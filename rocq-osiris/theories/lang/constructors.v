From osiris Require Import base.
Require Import syntax type_nel encode locations.

(* This file contains typeclasses which tie concrete values of the form
   [VData c args] and [VXData l args] to their logical representation. *)

(* -------------------------------------------------------------------------- *)

(* [Data c τ] bundles a function [ctor_apply : τ → A] with a proof that
   [∀ xs, #(ctor_apply xs) = VData [c] [xs]]. This means that
   [ctor_apply xs] can be used as a logical representation for [VData c xs]. *)

Class Data (c : data) (τ : types) (A : Type) `{Encode A} : Type :=
  { ctor_apply  : τ → A;
    ctor_encode : ∀ xs : τ, VData c (to_vals xs) = #(ctor_apply xs) }.

(* Only try and resolve the [Data] typeclass if the constructor [c] and
   the result type [A] are known. *)
Global Hint Mode Data ! - ! - : typeclass_instances.

(* -------------------------------------------------------------------------- *)
(* Some instances of the [Data] typeclass. *)

Global Instance Data_Some `{Encode A} : Data "Some" τ[A] (option A) :=
  { ctor_apply  := Some;
    ctor_encode := λ _, eq_refl }.

Global Instance Data_Cons `{Encode A} : Data "::" τ[A; list A] (list A) :=
  { ctor_apply  := λ '(x, xs), x :: xs;
    ctor_encode := λ '(_, _), eq_refl }.


(* -------------------------------------------------------------------------- *)

(* [Tagged c A] is the analogue of [Data] for constructors whose payload
   is an *inline record*: it ties the constructor [c] to the function
   building the corresponding logical value from the record. *)

Class Tagged (c : data) (A : Type) `{Encode A} : Type :=
  { tagged_apply  : record → A;
    tagged_encode : ∀ r : record, VTaggedRecord c r = #(tagged_apply r) }.

(* As for [Constant], resolution is keyed on the constructor name; [A] is
   left as an output so that automation can also use this when only the
   stored value is known. *)
Global Hint Mode Tagged ! - - : typeclass_instances.

(* Any inline-record value may be reflected at the [val] level as itself.
   Deliberately not an instance, for the same reason as [Constant_val]:
   it matches every constructor name. *)
Definition Tagged_val (c : data) : Tagged c val :=
  {| tagged_apply := VTaggedRecord c; tagged_encode := λ _, eq_refl |}.

(* -------------------------------------------------------------------------- *)

(* [TaggedEncode A] is [Tagged]'s converse: it says that every value
   of [A] encodes to an inline record, and names the constructor and
   the block it encodes to.

   Note this is related to, but distinct from [RecordRepr] (see
   [record_rules.v]), which sits on the other side of the pointer:
   [RecordRepr A τ t] models the contents of a block as a tuple of
   values, and the block's address is a parameter, not a function of
   the model value. *)

Class TaggedEncode (A : Type) `{Encode A} := {
  tagged_tag : A → data;
  tagged_blk : A → record;
  tagged_encode_eq : ∀ a : A, #a = VTaggedRecord (tagged_tag a) (tagged_blk a);
}.

Global Hint Mode TaggedEncode ! - : typeclass_instances.

(* -------------------------------------------------------------------------- *)

(* [Constant c A] is the nullary analogue of [Data]: it ties a constant
   constructor [c] to the logical value it encodes. *)

Class Constant (c : data) (A : Type) `{Encode A} : Type :=
  { constant_value  : A;
    constant_encode : VConstant c = #constant_value }.

Global Hint Mode Constant ! - - : typeclass_instances.

(* -------------------------------------------------------------------------- *)
(* Some instances of the [Constant] typeclass. *)

Global Instance Constant_unit : Constant "()" unit :=
  { constant_value := (); constant_encode := eq_refl }.

Global Instance Constant_true : Constant "true" bool :=
  { constant_value := true; constant_encode := eq_refl }.

Global Instance Constant_false : Constant "false" bool :=
  { constant_value := false; constant_encode := eq_refl }.

Global Instance Constant_None `{Encode A} : Constant "None" (option A) :=
  { constant_value := None; constant_encode := eq_refl }.

Global Instance Constant_nil `{Encode A} : Constant "[]" (list A) :=
  { constant_value := []; constant_encode := eq_refl }.

(* Any constant may be reflected at the [val] level, as itself.  This
   is deliberately *not* an instance: it matches every constructor
   name, so it would make [Constant c ?A] ambiguous for every [c] and
   defeat the type inference described above. We use it explicitly when
   the goal's postcondition is at type [val]. *)
Definition Constant_val (c : data) : Constant c val :=
  {| constant_value := VConstant c; constant_encode := eq_refl |}.


(* -------------------------------------------------------------------------- *)

(* [XData l τ] is the analogue of [Data] for extensible types: it ties
   a *location* [l] to the logical value it encodes. *)

Class XData (l : loc) (τ : types) (A : Type) `{Encode A} : Type :=
  { xctor_apply  : τ → A;
    xctor_encode : ∀ (xs : τ), VXData l (to_vals xs) = #(xctor_apply xs) }.

Global Hint Mode XData ! - ! - : typeclass_instances.


(* -------------------------------------------------------------------------- *)
(* Encode instance for tuples. *)

Definition encode_tuple {τ : types} : τ → val :=
  λ xs, VTuple (@to_vals τ xs).

Global Instance Encode_tuple {τ : types} : Encode τ :=
  { encode' := encode_tuple }.

Lemma encode_tuple_is_encode {τ : types} :
  ∀ (xs : τ),
    encode_tuple xs = #xs.
Proof. auto. Qed.

Lemma solve_encode_tuple {τ : types} vs (xs : τ) :
  vs = to_vals xs →
  VTuple vs = #xs.
Proof. intros ->. auto. Qed.

Global Hint Resolve encode_tuple_is_encode solve_encode_tuple : encode.

(* -------------------------------------------------------------------------- *)

(* [TypesOf A] computes the [types] value corresponding to the plain Rocq
   type [A], along with a proof that [coerce_to_type types_of = A].

   This lets [Encode_from_types] provide flat tuple encoding for any
   right-nested product type without requiring an explicit [τ[...]]
   annotation at use sites.

   Priority: [TypesOf_cons | 10] fires before [TypesOf_base | 100], so
   product types get the cons branch rather than a single-element base. *)
Class TypesOf (A : Type) : Type :=
  { types_of : types; types_of_eq : coerce_to_type types_of = A }.

Global Arguments types_of A {_}.
Global Arguments types_of_eq A {_}.

Global Instance TypesOf_base {A : Type} {HA : Encode A} : TypesOf A | 100 :=
  {| types_of := Tbase A; types_of_eq := eq_refl |}.

Global Instance TypesOf_cons {B C : Type} {HB : Encode B} {HC : TypesOf C}
    : TypesOf (B * C) | 10 :=
  {| types_of := Tcons B (types_of C);
     types_of_eq := f_equal (prod B) (types_of_eq C) |}.

(* Provides flat [VTuple] encoding for any right-nested product type.
   Priority 50 ensures direct [Encode] instances (priority ~1) still win,
   while this instance covers product types with no direct instance. *)
Global Instance Encode_from_types {A : Type} {HA : TypesOf A}
    : Encode A | 50.
Proof.
  rewrite <- (types_of_eq A).
  exact (@Encode_tuple (types_of A)).
Defined.

(* [Encode_from_types] and [TypesOf_base] form a cycle:
   [Encode A → TypesOf A → Encode A].  A search for [Encode A] with no
   direct instance therefore diverges instead of failing.  The
   offending step is [TypesOf_base] directly under [Encode_from_types];
   productive derivations always interleave [TypesOf_cons], so cutting the
   consecutive pair breaks the cycle without losing any solution. *)
Global Hint Cut [_* Encode_from_types TypesOf_base] : typeclass_instances.

(* Provides [Observe (B * C) val] when [Encode B] and [Encode C] are available.
   The explicit @type_nel.Tcons/@Tbase construction avoids the deferred-evar
   problem that arises when τ[B;C] is used as a type annotation inside a ∀. *)
Global Instance observe_prod_val {B C : Type} {HB : Encode B} {HC : Encode C}
    : Observe (B * C) val | 100 :=
  let enc : Encode (B * C) := @Encode_tuple (@type_nel.Tcons B HB (@Tbase C HC)) in
  Build_Observe _ _ (encode' (Encode := enc)).
