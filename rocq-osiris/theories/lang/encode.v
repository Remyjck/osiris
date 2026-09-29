From osiris Require Import base.
Require Import outcome.
Require Import syntax locations thread_ids notations.
From iris.base_logic.lib Require Import iprop.

(* The type class [Encode A] stipulates the existence of a function [encode]
   of type [A → val]. This function encodes Coq values of type [A] into
   object-language values of type [val]. *)

Class Encode (A : Type) :=
  { encode' : A → syntax.val }.

(* We will later make [encode] opaque. We keep [encode'] transparent
   to compute the encoding at will. *)

Definition encode `{HencA : Encode A} := @encode' A HencA.
Arguments encode {A HencA}.

Lemma encode_encode' `{Encode A} :
  ∀ (a : A), encode a = (encode' a).
Proof. tauto. Qed.

(* This declaration is supposed to tell Coq that a goal of the form [Encode ?A]
   should *not* be solved by instantiating [?A] in an arbitrary way. *)

Global Hint Mode Encode + : typeclass_instances.

(* A notation. *)

Notation "# v" := (encode v) (at level 8, format "# v").

(* -------------------------------------------------------------------------- *)

(* The function [encode] is sometimes, but not always, required to be
   injective. *)

Class EncodeInjective `{Encode A} :=
  { encode_injective : ∀ a1 a2 : A, #a1 = #a2 → a1 = a2 }.

(* -------------------------------------------------------------------------- *)

(* The tactic [encode] expects a goal of the form [v = encode x],
   where typically [v] is a known value and [x] is a metavariable.
   Finding a suitable instantiation of [x] amounts to inverting
   the function [encode]. *)

(* The tactic [encode] either succeeds or leaves the goal intact.
   Use [solve[encode]] if you wish to require success. *)

Create HintDb encode.

Ltac encode :=
  eauto with encode.

Local Ltac solve_encode :=
  intros; subst; eauto.

(* -------------------------------------------------------------------------- *)

(* [Observe] generalizes encode, in that the left hand side is not restricted to
   [val]. [Observe] appears in the definitions of our reasoning judgements, and
   is used to reason about computations that don't result in values. Typically,
   these computations are the product of some auxiliary function in the
   semantics. *)

Class Observe A V : Type :=
  { observe : A -> V }.

Arguments observe {_ _ _}.

Global Instance observe_encode `{Encode A} :
  Observe A val | 0 :=
  {| observe := encode |}.

(* NOTE : Do not declare an instance of [Observe A A], or [Observe val val], as
   it will instantiate evars eagerly to this instance when it is not desired.
   (Even if its weight is very high.)

   Instead, we define a marker class [NotVal], which we manually instantiate
   for types [A] for which we want [Observe A A] instances. *)

Class NotVal (A : Type) : Prop := {}.
Global Hint Mode NotVal + : typeclass_instances.
Global Instance notval_bool : NotVal bool := {}.
Global Instance notval_void : NotVal void := {}.
Global Instance notval_unit : NotVal () := {}.
Global Instance notval_env : NotVal env := {}.
Global Instance notval_int : NotVal int := {}.
Global Instance notval_loc : NotVal loc := {}.
Global Instance notval_cont : NotVal cont := {}.
Global Instance notval_array : NotVal array := {}.
Global Instance notval_record : NotVal record := {}.
Global Instance notval_thread : NotVal thread := {}.
Global Instance notval_listloc : NotVal (list loc) := {}.
Global Instance notval_block : NotVal (mut_tag * list loc) := {}.

Global Instance observe_id `{NotVal A} : Observe A A | 1 := { observe := id }.

Notation "♯ x" := (observe x) (at level 5, format "♯ x").

Class ObserveInjective `{Observe A V} : Type :=
  { observe_injective : ∀ a1 a2 : A, ♯a1 = ♯a2 → a1 = a2 }.

Definition returns {A V} `{Observe A V} (φ : A -> Prop):=
  λ (v : V), ∃ a, v = observe a ∧ φ a.

(* -------------------------------------------------------------------------- *)

Section lift_specs.

  (* Utility functions for writing postconditions on [ewp] *)

  Context {Σ : gFunctors}.

  Context {A X : Type}.

  (* Lifting specifications in Iris logic. *)

  Definition ilift (ζ : X -d> iProp Σ) (Φ : A -d> iProp Σ) : outcome2 A X -d> iProp Σ :=
    (λ v, match v with
          | O2Ret r => Φ r
          | O2Throw e => ζ e
          end)%I.

  Global Instance ilift_ne n :
    Proper (pointwise_relation _ (dist n) ==>
            pointwise_relation _ (dist n) ==>
            eq ==> (dist n)) ilift.
  Proof. repeat intro; subst; destruct y1; eauto. Qed.

  Global Instance ilift_proper :
    Proper (pointwise_relation _ (≡) ==>
            pointwise_relation _ (≡) ==>
            eq ==> (≡)) ilift.
  Proof. repeat intro; subst; destruct y1; eauto. Qed.

  Definition ireturns {V} `{Observe A V} (Φ : A → iProp Σ) : V → iProp Σ :=
    λ v, (∃ a : A, ⌜v = ♯ a⌝ ∗ Φ a)%I.

  Lemma ireturns_mono {V} `{Observe A V} (Φ Φ' : A → iProp Σ) v :
    (∀ a, Φ a ⊢ Φ' a) → ireturns Φ v ⊢ ireturns Φ' v.
  Proof.
    intros HΦ. apply bi.exist_mono => a.
    apply bi.sep_mono; [ done | apply HΦ ].
  Qed.

End lift_specs.

(* FIXME: We have to import [int] after declaring [ilift_ne], or
   type inference fails for the instance. *)

Require Import int.

(* -------------------------------------------------------------------------- *)

(* Values. *)

(* Sometimes a value is reflected as itself at the logical level. *)

(* This may be used, for instance, for functions, or for modules. *)
(* Because pure builds in [encode], this instance is needed when writing a [pure]
  judgement about an expression that returns a function. *)

(* This instance has low priority because it should be used only
   when there is no other choice. *)

Global Instance Encode_val : Encode val :=
  { encode' := λ v, v }.

Lemma solve_encode_val v :
  v = #v.
Proof. solve_encode. Qed.

(* This hint is disabled because it creates problems. It can indeed create
   confusion and lead the tactic [encode] to constructing terms that involve
   nested applications of the function [encode] -- something that should
   never happen.

Global Hint Resolve solve_encode_val | 1000 : encode.
 *)

(* -------------------------------------------------------------------------- *)

(* Unit. *)

Global Instance Encode_unit : Encode unit :=
  { encode' := λ x, let '() := x in VUnit }.
  (* We deconstruct [x] because we want an equation [VUnit = #?x] to
     force an instantiation of [x] with [()]. *)

Lemma solve_encode_unit :
  VUnit = #().
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_unit : encode.

(* -------------------------------------------------------------------------- *)

(* The empty type. *)

Global Instance Encode_void : Encode void :=
  { encode' u := match u with end }.
  (* We deconstruct [x] because we want an equation [VUnit = #?x] to
     force an instantiation of [x] with [()]. *)

(* -------------------------------------------------------------------------- *)

(* Booleans. *)

Global Instance Encode_bool : Encode bool :=
  { encode' := λ b, VBool b }.

Lemma solve_encode_false b :
  false = b →
  VFalse = #b.
Proof. solve_encode. Qed.

Lemma solve_encode_true b :
  true = b →
  VTrue = #b.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_false solve_encode_true : encode.

(* -------------------------------------------------------------------------- *)

(* Booleans, reflected as Coq propositions. *)

(* The function [truth : Prop → bool] maps a Coq proposition
   to the corresponding Boolean value. Defining this function
   requires Hilbert's [ε] operator. *)

From Stdlib Require Import Classical Epsilon.

Definition inh_bool : inhabited bool.
Proof. constructor. constructor. Qed.

Definition truth (P : Prop) : bool :=
  epsilon inh_bool (λ (b : bool), if b then P else ¬P).

(* If [P] is false then [truth P] is [false]. *)

Lemma truth_false (P : Prop) :
  ¬ P →
  truth P = false.
Proof.
  intros H.
  unfold truth.
  assert (existence: exists (b : bool), if b then P else ¬P).
  { exists false. assumption. }
  generalize (epsilon_spec inh_bool _ existence). clear existence.
  match goal with |- context[epsilon ?w ?P] => generalize (epsilon w P) end.
  intros [|]; tauto.
Qed.

Lemma truth_False :
  truth False = false.
Proof.
  eauto using truth_false.
Qed.

(* If [P] is true then [truth P] is [true]. *)

Lemma truth_true (P : Prop) :
  P →
  truth P = true.
Proof.
  intros H.
  unfold truth.
  assert (existence: exists (b : bool), if b then P else ¬P).
  { exists true. assumption. }
  generalize (epsilon_spec inh_bool _ existence). clear existence.
  match goal with |- context[epsilon ?w ?P] => generalize (epsilon w P) end.
  intros [|]; tauto.
Qed.

Lemma truth_True :
  truth True = true.
Proof.
  eauto using truth_true.
Qed.

(* [truth P] determines which of [P] and [¬P] holds. *)

Lemma truth_elim (P : Prop) :
  if truth P then P else ¬P.
Proof.
  case_eq (truth P); intro Heq.
  (* [NNPP] is Peirce's law. *)
  { eapply NNPP. intro H. eapply truth_false in H. congruence. }
  { intro H. eapply truth_true in H. congruence. }
Qed.

(* If [truth P] is [false] then  [P] is false. *)

Lemma truth_false_elim (P : Prop) :
  truth P = false →
  ¬ P.
Proof.
  intros H. generalize (truth_elim P). rewrite H. tauto.
Qed.

(* If [truth P] is [true] then  [P] is true. *)

Lemma truth_true_elim (P : Prop) :
  truth P = true →
  P.
Proof.
  intros H. generalize (truth_elim P). rewrite H. tauto.
Qed.

(* [truth : Prop → bool] is the inverse of [Is_true : bool → Prop]. *)

Lemma truth_Is_true b :
  truth (Is_true b) = b.
Proof.
  destruct b; simpl; [ rewrite truth_True | rewrite truth_False ]; eauto.
Qed.

Lemma Is_true_truth P :
  Is_true (truth P) ↔ P.
Proof.
  generalize (truth_elim P).
  generalize (truth P).
  intros [|]; simpl; tauto.
Qed.

(* The truth of [¬P] is the negation of the truth of [P]. *)

Lemma truth_neg P :
  truth (¬P) = negb (truth P).
Proof.
  generalize (truth_elim P). generalize (truth P).
  intros [|]; simpl; intros.
  { eapply truth_false. tauto. }
  { eapply truth_true. tauto. }
Qed.

(* If [b] reflects [P], [truth P] is [b] *)

Lemma truth_reflect P b : reflect P b → truth P = b.
Proof.
  inversion 1; auto using truth_true, truth_false.
Qed.

(* Similar but formulated in a way [lia] understands *)

Lemma truth_eq_true P b : (b = true ↔ P) → truth P = b.
Proof.
  destruct b; intros.
  - intuition auto using truth_true.
  - assert (¬P) by firstorder congruence.
    auto using truth_false.
Qed.

(* A Coq proposition can be encoded as an OCaml Boolean value. *)

(* In other words, the logical model of an OCaml Boolean value
   can be a Coq proposition. *)

Global Instance Encode_Prop : Encode Prop :=
  { encode' := λ P, VBool (truth P) }.

(* Allowing the tactic [encode] to use [solve_encode_False] and
   [solve_encode_True], where [P] is a metavariable, leads Coq to
   instantiate [P] with an arbitrary proposition that happens to be
   provably false or provably true. *)

(* So, the following two lemmas are currently *not* added to the
   hint database [encode]. *)

Lemma solve_encode_False (P : Prop) :
  ¬ P →
  VFalse = #P.
Proof.
  intros H. apply truth_false in H. simpl. rewrite H. reflexivity.
Qed.

Lemma solve_encode_True (P : Prop) :
  P →
  VTrue = #P.
Proof.
  intros H. apply truth_true in H. simpl. rewrite H. reflexivity.
Qed.

(* Global Hint Resolve solve_encode_False solve_encode_True : encode. *)

Lemma encode_truth (P : Prop) : #(truth P) = #P.
Proof. reflexivity. Qed.

Lemma iff_truth (P Q : Prop) : P ↔ Q → truth P = truth Q.
Proof.
  generalize (truth_elim P), (truth_elim Q).
  do 2 destruct (truth _); tauto.
Qed.

Lemma iff_encode (P Q : Prop) : P ↔ Q → #P = #Q.
Proof.
  simpl encode.
  by intros ->%iff_truth.
Qed.

(* -------------------------------------------------------------------------- *)

(* Natural numbers. *)

Global Instance Encode_nat : Encode nat :=
  { encode' := λ n, VInt (repr (Z.of_nat n)) }.

Lemma solve_encode_nat i n :
  i = repr (Z.of_nat n) →
  VInt i = #n.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_nat : encode.

(* -------------------------------------------------------------------------- *)

(* Integer numbers. *)

Global Instance Encode_Z : Encode Z :=
  { encode' := λ n, VInt (repr n) }.

Global Instance Encode_int : Encode int :=
  { encode' := λ n, VInt n }.

Lemma solve_encode_int i z :
  i = repr z →
  VInt i = #z.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_int : encode.

(* This should help: *)

Global Hint Resolve
  neg_repr
  add_repr_repr
  sub_repr_repr
  mul_repr_repr
  divs_repr_repr
  mods_repr_repr
  eq_repr_repr
  lt_repr_repr
  lnot_repr
  land_repr_repr
  lor_repr_repr
  lxor_repr_repr
  lsl_repr_repr
  lsr_repr_repr
  asr_repr_repr
: encode.

(* -------------------------------------------------------------------------- *)

(* First-class continuations. *)

Global Instance Encode_cont : Encode cont :=
  { encode' := λ l, VCont l }.

Lemma solve_encode_cont (l : cont) :
  VCont l = #l.
Proof. solve_encode. Qed.

(* Pointers to blocks. *)

Global Instance Encode_array : Encode syntax.array :=
  { encode' := λ l, VArray l }.

Lemma solve_encode_array (l : syntax.array) :
  VArray l = #l.
Proof. solve_encode. Qed.

Global Instance Encode_record : Encode record :=
  { encode' := λ l, VRecord l }.

Lemma solve_encode_record (l : record) :
  VRecord l = #l.
Proof. solve_encode. Qed.

(* -------------------------------------------------------------------------- *)

(* Environments. *)

Global Instance Encode_env : Encode env :=
  { encode' := λ η, VStruct η }.

Lemma solve_encode_env η :
  VStruct η = #η.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_env
| 0 (* higher priority than encoding lists *)
  : encode.

(* -------------------------------------------------------------------------- *)

(* Floats. *)

Global Instance Encode_float : Encode PrimFloat.float :=
  { encode' := λ f, VFloat f }.

(* -------------------------------------------------------------------------- *)

(* Char. *)

Global Instance Encode_char: Encode char :=
  { encode' := λ f, VChar f }.

(* -------------------------------------------------------------------------- *)

(* Options. *)

Global Instance Encode_option `{Encode A} : Encode (option A) :=
  { encode' :=
      λ o, match o with None => VNone | Some v => VSome #v end }.

Lemma solve_encode_None `{Encode A} (o : option A) :
  None = o →
  VNone = #o.
Proof. solve_encode. Qed.

Lemma solve_encode_Some `{Encode A} v (o : option A) (x : A) :
  Some x = o →
  v = #x →
  VSome v = #o.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_None solve_encode_Some : encode.

(* -------------------------------------------------------------------------- *)

(* Memory locations. *)

(* This instance is needed, for instance, for memory locations. *)

Global Instance Encode_loc : Encode loc :=
  { encode' := λ l, VLoc l }.

Lemma solve_encode_loc l :
  VLoc l = #l.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_loc : encode.

(* -------------------------------------------------------------------------- *)

(* Thread identifiers. *)

(* This instance is needed, for instance, for memory locations. *)

Global Instance Encode_thread : Encode thread :=
  { encode' := λ ι, VThread ι }.

Lemma solve_encode_thread ι :
  VThread ι = #ι.
Proof. solve_encode. Qed.

Global Hint Resolve solve_encode_thread : encode.

(* -------------------------------------------------------------------------- *)

(* Lists. *)

Fixpoint encode_list `{Encode A} (xs : list A) :=
  match xs with
  | []      => VNil
  | x :: xs => VCons #x (encode_list xs)
  end.

Global Instance Encode_list `{Encode A} : Encode (list A) :=
  { encode' := encode_list }.

Lemma encode_list_is_encode `{Encode A} :
  ∀ (xs : list A),
  encode_list xs = #xs.
Proof. solve_encode. Qed.

Lemma solve_encode_Nil `{Encode A} (xs : list A) :
  [] = xs →
  VNil = #xs.
Proof. solve_encode. Qed.

Lemma solve_encode_Cons `{Encode A} (xs : list A) x xs' v1 v2 :
  x :: xs' = xs →
  v1 = #x →
  v2 = #xs' →
  VCons v1 v2 = #xs.
Proof. solve_encode. Qed.

Global Hint Resolve
  encode_list_is_encode
  solve_encode_Nil solve_encode_Cons
: encode.

(* Useful for [pure (evals η _) φ ψ]. *)
Global Instance observe_list {A} `{Encode A}:
  Observe (list A) (list val) | 100 :=
  {| observe := (map encode.encode) |}.

Lemma solve_observe_nil A (Enc:Encode A) :
  forall (xs : list A),
    [] = xs →
    nil = ♯xs.
Proof. intros; subst; cbn; eauto. Qed.

Lemma solve_observe_cons {A} {Enc: Encode A} :
  forall (v : val) (a : A) tl vtl (x : list A),
    a :: tl = x ->
    v = # a ->
    vtl = ♯ tl ->
    v :: vtl = ♯ x.
Proof.
  induction tl; intros; subst; eauto.
Qed.

Global Hint Extern 0 (_ :: _ = ♯ _) =>
  simple eapply solve_observe_cons : encode.
Global Hint Extern 100 ([] = ♯ _) =>
  simple eapply solve_observe_nil: encode.

(* -------------------------------------------------------------------------- *)

(* Strings. *)

Global Instance Encode_string : Encode string :=
  { encode' := λ s, VString s }.

Lemma encode_string_is_encode s :
  VString s = #s.
Proof. solve_encode. Qed.
