(* From iris.proofmode Require Import proofmode classes. *)
(* From iris.bi Require Import weakestpre. *)
(* From iris Require Import base_logic.lib.gen_heap. *)

From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
From osiris.utils Require Import orders.
Require Export Externals.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import proofmode.

Open Scope Z_scope.

Local Transparent encode.

(* The symbols of the OCaml standard library are translated as
   [Stdlib.<symbol>].
   This file defines:
     1. symbols of [Stdlib], eg. (+), ... ;
     2. [Stdlib] as a module ;
     3.a. specifications for the symbols of the module ;
     3.b. a unified specification for the module ;
     4. a tactic to use automatically apply the aforementioned specs.

   After 3.b., the code is turned opaque to (1) better control its usage and (2)
   avoid it to be unfolded: some unfolding would lead to several duplications of
   continuations (ie. the rest of the code). *)

Local Abbreviation VClo1 body :=
  (
    VClo [] $
      AnonFun "x" $
      (body (EVar "x"))
  ).

Local Abbreviation VClo2 body :=
  (
    VClo [] $
      AnonFun "x" $
      EFun1Var "y" $
      (body (EVar "x") (EVar "y"))
  ).

Section StdLib__code.

  (* ------------------------------------------------------------------------ *)

  (* Arithmetic Operations. *)

  Definition Stdlib__add := VClo2 EIntAdd.
  Definition Stdlib__sub := VClo2 EIntSub.
  Definition Stdlib__mul := VClo2 EIntMul.
  Definition Stdlib__div := VClo2 EIntDiv.
  Definition Stdlib__neg := VClo1 EIntNeg.

  (* Arithmetic Comparisons. *)
  Definition Stdlib__lt : val := VClo2 EOpLt.
  Definition Stdlib__le : val := VClo2 EOpLe.
  Definition Stdlib__gt : val := VClo2 EOpGt.
  Definition Stdlib__ge : val := VClo2 EOpGe.

  (* Arithmetic part of the module. *)
  Definition Stdlib_arith_env : env :=
    [("+", Stdlib__add);
     ("-", Stdlib__sub);
     ("*", Stdlib__mul);
     ("/", Stdlib__div);
     ("~-", Stdlib__neg);
     ("<", Stdlib__lt);
     ("<=", Stdlib__le);
     (">=", Stdlib__ge);
     (">", Stdlib__gt)].

  (* ------------------------------------------------------------------------ *)

  (* Store-related functions. *)
  Definition Stdlib__ref : val := VClo1 ERef.
  Definition Stdlib__load : val := VClo1 ELoad.
  Definition Stdlib__store : val := VClo2 EStore.

  Definition Stdlib_store_env : env :=
    [("!", Stdlib__load);
     (":=", Stdlib__store);
     ("ref", Stdlib__ref)].

  (* ------------------------------------------------------------------------ *)

  (* Polymorphic Comparisons. *)
  Definition Stdlib__eq : val := VClo2 EOpEq.
  Definition Stdlib__ne : val := VClo2 EOpNe.
  Axiom Stdlib__compare : val.

  (* On Pairs. *)
  Definition Stdlib__fst : val :=
      VClo1 (λ (e : expr),
        ELet1 (PPair (PVar "x") PAny) e $
        EVar "x"
      ).
  Definition Stdlib__snd : val :=
    VClo1 (λ (e : expr),
       ELet1 (PPair PAny (PVar "y")) e $
       EVar "y"
      ).

  Definition Stdlib__raise : val := VClo1 ERaise.

  Definition Stdlib_misc_env : env :=
    [("=", Stdlib__eq);
     ("<>", Stdlib__ne);
     ("compare", Stdlib__compare);
     ("raise", Stdlib__raise);
     ("fst", Stdlib__fst);
     ("snd", Stdlib__snd)].

  (* ------------------------------------------------------------------------ *)

  (* Boolean Operations. *)
  Definition Stdlib__not : val := VClo1 EBoolNeg.
    (* Boolean conjunction and disjunction are not functions;
       they are primitive operations. *)

  Definition Stdlib_bool_env : env :=
    [("not", Stdlib__not)].

  (* Putting everything together. *)
  Definition Stdlib_env :=
    concat [Stdlib_arith_env;
            Stdlib_store_env;
            Stdlib_misc_env;
            Stdlib_bool_env].

  Definition Stdlib := VStruct Stdlib_env.
End StdLib__code.

Definition stdlib_env := ("Stdlib", Stdlib) :: Stdlib_env.

Definition toplevel me (φ : env -> Prop) :=
  eval_module stdlib_env me φ.

(* -------------------------------------------------------------------------- *)

(* Specification templates. *)

(* A specification for a pure function [decide] that decides a relation [R],
   subject to a precondition [P], producing a Boolean outcome. *)

(* This specification uses [pure] and a relation [R] of type [A → A → Prop]. *)

Definition decide_spec `{Encode A}
  (decide : val) (P : A → Prop) (R : A → A → bool)
:=
  ∀ (x : A),
    P x →
    pure (call decide #x) (λ v,
      ∀ (y : A),
      P y →
      pure (call v #y) (λ (b : bool), b = R x y) (⊥ : void.void → Prop)) (⊥ : void.void → Prop).

(* The above specification states that an application of [decide] to just
   one argument returns a closure. As a sanity check, we verify that this
   is stronger than the following statement, which describes an application
   of [decide] to two arguments. *)

Local Lemma decide_spec' `{Encode A}
  (decide : val) (P : A → Prop) (R : A → A → bool)
:
  decide_spec decide P R →
  ∀ (x y : A), P x → P y →
  pure
    (bind (call decide #x) (λ v, call v #y))
    (λ (b : bool),
      b = R x y) (⊥ : void.void → Prop).
Proof.
  intros Hspec x y Hx Hy.
  eapply pure_bind; [ eauto | intros v; cbn; intros Hv ].
  eauto.
Qed.

(* A specification for a [compare] function that decides a preorder [le],
   producing an integer code that encodes a three-way outcome. *)

(* The double application [compare x y] returns a (representable) integer
   code [c] such that the sign of [c] encodes the three possible outcomes
   of the comparison between [x] and [y]. *)

Definition compare_spec `{Encode A} (compare : val) (le : A → A → Prop) :=
  let lt := strict le in
  let eq := equivalent le in
  ∀ (x y : A),
    pure (call compare #x) (λ v,
        pure (call v #y) (λ (c : Z),
            representable c ∧
              (c < 0 ↔ lt x y)%Z ∧
              (c = 0 ↔ eq x y)%Z ∧
              (0 < c ↔ lt y x)%Z
          ) (⊥ : void.void → Prop)) (⊥ : void.void → Prop).
(* -------------------------------------------------------------------------- *)

Lemma Stdlib__eq_spec :
  decide_spec Stdlib__eq representable Z.eqb.
Proof.
  intros x Hx.
  pure_enter. rewrite <- fold_pre_eval. simpl. pure_ret. unfold observe, observe_encode.
  rewrite <- solve_encode_val. reflexivity.
  intros y Hy.
  pure_enter.
  eapply pure_eval_EOpEq; try (pure_path); auto with encode.
Qed.

Lemma Stdlib__ne_spec :
  decide_spec Stdlib__ne representable (λ x y, negb (x =? y)).
Proof.
  intros x Hx. pure_enter. rewrite <- fold_pre_eval. simpl. pure_ret.
  simpl. rewrite <- solve_encode_val. reflexivity.
  intros y Hy.
  pure_enter.
  eapply pure_eval_EOpNe; try (pure_path); auto.
Qed.
