From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
Require Import
  judgements pure_rules pattern_rules binding_rules call_rules.

(* This file defines contains reasoning rules about evaluation of expressions
  for pure judgements. *)

(* -------------------------------------------------------------------------- *)

(* EPath (x : path) *)

Lemma pure_eval_path `{Encode A} `{Encode C} η π (φ : A -> Prop) (ζ : C → Prop) a :
  lookup_path η π = Some #a →
  φ a →
  pure (eval η (EPath π)) φ ζ.
Proof.
  simpl_eval. intros -> Hφ.
  eapply pure_ret; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(**  *Anonymous functions. *)

(* EAnonFun (a : anonfun) *)

Lemma pure_eval_anonfun `{Encode C} η a (φ : val -> Prop) (ζ : C → Prop) :
  φ (VClo η a) ->
  pure (eval η (EAnonFun a)) φ ζ.
Proof.
  intros Hclo.
  simpl_eval.
  eapply pure_ret; eauto with pure.
Qed.

(* -------------------------------------------------------------------------- *)

(** *Function application: [e1 e2]. *)

(* EApp (e1 e2 : expr) *)

Lemma pure_eval_app `{Encode A, Encode B} `{Encode C}
  η e1 e2
  (φ1 : val → Prop) (φ2 : A → Prop) (ψ : B → Prop)
  (ζ : C → Prop) :
  pure (eval η e1) φ1 ζ →
  pure (eval η e2) φ2 ζ →
  (∀ v1 v2, φ1 v1 → φ2 v2 → pure (call v1 #v2) ψ ζ) →
  pure (eval η (EApp e1 e2)) ψ ζ.
Proof.
  intros He1 He2 Hp. simpl_eval.
  eapply pure_bind.
  { instantiate (1:= λ '(a1, a2), { call a1 #a2 ensures ψ raises ζ}).
    eapply pure_par; try eassumption. }
  intros [??] Hcall. apply Hcall.
Qed.

(* Simple version : the expressions must evaluate to a singleton
   value. This lemma is useful for practical instances where
   the value postcondition is an evar for the [e1, e2] expressions. *)

Lemma pure_eval_app_simple `{Encode A} `{Encode C}
  η e1 e2
  (f : val) (arg : A) (ψ : val → Prop)
  (ζ : C → Prop) :
  pure (eval η e1) (singleton f) ζ →
  pure (eval η e2) (singleton arg) ζ →
  pure (call f #arg) ψ ζ →
  pure (eval η (EApp e1 e2)) ψ ζ.
Proof.
  intros; eapply pure_eval_app; eauto; by intros ??->->.
Qed.

Lemma pure_eval_app_seq `{Encode A} `{Encode C}
  η e1 e2
  (ψ : val → Prop)
  (ζ : C → Prop) :
  pure (eval η e1) (λ f : val,
    pure (eval η e2) (λ arg : A,
      pure (call f #arg) ψ ζ) ζ) (⊥ : C → Prop) →
  pure (eval η (EApp e1 e2)) ψ ζ.
Proof.
  intros He1. simpl_eval.
  eapply pure_bind.
  eapply (pure_par_seq (A1:=val) (A2:=A) (B1:=C)).
  { instantiate (1:= λ '(f, arg), { call f #arg ensures ψ raises ζ }).
    apply He1. }
  intros [??] Hcall. apply Hcall.
  Unshelve. all: eauto with pure.
Qed.

(* -------------------------------------------------------------------------- *)

(** Evaluating tuples, or several expressions in parallel *)

Lemma pure_evals_cons `{Encode A} {τ : types} {C} `{Encode C} {ζ : C → Prop} η e es (φ : A → Prop) (φs : τ → Prop) :
  pure (eval η e) φ ζ →
  pure (evals η es) φs ζ →
  pure (A:=type_nel.Tcons A τ) (evals η (e :: es)) (λ '(x, xs), φ x ∧ φs xs) ζ.
Proof.
  intros He Hes. simpl_evals.
  eapply pure_bind.
  { eapply pure_par. apply He. apply Hes.
    instantiate (1:= λ '(a1, a2), φ a1 ∧ φs a2).
    simpl. tauto. }
  intros (x & xs) (Hφ & Hφs).
  eapply (pure_ret _ _ _ (x, xs)). simpl. reflexivity.
  tauto.
Qed.

Lemma pure_evals_singleton `{Encode A} {C} `{Encode C} {ζ : C → Prop} η e (φ : A → Prop) :
  pure (eval η e) φ ζ →
  pure (A:=τ[A]) (evals η [e]) φ ζ.
Proof.
  intros He. simpl_evals.
  eapply pure_bind.
  { eapply (pure_par (A2:=list val)).
    - apply He.
    - eapply pure_ret. encode. apply eq_refl.
    - intros x ? Hφ <-.
      instantiate (1:= λ '(a, ls), φ a ∧ ls = []).
      tauto. }
  intros (x & ?) (Hφ & ->).
  eapply pure_ret. reflexivity.
  apply Hφ.
Qed.

Lemma pure_evals_nil `{Encode C} η (φ : list val -> Prop) (ψ : C → Prop):
  φ [] ->
  pure (evals η nil) φ ψ.
Proof.
  intros. simpl_evals.
  eapply pure_ret; encode.
Qed.

(* -------------------------------------------------------------------------- *)

(** *Tuple construction: [(e1, e2, ...)]. *)

(* ETuple (es : list expr) *)

Lemma pure_eval_tuple {τ : types} {φ : τ → Prop} {C} `{Encode C} {ζ : C → Prop} (φ' : τ → Prop) η es :
  pure (evals η es) φ' ζ →
  (∀# (xs : τ), φ' xs → φ xs) →
  pure (eval η (ETuple es)) φ ζ.
Proof.
  intros Hes P.
  simpl_eval.
  eapply pure_bind. { apply Hes. }
  intros xs Hφ.
  eapply pure_ret. reflexivity.
  rewrite tforall_equiv in P.
  apply P, Hφ.
Qed.

(* -------------------------------------------------------------------------- *)

(** *Data constructor application: [A (e)]. *)

(* EData (c : data) (e : list expr) *)

(* The logical value of the constant is determined by the [Constant]
   typeclass resolution. *)
Lemma pure_eval_const {c : data} {B : Type} {HB : Encode B} {HC : Constant c B} `{Encode C}
  η (ψ : B -> Prop) (ζ : C → Prop) :
  ψ (@constant_value c B HB HC) ->
  pure (eval η (EConstant c)) ψ ζ.
Proof.
  intros. simpl_eval.
  eapply pure_ret.
  - apply constant_encode.
  - assumption.
Qed.

Lemma pure_eval_data `{DC : Data c τ A} `{Encode C} {φ : A → Prop} (φs : τ → Prop) η es (ζ : C → Prop) :
  pure (evals η es) φs ζ ->
  (∀# xs, φs xs → φ (DC.(ctor_apply) xs)) →
  pure (eval η (EData c es)) φ ζ.
Proof.
  intros Hes Hφ. simpl_eval.
  eapply pure_bind. apply Hes.
  intros xs Hφs.
  eapply pure_ret. simpl. apply DC.(ctor_encode).
  rewrite tforall_equiv in Hφ.
  apply Hφ, Hφs.
Qed.

(** *Extensible constructor application. *)

(* EXData (p : path) (e : list expr) *)

(* Although the declaration (i.e. allocation) of exceptions and effects
   cannot be verified by the [pure] wp, we can still verify the
   application of extensible constructors if their corresponding
   location is already bound in the environment. *)

Lemma pure_eval_xconstant `{Encode A} `{Encode C} {φ : A → Prop} {p} l (a : A) η (ζ : C → Prop) :
  VXData l [] = #a →
  lookup_path η p = Some #l →
  φ a →
  pure (eval η (EXData p [])) φ ζ.
Proof.
  intros Henc Hpath Hφ. simpl_eval.
  eapply pure_bind.
  { rewrite Hpath. eapply (pure_ret (A:=loc)). encode. apply eq_refl. }
  intros ? <-.
  eapply (pure_bind (A1:=list val)).
  { eapply (pure_ret (A:=list val)). encode. apply eq_refl. }
  intros ? <-.
  eapply pure_ret. simpl. apply Henc.
  apply Hφ.
Qed.

Lemma pure_eval_xdata `{XDC : XData l τ A} `{Encode C} {φ : A → Prop} {p} (φs : τ → Prop) η es (ζ : C → Prop) :
  lookup_path η p = Some #l →
  pure (evals η es) φs ζ ->
  (∀# xs, φs xs → φ (XDC.(xctor_apply) xs)) →
  pure (eval η (EXData p es)) φ ζ.
Proof.
  intros Hpath Hes Hφ. simpl_eval.
  eapply pure_bind.
  { rewrite Hpath. eapply (pure_ret (A:=loc)). encode. apply eq_refl. }
  intros ? <-.
  eapply pure_bind. { apply Hes. }
  intros xs Hφs.
  eapply pure_ret. simpl. apply XDC.(xctor_encode).
  rewrite tforall_equiv in Hφ.
  apply Hφ, Hφs.
Qed.

(* -------------------------------------------------------------------------- *)

(** *Boolean conjunction, disjunction, and negation. *)

(* Some special cases. *)

Local Lemma pure_as_bool `{Encode C} (m : microvx) (φ : bool → Prop) (ψ : C → Prop) :
  pure m φ ψ →
  pure (as_bool m) φ ψ.
Proof.
  intro Hm.
  eapply pure_bind; eauto.
  intros [] ?;
    with_strategy transparent [val_as_bool] cbn;
    eauto with pure.
Qed.

Local Lemma pure_bind_as_bool `{Encode C} {A} {EncA: Encode A}
  (m : microvx) (φ : bool → Prop) (ψ : A → Prop)
  (k : bool → micro val exn) :
  pure m φ (⊥ : C → Prop) →
  (∀ b : bool, φ b → pure (k b) ψ (⊥ : C → Prop)) →
  pure (bind (as_bool m) k) ψ (⊥ : C → Prop).
Proof.
  intros Hm Hp. eapply pure_bind.
  eapply pure_as_bool; done.
  apply Hp.
Qed.

(* EBoolConj (e1 e2 : expr) *)

Lemma pure_eval_conj `{Encode C} η e1 e2 (φ1 φ2 ψ : bool -> Prop) :
  pure (eval η e1) φ1 (⊥ : C → Prop) →
  pure (eval η e2) φ2 (⊥ : C → Prop) →
  (φ1 true -> forall b, φ2 b -> ψ b) ->
  (φ1 false -> ψ false) ->
  pure (eval η (EBoolConj e1 e2)) ψ (⊥ : C → Prop).
Proof.
  intros He1 He2 Ht Hf. simpl_eval.
  eapply pure_bind_as_bool; eauto.
  intros [] Hb.
  { specialize (Ht Hb).
    eapply pure_ret_mono; eauto. }
  { eapply pure_ret; eauto with encode. }
Qed.

(* Sequentialized version. *)

Lemma pure_eval_conj_seq `{Encode C} η e1 e2 (φ1 φ2 ψ : bool -> Prop) :
  pure (eval η e1)
    (fun b : bool =>
      if b then pure (eval η e2) ψ (⊥ : C → Prop)
      else ψ false) (⊥ : C → Prop) ->
  pure (eval η (EBoolConj e1 e2)) ψ (⊥ : C → Prop).
Proof.
  intros He. simpl_eval.
  eapply pure_bind_as_bool; eauto.
  intros [] Hb; eauto.
  eapply pure_ret; eauto with encode.
Qed.

(* EBoolDisj (e1 e2 : expr) *)

Lemma pure_eval_disj `{Encode C} η e1 e2 (φ1 φ2 ψ : bool -> Prop) :
  pure (eval η e1) φ1 (⊥ : C → Prop) →
  pure (eval η e2) φ2 (⊥ : C → Prop) →
  (φ1 true -> ψ true) ->
  (φ1 false -> forall b, φ2 b -> ψ b) ->
  pure (eval η (EBoolDisj e1 e2)) ψ (⊥ : C → Prop).
Proof.
  intros He1 He2 Ht Hf. simpl_eval.
  eapply pure_bind_as_bool; eauto.
  intros [] Hb.
  { eapply pure_ret; eauto with encode. }
  { specialize (Hf Hb).
    eapply pure_ret_mono; eauto. }
Qed.

(* Sequentialized version. *)

Lemma pure_eval_disj_seq `{Encode C} η e1 e2 (φ1 φ2 ψ : bool -> Prop) :
  pure (eval η e1)
    (fun b : bool =>
      if b then ψ true
      else pure (eval η e2) ψ (⊥ : C → Prop)) (⊥ : C → Prop) ->
  pure (eval η (EBoolDisj e1 e2)) ψ (⊥ : C → Prop).
Proof.
  intros He. simpl_eval.
  eapply pure_bind_as_bool; eauto.
  intros [] Hb; eauto.
  eapply pure_ret; eauto with encode.
Qed.

(* EBoolNeg (e : expr) *)

Lemma pure_eval_negb `{Encode C} η e (φ ψ : bool → Prop) :
  pure (eval η e) φ (⊥ : C → Prop) →
  (∀ b, φ b → ψ (negb b)) →
  pure (eval η (EBoolNeg e)) ψ (⊥ : C → Prop).
Proof.
  intros He Hp. simpl_eval.
  eapply pure_bind_as_bool; eauto.
  intros b Hb; eapply pure_ret; eauto with pure.
Qed.

Lemma pure_eval_not `{Encode C} η e (φ ψ : bool → Prop) :
  pure (eval η e) φ (⊥ : C → Prop) →
  (∀ P, φ P → ψ (negb P)) →
  pure (eval η (EBoolNeg e)) ψ (⊥ : C → Prop).
Proof.
  intros He Hp. simpl_eval.
  eapply pure_bind. by eapply pure_as_bool.
  intros. eapply pure_ret; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(** *Integer literals. *)

(* Helper lemmas for arithmetic operations. *)

Global Instance : Observe Z int := { observe := repr }.

Local Lemma pure_as_int `{Encode C} m (φ : Z → Prop) (ψ : C → Prop) :
  pure m φ ψ →
  pure (as_int m) φ ψ.
Proof.
  intros Hm; eapply pure_bind; eauto.
  intros; eapply pure_ret; eauto.
Qed.

(* EInt (i : Z) *)

Lemma pure_eval_int `{Encode C} η i (φ : Z -> Prop) (ψ : C → Prop) :
  φ i ->
  pure (eval η (EInt i)) φ ψ.
Proof.
  intros.
  simpl_eval.
  eapply pure_ret; eauto.
Qed.

(* EMaxInt *)

Lemma pure_eval_maxint `{Encode C} η (ψ : C → Prop) :
  pure (eval η EMaxInt) (singleton (int.repr int.max_signed)) ψ.
Proof.
  simpl_eval.
  eapply pure_ret; eauto.
Qed.

(* EMinInt *)

Lemma pure_eval_minint `{Encode C} η (ψ : C → Prop) :
  pure (eval η EMinInt) (singleton (int.repr int.min_signed)) ψ.
Proof.
  simpl_eval.
  eapply pure_ret; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(** *Integer arithmetic. *)

Lemma pure_par_as_int `{Encode B} m1 m2 (φ1 φ2 : Z → Prop) (φ : Z * Z → Prop) (ζ : B → Prop):
  pure m1 φ1 ζ →
  pure m2 φ2 ζ →
  (∀ z1 z2 : Z, φ1 z1 → φ2 z2 → φ (z1, z2)) →
  pure (par (as_int m1) (as_int m2)) φ ζ.
Proof.
  intros Hm1 Hm2 Hk.
  eapply pure_par; eauto.
  - unfold as_int.
    eapply pure_bind. apply Hm1.
    intros a Hφ. eapply pure_ret; encode.
  - unfold as_int.
    eapply pure_bind. apply Hm2.
    intros a Hφ. eapply pure_ret; encode.
Qed.

(* If [z] is representable and [z ≠ 0] then the runtime check *)
(*   performed by [check_div_by_zero (repr z)] must succeed. *)

Lemma pure_check_div_by_zero `{Encode B} z (ζ : B → Prop) :
  representable z →
  (z ≠ 0)%Z →
  pure (check_div_by_zero (repr z)) (λ v, v = ()) ζ.
Proof.
  intros.
  unfold check_div_by_zero.
  change int.zero with (repr 0).
  rewrite eq_repr_repr by representable.
  case_eq (z =? 0)%Z; [ rewrite Z.eqb_eq | rewrite Z.eqb_neq ]; intro.
  { tauto. }
  { by eapply pure_ret. }
Qed.

(* Primitive arithmetic operations. *)

(* EIntNeg (e : expr) *)
Lemma pure_eval_neg `{Encode B} η e (φ φe : Z -> Prop) (ζ : B → Prop) :
  pure (eval η e) φe ζ ->
  (forall z, φe z -> φ (- z)) ->
  pure (eval η (EIntNeg e)) φ ζ.
Proof.
  intros. simpl_eval.
  eapply pure_bind.
  eapply pure_as_int; eauto.
  intros i Hφe.
  eapply pure_ret; encode.
Qed.

(* EIntAdd (e1 e2 : expr) *)
Lemma pure_eval_add `{Encode B} η e1 e2 (φ1 φ2 φ : Z → Prop) (ζ : B → Prop) :
  pure (eval η e1) φ1 ζ →
  pure (eval η e2) φ2 ζ →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 + z2)) →
  pure (eval η (EIntAdd e1 e2)) φ ζ.
Proof.
  intros. simpl_eval. eapply pure_bind.
  instantiate (1:= λ '(z1, z2), φ (z1 + z2)).
  eapply pure_par_as_int; eauto.
  intros (i1, i2) Hφ.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntSub (e1 e2 : expr) *)
Lemma pure_eval_sub `{Encode B} η e1 e2 (φ1 φ2 φ : Z → Prop) (ζ : B → Prop) :
  pure (eval η e1) φ1 ζ →
  pure (eval η e2) φ2 ζ →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 - z2)) →
  pure (eval η (EIntSub e1 e2)) φ ζ.
Proof.
  intros. simpl_eval. eapply pure_bind.
  instantiate (1:= λ '(z1, z2), φ (z1 - z2)).
  eapply pure_par_as_int; eauto.
  intros (i1, i2) Hφ.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntMul (e1 e2 : expr) *)
Lemma pure_eval_mul `{Encode B} η e1 e2 (φ1 φ2 φ : Z → Prop) (ζ : B → Prop) :
  pure (eval η e1) φ1 ζ →
  pure (eval η e2) φ2 ζ →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 * z2)) →
  pure (eval η (EIntMul e1 e2)) φ ζ.
Proof.
  intros. simpl_eval. eapply pure_bind.
  instantiate (1:= λ '(z1, z2), φ (z1 * z2)).
  eapply pure_par_as_int; eauto.
  intros (i1, i2) Hφ.
  eapply pure_ret; eauto with encode.
Qed.

(* Import for "^~" notation. *)
From Stdlib Require Import ssrfun.

(* EIntDiv (e1 e2 : expr) *)
Lemma pure_eval_div `{Encode B} η e1 e2 (φ1 φ2 φ : Z → Prop) (ζ : B → Prop) :
  pure (eval η e1) φ1 ζ →
  pure (eval η e2) φ2 ζ →
  (∀ z1, φ1 z1 → representable z1) →
  (∀ z2, φ2 z2 → representable z2) →
  (∀ z2, φ2 z2 → z2 ≠ 0) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 ÷ z2)) →
  pure (eval η (EIntDiv e1 e2)) φ ζ.
Proof.
  intros. simpl_eval. eapply pure_bind.
  instantiate (1:= λ '(z1, z2), φ1 z1 ∧ φ2 z2).

  eapply pure_par_as_int; eauto.
  intros (i1, i2) (Hφ1 & Hφ2).
  eapply pure_bind.
  - apply pure_check_div_by_zero; eauto.
  - intros [] [].
    eapply pure_ret; last eauto.
    encode.
Qed.

(* EIntMod (e1 e2 : expr) *)
Lemma pure_eval_mod `{Encode B} η e1 e2 (φ1 φ2 φ : Z -> Prop) (ζ : B → Prop) :
  pure (eval η e1) φ1 ζ ->
  pure (eval η e2) φ2 ζ ->
  (∀ z1, φ1 z1 → representable z1) →
  (∀ z2, φ2 z2 → representable z2) →
  (∀ z2, φ2 z2 → z2 ≠ 0) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (z1 `rem` z2)) →
  pure (eval η (EIntMod e1 e2)) φ ζ.
Proof.
  intros. simpl_eval. eapply pure_bind.
  instantiate (1:= λ '(z1, z2), φ1 z1 ∧ φ2 z2).

  eapply pure_par_as_int; eauto.
  intros (i1, i2) (Hφ1 & Hφ2).
  eapply pure_bind.
  - apply pure_check_div_by_zero; eauto.
  - intros [] [].
    eapply pure_ret; last eauto.
    encode.
Qed.

(* -------------------------------------------------------------------------- *)

(** Integer logical operations. *)

(* Helper lemma for primitive arithmetic operations. *)

Local Lemma pure_if_in_shift_range {E} `{Encode C} `{Observe C E}
  z (m : micro val E) (φ : Z → Prop) (ψ : C → Prop) :
  in_shift_range z →
  pure m φ ψ →
  pure (A := Z) (V := val) (E := E)
    (if_in_shift_range (repr z) m) φ ψ.
Proof.
  intros.
  unfold if_in_shift_range, in_shift_range_b.
  rewrite signed_repr by eauto using in_shift_range_representable.
  by rewrite in_shift_range_b_spec.
Qed.

(* Primitive logical operations on machine integers. *)

(* EIntLand (e1 e2 : expr) *)

Lemma pure_eval_land `{Encode B} η e1 e2 (φ1 φ2 φ : Z → Prop) (ζ : B → Prop) :
  pure (eval η e1) φ1 ζ →
  pure (eval η e2) φ2 ζ →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.land z1 z2)) →
  pure (eval η (EIntLand e1 e2)) φ ζ.
Proof.
  intros. simpl_eval.
  eapply pure_bind.
  { instantiate (1:=λ '(z1,z2), φ (Z.land z1 z2)).
    eapply pure_par_as_int; eauto. }
  intros [??] ?.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntLor  (e1 e2 : expr) *)

Lemma pure_eval_lor `{Encode B} η e1 e2 (φ1 φ2 φ : Z → Prop) (ζ : B → Prop) :
  pure (eval η e1) φ1 ζ →
  pure (eval η e2) φ2 ζ →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.lor z1 z2)) →
  pure (eval η (EIntLor e1 e2)) φ ζ.
Proof.
  intros. simpl_eval.
  eapply pure_bind.
  { instantiate (1:=λ '(z1,z2), φ (Z.lor z1 z2)).
    eapply pure_par_as_int; eauto. }
  intros [??] ?.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntLxor (e1 e2 : expr) *)

Lemma pure_eval_lxor `{Encode B} η e1 e2 (φ1 φ2 φ : Z → Prop) (ζ : B → Prop) :
  pure (eval η e1) φ1 ζ →
  pure (eval η e2) φ2 ζ →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.lxor z1 z2)) →
  pure (eval η (EIntLxor e1 e2)) φ ζ.
Proof.
  intros. simpl_eval.
  eapply pure_bind.
  { instantiate (1:=λ '(z1,z2), φ (Z.lxor z1 z2)).
    eapply pure_par_as_int; eauto. }
  intros [??] ?.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntLnot (e : expr) *)

Lemma pure_eval_lnot `{Encode B} η e1 (φ1 φ : Z → Prop) (ζ : B → Prop) :
  pure (eval η e1) φ1 ζ →
  (∀ z1, φ1 z1 → φ (Z.lnot z1)) →
  pure (eval η (EIntLnot e1)) φ ζ.
Proof.
  intros He1%pure_as_int Hp. simpl_eval.
  eapply pure_bind; eauto. intros ??.
  eapply pure_ret; eauto.
  encode.
Qed.

(* EIntLsl  (e1 e2 : expr) *)

Lemma pure_eval_lsl `{Encode B} η e1 e2 (φ1 φ2 φ : Z → Prop) (ζ : B → Prop) :
  pure (eval η e1) φ1 ζ →
  pure (eval η e2) φ2 ζ →
  (∀ z1, φ1 z1 → representable z1) →
  (∀ z2, φ2 z2 → in_shift_range z2) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftl z1 z2)) →
  pure (eval η (EIntLsl e1 e2)) φ ζ.
Proof.
  intros. simpl_eval.
  eapply pure_bind.
  { instantiate (1:=λ '(z1,z2), φ1 z1 ∧ φ2 z2).
    eapply pure_par_as_int; eauto. }
  intros [??] [??].
  apply pure_if_in_shift_range; auto.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntLsr  (e1 e2 : expr) *)

Lemma pure_eval_lsr `{Encode B} η e1 e2 (φ1 φ2 φ : Z → Prop) (ζ : B → Prop) :
  pure (eval η e1) φ1 ζ →
  pure (eval η e2) φ2 ζ →
  (∀ z1, φ1 z1 → urepresentable z1) →
  (∀ z2, φ2 z2 → in_shift_range z2) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftr z1 z2)) →
  pure (eval η (EIntLsr e1 e2)) φ ζ.
Proof.
  intros. simpl_eval.
  eapply pure_bind.
  { instantiate (1:=λ '(z1,z2), φ1 z1 ∧ φ2 z2).
    eapply pure_par_as_int; eauto. }
  intros [??] [??].
  apply pure_if_in_shift_range; auto.
  eapply pure_ret; eauto with encode.
Qed.

(* EIntAsr  (e1 e2 : expr) *)

Lemma pure_eval_asr `{Encode B} η e1 e2 (φ1 φ2 φ : Z → Prop) (ζ : B → Prop) :
  pure (eval η e1) φ1 ζ →
  pure (eval η e2) φ2 ζ →
  (∀ z1, φ1 z1 → representable z1) →
  (∀ z2, φ2 z2 → in_shift_range z2) →
  (∀ z1 z2, φ1 z1 → φ2 z2 → φ (Z.shiftr z1 z2)) →
  pure (eval η (EIntAsr e1 e2)) φ ζ.
Proof.
  intros. simpl_eval.
  eapply pure_bind.
  { instantiate (1:=λ '(z1,z2), φ1 z1 ∧ φ2 z2).
    eapply pure_par_as_int; eauto. }
  intros [??] [??].
  apply pure_if_in_shift_range; auto.
  eapply pure_ret; eauto with encode.
Qed.

(* -------------------------------------------------------------------------- *)

(** Floating-point literals. *)

(* EFloat (f : float) *)
Lemma pure_eval_float `{Encode B} η f (φ : _ -> Prop) (ζ : B → Prop) :
  φ f ->
  pure (eval η (EFloat f)) φ ζ.
Proof.
  intros.
  simpl_eval.
  eapply pure_ret; eauto.
Qed.

(** Character literals. *)

(* EChar (c: char) *)
Lemma pure_eval_char `{Encode B} η c (φ : _ -> Prop) (ζ : B → Prop) :
  φ c ->
  pure (eval η (EChar c)) φ ζ.
Proof.
  intros.
  simpl_eval.
  eapply pure_ret; eauto.
Qed.

(** String literals. *)

(* EString (s: string) *)
Lemma pure_eval_string `{Encode B} η s (φ : _ -> Prop) (ζ : B → Prop) :
  φ s ->
  pure (eval η (EString s)) φ ζ.
Proof.
  intros.
  simpl_eval.
  eapply pure_ret; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(** Polymorphic comparison operators. *)

(* Helper lemma for Boolean operations *)

Lemma pure_eval_comparison_operator `{Encode A1, Encode A2} `{Encode B}
  η e1 e2 (x1 : A1) (x2 : A2) (f : val → val → micro bool exn) a (φ : bool → Prop) (ζ : B → Prop) :
  pure (eval η e1) (singleton x1) ζ →
  pure (eval η e2) (singleton x2) ζ →
  f #x1 #x2 = ret a →
  φ a →
  pure ('(v1, v2) ← par (eval η e1) (eval η e2);
        b ← f v1 v2;
        ret (VBool b)) φ ζ.
Proof.
  intros He1 He2 Ef Ha.
  eapply pure_bind. instantiate (1:=λ '(v1, v2), v1 = x1 ∧ v2 = x2).
  { eapply pure_par; eauto. }
  intros [??] (-> & ->).
  eapply (pure_bind (A1:=bool)).
  { simpl. rewrite Ef.
    eapply pure_ret. encode. apply Ha. }
  intros ? Hφ.
  eapply pure_ret. encode. apply Hφ.
Qed.

(* Boolean operations *)

(* EOpPhysEq (e1 e2 : expr) *)

Lemma pure_eval_EOpPhysEq_loc `{Encode B} η e1 e2 (x1 x2 : loc) (ζ : B → Prop) :
  pure (eval η e1) (singleton x1) ζ ->
  pure (eval η e2) (singleton x2) ζ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1.(address) ->
  representable x2.(address) ->
  pure (eval η (EOpPhysEq e1 e2)) (λ b, b = locations.eqb x1 x2) ζ.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_bind. instantiate (1:= λ '(a1, a2), singleton x1 a1 ∧ singleton x2 a2).
  { eapply pure_par; eauto. }
  intros [??] [-> ->].
  eapply pure_ret; last reflexivity. encode.
Qed.

(* EOpEq (e1 e2 : expr) *)

Lemma pure_eval_EOpEq `{Encode B} η e1 e2 (x1 x2 : Z) (ζ : B → Prop) :
  pure (eval η e1) (singleton x1) ζ ->
  pure (eval η e2) (singleton x2) ζ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpEq e1 e2)) (λ b, b = (x1 =? x2)%Z) ζ.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite eq_repr_repr; auto.
Qed.

(* EOpNe (e1 e2 : expr) *)

Lemma pure_eval_EOpNe `{Encode B} η e1 e2 (x1 x2 : Z) (ζ : B → Prop) :
  pure (eval η e1) (singleton x1) ζ ->
  pure (eval η e2) (singleton x2) ζ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpNe e1 e2)) (λ b, b = negb (x1 =? x2)%Z) ζ.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite eq_repr_repr; auto.
Qed.

(* EOpLt (e1 e2 : expr) *)

Lemma pure_eval_EOpLt `{Encode B} η e1 e2 (x1 x2 : Z) (ζ : B → Prop) :
  pure (eval η e1) (singleton x1) ζ ->
  pure (eval η e2) (singleton x2) ζ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLt e1 e2)) (λ b, b = (x1 <? x2)%Z) ζ.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto.
Qed.

(* EOpLe (e1 e2 : expr) *)

Lemma pure_eval_EOpLe `{Encode B} η e1 e2 (x1 x2 : Z) (ζ : B → Prop) :
  pure (eval η e1) (singleton x1) ζ ->
  pure (eval η e2) (singleton x2) ζ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpLe e1 e2)) (λ b, b = (x1 <=? x2)%Z) ζ.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto.
  by rewrite Z.leb_antisym.
Qed.

(* EOpGt (e1 e2 : expr) *)

Lemma pure_eval_EOpGt `{Encode B} η e1 e2 (x1 x2 : Z) (ζ : B → Prop) :
  pure (eval η e1) (singleton x1) ζ ->
  pure (eval η e2) (singleton x2) ζ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpGt e1 e2)) (λ b, b = (x1 >? x2)%Z) ζ.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto.
  by rewrite Z.gtb_ltb.
Qed.

(* EOpGe (e1 e2 : expr) *)

Lemma pure_eval_EOpGe `{Encode B} η e1 e2 (x1 x2 : Z) (ζ : B → Prop) :
  pure (eval η e1) (singleton x1) ζ ->
  pure (eval η e2) (singleton x2) ζ ->
  (* Representability hypotheses last for [x1] and [x2] evar initialisation *)
  representable x1 ->
  representable x2 ->
  pure (eval η (EOpGe e1 e2)) (λ b, b = (x1 >=? x2)%Z) ζ.
Proof.
  intros He1 He2 Hx1 Hx2. simpl_eval.
  eapply pure_eval_comparison_operator; eauto.
  rewrite lt_repr_repr; auto.
  lia.
Qed.

(* -------------------------------------------------------------------------- *)

(** Non-recursive local definition: [let bs in e]. *)

(* ELet (bs : list binding) (e : expr) *)

Lemma pure_eval_let `{Encode A, Encode B} η bs e (φ : A → Prop) (ψ : B → Prop) :
  bindings η bs (λ δ, pure (eval (δ ++ η) e) φ ψ) ψ →
  pure (eval η (ELet bs e)) φ ψ.
Proof.
  intros Hbs.
  simpl_eval.
  eapply pure_bind_unary.
  eapply pure_ret_mono; [ apply Hbs | ].
  intros η' He. apply He.
Qed.

Lemma pure_eval_let1 `{Encode A, Encode B, Encode C} η p e1 e (φ : B → Prop) (ψ : C → Prop) :
  pure (eval η e1) (λ a : A, pattern η [] p #a (λ δ, pure (eval (δ ++ η) e) φ ψ) False) ψ →
  pure (eval η (ELet1 p e1 e)) φ ψ.
Proof.
  intros He1.
  eapply pure_eval_let.
  eapply bindings_cons. apply He1.
  eapply bindings_nil. apply eq_refl.
  intros a η'.
  intros Hpat <-.
  apply Hpat.
Qed.

Lemma pure_eval_let1_conseq `{Encode A, Encode B, Encode C} η p e1 e (φ1 : A → Prop) (φ : B → Prop) (ψ : C → Prop) :
  pure (eval η e1) φ1 ψ →
  (∀ a : A, φ1 a → pattern η [] p #a (λ δ, pure (eval (δ ++ η) e) φ ψ) False) →
  pure (eval η (ELet1 p e1 e)) φ ψ.
Proof.
  intros He1 Hp.
  eapply pure_eval_let1.
  eapply pure_mono; eauto.
Qed.

(* slightly nicer versions for let1 where there is no environment concatenation *)
Lemma pure_eval_let1_extend `{Encode A, Encode B, Encode C} η p e1 e (φ : B → Prop) (ψ : C → Prop) :
  pure (eval η e1) (λ a : A, pattern η η p #a (λ η', pure (eval η' e) φ ψ) False) ψ →
  pure (eval η (ELet1 p e1 e)) φ ψ.
Proof.
  intros He1.
  eapply pure_eval_let1, (pure_ret_mono _ _ _ _ He1); intros a Ha.
  rewrite pattern_app in Ha.
  assumption.
Qed.

Lemma pure_eval_let1_extend_conseq `{Encode A, Encode B, Encode C} η p e1 e (φ1 : A → Prop) (φ : B → Prop) (ψ : C → Prop) :
  pure (eval η e1) φ1 ψ →
  (∀ a : A, φ1 a → pattern η η p #a (λ η', pure (eval η' e) φ ψ) False) →
  pure (eval η (ELet1 p e1 e)) φ ψ.
Proof.
  intros He1 Hp.
  eapply pure_eval_let1_extend.
  eapply pure_mono; eauto.
Qed.

Lemma pure_eval_let1var `{Encode A1, Encode B} `{Encode C} η x e1 e
  (φ1 : A1 → Prop) (ψ : B → Prop) (ζ : C → Prop) :
  pure (eval η e1) φ1 ζ →
  (∀ a1, φ1 a1 → pure (eval ((x, #a1) :: η) e) ψ ζ) →
  pure (eval η (ELet1Var x e1 e)) ψ ζ.
Proof.
  intros He1 He.
  simpl_eval.
  do 2 eapply pure_bind_unary.
  eapply pure_par.
  - exact He1.
  - eapply (pure_ret (A:=env)); [ encode | apply eq_refl ].
  - intros a1 ? Hφ1 <-.
    simpl. apply pure_irrefutably_extend.
    apply pat_PVar. simpl.
    rewrite bind_ret. apply He. exact Hφ1.
  Unshelve. all: exact _.
Qed.

Lemma pure_eval_let_simple `{Encode A1, Encode B} `{Encode C} η x e1 e
  (a1 : A1) (ψ : B → Prop) (ζ : C → Prop) :
  pure (eval η e1) (singleton a1) ζ →
  pure (eval ((x, #a1) :: η) e) ψ ζ →
  pure (eval η (ELet1Var x e1 e)) ψ ζ.
Proof.
  intros He1 He2.
  eapply pure_eval_let1var; eauto.
  congruence.
Qed.

Lemma pure_eval_let_pair `{Encode A1, Encode A2} `{Encode X} `{Encode C} (φ_pair : τ[A1;A2] → Prop)
  p1 p2 e1 e2 η φ (ψ : X -> Prop) (ζ : C → Prop) :
  pure (eval η e1) φ_pair ζ →
  (∀ δ, φ δ → pure (eval (δ ++ η) e2) ψ ζ) →
  (∀# (ab : τ[A1;A2]), φ_pair ab → pattern η [] (PPair p1 p2) #ab φ False) →
  pure (eval η (ELet1 (PPair p1 p2) e1 e2)) ψ ζ.
Proof.
  intros He1 He2 Hpat. simpl_eval.
  do 2 eapply pure_bind_unary.
  eapply pure_par. apply He1.
  eapply (pure_ret (A:=env)); [ encode | apply eq_refl ].
  intros (a1, a2) ? Hpair <-.
  simpl. apply pure_irrefutably_extend.
  eapply pure_ret_mono.
  specialize (Hpat a1 a2 Hpair). apply Hpat.
  intros δ Hδ. rewrite bind_ret.
  apply He2, Hδ.
Qed.

(* -------------------------------------------------------------------------- *)

(** Recursive local definition: [let rbs in e]. *)
(* ELetRec (rbs : list rec_binding) (e : expr) *)

Lemma pure_letrec `{Encode X, Encode Y} `{Encode C} {A} (WF_x : WellFounded X)
  (η : env) (f arg : var) e1 e2 (φ : X -> Prop) (φf : A -> X -> Y -> Prop) (Ψ : C → Prop)
  (P : A -> X -> Prop) (R : X -> X -> Prop) :
  (* Subgoal:
     Assuming that any recursive call of [f] on a smaller argument
     satisfies [φf], show that evaluating [e1] satisfies [φf]. *)
  (∀ vf (x : X) a,
      (∀ (y : X),
          wf_relation (WF := WF_x) y x ->
          R y x -> P a y -> pure (call vf #y) (φf a y) Ψ) ->
      (P a x -> pure (eval ((arg, #x) :: (f, vf) :: η) e1) (φf a x) Ψ)) ->
  (* Subgoal:
     Proceed with the right hand of the [let rec],
     assuming f satisfies its spec. *)
  (∀ vf,
      (∀ a x, P a x -> pure (call vf #x) (φf a x) Ψ) ->
      pure (eval ((f, vf) :: η) e2) φ Ψ) ->
  pure (eval η (ELetRec [RecBinding f (AnonFun arg e1)] e2)) φ Ψ.
Proof.
  intros He1 He2.
  simpl_eval. apply He2; clear He2.
  intros a y HPy.
  eapply pure_rec_call; eauto.
Qed.

Lemma pure_letrec_simple `{Encode X, Encode Y} `{Encode C} (WF_x : WellFounded X)
  (η : env) (f arg : var) e1 e2 (φ : val -> Prop) (φf : X -> Y -> Prop) (Ψ : C → Prop)
  (P : X -> Prop) (R : X -> X -> Prop) :
  (* Subgoal:
     Assuming that any recursive call of [f] on a smaller argument
     satisfies [φf], show that evaluating [e1] satisfies [φf]. *)
  (∀ vf (x : X),
      (∀ (y : X),
          wf_relation (WF := WF_x) y x ->
          R y x -> P y -> pure (call vf #y) (φf y) Ψ) ->
      (P x -> pure (eval ((arg, #x) :: (f, vf) :: η) e1) (φf x) Ψ)) ->
  (* Subgoal:
     Proceed with the right hand of the [let rec],
     assuming f satisfies its spec. *)
  (∀ vf,
      (∀ x, P x -> pure (call vf #x) (φf x) Ψ) ->
      pure (eval ((f, vf) :: η) e2) φ Ψ) ->
  pure (eval η (ELetRec [RecBinding f (AnonFun arg e1)] e2)) φ Ψ.
Proof.
  intros He1 He2.
  simpl_eval. apply He2; clear He2.
  intros y HPy.
  eapply pure_rec_call; eauto.
Qed.

Lemma pure_rec_call_no_pre `{Encode X} `{Encode Y} `{WF_x: WellFounded X} `{Encode B}
  (η : env) (f arg : var) e1 e2 (φ : X -> Prop) (φf : X -> Y -> Prop)
  (R : X -> X -> Prop) (ζ : B → Prop) :
  (* Subgoal:
     Assuming that any recursive call of [f] on a smaller argument
     satisfies [φf], show that evaluating [e1] satisfies [φf]. *)
  (∀ vf (x : X),
      (∀ (y : X),
          wf_relation (WF := WF_x) y x ->
          R y x -> pure (call vf #y) (φf y) ζ) ->
      pure (eval ((arg, #x) :: (f, vf) :: η) e1) (φf x) ζ) ->
  (* Subgoal:
     Proceed with the right hand of the [let rec],
     assuming f satisfies its spec. *)
  (∀ vf,
      (∀ (x : X), pure (call vf #x) (φf x) ζ) ->
      pure (eval ((f, vf) :: η) e2) φ ζ) ->
  pure (eval η (ELetRec [RecBinding f (AnonFun arg e1)] e2)) φ ζ.
Proof.
  intros He1 He2.
  simpl_eval. apply He2. clear He2.
  intros y.
  eapply pure_rec_call with (P := fun _ => True); eauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Sequence: [e1; e2]. *)
(* ESeq (e1 e2 : expr) *)

(* Sequencing of pure computations. *)
Lemma pure_seq `{Encode A} `{Encode C} (φ : A -> Prop) (ψ : C → Prop) η e1 e2 :
  pure (eval η e1) (λ _ : (), pure (eval η e2) φ ψ) ψ →
  pure (eval η (ESeq e1 e2)) φ ψ.
Proof.
  simpl_eval.
  intros. eapply pure_bind.
  eapply pure_mono; try done.
  cbn; intros; eapply pure_mono; done.
Qed.

Lemma pure_eval_seq `{Encode A} `{Encode C}
  η e1 e2 (φ : A -> Prop) φ' (Ψ : C → Prop) :
  pure (eval η e1) (λ _ : (), φ') Ψ ->
  (φ' -> pure (eval η e2) φ Ψ) ->
  pure (eval η (ESeq e1 e2)) φ Ψ.
Proof.
  intros He1 He2.
  eapply (@pure_seq A).
  by eapply pure_mono.
Qed.

Lemma pure_eval_seq_void `{Encode A} `{Encode C}
  η e1 e2 (Ψ : A -> Prop) (ζ : C → Prop) :
  pure (eval η e1) (λ _ : (), pure (eval η e2) Ψ ζ) ζ ->
  pure (eval η (ESeq e1 e2)) Ψ ζ.
Proof.
  intros; eapply pure_seq; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(** Conditional: [if e then e1] and [if e then e1 else e2]. *)

(* EIfThen (e e1 : expr) *)

Lemma pure_ifthen `{Encode C}
  η e e1 φ (ψ : C -> Prop) :
  pure (A := bool) (eval η e)
    (λ b : bool, if b then pure (eval η e1) φ ψ else φ tt) ψ →
  pure (eval η (EIfThen e e1)) φ ψ.
Proof.
  intros He. simpl_eval.
  eapply pure_bind. eapply pure_as_bool; eauto.
  cbn; intros * He1. destruct a; eauto.
  eapply pure_ret; eauto with encode.
Qed.

Lemma pure_eval_ifthen `{Encode C}
  η e e1 φ (P : Prop) (Ψ : C -> Prop) :
  pure (eval η e) (λ P', P' <-> P) Ψ ->
  (P -> pure (eval η e1) φ Ψ) ->
  (~ P -> φ tt) ->
  pure (eval η (EIfThen e e1)) φ Ψ.
Proof.
  intros He He1 Hfail.
  eapply pure_ifthen.
  eapply pure_wp_mono; eauto.
  intros; returns_eauto.
  exists (truth P); cbn; split; auto.
  do 2 f_equiv; apply iff_truth; done.
  generalize (truth_elim P).
  destruct (truth P); eauto; intros; eauto.
Qed.

(* EIfThenElse (e e1 e2 : expr) *)

Lemma pure_ifthenelse `{EncA: Encode A} `{Encode C}
  η e e1 e2 φ (ψ : C -> Prop) :
  pure (A := bool) (eval η e)
    (λ b : bool, pure (eval η (if b then e1 else e2)) φ ψ) ψ →
  pure (A := A) (eval η (EIfThenElse e e1 e2)) φ ψ.
Proof.
  intros He. simpl_eval.
  eapply pure_bind. eapply pure_as_bool; eauto.
  cbn; intros * Hif. destruct a; eauto.
Qed.

Lemma pure_eval_ifthenelse `{EncA: Encode A} `{Encode C}
  η e e1 e2 (φ : A -> _) φb (ψ : C → Prop) :
  pure (eval η e) φb ψ →
  (φb true  → pure (eval η e1) φ ψ) →
  (φb false → pure (eval η e2) φ ψ) →
  pure (eval η (EIfThenElse e e1 e2)) φ ψ.
Proof.
  simpl; intros Hb Ht Hf; simpl_eval.
  eapply pure_bind. apply pure_as_bool; eauto.
  intros [] ?; eauto with pure.
Qed.

Lemma pure_eval_ifthenelse_prop `{EncA: Encode A} `{Encode C}
  η e e1 e2 (P : Prop) (ψ : A → Prop) (ζ : C → Prop) :
  pure (eval η e) (λ P', P' <-> P) ζ →
  (P → pure (eval η e1) ψ ζ) →
  (~ P → pure (eval η e2) ψ ζ) →
  pure (eval η (EIfThenElse e e1 e2)) ψ ζ.
Proof.
  intros He He1 He2.
  eapply pure_ifthenelse.
  eapply pure_wp_mono; eauto.
  intros; returns_eauto.
  exists (truth P); cbn; split; auto.
  do 2 f_equiv; apply iff_truth; done.
  generalize (truth_elim P).
  destruct (truth P); eauto; intros; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(** Pattern matching: [match e with bs]. *)

(* [branches η v bs φ] is sugar for [pure (eval_branches η v bs) ##φ ⊥].

  [eval_branches] is used by [eval] when evaluating an [EMatch]. *)

Definition branches `{Encode A} `{Encode C}
  (η : env) (o : outcome3 val exn) bs (φ : A -> Prop) (Ψ : C → Prop) :=
  pure (eval_branches η o bs) φ Ψ.

Arguments branches {A EncodeA C EncodeC} _ _ _ _ _ : rename.

(* Properties about [branches] *)

(* Currently unused *)

Lemma branches_cons_unary `{Encode A} `{Encode C} η o cp e bs (φ : A -> Prop) (ψ : C → Prop) :
  cpattern η η cp o (λ η', pure (eval η' e) φ ψ) (branches η o bs φ ψ) ->
  branches η o (Branch cp e :: bs) φ ψ.
Proof.
  unfold branches.
  intros Hcpat. simpl_eval_branches.
  eapply pure_try2. apply Hcpat.
  - intros η' He.
    unfold continue. apply He.
  - intros [] Hbranches.
    unfold discontinue. apply Hbranches.
Qed.

Lemma branches_cons `{Encode A} `{Encode C} η o cp e bs (φ : A -> Prop) ψ' (ψ : C → Prop) :
  cpattern η η cp o (λ η', pure (eval η' e) φ ψ) ψ' ->
  (ψ' -> (branches η o bs φ ψ)) ->
  branches η o (Branch cp e :: bs) φ ψ.
Proof.
  intros Hcpat Hbranch.
  apply branches_cons_unary.
  eapply pure_exn_mono; [ apply Hcpat | intros [] Hψ; exact (Hbranch Hψ) ].
Qed.

(* Not matching a value is an error. *)

Lemma branches_val_nil `{Encode A} `{Encode C} η v (φ : A -> Prop) (Ψ : C → Prop) :
  False -> branches η (O2Ret v) nil φ Ψ.
Proof. contradiction. Qed.

(* Not matching an exception propagates the exception. *)

Lemma branches_exn_nil `{Encode A} η e (φ : A -> Prop) (Ψ : exn -> Prop) :
  Ψ e ->
  branches η (O2Throw e) nil φ Ψ.
Proof.
  intro HΨ. unfold branches. simpl_eval_branches.
  eapply pure_throw; [ encode | exact HΨ ].
Qed.

Lemma branches_single `{Encode A} `{Encode C} η v cp e (φ : A -> Prop) ψ (ζ : C → Prop) :
  cpattern η η cp v (λ η' : env, pure (eval η' e) φ ζ) ψ →
  (ψ -> False) ->
  branches η v [Branch cp e] φ ζ.
Proof.
  intros.
  eapply branches_cons; eauto.
  tauto.
Qed.

(* EMatch (e : expr) (bs : list branch) *)

Lemma pure_eval_match `{Encode A, Encode B} `{Encode C} η e bs (a : A) (φ : B -> Prop) (Ψ : C → Prop) :
  pure (eval η e) (singleton a) (⊥ : C → Prop) ->
  branches η (O3Ret #a) bs φ Ψ ->
  pure (eval η (EMatch e bs)) φ Ψ.
Proof.
  intros Heval Hmatch. simpl_eval.
  apply pure_wp_handle.
  apply (pure_wp_mono _ Heval); [ | intros ? (? & _ & []) ].
  intros ? (? & -> & ->).
  unfold continue. simpl_wrap_eval_branches.
  apply (pure_wp_mono _ Hmatch); eauto.
Qed.

Lemma pure_eval_match' `{Encode A, Encode B} `{Encode C} η e bs (φ : B -> Prop) (φ' : A -> Prop) (Ψ : C → Prop) :
  pure (eval η e) φ' (⊥ : C → Prop) ->
  (∀ (a : A), φ' a -> branches η (O3Ret #a) bs φ Ψ) ->
  pure (eval η (EMatch e bs)) φ Ψ.
Proof.
  intros Heval Hmatch. simpl_eval.
  apply pure_wp_handle.
  apply (pure_wp_mono _ Heval). 2: intros ? (? & _ & []).
  intros ? (a & -> & Ha).
  unfold continue. simpl_wrap_eval_branches.
  apply (pure_wp_mono _ (Hmatch _ Ha)); eauto.
Qed.

Lemma pure_eval_match'_exn `{Encode A, Encode B} `{Encode C, Encode D} η e bs (φ : B -> Prop) (φ' : A -> Prop) (ζ : D → Prop) (Ψ : C → Prop) :
  pure (eval η e) φ' ζ ->
  (∀ (a : A), φ' a -> branches η (O3Ret #a) bs φ Ψ) ->
  (∀ (ex : D), ζ ex -> branches η (O3Throw #ex) bs φ Ψ) ->
  pure (eval η (EMatch e bs)) φ Ψ.
Proof.
  intros He Hφ' Hζ.
  simpl_eval.
  apply pure_wp_handle.
  apply (pure_wp_mono _ He).
  - intros _v (a & -> & Ha).
    unfold continue. simpl_wrap_eval_branches.
    by apply Hφ'.
  - intros ex (c & -> & Hex).
    unfold discontinue. simpl_wrap_eval_branches.
    apply (Hζ _ Hex).
Qed.

(* -------------------------------------------------------------------------- *)

(** Raising an exception: [raise e]. *)

(* ERaise (e : expr) *)

Lemma pure_eval_raise `{Encode A} `{Encode C} η e (φ : A -> Prop) (ζ : C → Prop) :
  pure (eval η e) ζ ζ ->
  pure (eval η (ERaise e)) φ ζ.
Proof.
  intros Heval. simpl_eval.
  eapply pure_bind.
  eapply pure_exn_mono; eauto.
  intros a Ha. cbn. eapply pure_throw; [ encode | exact Ha ].
Qed.

(* -------------------------------------------------------------------------- *)

(** *Effectful expressions on [pure]. *)

(* For impure expressions that fell under the hood, we provide some
  "trivial" lemmas that warn the users that something has gone wrong. *)

Definition NOT_PURE (s : string) : Prop := False.

(** Performing an effect: [perform e]. *)

(* EPerform (e : expr) *)
Lemma pure_eval_perform `{Encode A} `{Encode C} η e (φ : _ -> Prop) (ζ : C → Prop) :
  NOT_PURE "[EPerform] is effectful; cannot be resolved with [pure]" ->
  pure (A := A) (eval η (EPerform e)) φ ζ.
Proof. done. Qed.

(** Continuing a continuation: [continue e1 e2]. *)

(* EContinue (e1 : expr) (e2 : expr) *)
Lemma pure_eval_continue `{Encode A} `{Encode C} η e1 e2 (φ : _ -> Prop) (ζ : C → Prop) :
  NOT_PURE "[EContinue] is effectful; cannot be resolved with [pure]" ->
  pure (A := A) (eval η (EContinue e1 e2)) φ ζ.
Proof. done. Qed.

(** Discontinuing a continuation: [discontinue e1 e2]. *)

(* EDiscontinue (e1 : expr) (e2 : expr) *)
Lemma pure_eval_discontinue `{Encode A} `{Encode C} η e1 e2 (φ : _ -> Prop) (ζ : C → Prop) :
  NOT_PURE "[EDiscontinue] is effectful; cannot be resolved with [pure]" ->
  pure (A := A) (eval η (EDiscontinue e1 e2)) φ ζ.
Proof. done. Qed.

(** Loop: [while e do body done]. *)
(* EWhile (e body : expr) *)

(* Loop: [for x = e1 to e2 do e done]. *)

Lemma pure_eval_loop_false `{Encode C} η e body (φ : _ -> Prop) (ζ : C → Prop) :
  φ () ->
  pure (eval η e) (singleton false) ζ ->
  pure (eval η (EWhile e body)) φ ζ.
Proof.
  intros Hφ Hfalse. simpl_eval.
  eapply pure_bind.
  { by apply pure_as_bool. }
  intros * ->; cbn; eauto.
  eapply pure_ret; cbn; eauto with pure.
  reflexivity.
Qed.

Lemma pure_eval_loop_true `{Encode C} η e body (φ : _ -> Prop) (ζ : C → Prop) :
  NOT_PURE "[EWhile] with a true guard is effectful; cannot be resolved with [pure]" ->
  pure (eval η e) (singleton true) ζ ->
  pure (A := unit) (eval η (EWhile e body)) φ ζ.
Proof. done. Qed.

(* EFor (x : var) (e1 e2 e : expr) *)

Lemma pure_eval_for `{Encode C} η x e1 e2 e (φ : _ -> Prop) (ζ : C → Prop) :
  NOT_PURE "[EFor] is effectful; cannot be resolved with [pure]" ->
  pure (A := unit) (eval η (EFor x e1 e2 e)) φ ζ.
Proof. done. Qed.

(* Fatal error: [assert false]. *)
(* We model OCaml's unreachable construct [.] in this way, too. *)

(* EAssertFalse *)

Lemma pure_eval_assertfalse `{Encode C} η (φ : _ -> Prop) (ζ : C → Prop) :
  NOT_PURE "[EAssertFalse] : Program has crashed" ->
  pure (A := unit) (eval η EAssertFalse) φ ζ.
Proof. done. Qed.

(* Reference allocation: [ref e]. *)

(* ERef (e: expr) *)

Lemma pure_eval_ref `{Encode A} `{Encode C} η e (φ : _ -> Prop) (ζ : C → Prop) :
  NOT_PURE "[ERef] is effectful; cannot be resolved with [pure]" ->
  pure (A := A) (eval η (ERef e)) φ ζ.
Proof. done. Qed.

(* Reference lookup: [!e]. *)

(* ELoad (e: expr) *)

Lemma pure_eval_load `{Encode A} `{Encode C} η e (φ : _ -> Prop) (ζ : C → Prop) :
  NOT_PURE "[ELoad] is effectful; cannot be resolved with [pure]" ->
  pure (A := A) (eval η (ELoad e)) φ ζ.
Proof. done. Qed.

(* Reference assignment: [e1 := e2]. *)

(* EStore (e1 e2: expr) *)

Lemma pure_eval_store `{Encode A} `{Encode C} η e1 e2 (φ : _ -> Prop) (ζ : C → Prop) :
  NOT_PURE "[EStore] is effectful; cannot be resolved with [pure]" ->
  pure (A := A) (eval η (EStore e1 e2)) φ ζ.
Proof. done. Qed.

(* Load from a field location: [Atomic.Loc.get e]. *)

(* EFieldLoad (e: expr) *)

Lemma pure_eval_field_load `{Encode A} `{Encode C} η e (φ : _ -> Prop) (ζ : C → Prop) :
  NOT_PURE "[EFieldLoad] is effectful; cannot be resolved with [pure]" ->
  pure (A := A) (eval η (EFieldLoad e)) φ ζ.
Proof. done. Qed.

(* -------------------------------------------------------------------------- *)

(** Runtime assertion: [assert(e)]. *)

(* EAssert (e : expr) *)

(* Runtime assertions. *)

Lemma pure_assert `{Encode B} η e (ψ : B → Prop) :
  pure (eval η e) (singleton true) ψ →
  pure (eval η (EAssert e)) (singleton ()) ψ.
Proof.
  intros He. simpl_eval.
  apply pure_choose.
  - eapply pure_ret; eauto. encode.
  - eapply pure_bind. eapply pure_as_bool; eauto.
    intros _ ->. cbn.
    eapply pure_ret; eauto. encode.
Qed.

Lemma pure_eval_assert_bool `{Encode C} η e :
  pure (eval η e) (singleton true) (⊥ : C → Prop) →
  pure (eval η (EAssert e)) (λ (_ : unit), True) (⊥ : C → Prop).
Proof.
  intros He. eapply pure_mono.
  eapply pure_assert. all: done.
Qed.

Lemma pure_eval_assert_Prop `{Encode C} η e :
  pure (eval η e) (λ P : Prop, P) (⊥ : C → Prop) →
  pure (eval η (EAssert e)) (λ (_ : unit), True) (⊥ : C → Prop).
Proof.
  intros He. eapply pure_mono.
  eapply pure_assert.
  eapply pure_wp_mono; first eapply He; eauto.
  all: try done.
  intros; returns_eauto; cbn; eauto.
  repeat econstructor. rewrite truth_true; eauto.
Qed.
