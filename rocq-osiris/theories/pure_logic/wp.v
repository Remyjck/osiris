From Stdlib Require Import Program.Equality.
From osiris Require Import base lang.
From stdpp Require Import relations.
From osiris.semantics Require Import code step eval pure.

(** This file defines the [pure_wp] predicate and its properties, which is used
  to state judgements about pure computations. *)

(* -------------------------------------------------------------------------- *)
(** The [pure_wp] predicate *)

(* [pure_wp m φ ψ] states that [m] is either a value satisfying [φ], a raised
exception satisfying [ψ], or can only do pure [may] reduction steps to states
[m'] also satisfying [pure m' φ ψ]. It is somewhat a terminating and pure
version of the standard WP. *)

Inductive pure_wp {A E} : micro A E → (A → Prop) → (E → Prop) → Prop :=
  | pure_wp_ret (φ : A → Prop) ψ a : φ a → pure_wp (ret a) φ ψ
  | pure_wp_throw φ (ψ : E → Prop) e : ψ e → pure_wp (throw e) φ ψ
  | pure_wp_may φ ψ m :
    (∃ m', may m m') →
    (∀ m', may m m' → pure_wp m' φ ψ) →
    pure_wp m φ ψ.

Create HintDb pure.
Global Hint Constructors pure_wp : pure.

(* -------------------------------------------------------------------------- *)
(** Specifications *)

(* [singleton x] is equivalent to a singleton set containing the element [x]. *)
Definition singleton {A} (a : A) : A → Prop := λ x, x = a.

Lemma singleton_eq {A} (a : A) :
  singleton a a.
Proof. reflexivity. Qed.

Global Hint Resolve singleton_eq : core.

(* Bottom instance for predicates, so we can write [⊥] for [λ _, False],
typically for disallowing exceptions *)

Global Instance Pred_bottom {A} : Bottom (A → Prop) := λ _, False.

(* -------------------------------------------------------------------------- *)

(** *Basic properties about [pure_wp]. *)


Section pure_wp_rules.

  (* Returning a single element satisfies the [singleton] predicate that
     contains the same element. *)
  Lemma pure_wp_ret_singleton {A E} (a : A) ψ :
    pure_wp (E := E) (ret a) (singleton a) ψ.
  Proof.
    intros; eapply pure_wp_ret; eauto.
  Qed.

  (** [pure_wp] is monotonic *)

  Lemma pure_wp_mono {A E} {φ φ' ψ ψ' : _ -> Prop} (m : micro A E) :
    pure_wp m φ ψ →
    (∀ a, φ a → φ' a) →
    (∀ e, ψ e → ψ' e) →
    pure_wp m φ' ψ'.
  Proof.
    induction 1; constructor; auto.
  Qed.

  Lemma pure_wp_mono_ret {A E} {φ φ' ψ : _ → Prop} (m : micro A E) :
    pure_wp m φ ψ → (∀ a, φ a → φ' a) → pure_wp m φ' ψ.
  Proof.
    induction 1; constructor; auto.
  Qed.

  Lemma pure_wp_ret_equiv {A E φ φ' ψ} (m : micro A E) :
    (∀ a, φ a ↔ φ' a) → pure_wp m φ ψ ↔ pure_wp m φ' ψ.
  Proof.
    intros; split; intros; eapply pure_wp_mono_ret; firstorder eauto.
  Qed.

  Lemma pure_wp_mono_throw {A E} {φ ψ ψ' : _ → Prop} (m : micro A E) :
    pure_wp m φ ψ → (∀ e, ψ e → ψ' e) → pure_wp m φ ψ'.
  Proof.
    induction 1; constructor; auto.
  Qed.

  (* Postconditions can be strengthened since final states must be reachable *)

  Lemma pure_wp_strengthen_reachable {A E} {φ ψ : _ → Prop} (m : micro A E) :
    pure_wp m φ ψ →
    pure_wp m
      (λ a, rtc may m (ret a) ∧ φ a)
      (λ e, rtc may m (throw e) ∧ ψ e).
  Proof.
    induction 1 as [ |  | ? ? ? Hex Hfo IH]; constructor; auto with relations.
    intros m' M. clear Hex.
    apply (pure_wp_mono _ (IH m' M)); firstorder; econstructor; eauto.
  Qed.

  (* A consequence rule that requires inclusion only on reachable final states *)

  Lemma pure_wp_mono_reachable {A E} {φ φ' ψ ψ' : _ → Prop} (m : micro A E) :
    pure_wp m φ ψ →
    (∀ a, rtc may m (ret a) → φ a → φ' a) →
    (∀ e, rtc may m (throw e) → ψ e → ψ' e) →
    pure_wp m φ' ψ'.
  Proof.
    intros P%pure_wp_strengthen_reachable Hv He.
    apply (pure_wp_mono _ P); firstorder.
  Qed.

  (** [pure_wp] is preserved by forward [may] steps *)

  Lemma pure_wp_may_forward {A E : Type} (φ : A → Prop) (ψ : E → Prop) m m' :
    pure_wp m φ ψ → may m m' → pure_wp m' φ ψ.
  Proof.
    induction 1; auto; inversion 1.
  Qed.

  Lemma pure_wp_rtc_may_forward {A E : Type} (φ : A → Prop) (ψ : E → Prop) m m' :
    pure_wp m φ ψ → rtc may m m' → pure_wp m' φ ψ.
  Proof.
    induction 2; eauto using pure_wp_may_forward.
  Qed.

  (** [pure_wp] is preserved by deterministic backward [may] steps *)

  Definition deterministically {X} (R : relation X) : relation X :=
    λ x y, R x y ∧ ∀ z, R x z → z = y.

  Lemma pure_wp_det_may_backward {A E : Type} (φ : A → Prop) (ψ : E → Prop) m m' :
    deterministically may m m' → pure_wp m' φ ψ → pure_wp m φ ψ.
  Proof.
    intros (M, MF) P. constructor. eauto. firstorder congruence.
  Qed.

  (** Inversion lemmas on [pure_wp] *)

  Lemma invert_pure_wp_crash {A E : Type} (φ : A → Prop) (ψ : E → Prop) :
    pure_wp (Crash) φ ψ → False.
  Proof.
    inversion 1; subst. firstorder eauto with invert_may.
  Qed.

  Lemma invert_pure_wp_ret {A E : Type} (φ : A → Prop) (ψ : E → Prop) a :
    pure_wp (ret a) φ ψ → φ a.
  Proof.
    intros S; remember (ret a) as m; revert a Heqm.
    induction S; try congruence. intros ? ->. exfalso. firstorder eauto with invert_may.
  Qed.

  Lemma invert_pure_wp_rtc_may_ret {A E : Type} (φ : A → Prop) (ψ : E → Prop) m a :
    pure_wp m φ ψ → rtc may m (ret a) → φ a.
  Proof.
    intros P S.
    eapply invert_pure_wp_ret.
    eapply pure_wp_rtc_may_forward; eauto.
  Qed.

  Lemma invert_pure_wp_throw {A E : Type} (φ : A → Prop) (ψ : E → Prop) e :
    pure_wp (throw e) φ ψ → ψ e.
  Proof.
    intros S; remember (throw e) as m; revert e Heqm.
    induction S; try congruence. intros ? ->. exfalso. firstorder eauto with invert_may.
  Qed.

  Lemma invert_pure_wp_may_crash {A E : Type} (φ : A → Prop) (ψ : E → Prop) m :
    may m (Crash) → pure_wp m φ ψ → False.
  Proof.
    eauto using invert_pure_wp_crash, pure_wp_may_forward.
  Qed.

  Lemma invert_pure_wp_may_may_crash {A E : Type} (φ : A → Prop) (ψ : E → Prop) m m' s :
    may m m' → may m' (crash s) → pure_wp m φ ψ → False.
  Proof.
    eauto using invert_pure_wp_crash, pure_wp_may_forward.
  Qed.

  Lemma invert_pure_wp_stop {A E X Y E'} (φ : A → Prop) (ψ : E → Prop) (c : code X Y E') (x : X) k :
    pure_wp (Stop c x k) φ ψ → match c with CEval | CLoop | CFlip => True | _ => False end.
  Proof.
    intros S. inversion S; subst.
    destruct H as (m', Hm'). assert (Wm' : pure_wp m' φ ψ) by eauto.
    destruct c; inversion Hm'; eq_dep_inj; subst; auto;
      eapply invert_pure_wp_may_crash; eauto.
  Qed.

  (** [pure_wp] is preserved by binds *)

  (* The _conseq format is slightly easier to prove and is easier to use in cases
    where a result is in hypothesis *)
  Lemma pure_wp_try2_conseq {A A' E E'} {φ ψ φ' ψ'} m (f : outcome2 A E → micro A' E') :
    pure_wp m φ ψ →
    (∀ a, φ a → pure_wp (continue f a) φ' ψ') →
    (∀ e, ψ e → pure_wp (discontinue f e) φ' ψ') →
    pure_wp (try2 m f) φ' ψ'.
  Proof.
    induction 1 as [ Ha | e | φ ψ m Hex Hm IHm]; intros Hv He; simpl; eauto.
    assert (Sm : pure_wp m φ ψ) by now econstructor.
    constructor.
    - destruct Hex as (m', Hm'). eexists. by apply may_try2.
    - intros m1 [(m' & Hm' & ->) | [(a & -> & Hm1) | (e & -> & Hm1)]]%invert_may_try2; eauto.
      eapply pure_wp_may_forward; eauto. apply invert_pure_wp_ret in Sm; auto.
      eapply pure_wp_may_forward; eauto. apply invert_pure_wp_throw in Sm; auto.
  Qed.

  Lemma pure_wp_try2 {A' A E E' φ ψ} m (f : outcome2 A E → micro A' E') :
    pure_wp m (λ a, pure_wp (continue f a) φ ψ) (λ e, pure_wp (discontinue f e) φ ψ) →
    pure_wp (try2 m f) φ ψ.
  Proof.
    intros P. eapply pure_wp_try2_conseq; eauto.
  Qed.

  Lemma pure_wp_bind {A' A E φ ψ} m (k : A → micro A' E) :
    pure_wp m (λ a, pure_wp (k a) φ ψ) ψ →
    pure_wp (bind m k) φ ψ.
  Proof.
    rewrite bind_as_try2. intros. eapply pure_wp_try2; eauto.
    eapply pure_wp_mono; eauto.
    intros e. rewrite discontinue_glue2. by constructor.
  Qed.

  Lemma pure_wp_try {A' A E E' φ ψ} m (f : A → micro A' E') (h : E → micro A' E') :
    pure_wp m (λ a, pure_wp (f a) φ ψ) (λ e, pure_wp (h e) φ ψ) →
    pure_wp (try m f h) φ ψ.
  Proof.
    eauto using pure_wp_try2.
  Qed.

  Lemma pure_wp_orelse {A E E'} (m1 : micro A E') (m2 : micro A E) φ ψ1 ψ :
    pure_wp m1 φ ψ1 →
    (∀ e, ψ1 e → pure_wp m2 φ ψ) →
    pure_wp (orelse m1 m2) φ ψ.
  Proof.
    intros. apply pure_wp_try2. eapply pure_wp_mono; eauto.
    intro. rewrite continue_glue2. by constructor.
  Qed.

  Lemma pure_wp_bind_conseq {A' A E} (φ : A → Prop) (ψ : E → Prop) (φ' : A' → Prop) m k :
    pure_wp m φ ψ →
    (∀ a, φ a → pure_wp (k a) φ' ψ) →
    pure_wp (bind m k) φ' ψ.
  Proof.
    intros. eapply pure_wp_bind, pure_wp_mono_ret; eauto.
  Qed.

  Lemma pure_wp_try_conseq {A' A E E' φ ψ φ' ψ'} m (f : A → micro A' E') (h : E → micro A' E') :
    pure_wp m φ ψ →
    (∀ a, φ a → pure_wp (f a) φ' ψ') →
    (∀ e, ψ e → pure_wp (h e) φ' ψ') →
    pure_wp (try m f h) φ' ψ'.
  Proof.
    intros. eapply pure_wp_try, pure_wp_mono; eauto.
  Qed.

  (** Characterization of [pure_wp] : a computation [m] satisfies some [pure_wp]
  if and only if [m] cannot do infinite [may] steps ([m] satisfies [sn may]) and
  all final computations reachable from [m] also satisfy the same [pure_wp] *)

  Lemma pure_wp_sn {A E} {φ : A → Prop} {ψ : E → Prop} m :
    pure_wp m φ ψ → sn may m.
  Proof.
    induction 1; try solve [constructor; intros y M; inversion M].
    constructor. firstorder.
  Qed.

  Lemma pure_wp_long_steps {A E} {φ : A → Prop} {ψ : E → Prop} m :
    pure_wp m φ ψ ↔ sn may m ∧ ∀ f, rtc may m f → final f → pure_wp f φ ψ.
  Proof.
    split.
    - intros W; split. by eapply pure_wp_sn.
      intros f S F.
      induction S. auto. apply IHS; auto.
      eauto using pure_wp_may_forward.
    - intros (SN, HF).
      revert HF; induction SN as [m SN IH]; intros HF.
      pose proof (may_cases m) as C.
      rewrite <-!Logic.or_assoc in C.
      destruct C as [C|(m', M)].
      + apply HF. constructor. firstorder subst; done.
      + constructor. eauto. clear m' M.
        intros m' M. apply IH; auto.
        intros f m'f F. apply HF; auto; econstructor; eauto.
  Qed.

  Lemma pure_wp_long_steps_ret_throw {A E} {φ : A → Prop} {ψ : E → Prop} m :
    pure_wp m φ ψ ↔
    sn may m ∧ (∀ a, rtc may m (ret a) → φ a)
            ∧ (∀ e, rtc may m (throw e) → ψ e)
            ∧ (¬rtc may m Crash).
  Proof.
    rewrite pure_wp_long_steps.
    split; intros [S L]; split; auto.
    - split; [|split].
      + intros a M. apply (invert_pure_wp_ret _ _ _ (L _ M I)).
      + intros e M. apply (invert_pure_wp_throw _ _ _ (L _ M I)).
      + intros M. apply (invert_pure_wp_crash _ _ (L _ M I)).
    - intros [] Hm []; constructor; firstorder.
  Qed.

  (* [pure_wp_exists_path] implies e.g. [pure_wp m (λ _, P) (λ _, P) → P] *)

  Lemma pure_wp_exists_path {A E} {φ : A → Prop} {ψ : E → Prop} m :
    pure_wp m φ ψ → ∃ f, rtc may m f ∧ final f ∧ pure_wp f φ ψ.
  Proof.
    intros W. induction W as [ | | ? ? m (m', M) Hf IH].
    - by repeat econstructor.
    - by repeat econstructor.
    - destruct (IH m' M) as (f & ? & ? & ?).
      assert (rtc may m f) by by econstructor.
      firstorder.
  Qed.

  Lemma pure_wp_exists_ret_or_throw {A E} {φ : A → Prop} {ψ : E → Prop} m :
    pure_wp m φ ψ →
    (∃ a, rtc may m (ret a) ∧ φ a) ∨
    (∃ e, rtc may m (throw e) ∧ ψ e).
  Proof.
    intros ([] & mf & [] & W)%pure_wp_exists_path.
    - apply invert_pure_wp_ret in W; eauto.
    - apply invert_pure_wp_throw in W; eauto.
    - apply invert_pure_wp_crash in W; tauto.
  Qed.

  Lemma pure_wp_invert_order {A1 E1 A2 E2} (m1 : micro A1 E1) (m2 : micro A2 E2) φ ψ :
    pure_wp m1 (λ a1, pure_wp m2 (λ a2, φ a1 a2) ψ) ⊥ →
    pure_wp m2 (λ a2, pure_wp m1 (λ a1, φ a1 a2) ⊥) ψ.
  Proof.
    intros Hm1.
    destruct (pure_wp_exists_ret_or_throw _ Hm1) as [(a1 & m1a1 & Ha1) | (? & ? & [])].
    apply (pure_wp_mono_reachable _ Ha1); auto. intros.
    apply (pure_wp_mono_reachable _ Hm1); auto. intros.
    eapply invert_pure_wp_ret, pure_wp_rtc_may_forward; eauto.
  Qed.


  (** [Par] preserves [pure_wp] *)

  (* From two [pure_wp]s on [m1] and [m2] we know [sn may m1] and [sn may m2],
  which can be combined to a [sn (either may may) (m1, m2)] on which we can
  perform an induction, to simulate the different steps that a [Par m1 m2 k]
  computation takes, in order to establish [pure_wp] on [Par m1 m2 k] *)

  Inductive either {A B} (R : A → A → Prop) (S : B → B → Prop) : A * B → A * B → Prop :=
    | either_left a a' b : R a a' → either R S (a, b) (a', b)
    | either_right a b b' : S b b' → either R S (a, b) (a, b').

  Lemma either_Acc {A B} (R : A → A → Prop) (S : B → B → Prop) a b :
    Acc R a → Acc S b → Acc (either R S) (a, b).
  Proof.
    intros Aa; revert b. induction Aa as [a Aa IHa].
    intros b Ab. induction Ab as [b Ab IHb].
    constructor.
    intros (a', b') H.
    inversion H; subst.
    eapply IHa; auto. constructor; eauto.
    eapply IHb; auto.
  Qed.

  (* [pure_wp] preserved by [Par] : linking postconditions with implications *)

  Lemma pure_wp_Par_conseq {A E A1 A2 E'} m1 m2 φ1 φ2 ψ1 ψ2 φ ψ
    (k : outcome2 (A1 * A2) E' → micro A E) :
    pure_wp m1 φ1 ψ1 →
    pure_wp m2 φ2 ψ2 →
    (∀ a1 a2, φ1 a1 → φ2 a2 → pure_wp (continue k (a1, a2)) φ ψ) →
    (∀ e, ψ1 e ∨ ψ2 e → pure_wp (discontinue k e) φ ψ) →
    pure_wp (Par m1 m2 k) φ ψ.
  Proof.
    intros H1 H2 Hret Hthr.
    pose proof either_Acc _ _ _ _ (pure_wp_sn _ H1) (pure_wp_sn _ H2) as SN.
    remember (m1, m2) as p.
    revert m1 m2 Heqp H1 H2.
    induction SN as [(m1, m2) SN IH].
    intros ? ? [=<-<-] H1 H2.
    constructor.
    - (* progress *)
      inversion H1; subst.
      + (* ret *) inversion H2; subst; eauto with may. firstorder. eexists. by eapply MayParRight.
      + (* throw *) eauto with may.
      + firstorder. eexists. by eapply MayParLeft.
    - (* preservation *)
      intros m' M.
      apply invert_may_par in M.
      repeat (destruct M as [M | M]).
      + destruct M as (? & ? & -> & -> & ->). apply Hret; eapply invert_pure_wp_ret; eauto.
      + destruct M as (m1' & M1 & ->). eapply (IH (m1', m2)); auto. constructor; apply M1. eauto using pure_wp_may_forward.
      + destruct M as (m2' & M2 & ->). eapply (IH (m1, m2')); auto. constructor; apply M2. eauto using pure_wp_may_forward.
      + destruct M as (e1 & -> & ->). apply Hthr. left. eapply invert_pure_wp_throw; eauto.
      + destruct M as (e2 & -> & ->). apply Hthr. right. eapply invert_pure_wp_throw; eauto.
      + destruct M as [[-> | ->] _]; exfalso; eapply invert_pure_wp_crash; eauto.
  Qed.

  (* Simpler version for the macro [par] *)
  Lemma pure_wp_par {A1 A2 E} (m1 m2 : micro _ E) φ1 φ2 (φ : A1 * A2 → Prop) ψ :
    pure_wp m1 φ1 ψ →
    pure_wp m2 φ2 ψ →
    (∀ a1 a2, φ1 a1 → φ2 a2 → φ (a1, a2)) →
    pure_wp (par m1 m2) φ ψ.
  Proof.
    intros; eapply pure_wp_Par_conseq; firstorder eauto using pure_wp_ret, pure_wp_throw.
  Qed.

  (* simpler version disallowing exceptions *)
  Lemma pure_wp_Par_conseq_ret {A E A1 A2 E'} m1 m2 φ1 φ2 φ
    (k : outcome2 (A1 * A2) E' → micro A E) :
    pure_wp m1 φ1 ⊥ →
    pure_wp m2 φ2 ⊥ →
    (∀ a1 a2, φ1 a1 → φ2 a2 → pure_wp (continue k (a1, a2)) φ ⊥) →
    pure_wp (Par m1 m2 k) φ ⊥.
  Proof.
    intros; eapply pure_wp_Par_conseq; eauto; firstorder.
  Qed.

  (* [pure_wp] preserved by [Par], stated by giving [m1] a [pure_wp m2]
  postcondition and [m2] a [pure_wp m1] postcondition. In other words, in a pure_wp
  setting, proving correct a parallel computation of [m1] and [m2] is the same as
  proving correct both sequentializations [m1; m2] and [m2; m1]. Both are needed
  since exceptions introduce nondeterminism. For example with [m1 = Throw e] and
  [m2 = Crash] we have [pure_wp m1 (λ _, False) (λ _, True)]. *)

  Lemma pure_wp_Par {A E A1 A2 E'} m1 m2 φ ψ
    (k : outcome2 (A1 * A2) E' → micro A E) :
    pure_wp m1
      (λ a1,
        pure_wp m2
          (λ a2, pure_wp (continue k (a1, a2)) φ ψ)
          (λ e, pure_wp (discontinue k e) φ ψ))
      (λ e, pure_wp (discontinue k e) φ ψ) →
    pure_wp m2
      (λ a2,
        pure_wp m1
          (λ a1, pure_wp (continue k (a1, a2)) φ ψ)
          (λ e, pure_wp (discontinue k e) φ ψ))
      (λ e, pure_wp (discontinue k e) φ ψ) →
    pure_wp (Par m1 m2 k) φ ψ.
  Proof.
    intros H1 H2.
    pose proof either_Acc _ _ _ _ (pure_wp_sn _ H1) (pure_wp_sn _ H2) as SN.
    remember (m1, m2) as p.
    revert m1 m2 Heqp H1 H2.
    induction SN as [(m1, m2) SN IH].
    intros ? ? [=<-<-] H1 H2.
    constructor.
    - (* progress *)
      inversion H1; subst.
      + (* ret *) inversion H2; subst; eauto with may. firstorder. eexists. by eapply MayParRight.
      + (* throw *) eauto with may.
      + firstorder. eexists. by eapply MayParLeft.
    - (* preservation *)
      intros m' M.
      apply invert_may_par in M.
      repeat (destruct M as [M | M]).
      + destruct M as (? & ? & -> & -> & ->). do 2 apply invert_pure_wp_ret in H1, H2; auto.
      + destruct M as (m1' & M1 & ->). eapply (IH (m1', m2)); auto.
        * constructor; apply M1.
        * eauto using pure_wp_may_forward.
        * eapply pure_wp_mono_ret; eauto.
          intros; eapply pure_wp_may_forward; eauto; eauto.
      + destruct M as (m2' & M2 & ->). eapply (IH (m1, m2')); auto.
        * constructor; apply M2.
        * eapply pure_wp_mono_ret; eauto.
          intros; eapply pure_wp_may_forward; eauto; eauto.
        * eauto using pure_wp_may_forward.
      + destruct M as (e1 & -> & ->). apply invert_pure_wp_throw in H1; eauto.
      + destruct M as (e2 & -> & ->). apply invert_pure_wp_throw in H2; eauto.
      + destruct M as [[-> | ->] _]; exfalso; eapply invert_pure_wp_crash; eauto.
  Qed.

  (** Sequentializations of [Par] for restricted forms of [pure_wp] *)

  (* If [m1] cannot raise exceptions, then it is enough to prove that [m1]
  satisfies [pure_wp] with the corresponding [pure_wp m2] in postcondition *)

  Lemma pure_wp_Par_val_left {A E A1 A2 E'} m1 m2 φ ψ
    (k : outcome2 (A1 * A2) E' → micro A E) :
    pure_wp m1
      (λ a1,
        pure_wp m2
          (λ a2, pure_wp (continue k (a1, a2)) φ ψ)
          (λ e, pure_wp (discontinue k e) φ ψ))
      ⊥ →
    pure_wp (Par m1 m2 k) φ ψ.
  Proof.
    intros H1.
    (* in order to run an induction on SN (either may may m1 m2) we establish
    [pure_wp m2] with a trivial postcondition for returns *)
    assert (H2 : pure_wp m2 (λ _, True) (λ e, pure_wp (discontinue k e) φ ψ)). {
      apply pure_wp_exists_ret_or_throw in H1.
      destruct H1 as [(a & _ & P) | (e & _ & [])].
      eapply pure_wp_mono; eauto.
    }
    pose proof either_Acc _ _ _ _ (pure_wp_sn _ H1) (pure_wp_sn _ H2) as SN.
    remember (m1, m2) as p.
    revert m1 m2 Heqp H1 H2.
    induction SN as [(m1, m2) SN IH].
    intros ? ? [=<-<-] H1 H2.
    constructor.
    - (* progress *)
      inversion H1; subst.
      + (* ret *) inversion H2; subst; eauto with may. firstorder. eexists. by eapply MayParRight.
      + (* throw *) eauto with may.
      + firstorder. eexists. by eapply MayParLeft.
    - (* preservation *)
      intros m' M.
      apply invert_may_par in M.
      repeat (destruct M as [M | M]).
      + destruct M as (? & ? & -> & -> & ->). do 2 apply invert_pure_wp_ret in H1; auto.
      + destruct M as (m1' & M1 & ->). eapply (IH (m1', m2)); auto.
        * constructor; apply M1.
        * eauto using pure_wp_may_forward.
      + destruct M as (m2' & M2 & ->). eapply (IH (m1, m2')); auto.
        * constructor; apply M2.
        * eapply pure_wp_mono_ret; eauto.
          intros; eapply pure_wp_may_forward; eauto; eauto.
        * eauto using pure_wp_may_forward.
      + destruct M as (e1 & -> & ->). apply invert_pure_wp_throw in H1; tauto.
      + destruct M as (e2 & -> & ->). eapply invert_pure_wp_throw in H2; eauto.
      + destruct M as [[-> | ->] _]; exfalso; eapply invert_pure_wp_crash; eauto.
  Qed.

  Lemma pure_wp_Par_val_right {A E A1 A2 E'} m1 m2 φ ψ
    (k : outcome2 (A1 * A2) E' → micro A E) :
    pure_wp m2
      (λ a2,
        pure_wp m1
          (λ a1, pure_wp (continue k (a1, a2)) φ ψ)
          (λ e, pure_wp (discontinue k e) φ ψ))
      ⊥ →
    pure_wp (Par m1 m2 k) φ ψ.
  Proof.
    intros H2.
    assert (H1 : pure_wp m1 (λ _, True) (λ e, pure_wp (discontinue k e) φ ψ)). {
      apply pure_wp_exists_ret_or_throw in H2.
      destruct H2 as [(a & _ & P) | (e & _ & [])].
      eapply pure_wp_mono; eauto.
    }
    pose proof either_Acc _ _ _ _ (pure_wp_sn _ H1) (pure_wp_sn _ H2) as SN.
    remember (m1, m2) as p.
    revert m1 m2 Heqp H1 H2.
    induction SN as [(m1, m2) SN IH].
    intros ? ? [=<-<-] H1 H2.
    constructor.
    - (* progress *)
      inversion H1; subst.
      + (* ret *) inversion H2; subst; eauto with may. firstorder. eexists. by eapply MayParRight.
      + (* throw *) eauto with may.
      + firstorder. eexists. by eapply MayParLeft.
    - (* preservation *)
      intros m' M.
      apply invert_may_par in M.
      repeat (destruct M as [M | M]).
      + destruct M as (? & ? & -> & -> & ->). do 2 apply invert_pure_wp_ret in H2; auto.
      + destruct M as (m1' & M1 & ->). eapply (IH (m1', m2)); auto.
        * constructor; apply M1.
        * eauto using pure_wp_may_forward.
        * eapply pure_wp_mono_ret; eauto.
          intros; eapply pure_wp_may_forward; eauto; eauto.
      + destruct M as (m2' & M2 & ->). eapply (IH (m1, m2')); auto.
        * constructor; apply M2.
        * eauto using pure_wp_may_forward.
      + destruct M as (e1 & -> & ->). apply invert_pure_wp_throw in H1; tauto.
      + destruct M as (e2 & -> & ->). eapply invert_pure_wp_throw in H2; tauto.
      + destruct M as [[-> | ->] _]; exfalso; eapply invert_pure_wp_crash; eauto.
  Qed.

  (* Slightly simpler case when none of the parties involved ([m1], [m2]) can
    throw exceptions *)

  Lemma pure_wp_Par_vals_left {A E A1 A2 E'} m1 m2 φ ζ
    (k : outcome2 (A1 * A2) E' → micro A E) :
    pure_wp m1 (λ a1, pure_wp m2 (λ a2, pure_wp (continue k (a1, a2)) φ ζ) ⊥) ⊥ →
    pure_wp (Par m1 m2 k) φ ζ.
  Proof.
    intros H1.
    apply pure_wp_Par_val_left.
    eapply pure_wp_mono; eauto. simpl. intros.
    eapply pure_wp_mono; firstorder eauto.
  Qed.

  Lemma pure_wp_Par_vals_right {A E A1 A2 E'} m1 m2 φ ζ
    (k : outcome2 (A1 * A2) E' → micro A E) :
    pure_wp m2 (λ a2, pure_wp m1 (λ a1, pure_wp (continue k (a1, a2)) φ ζ) ⊥) ⊥ →
    pure_wp (Par m1 m2 k) φ ζ.
  Proof.
    intros H2.
    apply pure_wp_Par_val_right.
    eapply pure_wp_mono; eauto. simpl. intros.
    eapply pure_wp_mono; firstorder eauto.
  Qed.

  (* The binary/conseq style is common *)

  Lemma pure_wpv_Par_left_conseq {A E A1 A2 E' m1 m2 φ φ1}
    {k : outcome2 (A1 * A2) E' → micro A E} :
    pure_wp m1 φ1 ⊥ →
    (∀ a1, φ1 a1 → pure_wp m2 (λ a2, pure_wp (continue k (a1, a2)) φ ⊥) ⊥) →
    pure_wp (Par m1 m2 k) φ ⊥.
  Proof.
    intros H1 H2.
    apply pure_wp_Par_vals_left.
    eapply pure_wp_mono; eauto.
  Qed.


  (** [pure_wp] is preserved by [Handle] *)

  Lemma pure_wp_handle {A E} m φ ψ (h : outcome3 _ _ → micro A E) :
    pure_wp m
      (λ a, pure_wp (h (O3Ret a)) φ ψ)
      (λ e, pure_wp (h (O3Throw e)) φ ψ) →
    pure_wp (Handle m h) φ ψ.
  Proof.
    intros Hm. dependent induction Hm; constructor; eauto with may.
    - intros m' M. inv M; auto. edestruct invert_may_ret; eauto.
    - intros m' M. inv M; auto. edestruct invert_may_throw; eauto.
    - firstorder eauto with may.
    - intros m' M. inv M.
      + firstorder; edestruct invert_may_ret; eauto.
      + firstorder; edestruct invert_may_throw; eauto.
      + firstorder. by edestruct (@invert_may_crash val val).
      + firstorder.
  Qed.

  (** on [Stop CEval] *)

  Lemma pure_wp_Eval {A E} η e k (φ : A → Prop) (ψ : E → Prop) :
    pure_wp (try2 (eval η e) k) φ ψ →
    pure_wp (Stop CEval (η, e) k) φ ψ.
  Proof.
    intros. eapply pure_wp_det_may_backward; eauto. repeat constructor.
    by intros m' ->%pure.invert_may_eval.
  Qed.

  (** [pure_wp] is preserved by [Flip] and [choose] *)

  Lemma pure_wp_Flip {A E φ ψ} u (k : outcome2 bool exn → micro A E) :
    pure_wp (continue k true) φ ψ →
    pure_wp (continue k false) φ ψ →
    pure_wp (Stop CFlip u k) φ ψ.
  Proof.
    intros H1 H2. constructor. eauto with may.
    intros m' M. by invdep M.
  Qed.

  Lemma pure_wp_choose {A φ ψ} (m1 m2 : micro A exn) :
    pure_wp m1 φ ψ →
    pure_wp m2 φ ψ →
    pure_wp (choose m1 m2) φ ψ.
  Proof.
    intros H1 H2.
    apply pure_wp_Flip; auto.
  Qed.


  (** More inversion lemmas on [pure_wp] : bind, [Par]s, [Handle] *)

  Lemma invert_pure_wp_try2 {A1 E1 B E' φ ψ} (m : micro A1 E1) (k : _ → micro B E') :
    pure_wp (try2 m k) φ ψ →
    pure_wp m
      (λ a, pure_wp (continue k a) φ ψ)
      (λ e, pure_wp (discontinue k e) φ ψ).
  Proof.
    remember (try2 m k) as mt; intros PS; revert m Heqmt.
    induction PS as [ |  | φ ψ m Hex HF IH]; intros m1 Hm1.
    (* if [try2 m1 k] is [ret] or [throw] then [m1] must be too *)
    - destruct m1; try discriminate.
      all: constructor; simpl in Hm1; rewrite <-Hm1; by constructor.
    - destruct m1; try discriminate.
      all: constructor; simpl in Hm1; rewrite <-Hm1; by constructor.
    - (* otherwise [m] reduces to some [m'], and all such [m'] are safe  *)
      subst m.
      (* from the fact that [try2 m1 k] reduce to [m']: *)
      destruct Hex as (m', [(m1' & Hm1 & ->) | ?]%invert_may_try2).
      + (* either [m1] reduces to [m1'] and [m' = try2 m1' k], conclude by IH *)
        constructor; eauto. intros m2 Hm2.
        eapply IH; eauto. by apply may_try2.
      + (* or [m1] is [ret] or [throw] and so is safe *)
        by hnf; firstorder (subst; eauto with pure).
  Qed.

  Lemma invert_pure_wp_bind {A1 E B φ ψ} (m : micro A1 E) (k : _ → micro B E) :
    pure_wp (bind m k) φ ψ →
    pure_wp m (λ a, pure_wp (k a) φ ψ) ψ.
  Proof.
    rewrite bind_as_try2.
    intros H%invert_pure_wp_try2.
    eapply pure_wp_mono; eauto.
    by intros ? ?%invert_pure_wp_throw.
  Qed.

  Corollary pure_wp_bind_mono {A B E} (m : micro A E) (f g : A -> micro B E) φ ζ :
    (∀ a, pure_wp (f a) φ ζ -> pure_wp (g a) φ ζ) ->
    pure_wp (bind m f) φ ζ -> pure_wp (bind m g) φ ζ.
  Proof.
    intros Hmono Hf.
    apply invert_pure_wp_bind in Hf.
    apply pure_wp_bind.
    eapply pure_wp_mono; eauto.
  Qed.

  Lemma invert_pure_wp_Par_ret_left {A E A1 A2 E' φ ψ}
    a1 m2 (k : outcome2 (A1 * A2) E' → micro A E) :
    pure_wp (Par (ret a1) m2 k) φ ψ →
    pure_wp m2
      (λ a2, pure_wp (continue k (a1, a2)) φ ψ)
      (λ e, pure_wp (discontinue k e) φ ψ).
  Proof.
    remember (Par _ m2 k) as m; intros PS; revert a1 m2 Heqm.
    induction PS as [ |  | φ ψ m Hex HF IH]; try discriminate; intros m1 m2 ->.
    destruct (may_cases m2) as [-> | [ | [ | Hm2 ]]].
    - now destruct (invert_pure_wp_crash _ _ (HF (Crash) ltac:(constructor))).
    - firstorder. subst. constructor. apply HF. constructor.
    - destruct H as (e, ->). constructor. apply (HF _ ltac:(constructor)).
    - constructor; eauto with may.
  Qed.

  Lemma invert_pure_wp_Par_left {A E A1 A2 E' φ ψ}
    m1 m2 (k : outcome2 (A1 * A2) E' → micro A E) :
    pure_wp (Par m1 m2 k) φ ψ →
    pure_wp m1
      (λ a1,
        pure_wp m2
          (λ a2, pure_wp (continue k (a1, a2)) φ ψ)
          (λ e, pure_wp (discontinue k e) φ ψ))
      (λ e, pure_wp (discontinue k e) φ ψ).
  Proof.
    remember (Par m1 m2 k) as m; intros PS; revert m1 m2 Heqm.
    induction PS as [ |  | φ ψ m Hex HF IH]; try discriminate; intros m1 m2 ->.
    destruct (may_cases m1) as [-> | [ | [ | Hm1 ]]].
    - now destruct (invert_pure_wp_crash _ _ (HF (Crash) ltac:(constructor))).
    - assert (PP : pure_wp (Par m1 m2 k) φ ψ) by by constructor.
      firstorder. subst. constructor. by eapply invert_pure_wp_Par_ret_left.
    - destruct H as (e, ->). constructor. apply (HF _ ltac:(constructor)).
    - constructor; eauto with may.
  Qed.

  Lemma invert_pure_wp_Par_ret_right {A E A1 A2 E' φ ψ}
    m1 a2 (k : outcome2 (A1 * A2) E' → micro A E) :
    pure_wp (Par m1 (ret a2) k) φ ψ →
    pure_wp m1
      (λ a1, pure_wp (continue k (a1, a2)) φ ψ)
      (λ e, pure_wp (discontinue k e) φ ψ).
  Proof.
    remember (Par _ _ k) as m; intros PS; revert m1 a2 Heqm.
    induction PS as [ |  | φ ψ m Hex HF IH]; try discriminate; intros m1 m2 ->.
    destruct (may_cases m1) as [ -> | [ | [ | Hm1 ]]].
    - now destruct (invert_pure_wp_crash _ _ (HF (Crash) ltac:(constructor))).
    - firstorder. subst. constructor. apply HF. constructor.
    - destruct H as (e, ->). constructor. apply (HF _ ltac:(constructor)).
    - constructor; eauto with may.
  Qed.

  Lemma invert_pure_wp_Par_right {A E A1 A2 E' φ ψ}
    m1 m2 (k : outcome2 (A1 * A2) E' → micro A E) :
    pure_wp (Par m1 m2 k) φ ψ →
    pure_wp m2
      (λ a2,
        pure_wp m1
          (λ a1, pure_wp (continue k (a1, a2)) φ ψ)
          (λ e, pure_wp (discontinue k e) φ ψ))
      (λ e, pure_wp (discontinue k e) φ ψ).
  Proof.
    remember (Par m1 m2 k) as m; intros PS; revert m1 m2 Heqm.
    induction PS as [ |  | φ ψ m Hex HF IH]; try discriminate; intros m1 m2 ->.
    destruct (may_cases m2) as [-> | [ | [ | Hm2 ]]].
    - now destruct (invert_pure_wp_crash _ _ (HF Crash ltac:(constructor))).
    - assert (PP : pure_wp (Par m1 m2 k) φ ψ) by by constructor.
      firstorder. subst. constructor. by eapply invert_pure_wp_Par_ret_right.
    - destruct H as (e, ->). constructor. apply (HF _ ltac:(constructor)).
    - constructor; eauto with may.
  Qed.

  Corollary invert_pure_wp_Par {A E A1 A2 E' φ ψ}
    m1 m2 (k : outcome2 (A1 * A2) E' → micro A E) :
    pure_wp (Par m1 m2 k) φ ψ →
    pure_wp m1
      (λ a1,
        pure_wp m2
          (λ a2, pure_wp (continue k (a1, a2)) φ ψ)
          (λ e, pure_wp (discontinue k e) φ ψ))
      (λ e, pure_wp (discontinue k e) φ ψ) /\
    pure_wp m2
      (λ a2,
        pure_wp m1
          (λ a1, pure_wp (continue k (a1, a2)) φ ψ)
          (λ e, pure_wp (discontinue k e) φ ψ))
      (λ e, pure_wp (discontinue k e) φ ψ).
  Proof.
    intros H.
    pose proof (invert_pure_wp_Par_left _ _ _ H).
    pose proof (invert_pure_wp_Par_right _ _ _ H).
    done.
  Qed.

  Lemma invert_pure_wp_handle {A E φ ψ} m (k : _ → micro A E) :
    pure_wp (Handle m k) φ ψ →
    pure_wp m
      (λ a, pure_wp (continue k a) φ ψ)
      (λ e, pure_wp (discontinue k e) φ ψ).
  Proof.
    remember (Handle m k) as h; intros PS; revert m Heqh.
    induction PS as [ |  | φ ψ _m Hex HF IH]; try discriminate; intros m ->.
    destruct (may_cases m) as [-> | [ | [ | Hm ]]].
    - now destruct (invert_pure_wp_crash _ _ (HF Crash ltac:(constructor))).
    - firstorder. subst. constructor. eauto with may.
    - destruct H as (e, ->). constructor. eauto with may.
    - constructor; eauto with may.
  Qed.

  Lemma invert_pure_wp_Eval {B X} η e (k : _ -> micro B X) φ ζ :
    pure_wp (Stop CEval (η, e) k) φ ζ ->
    pure_wp (try2 (eval η e) k) φ ζ.
  Proof.
    intros Hstop.
    inversion Hstop; subst.
    destruct H as [m' Hmay].
    specialize (H0 m' Hmay) as Hwp.
    pose proof (invert_may_eval _ _ _ Hmay) as ->; simpl in *.
    apply Hwp.
  Qed.

  Lemma invert_pure_wp_eval η e φ ζ :
    pure_wp (stop CEval (η, e)) φ ζ ->
    pure_wp (eval η e) φ ζ.
  Proof.
    intros Hstop.
    apply invert_pure_wp_Eval in Hstop.
    rewrite try2_inject2_right in Hstop.
    apply Hstop.
  Qed.

  (** Steps from pure_wp computations necessarily are [may] and preserve the store *)

  Lemma pure_wp_step_may {A E : Type} {φ : A → Prop} {ψ : E → Prop} {m σ m' σ'} :
    pure_wp m φ ψ → step (σ, m) (σ', m') → may m m' ∧ σ' = σ.
  Proof.
    revert σ σ' m' φ ψ; induction m; intros σ σ' m' φ ψ Hm Hstep.
    - inv Hstep.
    - inv Hstep.
    - inv Hstep.
    - apply invert_pure_wp_handle in Hm.
      inv Hstep; eauto with may.
      + by apply invert_pure_wp_stop in Hm.
      + by apply invert_pure_wp_stop in Hm.
      + by apply invert_pure_wp_stop in Hm.
      + by apply invert_pure_wp_stop in Hm.
      + by apply invert_pure_wp_stop in Hm.
      + edestruct IHm; eauto with may.
    - pose proof invert_pure_wp_stop _ _ _ _ _ Hm.
      destruct c; try tauto; invdep Hstep; split; auto; try destruct b; constructor.
    - pose proof invert_pure_wp_Par_left _ _ _ Hm as Hm1.
      pose proof invert_pure_wp_Par_right _ _ _ Hm as Hm2.
      invdep Hstep; try (split; [ | tauto ]).
      all: try by constructor.
      + destruct_code; by apply invert_pure_wp_stop in Hm1.
      + destruct_code; by apply invert_pure_wp_stop in Hm2.
      + edestruct IHm1; eauto with may.
      + edestruct IHm2; eauto with may.
  Qed.


  (* One proof of the preservation of [pure_wp] under [step]s. It may be removed
  since it is a consequence of [pure_wp_step_may] and [pure_wp_may_forward],
  however it is a demonstration that we can split a [pure_wp] on a [Par] into two
  with [invert_pure_wp_Par_*] and recombine them with
  [pure_wp_Par_sequentialization] after a step on either side. This technique is
  also useful for [pure_wp_simp]. *)

  Lemma pure_wp_preservation_duplicate {A E : Type} {φ : A → Prop} {ψ : E → Prop} {m σ m' σ'} :
    pure_wp m φ ψ → step (σ, m) (σ', m') → pure_wp m' φ ψ ∧ σ' = σ.
  Proof.
    revert σ σ' m' φ ψ; induction m; intros σ σ' m' φ ψ Hm Hstep.
    - inv Hstep.
    - inv Hstep.
    - inv Hstep.
    - apply invert_pure_wp_handle in Hm.
      inv Hstep; try by apply invert_pure_wp_stop in Hm.
      + by apply invert_pure_wp_ret in Hm.
      + by apply invert_pure_wp_throw in Hm.
      + by apply invert_pure_wp_crash in Hm.
      + edestruct IHm as [IH ->]; eauto. split; auto.
        eapply pure_wp_handle; eauto.
    - pose proof invert_pure_wp_stop _ _ _ _ _ Hm.
      destruct c; try tauto; invdep Hstep; split; auto;
        eapply pure_wp_may_forward; eauto; try destruct b; constructor.
    - pose proof invert_pure_wp_Par_left _ _ _ Hm as Hm1.
      pose proof invert_pure_wp_Par_right _ _ _ Hm as Hm2.
      invdep Hstep; try (split; [ | tauto ]).
      all: eauto using pure_wp_may_forward with may.
      + destruct_code; by apply invert_pure_wp_stop in Hm1.
      + destruct_code; by apply invert_pure_wp_stop in Hm2.
      + edestruct IHm1 as [IHm1' ->]; eauto. split; auto.
        eapply pure_wp_Par. apply IHm1'.
        eapply pure_wp_mono_ret; eauto. simpl.
        intros a2 Hm1'.
        eapply (IHm1 _ _ _ _ _ Hm1'); eauto.
      + edestruct IHm2 as [IHm2' ->]; eauto. split; auto.
        eapply pure_wp_Par. 2: apply IHm2'.
        eapply pure_wp_mono_ret; eauto. simpl.
        intros a1 Hm2'.
        eapply (IHm2 _ _ _ _ _ Hm2'); eauto.
  Qed.


  (** [pure_wp] : progress and preservation *)

  Lemma pure_wp_progress {A E : Type} {φ : A → Prop} {ψ : E → Prop} m :
    pure_wp m φ ψ → (∃ a, m = ret a) ∨ (∃ e, m = throw e) ∨ ∀ σ, can_step (σ, m).
  Proof.
    intros Hm.
    destruct m; eauto.
    - by apply invert_pure_wp_crash in Hm.
    - eauto using can_step_handle.
    - right; right; intros.
      apply can_step_stop.
      apply invert_pure_wp_stop in Hm.
      destruct c; auto.
    - eauto using can_step_par.
  Qed.

  Lemma pure_wp_preservation {A E : Type} {φ : A → Prop} {ψ : E → Prop} {m σ m' σ'} :
    pure_wp m φ ψ → step (σ, m) (σ', m') → pure_wp m' φ ψ ∧ σ' = σ.
  Proof.
    intros Hm Hstep.
    destruct (pure_wp_step_may Hm Hstep).
    eauto using pure_wp_may_forward.
  Qed.

  (** Intersection rules *)

  Lemma pure_wp_intersection {A E} `{Inhabited X} {φ ψ} (m : micro A E) :
    (∀ x : X, pure_wp m (φ x) ψ) →
    pure_wp m (λ a, ∀ x, φ x a) ψ.
  Proof.
    intros Hm.
    induction (Hm inhabitant); constructor; eauto using pure_wp_may_forward.
    intros x. apply (invert_pure_wp_ret _ _ _ (Hm x)).
  Qed.

  Lemma pure_wp_intersection_exn {A E} `{Inhabited X} `{Inhabited Y} {φ ψ} (m : micro A E) :
    (∀ (x : X) (y : Y), pure_wp m (φ x) (ψ y)) →
    pure_wp m (λ a, ∀ x, φ x a) (λ e, ∀ y, ψ y e).
  Proof.
    intros Hm.
    induction (Hm inhabitant inhabitant); constructor; eauto using pure_wp_may_forward.
    - intros x; apply (invert_pure_wp_ret _ _ _ (Hm x inhabitant)).
    - intros y; apply (invert_pure_wp_throw _ _ _ (Hm inhabitant y)).
  Qed.

  Lemma pure_wp_binary_intersection {A E φ1 φ2 ψ} (m : micro A E) :
    pure_wp m φ1 ψ →
    pure_wp m φ2 ψ →
    pure_wp m (λ a, φ1 a ∧ φ2 a) ψ.
  Proof.
    intros.
    set (post := λ (b : bool), λ a, if b then φ1 a else φ2 a).
    eapply @pure_wp_mono with (φ := λ a, ∀ b, post b a) (ψ := ψ).
    { eapply pure_wp_intersection.
      intros b. destruct b; unfold post; assumption. }
    { intros a Hpost. split.
      + apply (Hpost true).
      + apply (Hpost false). }
    { tauto. }
  Qed.

  Lemma pure_wp_intersection_pred {A E X} (P : X → Prop) {φ ψ} (m : micro A E) :
    (∃ x, P x) →
    (∀ x : X, P x → pure_wp m (φ x) ψ) →
    pure_wp m (λ a, ∀ x, P x → φ x a) ψ.
  Proof.
    intros (x, Px) Hm.
    induction (Hm x Px); constructor; eauto using pure_wp_may_forward.
    intros y Py. apply (invert_pure_wp_ret _ _ _ (Hm y Py)).
  Qed.

  (** Compatibility with [of_option] *)

  Lemma pure_wp_widen {A E} (o : option A) φ ψ :
    match o with
    | Some a => φ a
    | None => False
    end →
    pure_wp (E := E) (of_option o) φ ψ.
  Proof.
    unfold of_option. destruct o; last destruct 1.
    apply pure_wp_ret.
  Qed.

End pure_wp_rules.


Section pure_wp_reversible_rules.

Lemma pure_wp_reversible_Par {A E A1 A2 E'} m1 m2 (k : outcome2 (A1 * A2) E' → micro A E) φ ψ :
  (∃ φ1 φ2 ψ1 ψ2,
      pure_wp m1 φ1 ψ1 ∧
      pure_wp m2 φ2 ψ2 ∧
      (∀ a1 a2, φ1 a1 → φ2 a2 → pure_wp (continue k (a1, a2)) φ ψ) ∧
      (∀ e, ψ1 e ∨ ψ2 e → pure_wp (discontinue k e) φ ψ))
  <->
  pure_wp (Par m1 m2 k) φ ψ.
Proof.
  split.
  { firstorder eauto using pure_wp_Par_conseq. }
  intros P.
  pose proof invert_pure_wp_Par _ _ _ P as (P1 & P2).
  apply pure_wp_strengthen_reachable in P1.
  apply pure_wp_strengthen_reachable in P2.
  eexists _, _, _, _.
  split; eauto.
  split; eauto.
  split. 2: firstorder.
  intros a1 a2 (S1, Hm1) (S2, Hm2).
  eapply pure_wp_rtc_may_forward; eauto.
  apply rtc_trans with (Par (ret a1) (ret a2) k). 2: repeat econstructor.
  apply rtc_trans with (Par (ret a1) m2 k).
  - clear -S1. induction S1. done. econstructor; eauto. constructor; auto.
  - clear -S2. induction S2. done. econstructor; eauto. constructor; auto.
Qed.

Lemma pure_wp_reversible_par {A1 A2 E} m1 m2  (φ : A1 * A2 → Prop) (ψ : E → Prop) :
  (∃ φ1 φ2,
      pure_wp m1 φ1 ψ ∧
      pure_wp m2 φ2 ψ ∧
      (∀ a1 a2, φ1 a1 → φ2 a2 → φ (a1, a2)))
  <->
  pure_wp (par m1 m2) φ ψ.
Proof.
  split.
  { firstorder eauto using pure_wp_par. }
  intros (φ1 & φ2 & ψ1 & ψ2 & P1 & P2 & Ha & He)%pure_wp_reversible_Par.
  eexists φ1, φ2. split; [ | split ].
  - eapply pure_wp_mono_throw; eauto. intros; eapply invert_pure_wp_throw; eauto.
  - eapply pure_wp_mono_throw; eauto. intros; eapply invert_pure_wp_throw; eauto.
  - intros; eapply invert_pure_wp_ret; eauto.
Qed.

Lemma pure_wp_reversible_intersection {A E} `{Inhabited X} {φ ψ} (m : micro A E) :
  (∀ x : X, pure_wp m (φ x) ψ)
  <->
  pure_wp m (λ a, ∀ x, φ x a) ψ.
Proof.
  split.
  - apply pure_wp_intersection.
  - intros P x. eapply pure_wp_mono_ret; eauto.
Qed.

Context {A E} (φ : A → Prop) (ψ : E → Prop).

Lemma pure_wp_reversible_ret a : φ a <-> pure_wp (ret a) φ ψ.
Proof.
  split.
  - apply pure_wp_ret.
  - apply invert_pure_wp_ret.
Qed.

Lemma pure_wp_reversible_throw e : ψ e <-> pure_wp (throw e) φ ψ.
Proof.
  split.
  - apply pure_wp_throw.
  - apply invert_pure_wp_throw.
Qed.

Lemma pure_wp_reversible_handle m (h : outcome3 _ _ → _) :
  pure_wp m
    (λ a, pure_wp (h (O3Ret a)) φ ψ)
    (λ e, pure_wp (h (O3Throw e)) φ ψ)
  <->
  pure_wp (Handle m h) φ ψ.
Proof.
  split.
  - apply pure_wp_handle.
  - apply invert_pure_wp_handle.
Qed.

Lemma pure_wp_reversible_try2 {A' E'} m (f : outcome2 A' E' → _) :
  pure_wp m
    (λ a, pure_wp (continue f a) φ ψ)
    (λ e, pure_wp (discontinue f e) φ ψ)
  <->
  pure_wp (try2 m f) φ ψ.
Proof.
  split.
  - apply pure_wp_try2.
  - apply invert_pure_wp_try2.
Qed.

Lemma pure_wp_reversible_Stop_eval η e k :
  pure_wp (try2 (eval η e) k) φ ψ
  <->
  pure_wp (Stop CEval (η, e) k) φ ψ.
Proof.
  split.
  - apply pure_wp_Eval.
  - intros Hstop.
    apply invert_pure_wp_Eval in Hstop.
    apply Hstop.
Qed.

Lemma pure_wp_reversible_choose m1 m2 ζ :
  pure_wp m1 φ ζ ∧
  pure_wp m2 φ ζ
  <->
  pure_wp (choose m1 m2) φ ζ.
Proof.
  split.
  - intros []; by apply pure_wp_choose.
  - intros P; split; eapply pure_wp_may_forward; eauto; constructor.
Qed.

Lemma pure_wp_reversible_try {A' E'} m f g :
  pure_wp m (λ a : A', pure_wp (f a) φ ψ) (λ e : E', pure_wp (g e) φ ψ)
  <->
  pure_wp (try m f g) φ ψ.
Proof.
  unfold try.
  by rewrite <-pure_wp_reversible_try2.
Qed.

Lemma pure_wp_reversible_orelse {E'} (m1 : micro _ E') m2 :
  pure_wp m1 φ (λ _, pure_wp m2 φ ψ)
  <->
  pure_wp (orelse m1 m2) φ ψ.
Proof.
  unfold orelse.
  rewrite <-pure_wp_reversible_try.
  apply pure_wp_ret_equiv, pure_wp_reversible_ret.
Qed.

Lemma pure_wp_reversible_bind {A'} m (k : A' → micro A E) :
  pure_wp m (λ a, pure_wp (k a) φ ψ) ψ
  <->
  pure_wp (bind m k) φ ψ.
Proof.
  split.
  - apply pure_wp_bind.
  - apply invert_pure_wp_bind.
Qed.

End pure_wp_reversible_rules.
