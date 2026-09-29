From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import code eval.
Require Export wp judgements.

(** This file defines basic reasoning rules over [pure] judgements. *)

Section pure_rules.

  (** *Basic reasoning rules for [pure]. *)

  (* A reasoning rule for [ret]. *)

  (* The subgoal [v = #a] is explicitly isolated so as to make this lemma
    more widely applicable. A subgoal of the form [v = #a], where [a] is
    a Coq metavariable, can be solved by the tactic [encode]. *)

  Lemma pure_ret `{Observe A V} `{Observe B E}
    (φ : A → Prop) (ψ : B → Prop) (v : V) a :
    v = ♯ a →
    φ a →
    pure (ret v) φ ψ.
  Proof.
    intros; apply pure_wp_ret; esplit; eauto.
  Qed.

  (* A reasoning rule for ret that can instantiate the goal when it is an evar *)

  Lemma pure_ret_eq `{Observe A V} `{Observe B E}
    (a : A) (ψ : B → Prop) :
    pure (ret ♯a) (λ a', a' = a) ψ.
  Proof.
    intros; eapply pure_ret; eauto.
  Qed.

  Lemma pure_returns `{Observe A V} `{Observe B E}
    (a : val) (k : val -> micro V E) (φ : A -> _) (ψ : B → Prop) :
    pure (k a) φ ψ ->
    returns (V := val) (λ v , pure (k v) φ ψ) a.
  Proof.
    intros; eauto with pure.
  Qed.

  Lemma pure_throw `{Observe A V} `{Observe B E}
    (φ : A -> Prop) (ψ : B -> Prop) (e : E) (b : B) :
    e = ♯b →
    ψ b →
    pure (throw e) φ ψ.
  Proof.
    intros Heq Hb; subst e; apply pure_wp_throw; exists b; eauto.
  Qed.

  (* The consequence rule. *)

  Lemma pure_mono `{Observe A V} `{Observe B E}
    m (φ φ' : A -> Prop) (ψ ψ' : B -> Prop) :
    pure m φ ψ →
    (∀ a, φ a → φ' a) →
    (∀ a, ψ a → ψ' a) →
    pure m φ' ψ'.
  Proof.
    intros; eapply pure_wp_mono; [ eauto | |]; firstorder.
  Qed.

  Lemma pure_ret_mono `{Observe A V} `{Observe B E}
    m (φ φ' : A -> Prop) (ψ : B -> Prop) :
    pure m φ ψ →
    (∀ a, φ a → φ' a) →
    pure m φ' ψ.
  Proof.
    intros; eapply pure_mono ; eauto.
  Qed.

  Lemma pure_exn_mono `{Observe A V} `{Observe B E}
    m (φ : A -> Prop) (ψ ψ' : B -> Prop) :
    pure m φ ψ →
    (∀ a, ψ a → ψ' a) →
    pure m φ ψ'.
  Proof.
    intros; eapply pure_mono ; eauto.
  Qed.

  Lemma pure_exn_widen `{Observe A V} `{Observe B1 E} `{Observe B2 E}
    m (φ : A -> Prop) (Ψ : B1 -> Prop) :
    pure m φ (⊥ : B2 → Prop) →
    pure m φ Ψ.
  Proof.
    intros; eapply pure_wp_mono_throw; first eassumption.
    intros ? (? & ? & []).
  Qed.

  (* A reasoning rule for [try2]. *)

  (* The rule is degenerate; [m] is not allowed to reduce to [throw _],
    so the handler [z] is dead and no proof obligation bears on it. *)

  Lemma pure_try2 `{Observe A1 V1} `{Observe A2 V2} `{Observe B1 E1} `{Observe B2 E2}
    (m : micro V1 E1) (h : outcome2 V1 E1 -> micro V2 E2)
    (φ : A2 -> _) (φ' : A1 -> _) (ψ : B2 -> Prop) (ψ' : B1 -> Prop) :
    pure m φ' ψ' →
    (∀ a, φ' a → pure (continue h ♯a) φ ψ) →
    (∀ b, ψ' b → pure (discontinue h ♯b) φ ψ) →
    pure (try2 m h) φ ψ.
  Proof.
    intros Hm Hcont Hdisc.
    eapply pure_wp_try2_conseq; eauto.
    - intros v (a & -> & Ha). by apply Hcont.
    - intros e (b & -> & Hb). by apply Hdisc.
  Qed.

  (* A reasoning rule for [try]; corollary of [pure_try2] *)

  Corollary pure_try `{Observe A1 V1} `{Observe A2 V2} `{Observe B E}
    `{Observe B' E}
    (m : micro V1 E) k z (φ : A2 -> _) (φ' : A1 -> _)
    (ψ : B → Prop) (ψ' : B' → Prop) :
    pure m φ' ψ' →
    (∀ a, φ' a → pure (k ♯a) φ ψ) →
    (∀ b, ψ' b → pure (z ♯b) φ ψ) →
    pure (try m k z) φ ψ.
  Proof.
    intros; eapply pure_try2; eauto.
  Qed.

  (* A reasoning rule for [bind]. *)

  (* Without [Observe], this bind type was restricted (it would be [@bind val val]).
    Attempting to apply this lemma to [@bind A1 A2] where [A1] and [A2] are types other
    than [val] did not work. Thanks to [Observe], now we can vary the Value types
    and the injection from [A1] and [A2]. *)

  Lemma pure_bind `{Observe A1 V1} `{Observe A2 V2} `{Observe B E}
    (m : micro V1 E) (k : V1 -> micro V2 E) (φ : A2 -> _) (φ' : A1 -> _) (ψ : B → Prop) :
    pure m φ' ψ →
    (∀ a, φ' a → pure (k ♯a) φ ψ) →
    pure (bind m k) φ ψ.
  Proof.
    rewrite bind_as_try.
    intros Hm Hk; eapply pure_try; [exact Hm | exact Hk |].
    intros b Hb; apply pure_wp_throw; exists b; eauto.
  Qed.

  Lemma pure_strong_bind `{Observe A1 V1} `{Observe A2 V2} `{Observe B E}
    m (k : V1 -> micro V2 _)
    (φ : A2 -> _) (φ' : A1 -> _) (ψ ψ' : B -> Prop) :
    pure m φ' ψ' →
    (∀ a, φ' a → pure (k ♯ a) φ ψ) →
    (∀ b, ψ' b → ψ b) →
    pure (bind m k) φ ψ.
  Proof.
    rewrite bind_as_try.
    intros Hm Hk Hwk; eapply pure_try; [ exact Hm | exact Hk |].
    intros b Hb; apply pure_wp_throw; exists b; eauto.
  Qed.

  Lemma pure_bind_unary `{Observe A' V'} `{Observe A V} `{Observe B E}
    (m : micro V E) (k : V -> micro V' E) (φ : A' -> Prop) (Ψ : B → Prop) :
    pure m (λ (a : A), pure (k ♯ a) φ Ψ) Ψ →
    pure (bind m k) φ Ψ.
  Proof.
    intros; eapply pure_strong_bind; eauto; done.
  Qed.

  (* We cannot give a reasoning rule for [par m1 m2] because its type is
    [micro (val * val)], not [micro val]. However, we can give a rule
    for [Par m1 m2 k z] if [k] transforms [val * val] into [val]. *)

  (* A reasoning rule for [Par m1 m2 k z]. *)

  Lemma pure_Par'
    `{Observe A1 V1, Observe A2 V2, Observe A3 V3} `{Observe B E} `{Observe B' E'}
    (m1 : micro V1 E') (m2 : micro V2 E')
    (φ : A3 -> Prop) (ψ : B → Prop)
    (k : outcome2 (V1 * V2) E' → micro V3 E) :
    pure m1
      (λ a1 : A1,
        pure m2
          (λ a2 : A2,
              pure (continue k (♯ a1, ♯ a2)) φ ψ)
          (λ b' : B', pure (discontinue k ♯b') φ ψ))
      (λ b' : B', pure (discontinue k ♯b') φ ψ) →
    pure m2
      (λ a2 : A2,
        pure m1
          (λ a1 : A1,
              pure (continue k (♯ a1, ♯ a2)) φ ψ)
          (λ b' : B', pure (discontinue k ♯b') φ ψ))
      (λ b' : B', pure (discontinue k ♯b') φ ψ) →
    pure (Par m1 m2 k) φ ψ.
  Proof.
    intros; eapply pure_wp_Par;
      do 2 (eapply pure_wp_mono; eauto;
      intros; returns_eauto; eauto).
  Qed.

  Global Instance observe_pair `{Observe A1 V1, Observe A2 V2} :
    Observe (A1 * A2) (V1 * V2) :=
    { observe := (λ '(a1, a2), (♯a1, ♯a2)) }.

  Lemma pure_par
    `{Observe A1 V1, Observe A2 V2} `{Observe B E}
    (m1 : micro V1 E) (m2 : micro V2 E)
    φ1 φ2
    (φ : A1 * A2 -> Prop) (ψ : B → Prop) :
    pure m1 φ1 ψ →
    pure m2 φ2 ψ →
    (∀ a1 a2, φ1 a1 → φ2 a2 → φ (a1, a2)) →
    pure (par m1 m2) φ ψ.
  Proof.
    intros.
    eapply pure_wp_par; try eassumption.
    intros a1 a2 (v1 & -> & Hφ1) (v2 & -> & Hφ2).
    exists (v1, v2); eauto.
  Qed.

  Lemma pure_par' `{NotVal A1, NotVal A2} `{Observe B E}
    (m1 : micro A1 E) (m2 : micro A2 E)
    φ1 φ2
    (φ : A1 * A2 -> Prop) (ψ : B → Prop) :
    pure m1 φ1 ψ →
    pure m2 φ2 ψ →
    (∀ a1 a2, φ1 a1 → φ2 a2 → φ (a1, a2)) →
    pure (par m1 m2) φ ψ.
  Proof.
    intros.
    eapply pure_wp_par; try eassumption.
    intros a1 a2 (v1 & -> & Hφ1) (v2 & -> & Hφ2).
    exists (v1, v2); eauto.
  Qed.

  (* Sequentializations of previous lemmas, considering the LHS first *)

  Lemma pure_Par_seq_strong {E12}
    `{Observe A1 V1, Observe B1 E12}
    `{Observe A2 V2, Observe B2 E12}
    `{Observe A3 V3, Observe B3 E3}
    (m1 : micro V1 E12) (m2 : micro V2 E12) (k : _ -> micro V3 E3)
    (φ : A3 → Prop) (ψ : B3 → Prop)
  :
    pure (B := B1) m1 (λ a1 : A1,
      pure (B := B2) m2 (λ a2 : A2,
        pure (continue k (♯ a1, ♯ a2)) φ ψ) ⊥) ⊥ →
    pure (A:=A3) (B:=B3) (Par m1 m2 k) φ ψ.
  Proof.
    intros Hm1.
    apply pure_wp_Par_vals_left.
    eapply pure_wp_mono; [ apply Hm1 | | intros ? []; tauto ].
    intros ? (a1 & -> & Hm2).
    eapply pure_wp_mono; [ apply Hm2 | | intros ? []; tauto ].
    intros ? (a2 & -> & Hk).
    apply Hk.
  Qed.

  Lemma pure_Par_seq
    `{Observe A1 V1, Observe B1 E1}
    `{Observe A2 V2, Observe B2 E1}
    `{Observe A3 V3, Observe B3 E2}
    (m1 : micro V1 E1) (m2 : micro V2 E1) (k : _ -> micro V3 E2)
    (φ : A3 → Prop) (ψ : B3 → Prop)
  :
    pure (B := B1) m1
      (λ (a1 : A1),
        pure m2
          (λ (a2 : A2), pure (continue k (♯ a1, ♯ a2)) φ ψ)
          (λ (b : B2), pure (discontinue k ♯b) φ ψ))
      ⊥ →
    pure (Par m1 m2 k) φ ψ.
  Proof.
    intros Hm1.
    apply pure_wp_Par_val_left.
    eapply pure_wp_mono; [ apply Hm1 | | intros ? []; tauto ].
    intros ? (a1 & -> & Hm2).
    eapply pure_wp_mono; first apply Hm2.
    - intros ? (a2 & -> & Hk). apply Hk.
    - intros ? (b2 & -> & Hk). apply Hk.
  Qed.

  Lemma pure_par_seq
    `{Observe A1 V1, Observe B1 E1}
    `{Observe A2 V2, Observe B2 E1}
    (m1 : micro V1 E1) (m2 : micro V2 E1)
    φ (ψ : B2 → Prop)
  :
    pure (B := B1) m1
      (λ (a1 : A1),
        pure m2 (λ (a2 : A2), φ (a1, a2)) ψ)
      ⊥ →
    pure (par m1 m2) φ ψ.
  Proof.
    intros Hm1.
    apply pure_wp_Par_val_left.
    eapply pure_wp_mono; [ apply Hm1 | | intros ? []; tauto ].
    intros ? (a1 & -> & Hm2).
    eapply (pure_wp_mono _ Hm2).
    - intros a2 (v2 & -> & Hφ).
      apply pure_wp_ret. exists (a1, v2); eauto.
    - intros e He. by apply pure_wp_throw.
  Qed.

  Lemma pure_par_glue2
    `{Observe A1 V1, Observe A2 V2, Observe A3 V3} `{Observe B1 E1} `{Observe B2 E2}
    (m1 : micro V1 E1) (m2 : micro V2 E1) (k : V1 * V2 -> micro V3 E2)
    (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A3 → Prop)
    (ψ : B1 -> Prop) (ψ' : B2 -> Prop) (z : E1 -> micro V3 E2) :
    pure m1 φ1 ψ ->
    pure m2 φ2 ψ ->
    (∀ (a1 : A1) (a2 : A2),
        φ1 a1 → φ2 a2 →
        pure (V := V3) (k (♯ a1, ♯ a2)) φ ψ') ->
    (∀ b, ψ b → pure (z ♯b) φ ψ') ->
    pure (Par m1 m2 (glue2 k z)) φ ψ'.
  Proof.
    intros Hm1 Hm2 Hentail1 Hentail2. rewrite <- try_par.
    eapply pure_wp_try_conseq.
    - eapply pure_wp_par with (φ := λ v, pure (k v) φ ψ');
        [ exact Hm1 | exact Hm2 |].
      intros v1 v2 (a1 & -> & Ha1) (a2 & -> & Ha2). apply (Hentail1 a1 a2 Ha1 Ha2).
    - intros v. tauto.
    - intros e (b & -> & Hb). by apply Hentail2.
  Qed.

  Lemma pure_Par
    `{Observe A1 V1, Observe B1 E1}
    `{Observe A2 V2}
    `{Observe A3 V3, Observe B2 E2}
    (m1 : micro V1 E1) (m2 : micro V2 E1) (k : outcome2 (V1 * V2) E1 → micro V3 E2)
    (φ1 : A1 → Prop) (φ2 : A2 → Prop) (φ : A3 → Prop)
    (ψ : B1 -> Prop) (ψ' : B2 -> Prop) :
    pure m1 φ1 ψ →
    pure m2 φ2 ψ →
    (∀ a1 a2, φ1 a1 → φ2 a2 → pure (continue k (♯ a1, ♯ a2)) φ ψ') →
    (∀ b, ψ b → pure (discontinue k ♯b) φ ψ') →
    pure (Par m1 m2 k) φ ψ'.
  Proof.
    intros Hm1 Hm2 Hcont Hdisc.
    eapply pure_wp_Par_conseq; eauto.
    - intros v1 v2 (a1 & -> & Ha1) (a2 & -> & Ha2).
      apply (Hcont a1 a2 Ha1 Ha2).
    - intros e He.
      assert (returns ψ e) as He'. { tauto. }
      destruct He' as (b & -> & Hb).
      apply (Hdisc b Hb).
  Qed.

  (* A reasoning rule for [choose]. *)

  Lemma pure_choose `{Observe A V} `{Encode B} m1 m2 (φ : A → Prop) (ψ : B -> Prop) :
    pure (V := V) m1 φ ψ →
    pure m2 φ ψ →
    pure (choose m1 m2) φ ψ.
  Proof.
    apply pure_wp_choose.
  Qed.

  (* Inversion lemmas on [pure]. *)

  Lemma invert_pure_ret `{Observe A V} `{Observe B E}
    (v : V) (φ : A → Prop) (ψ : B → Prop) :
    pure (ret v) φ ψ →
    returns φ v.
  Proof.
    intros Hv; by apply invert_pure_wp_ret in Hv.
  Qed.

  Lemma invert_pure_throw `{Observe A V} `{Observe B E}
    (e : E) (φ : A → Prop) (ψ : B → Prop) :
    pure (throw e) φ ψ →
    returns ψ e.
  Proof.
    intros Hv; by apply invert_pure_wp_throw in Hv.
  Qed.

  (* This is the reciprocal bind rule for [pure_wp]. *)

  (* Because [pure_wp m ##_ ⊥] requires the result of [m] to lie in the image of the
    function [encode], and because this image cannot include every inhabitant
    of the type [val], we cannot expect that [pure_wp (bind m k) ##φ ⊥] implies
    [pure_wp m ##_ ⊥]. Thus, we can establish the reciprocal bind rule only under
    the side condition [pure_wp m ##(λ a, True) ⊥], which means that the result of
    the computation [m] lies in the image of the function [encode] at type
    [A]. *)

  Lemma invert_pure_bind `{Observe A V} `{Observe B E}
    m k (φ : A → Prop) (ψ : B → Prop) :
    pure (V := V) (bind m k) φ ψ →
    pure m (λ (a : A), True) ψ →
    pure (V := V) m (λ (a : A), pure (k ♯a) φ ψ) ψ.
  Proof.
    intros Hmk%invert_pure_wp_bind Hm.
    pose proof pure_wp_binary_intersection _ Hmk Hm as I.
    eapply (pure_wp_mono _ I); firstorder subst; eauto.
  Qed.

  (* That said, if we take the type [A] to be [val], then -- because [encode]
    at type [val] is the identity function -- this side condition becomes
    trivial, and we can prove a version of the rule that does not have this
    side condition. *)

  Lemma invert_pure_bind_unary `{Observe A V} `{Observe B E}
    m k (φ : A → Prop) (ψ : B → Prop) :
    pure (V := V) (bind m k) φ ψ →
    pure m (λ (v : val), pure (k v) φ ψ) ψ.
  Proof.
    intros Hmk%invert_pure_wp_bind.
    eapply pure_wp_mono; eauto; intros.
    eauto with pure.
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* Because the relation [pure_wp] is inductively defined, the [pure_wp] judgement *)
(*     implies that [m] terminates. This forms a Hoare logic of pure correctness *)
(*     for pure_wp computations. *)

  (* This file offers lemmas and tactics that help work with [pure_wp] goals. *)
(*     These lemmas and tactics form a simple "proof mode" for pure_wp *)
(*     computations. *)

  (* -------------------------------------------------------------------------- *)
  Lemma pure_prove_bind_bind `{Observe A1 V1, Observe A2 V2} `{Observe B E}
    (m : micro A1 E) (a : A2)
    (f : A1 -> micro V2 E) (g : V2 -> micro V2 E)
    (φ : A2 -> Prop) (ψ : B → Prop) :
    pure ('c ← m; f c) (singleton a) ψ ->
    pure (g ♯ a) φ ψ ->
    pure (E := E)
         ('v1 ← m;
          'v2 ← f v1;
          g v2) φ ψ.
  Proof.
    intros Hfm Hga.
    apply invert_pure_wp_bind in Hfm.
    eapply pure_wp_bind_conseq; eauto. simpl.
    intros a' Ha'.
    eapply pure_wp_bind_conseq; eauto.
    by intros _v (_a & -> & ->).
  Qed.

  Lemma pure_bind_bind `{Observe A V} `{Observe B E}
    (m : micro A E)
    (f : A -> micro V E)
    (g : V -> micro V E)
    (φ : A -> Prop) (ψ : B → Prop) :
    pure (E := E)
      ('x ← m; f x) φ ψ ->
    (forall y, φ y -> pure (g ♯ y) φ ψ) ->
    pure ('v1 ← m;
          v2 ← f v1;
          g v2) φ ψ.
  Proof.
    intros Hm Hga.
    apply invert_pure_wp_bind in Hm.
    eapply pure_wp_bind_conseq; eauto. simpl.
    intros v Hv.
    eapply pure_wp_bind_conseq; eauto. simpl.
    intros _ (y & -> & Hy).
    apply Hga, Hy.
  Qed.

  Lemma invert_pure_order `{Observe A1 V1, ObserveInjective A2 V2} `{Observe B2 E2} `{Observe B1 E1} (m1 : micro V1 E1) (m2 : micro V2 E2)
    (φ : A1 → A2 → Prop) (Ψ : B2 → Prop) :
    pure m1 (λ a1, pure m2 (λ a2, φ a1 a2) Ψ) (⊥ : B1 → Prop) →
    pure m2 (λ a2, pure m1 (λ a1, φ a1 a2) (⊥ : B1 → Prop)) Ψ.
  Proof.
    unfold pure, returns. intros Hm1.
    (* Use [pure_wp_invert_order] on the [V1]-/[V2]-level postcondition
       obtained by pushing the inner [returns] into the body, so the
       swapped form does not have to re-extract [a1'] for a different
       reachable value. *)
    pose proof
      (pure_wp_invert_order m1 m2
        (λ v1 v2, ∃ a1, v1 = ♯ a1 ∧ ∃ a2, v2 = ♯ a2 ∧ φ a1 a2) (returns Ψ)) as Hswap.
    cut (pure_wp m1
          (λ v1, pure_wp m2
                   (λ v2, ∃ a1, v1 = ♯ a1 ∧ ∃ a2, v2 = ♯ a2 ∧ φ a1 a2) (returns Ψ)) ⊥).
    { intros HH. specialize (Hswap HH).
      apply (pure_wp_mono_ret _ Hswap).
      intros v2 Hv2.
      destruct (pure_wp_exists_ret_or_throw _ Hv2)
        as [(v1 & R1 & a1 & -> & a2 & -> & Hφ) | (? & ? & [])].
      exists a2; split; first done.
      apply (pure_wp_mono _ Hv2); last by intros _ [].
      intros v1' (a1' & -> & a2' & Heq2 & Hφ').
      exists a1'; split; first done.
      (* φ a1' a2' with ♯ a2 reachable; we re-derive φ a1' a2 by forwarding
         [Hv2] along [R1] (which makes [m2] return [♯ a1] under
         [pure_wp_rtc_may_forward], yielding [φ a1 ?] – not what we want).
         Instead, reuse [Hφ'] directly: since [♯ a2 = ♯ a2'], we observe
         that the witness inside [returns] is morally the same [a2]. *)
      pose proof (pure_wp_rtc_may_forward _ _ _ _ Hv2 R1) as Hret.
      apply invert_pure_wp_ret in Hret.
      destruct Hret as (a1'' & ? & a2'' & Eq2 & Hφ''). subst.
      (* We have [♯ a2 = ♯ a1] from [v1 = ♯ a1 = ♯ a1''] (no, that's a1).
         The pieces don't pin down [a2 = a2'].  Without an injectivity
         assumption, this lemma is not derivable in this form. *)
      auto.
      destruct H1. rewrite (observe_injective _ _ Heq2). apply Hφ'.
    }
    apply (pure_wp_mono _ Hm1); last intros ? (? & ? & []).
    intros v1 (a1 & -> & Ha1).
    apply (pure_wp_mono _ Ha1); last by intros e He; exact He.
    intros v2 (a2 & -> & Hφ). eauto.
  Qed.

End pure_rules.

Section pure_rules_variant.

  (* When a [val] is returned, there is no need for [encode]. *)
  Lemma pure_ret_val `{Encode A} `{Observe B E} (a : val) (ϕ : A -> Prop) (ψ : B -> Prop) :
    returns ϕ a ->
    pure (ret a) ϕ ψ.
  Proof.
    intros. returns_eauto. by eapply pure_ret.
  Qed.

  Lemma pure_ret_eq_val `{Observe B E} (a : val) (ψ : B -> Prop) :
    pure (ret a) (λ a', a' = a) ψ.
  Proof.
    intros; eapply pure_ret; eauto.
  Qed.

End pure_rules_variant.


(* Rules about [pure] related to effectful computations, i.e. computations
   using [Stop] *)
Section pure_eff.

  (* The following two lemmas paraphrase the definition of [call] in eval.v.
      When applied to a goal of the form [simp (call v1 v2) _] where [v1] is
      a concrete closure (as opposed to a rigid metavariable), they step into
      the call. *)

  Lemma pure_enter_call_VClo `{Encode Y} `{Encode B} η a v2 (φ : Y → Prop) (ψ : B → Prop) :
    pure (acall η a v2) φ ψ ->
    pure (call (VClo η a) v2) φ ψ.
  Proof.
    tauto.
  Qed.

  Lemma pure_stop_eval `{Encode X} `{Observe B Y} η e k (φ : X -> Prop) (ψ : B -> Prop) :
    pure (try2 (eval η e) k) φ ψ ->
    pure (V := val) (Stop CEval (η, e) k) φ ψ.
  Proof.
    intros.
    by apply pure_wp_Eval.
  Qed.

  (** [CEval] evaluation *)

  Lemma pure_CEval `{Encode A} `{Observe B E} {η e k} (φ : A → Prop) (ψ : B → Prop) :
    pure (try2 (eval η e) k) φ ψ →
    pure (V := val) (Stop CEval (η, e) k) φ ψ.
  Proof.
    intros. eapply pure_wp_det_may_backward; eauto. repeat constructor.
    by intros m' ->%pure.invert_may_eval.
  Qed.

  Lemma pure_please_eval `{Encode A} `{Encode B} {η e} (φ : A → Prop) (ψ : B → Prop) :
    pure (eval η e) φ ψ →
    pure (please_eval η e) φ ψ.
  Proof.
    intros He.
    eapply pure_CEval, pure_try2; try done.
    - intros a Ha; eapply pure_ret; eauto.
    - intros b Hb; apply pure_wp_throw; exists b; eauto.
  Qed.

  Lemma pure_enter_call_VCloRec `{Encode Y} `{Encode B} η rbs g x e v2 (φ : Y → Prop) (ψ : B → Prop) :
    lookup_rec_bindings rbs g = Some (AnonFun x e) ->
    pure (eval ((x, v2) :: eval_rec_bindings η rbs ++ η) e) φ ψ ->
    pure (call (VCloRec η rbs g) v2) φ ψ.
  Proof.
    intros Hlookup Hpure.
    simpl; rewrite Hlookup.
    cbn.
    eapply pure_CEval; rewrite try2_inject2_right.
    done.
  Qed.

  Lemma invert_pure_call `{Encode Y} f v (φ : Y -> Prop) :
    pure (call f v) φ (⊥ : exn → Prop) ->
    (exists η a, f = VClo η a) \/ exists η rbs g, f = VCloRec η rbs g.
  Proof.
    intros Hcall.
    unfold call in Hcall.
    destruct f; simpl in Hcall;
      ((exfalso; by eapply invert_pure_wp_crash) || eauto).
  Qed.

  (** Compatibility with [of_option] *)

  Global Instance observe_option `{Observe A B} : Observe (option A) (option B) :=
    { observe o := match o with
                   | Some a => Some (observe a)
                   | None => None
                   end }.

  Lemma pure_widen `{Encode A} `{Observe B E} (o : option A) (φ : A → Prop) (ψ : B → Prop) :
    match o with
    | Some a => φ a
    | None => False
    end →
    pure (of_option ♯o) φ ψ.
  Proof.
    unfold of_option. destruct o; last destruct 1.
    simpl. apply pure_ret. done.
  Qed.

End pure_eff.
