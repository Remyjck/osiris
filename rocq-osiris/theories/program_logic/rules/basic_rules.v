From Stdlib Require Import Program.Equality.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.bi Require Import derived_laws.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.

Require Import subjective_step ewp tactics.

From osiris.pure_logic Require Export pure.

(** This file contains basic structural rules for [ewp_def]. *)

(* ------------------------------------------------------------------------ *)
Section ewp.
  Import ewp_rules_tactics.

  Context `{!osirisGS Σ}.
  Context {A X : Type}.
  Implicit Type m : micro A X.

  (* ------------------------------------------------------------------------ *)

  Lemma ewp_step {E Ψ Q} {σ π σ' κ κs} m m' μ :
    subjective_step (σ, m, dom π) κ (σ', m', μ) →
    state_interp (σ, κ ++ κs, π) -∗
    ewp_def E m Ψ Q ==∗
    |={E}[∅]▷=>
        ewp_def E m' Ψ Q ∗
          (match μ with
           | None => state_interp (σ', κs, π)
           | Some (ι', m') => ∃ φ', state_interp (σ', κs, <[ι':= φ']>π) ∗
                                        ewp_def ⊤ m' ⊥ (λ o, □ φ' o)
          end).
  Proof.
    intros Hstep.
    iIntros "Hsi Hwp".
    ewp_unfold m.
    ewp_case m.
    spec_state. iModIntro. iMod "Hwp" as "[%Hprog Hwp]".
    spec_step.
    by ewp_mask_elim.
  Qed.

  (* ------------------------------------------------------------------------ *)

  (** Monotonicity. *)
  Lemma ewp_strong_mono E1 E2 m Ψ1 Ψ2 Q' Q :
    E1 ⊆ E2 →
    ewp_def E1 m Ψ1 Q' -∗
    (Ψ1 ⊑ Ψ2)%ieff -∗
    (∀ o, Q' o ={E2}=∗ Q o) -∗
    ewp_def E2 m Ψ2 Q.
  Proof.
    iIntros (HE) "Hwp #Hmonoprot Hmono".
    iLöb as "IH" forall (m).
    ewp_unfold m.
    ewp_case m.
    (* Case: [m] is a [WPOutcome] *)
    { iApply ("Hmono" with "[> -]").
      by iApply (fupd_mask_mono E1 _). }

    (* Case: [m] is a [WPCrash]. *)
    { by iApply (fupd_mask_mono E1 _). }

    { (* Case: [m] is a [WPPerform]. We use [prot_mono]. *)
      iApply (fupd_mask_mono E1 _). set_solver.
      iMod "Hwp"; iModIntro.
      iDestruct "Hwp" as (φ) "(Hwp & HΨ)"; iExists φ.
      iSplitL "Hwp"; first iApply ("Hmonoprot" with "Hwp"); cbn.
      iIntros (?) "Hφ". iSpecialize ("HΨ" with "Hφ").
      iNext; iApply ("IH" with "HΨ Hmono"). }

    { (* Case: [m] is a [WPStep]. *)
      intro_state. iMod (fupd_mask_subseteq E1) as "Hmod". set_solver.
      spec_state. iModIntro.
      discharge_pure assumption.
      clear Hstep.
      iIntros (σ' m' μ) "%Hstep".
      spec_step.
      ewp_mask_elim. iMod "Hwp" as "(Hwp & Hforked)". iFrame.
      iMod "Hmod".
      iApply ("IH" with "Hwp Hmono"). }

    { (* Case: [m] is a [WPJoin]. *)
      intro_state_join. iMod (fupd_mask_subseteq E1) as "Hmod". set_solver.
      spec_state_join.
      iMod "Hwp". iModIntro.
      destruct (π !! t) as [φ'|] eqn:Hlookup.
      - iIntros "!> %o Ho". iSpecialize ("Hwp" with "Ho").
        ewp_mask_elim. iMod "Hwp" as "(Hwp & Hforked)". iFrame.
        iMod "Hmod".
        iApply ("IH" with "Hwp Hmono").
      - iMod "Hwp". by iMod "Hmod". }
  Qed.

  Local Tactic Notation "ewp_mono" "with" constr(s) :=
    iApply (ewp_strong_mono with s); auto; first iApply iEff_le_refl.

  Lemma ewp_prot_mono E m Ψ1 Ψ2 Q :
    (Ψ1 ⊑ Ψ2)%ieff -∗
    ewp_def E m Ψ1 Q -∗
    ewp_def E m Ψ2 Q.
  Proof. iIntros "Hprot Hm". iApply (ewp_strong_mono E E with "Hm Hprot"); auto. Qed.

  Lemma fupd_ewp E m Ψ Q :
    (|={E}=> ewp_def E m Ψ Q) ⊢ ewp_def E m Ψ Q.
  Proof.
    iIntros "He".
    ewp_unfold_all.
    ewp_case m; try iMod "He"; done.
  Qed.

  (* Eliminate update modality in postcondition *)
  Lemma ewp_fupd E m Ψ Q :
    ewp_def E m Ψ (λ o, |={E}=> Q o) -∗
    ewp_def E m Ψ Q.
  Proof. iIntros "He". ewp_mono with "He". Qed.

  Definition to_eff m :=
    match m with
    | Stop CPerf e k => Some e
    | _ => None
    end.

  Definition to_join m :=
    match m with
    | Stop CJoin ι k => Some ι
    | _ => None
    end.

  Lemma ewp_atomic E E2 m Ψ Q `{!subjective_step.Atomic m} :
    TCEq (to_eff m) None →
    TCEq (to_join m) None →
    (|={E,E2}=> ewp_def E2 m Ψ (λ o, |={E2,E}=> Q o)) ⊢ ewp_def E m Ψ Q.
  Proof.
    iIntros "%Heff %Hjoin Hm".
    ewp_unfold_all.
    ewp_case m.
    { by iDestruct "Hm" as ">>> $". }
    { by iDestruct "Hm" as ">> []". }
    { inversion Heff. }
    { intro_state.
      iMod "Hm".

      spec_state. iModIntro.

      construct_wp_nonret.
      iSpecialize ("Hm" $! σ' m' μ Hstep0).
      ewp_mask_elim. iMod "Hm" as "(Hewp & $)".
      (* Use atomicity. *)
      edestruct H; first eassumption; rewrite H0.
      - ewp_unfold_all.
        by iDestruct "Hewp" as ">>$".
      - ewp_unfold_all.
        by iDestruct "Hewp" as ">>$".
      - ewp_unfold_all.
        by iDestruct "Hewp" as ">[]". }

    { inversion Hjoin. }
  Qed.

  (* A fancy update that takes a step can be eliminated around a computation
     that takes a step. *)
  Lemma ewp_step_fupd E1 E2 m Ψ P Q :
    TCEq (is_ewp_case m) WPStep →
    E2 ⊆ E1 →
    (|={E1}[E2]▷=> P) -∗
    ewp_def E2 m Ψ (λ o, P ={E1}=∗ Q o) -∗
    ewp_def E1 m Ψ Q.
  Proof.
    iIntros (Hcase HE) "HR H".
    apply TCEq_eq in Hcase.
    ewp_unfold_all. rewrite Hcase.
    iIntros (σ κ κs π) "Hsi". iMod "HR".
    iMod ("H" with "Hsi") as "[$ H]".
    iIntros "!>" (σ' m' μ Hstep).
    iMod ("H" $! σ' m' μ with "[//]") as "H".
    iIntros "!> !>". iMod "H" as "[H $]". iMod "HR". iModIntro.
    iApply (ewp_strong_mono with "H"); [done|iApply iEff_le_refl|].
    iIntros (o) "HQ". by iApply "HQ".
  Qed.

  (** Derived rules *)

  Lemma ewp_mono E m Ψ Q' Q : (∀ o, Q' o ⊢ Q o) → ewp_def E m Ψ Q' ⊢ ewp_def E m Ψ Q.
  Proof.
    iIntros (HΦ) "H"; ewp_mono with "H".
    iIntros (v) "?". by iApply HΦ.
  Qed.

  Lemma ewp_mask_mono E1 E2 m Ψ Q :
    E1 ⊆ E2 →
    ewp_def E1 m Ψ Q ⊢ ewp_def E2 m Ψ Q.
  Proof. iIntros (?) "H". ewp_mono with "H". Qed.

  Global Instance ewp_mono' E m Ψ :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (ewp_def E m Ψ).
  Proof. by intros Φ Φ' ?; apply ewp_mono. Qed.

  Global Instance ewp_flip_mono' E m Ψ :
    Proper (pointwise_relation _ (CRelationClasses.flip (⊢)) ==> (CRelationClasses.flip (⊢))) (ewp_def E m Ψ).
  Proof. by intros Φ Φ' ?; apply ewp_mono. Qed.

  Lemma ewp_frame_l E m Ψ Φ R : R ∗ ewp_def E m Ψ Φ ⊢ ewp_def E m Ψ (λ o, R ∗ Φ o).
  Proof. iIntros "[? H]". iApply (ewp_strong_mono with "H"); auto with iFrame. iApply iEff_le_refl. Qed.
  Lemma ewp_frame_r E m Ψ Φ R : ewp_def E m Ψ Φ ∗ R ⊢ ewp_def E m Ψ (λ o, Φ o ∗ R).
  Proof. iIntros "[H ?]". iApply (ewp_strong_mono with "H"); auto with iFrame. iApply iEff_le_refl. Qed.

  Lemma ewp_wand E m Ψ Q' Q :
    ewp_def E m Ψ Q' -∗ (∀ v, Q' v -∗ Q v) -∗ ewp_def E m Ψ Q.
  Proof.
    iIntros "Hwp H". ewp_mono with "Hwp".
    iIntros (?) "?". by iApply "H".
  Qed.
  Lemma ewp_wand_l E m Ψ Q' Q :
    (∀ v, Q' v -∗ Q v) ∗ ewp_def E m Ψ Q' ⊢ ewp_def E m Ψ Q.
  Proof. iIntros "[H Hwp]". iApply (ewp_wand with "Hwp H"). Qed.
  Lemma ewp_wand_r E m Ψ Q' Q :
    ewp_def E m Ψ Q' ∗ (∀ v, Q' v -∗ Q v) ⊢ ewp_def E m Ψ Q.
  Proof. iIntros "[Hwp H]". iApply (ewp_wand with "Hwp H"). Qed.
  Lemma ewp_frame_wand E m Ψ Φ R :
    R -∗ ewp_def E m Ψ (λ o, R -∗ Φ o) -∗ ewp_def E m Ψ Φ.
  Proof.
    iIntros "HR HWP". iApply (ewp_wand with "HWP").
    iIntros (v) "HΦ". by iApply "HΦ".
  Qed.

End ewp.

Section ewp_pure.

  Context `{!osirisGS Σ}.
  Import ewp_rules_tactics.

  Lemma pure_ewp {A X} E Ψ (φ : A → Prop) (ζ : X → Prop) m :
    pure_wp m φ ζ →
    ⊢ ewp_def E m Ψ (ilift (λ e, ⌜ζ e⌝) (λ v, ⌜φ v⌝)).
  Proof.
    iIntros (Hm).
    iLöb as "IH" forall (m Hm).
    iApply ewp_unfold; rewrite /ewp_pre /=.
    ewp_case m.
    - iModIntro. destruct o; iPureIntro.
      + by eapply invert_pure_wp_ret in Hm.
      + by eapply invert_pure_wp_throw in Hm.
    - (* [crash]'s satisfy [ψ] *)
      by eapply invert_pure_wp_crash in Hm.
    - (* [perform] is not immediately pure *)
      by apply invert_pure_wp_stop in Hm.
    - (* Case: [m] can step *)
      intro_state.
      ewp_mask_intro "Hmod".
      assert (∀ σ, can_step (σ, m)) by
        (destruct (pure_wp_progress m Hm) as [(a, ->)|[(e, ->)|]]; auto; discriminate).
      construct_wp_nonret.
      (* and no step can change [σ] or escape [pure] *)
      ewp_cleanup_mod. ewp_mask_elim.
      specialize (H σ).
      apply invert_can_step_subjective_step in Hstep; last assumption.
      destruct Hstep as (Hstep & -> & ->).
      destruct (pure_wp_preservation Hm Hstep) as (Hm' & <-).
      iFrame.
      by iApply "IH".
    - by apply invert_pure_wp_stop in Hm.
  Qed.

  Lemma ewp_pure `{Encode A} (m : micro val exn) (ζ : exn → Prop) (φ : A → Prop) :
    pure m φ ζ →
    ⊢ EWP m ⟨⟨ e, ⌜ζ e⌝ ⟩⟩ {{ x, ⌜φ x⌝ }} .
  Proof.
    iIntros (Hpure).
    iApply ewp_mono; last (iApply pure_ewp; apply Hpure).
    iIntros ([v|e]).
    - iIntros "(%a & %Henc & %Ha)".
      iPureIntro.
      exists a. auto.
    - iIntros "%He".
      iPureIntro.
      destruct He as (c & -> & Hc). exists c. auto.
  Qed.

End ewp_pure.
