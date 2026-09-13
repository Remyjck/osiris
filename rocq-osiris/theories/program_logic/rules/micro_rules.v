From Stdlib Require Import Program.Equality.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
Require Import subjective_step ewp tactics.

Require Import basic_rules.

Import ewp_rules_tactics.

(** This file contains introduction and elimination rules for terminal [micro] computations, at the [ewp_def] level. *)

(* ------------------------------------------------------------------------ *)

Section ewp_basic_rules.

  Context `{!osirisGS Σ}.
  Import ewp_rules_tactics.

  Context {A X : Type}.
  Context {E : coPset} {Ψ : iEff Σ} {Q : outcome2 A X → iProp Σ}.

  Implicit Type m : micro A X.

  (* Values *)
  Lemma ewp_ret v :
    Q (O2Ret v) -∗ ewp_def E (ret v : micro A X) Ψ Q.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_ret_inv v :
    ewp_def E (Ret v : micro A X) Ψ Q ={E}=∗ Q (O2Ret v).
  Proof.
    iIntros "HRet".
    by rewrite ewp_unfold /ewp_pre.
  Qed.

  Lemma ewp_throw (e : X) :
    Q (O2Throw e) -∗ ewp_def E (Throw e : micro A X) Ψ Q.
  Proof. iIntros "Hζ". by rewrite ewp_unfold /ewp_pre. Qed.

  Lemma ewp_throw_inv v :
    ewp_def E (Throw v : micro A X) Ψ Q ={E}=∗ Q (O2Throw v).
  Proof.
    iIntros "HThrow".
    by rewrite ewp_unfold /ewp_pre.
  Qed.

  Lemma ewp_crash_inv :
    ewp_def E (Crash : micro A X) Ψ Q ={E}=∗ False.
  Proof.
    ewp_unfold (@Crash A X).
    by iIntros "Hsi".
  Qed.

  Lemma ewp_outcome2 o :
    Q o -∗ ewp_def E (inject2 o : micro A X) Ψ Q.
  Proof.
    iIntros "HΦ". destruct o; simpl.
    - by iApply ewp_ret.
    - by iApply ewp_throw.
  Qed.

  Lemma ewp_outcome2_inv o :
    ewp_def E (inject2 o : micro A X) Ψ Q ={E}=∗ Q o.
  Proof.
    iIntros "Hv".
    ewp_unfold (inject2 o); by destruct o.
  Qed.

  Lemma ewp_outcome2_fupd o :
    (|={E}=> Q o) -∗ ewp_def E (inject2 o : micro A X) Ψ Q.
  Proof.
    iIntros "HΦ".
    rewrite ewp_unfold /ewp_pre.
    by destruct o.
  Qed.

End ewp_basic_rules.

(* ------------------------------------------------------------------------ *)
(* Invert cases where there are premises of the form
          [ewp_def _ (ret _) _ _], [ewp_def _ Crash _ _], or [ewp_def _ (throw _) _ _] *)

Ltac ewp_invert :=
  lazymatch goal with
  (* ewp_def throw *)
  | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (throw _) _ _)] =>
      iPoseProof (ewp_throw_inv with "[$]") as "HΦ"
  (* ewp_def ret *)
  | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (ret _) _ _)] =>
      iPoseProof (ewp_ret_inv with "[$]") as "HΦ"
  (* ewp_def crash *)
  | |- context [environments.Esnoc _ ?Hwp (ewp_def _ Crash _ _)] =>
      iMod (ewp_crash_inv with "[$]") as "%"
  | |- context [environments.Esnoc _ ?Hwp (ewp_def _ (crash _) _ _)] =>
      iMod (ewp_crash_inv with "[$]") as "%"
  end.

(* -------------------------------------------------------------------------- *)

(* Effect and handler rules *)

Section ewp_rules.

  Context `{!osirisGS Σ}.

  Context {A X : Type}.
  Context {ι : thread} {E : coPset} {Ψ : iEff Σ} {Q : outcome2 A X → iProp Σ}.

  Implicit Type m : micro A X.
  Import ewp_rules_tactics.

  Lemma is_ewp_case_try2_None {B X'} m (f : _ -> micro B X'):
    is_ewp_case m = WPStep ->
    is_ewp_case (try2 m f) = WPStep.
  Proof.
    intros Hm. destruct m; inversion Hm; try done.
    destruct c; inversion H0; try done.
  Qed.

  Lemma is_ewp_case_try_None {B X'} m (f : A -> micro B X') (h : X -> micro B X'):
    is_ewp_case m = WPStep ->
    is_ewp_case (try m f h) = WPStep.
  Proof.
    intros Hm.
    unfold try.
    by apply is_ewp_case_try2_None.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** *Try rule *)

  Lemma ewp_try2 {B X'} m (f : _-> micro B X') Φ :
    ewp_def E m Ψ (λ o, ewp_def E (f o) Ψ Φ) -∗
    ewp_def E (try2 m f) Ψ Φ.
  Proof.
    iIntros "Hwp".
    iLöb as "IH" forall (m).
    ewp_case m.
    (* Case: [m1] is an outcome2. *)
    (* The result is immediate. *)
    { rewrite try2_inject2.
      iPoseProof (ewp_outcome2_inv with "Hwp") as "Hret"; cbn.
      iApply (fupd_ewp with "Hret"). }
    (* Case : [m1] is [crash]; trivial  *)
    { iClear "IH".
      iApply fupd_ewp.
      ewp_unfold (@Crash A X); by iMod "Hwp". }
    (* Case : [m1] is [Perform _ _]. *)
    { cbn.
      ewp_unfold_all.
      iMod "Hwp"; iModIntro.
      iApply (monotonic_prot with "[-Hwp] Hwp").
      iIntros (o) "Hwp !>".
      iApply ("IH" with "Hwp"). }
    { (* If [m] can step, then so can [try m f h]. *)
      pose proof (is_ewp_case_try2_None m f Hhm) as Hhm2.
      ewp_unfold_all. rewrite Hhm. rewrite Hhm2.
      (* Process a step of computation. *)
      intro_state. spec_state.
      iModIntro. pose proof Hstep as Hcp. apply invert_reducible in Hstep.
      destruct Hstep as [ Hstep | Hstep ].
      { (* Case: [m1] is [Join _]. *)
        destruct Hstep as (ι' & k & -> & Hdom).
        discriminate.  }
      destruct Hstep as [ Hstep | Hstep ].
      { (* Case: [m1] is [Fork _] *)
        destruct Hstep as (v1 & v2 & k & ->).
        simpl try2. construct_wp_nonret.
        remember (v1, v2) as p.
        destruct_subjective_step.
        eassert (subjective_step (σ', Stop CFork (v1, v2) k, dom π) _ _).
        { eapply ForkS. eassumption. }
        spec_step.
        ewp_mask_elim. iMod "Hwp" as "(Hwp & $)".
        iModIntro.
        iApply ("IH" with "Hwp"). }
      destruct Hstep as [ Hstep | Hstep ].
      { destruct Hstep as (Y & c & y & k & ->).
        iSplitR; [ iPureIntro; by apply reducible_try2 | ].
        simpl try2. cbn match.
        iIntros (σ' m' μ) "%Hstep2".
        dependent destruction Hstep2.
        { exfalso. eapply (no_step_Resolve _ c _ (pftry2 k f)); exact H. }
        (* [ResolveS] leaves the outcome abstract; recover its shape, which
           is what reduces [try2] here. *)
        destruct_is_result o;
          rewrite ?try2_inject2;
          eassert (subjective_step
                     (σ, Stop (CResolve c) (x0, p, v) k, dom π) _ _)
            by (by eapply ResolveS);
          spec_step;
          ewp_mask_elim; iMod "Hwp" as "(Hwp & $)";
          iModIntro; rewrite ?try2_inject2; iApply ("IH" with "Hwp"). }
      (* Get more information out of [e2]; *)
      construct_wp_nonret.
      pose proof (can_step_try2 _ _ f Hstep) as Hstep2.
      pose proof (invert_can_step_subjective_step _ _ _ _ _ _ _ Hstep0 Hstep2) as (_ & -> & ->).
      eapply invert_subjective_step_try2 in Hstep0; last assumption.
      destruct Hstep0 as (?&->&Hstep0).
      (* Can use information from above to get [wp] about stepped computation *)
      spec_step.
      ewp_mask_elim. iDestruct "Hwp" as ">(Hwp & $)"; iFrame.
      iModIntro.
      (* Apply induction hypothesis  *)
      by iApply ("IH" with "Hwp"). }
    (* Case: [WPJoin] *)
    { simpl. ewp_unfold_all.
      intro_state_join. spec_state_join. iMod "Hwp".
      destruct (π !! x); last done.
      iIntros "!> !> %o Ho". iSpecialize ("Hwp" with "Ho").
      ewp_mask_elim.
      iMod "Hwp" as "[Hwp $]".
      iModIntro.
      iApply ("IH" with "Hwp"). }
  Qed.

  Lemma ewp_try {B X'} m (f : A -> micro B X') (h : X -> micro B X') Φ :
    ewp_def E m Ψ
      (λ o, match o with
            | O2Ret v => ewp_def E (f v) Ψ Φ
            | O2Throw e => ewp_def E (h e) Ψ Φ
            end) -∗
    ewp_def E (try m f h) Ψ Φ.
  Proof.
    iIntros "Hwp".
    iApply ewp_try2.
    iApply (ewp_mono with "Hwp").
    iIntros ([|]) "Hwp"; by cbn.
  Qed.

  (** *Bind rule *)
  Lemma ewp_bind {B} m (k : _ -> micro B X) Φ :
    ewp_def E m  Ψ
      (λ o, match o with
            | O2Ret v => ewp_def E (k v) Ψ Φ
            | O2Throw e => Φ (O2Throw e)
            end) -∗
    ewp_def E (bind m k) Ψ Φ.
  Proof.
    iIntros "Hwp". rewrite bind_as_try. iApply ewp_try.
    iApply (ewp_mono with "[$]").
    iIntros ([v|e]).
    - iIntros "$".
    - iIntros "Hexn".
      iApply (ewp_throw with "Hexn").
  Qed.

  (* Par combinator *)

  Lemma ewp_Par {A1 A2 X'} (m1 : micro A1 X') (m2 : micro A2 X')
    (k: outcome2 (A1 * A2) X' → micro A X) Φ1 Φ2 :
    ewp_def E m1 Ψ Φ1 -∗
    ewp_def E m2 Ψ Φ2 -∗
    (∀ e, Φ1 (O2Throw e) -∗ ▷ ewp_def E (k (O2Throw e)) Ψ Q) ∧
    (∀ e, Φ2 (O2Throw e) -∗ ▷ ewp_def E (k (O2Throw e)) Ψ Q) ∧
    (∀ v1 v2,
       Φ1 (O2Ret v1) -∗ Φ2 (O2Ret v2) -∗
       ▷ ewp_def E (k (O2Ret (v1, v2))) Ψ Q) -∗
    ewp_def E (Par m1 m2 k) Ψ Q.
  Proof.
    iIntros "H1 H2 Hjoin".
    (* We proceed by Löb-induction after generalizing [m1] [m2] and [k]. *)
    iLöb as "IH" forall (m1 m2).

    ewp_unfold_head.
    intro_state.

    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_subjective_step; cbn; iMod "Hmod" as "_"; cbn; rename π into π'.

    { (* Case: [StepParRetRet].. *)
      ewp_invert; iRename "HΦ" into "HΦ2"; ewp_invert; iFrame.
      iMod "HΦ". iMod "HΦ2".
      iSpecialize ("Hjoin" with "HΦ HΦ2").
      ewp_mask_intro "Hmod"; ewp_mask_elim.
      iApply "Hjoin". }

    (* In the four following cases, one of the branches of the [Par] is either a
     [crash] or [throw _].

     We invert the cases where there are premises of the form [WP crash _] or
     [WP (throw _) _] *)
     1-4: ewp_invert; try done.

    (* [StepParThrowLeft/Right] *)
    { iMod "HΦ".
      iDestruct "Hjoin" as "[Hexn1 _]".
      iSpecialize ("Hexn1" with "[$]").
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame. }
    { iMod "HΦ".
      iDestruct "Hjoin" as "[_ [Hexn2 _]]".
      iSpecialize ("Hexn2" with "[$]").
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame. }

    { (* [StepThroughParLeft]. *)
      destruct_code.
      - (* [ParPerformLeft] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        ewp_unfold (Stop CPerf x k0).
        ewp_unfold_head.
        iMod "H1"; iModIntro.

        iApply (monotonic_prot with "[H2 Hjoin] H1").
        iIntros (?) "Hk".
        iNext.
        iApply ("IH" with "Hk H2 Hjoin").

      - (* Step then [ForkS]. *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        destruct x.
        rewrite (ewp_unfold (Stop CFork (v, v0) _)) /ewp_pre /=.
        clear κs.
        ewp_unfold_head. intro_state. spec_state. iModIntro.
        construct_wp_nonret. destruct_subjective_step.
        epose proof (ForkS _ _ _ _ _ _ H0).
        iSpecialize ("H1" $! _ _ _ H1).
        ewp_mask_elim. iMod "H1" as "(H1 & $)".
        iApply ("IH" with "H1 H2 Hjoin").

      - (* Step then [JoinS]. *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        rewrite (ewp_unfold (Stop CJoin x _)) /ewp_pre /=.
        clear κs.
        ewp_unfold_head. intro_state_join. spec_state_join. iMod "H1".
        destruct (π !! x); last done.
        iIntros "!> !> %o Ho". iSpecialize ("H1" with "Ho").
        ewp_mask_elim. iMod "H1" as "(H1 & $)".
        iApply ("IH" with "H1 H2 Hjoin").

      - ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        rewrite (ewp_unfold (Stop (CResolve c) x _)) /ewp_pre /=.
        clear κs.
        ewp_unfold_head. intro_state. spec_state. iModIntro.
        iSplitR; [ iPureIntro; by eapply reducible_resolve_cont | ].
        iIntros (σ'' m'' μ) "%Hstep2".
        dependent destruction Hstep2.
        { exfalso. eapply (no_step_Resolve _ _ _ _); eassumption. }
        (* An outcome is handed to the continuation; a crash aborts. *)
        destruct_is_result o;
          epose proof (ResolveS _ _ _ _ _ _ _ _ _ H0 ltac:(eassumption)) as Hs;
          rewrite ?try2_inject2 in Hs;
          iSpecialize ("H1" $! _ _ _ Hs);
          ewp_mask_elim; iMod "H1" as "(H1 & $)".
        + rewrite try2_inject2. iApply ("IH" with "H1 H2 Hjoin").
        + iApply fupd_ewp; iMod (ewp_crash_inv with "H1") as "[]". }

    { (* [StepThroughParRight]. *)
      destruct_code.

      - (* [StepParPerformRight] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        ewp_unfold (Stop CPerf x k0).
        ewp_unfold_head.
        iMod "H2"; iModIntro.
        iApply (monotonic_prot with "[H1 Hjoin] H2").
        iIntros (?) "H2".
        iNext.
        iApply ("IH" with "H1 H2 Hjoin").

      - (* [StepParForkRight] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        destruct x.
        rewrite (ewp_unfold (Stop CFork (v, v0) _)) /ewp_pre /=.
        clear κs.
        ewp_unfold_head. intro_state. spec_state. iModIntro.
        construct_wp_nonret. destruct_subjective_step.
        epose proof (ForkS _ _ _ _ _ _ H0).
        iSpecialize ("H2" $! _ _ _ H1).
        ewp_mask_elim. iMod "H2" as "(H2 & $)".
        iApply ("IH" with "H1 H2 Hjoin").

      - (* [StepParJoinRight] *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        rewrite (ewp_unfold (Stop CJoin x _)) /ewp_pre /=.
        clear κs.
        ewp_unfold_head. intro_state_join. spec_state_join. iMod "H2".
        destruct (π !! x); last done.
        iIntros "!> !> %o Ho". iSpecialize ("H2" with "Ho").
        ewp_mask_elim. iMod "H2" as "(H2 & $)".
        iApply ("IH" with "H1 H2 Hjoin").

      - (* [StepParResolveRight]: the mirror image of the left case. *)
        ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
        rewrite (ewp_unfold (Stop (CResolve c) x _)) /ewp_pre /=.
        clear κs.
        ewp_unfold_head. intro_state. spec_state. iModIntro.
        iSplitR; [ iPureIntro; by eapply reducible_resolve_cont | ].
        iIntros (σ'' m'' μ) "%Hstep2".
        dependent destruction Hstep2.
        { exfalso. eapply (no_step_Resolve _ _ _ _); eassumption. }
        destruct_is_result o;
          epose proof (ResolveS _ _ _ _ _ _ _ _ _ H0 ltac:(eassumption)) as Hs;
          rewrite ?try2_inject2 in Hs;
          iSpecialize ("H2" $! _ _ _ Hs);
          ewp_mask_elim; iMod "H2" as "(H2 & $)".
        + rewrite try2_inject2. iApply ("IH" with "H1 H2 Hjoin").
        + iApply fupd_ewp; iMod (ewp_crash_inv with "H2") as "[]". }

    { (* [ParLeft] *)
      eapply BaseS in H as Hstep.
      iCombine "Hsi Hpi Hti" as "Hsi".
      iPoseProof (ewp_step _ _ _ Hstep with "Hsi H1") as ">H1".
      iMod "H1". ewp_mask_elim. iMod "H1" as "(H1 & $)".
      iApply ("IH" with "H1 H2 Hjoin"). }

    { (* [ParRight] *)
      eapply BaseS in H as Hstep.
      iCombine "Hsi Hpi Hti" as "Hsi".
      iPoseProof (ewp_step _ _ _ Hstep with "Hsi H2") as ">H2".
      iMod "H2". ewp_mask_elim. iMod "H2" as "(H2 & $)".
      iApply ("IH" with "H1 H2 Hjoin"). }
  Qed.

End ewp_rules.
