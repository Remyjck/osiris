From iris.proofmode Require Import base ltac_tactics classes.
From iris.base_logic.lib Require Import iprop wsat gen_heap own token.
From iris.algebra Require Import gmap_view agree auth gmap.

From osiris.lang Require Import thread_ids.
From osiris.semantics Require Import eval.
From osiris.program_logic Require Import
  subjective_step ewp basic_rules micro_rules tactics.
Require Import satisfiable.base_logic_extension satisfiable.

From Stdlib Require Import Program.Equality.

(* [πp] is the post_map itself: the postconditions are stored in it directly,
   so there is no second map pairing gnames with the predicates they name. *)
Definition WPTP `{!osirisGS Σ} (π : thpool) (πp : post_map Σ) : iProp Σ :=
  ([∗ map] ι ↦ m; φ ∈ π; πp, ewp_def ⊤ m ⊥ (λ o, □ φ o)).

Definition is_final {A E} (m : micro A E) : Prop :=
  match m with
  | Ret _ | Throw _ => True
  | _ => False
  end.

Definition is_join {A E} (m : micro A E) : Prop :=
  match m with
  | Stop CJoin _ _ => True
  | _ => False
  end.

Definition not_stuck {A E} (m : micro A E) σ (π : gset thread) :=
  is_final m ∨ reducible m σ π ∨ is_join m.


(* -------------------------------------------------------------------------- *)
(* General gmap helper lemmas *)

Lemma not_elem_of_lookup {K} `{FinMapDom K M D} {A} (ι ι' : K) (π : M A) (m : A) :
  ι' ≠ ι ->
  π !! ι' = None ->
  (<[ ι := m ]> π) !! ι' = None.
Proof.
  intros Hneq Hlookup.
  apply not_elem_of_dom.
  rewrite dom_insert.
  apply not_elem_of_union; split.
  - apply not_elem_of_singleton.
    apply Hneq.
  - apply not_elem_of_dom. apply Hlookup.
Qed.

Lemma lookup_delete_ne_inv {K} `{Countable K} {A} (m : gmap K A) (i j : K) (x : A) :
  i ≠ j →
  m !! j = Some x →
  delete i m !! j = Some x.
Proof. intros. by rewrite lookup_delete_ne. Qed.

(* [insert_list] takes a list of bindings, a gmap,
   and inserts every binding into the gmap in order. *)
Fixpoint insert_list {A : Type} l (πp : gmap thread A) :=
    match l with
    | [] => πp
    | (ι, φ) :: t => <[ι:=φ]>(insert_list t πp)
    end.

Lemma insert_list_app {A : Type} l l' (πp : gmap thread A) :
  insert_list (l' ++ l) πp = insert_list l' (insert_list l πp).
Proof.
  induction l' as [ | [ι' φ'] l'].
  - reflexivity.
  - simpl. f_equal.
    apply IHl'.
Qed.

Lemma insert_list_lookup_not_in {A} ι l (πp : gmap thread A) :
  ι ∉ fst <$> l →
  insert_list l πp !! ι = πp !! ι.
Proof.
  induction l as [| [ι' a] l IH]; first done.
  rewrite fmap_cons not_elem_of_cons. simpl.
  intros [Hneq Hnin].
  rewrite lookup_insert_ne; first by apply IH.
  by symmetry.
Qed.

Lemma not_elem_of_insert_list {A} ι l (πp : gmap thread A) :
  ι ∉ dom (insert_list l πp) →
  (ι ∉ fst <$> l) ∧ ι ∉ dom πp.
Proof.
  induction l as [| [ι' a] l IH].
  - simpl.
    intros Hnin.
    split; [ apply not_elem_of_nil | exact Hnin ].
  - simpl. rewrite dom_insert.
    rewrite not_elem_of_union not_elem_of_singleton.
    intros [Hnhead Hndom].
    destruct (IH Hndom) as [Hnlist Hndom'].
    rewrite not_elem_of_cons.
    auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Helper lemmas for manipulating [WPTP]s. *)

(* [wp_wptp] established the correspondence between [EWP] and [WPTP] over a singleton. *)
Lemma wp_wptp `{!osirisGS Σ} ι m φ :
  ewp_def ⊤ m ⊥ (λ o, □ φ o) ⊣⊢ WPTP {[ι := m ]} {[ι := φ]}.
Proof.
  unfold WPTP.
  by rewrite big_sepM2_singleton.
Qed.

Lemma WPTP_dom `{!osirisGS Σ} π πp :
  WPTP π πp -∗ ⌜dom πp = dom π⌝.
Proof.
  iIntros "Hwps".
  iPoseProof (big_sepM2_dom with "Hwps") as "%Hdomeq".
  by iPureIntro.
Qed.

Lemma WPTP_dom_equiv `{!osirisGS Σ} π πp :
  WPTP π πp -∗ ⌜dom πp ≡ dom π⌝.
Proof.
  iIntros "Hwps".
  iPoseProof (big_sepM2_dom with "Hwps") as "%Hdomeq".
  iPureIntro; by rewrite Hdomeq.
Qed.

(* Isolate a specific thread in a [WPTP]. *)
Lemma WPTP_extract_wp `{!osirisGS Σ} π πp ι e :
  ⌜π !! ι = Some e⌝ -∗
  WPTP π πp -∗
  ∃ φ, ⌜πp !! ι = Some φ⌝ ∗
       ewp_def ⊤ e ⊥ (λ o, □ φ o) ∗ WPTP (delete ι π) (delete ι πp).
Proof.
  iIntros "%Hlookup Hwps".
  iPoseProof (WPTP_dom with "Hwps") as "%Hdomeq".
  assert (∃ φ, πp !! ι = Some φ) as (φ & Hlookup_p).
  { apply (elem_of_dom πp ι).
    rewrite Hdomeq. apply elem_of_dom. eexists; eassumption. }
  iPoseProof (big_sepM2_delete _ _ _ _ _ _ Hlookup Hlookup_p with "Hwps")
    as "(Hwp & Hwps)".
  iFrame.
  by iPureIntro.
Qed.

(* Reinsert a thread that was extracted back into a [WPTP]. *)
Lemma WPTP_insert_delete `{!osirisGS Σ} ι π1 πp m' φ :
  ⌜πp !! ι = Some φ⌝ -∗
  WPTP (delete ι π1) (delete ι πp) -∗
  ewp_def ⊤ m' ⊥ (λ o, □ φ o) -∗
  WPTP (<[ι:=m']> π1) πp.
Proof.
  iIntros "%Hlookup Hwps Hwp".
  replace πp with (<[ι:=φ]>πp) by apply (insert_id πp ι φ Hlookup).
  iApply big_sepM2_insert_delete.
  replace πp with (<[ι:=φ]>πp) at 2 by apply (insert_id πp ι φ Hlookup).
  iFrame.
Qed.

(* Reinsert a terminated thread's postcondition that was extracted
   back into a [WPTP]. *)
Lemma WPTP_insert_post_delete `{!osirisGS Σ} ι π1 πp φ o :
  ⌜πp !! ι = Some φ⌝ -∗
  ⌜π1 !! ι = Some (inject2 o)⌝ -∗
  WPTP (delete ι π1) (delete ι πp) -∗
  (|={⊤}=> □ φ o) -∗
  WPTP π1 πp.
Proof.
  iIntros "%Hlookup_p %Hlookup Hwps Hwp".
  replace πp with (<[ι:=φ]>πp) by apply (insert_id πp ι φ Hlookup_p).
  replace π1 with (<[ι:=inject2 o]>π1) by apply (insert_id π1 ι (inject2 o) Hlookup).
  iApply big_sepM2_insert_delete.
  replace πp with (<[ι:=φ]>πp) at 2 by apply (insert_id πp ι φ Hlookup_p).
  replace π1 with (<[ι:=inject2 o]>π1) at 2 by apply (insert_id π1 ι (inject2 o) Hlookup).
  iFrame.
  iApply fupd_ewp. iMod "Hwp". iModIntro.
  by iApply ewp_outcome2.
Qed.

(* Isolate a specific postcondition (i.e. terminated thread) in a [WPTP]. *)
Lemma WPTP_extract_outcome `{!osirisGS Σ} π πp ι o :
  ⌜π !! ι = Some (inject2 o)⌝ -∗
  WPTP π πp -∗
  ∃ φ, ⌜πp !! ι = Some φ⌝ ∗ WPTP (delete ι π) (delete ι πp) ∗ (|={⊤}=> □ φ o).
Proof.
  iIntros "%Hlookup Hwps".
  iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps") as "(%φ & %Hlookup_p & Hwp & Hwps)".
  iExists φ. iFrame "∗%".
  by iApply (ewp_outcome2_inv with "Hwp").
Qed.


Include ewp_rules_tactics.

Ltac invert_reducible :=
    lazymatch goal with
    | h: reducible ?e _ _ |- _ =>
        let hstep := fresh "Htstep" in
        let ι' := fresh "ι'" in
        let k := fresh "k" in
        let Heq_e := fresh "Heq_e" in
        let Hdom := fresh "Hdom" in
        let v1 := fresh "v" in
        let v2 := fresh "v" in
        let u := fresh "u" in
        let σ'_inner := fresh "σ_inner" in
        let e'_inner := fresh "e_inner" in
        let Hstep := fresh "Hstep" in
        let Y := fresh "Y" in
        let c := fresh "c" in
        let y := fresh "y" in
        apply invert_reducible in h as hstep;
        destruct hstep as
          [(ι' & k & Heq_e & Hdom)
          | [ (v1 & v2 & k & Heq_e) |
              [ (Y & c & y & k & Heq_e)
              | ([σ'_inner e'_inner] & Hstep) ]
          ] ];
        try subst e
    end.

Local Ltac iModFL_tac s := iMod s; iModIntro; iNext; iMod s; iModIntro.

Local Tactic Notation "iModFL" constr(s) "as" constr(s') :=
  iModFL_tac s; iDestruct s as s'.
Local Tactic Notation "iModFL" constr(s) := iModFL_tac s.

(* Compositional Lemmas for Adequacy *)
Section satisfiability_weakest_pre.
  Context `{!osirisGS Σ}.

  (* The trace plays no part here: not being stuck is a property of the
     store and the threadpool alone. We hand the weakest precondition the
     empty label, which is all a safety statement ever needs. *)

  Lemma EWP_not_stuck_post {A X} E (e : micro A X) σ κs πp Φ :
    state_interp (σ, κs, πp) ∗ ewp_def E e ⊥ Φ ={E}[∅]▷=∗
    ⌜not_stuck e σ (dom πp)⌝ ∗ (∀ o, ⌜e = inject2 o⌝ -∗ Φ o).
  Proof.
    iIntros "(Hsi & Hwp)". rewrite /not_stuck.
    ewp_unfold e.
    ewp_case e; simpl.
    - (* Case: [e] is an [outcome2]. *)
      ewp_mask_intro "Hmod". iNext. iMod "Hmod". iMod "Hwp". iModIntro.
      iSplitR.
      + (* Prove we are not stuck. *)
        iPureIntro; left; by destruct o.
      + (* Prove we satisfy the postcondition. *)
        iIntros (o' Heq).
        destruct o; destruct o'; unfold inject2 in Heq;
          inversion Heq; iApply "Hwp".
    - (* Case: [e] is a [perform]. *)
      iMod "Hwp" as "(% & [] & Hwp)".
    - (* Case: [e] takes a subjective_step. Being able to progress is exactly
         the first conjunct of the weakest precondition, so we read it out
         and never take the step. That is what lets a resolution, whose
         step carries a label we do not know here, go through like any
         other. This is Iris's [wp_not_stuck]. *)
      iAssert (|={E,∅}=> ⌜reducible e σ (dom πp)⌝)%I with "[Hsi Hwp]" as "Hcp".
      { spec_state. iModIntro. iPureIntro. exact Hstep. }
      iMod (fupd_plain_mask with "Hcp") as %Hprog.
      iApply step_fupd_intro; first set_solver.
      iNext. iSplitR; first (iPureIntro; right; left; exact Hprog).
      (* A computation that steps is not an outcome. *)
      iIntros (o Heq). rewrite Heq in Hhm. by destruct o.
    - (* Case: [e] is a join. *)
      spec_state_join.
      ewp_mask_intro "Hmod". iNext. iMod "Hmod". iModIntro.
      iSplitR.
      + (* Prove that we are not stuck. *)
        iPureIntro. by right; right.
      + (* Prove that if we are final, we satisfy the post (we are not final). *)
        iIntros (o HFalse). destruct o; discriminate HFalse.
  Qed.

  Inductive nsteps {A X} : nat → config A X → config A X → Prop :=
    nsteps_refl : ∀ ρ : config A X, nsteps 0 ρ ρ
  | nsteps_l :
    ∀ (n : nat) (ρ1 ρ2 ρ3 : config A X),
      step ρ1 ρ2 →
      nsteps n ρ2 ρ3 →
      nsteps (S n) ρ1 ρ3.

  (* The pool stores the predicate itself, so the [□ φ o] we hold is already
     the one the weakest precondition asks for: no agreement step is needed. *)
  Lemma ewp_join_inv {A X} φ σ κs πp ι' (k : _ → micro A X) Ψ Φ E o :
    ⌜πp !! ι' = Some φ⌝ -∗
    □ φ o -∗
    state_interp (σ, κs, πp) -∗
    ewp_def E (Stop CJoin ι' k) Ψ Φ -∗
    |={E}[∅]▷=> state_interp (σ, κs, πp) ∗ ewp_def E (k o) Ψ Φ.
  Proof.
    iIntros "%Hlookup Hφ Hsi Hwp".
    rewrite ewp_unfold /ewp_pre /=. spec_state_join.
    rewrite Hlookup.
    iMod "Hwp".
    iModIntro. iNext.
    iSpecialize ("Hwp" with "Hφ").
    ewp_mask_elim. iMod "Hwp" as "($ & $)". done.
  Qed.

  (* Relating a "real" threadpool step (from the definition of the semantics),
     to a "local" thread step (from the definition of our weakest pre). *)
  Lemma threadpool_subjective_step (σ1 σ2 : store) (π1 π2 : thpool) κ :
    (* If the threadpool can take an instrumented step *)
    proph_step (σ1, π1) κ (σ2, π2) →
    (* Then either that step was a join, which emits nothing *)
    (∃ ι ι' k m,
        π1 !! ι = Some (Stop CJoin ι' k) ∧
        attempt_join ι' π1 k = Some m ∧
        σ1 = σ2 ∧
        κ = [] ∧
          π2 = <[ι:=m]>π1)
    ∨
    (* Or that step can be emulated by a [subjective_step] with the same
       label, which is where a resolution's observation comes from. *)
    ∃ (ι : thread) (m m' : microvx) μ,
      π1 !! ι = Some m ∧
      π2 !! ι = Some m' ∧
      subjective_step (σ1, m, dom π1) κ (σ2, m', μ) ∧
      (* With different descriptions of [π2] depending on
         whether a new thread was forked or not. *)
      match μ with
      | None => π2 = <[ι:=m']>π1
      | Some (ι', mf) => <[ι:=m']> π1 !! ι' = None ∧ π2 = <[ι':=mf]>(<[ι:=m']>π1)
      end.
  Proof.
    intros Htpstep.
    inversion_clear Htpstep as [ ? ? Hpure | ]; [ inversion_clear Hpure | ].
    - (* BaseTP case: π !! ι = Some m, step (σ, m) (σ', m') *)
      right; rename H into Hlookup, H0 into Hstep; subst.
      eapply BaseS in Hstep as Htstep.
      exists ι, m, m', None.
      split; [exact Hlookup | split; [ apply lookup_insert_eq | split; [exact Htstep | reflexivity]]].
    - (* ForkTP case: π !! ι = Some (Stop CFork ...), π !! ι' = None *)
      right; rename H into Hlookup, H0 into Hfresh; subst.
      exists ι, (Stop CFork (v1, v2) k), (continue k (VThread ι')), (Some (ι', call v1 v2)).
      split; [exact Hlookup | ].
      split; [rewrite lookup_insert_ne; [apply lookup_insert_eq | ] | ].
      { intros Heq_ι. subst ι'. rewrite Hfresh in Hlookup. discriminate Hlookup. }
      split.
      + apply ForkS. apply (not_elem_of_dom π1). exact Hfresh.
      + split; [| reflexivity].
        rewrite lookup_insert_ne; [exact Hfresh | ].
        intros Heq_ι'. subst ι'. rewrite Hfresh in Hlookup. discriminate Hlookup.
    - (* JoinTP case: π !! ι = Some (Stop CJoin ...), attempt_join ... *)
      left; rename H into Hlookup, H0 into Hattempt; subst.
      exists ι, ι', k, m.
      split; [exact Hlookup | split; [exact Hattempt | done]].
    (* [ResolveTS] is [ResolveS] one level up: same outcome, so the same
       [resolve_obs] label and the same [try2] target. *)
    - right; rename H into Hlookup, H0 into Hstep; subst.
      eexists ι, _, (try2 b k), None.
      split; [exact Hlookup | split; [apply lookup_insert_eq | ]].
      split; [by eapply ResolveS | reflexivity].
  Qed.

  Lemma wptp_tstep (π1 : thpool) (πp : post_map Σ) σ1 σ2 m m' ι μ κ κs :
    ⌜π1 !! ι = Some m⌝ -∗
    ⌜subjective_step (σ1, m, dom πp) κ (σ2, m', μ)⌝ -∗
    (state_interp (σ1, κ ++ κs, πp) ∗ WPTP π1 πp) ={⊤}[∅]▷=∗
     match μ with
     | None => state_interp (σ2, κs, πp) ∗ WPTP (<[ι:=m']>π1) πp
     | Some (ι', mforked) => ∃ (φ : outcome2 val exn -d> iPropO Σ),
       state_interp (σ2, κs, <[ι':=φ]>πp) ∗ WPTP (<[ι':=mforked]> (<[ι:=m']>π1)) (<[ι':=φ]>πp)
     end.
  Proof.
    iIntros "%Hlookup %Hstep [Hsi Hwps]".
    iPoseProof (WPTP_dom_equiv with "Hwps") as "%Hdomeq".
    iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps")
      as "(%φ & %Hlookup_p & Hwp & Hwps)".
    iPoseProof (ewp_step with "Hsi Hwp") as ">Hwp". { apply Hstep. }
    iModFL "Hwp" as "[Hwp Hμ]".
    inversion Hstep; subst; iFrame;
      (* [BaseS] and the three [Resolve] rules all leave the threadpool
         with a single entry updated. *)
      try iApply (WPTP_insert_delete $! Hlookup_p with "Hwps [$]").
    - (* Case: subjective_step is a [ForkS]. *)
      iDestruct "Hμ" as "(%φ' & Hsi & Hcall)".
      iFrame.
      iPoseProof (WPTP_insert_delete $! Hlookup_p with "Hwps [$]") as "Hwps".
      iApply big_sepM2_insert.
      { match goal with Hfresh : _ ∉ _ |- _ =>
          setoid_rewrite Hdomeq in Hfresh; apply not_elem_of_dom in Hfresh;
          rewrite lookup_insert_ne; try assumption;
          apply (lookup_ne π1); by rewrite Hfresh Hlookup
        end. }
      { apply not_elem_of_dom; assumption. }
      iFrame.
  Qed.

  Ltac invert_proph_step :=
    lazymatch goal with
    | h: proph_step (?σ1, ?π1) ?κ (?σ2, ?π2) |- _ =>
        let Hsteps := fresh "Hsteps" in
        (have Hsteps := threadpool_subjective_step σ1 σ2 π1 π2 κ h);
        destruct Hsteps as
          [ (ι & ι' & k & e & Hlookup & Hattempt & Heq_σ & Heq_κ & Heq_π2)
          | (ι & e & e' & μ & Hlookup & Hlookup' & Htstep & Hμ)
          ];
        subst;
        last first
    end.

  Lemma wptp_step (π1 π2 : thpool) (πp : post_map Σ) σ1 σ2 κ κs :
    ⌜proph_step (σ1, π1) κ (σ2, π2)⌝ -∗
    (state_interp (σ1, κ ++ κs, πp) ∗ WPTP π1 πp) ={⊤}[∅]▷=∗
    (∃ (l : list (thread * (outcome2 val exn -d> iPropO Σ))),
        ⌜∀ ι', ι' ∈ fst <$> l → ι' ∉ dom (πp)⌝ ∗
        state_interp (σ2, κs, insert_list l πp) ∗ WPTP π2 (insert_list l πp)).
  Proof.
    iIntros "%Hstep [Hsi Hwps]".
    iPoseProof (WPTP_dom with "Hwps") as "%Hdomeq".
    iCombine "Hsi Hwps" as "Hwps".
    invert_proph_step.
    - (* Case: [proph_step] is immitated by a [subjective_step]. *)
      rewrite <- Hdomeq in Htstep.
      iPoseProof (wptp_tstep $! Hlookup Htstep with "Hwps") as "Hwps". (* Use [wptp_tstep]. *)
      iModFL "Hwps".
      destruct μ as [[ι' mforked] | ]; last first.
      + (* Subcase: the step did not fork any new threads. *)
        subst π2.
        iDestruct "Hwps" as "(Hsi & Hwps)".
        iExists []. iFrame.
        iPureIntro. intros ι' Hin. by apply not_elem_of_nil in Hin.
      + (* Subcase: the step results in a forked thread. *)
        destruct Hμ as [Hfresh Heq_π2]. subst π2.
        iDestruct "Hwps" as "(%φ' & Hsi & Hwps)".
        iExists [(ι', φ')].
        iFrame.
        iPureIntro. intros ι'' Hin. apply list_elem_of_singleton in Hin as ->.
        rewrite Hdomeq. apply not_elem_of_dom.
        assert (ι ≠ ι') as Hneq_ι.
        { intros Heq_ι. subst ι'. rewrite lookup_insert_eq in Hfresh. discriminate Hfresh. }
        rewrite lookup_insert_ne in Hfresh; last exact Hneq_ι.
        exact Hfresh.
    - (* Case: [proph_step] is a join. *)
      iDestruct "Hwps" as "(Hsi & Hwps)".
      iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps") as "(%φ & %Hlookup_p & Hwp & Hwps)".
      case (πp !! ι') eqn:Hlookup_p'.
      + (* Case: the join was successful. *)
        rename o into φ'.
        assert (∃ o, π1 !! ι' = Some (inject2 o) ∧ e = k o) as (o & Hlookup' & Heq_e).
        { unfold attempt_join in Hattempt.
          assert (is_Some (π1 !! ι')) as [e' Hlookup'].
          { apply elem_of_dom. setoid_rewrite <- Hdomeq.
            apply (elem_of_dom πp ι'). exists φ'. exact Hlookup_p'. }
          rewrite Hlookup' in Hattempt.
          destruct e'; inversion Hattempt; try discriminate; subst; rewrite Hlookup'.
          - exists (O2Ret a). split; reflexivity.
          - exists (O2Throw e0). split; reflexivity. }
        subst e.
        assert (ι ≠ ι') as Hneq.
        { intros Heq_ι. subst ι'. rewrite Hlookup' in Hlookup.
          inversion Hlookup as [Heq_stop]. destruct o; discriminate Heq_stop. }
        pose proof (lookup_delete_ne_inv _ _ _ _ Hneq Hlookup') as Hlookup_del.
        iPoseProof (WPTP_extract_outcome (delete ι π1) (delete ι πp) ι' with "[//] Hwps")
          as "(%φ'' & %Hlookup_p'' & Hwps & Ho)".
        pose proof (lookup_delete_ne_inv _ _ _ _ Hneq Hlookup_p') as Hlookup_del_p.
        rewrite Hlookup_del_p in Hlookup_p''. inversion Hlookup_p''; subst φ''.
        iMod "Ho" as "#Ho".
        iPoseProof (ewp_join_inv $! Hlookup_p' with "Ho Hsi Hwp") as "Hwp".
        iModFL "Hwp" as "(Hsi & Hwp)".
        iExists []. iFrame "Hsi".
        iPoseProof (WPTP_insert_post_delete $! Hlookup_del_p Hlookup_del with "Hwps Ho") as "Hwps".
        iPoseProof (WPTP_insert_delete $! Hlookup_p with "Hwps [$]") as "$".
        iPureIntro. intros ι'' Hin. by apply not_elem_of_nil in Hin.
      + ewp_unfold (Stop CJoin ι' k). spec_state_join.
        iMod "Hwp".
        setoid_rewrite Hlookup_p'.
        by repeat iMod "Hwp".
  Qed.

  Lemma wptp_steps k π1 π2 σ1 σ2 πp κs κs' :
    ⌜proph_steps k(σ1, π1) κs (σ2, π2)⌝ -∗
    state_interp (σ1, κs ++ κs', πp) ∗ WPTP π1 πp ={⊤}[∅]▷=∗^k
    (∃ (l : list (thread * (outcome2 val exn -d> iPropO Σ))),
        ⌜∀ ι', ι' ∈ fst <$> l → ι' ∉ dom (πp)⌝ ∗
        state_interp (σ2, κs', insert_list l πp) ∗ WPTP π2 (insert_list l πp)).
  Proof.
    induction k as [|k IH] in  πp, π1, σ1, κs |-*; iIntros "%Hsteps Hwps".
    - inversion_clear Hsteps. simpl.
      iExists []. iFrame.
      iPureIntro; simpl; intros ? HF.
      by apply not_elem_of_nil in HF.
    - inversion_clear Hsteps as [| ? ? [σ1' π1'] ? ? ? Hstep1 Hsteps1].
      simpl.
      rewrite -assoc_L.
      iPoseProof (wptp_step $! Hstep1 with "Hwps") as "Hwps".
      iModFL "Hwps" as "(%l & %Hl & Hwps)".
      iPoseProof (IH $! Hsteps1 with "Hwps") as "Hwps".
      iApply (step_fupdN_wand with "Hwps").
      iIntros "(%l' & %Hl' & Hwps)".
      iExists (l' ++ l).
      rewrite insert_list_app.
      iFrame.
      iPureIntro.
      intros ι' Hin.
      rewrite fmap_app in Hin; apply elem_of_app in Hin.
      destruct Hin.
      + specialize (Hl' ι' H).
        by apply not_elem_of_insert_list in Hl' as [_ Hndom].
      + apply Hl, H.
  Qed.

  (* composing the adequacy lemmas *)
  Lemma wptp_adequacy k σ1 σ2 π2 ι e κs Φ :
    ⌜proph_steps k(σ1, {[ι:=e]}) κs (σ2, π2)⌝ -∗
    (state_interp (σ1, κs, {[ι := (λ o, ⌜Φ o⌝)%I]}) ∗
     ewp_def ⊤ e ⊥ (λ o, ⌜Φ o⌝)) ={⊤}[∅]▷=∗^k
    (∀ ι' e, ⌜π2 !! ι' = Some e⌝ ={⊤}[∅]▷=∗
      ⌜not_stuck e σ2 (dom π2)⌝ ∗
      (∀ o, ⌜π2 !! ι = Some (inject2 o)⌝ -∗ |={⊤}=> □ ⌜Φ o⌝)).
  Proof.
    iIntros "%Hsteps (Hsi & Hwp)".
    iPoseProof (ewp_wand with "Hwp []") as "Hwp".
    { iIntros (o) "%Ho". instantiate (1:=λ o, (□ ⌜Φ o⌝)%I).
      by iModIntro. }
    iCombine "Hsi Hwp" as "Hwps".
    rewrite wp_wptp.
    instantiate (1 := ι).
    remember {[ι := (λ o, ⌜Φ o⌝)%I]} as πp.
    rewrite -(right_id_L [] (++) κs).
    iPoseProof (wptp_steps $! Hsteps with "Hwps") as "Hwps".
    iApply (step_fupdN_wand with "Hwps").
    iIntros "(%l & %Hl & Hsi & Hwps)".
    iPoseProof (WPTP_dom with "Hwps") as "%Hdomeq".
    iIntros (ι' e' Hlookup).
    iPoseProof (WPTP_extract_wp $! Hlookup with "Hwps") as "(%φ' & %Hlookup_p & Hwp & Hwps)".
    iCombine "Hsi Hwp" as "Hwp".
    iPoseProof (EWP_not_stuck_post with "Hwp") as "Hwp".
    rewrite Hdomeq.
    iModFL "Hwp" as "($ & Hpost)".
    assert (insert_list l πp !! ι = Some (λ o, ⌜Φ o⌝)%I) as Hlookup_orig.
    { rewrite insert_list_lookup_not_in.
      - by rewrite Heqπp lookup_singleton_eq.
      - intros Hin%Hl. rewrite Heqπp dom_singleton in Hin.
        apply Hin. by apply elem_of_singleton. }
    case (decide (ι' = ι)) as [Heq_ι | Hneq].
    - subst ι'. iIntros (o Hlookup').
      rewrite Hlookup_orig in Hlookup_p.
      rewrite Hlookup' in Hlookup.
      inversion Hlookup_p; subst φ'.
      inversion Hlookup; subst e'.
      by iApply ("Hpost" $! o eq_refl).
    - iIntros (o Hlookup_og).
      pose proof (lookup_delete_ne_inv _ _ _ _ Hneq Hlookup_og) as Hlookup_del_π2.
      iPoseProof (WPTP_extract_outcome (delete ι' π2) (delete ι' (insert_list l πp)) ι with "[//] Hwps")
        as "(%φ'' & %Hlookup_p' & _ & HΦ)".
      rewrite lookup_delete_ne in Hlookup_p'; last exact Hneq.
      rewrite Hlookup_orig in Hlookup_p'. inversion Hlookup_p'; subst φ''.
      done.
  Qed.

  Lemma ewp_adequacy m F n ι e σ1 σ2 π2 k κs Φ :
    (* if we can prove satisfiable of a weakest pre and the state interpretation *)
    SAT m F [view ⊤; supply n]
      (state_interp (σ1, κs, {[ι := (λ o, ⌜Φ o⌝)%I]}) ∗
       ewp_def ⊤ e ⊥ (λ o, ⌜Φ o⌝)%I) →
    (* and we take a k-step execution to [e'] and some forked of threads *)
    proph_steps k(σ1, {[ι := e]}) κs (σ2, π2) →
    (* then no thread is stuck *)
    (∀ ι m, π2 !! ι = Some m → not_stuck m σ2 (dom π2)) ∧
    (∀ o, π2 !! ι = Some (inject2 o) → Φ o).
  Proof.
    intros Hsat Hsteps.
    eapply SAT_mono in Hsat; last iApply (wptp_adequacy k σ1 σ2 π2 _ _ κs $! Hsteps).
    apply SAT_elim_iterated in Hsat; last first.
    { intros P HsatP; by eapply SAT_fupd, SAT_later, SAT_fupd. }
    split.
    - (* Prove that no thread is stuck. *)
      intros ι' e' Hlookup.
      eapply SAT_mono in Hsat; last first. (* Instantiate inside SAT. *)
      { iIntros "Hx". iSpecialize ("Hx" $! ι' e' Hlookup). iExact "Hx". }
      apply SAT_fupd, SAT_later, SAT_fupd in Hsat.
      eapply SAT_mono in Hsat; last first. (* Symmetry inside SAT. *)
      { iIntros "[Hns Ho]". iCombine "Ho Hns" as "Hx". iExact "Hx". }
      rewrite -SAT_frame_cons in Hsat.
      by apply SAT_elim in Hsat.
    - (* Prove that if the initial thread has terminated,
         then the postcondition holds. *)
      intros o Hlookup.
      eapply SAT_mono in Hsat; last first. (* Instantiate inside SAT. *)
      { iIntros "Hx". iSpecialize ("Hx" $! ι (inject2 o) Hlookup). iExact "Hx". }
      apply SAT_fupd, SAT_later, SAT_fupd in Hsat.
      rewrite -SAT_frame_cons in Hsat.
      eapply SAT_mono in Hsat; last first.
      { iIntros "HΦ". iSpecialize ("HΦ" $! o Hlookup). iExact "HΦ". }
      apply SAT_fupd, SAT_pers in Hsat.
      apply SAT_elim in Hsat.
      by apply Hsat.
  Qed.

End satisfiability_weakest_pre.


(* Lemma for handling the allocation of invariants and later credits. *)
(* To use it, you should:
    - pick a type X that carries all of the global ghost names for your language (e.g., [heapGS] for HeapLang)
    - pick a function [I] that takes the ghost names and produces an Iris instance
    - prove that you can allocate the initial state interpretation for some [x: X]
    - prove a weakest precondition for all choices of [x: X]

  Then you obtain the result of [wp_adequacy] for your choice of [X] and [I]. *)
Local Existing Instance invGS_wsat.
Lemma SAT_ewp_adequacy `{invGpreS Σ} (X: Type) (I: X → osirisGS Σ) σ1 σ2 π2 (e : micro val exn) ι n k κs P Φ :
  (* allocate the initial state interpretation, for the trace the execution
     we are about to consider will produce *)
  (∀ (iv: invGS_gen HasNoLc Σ) (F: iProp Σ), SAT Alloc F [view ⊤; supply 0] True →
   ∃ (x: X),
    let i: osirisGS Σ := I x in
    let inv: invGS_gen HasNoLc Σ := osiris_invGS Σ in (* we ensure that all inferences of [invGS] point to this instance *)
    SAT Alloc F [view ⊤; supply n] (state_interp (σ1, κs, ∅) ∗ P x)) →
  (* prove the weakest precondition for all choices of [X] *)
  (∀ x, let i: osirisGS Σ := I x in P x ⊢ ewp_def ⊤ e ⊥ (λ o, ⌜Φ o⌝)) →
  (* then any k-step execution is safe: *)
  proph_steps k(σ1, {[ι := e]}) κs (σ2, π2) →
  (∀ ι m, π2 !! ι = Some m → not_stuck m σ2 (dom π2)) ∧
  (∀ o, π2 !! ι = Some (inject2 o) → Φ o).
Proof.
  intros Halloc Hwp Hsteps.
  pose proof (SAT_intro (Σ := Σ)) as Hsat.
  eapply SAT_alloc_fancy_updates in Hsat as [Hi Hsat].
  eapply (Halloc Hi True%I) in Hsat as (x & Hsat); eauto; simpl in *.
  eapply SAT_mono in Hsat; last first.
  { iIntros "((Hsi & Hpi & Hti) & HP)". iPoseProof (Hwp x with "HP") as "Hwp".
    iCombine "Hsi Hpi Hti Hwp" as "Hx". iExact "Hx". }
  eapply (@ewp_adequacy Σ (I x)), Hsteps.
  apply SAT_bupd.
  eapply SAT_mono, Hsat.
  { iIntros "(Hsi & Hpi & Hti & Hwp)".
    iMod (thread_alloc ∅ ι (λ o, ⌜Φ o⌝)%I with "Hti") as "(Hti & _)";
      first apply (lookup_empty (M := gmap thread) ι).
    rewrite insert_empty.
    iModIntro. iFrame. }
Qed.

(* The prophecy map starts empty: no identifier has been allocated yet, so
   no resolution in [κs] can concern one, and [proph_map_init] is happy
   with any trace. Freshness for the store then keeps the two in step, as
   [osiris_proph_interp] records. *)

Lemma osiris_initial_allocation `{!osirisGpreS Σ} (ι : thread) σ κs (_ : invGS_gen HasNoLc Σ) (F : iProp Σ) (P: outcome2 val exn → Prop) :
  SAT Alloc F [view ⊤; supply 0] True →
  ∃ (h: osirisGS Σ),
    let inv: invGS_gen HasNoLc Σ := osiris_invGS Σ in
    SAT Alloc F [view ⊤; supply 0] (state_interp (σ, κs, ∅)).
Proof.
  intros Hsat.
  eapply SAT_frame_resource with (R := view _) in Hsat; last apply _.
  eapply SAT_frame_resource with (R := supply _) in Hsat; last apply _.
  eapply (SAT_gen_heap_init σ) in Hsat as [Hgen Hsat].
  (* The thread postconditions and the block map are authoritative maps of
     agreements, allocated with the generic resource allocation. *)
  assert (Hva : ✓ (● (∅ : thread_postUR Σ))).
  { apply auth_auth_valid. exact (ucmra_unit_valid (A := thread_postUR Σ)). }
  eapply (SAT_alloc_res _ _ _ _ Hva) in Hsat as [γpost Hsat].
  eapply (SAT_proph_map_init κs ∅) in Hsat as [Hproph Hsat].
  assert (Hvb : ✓ (● (∅ : block_mapUR))).
  { apply auth_auth_valid. exact (ucmra_unit_valid (A := block_mapUR)). }
  eapply (SAT_alloc_res _ _ _ _ Hvb) in Hsat as [γ Hsat].
  do 2 apply SAT_unframe_resource in Hsat.
  pose (hg := (@OsirisGS Σ _ _ Hgen γpost γ Hproph)).
  exists hg.
  eapply SAT_mono; last apply Hsat.
  iIntros "(Harri & Hproph & Hpost & Hgen & _ & _)".
  iFrame "Hgen".
  iSplitL "Harri".
  { iExists ∅. rewrite block_map_auth_empty. iFrame "Harri". iPureIntro.
    intros a ls Hlookup. rewrite lookup_empty in Hlookup. discriminate. }
  iSplitL "Hproph".
  { iExists ∅. iFrame "Hproph". iPureIntro. set_solver. }
  rewrite /osiris_thread_interp thread_post_auth_empty. iFrame "Hpost".
Qed.

(* -------------------------------------------------------------------------- *)
(** * Adequacy. *)

Section adequacy.

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP] for computations under open gFunctors [Σ]. *)

  Lemma osiris_adequacy Σ `{!osirisGpreS Σ} (e : micro val exn) ι σ1 π2 σ2 k κs Φ :
    (* If we can show [EWP e1 {{ True }}] with the ghost state provided by [Σ]. *)
    (∀ `{!osirisGS Σ}, ⊢ ewp_def ⊤ e ⊥ (λ o, ⌜Φ o⌝)) →
    (* then any k-step execution, with the trace [κs] it produces, is safe: *)
    proph_steps k(σ1, {[ι := e]}) κs (σ2, π2) →
    (∀ ι m, π2 !! ι = Some m → not_stuck m σ2 (dom π2)) ∧
    (∀ o, π2 !! ι = Some (inject2 o) → Φ o).
  Proof.
    intros Hwp.
    eapply SAT_ewp_adequacy with (X := osirisGS Σ) (P := λ _, bi_pure True).
    - intros iv F Hsat_init.
      have [h Hsat] := (@osiris_initial_allocation Σ osirisGpreS0 ι σ1 κs iv F Φ Hsat_init).
      exists h.
      eapply SAT_mono, Hsat.
      apply bi.sep_True_2.
    - apply Hwp.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP] for a closed list of gFunctors. *)

  (* Example of an adequacy statement instantiated with a specific set of [gFunctors]. *)

  Definition osiris_adequacy_closed (e : micro val exn) ι σ1 π2 σ2 k κs Φ :
    (∀ `{!osirisGS osirisΣ}, ⊢ ewp_def ⊤ e ⊥ (λ o, ⌜Φ o⌝)) →
    proph_steps k(σ1, {[ι :=e]}) κs (σ2, π2) →
    (∀ ι m, π2 !! ι = Some m → not_stuck m σ2 (dom π2)) ∧
    (∀ o, π2 !! ι = Some (inject2 o) → Φ o).
  Proof.
    intros Hwp. eapply osiris_adequacy, Hwp. apply _.
  Qed.

End adequacy.
