From Stdlib Require Import Program.Equality.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap proph_map.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
Require Import subjective_step ewp tactics.

Require Import basic_rules.

Import ewp_rules_tactics.

(* -------------------------------------------------------------------------- *)
(** * Reasoning rules for prophecy variables. *)

(* A prophecy variable is a name to which the logic can attach a claim
   about the future of the execution. [proph p pvs] says that the
   remaining resolutions of [p], in order, will be [pvs]. That is a claim
   about what has not happened yet, and the only thing that makes it
   sound is the observation trace threaded through [state_interp]: the
   step relation records every resolution, and adequacy quantifies over an
   execution together with the trace it produces. See
   [osiris_proph_interp] in ewp.v.

   The two rules below are the whole interface. [ewp_new_proph] mints a
   prediction; [ewp_resolve] cashes one in. *)

Section proph.

  Context `{!osirisGS Σ}.
  Context {A X : Type}.

  Implicit Types E : coPset.
  Implicit Types Ψ : iEff Σ.

  (* ------------------------------------------------------------------------ *)
  (** ** Allocation. *)

  Lemma ewp_new_proph `{Observe A V} `{HobsB : Observe B X} E Ψ (ζ : B → iProp Σ) (Φ : A → _) u
    (k : outcome2 loc exn → micro V X) :
    ▷ (∀ (p : loc) (pvs : list (val * val)),
         proph p pvs -∗
         EWP (continue k p) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }})
    ⊢ EWP (Stop CNewProph u k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    ewp_unfold_head.
    intro_state.
    ewp_mask_intro "Hmod".
    construct_wp_nonret.
    destruct_subjective_step.
    (* [StepNewProph] picked a location [p] fresh for the store. *)
    iDestruct "Hpi" as (ps Hps) "Hpm".
    iMod (proph_map_new_proph p ps with "Hpm") as "[Hpm Hp]".
    { (* [p] is fresh for the store, hence for [ps]. *)
      intros Hin. apply Hps in Hin. apply not_elem_of_dom in H0. done. }
    iMod (osiris_state_alloc σ p (Val VUnit) H0 with "Hsi")
      as "(Hsi & _ & _ & _)".
    iIntros "!> !>".
    iSpecialize ("H" with "Hp").
    ewp_mask_elim. iFrame "H Hsi Hti".
    (* The allocated identifier joins the set, and the store grew to match. *)
    iExists ({[p]} ∪ ps). iFrame "Hpm". iPureIntro.
    rewrite dom_insert. set_solver.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** ** Resolution. *)

  (* [Stop (CResolve c) (x, p, v) k] performs the system call [c x] and
     resolves [p] with the pair of its result and [v], in one step. This is
     HeapLang's [wp_resolve] in Osiris's terms.

     The first premise is atomicity, and it is not a technicality: a call
     that steps to a whole computation rather than to a result has no
     result for the resolution to record. It holds for exactly the four
     operations [eval] admits under a resolution: load, exchange,
     compare-and-set, fetch-and-add. *)

  Definition call_is_atomic {Y} (c : code Y val exn) (x : Y) : Prop :=
    (match c with CPerf | CResolve _ => False | _ => True end
       ∧ ¬ is_concurrent_code c) ∧
    (∀ σ σ' m', step (σ, stop c x) (σ', m') →
      (∃ w, m' = Ret w) ∨ (∃ e, m' = Throw e) ∨ m' = Crash).

  Lemma ewp_resolve `{Observe A V} `{HobsB : Observe B X} E Ψ (ζ : B → iProp Σ) (Φ : A → _) {Y}
    (c : code Y val exn) x (p : loc) (v : val)
    (pvs : list (val * val)) (k : outcome2 val exn → micro V X) :
    call_is_atomic c x →
    proph p pvs -∗
    EWP (stop c x) @ E <| Ψ |>
      ⟨⟨ e, EWP (discontinue k e) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} ⟩⟩
      {{ w, ∀ pvs', ⌜pvs = (w, v) :: pvs'⌝ -∗ proph p pvs' -∗
              EWP (continue k w) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} }}
    -∗ EWP (Stop (CResolve c) (x, p, v) k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros ([[Hprog Hconc] Hat]) "Hp Hwp".
    assert (is_ewp_case (stop c x) = WPStep) as Hcase.
    { destruct c; simpl; try done; try (exfalso; by apply Hconc). }
    iEval (rewrite /impure (ewp_unfold (stop c x)) /ewp_pre Hcase) in "Hwp".
    ewp_unfold_head.
    iIntros (σ κ κs π) "Hsi".
    (* Progress comes from the code alone, so it is available before we
       know anything about the trace. *)
    assert (can_step (σ, stop c x)) as Hcs by (by apply can_step_stop).
    (* The label decides which of the three [Resolve] rules can have
       fired: only the successful one emits, so an empty label means the
       call threw or crashed. *)
    destruct κ as [| [p' [w' v']] κ''].
    - (* No observation: the call is run against the trace unchanged, and
         the prophecy is left untouched. *)
      iMod ("Hwp" $! σ [] κs π with "Hsi") as "[_ Hwp]".
      iModIntro. iSplit.
      { iPureIntro. eapply can_progress_resolve; [ exact Hcs | apply Hat ]. }
      iIntros (σ' m' μ) "%Hstep".
      (* [dependent destruction] wants the payload to be a variable. *)
      remember (x, p, v) as y eqn:Hy.
      dependent destruction Hstep.
      { exfalso. eapply (no_step_Resolve _ c _ k); eassumption. }
      destruct_is_result [w | e]; simpl in *; simplify_eq.
      + (* the call threw *)
        iMod ("Hwp" $! σ' (throw e) None with "[%]") as "Hwp";
          first by apply BaseS.
        iModIntro. iNext. iMod "Hwp" as "[Hwp $]".
        iApply fupd_ewp.
        iEval (rewrite (ewp_unfold (throw e)) /ewp_pre /=) in "Hwp".
        iMod "Hwp" as "(%b & -> & Hwp)". iModIntro. iExact "Hwp".
      + (* the call crashed *)
        iMod ("Hwp" $! σ' Crash None with "[%]") as "Hwp";
          first by apply BaseS.
        iModIntro. iNext. iMod "Hwp" as "[Hwp $]".
        ewp_unfold (@Crash val exn). by iMod "Hwp".
    - iMod ("Hwp" $! σ [] (((p', (w', v')) :: κ'') ++ κs) π with "[Hsi]")
        as "[_ Hwp]".
      { by iFrame "Hsi". }
      iModIntro. iSplit.
      { iPureIntro. eapply can_progress_resolve; [ exact Hcs | apply Hat ]. }
      iIntros (σ' m' μ) "%Hstep".
      remember (x, p, v) as y eqn:Hy.
      dependent destruction Hstep.
      destruct_is_result [w | e]; simpl in *; simplify_eq.
      iMod ("Hwp" $! σ' (ret w') None with "[%]") as "Hwp";
        first by apply BaseS.
      iModIntro. iNext. iMod "Hwp" as "[Hwp ($ & Hpi & $)]".
      iDestruct "Hpi" as (ps Hps) "Hpm".
      iMod (proph_map_resolve_proph p' (w', v') κs ps pvs with "[$Hpm $Hp]")
        as (pvs') "(%Heq & Hpm & Hp)".
      iSplitR "Hpm"; last (iExists ps; by iFrame "Hpm").
      iApply fupd_ewp.
      iEval (rewrite (ewp_unfold (ret w')) /ewp_pre /=) in "Hwp".
      iMod "Hwp". iModIntro.
      iDestruct "Hwp" as (a) "[%Ha Hwp]". simpl in Ha. subst w'.
      iModIntro. by iApply ("Hwp" with "[//] Hp").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** ** Resolution one step late. *)

  (* [CReturn] is the trivial call that returns its argument, which is what
     [eval] resolves on when the annotated expression is not a single
     operation. Atomic in the sense above, trivially: its only step
     returns. *)

  Lemma call_is_atomic_return (w : val) : call_is_atomic CReturn w.
  Proof.
    split; first (split; [ done | by intros [] ]).
    intros σ σ' m' Hstep. dependent destruction Hstep. eauto.
  Qed.

  (* The four operations that [eval] resolves at their own step. Each takes
     exactly one step, and that step lands on an outcome, which is what
     makes the fused form available for them and no one else. *)

  Local Ltac solve_call_is_atomic :=
    split; first (split; [ done | by intros [] ]);
    intros σ σ' m' Hstep; dependent destruction Hstep;
    rewrite /step_load_2 /step_exchange_2 /step_cas_2 /step_faa_2;
    repeat case_match; eauto.

  Lemma call_is_atomic_load x : call_is_atomic CLoad x.
  Proof. solve_call_is_atomic. Qed.

  Lemma call_is_atomic_exchange x : call_is_atomic CExchange x.
  Proof. solve_call_is_atomic. Qed.

  Lemma call_is_atomic_cas x : call_is_atomic CCAS x.
  Proof. solve_call_is_atomic. Qed.

  Lemma call_is_atomic_faa x : call_is_atomic CFAA x.
  Proof. solve_call_is_atomic. Qed.

  Global Instance resolve_atomic {Y} (c : code Y val exn) x p v :
    Atomic (resolve c x p v).
  Proof.
    intros σ π σ' m' μ κ Hstep.
    rewrite /resolve in Hstep.
    remember (x, p, v) as y eqn:Hy.
    dependent destruction Hstep.
    - exfalso. eapply (no_step_Resolve _ c _ inject2); eassumption.
    - destruct_is_result [w | e].
      + by eapply subjective_step.is_ret.
      + by eapply subjective_step.is_throw.
      + by eapply subjective_step.is_crash.
  Qed.

  (* The rule a client uses for a non-atomic resolution. There is no
     exception case: [CReturn] cannot throw, and no state to reason about:
     the step exists only to carry the observation. So the whole content of
     the rule is that the prediction's head is the value that was
     computed. *)

  Lemma ewp_resolve_return `{Observe A V} `{HobsB : Observe B X} E Ψ (ζ : B → iProp Σ) (Φ : A → _)
    (w : val) (p : loc)
    (v : val) (pvs : list (val * val)) (k : outcome2 val exn → micro V X) :
    proph p pvs -∗
    (∀ pvs', ⌜pvs = (w, v) :: pvs'⌝ -∗ proph p pvs' -∗
       EWP (continue k w) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }})
    -∗ EWP (Stop (CResolve CReturn) (w, p, v) k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hp H".
    iApply (ewp_resolve with "Hp"); first apply call_is_atomic_return.
    (* All that is left is the weakest precondition of [stop CReturn w],
       which returns [w] in one step. *)
    ewp_unfold_head.
    intro_state.
    ewp_mask_intro "Hmod".
    construct_wp_nonret.
    destruct_subjective_step.
    ewp_mask_elim. iFrame.
    ewp_unfold_head. iModIntro. iExists w. by iSplit.
  Qed.

End proph.
