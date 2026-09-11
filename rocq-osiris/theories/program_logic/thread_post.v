(* A thread-indexed map of postconditions.

   This is what [osiris_thread_interp] is built from: a single ghost map whose
   values are the postconditions themselves, so a thread id indexes its
   predicate directly. There is no gname naming a saved predicate in between.
   The construction mirrors Iris's own [wsat], which stores invariants as
   [gmap_view positive (agree (later (iProp Σ)))].

   The [▶] under the [agree] is what keeps the domain equation contractive.
   It is also the one cost of the design: reading a thread's predicate back
   out of the map only ever gives agreement up to a [▷], so a client holding
   [valid_thread ι P] learns [▷ (Q o ≡ P o)] rather than a definitional
   equality. Every rule that needs it is already under a [▷]. *)

From iris.algebra Require Import gmap_view agree dfrac.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import thread_ids syntax locations encode.
From osiris.semantics Require Import semantics.

Definition postO (Σ : gFunctors) : ofe := outcome2 val exn -d> iPropO Σ.

Class threadPostG (Σ : gFunctors) := {
  #[global] thread_post_inG ::
    inG Σ (gmap_viewR thread (agreeR (outcome2 val exn -d> laterO (iPropO Σ))));
}.

Definition threadPostΣ : gFunctors :=
  #[ GFunctor (gmap_viewRF thread (agreeRF (outcome2 val exn -d> ▶ ∙))) ].

Global Instance subG_threadPostΣ {Σ} : subG threadPostΣ Σ → threadPostG Σ.
Proof. solve_inG. Qed.

Section thread_post.
  Context `{!threadPostG Σ}.

  (* One step of unfolding, exactly as [wsat]'s [invariant_unfold]: the [▶] is
     what keeps the domain equation contractive. *)
  Definition post_unfold (P : postO Σ) : outcome2 val exn -d> laterO (iPropO Σ) :=
    λ o, Next (P o).

  Global Instance post_unfold_contractive : Contractive post_unfold.
  Proof.
    intros n P Q HPQ o. apply Next_contractive.
    dist_later_intro as m Hm. exact (HPQ o).
  Qed.

  Definition thread_post_auth (γ : gname) (π : gmap thread (postO Σ)) : iProp Σ :=
    own γ (gmap_view_auth (DfracOwn 1) ((λ P, to_agree (post_unfold P)) <$> π)).

  Definition thread_post_frag (γ : gname) (ι : thread) (P : postO Σ) : iProp Σ :=
    own γ (gmap_view_frag ι DfracDiscarded (to_agree (post_unfold P))).

  Global Instance thread_post_frag_persistent γ ι P :
    Persistent (thread_post_frag γ ι P).
  Proof. apply _. Qed.

  Global Instance thread_post_frag_contractive γ ι : Contractive (thread_post_frag γ ι).
  Proof. solve_contractive. Qed.

  (* The shape the adequacy proof allocates the map in. *)
  Lemma thread_post_auth_empty γ :
    thread_post_auth γ ∅ ⊣⊢ own γ (gmap_view_auth (DfracOwn 1) ∅).
  Proof. by rewrite /thread_post_auth fmap_empty. Qed.

  Lemma thread_post_init :
    ⊢ |==> ∃ γ, thread_post_auth γ ∅.
  Proof.
    iMod (own_alloc (gmap_view_auth (DfracOwn 1) ∅)) as (γ) "H";
      first by apply gmap_view_auth_valid.
    iExists γ. by rewrite /thread_post_auth fmap_empty.
  Qed.

  (* Looking a thread up in the authoritative map recovers its postcondition,
     up to a step-indexed (hence [▷]) equality. *)
  Lemma thread_post_lookup γ π ι P :
    thread_post_auth γ π -∗ thread_post_frag γ ι P -∗
    ∃ Q, ⌜π !! ι = Some Q⌝ ∗ ▷ (∀ o, Q o ≡ P o).
  Proof.
    rewrite /thread_post_auth /thread_post_frag.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as "Hv".
    rewrite gmap_view_both_validI_total.
    iDestruct "Hv" as (Q') "(_ & _ & HQ' & _ & Hincl)".
    rewrite lookup_fmap.
    destruct (π !! ι) as [Q|] eqn:Hπ; simpl; last first.
    { iDestruct "HQ'" as %?. done. }
    iDestruct "HQ'" as %[= <-].
    iExists Q. iSplit; first done.
    rewrite to_agree_includedI discrete_fun_equivI.
    iApply bi.later_forall_2. iIntros (o). rewrite -later_equivI.
    iApply internal_eq_sym. iApply ("Hincl" $! o).
  Qed.

  Lemma thread_post_alloc γ π ι P :
    π !! ι = None →
    thread_post_auth γ π ==∗ thread_post_auth γ (<[ι := P]> π) ∗ thread_post_frag γ ι P.
  Proof.
    iIntros (Hfresh) "Hauth".
    rewrite /thread_post_auth /thread_post_frag -own_op fmap_insert.
    iApply (own_update with "Hauth").
    apply (gmap_view_alloc _ ι DfracDiscarded (to_agree _)); [|done..].
    by rewrite lookup_fmap Hfresh.
  Qed.

End thread_post.
