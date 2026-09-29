(* A thread-indexed map of postconditions.

   This is what [osiris_thread_interp] is built from: a single ghost map whose
   values are the postconditions themselves, so a thread id indexes its
   predicate directly. There is no gname naming a saved predicate in between.

   A postcondition is written once, when its thread is forked, and only read
   afterwards, so no ownership of an entry is needed. The map is an
   authoritative map of agreements: a fragment [◯ {[ι := to_agree P]}] is
   persistent by construction.

   The [▶] under the [agree] is what keeps the domain equation contractive.
   It is also the one cost of the design: reading a thread's predicate back
   out of the map only ever gives agreement up to a [▷], so a client holding
   [valid_thread ι P] learns [▷ (Q o ≡ P o)] rather than a definitional
   equality. Every rule that needs it is already under a [▷]. *)

From iris.algebra Require Import auth gmap agree.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import thread_ids syntax locations encode.
From osiris.semantics Require Import semantics.

Definition postO (Σ : gFunctors) : ofe := outcome2 val exn -d> iPropO Σ.

Definition thread_postUR (Σ : gFunctors) : ucmra :=
  gmapUR thread (agreeR (outcome2 val exn -d> laterO (iPropO Σ))).

Class threadPostG (Σ : gFunctors) := {
  #[global] thread_post_inG ::
    inG Σ (authR (gmapUR thread (agreeR (outcome2 val exn -d> laterO (iPropO Σ)))));
}.

Definition threadPostΣ : gFunctors :=
  #[ GFunctor (authRF (gmapURF thread (agreeRF (outcome2 val exn -d> ▶ ∙)))) ].

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
    own γ (● (((λ P, to_agree (post_unfold P)) <$> π) : thread_postUR Σ)).

  Definition thread_post_frag (γ : gname) (ι : thread) (P : postO Σ) : iProp Σ :=
    own γ (◯ ({[ι := to_agree (post_unfold P)]} : thread_postUR Σ)).

  Global Instance thread_post_frag_persistent γ ι P :
    Persistent (thread_post_frag γ ι P).
  Proof. apply _. Qed.

  Global Instance thread_post_frag_contractive γ ι : Contractive (thread_post_frag γ ι).
  Proof. solve_contractive. Qed.

  (* The shape the adequacy proof allocates the map in. *)
  Lemma thread_post_auth_empty γ :
    thread_post_auth γ ∅ ⊣⊢ own γ (● (∅ : thread_postUR Σ)).
  Proof. by rewrite /thread_post_auth fmap_empty. Qed.

  Lemma thread_post_init :
    ⊢ |==> ∃ γ, thread_post_auth γ ∅.
  Proof.
    iMod (own_alloc (● (∅ : thread_postUR Σ))) as (γ) "H".
    { apply auth_auth_valid. exact (ucmra_unit_valid (A := thread_postUR Σ)). }
    iExists γ. by rewrite thread_post_auth_empty.
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
    rewrite auth_both_validI.
    iDestruct "Hv" as "[[%c Heq] Hval]".
    rewrite gmap_equivI gmap_validI.
    iSpecialize ("Heq" $! ι). iSpecialize ("Hval" $! ι).
    rewrite lookup_op lookup_singleton_eq lookup_fmap.
    (* The lookups came out of rewrites, so [destruct] alone may not reach
       them in the hypotheses: every case split is followed by [rewrite ?H].
       The frame [c] may hold a copy of the same entry; validity makes it
       agree, so it changes nothing. *)
    iAssert (∃ Q, ⌜π !! ι = Some Q⌝ ∗ to_agree (post_unfold Q) ≡ to_agree (post_unfold P))%I
      with "[Heq Hval]" as (Q) "[%Hπ Heq]".
    { destruct (π !! ι) as [Q|] eqn:Hπ; rewrite ?Hπ /=;
        destruct (c !! ι) as [z|] eqn:Hc; rewrite ?Hc /= option_equivI /=;
        try by iDestruct "Heq" as "[]".
      - iExists Q. iSplit; first done.
        iDestruct "Heq" as "#Heq".
        rewrite option_validI /=. iRewrite "Heq" in "Hval".
        iDestruct (agree_op_invI with "Hval") as "Hxz".
        iRewrite -"Hxz" in "Heq". by rewrite agree_idemp.
      - iExists Q. by iSplit. }
    iExists Q. iSplit; first done.
    rewrite agree_equivI discrete_fun_equivI.
    iApply bi.later_forall_2. iIntros (o). rewrite -later_equivI.
    iApply ("Heq" $! o).
  Qed.

  Lemma thread_post_alloc γ π ι P :
    π !! ι = None →
    thread_post_auth γ π ==∗ thread_post_auth γ (<[ι := P]> π) ∗ thread_post_frag γ ι P.
  Proof.
    iIntros (Hfresh) "Hauth".
    rewrite /thread_post_auth /thread_post_frag -own_op fmap_insert.
    iApply (own_update with "Hauth").
    apply auth_update_alloc.
    apply (alloc_singleton_local_update
             (A := agreeR (outcome2 val exn -d> laterO (iPropO Σ)))); last done.
    by rewrite lookup_fmap Hfresh.
  Qed.

End thread_post.
