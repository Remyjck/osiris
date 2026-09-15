From iris.base_logic.lib Require Import own gen_heap ghost_map invariants token proph_map.
From iris.base_logic Require Import ghost_map.
From iris.algebra Require Import gmap_view dfrac gset auth excl ofe.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import thread_ids syntax locations encode.
From osiris.semantics Require Import semantics.
Require Import subjective_step.
Require Export thread_post.

(* -------------------------------------------------------------------------- *)

(** *Basic resource algebra for Osiris *)

(* The store is viewed as an authoritative ghost map. *)

Section ghost_instances.

  Context (Σ : gFunctors).

  (* We have to declare ghost state singletons for our global state,
     which are documented here:
     https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/resource_algebras.md?ref_type=heads#advanced-topic-ghost-state-singletons
   *)

  (* The [osirisGpreS] typeclass is used for ghost-state initialisation
     in our proof of adequacy. *)

  Class osirisGpreS := {
      #[global] osirisGpreS_iris :: invGpreS Σ;
      #[global] osiris_gen_GpreS :: gen_heapGpreS locations.loc mem_block Σ;
      #[global] osiris_threadPostG :: threadPostG Σ;
      osiris_tokenG :: tokenG Σ;
      #[global] osiris_array_ghostG :: ghost_mapG Σ locations.loc (list locations.loc);
      #[global] osiris_prophGpreS :: proph_mapGpreS locations.loc (val * val) Σ;
    }.

  (* The [osirisGS] typeclass is what we use in our proofs.
     The "simple" ghost state is inherited from [osirisGpreS].

     The other ghost-state singletons which are stated explicitly are those
     that require an initialisation lemma in the proof of adequacy,
     such as [gen_heap_init] for the heap and the postcondition-tracking map. *)

  Class osirisGS := OsirisGS
    { osiris_inG :: osirisGpreS;
      (* This gives us fancy updates (without allowing Later Credits). *)
      osiris_invGS :: invGS_gen HasNoLc Σ;
      (* This gives us a heap, which maps locations to values. *)
      osiris_genGS :: gen_heapGS locations.loc mem_block Σ;
      (* This names the ghost map holding the thread postconditions. The
         predicates are stored in it directly, indexed by thread id. *)
      osiris_post_name : gname;
      (* This gives us tokens, for resource transfer when joining threads *)
      (* This gives us a ghost map tracking array locations (persistent per array). *)
      osiris_array_ghostGS :: ghost_mapG Σ locations.loc (list locations.loc);
      osiris_array_name : gname;
      (* This gives us the prophecy map, relating [proph] assertions to
         the observations the execution has yet to produce. *)
      osiris_prophGS :: proph_mapGS locations.loc (val * val) Σ;
    }.

End ghost_instances.

(* Provide a minimal gFunctors for invariants, the store, and the thread postconditions. *)
Definition osirisΣ : gFunctors :=
  #[ invΣ;
     gen_heapΣ locations.loc mem_block;
     threadPostΣ;
     tokenΣ;
     ghost_mapΣ locations.loc (list locations.loc);
     proph_mapΣ locations.loc (val * val)
    ].

(* Show that inclusion of [osirisΣ] in [Σ] is enough to instantiate [osirisGpreS Σ]. *)
Global Instance subG_heapGpreS {Σ} : subG osirisΣ Σ → osirisGpreS Σ.
Proof. solve_inG. Qed.

#[global] Arguments OsirisGS Σ {_ _ _ _ _ _ _} : assert.


(* -------------------------------------------------------------------------- *)
(* Notations for ghost resouces. *)

(* Ownership of the heap. *)

Notation "l ↦ dq v" :=
  (pointsto l dq (Val v))
    (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

(* Ownership of continuations. *)

(* We declare that [cont] can be used as keys for pointstos. *)
Global Instance osiris_cont_heapGS `{osirisGS Σ} : gen_heap.gen_heapGS cont mem_block Σ.
Proof. unfold cont; simpl. apply (osiris_genGS Σ). Defined.

Definition isCont `{osirisGS Σ} (k : cont) (sk : outcome2 val exn -> microvx)
  : iProp Σ :=
  gen_heap.pointsto k (DfracOwn 1) (Kont sk).

Definition isShot `{osirisGS} (k : cont) : iProp Σ :=
  pointsto k (DfracOwn 1) Shot.

(* Ownership of memory blocks. *)

(* We declare that [block] can be used as keys for pointstos. *)
Global Instance osiris_block_heapGS `{osirisGS Σ} : gen_heap.gen_heapGS locations.loc mem_block Σ.
Proof. apply (osiris_genGS Σ). Defined.

Definition isBlock `{osirisGS Σ} (b : locations.loc) dq t : iProp Σ :=
  ∃ ls, gen_heap.pointsto b dq (Block t ls).

(* Taking a freshly allocated block's exclusive tag to the persistent
   form above. Every block that enters a shared invariant goes through
   this. *)

Lemma isBlock_persist `{osirisGS Σ} b t :
  isBlock b (DfracOwn 1) t ==∗ isBlock b DfracDiscarded t.
Proof.
  iIntros "H".
  iDestruct "H" as (ls) "H".
  iMod (gen_heap.pointsto_persist with "H") as "H".
  iModIntro. iExists ls. iFrame.
Qed.

(* -------------------------------------------------------------------------- *)
(* Definition of the state interpretation. *)

Section state_interp.

  Context `{!osirisGS Σ}.

  (* The state interpretation pairs a heap interpretation
     [osiris_state_interp σ] with a thread-pool interpretation
     [osiris_thread_interp π]. *)

  (* The heap interpretation [osiris_state_interp σ] has two components.
     The main component is a [gen_heap] authoritative resource over the
     physical store [σ], which gives exclusive ownership of individual memory
     cells via [l ↦ v]. The auxiliary component is a ghost map that records,
     for each allocated array block, its list of element locations. The
     [array_coherent] predicate ties the two: every entry in the ghost map
     points to a [Block] block in [σ] with the same locations. *)

  (* The ghost map for arrays is kept separate from the heap because array
     identity must be persistent: once a block is allocated its location list
     never changes. On allocation we immediately persist the fragment and hand
     it out as [isBlockLocs a ls], a read-only token that can be shared freely
     between concurrent threads and used to look up element locations.
     Crucially, [isBlockLocs] does not track the mutability tag, so the tag can
     be updated freely without invalidating any ghost resources. *)

  (* The thread-pool interpretation [osiris_thread_interp π] is a ghost map
     from thread ids to postconditions. A thread id indexes its predicate
     directly, which is what lets a joining thread recover the postcondition
     of a terminated thread. See [thread_post.v] for the construction. *)

  Definition osiris_thread_interp (π : post_map Σ) : iProp Σ :=
    thread_post_auth (osiris_post_name Σ) π.

  (* [valid_thread ι P] is a persistent token that witnesses
     thread ι has postcondition P. *)
  Definition valid_thread (ι : thread) (P : outcome2 val exn -d> iPropO Σ) : iProp Σ :=
    thread_post_frag (osiris_post_name Σ) ι P.

  Global Instance valid_thread_persistent ι P :
    Persistent (valid_thread ι P).
  Proof. apply _. Qed.

  Global Instance valid_thread_contractive ι : Contractive (valid_thread ι).
  Proof. apply _. Qed.

  (* Coherence between the ghost array map σ' and the physical store σ:
     every array registered in σ' has a corresponding block in σ with the same locations. *)
  Definition array_coherent (σ' : gmap locations.loc (list loc)) (σ : store) : Prop :=
    ∀ (a : loc) (ls : list loc),
      σ' !! (a : loc) = Some ls → ∃ t : mut_tag, σ !! a = Some (Block t ls).

  Definition array_interp (σ : store) : iProp Σ :=
    ∃ σ', ghost_map_auth (osiris_array_name Σ) 1 σ' ∗ ⌜array_coherent σ' σ⌝.

  Definition osiris_state_interp (σ : store) : iProp Σ :=
    @gen_heap_interp locations.loc _ _ mem_block Σ _ σ ∗ array_interp σ.

  (* The prophecy interpretation. [κs] is the list of observations the
     execution has yet to produce, and [proph_map_interp κs ps] ties the
     [proph p vs] assertions to it. *)

  (* [ps] is the set of prophecy identifiers allocated so far. It is
     pinned to the store's domain: allocating a prophecy needs a fresh
     identifier for [ps], while the operational rule [StepNewProph] offers
     a fresh one for the store. Tying the two lets the freshness conditions
     meet. *)

  Definition osiris_proph_interp (σ : store) (κs : list observation) : iProp Σ :=
    ∃ ps, ⌜ps ⊆ dom σ⌝ ∗ proph_map_interp κs ps.

  Lemma osiris_proph_interp_mono σ σ' κs :
    dom σ ⊆ dom σ' →
    osiris_proph_interp σ κs -∗ osiris_proph_interp σ' κs.
  Proof.
    iIntros (Hsub) "(%ps & %Hps & H)".
    iExists ps. iFrame. iPureIntro. set_solver.
  Qed.

  Definition state_interp : (store * list observation * post_map Σ) -> iProp Σ :=
    (λ '(σ, κs, π),
       osiris_state_interp σ ∗ osiris_proph_interp σ κs ∗ osiris_thread_interp π)%I.

  (* [isBlockLocs a ls] is the persistent ghost knowledge that array [a] has locations [ls]. *)
  Definition isBlockLocs (a : loc) (ls : list locations.loc) : iProp Σ :=
    (a ↪[osiris_array_name Σ]□ ls ∗ ⌜(list_z.length ls ≤ int.max_array_length)%Z⌝)%I.

  Global Instance isBlockLocs_pers a ls : Persistent (isBlockLocs a ls).
  Proof. apply _. Qed.

  Global Instance isBlockLocs_pers_array (a : syntax.array) ls : Persistent (isBlockLocs a ls) :=
    isBlockLocs_pers a ls.

  Global Instance isBlockLocs_pers_record (a : syntax.record) ls : Persistent (isBlockLocs a ls) :=
    isBlockLocs_pers a ls.

  Lemma isBlockLocs_valid a ls1 ls2 :
    isBlockLocs a ls1 -∗ isBlockLocs a ls2 -∗ ⌜ls2 = ls1⌝.
  Proof.
    iIntros "(Ha & _) (Ha' & _)".
    iPoseProof (ghost_map_elem_agree with "Ha Ha'") as "%H".
    iPureIntro. exact (eq_sym H).
  Qed.

  Lemma isBlockLocs_length a ls :
    isBlockLocs a ls -∗ ⌜(list_z.length ls ≤ int.max_array_length)%Z⌝.
  Proof. iIntros "(_ & $)". Qed.

  (* -------------------------------------------------------------------- *)
  (** [osiris_state_interp] operations. *)

  Lemma osiris_state_valid σ l dq (v : mem_block) :
    osiris_state_interp σ -∗ pointsto l dq v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "(Hmem & _) Hl".
    iApply (gen_heap_valid with "Hmem Hl").
  Qed.

  Lemma osiris_state_valid_array σ (l : loc) ls :
    osiris_state_interp σ -∗
    l ↪[osiris_array_name Σ]□ ls -∗
    ∃ t, ⌜σ !! (l : locations.loc) = Some (Block t ls)⌝.
  Proof.
    iIntros "(_ & %A & Hauth & %Hcoh) #Hfrag".
    iDestruct (ghost_map_lookup with "Hauth Hfrag") as "%Hlookup".
    destruct (Hcoh l ls Hlookup) as (t & Hσl).
    iExists t. iPureIntro. exact Hσl.
  Qed.

  (* [mem_block_view] splits a [mem_block] into the [Block] case (which carries
     a list of locations) and everything else. Used to shorten the proof of
     [osiris_state_alloc]. *)
  Variant mem_block_view : mem_block → Type :=
  | view_block t ls : mem_block_view (Block t ls)
  | view_nonblock b  : (∀ t ls, b ≠ Block t ls) → mem_block_view b.

  Lemma block_view b : mem_block_view b.
  Proof. destruct b; econstructor; congruence. Defined.

  Lemma osiris_state_alloc σ (l : locations.loc) (v : mem_block) :
    σ !! l = None →
    osiris_state_interp σ ==∗
    osiris_state_interp (<[l := v]>σ) ∗ pointsto l (DfracOwn 1) v ∗ meta_token l ⊤ ∗
    match block_view v with
    | view_block _ ls => (l : loc) ↪[osiris_array_name Σ]□ ls
    | view_nonblock _ _ => True
    end.
  Proof.
    iIntros (Hfresh) "(Hmem & (%σ' & Hauth & %Hcoh))".
    iMod (gen_heap_alloc σ l v with "Hmem") as "(Hmem & Hl & Hmeta)"; first done.
    destruct (block_view v).
    - (* Block: register the new block in the ghost array map. *)
      iAssert ⌜σ' !! (l : loc) = None⌝%I as "%HA_fresh".
      { iPureIntro. apply not_elem_of_dom. intros Hin.
        apply elem_of_dom in Hin as (ls' & Hlookup).
        destruct (Hcoh l ls' Hlookup) as (? & Hσl).
        rewrite Hσl in Hfresh. done. }
      iMod (ghost_map_insert (l : loc) ls with "Hauth") as "(Hauth & Hfrag)"; first done.
      iMod (ghost_map.ghost_map_elem_persist with "Hfrag") as "Hfrag".
      iModIntro. iSplitL "Hmem Hauth"; last iFrame.
      iFrame "Hmem". iExists (<[(l : loc) := ls]>σ'). iFrame. iPureIntro.
      intros a ls_a Hlookup.
      destruct (decide (a = l)) as [->|Hne].
      + rewrite lookup_insert in Hlookup. simplify_map_eq.
        exists t. rewrite lookup_insert. rewrite decide_True_pi. done.
      + rewrite lookup_insert_ne in Hlookup; last done.
        destruct (Hcoh a ls_a Hlookup) as (t_a & Hσa).
        exists t_a. rewrite lookup_insert_ne; done.
    - (* Not a Block: array coherence is trivially preserved. *)
      iModIntro. iFrame. iPureIntro.
      intros a ls_a Hlookup.
      destruct (Hcoh a ls_a Hlookup) as (t_a & Hσa).
      destruct (decide (a = l)) as [->|Hne].
      + congruence.
      + exists t_a. rewrite lookup_insert_ne; done.
  Qed.

  Lemma osiris_state_update (v' v : mem_block) σ l :
    (∀ t ls, v ≠ Block t ls) →
    osiris_state_interp σ -∗ pointsto l (DfracOwn 1) v ==∗
    osiris_state_interp (<[l := v']>σ) ∗ pointsto l (DfracOwn 1) v'.
  Proof.
    iIntros (Hnotblock) "(Hmem & Harreg) Hl".
    iDestruct (gen_heap_valid with "Hmem Hl") as "%Hσl".
    iMod (gen_heap_update with "Hmem Hl") as "(Hmem & Hl)".
    iModIntro. iFrame.
    iDestruct "Harreg" as "(%σ' & $ & %Hcoh)". iPureIntro.
    intros a ls_a Hlookup.
    destruct (Hcoh a ls_a Hlookup) as (t_a & Hσa).
    destruct (decide (a = l)) as [->|Hne].
    - rewrite Hσl in Hσa. injection Hσa as Hσa.
      exact (False_rect _ (Hnotblock t_a ls_a Hσa)).
    - exists t_a. rewrite lookup_insert_ne; done.
  Qed.

  Lemma osiris_state_set_tag σ l t t' ls :
    osiris_state_interp σ -∗ pointsto l (DfracOwn 1) (Block t ls) ==∗
    osiris_state_interp (<[l := Block t' ls]>σ) ∗ pointsto l (DfracOwn 1) (Block t' ls).
  Proof.
    iIntros "(Hmem & Harreg) Hl".
    iDestruct (gen_heap_valid with "Hmem Hl") as "%Hσl".
    iMod (gen_heap_update with "Hmem Hl") as "(Hmem & Hl)".
    iModIntro. iFrame.
    iDestruct "Harreg" as "(%A & Hauth & %Hcoh)". iExists A. iFrame. iPureIntro.
    intros a ls_a Hlookup.
    destruct (Hcoh a ls_a Hlookup) as (t_a & Hσa).
    destruct (decide (a = l)) as [->|Hne].
    - rewrite Hσl in Hσa. injection Hσa as <-.
      subst. exists t'. rewrite lookup_insert. rewrite decide_True_pi. done.
    - exists t_a. rewrite lookup_insert_ne; done.
  Qed.

  (* -------------------------------------------------------------------- *)
  (** [osiris_thread_interp] operations. *)

  (** If we have a [valid_thread] resource, then the thread exists in the
      threadpool, and the predicate recorded there agrees with ours. The
      agreement is step-indexed, hence the [▷]. *)
  Lemma valid_thread_lookup π ι P :
    osiris_thread_interp π -∗
    valid_thread ι P -∗
    osiris_thread_interp π ∗ ∃ Q, ⌜π !! ι = Some Q⌝ ∗ ▷ (∀ o, Q o ≡ P o).
  Proof.
    iIntros "Hti #Hvalid".
    iDestruct (thread_post_lookup with "Hti Hvalid") as "#Hagree".
    by iFrame "Hti Hagree".
  Qed.

  (** Allocate a new thread in the threadpool with a given postcondition.

      This gives us a [valid_thread] resource
      that witnesses the thread's postcondition. *)
  Lemma thread_alloc π ι (P : outcome2 val exn -d> iPropO Σ) :
    π !! ι = None →
    osiris_thread_interp π ==∗
      osiris_thread_interp (<[ ι := P ]> π) ∗ valid_thread ι P.
  Proof. iIntros (Hlookup) "Hauth". by iApply thread_post_alloc. Qed.

End state_interp.
