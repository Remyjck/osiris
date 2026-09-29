From iris.base_logic.lib Require Import own gen_heap ghost_map invariants saved_prop token proph_map.
From iris.base_logic Require Import ghost_map.
From iris.algebra Require Import gmap_view dfrac gset auth excl ofe.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import thread_ids syntax locations encode.
From osiris.semantics Require Import semantics.
Require Import subjective_step.
Require Export protocols.

Definition discrete_fun2 {A B} := λ (C : A -> B → ofe), ∀ (x : A) (y : B), C x y.

Section discrete_fun2.

  Context {A B : Type} {C : A -> B -> ofe}.
  Implicit Types f g : discrete_fun2 C.

  Global Instance discrete_fun2_dist : Dist (discrete_fun2 C) :=
    λ n (f g : discrete_fun2 C), ∀ (x : A) (y : B), f x y ≡{n}≡ g x y.

  Global Instance discrete_fun2_equiv : Equiv (discrete_fun2 C) :=
    λ (f g : discrete_fun2 C), ∀ (x : A) (y : B), f x y ≡ g x y.

  Definition discrete_fun2_ofe_mixin : OfeMixin (discrete_fun2 C).
  Proof.
    split.
    - split; [ intros Hequiv n | intros Hdist ].
      + rewrite /dist /discrete_fun2_dist.
        intros x' y'. specialize (Hequiv x' y'). by rewrite Hequiv.
      + rewrite /equiv /discrete_fun2_equiv.
        intros x' y'. apply equiv_dist. intros n.
        specialize (Hdist n x' y'). apply Hdist.
    - intros n. rewrite /dist. split.
      + intros f x y. auto.
      + intros f g Hdist x y.
        symmetry.
        apply Hdist.
      + intros f g h Hdistfg Hdistgh.
        rewrite /discrete_fun2_dist in Hdistfg Hdistgh |-*.
        intros x y.
        transitivity (g x y); auto.
    - intros n m f g Hdist Hlt.
      rewrite /dist /discrete_fun2_dist. intros x y.
      eapply dist_le. apply Hdist. apply Hlt.
  Qed.

  Canonical Structure discrete_fun2O : ofe := Ofe (discrete_fun2 C) discrete_fun2_ofe_mixin.

  Program Definition discrete_fun2_chain (c : chain discrete_fun2O)
    (x : A) (y : B) : chain (C x y) := {| chain_car n := c n x y |}.
  Next Obligation. intros c x y n i ?. by apply (chain_cauchy c). Qed.

  Program Definition discrete_fun2_bchain {n} (c : bchain discrete_fun2O n)
    (x : A) (y : B) : bchain (C x y) n := {| bchain_car n Hn := c n Hn x y |}.
  Next Obligation. intros n c x y m p Hm Hp Hmp. by apply (bchain_cauchy n c). Qed.

  Global Program Instance discrete_fun2_cofe `{∀ x y, Cofe (C x y)} :
      Cofe discrete_fun2O := {
    compl c x y := compl (discrete_fun2_chain c x y);
    lbcompl n Hn c x y := lbcompl Hn (discrete_fun2_bchain c x y)
  }.
  Next Obligation.
    intros ? n c x y.
    apply (conv_compl n (discrete_fun2_chain c x y)).
  Qed.
  Next Obligation. intros ? n Hn c m Hm x y. by rewrite (conv_lbcompl _ _ Hm). Qed.
  Next Obligation.
    intros ? n Hn c1 c2 m Hc x y. apply lbcompl_ne=> ?? /=. by apply Hc.
  Qed.

  Global Instance discrete_fun2_inhabited `{∀ x y, Inhabited (C x y)} : Inhabited discrete_fun2O :=
    populate (λ _, inhabitant).

End discrete_fun2.

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
      #[global] osiris_thread_gen_GpreS :: gen_heapGpreS thread gname Σ;
      #[global] osiris_savedPredG :: savedPredG Σ (outcome2 val exn);
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
      (* This gives us a ghost map for thread postconditions (stored as gnames). *)
      osiris_thread_postGS :: gen_heapGS thread gname Σ;
      (* savedPropG is inherited from osirisGpreS via osiris_inG *)
      (* This gives us tokens, for resource transfer when joining threads *)
      (* This gives us a ghost map tracking array locations (persistent per array). *)
      osiris_array_ghostGS :: ghost_mapG Σ locations.loc (list locations.loc);
      osiris_array_name : gname;
      (* This gives us the prophecy map, relating [proph] assertions to
         the observations the execution has yet to produce. *)
      osiris_prophGS :: proph_mapGS locations.loc (val * val) Σ;
    }.

End ghost_instances.

(* Provide a minimal gFunctors for invariants, the store, and named postconditions for threads. *)
Definition osirisΣ : gFunctors :=
  #[ invΣ;
     gen_heapΣ locations.loc mem_block;
     gen_heapΣ thread gname;
     savedPredΣ (outcome2 val exn);
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
     from thread ids to gnames. Each gname names a saved predicate that stores
     the postcondition of that thread. This allows a joining thread to recover
     the postcondition of a terminated thread. *)

  Definition osiris_thread_interp π : iProp Σ :=
    @gen_heap_interp thread _ _ gname Σ _ π.

  (* [valid_thread ι P] is a persistent token that witnesses
     thread ι has postcondition P. *)
  Definition valid_thread (ι : thread) (P : outcome2 val exn -d> iPropO Σ) : iProp Σ :=
    ∃ γ, pointsto ι DfracDiscarded γ ∗ saved_pred_own γ DfracDiscarded P.

  Global Instance valid_thread_persistent ι P :
    Persistent (valid_thread ι P).
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

  (* The prophecy interpretation. Unlike every other component of the state
     interpretation, [proph_map_interp] does not describe the present: [κs]
     is the list of observations the execution has yet to produce, and
     [proph_map_interp κs ps] ties the [proph p vs] assertions to it. That
     is what makes a prediction meaningful, and why the trace must reach
     adequacy; see [ewp_adequacy.v].

     [ps] is the set of prophecy identifiers allocated so far; it is
     existentially quantified here because no rule needs to name it. *)

  (* [ps] is the set of prophecy identifiers allocated so far. It is
     pinned to the store's domain, and that is not bookkeeping: allocating
     a prophecy needs an identifier fresh for [ps], while the operational
     rule [StepNewProph] only offers one fresh for the store. Tying the
     two is what lets the two freshness conditions meet. Nothing ever
     removes a location from the store, so the inclusion is easy to
     maintain; see [osiris_proph_interp_mono]. *)

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

  (** If we have a [valid_thread] resource, then the thread exists in the threadpool
      and we can look up its gname from the ghost map, which points to the postcondition. *)
  Lemma valid_thread_lookup π ι P :
    osiris_thread_interp π -∗
    valid_thread ι P -∗
    osiris_thread_interp π ∗ ∃ γ, ⌜π !! ι = Some γ⌝ ∗ saved_pred_own γ DfracDiscarded P.
  Proof.
    iIntros "Hti #Hvalid".
    rewrite /valid_thread.
    iDestruct "Hvalid" as (γ) "[#Hpt #Hsaved]".
    iDestruct (gen_heap_valid with "Hti Hpt") as %Hlookup.
    iFrame "Hti". iExists γ. iFrame "Hsaved". iPureIntro. done.
  Qed.

  (** Allocate a new thread in the threadpool with a given postcondition.

      This gives us a [valid_thread] resource
      that witnesses the thread's postcondition. *)
  Lemma thread_alloc π ι (P : outcome2 val exn -d> iPropO Σ) :
    π !! ι = None →
    osiris_thread_interp π ==∗
      ∃ γ, osiris_thread_interp (<[ ι := γ ]> π) ∗ pointsto ι DfracDiscarded γ ∗ saved_pred_own γ DfracDiscarded P.
  Proof.
    iIntros (Hlookup) "Hauth".
    (* Allocate a saved predicate for the postcondition P *)
    iMod (saved_pred_alloc P DfracDiscarded) as (γ) "#Hsaved"; first done.
    (* Insert γ into the thread ghost map *)
    iMod (gen_heap_alloc π ι γ with "Hauth") as "(Hauth & Hvalid & _)"; first done.
    (* Make the pointsto persistent *)
    iMod (pointsto_persist with "Hvalid") as "#Hvalid".
    iModIntro. iExists γ. iFrame "Hauth".
    (* Package up valid_thread *)
    iFrame "Hvalid Hsaved".
  Qed.

End state_interp.

(* ========================================================================== *)

(** *Effect-aware Weakest Precondition *)

(* The type [ewp_case A E] represents computations that are handled
   differently by [ewp]:

      Either
      (1) a terminated computation with result of type (outcome2 A E),
      (2) a crash
      (3) a performed effect
      (4) a computation that can take a step
      (5) a join
 *)

Inductive ewp_case (A E : Type) : Type :=
  WPOutcome : (outcome2 A E) → ewp_case A E
| WPCrash : ewp_case A E
| WPPerform : C.eff -> (outcome2 val exn -> micro A E) → ewp_case A E
| WPStep : ewp_case A E
| WPJoin : thread → (outcome2 val exn → micro A E) → ewp_case A E.

Arguments ewp_case {A E}.

Arguments WPOutcome {A E}.
Arguments WPCrash {A E}.
Arguments WPPerform {A E}.
Arguments WPStep {A E}.
Arguments WPJoin {A E}.

(* Determine which [ewp_case] a given [m] is. *)
Definition is_ewp_case {A X} (m : micro A X) : ewp_case :=
  match m with
  | Ret v => WPOutcome (O2Ret v)
  | Throw e => WPOutcome (O2Throw e)
  | Crash => WPCrash
  | Stop CPerf e k => WPPerform e k
  | Stop CJoin ι' k => WPJoin ι' k
  | _ => WPStep
  end.

Lemma subjective_step_is_WPStep {A X} σ π (m m' : micro A X) σ' μ κ :
  subjective_step (σ, m, π) κ (σ', m', μ) ->
  is_ewp_case m = WPStep.
Proof.
  intros Hwp.
  destruct_subjective_step; reflexivity.
Qed.

Lemma inv_is_ewp_case_outcome {A X} (m : micro A X) o :
  is_ewp_case m = WPOutcome o →
  m = inject2 o.
Proof. destruct m; try by inversion 1. destruct c; discriminate 1. Qed.

(* -------------------------------------------------------------------------- *)

(** *Definition of the effectful weakest precondition *)

Section ewp_def.

  Context `{!osirisGS Σ}.

  (* [ewp] takes four parameters:
     - [ι]: the identifier of the current thread
     - [E]: the mask i.e. set of names we may open.
     - [m]: the ongoing computation, an element of the [micro] monad.
     - [Ψ]: the current protocol (in the sense of Hazel)
     - [φ]: the postcondition
   *)

  Definition ewp_pre
    (ewp : ∀ {A X}, coPset -d> micro A X -d> (iEff Σ) -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :
    (∀ {A X}, coPset -d> micro A X -d> (iEff Σ) -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :=
    λ A X E m Ψ φ,
      (match is_ewp_case m with
       (* [EWP1]: Returned values and raised exceptions. *)
       | WPOutcome o => |={E}=> φ o
       (* [EWP2]: Undefined and undesirable behaviour. *)
       | WPCrash => |={E}=> False
       (* [EWP3]: Effectful case
          The effect [e] satisfies protocol Ψ and the permitted replies
          satisfy the [ewp] when continued with the continuation [k]. *)
       | WPPerform e k =>
           |={E}=> Ψ allows perform e << λ o, ▷ ewp E (k o) Ψ φ >>
       | WPStep =>
           ∀ σ κ κs π,
             state_interp (σ, κ ++ κs, π) ={E, ∅}=∗
             ⌜can_progress σ (dom π) m⌝ ∗
             ∀ σ' m' μ,
               ⌜subjective_step (σ, m, dom π) κ (σ', m', μ)⌝ ={∅}=∗ ▷ (|={∅,E}=>
               ewp E m' Ψ φ ∗
               match μ with
               | None => state_interp (σ', κs, π)
               | Some (ι', mforked) =>
                   ∃ φ' γ, state_interp (σ', κs, <[ι' := γ]> π) ∗
                           saved_pred_own γ DfracDiscarded φ' ∗
                           ewp ⊤ mforked ⊥ (λ o, □ φ' o)
               end)
       (* [EWP5]: A request to join a thread [ι']. *)
       | WPJoin ι' k =>
           ∀ σ κs π,
             state_interp (σ, κs, π) ={E, ∅}=∗
             match π !! ι' with
             | None => |={∅, E}=> ▷ False
             | Some γ =>
                 ∃ φ', saved_pred_own γ DfracDiscarded φ' ∗
                       ▷ (∀ o, □ φ' o ={∅}=∗ |={∅,E}=>
                          ewp E (k o) Ψ φ ∗ state_interp (σ, κs, π))
             end
       end)%I.

  Local Instance ewp_pre_contractive : Contractive ewp_pre.
  Proof.
    rewrite /ewp_pre /= => n ewp ewp' Hwp A X E m Ψ φ.
    f_equiv. do 2 f_equiv. intro o. f_contractive. apply Hwp.
    - repeat (f_contractive || f_equiv || apply Hwp).
    - repeat (f_contractive || f_equiv || apply Hwp).
  Qed.

  Definition ewp_def : ∀ A X, coPset -> micro A X -d> (iEff Σ) -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ :=
    @fixpoint _ _ discrete_fun2_cofe _ ewp_pre ewp_pre_contractive.

  Local Definition ewp_aux : seal (@ewp_def). Proof. by eexists. Qed.
  Definition ewp' := ewp_aux.(unseal).

  Global Arguments ewp' {E e Ψ Φ} : rename.
  Global Arguments ewp_def {A X}.

End ewp_def.

(* -------------------------------------------------------------------------- *)

Section ewp_properties.

Context {A X P : Type}.
Context `{osirisGS Σ}.
Implicit Type Ψ : iEff Σ.
Implicit Type φ : outcome2 A X → iProp Σ.
Implicit Type a : val.
Implicit Type m : micro A X.

(* Notation wp := (wp (PROP:=iProp Σ)). *)

Lemma ewp_unfold {E} {Ψ} {φ} (m : micro A X)  :
  ewp_def E m Ψ φ ⊣⊢ ewp_pre (@ewp_def Σ _) E m Ψ φ.
Proof.
  rewrite {1}/ewp_def.
  apply (@fixpoint_unfold _ _ discrete_fun2_cofe _ ewp_pre).
Qed.

Local Ltac ewp_unfold_all :=
  rewrite !ewp_unfold /ewp_pre /=.

Global Instance ewp_ne E m n Ψ :
  Proper (pointwise_relation _ (dist n) ==> (dist n)) (ewp_def E m Ψ).
Proof.
  induction (lt_wf n) as [n _ IH] in m, Ψ |-* => Φ Ψ' HΦ.
  ewp_unfold_all.
  f_equiv. f_equiv.
  - do 8 f_equiv.
  - repeat f_equiv. intro o. f_contractive.
    apply IH; auto; intro; auto.
    eapply dist_lt; eauto.
  - do 20 (f_contractive || f_equiv).
    do 2 f_equiv.
    apply IH; eauto.
    f_equiv.
    eapply dist_lt; eauto.
  - do 18 (f_contractive || f_equiv).
    + f_equiv. apply IH; eauto. f_equiv. eapply dist_lt; eauto.
Qed.

Global Instance ewp_proper E m Ψ:
  Proper
    (pointwise_relation _ (≡) ==> (≡))
    (ewp_def E m Ψ).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ewp_ne=>v; apply equiv_dist.
Qed.

Global Instance ewp_contractive E m Ψ n:
  TCEq (is_ewp_case m) WPStep →
  Proper
    (pointwise_relation _ (dist_later n) ==> dist n)
    (ewp_def E m Ψ).
Proof.
  intros He Φ Ψ' HΦ. ewp_unfold_all. rewrite He /=.
  repeat (f_contractive || f_equiv).
Qed.

End ewp_properties.


(* ========================================================================== *)

Definition impure {A V X} `{osirisGS Σ} `{Observe A V}
  (E : coPset) (m : micro V X) (Ψ : iEff Σ) :
  ∀ {B} `{Observe B X}, (B → iProp Σ) → (A → iProp Σ) → iProp Σ :=
  λ B _ ζ Φ, ewp_def E m Ψ (ilift (ireturns ζ) (ireturns Φ)).

(* ========================================================================== *)

(** *Notation *)

(* Bottom instance for function types, needed for the ⊥ in notations *)
Global Instance bottom_fun {Σ} {A : Type} : Bottom (A → iProp Σ) := λ _, False%I.

(* Notation for [impure] *)

(* Notations with explicit exceptional postcondition.
   The exception postcondition comes before the return postcondition
   so the parser can distinguish from the short form. *)

Notation "'EWP' e ⟨⟨ ζ ⟩⟩ {{ Φ } }" :=
  (impure ⊤ e%E ⊥ ζ%I Φ%I)
    (at level 0, e, Φ, ζ at level 200,
      format "'[' 'EWP'  e  '/' '[ '  ⟨⟨  ζ  ⟩⟩  {{  Φ  } } ']' ']'")
    : bi_scope.

Notation "'EWP' e @ E ⟨⟨ ζ ⟩⟩ {{ Φ } }" :=
  (impure E e%E ⊥ ζ%I Φ%I)
    (at level 0, e, Φ, ζ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  ⟨⟨  ζ  ⟩⟩  {{  Φ  } } ']' ']'")
    : bi_scope.

Notation "'EWP' e <| Ψ '|>' ⟨⟨ ζ ⟩⟩ {{ Φ } }" :=
  (impure ⊤ e%E Ψ%I ζ%I Φ%I)
    (at level 0, e, Ψ, Φ, ζ at level 200,
      format "'[hv' 'EWP'  e  '/' <| Ψ '|>'  ⟨⟨  ζ  ⟩⟩  {{  '[' Φ  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E <| Ψ '|>' ⟨⟨ ζ ⟩⟩ {{ Φ } }" :=
  (impure E e%E Ψ%I ζ%I Φ%I)
    (at level 0, e, Ψ, Φ, ζ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  <|  Ψ  '|>'  ⟨⟨  ζ  ⟩⟩  {{  Φ  } } ']' ']'")
    : bi_scope.

(* Notations without exceptional postcondition (uses ⊥) *)

Notation "'EWP' e {{ Φ } }" :=
  (impure ⊤ e%E ⊥ (⊥ : exn → iProp _) Φ%I)
    (at level 0, e, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' {{  Φ  } } ']' ']'")
    : bi_scope.

Notation "'EWP' e @ E {{ Φ } }" :=
  (impure E e%E ⊥ (⊥ : exn → iProp _) Φ%I)
    (at level 0, e, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  {{  Φ  } } ']' ']'")
    : bi_scope.

Notation "'EWP' e <| Ψ '|>' {{ Φ } }" :=
  (impure ⊤ e%E Ψ%I (⊥ : exn → iProp _) Φ%I)
    (at level 0, e, Ψ, Φ at level 200,
      format "'[hv' 'EWP'  e  '/' <| Ψ '|>'  {{  '[' Φ  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E <| Ψ |> {{ Φ } }" :=
  (impure E e%E Ψ%I (⊥ : exn → iProp _) Φ%I)
    (at level 0, e, Ψ, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  <|  Ψ  '|>'  {{  Φ  } } ']' ']'")
    : bi_scope.

(* Notations taking the postconditions as a binder and a body, the analogue of
   Iris' [WP e {{ v, Q }}]. Either postcondition may be written in either style,
   so each of the four [@ E] / [<| Ψ |>] shapes comes in four flavours.

   These come after the predicate notations above, and printing picks the most
   recently declared match, so they are the ones used for printing. As in Iris,
   that means an opaque postcondition prints eta-expanded, as [{{ v, Φ v }}].

   The general approach for the formats: an outer '[hv' to switch between
   "horizontal mode" where it all fits on one line, and "vertical mode" where
   each '/' becomes a line break; then a nested box around each postcondition so
   that it stays maximally horizontal and suitably indented. *)

(* Binder on the return postcondition, exceptional postcondition given. *)

Notation "'EWP' e ⟨⟨ ζ ⟩⟩ {{ v , Q } }" :=
  (impure ⊤ e%E ⊥ ζ%I (λ v, Q%I))
    (at level 0, e, ζ, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' ⟨⟨  ζ  ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E ⟨⟨ ζ ⟩⟩ {{ v , Q } }" :=
  (impure E e%E ⊥ ζ%I (λ v, Q%I))
    (at level 0, e, ζ, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  ⟨⟨  ζ  ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e <| Ψ '|>' ⟨⟨ ζ ⟩⟩ {{ v , Q } }" :=
  (impure ⊤ e%E Ψ%I ζ%I (λ v, Q%I))
    (at level 0, e, Ψ, ζ, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' <|  Ψ  |>  ⟨⟨  ζ  ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E <| Ψ '|>' ⟨⟨ ζ ⟩⟩ {{ v , Q } }" :=
  (impure E e%E Ψ%I ζ%I (λ v, Q%I))
    (at level 0, e, Ψ, ζ, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  <|  Ψ  |>  ⟨⟨  ζ  ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

(* Binder on the exceptional postcondition only. *)

Notation "'EWP' e ⟨⟨ w , R ⟩⟩ {{ Φ } }" :=
  (impure ⊤ e%E ⊥ (λ w, R%I) Φ%I)
    (at level 0, e, R, Φ at level 200, w at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  Φ  } } ']'")
    : bi_scope.

Notation "'EWP' e @ E ⟨⟨ w , R ⟩⟩ {{ Φ } }" :=
  (impure E e%E ⊥ (λ w, R%I) Φ%I)
    (at level 0, e, R, Φ at level 200, w at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  Φ  } } ']'")
    : bi_scope.

Notation "'EWP' e <| Ψ '|>' ⟨⟨ w , R ⟩⟩ {{ Φ } }" :=
  (impure ⊤ e%E Ψ%I (λ w, R%I) Φ%I)
    (at level 0, e, Ψ, R, Φ at level 200, w at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' <|  Ψ  |>  ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  Φ  } } ']'")
    : bi_scope.

Notation "'EWP' e @ E <| Ψ '|>' ⟨⟨ w , R ⟩⟩ {{ Φ } }" :=
  (impure E e%E Ψ%I (λ w, R%I) Φ%I)
    (at level 0, e, Ψ, R, Φ at level 200, w at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  <|  Ψ  |>  ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  Φ  } } ']'")
    : bi_scope.

(* Binders on both postconditions. *)

Notation "'EWP' e ⟨⟨ w , R ⟩⟩ {{ v , Q } }" :=
  (impure ⊤ e%E ⊥ (λ w, R%I) (λ v, Q%I))
    (at level 0, e, R, Q at level 200,
     w at level 200 as pattern, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E ⟨⟨ w , R ⟩⟩ {{ v , Q } }" :=
  (impure E e%E ⊥ (λ w, R%I) (λ v, Q%I))
    (at level 0, e, R, Q at level 200,
     w at level 200 as pattern, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e <| Ψ '|>' ⟨⟨ w , R ⟩⟩ {{ v , Q } }" :=
  (impure ⊤ e%E Ψ%I (λ w, R%I) (λ v, Q%I))
    (at level 0, e, Ψ, R, Q at level 200,
     w at level 200 as pattern, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' <|  Ψ  |>  ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E <| Ψ '|>' ⟨⟨ w , R ⟩⟩ {{ v , Q } }" :=
  (impure E e%E Ψ%I (λ w, R%I) (λ v, Q%I))
    (at level 0, e, Ψ, R, Q at level 200,
     w at level 200 as pattern, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  <|  Ψ  |>  ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

(* Binder on the return postcondition, no exceptional postcondition.

   These must come last: for a computation whose exceptional postcondition is
   [⊥], the notations above also match (printing [⊥] eta-expanded as
   [⟨⟨ w, ⊥ w ⟩⟩]), and printing picks the most recently declared match. *)

Notation "'EWP' e {{ v , Q } }" :=
  (impure ⊤ e%E ⊥ (⊥ : exn → iProp _) (λ v, Q%I))
    (at level 0, e, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E {{ v , Q } }" :=
  (impure E e%E ⊥ (⊥ : exn → iProp _) (λ v, Q%I))
    (at level 0, e, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e <| Ψ '|>' {{ v , Q } }" :=
  (impure ⊤ e%E Ψ%I (⊥ : exn → iProp _) (λ v, Q%I))
    (at level 0, e, Ψ, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' <|  Ψ  |>  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E <| Ψ '|>' {{ v , Q } }" :=
  (impure E e%E Ψ%I (⊥ : exn → iProp _) (λ v, Q%I))
    (at level 0, e, Ψ, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  <|  Ψ  |>  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

(* Both binders are parsed [as pattern], so either postcondition may destructure
   its result directly: [{{ (x, y), Q }}], [⟨⟨ (i, j), R ⟩⟩]. Write the pattern
   without a leading [']: a quoted [{{ '(x, y), Q }}] would send the parser into
   stdpp's ["' x ← y ; z"] (monadic bind) rule and fail asking for [←]. This is
   also the form Rocq prints back, so the notation round-trips. *)

(* Texan triples for [EWP] are declared in [program_logic/triples.v]. *)

(* N.B. A slight hack to control the namespace of constructs that have the same
  name in [stdpp] and [osiris]. *)
From osiris.lang Require Export syntax.
From osiris.semantics Require Export code micro step.
