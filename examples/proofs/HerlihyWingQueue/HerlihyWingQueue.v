(******************************************************************************)
(*                                                                            *)
(*        The Herlihy-Wing queue is linearizable, as a FIFO queue             *)
(*                                                                            *)
(******************************************************************************)

(* Verification of [examples/src/HerlihyWingQueue.ml] against a FIFO
   specification: logically atomic triples for [enqueue] and [dequeue] against
   a shared abstract state [queue_content γ ls], where [ls : list val] is the
   contents of the queue, oldest element first.

     - [enqueue q x] appends [x] at the end;
     - [dequeue q] removes and returns the element at the front.

   This queue is the textbook example of a linearizable data structure whose
   operations have no fixed linearization point: [enqueue] has none. Which of
   two concurrent enqueues comes first in the queue is not determined by
   anything that has happened when they run -- it is determined by the order in
   which the queue will later hand the two elements out. The proof therefore
   reads that order off a prophecy, and an enqueue commits at whatever moment
   its position in the order becomes fixed, which may be before it has written
   anything at all.

   The development is split as follows:

     - [Ghost.v]     the resource algebras and their token lemmas;
     - [Blocks.v]    the prophecy abstraction and the block decomposition;
     - [Invariant.v] the invariant, and the machinery for committing a run of
                     pending enqueues on their behalf;
     - this file     the specifications and the operation proofs.

   It is a port of [logatom/herlihy_wing_queue/hwq.v] from Iris-examples. *)

From iris.algebra Require Import auth excl agree csum gmap numbers.
From iris.base_logic.lib Require Import invariants saved_prop proph_map.

From osiris.utils Require Import list_z big_opLZ.

From osiris Require Import osiris.
From osiris.program_logic Require Import atomic.
From osiris.stdlib.proofs Require Import array.
From osiris.examples Require Import og_HerlihyWingQueue.

Require Import Ghost Blocks Invariant.

Open Scope Z.

(* [osiris.stdlib.proofs.array] binds [map] to the OCaml [Array.map]
   expression, which would shadow the list [map] that the invariant is
   phrased with. *)
Local Abbreviation map := Corelib.Lists.ListDef.map.

(* The logical models of the two record shapes this module allocates, so that
   [imp_record] can be used at their allocation sites. *)
Record slot_fields : Type := mkSlotFields { slot_v : option val }.
Record queue_fields : Type :=
  mkQueueFields { queue_items : array; queue_proph : proph_id; queue_back : Z }.

Instance slot_fields_repr : RecordRepr slot_fields τ[option val] Mut :=
  { repr_to_types r := r.(slot_v);
    types_to_repr := λ o, {| slot_v := o |};
    repr_id := λ o, eq_refl }.

Instance queue_fields_repr : RecordRepr queue_fields τ[array; proph_id; Z] Mut :=
  { repr_to_types r := (r.(queue_items), (r.(queue_proph), r.(queue_back)));
    types_to_repr := λ a p b,
      {| queue_items := a; queue_proph := p; queue_back := b |};
    repr_id := λ '(a, (p, b)), eq_refl }.

Abbreviation v_field := 0%Z (only parsing).
Abbreviation items_field := 0%Z (only parsing).
Abbreviation proph_field := 1%Z (only parsing).
Abbreviation back_field := 2%Z (only parsing).

(* ------------------------------------------------------------------------ *)
(** ** Pattern matching on a slot's contents

    The pure pattern engine has no built-in case for a general constructor
    pattern, so each development registers the ones it needs through
    [pattern_hook]. The only constructor patterns here are the [Some x] and
    [None] of a slot's ['a option] contents. *)

Ltac solve_data_shape :=
  first [ reflexivity | solve [ encode ] | symmetry; solve [ encode ] ].

Ltac pattern_hook ::=
  first
    [ eapply (pat_PData_neq _ _ _ _ _ _ _ (λ _ : env, False));
        [ solve_data_shape | congruence ]
    | eapply pat_PData_eq; [ solve_data_shape | ] ].

Ltac skip_branch :=
  iApply deep_handle_cons_iris'; iApply icpat_CVal; iApply ipattern_pure_cps;
  [ eapply (pat_PData_neq _ _ _ _ _ _ _ (λ _ : env, False));
      [ solve_data_shape | congruence ]
  | iSplit; [ iIntros (?) "%Hfalse"; done | iIntros "_" ] ].

(* ------------------------------------------------------------------------ *)

Section HerlihyWingQueue.

Context `{!osirisGS Σ, !hwqG Σ, !savedPropG Σ, !inG Σ (authR natUR)}.

(* The queue allocates a three-field record and one-field slots. *)
Hypothesis Hmax3 : 3 ≤ max_array_length.

(* ---------------------------------------------------------------------- *)
(** ** [create] *)

Definition create_spec create : iProp Σ :=
  {{ ⌜0 < cap ≤ max_array_length⌝ }}
  create cap : Z
  {{ RET (q : queue); ∃ γ, is_queue γ cap q ∗ queue_content γ [] ∗
                             enqueue_permit γ (Z.to_nat cap) }}.

Lemma create_proof η :
  path_spec ["Array"; "init"] init_spec' η -∗
  EWP (eval η (EAnonFun __create)) {{ create_spec }}.
Proof.
  iIntros "#HArray".
  unfold create_spec.
  iApply imp_EAnon_pers.
  iIntros "!>" (cap).
  iIntros "%Hcap".
  iApply imp_please; iNext.

  (* [let items = Array.init capacity (fun _ -> { v = None }) in ...] *)
  imp_let $! (λ a : array, ∃ ss : list slot, ⌜list_z.length ss = cap⌝ ∗
                             a ↦∗ ss ∗
                             [∗ listZ] k ↦ s ∈ ss, slot_pointsto s None)%I.
  { imp_app τ[Z; val].
    { iApply (imp_EAnon_pers τ[Z]
                (λ (i : Z) m, ⌜0 ≤ i < cap⌝ -∗
                              EWP m {{ (s : slot), slot_pointsto s None }})%I).
      iIntros "!>" (i) "_".
      iApply imp_please; iNext.
      imp_match.
      iApply (imp_wand with "[]"); [ imp_record | ].
      iIntros (s) "H /=".
      iDestruct "H" as (o) "[Hs ->]".
      rewrite /ownRecord /ownBlock /=.
      iDestruct "Hs" as (ls) "(#Hlocs & _ & Hxs)".
      iDestruct (big_sepLZ2_cons_inv_r with "Hxs") as (l ls') "(-> & Hl & Hxs)".
      iDestruct (big_sepLZ2_nil_inv_r with "Hxs") as %->.
      iExists l. by iFrame "Hlocs Hl". }
    iIntros "#Hf Hinit".
    iApply ("Hinit" $! slot _ _ (λ _ s, slot_pointsto s None)%I with "[$Hf]").
    iPureIntro; lia. }

  (* [let proph = Proph.create () in ...]: the queue's prophecy. *)
  iIntros (a) "(%ss & %Hlen & Harr & Hslots)".
  iApply (imp_ELet_var (λ p : proph_id, ∃ pvs, proph p pvs)%I with "[]").
  { iApply imp_ENewProph. iIntros "!>" (p pvs) "Hp". by iExists pvs. }
  iIntros (p) "[%pvs Hproph]".

  (* [{ items; proph; back = 0 }]. *)
  iApply imp_fupd.
  iApply (imp_wand with "[]"); [ imp_record | ].  iIntros (q) "H /=".
  iDestruct "H" as (a' p' b') "(Hq & -> & -> & ->)".

  (* Split the fresh record: [items] and [proph] are never written again, so
     their points-to are discarded here and shared; [back] goes to the
     invariant. The array itself is likewise frozen. *)
  rewrite /ownRecord /ownBlock /=.
  iDestruct "Hq" as (lls) "(#Hqlocs & _ & Hxs)".
  iDestruct (big_sepLZ2_cons_inv_r with "Hxs") as (ql ls1) "(-> & Hql & Hxs)".
  iDestruct (big_sepLZ2_cons_inv_r with "Hxs") as (pl ls2) "(-> & Hpl & Hxs)".
  iDestruct (big_sepLZ2_cons_inv_r with "Hxs") as (bl ls3) "(-> & Hbl & Hxs)".
  iDestruct (big_sepLZ2_nil_inv_r with "Hxs") as %->.
  iMod (gen_heap.pointsto_persist with "Hql") as "#Hql".
  iMod (gen_heap.pointsto_persist with "Hpl") as "#Hpl".
  iDestruct (ownArray_isSlice with "Harr") as "Hsl".
  iMod (isSlice_persist with "Hsl") as "#Hsl".
  iDestruct (slots_at_intro with "Hslots") as "[#Hats Hslots]".

  (* Ghost state. *)
  iMod (new_elts (Σ:=Σ) []) as (γel) "[Hel● Hel◯]".
  iMod (new_back (Σ:=Σ)) as (γbk) "Hbk".
  iMod (new_back (Σ:=Σ)) as (γi2) "Hi2".
  iMod (new_no_contra (Σ:=Σ)) as (γct) "Hct".
  iMod (new_slots (Σ:=Σ)) as (γsl) "Hsl●".
  iMod (own_alloc (● (Z.to_nat cap) ⋅ ◯ (Z.to_nat cap))) as (γcp) "[Hcpa Hcpf]".
  { by apply auth_both_valid_discrete. }
  iMod (own_unit (authUR natUR) γcp) as "Hzero".

  set (γ := HwqNames γbk γi2 γel γct γsl γcp).
  set (bs := map (λ i : Z, (i, @nil Z)) (take_slots cap ∅ pvs) : blocks).

  iMod (inv_alloc hwqN _ (hwq_inv_inner γ cap ss bl p)
          with "[Hbl Hproph Hslots Hbk Hi2 Hct Hsl● Hel● Hcpa Hzero]") as "#Hinv".
  { iNext. iExists 0, (take_slots cap ∅ pvs), [], [], (NoCont bs), ∅, ∅.
    rewrite /= fmap_empty big_sepM_empty.
    iFrame "Hbl Hbk Hcpa Hel● Hsl● Hct".
    iSplitL "Hslots".
    { iApply (big_sepLZ_impl with "Hslots").
      iIntros "!>" (k s _) "Hs". by rewrite array_get_empty. }
    rewrite /i2_lower_bound /=. iFrame "Hzero Hi2".
    iSplitL "Hproph"; first (iExists pvs; by iFrame).
    iPureIntro. rewrite /hwq_pure. split_and!.
    - lia.
    - lia.
    - intros i. rewrite lookup_empty. split; [ lia | by intros [? ?] ].
    - intros i. rewrite lookup_empty /=. split; [ done | by intros ? ].
    - intros i Hi. by inversion Hi.
    - intros i Hi. by inversion Hi.
    - rewrite elements_empty app_nil_r.
      specialize (take_data_NoDup cap ∅ pvs) as H.
      by apply NoDup_app in H as (H & _ & _).
    - intros i Hi. by eapply take_data_bound.
    - intros b Hb. by eapply initial_block_valid.
    - done.
    - apply flatten_blocks_initial. }

  iModIntro. iExists γ.
  rewrite /queue_content /enqueue_permit /=.
  iFrame "Hel◯ Hcpf".
  iExists ql, pl, bl, a, ss, p.
  iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro; lia | ].
  by iFrame "Hqlocs Hql Hpl Hsl Hats Hinv".
Qed.

(* ---------------------------------------------------------------------- *)
(** ** [enqueue] *)

(* [enqueue q x] appends [x]. There is no linearization point in the code:
   the atomic update is either run by this call, at its own exchange, or
   handed over to a dequeuer that has to overtake it and is run there. Which
   of the two happens is decided by the prophecy at the fetch-and-add. *)
Definition enqueue_spec (q : queue) (x : val) (m : microvx) : iProp Σ :=
  ∀ γ (cap : Z),
  is_queue γ cap q -∗
  enqueue_permit γ 1 -∗
  <<{ ∀∀ ls : list val, queue_content γ ls }>>
    m @ ↑hwqN
  <<{ queue_content γ (ls ++ [x]) | RET () }>>.

(* What an [enqueue] carries away from its fetch-and-add.

   The fetch-and-add is where the prophecy is consulted, and where the call's
   fate is decided. Either the prediction says this call's element comes out
   before every element still in flight, in which case the call commits right
   there and keeps its postcondition; or it does not, in which case the call
   registers itself as pending: it hands its atomic update to the invariant,
   for a dequeuer to run on its behalf, and keeps only the name of the saved
   proposition standing for its postcondition.

   [slot_writing_tok] is the exclusive right to fill slot [i], spent at the
   exchange. *)
Definition enq_state γ (i : Z) (x : val) (P : iProp Σ) : iProp Σ :=
  (slot_val_wit γ.(hwq_sl) i x ∗
   slot_writing_tok γ.(hwq_sl) i ∗
   ((* committed already *)
    (slot_committed_wit γ.(hwq_sl) i ∗ P)
    ∨ (* pending: the atomic update is in the invariant *)
    (∃ g, slot_token γ.(hwq_sl) i ∗ slot_name_tok γ.(hwq_sl) i g ∗
          saved_prop_own g DfracDiscarded P)))%I.

Lemma enqueue_proof η :
  ⊢ EWP (eval η (EAnonFun __enqueue))
      {{ c, □ iSpec τ[queue; val] c enqueue_spec }}.
Proof.
  iApply (imp_EAnon_pers τ[queue; val]).
  iIntros "!>" (q x).
  unfold enqueue_spec.
  iIntros (γ cap) "#Hq Hpermit". iIntros (Φ) "AU".
  iDestruct "Hq" as (ql pl bl a ss p)
    "(%Hlen & %Hcap & #Hqlocs & #Hql & #Hpl & #Hsl & #Hats & #Hinv)".
  iApply imp_please; iNext.

  (* [let i = Atomic.Loc.fetch_and_add [%atomic.loc q.back] 1 in ...]

     This claims slot [i], and consults the prophecy. *)
  iApply (imp_ELet_var
            (λ i : Z, ⌜0 ≤ i < cap⌝ ∗ enq_state γ i x (Φ ()))%I
            with "[Hpermit AU]").
  { iApply (imp_faa_atomic (⊤ ∖ ↑hwqN) ⊤ _ _ _
              (λ l : loc, ⌜l = bl⌝)%I (λ j : Z, ⌜j = 1⌝)%I
              with "[] [] [Hpermit AU]").
    { iApply (imp_EAtomicLoc back_field q [ql; pl; bl] with "Hqlocs [] []").
      { list_z.length; lia. }
      { imp_path. }
      { iNext. iPureIntro. by vm_compute. } }
    { imp_step. }
    iNext.
    iInv "Hinv" as "(%back & %pvs & %pref & %rest & %cont & %slots & %deqs &
                     >Hbl & Hslots & >Hbk & >Hcpa & >Hcpf & >Hi2 & >Hel & >Hsl● &
                     >Hproph & Hbig & >Hcont & >%Hpure)" "Hclose".
    iDestruct (capacity_bound with "Hcpa Hcpf Hpermit") as %Hcp.
    iModIntro. iIntros (l j) "-> ->".
    iExists back. iFrame "Hbl". iIntros "!> Hbl".
    destruct Hpure as ((Hback0 & Hbackcap) & Hslots_dom & Hstate & Hpref
                       & Hdeqs & (Hpvs_ND & Hpvs_cap) & Hcs).
    (* The permit bounds [back]: slot [back] exists and is free. *)
    assert (Hi_cap : back < cap) by lia.
    assert (Hi_free : slots !! back = None).
    { destruct (slots !! back) as [d|] eqn:HE; last done.
      exfalso. assert (Hs : is_Some (slots !! back)) by eauto.
      apply Hslots_dom in Hs. lia. }
    assert (Hi_not_deq : back ∉ deqs).
    { intros HD. specialize (Hdeqs back HD) as (HH & _).
      rewrite Hi_free in HH. by inversion HH. }
    (* [back] grows by one; the enqueue permit is spent. *)
    iMod (back_incr with "Hbk") as "Hbk".
    iEval (rewrite -Nat.add_1_r) in "Hbk".
    iCombine "Hcpf Hpermit" as "Hcpf".

    (* The four cases. In the first three the call commits at once; in the
       last it registers itself as pending. *)
    destruct cont as [i1 i2|bs].

    { (* A contradiction is already on record: nothing is predicted any more,
         so the element simply goes at the end. *)
      iDestruct "Hcont" as "#Hct".
      iMod "AU" as (ls) "[Hc [_ Hcommit]]".
      iDestruct (sync_elts with "Hel Hc") as %<-.
      iMod (update_elts _ _ _ (map (get_value slots deqs) pref ++ (rest ++ [x]))
              with "Hel Hc") as "[Hel Hc]".
      iMod ("Hcommit" with "[Hc]") as "HΦ".
      { rewrite app_assoc. iExact "Hc". }
      iMod (alloc_done_slot γ.(hwq_sl) slots back x Hi_free with "Hsl●")
        as "[Hsl● (Htok & #Hvw & #Hcw & Hwt)]".
      iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hproph Hbig
                            Htok]") as "_".
      { iNext.
        iExists (back + 1), pvs, pref, (rest ++ [x]), (WithCont i1 i2),
                (<[back := (x, Done, false)]> slots), deqs.
        replace (Z.to_nat (back + 1)) with (Z.to_nat back + 1)%nat by lia.
        rewrite fmap_insert.
        iFrame "Hbl Hbk Hcpa Hcpf Hi2 Hsl● Hproph Hct".
        iSplitL "Hslots".
        { iApply (big_sepLZ_impl with "Hslots").
          iIntros "!>" (k s _) "Hs".
          destruct (decide (k = back)) as [->|Hne].
          { by rewrite array_get_insert_fresh. }
          by rewrite array_get_insert_ne. }
        iSplitL "Hel".
        { assert (Hnb : back ∉ pref).
          { intros Hin. specialize (Hpref back Hin) as (HH & _).
            rewrite Hi_free in HH. by inversion HH. }
          rewrite (map_get_value_not_in_pref back (x, Done, false) pref slots
                     deqs eq_refl Hnb).
          rewrite app_assoc. iExact "Hel". }
        iSplitL "Hbig Htok".
        { iApply big_sepM_insert; first done.
          iFrame "Hbig". rewrite /per_slot_own /=. by iFrame "Hvw Hcw Htok". }
        iPureIntro. rewrite /hwq_pure.
        destruct Hcs as ((HB1 & (HB2 & HB3) & HB4) & HC2 & HC3 & HC4 & HC5
                         & HC6).
        assert (Hne1 : back ≠ i1) by lia.
        assert (Hdom' : ∀ k, 0 ≤ k < back + 1
                             ↔ is_Some (<[back:=(x, Done, false)]> slots !! k)).
        { intros k. destruct (decide (back = k)) as [->|Hne].
          - rewrite lookup_insert_eq.
            split; [ intros _; by eexists | intros _; lia ].
          - rewrite (lookup_insert_ne _ _ _ _ Hne) -Hslots_dom.
            split; intros; lia. }
        assert (Hstate' : ∀ k,
          (was_committed <$> <[back:=(x, Done, false)]> slots !! k = Some false
           → was_written <$> <[back:=(x, Done, false)]> slots !! k = Some false)
          ∧ (was_written <$> <[back:=(x, Done, false)]> slots !! k = Some false
             → k ∉ deqs)).
        { intros k. destruct (decide (back = k)) as [->|Hne].
          - rewrite lookup_insert_eq /=.
            split; [ intros HH; by inversion HH | intros _; exact Hi_not_deq ].
          - rewrite (lookup_insert_ne _ _ _ _ Hne). apply Hstate. }
        assert (Hpref' : ∀ k, k ∈ pref →
          was_committed <$> <[back:=(x, Done, false)]> slots !! k = Some true
          ∧ (k ∉ deqs) ∧ k ≠ i1).
        { intros k Hk. destruct (decide (back = k)) as [->|Hne].
          - exfalso. specialize (Hpref k Hk) as (HH & _).
            rewrite Hi_free in HH. by inversion HH.
          - rewrite (lookup_insert_ne _ _ _ _ Hne). by apply Hpref. }
        assert (Hdeqs' : ∀ k, k ∈ deqs →
          was_written <$> <[back:=(x, Done, false)]> slots !! k = Some true
          ∧ was_committed <$> <[back:=(x, Done, false)]> slots !! k = Some true
          ∧ array_get (<[back:=(x, Done, false)]> slots) deqs k = None).
        { intros k Hk. assert (Hne : back ≠ k).
          { intros ->. by apply Hi_not_deq. }
          rewrite (lookup_insert_ne _ _ _ _ Hne)
                  (array_get_insert_ne _ _ _ _ _ Hne).
          by apply Hdeqs. }
        split_and!;
          [ lia | lia | exact Hdom' | exact Hstate' | exact Hpref'
          | exact Hdeqs' | exact Hpvs_ND | exact Hpvs_cap
          | lia | lia | lia | lia
          | by rewrite (lookup_insert_ne _ _ _ _ Hne1)
          | by rewrite (lookup_insert_ne _ _ _ _ Hne1)
          | exact HC4
          | by rewrite (array_get_insert_ne _ _ _ _ _ Hne1)
          | exact HC6 ]. }
      iModIntro. iSplitR; first by iPureIntro; lia.
      rewrite /enq_state. iFrame "Hvw Hwt". iLeft. by iFrame "Hcw HΦ". }

    { (* No contradiction. The prediction is a list of blocks. *)
      destruct Hcs as (Hbv & Hrest & Hpvs).
      iMod (i2_lower_bound_update _ _ (Z.to_nat (back + 1)) with "Hi2")
        as "Hi2"; first lia.
      destruct bs as [|[b_u b_ps] bs].

      { (* The prediction is exhausted: nothing is claimed about the future,
           so the element simply goes at the end. *)
        iMod "AU" as (ls) "[Hc [_ Hcommit]]".
        iDestruct (sync_elts with "Hel Hc") as %<-.
        iMod (update_elts _ _ _
                (map (get_value slots deqs) pref ++ (rest ++ [x]))
                with "Hel Hc") as "[Hel Hc]".
        iMod ("Hcommit" with "[Hc]") as "HΦ".
        { rewrite app_assoc. iExact "Hc". }
        iMod (alloc_done_slot γ.(hwq_sl) slots back x Hi_free with "Hsl●")
          as "[Hsl● (Htok & #Hvw & #Hcw & Hwt)]".
        iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hproph Hbig
                              Htok Hcont]") as "_".
        { iNext.
          iExists (back + 1), pvs, pref, (rest ++ [x]), (NoCont []),
                  (<[back := (x, Done, false)]> slots), deqs.
          replace (Z.to_nat (back + 1)) with (Z.to_nat back + 1)%nat by lia.
          rewrite fmap_insert.
          iFrame "Hbl Hbk Hcpa Hcpf Hi2 Hsl● Hproph Hcont".
          iSplitL "Hslots".
          { iApply (big_sepLZ_impl with "Hslots").
            iIntros "!>" (k s _) "Hs".
            destruct (decide (k = back)) as [->|Hne].
            { by rewrite array_get_insert_fresh. }
            by rewrite array_get_insert_ne. }
          iSplitL "Hel".
          { assert (Hnb : back ∉ pref).
            { intros Hin. specialize (Hpref back Hin) as (HH & _).
              rewrite Hi_free in HH. by inversion HH. }
            rewrite (map_get_value_not_in_pref back (x, Done, false) pref slots
                       deqs eq_refl Hnb).
            rewrite app_assoc. iExact "Hel". }
          iSplitL "Hbig Htok".
          { iApply big_sepM_insert; first done.
            iFrame "Hbig". rewrite /per_slot_own /=. by iFrame "Hvw Hcw Htok". }
          iPureIntro. rewrite /hwq_pure.
          assert (Hdom' : ∀ k, 0 ≤ k < back + 1
                          ↔ is_Some (<[back:=(x, Done, false)]> slots !! k)).
          { intros k. destruct (decide (back = k)) as [->|Hne].
            - rewrite lookup_insert_eq.
              split; [ intros _; by eexists | intros _; lia ].
            - rewrite (lookup_insert_ne _ _ _ _ Hne) -Hslots_dom.
              split; intros; lia. }
          assert (Hstate' : ∀ k,
            (was_committed <$> <[back:=(x, Done, false)]> slots !! k
               = Some false
             → was_written <$> <[back:=(x, Done, false)]> slots !! k
               = Some false)
            ∧ (was_written <$> <[back:=(x, Done, false)]> slots !! k
               = Some false → k ∉ deqs)).
          { intros k. destruct (decide (back = k)) as [->|Hne].
            - rewrite lookup_insert_eq /=.
              split; [ intros HH; by inversion HH | intros _; exact Hi_not_deq ].
            - rewrite (lookup_insert_ne _ _ _ _ Hne). apply Hstate. }
          assert (Hpref' : ∀ k, k ∈ pref →
            was_committed <$> <[back:=(x, Done, false)]> slots !! k = Some true
            ∧ (k ∉ deqs) ∧ True).
          { intros k Hk. destruct (decide (back = k)) as [->|Hne].
            - exfalso. specialize (Hpref k Hk) as (HH & _).
              rewrite Hi_free in HH. by inversion HH.
            - rewrite (lookup_insert_ne _ _ _ _ Hne).
              specialize (Hpref k Hk) as (H1 & H2 & _). by split_and!. }
          assert (Hdeqs' : ∀ k, k ∈ deqs →
            was_written <$> <[back:=(x, Done, false)]> slots !! k = Some true
            ∧ was_committed <$> <[back:=(x, Done, false)]> slots !! k
              = Some true
            ∧ array_get (<[back:=(x, Done, false)]> slots) deqs k = None).
          { intros k Hk. assert (Hne : back ≠ k).
            { intros ->. by apply Hi_not_deq. }
            rewrite (lookup_insert_ne _ _ _ _ Hne)
                    (array_get_insert_ne _ _ _ _ _ Hne).
            by apply Hdeqs. }
          split_and!;
            [ lia | lia | exact Hdom' | exact Hstate' | exact Hpref'
            | exact Hdeqs' | exact Hpvs_ND | exact Hpvs_cap
            | intros b Hb; by inversion Hb
            | by intros HH
            | exact Hpvs ]. }
        iModIntro. iSplitR; first by iPureIntro; lia.
        rewrite /enq_state. iFrame "Hvw Hwt". iLeft. by iFrame "Hcw HΦ". }

      (* The prediction is non-trivial: it says which slots come out next,
         grouped into blocks. *)
      assert (Hrest0 : rest = []) by (apply Hrest; done). subst rest.
      assert (Hdisj : ∀ k, k ∈ pref → k ∉ b_u :: (b_ps ++ flatten_blocks bs)).
      { apply NoDup_app in Hpvs_ND as (HH & _ & _). rewrite Hpvs in HH.
        by apply NoDup_app in HH as (_ & HH & _). }
      assert (HND : NoDup (b_u :: b_ps ++ flatten_blocks bs)).
      { apply NoDup_app in Hpvs_ND as (HH & _ & _). rewrite Hpvs in HH.
        by apply NoDup_app in HH as (_ & _ & HH). }
      assert (Hnb : back ∉ pref).
      { intros Hin. specialize (Hpref back Hin) as (HH & _).
        rewrite Hi_free in HH. by inversion HH. }
      destruct (decide (b_u = back)) as [->|Hbu].

      { (* Our slot heads the next block. The prediction says this call's
           element comes out before every element still in flight, so this
           call commits here -- and so does every pending enqueue in its
           block, in slot order. *)
        assert (Hbvi : block_valid slots (back, b_ps))
          by (apply Hbv, list_elem_of_here).
        destruct Hbvi as (_ & Hbv2). simpl in Hbv2.
        apply NoDup_cons in HND as (Hnotin & HND').
        assert (Hnotin_back : back ∉ b_ps).
        { intros HH. apply Hnotin, elem_of_app. by left. }
        assert (HNDps : NoDup b_ps)
          by (by apply NoDup_app in HND' as (HH & _ & _)).
        assert (Hps_ne : ∀ k, k ∈ b_ps → back ≠ k).
        { intros k Hk ->. apply Hnotin, elem_of_app. by left. }
        assert (Hps_Some : ∀ k, k ∈ b_ps →
                  is_Some (<[back := (x, Done, false)]> slots !! k)).
        { intros k Hk. rewrite lookup_insert_ne; last by apply Hps_ne.
          specialize (Hbv2 k Hk).
          destruct (slots !! k) as [d|]; [ by eexists | by inversion Hbv2 ]. }

        (* Allocate our slot, already committed. *)
        iMod (alloc_done_slot γ.(hwq_sl) slots back x Hi_free with "Hsl●")
          as "[Hsl● (Htok & #Hvw & #Hcw & Hwt)]".
        (* Run our own atomic update. *)
        iMod "AU" as (ls) "[Hc [_ Hcommit]]".
        iDestruct (sync_elts with "Hel Hc") as %<-.
        iMod (update_elts _ _ _ (map (get_value slots deqs) pref ++ [x])
                with "Hel Hc") as "[Hel Hc]".
        iMod ("Hcommit" with "[Hc]") as "HΦ"; first by rewrite app_nil_r.
        (* Register our slot, then run the whole block's atomic updates. *)
        iDestruct (big_sepM_insert (per_slot_own γ) slots back (x, Done, false)
                     with "[Htok Hbig]") as "Hbig"; first done.
        { iFrame "Hbig". rewrite /per_slot_own /=. by iFrame "Hvw Hcw Htok". }
        iMod (big_lemma γ (map (get_value slots deqs) pref ++ [x])
                (<[back := (x, Done, false)]> slots) b_ps HNDps
                with "Hsl● Hbig Hel") as "(Hsl● & Hbig & Hel)".
        { intros k Hk. rewrite lookup_insert_ne; last by apply Hps_ne.
          by apply Hbv2. }

        iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hproph Hbig
                              Hcont]") as "_".
        { iNext.
          iExists (back + 1), pvs, (pref ++ back :: b_ps), [], (NoCont bs),
                  (map_imap (helped b_ps) (<[back := (x, Done, false)]> slots)),
                  deqs.
          replace (Z.to_nat (back + 1)) with (Z.to_nat back + 1)%nat by lia.
          iFrame "Hbl Hbk Hcpa Hcpf Hi2 Hsl● Hproph Hbig Hcont".
          iSplitL "Hslots".
          { iApply (big_sepLZ_impl with "Hslots").
            iIntros "!>" (k s _) "Hs". rewrite array_get_helped.
            destruct (decide (k = back)) as [->|Hne].
            { by rewrite array_get_insert_fresh. }
            by rewrite array_get_insert_ne. }
          iSplitL "Hel".
          { rewrite app_nil_r map_get_value_helped map_app map_cons.
            rewrite (map_get_value_not_in_pref back (x, Done, false) pref slots
                       deqs eq_refl Hnb).
            rewrite (get_value_insert_eq slots deqs back (x, Done, false)) /=.
            rewrite -(get_values_map _ deqs b_ps Hps_Some).
            iEval (rewrite -app_assoc) in "Hel". iExact "Hel". }
          iPureIntro. rewrite /hwq_pure.
          assert (Hins_dom : ∀ k, 0 ≤ k < back + 1
                        ↔ is_Some (<[back:=(x, Done, false)]> slots !! k)).
          { intros k. destruct (decide (back = k)) as [->|Hne].
            - rewrite lookup_insert_eq.
              split; [ intros _; by eexists | intros _; lia ].
            - rewrite (lookup_insert_ne _ _ _ _ Hne) -Hslots_dom.
              split; intros; lia. }
          assert (Hins_state : ∀ k,
            (was_committed <$> <[back:=(x, Done, false)]> slots !! k
               = Some false
             → was_written <$> <[back:=(x, Done, false)]> slots !! k
               = Some false)
            ∧ (was_written <$> <[back:=(x, Done, false)]> slots !! k
               = Some false → k ∉ deqs)).
          { intros k. destruct (decide (back = k)) as [->|Hne].
            - rewrite lookup_insert_eq /=.
              split; [ intros HH; by inversion HH | intros _; exact Hi_not_deq ].
            - rewrite (lookup_insert_ne _ _ _ _ Hne). apply Hstate. }
          split_and!.
          - lia.
          - lia.
          - intros k. by rewrite helped_is_Some.
          - intros k. rewrite !was_written_helped. split.
            + intros HH%was_committed_helped. by apply Hins_state.
            + apply Hins_state.
          - intros k Hk. apply elem_of_app in Hk as [Hk|Hk].
            + (* an index already committed *)
              specialize (Hdisj k Hk) as Hk'.
              assert (Hk1 : k ≠ back) by set_solver.
              assert (Hk2 : k ∉ b_ps) by set_solver.
              rewrite (helped_not_in _ _ _ Hk2)
                      (lookup_insert_ne _ _ _ _ (λ H, Hk1 (eq_sym H))).
              specialize (Hpref k Hk) as (H1 & H2 & _). by split_and!.
            + apply elem_of_cons in Hk as [->|Hk].
              * rewrite (helped_not_in _ _ _ Hnotin_back) lookup_insert_eq.
                by split_and!.
              * rewrite (was_committed_helped_in _ _ _ Hk (Hps_Some _ Hk)).
                split_and!; try done.
                apply Hins_state, Hins_state.
                rewrite lookup_insert_ne; last by apply Hps_ne.
                by apply Hbv2.
          - intros k Hk.
            assert (Hk2 : k ∉ b_ps).
            { intros Hin. specialize (Hbv2 k Hin) as HH.
              apply Hstate in HH. apply Hstate in HH. done. }
            assert (Hk1 : back ≠ k).
            { intros ->. by apply Hi_not_deq. }
            rewrite array_get_helped (helped_not_in _ _ _ Hk2)
                    (lookup_insert_ne _ _ _ _ Hk1)
                    (array_get_insert_ne _ _ _ _ _ Hk1).
            by apply Hdeqs.
          - exact Hpvs_ND.
          - exact Hpvs_cap.
          - intros b Hb. destruct b as [b1 b2].
            assert (Hbfl1 : b1 ∈ flatten_blocks bs)
              by (by apply (flatten_blocks_mem1 bs (b1, b2) Hb)).
            assert (Hb1' : b1 ∉ b_ps).
            { intros Hin. apply NoDup_app in HND' as (_ & HH & _).
              by apply (HH b1 Hin). }
            assert (Hb1'' : back ≠ b1).
            { intros ->. apply Hnotin, elem_of_app. by right. }
            specialize (Hbv (b1, b2) (list_elem_of_further _ _ _ Hb))
              as (Hv1 & Hv2). simpl in Hv1, Hv2.
            split; simpl.
            + by rewrite (helped_not_in _ _ _ Hb1')
                         (lookup_insert_ne _ _ _ _ Hb1'').
            + intros j Hj. simpl in Hj.
              assert (Hjfl : j ∈ flatten_blocks bs)
                by (by apply (flatten_blocks_mem2 bs (b1, b2) Hb j Hj)).
              assert (Hj1' : j ∉ b_ps).
              { intros Hin. apply NoDup_app in HND' as (_ & HH & _).
                by apply (HH j Hin). }
              assert (Hj1'' : back ≠ j).
              { intros ->. apply Hnotin, elem_of_app. by right. }
              rewrite (helped_not_in _ _ _ Hj1')
                      (lookup_insert_ne _ _ _ _ Hj1'').
              by apply Hv2.
          - by intros _.
          - rewrite Hpvs /=. by rewrite -app_assoc. }
        iModIntro. iSplitR; first by iPureIntro; lia.
        rewrite /enq_state. iFrame "Hvw Hwt". iLeft. by iFrame "Hcw HΦ". }

      { (* Our slot does not head the next block. The prediction says some
           other element comes out first, so this call cannot commit yet: it
           joins the block ahead of it as a pending enqueue, handing its
           atomic update to the invariant for a dequeuer to run. *)
        iMod (saved_prop_alloc (Φ ()) DfracDiscarded) as (g) "#Hsaved"; first done.
        iMod (alloc_pend_slot γ.(hwq_sl) slots back x g Hi_free with "Hsl●")
          as "[Hsl● (Htok & #Hvw & Hpend & Hname & Hwt)]".
        iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hproph Hbig
                              Hpend Hcont AU]") as "_".
        { iNext.
          iExists (back + 1), pvs, pref, [],
                  (NoCont (glue_blocks (b_u, b_ps) back bs)),
                  (<[back := (x, Pend g, false)]> slots), deqs.
          replace (Z.to_nat (back + 1)) with (Z.to_nat back + 1)%nat by lia.
          rewrite fmap_insert.
          iFrame "Hbl Hbk Hcpa Hcpf Hi2 Hsl● Hproph Hcont".
          iSplitL "Hslots".
          { iApply (big_sepLZ_impl with "Hslots").
            iIntros "!>" (k s _) "Hs".
            destruct (decide (k = back)) as [->|Hne].
            { by rewrite array_get_insert_fresh. }
            by rewrite array_get_insert_ne. }
          iSplitL "Hel".
          { by rewrite (map_get_value_not_in_pref back (x, Pend g, false) pref
                          slots deqs eq_refl Hnb). }
          iSplitL "Hbig Hpend AU".
          { iApply big_sepM_insert; first done.
            iFrame "Hbig". rewrite /per_slot_own /=. iFrame "Hvw Hpend".
            iExists (Φ ()). iFrame "Hsaved". iExact "AU". }
          iPureIntro. rewrite /hwq_pure.
          assert (Hdom' : ∀ k, 0 ≤ k < back + 1
                          ↔ is_Some (<[back:=(x, Pend g, false)]> slots !! k)).
          { intros k. destruct (decide (back = k)) as [->|Hne].
            - rewrite lookup_insert_eq.
              split; [ intros _; by eexists | intros _; lia ].
            - rewrite (lookup_insert_ne _ _ _ _ Hne) -Hslots_dom.
              split; intros; lia. }
          assert (Hstate' : ∀ k,
            (was_committed <$> <[back:=(x, Pend g, false)]> slots !! k
               = Some false
             → was_written <$> <[back:=(x, Pend g, false)]> slots !! k
               = Some false)
            ∧ (was_written <$> <[back:=(x, Pend g, false)]> slots !! k
               = Some false → k ∉ deqs)).
          { intros k. destruct (decide (back = k)) as [->|Hne].
            - rewrite lookup_insert_eq /=.
              split; [ by intros _ | intros _; exact Hi_not_deq ].
            - rewrite (lookup_insert_ne _ _ _ _ Hne). apply Hstate. }
          assert (Hpref' : ∀ k, k ∈ pref →
            was_committed <$> <[back:=(x, Pend g, false)]> slots !! k
              = Some true
            ∧ (k ∉ deqs) ∧ True).
          { intros k Hk. assert (Hne : back ≠ k) by (intros ->; by apply Hnb).
            rewrite (lookup_insert_ne _ _ _ _ Hne).
            specialize (Hpref k Hk) as (H1 & H2 & _). by split_and!. }
          assert (Hdeqs' : ∀ k, k ∈ deqs →
            was_written <$> <[back:=(x, Pend g, false)]> slots !! k = Some true
            ∧ was_committed <$> <[back:=(x, Pend g, false)]> slots !! k
              = Some true
            ∧ array_get (<[back:=(x, Pend g, false)]> slots) deqs k = None).
          { intros k Hk. assert (Hne : back ≠ k).
            { intros ->. by apply Hi_not_deq. }
            rewrite (lookup_insert_ne _ _ _ _ Hne)
                    (array_get_insert_ne _ _ _ _ _ Hne).
            by apply Hdeqs. }
          split_and!;
            [ lia | lia | exact Hdom' | exact Hstate' | exact Hpref'
            | exact Hdeqs' | exact Hpvs_ND | exact Hpvs_cap
            | by eapply glue_blocks_valid
            | by intros _
            | ].
          rewrite Hpvs. f_equal. apply flatten_blocks_glue. }
        iModIntro. iSplitR; first by iPureIntro; lia.
        rewrite /enq_state. iFrame "Hvw Hwt". iRight.
        iExists g. by iFrame "Htok Hname Hsaved". } } }

  iIntros (i) "[%Hi Hst]".

  (* [let s = q.items.(i) in ...]: the [items] field and the array are both
     read-only, so this reads two persistent points-to. *)
  iApply (imp_ELet_var (λ s : slot, ⌜s = ss !!! i⌝)%I with "[]").
  { iApply (imp_wand with "[]").
    { iApply (imp_EArrayGet' a i 0 DfracDiscarded ss with "[%] Hsl [] []").
      - lia.
      - iApply (imp_ERecordAccess_pers items_field q [ql; pl; bl] DfracDiscarded a
                  with "Hqlocs [] [] []").
        { by vm_compute. }
        { imp_path. }
        { iExact "Hql". }
        { iIntros "!> _". done. }
      - imp_path. }
    iIntros (s) "[-> _]". rewrite Z.sub_0_r. done. }
  iIntros (s) "->".
  iDestruct (big_sepLZ_lookup _ ss i (ss !!! i) with "Hats") as "(%l & #Hcell)".
  { apply list_lookup_lookup_total_valid. list_z.length; lia. }

  (* [let _old = Atomic.Loc.exchange [%atomic.loc s.v] (Some x) in ()].

     The write. Whether this is also the linearization point depends on what
     the fetch-and-add decided: if the call is still pending, its atomic
     update is run here, and -- because the prediction said this element would
     not come out first -- the invariant enters a contradiction state. *)
  imp_match (option val) $! (λ _ : option val, ▷ Φ ())%I with "[Hst]".
  { iApply (imp_exchange_atomic (⊤ ∖ ↑hwqN) ⊤ _ _ _
              (λ l' : loc, ⌜l' = l⌝)%I (λ o : option val, ⌜o = Some x⌝)%I
              with "[] [] [Hst]").
    { iApply (imp_EAtomicLoc v_field (ss !!! i) [l] with "Hcell [] []").
      { list_z.length; lia. }
      { imp_path. }
      { iNext. iPureIntro. by vm_compute. } }
    { imp_step. simpl. iIntros (y) "->". done. }
    iNext.
    iInv "Hinv" as "(%back & %pvs & %pref & %rest & %cont & %slots & %deqs &
                     >Hbl & Hslots & >Hbk & >Hcpa & >Hcpf & >Hi2 & >Hel & >Hsl● &
                     >Hproph & Hbig & >Hcont & >%Hpure)" "Hclose".
    iDestruct "Hst" as "(#Hvw & Hwt & Hcase)".
    iDestruct (use_val_wit with "Hsl● Hvw") as %Hval.
    iDestruct (writing_tok_not_written with "Hsl● Hwt") as %Hnw.
    destruct Hpure as ((Hback0 & Hbackcap) & Hslots_dom & Hstate & Hpref
                       & Hdeqs & (Hpvs_ND & Hpvs_cap) & Hcs).
    (* Our slot still holds [x] and has not been written. *)
    assert (Hsi : ∃ st, slots !! i = Some (x, st, false)).
    { destruct (slots !! i) as [[[v st] w]|] eqn:HE; last by inversion Hval.
      simpl in Hval, Hnw. injection Hval as ->. injection Hnw as ->.
      by exists st. }
    destruct Hsi as [st Hsi].
    assert (Hi_deq : i ∉ deqs) by (apply Hstate; by rewrite Hsi).
    assert (Hi_back : i < back)
      by (apply Hslots_dom; rewrite Hsi; by eexists).
    iModIntro. iIntros (l' o) "-> ->".
    iExists (array_get slots deqs i).
    iAssert (▷ (l ↦ #(array_get slots deqs i) ∗
                ∀ f : Z → option val,
                  ⌜∀ k, k ≠ i → f k = array_get slots deqs k⌝ -∗
                  l ↦ #(f i) -∗
                  [∗ listZ] k ↦ s ∈ ss, slot_pointsto s (f k)))%I
      with "[Hslots]" as "[Hpt Hback]".
    { iNext.
      iDestruct (slots_lookup_acc ss (array_get slots deqs) i (ss !!! i)
                   with "Hslots") as "[Hpt Hback]".
      { apply list_lookup_lookup_total_valid. list_z.length; lia. }
      iDestruct (slot_pointsto_open with "Hcell Hpt") as "$".
      iIntros (f Hf) "Hl". iApply ("Hback" $! f with "[%] [Hl]"); first done.
      by iApply (slot_pointsto_close with "Hcell Hl"). }
    iFrame "Hpt".
    iIntros "!> Hl".
    iMod (use_writing_tok with "Hsl● Hwt") as "[Hsl● #Hww]".
    (* The value is now visible to dequeuers, whichever bookkeeping follows. *)
    iAssert (∀ f : slot_data → slot_data,
               ⌜∀ d, val_of (f d) = val_of d⌝ -∗
               ⌜∀ d, was_written (f d) = true⌝ -∗
               [∗ listZ] k ↦ s ∈ ss,
                 slot_pointsto s (array_get (update_slot i f slots) deqs k))%I
      with "[Hl Hback]" as "Hback".
    { iIntros (f Hf1 Hf2).
      iApply ("Hback" $! (array_get (update_slot i f slots) deqs) with "[%]").
      { intros k Hne. apply array_get_update_slot_ne. congruence. }
      rewrite /array_get update_slot_lookup Hsi /=.
      rewrite (decide_False _ _ Hi_deq).
      assert (Hpv : physical_value (f (x, st, false)) = Some x).
      { specialize (Hf1 (x, st, false)). specialize (Hf2 (x, st, false)).
        destruct (f (x, st, false)) as [[v' st'] w'].
        simpl in Hf1, Hf2. by subst. }
      rewrite Hpv. iExact "Hl". }

    iDestruct "Hcase" as "[[#Hcw HΦ] | (%g & Htok & Hname & #Hsaved)]".

    { (* The call already committed, at the fetch-and-add. All that is left
         is to record that the slot has been written. *)
      iDestruct (use_committed_wit with "Hsl● Hcw") as %Hcommitted.
      rewrite update_slot_lookup Hsi /= in Hcommitted.
      iDestruct ("Hback" $! set_written with "[%] [%]") as "Hslots";
        [ apply val_of_set_written | apply was_written_set_written | ].
      iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hproph Hbig
                            Hcont]") as "_".
      { iNext.
        iExists back, pvs, pref, rest, cont, (update_slot i set_written slots),
                deqs.
        iFrame "Hbl Hslots Hbk Hcpa Hcpf Hi2 Hsl● Hproph Hcont".
        iSplitL "Hel".
        { by rewrite (map_get_value_update_slot_not_in i set_written pref slots
                        deqs val_of_set_written). }
        iSplitL "Hbig".
        { rewrite /update_slot Hsi.
          iDestruct (big_sepM_delete _ slots i _ Hsi with "Hbig")
            as "[(H1 & H2 & H3) Hbig]".
          iApply big_sepM_insert; first by apply lookup_delete_eq.
          iFrame "Hbig". rewrite /per_slot_own /=. by iFrame "H1 Hww H3". }
        iPureIntro. rewrite /hwq_pure.
        assert (Hdom' : ∀ k, 0 ≤ k < back
                        ↔ is_Some (update_slot i set_written slots !! k)).
        { intros k. destruct (decide (i = k)) as [->|Hne].
          - rewrite update_slot_lookup Hsi /=.
            split; [ intros _; by eexists | intros _; lia ].
          - rewrite (update_slot_lookup_ne _ _ _ _ Hne). apply Hslots_dom. }
        assert (Hstate' : ∀ k,
          (was_committed <$> update_slot i set_written slots !! k = Some false
           → was_written <$> update_slot i set_written slots !! k = Some false)
          ∧ (was_written <$> update_slot i set_written slots !! k = Some false
             → k ∉ deqs)).
        { intros k. destruct (decide (i = k)) as [->|Hne].
          - rewrite update_slot_lookup Hsi /=.
            destruct st as [g|g|]; simpl in Hcommitted;
              try by inversion Hcommitted;
              split; intros HH; by inversion HH.
          - rewrite (update_slot_lookup_ne _ _ _ _ Hne). apply Hstate. }
        assert (Hpref' : ∀ k, k ∈ pref →
          was_committed <$> update_slot i set_written slots !! k = Some true
          ∧ (k ∉ deqs)
          ∧ match cont with WithCont i1 _ => k ≠ i1 | NoCont _ => True end).
        { intros k Hk. destruct (decide (i = k)) as [->|Hne].
          - rewrite update_slot_lookup Hsi /=.
            specialize (Hpref k Hk) as (_ & H2 & H3). by split_and!.
          - rewrite (update_slot_lookup_ne _ _ _ _ Hne). by apply Hpref. }
        assert (Hdeqs' : ∀ k, k ∈ deqs →
          was_written <$> update_slot i set_written slots !! k = Some true
          ∧ was_committed <$> update_slot i set_written slots !! k = Some true
          ∧ array_get (update_slot i set_written slots) deqs k = None).
        { intros k Hk. assert (Hne : i ≠ k) by (intros ->; by apply Hi_deq).
          rewrite (update_slot_lookup_ne _ _ _ _ Hne)
                  (array_get_update_slot_ne _ _ _ _ _ Hne).
          by apply Hdeqs. }
        split_and!;
          [ lia | lia | exact Hdom' | exact Hstate' | exact Hpref'
          | exact Hdeqs' | exact Hpvs_ND | exact Hpvs_cap | ].
        destruct cont as [i1 i2|bs].
        - destruct Hcs as ((HB1 & (HB2 & HB3) & HB4) & HC2 & HC3 & HC4 & HC5
                           & HC6).
          assert (Hne : i ≠ i1).
          { intros ->. rewrite Hsi /= in HC3. by inversion HC3. }
          rewrite (update_slot_lookup_ne _ _ _ _ Hne)
                  (array_get_update_slot_ne _ _ _ _ _ Hne).
          split_and!; try lia; try done.
        - destruct Hcs as (Hbv & Hrest & Hpvs). split_and!; try done.
          intros b Hb. specialize (Hbv b Hb) as (Hv1 & Hv2).
          assert (Hne1 : i ≠ b.1) by (intros ->; by rewrite Hsi in Hv1).
          split.
          + by rewrite (update_slot_lookup_ne _ _ _ _ Hne1).
          + intros j Hj. specialize (Hv2 j Hj) as HH.
            assert (Hne2 : i ≠ j).
            { intros ->. rewrite Hsi /= in HH.
              destruct st as [g|g|]; simpl in Hcommitted;
                by inversion Hcommitted. }
            rewrite (update_slot_lookup_ne _ _ _ _ Hne2). exact HH. }
      iModIntro. iNext. iExact "HΦ". }

    (* The call registered itself as pending at the fetch-and-add. Its atomic
       update is either still in the invariant -- in which case it runs it
       here -- or has been run for it, in which case its postcondition is
       waiting to be collected. *)
    iDestruct (use_name_tok with "Hsl● Hname") as %Hname.
    rewrite update_slot_lookup Hsi /= in Hname.
    iDestruct (big_sepM_delete _ slots i _ Hsi with "Hbig")
      as "[(#Hvw' & _ & Hslot) Hbig]".
    destruct st as [g'|g'|]; simpl in Hname; last by inversion Hname.
    all: injection Hname as ->.

    { (* Still pending. This is the linearization point: the call runs its own
         atomic update, and its element goes at the end of the queue -- which
         contradicts the prediction, if the prediction still claims some other
         slot comes out next. *)
      iDestruct "Hslot" as "(Hpend & %Q & #Hsaved' & AU)".
      iDestruct (saved_prop_agree with "Hsaved Hsaved'") as "#HQeq".
      iMod "AU" as (ls) "[Hc [_ Hcommit]]".
      iDestruct (sync_elts with "Hel Hc") as %<-.
      iMod (update_elts _ _ _
              (map (get_value slots deqs) pref ++ (rest ++ [x]))
              with "Hel Hc") as "[Hel Hc]".
      iMod ("Hcommit" with "[Hc]") as "HQ"; first (rewrite app_assoc; iExact "Hc").
      iMod (use_pending_tok with "Hsl● Hpend") as "[Hsl● #Hcw]".
      { by rewrite update_slot_lookup Hsi. }
      iMod (helped_to_done with "Hsl● Hname") as "Hsl●".
      { by rewrite update_slot_lookup update_slot_lookup Hsi. }
      rewrite update_slot_written_helped_done.
      iDestruct ("Hback" $! set_written_and_done with "[%] [%]") as "Hslots";
        [ by intros [[??]?] | by intros [[??]?] | ].
      iDestruct (big_sepM_insert (per_slot_own γ) (delete i slots) i
                   (x, Done, true) with "[Htok Hbig]") as "Hbig";
        first by apply lookup_delete_eq.
      { iFrame "Hbig". rewrite /per_slot_own /=. by iFrame "Hvw Hww Hcw Htok". }
      assert (Hupd : <[i:=(x, Done, true)]> (delete i slots)
                     = update_slot i set_written_and_done slots)
        by (by rewrite /update_slot Hsi).
      iEval (rewrite Hupd) in "Hbig".
      (* The common pure obligations, for the slot now written and done. *)
      assert (Hdom' : ∀ k, 0 ≤ k < back
                      ↔ is_Some (update_slot i set_written_and_done slots !! k)).
      { intros k. destruct (decide (i = k)) as [->|Hne].
        - rewrite update_slot_lookup Hsi /=.
          split; [ intros _; by eexists | intros _; lia ].
        - rewrite (update_slot_lookup_ne _ _ _ _ Hne). apply Hslots_dom. }
      assert (Hstate' : ∀ k,
        (was_committed <$> update_slot i set_written_and_done slots !! k
           = Some false
         → was_written <$> update_slot i set_written_and_done slots !! k
           = Some false)
        ∧ (was_written <$> update_slot i set_written_and_done slots !! k
           = Some false → k ∉ deqs)).
      { intros k. destruct (decide (i = k)) as [->|Hne].
        - rewrite update_slot_lookup Hsi /=.
          split; intros HH; by inversion HH.
        - rewrite (update_slot_lookup_ne _ _ _ _ Hne). apply Hstate. }
      assert (Hdeqs' : ∀ k, k ∈ deqs →
        was_written <$> update_slot i set_written_and_done slots !! k = Some true
        ∧ was_committed <$> update_slot i set_written_and_done slots !! k
          = Some true
        ∧ array_get (update_slot i set_written_and_done slots) deqs k = None).
      { intros k Hk. assert (Hne : i ≠ k) by (intros ->; by apply Hi_deq).
        rewrite (update_slot_lookup_ne _ _ _ _ Hne)
                (array_get_update_slot_ne _ _ _ _ _ Hne).
        by apply Hdeqs. }
      assert (Hgv : map (get_value (update_slot i set_written_and_done slots)
                           deqs) pref
                    = map (get_value slots deqs) pref).
      { apply map_get_value_update_slot_not_in. by intros [[??]?]. }
      assert (Hwritten : array_get (update_slot i set_written_and_done slots)
                           deqs i = Some x).
      { apply array_get_set_written_and_done; [ by rewrite Hsi | exact Hi_deq ]. }

      destruct cont as [i1 i2|bs].

      { (* A contradiction is already on record; keep it. *)
        iDestruct "Hcont" as "#Hct".
        destruct Hcs as ((HB1 & (HB2 & HB3) & HB4) & HC2 & HC3 & HC4 & HC5
                         & HC6).
        assert (Hne1 : i ≠ i1) by (intros ->; rewrite Hsi /= in HC2;
                                   by inversion HC2).
        iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hproph
                              Hbig]") as "_".
        { iNext.
          iExists back, pvs, pref, (rest ++ [x]), (WithCont i1 i2),
                  (update_slot i set_written_and_done slots), deqs.
          iFrame "Hbl Hslots Hbk Hcpa Hcpf Hi2 Hsl● Hproph Hbig Hct".
          iSplitL "Hel"; first by rewrite Hgv.
          iPureIntro. rewrite /hwq_pure.
          assert (Hpref' : ∀ k, k ∈ pref →
            was_committed <$> update_slot i set_written_and_done slots !! k
              = Some true ∧ (k ∉ deqs) ∧ k ≠ i1).
          { intros k Hk. assert (Hne : i ≠ k).
            { intros ->. specialize (Hpref k Hk) as (HH & _).
              rewrite Hsi /= in HH. by inversion HH. }
            rewrite (update_slot_lookup_ne _ _ _ _ Hne). by apply Hpref. }
          split_and!;
            [ lia | lia | exact Hdom' | exact Hstate' | exact Hpref'
            | exact Hdeqs' | exact Hpvs_ND | exact Hpvs_cap
            | lia | lia | lia | lia
            | by rewrite (update_slot_lookup_ne _ _ _ _ Hne1)
            | by rewrite (update_slot_lookup_ne _ _ _ _ Hne1)
            | exact HC4
            | by rewrite (array_get_update_slot_ne _ _ _ _ _ Hne1)
            | exact HC6 ]. }
        iModIntro. iNext. iRewrite "HQeq". iExact "HQ". }

      destruct Hcs as (Hbv & Hrest & Hpvs).
      destruct bs as [|[i2 ps] bs].

      { (* The prediction is exhausted: nothing to contradict. *)
        iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hproph
                              Hbig Hcont]") as "_".
        { iNext.
          iExists back, pvs, pref, (rest ++ [x]), (NoCont []),
                  (update_slot i set_written_and_done slots), deqs.
          iFrame "Hbl Hslots Hbk Hcpa Hcpf Hi2 Hsl● Hproph Hbig Hcont".
          iSplitL "Hel"; first by rewrite Hgv.
          iPureIntro. rewrite /hwq_pure.
          assert (Hpref' : ∀ k, k ∈ pref →
            was_committed <$> update_slot i set_written_and_done slots !! k
              = Some true ∧ (k ∉ deqs) ∧ True).
          { intros k Hk. assert (Hne : i ≠ k).
            { intros ->. specialize (Hpref k Hk) as (HH & _).
              rewrite Hsi /= in HH. by inversion HH. }
            rewrite (update_slot_lookup_ne _ _ _ _ Hne).
            specialize (Hpref k Hk) as (H1 & H2 & _). by split_and!. }
          split_and!;
            [ lia | lia | exact Hdom' | exact Hstate' | exact Hpref'
            | exact Hdeqs' | exact Hpvs_ND | exact Hpvs_cap
            | intros b Hb; by inversion Hb
            | by intros HH
            | exact Hpvs ]. }
        iModIntro. iNext. iRewrite "HQeq". iExact "HQ". }

      (* The prediction says slot [i2] is handed out before ours. That is now
         false: our element went to the back of the queue while slot [i2] has
         not even been claimed. Record the contradiction; the scan that
         resolves the prophecy will derive [False] from it. *)
      assert (Hbvi2 : block_valid slots (i2, ps))
        by (apply Hbv, list_elem_of_here).
      destruct Hbvi2 as (Hi2_free & _). simpl in Hi2_free.
      assert (Hi2_cap : 0 ≤ i2 < cap).
      { apply Hpvs_cap. rewrite Hpvs. apply elem_of_app. right.
        apply list_elem_of_here. }
      assert (Hi2_back : back ≤ i2).
      { destruct (decide (i2 < back)) as [Hlt|Hge]; last lia. exfalso.
        assert (HH : is_Some (slots !! i2)) by (apply Hslots_dom; lia).
        destruct HH as [d Hd]. by rewrite Hi2_free in Hd. }
      iMod (to_contra i i2 with "Hcont") as "#Hct".
      iMod (i2_lower_bound_update _ _ (Z.to_nat i2) with "Hi2") as "Hi2";
        first lia.
      iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hproph
                            Hbig]") as "_".
      { iNext.
        iExists back, pvs, pref, (rest ++ [x]), (WithCont i i2),
                (update_slot i set_written_and_done slots), deqs.
        iFrame "Hbl Hslots Hbk Hcpa Hcpf Hi2 Hsl● Hproph Hbig Hct".
        iSplitL "Hel"; first by rewrite Hgv.
        iPureIntro. rewrite /hwq_pure.
        assert (Hpref' : ∀ k, k ∈ pref →
          was_committed <$> update_slot i set_written_and_done slots !! k
            = Some true ∧ (k ∉ deqs) ∧ k ≠ i).
        { intros k Hk. assert (Hne : i ≠ k).
          { intros ->. specialize (Hpref k Hk) as (HH & _).
            rewrite Hsi /= in HH. by inversion HH. }
          rewrite (update_slot_lookup_ne _ _ _ _ Hne).
          specialize (Hpref k Hk) as (H1 & H2 & _).
          split_and!; [ exact H1 | exact H2 | congruence ]. }
        split_and!;
          [ lia | lia | exact Hdom' | exact Hstate' | exact Hpref'
          | exact Hdeqs' | exact Hpvs_ND | exact Hpvs_cap
          | lia | lia | lia | lia
          | by rewrite update_slot_lookup Hsi
          | by rewrite update_slot_lookup Hsi
          | exact Hi_deq
          | by rewrite Hwritten
          | ].
        rewrite Hpvs /=. exists (ps ++ flatten_blocks bs).
        by rewrite -app_assoc. }
      iModIntro. iNext. iRewrite "HQeq". iExact "HQ". }

    { (* Already helped: the postcondition is parked in the invariant. *)
      iDestruct "Hslot" as "(#Hcw & %Q & #Hsaved' & HQ)".
      iDestruct (saved_prop_agree with "Hsaved Hsaved'") as "#HQeq".
      iMod (helped_to_done with "Hsl● Hname") as "Hsl●".
      { by rewrite update_slot_lookup Hsi. }
      rewrite update_slot_written_done.
      iDestruct ("Hback" $! set_written_and_done with "[%] [%]") as "Hslots";
        [ by intros [[??]?] | by intros [[??]?] | ].
      iDestruct (big_sepM_insert (per_slot_own γ) (delete i slots) i
                   (x, Done, true) with "[Htok Hbig]") as "Hbig";
        first by apply lookup_delete_eq.
      { iFrame "Hbig". rewrite /per_slot_own /=. by iFrame "Hvw Hww Hcw Htok". }
      assert (Hupd : <[i:=(x, Done, true)]> (delete i slots)
                     = update_slot i set_written_and_done slots)
        by (by rewrite /update_slot Hsi).
      iEval (rewrite Hupd) in "Hbig".
      iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hproph
                            Hbig Hcont]") as "_".
      { iNext.
        iExists back, pvs, pref, rest, cont,
                (update_slot i set_written_and_done slots), deqs.
        iFrame "Hbl Hslots Hbk Hcpa Hcpf Hi2 Hsl● Hproph Hbig Hcont".
        iSplitL "Hel".
        { rewrite (map_get_value_update_slot_not_in i set_written_and_done pref
                     slots deqs); [ iExact "Hel" | by intros [[??]?] ]. }
        iPureIntro. rewrite /hwq_pure.
        assert (Hdom' : ∀ k, 0 ≤ k < back
                    ↔ is_Some (update_slot i set_written_and_done slots !! k)).
        { intros k. destruct (decide (i = k)) as [->|Hne].
          - rewrite update_slot_lookup Hsi /=.
            split; [ intros _; by eexists | intros _; lia ].
          - rewrite (update_slot_lookup_ne _ _ _ _ Hne). apply Hslots_dom. }
        assert (Hstate' : ∀ k,
          (was_committed <$> update_slot i set_written_and_done slots !! k
             = Some false
           → was_written <$> update_slot i set_written_and_done slots !! k
             = Some false)
          ∧ (was_written <$> update_slot i set_written_and_done slots !! k
             = Some false → k ∉ deqs)).
        { intros k. destruct (decide (i = k)) as [->|Hne].
          - rewrite update_slot_lookup Hsi /=.
            split; intros HH; by inversion HH.
          - rewrite (update_slot_lookup_ne _ _ _ _ Hne). apply Hstate. }
        assert (Hpref' : ∀ k, k ∈ pref →
          was_committed <$> update_slot i set_written_and_done slots !! k
            = Some true ∧ (k ∉ deqs)
          ∧ match cont with WithCont i1 _ => k ≠ i1 | NoCont _ => True end).
        { intros k Hk. destruct (decide (i = k)) as [->|Hne].
          - rewrite update_slot_lookup Hsi /=.
            specialize (Hpref k Hk) as (_ & H2 & H3). by split_and!.
          - rewrite (update_slot_lookup_ne _ _ _ _ Hne). by apply Hpref. }
        assert (Hdeqs' : ∀ k, k ∈ deqs →
          was_written <$> update_slot i set_written_and_done slots !! k
            = Some true
          ∧ was_committed <$> update_slot i set_written_and_done slots !! k
            = Some true
          ∧ array_get (update_slot i set_written_and_done slots) deqs k = None).
        { intros k Hk. assert (Hne : i ≠ k) by (intros ->; by apply Hi_deq).
          rewrite (update_slot_lookup_ne _ _ _ _ Hne)
                  (array_get_update_slot_ne _ _ _ _ _ Hne).
          by apply Hdeqs. }
        split_and!;
          [ lia | lia | exact Hdom' | exact Hstate' | exact Hpref'
          | exact Hdeqs' | exact Hpvs_ND | exact Hpvs_cap | ].
        destruct cont as [i1 i2|bs].
        - destruct Hcs as ((HB1 & (HB2 & HB3) & HB4) & HC2 & HC3 & HC4 & HC5
                           & HC6).
          assert (Hne : i ≠ i1).
          { intros ->. rewrite Hsi /= in HC3. by inversion HC3. }
          rewrite (update_slot_lookup_ne _ _ _ _ Hne)
                  (array_get_update_slot_ne _ _ _ _ _ Hne).
          split_and!; try lia; try done.
        - destruct Hcs as (Hbv & Hrest & Hpvs). split_and!; try done.
          intros b Hb. specialize (Hbv b Hb) as (Hv1 & Hv2).
          assert (Hne1 : i ≠ b.1) by (intros ->; by rewrite Hsi in Hv1).
          split.
          + by rewrite (update_slot_lookup_ne _ _ _ _ Hne1).
          + intros j Hj. specialize (Hv2 j Hj) as HH.
            assert (Hne2 : i ≠ j) by (intros ->; rewrite Hsi /= in HH;
                                      by inversion HH).
            rewrite (update_slot_lookup_ne _ _ _ _ Hne2). exact HH. }
      iModIntro. iNext. iRewrite "HQeq". iExact "HQ". } }

  iIntros "HΦ". next_branch. iApply imp_EUnit. iExact "HΦ".
Qed.

(* ---------------------------------------------------------------------- *)
(** ** [scan] and [dequeue] *)

(* [dequeue q] removes and returns the element at the front of the queue. *)
Definition dequeue_spec (q : queue) (m : microvx) : iProp Σ :=
  ∀ γ (cap : Z),
  is_queue γ cap q -∗
  <<{ ∀∀ ls : list val, queue_content γ ls }>>
    m @ ↑hwqN
  <<{ ∃∃ (y : val) (ls' : list val), ⌜ls = y :: ls'⌝ ∗ queue_content γ ls'
    | RET y }>>.

(* The atomic update of a [dequeue] in progress, named so that it can be
   mentioned in the postcondition of the exchange's [match]. *)
Definition dequeue_AU γ (Φ : val → iProp Σ) : iProp Σ :=
  (AU <{ ∃∃ ls : list val, queue_content γ ls }> @ ⊤ ∖ ↑hwqN, ∅
      <{ ∀∀ (y : val) (ls' : list val), ⌜ls = y :: ls'⌝ ∗ queue_content γ ls',
         COMM Φ y }>)%I.

(* [scan]'s licence to disbelieve the prediction.

   The scan takes from a slot below [n], while a contradiction state claims
   that the next slot the queue hands out is [i2]. To commit, the scan must
   rule that out. There are two ways it can know, and it carries whichever
   applies:

   - Left: no contradiction has been recorded since the scan read [back], and
     any that is recorded from now on has [i2 ≥ n]. Since the scan only takes
     below [n], such a contradiction cannot be about the slot it takes.

   - Right: a contradiction was already on record when the scan started, and
     the scan has not yet reached the slot [i1] that caused it. Since a
     contradiction has [i1 < i2], and the scan is at [i ≤ i1], the slot it
     takes is below [i2].

   The right disjunct has to be maintained as the scan advances, which it is:
   the invariant says slot [i1] is non-empty, so a slot that the scan finds
   empty is not [i1]. *)
Definition scan_cont γ (n i : Z) : iProp Σ :=
  no_contra_wit γ.(hwq_i2) (Z.to_nat n) ∨
  (∃ i1 i2, contra γ.(hwq_ct) i1 i2 ∗ ⌜i ≤ i1⌝).

(* [scan q n i] looks for an element in slots [i, n), and restarts from a
   freshly read bound when it reaches [n]. *)
Definition scan_aux_spec (q : queue) (n i : Z) (m : microvx) : iProp Σ :=
  ∀ γ (cap : Z),
  is_queue γ cap q -∗
  ⌜0 ≤ i ≤ cap⌝ -∗ ⌜0 ≤ n ≤ cap⌝ -∗
  scan_cont γ n i -∗
  <<{ ∀∀ ls : list val, queue_content γ ls }>>
    m @ ↑hwqN
  <<{ ∃∃ (y : val) (ls' : list val), ⌜ls = y :: ls'⌝ ∗ queue_content γ ls'
    | RET y }>>.

(* Reading [back] establishes the scan's licence from scratch, whichever of
   the two forms applies to the state it finds. *)
Lemma scan_cont_intro γ cap (b : Z) back pvs pref rest cont slots deqs :
  0 ≤ b →
  hwq_pure cap back pvs pref rest cont slots deqs →
  (match cont with
   | NoCont _       => no_contra γ.(hwq_ct)
   | WithCont i1 i2 => contra γ.(hwq_ct) i1 i2
   end) -∗
  i2_lower_bound γ.(hwq_i2)
    (Z.to_nat (match cont with WithCont _ i2 => i2 | NoCont _ => back end)) -∗
  ⌜b ≤ back⌝ -∗
  |==> i2_lower_bound γ.(hwq_i2)
         (Z.to_nat (match cont with WithCont _ i2 => i2 | NoCont _ => back end)) ∗
       (match cont with
        | NoCont _       => no_contra γ.(hwq_ct)
        | WithCont i1 i2 => contra γ.(hwq_ct) i1 i2
        end) ∗
       scan_cont γ b 0.
Proof.
  iIntros (Hb Hpure) "Hcont Hi2 %Hle".
  destruct cont as [i1 i2|bs].
  - iDestruct "Hcont" as "#Hc".
    iAssert (scan_cont γ b 0) as "#Hsc".
    { iRight. iExists i1, i2. iFrame "Hc". iPureIntro.
      destruct Hpure as (_ & _ & _ & _ & _ & _ & ((H1 & _) & _)). lia. }
    iModIntro. iSplitL "Hi2"; [ iExact "Hi2" | ].
    iSplitR; [ iExact "Hc" | ]. iExact "Hsc".
  - iMod (i2_lower_bound_snapshot with "Hi2") as "[Hi2 Hwit]".
    iModIntro. iSplitL "Hi2"; [ iExact "Hi2" | ].
    iSplitL "Hcont"; [ iExact "Hcont" | ]. iLeft.
    iApply (own_mono with "Hwit"). apply auth_frag_mono.
    apply max_nat_included. simpl. lia.
Qed.

Lemma scan_proof η :
  ▷ in_env "scan" (λ scan, □ iSpec τ[queue; Z; Z] scan scan_aux_spec) η -∗
  □ fun_spec.predicate_over_function_body τ[queue; Z; Z] scan_aux_spec η
      (EAnonFun (AnonFun "q" (EAnonFun __scan_fun1))).
Proof.
  iIntros "#IH".
  iIntros "!>" (q n i).
  unfold scan_aux_spec at 2.
  iIntros (γ cap) "#Hq %Hi %Hn #Hsc". iIntros (Φ) "AU".
  iDestruct "Hq" as (ql pl bl a ss p)
    "(%Hlen & %Hcap & #Hqlocs & #Hql & #Hpl & #Hsl & #Hats & #Hinv)".
  iAssert (is_queue γ cap q) as "#Hqueue".
  { iExists ql, pl, bl, a, ss, p.
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    by iFrame "Hqlocs Hql Hpl Hsl Hats Hinv". }
  iApply imp_please; iNext.
  imp_if.

  { (* [i >= n]: this pass found nothing.
       [let n = Atomic.Loc.get [%atomic.loc q.back] in scan q n 0].
       Reading [back] is not a linearization point; it only fixes the range
       of the next pass, and re-establishes the scan's licence. *)
    iApply (imp_ELet_var
              (λ n' : Z, ⌜0 ≤ n' ≤ cap⌝ ∗ scan_cont γ n' 0)%I with "[]").
    { iApply (imp_load_atomic (⊤ ∖ ↑hwqN) ⊤ _ _ (λ l : loc, ⌜l = bl⌝)%I).
      { iApply (imp_EAtomicLoc back_field q [ql; pl; bl] with "Hqlocs [] []").
        { list_z.length; lia. }
        { imp_path. }
        { iNext. iPureIntro. by vm_compute. } }
      iIntros (l) "->".
      iInv "Hinv" as "(%back & %pvs & %pref & %rest & %cont & %slots & %deqs &
                       >Hbl & Hslots & Hbk & Hcpa & Hcpf & >Hi2 & Hel & Hsl● &
                       Hproph & Hbig & >Hcont & >%Hpure)" "Hclose".
      iModIntro. iExists (DfracOwn 1), back. iFrame "Hbl". iIntros "!> Hbl".
      iMod (scan_cont_intro γ cap back back pvs pref rest cont slots deqs
              with "Hcont Hi2 []") as "(Hi2 & Hcont & #Hsc')";
        [ by destruct Hpure as ((? & ?) & _); lia | done | by iPureIntro | ].
      iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hproph Hbig
                            Hcont]") as "_".
      { iNext. iExists back, pvs, pref, rest, cont, slots, deqs. by iFrame. }
      iModIntro. iFrame "Hsc'". iPureIntro.
      destruct Hpure as ((? & ?) & _). lia. }
    iIntros (n') "[%Hn' #Hsc']".
    imp_app τ[queue; Z; Z].
    iIntros "Hm".
    iApply ("Hm" $! γ cap with "Hqueue [%] [%] Hsc' AU"); lia. }

  (* [i < n]: look at slot [i]. *)
  assert (Hin : i < n) by lia.
  iApply (imp_ELet_var (λ s : slot, ⌜s = ss !!! i⌝)%I with "[]").
  { iApply (imp_wand with "[]").
    { iApply (imp_EArrayGet' a i 0 DfracDiscarded ss with "[%] Hsl [] []").
      - lia.
      - iApply (imp_ERecordAccess_pers items_field q [ql; pl; bl] DfracDiscarded a
                  with "Hqlocs [] [] []").
        { by vm_compute. }
        { imp_path. }
        { iExact "Hql". }
        { iIntros "!> _". done. }
      - imp_path. }
    iIntros (s) "[-> _]". rewrite Z.sub_0_r. done. }
  iIntros (s) "->".
  iDestruct (big_sepLZ_lookup _ ss i (ss !!! i) with "Hats") as "(%l & #Hcell)".
  { apply list_lookup_lookup_total_valid. list_z.length; lia. }

  (* [let p = q.proph in ...] *)
  iApply (imp_ELet_var (λ p' : proph_id, ⌜p' = p⌝)%I with "[]").
  { iApply (imp_ERecordAccess_pers proph_field q [ql; pl; bl] DfracDiscarded p
              with "Hqlocs [] [] []").
    { by vm_compute. }
    { imp_path. }
    { iExact "Hpl". }
    { iIntros "!> _". done. } }
  iIntros (p') "->".

  (* [match Atomic.Loc.exchange [%atomic.loc s.v] None [@resolve p i] with ...]

     This is the linearization point of the whole specification, and the one
     place the prophecy is read. The exchange empties slot [i] and reports
     what was there, in one step, and resolves the queue's prophecy with that
     pair. If it found [Some y], then [y] is the front of the queue: the
     prediction said slot [i] would be handed out next, and the invariant
     keeps the commit prefix in exactly that order, so [y] is the head of the
     logical contents. *)
  iAssert (dequeue_AU γ Φ) with "[AU]" as "AU"; first iExact "AU".
  imp_match (option val) $! (λ o : option val,
      match o with
      | Some y => Φ y
      | None   => dequeue_AU γ Φ ∗ scan_cont γ n (i + 1)
      end)%I with "[AU]".
  { iApply (imp_EResolve_EExchange_atomic (⊤ ∖ ↑hwqN) ⊤ _ _ _ _ _ p #i
              (λ l' : loc, ⌜l' = l⌝)%I (λ o : option val, ⌜o = None⌝)%I
              with "[] [] [AU]").
    (* The prophecy [p] and the index [i] are read off the environment: no
       step, no effect, so these are side conditions rather than goals about
       their evaluation. *)
    { reflexivity. }
    { reflexivity. }
    { iApply (imp_EAtomicLoc v_field (ss !!! i) [l] with "Hcell [] []").
      { list_z.length; lia. }
      { imp_path. }
      { iNext. iPureIntro. by vm_compute. } }
    { imp_step. }
    iNext.
    iInv "Hinv" as "(%back & %pvs & %pref & %rest & %cont & %slots & %deqs &
                     >Hbl & Hslots & Hbk & Hcpa & Hcpf & >Hi2 & >Hel & >Hsl● &
                     >Hproph & Hbig & >Hcont & >%Hpure)" "Hclose".
    iModIntro. iIntros (l' o) "-> ->".
    iDestruct "Hproph" as (rs) "[Hp %Hpvs]".
    iExists (array_get slots deqs i), rs.
    (* Reach into the array at index [i]; what comes back may be given back
       with the contents changed at that index only. *)
    iAssert (▷ (l ↦ #(array_get slots deqs i) ∗
                ∀ f : Z → option val,
                  ⌜∀ k, k ≠ i → f k = array_get slots deqs k⌝ -∗
                  l ↦ #(f i) -∗
                  [∗ listZ] k ↦ s ∈ ss, slot_pointsto s (f k)))%I
      with "[Hslots]" as "[Hpt Hback]".
    { iNext.
      iDestruct (slots_lookup_acc ss (array_get slots deqs) i (ss !!! i)
                   with "Hslots") as "[Hpt Hback]".
      { apply list_lookup_lookup_total_valid. list_z.length; lia. }
      iDestruct (slot_pointsto_open with "Hcell Hpt") as "$".
      iIntros (f Hf) "Hl". iApply ("Hback" $! f with "[%] [Hl]"); first done.
      by iApply (slot_pointsto_close with "Hcell Hl"). }
    iFrame "Hpt Hp".
    iIntros "!>" (rs') "%Hrs Hp Hl".
    assert (Hrep : representable i)
      by (apply array_size_representable; lia).
    destruct Hpure as ((Hback0 & Hbackcap) & Hslots_dom & Hstate & Hpref
                       & Hdeqs & (Hpvs_ND & Hpvs_cap) & Hcs).
    destruct (array_get slots deqs i) as [y|] eqn:Hget.

    - (* The exchange found [y] in slot [i]: this is the take. *)
      (* The prophecy said so. *)
      assert (Hi_deq : i ∉ deqs).
      { intros Hin_deq. specialize (Hdeqs i Hin_deq) as (_ & _ & HH).
        rewrite HH in Hget. by inversion Hget. }
      rewrite Hrs take_data_cons_some in Hpvs; [ | done | lia | done ].
      (* Slot [i] holds [y], was written, and -- since it was written -- was
         committed. *)
      assert (Hsi : ∃ st, slots !! i = Some (y, st, true)).
      { rewrite /array_get in Hget.
        destruct (slots !! i) as [[[v st] w]|] eqn:HE; last by inversion Hget.
        rewrite decide_False in Hget; last done.
        destruct w; last by inversion Hget. simpl in Hget.
        injection Hget as ->. by exists st. }
      destruct Hsi as [st Hsi].
      assert (Hcommitted : was_committed (y, st, true) = true).
      { destruct (was_committed (y, st, true)) eqn:HE; first done. exfalso.
        specialize (Hstate i) as [HS _]. rewrite Hsi /= in HS.
        specialize (HS (f_equal Some HE)). by inversion HS. }
      (* A contradiction on record claims that slot [i2] is handed out next.
         The scan's licence says [i2] is beyond the slot just taken, so the
         take refutes it. *)
      iAssert ⌜match cont with
               | NoCont _      => True
               | WithCont _ i2 => i < i2
               end⌝%I as %Hcont_lt.
      { destruct cont as [i1 i2|bs]; last done.
        destruct Hcs as ((Hc0 & Hc12 & _) & _).
        iDestruct "Hsc" as "[Hwit | (%j1 & %j2 & #Hc & %Hj)]".
        - iDestruct (back_le with "Hi2 Hwit") as %Hle. iPureIntro. lia.
        - iDestruct (contra_agree with "Hc Hcont") as %[-> ->].
          iPureIntro. lia. }
      (* The commit prefix begins with [i]. *)
      assert (Hpref_i : ∃ pref', pref = i :: pref').
      { destruct pref as [|i' pref'].
        - exfalso. destruct cont as [i1 i2|bs].
          + destruct Hcs as (_ & _ & _ & _ & _ & [z Hz]).
            rewrite Hpvs fmap_cons in Hz. cbn [app fst] in Hz.
            injection Hz as Hz1 _. lia.
          + (* No contradiction: the prediction's next slot heads a block, and
               a block's head is an unclaimed slot -- but slot [i] is claimed. *)
            destruct Hcs as (Hbv & _ & Hbf).
            rewrite Hpvs fmap_cons in Hbf. cbn [app fst] in Hbf.
            destruct bs as [|[b_u b_ps] bs]; first by inversion Hbf.
            cbn [flatten_blocks] in Hbf. injection Hbf as Hb_u _.
            assert (block_valid slots (b_u, b_ps)) as [Hnone _]
              by (apply Hbv, list_elem_of_here).
            simpl in Hnone. rewrite -Hb_u Hsi in Hnone. by inversion Hnone.
        - exists pref'. destruct cont as [i1 i2|bs].
          + destruct Hcs as (_ & _ & _ & _ & _ & [z Hz]).
            rewrite Hpvs fmap_cons in Hz. cbn [app fst] in Hz.
            injection Hz as Hz1 _. by rewrite Hz1.
          + destruct Hcs as (_ & _ & Hbf).
            rewrite Hpvs fmap_cons in Hbf. cbn [app fst] in Hbf.
            injection Hbf as Hz1 _. by rewrite Hz1. }
      destruct Hpref_i as [pref' ->].
      (* Commit: the element found is the head of the logical contents. *)
      iMod "AU" as (ls) "[Hc [_ Hcommit]]".
      iDestruct (sync_elts with "Hel Hc") as %<-.
      iMod (update_elts _ _ _ (map (get_value slots deqs) pref' ++ rest)
              with "Hel Hc") as "[Hel Hc]".
      iMod ("Hcommit" $! y (map (get_value slots deqs) pref' ++ rest)
              with "[$Hc]") as "HΦ".
      { iPureIntro. simpl. by rewrite /get_value Hsi. }
      (* Give the array back with slot [i] emptied. *)
      iDestruct ("Hback" $! (array_get slots ({[i]} ∪ deqs)) with "[%] [Hl]")
        as "Hslots".
      { intros k Hk. by apply array_get_more_deqs. }
      { by rewrite array_get_deq; last set_solver. }
      iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hp Hbig
                            Hcont]") as "_".
      { iNext.
        iExists back, (take_slots cap ({[i]} ∪ deqs) rs'), pref', rest, cont,
                slots, ({[i]} ∪ deqs).
        iFrame "Hbl Hslots Hbk Hcpa Hcpf Hi2 Hsl● Hbig Hcont".
        iSplitL "Hel".
        { iExact "Hel". }
        iSplitL "Hp"; first (iExists rs'; by iFrame).
        iPureIntro. rewrite /hwq_pure. split_and!; try done.
        - (* uncommitted ⇒ unwritten; unwritten ⇒ not dequeued *)
          intros k. split; first by apply Hstate.
          intros Hk Hk_deq. apply elem_of_union in Hk_deq as [Hk_i|Hk_deq].
          + apply elem_of_singleton_1 in Hk_i as ->.
            rewrite Hsi /= in Hk. by inversion Hk.
          + by eapply Hstate.
        - (* the commit prefix *)
          intros k Hk.
          assert (Hk' : k ∈ i :: pref') by set_solver.
          specialize (Hpref k Hk') as (H1 & H2 & H3). split_and!; try done.
          apply not_elem_of_union. split; last done.
          apply not_elem_of_singleton. intros ->.
          (* [i] occurs once in the prediction, and it heads the prefix. *)
          destruct cont as [i1 i2|bs].
          + destruct Hcs as (_ & _ & _ & _ & _ & [z Hz]).
            rewrite Hpvs fmap_cons in Hz. cbn [app fst] in Hz.
            injection Hz as Hz.
            apply (take_data_deqs cap ({[i]} ∪ deqs) rs' i); first set_solver.
            rewrite Hz. apply elem_of_app. left.
            apply elem_of_app. by left.
          + destruct Hcs as (_ & _ & Hbf).
            rewrite Hpvs fmap_cons in Hbf. cbn [app fst] in Hbf.
            injection Hbf as Hbf.
            apply (take_data_deqs cap ({[i]} ∪ deqs) rs' i); first set_solver.
            rewrite Hbf. apply elem_of_app. by left.
        - (* dequeued slots *)
          intros k Hk. apply elem_of_union in Hk as [Hk|Hk].
          + apply elem_of_singleton_1 in Hk as ->.
            rewrite Hsi /=. split_and!; [ done | by f_equal | ].
            apply array_get_deq. set_solver.
          + specialize (Hdeqs k Hk) as (H1 & H2 & H3). split_and!; try done.
            apply array_get_deq. set_solver.
        - apply take_data_NoDup.
        - intros k Hk. by eapply take_data_bound.
        - (* the contradiction status is unchanged *)
          destruct cont as [i1 i2|bs].
          + destruct Hcs as ((HB1 & (HB2 & HB3) & HB4) & HC2 & HC3 & HC4 & HC5
                             & [z Hz]).
            assert (Hi1_not_i : i1 ≠ i).
            { intros ->. assert (Hii : i ∈ i :: pref') by set_solver.
              by specialize (Hpref i Hii) as (_ & _ & ?). }
            split_and!; try done.
            * apply not_elem_of_union. split; last done.
              by apply not_elem_of_singleton.
            * rewrite /array_get. rewrite /array_get in HC5.
              destruct (slots !! i1) as [d|]; last done.
              rewrite decide_False; last set_solver.
              rewrite decide_False in HC5; last done. done.
            * rewrite Hpvs fmap_cons in Hz. cbn [app fst] in Hz.
              injection Hz as Hz. by exists z.
          + destruct Hcs as (HC1 & HC2 & HC3). split_and!; try done.
            rewrite Hpvs fmap_cons in HC3. cbn [app fst] in HC3.
            by injection HC3 as HC3. }
      by iModIntro.

    - (* The exchange found nothing: writing [None] over [None] changes
         nothing, and the scan moves on. *)
      rewrite Hrs take_data_cons_none in Hpvs; [ | done | lia ].
      iDestruct ("Hback" $! (array_get slots deqs) with "[%] [Hl]")
        as "Hslots"; [ done | by rewrite Hget | ].
      (* The scan's licence survives the step: a contradiction on record has
         its slot [i1] non-empty, and slot [i] was empty, so [i ≠ i1]. *)
      iAssert (scan_cont γ n (i + 1)) as "#Hsc'".
      { iDestruct "Hsc" as "[Hwit | (%j1 & %j2 & #Hc & %Hj)]".
        { by iLeft. }
        iAssert ⌜j1 ≠ i⌝%I as %Hne.
        { destruct cont as [i1 i2|bs].
          - iDestruct (contra_agree with "Hc Hcont") as %[-> ->].
            destruct Hcs as (_ & _ & _ & _ & HC5 & _).
            iPureIntro. intros ->. by rewrite Hget in HC5.
          - by iDestruct (contra_not_no_contra with "Hcont Hc") as %[]. }
        iRight. iExists j1, j2. iFrame "Hc". iPureIntro. lia. }
      iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hp Hbig
                            Hcont]") as "_".
      { iNext. iExists back, pvs, pref, rest, cont, slots, deqs.
        iFrame "Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hbig Hcont".
        iSplitL "Hp"; first (iExists rs'; by iFrame).
        iPureIntro. rewrite /hwq_pure. by split_and!. }
      iModIntro. by iFrame "AU Hsc'". }

  iIntros "Hc".
  destruct a0 as [y|].
  { (* [Some x -> x] *)
    next_branch. imp_path. }
  (* [None -> scan q n (i + 1)] *)
  skip_branch.
  next_branch.
  iDestruct "Hc" as "[AU #Hsc']".
  imp_app τ[queue; Z; Z].
  iIntros "Hm".
  iApply ("Hm" $! γ cap with "Hqueue [%] [%] Hsc' AU"); lia.
Qed.

Lemma dequeue_proof η :
  in_env "scan" (λ scan, □ iSpec τ[queue; Z; Z] scan scan_aux_spec) η -∗
  EWP (eval η (EAnonFun __dequeue))
    {{ c, □ iSpec τ[queue] c dequeue_spec }}.
Proof.
  iIntros "#Iscan".
  iApply (imp_EAnon_pers τ[queue]).
  iIntros "!>" (q).
  unfold dequeue_spec.
  iIntros (γ cap) "#Hq". iIntros (Φ) "AU".
  iDestruct "Hq" as (ql pl bl a ss p)
    "(%Hlen & %Hcap & #Hqlocs & #Hql & #Hpl & #Hsl & #Hats & #Hinv)".
  iAssert (is_queue γ cap q) as "#Hqueue".
  { iExists ql, pl, bl, a, ss, p.
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    by iFrame "Hqlocs Hql Hpl Hsl Hats Hinv". }
  iApply imp_please; iNext.

  (* [let n = Atomic.Loc.get [%atomic.loc q.back] in scan q n 0].

     Reading [back] fixes the range of the first pass and establishes the
     scan's licence to disbelieve the prediction. *)
  iApply (imp_ELet_var
            (λ n' : Z, ⌜0 ≤ n' ≤ cap⌝ ∗ scan_cont γ n' 0)%I with "[]").
  { iApply (imp_load_atomic (⊤ ∖ ↑hwqN) ⊤ _ _ (λ l : loc, ⌜l = bl⌝)%I).
    { iApply (imp_EAtomicLoc back_field q [ql; pl; bl] with "Hqlocs [] []").
      { list_z.length; lia. }
      { imp_path. }
      { iNext. iPureIntro. by vm_compute. } }
    iIntros (l) "->".
    iInv "Hinv" as "(%back & %pvs & %pref & %rest & %cont & %slots & %deqs &
                     >Hbl & Hslots & Hbk & Hcpa & Hcpf & >Hi2 & Hel & Hsl● &
                     Hproph & Hbig & >Hcont & >%Hpure)" "Hclose".
    iModIntro. iExists (DfracOwn 1), back. iFrame "Hbl". iIntros "!> Hbl".
    iMod (scan_cont_intro γ cap back back pvs pref rest cont slots deqs
            with "Hcont Hi2 []") as "(Hi2 & Hcont & #Hsc')";
      [ by destruct Hpure as ((? & ?) & _); lia | done | by iPureIntro | ].
    iMod ("Hclose" with "[Hbl Hslots Hbk Hcpa Hcpf Hi2 Hel Hsl● Hproph Hbig
                          Hcont]") as "_".
    { iNext. iExists back, pvs, pref, rest, cont, slots, deqs. by iFrame. }
    iModIntro. iFrame "Hsc'". iPureIntro.
    destruct Hpure as ((? & ?) & _). lia. }
  iIntros (n') "[%Hn' #Hsc']".
  imp_app τ[queue; Z; Z].
  iIntros "Hm".
  iApply ("Hm" $! γ cap with "Hqueue [%] [%] Hsc' AU"); lia.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** The module *)

Definition HerlihyWingQueue_names : gset var :=
  {["create"; "enqueue"; "scan"; "dequeue"]}.

Theorem HerlihyWingQueue_module_proof η :
  in_env "Array" array_module_spec η -∗
  EWP (eval_mexpr η __main)
    {{ context [
         var_spec "create"  create_spec;
         var_spec "enqueue" (λ enqueue, □ iSpec τ[queue; val] enqueue enqueue_spec);
         var_spec "dequeue" (λ dequeue, □ iSpec τ[queue] dequeue dequeue_spec)
       ] HerlihyWingQueue_names }}.
Proof.
  iIntros "#HArray".
  iApply imp_module.

  (* [let create capacity = ...]: the one item that needs [Array.init]. *)
  iApply (imp_sitems_let create_spec).
  { iApply create_proof.
    ltac2:(solve_path_spec ()). iIntros (init) "Hinit".
    iApply (init_spec_spec' with "Hinit"). }
  iIntros (create) "#Hcreate".

  (* [let enqueue q x = ...] *)
  iApply (imp_sitems_let
            (λ enqueue : val, □ iSpec τ[queue; val] enqueue enqueue_spec)%I).
  { iApply enqueue_proof. }
  iIntros (enqueue) "#Henqueue".

  (* [let rec scan q n i = ...]: the Löb induction happens inside
     [imp_sitems_letrec_iSpec]; all we owe is the body, under the assumption
     that "scan" is bound (one step later) to a value satisfying
     [scan_aux_spec]. *)
  iApply (imp_sitems_letrec_iSpec τ[queue; Z; Z] scan_aux_spec).
  { iIntros "!> #IH".
    iApply bi.intuitionistically_elim.
    iApply scan_proof. iFrame "#". auto. }
  iIntros (scan) "#Hscan".

  (* [let dequeue q = ...] *)
  iApply (imp_sitems_let
            (λ dequeue : val, □ iSpec τ[queue] dequeue dequeue_spec)%I).
  { iApply dequeue_proof. iFrame "#". auto. }
  iIntros (dequeue) "#Hdequeue".

  iApply imp_sitems_nil.
  rewrite /context /HerlihyWingQueue_names /=.
  iSplit.
  { iPureIntro. rewrite /dom /dom_env /=. set_solver. }
  repeat iSplit;
    [ iFrame "Hcreate" | iFrame "Henqueue" | iFrame "Hdequeue" | done ]; auto.
Qed.

End HerlihyWingQueue.

(* -------------------------------------------------------------------------- *)
(** * Why this queue needs a prophecy

    Nothing above rests on an admitted lemma: [Print Assumptions
    HerlihyWingQueue_module_proof] reports only the framework's own axioms
    (functional extensionality, [Eq_rect_eq], and the abstract
    [max_array_length] / [int_size] / [float]). [Hmax3] is a section
    hypothesis, discharged by the caller.

    ** The order of two enqueues is not determined by the past

    A dequeuer scans left to right and takes the first slot it finds filled,
    but a slot it has already passed may be filled behind it. So at the instant
    it takes slot [j] there may well be a smaller filled slot [k < j] still
    sitting in the array. The queue is nevertheless FIFO -- that is Herlihy and
    Wing's theorem -- but only once the enqueues are allowed to linearize in an
    order that is not their slot order, and choosing that order needs
    information about the future.

    Concretely, take two enqueues [A] and [B] that claim slots 0 and 1 in that
    order, and let [B] fill its slot first. Consider the two schedules

      (1) ..., B fills 1, D reads back, D sees slot 0 empty,
               D takes slot 1 and returns [b], A fills 0;
      (2) ..., B fills 1, A fills 0, D reads back, D takes slot 0
               and returns [a];

    In (1) the only valid linearization has [enq b] before [enq a] -- [D]
    returns [b] while [a] is not yet in the queue. In (2) the only valid one
    has [enq a] before [enq b] -- [D] returns [a], so [a] must be at the head.
    But [B]'s operation ends at its store, so its linearization point is at the
    latest there, and the two schedules agree up to and including that step.
    The order of the two enqueues therefore cannot be decided from the past: it
    is genuinely future-dependent, which is exactly why this queue is the
    textbook example.

    ** One prophecy, for the whole queue

    A per-call prophecy is not enough: the enqueuer's only later step is its
    store, which observes nothing, and the dequeuer that could distinguish the
    two schedules (by reading slot 0) need not even have started when the
    decision is due. So the prophecy is allocated with the queue, stored in it,
    and resolved by every one of [scan]'s exchanges -- that is what the [proph]
    field and the [@resolve p i] annotation are. In the two schedules above the
    resolution trace differs ([(None,0),(Some b,1)] versus [(Some a,0)]), which
    is exactly the information the past does not carry.

    From it the commit order follows: an enqueue joins the queue in the order
    its element will be handed out, as early as it can. Both halves of the
    argument then fall out: a dequeue takes the head because the head is the
    next element of the prediction; and an enqueue joins at the tail because
    everything ahead of it in the prediction has already joined.

    ** What makes it go through

    Two ingredients, neither of them obvious:

    - the decoding of the trace truncates (see [take_data] in [Blocks.v]).
      [pvs] is universally quantified when the prophecy is created, so nothing
      whatsoever may be assumed about it. A decoding that stops at the first
      entry which could not possibly be a real observation -- an index outside
      the array, a take of a slot already emptied, a value of the wrong shape
      -- satisfies the invariant's properties for an arbitrary trace, so no
      property has to be established at creation time and then maintained.

    - when the prediction turns out to be wrong, the invariant does not try to
      repair it. It moves, once and for all, to a contradiction state
      [WithCont i1 i2] recording the two indices whose order was mispredicted,
      and stops claiming anything about the future; an enqueue may then commit
      into the unordered tail [rest]. That contradiction is never resolved into
      a proof that the prediction was right -- it is resolved into [False], by
      the scan that eventually performs the take the prediction ruled out. That
      is what [scan_cont] is: the scan's licence to disbelieve the prediction.

    ** A note on the program

    [enqueue] discards the exchange's result with [match ... with | _ -> ()]
    rather than [let _old = ... in ()]. The two are the same program, but
    Osiris charges a step for the former ([imp_EMatch] grants a later) and none
    for the latter, and [enqueue] needs exactly one: when a dequeuer has
    committed on its behalf, it collects its postcondition through
    [saved_prop_agree], which yields [▷ (P ≡ Q)] and nothing better. *)
