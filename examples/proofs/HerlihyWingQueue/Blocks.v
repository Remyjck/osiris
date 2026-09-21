(******************************************************************************)
(*                                                                            *)
(*        Herlihy-Wing queue: the prophecy and the block decomposition        *)
(*                                                                            *)
(******************************************************************************)

(* This file is the combinatorial heart of the FIFO proof. It contains no Iris
   at all: just the two data abstractions that the invariant is built on.

   1. [take_data] reads the future off the queue's prophecy. Every exchange
      performed by [scan] resolves the prophecy with the pair (what it found,
      which slot it looked at), so the resolution trace records, in order, the
      elements the queue is going to hand out. [take_data] decodes that trace.

      The decoding is truncated: it stops at the first entry that could not
      possibly be a real observation. This is essential. The trace [pvs] is
      universally quantified when the prophecy is created, so nothing may be
      assumed about it -- but every property below holds for an arbitrary
      [pvs], because a trace that would break the property is cut short before
      it does.

   2. [blocks] is the decomposition of the predicted future into blocks. A
      block is one slot that no enqueue has claimed yet, followed by the slots
      of the enqueues that are pending -- claimed but not yet committed. The
      point of the decomposition is that a pending enqueue can be inserted
      into the logical contents at the position of the unused slot heading its
      block, which is how an enqueue commits before it has written anything.

      When the prediction turns out to be wrong the invariant leaves the block
      world and enters a contradiction state, [WithCont i1 i2], which records
      the two indices whose relative order was mispredicted. See
      [cont_status]. *)

From iris.algebra Require Import auth excl agree csum gmap numbers.
From stdpp Require Import list.

From osiris Require Import osiris.

Require Import Ghost.

Open Scope Z.

(* ------------------------------------------------------------------------ *)
(** ** Reading the future off the prophecy *)

(* A resolution is [(#(Some y), #j)] when a scan took the element [y] out of
   slot [j], and [(#(None : option val), #j)] when it found slot [j] empty.
   [take_data cap deqs pvs] is the list of (slot, element) pairs that the
   queue will still hand out, given that the slots in [deqs] have already been
   emptied. *)

Fixpoint take_data (cap : Z) (deqs : gset Z) (pvs : list (val * val))
    : list (Z * val) :=
  match pvs with
  | (VData d args, VInt t) :: pvs' =>
      let j := signed t in
      if decide (0 ≤ j < cap) then
        match args with
        | [y] =>
            if String.eqb d "Some" then
              (if decide (j ∈ deqs) then []
               else (j, y) :: take_data cap ({[j]} ∪ deqs) pvs')
            else []
        | [] => if String.eqb d "None" then take_data cap deqs pvs' else []
        | _ => []
        end
      else []
  | _ => []
  end.

Abbreviation take_slots cap deqs pvs := ((take_data cap deqs pvs).*1).

(* The three properties the invariant needs, for an arbitrary trace. *)

Lemma take_data_deqs cap deqs pvs j :
  j ∈ deqs → j ∉ take_slots cap deqs pvs.
Proof.
  revert deqs. induction pvs as [|[w t] pvs IH]; intros deqs Hj; first set_solver.
  destruct w; try set_solver.
  destruct t; try set_solver.
  simpl. case_decide as Hn; last set_solver.
  destruct v as [|y [|? ?]]; simpl.
  - case_match; [ by apply IH | set_solver ].
  - case_match; last set_solver.
    case_decide as Hin; first set_solver.
    rewrite fmap_cons elem_of_cons. intros [->|Hcon]; first done.
    eapply (IH ({[signed i]} ∪ deqs)); [ set_solver | exact Hcon ].
  - set_solver.
Qed.

Lemma take_data_bound cap deqs pvs j :
  j ∈ take_slots cap deqs pvs → 0 ≤ j < cap.
Proof.
  revert deqs. induction pvs as [|[w t] pvs IH]; intros deqs Hj; first set_solver.
  destruct w; try set_solver.
  destruct t; try set_solver.
  simpl in Hj. case_decide as Hn; last set_solver.
  destruct v as [|y [|? ?]]; simpl in Hj.
  - case_match; [ by eapply IH | set_solver ].
  - case_match; last set_solver.
    case_decide as Hin; first set_solver.
    rewrite fmap_cons elem_of_cons in Hj. destruct Hj as [->|Hj]; first done.
    by eapply IH.
  - set_solver.
Qed.

Lemma take_data_NoDup cap deqs pvs :
  NoDup (take_slots cap deqs pvs ++ elements deqs).
Proof.
  revert deqs. induction pvs as [|[w t] pvs IH]; intros deqs;
    first apply NoDup_elements.
  destruct w; try apply NoDup_elements.
  destruct t; try apply NoDup_elements.
  simpl. case_decide as Hn; last apply NoDup_elements.
  destruct v as [|y [|? ?]]; simpl; try apply NoDup_elements.
  - case_match; [ apply IH | apply NoDup_elements ].
  - case_match; last apply NoDup_elements.
    case_decide as Hin; first apply NoDup_elements.
    specialize (IH ({[signed i]} ∪ deqs)) as H1.
    assert (signed i ∉ take_slots cap ({[signed i]} ∪ deqs) pvs) as H2.
    { apply take_data_deqs. set_solver. }
    apply NoDup_app in H1 as (H1_1 & H1_2 & H1_3).
    rewrite fmap_cons -app_comm_cons. apply NoDup_cons. split.
    { rewrite elem_of_app. intros [?|?%elem_of_elements]; [ done | set_solver ]. }
    apply NoDup_app. repeat split; [ done | | apply NoDup_elements ].
    intros k Hk Hk'%elem_of_elements.
    eapply (H1_2 k); [ done | ]. by apply elem_of_elements; set_solver.
Qed.

Lemma take_slots_NoDup cap deqs pvs : NoDup (take_slots cap deqs pvs).
Proof.
  specialize (take_data_NoDup cap deqs pvs) as H.
  by apply NoDup_app in H as (H & _ & _).
Qed.

(* Consuming one resolution. *)

Lemma take_data_cons_some cap deqs (y : val) (j : Z) pvs :
  representable j → 0 ≤ j < cap → j ∉ deqs →
  take_data cap deqs ((#(Some y), #j) :: pvs)
  = (j, y) :: take_data cap ({[j]} ∪ deqs) pvs.
Proof.
  intros Hrep Hb Hj.
  change (#(Some y)) with (VData "Some" [y]).
  change (#j) with (VInt (repr j)).
  simpl. rewrite signed_repr //.
  rewrite decide_True //. by rewrite decide_False.
Qed.

Lemma take_data_cons_none cap deqs (j : Z) pvs :
  representable j → 0 ≤ j < cap →
  take_data cap deqs ((#(None : option val), #j) :: pvs)
  = take_data cap deqs pvs.
Proof.
  intros Hrep Hb.
  change (#(None : option val)) with (VData "None" (@nil val)).
  change (#j) with (VInt (repr j)).
  simpl. rewrite signed_repr //. by rewrite decide_True.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Blocks

    A block [(i, ps)] is one unused slot [i] -- no enqueue has claimed it --
    followed by the slots [ps] of the enqueues that are pending: they have
    claimed their slot but have not committed.

    The invariant keeps the predicted future split into such blocks. Reading
    the blocks left to right and flattening them back out recovers the
    prediction, so [flatten_blocks] is the bridge between the block world and
    [take_slots]. *)

Definition block  : Type := Z * list Z.
Definition blocks : Type := list block.

(* A block is valid when its head is genuinely unused and its tail is
   genuinely pending. *)

Definition block_valid (slots : gmap Z slot_data) (b : block) :=
  slots !! b.1 = None ∧
  ∀ i, i ∈ b.2 → was_committed <$> (slots !! i) = Some false.

(* [glue_blocks b i bs] records that slot [i] has just been claimed by a
   pending enqueue: [i] stops being the unused head of its own block and
   becomes a pending member of the block that precedes it. *)

Fixpoint glue_blocks (b : block) (i : Z) (bs : blocks) : blocks :=
  match bs with
  | []               => [b]
  | (j, pends) :: bs => if decide (i = j) then (b.1, b.2 ++ i :: pends) :: bs
                        else b :: glue_blocks (j, pends) i bs
  end.

Fixpoint flatten_blocks (bs : blocks) : list Z :=
  match bs with
  | []               => []
  | (i, pends) :: bs => i :: pends ++ flatten_blocks bs
  end.

Lemma blocks_elem1 b (bls : blocks) :
  b ∈ bls → b.1 ∈ flatten_blocks bls.
Proof.
  intros H. induction bls as [|b' bls IH]; first by inversion H.
  destruct (decide (b' = b)) as [->|Hb_not_b'].
  - destruct b as [b_u b_ps]. by apply list_elem_of_here.
  - destruct b' as [b'_u b'_bs]. simpl.
    apply list_elem_of_further. apply elem_of_app; right.
    apply IH. apply elem_of_cons in H as [H|H]; last done.
    by rewrite H in Hb_not_b'.
Qed.

Lemma blocks_elem2 b (bls : blocks) :
  b ∈ bls → ∀ i, i ∈ b.2 → i ∈ flatten_blocks bls.
Proof.
  intros H. induction bls as [|b' bls IH]; first by inversion H.
  destruct (decide (b' = b)) as [->|Hb_not_b'].
  - destruct b as [b_u b_ps]. intros i Hi. simpl in *.
    apply list_elem_of_further. apply elem_of_app. by left.
  - destruct b' as [b'_u b'_bs]. simpl. intros i Hi.
    apply list_elem_of_further. apply elem_of_app; right.
    apply IH; last done. apply elem_of_cons in H as [H|H]; last done.
    by rewrite H in Hb_not_b'.
Qed.

Lemma glue_blocks_valid slots i b_unused b_pendings (bls : blocks) v γ :
  slots !! i = None →
  b_unused ≠ i →
  NoDup (b_unused :: b_pendings ++ flatten_blocks bls) →
  (∀ b : block, b ∈ (b_unused, b_pendings) :: bls → block_valid slots b) →
  ∀ b, b ∈ glue_blocks (b_unused, b_pendings) i bls →
       block_valid (<[i:=(v, Pend γ, false)]> slots) b.
Proof.
  intros Hi. revert b_unused b_pendings.
  induction bls as [|[b_u b_ps] bls IH];
    intros b_unused b_pendings Hb_unused_not_i HND Hblocks_valid [b_u' b_ps'] Hb.
  - apply Hblocks_valid in Hb as Hvalid.
    apply list_elem_of_singleton in Hb. simplify_eq.
    destruct Hvalid as (Hvalid1 & Hvalid2). split.
    + by rewrite lookup_insert_ne.
    + simpl in *. intros k Hk. specialize (Hvalid2 _ Hk) as Hvalid_k.
      destruct (decide (k = i)) as [->|Hk_not_i].
      * by rewrite lookup_insert_eq.
      * by rewrite lookup_insert_ne.
  - simpl in Hb. destruct (decide (i = b_u)) as [->|Hi_not_b_u].
    + apply elem_of_cons in Hb as [Hb|Hb].
      * simplify_eq.
        assert ((b_unused, b_pendings) ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: bls)
          as Hvalid%Hblocks_valid by set_solver.
        destruct Hvalid as (Hvalid1 & Hvalid2).
        assert ((b_u, b_ps) ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: bls)
          as Hvalid'%Hblocks_valid by set_solver.
        destruct Hvalid' as (Hvalid1' & Hvalid2').
        split; simpl.
        ** by rewrite lookup_insert_ne.
        ** intros k Hk. apply elem_of_app in Hk as [Hk|Hk].
           *** assert (k ≠ b_u) as HNEq2.
               { apply NoDup_cons in HND as (_ & HND).
                 apply NoDup_app in HND as (_ & HND & _). apply HND in Hk.
                 simpl in Hk. by apply not_elem_of_cons in Hk as (Hk & _). }
               rewrite lookup_insert_ne; last done. by apply Hvalid2.
           *** apply elem_of_cons in Hk as [->|Hk]; first by rewrite lookup_insert_eq.
               assert (b_u ≠ k) as HNEq2.
               { apply NoDup_cons in HND as (_ & HND).
                 apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
                 apply NoDup_cons in HND as (HND & _).
                 apply not_elem_of_app in HND as (HND & _).
                 intros ->. apply HND, Hk. }
               rewrite lookup_insert_ne; last done. by apply Hvalid2'.
      * assert ((b_u', b_ps') ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: bls)
          as Hvalid%Hblocks_valid by set_solver.
        destruct Hvalid as (Hvalid1 & Hvalid2). rewrite /block_valid.
        assert (b_u ≠ b_u') as HNeq1.
        { apply NoDup_cons in HND as (_ & HND).
          apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
          apply NoDup_cons in HND as (HND & _). intros <-.
          apply not_elem_of_app in HND as (_ & HND). apply HND.
          by apply blocks_elem1 in Hb. }
        rewrite lookup_insert_ne; last done. split; first done.
        intros k Hk. simpl in Hk.
        assert (b_u ≠ k) as HNeq2.
        { apply NoDup_cons in HND as (_ & HND).
          apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
          apply NoDup_cons in HND as (HND & _). intros <-.
          apply not_elem_of_app in HND as (_ & HND). apply HND.
          by eapply blocks_elem2 in Hb. }
        rewrite lookup_insert_ne; last done. by apply Hvalid2.
    + apply elem_of_cons in Hb as [Hb|Hb].
      * simplify_eq.
        assert ((b_unused, b_pendings) ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: bls)
          as Hvalid%Hblocks_valid by set_solver.
        destruct Hvalid as (Hvalid1 & Hvalid2). split.
        ** by rewrite lookup_insert_ne.
        ** intros k Hk. simpl in *.
           assert (k ≠ i) as HNEq.
           { intros ->. apply Hvalid2 in Hk. rewrite Hi in Hk. by inversion Hk. }
           rewrite lookup_insert_ne; last done. by apply Hvalid2.
      * eapply IH; last done; first done.
        { apply NoDup_cons in HND as (_ & HND).
          by apply NoDup_app in HND as (_ & _ & HND). }
        intros b' Hb'.
        assert (b' ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: bls)
          as Hb'_valid%Hblocks_valid by set_solver. done.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The contradiction status

    The invariant is normally in the state [NoCont bs]: the prediction is
    still consistent with what has happened, and [bs] is its block
    decomposition. When a dequeuer's exchange contradicts the prediction, the
    invariant moves -- once and for all -- to [WithCont i1 i2], recording the
    two indices involved. From then on the invariant no longer claims that the
    prediction is right; it claims instead that the contradiction will be
    exposed, which is enough to derive [False] when the mispredicting scan
    finally resolves. *)

Inductive cont_status :=
  | WithCont : Z → Z → cont_status
  | NoCont   : blocks  → cont_status.

Global Instance cont_status_inhabited : Inhabited cont_status.
Proof. constructor. refine (NoCont []). Qed.

Lemma initial_block_valid b (pvs : list Z) :
  b ∈ map (λ i : Z, (i, [])) pvs → block_valid ∅ b.
Proof.
  intros H. induction pvs as [|i pvs IH].
  - by inversion H.
  - simpl in H. apply elem_of_cons in H as [->|H].
    + split; first by apply lookup_empty. intros k Hk. by inversion Hk.
    + apply IH, H.
Qed.

Lemma flatten_blocks_initial (pvs : list Z) :
  pvs = flatten_blocks (map (λ i : Z, (i, [])) pvs).
Proof.
  induction pvs as [|i pvs IH]; first done.
  simpl. f_equal. by apply IH.
Qed.

Lemma flatten_blocks_glue b (bs : blocks) i :
  flatten_blocks (b :: bs) = flatten_blocks (glue_blocks b i bs).
Proof.
  revert b.
  induction bs as [|[b_u' b_ps'] bs IH]; intros [b_u b_ps]; first done.
  simpl. destruct (decide (i = b_u')) as [->|HNEq]; simpl.
  - by rewrite -app_assoc.
  - by rewrite -IH.
Qed.

Lemma flatten_blocks_mem1 (bls : blocks) :
  ∀ b, b ∈ bls → b.1 ∈ flatten_blocks bls.
Proof.
  intros b Hb. induction bls as [|[i ps] bs IH]; first by inversion Hb.
  apply elem_of_cons in Hb as [->|Hb]; first by apply list_elem_of_here.
  simpl. apply list_elem_of_further. apply elem_of_app. right. by apply IH.
Qed.

Lemma flatten_blocks_mem2 (bls : blocks) :
  ∀ b, b ∈ bls → ∀ i, i ∈ b.2 → i ∈ flatten_blocks bls.
Proof.
  intros b Hb. induction bls as [|[i ps] bs IH]; first by inversion Hb.
  intros k Hk. apply elem_of_cons in Hb as [->|Hb]; simpl.
  - apply list_elem_of_further. apply elem_of_app. by left.
  - apply list_elem_of_further. apply elem_of_app. right. by apply IH.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Reading the array

    Osiris models the array of slots as a [Z]-indexed list of records, and the
    invariant owns each slot's cell separately. So, unlike the original
    development, there is no need for a list of physical array contents: the
    value in slot [i] is given pointwise by [array_get]. *)

(* What is physically in slot [i]: nothing if the slot was never claimed or
   has already been emptied by a dequeuer, and otherwise whatever its enqueuer
   has written. *)

Definition array_get (slots : gmap Z slot_data) (deqs : gset Z) (i : Z)
    : option val :=
  match slots !! i with
  | None   => None
  | Some d => if decide (i ∈ deqs) then None else physical_value d
  end.

Lemma array_get_empty deqs i : array_get ∅ deqs i = None.
Proof. by rewrite /array_get lookup_empty. Qed.

Lemma array_get_deq slots deqs i : i ∈ deqs → array_get slots deqs i = None.
Proof.
  intros Hi. rewrite /array_get. destruct (slots !! i); last done.
  by rewrite decide_True.
Qed.

Lemma array_get_insert_ne slots deqs i k d :
  i ≠ k → array_get (<[i:=d]> slots) deqs k = array_get slots deqs k.
Proof. intros H. by rewrite /array_get lookup_insert_ne. Qed.

Lemma array_get_insert_unwritten slots deqs i d :
  was_written d = false → array_get (<[i:=d]> slots) deqs i = None.
Proof.
  intros H. rewrite /array_get lookup_insert_eq.
  destruct (decide (i ∈ deqs)); first done.
  destruct d as [[dv ds] dw]; simpl in H. by subst dw.
Qed.

(* Claiming a fresh slot does not change what is physically there: the slot
   was empty because no one had claimed it, and it is still empty because its
   enqueuer has not written yet. *)
Lemma array_get_insert_fresh slots deqs i d :
  slots !! i = None → was_written d = false →
  array_get (<[i:=d]> slots) deqs i = array_get slots deqs i.
Proof.
  intros H1 H2. rewrite (array_get_insert_unwritten _ _ _ _ H2).
  by rewrite /array_get H1.
Qed.

Lemma array_get_update_slot_ne slots deqs i k f :
  i ≠ k → array_get (update_slot i f slots) deqs k = array_get slots deqs k.
Proof. intros H. by rewrite /array_get update_slot_lookup_ne. Qed.

Lemma array_get_set_written slots deqs i v :
  val_of <$> slots !! i = Some v →
  i ∉ deqs →
  array_get (update_slot i set_written slots) deqs i = Some v.
Proof.
  intros Hv Hi. rewrite /array_get update_slot_lookup.
  destruct (slots !! i) as [[[dv ds] dw]|]; last by inversion Hv.
  simpl in Hv. injection Hv as ->. by rewrite decide_False.
Qed.

Lemma array_get_set_written_and_done slots deqs i v :
  val_of <$> slots !! i = Some v →
  i ∉ deqs →
  array_get (update_slot i set_written_and_done slots) deqs i = Some v.
Proof.
  intros Hv Hi. rewrite /array_get update_slot_lookup.
  destruct (slots !! i) as [[[dv ds] dw]|]; last by inversion Hv.
  simpl in Hv. injection Hv as ->. by rewrite decide_False.
Qed.

Lemma array_get_more_deqs slots deqs i k :
  i ≠ k → array_get slots ({[i]} ∪ deqs) k = array_get slots deqs k.
Proof.
  intros H. rewrite /array_get. destruct (slots !! k); last done.
  destruct (decide (k ∈ deqs)) as [Hk|Hk].
  - rewrite !decide_True //. set_solver.
  - rewrite !decide_False //. set_solver.
Qed.

(* The logical value held in slot [i], used to turn a list of slot indices
   into a list of elements. *)

Definition get_value (slots : gmap Z slot_data) (deqs : gset Z) (i : Z) : val :=
  match slots !! i with
  | None   => inhabitant
  | Some d => val_of d
  end.

Lemma get_value_insert_eq slots deqs i d :
  get_value (<[i:=d]> slots) deqs i = val_of d.
Proof. by rewrite /get_value lookup_insert_eq. Qed.

Lemma map_get_value_not_in_pref i d (pref : list Z) slots deqs :
  was_written d = false →
  i ∉ pref →
  map (get_value (<[i:=d]> slots) deqs) pref = map (get_value slots deqs) pref.
Proof.
  intros Hd. induction pref as [|k pref IH]; intros Hi; first done.
  rewrite /= IH; last by set_solver. f_equal. rewrite /get_value.
  rewrite lookup_insert_ne; first done. set_solver.
Qed.

Lemma map_get_value_update_slot_not_in i f (pref : list Z) slots deqs :
  (∀ d, val_of (f d) = val_of d) →
  map (get_value (update_slot i f slots) deqs) pref
  = map (get_value slots deqs) pref.
Proof.
  intros Hf. induction pref as [|k pref IH]; first done.
  rewrite /= IH. f_equal. rewrite /get_value.
  destruct (decide (i = k)) as [->|Hne].
  - rewrite update_slot_lookup. by destruct (slots !! k) as [d|]; simpl; rewrite ?Hf.
  - by rewrite update_slot_lookup_ne.
Qed.
