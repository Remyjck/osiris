(******************************************************************************)
(*                                                                            *)
(*               Herlihy-Wing queue: the FIFO invariant                       *)
(*                                                                            *)
(******************************************************************************)

(* This file states the invariant of the FIFO proof, and proves the handful of
   lemmas about it that the operation proofs need.

   The shape of the invariant. The logical contents of the queue are

       map (get_value slots deqs) pref ++ rest

   where [pref] is a prefix of the predicted future -- the slots the queue is
   going to hand out, in the order it will hand them out -- and [rest] is a
   list of elements whose slot is not yet known.

   That split is the whole trick. An enqueue that has claimed slot [i] but has
   not written into it yet may already have to commit, because a concurrent
   dequeue is about to overtake it. The prediction says where its element will
   come out, so the enqueue can commit *into [pref]*, at the right position,
   before it has written anything. [rest] holds the elements of the enqueues
   that commit the ordinary way, at their own write.

   When the prediction turns out to be wrong the invariant switches to
   [WithCont i1 i2] and stops claiming anything about the future; what it then
   claims instead is enough to derive [False] when the mispredicting scan
   resolves. *)

From iris.algebra Require Import auth excl agree csum gmap numbers.
From iris.base_logic.lib Require Import invariants saved_prop proph_map.

(* [big_opLZ] is imported ahead of the osiris modules: it re-exports stdpp's
   [x ← _ ; _] notation, which would otherwise shadow the [micro] one. *)
From osiris.utils Require Import list_z big_opLZ.

From osiris Require Import osiris.
From osiris.program_logic Require Import atomic.

Require Import Ghost Blocks.

Open Scope Z.

(* A slot is a one-field record [{ v : 'a option [@atomic] }]; a queue is a
   three-field record [{ items : 'a slot array; proph : Proph.t;
   back : int [@atomic] }]. *)
Abbreviation queue := record.
Abbreviation slot := record.

Record hwq_names := HwqNames {
  hwq_bk : gname; (** monotonicity of [back] *)
  hwq_i2 : gname; (** lower bound on the second index of any contradiction *)
  hwq_el : gname; (** logical contents of the queue *)
  hwq_ct : gname; (** the contradiction one-shot *)
  hwq_sl : gname; (** per-slot data *)
  hwq_cp : gname; (** capacity accounting: enqueue permits *)
}.

Section HerlihyWingQueue.

Context `{!osirisGS Σ, !hwqG Σ, !savedPropG Σ, !inG Σ (authR natUR)}.

Definition hwqN : namespace := nroot .@ "hwq".

(* ---------------------------------------------------------------------- *)
(** ** The client-facing abstract state *)

(* The logical contents of the queue, as a list, oldest element first. *)
Definition queue_content γ (ls : list val) : iProp Σ :=
  hwq_cont γ.(hwq_el) ls.

Lemma queue_content_exclusive γ ls1 ls2 :
  queue_content γ ls1 -∗ queue_content γ ls2 -∗ False.
Proof. apply hwq_cont_exclusive. Qed.

(* The right to call [enqueue] [n] more times. The array is finite and each
   [enqueue] claims a slot forever, so the number of enqueues is bounded by
   the capacity; [create] hands the client exactly [cap] permits. *)
Definition enqueue_permit γ (n : nat) : iProp Σ :=
  own γ.(hwq_cp) (◯ n).

Lemma enqueue_permit_split γ n k :
  enqueue_permit γ (n + k) ⊣⊢ enqueue_permit γ n ∗ enqueue_permit γ k.
Proof. by rewrite /enqueue_permit -own_op -auth_frag_op. Qed.

Lemma capacity_bound γ (b n cap : nat) :
  own γ.(hwq_cp) (● cap) -∗ own γ.(hwq_cp) (◯ b) -∗ enqueue_permit γ n -∗
  ⌜(b + n ≤ cap)%nat⌝.
Proof.
  iIntros "Ha Hb Hn".
  iCombine "Hb Hn" as "Hbn".
  iDestruct (own_valid_2 with "Ha Hbn") as %[Hle _]%auth_both_valid_discrete.
  iPureIntro. by apply nat_included in Hle.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Slots, physically *)

(* The physical cell of a slot record: its single field's location. It is
   persistent, so a thread can name a slot's cell without opening the queue's
   invariant -- which is what lets [%atomic.loc s.v] be evaluated before the
   atomic step that reads or writes it. *)
Definition slot_cell (s : slot) (l : loc) : iProp Σ := blockLocs s [l].

Definition slot_at (s : slot) : iProp Σ := ∃ l, slot_cell s l.

Definition slot_pointsto (s : slot) (o : option val) : iProp Σ :=
  ∃ l, slot_cell s l ∗ l ↦ₗ #o.

Global Instance slot_cell_pers s l : Persistent (slot_cell s l).
Proof. apply _. Qed.
Global Instance slot_at_pers s : Persistent (slot_at s).
Proof. apply _. Qed.

Lemma slot_cell_agree s l l' :
  slot_cell s l -∗ slot_cell s l' -∗ ⌜l' = l⌝.
Proof.
  iIntros "H1 H2".
  by iDestruct (blockLocs_valid with "H1 H2") as %[= ->].
Qed.

Lemma slot_pointsto_open s l o :
  slot_cell s l -∗ slot_pointsto s o -∗ l ↦ₗ #o.
Proof.
  iIntros "#Hc (%l' & #Hc' & Hl)".
  by iDestruct (slot_cell_agree with "Hc Hc'") as %->.
Qed.

Lemma slot_pointsto_close s l o :
  slot_cell s l -∗ l ↦ₗ #o -∗ slot_pointsto s o.
Proof. iIntros "#Hc Hl". iExists l. by iFrame "Hc Hl". Qed.

(* ---------------------------------------------------------------------- *)
(** ** The prophecy *)

(* [pvs] is the sequence of slots the queue will still hand out, decoded from
   the raw resolution trace [rs] by [take_slots]. Because the decoding
   truncates, this holds for whatever [rs] the prophecy turns out to carry. *)
Definition hwq_proph (p : proph_id) (cap : Z) (deqs : gset Z) (pvs : list Z)
    : iProp Σ :=
  ∃ rs, proph p rs ∗ ⌜pvs = take_slots cap deqs rs⌝.

Lemma hwq_proph_facts p cap deqs pvs :
  hwq_proph p cap deqs pvs -∗
  ⌜NoDup (pvs ++ elements deqs) ∧ (∀ i, i ∈ pvs → 0 ≤ i < cap)
   ∧ (∀ i, i ∈ deqs → i ∉ pvs)⌝.
Proof.
  iIntros "(%rs & Hp & ->)". iPureIntro. split_and!.
  - apply take_data_NoDup.
  - intros i Hi. by eapply take_data_bound.
  - intros i Hi. by apply take_data_deqs.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** The invariant *)

(* The atomic update an enqueue of [x] hands over when it asks to be helped.
   [Q] stands for the caller's postcondition; it is kept as a saved
   proposition so that the helper can discharge it without knowing it. *)
Definition enqueue_AU γ (x : val) (Q : iProp Σ) : iProp Σ :=
  (AU <{ ∃∃ ls : list val, queue_content γ ls }> @ ⊤ ∖ ↑hwqN, ∅
      <{ queue_content γ (ls ++ [x]), COMM Q }>)%I.

(* What the invariant owns for one claimed slot. The three states are:

   - [Pend γ]: the enqueue has not committed. The invariant holds its atomic
     update, so a dequeuer that needs to overtake it may commit it.
   - [Help γ]: someone has committed it on its behalf; the postcondition is
     waiting to be collected.
   - [Done]: the enqueue knows it has committed. *)
Definition per_slot_own γ (i : Z) (d : slot_data) : iProp Σ :=
  (slot_val_wit γ.(hwq_sl) i (val_of d) ∗
   (if was_written d then slot_written_wit γ.(hwq_sl) i else True) ∗
   match state_of d with
   | Pend g => slot_pending_tok γ.(hwq_sl) i ∗
               ∃ Q, saved_prop_own g DfracDiscarded Q ∗ enqueue_AU γ (val_of d) Q
   | Help g => slot_committed_wit γ.(hwq_sl) i ∗
               ∃ Q, saved_prop_own g DfracDiscarded Q ∗ ▷ Q
   | Done   => slot_committed_wit γ.(hwq_sl) i ∗ slot_token γ.(hwq_sl) i
   end)%I.

(* The pure side conditions of the invariant, factored out for readability. *)
Definition hwq_pure (cap back : Z) (pvs pref : list Z) (rest : list val)
    (cont : cont_status) (slots : gmap Z slot_data) (deqs : gset Z) : Prop :=
  (* [back] never runs past the end of the array: the enqueue permits, of
     which there are only [cap], are what bound it. So, unlike the original
     development, there is no [min] to carry around. *)
  0 ≤ back ≤ cap ∧
  (* Claimed slots are exactly those below [back]. *)
  (∀ i, (0 ≤ i < back) ↔ is_Some (slots !! i)) ∧
  (* An uncommitted slot has not been written, and an unwritten slot has not
     been dequeued. *)
  (∀ i, (was_committed <$> slots !! i = Some false →
         was_written <$> slots !! i = Some false) ∧
        (was_written <$> slots !! i = Some false → i ∉ deqs)) ∧
  (* The commit prefix names committed, undequeued slots -- and, in a
     contradiction state, never the slot that caused it. *)
  (∀ i, i ∈ pref → was_committed <$> slots !! i = Some true ∧ (i ∉ deqs) ∧
                   (match cont with WithCont i1 _ => i ≠ i1 | _ => True end)) ∧
  (* A dequeued slot was written and committed, and now reads empty. *)
  (∀ i, i ∈ deqs → was_written <$> slots !! i = Some true ∧
                   was_committed <$> slots !! i = Some true ∧
                   array_get slots deqs i = None) ∧
  (* The prediction never repeats a slot and never leaves the array. *)
  (NoDup (pvs ++ elements deqs) ∧ (∀ i, i ∈ pvs → 0 ≤ i < cap)) ∧
  match cont with
  | NoCont bs =>
    (* No contradiction: the prediction beyond the commit prefix is exactly
       the block decomposition [bs]. *)
    (∀ b, b ∈ bs → block_valid slots b) ∧
    (bs ≠ [] → rest = []) ∧
    pvs = pref ++ flatten_blocks bs
  | WithCont i1 i2 =>
    (* A contradiction: slot [i1] was filled and committed, and is still
       there to be found, yet the prediction claims the queue will hand out
       [i2] next. Whoever resolves that will derive [False]. *)
    (0 ≤ i1 ∧ i1 < i2 < cap ∧ i1 < back) ∧
    was_committed <$> slots !! i1 = Some true ∧
    was_written <$> slots !! i1 = Some true ∧ (i1 ∉ deqs) ∧
    array_get slots deqs i1 ≠ None ∧
    pref ++ [i2] `prefix_of` pvs
  end.

Definition hwq_inv_inner γ (cap : Z) (ss : list slot) (bl : loc) (p : proph_id)
    : iProp Σ :=
  (∃ (back  : Z)                (** physical value of [q.back] *)
     (pvs   : list Z)           (** the predicted future *)
     (pref  : list Z)           (** commit prefix of the prediction *)
     (rest  : list val)         (** logical queue after the commit prefix *)
     (cont  : cont_status)      (** contradiction, or prophecy suffix *)
     (slots : gmap Z slot_data) (** per-slot data for claimed indices *)
     (deqs  : gset Z),          (** dequeued indices *)
   (* Physical state. *)
   bl ↦ₗ #back ∗
   ([∗ listZ] i ↦ s ∈ ss, slot_pointsto s (array_get slots deqs i)) ∗
   (* Ghost state. *)
   back_value γ.(hwq_bk) (Z.to_nat back) ∗
   own γ.(hwq_cp) (● Z.to_nat cap) ∗
   own γ.(hwq_cp) (◯ Z.to_nat back) ∗
   i2_lower_bound γ.(hwq_i2)
     (Z.to_nat (match cont with
                | WithCont _ i2 => i2
                | NoCont _      => back
                end)) ∗
   own γ.(hwq_el) (● (Excl' (map (get_value slots deqs) pref ++ rest))) ∗
   own γ.(hwq_sl) (● (of_slot_data <$> slots : gmap Z per_slot)) ∗
   hwq_proph p cap deqs pvs ∗
   ([∗ map] i ↦ d ∈ slots, per_slot_own γ i d) ∗
   match cont with
   | NoCont _       => no_contra γ.(hwq_ct)
   | WithCont i1 i2 => contra γ.(hwq_ct) i1 i2
   end ∗
   ⌜hwq_pure cap back pvs pref rest cont slots deqs⌝)%I.

Definition is_queue γ (cap : Z) (q : queue) : iProp Σ :=
  ∃ (ql pl bl : loc) (a : array) (ss : list slot) (p : proph_id),
    ⌜list_z.length ss = cap⌝ ∗
    ⌜0 < cap ≤ max_array_length⌝ ∗
    blockLocs q [ql; pl; bl] ∗
    ql ↦ₗ□ #a ∗
    pl ↦ₗ□ #p ∗
    a ↦∗[0]□ ss ∗
    ([∗ listZ] s ∈ ss, slot_at s) ∗
    inv hwqN (hwq_inv_inner γ cap ss bl p).

Global Instance is_queue_pers γ cap q : Persistent (is_queue γ cap q).
Proof. apply _. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Instances *)

Global Instance blocks_match_persistent (bs : blocks) γc i1 :
  Persistent (match bs with
              | []           => True
              | (i2, _) :: _ => contra γc i1 i2
              end)%I.
Proof. destruct bs as [|[i2 _] _]; apply _. Qed.

Global Instance cont_match_persistent cont γc :
  Persistent (match cont with
              | NoCont _       => True
              | WithCont i1 i2 => contra γc i1 i2
              end)%I.
Proof. destruct cont as [i1 i2|_]; apply _. Qed.

Global Instance contra_timeless_match cont γc :
  Timeless (match cont with
            | NoCont _       => no_contra γc
            | WithCont i1 i2 => contra γc i1 i2
            end).
Proof. destruct cont as [i1 i2|_]; apply _. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Reaching into the array *)

(* Reaching into the invariant's physical contents at one index. What comes
   back may be given back with the contents changed *at that index only* --
   which is exactly what a single atomic operation on one slot does. *)
Lemma slots_lookup_acc (ss : list slot) (f : Z → option val) (i : Z) s :
  ss !! i = Some s →
  ([∗ listZ] k ↦ s' ∈ ss, slot_pointsto s' (f k)) -∗
  slot_pointsto s (f i) ∗
  (∀ f' : Z → option val, ⌜∀ k, k ≠ i → f' k = f k⌝ -∗ slot_pointsto s (f' i) -∗
         [∗ listZ] k ↦ s' ∈ ss, slot_pointsto s' (f' k)).
Proof.
  iIntros (Hi) "Hss".
  iDestruct (big_sepLZ_lookup_acc_impl i s with "Hss") as "[$ Hclose]";
    first exact Hi.
  iIntros (f' Hf') "Hs".
  iApply ("Hclose" $! (λ k s', slot_pointsto s' (f' k))%I with "[] Hs").
  iIntros "!>" (k s'') "_ %Hne Hs''". by rewrite Hf'.
Qed.

Lemma slots_at_intro (ss : list slot) (f : Z → option val) :
  ([∗ listZ] k ↦ s ∈ ss, slot_pointsto s (f k)) -∗
  ([∗ listZ] s ∈ ss, slot_at s) ∗ ([∗ listZ] k ↦ s ∈ ss, slot_pointsto s (f k)).
Proof.
  iIntros "Hss".
  rewrite -big_sepLZ_sep.
  iApply (big_sepLZ_impl with "Hss").
  iIntros "!>" (k s _) "(%l & #Hc & Hl)".
  iSplitR; [ by iExists l | ]. iExists l. by iFrame "Hc Hl".
Qed.

(* Whatever a dequeuer finds in slot [i], it is either the value the slot's
   enqueuer put there or nothing at all. *)
Lemma array_contents_cases γ slots deqs i v :
  own γ.(hwq_sl) (● (of_slot_data <$> slots) : slotUR) -∗
  slot_val_wit γ.(hwq_sl) i v -∗
    ⌜array_get slots deqs i = Some v ∨ array_get slots deqs i = None⌝.
Proof.
  iIntros "Hs● Hwit".
  iDestruct (use_val_wit with "Hs● Hwit") as %Hslots_i.
  destruct (slots !! i) as [d|] eqn:HEq; last by inversion Hslots_i.
  destruct d as [[v' si] wi]. inversion Hslots_i as [H]; subst v'.
  rewrite /array_get HEq. simpl. iPureIntro.
  destruct (decide (i ∈ deqs)); first by right.
  destruct wi; by [ left | right ].
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Committing a run of pending enqueues

    This is the machinery a dequeuer uses when it must overtake a block of
    enqueues that have claimed their slots but not committed. It commits all
    of them at once, in slot order, by running each one's stored atomic
    update. *)

Definition get_values (slots : gmap Z slot_data) (ps : list Z) : list val :=
  fold_right (λ i acc, match val_of <$> slots !! i with
                       | None   => acc
                       | Some v => v :: acc end) [] ps.

Lemma get_values_not_in n ps d s :
  n ∉ ps → get_values (<[n:=d]> s) ps = get_values s ps.
Proof.
  intros H. induction ps as [|q ps IH]; first done. simpl.
  assert (n ≠ q) as Hn_not_q by set_solver.
  rewrite lookup_insert_ne; last done.
  rewrite IH; first done. set_solver.
Qed.

(* [helped ps] moves every slot in [ps] from [Pend] to [Help]. *)
Definition helped (ps : list Z) (i : Z) (d : slot_data) : option slot_data :=
  match state_of d with
  | Pend g => if decide (i ∈ ps) then Some (val_of d, Help g, was_written d)
              else Some d
  | _      => Some d
  end.

Lemma is_Some_helped (ps : list Z) i d : is_Some (helped ps i d).
Proof.
  rewrite /helped. destruct (state_of d); try by eexists.
  destruct (decide (i ∈ ps)); by eexists.
Qed.

Lemma map_imap_helped_nil slots : map_imap (helped []) slots = slots.
Proof.
  apply map_eq. intros i. rewrite map_lookup_imap.
  destruct (slots !! i) as [d|] eqn:HEq; simpl.
  - rewrite /helped /=. by destruct (state_of d).
  - done.
Qed.

(* Helping changes only the bookkeeping state of a slot: not the value it
   holds, and not whether that value has been written. So it is invisible
   both to a dequeuer reading the array and to the logical contents. *)

Lemma array_get_helped ps slots deqs k :
  array_get (map_imap (helped ps) slots) deqs k = array_get slots deqs k.
Proof.
  rewrite /array_get map_lookup_imap.
  destruct (slots !! k) as [[[v st] w]|] eqn:HE; last done.
  rewrite /= /helped /=. destruct st as [g|g|]; simpl; try done.
  by destruct (decide (k ∈ ps)).
Qed.

Lemma get_value_helped ps slots deqs k :
  get_value (map_imap (helped ps) slots) deqs k = get_value slots deqs k.
Proof.
  rewrite /get_value map_lookup_imap.
  destruct (slots !! k) as [[[v st] w]|] eqn:HE; last done.
  rewrite /= /helped /=. destruct st as [g|g|]; simpl; try done.
  by destruct (decide (k ∈ ps)).
Qed.

Lemma map_get_value_helped ps slots deqs (l : list Z) :
  map (get_value (map_imap (helped ps) slots) deqs) l
  = map (get_value slots deqs) l.
Proof.
  induction l as [|k l IH]; first done.
  by rewrite /= get_value_helped IH.
Qed.

(* A slot that is not being helped is left exactly as it was. *)
Lemma helped_not_in ps slots k :
  k ∉ ps → map_imap (helped ps) slots !! k = slots !! k.
Proof.
  intros Hk. rewrite map_lookup_imap.
  destruct (slots !! k) as [d|]; last done.
  rewrite /= /helped. destruct (state_of d) as [g|g|]; try done.
  by rewrite decide_False.
Qed.

Lemma helped_is_Some ps slots k :
  is_Some (map_imap (helped ps) slots !! k) ↔ is_Some (slots !! k).
Proof.
  rewrite map_lookup_imap. destruct (slots !! k) as [d|]; simpl.
  - split; intros _; [ by eexists | apply is_Some_helped ].
  - split; intros [? HH]; by inversion HH.
Qed.

Lemma was_written_helped ps slots k :
  was_written <$> map_imap (helped ps) slots !! k = was_written <$> slots !! k.
Proof.
  rewrite map_lookup_imap. destruct (slots !! k) as [[[v st] w]|]; last done.
  rewrite /= /helped /=. destruct st as [g|g|]; simpl; try done.
  by destruct (decide (k ∈ ps)).
Qed.

(* Helping only ever moves a slot from uncommitted to committed, so an
   uncommitted slot in the helped map was uncommitted before. *)
Lemma was_committed_helped ps slots k :
  was_committed <$> map_imap (helped ps) slots !! k = Some false →
  was_committed <$> slots !! k = Some false.
Proof.
  rewrite map_lookup_imap. destruct (slots !! k) as [[[v st] w]|]; last done.
  rewrite /= /helped /=.
  destruct st as [g|g|]; simpl; try destruct (decide (k ∈ ps)); done.
Qed.

Lemma was_committed_helped_in ps slots k :
  k ∈ ps → is_Some (slots !! k) →
  was_committed <$> map_imap (helped ps) slots !! k = Some true.
Proof.
  intros Hk [d Hd]. rewrite map_lookup_imap Hd /= /helped.
  destruct d as [[v st] w]. destruct st as [g|g|]; simpl; try done.
  by rewrite decide_True.
Qed.

(* On a list of slots that have all been claimed, [get_values] -- which is how
   [big_lemma] reports the elements it committed -- is just the pointwise
   [get_value]. *)
Lemma get_values_map (m : gmap Z slot_data) deqs (ps : list Z) :
  (∀ k, k ∈ ps → is_Some (m !! k)) →
  get_values m ps = map (get_value m deqs) ps.
Proof.
  induction ps as [|k ps IH]; first done.
  intros Hall. simpl. destruct (m !! k) as [d|] eqn:HE; simpl.
  - rewrite /get_value HE. f_equal. apply IH.
    intros j Hj. apply Hall, list_elem_of_further, Hj.
  - exfalso. specialize (Hall k (list_elem_of_here _ _)) as [d Hd].
    by rewrite HE in Hd.
Qed.

(* Committing a whole block of pending enqueues, in slot order. Each one's
   stored atomic update is run, its element is appended to the logical
   contents, and its postcondition is parked in the invariant for it to
   collect later. *)
Lemma big_lemma γ (ls : list val) slots (ps : list Z) :
  NoDup ps →
  (∀ i, i ∈ ps → was_committed <$> slots !! i = Some false) →
  own γ.(hwq_sl) (● (of_slot_data <$> slots) : slotUR) -∗
   ([∗ map] i ↦ d ∈ slots, per_slot_own γ i d) -∗
   own γ.(hwq_el) (● (Excl' ls)) ={⊤ ∖ ↑hwqN}=∗
    own γ.(hwq_sl) (● (of_slot_data <$> map_imap (helped ps) slots) : slotUR) ∗
    ([∗ map] i ↦ d ∈ map_imap (helped ps) slots, per_slot_own γ i d) ∗
    own γ.(hwq_el) (● (Excl' (ls ++ get_values slots ps))).
Proof.
  revert ps. iIntros (ps).
  iInduction ps as [|n ps] "IH" forall (slots ls); iIntros (HNoDup H) "Hs● Hbig He●".
  - iModIntro. rewrite /= app_nil_r map_imap_helped_nil. iFrame.
  - assert (∀ i : Z, i ∈ ps → was_committed <$> slots !! i = Some false) as H1.
    { intros i Hi. apply H. apply list_elem_of_further, Hi. }
    assert (was_committed <$> slots !! n = Some false) as H2.
    { apply H. apply list_elem_of_here. }
    assert (∃ vn γn wn, slots !! n = Some (vn, Pend γn, wn)) as Hn.
    { destruct (slots !! n) as [[[vn sn] wn]|]; last by inversion H2.
      (destruct sn as [γn|γn|]; last by inversion H2); by exists vn, γn, wn. }
    apply NoDup_cons in HNoDup. destruct HNoDup as [Hn_not_in_ps HNoDup].
    destruct Hn as [v [g [w Hn]]].
    assert (slots = <[n:=(v, Pend g, w)]> (delete n slots)) as Hs.
    { by rewrite insert_delete_eq insert_id. }
    rewrite [in ([∗ map] _ ↦ _ ∈ slots, _)%I]Hs.
    iDestruct (big_sepM_insert with "Hbig")
      as "[Hbig_n Hbig]"; first by apply lookup_delete_eq.
    iDestruct "Hbig_n" as "[Hval_wit_n [Hwritten_n [Hpending_tok_n H']]]".
    iDestruct "H'" as (Q) "[Hsaved AU]".
    iMod "AU" as (elts_AU) "[He◯ [_ Hclose]]".
    iDestruct (sync_elts with "He● He◯") as %<-.
    iMod (update_elts _ _ _ (ls ++ [v]) with "He● He◯") as "[He● He◯]".
    iMod ("Hclose" with "[$He◯]") as "HPost".
    iMod (use_pending_tok with "Hs● Hpending_tok_n")
      as "[Hs● Hcommitted_wit_n]"; first by rewrite Hn.
    iCombine "Hsaved HPost" as "Hn".
    iDestruct (big_sepM_insert _ (delete n slots) n (v, Help g, w)
      with "[Hn Hval_wit_n Hwritten_n Hcommitted_wit_n Hbig]")
      as "Hbig"; first by apply lookup_delete_eq.
    { iClear "IH". iFrame "Hbig". rewrite /per_slot_own /=. iFrame.
      iExists Q. iDestruct "Hn" as "[$ HPost]". iNext. done. }
    rewrite insert_delete_eq /update_slot Hn insert_delete_eq.
    assert (∀ i : Z, i ∈ ps → was_committed <$> <[n:=(v, Help g, w)]> slots !! i = Some false) as HHH.
    { intros i Hi. rewrite lookup_insert_ne; [ by apply H1 | by set_solver ]. }
    iMod ("IH" $! (<[n:=(v, Help g, w)]> slots) (ls ++ [v]) HNoDup HHH
            with "Hs● Hbig He●") as "[Hs● [Hbig He●]]"; iClear "IH".
    assert (map_imap (helped ps) (<[n:=(v, Help g, w)]> slots)
            = map_imap (helped (n :: ps)) slots) as ->.
    { apply map_eq. intros i. destruct (decide (i = n)) as [->|Hi_not_n].
      - rewrite map_lookup_imap map_lookup_imap /= lookup_insert_eq Hn /=.
        rewrite /helped /=. rewrite decide_True; first done. set_solver.
      - rewrite map_lookup_imap map_lookup_imap /= lookup_insert_ne; last done.
        destruct (slots !! i) as [[[vi si] wi]|]; last done. simpl.
        rewrite /helped /=. destruct si; try done.
        destruct (decide (i ∈ n :: ps)).
        + rewrite decide_True; first done. set_solver.
        + rewrite decide_False; first done. set_solver. }
    iModIntro. iFrame.
    by rewrite /= Hn -app_assoc /= get_values_not_in.
Qed.

End HerlihyWingQueue.
