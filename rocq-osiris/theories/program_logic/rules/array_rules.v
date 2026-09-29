From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang.
Require Import osiris_utils.
Require Import ewp.
Require Import impure_rules stop_rules.
From osiris.utils Require Import list_z big_opLZ.

(** This file defines array resource predicates and [EWP] rules for array expressions. *)

Local Abbreviation array := syntax.array.

Section array_resources.

  Context `{!osirisGS Σ}.

  (* [blockLocs a ls] is defined in ghost_state.v as a persistent ghost map entry.
     The definition, [blockLocs_pers], [blockLocs_valid], and [blockLocs_length] lemmas
     are all there. *)

  (* Ownership over a segment of the array. *)

  Definition isSlice `{Encode A} a dq (i : Z) (xs : list A) : iProp Σ :=
    ∃ ls, blockLocs a ls ∗
    ⌜0 ≤ i ≤ length ls - length xs⌝ ∗
    [∗ listZ] l;x ∈ seg i (i + length xs) ls; xs, l ↦ₗ{dq} #x.

  Lemma isSlice_blockLocs `{Encode A} a dq i (xs : list A) :
    isSlice a dq i xs -∗ ∃ ls, blockLocs a ls ∗ ⌜0 ≤ i ≤ length ls - length xs⌝.
  Proof. iIntros "(%ls & $ & $ & _)". Qed.

  Lemma isSlice_in_bounds `{Encode A} a dq i (xs : list A) :
    isSlice a dq i xs -∗ ⌜0 ≤ i⌝.
  Proof.
    iIntros "Hslice".
    iPoseProof (isSlice_blockLocs with "Hslice") as "(%ls & Hblock & %Hbounds)".
    iPureIntro. lia.
  Qed.

  (* Ownership of the whole array.
     Includes the exclusive physical block ownership [a ⤇{1} Mut ls], enabling freeze. *)

  Definition ownArray `{Encode A} (a : array) dq (xs : list A) : iProp Σ :=
    ∃ ls, blockLocs a ls ∗ blockTag a dq Mut ∗ isSlice a dq 0 xs ∗ ⌜length ls = length xs⌝.

  Lemma ownArray_blockLocs `{Encode A} a dq (xs : list A) :
    ownArray a dq xs -∗ ∃ ls, blockLocs a ls ∗ ⌜length ls = length xs⌝.
  Proof. iIntros "(%ls & #$ & _ & _ & $)". Qed.

  Lemma ownArray_length `{Encode A} a dq (xs : list A) :
    ownArray a dq xs -∗ ⌜0 ≤ length xs ≤ max_array_length⌝.
  Proof.
    iIntros "Hown".
    iPoseProof (ownArray_blockLocs with "Hown") as "(%ls & Ha & %Hlenls)".
    iPoseProof (blockLocs_length with "Ha") as "%Hboundls".
    iPureIntro. rewrite Hlenls in Hboundls.
    split; [ by length_nonneg xs | apply Hboundls ].
  Qed.

  Lemma ownArray_isSlice `{Encode A} a dq (xs : list A) :
    ownArray a dq xs -∗ isSlice a dq 0 xs.
  Proof. iIntros "(%ls & #Ha & _ & $ & %Hlen)". Qed.

  (* Making a slice read-only. An array written once at creation and then
     only read (the [items] array of a concurrent data structure, say) can
     have its points-to discarded here and shared freely afterwards, so
     that a reader needs no invariant. *)
  Lemma isSlice_persist `{Encode A} (E : coPset) a i (xs : list A) :
    isSlice a (DfracOwn 1) i xs ={E}=∗ isSlice a DfracDiscarded i xs.
  Proof.
    iIntros "(%ls & #Hblock & %Hbound & Hpts)".
    iMod (big_opLZ.big_sepLZ2_fupd E
            (λ (_ : Z) (l : locations.loc) (x : A), (l ↦ₗ□ #x)%I)
            with "[Hpts]") as "Hpts".
    { iApply (big_opLZ.big_sepLZ2_impl with "Hpts").
      iIntros "!>" (k l x _ _) "Hl".
      by iMod (gen_heap.pointsto_persist with "Hl"). }
    iModIntro. iExists ls.
    iSplitR; [ iExact "Hblock" | ].
    iSplitR; [ iPureIntro; exact Hbound | ].
    iExact "Hpts".
  Qed.

  Lemma isSlice_ownArray `{Encode A} a dq ls (xs : list A) :
    blockLocs a ls -∗
    blockTag a dq Mut -∗
    isSlice a dq 0 xs -∗
    ⌜length ls = length xs⌝ -∗
    ownArray a dq xs.
  Proof. iIntros "#Ha Hmut $ $". iFrame "Hmut Ha". Qed.

End array_resources.

Notation "a ↦∗ dq xs" :=
    (ownArray a dq xs)
      (at level 20, dq custom dfrac at level 1, format "a  ↦∗ dq  xs") : bi_scope.
Notation "a ↦∗[ i ] dq xs" :=
  (isSlice a dq i xs)
    (at level 20, dq custom dfrac at level 1, i at level 200, format "a  ↦∗[ i ] dq  xs") : bi_scope.

Section array_resources.

  Lemma Slice_app `{!osirisGS Σ} `{Encode A} j dq a i (xs ys : list A) :
    j = i + length xs →
    a ↦∗[i]{dq} (xs ++ ys) ⊣⊢ (a ↦∗[i]{dq} xs ∗ a ↦∗[j]{dq} ys).
  Proof.
    intros ->.
    lengths.
    iSplit; iIntros "Hslice".
    - iDestruct "Hslice" as "(%ls & #$ & %Hbound & Hls)".
      length in Hbound. length.
      rewrite (split_seg (i + length xs)); try lia.
      iPoseProof (big_sepLZ2_app_inv with "Hls")
        as "($ & Hslice2)"; first (length; lia).
      replace (i + (length xs + length ys)) with (i + length xs + length ys) by lia.
      iFrame.
      iPureIntro. lia.

    - iDestruct "Hslice" as "(Hslice1 & Hslice2)".
      iDestruct "Hslice1" as "(%ls & #Harr & %Hlen & Hslice1)".
      iDestruct "Hslice2" as "(% & #Harr' & %Hlen' & Hslice2)".
      iPoseProof (blockLocs_valid with "Harr Harr'") as "->".
      iFrame "#". length.

      iPoseProof (big_sepLZ2_app with "Hslice1 Hslice2") as "Hslice".
      rewrite -(split_seg (i + length xs)); try lia.
      replace (i + (length xs + length ys)) with (i + length xs + length ys) by lia.
      iFrame "∗".
      iPureIntro. lia.
  Qed.

  (* We can split a slice on an index [j] of the model [xs].

     This results in two slices with models
     [seg 0 j xs] and [seg j (length xs) xs]. *)

  Lemma split_Slice `{!osirisGS Σ} `{Encode A} (j : Z) dq ls i (xs : list A) :
    0 ≤ j ≤ length xs →
    ls ↦∗[i]{dq} xs ⊣⊢ ls ↦∗[i]{dq} (seg 0 j xs) ∗ ls ↦∗[i + j]{dq} (seg j (length xs) xs).
  Proof.
    lengths.
    rewrite -{1}(seg_all 0 (length xs) xs); try lia.
    rewrite (split_seg j); try lia.
    rewrite (Slice_app (i + j)). reflexivity.
    length; lia.
  Qed.

End array_resources.


Section array_reasoning.

  Context `{!osirisGS Σ}.

  Context {η : env} {E : coPset} {Ψ : iEff Σ}.

  Global Instance notval_block : NotVal (mut_tag * list loc) := {}.
  Global Instance notval_listloc : NotVal (list loc) := {}.

  Implicit Types ζ : exn → iProp Σ.

  (** General [as_array] rule.  Given that the postcondition of [m] implies
      [blockLocs a ls] for some [a] and [ls], the [load_block] step is
      discharged automatically and [Φ ls] is delivered. *)
  Lemma imp_as_array {ζ} {Φ : array → iProp Σ} (m : microvx) :
    EWP m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    EWP as_array m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm".
    iApply (imp_bind with "Hm").
    iIntros (a) "HΦ".
    iApply (imp_ret with "HΦ"). encode.
  Qed.

  Lemma imp_EArrayLit `{Encode A} {ζ} (Φs : list (A → iProp Σ)) es :
    ⌜length Φs = length es ∧ length es ≤ max_array_length⌝ -∗
    EWP evals η es @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ xs, [∗ listZ] x;Φ ∈ xs;Φs, Φ x }} -∗
    EWP eval η (EArrayLit es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ a, ∃ xs, a ↦∗ xs ∗ [∗ listZ] x;Φ ∈ xs;Φs, Φ x }}.
  Proof.
    iIntros "[%Hleneq %Hlenbound] He". simpl_eval.
    iApply (imp_bind (A1:=list A) with "He").
    iIntros (xs) "HΦs".
    iApply (imp_bind (A1:=list loc)).
    { iApply imp_allocn. iIntros "!>" (ls) "Hls". iExact "Hls". }
    iIntros (arr) "Hls".
    iPoseProof (big_sepLZ2_length with "Hls") as "%Hlenls".
    iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenxs".
    iApply (imp_bind (A1:=loc)).
    { iApply (imp_alloc_block Mut arr with "[]").
      iPureIntro. rewrite Hlenls Hlenxs Hleneq. apply Hlenbound. }
    iIntros (a) "(Ha & #Harr)".
    iApply imp_ret; first encode.
    iFrame "HΦs".

    (* Goal: establish [a ↦∗ xs] from [a ⤇{1} Mut arr], [blockLocs a arr],
       and [∀ l x ∈ arr xs, l ↦ₗ #x ]. *)
    iApply (isSlice_ownArray with "Harr Ha [Hls] [//]").
    iFrame "Harr". seg. iFrame "Hls".
    iPureIntro; lia.
  Qed.

  Lemma imp_EArrayEmpty `{Encode A} {ζ} :
    ⊢ EWP eval η (EArrayLit []) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
        {{ a, a ↦∗ (@nil A) }}.
  Proof.
    iApply imp_wand.
    - iApply (imp_EArrayLit (@nil (A → _))  []).
      iPureIntro; length; split; auto.
      pose proof (max_array_positive). lia.
      simpl_evals. iApply imp_ret; first encode.
      by iApply big_sepLZ2_nil.
    - iIntros (a) "(%xs & HownArr & Hxs)".
      iPoseProof (big_sepLZ2_nil_inv_r with "Hxs") as "->".
      iApply "HownArr".
  Qed.

  Lemma imp_EArrayLength' {ζ} (ls : list loc) e :
    EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (a : array), blockLocs a ls }} -∗
    EWP eval η (EArrayLength e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = length ls⌝ }}.
  Proof.
    iIntros "He". simpl_eval.
    iApply (imp_bind with "[He] [-]").
    { iApply (imp_as_array with "He"). }
    iIntros (a) "#HBlock".
    iApply imp_bind.
    { iApply (imp_load_block_ghost with "HBlock"). }
    iIntros ((t & ls')) "->". iApply imp_ret; first encode. auto.
  Qed.

  Lemma imp_EArrayLength `{Encode A} {ζ} dq (xs : list A) e :
    EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a, a ↦∗{dq} xs }} -∗
    EWP eval η (EArrayLength e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = length xs⌝ }}.
  Proof.
    iIntros "He". simpl_eval.
    iApply (imp_bind with "[He] [-]").
    { iApply (imp_as_array with "He"). }
    iIntros (a) "Hslice".
    iPoseProof (ownArray_blockLocs with "Hslice") as "(%ls & #Hblock & %Hbounds)".
    iApply imp_bind.
    { iApply (imp_load_block_ghost with "Hblock"). }
    iIntros ((t & ls')) "->".
    iApply imp_ret; first encode.
    auto.
  Qed.

  Lemma imp_EArrayMake `{Encode A} {ζ} {e1 e2} (n : Z) (Φ : A → iProp Σ) :
    ⌜0 ≤ n ≤ max_array_length⌝ -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ i, ⌜i = n⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    EWP eval η (EArrayMake e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ (a : array), ∃ x, Φ x ∗ a ↦∗ (replicate n x) }}.
  Proof.
    iIntros (Hbound) "He1 He2". simpl_eval.
    iApply (imp_bind_par with "[He1] He2").
    { iApply (imp_as_int with "He1"). }
    iIntros (? x) "->  Hφ /=".
    rewrite signed_repr; last representable.
    case_decide; last contradiction.
    iApply imp_bind.
    { rewrite <- fmap_replicate. iApply imp_allocn.
      iIntros "!>" (ls) "Hpts". iExact "Hpts". }
    iIntros (arr) "!> Hpts".
    iPoseProof (big_sepLZ2_length with "Hpts") as "%Hlen'".
    iApply imp_bind.
    { iApply (imp_alloc_block Mut arr).
      iPureIntro. length in Hlen'. length; lia. }
    iIntros (a) "(Ha & #Harr)".

    iApply imp_ret; first encode.
    simpl. length in Hlen'.
    iFrame "Hφ".
    iFrame "#∗". seg. iFrame "Hpts".
    iPureIntro.
    length; lia.
  Qed.

  Global Instance inhabited_loc : Inhabited loc.
  Proof.
    do 2 constructor. apply Z.inhabited.(inhabitant).
  Qed.

  Lemma big_sepLZ2_lookup_seg_acc `{Inhabited A, Inhabited B} k i j (xs : list A) (ys : list B) (Φ : Z → A → B → iProp Σ) :
    valid_seg i j xs →
    i ≤ k < j →
    ([∗ listZ] k↦l; x ∈ seg i j xs; ys, Φ k l x) -∗
    Φ (k - i) (xs !!! k) (ys !!! (k - i)) ∗
    (Φ (k - i) (xs !!! k) (ys !!! (k - i)) -∗ [∗ listZ] k↦l; x ∈ seg i j xs; ys, Φ k l x).
  Proof.
    iIntros (Hvalid Hlek) "Hseg".
    iPoseProof (big_sepLZ2_length with "Hseg") as "%Hlen".
    iApply (big_sepLZ2_lookup_acc _ _ _ (k - i) with "Hseg"); lookup.
    - replace (i + (k - i)) with k by lia.
      apply list_lookup_lookup_total_valid. lia.
    - apply list_lookup_lookup_total_valid.
      revert Hlen. length. lia.
  Qed.

  Lemma big_sepLZ2_insert_seg_acc `{Inhabited A, Inhabited B} k i j (xs : list A) (ys : list B) (Φ : Z → A → B → iProp Σ) :
    valid_seg i j xs →
    i ≤ k < j →
    ([∗ listZ] k↦l; x ∈ seg i j xs; ys, Φ k l x) -∗
    Φ (k - i) (xs !!! k) (ys !!! (k - i)) ∗
    (∀ x y, Φ (k - i) x y -∗ [∗ listZ] n↦l; x ∈seg i j (<[k:=x]>xs); <[k-i:=y]>ys, Φ n l x).
  Proof.
    iIntros (Hvalid Hlek) "Hseg".
    iPoseProof (big_sepLZ2_length with "Hseg") as "%Hlen".
    setoid_rewrite seg_insert_inside; last lia.
    iApply (big_sepLZ2_insert_acc _ _ _ (k - i) with "Hseg"); lookup.
    - replace (i + (k - i)) with k by lia.
      apply list_lookup_lookup_total_valid. lia.
    - apply list_lookup_lookup_total_valid.
      revert Hlen. length. lia.
  Qed.

  Lemma slice_insert_acc `{Encode A, Inhabited A} (i j : Z) (a : array) (xs : list A) (ls : list loc) :
    j ≤ i < j + length xs →
    a ↦∗[j] xs -∗
    blockLocs a ls -∗
    (ls !!! i) ↦ₗ #(xs !!! (i - j)) ∗
    (∀ y, (ls !!! i) ↦ₗ #y -∗ a ↦∗[j] <[i - j := y]> xs).
  Proof.
    iIntros "%Hbound_i Hslice #Hblock".
    iDestruct "Hslice" as "(% & #Hblock' & %Hbounds & Hseg)".
    iPoseProof (blockLocs_valid with "Hblock Hblock'") as "->".
    iPoseProof (big_sepLZ2_insert_seg_acc i with "Hseg") as "(Hpts & Hseg)".
    lengths. lia. lia.
    iFrame.
    iIntros "%y Hpts". iSpecialize ("Hseg" with "Hpts").
    unfold isSlice. update. length.
    iFrame "∗#%".
  Qed.

  Lemma slice_lookup_acc `{Encode A, Inhabited A} (i j : Z) (a : array) dq (xs : list A) (ls : list loc) :
    j ≤ i < j + length xs →
    a ↦∗[j]{dq} xs -∗
    blockLocs a ls -∗
    (ls !!! i) ↦ₗ{dq} #(xs !!! (i - j)) ∗
    ((ls !!! i) ↦ₗ{dq} #(xs !!! (i - j)) -∗ a ↦∗[j]{dq} xs).
  Proof.
    iIntros "%Hbound_i Hslice #Hblock".
    iDestruct "Hslice" as "(% & #Hblock' & %Hbounds & Hseg)".
    iPoseProof (blockLocs_valid with "Hblock Hblock'") as "->".
    iPoseProof (big_sepLZ2_lookup_seg_acc i with "Hseg") as "(Hpts & Hseg)".
    lengths. lia. lia.
    iFrame.
    iIntros "Hpts". iSpecialize ("Hseg" with "Hpts").
    iFrame "∗#%".
  Qed.

  Lemma imp_EArrayGet2 `{Encode A, Inhabited A} {Φ : A → iProp Σ} {ζ} (Φ2 : Z → iProp Σ) e1 e2 (a : array) ls :
    ▷ blockLocs a ls -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a', ⌜a'=a⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    (∀ i, Φ2 i -∗
          ∃ dq j xs,
            ▷ (⌜j ≤ i < j + length xs⌝ ∗ a ↦∗[j]{dq} xs) ∗
            ▷ (a ↦∗[j]{dq} xs -∗ Φ (xs !!! (i - j)))) -∗
    EWP eval η (EArrayGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "#Ha He1 He2 P". simpl_eval.
    iApply (imp_bind_par with "[He1] [He2]").
    - iApply (imp_as_array with "He1").
    - iApply (imp_as_int with "He2").
    - iIntros (? i) "-> HΦ2".
      iDestruct ("P" with "HΦ2") as
        "(%dq & %j & %xs & Hslice & Hlookup)". iNext.
      iDestruct "Hslice" as "(%Hbound & Hslice)".
      iPoseProof (isSlice_blockLocs with "Hslice") as "(% & #Ha' & %Hbound')".
      iPoseProof (blockLocs_valid with "Ha Ha'") as "->".
      iPoseProof (blockLocs_length with "Ha") as "%Hlenls".

      simpl.
      iApply imp_bind. iApply (imp_load_block_ghost with "Ha").
      iIntros ((t & ls')) "-> /=".
      rewrite signed_repr; last representable.
      rewrite list_lookup_lookup_total_valid; last lia.
      (* Subgoal: [load (a !!! i)] *)
      iPoseProof (slice_lookup_acc i with "Hslice Ha") as "(Hl & Hslice)".
      assumption.
      iApply (imp_load' with "Hl").
      iIntros "!> Hl".
      iApply "Hlookup".
      iApply ("Hslice" with "Hl").
  Qed.

  Lemma imp_EArrayGet' `{Encode A, Inhabited A} {ζ} (a : array) (i j : Z) dq (xs : list A) e1 e2 :
    ⌜j ≤ i < j + length xs⌝ -∗
    ▷ a ↦∗[j]{dq} xs -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a', ⌜a' = a⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ i', ⌜i' = i⌝ }} -∗
    EWP eval η (EArrayGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ (x : A), ⌜x = xs !!! (i - j)⌝ ∗ a ↦∗[j]{dq} xs }}.
  Proof.
    iIntros (Hlen) "Hslice He1 He2".
    iDestruct "Hslice" as "(%ls & #Harr & >%Hlenls & H)".
    iApply (imp_EArrayGet2 with "Harr He1 He2").
    iIntros (?) "->".
    iExists dq, j, xs.
    iSplitL. { iFrame. iFrame "%#". }
    iIntros "!> $ //".
  Qed.

  Lemma imp_EArrayGet `{Encode A, Inhabited A} {ζ} (a : array) (i j : Z) dq (xs : list A) e1 e2 :
    ⌜0 ≤ i < length xs⌝ -∗
    a ↦∗{dq} xs -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a', ⌜a' = a⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ i', ⌜i' = i⌝ }} -∗
    EWP eval η (EArrayGet e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ (x : A), ⌜x = xs !!! i⌝ ∗ a ↦∗{dq} xs }}.
  Proof.
    iIntros (Hlen) "Hown He1 He2".
    iDestruct "Hown" as "(%ls & #Harr & Hblock & Hslice & %Hlenls)".
    iApply (imp_wand with "[- Hblock]").
    { iApply (imp_EArrayGet' with "[%] Hslice He1 He2").
      lia. }
    iIntros (x) "(-> & Hslice)".
    iSplit.
    + iPureIntro. rewrite Z.sub_0_r. reflexivity.
    + iApply (isSlice_ownArray with "Harr Hblock Hslice [%]").
      assumption.
  Qed.

  Lemma imp_EArraySet2 `{Encode A, Inhabited A} {Φ : unit → iProp Σ} {ζ}
    (Φ3 : A → iProp Σ) (Φ1 : array → iProp Σ) (Φ2 : Z → iProp Σ) e1 e2 e3 :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    EWP eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ3  }} -∗
    (∀ a i y, Φ1 a -∗ Φ2 i -∗ Φ3 y -∗
                 ∃ j xs,
                   ▷ (⌜j ≤ i < j + length xs⌝ ∗ a ↦∗[j] xs) ∗
                   ▷ (a ↦∗[j] (<[i - j := y]> xs) -∗ Φ ())) -∗
    EWP eval η (EArraySet e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He1 He2 He3 P". simpl_eval.
    iApply (imp_bind_par (A2:=(Z * A)) with "[He1] [He2 He3]").
    { iApply (imp_as_array with "He1"). }
    { iApply (imp_par with "[He2] He3").
      iApply (imp_as_int with "He2"). }
    iIntros (a (i & y)) "HΦ1 (HΦ2 & HΦ3)".
    iDestruct ("P" with "HΦ1 HΦ2 HΦ3") as
        "(%j & %xs & Hslice & HΦ)". iNext.
    iDestruct "Hslice" as "(%Hbound & Hslice)".
    iPoseProof (isSlice_blockLocs with "Hslice") as "(%ls & #Hblock & %Hbounds)".
    iPoseProof (blockLocs_length with "Hblock") as "%Hlen'".

    iApply imp_bind. { iApply (imp_load_block_ghost with "Hblock"). }
    iIntros ((t & ls')) "-> /=".
    rewrite signed_repr; last representable.
    rewrite list_lookup_lookup_total_valid; last lia.
    (* Subogal: [store (a !!! i) #y] *)
    iPoseProof (slice_insert_acc i with "Hslice Hblock") as "(Hl & Hslice)".
    lia.

    iApply (imp_store' with "Hl").
    iIntros "!> Hl".
    iApply "HΦ".
    iApply ("Hslice" with "Hl").
  Qed.

  Lemma imp_EArraySet' `{Encode A, Inhabited A} {ζ}
    (Φ : A → iProp Σ) (i j : Z) (a : array) xs e1 e2 e3 :
    ⌜j ≤ i < j + length xs ⌝ -∗
    ▷ a ↦∗[j] xs -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a', ⌜a'=a⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ i', ⌜i'=i⌝ }} -∗
    EWP eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    EWP eval η (EArraySet e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ (_ : unit), ∃ y, Φ y ∗ a ↦∗[j] (<[i-j:=y]> xs) }}.
  Proof.
    iIntros (Hbound) "Hslice He1 He2 He3".
    iDestruct "Hslice" as "(%ls & #Harr & >%Hlenls & slice)".
    iApply (imp_EArraySet2 with "He1 He2 He3").
    iIntros (???) "-> -> HΦ".
    iExists j, xs. iSplitL "slice".
    - iFrame. iFrame "%#".
    - iIntros "!> $". iFrame.
  Qed.

  Lemma imp_EArraySet `{Encode A, Inhabited A} {ζ}
    (Φ : A → iProp Σ) (i j : Z) (a : array) xs e1 e2 e3 :
    ⌜0 ≤ i < length xs⌝ -∗
    a ↦∗ xs -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a', ⌜a'=a⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ i', ⌜i'=i⌝ }} -∗
    EWP eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    EWP eval η (EArraySet e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ (_ : unit), ∃ y, Φ y ∗ a ↦∗ (<[i:=y]> xs) }}.
  Proof.
    iIntros (Hbound) "Hown He1 He2 He3".
    iDestruct "Hown" as "(%ls & #Harr & Hblock & Hslice & %Hlenls)".
    iApply (imp_wand with "[- Hblock]").
    { iApply (imp_EArraySet' with "[%] Hslice He1 He2 He3").
      lia. }
    iIntros ([]) "(%y & $ & Hslice)".
    rewrite Z.sub_0_r.
    iApply (isSlice_ownArray with "Harr Hblock Hslice [%]").
    by length.
  Qed.

End array_reasoning.
