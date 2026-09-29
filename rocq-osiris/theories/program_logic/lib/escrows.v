From iris Require Import gen_heap proofmode.proofmode token invariants.
From osiris Require Import lang program_logic.ewp.

(* This section complements iris.bi.big_op *)
Section big_op.
  Context {PROP : bi}.

  Section sep_list.
    Context {A : Type}.
    Implicit Types l : list A.
    Implicit Types Φ Ψ : nat → A → PROP.

    (* Move a persistent proposition into each term of a [big_sepL] *)
    Lemma pers_big_sepL P Φ l :
      □ P ∗ ([∗ list] k ↦ y ∈ l, Φ k y) ⊢ [∗ list] k ↦ y ∈ l, □ P ∗ Φ k y.
    Proof.
      revert Φ.
      induction l as [ | x l ]; auto; intros Φ.
      iIntros "/= (#$ & $ & HS)". iApply IHl; auto.
    Qed.

    (* [big_sepL_mono] but provides a persistent proposition in the premise *)
    Lemma big_sepL_mono_pers P Φ Ψ l :
      (∀ k y, l !! k = Some y → □ P ∗ Φ k y ⊢ Ψ k y) →
      □ P ∗ ([∗ list] k ↦ y ∈ l, Φ k y) ⊢ [∗ list] k ↦ y ∈ l, Ψ k y.
    Proof.
      iIntros (H) "?".
      iApply big_sepL_mono. apply H.
      by iApply pers_big_sepL.
    Qed.
  End sep_list.

  Section sep_list2.
    Context {A B : Type}.

    (* [big_sepL2_const_sepL_l] but length equality is a premise instead, so
    that it does not need to appear in the goal before rewriting *)
    Lemma big_sepL2_const_sepL_l' (Φ : nat → A → PROP) (l1 : list A) (l2 : list B) :
      length l1 = length l2 →
      ([∗ list] k↦y1;_ ∈ l1;l2, Φ k y1) ⊣⊢ ([∗ list] k↦y1 ∈ l1, Φ k y1).
    Proof.
      intros.
      rewrite big_sepL2_const_sepL_l.
      iSplit; auto.
      iIntros "(_ & $)".
    Qed.

    (* similarly corresponding to [big_sepL2_const_sepL_r] *)
    Lemma big_sepL2_const_sepL_r' (Φ : nat → B → PROP) (l1 : list A) (l2 : list B) :
      length l1 = length l2 →
      ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y2) ⊣⊢ ([∗ list] k↦y2 ∈ l2, Φ k y2).
    Proof.
      intros.
      rewrite big_sepL2_const_sepL_r.
      iSplit; auto.
      iIntros "(_ & $)".
    Qed.

    (* similarly corresponding to [big_sepL2_alt] *)
    Lemma big_sepL2_alt' (Φ : nat → A → B → PROP) (l1 : list A) (l2 : list B) :
        length l1 = length l2 →
        ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2)
          ⊣⊢ ([∗ list] k↦xy ∈ zip l1 l2, Φ k xy.1 xy.2).
    Proof.
      intros; rewrite big_sepL2_alt. iSplit. by iIntros "(_ & $)". by iIntros "$".
    Qed.
  End sep_list2.
End big_op.



Section escrows.

  Context `{!osirisGS Σ}.
  Context (N : namespace).

  (* An escrow for a resource [R], that do not yet have at the time of applying
     this lemma, is a persistent formula [E] with an introduction rule and an
     elimination rule. The introduction rule consumes [R] and produces [□E],
     which can be freely shared, and the elimination implication, itself a
     resource, 'consumes' [E] and produces [R] *)
  Lemma alloc_escrow (R : iProp Σ) :
    ⊢ |={∅}=> ∃ E, (▷R -∗ |={∅}=> □ E) ∗ (E -∗ |={↑N}=> ▷R).
  Proof.
    (* The escrow is just an invariant of the form "token or R". The token is
       allocated now (at fork time) but the invariant will only be allocated
       when the resource has been provided (i.e. when the forked thread
       terminates). *)
    iDestruct token_alloc as "> (%γ & Hγ)".
    iExists (inv N (token γ ∨ R)).
    iSplitR.
    - (* Intro: we have [R], the resource produced by the child process *)
      iIntros "!> H".
      iMod (inv_alloc N _ (token γ ∨ R) with "[$]") as "#Hinv". auto.
    - (* Elim: by joining the child process, we will get ownership of the
      invariant it allocated, so we can assume it in the elimination rule *)
      iIntros "!> Hinv".
      iInv "Hinv" as "[Htok | Hφ]".
      + iAssert (▷ False)%I with "[-]" as "#F".
        * iNext. iApply (token_exclusive with "[$] [$]").
        * iSplitL; auto.
      + iModIntro. iSplitL "Hγ"; auto.
  Qed.

  (* For two resources, we can use the same formula with one intro rule (the
  resources are relinquished at the same time) and two elimination resources, so
  that resources can be recovered from the escrow by different threads. *)
  Lemma alloc_escrow_2 (φ1 φ2 : iProp Σ) :
    ⊢ |={∅}=> ∃ ψ, (▷φ1 ∗ ▷φ2 -∗ |={∅}=> □ ψ) ∗ (ψ -∗ |={↑N}=> ▷φ1) ∗ (ψ -∗ |={↑N}=> ▷φ2).
  Proof.
    iMod (alloc_escrow φ1) as "(%E1 & i1 & e1)".
    iMod (alloc_escrow φ2) as "(%E2 & i2 & e2)".
    iModIntro.
    iExists (E1 ∗ E2)%I.
    iSplitL "i1 i2".
    - iIntros "(r1 & r2)".
      iMod ("i1" with "r1") as "#$".
      iMod ("i2" with "r2") as "#$".
      done.
    - iSplitL "e1".
      + iIntros "(H1 & H2)". by iApply "e1".
      + iIntros "(H1 & H2)". by iApply "e2".
  Qed.

  (* Allocate a finite number of tokens *)
  Lemma tokens_alloc n :
    ⊢ |={∅}=> ∃ ts : list (iProp Σ),
    ⌜length ts = n⌝ ∗ [∗ list] t ∈ ts, t ∗ (t ∗ t -∗ False).
  Proof.
    induction n.
    - iExists nil; auto.
    - iDestruct token_alloc as "> (%γ & Hγ)".
      iPoseProof IHn as "> (%l & % & Hl)".
      iExists (token γ :: l); simpl. iModIntro.
      iSplit; auto; iFrame.
      iIntros "(? & ?)". iApply (token_exclusive with "[$] [$]").
  Qed.

  (* Make a escrow for a list of resources *)
  Lemma alloc_escrow_list (φs : list (iProp Σ)) :
    ⊢ |={∅}=> ∃ ψ,
      □(([∗list] φ ∈ φs, ▷φ) -∗ |={∅}=> □ ψ)
       ∗ [∗list] φ ∈ φs, (ψ -∗ |={↑N}=> ▷ φ).
  Proof.
    (* This proof could be simplified by using several times [alloc_escrow], we
    keep it this way for now because it might be more robust with respect to
    changes of [joinable] *)
    iDestruct (tokens_alloc (length φs)) as "> (%ts & % & Hts)".
    iExists (inv N ([∗list] φ; t ∈ φs; ts, t ∨ φ)).
    iSplitR.
    - iIntros "!> !> H".
      iMod (inv_alloc N _ ([∗ list] φ;t ∈ φs;ts, t ∨ φ) with "[H]") as "#Hinv"; auto.
      iApply (big_sepL2_mono (λ _ φ _, φ)); auto.
      rewrite big_sepL2_const_sepL_l -big_sepL_later. auto.
    - iModIntro.
      rewrite -big_sepL2_const_sepL_r' //.
      rewrite -big_sepL2_const_sepL_l' //.
      iApply (big_sepL2_mono with "Hts").
      iIntros (k φ t Eφ Ek) "(Ht & Hexcl) Hinv".
      iInv "Hinv" as "Hs".
      iModIntro.
      rewrite big_sepL2_alt' //.
      set (z := zip _ _).
      assert (Zk : z !! k = Some (φ, t)) by now apply lookup_zip_with_Some; eauto.
      subst z.
      apply list_elem_of_split_length in Zk.
      destruct Zk as (l1 & l2 & -> & Hk). change ((φ, t) :: l2) with ([(φ, t)] ++ l2).
      rewrite !big_sepL_app big_sepL_singleton /=.
      iDestruct "Hs" as "(Before & Hescr & After)".
      iAssert (▷ (t ∗ φ))%I with "[Ht Hexcl Hescr]" as "(Ht & Hφ)".
      { iNext. iDestruct "Hescr" as "[? | $]".
        - iDestruct ("Hexcl" with "[$]") as "[]".
        - iFrame. }
      iSplitR "Hφ". iFrame. done.
  Qed.

End escrows.
