(* The resources describing a memory block, for arrays and records alike.

   [blockLocs a ls] is the persistent knowledge that block [a] has element
   locations [ls], read from the block ghost map. It never changes, so it can
   be shared freely between threads. [blockTag a dq t] is (a fraction of) the
   heap cell of [a], which records its mutability tag [t]; changing the tag
   needs all of it. *)

From iris.base_logic.lib Require Import gen_heap.
From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import thread_ids syntax locations encode.
From osiris.semantics Require Import semantics.
Require Import ghost_state.

Definition blockTag `{osirisGS Σ} (b : locations.loc) dq t : iProp Σ :=
  ∃ ls, gen_heap.pointsto b dq (Block t ls).

(* Taking a freshly allocated block's exclusive tag to the persistent
   form above. Every block that enters a shared invariant goes through
   this. *)

Lemma blockTag_persist `{osirisGS Σ} b t :
  blockTag b (DfracOwn 1) t ==∗ blockTag b DfracDiscarded t.
Proof.
  iIntros "H".
  iDestruct "H" as (ls) "H".
  iMod (gen_heap.pointsto_persist with "H") as "H".
  iModIntro. iExists ls. iFrame.
Qed.

Section block_locs.

  Context `{!osirisGS Σ}.

  (* [blockLocs a ls] is the persistent ghost knowledge that block [a] has locations [ls]. *)
  Definition blockLocs (a : loc) (ls : list locations.loc) : iProp Σ :=
    (block_map_elem (osiris_block_name Σ) a ls ∗ ⌜(list_z.length ls ≤ int.max_array_length)%Z⌝)%I.

  Global Instance blockLocs_pers a ls : Persistent (blockLocs a ls).
  Proof. apply _. Qed.

  Global Instance blockLocs_pers_array (a : syntax.array) ls : Persistent (blockLocs a ls) :=
    blockLocs_pers a ls.

  Global Instance blockLocs_pers_record (a : syntax.record) ls : Persistent (blockLocs a ls) :=
    blockLocs_pers a ls.

  Lemma blockLocs_valid a ls1 ls2 :
    blockLocs a ls1 -∗ blockLocs a ls2 -∗ ⌜ls2 = ls1⌝.
  Proof.
    iIntros "(Ha & _) (Ha' & _)".
    iPoseProof (block_map_elem_agree with "Ha Ha'") as "%H".
    iPureIntro. exact (eq_sym H).
  Qed.

  Lemma blockLocs_length a ls :
    blockLocs a ls -∗ ⌜(list_z.length ls ≤ int.max_array_length)%Z⌝.
  Proof. iIntros "(_ & $)". Qed.

End block_locs.
