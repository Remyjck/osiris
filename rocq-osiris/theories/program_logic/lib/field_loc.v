(* Field locations, and references as one-field records.

   [field_at r f l] is the persistent knowledge that field [f] of the
   record [r] is stored at location [l]. [r ↦[f]{dq} v] owns the
   content of that field, that is, [l ↦ₗ{dq} v]. A reference is a mutable
   record with a single field, so [r ↦{dq} v] is the ownership of field
   [0] of such a record, together with the persistent knowledge of its
   shape. *)

From iris.base_logic.lib Require Import gen_heap.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.

From osiris Require Import base.
From osiris.lang Require Import syntax locations encode.
From osiris.semantics Require Import semantics.
From osiris.utils Require Import list_z dfractional.
Require Import ghost_state block_resources.

(* [gen_heap] exports the joining direction ([pointsto_combine]) but no
   splitting law for a general [dfrac], only the [Qp]-indexed
   [Fractional] instance. We derive it once here; this is the only place
   that has to look through [gen_heap]'s sealing. *)

Lemma pointsto_dsplit {L V Σ} `{Countable L} `{!gen_heapGS L V Σ}
    (l : L) dq1 dq2 (v : V) :
  pointsto l (dq1 ⋅ dq2) v ⊣⊢ pointsto l dq1 v ∗ pointsto l dq2 v.
Proof.
  rewrite gen_heap.pointsto_unseal /gen_heap.pointsto_def
          ghost_map.ghost_map_elem_unseal /ghost_map.ghost_map_elem_def
          -own_op.
  f_equiv. by rewrite -gmap_view.gmap_view_frag_op agree_idemp.
Qed.

Section field_loc.

  Context `{!osirisGS Σ}.

  Definition field_at (r : record) (f : field) (l : loc) : iProp Σ :=
    ∃ ls, blockLocs r ls ∗ ⌜ls !! f = Some l⌝.

  Global Instance field_at_pers r f l : Persistent (field_at r f l).
  Proof. apply _. Qed.

  Lemma field_at_agree r f l1 l2 :
    field_at r f l1 -∗ field_at r f l2 -∗ ⌜l1 = l2⌝.
  Proof.
    iIntros "(%ls1 & Hls1 & %H1) (%ls2 & Hls2 & %H2)".
    iPoseProof (blockLocs_valid with "Hls1 Hls2") as "->".
    iPureIntro. congruence.
  Qed.

  Definition field_pointsto (r : record) (f : field) dq (v : val) : iProp Σ :=
    ∃ l, field_at r f l ∗ l ↦ₗ{dq} v.

  (* [is_ref r]: [r] is a mutable block with exactly one field. *)
  Definition is_ref (r : record) : iProp Σ :=
    blockTag r DfracDiscarded Mut ∗ ∃ l, blockLocs r (list_z.singleton l).

  Global Instance is_ref_pers r : Persistent (is_ref r).
  Proof. unfold record, tc_opaque in r. apply _. Qed.

  Definition ref_pointsto (r : record) dq (v : val) : iProp Σ :=
    is_ref r ∗ field_pointsto r 0 dq v.

End field_loc.

(* Without this, the proofmode looks through the definitions: for instance,
   [iDestruct] would split [r ↦ v] into [is_ref r] and [r ↦[0] v] rather
   than into two fractions. *)
Global Typeclasses Opaque field_at field_pointsto is_ref ref_pointsto.

Notation "r ↦[ f ] dq v" := (field_pointsto r f dq v)
  (at level 20, dq custom dfrac at level 1,
   format "r  ↦[ f ] dq  v") : bi_scope.

Notation "r ↦ dq v" := (ref_pointsto r dq v)
  (at level 20, dq custom dfrac at level 1,
   format "r  ↦ dq  v") : bi_scope.

Section field_loc_laws.

  Context `{!osirisGS Σ}.

  Global Instance field_at_timeless r f l : Timeless (field_at r f l).
  Proof. unfold record, tc_opaque in r. rewrite /field_at. apply _. Qed.

  Global Instance is_ref_timeless r : Timeless (is_ref r).
  Proof. unfold record, tc_opaque in r. rewrite /is_ref. apply _. Qed.

  Global Instance field_pointsto_timeless r f dq v : Timeless (r ↦[f]{dq} v)%I.
  Proof. unfold record, tc_opaque in r. rewrite /field_pointsto /field_at. apply _. Qed.

  Global Instance ref_pointsto_timeless r dq v : Timeless (r ↦{dq} v)%I.
  Proof.
    unfold record, tc_opaque in r.
    rewrite /ref_pointsto /is_ref /field_pointsto /field_at. apply _.
  Qed.

  Global Instance field_pointsto_dfractional r f v :
    DFractional (λ dq, r ↦[f]{dq} v)%I.
  Proof.
    intros dq1 dq2. rewrite /field_pointsto. iSplit.
    - iIntros "(%l & #Hl & Hv)". rewrite pointsto_dsplit.
      iDestruct "Hv" as "[H1 H2]". iSplitL "H1"; iExists l; iFrame "#∗".
    - iIntros "[(%l1 & #Hl1 & H1) (%l2 & #Hl2 & H2)]".
      iPoseProof (field_at_agree with "Hl1 Hl2") as "<-".
      iExists l1. iFrame "#". rewrite pointsto_dsplit. iFrame.
  Qed.

  Global Instance field_pointsto_as_dfractional r f dq v :
    AsDFractional (r ↦[f]{dq} v)%I (λ dq, r ↦[f]{dq} v)%I dq.
  Proof. constructor; done || apply _. Qed.

  Global Instance field_pointsto_fractional r f v :
    Fractional (λ q, r ↦[f]{#q} v)%I.
  Proof. apply (dfractional_fractional (λ dq, r ↦[f]{dq} v)%I). Qed.

  Global Instance field_pointsto_as_fractional r f q v :
    AsFractional (r ↦[f]{#q} v)%I (λ q, r ↦[f]{#q} v)%I q.
  Proof. constructor; done || apply _. Qed.

  Global Instance ref_pointsto_dfractional r v :
    DFractional (λ dq, r ↦{dq} v)%I.
  Proof.
    intros dq1 dq2. rewrite /ref_pointsto field_pointsto_dfractional.
    iSplit.
    - iIntros "(#Hr & H1 & H2)". iFrame "#∗".
    - iIntros "[(#Hr & H1) (_ & H2)]". iFrame "#∗".
  Qed.

  Global Instance ref_pointsto_as_dfractional r dq v :
    AsDFractional (r ↦{dq} v)%I (λ dq, r ↦{dq} v)%I dq.
  Proof. constructor; done || apply _. Qed.

  Global Instance ref_pointsto_fractional r v :
    Fractional (λ q, r ↦{#q} v)%I.
  Proof. apply (dfractional_fractional (λ dq, r ↦{dq} v)%I). Qed.

  Global Instance ref_pointsto_as_fractional r q v :
    AsFractional (r ↦{#q} v)%I (λ q, r ↦{#q} v)%I q.
  Proof. constructor; done || apply _. Qed.

  Lemma field_pointsto_valid_2 r f dq1 dq2 v1 v2 :
    r ↦[f]{dq1} v1 -∗ r ↦[f]{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite /field_pointsto.
    iIntros "(%l1 & #Hl1 & H1) (%l2 & #Hl2 & H2)".
    iPoseProof (field_at_agree with "Hl1 Hl2") as "<-".
    iPoseProof (pointsto_valid_2 with "H1 H2") as "[% %Heq]".
    by simplify_eq.
  Qed.

  Lemma field_pointsto_agree r f dq1 dq2 v1 v2 :
    r ↦[f]{dq1} v1 -∗ r ↦[f]{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    by iDestruct (field_pointsto_valid_2 with "H1 H2") as "[_ $]".
  Qed.

  Lemma field_pointsto_persist r f dq v :
    r ↦[f]{dq} v ==∗ r ↦[f]□ v.
  Proof.
    rewrite /field_pointsto.
    iIntros "(%l & #Hl & Hv)".
    iMod (pointsto_persist with "Hv") as "Hv".
    iModIntro. iExists l. iFrame "#∗".
  Qed.

  Lemma ref_pointsto_valid_2 r dq1 dq2 v1 v2 :
    r ↦{dq1} v1 -∗ r ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite /ref_pointsto.
    iIntros "(_ & H1) (_ & H2)".
    iApply (field_pointsto_valid_2 with "H1 H2").
  Qed.

  Lemma ref_pointsto_agree r dq1 dq2 v1 v2 :
    r ↦{dq1} v1 -∗ r ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    rewrite /ref_pointsto.
    iIntros "(_ & H1) (_ & H2)".
    iApply (field_pointsto_agree with "H1 H2").
  Qed.

  Lemma ref_pointsto_persist r dq v :
    r ↦{dq} v ==∗ r ↦□ v.
  Proof.
    rewrite /ref_pointsto.
    iIntros "(#Hr & H)".
    iMod (field_pointsto_persist with "H") as "H".
    iModIntro. iFrame "#∗".
  Qed.

  (* The locations of a block give those of its fields. *)

  Lemma blockLocs_field_at r ls f :
    list_z.valid f ls → blockLocs r ls -∗ field_at r f (ls !!! f).
  Proof.
    iIntros (Hvalid) "#Hls". rewrite /field_at. iExists ls. iFrame "Hls".
    iPureIntro. by apply list_lookup_lookup_total_valid.
  Qed.

  (* Once the location of a field is known, the field is that cell. *)

  Lemma field_pointsto_at r f l dq v :
    field_at r f l -∗ (r ↦[f]{dq} v ∗-∗ l ↦ₗ{dq} v).
  Proof.
    iIntros "#Hl". rewrite /field_pointsto. iSplit.
    - iIntros "(%l' & #Hl' & Hv)".
      by iPoseProof (field_at_agree with "Hl Hl'") as "<-".
    - iIntros "Hv". iExists l. iFrame "#∗".
  Qed.

  Lemma is_ref_field_at r :
    is_ref r -∗ ∃ l, field_at r 0 l ∗ blockLocs r (list_z.singleton l).
  Proof.
    rewrite /is_ref /field_at. iIntros "(_ & %l & #Hls)".
    iExists l. iSplit; last done.
    iExists (list_z.singleton l). iFrame "Hls".
    iPureIntro. apply list_lookup_singleton_eq_0.
  Qed.

  Lemma ref_pointsto_is_ref r dq v :
    r ↦{dq} v ⊢ is_ref r ∗ r ↦{dq} v.
  Proof. rewrite /ref_pointsto. iIntros "[#$ $]". Qed.

  (* The field view of a reference: its only field is at the location
     recorded in its block. *)

  Lemma ref_pointsto_unfold r dq v :
    r ↦{dq} v ⊣⊢
    blockTag r DfracDiscarded Mut ∗ ∃ l, blockLocs r (list_z.singleton l) ∗ l ↦ₗ{dq} v.
  Proof.
    unfold record, tc_opaque in r.
    rewrite /ref_pointsto /is_ref /field_pointsto /field_at. iSplit.
    - iIntros "((#Htag & %l & #Hls) & %l' & (%ls & #Hls' & %Hf) & Hv)".
      iPoseProof (blockLocs_valid with "Hls Hls'") as "->".
      rewrite list_lookup_singleton_eq_0 in Hf. simplify_eq. iFrame "#∗".
    - iIntros "(#Htag & %l & #Hls & Hv)".
      iFrame "#∗". by rewrite list_lookup_singleton_eq_0.
  Qed.

  (* Once the location of its field is known, a reference is that cell. *)

  Lemma ref_pointsto_at r l dq v :
    blockLocs r (list_z.singleton l) -∗
    (r ↦{dq} v ∗-∗ blockTag r DfracDiscarded Mut ∗ l ↦ₗ{dq} v).
  Proof.
    unfold record, tc_opaque in r.
    iIntros "#Hls". rewrite ref_pointsto_unfold. iSplit.
    - iIntros "(#Htag & %l' & #Hls' & Hv)".
      iPoseProof (blockLocs_valid with "Hls Hls'") as "%Heq".
      apply (f_equal (λ ls, ls !! 0%Z)) in Heq.
      rewrite !list_lookup_singleton_eq_0 in Heq. simplify_eq. iFrame "#∗".
    - iIntros "(#Htag & Hv)". iFrame "#∗".
  Qed.

End field_loc_laws.
