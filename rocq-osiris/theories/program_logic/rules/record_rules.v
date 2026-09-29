From iris Require Import gen_heap proofmode.proofmode.
From iris.bi.lib Require Import fractional.
From osiris Require Import lang type_nel.
Require Import osiris_utils.
Require Import ewp.
Require Import impure_rules stop_rules.
From osiris.utils Require Import list_z big_opLZ dfractional.

(** This file defines record resource predicates and [EWP] rules for record expressions. *)

(* [record] is [tc_opaque loc]; expose [loc]'s instances *)
Global Instance record_eq_decision : EqDecision record.
Proof. unfold record; simpl. apply _. Defined.
Global Instance record_countable : Countable record.
Proof. unfold record; simpl. apply _. Defined.
Global Instance record_inhabited : Inhabited record.
Proof. unfold record; simpl; apply _. Defined.

Section record_resources.

  Context `{!osirisGS Σ}.

  (* [ownBlock r dq t xs] is the representation predicate for a block of memory:
     - [r] is the location at which the block is stored
     - [dq] is the (possibly discarded) fraction of the ownership carried
     - [t] is the tag [Mut/Immut] of the block (for allowing physical equality)
     - [xs] is the logical representation of the block as a tuple

     The fraction is a [dfrac] rather than a [Qp] so that a block whose
     contents will never change again can be shared persistently, at
     [DfracDiscarded].

     The mutability tag is held *persistently*, at [isBlockP], rather than
     at [dq], which governs the fields only. Tying the two together would
     make [ownBlock] unusable for any block compared physically or CASed
     on, since [compare_and_set_spec] needs a tag witness that outlives the
     atomic step it was read at, and
     [isBlock r DfracDiscarded t ∗ isBlock r (DfracOwn 1) t] is
     [isBlock r (DfracBoth 1) t], which is invalid. Clients that need to
     *change* a tag must hold the exclusive [isBlock] themselves;
     [imp_ERecord] hands it back for that reason. *)

  Definition ownBlock {τ : types} (r : record) dq (t : mut_tag) (xs : τ) : iProp Σ :=
    ∃ ls, isBlockLocs r ls ∗ isBlock r DfracDiscarded t ∗
      [∗ listZ] l;v ∈ ls; (to_vals xs), l ↦{dq} v.

End record_resources.

Section record_resources_frac.

  Context `{!osirisGS Σ}.

  (* [gen_heap] exports the joining direction ([pointsto_combine]) but no
     splitting law for a general [dfrac], only the [Qp]-indexed
     [Fractional] instance. We derive it once here; this is the only
     place that has to look through [gen_heap]'s sealing. *)

  Local Lemma pointsto_dsplit {L V} `{Countable L} `{!gen_heapGS L V Σ}
      (l : L) dq1 dq2 (v : V) :
    pointsto l (dq1 ⋅ dq2) v ⊣⊢ pointsto l dq1 v ∗ pointsto l dq2 v.
  Proof.
    rewrite gen_heap.pointsto_unseal /gen_heap.pointsto_def
            ghost_map.ghost_map_elem_unseal /ghost_map.ghost_map_elem_def
            -own_op.
    f_equiv. by rewrite -gmap_view.gmap_view_frag_op agree_idemp.
  Qed.

  Global Instance isBlock_dfractional (b : locations.loc) t :
    DFractional (λ dq, isBlock b dq t).
  Proof.
    intros dq1 dq2. unfold isBlock. iSplit.
    - iIntros "(%ls & Hb)".
      rewrite pointsto_dsplit.
      iDestruct "Hb" as "[Hb1 Hb2]".
      iSplitL "Hb1"; iExists ls; iFrame.
    - iIntros "([%ls1 Hb1] & [%ls2 Hb2])".
      iPoseProof (gen_heap.pointsto_agree with "Hb1 Hb2") as "%Heq". simplify_eq.
      iExists ls2. rewrite pointsto_dsplit. iFrame.
  Qed.

  (* [record] is typeclass-opaque, so the previous instance does not apply
     to [record]-typed arguments; restate it. *)
  Global Instance isBlock_dfractional_rec (r : record) t :
    DFractional (λ dq, isBlock r dq t) := isBlock_dfractional r t.

  Global Instance isBlock_pers (r : record) t : Persistent (isBlock r DfracDiscarded t).
  Proof. unfold record in r. unfold tc_opaque in r. apply _. Qed.

  Global Instance ownBlock_dfractional {τ : types} (r : record) t (xs : τ) :
    DFractional (λ dq, ownBlock r dq t xs).
  Proof.
    intros dq1 dq2. unfold ownBlock. iSplit.
    - iIntros "(%ls & #Hblock & #Htag & Hxs)".
      iAssert ([∗ listZ] l;v ∈ ls; (to_vals xs), l ↦{dq1} v ∗ l ↦{dq2} v)%I
        with "[Hxs]" as "Hxs'".
      { iApply (big_sepLZ2_mono with "Hxs").
        intros k l v _ _. rewrite pointsto_dsplit. iIntros "[Hl1 Hl2]". iFrame. }
      rewrite big_sepLZ2_sep.
      iDestruct "Hxs'" as "[Hxs1 Hxs2]".
      iSplitL "Hxs1"; iExists ls; iFrame "#∗".
    - iIntros "([%ls1 (#Hblock1 & #Htag1 & Hxs1)] & [%ls2 (#Hblock2 & _ & Hxs2)])".
      iPoseProof (isBlockLocs_valid with "Hblock1 Hblock2") as "<-".
      iExists ls2. iFrame "Hblock1 Htag1".
      iAssert ([∗ listZ] l;v ∈ ls2; to_vals xs, l ↦{dq1} v ∗ l ↦{dq2} v)%I
        with "[Hxs1 Hxs2]" as "Hxs".
      { rewrite big_sepLZ2_sep. iFrame. }
      iApply (big_sepLZ2_mono with "Hxs").
      intros k l v _ _. rewrite pointsto_dsplit. iIntros "$".
  Qed.

  (* [AsDFractional] is what lets the proofmode split these at an
     abstract [dfrac] (see [into_sep_dfractional]). *)

  Global Instance isBlock_as_dfractional (b : locations.loc) dq t :
    AsDFractional (isBlock b dq t) (λ dq, isBlock b dq t) dq.
  Proof. constructor; done || apply _. Qed.

  Global Instance isBlock_as_dfractional_rec (r : record) dq t :
    AsDFractional (isBlock r dq t) (λ dq, isBlock r dq t) dq :=
    isBlock_as_dfractional r dq t.

  Global Instance ownBlock_as_dfractional {τ : types} (r : record) dq t (xs : τ) :
    AsDFractional (ownBlock r dq t xs) (λ dq, ownBlock r dq t xs) dq.
  Proof. constructor; done || apply _. Qed.

  (* The [Qp]-indexed instances Iris's proofmode uses ([iSplitL],
     [iCombine], [iDestruct "H" as "[H1 H2]"]) are now consequences of the
     [dfrac] ones. [Φ] has to be supplied explicitly; see the comment on
     [dfractional_fractional]. *)

  Global Instance isBlock_fractional (b : locations.loc) t :
    Fractional (λ q, isBlock b (DfracOwn q) t).
  Proof. apply (dfractional_fractional (λ dq, isBlock b dq t)). Qed.

  Global Instance isBlock_as_fractional (b : locations.loc) q t :
    AsFractional (isBlock b (DfracOwn q) t) (λ q, isBlock b (DfracOwn q) t) q.
  Proof. constructor; done || apply _. Qed.

  Global Instance ownBlock_fractional {τ : types} (r : record) t (xs : τ) :
    Fractional (λ q, ownBlock r (DfracOwn q) t xs).
  Proof. apply (dfractional_fractional (λ dq, ownBlock r dq t xs)). Qed.

  Global Instance ownBlock_as_fractional {τ : types} (r : record) q t (xs : τ) :
    AsFractional (ownBlock r (DfracOwn q) t xs) (λ q, ownBlock r (DfracOwn q) t xs) q.
  Proof. constructor; done || apply _. Qed.

  (* At the discarded fraction the block is freely duplicable. It is not
     declared [Persistent]: that search bottoms out in [Persistent]
     instances for [ghost_map_elem]/[pointsto] keyed on [locations.loc],
     which do not fire for the typeclass-opaque [record]. Duplication is
     what clients actually need, and it comes straight from the
     [DFractional] law. *)

  Lemma ownBlock_discarded_dup {τ : types} (r : record) t (xs : τ) :
    ownBlock r DfracDiscarded t xs ⊣⊢
    ownBlock r DfracDiscarded t xs ∗ ownBlock r DfracDiscarded t xs.
  Proof. apply (dfractional_discarded_dup (λ dq, ownBlock r dq t xs)). Qed.

End record_resources_frac.

Section records_reasoning.

  Context `{!osirisGS Σ}.

  Context {η : env} {E : coPset} {Ψ : iEff Σ}.
  Implicit Types ζ : exn → iProp Σ.

  Lemma imp_as_record {ζ} {Φ : record → iProp Σ} (m : microvx) :
    EWP m @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    impure E (as_record m) Ψ ζ Φ.
  Proof.
    iIntros "Hm".
    iApply (imp_bind with "Hm").
    iIntros (r) "HΦ".
    iApply (imp_ret with "HΦ"). encode.
  Qed.

  Local Instance notval_listval : NotVal (list val) := {}.

  Lemma imp_ERecord {τ : types} {ζ} (Φs : τ -#> iProp Σ) t es :
    τ_length τ ≤ max_array_length →
    impure E (evals η es) Ψ ζ Φs -∗
    impure E (eval η (ERecord t es)) Ψ ζ
      (λ r, ∃# (xs : τ), ownBlock r (DfracOwn 1) t xs ∗ Φs xs).
  Proof.
    iIntros "%Hlength Hes". simpl_eval.
    iApply (imp_bind with "Hes").
    iIntros (xs) "HΦs".
    iApply (imp_bind (A1:=list loc)).
    { simpl.
      replace (to_vals xs) with
      (@observe (list val) (list val) (@observe_list val Encode_val) (to_vals xs)).
      iApply (@imp_allocn _ _ _ _ _ val Encode_val (λ ls, [∗ listZ] l;v ∈ ls; (to_vals xs), l ↦ v)%I (to_vals xs)).
      iIntros "!>" (ls) "$".
      simpl. rewrite map_id. reflexivity. }
    iIntros (ls) "Hls".
    iPoseProof (big_sepLZ2_length with "Hls") as "%Hlength_ls".
    iApply imp_bind.
    { iApply imp_alloc_block.
      iPureIntro. simpl.
      rewrite Hlength_ls. rewrite to_vals_length. assumption. }
    iIntros (r) "(Hmut & Hblocks)".
    (* [ownBlock] carries the tag persistently, so discard it here. This
       is the point of no return for freezing: once a persistent [Mut]
       witness exists, changing the tag would falsify it, and [dfrac]
       enforces that by making [DfracOwn 1] unreachable afterwards. There
       is no freeze rule for records ([EFreeze] is [array]-typed), so
       nothing is lost. *)
    iMod (isBlock_persist with "Hmut") as "#Htag".
    iApply imp_ret. encode.
    rewrite bi_texist_equiv. iFrame "∗#".
  Qed.

  Lemma imp_ERecordAccess2 {τ : types} {ζ} f {Φ : (τ !!! f) → iProp Σ} r ls e :
    ▷ isBlockLocs r ls -∗
    impure E (eval η e) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    (∃ dq t (xs : τ),
      ▷ (⌜valid_field f τ⌝ ∗ ownBlock r dq t xs) ∗
      ▷ (ownBlock r dq t xs -∗ Φ (xs !!τ f))) -∗
    impure E (eval η (ERecordAccess e f)) Ψ ζ Φ.
  Proof.
    iIntros "#Hblock He P". simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_record with "He"). }
    iIntros (?) "->".
    iDestruct "P" as
        "(%dq & %t & %xs & P1 & P2)".
    iCombine "Hblock P1 P2" as "P".

    iApply (imp_bind (A1:=(mut_tag * list loc)) with "[P]").
    { iApply (imp_load_block_ghost' with "Hblock P"). }
    iIntros ((? & ?)) "(-> & #Hblock' & (%Hvalid_field & Hown) & HΦ) /=".
    iClear "Hblock".

    iDestruct "Hown" as "(%ls' & #Hblock & Htag & Hxs)".
    iPoseProof (isBlockLocs_valid with "Hblock' Hblock") as "->".
    iPoseProof (isBlockLocs_length with "Hblock") as "%Hlen".
    iPoseProof (big_sepLZ2_length with "Hxs") as "%Hlen_xs".
    assert (valid f ls) as Hvalid.
    { destruct Hvalid_field. split; first lia.
      rewrite Hlen_xs to_vals_length. assumption. }

    rewrite (list_lookup_lookup_total_valid ls f Hvalid).

    iPoseProof (big_sepLZ2_lookup_acc _ ls (to_vals xs) f with "Hxs") as "(Hx & Hxs)".
    { apply list_lookup_lookup_total_valid. assumption. }
    { instantiate (1:= #(xs !!τ f)).
      transitivity (@Some val ((to_vals xs) !!! f)).
      - apply list_lookup_lookup_total_valid.
        rewrite <- Hlen_xs. assumption.
      - f_equal.
        apply lookup_total_to_vals. }
    iApply (imp_load' with "Hx").
    iIntros "!> Hx".
    iApply "HΦ".
    iExists ls. iFrame "∗#".
    iApply ("Hxs" with "Hx").
  Qed.

  Lemma imp_ERecordAccess {τ : types} {ζ} (r : record) f dq t (xs : τ) e :
    valid_field f τ →
    ▷ ownBlock r dq t xs -∗
    impure E (eval η e) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    impure E (eval η (ERecordAccess e f)) Ψ ζ
      (λ (x : τ !!! f), ⌜x = xs !!τ f⌝  ∗ ownBlock r dq t xs).
  Proof.
    iIntros (Hvalid_field) "Hown He".
    iDestruct "Hown" as "(%ls & #Hblock & Htag & Hxs)".
    iApply (imp_ERecordAccess2 with "Hblock He").
    iExists dq, t, xs.
    iSplitL "Htag Hxs"; iNext.
    - iFrame "∗#%".
    - iIntros "$ //".
  Qed.

  (* [EAtomicLoc e f] returns the location of the field [f] of the record
     [e] as a first-class value. Only the persistent ghost knowledge
     [isBlockLocs] is required: no ownership of the fields is needed. This
     is essential in concurrent settings, where this ownership is typically
     governed by an invariant. The atomic rules (load, store, CAS, FAA)
     then apply to the returned location. *)

  Lemma imp_EAtomicLoc {ζ} {Φ : loc → iProp Σ} f r ls e :
    valid f ls →
    ▷ isBlockLocs r ls -∗
    impure E (eval η e) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    ▷ Φ (ls !!! f) -∗
    impure E (eval η (EAtomicLoc e f)) Ψ ζ Φ.
  Proof.
    iIntros (Hvalid) "#Hblock He HΦ". simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_record with "He"). }
    iIntros (?) "->".
    iApply (imp_bind (A1:=(mut_tag * list loc)) with "[HΦ]").
    { iApply (imp_load_block_ghost' with "Hblock HΦ"). }
    iIntros ((? & ?)) "(-> & HΦ) /=".
    rewrite (list_lookup_lookup_total_valid ls f Hvalid).
    iApply (imp_ret with "HΦ"). encode.
  Qed.

  Lemma imp_ERecordAccess_pers {ζ} `{Encode A} f {Φ : A → iProp Σ} r ls dq (v : A) e :
    valid f ls →
    ▷ isBlockLocs r ls -∗
    impure E (eval η e) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    ▷ (ls !!! f) ↦{dq} #v -∗
    ▷ ((ls !!! f) ↦{dq} #v -∗ Φ v) -∗
    impure E (eval η (ERecordAccess e f)) Ψ ζ Φ.
  Proof.
    iIntros (Hvalid) "#Hblock He Hl HΦ". simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_record with "He"). }
    iIntros (?) "->".
    iApply (imp_bind (A1:=(mut_tag * list loc)) with "[]").
    { iApply (imp_load_block_ghost with "Hblock"). }
    iIntros ([? ?]) "-> /=".
    rewrite (list_lookup_lookup_total_valid ls f Hvalid).
    iApply (imp_load' with "Hl").
    iIntros "!> Hl".
    iApply ("HΦ" with "Hl").
  Qed.

  Lemma imp_ERecordSet2 {τ : types} {ζ} f {Φ : unit → iProp Σ} (Φ1 : record → iProp Σ) (Φ2 : τ !!! f → iProp Σ) e1 e2 :
    impure E (eval η e1) Ψ ζ Φ1 -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    (∀ r a, Φ1 r -∗ Φ2 a -∗
            ∃ t (xs : τ),
              ▷ (⌜valid_field f τ⌝ ∗ ownBlock r (DfracOwn 1) t xs) ∗
              ▷ (ownBlock r (DfracOwn 1) t <[f τ= a]> xs -∗ Φ ())) -∗
    impure E (eval η (ERecordSet e1 f e2)) Ψ ζ Φ.
  Proof.
    iIntros "He1 He2 P". simpl_eval.
    iApply (imp_bind_par with "[He1] He2").
    { iApply (imp_as_record with "He1"). }
    iIntros (r a) "HΦ1 HΦ2".
    iDestruct ("P" with "HΦ1 HΦ2") as
        "(%j & %xs & Hown & HΦ)". iNext.
    iDestruct "Hown" as "(%Hvalid_field & Hown)".
    iDestruct "Hown" as "(%ls & #Hblock & Htag & Hxs)".
    iPoseProof (isBlockLocs_length with "Hblock") as "%Hlen_ls".
    iPoseProof (big_sepLZ2_length with "Hxs") as "%Hlen_xs".

    iApply imp_bind. { iApply (imp_load_block_ghost with "Hblock"). }
    iIntros ((t & ls')) "-> /=".

    assert (valid f ls) as Hvalid.
    { destruct Hvalid_field. split; first lia.
      rewrite Hlen_xs to_vals_length. assumption. }

    rewrite (list_lookup_lookup_total_valid ls f Hvalid).

    iPoseProof (big_sepLZ2_insert_acc _ ls (to_vals xs) f with "Hxs") as "(Hx & Hxs)".
    { apply list_lookup_lookup_total_valid. assumption. }
    { instantiate (1:= #(xs !!τ f)).
      transitivity (@Some val ((to_vals xs) !!! f)).
      - apply list_lookup_lookup_total_valid.
        rewrite <- Hlen_xs. assumption.
      - f_equal.
        apply lookup_total_to_vals. }
    iApply (imp_store' with "Hx").
    iIntros "!> Hx".
    iApply "HΦ".
    iExists ls. iFrame "∗#".
    iSpecialize ("Hxs" with "Hx").
    update. rewrite insert_to_vals.
    iApply "Hxs".
  Qed.

  Lemma imp_ERecordSet {τ : types} {ζ} f (Φ : τ !!! f → iProp Σ) (r : record) t (xs : τ) e1 e2 :
    valid_field f τ →
    ▷ ownBlock r (DfracOwn 1) t xs -∗
    impure E (eval η e1) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ Φ -∗
    impure E (eval η (ERecordSet e1 f e2)) Ψ ζ
      (λ (_ : unit), ∃ a, Φ a ∗ ownBlock r (DfracOwn 1) t (<[f τ= a]> xs)).
  Proof.
    iIntros (Hvalid_field) "Hown He1 He2".
    iApply (imp_ERecordSet2 with "He1 He2").
    iIntros (? a) "-> HΦ".
    iFrame "∗%".
    iIntros "!> Hown".
    iFrame.
  Qed.

End records_reasoning.

(* So far, our logical model of records has been tuples. Although this
   is sufficiently expressive for most purposes, we can allow users to
   provide their own logical model by mapping to our tuples. *)

Section encoded_fields.

  Context `{!osirisGS Σ}.

  (* [RecordRepr A τ t] ties a logical model type [A] to a record with
     fields described by [τ] and with mutable tag [t]. *)

  (* For example, a record type [point := { x : Z; y : Z }] would need
     an instance [RecordRepr point τ[Z; Z] (Mut/Immut)]. *)

  Class RecordRepr (A : Type) (τ : types) (t : mut_tag) :=
    { repr_to_types : A → τ;
      types_to_repr : τ -#> A;
      repr_id : ∀ xs, (repr_to_types ∘ types_to_repr) xs = xs }.

  (* [ownRecord] defines the ownership of a record with logical model [a : A]. *)

  Definition ownRecord `{RecordRepr A τ t} (r : record) dq (a : A) : iProp Σ :=
    ownBlock (τ:=τ) r dq t (repr_to_types a).

  Global Instance ownRecord_dfractional `{RecordRepr A τ t} r (a : A) :
    DFractional (λ dq, ownRecord r dq a) := _.

  Global Instance ownRecord_as_dfractional `{RecordRepr A τ t} r dq (a : A) :
    AsDFractional (ownRecord r dq a) (λ dq, ownRecord r dq a) dq.
  Proof. constructor; done || apply _. Qed.

  Global Instance ownRecord_fractional `{RecordRepr A τ t} r (a : A) :
    Fractional (λ q, ownRecord r (DfracOwn q) a).
  Proof. apply (dfractional_fractional (λ dq, ownRecord r dq a)). Qed.

  Global Instance ownRecord_as_fractional `{RecordRepr A t} (r : record) q (a : A) :
    AsFractional (ownRecord r (DfracOwn q) a) (λ q, ownRecord r (DfracOwn q) a) q.
  Proof. constructor; done || apply _. Qed.

  Lemma ownRecord_discarded_dup `{RecordRepr A τ t} (r : record) (a : A) :
    ownRecord r DfracDiscarded a ⊣⊢
    ownRecord r DfracDiscarded a ∗ ownRecord r DfracDiscarded a.
  Proof. apply (dfractional_discarded_dup (λ dq, ownRecord r dq a)). Qed.

  (* -------------------------------------------------------------------------- *)

  (* We can now redefine reasoning rules in terms of user-provided
     logical models, instead of tuples. *)

  (* [Φs] is uncurried ([τ → iProp Σ], not [τ -#> iProp Σ]) so that,
     when it is an evar, the [evals] premise keeps a bare-evar
     postcondition that [imp_evals_cons] can instantiate.  With a
     curried evar the premise reads [tapp ?Φs], whose unfolding on
     records of three or more fields contains nested pair matches that
     unification cannot solve. *)
  Lemma imp_record `{RecordRepr A τ t} {η E Ψ} {ζ : exn → iProp Σ}
    es (Φs : τ → iProp Σ) :
    (τ_length τ ≤ max_array_length)%Z →
    impure E (evals η es) Ψ ζ Φs -∗
    impure E (eval η (ERecord t es)) Ψ ζ
      (λ r, ∃# (xs : τ), ownRecord r (DfracOwn 1) (types_to_repr xs) ∗ Φs xs).
  Proof.
    iIntros (Hlength) "Hes".
    iApply (imp_wand with "[-]").
    { iApply (imp_ERecord (tbind Φs) with "[Hes]"); first assumption.
      iApply (imp_wand with "Hes").
      iIntros (xs) "H". rewrite tapp_bind. iApply "H". }
    iIntros (r).
    rewrite !bi_texist_equiv.
    iIntros "(%xs & Hr & HΦ)".
    rewrite tapp_bind.
    iFrame. unfold ownRecord.
    pose proof repr_id as Hid. simpl in Hid. rewrite Hid.
    iApply "Hr".
  Qed.

  (* Note the [dq]: reading a field needs no more than a discarded share,
     so this rule now covers immutable records shared persistently. *)
  Lemma imp_record_access `{RecordRepr A τ t} {η E Ψ} {ζ : exn → iProp Σ} f (r : record) (dq : dfrac) (a : A) (e : expr) :
    valid_field f τ →
    ▷ ownRecord r dq a -∗
    impure E (eval η e) Ψ ζ (λ r', ⌜r' = r⌝) -∗
    impure E (eval η (ERecordAccess e f)) Ψ ζ (λ (x : τ !!! f), ⌜x = repr_to_types a !!τ f⌝ ∗ ownRecord r dq a).
  Proof.
    iIntros (Hvalid) "Hown He".
    iApply (imp_wand with "[-]").
    { iApply (imp_ERecordAccess with "Hown He"). assumption. }
    iIntros (x) "($ & $)".
  Qed.

  (* Despite what we might expect, we do not require the record to be
     mutable for an update to occur. The OCaml typechecker should make
     such a situation impossible, so we only expect this to be relevant
     in the case where unsafe type coercions were used. In such a case,
     our semantics allow updating records with "immutable" fields as
     long as we have full ownership. *)

  Lemma imp_record_update' `{RecordRepr A τ t} {η E Ψ} {ζ : exn → iProp Σ} (r : record) f e1 e2
  (Φ2 : τ !!! f → iProp Σ) (Φ : unit → iProp Σ) :
    valid_field f τ →
    impure E (eval η e1) Ψ ζ (λ r', ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    (∀ (x : τ !!! f), Φ2 x -∗
      ∃ (a : A), ▷ ownRecord r (DfracOwn 1) a ∗
      ▷ (ownRecord r (DfracOwn 1) (types_to_repr (<[ f τ= x ]> (repr_to_types a))) -∗ Φ ())) -∗
    impure E (eval η (ERecordSet e1 f e2)) Ψ ζ Φ.
  Proof.
    iIntros (Hvf) "He1 He2 HΦ".
    iApply (imp_ERecordSet2 with "He1 He2").
    iIntros (? x) "-> HΦ2".
    iDestruct ("HΦ" $! x with "HΦ2") as (a) "(Hown & HΦ)".
    iExists t, (repr_to_types a).
    iSplitL "Hown"; iNext.
    - iFrame "%". iApply "Hown".
    - unfold ownRecord. pose proof repr_id as Hid. simpl in Hid. rewrite Hid.
      iApply "HΦ".
  Qed.

  Lemma imp_record_update `{RecordRepr A τ t} {η E Ψ} {ζ : exn → iProp Σ} (r : record) f (a : A) e1 e2 Φ :
    valid_field f τ →
    ▷ ownRecord r (DfracOwn 1) a -∗
    impure E (eval η e1) Ψ ζ (λ r', ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ Φ -∗
    impure E (eval η (ERecordSet e1 f e2)) Ψ ζ
      (λ _ : unit, ∃ (x : τ !!! f), Φ x ∗
         ownRecord r (DfracOwn 1) (types_to_repr (<[ f τ= x]> (repr_to_types a)))).
  Proof.
    iIntros (Hvf) "Hown He1 He2".
    iApply (imp_record_update' with "He1 He2"). assumption.
    iIntros (x) "HΦ". iFrame "Hown".
    iIntros "!> $". iApply "HΦ".
  Qed.

End encoded_fields.

Notation "r ⤇ dq a" :=
  (ownRecord r dq a)
    (at level 20, dq custom dfrac at level 1, format "r  ⤇ dq  a") : bi_scope.
