From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang type_nel.
Require Import osiris_utils.
Require Import ewp.
Require Import impure_rules stop_rules evals_rules record_rules.
From osiris.utils Require Import list_z big_opLZ.

(** Reasoning rules for single record fields, and for references
    ([ERef], [ELoad], [EStore]), which are mutable records with one field
    ([field_loc.v]). *)

Section field_rules.

  Context `{!osirisGS Σ}.

  Context {η : env} {E : coPset} {Ψ : iEff Σ}.
  Implicit Types ζ : exn → iProp Σ.

  (** * Field access *)

  Lemma imp_ERecordAccess_field2 `{Encode A} {Φ : A → iProp Σ} {ζ} (Φ1 : record → iProp Σ) f e :
    impure E (eval η e) Ψ ζ Φ1 -∗
    (∀ r, Φ1 r -∗ ∃ dq a, ▷ r ↦[f]{dq} #a ∗ ▷ (r ↦[f]{dq} #a -∗ Φ a)) -∗
    impure E (eval η (ERecordAccess e f)) Ψ ζ Φ.
  Proof.
    iIntros "He P". simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_record with "He"). }
    iIntros (r) "HΦ1".
    iDestruct ("P" with "HΦ1") as (dq a) "[Hf HΦ]".
    rewrite /field_pointsto /field_at.
    iDestruct "Hf" as (l) "[(%ls & #Hls & >%Hf) Hl]".
    iApply (imp_bind (A1:=(mut_tag * list loc))).
    { iApply (imp_load_block_ghost with "Hls"). }
    iIntros ([? ?]) "-> /=". rewrite Hf.
    iApply (imp_load' with "Hl").
    iIntros "!> Hl". iApply "HΦ".
    iExists l. iFrame "∗#%".
  Qed.

  Lemma imp_ERecordAccess_field `{Encode A} {ζ} (r : record) f dq (a : A) e :
    ▷ r ↦[f]{dq} #a -∗
    impure E (eval η e) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    impure E (eval η (ERecordAccess e f)) Ψ ζ (λ (a' : A), ⌜a' = a⌝ ∗ r ↦[f]{dq} #a).
  Proof.
    iIntros "Hf He".
    iApply (imp_ERecordAccess_field2 with "He").
    iIntros (?) "->". iFrame. by iIntros "!> $".
  Qed.

  (** * Field update *)

  Lemma imp_ERecordSet_field2' `{Encode A} {Φ : unit → iProp Σ} {ζ} f e1 e2
      (Φ1 : record → iProp Σ) (Φ2 : A → iProp Σ) :
    impure E (eval η e1) Ψ ζ Φ1 -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    (∀ r a, Φ1 r -∗ Φ2 a -∗
      ▷ ∃ v, r ↦[f] v ∗ ▷ (r ↦[f] #a -∗ Φ ())) -∗
    impure E (eval η (ERecordSet e1 f e2)) Ψ ζ Φ.
  Proof.
    iIntros "He1 He2 P". simpl_eval.
    iApply (imp_bind_par with "[He1] He2").
    { iApply (imp_as_record with "He1"). }
    iIntros (r a) "H1 H2".
    iSpecialize ("P" with "H1 H2").
    rewrite /field_pointsto /field_at.
    iDestruct "P" as (v) "[Hf HΦ]".
    iDestruct "Hf" as (l) "[(%ls & #Hls & >%Hf) Hl]".
    iApply (imp_bind (A1:=(mut_tag * list loc)) with "[Hl HΦ]").
    { iApply (imp_load_block_ghost' with "Hls [Hl HΦ]"). iNext. iCombine "Hl HΦ" as "H". iExact "H". }
    iIntros "!>" ([? ?]) "(-> & Hl & HΦ) /=". rewrite Hf.
    iApply (imp_store' with "Hl").
    iIntros "!> Hl". iApply "HΦ".
    iExists l. iFrame "∗#%".
  Qed.

  Lemma imp_ERecordSet_field2 `{Encode A} {Φ : unit → iProp Σ} {ζ} (r : record) f e1 e2
      (Φ2 : A → iProp Σ) :
    impure E (eval η e1) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    (∀ a, Φ2 a -∗ ▷ ∃ v, r ↦[f] v ∗ ▷ (r ↦[f] #a -∗ Φ ())) -∗
    impure E (eval η (ERecordSet e1 f e2)) Ψ ζ Φ.
  Proof.
    iIntros "He1 He2 P".
    iApply (imp_ERecordSet_field2' with "He1 He2").
    iIntros (? a) "-> H2". iApply ("P" with "H2").
  Qed.

  Lemma imp_ERecordSet_field `{Encode A} {ζ} (r : record) f v (a : A) e1 e2 :
    ▷ r ↦[f] v -∗
    impure E (eval η e1) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ (λ (a' : A), ⌜a' = a⌝) -∗
    impure E (eval η (ERecordSet e1 f e2)) Ψ ζ (λ (_ : unit), r ↦[f] #a).
  Proof.
    iIntros "Hf He1 He2".
    iApply (imp_ERecordSet_field2 with "He1 He2").
    iIntros (?) "-> !>". iFrame. by iIntros "!> $".
  Qed.

End field_rules.

(* A lookup and an assignment of a reference evaluate exactly as a read and
   a write of field [0] of a record. *)

Lemma eval_ELoad η e : eval η (ELoad e) = eval η (ERecordAccess e 0).
Proof. unfold eval. rewrite seal_eq. reflexivity. Qed.

Lemma eval_EStore η e1 e2 : eval η (EStore e1 e2) = eval η (ERecordSet e1 0 e2).
Proof. unfold eval. rewrite seal_eq. reflexivity. Qed.

Lemma eval_EResolve_ELoad η e ep ev :
  eval η (EResolve (ELoad e) ep ev) = eval η (EResolve (ERecordAccess e 0) ep ev).
Proof. unfold eval. rewrite seal_eq. reflexivity. Qed.

Section ref_rules.

  Context `{!osirisGS Σ}.

  Context {η : env} {E : coPset} {Ψ : iEff Σ}.
  Implicit Types ζ : exn → iProp Σ.

  (** * Allocation: [ref e] *)

  (* The allocation step pays for the later in front of the continuation,
     once the value of [e] is known. *)
  Local Lemma imp_ref_gen `{Encode A} {ζ} {Φ' : record → iProp Σ} (Φ : A → iProp Σ) e :
    impure E (eval η e) Ψ ζ Φ -∗
    (∀ a, Φ a -∗ ▷ ∀ r, r ↦ #a -∗ Φ' r) -∗
    impure E (eval η (ERef e)) Ψ ζ Φ'.
  Proof.
    iIntros "He Hk". simpl_eval.
    iApply (imp_bind with "He").
    iIntros (a) "HΦ".
    iSpecialize ("Hk" with "HΦ").
    iApply (imp_bind (A1:=loc) with "[Hk]").
    { iApply imp_alloc2.
      iIntros "!>" (l) "Hl". iCombine "Hk Hl" as "H". iExact "H". }
    iIntros (l) "(Hk & Hl)".
    iApply imp_bind.
    { iApply imp_alloc_block. iPureIntro.
      pose proof int.max_array_positive.
      rewrite -singleton_unfold length_singleton. lia. }
    iIntros (r) "(Htag & #Hls)".
    iMod (blockTag_persist with "Htag") as "#Htag".
    iApply imp_ret; first encode.
    iApply "Hk".
    rewrite /ref_pointsto /is_ref /field_pointsto /field_at -singleton_unfold.
    iFrame "#". iExists l. iFrame "∗#". by rewrite list_lookup_singleton_eq_0.
  Qed.

  Lemma imp_ref2' `{Encode A} {ζ} {Φ' : record → iProp Σ} (Φ : A → iProp Σ) e :
    impure E (eval η e) Ψ ζ Φ -∗
    ▷ (∀ a r, Φ a -∗ r ↦ #a -∗ Φ' r) -∗
    impure E (eval η (ERef e)) Ψ ζ Φ'.
  Proof.
    iIntros "He Hk".
    iApply (imp_ref_gen with "He").
    iIntros (a) "HΦ !> %r Hr". iApply ("Hk" with "HΦ Hr").
  Qed.

  Lemma imp_ref2 `{Encode A} {ζ} (Φ : A → iProp Σ) e :
    impure E (eval η e) Ψ ζ (λ a, ▷ Φ a) -∗
    impure E (eval η (ERef e)) Ψ ζ (λ (r : record), ∃ a, Φ a ∗ r ↦ #a).
  Proof.
    iIntros "He".
    iApply (imp_ref_gen with "He").
    iIntros (a) "HΦ !> %r Hr". iFrame.
  Qed.

  Lemma imp_ref `{Encode A} {ζ} (a : A) e :
    impure E (eval η e) Ψ ζ (λ a', ⌜a' = a⌝) -∗
    impure E (eval η (ERef e)) Ψ ζ (λ (r : record), r ↦ #a).
  Proof.
    iIntros "He".
    iApply (imp_ref2' with "He").
    iIntros "!>" (? r) "-> $".
  Qed.

  (** * Dereference: [!e] *)

  Lemma imp_deref2 `{Encode A} {Φ : A → iProp Σ} {ζ} (Φ1 : record → iProp Σ) e :
    impure E (eval η e) Ψ ζ Φ1 -∗
    (∀ r, Φ1 r -∗ ∃ q a, ▷ r ↦{q} #a ∗ ▷ (r ↦{q} #a -∗ Φ a)) -∗
    impure E (eval η (ELoad e)) Ψ ζ Φ.
  Proof.
    rewrite eval_ELoad /ref_pointsto. iIntros "He P".
    iApply (imp_ERecordAccess_field2 with "He").
    iIntros (r) "HΦ1".
    iDestruct ("P" with "HΦ1") as (q a) "[[#Hr Hf] HΦ]".
    iExists q, a. iFrame "Hf".
    iIntros "!> Hf". iApply "HΦ". iFrame "∗#".
  Qed.

  Lemma imp_deref `{Encode A} {ζ} {e} (r : record) q (a : A) :
    ▷ r ↦{q} #a -∗
    impure E (eval η e) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    impure E (eval η (ELoad e)) Ψ ζ (λ (a' : A), ⌜a' = a⌝ ∗ r ↦{q} #a).
  Proof.
    iIntros "Hr He".
    iApply (imp_deref2 with "He").
    iIntros (?) "->". iFrame. by iIntros "!> $".
  Qed.

  (** * Assignment: [e1 := e2] *)

  Lemma imp_assign2' `{Encode A} {Φ : unit → iProp Σ} {ζ} e1 e2
      (Φ1 : record → iProp Σ) (Φ2 : A → iProp Σ) :
    impure E (eval η e1) Ψ ζ Φ1 -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    (∀ r a, Φ1 r -∗ Φ2 a -∗
      ▷ ∃ v, r ↦ v ∗ ▷ (r ↦ #a -∗ Φ ())) -∗
    impure E (eval η (EStore e1 e2)) Ψ ζ Φ.
  Proof.
    rewrite eval_EStore /ref_pointsto. iIntros "He1 He2 P".
    iApply (imp_ERecordSet_field2' with "He1 He2").
    iIntros (r a) "H1 H2".
    iDestruct ("P" with "H1 H2") as "P". iNext.
    iDestruct "P" as (v) "[[#Hr Hf] HΦ]".
    iExists v. iFrame "Hf".
    iIntros "!> Hf". iApply "HΦ". iFrame "∗#".
  Qed.

  Lemma imp_assign2 `{Encode A} {Φ : unit → iProp Σ} {ζ} (r : record) e1 e2 (Φ2 : A → iProp Σ) :
    impure E (eval η e1) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    (∀ a, Φ2 a -∗ ▷ ∃ v, r ↦ v ∗ ▷ (r ↦ #a -∗ Φ ())) -∗
    impure E (eval η (EStore e1 e2)) Ψ ζ Φ.
  Proof.
    iIntros "He1 He2 P".
    iApply (imp_assign2' with "He1 He2").
    iIntros (? a) "-> H2". iApply ("P" with "H2").
  Qed.

  Lemma imp_assign' `{Encode A} {ζ} {Φ} (Φ' : A → iProp Σ) {e1 e2} (r : record) v :
    ▷ r ↦ v -∗
    impure E (eval η e1) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ Φ' -∗
    ▷ (∀ a, Φ' a -∗ r ↦ #a -∗ Φ) -∗
    impure E (eval η (EStore e1 e2)) Ψ ζ (λ (_ : unit), Φ).
  Proof.
    iIntros "Hr He1 He2 Hk".
    iApply (imp_assign2 with "He1 He2").
    iIntros (a) "HΦ' !>". iFrame.
    iIntros "!> Hr". iApply ("Hk" with "HΦ' Hr").
  Qed.

  Lemma imp_assign `{Encode A} {ζ} {e1 e2} (r : record) (a : A) v :
    ▷ r ↦ v -∗
    impure E (eval η e1) Ψ ζ (λ (r' : record), ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ (λ (a' : A), ⌜a' = a⌝) -∗
    impure E (eval η (EStore e1 e2)) Ψ ζ (λ (_ : unit), r ↦ #a).
  Proof.
    iIntros "Hr He1 He2".
    iApply (imp_assign' with "Hr He1 He2").
    iIntros "!>" (?) "-> $".
  Qed.

End ref_rules.
