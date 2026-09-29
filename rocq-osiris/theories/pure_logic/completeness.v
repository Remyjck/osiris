From osiris Require Import base.
From osiris.lang Require Import syntax encode notations locations.
From osiris.semantics Require Import semantics.
Require Import pure_rules pattern_rules.

(* Completeness/reversibility of some rules -- useful to check that we did not
forget any case in the rules that we show *)

(** Different versions for [POr] *)

Lemma reversible_pat_POr_unary η δ p1 p2 v φ ψ :
  pattern η δ p1 v φ (pattern η δ p2 v φ ψ)
  <->
  pattern η δ (POr p1 p2) v φ ψ.
Proof.
  unfold pattern. simpl_eval_pat.
  unfold pure.
  split.
  - intro H. apply pure_wp_reversible_orelse.
    eapply pure_wp_mono_throw. { apply H. }
    unfold returns. intros u [u' [? HQ]]. exact HQ.
  - intro H. apply pure_wp_reversible_orelse in H.
    eapply pure_wp_mono_throw. { apply H. }
    unfold returns. intros u HQ. exists u. destruct u. auto.
Qed.

Lemma reversible_pat_POr η δ p1 p2 v φ ψ :
  (∃ ψ1, pattern η δ p1 v φ ψ1 ∧ (ψ1 → pattern η δ p2 v φ ψ))
  <->
  pattern η δ (POr p1 p2) v φ ψ.
Proof.
  rewrite <-reversible_pat_POr_unary.
  firstorder eauto using pattern_exn_mono.
Qed.

Lemma reversible_pat_POr_2 η δ p1 p2 v φ (ψ : Prop) :
  (∃ ψ1 ψ2,
    pattern η δ p1 v φ ψ1 ∧
    (ψ1 → pattern η δ p2 v φ ψ2) ∧
    (ψ1 ∧ ψ2 → ψ))
  <->
  pattern η δ (POr p1 p2) v φ ψ.
Proof.
  rewrite <-reversible_pat_POr.
  firstorder eauto using pattern_exn_mono.
Qed.


(** [PData] *)

Lemma reversible_pat_PData_nil η δ c c' (φ : env → Prop) (ψ : Prop) :
  (c = c' → φ δ)
  <->
  pattern η δ (PData c nil) (VData c' nil) φ (ψ ∨ c ≠ c').
Proof.
  unfold pattern; intros. simpl_eval_pat.
  destruct_string_eqb.
  - split.
    + intros Hφ. eapply pure_ret; eauto.
    + intros Hret. apply invert_pure_ret in Hret.
      destruct Hret as (? & -> & Hφ). tauto.
  - split.
    + intros _.
      eapply pure_throw; auto.
    + intros _ Heq'.
      contradiction.
Qed.

Lemma reversible_pat_PData_or η δ c c' ps vs φ ψ :
  (c = c' -> patterns η δ ps vs φ ψ)
  <->
  pattern η δ (PData c ps) (VData c' vs) φ (ψ ∨ c ≠ c').
Proof.
  unfold pattern; intros. simpl_eval_pat.
  destruct_string_eqb.
  - assert (ψ ↔ (ψ ∨ c ≠ c')) by tauto.
    unfold patterns.
    firstorder eauto using pure_exn_mono.
    eapply pure_exn_mono. apply H2. tauto.
  - split; intros _.
    + eapply pure_throw. reflexivity. tauto.
    + contradiction.
Qed.


(** [PXData], assuming the path lookup is safe *)

Lemma reversible_pat_PXData η δ π ps l l' vs φ ψ :
  lookup_path η π = Some (VFieldLoc l') →
  (l = l' → patterns η δ ps vs φ ψ)
  <->
  pattern η δ (PXData π ps) (VXData l vs) φ (ψ ∨ l ≠ l').
Proof.
  unfold pattern. simpl_eval_pat. intros ->.
  change (as_field_loc (of_option (Some (VFieldLoc l')))) with (@ret _ unit l'). rewrite bind_ret.
  destruct (eqb_spec l l').
  - unfold patterns.
    assert ((ψ ∨ l ≠ l') → ψ) by tauto.
    firstorder eauto using pure_exn_mono.
    eapply pure_exn_mono. apply H1. tauto.
  - split; intros _.
    + eapply pure_throw. reflexivity. tauto.
    + contradiction.
Qed.
