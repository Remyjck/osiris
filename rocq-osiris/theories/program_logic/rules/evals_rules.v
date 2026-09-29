From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import lang.
From osiris.utils Require Import list_z.
Require Import osiris_utils.
Require Import ewp tactics fun_spec escrows.
Require Import
  basic_rules impure_rules stop_rules
  handler_rules auxiliary_rules.

Section evals_rules.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ}.

  Local Instance notval_listval : NotVal (list val) := {}.

  Lemma imp_evals_nil η (Φ : list val → iProp Σ) :
    Φ [] -∗
    impure E (evals η []) Ψ ζ Φ.
  Proof.
    iIntros "HΦ".
    simpl_evals.
    by iApply (imp_ret with "HΦ").
  Qed.

  Global Instance observe_types_cons `{Encode A} {τ : types} : Observe (A * τ) (list val) :=
  { observe := λ '(x, xs), observe x :: observe xs }.

  Lemma imp_evals_cons `{Encode A} {τ : types} η e es (Φ : A → iProp Σ) (Φs : τ → iProp Σ) :
    impure E (eval η e) Ψ ζ Φ -∗
    impure E (evals η es) Ψ ζ Φs -∗
    impure (A:=type_nel.Tcons A τ) E (evals η (e :: es)) Ψ ζ (λ '(x, xs), Φ x ∗ Φs xs).
  Proof.
    iIntros "He Hes".
    simpl_evals.
    iApply (imp_bind_par with "He Hes").
    iIntros (x xs) "HΦ HΦs".
    iApply (imp_ret _ (x, xs)).
    - reflexivity.
    - iFrame.
  Qed.

  Local Instance observe_singleton `{Encode A} : Observe A (list val) :=
  { observe := λ (x : A), [ encode.encode x ] }.

  Lemma imp_evals_singleton `{Encode A} η e (Φ : A → iProp Σ) :
    impure E (eval η e) Ψ ζ Φ -∗
    impure E (evals η [e]) Ψ ζ Φ.
  Proof.
    iIntros "He". simpl_evals.
    iApply (imp_bind_par (A2:=list val) (H1:=observe_id) with "He").
    { set_postcondition (λ (l : list val), ⌜l = []⌝)%I.
      iApply (imp_ret _ []); auto. }
    iIntros (x xs) "HΦ ->".
    iApply (imp_ret _ x). encode.
    iApply "HΦ".
  Qed.

  Lemma imp_EData `{DC : Data c τ A} {Φ : A → iProp Σ} η es (Φs : τ → iProp Σ) :
    impure E (evals η es) Ψ ζ Φs -∗
    (∀# xs, Φs xs -∗ Φ (DC.(ctor_apply) xs)) -∗
    EWP eval η (EData c es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H Hk". simpl_eval.
    iApply (imp_bind with "H").
    iIntros (xs) "HΦs".
    rewrite bi_tforall_equiv.
    iDestruct ("Hk" with "HΦs") as "HΦ".
    iApply (imp_ret _ (DC.(ctor_apply) xs)); last iApply "HΦ".
    simpl. apply DC.(ctor_encode).
  Qed.

  Lemma imp_EData_evar `{DC : Data c τ A} η es (Φs : τ → iProp Σ) :
    impure E (evals η es) Ψ ζ Φs -∗
    EWP eval η (EData c es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ x, ∃# xs, ⌜x = DC.(ctor_apply) xs⌝ ∗ Φs xs }}.
  Proof.
    iIntros "Hes".
    iApply (imp_EData with "Hes").
    rewrite bi_tforall_equiv. setoid_rewrite bi_texist_equiv.
    iIntros (xs) "$ //".
  Qed.

  Lemma imp_EXData `{DC : XData l τ A} {Φ : A → iProp Σ} η π es (Φs : τ → iProp Σ) :
    lookup_path η π = Some #l →
    impure E (evals η es) Ψ ζ Φs -∗
    (∀# xs, Φs xs -∗ Φ (DC.(xctor_apply) xs)) -∗
    EWP eval η (EXData π es) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hlookup) "He Hk". simpl_eval.
    rewrite Hlookup. unfold as_field_loc; simpl. rewrite !bind_ret.
    iApply (imp_bind with "He").
    rewrite bi_tforall_equiv.
    iIntros (xs) "HΦs".
    iDestruct ("Hk" with "HΦs") as "HΦ".
    iApply (imp_ret _ (DC.(xctor_apply) xs)); last iApply "HΦ".
    simpl. apply DC.(xctor_encode).
  Qed.

  Lemma imp_ETuple {τ : types} {Φ : τ → iProp Σ} (Φs : τ → iProp Σ) η es :
    impure E (evals η es) Ψ ζ Φs -∗
    (∀# (xs : τ), Φs xs -∗ Φ xs) -∗
    impure E (eval η (ETuple es)) Ψ ζ Φ.
  Proof.
    iIntros "Hes Hk".
    simpl_eval.
    iApply (imp_bind with "Hes").
    iIntros (xs) "HΦs".
    rewrite bi_tforall_equiv.
    iDestruct ("Hk" with "HΦs") as "HΦ".
    iApply (imp_ret with "HΦ").
    encode.
  Qed.

  (* Tuple construction without a monotonicity premise: the elements
     are evaluated directly against the tuple postcondition [Φ].  This
     is the version to use when [Φ] is still an evar, since the split
     amongst the elements then determines [Φ] and no monotonicity goal
     is needed. *)
  Lemma imp_ETuple_evar {τ : types} {Φ : τ → iProp Σ} η es :
    impure E (evals η es) Ψ ζ Φ -∗
    impure E (eval η (ETuple es)) Ψ ζ Φ.
  Proof.
    iIntros "Hes".
    simpl_eval.
    iApply (imp_bind with "Hes").
    iIntros (xs) "HΦs".
    iApply (imp_ret with "HΦs").
    encode.
  Qed.

  (* Reflexivity of the [imp_ETuple] monotonicity premise.  Used by the
     [imp_step] automation to discharge that premise when a tuple is
     solved without a selection pattern: applying it unifies the
     intermediate postcondition with the tuple postcondition. *)
  Lemma tuple_mono_refl {τ : types} (Φ : τ → iProp Σ) :
    ⊢ ∀# (xs : τ), Φ xs -∗ Φ xs.
  Proof. rewrite bi_tforall_equiv. iIntros (xs) "H". iApply "H". Qed.

End evals_rules.
