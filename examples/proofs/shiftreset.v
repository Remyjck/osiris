From stdpp Require Import telescopes.
From iris.algebra Require Import excl_auth.

From osiris Require Import osiris.
From osiris.examples Require Import og_shiftreset.

(* Reasoning about delimited control via [shift/reset].

   Note: Sanity check example following [Hazel] [shift_reset] example and
         specification. *)

(* ========================================================================== *)
(** * Protocol. *)

(* ------------------------------------------------------------------------ *)
(** Shift Protocol. *)

Section shift_protocol.
  Context `{!osirisGS Σ}.

  Definition shift shift_eff h : val := VXData shift_eff [h].

  Definition is_shift (Ψ : iEff Σ) (Φ Q : val → iPropO Σ) h : iProp Σ :=
    iSpec τ[cont] h (λ k m,
        (∀ w, Q w -∗ may_resume (O2Ret w) k ⊤ Ψ ⊥ Φ) -∗
        ▷ EWP m <| Ψ |> {{ Φ }})%I.

  (* Note that this specification is different from in [Hazel]; there is
     no recursive reference within the specification itself. *)

  Definition SHIFT ℓ :
    (iEffO -d> (val -d> iPropO Σ) -d> iEffO) := λ Ψ Φ,
    (>> h Q >> !(shift ℓ h) {{ (is_shift Ψ Φ Q h) }};
      << w << ?(O2Ret w) {{ Q w }})%ieff.

  Lemma upcl_SHIFT ℓ Ψ Φ v Φ' :
    (SHIFT ℓ Ψ Φ) allows perform v << Φ' >> ⊣⊢
      (∃ t Q,
          ⌜v = shift ℓ t ⌝ ∗ is_shift Ψ Φ Q t ∗
          (∀ v, Q v -∗ Φ' (O2Ret v)))%I.
  Proof.
    transitivity (iEff_car (upcl (SHIFT ℓ Ψ Φ)) v Φ').
    - by iApply iEff_car_proper.
    - by rewrite /SHIFT (upcl_tele' [tele _ _] [tele _]).
  Qed.

End shift_protocol.

(* ------------------------------------------------------------------------ *)
(** Reasoning Rules. *)

Section reasoning_rules.
  Context `{!osirisGS Σ}.

  Definition env (shift_eff : loc) := ("Shift", #shift_eff) :: [].

  (* Mapping of translated function declaration names *)
  Definition shift_f := (EAnonFun __shift).
  Definition reset_f := (EAnonFun __reset).

  Definition reset_spec ℓ reset : iProp Σ :=
    □ {{ ∀ (Ψ : iEff Σ) (Φ : val → iProp Σ);
       iSpec τ[unit] f (λ _ m, EWP m <| SHIFT ℓ Ψ Φ |> {{ Φ }}) }}
    reset f : val @ ⊤ <| Ψ |>
    {{ RET w; Φ w }}.

  Definition shift_spec ℓ shift : iProp Σ :=
    □ {{ ∀ (Ψ : iEff Σ) (Φ Q : val → iProp Σ); is_shift Ψ Φ Q f }}
    shift f : val @ ⊤ <| SHIFT ℓ Ψ Φ |>
    {{ RET w; Q w }}.

End reasoning_rules.

Inductive effect : Type :=
| Shift (f : val).

Local Instance encode_effect l : Encode effect :=
  { encode' := λ eff, match eff with
                     | Shift f => VXData l [f]
                     end }.

(* ------------------------------------------------------------------------ *)
(** Verification. *)

Section verification.
  Context `{!osirisGS Σ}.

  Context (shift_eff : loc).
  Local Instance : Encode effect := encode_effect shift_eff.
  Local Instance name_effect l : @XData l τ[val] effect (encode_effect l) :=
  { xctor_apply := λ f, Shift f;
    xctor_encode := λ f, eq_refl }.

  Lemma establish_shift_spec η :
    lookup_name η "Shift" = Some #shift_eff →
    ⊢ EWP eval η (EAnonFun __shift) {{ shift_spec shift_eff }}.
  Proof.
    iIntros (Hlookup).
    rewrite /shift_spec.
    iApply (imp_EAnon_pers τ[val]); simpl.
    iIntros "!>" (f).
    iIntros (Ψ Φ Q) "Hf".
    iApply imp_please; iNext.
    iApply (imp_EPerform (λ eff, ⌜eff = Shift f⌝)%I).
    { iApply (imp_EXData (l:=shift_eff)). apply Hlookup.
      iApply imp_evals_singleton. imp_path.
      iIntros (?) "-> //". }
    iIntros (? ->).
    rewrite upcl_SHIFT. iFrame.
    iSplit; first equality.
    iIntros (o) "$". auto.
  Qed.

  Lemma establish_reset_spec η :
    lookup_name η "Shift" = Some #shift_eff →
    ⊢ EWP eval η (EAnonFun __reset) {{ reset_spec shift_eff }}.
  Proof.
    iIntros (Hlookup).
    rewrite /reset_spec.
    iApply (imp_EAnon_pers τ[val]); simpl.
    iIntros "!>" (f).
    iIntros (Ψ Φ) "Hf".
    iApply imp_please; iNext.

    iApply (imp_EHandler (A':=val) with "[Hf]").
    { imp_app τ[unit] with "[Hf]".
      iIntros "$". }

    iLöb as "IH".
    iApply prove_deep_handler_spec.
    iSplit; last (iSplit; first iIntros (? [])).

    (* Base case: we just return the value. *)
    { iIntros (v) "Φ !>".
      imp_branches.
      imp_path. }

    (* Handler case: an effect is being performed. *)
    iIntros (v k) "Hprot".
    rewrite upcl_SHIFT.
    iDestruct "Hprot" as (g Q) "[-> [Hg Hk]]".

    unfold is_shift.

    iModIntro. imp_branches.
    iApply (imp_EApp τ[cont] with "[Hg] []"); try imp_step.
    iIntros (? -> m) "Hwp".
    iApply "Hwp".
    iIntros (v) "HQ".
    iApply ("Hk" with "HQ IH").
  Qed.

End verification.
