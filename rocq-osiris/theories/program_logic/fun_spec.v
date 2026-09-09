From iris.bi Require Import interface.

From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.
Require Import ewp impure_rules stop_rules.
From osiris.pure_logic Require Import fun_spec.

From iris.proofmode Require Import proofmode.

From Equations Require Import Equations.

Equations bi_pure_spec (PROP: bi) (τ : types) (f : τ -#> microvx -> Prop) : (τ -#> microvx -> PROP) :=
| PROP, Tbase T, f :=
    λ x m, bi_pure (f x m)
| PROP, type_nel.Tcons T τ', f :=
    λ x, bi_pure_spec PROP τ' (f x).

Arguments bi_pure_spec {_ _} _.

Section imp_spec.

  Context `{!osirisGS Σ}.

  (* -------------------------------------------------------------------------- *)

  (* To reason about curried n-ary function, and give them natural specifications
   (i.e. specifications over the function when fully applied)
   We introduce the predicate [Spec arg_τ c P]. *)

  (* [Spec arg_τ c P] should be read as "[c] is a function value, with
   arguments described by [arg_τ], and with specification [P]." *)

  (* [Spec] matches on the list of argument types [arg_τ], producing a series of
   nested calls, where the base case asserts [P] over the full call. *)

  Equations iSpec (τ : types) (c : val) (P : τ -#> microvx -> iProp Σ) : iProp Σ :=
  | Tbase X, c, P :=
      ∀ (x : X), P x (call c #x)
  | type_nel.Tcons X τ', c, P :=
      ∀ (x : X), @impure val val exn Σ _ _ ⊤ (call c #x) ⊥ ⊥ (λ (c : val), iSpec τ' c (P x)).

  Local Lemma imp_eval_anon_unary `{Encode X}
    (P : τ[X] -#> microvx -> iProp Σ) η (x : var) e E Ψ
    :
    (∀ (v : X), P v (please_eval ((x, #v) :: η) e)) -∗
    EWP (eval η (EAnonFun (AnonFun x e))) @ E <|Ψ|> {{ c, iSpec τ[X] c P }}.
  Proof.
    iIntros "HP"; simpl_eval.
    iApply (@imp_ret _ _ val val); auto.
  Qed.

  Local Lemma imp_eval_anon_binary `{Encode X, Encode Y}
    (P : τ[X;Y] -#> microvx -> iProp Σ) η (x y : var) e E Ψ
    :
    (∀ (vx : X) (vy : Y), P vx vy (please_eval ((y, #vy) :: (x, #vx) :: η) e)) -∗
    EWP (eval η (EAnonFun (AnonFun x (EAnonFun (AnonFun y e))))) @ E <|Ψ|> {{ c, iSpec τ[X;Y] c P }}.
  Proof.
    iIntros "HP"; simpl_eval.
    iApply (@imp_ret _ _ val val); first auto.
    simpl; simp iSpec.
    iIntros (vx). simpl.
    iApply imp_please. iNext.
    iApply (imp_eval_anon_unary).
    iIntros (vy).
    iApply "HP".
  Qed.

  (* [iSpec] is monotonic over specification predicates. *)

  Lemma iSpec_mono (τ : types) (P P' : τ -#> microvx -> iProp Σ) c :
    iSpec τ c P -∗
    (∀# args, ∀ m, (P args) m -∗ (P' args) m) -∗
    iSpec τ c P'.
  Proof.
    revert c.
    induction τ as [ | X HX arg_τ IH ]; iIntros (c) "HP Hmono".
    { simp iSpec. iIntros (x).
      iApply "Hmono". iApply "HP". }
    simp iSpec; iIntros (x).
    iApply (imp_wand with "HP").
    iIntros (c') "HSpec'".
    iApply (IH with "HSpec'").
    iApply "Hmono".
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* We define [predicate_over_function_body τ P η e], which fetches the
     function body from a series of nested [EAnonFun] in [e], at a depth
     equal to the number of arguments specified by [τ], and asserts [P]
     over the evaluation of that function body. *)

  (* In particular, [predicate_over_function_body] can be used to prove
     a goal of the form [Spec τ c P]. *)

  Equations predicate_over_function_body
    (τ : types)
    (P : τ -#> microvx -> iProp Σ)
    (η : env)
    (e : expr)
    : iProp Σ :=
  | Tbase X, P, η, EAnonFun (AnonFun arg e) :=
      ∀ (x : X), P x (please_eval ((arg, #x) :: η) e)
  | type_nel.Tcons X arg_τ', P, η, (EAnonFun (AnonFun arg e)) :=
      ∀ (x : X), predicate_over_function_body arg_τ' (P x) ((arg, #x) :: η) e
  (* If the expression isn't an [EAnonFun] we produce an unprovable proposition. *)
  | _, _, _, _ := False.

  (* We always want to unfold [predicate_over_function_body] until only a
   statement of the form [∀ x, P x (eval η e)] remains. *)
  Arguments predicate_over_function_body !τ /.
  Transparent predicate_over_function_body.
  Strategy transparent [ predicate_over_function_body ].

  Lemma invert_predicate_over_body τ P η e :
    predicate_over_function_body τ P η e -∗
    ⌜∃ arg e', e = EAnonFun (AnonFun arg e')⌝.
  Proof.
    iIntros "HP".
    funelim (predicate_over_function_body τ P η e); try done;
      iPureIntro; eexists _, _; reflexivity.
  Qed.

  Local Lemma prove_iSpec (τ : types) η x e (P : τ -#> microvx -> iProp Σ) :
    predicate_over_function_body τ P η (EAnonFun (AnonFun x e)) -∗
    iSpec τ (VClo η (AnonFun x e)) P.
  Proof.
    iLöb as "IH" forall (e x η τ P).
    iIntros "HP".
    destruct τ as [ X | X HX τ ].
    { iApply "HP". }
    simp iSpec; iIntros (vx).
    simp predicate_over_function_body.
    iSpecialize ("HP" $! vx).
    iPoseProof (invert_predicate_over_body with "HP") as "(%y & %e' & ->)".
    simpl. iApply imp_please. iNext. simpl_eval.
    iApply (@imp_ret _ _ val val); first reflexivity.
    iApply ("IH" with "HP").
  Qed.

  Lemma prove_iSpec_pers (τ : types) η x e (P : τ -#> microvx -> iProp Σ) :
    □ predicate_over_function_body τ P η (EAnonFun (AnonFun x e)) -∗
    □ iSpec τ (VClo η (AnonFun x e)) P.
  Proof.
    iLöb as "IH" forall (e x η τ P).
    iIntros "#HP".
    destruct τ as [ X | X HX τ ].
    { iApply "HP". }
    simp iSpec; iIntros (vx).
    simp predicate_over_function_body.
    iSpecialize ("HP" $! vx).
    iPoseProof (invert_predicate_over_body with "HP") as "(%y & %e' & ->)".
    simpl. iModIntro. iApply imp_please. iNext. simpl_eval.
    iApply (@imp_ret _ _ val val); first reflexivity.
    iApply ("IH" with "HP").
  Qed.

  (* The reasoning rule for an n-ary non-recursive function. *)

  Lemma imp_EAnon
    (τ : types)
    (P : τ -#> microvx -> iProp Σ)
    η
    (x : var)
    e E Ψ :
    predicate_over_function_body τ P η (EAnonFun (AnonFun x e)) -∗
    EWP (eval η (EAnonFun (AnonFun x e))) @ E <| Ψ |> {{ c, iSpec τ c P }}.
  Proof.
    iIntros "HP".
    simpl_eval; iApply (@imp_ret _ _ val val); first reflexivity.
    by iApply prove_iSpec.
  Qed.

  Lemma imp_EAnon_pers
    (τ : types)
    (P : τ -#> microvx -> iProp Σ)
    η
    (x : var)
    e E Ψ :
    □ predicate_over_function_body τ P η (EAnonFun (AnonFun x e)) -∗
    EWP (eval η (EAnonFun (AnonFun x e))) @ E <| Ψ |> {{ c, □ iSpec τ c P }}.
  Proof.
    iIntros "HP".
    simpl_eval; iApply (@imp_ret _ _ val val); first reflexivity.
    by iApply prove_iSpec_pers.
  Qed.

  Lemma imp_EAnon_poly
    (τ : tele → types)
    (P : ∀ TS, (τ TS) -#> microvx -> iProp Σ)
    η
    (x : var)
    e E Ψ :
    (□ ∀ (TS : tele), predicate_over_function_body (τ TS) (P TS) η (EAnonFun (AnonFun x e))) -∗
    EWP (eval η (EAnonFun (AnonFun x e))) @ E <| Ψ |> {{ c, ∀ TS, □ iSpec (τ TS) c (P TS) }}.
  Proof.
    iIntros "HP".
    simpl_eval; iApply (@imp_ret _ _ val val); first reflexivity.
    iIntros (TS).
    by iApply prove_iSpec_pers.
  Qed.

  Lemma pure_iSpec `{Encode B} τ c P :
    ⌜Spec τ c P⌝ -∗
    iSpec τ c (bi_pure_spec P)%I.
  Proof.
    iLöb as "IH" forall (τ c P).
    iIntros "%HSpec".
    destruct τ as [ X | X HX τ ].
    { simp iSpec. simp Spec in HSpec. simp bi_pure_spec.
      iIntros (x).
      iPureIntro.
      apply HSpec. }
    simp iSpec. iIntros (x). simp Spec in HSpec.
    specialize (HSpec x).
    destruct c; simpl in HSpec; try by apply wp.invert_pure_wp_crash in HSpec.
    - destruct a; simpl in *.
      iApply imp_please. iNext.
      iApply imp_wand.
      { iApply (impure_pure (B:=B)). apply wp.invert_pure_wp_eval in HSpec.
        eapply wp.pure_wp_mono. apply HSpec.
        - intros v Hv. exists v. split; first reflexivity. exact Hv.
        - intros ? []. }
      iIntros (c); iApply "IH".
    - simpl.
      case_eq (lookup_rec_bindings rbs f).
      + intros a Heqlookup. rewrite Heqlookup in HSpec.
        simpl in *. destruct a; simpl in *.
        iApply imp_please; iNext.
        apply wp.invert_pure_wp_eval in HSpec.
        iApply imp_wand.
        { iApply (impure_pure (B:=B)).
          eapply wp.pure_wp_mono. apply HSpec.
          - intros v Hv. exists v. split; first reflexivity. exact Hv.
          - intros ? []. }
        iIntros (c); iApply "IH".
      + intros Heqlookup. rewrite Heqlookup in HSpec.
        simpl in HSpec.
        by apply wp.invert_pure_wp_crash in HSpec.
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* [imp_EApp_partial] is a lemma for partial application. *)


  (* For now, we don't allow masks to be opened when proving [e] and [e1] *)
  Lemma imp_EApp_partial `{Encode X} (τ: types) η e e1 {ζ Ψ}
    (P : type_nel.Tcons X τ -#> microvx -> iProp Σ) :
    EWP eval η e <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ c, iSpec (type_nel.Tcons X τ) c P }} -∗
    EWP eval η e1 <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ v1, ∃ (x : X), ⌜v1 = #x⌝ }} -∗
    EWP eval η (EApp e e1) <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ c, ∃ (x : X), iSpec τ c (P x) }}.
  Proof.
    iIntros "He He1". simpl_eval.
    iApply (imp_bind_par with "He He1").
    iIntros (c v1) "HSpec [%x ->]". simpl. simp iSpec.
    iSpecialize ("HSpec" $! x).
    iApply (imp_mono_prot with "[HSpec]"); [ | iApply iEff_le_bottom ].
    rewrite /continue /=.
    iApply (imp_wand with "[HSpec]").
    iApply (imp_wand_exn with "HSpec"). iIntros (? []).
    iIntros (c') "$".
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* We provide infrastructure for reasoning about n-ary function application,
     similar to the pure case. *)

End imp_spec.

(* The following definitions are outside the section to avoid capturing Σ *)

Section imp_EApp_prop_aux_def.

  Context `{!osirisGS Σ}.
  Context (η : env) (Ψ : iEff Σ) (ζ : exn → iProp Σ).
  Context (expr_base : expr) (goal_prop : expr -> iProp Σ).

  (* [accumulate_argument_premises_and_build_consequence_hyp] builds up
     premises for each argument and a consequence hypothesis. *)

  Equations accumulate_argument_premises_and_build_consequence_hyp
    (τ : types) (es : list expr) (conseq_acc : τ -#> iProp Σ -> iProp Σ) :
    iProp Σ :=
  | Tbase X, es, conseq_acc :=
      ∀ (e : expr) (φ : X -> iProp Σ),
        EWP eval η e <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ x, φ x }} -∗
        (* [Hconseq] is the consequence premise built over all parameters *)
        let Hconseq := ∀ (x : X), conseq_acc x (φ x) in
        (* [nested_eapp] is the nested application *)
        let nested_eapp := app_exprs expr_base (e :: es) in
        Hconseq -∗ goal_prop (nested_eapp)
  | type_nel.Tcons X τ', es, conseq_acc :=
      ∀ (e : expr) (φ : X -> iProp Σ),
        EWP eval η e <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ x, φ x }} -∗
        let conseq_acc :=
          (λ# (tt : τ') (Q : iProp Σ),
              ∀ (x : X),
                φ x -∗
                (tapp (conseq_acc x) tt) Q)
        in
        accumulate_argument_premises_and_build_consequence_hyp
          τ' (e :: es) conseq_acc.

  Arguments accumulate_argument_premises_and_build_consequence_hyp !τ /.
  Transparent accumulate_argument_premises_and_build_consequence_hyp.
  Strategy transparent [ accumulate_argument_premises_and_build_consequence_hyp ].

  (* Monotonicity of the accumulator *)

  Lemma imp_EApp_mono (τ : types) es (Hmon' Hmon : τ -#> iProp Σ -> iProp Σ) :
    accumulate_argument_premises_and_build_consequence_hyp τ es Hmon' -∗
    □ (∀ args (P : iProp Σ), Hmon args P -∗ Hmon' args P) -∗
    accumulate_argument_premises_and_build_consequence_hyp τ es Hmon.
  Proof.
    revert es.
    induction τ as [ X HX | X HX τ IH ]; iIntros (es) "HEApp' #Hmono"; simpl.
    - iIntros (ex φx) "Hex Hx". cbn zeta.
      iSpecialize ("HEApp'" $! ex φx with "Hex"). cbn zeta.
      iApply "HEApp'".
      iIntros (v). iApply ("Hmono" with "Hx").
    - iIntros (ex φx) "Hex".
      iApply (IH with "[HEApp' Hex]").
      + iApply ("HEApp'" with "Hex").
      + iModIntro. iIntros (args P). rewrite !tapp_bind.
        iIntros "Hx" (x) "Hφx".
        iApply ("Hmono" $! (x, args) P).
        iApply ("Hx" with "Hφx").
  Qed.

End imp_EApp_prop_aux_def.

Section imp_EApp_def.
  Context `{!osirisGS Σ}.

  Definition imp_EApp_prop `{Encode A} (τ : types) : iProp Σ :=
    ∀ (η : env) (e : expr) (Φ' : A -> iProp Σ) (Ψ : iEff Σ) ζ
      (P : τ -#> microvx -> iProp Σ),
    EWP eval η e <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ c, iSpec τ c P }} -∗
    accumulate_argument_premises_and_build_consequence_hyp
      η Ψ ζ e
      (λ e, EWP eval η e <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ v, Φ' v }})
      τ
      []
      (λ# (tt : τ) (Q : iProp Σ),
           Q -∗ ∀ m, (tapp P tt) m -∗ ▷ EWP m <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ v, Φ' v }}).

  Arguments imp_EApp_prop {_ _} !τ /.
  Transparent imp_EApp_prop.
  Strategy transparent [ imp_EApp_prop ].

  (* Helper lemma for the induction step *)

  Lemma imp_EApp_prop_induction_step
    (τ : types) (η : env) (Ψ : iEff Σ) ζ e (g : expr -> iProp Σ) :
    ∀ (Hconseq : τ -#> iProp Σ -> iProp Σ) (es : list expr) (ei : expr),
      app_exprs (EApp e ei) es = app_exprs e (es ++ [ei]) →
      accumulate_argument_premises_and_build_consequence_hyp
        η Ψ ζ (EApp e ei) g τ es Hconseq -∗
      accumulate_argument_premises_and_build_consequence_hyp
        η Ψ ζ e g τ (es ++ [ei]) Hconseq.
  Proof.
    induction τ as [ X HX | X HX τ IH ]; iIntros (Hconseq es ei HeqEApp) "Happlied".
    - (* Base case *)
      simpl in *. rewrite <- HeqEApp. iApply "Happlied".
    - (* Inductive case *)
      iIntros (ex φx) "Hex". cbn zeta.
      iApply (IH (λ# (tt : τ) (B : iProp Σ),
                   ∀ x : X,
                     φx x -∗
                     tapp Hconseq (x, tt) B)%I
                 (ex :: es) ei).
      + simpl. f_equal. apply HeqEApp.
      + iApply ("Happlied" with "Hex").
  Qed.

  (* Main lemma for n-ary function application *)

  Lemma imp_EApp `{Encode A} (τ : types) :
    ⊢ @imp_EApp_prop A _ τ.
  Proof.
    induction τ as [ X HX | X HX τ IH].
    - (* Base case *)
      unfold imp_EApp_prop.
      iIntros (η e Φ' Ψ ζ P) "HSpec"; iIntros (ex φx) "Hex"; cbn zeta.
      iIntros "Hmono".
      simpl_eval.
      iApply (imp_bind_par with "HSpec Hex").
      iIntros (c x) "HSpec' Hφx". simpl. simp iSpec.
      iApply ("Hmono" with "Hφx HSpec'").

    - (* Inductive case: multi-argument function *)
      unfold imp_EApp_prop.
      iIntros (η e Φ' Ψ ζ P) "HSpec"; iIntros (ex φx) "Hex".
      change [ex] with ([] ++ [ex]).
      iApply (imp_EApp_prop_induction_step τ η Ψ ζ e
              (λ e, EWP eval η e <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ x, Φ' x }})%I); first reflexivity.

    (* Define the intermediate specification P' *)
    set (P' := (λ# (tt : τ) m,
                 ∃ x : X,
                   φx x ∗
                   tapp P (x, tt) m)%I : τ -#> microvx -> iProp Σ).

    (* Use IH *)
    iPoseProof IH as "HIH".
    unfold imp_EApp_prop.
    iSpecialize ("HIH" $! η (EApp e ex) _ _ _ P' with "[HSpec Hex]").
    { simpl_eval.
      iApply (imp_bind_par with "HSpec Hex").
      iIntros (??) "HSpec Hφx /=".
      simp iSpec.
      iPoseProof (imp_mono_prot with "HSpec []") as "HSpec"; first iApply iEff_le_bottom.
      iNext. rewrite /continue /=.
      iApply (imp_wand with "[HSpec]").
      iApply (imp_wand_exn with "HSpec"); first iIntros (? []).

      iIntros (c) "HSpec /=".
      iApply (iSpec_mono with "HSpec").
      rewrite bi_tforall_equiv.
      iIntros (xs m) "HP".
      subst P'. cbn. rewrite tapp_bind.
      iFrame. }

    (* Apply monotonicity *)
    iApply (imp_EApp_mono with "HIH").

    iIntros "!>" (args Q). rewrite !tapp_bind.
    iIntros "H HQ %m (%x & Hφx & HP)".
    iSpecialize ("H" $! x with "Hφx").
    rewrite tapp_bind.
    iApply ("H" with "HQ HP").
  Qed.

  Definition imp_EApp_pers_prop `{Encode A} (τ : types) : iProp Σ :=
    ∀ (η : env) (e : expr) (Φ' : A -> iProp Σ) (Ψ : iEff Σ) ζ
      (P : τ -#> microvx -> iProp Σ),
    EWP eval η e <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ c, □ iSpec τ c P }} -∗
    accumulate_argument_premises_and_build_consequence_hyp
      η Ψ ζ e
      (λ e, EWP eval η e <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ v, Φ' v }})
      τ
      []
      (λ# (tt : τ) (Q : iProp Σ),
           Q -∗ ∀ m, (tapp P tt) m -∗ ▷ EWP m <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ v, Φ' v }}).

  Arguments imp_EApp_pers_prop {_ _} !τ /.
  Transparent imp_EApp_pers_prop.
  Strategy transparent [ imp_EApp_pers_prop ].

   Lemma imp_EApp_pers `{Encode A} (τ : types) :
    ⊢ @imp_EApp_pers_prop A _ τ.
   Proof.
     unfold imp_EApp_pers_prop.
     iIntros (η e Φ' Ψ ζ P) "He".
     iApply imp_EApp.
     iApply (imp_wand with "He").
     iIntros (?) "#$".
   Qed.

End imp_EApp_def.


(* We expect that sometimes we will not want to abstract a function and give it a spec.
   Rather, we will wish to evaluate it down to its body *)

Section transparent_funs.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ}.

 Lemma imp_EAnon_literal η a :
   ⊢ EWP (eval η (EAnonFun a)) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ v, ⌜v = VClo η a⌝ }}.
 Proof.
   simpl_eval.
   iApply imp_ret; auto.
 Qed.

 Lemma imp_EApp_literal B `{Encode A, Encode B} {Φ : A → iProp Σ} Φ1 η' v e η p e1 :
   lookup_path η p = Some (VClo η' (AnonFun v e)) →
   EWP (eval η e1) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
   (∀ (x : B), Φ1 x -∗
               ▷ EWP (eval ((v, #x) :: η') e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
   EWP (eval η (EApp (EPath p) e1)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
 Proof.
   iIntros (Hlookup) "He Hbody".
   simpl_eval.
   iApply (imp_bind_par (A1:=val) (A2:=B) with "[] He").
   { iApply imp_of_option.
     instantiate (1 := (λ f, ⌜f = (VClo η' (Anon (v => e)))⌝)%I).
     rewrite Hlookup. iExists _; auto. }
   iIntros (??) "-> HΦ".
   rewrite /continue /=.
   iApply imp_please.
   iApply ("Hbody" with "HΦ").
 Qed.

 Lemma imp_EApp_literal2 B C `{Encode A, Encode B, Encode C} {Φ : A → iProp Σ} Φ1 Φ2 η' v1 v2 e η p e1 e2 :
   lookup_path η p = Some (VClo η' (AnonFun v1 (EAnonFun (AnonFun v2 e)))) →
   EWP (eval η e1) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
   EWP (eval η e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
   (∀ (x : B) (y : C), Φ1 x -∗ Φ2 y -∗
               ▷^2 EWP (eval ((v2, #y) :: (v1, #x) :: η') e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
   EWP (eval η (EApp (EApp (EPath p) e1) e2)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
 Proof.
   iIntros (Hlookup) "He1 He2 Hbody". simpl_eval.
   iApply (imp_bind_par (A1:=val) (A2:=C) with "[He1] He2").
   { iApply (imp_bind_par (A1:=val) (A2:=B) with "[] He1").
     { iApply imp_of_option.
       instantiate (1 := (λ f, ⌜f = (VClo η' _)⌝)%I).
       rewrite Hlookup. iExists _; auto. }
     iIntros (??) "-> HΦ".
     rewrite /continue /=.
     iApply imp_please.
     iApply imp_wand. iApply imp_EAnon_literal.
     iIntros "!> !>" (v) "Hv". iCombine "Hv HΦ" as "Hv".
     instantiate (1 := (λ v, ∃ y, ⌜v = VClo (v1 ~> #y;
                    η') (Anon (v2 => e))⌝ ∗ Φ1 y)%I).
       simpl. iFrame. }
   iIntros (??) "(% & -> & HΦ1) HΦ2".
   rewrite /continue /=.
   iApply imp_please.
   iApply ("Hbody" with "HΦ1 HΦ2").
 Qed.

 Lemma imp_EApp_literal3 B C D `{Encode A, Encode B, Encode C, Encode D} {Φ : A → iProp Σ}
   Φ1 Φ2 Φ3 η' v1 v2 v3 e η p e1 e2 e3 :
   lookup_path η p = Some (VClo η' (AnonFun v1 (EAnonFun (AnonFun v2 (EAnonFun (AnonFun v3 e)))))) →
   EWP (eval η e1) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
   EWP (eval η e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
   EWP (eval η e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ3 }} -∗
   (∀ (x : B) (y : C) (z : D), Φ1 x -∗ Φ2 y -∗ Φ3 z -∗
               ▷^2 EWP (eval ((v3,#z) :: (v2, #y) :: (v1, #x) :: η') e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
   EWP (eval η (EApp (EApp (EApp (EPath p) e1) e2) e3)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
 Proof.
   iIntros (Hlookup) "He1 He2 He3 Hbody". simpl_eval.
   iApply (imp_bind_par (A1:=val) (A2:=D) with "[He1 He2] He3").
   { iApply (imp_bind_par (A1:=val) (A2:=C) with "[He1] He2").
     { iApply (imp_bind_par (A1:=val) (A2:=B) with "[] He1").
       iApply imp_of_option.
       instantiate (1 := (λ f, ⌜f = (VClo η' _)⌝)%I).
       rewrite Hlookup. iExists _; auto.
       iIntros (??) "-> HΦ".
       rewrite /continue /=.
       iApply imp_please.
       iApply imp_wand. iApply imp_EAnon_literal.
       iIntros "!> !>" (v) "Hv".
       instantiate (1 := (λ v, ∃ y, ⌜v = VClo _ _⌝ ∗ Φ1 y)%I).
       simpl. iFrame. }
     iIntros (??) "(% & -> & HΦ1) HΦ2".
     rewrite /continue /=.
     iApply imp_please.
     iApply imp_wand. iApply imp_EAnon_literal.
     iIntros "!> !>" (v) "->".
     instantiate (1 := (λ v, ∃ y z, ⌜v = VClo _ _⌝ ∗ Φ1 y ∗ Φ2 z)%I).
     simpl. iFrame. iPureIntro. reflexivity. }
   iIntros (??) "(% & % & -> & HΦ1 & HΦ2) HΦ3".
   rewrite /continue /=.
   iApply imp_please.
   iApply ("Hbody" with "HΦ1 HΦ2 HΦ3").
 Qed.

End transparent_funs.


Notation "'∀∀' t1 .. tn ; P" :=
  (∀.. (TS : TeleS (λ t1, .. (TeleS (λ tn, TeleO)) ..)),
   @tele_app
     (TeleS (λ t1, .. (TeleS (λ tn, TeleO)) ..))
     _
     (λ t1, .. (λ tn, P) ..) TS)%I
  (at level 50,
   t1 closed binder, tn closed binder).

  (* Notation "'types' t1 .. tn ; P" := *)
  (* (∀.. (TS : TeleS (λ t1, TeleS (λ (_ : Encode t1), .. (TeleS (λ tn, TeleS (λ (_ : Encode t1), TeleO))) ..))), *)
  (*  @tele_app *)
  (*    (TeleS (λ t1, TeleS (λ (_ : Encode t1), .. (TeleS (λ tn, TeleS (λ (_ : Encode t1), TeleO))) ..))) *)
  (*    _ *)
  (*    (λ t1 _, .. (λ tn _, P) ..) TS)%I *)
  (* (at level 50, *)
  (*  t1 closed binder, tn closed binder). *)

Notation "'{{' ∀ x .. y ; P } } c a .. b ':' τ1 .. τn τm {{ 'RET' v ; Q } }" :=
  (□
         iSpec
           (type_nel.Tcons τ1 (.. (type_nel.Tcons τn (Tbase τm)) ..))
           c
           (λ a, .. (λ b, λ (m : microvx),
             (∀ x, .. (∀ y,
               P -∗ EWP m {{ v, Q }}
             ) ..))
           ..)
       )%I
  (at level 20,
   x closed binder, y closed binder,
   τ1, τn, τm at level 9, c at level 9, Q at level 200,
   a closed binder, b closed binder,
   v at level 200 as pattern,
   format
     "'[hv' {{ '[' ∀ x .. y ; P ']' } } '/  ' c  '[' a .. b ']'  ':'  '[' τ1  ..  τn  τm ']' '/' {{  '[' 'RET'  v ;  '/' Q ']' } } ']'")
  : bi_scope.

Notation "'{{' P } } c a .. b ':' τ1 .. τn τm {{ 'RET' v ; Q } }" :=
  (□
         iSpec
           (type_nel.Tcons τ1 (.. (type_nel.Tcons τn (Tbase τm)) ..))
           c
           (λ a, .. (λ b, λ (m : microvx),
               P -∗ EWP m {{ v, Q }})
           ..)
       )%I
  (at level 20,
   τ1, τn, τm at level 9, c at level 9, Q at level 200,
   a closed binder, b closed binder,
   v at level 200 as pattern,
   format
     "'[hv' {{ '[' P ']' } } '/  ' c  '[' a .. b ']'  ':'  '[' τ1  ..  τn  τm ']' '/' {{  '[' 'RET'  v ;  '/' Q ']' } } ']'")
  : bi_scope.

Notation "'{{' ∀ x .. y ; P } } c a .. b ':' τ {{ 'RET' v ; Q } }" :=
  (□ iSpec (Tbase τ) c (λ a, .. (λ b, λ (m : microvx), (∀ x, .. (∀ y, P -∗ EWP m {{ v, Q }}) ..)) ..))%I
    (at level 20, x closed binder, y closed binder, τ, c at level 9, Q at level 200,
                  a closed binder, b closed binder, v at level 200 as pattern,
     format "'[hv' {{  '[' ∀  x .. y ;  P  ']' } }  '/  ' c  '[' a .. b ']'  ':'   τ  '/' {{  '[' 'RET' v ;  '/' Q  ']' } } ']'")
     : bi_scope.

Notation "'{{' P } } c a .. b ':' τ {{ 'RET' v ; Q } }" :=
  (□ iSpec (Tbase τ) c (λ a, .. (λ b, λ (m : microvx), P -∗ EWP m {{ v, Q }}) ..))%I
    (at level 20, τ, c at level 9, Q at level 200,
                  a closed binder, b closed binder, v at level 200 as pattern,
     format "'[hv' {{  '[' P  ']' } }  '/  ' c  '[' a .. b ']'  ':'   τ  '/' {{  '[' 'RET' v ;  '/' Q  ']' } } ']'")
     : bi_scope.
