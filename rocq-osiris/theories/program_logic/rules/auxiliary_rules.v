From iris.proofmode Require Import proofmode.
From Equations Require Import Equations.

From osiris.lang Require Import lang.
From osiris.semantics Require Import eval.
Require Import ewp.
Require Import impure_rules stop_rules.
From osiris.program_logic Require Import fun_spec.

From osiris.pure_logic Require Import pattern_rules.

(** This file contains [EWP] rules for module and binding evaluation. *)

Section imp_eval.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ}.

  Lemma imp_module sitems {Q : env -> iProp Σ} η :
    EWP (eval_sitems (η, []) sitems) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ((_, δ) : envs), Q δ }} -∗
    EWP (eval_mexpr η (MStruct sitems)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hsitems".
    simpl_eval_mexpr.
    iApply (imp_bind with "Hsitems").
    iIntros ([η' δ']) "HQ".
    iApply (imp_ret with "HQ"). encode.
  Qed.

  Lemma imp_sitems_cons {Q : envs → iProp Σ} (φ : envs → iProp Σ) sitem sitems (ηδ : envs) :
    EWP (eval_sitem ηδ sitem) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ φ }} -∗
    (∀ ηδ, φ ηδ -∗ EWP eval_sitems ηδ sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    EWP (eval_sitems ηδ (sitem :: sitems)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hsitem Hcov".
    simpl_eval_sitems. iApply (imp_bind with "Hsitem").
    iIntros ([η' δ']) "Hφ".
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma imp_sitems_nil Q ηδ :
    Q ηδ -∗
    EWP eval_sitems ηδ [] @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    simpl_eval_sitems.
    iIntros "HQ". destruct ηδ.
    by iApply (imp_ret with "HQ").
  Qed.

  Lemma imp_sitem_letrec_singleton (spec : val → iProp Σ) x af (η δ : env) :
    spec (VCloRec η [RecBinding x af] x) -∗
    EWP (eval_sitem (η, δ) (ILetRec [RecBinding x af])) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{
          λ '(η0, δ0),
            ∃ clo, spec clo ∧ ⌜η0 = (x, clo) :: η⌝ ∧ ⌜δ0 = (x, clo) :: δ⌝
      }}.
  Proof.
    iIntros "Hspec".
    simpl_eval_sitem.
    iApply imp_ret. instantiate (1:=(_,_)). reflexivity.
    iExists _. iFrame.
    iSplit; iPureIntro; reflexivity.
  Qed.

  Lemma imp_sitems_letrec sitems (spec : val → iProp Σ) x af (η δ : env) Q :
    spec (VCloRec η [RecBinding x af] x) -∗
    (∀ v, spec v -∗ EWP (eval_sitems ((x, v) :: η, (x, v) :: δ) sitems) @ E <|Ψ|>
      ⟨⟨ζ⟩⟩ {{ Q }}) -∗
    EWP (eval_sitems (η, δ) ((ILetRec [RecBinding x af]) :: sitems)) @ E <|Ψ|>
      ⟨⟨ζ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hspec Hcov".
    iApply (imp_sitems_cons with "[Hspec]").
    { iApply (imp_sitem_letrec_singleton with "Hspec"). }
    iIntros ([??]) "(% & Hspec & [-> ->])".
    iApply ("Hcov" with "Hspec").
  Qed.

  Lemma imp_struct_let bs (Q : envs → iProp Σ) (Q' : env → iProp Σ) η δ :
    EWP (eval_bindings η bs) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q' }} -∗
    (∀ η', Q' η' -∗ Q (η' ++ η, η' ++ δ)) -∗
    EWP (eval_sitem (η, δ) (ILet bs)) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hbindings Hmono".
    simpl_eval_sitem.
    iApply (imp_bind with "Hbindings").
    iIntros (η') "HQ'".
    iApply imp_ret; first (instantiate (1:=(_,_)); encode).
    iApply ("Hmono" with "HQ'").
  Qed.

  Lemma imp_bindings_cons `{Encode A} (Φ : A → iProp Σ) η e bs Q P p :
    EWP eval η e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    (∀ (a : A), Φ a -∗ ⌜pattern η [] p #a (P a) False⌝) -∗
    EWP eval_bindings η bs @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }} -∗
    EWP eval_bindings η (Binding p e :: bs) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩
      {{ η, ∃ a η' δ', ⌜η = η' ++ δ'⌝ ∗ Φ a ∗ ⌜P a η'⌝ ∗ Q δ' }}.
  Proof.
    iIntros "He Hpat Hbs".
    simpl_eval_bindings.
    iApply (imp_bind_par (A1:=A) with "He Hbs").
    iIntros (a δ') "HΦ HQ !>".
    iDestruct ("Hpat" with "HΦ") as "%Hpat".
    iApply (imp_wand _ _ _ _ (λ η, ⌜∃ η', η = η' ++ δ' ∧ P a η'⌝)%I with "[] [-]"); last first.
    { iIntros (?) "(%η' & -> & %HP)".
      iFrame. by iFrame "%". }
    iApply (impure_pure (B:=unit)).
    apply binding_rules.pure_irrefutably_extend.
    eapply (iffRL (binding_rules.pattern_app η δ' p #a _ False)).
    eapply pattern_env_mono. { apply Hpat. }
    intros η' HP. exists η'. auto.
  Qed.

  Lemma imp_bindings_nil η :
    ⊢ EWP eval_bindings η [] @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ η, ⌜η = []⌝ }}.
  Proof.
    simpl_eval_bindings.
    iApply imp_ret. reflexivity. auto.
  Qed.

  Lemma imp_bind_var `{Encode A} (Φ : A → iProp Σ) η e name :
    EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    EWP eval_bindings η [Binding (PVar name) e] @ E <| Ψ |> ⟨⟨ ζ ⟩⟩
          {{ (η' : env), ∃ a : A, Φ a ∧ ⌜η' = [(name, #a)]⌝ }}.
  Proof.
    iIntros "HSpec".
    iApply (imp_wand with "[HSpec]").
    { iApply (imp_bindings_cons with "HSpec").
      - iIntros (a) "HΦ".
        iPureIntro; apply pat_PVar.
        instantiate (1:=(λ a η, η = [(name, #a)])).
        reflexivity.
      - iApply imp_bindings_nil. }
    iIntros (η') "(%a & % & % & -> & HΦ & -> & ->)".
    iFrame. auto.
  Qed.

  Lemma imp_struct_let_single `{Encode A} (spec : A → iProp Σ) name e (η δ : env) :
    EWP (eval η e) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ spec }} -∗
    EWP (eval_sitem (η, δ) (ILet [Binding (PVar name) e])) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{
          λ '(η', δ'),
            ∃ a : A, spec a ∧ ⌜η' = (name, #a) :: η ∧ δ' = (name, #a) :: δ⌝
      }}.
  Proof.
    iIntros "Hspec".
    iApply (imp_struct_let with "[Hspec]").
    { iApply (imp_bind_var with "Hspec"). }
    iIntros (?) "(%a & Hspec & ->)".
    iFrame. iPureIntro; split; reflexivity.
  Qed.

  Lemma imp_sitem_extend es (Q : envs -> iProp Σ) (η δ : env) :
    EWP eval_type_extensions es @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (δ' : env), Q (δ' ++ η, δ' ++ δ) }} -∗
    EWP eval_sitem (η,δ) (IExtend es) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hes".
    simpl_eval_sitem.
    iApply (imp_bind _ _ (λ δ', ret (δ' ++ η, δ' ++ δ)) with "Hes").
    iIntros (η') "HQ".
    iApply (imp_ret with "HQ"); reflexivity.
  Qed.

  Lemma imp_sitems_extend sitems x Q η δ :
    (∀ l, l ↦ₗ #() -∗
          EWP eval_sitems ((x, #l) :: η, (x, #l) :: δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    EWP eval_sitems (η,δ) ((IExtend [x]) :: sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hcov".
    iApply (imp_sitems_cons).
    { iApply (imp_sitem_extend).
      iApply imp_bind. iApply imp_alloc.
      iIntros (l) "Hl"; simpl; iApply imp_ret. reflexivity.
      Unshelve.
      2: (apply (λ ηδ,
                   (∃ l, ⌜ηδ = ((x, #l) :: η, (x, #l):: δ)⌝ ∗ l ↦ₗ VUnit)%I)).
      simpl.
      iExists l; iFrame. iPureIntro; reflexivity. }
    iIntros ([??]) "(% & -> & Hl)".
    iApply ("Hcov" with "Hl").
  Qed.

  Lemma imp_sitem_open me Q φ (η δ : env) :
    EWP eval_mexpr η me @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ φ }} -∗
    ( ∀ δ', φ δ' -∗ Q (δ' ++ η, δ) ) -∗
    EWP eval_sitem (η, δ) (IOpen me) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hme Hcov". simpl_eval_sitem.
    iApply (imp_bind with "[Hme]").
    { iApply (imp_as_struct with "Hme"). }
    iIntros (η') "Hφ".
    iApply imp_ret; first (instantiate (1:=(_,_)); encode).
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma imp_sitem_module m me Q (φ : env → iProp Σ) (η δ : env) :
    EWP eval_mexpr η me @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ φ }} -∗
    ( ∀ δ', φ δ' -∗ Q ((m, #δ') :: η, (m, #δ') :: δ) ) -∗
    EWP eval_sitem (η, δ) (IModule m me) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hme Hcov". simpl_eval_sitem.
    iApply (imp_bind with "Hme").
    iIntros (η') "Hφ".
    iApply imp_ret; first (instantiate (1:=(_,_)); encode).
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma imp_sitems_module {m me sitems Q} (φ : env → iProp Σ) (η δ : env) :
    EWP eval_mexpr η me @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ φ }} -∗
    ( ∀ δ', φ δ' -∗ EWP eval_sitems ((m, #δ') :: η, (m, #δ') :: δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    EWP eval_sitems (η, δ) ((IModule m me) :: sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hme Hcov".
    iApply (imp_sitems_cons with "[Hme]").
    { iApply (imp_sitem_module with "Hme").
      iIntros (δ') "Hφ".
      instantiate (1 := (λ ηδ, ∃ δ', φ δ' ∗ ⌜ηδ = (_,_)⌝)%I).
      iFrame. auto. }
    iIntros (?) "(% & Hφ & ->)".
    iApply ("Hcov" with "Hφ").
  Qed.

  Lemma imp_type_extension_cons e es Q :
    ▷ (∀ l, l ↦ₗ #() -∗
            EWP eval_type_extensions es @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ δ, Q ((e, #l) :: δ) }}) -∗
    EWP eval_type_extensions (e :: es) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hes". simpl.
    iApply (imp_bind with "[Hes]").
    { iApply imp_alloc2. iIntros "!>" (l) "Hl".
      iSpecialize ("Hes" with "Hl").
      iExact "Hes". }
    iIntros (l) "Hes".
    iApply (imp_bind with "Hes").
    iIntros (η) "HQ".
    iApply (imp_ret with "HQ"). reflexivity.
  Qed.

  Lemma imp_type_extension_nil :
    ⊢ EWP eval_type_extensions [] @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ η, ⌜η = []⌝ }}.
  Proof. simpl. by iApply imp_ret. Qed.

  Lemma imp_let `{Encode A} (spec : A → iProp Σ) x e Q η δ :
    EWP eval η e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ spec }} -∗
    (∀ a, spec a -∗ Q ((x, #a) :: η, (x, #a) :: δ)) -∗
    EWP eval_sitem (η, δ) (ILet [Binding (PVar x) e]) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "He HQ".
    iApply (imp_wand _ (eval_sitem (η, δ) (ILet [Binding (PVar x) e])) with "[He]").
    iApply (imp_struct_let_single with "He").
    iIntros ([η' δ']) "(%a & Ha & -> & ->)".
    iApply ("HQ" with "Ha").
  Qed.

  Lemma imp_sitems_let `{Encode A} (spec : A → iProp Σ) sitems x e Q η δ :
    EWP eval η e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ spec }} -∗
      (∀ a, spec a -∗
            EWP eval_sitems ((x, #a) :: η, (x, #a) :: δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
      EWP eval_sitems (η, δ) ((ILet [Binding (PVar x) e])::sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "He Hcov".
    iApply (imp_sitems_cons with "[He]").
    iApply (imp_let with "He").
    instantiate (1 := (λ ηδ, ∃ a, spec a ∗ ⌜ηδ = (x ~> #a; η, x ~> #a; δ)⌝)%I).
    iIntros (a) "Ha". iFrame. auto.
    iIntros (ηδ) "(%a & Ha & ->)".
    iApply ("Hcov" with "Ha").
  Qed.

  Lemma imp_sitems_external Φ sitems x e Q η δ :
    EWP eval [] e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    (∀ v, Φ v -∗ EWP eval_sitems ((x, v) :: η, (x, v) :: δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    EWP eval_sitems (η, δ) ((IExternal x e)::sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "He Hcov".
    iApply (imp_sitems_cons with "[He]").
    { simpl_eval_sitem.
      instantiate (1 := (λ ηδ, ∃ x0, ⌜ηδ = (x ~> x0; η, x ~> x0; δ)⌝ ∗ Φ x0)%I).
      iApply (imp_bind with "He").
      iIntros (?) "HΦ".
      iApply imp_ret; first (instantiate (1:=(_,_)); encode).
      by iFrame. }
    iIntros (?) "(% & -> & HΦ)".
    iApply ("Hcov" with "HΦ").
  Qed.

  (* ---------------------------------------------------------------------- *)

  (** Löb induction for [ILetRec].

      [imp_sitem_letrec_singleton] and [imp_sitems_letrec] above demand that
      the caller already establish the specification of the recursive closure.
      That is unworkable in practice: the whole point of a recursive function
      is that its own specification is available at the recursive call sites.
      The rules below close that gap by performing the Löb induction once and
      for all, in terms of [iSpec].

      They cover a [let rec] with a single binding, which is what
      [eval_rec_bindings] makes tractable: for a singleton [rbs], the
      environment fragment it produces is just [(f, clo)], so calling the
      recursive closure coincides with calling an ordinary closure whose
      environment binds [f] to itself. Mutually recursive groups would need
      a family of specifications, one per binding, and are not handled here. *)

  (* Calling the recursive closure [VCloRec η [RecBinding f a] f] is the very
     same computation as calling the plain closure [VClo ((f, clo) :: η) a].
     [call] looks [f] up in the singleton binding group, finds [a], and runs
     it in [eval_rec_bindings η rbs ++ η], which is exactly [(f, clo) :: η]. *)

  Lemma call_VCloRec_singleton f a η v :
    call (VCloRec η [RecBinding f a] f) v
    = call (VClo ((f, VCloRec η [RecBinding f a] f) :: η) a) v.
  Proof. simpl. rewrite String.eqb_refl. reflexivity. Qed.

  (* [iSpec] inspects its function value only through [call], so two values
     that are called alike have the same specifications. *)

  Lemma iSpec_call_ext (τ : types) (c1 c2 : val) P :
    (∀ v, call c1 v = call c2 v) →
    iSpec τ c1 P ⊣⊢ iSpec τ c2 P.
  Proof.
    intros Hcall. destruct τ as [X|X ? τ']; simp iSpec;
      apply bi.forall_proper => x; by rewrite Hcall.
  Qed.

  (* [iSpec_letrec] is the Löb induction principle for a recursive closure.

     To establish [iSpec τ clo P] for the closure [clo] built by
     [let rec f = fun x -> e], it suffices to establish the specification
     over the function body, that is [predicate_over_function_body] (the
     same premise [imp_EAnon_pers] asks for), in the environment
     [(f, clo) :: η], while *assuming* [iSpec τ clo P] one step later.

     The later is not a restriction in practice: entering the body of [f]
     costs a step (see [acall]/[imp_please]), so the induction hypothesis is
     always available by the time a recursive call is reached. *)

  Lemma iSpec_letrec (τ : types) (P : τ -#> microvx -> iProp Σ) f x e η :
    □ (▷ (□ iSpec τ (VCloRec η [RecBinding f (AnonFun x e)] f) P) -∗
       predicate_over_function_body τ P
         ((f, VCloRec η [RecBinding f (AnonFun x e)] f) :: η)
         (EAnonFun (AnonFun x e))) -∗
    □ iSpec τ (VCloRec η [RecBinding f (AnonFun x e)] f) P.
  Proof.
    iIntros "#Hbody".
    iLöb as "IH".
    rewrite (iSpec_call_ext τ _ _ P (call_VCloRec_singleton f (AnonFun x e) η)).
    iApply prove_iSpec_pers.
    iModIntro. iApply ("Hbody" with "IH").
  Qed.

  (* The [ILetRec] rule proper: evaluating [let rec f = fun x -> e] as a
     structure item binds [f], in both environments, to a value satisfying
     [iSpec τ _ P]. *)

  Lemma imp_sitem_letrec_iSpec (τ : types) (P : τ -#> microvx -> iProp Σ)
      f x e (η δ : env) :
    □ (▷ (□ iSpec τ (VCloRec η [RecBinding f (AnonFun x e)] f) P) -∗
       predicate_over_function_body τ P
         ((f, VCloRec η [RecBinding f (AnonFun x e)] f) :: η)
         (EAnonFun (AnonFun x e))) -∗
    EWP (eval_sitem (η, δ) (ILetRec [RecBinding f (AnonFun x e)])) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{
          λ '(η0, δ0),
            ∃ c, (□ iSpec τ c P) ∧ ⌜η0 = (f, c) :: η⌝ ∧ ⌜δ0 = (f, c) :: δ⌝
      }}.
  Proof.
    iIntros "#Hbody".
    iApply imp_sitem_letrec_singleton.
    by iApply iSpec_letrec.
  Qed.

  (* The same rule, threaded through the rest of a structure: this is the
     form used when walking down the items of a module. *)

  Lemma imp_sitems_letrec_iSpec (τ : types) (P : τ -#> microvx -> iProp Σ)
      f x e sitems (η δ : env) Q :
    □ (▷ (□ iSpec τ (VCloRec η [RecBinding f (AnonFun x e)] f) P) -∗
       predicate_over_function_body τ P
         ((f, VCloRec η [RecBinding f (AnonFun x e)] f) :: η)
         (EAnonFun (AnonFun x e))) -∗
    (∀ c, □ iSpec τ c P -∗
          EWP (eval_sitems ((f, c) :: η, (f, c) :: δ) sitems) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    EWP (eval_sitems (η, δ) (ILetRec [RecBinding f (AnonFun x e)] :: sitems)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "#Hbody Hcont".
    iApply (imp_sitems_letrec _ (λ c, □ iSpec τ c P)%I with "[] Hcont").
    by iApply iSpec_letrec.
  Qed.

  (* ---------------------------------------------------------------------- *)

  Lemma imp_sitems_open Φ sitems me Q η δ :
    impure E (eval_mexpr η me) Ψ ζ Φ -∗
    (∀ δ', Φ δ' -∗ impure E (eval_sitems (δ' ++ η, δ) sitems) Ψ ζ Q) -∗
    impure E (eval_sitems (η, δ) ((IOpen me) :: sitems)) Ψ ζ Q.
  Proof.
    iIntros "Hme Hcov".
    iApply (imp_sitems_cons with "[Hme]").
    { iApply (imp_sitem_open with "Hme").
      instantiate (1 := (λ ηδ, ∃ δ', ⌜ηδ = (δ' ++ η, δ)⌝ ∗ Φ δ')%I).
      iIntros (δ') "$ //". }
    iIntros (?) "(%δ' & -> & HΦ)".
    iApply ("Hcov" with "HΦ").
  Qed.

End imp_eval.
