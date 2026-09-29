From Stdlib.Logic Require Import FunctionalExtensionality.
From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.

Require Import wp pure_rules judgements pattern_rules.

(* A judgement for the evaluation of let bindings. *)

Definition bindings `{Encode B} η bs (φ : env -> Prop) (ζ : B -> Prop) :=
  pure (eval_bindings η bs) φ ζ.

Lemma pure_irrefutably_extend `{Observe B E} η δ p v (φ : env → Prop) (ψ : B → Prop) :
  pattern η δ p v φ False →
  pure (irrefutably_extend η δ p v) φ ψ.
Proof.
  intros Hpat.
  apply pure_wp_try, (pure_wp_mono _ Hpat);
    firstorder eauto with pure.
Qed.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [bindings]. *)

Lemma bindings_cons_unary `{Encode A, Encode B} η p e bs φ :
  pure (eval η e) (λ a : A, bindings η bs (λ η', pattern η η' p #a φ False) (⊥ : B → Prop)) (⊥ : B → Prop) ->
  bindings η (Binding p e :: bs) φ (⊥ : B → Prop).
Proof.
  unfold bindings. simpl. intros He.
  simpl_eval_bindings. eapply pure_bind_unary.
  eapply pure_par_seq; eauto.
  eapply pure_ret_mono. { apply He. } intros a Ha.
  eapply pure_ret_mono. { apply Ha. } intros η' Hpat.
  apply pure_irrefutably_extend. apply Hpat.
  Unshelve. all: eauto with pure.
Qed.

Lemma bindings_cons `{Encode A, Encode B} η p e bs (φ1 : A -> Prop) φ2 φ (ψ : B → Prop) :
  pure (eval η e) φ1 ψ ->
  bindings η bs φ2 ψ ->
  (∀ (a : A) (η' : env), φ1 a -> φ2 η' -> pattern η η' p #a φ False) ->
  bindings η (Binding p e :: bs) φ ψ.
Proof.
  intros He Hbs Hp.
  unfold bindings.
  simpl_eval_bindings. eapply pure_bind_unary.
  eapply pure_par; eauto.
  intros a1 η' Hφ1 Hφ2.
  apply pure_irrefutably_extend.
  apply Hp; auto.
Qed.

Lemma bindings_nil `{Encode B} η (φ : env -> Prop) (ψ : B → Prop) :
  φ [] ->
  bindings η [] φ ψ.
Proof.
  unfold bindings. simpl_eval_bindings. apply pure_ret. encode.
Qed.

Lemma bindings_var `{Encode A, Encode B} η v e bs (φ : A -> Prop) φ' (ψ : B → Prop) :
  pure (eval η e) φ ψ ->
  bindings η bs φ' ψ ->
  bindings η
    (Binding (PVar v) e :: bs)
    (λ η,
      ∃ a η', φ a /\ φ' η' /\ η = (v, #a) :: η') ψ.
Proof.
  intros.
  eapply bindings_cons; eauto.
  intros; unfold pattern. simpl_eval_pat.
  eapply pure_ret; eauto.
Qed.

Lemma bindings_pair `{Encode A, Encode B, Encode C} η p1 p2 e bs (φ : env → Prop) φ'
  (φ_pair : τ[A;B] -> Prop) (ψ : C → Prop) :
  pure (eval η e) φ_pair ψ ->
  bindings η bs φ' ψ ->
  (∀ ab η', φ_pair ab -> φ' η' -> pattern η η' (PPair p1 p2) #ab φ False) ->
  bindings η (Binding (PPair p1 p2) e :: bs) φ ψ.
Proof.
  intros Hpure Hbs Hpat.
  eapply bindings_cons; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* More flexible cons rule *)

Section eval_pat_app.
  Local Ltac rew := repeat (unfold orelse, try, glue2, continue || rewrite ?bind_as_try, ?try2_try2; simpl).
  Local Ltac ext x := let o := fresh "o" in f_equal; extensionality o; destruct o as [ x | ]; auto.

  Lemma eval_pat_app_aux η ps :
  list_all@{Prop; Set Set} pat
      (λ p : pat,
         ∀ (v : val) (δ : env), eval_pat η δ p v = 'δ' ← eval_pat η [] p v;
                                                   ret (δ' ++ δ))
      ps →
  ∀ (vs : list val) (δ : env),
  eval_pats η δ ps vs = 'δ' ← eval_pats η [] ps vs;
                        ret (δ' ++ δ).
  Proof.
   induction ps; intros Hinv vs δ.
   - destruct vs; simpl_eval_pats; try reflexivity.
   - simpl_eval_pats. destruct vs; first done.
     inversion Hinv as [ | ? Hpat ? Hpats ]; subst.
     rewrite Hpat. rewrite !bind_bind. f_equal. extensionality δ'.
     rewrite bind_ret, bind_bind.
     rewrite IHps; last assumption. rewrite (IHps Hpats vs δ').
     rewrite !bind_bind.
     f_equal. extensionality δ''.
     rewrite !bind_ret. by rewrite app_assoc.
  Qed.

  Lemma eval_pat_app p v η δ : eval_pat η δ p v = 'δ' ← eval_pat η [] p v; ret (δ' ++ δ).
  Proof.
    revert p v δ.
    induction p; intros ? ?; intros; simpl_eval_pat || simpl_eval_pats || idtac; simpl; auto.
    - rewrite IHp. rewrite !bind_bind. reflexivity.
    - rewrite IHp1, IHp2. rew. ext δ'.
    - destruct v; auto. apply eval_pat_app_aux; assumption.
    - destruct v; auto. destruct (_ =? _)%string; auto.
      apply eval_pat_app_aux; assumption.
    - destruct v; auto. destruct (lookup_path η π); last by unfold bind.
      unfold as_field_loc; simpl; rewrite bind_ret.
      destruct v0; simpl; try by rewrite !bind_crash.
      rewrite !bind_ret.
      destruct (locations.eqb _ _); auto.
      apply eval_pat_app_aux; assumption.
    - destruct v; auto.
      rew. f_equal. ext o. simpl; unfold continue; simpl.
      destruct o. rew. f_equal. ext vs.
      clear m l0. revert vs. generalize dependent δ.
      induction fps.
      + simpl_eval_fpats. reflexivity.
      + simpl_eval_fpats. intros δ vs.
        inversion H as [ | ? Hfpat ? Hpats ]; subst.
        specialize (IHfps Hpats). clear Hpats.
        destruct a.
        destruct vs; first reflexivity.
        inversion Hfpat as [ ? ? ? Hpat ]; subst.
        rewrite Hpat. rewrite bind_bind.
        rew. f_equal. extensionality o. destruct o; last reflexivity.
        rewrite bind_ret, !bind_ret_right.
        rewrite IHfps.
        rewrite (IHfps a). rewrite try2_try2.
        f_equal. extensionality o; destruct o; last done.
        simpl; unfold continue. by rewrite app_assoc.
    - destruct v; auto. destruct (_ =? _)%string; auto.
    - destruct v; auto.
      rew. f_equal. ext o. rew.
      destruct o. rew. f_equal. ext o. case_decide; last done.
      rewrite eval_pat_app_aux; last assumption.
      by rewrite bind_as_try2.
    - destruct v; auto. destruct (int.eq _ _); auto.
    - destruct v; auto. destruct (_ =? _)%char; auto.
    - destruct v; auto. destruct (_ =? _)%string; auto.
  Qed.
End eval_pat_app.

Lemma pattern_app η δ p v φ ψ :
  pattern η δ p v φ ψ ↔ pattern η [] p v (λ δ', φ (δ' ++ δ)) ψ.
Proof.
  unfold pattern, pure.
  rewrite eval_pat_app, <-pure_wp_reversible_bind.
  apply pure_wp_ret_equiv; intros δ'.
  rewrite <-pure_wp_reversible_ret. unfold returns.
  split; intros (? & Heq & Hφ).
  - exists δ'. rewrite Heq. eauto.
  - exists (δ' ++ δ). simpl in Heq. rewrite <- Heq in Hφ. eauto.
Qed.

Definition binding `{Encode A, Encode B} η p e φ (ψ : B → Prop) :=
  pure (eval η e) (λ a : A, pattern η [] p #a φ False) ψ.

Lemma binding_bindings_conseq `{Encode A, Encode B} η p e bs (φ1 φ2 φ : env → Prop) (ψ : B → Prop) :
  binding (A := A) η p e φ1 ψ →
  bindings η bs φ2 ψ →
  (∀ δ η', φ1 δ → φ2 η' → φ (δ ++ η')) →
  bindings η (Binding p e :: bs) φ ψ.
Proof.
  intros He Hbs Hp.
  eapply bindings_cons; eauto.
  intros a η' Hpa Hη'.
  apply pattern_app.
  eapply pure_ret_mono. apply Hpa. eauto.
Qed.

Instance observe_injective_id `{NotVal A} : @ObserveInjective A A _.
Proof. constructor. intros ??; simpl; auto. Qed.

(* May be easier to use but assumes [e] cannot raise exceptions *)
Lemma binding_bindings `{Encode A, Encode B} η p e bs (φ1 φ2 φ : env → Prop) (ψ : B → Prop) :
  binding (A := A) η p e (λ δ, bindings η bs (λ η', φ (δ ++ η')) ψ) (⊥ : B → Prop) →
  bindings η (Binding p e :: bs) φ ψ.
Proof.
  intros He.
  unfold bindings.
  simpl_eval_bindings. eapply pure_bind_unary.
  eapply pure_par_seq.
  eapply pure_ret_mono. { apply He. } intros a Hpat_a.
  apply invert_pure_order in Hpat_a.
  eapply pure_ret_mono. { apply Hpat_a. }
  intros η' Hpat_η'.
  apply pure_irrefutably_extend.
  eapply (pattern_app η η' p ♯a φ ⊥).
  apply Hpat_η'.
  Unshelve. all: eauto with pure.
Qed.
