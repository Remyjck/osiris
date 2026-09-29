From osiris Require Import base.
From osiris.lang Require Import syntax encode notations locations.
From osiris.semantics Require Import semantics.

Require Import
  pure_rules pattern_rules binding_rules call_rules expr_rules.

(* This file defines contains reasoning rules about top-level definitions,
   such as struct items, bindings, and modules. *)

(* -------------------------------------------------------------------------- *)

(* A judgement for the evaluation of structure items. *)

Definition struct_item ηδ item (φ : envs -> Prop) :=
  pure (eval_sitem ηδ item) φ (λ _ : void, False).

Definition struct_items ηδ sitems (φ : envs -> Prop) :=
  pure (eval_sitems ηδ sitems) φ (λ _ : void, False).


(* A judgement for the evaluation of module expressions. *)

Definition eval_module η me (φ : env -> Prop) :=
  pure (eval_mexpr η me) φ (λ _ : void, False).


(* A judgement for module coercion. *)

Definition coerces c η (φ : env -> Prop) :=
  pure (of_option (coerce c (VStruct η))) φ (λ _ : void, False).

(* -------------------------------------------------------------------------- *)

Lemma struct_consequence ηδ item (φ φ' : envs -> Prop) :
  struct_item ηδ item φ ->
  (∀ ηδ, φ ηδ -> φ' ηδ) ->
  struct_item ηδ item φ'.
Proof.
  unfold struct_item. eauto using pure_mono.
Qed.

(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [structs]. *)

Lemma structs_nil ηδ (φ : envs -> Prop) :
  φ ηδ ->
  struct_items ηδ [] φ.
Proof.
  unfold struct_items.
  simpl_eval_sitems.
  apply pure_ret. destruct ηδ. auto.
Qed.

Lemma structs_cons_unary ηδ item items (φ : envs -> Prop) :
  struct_item ηδ item (λ ηδ', struct_items ηδ' items φ) ->
  struct_items ηδ (item :: items) φ.
Proof.
  unfold struct_items, struct_item. intros.
  simpl_eval_sitems.
  apply (pure_bind_unary (A':=envs) (A:=envs)).
  eapply pure_mono; eauto. intros [??]. auto.
Qed.

Lemma structs_cons ηδ item items φ ψ :
  struct_item ηδ item ψ ->
  (∀ ηδ', ψ ηδ' -> struct_items ηδ' items φ) ->
  struct_items ηδ (item :: items) φ.
Proof.
  unfold struct_items, struct_item. intros.
  simpl_eval_sitems.
  eapply pure_bind; eauto.
  intros [??]; auto.
Qed.

(* Syntax-directed reasoning rules for the judgement [struct]. *)

Lemma struct_let η δ bs (φ : envs -> Prop) ψ :
  bindings η bs ψ (⊥ : void → Prop) ->
  (∀ η', ψ η' -> φ (η' ++ η, η' ++ δ)) ->
  struct_item (η, δ) (ILet bs) φ.
Proof.
  unfold struct_item; simpl_eval_sitem; intros.
  eapply pure_bind; eauto.
  intros.
  eapply pure_ret; eauto. encode.
Qed.

Lemma unfold_struct_letrec η δ rbs (φ : envs -> Prop) ψ :
  ψ (eval_rec_bindings η rbs) ->
  (∀ η', ψ η' -> φ (η' ++ η, η' ++ δ)) ->
  struct_item (η, δ) (ILetRec rbs) φ.
Proof.
  unfold struct_item; intros.
  simpl_eval_sitem.
  eapply pure_ret; eauto. encode.
Qed.

Lemma struct_let_single η δ e name (spec : val -> Prop) :
  pure (eval η e) spec (⊥ : void → Prop) ->
  struct_item (η, δ) (ILet [Binding (PVar name) e])
    (λ '(η0, δ0),
      ∃ clo, spec clo /\
                   η0 = [(name, clo)] ++ η /\
                   δ0 = [(name, clo)] ++ δ) .
Proof.
  intros; unfold struct_item; simpl_eval_sitem.
  eapply pure_bind_unary.
  eapply bindings_cons. { eapply H. } { apply bindings_nil. apply eq_refl. }
  intros v ? Hspec <-.
  apply pat_PVar.
  eapply (pure_ret _ _ _ ((name ¬> #v) ++ η, (name ¬> #v) ++ δ)); eauto.
Qed.

Lemma struct_let_pat η δ p e (spec : val -> Prop) (φ : envs -> Prop) ψ :
  pure (eval η e) (λ v, pattern η [] p v ψ False) (⊥ : void → Prop) ->
  (∀ η', ψ η' -> φ (η' ++ η, η' ++ δ)) ->
  struct_item (η, δ) (ILet [Binding p e]) φ.
Proof.
  intros; unfold struct_item; simpl_eval_sitem.
  eapply pure_bind_unary.
  eapply bindings_cons. { eapply H. } { apply bindings_nil. apply eq_refl. }
  intros v ? Hpat <-.
  simpl in Hpat.
  eapply pattern_mono; [ apply Hpat | | auto ].
  intros η' HΨ.
  eapply pure_ret; eauto. encode.
Qed.

Lemma struct_letrec_single η δ name af (spec : val -> Prop) :
  spec (VCloRec η [RecBinding name af] name) ->
  struct_item (η, δ)
    (ILetRec [RecBinding name af])
    (λ '(η0, δ0),
      ∃ clo, spec clo /\
               η0 = [(name, clo)] ++ η /\
               δ0 = [(name, clo)] ++ δ) .
Proof.
  intros; unfold struct_item.
  simpl_eval_sitem.
  eapply (pure_ret _ _ _ (name ~> VCloRec η [RecBinding name af] name;
         η, name ~> VCloRec η [RecBinding name af] name;
         δ)); eauto.
Qed.

Lemma struct_external η δ x e (spec : val -> Prop) :
  pure (eval [] e) spec (⊥ : void → Prop) ->
  struct_item (η, δ) (IExternal x e)
    (λ '(η0, δ0),
      ∃ clo, spec clo /\
                   η0 = [(x, clo)] ++ η /\
                   δ0 = [(x, clo)] ++ δ).
Proof.
  intros; unfold struct_item.
  simpl_eval_sitem.
  apply pure_wp_bind.
  eapply pure_wp_mono_ret. eassumption.
  intros f (? & -> & ?).
  eapply (pure_ret _ _ _ (x ~> ♯x0;
   η, x ~> ♯x0;
   δ)); eauto.
Qed.

Lemma struct_module η δ m me (φ : envs -> Prop) (φ' : env -> Prop) :
  eval_module η me φ' ->
  (∀ η', φ' η' -> φ ((m, VStruct η') :: η, (m, VStruct η') :: δ)) ->
  struct_item (η, δ) (IModule m me) φ.
Proof.
  unfold struct_item; intros.
  simpl_eval_sitem.
  eapply pure_bind; eauto.
  intros η' Hφ'. eapply pure_ret; eauto. encode.
Qed.

Lemma struct_open η δ me (φ : envs -> Prop) (φ' : env -> Prop) :
  eval_module η me φ' ->
  (∀ η', φ' η' -> φ (η' ++ η, δ)) ->
  struct_item (η, δ) (IOpen me) φ.
Proof.
  unfold struct_item; intros.
  simpl_eval_sitem.
  eapply pure_bind.
  { unfold as_struct.
    eapply pure_bind; eauto.
    intros η' Hφ'. eapply (pure_ret (A:=env)); eauto. }
  intros η' Hφ'. eapply pure_ret; eauto. encode.
Qed.

Lemma struct_include η δ me (φ : envs -> Prop) module_spec :
  eval_module η me module_spec ->
  (∀ η', module_spec η' ->
         φ (η' ++ η, η' ++ δ)) ->
  struct_item (η, δ) (IInclude me) φ.
Proof.
  unfold struct_item; intros.
  simpl_eval_sitem.
  eapply pure_bind.
  { unfold as_struct.
    eapply pure_bind; eauto.
    intros η' Hφ'. eapply (pure_ret (A:=env)); eauto. }
  intros η' Hφ'. eapply pure_ret; eauto. encode.
Qed.

(* Rec *)

Lemma struct_letrec_function `{Encode X, Encode Y} `{Encode C}
  `{WF_x : WellFounded X}
  η δ f bs
  (φf : X -> Y -> Prop)
  (Ψ : envs -> Prop)
  (R : X -> X -> Prop)
  (P : X -> Prop)
  (ζ : C → Prop) :
  (∀ vf x,
    (∀ y,
        wf_relation (WF := WF_x) y x ->
        R y x ->
        P y ->
        pure (call vf #y) (φf y) ζ) ->
      P x ->
      branches (("__osiris_anonymous_arg", #x) :: (f, vf) :: η) (O3Ret #x) bs (φf x) ζ) ->
  (∀ vf, (∀ x, P x -> pure (call vf #x) (φf x) ζ) -> Ψ ((f, vf) :: η, (f, vf) :: δ)) ->
  struct_item (η, δ) (ILetRec [RecBinding f (AnonFunction bs)]) Ψ.
Proof.
  intros Hvf Hnext.
  eapply unfold_struct_letrec. cbn.
  apply eq_refl.
  intros ? <-. eapply Hnext.
  intros x HP.
  eapply pure_rec_call; eauto.
  intros ????.
  eapply pure_eval_match. { eapply pure_eval_path; reflexivity. }
  eauto.
Qed.

Lemma struct_letrec2 `{Encode X, Encode Y, Encode W} `{WF_xy : WellFounded (X * Y)} (A : Type)
  η δ f arg1 arg2 e
  (Ψ : envs -> Prop)
  (φf : A -> X -> Y -> W -> Prop)
  (R : (X * Y) -> (X * Y) -> Prop)
  (P : A -> X -> Y -> Prop)
  (ζ : A -> exn -> Prop) :
  (∀ vf x1 y1 a,
      (∀ x2 y2,
          wf_relation (WF := WF_xy) (x2, y2) (x1, y1) ->
          R (x2, y2) (x1, y1) ->
          P a x2 y2 ->
          pure_call2 vf #x2 #y2 (φf a x2 y2) (ζ a)) ->
      P a x1 y1 ->
      pure (eval ((arg2, #y1) :: (arg1, #x1) :: (f, vf) :: η) e)
        (φf a x1 y1) (ζ a)) ->
  (∀ vf,
      (∀ a x y, P a x y -> pure_call2 vf #x #y (φf a x y) (ζ a)) ->
      Ψ ((f, vf) :: η, (f, vf) :: δ)) ->
  struct_item (η, δ) (ILetRec [RecBinding f (AnonFun arg1 (EAnonFun (AnonFun arg2 e)))]) Ψ.
Proof.
  intros Hvf Hnext.
  eapply unfold_struct_letrec. cbn.
  apply eq_refl.
  intros ? <-. eapply Hnext.
  intros a x y HP.
  eapply pure_rec_call2; eauto.
  intros ?????.
  eapply pure_eval_anonfun. simpl. apply pure_stop_eval.
  rewrite try2_inject2_right.
  eauto.
Qed.

Lemma struct_letrec `{Encode X, Encode Y} `{Encode C} `{WF_x : WellFounded X}
  η δ f arg e1
  (φf : X -> Y -> Prop)
  (Ψ : envs -> Prop)
  (R : X -> X -> Prop)
  (P : X -> Prop) (ζ : C → Prop) :
  (∀ vf x,
      (∀ y,
          wf_relation (WF := WF_x) y x ->
          R y x ->
          P y ->
          pure (call vf #y) (φf y) ζ) ->
      P x ->
      pure (eval ((arg, #x) :: (f, vf) :: η) e1) (φf x) ζ) ->
  (∀ vf, (∀ x, P x -> pure (call vf #x) (φf x) ζ) -> Ψ ((f, vf) :: η, (f, vf) :: δ)) ->
  struct_item (η, δ) (ILetRec [RecBinding f (AnonFun arg e1)]) Ψ.
Proof.
  intros Hvf Hnext.
  eapply unfold_struct_letrec. cbn.
  apply eq_refl.
  intros ? <-. eapply Hnext.
  intros x HP.
  eapply pure_rec_call; eauto.
Qed.


(* -------------------------------------------------------------------------- *)

(* Syntax-directed reasoning rules for the auxiliary judgement [module]. *)

#[export]
  Hint Extern 1 (returns _ _) => unfold returns; by firstorder : pure.

Lemma pure_wp_module η me φ :
  eval_module η me φ ->
  pure (eval_mexpr η me) φ (⊥ : void → Prop).
Proof.
  repeat intro.
  eapply pure_mono; intros; eauto with pure.
Qed.

Lemma module_struct η sitems φ :
  struct_items (η, []) sitems (λ '(η, δ), φ δ) ->
  eval_module η (MStruct sitems) φ.
Proof.
  intros; unfold eval_module.
  simpl_eval_mexpr.
  eapply pure_bind; [ eassumption | ].
  intros [??] Hφ.
  eapply pure_ret; eauto.
Qed.

Lemma module_struct_let η bs sitems φ ψ :
  bindings η bs ψ (⊥ : void → Prop) ->
  (∀ η', ψ η' ->
         struct_items (η' ++ η, η') sitems (λ '(_, δ), φ  δ)) ->
  eval_module η (MStruct ((ILet bs) :: sitems)) φ.
Proof.
  intros Hbs Hψsitems.
  eapply module_struct.
  { eapply structs_cons_unary.
    eapply struct_let; [ eassumption | ].
    intros; rewrite app_nil_r; by apply Hψsitems. }
Qed.

Lemma module_path η π φ m :
  lookup_path η π = Some #m →
  φ m →
  eval_module η (MPath π) φ.
Proof.
  intros Hlookup Hφ.
  unfold eval_module; simpl_eval_mexpr.
  eapply pure_wp_widen.
  rewrite Hlookup.
  exists m. auto.
Qed.

Lemma module_coercion η me c φ :
  eval_module η me φ ->
  (∀ η', φ η' -> coerces c η' φ) ->
  eval_module η (MCoercion me c) φ.
Proof.
  intros; unfold eval_module.
  simpl_eval_mexpr.
  eapply pure_bind; [ eassumption | ].
  intros m Hφ.
  unfold coerces in *; auto.
Qed.
