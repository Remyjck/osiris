From osiris Require Import base.
From osiris.lang Require Import syntax encode notations locations.
From osiris.semantics Require Import semantics.
Require Import pure_rules.

Open Scope Z_scope.

(* This file defines judgements for Hoare-style reasoning on
   the auxiliary functions in [semantics/eval.v]. *)

(* -------------------------------------------------------------------------- *)

(* A judgement and a set of reasoning rules for pattern matching. *)

(* The judgement [pattern η p v φ ψ] means that, in the environment [η],
   matching the pattern [p] against the value [v] is safe and either
   results in an extended environment that satisfies [φ]
   or fails (by reducing to [throw ()]) and guarantees [ψ]. *)

Definition cpattern η δ p o (φ : env -> Prop) (ψ : Prop) :=
  pure (eval_cpat η δ p o) φ (λ (_ : unit), ψ).

Definition pattern η δ p v (φ : env -> Prop) (ψ : Prop) :=
  pure (eval_pat η δ p v) φ (λ (_ : unit), ψ).

Definition patterns η δ ps vs (φ : env -> Prop) (ψ : Prop) :=
  pure (eval_pats η δ ps vs) φ (λ (_ : unit), ψ).

(* [fpatterns η δ fps vs φ ψ] matches the field patterns [fps] against the
   (already loaded) field values [vs] of a record. Loading the fields from
   the heap is not a pure operation; it is handled by the Iris-level
   judgement [ipattern] (see [program_logic/rules/ipattern_rules.v]),
   which defers to [fpatterns] once the values are in hand. *)

Definition fpatterns η δ fps vs (φ : env -> Prop) (ψ : Prop) :=
  pure (eval_fpats η δ fps vs) φ (λ (_ : unit), ψ).

(* -------------------------------------------------------------------------- *)

Section pattern_rules.

  Implicit Type φ : env -> Prop.
  Implicit Type ψ : Prop.

  (* Monotonicity properties for [cpattern], [pattern], and [patterns]. *)

  Lemma cpattern_mono η δ p v (φ φ' : env -> Prop) (ψ ψ' : Prop) :
    cpattern η δ p v φ ψ →
    (∀ δ, φ δ → φ' δ) →
    (ψ → ψ') →
    cpattern η δ p v φ' ψ'.
  Proof.
    unfold cpattern; eauto using pure_mono.
  Qed.

  Lemma cpattern_env_mono η δ p v (φ φ' : env -> Prop) (ψ : Prop) :
    cpattern η δ p v φ ψ →
    (∀ δ, φ δ → φ' δ) →
    cpattern η δ p v φ' ψ.
  Proof. intros; by eapply cpattern_mono. Qed.

  Lemma cpattern_exn_mono η δ p v (φ : env -> Prop) (ψ ψ': Prop) :
    cpattern η δ p v φ ψ →
    (ψ → ψ') →
    cpattern η δ p v φ ψ'.
  Proof. intros; by eapply cpattern_mono. Qed.

  Lemma pattern_mono η δ p v (φ φ' : env -> Prop) (ψ ψ' : Prop) :
    pattern η δ p v φ ψ →
    (∀ δ, φ δ → φ' δ) →
    (ψ → ψ') →
    pattern η δ p v φ' ψ'.
  Proof.
    unfold pattern; eauto using pure_mono.
  Qed.

  Lemma pattern_env_mono η δ p v (φ φ' : env -> Prop) (ψ : Prop) :
    pattern η δ p v φ ψ →
    (∀ δ, φ δ → φ' δ) →
    pattern η δ p v φ' ψ.
  Proof. intros; by eapply pattern_mono. Qed.

  Lemma pattern_exn_mono η δ p v (φ : env -> Prop) (ψ ψ': Prop) :
    pattern η δ p v φ ψ →
    (ψ → ψ') →
    pattern η δ p v φ ψ'.
  Proof. intros; by eapply pattern_mono. Qed.

  Lemma patterns_mono η δ ps vs (φ φ' : env -> Prop) (ψ ψ' : Prop) :
    patterns η δ ps vs φ ψ →
    (∀ η, φ η → φ' η) →
    (ψ → ψ') →
    patterns η δ ps vs φ' ψ'.
  Proof.
    unfold patterns; eauto using pure_mono.
  Qed.

  Lemma patterns_env_mono η δ ps vs (φ φ' : env -> Prop) (ψ : Prop) :
    patterns η δ ps vs φ ψ →
    (∀ δ, φ δ → φ' δ) →
    patterns η δ ps vs φ' ψ.
  Proof. intros; by eapply patterns_mono. Qed.

  Lemma patterns_exn_mono η δ ps vs (φ : env -> Prop) (ψ ψ': Prop) :
    patterns η δ ps vs φ ψ →
    (ψ → ψ') →
    patterns η δ ps vs φ ψ'.
  Proof. intros; by eapply patterns_mono. Qed.

  (* -------------------------------------------------------------------------- *)

  (* Syntax-directed reasoning rules for the judgement [pattern]. *)

  (* From an operational point of view, the repeated application of these
    lemmas to a pattern [p] and a value [v] have the effect of translating
    the pattern matching operation [p = v] into a positive formula and a
    negative formula. The positive formula, the postcondition [φ],
    accumulates a sequence of universal quantifiers and equations that
    describe what is learnt when pattern matching succeeds. The negative
    formula, the failure postcondition [ψ], describes what is learnt when
    pattern matching fails. *)

  (* When a pattern cannot fail or can fail due to several distinct causes,
    a naive statement of its reasoning rule would have one occurrence of
    [ψ] in its conclusion and no occurrence or multiple occurrences of [ψ]
    in its premises. From an operational point of view, this is
    undesirable, because [ψ] is then unconstrained or duplicated. We avoid
    this phenomenon by using [False] or a disjunction in the conclusion of
    the reasoning rule. Thus, from an operational point of view, applying
    the reasoning rule instantiates the failure postcondition with a
    logical connective. *)

  Lemma pat_PAny η δ v φ :
    φ δ →
    pattern η δ PAny v φ False.
  Proof.
    unfold pattern. simpl_eval_pat. eauto using pure_ret.
  Qed.

  Lemma pat_PVar η δ x v φ :
    φ ((x, v) :: δ) →
    pattern η δ (PVar x) v φ False.
  Proof.
    unfold pattern. simpl_eval_pat. eauto using pure_ret.
  Qed.

  (* Given a goal of the form [pattern η (PVar x) v ?φ False],
    applying the lemma [pat_PVar2] solves the goal and
    instantiates the postcondition [?φ]. *)

  Lemma pat_PVar2 η δ x v :
    pattern η δ (PVar x) v (λ δ', δ' = (x, v) :: δ) False.
  Proof.
    by apply pat_PVar.
  Qed.

  Ltac pat_PVar :=
    match goal with
    | |- pattern _ (PVar _) _ _ _ =>
        (apply pat_PVar2 || eapply pat_PVar)
    end.

  Lemma pat_PAlias η δ p x v φ ψ :
    pattern η δ p v (λ δ, φ ((x, v) :: δ)) ψ →
    pattern η δ (PAlias p x) v φ ψ.
  Proof.
    unfold pattern. simpl_eval_pat; intros.
    eapply pure_bind. apply H.
    eauto using pure_mono, pure_ret.
  Qed.

  Lemma pure_orelse `{Observe A V} `{Observe B1 E1, Observe B2 E2}
  (m1 : micro V E1) (m2 : micro V E2) (φ : A → Prop)
  (Ψ1 : B1 → Prop) (Ψ2 : B2 → Prop) :
    pure m1 φ Ψ1 →
    (∀ e, Ψ1 e → pure m2 φ Ψ2) →
    pure (orelse m1 m2) φ Ψ2.
  Proof.
    intros Hm1 Hm2.
    eapply pure_wp_orelse; eauto.
    intros e1 (b1 & -> & HΨ1). eapply Hm2, HΨ1.
  Qed.

  Lemma pat_POr η δ p1 p2 v φ ψ1 ψ2 :
    pattern η δ p1 v φ ψ1 →
    (ψ1 → pattern η δ p2 v φ ψ2) →
    pattern η δ (POr p1 p2) v φ (ψ1 ∧ ψ2).
      (* The conjunction [ψ1 ∧ ψ2] reflects the fact that, for the
        disjunction pattern to fail, both sides must fail. *)
  Proof.
    unfold pattern. simpl_eval_pat; intros.
    eauto using pure_orelse, pure_mono.
  Qed.

  Lemma pat_PUnit η δ v φ :
    φ δ →
    v = #() →
    pattern η δ PUnit v φ False.
  Proof.
    unfold pattern. intros ? ->; simpl_eval_pat.
    eauto using pure_ret.
  Qed.

  Lemma pat_PTuple `{Encode A} η δ ps (a : A) vs φ ψ :
    #a = VTuple vs ->
    patterns η δ ps vs φ ψ →
    pattern η δ (PTuple ps) #a φ ψ.
  Proof.
    unfold patterns, pattern.
    intros ->. by simpl_eval_pat.
  Qed.

  Lemma pat_PTuple_val δ η ps vs φ ψ :
    patterns δ η ps vs φ ψ ->
    pattern δ η (PTuple ps) (VTuple vs) φ ψ.
  Proof.
    unfold pattern. by simpl_eval_pat.
  Qed.

  Lemma pat_PPair `{Encode A, Encode B} η δ p1 p2 v1 v2 (x1 : A) (x2 : B) φ ψ1 ψ2 :
    v1 = #x1 ->
    v2 = #x2 ->
    pattern η δ p1 #x1 (λ δ', pattern η δ' p2 #x2 φ (ψ2)) (ψ1) ->
    pattern η δ (PPair p1 p2) (VPair v1 v2) φ (ψ1 \/ ψ2).
  Proof.
    intros Heq1 Heq2 Hpat; subst.
    unfold pattern in Hpat |- *. simpl_eval_pat.
    eapply pure_strong_bind; [ apply Hpat | | tauto ].
    simpl; intros. rewrite !bind_ret_right.
    eapply pure_strong_bind; [ apply H1 | | tauto ].
    intros η' Hφ. rewrite bind_ret.
    eapply pure_ret; eauto.
  Qed.

  Lemma pat_PData_nil η δ c c' φ ψ :
    (c = c' -> φ δ) ->
    pattern η δ (PData c nil) (VData c' nil) φ (ψ ∨ c ≠ c').
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros. simpl_eval_pat.
    destruct_string_eqb;
      eauto using pure_throw, pure_mono, pure_ret.
  Qed.

  Lemma pat_PData_or η δ c c' ps vs φ ψ :
    (c = c' -> patterns η δ ps vs φ ψ) ->
    pattern η δ (PData c ps) (VData c' vs) φ (ψ ∨ c ≠ c').
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros. simpl_eval_pat.
    destruct_string_eqb; eauto using pure_throw.
    eapply pure_mono; first apply H; eauto.
  Qed.

  Lemma pat_PData_eq η δ c ps v vs φ ψ :
    v = VData c vs ->
    patterns η δ ps vs φ ψ →
    pattern η δ (PData c ps) v φ ψ.
      (* This form is useful when [c = c'] is statically known. The
         equation [v = VData c vs] is taken explicitly so that the
         caller can supply it via the [encode] hint database; this is
         needed because [encode.encode] is declared [Opaque] in the
         proofmode and so [#x] cannot be unified with [VData c vs] by
         [eapply] alone. *)
  Proof.
    unfold pattern; intros -> ?. simpl_eval_pat.
    destruct_string_eqb; solve [ eauto using pure_wp_throw | tauto ].
  Qed.

  Lemma pat_PData_neq η δ c ps c' v vs φ :
    v = VData c' vs ->
    c ≠ c' →
    pattern η δ (PData c ps) v φ True.
      (* This form is useful when [c ≠ c'] is statically known. See
         [pat_PData_eq] for why the [v = VData c' vs] equation is
         explicit. *)
  Proof.
    unfold pattern; intros -> ?. simpl_eval_pat.
    destruct_string_eqb; solve [ eauto using pure_throw | tauto ].
  Qed.

  Lemma pat_PData_neq_tagged η δ c ps c' v l φ :
    v = VTaggedRecord c' l ->
    c ≠ c' →
    pattern η δ (PData c ps) v φ True.
      (* This form is useful when [c ≠ c'] is statically known. See
         [pat_PData_eq] for why the [v = VData c' vs] equation is
         explicit. *)
  Proof.
    unfold pattern; intros -> ?. simpl_eval_pat.
    eauto using pure_throw.
  Qed.

  Lemma pat_PData η δ c ps c' v vs φ :
    v = VData c' vs ->
    (c = c' -> patterns η δ ps vs φ True) ->
    pattern η δ (PData c ps) v φ True.
  Proof.
    unfold pattern; intros. simpl_eval_pat. subst.
    destruct_string_eqb; solve [ eauto using pure_throw | tauto ].
  Qed.

  (* Rules for inline-record patterns. An inline-record pattern
     [PTaggedRecord c p] matches an inline-record value with the same
     constructor; the sub-pattern [p] is matched against the
     underlying record. *)

  Lemma pat_PTaggedRecord_or η δ c c' p l φ ψ :
    (c = c' -> pattern η δ p (VRecord l) φ ψ) ->
    pattern η δ (PTaggedRecord c p) (VTaggedRecord c' l) φ (ψ ∨ c ≠ c').
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros. simpl_eval_pat.
    destruct_string_eqb; eauto using pure_throw.
    eapply pure_mono; first apply H; eauto.
  Qed.

  Lemma pat_PTaggedRecord_eq η δ c p v l φ ψ :
    v = VTaggedRecord c l ->
    pattern η δ p (VRecord l) φ ψ →
    pattern η δ (PTaggedRecord c p) v φ ψ.
      (* This form is useful when [c = c'] is statically known. See
         [pat_PData_eq] for why the [v = VTaggedRecord c l] equation is
         explicit. *)
  Proof.
    unfold pattern; intros -> ?. simpl_eval_pat.
    destruct_string_eqb; solve [ eauto using pure_wp_throw | tauto ].
  Qed.

  Lemma pat_PTaggedRecord_neq η δ c p c' v l φ :
    v = VTaggedRecord c' l ->
    c ≠ c' →
    pattern η δ (PTaggedRecord c p) v φ True.
      (* This form is useful when [c ≠ c'] is statically known. *)
  Proof.
    unfold pattern; intros -> ?. simpl_eval_pat.
    destruct_string_eqb; solve [ eauto using pure_throw | tauto ].
  Qed.

  Lemma pat_PTaggedRecord_neq_data η δ c p c' v vs φ :
    v = VData c' vs ->
    c ≠ c' →
    pattern η δ (PTaggedRecord c p) v φ True.
      (* This form is useful when [c ≠ c'] is statically known. *)
  Proof.
    unfold pattern; intros -> ?. simpl_eval_pat.
    eauto using pure_throw.
  Qed.

  Lemma pat_PTaggedRecord η δ c p c' v l φ :
    v = VTaggedRecord c' l ->
    (c = c' -> pattern η δ p (VRecord l) φ True) ->
    pattern η δ (PTaggedRecord c p) v φ True.
  Proof.
    unfold pattern; intros. simpl_eval_pat. subst.
    destruct_string_eqb; solve [ eauto using pure_throw | tauto ].
  Qed.

  (* This more general version is not used in tactics at the moment *)
  Lemma pat_PXData η δ π ps l l' vs φ ψ :
    lookup_path η π = Some (VFieldLoc l') →
    (l = l' → patterns η δ ps vs φ ψ) →
    pattern η δ (PXData π ps) (VXData l vs) φ (ψ ∨ l ≠ l').
  Proof.
    unfold pattern. simpl_eval_pat. intros ->.
    change (as_field_loc (of_option (Some (VFieldLoc l')))) with (@ret _ unit l').
    rewrite bind_ret.
    destruct (eqb_spec l l').
    - firstorder eauto using pure_exn_mono.
    - intros. eapply pure_throw. encode. tauto.
  Qed.

  Lemma pat_PXData_eq η δ π ps l vs φ ψ :
    lookup_path η π = Some (VFieldLoc l) ->
    patterns η δ ps vs φ ψ →
    pattern η δ (PXData π ps) (VXData l vs) φ ψ.
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros Hlookup Hpat.
    simpl_eval_pat; rewrite Hlookup.
    unfold as_field_loc, val_as_field_loc; simpl; rewrite !bind_ret.
    unfold locations.eqb; destruct l; cbn.
    by rewrite Z.eqb_refl.
  Qed.

  Lemma pat_PXData_neq η δ π ps l1 l2 vs φ :
    lookup_path η π = Some (VFieldLoc l1) ->
    (address l1 <> address l2) ->
    pattern η δ (PXData π ps) (VXData l2 vs) φ True.
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros Hlookup Heq; simpl_eval_pat.
    rewrite Hlookup.
    unfold as_field_loc, val_as_field_loc; cbn; rewrite !bind_ret.
    unfold locations.eqb; simpl.
    destruct l1, l2; simpl in *.
    replace (address0 =? address) with false;
      last by apply eq_sym; apply Z.eqb_neq.
    eapply pure_throw. encode. tauto.
  Qed.

  Lemma pat_PXData_neq' η δ π ps l1 l2 vs :
    lookup_path η π = Some (VFieldLoc l1) ->
    (address l1 <> address l2) ->
    pattern η δ (PXData π ps) (VXData l2 vs) (λ _, False) True.
      (* This form is useful when the truth of the equality [c = c']
        is not statically known. *)
  Proof.
    unfold pattern; intros Hlookup Heq; simpl_eval_pat.
    rewrite Hlookup.
    unfold as_field_loc, val_as_field_loc; cbn; rewrite !bind_ret.
    unfold locations.eqb; simpl.
    destruct l1, l2; simpl in *.
    replace (address0 =? address) with false;
      last by apply eq_sym; apply Z.eqb_neq.
    eapply pure_throw. encode. tauto.
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* Syntax-directed reasoning rules for the auxiliary judgement [patterns]. *)

  Lemma pats_PNil η δ φ :
    φ δ →
    patterns η δ [] [] φ False.
  Proof.
    unfold patterns.
    simpl_eval_pats.
    eauto using pure_ret.
  Qed.

  Lemma pats_PCons_unary η δ p ps v vs φ ψ1 ψ2 :
    pattern η δ p v (λ δ, patterns η δ ps vs φ ψ2) ψ1 →
    patterns η δ (p :: ps) (v :: vs) φ (ψ1 \/ ψ2).
  Proof.
    unfold patterns, patterns. intros Hp; simpl_eval_pats.
    eapply pure_strong_bind; [ apply Hp | | tauto ].
    intros η' Hη'.
    eapply pure_strong_bind; [ apply Hη' | | tauto ].
    simpl; intros.
    eapply pure_ret; eauto.
  Qed.

  Lemma pats_PCons_unary_false η δ p ps v vs φ :
    pattern η δ p v (λ δ, patterns η δ ps vs φ False) False ->
    patterns η δ (p :: ps) (v :: vs) φ False.
  Proof.
    intros.
    assert (False \/ False -> False) as HFalse by tauto.
    eapply patterns_exn_mono; [ clear HFalse | exact HFalse ].
    by apply pats_PCons_unary.
  Qed.

  Lemma pats_PCons η δ p ps v vs φ' φ ψ1 ψ2 :
    pattern η δ p v φ' ψ1 →
    (∀ δ, φ' δ → patterns η δ ps vs φ ψ2) →
    patterns η δ (p :: ps) (v :: vs) φ (ψ1 ∨ ψ2).
  Proof.
    intros. eapply pats_PCons_unary.
    eapply pattern_mono; eauto.
  Qed.

  (* Rules for field patterns. *)

  Lemma fpatterns_mono η δ fps vs (φ φ' : env -> Prop) (ψ ψ' : Prop) :
    fpatterns η δ fps vs φ ψ →
    (∀ δ, φ δ → φ' δ) →
    (ψ → ψ') →
    fpatterns η δ fps vs φ' ψ'.
  Proof.
    unfold fpatterns; eauto using pure_mono.
  Qed.

  Lemma fpats_nil η δ vs φ ψ :
    φ δ →
    fpatterns η δ [] vs φ ψ.
  Proof.
    unfold fpatterns. simpl_eval_fpats.
    eauto using pure_ret.
  Qed.

  (* Given a goal [fpatterns η δ [] vs ?φ ?ψ], applying [fpats_nil2]
     solves the goal, instantiating the success postcondition [?φ] with
     an environment equality and the failure postcondition [?ψ] with
     [False] (compare [pat_PVar2]). *)

  Lemma fpats_nil2 η δ vs :
    fpatterns η δ [] vs (λ δ', δ' = δ) False.
  Proof.
    by apply fpats_nil.
  Qed.

  (* [vs] is in one-to-one correspondence with [fps]: its head is the
     value of the field that the head pattern selects. The field index
     [f] plays no role here; the selection happened in [loadfs], where the
     field was read. The head is named by an equation rather than by a
     [v :: vs'] pattern, so that the automation can normalize it (see
     [fpats] in [pure_tactics]). *)

  Lemma fpats_cons_unary η δ f p fps vs vs' v φ ψ1 ψ2 :
    vs = v :: vs' →
    pattern η δ p v (λ δ, fpatterns η δ fps vs' φ ψ2) ψ1 →
    fpatterns η δ ((f, p) :: fps) vs φ (ψ1 ∨ ψ2).
  Proof.
    unfold fpatterns. intros -> Hp. simpl_eval_fpats.
    eapply pure_strong_bind; [ apply Hp | | tauto ].
    intros δ' Hδ'.
    eapply pure_strong_bind; [ apply Hδ' | | tauto ].
    simpl; intros.
    eapply pure_ret; eauto.
  Qed.

  Lemma fpats_cons η δ f p fps vs vs' v φ' φ ψ1 ψ2 :
    vs = v :: vs' →
    pattern η δ p v φ' ψ1 →
    (∀ δ, φ' δ → fpatterns η δ fps vs' φ ψ2) →
    fpatterns η δ ((f, p) :: fps) vs φ (ψ1 ∨ ψ2).
  Proof.
    intros. eapply fpats_cons_unary; first eassumption.
    eapply pattern_mono; eauto.
  Qed.

  (* -------------------------------------------------------------------------- *)

  Local Ltac pats :=
    repeat first [
        eapply pats_PNil; [ eauto ]
      | eapply pats_PCons; [ eauto | simpl; intros ]
      ].

  (* -------------------------------------------------------------------------- *)

  Lemma pat_PConst η δ c c' φ :
    (c = c' -> φ δ) ->
    pattern η δ (PConstant c) (VConstant c') φ (c <> c').
  Proof.
    intros Hφ.
    eapply pattern_mono.
    { eapply pat_PData_or.
      intros Hc; specialize (Hφ Hc).
      pats. }
    { tauto. }
    { tauto. }
  Qed.

  Lemma pat_PConst_eq η δ c φ :
    φ δ ->
    pattern η δ (PConstant c) (VConstant c) φ False.
  Proof.
    intros Hφ.
    eapply pattern_exn_mono; [ eapply pat_PConst; eauto | tauto ].
  Qed.

  Lemma pat_PConst_neq η δ c c' e ψ :
    c <> c' ->
    ψ ->
    pattern η δ (PConstant c) (VData c' e) (λ _, False) ψ.
  Proof.
    intros Hneq Hψ.
    unfold pattern. simpl_eval_pat.
    apply String.eqb_neq in Hneq as ->.
    eapply pure_throw. encode. tauto.
  Qed.

  Lemma pat_PConst_neq_inline η δ c c' l ψ :
    c <> c' ->
    ψ ->
    pattern η δ (PConstant c) (VTaggedRecord c' l) (λ _, False) ψ.
  Proof.
    intros Hneq Hψ.
    unfold pattern. simpl_eval_pat.
    eapply pure_throw. encode. tauto.
  Qed.

  Lemma pat_false η δ v (P : Prop) φ :
    v = #P →
    (¬P → φ δ) →
    pattern η δ (PConstant "false") v φ P.
  Proof.
    intros -> ?; simpl.
    destruct (truth P) eqn:?.

    { eapply pattern_env_mono.
      eapply pat_PConst_neq;
        [ by simpl | by apply truth_true_elim].
      done. }

    { eapply pattern_exn_mono.
      eapply pat_PConst_eq;
        auto using truth_false_elim.
      tauto. }
  Qed.

  Lemma pat_true η δ v (P : Prop) φ :
    v = #P →
    (P → φ δ) →
    pattern η δ (PConstant "true") v φ (¬P).
  Proof.
    intros -> Hφ; simpl.
    destruct (truth P) eqn:?.

    { eapply pattern_exn_mono.
      eapply pat_PConst_eq;
        apply Hφ; by apply truth_true_elim.
      tauto. }

    { eapply pattern_env_mono.
      eapply pat_PConst_neq;
        [ by simpl | by apply truth_false_elim].
      intros; tauto. }
  Qed.

  Lemma pat_PInt η δ v (i j : Z) (φ : env → Prop) :
    int.representable i →
    int.representable j →
    v = #j →
    (i = j → φ δ) →
    pattern η δ (PInt i) v φ (i <> j).
  Proof.
    intros Hi Hj -> Hφ.
    unfold pattern; simpl_eval_pat.
    rewrite int.eq_repr_repr; auto.
    destruct (_ =? _) eqn:E.
    - eapply pure_ret. encode. apply Hφ. by apply Z.eqb_eq.
    - eapply pure_throw. encode. by apply Z.eqb_neq.
  Qed.

  (* -------------------------------------------------------------------------- *)

  Lemma cpat_CVal η δ p v φ ψ :
    pattern η δ p v φ ψ ->
    cpattern η δ (CVal p) (O2Ret v) φ ψ.
  Proof.
    tauto.
  Qed.

  Lemma cpat_CExc η δ p v φ ψ :
    pattern η δ p v φ ψ ->
    cpattern η δ (CExc p) (O2Throw v) φ ψ.
  Proof.
    tauto.
  Qed.

  Lemma cpat_COr η δ cp1 cp2 o φ ψ1 ψ2 :
    cpattern η δ cp1 o φ ψ1 ->
    (ψ1 → cpattern η δ cp2 o φ ψ2) ->
    cpattern η δ (COr cp1 cp2) o φ (ψ1 /\ ψ2).
  Proof.
    unfold cpattern. intros.
    eapply pure_orelse; [ eassumption | ].
    eauto using pure_mono.
  Qed.

  Lemma cpat_CEff η δ peff pk v k φ ζ1 :
    pattern η δ peff v (λ δ, pattern η δ pk (VCont k) φ False) ζ1 ->
    cpattern η δ (CEff peff pk) (O3Perform v k) φ ζ1.
  Proof.
    unfold cpattern, pattern; intros. simpl.
    eapply pure_bind_unary.
    eapply pure_ret_mono. apply H. intros η' Hη'.
    eapply pure_exn_mono. apply Hη'. tauto.
  Qed.

  Fixpoint valid_cpattern_match {A E} cp (o : outcome3 A E) :=
    match cp, o with
    | CVal _, O3Ret _
    | CExc _, O3Throw _
    | CEff _ _, O3Perform _ _ =>
        true
    | COr cp1 cp2, _ =>
        valid_cpattern_match cp1 o || valid_cpattern_match cp2 o
    | _, _ =>
        false
    end.

  Lemma invert_valid_match cp o :
    valid_cpattern_match cp o = false ->
    ∀ η δ, eval_cpat η δ cp o = throw ().
  Proof.
    intros Hvalid η δ.
    induction cp; destruct o; simpl in *; try congruence;
      (* Only the [COr cp1 cp2] case remains. *)
      unfold orelse;
      apply orb_false_elim in Hvalid as [H1 H2];
      apply IHcp1 in H1; apply IHcp2 in H2;
      by rewrite H1, H2, !try_throw.
  Qed.

  Lemma cpat_mismatch η δ cp o φ (ψ : Prop) :
    valid_cpattern_match cp o = false ->
    ψ ->
    cpattern η δ cp o φ ψ.
  Proof.
    intros.
    unfold cpattern.
    rewrite invert_valid_match by assumption.
    eapply pure_throw. encode. tauto.
  Qed.

  (* -------------------------------------------------------------------------- *)

  (* Syntax-directed reasoning for data *)

  (* The following reasoning rules exemplify a general approach for matching
    against algebraic data types. *)

  Lemma pat_pNil `{Encode A} η δ v (xs : list A) φ :
    v = #xs →
    (xs = [] -> φ δ) →
    (* Enter the branch with knowledge that [xs] is empty *)
    pattern η δ pNil v φ (xs ≠ []).
    (* If the match is unsuccessful, move to the next branch
      with the knowledge that [xs] is not empty *)
  Proof.
    intros; subst.
    destruct xs; eapply pattern_exn_mono.
    { eapply pat_PConst; eauto. }
    { tauto. }
    { eapply pat_PData_neq; [ reflexivity | done ]. }
    { congruence. }
  Qed.

  (* [pat_pCons_cut] exists for pedagogical purposes.
    We use [pat_pCons] in practice to avoid headaches caused
    by evar instantiation scopes. *)

  Lemma pat_pCons_cut `{Encode A} v xs η δ p1 p2 φ (φ1 : A -> env -> Prop)
    (ψ1 : A -> Prop) (ψ2 : list A -> Prop)
    :
    v = #xs ->
    (∀ (x : A) (xs' : list A),
        xs = x :: xs' →
        pattern η δ p1 #x (φ1 x) (ψ1 x)) ->
        (* If [#x] matches [p1], we gain the knowledge [φ1 x η0].
          Otherwise, we gain the knowledge [ψ1 x] *)
    (∀ (x : A) (xs' : list A),
        xs = x :: xs' →
        (forall δ', φ1 x δ' -> pattern η δ' p2 #xs' φ (ψ2 xs'))) ->
        (* If [#xs'] does not match [p2], then we gain the knowledge [ψ2 xs'] *)
    pattern η δ (pCons p1 p2) v φ (xs = [] \/ (exists x xs', xs = x :: xs' /\ (ψ1 x \/ ψ2 xs'))).
    (* There are three ways the match can be unsuccessful:
      - the list is empty
      - the list is non-empty, but its head did not match [p1]
      - the list is non-empty, but its tail did not match [p2] *)
  Proof.
    intros; subst.
    destruct xs.
    { eapply pattern_exn_mono.
      { eapply pat_PData_neq; [ reflexivity | done ]. }
      tauto. }
    { eapply pattern_exn_mono.
      { eapply pat_PData_eq; [ reflexivity | pats ]. }
      right; do 2 eexists; split; [ reflexivity | tauto ]. }
  Qed.

  Lemma pat_pCons `{Encode A} v xs η δ p1 p2 φ
    (ψ1 : A -> Prop) (ψ2 : list A -> Prop)
    :
    v = #xs ->
    (∀ (x : A) (xs' : list A),
        xs = x :: xs' →
        pattern η δ p1 #x
          (λ δ',
            pattern η δ' p2 #xs' φ (ψ2 xs'))
          (ψ1 x)) ->
    pattern η δ (pCons p1 p2) v φ
      (xs = [] \/ (exists x xs', xs = x :: xs' /\ (ψ1 x \/ ψ2 xs'))).
  Proof.
    intros; subst.
    destruct xs; eapply pattern_exn_mono.
    { eapply pat_PData_neq. encode. auto. }
    { tauto. }
    { eapply pat_PData_eq; pats. encode. }
    { clear; right; do 2 eexists; split; [ reflexivity | tauto ]. }
  Qed.

  (* The previous lemmas start to give us a general scheme for reasoning about
    pattern matching on ADTs.

    More experimenting is required.
    As of now (29/02/24), see [examples/splay.v] for more examples. *)

  (* Pattern proofmode tactics *)


  Definition is_not_O3Throw {A X} (o : outcome3 A X) :=
    match o with
    | O3Throw _ => False
    | _ => True
    end.

  Definition is_not_O3Ret {A X} (o : outcome3 A X) :=
    match o with
    | O3Ret _ => False
    | _ => True
    end.

  Definition is_not_O3Perform {A X} (o : outcome3 A X) :=
    match o with
    | O3Perform _ _ => False
    | _ => True
    end.

  Lemma cpat_CExc_abst η δ p o φ ψ :
    (forall e, o = O3Throw e -> pattern η δ p e φ ψ) ->
    cpattern η δ (CExc p) o φ (is_not_O3Throw o ∨ ψ).
  Proof.
    intros Hpat.
    unfold cpattern.
    destruct o; simpl.
    - eapply pure_throw. encode. by left.
    - eapply pure_mono; [ apply Hpat | auto | auto ].
      reflexivity.
    - eapply pure_throw. encode. by left.
  Qed.

  Lemma cpat_CVal_abst η δ p o φ ψ :
    (forall v, o = O3Ret v -> pattern η δ p v φ ψ) ->
    cpattern η δ (CVal p) o φ (is_not_O3Ret o ∨ ψ).
  Proof.
    intros Hpat.
    unfold cpattern.
    destruct o; simpl.
    - eapply pure_mono; [ apply Hpat | auto | auto ].
      reflexivity.
    - eapply pure_throw. encode. by left.
    - eapply pure_throw. encode. by left.
  Qed.

  Lemma cpat_CEff_abst η δ peff pk o φ ψ1 ψ2 :
    (forall eff k,
        o = O3Perform eff k ->
        pattern η δ peff eff (λ δ, pattern η δ pk (VCont k) φ ψ2) ψ1) ->
    cpattern η δ (CEff peff pk) o φ (is_not_O3Perform o ∨ ψ1 ∨ ψ2).
  Proof.
    intros Hpat.
    unfold cpattern.
    destruct o; simpl.
    - eapply pure_throw. encode. by left.
    - eapply pure_throw. encode. by left.
    - eapply pure_bind_unary.
      eapply pure_mono; [ apply Hpat; reflexivity | | auto ].
      intros δ' Hpat2.
      eapply pure_mono; [ apply Hpat2 | auto | auto ].
  Qed.

  Lemma cpat_CEff_impossible η δ peff pk (o : outcome2 val exn) φ :
    cpattern η δ (CEff peff pk) o φ True.
  Proof.
    unfold cpattern.
    destruct o; simpl; by eapply pure_throw.
  Qed.

End pattern_rules.
