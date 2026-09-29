From osiris Require Import osiris.
From osiris.examples Require Import og_find.

From Stdlib Require Import Wellfounded.Inverse_Image.

Section pure_specifications.

(** Specification for [iter]. *)

(* We first give a generalized specification for [iter],
   where we assume that [iter] is being called on the suffix [lsuf] of a larger list. *)

Definition listiter_spec_inv `{Encode A} (f : val) (lsuf : list A) (m : microvx) : Prop :=
  ∀ (lpre l : list A) (I : list A → Prop) `(Encode B) (φ : B → Prop),
    lpre ++ lsuf = l ->
    Spec τ[A] f (λ (X : A) (mf : microvx),
        ∀ (Xs : list A),
          (Xs ++ [X]) `prefix_of` l ->
          I Xs ->
          pure mf
            (λ v : (), I (Xs ++ [X])) (λ e, φ e ∧ I Xs)) ->
      I lpre ->
      pure m
        (λ (v : ()), I l)
        (λ e, φ e ∧ ∃ Xs, I Xs ∧ Xs `prefix_of` l).

(* [listiter_spec] is the actual specification of [iter]. *)

Definition listiter_spec `{Encode A} (f : val) (l : list A) (m : microvx) : Prop :=
  (* For any invariant [I] over the list and exception specification [φ]. *)
  ∀ (I : list A → Prop) `(Encode B) (φ : B → Prop),
    (* If [f] is a function taking one argument [X] of type [A]. *)
    Spec τ[A] f (λ (X : A) (mf : microvx),
        (* Such that for any prefix [Xs] of [l] such that [Xs ++ [X]] is also a prefix of [l]. *)
        ∀ (Xs : list A),
          (Xs ++ [X]) `prefix_of` l ->
          (* Under the assumption that the invariant holds over the prefix of [l]. *)
          I Xs ->
          (* Then calling [f] either succeeds and the invariant is extended,
             or fails with postcondition [φ]. *)
          pure mf
            (λ v : (), I (Xs ++ [X])) (λ e, φ e ∧ I Xs)) ->
    (* If the invariant [I] holds over the empty list (base case). *)
    I [] ->
    (* Then calling [iter] either succeeds and the invariant holds over the whole list,
       or fails with postcondition [φ] and invariant holds for some prefix of the list. *)
    pure m
      (λ (v : ()), I l)
      (λ e, φ e ∧ ∃ Xs, I Xs ∧ Xs `prefix_of` l).

(* An intermediate specification which holds for the lambda expression used by [iter]. *)

Context `{Encode A}.
Context (ℓ : loc).
Inductive exception := Found (a : A).

Local Instance encode_exception : Encode exception :=
  { encode' := λ e, match e with | Found a => VXData ℓ [ #a ] end }.

Local Instance xdata_found : XData ℓ τ[A] exception :=
  { xctor_apply := λ a, Found a;
    xctor_encode := λ a, eq_refl }.

Definition lambda_spec (l : list A) φ (X : A) (m : microvx) : Prop :=
  ∀ (Xs : list A),
    (Xs ++ [X]) `prefix_of` l ->
    Forall (λ x, ¬ (φ x)) Xs ->
    pure m
      (λ (v :()), Forall (λ x, ¬ (φ x)) (Xs ++ [X]))
      (λ e, (∃ (x : A), e = Found x ∧ x ∈ l ∧ φ x) ∧ Forall (λ x, ¬ (φ x)) Xs).

End pure_specifications.

(* -------------------------------------------------------------------------- *)

(* Well-foundedness *)

#[local] Program Instance list_tuple_wf {A B} : WellFounded (B * list A) :=
  {| wf_relation := (fun x y => (length x.2 < length y.2)%nat )|}.
Next Obligation. intros; apply wf_inverse_image, lt_wf. Qed.


(* -------------------------------------------------------------------------- *)

Section iris_proof.

Context `{Encode A}.
Context `{!osirisGS Σ}.

(* The specification of our [find_first] function. *)

Definition find_spec find : iProp Σ :=
  {{ ∀ (φ : A -> Prop);
     (* Assuming that [pred] is a pure function such that
        [pred x] reflects the pure proposition [φ x]*)
     ∀ `(Encode B), ⌜Spec τ[A] pred (λ x mx, pure mx (λ (P : Prop), P <-> φ x) (⊥ : B → Prop))⌝ }}
  (* Calling [find l pred] returns an option [o] such that
     - if [o = Some x] then [φ x]
     - if [o = None] then there is no [x] such that [φ x]. *)
  find l pred : (list A) val
  {{ RET (o : option A); ⌜match o with
                          | Some x => x ∈ l ∧ φ x
                          | None => Forall (λ x, ¬ (φ x)) l
                          end⌝ }}.

(* Our high level statement:
   "After evaluation the [__main] module corresponding to the whole
    [find.ml] file, we get a module with a value in the "find_first"
    field which is specified by [find_spec]." *)


Lemma iter_module_pure η :
  ⊢ EWP (eval_mexpr η __main)
    {{ context [
         var_spec "find_first" find_spec
       ]
       {["find_first";"iter"]} }}.
Proof.
  (* Enter the module and face the struct items. *)
  iApply imp_module.
  (* Process the first structure item. *)
  iApply imp_sitems_cons.
  (* After evaluating the first struct item, we will enrich the scoping
     environment with some value [iter] such that
     [Spec τ[val; list A] iter listiter_spec]. *)
  instantiate (1 := (λ (ηδ : envs),
            ⌜∃ iter, ηδ = (("iter", iter) :: η, [("iter",iter)]) ∧
                     Spec τ[val; list A] iter listiter_spec⌝)%I).
  { (* Proof of [iter]. *)
    iApply (impure_pure (B:=void) (eval_sitem (η, []) (ILetRec __iter_bindings))).
    (* Enter the body of the recursive function. *)
    eapply (struct_letrec τ[val; list A]) with (P := listiter_spec_inv).
    { (* Side-condition: the expression is a function. *) repeat eexists. }
    { (* Give the decreasing argument to justify recursive calls *)
      apply list_tuple_wf. }
    { (* Enter the body *) simpl.
      intros iter f l IH.
      unfold listiter_spec_inv.
      intros lpre lsuf I B HencB φ Heql Hf HI.
      eapply pure_please_eval. abstract_env.

      (* Evaluate the [function] expression. *)
      eapply pure_eval_match. { (* Evaluation the scrutinee. *) pure_path. }
      pure_match.

      (* First branch of the function. *)
      { pure_const. rewrite app_nil_r. apply HI. }
      (* Second branch of the function. *)
      rename xs' into l.
      eapply pure_eval_seq.
      { (* Evaluate [f x]. *)
        eapply (pure_EApp τ[A]). { pure_path. apply Hf. } pure_path.
        simpl.
        intros ? <- callsite_f Hcall_f.
        (* Prove that the exceptional postcondition is of the right form. *)
        eapply pure_exn_mono.
        { apply Hcall_f; eauto.
          apply prefix_app. apply prefix_cons. apply prefix_nil. }
        intros e (Hφ & _).
        split; first assumption.
        exists lpre. split; first assumption.
        replace lpre with (lpre ++ []) at 1 by apply app_nil_r.
        apply prefix_app; apply prefix_nil. }
      (* Evaluate the second half of the sequence: [iter f l]. *)
      intros Hlprex.
      eapply (pure_EApp τ[val; list A]).
      { pure_path. eassumption. }
      { pure_path. } { pure_path. }
      simpl; unfold tapp.
      intros ?? <-<- m Hm; unfold listiter_spec in Hm.
      (* Justify the recursive call: the measure has decreased and
         the preconditions are satisfied. *)
      eapply Hm; [ lia | | apply Hf | apply Hlprex ].
      change (x :: l) with ([x] ++ l); by rewrite app_assoc. }

    (* Weaken the invariant specification to [listiter_spec]. *)
    intros iter Hiter.
    exists iter; split; first reflexivity.
    eapply Spec_mono; [ apply Hiter | simpl ].
    intros f l m Hinvspec; unfold listiter_spec, tapp.
    intros I φ Hf HI.
    specialize (Hinvspec [] l).
    apply Hinvspec; auto. }

  (* Introduce our expanded environment which now contains [iter]. *)
  iIntros (?) "(%iter & -> & %Hiter)".
  (* We now face the toplevel definition of [find_elem]. *)
  iApply (imp_sitems_let
            (* We give [find_elem] the specification [find_spec]. *)
            find_spec).

  { (* Start of the proof from the paper *)
    (* Subgoal: Prove that [find_elem] satisfies its specification. *)
    (* Step into the function's body *)
    unfold find_spec.
    iApply (imp_EAnon_pers τ[list A; val]).
    (* Introduce the function's arguments. *)
    iIntros "!>" (l pred φ Hpred).
    (* Declare and open a local module. *)
    iApply imp_please. iNext.
    iApply imp_ELetOpen.
    (* Evaluate the module expression. *)
    iApply imp_module; iApply imp_sitems_extend;
      iIntros (found) "Hfound".
    (* Finish evaluating the local module and enrich the scoping environment. *)
    iApply imp_sitems_nil.
    instantiate (1 := (λ δ, ∃ l, ⌜δ = ("Found" ¬> #l)⌝ ∗ l ↦ #())%I).
    by iFrame.

    iIntros (δ) "(%found & -> & Hfound)".
    (* We are done with the effectful part of the program, so we can drop down
       to Horus, the pure program logic. *)
    iApply (impure_pure (B:=void)).
    pose encode_exception := @encode_exception A H found.
    pose xdata_found := @xdata_found A H found.
    eapply pure_eval_match'_exn.
    { (* Subgoal: evaluate the scrutinee [List.iter _ _]. *)
      eapply (pure_EApp τ[val; list A]); last (simpl; unfold tapp).
      { (* Find iter in the environment. *) pure_path. eassumption. }
      2:{ (* find [l] in the environment. *) pure_path. }
      { (* Evaluate the lambda expression we pass to [iter]:
           it is a function with
           - a single argument of type [a]
           - a specification [scan_spec]. *)
          eapply (pure_eval_anon τ[A]) with (P := lambda_spec found l φ); simpl.
          unfold lambda_spec.
          (* Prove that the lambda expression satisfies its spec. *)
          intros x Xs Hpref Hforall.
          apply pure_please_eval.
          eapply pure_eval_ifthen.
          { (* Subgoal: evaluate the conditional [pred x]. *)
            specialize (Hpred exception encode_exception).
            eapply (pure_EApp τ[A]);
              [ pure_path; eassumption | pure_path | simpl; unfold tapp ].
            (* We now connect the specs of [pred] and the lambda.
               They have the same success postcondition, so we only need
               to exploit the fact that [pred] cannot fail. *)
            intros ? <- m Hm; eapply (pure_exn_widen (B1:=exception)), Hm. }
          - (* Case: [pred x] returned true and we learn [φ x]. *)
            intros Hx.
            apply pure_eval_raise.
            (* Evaluate the constructor [Found x]. *)
            eapply (pure_eval_xdata (l:=found)). reflexivity.
            eapply pure_evals_singleton. pure_path.
            intros ? <-.
            (* Prove the failure postcondition of the lambda.
               That is to say, that [φ] holds for some [x ∈ xs]. *)
            split; last auto.
            exists x; split; first reflexivity.
            split; last assumption.
            eapply elem_of_prefix; last eassumption.
            apply elem_of_app; right.
            apply list_elem_of_here.
          - (* Case: [pred x] returned false and we learn [¬ φ x]. *)
            intros Hnφ.
            (* Prove the success postcondition of the lambda.
             That is to say, that [φ] does not hold over the prefix of
             [xs] we have visited so far. *)
            apply Forall_app_2; [ apply Hforall | ].
            apply Forall_singleton. apply Hnφ. }
        (* Use the spec of [iter] *)
        intros ? scan Hscan <- m Hm.
        apply (Hm (λ Xs, Forall (λ x, ¬ φ x) Xs)).
        apply Hscan. by apply Forall_nil. }

    (* We have now finished evaluating the scrutinee of the
       [match .. with ..] expression, we move on to the branches. *)
    - (* Case 1: We returned a value, we don't get caught in the branch *)
      intros () Hforall. pure_match.
      pure_const.
      apply Hforall.

    - (* Case 2: We raised an exception, we get caught by the branch. *)
      simpl. intros ? [(x & -> & Hx) _].
      rewrite (@encode_encode' exception).
      pure_match.
      pure_data.
      by intros ? <-. }

  (* We conclude: update the environment to add [find_elem] to it. *)
  iIntros (find) "#Hfind".
  iApply imp_sitems_nil.
  (* Show that the toplevel module satisfies its spec: it contains a value named
     ["find_elem"] which is specified by [iSpec find find_spec]. *)
  iFrame "#"; simpl. auto.
Qed.

End iris_proof.
