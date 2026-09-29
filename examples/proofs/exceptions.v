(** This file contains both a "pure" and "effectful" proof of exceptions.v, to guide the
   generalization of lemmas about [pure] to non-trivial exceptional postconditions.  *)

From osiris Require Import osiris.
From osiris.examples Require Import og_exception.

Definition stdlib_with_notfound :=
  ("Not_found", (VFieldLoc (Loc 0))) :: [].

Inductive exception :=
| Not_found.

Instance encode_exception : Encode exception :=
  { encode' := λ _, VXData (Loc 0) [] }.

Section proof_pure.

  Variable A : Type.
  Hypothesis HA : Encode A.

  (* Calling [head #l] either returns [#h] when [l = h :: t],
     or throws an exception when [l = []]. *)

  Definition head_spec (l : list A) m :=
    pure m
      (λ h : A, exists t, l = h :: t)
      (λ e, e = VXData (Loc 0) [] ∧ l = []).

  (* Calling [catch_head #l] either returns [Some #h] when [l = h ::t],
     or returns [None] when [l = []]. *)

  Definition catch_head_spec (l : list A) (m : microvx) :=
    pure m (λ hopt, hopt = list.head l) (⊥ : exn → Prop).

  Lemma let_fun τ P η δ x e f sitems φ :
    predicate_over_function_body τ P η (EAnonFun (Anon (x => e))) ->
    (∀ c, Spec τ c P -> struct_items ((f, c) :: η, (f, c) :: δ) sitems φ) ->
    struct_items (η, δ) ((ILet [Binding (PVar f) (EAnonFun (AnonFun x e))]) :: sitems) φ.
  Proof.
    intros Hpred Hmono.
    eapply structs_cons.
    { apply struct_let_single.
      apply pure_eval_anon. apply Hpred. }
    intros [η' δ'] (clo & HSpec & -> & ->).
    apply Hmono, HSpec.
  Qed.

  Lemma example :
    eval_module stdlib_with_notfound __main (λ η, True).
  Proof.
    unfold __main.
    apply module_struct.

    (* Struct item: [let head l = ...] *)
    apply (let_fun τ[list A] head_spec).
    { simpl.
      unfold head_spec; intros l.
      apply pure_please_eval.
      eapply pure_eval_match. { pure_path. }
      pure_match.
      - eapply pure_eval_raise.
        eapply (pure_eval_xconstant (Loc 0) (VXData (Loc 0) [])). simpl. reflexivity.
        pure_path.
        split; reflexivity.
      - pure_path. eauto. }
    intros head Hhead.

    (* Struct item: [let catch_head l = ...] *)
    apply (let_fun τ[list A] catch_head_spec).
    { simpl.
      unfold catch_head_spec; intros l.
      change encode_list with (@encode.encode (list A) _).
      apply pure_please_eval.
      eapply pure_eval_match'_exn.
      - eapply (pure_EApp τ[list A]).
        { pure_path. eassumption. }
        { pure_path. }
        simpl.
        intros l' <- m Hm. apply Hm.
      - intros h (t & ->). pure_match.
        eapply pure_eval_data.
        eapply pure_evals_singleton. pure_path.
        intros xs <-; auto.
      - intros e (-> & ->). pure_match.
        pure_const. reflexivity. }
    intros catch_head Hcatch_head.

    (* Struct item: [let catch_head2 l = ...] *)
    apply (let_fun τ[list A] catch_head_spec).
    { simpl.
      unfold catch_head_spec; intros l.
      apply pure_please_eval.
      eapply pure_eval_match'_exn.
      { instantiate (5:=λ o, ∃ h t, l = h :: t ∧ o = Some h).
        pure_data.
        { eapply (pure_EApp τ[list A]).
          { pure_path. eassumption. }
          { pure_path. }
          simpl.
          intros ? <- m Hm. apply Hm. }
        intros h (t & ->). exists h, t. eauto. }
      - intros o (a & t & -> & ->).
        pure_match. pure_path.
      - intros e (-> & ->).
        pure_match. pure_const. reflexivity. }

    intros catch_head2 Hcatch_head2.

    (* We have gone though all of the struct items, time to conclude. *)
    finished_struct.
    done.
  Qed.

End proof_pure.
