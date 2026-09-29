From stdpp Require Import telescopes.
From iris.algebra Require Import excl_auth.

From osiris Require Import osiris.
From osiris.examples Require Import og_localstate.

(* ========================================================================== *)
(** * Protocol. *)

(* LATER: Make the type of state abstract (i.e. Encode .. ) *)
Definition state := Z.

Local Instance : Encode state := { encode' := λ z, VInt (repr z) }.

Section protocols.

  Context (rl wl : loc).

  Definition read : val := VXData rl [].
  Definition write (v : state) : val := VXData wl [ # v].

  Definition READ {Σ} (St : state -> _) : iEff Σ :=
    (>> x  >> ! (read) {{ St x }}; ? (O2Ret (# x)) {{ St x }}).
  Definition WRITE {Σ} St : iEff Σ :=
    (>> x y >> ! (write y) {{ St x }}; ? (O2Ret VUnit) {{ St y }}).
  Definition STATE {Σ} (St : state -> _) : iEff Σ := (READ St <+> WRITE St)%ieff.

  Lemma upcl_state {Σ} St v Φ :
    STATE (Σ:=Σ) St allows perform v << Φ >> ⊣⊢
    (READ St allows perform v << Φ >>) ∨
      (WRITE St allows perform v << Φ >>).
  Proof. by rewrite /STATE; apply upcl_sum. Qed.

  Lemma upcl_read {Σ} St v Φ :
    READ (Σ:=Σ) St allows perform v << Φ >> ⊣⊢
    (∃ x, ⌜ v = read ⌝ ∗ St x ∗ (St x -∗ Φ (O2Ret (# x))))%I.
  Proof. by rewrite /READ /prot (upcl_tele' [tele _] [tele]). Qed.

  Lemma upcl_write {Σ} St v Φ :
    WRITE (Σ:=Σ) St allows perform v << Φ >> ⊣⊢
    (∃ x y, ⌜ v = write y ⌝ ∗ St x ∗ (St y -∗ Φ (O2Ret #())))%I.
  Proof. by rewrite /WRITE /prot (upcl_tele' [tele _ _] [tele]). Qed.

End protocols.

(* ========================================================================== *)
(** * Verification. *)

(* -------------------------------------------------------------------------- *)
(** Ghost Theory. *)

Section ghost_theory.
  Context `{!inG Σ (excl_authR (leibnizO val))}.

  Definition auth_state γ v := own γ (●E (v : ofe_car (leibnizO val))).
  Definition points_to  γ v := own γ (◯E (v : ofe_car (leibnizO val))).

  Lemma ghost_var_alloc v : ⊢ (|==> ∃ γ, auth_state γ v ∗ points_to γ v)%I.
  Proof.
    iMod (own_alloc ((●E (v : ofe_car (leibnizO val))) ⋅
                     (◯E (v : ofe_car (leibnizO val))))) as (γ) "[??]";
    [ apply excl_auth_valid | eauto with iFrame ]; done.
  Qed.
  Lemma ghost_var_agree γ v w : ⊢ (auth_state γ v ∗ points_to γ w) → ⌜ v = w ⌝.
  Proof.
    iIntros "[H● H◯]".
    by iDestruct (own_valid_2 with "H● H◯") as %?%excl_auth_agree_L.
  Qed.
  Lemma ghost_var_update γ w u v :
    auth_state γ u -∗ points_to γ v ==∗ auth_state γ w  ∗ points_to γ w.
  Proof.
    iIntros "Hγ● Hγ◯".
    iMod (own_update_2 _ _ _ (●E (w : ofe_car (leibnizO val)) ⋅
                              ◯E (w : ofe_car (leibnizO val)))
      with "Hγ● Hγ◯") as "[$$]";
    [ apply excl_auth_update | ]; done.
  Qed.

  (* LATER: Can we generalize this so we don't manually write down existentials
     everywhere? *)

End ghost_theory.

(* LATER: Give more control on opacity *)
Opaque auth_state.
Opaque encode.encode.

(* -------------------------------------------------------------------------- *)
(** Specification & Verification. *)

Section verification.
  Context `{!osirisGS Σ} `{!inG Σ (excl_authR (leibnizO val))}.

  Section alloc_effects.

  Context (rl wl : loc).

  Inductive effects : Type :=
  | Read
  | Write (y : Z).

  Local Instance encode_effects : Encode effects :=
    { encode' eff := match eff with
                    | Read => VXData rl []
                    | Write y => VXData wl [ #y ]
                    end }.

  Lemma confront_addresses l1 l2 :
    ∀ v1 v2,
      (l1 ↦ v1) -∗
      (l2 ↦ v2) -∗
      ⌜address l1 ≠ address l2⌝.
  Proof.
    iIntros (v1 v2) "Hl1 Hl2".
    iPoseProof (gen_heap.pointsto_ne with "Hl1 Hl2") as "%Hne".
    iPureIntro. destruct l1, l2. simpl.
    intros ->. by apply Hne.
  Qed.

  Definition main_spec `{Encode A} (spec : A → iProp Σ) main : iProp Σ :=
    {{ ∀ (init : state) rl wl St; St init }}
    main t : unit @ ⊤ <| STATE rl wl St |>
    {{ RET v; spec v }}.

  Definition run_spec run : iProp Σ :=
    {{ ∀ `(Encode A) (spec : A → iProp Σ);
       main_spec spec main }}
    run init main : state val
    {{ RET (v : state * A); spec (snd v) }}.

  Lemma localstate_run_spec :
    ∀ η,
      ⌜ lookup_name η "Get" = Some #rl ⌝ -∗
      ⌜ lookup_name η "Set" = Some #wl ⌝ -∗
      ⌜ address rl ≠ address wl ⌝ -∗
      EWP eval η (EAnonFun __run) {{ run_spec }}.
  Proof.
    cbn zeta.
    iIntros (env HGet HSet Haddr).
    unfold run_spec.

    (* Call the anonymous function. *)
    iApply (imp_EAnon_pers τ[ state; val ]); simpl.
    iIntros "!>" (init main A HencA spec) "Hspec".
    iApply imp_please; iNext.
    iApply fupd_imp.
    iMod (ghost_var_alloc (# init)) as (γ) "[Hstate Hpoints_to]"; iModIntro.

    (* Evaluate allocation of [init] *)
    iApply (imp_ELet_var (λ l, l ↦ #init)%I).

    (* Evaluating the let-bound expression *)
    { (* Allocate a new location with value [init] *)
      imp_ref. }

    (* Continuing with the rest of the computation *)
    iIntros (l) "Hl".

    (* LATER : Hide the [V] constructor for blocks *)

    (* -------------------------------------------------------------------------- *)
    (* 3. At an [EMatch] -- more interesting part of this proof. *)
    iApply (imp_EHandler (A':=A) with "[Hspec Hpoints_to]").

    { (* 3A. Call to [main] in the handled expression *)
      imp_app τ[unit] with "[Hspec]".
      { iApply "Hspec". }
      iIntros "Hmain".
      iSpecialize ("Hmain" $! _ _ _ (λ init, points_to γ #init) with "Hpoints_to").
      iApply "Hmain". }

    generalize (# init) at 3 as init_; intros init_.
    iLöb as "IH" forall (init).
    iApply prove_deep_handler_spec.
    iSplit; last (iSplit; first iIntros (? [])).

    { (* Value case *)
      iIntros (?) "Hspec"; iNext.
      imp_branches.
      iApply (imp_EPair with "[Hl]"); try imp_step.
      iIntros (? ?) "(-> & Hl) ->". iApply "Hspec". }
    (* Finally, we prove the specification over handler. *)

    instantiate (1 := wl). instantiate (1 := rl).
    (* -------------------------------------------------------------------------- *)
    (* Effectful case *)
    iIntros (v k) "Hp".
    iDestruct (upcl_state with "Hp") as "[ H_READ | H_WRITE ]".

    { (* READ case *)
      rewrite upcl_read.
      iDestruct "H_READ" as (x ->) "(Hx & H_READ)".
      iCombine "Hstate Hx" as "H".
      iDestruct (ghost_var_agree with "H") as %->.

      iNext.
      imp_branches.
      - (* EWP Goal: [continue k (!var : t)]. *)
        iDestruct "H" as "(Hauth & Hx)".
        iSpecialize ("H_READ" with "Hx"). simpl.
        iApply (imp_EContinue (B:=state) with "[] [Hl]"); try imp_step.

        iIntros (? ? ->) "[-> Hl]".
        iApply "H_READ". iApply ("IH" with "Hauth Hl"). }

    (* -------------------------------------------------------------------------- *)
    { (* WRITE case *)
      cbn; rewrite upcl_write.
      iDestruct "H_WRITE" as (??->) "(Hx & H_WRITE)".
      iCombine "Hstate Hx" as "H".
      iDestruct (ghost_var_agree with "H") as %Hag.

      iNext.
      imp_branches.
      { (* EWP Goal: [var := y; continue k ()]. *)
        iApply (imp_ESeq with "[Hl]").
        { (* EWP Subgoal: [var := y]. *) imp_store l y. }
        iIntros "Hl".

        (* EWP Subgoal: [continue k ()]. *)
        iDestruct "H" as "(Hauth & Hx)".

        iApply fupd_imp.
        iDestruct (ghost_var_update γ (# y) with "Hauth Hx") as ">(Hauth & Hx)".
        iModIntro.

        iApply (imp_EContinue (B:=unit)); try imp_step.
        iIntros (??) "-> -> !>".
        iApply ("H_WRITE" with "Hx").
        iApply ("IH" with "Hauth Hl"). } }
  Qed.

  End alloc_effects.

  Definition dummy_env := ("Effect", VStruct [("Deep", VStruct [])]) :: (* stdlib_env *) [].

  Instance xdata_write rl wl : @XData wl τ[Z] effects (encode_effects rl wl) :=
    { xctor_apply := λ i, Write i; xctor_encode := λ i, eq_refl }.

  Lemma module_proof (Q : val -> iProp Σ) :
    ⊢ EWP (eval_mexpr dummy_env __main)
      {{ η, ∃ run, ⌜lookup_name η "run" = Some run⌝ ∗ run_spec run }}.
  Proof.
    iApply imp_module.
    iApply (imp_sitems_cons).

    (* [open Effect] *)
    { set_postcondition (λ η, ⌜η = (_, _)⌝)%I.
      iApply (imp_sitem_open).
      { simpl_eval_mexpr.
        set_postcondition (λ δ, ⌜δ = [_]⌝)%I.
        iApply imp_ret; first encode. done. }
      iIntros (? ->) "//". }
    iIntros (? ->).

    (* [open Effect.Deep] *)
    iApply imp_sitems_cons.
    { set_postcondition (λ η, ⌜η = (_, _)⌝)%I.
      iApply (imp_sitem_open).
      { simpl_eval_mexpr.
        set_postcondition (λ δ, ⌜δ = []⌝)%I.
        iApply imp_ret; first encode. done. }
      iIntros (? ->) "//". }
    iIntros (? ->).

    (* [type _ Effect.t += Get : t Effect.t] *)
    iApply imp_sitems_extend.
    iIntros (rl) "Hrl".

    (* [type _ Effect.t += Set : t -> unit Effect.t] *)
    iApply imp_sitems_extend.
    iIntros (wl) "Hwl".

    set enc_eff := encode_effects rl wl.
    set xdata_eff := xdata_write rl wl.

    (* [let get () = perform Get] *)
    iApply (imp_sitems_let (λ v,
              {{ ∀ St x; St x }}
              v u : unit @ ⊤ <| STATE rl wl St |>
              {{ RET X; ⌜X = x⌝ }})%I).
    { iApply (imp_EAnon_pers τ[unit]).
      iIntros "!>" ([] St x) "HSt".
      iApply imp_please. iNext.
      imp_match.
      iApply (imp_EPerform (B:=effects) with "[] [HSt]").
      { set_postcondition (λ e, ⌜e = Read⌝)%I.
        admit. (* iApply (imp_EXData (l:=rl)). *) }
      iIntros (? ->).
      rewrite upcl_state.
      iLeft. rewrite upcl_read. iFrame. iSplit.
      - equality.
      - iIntros "HSt".
        simpl. iExists _; iSplit; equality. }
    iIntros (get) "#Hget".

    (* [let set y = perform (Set y)] *)
    iApply (imp_sitems_let (λ v,
              {{ ∀ St x; St x }}
              v y : Z @ ⊤ <| STATE rl wl St |>
              {{ RET (_ : unit); St y }})%I).
    { iApply (imp_EAnon_pers τ[Z]).
      iIntros "!>" (y St x) "HSt".
      iApply imp_please; iNext.
      iApply (imp_EPerform (λ eff, ⌜eff = Write y⌝)%I).
      { iApply (imp_EXData (l:=wl)). reflexivity.
        iApply imp_evals_singleton. imp_path.
        iIntros (?) "-> //". }
      iIntros (? ->).
      rewrite upcl_state upcl_write.
      iRight. iExists x, y. iFrame. iSplit.
      - iPureIntro. encode.
      - iIntros "$". iExists _; auto. }
    iIntros (fset) "#Hset".

    (* [let run (type a) init maint : t * a =] *)
    iPoseProof (confront_addresses with "Hrl Hwl") as "%Haddr".
    iApply (imp_sitems_let run_spec).
    { iApply (localstate_run_spec with "[] [] []"); iPureIntro.
      reflexivity.
      reflexivity.
      apply Haddr. }

    iIntros (run) "#Hrun".
    iApply imp_sitems_nil; simpl.
    iExists _; iFrame "#". equality.
  Admitted.

End verification.
