From stdpp Require Import telescopes.
From iris.algebra Require Import excl_auth.

From osiris Require Import osiris.
From osiris.examples Require Import og_inversion.

(* ========================================================================== *)
(** * Iteration Descriptors. *)

Class FinitelyObservable (A : Type) := {
    (* [permitted T Xs] holds if [Xs] is a possible prefix
     of visited elements of the collection [T]. *)
    permitted : list A → Prop;

    (* [complete T Xs] holds if [Xs] is the complete list
     of elements of the collection [T]. *)
    complete  : list A → Prop;
  }.

Section iteration_methods.
  Context `{!osirisGS Σ}.
  Context {A : Type} `{Encode A, FinitelyObservable A}.

  Definition Iter_spec iter : iProp Σ :=
    {{ ∀ Ψ E I;
       {{ ∀ (Xs : list A); ⌜permitted (Xs ++ [X])⌝ ∗ I Xs }}
       f X : A @ E <| Ψ |>
       {{ RET (_ : unit); I (Xs ++ [X]) }} ∗
       I [] }}
    iter f : val @ E <| Ψ |>
    {{ RET (_ : unit); ∃ Xs, I Xs ∗ ⌜complete Xs⌝ }}.

End iteration_methods.


(* ========================================================================== *)
(** * Lazy Sequences. *)

Section lazy_sequences.
  Context `{!osirisGS Σ}.
  Context  {A : Type} `{Encode A, FinitelyObservable A}.

  Inductive seq : Type :=
  | Nil
  | Cons (X : A) (v : val).

  Definition encode_seq (s : seq) : val :=
    match s with
    | Nil => VData "Nil" []
    | Cons X v => VData "Cons" [ #X; v ]
    end.

  Global Instance : Encode seq := { encode' := encode_seq }.

  Global Instance : Constant "Nil" seq :=
    { constant_value := Nil; constant_encode := eq_refl }.

  (* ------------------------------------------------------------------------ *)
  (** Specification of Heads. *)

  (* The predicate [isHead] is defined as [isHead_pre isSeq], where [isSeq] is
     the fixpoint of [isSeq_pre]. *)
  (* A head is either a [Cons] pair or a [Nil] marker. *)
  Definition isHead_pre
    (isSeq :  iEff Σ -d> val -d> list A -d> iPropO Σ)
           :  iEff Σ -d> seq -d> list A -d> iPropO Σ  :=
    λ Ψ h Xs,
      match h with
      | Nil =>
          ⌜ complete Xs ⌝
      | Cons X k =>
                 ⌜ permitted (Xs ++ [X]) ⌝ ∗ ▷ isSeq Ψ k (Xs ++ [X])
      end%I.

  (* ------------------------------------------------------------------------ *)
  (** Specification of Sequences. *)

  (* A sequence is a thunk [k] that, when applied to [#()], produces a head
     [h] s.t. [isHead Ψ1 Ψ2 h Xs]. *)
  Definition isSeq_pre
    (isSeq :  iEff Σ -d> val -d> list A -d> iPropO Σ)
           : (iEff Σ -d> val -d> list A -d> iPropO Σ) :=
    λ Ψ k Xs,
      iSpec τ[unit] k (λ _ m,
          EWP m <| Ψ |> {{ h, isHead_pre isSeq Ψ h Xs }})%I.

  (* [isSeq_pre] is contractive, therefore it admits a fixpoint. *)
  Local Instance isHead_pre_contractive : Contractive isSeq_pre.
  Proof.
    rewrite /isSeq_pre /isHead_pre => n isSeq isSeq' HisSeq Ψ k us.
    Transparent iSpec. unfold iSpec. Opaque iSpec.
  Admitted.
  Definition isSeq_def :
    iEff Σ -d> val -d> list A -d> iPropO Σ :=
    fixpoint (isSeq_pre).
  Definition isSeq_aux : seal isSeq_def. Proof. by eexists. Qed.
  Definition isSeq := isSeq_aux.(unseal).
  Definition isHead := isHead_pre isSeq.
  Definition isSeq_eq : isSeq = isSeq_def := isSeq_aux.(seal_eq).
  Global Lemma isSeq_unfold Ψ k us :
    isSeq Ψ k us ⊣⊢ isSeq_pre isSeq Ψ k us.
  Proof. by rewrite isSeq_eq/isSeq_def;apply(fixpoint_unfold isSeq_pre). Qed.
  Global Lemma isHead_unfold Ψ :
    isHead Ψ = isHead_pre isSeq Ψ.
  Proof. done. Qed.

End lazy_sequences.


(* ========================================================================== *)
(** * Protocol. *)


(* ========================================================================== *)
(** * Verification. *)

Section verification.

  (* ------------------------------------------------------------------------ *)
  (** Ghost Theory. *)

  Section ghost_theory.
    Context {A : Type}.

    (* We use ghost variables with contents in the CMRA [Auth(Ex(List A))]. *)
    Context `{!inG Σ (excl_authR (leibnizO (list A)))}.

    (* The assertion [own γ (●E Ys)] states that the handler
       has seen the elements [Ys]. *)
    Definition handlerView γ Ys : iProp Σ :=
      own γ (●E (Ys : ofe_car (leibnizO (list A)))).
    (* The assertion [own γ (◯E Xs)] states that [iter]
       has seen the elements [Xs]. *)
    Definition iterView γ Xs : iProp Σ :=
      own γ (◯E (Xs : ofe_car (leibnizO (list A)))).

    (* Create a new ghost cell from this CMRA. *)
    (* In the verification of [invert], the ghost variable [γ]
       initially holds the empty list. *)
    Lemma new_cell Zs : ⊢ (|==> ∃ γ, handlerView γ Zs ∗ iterView γ Zs)%I.
    Proof.
      iMod (own_alloc ((●E (Zs : ofe_car (leibnizO (list A)))) ⋅
                       (◯E (Zs : ofe_car (leibnizO (list A)))))) as (γ) "[??]";
      [ apply excl_auth_valid | eauto with iFrame ]; done.
    Qed.

    (* Handler and [iter]'s views are in agreement. *)
    Lemma confront_views γ Ys Xs :
      handlerView γ Ys -∗ iterView γ Xs -∗ ⌜ Xs = Ys ⌝.
    Proof.
      iIntros "Hγ● Hγ◯".
      by iDestruct (own_valid_2 with "Hγ● Hγ◯") as %?%excl_auth_agree_L.
    Qed.

    (* With the ownership of both views, one can update the contents of [γ]. *)
    Lemma update_cell γ Zs Ys Xs :
      handlerView γ Ys -∗ iterView γ Xs ==∗ handlerView γ Zs  ∗ iterView γ Zs.
    Proof.
      iIntros "Hγ● Hγ◯".
      iMod (own_update_2 _ _ _ (●E (Zs : ofe_car (leibnizO (list A))) ⋅
                                ◯E (Zs : ofe_car (leibnizO (list A))))
        with "Hγ● Hγ◯") as "[$$]";
      [ apply excl_auth_update |]; done.
    Qed.

  End ghost_theory.

  (* ========================================================================== *)
  (** * Specification. *)

  (* The specification of [invert] depends on (1) the specification of a
   iteration method [isIter] and (2) the specification of a lazy sequence
   [isSeq], both of which are introduced in the theory [iteration.v]. *)

  Section specification.
    Context `{!osirisGS Σ}.
    Context {A : Type} `{Encode A, FinitelyObservable A}.

    (* ------------------------------------------------------------------------ *)
    (** Specification of [invert]. *)

    Definition env : env := (* stdlib_env *) [].

    Definition invert_spec invert : iProp Σ :=
      {{ Iter_spec iter }}
      invert iter : val
      {{ RET k; isSeq ⊥ k [] }}.

  End specification.

  Inductive effect `{Encode A} : Type :=
  | Yield (a : A).

  Local Instance encode_effect (A : Type) `{Encode A} l : Encode (@effect A _) :=
      { encode' eff := match eff with Yield a => VXData l [ #a ] end }.


  Section invert_correct.
    Context `{!osirisGS Σ}.
    Context  {A : Type} `{Encode A, FinitelyObservable A}.
    Context `{!inG Σ (excl_authR (leibnizO (list A)))}.

    Local Instance data_seq_cons : Data "Cons" τ[A; val] (@seq A) :=
      { ctor_apply := λ '(x, s), Cons x s;
        ctor_encode := λ '(x, s), eq_refl }.

    Section inversion_protocol.

    Context (l : loc).

    Local Instance encode_eff_l : Encode (@effect A _) := encode_effect A l.
    Lemma solve_encode_effect (a : A) :
      VXData l [ #a ] = @encode.encode _ (encode_eff_l) (Yield a).
    Proof. reflexivity. Qed.

    (* This protocol describes the effects performed by [yield]. *)

    Definition ψ_yield (iterView : list A → iProp Σ) : iEff Σ :=
      (>> Xs X >>
         ! #(Yield X)
         {{ iterView Xs ∗ ⌜ permitted (Xs ++ [X]) ⌝ }};
       ? (@O2Ret val exn #())
         {{ iterView (Xs ++ [X]) }}).

    Lemma upcl_yield iterView v Φ :
      (ψ_yield iterView) allows perform v << Φ >> ⊣⊢
      (∃ Xs (X : A), ⌜ v = #(Yield X) ⌝ ∗
                     (iterView Xs ∗
                      ⌜ permitted (Xs ++ [X]) ⌝) ∗
                     (iterView (Xs ++ [X]) -∗ Φ (O2Ret (VUnit))))%I.
    Proof. by rewrite /prot /ψ_yield (upcl_tele' [tele _ _] [tele]) //=. Qed.

    Lemma yield_handler_correct γ (Ys : list A) η :
      lookup_name η "Yield" = Some #l →
      handlerView γ Ys -∗
      (deep_handler_spec ⊤ (ψ_yield (iterView γ)) ⊥
         (λ (_ : unit), ∃ Xs : list A, iterView γ Xs ∗ ⌜complete Xs⌝)
         η __invert_branches1
        ⊥ ⊥ (λ h, isHead ⊥ h Ys)).
    Proof.
      intros Hlookup.
      iLöb as "IH" forall (Ys γ).
      iIntros "HhandlerView".
      iApply prove_deep_handler_spec; iSplit; last iSplit.

      (* Value case: *)
      { iIntros ([]) "(%Xs & HiterView & %Hcomplete)".
        iPoseProof (confront_views with "HhandlerView HiterView") as "->".
        iModIntro.
        imp_branches.
        imp_constant with "[]".
        iPureIntro; apply Hcomplete. }

      (* Exceptional case: *)
      { iIntros (? []). }

      (* Effectful case: *)
      { iIntros (v k) "HProt !>".
        (* Inversion on the [allows perform]. *)
        rewrite upcl_yield.
        iDestruct "HProt" as "(%Xs & %X & -> & [HiterView %Hpermitted] & HProt)".
        iPoseProof (confront_views with "HhandlerView HiterView") as "->".
        (* Update the handler and iterator views. *)
        iApply fupd_imp;
          iMod (update_cell γ (Ys ++ [X]) with "HhandlerView HiterView")
          as "[HhandlerView HiterView]";
          iModIntro.

        imp_branches. (* FIXME: [#k] appears in the environment as [VCont k]. *)

        (* [Seq.Cons (x, fun () -> continue k ())]. *)
        iApply (imp_EData with "[-]"). iApply imp_evals_cons.
        { imp_path. }
        { (* [fun () -> continue k ()] *)
          iApply imp_evals_singleton.
          iApply (imp_EAnon τ[unit]
                    (λ _ m, EWP m {{ k, isHead ⊥ k (Ys ++ [X]) }})%I); simpl.
          iIntros ([]).
          iApply imp_please; iNext.
          (* [fun () -> ...] is a pattern match on the argument,
             it gets desugared to [fun x -> match x with | () -> ...]. *)
          imp_match.

          (* [continue k ()] *)
          iApply (imp_EContinue (B:=unit)); try imp_step.
          iIntros (?[] ->) "_".
          iSpecialize ("IH" with "HhandlerView").
          iApply ("HProt" with "HiterView IH"). }

        iIntros (? f) "(-> & HSpec) /=".
        iFrame "%".
        rewrite isSeq_unfold /isSeq_pre /=.
        iApply "HSpec". }
    Qed.

    End inversion_protocol.

    Definition invert := (EAnonFun __invert).

    Local Instance xdata_yield yl `{Encode A} : @XData yl τ[A] effect (encode_effect A yl) :=
      { xctor_apply := λ a, Yield a;
        xctor_encode := λ a, eq_refl }.

    Lemma ewp_invert η :
      ⊢ EWP (eval η invert) {{ invert_spec }}.
    Proof.
      unfold invert_spec.
      iApply (imp_EAnon_pers τ[val]); simpl.
      iIntros "!>" (iter) "Hiter". iApply imp_please; iNext.

      (* Initialise handler view and iterator view. *)
      iApply fupd_imp.
      iMod (new_cell []) as (γ) "[HhandlerView HiterView]"; iModIntro.

      (* [let open struct ...] *)
      iApply imp_ELetOpen.
      { (* Subgoal: [EWP eval_mexpr η (MStruct []) {{ ... }}]. *)
        iApply imp_module. iApply imp_sitems_extend.
        iIntros (yl) "Hyl". iApply imp_sitems_nil.
        instantiate (1 := (λ δ, ∃ yl, ⌜δ = [_]⌝ ∗ yl ↦ #())%I).
        by iFrame. }
      iIntros (?) "(%yl & -> & Hyl)".

      (* [let yield x = ...] *)
      iApply (imp_ELet_var (λ v,
                {{ ∀ (Xs : list A); ⌜permitted (Xs ++ [X])⌝ ∗ iterView γ Xs }}
                v X : A @ ⊤ <| ψ_yield yl (iterView γ) |>
                {{ RET (_ : unit); iterView γ (Xs ++ [X]) }})%I).
      { iApply (imp_EAnon_pers τ[A]). simpl.
        iIntros "!>" (X Xs) "(Hiter & Hpermitted)".
        iApply imp_please; iNext.
        iApply (imp_EPerform (H0:=encode_effect A yl)).
        { set_postcondition (λ (a : effect), ⌜a = Yield X⌝)%I.
          iApply (imp_EXData (l:=yl)). reflexivity.
          iApply imp_evals_singleton. imp_path.
          iIntros (x) "-> //". }
        iIntros (? ->).
        rewrite upcl_yield.
        iExists _, _.
        iSplit; [ iPureIntro; reflexivity | iFrame ].
        iIntros; iExists tt; iSplit; [ equality | iAssumption ]. }
      iIntros (yield) "#yield_spec".

      iApply (imp_wand with "[-]"); last first.
      { iIntros (k) "H".
        rewrite isSeq_unfold /isSeq_pre.
        iExact "H". }
      iApply (imp_EAnon τ[unit]).
      iIntros ([]).
      iApply imp_please; iNext.
      (* [fun () -> ... ] has been translated as
         [fun x -> match x with | () -> ... ]. *)
      imp_match.
      change (encode' ()) with (#()).
      change (encode' iter) with (#iter).
      simpl.

      (* [match_with iter yield { ...] *)
      iApply (imp_EHandler (A' := unit) with "[Hiter HiterView]").
      { imp_app τ[val] with "[Hiter]".
        { iApply "Hiter". }
        iIntros "Hm".
        iApply ("Hm" with "[$yield_spec $HiterView]"). }

      iApply (yield_handler_correct yl with "HhandlerView").
      reflexivity.
   Qed.

End invert_correct.

End verification.
