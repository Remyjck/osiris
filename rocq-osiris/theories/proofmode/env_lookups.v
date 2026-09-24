From iris.proofmode Require Import proofmode.

From osiris.lang Require Import encode type_nel constructors.
From osiris.semantics Require Import eval.
From osiris.program_logic Require Import program_logic.

From osiris.utils Require Import tactics.
Require Import equality.

(* This file defines the [imp_path] tactic, used for solving goals of the
   form [EWP (eval η (EPath p)) {{ Φ }}]. *)

(* --------------------------------------------------------------------------*)
(* Specifications for whole modules. *)

Section ModuleSpecs.
  Context `{!osirisGS Σ}.

  (* Specification over a path:
     [path_spec p Φ η] states that in environment [η],
     [p] resolves to some value [#x], and that [Φ x] holds. *)
  Definition path_spec `{Encode A} (p : path) (Φ : A → iProp Σ) (η : env) : iProp Σ :=
    ∃ x, ⌜lookup_path η p = Some #x⌝ ∗ Φ x.

  (* Specification over a name - aka a singleton path. *)
  Definition in_env `{Encode A} (name : var) (Φ : A → iProp Σ) (η : env) : iProp Σ :=
    ∃ x, ⌜lookup_name η name = Some #x⌝ ∗ Φ x.

  (* A pure variant of [in_env], in Prop. *)
  Definition pure_in_env `{Encode A} (name : var) (Φ : A → Prop) (η : env) : Prop :=
    ∃ x, lookup_name η name = Some #x ∧ Φ x.

  (* We use [enc_spec] to represent postconditions ([enc_spec.spec])
     over arbitary encodable types ([enc_spec.res_type]). *)
  Record enc_spec {PROP : Type} :=
    is_spec
      {
        res_type : Type;
        res_type_enc : Encode res_type;
        spec : res_type → PROP;
      }.
  (* Make it so [enc_spec] displays as [has_spec name Φ]. *)
  Global Arguments enc_spec {_}.
  Global Arguments res_type {_}.
  Global Arguments res_type_enc {_}.
  Global Arguments spec {_}.
  Global Arguments is_spec {_ _ _}.
  Global Add Printing Constructor enc_spec.

  Instance dom_env : Dom (env) (gset var) := λ η, list_to_set (η.*1).

  (* [context (zip xs Φs) d η] is a specification over an environment [η].

     It states that every name in [xs] is bound to some value in [η],
     and this variable persistently satisfies the corresponding
     postcondition in [Φs].

     Additionally, [context] states [η]'s domain is [d]. *)

  Definition context (specs : list (var * @enc_spec (iProp Σ))) d : env → iProp Σ :=
    λ η, (⌜dom η = d⌝ ∗
           [∗ list] '(x, s) ∈ specs,
            @in_env s.(res_type) s.(res_type_enc) x (λ res, □ s.(spec) res) η)%I.

  (* Because all of the specifications in [context] hold persistently,
     [context] is persistent. *)
  Global Instance context_pers specs d η : Persistent (context specs d η).
  Proof. apply _. Qed.

  (* A rephrasing of [context] in a pure context. *)
  Definition pure_context (specs : list (name * @enc_spec Prop)) d : env → Prop :=
    λ η, dom η = d ∧
         Forall (λ '(x, s),
                   @pure_in_env s.(res_type) s.(res_type_enc) x s.(spec) η) specs.

  (* [var_spec] acts as a smart constructor for a pair of a variable
     and its specification. *)
  Definition var_spec {PROP} `{Encode A} (x : var) (Φ : A → PROP) : var * (@enc_spec PROP) :=
    (x, is_spec Φ).

  (* Check *)
  (*   context [ *)
  (*      var_spec "+" (λ add, iSpec τ[Z; Z] add (λ i j m, EWP m {{ n, ⌜(n = i + j)%Z⌝ }})%I); *)
  (*      var_spec "-" (λ sub, iSpec τ[Z; Z] sub (λ i j m, EWP m {{ n, ⌜(n = i - j)%Z⌝ }})%I) *)
  (*    ] {["+";"-";"*"]}. *)

End ModuleSpecs.

(* --------------------------------------------------------------------------*)
(* Lemmas for resolving names. *)

Section LookupName.

  Lemma lookup_name_nil name :
    lookup_name [] name = None.
  Proof. reflexivity. Qed.

  Lemma lookup_name_app_l name xs ys a :
    lookup_name xs name = Some a →
    lookup_name (xs ++ ys) name = Some a.
  Proof.
    induction xs as [|[x v] xs IH].
    - rewrite lookup_name_nil. discriminate 1.
    - simpl.
      destruct (name =? x)%string.
      + inversion 1; by subst.
      + apply IH.
  Qed.

  Lemma lookup_name_app_r name xs ys :
    lookup_name xs name = None →
    lookup_name (xs ++ ys) name = lookup_name ys name.
  Proof.
    induction xs as [|[x v] xs IH].
    - auto.
    - simpl.
      destruct (name =? x)%string.
      + discriminate 1.
      + apply IH.
  Qed.

  Lemma not_elem_of_dom_lookup_name (η : env) name :
    name ∉ (list_to_set (η.*1) : gset var) → lookup_name η name = None.
  Proof.
    induction η as [|[y v] η IH]; simpl; first done.
    intros Hnin.
    simpl in Hnin.
    apply not_elem_of_union in Hnin as [Hne Hnin].
    apply not_elem_of_singleton in Hne.
    destruct (name =? y)%string eqn:Heq; last by apply IH.
    exfalso. apply Hne. by apply String.eqb_eq in Heq.
  Qed.

  Lemma lookup_path_cons π (η : env) y w :
    (match π with [] => True | x :: _ => (x =? y)%string = false end) →
    lookup_path ((y, w) :: η) π = lookup_path η π.
  Proof.
    destruct π as [|x π]; simpl; first done.
    intros Hne.
    destruct π as [|z π]; simpl; rewrite Hne; reflexivity.
  Qed.

  Lemma lookup_path_app_r π (η δ : env) :
    (match π with [] => True | x :: _ => lookup_name δ x = None end) →
    lookup_path (δ ++ η) π = lookup_path η π.
  Proof.
    destruct π as [|x π]; simpl; first done.
    intros Hδ.
    destruct π as [|y π]; simpl; rewrite (lookup_name_app_r x δ η Hδ); reflexivity.
  Qed.

End LookupName.

(* --------------------------------------------------------------------------*)
(* Lemmas for reasoning about [in_env]. *)

Section InEnv.
  Context `{!osirisGS Σ}.
  Context `{Encode A} {Φ : A → iProp Σ}.

  Lemma in_env_mono (Φ' : A → iProp Σ) x η :
    in_env x Φ' η -∗
    (∀ a, Φ' a -∗ Φ a) -∗
    in_env x Φ η.
  Proof.
    iIntros "(%a & % & HΦ') Hmono".
    iExists a. iSplit; [ iPureIntro; assumption | ].
    iApply ("Hmono" with "HΦ'").
  Qed.

  (* [in_env] when the name [x] is found in the first of two
     environment fragments. See the [Context] section for
     [in_env_app_r]. *)

  Lemma in_env_app_l x δ η :
    in_env x Φ δ -∗
    in_env x Φ (δ ++ η).
  Proof.
    iIntros "(% & % & $)".
    iPureIntro.
    by apply lookup_name_app_l.
  Qed.

  (* The interaction of [in_env] and cons. *)

  (* If the head does not match the name we are looking for,
     we continue looking in the tail of the environment. *)

  Lemma in_env_cons {η v} x y :
    (x =? y)%string = false →
    in_env x Φ η -∗
    in_env x Φ ((y, v) :: η).
  Proof.
    iIntros (Hneq) "(%a & %Hlookup & $)".
    iPureIntro.
    simpl lookup_name; rewrite Hneq; apply Hlookup.
  Qed.

  (* If the head matches the name we are looking for,
     we have to prove the postcondition over the value we have found. *)

  Lemma in_env_here {η v} x y :
    (x =? y)%string = true →
    Φ v -∗
    in_env x Φ ((y, #v) :: η).
  Proof.
    iIntros (Heq) "$".
    iPureIntro.
    simpl lookup_name; rewrite Heq. reflexivity.
  Qed.

  Lemma in_env_here_inline {η} (c : data) (r : record) (mk : record → A) x y :
    (x =? y)%string = true →
    (∀ r' : record, VInline c r' = #(mk r')) →
    Φ (mk r) -∗
    in_env x Φ ((y, VInline c r) :: η).
  Proof.
    iIntros (Heq Hmk) "HΦ".
    rewrite Hmk.
    by iApply in_env_here.
  Qed.

End InEnv.

(* --------------------------------------------------------------------------*)
(* Lemmas for reasoning about [path_spec]. *)

Section PathSpec.
  Context `{!osirisGS Σ}.
  Context `{Encode A} {Φ : A → iProp Σ}.

  (* When the path is a singleton, proving [path_spec [x] Φ η] is
     equivalent to proving [in_env x Φ η]. *)

  Lemma path_spec_singleton x η :
    in_env x Φ η -∗ path_spec [x] Φ η.
  Proof.
    unfold in_env.
    iIntros "(%v & Hlookup & HΦ)".
    iExists v. simpl. iFrame.
  Qed.

  (* When the path is a cons, we know that the head of the path must
     resolve to a module in the environment.

     We will then have to resolve the tail of the path within
     that module. *)

  Lemma path_spec_cons {η x p} (mspec : env → iProp Σ) :
    in_env x mspec η -∗
    (∀ (δ : env), mspec δ -∗ path_spec p Φ δ) -∗
    path_spec (x :: p) Φ η.
  Proof.
    iIntros "(%δ & %Hlookup & Hpost) Hcov".
    iDestruct ("Hcov" with "Hpost") as "(% & %Hlookup' & HΦ)".
    iFrame. iPureIntro.
    simpl. destruct p.
    - simpl in Hlookup'. discriminate Hlookup'.
    - rewrite Hlookup. apply Hlookup'.
  Qed.

  Lemma path_spec_mono (Φ' : A → iProp Σ) p η :
    path_spec p Φ' η -∗
    (∀ a, Φ' a -∗ Φ a) -∗
    path_spec p Φ η.
  Proof.
    iIntros "(%a & %Hlookup & HΦ') Hmono".
    iExists a. iSplit; first done.
    iApply ("Hmono" with "HΦ'").
  Qed.

  Lemma path_spec_cons_env p η y w :
    (match p with [] => True | x :: _ => (x =? y)%string = false end) →
    path_spec p Φ η -∗
    path_spec p Φ ((y, w) :: η).
  Proof.
    iIntros (Hne) "(%v & %Hlookup & HΦ)".
    iExists v. iSplit; last done.
    iPureIntro. by rewrite (lookup_path_cons p η y w Hne).
  Qed.

  Lemma path_spec_app_r p η δ d mspec :
    (match p with [] => True | x :: _ => x ∉ d end) →
    context mspec d δ -∗
    path_spec p Φ η -∗
    path_spec p Φ (δ ++ η).
  Proof.
    iIntros (Hnin) "(%Hdom & _) (%v & %Hlookup & HΦ)".
    iExists v. iSplit; last done.
    iPureIntro.
    rewrite (lookup_path_app_r p η δ); [done|].
    destruct p as [|x p]; first done.
    apply not_elem_of_dom_lookup_name.
    unfold dom, dom_env in Hdom. rewrite Hdom. exact Hnin.
  Qed.

End PathSpec.


(* --------------------------------------------------------------------------*)
(* Lemmas for exploiting [context] hypotheses to prove [in_env]. *)

Section Context.
  Context `{!osirisGS Σ}.
  Context `{Encode A}.

  (* If the pair [(x, Φ)] appears in a [context _ _ η] hypothesis,
     then we know [in_env x Φ η]. *)

  Lemma extract_context {Φ : A → iProp Σ} {η} xs ys d x :
    context (xs ++ var_spec x Φ :: ys) d η -∗ in_env x Φ η.
  Proof.
    unfold context.
    iIntros "(%Hdom & Hspecs)".
    iPoseProof (big_sepL_lookup _ _ (length xs) with "Hspecs") as "HΦ".
    { by apply list_lookup_middle. }
    unfold var_spec.
    iApply (in_env_mono with "HΦ").
    iIntros (res) "#$".
  Qed.

  (* When the name is in the second of two environment fragments
     [η] and [δ], we can exploit a [context] hypothesis over the first
     fragment [η] to prove that the name does not appear in [η].

     We then continue looking in the second fragment. *)

  Lemma in_env_app_r {Φ : A → iProp Σ} {η x} δ d mspec :
    x ∉ d →
    context mspec d δ -∗
    in_env x Φ η -∗
    in_env x Φ (δ ++ η).
  Proof.
    iIntros (Hnin) "(%Hdom & _) Hη".
    iInduction δ as [| [y v] δ ] "IH" forall (d Hnin Hdom).
    - iApply "Hη".
    - simpl. iApply in_env_cons.
      + unfold dom, dom_env in Hdom.
        rewrite <- Hdom in Hnin; simpl in Hnin.
        apply not_elem_of_union in Hnin as [Hnin _].
        apply not_elem_of_singleton in Hnin.
        by apply String.eqb_neq.
      + iApply ("IH" $! (dom δ) with "[] [//] Hη").
        iPureIntro.
        unfold dom, dom_env in Hdom.
        rewrite <- Hdom in Hnin; simpl in Hnin.
        apply not_elem_of_union in Hnin as [_ Hnin].
        apply Hnin.
  Qed.

  (* Proving [in_env x Φ η] when we know [context mspec d η]. *)

  (* We can either directly find the specification [Φ], or find
     another specification [Φ'], in which case we use the monotonicity
     over [in_env]. *)

  Lemma in_env_context {Φ : A → iProp Σ} {x} η d (mspec : list (var * enc_spec)) :
    var_spec x Φ ∈ mspec →
    context mspec d η -∗
    in_env x Φ η.
  Proof.
    iIntros (Hin) "Hcontext".
    apply list_elem_of_split in Hin as (l1 & l2 & ->).
    iPoseProof (extract_context with "Hcontext") as "$".
  Qed.

  Lemma in_env_context_mono {Φ : A → iProp Σ} Φ' {x} δ d mspec :
    var_spec x Φ' ∈ mspec →
    context mspec d δ -∗
    (∀ a, Φ' a -∗ Φ a) -∗
    in_env x Φ δ.
  Proof.
    iIntros (Hin) "Hcontext Hmono".
    apply list_elem_of_split in Hin as (l1 & l2 & ->).
    iPoseProof (extract_context with "Hcontext") as "Hspec".
    iApply (in_env_mono with "Hspec Hmono").
  Qed.

  Lemma in_env_lookup `{Encode A} {x} (a : A) η :
    lookup_name η x = Some #a →
    ⊢ @in_env Σ _ _ x (λ a', ⌜a' = a⌝)%I η.
  Proof. iIntros (Hlookup). by iExists a. Qed.

End Context.

Section PathRule.
  Context `{!osirisGS Σ}.

  (* Using [path_spec] defined above, we prove a new reasoning rule
     for paths lookups in the environment.

     The end-user should never see [path_spec], and we should trive
     to automatically discharge that proof obligation in all cases. *)

  Lemma imp_EPath_spec {E : coPset} {Ψ : iEff Σ} {A : Type} {EncA : Encode A}
    {Φ : A → iProp Σ} {ζ : exn → iProp Σ} (η : env) (p : path) :
    path_spec p Φ η -∗
    EWP eval η (EPath p) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} : iProp Σ.
  Proof.
    iIntros "(% & %Hlookup & Hspec)".
    simpl_eval.
    iApply imp_of_option.
    rewrite Hlookup.
    iExists x; auto.
  Qed.

End PathRule.

(* --------------------------------------------------------------------------*)
(* --------------------------------------------------------------------------*)
(* Implementing the [imp_path] tactic. *)

From Ltac2 Require Import Ltac2 Printf Bool.

(** Fetching hypotheses in the iris context. *)

(* [is_arg_of arg t] checks if [t] is an application, and if it is,
   checks whether [arg] is an argument of that application.

   We use it to check whether a hypothesis mentions a given term. *)

Ltac2 is_arg_of (arg : constr) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App _ tail =>
      Array.mem Constr.equal arg tail
  | _ => false
  end.

(* [get_env_spec η] takes an environment fragment [η] and tries to
   find a hypothesis of the form [context _ _ η] in the iris context.

   If found, it returns the name (a Gallina term of type [base.ident])
   of that hypothesis. *)

Ltac2 get_context_spec (η : constr) : constr :=
  let (pers_hyps, spat_hyps) := get_iris_hyps () in
  let rec go env :=
    lazy_match! env with
    | environments.Enil =>
        Control.zero (Tactic_failure
                        (Some (fprintf "Could not find [context] specification for environment %t" η)))
    | environments.Esnoc ?env ?name ?prop =>
        match! prop with
        | env_lookups.context _ _ ?δ =>
            if Constr.equal η δ then
              name
            else
              go env
        | _ =>
            (* If we [η] appears as an argument of the hypothesis
               (this occurs when the module specification is behind a definition). *)
            if is_arg_of η prop then
              (* We try to unify the hypothesis with [context _ _ η],
                 if successfull, we return the hypothesis' name *)
              Control.plus
                (fun _ =>
                   Std.unify prop open_constr:(env_lookups.context _ _ $η);
                   name)
                (fun _ => go env)
            else go env
        end
    end
  in
  Control.plus
    (fun _ => go pers_hyps)
    (fun _ => go spat_hyps).


(* [get_in_env x η] takes a name [x] and an environment fragment [η]
   and tries to find a hypothesis fo the form [in_env x _ η] in the
   iris context. *)

Ltac2 get_in_env (x : constr) (η : constr) : constr :=
  let (pers_hyps, spat_hyps) := get_iris_hyps () in
  let rec go env :=
    lazy_match! env with
    | environments.Enil =>
        Control.zero (Tactic_failure
                        (Some (fprintf "Could not find [in_env] specification for name %t" x)))
    | environments.Esnoc ?env ?name ?prop =>
        match! prop with
        | in_env ?y _ ?δ =>
            if Constr.equal x y && Constr.equal η δ then
              name
            else
              go env
        | _ => go env
        end
    end
  in
  Control.plus
    (fun _ => go pers_hyps)
    (fun _ => go spat_hyps).

(* [is_env_spec δ prop] checks whether [prop] is a specification of the
   environment [δ] itself, i.e. whether it has one of the three shapes
   an environment is ever specified by. The check is up to conversion,
   so that a module specification hidden behind a definition is
   recognised too (as in [get_context_spec]). *)

Ltac2 is_env_spec (δ : constr) (prop : constr) : bool :=
  Control.plus
    (fun _ =>
       first [ Std.unify prop open_constr:(in_env _ _ $δ)
             | Std.unify prop open_constr:(env_lookups.context _ _ $δ)
             | Std.unify prop open_constr:(path_spec _ _ $δ) ];
       true)
    (fun _ => false).

(* [get_env_spec δ] returns the name of an intuitionistic hypothesis
   specifying the environment [δ], as judged by [is_env_spec].

   Only the intuitionistic hypotheses are searched: a module
   specification is persistent, and it is used twice when resolving a
   path through that module (once for the head, once for the tail). *)

Ltac2 get_env_spec (δ : constr) : constr :=
  let (pers_hyps, _) := get_iris_hyps () in
  let rec go env :=
    lazy_match! env with
    | environments.Enil =>
        Control.zero (Tactic_failure
                        (Some (fprintf "Could not find a specification for the environment %t" δ)))
    | environments.Esnoc ?env ?name ?prop =>
        if is_env_spec δ prop then name else go env
    end
  in
  go pers_hyps.

(* [solve_env_spec_evar ()] instantiates a goal of the form [?spec δ],
   where [?spec] is still an evar.

   This is what [in_env_here] leaves behind when the name being resolved
   is bound to a module's environment: [path_spec_cons] introduces the
   module's specification as an evar, to be discovered while resolving
   the head of the path. Nothing downstream can make progress until it
   is instantiated, so we read it off the context. [iExact] then
   abstracts [δ] out of the hypothesis, which is what gives [?spec] the
   pointwise form the rest of the path needs.

   A postcondition evar over an ordinary value is left alone: no
   hypothesis has the shape [is_env_spec] looks for, and such an evar is
   meant to stay, for [solve_eq_goal] or [iFrame] to instantiate. Same
   for a concrete specification left for the caller to discharge. *)

Ltac2 solve_env_spec_evar () :=
  lazy_match! get_iris_goal () with
  | ?spec ?δ =>
      if Constr.is_evar spec then
        Control.plus
          (fun _ => let hyp := get_env_spec δ in iExact $hyp)
          (fun _ => ())
      else ()
  | _ => ()
  end.

(* [get_path_spec p η] tries to find a hypothesis of the form
   [path_spec p' _ η] in the iris context, for a path [p'] equal to [p]
   (and the same environment [η]). This lets [solve_path_spec] reuse an
   already-available [path_spec] hypothesis directly when the caller
   kept it folded (e.g. [path_spec ["G";"fresh"] Φ η] introduced via a
   plain [iIntros "#HG"], not destructured into the per-segment
   [in_env]/[context] facts the rest of [imp_path] otherwise looks
   for). *)

Ltac2 get_path_spec (p : constr) (η : constr) : constr :=
  let (pers_hyps, spat_hyps) := get_iris_hyps () in
  let rec go env :=
    lazy_match! env with
    | environments.Enil =>
        Control.zero (Tactic_failure
                        (Some (fprintf "Could not find [path_spec] hypothesis for path %t" p)))
    | environments.Esnoc ?env ?name ?prop =>
        match! prop with
        | path_spec ?p' _ ?δ =>
            if Constr.equal p p' && Constr.equal η δ then
              name
            else
              go env
        | _ => go env
        end
    end
  in
  Control.plus
    (fun _ => go pers_hyps)
    (fun _ => go spat_hyps).


(** Applying lemmas that reason about [in_env]. *)

(* These lemmas often come with side-conditions.
   The tactics fails if those side conditions cannot be solved. *)

Ltac2 in_env_cons () :=
  iApply in_env_cons;
  (* For this tactic to succeed, it must solve the [x =? y = false]
     condiction of the [in_env_cons] lemma. *)
  Control.focus 1 1 (fun _ => reflexivity).

Ltac2 in_env_here () :=
  iApply in_env_here;
  (* For this tactic to succeed, it must solve the [x =? y = true]
     condition of [in_env_here]. *)
  Control.focus 1 1 (fun _ => apply String.eqb_refl).

Ltac2 in_env_here_inline_tac () :=
  iApply in_env_here_inline;
  Control.focus 1 1 (fun _ => apply String.eqb_refl);
  Control.focus 1 1 (fun _ => apply inline_encode).

Ltac2 in_env_app_l () :=
  iApply in_env_app_l.

Ltac2 in_env_app_r (hyp : constr) :=
  iApply (in_env_app_r with $hyp);
  (* For this tactic to succeed, it must solve the [x ∉ d] condition
     of [in_env_app_r]. *)
  Control.focus 1 1 (fun _ => complete (fun _ => ltac1:(set_solver))).

Ltac2 in_env_context hyp :=
  Control.plus
    (fun _ =>
       iApply (in_env_context with $hyp);
       (* For this branch of the tactic to succeed, it must solve the
          [var_spec x Φ ∈ mspec] condition of [in_env_context] *)
       complete (fun _ => repeat constructor))
    (* If the previous branch of the tactic failed,
       try again with the monotonic variant of the lemma. *)
    (fun _ =>
       iApply (in_env_context_mono with $hyp) >
         (* Note that the first condition must still succeed, but we
            are allowed to fail to discharge the monotonicity
            condition, which then becomes a proof obligation for the
            user. *)
         [  complete (fun _ => repeat constructor) | auto ]).


(** Solving environment lookup goals. *)

(* [solve_in_env ()] solves a goal of the form [in_env x Φ η]. *)

(*
   It works by matching on the shape of [η]:

   - cons: apply either [in_env_here] or [in_env_cons].
   - app: apply either [in_env_app_r] or [in_env_app_l].
   - otherwise: try and find a hypothesis on [η] in the context.

   When the head of the cons *is* the name we are after,
   [in_env_here_inline] could also apply. It is deliberately not offered
   here as an extra alternative: making it reachable by backtracking
   perturbs an earlier, unrelated bracket of the same [imp_app]. *)

Ltac2 rec solve_in_env () :=
  lazy_match! get_iris_goal () with
  | in_env ?name _ ?env =>
      (* We use [match!] instead of [lazy_match!] so that we always
         fall back to the last branch in case we have a hypothesis
         over an environment which is an app or a cons. *)
      match! env with
      | (?name', ?_val) :: _ =>
          if Constr.equal name name' then
            (in_env_here ();
             (* [in_env_here] leaves the specification of the value found,
                which may still be an evar. *)
             Control.enter solve_env_spec_evar)
          else
            (in_env_cons ();
             Control.enter solve_in_env)
      | ?δ ++ _ =>
          Control.plus
            (fun _ =>
               let spec_name := get_context_spec δ in
               in_env_app_r spec_name;
               Control.enter solve_in_env)
            (fun _ =>
               in_env_app_l ();
               solve_in_env ())
      | ?η =>
          Control.plus
            (* Try to find a corresponding [in_env] hypothesis. *)
            (fun _ =>
               let spec_name := get_in_env name η in
               iApply (in_env_mono with $spec_name);
               let ha := iFresh "ha" in
               iIntros ("% " ++ $ha)%string; try (iApply $ha))
            (fun _ =>
               Control.plus
                 (* Try to find a corresponding [context] hypothesis. *)
                 (fun _ =>
                    let spec_name := get_context_spec η in
                    in_env_context spec_name)
                 (fun _ =>
                    Control.plus
                      (* Try to find a [lookup_name] hypothesis.  We use
                         [match!] rather than [lazy_match!] so that, when
                         several [lookup_name] hypotheses are in context
                         (e.g. one per element of a tuple), we backtrack
                         through them until we find the one matching [name]
                         and [η]. *)
                      (fun _ =>
                         match! goal with
                         | [ h : lookup_name ?δ ?name' = Some #_ |- _ ] =>
                             if (Constr.equal δ η) && Constr.equal name' name then
                               let h := Control.hyp h in
                               let specialized_lemma := open_constr:(in_env_lookup _ _ $h) in
                               iApply $specialized_lemma
                             else
                               Control.zero (Tactic_failure None)
                         end)
                      (fun _ =>
                         Control.zero (Tactic_failure
                                         (Some (fprintf "Could not solve goal [in_env %t _ %t]" name env))))))
      end
  | _ => Control.zero (Tactic_failure (Some (fprintf "Expected goal to be [in_env]")))
  end.

(* [path_spec_to_in_env] takes a goal of the form [path_spec p Φ η]
   and reduces it to a goal of the form [in_env _ _ η] by applying
   either [path_spec_singleton] or [path_spec_cons]. *)

(* We use the [detected_path] type as a return type for
   [path_spec_to_in_env] to indicate which choice was made. *)

Ltac2 Type detected_path :=
  [ | Psingleton
    | Pcons ].

Ltac2 rec path_spec_to_in_env () : detected_path :=
  lazy_match! get_iris_goal () with
  | path_spec ?path ?_spec ?_env =>
      match! path with
      | [ _ ] =>
          iApply path_spec_singleton;
          Psingleton
      | _ =>
          iApply path_spec_cons;
          Pcons
      end
  | _ => Control.zero (Tactic_failure (Some (fprintf "Expected goal to be [path_spec]")))
  end.

(* [try_reuse_path_spec] solves a goal [path_spec p Φ env] by reusing an
   available [path_spec p _ env'] hypothesis directly, for an [env'] equal
   to [env] up to bindings prepended after the hypothesis was obtained
   (a function argument bound via [iIntros "!>" (v)], say, or a [context]
   fragment appended by module-opening).

   It walks down [env]'s cons/app structure like [solve_in_env] does for
   [in_env] goals, via [path_spec_cons_env]/[path_spec_app_r], stopping as
   soon as [get_path_spec] finds a hypothesis for the path and the
   environment reached so far. *)

Ltac2 rec try_reuse_path_spec () :=
  lazy_match! get_iris_goal () with
  | path_spec ?p ?_spec ?goal_env =>
      match! goal_env with
      | (?_y, ?_w) :: ?_rest =>
          Control.plus
            (fun _ =>
               iApply path_spec_cons_env;
               Control.focus 1 1 (fun _ => complete (fun _ => reflexivity));
               try_reuse_path_spec ())
            (fun _ =>
               let hyp_name := get_path_spec p goal_env in
               iApply (path_spec_mono with $hyp_name);
               iIntros "% #Hspec"; iApply "Hspec")
      | ?δ ++ ?_rest =>
          Control.plus
            (fun _ =>
               let spec_name := get_context_spec δ in
               iApply (path_spec_app_r with $spec_name);
               Control.focus 1 1 (fun _ => complete (fun _ => ltac1:(set_solver)));
               try_reuse_path_spec ())
            (fun _ =>
               let hyp_name := get_path_spec p goal_env in
               iApply (path_spec_mono with $hyp_name);
               iIntros "% #Hspec"; iApply "Hspec")
      | ?base_env =>
          let hyp_name := get_path_spec p base_env in
          iApply (path_spec_mono with $hyp_name);
          iIntros "% #Hspec"; iApply "Hspec"
      end
  | _ => Control.zero (Tactic_failure None)
  end.

(* [solve_path_spec] solves a goal of the form [path_spec p Φ η]. *)

(* It first tries [try_reuse_path_spec] (see above). Failing that (no
   [path_spec] hypothesis found anywhere along the way, or its
   postcondition doesn't line up with the goal's), it falls back to the
   original strategy: [path_spec_to_in_env] reduces the goal to
   [in_env _ _ η], which [solve_in_env] then solves.

   In the case where the path is not a singleton, [solve_path_spec]
   calls itself recursively on the tail of the path. *)

Ltac2 rec solve_path_spec () :=
  Control.plus
    try_reuse_path_spec
    (fun _ =>
       match path_spec_to_in_env () with
       | Psingleton => solve_in_env ()
       | Pcons =>
           Control.focus 1 1 (fun _ => complete solve_in_env);
           let hyp_name := iFresh "Hpath" in
           iIntros ("% #" ++ $hyp_name)%string;
           solve_path_spec ()
       end).

(** User-level tactics. *)

(* Ltac1 entry points for the two solvers above, so that the environment
   dependencies left over by a body lemma can be discharged without
   writing an [ltac2:(...)] quotation. Ltac1 and Ltac2 have separate
   namespaces, so these keep the names of the tactics they call. *)

Tactic Notation "solve_in_env" := ltac2:(solve_in_env ()).
Tactic Notation "solve_path_spec" := ltac2:(solve_path_spec ()).

(* [solve_env] discharges one environment-dependency goal, whichever of
   the two forms it takes. Body lemmas state their dependencies under a
   [▷] when the binding is recursive, so the later is stripped first. *)

(* Written after [iApply foo_proof], as [iApply foo_proof; solve_env], it
   discharges every dependency of [foo] on its environment at once. *)

Ltac solve_env :=
  (* A body lemma states its environment dependencies under a [▷] when
     the binding is recursive, and under a [□] when the specification is
     used more than once (the shape the stdlib proofs use). *)
  repeat (first [ iNext | iModIntro ]);
  first [ solve_in_env | solve_path_spec ];
  (* Reaching the binding leaves its specification as a goal; it is in
     the context, as the hypothesis the lookup was resolved against. *)
  try (iFrame "#"; done).

Ltac2 solve_eq_goal () :=
  (* The postcondition may be wrapped in the [tapp] coercion (from the
     n-ary application machinery used for tuples and records), which
     hides the postcondition evar behind [tapp].  When [tapp] is applied
     to an evar, unfold it so that the evar appears as the head of the
     goal and the evar branch below fires.  We only do so for an evar,
     to leave concrete postconditions untouched for downstream tactics.
     ([cbn]/[simpl] do not reduce [tapp], because of the [Arguments tapp
     ... /] simpl-nomatch hint.) *)
  (lazy_match! get_iris_goal () with
   | tapp ?f _ => if Constr.is_evar f then ltac1:(unfold tapp) else ()
   | _ => ()
   end);
  lazy_match! get_iris_goal () with
  | (⌜_ = _⌝)%I => ltac1:(equality)
  | ?spec ?x =>
      match Constr.Unsafe.kind spec with
      | Constr.Unsafe.Evar _ _ =>
          let prop := '(λ x,⌜x=$x⌝)%I in
          (* Instantiate the postcondition evar to [λ x, ⌜x = v⌝], then
             discharge the resulting equality with [equality] (as in the
             concrete branch above).  We must instantiate the evar
             unconditionally (not under [try_complete]): otherwise a
             failure to fully close would roll the instantiation back and
             leave an evar postcondition, on which the subsequent
             [iFrame] raises a unification error.  We use [equality]
             rather than [auto], which is too weak to close the pure
             equality. *)
          Std.unify spec prop;
          try (ltac1:(equality))
      | _ => ()
      end
  end.

Ltac2 imp_path_tac () :=
    (* Resolve the path. *)
    iApply imp_EPath_spec;
    solve_path_spec ();
    (* If there is a goal remaining. *)
    Control.enter
      (fun _ =>
         if empty_spatial_env () then
           (* If there are no resources, first try to solve the goal as an equality. *)
           (solve_eq_goal ();
           (* If that failed, try to frame the persistent resources. *)
            Control.enter (fun _ => iFrame "#"))
         else
           try_complete (fun _ => iFrame)).

Ltac2 Notation "imp_path" := imp_path_tac ().
Tactic Notation "imp_path" := ltac2:(imp_path).

Ltac2 Notation "imp_path_eq" :=
  imp_path_tac (); solve_eq_goal ().
Tactic Notation "imp_path_eq" := ltac2:(imp_path_eq).

(* --------------------------------------------------------------------------*)
(* Testing the [imp_path] tactic. *)

From iris.proofmode Require Import ltac_tactics.

Set Default Proof Mode "Classic".

Section TacticTests.

  Context `{!osirisGS Σ}.

  Local Open Scope Z.

  (* We define a short program, [e]:
     ```
     let x = 2 in
     let y = z in
     Module1.add (Module2.Module3.sub y x) a
     ```
   *)

  Definition e :=
    ELet [Binding (PVar "x") (EInt 2)] (
        ELet [Binding (PVar "y") (EPath ["z"])] (
            EApp
              (EApp (EPath ["Module1"; "add"])
                 (EApp
                    (EApp (EPath ["Module2";"Module3";"sub"]) (EPath ["y"]))
                    (EPath ["x"])))
              (EPath ["a"])
          )
      ).

  (* We then verify this program under the assumption that:
     - [z] is in the environment and is positive
     - Module1 is in the environment and contains [add]
     - Module2 is in the environment and contains [Module3],
       which contains [sub] *)

  Definition add_spec add : iProp Σ :=
    □ {{ True }} add (i : Z) (j : Z) : Z Z {{ RET k; ⌜(k = i + j)%Z⌝ }}.
  Definition sub_spec sub : iProp Σ :=
    □ {{ True }} sub (i : Z) (j : Z) : Z Z {{ RET k; ⌜(k = i - j)%Z⌝ }}.
  Definition a_spec a : iProp Σ := ∀ (A : Type), □ ⌜a > 2⌝.

  Definition module3_spec η := context [var_spec "sub" sub_spec] {["sub"]} η.
  Definition module2_spec η := context [var_spec "Module3" module3_spec] {["Module3"; "some"; "other"; "stuff"]} η.

  Lemma example_proof δ η :
    in_env "z" (λ (i : Z), ⌜i > 0⌝) η -∗
    in_env "a" a_spec η -∗
    context [var_spec
               "Module1"
               (context [var_spec "some_other_val" (λ (_ : val), True);
                         var_spec "add" add_spec] {["some_other_val";"add"]})
      ] {["Module1"]} δ -∗
    context [var_spec "Module2" module2_spec] {["Module2";"z"]} η -∗
    EWP (eval (δ ++ η) e) {{ (i : Z), ⌜i > 0⌝ }}.
  Proof.
    iIntros "#zspec #aspec #δspec #ηspec".
    (* TODO: imp_let tactic which instantiates
       the return type of the left member with an evar. *)
    evar(B:Type).
    evar(HB:Encode B).
    iApply (imp_ELet_var (B:=B)). { iApply imp_EInt. }
    subst B HB.
    iIntros (? ->).
    iApply (imp_ELet_var (B:=Z)).
    { imp_path. }
    iIntros (z) "%yspec".
    iApply (imp_EApp τ[Z;Z]).
    { imp_path. }
    { iApply (imp_EApp τ[Z;Z]).
      { imp_path. }
      { imp_path. }
      { imp_path. }
      iIntros (??) "-> -> %m Hm !>".
      by iApply "Hm". }
    { imp_path. }
    iIntros (??) "-> #%Ha %m Hm !>".
    iSpecialize ("Hm" with "[//]").
    iApply (imp_wand with "Hm").
    iIntros (y ->). iPureIntro.
    specialize (Ha unit).
    lia.
  Qed.

  (* A path into a module whose environment is bound in place, rather
     than spliced into the environment with [++]. This is the shape
     [imp_sitems_module] produces: the module's bindings come as a plain
     [in_env] hypothesis over a fresh environment variable [δM].

     [path_spec_cons] leaves the module's own specification as an evar,
     which [solve_env_spec_evar] reads off the context. *)

  Lemma example_module_path (δM η : env) :
    in_env "sub" sub_spec δM -∗
    path_spec ["Module"; "sub"] sub_spec (("Module", #δM) :: η).
  Proof.
    iIntros "#HM". solve_path_spec.
  Qed.

  (* One module deeper, the outer module being specified by a [context]
     hypothesis: the evar for the outer environment is read off that
     hypothesis, and the inner one off [module3_spec]. *)

  Lemma example_nested_module_path (δM η : env) :
    context [var_spec "Module3" module3_spec] {["Module3"]} δM -∗
    path_spec ["Module2"; "Module3"; "sub"] sub_spec (("Module2", #δM) :: η).
  Proof.
    iIntros "#HM". solve_path_spec.
  Qed.

End TacticTests.
