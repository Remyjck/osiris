From iris.proofmode Require Import proofmode environments ltac_tactics.

From osiris.lang Require Import lang.

From osiris.program_logic Require Import program_logic osiris_utils.
Require Import pure_tactics.

From osiris.utils Require Import tactics.

(** *Utility *)

Section helper_lemmas.

Context `{!osirisGS Σ}.

Lemma bi_sep_intro (P Q : iProp Σ) :
  P -∗
  Q -∗
  P ∗ Q.
Proof.
  iIntros "H1 H2".
  iFrame.
Qed.

Lemma bi_emp_intro :
  ⊢ @bi_emp (iProp Σ).
Proof.
  done.
Qed.

End helper_lemmas.

From Ltac2 Require Import Ltac2 Printf.


Create HintDb osiris.
Create Rewrite HintDb osiris.

Set Default Proof Mode "Classic".

(* Some hints used for resolving [repr] expressions *)
Global Hint Rewrite eq_repr_repr sub_repr_repr mul_repr_repr: osiris.
Global Hint Extern 1 (representable _) => representable : osiris.
Global Hint Unfold val_as_int : osiris.

(* -------------------------------------------------------------------------- *)

(** *Proving Handlers and Matches *)

(* Proving that a handler satisfies its specification involves proving
   the effectful case and the return/exceptional case. *)

Ltac prove_handler_spec :=
  rewrite deep_handler_spec_unfold; iSplit.


(* -------------------------------------------------------------------------- *)

(** *Entering and Skipping Handler Branches *)

Ltac2 do_iintros () :=
  try (iModIntro);
  lazy_match! get_iris_goal () with
  | bi_forall _ =>
      (* Match case: [∀ η', ⌜Hη η'⌝ -∗ EWP (eval η' e) ...].
         When [Hη] is a concrete equality [λ η', η' = δ] (the no-guard case,
         e.g. built-in patterns), rewrite with it.  When [Hη] is still an evar
         (unreachable branch), close via [False].  Otherwise [Hη] is a guarded
         postcondition [λ η', ∃ …, c = … ∧ η' = δ] produced by [close_success]
         for a constructor pattern: leave the body goal for the user to
         introduce with their own pattern (e.g. [iIntros (η') "(%r & %Hc & ->)"]),
         so the matched-constructor equation is available in the branch body. *)
      Control.plus
        (fun _ => ltac1:(iIntros (? ->)))
        (fun _ => Control.plus
                    (* Genuine unreachable branch: [iIntros (? [])] closes it.
                       Gated by [complete] so it does *not* fire on a guarded
                       postcondition (where it would introduce without closing). *)
                    (fun _ => complete (fun _ => ltac1:(iIntros (? []))))
                    (fun _ => ()))
  | bi_wand ?h _ =>
      lazy_match! h with
      | ⌜True⌝%I => iIntros "_"
      | True => iIntros "_"
      | ⌜False⌝%I => iIntros "[]"
      | False => iIntros "[]"
      | ⌜not _⌝%I =>
          (* [⌜¬P⌝ -∗ Q]: introduce [H : ¬P] and apply [([])], leaving
             sub-goal [P].  This lets the user close the no-match case
             with [auto]/[reflexivity] when P is a tautology (e.g. [1 = 1]). *)
          ltac1:(iIntros ([]))
      | ⌜_⌝%I =>
          ltac1:(_iIntros0 (intro_patterns.IPure (intro_patterns.IGallinaAnon)));
          (* If the introduced hypothesis is False-valued (e.g. [(False ∨ False) ∨ False]
             from a no-match branch), close the goal immediately via exfalso. *)
          try ltac1:(exfalso; tauto)
      | _ => iIntros "?"
      end
  | _ => ()
  end.

(* -------------------------------------------------------------------------- *)

(** *Closing a match-success postcondition while preserving the guard *)

(* When [solve_pure_cpattern] drives the [cpattern]/[pattern] machinery on
   an Iris match, the per-branch success postcondition [Hη : env → Prop] is
   an evar threaded from [deep_handle_cons] down to the matching leaf, where
   it surfaces as a goal [?Hη δ] ([δ] the matched environment).

   [apply eq_refl] pins [?Hη := λ η', η' = δ], which drops the guard for a
   constructor pattern: matching leaves the bound variables and a guard
   equation [c = Ctor …] in context, and a bare environment equality throws
   them away, leaving the branch body unconstrained by the matched case.

   [close_success before] instead closes over the hypotheses introduced
   since [before]:
     [λ η', ∃ <delta vars>, <delta guards> ∧ η' = δ],
   so the branch body goal carries the matched-constructor equation. With no
   such hypotheses it degenerates to [λ η', η' = δ]. *)

(* [subst_var id t c] replaces every occurrence of the local variable [id] in
   [c] by [t].  [t] is atomic (a variable), so no de Bruijn lifting is needed. *)
Ltac2 rec subst_var (id : ident) (t : constr) (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var v => if Ident.equal v id then t else c
  | _ => Constr.Unsafe.map (subst_var id t) c
  end.

Ltac2 is_prop (ty : constr) : bool := Constr.equal (Constr.type ty) constr:(Prop).

(* [occurs id c] holds when the local variable [id] appears in [c].  Tested by
   substituting [id] for a sentinel and checking whether [c] changed. *)
Ltac2 occurs (id : ident) (c : constr) : bool :=
  let sentinel := Constr.Unsafe.make (Constr.Unsafe.Var @osiris_occ_sentinel) in
  Bool.neg (Constr.equal c (subst_var id sentinel c)).

(* [build_closure delta seed] builds, in the current context, the body
   [∃ <delta vars>, <delta guards> ∧ seed], where [delta] is the outer-first
   list of [(ident, type)] introduced during matching: a [Prop]-typed entry
   becomes a conjunct, any other entry becomes an existential binder (its
   ambient occurrences in the remaining entries and in [seed] are abstracted
   into the fresh binder via [subst_var]). *)
Ltac2 rec build_closure (delta : (ident * constr) list) (seed : constr) : constr :=
  match delta with
  | [] => seed
  | p :: rest =>
      let (id, ty) := p in
      if is_prop ty then
        let rt := build_closure rest seed in constr:($ty /\ $rt)
      else
        let fid := Fresh.in_goal id in
        let fvar := Constr.Unsafe.make (Constr.Unsafe.Var fid) in
        let rest := List.map (fun q => let (i, t) := q in (i, subst_var id fvar t)) rest in
        let seed := subst_var id fvar seed in
        let lam := Constr.in_context fid ty
                     (fun () => let rt := build_closure rest seed in exact $rt) in
        constr:(@ex $ty $lam)
  end.

Ltac2 hyp_ids () : ident list :=
  List.map (fun h => let (id, _, _) := h in id) (Control.hyps ()).

Ltac2 rec dedup_props (seen : constr list) (delta : (ident * constr) list)
  : (ident * constr) list :=
  match delta with
  | [] => []
  | p :: rest =>
      let (_, ty) := p in
      if is_prop ty then
        if List.exist (fun t => Constr.equal t ty) seen
        then dedup_props seen rest
        else p :: dedup_props (ty :: seen) rest
      else p :: dedup_props seen rest
  end.

(* [relevant_delta delta d] selects, from the matching-introduced hypotheses
   [delta], exactly those that carry useful information about the matched value:
   - a [Prop] guard is kept iff it mentions a matching-introduced *variable*
     (this is what distinguishes a constructor guard [c = Root r] from a benign
     side condition like [1 = 1] that built-in patterns leave behind);
   - a variable is kept iff it is mentioned by the matched environment [d] or by
     a kept guard (so the resulting existential closure is well-scoped).
   When nothing is relevant (built-in patterns), the result is empty and the
   closure degenerates to [λ η', η' = d]. *)
Ltac2 relevant_delta (delta : (ident * constr) list) (d : constr)
  : (ident * constr) list :=
  let vars := List.map (fun q => let (i, _) := q in i)
                (List.filter (fun q => let (_, ty) := q in Bool.neg (is_prop ty)) delta) in
  let guard_mentions := fun ty => List.exist (fun v => occurs v ty) vars in
  let mguards := List.filter
                   (fun q => let (_, ty) := q in Bool.and (is_prop ty) (guard_mentions ty))
                   delta in
  let needed := fun v =>
    Bool.or (occurs v d)
            (List.exist (fun q => let (_, gty) := q in occurs v gty) mguards) in
  List.filter
    (fun q => let (id, ty) := q in
              if is_prop ty then guard_mentions ty
              else needed id)
    delta.

Ltac2 close_success (before : ident list) : unit :=
  let delta :=
    dedup_props []
      (List.map (fun h => let (id, _, ty) := h in (id, ty))
        (List.filter
           (fun h => let (id, _, _) := h in
                     Bool.neg (List.mem Ident.equal id before))
           (Control.hyps ()))) in
  lazy_match! goal with
  | [ |- ?h ?d ] =>
      if Constr.is_evar h then
        let delta := relevant_delta delta d in
        let efresh := Fresh.in_goal @η in
        let body := Constr.in_context efresh constr:(env)
          (fun () =>
             let ev := Constr.Unsafe.make (Constr.Unsafe.Var efresh) in
             let b := build_closure delta constr:($ev = $d) in
             exact $b) in
        unify $h $body;
        ltac1:(repeat eexists; repeat split; try eassumption; try reflexivity)
      else ()
  | [ |- _ ] => ()
  end.

(* The pure matching engine, shared by the pure and mixed routes of
   [next_branch].  [solve_pure_cpattern] expects a pure goal
   [cpattern η δ cp o ?φ ?ψ]: it resolves the [cpattern] level
   ([specify_cpattern]), drives the resulting [pattern] goals with
   [pattern_match0], and closes the leaves ([close_pure_leaves]).

   It is the iris proofmode analog of [pure_match] in the pure mode. *)

Local Ltac2 close_pure_leaves (before : ident list) : unit :=
  try (Control.enter
         (fun _ =>
            match! goal with
            | [ |- ?g ] =>
                if Constr.is_evar g then
                  apply I
                else
                  (* [?Hη δ]: the match postcondition evar applied to the
                     matched environment. [close_success] instantiates it to
                     the existential closure of the hypotheses introduced
                     since [before]. Skipped if it fails. *)
                  Control.plus
                    (fun _ => close_success before)
                    (fun _ => ())
            end)).

Local Ltac2 solve_pure_cpattern () : unit :=
  (* Snapshot the context *before* matching, so [close_success] can later
     tell which hypotheses (bound variables, guard equations) the matching
     introduced. *)
  let before := hyp_ids () in
  let n := specify_cpattern () in
  if (Int.gt n 0)
  then
    (* [specify_cpattern] resolves
       a [cpattern] and leaves behind a [pattern] which needs
       to be solved with a [pattern_match0] here. *)
    (Control.focus 1 n pattern_match0;
     close_pure_leaves before)
  else ().

(* [icpattern_pure_route]/[ipattern_pure_route] lower an Iris pattern
   judgement whose pattern does not read the heap to the pure engine,
   through the [icpattern_pure_cps]/[ipattern_pure_cps] lemmas.  After
   [do_iintros] enters the success/failure wands, [k] continues on the
   surviving goals: the branch body or a remaining pattern judgement on
   the success side, the remaining branches on the failure side. *)

Local Ltac2 icpattern_pure_route (k : unit -> unit) :=
  iApply icpattern_pure_cps;
  Control.focus 1 1 solve_pure_cpattern;
  (* Beta-reduce any redexes introduced by evar instantiation
     (e.g. [⌜(λ η', η' = δ) η'⌝] → [⌜η' = δ⌝]) so that [do_iintros]
     can recognise the equality and apply [iIntros (? ->)]. *)
  try (last (fun _ => ltac1:(cbn beta)));
  (* [do_iintros] may close a side entirely (e.g. an unreachable
     failure wand), so [k] is re-entered only on the surviving goals. *)
  last (fun _ => iSplit;
                 Control.enter (fun _ => do_iintros ();
                                         Control.enter (fun _ => k ()))).

Local Ltac2 ipattern_pure_route (k : unit -> unit) :=
  iApply ipattern_pure_cps;
  Control.focus 1 1
    (fun _ =>
       let before := hyp_ids () in
       pattern_match0 ();
       close_pure_leaves before);
  try (last (fun _ => ltac1:(cbn beta)));
  last (fun _ => iSplit;
                 Control.enter (fun _ => do_iintros ();
                                         Control.enter (fun _ => k ()))).

(* -------------------------------------------------------------------------- *)

(** *Iris-level pattern matching *)

(* [next_branch] processes one branch of an [EWP (eval_branches η o
   (Branch cp e :: bs))] goal. It applies [deep_handle_cons_iris'], which
   threads the branch body and the remaining branches through the
   [icpattern] judgement, then dispatches on the pattern:

   - a pattern (or sub-pattern) that does not read the heap is lowered to
     the pure engine ([icpattern_pure_route]/[ipattern_pure_route]);
   - heap-reading patterns are walked with the matching [ipat_*] rule.
     Record patterns consume and give back the ownership hypothesis
     [r ⤇ _] / [ownBlock r _ _ _] from the spatial context, and their
     field sub-patterns go to the pure [fpatterns] automation.

   On success the remaining goal is the branch body [EWP (eval η' e) ...],
   with the ownership hypotheses back under their own names; on refutation
   it is [EWP (eval_branches η o bs) ...] for the remaining branches. *)

(* [reads_heap p] detects (sub-)patterns whose matching must read the
   heap: record and array patterns. *)

Ltac2 reads_heap (p : constr) : bool :=
  match! p with
  | context [ PRecord _ ] => true
  | context [ PArray _ ] => true
  | _ => false
  end.

(* [get_record_ownership r] finds a spatial hypothesis [ownRecord r _ _]
   or [ownBlock r _ _ _] for the record location [r] and returns its
   proofmode identifier. *)

Ltac2 get_record_ownership (r : constr) : constr :=
  let (_, spat_hyps) := get_iris_hyps () in
  let rec go env :=
    lazy_match! env with
    | environments.Enil =>
        Control.zero
          (Tactic_failure
             (Some (fprintf "Could not find ownership of the record block %t" r)))
    | environments.Esnoc ?env ?name ?prop =>
        match! prop with
        | ownRecord ?r' _ _ => if Constr.equal r r' then name else go env
        | ownBlock ?r' _ _ _ => if Constr.equal r r' then name else go env
        | _ => go env
        end
    end
  in
  go spat_hyps.

(* [ipat_record_cps v k] processes a goal
   [ipattern η δ (PRecord fps) v Φ ψ]: it locates the ownership of the
   record block behind [v], applies the continuation-passing record
   rule, solves the field patterns with the pure automation, and runs
   [k] on the continuation, with the matched environment substituted
   and the ownership back in the context under its original name. *)

(* Solve a goal [v = VRecord ?r], [v = VTuple ?vs], [v = VTaggedRecord s ?v'],
   ... where [v] may be an encoded value [# x]. *)
Local Ltac2 solve_val_eq () :=
  solve [ ltac1:(first [ reflexivity
                       | rewrite encode_encode'; reflexivity
                       | encode ]) ].

Local Ltac2 ipat_record_cps (v : constr) (k : unit -> unit) :=
  let r :=
    lazy_match! v with
    | VRecord ?r => r
    | # ?r => r
    | _ =>
        Control.zero
          (Tactic_failure
             (Some (fprintf "[next_branch] cannot find a record block in %t" v)))
    end
  in
  let hname := get_record_ownership r in
  let name := match! hname with
              | base.ident.INamed ?s => s
              | _ => '"Hrec"%string
              end in
  let pat := '("% -> " ++ $name)%string in
  let solve_valid_fields := fun () =>
    solve [ ltac1:(unfold valid_field; repeat constructor; simpl; lia) ]
  in
  let apply_one := fun (lem : constr) =>
    iApply ($lem with $hname) >
      [ solve_val_eq ()
      | solve_valid_fields ()
      | pattern_match0 ()
      | solve [ ltac1:(tauto) ]
      | iIntros $pat; k () ]
  in
  Control.plus
    (fun _ => apply_one 'ipat_PRecord_repr_cps)
    (fun _ => apply_one 'ipat_PRecord_cps).

Local Ltac2 stop_here (t : unit -> unit) : unit :=
  Control.plus t (fun _ => ()).

Ltac2 rec ipattern_match_aux () :=
  ltac1:(cbn beta);
  (* [Control.case] (not [Control.plus]) so that this probe is not a
     backtracking point: a failure later in the walk must propagate,
     not rewind into the [Err] arm and succeed silently. *)
  match Control.case (fun _ => get_iris_goal ()) with
  | Err _ =>
      (* Not an Iris entailment: a pure side condition the pure engine
         left for the user (e.g. the witness of a refuted branch). *)
      ()
  | Val gk =>
  let (g, _) := gk in
  lazy_match! g with
  | icpattern _ _ ?cp _ _ _ =>
      if reads_heap cp then
        lazy_match! cp with
        | CVal _ => iApply icpat_CVal; ipattern_match_aux ()
        | _ =>
            Control.zero
              (Tactic_failure
                 (Some (fprintf
                    "[next_branch] unsupported heap-reading computation pattern %t" cp)))
        end
      else icpattern_pure_route ipattern_match_aux
  | ipatterns _ _ (_ :: _) _ _ _ =>
      iApply ipats_cons; ipattern_match_aux ()
  | ipatterns _ _ nil _ _ _ =>
      iApply ipats_nil; ipattern_match_aux ()
  | ipattern _ _ ?p ?v _ _ =>
      if reads_heap p then
        lazy_match! p with
        | PAlias _ _ => iApply ipat_PAlias; ipattern_match_aux ()
        | PTuple _ =>
            stop_here
              (fun _ => iApply ipat_PTuple' >
                          [ solve_val_eq () | ipattern_match_aux () ])
        | PTaggedRecord _ _ =>
            Control.plus
              (fun _ => iApply ipat_PTaggedRecord_eq >
                          [ solve_val_eq ()
                          | ipattern_match_aux () ])
              (fun _ => stop_here
                  (fun _ => iApply ipat_PTaggedRecord_neq > [ ltac1:(congruence) | () ]))
        | PRecord _ =>
            stop_here
              (fun _ => ipat_record_cps v (fun _ => ipattern_match_aux ()))
        | _ =>
            Control.zero
              (Tactic_failure
                 (Some (fprintf
                    "[next_branch] unsupported heap-reading pattern %t" p)))
        end
      else ipattern_pure_route ipattern_match_aux
  | _ =>
      (* Not a pattern judgement: the branch body (or the remaining
         branches) has been reached. *)
      ()
  end
  end.

(* [iApply deep_handle_cons_iris'] can succeed *vacuously* on a goal whose
   postcondition is still an evar, by unifying the whole [icpattern]
   premise into the evar and leaving no goal at all. Reject that case so
   [next_branch] fails cleanly, backtracking the spurious unification
   instead of corrupting the scrutinee's postcondition. *)

Local Ltac2 apply_deep_handle_cons_iris' () :=
  iApply deep_handle_cons_iris';
  if Int.equal (Control.numgoals ()) 1 then ()
  else Control.zero
         (Tactic_failure
            (Some (Message.of_string
               "[next_branch] expected an [eval_branches] goal"))).

Ltac2 next_branch0 () :=
  let resumable () :=
    match Control.case (fun _ => get_iris_goal ()) with
    | Err _ => false
    | Val gk =>
        let (g, _) := gk in
        lazy_match! g with
        | icpattern _ _ _ _ _ _ => true
        | ipattern _ _ _ _ _ _ => true
        | ipatterns _ _ _ _ _ _ => true
        | _ => false
        end
    end
  in
  if resumable () then progress (ipattern_match_aux ())
  else
    (Control.plus
       (fun _ => apply_deep_handle_cons_iris' ())
       (fun _ => ltac1:(progress simpl); apply_deep_handle_cons_iris' ());
     ipattern_match_aux ()).

Ltac2 Notation "next_branch" := next_branch0 ().
Tactic Notation "next_branch" := ltac2:(next_branch0 ()).

(* [imp_branches] processes all branches of an [EWP (eval_branches η o bs)]
   goal, one Iris subgoal per branch; the Iris analogue of [pure_match].
   For each branch it applies [next_branch], which resolves the pattern,
   [iSplit]s into the match/no-match pair, auto-closes no-match goals whose
   postcondition is provably [False], and leaves the branch body as an open
   subgoal. Recursion stops when [next_branch] fails. *)

Ltac2 rec imp_branches0 () :=
  Control.plus
    (fun _ =>
       next_branch0 ();
       try (last (fun _ => imp_branches0 ())))
    (fun _ => ()).

Ltac2 Notation "imp_branches" := imp_branches0 ().
Tactic Notation "imp_branches" := ltac2:(imp_branches0 ()).

(* -------------------------------------------------------------------------- *)

(** *Match *)

(* [imp_match] applies the [imp_EMatch] rule to a goal of the form
   [EWP eval η (EMatch e bs) ...].  It dispatches two subgoals:
     1. the scrutinee expression [EWP eval η e {{ Φ' }}], which [imp_step]
        is tried on automatically;
     2. the eval_branches continuation, where [simple_intros] peels off the
        [∀ a, Φ' a -∗ ▷] prefix and then [imp_branches] automatically
        processes all pattern branches.
   Optionally, the intermediate type [A'] of the scrutinee can be given as
   an argument.  If omitted, [A'] and its [Encode] instance are left as
   evars, to be resolved by the scrutinee subgoal. *)

From osiris.proofmode Require Import imp_tactics.

(* [phi], when given, fixes the scrutinee's postcondition [Φ'] up front
   (via [imp_EMatch (Φ':=phi)]). Needed whenever the continuation proof
   picks its own witnesses for an existential [Φ']: [iExists] cannot act
   on an evar-headed goal. Mirrors the [imp_store' l $! Φ] convention. *)

Ltac2 imp_match_tac (a' : constr option) (phi : constr option) (selpat : constr option) :=
  let e := get_expr () in
  lazy_match! eval hnf in $e with
  | EMatch _ _ =>
    let a :=
      match a' with
      | None =>
        mk_evar @imp_match_A' 'Type;
        let match_a := Control.hyp @imp_match_A' in
        (* The [Encode] evar must be created with [evar], not by
           pretyping an [open_constr] hole: [imp_match_A'] is
           syntactically rigid, so elaborating [(_ : Encode
           imp_match_A')] satisfies the [Hint Mode] and eagerly runs
           the instance search, which picks an arbitrary instance and
           pins [imp_match_A'] to its carrier.  [evar] creates the
           hole without resolution; the let-binding still acts as the
           local instance when [iApply] later searches
           [Encode imp_match_A']. *)
        let ty := constr:(Encode $match_a) in
        ltac1:(t |- evar (imp_match_HA' : t)) (Ltac1.of_constr ty);
        match_a
      | Some a => a
      end
    in
    let specialized_match :=
      match phi with
      | None => open_constr:(imp_EMatch (A':=$a))
      | Some phi => open_constr:(imp_EMatch (A':=$a) $phi)
      end
    in
    (match selpat with
    | None => iApply $specialized_match
    | Some sel => iApply ($specialized_match with $sel)
    end) >
    [ try (imp_step0 None) | simple_intros (); try (imp_branches0 ()) ]
  | _ =>
      Control.zero (Tactic_failure
        (Some (fprintf "[imp_match] Expected EMatch expression, got %t" e)))
  end.

Ltac2 Notation "imp_match" a'(constr) := imp_match_tac (Some a') None None.
Ltac2 Notation "imp_match" := imp_match_tac None None None.
Ltac2 Notation "imp_match" a'(constr) "with" sel(constr) :=
  imp_match_tac (Some a') None (Some sel).
Ltac2 Notation "imp_match" "with" sel(constr) :=
  imp_match_tac None None (Some sel).
Ltac2 Notation "imp_match" a'(constr) "$!" phi(constr) :=
  imp_match_tac (Some a') (Some phi) None.
Ltac2 Notation "imp_match" a'(constr) "$!" phi(constr) "with" sel(constr) :=
  imp_match_tac (Some a') (Some phi) (Some sel).

Tactic Notation "imp_match" constr(a') :=
  let tac := ltac2:(a' |- imp_match_tac (Ltac1.to_constr a') None None) in
  tac a'.
Tactic Notation "imp_match" := ltac2:(imp_match_tac None None None).
Tactic Notation "imp_match" constr(a') "with" constr(sel) :=
  let tac := ltac2:(a' sel |-
                      imp_match_tac (Ltac1.to_constr a') None (Ltac1.to_constr sel)) in
  tac a' sel.
Tactic Notation "imp_match" "with" constr(sel) :=
  let tac := ltac2:(sel |- imp_match_tac None None (Ltac1.to_constr sel)) in
  tac sel.
Tactic Notation "imp_match" constr(a') "$!" constr(phi) :=
  let tac := ltac2:(a' phi |-
                      imp_match_tac (Ltac1.to_constr a') (Ltac1.to_constr phi) None) in
  tac a' phi.
Tactic Notation "imp_match" constr(a') "$!" constr(phi) "with" constr(sel) :=
  let tac := ltac2:(a' phi sel |-
                      imp_match_tac (Ltac1.to_constr a') (Ltac1.to_constr phi) (Ltac1.to_constr sel)) in
  tac a' phi sel.
