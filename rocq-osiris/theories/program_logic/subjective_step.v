From Stdlib Require Import Program.Equality.

From stdpp Require Import gmap fin_map_dom fin_sets.
From osiris Require Import base.
From osiris.lang Require Import lang.
From osiris.utils.logic Require Import lsteps.
From osiris.semantics Require Import code eval step.

From iris.base_logic.lib Require Import iprop own.

(* -------------------------------------------------------------------------- *)

(* The store of the program logic is the heap of the semantics together with
   the set of prophecy identifiers allocated so far, which is where the
   freshness of a new prophecy is decided. *)

Global Instance proph_id_eq_decision : EqDecision proph_id :=
  locations.loc_eq_decision.

Global Instance proph_id_countable : Countable proph_id :=
  locations.loc_countable.

Global Instance proph_id_infinite : Infinite proph_id :=
  locations.Infinite_loc.

Record store : Type := Store {
  st_heap : heap;
  used_proph_id : gset proph_id;
}.

Global Instance store_empty : Empty store := Store ∅ ∅.

Definition store_upd_heap (f : heap → heap) (σ : store) : store :=
  Store (f σ.(st_heap)) σ.(used_proph_id).
Global Arguments store_upd_heap _ _ /.

Definition store_upd_used_proph_id (f : gset proph_id → gset proph_id)
    (σ : store) : store :=
  Store σ.(st_heap) (f σ.(used_proph_id)).
Global Arguments store_upd_used_proph_id _ _ /.

(* A step that leaves the heap unchanged leaves the store unchanged. *)

Lemma store_eta (σ : store) : Store σ.(st_heap) σ.(used_proph_id) = σ.
Proof. by destruct σ. Qed.

Lemma store_upd_heap_id (σ : store) : store_upd_heap (λ _, σ.(st_heap)) σ = σ.
Proof. apply store_eta. Qed.

(* The thread-pool configurations of the program logic. *)

Definition ptconfig : Type := (store * thpool)%type.

Section subjective_step.

  Context {Σ : gFunctors}.

  Definition is_outcome {A X} (m : micro A X) :=
    match m with
    | Ret v => Some (O2Ret v)
    | Throw v => Some (O2Throw v)
    | _ => None
    end.

  (* A thread pool's postconditions, indexed by thread id. The predicates are
     stored directly, so no gname indirection is needed to reach them. *)
  Definition post_map (Σ' : gFunctors) := gmap thread (outcome2 val exn -d> iPropO Σ').
  Instance lookup_post_map : Lookup thread (outcome2 val exn -d> iPropO Σ) (post_map Σ).
  Proof. apply _. Defined.

  Definition th_config A X : Type := store * (micro A X) * (gset thread).
  Definition th_config_step A X : Type := store * (micro A X) * option (thread * microvx).

  (* [subjective_step] is the stepping relation viewed from a single thread.
     A step of the semantics acts on the heap and leaves the prophecy
     identifiers alone. *)

  Inductive subjective_step {A X} :
    th_config A X -> list observation -> th_config_step A X -> Prop :=
  | BaseS : ∀ (m : micro A X) σ m' σ' π,
      step (σ.(st_heap), m) (σ', m') ->
      subjective_step (σ, m, π) [] (store_upd_heap (λ _, σ') σ, m', None)
  | ForkS : ∀ σ ι (π : gset thread) v1 v2 (k : outcome2 val exn -> micro A X),
      ι ∉ π ->
      subjective_step
        (σ, Stop CFork (v1, v2) k, π) []
        (σ, continue k (VThread ι), Some (ι, call v1 v2))
  (* [stop CNewProph ()] allocates a prophecy identifier. *)
  | NewProphS : ∀ σ x p π (k : outcome2 proph_id exn -> micro A X),
      p ∉ σ.(used_proph_id) ->
      subjective_step
        (σ, Stop CNewProph x k, π) []
        (store_upd_used_proph_id ({[ p ]} ∪.) σ, continue k p, None)
  (* The stop call and the resolution happen in one subjective step. An
     observation emitted one step later could be separated from the effect
     by another thread, and could separate it from the linearization point. *)
  | ResolveS : ∀ {Y} σ h' (c : code Y val exn) x p v b π
        (k : outcome2 val exn -> micro A X),
      step (σ.(st_heap), stop c x) (h', b) ->
      is_result b ->
      subjective_step
        (σ, Stop (CResolve c) (x, p, v) k, π) (resolve_obs p v b)
        (store_upd_heap (λ _, h') σ, try2 b k, None)
  .

  Global Arguments subjective_step {A X}.

(* -------------------------------------------------------------------------- *)

  (* [proph_step] is exactly the semantic model [threadpool_step], acting on
     the heap, plus the allocation and the resolution of prophecies. *)

  Inductive proph_step : ptconfig -> list observation -> ptconfig -> Prop :=
  | PureTS :
    ∀ σ π h' π',
      threadpool_step (σ.(st_heap), π) (h', π') ->
      proph_step (σ, π) [] (store_upd_heap (λ _, h') σ, π')

  (* [NewProphS] one pool level up. *)
  | NewProphTS :
    ∀ ι π σ x p k,
      π !! ι = Some (Stop CNewProph x k) ->
      p ∉ σ.(used_proph_id) ->
      proph_step
        (σ, π) []
        (store_upd_used_proph_id ({[ p ]} ∪.) σ, <[ ι := continue k p ]> π)

  (* [ResolveS] one pool level up: same [is_result] premise, same [try2]
     dispatch on the outcome, same [resolve_obs] label. *)
  | ResolveTS :
    ∀ ι π σ h' {Y} (c : code Y val exn) x p v b k,
      π !! ι = Some (Stop (CResolve c) (x, p, v) k) ->
      step (σ.(st_heap), stop c x) (h', b) ->
      is_result b ->
      proph_step
        (σ, π) (resolve_obs p v b)
        (store_upd_heap (λ _, h') σ, <[ ι := try2 b k ]> π)
  .

End subjective_step.

Create HintDb subjective_step.

Global Hint Constructors subjective_step : subjective_step.
Global Hint Constructors proph_step : subjective_step.

(* Runs of the instrumented model accumulate a trace, hence [lsteps];
   [erased_proph_step] forgets it again for the clients that only need
   reachability. *)

Abbreviation proph_steps := (lsteps proph_step).
Abbreviation erased_proph_step := (erased_lstep proph_step).

Lemma erased_proph_steps_proph_steps c1 c2 :
  rtc erased_proph_step c1 c2 ↔ ∃ n κs, proph_steps n c1 κs c2.
Proof. apply erased_lsteps_lsteps. Qed.

(* Every step of the semantic model is a silent step of the instrumented one,
   on the heap of the store. *)

Lemma threadpool_step_proph_step σ π h' π' :
  threadpool_step (σ.(st_heap), π) (h', π') →
  proph_step (σ, π) [] (store_upd_heap (λ _, h') σ, π').
Proof. apply PureTS. Qed.

(* A pool step that leaves the heap alone leaves the store alone. *)

Lemma PureTS_same σ π π' :
  threadpool_step (σ.(st_heap), π) (σ.(st_heap), π') →
  proph_step (σ, π) [] (σ, π').
Proof.
  intros Hstep. pose proof (PureTS σ π _ π' Hstep) as Ht.
  by rewrite store_upd_heap_id in Ht.
Qed.

From iris.bi Require Import bi.

Ltac destruct_subjective_step :=
  (* For some reason, [dependent destruction] does not like it when
     the argument [x] of [Stop] is not a variable. *)
  try lazymatch goal with
    | h: subjective_step (?σ, Stop ?c ?x ?k, ?π) ?κ ?m' |- _ =>
          remember x
    | h: subjective_step (?σ, stop ?c ?x, ?π) ?κ ?m' |- _ =>
          remember x
    end;
  match goal with h: subjective_step ?m ?κ ?m' |- _ =>
                    dependent destruction h
  end;
  try destruct_step;
  (* We will often conclude that the list of forked threads is empty. *)
  try rewrite bi.sep_emp.


Section reducible.

  Context {Σ : gFunctors}.

(* -------------------------------------------------------------------------- *)

  (* The counterpart of Iris's [reducible e σ]. A join counts as reducible
     as soon as the thread it waits on exists. *)
  Definition reducible {A E} (m : micro A E) σ (π : gset thread) :=
    match m with
    | Stop CJoin ι' k => ι' ∈ π
    | _ => ∃ κ σ' m' (μ : option (thread * microvx)),
      subjective_step (σ, m, π) κ (σ', m', μ)
    end.

  Lemma invert_reducible {A E} m σ π :
    @reducible A E m σ π ->
    ((∃ ι' k, m = Stop CJoin ι' k ∧ ι' ∈ π) ∨
      (∃ v1 v2 k, m = Stop CFork (v1, v2) k) ∨
      (∃ x k, m = Stop CNewProph x k) ∨
      (∃ Y (c : code Y val exn) y k, m = Stop (CResolve c) y k) ∨
      (can_step (σ.(st_heap), m))).
  Proof.
    intros Hcp.
    unfold reducible in Hcp.
    (* Cases on the micro computation. *)
    destruct m;
      (* If that computation is a Stop, destruct the code *)
      try destruct_code;
      (* Generally try to invert Hcp *)
      try (destruct Hcp as (κ & σ' & m' & μ & Hcp);
           dependent destruction Hcp;
           destruct_step; auto with step can_step);
      (* [NewProph] and [Resolve]: one goal per code, all of the same shape. *)
      try solve [do 2 right; left; repeat eexists];
      try solve [do 3 right; left; repeat eexists];
      (* There remains some cases *)
      try solve [(do 4 right; auto with step can_step)].

    (* Only the concurrent [Stop] cases are left. *)
    - right; left. destruct x. repeat eexists.
    - left. repeat eexists. apply Hcp.
  Qed.

  Arguments reducible : simpl never.

  Lemma can_step_reducible {A E} (m : micro A E) σ :
    ∀ π,
      can_step (σ.(st_heap), m) ->
      reducible m σ π.
  Proof.
    intros π ([σ' m'] & Hstep).
    unfold reducible.
    destruct_step;
      do 4 eexists;
      by (eapply BaseS; eauto with step can_step).
    Unshelve. apply b.
  Qed.

  Lemma reducible_fork {A E} σ π x (k : _ -> micro A E) :
    reducible (Stop CFork x k) σ π.
  Proof.
    destruct x.
    unfold reducible.
    do 4 eexists. eapply ForkS.
    apply is_fresh.
  Qed.

  Lemma reducible_new_proph {A E} σ π x (k : _ -> micro A E) :
    reducible (Stop CNewProph x k) σ π.
  Proof.
    unfold reducible.
    do 4 eexists. eapply NewProphS.
    apply is_fresh.
  Qed.

  (* A [Resolve] can progress provided the system call it wraps can step
     and that step lands on an outcome, which is exactly [ResolveS]'s
     [is_result] premise. *)

  Lemma reducible_resolve {A E X} σ π (c : code X val exn) x p v
    (k : outcome2 val exn -> micro A E) :
    can_step (σ.(st_heap), stop c x) ->
    (∀ h' m', step (σ.(st_heap), stop c x) (h', m') ->
       (∃ w, m' = Ret w) ∨ (∃ e, m' = Throw e) ∨ m' = Crash) ->
    reducible (Stop (CResolve c) (x, p, v) k) σ π.
  Proof.
    intros Hcs Hat.
    unfold reducible.
    destruct Hcs as ([σ' m'] & Hstep).
    do 4 eexists. eapply ResolveS; [ exact Hstep | ].
    by destruct (Hat _ _ Hstep) as [(w & ->) | [(e & ->) | ->]].
  Qed.

  Lemma reducible_join {A E} σ π ι' (k : _ -> micro A E) :
    ι' ∈ π ->
    reducible (Stop CJoin ι' k) σ π.
  Proof.
    intros Hπ; simpl.
    unfold reducible.
    assumption.
  Qed.

  Lemma not_reducible_Crash {A E} σ π :
    ¬ @reducible A E Crash σ π.
  Proof.
    unfold reducible. intros (κ & σ' & m' & μ & Hstep).
    dependent destruction Hstep.
    eapply invert_can_step_Crash. eexists. eassumption.
  Qed.

  (* No rule for [Resolve] inspects its continuation, so progress does not
     depend on it. This is what the congruence rules need: [try2] and the
     [Par]/[Handle] float-ups all change only the continuation. *)

  Lemma reducible_resolve_cont {A B E E' X} σ π (c : code X val exn) y
    (k : outcome2 val exn -> micro A E) (k' : outcome2 val exn -> micro B E') :
    reducible (Stop (CResolve c) y k) σ π ->
    reducible (Stop (CResolve c) y k') σ π.
  Proof.
    unfold reducible.
    intros (κ & σ' & m' & μ & Hcp).
    dependent destruction Hcp.
    - exfalso. eapply (no_step_Resolve _ c y k); exact H.
    - do 4 eexists. by eapply ResolveS.
  Qed.

  (* [try2] pushes into continuations, and no rule of [subjective_step] looks
     at a continuation, so progress is preserved by it. *)

  Lemma reducible_try2 {A B E E'} (m : micro A E) σ π
    (f : outcome2 A E -> micro B E') :
    reducible m σ π ->
    reducible (try2 m f) σ π.
  Proof.
    intros Hcp.
    pose proof Hcp as Hcp'.
    apply invert_reducible in Hcp'.
    destruct Hcp' as [ (ι' & k & -> & Hdom)
                     | [ (v1 & v2 & k & ->)
                     | [ (x & k & ->)
                     | [ (Y & c & y & k & ->) | Hcs ] ] ] ].
    - by apply reducible_join.
    - apply reducible_fork.
    - apply reducible_new_proph.
    - (* [try2] only changes the continuation. *)
      simpl try2. cbn match.
      by eapply reducible_resolve_cont.
    - apply can_step_reducible. by apply can_step_try2.
  Qed.

  Lemma inv_reducible_join {A E} σ (π : post_map Σ) ι' (k : _ -> micro A E) :
    reducible (Stop CJoin ι' k) σ (dom π) ->
    ∃ φ, π !! ι' = Some φ.
  Proof.
    intros Hprog; simpl.
    apply (elem_of_dom π ι').
    unfold reducible in Hprog.
    apply Hprog.
  Qed.

  Lemma invert_subjective_step_resume {A E : Type} π (σ σ' : store) κ m' μ (l : loc) (o : outcome2 val exn)
    (k : outcome2 val exn → micro A E)
    (sk : outcome2 val exn → microvx) :
    σ.(st_heap) !! l = Some (Kont sk) →
    subjective_step (σ, Stop CResume (l, o) k, π) κ (σ', m', μ) →
      σ' = store_upd_heap <[l:=Shot]> σ ∧
      m' = try2 (sk o) k ∧
      μ = None.
  Proof.
    intros Hlookup Hstep.
    dependent destruction Hstep.
    destruct_step.
    repeat split; auto.
    - simpl. unfold step_resume_1. rewrite Hlookup. reflexivity.
    - unfold step_resume_2. rewrite Hlookup. reflexivity.
  Qed.

  (* If [m] takes a [subjective_step] to some [m'],
     and [m] can take a sequential step,
     then it took that sequential step which resulted in [m']. *)
  (* A computation that can take a sequential step took one, and a
     sequential step emits nothing and leaves the prophecy identifiers
     alone: only a [NewProph] or a [Resolve] does otherwise, and neither
     has a sequential step. *)
  Lemma invert_can_step_subjective_step {A E} σ π (m : micro A E) m' μ σ' κ :
    subjective_step (σ, m, π) κ (σ', m', μ) ->
    can_step (σ.(st_heap), m) ->
    (∃ h', σ' = store_upd_heap (λ _, h') σ ∧ step (σ.(st_heap), m) (h', m')) ∧
      μ = None ∧ κ = [].
  Proof.
    intros Hwpstep Hstep.
    dependent destruction Hwpstep;
      try solve [ exfalso; eauto with invert_can_step ].
    { split; [ by eexists | done ]. }
    (* The [Resolve] cases are vacuous: a [Resolve] has no [step]. *)
    all: exfalso; eauto with invert_can_step.
  Qed.

  Local Ltac invert_try2 :=
    match goal with
    | h: step (_, try2 _ _) (_, _) |- _ => apply invert_step_try2 in h as (? & ? & ->)
    end.

  Lemma invert_subjective_step_try2 {A B E' E} σ π m m' (k : outcome2 A E' -> micro B E) σ' μ κ :
    subjective_step (σ, (try2 m k), π) κ (σ', m', μ) ->
    can_step (σ.(st_heap), m) ->
    ∃ m'', m' = try2 m'' k ∧ subjective_step (σ, m, π) [] (σ', m'', None).
  Proof.
    intros Hwp Hstep.
    dependent destruction Hwp;
      try solve [ exfalso; eauto with invert_can_step ].
    { apply invert_step_try2 in H; last assumption.
      destruct H as (? & Hstep' & ->).
      eexists; split; [ reflexivity | apply BaseS; assumption ]. }
    (* In the remaining cases ([Fork], [Join] and the three [Resolve]s)
       [try2] pushes into the continuation, so [m] is itself the offending
       [Stop], which cannot step, contradicting [can_step (σ, m)]. *)
    all: symmetry in x;
      apply invert_try2_eq_stop in x as (k' & -> & ->);
        try (intros ? ->);
      exfalso; eauto with invert_can_step.
  Qed.

End reducible.

Global Opaque reducible.

Create HintDb reducible.

Global Hint Resolve
  reducible_join
  reducible_fork
  reducible_new_proph : reducible.

Section Atomicity.

  Context {A X : Type}.
  Implicit Type m : micro A X.

  Inductive is_outcome3 m : Prop :=
  | is_ret a : m = Ret a → is_outcome3 m
  | is_throw e : m = Throw e → is_outcome3 m
  | is_crash : m = Crash → is_outcome3 m.

  Class Atomic m : Prop :=
    atomic :
      ∀ σ π σ' m' μ κ,
      subjective_step (σ, m, π) κ (σ', m', μ) →
      is_outcome3 m'.

End Atomicity.
