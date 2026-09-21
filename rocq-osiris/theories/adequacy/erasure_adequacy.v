From Stdlib Require Import Program.Equality.
From stdpp Require Import gmap.
From iris.proofmode Require Import base ltac_tactics classes.
From osiris.lang Require Import lang.
From osiris.utils.logic Require Import lsteps.
From osiris.semantics Require Import semantics.
From osiris.program_logic Require Import subjective_step ewp.
Require Import ewp_adequacy erasure erasure_eval.

(* -------------------------------------------------------------------------- *)

(** * Erasure of prophecies. *)

(* This file contains the [erasure] theorem. Formally, we state it as:

    erase_store σ σe →
    (* If the annotated program is safe from [σ], and each of its results
       satisfies [Φ] *)
    (∀ k κs σ2 π,
       threadpool_steps k (σ, {[ ι := eval [] e ]}) κs (σ2, π) →
       (∀ ι' m, π !! ι' = Some m → not_stuck m σ2 (dom π)) ∧
       (∀ o, π !! ι = Some (inject2 o) → Φ o)) →
    (* then the program with its annotations removed is safe from [σe], emits
       nothing, and returns the erasure of a result of the annotated one. *)
    (∀ k κs σ2 π,
       threadpool_steps k (σe, {[ ι := eval [] (erase_expr e) ]}) κs (σ2, π) →
       κs = [] ∧
       (∀ ι' m, π !! ι' = Some m → not_stuck m σ2 (dom π)) ∧
       (∀ o, π !! ι = Some (inject2 o) → ∃ o', erase_outcome o' = o ∧ Φ o')).
*)

(* -------------------------------------------------------------------------- *)

(** ** Reachability. *)

Abbreviation proph_steps_one := (lsteps_once proph_step).
Abbreviation proph_steps_trans := (lsteps_trans proph_step).

(* [safe σ π]: any reachable configuration from (σ, π) is safe. *)

Definition safe (σ : store) (π : thpool) : Prop :=
  ∀ σ' π',
    rtc erased_proph_step (σ, π) (σ', π') →
    ∀ ι m, π' !! ι = Some m → not_stuck m σ' (dom π').

Lemma safe_rtc σ π σ' π' :
  safe σ π →
  rtc erased_proph_step (σ, π) (σ', π') →
  safe σ' π'.
Proof.
  intros Hsafe Hrtc σ'' π'' Hrtc' ι m Hm.
  eapply Hsafe; last done. by etrans.
Qed.

Lemma safe_steps σ π n κs σ' π' :
  safe σ π →
  proph_steps n (σ, π) κs (σ', π') →
  safe σ' π'.
Proof.
  intros Hsafe Hsteps. eapply safe_rtc; [ exact Hsafe | ].
  apply erased_proph_steps_proph_steps. by eauto.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma erase_thpool_singleton ι m m' :
  erase_microvx m m' →
  erase_thpool {[ ι := m ]} {[ ι := m' ]}.
Proof.
  intros Hm ι'. unfold erase_thpool, map_relation, thpool.
  destruct (decide (ι = ι')) as [ -> | Hne ].
  - by rewrite !lookup_singleton_eq.
  - by rewrite !lookup_singleton_ne.
Qed.

(* A thread of the erased pool comes from a thread of the annotated one. *)

Lemma erase_thpool_lookup π πe ι me :
  erase_thpool π πe →
  πe !! ι = Some me →
  ∃ m, π !! ι = Some m ∧ erase_microvx m me.
Proof.
  intros Hπ Hme. specialize (Hπ ι). unfold thpool in *.
  rewrite Hme in Hπ.
  destruct (π !! ι) as [ m | ] eqn:Hm; rewrite Hm in Hπ; simpl in Hπ;
    [ by eauto | done ].
Qed.

(* A crashing thread contradicts safety: a crash is stuck. *)

Lemma safe_not_crash σ π ι :
  safe σ π → π !! ι = Some Crash → False.
Proof.
  intros Hsafe Hι.
  destruct (Hsafe σ π (rtc_refl _ _) ι Crash Hι) as [ [] | [ Hcp | [] ] ].
  destruct (subjective_step.invert_reducible _ _ _ Hcp) as [ H | [ H | [ H | H ] ] ];
    try by destruct H as (?&?&?&?).
  - by destruct H as (?&?&?&?&?).
  - by eapply invert_can_step_Crash.
Qed.

(* The annotated thread reaches the corresponding result. It may still have
   to step: the erasure of a resolution attached to a value is that value,
   so the annotated program can be one [CReturn] behind. *)

Local Ltac erase_result_step :=
  match goal with
  | Hsafe : safe ?σ ?π,
    Hι : ?π !! ?ι = Some (Stop (CResolve CReturn) (?w, ?p, ?v) ?k) |- _ =>
      assert (proph_step (σ, π) [(p, (w, v))]
                (σ, <[ ι := continue k w ]> π))
        by (apply (ResolveTS ι π σ σ CReturn w p v (Ret w) k Hι);
            [ exact (StepReturn σ w inject2) | done ])
  | Hsafe : safe ?σ ?π,
    Hι : ?π !! ?ι = Some (Stop CReturn ?w ?k) |- _ =>
      assert (proph_step (σ, π) [] (σ, <[ ι := continue k w ]> π))
        by (apply PureTS;
            apply (BaseTS ι π (Stop CReturn w k) σ (continue k w) σ Hι);
            apply StepReturn)
  end.

(* Having taken that step, the induction hypothesis carries the rest: the
   erased thread is unchanged, only the annotated pool has moved on. *)

Local Ltac erase_not_stuck_finish :=
  match goal with
  | Hstep : proph_step (?σ, ?π) ?κ0 (?σ, <[ ?ι := continue ?k ?w ]> ?π),
    Hsafe : safe ?σ ?π, IH : ∀ _ _, _ → _ → @JMeq _ _ _ _ → _,
    Hm : erase_micro _ _ (continue ?k ?w) ?me |- _ =>
      let Hsafe' := fresh "Hsafe'" in
      assert (Hsafe' : safe σ (<[ ι := continue k w ]> π))
        by (eapply safe_steps; [ exact Hsafe | ];
            econstructor; [ exact Hstep | constructor ]);
      apply (IH (O2Ret w) (continue k w) eq_refl eq_refl JMeq_refl me σ
                (<[ ι := continue k w ]> π) _ _ ι Hsafe'
                ltac:(by rewrite lookup_insert_eq) Hm)
  end.

(* -------------------------------------------------------------------------- *)

(** ** Thread-level steps. *)

(* The steps a thread can take alone (without concurrency): a [step], or a resolution. *)

Inductive tstep {A E} : store * micro A E → list observation → store * micro A E → Prop :=
  | TBase σ m σ' m' :
      step (σ, m) (σ', m') →
      tstep (σ, m) [] (σ', m')
  | TResolve {Y} σ σ' (c : code Y val exn) x p v b k :
      step (σ, stop c x) (σ', b) →
      is_result b →
      tstep (σ, Stop (CResolve c) (x, p, v) k) (resolve_obs p v b)
            (σ', try2 b k)
.

(* Runs of [tstep], sharing the generic labelled-steps machinery with
   [proph_steps] (utils/logic/lsteps.v). *)

Abbreviation tsteps := (lsteps tstep).
Abbreviation tsteps_one := (lsteps_once tstep).
Abbreviation tsteps_trans := (lsteps_trans tstep).

(* A [tstep] can resolve, so it lands in the instrumented model. *)

Lemma tstep_proph_step ι π (c1 c2 : store * microvx) κ :
  π !! ι = Some c1.2 →
  tstep c1 κ c2 →
  proph_step (c1.1, π) κ (c2.1, <[ ι := c2.2 ]> π).
Proof.
  intros Hι Hstep. dependent destruction Hstep; simpl in *.
  - by apply PureTS; eapply BaseTS.
  - by eapply ResolveTS.
Qed.

Lemma tsteps_proph_steps ι n (c1 c2 : store * microvx) κ π :
  π !! ι = Some c1.2 →
  tsteps n c1 κ c2 →
  proph_steps n (c1.1, π) κ (c2.1, <[ ι := c2.2 ]> π).
Proof.
  intros Hι Hsteps. revert π Hι.
  induction Hsteps as [ c | n c1 c2 c3 κ κs Hstep Hsteps IH ]; intros π Hι.
  - unfold thpool in *. rewrite insert_id; [ constructor | done ].
  - econstructor; [ by eapply tstep_proph_step | ].
    unfold thpool, insert_thpool in *.
    rewrite <- (insert_insert_eq π ι c3.2 c2.2).
    apply IH. by rewrite lookup_insert_eq.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Stuck threads. *)

Definition is_result {A E} (m : micro A E) : Prop :=
  match m with
  | Ret _ | Throw _ | Crash => True
  | _ => False
  end.

Definition steppable_code {X Y E} (c : code X Y E) : Prop :=
  match c with CPerf | CResolve _ => False | _ => True end.

Lemma not_steppable_step_through_par {X Y E} (c : code X Y E) :
  ¬ steppable_code c → step_through_par_code c.
Proof. destruct c; simpl; tauto. Qed.

Lemma not_stuck_call {A E X Y} σ (π : gset thread) (c : code X Y exn) x
    (k : outcome2 Y exn → micro A E) :
  steppable_code c →
  not_stuck (Stop c x k) σ π.
Proof.
  intros Hc. destruct c; try done;
    try (right; left;
         apply subjective_step.can_step_reducible, can_step_stop;
         split; [ done | by intros [] ]).
  - (* a fork makes progress by creating a thread *)
    right; left. by apply subjective_step.reducible_fork.
  - (* a join is waiting *)
    by right; right.
Qed.

Lemma not_stuck_call_code {A E X Y} σ (π : gset thread) (c : code X Y exn) x
    (k : outcome2 Y exn → micro A E) :
  no_proph_code c →
  not_stuck (Stop c x k) σ π →
  steppable_code c.
Proof.
  intros Hc [ [] | [ Hcp | Hj ] ]; last by destruct c.
  destruct c; try done.
  (* [perform] does not step, and no rule of [subjective_step] applies to it. *)
  destruct Hcp as (κ & σ' & m' & μ & Hts).
  by dependent destruction Hts; destruct_step.
Qed.

(* A call that steps is one of the codes that step. *)

Lemma step_stop_steppable {X Y} σ σ' (c : code X Y exn) x (b : micro Y exn) :
  step (σ, stop c x) (σ', b) →
  steppable_code c.
Proof. intros Hstep. by destruct_step. Qed.

Lemma not_stuck_resolve_code {A E X} σ (π : gset thread) (c : code X val exn)
    x p v (k : outcome2 val exn → micro A E) :
  no_proph_code c →
  not_stuck (Stop (CResolve c) (x, p, v) k) σ π →
  steppable_code c.
Proof.
  intros Hc [ [] | [ Hcp | [] ] ].
  destruct Hcp as (κ & σ' & m' & μ & Hts).
  (* The resolution steps only if the call it wraps does. *)
  dependent destruction Hts; first destruct_step;
    by eapply step_stop_steppable.
Qed.

Definition mstuck {A E} σ (m : micro A E) : Prop :=
  m = Crash ∨
  ∃ X (c : code X val exn) x p v (k : outcome2 val exn → micro A E),
    m = Stop (CResolve c) (x, p, v) k ∧
    ∀ σ' b, step (σ, stop c x) (σ', b) → ¬ is_result b.

(* -------------------------------------------------------------------------- *)

(** ** A call and the call it wraps. *)

(* A call applies its continuation without inspecting it (the algebraicity of
   [try2_step_load_2] and siblings), so a step of [Stop c x k] is a step of
   [stop c x] with [k] plugged in after. Both directions are needed: taking
   the erased step apart, and putting the annotated one back together. *)

Lemma step_stop_join {A E X Y} σ (c : code X Y exn) x
    (k : outcome2 Y exn → micro A E) σ' b :
  step (σ, stop c x) (σ', b) →
  step (σ, Stop c x k) (σ', try2 b k).
Proof. intros. rewrite <- (try2_stop c x k). by apply step_try2. Qed.

Lemma step_stop_split {A E X Y} σ (c : code X Y exn) x
    (k : outcome2 Y exn → micro A E) σ' m' :
  step (σ, Stop c x k) (σ', m') →
  ∃ b, step (σ, stop c x) (σ', b) ∧ m' = try2 b k.
Proof.
  intros Hstep.
  destruct_step; eexists; (split; [ solve [ econstructor; eauto ] | ]).
  (* What is left of each case is the algebraicity equation: the bare call
     applies [inject2] where the call with a continuation applies [k]. *)
  all: rewrite ?try2_inject2_right;
       unfold step_load_2, step_load_block_2, step_exchange_2, step_set_tag_2,
              step_cas_2, step_faa_2, step_resume_2, step_wrap_2;
       repeat case_match; simplify_eq; try reflexivity.
  (* [resume] runs the stored continuation, which is itself a computation. *)
  by rewrite try2_inject2_right.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Stores. *)

(* Erasure neither allocates nor moves anything, so the two stores have the
   same domain and agree cell by cell. *)

Lemma erase_store_lookup σ σe l b :
  erase_store σ σe →
  σ !! l = Some b →
  ∃ be, σe !! l = Some be ∧ erase_mem_block b be.
Proof.
  intros Hσ Hl. specialize (Hσ l). unfold store in *. rewrite Hl in Hσ.
  destruct (σe !! l) as [ be | ]; [ by eauto | done ].
Qed.

Lemma erase_store_lookup_erased σ σe l be :
  erase_store σ σe →
  σe !! l = Some be →
  ∃ b, σ !! l = Some b ∧ erase_mem_block b be.
Proof.
  intros Hσ Hl. specialize (Hσ l). unfold store in *. rewrite Hl in Hσ.
  destruct (σ !! l) as [ b | ]; [ by eauto | done ].
Qed.

Lemma erase_store_none σ σe l :
  erase_store σ σe →
  σe !! l = None →
  σ !! l = None.
Proof.
  intros Hσ Hl. specialize (Hσ l). unfold store in *. rewrite Hl in Hσ.
  by destruct (σ !! l) as [ b | ].
Qed.

Lemma erase_store_insert σ σe l b be :
  erase_store σ σe →
  erase_mem_block b be →
  erase_store (<[ l := b ]> σ) (<[ l := be ]> σe).
Proof.
  intros Hσ Hb i. unfold store in *.
  destruct (decide (l = i)) as [ -> | Hne ].
  - by rewrite !lookup_insert_eq.
  - rewrite !lookup_insert_ne //; try apply Hσ.
Qed.

(* Physical equality inspects locations, continuations, constant
   constructors and the tag of a block, never a value that erasure
   rewrites. So the two programs compare alike, with no side condition;
   HeapLang needs [vals_compare_safe] here. *)

Lemma erase_phys_eq_blocks σ σe l1 l2 :
  erase_store σ σe →
  match σe !! l1, σe !! l2 with
  | Some (Block Mut _), Some (Block _ _)
  | Some (Block _ _), Some (Block Mut _) => Some (locations.eqb l1 l2)
  | _, _ => None
  end
  = match σ !! l1, σ !! l2 with
    | Some (Block Mut _), Some (Block _ _)
    | Some (Block _ _), Some (Block Mut _) => Some (locations.eqb l1 l2)
    | _, _ => None
    end.
Proof.
  intros Hσ. pose proof (Hσ l1) as H1. pose proof (Hσ l2) as H2.
  destruct (σ !! l1) as [ [ ] | ] eqn:E1, (σe !! l1) as [ [ ] | ] eqn:E2,
           (σ !! l2) as [ [ ] | ] eqn:E3, (σe !! l2) as [ [ ] | ] eqn:E4;
    rewrite ?E1 ?E2 ?E3 ?E4 in H1 H2;
    simpl in H1, H2; destruct_and?; simplify_eq; try done;
    by repeat case_match.
Qed.

(* Only one way: a prophecy and a location do not compare, but their
   erasures, two locations, do. *)

Lemma erase_phys_eq_val_store σ σe v1 v2 b :
  erase_store σ σe →
  phys_eq_val_store v1 v2 σ = Some b →
  phys_eq_val_store (erase_val v1) (erase_val v2) σe = Some b.
Proof.
  intros Hσ Hb. destruct v1, v2;
    repeat (match goal with
            | |- context [ VData ?c ?l ] => is_var l; destruct l
            end);
    simpl in *; try done.
  (* What is left is the block comparison, which reads the two blocks' tags
     out of the store. *)
  all: by rewrite (erase_phys_eq_blocks σ σe).
Qed.

(* -------------------------------------------------------------------------- *)

(** ** The store operations. *)

Local Ltac erase_op l :=
  let H1 := fresh "H1" in
  let H2 := fresh "H2" in
  let Hl := fresh "Hl" in
  match goal with
  | H : erase_store ?σ ?σe |- _ =>
      pose proof (H l) as Hl;
      destruct (σ !! l) as [ [ | | | ] | ] eqn:H1,
               (σe !! l) as [ [ | | | ] | ] eqn:H2;
      rewrite ?H1 ?H2 in Hl
  end;
  simpl in Hl; try done; destruct_and?; subst; simpl.

Lemma erase_step_load_2 σ σe l :
  erase_store σ σe →
  erase_microvx (step_load_2 σ l inject2) (step_load_2 σe l inject2).
Proof.
  intros Hσ. unfold step_load_2. erase_op l;
    first [ apply EM_Crash | exact (EM_Ret erase_val erase_val _) ].
Qed.

Lemma erase_step_load_block_2 σ σe l :
  erase_store σ σe →
  erase_micro id erase_val
    (step_load_block_2 σ l inject2) (step_load_block_2 σe l inject2).
Proof.
  intros Hσ. unfold step_load_block_2. erase_op l;
    first [ apply EM_Crash | exact (EM_Ret id erase_val _) ].
Qed.

Lemma erase_step_exchange_1 σ σe l v :
  erase_store σ σe →
  erase_store (step_exchange_1 σ l v) (step_exchange_1 σe l (erase_val v)).
Proof.
  intros Hσ. unfold step_exchange_1. erase_op l;
    first [ by apply erase_store_insert | done ].
Qed.

Lemma erase_step_exchange_2 σ σe l :
  erase_store σ σe →
  erase_microvx (step_exchange_2 σ l inject2) (step_exchange_2 σe l inject2).
Proof.
  intros Hσ. unfold step_exchange_2. erase_op l;
    first [ apply EM_Crash | exact (EM_Ret erase_val erase_val _) ].
Qed.

Lemma erase_step_set_tag_1 σ σe l t :
  erase_store σ σe →
  erase_store (step_set_tag_1 σ l t) (step_set_tag_1 σe l t).
Proof.
  intros Hσ. unfold step_set_tag_1. erase_op l;
    first [ by apply erase_store_insert | done ].
Qed.

Lemma erase_step_set_tag_2 σ σe l :
  erase_store σ σe →
  erase_micro id erase_val
    (step_set_tag_2 σ l inject2) (step_set_tag_2 σe l inject2).
Proof.
  intros Hσ. unfold step_set_tag_2. erase_op l;
    first [ apply EM_Crash | exact (EM_Ret id erase_val _) ].
Qed.

(* Compare-and-set first compares. Where the annotated program can compare,
   the erased one compares alike. Where it cannot (a prophecy against a
   location), it crashes, and the erased program may go on to write: the
   stores are then no longer related, which the crash makes moot. *)

Lemma erase_step_cas σ σe l seen v :
  erase_store σ σe →
  step_cas_2 σ l seen v inject2 = Crash
  ∨ (erase_store (step_cas_1 σ l seen v)
                 (step_cas_1 σe l (erase_val seen) (erase_val v))
     ∧ erase_microvx (step_cas_2 σ l seen v inject2)
                     (step_cas_2 σe l (erase_val seen) (erase_val v) inject2)).
Proof.
  intros Hσ. unfold step_cas_1, step_cas_2. erase_op l;
    try (right; split; [ done | apply EM_Crash ]).
  destruct (phys_eq_val_store _ seen σ) as [ b | ] eqn:Hb; [ | by left ].
  rewrite (erase_phys_eq_val_store σ σe _ _ b Hσ Hb). right.
  destruct b; (split; [ by apply erase_store_insert || done | ]);
    exact (EM_Ret erase_val erase_val _).
Qed.

(* Fetch-and-add insists on an integer, which erasure leaves alone. *)

Lemma erase_step_faa_1 σ σe l i :
  erase_store σ σe →
  erase_store (step_faa_1 σ l i) (step_faa_1 σe l i).
Proof.
  intros Hσ. unfold step_faa_1. erase_op l;
    try (match goal with v : val |- _ => destruct v end; simpl);
    first [ by apply erase_store_insert | done ].
Qed.

Lemma erase_step_faa_2 σ σe l i :
  erase_store σ σe →
  erase_microvx (step_faa_2 σ l i inject2) (step_faa_2 σe l i inject2).
Proof.
  intros Hσ. unfold step_faa_2. erase_op l;
    try (match goal with v : val |- _ => destruct v end; simpl);
    first [ apply EM_Crash | exact (EM_Ret erase_val erase_val _) ].
Qed.

Lemma erase_step_resume_1 σ σe l :
  erase_store σ σe →
  erase_store (step_resume_1 σ l) (step_resume_1 σe l).
Proof.
  intros Hσ. unfold step_resume_1. erase_op l;
    first [ by apply erase_store_insert | done ].
Qed.

Lemma erase_step_resume_2 σ σe l o :
  erase_store σ σe →
  erase_microvx (step_resume_2 σ l o inject2)
             (step_resume_2 σe l (erase_outcome o) inject2).
Proof.
  intros Hσ. unfold step_resume_2. erase_op l;
    (* the stored continuation is related pointwise, and running it under
       [inject2] preserves that *)
    first [ apply EM_Crash | done
          | eapply erase_try2; [ done | intros o'; apply erase_inject2 ] ].
Qed.

(* [wrap] stores a continuation that re-installs the handler; the two
   programs store the same thing up to erasure. *)

Lemma erase_step_wrap_1 σ σe l η bs l' :
  erase_store σ σe →
  erase_store (step_wrap_1 σ l η bs l')
              (step_wrap_1 σe l (erase_env η) (erase_branches bs) l').
Proof.
  intros Hσ. unfold step_wrap_1. apply erase_store_insert; [ done | ].
  intros o. eapply EM_Handle.
  - apply (erase_stop CResume (l, o)). done.
  - intros o3. apply erase_wrap_eval_branches.
Qed.

Lemma erase_step_shallow_wrap_1 σ σe l η bs l' :
  erase_store σ σe →
  erase_store (step_shallow_wrap_1 σ l η bs l')
              (step_shallow_wrap_1 σe l (erase_env η) (erase_branches bs) l').
Proof.
  intros Hσ. unfold step_shallow_wrap_1. apply erase_store_insert; [ done | ].
  intros o. eapply EM_Handle.
  - apply (erase_stop CResume (l, o)). done.
  - intros o3. apply erase_shallow_eval_branches.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** The step of a call. *)

(* Where the erasure of a system call is checked against the semantics, one
   code at a time. The only place the proof looks at the store. *)

Lemma erase_step_call {X Y} (c : code X Y exn) x σ σe σe' (be : micro Y exn) :
  no_proph_code c →
  erase_store σ σe →
  step (σe, stop c (erase_code_arg c x)) (σe', be) →
  ∃ σ' b,
    step (σ, stop c x) (σ', b) ∧
    (b = Crash ∨
     erase_store σ' σe' ∧ erase_micro (erase_code_res c) erase_val b be).
Proof.
  intros Hc Hσ Hstep.
  dependent destruction c; try done; simpl in *.
  (* Each code takes its own step, and the erased one fixes which. *)
  all: destruct_pairs x; simpl in *; destruct_step; simpl in *.
  (* The annotated program takes the same step, at the same location and
     with the same Boolean where there is a choice. *)
  all: eexists; eexists; split;
       [ solve [ econstructor; eauto using erase_store_none ] | ].
  (* Only compare-and-set can crash where its erasure does not. *)
  all: first [ by apply erase_step_cas | right; split ].
  (* What is left is one store relation and one computation relation per
     code, which is what the lemmas above are for. *)
  (* [CEval] and [CLoop] hand over a computation of their own. *)
  - exact Hσ.
  - rewrite !try2_inject2_right; apply erase_eval.
  - exact Hσ.
  - rewrite !try2_inject2_right; apply erase_loop_body.
  (* [CFlip] returns the same Boolean, [CAlloc] and [CAllocBlock] the
     location they have just allocated. *)
  - exact Hσ.
  - exact (EM_Ret id erase_val b).
  - by apply erase_store_insert.
  - exact (EM_Ret id erase_val l).
  - by apply erase_store_insert.
  - exact (EM_Ret id erase_val l0).
  (* The reads leave the store alone. *)
  - exact Hσ.
  - by apply erase_step_load_2.
  - exact Hσ.
  - by apply erase_step_load_block_2.
  (* Interactions with the store. *)
  - by apply erase_step_exchange_1.
  - by apply erase_step_exchange_2.
  - by apply erase_step_set_tag_1.
  - by apply erase_step_set_tag_2.
  - by apply erase_step_faa_1.
  - by apply erase_step_faa_2.
  - by apply erase_step_resume_1.
  - by apply erase_step_resume_2.
  (* [CWrap], deep then shallow: the continuation is allocated and its
     location returned. *)
  - by apply erase_step_wrap_1.
  - exact (EM_Ret id erase_val l').
  - by apply erase_step_shallow_wrap_1.
  - exact (EM_Ret id erase_val l').
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Contexts. *)

(* A thread that can run into something stuck: how every failing case of the
   backward simulation reports itself. This corresponsd to Iris'
   [prim_step_matched_by_erased_steps]. *)

Definition reaches_stuck {A E} σ (m : micro A E) : Prop :=
  ∃ n κ σ' m', tsteps n (σ, m) κ (σ', m') ∧ mstuck σ' m'.

Lemma reaches_stuck_steps {A E} n σ (m : micro A E) κ σ' m' :
  tsteps n (σ, m) κ (σ', m') → mstuck σ' m' → reaches_stuck σ m.
Proof. intros. by exists n, κ, σ', m'. Qed.

Lemma reaches_stuck_now {A E} σ (m : micro A E) :
  mstuck σ m → reaches_stuck σ m.
Proof. exists 0, [], σ, m. split; [ constructor | done ]. Qed.

Lemma reaches_stuck_after {A E} n σ (m : micro A E) κ σ' m' :
  tsteps n (σ, m) κ (σ', m') → reaches_stuck σ' m' → reaches_stuck σ m.
Proof.
  intros Hs (n2 & κ2 & σ2 & m2 & Hs2 & Hst).
  exists (n + n2), (κ ++ κ2), σ2, m2. split; [ by eapply tsteps_trans | done ].
Qed.

(* A thread's steps drive the same thread under a [Handle] or in a branch of
   a [Par]. *)

(* The three lemmas differ only in the context [C] and in two step rules: one
   for an ordinary step, one to float a resolution out to the top of the
   thread. *)

(* A context commutes with a resolved outcome: both sides are [C (k o)]. *)

Lemma try2_inject2_frame {A E B F} (C : micro A E → micro B F)
    (o : outcome2 val exn) (k : outcome2 val exn → micro A E) :
  C (try2 (inject2 o) k) = try2 (inject2 o) (λ o', C (k o')).
Proof. by rewrite !try2_inject2. Qed.

Lemma tstep_frame {A E B F} (C : micro A E → micro B F) σ m κ σ' m' :
  (∀ σ1 m1 σ2 m2, step (σ1, m1) (σ2, m2) → step (σ1, C m1) (σ2, C m2)) →
  (∀ X σ1 (c : code X val exn) y k,
     step (σ1, C (Stop (CResolve c) y k))
          (σ1, Stop (CResolve c) y (λ o, C (k o)))) →
  tstep (σ, m) κ (σ', m') →
  (∃ n, tsteps n (σ, C m) κ (σ', C m'))
  ∨ (∃ n, tsteps n (σ, C m) κ (σ', Crash) ∧ mstuck σ' (Crash : micro B F)).
Proof.
  intros Hbase Hthrough Hstep. dependent destruction Hstep.
  - left. exists 1. apply tsteps_one, TBase. by apply Hbase.
  (* The resolution floats to the top of the thread and resolves there. The
     context survives a returned or a thrown outcome, but not a crash, which
     [try2] propagates in place of [C Crash]. *)
  - destruct_is_result o.
    + left. exists 2.
      eapply (lsteps_l _ 1 _ _ _ []); [ apply TBase, Hthrough | ].
      apply tsteps_one. rewrite try2_inject2_frame.
      exact (TResolve σ σ' c x p v (inject2 o) (λ o, C (k o)) H H0).
    + right. exists 2. split; [ | by left ].
      eapply (lsteps_l _ 1 _ _ _ []); [ apply TBase, Hthrough | ].
      apply tsteps_one.
      exact (TResolve σ σ' c x p v Crash (λ o, C (k o)) H H0).
Qed.

Lemma tstep_handle {A E} σ (m : microvx) κ σ' m'
    (h : _ → micro A E) :
  tstep (σ, m) κ (σ', m') →
  (∃ n, tsteps n (σ, Handle m h) κ (σ', Handle m' h))
  ∨ (∃ n, tsteps n (σ, Handle m h) κ (σ', Crash) ∧ mstuck σ' (Crash : micro A E)).
Proof.
  intros Hs. eapply (tstep_frame (λ m, Handle m h)); [ | | exact Hs ].
  - intros. by apply StepHandleLeft.
  - intros. by apply StepHandleResolve.
Qed.

(* Only lifting a single step depends on the context; lifting a whole run
   does not. This is the latter, once, over any [C]. *)

Lemma tsteps_frame {A E B F} (C : micro A E → micro B F) n σ m κ σ' m' :
  (∀ σ1 m1 κ1 σ2 m2,
     tstep (σ1, m1) κ1 (σ2, m2) →
     (∃ j, tsteps j (σ1, C m1) κ1 (σ2, C m2))
     ∨ (∃ j, tsteps j (σ1, C m1) κ1 (σ2, Crash) ∧ mstuck σ2 (Crash : micro B F))) →
  tsteps n (σ, m) κ (σ', m') →
  (∃ n', tsteps n' (σ, C m) κ (σ', C m')) ∨ reaches_stuck σ (C m).
Proof.
  intros HC.
  remember (σ, m) as c1 eqn:Hc1. remember (σ', m') as c2 eqn:Hc2.
  intros Hsteps. revert σ m σ' m' Hc1 Hc2.
  induction Hsteps as [ c | n c1 c2 c3 κ1 κs Hstep Hsteps IH ];
    intros σ m σ' m' -> Hc2.
  - injection Hc2 as -> ->. left. exists 0. constructor.
  - destruct c2 as (σ1, m1).
    destruct (HC σ m κ1 σ1 m1 Hstep) as [ [ n1 H1 ] | [ n1 [ H1 H2 ] ] ].
    + destruct (IH σ1 m1 σ' m' eq_refl Hc2) as [ [ n2 H3 ] | H3 ].
      * left. exists (n1 + n2). by eapply tsteps_trans.
      * right. by eapply reaches_stuck_after.
    + right. by eapply reaches_stuck_steps.
Qed.

Lemma tsteps_handle {A E} n σ (m : microvx) κ σ' m'
    (h : _ → micro A E) :
  tsteps n (σ, m) κ (σ', m') →
  (∃ n', tsteps n' (σ, Handle m h) κ (σ', Handle m' h))
  ∨ reaches_stuck σ (Handle m h).
Proof.
  intros Hs. eapply (tsteps_frame (λ m, Handle m h)); [ | exact Hs ].
  intros. by apply tstep_handle.
Qed.

Lemma tstep_par_l {A1 A2 A E E'} σ (m1 : micro A1 E') m1' κ σ' m2
    (k : outcome2 (A1 * A2) E' → micro A E) :
  tstep (σ, m1) κ (σ', m1') →
  (∃ n, tsteps n (σ, Par m1 m2 k) κ (σ', Par m1' m2 k))
  ∨ (∃ n, tsteps n (σ, Par m1 m2 k) κ (σ', Crash) ∧ mstuck σ' (Crash : micro A E)).
Proof.
  intros Hs. eapply (tstep_frame (λ m1, Par m1 m2 k)); [ | | exact Hs ].
  - intros. by apply StepParLeft.
  - intros. apply StepThroughParLeft. done.
Qed.

Lemma tstep_par_r {A1 A2 A E E'} σ (m2 : micro A2 E') m2' κ σ' m1
    (k : outcome2 (A1 * A2) E' → micro A E) :
  tstep (σ, m2) κ (σ', m2') →
  (∃ n, tsteps n (σ, Par m1 m2 k) κ (σ', Par m1 m2' k))
  ∨ (∃ n, tsteps n (σ, Par m1 m2 k) κ (σ', Crash) ∧ mstuck σ' (Crash : micro A E)).
Proof.
  intros Hs. eapply (tstep_frame (λ m2, Par m1 m2 k)); [ | | exact Hs ].
  - intros. by apply StepParRight.
  - intros. apply StepThroughParRight. done.
Qed.

Lemma tsteps_par_l {A1 A2 A E E'} n σ (m1 : micro A1 E') κ σ' m1' m2
    (k : outcome2 (A1 * A2) E' → micro A E) :
  tsteps n (σ, m1) κ (σ', m1') →
  (∃ n', tsteps n' (σ, Par m1 m2 k) κ (σ', Par m1' m2 k))
  ∨ reaches_stuck σ (Par m1 m2 k).
Proof.
  intros Hs. eapply (tsteps_frame (λ m1, Par m1 m2 k)); [ | exact Hs ].
  intros. by apply tstep_par_l.
Qed.

Lemma tsteps_par_r {A1 A2 A E E'} n σ (m2 : micro A2 E') κ σ' m2' m1
    (k : outcome2 (A1 * A2) E' → micro A E) :
  tsteps n (σ, m2) κ (σ', m2') →
  (∃ n', tsteps n' (σ, Par m1 m2 k) κ (σ', Par m1 m2' k))
  ∨ reaches_stuck σ (Par m1 m2 k).
Proof.
  intros Hs. eapply (tsteps_frame (λ m2, Par m1 m2 k)); [ | exact Hs ].
  intros. by apply tstep_par_r.
Qed.

Lemma mstuck_frame {A E B F} (C : micro A E → micro B F) σ m :
  step (σ, C Crash) (σ, Crash) →
  (∀ X σ1 (c : code X val exn) y k,
     step (σ1, C (Stop (CResolve c) y k))
          (σ1, Stop (CResolve c) y (λ o, C (k o)))) →
  mstuck σ m → reaches_stuck σ (C m).
Proof.
  intros Hcrash Hthrough [ -> | (X & c & x & p & v & k & -> & Hc) ].
  - exists 1, [], σ, Crash. split; [ | by left ].
    by apply tsteps_one, TBase.
  - exists 1, [], σ, (Stop (CResolve c) (x, p, v) (λ o, C (k o))).
    split; [ by apply tsteps_one, TBase | ].
    right. by exists X, c, x, p, v, (λ o, C (k o)).
Qed.

Lemma mstuck_handle {A E} σ (m : microvx) (h : _ → micro A E) :
  mstuck σ m → reaches_stuck σ (Handle m h).
Proof.
  apply (mstuck_frame (λ m, Handle m h)).
  - by apply StepHandleCrash.
  - intros. by apply StepHandleResolve.
Qed.

Lemma mstuck_par_l {A1 A2 A E E'} σ (m1 : micro A1 E') m2
    (k : outcome2 (A1 * A2) E' → micro A E) :
  mstuck σ m1 → reaches_stuck σ (Par m1 m2 k).
Proof.
  apply (mstuck_frame (λ m1, Par m1 m2 k)).
  - by apply StepParCrashLeft.
  - intros. apply StepThroughParLeft. done.
Qed.

Lemma mstuck_par_r {A1 A2 A E E'} σ (m2 : micro A2 E') m1
    (k : outcome2 (A1 * A2) E' → micro A E) :
  mstuck σ m2 → reaches_stuck σ (Par m1 m2 k).
Proof.
  apply (mstuck_frame (λ m2, Par m1 m2 k)).
  - by apply StepParCrashRight.
  - intros. apply StepThroughParRight. done.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Stripping the calls erasure removes. *)

(* [CReturn], and the resolution attached to a value that compiles to it,
   are the only nodes the annotated program has and the erased one does not.
   Stepping them away is what makes the two computations line up, and causes
   a stutter that the simulation has to absorb. *)

(* A [CResolve] is a stutter exactly when the call it wraps is a [CReturn]. *)

Definition stutter_code {X Y E} (c : code X Y E) : Prop :=
  match c with
  | CReturn => True
  | CResolve c' => ¬ no_proph_code c'
  | _ => False
  end.

Definition no_stutter {A E} (m : micro A E) : Prop :=
  match m with Stop c _ _ => ¬ stutter_code c | _ => True end.

Lemma no_proph_no_stutter {X Y E} (c : code X Y E) :
  no_proph_code c → ¬ stutter_code c.
Proof. destruct c; simpl; tauto. Qed.

Lemma no_proph_resolve_no_stutter {X} (c : code X val exn) :
  no_proph_code c → ¬ stutter_code (CResolve c).
Proof. simpl. tauto. Qed.

(* The two stutter steps themselves. Both leave the store alone; the
   resolution emits its observation, the bare [CReturn] emits none. *)

Lemma tstep_return {A E} σ w (k : outcome2 val exn → micro A E) :
  tstep (σ, Stop CReturn w k) [] (σ, continue k w).
Proof. apply TBase, StepReturn. Qed.

Lemma tstep_resolve_return {A E} σ w p v (k : outcome2 val exn → micro A E) :
  tstep (σ, Stop (CResolve CReturn) (w, p, v) k) [(p, (w, v))]
        (σ, continue k w).
Proof. exact (TResolve σ σ CReturn w p v (Ret w) k (StepReturn σ w inject2) I). Qed.

Lemma erase_unstutter {A E} (fA : A → A) (fE : E → E) ma me σ :
  erase_micro fA fE ma me →
  reaches_stuck σ ma
  ∨ (∃ n κ ma0, tsteps n (σ, ma) κ (σ, ma0) ∧
                erase_micro fA fE ma0 me ∧ no_stutter ma0).
Proof.
  intros Hm. induction Hm.
  (* Everything but the two calls erasure removes is already in shape. *)
  - right. exists 0, [], (Ret a). split; [ constructor | ]. by split; [ apply EM_Ret | ].
  - right. exists 0, [], (Throw e). split; [ constructor | ]. by split; [ apply EM_Throw | ].
  - right. exists 0, [], Crash. split; [ constructor | ]. by split; [ apply EM_CrashL | ].
  - right. exists 0, [], (Handle m h). split; [ constructor | ].
    by split; [ apply EM_Handle | ].
  - right. exists 0, [], (Stop c x k). split; [ constructor | ].
    split; [ by apply EM_Stop | ]. by apply no_proph_no_stutter.
  - right. exists 0, [], (Stop CNewProph x k). split; [ constructor | ].
    split; [ by apply EM_NewProph | by intros [] ].
  - right. exists 0, [], (Stop (CResolve c) (x, p, v) k). split; [ constructor | ].
    split; [ by apply EM_Resolve | ]. by apply no_proph_resolve_no_stutter.
  (* A resolution attached to a value: it steps, and the store is unchanged. *)
  - destruct IHHm as [ Hstuck | (n & κ & ma0 & Hsteps & Hma0 & Hns) ].
    + left. eapply reaches_stuck_after; [ | exact Hstuck ].
      by apply tsteps_one, tstep_resolve_return.
    + right. exists (S n), ([(p, (w, v))] ++ κ), ma0. split; [ | done ].
      econstructor; [ apply tstep_resolve_return | exact Hsteps ].
  (* The [CReturn] it compiles to. *)
  - destruct IHHm as [ Hstuck | (n & κ & ma0 & Hsteps & Hma0 & Hns) ].
    + left. eapply reaches_stuck_after; [ | exact Hstuck ].
      by apply tsteps_one, tstep_return.
    + right. exists (S n), ([] ++ κ), ma0. split; [ | done ].
      econstructor; [ apply tstep_return | exact Hsteps ].
  - right. exists 0, [], (Par m1 m2 k). split; [ constructor | ].
    split; [ | done ]. by eapply EM_Par.
Qed.

(* Stripping the stutter inside a context, which is how the [Handle] and
   [Par] cases of the simulation start: either the annotated thread runs into
   something stuck, or it reaches the same context around a computation under
   the erasure relation. *)

Lemma mstuck_under_handle {A E} σ (m : microvx) (h : _ → micro A E) :
  reaches_stuck σ m → reaches_stuck σ (Handle m h).
Proof.
  intros (n & κ & σ' & m0 & Hs & Hst).
  destruct (tsteps_handle n σ m κ σ' m0 h Hs)
    as [ [ n' H ] | H ]; last done.
  eapply reaches_stuck_after; [ exact H | by apply mstuck_handle ].
Qed.

Lemma mstuck_under_par_l {A1 A2 A E E'} σ (m1 : micro A1 E') m2
    (k : outcome2 (A1 * A2) E' → micro A E) :
  reaches_stuck σ m1 → reaches_stuck σ (Par m1 m2 k).
Proof.
  intros (n & κ & σ' & m0 & Hs & Hst).
  destruct (tsteps_par_l n σ m1 κ σ' m0 m2 k Hs)
    as [ [ n' H ] | H ]; last done.
  eapply reaches_stuck_after; [ exact H | by apply mstuck_par_l ].
Qed.

Lemma mstuck_under_par_r {A1 A2 A E E'} σ (m2 : micro A2 E') m1
    (k : outcome2 (A1 * A2) E' → micro A E) :
  reaches_stuck σ m2 → reaches_stuck σ (Par m1 m2 k).
Proof.
  intros (n & κ & σ' & m0 & Hs & Hst).
  destruct (tsteps_par_r n σ m2 κ σ' m0 m1 k Hs)
    as [ [ n' H ] | H ]; last done.
  eapply reaches_stuck_after; [ exact H | by apply mstuck_par_r ].
Qed.

Lemma handle_unstutter {A E} σ (m m' : microvx) (h : _ → micro A E) :
  erase_microvx m m' →
  reaches_stuck σ (Handle m h)
  ∨ (∃ n κ m0, tsteps n (σ, Handle m h) κ (σ, Handle m0 h) ∧
               erase_microvx m0 m' ∧ no_stutter m0).
Proof.
  intros Hm.
  destruct (erase_unstutter erase_val erase_val m m' σ Hm)
    as [ Hst | (n & κ & m0 & Hs & Hm0 & Hns) ].
  - left. by apply mstuck_under_handle.
  - destruct (tsteps_handle n σ m κ σ m0 h Hs)
      as [ [ n' H ] | H ]; last by left.
    right. by exists n', κ, m0.
Qed.

Lemma par_l_unstutter {A1 A2 A E E'} σ (m1 m1' : micro A1 E') f1 fE' m2
    (k : outcome2 (A1 * A2) E' → micro A E) :
  erase_micro f1 fE' m1 m1' →
  reaches_stuck σ (Par m1 m2 k)
  ∨ (∃ n κ m0, tsteps n (σ, Par m1 m2 k) κ (σ, Par m0 m2 k) ∧
               erase_micro f1 fE' m0 m1' ∧ no_stutter m0).
Proof.
  intros Hm.
  destruct (erase_unstutter f1 fE' m1 m1' σ Hm)
    as [ Hst | (n & κ & m0 & Hs & Hm0 & Hns) ].
  - left. by apply mstuck_under_par_l.
  - destruct (tsteps_par_l n σ m1 κ σ m0 m2 k Hs)
      as [ [ n' H ] | H ]; last by left.
    right. by exists n', κ, m0.
Qed.

Lemma par_r_unstutter {A1 A2 A E E'} σ (m2 m2' : micro A2 E') f2 fE' m1
    (k : outcome2 (A1 * A2) E' → micro A E) :
  erase_micro f2 fE' m2 m2' →
  reaches_stuck σ (Par m1 m2 k)
  ∨ (∃ n κ m0, tsteps n (σ, Par m1 m2 k) κ (σ, Par m1 m0 k) ∧
               erase_micro f2 fE' m0 m2' ∧ no_stutter m0).
Proof.
  intros Hm.
  destruct (erase_unstutter f2 fE' m2 m2' σ Hm)
    as [ Hst | (n & κ & m0 & Hs & Hm0 & Hns) ].
  - left. by apply mstuck_under_par_r.
  - destruct (tsteps_par_r n σ m2 κ σ m0 m1 k Hs)
      as [ [ n' H ] | H ]; last by left.
    right. by exists n', κ, m0.
Qed.

(* Two calls of the same code, at the same store, agree on whether they
   produce an outcome. *)

(* The calls that float out of a [Par] are exactly the ones that do not step
   on their own, so a resolution wrapping one of them is stuck. *)

Lemma step_through_par_no_step {X Y} σ σx (c : code X Y exn) x
    (bx : micro Y exn) :
  step_through_par_code c →
  step (σ, stop c x) (σx, bx) →
  False.
Proof. intros Hc Hstep. destruct_step; by simpl in *. Qed.

Lemma step_stop_shape {X Y} σ σ1 σ2 (c : code X Y exn) x (b1 b2 : micro Y exn) :
  step (σ, stop c x) (σ1, b1) →
  step (σ, stop c x) (σ2, b2) →
  is_result b1 ∨ b1 = b2.
Proof.
  intros H1 H2. destruct_step; destruct_step;
    first [ by right | left; simpl; by repeat case_match ].
Qed.

(* -------------------------------------------------------------------------- *)

(* A step of an erased thread is matched by steps of the annotated one,
   unless the latter runs into something stuck. *)

Local Ltac stutter_absurd :=
  match goal with
  | H : no_stutter _ |- _ =>
      exfalso; simpl in H; first [ by apply H | apply H; by intros [] ]
  end.

(* The witness that a resolution is stuck where it stands: [mstuck]'s second
   disjunct. *)

Local Ltac stuck_resolution :=
  right; do 6 eexists; split; [ done | ];
  intros ? ? ?; by destruct_step.

Local Ltac stuck_resolution_par :=
  right; do 6 eexists; split; [ done | ];
  intros ? ? Hbx;
  by destruct (step_through_par_no_step _ _ _ _ _ ltac:(eassumption) Hbx).

(* Stripping the stutter off one branch of a [Par]. *)

Local Ltac unstutter_l :=
  match goal with
  | |- reaches_stuck ?σ (Par ?m1 ?m2 ?k) ∨ _ =>
      destruct (par_l_unstutter σ m1 _ _ _ m2 k ltac:(eassumption))
        as [ ? | (n1 & κ1 & u1 & Hs1 & Hu1 & Hns1) ]; first by left
  end.

Local Ltac unstutter_r :=
  match goal with
  | |- reaches_stuck ?σ (Par ?m1 ?m2 ?k) ∨ _ =>
      destruct (par_r_unstutter σ m2 _ _ _ m1 k ltac:(eassumption))
        as [ ? | (n2 & κ2 & u2 & Hs2 & Hu2 & Hns2) ]; first by left
  end.

(* Every case in which the annotated thread keeps up ends the same way: run,
   take one more step, land on something that erases to where the erased
   thread went. This absorbs the step count and the observation list. *)

Lemma matched_advance {A E} (fA : A → A) (fE : E → E)
    n σ (ma : micro A E) κ σ0 m0 κ' σ' ma' σe' me' :
  tsteps n (σ, ma) κ (σ0, m0) →
  tstep (σ0, m0) κ' (σ', ma') →
  erase_store σ' σe' →
  erase_micro fA fE ma' me' →
  reaches_stuck σ ma
  ∨ ∃ n κ σ' ma', tsteps n (σ, ma) κ (σ', ma')
                  ∧ erase_store σ' σe' ∧ erase_micro fA fE ma' me'.
Proof.
  intros Hs Hstep Hσ' Hr. right.
  exists (n + 1), (κ ++ κ'), σ', ma'. split; [ | done ].
  eapply tsteps_trans; [ exact Hs | by apply tsteps_one ].
Qed.

(* The dual: the annotated thread steps *first*. *)

Lemma matched_prepend {A E} (fA : A → A) (fE : E → E)
    σ σ0 (ma ma0 : micro A E) κ0 σe' me' :
  tstep (σ, ma) κ0 (σ0, ma0) →
  reaches_stuck σ0 ma0
  ∨ (∃ n κ σ' ma', tsteps n (σ0, ma0) κ (σ', ma')
                   ∧ erase_store σ' σe' ∧ erase_micro fA fE ma' me') →
  reaches_stuck σ ma
  ∨ ∃ n κ σ' ma', tsteps n (σ, ma) κ (σ', ma')
                  ∧ erase_store σ' σe' ∧ erase_micro fA fE ma' me'.
Proof.
  intros Hstep [ Hst | (n & κ & σ' & ma' & Hs & Hσ' & Hr) ].
  - left. eapply reaches_stuck_after; [ by apply tsteps_one, Hstep | done ].
  - right. exists (S n), (κ0 ++ κ), σ', ma'. split; [ | done ].
    econstructor; [ exact Hstep | exact Hs ].
Qed.

(* Each case of [erase_step_micro] is one of four moves. *)

(* [mstuck]: the thread crashed, or it sits at a resolution whose stop call
   cannot step. *)

Local Ltac es_mstuck :=
  first [ by left | stuck_resolution | stuck_resolution_par ].

(* The annotated thread ran into something stuck from [Hs]. *)
Local Tactic Notation "es_stuck" uconstr(Hs) :=
  left; eapply reaches_stuck_after;
    [ exact Hs
    | first [ apply mstuck_handle; es_mstuck
            | apply mstuck_par_l; es_mstuck
            | apply mstuck_par_r; es_mstuck ] ].

(* Split on the shape of the computation the erasure relation
   relates. *)
Local Tactic Notation "es_shape" ident(H) :=
  dependent destruction H; try stutter_absurd; try done.

(* The source thread keeps up by taking [rule], leaving only the
   erasure of where it landed. [Hs] is the run that precedes it. *)
Local Tactic Notation "es_advance" uconstr(Hs) uconstr(rule) :=
  eapply matched_advance; [ exact Hs | by apply TBase, rule | done | ].

(* The stop call under a resolution reduced to a computation rather than
   to an outcome, so the resolution has nothing to resolve with and is stuck
   where it stands. [Hb] is that call's step. *)
Local Tactic Notation "es_resolve_stuck" uconstr(Hb) :=
  left; apply reaches_stuck_now; right; do 6 eexists; split; [ done | ];
  intros σx bx Hbx Hres;
  by destruct (step_stop_shape _ _ _ _ _ _ _ Hb Hbx) as [ ? | <- ].

Lemma erase_step_micro {A E} (fA : A → A) (fE : E → E) (ma me : micro A E) σ σe :
  erase_micro fA fE ma me →
  erase_store σ σe →
  ∀ σe' me',
    step (σe, me) (σe', me') →
    reaches_stuck σ ma
    ∨ (∃ n κ σ' ma', tsteps n (σ, ma) κ (σ', ma') ∧ erase_store σ' σe' ∧
                     erase_micro fA fE ma' me').
Proof.
  intros Hm Hσ. induction Hm; intros σe' me' Hstep.
  - (* Ret *) by destruct_step.
  - (* Throw *) by destruct_step.
  (* An annotated crash is stuck where it stands. *)
  - (* Crash *) left. by apply reaches_stuck_now; left.
  (* [Handle]: strip the stutter off the handled computation, then read the
     erased step. Wherever the annotated computation crashed instead, the
     handler propagates the crash. *)
  - (* Handle *)
    rename H into Hh, IHHm into IHm.
    destruct (handle_unstutter σ m m' h Hm)
      as [ ? | (n & κ & m0 & Hs & Hm0 & Hns) ]; first by left.
    destruct_step.
    + (* StepHandleRet *)
      es_shape Hm0;
        [ es_advance Hs StepHandleRet; apply (Hh (O3Ret _)) | es_stuck Hs ].
    + (* StepHandleThrow *)
      es_shape Hm0;
        [ es_advance Hs StepHandleThrow; apply (Hh (O3Throw _)) | es_stuck Hs ].
    + (* StepHandlePerform: the handler captures the continuation, at the
         same fresh location on both sides. *)
      es_shape Hm0;
        [ es_stuck Hs
        | eapply matched_advance;
            [ exact Hs
            | apply TBase, StepHandlePerform; by eapply erase_store_none
            | apply erase_store_insert; by auto
            | apply (Hh (O3Perform _ _)) ]
        | es_stuck Hs ].
    + (* StepHandleFork *)
      es_shape Hm0;
        [ es_stuck Hs
        | es_advance Hs StepHandleFork; eapply EM_Stop; [ done | ]; intros o;
          apply EM_Handle; [ by auto | apply Hh ]
        | es_stuck Hs ].
    + (* StepHandleJoin *)
      es_shape Hm0;
        [ es_stuck Hs
        | es_advance Hs StepHandleJoin; eapply EM_Stop; [ done | ]; intros o;
          apply EM_Handle; [ by auto | apply Hh ]
        | es_stuck Hs ].
    + (* StepHandleResolve: the erased program has no resolution left, so
         this thread can only be the erasure of one that crashed. *)
      es_shape Hm0; es_stuck Hs.
    + (* StepHandleCrash *) es_shape Hm0; es_stuck Hs.
    + (* StepHandleLeft *)
      destruct (IHm _ _ ltac:(eassumption))
        as [ Hst2 | (n2 & κ2 & σ2 & ma2 & Hs2 & Hσ2 & Hr2) ].
      * left. by apply mstuck_under_handle.
      * destruct (tsteps_handle n2 σ m κ2 σ2 ma2 h Hs2)
          as [ [ n3 H3 ] | H3 ]; last by left.
        eauto 9 using EM_Handle.
  (* An ordinary call: the erased program's step is the annotated one's. *)
  - (* Stop *)
    rename H into Hc.
    destruct (step_stop_split _ _ _ _ _ _ Hstep) as (be & Hbe & ->).
    destruct (erase_step_call c x σ σe σe' be Hc Hσ Hbe)
      as (σ' & b & Hb & [ -> | (Hσ' & Hrel) ]).
    { (* The annotated call crashed: it is stuck after one step. *)
      left. eapply reaches_stuck_after;
        [ apply tsteps_one, TBase; by apply step_stop_join
        | by apply reaches_stuck_now; left ]. }
    right. exists 1, [], σ', (try2 b k). split; [ | split; [ done | ] ].
    + apply tsteps_one, TBase. by apply step_stop_join.
    + by eapply erase_try2.
  (* [Proph.create ()] and [ref ()] take the same step, down to the location
     they pick. *)
  - (* NewProph *)
    rename H into Hk.
    destruct_step.
    right. exists 1, [], (<[ l := Val VUnit ]> σ), (continue k l). split.
    + apply tsteps_one, TBase, StepNewProph. by eapply erase_store_none.
    + split; [ by apply erase_store_insert | apply (Hk (O2Ret l)) ].
  - (* Resolve *)
    rename H into Hc, H0 into Hnt, H1 into Hk.
    destruct (step_stop_split _ _ _ _ _ _ Hstep) as (be & Hbe & ->).
    destruct (erase_step_call c x σ σe σe' be Hc Hσ Hbe)
      as (σ' & b & Hb & [ -> | (Hσ' & Hrel) ]).
    { (* The annotated call crashed: so does the resolution. *)
      left. eapply reaches_stuck_after;
        [ apply tsteps_one; exact (TResolve σ σ' c x p v Crash k Hb I)
        | by apply reaches_stuck_now; left ]. }
    destruct b as [ w | ex | | | | ].
    + (* the stop returned, so the resolution happens *)
      right. exists 1, [(p, (w, v))], σ', (continue k w). split;
        [ apply tsteps_one; exact (TResolve σ σ' c x p v (Ret w) k Hb I) | ].
      split; [ done | ]. dependent destruction Hrel. apply (Hk w).
    + (* the stop raised, which the codes a resolution may wrap never do *)
      by destruct (Hnt _ _ _ Hb).
    + (* the call crashed *)
      right. exists 1, [], σ', Crash. split;
        [ apply tsteps_one; exact (TResolve σ σ' c x p v Crash k Hb I) | ].
      split; [ done | apply EM_CrashL ].
    (* The call reduced to a computation rather than to an outcome, so the
       annotated thread is stuck, which [safe] excludes at the pool level. *)
    + es_resolve_stuck Hb.
    + es_resolve_stuck Hb.
    + es_resolve_stuck Hb.
  (* The two calls erasure removes: the annotated program steps first, and
     the induction hypothesis carries the rest. *)
  - (* ResolveReturn *)
    rename IHHm into IHm.
    eapply matched_prepend; [ apply tstep_resolve_return | by apply IHm ].
  - (* Return *)
    rename IHHm into IHm.
    eapply matched_prepend; [ apply tstep_return | by apply IHm ].
  - (* Par *)
    rename H into Hk, IHHm1 into IHm1, IHHm2 into IHm2.
    destruct_step.
    + (* StepParRetRet: both branches have to be stripped before they can be
         read together. *)
      unstutter_l.
      destruct (par_r_unstutter σ m2 _ f2 fE' u1 k Hm2)
        as [ (n2 & κ2 & σ2 & ma2 & Hs2 & Hst2)
           | (n2 & κ2 & u2 & Hs2 & Hu2 & Hns2) ];
        first (left; eapply reaches_stuck_steps;
                 [ by eapply tsteps_trans | done ]).
      es_shape Hu1; last es_stuck (tsteps_trans _ _ _ _ _ _ _ Hs1 Hs2).
      es_shape Hu2; last es_stuck (tsteps_trans _ _ _ _ _ _ _ Hs1 Hs2).
      es_advance (tsteps_trans _ _ _ _ _ _ _ Hs1 Hs2) StepParRetRet;
        apply (Hk (O2Ret (_, _))).
    + (* StepParCrashLeft *) unstutter_l; es_shape Hu1; es_stuck Hs1.
    + (* StepParCrashRight *) unstutter_r; es_shape Hu2; es_stuck Hs2.
    + (* StepParThrowLeft *)
      unstutter_l; es_shape Hu1;
        [ es_advance Hs1 StepParThrowLeft; apply (Hk (O2Throw _))
        | es_stuck Hs1 ].
    + (* StepParThrowRight *)
      unstutter_r; es_shape Hu2;
        [ es_advance Hs2 StepParThrowRight; apply (Hk (O2Throw _))
        | es_stuck Hs2 ].
    + (* StepThroughParLeft *)
      unstutter_l; es_shape Hu1;
        [ es_stuck Hs1
        | es_advance Hs1 StepThroughParLeft; eapply EM_Stop; [ done | ];
          eauto using EM_Par
        | es_stuck Hs1 ].
    + (* StepThroughParRight *)
      unstutter_r; es_shape Hu2;
        [ es_stuck Hs2
        | es_advance Hs2 StepThroughParRight; eapply EM_Stop; [ done | ];
          eauto using EM_Par
        | es_stuck Hs2 ].
    + (* StepParLeft *)
      destruct (IHm1 _ _ ltac:(eassumption))
        as [ Hst2 | (n2 & κ2 & σ2 & ma2 & Hs2 & Hσ2 & Hr2) ].
      * left. by apply mstuck_under_par_l.
      * destruct (tsteps_par_l n2 σ m1 κ2 σ2 ma2 m2 k Hs2)
          as [ [ n3 H3 ] | H3 ]; last by left.
        eauto 9 using EM_Par.
    + (* StepParRight *)
      destruct (IHm2 _ _ ltac:(eassumption))
        as [ Hst2 | (n2 & κ2 & σ2 & ma2 & Hs2 & Hσ2 & Hr2) ].
      * left. by apply mstuck_under_par_r.
      * destruct (tsteps_par_r n2 σ m2 κ2 σ2 ma2 m1 k Hs2)
          as [ [ n3 H3 ] | H3 ]; last by left.
        eauto 9 using EM_Par.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma erase_thpool_insert π πe ι m me :
  erase_thpool π πe →
  erase_microvx m me →
  erase_thpool (<[ ι := m ]> π) (<[ ι := me ]> πe).
Proof.
  intros Hπ Hm ι'. unfold thpool, insert_thpool, lookup_thpool in *.
  destruct (decide (ι = ι')) as [ -> | Hne ].
  - by rewrite !lookup_insert_eq.
  - rewrite !lookup_insert_ne //; try apply Hπ.
Qed.

(* The erased pool does not move while the annotated one steps away a
   stutter, so the insertion happens on one side only. *)

Lemma erase_thpool_insert_l π πe ι m me :
  erase_thpool π πe →
  πe !! ι = Some me →
  erase_microvx m me →
  erase_thpool (<[ ι := m ]> π) πe.
Proof.
  intros Hπ Hme Hm ι'. unfold thpool, insert_thpool, lookup_thpool in *.
  destruct (decide (ι = ι')) as [ -> | Hne ].
  - rewrite lookup_insert_eq Hme. exact Hm.
  - rewrite lookup_insert_ne //; try apply Hπ.
Qed.

Lemma erase_thpool_none π πe ι :
  erase_thpool π πe →
  πe !! ι = None →
  π !! ι = None.
Proof.
  intros Hπ Hι. specialize (Hπ ι). unfold thpool in *. rewrite Hι in Hπ.
  destruct (π !! ι) as [ m | ] eqn:Hm; rewrite Hm in Hπ;
    [ exfalso; exact Hπ | done ].
Qed.

Lemma mstuck_not_not_stuck {A E} σ (m : micro A E) (π : gset thread) :
  mstuck σ m →
  not_stuck m σ π →
  False.
Proof.
  intros [ -> | (X & c & x & p & v & k & -> & Hc) ] [ [] | [ Hcp | [] ] ].
  - destruct Hcp as (κ & σ' & m' & μ & Hts).
    by dependent destruction Hts; destruct_step.
  - destruct Hcp as (κ & σ' & m' & μ & Hts).
    remember (x, p, v) as y eqn:Hy.
    dependent destruction Hts;
      first [ by destruct_step
            | (simplify_eq; eapply Hc; [ eassumption | done ]) ].
Qed.

Lemma safe_not_mstuck σ π ι (m : microvx) n κ σ' m' :
  safe σ π →
  π !! ι = Some m →
  tsteps n (σ, m) κ (σ', m') →
  mstuck σ' m' →
  False.
Proof.
  intros Hsafe Hι Hs Hst.
  eapply mstuck_not_not_stuck; [ exact Hst | ].
  eapply Hsafe.
  - apply erased_proph_steps_proph_steps. eexists _, _.
    exact (tsteps_proph_steps ι n (σ, m) (σ', m') κ π Hι Hs).
  - simpl. unfold thpool, insert_thpool, lookup_thpool. apply lookup_insert_eq.
Qed.

Lemma safe_not_reaches_stuck σ π ι (m : microvx) :
  safe σ π → π !! ι = Some m → reaches_stuck σ m → False.
Proof. intros ? ? (n & κ & σ' & m' & ? & ?). by eapply safe_not_mstuck. Qed.

(* The two ways safety rules out an annotated thread that the erased one has
   left behind: it crashed where the erased thread went on, or it sits at a
   resolution whose call cannot step. Both [erase_fork_backward] and
   [erase_join_backward] discharge their dead branches with these. *)

Local Tactic Notation "safe_crashed" uconstr(Hsafe) uconstr(Hι) uconstr(Hs) :=
  by destruct (safe_not_mstuck _ _ _ _ _ _ _ _ Hsafe Hι Hs (or_introl eq_refl)).

Local Tactic Notation "safe_unresolved"
    uconstr(Hsafe) uconstr(Hι) uconstr(Hs) :=
  exfalso; eapply safe_not_mstuck; [ exact Hsafe | exact Hι | exact Hs | ];
  stuck_resolution.

(* The pool runs off both stutters and then performs the join itself. *)

Local Tactic Notation "join_step" uconstr(Hι2) :=
  eapply proph_steps_trans; [ by eapply proph_steps_trans | ];
  apply proph_steps_one; apply PureTS; eapply JoinTS; [ exact Hι2 | ];
  unfold attempt_join, thpool, insert_thpool, lookup_thpool;
  by rewrite lookup_insert_eq.

Lemma erase_fork_backward σ π πe ι ι' (v1 v2 : val) k :
  safe σ π →
  erase_thpool π πe →
  πe !! ι = Some (Stop CFork (v1, v2) k) →
  πe !! ι' = None →
  ∃ n κ π',
    proph_steps n (σ, π) κ (σ, π') ∧
    erase_thpool π'
      (<[ ι' := call v1 v2 ]> (<[ ι := continue k (VThread ι') ]> πe)).
Proof.
  intros Hsafe Hπ Hιe Hnone.
  destruct (erase_thpool_lookup _ _ _ _ Hπ Hιe) as (ma & Hι & Hma).
  destruct (erase_unstutter erase_val erase_val ma _ σ Hma)
    as [ Hst1 | (n1 & κ1 & ma0 & Hs1 & Hma0 & Hns) ];
    first by destruct (safe_not_reaches_stuck _ _ _ _ Hsafe Hι Hst1).
  assert (ι ≠ ι') by congruence.
  remember (v1, v2) as vv eqn:Hvv.
  dependent destruction Hma0; try stutter_absurd; try done; fold erase_val in *.
  - safe_crashed Hsafe Hι Hs1.
  - destruct x as (w1, w2). simpl in Hvv. simplify_eq.
    eexists (n1 + 1), (κ1 ++ []), _. split.
    + eapply proph_steps_trans;
        [ exact (tsteps_proph_steps ι n1 (σ, ma) (σ, _) κ1 π Hι Hs1) | ].
      simpl. apply proph_steps_one.
      apply PureTS. eapply ForkTS. apply lookup_insert_eq.
      rewrite lookup_insert_ne; last done.
      by eapply erase_thpool_none.
    + apply erase_thpool_insert; [ | apply erase_call ].
      apply erase_thpool_insert; [ | by apply H0].
      eapply erase_thpool_insert_l; eauto using EM_Stop.
  - (* a resolution wrapping a fork never resolves, so the thread is stuck *)
    safe_unresolved Hsafe Hι Hs1.
Qed.

Lemma erase_join_backward σ π πe ι ι' k m :
  safe σ π →
  erase_thpool π πe →
  πe !! ι = Some (Stop CJoin ι' k) →
  attempt_join ι' πe k = Some m →
  ∃ n κ π',
    proph_steps n (σ, π) κ (σ, π') ∧
    erase_thpool π' (<[ ι := m ]> πe).
Proof.
  intros Hsafe Hπ Hιe Hjoin.
  destruct (erase_thpool_lookup _ _ _ _ Hπ Hιe) as (ma & Hι & Hma).
  destruct (erase_unstutter erase_val erase_val ma _ σ Hma)
    as [ Hst1 | (n1 & κ1 & ma0 & Hs1 & Hma0 & Hns) ];
    first by destruct (safe_not_reaches_stuck _ _ _ _ Hsafe Hι Hst1).
  assert (Hsteps1 : proph_steps n1 (σ, π) κ1 (σ, <[ ι := ma0 ]> π))
    by exact (tsteps_proph_steps ι n1 (σ, ma) (σ, ma0) κ1 π Hι Hs1).
  assert (Hsafe1 : safe σ (<[ ι := ma0 ]> π))
    by (eapply safe_steps; [ exact Hsafe | exact Hsteps1 ]).
  assert (Hπ1 : erase_thpool (<[ ι := ma0 ]> π) πe)
    by (eapply erase_thpool_insert_l; [ exact Hπ | exact Hιe | exact Hma0 ]).
  assert (Hι1 : <[ ι := ma0 ]> π !! ι = Some ma0)
    by (unfold thpool, insert_thpool, lookup_thpool; apply lookup_insert_eq).
  (* Naming the pool the stutter leads to keeps it in reach of the case
     analysis below, which rewrites the computation it holds. *)
  remember (<[ ι := ma0 ]> π) as π1 eqn:Hπ1eq.
  dependent destruction Hma0; try stutter_absurd; try done.
  - safe_crashed Hsafe Hι Hs1.
  - unfold attempt_join in Hjoin.
    destruct (πe !! x) as [ me' | ] eqn:Hxe; rewrite Hxe in Hjoin.
    + (* the joined thread exists, so strip its stutter too *)
      assert (ι ≠ x).
      { intros ->. rewrite Hιe in Hxe. injection Hxe as <-. by simpl in Hjoin. }
      destruct (erase_thpool_lookup _ _ _ _ Hπ Hxe) as (ma' & Hx & Hma').
      assert (Hx1 : π1 !! x = Some ma')
        by (subst π1; unfold thpool, insert_thpool, lookup_thpool;
            rewrite lookup_insert_ne //).
      destruct (erase_unstutter erase_val erase_val ma' me' σ Hma')
        as [ Hst2 | (n2 & κ2 & ma0' & Hs2 & Hma0' & Hns') ];
        first by destruct (safe_not_reaches_stuck _ _ _ _ Hsafe1 Hx1 Hst2).
      assert (Hsteps2 : proph_steps n2 (σ, π1) κ2 (σ, <[ x := ma0' ]> π1))
        by exact (tsteps_proph_steps x n2 (σ, ma') (σ, ma0') κ2 _ Hx1 Hs2).
      eassert (Hι2 : <[ x := ma0' ]> π1 !! ι = Some _).
      { unfold thpool, insert_thpool, lookup_thpool.
        rewrite lookup_insert_ne //. }
      (* the joined thread is a result on one side exactly when it is on the
         other, and erasure maps that result *)
      destruct me' as [ v | ex | | | | ]; simplify_eq;
        dependent destruction Hma0'; try stutter_absurd;
        try safe_crashed Hsafe1 Hx1 Hs2.
      * eexists (n1 + n2 + 1), ((κ1 ++ κ2) ++ []), _.
        split; [ join_step Hι2 | ].
        apply erase_thpool_insert; [ | apply (H0 (O2Ret _)) ].
        eapply erase_thpool_insert_l; [ done | exact Hxe | apply EM_Ret ].
      * eexists (n1 + n2 + 1), ((κ1 ++ κ2) ++ []), _.
        split; [ join_step Hι2 | ].
        apply erase_thpool_insert; [ | apply (H0 (O2Throw _)) ].
        eapply erase_thpool_insert_l; [ done | exact Hxe | apply EM_Throw ].
    + (* the joined thread does not exist, and both programs crash *)
      simplify_eq.
      assert (π !! x = None) by by eapply erase_thpool_none.
      assert (ι ≠ x) by congruence.
      eexists (n1 + 1), (κ1 ++ []), _. split.
      { eapply proph_steps_trans; [ exact Hsteps1 | ].
        apply proph_steps_one, PureTS. eapply JoinTS; [ exact Hι1 | ].
        unfold attempt_join, thpool, insert_thpool, lookup_thpool.
        rewrite lookup_insert_ne //. by simplify_option_eq. }
      apply erase_thpool_insert; [ | apply EM_Crash ].
      eapply erase_thpool_insert_l; [ done | exact Hιe | ].
      by apply EM_Stop.
  - (* a resolution wrapping a join never resolves *)
    safe_unresolved Hsafe Hι Hs1.
Qed.

Lemma erase_step_backward σ π σe πe σe' πe' :
  safe σ π →
  erase_store σ σe →
  erase_thpool π πe →
  threadpool_step (σe, πe) (σe', πe') →
  ∃ n κ σ' π',
    proph_steps n (σ, π) κ (σ', π') ∧
    erase_store σ' σe' ∧ erase_thpool π' πe'.
Proof.
  intros Hsafe Hσ Hπ Hstep. dependent destruction Hstep.
  - destruct (erase_thpool_lookup _ _ _ _ Hπ H) as (ma & Hι & Hma).
    destruct (erase_step_micro erase_val erase_val ma m σ σe Hma Hσ _ _ H0)
      as [ Hst | (n & κ & σ2 & ma2 & Hs & Hσ2 & Hr) ].
    { by destruct (safe_not_reaches_stuck σ π ι ma Hsafe Hι Hst). }
    exists n, κ, σ2, (<[ ι := ma2 ]> π). split; [ | split; [ done | ] ].
    + exact (tsteps_proph_steps ι n (σ, ma) (σ2, ma2) κ π Hι Hs).
    + by apply erase_thpool_insert.
  - edestruct erase_fork_backward as (n & κ & π' & Hsteps & Hπ');
      [ exact Hsafe | exact Hπ | eassumption | eassumption | ].
    by exists n, κ, σ, π'.
  - edestruct erase_join_backward as (n & κ & π' & Hsteps & Hπ');
      [ exact Hsafe | exact Hπ | eassumption | eassumption | ].
    by exists n, κ, σ, π'.
Qed.

(* Safety transfers to the erased configuration. *)

(* Progress transfers, independently of the store and the pool: an erased
   thread is a result, or heads a call that steps whatever the store holds,
   or is a [join], which [not_stuck] admits as waiting. *)

Lemma erase_not_stuck_micro ma :
  ∀ me σ (π : thpool) σe (πe : thpool) ι,
    safe σ π →
    π !! ι = Some ma →
    erase_microvx ma me →
    not_stuck me σe (dom πe).
Proof.
  dependent induction ma; intros me σ π σe πe ι Hsafe Hι Hm.
  - dependent destruction Hm. by left.
  - dependent destruction Hm. by left.
  - by destruct (safe_not_crash _ _ _ Hsafe Hι).
  - dependent destruction Hm.
    right; left.
    by apply subjective_step.can_step_reducible, can_step_handle.
  - dependent destruction Hm.
    + apply not_stuck_call. eapply not_stuck_call_code; [ done | ].
      by eapply (Hsafe σ π (rtc_refl _ _)).
    + right; left. apply subjective_step.can_step_reducible, can_step_stop;
        split; [ done | by intros [] ].
    + apply not_stuck_call. eapply not_stuck_resolve_code; [ done | ].
      by eapply (Hsafe σ π (rtc_refl _ _)).
    + (* the two calls erasure removes: the annotated program steps first *)
      erase_result_step; erase_not_stuck_finish.
    + erase_result_step; erase_not_stuck_finish.
  - dependent destruction Hm.
    right; left. by apply subjective_step.can_step_reducible, can_step_par.
Qed.

Lemma erase_not_stuck σ π σe πe :
  safe σ π →
  erase_store σ σe →
  erase_thpool π πe →
  ∀ ι m, πe !! ι = Some m → not_stuck m σe (dom πe).
Proof.
  intros Hsafe Hσ Hπ ι m Hme.
  destruct (erase_thpool_lookup _ _ _ _ Hπ Hme) as (ma & Hι & Hm).
  by eapply erase_not_stuck_micro.
Qed.

(* A result of the erased program is the erasure of a result of the
   annotated one. *)

(* The outcome is passed in: it cannot be inferred, since the induction
   hypothesis mentions it under [inject2], a match that unification will not
   invert. *)

Local Ltac erase_result_finish oe :=
  match goal with
  | Hstep : proph_step (?σ, ?π) ?κ0 (?σ, <[ ?ι := continue ?k ?w ]> ?π),
    Hsafe : safe ?σ ?π, IH : ∀ _ _, _ → _ → @JMeq _ _ _ _ → _,
    Hm : erase_micro _ _ (continue ?k ?w) _ |- _ =>
      let Hsafe' := fresh "Hsafe'" in
      assert (Hsafe' : safe σ (<[ ι := continue k w ]> π))
        by (eapply safe_steps; [ exact Hsafe | ];
            econstructor; [ exact Hstep | constructor ]);
      destruct (IH (O2Ret w) (continue k w) eq_refl eq_refl JMeq_refl oe σ
                   (<[ ι := continue k w ]> π) ι Hsafe'
                   ltac:(by rewrite lookup_insert_eq) Hm)
        as (n & κ & σ' & π' & o' & Hsteps & Ho' & Hoe);
      exists (S n), (κ0 ++ κ), σ', π', o'; split_and!; try done;
      econstructor; [ exact Hstep | exact Hsteps ]
  end.

Lemma erase_result_micro m :
  ∀ oe σ π ι,
    safe σ π →
    π !! ι = Some m →
    erase_microvx m (inject2 oe) →
    ∃ n κ σ' π' o',
      proph_steps n (σ, π) κ (σ', π') ∧
      π' !! ι = Some (inject2 o') ∧ erase_outcome o' = oe.
Proof.
  dependent induction m;
    intros oe σ π ι Hsafe Hι Hm; destruct oe as [ ve | exe ]; simpl in Hm.
  - dependent destruction Hm.
    exists 0, [], σ, π, (O2Ret a). split_and!; [ constructor | done | done ].
  - dependent destruction Hm.
  - dependent destruction Hm.
  - dependent destruction Hm.
    exists 0, [], σ, π, (O2Throw e). split_and!; [ constructor | done | done ].
  - by destruct (safe_not_crash _ _ _ Hsafe Hι).
  - by destruct (safe_not_crash _ _ _ Hsafe Hι).
  (* [Handle] and [Par] erase to a [Handle] and a [Par], never to a result. *)
  - dependent destruction Hm.
  - dependent destruction Hm.
  (* [Stop]: the only calls whose erasure can be a result are the two that
     erasure removes, and each costs the annotated program one step. *)
  - dependent destruction Hm; erase_result_step; erase_result_finish (@O2Ret val val ve).
  - dependent destruction Hm; erase_result_step; erase_result_finish (@O2Throw val val exe).
  - dependent destruction Hm.
  - dependent destruction Hm.
Qed.

Lemma erase_result σ π σe πe ι oe :
  safe σ π →
  erase_store σ σe →
  erase_thpool π πe →
  πe !! ι = Some (inject2 oe) →
  ∃ n κ σ' π' o',
    proph_steps n (σ, π) κ (σ', π') ∧
    π' !! ι = Some (inject2 o') ∧ erase_outcome o' = oe.
Proof.
  intros Hsafe Hσ Hπ Hme.
  destruct (erase_thpool_lookup _ _ _ _ Hπ Hme) as (m & Hι & Hm).
  by eapply erase_result_micro.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** The simulation. *)

(* The invariant: every configuration the erased program reaches is the
   erasure of a configuration the annotated program reaches. *)

Lemma erase_sim k ce ce' :
  threadpool_steps k ce ce' →
  ∀ σ π,
    safe σ π →
    erase_store σ ce.1 →
    erase_thpool π ce.2 →
    ∃ n κ σ' π',
      proph_steps n (σ, π) κ (σ', π') ∧
      safe σ' π' ∧ erase_store σ' ce'.1 ∧ erase_thpool π' ce'.2.
Proof.
  induction 1 as [ c | n c1 c2 c3 Hstep Hsteps IH ];
    intros σ π Hsafe Hσ Hπ.
  - exists 0, [], σ, π. split_and!; try done. constructor.
  - destruct c1 as [σe1 πe1], c2 as [σe2 πe2].
    destruct (erase_step_backward σ π σe1 πe1 σe2 πe2)
      as (n1 & κ1 & σ1 & π1 & Hsteps1 & Hσ1 & Hπ1); [ done.. | ].
    destruct (IH σ1 π1) as (n2 & κ2 & σ2 & π2 & Hsteps2 & Hsafe2 & Hσ2 & Hπ2);
      [ by eapply safe_steps | done | done | ].
    exists (n1 + n2), (κ1 ++ κ2), σ2, π2. split_and!; try done.
    by eapply proph_steps_trans.
Qed.

(* -------------------------------------------------------------------------- *)

Theorem erasure (e : expr) ι (Φ : outcome2 val exn → Prop) σ σe :
  (* Let [σe] be an erasure of the initial store [σ]. *)
  erase_store σ σe →
  (∀ k κs σ2 π,
     proph_steps k (σ, {[ ι := eval [] e ]}) κs (σ2, π) →
     (∀ ι' m, π !! ι' = Some m → not_stuck m σ2 (dom π)) ∧
     (∀ o, π !! ι = Some (inject2 o) → Φ o)) →
  (∀ k σ2 π,
     threadpool_steps k (σe, {[ ι := eval [] (erase_expr e) ]}) (σ2, π) →
     (∀ ι' m, π !! ι' = Some m → not_stuck m σ2 (dom π)) ∧
     (∀ o, π !! ι = Some (inject2 o) → ∃ o', erase_outcome o' = o ∧ Φ o')).
Proof.
  intros Hσ Hann k σ2 πe Hsteps.
  (* The two initial thread pools are related, by [1] and [2]. *)
  assert (Hπ : erase_thpool {[ ι := eval [] e ]}
                            {[ ι := eval [] (erase_expr e) ]}).
  { apply erase_thpool_singleton, erase_eval. }
  assert (Hsafe : safe σ {[ ι := eval [] e ]}).
  { intros σ' π' Hrtc ι' m Hm.
    apply erased_proph_steps_proph_steps in Hrtc as (k' & κs' & Hsteps').
    by eapply Hann. }
  (* So the configuration the erased program has reached is the erasure of
     one the annotated program reaches. *)
  destruct (erase_sim _ _ _ Hsteps _ _ Hsafe Hσ Hπ)
    as (n & κ & σ' & π' & Hann' & Hsafe' & Hσ' & Hπ').
  split.
  - (* Safety, by [4]. *)
    by eapply erase_not_stuck.
  - (* Results, by [5]: the annotated program reaches the corresponding
       result in a few more steps, and [Hann] applies there. *)
    intros o Ho.
    destruct (erase_result _ _ _ _ _ _ Hsafe' Hσ' Hπ' Ho)
      as (n2 & κ2 & σ'' & π'' & o' & Hsteps2 & Ho' & <-).
    exists o'. split; first done.
    eapply Hann; last done.
    by eapply proph_steps_trans.
Qed.

(* -------------------------------------------------------------------------- *)

(* The two theorems compose: from an [EWP] proof of the annotated program,
   the erased program is safe in the semantic model. *)

Corollary erasure_adequacy Σ `{!osirisGpreS Σ} (e : expr) ι Φ σ σe :
  erase_store σ σe →
  (∀ `{!osirisGS Σ}, ⊢ ewp_def ⊤ (eval [] e) ⊥ (λ o, ⌜Φ o⌝)) →
  (∀ k σ2 π,
     threadpool_steps k (σe, {[ ι := eval [] (erase_expr e) ]}) (σ2, π) →
     (∀ ι' m, π !! ι' = Some m → not_stuck m σ2 (dom π)) ∧
     (∀ o, π !! ι = Some (inject2 o) → ∃ o', erase_outcome o' = o ∧ Φ o')).
Proof.
  intros Hσ Hwp. eapply erasure; [ done | ]. intros.
  by eapply osiris_adequacy.
Qed.

(* A simpler statement under an empty initial heap. *)

Corollary erasure_adequacy_empty Σ `{!osirisGpreS Σ} (e : expr) ι Φ :
  (∀ `{!osirisGS Σ}, ⊢ ewp_def ⊤ (eval [] e) ⊥ (λ o, ⌜Φ o⌝)) →
  (∀ k σ2 π,
     threadpool_steps k (∅, {[ ι := eval [] (erase_expr e) ]}) (σ2, π) →
     (∀ ι' m, π !! ι' = Some m → not_stuck m σ2 (dom π)) ∧
     (∀ o, π !! ι = Some (inject2 o) → ∃ o', erase_outcome o' = o ∧ Φ o')).
Proof.
  intros Hwp.
  eapply (erasure_adequacy Σ); [ apply erase_store_empty | apply Hwp ].
Qed.
