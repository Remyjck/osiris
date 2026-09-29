From Stdlib Require Import Logic.FunctionalExtensionality Program.Equality.
From stdpp Require Import gmap relations.
From osiris Require Import base.
From osiris.utils.logic Require Import lsteps.
From osiris.lang Require Import lang.
Require Import code eval.

(* This file equips the [micro] monad with an operational semantics, that is,
   a reduction semantics of the form [step c c'] where [c] and [c'] are pairs
   of a store and a computation. *)

(* The definition of the relation [step] gives meaning to system calls, that
   is, to [Stop] events. For example, a [Stop CEval] event is interpreted as a
   request for a recursive invocation of the evaluator. It also gives meaning
   to the monad's non-standard constructs, namely [Handle] and [Par]. *)

(* -------------------------------------------------------------------------- *)

(* A memory block stores either a value, a block of memory, or a captured continuation.

   A continuation is either not-yet-shot or already shot.

   This gives rise to four cases: [Val] for values, [Block] for blocks of
   memory, [Kont] for continuations, and [Shot] for already-shot
   continuations.  *)

Inductive mem_block : Type :=
| Val (v : val)
| Block (t : mut_tag) (ls : list loc)
| Kont (k : outcome2 val exn → microvx)
| Shot.

(* A heap is a finite map of locations to memory blocks. Prophecies have no
   operational content, so the semantics does not track them: the set of
   allocated prophecy identifiers belongs to the program logic's store. *)

Abbreviation heap :=
  (gmap loc mem_block).

Implicit Type σ : heap.

Global Instance cont_eq_decision : EqDecision cont.
Proof. solve_decision. Defined.

Global Instance cont_countable : Countable cont.
Proof. unfold cont; simpl. apply locations.loc_countable. Defined.

Definition cont_store : Type :=
  tc_opaque (gmap cont mem_block).

Global Instance lookup_cont : Lookup cont mem_block cont_store :=
  (@gmap_lookup cont cont_eq_decision cont_countable mem_block).

Global Instance insert_cont : Insert cont mem_block cont_store.
Proof.
  unfold cont_store; simpl. unfold cont; simpl.
  change cont_eq_decision with loc_eq_decision.
  change cont_countable with loc_countable.
  apply map_insert.
Defined.

Lemma store_conversion : cont_store = heap.
Proof. reflexivity. Qed.


(* A configuration is a pair of a heap and a computation. *)

Definition config (A E : Type) : Type :=
  heap * micro A E.

(* This tactic explodes a configuration [c] into a pair [(σ, m)]. *)

Ltac destruct_config :=
  repeat match goal with c: config _ _ |- _ => destruct c end.

(* -------------------------------------------------------------------------- *)

(* A few technical tactics. *)

(* [exploit_location_lookup] rewrites an equality hypothesis [σ !! l = _]
   to rewrite in another hypothesis or in the goal, provided it mentions
   [σ !! l]. *)

Local Ltac exploit_location_lookup :=
  match goal with
  h1: ?σ !! ?l = _,
  h2: context[?σ !! ?l]
  |- _ =>
    rewrite h1 in h2
  |
  h1: ?σ !! ?l = _
  |- context[?σ !! ?l]
  =>
    rewrite h1
  end.

(* [case_location_lookup] finds an occurrence of [σ !! l] in a hypothesis or
   in the goal and performs a case analysis on [σ !! l], giving rise to 5
   cases (value block; block-of-memory block; ordinary continuation block;
   shot continuation block; nonexistent address). *)

Ltac case_location_lookup :=
  match goal with
  |- context[?σ !! ?l] =>
      let Hσ := fresh in
      destruct (σ !! l) as [ [ | | | ] |] eqn:Hσ
  | h: context[?σ !! ?l] |- _ =>
      let Hσ := fresh in
      destruct (σ !! l) as [ [ | | | ] |] eqn:Hσ
  end.

Create HintDb exploit_location_lookup.

Local Hint Extern 1 (_ = _) =>
  exploit_location_lookup
: exploit_location_lookup.

(* -------------------------------------------------------------------------- *)

(* [step_load σ l k] is the right-hand side of the reduction rule [StepLoad].

   The rule loads a value from the store [σ] at location [l] and returns it to
   the continuation [k]. It fails if this location is not in the domain of [σ]
   or contains something other than a value. *)

Definition step_load_2 {A E} σ (l : loc) (k : outcome2 val exn → _) : micro A E :=
  match σ !! l with
  | Some (Val v) => continue k v
  | _          => crash "load error: unbound location"
  end.

Abbreviation step_load σ l k :=
  (σ, step_load_2 σ l k).

(* [step_load_2] commutes with [try2]. This expresses the intuition that
   [step_load_2 σ l k] is parametric in the continuation [k]: it applies
   [k] without inspecting it. In other words, loading is an "algebraic"
   effect. *)

Lemma try2_step_load_2 {A E B F} σ l k (k' : outcome2 A E → micro B F) :
  try2 (step_load_2 σ l k) k' = step_load_2 σ l (pftry2 k k').
Proof.
  unfold step_load_2. intros. case_location_lookup; simplify_eq; eauto.
Qed.

(* [step_load_block σ l k] is the right-hand side of the reduction rule [StepLoadBlock].

   The rule loads a value from the store [σ] at location [l] and returns it to
   the continuation [k]. It fails if this location is not in the domain of [σ]
   or contains something other than a value. *)

Definition step_load_block_2 {A E} σ (l : loc) (k : outcome2 (mut_tag * list loc) exn → _) : micro A E :=
  match σ !! l with
  | Some (Block t ls) => continue k (t, ls)
  | _          => crash "load error: unbound location"
  end.

Abbreviation step_load_block σ l k :=
  (σ, step_load_block_2 σ l k).

(* [step_load_2] commutes with [try2]. This expresses the intuition that
   [step_load_2 σ l k] is parametric in the continuation [k]: it applies
   [k] without inspecting it. In other words, loading is an "algebraic"
   effect. *)

Lemma try2_step_load_block_2 {A E B F} σ l k (k' : outcome2 A E → micro B F) :
  try2 (step_load_block_2 σ l k) k' = step_load_block_2 σ l (pftry2 k k').
Proof.
  unfold step_load_block_2. intros. case_location_lookup; simplify_eq; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [step_exchange σ l v' k] is the right-hand side of the reduction rule [StepExchange].

   This rule loads a value [v] from the store [σ] at location [l], overwrites
   it with the value [v'], and returns [v] to the continuation [k].
   It fails if the location [l] is not in the domain of [σ] or contains
   something other than a value. *)

Definition step_exchange_1 σ l v' : heap :=
  match σ !! l with
  | Some (Val v) => <[ l := Val v' ]> σ
  | _          => σ
  end.

Definition step_exchange_2 {A E} σ l (k : outcome2 val exn → _) : micro A E :=
  match σ !! l with
  | Some (Val v) => continue k v
  | _          => crash "exchange error: unbound location"
  end.

Abbreviation step_exchange σ l v' k :=
  (step_exchange_1 σ l v', step_exchange_2 σ l k).

(* Storing is an algebraic effect. *)

Lemma try2_step_exchange_2 {A B E F} σ l
  (k : outcome2 val exn → micro A E)
  (k' : outcome2 A E → micro B F)
:
  step_exchange_2 σ l (pftry2 k k') = try2 (step_exchange_2 σ l k) k'.
Proof.
  unfold step_exchange_2. intros. case_location_lookup; simplify_eq; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [step_set_tag σ l t k] is the right-hand side of the reduction rule [StepSetTag].

   This rule looks up the memory block at location [l] in the store [σ], changes
   its mutability tag to [t], and returns unit to the continuation [k].
   It fails if [l] is not in the domain of [σ] or does not contain a [Block]. *)

Definition step_set_tag_1 σ l t : heap :=
  match σ !! l with
  | Some (Block _ ls) => <[ l := Block t ls ]> σ
  | _          => σ
  end.

Definition step_set_tag_2 {A E} σ l (k : outcome2 unit exn → _) : micro A E :=
  match σ !! l with
  | Some (Block _ _) => continue k ()
  | _          => crash "set_tag error: unbound location"
  end.

Abbreviation step_set_tag σ l t k :=
  (step_set_tag_1 σ l t, step_set_tag_2 σ l k).

(* Storing is an algebraic effect. *)

Lemma try2_step_set_tag_2 {A B E F} σ l
  (k : outcome2 unit exn → micro A E)
  (k' : outcome2 A E → micro B F)
:
  step_set_tag_2 σ l (pftry2 k k') = try2 (step_set_tag_2 σ l k) k'.
Proof.
  unfold step_set_tag_2. intros. case_location_lookup; simplify_eq; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [step_cas σ l seen v' k] is the right-hand side of the reduction rule [StepCAS].

   If [l] maps to a value [v] and [phys_eq_val_store v seen σ] holds, the
   rule overwrites [v] with [v'] and returns [VTrue]; if physical equality
   does not hold, [v] is left unchanged and [VFalse] is returned. It fails
   if [l] is not in the domain of [σ] or contains something other than a
   value, or if physical equality is undefined for the given values. *)

Definition phys_eq_val_store v1 v2 σ : option bool :=
  match v1, v2 with
  | VFieldLoc l1, VFieldLoc l2 =>
      Some (locations.eqb l1 l2)
  | VArray l1, VArray l2
  | VRecord l1, VRecord l2
  | VTaggedRecord _ l1, VTaggedRecord _ l2 =>
      match σ !! l1, σ !! l2 with
      | Some (Block Mut _), Some (Block _ _)
      | Some (Block _ _), Some (Block Mut _) => Some (locations.eqb l1 l2)
      | _, _ => None
      end
  | VCont k1, VCont k2 =>
      Some (locations.eqb k1 k2)
  | VData c1 [], VData c2 [] =>
      Some (c1 =? c2)%string
  | _, _ =>
      None
  end.

Definition step_cas_1 σ l seen (v' : val) : heap :=
  match σ !! l with
  | Some (Val v) =>
      match phys_eq_val_store v seen σ with
      | Some true => <[ l := Val v' ]> σ
      | _ => σ
      end
  | _           => σ
  end.

Definition step_cas_2 {A E} σ l seen (v' : val) (k : outcome2 val exn → _) : micro A E :=
  match σ !! l with
  | Some (Val v) => match phys_eq_val_store v seen σ with
                  | Some true => continue k VTrue
                  | Some false => continue k VFalse
                  | None => physical_equality_error "invalid or unsupported arguments"
                  end
  | _          => crash "store error: unbound location"
  end.

Abbreviation step_cas σ l seen v' k :=
  (step_cas_1 σ l seen v', step_cas_2 σ l seen v' k).

(* Comparing-and-setting is an algebraic effect. *)

Lemma try2_step_cas_2 {A B E F} σ l seen v'
  (k : outcome2 val exn → micro A E)
  (k' : outcome2 A E → micro B F)
:
  step_cas_2 σ l seen v' (pftry2 k k') = try2 (step_cas_2 σ l seen v' k) k'.
Proof.
  unfold step_cas_2. intros.
  case_location_lookup; simplify_eq; eauto.
  destruct (phys_eq_val_store v seen σ); eauto.
  destruct b; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [step_faa σ l i k] is the right-hand side of the reduction rule [StepFAA].

   This rule loads a value [j] from the store [σ] at location [l], overwrites
   it with the value [i + j], and returns [j] to the continuation [k].
   It fails if the location [l] is not in the domain of [σ] or contains
   something other than an int. *)

Definition step_faa_1 σ l (i : int) : heap :=
  match σ !! l with
  | Some (Val (VInt j)) =>
      <[ l := Val (VInt (int.add j i)) ]> σ
  | _           => σ
  end.

Definition step_faa_2 {A E} σ l (i : int) (k : outcome2 val exn → _) : micro A E :=
  match σ !! l with
  | Some (Val (VInt j)) =>
      continue k (VInt j)
  | _          => crash "store error: unbound location or not int"
  end.

Abbreviation step_faa σ l i k :=
  (step_faa_1 σ l i, step_faa_2 σ l i k).

(* Fetching-and-adding is an algebraic effect. *)

Lemma try2_step_faa_2 {A B E F} σ l i
  (k : outcome2 val exn → micro A E)
  (k' : outcome2 A E → micro B F)
:
  step_faa_2 σ l i (pftry2 k k') = try2 (step_faa_2 σ l i k) k'.
Proof.
  unfold step_faa_2. intros.
  case_location_lookup; simplify_eq; eauto.
  destruct v; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [step_resume σ l o] is the right-hand side of the rule [StepResume].

   This rule loads a continuation [sk] from the store [σ] at location [l],
   overwrites it with [Shot], and resumes [sk] with the outcome [o] -- so the
   result of resuming [sk] with [o] is returned to the continuation [k]. This
   rule fails if the location [l] is not in the domain of [σ] or contains
   something other than a continuation. *)

Definition step_resume_1 σ l :=
  match σ !! l with
  | Some (Kont sk) => <[l := Shot]> σ
  | _           => σ
  end.

Definition step_resume_2 {A E} σ l o k : micro A E :=
  match σ !! l with
  | Some (Kont sk) => try2 (sk o) k
  | _           => crash "resume error: unbound location"
  end.

Abbreviation step_resume σ l o k :=
  (step_resume_1 σ l, step_resume_2 σ l o k).

(* Resuming is an algebraic effect. *)

Create HintDb try_try.
Hint Extern 1 (_ = _) => rewrite try_try : try_try.
Hint Extern 1 (_ = _) => rewrite try2_try2 : try_try.

Lemma try2_step_resume_2 {A B E F} σ l o
  (k : _ → micro A E)
  (k' : outcome2 A E → micro B F)
:
  step_resume_2 σ l o (pftry2 k k') = try2 (step_resume_2 σ l o k) k'.
Proof.
  unfold step_resume_2. intros.
  case_location_lookup; simplify_eq; eauto with try_try.
Qed.

(* -------------------------------------------------------------------------- *)

(* [step_wrap σ l deep η bs l' k] is the right-hand side of the reduction
   rule [StepWrap]. *)

Definition step_wrap_1 σ l η bs l' :=
  <[l' := Kont (λ o, Handle (stop CResume (l, o)) (wrap_eval_branches η bs))]> σ.

Definition step_wrap_2 {A E} l' (k : outcome2 loc exn → _) : micro A E :=
  continue k l'.

Abbreviation step_wrap σ l η bs l' k :=
  (step_wrap_1 σ l η bs l', step_wrap_2 l' k).

Definition step_shallow_wrap_1 σ l η bs l' :=
  <[l' := Kont (λ o, Handle (stop CResume (l, o)) (shallow_eval_branches η bs bs))]> σ.

Abbreviation step_shallow_wrap σ l η bs l' k :=
  (step_shallow_wrap_1 σ l η bs l', step_wrap_2 l' k).

(* Installing is an algebraic effect. *)

Lemma try2_step_wrap_2 {A B E F} l'
  (k : _ → micro A E)
  (k' : outcome2 A E → micro B F)
:
  step_wrap_2 l' (pftry2 k k') = try2 (step_wrap_2 l' k) k'.
Proof.
  unfold step_wrap_2. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* A summary of our algebraicity laws. *)

Create HintDb try2_algebraic.

Global Hint Resolve
  try2_step_load_2
  try2_step_load_block_2
  try2_step_exchange_2
  try2_step_set_tag_2
  try2_step_cas_2
  try2_step_faa_2
  try2_step_resume_2
  try2_step_wrap_2
: try2_algebraic.


(* -------------------------------------------------------------------------- *)

(* The relation [step] is defined as follows. *)

(* [Ret a] and [Throw e] cannot step. They are results. *)

(* [Crash] cannot step. *)

(* [Stop CPerf e k] cannot step by itself. If it appears in the scope of
   [Handle] then it can step. *)

(* The reduction rules are designed so that [Handle] and [Par] can always
   step. There is a lot of non-determinism in the reduction of [Par]. *)

Inductive step {A E} : config A E → config A E → Prop :=

  (* [Stop CEval (η, e) k] steps to an invocation of [eval η e] under
     [try2 _ k]. Thus, from the user's perspective, the computation
     [stop CEval (η, e)] behaves just like [eval η e]. *)
  | StepEval :
      ∀ σ η e k,
      step
        (σ, Stop CEval (η, e) k)
        (σ, try2 (eval η e) k)

  (* [Stop CReturn w k] does nothing and returns [w]. Its only purpose is
     to give a resolution a step to happen at; see [CReturn] in code.v. *)
  | StepReturn :
      ∀ σ w k,
      step
        (σ, Stop CReturn w k)
        (σ, continue k w)

  (* [stop (η, x, i1, i2, e)] behaves like [loop η x i1 i2 e]. *)
  | StepLoop :
      ∀ σ η x i1 i2 e k,
      step
        (σ, Stop CLoop (η, x, i1, i2, e) k)
        (σ, try2 (loop η x i1 i2 e) k)

  (* [stop CFlip ()] returns either [false] or [true]. *)
  | StepFlip :
      ∀ b σ x k,
      step
        (σ, Stop CFlip x k)
        (σ, continue k b)

  (* [stop CAlloc v] allocates a fresh location in the heap,
     initializes it with the value [v], and returns the location. *)
  | StepAlloc :
      ∀ σ v l k,
      σ !! l = None →
      step
        (σ, Stop CAlloc v k)
        (<[ l := Val v ]> σ, continue k l)

  | StepAllocBlock :
    ∀ σ t ls l k,
      σ !! l = None →
      step
        (σ, Stop CAllocBlock (t, ls) k)
        (<[ l := Block t ls ]> σ, continue k l)

  (* If the location [l] exists and contains a value [v], then
     [stop CLoad l] returns this value; otherwise, it crashes. *)
  | StepLoad :
      ∀ σ l k c',
      c' = step_load σ l k →
      step
        (σ, Stop CLoad l k)
        c'

  | StepLoadBlock :
    ∀ σ l k c',
    c' = step_load_block σ l k →
    step
      (σ, Stop CLoadBlock l k)
      c'

  (* If the location [l] exists and contains a value [v], then
     [stop CExchange (l, v')] overwrites this value with [v'];
     otherwise, it crashes. *)
  | StepExchange :
      ∀ σ l v' k c',
      c' = step_exchange σ l v' k →
      step
        (σ, Stop CExchange (l, v') k)
        c'

  | StepSetTag :
      ∀ σ l t k c',
      c' = step_set_tag σ l t k →
      step
        (σ, Stop CSetBlockTag (l, t) k)
        c'

  | StepCAS :
      ∀ σ l seen v k c',
      c' = step_cas σ l seen v k →
      step
        (σ, Stop CCAS (l, seen, v) k)
        c'

  | StepFAA :
      ∀ σ l i k c',
      c' = step_faa σ l i k →
      step
        (σ, Stop CFAA (l, i) k)
        c'

  (* If [Handle _ h] observes a normal result [ret v] then it reduces to an
     application of the first arm of the handler [h] to the value [v]. *)
  | StepHandleRet :
      ∀ σ v h,
      step
        (σ, Handle (Ret v) h)
        (σ, h (O3Ret v))

  (* If [Handle _ h] observes an exception [throw e] then it reduces to an
     application of the second arm of the handler [h] to the exception [e]. *)
  | StepHandleThrow :
      ∀ σ e h,
      step
        (σ, Handle (Throw e) h)
        (σ, h (O3Throw e))

  (* If [Handle _ h] observes an effect [perform e k] then it captures the
     continuation [k], which becomes stored at a fresh address [l] in the
     heap. Then, it reduces to an application of the third arm of the
     handler [h] to the effect [e] and to the location [l]. *)
  | StepHandlePerform :
      ∀ σ e k h l,
      σ !! l = None →
      step
        (σ, Handle (Stop CPerf e k) h)
        (<[l := Kont k]> σ, h (O3Perform e l))

  | StepHandleFork :
    ∀ σ x k h,
      step
        (σ, Handle (Stop CFork x k) h)
        (σ, Stop CFork x (λ o, Handle (k o) h))

  | StepHandleJoin :
    ∀ σ ι k h,
      step
        (σ, Handle (Stop CJoin ι k) h)
        (σ, Stop CJoin ι (λ o, Handle (k o) h))

  (* A resolution floats out of [Handle] for the same reason a fork does:
     the step that gives it meaning lives in [subjective_step], so it must
     reach the top of its thread. *)
  | StepHandleResolve :
    ∀ {X} σ (c : code X val exn) y k h,
      step
        (σ, Handle (Stop (CResolve c) y k) h)
        (σ, Stop (CResolve c) y (λ o, Handle (k o) h))

  (* The allocation of a prophecy floats out for the same reason: the set of
     allocated identifiers is not part of the heap. *)
  | StepHandleNewProph :
    ∀ σ x k h,
      step
        (σ, Handle (Stop CNewProph x k) h)
        (σ, Stop CNewProph x (λ o, Handle (k o) h))

  (* If [Handle _ h] observes a crash then this crash is propagated. *)
  | StepHandleCrash :
      ∀ σ h,
      step
        (σ, Handle Crash h)
        (σ, Crash)

  (* Reduction under [Handle _ h] is permitted. *)
  | StepHandleLeft :
      ∀ σ σ' m m' h,
      step (σ, m) (σ', m') →
      step (σ, Handle m h) (σ', Handle m' h)

  (* [stop Resume (l, o)] reads the continuation [sk] that is stored
     at address [l] in the heap, updates [l] to [Shot], and resumes the
     continuation [sk] with the outcome [o]. *)
  | StepResume :
      ∀ σ l o k c',
      c' = step_resume σ l o k →
      step
        (σ, Stop CResume (l, o) k)
        c'

  (* [stop CWrap (deep, l, η, bs)] wraps the continuation that is currently
     stored at address [l] in an effect handler described by [deep], [η], and
     [bs]. This results in a new continuation, which is stored in the heap at
     a fresh location [l']. This location is returned. *)
  | StepWrap :
      ∀ σ l η bs k l' c',
      σ !! l' = None →
      c' = step_wrap σ l η bs l' k →
      step
        (σ, Stop CWrap (true, l, η, bs) k)
        c'
  | StepShallowWrap :
      ∀ σ l η bs k l' c',
      σ !! l' = None →
      c' = step_shallow_wrap σ l η bs l' k →
      step
        (σ, Stop CWrap (false, l, η, bs) k)
        c'

  (* If [m1] and [m2] have reached values [v1] and [v2],
     then the continuation [k] is applied to the pair [(v1, v2)]. *)
  | StepParRetRet :
      ∀ {A1 A2 E'} σ v1 v2 (k : outcome2 (A1 * A2) E' → _),
      step
        (σ, Par (Ret v1) (Ret v2) k)
        (σ, continue k (v1, v2))

  (* A hard failure on either side can be propagated up. *)
  | StepParCrashLeft :
      ∀ {A1 A2 E'} σ m2 (k : outcome2 (A1 * A2) E' → _),
      step
        (σ, Par Crash m2 k)
        (σ, Crash)

  | StepParCrashRight :
      ∀ {A1 A2 E'} σ m1 (k : outcome2 (A1 * A2) E' → _),
      step
        (σ, Par m1 Crash k)
        (σ, Crash)

  (* If a soft failure on either side is detected, then
     the failure component of the continuation [k] can be invoked. *)
  | StepParThrowLeft :
      ∀ {A1 A2 E'} σ m2 e (k : outcome2 (A1 * A2) E' → _),
      step
        (σ, Par (Throw e) m2 k)
        (σ, discontinue k e)

  | StepParThrowRight :
      ∀ {A1 A2 E'} σ m1 e (k : outcome2 (A1 * A2) E' → _),
      step
        (σ, Par m1 (Throw e) k)
        (σ, discontinue k e)

  (* If [Stop (perform e) k] appears under the context [Par _ m2 h] then
     it can capture this evaluation context frame. Thus, it reduces to a
     new term where [Stop (perform e) _] now appears naked and the captured
     evaluation context is [Par (k _) m2 h]. *)
  | StepThroughParLeft :
    ∀ {X Y E A1 A2 E'} σ m2 (c : code X Y E) x k (h : outcome2 (A1 * A2) E' -> _),
      step_through_par_code c ->
      step
        (σ, Par (Stop c x k) m2 h)
        (σ, Stop c x (λ o, Par (k o) m2 h))

  | StepThroughParRight :
    ∀ {X Y E A1 A2 E'} σ m1 (c : code X Y E) x k (h : outcome2 (A1 * A2) E' -> _),
      step_through_par_code c ->
      step
        (σ, Par m1 (Stop c x k) h)
        (σ, Stop c x (λ o, Par m1 (k o) h))

  (* Reduction steps on either side are permitted. *)
  | StepParLeft :
      ∀ {A1 A2 E'} σ σ' m1 m'1 m2 (k : outcome2 (A1 * A2) E' → _),
      step (σ, m1) (σ', m'1) →
      step
        (σ, Par m1 m2 k)
        (σ', Par m'1 m2 k)

  | StepParRight :
      ∀ {A1 A2 E'} σ σ' m1 m2 m'2 (k : outcome2 (A1 * A2) E' → _),
      step (σ, m2) (σ', m'2) →
      step
        (σ, Par m1 m2 k)
        (σ', Par m1 m'2 k)
.

(* Note: we considered removing the [StepParLeft] and [StepParRight] rules,
   and replacing them with stronger versions of the [StepThroughPar] rules.

   However, this would make computations like [Par (Handle m k) m2] and
   [Par (Par m1 m2) m3] stuck. *)

Create HintDb step.

Global Hint Constructors step : step.

Ltac destruct_step :=
  (* For some reason, [dependent destruction] does not like it when
     the argument [x] of [Stop] is not a variable. *)
  try lazymatch goal with
    | h: step (?σ, Stop ?c ?x ?k) ?m' |- _ =>
          remember x
    | h: step (?σ, stop ?c ?x) ?m' |- _ =>
        remember x
  end;
  lazymatch goal with h: step ?m ?m' |- _ =>
    dependent destruction h
  end.

(* -------------------------------------------------------------------------- *)

Section threadpool.

  Definition thpool : Type := gmap thread (micro val exn).

  Implicit Type ι : thread.

  Global Instance lookup_thpool : Lookup thread (microvx) (thpool).
  Proof.
    apply gmap_lookup.
  Defined.

  Global Instance insert_thpool : Insert thread (microvx) (thpool).
  Proof.
    apply _.
  Defined.

  Definition tconfig := (heap * thpool)%type.

  Definition attempt_join {A E} ι π (k : outcome2 val exn -> micro A E) :=
    match @lookup _ _ _ lookup_thpool ι π with
    (* Joining a thread which has terminated. *)
    | Some m =>
        match m with
        (* If the joined thread terminated sucessfully, continue with unit. *)
        | Ret v => Some (continue k v)
        (* If the joined thread raised an exception, re-raise the exception. *)
        | Throw ex => Some (discontinue k ex)
        (* We do not step while attempting to join an active thread. *)
        | _ => None
        end
    (* Attempting to join an invalid thread results in a [crash]. *)
    | None => Some (crash "join invalid thread")
    end.

  (* The semantic model for concurrency via a pool of threads. *)

  Inductive threadpool_step : tconfig -> tconfig -> Prop :=
  | BaseTS :
    ∀ ι π m σ m' σ',
      π !! ι = Some m ->
      step (σ, m) (σ', m') ->
      threadpool_step (σ, π) (σ', <[ ι := m' ]> π)
  | ForkTS :
    ∀ ι π ι' v1 v2 k σ,
      π !! ι = Some (Stop CFork (v1, v2) k) ->
      π !! ι' = None ->
      threadpool_step
        (σ, π)
        (σ, @insert _ _ _ insert_thpool ι' (call v1 v2) (
                @insert _ _ _ insert_thpool ι (continue k (VThread ι')) π))
  | JoinTS :
    ∀ ι π ι' k m σ,
      π !! ι = Some (Stop CJoin ι' k) ->
      attempt_join ι' π k = Some m ->
      threadpool_step
        (σ, π)
        (σ, <[ ι := m ]> π)
  .

End threadpool.

Abbreviation threadpool_steps := (nsteps threadpool_step).

(* -------------------------------------------------------------------------- *)

(* Some derived rules. *)

Lemma StepLoadSuccess {A E} σ (l : loc) (k : outcome2 val exn → micro A E) v :
  σ !! l = Some (Val v) →
  step
    (σ, Stop CLoad l k)
    (σ, continue k v).
Proof.
  intros Heq. econstructor. unfold step_load_2.
  rewrite Heq. eauto.
Qed.

Lemma StepExchangeSuccess {A E} σ (l : loc) v v' (k : outcome2 val exn → micro A E) :
  σ !! l = Some (Val v) →
  step
    (σ, Stop CExchange (l, v') k)
    (<[ l := Val v' ]> σ, continue k v).
Proof.
  intros Heq. econstructor. unfold step_exchange_1, step_exchange_2.
  rewrite Heq. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* [is_ret m] is [Some a] if and only if [m] is [Ret a]. *)

(* [is_ret] offers an executable way of testing whether a computation is
   [Ret _]. *)

Definition is_ret {A E} (m : micro A E) : option A :=
  match m with
  | Ret a => Some a
  | _     => None
  end.

(* Basic properties of [is_ret]. *)

Lemma invert_is_ret_Some {A E} {m : micro A E} {a} :
  is_ret m = Some a →
  m = Ret a.
Proof.
  destruct m; inversion 1; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

Definition is_result {A E} (m : micro A E) : Prop :=
  match m with
  | Ret _ | Throw _ | Crash => True
  | _ => False
  end.

(* Recovering the shape for the proofs that must treat the cases
   differently. A result is either an [outcome2] or a crash. *)

Lemma is_result_inv {A E} (m : micro A E) :
  is_result m → (∃ o, m = inject2 o) ∨ m = Crash.
Proof.
  destruct m; simpl; try done;
    [ left; by exists (O2Ret a) | left; by exists (O2Throw e) | by right ].
Qed.

(* Consuming the [is_result] hypothesis a resolution rule leaves behind, and
   substituting the shape it reveals throughout. *)

Tactic Notation "destruct_is_result" simple_intropattern(p) :=
  match goal with
  | Hr : is_result _ |- _ =>
      destruct (is_result_inv _ Hr) as [ (p & ->) | -> ]
  end.

(* The observation a resolution emits, given the outcome its call reached. *)

Definition resolve_obs (p : proph_id) (v : val) (b : microvx) : list observation :=
  match b with
  | Ret w => [(p, (w, v))]
  | _ => []
  end.

(* -------------------------------------------------------------------------- *)

(* [is_not_ret m] holds if [m] is not [ret _]. *)

Abbreviation is_not_ret m :=
  (is_ret m = None).

(* -------------------------------------------------------------------------- *)

(* Basic properties of [is_not_ret]. *)

Lemma is_not_ret_ret {A E} (a : A) :
  is_not_ret (ret a : micro A E) →
  False.
Proof.
  simpl. congruence.
Qed.

Lemma is_not_ret_bind {A B E} (m : micro A E) (f : A → micro B E) :
  is_not_ret m →
  is_not_ret (bind m f).
Proof.
  destruct m; simpl; congruence.
Qed.

(* -------------------------------------------------------------------------- *)

(* [is_throw m] is [Some a] if and only if [m] is [Throw a]. *)

(* [is_throw] offers an executable way of testing whether a computation is
   [Throw _]. *)

Definition is_throw {A B} (m : micro A B) : option B :=
  match m with
  | Throw a => Some a
  | _       => None
  end.

(* Basic properties of [is_throw]. *)

Lemma invert_is_throw_Some {A E} {m : micro A E} {a} :
  is_throw m = Some a →
  m = Throw a.
Proof.
  destruct m; inversion 1; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* [is_not_throw m] holds if [m] is not [throw _]. *)

Abbreviation is_not_throw m :=
  (is_throw m = None).

(* -------------------------------------------------------------------------- *)

(* Basic properties of [is_not_throw]. *)

Lemma is_not_throw_throw {A E} (a : E) :
  is_not_throw (throw a : micro A E) →
  False.
Proof.
  simpl. congruence.
Qed.

Lemma is_not_throw_ret {A E} (e : A) :
  is_not_throw (ret e : micro A E).
Proof.
  reflexivity.
Qed.

Lemma is_not_throw_crash {A E} :
  is_not_throw (Crash : micro A E).
Proof.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

(* [c] can step if there exists [c'] such that [c] steps to [c']. *)

Definition can_step {A E} (c : config A E) :=
  ∃ c', step c c'.

Global Hint Unfold can_step : step.

Ltac destruct_can_step :=
  match goal with
  | h: can_step _ |- _ =>
      destruct h as ((? & ?) & ?)
  end.

(* -------------------------------------------------------------------------- *)

(* Basic lemmas about [step] and [can_step]. *)

(* [Ret a] cannot step. *)

Lemma invert_can_step_Ret {A E} σ a :
  can_step ((σ, Ret a) : config A E) →
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

(* [Crash] cannot step. *)

Lemma invert_can_step_Crash {A E} σ :
  can_step ((σ, Crash) : config A E) →
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

(* [throw e] cannot step. *)

Lemma invert_can_step_Throw {A E} σ e :
  can_step ((σ, throw e) : config A E) →
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

(* [perform e] cannot step. *)

Lemma invert_can_step_perform σ e :
  can_step (σ, perform e) →
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

Lemma invert_can_step_fork {A E} σ v1 v2 (k : _ -> micro A E) :
  can_step (σ, (Stop CFork (v1, v2) k)) ->
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

Lemma invert_can_step_join {A E} σ ι (k : _ -> micro A E) :
  can_step (σ, (Stop CJoin ι k)) ->
  False.
Proof.
  intros. destruct_can_step. destruct_step.
Qed.

(* A resolution has no sequential step either: the step that gives it
   meaning lives in [subjective_step], where it emits an observation. *)
Lemma invert_can_step_resolve {A E X} σ (c : code X val exn) y (k : _ -> micro A E) :
  can_step (σ, (Stop (CResolve c) y k)) ->
  False.
Proof.
  intros. destruct_can_step. inversion H.
Qed.

Lemma invert_can_step_new_proph {A E} σ x (k : _ -> micro A E) :
  can_step (σ, (Stop CNewProph x k)) ->
  False.
Proof.
  intros. destruct_can_step. inversion H.
Qed.

Create HintDb invert_can_step.

Global Hint Resolve
  invert_can_step_Ret
  invert_can_step_Crash
  invert_can_step_Throw
  invert_can_step_perform
  invert_can_step_fork
  invert_can_step_join
  invert_can_step_new_proph
  invert_can_step_resolve
: invert_can_step.

(* -------------------------------------------------------------------------- *)

(* If the location [l] exists in the store and contains a value,
   then [stop CLoad l] can step in only one way. *)

Lemma invert_step_load {A E} σ σ' l v k m' :
  σ !! l = Some (Val v) →
  @step A E (σ, Stop CLoad l k) (σ', m') →
  σ' = σ ∧
  m' = continue k v.
Proof.
  intros Heq Hstep. destruct_step.
  unfold step_load_2. rewrite Heq.
  eauto.
Qed.

(* If the location [l] exists in the store and contains a value,
   then [stop CExchange (l, v')] can step in only one way. *)

Lemma invert_step_exchange {A E} σ l v' v k σ' m' :
  σ !! l = Some (Val v) →
  @step A E (σ, Stop CExchange (l, v') k) (σ', m') →
  σ' = <[ l := Val v' ]> σ ∧
  m' = continue k v.
Proof.
  intros Heq Hstep. destruct_step.
  unfold step_exchange_1, step_exchange_2. rewrite Heq.
  eauto.
Qed.

(* If the location [l] exists in the store and contains a continuation,
   then [stop CResume (l, o)] can step in only one way. *)

Lemma invert_step_resume {A E} σ σ' (l : cont) o k sk m' :
  (σ : cont_store) !! l = Some (Kont sk) →
  @step A E (σ, Stop CResume (l, o) k) (σ', m') →
  σ' = <[ l := Shot ]> (σ : cont_store) ∧
  m' = try2 (sk o) k.
Proof.
  intros Heq Hstep. destruct_step.
  unfold step_resume_1, step_resume_2.
  assert (Heq' : σ !! (l : loc) = Some (Kont sk)) by exact Heq.
  rewrite Heq'.
  eauto.
Qed.

Lemma invert_step_resume_shot {A E} σ σ' (l : cont) o k m' :
  (σ : cont_store) !! l = Some Shot →
  @step A E (σ, Stop CResume (l, o) k) (σ', m') →
  σ = σ' /\
  ∃ s, m' = crash s.
Proof.
  intros Heq Hstep.
  destruct_step.
  unfold step_resume_1, step_resume_2.
  assert (Heq' : σ !! (l : loc) = Some Shot) by exact Heq.
  rewrite Heq'.
  eauto.
Qed.

(* [stop CInstall (deep, l, η, bs)] can step in only one way. *)

Lemma invert_step_wrap_deep {A E} σ σ' l η bs k m' :
  @step A E (σ, Stop CWrap (true, l, η, bs) k) (σ', m') →
  ∃ l',
  σ !! l' = None ∧
    σ' = <[ l' := Kont (λ o, Handle (stop CResume (l, o))
                            (wrap_eval_branches η bs)) ]> σ ∧
  m' = continue k l'.
Proof.
  intros Hstep. destruct_step.
  unfold step_wrap_1, step_wrap_2.
  eauto.
Qed.

Lemma invert_step_wrap_shallow {A E} σ σ' l η bs k m' :
  @step A E (σ, Stop CWrap (false, l, η, bs) k) (σ', m') →
  ∃ l',
  σ !! l' = None ∧
    σ' = <[ l' := Kont (λ o, Handle (stop CResume (l, o))
                            (shallow_eval_branches η bs bs)) ]> σ ∧
  m' = continue k l'.
Proof.
  intros Hstep. destruct_step.
  unfold step_wrap_1, step_wrap_2.
  eauto.
Qed.

Lemma invert_step_alloc {A E} σ σ' v k m' :
  @step A E (σ, Stop CAlloc v k) (σ', m') →
  ∃ l,
    σ !! l = None ∧
    σ' = <[ l := Val v ]> σ ∧
    m' = continue k l.
  Proof.
    intros Hstep. destruct_step.
    eexists. eauto.
  Qed.

Lemma invert_step_alloc_block {A E} σ σ' t ls k m' :
  @step A E (σ, Stop CAllocBlock (t, ls) k) (σ', m') →
  ∃ l,
    σ !! l = None ∧
    σ' = <[ l := Block t ls ]> σ ∧
    m' = continue k l.
  Proof.
    intros Hstep. destruct_step.
    eexists. eauto.
  Qed.

(* A term that can step is not [ret _]. *)

Lemma can_step_is_not_ret {A E} σ m :
  can_step ((σ, m) : config A E) →
  is_not_ret m.
Proof.
  intros.
  destruct m; solve [ exfalso; eauto with invert_can_step | simpl; tauto ].
Qed.

(* If [c] is not [CPerf _] or a concurrent step, [Stop c x k] can step. *)

Lemma can_step_stop {A X Y E' E}
  σ (c : code X Y E') x (k : outcome2 Y E' → _) :
  match c with | CPerf | CNewProph | CResolve _ => False | _ => True end ∧
  not (is_concurrent_code c) ->
  can_step ((σ, Stop c x k) : config A E).
Proof.
  destruct c; repeat destruct x as (x & ?); try destruct o;
  (* Get rid of [CPerf]. *)
  first [ tauto | intros _ ];
  (* Deal with all remaining cases except [CFlip], [CAlloc], [CInstall]. *)
  eauto using StepLoad with step.
  (* In the case of allocation, we must exhibit an address [l]
     that is not in the domain of [σ]. *)
  { eexists. apply StepAlloc.
    apply not_elem_of_dom.
    apply is_fresh. }
  { eexists. apply StepAllocBlock.
    eapply not_elem_of_dom.
    apply is_fresh. }
  (* In the case of wrap, we must also exhibit an address [l]
     that is not in the domain of [σ]. *)
  { set (l' := fresh (dom σ)).
    assert (σ !! l' = None) by apply not_elem_of_dom, is_fresh.
    destruct x;
      eauto using StepWrap, StepShallowWrap with step. }
  (* For [CFlip], we need to provide a boolean. *)
  Unshelve. refine true.
Qed.

Global Hint Resolve can_step_stop : step.

(* The following two auxiliary lemmas are used in the proof of
   [can_step_handle_par], which establishes a stronger result. *)

Local Lemma can_step_under_handle {A E} σ m h :
  can_step (σ, m) →
  can_step ((σ, Handle m h) : config A E).
Proof.
  intros; destruct_can_step; eauto using StepHandleLeft with step.
Qed.

Local Lemma can_step_under_par {A1 A2 A E' E}
  σ m1 m2 (k : outcome2 (A1 * A2) E' → _) :
  can_step (σ, m1) ∨ can_step (σ, m2) →
  can_step ((σ, Par m1 m2 k) : config A E).
Proof.
  intros [|]; destruct_can_step;
  eauto using StepParLeft, StepParRight with step.
Qed.

(* [Handle] and [Par] can step. *)

Lemma can_step_handle_par :
  ∀ {A E} (m : micro A E),
    match m with | Handle _ _ | Par _ _ _ => True | _ => False end →
  ∀ σ,
  can_step (σ, m).
Proof.
  induction m; try tauto; intros _ σ.
  (* We get two goals, [Handle] and [Par]. *)

  (* Case: [Handle]. *)
  {
    (* Clear the (useless) second induction hypothesis. *)
    clear H.
    (* Analyze [m]; analyze [c]. *)
    destruct m; eauto using can_step_under_handle with step.
    destruct c; eauto using can_step_under_handle with step.
    (* We are now looking at [perform] under [handle]. *)
    (* An allocation is involved, so (again) we must exhibit
       an address [l] that is not in the domain of [σ]. *)
    set (l := fresh (dom σ)).
    assert (σ !! l = None) by apply not_elem_of_dom, is_fresh.
    (* At this point, the reduction rule [StepHandlePerform] is
       exploited. It is worth noting that this rule can be used
       only if the computation that is being handled has type
       [micro val exn], as opposed to [micro A E]. This explains
       why the [Handle] construct is restricted to this case. *)
    eauto using StepHandlePerform with step.
  }

  (* Case: [Par]. *)
  {
    (* Analyze [m1]. *)
    destruct m1; eauto using can_step_under_par with step.
    + (* Analyze [m2]. *)
      destruct m2; eauto using can_step_under_par with step.
      (* We are now looking at [Stop] under [Par]. *)
      destruct c; eauto 6 using can_step_under_par with step;
        (* All the remaining codes are concurrent. *)
        by eexists; eapply StepThroughParRight.
    + (* We are now looking at [Stop] under [Par]. *)
      destruct c; eauto 6 using can_step_under_par with step;
        by eexists; eapply StepThroughParLeft.
  }

Qed.

(* Corollaries: [Handle] can step; [Par] can step. *)

Lemma can_step_handle {A E} σ m h :
  can_step ((σ, Handle m h) : config A E).
Proof.
  eauto using can_step_handle_par.
Qed.

Lemma can_step_par
  {A E A1 A2 E'} σ m1 m2 (k : outcome2 (A1 * A2) E' → _) :
  can_step ((σ, Par m1 m2 k) : config A E).
Proof.
  eauto using can_step_handle_par.
Qed.

Global Hint Resolve
  can_step_handle can_step_par
: step.

(* Stepping in the left-hand side of [try2] is permitted. *)

(* This corresponds to reduction under an evaluation context. *)

Lemma step_try2 {A B E' E} σ σ' m m' (h : outcome2 A E' → micro B E) :
  step (σ, m) (σ', m') →
  step (σ, try2 m h) (σ', try2 m' h).
Proof.
  inversion 1;
  simplify_eq;
  simpl try2;
  rewrite ?try2_try2;
  eauto with step try2_algebraic f_equal.
  rewrite try2_continue; constructor.
Qed.

(* As special cases, stepping under [try] or [bind] is also permitted. *)

Lemma step_try {A B E' E} σ σ' m m' (f : A → micro B E) (h : E' → _) :
  step (σ, m) (σ', m') →
  step (σ, try m f h) (σ', try m' f h).
Proof.
  eauto using step_try2.
Qed.

Lemma step_bind {A B E} σ σ' m m' (f : A → micro B E) :
  step (σ, m) (σ', m') →
  step (σ, bind m f) (σ', bind m' f).
Proof.
  rewrite !bind_as_try. eauto using step_try.
Qed.

(* Corollaries. *)

Lemma can_step_try2 {A B E' E} σ m (h : outcome2 A E' → micro B E) :
  can_step (σ, m) →
  can_step (σ, try2 m h).
Proof.
  unfold can_step. intros ([] & Hstep). eauto using step_try2.
Qed.

Lemma can_step_try {A B E' E} σ m (f : A → micro B E) (h : E' → _) :
  can_step (σ, m) →
  can_step (σ, try m f h).
Proof.
  unfold can_step. intros ([] & Hstep). eauto using step_try.
Qed.

Lemma can_step_bind {A B E} σ m (f : A → micro B E) :
  can_step (σ, m) →
  can_step (σ, bind m f).
Proof.
  rewrite bind_as_try. eauto using can_step_try.
Qed.

Create HintDb can_step.

Global Hint Resolve can_step_try2 can_step_try can_step_bind : can_step.

(* If [try m f h] takes a step, and if [m] can step, then the step taken by
   [try m f h] must a step of [m] under the context [try _ f h]. *)

(* In other words, reduction under a context is mandatory: no other reduction
   is possible. *)

Lemma invert_step_try2 {A B E' E σ} {m} {h : outcome2 A E' → micro B E} {σ' mm} :
  step (σ, try2 m h) (σ', mm) →
  can_step (σ, m) →
  (∃ m', step (σ, m) (σ', m') ∧ mm = try2 m' h).
Proof.
  destruct m;
  simpl try2;
  intros;
  (* Case: [Ret] *)
  try solve [ exfalso; eauto with invert_can_step ];
  (* Every other case: *)
  destruct_step;
  eauto with step try2_algebraic try_try.
Qed.

Lemma invert_step_try {A B E' E σ} {m} {f : A → micro B E} {h : E' → _} {σ' mm} :
  step (σ, try m f h) (σ', mm) →
  can_step (σ, m) →
  (∃ m', step (σ, m) (σ', m') ∧ mm = try m' f h).
Proof.
  eauto using invert_step_try2.
Qed.

(* A stronger version of the following lemma is proved later on. *)

Lemma invert_step_bind_weak {A B E σ} {m} {f : A → micro B E} {σ' mm} :
  step (σ, bind m f) (σ', mm) →
  can_step (σ, m) →
  (∃ m', step (σ, m) (σ', m') ∧ mm = bind m' f).
Proof.
  intros Hstep Hcan.
  rewrite bind_as_try in Hstep.
  destruct (invert_step_try Hstep Hcan) as (m' & ? & ?). subst mm.
  exists m'. rewrite bind_as_try. eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* More properties of [is_not_ret]. *)

Lemma is_not_ret_try {A B E' E σ} m (f : A → micro B E) (h : E' → _) :
  can_step (σ, m) →
  is_not_ret (try m f h).
Proof.
  destruct m; simpl; intros;
  solve [ eauto | exfalso; eauto with invert_can_step ].
Qed.

(* -------------------------------------------------------------------------- *)

(* A resolution never steps on its own: the step that gives it meaning
   belongs to [subjective_step]. The program-logic rules use this to discharge
   an impossible [step] hypothesis. *)

Lemma no_step_Resolve {A E X} σ (c : code X val exn) y k σ' m' :
  ¬ step ((σ, Stop (CResolve c) y k) : config A E) (σ', m').
Proof. inversion 1. Qed.

(* Nor does the allocation of a prophecy. *)

Lemma no_step_NewProph {A E} σ x k σ' m' :
  ¬ step ((σ, Stop CNewProph x k) : config A E) (σ', m').
Proof. inversion 1. Qed.

(* -------------------------------------------------------------------------- *)

(* Every computation is either a result, one of the five codes whose step
   belongs to the pool, or able to step on its own. *)

Lemma only_crash_and_throw_and_perform_and_concurrent_are_stuck' {A E} σ (m : micro A E) :
  match m with
  | Ret _ | Crash | Throw _
  | Stop CPerf _ _ | Stop CFork _ _ | Stop CJoin _ _
  | Stop CNewProph _ _ | Stop (CResolve _) _ _ =>
      True
  | _ =>
      can_step (σ, m)
  end.
Proof.
  destruct m; eauto with step.
  destruct_code; eauto with step.
Qed.

(* The following lemma is a stronger version of [invert_step_bind_weak].
   It requires just [is_not_ret m] instead of [can_step (_, m)]. *)

Lemma invert_step_bind {A B E σ m} {f : A → micro B E} {σ' mm} :
  step (σ, bind m f) (σ', mm) →
  is_not_ret m →
  (∃ m', step (σ, m) (σ', m') ∧ mm = bind m' f).
Proof.
  intros.
  destruct m; intros; try destruct_code;
  (* This takes care of the cases covered by the weak lemma: *)
  eauto using invert_step_bind_weak with step;
  (* The remaining cases are [ret _] and the stuck terms. *)
  simpl in *; solve [ congruence | destruct_step ].
Qed.

(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)

Definition steps {A E} := @nsteps (config A E) step.

Create HintDb steps.

Global Hint Unfold steps : steps.
Global Hint Constructors nsteps : steps.

Definition produces {A E} n (m : micro A E) σ a :=
  steps n (σ, m) (σ, Ret a).

Global Hint Unfold produces : steps.

(* -------------------------------------------------------------------------- *)

(* Lemmas about [produces]. *)

(* [step] and [produces] can be composed. *)

Lemma step_produces {A E} n (m m' : micro A E) σ a :
  step (σ, m) (σ, m') →
  produces n m' σ a →
  produces (S n) m σ a.
Proof.
  unfold produces. econstructor; eauto.
Qed.

Global Hint Resolve step_produces : steps.
