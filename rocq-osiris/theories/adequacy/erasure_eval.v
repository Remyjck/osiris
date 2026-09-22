From osiris.utils Require Import base list_z.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics strategy.
Require Import erasure.

(* -------------------------------------------------------------------------- *)

(** * The erasure commutes with the interpreter. *)

(* This file proves
   [erase_eval : (∀ η, erase_microvx
                         (eval η e)
                         (eval (erase_env η) (erase_expr e)))]

   [erase_eval] ties the erasure of computations to the erasure of
   syntax. Running the erasure of a program is running the erased
   program. *)

Fixpoint erase_fvals (fvs : list (field * val)) : list (field * val) :=
  match fvs with
  | [] => []
  | (f, v) :: fvs => (f, erase_val v) :: erase_fvals fvs
  end.

Definition erase_envs : envs → envs := prod_map erase_env erase_env.

(* -------------------------------------------------------------------------- *)

(** ** Value coercions. *)

(* Every [val_as_X] inspects the head constructor of a value and either
   returns a component of it or crashes. A prophecy crashes where its
   erasure, a location, may not. *)

Local Ltac erase_val_as v :=
  destruct v; simpl; repeat case_match;
    first [ apply EM_Crash | apply EM_Ret | apply EM_CrashL ].

Lemma erase_val_as_loc {E} (fE : E → E) v :
  erase_micro id fE (val_as_loc v) (val_as_loc (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_val_as_int (v : val) :
  erase_micro id erase_val (val_as_int v) (val_as_int (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_val_as_bool (v : val) :
  erase_micro id erase_val (val_as_bool v) (val_as_bool (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_val_as_thread {E} (fE : E → E) v :
  erase_micro id fE (val_as_thread v) (val_as_thread (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_val_as_cont {E} (fE : E → E) v :
  erase_micro id fE (val_as_cont v) (val_as_cont (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_val_as_struct {E} (fE : E → E) v :
  erase_micro erase_env fE (val_as_struct v) (val_as_struct (erase_val v)).
Proof. erase_val_as v. Qed.

(* -------------------------------------------------------------------------- *)

(** ** Environment lookups. *)

(* These are functions, not computations: erasure commutes with them as an
   equation. *)

Lemma erase_val_as_struct_opt v :
  val_as_struct_opt (erase_val v) = erase_env <$> val_as_struct_opt v.
Proof. by destruct v. Qed.

Lemma erase_lookup_name η x :
  lookup_name (erase_env η) x = erase_val <$> lookup_name η x.
Proof.
  induction η as [| [y v] η IH ]; simpl; first done.
  by case_match.
Qed.

Lemma erase_lookup_path η π :
  lookup_path (erase_env η) π = erase_val <$> lookup_path η π.
Proof.
  revert η. induction π as [| x π IH ]; intros η; simpl; first done.
  destruct π as [| y π ].
  - apply erase_lookup_name.
  - rewrite erase_lookup_name.
    destruct (lookup_name η x) as [ v | ]; simpl; last done.
    rewrite erase_val_as_struct_opt.
    destruct (val_as_struct_opt v) as [ xvs | ]; simpl; last done.
    apply IH.
Qed.

Lemma erase_eval_proph_arg η a :
  eval_proph_arg (erase_env η) a = erase_val <$> eval_proph_arg η a.
Proof. destruct a; simpl; [ apply erase_lookup_path | done | done ]. Qed.

(* -------------------------------------------------------------------------- *)

(** ** Coercions of computations. *)

Lemma erase_as_loc {E} (fE : E → E) m m' :
  erase_micro erase_val fE m m' → erase_micro id fE (as_loc m) (as_loc m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_loc.
Qed.

Lemma erase_as_int m m' :
  erase_micro erase_val erase_val m m' →
  erase_micro id erase_val (as_int m) (as_int m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_int.
Qed.

Lemma erase_as_bool m m' :
  erase_micro erase_val erase_val m m' →
  erase_micro id erase_val (as_bool m) (as_bool m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_bool.
Qed.

Lemma erase_as_thread {E} (fE : E → E) m m' :
  erase_micro erase_val fE m m' →
  erase_micro id fE (as_thread m) (as_thread m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_thread.
Qed.

Lemma erase_as_cont {E} (fE : E → E) m m' :
  erase_micro erase_val fE m m' → erase_micro id fE (as_cont m) (as_cont m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_cont.
Qed.

Lemma erase_as_struct {E} (fE : E → E) m m' :
  erase_micro erase_val fE m m' →
  erase_micro erase_env fE (as_struct m) (as_struct m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_struct.
Qed.

Lemma erase_val_as_record {E} (fE : E → E) v :
  erase_micro id fE (val_as_record v) (val_as_record (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_val_as_array {E} (fE : E → E) v :
  erase_micro id fE (val_as_array v) (val_as_array (erase_val v)).
Proof. erase_val_as v. Qed.

Lemma erase_as_record {E} (fE : E → E) m m' :
  erase_micro erase_val fE m m' → erase_micro id fE (as_record m) (as_record m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_record.
Qed.

Lemma erase_as_array {E} (fE : E → E) m m' :
  erase_micro erase_val fE m m' → erase_micro id fE (as_array m) (as_array m').
Proof.
  intros Hm. eapply erase_bind; [ done | ]. intros v. apply erase_val_as_array.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Store operations. *)

Lemma erase_load {E} (fE : E → E) l :
  erase_micro erase_val fE (load l) (load l).
Proof.
  apply (EM_Stop _ _ CLoad); [ done | ].
  intros [ v | e ]; simpl; [ apply EM_Ret | apply EM_Crash ].
Qed.

Lemma erase_load_block {E} (fE : E → E) l :
  erase_micro id fE (load_block l) (load_block l).
Proof.
  apply (EM_Stop _ _ CLoadBlock); [ done | ].
  intros [ r | e ]; simpl; [ apply EM_Ret | apply EM_Crash ].
Qed.

Lemma erase_loadn {E} (fE : E → E) ls :
  erase_micro erase_vals fE (loadn ls) (loadn ls).
Proof.
  induction ls as [| l ls IH ]; simpl.
  - exact (EM_Ret erase_vals fE []).
  - eapply erase_bind; [ apply erase_load | ]. intros v.
    eapply erase_bind; [ apply IH | ]. intros vs.
    exact (EM_Ret erase_vals fE (v :: vs)).
Qed.

Lemma erase_alloc v :
  erase_micro id erase_val (alloc v) (alloc (erase_val v)).
Proof. apply (erase_stop CAlloc v). done. Qed.

Lemma erase_allocn vs :
  erase_micro id erase_val (allocn vs) (allocn (erase_vals vs)).
Proof.
  induction vs as [| v vs IH ]; simpl.
  - exact (EM_Ret id erase_val []).
  - eapply erase_bind; [ apply erase_alloc | ]. intros l.
    eapply erase_bind; [ apply IH | ]. intros ls.
    exact (EM_Ret id erase_val (l :: ls)).
Qed.

Lemma erase_alloc_block t ls :
  erase_micro id erase_val (alloc_block t ls) (alloc_block t ls).
Proof. apply (erase_stop CAllocBlock (t, ls)). done. Qed.

Lemma erase_exchange l v :
  erase_microvx (exchange l v) (exchange l (erase_val v)).
Proof. apply (erase_stop CExchange (l, v)). done. Qed.

Lemma erase_store_op l v :
  erase_microvx (code.store l v) (code.store l (erase_val v)).
Proof.
  unfold code.store.
  eapply erase_bind; [ apply erase_exchange | ]. intros w.
  exact (EM_Ret erase_val erase_val VUnit).
Qed.

Lemma erase_cas l seen v :
  erase_microvx (cas l seen v) (cas l (erase_val seen) (erase_val v)).
Proof. apply (erase_stop CCAS (l, seen, v)). done. Qed.

Lemma erase_faa l i :
  erase_microvx (faa l i) (faa l i).
Proof. apply (erase_stop CFAA (l, i)). done. Qed.

Lemma erase_set_tag l t :
  erase_micro id erase_val (set_tag l t) (set_tag l t).
Proof. apply (erase_stop CSetBlockTag (l, t)). done. Qed.

Lemma erase_update ls fvs :
  erase_micro id erase_val (update ls fvs) (update ls (erase_fvals fvs)).
Proof.
  induction fvs as [| [f v] fvs IH ]; simpl.
  - exact (EM_Ret id erase_val ()).
  - case_match; last apply EM_Crash.
    eapply erase_bind; [ apply erase_store_op | ]. intros w. apply IH.
Qed.

Lemma erase_loadfs {E} (fE : E → E) ls fps :
  erase_micro erase_vals fE (loadfs ls fps) (loadfs ls fps).
Proof.
  induction fps as [| [f p] fps IH ]; simpl.
  - exact (EM_Ret erase_vals fE []).
  - eapply erase_bind.
    { case_match; [ apply erase_load | apply EM_Crash ]. }
    intros v. eapply erase_bind; [ apply IH | ]. intros vs.
    exact (EM_Ret erase_vals fE (v :: vs)).
Qed.

(* [fvals] selects fields out of an already-loaded block; it is a function,
   not a computation. [!!!] returns the inhabitant of [val] on an index out
   of range, and that inhabitant is erasure-stable. *)

Lemma erase_val_inhabitant : erase_val inhabitant = inhabitant.
Proof. done. Qed.

(* -------------------------------------------------------------------------- *)

(** ** Arithmetic side conditions. *)

Lemma erase_check_div_by_zero i :
  erase_micro id erase_val (check_div_by_zero i) (check_div_by_zero i).
Proof.
  unfold check_div_by_zero. case_match.
  - apply EM_Crash.
  - exact (EM_Ret id erase_val ()).
Qed.

Lemma erase_if_in_shift_range {A E} (fA : A → A) (fE : E → E) i m m' :
  erase_micro fA fE m m' →
  erase_micro fA fE (if_in_shift_range i m) (if_in_shift_range i m').
Proof.
  intros Hm. unfold if_in_shift_range. case_match; [ done | apply EM_Crash ].
Qed.

(* [Array.make] builds its initial contents with [replicate]. *)

Lemma erase_vals_init_segment i k v :
  erase_vals (init_segment i k (λ _, v)) = init_segment i k (λ _, erase_val v).
Proof. revert i. induction k as [| k IH ]; intros i; simpl; by rewrite ?IH. Qed.

Lemma erase_vals_replicate n v :
  erase_vals (list_z.replicate n v) = list_z.replicate n (erase_val v).
Proof.
  unfold list_z.replicate, list_z.init. case_decide; first done.
  apply erase_vals_init_segment.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Comparisons. *)

Lemma erase_phys_eq_val v1 v2 :
  erase_micro id erase_val
    (phys_eq_val v1 v2) (phys_eq_val (erase_val v1) (erase_val v2)).
Proof.
  destruct v1, v2; simpl;
    try apply EM_Crash;
    (* Two blocks: both sides load the same two blocks and compare tags. *)
    try (eapply erase_bind;
         [ eapply erase_par; apply erase_load_block
         | intros [[t1 ls1] [t2 ls2]];
           cbn beta iota zeta delta [ id prod_map fst snd ];
           repeat case_match;
           first [ apply EM_Crash | exact (EM_Ret id erase_val _) ] ]);
    (* Constant constructors: the argument lists are erased pointwise, so
       one is empty exactly when the other is. *)
    try (destruct v as [| ? ? ], v0 as [| ? ? ]; simpl;
         first [ apply EM_Crash | exact (EM_Ret id erase_val _) ]);
    try (exact (EM_Ret id erase_val _)).
  (* A constant constructor against something that is not one: both sides
     take the error branch whatever the argument list looks like. A
     prophecy: only the annotated side crashes. It must be caught before
     [case_match], which would otherwise destruct the string of the
     erased [VUnit]'s comparison forever. *)
  all: solve [ apply EM_CrashL | repeat case_match; apply EM_CrashL ].
Qed.

(* [eq_val] traverses tuples and data with a local [fix]; [eq_vals] mirrors
   it, so that the list case of the induction has something to be stated
   about. The two are convertible. *)

Fixpoint eq_vals (vs1 vs2 : list val) : micro bool exn :=
  match vs1, vs2 with
  | [], [] => ret true
  | v1 :: vs1, v2 :: vs2 =>
      b ← eq_val v1 v2 ;
      b' ← eq_vals vs1 vs2 ;
      ret (b && b')
  | _ :: _, [] | [], _ :: _ =>
      structural_equality_error "tuple length mismatch"
  end.

Lemma erase_eq_vals vs1 :
  list_all@{Prop; Set Set} val
    (λ v1 : val, ∀ v2 : val, erase_micro id erase_val (eq_val v1 v2) (eq_val (erase_val v1) (erase_val v2)))
      vs1 →
  ∀ vs2,
  erase_micro id erase_val
    (eq_vals vs1 vs2) (eq_vals (erase_vals vs1) (erase_vals vs2)).
Proof.
  intros Hinv.
  induction vs1 as [ | v1 vs1 IHvs ].
  - intros vs2. destruct vs2; constructor.
  - intros [ | v2 vs2 ]; first constructor.
    simpl.
    eapply erase_bind; [ by inversion Hinv | ]. intros b.
    eapply erase_bind; [ by apply IHvs; inversion Hinv | ]. intros b'.
    apply (EM_Ret id erase_val (b && b')).
Qed.

Lemma erase_eq_val v1 :
  ∀ v2, erase_micro id erase_val
          (eq_val v1 v2) (eq_val (erase_val v1) (erase_val v2)).
Proof.
  (* [EM_CrashL]: a prophecy does not compare, but its erasure [VUnit]
     does. *)
  induction v1;
    intros; try (destruct v2; simpl; first [ apply EM_CrashL
                                           | exact (EM_Ret id erase_val _) ]).
  - destruct v2; simpl; try apply EM_CrashL. fold eq_vals. fold erase_vals.
    apply erase_eq_vals. apply H.
  - destruct v2; simpl; try apply EM_CrashL. fold eq_vals. fold erase_vals.
    case_match; try by constructor.
    apply erase_eq_vals. apply H.
Qed.

Lemma erase_ne_val v1 v2 :
  erase_micro id erase_val (ne_val v1 v2) (ne_val (erase_val v1) (erase_val v2)).
Proof.
  unfold ne_val. eapply erase_bind; [ apply erase_eq_val | ]. intros b.
  exact (EM_Ret id erase_val (negb b)).
Qed.

Lemma erase_lt_val v1 v2 :
  erase_micro id erase_val (lt_val v1 v2) (lt_val (erase_val v1) (erase_val v2)).
Proof.
  destruct v1, v2; simpl;
    first [ apply EM_Crash | exact (EM_Ret id erase_val _) ].
Qed.

Lemma erase_gt_val v1 v2 :
  erase_micro id erase_val (gt_val v1 v2) (gt_val (erase_val v1) (erase_val v2)).
Proof. apply erase_lt_val. Qed.

Lemma erase_le_val v1 v2 :
  erase_micro id erase_val (le_val v1 v2) (le_val (erase_val v1) (erase_val v2)).
Proof.
  unfold le_val. eapply erase_bind; [ apply erase_gt_val | ]. intros b.
  exact (EM_Ret id erase_val (negb b)).
Qed.

Lemma erase_ge_val v1 v2 :
  erase_micro id erase_val (ge_val v1 v2) (ge_val (erase_val v1) (erase_val v2)).
Proof.
  unfold ge_val. eapply erase_bind; [ apply erase_lt_val | ]. intros b.
  exact (EM_Ret id erase_val (negb b)).
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Effects and continuations. *)

Lemma erase_perform v : erase_microvx (perform v) (perform (erase_val v)).
Proof. apply (erase_stop CPerf v). done. Qed.

Lemma erase_resume l o :
  erase_microvx (resume l o) (resume l (erase_outcome o)).
Proof. apply (erase_stop CResume (l, o)). done. Qed.

Lemma erase_please_eval η e :
  erase_microvx (please_eval η e) (please_eval (erase_env η) (erase_expr e)).
Proof. apply (erase_stop CEval (η, e)). done. Qed.

Lemma erase_wrap l η bs :
  erase_micro id erase_val
    (wrap l η bs) (wrap l (erase_env η) (erase_branches bs)).
Proof. apply (erase_stop CWrap (true, l, η, bs)). done. Qed.

Lemma erase_shallow_wrap l η bs :
  erase_micro id erase_val
    (shallow_wrap l η bs) (shallow_wrap l (erase_env η) (erase_branches bs)).
Proof. apply (erase_stop CWrap (false, l, η, bs)). done. Qed.

Lemma erase_wrap_outcome η bs (o : outcome3 val exn) :
  erase_micro erase_out3 erase_val
    (wrap_outcome η bs o)
    (wrap_outcome (erase_env η) (erase_branches bs) (erase_out3 o)).
Proof.
  destruct o as [ v | ex | ev k ]; simpl.
  - exact (EM_Ret erase_out3 erase_val (O3Ret v)).
  - exact (EM_Ret erase_out3 erase_val (O3Throw ex)).
  - eapply erase_bind; [ apply erase_wrap | ]. intros k'.
    exact (EM_Ret erase_out3 erase_val (O3Perform ev k')).
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Prophecies. *)

(* Allocating a prophecy is a step that erasure drops: whichever identifier
   it picks, the prophecy erases to unit. *)

Lemma erase_new_proph :
  erase_microvx ('p ← new_proph ; ret (VProph p)) (ret VUnit).
Proof.
  apply EM_NewProph. intros p.
  exact (EM_Ret erase_val erase_val (VProph p)).
Qed.

Lemma erase_resolve_return w p v :
  erase_microvx (resolve CReturn w p v) (ret (erase_val w)).
Proof. apply EM_ResolveReturn. apply EM_Ret. Qed.

Lemma erase_bind_resolve_return p v m m' :
  erase_microvx m m' →
  erase_microvx (bind m (λ w, resolve CReturn w p v)) m'.
Proof.
  intros Hm.
  (* The erased side does nothing after the expression; [bind m' ret] is [m']. *)
  rewrite <- (bind_ret_right m').
  eapply erase_bind; [ done | ]. intros w. apply erase_resolve_return.
Qed.

(* The four calls that may carry a fused resolution never throw: their steps
   return a value or crash. *)

Local Ltac no_throw :=
  intros σ σ' ex Hstep; destruct_step;
  unfold step_load_2, step_exchange_2, step_cas_2, step_faa_2 in *;
  repeat case_match; simplify_eq.

Lemma code_no_throw_load l : code_no_throw CLoad l.
Proof. no_throw. Qed.

Lemma code_no_throw_exchange x : code_no_throw CExchange x.
Proof. no_throw. Qed.

Lemma code_no_throw_cas x : code_no_throw CCAS x.
Proof. no_throw. Qed.

Lemma code_no_throw_faa x : code_no_throw CFAA x.
Proof. no_throw. Qed.

Lemma erase_resolve_load l p v :
  erase_microvx (resolve CLoad l p v) (load l).
Proof.
  apply EM_Resolve; [ done | apply code_no_throw_load | ].
  intros w. apply EM_Ret.
Qed.

Lemma erase_resolve_exchange l w p v :
  erase_microvx (resolve CExchange (l, w) p v) (exchange l (erase_val w)).
Proof.
  apply EM_Resolve; [ done | apply code_no_throw_exchange | ].
  intros u. apply EM_Ret.
Qed.

Lemma erase_resolve_cas l seen w p v :
  erase_microvx (resolve CCAS (l, seen, w) p v)
             (cas l (erase_val seen) (erase_val w)).
Proof.
  apply EM_Resolve; [ done | apply code_no_throw_cas | ].
  intros u. apply EM_Ret.
Qed.

Lemma erase_resolve_faa l i p v :
  erase_microvx (resolve CFAA (l, i) p v) (faa l i).
Proof.
  apply EM_Resolve; [ done | apply code_no_throw_faa | ].
  intros u. apply EM_Ret.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Threads, loops and choice. *)

Lemma erase_fork v1 v2 :
  erase_microvx (fork v1 v2) (fork (erase_val v1) (erase_val v2)).
Proof. apply (erase_stop CFork (v1, v2)). done. Qed.

Lemma erase_join t : erase_microvx (join t) (join t).
Proof. apply (erase_stop CJoin t). done. Qed.

Lemma erase_loop η x i1 i2 e :
  erase_microvx (code.loop η x i1 i2 e)
             (code.loop (erase_env η) x i1 i2 (erase_expr e)).
Proof. apply (erase_stop CLoop (η, x, i1, i2, e)). done. Qed.

Lemma erase_flip : erase_micro id erase_val flip flip.
Proof. apply (erase_stop CFlip ()). done. Qed.

Lemma erase_choose {A} (fA : A → A) m1 m1' m2 m2' :
  erase_micro fA erase_val m1 m1' →
  erase_micro fA erase_val m2 m2' →
  erase_micro fA erase_val (choose m1 m2) (choose m1' m2').
Proof.
  intros Hm1 Hm2. unfold choose.
  eapply erase_bind; [ apply erase_flip | ]. intros b. by destruct b.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Calls. *)

(* A call does not evaluate the closure's body; it asks the machine to, with
   [stop CEval]. That keeps [eval] structurally recursive, and lets this be
   proved ahead of the induction: the body is an argument of a system call,
   erased by [erase_code_arg CEval]. *)

Lemma erase_env_app η1 η2 :
  erase_env (η1 ++ η2) = erase_env η1 ++ erase_env η2.
Proof. induction η1 as [| [x v] η1 IH ]; simpl; by rewrite ?IH. Qed.

Lemma erase_eval_rec_bindings_aux η rbs rbs' :
  eval_rec_bindings_aux (erase_env η) (erase_rec_bindings rbs)
                        (erase_rec_bindings rbs') =
  erase_env (eval_rec_bindings_aux η rbs rbs').
Proof. induction rbs' as [| [g a] rbs' IH ]; simpl; by rewrite ?IH. Qed.

Lemma erase_eval_rec_bindings η rbs :
  eval_rec_bindings (erase_env η) (erase_rec_bindings rbs) =
  erase_env (eval_rec_bindings η rbs).
Proof. apply erase_eval_rec_bindings_aux. Qed.

Lemma erase_lookup_rec_bindings rbs g :
  lookup_rec_bindings (erase_rec_bindings rbs) g =
  erase_anonfun <$> lookup_rec_bindings rbs g.
Proof.
  induction rbs as [| [g' a] rbs IH ]; simpl; first done. by case_match.
Qed.

Lemma erase_acall η a v :
  erase_microvx (acall η a v) (acall (erase_env η) (erase_anonfun a) (erase_val v)).
Proof.
  destruct a as [ x e ]. unfold acall, please_eval.
  apply (erase_stop CEval ((x, v) :: η, e)). done.
Qed.

Lemma erase_call v1 v2 :
  erase_microvx (call v1 v2) (call (erase_val v1) (erase_val v2)).
Proof.
  destruct v1; simpl; try apply EM_Crash.
  - apply erase_acall.
  - rewrite erase_eval_rec_bindings, erase_lookup_rec_bindings, <- erase_env_app.
    eapply erase_bind.
    + apply (erase_of_option erase_anonfun erase_val).
    + intros a. apply erase_acall.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Two-armed handlers. *)

Lemma erase_try {A B E E'} (fA : A → A) (fE' : E' → E') (fB : B → B) (fE : E → E)
    m m' (f : A → micro B E) f' (h : E' → micro B E) h' :
  erase_micro fA fE' m m' →
  (∀ a, erase_micro fB fE (f a) (f' (fA a))) →
  (∀ ex, erase_micro fB fE (h ex) (h' (fE' ex))) →
  erase_micro fB fE (try m f h) (try m' f' h').
Proof.
  intros Hm Hf Hh. unfold try.
  eapply erase_try2; [ done | ]. intros [ a | ex ]; simpl; [ apply Hf | apply Hh ].
Qed.

Lemma erase_orelse {A E E'} (fA : A → A) (fE' : E' → E') (fE : E → E)
    m1 m1' m2 m2' :
  erase_micro fA fE' m1 m1' →
  erase_micro fA fE m2 m2' →
  erase_micro fA fE (orelse m1 m2) (orelse m1' m2').
Proof.
  intros Hm1 Hm2. unfold orelse.
  eapply erase_try; [ done | intros a; apply EM_Ret | intros ex; done ].
Qed.

Lemma erase_vals_length vs : length (erase_vals vs) = length vs.
Proof.
  induction vs as [| v vs IH ]; first done.
  change (list_z.length (erase_val v :: erase_vals vs) =
          list_z.length (v :: vs)).
  rewrite !list_z.length_cons. by rewrite IH.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Module coercions and type extensions. *)

Section Coerces.

(* The bind below is the option monad's, as in [pre_coerces]. *)
Local Open Scope stdpp.

Fixpoint coerces (xcs : list fcoercion) (xvs : env) : option env :=
  match xcs with
  | [] => Some []
  | (x, c) :: xcs =>
      v ← lookup_name xvs x ;
      v ← coerce c v ;
      xvs' ← coerces xcs xvs ;
      Some ((x, v) :: xvs')
  end.

End Coerces.

Lemma erase_coerces xcs :
  list_all@{Type ; Set Set} (var * coercion)
    (prod_all@{Type Prop ; Set Set Set Set} string (λ _, unit) coercion
      (λ c, ∀ v, coerce c (erase_val v) = erase_val <$> coerce c v))
    xcs →
  ∀ η,
    coerces xcs (erase_env η) = erase_env <$> coerces xcs η.
Proof.
  induction xcs as [ | (x, c) xcs IHs ]; intros Hinv.
  - done.
  - inversion Hinv as [ | ? Hxc ? Hxcs ]; subst.
    inversion Hxc as [ ??? Hcoerce ]; subst.
    intros η. simpl. rewrite erase_lookup_name.
    destruct (lookup_name η x); last done.
    simpl. rewrite Hcoerce.
    destruct (coerce c v); last done.
    rewrite IHs. by destruct (coerces xcs η). assumption.
Qed.

Lemma erase_coerce c :
  ∀ v, coerce c (erase_val v) = erase_val <$> coerce c v.
Proof.
  induction c;
    (* [coerce]'s body carries the local [fix]; [coerces] is the same term *)
    intros; simpl; change (pre_coerces coerce) with coerces.
  - done.
  - rewrite erase_val_as_struct_opt.
    destruct (val_as_struct_opt v) as [ xvs | ]; simpl; last done.
    rewrite erase_coerces; last apply H.
    by destruct (coerces xcs xvs).
Qed.

Lemma erase_eval_type_extensions cs :
  erase_micro erase_env erase_val
    (eval_type_extensions cs) (eval_type_extensions cs).
Proof.
  induction cs as [| c cs IH ]; simpl.
  - exact (EM_Ret erase_env erase_val []).
  - eapply erase_bind; [ apply (erase_alloc VUnit) | ]. intros l.
    eapply erase_bind; [ apply IH | ]. intros η.
    exact (EM_Ret erase_env erase_val ((c, VLoc l) :: η)).
Qed.


(* -------------------------------------------------------------------------- *)

(** ** Unfolding equations for the list evaluators. *)

(* [simpl_eval*] unseals and simplifies, which for a list evaluator goes one
   step too far: it inlines the head's evaluator too, and the induction
   hypothesis, stated with the sealed name, stops matching. These expose
   exactly one layer. They belong in eval.v next to [fold_pre_*]; they live
   here to avoid rebuilding the world. *)

Lemma evals_cons η e es :
  evals η (e :: es) =
  ('(v, vs) ← pair_op LiberalStrategy.tuple_order (eval η e) (evals η es) ;
   ret (v :: vs)).
Proof. unfold evals; rewrite seal_eq; by simpl. Qed.

Lemma evalfs_cons η f e fes :
  evalfs η (Fexpr f e :: fes) =
  ('(v, fvs) ← par (eval η e) (evalfs η fes) ; ret ((f, v) :: fvs)).
Proof. unfold evalfs; rewrite seal_eq; by simpl. Qed.

Lemma eval_bindings_cons η p e bs :
  eval_bindings η (Binding p e :: bs) =
  ('(v, δ) ← pair_op LiberalStrategy.let_and_order
               (eval η e) (eval_bindings η bs) ;
   irrefutably_extend η δ p v).
Proof. unfold eval_bindings; rewrite seal_eq; by simpl. Qed.

Lemma eval_sitems_cons ηδ i items :
  eval_sitems ηδ (i :: items) =
  (ηδ' ← eval_sitem ηδ i ; eval_sitems ηδ' items).
Proof.
  unfold eval_sitems, eval_sitem; rewrite !seal_eq; by simpl.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** The computation under a resolution. *)

Definition eval_resolved (η : env) (e : expr) (p : proph_id) (v : val) : microvx :=
  match e with
  | ELoad e1 =>
      r ← as_record (eval η e1) ;
      '(_, ls) ← load_block r ;
      match ls !! 0%Z with
      | Some l => resolve CLoad l p v
      | None => Crash
      end
  | EFieldLoad e1 =>
      l ← as_loc (eval η e1) ;
      resolve CLoad l p v
  | ERecordAccess e1 f =>
      r ← as_record (eval η e1) ;
      '(_, ls) ← load_block r ;
      match ls !! f with
      | Some l => resolve CLoad l p v
      | None => Crash
      end
  | EExchange e1 e2 =>
      '(l, w) ← pair_op LiberalStrategy.fun_app_order
                  (as_loc (eval η e1)) (eval η e2) ;
      resolve CExchange (l, w) p v
  | ECAS e1 e2 e3 =>
      '(l, seen, w) ← par (par (as_loc (eval η e1)) (eval η e2)) (eval η e3) ;
      resolve CCAS (l, seen, w) p v
  | EFAA e1 e2 =>
      '(l, i) ← par (as_loc (eval η e1)) (as_int (eval η e2)) ;
      resolve CFAA (l, i) p v
  | _ =>
      w ← eval η e ;
      resolve CReturn w p v
  end.

Lemma erase_resolved_of_eval e :
  (∀ η p v, eval_resolved η e p v = (w ← eval η e ; resolve CReturn w p v)) →
  (∀ η, erase_microvx (eval η e) (eval (erase_env η) (erase_expr e))) →
  ∀ η p v, erase_microvx (eval_resolved η e p v)
             (eval (erase_env η) (erase_expr e)).
Proof.
  intros Hres He η p v. rewrite Hres. by apply erase_bind_resolve_return.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** The [erase_eval] lemma. *)

(* [ee_ret] threads the payload explicitly. *)

Local Ltac ee_ret :=
  lazymatch goal with
  | |- erase_micro ?fA ?fE (Ret ?a) _ => exact (EM_Ret fA fE a)
  | |- erase_micro ?fA ?fE (Throw ?e) _ => exact (EM_Throw fA fE e)
  end.

(* Fully destruct tuples. *)
Ltac destruct_pairs x :=
  repeat (let T := type of x in
          let T := eval hnf in T in
          lazymatch T with
          | (_ * _)%type => destruct x as [x ?]
          | unit => destruct x
          end).

(* After a [bind], the erased side has the payload map applied to the
   value that was just introduced. Reducing those makes the two sides
   line up again. *)
Local Ltac ee_pair :=
  cbn beta iota zeta delta [ id prod_map fst snd ].

Local Ltac ee_cons_eqs :=
  rewrite ?evals_cons, ?evalfs_cons, ?eval_bindings_cons, ?eval_sitems_cons.

Local Ltac ee_expose_cons :=
  cbn beta iota delta
    [ erase_exprs erase_fexprs erase_branches erase_bindings
      erase_rec_bindings erase_sitems ];
  ee_cons_eqs.

Lemma erase_evals_pats ps :
  list_all@{Prop; Set Set} pat
      (λ p : pat,
         ∀ (η δ : env) (v : val),
           erase_micro erase_env id (eval_pat η δ p v)
             (eval_pat (erase_env η) (erase_env δ) p (erase_val v)))
      ps →
  ∀ (η δ : env) (vs : list val),
    erase_micro erase_env id (eval_pats η δ ps vs)
    (eval_pats (erase_env η) (erase_env δ) ps (erase_vals vs)).
Proof.
  induction ps as [ | p ps IHps ].
  - intros. destruct vs; simpl_eval_pats.
    + ee_ret.
    + constructor.
  - intros Hinv.
    inversion Hinv as [ | ? Hpat ? Hpats ]; subst.
    intros η δ vs.
    simpl_eval_pats. case_match; first constructor.
    subst. simpl.
    eapply erase_bind. apply Hpat. intro b.
    eapply erase_bind. apply IHps. apply Hpats. intro η'.
    ee_ret.
Qed.

Lemma erase_eval_fpats fps :
  list_all@{Type ; Set Set} (field * pat)
    (prod_all@{Type Prop ; Set Set Set Set} Z (λ _ : Z, ()%type) pat
       (λ p : pat,
          ∀ (η δ : env) (v : val),
            erase_micro erase_env id (eval_pat η δ p v) (eval_pat (erase_env η) (erase_env δ) p (erase_val v))))
    fps →
  ∀ (η δ : env) (vs : list val),
  erase_micro erase_env id (eval_fpats η δ fps vs) (eval_fpats (erase_env η) (erase_env δ) fps (erase_vals vs)).
Proof.
  induction fps as [ | (f, p) ps IHps ]; intros Hinv η δ vs.
  - destruct vs; simpl_eval_fpats; ee_ret.
  - inversion Hinv as [ | ? Hprod ? Hpats ]; subst.
    inversion Hprod as [ ??? Hpat ]; subst.
    simpl_eval_fpats. destruct vs; first constructor.
    simpl.
    eapply erase_bind; [ apply Hpat | ]. intros η'.
    eapply erase_bind; [ apply IHps; assumption | ]. intros η''.
    ee_ret.
Qed.

Lemma erase_eval_pat p :
  ∀ η δ v, erase_micro erase_env id
             (eval_pat η δ p v)
             (eval_pat (erase_env η) (erase_env δ) p (erase_val v)).
Proof.
  induction p.
  (* A pattern holds no expressions, so both sides run the *same* pattern
     against a value and its erasure, and every test they make is one
     erasure preserves. *)
  - (* PUnsupported *)
    intros η δ v; simpl_eval_pat; apply EM_Crash.
  - (* PAny *)
    intros η δ v; simpl_eval_pat; ee_ret.
  - (* PVar *)
    intros η δ v; simpl_eval_pat; ee_ret.
  - (* PAlias *)
    intros η δ v; simpl_eval_pat;
    eapply erase_bind; [ apply IHp | ]; intros δ'; ee_pair; ee_ret.
  - (* POr *)
    intros η δ v; simpl_eval_pat;
    eapply erase_orelse; [ apply IHp1 | apply IHp2 ].
  - (* PTuple *)
    intros η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash.
    fold erase_vals.
    apply erase_evals_pats; assumption.
  - (* PData: a prophecy is not data, but its erasure [VUnit] is. *)
    intros η δ v;
    destruct v; simpl_eval_pat; try apply EM_CrashL; try ee_ret;
    case_match; [ | ee_ret ]. fold erase_vals.
    apply erase_evals_pats; assumption.
  - (* PXData *)
    intros η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash; try ee_ret;
    rewrite erase_lookup_path;
    eapply erase_bind; [ apply erase_as_loc, erase_of_option | ]; intros l';
    ee_pair;
    case_match; [ | ee_ret ].
    fold erase_vals.
    apply erase_evals_pats; assumption.
  - (* PRecord *)
    intros η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    eapply erase_bind; [ apply erase_loadfs | ]; intros vs; ee_pair.
    apply erase_eval_fpats; assumption.
  - (* PInline: as for [PData], a prophecy crashes where [VUnit] throws. *)
    intros η δ v;
    destruct v; simpl_eval_pat; try apply EM_CrashL; try ee_ret;
    case_match; [ apply IHp | ee_ret ].
  - (* PArray *)
    intros η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    eapply erase_bind; [ apply erase_loadn | ]; intros vs; ee_pair;
    rewrite erase_vals_length;
    case_decide; [ apply erase_evals_pats; assumption | ee_ret ].
  - (* PInt *)
    intros η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    case_match; ee_ret.
  - (* PChar *)
    intros η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    case_match; ee_ret.
  - (* PString *)
    intros η δ v;
    destruct v; simpl_eval_pat; try apply EM_Crash;
    case_match; ee_ret.
Qed.

Lemma erase_eval_cpat cp :
  ∀ η δ o, erase_micro erase_env id
             (eval_cpat η δ cp o)
             (eval_cpat (erase_env η) (erase_env δ) cp (erase_out3 o)).
Proof.
  induction cp as [ p | p | pe pk | cp1 IH1 cp2 IH2 ];
    intros η δ o; destruct o; simpl;
    first [ ee_ret
          | apply erase_eval_pat
          | eapply erase_bind;
              [ apply erase_eval_pat | intros δ'; apply erase_eval_pat ]
          (* [eapply]: the exception map of the first alternative appears
             only in that premise, so [apply] cannot infer it *)
          | eapply erase_orelse; [ apply IH1 | apply IH2 ] ].
Qed.

Lemma erase_irrefutably_extend {E} (fE : E → E) η δ p v :
  erase_micro erase_env fE
    (irrefutably_extend η δ p v)
    (irrefutably_extend (erase_env η) (erase_env δ) p (erase_val v)).
Proof.
  unfold irrefutably_extend.
  eapply erase_try; [ apply erase_eval_pat | intros δ'; apply EM_Ret | ].
  intros []. apply EM_Crash.
Qed.

Lemma erase_evals es :
  list_all@{Type ; Set Set} expr (λ e, ∀ η, erase_microvx (eval η e) (eval (erase_env η) (erase_expr e))) es →
  ∀ η,
    erase_micro erase_vals erase_val (evals η es) (evals (erase_env η) (erase_exprs es)).
Proof.
  induction es as [ | e es IHes ]; intros Hinv η.
  - simpl_evals. constructor.
  - simpl_evals.
    inversion Hinv as [ | ? He ? Hes ]; subst.
    eapply erase_bind;
      [ apply erase_par; [ apply He | apply IHes, Hes ] | ].
    intros (v, vs).
    ee_ret.
Qed.

Fixpoint erase_unzip (fvs : list (field * val)) :=
  match fvs with
  | [] => []
  | (f, v) :: fvs => (f, erase_val v) :: erase_unzip fvs
  end.

Lemma erase_evalfs fes :
  list_all fexpr (λ '(Fexpr f e), ∀ η, erase_microvx (eval η e) (eval (erase_env η) (erase_expr e))) fes →
  ∀ η,
    erase_micro erase_unzip erase_val (evalfs η fes) (evalfs (erase_env η) (erase_fexprs fes)).
Proof.
  induction fes as [ | (f, e) fes IHfes ]; intros Hinv η.
  - simpl_evalfs. ee_ret.
  - simpl_evalfs.
    inversion Hinv as [ | (? & ?) He ? Hfes ].
    eapply erase_bind.
    eapply erase_par; [ apply He | apply IHfes, Hfes ].
    intros (v, fvs).
    simpl. ee_ret.
Qed.

Lemma erase_eval_bindings bs :
  list_all binding (λ '(Binding p e), ∀ η, erase_microvx (eval η e) (eval (erase_env η) (erase_expr e))) bs →
  ∀ η,
    erase_micro erase_env erase_val (eval_bindings η bs) (eval_bindings (erase_env η) (erase_bindings bs)).
Proof.
  induction bs as [ | (p, e) bs IHbs ]; intros Hinv η.
  - simpl_eval_bindings. ee_ret.
  - simpl_eval_bindings.
    inversion Hinv as [ | (? & ?) He ? Hbs ]; subst.
    eapply erase_bind.
    eapply erase_par; [ apply He | apply IHbs, Hbs ].
    intros (v, η').
    simpl. apply erase_irrefutably_extend.
Qed.

Lemma erase_eval_branches_aux bs :
  list_all branch (λ '(Branch cpat e), ∀ η, erase_microvx (eval η e) (eval (erase_env η) (erase_expr e))) bs →
  ∀ η o,
  erase_microvx (eval_branches η o bs) (eval_branches (erase_env η) (erase_out3 o) (erase_handler bs)).
Proof.
  induction bs as [ | (p, e) bs IHbs ]; intros Hinv η o.
  - simpl_eval_branches. destruct o; constructor. constructor.
    intros o. rewrite !try2_inject2. simpl. apply erase_resume.
  - simpl_eval_branches.
    inversion Hinv as [ | (? & ?) He ? Hbs ]; subst.
    eapply erase_try2. apply erase_eval_cpat. intros [|()].
    + simpl. apply He.
    + simpl. apply IHbs, Hbs.
Qed.

Lemma erase_shallow_eval_branches_aux bs :
  list_all branch (λ '(Branch cpat e), ∀ η, erase_microvx (eval η e) (eval (erase_env η) (erase_expr e))) bs →
  ∀ η all_bs o,
    erase_micro erase_val erase_val (shallow_eval_branches η bs all_bs o)
      (shallow_eval_branches (erase_env η) (erase_branches bs) (erase_branches all_bs) (erase_out3 o)).
Proof.
  induction bs as [ | (p, e) bs IHbs ]; intros Hinv η all_bs o.
  - simpl_shallow_eval_branches. destruct o; constructor. constructor.
    intros o. fold (@bind loc val exn). simpl. destruct o; constructor. constructor.
    intros o. rewrite !try2_inject2. apply erase_resume.
  - simpl_shallow_eval_branches.
    inversion Hinv as [ | (? & ?) He ? Hbs ]; subst.
    eapply erase_try. apply erase_eval_cpat. apply He.
    intros (). apply IHbs, Hbs.
Qed.

Lemma erase_eval_sitems items :
  list_all sitem
    (λ struct : sitem,
       ∀ (l : list (var * val)) (η : env),
         erase_micro (λ '(η0, δ), (erase_env η0, erase_env δ)) erase_val (eval_sitem (η, l) struct)
           (eval_sitem (erase_env η, erase_env l) (erase_sitem struct)))
    items →
  ∀ (η : env) (δ : env),
    erase_micro erase_envs erase_val (eval_sitems (η, δ) items) (eval_sitems (erase_env η, erase_env δ) (erase_sitems items)).
Proof.
  induction items as [ | s items IHs]; intros Hinv η δ.
  - simpl_eval_sitems. ee_ret.
  - simpl. unfold eval_sitems. rewrite seal_eq. cbn [pre_eval_sitems].
    rewrite fold_pre_eval_sitem, fold_pre_eval_sitems.
    inversion Hinv as [ | ? Hitem ? Hitems ]; subst.
    eapply erase_bind. apply Hitem. intros (? & ?).
    apply IHs, Hitems.
Qed.

Lemma list_all_proj_1 {A : Type} P1 P2 l :
  list_all A (λ a, P1 a ∧ P2 a) l →
  list_all A P1 l.
Proof.
  induction l as [ | a l IH ].
  - constructor.
  - inversion 1; subst.
    constructor. apply H0. by apply IH.
Qed.

Lemma erase_eval e :
  (∀ η, erase_microvx (eval η e) (eval (erase_env η) (erase_expr e)))
  ∧ (∀ η p v, erase_microvx (eval_resolved η e p v)
       (eval (erase_env η) (erase_expr e))).
Proof.
  einduction e using expr_fexpr_rec;
  try (apply and_dup; [ apply erase_resolved_of_eval; done | intros η ]).
  (* One case per clause of [eval], each following the shape of the
     computation that clause builds. *)
  - (* EUnsupported *)
    simpl_eval; apply EM_Crash.
  - (* EPath *)
    simpl_eval;
    rewrite erase_lookup_path; apply erase_of_option.
  - (* EAnonFun *)
    simpl_eval; ee_ret.
  - (* EApp *)
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe0_1 | apply IHe0_2 ] | ];
    intros [ v1 v2 ]; ee_pair; apply erase_call.
  - (* ETuple *)
    simpl_eval;
    eapply erase_bind; [ | intros vs; ee_pair; ee_ret ].
    fold erase_exprs. apply erase_evals. eapply list_all_proj_1, H.
  - (* EData *)
    simpl_eval;
    eapply erase_bind; [ apply erase_evals; eapply list_all_proj_1, H | ].
    intros vs; ee_pair; ee_ret.
  - (* EXData *)
    simpl_eval;
    rewrite erase_lookup_path;
    eapply erase_bind; [ apply erase_as_loc, erase_of_option | ]; intros l;
    ee_pair;
    eapply erase_bind; [ apply erase_evals; eapply list_all_proj_1, H | ]; intros vs; ee_pair; ee_ret.
  - (* ERecord *)
    simpl_eval;
    eapply erase_bind; [ apply erase_evals; eapply list_all_proj_1, H | ]; intros vs; ee_pair;
    eapply erase_bind; [ apply erase_allocn | ]; intros ls; ee_pair;
    eapply erase_bind; [ apply erase_alloc_block | ]; intros l; ee_pair; ee_ret.
  - (* ERecordUpdate *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par; [ apply erase_as_record, IHe0 | ] | ].
    fold erase_fexprs. apply erase_evalfs. apply H.
    intros [ r fvs ]; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    eapply erase_bind; [ apply erase_loadn | ]; intros vs; ee_pair;
    eapply erase_bind; [ apply erase_allocn | ]; intros ls'; ee_pair;
    eapply erase_bind; [ apply erase_update | ]; intros []; ee_pair;
    eapply erase_bind; [ apply erase_alloc_block | ]; intros l; ee_pair; ee_ret.
  - (* ERecordAccess *)
    simpl_eval.
    split.
    + intros η.
      eapply erase_bind; [ apply erase_as_record, IHe0 | ]; intros r; ee_pair;
      eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
      destruct (ls !! f); [ apply erase_load | apply EM_Crash ].
    + intros η p v. cbn beta iota delta [ eval_resolved ].
      eapply erase_bind; [ apply erase_as_record, IHe0 | ]; intros r; ee_pair;
      eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
      destruct (ls !! f); [ apply erase_resolve_load | apply EM_Crash ].
  - (* ERecordSet *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par; [ apply erase_as_record, IHe0_1 | apply IHe0_2 ] | ];
    intros [ r v ]; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    destruct (ls !! f); [ apply erase_store_op | apply EM_Crash ].
  - (* EAtomicLoc *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_record, IHe0 | ]; intros r; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    destruct (ls !! f); [ ee_ret | apply EM_Crash ].
  - (* EInline *)
    simpl_eval;
    eapply erase_bind; [ apply erase_evals; eapply list_all_proj_1, H | ]; intros vs; ee_pair;
    eapply erase_bind; [ apply erase_allocn | ]; intros ls; ee_pair;
    eapply erase_bind; [ apply erase_alloc_block | ]; intros l; ee_pair; ee_ret.
  - (* EArrayLit *)
    simpl_eval;
    eapply erase_bind; [ eapply erase_evals, list_all_proj_1, H | ]; intros vs; ee_pair;
    eapply erase_bind; [ apply erase_allocn | ]; intros ls; ee_pair;
    eapply erase_bind; [ apply erase_alloc_block | ]; intros l; ee_pair; ee_ret.
  - (* EArrayLength *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_array, IHe0 | ]; intros a; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    ee_ret.
  - (* EArrayGet *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_array, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ a i ]; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    destruct (ls !! signed i); [ apply erase_load | apply EM_Crash ].
  - (* EArraySet *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_array, IHe0_1 | apply erase_par;
              [ apply erase_as_int, IHe0_2 | apply IHe0_3 ] ] | ];
    intros [ a [ i v ] ]; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    destruct (ls !! signed i); [ apply erase_store_op | apply EM_Crash ].
  - (* EArrayMake *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par; [ apply erase_as_int, IHe0_1 | apply IHe0_2 ] | ];
    intros [ n v ]; ee_pair;
    case_decide; [ | apply EM_Crash ];
    rewrite <- erase_vals_replicate;
    eapply erase_bind; [ apply erase_allocn | ]; intros ls; ee_pair;
    eapply erase_bind; [ apply erase_alloc_block | ]; intros l; ee_pair; ee_ret.
  - (* EFreeze *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_array, IHe0 | ]; intros a; ee_pair;
    eapply erase_bind; [ apply erase_set_tag | ]; intros []; ee_pair; ee_ret.
  - (* EUnfreeze *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_array, IHe0 | ]; intros a; ee_pair;
    eapply erase_bind; [ apply erase_set_tag | ]; intros []; ee_pair; ee_ret.
  - (* EBoolConj *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_bool, IHe0_1 | ]; intros b; ee_pair;
    destruct b; [ apply IHe0_2 | ee_ret ].
  - (* EBoolDisj *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_bool, IHe0_1 | ]; intros b; ee_pair;
    destruct b; [ ee_ret | apply IHe0_2 ].
  - (* EBoolNeg *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_bool, IHe0 | ]; intros b; ee_pair;
    ee_ret.
  - (* EInt *)
    simpl_eval; ee_ret.
  - (* EMaxInt *)
    simpl_eval; ee_ret.
  - (* EMinInt *)
    simpl_eval; ee_ret.
  - (* EIntNeg *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_int, IHe0 | ]; intros i; ee_pair;
    ee_ret.
  - (* EIntAdd *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ i1 i2 ]; ee_pair; ee_ret.
  - (* EIntSub *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ i1 i2 ]; ee_pair; ee_ret.
  - (* EIntMul *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ i1 i2 ]; ee_pair; ee_ret.
  - (* EIntDiv *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ i1 i2 ]; ee_pair;
    eapply erase_bind; [ apply erase_check_div_by_zero | ]; intros []; ee_pair;
    ee_ret.
  - (* EIntMod *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ i1 i2 ]; ee_pair;
    eapply erase_bind; [ apply erase_check_div_by_zero | ]; intros []; ee_pair;
    ee_ret.
  - (* EIntLand *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ i1 i2 ]; ee_pair; ee_ret.
  - (* EIntLor *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ i1 i2 ]; ee_pair; ee_ret.
  - (* EIntLxor *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ i1 i2 ]; ee_pair; ee_ret.
  - (* EIntLnot *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_int, IHe0 | ]; intros i; ee_pair;
    ee_ret.
  - (* EIntLsl *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ i1 i2 ]; ee_pair; apply erase_if_in_shift_range; ee_ret.
  - (* EIntLsr *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ i1 i2 ]; ee_pair; apply erase_if_in_shift_range; ee_ret.
  - (* EIntAsr *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ i1 i2 ]; ee_pair; apply erase_if_in_shift_range; ee_ret.
  - (* EFloat *)
    simpl_eval; ee_ret.
  - (* EChar *)
    simpl_eval; ee_ret.
  - (* EString *)
    simpl_eval; ee_ret.
  - (* EOpPhysEq *)
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe0_1 | apply IHe0_2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_phys_eq_val | ]; intros b; ee_pair; ee_ret.
  - (* EOpEq *)
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe0_1 | apply IHe0_2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_eq_val | ]; intros b; ee_pair; ee_ret.
  - (* EOpNe *)
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe0_1 | apply IHe0_2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_ne_val | ]; intros b; ee_pair; ee_ret.
  - (* EOpLt *)
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe0_1 | apply IHe0_2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_lt_val | ]; intros b; ee_pair; ee_ret.
  - (* EOpLe *)
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe0_1 | apply IHe0_2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_le_val | ]; intros b; ee_pair; ee_ret.
  - (* EOpGt *)
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe0_1 | apply IHe0_2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_gt_val | ]; intros b; ee_pair; ee_ret.
  - (* EOpGe *)
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe0_1 | apply IHe0_2 ] | ];
    intros [ v1 v2 ]; ee_pair;
    eapply erase_bind; [ apply erase_ge_val | ]; intros b; ee_pair; ee_ret.
  - (* ELet *)
    simpl_eval;
    eapply erase_bind; [ apply erase_eval_bindings, H | ];
    intros δ; ee_pair;
    rewrite <- erase_env_app; apply IHe0.
  - (* ELetRec *)
    simpl_eval. rewrite !bind_ret. rewrite erase_eval_rec_bindings.
    rewrite <- erase_env_app. apply IHe0.
  - (* ESeq *)
    simpl_eval;
    eapply erase_bind; [ apply IHe0_1 | ]; intros w; ee_pair; apply IHe0_2.
  - (* EIfThen *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_bool, IHe0_1 | ]; intros b; ee_pair;
    destruct b; [ apply IHe0_2 | ee_ret ].
  - (* EIfThenElse *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_bool, IHe0_1 | ]; intros b; ee_pair;
    destruct b; [ apply IHe0_2 | apply IHe0_3 ].
  - (* EMatch *)
    simpl_eval;
    apply EM_Handle; [ apply IHe0 | ]; intros o; simpl_wrap_eval_branches;
    eapply erase_bind; [ apply erase_wrap_outcome | ]; intros o'; ee_pair.
    fold erase_branches. apply erase_eval_branches_aux. apply H.
  - (* EShallowMatch *)
    simpl_eval;
    apply EM_Handle; [ apply IHe0 | ]; intros o. fold erase_branches.
    apply erase_shallow_eval_branches_aux; assumption.
  - (* ERaise *)
    simpl_eval;
    eapply erase_bind; [ apply IHe0 | ]; intros w; ee_pair; ee_ret.
  - (* EPerform *)
    simpl_eval;
    eapply erase_bind; [ apply IHe0 | ]; intros w; ee_pair; apply erase_perform.
  - (* EContinue *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par; [ apply erase_as_cont, IHe0_1 | apply IHe0_2 ] | ];
    intros [ l w ]; ee_pair; apply erase_resume.
  - (* EDiscontinue *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par; [ apply erase_as_cont, IHe0_1 | apply IHe0_2 ] | ];
    intros [ l w ]; ee_pair; apply erase_resume.
  - (* EWhile *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_bool, IHe0_1 | ]; intros b; ee_pair;
    destruct b; [ | ee_ret ];
    eapply erase_bind; [ apply IHe0_2 | ]; intros w; ee_pair;
    apply erase_please_eval.
  - (* EFor *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par;
          [ apply erase_as_int, IHe0_1 | apply erase_as_int, IHe0_2 ] | ];
    intros [ i1 i2 ]; ee_pair; apply erase_loop.
  - (* EAssertFalse *)
    simpl_eval; apply EM_Crash.
  - (* EAssert *)
    simpl_eval;
    apply erase_choose; [ ee_ret | ];
    eapply erase_bind; [ apply erase_as_bool, IHe0 | ]; intros b; ee_pair;
    destruct b; [ ee_ret | apply EM_Crash ].
  - (* ELetSitem *)
    simpl.
    unfold eval. rewrite !seal_eq. cbn [pre_eval].
    rewrite fold_pre_eval.
    rewrite fold_pre_eval_bindings.
    rewrite fold_pre_eval_mexpr. rewrite fold_pre_eval_sitem.
    eapply erase_bind.
    (* Here, we need to state exactly the inductive premise of [erase_eval_sitems]. *)
    revert η. change [] with (erase_env []) at 2. generalize (nil : env).
    apply IHe0. simpl in IHe0.
    intros (η' & δ). instantiate (1:= λ '(η, δ), (erase_env η, erase_env δ)). simpl.
    apply IHe1.
  - (* ERef *)
    simpl_eval;
    eapply erase_bind; [ apply IHe0 | ]; intros w; ee_pair;
    eapply erase_bind; [ apply erase_alloc | ]; intros l; ee_pair;
    eapply erase_bind; [ apply erase_alloc_block | ]; intros r; ee_pair; ee_ret.
  - (* ELoad *)
    simpl_eval.
    split.
    + intros η.
      eapply erase_bind; [ apply erase_as_record, IHe0 | ]; intros r; ee_pair;
      eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
      destruct (ls !! 0%Z); [ apply erase_load | apply EM_Crash ].
    + intros η p v. cbn beta iota delta [ eval_resolved ].
      eapply erase_bind; [ apply erase_as_record, IHe0 | ]; intros r; ee_pair;
      eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
      destruct (ls !! 0%Z); [ apply erase_resolve_load | apply EM_Crash ].
  - (* EStore *)
    simpl_eval;
    eapply erase_bind;
      [ apply erase_par; [ apply erase_as_record, IHe0_1 | apply IHe0_2 ] | ];
    intros [ r w ]; ee_pair;
    eapply erase_bind; [ apply erase_load_block | ]; intros [ t ls ]; ee_pair;
    destruct (ls !! 0%Z); [ apply erase_store_op | apply EM_Crash ].
  - (* EFieldLoad *)
    simpl_eval.
    split.
    + intros η.
      eapply erase_bind; [ apply erase_as_loc, IHe0 | ]. intros l. ee_pair.
      apply erase_load.
    + intros η p v. cbn beta iota delta [ eval_resolved ].
      eapply erase_bind; [ apply erase_as_loc, IHe0 | ]. intros l. ee_pair.
      apply erase_resolve_load.
  - (* EExchange *)
    simpl_eval.
    split.
    + intros η.
      eapply erase_bind;
        [ apply erase_par; [ apply erase_as_loc, IHe0_1 | apply IHe0_2 ] | ].
      intros [ l w ]. ee_pair. apply erase_exchange.
    + intros η p v. cbn beta iota delta [ eval_resolved ].
      eapply erase_bind;
        [ apply erase_pair_op; [ apply erase_as_loc, IHe0_1 | apply IHe0_2 ] | ].
      intros [ l w ]. ee_pair. apply erase_resolve_exchange.
  - (* ECAS *)
    simpl_eval.
    split.
    + intros η.
      eapply erase_bind;
        [ apply erase_par;
            [ apply erase_par; [ apply erase_as_loc, IHe0_1 | apply IHe0_2 ]
            | apply IHe0_3 ] | ].
      intros [ [ l seen ] w ]. ee_pair. apply erase_cas.
    + intros η p v. cbn beta iota delta [ eval_resolved ].
      eapply erase_bind;
        [ apply erase_par;
            [ apply erase_par; [ apply erase_as_loc, IHe0_1 | apply IHe0_2 ]
            | apply IHe0_3 ] | ].
      intros [ [ l seen ] w ]. ee_pair. apply erase_resolve_cas.
  - (* EFAA *)
    simpl_eval.
    split.
    + intros η.
      eapply erase_bind;
        [ apply erase_par;
            [ apply erase_as_loc, IHe0_1 | apply erase_as_int, IHe0_2 ] | ].
      intros [ l i ]. ee_pair. apply erase_faa.
    + intros η p v. cbn beta iota delta [ eval_resolved ].
      eapply erase_bind;
        [ apply erase_par;
            [ apply erase_as_loc, IHe0_1 | apply erase_as_int, IHe0_2 ] | ].
      intros [ l i ]. ee_pair. apply erase_resolve_faa.
  - (* ENewProph *)
    simpl_eval; apply erase_new_proph.
  - (* EResolve *)
    simpl_eval.
    destruct (lookup_path η π) as [ [ ] | ]; try unfold as_proph; simpl;
    try apply EM_CrashL.
    destruct (eval_proph_arg η a) as [ w | ]; simpl; try apply EM_CrashL.
    rewrite bind_ret. simpl. rewrite !bind_ret.
    apply IHe0.
  - (* EIgnore *)
    simpl_eval;
    eapply erase_bind; [ apply IHe0 | ]; intros w; ee_pair; ee_ret.
  - (* EFork *)
    simpl_eval;
    eapply erase_bind; [ apply erase_par; [ apply IHe0_1 | apply IHe0_2 ] | ];
    intros [ f w ]; ee_pair; apply erase_fork.
  - (* EJoin *)
    simpl_eval;
    eapply erase_bind; [ apply erase_as_thread, IHe0 | ]; intros t; ee_pair;
    apply erase_join.
  - (* Fexpr *)
    simpl.
    apply IHe0.
  - (* Branch *)
    simpl.
    apply IHe0.
  - (* Binding *)
    simpl.
    apply IHe0.
  - (* ILet *)
    intros δ η; simpl_eval_sitem;
    eapply erase_bind; [ apply erase_eval_bindings; assumption |  intros δ'; ee_pair ].
    rewrite <- !erase_env_app.
    ee_ret.
  - (* ILetRec *)
    simpl. fold erase_rec_bindings. simpl_eval_sitem.
    intros δ η. rewrite erase_eval_rec_bindings, <- !erase_env_app.
    ee_ret.
  - (* IModule *)
    simpl. intros δ η.
    simpl_eval_sitem. eapply erase_bind. { revert η. apply IHe0. }
    intros v. ee_ret.
  - (* IOpen *)
    simpl. intros δ η.
    simpl_eval_sitem.
    eapply erase_bind.
    { apply erase_as_struct. apply IHe0. }
    intros η'. rewrite <- erase_env_app.
    ee_ret.
  - (* IInclude *)
    simpl. intros δ η.
    simpl_eval_sitem. eapply erase_bind. { apply erase_as_struct. apply IHe0. }
    intros η'. rewrite <- !erase_env_app.
    ee_ret.
  - (* IExternal *)
    simpl. intros δ η.
    simpl_eval_sitem. eapply erase_bind. { apply IHe0. }
    intros v. ee_ret.
  - (* IExtend *)
    simpl. intros δ η.
    simpl_eval_sitem. eapply erase_bind. { apply erase_eval_type_extensions. }
    intros η'. rewrite <- !erase_env_app. ee_ret.
  - (* MUnsupported *)
    intros η; simpl_eval_mexpr; apply EM_Crash.
  - (* MPath *)
    intros η; simpl_eval_mexpr;
    rewrite erase_lookup_path; apply erase_of_option.
  - (* MStruct *)
    intros η; simpl_eval_mexpr;
    eapply erase_bind. fold erase_sitems. apply erase_eval_sitems; assumption.
    intros (? & ?); ee_pair; ee_ret.
  - (* MFunctor *)
    intros η; simpl_eval_mexpr; ee_ret.
  - (* MCoercion *)
    intros η; simpl_eval_mexpr;
    eapply erase_bind.
    { apply IHe0. }
    intros v; ee_pair;
    rewrite erase_coerce; apply erase_of_option.
Qed.

(* -------------------------------------------------------------------------- *)

(** ** Branch lists on their own. *)

(* The metatheory also meets a branch list with no expression in scope:
   [StepWrap] stores a continuation re-installing a handler, whose branches
   are the [CWrap] argument. [branches_ind] would mean re-proving all of
   [expr_ind]'s premises; the bodies only need [erase_eval], so a plain
   induction on the list does. *)

Lemma erase_eval_branches bs :
  ∀ η o, erase_microvx (eval_branches η o bs)
           (eval_branches (erase_env η) (erase_out3 o) (erase_branches bs)).
Proof.
  apply erase_eval_branches_aux.
  induction bs as [| [ cp e0 ] bs IH ].
  constructor.
  constructor; last apply IH.
  apply erase_eval.
Qed.

Lemma erase_shallow_eval_branches bs :
  ∀ η all_bs o,
    erase_microvx (shallow_eval_branches η bs all_bs o)
      (shallow_eval_branches (erase_env η) (erase_branches bs)
                             (erase_branches all_bs) (erase_out3 o)).
Proof.
  apply erase_shallow_eval_branches_aux.
  induction bs as [| [ cp e0 ] bs IH ].
  constructor.
  constructor; last apply IH.
  apply erase_eval.
Qed.


Lemma erase_wrap_eval_branches η bs o :
  erase_microvx (wrap_eval_branches η bs o)
    (wrap_eval_branches (erase_env η) (erase_branches bs) (erase_out3 o)).
Proof.
  simpl_wrap_eval_branches.
  eapply erase_bind; [ apply erase_wrap_outcome | ]. intros o'. ee_pair.
  apply erase_eval_branches.
Qed.


(* [StepLoop] replaces the [CLoop] call by the loop's own definition, so the
   metatheory needs the erasure of that too, not only of the call.
   [erase_loop] above relates the calls. *)

Lemma erase_loop_body η x i1 i2 e :
  erase_microvx (E.loop η x i1 i2 e) (E.loop (erase_env η) x i1 i2 (erase_expr e)).
Proof.
  unfold E.loop. case_match.
  - (* the last iteration: run the body and stop *)
    eapply erase_bind; [ apply erase_eval | ]. intros w. ee_pair. ee_ret.
  - case_match.
    + (* the bounds cross: nothing to do *)
      ee_ret.
    + (* run the body, then ask for the next iteration *)
      eapply erase_bind; [ apply erase_eval | ]. intros w. ee_pair.
      apply erase_loop.
Qed.
