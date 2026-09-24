From osiris.utils Require Import tactics.
From osiris.lang Require Import encode type_nel constructors.
From osiris.program_logic Require Import program_logic osiris_utils.
Require Import env_lookups tactics.
From stdpp Require Import strings.
From Ltac2 Require Import Ltac2 Printf.

Ltac2 rec utypes_from_exprs (es : constr) : constr :=
  lazy_match! es with
  | cons _ nil => open_constr:(type_nel.Tbase _)
  | cons _ ?es  =>
    let base := utypes_from_exprs es in
    open_constr:(type_nel.Tcons _ $base)
  | nil =>
    Control.throw
        (Tactic_failure
           (Some
              (Message.of_string "Cannot build empty [types]. ")))
  end.


Ltac2 imp_int_tac () :=
  let e := get_expr () in
  lazy_match! eval hnf in $e with
  | EInt _ => iApply imp_EInt
  | EMaxInt => iApply imp_EMaxInt
  | EMinInt => iApply imp_EMinInt
  | _ =>
      Control.zero
        (Tactic_failure
           (Some (fprintf "Expected %t to be an int literal" e)))
  end.

Ltac2 Notation "imp_int" := imp_int_tac ().
Tactic Notation "imp_int" := ltac2:(imp_int).

Ltac2 Type arith_type :=
  [ Literal | Op | Op_frac(constr) | Comparison ].

Ltac2 fetch_appropriate_arith_lemma (e : constr) (r : constr option) : (constr * arith_type) option :=
  lazy_match! e with
  | EInt _ => Some ('imp_EInt, Literal)
  | EMaxInt => Some ('imp_EMaxInt, Literal)
  | EMinInt => Some ('imp_EMinInt, Literal)
  | EIntAdd _ _ =>
    match r with
    | Some r => Some ('imp_EIntAdd_frac, Op_frac r)
    | None => Some ('imp_EIntAdd, Op)
    end
  | EIntSub _ _ => Some ('imp_EIntSub, Op)
  | EIntMul _ _ =>
    match r with
    | Some r => Some ('imp_EIntMul_frac, Op_frac r)
    | None => Some ('imp_EIntMul, Op)
    end
  | EIntDiv _ _ => Some ('imp_EIntDiv, Op)
  | EIntMod _ _ => Some ('imp_EIntMod, Op)
  | EOpEq _ _ => Some ('imp_EOpEq_Z, Comparison)
  | EOpNe _ _ => Some ('imp_EOpNe_Z, Comparison)
  | EOpLt _ _ => Some ('imp_EOpLt_Z, Comparison)
  | EOpLe _ _ => Some ('imp_EOpLe_Z, Comparison)
  | EOpGt _ _ => Some ('imp_EOpGt_Z, Comparison)
  | EOpGe _ _ => Some ('imp_EOpGe_Z, Comparison)
  | _ => None
  end.

Ltac2 representable () := ltac1:(int.representable).

(* [mk_evar id ty] introduces a local let-binding [id : ty := ?x] into the
   proof context, where [?x] is a fresh metavariable.  The head symbol [id]
   is syntactically rigid, so [Hint Mode Encode +] is satisfied when Coq later
   searches for [Encode id], while the actual type is still deferred. *)
Ltac2 mk_evar (id : ident) (ty : constr) :=
  let v := open_constr:((_ : $ty)) in
  Std.pose (Some id) v.

Ltac2 get_pointsto (l : constr) : constr * constr :=
  let (_, spat_hyps) := get_iris_hyps () in
  let rec go env :=
    lazy_match! env with
    | environments.Enil =>
        Control.zero (Tactic_failure
                        (Some (fprintf "Could not find hypothesis [%t ↦ₗ _]" l)))
    | environments.Esnoc ?env ?name ?prop =>
        match! prop with
        | (?l' ↦ₗ (#?a))%I =>
            if Constr.equal l l' then
              (name, Constr.type a)
            else
              go env
        | (▷ ?l' ↦ₗ (#?a))%I =>
            if Constr.equal l l' then
              (name, Constr.type a)
            else
              go env
        (* A bare (unencoded) stored value is just a [val]. *)
        | (?l' ↦ₗ ?v)%I =>
            if Constr.equal l l' then
              (name, Constr.type v)
            else
              go env
        | (▷ ?l' ↦ₗ ?v)%I =>
            if Constr.equal l l' then
              (name, Constr.type v)
            else
              go env
        | _ => go env
        end
    end
  in
  go spat_hyps.

(* The same, for a reference points-to [r ↦ _]. *)
Ltac2 get_ref_pointsto (r : constr) : constr * constr :=
  let (_, spat_hyps) := get_iris_hyps () in
  let rec go env :=
    lazy_match! env with
    | environments.Enil =>
        Control.zero (Tactic_failure
                        (Some (fprintf "Could not find hypothesis [%t ↦ _]" r)))
    | environments.Esnoc ?env ?name ?prop =>
        match! prop with
        | (?r' ↦ (#?a))%I =>
            if Constr.equal r r' then (name, Constr.type a) else go env
        | (▷ ?r' ↦ (#?a))%I =>
            if Constr.equal r r' then (name, Constr.type a) else go env
        | (?r' ↦ ?v)%I =>
            if Constr.equal r r' then (name, Constr.type v) else go env
        | (▷ ?r' ↦ ?v)%I =>
            if Constr.equal r r' then (name, Constr.type v) else go env
        | _ => go env
        end
    end
  in
  go spat_hyps.

Ltac2 is_Some (o : constr option) : bool :=
  match o with
  | Some _ => true
  | None => false
  end.

Ltac2 is_arith_expr (e : constr) : bool :=
  match! e with
  | EInt _ => true
  | EMaxInt => true
  | EMinInt => true
  | EIntAdd _ _ => true
  | EIntSub _ _ => true
  | EIntMul _ _ => true
  | EIntDiv _ _ => true
  | EIntMod _ _ => true
  | EOpEq _ _ => true
  | EOpNe _ _ => true
  | EOpLt _ _ => true
  | EOpLe _ _ => true
  | EOpGt _ _ => true
  | EOpGe _ _ => true
  | _ => false
  end.

(* [selpat_from_reading] is used when the tactics are reading from a
   given resource.

   When we apply lemmas (such as [imp_EIntAdd_frac], for example), the
   user may have specified a "reading" resource and additional
   resources to be split amongst the subgoals.

   We get the right selection pattern to feed to [imp_EIntAdd_frac] by
   concatenating the name of the reading resource and the selection
   pattern. *)

Ltac2 selpat_from_reading (selpat : constr option) (reading : constr option) : constr :=
  match selpat, reading with
  | Some s, Some r => '(String.concat $r $s)
  | Some s, None => s
  | None, Some r => r
  | None, None => '""
  end.

(* [unfold_impure_evals] dispatches resources amongst the elements of
   a tuple via a selection pattern with one bracketed group per
   element, e.g. ["[Hx] [Hy]"].  Each [imp_evals_cons] is a binary
   wand splitting the head element from the tail; we peel the first
   group off for the head and pass the remaining groups down the
   recursion.  Because an under-specified pattern leaves the trailing
   premise with whatever spatial resources the leading premises did
   not claim, naming only the head group at each step is enough.

   [selpat_head] returns the first ["[...]"] group, [selpat_tail] the
   rest of the pattern. *)

Definition selpat_head (s : string) : string :=
  match String.index 0 "]" s with
  | Some j => String.substring 0 (S j) s
  | None => s
  end.

Definition selpat_tail (s : string) : string :=
  match String.index 0 "]" s with
  | Some j => String.substring (S j) (String.length s - S j) s
  | None => ""
  end.

Ltac2 rec unfold_impure_evals (selpat : constr option) :=
  let e := get_iris_goal () in
  lazy_match! e with
  | impure _ (evals _ [_]) _ _ _  =>
    match selpat with
    | None => iApply imp_evals_singleton
    | Some s => iApply (imp_evals_singleton with (selpat_head $s))
    end
  | impure _ (evals _ (_ :: _)) _ _ _ =>
    match selpat with
    | None =>
      iApply imp_evals_cons >
      [ | unfold_impure_evals None ]
    | Some s =>
      iApply (imp_evals_cons with (selpat_head $s)) >
      [ | unfold_impure_evals (Some '(selpat_tail $s)) ]
    end
  end.

(* Discharges the monotonicity goal left by [imp_ETuple] when the
   tuple is being solved automatically (i.e. without a user-provided
   selection pattern): the per-element postcondition is taken to be
   the tuple postcondition itself, which closes the goal whenever the
   latter is still an evar or already has the per-element shape. *)
Ltac2 discharge_tuple_mono () :=
  iApply tuple_mono_refl.

Ltac2 get_postcondition_arg_type () :=
  let phi :=
    lazy_match! get_iris_goal () with
    | impure _ _ _ _ ?phi => phi
    end
  in
  lazy_match! Constr.type phi with
  | ?b → _ =>
    (* In an [evals] context the domain appears as
       [coerce_to_type (Tbase B)]; reduce it so instance search
       keys on [B] itself (the coerced form selects
       [Encode_tuple] instead of the element type's own
       [Encode] instance).  [coerce_to_type] is [simpl never],
       hence the targeted [cbv]. *)
    (eval cbv beta iota delta [type_nel.coerce_to_type] in $b)
  end.

(* Specializes [imp_EConstant] (or [imp_EConstant'] when [primed]) to
   the constant [c] of the focused goal's expression and to the domain
   type [B] of its postcondition.  Both keys must be concrete at
   elaboration time so that the [Constant c B] instance is resolved
   then: an application left with an unresolved instance cannot unify
   [constant_value] against a fixed postcondition. *)
Ltac2 specialized_imp_EConstant (primed : bool) (bopt : constr option) : constr :=
  let e := get_expr () in
  let c :=
    lazy_match! eval hnf in $e with
    | EData ?c [] => c
    end
  in
  let b :=
    match bopt with
    | Some b => b
    | None => get_postcondition_arg_type ()
    end
  in
  (* Determining the [Constant] instance; kept in step with the twin
     logic in [pure_const0] (pure_tactics.v). *)
  let hc := determine_Constant_instance c b in
  if primed then '(imp_EConstant' (HC:=$hc))
  else '(imp_EConstant (HC:=$hc)).

Ltac2 rec imp_step0 (reading : constr option) :=
  let e := get_expr () in
  let e := (eval hnf in $e) in
  let complete_steps := fun () => complete (fun () => imp_step0 reading) in
  if is_arith_expr e then imp_arith_tac None reading else
  lazy_match! e with
  | EPath _ => imp_path
  | EFieldLoad _ => imp_load0 None reading
  (* References. *)
  | ERef _ => imp_alloc0 None reading
  | ELoad _ => iApply (imp_deref with "[$]"); try (imp_step0 reading)
  | EStore _ _ =>
      Control.plus
        (fun _ => iApply (imp_assign with "[$]");
                  Control.dispatch [(fun _ => imp_step0 reading); complete_steps])
        (fun _ =>
           mk_evar @imp_store_A 'Type;
           let store_a := Control.hyp @imp_store_A in
           mk_evar @imp_store_HA open_constr:(Encode $store_a);
           let specialized_store := open_constr:(imp_assign' (A:=$store_a)) in
           iApply ($specialized_store with "[$]");
           try (imp_step0 reading))
  | ERecordAccess _ _ => imp_field_access0 reading
  | ERecordSet _ _ _ => imp_field_set0 reading
  | EData _ _ => imp_data0 None reading
  | ETuple _ =>
      (* Without a selection pattern we cannot, in general, split the
         resources between the elements.  Rather than leave the proof
         in a half-finished state, we wrap the whole tuple resolution
         in [complete]: either it clears the goal (elements stepped and
         the monotonicity goal discharged), or it fails atomically and
         leaves the goal untouched. *)
      complete (fun () =>
        imp_tuple0 None reading;
        Control.enter (fun () =>
          Control.plus
            (fun () => imp_step0 reading)
            (fun _ => discharge_tuple_mono ())))
  | ERecord _ _ =>
      complete (fun () => imp_record0 None reading None)
  | EInline _ _ _ =>
      complete (fun () => imp_record0 None reading None)
  | ERecordAccess _ _ => imp_record_access0 None
  | _ =>
      Control.zero
        (Tactic_failure
           (Some (fprintf "[imp_step] doesn't know how to handle expression %t" e)))
  end

with imp_tuple0 (selpat : constr option) (reading : constr option) :=
  let e := get_expr () in
  let e := (eval hnf in $e) in
  lazy_match! e with
  | ETuple ?es =>
    let τ := utypes_from_exprs es in
    (* Once the [evals] of the elements is in focus, split the
       resources amongst the elements (according to [selpat]) and step
       each one. *)
    let step_elements () :=
      unfold_impure_evals selpat;
      Control.enter (fun () => try (imp_step0 reading))
    in
    (* Inspect the tuple postcondition to pick the right rule. *)
    let post :=
      lazy_match! get_iris_goal () with
      | impure _ _ _ _ ?phi => phi
      end
    in
    if Constr.is_evar post then
      (* The postcondition is still an evar:
         we use the monotonicity-free rule. *)
      let specialized_tuple := '(imp_ETuple_evar (τ:=$τ)) in
      iApply $specialized_tuple; step_elements ()
    else
      (* The postcondition is fixed: use the rule with the built-in
         monotonicity premise.  We send all the spatial resources to
         the [evals] premise (["[-] []"]) so they can be split amongst
         the elements, step them, and leave only the monotonicity goal
         to the user. *)
      let specialized_tuple := '(imp_ETuple (τ:=$τ)) in
      let select_evals := '"[-] []" in
      iApply ($specialized_tuple with $select_evals) >
      [ step_elements () | simpl type_nel.tforall ]
  end

with imp_data0 (selpat : constr option) (reading : constr option) :=
  let e := get_expr () in
  let e := (eval hnf in $e) in
  lazy_match! e with
  | EData _ [] =>
      let lem := specialized_imp_EConstant false None in
      iApply $lem
  | EData _ _ =>
    (* Like [imp_tuple0]: split the resources amongst the constructor
       arguments (according to [selpat]) and step each one. *)
    let step_args () :=
      unfold_impure_evals selpat;
      Control.enter (fun () => try (imp_step0 reading))
    in
    let post :=
      lazy_match! get_iris_goal () with
      | impure _ _ _ _ ?phi => phi
      end
    in
    if Constr.is_evar post then
      (* The postcondition is still an evar: use the monotonicity-free
         rule, which sets it to [λ x, ∃# xs, ⌜x = ctor_apply xs⌝ ∗ Φs xs],
         determined by the split.  No monotonicity goal is left behind. *)
      (iApply imp_EData_evar; step_args ())
    else
      (* The postcondition is fixed: use the rule with the built-in
         monotonicity premise.  We send all the spatial resources to the
         [evals] premise (["[-] []"]) so they can be split amongst the
         arguments, step them, and leave only the monotonicity goal to
         the user. *)
      let select_evals := '"[-] []" in
      iApply (imp_EData with $select_evals) >
      [ step_args () | simpl constructors.ctor_apply; simpl type_nel.tforall ]
  | _ =>
    Control.zero
        (Tactic_failure
           (Some (fprintf "[imp_data] doesn't know how to handle expression %t" e)))
  end

with imp_load0 (l : constr option) (reading : constr option) :=
  let specialized_load :=
    match l with
    | Some l => open_constr:(imp_EFieldLoad _ _ $l)
    | None => 'imp_EFieldLoad
    end
  in
  iApply ($specialized_load with "[$]");
  try (imp_step0 reading)

with imp_alloc0 (x : constr option) (reading : constr option) :=
  match x with
  | Some x =>
      let spec_ref := open_constr:(imp_ref $x) in
      iApply $spec_ref; try (imp_step0 reading)
  | None =>
      Control.plus
        (fun _ => iApply imp_ref;
                  complete (fun _ => imp_step0 None))
        (fun _ => iApply imp_ref2; try (imp_step0 reading))
  end

with imp_arith_tac (selpat : constr option) (reading : constr option) :=
  let e := get_expr () in
  let e := eval hnf in $e in
  let s := selpat_from_reading selpat reading in
  match fetch_appropriate_arith_lemma e reading with
  | Some (lemma, arith_kind) =>
      match arith_kind with
      | Op_frac r =>
          (* Try direct application first; if the postcondition shape doesn't
             unify with the lemma's conclusion, fall back via imp_wand so the
             user only needs to close the resulting monotonicity subgoal. *)
          Control.plus
            (fun _ =>
               iApply ($lemma with $s);
               iIntros $r; Control.enter (fun _ => try (imp_step0 reading)))
            (fun _ =>
               let select_all := '"[-]" in
               iApply (imp_wand with $select_all);
               Control.focus 1 1 (fun _ =>
                 iApply ($lemma with $s);
                 iIntros $r; Control.enter (fun _ => try (imp_step0 reading))))
      | _ =>
          iApply ($lemma with $s);
          match arith_kind with
          | Literal => ()
          | Op =>
              Control.extend [] (fun _ => try (imp_step0 None))
                [ fun _ =>
                    simple_intros ();
                    lazy_match! get_iris_goal () with
                    | bi_wand _ _ => ()
                    (* When the postcondition is still an evar, the goal
                       is [?Φ result]; [auto] chokes on it (it tries to
                       frame the persistent context against the evar), so
                       we first try [solve_eq_goal], which instantiates
                       [?Φ] to [λ x, ⌜x = result⌝].  Fall back to [auto]
                       for a concrete postcondition. *)
                    | _ =>
                        Control.plus
                          (fun _ => complete (fun _ => solve_eq_goal ()))
                          (fun _ => auto)
                    end ]
          | Op_frac _ => ()
          | Comparison =>
              lastn [ (fun _ => imp_step0 reading); (fun _ => imp_step0 reading) ];
              firstn [ representable; representable ]
          end
      end
  | None =>
      Control.zero
        (Tactic_failure
           (Some (fprintf "Expected %t to be an arithmetic expression" e)))
  end

with imp_record0 (selpat : constr option) (reading : constr option) (a_opt : constr option) :=
  let e := get_expr () in
  let e := (eval hnf in $e) in
  let specialized_lemma () :=
    (* [a_opt], when given, pins the [RecordRepr]'s logical model type [A]
       explicitly (via [imp_record $! A]), instead of leaving both [A] and
       the field types of [τ] to typeclass search. This is needed whenever
       more than one [RecordRepr] instance shares the same field-count
       shape (e.g. two distinct single-field [Mut] records): search alone
       cannot tell them apart and silently picks an arbitrary match, so the
       caller must disambiguate by hand. *)
    match! e with
    | ERecord _ ?es =>
      match a_opt with
      | Some a => '(imp_record (A:=$a))
      | None =>
        let τ := utypes_from_exprs es in
        '(imp_record (τ:=$τ))
      end
    | EInline _ _ ?es =>
      match a_opt with
      | Some a => '(imp_inline_record (A:=$a))
      | None =>
        let τ := utypes_from_exprs es in
        '(imp_inline_record (τ:=$τ))
      end
    | _ =>
      Control.zero
        (Tactic_failure
           (Some (fprintf "[imp_record] doesn't know how to handle expression %t" e)))
    end
  in
  let step_elements () :=
    (* Once the [evals] of the elements is in focus, split the
       resources amongst the elements (according to [selpat]) and step
       each one. *)
    unfold_impure_evals selpat;
    Control.enter (fun () => try (imp_step0 reading))
  in
  (* When the goal's postcondition is at a type other than [record], the
     expression builds a value of a *variant* type whose constructor
     carries this inline record (the [Root]/[Link] situation). The plain
     rule is [record]-typed, so fall back to [imp_inline_record_as], which
     recovers the constructor from the [Inline] class keyed on [c]. *)
  let apply_record_as () :=
    lazy_match! e with
    | EInline ?c _ ?es =>
        let lemma :=
          match a_opt with
          | Some b => '(imp_inline_record_as (B:=$b) $c (inline_apply (c:=$c)))
          | None =>
              let τ := utypes_from_exprs es in
              '(imp_inline_record_as (τ:=$τ) $c (inline_apply (c:=$c)))
          end
        in
        iApply $lemma >
          [ ltac1:(intro; symmetry; apply inline_encode)
          | simpl; try ltac1:(lia)
          | step_elements () ]
    | _ =>
        Control.zero
          (Tactic_failure
             (Some (fprintf "[imp_record] doesn't know how to handle expression %t" e)))
    end
  in
  (* Which rule applies is decided by the postcondition's domain type,
     rather than by trying the plain rule and falling back: a failed
     [iApply] still elaborates its lemma, and the evars it creates for the
     implicit [{η E Ψ ζ}] stay on the shelf even after backtracking,
     surfacing as "remaining shelved goals" at [Qed].

     The test is exact: both plain rules conclude with a [record]-typed
     postcondition, so a domain that is neither [record] nor an evar is
     precisely what they cannot handle. *)
  let use_record_as () :=
    lazy_match! get_iris_goal () with
    | impure _ _ _ _ ?phi =>
        match Constr.Unsafe.kind (Constr.type phi) with
        | Constr.Unsafe.Prod b _ =>
            let a := Constr.Binder.type b in
            if Constr.is_evar a then false
            else if Constr.equal a 'record then false
            else true
        | _ => false
        end
    | _ => false
    end
  in
  let apply_record () :=
    if use_record_as () then apply_record_as ()
    else
      let lemma := specialized_lemma () in
      iApply $lemma >
        [ simpl; try ltac1:(lia) | step_elements () ]
  in
  let post :=
    lazy_match! get_iris_goal () with
    | impure _ _ _ _ ?phi => phi
    end
  in
  if Constr.is_evar post then apply_record ()
  else
    (* The postcondition is fixed: it cannot unify with the rule's
       [∃# xs, ownRecord …] shape directly, so step the record against
       a fresh postcondition via [imp_wand] (sending it all the spatial
       resources) and leave the entailment into the goal's
       postcondition to the user. *)
    let select_all := '"[-]" in
    iApply (imp_wand with $select_all) >
      [ apply_record () | ]

with imp_record_access0 (r : constr option) :=
  let specialized_load :=
    match r with
    | Some r => open_constr:(imp_record_access _ $r)
    | None => 'imp_record_access
    end
  in
  iApply ($specialized_load with "[$]");
  Control.dispatch [ (fun _ => split; simpl; ltac1:(lia)); (fun _ => imp_step0 None) ]

(* Reading or writing a single field: use a field points-to [r ↦[f] _]
   from the context when there is one; a read otherwise falls back to the
   ownership of the whole record. *)
with imp_field_access0 (reading : constr option) :=
  Control.plus
    (fun _ => iApply (imp_ERecordAccess_field with "[$]"); try (imp_step0 reading))
    (fun _ => imp_record_access0 None)

with imp_field_set0 (reading : constr option) :=
  iApply (imp_ERecordSet_field with "[$]");
  Control.dispatch
    [(fun _ => imp_step0 reading); (fun _ => complete (fun () => imp_step0 reading))].

Tactic Notation "imp_load" constr(l) :=
  let tac := ltac2:(l |- imp_load0 (Ltac1.to_constr l) None) in
  tac l.
Tactic Notation "imp_load" := ltac2:(imp_load0 None None).

Tactic Notation "imp_tuple" := ltac2:(imp_tuple0 None None).
Tactic Notation "imp_tuple" "with" constr(sel) :=
  let tac := ltac2:(sel |- imp_tuple0 (Ltac1.to_constr sel) None) in
  tac sel.

Tactic Notation "imp_data" := ltac2:(imp_data0 None None).
Tactic Notation "imp_data" "with" constr(sel) :=
  let tac := ltac2:(sel |- imp_data0 (Ltac1.to_constr sel) None) in
  tac sel.

Tactic Notation "imp_record" := ltac2:(imp_record0 None None None).
Tactic Notation "imp_record" "with" constr(sel) :=
  let tac := ltac2:(s |- imp_record0 (Ltac1.to_constr s) None None) in
  tac sel.
Tactic Notation "imp_record" "$!" constr(a) :=
  let tac := ltac2:(a |- imp_record0 None None (Ltac1.to_constr a)) in
  tac a.
Tactic Notation "imp_record" "with" constr(sel) "$!" constr(a) :=
  let tac := ltac2:(sel a |- imp_record0 (Ltac1.to_constr sel) None (Ltac1.to_constr a)) in
  tac sel a.

Tactic Notation "imp_record_read" constr(r) :=
  let tac := ltac2:(r |- imp_record_access0 (Ltac1.to_constr r)) in
  tac r.
Tactic Notation "imp_record_read" := ltac2:(imp_record_access0 None).

Tactic Notation "imp_step" := ltac2:(imp_step0 None).
Tactic Notation "imp_step" "reading" constr(c) :=
  let tac := ltac2:(c |- imp_step0 (Ltac1.to_constr c)) in
  tac c.


Tactic Notation "imp_ref" constr(x) :=
  let tac := ltac2:(x |- imp_alloc0 (Ltac1.to_constr x) None) in
  tac x.
Tactic Notation "imp_ref" := ltac2:(imp_alloc0 None None).

(* [imp_store r x] steps an assignment [e1 := e2] to the reference [r]. *)
Ltac2 imp_store_tac (l : constr) (x : constr option) :=
  let (hl, a) := get_ref_pointsto l in
  match x with
  | Some x =>
      let specialized_store := open_constr:(imp_assign $l $x) in
      iApply ($specialized_store with $hl) >
       [try (imp_step0 None) | try (imp_step0 None) ]
  | None =>
      let specialized_store := open_constr:(imp_assign' (A:=$a) _ $l) in
      iApply ($specialized_store with $hl) >
        [try (imp_step0 None) | try (imp_step0 None) |
          iIntros "!>"; cbn beta;
          lazy_match! get_iris_goal () with
          | bi_forall (λ a, bi_wand (bi_pure (a = _)) _) =>
              let name := match! hl with | base.ident.INamed ?s => s | _ => '"" end in
              let pat := '("% -> " ++ $name)%string in
              iIntros $pat; auto
          end
        ]
  end.

Ltac2 imp_store2_tac (l : constr) :=
  let specialized_store2 := open_constr:(imp_assign2 $l) in
  iApply $specialized_store2; try (imp_step0 None).

Ltac2 Notation "imp_store" l(constr) x(constr) := imp_store_tac l (Some x).
Ltac2 Notation "imp_store" l(constr) := imp_store_tac l None.
Tactic Notation "imp_store" constr(l) constr(x) :=
  let tac := ltac2:(l x |- imp_store_tac (Option.get (Ltac1.to_constr l)) (Ltac1.to_constr x)) in
  tac l x.
Tactic Notation "imp_store" constr(l) :=
  let tac := ltac2:(l |- imp_store_tac (Option.get (Ltac1.to_constr l)) None) in
  tac l.
Ltac2 Notation "imp_store2" l(constr) := imp_store2_tac l.
Tactic Notation "imp_store2" constr(l) :=
  let tac := ltac2:(l |- imp_store2_tac (Option.get (Ltac1.to_constr l))) in
  tac l.

(* [imp_store' r $! Φ] steps an assignment [e1 := e2] to the reference
   [r]. It locates the hypothesis [r ↦ _], applies [imp_assign'] with
   final postcondition [Φ], and steps [e1] and [e2], leaving the
   continuation goal [∀ a, Φ' a -∗ r ↦ #a -∗ Φ].

   The [Encode] instance of the stored value cannot be inferred at
   application time (its type is still undetermined), so it is computed
   from the syntax of [e2]: an inline record [EInline c t es] is encoded
   by [encode_record c]; otherwise we default to the type of the value
   currently stored in [r]. *)

Ltac2 imp_store'_tac (l : constr) (phi : constr option) :=
  let (hl, a) := get_ref_pointsto l in
  let e := get_expr () in
  let e := (eval hnf in $e) in
  let e2 :=
    lazy_match! e with
    | EStore _ ?e2 => e2
    | _ =>
        Control.zero
          (Tactic_failure
             (Some (fprintf "[imp_store'] expected %t to be an assignment" e)))
    end
  in
  let lemma :=
    lazy_match! eval hnf in $e2 with
    | EInline ?c _ _ =>
        match phi with
        | Some phi => open_constr:(imp_assign' (H:=encode_record $c) (Φ:=$phi) _ $l)
        | None => open_constr:(imp_assign' (H:=encode_record $c) _ $l)
        end
    | _ =>
        match phi with
        | Some phi => open_constr:(imp_assign' (A:=$a) (Φ:=$phi) _ $l)
        | None => open_constr:(imp_assign' (A:=$a) _ $l)
        end
    end
  in
  iApply ($lemma with $hl) >
    [ try (imp_step0 None) | try (imp_step0 None) | () ].

Ltac2 Notation "imp_store'" l(constr) := imp_store'_tac l None.
Ltac2 Notation "imp_store'" l(constr) "$!" phi(constr) := imp_store'_tac l (Some phi).
Tactic Notation "imp_store'" constr(l) :=
  let tac := ltac2:(l |- imp_store'_tac (Option.get (Ltac1.to_constr l)) None) in
  tac l.
Tactic Notation "imp_store'" constr(l) "$!" constr(phi) :=
  let tac := ltac2:(l phi |- imp_store'_tac (Option.get (Ltac1.to_constr l)) (Ltac1.to_constr phi)) in
  tac l phi.

(* [imp_ref'] steps an allocation [ref e]: it applies [imp_ref2'],
   steps [e], and leaves the continuation goal
   [∀ a r, Φ a -∗ r ↦ #a -∗ Φ' r]. As in [imp_store'], the [Encode]
   instance of the allocated value is computed from the syntax of
   [e]. *)

Ltac2 imp_ref'_tac () :=
  let e := get_expr () in
  let e := (eval hnf in $e) in
  let e1 :=
    lazy_match! e with
    | ERef ?e1 => e1
    | _ =>
        Control.zero
          (Tactic_failure
             (Some (fprintf "[imp_ref'] expected %t to be a ref expression" e)))
    end
  in
  let lemma :=
    lazy_match! eval hnf in $e1 with
    | EInline ?c _ _ => open_constr:(imp_ref2' (H:=encode_record $c))
    | ERecord _ _ => open_constr:(imp_ref2' (A:=record))
    | _ =>
        Control.zero
          (Tactic_failure
             (Some (fprintf "[imp_ref'] cannot determine the encoding of %t; use [imp_ref] or apply [imp_ref2'] with explicit [A]/[H]" e1)))
    end
  in
  iApply $lemma >
    [ try (imp_step0 None) | () ].

Ltac2 Notation "imp_ref'" := imp_ref'_tac ().
Tactic Notation "imp_ref'" := ltac2:(imp_ref'_tac ()).

(* Ltac2 imp_arith_tac (selpat : constr option) (reading : constr option) := *)
(*   let e := get_expr () in *)
(*   let e := eval hnf in $e in *)
(*   let s := *)
(*     match selpat, reading with *)
(*     | Some s, Some r => '(String.concat $s $r) *)
(*     | Some s, None => s *)
(*     | None, _ => '"" *)
(*     end *)
(*   in *)
(*   match fetch_appropriate_arith_lemma e reading with *)
(*   | Some (lemma, arith_kind) => *)
(*       iApply ($lemma with $s); *)
(*       match arith_kind with *)
(*       | Literal => () *)
(*       | Op => *)
(*           Control.extend [] (fun _ => try (imp_step0 reading)) *)
(*             [ fun _ => *)
(*                 simple_intros (); *)
(*                 lazy_match! get_iris_goal () with *)
(*                 | bi_wand _ _ => () *)
(*                 | _ => auto *)
(*                 end ] *)
(*       | Comparison => *)
(*           lastn [ (fun _ => imp_step0 reading); (fun _ => imp_step0 reading) ]; *)
(*           firstn [ representable; representable ] *)
(*       end *)
(*   | None => *)
(*       Control.zero *)
(*         (Tactic_failure *)
(*            (Some (fprintf "Expected %t to be an arithmetic expression" e))) *)
(*   end. *)

Ltac2 Notation "imp_arith" "with" s(constr) "reading" r(constr) := imp_arith_tac (Some s) (Some r).
Ltac2 Notation "imp_arith" "reading" r(constr) := imp_arith_tac None (Some r).
Ltac2 Notation "imp_arith" "with" s(constr) := imp_arith_tac (Some s) None.
Ltac2 Notation "imp_arith" := imp_arith_tac None None.
Tactic Notation "imp_arith" "with" constr(s) "reading" constr(r) :=
  let tac := ltac2:(s r |- imp_arith_tac (Ltac1.to_constr s) (Ltac1.to_constr r)) in
  tac s r.
Tactic Notation "imp_arith" "reading" constr(r) :=
  let tac := ltac2:(r |- imp_arith_tac None (Ltac1.to_constr r)) in
  tac r.
Tactic Notation "imp_arith" "with" constr(s) :=
  let tac := ltac2:(s |- imp_arith_tac (Ltac1.to_constr s) None) in
  tac s.
Tactic Notation "imp_arith" := ltac2:(imp_arith).

Ltac2 rec length_type_nel (τ : constr) :=
  match! eval hnf in $τ with
  | type_nel.Tbase _ => 1
  | type_nel.Tcons _ ?τ => Int.add 1 (length_type_nel τ)
  | _ =>
      Control.throw
        (Tactic_failure (Some (fprintf "Failed to count number of types in %t" τ)))
  end.

Ltac2 imp_app_tac (types : constr) (sel : constr option) :=
  let specialized_eapp := open_constr:(imp_EApp $types) in
  let num_arg_goals := length_type_nel types in
  match sel with
  | Some sel => iApply ($specialized_eapp with $sel)
  | None => iApply $specialized_eapp
  end;
  let arg_tacs :=
    List.init num_arg_goals (fun _ => (fun _ => try (imp_step0 None)))
  in
  let conseq_tac () :=
    (unfold tapp, tbind; simple_intros ())
  in
  Control.dispatch (imp_path_tac :: (List.append arg_tacs [conseq_tac])).

Ltac2 Notation "imp_app" types(constr) := imp_app_tac types None.
Ltac2 Notation "imp_app" types(constr) "with" sel(constr) :=
  imp_app_tac types (Some sel).
Tactic Notation "imp_app" constr(types) :=
  let tac := ltac2:(types |- imp_app_tac (Option.get (Ltac1.to_constr types)) None) in
  tac types.
Tactic Notation "imp_app" constr(types) "with" constr(sel) :=
  let tac := ltac2:(types sel |-
                      imp_app_tac
                        (Option.get (Ltac1.to_constr types))
                        (Ltac1.to_constr sel)) in
  tac types sel.

Ltac2 imp_for_tac (invariant : constr) (i : constr) (j : constr) (selpat : constr option) :=
  let specialized_for := '(imp_EFor $invariant $i $j) in
  (match selpat with
  | None => iApply $specialized_for
  | Some s => iApply ($specialized_for with $s)
  end) >
    [ representable () | representable () | try (imp_step0 None) | try (imp_step0 None) | | iIntros "!>" ].

Tactic Notation "imp_for" constr(i) "to" constr(j) "$!" constr(invariant) "with" constr(sel) :=
  let tac := ltac2:(inv i j sel |-
                      imp_for_tac
                        (Option.get (Ltac1.to_constr inv))
                        (Option.get (Ltac1.to_constr i))
                        (Option.get (Ltac1.to_constr j))
                        (Ltac1.to_constr sel)) in
  tac invariant i j sel.
Tactic Notation "imp_for" constr(i) "to" constr(j) "$!" constr(invariant) :=
  let tac := ltac2:(inv i j |-
                      imp_for_tac
                        (Option.get (Ltac1.to_constr inv))
                        (Option.get (Ltac1.to_constr i))
                        (Option.get (Ltac1.to_constr j))
                        None) in
  tac invariant i j.

Ltac2 imp_if_tac (selpat : constr option) :=
  let specialized_if :=
    let e := get_expr () in
    lazy_match! eval hnf in $e with
    | EIfThen _ _ => 'imp_EIfThen2
    | EIfThenElse _ _ _ => 'imp_EIfThenElse2
    end
  in
  (match selpat with
  | None => iApply $specialized_if
  | Some s => iApply ($specialized_if with $s)
  end) >
    [ try (imp_step0 None) | iSplit; try (iIntros "%") ].

Tactic Notation "imp_if" "with" constr(sel) :=
  let tac := ltac2:(sel |- imp_if_tac (Ltac1.to_constr sel)) in
  tac sel.
Tactic Notation "imp_if" := ltac2:(imp_if_tac None).

Ltac2 imp_constant_tac (bopt : constr option) (sel : constr option) :=
  let lem := specialized_imp_EConstant (is_Some sel) bopt in
  match sel with
  | None => iApply $lem
  | Some s => iApply ($lem with $s)
  end.

Tactic Notation "imp_constant" constr(b) "with" constr(sel) :=
  let tac := ltac2:(b sel |- imp_constant_tac (Ltac1.to_constr b) (Ltac1.to_constr sel)) in
  tac b sel.
Tactic Notation "imp_constant" "with" constr(sel) :=
  let tac := ltac2:(sel |- imp_constant_tac None (Ltac1.to_constr sel)) in
  tac sel.
Tactic Notation "imp_constant" constr(b) :=
  let tac := ltac2:(b |- imp_constant_tac (Ltac1.to_constr b) None) in
  tac b.
Tactic Notation "imp_constant" := ltac2:(imp_constant_tac None None).

Ltac2 imp_let_tac (phi1 : constr option) (phi2 : constr option) (enc2 : constr option) :=
  let e := get_expr () in
  let mk_b () :=
    mk_evar @imp_let_B 'Type;
    let b := Control.hyp @imp_let_B in
    let tyb := constr:(Encode $b) in
    ltac1:(t |- evar (imp_let_HB : t)) (Ltac1.of_constr tyb);
    b
  in
  let mk_c () :=
    mk_evar @imp_let_C 'Type;
    let c := Control.hyp @imp_let_C in
    let tyc := constr:(Encode $c) in
    ltac1:(t |- evar (imp_let_HC : t)) (Ltac1.of_constr tyc);
    c
  in
  lazy_match! eval hnf in $e with
  | ELet [Binding (PVar _) _] _ =>
      let lem :=
        match phi1 with
        | None => let b := mk_b () in open_constr:(imp_ELet_var (B:=$b))
        | Some p1 => open_constr:(imp_ELet_var $p1)
        end
      in iApply $lem
  | ELet [Binding (PVar _) _; Binding (PVar _) _] _ =>
      let lem :=
        match phi1, phi2 with
        | None, None =>
            let b := mk_b () in
            let c := mk_c () in
            open_constr:(imp_ELet_var2 (B:=$b) (C:=$c))
        | Some p1, Some p2 =>
            match enc2 with
            | None => open_constr:(imp_ELet_var2 $p1 $p2)
            | Some h2 => open_constr:(imp_ELet_var2 (HC:=$h2) $p1 $p2)
            end
        | Some _, None =>
            Control.zero (Tactic_failure
              (Some (Message.of_string
                "[imp_let] for two bindings, give both postconditions or neither")))
        | None, Some _ =>
            Control.zero (Tactic_failure
              (Some (Message.of_string
                "[imp_let] for two bindings, give both postconditions or neither")))
        end
      in iApply $lem
  | ELet _ _ =>
      Control.zero (Tactic_failure
        (Some (Message.of_string "[imp_let] only supports 1 or 2 [PVar] bindings")))
  | _ =>
      Control.zero (Tactic_failure
        (Some (fprintf "[imp_let] Expected ELet expression, got %t" e)))
  end.

Ltac2 Notation "imp_let" := imp_let_tac None None None.
Ltac2 Notation "imp_let" "$!" phi1(constr) := imp_let_tac (Some phi1) None None.
Ltac2 Notation "imp_let" "$!" phi1(constr) "$!" phi2(constr) :=
  imp_let_tac (Some phi1) (Some phi2) None.
Ltac2 Notation "imp_let" "$!" phi1(constr) "$!" phi2(constr) "enc2" henc2(constr) :=
  imp_let_tac (Some phi1) (Some phi2) (Some henc2).
Tactic Notation "imp_let" := ltac2:(imp_let_tac None None None).
Tactic Notation "imp_let" "$!" constr(phi1) :=
  let tac := ltac2:(phi1 |- imp_let_tac (Ltac1.to_constr phi1) None None) in
  tac phi1.
Tactic Notation "imp_let" "$!" constr(phi1) "$!" constr(phi2) :=
  let tac := ltac2:(phi1 phi2 |-
                      imp_let_tac (Ltac1.to_constr phi1) (Ltac1.to_constr phi2) None) in
  tac phi1 phi2.
Tactic Notation "imp_let" "$!" constr(phi1) "$!" constr(phi2) "enc2" constr(henc2) :=
  let tac := ltac2:(phi1 phi2 henc2 |-
                      imp_let_tac (Ltac1.to_constr phi1) (Ltac1.to_constr phi2)
                        (Ltac1.to_constr henc2)) in
  tac phi1 phi2 henc2.

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
              (EApp (EPath ["add"])
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
  Definition a_spec a : iProp Σ := □ ⌜a > 2⌝.

  Definition module3_spec η := context [var_spec "sub" sub_spec] {["sub"]} η.
  Definition module2_spec η := context [var_spec "Module3" module3_spec] {["Module3"; "some"; "other"; "stuff"]} η.

  Lemma example_proof δ η add :
    in_env "z" (λ (i : Z), ⌜i > 0⌝) η -∗
    add_spec add -∗
    in_env "a" a_spec η -∗
    context [var_spec
               "Module1"
               (context [var_spec "some_other_val" (λ (_ : val), True);
                         var_spec "add" add_spec] {["some_other_val";"add"]})
      ] {["Module1"]} δ -∗
    context [var_spec "Module2" module2_spec] {["Module2";"z"]} η -∗
    EWP (eval (("add",add)::δ ++ η) e) {{ (i : Z), ⌜i > 0⌝ }}.
  Proof.
    iIntros "#zspec #add_spec #aspec #δspec #ηspec".
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
    imp_app τ[Z;Z].
    { imp_app τ[Z;Z].
      iIntros "Hm".
      by iApply "Hm". }
    iIntros "-> #%Ha Hm".
    iSpecialize ("Hm" with "[//]").
    iApply (imp_wand with "Hm").
    iIntros (y ->). iPureIntro.
    lia.
  Qed.

End TacticTests.
