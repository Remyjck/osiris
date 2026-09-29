From stdpp Require Import gmap.
From osiris.utils Require Import base.
From osiris.lang Require Import syntax locations notations thread_ids.
From osiris.semantics Require Import code step strategy eval.
From osiris.stdlib Require Import Stdlib.

(** Final micro states. They correspond to [micro] constructs that cannot
perform a [step] reduction. *)

Inductive final A E :=
  | FRet (a : A)
  | FThrow (e : E)
  | FCrash
  | FPerform (e : eff) (k : outcome2 val exn → micro A E)
  | FConcurrent
  (* A prophecy resolution on a call that cannot reach a result in one step.
     [step] has no rule for one either; see [eval.v], which only ever builds a
     resolution on [CLoad], [CExchange], [CCAS], [CFAA] and [CReturn]. *)
  | FStuck
.

Arguments FRet {A E}.
Arguments FThrow {A E}.
Arguments FCrash {A E}.
Arguments FPerform {A E}.
Arguments FConcurrent {A E}.
Arguments FStuck {A E}.

Inductive step_result A E :=
  | Final (f : final A E)
  | Step (l : list (config A E)).

Arguments Final {A E}.
Arguments Step {A E}.

(* Above is not in the functor as it should not depend on the strategy *)

Module RunF (Strat : Strategy).
Module M := EvalF Strat. Import M.

(** Perform one step of confluent parallel reductions or returns [None] if there
is no trivially confluent step. It can eliminate a large part of the
nondeterminism introduced by [Par] constructs *)

Fixpoint confluent_step {A E} (σ : heap) (m : micro A E) : option (config A E) :=
  match m with
  (* Final micros do not step *)
  | Ret _ | Throw _ | Crash => None
  (* Most side effects are not confluent *)
  | Stop (CFlip | CLoad | CLoadBlock | CSetBlockTag | CExchange | CCAS | CFAA | CPerf | CResume | CWrap | CFork | CJoin) _ _ => None
  (* [CEval], [CLoop], [CAlloc], [Handle] have only one way to reduce *)
  | Stop CEval (η, e) k => Some (σ, try2 (pre_eval η e) k)
  | Stop CLoop (η, x, i1, i2, e) k => Some (σ, try2 (loop η x i1 i2 e) k)
  | Stop CAlloc v k => Some (let l := fresh (dom σ) in (<[l:=Val v]>σ, continue k l))
  | Stop CAllocBlock (t, ls) k => Some (let l := fresh (A:=loc) (dom σ) in
                                   (insert l (Block t ls) σ, continue k l))
  (* [CReturn w] returns [w] and does nothing else. [CNewProph] has no step
     in the semantics: a prophecy has no runtime meaning, so the interpreter
     hands out an arbitrary identifier. *)
  | Stop CReturn w k => Some (σ, continue k w)
  | Stop CNewProph _ k => Some (σ, continue k (Loc 0))
  (* A resolution takes the step of the call it wraps and drops the ghost pair
     [(p, v)], so it is confluent exactly when that call is. *)
  | Stop (CResolve CReturn) (w, _, _) k => Some (σ, continue k w)
  | Stop (CResolve _) _ _ => None
  | Handle (Ret v) h => Some (σ, h (O3Ret v))
  | Handle (Throw e) h => Some (σ, h (O3Throw e))
  | Handle Crash h => Some (σ, Crash)
  | Handle m h => option_map (λ '(σ', m'), (σ', Handle m' h)) (confluent_step σ m)
  (* Some [Par] configurations also have only one possible [step] *)
  | Par (Ret v1) (Ret v2) k => Some (σ, continue k (v1, v2))
  | Par (Crash) (Ret _) _ | Par (Ret _) (Crash) _ => Some (σ, Crash)
  | Par (Throw e) (Ret _) k | Par (Ret _) (Throw e) k => Some (σ, discontinue k e)
  | Par (Stop CPerf e k) (Ret v) h => Some (σ, Stop CPerf e (λ o, Par (k o) (Ret v) h))
  | Par (Ret v) (Stop CPerf e k) h => Some (σ, Stop CPerf e (λ o, Par (Ret v) (k o) h))
  (* Others are necessarily non-deterministic *)
  | Par (Throw _ | Crash | Stop CPerf _ _)
        (Throw _ | Crash | Stop CPerf _ _) _ => None
  (* Other [Par] configurations can step in confluent ways if subterms can *)
  | Par m1 m2 k =>
      match confluent_step σ m1 with
      | None =>
          match confluent_step σ m2 with
          | None => None
          | Some (σ', m2') => Some (σ', Par m1 m2' k)
          end
      | Some (σ', m1') =>
          (* even if [m1] reduced, it can be useful to reduce [m2] in particular
          if [m1] is a long computation and [m2] is short *)
          match confluent_step σ m2 with
          | None => Some (σ', Par m1' m2 k)
          | Some (σ'', m2') => Some (σ'', Par m1' m2' k)
          end
      end
  end.


(* A step function returns [Step l] where [l] is a list of the possible
configurations that can be reached in one step (and optionally several
deterministic steps), or [Final] if the argument was in fact stuck. *)


(** Returns the list [l] of configurations to which [(σ, m)] can step to, as
  [Step l] if it can indeed step. Otherwise if [m] is final, returns [Final f]
  where [f] corresponds to [m]. The latter is used instead of simply returning
  e.g. [None] to make the image of [Par m1 m2 _] depend only of the images of
  [m1] and [m2] instead of depending of [m1] and [m2] themselves. *)

Fixpoint stepto {A E} (σ : heap) (m : micro A E) {struct m} : step_result A E :=
  match m with
  (* Already final *)
  | Ret x => Final (FRet x)
  | Throw x => Final (FThrow x)
  | Crash => Final (FCrash)
  | Stop CPerf e k => Final (FPerform e k)
  | Stop CFork m k => Final FConcurrent
  | Stop CJoin ι' k => Final FConcurrent

  (* Handlers do not introduce nondeterminism *)
  | Handle m1 h =>
      match stepto σ m1 with
      | Final (FPerform e k) => let l := fresh (dom σ) in Step [(<[l:=Kont k]> σ, h (O3Perform e l))]
      | Final (FRet v)   => Step [(σ, h (O3Ret v))]
      | Final (FThrow e) => Step [(σ, h (O3Throw e))]
      | Final (FCrash) => Step [(σ, Crash)]
      | Final FConcurrent => Step [(σ, Crash)]
      (* A resolution floats out of a handler ([StepHandleResolve]), so a stuck
         one is stuck under [Handle] too. *)
      | Final FStuck => Final FStuck
      | Step l => Step (map (λ '(σ', m'), (σ', Handle m' h)) l)
      end

  (* Some [Stop] cases are confluent and covered in the same way as in [confluent_step] *)
  | Stop CEval (η, e) k => Step [(σ, try2 (pre_eval η e) k)]
  | Stop CLoop (η, x, i1, i2, e) k => Step [(σ, try2 (loop η x i1 i2 e) k)]
  | Stop CAlloc v k => let l := fresh (dom σ) in
                       Step [(<[l:=Val v]>σ, continue k l)]
  | Stop CAllocBlock (t, ls) k => let l := fresh (A:=loc) (dom σ) in
                             Step [(insert l (Block t ls) σ, continue k l)]
  | Stop CSetBlockTag (t, l) k =>
      Step [step_set_tag σ t l k]

  (* [Stop] cases involving the store or flips typically break confluence *)
  | Stop CLoad l k => Step [step_load σ l k]
  | Stop CLoadBlock l k => Step [step_load_block σ l k]
  | Stop CExchange (l, v') k => Step [step_exchange σ l v' k]
  | Stop CCAS (l, seen, v') k => Step [step_cas σ l seen v' k]
  | Stop CFAA (l, i) k => Step [step_faa σ l i k]
  | Stop CResume (l, o) k => Step [step_resume σ l o k]
  | Stop CWrap (true, l, η, bs) k => Step [step_wrap σ l η bs (fresh (dom σ)) k]
  | Stop CWrap (false, l, η, bs) k => Step [step_shallow_wrap σ l η bs (fresh (dom σ)) k]
  | Stop CFlip x k => Step [(σ, continue k false); (σ, continue k true)]

  (* [CReturn] and [CNewProph] are confluent; see [confluent_step]. *)
  | Stop CReturn w k => Step [(σ, continue k w)]
  | Stop CNewProph _ k => Step [(σ, continue k (Loc 0))]

  (* A resolution performs the call it wraps in a single step, dropping the
     ghost pair [(p, v)]: the resolution leaves no trace in the store, so each
     case below is the case of the wrapped call, applied to the same [k]. *)
  | Stop (CResolve CReturn) (w, _, _) k => Step [(σ, continue k w)]
  | Stop (CResolve CLoad) (l, _, _) k => Step [step_load σ l k]
  | Stop (CResolve CExchange) ((l, v'), _, _) k => Step [step_exchange σ l v' k]
  | Stop (CResolve CCAS) ((l, seen, v'), _, _) k => Step [step_cas σ l seen v' k]
  | Stop (CResolve CFAA) ((l, i), _, _) k => Step [step_faa σ l i k]
  | Stop (CResolve _) _ _ => Final FStuck

  (* [Par] of two [Ret]s is also confluent and results in one possible configuration *)
  | Par (Ret v1) (Ret v2) k => Step [(σ, continue k (v1, v2))]

  (* In other [Par] cases, assuming [confluent_step] has been used to resolve
     non-determinism, we need to reduce either [m1] first or [m2] first *)
  | Par m1 m2 k =>
      (* Outcomes of [m1] starting first *)
      let m1_first :=
        match stepto σ m1 with
        | Final f =>
            match f with
            (* If [m1] is a [Ret], then it can be delayed until [m2] is
               resolved, so it does not participate in [m1_first] *)
            | FRet _ => []
            (* In all other cases, control can go to [m1], disregarding [m2] or
               delaying it into a perform's continuation *)
            | FThrow e1 => [(σ, discontinue k e1)]
            | FCrash => [(σ, Crash)]
            | FConcurrent => [(σ, Crash)]
            | FPerform e1 k1 => [(σ, Stop CPerf e1 (λ o, Par (k1 o) m2 k))]
            (* A stuck [m1] contributes no transition; [m2] may still step *)
            | FStuck => []
            end
        (* [m1] taking a step *)
        | Step l => map (λ '(σ1', m1'), (σ1', Par m1' m2 k)) l
        end
      in
      (* Symmetrically for [m2] acting first *)
      let m2_first :=
        match stepto σ m2 with
        | Final f =>
            match f with
            | FRet _ => []
            | FThrow e2 => [(σ, discontinue k e2)]
            | FCrash => [(σ, Crash)]
            | FPerform e2 k2 => [(σ, Stop CPerf e2 (λ o, Par m1 (k2 o) k))]
            | FConcurrent => [(σ, Crash)]
            | FStuck => []
            end
        | Step l => map (λ '(σ2', m2'), (σ2', Par m1 m2' k)) l
        end
      in
      (* Returning all possibilities *)
      Step (m1_first ++ m2_first)
end.

(* Combine the two step functions -- iteration and coalescing may be best
   handled on the OCaml side *)

(* First try to resolve nondeterminism with [confluent_step]. If one is found,
   it is considered the same as a 'non-confluent' step to exactly one
   configuration. Otherwise, run non-confluent stepping. *)

Definition step {A E} (cfg : config A E) :=
  let (σ, m) := cfg in
  match confluent_step σ m with
  | Some cfg' => Step [cfg']
  | None => stepto σ m
  end.

(* We could resolve more nondeterminism coming from a tree of [Par]'s in some
cases.

- If there are some [Stop CAlloc]'s (and some [Stop CInstall]'s) then it should
  be fine to perform them first, since they commute with everything up to memory
  permutation. One may treat an allocation as a pure step, which may reveal some
  more effects later.

- If there is a [Stop CPerf] somewhere, then anything could happen: stores
  might be cancelled by discontinuing the continuation, reads can happen before
  or after the handler handles, so we can spare no interleaving.

- If there are only loads, one could think that they can be sequentialized, but
  this is not true: a load comes with a continuation that might invalidate the
  reads sequentialized before it, e.g. in [let r = ref 0 in (!r, r := !r + 1))]
  the two [!r] loads would be the only Stops in a Par tree but the
  sequentialization would yield [(0, ())] as the list of possible results,
  whereas [(1, ())] is also possible.

It is tempting to think in terms of trivial continuations because they are so
common, for example in [let x = !r + !r in _], but from the point of view of
elements of micro, those are indistinguishable from complex ones, e.g. the
result of [eval] on [((r := 1 + !r), (r := 2 * !r))] would just be a Par of two
loads on r and s.

One approach could be to reify bind into a micro construct [Bind] and to
disallow continuations in some Stop constructs, or mark some continuations as
pure (or read-only). Then we could treat a tree of Stops knowing e.g. that all
of the reads' continuations won't touch the store before the first argument of
the bind reaches a final state. *)

End RunF.

(* Environment allowing [open Effect], [open Effect.Deep] etc. *)
Definition effect_stdlib_env : env :=
  [("Effect",
     (VStruct [("Deep", VStruct []); ("Shallow", VStruct [])]))
  ] ++ stdlib_env.


(** Implementing a few I/O primitives by piggy-backing user-defined effects *)
(* This is a hack, the proper way should be to do external interactions in the
micro monad, so that we are able to reason about it in proofs. *)

Definition io_loc := 0%Z.

(* Closure with one argument [arg] performing the effect stored at [io_loc] with
   the pair of arguments [(name, arg)] *)
Definition clo_io_perform (name : string) : val :=
  (* closure with environment mapping [E] to [io_loc] *)
  VClo [("E", VFieldLoc (Loc io_loc))] $
    (* [λ x, perform (E (name, x))] *)
    AnonFun "x" (EPerform (EXData ["E"] [EString name; EPath ["x"]])).

(* Store with I/O effect allocated *)
Definition io_store : heap := {[ Loc io_loc := Val VUnit ]}.

(* Environment with some I/O primitives *)
Definition io_env : env :=
  [("print_int",     clo_io_perform "print_int");
   ("print_string",  clo_io_perform "print_string");
   ("print_endline", clo_io_perform "print_endline");
   ("print_newline", clo_io_perform "print_newline");
   ("read_int",      clo_io_perform "read_int");
   ("read_line",     clo_io_perform "read_line")].


(** Printers may be easier to define in Rocq than in OCaml *)

From Stdlib Require Import Numbers.DecimalString.

Definition string_of_Z (z : Z) : string := NilZero.string_of_int (Z.to_int z).

Definition string_of_char (c : char) : string := String c EmptyString.

Definition string_of_field (f : Z) : string := NilZero.string_of_int (Z.to_int f).

Definition string_of_pair {A B} (pa : A → string) (pb : B → string) : A * B → string :=
  λ '(a, b), ("(" ++ pa a ++ ", " ++ pb b ++ ")")%string.

Fixpoint string_of_pat (p : pat) : string :=
  match p with
  | PUnsupported => "PUnsupported"
  | PAny => "PAny"
  | PVar var => "PVar(" ++ var ++ ")"
  | PAlias pat var => "PAlias(" ++ string_of_pat pat ++ ", " ++ var ++ ")"
  | POr pat1 pat2 => "POr(" ++ string_of_pat pat1 ++ ", " ++ string_of_pat pat2 ++ ")"
  | PTuple list_pat => "PTuple(" ++ String.concat "," (map string_of_pat list_pat) ++ ")"
  | PData data list_pat => "PData(" ++ data ++ ", " ++ String.concat "," (map string_of_pat list_pat) ++ ")"
  | PXData path list_pat => "PXData(" ++ String.concat "." path ++ ", " ++ String.concat "," (map string_of_pat list_pat) ++ ")"
  | PRecord fs => "PRecord(" ++ String.concat "," (map (string_of_pair string_of_field string_of_pat) fs) ++ ")"
  | PTaggedRecord data pat => "PTaggedRecord(" ++ data ++ ", " ++ string_of_pat pat ++ ")"
  | PArray list_pat => "PArray(" ++ String.concat "," (map string_of_pat list_pat) ++ ")"
  | PInt Z => "PInt(" ++ string_of_Z Z ++ ")"
  | PChar char => "PChar(" ++ string_of_char char ++ ")"
  | PString string => "PString(" ++ string ++ ")"
  end.

Fixpoint string_of_cpat (cp : cpat) : string :=
  match cp with
  | CVal p => "CVal(" ++ string_of_pat p ++ ")"
  | CExc p => "CExc(" ++ string_of_pat p ++ ")"
  | CEff p k => "CExc(" ++ string_of_pat p ++ ", " ++ string_of_pat k ++ ")"
  | COr cpat1 cpat2 => "CPOr(" ++ string_of_cpat cpat1 ++ ", " ++ string_of_cpat cpat2 ++ ")"
  end.

Fixpoint string_of_coercion (c : coercion) : string :=
  match c with
  | CIdentity => "CIdentity"
  | CStruct l => "CStruct(" ++ String.concat "," (map (string_of_pair id string_of_coercion) l) ++ ")"
  end.

Definition string_of_mut_tag (t : mut_tag) :=
  match t with
  | Mut => "Mut"
  | Immut => "Immut"
  end.

Definition string_of_proph_arg (a : proph_arg) : string :=
  match a with
  | PArgPath π => "PArgPath(" ++ String.concat "." π ++ ")"
  | PArgData c => "PArgData(" ++ c ++ ")"
  | PArgInt i => "PArgInt(" ++ string_of_Z i ++ ")"
  end.

Fixpoint string_of_expr (e : expr) : string :=
  match e with
  | EUnsupported => "EUnsupported"
  | EPath path => "EPath(" ++ String.concat "." path ++  ")"
  | EAnonFun anonfun => "EAnonFun(" ++ string_of_anonfun anonfun ++ ")"
  | EApp e1 e2 => "EApp(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | ETuple list_expr => "ETuple(" ++ String.concat "," (map string_of_expr list_expr) ++ ")"
  | EData data es => "EData(" ++ data ++ ", [" ++  String.concat "; " (map string_of_expr es) ++ "])"
  | EXData path es => "EXData([" ++ String.concat "." path ++ "], [" ++  String.concat "; " (map string_of_expr es) ++ "])"
  | ERecord t fes => "ERecord(" ++ string_of_mut_tag t ++ ", [" ++ String.concat "; " (map string_of_expr fes) ++ "]" ++ ")"
  | ERecordUpdate expr fes => "ERecordUpdate(" ++ string_of_expr expr ++ ", " ++ String.concat "; " (map string_of_fexpr fes) ++ ")"
  | ERecordAccess expr field => "ERecordAccess(" ++ string_of_expr expr ++ ", " ++ string_of_field field ++ ")"
  | ERecordSet e1 f e2 => "ERecordSet(" ++ string_of_expr e1 ++ ", " ++ string_of_field f ++ ", " ++ string_of_expr e2 ++ ")"
  | EAtomicLoc e f => "EAtomicLoc(" ++ string_of_expr e ++ ", " ++ string_of_field f ++ ")"
  | EInline c t es => "EInline(" ++ c ++ ", " ++ string_of_mut_tag t ++ ", [" ++ String.concat "; " (map string_of_expr es) ++ "])"
  | EArrayLit list_expr => "EArrayLit(" ++ String.concat "," (map string_of_expr list_expr) ++ ")"
  | EArrayLength expr => "EArrayLength(" ++ string_of_expr expr ++ ")"
  | EArrayGet e1 e2 => "EArrayGet(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EArraySet e1 e2 e3 => "EArraySet(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ", " ++ string_of_expr e3 ++ ")"
  | EArrayMake e1 e2 => "EArrayMake(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EFreeze e => "EFreeze(" ++ string_of_expr e ++ ")"
  | EUnfreeze e => "EUnfreeze(" ++ string_of_expr e ++ ")"
  | EBoolConj e1 e2 => "EBoolConj(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EBoolDisj e1 e2 => "EBoolDisj(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EBoolNeg e => "EBoolNeg(" ++ string_of_expr e ++ ")"
  | EInt Z => "EInt(" ++ string_of_Z Z ++ ")"
  | EMaxInt => "EMaxInt"
  | EMinInt => "EMinInt"
  | EIntNeg e => "EIntNeg(" ++ string_of_expr e ++ ")"
  | EIntAdd e1 e2 => "EIntAdd(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EIntSub e1 e2 => "EIntSub(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EIntMul e1 e2 => "EIntMul(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EIntDiv e1 e2 => "EIntDiv(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EIntMod e1 e2 => "EIntMod(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EIntLand e1 e2 => "EIntLand(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EIntLor e1 e2 => "EIntLor(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EIntLxor e1 e2 => "EIntLxor(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EIntLnot e => "EIntLnot(" ++ string_of_expr e ++ ")"
  | EIntLsl e1 e2 => "EIntLsl(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EIntLsr e1 e2 => "EIntLsr(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EIntAsr e1 e2 => "EIntAsr(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EFloat float => "EFloat(?)"
  | EChar char => "EChar('" ++ string_of_char char ++ "')"
  | EString string => "EString(""" ++ string ++ """)"
  | EOpPhysEq e1 e2 => "EOpPhysEq(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EOpEq e1 e2 => "EOpEq(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EOpNe e1 e2 => "EOpNe(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EOpLt e1 e2 => "EOpLt(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EOpLe e1 e2 => "EOpLe(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EOpGt e1 e2 => "EOpGt(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EOpGe e1 e2 => "EOpGe(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | ELet list_binding e => "ELet([" ++ String.concat "; " (map string_of_binding list_binding) ++ "], " ++ string_of_expr e ++ ")"
  | ELetRec list_rec_binding e => "ELetRec([" ++ String.concat "; " (map string_of_rec_binding list_rec_binding) ++ "], " ++ string_of_expr e ++ ")"
  | ESeq e1 e2 => "ESeq(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EIfThen e1 e2 => "EIfThen(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EIfThenElse e e1 e2 => "EIfThenElse(" ++ string_of_expr e ++ ", " ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EMatch e bs => "EMatch(" ++ string_of_expr e ++ " with " ++ String.concat " | " (map string_of_branch bs) ++ ")"
  | EShallowMatch e bs => "EShallowMatch(" ++ string_of_expr e ++ " with " ++ String.concat " | " (map string_of_branch bs) ++ ")"
  | ERaise e => "ERaise(" ++ string_of_expr e ++ ")"
  | EPerform e => "EPerform(" ++ string_of_expr e ++ ")"
  | EContinue e1 e2 => "EContinue(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EDiscontinue e1 e2 => "EDiscontinue(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EWhile e1 e2 => "EWhile(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EFor var e1 e2 e => "EFor(" ++ var ++ ", " ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ", " ++ string_of_expr e ++ ")"
  | EAssertFalse => "EAssertFalse"
  | EAssert e => "EAssert(" ++ string_of_expr e ++ ")"
  | ELetSitem s e => "ELetSitem(" ++ string_of_sitem s ++ ", " ++ string_of_expr e ++ ")"
  | ERef e => "ERef(" ++ string_of_expr e ++ ")"
  | ELoad e => "ELoad(" ++ string_of_expr e ++ ")"
  | EStore e1 e2 => "EStore(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EFieldLoad e => "EFieldLoad(" ++ string_of_expr e ++ ")"
  | EExchange e1 e2 => "EExchange(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | ECAS e1 e2 e3 => "ECAS(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ", " ++ string_of_expr e3 ++ ")"
  | EFAA e1 e2 => "EFAA(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | ENewProph => "ENewProph"
  | EResolve e π a => "EResolve(" ++ string_of_expr e ++ ", " ++ String.concat "." π ++ ", " ++ string_of_proph_arg a ++ ")"
  | EIgnore e => "EIgnore(" ++ string_of_expr e ++ ")"
  | EFork e1 e2 => "EFork(" ++ string_of_expr e1 ++ ", " ++ string_of_expr e2 ++ ")"
  | EJoin e => "EFork(" ++ string_of_expr e ++ ")"
  end
  with string_of_fexpr (x : fexpr) : string :=
  match x with
  | Fexpr field e => string_of_field field ++ "=" ++ string_of_expr e
  end
  with string_of_branch (x : branch) : string :=
  match x with
  | Branch cpat e => "Branch(" ++ string_of_cpat cpat ++ ", " ++ string_of_expr e ++ ")"
  end
  with string_of_binding (x : binding) : string :=
  match x with
  | Binding pat e => "Binding(" ++ string_of_pat pat ++ ", " ++ string_of_expr e ++ ")"
  end
  with string_of_rec_binding (x : rec_binding) : string :=
  match x with
  | RecBinding var anonfun => "RecBinding(" ++ var ++ "," ++ string_of_anonfun anonfun ++ ")"
  end
  with string_of_anonfun (x : anonfun) : string :=
  match x with
  | AnonFun var e => "AnonFun(" ++ var ++ ", " ++ string_of_expr e ++ ")"
  end
  with string_of_mexpr (x : mexpr) : string :=
  match x with
  | MUnsupported => "MUnsupported"
  | MPath path => "MPath(" ++ String.concat "." path ++  ")"
  | MStruct list_sitem => "MStruct(" ++ String.concat "; " (map string_of_sitem list_sitem) ++ ")"
  | MFunctor var list_sitem => "MFunctor(" ++ var ++ ", " ++ String.concat "; " (map string_of_sitem list_sitem) ++ ")"
  | MCoercion mexpr coercion => "MCoercion(" ++ string_of_mexpr mexpr ++ ", " ++ string_of_coercion coercion ++ ")"
  end
  with string_of_sitem (x : sitem) : string :=
  match x with
  | ILet list_binding => "ILet(" ++ String.concat "; " (map string_of_binding list_binding) ++ ")"
  | ILetRec list_rec_binding => "ILetRec(" ++ String.concat "; " (map string_of_rec_binding list_rec_binding) ++ ")"
  | IModule module mexpr => "IModule(" ++ module ++ ", " ++ string_of_mexpr mexpr ++ ")"
  | IOpen mexpr => "IOpen(" ++ string_of_mexpr mexpr ++ ")"
  | IInclude mexpr => "IInclude(" ++ string_of_mexpr mexpr ++ ")"
  | IExternal var expr => "IExternal(" ++ var ++ ", " ++ string_of_expr expr ++ ")"
  | IExtend list_name => "IExtend(" ++ String.concat ", " list_name ++ " )"
  end.

Definition string_of_int (i : int.int) : string := string_of_Z (int.M.intval i).

Definition string_of_tag (t : mut_tag) : string :=
  match t with
  | Mut => "Mut"
  | Immut => "Immut"
  end.

Fixpoint string_of_val (v : val) : string :=
  match v with
  | VClo env anonfun => "<clo>"
  | VCloRec env bindings f => "<clorec(" ++ f ++ ")>"
  | VString s => """" ++ s ++ """"
  | VInt i => "VInt(" ++ string_of_int i ++ ")"
  | VFloat f => "VFloat(?)"
  | VTuple l => "VTuple(" ++ String.concat "; " (map string_of_val l) ++ ")"
  | VData data vs => "VData(" ++ data ++ ", [" ++ String.concat "; " (map string_of_val vs) ++ "])"
  | VXData loc vs => "VXData(" ++ string_of_Z loc.(address) ++ ", [" ++ String.concat "; " (map string_of_val vs) ++ "])"
  | VFieldLoc l   => "VFieldLoc("   ++ string_of_Z l.(address) ++ ")"
  | VProph p => "VProph(" ++ string_of_Z p.(address) ++ ")"
  | VCont l  => "VCont("  ++ string_of_Z l.(address) ++ ")"
  | VThread thread => "VFieldLoc(" ++ string_of_Z thread.(tid) ++ ")"
  | VRecord l => "VRecord(" ++ string_of_Z l.(address) ++ ")"
  | VArray l => "VArray(" ++ string_of_Z l.(address) ++ ")"
  | VTaggedRecord c l => "VTaggedRecord(" ++ c ++ ", " ++ string_of_Z l.(address) ++ ")"
  | VStruct fields => "VStruct(" ++ String.concat "; " (map (string_of_pair id string_of_val) fields) ++ ")"
  | VFunctor fields v l  => "VFunctor(Unsupported)"
  | VChar c => "VChar(" ++ string_of_char c ++ ")"
  end.

Definition string_of_outcome2 (o : outcome2 val exn) : string :=
  match o with
  | O2Ret v => string_of_val v
  | O2Throw e => string_of_val e
  end.

Definition abstr_printer {A} : A → string := λ _, "<abstr>".

Fixpoint string_of_code {X Y Z} (c : code X Y Z) : string :=
  match c with
  | CEval => "CEval"
  | CLoop => "CLoop"
  | CFlip => "CFlip"
  | CAlloc => "CAlloc"
  | CAllocBlock => "CAllocBlock"
  | CLoad => "CLoad"
  | CLoadBlock => "CLoadBlock"
  | CExchange => "CExchange"
  | CSetBlockTag => "CSetBlockTag"
  | CCAS => "CCAS"
  | CFAA => "CFAA"
  | CPerf => "CPerf"
  | CResume => "CResume"
  | CWrap => "CWrap"
  | CFork => "CFork"
  | CJoin => "CJoin"
  | CNewProph => "CNewProph"
  | CReturn => "CReturn"
  | CResolve c => "CResolve(" ++ string_of_code c ++ ")"
  end.

Definition string_of_bool (b : bool) : string :=
  match b with
  | true => "true"
  | false => "false"
  end.

Definition string_of_env (e : env) : string :=
  "ENV(" ++ String.concat ", " (map (λ '(x, v), x ++ "=" ++ string_of_val v)%string e)  ++ ")".

Fixpoint string_of_micro {A E} (ppa : A → string) (ppe : E → string) (m : micro A E) : string :=
  match m with
  | Ret a => "Ret(" ++ ppa a ++ ")"
  | Throw e => "Throw(" ++ ppe e ++ ")"
  | Crash => "Crash"
  | Stop CEval (η, e) k => "Stop(CEval, " ++ string_of_env η ++ ", " ++ string_of_expr e ++ "), <cont>)"
  | Stop CLoop (η, x, a, b, e) k => "Stop(CLoop, (<env>, " ++ x ++ ", " ++ string_of_int a ++ ", " ++ string_of_int b ++ ", " ++ string_of_expr e ++ "), <cont>)"
  | Stop CFlip () k => "Stop(CFlip" ++ ", (), <cont>)"
  | Stop CAlloc v k => "Stop(CAlloc" ++ ", " ++ string_of_val v ++ ", <cont>)"
  | Stop CAllocBlock (t, ls) k =>
      "Stop(CAllocBlock" ++ ", " ++ string_of_mut_tag t ++ ", " ++ "[" ++ String.concat ";" (List.map (fun l => string_of_Z l.(address)) ls) ++ "], <cont>)"
  | Stop CLoad loc k => "Stop(CLoad" ++ ", " ++ string_of_Z loc.(address) ++ ", <cont>)"
  | Stop CLoadBlock loc k => "Stop(CLoadBlock" ++ ", " ++ string_of_Z loc.(address) ++ ", <cont>)"
  | Stop CExchange (loc, v) k => "Stop(CExchange" ++ ", " ++ string_of_Z loc.(address) ++ ", " ++ string_of_val v ++ ", <cont>)"
  | Stop CSetBlockTag (l, t) k => "Stop(CSetBlockTag" ++ ", " ++ string_of_Z l.(address) ++ ", " ++ string_of_tag t ++ ", <cont>)"
  | Stop CCAS (loc, seen, v) k => "Stop(CCAS" ++ ", " ++ string_of_Z loc.(address) ++ ", " ++ string_of_val seen ++ ", " ++ string_of_val v ++ ", <cont>)"
  | Stop CFAA (loc, i) k => "Stop(CFAA" ++ ", " ++ string_of_Z loc.(address) ++ ", " ++ string_of_int i ++ ", <cont>)"
  | Stop CPerf v k => "Stop(CPerf" ++ ", " ++ string_of_val v ++ ", <cont>)"
  | Stop CResume (loc, o2) k => "Stop(CResume" ++ ", " ++ string_of_Z loc.(address) ++ ", " ++ string_of_outcome2 o2 ++ ", <cont>)"
  | Stop CWrap (d, loc, η, h) k => "Stop(CWrap" ++ ", " ++ string_of_bool d ++ ", " ++ string_of_Z loc.(address) ++ "<env>, <handler>" ++ ", <cont>)"
  | Stop CFork (v1, v2) k => "Stop(CFork" ++ ", " ++ string_of_val v1 ++ ", " ++ string_of_val v2 ++ ", <cont>)"
  | Stop CJoin ι' k => "Stop(CFork" ++ ", " ++ string_of_Z ι'.(tid) ++ ", <cont>)"
  | Stop CNewProph () k => "Stop(CNewProph" ++ ", (), <cont>)"
  | Stop CReturn w k => "Stop(CReturn" ++ ", " ++ string_of_val w ++ ", <cont>)"
  | Stop (CResolve c) (_, p, v) k =>
      "Stop(CResolve(" ++ string_of_code c ++ "), <arg>, " ++ string_of_Z p.(address) ++ ", " ++ string_of_val v ++ ", <cont>)"
  | Handle m h => "Handle(" ++ string_of_micro string_of_val string_of_val m ++ ", <handler>)"
  | Par m1 m2 k =>
      "Par(" ++
        string_of_micro abstr_printer abstr_printer m1 ++ ", " ++
        string_of_micro abstr_printer abstr_printer m2 ++ ", <cont>)"
  end.

Definition string_of_microvx := string_of_micro string_of_val string_of_val.

Definition string_of_block (b : mem_block) : string :=
  match b with
  | Val v => "Val(" ++ string_of_val v ++ ")"
  | Block t ls => "Block(" ++ string_of_tag t ++ ", " ++ "[" ++ String.concat ";" (map (fun l => string_of_Z l.(address)) ls) ++ "])"
  | Kont _ => "Kont(<cont>)"
  | Shot => "Shot"
  end.

Definition string_of_store (σ : heap) : string :=
  "store(" ++
      String.concat "; "
        (map
           (λ '(loc, block), string_of_Z loc.(address) ++ "↦" ++ string_of_block block)
           (map_to_list σ))%string ++ ")".

Definition string_of_config (c : config val exn) : string :=
  string_of_pair
    string_of_store
    string_of_microvx
    c.

Definition string_of_list_config (l : list (config val exn)) : string :=
  String.concat "; " (map string_of_config l).
