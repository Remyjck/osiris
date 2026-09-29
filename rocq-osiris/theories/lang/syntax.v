From osiris.utils Require Import base.
Require Import float int char locations thread_ids.

(* This file should be in sync with osiris/src/Syntax.ml. *)

Inductive mut_tag : Type := Mut | Immut.

(* ------------------------------------------------------------------------ *)

(* Variables. *)

Definition var :=
  string.

(* Module names. *)

Definition module :=
  string.

(* We place variables and module names in the same namespace. (This creates
   no conflicts because OCaml variables begin with a lowercase letter while
   OCaml module names begin with an uppercase letter.) Thus, variables and
   module names appear together in environments, structures, etc. *)

Definition name :=
  string. (* A variable or module name. *)

(* ------------------------------------------------------------------------ *)

(* Module paths. *)

(* A module path is a possibly-empty list of module names [M], followed with
   a final name, which can be a variable [x] or a module name [M]. *)

Definition path := list name.

(* ------------------------------------------------------------------------ *)

(* Data constructors. *)

Definition data :=
  string.

(* Record fields. *)

Definition field :=
  Z.

(* Data constructors and record fields are not treated like variables and
   module names. They are never considered "bound" and never looked up in
   an environment. They are regarded as constants. *)

(* In OCaml, a data constructor or field can be a qualified name. Here, only
   a short (unqualified) name is retained; the rest is irrelevant. *)

(* ------------------------------------------------------------------------ *)

(* First-class continuations. *)

Definition cont :=
  tc_opaque loc.

(* Pointers to blocks of memory. *)

Definition array :=
  tc_opaque loc.

Definition record :=
  tc_opaque loc.

(* Prophecy identifiers. They live apart from the heap: the program logic
   tracks which ones are in use. *)

Definition proph_id :=
  tc_opaque loc.

(* Without this, the typeclass engine unfolds both [cont] and [block] to the
   same [tc_opaque loc] body, making Encode/Observe instances ambiguous. *)
Global Typeclasses Opaque cont array record proph_id.

(* ------------------------------------------------------------------------ *)

(* Machine integers. *)

Abbreviation int :=
  int.int.

(* Characters. *)

Definition char :=
  Ascii.ascii.

(* ------------------------------------------------------------------------ *)

(* Patterns. *)

(* An ordinary pattern, or value pattern, has type [pat].
   Such a pattern is used in a case analysis on a value. *)

Scheme All for list.
Scheme All for prod.

Inductive pat :=
  (* A placeholder for as-yet-unsupported constructs. *)
  | PUnsupported
  (* The wildcard pattern. *)
  | PAny
  (* A variable. *)
  | PVar (x : var)
  (* An alias pattern [p as x]. *)
  | PAlias (p : pat) (x : var)
  (* A disjunction pattern [p1 | p2]. *)
  | POr (p1 p2 : pat)
  (* A tuple pattern. *)
  | PTuple (ps : list pat)
  (* A data constructor pattern in an ordinary algebraic data type. *)
  | PData (c : data) (ps : list pat)
  (* A data constructor pattern in an extensible algebraic data type.
     In [PXData (π, ps)], the path [π] is expected to denote a memory
     location, which serves as a dynamically-allocated name. *)
  | PXData (π : path) (ps : list pat)
  (* PRecord: a record pattern. *)
  | PRecord (fps : list (field * pat))
  (* An inline-record pattern: [C p] where [C] is an inline-record
     constructor and [p] matches the underlying record. *)
  | PInline (c : data) (p : pat)
  (* PArray: an array pattern. *)
  | PArray (ps : list pat)
  (* A literal integer pattern. *)
  | PInt (i : Z)
  (* A literal character pattern. *)
  | PChar (c: char)
  (* A literal string pattern. *)
  | PString (s : string).

(* Computation patterns. *)

(* A computation pattern [cp] has type [cpat]. Such a pattern is used
   in a case analysis on a three-branch outcome, which represents a
   value, an exception, or an effect. *)

Inductive cpat :=
  (* This pattern matches a normal termination outcome. It guards the
     "return branch" in an effect handler. In OCaml's concrete syntax,
     it corresponds to the absence of an [exception] or [effect]
     keyword in a [match] construct. *)
  | CVal (p : pat)
  (* This pattern matches an exceptional outcome. In OCaml's concrete
     syntax, it corresponds to the presence of the [exception] keyword
     in a [match] branch. *)
  | CExc (p : pat)
  (* This pattern matches an effect. In OCaml's concrete syntax, it
     corresponds to the presence of the [effect] keyword in a [match]
     branch. *)
  | CEff (p : pat) (k : pat)
  (* A disjunction pattern [cp1 | cp2]. *)
  | COr (cp1 : cpat) (cp2 : cpat).

(* ------------------------------------------------------------------------ *)

(* Module coercions. *)

(* Module coercions can be understood as a very impoverished form of module
   types. They play a role in the dynamic semantics of the shape restriction
   operation on modules. *)

Inductive coercion :=
  (* The coercion [CIdentity] has no effect. *)
  | CIdentity

  (* The coercion [CStruct cs] expects to be applied to a structure. The
     fields named in the list [xcs] are retained, and the corresponding
     coercions in the list [xcs] are applied to them. All other fields are
     dropped. *)
| CStruct (xcs : list (var * coercion)).

Definition fcoercion :=
  (var * coercion)%type.

Definition fcoercions :=
  list fcoercion.
      (* A field-coercion list [xcs] must have no duplicate names. *)

(* ------------------------------------------------------------------------ *)

(* The auxiliary argument of a prophecy resolution. *)

(* A resolution [e [@resolve p v]] is a ghost annotation: it must not change
   what the program does. So neither [p] nor [v] is an arbitrary expression.
   [p] is a path to a pre-existing prophecy variable, and [v] is drawn from
   the type [proph_arg]. *)

Inductive proph_arg :=
  (* A path [x] or [π.x], looked up in the environment. *)
  | PArgPath (π : path)
  (* A constant data constructor: [()], [true], [false], [None], ... *)
  | PArgData (c : data)
  (* An integer literal. *)
  | PArgInt (i : Z).

(* ------------------------------------------------------------------------ *)

(* Primitive operators. *)

(* A binary operator is a strict, effect-free primitive: both of its operands
   are evaluated (in parallel: see [EBinOp] in [eval.v]) before the operator
   itself is applied to the resulting values. The short-circuiting Boolean
   connectives [&&] and [||] are therefore *not* binary operators; they remain
   separate constructs ([EBoolConj] and [EBoolDisj]). *)

Inductive bin_op :=
  (* Integer arithmetic. *)
  | BAdd | BSub | BMul | BDiv | BMod
  (* Integer logical operations. *)
  | BLand | BLor | BLxor | BLsl | BLsr | BAsr
  (* Physical equality [==]. *)
  | BPhysEq
  (* Polymorphic structural comparison. *)
  | BEq | BNe | BLt | BLe | BGt | BGe.

(* A unary operator is subject to the same discipline. *)

Inductive un_op :=
  (* Integer negation and bitwise complement. *)
  | UNeg | ULnot
  (* Boolean negation. *)
  | UNot.

(* ------------------------------------------------------------------------ *)

(* Expressions. *)

Inductive expr :=

  (* A placeholder for as-yet-unsupported constructs. *)
  | EUnsupported

  (* Path: [x] or [π.x]. *)
  | EPath (x : path)

  (* An anonymous function. *)
  | EAnonFun (a : anonfun)

  (* Function application: [e1 e2]. *)
  (* Every function is considered unary. *)
  | EApp (e1 e2 : expr)

  (* Tuple construction: [(e1, e2, ...)]. *)
  | ETuple (es : list expr)

  (* Data constructor application: [A (e)]. *)
  (* Every data constructor is considered unary. *)
  | EData (c : data) (e : list expr)
  | EXData (π : path) (e : list expr)

  (* Record construction: [{ es }]. *)
  | ERecord (t : mut_tag) (es : list expr)
  (* Record update: [{ e with es }]. *)
  | ERecordUpdate (e : expr) (fes : list fexpr)
  (* Record access: [e.f]. *)
  | ERecordAccess (e : expr) (f : field)
  (* Mutable record field assignment: [e1.f <- e2]. *)
  | ERecordSet (e1 : expr) (f : field) (e2 : expr)
  (* Atomic record field location: [[%atomic.loc e.f]]. *)
  | EAtomicLoc (e : expr) (f : field)

  (* Inline-record construction: [A {es}] *)
  | EInline (c : data) (t : mut_tag) (es : list expr)

  (* An array literal: [ [|1;2;3|] ] *)
  | EArrayLit (es : list expr)
  (* Length of an array: [Array.length a] *)
  | EArrayLength (e : expr)
  (* Array access with bounds check: [Array.get a n] *)
  | EArrayGet (e1 e2 : expr)
  (* Array update with bounds check: [Array.set a n v] *)
  | EArraySet (e1 e2 e3 : expr)
  (* Array creation: [Array.make n v] *)
  | EArrayMake (e1 e2 : expr)

  | EFreeze (e : expr)
  | EUnfreeze (e : expr)

  (* Boolean conjunction and disjunction. These short-circuit, so they are
     not binary operators: see [bin_op]. *)
  | EBoolConj (e1 e2 : expr)
  | EBoolDisj (e1 e2 : expr)

  (* Application of a unary operator: [op e]. *)
  | EUnOp (op : un_op) (e : expr)
  (* Application of a binary operator: [e1 op e2]. *)
  | EBinOp (op : bin_op) (e1 e2 : expr)

  (* Integer literals. *)
  | EInt (i : Z)
  | EMaxInt
  | EMinInt

  (* Floating-point literals. *)
  | EFloat (f : float)

  (* Character literals. *)
  | EChar (c: char)

  (* String literals. *)
  | EString (s: string)

  (* Non-recursive local definition: [let bs in e]. *)
  | ELet (bs : list binding) (e : expr)

  (* Recursive local definition: [let rbs in e]. *)
  | ELetRec (rbs : list rec_binding) (e : expr)

  (* Sequence: [e1; e2]. *)
  | ESeq (e1 e2 : expr)

  (* Conditional: [if e then e1] and [if e then e1 else e2]. *)
  | EIfThen (e e1 : expr)
  | EIfThenElse (e e1 e2 : expr)

  (* Pattern matching: [match e with bs]. *)
  | EMatch (e : expr) (bs : list branch)
  (* Pattern matching with shallow handling of effects. *)
  | EShallowMatch (e : expr) (bs : list branch)

  (* Raising an exception: [raise e]. *)
  | ERaise (e : expr)

  (* Performing an effect: [perform e]. *)
  | EPerform (e : expr)
  (* Continuing a continuation: [continue e1 e2]. *)
  | EContinue (e1 : expr) (e2 : expr)
  (* Discontinuing a continuation: [discontinue e1 e2]. *)
  | EDiscontinue (e1 : expr) (e2 : expr)

  (* Loop: [while e do body done]. *)
  | EWhile (e body : expr)
  (* Loop: [for x = e1 to e2 do e done]. *)
  | EFor (x : var) (e1 e2 e : expr)

  (* Fatal error: [assert false]. *)
  (* We model OCaml's unreachable construct [.] in this way, too. *)
  | EAssertFalse

  (* Runtime assertion: [assert(e)]. *)
  | EAssert (e : expr)

  (* Bringing a structure item into scope:
     [let exception E in e]
     [let external add_int : int -> int -> int = "%addint" in e]
     [let open M in e]. *)
  | ELetSitem (struct : sitem) (e : expr)

  (* References. As in OCaml, a reference is a mutable record with a single
     field: these behave as [ERecord], [ERecordAccess] and [ERecordSet] at
     field [0]. *)
  (* Reference allocation: [ref e]. *)
  | ERef (e : expr)
  (* Reference lookup: [!e]. *)
  | ELoad (e : expr)
  (* Reference assignment: [e1 := e2]. *)
  | EStore (e1 e2 : expr)

  (* Atomic operations on a field location (see [EAtomicLoc]). *)
  (* Load: [Atomic.Loc.get e]. *)
  | EFieldLoad (e : expr)
  (* Exchange: [Atomic.Loc.exchange e1 e2]. *)
  | EExchange (e1 e2 : expr)
  (* Compare-and-set: [Atomic.Loc.compare_and_set e1 e2 e3]. *)
  | ECAS (e1 e2 e3 : expr)
  (* Fetch-and-add: [Atomic.Loc.fetch_and_add e1 e2]. *)
  | EFAA (e1 e2 : expr)

  (* Allocating a prophecy variable: [Proph.create ()]. *)
  | ENewProph
  (* Resolving a prophecy variable: [e [@resolve π a]]. *)
  | EResolve (e : expr) (π : path) (a : proph_arg)

  | EIgnore (e : expr)

  (* Creating a thread: ≈ [Thread.create f arg]. *)
  | EFork (e1 e2 : expr)
  (* Waiting for another thread to terminate: ≈ [Domain.join th]. *)
  | EJoin (e : expr)

(* Field-expression pairs. *)

with fexpr :=
  | Fexpr (f : field)  (e : expr)

(* A branch is of the form [cp -> e],
   where [cp] is a computation pattern. *)

with branch :=
  | Branch (cp : cpat) (e : expr)

(* A binding is of the form [p = e]. *)

with binding :=
  | Binding (p : pat) (e : expr)

(* A recursive binding is of the form [f = a]. *)

with rec_binding :=
  | RecBinding (f : var) (a : anonfun)

(* An anonymous function is of the form [fun x -> e]. We allow only
   this form as a primitive construct, because this simplifies the
   evaluator. The constructs [function bs], where [bs] is a list of
   branches, and [fun ps -> e], where [ps] is a list of patterns, are
   regarded as sugar: see [EFunction] and [EFunMultiPat]. *)

with anonfun :=
  | AnonFun (x : var) (e : expr)

(* ------------------------------------------------------------------------ *)

(* Module expressions. *)

with mexpr :=

  (* A placeholder for as-yet-unsupported constructs. *)
  | MUnsupported

  (* A module path. *)
  | MPath (π : path)

  (* A structure [struct ... end]. *)
  | MStruct (items : list sitem)

  (* A functor [functor _ -> struct ... end]. *)
  | MFunctor (x : var) (items : list sitem)

  (* A coercion, that is, a shape restriction operation. This operation is
     written [M : S] in OCaml surface syntax, and is sometimes implicit: for
     example, a functor application [F(M)] must be understood as [F(M : S)]
     where [S] is the expected shape of the argument of the functor [F]. *)
  | MCoercion (me : mexpr) (c : coercion)

(* Structure items. *)

with sitem :=

  (* A non-recursive toplevel definition [let bs]. *)
  | ILet (bs : list binding)

  (* A recursive toplevel definition [let rec rbs]. *)
  | ILetRec (rbs : list rec_binding)

  (* A module definition [M = me]. *)
  | IModule (m : module) (me : mexpr)

  (* An [open] directive [open me]. *)
  | IOpen (me : mexpr)

  (* An [include] directive [include me]. *)
  | IInclude (me : mexpr)

  (* An external declaration [external x = e]. *)
  | IExternal (x : var) (e : expr)

  (* An extensible variant type extension [type t += cs]. *)
  | IExtend (cs : list name)

.

Scheme expr_fexpr_rec := Induction for expr Sort Set
  with fexprs_expr_rec := Induction for fexpr Sort Set
  with bindings_expr_rec := Induction for binding Sort Set
  with branches_expr_rec := Induction for branch Sort Set
  with sitem_expr_rec := Induction for sitem Sort Set
  with mexpr_expr_rec := Induction for mexpr Sort Set.

(* ------------------------------------------------------------------------ *)

(* A handler is a list of branches. *)

Definition handler := list branch.

(* ------------------------------------------------------------------------ *)

(* Values. *)

(* These values serve as values both for expressions and for module
   expressions. Similarly, environments map both variables to values
   and modules to values. *)

Inductive val : Type :=
  (* A simple (non-recursive) closure. *)
  | VClo (η : list (var * val)) (a : anonfun)
  (* A recursive closure. *)
  (* [η] is the environment at the closure creation site. It does not include
     entries for the functions defined by the recursive bindings [rbs]. *)
  (* The recursive bindings [rbs] are those of the closure creation site. *)
  (* The name [f] is the closure's entry point. *)
  | VCloRec (η : list (var * val)) (rbs : list rec_binding) (f : var)
  (* A string. *)
  | VString (s: string)
  (* A machine integer. *)
  | VInt (i : int)
  (* A floating-point number. *)
  | VFloat (f : float)
  (* A tuple. *)
  | VTuple (vs : list val)
  (* A data constructor value. *)
  | VData (c : data) (v : list val)
  (* A data constructor value for an extensible type. *)
  (* Extension constructors are dynamically alocated to the heap.
     [l] is the location of the constructor. Extensible types can
     alias by having two constructors point to the same location. *)
  | VXData (l: loc) (v : list val)
  (* A location. *)
  | VLoc (l : loc)
  (* A prophecy identifier. *)
  | VProph (p : proph_id)
  (* Both records and array are represented as pointers to a block. *)
  | VRecord (l : loc)
  | VArray (l : loc)
  (* Inline records contain both a tag and a pointer to a block. *)
  | VInline (c : data) (l : loc)
  (* A continuation; more precisely, a location which stores a continuation. *)
  | VCont (k : cont)
  (* A thread id. *)
  | VThread (t : thread)
  (* A module. *)
  | VStruct (xvs : list (var * val))
  (* A functor. *)
  | VFunctor (η : list (var * val)) (x : var) (xvs : list sitem)
  | VChar (c: char)
.

(* Osiris' own scopes for expressions and values. Osiris used to borrow the
   [expr_scope] and [val_scope] that Iris declares in [iris.bi.weakestpre], but
   pulling that module into scope also brings Iris' Texan triple notations,
   which clash with ours (see [program_logic/triples.v]).

   Only the scopes are declared here; the notations that populate [expr_scope]
   live in [notations.v]. This way a file can delimit with [%E] / [%V] without
   pulling in the notations themselves. *)
Declare Scope expr_scope.
Delimit Scope expr_scope with E.

Declare Scope val_scope.
Delimit Scope val_scope with V.

Definition env := list (var * val).
Definition envs := (env * env)%type.

(* ------------------------------------------------------------------------ *)

(* Core sugar, used in eval.v. *)

(* More sugar is defined in sugar.v. *)

(* Primitive operators. *)

(* [EUnOp] and [EBinOp] subsume what used to be one expression constructor per
   operator. These abbreviations restore the old names: they are accepted both
   in terms and in patterns, so the translator, the notations of [notations.v]
   and the reasoning rules can keep spelling out [EIntAdd e1 e2] and friends. *)

Abbreviation EIntNeg e := (EUnOp UNeg e).
Abbreviation EIntLnot e := (EUnOp ULnot e).
Abbreviation EBoolNeg e := (EUnOp UNot e).

Abbreviation EIntAdd e1 e2 := (EBinOp BAdd e1 e2).
Abbreviation EIntSub e1 e2 := (EBinOp BSub e1 e2).
Abbreviation EIntMul e1 e2 := (EBinOp BMul e1 e2).
Abbreviation EIntDiv e1 e2 := (EBinOp BDiv e1 e2).
Abbreviation EIntMod e1 e2 := (EBinOp BMod e1 e2).

Abbreviation EIntLand e1 e2 := (EBinOp BLand e1 e2).
Abbreviation EIntLor  e1 e2 := (EBinOp BLor e1 e2).
Abbreviation EIntLxor e1 e2 := (EBinOp BLxor e1 e2).
Abbreviation EIntLsl  e1 e2 := (EBinOp BLsl e1 e2).
Abbreviation EIntLsr  e1 e2 := (EBinOp BLsr e1 e2).
Abbreviation EIntAsr  e1 e2 := (EBinOp BAsr e1 e2).

Abbreviation EOpPhysEq e1 e2 := (EBinOp BPhysEq e1 e2).
Abbreviation EOpEq e1 e2 := (EBinOp BEq e1 e2).
Abbreviation EOpNe e1 e2 := (EBinOp BNe e1 e2).
Abbreviation EOpLt e1 e2 := (EBinOp BLt e1 e2).
Abbreviation EOpLe e1 e2 := (EBinOp BLe e1 e2).
Abbreviation EOpGt e1 e2 := (EBinOp BGt e1 e2).
Abbreviation EOpGe e1 e2 := (EBinOp BGe e1 e2).

(* Unit. *)

Abbreviation PUnit :=
  (PData "()" $ []).

Abbreviation EUnit :=
  (EData "()" $ []).

Abbreviation VUnit :=
  (VData "()" $ []).

(* Constant constructors, that is, constructors of arity 0. *)

Abbreviation PConstant c :=
  (PData c $ []).

Abbreviation EConstant c :=
  (EData c $ []).

Abbreviation VConstant c :=
  (VData c $ []).

(* The Boolean constants. *)

Definition BoolConstructor (b : bool) :=
  if b then "true" else "false".

Abbreviation PBool b :=
  (PConstant (BoolConstructor b)).

Abbreviation EBool b :=
  (EConstant (BoolConstructor b)).

Abbreviation EFalse :=
  (EBool false).

Abbreviation ETrue :=
  (EBool true).

Abbreviation VBool b :=
  (VConstant (BoolConstructor b)).

Abbreviation VFalse :=
  (VConstant "false").

Abbreviation VTrue :=
  (VConstant "true").

(* ------------------------------------------------------------------------ *)

(* Lemmas about the auxiliary function [BoolConstructor]. *)

Lemma BoolConstructor_injective b1 b2 :
  BoolConstructor b1 = BoolConstructor b2 →
  b1 = b2.
Proof.
  destruct b1, b2; simpl; congruence.
Qed.

Lemma BoolConstructor_congruent_contrapositive b1 b2 :
  BoolConstructor b1 ≠ BoolConstructor b2 →
  b1 ≠ b2.
Proof.
  congruence.
Qed.
