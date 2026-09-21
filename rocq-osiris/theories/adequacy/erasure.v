From stdpp Require Import list gmap.
From osiris.utils Require Import base.
From osiris.lang Require Import syntax outcome.
From osiris.semantics Require Import semantics strategy.
From osiris.program_logic Require Import subjective_step.

(* -------------------------------------------------------------------------- *)

(** * Erasure of prophecies. *)

(* This file defines the erasure of prophecies from a program (of type
   [expr]).
   Only two constructs in this work mention prophecies:
   - [ENewProph] erases to [()].
   - [EResolve e π a] erases to [e]. *)

(* Local [fix]es, as in lang/ind.v: [list expr] is not part of [expr]'s
   family, so a sibling [with erase_exprs] would fail the guard condition.
   Top-level names for them come after the definition. *)

Fixpoint erase_expr (e : expr) : expr :=
  let erase_exprs :=
    fix erase_exprs es :=
      match es with
      | nil => nil
      | e :: es => erase_expr e :: erase_exprs es
      end in
  let erase_fexprs :=
    fix erase_fexprs fes :=
      match fes with
      | nil => nil
      | Fexpr f e :: fes => Fexpr f (erase_expr e) :: erase_fexprs fes
      end in
  let erase_branches :=
    fix erase_branches bs :=
      match bs with
      | nil => nil
      | Branch cp e :: bs => Branch cp (erase_expr e) :: erase_branches bs
      end in
  let erase_bindings :=
    fix erase_bindings bs :=
      match bs with
      | nil => nil
      | Binding p e :: bs => Binding p (erase_expr e) :: erase_bindings bs
      end in
  let erase_rec_bindings :=
    fix erase_rec_bindings rbs :=
      match rbs with
      | nil => nil
      | RecBinding f a :: rbs =>
          RecBinding f (erase_anonfun a) :: erase_rec_bindings rbs
      end in
  match e with
  | ENewProph =>
      EUnit
  | EResolve e π a =>
      erase_expr e

  | EUnsupported =>
      EUnsupported
  | EPath x =>
      EPath x
  | EAnonFun a =>
      EAnonFun (erase_anonfun a)
  | EApp e1 e2 =>
      EApp (erase_expr e1) (erase_expr e2)
  | ETuple es =>
      ETuple (erase_exprs es)
  | EData c es =>
      EData c (erase_exprs es)
  | EXData π es =>
      EXData π (erase_exprs es)
  | ERecord t es =>
      ERecord t (erase_exprs es)
  | ERecordUpdate e fes =>
      ERecordUpdate (erase_expr e) (erase_fexprs fes)
  | ERecordAccess e f =>
      ERecordAccess (erase_expr e) f
  | ERecordSet e1 f e2 =>
      ERecordSet (erase_expr e1) f (erase_expr e2)
  | EAtomicLoc e f =>
      EAtomicLoc (erase_expr e) f
  | EInline c t es =>
      EInline c t (erase_exprs es)
  | EArrayLit es =>
      EArrayLit (erase_exprs es)
  | EArrayLength e =>
      EArrayLength (erase_expr e)
  | EArrayGet e1 e2 =>
      EArrayGet (erase_expr e1) (erase_expr e2)
  | EArraySet e1 e2 e3 =>
      EArraySet (erase_expr e1) (erase_expr e2) (erase_expr e3)
  | EArrayMake e1 e2 =>
      EArrayMake (erase_expr e1) (erase_expr e2)
  | EFreeze e =>
      EFreeze (erase_expr e)
  | EUnfreeze e =>
      EUnfreeze (erase_expr e)
  | EBoolConj e1 e2 =>
      EBoolConj (erase_expr e1) (erase_expr e2)
  | EBoolDisj e1 e2 =>
      EBoolDisj (erase_expr e1) (erase_expr e2)
  | EBoolNeg e =>
      EBoolNeg (erase_expr e)
  | EInt i =>
      EInt i
  | EMaxInt =>
      EMaxInt
  | EMinInt =>
      EMinInt
  | EIntNeg e =>
      EIntNeg (erase_expr e)
  | EIntAdd e1 e2 =>
      EIntAdd (erase_expr e1) (erase_expr e2)
  | EIntSub e1 e2 =>
      EIntSub (erase_expr e1) (erase_expr e2)
  | EIntMul e1 e2 =>
      EIntMul (erase_expr e1) (erase_expr e2)
  | EIntDiv e1 e2 =>
      EIntDiv (erase_expr e1) (erase_expr e2)
  | EIntMod e1 e2 =>
      EIntMod (erase_expr e1) (erase_expr e2)
  | EIntLand e1 e2 =>
      EIntLand (erase_expr e1) (erase_expr e2)
  | EIntLor e1 e2 =>
      EIntLor (erase_expr e1) (erase_expr e2)
  | EIntLxor e1 e2 =>
      EIntLxor (erase_expr e1) (erase_expr e2)
  | EIntLnot e =>
      EIntLnot (erase_expr e)
  | EIntLsl e1 e2 =>
      EIntLsl (erase_expr e1) (erase_expr e2)
  | EIntLsr e1 e2 =>
      EIntLsr (erase_expr e1) (erase_expr e2)
  | EIntAsr e1 e2 =>
      EIntAsr (erase_expr e1) (erase_expr e2)
  | EFloat f =>
      EFloat f
  | EChar c =>
      EChar c
  | EString s =>
      EString s
  | EOpPhysEq e1 e2 =>
      EOpPhysEq (erase_expr e1) (erase_expr e2)
  | EOpEq e1 e2 =>
      EOpEq (erase_expr e1) (erase_expr e2)
  | EOpNe e1 e2 =>
      EOpNe (erase_expr e1) (erase_expr e2)
  | EOpLt e1 e2 =>
      EOpLt (erase_expr e1) (erase_expr e2)
  | EOpLe e1 e2 =>
      EOpLe (erase_expr e1) (erase_expr e2)
  | EOpGt e1 e2 =>
      EOpGt (erase_expr e1) (erase_expr e2)
  | EOpGe e1 e2 =>
      EOpGe (erase_expr e1) (erase_expr e2)
  | ELet bs e =>
      ELet (erase_bindings bs) (erase_expr e)
  | ELetRec rbs e =>
      ELetRec (erase_rec_bindings rbs) (erase_expr e)
  | ESeq e1 e2 =>
      ESeq (erase_expr e1) (erase_expr e2)
  | EIfThen e e1 =>
      EIfThen (erase_expr e) (erase_expr e1)
  | EIfThenElse e e1 e2 =>
      EIfThenElse (erase_expr e) (erase_expr e1) (erase_expr e2)
  | EMatch e bs =>
      EMatch (erase_expr e) (erase_branches bs)
  | EShallowMatch e bs =>
      EShallowMatch (erase_expr e) (erase_branches bs)
  | ERaise e =>
      ERaise (erase_expr e)
  | EPerform e =>
      EPerform (erase_expr e)
  | EContinue e1 e2 =>
      EContinue (erase_expr e1) (erase_expr e2)
  | EDiscontinue e1 e2 =>
      EDiscontinue (erase_expr e1) (erase_expr e2)
  | EWhile e body =>
      EWhile (erase_expr e) (erase_expr body)
  | EFor x e1 e2 e =>
      EFor x (erase_expr e1) (erase_expr e2) (erase_expr e)
  | EAssertFalse =>
      EAssertFalse
  | EAssert e =>
      EAssert (erase_expr e)
  | ELetSitem s e =>
      ELetSitem (erase_sitem s) (erase_expr e)
  | ERef e =>
      ERef (erase_expr e)
  | ELoad e =>
      ELoad (erase_expr e)
  | EStore e1 e2 =>
      EStore (erase_expr e1) (erase_expr e2)
  | EExchange e1 e2 =>
      EExchange (erase_expr e1) (erase_expr e2)
  | ECAS e1 e2 e3 =>
      ECAS (erase_expr e1) (erase_expr e2) (erase_expr e3)
  | EFAA e1 e2 =>
      EFAA (erase_expr e1) (erase_expr e2)
  | EIgnore e =>
      EIgnore (erase_expr e)
  | EFork e1 e2 =>
      EFork (erase_expr e1) (erase_expr e2)
  | EJoin e =>
      EJoin (erase_expr e)
  end

with erase_anonfun (a : anonfun) : anonfun :=
  match a with
  | AnonFun x e => AnonFun x (erase_expr e)
  end

with erase_mexpr (me : mexpr) : mexpr :=
  let erase_sitems :=
    fix erase_sitems items :=
      match items with
      | nil => nil
      | i :: items => erase_sitem i :: erase_sitems items
      end in
  match me with
  | MUnsupported =>
      MUnsupported
  | MPath π =>
      MPath π
  | MStruct items =>
      MStruct (erase_sitems items)
  | MFunctor x items =>
      MFunctor x (erase_sitems items)
  | MCoercion me c =>
      MCoercion (erase_mexpr me) c
  end

with erase_sitem (i : sitem) : sitem :=
  let erase_bindings :=
    fix erase_bindings bs :=
      match bs with
      | nil => nil
      | Binding p e :: bs => Binding p (erase_expr e) :: erase_bindings bs
      end in
  let erase_rec_bindings :=
    fix erase_rec_bindings rbs :=
      match rbs with
      | nil => nil
      | RecBinding f a :: rbs =>
          RecBinding f (erase_anonfun a) :: erase_rec_bindings rbs
      end in
  match i with
  | ILet bs =>
      ILet (erase_bindings bs)
  | ILetRec rbs =>
      ILetRec (erase_rec_bindings rbs)
  | IModule m me =>
      IModule m (erase_mexpr me)
  | IOpen me =>
      IOpen (erase_mexpr me)
  | IInclude me =>
      IInclude (erase_mexpr me)
  | IExternal x e =>
      IExternal x (erase_expr e)
  | IExtend cs =>
      IExtend cs
  end
.

(* -------------------------------------------------------------------------- *)

(* Top-level names for the traversals above. They mirror the local [fix]es
   exactly, so the equations relating them hold by conversion. *)

Definition erase_fexpr (fe : fexpr) : fexpr :=
  match fe with
  | Fexpr f e => Fexpr f (erase_expr e)
  end.

Definition erase_branch (b : branch) : branch :=
  match b with
  | Branch cp e => Branch cp (erase_expr e)
  end.

Definition erase_binding (b : binding) : binding :=
  match b with
  | Binding p e => Binding p (erase_expr e)
  end.

Definition erase_rec_binding (rb : rec_binding) : rec_binding :=
  match rb with
  | RecBinding f a => RecBinding f (erase_anonfun a)
  end.

Fixpoint erase_exprs (es : list expr) : list expr :=
  match es with
  | nil => nil
  | e :: es => erase_expr e :: erase_exprs es
  end.

Fixpoint erase_fexprs (fes : list fexpr) : list fexpr :=
  match fes with
  | nil => nil
  | Fexpr f e :: fes => Fexpr f (erase_expr e) :: erase_fexprs fes
  end.

Fixpoint erase_branches (bs : list branch) : list branch :=
  match bs with
  | nil => nil
  | Branch cp e :: bs => Branch cp (erase_expr e) :: erase_branches bs
  end.

Fixpoint erase_bindings (bs : list binding) : list binding :=
  match bs with
  | nil => nil
  | Binding p e :: bs => Binding p (erase_expr e) :: erase_bindings bs
  end.

Fixpoint erase_rec_bindings (rbs : list rec_binding) : list rec_binding :=
  match rbs with
  | nil => nil
  | RecBinding f a :: rbs => RecBinding f (erase_anonfun a) :: erase_rec_bindings rbs
  end.

Fixpoint erase_sitems (items : list sitem) : list sitem :=
  match items with
  | nil => nil
  | i :: items => erase_sitem i :: erase_sitems items
  end.


Abbreviation erase_handler := erase_branches.


Lemma erase_exprs_fmap es : erase_exprs es = erase_expr <$> es.
Proof. reflexivity. Qed.

Lemma erase_fexprs_fmap fes : erase_fexprs fes = erase_fexpr <$> fes.
Proof. induction fes as [| [f e] fes IH]; simpl; by rewrite ?IH. Qed.

Lemma erase_branches_fmap bs : erase_branches bs = erase_branch <$> bs.
Proof. induction bs as [| [cp e] bs IH]; simpl; by rewrite ?IH. Qed.

Lemma erase_bindings_fmap bs : erase_bindings bs = erase_binding <$> bs.
Proof. induction bs as [| [p e] bs IH]; simpl; by rewrite ?IH. Qed.

Lemma erase_rec_bindings_fmap rbs :
  erase_rec_bindings rbs = erase_rec_binding <$> rbs.
Proof. induction rbs as [| [f a] rbs IH]; simpl; by rewrite ?IH. Qed.

Lemma erase_sitems_fmap items : erase_sitems items = erase_sitem <$> items.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)

(* The equations that connect [erase_expr] to those names. Each one holds by
   conversion; they are stated anyway, as the readable form of the definition
   and as rewriting rules for the proofs to come. *)

Lemma erase_ETuple es :
  erase_expr (ETuple es) = ETuple (erase_exprs es).
Proof. reflexivity. Qed.

Lemma erase_EData c es :
  erase_expr (EData c es) = EData c (erase_exprs es).
Proof. reflexivity. Qed.

Lemma erase_EXData π es :
  erase_expr (EXData π es) = EXData π (erase_exprs es).
Proof. reflexivity. Qed.

Lemma erase_ERecord t es :
  erase_expr (ERecord t es) = ERecord t (erase_exprs es).
Proof. reflexivity. Qed.

Lemma erase_EInline c t es :
  erase_expr (EInline c t es) = EInline c t (erase_exprs es).
Proof. reflexivity. Qed.

Lemma erase_EArrayLit es :
  erase_expr (EArrayLit es) = EArrayLit (erase_exprs es).
Proof. reflexivity. Qed.

Lemma erase_ERecordUpdate e fes :
  erase_expr (ERecordUpdate e fes) =
  ERecordUpdate (erase_expr e) (erase_fexprs fes).
Proof. reflexivity. Qed.

Lemma erase_EMatch e bs :
  erase_expr (EMatch e bs) = EMatch (erase_expr e) (erase_branches bs).
Proof. reflexivity. Qed.

Lemma erase_EShallowMatch e bs :
  erase_expr (EShallowMatch e bs) =
  EShallowMatch (erase_expr e) (erase_branches bs).
Proof. reflexivity. Qed.

Lemma erase_ELet bs e :
  erase_expr (ELet bs e) = ELet (erase_bindings bs) (erase_expr e).
Proof. reflexivity. Qed.

Lemma erase_ELetRec rbs e :
  erase_expr (ELetRec rbs e) = ELetRec (erase_rec_bindings rbs) (erase_expr e).
Proof. reflexivity. Qed.

Lemma erase_MStruct items :
  erase_mexpr (MStruct items) = MStruct (erase_sitems items).
Proof. reflexivity. Qed.

Lemma erase_MFunctor x items :
  erase_mexpr (MFunctor x items) = MFunctor x (erase_sitems items).
Proof. reflexivity. Qed.

Lemma erase_ILet bs :
  erase_sitem (ILet bs) = ILet (erase_bindings bs).
Proof. reflexivity. Qed.

Lemma erase_ILetRec rbs :
  erase_sitem (ILetRec rbs) = ILetRec (erase_rec_bindings rbs).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)

(** * Erasure of values. *)

(* We need to deal with the case where a closure has captured a prophecy.

   We erase [ENewProph] to unit, so a prophecy [VProph p] erases to
   [VUnit]. This is unlike HeapLang's [LitProphecy p], which must become
   [LitPoison] and is then stuck wherever the erased program uses it. *)

Fixpoint erase_val (v : val) : val :=
  let erase_vals :=
    fix erase_vals vs :=
      match vs with
      | nil => nil
      | v :: vs => erase_val v :: erase_vals vs
      end in
  let erase_env :=
    fix erase_env η :=
      match η with
      | nil => nil
      | (x, v) :: η => (x, erase_val v) :: erase_env η
      end in
  match v with
  | VClo η a => VClo (erase_env η) (erase_anonfun a)
  | VCloRec η rbs f => VCloRec (erase_env η) (erase_rec_bindings rbs) f
  | VString s => VString s
  | VInt i => VInt i
  | VFloat f => VFloat f
  | VTuple vs => VTuple (erase_vals vs)
  | VData c vs => VData c (erase_vals vs)
  | VXData l vs => VXData l (erase_vals vs)
  | VLoc l => VLoc l
  | VProph p => VUnit
  | VRecord l => VRecord l
  | VArray l => VArray l
  | VInline c l => VInline c l
  | VCont k => VCont k
  | VThread t => VThread t
  | VStruct xvs => VStruct (erase_env xvs)
  | VFunctor η x items => VFunctor (erase_env η) x (erase_sitems items)
  | VChar c => VChar c
  end.

Fixpoint erase_vals (vs : list val) : list val :=
  match vs with
  | nil => nil
  | v :: vs => erase_val v :: erase_vals vs
  end.

Fixpoint erase_env (η : env) : env :=
  match η with
  | nil => nil
  | (x, v) :: η => (x, erase_val v) :: erase_env η
  end.

(* The outcome of a computation, under given maps on results and exceptions.
   Usually both are [erase_val], but a computation returning a location has
   nothing to erase in its result, and then [fA] is the identity. *)

Definition erase_out2 {A E} (fA : A → A) (fE : E → E) (o : outcome2 A E)
: outcome2 A E :=
  match o with
  | O2Ret a => O2Ret (fA a)
  | O2Throw e => O2Throw (fE e)
  end.

Definition erase_outcome : outcome2 val exn → outcome2 val exn :=
  erase_out2 erase_val erase_val.

(* The three-branch outcome that a handler observes. Its effect payload is a
   value; its continuation is a location, which erasure leaves alone. *)

Definition erase_out3 (o : outcome3 val exn) : outcome3 val exn :=
  match o with
  | O3Ret v => O3Ret (erase_val v)
  | O3Throw e => O3Throw (erase_val e)
  | O3Perform v k => O3Perform (erase_val v) k
  end.

(* -------------------------------------------------------------------------- *)

(** * Erasure of system calls. *)

(* A [Stop] call's argument can contain syntax ([CEval], for example),
   so erasing a [Stop] means erasing that argument. *)

Fixpoint erase_code_arg {X Y} (c : code X Y exn) : X → X :=
  match c in code X Y E return X → X with
  | CEval => λ '(η, e), (erase_env η, erase_expr e)
  | CLoop => λ '(η, x, i1, i2, e), (erase_env η, x, i1, i2, erase_expr e)
  | CFlip => id
  | CAlloc => erase_val
  | CAllocBlock => id
  | CLoad => id
  | CLoadBlock => id
  | CExchange => λ '(l, v), (l, erase_val v)
  | CSetBlockTag => id
  | CCAS => λ '(l, seen, v), (l, erase_val seen, erase_val v)
  | CFAA => id
  | CPerf => erase_val
  | CResume => λ '(l, o), (l, erase_outcome o)
  | CWrap => λ '(deep, k, η, bs), (deep, k, erase_env η, erase_branches bs)
  | CFork => λ '(f, a), (erase_val f, erase_val a)
  | CJoin => id
  | CNewProph => id
  | CResolve c => λ '(x, p, v), (erase_code_arg c x, p, v)
  | CReturn => erase_val
  end.

Definition erase_code_res {X Y} (c : code X Y exn) : Y → Y :=
  match c in code X Y E return Y → Y with
  | CFlip => id
  | CAlloc => id
  | CAllocBlock => id
  | CLoadBlock => id
  | CSetBlockTag => id
  | CWrap => id
  | CNewProph => id
  | CEval => erase_val
  | CLoop => erase_val
  | CLoad => erase_val
  | CExchange => erase_val
  | CCAS => erase_val
  | CFAA => erase_val
  | CPerf => erase_val
  | CResume => erase_val
  | CFork => erase_val
  | CJoin => erase_val
  | CResolve _ => erase_val
  | CReturn => erase_val
  end.

(* The three calls that erasure does not leave in place. *)

Definition no_proph_code {X Y E} (c : code X Y E) : Prop :=
  match c with
  | CNewProph | CResolve _ | CReturn => False
  | CEval => True
  | CLoop => True
  | CFlip => True
  | CAlloc => True
  | CAllocBlock => True
  | CLoad => True
  | CLoadBlock => True
  | CExchange => True
  | CSetBlockTag => True
  | CCAS => True
  | CFAA => True
  | CPerf => True
  | CResume => True
  | CWrap => True
  | CFork => True
  | CJoin => True
  end.

(* A call that cannot raise, which return or crash but never thrown.
   Needed because a resolution propagates an exception where the bare
   [Stop] it erases to crashes. *)

Definition code_no_throw {X Y} (c : code X Y exn) (x : X) : Prop :=
  ∀ σ σ' ex, ¬ step (σ, stop c x) (σ', Throw ex).

(* -------------------------------------------------------------------------- *)

(** * Erasure of [micro] computations. *)

(* The erasure of [micro] computations is defined as a relation rather
   than a function.
   This is specifically because [Par m1 m2 k]'s payload types [A1] and
   [A2] are bound by the constructor, so a [Fixpoint] on the term
   cannot produce the maps its branches need.

   Three constructors carry the content:

   - [EM_NewProph]: [Proph.create ()] becomes [()]. Erasure drops the
     allocation, whatever identifier it picks.
   - [EM_Resolve]: an annotated call becomes the call itself, at the same
     step; [p] and [v] are dropped.
   - [EM_ResolveReturn] / [EM_Return]: [eval] compiles a resolution on a
     non-atomic expression into a [CReturn] whose only job is to give the
     resolution a step. Erasure drops the node rather than leaving a no-op
     to keep [erase (eval η e) = eval (erase η) (erase e)].

   [EM_Stop] handles every other call under [no_proph_code]. *)

Inductive erase_micro : ∀ (A E : Type), (A → A) → (E → E) → micro A E → micro A E → Prop :=

  | EM_Ret {A E} (fA : A → A) (fE : E → E) a :
      erase_micro _ _ fA fE (Ret a) (Ret (fA a))

  | EM_Throw {A E} (fA : A → A) (fE : E → E) e :
      erase_micro _ _ fA fE (Throw e) (Throw (fE e))

  (* An annotated computation that crashes may erase to anything. This
     rule is required by [eval]: [erase_expr] drops a resolution
     ([EResolve e π a] becomes [e]) but [eval] looks [π] and [a] up in
     the environment before evaluating anything, which could crash if
     [π] isn't a well-formed path.

     I feel like this rule can be justified by the fact that a crash
     is stuck, so a configuration reaching one will violate the safety
     hypothesis. Additionaly, [erase_micro] occurs in the metatheorem
     as a hypothesis, where admitting more pairs weakens nothing. *)
  | EM_CrashL {A E} (fA : A → A) (fE : E → E) m' :
      erase_micro _ _ fA fE Crash m'

  | EM_Handle {A E} (fA : A → A) (fE : E → E) m m' h h' :
      erase_micro _ _ erase_val erase_val m m' →
      (∀ o, erase_micro _ _ fA fE (h o) (h' (erase_out3 o))) →
      erase_micro _ _ fA fE (Handle m h) (Handle m' h')

  | EM_Stop {A E X Y} (fA : A → A) (fE : E → E) (c : code X Y exn) x k k' :
      no_proph_code c →
      (∀ o, erase_micro _ _ fA fE (k o)
              (k' (erase_out2 (erase_code_res c) erase_val o))) →
      erase_micro _ _ fA fE (Stop c x k) (Stop c (erase_code_arg c x) k')

  | EM_NewProph {A E} (fA : A → A) (fE : E → E) x k m' :
      (∀ p, erase_micro _ _ fA fE (continue k p) m') →
      erase_micro _ _ fA fE (Stop CNewProph x k) m'

  | EM_Resolve {A E X} (fA : A → A) (fE : E → E) (c : code X val exn) x p v k k' :
      no_proph_code c →
      code_no_throw c x →
      (* The result map is the call's own, [erase_code_res c]. Saying instead
         that it is [erase_val] would need a case analysis on a code whose
         result type is already fixed, leaving irrefutable equations between
         types. *)
      (∀ w, erase_micro _ _ fA fE
              (k (O2Ret w)) (k' (O2Ret (erase_code_res c w)))) →
      erase_micro _ _ fA fE
        (Stop (CResolve c) (x, p, v) k) (Stop c (erase_code_arg c x) k')

  | EM_ResolveReturn {A E} (fA : A → A) (fE : E → E) w p v k m' :
      erase_micro _ _ fA fE (continue k w) m' →
      erase_micro _ _ fA fE (Stop (CResolve CReturn) (w, p, v) k) m'

  | EM_Return {A E} (fA : A → A) (fE : E → E) w k m' :
      erase_micro _ _ fA fE (continue k w) m' →
      erase_micro _ _ fA fE (Stop CReturn w k) m'

  | EM_Par {A E A1 A2 E'} (fA : A → A) (fE : E → E)
      (f1 : A1 → A1) (f2 : A2 → A2) (fE' : E' → E') m1 m1' m2 m2' k k' :
      erase_micro _ _ f1 fE' m1 m1' →
      erase_micro _ _ f2 fE' m2 m2' →
      (∀ o, erase_micro _ _ fA fE (k o)
              (k' (erase_out2 (prod_map f1 f2) fE' o))) →
      erase_micro _ _ fA fE (Par m1 m2 k) (Par m1' m2' k')
.

Global Arguments erase_micro {A E} fA fE m m'.

(* A derived constructor: [EM_Crash] is [EM_CrashL] at [m' := Crash]. *)
Definition EM_Crash {A E} (fA : A → A) (fE : E → E) :
  erase_micro fA fE (Crash : micro A E) Crash :=
  EM_CrashL fA fE Crash.

(* The instance the metatheory uses: a computation of an OCaml program,
   whose results and exceptions are both values. *)

Abbreviation erase_microvx := (erase_micro erase_val erase_val).

(* -------------------------------------------------------------------------- *)

(** ** The erasure is a congruence for the monad. *)

(* [eval] builds computations out of [ret], [bind], [try2], [par] and
   [stop]. The lemmas below say that erasing a compound means erasing
   its pieces, with the payload maps threaded through. *)

Lemma erase_inject2 {A E} (fA : A → A) (fE : E → E) o :
  erase_micro fA fE (inject2 o) (inject2 (erase_out2 fA fE o)).
Proof. destruct o; simpl; [ apply EM_Ret | apply EM_Throw ]. Qed.

Lemma erase_try2 {A E B F} (fA : A → A) (fE : E → E) (fB : B → B) (fF : F → F)
    m m' (g : outcome2 A E → micro B F) g' :
  erase_micro fA fE m m' →
  (∀ o, erase_micro fB fF (g o) (g' (erase_out2 fA fE o))) →
  erase_micro fB fF (try2 m g) (try2 m' g').
Proof.
  intros Hm. revert g g'.
  induction Hm;
    intros g g' Hg; simpl.
  - exact (Hg (O2Ret _)).
  - exact (Hg (O2Throw _)).
  - apply EM_CrashL.
  - apply EM_Handle; [ done | ]. intros o. by apply H0.
  - apply EM_Stop; [ done | ]. intros o. by apply H1.
  - apply EM_NewProph. intros o. by apply H0.
  - apply EM_Resolve; [ done | done | ]. intros w. by apply H2.
  - apply EM_ResolveReturn. by apply IHHm.
  - apply EM_Return. by apply IHHm.
  - eapply EM_Par; [ done | done | ]. intros o. by apply H0.
Qed.

Lemma erase_bind {A B E} (fA : A → A) (fE : E → E) (fB : B → B) m m' f f' :
  erase_micro fA fE m m' →
  (∀ a, erase_micro fB fE (f a) (f' (fA a))) →
  erase_micro fB fE (bind m f) (bind m' f').
Proof.
  intros Hm. revert f f'.
  induction Hm;
    intros f f' Hf; simpl.
  - apply Hf.
  - apply EM_Throw.
  - apply EM_CrashL.
  - apply EM_Handle; [ done | ]. intros o. by apply H0.
  - apply EM_Stop; [ done | ]. intros o. by apply H1.
  - apply EM_NewProph. intros o. by apply H0.
  - apply EM_Resolve; [ done | done | ]. intros w. by apply H2.
  - apply EM_ResolveReturn. by apply IHHm.
  - apply EM_Return. by apply IHHm.
  - eapply EM_Par; [ done | done | ]. intros o. by apply H0.
Qed.

Lemma erase_par {A1 A2 E} (f1 : A1 → A1) (f2 : A2 → A2) (fE : E → E)
    m1 m1' m2 m2' :
  erase_micro f1 fE m1 m1' →
  erase_micro f2 fE m2 m2' →
  erase_micro (prod_map f1 f2) fE (par m1 m2) (par m1' m2').
Proof.
  intros Hm1 Hm2.
  eapply EM_Par; [ eassumption | eassumption | ]. intros o. apply erase_inject2.
Qed.

Lemma erase_stop {X Y} (c : code X Y exn) x :
  no_proph_code c →
  erase_micro (erase_code_res c) erase_val (stop c x) (stop c (erase_code_arg c x)).
Proof.
  intros Hc. apply EM_Stop; [ done | ]. intros o. apply erase_inject2.
Qed.

Lemma erase_ret {A E} (fA : A → A) (fE : E → E) a :
  erase_micro fA fE (ret a) (ret (fA a)).
Proof. apply EM_Ret. Qed.

Lemma erase_of_option {A E} (fA : A → A) (fE : E → E) (o : option A) :
  erase_micro fA fE (of_option o) (of_option (fA <$> o)).
Proof. destruct o; simpl; [ apply EM_Ret | apply EM_Crash ]. Qed.

(* The three evaluation orders, and hence [pair_op] whatever the strategy
   picks. *)

Lemma erase_ltr {A1 A2 E} (f1 : A1 → A1) (f2 : A2 → A2) (fE : E → E)
    m1 m1' m2 m2' :
  erase_micro f1 fE m1 m1' →
  erase_micro f2 fE m2 m2' →
  erase_micro (prod_map f1 f2) fE (ltr m1 m2) (ltr m1' m2').
Proof.
  intros Hm1 Hm2. unfold ltr.
  eapply erase_bind; [ done | ]. intros a1. cbn beta.
  eapply erase_bind; [ done | ]. intros a2. cbn beta.
  exact (EM_Ret (prod_map f1 f2) fE (a1, a2)).
Qed.

Lemma erase_rtl {A1 A2 E} (f1 : A1 → A1) (f2 : A2 → A2) (fE : E → E)
    m1 m1' m2 m2' :
  erase_micro f1 fE m1 m1' →
  erase_micro f2 fE m2 m2' →
  erase_micro (prod_map f1 f2) fE (rtl m1 m2) (rtl m1' m2').
Proof.
  intros Hm1 Hm2. unfold rtl.
  eapply erase_bind; [ done | ]. intros a2. cbn beta.
  eapply erase_bind; [ done | ]. intros a1. cbn beta.
  exact (EM_Ret (prod_map f1 f2) fE (a1, a2)).
Qed.

Lemma erase_pair_op dir {A1 A2 E} (f1 : A1 → A1) (f2 : A2 → A2) (fE : E → E)
    m1 m1' m2 m2' :
  erase_micro f1 fE m1 m1' →
  erase_micro f2 fE m2 m2' →
  erase_micro (prod_map f1 f2) fE (pair_op dir m1 m2) (pair_op dir m1' m2').
Proof.
  destruct dir; simpl;
    eauto using erase_ltr, erase_rtl, erase_par.
Qed.

(* -------------------------------------------------------------------------- *)

(** * Erasure of stores and thread pools. *)

(* A block holds a value, a block of locations, or a continuation
   (where a continuation is a function into computations).
   Locations are unchanged: erasure neither allocates nor moves
   anything, but we need to erase stored values and continuations. *)

Definition erase_mem_block (b b' : mem_block) : Prop :=
  match b, b' with
  | Val v, Val v' => v' = erase_val v
  | Block t ls, Block t' ls' => t' = t ∧ ls' = ls
  | Kont k, Kont k' => ∀ o, erase_microvx (k o) (k' (erase_outcome o))
  | Shot, Shot => True
  | _, _ => False
  end.

Definition erase_heap :
    gmap locations.loc mem_block → gmap locations.loc mem_block → Prop :=
  map_relation (λ _, erase_mem_block) (λ _ _, False) (λ _ _, False).

(* The annotated program runs against the program logic's store, the erased
   one against a plain heap: only the heaps are related, since no program
   reads the prophecy identifiers it has allocated. *)

Definition erase_store (σ : store) (σe : heap) : Prop :=
  erase_heap σ.(st_heap) σe.

Definition erase_thpool : thpool → thpool → Prop :=
  map_relation (λ _, erase_microvx) (λ _ _, False) (λ _ _, False).

(* A program starts in the empty store, which is its own erasure. *)

Lemma erase_store_empty : erase_store ∅ ∅.
Proof.
  unfold erase_store, erase_heap, map_relation. intros l.
  simpl. rewrite lookup_empty. done.
Qed.
