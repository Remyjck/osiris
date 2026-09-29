(* Extracted modules *)
open Extracted.BinNums
open Extracted.Datatypes
open Extracted.String
open Extracted.Ascii
(* OCaml's standard library *)
open Stdlib

(** Numbers, lists, products, strings *)

let rec pos = function
  | 0 -> invalid_arg "pos" (* negative values end up here *)
  | 1 -> Coq_xH
  | i -> if i mod 2 = 0 then Coq_xO (pos (i / 2)) else Coq_xI (pos (i / 2))

let n = function 0 -> N0 | i -> Npos (pos i)

let z = function
  | 0 -> Z0
  | i -> if i > 0 then Zpos (pos i) else Zneg (pos (- i))

let rec nat = function
  | 0 -> O
  | n -> S (nat (n - 1))

let list = List.map

let prod f1 f2 (a1, a2) = (f1 a1, f2 a2)

let char c = ascii_of_N (n (Char.code c))

let string s = String.fold_right (fun c a -> String (char c, a)) s EmptyString


(** Syntax types *)

module O = Translatorlib.Syntax
module E = Extracted.Syntax

let var = string
let name = string
let path = list string
let data = string
let field = z

let mut_tag : O.mut_tag -> E.mut_tag = function
  | Mut -> Mut
  | Immut -> Immut

let proph_arg : O.proph_arg -> E.proph_arg = function
  | PArgPath p -> PArgPath (path p)
  | PArgData d -> PArgData (data d)
  | PArgInt i -> PArgInt (z i)

let rec pat : O.pat -> E.pat = function
  | PUnsupported    -> PUnsupported
  | PAny            -> PAny
  | PVar v          -> PVar (var v)
  | PAlias (p, v)   -> PAlias (pat p, var v)
  | POr (p1, p2)    -> POr (pat p1, pat p2)
  | PTuple ps       -> PTuple (list pat ps)
  | PData (d, ps)   -> PData (data d, pats ps)
  | PXData (ph, ps) -> PXData (path ph, pats ps)
  | PRecord fps     -> PRecord (fpats fps)
  | PTaggedRecord (d, p)  -> PTaggedRecord (data d, pat p)
  | PInt i          -> PInt (z i)
  | PChar c         -> PChar (char c)
  | PString s       -> PString (string s)

and cpat : O.cpat -> E.cpat = function
  | CVal p -> CVal (pat p)
  | CExc p -> CExc (pat p)
  | CEff (p1, p2) -> CEff (pat p1, pat p2)
  | COr (cp1, cp2) -> COr (cpat cp1, cpat cp2)

and pats l = list pat l
and fpats l = list (prod field pat) l


let rec coercion : O.coercion -> E.coercion = function
  | CIdentity -> CIdentity
  | CStruct fcs -> CStruct (fcoercions fcs)

and fcoercions l = list (fun (_, c) -> (EmptyString, coercion c)) l


let rec expr : O.expr -> E.expr = function
  | EDecorate (_, e) -> expr e
  | EUnsupported -> EUnsupported
  | EPath p -> EPath (path p)
  | EAnonFun af -> EAnonFun (anonfun af)
  | EApp (e1, e2) -> EApp (expr e1, expr e2)
  | ETuple es -> ETuple (exprs es)
  | EData (d, es) -> EData (data d, exprs es)
  | EXData (p, es) -> EXData (path p, exprs es)
  | ERecord (t, es) -> ERecord (mut_tag t, exprs es)
  | ERecordUpdate (e, fes) -> ERecordUpdate (expr e, fexprs fes)
  | ERecordAccess (e, f) -> ERecordAccess (expr e, field f)
  | ERecordSet (e1, f, e2) -> ERecordSet (expr e1, field f, expr e2)
  | EAtomicLoc (e, f) -> EAtomicLoc (expr e, field f)
  | EInline (d, t, es) -> EInline (data d, mut_tag t, exprs es)
  | EArrayLit es -> EArrayLit (exprs es)
  | EArrayLength e -> EArrayLength (expr e)
  | EArrayGet (e1, e2) -> EArrayGet (expr e1, expr e2)
  | EArraySet (e1, e2, e3) -> EArraySet (expr e1, expr e2, expr e3)
  | EArrayMake (e1, e2) -> EArrayMake (expr e1, expr e2)
  | EFreeze e -> EFreeze (expr e)
  | EUnfreeze e -> EUnfreeze (expr e)
  | EBoolConj (e1, e2) -> EBoolConj (expr e1, expr e2)
  | EBoolDisj (e1, e2) -> EBoolDisj (expr e1, expr e2)
  (* One constructor per operator on the translator's side; a single
     [EUnOp] / [EBinOp] node carrying an operator code on the Rocq side. *)
  | EBoolNeg e -> EUnOp (UNot, expr e)
  | EIntNeg e -> EUnOp (UNeg, expr e)
  | EIntLnot e -> EUnOp (ULnot, expr e)
  | EInt i -> EInt (z i)
  | EMaxInt -> EMaxInt
  | EMinInt -> EMinInt
  | EIntAdd (e1, e2) -> EBinOp (BAdd, expr e1, expr e2)
  | EIntSub (e1, e2) -> EBinOp (BSub, expr e1, expr e2)
  | EIntMul (e1, e2) -> EBinOp (BMul, expr e1, expr e2)
  | EIntDiv (e1, e2) -> EBinOp (BDiv, expr e1, expr e2)
  | EIntMod (e1, e2) -> EBinOp (BMod, expr e1, expr e2)
  | EIntLand (e1, e2) -> EBinOp (BLand, expr e1, expr e2)
  | EIntLor (e1, e2) -> EBinOp (BLor, expr e1, expr e2)
  | EIntLxor (e1, e2) -> EBinOp (BLxor, expr e1, expr e2)
  | EIntLsl (e1, e2) -> EBinOp (BLsl, expr e1, expr e2)
  | EIntLsr (e1, e2) -> EBinOp (BLsr, expr e1, expr e2)
  | EIntAsr (e1, e2) -> EBinOp (BAsr, expr e1, expr e2)
  | EFloat s -> EFloat (float_of_string s)
  | EChar c -> EChar (char c)
  | EString s -> EString (string s)
  | EOpPhysEq (e1, e2) -> EBinOp (BPhysEq, expr e1, expr e2)
  | EOpEq (e1, e2) -> EBinOp (BEq, expr e1, expr e2)
  | EOpNe (e1, e2) -> EBinOp (BNe, expr e1, expr e2)
  | EOpLt (e1, e2) -> EBinOp (BLt, expr e1, expr e2)
  | EOpLe (e1, e2) -> EBinOp (BLe, expr e1, expr e2)
  | EOpGt (e1, e2) -> EBinOp (BGt, expr e1, expr e2)
  | EOpGe (e1, e2) -> EBinOp (BGe, expr e1, expr e2)
  | ELet (bs, e) -> ELet (bindings bs, expr e)
  | ELetRec (rbs, e) -> ELetRec (rec_bindings rbs, expr e)
  | ESeq (e1, e2) -> ESeq (expr e1, expr e2)
  | EIfThen (e1, e2) -> EIfThen (expr e1, expr e2)
  | EIfThenElse (e1, e2, e3) -> EIfThenElse (expr e1, expr e2, expr e3)
  | EMatch (e, bs) -> EMatch (expr e, branches bs)
  | EShallowMatch (e, bs) -> EShallowMatch (expr e, branches bs)
  | ERaise e -> ERaise (expr e)
  | EPerform e -> EPerform (expr e)
  | EContinue (e1, e2) -> EContinue (expr e1, expr e2)
  | EDiscontinue (e1, e2) -> EDiscontinue (expr e1, expr e2)
  | EWhile (e1, e2) -> EWhile (expr e1, expr e2)
  | EFor (v, e1, e2, e3) -> EFor (var v, expr e1, expr e2, expr e3)
  | EAssertFalse -> EAssertFalse
  | EAssert e -> EAssert (expr e)
  | ELetSitem (s, e) -> ELetSitem (sitem s, expr e)
  | ERef e -> ERef (expr e)
  | ELoad e -> ELoad (expr e)
  | EStore (e1, e2) -> EStore (expr e1, expr e2)
  | EFieldLoad e -> EFieldLoad (expr e)
  | EExchange (e1, e2) -> EExchange (expr e1, expr e2)
  | ECAS (e1, e2, e3) -> ECAS (expr e1, expr e2, expr e3)
  | EFAA (e1, e2) -> EFAA (expr e1, expr e2)
  | ENewProph -> ENewProph
  | EResolve (e, p, a) -> EResolve (expr e, path p, proph_arg a)
  | EIgnore e -> EIgnore (expr e)
  | EFork (e1, e2) -> EFork (expr e1, expr e2)
  | EJoin e -> EJoin (expr e)

and fexpr : O.fexpr -> E.fexpr = function
  Fexpr (f, e) -> Fexpr (field f, expr e)

and branch : O.branch -> E.branch = function
  | Branch (cp, e) -> Branch (cpat cp, expr e)

and binding : O.binding -> E.binding = function
  | Binding (p, e) -> Binding (pat p, expr e)

and rec_binding : O.rec_binding -> E.rec_binding = function
  | RecBinding (v, af) -> RecBinding (var v, anonfun af)

and anonfun : O.anonfun -> E.anonfun = function
  | AnonFun (v, e) -> AnonFun (var v, expr e)
  | AnonFunction bs -> Extracted.Notations.coq_AnonFunction (branches bs)

and mexpr : O.mexpr -> E.mexpr = function
  | MUnsupported -> MUnsupported
  | MPath p -> MPath (path p)
  | MStruct l -> MStruct (sitems l)
  | MFunctor (v, l) -> MFunctor (var v, sitems l)
  | MCoercion (me, c) -> MCoercion (mexpr me, coercion c)

and sitem : O.sitem -> E.sitem = function
  | ILet bs -> ILet (bindings bs)
  | ILetRec rbs -> ILetRec (rec_bindings rbs)
  | IModule (n, me) -> IModule (name n, mexpr me)
  | IOpen me -> IOpen (mexpr me)
  | IInclude me -> IInclude (mexpr me)
  | IExternal (v, e) -> IExternal (var v, expr e)
  | IExtend l -> IExtend (list name l)

and sitems l = list sitem l
and rec_bindings l = list rec_binding l
and bindings l = list binding l
and branches l = list branch l
and fexprs l = list fexpr l
and exprs l = list expr l
