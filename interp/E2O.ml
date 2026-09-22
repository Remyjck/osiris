(* Extracted modules *)
open Extracted.BinNums
open Extracted.Datatypes
open Extracted.String
open Extracted.Ascii
(* OCaml's standard library *)
open Stdlib

(** Numbers, lists, products, strings *)

let rec pos = function
  | Coq_xH -> 1
  | Coq_xO p -> 2 * pos p
  | Coq_xI p -> 2 * pos p + 1

let n = function N0 -> 0 | Npos p -> pos p

let z = function
  | Z0 -> 0
  | Zpos p -> pos p
  | Zneg p -> - pos p

let rec nat = function
  | O -> 1
  | S n -> 1 + nat n

let list = List.map

let prod f1 f2 (a1, a2) = (f1 a1, f2 a2)

let char c = Char.chr (n (coq_N_of_ascii c))

let string s =
  String.(concat "" (List.map (make 1) (list char (list_ascii_of_string s))))


(** Syntax types *)

module O = Translatorlib.Syntax
module E = Extracted.Syntax

let var = string
let name = string
let path = list string
let data = string
let field = z

let mut_tag : E.mut_tag -> O.mut_tag = function
  | Mut -> Mut
  | Immut -> Immut

let proph_arg : E.proph_arg -> O.proph_arg = function
  | PArgPath p -> PArgPath (path p)
  | PArgData d -> PArgData (data d)
  | PArgInt i -> PArgInt (z i)

let rec pat : E.pat -> O.pat = function
  | PUnsupported    -> PUnsupported
  | PAny            -> PAny
  | PVar v          -> PVar (var v)
  | PAlias (p, v)   -> PAlias (pat p, var v)
  | POr (p1, p2)    -> POr (pat p1, pat p2)
  | PTuple ps       -> PTuple (list pat ps)
  | PData (d, ps)   -> PData (data d, pats ps)
  | PXData (ph, ps) -> PXData (path ph, pats ps)
  | PRecord fps     -> PRecord (fpats fps)
  | PInline (d, p)  -> PInline (data d, pat p)
  | PArray _        -> PUnsupported
  | PInt i          -> PInt (z i)
  | PChar c         -> PChar (char c)
  | PString s       -> PString (string s)

and cpat : E.cpat -> O.cpat = function
  | CVal p -> CVal (pat p)
  | CExc p -> CExc (pat p)
  | CEff (p1, p2) -> CEff (pat p1, pat p2)
  | COr (cp1, cp2) -> COr (cpat cp1, cpat cp2)

and pats l = list pat l
and fpats l = list (prod field pat) l


let rec coercion : E.coercion -> O.coercion = function
  | CIdentity -> CIdentity
  | CStruct fcs -> CStruct (fcoercions fcs)

and fcoercions l = list (fun (_, c) -> (0, coercion c)) l


let rec expr : E.expr -> O.expr = function
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
  | EBoolNeg e -> EBoolNeg (expr e)
  | EInt i -> EInt (z i)
  | EMaxInt -> EMaxInt
  | EMinInt -> EMinInt
  | EIntNeg e -> EIntNeg (expr e)
  | EIntAdd (e1, e2) -> EIntAdd (expr e1, expr e2)
  | EIntSub (e1, e2) -> EIntSub (expr e1, expr e2)
  | EIntMul (e1, e2) -> EIntMul (expr e1, expr e2)
  | EIntDiv (e1, e2) -> EIntDiv (expr e1, expr e2)
  | EIntMod (e1, e2) -> EIntMod (expr e1, expr e2)
  | EIntLand (e1, e2) -> EIntLand (expr e1, expr e2)
  | EIntLor (e1, e2) -> EIntLor (expr e1, expr e2)
  | EIntLxor (e1, e2) -> EIntLxor (expr e1, expr e2)
  | EIntLnot e -> EIntLnot (expr e)
  | EIntLsl (e1, e2) -> EIntLsl (expr e1, expr e2)
  | EIntLsr (e1, e2) -> EIntLsr (expr e1, expr e2)
  | EIntAsr (e1, e2) -> EIntAsr (expr e1, expr e2)
  | EFloat s -> EFloat (string_of_float s)
  | EChar c -> EChar (char c)
  | EString s -> EString (string s)
  | EOpPhysEq (e1, e2) -> EOpPhysEq (expr e1, expr e2)
  | EOpEq (e1, e2) -> EOpEq (expr e1, expr e2)
  | EOpNe (e1, e2) -> EOpNe (expr e1, expr e2)
  | EOpLt (e1, e2) -> EOpLt (expr e1, expr e2)
  | EOpLe (e1, e2) -> EOpLe (expr e1, expr e2)
  | EOpGt (e1, e2) -> EOpGt (expr e1, expr e2)
  | EOpGe (e1, e2) -> EOpGe (expr e1, expr e2)
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


and fexpr : E.fexpr -> O.fexpr = function
  Fexpr (f, e) -> Fexpr (field f, expr e)

and branch : E.branch -> O.branch = function
  | Branch (cp, e) -> Branch (cpat cp, expr e)

and binding : E.binding -> O.binding = function
  | Binding (p, e) -> Binding (pat p, expr e)

and rec_binding : E.rec_binding -> O.rec_binding = function
  | RecBinding (v, af) -> RecBinding (var v, anonfun af)

and anonfun : E.anonfun -> O.anonfun = function
  | AnonFun (v, e) -> AnonFun (var v, expr e)
  (* not handling the AnonFunction syntactic sugar  *)

and mexpr : E.mexpr -> O.mexpr = function
  | MUnsupported -> MUnsupported
  | MPath p -> MPath (path p)
  | MStruct l -> MStruct (sitems l)
  | MFunctor (v, l) -> MFunctor (var v, sitems l)
  | MCoercion (me, c) -> MCoercion (mexpr me, coercion c)

and sitem : E.sitem -> O.sitem = function
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
