open Printf
let map = List.map
open Syntax
open Rocq

(* This module transforms the Osiris AST into the Rocq AST. *)

(* Cut marks are inserted by invoking [cut] in several places: anonymous
   functions, recursive let bindings, branches of conditional constructs,
   right-hand sides of [let] expressions and sequences. This may help
   improve the readability of the generated definitions and reduce the
   size of the goals that appear while verifying the code in Rocq. *)

(* -------------------------------------------------------------------------- *)

(* Naming cuts after the source code. *)

(* [prefix] is the qualified name of the innermost enclosing binding (or
   created by cuts, so that these definitions carry stable, meaningful
   module). It is used as a base name for the Rocq toplevel definitions
   names. *)

let prefix =
  ref ""

let scoped x =
  if !prefix = "" then x else !prefix ^ "_" ^ x

(* A binding name can be used as a prefix only if it is an ordinary
   identifier; e.g., an operator name such as [+] cannot appear inside
   a Rocq identifier. *)

let is_identifier x =
  x <> "" &&
  String.for_all (fun c ->
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') ||
    ('0' <= c && c <= '9') || c = '_' || c = '\''
  ) x

(* [named x f] evaluates [f()] with the prefix extended with [x]. *)

let named x f =
  if not (is_identifier x) then f() else begin
    let saved = !prefix in
    prefix := scoped x;
    let result = f() in
    prefix := saved;
    result
  end

(* -------------------------------------------------------------------------- *)

(* Variables, module names, data constructors, and field names are
   represented in Rocq as strings. *)

(* Because an OCaml identifier cannot contain a double quote character,
   there is no need for escaping of any kind. *)

let quote s =
  plain (sprintf "\"%s\"" s)

let var =
  quote

let data =
  quote

let field f =
  plain (sprintf "%i%%Z" f)

let path (pi : path) : expression =
  list (map var pi)

let mut_tag (t : Syntax.mut_tag) =
  match t with
  | Mut   -> plain "Mut"
  | Immut -> plain "Immut"

(* -------------------------------------------------------------------------- *)

(* Integer literals. *)

(* We add parentheses in case of a negative literal. *)
let int i =
  let s = string_of_int i in
  if i < 0 then plain ("(" ^ s ^ ")") else plain s

(* -------------------------------------------------------------------------- *)

(* The auxiliary argument of a prophecy resolution. *)

let proph_arg (a : proph_arg) : expression =
  match a with
  | PArgPath pi ->
      c "PArgPath" [ path pi ]
  | PArgData d ->
      c "PArgData" [ data d ]
  | PArgInt i ->
      c "PArgInt" [ int i ]

(* -------------------------------------------------------------------------- *)

(* String literals. *)

(* A Rocq string literal can contain any character below ASCII 128,
   with the exception of the double quote character, which must be
   repeated. It can also contain valid UTF8 characters. *)

(* A scope annotation [%string] could be added, but is unnecessary
   as the library [osiris] makes it the default scope. *)

let is_double_quote =
  function '"' -> true | _ -> false

let repeat_double_quotes s =
  StringExtra.double is_double_quote s

let string s =
  quote (repeat_double_quotes s)

(* -------------------------------------------------------------------------- *)

(* Character literals. *)

(* In Rocq, a character has type [ascii]. A character is internally represented
   as a tuple of eight Boolean values. However, this information need not be
   exposed here. Instead, we use Rocq's character literal notation. A character
   literal is a string literal followed with the scope annotation [%char]. *)

let char (cc: char) =
  let s = String.make 1 cc in
  plain (sprintf "\"%s\"%%char" (repeat_double_quotes s))

(* -------------------------------------------------------------------------- *)

(* Patterns. *)

let rec pat (p : pat) =
  match p with

  | PUnsupported ->
      c "PUnsupported" []

  | PAny ->
      c "PAny" []

  | PVar  x ->
      c "PVar" [ var x ]

  | PAlias (p, x) ->
      c "PAlias" [ pat p; var x ]

  | PTuple ps ->
      clist "PTuple" (map pat ps)

  | PData (d, ps) ->
      c "PData" [ data d ; list (map pat ps) ]

  | PXData (pi, ps) ->
      c "PXData" [ path pi ; list (map pat ps) ]

  | PRecord fps ->
      c "PRecord" [ fpats fps ]

  | PTaggedRecord (d, p) ->
      c "PTaggedRecord" [ data d ; pat p ]

  | PInt i ->
      c "PInt" [ int i ]

  | PChar cc ->
      c "PChar" [ char cc ]

  | PString s ->
     c "PString" [ string s ]

  | POr (p1, p2) ->
     c "POr" [ pat p1; pat p2 ]

and cpat (cp : cpat) =
  match cp with

  | CVal p ->
     c "CVal" [ pat p ]

  | CExc p ->
     c "CExc" [ pat p ]

  | CEff (p1, p2) ->
     c "CEff" [ pat p1; pat p2 ]

  | COr (p1, p2) ->
     c "COr" [ cpat p1; cpat p2 ]

and fpats fps =
  list (map fpat fps)

and fpat (f, p) =
  pair (field f) (pat p)

(* -------------------------------------------------------------------------- *)

(* Coercions. *)

let rec coercion = function
  | CIdentity ->
      c "CIdentity" []
  | CStruct fcs ->
      c "CStruct" [ fcoercions fcs ]

and fcoercions fcs =
  list (map fcoercion fcs)

and fcoercion (f, co) =
  pair (field f) (coercion co)

(* -------------------------------------------------------------------------- *)

(* Expressions. *)

let rec expr (e : expr) =
  match e with

  | EDecorate (snippet, e) ->
      c "deco" [ string snippet; expr e ]

  | EUnsupported ->
      c "EUnsupported" []

  | EPath pi ->
      c "EPath" [path pi]

  | EAnonFun a ->
      c "EAnonFun" [ cut (scoped "fun") (anonfun a) ]

  | EApp (e1, e2) ->
      c "EApp" [ expr e1; expr e2 ]

  | ETuple es ->
      clist "ETuple" (exprs es)

  | EData (d, e) ->
      c "EData" [ data d ; list (exprs e) ]

  | EXData (pi, e) ->
      c "EXData" [ path pi ; list (exprs e) ]

  | ERecord (t, es) ->
      c "ERecord" [ mut_tag t; list (exprs es) ]

  | ERecordUpdate (e, fes) ->
      c "ERecordUpdate" [ expr e; fexprs fes ]

  | ERecordAccess (e, f) ->
      c "ERecordAccess" [ expr e; field f ]

  | ERecordSet (e1, f, e2) ->
      c "ERecordSet" [ expr e1; field f; expr e2 ]

  | EAtomicLoc (e, f) ->
      c "EAtomicLoc" [ expr e; field f ]

  | EInline (d, t, es) ->
      c "EInline" [ data d; mut_tag t; list (exprs es) ]

  | EArrayLength e ->
      c "EArrayLength" [ expr e ]

  | EArrayGet (e1, e2) ->
      c "EArrayGet" [ expr e1; expr e2 ]

  | EArraySet (e1, e2, e3) ->
      c "EArraySet" [ expr e1; expr e2; expr e3 ]

  | EArrayMake (e1, e2) ->
      c "EArrayMake" [ expr e1; expr e2 ]

  | EFreeze e ->
      c "EFreeze" [ expr e ]

  | EUnfreeze e ->
      c "EUnfreeze" [ expr e ]

  | EArrayLit es ->
      c "EArrayLit" [ list (map expr es) ]

  | EBoolConj (e1, e2) ->
      c "EBoolConj" [ expr e1; expr e2 ]

  | EBoolDisj (e1, e2) ->
      c "EBoolDisj" [ expr e1; expr e2 ]

  | EBoolNeg e ->
      c "EBoolNeg" [ expr e ]

  | EInt i ->
      c "EInt" [ int i ]

  | EMaxInt ->
      c "EMaxInt" []

  | EMinInt ->
      c "EMinInt" []

  | EIntNeg e ->
      c "EIntNeg" [ expr e ]

  | EIntAdd (e1, e2) ->
      c "EIntAdd" [ expr e1; expr e2 ]

  | EIntSub (e1, e2) ->
      c "EIntSub" [ expr e1; expr e2 ]

  | EIntMul (e1, e2) ->
      c "EIntMul" [ expr e1; expr e2 ]

  | EIntDiv (e1, e2) ->
      c "EIntDiv" [ expr e1; expr e2 ]

  | EIntMod (e1, e2) ->
      c "EIntMod" [ expr e1; expr e2 ]

  | EIntLand (e1, e2) ->
      c "EIntLand" [expr e1; expr e2]

  | EIntLor  (e1, e2) ->
      c "EIntLor" [expr e1; expr e2]

  | EIntLxor (e1, e2) ->
      c "EIntLxor" [expr e1; expr e2]

  | EIntLnot e ->
      c "EIntLnot" [expr e]

  | EIntLsl  (e1, e2) ->
      c "EIntLsl" [expr e1; expr e2]

  | EIntLsr  (e1, e2) ->
      c "EIntLsr" [expr e1; expr e2]

  | EIntAsr  (e1, e2) ->
      c "EIntAsr" [expr e1; expr e2]

  | EFloat f ->
      c "EFloat" [ plain (sprintf "(%s)%%float" f)]

  | EChar cc ->
      c "EChar" [char cc]

  | EString s ->
      c "EString" [string s]

  | EOpPhysEq (e1, e2) ->
      c "EOpPhysEq" [ expr e1; expr e2 ]

  | EOpEq (e1, e2) ->
      c "EOpEq" [ expr e1; expr e2 ]

  | EOpNe (e1, e2) ->
      c "EOpNe" [ expr e1; expr e2 ]

  | EOpLt (e1, e2) ->
      c "EOpLt" [ expr e1; expr e2 ]

  | EOpLe (e1, e2) ->
      c "EOpLe" [ expr e1; expr e2 ]

  | EOpGt (e1, e2) ->
      c "EOpGt" [ expr e1; expr e2 ]

  | EOpGe (e1, e2) ->
      c "EOpGe" [ expr e1; expr e2 ]

  | ELet (bs, e) ->
      c "ELet" [ bindings bs; cut_expr e ]

  | ELetRec (rbs, e) ->
      c "ELetRec" [ rec_bindings rbs; cut_expr e ]

  | ESeq (e1, e2) ->
      c "ESeq" [ expr e1; cut_expr e2 ]

  | EIfThen (e, e1) ->
      c "EIfThen" [ expr e; cut_expr e1 ]

  | EIfThenElse (e, e1, e2) ->
      c "EIfThenElse" [ expr e; cut_expr e1; cut_expr e2 ]

  | EMatch (e, bs) ->
      c "EMatch" [ expr e; branches bs ]

  | EShallowMatch (e, bs) ->
      c "EShallowMatch" [ expr e; branches bs ]

  | ERaise e ->
     c "ERaise" [ expr e ]

  | EPerform e ->
     c "EPerform" [ expr e ]

  | EContinue (e1, e2) ->
     c "EContinue" [ expr e1; expr e2 ]

  | EDiscontinue (e1, e2) ->
     c "EDiscontinue" [ expr e1; expr e2 ]

  | EWhile (e1, e2) ->
      c "EWhile" [ expr e1; cut_expr e2 ]

  | EFor (x, e1, e2, e3) ->
      c "EFor" [ var x; expr e1; expr e2; cut_expr e3 ]

  | EAssertFalse ->
      c "EAssertFalse" []

  | EAssert e ->
      c "EAssert" [ expr e ]

  | ELetSitem (s, e) ->
      c "ELetSitem" [ structure_item s; cut_expr e ]

  | ERef e ->
      c "ERef" [ expr e ]

  | ELoad e ->
      c "ELoad" [ expr e ]

  | EStore (e1, e2) ->
      c "EStore" [ expr e1; expr e2 ]

  | EFieldLoad e ->
      c "EFieldLoad" [ expr e ]

  | EExchange (e1, e2) ->
      c "EExchange" [ expr e1; expr e2 ]

  | ECAS (e1, e2, e3) ->
      c "ECAS" [ expr e1; expr e2; expr e3 ]

  | EFAA (e1, e2) ->
      c "EFAA" [ expr e1; expr e2 ]

  | ENewProph ->
      c "ENewProph" []

  | EResolve (e, pi, a) ->
      c "EResolve" [ expr e; path pi; proph_arg a ]

  | EIgnore e ->
      c "EIgnore" [ expr e ]

  | EFork (e1, e2) ->
      c "EFork" [ expr e1; expr e2 ]

  | EJoin e ->
      c "EJoin" [ expr e ]

(* If [e] carries a decoration, then [cut_expr e] takes care of
   cutting below the decoration so the decoration hides the cut in the
   eyes of the end user. (If we cut above the decoration then the end
   user would see the Rocq toplevel definition created by the cut, and
   would not see the decoration until they unfold this definition.) *)

and cut_expr e =
  match e with
  | EDecorate (snippet, e) ->
      c "deco" [ string snippet; cut_expr e ]
  | e ->
      cut (scoped "exp") (expr e)

and exprs es =
  map expr es

and anonfun = function
  | AnonFun (x, e) ->
      c "AnonFun" [ var x; expr e ]
  | AnonFunction bs ->
      c "AnonFunction" [ branches bs ]

and branch = function
  | Branch (cp, e) ->
      c "Branch" [ cpat cp; expr e ]

and branches (bs : branches) =
  cut (scoped "branches") (list (map branch bs))

and fexpr = function
  | Fexpr (f, e) ->
    c "Fexpr" [ field f; expr e ]

and fexprs (fes : fexprs) =
  list (map fexpr fes)


(* -------------------------------------------------------------------------- *)

(* Bindings. *)

and binding = function
  | Binding ((PVar x | PAlias (_, x)) as p, e) when is_identifier x ->
      named x (fun () -> c "Binding" [ pat p; named_rhs e ])
  | Binding (p, e) ->
      c "Binding" [ pat p; expr e ]

(* The right-hand side of a named binding. If it is an anonymous function
   (possibly under a decoration), then the cut is named after the binding
   itself, so that a source function [let set ...] yields a Rocq toplevel
   definition [__set]. *)

and named_rhs e =
  match e with
  | EDecorate (snippet, e) ->
      c "deco" [ string snippet; named_rhs e ]
  | EAnonFun a ->
      c "EAnonFun" [ cut !prefix (anonfun a) ]
  | e ->
      expr e

and rec_binding = function
  | RecBinding (x, a) ->
      named x (fun () -> c "RecBinding" [ var x; anonfun a ])

and bindings (bs : bindings) =
  list (map binding bs)

and rec_bindings (rbs : rec_bindings) =
  let base =
    match rbs with
    | RecBinding (x, _) :: _ when is_identifier x -> scoped x ^ "_bindings"
    | _ -> scoped "bindings"
  in
  cut base (list (map rec_binding rbs))

(* -------------------------------------------------------------------------- *)

(* Structure items. *)

and structure_item (item : sitem) =
  match item with

  | ILet bs ->
     c "ILet" [ bindings bs ]

  | ILetRec rbs ->
     c "ILetRec" [ rec_bindings rbs ]

  | IModule (m, me) ->
      c "IModule" [ var m; named m (fun () -> mexpr me) ]

  | IOpen me ->
      c "IOpen" [ mexpr me ]

  | IInclude me ->
      c "IInclude" [ mexpr me ]

  | IExternal (x, e) ->
      c "IExternal" [ var x; expr e ]

  | IExtend cs ->
      clist "IExtend" (map var cs)

and structure_items items =
  map structure_item items

(* -------------------------------------------------------------------------- *)

(* Module expressions. *)

and mexpr (me : mexpr) =
  match me with

  | MUnsupported ->
      c "MUnsupported" []

  | MPath pi ->
      c "MPath" [path pi]

  | MStruct items ->
      clist "MStruct" (structure_items items)

  | MFunctor (x, items) ->
      c "MFunctor" ([ var x ] @ structure_items items)

  | MCoercion (me, co) ->
      c "MCoercion" [ mexpr me; coercion co ]

(* -------------------------------------------------------------------------- *)

(* The main function. *)

let module_expression me =
  prefix := "";
  mexpr me
