From osiris.utils Require Import base.
Require Import int syntax.

Coercion EApp : expr >-> Funclass.

(* We use [Goal (trivial e)] to avoid printing notation the notation of [e]
   to stdout when compiling *)

Local Definition trivial {A : Type} := (fun (_ : A) => True).

(* ------------------------------------------------------------------------ *)

(* Decorations. *)

(* A decoration is a string (typically, a snippet extracted out of the
   OCaml source file) that has no semantic meaning. *)
(* When a decoration is present, the underlying AST is not shown. *)

Definition deco {A} (decoration : string) (a : A) :=
  a.

Notation "'ocaml' decoration" := (deco decoration _)
                                   (at level 8, only printing).

(* ------------------------------------------------------------------------ *)

(** Define some derived forms. *)

(* Pairs: pattern, expression, value. *)

Definition PPair p1 p2 :=
  PTuple [p1; p2].

Definition EPair e1 e2 :=
  ETuple [e1; e2].

Definition VPair v1 v2 :=
  VTuple [v1; v2].


(* Options: values. *)

Definition VNone :=
  (VConstant "None").

Definition VSome v :=
  (VData "Some" [ v ]).


(* Lists: patterns, expressions, values. *)

Definition pNil :=
  (PConstant "[]").

Definition pCons p1 p2 :=
  (PData "::" [p1; p2]).

Definition eNil :=
  (EConstant "[]").

Definition eCons e1 e2 :=
  (EData "::" [e1; e2]).

Definition VNil :=
  (VConstant "[]").

Definition VCons v1 v2 :=
  (VData "::" [v1; v2]).

(* Expressions. *)

(* [x]. *)

Definition EVar x :=
  (EPath [x]).

(* [EVar] always unfolds so that tactics inspecting the head of an expression
   see [EPath] rather than the [EVar] alias. *)
Arguments EVar /.

(* [p = e]. *)

Definition Binding1 (p : pat) (e : expr) : list binding :=
  [Binding p e].

(* [let p = e1 in e2]. *)

Definition ELet1 (p : pat) (e1 e2 : expr) :=
  ELet (Binding1 p e1) e2.

(* [let x = e1 in e2]. *)

Definition ELet1Var (x : var) (e1 e2 : expr) :=
  ELet1 (PVar x) e1 e2.

Definition EFun1Var (x : var) (e : expr) :=
  EAnonFun (AnonFun x e).

(* [function bs] is sugar for [fun x -> match x with bs]. *)

(* The variable [x] must not occur micro in [bs]. *)

(* We use a reserved name for [x]. Provided end users do not use such a
   reserved name in their OCaml source code, we can be assured that [x]
   does not occur micro in [bs]. *)

Definition AnonFunction (bs : list branch) : anonfun :=
  let x := "__osiris_anonymous_arg" in
  AnonFun x (EMatch (EVar x) bs).

Definition EFunction (bs : list branch) :=
  EAnonFun (AnonFunction bs).

(* [rec f x = e1]. *)

Definition RecBinding1Var (f x : var) (e1 : expr) : list rec_binding :=
  [RecBinding f (AnonFun x e1)].

(* [rec f 'p = e] *)

Definition RecBinding1Pat f p e :=
  [RecBinding f $ AnonFun p e].

(* [rec f = a] *)

Definition RecBinding1 f a :=
  [RecBinding f a].

(* [let rec f x = e1 in e2]. *)

Definition ELetRec1Var (f x : var) (e1 e2 : expr) :=
  ELetRec (RecBinding1Var f x e1) e2.

(* ------------------------------------------------------------------------ *)

(* A notation scope for [expr], includes arithmetic and booleans.
   The scope itself is declared in [syntax.v], so that the [%E] delimiter is
   available to files that only need to delimit, not to those notations. *)

Notation "- e" := (EIntNeg e) : expr_scope.
Infix "+" := (EBinOp BAdd) : expr_scope.
Infix "-" := (EBinOp BSub) : expr_scope.
Infix "*" := (EBinOp BMul) : expr_scope.
Infix "&&" := EBoolConj : expr_scope.
Infix "||" := EBoolDisj : expr_scope.
Infix "==" := (EBinOp BPhysEq) (at level 90) : expr_scope.
Infix "=" := (EBinOp BEq) : expr_scope.
Infix "<>" := (EBinOp BNe) : expr_scope.
Infix "<" := (EBinOp BLt) : expr_scope.
Infix "<=" := (EBinOp BLe) : expr_scope.
Infix ">" := (EBinOp BGt) : expr_scope.
Infix ">=" := (EBinOp BGe) : expr_scope.

Definition EInt_of_Z Z := EInt Z.

Definition Z_of_EInt e :=
  match e with
  | EInt z => Some z
  | _ => None
  end.

Number Notation expr EInt_of_Z Z_of_EInt : expr_scope.

Open Scope expr_scope.

(* -------------------------------------------------------------------------- *)
(* Environment-related rules. *)

(* Environments are associative lists.
   They are written as:
   - [name1 ~> value1 ;
      ... ;
      namen ~> valuen] if line-breaking is necessary,
   - [name1 ~> value1; ...; namen ~> valuen] otherwise. *)

Notation "n1 ~> v1 ; η" :=
  (@cons (var * val) (n1, v1) η)
    (at level 80, η at level 200, right associativity,
      format "n1  ~>  v1 ;  '//' η").

Notation "n1 ¬> v1" :=
  (@cons (var * val) (n1, v1) nil)
    (at level 80, right associativity,
      format "n1  ¬>  v1").

Notation "x  '≈>'  f" :=
  (RecBinding x f)
    (only printing, at level 100, no associativity).

(* -------------------------------------------------------------------------- *)
(* Paths, tuples and ADTs. *)

Notation "'EPath' x1 '.' .. '.' xm" :=
  (EPath (cons x1 (.. (cons xm nil) ..)))
    (at level 200,
      only printing,
       format "'EPath'  x1 '.' .. '.' xm").

Goal (trivial (EPath ["base"])). Abort.

Goal (trivial
        (EPath ["A"; "B"; "C"; "base"])).
Abort.


(* -------------------------------------------------------------------------- *)
(* Closures, function applications, and function calls. *)

Notation "'Anon' '(' '_' '=>' e ')'" :=
  (AnonFun "__osiris_anonymous_arg" e)
    (at level 0,
      format "'Anon'  '(' '_'  '=>' '/    '  '[hv' e ']' ')'").

Goal (trivial
        (AnonFun "__osiris_anonymous_arg" (EInt 0))).
Abort.

Notation "'Anon' '(' x '=>' e ')'" :=
  (AnonFun x e)
    (at level 0,
      format "'Anon'  '(' x  '=>'  '/    ' '[hv' e ']' ')'").

Goal (trivial (AnonFun "argname" (EInt 1))).
Abort.

Goal (trivial
        (AnonFun "x" (ETuple
                        [EInt 0;EInt 0;EInt 0;EInt 0;EInt 0;EInt 0;
                         EInt 0;EInt 0;EInt 0;EInt 0;EInt 0;EInt 0]))).
Abort.

Goal (trivial (EAnonFun (AnonFun "argname" (EInt 1)))). Abort.

Goal (trivial (EAnonFun (AnonFun "__osiris_anonymous_arg" (EInt 0)))). Abort.

Notation "'_'" := (EPath "__osiris_anonymous_arg") (only printing).

Notation "'EApp' '(' e1 ')' '(' e2 ',' .. ',' en ')'" :=
  (EApp (.. (EApp e1 e2) ..) en)
    (at level 0,
      only printing,
      format "'EApp'  '(' e1 ')'  '/' '(' e2 ','  '/' .. ','  '/' en ')'").

Goal (trivial (EApp (EString "fun") (EString "arg"))). Abort.

Goal (trivial
        (EApp
         (EApp
            (EApp
               (EString "fun") (EString "arg1"))
            (EString "arg2"))
         (EString "arg3"))).
Abort.

(* -------------------------------------------------------------------------- *)
(* Loops and conditionals. *)

Notation "e1 ;; e2" :=
  (ESeq e1 e2)
    (at level 100, e2 at level 200,
      format "'[' '[hv' '[' e1 ']' ;; ']' '/' e2 ']'").

Goal (trivial
        (ESeq
         (EApp (EPath ["f"]) (EPath ["x"]))
         (EAssert (EOpEq (EPath ["x"]) (EInt 2))))).
Abort.

(* -------------------------------------------------------------------------- *)
(* Pattern matching. *)

Notation "'EMatch' '(' x ')' []" :=
  (EMatch x [])
    (at level 0,
      only printing,
      no associativity,
      format "'EMatch'  '(' x ')'  []").

Goal (trivial (EMatch (EPath ["l"]) [])). Abort.

Notation "'EMatch' '(' x ')' 'with' b1 .. bn 'end'" :=
  (EMatch x (cons b1 (.. (cons bn nil) ..)))
    (at level 0,
      only printing,
      no associativity,
      format "'[v' 'EMatch'  '(' x ')'  'with' '//'     '[' b1 '//' ..  '//' bn ']'  '//' 'end' ']'").

Goal (trivial (EMatch (EPath ["l"]) [])). Abort.

Goal (trivial (EMatch (EPath ["l"]) [Branch (CVal PAny) (EInt 1)])). Abort.

Goal (trivial
        (EMatch (EPath ["l"]) [Branch (CVal PAny) (EInt 1); Branch (CVal PAny) 2])).
Abort.

Notation "'|' cpat '->' e" :=
  (Branch cpat e)
    (at level 80,
      only printing,
      format "'|'  cpat  '->'  '[' '/' e ']'").

Goal (trivial (EMatch (EPath ["l"]) [Branch (CVal PAny) (EInt 1)])). Abort.

Goal (trivial
        (EMatch
           (EPath ["l"])
           [Branch (CVal PAny)
              (ESeq
                 (EApp (EPath ["f"]) (EPath ["x"]))
                 (ESeq
                    (EApp (EPath ["f"]) (EPath ["x"]))
                    (ESeq
                       (EApp (EPath ["f"]) (EPath ["x"]))
                       (EAssert (EOpEq (EPath ["x"]) (EInt 2)))
                    )
                 )
              );
            Branch (CExc PAny) 2]
     )).
Abort.

Goal (trivial (Branch (CVal PAny) 2)). Abort.


Close Scope expr_scope.
