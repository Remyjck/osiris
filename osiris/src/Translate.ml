open Printf
let map = List.map

(* ocaml-compiler-libs: *)
open Longident
  (* https://github.com/ocaml/ocaml/blob/trunk/parsing/longident.mli *)
open Asttypes
  (* https://github.com/ocaml/ocaml/blob/trunk/parsing/asttypes.mli *)
open Primitive
  (* https://github.com/ocaml/ocaml/blob/trunk/typing/primitive.mli *)
open Types
  (* https://github.com/ocaml/ocaml/blob/trunk/typing/types.mli *)
open Path
  (* https://github.com/ocaml/ocaml/blob/trunk/typing/path.mli *)
open Typedtree
  (* https://github.com/ocaml/ocaml/blob/trunk/typing/typedtree.mli *)
open Data_types
  (* https://github.com/ocaml/ocaml/blob/trunk/typing/data_types.mli *)

(* Osiris: *)
open Syntax

module Make (M :  sig
  val warnings : bool
  val debug : ('a, out_channel, unit) format -> 'a
end) = struct
open M

(* -------------------------------------------------------------------------- *)

(* Printers (for debugging only). *)

let show_longident (i : Longident.t) =
    Longident.flatten i |>
    List.fold_left (fun acc s -> acc ^ "." ^ s) String.empty

let rec show_path (p : Path.t) =
  match p with
  | Pident i ->
      (* A variable or module identifier. *)
      Ident.name i
  | Pdot (p, x) ->
      (* A field selection in a structure. *)
      sprintf "%s.%s" (show_path p) x
  | Papply (p1, p2) ->
      (* A functor application. *)
      sprintf "%s(%s)" (show_path p1) (show_path p2)
  | Pextra_ty (p, Pcstr_ty data) ->
      (* This path names the inline record carried by the data constructor
         [data] of the algebraic data type [p]. See [path.mli]. *)
      (* OCaml has no agreed-upon surface syntax for this concept. *)
      sprintf "%s/%s{}" (show_path p) data
  | Pextra_ty (p, Pext_ty) ->
      (* This path names the inline record carried by the extensible data
         constructor [p]. See [path.mli]. *)
      (* OCaml has no agreed-upon surface syntax for this concept. *)
      sprintf "%s{}" (show_path p)

(* -------------------------------------------------------------------------- *)

(* Warnings. *)

let prerr_loc (loc : Location.t) =
  Location.print_loc Format.err_formatter loc;
  Format.pp_print_flush Format.err_formatter ()

let unsupported loc construct v =
  if warnings then begin
    prerr_loc loc;
    eprintf ":\n";
    eprintf "Warning: unsupported construct (%s).\n" construct;
    flush stderr
  end;
  v

let eunsupported loc construct : expr =
  unsupported loc construct EUnsupported

let punsupported loc construct : pat =
  unsupported loc construct PUnsupported

let ounsupported loc construct : _ option =
  unsupported loc construct None

let munsupported loc construct : mexpr =
  unsupported loc construct MUnsupported

exception Unsupported

(* -------------------------------------------------------------------------- *)

(* Recognizing global identifiers and paths. *)

exception Unrecognized

(* [recognize_global_ident id] checks that [id] is a global identifier, and
   if so, returns its name. Otherwise, [Unrecognized] is raised. *)

let recognize_global_ident (id : Ident.t) : string =
  if Ident.global id then
    Ident.name id
  else
    raise Unrecognized

(* [recognize_global_path path] checks that [path] is rooted at a global
   identifier, and if so, converts this path to a list of strings, where
   the first element of the list represents the root of the path.
   Otherwise, [Unrecognized] is raised. *)

let rec recognize_global_path path : string list =
  match path with
  | Pident id ->
      [recognize_global_ident id]
  | Pdot (parent, field) ->
      recognize_global_path parent @ [field]
  | Papply _
  | Pextra_ty _ ->
      raise Unrecognized

(* Recognizing the Boolean expression [false]. *)

(* This code is a bit fragile, as the user might find a way of redefining
   the identifier [false] to mean something else. The risk seems low. *)

let is_false (e : expression) : bool =
  match e.exp_desc with
  | Texp_construct ({ txt = Lident "false"; _}, _, []) ->
      true
  | _ ->
      false

(* -------------------------------------------------------------------------- *)

(* If the source file is available, then we insert decorations into the
   generated AST. *)

module Run (X : sig val source : string option end) = struct

(* A source code location (a pair of positions) is converted to a string.
   This can fail if [source] is [None], which means that [--decorate] is
   off or that the soure file could not be found. It can also fail if
   [extract] fails, which can happen if the source code positions are
   out of range. *)

(* [2k+3] is the maximum length of a snippet. *)

let k =
  15

let return =
  Option.some

let (let*) =
  Option.bind

let convert (loc : Location.t) : string option =
  let* source = X.source in
  let startp, endp = Location.(loc.loc_start, loc.loc_end) in
  let* snippet = ErrorReports.(extract source (startp, endp)) in
  return ErrorReports.(snippet |> sanitize |> compress |> shorten k)

(* Decorating an expression with a location. *)

let decorate (loc : Location.t) (e : expr) : expr =
  match convert loc with
  | Some snippet ->
      EDecorate (snippet, e)
  | None ->
      (* If we are unable to produce a decoration, forget about it. *)
      e

(* -------------------------------------------------------------------------- *)

(* Stripping off a location. *)

let txt (x : 'a loc) : 'a =
  x.txt

(* -------------------------------------------------------------------------- *)

(* Long identifiers are preserved when they designate a value or module. *)

let translate_longident (i : Longident.t) : path = Longident.flatten i

let debug_ident kind path id =
  (* [id] is the long identifier that appears in the source code.
     [path] is the corresponding resolved path. *)
  debug "    %s\n" kind;
  debug "      id = %s\n" (show_longident id);
  debug "      path = %s\n" (show_path path)

let translate_exp_ident path id : path =
  debug_ident "Texp_ident" path id;
  (* For the moment, we ignore [path] and keep [id]. However, [path]
     could be used to identify references to the OCaml standard library. *)
  translate_longident id

let translate_mod_ident path id : path =
  debug_ident "Tmod_ident" path id;
  translate_longident id

(* Long identifiers are unqualified (turned into short identifiers) when
   they designate data constructors or record fields. *)

let translate_data_constructor id constructor_desc : data =
  (* [id] is the data constructor that appears in the source code,
     possibly a long identifier. *)
  (* [constructor_desc] is the constructor description constructed by
     the OCaml type-checker. *)
  assert (Longident.last (txt id) = constructor_desc.cstr_name);
  constructor_desc.cstr_name

let translate_record_field id label_desc : field =
  (* [id] is the record field that appears in the source code,
     possibly a long identifier. *)
  (* [label_desc] is the field description constructed by the OCaml
     type-checker. *)
  assert (Longident.last (txt id) = label_desc.lbl_name);
  label_desc.lbl_pos

(* -------------------------------------------------------------------------- *)

(* Constants. *)

(* We may wish to check that integer constants are definitely representable
   (i.e., fit in 31 bits). Otherwise, the code would be non-portable and
   non-verifiable. TODO *)

let translate_exp_constant loc (c : constant) : expr =
  match c with
  | Const_int i ->
      EInt i
  | Const_char c ->
      EChar c
  | Const_string (s, _, _) ->
      EString s
  | Const_float f ->
     (* Remove the decimal-point if there is no fractional part. *)
     let f = Float.of_string f in
     EFloat (sprintf "%g" f)
  | Const_int32 _ ->
      eunsupported loc "32-bit integer literal"
  | Const_int64 _ ->
      eunsupported loc "64-bit integer literal"
  | Const_nativeint _ ->
      eunsupported loc "native integer literal"

(* -------------------------------------------------------------------------- *)

(* The [@resolve p v] annotation, which resolves the prophecy [p] with the
   pair of the annotated expression's result and [v]. *)
let resolve_attribute = "resolve"

(* [translate_proph loc e] translates the first argument of a [@resolve]
   annotation, which names the prophecy. It must be an identifier: a
   prophecy is looked up in the environment, and nothing else may be
   evaluated at a resolution. *)

let translate_proph loc (e : Parsetree.expression) : path =
  let open Parsetree in
  match e.pexp_desc with
  | Pexp_ident id ->
      translate_longident (txt id)
  | _ ->
      unsupported loc
        "this prophecy in [@resolve]: it must be an identifier" []

(* [translate_proph_arg loc e] translates the second argument of a
   [@resolve] annotation, the auxiliary value the prophecy is resolved
   with. It must be an identifier or a constant, for the same reason. *)

let translate_proph_arg loc (e : Parsetree.expression) : proph_arg =
  let open Parsetree in
  match e.pexp_desc with
  | Pexp_ident id ->
      PArgPath (translate_longident (txt id))
  | Pexp_construct (id, None) ->
      (* [()], [true], [false], and any other constant data constructor. *)
      PArgData (Longident.last (txt id))
  | Pexp_constant { pconst_desc = Pconst_integer (s, None); _ } ->
      PArgInt (int_of_string s)
  | _ ->
      unsupported loc
        "this argument of [@resolve]: it must be an identifier or a constant"
        (PArgData "()")

(* [names_value m f path] tests whether [path] designates the value [f] of a
   module named [m]. Dune wraps a library's modules, so [m] may be reached
   through a generated prefix, as in [SomeLibrary__Proph]; we accept that, and
   we accept a qualifying prefix such as [Stdlib]. *)

let names_value m f path =
  match List.rev path with
  | f' :: m' :: _ ->
      f' = f && (m' = m || Filename.check_suffix m' ("__" ^ m))
  | _ ->
      false

(* [recognize_resolve attrs] returns the prophecy and the tag of the
   [@resolve] annotation carried by [attrs], if there is one. *)

let recognize_resolve (attrs : Parsetree.attributes) : (path * proph_arg) option =
  let open Parsetree in
  match
    List.find_opt (fun a -> txt a.attr_name = resolve_attribute) attrs
  with
  | None ->
      None
  | Some attr ->
      let loc = attr.attr_loc in
      begin match attr.attr_payload with
      | PStr [ { pstr_desc = Pstr_eval (
            { pexp_desc = Pexp_apply (p, [ (Nolabel, v) ]); _ }, _
          ); _ } ] ->
          Some (translate_proph loc p, translate_proph_arg loc v)
      | _ ->
          unsupported loc
            "this [@resolve] annotation: it must be written [@resolve p v]"
            (Some ([], PArgData "()"))
      end

(* -------------------------------------------------------------------------- *)

let translate_pat_constant loc (c : constant) : pat =
  match c with
  | Const_int i ->
      PInt i
  | Const_char c ->
      PChar c
  | Const_string (s, _, _) ->
      PString s
  | Const_float _ ->
      punsupported loc "floating-point literal"
  | Const_int32 _ ->
      punsupported loc "32-bit integer literal"
  | Const_int64 _ ->
      punsupported loc "64-bit integer literal"
  | Const_nativeint _ ->
      punsupported loc "native integer literal"

(* -------------------------------------------------------------------------- *)

(* Recognizing a constructor in an extensible algebraic data type,
   as opposed to a constructor in an ordinary algebraic data type. *)

(* See [types.mli]. *)

let is_extensible (constructor_desc : Data_types.constructor_description) =
  match constructor_desc.Data_types.cstr_tag with
  | Data_types.Cstr_constant _
  | Data_types.Cstr_block _
  | Data_types.Cstr_unboxed ->
      false
  | Data_types.Cstr_extension _ ->
      true

let is_inline (constructor_desc : Data_types.constructor_description) =
  match constructor_desc.cstr_inlined with
  | None -> false
  | Some _ -> true

(* -------------------------------------------------------------------------- *)

(* Patterns, also known as value patterns. *)

(* The type [pattern] is a synonym for [value general_pattern]. *)

let rec translate_pat (pat: pattern) : pat =
  let loc = pat.pat_loc in
  match pat.pat_desc with

  | Tpat_any ->
      PAny

  | Tpat_var (_, x, _) ->
      PVar (txt x)

  | Tpat_alias (pat, _, x, _, _) ->
      (* A type-constrained binding [let (x : t) = ...] is elaborated by the
         OCaml typechecker as [Tpat_alias (Tpat_any, x)]. An alias of a
         wildcard is just a variable, so we simplify it to [PVar]. *)
      begin match translate_pat pat with
      | PAny -> PVar (txt x)
      | pat  -> PAlias (pat, txt x)
      end

  | Tpat_constant c ->
      translate_pat_constant loc c

  | Tpat_tuple pats ->
      PTuple (translate_pats (snd @@ List.split pats))

  | Tpat_construct (id, constructor_desc, pats, _optional_type_annotation) ->
      (* An OCaml data constructor application is always translated as an
         application of the data constructor to a tuple of its arguments. *)
    let data = translate_data_constructor id constructor_desc in
    if is_inline constructor_desc then
      (* An inline-record constructor pattern has exactly one argument:
         a pattern for the record itself. *)
      match pats with
      | [ p ] -> PInline (data, translate_pat p)
      | _ -> assert false
    else
      let tuple = translate_pats pats in
      if is_extensible constructor_desc then
        PXData (translate_longident (txt id), tuple)
      else
        PData (data, tuple)

  | Tpat_variant _ ->
      punsupported loc "polymorphic variant pattern"

  | Tpat_record (fields, _closed_flag) ->
      PRecord (translate_field_patterns fields)

  | Tpat_array _ ->
      punsupported loc "array pattern"

  | Tpat_lazy _ ->
      punsupported loc "lazy pattern"

  | Tpat_or (pat1, pat2, _) ->
     POr (translate_pat pat1, translate_pat pat2)

and translate_pats (pats : value general_pattern list) : pats =
  map translate_pat pats

and translate_field_patterns fields : fpats =
  map translate_field_pattern fields

and translate_field_pattern (i, label_desc, pat) : field * pat =
  translate_record_field i label_desc,
  translate_pat pat

(* -------------------------------------------------------------------------- *)

(* Computation patterns distinguish normal termination and exceptions. *)

let rec translate_computation_pattern (pat : computation general_pattern) : cpat =
  match pat.pat_desc with
  | Tpat_value p ->
     (* We need a coercion because the type of Tpat_value is private. *)
     CVal (translate_pat (p :> pattern))

  | Tpat_exception p ->
     CExc (translate_pat p)

  | Tpat_or (p1, p2, _) ->
     let cp1 = translate_computation_pattern p1 in
     let cp2 = translate_computation_pattern p2 in
     COr (cp1, cp2)

(* -------------------------------------------------------------------------- *)

(* N-ary function applications are encoded in terms of nested binary function
   applications. *)

let apply e1 e2 =
  EApp (e1, e2)

let apply e1 e2s =
  List.fold_left apply e1 e2s

(* -------------------------------------------------------------------------- *)

(* References. *)

(* As in OCaml, a reference, like an [Atomic.t], is a mutable record with a
   single field. *)

let make_ref e =
  ERecord (Mut, [e])

let load_ref e =
  ERecordAccess (e, 0)

let store_ref e1 e2 =
  ERecordSet (e1, 0, e2)

let field_loc_ref e =
  EAtomicLoc (e, 0)

(* -------------------------------------------------------------------------- *)

(* Expressions. *)

let rec translate_expr (e: expression) : expr =
  let loc = e.exp_loc in
  decorate loc @@
  match recognize_resolve e.exp_attributes with
  | Some (p, v) ->
      (* [e [@resolve p v]]. The resolution is fused with [e]: it happens at
         the very step at which [e] produces its result, which is why only an
         atomic operation may carry one. That restriction is enforced by the
         semantics, in [eval], rather than here. *)
      EResolve (translate_expr_desc e, p, v)
  | None ->
      translate_expr_desc e

and translate_expr_desc (e: expression) : expr =
  let loc = e.exp_loc in
  match e.exp_desc with

  | Texp_ident (path, id, _) ->
      EPath (translate_exp_ident path (txt id))

  | Texp_constant c ->
      translate_exp_constant loc c

  | Texp_let (Nonrecursive, vbs, e) ->
      ELet (translate_bindings vbs, translate_expr e)

  | Texp_let (Recursive, vbs, e) ->
      begin try
        ELetRec (translate_rec_bindings vbs, translate_expr e)
      with Unsupported ->
        eunsupported loc "recursive definition of values"
      end

  | Texp_function (params, body) ->
     begin try
       translate_function params body
     with Unsupported ->
       eunsupported loc "labelled or optional argument"
     end

  | Texp_apply (e, args) ->
      translate_application loc e args

  | Texp_match (e, comp_cases, eff_cases, _partial) ->
      let comp_branches = translate_computation_cases comp_cases in
      let eff_branches = translate_effect_cases eff_cases in
      EMatch (translate_expr e, List.append comp_branches eff_branches)

  | Texp_try (e, exn_cases, eff_cases) ->
      (* We desugar [try e with bs] intro [match e with (v -> v :: bs)] *)
      let val_branch = Branch (CVal (PVar "__osiris_anonymous_arg"), EPath ["__osiris_anonymous_arg"]) in
      let exn_branches = translate_exception_cases exn_cases in
      let eff_branches = translate_effect_cases eff_cases in
      EMatch (translate_expr e, val_branch :: (List.append exn_branches eff_branches))

  | Texp_tuple es ->
      ETuple (translate_exprs (snd @@ List.split es))

  | Texp_construct (id, constructor_desc, es) ->
      (* An OCaml data constructor application is always translated as an
         application of the data constructor to a tuple of its arguments. *)
    let data = translate_data_constructor id constructor_desc in
    if is_inline constructor_desc then
      (* An inline record must only have one argument under the constructor:
         the record. *)
      match es with
      | [ { exp_desc = Texp_record { fields; _ }; _ } ] ->
        let tuple =
          translate_record_field_defs fields |>
          List.map (fun (Fexpr (_, e)) -> e)
        in
        EInline (data, is_mutable_record fields, tuple)
      | _ -> assert false
    else
      let tuple = translate_exprs es in
      if is_extensible constructor_desc then
        EXData (translate_longident (txt id), tuple)
      else
        EData (data, tuple)

  | Texp_variant _ ->
      eunsupported loc "polymorphic variant"

  | Texp_record { fields; representation = _; extended_expression = None } ->
      translate_record_construction fields

  | Texp_record { fields; representation = _; extended_expression = Some e } ->
      translate_record_update e fields

  | Texp_atomic_loc (e, id, label_desc) ->
      (* An atomic field location [[%atomic.loc e.f]] denotes the location
         of the field [f] of the record [e]. Because every record field is
         modeled as a separate location, this location can be returned as a
         first-class value, on which the atomic primitives operate. *)
      let field = translate_record_field id label_desc in
      EAtomicLoc (translate_expr e, field)

  | Texp_field (e, id, label_desc) ->
      let field = translate_record_field id label_desc in
      ERecordAccess (translate_expr e, field)

  | Texp_setfield (e1, id, label_desc, e2) ->
      let field = translate_record_field id label_desc in
      ERecordSet (translate_expr e1, field, translate_expr e2)

  | Texp_array (_, es) ->
      EArrayLit (map translate_expr es)

  | Texp_ifthenelse (e1, e2, Some e3) ->
      EIfThenElse (translate_expr e1, translate_expr e2, translate_expr e3)

  | Texp_ifthenelse (e1, e2, None) ->
      EIfThen (translate_expr e1, translate_expr e2)

  | Texp_sequence (e1, e2) ->
      ESeq (translate_expr e1, translate_expr e2)

  | Texp_while (e, body) ->
      EWhile (translate_expr e, translate_expr body)

  | Texp_for (i, _, e1, e2, Upto, e3) ->
      let i = Ident.name i in
      EFor (i, translate_expr e1, translate_expr e2, translate_expr e3)

  | Texp_for (_i, _, _e1, _e2, Downto, _e3) ->
      eunsupported loc "downto"

  | Texp_send _
  | Texp_new _
  | Texp_instvar _
  | Texp_setinstvar _
  | Texp_override _ ->
      eunsupported loc "objects"

  | Texp_assert (e, _) ->
      if is_false e then
        EAssertFalse
      else
        EAssert (translate_expr e)

  | Texp_lazy _ ->
      eunsupported loc "lazy"

  | Texp_object _ ->
      eunsupported loc "objects"

  | Texp_pack _ ->
      eunsupported loc "first-class modules"

  | Texp_letop _ ->
      eunsupported loc "let operators"

  | Texp_unreachable ->
      (* [assert false] and [.] are both translated to [EAssertFalse]. *)
      EAssertFalse

  | Texp_extension_constructor _ ->
      eunsupported loc "extension constructors"

  | Texp_struct_item (s, e) ->
      match translate_structure_item s with
      | None -> translate_expr e
      | Some s -> ELetSitem (s, translate_expr e)

and translate_exprs es : exprs =
  map translate_expr es

(* -------------------------------------------------------------------------- *)

(* Expressions: function applications. *)

(* We first check whether this is application is recognized as a special
   application. If so, it receives special treatment. Otherwise, it is
   treated as a normal application. *)

and translate_application loc e args =
  try
    translate_special_application loc e args
  with Unrecognized ->
    (* Default case: [e args]. *)
    let e = translate_expr e in
    apply e (translate_labeled_arguments loc args)

(* -------------------------------------------------------------------------- *)

(* Expressions: recognition of special applications, that is,
   applications of primitive operations and
   applications of standard library functions. *)

(* If this application is not recognized, then [Unrecognized] is raised. *)

and translate_special_application loc e args =
  match e.exp_desc with

  | Texp_ident (path, _, { val_kind = Val_prim p; _ }) ->
      let path = recognize_global_path path in
      (* This is an application of a primitive operation (to an
         as-yet-undetermined number of arguments). *)
      translate_primitive_application loc path p args

  | Texp_ident (path, _, _) ->
      let path = recognize_global_path path in
      (* This may be an application of a standard library function. *)
      translate_stdlib_application loc path args

  | _ ->
      raise Unrecognized

(* -------------------------------------------------------------------------- *)

(* Expressions: applications of standard library functions. *)

(* If this application is not recognized, then [Unrecognized] is raised. *)

and translate_stdlib_application loc path args =
  match path, translate_labeled_arguments loc args with
  | ["Stdlib"; "Effect"; "Deep"; "continue"], [e1; e2] ->
      EContinue (e1, e2)
  | ["Stdlib"; "Effect"; "Deep"; "discontinue"], [e1; e2] ->
      EDiscontinue (e1, e2)
  (* [Atomic.t] is a record with one atomic field (see the standard
     library's [atomic.ml]). *)
  | ["Stdlib"; "Atomic"; "make"], [e] ->
      make_ref e
  | ["Stdlib"; "Atomic"; "get"], [e] ->
      load_ref e
  | ["Stdlib"; "Atomic"; "set"], [e1; e2] ->
      store_ref e1 e2
  | ["Stdlib"; "Atomic"; "exchange"], [e1; e2] ->
      EExchange (field_loc_ref e1, e2)
  | ["Stdlib"; "Atomic"; "compare_and_set"], [e1; e2; e3] ->
      ECAS (field_loc_ref e1, e2, e3)
  | ["Stdlib"; "Atomic"; "fetch_and_add"], [e1; e2] ->
      EFAA (field_loc_ref e1, e2)
  (* [Proph.create ()] allocates a prophecy variable. The module's own
     definition is never the one that is verified: it exists so that an
     annotated program still compiles and runs. *)
  | _, [_] when names_value "Proph" "create" path ->
      ENewProph
  | _, _ ->
      raise Unrecognized

(* -------------------------------------------------------------------------- *)

(* Expressions: applications of primitive operations. *)

(* An application of a primitive operation (to a correct number of arguments)
   is recognized as such. If the primitive operation is not recognized or is
   applied to an incorrect number of arguments, then [Unrecognized] is
   raised. *)

(* In the case of Boolean conjunction (&&) and disjunction (||), this is
   crucial in order to obtain the correct (short-circuit) semantics. *)

(* This is otherwise not crucial for soundness, but this should help us by
   allowing us to produce simpler code. *)

(* Some primitive operations are intentionally not recognized as such. They
   are treated as standard library functions. These include %ignore, %incr,
   %decr, %field0 (fst), %field1 (snd). *)

(* Some primitive operations have multiple distinct meanings. For instance,
   [%identity] can represent [Obj.magic], [Char.code], or unary integer [+].
   As another example, [%field0] can represents [fst] on pairs or [!] on
   references. We must distinguish between these meanings. To do so, we use
   both the OCaml identifier and the primitive operation. This is not 100%
   bulletproof. *)

and translate_primitive_application loc path p args =
  match path, p.prim_name, translate_labeled_arguments loc args with

  (* Erasing applications of [Obj.magic] is an experimental feature. It takes
     careful consideration and arguments to ascertain that this is sound. *)
  | ["Stdlib"; "Obj"; "magic"], "%identity", [e] ->
      e

  (* Integers. *)

  | ["Stdlib"; "~+"], "%identity", [e] ->
      e
  | _, "%negint", [e] ->
      EIntNeg e
  | _, "%addint", [e1; e2] ->
      EIntAdd (e1, e2)
  | _, "%subint", [e1; e2] ->
      EIntSub (e1, e2)
  | _, "%mulint", [e1; e2] ->
      EIntMul (e1, e2)
  | _, "%divint", [e1; e2] ->
      EIntDiv (e1, e2)
  | _, "%modint", [e1; e2] ->
      EIntMod (e1, e2)
  | _, "%predint", [e] ->
      EIntSub (e, EInt 1)
  | _, "%succint", [e] ->
      EIntAdd (e, EInt 1)
  | _, "%andint", [e1; e2] ->
      EIntLand (e1, e2)
  | _, "%orint", [e1; e2] ->
      EIntLor  (e1, e2)
  | _, "%xorint", [e1; e2] ->
      EIntLxor (e1, e2)
  | _, "%lslint", [e1; e2] ->
      EIntLsl  (e1, e2)
  | _, "%lsrint", [e1; e2] ->
      EIntLsr  (e1, e2)
  | _, "%asrint", [e1; e2] ->
      EIntAsr  (e1, e2)

  (* Structural equality and comparison. *)

  | _, "%equal", [e1; e2] ->
      EOpEq (e1, e2)
  | _, "%notequal", [e1; e2] ->
      EOpNe (e1, e2)
  | _, "%lessthan", [e1; e2] ->
      EOpLt (e1, e2)
  | _, "%greaterthan", [e1; e2] ->
      EOpGt (e1, e2)
  | _, "%lessequal", [e1; e2] ->
      EOpLe (e1, e2)
  | _, "%greaterequal", [e1; e2] ->
      EOpGe (e1, e2)

  (* Physical equality. *)

  | _, "%eq", [e1; e2] ->
      EOpPhysEq (e1, e2)
  | _, "%noteq", [e1; e2] ->
      EBoolNeg (EOpPhysEq (e1, e2))

  (* Booleans. *)

  | _, "%boolnot", [e] ->
      EBoolNeg e
  | _, "%sequand", [e1; e2] ->
      EBoolConj (e1, e2)
  | _, "%sequor", [e1; e2] ->
      EBoolDisj (e1, e2)

  (* Functions. *)

  | _, "%apply", [e1; e2] ->
      (* We assume that [e1] is not itself a primitive operation. *)
      apply e1 [e2]
  | _, "%revapply", [e1; e2] ->
      (* We assume that [e2] is not itself a primitive operation. *)
      apply e2 [e1]

  (* References. *)

  | ["Stdlib"; "ref"], "%makemutable", [e] ->
      make_ref e
  | ["Stdlib"; "!"], "%field0", [e] ->
      load_ref e
  | ["Stdlib"; ":="], "%setfield0", [e1; e2] ->
      store_ref e1 e2

  (* Atomic references. *)
  | ["Stdlib"; "Atomic"; "ignore"], "%ignore", [e] ->
      EIgnore e

  (* Atomic field locations. These primitives are recognized regardless of
     the path through which they are named, e.g. [Atomic.Loc.get] in the
     standard library or a local alias. Their first argument is an atomic
     location, that is, a value of the form [VLoc l]. *)
  | _, "%atomic_load_loc", [e] ->
      ELoad e
  | _, "%atomic_exchange_loc", [e1; e2] ->
      EExchange (e1, e2)
  | _, "%atomic_cas_loc", [e1; e2; e3] ->
      ECAS (e1, e2, e3)
  | _, "%atomic_fetch_add_loc", [e1; e2] ->
      EFAA (e1, e2)

  (* Arrays. *)

  | ["Stdlib"; "Array"; "length"], "%array_length", [e] ->
      EArrayLength e
  | ["Stdlib"; "Array"; "get"], "%array_safe_get", [e1; e2] ->
      EArrayGet (e1, e2)
  | ["Stdlib"; "Array"; "set"], "%array_safe_set", [e1; e2; e3] ->
      EArraySet (e1, e2, e3)
  (* We currently do not differentiate between safe and
     unsafe array primitives. *)
  | ["Stdlib"; "Array"; "unsafe_get"], "%array_unsafe_get", [e1; e2] ->
      EArrayGet (e1, e2)
  | ["Stdlib"; "Array"; "unsafe_set"], "%array_unsafe_set", [e1; e2; e3] ->
      EArraySet (e1, e2, e3)
  | ["Stdlib"; "Array"; "make"], "caml_array_make", [e1; e2] ->
      EArrayMake (e1, e2)

  (* Exceptions. *)

  | ["Stdlib"; "raise"], "%raise", [e] ->
      ERaise e

  (* Effects. *)

  | ["Stdlib"; "Effect"; "perform"], "%perform", [e] ->
      EPerform e

  | _, _, _ ->
      raise Unrecognized

(* -------------------------------------------------------------------------- *)

(* Expressions: anonymous functions. *)

(* We translate a function parameter to a hole which expects
   an expression corresponding to the body of a function. *)

and translate_function_param (param : function_param) e : expr =
  match param.fp_arg_label with
  | Labelled _ | Optional _ -> raise Unsupported
  | Nolabel ->
     match param.fp_kind with
     | Tparam_optional_default (_, _) -> raise Unsupported
     | Tparam_pat p ->
        match translate_pat p with
        (* We recognize the special case of [fun x -> e]. In this case
           we can use [AnonFun], a primitive form in the Osiris AST. *)
        | PVar x ->
           EAnonFun (AnonFun (x, e))
        | p ->
           EAnonFun (AnonFunction [Branch (CVal p, e)])

and translate_function_params params e : expr =
  match params with
  | [] -> e
  | param :: params ->
     translate_function_param param (translate_function_params params e)

and translate_function_body : function_body -> expr = function
  | Tfunction_body e -> translate_expr e
  | Tfunction_cases { cases; partial = _; param = _; loc = _; exp_extra = _; attributes = _ } ->
     EAnonFun (AnonFunction (translate_value_cases cases))

and translate_function params body : expr =
  (translate_function_params params (translate_function_body body))


(* -------------------------------------------------------------------------- *)

(* Expressions: actual arguments in applications. *)

and translate_labeled_arguments loc args =
  map (translate_labeled_argument loc) args

and translate_labeled_argument loc arg : expr =
  match arg with
  | Nolabel, Arg e ->
      (* An ordinary unlabeled argument. *)
      translate_expr e
  | _, _ ->
      (* A labeled argument, or an unlabeled argument that participates
         in a labeled function application. *)
      eunsupported loc "labeled arguments"

(* -------------------------------------------------------------------------- *)

(* Cases in [fun], [match], [try] constructs. *)

and translate_case : type k . (k general_pattern -> cpat) -> k case -> branch =
  fun translate_pat case ->
  let pat = case.c_lhs
  and e = case.c_rhs in
  Branch (
    translate_pat pat,
    match case.c_guard with
    | None ->
        translate_expr e
    | Some guard ->
        let loc = guard.exp_loc in
        eunsupported loc "when clause"
  )

and translate_value_case (case : value case) : branch =
  translate_case (fun p -> CVal (translate_pat p)) case

and translate_value_cases cases =
  map translate_value_case cases

and translate_exception_case (case : value case) : branch =
  translate_case (fun p -> CExc (translate_pat p)) case

and translate_effect_case (case : value case) : branch =
  let cont_pat =
    match case.c_cont with
    | None -> PAny
    | Some k -> PVar (Ident.name k)
  in
  translate_case (fun p -> CEff ((translate_pat p), cont_pat)) case

and translate_exception_cases cases =
  map translate_exception_case cases

and translate_effect_cases cases =
  map translate_effect_case cases

and translate_computation_case (case : computation case) : branch =
  translate_case translate_computation_pattern case

and translate_computation_cases cases =
  map translate_computation_case cases

(* -------------------------------------------------------------------------- *)

(* Non-recursive bindings. *)

and translate_binding (vb : value_binding) : binding =
  Binding (translate_pat vb.vb_pat, translate_expr vb.vb_expr)

and translate_bindings vbs =
  map translate_binding vbs

(* -------------------------------------------------------------------------- *)

(* Recursive bindings. *)

(* In a recursive binding [p = e], the pattern [p] must be a variable,
   and the right-hand side [e] must be an anonymous function.
   OCaml enforces the first restriction.
   We impose the second restriction. *)

and project_EAnonFun (e : expr) : anonfun =
  match e with
  | EDecorate (_, e) ->
      project_EAnonFun e
  | EAnonFun a -> a
  | _ -> raise Unsupported

and project_Tpat_var (pat : value general_pattern) : var =
  match pat.pat_desc with
  | Tpat_var (_, v, _) -> txt v
  (* A type-constrained binding [let rec f : t = ...] is elaborated as
     [Tpat_alias (Tpat_any, f)]; it binds exactly one variable. *)
  | Tpat_alias ({ pat_desc = Tpat_any; _ }, _, v, _, _) -> txt v
  | _ -> assert false

and translate_rec_binding (vb : value_binding) : rec_binding =
  let x = project_Tpat_var vb.vb_pat
  and a = project_EAnonFun (translate_expr vb.vb_expr) in
  RecBinding (x, a)

and translate_rec_bindings vbs =
  map translate_rec_binding vbs

(* -------------------------------------------------------------------------- *)

(* Records. *)

and is_mutable_record fields : mut_tag =
  if
    Array.exists
      (fun (label_desc, _) -> label_desc.lbl_mut = Mutable)
      fields
  then
    Mut
  else
    Immut

and translate_record_construction fields : expr =
  (* Here we rely on the invariant that fields are ordered by the position of the label *)
  ERecord (is_mutable_record fields, translate_record_field_defs fields |> List.map (fun (Fexpr (_, e)) -> e))

and translate_record_update e fields : expr =
  ERecordUpdate (translate_expr e, translate_record_field_defs fields)

and translate_record_field_defs fields : fexprs =
  List.filter_map translate_record_field_def (Array.to_list fields)

and translate_record_field_def (label_desc, label_def) : fexpr option =
  match label_def with
  | Kept _ ->
      (* This field is omitted. This can occur only in a record update
          expression. *)
      None
  | Overridden (id, e) ->
      (* This field is defined. *)
      Some (
        Fexpr (
          translate_record_field id label_desc,
          translate_expr e)
      )

(* -------------------------------------------------------------------------- *)

(* External declarations. *)

(* [translate_primitive_expr prim_name args] translates a primitive operation
   applied to given argument expressions. This is used to build the body
   of external declarations. *)

and translate_primitive_expr prim_name args =
  match prim_name, args with

  (* Integers. *)

  | "%negint", [e] ->
      EIntNeg e
  | "%addint", [e1; e2] ->
      EIntAdd (e1, e2)
  | "%subint", [e1; e2] ->
      EIntSub (e1, e2)
  | "%mulint", [e1; e2] ->
      EIntMul (e1, e2)
  | "%divint", [e1; e2] ->
      EIntDiv (e1, e2)
  | "%modint", [e1; e2] ->
      EIntMod (e1, e2)
  | "%predint", [e] ->
      EIntSub (e, EInt 1)
  | "%succint", [e] ->
      EIntAdd (e, EInt 1)
  | "%andint", [e1; e2] ->
      EIntLand (e1, e2)
  | "%orint", [e1; e2] ->
      EIntLor (e1, e2)
  | "%xorint", [e1; e2] ->
      EIntLxor (e1, e2)
  | "%lslint", [e1; e2] ->
      EIntLsl (e1, e2)
  | "%lsrint", [e1; e2] ->
      EIntLsr (e1, e2)
  | "%asrint", [e1; e2] ->
      EIntAsr (e1, e2)

  (* Structural equality and comparison. *)

  | "%equal", [e1; e2] ->
      EOpEq (e1, e2)
  | "%notequal", [e1; e2] ->
      EOpNe (e1, e2)
  | "%lessthan", [e1; e2] ->
      EOpLt (e1, e2)
  | "%greaterthan", [e1; e2] ->
      EOpGt (e1, e2)
  | "%lessequal", [e1; e2] ->
      EOpLe (e1, e2)
  | "%greaterequal", [e1; e2] ->
      EOpGe (e1, e2)

  (* Physical equality. *)

  | "%eq", [e1; e2] ->
      EOpPhysEq (e1, e2)
  | "%noteq", [e1; e2] ->
      EBoolNeg (EOpPhysEq (e1, e2))

  (* Booleans. *)

  | "%boolnot", [e] ->
      EBoolNeg e
  | "%sequand", [e1; e2] ->
      EBoolConj (e1, e2)
  | "%sequor", [e1; e2] ->
      EBoolDisj (e1, e2)

  (* Functions. *)

  | "%apply", [e1; e2] ->
      EApp (e1, e2)
  | "%revapply", [e1; e2] ->
      EApp (e2, e1)
  | "%identity", [e] ->
      e

  (* References. *)

  | "%makemutable", [e] ->
      make_ref e
  | "%setfield0", [e1; e2] ->
      store_ref e1 e2

  (* Atomic field locations. *)

  | "%atomic_load_loc", [e] ->
      ELoad e
  | "%atomic_exchange_loc", [e1; e2] ->
      EExchange (e1, e2)
  | "%atomic_cas_loc", [e1; e2; e3] ->
      ECAS (e1, e2, e3)
  | "%atomic_fetch_add_loc", [e1; e2] ->
      EFAA (e1, e2)

  (* Arrays. *)

  | "%array_length", [e] ->
      EArrayLength e
  | "%array_safe_get", [e1; e2] ->
      EArrayGet (e1, e2)
  | "%array_safe_set", [e1; e2; e3] ->
      EArraySet (e1, e2, e3)
  | "%array_unsafe_get", [e1; e2] ->
      EArrayGet (e1, e2)
  | "%array_unsafe_set", [e1; e2; e3] ->
      EArraySet (e1, e2, e3)
  | "caml_array_make", [e1; e2] ->
      EArrayMake (e1, e2)
  (* TODO: for testing purposes, we naively translate all applications of "opaque" to freeze.
     This is of course incorrect, and should rely on type-level information for more precise translation. *)
  | "%opaque", [e] ->
      EFreeze e
  | "%freeze", [e] ->
      EFreeze e
  | "%unfreeze", [e] ->
      EUnfreeze e

  (* Exceptions. *)

  | "%raise", [e] ->
      ERaise e

  (* Effects. *)

  | "%perform", [e] ->
      EPerform e

  | _, _ ->
      raise Unrecognized

(* [translate_external loc vd] translates an external declaration. The
   primitive operation is wrapped in anonymous functions corresponding to
   its arity. *)

and translate_external loc (vd : Typedtree.value_description) : sitem option =
  match vd.val_val.val_kind with
  | Val_prim p ->
      let x = Ident.name vd.val_id in
      let arity = p.prim_arity in
      let vars = List.init arity (fun i ->sprintf "__x%d" i) in
      let args = map (fun s -> EPath [ s ]) vars in
      begin try
        (* Build the body by passing the arguments to the right primitive. *)
        let body = translate_primitive_expr p.prim_name args in
        (* Build the "eta-expanded" expression *)
        let e =
            List.fold_right
                (fun s e -> EAnonFun (AnonFun (s, e)))
                vars body
        in
        Some (IExternal (x, e))
      with Unrecognized ->
        ounsupported loc
          (sprintf "external declaration for primitive %s" p.prim_name)
      end
  | _ ->
      ounsupported loc "external declaration without primitive"

(* -------------------------------------------------------------------------- *)

(* Structure items. *)

and translate_structure_item (item : structure_item) : sitem option =
  let loc = item.str_loc in
  match item.str_desc with

  | Tstr_eval (e, _) ->
      (* An expression [e] at the toplevel is translated in the same way
         as the toplevel binding [let _ = e]. *)
      Some (ILet [Binding (PAny, translate_expr e)])

  | Tstr_value (Nonrecursive, vbs) ->
      Some (ILet (translate_bindings vbs))

  | Tstr_value (Recursive, vbs) ->
      begin try
        Some (ILetRec (translate_rec_bindings vbs))
      with Unsupported ->
        ounsupported loc "recursive definition of values"
      end

  | Tstr_primitive vd ->
      translate_external loc vd

  | Tstr_type _ ->
      (* A type definition is silently ignored. *)
      None

  | Tstr_typext { tyext_constructors = tys; _} ->
      Some (IExtend (map (fun c -> txt c.ext_name) tys))

  | Tstr_exception { tyexn_constructor = ty; _} ->
      Some (IExtend [ txt ty.ext_name ] )

  | Tstr_module { mb_id = Some id; mb_expr = me; _} ->
      let m = Ident.name id in
      Some (IModule (m, translate_mod_expr me))

  | Tstr_module { mb_id = None; _} ->
      ounsupported loc "module _"

  | Tstr_recmodule _ ->
      ounsupported loc "recursive module"

  | Tstr_modtype _ ->
      (* A module type definition is silently ignored. *)
      None

  | Tstr_open { open_expr = me; _ } ->
      Some (IOpen (translate_mod_expr me))

  | Tstr_class _ ->
      ounsupported loc "class definition"

  | Tstr_class_type _ ->
      (* A class type definition is silently ignored. *)
      None

  | Tstr_include { incl_mod = me; _ } ->
     Some (IInclude (translate_mod_expr me))

  | Tstr_attribute _ ->
      (* An attribute is silently ignored. *)
      None

and translate_structure_items items =
  List.filter_map translate_structure_item items

(* -------------------------------------------------------------------------- *)

(* Module expressions. *)

and translate_structure (str : structure) : mexpr =
  MStruct (translate_structure_items str.str_items)

and translate_mod_expr (me : module_expr) : mexpr =
  let loc = me.mod_loc in
  match me.mod_desc with

  | Tmod_ident (path, id) ->
      MPath (translate_mod_ident path (txt id))

  | Tmod_structure str ->
      translate_structure str

  | Tmod_functor _ ->
      munsupported loc "functor"

  | Tmod_apply _ ->
      munsupported loc "functor application"

  | Tmod_apply_unit _ ->
      munsupported loc "functor unit application"

  | Tmod_constraint _ ->
      munsupported loc "signature ascription"

  | Tmod_unpack _ ->
      munsupported loc "first-class modules"

(* -------------------------------------------------------------------------- *)

end (* Run *)

(* The main function. *)

let unit source str =
  let open Run(struct let source = source end) in
  translate_structure str

end
