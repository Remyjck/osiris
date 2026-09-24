# Repo Roadmap

The Osiris project is organized as a dune workspace with four top-level sub-projects:
- `rocq-osiris/`: the core Rocq development (language model, program logics, stdlib translation)
- `osiris/`: the OCaml-to-Rocq translator
- `interp/`: the validation framework (Rocq extraction + OCaml interpreter)
- `examples/`: translated OCaml examples and their Rocq proofs

## Rocq Development

The Rocq development offers:
- a deep embedding of a fragment of OCaml in Rocq
- two program logics to reason about OCaml programs

### Model of the Language (`rocq-osiris/theories/`)

- `lang/`: core AST (`syntax.v`), the `Encode A` typeclass (`encode.v`), numeric types, memory locations, thread identifiers, notations, and induction principles. Re-exported via `lang.v`.

- `semantics/`: the `micro` monad (`micro.v`), OCaml-specific effect codes, the monadic definitional interpreter (`eval.v`), small-step operational semantics (`step.v`), pure reduction steps, and pluggable evaluation strategies for the interpreter. Re-exported via `semantics.v`.

### Horus — pure program logic (`rocq-osiris/theories/pure_logic/`)

Horus reasons about pure (non-effectful) OCaml programs.

- `wp.v`: `pure_wp` definition: the base notion for pure judgements
- `judgements.v`: the `pure` judgements and relevant notations
- `pure_rules.v`: core rules over `pure` judgements (bind, ret, throw)
- `expr_rules.v`: reasoning rules for evaluating expressions
- `binding_rules.v`: rules for `let` and `let rec` bindings
- `pattern_rules.v`: rules for pattern matching
- `toplevel_rules.v`: rules for top-level definitions (struct items, bindings, modules)
- `fun_spec.v`: `Spec` abstraction for reasoning about n-ary function calls
- `pure.v`: umbrella re-export

### Osiris — effectful program logic (`rocq-osiris/theories/program_logic/`)

Osiris reasons about arbitrary OCaml programs with Iris.

- `ewp.v`: definition of our weakest precondition
- `fun_spec.v`: `iSpec` abstraction for reasoning about n-ary function calls
- `osiris_utils.v`: utility definitions for Osiris proofs (re-exported via proofmode)
- `lib/`: the custom ghost state Osiris is built on:
  - `ghost_state.v`: Osiris's ghost state (`osirisGS`, `osirisΣ`), heap and thread
    resources (`valid_thread`), and the state interpretation
  - `block_resources.v`: block resources (`blockLocs`, `blockTag`)
  - `block_map.v`: block ghost map, an authoritative map of agreements from each
    block to its element locations
  - `thread_post.v`: thread postconditions, an authoritative map of agreements
    from thread ids to their postconditions
  - `protocols.v`: Iris effect protocols (adapted from Hazel by Vilhena & Pottier)
  - `escrows.v`: escrow allocation lemmas, and `big_sepL` helpers
- `rules/`: EWP reasoning rules:
  - `basic_rules.v`: core EWP definition and pure-step rules
  - `micro_rules.v`: rules for micro monad constructs (ret, throw, crash, bind, try, Par)
  - `stop_rules.v`: rules for the effects provided by `Stop`
  - `handler_rules.v`: rules for effect handlers
  - `auxiliary_rules.v`: rules for evaluating modules and struct items
  - `expr_rules.v`: rules for evaluating expressions
  - `array_rules.v`: rules for array operations
  - `record_rules.v`: rules for record operations
  - `atomic_rules.v`: `Atomic` typeclass instances; invariant-based atomic rules for load/store/CAS/FAA
- `adequacy/`: metatheory:
  - `adequacy.v`: adequacy theorem for Horus
  - `ewp_adequacy.v`: adequacy theorem for Osiris
  - `erasure.v`: erasure of prophecies from expressions, values, computations
    and stores (`erase_expr`, `erase_val`, `erase_micro`, `erase_store`)
  - `erasure_eval.v`: the erasure commutes with the interpreter (`erase_eval`)
  - `erasure_adequacy.v`: safety of an annotated program implies safety of
    the program with the annotations removed, and the erased
    program emits no observation (`erasure`, `erasure_adequacy`)
- `program_logic.v`: umbrella re-export (also re-exports Horus)

### Proofmode (`rocq-osiris/theories/proofmode/`)

- `pure_tactics.v`: tactics for discharging pure goals
- `imp_tactics.v`: tactics for Iris/EWP goals (`imp_store_atomic`, `imp_arith`, `imp_if`, …)
- `env_lookups.v`: specifications for modules (environments), the `imp_path` tactic, and
  the `solve_env` tactic
- `handler_tactics.v`: tactics for reasoning about handlers
- `setup.v`: opacity settings and general proofmode configuration (exported last)
- `proofmode.v`: umbrella re-export

### Utilities (`rocq-osiris/utils/`)

- `base.v`: base imports
- `logic/`: mathematical utilities:
  - `list_z.v`: lists with Z-valued indices
  - `big_opLZ.v`: big ops on lists with Z indices
  - `orders.v`: ordering relations
  - `sorting.v`: properties of sorted lists
- `tactics/`: tactic utilities:
  - `ltac2_utils.v`: Ltac2 helpers
  - `iris_bindings.v`: Iris binding tactics

### Top-level (`rocq-osiris/theories/`)

- `osiris.v`: re-exports the language model, program logics, and proofmode as a single import
- `test/`: manual tests for the operational semantics and record encoding

### Standard Library (`rocq-osiris/stdlib/`)

- `Stdlib.v`: translation-independent definitions of the OCaml standard library environment
- `Externals.v`: external (unverified) primitives
- `og_*.v`: auto-generated translations of OCaml stdlib modules (produced by the translator)
- `proofs/`: specifications and proofs for translated stdlib modules:
  - `array.v`: array operations
  - `iarray.v`: immutable array operations

## Validation

`interp/` extracts the Rocq semantics to OCaml and wraps it in an interpreter (`interp.exe`) that runs OCaml source files by invoking the extracted `eval` and intercepting I/O effects. Run with e.g. `dune exec interp/interp.exe <file.ml>` from the workspace root.

Tests are in `tests/`:
- `tests/*.ml`: handwritten `.ml` test files
- `tests/ocaml-testsuite/`: tests adapted from OCaml's test suite
- `tests/runtests.sh`: checks that for each test file, `ocaml file.ml` and `interp.exe file.ml` produce the same output

## Translator

The translator from OCaml source files to Rocq definitions is under `osiris/`.

- `osiris/src/`
  - `Syntax.ml`: definition of the Osiris AST; must stay in sync with `rocq-osiris/theories/lang/syntax.v`
  - `Translate.ml`: transforms OCaml parsetree expressions into the Osiris AST
  - `Rocqify.ml`: transforms the Osiris AST into Rocq source text
  - `Main.ml`: entry point; reads `.cmt` files, calls dune for module discovery, writes `og_*.v` files
  - `Dune.ml`: discovers modules and `.cmt` file paths via `dune describe`; extracts workspace root for correct path resolution
- `osiris/lib/`: the OCaml support library shipped with the translator
  - `proph.ml`: the `Proph` module for prophecy allocation. This module is treated specially by the translator


# Correspondence with the paper

We give a correspondence between features of the paper and their Rocq mechanization.

### Section 3: A Monadic Interpreter

* OCaml expressions and patterns → `rocq-osiris/theories/lang/syntax.v`
* Translator → `osiris/`
* OLang's type of values → `rocq-osiris/theories/lang/syntax.v`
* eval_expr/eval_pat → `rocq-osiris/theories/semantics/eval.v`
* internals of eval + other auxiliary functions → `rocq-osiris/theories/semantics/eval.v`
* outcomes → `rocq-osiris/theories/lang/outcome.v`
* The micro public interface → `rocq-osiris/theories/semantics/code.v` (and some bits in `micro.v`)

### Section 4: The Micro Monad

* The micro monad definition → `rocq-osiris/theories/semantics/micro.v`
* Codes/system calls → `rocq-osiris/theories/semantics/code.v`

### Section 5: Small-step semantics for the Micro Monad

* Configurations/stores → `rocq-osiris/theories/semantics/step.v`
* Stepping relation → `rocq-osiris/theories/semantics/step.v`

### Section 6: Validation

* Extraction → `interp/extracted/extract.v`
* Step function → `interp/run.v`
* OCaml interpreter → `interp/interp.ml`
* Test suite → `tests/`

### Section 7: Horus

* Pure reductions → `rocq-osiris/theories/semantics/pure.v`
* Claims about pure steps → `rocq-osiris/theories/semantics/pure_step.v`
* Pure wp → `rocq-osiris/theories/pure_logic/wp.v`
* Pure rules for micro → `rocq-osiris/theories/pure_logic/pure_rules.v`
* encoding → `rocq-osiris/theories/lang/encode.v`
* Definition of pure__# (`pure` in the development) → `rocq-osiris/theories/pure_logic/judgements.v`
* Definition of expr → `rocq-osiris/theories/pure_logic/judgements.v` (just notation)
* Rules for expressions → `rocq-osiris/theories/pure_logic/expr_rules.v`
* Definition of pat → `rocq-osiris/theories/pure_logic/pattern_rules.v`
* Definition of branches → `rocq-osiris/theories/pure_logic/expr_rules.v`
* Definition of spec → `rocq-osiris/theories/pure_logic/fun_spec.v`
* Spec public API → `rocq-osiris/theories/pure_logic/fun_spec.v`
* Merge example → `examples/proofs/merge.v`
* Splay example → `examples/proofs/splay.v`

### Section 8: Osiris

* Definition of impure → `rocq-osiris/theories/program_logic/ewp.v`
* Micro level rules → `rocq-osiris/theories/program_logic/rules/micro_rules.v`
* Rules for Handle → `rocq-osiris/theories/program_logic/rules/handler_rules.v`
* Definition of impure__# → `rocq-osiris/theories/program_logic/ewp.v` (lifting notation)
* Find example → `examples/proofs/find.v`
