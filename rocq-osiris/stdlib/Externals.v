From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Import fancy_updates.
From iris.prelude Require Import options.
Import uPred.

From osiris.lang Require Import type_nel encode int notations locations.
From osiris.semantics Require Import eval.
From osiris.program_logic Require Import program_logic.
From osiris.proofmode Require Import env_lookups.
From osiris.utils Require Import list_z.

Abbreviation VEta1 body :=
  (
    VClo [] $
         AnonFun "__x0" $
         body (EPath [ "__x0" ])
  ).
Abbreviation VEta2 body :=
  (
    VClo [] $
         AnonFun "__x0" $
         EAnonFun (AnonFun "__x1"
         (body (EPath [ "__x0" ]) (EPath [ "__x1" ])))
  ).
Abbreviation VEta3 body :=
  (
    VClo [] $
         AnonFun "__x0" $
         EAnonFun (AnonFun "__x1" $
         EAnonFun (AnonFun "__x2" $
                     (body (EPath [ "__x0" ]) (EPath [ "__x1" ]) (EPath [ "__x2" ]))))
  ).

Abbreviation EEta1 body :=
  (
    EAnonFun $
      AnonFun "__x0" $
      body (EPath [ "__x0" ])
  ).
Abbreviation EEta2 body :=
  (
    EAnonFun $
      AnonFun "__x0" $
      EAnonFun (AnonFun "__x1"
                  (body (EPath [ "__x0" ]) (EPath [ "__x1" ])))
  ).
Abbreviation EEta3 body :=
  (
    EAnonFun $
         AnonFun "__x0" $
         EAnonFun (AnonFun "__x1" $
         EAnonFun (AnonFun "__x2" $
                     (body (EPath [ "__x0" ]) (EPath [ "__x1" ]) (EPath [ "__x2" ]))))
  ).

Section ExternalsDef.

  Context `{!osirisGS Σ}.

  Implicit Types ζ : exn → iProp Σ.

  (* ------------------------------------------------------------------------ *)
  (* Content of Externals used in [stdlib/int.ml]. *)

  Definition Externals__negint : val := VEta1 EIntNeg.
  Definition Externals__addint : val := VEta2 EIntAdd.

  Lemma add_spec :
    ⊢ {{ True }} Externals__addint i j : Z Z {{ RET (n : Z); ⌜(n = i + j)%Z⌝ }}.
  Proof.
    iModIntro.
    rewrite iSpec_equation_2.
    iIntros (i).
    iApply imp_please. iNext.
    iApply imp_EAnon.
    iIntros (j). iIntros "_". iApply imp_please. iNext.
    iApply imp_EIntAdd.
    - instantiate (1:=(λ n', ⌜n' = i⌝)%I).
      iApply imp_EPath; auto.
    - instantiate (1:=(λ n', ⌜n' = j⌝)%I).
      iApply imp_EPath; auto.
    - iIntros "!>" (??) "-> ->". done.
  Qed.

  Definition Externals__subint : val := VEta2 EIntSub.

  Lemma sub_spec :
    ⊢ {{ True }} Externals__subint i j : Z Z {{ RET (n : Z); ⌜(n = i - j)%Z⌝ }}.
  Proof.
    iModIntro.
    rewrite iSpec_equation_2.
    iIntros (i).
    iApply imp_please. iNext.
    iApply imp_EAnon.
    iIntros (j). iIntros "_". iApply imp_please. iNext.
    iApply imp_EIntSub.
    - instantiate (1:=(λ n', ⌜n' = i⌝)%I).
      iApply imp_EPath; auto.
    - instantiate (1:=(λ n', ⌜n' = j⌝)%I).
      iApply imp_EPath; auto.
    - iIntros "!>" (??) "-> ->". done.
  Qed.

  Definition Externals__mulint : val := VEta2 EIntMul.
  Definition Externals__divint : val := VEta2 EIntDiv.
  Definition Externals__modint : val := VEta2 EIntMod.
  Definition Externals__succint : val :=
    VEta1 (fun x => EIntAdd x (EInt 1)).
  Definition Externals__predint : val :=
    VEta1 (fun x => EIntSub x (EInt 1)).

  Definition Externals__lessthan : val := VEta2 EOpLt.
  Definition Externals__greaterthan : val := VEta2 EOpGt.
  Definition Externals__lessequal : val := VEta2 EOpLe.
  Definition Externals__greaterequal : val := VEta2 EOpGe.

  (* The following names are used in [stdlib/int.ml], but they are not supported
     yet: - %andint
          - %orint
          - %xorint
          - %lslint
          - %asrint
          - %lsrint
          - %floatofint
          - %intoffloat
          - caml_format_int
          - caml_hash *)

  (* ------------------------------------------------------------------------ *)

  (* On Booleans. *)

  Definition Externals__boolnot : val := VEta1 EBoolNeg.

  (* ------------------------------------------------------------------------ *)

  Definition Externals__revapply : val :=
    VClo [] $
         AnonFun "x" $
         EFun1Var "y" $
         EApp (EVar "y") (EVar "x").

  Definition Externals__apply : val :=
    VClo [] $
         AnonFun "x" $
         EFun1Var "y" $
         EApp (EVar "x") (EVar "y").

  Definition Externals__identity : val :=
    VClo [] $
         AnonFun "x" $ EVar "x".

  Definition Externals__ignore : val :=
    VClo [] $ AnonFun "_" $ EUnit.

  (* Comparison. *)
  Definition Externals__eq : val := VEta2 EOpEq.
  Definition Externals__ne : val := VEta2 EOpNe.

  (* ------------------------------------------------------------------------ *)

  (* On constructed types. *)

  Definition Externals__field0 : val :=
    VEta1 (λ (e : expr),
             ELet1 (PPair (PVar "x") PAny) e $
                   EVar "x").

  Definition Externals__field1 : val :=
    VEta1 (λ (e : expr),
             ELet1 (PPair PAny (PVar "x")) e $
                   EVar "x").

  (* ------------------------------------------------------------------------ *)
  (* Content of Externals used in [stdlib/array.ml]. *)

  (** "%array_length" *)

  Definition Externals__array_length : val := VEta1 EArrayLength.
  Definition Externals__array_length_expr := EEta1 EArrayLength.

  Definition array_length_spec length : iProp Σ :=
    {{ ∀ (ls : list loc); blockLocs a ls }}
    length a : array
    {{ RET n'; ⌜n' = list_z.length ls⌝ }}.

  Lemma imp_externals_length {E Ψ ζ} (sitems : list sitem) (x : var) (Q : envs → iProp Σ) (η δ : env) :
    (∀ length,
       array_length_spec length -∗
       EWP eval_sitems (x ~> length;
                     η, x ~> length;
                     δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    EWP eval_sitems (η, δ) (IExternal x Externals__array_length_expr :: sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hsitems".
    iApply (imp_sitems_external with "[] Hsitems").
    iApply imp_wand_exn.
    - iApply (imp_EAnon_pers τ[array]).
      iIntros "!>" (a n) "Harr".
      iApply imp_please; iNext.
      iApply imp_EArrayLength'. imp_path.
    - iIntros (? []).
  Qed.

  (** "%array_get" and "%array_unsafe_get" *)

  Definition Externals__array_get : val := VEta2 EArrayGet.
  Definition Externals__array_get_expr : expr := EEta2 EArrayGet.

  Definition array_get_spec get : iProp Σ :=
    {{ ∀ `(Encode A, Inhabited A) dq j (xs : list A);
       ▷ a ↦∗[j]{dq} xs ∗ ⌜j ≤ i < j + length xs⌝ }}
    get a i : array Z
    {{ RET (v : A); ⌜v = xs !!! (i - j)⌝ ∗ a ↦∗[j]{dq} xs }}.

  Lemma imp_externals_get {E Ψ ζ} (sitems : list sitem) (x : var) (Q : envs → iProp Σ) (η δ : env) :
    (∀ get,
       array_get_spec get -∗
       EWP eval_sitems (x ~> get;
                     η, x ~> get;
                     δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    EWP eval_sitems (η, δ) (IExternal x Externals__array_get_expr :: sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hsitems".
    iApply (imp_sitems_external with "[] Hsitems").
    iApply imp_wand_exn.
    - iApply (imp_EAnon_pers).
      iIntros "!>" (a i A HencA HinhA dq j xs) "(Hslice & %Hbounds)".
      iApply imp_please; iNext.
      iApply (imp_EArrayGet' with "[%] Hslice"); try imp_path.
      assumption.
    - iIntros (? []).
  Qed.

  (** "%array_set" and "%array_unsafe_set" *)

  Definition Externals__array_set : val := VEta3 EArraySet.
  Definition Externals__array_set_expr : expr := EEta3 EArraySet.

  Definition array_set_spec set : iProp Σ :=
    ∀∀ `(Encode A, Inhabited A);
    {{ ∀ j (xs : list A) Φ;
       ▷ a ↦∗[j] xs ∗ Φ x ∗ ⌜j ≤ i < j + length xs⌝ }}
    set a i x : array Z A
    {{ RET (_ : unit); ∃ x, Φ x ∗ a ↦∗[j] (<[i - j:=x]> xs) }}.

  Lemma imp_externals_set {E Ψ ζ} (sitems : list sitem) (x : var) (Q : envs → iProp Σ) (η δ : env) :
    (∀ set,
       array_set_spec set -∗
       EWP eval_sitems (x ~> set;
                     η, x ~> set;
                     δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    EWP eval_sitems (η, δ) (IExternal x Externals__array_set_expr :: sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hsitems".
    iApply (imp_sitems_external with "[] Hsitems").
    iApply imp_wand_exn.
    - iApply imp_EAnon_poly.
      iIntros "!>" (A HencA HinhA); simpl.
      iIntros "%a %i %y %j %xs %Φ (Hslice & HΦ & %Hbounds)".
      iApply imp_please; iNext.
      iApply (imp_EArraySet' with "[%] Hslice"); try imp_path.
      assumption.
    - iIntros (? []).
  Qed.

  (** "caml_array_make" *)

  Definition Externals__array_make : val := VEta2 EArrayMake.
  Definition Externals__array_make_expr : expr := EEta2 EArrayMake.

  Definition array_make_spec make : iProp Σ :=
    ∀∀ `(Encode A);
    {{ ∀ Φ; ⌜0 ≤ n ≤ max_array_length⌝ ∗ Φ x }}
    make n x : Z A
    {{ RET a; ∃ x, Φ x ∗ a ↦∗ (replicate n x) }}.

  Lemma imp_externals_make {E Ψ ζ} (sitems : list sitem) (x : var) (Q : envs → iProp Σ) (η δ : env) :
    (∀ make,
       array_make_spec make -∗
       EWP eval_sitems (x ~> make;
                        η, x ~> make;
                        δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    EWP eval_sitems (η, δ) (IExternal x Externals__array_make_expr :: sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hsitems".
    iApply (imp_sitems_external with "[] Hsitems").
    iApply imp_wand_exn.
    - iApply imp_EAnon_poly.
      iIntros "!>" (A HencA); simpl.
      iIntros "%n %y %Φ (%hbound & HΦ)".
      iApply imp_please; iNext.
      iApply imp_EArrayMake; try imp_path.
      + iPureIntro; assumption.
    - iIntros (? []).
  Qed.

  Definition Externals__freeze : val := VEta1 EFreeze.
  Definition Externals__freeze_expr : expr := EEta1 EFreeze.

  Definition freeze_spec freeze : iProp Σ :=
    {{ ∀ t; blockTag l (DfracOwn 1) t }}
    freeze l : array
    {{ RET l'; ⌜l' = l⌝ ∗ blockTag l (DfracOwn 1) Immut }}.

  Lemma imp_externals_freeze {E Ψ ζ} (sitems : list sitem) (x : var) (Q : envs → iProp Σ) (η δ : env) :
    (∀ freeze,
       freeze_spec freeze -∗
       EWP eval_sitems (x ~> freeze;
                        η, x ~> freeze;
                        δ) sitems @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}) -∗
    EWP eval_sitems (η, δ) (IExternal x Externals__freeze_expr :: sitems) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Q }}.
  Proof.
    iIntros "Hsitems".
    iApply (imp_sitems_external with "[] Hsitems").
    iApply imp_wand_exn.
    - iApply imp_EAnon_pers.
      iIntros "!> %l %t Hblock".
      iApply imp_please; iNext.
      iApply (imp_EFreeze with "Hblock"); imp_path.
    - iIntros (? []).
  Qed.


End ExternalsDef.
