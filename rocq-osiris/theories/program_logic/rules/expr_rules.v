From iris Require Import gen_heap proofmode.proofmode.
From iris.base_logic.lib Require Import proph_map.
From osiris.lang Require Import lang.
Require Import osiris_utils.
Require Import ewp tactics fun_spec escrows.
Require Import
  basic_rules impure_rules stop_rules proph_rules
  handler_rules auxiliary_rules atomic_rules.

(** This file contains [EWP] rules for OCaml expression forms. *)

Section imp_rules_expr.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ}.
  Context {A : Type} `{EncA : Encode A} {Φ : A → iProp Σ}.
  Implicit Types ζ : exn → iProp Σ.

  (* -------------------------------------------------------------------------- *)
  (* Lemmas about [expr]s *)

  (** * EPath : path → expr *)

  Lemma imp_EPath {ζ} (a : A) η p :
    lookup_path η p = Some #a →
    Φ a -∗
    EWP eval η (EPath p) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "%Hlookup HΦ". simpl_eval.
    iApply imp_of_option.
    rewrite Hlookup.
    by iFrame.
  Qed.

  (** * EAnonFun : anonfun → expr *)
  (** * EApp : expr → expr → expr *)
  (* See [fun_spec.v] *)

  Lemma imp_EApp' `{Encode B} {ζ} η e1 e2 Φ1 (Φ2 : B → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ f x, Φ1 f -∗ Φ2 x -∗ EWP call f #x @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (EApp e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 H". simpl_eval.
    iApply (imp_bind_par with "H1 H2").
    iIntros (??) "HΦ1 HΦ2 !>".
    iApply ("H" with "HΦ1 HΦ2").
  Qed.

  (* The following [imp_call_*] lemmas just follow the reduction rules for
  function calls when a closure is applied. For better modularity and smaller
  proof terms, it should generally preferred to have a specification ready for
  the available functions values, having abstracted away the closure values.
  Maybe in some cases, though, having a specification for a simple function
  might be too verbose or be too trivial, and one could simply wish to "just
  reduce" the term, in which case those lemmas may be useful. *)
  Lemma imp_call_nonrec {ζ} η x_arg body v_arg :
    ▷EWP eval ((x_arg, v_arg) :: η) body @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    EWP call (VClo η (AnonFun x_arg body)) v_arg @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    by iApply imp_please.
  Qed.

  Lemma imp_call_rec {ζ} η f x body bs v :
    lookup_rec_bindings bs f = Some (AnonFun x body) ->
    ▷ EWP eval ((x, v) :: eval_rec_bindings η bs ++ η) body @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    EWP call (VCloRec η bs f) v @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hlk) "H /=". rewrite Hlk /=.
    by iApply imp_please.
  Qed.

  (** * ETuple : list expr → expr *)
  (* See [evals_rules.v]. *)

End imp_rules_expr.

Section imp_rules_expr.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ}.
  Implicit Types ζ μ : exn → iProp Σ.

  Lemma imp_EUnit {Φ ζ} η :
    Φ tt -∗
    EWP eval η EUnit @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    simpl_eval; by iApply imp_ret.
  Qed.

  Lemma imp_EUnit_forward {ζ} η :
    ⊢ EWP eval η EUnit @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ u, ⌜u = tt⌝ }}.
  Proof.
    simpl_eval; iApply imp_ret; [ encode | auto ].
  Qed.

  Local Instance observe_tuple {V : Type} `{Observe A V} `{Observe B V} : Observe (A * B) (list V) :=
    { observe := (λ '(a, b), [ observe a; observe b ]) }.

  Lemma imp_EPair `{Encode A, Encode B} {ζ} {Φ : τ[A;B] → iProp Σ} η e1 e2 (Φ1 : A → iProp Σ) (Φ2 : B → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    (∀ a1 a2, Φ1 a1 -∗ Φ2 a2 -∗ Φ (a1, a2)) -∗
    EWP eval η (EPair e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin". simpl_eval.
    iApply (imp_bind (A:=τ[A;B]) with "[-]").
    { iApply (imp_bind_par (A2:=list B) with "H1 [H2]").
      { iApply (imp_bind_par (A2:=list val) with "H2").
        { set_postcondition (λ l, ⌜l=[]⌝)%I.
          iApply imp_ret. encode. auto. }
        iIntros (b ?) "HΦ2 -> !>".
        set_postcondition (λ (l : list B), ∃ b, ⌜l = [b]⌝ ∗ Φ2 b)%I.
        iApply (imp_ret _ [b]). reflexivity.
        by iFrame. }
      iIntros (a ?) "HΦ1 (%b & -> & HΦ2) !>".
      iSpecialize ("Hjoin" with "HΦ1 HΦ2"). simpl.
      iApply (imp_ret _ ((a, b) : τ[A;B]) with "Hjoin"). encode. }
    iIntros (p) "HΦ".
    iApply (imp_ret with "HΦ"). auto.
  Qed.

  (** * EData : data → expr → expr *)
  (* See [evals_rules.v] *)

  (* The logical value of the constant is determined by the [Constant] typeclass. *)
  Lemma imp_EConstant {c : data} {B : Type} {HB : Encode B} {HC : Constant c B} {ζ} η :
    ⊢ EWP eval η (EConstant c) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ b, ⌜b = @constant_value c B HB HC⌝ }}.
  Proof.
    simpl_eval. iApply imp_ret; [apply constant_encode | done].
  Qed.

  Lemma imp_EConstant' {c : data} {B : Type} {HB : Encode B} {HC : Constant c B} {Φ' : B → iProp Σ} {ζ} η :
    Φ' (@constant_value c B HB HC) -∗
    EWP eval η (EConstant c) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ' }}.
  Proof.
    iIntros "HΦ". simpl_eval.
    iApply (imp_ret with "HΦ"). apply constant_encode.
  Qed.

  (** * EXData : data → expr → expr *)
  (* See [evals_rules.v] *)

  (** * ERecord : list fexpr → expr *)
  (** * ERecordUpdate : expr → list fexpr → expr *)
  (** * ERecordAccess : expr → field → expr *)
  (* See [record_rules.v]. *)

  (** * EFreeze : expr → expr *)

  Lemma imp_EFreeze2 {ζ} (Φ : array → iProp Σ) (Φ' : array → iProp Σ) η e :
    impure E (eval η e) Ψ ζ Φ' -∗
    (∀ l, Φ' l -∗ ∃ t, ▷ blockTag l (DfracOwn 1) t ∗ Φ l) -∗
    impure E (eval η (EFreeze e)) Ψ ζ (λ l, Φ l ∗ blockTag l (DfracOwn 1) Immut).
  Proof.
    iIntros "He Hcov".
    simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_array with "He"). }
    iIntros (l) "HΦl".
    iDestruct ("Hcov" with "HΦl") as "(%t & Hl & HΦ)".
    iApply (imp_bind with "[Hl]").
    { iApply (imp_set_tag with "Hl"). }
    iIntros ([]) "Hl".
    iApply imp_ret; first encode.
    iFrame.
  Qed.

  Lemma imp_EFreeze {ζ} (l : array) t η e :
    ▷ blockTag l (DfracOwn 1) t -∗
    impure E (eval η e) Ψ ζ (λ l', ⌜l' = l⌝) -∗
    impure E (eval η (EFreeze e)) Ψ ζ (λ l', ⌜l' = l⌝ ∗ blockTag l (DfracOwn 1) Immut).
  Proof.
    iIntros "Hl He".
    iApply (imp_wand with "[-]").
    { iApply (imp_EFreeze2 (λ l', ⌜l' = l⌝)%I with "He").
      iIntros (?) "->". by iFrame. }
    iIntros (?) "(-> & $) //".
  Qed.

  (** * EUnfreeze : expr → expr *)

  Lemma imp_EUnfreeze {ζ} (Φ' : array → iProp Σ) (Φ : array → iProp Σ) η e :
    impure E (eval η e) Ψ ζ Φ' -∗
    (∀ l, Φ' l -∗ ∃ t, blockTag l (DfracOwn 1) t ∗ Φ l) -∗
    impure E (eval η (EUnfreeze e)) Ψ ζ (λ l, Φ l ∗ blockTag l (DfracOwn 1) Mut).
  Proof.
    iIntros "He Hcov".
    simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_array with "He"). }
    iIntros (l) "HΦl".
    iDestruct ("Hcov" with "HΦl") as "(%t & Hl & HΦ)".
    iApply (imp_bind with "[Hl]").
    { iApply (imp_set_tag with "Hl"). }
    iIntros ([]) "Hl".
    iApply imp_ret; first encode.
    iFrame.
  Qed.

  (** * EBoolConj : expr → expr → expr *)
  (** * EBoolDisj : expr → expr → expr *)
  (** * EBoolNeg : expr → expr *)

  Lemma imp_EBoolNeg {ζ} (Φ : bool → iProp Σ) η e :
    impure E (eval η e) Ψ ζ (λ b, Φ (negb b)) -∗
    impure E (eval η (EBoolNeg e)) Ψ ζ Φ.
  Proof.
    iIntros "He".
    simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_bool with "He"). }
    iIntros (b) "HΦ".
    iApply (imp_ret with "HΦ"); first encode.
  Qed.

  (* [e1 || e2] short-circuits: [e2] is evaluated only when [e1] yields
     [false], so the continuation owes a proof for [e2] in that case
     alone, and [Φ true] outright in the other. *)
  Lemma imp_EBoolDisj {ζ} (Φ Φ1 : bool → iProp Σ) η e1 e2 :
    impure E (eval η e1) Ψ ζ Φ1 -∗
    (∀ b1, Φ1 b1 -∗
           if b1 then Φ true else impure E (eval η e2) Ψ ζ Φ) -∗
    impure E (eval η (EBoolDisj e1 e2)) Ψ ζ Φ.
  Proof.
    iIntros "He1 He2".
    simpl_eval.
    iApply (imp_bind with "[He1]").
    { iApply (imp_as_bool with "He1"). }
    iIntros (b1) "HΦ1".
    iDestruct ("He2" with "HΦ1") as "He2".
    destruct b1.
    - iApply (imp_ret with "He2"); first encode.
    - iApply "He2".
  Qed.

  (** * EInt : Z → expr *)

  Lemma imp_EInt {ζ} η i :
    ⊢ EWP eval η (EInt i) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = i⌝ }}.
  Proof.
    simpl_eval; by iApply imp_ret.
  Qed.

  (** * EMaxInt : expr *)

  Lemma imp_EMaxInt {ζ} η :
    ⊢ EWP eval η EMaxInt @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = max_signed⌝ }}.
  Proof. simpl_eval. iApply imp_ret; [ encode | auto ]. Qed.

  (** * EMinInt : expr *)

  Lemma imp_EMinInt {ζ} η :
    ⊢ EWP eval η EMinInt @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = min_signed⌝ }}.
  Proof. simpl_eval. iApply imp_ret; [ encode | auto ]. Qed.

  (** * EIntNeg : expr → expr *)

  Lemma imp_EIntNeg {ζ} η e (Φ1 : Z → iProp Σ) Φ :
    EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    (∀ i, Φ1 i -∗ Φ (- i)) -∗
    EWP eval η (EIntNeg e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He Hcon". simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_int with "He"). }
    iIntros (i) "HΦ1".
    iApply imp_ret; first encode.
    iApply ("Hcon" with "HΦ1").
  Qed.

  (** * EIntAdd : expr → expr → expr *)

  Lemma imp_EIntAdd {ζ} η e1 e2 (Φ1 Φ2 : Z → iProp Σ) Φ :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ i j, Φ1 i -∗ Φ2 j -∗ Φ (i + j)) -∗
    EWP eval η (EIntAdd e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin /=". simpl_eval.
    iApply (imp_bind_par with "[H1] [H2]").
    { iApply (imp_as_int with "H1"). }
    { iApply (imp_as_int with "H2"). }
    iIntros (i j) "HΦ1 HΦ2 !>".
    iApply imp_ret. encode.
    iApply ("Hjoin" with "HΦ1 HΦ2").
  Qed.

  Lemma imp_EIntAdd_frac' `{fractional.AsFractional _ P Q q} {ζ} η e1 e2 (Φ1 Φ2 : Z → iProp Σ) Φ :
    P -∗
    (Q (q/2)%Qp -∗ EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a1, Φ1 a1 ∗ Q (q/2)%Qp }}) -∗
    (Q (q/2)%Qp -∗ EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a2, Φ2 a2 ∗ Q (q/2)%Qp }}) -∗
    ▷ (∀ i j, Φ1 i -∗ Φ2 j -∗ Φ (i + j)) -∗
    EWP eval η (EIntAdd e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ i, Φ i ∗ P }}.
  Proof.
    iIntros "P H1 H2 Hjoin /=". rewrite -{3}fold_pre_eval /= !fold_pre_eval.
    fold (as_int (eval η e1)) (as_int (eval η e2)).
    iApply (imp_bind_par_frac with "P [H1] [H2]").
    { iIntros "Q". iSpecialize ("H1" with "Q").
      iApply (imp_as_int with "H1"). }
    { iIntros "Q". iSpecialize ("H2" with "Q").
      iApply (imp_as_int with "H2"). }
    iIntros (i j) "HΦ1 HΦ2 !>".
    iApply imp_ret. encode.
    iApply ("Hjoin" with "HΦ1 HΦ2").
  Qed.

  Lemma imp_EIntAdd_frac `{fractional.AsFractional _ P Q q} {ζ} {e1 e2} (x1 x2 : Z) η :
    P -∗
    (Q (q/2)%Qp -∗ EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a1, ⌜a1 = x1⌝  ∗ Q (q/2)%Qp }}) -∗
    (Q (q/2)%Qp -∗ EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a2, ⌜a2 = x2⌝ ∗ Q (q/2)%Qp }}) -∗
    EWP eval η (EIntAdd e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ i, ⌜i = (x1 + x2)%Z⌝  ∗ P }}.
  Proof.
    iIntros "P H1 H2 /=".
    iApply (imp_EIntAdd_frac' with "P H1 H2").
    iIntros "!>" (??) "-> -> //".
  Qed.

  (** * EIntSub : expr → expr → expr *)

  Lemma imp_EIntSub {ζ} η e1 e2 (Φ1 Φ2 : Z → iProp Σ) Φ :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ i j, Φ1 i -∗ Φ2 j -∗ Φ (i - j)) -∗
    EWP eval η (EIntSub e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin /=". simpl_eval.
    iApply (imp_bind_par with "[H1] [H2]").
    { iApply (imp_as_int with "H1"). }
    { iApply (imp_as_int with "H2"). }
    iIntros (i j) "HΦ1 HΦ2 !>".
    iApply imp_ret. encode.
    iApply ("Hjoin" with "HΦ1 HΦ2").
  Qed.

  (** * EIntMul : expr → expr → expr *)

  Lemma imp_EIntMul {ζ} η e1 e2 (Φ1 Φ2 : Z → iProp Σ) Φ :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ i j, Φ1 i -∗ Φ2 j -∗ Φ (i * j)) -∗
    EWP eval η (EIntMul e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin /=". simpl_eval.
    iApply (imp_bind_par with "[H1] [H2]").
    { iApply (imp_as_int with "H1"). }
    { iApply (imp_as_int with "H2"). }
    iIntros (i j) "HΦ1 HΦ2 !>".
    iApply imp_ret. encode.
    iApply ("Hjoin" with "HΦ1 HΦ2").
  Qed.

    Lemma imp_EIntMul_frac' `{fractional.AsFractional _ P Q q} {ζ} η e1 e2 (Φ1 Φ2 : Z → iProp Σ) Φ :
    P -∗
    (Q (q/2)%Qp -∗ EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a1, Φ1 a1 ∗ Q (q/2)%Qp }}) -∗
    (Q (q/2)%Qp -∗ EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a2, Φ2 a2 ∗ Q (q/2)%Qp }}) -∗
    ▷ (∀ i j, Φ1 i -∗ Φ2 j -∗ Φ (i * j)) -∗
    EWP eval η (EIntMul e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ i, Φ i ∗ P }}.
  Proof.
    iIntros "P H1 H2 Hjoin /=". rewrite -{3}fold_pre_eval /= !fold_pre_eval.
    fold (as_int (eval η e1)) (as_int (eval η e2)).
    iApply (imp_bind_par_frac with "P [H1] [H2]").
    { iIntros "Q". iSpecialize ("H1" with "Q").
      iApply (imp_as_int with "H1"). }
    { iIntros "Q". iSpecialize ("H2" with "Q").
      iApply (imp_as_int with "H2"). }
    iIntros (i j) "HΦ1 HΦ2 !>".
    iApply imp_ret. encode.
    iApply ("Hjoin" with "HΦ1 HΦ2").
  Qed.

  Lemma imp_EIntMul_frac `{fractional.AsFractional _ P Q q} {ζ} {e1 e2} (x1 x2 : Z) η :
    P -∗
    (Q (q/2)%Qp -∗ EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a1, ⌜a1 = x1⌝ ∗ Q (q/2)%Qp }}) -∗
    (Q (q/2)%Qp -∗ EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a2, ⌜a2 = x2⌝ ∗ Q (q/2)%Qp }}) -∗
    EWP eval η (EIntMul e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ i, ⌜i = (x1 * x2)%Z⌝ ∗ P }}.
  Proof.
    iIntros "P H1 H2 /=".
    iApply (imp_EIntMul_frac' with "P H1 H2").
    iIntros "!>" (??) "-> -> //".
  Qed.

  (** * EIntDiv : expr → expr → expr *)

  Lemma imp_EIntDiv {ζ} η e1 e2 (Φ1 Φ2 : Z → iProp Σ) Φ :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ i j, Φ1 i -∗ Φ2 j -∗
              ⌜representable i⌝ ∧ ⌜representable j⌝ ∧ ⌜j ≠ 0⌝ ∧ Φ (i `quot` j)) -∗
    EWP eval η (EIntDiv e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin /=". simpl_eval.
    iApply (imp_bind_par with "[H1] [H2]").
    { iApply (imp_as_int with "H1"). }
    { iApply (imp_as_int with "H2"). }
    iIntros (i j) "HΦ1 HΦ2 !>".
    iDestruct ("Hjoin" with "HΦ1 HΦ2")
      as "(%Hrepr1 & %Hrepr2 & %Hneq & HΦ)".
    rewrite /continue /=.
    iApply imp_bind.
    { rewrite /check_div_by_zero /=.
      rewrite eq_repr_repr; try representable.
      rewrite (iffRL (Z.eqb_neq j 0) Hneq).
      iApply imp_ret; first encode.
      by instantiate (1 := (λ _, True)%I). }
    iIntros ([]) "_".
    iApply (imp_ret with "HΦ"); encode.
  Qed.

  (** * EIntMod : expr → expr → expr *)

  Lemma imp_EIntMod {ζ} η e1 e2 (Φ1 Φ2 : Z → iProp Σ) Φ :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ i j, Φ1 i -∗ Φ2 j -∗
              ⌜representable i⌝ ∧ ⌜representable j⌝ ∧ ⌜j ≠ 0⌝ ∧ Φ (i `rem` j)) -∗
    EWP eval η (EIntMod e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin /=". simpl_eval.
    iApply (imp_bind_par with "[H1] [H2]").
    { iApply (imp_as_int with "H1"). }
    { iApply (imp_as_int with "H2"). }
    iIntros (i j) "HΦ1 HΦ2 !>".
    iDestruct ("Hjoin" with "HΦ1 HΦ2")
      as "(%Hrepr1 & %Hrepr2 & %Hneq & HΦ)".
    rewrite /continue /=.
    iApply imp_bind.
    { rewrite /check_div_by_zero /=.
      rewrite eq_repr_repr; try representable.
      rewrite (iffRL (Z.eqb_neq j 0) Hneq).
      iApply imp_ret; first encode.
      by instantiate (1 := (λ _, True)%I). }
    iIntros ([]) "_".
    iApply (imp_ret with "HΦ"); encode.
  Qed.

  (** * EIntLand : expr → expr → expr *)
  (** * EIntLor : expr → expr → expr *)
  (** * EIntLxor : expr → expr → expr *)
  (** * EIntLnot : expr → expr *)
  (** * EIntLsl : expr → expr → expr *)
  (** * EIntLsr : expr → expr → expr *)
  (** * EIntAsr : expr → expr → expr *)
  (** * EFloat : float → expr *)
  (** * EChar : char → expr *)
  (** * EString : string → expr *)
  (** * EOpPhysEq : expr → expr → expr *)

  Lemma imp_EOpPhysEq_loc {ζ} η e1 e2 (Φ1 Φ2 : loc → iProp Σ) (Φ : bool → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ l1 l2, Φ1 l1 -∗ Φ2 l2 -∗ Φ (locations.eqb l1 l2)) -∗
    EWP eval η (EOpPhysEq e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 Hjoin /=". simpl_eval.
    iApply (imp_bind_par with "H1 H2").
    iIntros (l1 l2) "HΦ1 HΦ2 !>".
    rewrite /phys_eq_val /=.
    iApply (imp_bind with "[]").
    { iApply imp_ret; first reflexivity.
      instantiate (1 := (λ b, ⌜b = locations.eqb l1 l2⌝)%I). done. }
    iIntros (b) "->". iApply (imp_ret with "(Hjoin HΦ1 HΦ2)"). encode.
  Qed.

  (* Physical equality of two (non-inline) records. Unlike [loc], deciding
     physical equality of a [VRecord] requires consulting the store (to
     check that at least one operand is a mutable block), hence the extra
     [blockTag ... DfracDiscarded t] knowledge threaded through [Φ1]/[Φ2]. *)
  Lemma imp_EOpPhysEq_record {ζ} η e1 e2 (Φ1 Φ2 : record → iProp Σ) (Φ : bool → iProp Σ) t1 t2 :
    t1 = Mut ∨ t2 = Mut →
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l, Φ1 l ∗ blockTag l DfracDiscarded t1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l, Φ2 l ∗ blockTag l DfracDiscarded t2 }} -∗
    ▷ (∀ l1 l2, Φ1 l1 -∗ Φ2 l2 -∗ Φ (locations.eqb l1 l2)) -∗
    EWP eval η (EOpPhysEq e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hmut) "H1 H2 Hjoin /=". simpl_eval.
    iApply (imp_bind_par with "H1 H2").
    iIntros (l1 l2) "[HΦ1 Hb1] [HΦ2 Hb2] !>".
    rewrite /phys_eq_val /=.
    iApply (imp_bind with "[Hb1 Hb2]").
    { iDestruct "Hb1" as (ls1) "Hb1".
      iDestruct "Hb2" as (ls2) "Hb2".
      iPoseProof (imp_load_block with "Hb1") as "Hb1'".
      iPoseProof (imp_load_block with "Hb2") as "Hb2'".
      iApply (imp_bind_par with "Hb1' Hb2'").
      iIntros ([t1' ls1'] [t2' ls2']) "(-> & -> & _) (-> & -> & _) !>".
      destruct t1, t2; rewrite /=;
        [ iApply imp_ret; first reflexivity;
          instantiate (1 := (λ b, ⌜b = locations.eqb l1 l2⌝)%I); done
        | iApply imp_ret; first reflexivity; done
        | iApply imp_ret; first reflexivity; done
        | exfalso; destruct Hmut as [Hc | Hc]; discriminate Hc ]. }
    iIntros (b) "->". iApply (imp_ret with "(Hjoin HΦ1 HΦ2)"). encode.
  Qed.

  (* Physical equality of two references (see [field_loc.v]). *)
  Lemma imp_EOpPhysEq_ref {ζ} η e1 e2 (Φ1 Φ2 : record → iProp Σ) (Φ : bool → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ r, Φ1 r ∗ is_ref r }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ r, Φ2 r ∗ is_ref r }} -∗
    ▷ (∀ r1 r2, Φ1 r1 -∗ Φ2 r2 -∗ Φ (locations.eqb r1 r2)) -∗
    EWP eval η (EOpPhysEq e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He1 He2 Hk".
    iApply (imp_EOpPhysEq_record _ _ _ Φ1 Φ2 _ Mut Mut with "[He1] [He2] Hk");
      first by left.
    all: iApply (imp_wand with "[-]"); [ iAssumption | ].
    all: rewrite /is_ref; iIntros (r) "($ & $ & _)".
  Qed.

  (** * EOpEq : expr → expr → expr *)

  Lemma imp_EOpEq `{Encode A1, Encode A2} {Φ : bool → iProp Σ} {ζ} η e1 e2 Φ1 Φ2 :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ (v1 : A1) (v2 : A2),
         Φ1 v1 -∗ Φ2 v2 -∗
         EWP eq_val #v1 #v2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (EOpEq e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 P". simpl_eval.
    iApply (imp_bind_par with "H1 H2").
    iIntros (v1 v2) "HΦ1 HΦ2 !>".
    rewrite /continue /=.
    iApply (imp_bind with "[-]").
    iApply ("P" with "HΦ1 HΦ2").
    iIntros (b) "HΦ".
    iApply (imp_ret (VBool b) b with "HΦ"). encode.
  Qed.

  Lemma imp_EOpEq_Z {ζ} η e1 e2 (i j : Z) :
    representable i ->
    representable j ->
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = i⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = j⌝ }} -∗
    EWP eval η (EOpEq e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ b, ⌜b = (i =? j)%Z⌝ }}.
  Proof.
    iIntros (Hn1 Hn2) "H1 H2".
    iApply (imp_EOpEq with "H1 H2").
    iIntros "!>" (v1 v2) "-> ->".
    iApply imp_ret; first encode.
    iPureIntro. rewrite eq_repr_repr; try representable.
  Qed.

  (** * EOpNe : expr → expr → expr *)

  Lemma imp_EOpNe `{Encode A1, Encode A2} {Φ : bool → iProp Σ} {ζ} η e1 e2 Φ1 Φ2 :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ (v1 : A1) (v2 : A2),
         Φ1 v1 -∗ Φ2 v2 -∗
         EWP ne_val #v1 #v2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (EOpNe e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 P". simpl_eval.
    iApply (imp_bind_par with "H1 H2").
    iIntros (v1 v2) "HΦ1 HΦ2 !>".
    rewrite /continue /=.
    iApply (imp_bind with "[-]").
    iApply ("P" with "HΦ1 HΦ2").
    iIntros (b) "HΦ".
    iApply (imp_ret (VBool b) b with "HΦ"). encode.
  Qed.

  Lemma imp_EOpNe_Z {ζ} η e1 e2 (i j : Z) :
    representable i ->
    representable j ->
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = i⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = j⌝ }} -∗
    EWP eval η (EOpNe e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ b, ⌜b ≠ (i =? j)%Z⌝ }}.
  Proof.
    iIntros (Hn1 Hn2) "H1 H2".
    iApply (imp_EOpNe with "H1 H2").
    iIntros "!>" (v1 v2) "-> ->".
    iApply imp_ret; first encode.
    iPureIntro. rewrite eq_repr_repr; try representable.
    case (i =? j); auto.
  Qed.

  (** * EOpLt : expr → expr → expr *)

  Lemma imp_EOpLt `{Encode A1, Encode A2} {Φ : bool → iProp Σ} {ζ} η e1 e2 Φ1 Φ2 :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ (v1 : A1) (v2 : A2),
         Φ1 v1 -∗ Φ2 v2 -∗
         EWP lt_val #v1 #v2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (EOpLt e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 P". simpl_eval.
    iApply (imp_bind_par with "H1 H2").
    iIntros (v1 v2) "HΦ1 HΦ2 !>".
    rewrite /continue /=.
    iApply (imp_bind with "[-]").
    iApply ("P" with "HΦ1 HΦ2").
    iIntros (b) "HΦ".
    iApply (imp_ret (VBool b) b with "HΦ"). encode.
  Qed.

  Lemma imp_EOpLt_Z {ζ} η e1 e2 (i j : Z) :
    representable i ->
    representable j ->
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = i⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = j⌝ }} -∗
    EWP eval η (EOpLt e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ b, ⌜b = (i <? j)%Z⌝ }}.
  Proof.
    iIntros (Hn1 Hn2) "H1 H2".
    iApply (imp_EOpLt with "H1 H2").
    iIntros "!>" (v1 v2) "-> ->".
    iApply imp_ret; first encode.
    iPureIntro. rewrite lt_repr_repr; try representable.
  Qed.

  (* If we don't care about the value of the result for functional
     correctness, we can drop the representability assumptions in
     exchange for loosing any information about the result. *)

  Lemma imp_EOpLt_Z_weak {ζ} η e1 e2 (i j : Z) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = i⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = j⌝ }} -∗
    EWP eval η (EOpLt e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (b : bool), True }}.
  Proof.
    iIntros "H1 H2".
    iApply (imp_EOpLt with "H1 H2").
    iIntros "!>" (v1 v2) "-> ->".
    iApply imp_ret; first encode. done.
  Qed.

  (** * EOpLe : expr → expr → expr *)

  Lemma imp_EOpLe `{Encode A1, Encode A2} {Φ : bool → iProp Σ} {ζ} η e1 e2 Φ1 Φ2 :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ (v1 : A1) (v2 : A2),
         Φ1 v1 -∗ Φ2 v2 -∗
         EWP le_val #v1 #v2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (EOpLe e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 P". simpl_eval.
    iApply (imp_bind_par with "H1 H2").
    iIntros (v1 v2) "HΦ1 HΦ2 !>".
    rewrite /continue /=.
    iApply (imp_bind with "[-]").
    iApply ("P" with "HΦ1 HΦ2").
    iIntros (b) "HΦ".
    iApply (imp_ret (VBool b) b with "HΦ"). encode.
  Qed.

  Lemma imp_EOpLe_Z {ζ} η e1 e2 (i j : Z) :
    representable i ->
    representable j ->
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = i⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = j⌝ }} -∗
    EWP eval η (EOpLe e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ b, ⌜b = (i <=? j)%Z⌝ }}.
  Proof.
    iIntros (Hn1 Hn2) "H1 H2".
    iApply (imp_EOpLe with "H1 H2").
    iIntros "!>" (v1 v2) "-> ->".
    iApply imp_ret; first encode.
    iPureIntro. rewrite lt_repr_repr; try representable.
    rewrite Z.ltb_antisym.
    case (i <=? j); auto.
  Qed.

  (** * EOpGt : expr → expr → expr *)

  Lemma imp_EOpGt `{Encode A1, Encode A2} {Φ : bool → iProp Σ} {ζ} η e1 e2 Φ1 Φ2 :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ (v1 : A1) (v2 : A2),
         Φ1 v1 -∗ Φ2 v2 -∗
         EWP gt_val #v1 #v2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (EOpGt e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 P". simpl_eval.
    iApply (imp_bind_par with "H1 H2").
    iIntros (v1 v2) "HΦ1 HΦ2 !>".
    rewrite /continue /=.
    iApply (imp_bind with "[-]").
    iApply ("P" with "HΦ1 HΦ2").
    iIntros (b) "HΦ".
    iApply (imp_ret (VBool b) b with "HΦ"). encode.
  Qed.

  Lemma imp_EOpGt_Z {ζ} η e1 e2 (i j : Z) :
    representable i ->
    representable j ->
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = i⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = j⌝ }} -∗
    EWP eval η (EOpGt e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ b, ⌜b = (i >? j)%Z⌝ }}.
  Proof.
    iIntros (Hn1 Hn2) "H1 H2".
    iApply (imp_EOpGt with "H1 H2").
    iIntros "!>" (v1 v2) "-> ->".
    iApply imp_ret; first encode.
    iPureIntro. rewrite lt_repr_repr; try representable.
    by rewrite Z.gtb_ltb.
  Qed.

  Lemma imp_EOpGt_Z_weak {ζ} η e1 e2 (i j : Z) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = i⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = j⌝ }} -∗
    EWP eval η (EOpGt e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (b : bool), True }}.
  Proof.
    iIntros "H1 H2".
    iApply (imp_EOpGt with "H1 H2").
    iIntros "!>" (v1 v2) "-> ->".
    iApply imp_ret; first encode. done.
  Qed.

  (** * EOpGe : expr → expr → expr *)

  Lemma imp_EOpGe `{Encode A1, Encode A2} {Φ : bool → iProp Σ} {ζ} η e1 e2 Φ1 Φ2 :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ (v1 : A1) (v2 : A2),
         Φ1 v1 -∗ Φ2 v2 -∗
         EWP ge_val #v1 #v2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (EOpGe e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 P". simpl_eval.
    iApply (imp_bind_par with "H1 H2").
    iIntros (v1 v2) "HΦ1 HΦ2 !>".
    rewrite /continue /=.
    iApply (imp_bind with "[-]").
    iApply ("P" with "HΦ1 HΦ2").
    iIntros (b) "HΦ".
    iApply (imp_ret (VBool b) b with "HΦ"). encode.
  Qed.

  Lemma imp_EOpGe_Z {ζ} η e1 e2 (i j : Z) :
    representable i ->
    representable j ->
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = i⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ n, ⌜n = j⌝ }} -∗
    EWP eval η (EOpGe e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ b, ⌜b = (i >=? j)%Z⌝ }}.
  Proof.
    iIntros (Hn1 Hn2) "H1 H2".
    iApply (imp_EOpGe with "H1 H2").
    iIntros "!>" (v1 v2) "-> ->".
    iApply imp_ret; first encode.
    iPureIntro. rewrite lt_repr_repr; try representable.
    rewrite Z.geb_leb Z.ltb_antisym.
    case (j <=? i); auto.
  Qed.

  (** * ELet : list binding → expr → expr *)

  (* Intermediate lemma: using [eval_bindings] hypothesis *)
  Lemma imp_ELet `{Encode A} {Φ : A → iProp Σ} {ζ} η bs e Φ1 :
    EWP eval_bindings η bs @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    (∀ (δ : env), Φ1 δ -∗ EWP eval (δ ++ η) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (ELet bs e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hbindings P /=". simpl_eval.
    iApply (imp_bind _ _ (λ (δ : env), eval (δ ++ η) e) with "Hbindings").
    iIntros (δ) "Hδ". change (♯ δ ++ η) with (δ ++ η).
    iApply ("P" with "Hδ").
  Qed.

  Lemma imp_bindings_singleton `{Encode A} {ζ} {Φ : env → iProp Σ} (Φ1 : A → iProp Σ) {η p e} φs :
    EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    (∀ x, Φ1 x -∗ ⌜pattern η nil p #x (φs #x) False⌝) -∗
    (∀ x δ, Φ1 x -∗ ⌜φs #x δ⌝ -∗ Φ δ) -∗
    EWP eval_bindings η [ Binding p e ] @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 P HΦ /=".
    iApply (imp_wand with "[H1 P]").
    iApply (imp_bindings_cons with "H1 P").
    { iApply imp_bindings_nil. }
    iIntros (δ) "(%a & %η' & %δ' & -> & HΦ1 & Hφs & ->)".
    rewrite app_nil_r.
    iApply ("HΦ" with "HΦ1 Hφs").
  Qed.

  (* Specialized [ELet] lemmas *)

  (* TODO: Have *_singleton *_cons lemmas about relevant expr constructs *)
  Corollary imp_ELet_singleton `{Encode A, Encode B} {Φ : A → iProp Σ} {ζ} {Φ1 : B → iProp Σ} {η p e e'} φ :
    EWP eval η e' @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    (∀ (x : B), Φ1 x -∗ ⌜pattern η nil p (#x) (φ #x) False⌝) -∗
    (∀ x δ, Φ1 x -∗ ⌜φ #x δ⌝ -∗
            EWP eval (δ ++ η) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (ELet [ Binding p e' ] e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He' HP He".
    iApply (imp_ELet with "[He' HP He]").
    iApply (imp_bindings_singleton with "He' HP He").
    iIntros (δ) "$".
  Qed.

  (* Special case of [let x = e' in e] *)
  Lemma imp_ELet_var `{Encode A, Encode B} {ζ} {Φ : A → iProp Σ} (Φ' : B → iProp Σ) {η x e e'} :
    EWP eval η e' @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ' }} -∗
    (∀ b, Φ' b -∗ EWP eval ((x, #b) :: η) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (ELet [Binding (PVar x) e'] e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H P".
    iApply (imp_ELet_singleton with "H").
    { iIntros (v) "_".
      iPureIntro.
      apply pat_PVar.
      instantiate (1 := λ v l, l = [(x, v)]).
      reflexivity. }
    iIntros (v δ) "HΦ ->".
    iApply ("P" with "HΦ").
  Qed.

  (* Special case of [let _ = e' in e] *)
  Lemma imp_ELet_wild `{Encode A, Encode B} {ζ} {Φ : A → iProp Σ} (R : iProp Σ) {η e e'} :
    EWP eval η e' @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (_ : B), R }} -∗
    (R -∗ EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (ELet [Binding PAny e'] e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H P".
    iApply (imp_ELet_singleton with "H").
    { iIntros (v) "_".
      iPureIntro. apply pat_PAny.
      instantiate (1 := λ v l, l = []).
      reflexivity. }
    iIntros (v δ) "HR ->".
    iApply ("P" with "HR").
  Qed.

  (* Special case of [let (x, y) = e' in e] *)
  Lemma imp_ELet_pair `{Encode C, Encode A, Encode B} {ζ} {Φ : C → iProp Σ} (Φ' : τ[A; B] → iProp Σ) {η x y e e'} :
    EWP eval η e' @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ' }} -∗
    (∀ a b, Φ' (a, b) -∗ EWP eval ((y, #b) :: (x, #a) :: η) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (ELet [Binding (PTuple [PVar x; PVar y]) e'] e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H P".
    iApply (imp_ELet_singleton with "H").
    { iIntros ([a b]) "_".
      iPureIntro. eapply pat_PTuple. encode.
      eapply pats_PCons_unary_false.
      apply pat_PVar.
      eapply pats_PCons_unary_false.
      apply pat_PVar.
      eapply pats_PNil.
      instantiate (1 := λ v l, match v with
                               | VTuple [a; b] => l = [(y, b); (x, a)]
                               | _ => False
                               end).
      reflexivity. }
    iIntros ([a b] δ) "HΦ ->".
    iApply ("P" with "HΦ").
  Qed.

  (* Special case of [let x = e1 and y = e2 in e]. *)
  Lemma imp_ELet_var2 `{HA : Encode A} `{HB : Encode B} `{HC : Encode C}
      {ζ} {Φ : A → iProp Σ} (Φ1 : B → iProp Σ) (Φ2 : C → iProp Σ) {η x y e e1 e2} :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    (∀ b c, Φ1 b -∗ Φ2 c -∗ EWP eval ((x, #b) :: (y, #c) :: η) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (ELet [Binding (PVar x) e1; Binding (PVar y) e2] e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 P".
    iApply (imp_ELet with "[H1 H2]").
    { iApply (imp_bindings_cons with "H1").
      { iIntros (b) "_". iPureIntro. apply pat_PVar.
        instantiate (1 := λ (v : B) (l : env), l = [(x, #v)]). reflexivity. }
      iApply (imp_bindings_singleton (Φ:=(λ δ, ∃ c, Φ2 c ∗ ⌜δ = [(y, #c)]⌝)%I) with "H2").
      { iIntros (c) "_". iPureIntro. apply pat_PVar.
        instantiate (1 := λ v l, l = [(y, v)]). reflexivity. }
      iIntros (c δ) "HΦ2 %Hδ". iExists c. iFrame "HΦ2". iPureIntro. exact Hδ. }
    iIntros (δ) "(%b & %η' & %δ' & -> & HΦ1 & -> & %c & HΦ2 & ->)".
    iApply ("P" with "HΦ1 HΦ2").
  Qed.

  (** * ELetRec : list rec_binding → expr → expr *)

  Lemma imp_ELetRec `{Encode A} {Φ : A → iProp Σ} {ζ} η bs e :
    let δ := eval_rec_bindings η bs in
    EWP eval (δ ++ η) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    EWP eval η (ELetRec bs e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    simpl_eval; auto.
  Qed.

  (** * ESeq : expr → expr → expr *)

  Lemma imp_ESeq `{Encode A} {Φ : A → iProp Σ} {ζ} (Φ1 : unit → iProp Σ) η e1 e2 :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    (Φ1 () -∗ EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (ESeq e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He1 He2 /=". simpl_eval.
    iApply (imp_bind with "He1 [He2]").
    iIntros ([]). iExact "He2".
  Qed.

  (** * EIfThen : expr → expr → expr *)

  Lemma imp_EIfThen {Φ : unit → iProp Σ} {ζ} η eb e1 (Φb : bool → iProp Σ) :
    EWP eval η eb @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φb }} -∗
    (∀ b, Φb b -∗
          if b then EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
          else Φ ()) -∗
    EWP eval η (EIfThen eb e1) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hb He /=". simpl_eval.
    iApply (imp_bind with "[Hb]").
    { iApply (imp_as_bool with "Hb"). }
    iIntros (b) "Hb". change (♯b) with b.
    iSpecialize ("He" with "Hb").
    destruct b.
    - iApply "He".
    - iApply (imp_ret VUnit ()); auto.
  Qed.

  Lemma imp_EIfThen2 {Φ : unit → iProp Σ} {ζ} η eb e1 (Φb : bool → iProp Σ) :
    EWP eval η eb @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φb }} -∗
    (Φb true -∗
     EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (Φb false -∗ Φ ()) -∗
    EWP eval η (EIfThen eb e1) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hb He".
    iApply (imp_EIfThen with "Hb").
    iIntros ([|]) "HΦb";
      iApply ("He" with "HΦb").
  Qed.

  (** * EIfThenElse : expr → expr → expr → expr *)

  Lemma imp_EIfThenElse `{Encode A} {Φ : A → iProp Σ} {ζ} η eb e1 e2 (Φb : bool → iProp Σ) :
    EWP eval η eb @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φb }} -∗
    (∀ b, Φb b -∗
          if b then EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
          else EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (EIfThenElse eb e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hb He /=". simpl_eval.
    iApply (imp_bind with "[Hb]").
    { iApply (imp_as_bool with "Hb"). }
    iIntros (b) "Hb". change (♯b) with b.
    iSpecialize ("He" with "Hb").
    destruct b; iApply "He".
  Qed.

  Lemma imp_EIfThenElse2 `{Encode A} {Φ : A → iProp Σ} {ζ} η eb e1 e2 (Φb : bool → iProp Σ) :
    EWP eval η eb @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φb }} -∗
    (Φb true -∗
     EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (Φb false -∗
     EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (EIfThenElse eb e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hb He /=".
    iApply (imp_EIfThenElse with "Hb").
    iIntros ([|]) "HΦb"; iApply ("He" with "HΦb").
  Qed.

  (** * EMatch : expr → list branch → expr *)

  Lemma imp_EHandler `{Encode A, Encode A'} {Φ : A → iProp Σ} {ζ} Ψ' ζ' (Φ' : A' → iProp Σ) η e bs :
    EWP eval η e @ E <|Ψ'|> ⟨⟨ ζ' ⟩⟩ {{ Φ' }} -∗
    deep_handler_spec E Ψ' ζ' Φ' η bs Ψ ζ Φ -∗
    EWP eval η (EMatch e bs) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He Hbs"; simpl_eval.
    iApply (imp_deep_handler with "He Hbs").
  Qed.

  Lemma imp_EMatch2 `{Encode A, Encode A'} {Φ : A → iProp Σ} {ζ} ζ' (Φ' : A' → iProp Σ) η e bs :
    EWP eval η e @ E ⟨⟨ ζ' ⟩⟩ {{ Φ' }} -∗
    (∀ a : A', Φ' a -∗ ▷ EWP eval_branches η (O2Ret #a) bs @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    (∀ e0 : exn, ζ' e0 -∗ ▷ EWP eval_branches η (O2Throw e0) bs @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (EMatch e bs) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He Hbs"; simpl_eval.
    iApply (imp_deep_handler with "He").
    iApply (prove_deep_handler_spec).
    iSplit; last iSplit.
    - iDestruct "Hbs" as "[$ _]".
    - iDestruct "Hbs" as "[_ $]".
    - iIntros (v k) "HProt".
      by rewrite /prot upcl_bottom.
  Qed.

  Lemma imp_EMatch `{Encode A, Encode A'} {Φ : A → iProp Σ} {ζ} (Φ' : A' → iProp Σ) η e bs :
    EWP eval η e @ E {{ Φ' }} -∗
    (∀ a : A', Φ' a -∗ ▷ EWP eval_branches η (O2Ret #a) bs @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (EMatch e bs) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He Hbs"; simpl_eval.
    iApply (imp_deep_handler with "He").
    iApply (prove_deep_handler_spec).
    iSplit; last iSplit.
    - iApply "Hbs".
    - iIntros (? []).
    - iIntros (v k) "HProt".
      by rewrite /prot upcl_bottom.
  Qed.

  (** * ERaise : expr → expr *)

  Lemma imp_ERaise `{Encode A} {Φ : A → iProp Σ} {ζ} η e :
    EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ζ }} -∗
    EWP eval η (ERaise e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H". simpl_eval.
    iApply (imp_bind with "H").
    iIntros (ex) "Hζ".
    by iApply (imp_throw _ ex with "Hζ").
  Qed.

  (** * EWhile : expr → expr → expr *)

  Lemma imp_EWhile {ζ} (I : bool → iProp Σ) η e body :
    I true -∗
    □ (I true -∗ EWP (eval η e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ I }}) -∗
    □ (I true -∗ EWP (eval η body) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ _ : unit, I true }}) -∗
    EWP eval η (EWhile e body) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ _ : unit, I false }}.
  Proof.
    iIntros "HP #He #Hbody".
    simpl_eval.
    iLöb as "IH".
    iApply (imp_bind I with "[HP]").
    { iApply imp_as_bool. iApply ("He" with "HP"). }
    iIntros (b) "HP_b".
    destruct b; simpl.
    - iApply (imp_bind (λ _ : unit, I true)%I with "[HP_b]").
      { iApply ("Hbody" with "HP_b"). }
      iIntros (_) "HP_true".
      iApply imp_please. iNext. simpl_eval.
      iApply "IH". iExact "HP_true".
    - iApply (imp_ret VUnit ()); first encode.
      iApply "HP_b".
  Qed.

  (** * EFor : var → expr → expr → expr → expr *)

  Lemma imp_EFor {ζ} (I : Z → iProp Σ) (i j : Z) x e1 e2 e  η :
    representable i →
    representable j →
    EWP (eval η e1) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ i', ⌜i' = i⌝ }} -∗
    EWP (eval η e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ j', ⌜j' = j⌝ }} -∗
    I i -∗
    (□ ∀ i' : Z,
       ⌜i ≤ i' ≤ j⌝ -∗ I i' -∗
       EWP eval (x ~> #i'; η) e @ E <| Ψ |> ⟨⟨ ζ ⟩⟩
         {{ _ : (), I (i' + 1) }}) -∗
    EWP eval η (EFor x e1 e2 e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ (_ : unit), I ((j + 1) `max` i)%Z }}.
  Proof.
    iIntros (Hrepr1 Hrepr2) "He1 He2 HI He". simpl_eval.
    iApply (imp_bind_par with "[He1] [He2]").
    { iApply (imp_as_int with "He1"). }
    { iApply (imp_as_int with "He2"). }
    iIntros (??) "-> -> !>".
    rewrite /continue /=.
    iApply (imp_loop with "HI He"); assumption.
  Qed.

  (** * EAssertFalse : expr *)

  Lemma impEAssertFalse {ζ} η :
    False -∗
    EWP eval η EAssertFalse @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (_ : unit), False }}.
  Proof.
    iIntros "HF". simpl_eval.
    rewrite /assertion_failure.
    iDestruct "HF" as "[]".
  Qed.

  (** * EAssert : expr → expr *)

  Lemma imp_EAssert {R : iProp Σ} {ζ} η e :
    R ∧ EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ b, ⌜b = true⌝ ∗ R }} -∗
    EWP eval η (EAssert e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (_ : unit), R }}.
  Proof.
    iIntros "H /=". simpl_eval.
    iApply imp_choose.
    iSplit.
    - iApply imp_ret; first encode.
      iDestruct "H" as "[$ _]".
    - iDestruct "H" as "[_ H]".
      iApply (imp_bind with "[H]").
      { iApply (imp_as_bool with "H"). }
      iIntros (?) "[-> HR]".
      simpl.
      iApply (imp_ret VUnit ()); auto.
  Qed.

  (** * ELetSitem : mexpr → expr → expr *)

  Lemma imp_ELetOpen `{Encode A} {Φ : A → iProp Σ} {ζ} (Φ' : env → iProp Σ) η me e :
    EWP eval_mexpr η me @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ' }} -∗
    (∀ δ, Φ' δ -∗ EWP eval (δ ++ η) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP eval η (ELetSitem (IOpen me) e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hme He". simpl_eval. rewrite bind_bind.
    iApply (imp_bind _ _ (λ δ, eval (δ ++ η) e) with "[Hme]").
    { iApply (imp_as_struct with "Hme"). }
    iApply "He".
  Qed.

  (** * ELoad : expr → expr *)

  (* [ELoad] reads a field location (see [EAtomicLoc]). The rules for
     references, which are one-field records, are in [ref_rules.v]. *)

  Lemma imp_ELoad2 `{Encode A} {Φ : A → iProp Σ} {ζ} (Φ1 : loc → iProp Σ) η e :
    EWP (eval η e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    (∀ l, Φ1 l -∗ ∃ q a, ▷ l ↦ₗ{q} #a ∗ ▷ (l ↦ₗ{q} #a -∗ Φ a)) -∗
    EWP eval η (ELoad e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He P". simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_loc with "He"). }
    iIntros (l) "HΦ1".
    iDestruct ("P" with "HΦ1") as "(%q & %a & Hl & P)".
    change (♯l) with l.
    iApply (imp_load' with "Hl P").
  Qed.

  Lemma imp_ELoad `{Encode A} {ζ} η e l q (a : A) :
    ▷ l ↦ₗ{q} #a -∗
    EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l', ⌜l' = l⌝ }} -∗
    EWP eval η (ELoad e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ v, ⌜v = a⌝ ∗ l ↦ₗ{q} #a }}.
  Proof.
    iIntros "Hl He /=".
    iApply (imp_ELoad2 with "He").
    iIntros (?) "->". iFrame.
    iIntros "!> $". auto.
  Qed.

  (** * ECAS : expr → expr → expr → expr *)

  Lemma imp_ECAS2' `{PhysEqDec A} {Φ : bool → iProp Σ} {ζ} η e1 e2 e3 (Φ1 : loc → iProp Σ) (Φ2 Φ3 : A → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    EWP eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ3 }} -∗
    (∀ l seen a,
       Φ1 l -∗ Φ2 seen -∗ Φ3 a -∗
       ▷ ∃ v1, l ↦ₗ #v1 ∗
               ▷ (l ↦ₗ (if phys_eq_val_ v1 seen then #a else #v1) -∗ Φ (phys_eq_val_ v1 seen))) -∗
    EWP eval η (ECAS e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 H3 P /=". simpl_eval.
    iApply (imp_bind_par (A1:=loc*A) with "[H1 H2] H3").
    { iApply (imp_par with "[H1] H2").
      { iApply (imp_as_loc with "H1"). } }
    iIntros ((l & x) y) "(H1 & H2) H3".
    iSpecialize ("P" with "H1 H2 H3").
    iNext. iDestruct "P" as "(%v & Hl & HΦ)".
    rewrite /continue /=.
    iApply (imp_cas with "Hl HΦ").
  Qed.

  Lemma imp_ECAS2 `{PhysEqDec A} {Φ : bool → iProp Σ} {ζ} (l : loc) η e1 e2 e3 (Φ2 Φ3 : A → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l', ⌜l' = l⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    EWP eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ3 }} -∗
    (∀ seen a,
       Φ2 seen -∗ Φ3 a -∗
       ▷ ∃ v1, l ↦ₗ #v1 ∗
               ▷ (l ↦ₗ (if phys_eq_val_ v1 seen then #a else #v1) -∗ Φ (phys_eq_val_ v1 seen))) -∗
    EWP eval η (ECAS e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 H3 P /=".
    iApply (imp_ECAS2' with "H1 H2 H3").
    iIntros (? seen a) "-> HΦ2 HΦ3".
    iApply ("P" with "HΦ2 HΦ3").
  Qed.

  Lemma imp_ECAS' `{PhysEqDec A} {Φ : bool → iProp Σ} {ζ} (l : loc) v η e1 e2 e3 (Φ2 Φ3 : A → iProp Σ) :
    l ↦ₗ #v -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l', ⌜l' = l⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    EWP eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ3 }} -∗
    (∀ seen a,
       Φ2 seen -∗ Φ3 a -∗
       ▷ ▷ (l ↦ₗ (if phys_eq_val_ v seen then #a else #v) -∗ Φ (phys_eq_val_ v seen))) -∗
    EWP eval η (ECAS e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl H1 H2 H3 P".
    iApply (imp_ECAS2 with "H1 H2 H3").
    iIntros (seen a) "HΦ2 HΦ3".
    iSpecialize ("P" with "HΦ2 HΦ3").
    iFrame.
  Qed.

  Lemma imp_ECAS `{PhysEqDec A} {ζ} (l : loc) (v v' : A) η e1 e2 e3 (Φ2 Φ3 : A → iProp Σ) :
    l ↦ₗ #v -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l', ⌜l' = l⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    EWP eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ v, ⌜v = v'⌝ }} -∗
    EWP eval η (ECAS e1 e2 e3) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{
          λ b, ∃ seen, Φ2 seen ∗ ⌜b = phys_eq_val_ v seen⌝ ∗ l ↦ₗ (if b then #v' else #v)
      }}.
  Proof.
    iIntros "Hl H1 H2 H3".
    iApply (imp_ECAS' with "Hl H1 H2 H3").
    iIntros (seen ?) "HΦ2 ->".
    iIntros "!> !> $".
    by iFrame.
  Qed.

  (** * EFAA : expr → expr → expr *)

  Lemma imp_EFAA' {Φ : Z → iProp Σ} {ζ} (l : loc) (j : Z) η e1 e2 (Φ2 : Z → iProp Σ) :
    l ↦ₗ #j -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l', ⌜l' = l⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    (∀ i,
       Φ2 i -∗
       ▷ ▷ (l ↦ₗ #(j + i) -∗ Φ j)) -∗
    EWP eval η (EFAA e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl H1 H2 P". simpl_eval.
    iApply (imp_bind_par with "[H1] [H2]").
    { iApply (imp_as_loc with "H1"). }
    { iApply (imp_as_int with "H2"). }
    iIntros (? i) "-> H2".
    iSpecialize ("P" with "H2").
    iApply (imp_faa with "Hl P").
  Qed.

  Lemma imp_EFAA {Φ : Z → iProp Σ} {ζ} (l : loc) (i j : Z) η e1 e2 :
    l ↦ₗ #j -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l', ⌜l' = l⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ i', ⌜i' = i⌝ }} -∗
    EWP eval η (EFAA e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ j', ⌜j' = j⌝ ∗ l ↦ₗ #(j + i) }}.
  Proof.
    iIntros "Hl H1 H2".
    iApply (imp_EFAA' with "Hl H1 H2").
    iIntros (?) "-> !> !> $ //".
  Qed.

  (** * ENewProph : expr *)

  Lemma imp_ENewProph {Φ : proph_id → iProp Σ} {ζ} η :
    ▷ (∀ (p : proph_id) (pvs : list (val * val)), proph p pvs -∗ Φ p) -∗
    EWP eval η ENewProph @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H". simpl_eval.
    rewrite /new_proph bind_stop_gen.
    iApply ewp_new_proph. iIntros "!>" (p pvs) "Hp".
    rewrite /continue /= bind_ret.
    iApply imp_ret; [ encode | by iApply "H" ].
  Qed.

  (** * EResolve : expr → path → proph_arg → expr *)

  (* The prophecy and the auxiliary argument are not expressions: they are
     read off the environment, in no step and with no effect. So, as in
     [imp_EPath], they are side conditions on the lookup, not premises about
     an evaluation. *)

  (* The general case: the annotated expression is not one of the
     single-step operations (the four atomic ones and a field read), so the
     resolution happens one step after it returns. See [CReturn] in
     code.v. *)

  Lemma imp_EResolve {A} `{Encode A} {Φ : A → iProp Σ} {ζ}
      η e (ep : path) (ev : proph_arg) (p : proph_id) (v : val) pvs (Φe : A → iProp Σ) :
    match e with
    | ELoad _ | ERecordAccess _ _ | EExchange _ _ | ECAS _ _ _ | EFAA _ _ => False
    | _ => True
    end →
    lookup_path η ep = Some #p →
    eval_proph_arg η ev = Some v →
    proph p pvs -∗
    EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φe }} -∗
    (∀ (a : A) pvs', ⌜pvs = (♯a, v) :: pvs'⌝ -∗ proph p pvs' -∗ Φe a -∗ Φ a) -∗
    EWP eval η (EResolve e ep ev) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hne Hp Hv) "Hproph He Hcont". simpl_eval.
    rewrite (bind_proph_args Hp Hv).
    (* [eval] dispatches on the annotated expression's syntax, so the
       side condition has to be discharged one constructor at a time; the
       four single-step operations are the ones it rules out. *)
    destruct e; try contradiction Hne.
    all: iApply (imp_bind with "He"); iIntros (res) "HΦe";
         iApply (ewp_resolve_return with "Hproph");
         iIntros (pvs2) "%Heq2 Hp2";
         rewrite /continue /=;
         iApply imp_ret; [ encode | by iApply ("Hcont" with "[//] Hp2 HΦe") ].
  Qed.

  (* The four fused cases. Here the resolution happens at the operation's
     own step, so the prediction's head is available at the linearization
     point rather than one step after it. Each mirrors the corresponding
     unannotated rule, with the operation's postcondition extended by the
     prophecy's head. *)

  Lemma imp_EResolve_ELoad {A} `{Encode A} {Φ : A → iProp Σ} {ζ}
      η e1 (ep : path) (ev : proph_arg) (l : loc) (p : proph_id) (v : val) q (a : A) pvs :
    lookup_path η ep = Some #p →
    eval_proph_arg η ev = Some v →
    ▷ l ↦ₗ{q} #a -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l', ⌜l' = l⌝ }} -∗
    proph p pvs -∗
    (∀ pvs', ⌜pvs = (♯a, v) :: pvs'⌝ -∗ proph p pvs' -∗ l ↦ₗ{q} #a -∗ Φ a) -∗
    EWP eval η (EResolve (ELoad e1) ep ev) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hp Hv) "Hl H1 Hproph Hcont". simpl_eval.
    rewrite (bind_proph_args Hp Hv).
    iApply (imp_bind with "[H1]").
    { iApply (imp_as_loc with "H1"). }
    iIntros (l0) "->".
    rewrite /resolve.
    iApply (ewp_resolve with "Hproph"); first apply call_is_atomic_load.
    iApply (imp_stop_load with "Hl"). iIntros "!> Hl".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    iIntros (pvs2) "%Heq2 Hp2".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    by iApply ("Hcont" with "[//] Hp2 Hl").
  Qed.

  Lemma imp_EResolve_EFAA {Φ : Z → iProp Σ} {ζ}
      η e1 e2 (ep : path) (ev : proph_arg) (l : loc) (p : proph_id) (v : val) (i j : Z) pvs :
    lookup_path η ep = Some #p →
    eval_proph_arg η ev = Some v →
    ▷ l ↦ₗ #j -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l', ⌜l' = l⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ i', ⌜i' = i⌝ }} -∗
    proph p pvs -∗
    (∀ pvs', ⌜pvs = (♯j, v) :: pvs'⌝ -∗ proph p pvs' -∗ l ↦ₗ #(j + i) -∗ Φ j) -∗
    EWP eval η (EResolve (EFAA e1 e2) ep ev) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hp Hv) "Hl H1 H2 Hproph Hcont". simpl_eval.
    rewrite (bind_proph_args Hp Hv).
    iApply (imp_bind_par with "[H1] [H2]").
    { iApply (imp_as_loc with "H1"). }
    { iApply (imp_as_int with "H2"). }
    iIntros (l0 i0) "-> ->".
    rewrite /resolve.
    iApply (ewp_resolve with "Hproph"); first apply call_is_atomic_faa.
    iApply (imp_stop_faa with "Hl"). iIntros "!> !> Hl".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    iIntros (pvs2) "%Heq2 Hp2".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    iApply ("Hcont" with "[//] Hp2"). rewrite add_repr_repr. iApply "Hl".
  Qed.

  Lemma imp_EResolve_EExchange {A} `{Encode A} {Φ : A → iProp Σ} {ζ}
      η e1 e2 (ep : path) (ev : proph_arg) (l : loc) (p : proph_id) (v : val) (a b : A) pvs :
    lookup_path η ep = Some #p →
    eval_proph_arg η ev = Some v →
    ▷ l ↦ₗ #a -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l', ⌜l' = l⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ b', ⌜b' = b⌝ }} -∗
    proph p pvs -∗
    (∀ pvs', ⌜pvs = (♯a, v) :: pvs'⌝ -∗ proph p pvs' -∗ l ↦ₗ #b -∗ Φ a) -∗
    EWP eval η (EResolve (EExchange e1 e2) ep ev) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hp Hv) "Hl H1 H2 Hproph Hcont". simpl_eval.
    rewrite (bind_proph_args Hp Hv).
    iApply (imp_bind_par with "[H1] H2").
    { iApply (imp_as_loc with "H1"). }
    iIntros (l0 b0) "-> ->".
    rewrite /resolve.
    iApply (ewp_resolve with "Hproph"); first apply call_is_atomic_exchange.
    iApply (imp_stop_exchange with "Hl"). iIntros "!> !> Hl".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    iIntros (pvs2) "%Heq2 Hp2".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    by iApply ("Hcont" with "[//] Hp2 Hl").
  Qed.

  Lemma imp_EResolve_ECAS {A} `{PhysEqDec A} {Φ : bool → iProp Σ} {ζ}
      η e1 e2 e3 (ep : path) (ev : proph_arg) (l : loc) (p : proph_id) (v : val)
      (seen a v1 : A) pvs :
    lookup_path η ep = Some #p →
    eval_proph_arg η ev = Some v →
    ▷ l ↦ₗ #v1 -∗
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l', ⌜l' = l⌝ }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ s', ⌜s' = seen⌝ }} -∗
    EWP eval η e3 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a', ⌜a' = a⌝ }} -∗
    proph p pvs -∗
    (∀ pvs', ⌜pvs = (♯(phys_eq_val_ v1 seen), v) :: pvs'⌝ -∗ proph p pvs' -∗
       l ↦ₗ (if phys_eq_val_ v1 seen then #a else #v1) -∗
       Φ (phys_eq_val_ v1 seen)) -∗
    EWP eval η (EResolve (ECAS e1 e2 e3) ep ev) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros (Hp Hv) "Hl H1 H2 H3 Hproph Hcont". simpl_eval.
    rewrite (bind_proph_args Hp Hv).
    iApply (imp_bind_par (A1:=loc*A) with "[H1 H2] H3").
    { iApply (imp_par with "[H1] H2"). { iApply (imp_as_loc with "H1"). } }
    iIntros ((l0 & s0) a0) "(-> & ->) ->".
    rewrite /resolve.
    iApply (ewp_resolve with "Hproph"); first apply call_is_atomic_cas.
    iApply (imp_stop_cas with "Hl"). iIntros "!> !> Hl".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    iIntros (pvs2) "%Heq2 Hp2".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    by iApply ("Hcont" with "[//] Hp2 Hl").
  Qed.

  (** * EPerform : expr -> expr *)

  Lemma imp_EPerform `{Encode A, Encode B} {Φ : A → iProp Σ} {ζ} (Φ1 : B → iProp Σ) η e :
    EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    (∀ x, Φ1 x -∗ Ψ allows perform #x << ilift (ireturns ζ) (ireturns Φ) >>) -∗
    EWP eval η (EPerform e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "He Hv". simpl_eval.
    iApply (imp_bind with "He").
    iIntros (x) "HΦ1". change (♯x) with (#x).
    iApply imp_perform.
    iApply ("Hv" with "HΦ1").
  Qed.

  (** * EContinue : expr -> expr -> expr *)

  Lemma imp_EContinue `{Encode A, Encode B} {Φ : A → iProp Σ} {ζ}
    η e1 e2 (Φ1 : cont → iProp Σ) (Φ2 : B → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    (∀ (k : cont) x, Φ1 k -∗ Φ2 x -∗
                ▷ may_resume (O2Ret #x) k E Ψ ζ Φ) -∗
    EWP eval η (EContinue e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hk Hv Hmon". simpl_eval.
    iApply (imp_bind_par (A2 := B) with "[Hk] Hv").
    { iApply (imp_as_cont with "Hk"). }
    iIntros (k x) "Hk Hx".
    iSpecialize ("Hmon" with "Hk Hx").
    iNext. rewrite /continue /=.
    iApply "Hmon".
  Qed.

  Lemma imp_EDiscontinue `{Encode A} {Φ : A → iProp Σ} {ζ}
    η e1 e2 (Φ1 : cont → iProp Σ) (Φ2 : exn → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    (∀ (k : cont) e, Φ1 k -∗ Φ2 e -∗
                ▷ may_resume (O2Throw e) k E Ψ ζ Φ) -∗
    EWP eval η (EDiscontinue e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hk Hv Hmon". simpl_eval.
    iApply (imp_bind_par (A2 := exn) with "[Hk] Hv").
    { iApply (imp_as_cont with "Hk"). }
    iIntros (k x) "Hk Hx".
    iSpecialize ("Hmon" with "Hk Hx").
    iNext. rewrite /continue /=.
    iApply "Hmon".
  Qed.

  Local Lemma imp_EContinue' `{Encode A, Encode B} {Φ : A → iProp Σ} {ζ}
    η e1 e2 (Φ1 : cont → iProp Σ) (Φ2 : B → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    (∀ k x, Φ1 k -∗ Φ2 x -∗
            ∃ sk, isCont k sk ∗
                  ▷ (isShot k -∗
                     ▷ EWP (sk (O2Ret #x)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }})) -∗
    EWP eval η (EContinue e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H1 H2 H3".
    iApply (imp_EContinue with "H1 H2").
    iIntros (??) "H1 H2".
    iSpecialize ("H3" with "H1 H2").
    iDestruct "H3" as (?) "(H1 & H2)".
    iApply (imp_resume with "H1 H2").
  Qed.

  Local Lemma imp_EFork' `{Encode A, Encode B} {ζ}
    (Φ1 : val → iProp Σ) (Φ2 : B → iProp Σ) μ (φ : A → iProp Σ) η e1 e2 :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ ι' f x, isThread ι' μ φ -∗ Φ1 f -∗ Φ2 x -∗
                  EWP call f #x ⟨⟨ e, □ μ e ⟩⟩ {{ x, □ φ x }}) -∗
    EWP eval η (EFork e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ι, isThread ι μ φ }}.
  Proof.
    iIntros "H1 H2 Hcall". simpl_eval.
    iApply (imp_bind_par (A1:=val) (A2:=B) with "H1 H2").
    iIntros (f x) "Hf Hx !>".
    rewrite /continue /=.
    iApply (imp_fork (B:=A) (Bμ:=exn)).
    iIntros "!> %ι' #Hthread". iFrame "#".
    iApply ("Hcall" with "Hthread Hf Hx").
  Qed.

  Lemma imp_EFork `{Encode A, Encode B} {ζ}
    P μ (φ : A → iProp Σ) η e1 e2 (φ_arg : B → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ f, iSpec τ[B] f P }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a, φ_arg a }} -∗
    ▷ (∀ ι' a m, isThread ι' μ φ -∗ φ_arg a -∗
                 P a m -∗ EWP m ⟨⟨ e, □ μ e ⟩⟩ {{ o, □ φ o }}) -∗
    EWP eval η (EFork e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ι, isThread ι μ φ }}.
  Proof.
    iIntros "H1 H2 Hcall".
    iApply (imp_EFork' with "H1 H2").
    iIntros "!>" (ι' f a) "Hvalid HSpec H2".
    rewrite iSpec_equation_1.
    iSpecialize ("HSpec" $! a).
    iApply ("Hcall" $! ι' a (call f #a) with "Hvalid H2 HSpec").
  Qed.

  (* Rule for fork when the postcondition of the spawned thread is persistent *)
  Local Lemma imp_EFork_persistent' `{Encode B} {ζ}
    (Φ1 : val → iProp Σ) (Φ2 : B → iProp Σ) (φ : iProp Σ) η e1 e2 :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ v1 v2, Φ1 v1 -∗ Φ2 v2 -∗
                  EWP call v1 #v2 {{ (_ : B), □ φ }}) -∗
    EWP eval η (EFork e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ι', □ joinable B ι' φ }}.
  Proof.
    iIntros "H1 H2 Hcall". simpl_eval.
    iApply (imp_bind_par with "H1 H2").
    iIntros (f x) "Hf Hx !>".
    rewrite /continue /=.
    iApply (imp_fork (B:=B) (Bμ:=exn)).
    iIntros "!> %ι' #Hthread".
    iSplitL.
    + iSpecialize ("Hcall" with "Hf Hx").
      iApply (imp_wand_exn _ _ _ ⊥ with "Hcall").
      instantiate (1 := (λ _, False)%I).
      iIntros (? []).
    + iFrame "#".
      iIntros "!>" ([|]); [ | iIntros "(% & _ & [])" ].
      iIntros "(% & _ & Hφ) !> !>".
      iApply "Hφ".
  Qed.

  Lemma imp_EFork_persistent `{Encode A} {ζ}
    φ P η e1 e2 (φ_arg : A → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ f, iSpec τ[A] f P }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ φ_arg }} -∗
    ▷ (∀ a m, φ_arg a -∗
                 P a m -∗ EWP m {{ (_ : A), □ φ }}) -∗
    EWP eval η (EFork e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ι', □ joinable A ι' φ }}.
  Proof.
    iIntros "H1 H2 Hcall".
    iApply (imp_EFork_persistent' with "H1 H2").
    iIntros "!>" (f v) "HSpec H2"; simpl.
    iApply ("Hcall" with "H2").
    rewrite iSpec_equation_1.
    iApply "HSpec".
  Qed.

  (* Rule for fork when the postcondition of the spawned thread is a list of
  resources that other threads can recover when joining. *)
  Local Lemma imp_EFork_resourceful_list' `{Encode B} {ζ}
    (Φ1 : val → iProp Σ) (Φ2 : B → iProp Σ) φs η e1 e2 :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ1 }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ2 }} -∗
    ▷ (∀ v1 v2, Φ1 v1 -∗ Φ2 v2 -∗
                  EWP call v1 #v2 {{ (_ : B), [∗ list] φ ∈ φs, φ }}) -∗
    EWP eval η (EFork e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ι', [∗ list] φ ∈ φs, joinable B ι' φ }}.
  Proof.
    (* TODO reuse the proof from [stop_rules.v] instead of having this one, which is now redundant *)
    iIntros "H1 H2 Hcall". simpl_eval.
    iApply (imp_bind_par with "H1 H2").
    iIntros (f x) "Hf Hx !>".
    rewrite /continue /=.
    iApply (imp_fork_resourceful (B:=B)).
    iIntros "!>" (ι') "Hjoinable /=". iFrame.
    iApply ("Hcall" with "Hf Hx").
  Qed.

  Lemma imp_EFork_resourceful_list `{Encode A} {ζ}
    φs P η e1 e2 (φ_arg : A → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ f, iSpec τ[A] f P }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a, φ_arg a }} -∗
    ▷ (∀ a m, φ_arg a -∗
              P a m -∗ EWP m {{ (_ : A), [∗ list] φ ∈ φs, φ }}) -∗
    EWP eval η (EFork e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ι', [∗ list] φ ∈ φs, joinable A ι' φ }}.
  Proof.
    (* TODO reuse the proof from [stop_rules.v] instead of having this one, which is now redundant *)
    iIntros "H1 H2 Hcall".
    iApply (imp_EFork_resourceful_list' with "H1 H2").
    iIntros "!>" (f v) "HSpec H2"; simpl.
    iApply ("Hcall" with "H2").
    rewrite iSpec_equation_1.
    iApply "HSpec".
  Qed.

  (* Specialization for one and two resources instead of a list of resources *)

  Local Lemma imp_EFork_one_resource `{Encode A} {ζ}
    φ P η e1 e2 (φ_arg : A → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ f, iSpec τ[A] f P }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a, φ_arg a }} -∗
    ▷ (∀ a m, φ_arg a -∗ P a m -∗ EWP m {{ (_ : A), φ }}) -∗
    EWP eval η (EFork e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ι', joinable A ι' φ }}.
  Proof.
    iIntros "H1 H2 H".
    iApply (imp_wand with "[-]").
    iApply (imp_EFork_resourceful_list [φ] with "H1 H2 [H]").
    - iIntros "!> % % H1 H2".
      iSpecialize ("H" with "H1 H2").
      iApply (imp_wand with "H").
      iIntros (_) "/= $".
    - iIntros (ι') "($ & ?)".
  Qed.

  Local Lemma imp_EFork_two_resources `{Encode A} {ζ}
    φ1 φ2 P η e1 e2 (φ_arg : A → iProp Σ) :
    EWP eval η e1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ f, iSpec τ[A] f P }} -∗
    EWP eval η e2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a, φ_arg a }} -∗
    ▷ (∀ a m, φ_arg a -∗ P a m -∗ EWP m {{ (_ : A), φ1 ∗ φ2 }}) -∗
    EWP eval η (EFork e1 e2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ι', joinable A ι' φ1 ∗ joinable A ι' φ2 }}.
  Proof.
    iIntros "H1 H2 H".
    iApply (imp_wand with "[-]").
    iApply (imp_EFork_resourceful_list [φ1; φ2] with "H1 H2 [H]").
    - iIntros "!> % % H1 H2".
      iSpecialize ("H" with "H1 H2").
      iApply (imp_wand with "H").
      iIntros (_) "/= ($ & $)".
    - iIntros (ι') "($ & $ & ?)".
  Qed.

  Lemma imp_EJoin2 `{Encode A} {ζ} e η μ (φ : A → iProp Σ) Φ :
    EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ι, isThread ι μ φ }} -∗
    ▷ (∀ x, □ φ x -∗ Φ x) ∧ ▷ (∀ e : exn, □ μ e -∗ ζ e) -∗
    EWP eval η (EJoin e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hid Hjoined". simpl_eval.
    iApply (imp_bind with "[Hid]").
    { iApply (imp_as_thread with "Hid"). }
    iIntros (ι') "Hthread".
    iApply (imp_join with "Hthread [Hjoined]").
    iSplit; first by iDestruct "Hjoined" as "[$ _]".
    iDestruct "Hjoined" as "[_ Hjoined]".
    iIntros "!>" (b) "#Hμ". iExists b.
    iSplit; first done. by iApply "Hjoined".
  Qed.

  Lemma imp_EJoin `{Encode A} {ζ} e η (φ : A → iProp Σ) Φ :
    EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ι, isThread ι (⊥ : exn → iProp Σ) φ }} -∗
    ▷ (∀ x, □ φ x -∗ Φ x) -∗
    EWP eval η (EJoin e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hid Hjoined".
    iApply (imp_EJoin2 with "Hid").
    iSplit; iNext.
    - iExact "Hjoined".
    - iIntros (? []).
  Qed.

  (* The joinable rule for join is the same for persistent and resourceful posts *)
  Lemma imp_EJoin_joinable `{Encode A} {ζ} e η φ (Φ : A → iProp Σ) :
    ↑joinN ⊆ E →
    EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ ι', joinable A ι' φ }} -∗
    ▷ (∀ x, ▷ φ -∗ Φ x) ∧ ▷ (∀ e, ▷ φ -∗ ζ e) -∗
    EWP eval η (EJoin e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "%Hmask Hid Hjoined". simpl_eval.
    iApply (imp_bind with "[Hid]").
    { iApply (imp_as_thread with "Hid"). }
    iIntros (ι') "Hjoinable".
    iDestruct "Hjoinable" as "(% & % & % & % & HThread & Hjoinable)".
    iApply (imp_fupd E (join ι')).
    iApply (imp_fupd_exn E (join ι')).
    iApply (imp_join with "[$]").
    iSplit; iNext.
    - iIntros (x) "#Hφ".
      iDestruct "Hjoined" as "[P _]".
      iApply "P".
      iSpecialize ("Hjoinable" $! (O2Ret ♯x) with "[]").
      { iExists x. iSplit; [ done | iApply "Hφ" ]. }
      iMod (fupd_mask_subseteq (↑joinN) Hmask) as "O".
      iMod "Hjoinable".
      by iMod "O".
    - iIntros (b) "#Hμ".
      iDestruct "Hjoined" as "[_ P]".
      iExists (♯b). iSplit; first (iPureIntro; apply solve_encode_val).
      iApply "P".
      iSpecialize ("Hjoinable" $! (O2Throw ♯b) with "[]").
      { iExists b. iSplit; [ done | iApply "Hμ" ]. }
      iMod (fupd_mask_subseteq (↑joinN) Hmask) as "O".
      iMod "Hjoinable".
      by iMod "O".
  Qed.

  (* TODO add a persistent predicate [thread_outcome ι o] so that [joinable] can
  talk about the outcome of the spawned thread. This is also needed when the
  spawned thread allocates and returns an address that is joined several times,
  e.g. by several threads, or even to prove safety of such programs:

  assert Domain.(let d = spawn ref in join d = join d)

  assert Domain.(let d = spawn Random.bool in join d = join d) *)

End imp_rules_expr.
