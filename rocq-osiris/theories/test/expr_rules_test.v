From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import osiris lang.
From osiris.program_logic Require Import ewp.
From osiris.proofmode Require Import proofmode.

Section test_expr_rules.
Context `{!osirisGS Σ}.

(* Useful when goal is [R ⊢ WP (ret v) {{ ?evar }}] *)
(* iApply-ing it will fail without providing much information if [R] or [v]
   depends on a variable [y] that was created after the creation of the evar, in
   which case, instantiate the evar with something like [λx, ∃y, ⌜x = y⌝ ∗ R] *)
Lemma imp_ret_eq `{Encode A} {Ψ} (v : A) :
  ⊢ EWP (@Ret val exn #v) <|Ψ|> {{ x, ⌜x = v⌝ }}.
Proof.
  iApply imp_ret; auto.
Qed.


(* Useful when goal is [R ⊢ ?evar v] *)
Lemma goal_eq {A} (v : A) (R : iProp Σ) φ :
  φ = (λ x, ⌜x = v⌝ ∗ R)%I ->
  R ⊢ φ v.
Proof.
  iIntros (->) "R".
  auto.
Qed.

(* Useful when goal is [⊢ ?evar v] *)
Lemma goal_eq_emp {A} (v : A) (φ : _ -> iProp Σ) :
  φ = (λ x, ⌜x = v⌝)%I ->
  ⊢ φ v.
Proof.
  iIntros (->).
  auto.
Qed.

(* References are one-field mutable records: [ref e] is [ERecord Mut [e]],
   [!e] is [ERecordAccess e 0] and [e1 := e2] is [ERecordSet e1 0 e2]. *)

Local Abbreviation ERef e := (ERecord Mut [e]).
Local Abbreviation EDeref e := (ERecordAccess e 0%Z).
Local Abbreviation EAssign e1 e2 := (ERecordSet e1 0%Z e2).

(* [ref 1] *)

Lemma example_ref_1 η:
  ⊢ EWP (eval η (ERef (EInt 1))) {{ (r : record), r ↦ #1%Z }}.
Proof.
  imp_ref.
Qed.

(* [!x] *)
Lemma example_load η x (r : record) v :
  r ↦ #v ⊢ EWP (eval (x~>#r; η) (EDeref (EVar x))) {{ v', ⌜v' = v⌝ ∗ r ↦ v }}.
Proof.
  iIntros "Hr".
  imp_step.
Qed.

(* [x := 2] *)
Lemma example_store η x (r : record) :
  lookup_name η x = Some #r ->
  r ↦ #1%Z
    ⊢ EWP (eval η (EAssign (EVar x) (EInt 2)))
    {{ (_ : unit), r ↦ #2 }}.
Proof.
  iIntros (Hx) "Hr".
  imp_store r.
Qed.

(* [x := 2; x := 4] *)
Lemma example_2_stores η x (r : record) :
  lookup_name η x = Some #r ->
  r ↦ #1%Z
  ⊢ EWP (eval η
           (ESeq
              (EAssign (EVar x) (EInt 2))
              (EAssign (EVar x) (EInt 4))))
      {{ (_ : unit), r ↦ #4%Z }}.
Proof.
  iIntros (Hx) "Hr".
  iApply (imp_ESeq with "[Hr]").
  - imp_store r 2%Z.
  - iIntros "Hr".
    imp_store r.
Qed.

(* [!(ref 1)]  *)
Lemma example_load_ref η :
  ⊢ EWP (eval η (EDeref (ERef (EInt 1)))) {{ r, ⌜r = 1%Z⌝ }}.
Proof.
  iApply (imp_deref2 (λ r, r ↦ #1%Z)%I).
  - (* ref 1 *)
    imp_ref.
  - (* load *)
    iIntros (r) "$".
    auto.
Qed.

(* [x := 1 + !x] *)
Lemma example_incr η x (rx : record) n :
  lookup_name η x = Some #rx ->
  rx ↦ #n
  ⊢ EWP (eval η (EAssign (EVar x) (EIntAdd (EInt 1) (EDeref (EVar x)))))
    {{ (_ : unit), rx ↦ #(1 + n)%Z }}.
Proof.
  iIntros (Ex) "Hx".
  iApply (imp_assign2 (A:=Z) with "[] [Hx]").

  - (* l-value x *)
    imp_path.

  - (* 1 + !x *)
    set_postcondition (λ i, ⌜(i = 1 + n)%Z⌝ ∗ rx ↦ #n)%I.
    imp_arith with "[] [Hx]".
    (* add's postcondition *)
    iIntros "(-> & $)".
    auto.

  - (* store's postcondition *)
    iIntros (n2) "(-> & Hrx)".
    iFrame. auto.
Qed.

(* [x := !x + !x] *)
Lemma example_double η x (rx : record) n :
  lookup_name η x = Some #rx ->
  rx ↦ #n
  ⊢ EWP (eval η (EAssign (EVar x) (EDeref (EVar x) + EDeref (EVar x))))
    {{ (_ : unit), rx ↦ #(2 * n)%Z }}.
Proof.
  iIntros (Ex) "Hx".
  iApply (imp_assign2 (A:=Z) with "[] [Hx]").
  - imp_path.
  - (* !x + !x *)
    iDestruct "Hx" as "(Hx1 & Hx2)".
    set_postcondition (λ i, ⌜(i = 2 * n)%Z⌝ ∗ rx ↦ #n)%I.
    imp_arith with "[Hx1] [Hx2]".
    (* add's postcondition *)
    iIntros "(-> & Hx1) (-> & Hx2)".
    iCombine "Hx1" "Hx2" as "$".
    iPureIntro; lia.
  - (* := *)
    iIntros (i) "(-> & Hx)".
    iFrame. auto.
Qed.

(* The current automation does not scale when we have to split
   ownership in this way.

   For example, the following proof should be mostly automatable. *)

(* [x := (!x * !x) + (!x * !x)] *)
Lemma example_double_double η x (rx : record) n :
  lookup_name η x = Some #rx ->
  rx ↦ #n
  ⊢ EWP (eval η (EAssign (EVar x)
     ((EDeref (EVar x) + EDeref (EVar x)) * (EDeref (EVar x) + EDeref (EVar x)) )))
    {{ (_ : unit), rx ↦ #((2 * n)^2)%Z }}.
Proof.
  iIntros (Ex) "Hx".
  iApply (imp_assign2 (A:=Z) with "[] [Hx]").
  - imp_path.
  - (* !x + !x *)
    imp_arith reading "Hx".
  - (* := *)
    iIntros (i) "(-> & Hx)".
    iFrame. iIntros "!> !> Hlx".
    replace ((n + n) * (n + n))%Z with ((2 * n) ^ 2)%Z by lia.
    iApply "Hlx".
Qed.


(* [(!x, !y)] *)
Lemma example_tuple_resources η x (rx : record) y (ry : record) (n : Z) :
  lookup_name η x = Some #rx ->
  lookup_name η y = Some #ry ->
  rx ↦ #n -∗
  ry ↦ #n -∗
  EWP (eval η (ETuple [EDeref (EVar x); EDeref (EVar y)]))
    {{ (x, y), ⌜x = n⌝ ∗ ⌜y = n⌝ ∗ rx ↦ #n ∗ ry ↦ #n }}.
Proof.
  iIntros (Ex Ey) "Hx Hy".
  imp_tuple with "[Hx] [Hy]".
  (* Only the monotonicity goal remains; the elements were stepped. *)
  iIntros (x0 y0) "((-> & ?) & (-> & ?))". by iFrame.
Qed.

Lemma example_data_resources η x (rx : record) (n : Z) :
  lookup_name η x = Some #rx ->
  rx ↦ #n -∗
  EWP (eval η (EData "::" [EDeref (EVar x); EData "[]" []]))
    {{ (l : list Z), ⌜l = [n]⌝ ∗ rx ↦ #n }}.
Proof.
  iIntros (Ex) "Hx".
  imp_data with "[Hx]".
  (* Only the monotonicity goal remains; the arguments were stepped. *)
  iIntros (h t) "((-> & ?) & ->)". by iFrame.
Qed.

(* [x.f], with only the field [f = 1] of [x] owned *)
Lemma example_field_read η x (r : record) (n : Z) :
  lookup_name η x = Some #r ->
  r ↦[1] #n ⊢
  EWP (eval η (ERecordAccess (EVar x) 1%Z)) {{ v, ⌜v = n⌝ ∗ r ↦[1] #n }}.
Proof.
  iIntros (Hx) "Hr".
  imp_step.
Qed.

(* [x.f <- 2] *)
Lemma example_field_write η x (r : record) (n : Z) :
  lookup_name η x = Some #r ->
  r ↦[1] #n ⊢
  EWP (eval η (ERecordSet (EVar x) 1%Z (EInt 2))) {{ (_ : unit), r ↦[1] #2%Z }}.
Proof.
  iIntros (Hx) "Hr".
  imp_step.
Qed.

Lemma example_env_lookup `{Encode A} η (fun_spec : A → iProp Σ) :
  in_env "fun" (λ a, □ fun_spec a) η -∗
  EWP (eval (("x", #1%Z) :: ("y", #2%Z) :: ("a", #1%Z) :: ("z", #3%Z) :: η) (EVar "z"))
    {{ (i : Z), ⌜i = 3%Z⌝ }}.
Proof.
  iIntros "#Hf".
  iApply imp_wand.
  imp_path.
  iIntros (?) "-> //".
Qed.

(* match 1 with _ -> true *)

Lemma simple_PAny_match η :
  ⊢ EWP eval η
    (EMatch (EInt 1)
      [Branch (CVal PAny) (EConstant "true")])
    {{ b, ⌜b = true⌝ }}.
Proof.
  iStartProof.
  imp_match.
  imp_constant.
Qed.

(* match 1 with 1 -> true | _ -> false *)

Lemma simple_PInt_eq_match η :
  ⊢ EWP eval η
    (EMatch (EInt 1)
      [Branch (CVal (PInt 1)) (EConstant "true");
       Branch (CVal  PAny   ) (EConstant "false")])
    {{ b, ⌜b = true⌝ }}.
Proof.
  iStartProof.
  imp_match.
  - imp_constant.
  - auto.
Qed.

(* checking now whether pat_pNil works with
match [] with _ :: _ -> 1 | _ -> 2 *)

Lemma simple_true_true_match `{Encode A} η :
  ⊢ EWP eval η
    (EMatch (EData "[]" [])
      [Branch (CVal (PData "::" [ PAny; PAny ])) (EInt 1);
       Branch (CVal (PConstant "[]")) (EInt 2)])
    {{ i, ⌜i = 2%Z⌝ }}.
Proof.
  iStartProof.
  imp_match (list A).
  - imp_int.
  - auto.
Qed.

(* Testing imp_branches: automatically process all match branches *)

Lemma imp_branches_PAny η :
  ⊢ EWP eval η
    (EMatch (EInt 1)
      [Branch (CVal PAny) (EConstant "true")])
    {{ b, ⌜b = true⌝ }}.
Proof.
  iStartProof.
  imp_match.
  imp_constant.
Qed.

Lemma imp_branches_two_branches η :
  ⊢ EWP eval η
    (EMatch (EInt 1)
      [Branch (CVal (PInt 1)) (EConstant "true");
       Branch (CVal  PAny   ) (EConstant "false")])
    {{ b, ⌜b = true⌝ }}.
Proof.
  iStartProof.
  imp_match.
  - imp_constant.
  - auto.
Qed.

End test_expr_rules.
