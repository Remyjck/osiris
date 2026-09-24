From osiris Require Import osiris.
From osiris.stdlib Require Import Externals Stdlib.

(* The deep embedding obtained from translating [queue.ml]. *)
From osiris.stdlib Require Import og_queue.

(* Boilerplate pertaining to the [cell] and [t] types. *)

Section boilerplate.

  Inductive cell : Type :=
  | Nil
  | Cons (r : record).

  Global Instance record_eq_dec : EqDecision record.
  Proof. solve_decision. Qed.

  Global Instance cell_eq_dec : EqDecision cell.
  Proof. solve_decision. Qed.

  Record cons `{Encode A} := { content : A; next : cell }.

  Record t := { length : Z; first : cell; last : cell }.

  Global Instance encode_cell : Encode cell :=
    { encode' c := match c with
                   | Nil => VConstant "Nil"
                   | Cons r => VInline "Cons" r
                   end }.

  Global Instance Constant_Nil : Constant "Nil" cell :=
    { constant_value := Nil; constant_encode := eq_refl }.

  Global Instance cons_repr `{Encode A} : RecordRepr (@cons A _) τ[A; cell] Mut :=
    { repr_to_types c := (c.(content), c.(next));
      types_to_repr := λ c n, {| content := c; next := n |};
      repr_id := λ '(c, n), eq_refl }.

  Global Instance t_repr : RecordRepr t τ[Z; cell; cell] Mut :=
    { repr_to_types t := (t.(length), (t.(first), t.(last)));
      types_to_repr := λ l fst lst, {| length := l; first := fst; last := lst |};
      repr_id := λ '(l, (fst, lst)), eq_refl }.

End boilerplate.

(* The [Cell], [Cell_Seg], and [Queue] resources.

   I have tried to keep them faithful to the CFML definitions, but I have replaced the [IF] with a match.
   Feel free to use [if decide (l = []) then ...] instead if you prefer. *)

Section queue_resources.

  Context `{!osirisGS Σ}.

  Definition Cell `{Encode A} (v : A) (n c : cell) : iProp Σ :=
    ∃ r,
      ⌜c = Cons r⌝ ∗ r ⤇ {| content := v; next := n |}.

  Fixpoint Cell_Seg `{Encode A} (l : list A) (to from : cell) : iProp Σ :=
    match l with
    | [] => ⌜to = from⌝
    | x :: l' => ∃ n, Cell x n from ∗ Cell_Seg l' to n
    end.

  Definition Queue `{Encode A} (l : list A) (q : record) : iProp Σ :=
    ∃ (cf cl : cell),
      q ⤇ {| length := list_z.length l; first := cf; last := cl |} ∗
      match l with
      | [] => ⌜cf = Nil⌝ ∗ ⌜cl = Nil⌝
      | x :: l' => Cell_Seg l' cl cf ∗ Cell_Seg [x] Nil cl
      end.

  Lemma Cell_Seg_nil `{Encode A} (to from : cell) :
    Cell_Seg (@nil A) to from ∗-∗ ⌜to = from⌝.
  Proof. auto. Qed.

  Lemma Cell_Seg_Nil `{Encode A} :
    ⊢ Cell_Seg (@nil A) Nil Nil.
  Proof. auto. Qed.

  Lemma Cell_Seg_cons `{Encode A} (x : A) (l : list A) (to from : cell) :
    Cell_Seg (x :: l) to from -∗
    ∃ n, Cell x n from ∗ Cell_Seg l to n.
  Proof. auto. Qed.

  Lemma Cell_Seg_Nil2 `{Encode A} (c : cell) (l : list A) :
    Cell_Seg l c Nil -∗ ⌜l = []⌝ ∗ ⌜c = Nil⌝.
  Proof.
    iIntros "HSeg".
    destruct l as [|x l']; first auto.
    iPoseProof (Cell_Seg_cons with "HSeg") as "(%n & HCell & _)".
    iDestruct "HCell" as "(%r & %Hcontra & _)".
    discriminate Hcontra.
  Qed.

  (* I have written [Queue_if] and [Queue_if_first] with a [match] and
     an [if decide] respectively. Feel free to pick whichever style
     you prefer. *)

  Lemma Queue_if `{Encode A} (l : list A) (q : loc) :
    Queue l q -∗
    ∃ cf cl,
      q ⤇ {| length := list_z.length l; first := cf; last := cl |} ∗
      match cl with
      | Nil => ⌜l = []⌝ ∗ ⌜cf = Nil⌝
      | _ => ∃ x l', ⌜l = x :: l'⌝ ∗ Cell_Seg l' cl cf ∗ Cell_Seg [x] Nil cl
      end.
  Proof.
    iIntros "(%cf & %cl & $ & Hl)".
    destruct l as [|x l'].
    { by iDestruct "Hl" as "(-> & ->)". }
    simpl Cell_Seg.
    iDestruct "Hl" as "(HSeg1 & (%n & HCell & <-))".
    iDestruct "HCell" as "(%r & -> & Hr)".
    by iFrame.
  Qed.

  Lemma Queue_if_first `{Encode A} (l : list A) (q : loc) :
    Queue l q -∗
    ∃ cf cl,
      q ⤇ {| length := list_z.length l; first := cf; last := cl |} ∗
      if decide (cf = Nil) then ⌜l = []⌝ ∗ ⌜cl = Nil⌝ else
      ∃ x l', ⌜l = x :: l'⌝ ∗ Cell_Seg l' cl cf ∗ Cell_Seg [x] Nil cl.
  Proof.
    iIntros "(%cf & %cl & $ & Hl)".
    destruct l as [|x l'].
    { iDestruct "Hl" as "(-> & ->)". by case_decide. }
    iDestruct "Hl" as "(HSeg1 & (%n & HCell & <-))".
    iDestruct "HCell" as "(%r & -> & Hr)".
    destruct l' as [|y l'']; simpl Cell_Seg.
    { iDestruct "HSeg1" as "<-".
      case_decide; first discriminate.
      iExists x, []. iFrame.
      equality. (* Osiris helper tactic to prove equalities. *) }
    { iDestruct "HSeg1" as "(%n & HCell & HCell_Seg)".
      iDestruct "HCell" as "(%r' & -> & Hr')".
      case_decide; first discriminate.
      iExists x, (y :: l''). iFrame.
      equality. }
  Qed.

End queue_resources.

(* This section contains the proofs of the functions.
   We work with weakest preconditions rather than triples. *)

(* Functions which call other functions should have an assumption that
   those other functions are in-scope.

   These assumptions are written [□ in_env "name" spec η], examples can
   be found in 'array.v', e.g. in [imp_init]. *)

Section proofs.

  Context `{!osirisGS Σ}.

  (* For create, we have one argument of type [unit], and the
     specification is for any type, we get [q] an empty queue with
     elements of that type. *)

  Definition create_spec create : iProp Σ :=
    □ {{ ∀ A (HencA : Encode A); True }}
    create u : unit
    {{ RET q; Queue (@nil A) q }}.

  Definition create := (EAnonFun __create).

  (* Because our language has words of arbitrary size, we need to
     assume that the words are big enough to index all of the fields of
     [t] records. *)
  Hypothesis max_fields : 3 ≤ max_array_length.

  Lemma imp_create η :
    ⊢ EWP (eval η create) {{ create_spec }}.
  Proof.
    (* [imp_EAnon_pers] is the lemma for proving that a function
       persistently satisfies its specification. *)
    unfold create, create_spec.
    iApply imp_EAnon_pers.
    iIntros "!> /=".
    iIntros ([] A HencA) "_".
    iApply imp_please; iNext.

    (* The [()] argument binding acts as a match on the first argument *)
    imp_match unit. rewrite -encode_encode'.

    imp_record.
    simpl.
    iIntros (v) "(%l & %cf & %cl & Hv & -> & -> & ->)".
    unfold Queue. by iFrame.
  Qed.

End proofs.

(* After having proven all the functions individually, we want to prove
   that the whole module is correct.

   A module specification (currently called [context]) asserts the
   domain of the module, and specifications for a subset of the domain. *)

Section module_proof.

  Context `{!osirisGS Σ}.

  Definition queue_module_dom : gset var :=
    {[ "Empty";
       "create";
       "clear";
       "add";
       "push";
       "peek";
       "peek_opt";
       "top";
       "take";
       "take_opt";
       "pop";
       "copy";
       "is_empty";
       "length";
       "iter";
       "fold";
       "transfer";
       "to_seq";
       "add_seq";
       "of_seq"
     ]}.

  Definition queue_module_spec : env → iProp Σ :=
    (context [
       var_spec "create" create_spec
     ]
     queue_module_dom)%I.

  Local Notation "'next_top:' sitem" :=
    (impure ⊤ (eval_sitems _ (sitem :: _)) ⊥ ⊥ _) (at level 20).

  Hypothesis max_fields : 3 ≤ max_array_length.

  (* The proof of the whole module. *)

  Lemma module_proof η :
    ⊢ EWP (eval_mexpr η __main) {{ queue_module_spec }}.
  Proof.
    iApply imp_module.
    iApply imp_sitems_extend. iIntros (empty) "Hempty".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_create. assumption. }
    iIntros (create) "#Hcreate".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (clear) "Hclear".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (add) "Hadd".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (push) "Hpush".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (peek) "Hpeek".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (peek_opt) "Hpeek_opt".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (top) "Htop".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (take) "Htake".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (take_opt) "Htake_opt".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (pop) "Hpop".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (copy) "Hcopy".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (is_empty) "His_empty".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (length) "Hlength".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (iter) "Hiter".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fold) "Hfold".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (transfer) "Htransfer".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_seq) "Hto_seq".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (add_seq) "Hadd_seq".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_seq) "Hof_seq".

    iApply imp_sitems_nil.
    iFrame "#". simpl. auto.

Admitted.

End module_proof.
