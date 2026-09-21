From osiris Require Import osiris.
From osiris.stdlib Require Import og_atomic.

(** * Specifications for the [Atomic] stdlib module.

    The [Atomic.Loc] operations are compiler primitives; Osiris
    translates them as eta-expanded closures over the corresponding
    Osiris instructions ([ECAS], [EFAA], ...), so their specifications
    are proved directly against those closures.

    For now only [Loc.compare_and_set] is specified, at inline-record
    values (the shape needed by clients that CAS a variant field, e.g.
    the concurrent union-find example). The remaining operations can be
    specified the same way when a client needs them. *)

Section atomic_proofs.

  Context `{!osirisGS Σ}.

  (* The logically-atomic specification of [Atomic.Loc.compare_and_set]
     at inline-record values. *)

  Definition compare_and_set_spec compare_and_set : iProp Σ :=
  ∀∀ `(InlineEncode A);
  {{ ∀ E2 Φ;
     ▷ (|={⊤, E2}=>
        ∃ (a : A) dq1 dq2 t,
          ▷ l ↦ₗ #a ∗ ▷ blockTag (inline_blk a) dq1 t ∗
          ▷ blockTag (inline_blk seen) dq2 Mut ∗
          ▷ (l ↦ₗ #(if locations.eqb (inline_blk a) (inline_blk seen) then
                      v'
                    else
                      a) -∗
            blockTag (inline_blk a) dq1 t -∗
            blockTag (inline_blk seen) dq2 Mut -∗
            |={E2, ⊤}=>
              Φ (locations.eqb (inline_blk a) (inline_blk seen)))) }}
  compare_and_set l seen v' : loc A A
  {{ RET b; Φ b }}.

  Lemma imp_Loc_compare_and_set η :
    ⊢ EWP (eval η (EAnonFun __Loc_fun5))
        {{ compare_and_set_spec }}.
  Proof.
    unfold compare_and_set_spec.
    iApply imp_EAnon_poly.
    iIntros "!>" (A HencA HinlA). simpl.
    iIntros (l seen v').
    iIntros (E2 Φ) "Hfupd".
    iApply imp_please; iNext.
    iApply (imp_cas_inline_atomic E2 ⊤ _ _ _ _
              (λ l0 : loc, ⌜l0 = l⌝)%I (λ s : val, ⌜s = #seen⌝)%I
              (λ w : val, ⌜w = #v'⌝)%I
              with "[] [] [] [Hfupd]").
    { imp_path. }
    { imp_path. }
    { imp_path. }
    iNext.
    iMod "Hfupd".
    iModIntro.
    iIntros (l0 s w) "-> -> ->".
    iDestruct "Hfupd" as (a dq1 dq2 t) "(Hl & Hr & Hrs & Hk)".
    iExists (inline_tag a), (inline_tag seen),
            (inline_blk a), (inline_blk seen), dq1, dq2, t.
    iSplitR; first by rewrite (inline_encode_eq seen).
    rewrite -(inline_encode_eq a).
    iFrame "Hl Hr Hrs".
    iNext. iIntros "Hl Hr Hrs".
    (* The two shapes of the written value differ only by where the [if]
       sits, inside or outside the encoding. *)
    destruct (locations.eqb (inline_blk a) (inline_blk seen));
      iApply ("Hk" with "Hl Hr Hrs").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* Module-level specifications, in the style of [array_module_spec]. *)

  Definition atomic_loc_module_dom : gset var :=
    {[ "get"; "exchange"; "compare_and_set"; "fetch_and_add";
       "set"; "incr"; "decr" ]}.

  Definition atomic_loc_module_spec : env → iProp Σ :=
    (context [
         var_spec "compare_and_set" compare_and_set_spec
      ] atomic_loc_module_dom)%I.

  Definition atomic_module_dom : gset var :=
    {[ "Loc"; "make"; "get"; "set"; "exchange"; "compare_and_set";
       "fetch_and_add"; "incr"; "decr" ]}.

  Definition atomic_module_spec : env → iProp Σ :=
    (context [
         var_spec "Loc" (λ δ : env, atomic_loc_module_spec δ)
      ] atomic_module_dom)%I.

  Global Instance atomic_spec_pers η : Persistent (atomic_module_spec η).
  Proof. apply _. Qed.

  (* The [Atomic] module satisfies its specification. The operations
     without a specification are admitted, as in [array.module_proof]. *)
  Lemma module_proof η :
    ⊢ EWP (eval_mexpr η __main) {{ atomic_module_spec }}.
  Proof.
    iApply imp_module.
    iApply (imp_sitems_module atomic_loc_module_spec).
    { iApply imp_module.
      iApply (imp_sitems_external (λ _, True)%I).
      { admit. }
      iIntros (get) "_".
      iApply (imp_sitems_external (λ _, True)%I).
      { admit. }
      iIntros (exchange) "_".
      iApply (imp_sitems_external compare_and_set_spec).
      { iApply imp_Loc_compare_and_set. }
      iIntros (cas) "#Hcas".
      iApply (imp_sitems_external (λ _, True)%I).
      { admit. }
      iIntros (faa) "_".
      iApply (imp_sitems_let (A:=val)).
      { admit. }
      iIntros (set) "_".
      iApply (imp_sitems_let (A:=val)).
      { admit. }
      iIntros (incr) "_".
      iApply (imp_sitems_let (A:=val)).
      { admit. }
      iIntros (decr) "_".
      iApply imp_sitems_nil.
      iFrame "#". simpl. auto. }

    iIntros (δLoc) "#HLoc".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (make) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (get) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (set) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (exchange) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (cas) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (faa) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (incr) "_".
    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (decr) "_".
    iApply imp_sitems_nil.
    iFrame "#". simpl. auto.
  Admitted.

  (* Resolving [Atomic.Loc.compare_and_set] through the module
     specification. This is the form clients use to discharge a
     top-level alias such as [let cas = Atomic.Loc.compare_and_set]. *)
  Lemma atomic_cas_path_spec η :
    in_env "Atomic" atomic_module_spec η -∗
    path_spec ["Atomic"; "Loc"; "compare_and_set"] compare_and_set_spec η.
  Proof.
    iIntros "(%δA & %HA & #HAspec)".
    rewrite /atomic_module_spec /atomic_loc_module_spec /context /=.
    iDestruct "HAspec" as "(%HdomA & HLoc & _)".
    iDestruct "HLoc" as "(%δL & %HL & #HLspec)".
    iDestruct "HLspec" as "(%HdomL & Hcas & _)".
    iDestruct "Hcas" as "(%cas & %Hcas & #Hspec)".
    iExists cas.
    iSplit; last done.
    iPureIntro.
    simpl. rewrite HA /=.
    rewrite -!solve_encode_env /=.
    rewrite HL /=.
    rewrite -!solve_encode_env /=.
    exact Hcas.
  Qed.

End atomic_proofs.
