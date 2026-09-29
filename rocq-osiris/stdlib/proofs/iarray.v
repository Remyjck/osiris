From osiris Require Import osiris.
From osiris.stdlib Require Import Externals Stdlib array.

From osiris.stdlib Require Import og_iarray.
From osiris.utils Require Import list_z big_opLZ.

Definition iarray : Type := syntax.array.

Section iarray_resources.

  Context `{!osirisGS Σ}.

  Definition owniArray `{Encode A} (a : iarray) (xs : list A) : iProp Σ :=
    ∃ ls, isBlockLocs a ls ∗ [∗ listZ] l;x ∈ ls; xs, l ↦□ #x.

  Global Instance isBlockLocs_pers' (a : iarray) ls : Persistent (isBlockLocs a ls).
  Proof. apply _. Qed.

  Global Instance iArray_pers `{Encode A} a (xs : list A) : Persistent (owniArray a xs).
  Proof. apply _. Qed.

  Lemma ownArray_isBlockLocs `{Encode A} (a : iarray) (xs : list A) :
    owniArray a xs -∗ ∃ ls, isBlockLocs a ls.
  Proof. iIntros "(%ls & $ & _)". Qed.

End iarray_resources.

Notation "a ↦□∗ xs" := (owniArray a xs) (at level 20).

Section freeze_iarray.

  Context `{!osirisGS Σ}.

  Definition freeze_array_spec freeze : iProp Σ :=
    {{ ∀ `(Encode A) (xs : list A); a ↦∗ xs }}
    freeze a : array
    {{ RET (a' : iarray); a' ↦□∗ xs ∗ isBlock a' (DfracOwn 1) Immut }}.

  Lemma imp_freeze_array freeze :
    freeze_spec freeze -∗
    freeze_array_spec freeze.
  Proof.
    iIntros "#Hspec !>".
    iApply (iSpec_mono with "Hspec").
    iIntros (b m) "Hm %A %HencA %xs Hown".
    (* Unfold ownArray: extracts isBlockLocs, isBlock (DfracOwn 1 Mut), isSlice, length-eq *)
    iDestruct "Hown" as "(%ls & #Harr & Hblock & Hslice & %Hlenls)".
    (* Extract the slice contents for persistence later *)
    iDestruct "Hslice" as "(%ls' & #Harr' & %Hle & Hown)".
    iPoseProof (isBlockLocs_valid with "Harr Harr'") as "->".
    (* Now apply freeze to the physical block *)
    iSpecialize ("Hm" with "Hblock").
    iPoseProof (big_sepLZ2_mono with "Hown") as "Hown".
    { iIntros (k ?? Hlookup1 Hlookup2) "Hpointsto".
      iApply (gen_heap.pointsto_persist with "Hpointsto"). }
    iPoseProof (big_sepLZ2_bupd with "Hown") as ">Hown".
    iApply (imp_wand with "Hm").
    iIntros (a') "(-> & $)".
    (* Build owniArray *)
    iExists ls. iFrame "#".
    seg. iApply "Hown".
  Qed.


End freeze_iarray.

Section init_proof.

  Context `{!osirisGS Σ}.

  Definition init_spec init : iProp Σ :=
    {{ ∀ `(Encode A, Inhabited A) (I : list A → iProp Σ);
       ⌜0 ≤ n ≤ max_array_length⌝ ∗
       (* [f] is a function [Z → A], such that [f i] preserves
          an invariant [I] over the results of all calls to [f i] so far. *)
       {{ ∀ xs; ⌜0 ≤ i < n⌝ ∗ ⌜length xs = i⌝ ∗ I xs }}
       f i : Z
       {{ RET x; I (xs ++ singleton x) }} ∗
       I [] }}
    (* Calling [init f n] returns an array [a] such that [ownArray a xs],
       and such that [Φ i] holds for the [i]'th element of xs. *)
    init n f : Z val
    {{ RET a; ∃ (xs : list A), ⌜length xs = n⌝ ∗ a ↦□∗ xs ∗
                isBlock a (DfracOwn 1) Immut ∗ I xs }}.

  Definition init := (EAnonFun __init).

  Lemma imp_init η :
    □ in_env "Array" array_module_spec η -∗
    □ in_env "unsafe_of_array" freeze_spec η -∗
    EWP (eval η init) {{ init_spec }}.
  Proof.
    iIntros "#Hlookup1 #Hlookup2".
    unfold init, init_spec.
    iApply imp_EAnon_pers.
    iIntros "!> /=".
    iIntros (n f).
    change (VInt (int.repr n)) with #n.
    iIntros (A HencA HinhA I) "(%Hbounds & #Hf & HI)".
    iApply imp_please; iNext.
    iPoseProof (in_env_mono with "Hlookup2 []") as "Hlookup2'".
    { iIntros (freeze). iApply imp_freeze_array. }
    iClear "Hlookup2".
    imp_app τ[array] with "[] [HI]".
    { imp_app τ[Z;val].
      iIntros "Hm".
      iApply ("Hm" $! A HencA HinhA I with "[$HI $Hf //]"). }
    iIntros "(%xs & %Hlenxs & Hown & HI) Hm".
    iSpecialize ("Hm" with "Hown").
    iApply (imp_wand with "Hm").
    iIntros (a) "($ & $)". iFrame "∗%".
  Qed.

End init_proof.


Section module_proof.
  Context `{!osirisGS Σ}.

  Local Notation "'next_top:' sitem" :=
    (impure ⊤ (eval_sitems _ (sitem :: _)) ⊥ ⊥ _) (at level 20).

  Definition iarray_module_dom : gset var :=
    {[ "length";
        "get";
        "unsafe_get";
        "concat";
        "append_prim";
        "unsafe_sub";
        "unsafe_of_array";
        "unsafe_to_array";
        "create_float";
        "init";
        "append";
        "sub";
        "iter";
        "iter2";
        "map";
        "map2";
        "iteri";
        "mapi";
        "to_list";
        "of_list";
        "to_array";
        "of_array";
        "fold_left";
        "fold_left_map";
        "fold_right";
        "exists";
        "for_all";
        "for_all2";
        "exists2";
        "equal";
        "compare";
        "mem";
        "memq";
        "find_opt";
        "find_index";
        "find_map";
        "find_mapi";
        "split";
        "combine";
        "lift_sort";
        "sort";
        "stable_sort";
        "fast_sort";
        "to_seq";
        "to_seqi";
        "of_seq"
    ]}.

  Definition iarray_module_spec : env → iProp Σ :=
    (context [
      ] iarray_module_dom)%I.

  Global Instance iarray_spec_pers η : Persistent (iarray_module_spec η).
  Proof. apply context_pers. Qed.

  Global Instance in_env_pers `{Encode A} name η (Φ : A → iProp Σ) :
    (∀ a, Persistent (Φ a)) →
    Persistent (in_env name Φ η).
  Proof. intros. apply _. Qed.

  Lemma imp_mpath (Φ : env → iProp Σ) p η E Ψ (ζ : exn → iProp Σ) :
    path_spec p Φ η -∗
    impure E (eval_mexpr η (MPath p)) Ψ ζ Φ.
  Proof.
    iIntros "Hpath".
    simpl_eval_mexpr.
    iDestruct "Hpath" as "(%m & -> & HΦ)".
    iApply imp_of_option. by iFrame.
  Qed.


  Lemma module_proof η :
    in_env "Stdlib" (λ (η : env), in_env "Array" array_module_spec η) η -∗
    EWP (eval_mexpr η __main) {{ iarray_module_spec }}.
  Proof.
    iIntros "#Hstdlib".
    iApply imp_module.
    iApply imp_sitems_open. { iApply imp_mpath. ltac2:(solve_path_spec ()). }
    iIntros (?) "#Harray".
    iApply imp_externals_length. iIntros (length) "#Hlength".
    iApply imp_externals_get. iIntros (get) "#Hget".
    iApply imp_externals_get. iIntros (unsafe_get) "#Hsafe_get".
    iApply imp_externals_freeze. iIntros (freeze) "#Hfreeze".
    iApply imp_externals_freeze. iIntros (unfreeze) "#Hunfreeze".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_init; iModIntro.
      ltac2:(solve_in_env ()). ltac2:(solve_in_env ()). iFrame "#". }
    iIntros (init) "#Hinit".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (append) "Happend".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (sub) "Hsub".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_iter; (iFrame "#"; auto). }
    iIntros (iter) "#Hiter".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (iter2) "Hiter2".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (map) "Hmap".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (map2) "Hmap2".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_iteri; (iFrame "#"; auto). }
    iIntros (iteri) "#Hiteri".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (mapi) "Hmapi".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_list) "Hto_list".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_list) "Hof_list".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_array) "Hto_array".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_array) "Hof_array".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_fold_left; (iFrame "#"; auto). }
    iIntros (fold_left) "#Hfold_left".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fold_left_map) "Hfold_left_map".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fold_right) "Hfold_right".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (vexists) "Hexists".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (for_all) "Hfor_all".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (for_all2) "Hfor_all2".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (vexists2) "Hexists2".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (equal) "Hequal".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (compare) "Hcompare".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (mem) "Hmem".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (memq) "Hmemq".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (find_opt) "Hfind_opt".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (find_index) "Hfind_index".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (find_map) "Hfind_map".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (find_mapi) "Hfind_mapi".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (split) "Hsplit".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (combine) "Hcombine".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (lift_sort) "Hlift_sort".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (sort) "Hsort".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (stable_sort) "Hstable_sort".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fast_sort) "Hfast_sort".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_seq) "Hto_seq".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_seqi) "Hto_seqi".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_seq) "Hof_seq".

    iApply imp_sitems_nil.
    iFrame "#". simpl. auto.

  Admitted.

End module_proof.
