From osiris Require Import osiris.
From osiris.stdlib Require Import Externals Stdlib.

From osiris.utils Require Import list_z big_opLZ.
From osiris.stdlib Require Import og_array.

Open Scope Z.

Section init_proof.

  Context `{!osirisGS Σ}.

  Definition init_spec init : iProp Σ :=
    {{ ∀ `(Encode A, Inhabited A) (I : list A → iProp Σ);
        ⌜0 ≤ n ≤ max_array_length⌝ ∗ I [] ∗
        (* [f] is a function [Z → A], such that [f i] preserves
            an invariant [I] over the results of all calls to [f i] so far. *)
        {{ ∀ xs; ⌜0 ≤ i < n⌝ ∗ ⌜length xs = i⌝ ∗ I xs }}
        f i : Z
        {{ RET x; I (xs ++ singleton x) }}
    }}
      init n f : Z val
    (* Calling [init f n] returns an array [a] such that [ownArray a xs],
            and such that [Φ i] holds for the [i]'th element of xs. *)
    {{ RET a; ∃ (xs : list A), ⌜length xs = n⌝ ∗ a ↦∗ xs ∗ I xs }}.

  Definition init_spec' init : iProp Σ :=
    {{ ∀ `(Encode A, Inhabited A) (Φ : Z → A → iProp Σ);
      ⌜0 ≤ n ≤ max_array_length⌝ ∗ {{ ⌜0 ≤ i < n⌝ }} f i : Z {{ RET x; Φ i x }} }}
    init n f : Z val
    {{ RET a; ∃ (xs : list A), ⌜length xs = n⌝ ∗ a ↦∗ xs ∗ [∗ listZ] i↦x ∈ xs, Φ i x }}.

  Definition init_pure_spec init : iProp Σ :=
    {{ ∀ `(Encode A, Inhabited A) (Φ : Z → A);
       ⌜0 ≤ n ≤ max_array_length⌝ ∗ {{ ⌜0 ≤ i < n⌝ }} f i : Z {{ RET x; ⌜x = Φ i⌝ }} }}
    init n f : Z val
    {{ RET a; a ↦∗ list_z.init n Φ }}.

  Lemma init_spec_spec' init :
    init_spec init -∗ init_spec' init.
  Proof.
    iIntros "#Hinit !>".
    iApply (iSpec_mono with "Hinit"); simpl. iClear "Hinit".
    iIntros (n f m) "Hm".
    iIntros (A HencA HinhA Φ) "(%Hbounds & #Hf)".
    iApply ("Hm" $! A HencA HinhA (λ xs, [∗ listZ] i↦x ∈ xs, Φ i x)%I).
    iFrame "%". iSplit; first by iApply big_sepLZ_nil.
    iIntros "!>".
    iApply (iSpec_mono with "Hf").
    iIntros (i m') "Himp /=".
    iIntros (xs) "(%Hboundsi & <- & HΦs)".
    iSpecialize ("Himp" $! Hboundsi).
    iApply (imp_wand with "Himp").
    iIntros (x) "HΦ".
    iApply big_sepLZ_snoc. iFrame.
  Qed.

  Lemma init_spec'_pure_spec init :
    init_spec' init -∗ init_pure_spec init.
  Proof.
    iIntros "#Hinit !>".
    iApply (iSpec_mono with "Hinit"); simpl.
    iIntros (n f m) "Hm".
    iIntros (A HencA HinhA Φ) "(%Hbounds & #Hf)".
    iSpecialize ("Hm" $! A HencA HinhA (λ i x, ⌜x = Φ i⌝)%I with "[$Hf //]").
    iApply (imp_wand with "Hm").
    iIntros (a) "(%xs & %Hlen & Hown & HlistZ)".
    iPoseProof (big_sepLZ_pure_1 with "HlistZ") as "%Hlist".
    iAssert (⌜list_z.init n Φ = xs⌝)%I as "->".
    { iPureIntro.
      eapply list_eq_same_length.
      - length. apply eq_sym, Hlen.
      - reflexivity.
      - intros i Hvalid.
        lookup.
        apply lookup_valid_is_Some in Hvalid as [? Hlookup].
        rewrite Hlookup.
        apply Hlist in Hlookup as ->.
        reflexivity. }
    iApply "Hown".
  Qed.

  Lemma init_spec_pure_spec init :
    init_spec init -∗ init_pure_spec init.
  Proof.
    iIntros "Hinit".
    iApply init_spec'_pure_spec.
    by iApply init_spec_spec'.
  Qed.

  Definition init := (EAnonFun __init).

  Lemma imp_init η :
    □ in_env "make" array_make_spec η -∗
    □ in_env "unsafe_set" array_set_spec η -∗
    EWP (eval η init) {{ init_spec }}.
  Proof.
    iIntros "#Hlookup1 #Hlookup2".
    iApply imp_EAnon_pers.
    iIntros "!> /=".
    iIntros (n f A HencA HinhA I) "(%Hbounds & HI & #Hf)".
    iApply imp_please; iNext.

    (* [if l = 0] *)
    imp_if.
    { (* Case: [n = 0]. *)
      iApply imp_wand. iApply (imp_EArrayEmpty (A:=A)).
      iIntros (a) "$".
      iFrame. iPureIntro; length; lia. }

    (* [if l < 0] *)
    imp_if.
    { (* Case: [n < 0]. *)
      (* This case is forbidden by the spec. *) lia. }

    iApply (imp_ELet_var (B:=array) with "[HI]").
    { (* Subgoal: [make l (f 0)] *)
      imp_app τ[Z;A] with "[] [] [HI]".
      - (* (f 0) *)
        imp_app τ[Z].
        iIntros "Hm". iApply ("Hm" with "[$HI]").
        iPureIntro; length; lia.
      - iIntros "HI Hm".
        iApply ("Hm" with "[%//] HI"). }

    iIntros (res) "(%x & HΦx & HownArr)".

    (* Subgoal: [for i = 1 to ... done; res]. *)
    iApply (imp_ESeq with "[HownArr HΦx]").
    { (* Subgoal: [for i = 1 to ... done]. *)
      imp_for 1 to (n - 1) $!
        (λ i, ∃ xs,
            ⌜length xs = i⌝ ∗
            res ↦∗ (xs ++ replicate (n - i) x) ∗
            I xs)%I
        with "[] [] [HownArr HΦx]".
      { (* Prove that the loop invariant holds at index [1]. *)
        iFrame. iSplitR; first (iPureIntro; length; lia).
        rewrite (split_replicate x n 1); last lia.
        replicate. iFrame. }

      (* Prove the loop's body produces the loop invariant at index
         [i' + 1], assuming that the loop invariant holds at index
         [i']. *)
      iIntros (i Hbound) "(%xs & %Hlenxs & Hown & HI)".

      (* Subgoal: [unsafe_set res i (f i)]. *)
      imp_app τ[array;Z;A] with "[] [] [] [HI]".
      { (* unsafe_set *)
        iSpecialize ("ha" $! A HencA HinhA). iAssumption. }
      { (* (f i) *)
        imp_app τ[Z].
        iIntros "Hm".
        iApply ("Hm" with "[$HI]"); iPureIntro; length; lia. }
      iIntros "HI Hm".
      iDestruct "Hown" as "(%ls & #Harr & Htag & Hslice & %Hlenls)".
      iSpecialize ("Hm" with "Hslice [HI] [%]").
      { instantiate (1:=(λ y, I (xs ++ singleton y))). iFrame. }
      { length; lia. }
      iApply (imp_wand with "Hm").
      iIntros (_) "(% & $ & Hslice)".
      rewrite Z.sub_0_r -app_assoc.
      rewrite (split_replicate x (n - i) 1); last lia.
      update. replace (n - (i + 1)) with (n - i - 1) by lia.
      iPoseProof (isSlice_ownArray with "Harr Htag Hslice [%]") as "Hown".
      { length; length in Hlenls. lia. }
      iFrame. iPureIntro; length; lia. }

    iIntros "(%xs & %Hlen & Hslice & HI)".
    imp_path.
    replicate. unfold ownArray.
    iFrame. rewrite Hlen.
    replace (n - 1 + 1) with n by lia.
    assert (n `max` 1 = n) as -> by lia.
    by iFrame "#".
  Qed.

End init_proof.


Section iter_proof.

  Context `{!osirisGS Σ}.

  Definition invariant_preserving `{Encode A, Inhabited A} I xs f : iProp Σ :=
    {{ ∀ Xs; ⌜Xs ++ singleton X `prefix_of` xs⌝ ∗ I Xs }}
       f X : A
    {{ RET (); I (Xs ++ singleton X) }}.

  Definition iter_spec iter : iProp Σ :=
    {{ ∀ `(Encode A, Inhabited A) dq (xs : list A) (I : list A → iProp Σ);
        a ↦∗{dq} xs ∗ invariant_preserving I xs f ∗ I [] }}
    iter f a : val array
    {{ RET (); I xs ∗ a ↦∗{dq} xs }}.

  Definition iter := (EAnonFun __iter).

  Lemma singleton_prefix `{Inhabited A} x (xs : list A) :
    0 < length xs →
    x = xs !!! 0 →
    singleton x `prefix_of` xs.
  Proof.
    intros Hlen ->.
    exists (seg 1 (length xs) xs).
    rewrite -(seg_is_singleton 0 1 xs); try lia.
    rewrite -split_seg; try lia.
    by seg.
  Qed.

  Lemma complete_prefix {A} (xs ys : list A) :
    length xs = length ys →
    xs `prefix_of` ys →
    xs = ys.
  Proof.
    intros Hlen (xs' & ->).
    rewrite length_app in Hlen.
    assert (length xs' = 0) as Hlen0 by lia.
    apply nil_length_inv in Hlen0 as ->.
    by rewrite app_nil_r.
  Qed.

  Lemma prefix_snoc `{Inhabited A} (xs ys : list A) :
    ys `prefix_of` xs →
    length ys < length xs →
    ys ++ singleton (xs !!! length ys) `prefix_of` xs.
  Proof.
    intros (xs' & ->) Hlens.
    apply prefix_app.
    apply singleton_prefix.
    - revert Hlens; length; lia.
    - by lookup.
  Qed.

  Lemma imp_iter η :
    □ in_env "length" array_length_spec η -∗
    □ in_env "unsafe_get" array_get_spec η -∗
    EWP (eval η iter) {{ iter_spec }}.
  Proof.
    iIntros "#Hlength #Hget".
    iApply imp_EAnon_pers. simpl.
    iIntros "!>" (f a A HencA HinhA dq xs I) "(Hown & #Hf & HI)".
    iApply imp_please; iNext.
    iDestruct "Hown" as "(% & #Harr & Htag & Hslice & %Hlenls)".
    iPoseProof (isBlockLocs_length with "Harr") as "%Hmaxlength".
    length_nonneg xs.
    iApply (imp_wand with "[Hslice HI]").
    - imp_for 0 to (length xs - 1) $!
        (λ i, a ↦∗[0]{dq} xs ∗
              ∃ Xs, I Xs ∗ ⌜length Xs = i⌝ ∗ ⌜Xs `prefix_of` xs⌝)%I
        with "[] [] [-]".
      { set_postcondition (λ n, ⌜n = length ls⌝)%I.
        imp_app τ[array].
        iIntros "Hm". iApply ("Hm" with "Harr"). }
      { iIntros "->". iPureIntro. by rewrite Hlenls. }

      { (* Establish the invariant for [i = 0]. *)
        iFrame. iPureIntro. split; [ by length | apply prefix_nil ]. }

      (* Body of the [for] loop. *)
      iIntros (i') "%Hi' (Hslice & (%Xs & HI & <- & %Hprefix))".
      (* Subgoal: f (unsafe_get a i) *)
      imp_app τ[A] with "[] [Hslice]".
      { (* unsafe_get a i *)
        imp_app τ[array;Z].
        iIntros "Hm".
        iApply ("Hm" $! A with "Hslice [%]").
        lia. }
      iIntros "(-> & Hslice) Hm". rewrite Z.sub_0_r.
      apply prefix_snoc in Hprefix; try lia.
      iSpecialize ("Hm" with "[$HI //]").
      iApply (imp_wand with "Hm").
      iIntros ([]) "$". iFrame.
      iPureIntro.
      split; [ length; reflexivity | assumption ].
    - iIntros ([]) "(Hslice & %Xs & HI & %HlenXs & %Hprefix)".
      (* Show that we have covered the full list. *)
      rewrite (complete_prefix Xs xs); [ | lia | assumption ].
      iFrame "HI".
      iApply (isSlice_ownArray with "Harr Htag Hslice [//]").
  Qed.

End iter_proof.


(* TODO: copy, append, sub, fill, blit use unsupported primitives
   (unsafe_sub, append_prim, unsafe_blit, unsafe_fill). *)

Section iter2_spec.

  Context `{!osirisGS Σ}.

  (** [iter2 f a b] applies function [f] to all elements of [a] and [b]
      pairwise. Raises if the arrays have different lengths. *)
  Definition iter2_spec iter2 : iProp Σ :=
  {{ ∀ `(Encode A, Inhabited A) `(Encode B, Inhabited B)
        dq1 dq2 (xs : list A) (ys : list B) (I : list (A * B) → iProp Σ);
        ⌜length xs = length ys⌝ ∗
         a ↦∗{dq1} xs ∗
         b ↦∗{dq2} ys ∗
         {{ ∀ (visited : list (A * B)); ⌜visited ++ singleton (x, y) `prefix_of` zip xs ys⌝ ∗ I visited }}
         f x y : A B
         {{ RET (); I (visited ++ singleton (x, y)) }} ∗
         I [] }}
  iter2 f a b : val array array
  {{ RET (); I (zip xs ys) ∗ a ↦∗{dq1} xs ∗ b ↦∗{dq2} ys }}.

End iter2_spec.


Section map_spec.

  Context `{!osirisGS Σ}.

  (** [map f a] applies function [f] to all elements of [a], and builds
      a new array with the results returned by [f]. *)
  Definition map_spec map : iProp Σ :=
  {{ ∀ `(Encode A, Inhabited A) `(Encode B, Inhabited B) dq (xs : list A) (Φ : A → B → iProp Σ);
     a ↦∗{dq} xs ∗ {{ True }} f x : τ[A] {{ RET y; Φ x y }} }}
  map f a : val array
  {{ RET b; ∃ (ys : list B), b ↦∗ ys ∗ a ↦∗{dq} xs ∗
                             [∗ listZ] x;y ∈ xs;ys, Φ x y }}.

  Definition map := (EAnonFun __map).

  Lemma imp_map η :
    □ in_env "length" array_length_spec η -∗
    □ in_env "unsafe_get" array_get_spec η -∗
    □ in_env "unsafe_set" array_set_spec η -∗
    □ in_env "make" array_make_spec η -∗
    EWP (eval η map) {{ map_spec }}.
  Proof.
    iIntros "#Hlength #Hget #Hset #Hmake".
    iApply imp_EAnon_pers. simpl.
    iIntros "!>" (f a A HencA HinhA B HencB HinhB dq xs Φ) "(Hown & #Hf)".
    iApply imp_please; iNext.
    iDestruct "Hown" as "(%ls & #Harr & Htag & Hslice & %Hlenls)".
    iPoseProof (isBlockLocs_length with "Harr") as "%Hmaxlength".

    (* let l = length a in ... *)
    iApply (imp_ELet_var (B:=Z) with "[]").
    { imp_app τ[array].
      iIntros "Hm". iApply ("Hm" with "Harr"). }
    iIntros (l) "->".

    length_nonneg xs.

    (* if l = 0 then [||] else ... *)
    imp_if.
    { (* Case: length xs = 0, so xs = [] *)
      iApply imp_wand.
      iApply (imp_EArrayEmpty (A:=B)).
      iIntros (a') "$". iFrame "∗#".
      rewrite (nil_length_inv xs); last lia.
      iSplit. iPureIntro. length; lia.
      by rewrite big_sepLZ2_nil. }

    (* Case: length xs > 0 *)

    (* let r = make l (f (unsafe_get a 0)) in ... *)
    iApply (imp_ELet_var (B:=array) with "[Hslice]").
    { set_postcondition
        (λ r, ∃ y, a ↦∗[0]{dq} xs ∗ Φ (xs !!! 0) y ∗ r ↦∗ (replicate (length xs) y))%I.
      imp_app τ[Z; B] with "[] [] [Hslice]".
      { (* f (unsafe_get a 0) *)
        imp_app τ[A] with "[] [Hslice]".
        (* function: f *)
        (* arg: unsafe_get a 0 *)
        { imp_app τ[array; Z].
          (* continuation for unsafe_get *)
          iIntros "Hm".
          iSpecialize ("Hm" $! A with "Hslice").
          iApply "Hm".
          iPureIntro; lia. }
        (* continuation for f *)
        iIntros "(%Hlookup & Hslice) Hm".
        set_postcondition (λ y, a ↦∗[0]{dq} xs ∗ Φ (xs !!! 0) y)%I.
        iFrame "Hslice". rewrite Hlookup Z.sub_0_r.
        by iApply "Hm". }
      (* continuation for make *)
      iIntros "($ & HΦy0) Hm".
      rewrite Hlenls.
      iApply ("Hm" with "[%] HΦy0"); first lia. }

    (* We have now allocated a new array, [res]. *)

    iIntros (res) "(%y & HsliceSrc & HΦy & HownRes)".
    iDestruct "HownRes" as "(%ls' & #Harr' & HtagRes & HsliceRes & %Hlenls')".
    length in Hlenls'.

    (* for i = 1 to l - 1 do unsafe_set r i (f (unsafe_get a i)) done; r *)
    iApply (imp_ESeq with "[HsliceSrc HsliceRes HΦy]").
    { imp_for 1 to (length xs - 1) $!
        (λ i, a ↦∗[0]{dq} xs ∗
              ∃ (ys : list B),
                res ↦∗[0] (ys ++ replicate (length xs - i) y) ∗
                [∗ listZ] x;y ∈ seg 0 i xs;ys, Φ x y)%I
        with "[] [] [HsliceSrc HsliceRes HΦy]".

      { (* Initial invariant at i = 1 *)
        iFrame "HsliceSrc".
        rewrite (split_replicate y _ 1); last lia. replicate.
        iFrame "HsliceRes".
        rewrite seg_is_singleton; try lia.
        iApply (big_sepLZ2_singleton with "HΦy"). }

      (* Loop body: unsafe_set r i (f (unsafe_get a i)) *)
      iIntros (i') "%Hi' (HsliceSrc & %ys & HsliceRes & HΦs)".
      imp_app τ[array; Z; B] with "[] [] [] [HsliceSrc HsliceRes HΦs]".
      { (* unsafe_set *) iSpecialize ("ha" $! B HencB HinhB). iAssumption. }
      { (* f (unsafe_get a i) *)
        imp_app τ[A] with "[] [HsliceSrc]".
        (* function: f *)
        (* arg: unsafe_get a i *)
        { imp_app τ[array;Z].
          (* continuation for unsafe_get on source array a *)
          iIntros "Hm".
          iApply ("Hm" $! A with "HsliceSrc").
          - iPureIntro; lia. }
        (* continuation for f *)
        iIntros "(%Hlookup & HsliceSrc) Hm /=".
        set_postcondition
          (λ x,
             a ↦∗[0]{dq} xs ∗
             res ↦∗[0] (ys ++ replicate (length xs - i') y) ∗
             Φ (xs !!! i') x ∗
             [∗ listZ] x;y ∈ (seg 0 i' xs);ys, Φ x y)%I.
        iFrame. rewrite Hlookup Z.sub_0_r. by iApply "Hm". }
      (* continuation for unsafe_set *)
      iIntros "($ & HsliceRes & HΦy & HΦs) Hm".
      iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenys".
      length in Hlenys. length_nonneg ys.
      iSpecialize ("Hm" with "HsliceRes HΦy [%]").
      { length. lia. }
      iApply (imp_wand with "Hm").
      iIntros ([]) "(% & HΦ & HsliceRes)".
      iExists (ys ++ singleton x0).
      update.
      replace (length xs - i' -1 - (i' - 0 -length ys))
        with (length xs - (i' + 1)) by lia.
      rewrite app_assoc. iFrame.

      rewrite (split_seg i' xs 0 (i' + 1)); try lia.
      iApply (big_sepLZ2_app with "HΦs").
      rewrite seg_is_singleton; try lia.
      iApply (big_sepLZ2_singleton with "HΦ"). }

    (* After the loop: return r *)
    iIntros "(HownSrc & %ys & HsliceRes & HΦs)".
    imp_path. seg. replicate.
    iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenys".
    iFrame "HΦs".
    iPoseProof (isSlice_ownArray with "Harr Htag HownSrc [//]") as "$".
    iPoseProof (isSlice_ownArray with "Harr' HtagRes HsliceRes [%]") as "$".
    lia.
  Qed.

End map_spec.


Section map_inplace_spec.

  Context `{!osirisGS Σ}.

  (** [map_inplace f a] applies function [f] to all elements of [a],
      replacing each element with the result in place. *)
  Definition map_inplace_spec map_inplace : iProp Σ :=
  {{ ∀ `(Encode A, Inhabited A) (xs : list A) (Φ : A → A → iProp Σ);
     a ↦∗ xs ∗ {{ True }} f x : τ[A] {{ RET y; Φ x y }} }}
  map_inplace f a : val array
  {{ RET (); ∃ (ys : list A), a ↦∗ ys ∗ [∗ listZ] x;y ∈ xs;ys, Φ x y }}.

  Definition map_inplace := (EAnonFun __map_inplace).

  Lemma imp_map_inplace η :
    □ in_env "length" array_length_spec η -∗
    □ in_env "unsafe_get" array_get_spec η -∗
    □ in_env "unsafe_set" array_set_spec η -∗
    EWP (eval η map_inplace) {{ map_inplace_spec }}.
  Proof.
    iIntros "#Hlength #Hget #Hset".
    iApply imp_EAnon_pers.
    iIntros "!>" (f a A HencA HinhA xs Φ) "(Hown & #Hf)".
    iApply imp_please; iNext.
    iDestruct "Hown" as "(%ls & #Ha & Htag & Hslice_init & %Hlenls)".
    iPoseProof (isBlockLocs_length with "Ha") as "%Hboundxs".
    length_nonneg xs.

    iApply (imp_wand with "[Hslice_init]").
    - imp_for 0 to (length xs - 1) $!
        (λ i, ∃ (ys : list A),
             a ↦∗[0] (ys ++ seg i (length xs) xs) ∗
            [∗ listZ] x;y ∈ (seg 0 i xs);ys, Φ x y)%I
        with "[] [] [-]".
      { set_postcondition (λ n, ⌜n = length ls⌝)%I.
        imp_app τ[array].
        iIntros "Hm". iApply ("Hm" with "Ha"). }
      { iIntros "->". iPureIntro. by rewrite Hlenls. }

      { (* Establish the invariant for [i = 0]. *)
        iExists []. seg. rewrite big_sepLZ2_nil. iFrame. }

      iIntros (i) "%Hi (%ys & Hslice & HΦs)".
      iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenys".
      length in Hlenys.
      (* unsafe_set a i (f (unsafe_get a i)) *)
      imp_app τ[array; Z; A] with "[] [] [] [Hslice HΦs]".
      { (* unsafe_set *) iSpecialize ("ha" $! A HencA HinhA). iAssumption. }
      { (* arg 3: f (unsafe_get a i) *)
        set_postcondition (λ (y : A), a ↦∗[0] (ys ++ seg i (length xs) xs) ∗
                                Φ _ y ∗
                                [∗ listZ] x;y ∈ (seg 0 i xs);ys, Φ x y)%I.
        imp_app τ[A] with "[] [Hslice]".
        (* function: f *)
        { (* arg: unsafe_get a i *)
          imp_app τ[array;Z].
          (* continuation for unsafe_get *)
          iIntros "Hm".
          iApply ("Hm" $! A with "Hslice").
          iPureIntro; length; lia. }
        (* continuation for f *)
        iIntros "(-> & $) Hm". iFrame "HΦs".
        by iApply "Hm". }
      (* continuation for unsafe_set: all three args resolved *)
      iIntros "(Hslice & HΦy & HΦs) Hm".
      iSpecialize ("Hm" with "Hslice HΦy [%]"); first (length; lia).

      iApply (imp_wand with "Hm [HΦs]").
      iIntros ([]) "(% & HΦ & Hslice)". rewrite Z.sub_0_r.
      iExists (ys ++ singleton x0).
      rewrite {2}(split_seg (i+1) xs i (length xs)); try lia.
      rewrite (seg_is_singleton i (i + 1)); try lia.
      update. rewrite app_assoc.
      iFrame "Hslice".

      rewrite (split_seg i xs 0 (i+1)); try lia.
      iApply (big_sepLZ2_app with "HΦs").
      rewrite (seg_is_singleton i (i+1)); try lia.
      iApply big_sepLZ2_singleton. lookup.
      replace (i + (i - length ys)) with i by lia.
      iApply "HΦ".

    - iIntros ([]) "(%ys & Hslice & HΦs)".
      seg.
      iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenys". iFrame "HΦs".
      iApply (isSlice_ownArray with "Ha Htag Hslice [%]").
      lia.
  Qed.

End map_inplace_spec.


Section mapi_inplace_spec.

  Context `{!osirisGS Σ}.

  (** [mapi_inplace f a] applies function [f] to the index and all elements
      of [a], replacing each element with the result in place. *)
  Definition mapi_inplace_spec mapi_inplace : iProp Σ :=
  {{ ∀ `(Encode A, Inhabited A) (xs : list A) (Φ : Z → A → A → iProp Σ);
     a ↦∗ xs ∗ {{ ⌜0 ≤ i < length xs⌝ }} f i x : Z A {{ RET y; Φ i x y }} }}
  mapi_inplace f a : val array
  {{ RET (); ∃ (ys : list A), a ↦∗ ys ∗ [∗ listZ] i↦x;y ∈ xs;ys, Φ i x y }}.

  Definition mapi_inplace := (EAnonFun __mapi_inplace).

  Lemma imp_mapi_inplace η :
    □ in_env "length" array_length_spec η -∗
    □ in_env "unsafe_get" array_get_spec η -∗
    □ in_env "unsafe_set" array_set_spec η -∗
    EWP (eval η mapi_inplace) {{ mapi_inplace_spec }}.
  Proof.
    iIntros "#Hlength #Hget #Hset".
    iApply imp_EAnon_pers.
    iIntros "!>" (f a A HencA HinhA xs Φ) "(Hown & #Hf)".
    iApply imp_please; iNext.
    iDestruct "Hown" as "(%ls & #Ha & Htag & Hslice_init & %Hlenls)".
    iPoseProof (isBlockLocs_length with "Ha") as "%Hboundxs".
    length_nonneg xs.

    iApply (imp_wand with "[Hslice_init]").
    - imp_for 0 to (length xs - 1)
        $! (λ i, ∃ (ys : list A),
            a ↦∗[0] (ys ++ seg i (length xs) xs) ∗
            [∗ listZ] j↦x;y ∈ (seg 0 i xs);ys, Φ j x y)%I
        with "[] [] [-]".
      { set_postcondition (λ n, ⌜n = length ls⌝)%I.
        imp_app τ[array].
        iIntros "Hm". iApply ("Hm" with "Ha"). }
      { iIntros "->". iPureIntro. lia. }

      { (* Establish the invariant for [i = 0]. *)
        iExists []. seg. rewrite big_sepLZ2_nil. iFrame. }

      iIntros (i) "%Hi (%ys & Hslice & HΦs)".
      iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenys".
      revert Hlenys; length; intros.
      (* unsafe_set a i (f i (unsafe_get a i)) *)
      imp_app τ[array; Z; A] with "[] [] [] [Hslice HΦs]".
      { (* unsafe_set *) iSpecialize ("ha" $! A HencA HinhA). iAssumption. }
      { (* arg 3: f i (unsafe_get a i) *)
        set_postcondition
          (λ y, a ↦∗[0] (ys ++ seg i (length xs) xs) ∗
                Φ i _ y ∗
                [∗ listZ] j↦x;y ∈ (seg 0 i xs);ys, Φ j x y)%I.
        imp_app τ[Z; A] with "[] [] [Hslice]".
        (* function: f *)
        { (* arg 2 to f: unsafe_get a i *)
          imp_app τ[array;Z].
          (* continuation for unsafe_get *)
          iIntros "Hm".
          iApply ("Hm" $! A with "Hslice").
          iPureIntro; length; lia. }
        (* continuation for f: gets i and element *)
        iIntros "(-> & Hslice) Hm".
        iSpecialize ("Hm" with "[%]"); first lia.
        iApply (imp_wand with "Hm [Hslice HΦs]").
        lookup.
        iIntros (y) "$". iFrame. }

      (* continuation for unsafe_set: all three args resolved *)
      iIntros "(Hslice & HΦy & HΦs) Hm".
      iSpecialize ("Hm" with "Hslice HΦy [%]"); first (length; lia).
      iApply (imp_wand with "Hm").
      iIntros ([]) "(%x0 & HΦ & Hslice)".
      iExists (ys ++ singleton x0).
      rewrite (split_seg (i+1) xs i); try lia.
      rewrite seg_is_singleton'; try lia.
      update. rewrite app_assoc.
      iFrame "Hslice".

      rewrite (split_seg i xs 0 (i+1)); try lia.
      iApply (big_sepLZ2_app with "HΦs").
      rewrite seg_is_singleton'; try lia.
      iApply big_sepLZ2_singleton. length. lookup.
      replace (i + (i - length ys)) with i by lia. by rewrite Z.add_0_r.

    - iIntros ([]) "(%ys & Hslice & HΦs)".
      seg.
      iPoseProof (big_sepLZ2_length with "HΦs") as "%Hlenys".
      iPoseProof (isSlice_ownArray with "Ha Htag Hslice [%]") as "Hown".
      { revert Hlenys; length; intros. lia. }
      iFrame.
  Qed.

End mapi_inplace_spec.


Section map2_spec.

  Context `{!osirisGS Σ}.

  (** [map2 f a b] applies function [f] to all elements of [a] and [b]
      pairwise, and builds an array with the results. *)
  Definition map2_spec : val → array → array → microvx → iProp Σ :=
    λ f a b m,
      (∀ (A B C : Type) (_ : Encode A) (_ : Encode B) (_ : Encode C)
         (_ : Inhabited A) (_ : Inhabited B)
         dq1 dq2 (xs : list A) (ys : list B) (Φ : A → B → C → iProp Σ),
         ⌜length xs = length ys⌝ -∗
         a ↦∗{dq1} xs -∗
         b ↦∗{dq2} ys -∗
         □ iSpec τ[A; B] f (λ (x : A) (y : B) m, EWP m {{ (z : C), Φ x y z }}) -∗
         EWP m {{ c, ∃ (zs : list C),
                    ⌜length zs = length xs⌝ ∗
                    c ↦∗ zs ∗
                    a ↦∗{dq1} xs ∗
                    b ↦∗{dq2} ys ∗
                    [∗ listZ] t;z ∈ (zip xs ys); zs, Φ t.1 t.2 z }})%I.

End map2_spec.


Section iteri_spec.

  Context `{!osirisGS Σ}.


  (** [iteri f a] applies function [f] to the index and all elements of [a],
      in order. Like [iter] but [f] also receives the index. *)
  Definition iteri_spec : val → array → microvx → iProp Σ :=
    λ f a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A) dq (xs : list A) (I : list A → iProp Σ),
         a ↦∗{dq} xs -∗
         □ iSpec τ[Z; A] f (λ (i : Z) (x : A) m,
                              ∀ (Xs : list A),
                              ⌜Xs ++ singleton x `prefix_of` xs⌝ -∗
                              ⌜length Xs = i⌝ -∗
                              I Xs -∗
                              EWP m {{ (_ : unit), I (Xs ++ singleton x) }}) -∗
         I [] -∗
         EWP m {{ (_ : unit), I xs ∗ a ↦∗{dq} xs }})%I.

  Definition iteri := (EAnonFun __iteri).

  Lemma imp_iteri η :
    □ in_env "length" array_length_spec η -∗
    □ in_env "unsafe_get" array_get_spec η -∗
    EWP (eval η iteri) {{ c, □ iSpec τ[val; array] c iteri_spec }}.
  Proof.
    iIntros "#Hlookup #Hlookup'".
    iApply imp_EAnon_pers.
    iIntros "!>" (f a A HencA HinhA dq xs I) "Hown #Hf HI".
    iApply imp_please; iNext.
    iDestruct "Hown" as "(%ls & #Ha & Htag & Hslice_init & %Hlenls)".
    iPoseProof (isBlockLocs_length with "Ha") as "%Hboundxs".
    length_nonneg xs.

    iApply (imp_wand with "[Hslice_init HI]").
    - imp_for 0 to (length xs - 1)
        $! (λ i, a ↦∗[0]{dq} xs ∗ ∃ Xs, I Xs ∗ ⌜length Xs = i⌝ ∗ ⌜Xs `prefix_of` xs⌝)%I
        with "[] [] [-]".
      { set_postcondition (λ n, ⌜n = length ls⌝)%I.
        imp_app τ[array].
        iIntros "Hm". iApply ("Hm" with "Ha"). }
      { iIntros "->". iPureIntro. lia. }

      { (* Establish the invariant when [i = 0]. *)
        iFrame. iPureIntro. split; [ by length | apply prefix_nil ]. }

      iIntros (i') "%Hi' (Hslice & (%Xs & HI & %HlenXs & %Hprefix))".
      (* f i (unsafe_get a i) *)
      imp_app τ[Z;A] with "[] [] [Hslice]".
      (* unsafe_get a i *)
      { imp_app τ[array;Z].
        iIntros "Hm".
        iApply ("Hm" $! A with "Hslice [%]").
        lia. }
      iIntros "(%Hget & Hslice) Hm".
      assert (Xs ++ singleton x `prefix_of` xs).
      { destruct Hprefix as (xrest & ->); rewrite length_app in Hi'.
        apply prefix_app.
        apply singleton_prefix; first lia.
        rewrite Hget. lookup.
        by rewrite HlenXs Z.sub_diag. }
      iSpecialize ("Hm" with "[//] [//] HI").

      iApply (imp_wand with "Hm").
      iIntros ([]) "$". iFrame.
      iPureIntro; split; [ length; lia | assumption ].

    - iIntros ([]) "(Hslice & %Xs & HI & %HlenXs & %Hprefix)".
      rewrite (complete_prefix Xs xs); [ | lia | assumption ].
      iFrame "HI".
      iApply (isSlice_ownArray with "Ha Htag Hslice [//]").
  Qed.

End iteri_spec.


Section mapi_spec.

  Context `{!osirisGS Σ}.


  (** [mapi f a] applies function [f] to the index and all elements of [a],
      and builds an array with the results. *)
  Definition mapi_spec : val → array → microvx → iProp Σ :=
    λ f a m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A)
         dq (xs : list A) (Φ : Z → A → B → iProp Σ),
         a ↦∗{dq} xs -∗
         □ iSpec τ[Z; A] f (λ (i : Z) (x : A) m,
                              ⌜0 ≤ i < length xs⌝ -∗
                              EWP m {{ (y : B), Φ i x y }}) -∗
         EWP m {{ b, ∃ (ys : list B),
                    b ↦∗ ys ∗
                    a ↦∗{dq} xs ∗
                    [∗ listZ] i↦x;y ∈ xs;ys, Φ i x y }})%I.

End mapi_spec.


Section to_list_spec.

  Context `{!osirisGS Σ}.


  (** [to_list a] returns a list containing the elements of [a]. *)
  Definition to_list_spec : array → microvx → iProp Σ :=
    λ a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A) dq (xs : list A),
         a ↦∗{dq} xs -∗
         EWP m {{ (ys : list A), ⌜ys = xs⌝ ∗ a ↦∗{dq} xs }})%I.

End to_list_spec.


Section of_list_spec.

  Context `{!osirisGS Σ}.


  (** [of_list l] returns a fresh array containing the elements of [l]. *)
  Definition of_list_spec : val → microvx → iProp Σ :=
    λ l m,
      (∀ (A : Type) (_ : Encode A) (xs : list A),
         ⌜l = #xs⌝ -∗
         ⌜length xs ≤ max_array_length⌝ -∗
         EWP m {{ a, a ↦∗ xs }})%I.

End of_list_spec.


Section equal_spec.

  Context `{!osirisGS Σ}.


  (** [equal eq a b] tests whether [a] and [b] are element-wise equal,
      using [eq] to compare elements. *)
  Definition equal_spec : val → array → array → microvx → iProp Σ :=
    λ eq a b m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq1 dq2 (xs ys : list A) (P : A → A → Prop) (_ : ∀ x y, Decision (P x y)),
         a ↦∗{dq1} xs -∗
         b ↦∗{dq2} ys -∗
         □ iSpec τ[A; A] eq (λ (x : A) (y : A) m,
                               EWP m {{ (r : bool), ⌜r = bool_decide (P x y)⌝ }}) -∗
         EWP m {{ (r : bool),
                    a ↦∗{dq1} xs ∗
                    b ↦∗{dq2} ys ∗
                    ⌜r = true ↔ length xs = length ys ∧ Forall2 P xs ys⌝ }})%I.

End equal_spec.


Section compare_spec.

  Context `{!osirisGS Σ}.


  (** [compare cmp a b] compares arrays lexicographically using [cmp]
      for elements. Returns an integer: negative, zero, or positive. *)
  Definition compare_spec : val → array → array → microvx → iProp Σ :=
    λ cmp a b m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq1 dq2 (xs ys : list A) (f : A → A → Z),
         a ↦∗{dq1} xs -∗
         b ↦∗{dq2} ys -∗
         □ iSpec τ[A; A] cmp (λ (x : A) (y : A) m,
                                EWP m {{ (c : Z), ⌜c = f x y⌝ }}) -∗
         EWP m {{ (r : Z),
                    a ↦∗{dq1} xs -∗
                    b ↦∗{dq2} ys -∗
                    ⌜(length xs ≠ length ys → r = if bool_decide (length xs < length ys) then -1 else 1) ∧
                     (length xs = length ys → (r = 0 ↔ Forall2 (λ x y, f x y = 0) xs ys))⌝ }})%I.

End compare_spec.


Section fold_left_spec.

  Context `{!osirisGS Σ}.


  (** [fold_left f init a] computes [f (... (f (f init a.(0)) a.(1)) ...) a.(n-1)]. *)
  Definition fold_left_spec fold_left : iProp Σ :=
  ∀∀ `(Encode A) `(Encode B);
  {{ ∀ `(Inhabited B) dq (xs : list B) (I : A → list B → iProp Σ);
     a ↦∗{dq} xs ∗
     {{ ∀ visited; ⌜visited ++ singleton b `prefix_of` xs⌝ ∗ I acc visited }}
     f acc b : A B
     {{ RET acc'; I acc' (visited ++ singleton b) }} ∗
     I x [] }}
  fold_left f x a : val A array
  {{ RET r; I r xs ∗ a ↦∗{dq} xs }}.

  (** [fold_left f init a] computes [f (... (f (f init a.(0)) a.(1)) ...) a.(n-1)]. *)
  Definition fold_left_pure_spec fold_left : iProp Σ :=
  ∀∀ `(Encode A) `(Encode B);
  {{ ∀ `(Inhabited B) dq (xs : list B) (Φ : A → B → A);
     a ↦∗{dq} xs ∗
     {{ True }} f acc b : A B {{ RET acc'; ⌜acc' = Φ acc b⌝ }} }}
  fold_left f x a : val A array
  {{ RET r; ⌜r = List.fold_left Φ xs x⌝ ∗ a ↦∗{dq} xs }}.

  Lemma fold_left_spec_pure_spec :
    ∀ fold_left, fold_left_spec fold_left -∗ fold_left_pure_spec fold_left.
  Proof.
    iIntros (fl) "#Hflspec". unfold fold_left_pure_spec; simpl.
    iIntros (A HencA B HencB) "!>".
    iSpecialize ("Hflspec" $! A _ B _).
    iApply (iSpec_mono with "Hflspec").
    iIntros (f x a m) "Hm". iIntros (HinhB dq xs Φ) "(Hown & #Hf)".
    iApply ("Hm" $! _ dq xs (λ acc visited, ⌜acc = fold_left Φ visited x⌝)%I with "[$Hown]").
    iSplit; [ iModIntro | done ].
    iApply (iSpec_mono with "Hf").
    iIntros (acc b m') "Hm %visited (%Hvisited & %Hacc)".
    iSpecialize ("Hm" with "[//]").
    iApply (imp_wand with "Hm").
    iPureIntro.
    intros acc' Hacc'.
    rewrite fold_left_app Hacc' Hacc.
    reflexivity.
  Qed.

  Definition fold_left := (EAnonFun __fold_left).

  Lemma imp_fold_left η :
    □ in_env "length" array_length_spec η -∗
    □ in_env "unsafe_get" array_get_spec η -∗
    EWP (eval η fold_left) {{ fold_left_spec }}.
  Proof.
    iIntros "#Hlookup #Hlookup'".
    iApply imp_EAnon_poly_pers.
    iIntros (A HencA) "!>".
    iIntros (f x a B HencB HinhB dq xs I) "Hown #Hf HI".
    iApply imp_please; iNext.

    (* let r = ref x in ... *)
    iApply (imp_ELet_var (B:=loc)).
    { imp_ref x. }
    iIntros (r) "Hr".

    iDestruct "Hown" as "(%ls & #Ha & Htag & Hslice_init & %Hlenls)".
    iPoseProof (isBlockLocs_length with "Ha") as "%Hboundxs".
    length_nonneg xs.
    (* for i = 0 to length a - 1 do r := f !r (unsafe_get a i) done; !r *)
    iApply (imp_ESeq with "[Hslice_init HI Hr]").
    { imp_for 0 to (length xs - 1) $!
        (λ i, a ↦∗[0]{dq} xs ∗
              ∃ (acc : A) (Xs : list B),
                r ↦ #acc ∗ I acc Xs ∗ ⌜length Xs = i⌝ ∗ ⌜Xs `prefix_of` xs⌝)%I
        with "[] [] [-]".
      { set_postcondition (λ n, ⌜n = length ls⌝)%I.
        imp_app τ[array].
        iIntros "Hm". iApply ("Hm" with "Ha"). }
      { iIntros "->". iPureIntro. lia. }

      { (* Establish the invariant for [i = 0]. *)
        iFrame. iPureIntro. split; first by length. apply prefix_nil. }

      iIntros (i') "%Hi' (Hslice & %acc & %Xs & Hr & HI & <- & %Hprefix)".
      (* r := f !r (unsafe_get a i) *)
      iApply (imp_wand with "[Hr HI Hslice]").
      set_postcondition
        (λ (_ : unit), ∃ x X, ⌜Xs ++ singleton X `prefix_of` xs⌝ ∗
                              r ↦ #x ∗ a ↦∗[0]{dq} xs ∗ I x (Xs ++ singleton X))%I.
      - iApply (imp_EStore2 (A:=A) with "[] [Hr HI Hslice]").
        imp_path.
        + (* f !r (unsafe_get a i) *)
          set_postcondition
            (λ x, ∃ X, ⌜Xs ++ singleton X `prefix_of` xs⌝ ∗
                       r ↦ #acc ∗ a ↦∗[0]{dq} xs ∗ I x (Xs ++ singleton X))%I.
          imp_app τ[A; B] with "[] [Hr] [Hslice]".
          { (* unsafe_get a i *)
            imp_app τ[array;Z].
            iIntros "Hm".
            iApply ("Hm" $! B with "Hslice [%]").
            lia. }
          (* continuation after getting the element *)
          iIntros "(-> & Hr) (-> & Hslice) Hm". rewrite Z.sub_0_r.
          apply prefix_snoc in Hprefix; last lia.
          iSpecialize ("Hm" with "[//] HI").

          iApply (imp_wand with "Hm").
          iIntros (acc'') "HI".
          iFrame "∗%".
        + iIntros (?) "(%acc' & Hpref & Hr & Hslice & HI)".
          iFrame.
          iIntros "!> !> $". iFrame.
      - iIntros ([]) "(% & % & Hpref & Hr & Hslice & HI)".
        iFrame. iPureIntro; length; lia. }

    iIntros "(Hslice & %acc' & %Xs & Hr & HI & %HlenXs & %Hprefix)".
    iApply (imp_wand with "[Hr]"). { imp_load r. }
    iIntros (?) "(-> & Hr)".
    rewrite (complete_prefix Xs xs); [ | lia | assumption ].
    iFrame "HI".
    iApply (isSlice_ownArray with "Ha Htag Hslice [//]").
  Qed.

End fold_left_spec.


Section fold_left_map_spec.

  Context `{!osirisGS Σ}.
  Context (A : Type) `{HencA : !Encode A}.


  (** [fold_left_map f acc input_array] is like [fold_left] but also builds
      an output array from the second component of [f]'s return value. *)
  Definition fold_left_map_spec : val → A → array → microvx → iProp Σ :=
    λ f x input_array m,
      (∀ `(Encode B, Inhabited B) `(Encode C)
         dq (xs : list B) (Φ : A → B → A → C → iProp Σ),
         input_array ↦∗{dq} xs -∗
         □ iSpec τ[A; B] f (λ (acc : A) (b : B) m,
                              EWP m {{ (p : τ[A; C]), Φ acc b p.1 p.2 }}) -∗
         EWP m {{ ((y, output_array) : τ[A; array]),
                    ∃ (ys : list C), ⌜length ys = length xs⌝ ∗
                      input_array ↦∗{dq} xs ∗
                      output_array ↦∗ ys ∗
                      ⌜True⌝ (* TODO: characterize the final accumulator and output *) }})%I.

End fold_left_map_spec.


Section fold_right_spec.

  Context `{!osirisGS Σ}.
  Context (B : Type) `{!Encode B}.


  (** [fold_right f a init] computes [f a.(0) (f a.(1) (... (f a.(n-1) init) ...))]. *)
  Definition fold_right_spec : val → array → B → microvx → iProp Σ :=
    λ f a x m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq (xs : list A) (I : B → Z → iProp Σ),
         a ↦∗{dq} xs -∗
         □ iSpec τ[A; B] f (λ (a : A) (b : B) m,
                              ∀ i, ⌜0 ≤ i < length xs⌝ -∗
                                   ⌜xs !!! i = a⌝ -∗
                                   I b (i + 1) -∗
                                   EWP m {{ (b' : B), I b' i }}) -∗
         I x (length xs) -∗
         EWP m {{ (r : B), I r 0 ∗ a ↦∗{dq} xs }})%I.

End fold_right_spec.


Section exists_spec.

  Context `{!osirisGS Σ}.


  (** [exists p a] checks if at least one element of [a] satisfies [p]. *)
  Definition exists_spec : val → array → microvx → iProp Σ :=
    λ p a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq (xs : list A) (P : A → Prop) (_ : ∀ x, Decision (P x)),
         a ↦∗{dq} xs -∗
         □ iSpec τ[A] p (λ (x : A) m,
                           EWP m {{ (b : bool), ⌜b = bool_decide (P x)⌝ }}) -∗
         EWP m {{ (b : bool),
                    a ↦∗{dq} xs ∗
                    ⌜b = true ↔ Exists P xs⌝ }})%I.

End exists_spec.


Section for_all_spec.

  Context `{!osirisGS Σ}.


  (** [for_all p a] checks if all elements of [a] satisfy the predicate [p]. *)
  Definition for_all_spec : val → array → microvx → iProp Σ :=
    λ p a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq (xs : list A) (P : A → Prop) (_ : ∀ x, Decision (P x)),
         a ↦∗{dq} xs -∗
         □ iSpec τ[A] p (λ (x : A) m,
                           EWP m {{ (b : bool), ⌜b = bool_decide (P x)⌝ }}) -∗
         EWP m {{ (b : bool),
                    a ↦∗{dq} xs ∗
                    ⌜b = true ↔ Forall P xs⌝ }})%I.

End for_all_spec.


Section for_all2_spec.

  Context `{!osirisGS Σ}.


  (** [for_all2 p a b] checks if all corresponding elements of [a] and [b]
      satisfy the predicate [p]. Raises if the arrays have different lengths. *)
  Definition for_all2_spec : val → array → array → microvx → iProp Σ :=
    λ p a b m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A) (_ : Inhabited B)
         dq1 dq2 (xs : list A) (ys : list B) (P : A → B → Prop) (_ : ∀ x y, Decision (P x y)),
         ⌜length xs = length ys⌝ -∗
         a ↦∗{dq1} xs -∗
         b ↦∗{dq2} ys -∗
         □ iSpec τ[A; B] p (λ (x : A) (y : B) m,
                              EWP m {{ (r : bool), ⌜r = bool_decide (P x y)⌝ }}) -∗
         EWP m {{ (r : bool),
                    a ↦∗{dq1} xs ∗
                    b ↦∗{dq2} ys ∗
                    ⌜r = true ↔ Forall2 P xs ys⌝ }})%I.

End for_all2_spec.


Section exists2_spec.

  Context `{!osirisGS Σ}.


  (** [exists2 p a b] checks if there exist corresponding elements of [a]
      and [b] that satisfy [p]. Raises if the arrays have different lengths. *)
  Definition exists2_spec : val → array → array → microvx → iProp Σ :=
    λ p a b m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A) (_ : Inhabited B)
         dq1 dq2 (xs : list A) (ys : list B) (P : A → B → Prop) (_ : ∀ x y, Decision (P x y)),
         ⌜length xs = length ys⌝ -∗
         a ↦∗{dq1} xs -∗
         b ↦∗{dq2} ys -∗
         □ iSpec τ[A; B] p (λ (x : A) (y : B) m,
                              EWP m {{ (r : bool), ⌜r = bool_decide (P x y)⌝ }}) -∗
         EWP m {{ (r : bool),
                    a ↦∗{dq1} xs ∗
                    b ↦∗{dq2} ys ∗
                    ⌜r = true ↔ Exists (λ p, P p.1 p.2) (zip xs ys)⌝ }})%I.

End exists2_spec.


(* TODO: mem and memq use stdlib compare / physical equality,
   which are not yet modeled. *)


Section find_opt_spec.

  Context `{!osirisGS Σ}.


  (** [find_opt p a] returns the first element of [a] that satisfies [p],
      or [None] if no such element exists. *)
  Definition find_opt_spec : val → array → microvx → iProp Σ :=
    λ p a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq (xs : list A) (P : A → Prop) (_ : ∀ x, Decision (P x)),
         a ↦∗{dq} xs -∗
         □ iSpec τ[A] p (λ (x : A) m,
                           EWP m {{ (b : bool), ⌜b = bool_decide (P x)⌝ }}) -∗
         EWP m {{ (r : option A),
                    a ↦∗{dq} xs ∗
                    match r with
                    | Some x => ⌜x ∈ xs ∧ P x⌝
                    | None => ⌜Forall (λ x, ¬ P x) xs⌝
                    end }})%I.

End find_opt_spec.


Section find_index_spec.

  Context `{!osirisGS Σ}.


  (** [find_index p a] returns the index of the first element that
      satisfies [p], or [None]. *)
  Definition find_index_spec : val → array → microvx → iProp Σ :=
    λ p a m,
      (∀ (A : Type) (_ : Encode A) (_ : Inhabited A)
         dq (xs : list A) (P : A → Prop) (_ : ∀ x, Decision (P x)),
         a ↦∗{dq} xs -∗
         □ iSpec τ[A] p (λ (x : A) m,
                           EWP m {{ (b : bool), ⌜b = bool_decide (P x)⌝ }}) -∗
         EWP m {{ (r : option Z),
                    a ↦∗{dq} xs ∗
                    match r with
                    | Some i => ⌜0 ≤ i < length xs ∧ P (xs !!! i) ∧
                                  Forall (λ x, ¬ P x) (take i xs)⌝
                    | None => ⌜Forall (λ x, ¬ P x) xs⌝
                    end }})%I.

End find_index_spec.


Section find_map_spec.

  Context `{!osirisGS Σ}.


  (** [find_map f a] applies [f] to each element and returns the first
      [Some] result, or [None] if [f] returns [None] on all elements. *)
  Definition find_map_spec : val → array → microvx → iProp Σ :=
    λ f a m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A)
         dq (xs : list A) (g : A → option B),
         a ↦∗{dq} xs -∗
         □ iSpec τ[A] f (λ (x : A) m,
                           EWP m {{ (r : option B), ⌜r = g x⌝ }}) -∗
         EWP m {{ (r : option B),
                    a ↦∗{dq} xs ∗
                    match r with
                    | Some y => ⌜∃ x, x ∈ xs ∧ g x = Some y⌝
                    | None => ⌜Forall (λ x, g x = None) xs⌝
                    end }})%I.

End find_map_spec.


Section find_mapi_spec.

  Context `{!osirisGS Σ}.


  (** [find_mapi f a] applies [f] to the index and each element and returns
      the first [Some] result, or [None]. *)
  Definition find_mapi_spec : val → array → microvx → iProp Σ :=
    λ f a m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A)
         dq (xs : list A) (g : Z → A → option B),
         a ↦∗{dq} xs -∗
         □ iSpec τ[Z; A] f (λ (i : Z) (x : A) m,
                              ⌜0 ≤ i < length xs⌝ -∗
                              EWP m {{ (r : option B), ⌜r = g i x⌝ }}) -∗
         EWP m {{ (r : option B),
                    a ↦∗{dq} xs ∗
                    match r with
                    | Some y => ⌜∃ i, 0 ≤ i < length xs ∧ g i (xs !!! i) = Some y⌝
                    | None => ⌜∀ i, 0 ≤ i < length xs → g i (xs !!! i) = None⌝
                    end }})%I.

End find_mapi_spec.


Section split_spec.

  Context `{!osirisGS Σ}.


  (** [split x] takes an array of pairs and returns a pair of arrays. *)
  Definition split_spec : array → microvx → iProp Σ :=
    λ a m,
      (∀ (A B : Type) `(Encode A) `(Encode B) (_ : Inhabited (A * B))
         dq (ps : list (A * B)),
         a ↦∗{dq} ps -∗
         EWP m {{ ((b1, b2) : τ[array;array]),
                    a ↦∗{dq} ps ∗
                    b1 ↦∗ (fst <$> ps) ∗
                    b2 ↦∗ (snd <$> ps) }})%I.

End split_spec.


Section combine_spec.

  Context `{!osirisGS Σ}.


  (** [combine a b] takes two arrays and returns an array of pairs.
      Raises if the arrays have different lengths. *)
  Definition combine_spec : array → array → microvx → iProp Σ :=
    λ a b m,
      (∀ (A B : Type) (_ : Encode A) (_ : Encode B) (_ : Inhabited A) (_ : Inhabited B)
         dq1 dq2 (xs : list A) (ys : list B),
         ⌜length xs = length ys⌝ -∗
         a ↦∗{dq1} xs -∗
         b ↦∗{dq2} ys -∗
         EWP m {{ r,
                    a ↦∗{dq1} xs -∗
                    b ↦∗{dq2} ys -∗
                    r ↦∗ (zip xs ys) }})%I.

End combine_spec.


(* TODO: sort, stable_sort, stable_sort_sub, fast_sort. *)

(* TODO: shuffle is EUnsupported in the translation. *)

(* TODO: to_seq, to_seqi, of_rev_list, of_seq depend on Seq module. *)

Section module_proof.
  Context `{!osirisGS Σ}.

  Local Notation "'next_top:' sitem" :=
    (impure ⊤ (eval_sitems _ (sitem :: _)) ⊥ ⊥ _) (at level 20).

  Definition array_module_dom : gset var :=
    {[ "length";
        "get";
        "set";
        "unsafe_get";
        "unsafe_set";
        "make";
        "unsafe_sub";
        "append_prim";
        "concat";
        "unsafe_blit";
        "unsafe_fill";
        "create_float";
        "Floatarray";
        "init";
        "make_matrix";
        "init_matrix";
        "copy";
        "append";
        "sub";
        "fill";
        "blit";
        "iter";
        "iter2";
        "map";
        "map_inplace";
        "mapi_inplace";
        "map2";
        "iteri";
        "mapi";
        "to_list";
        "list_length";
        "of_list";
        "equal";
        "stdlib_compare";
        "compare";
        "fold_left";
        "fold_left_map";
        "fold_right";
        "fold_left2";
        "fold_right2";
        "exists";
        "for_all";
        "for_all2";
        "exists2";
        "mem";
        "memq";
        "find_opt";
        "find_index";
        "find_map";
        "find_mapi";
        "split";
        "combine";
        "Bottom";
        "sort";
        "cutoff";
        "unsafe_stable_sort_sub";
        "stable_sort_sub";
        "stable_sort";
        "fast_sort";
        "shuffle_contract_violation";
        "shuffle";
        "to_seq";
        "to_seqi";
        "of_rev_list";
        "of_seq"
    ]}.

  Definition array_module_spec : env → iProp Σ :=
    (context [
         var_spec "init" init_spec;
         var_spec "iter" iter_spec;
         var_spec "iteri" (λ iteri, □ iSpec τ[val;array] iteri iteri_spec);
         var_spec "fold_left" (λ fold_left, □ ∀ A (HencA : Encode A), iSpec τ[val;A;array] fold_left (fold_left_spec A));
         var_spec "map" map_spec;
         var_spec "map_inplace" map_inplace_spec;
         var_spec "mapi_inplace" mapi_inplace_spec
      ] array_module_dom)%I.

  Global Instance array_spec_pers η : Persistent (array_module_spec η).
  Proof. apply _. Qed.

  Lemma module_proof η :
    ⊢ EWP (eval_mexpr η __main) {{ array_module_spec }}.
  Proof.
    iApply imp_module.
    iApply imp_externals_length. iIntros (length) "#Hlength".
    iApply imp_externals_get. iIntros (get) "#Hget".
    iApply imp_externals_set. iIntros (set) "#Hset".
    iApply imp_externals_get. iIntros (safe_get) "#Hsafe_get".
    iApply imp_externals_set. iIntros (safe_set) "#Hsafe_set".
    iApply imp_externals_make. iIntros (make) "#Hmake".

    iApply (imp_sitems_module).
    { simpl_eval_mexpr.
      iApply imp_ret; first encode.
      instantiate (1 := (λ δ, ⌜δ = []⌝)%I). done. }
    iIntros (? ->).

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_init; (iFrame "#"; auto). }
    iIntros (init) "#Hinit".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (make_matrix) "Hmake_matrix".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (init_matrix) "Hinit_matrix".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (copy) "Hcopy".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (append) "Happend".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (sub) "Hsub".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (fill) "Hfill".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (blit) "Hblit".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_iter; (iFrame "#"; auto). }
    iIntros (iter) "#Hiter".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (iter2) "Hiter2".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_map; (iFrame "#"; auto). }
    iIntros (map) "#Hmap".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_map_inplace; (iFrame "#"; auto). }
    iIntros (map_inplace) "#Hmap_inplace".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_mapi_inplace; (iFrame "#"; auto). }
    iIntros (mapi_inplace) "#Hmapi_inplace".

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

    iApply (imp_sitems_letrec).
    { admit. }
    iIntros (list_length) "Hlist_length".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_list) "Hof_list".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (equal) "Hequal".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (stdlib_compare) "Hstdlib_compare".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (compare) "Hcompare".

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
    iIntros (fold_right_map) "Hfold_right_map".

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

    iApply (imp_sitems_extend).
    iIntros (bottom) "Hbottom".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (sort) "Hsort".

    iApply (imp_sitems_let (A:=Z)).
    { imp_int. }
    iIntros (?) "->".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (unstable_sort) "Hunstable_sort".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (stable_sort_sub) "Hstable_sort_sub".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (stable_sort) "Hstable_sort".

    iApply (imp_sitems_let (A:=val)).
    { iApply imp_EPath; first auto. admit. }
    iIntros (fast_sort) "Hfast_sort".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (shuffle_contract_violation) "Hshuffle_contract_violation".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (shuffle) "Hshuffle".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_seq) "Hto_seq".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (to_seqi) "Hto_seqi".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_rev_list) "Hof_rev_list".

    iApply (imp_sitems_let (A:=val)).
    { admit. }
    iIntros (of_seq) "Hof_seq".

    iApply imp_sitems_nil.
    iFrame "#". simpl. auto.

  Admitted.

End module_proof.
