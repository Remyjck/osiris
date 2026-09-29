From Stdlib Require Import Program.Equality.
From iris.base_logic.lib Require Import fancy_updates gen_heap.
From iris.proofmode Require Import proofmode.

From iris.base_logic.lib Require Import own.

From osiris.utils Require Import base big_opLZ.
From osiris.lang Require Import lang.
From osiris.semantics Require Import semantics.

Require Import subjective_step ewp tactics basic_rules escrows.
Require Import osiris_utils.
Require Import impure_rules micro_rules.
Import ewp_rules_tactics.
Definition is_Ret {A X} (m : micro A X) := ∃ a, m = ret a.
Lemma is_Ret_Throw {A X} (e : X) : ¬ is_Ret (@Throw A X e).
Proof. intros (a & H). discriminate H. Qed.
Lemma is_Ret_Crash {A X} : ¬ is_Ret (@Crash A X).
Proof. intros (a & H). discriminate H. Qed.
Lemma is_Ret_Handle {A X} m k : ¬ is_Ret (@Handle A X m k).
Proof. intros (a & H). discriminate H. Qed.
Lemma is_Ret_Stop {A E X Y E'} c x k : ¬ is_Ret (@Stop A E X Y E' c x k).
Proof. intros (a & H). discriminate H. Qed.
Lemma is_Ret_Par {A E A1 A2 E'} m1 m2 k : ¬ is_Ret (@Par A E A1 A2 E' m1 m2 k).
Proof. intros (a & H). discriminate H. Qed.
Definition is_Ret_proj {A X} (m : micro A X) :=
  match m as mx0 return (is_Ret mx0 → A) with
  | Ret x => λ _ : is_Ret (ret x), x
  | Throw e => False_rect A ∘ (is_Ret_Throw e)
  | Crash => False_rect A ∘ is_Ret_Crash
  | Handle m k => False_rect A ∘ (is_Ret_Handle m k)
  | Stop c x k => False_rect A ∘ (is_Ret_Stop c x k)
  | Par m1 m2 k => False_rect A ∘ (is_Ret_Par m1 m2 k)
  end.
(* ------------------------------------------------------------------------ *)
(** This file contains [EWP] rules for [Stop] system calls, concurrency primitives, and loop combinators. *)
Section imp_stop.
  Context `{!osirisGS Σ}.
  Context {A X : Type} `{Hobs : Observe Encoded A}.
  Context {Bx : Type} `{HobsB : Observe Bx X}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : Bx → iProp Σ} {Φ : Encoded → iProp Σ}.
  Implicit Type m : micro A X.
  (* ------------------------------------------------------------------------ *)
  (* [CFlip]. *)
  (* Non-deterministic choose: note the use of non-separating conjunction *)
  Lemma imp_stop_flip u (k: _ → micro A X) :
    ▷(EWP continue k true @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }} ∧ EWP continue k false @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }})
    ⊢ EWP (Stop CFlip u k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    ewp_unfold_head.
    intro_state.
    ewp_mask_intro "Hmod".
    construct_wp_nonret; destruct_subjective_step; cbn; iMod "Hmod" as "_"; cbn;
      ewp_mask_intro "Hmod"; ewp_mask_elim; iFrame.
    destruct b.
    { iApply (bi.and_elim_l with "H"). }
    { iApply (bi.and_elim_r with "H"). }
  Qed.
  (* ------------------------------------------------------------------------ *)
  (* [CAlloc]. *)
  Lemma imp_stop_alloc' v (k : _ → micro A X) :
    ▷ (∀ (l : loc),
          (l ↦ₗ v ∗ meta_token l ⊤) -∗
          EWP (continue k l) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ⊢
    EWP (Stop CAlloc v k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    ewp_unfold_head; intro_state. ewp_mask_intro "Hmod".
    construct_wp_nonret.
    destruct_subjective_step.
    iMod (osiris_state_alloc σ l (Val v) H with "Hsi") as "(Hsi & Hl & Hmeta & _)".
    iIntros "!> !>". iSpecialize ("H" with "[$Hl $Hmeta]").
    ewp_mask_elim. iFrame.
  Qed.
  Lemma imp_stop_alloc v (k : _ → micro A X) :
    ▷ (∀ (l : loc), l ↦ₗ v -∗
            EWP (continue k l) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ⊢
    EWP (Stop CAlloc v k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    iApply imp_stop_alloc'.
    iIntros "!>" (l) "(Hpts & _)".
    iApply ("H" with "Hpts").
  Qed.
  (* [CAllocBlock]. *)
  Lemma imp_stop_alloc_block t ls (k : _ → micro A X) :
    ⌜list_z.length ls ≤ max_array_length⌝ -∗
    ▷ (∀ (l : loc),
         blockTag l (DfracOwn 1) t -∗
         blockLocs l ls -∗
         EWP (continue k l) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP (Stop CAllocBlock (t, ls) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "%Hbound H".
    ewp_unfold_head; intro_state. ewp_mask_intro "Hmod".
    construct_wp_nonret.

    destruct_subjective_step. subst.

    iMod (osiris_state_alloc σ l (Block t ls) H with "Hsi") as "(Hsi & Hl & _ & Hfrag)".
    iIntros "!> !>".
    iSpecialize ("H" with "[Hl] [Hfrag]").
    { iFrame "Hl". }
    { iFrame "Hfrag". iPureIntro. done. }
    ewp_mask_elim. iFrame.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [CLoad]. *)
  Lemma imp_stop_load l v (dq : dfrac) (k: _ → micro A X) :
    ▷ l ↦ₗ{dq} v ⊢
    ▷ (
        l ↦ₗ{dq} v -∗
        EWP (continue k v) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
      ) -∗
    EWP (Stop CLoad l k) @ E <|Ψ|>  ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.
    iIntros "!> !>".

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (osiris_state_valid with "Hsi Hl") as "%".
    (* Thus, the reduction step must be a successful step. *)
    destruct_subjective_step.

    rewrite /step_load_2 H0.
    ewp_mask_elim. iFrame.
    iApply ("Hwp" with "Hl").
  Qed.

  (* [CLoadBlock]. *)
  Lemma imp_stop_load_block (l : loc) t ls (dq : dfrac) (k: _ → micro A X) :
    ▷ pointsto l dq (Block t ls) ⊢
    ▷ (
        pointsto l dq (Block t ls) -∗
        EWP (continue k (t, ls)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
      ) -∗
    EWP (Stop CLoadBlock l k) @ E <|Ψ|>  ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.
    iIntros "!> !>".

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (osiris_state_valid with "Hsi Hl") as "%H0".
    (* Thus, the reduction step must be a successful step. *)
    destruct_subjective_step.

    rewrite /step_load_block_2 H0.
    ewp_mask_elim. iFrame.
    iApply ("Hwp" with "Hl").
  Qed.

  (* [CLoadBlock] via ghost map: use the persistent [blockLocs] to justify the step.
     This avoids requiring physical block ownership for read-only array operations. *)
  Lemma imp_stop_load_block_ghost (l : loc) ls (k: _ → micro A X) :
    ▷ blockLocs l ls -∗
    ▷ (∀ t,
        EWP (continue k (t, ls)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP (Stop CLoadBlock l k) @ E <|Ψ|>  ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "#(Hfrag & _) Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.
    iIntros "!> !>".
    (* Use the ghost map and coherence to determine the physical heap contents. *)
    iDestruct (osiris_state_valid_block with "Hsi Hfrag") as "(%t & %Hσl)".
    (* Thus the reduction step must succeed. *)
    destruct_subjective_step.
    rewrite /step_load_block_2 Hσl.
    ewp_mask_elim. iFrame.
    iApply ("Hwp" $! t).
  Qed.
  (* ------------------------------------------------------------------------ *)
  (* [CExchange]. *)
  Lemma imp_stop_exchange l v v' (k : _ → micro A X) :
    ▷ l ↦ₗ v ⊢
    ▷ (
        l ↦ₗ v' -∗
        EWP (continue k v) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
      ) -∗
    EWP (Stop CExchange (l, v') k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.
    (* Argue that [l] must be in the domain of the ghost heap. *)
    iIntros "!> !>".
    iDestruct (osiris_state_valid with "Hsi Hl") as "%H0".
    destruct_subjective_step.
    iMod (osiris_state_update (Val v') with "Hsi Hl") as "[Hsi Hl]".
    { intros; discriminate. }
    rewrite /step_exchange_1 /step_exchange_2 H0.
    ewp_mask_elim. iFrame.
    iApply ("Hwp" with "Hl").
  Qed.
  (* ------------------------------------------------------------------------ *)
  (* [CSetBlockTag]. *)
  Lemma imp_stop_set_tag l t t' (k : _ → micro A X) :
    ▷ (blockTag l (DfracOwn 1) t) ⊢
    ▷ (
        (blockTag l (DfracOwn 1) t') -∗
        EWP (continue k ()) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
      ) -∗
    EWP (Stop CSetBlockTag (l, t') k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.
    (* Argue that [l] must be in the domain of the ghost heap. *)
    iIntros "!> !>".
    iDestruct "Hl" as "(%ls & Hl)".
    iDestruct (osiris_state_valid with "Hsi Hl") as "%H0".
    destruct_subjective_step.
    iMod (osiris_state_set_tag with "Hsi Hl") as "[Hsi Hl]".
    rewrite /step_set_tag_1 /step_set_tag_2 H0.
    ewp_mask_elim. iFrame.
    iDestruct ("Hwp" with "[$]") as "$".
  Qed.
  (* ------------------------------------------------------------------------ *)
  (* [CCAS]. *)
  Class PhysEqDec A `{Encode A} : Prop :=
    phys_eq_dec :
      ∀ (a b : A), is_Ret (phys_eq_val #a #b).
  Global Instance phys_eq_dec_loc : PhysEqDec loc.
  Proof.
    intros i j. simpl. eexists; eauto.
  Qed.
  Global Instance phys_eq_dec_bool : PhysEqDec bool.
  Proof.
    intros [|] [|]; simpl; eexists; eauto.
  Qed.
  Definition phys_eq_val_ `{Hped : PhysEqDec B} : B → B → bool :=
    λ a b,
      @is_Ret_proj bool exn (phys_eq_val #a #b) (Hped a b).

  Lemma phys_eq_val_proj `{Hped : PhysEqDec B} a b :
    phys_eq_val #a #b = ret (phys_eq_val_ a b).
  Proof.
    unfold phys_eq_val_. destruct Hped as [decision ->].
    reflexivity.
  Qed.
  Lemma phys_eq_val__store `{Hped : PhysEqDec B} a b :
    ∀ σ, phys_eq_val_store #a #b σ = Some (phys_eq_val_ a b).
  Proof.
    intros σ.
    pose proof (phys_eq_val_proj a b) as Hproj.
    unfold phys_eq_val in Hproj.
    unfold phys_eq_val_store.
    destruct (#a); try discriminate Hproj.
    (* VData case *)
    { destruct v; try (cbn in Hproj; discriminate Hproj).
      destruct (#b); try (cbn in Hproj; discriminate Hproj).
      destruct v; try (cbn in Hproj; discriminate Hproj).
      cbn in Hproj. injection Hproj as <-. reflexivity. }
    (* VFieldLoc case *)
    { destruct (#b); try (cbn in Hproj; discriminate Hproj).
      cbn in Hproj. injection Hproj as <-. reflexivity. }
    (* VRecord case: par creates Par constructor, which is never ret *)
    { destruct (#b); try (cbn in Hproj; discriminate Hproj). }
    (* VTaggedRecord case: par creates Par constructor, which is never ret *)
    { destruct (#b); try (cbn in Hproj; discriminate Hproj). }
    (* VArray case: par creates Par constructor, which is never ret *)
    { destruct (#b); try (cbn in Hproj; discriminate Hproj). }
  Qed.

  (* CAS success: the physical equality holds, so the store is updated from
     [seen] to [v'], and the continuation receives [VTrue]. *)
  Lemma imp_stop_cas `{PhysEqDec B} l (seen v v' : B) (k : _ → micro A X) :
    ▷ l ↦ₗ #v ⊢
    ▷ (
          l ↦ₗ (if phys_eq_val_ v seen then #v' else #v) -∗
          EWP (continue k #(phys_eq_val_ v seen)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
      ) -∗
    EWP (Stop CCAS (l, #seen, #v') k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.
    iIntros "!> !>".
    iDestruct (osiris_state_valid with "Hsi Hl") as "%Hvalid".
    destruct_subjective_step.
    destruct (phys_eq_val_ v seen) eqn:Hpeq.
    - iMod (osiris_state_update (Val #v') with "Hsi Hl") as "[Hsi Hl]".
      { intros; discriminate. }
      rewrite /step_cas_1 /step_cas_2 Hvalid (phys_eq_val__store v seen σ.(st_heap)) Hpeq /=.
      ewp_mask_elim. iFrame.
      iDestruct ("Hwp" with "Hl") as "$".
    - rewrite /step_cas_1 /step_cas_2 Hvalid (phys_eq_val__store v seen σ.(st_heap)) Hpeq /=.
      ewp_mask_elim. iFrame.
      iApply ("Hwp" with "Hl").
  Qed.

  (* CAS on inline-record values ([VTaggedRecord]): physical equality compares the
     underlying block locations, provided at least one of the two blocks is
     mutable. [PhysEqDec] is not applicable here, because deciding physical
     equality of blocks requires consulting the store. Instead, we require
     (fractions of) the [blockTag] predicates of both blocks, with the block
     of [seen] mutable; these resolve the comparison. *)
  Lemma imp_stop_cas_inline l (c cs : data) (r rs : record) (v' : val)
      dq1 dq2 t (k : _ → micro A X) :
    ▷ l ↦ₗ VTaggedRecord c r -∗
    ▷ blockTag r dq1 t -∗
    ▷ blockTag rs dq2 Mut -∗
    ▷ (
        l ↦ₗ (if locations.eqb r rs then v' else VTaggedRecord c r) -∗
        blockTag r dq1 t -∗
        blockTag rs dq2 Mut -∗
        EWP (continue k #(locations.eqb r rs)) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
      ) -∗
    EWP (Stop CCAS (l, VTaggedRecord cs rs, v') k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hr Hrs Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.
    iIntros "!> !>".
    iDestruct (osiris_state_valid with "Hsi Hl") as "%Hvalid".
    iDestruct "Hr" as (ls1) "Hr".
    iDestruct (osiris_state_valid with "Hsi Hr") as "%Hr".
    iDestruct "Hrs" as (ls2) "Hrs".
    iDestruct (osiris_state_valid with "Hsi Hrs") as "%Hrs".
    destruct_subjective_step.
    assert (Hpeq : phys_eq_val_store (VTaggedRecord c r) (VTaggedRecord cs rs) σ.(st_heap)
                     = Some (locations.eqb r rs)).
    { rewrite /phys_eq_val_store Hr Hrs. by destruct t. }
    rewrite /step_cas_1 /step_cas_2 Hvalid Hpeq.
    destruct (locations.eqb r rs) eqn:Heqb.
    - iMod (osiris_state_update (Val v') with "Hsi Hl") as "[Hsi Hl]".
      { intros; discriminate. }
      ewp_mask_elim. iFrame.
      iApply ("Hwp" with "Hl [Hr] [Hrs]"); iExists _; iFrame.
    - ewp_mask_elim. iFrame.
      iApply ("Hwp" with "Hl [Hr] [Hrs]"); iExists _; iFrame.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [CFAA]. *)
  Lemma imp_stop_faa l (i j : int) (k : _ → micro A X) :
    ▷ l ↦ₗ #j ⊢
    ▷ (
        l ↦ₗ #(int.add j i) -∗
        EWP (continue k #j) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}
      ) -∗
    EWP (Stop CFAA (l, i) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.
    iIntros "!> !>".
    iDestruct (osiris_state_valid with "Hsi Hl") as "%Hvalid".
    destruct_subjective_step.
    iMod (osiris_state_update (Val #(int.add j i)) with "Hsi Hl") as "[Hsi Hl]".
    { intros; discriminate. }
    rewrite /step_faa_1 /step_faa_2 Hvalid /=.
    ewp_mask_elim. iFrame.
    iDestruct ("Hwp" with "Hl") as "$".
  Qed.
  (* ------------------------------------------------------------------------ *)
  (* [CPerform]. *)
  Lemma imp_stop_perform (v : val) (k : _ → micro A X) :
    Ψ allows perform v << λ o, ▷ impure E (k o) Ψ ζ Φ >> -∗
    EWP (Stop CPerf v k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hallows".
    ewp_unfold (Stop CPerf v k).
    iApply ("Hallows").
  Qed.
  (* ------------------------------------------------------------------------ *)
  (* [CResume] *)
  (* Resuming a continuation from a location in the store. *)
  Lemma imp_stop_resume l o sk (k: _ → micro A X) :
    isCont l sk ⊢
    (isShot l -∗ ▷ EWP (try2 (sk o) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP (Stop CResume (l, o) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (osiris_state_valid with "Hsi Hl") as "%H0".
    (* Thus, the reduction step must be a successful step. *)
    destruct_subjective_step.

    (* Update the ghost heap. *)
    iMod (osiris_state_update Shot with "Hsi Hl") as "[Hsi Hl]".
    { intros; discriminate. }
    iSpecialize ("Hwp" with "Hl").
    ewp_mask_elim.
    rewrite /step_resume_1 /step_resume_2 H0. iFrame.
  Qed.

  Lemma imp_stop_resume_crash l o (k: _ → micro A X) :
    isShot l -∗
    EWP (crash "resume error: unbound location") @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    EWP (Stop CResume (l, o) k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hcrash".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.

    (* Argue that [l] must be in the domain of the ghost heap. *)
    iDestruct (osiris_state_valid with "Hsi Hl") as "%".
    (* Thus, the reduction step must be a successful step. *)
    destruct_subjective_step.

    (* Update the ghost heap. *)
    ewp_mask_elim.
    rewrite /step_resume_1 /step_resume_2 H0. by iFrame.
  Qed.
  (* ------------------------------------------------------------------------ *)
  (* [CWrap] *)
  (* Installing a handler with branches [bs] on top of a continuation
     that is located in the store at location [l]. *)
  Lemma imp_stop_wrap_deep l η bs (k: _ -> micro A X) :
    (∀ l',
      isCont l'
        (λ o, Handle (stop CResume (l, o)) (wrap_eval_branches η bs)) -∗
     ▷ EWP (continue k l') @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP (Stop CWrap (true, l, η, bs) k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.
    (* The reduction step must be a successful step. *)
    destruct_subjective_step.
    (* Allocate a new location in the heap. *)
    iMod (osiris_state_alloc σ l' (Kont _) H with "Hsi") as "(Hsi & Hl' & _)".
    iSpecialize ("Hwp" with "Hl'").
    ewp_mask_elim. iFrame.
  Qed.
  Lemma imp_stop_wrap_shallow l η bs (k: _ -> micro A X) :
    (∀ l',
      isCont l'
        (λ o, Handle (stop CResume (l, o)) (shallow_eval_branches η bs bs)) -∗
     ▷ EWP (continue k l') @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP (Stop CWrap (false, l, η, bs) k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hwp".
    ewp_unfold_head; intro_state; ewp_mask_intro "Hmod".
    construct_wp_nonret.
    (* The reduction step must be a successful step. *)
    destruct_subjective_step.
    (* Allocate a new location in the heap. *)
    iMod (osiris_state_alloc σ l' (Kont _) H with "Hsi") as "(Hsi & Hl' & _)".
    iSpecialize ("Hwp" with "Hl'").
    ewp_mask_elim.
    unfold step_wrap_2.
    iFrame.
  Qed.

End imp_stop.

Section imp_stop_concurrent.
  Context `{!osirisGS Σ}.

  Context {A X : Type} `{Hobs : Observe Encoded A}.
  Context {Bx : Type} `{HobsB : Observe Bx X}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : Bx → iProp Σ} {Φ : Encoded → iProp Σ}.

  Implicit Type m : micro A X.
  (* When forking a thread, we must prove that the forked thread is
     safe, and that the parent thread is safe.
     We learn that the forked thread has an address ι' and is initially alive *)
  Definition isThread `{Observe B val} `{Observe Bμ exn}
    (ι : thread) (ζ : Bμ → iProp Σ) (Φ : B → iProp Σ) : iProp Σ :=
    valid_thread ι (ilift (ireturns ζ) (ireturns Φ)).

  (* [joinable ι φ] allows one to join on [ι] and to recover the non-necessarily
     persistent postcondition [φ] (after opening and closing an invariant) *)
  Definition joinN := nroot .@ "join".
  (* We need the implicit [Encode] to be outside of the existential,
     so that we know the return type when we join thread [ι]. *)
  Definition joinable B `{Observe B val} ι φ :=
    (∃ Bμ (HencBμ : Encode Bμ) (ζ : Bμ → iProp Σ) (Φ : B → iProp Σ),
        isThread ι ζ Φ ∗
        ∀ o, ilift (ireturns ζ) (ireturns Φ) o ={↑joinN}=∗ ▷ φ)%I.
  (* ------------------------------------------------------------------------ *)
  (* [CFork]. *)
  Lemma imp_stop_fork' `{Encode B} `{HencBμ : Encode Bμ}
    (μ : Bμ → iProp Σ) (φ : B → iProp Σ) v1 v2 (k : _ -> micro A X) :
    ▷ (∀ ι',
         isThread ι' μ φ -∗
         EWP call v1 v2 ⟨⟨ e, □ μ e ⟩⟩ {{ v, □ φ v }} ∗
         EWP (continue k (VThread ι')) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP (Stop CFork (v1, v2) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hfork".
    ewp_unfold_head. intro_state.
    ewp_mask_intro "Hmod".
    construct_wp_nonret.
    destruct_subjective_step.
    iMod (thread_alloc π ι _ (not_elem_of_dom_1 _ _ H0) with "Hti")
      as "(Hti & #Hvalid)".
    ewp_mask_elim.
    iDestruct ("Hfork" with "Hvalid") as "[Hcall Hcontinue]".
    iFrame "#∗".
    iApply (ewp_mono with "Hcall").
    iIntros ([|]) "/="; iIntros "(%a' & -> & #Hφ)"; iModIntro;
      iExists a'; iSplit; done.
  Qed.

  (* We do not expect that the forked thread needs to know its own postcondition. *)
  Lemma imp_stop_fork `{Encode B} `{HencBμ : Encode Bμ}
    (μ : Bμ → iProp Σ) (φ : B → iProp Σ) v1 v2 (k : _ -> micro A X) :
    ▷ (∀ ι', isThread ι' μ φ -∗ EWP (continue k (VThread ι')) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    ▷ (EWP call v1 v2 ⟨⟨ e, □ μ e ⟩⟩ {{ v, □ φ v }}) -∗
    EWP (Stop CFork (v1, v2) k) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hcontinue Hfork".
    iApply (imp_stop_fork' (B:=B) (Bμ:=Bμ)).
    iIntros "!> %ι' #Hvalid".
    iSplitL "Hfork".
    - iApply "Hfork".
    - iApply ("Hcontinue" with "Hvalid").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [CJoin]. *)
  Lemma imp_stop_join `{Observe B val} `{HencBμ : Encode Bμ}
    ι' (k : _ -> micro A X) (φ : B → iProp Σ) (μ : Bμ → iProp Σ) :
    isThread ι' μ φ -∗
    ▷ (∀ x, □ φ x -∗ EWP continue k ♯x @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) ∧
    ▷ (∀ b, □ μ b -∗ EWP discontinue k ♯b @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP (Stop CJoin ι' k) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hι Hk".
    ewp_unfold_head. intro_state_join.
    ewp_mask_intro "Hmod".
    iPoseProof (valid_thread_lookup with "Hti Hι") as "(Hti & %Q & %Hlookup & #Hagree)".
    assert (ι' ∈ dom π) as Hdom by (apply (elem_of_dom π ι'); eexists; eassumption).
    rewrite Hlookup.
    iFrame.
    iIntros "!> %o #Ho".
    (* The pool stores [Q]; [isThread] names the same predicate, but only up
       to a step-indexed equality. We are under the [▷], so we may use it. *)
    iRewrite ("Hagree" $! o) in "Ho".
    ewp_mask_elim. rewrite /continue /discontinue.
    destruct o; [ iDestruct "Hk" as "[Hk _]" | iDestruct "Hk" as "[_ Hk]" ];
      iDestruct "Ho" as "(%v & -> & Hφ)"; iApply ("Hk" $! v with "Hφ").
  Qed.

End imp_stop_concurrent.

Section imp_combinators.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ}.

  (* ------------------------------------------------------------------------ *)
  (* [CEval]. *)
  Lemma imp_please `{Observe A val} {Φ : A → iProp Σ} η e :
    ▷ EWP eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    EWP please_eval η e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Himp".
    rewrite /please_eval.
    ewp_unfold_head.
    intro_state. ewp_mask_intro "Hclose".
    construct_wp_nonret. subjective_step.destruct_subjective_step.
    iModIntro. ewp_mask_elim.
    rewrite try2_inject2_right. by iFrame.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [CLoop]. *)
  Lemma imp_empty_loop (R : iProp Σ) i j e x η :
    int.representable i →
    int.representable j →
    ⌜(j < i)%Z⌝ -∗
    R -∗
    EWP code.loop x η (int.repr i) (int.repr j) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (_ : unit), R }}.
  Proof.
    iIntros (Hrepr1 Hrepr2 Hbounds) "HR".
    rewrite /impure /=.
    ewp_unfold_head.
    intro_state. ewp_mask_intro "Hmod". rewrite /code.loop.
    construct_wp_nonret. subjective_step.destruct_subjective_step.
    ewp_mask_elim. iFrame.
    rewrite try2_inject2_right.
    rewrite /E.loop.
    rewrite int.lt_repr_repr; try assumption.
    rewrite int.eq_repr_repr; try assumption.
    assert ((i =? j) = false)%Z as -> by lia.
    assert ((j <? i) = true)%Z as -> by lia.
    iApply (imp_ret VUnit ()); [ encode | auto ].
  Qed.

  Lemma imp_nonempty_loop (I : Z → iProp Σ) i j e x η :
    int.representable i →
    int.representable j →
    ⌜(i ≤ j)%Z⌝ -∗
    I i -∗
    □ (∀ i',
         ⌜(i ≤ i' ≤ j)%Z⌝ -∗
         I i' -∗
         EWP (eval ((x, #i') :: η) e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (_ : unit), I (i' + 1)%Z }}) -∗
    EWP code.loop η x (int.repr i) (int.repr j) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (_ : unit), I (j + 1)%Z }}.
  Proof.
    iIntros (Hrepr1 Hrepr2 Hbounds) "HR #He".
    iLöb as "IH" forall (i j Hrepr1 Hrepr2 Hbounds) "He".
    rewrite /impure.
    ewp_unfold_head.
    intro_state. ewp_mask_intro "Hmod". rewrite /code.loop.
    construct_wp_nonret. subjective_step.destruct_subjective_step.
    ewp_mask_elim. iFrame.
    rewrite try2_inject2_right.
    rewrite /E.loop.
    assert (int.lt (int.repr j) (int.repr i) = false) as ->.
    { rewrite int.lt_repr_repr; first lia; assumption. }
    iPoseProof ("He" $! i with "[] HR") as "Heapp". iPureIntro; lia.
    rewrite int.eq_repr_repr; try assumption.
    case (decide (i = j)%Z); intros Heq.
    - assert ((i =? j) = true)%Z as -> by lia.
      iApply ewp_bind.
      iApply (ewp_mono with "Heapp").
      iIntros ([|]) "Ho".
      + iDestruct "Ho" as "(% & %Henc & HR)".
        iApply (imp_ret VUnit ()); first encode.
        rewrite Heq. iApply "HR".
      + done.
    - assert ((i =? j) = false)%Z as -> by lia.
      iApply ewp_bind.
      iApply (ewp_wand with "Heapp").
      iIntros ([|]) "Ho".
      + iDestruct "Ho" as "(% & %Henc & HR)".
        iSpecialize ("IH" $! (i + 1)%Z j).
        iSpecialize ("IH" with "[] [] [] HR").
        { iPureIntro.
          rewrite /int.representable in Hrepr1 Hrepr2 |- *.
          lia. }
        { iPureIntro; assumption. }
        { iPureIntro; lia. }
        replace (int.add (int.repr i) (int.one)) with (int.repr (i + 1)).
        iApply "IH".
        iIntros "!>" (?) "%Hbounds' HR".
        iApply ("He" with "[] HR").
        iPureIntro. lia.
        by rewrite int.add_repr_repr.
      + done.
  Qed.

  Lemma imp_loop (I : Z → iProp Σ) i j e x η :
    int.representable i →
    int.representable j →
    I i -∗
    □ (∀ i',
         ⌜(i ≤ i' ≤ j)%Z⌝ -∗
         I i' -∗
         EWP (eval ((x, #i') :: η) e) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (_ : unit), I (i' + 1)%Z }}) -∗
    EWP code.loop η x (int.repr i) (int.repr j) e @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ (_ : unit), I ((j + 1) `max` i)%Z }}.
  Proof.
    iIntros (Hrepr1 Hrepr2) "HI #He".
    case (decide (j < i)%Z); intros Hlt.
    - iApply imp_empty_loop; try assumption.
      iPureIntro; assumption.
      replace ((j + 1) `max` i)%Z with i by lia.
      iAssumption.
    - replace ((j + 1) `max` i)%Z with (j + 1)%Z by lia.
      iApply (imp_nonempty_loop with "[] HI He"); try assumption.
      iPureIntro; lia.
  Qed.

  (* [CFlip]. *)
  (* Non-deterministic choose: note the use of non-separating conjunction *)
  Lemma imp_flip {Φ : bool → iProp Σ} :
      ▷( Φ true ∧ Φ false)
      ⊢ EWP code.flip @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    iApply imp_stop_flip. iNext.
    iSplit.
    - iDestruct "H" as "[H _]".
      iApply (imp_ret _ true eq_refl). iFrame.
    - iDestruct "H" as "[_ H]".
      iApply (imp_ret _ false eq_refl). iFrame.
  Qed.

  Lemma imp_choose {V : Type} `{Observe A V} {Φ : A → iProp Σ} (m1 m2 : micro V exn) :
    EWP m1 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} ∧ EWP m2 @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }} -∗
    EWP (code.choose m1 m2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hm". rewrite /code.choose.
    iApply (imp_bind (λ (b : bool), True)%I).
    { iApply imp_flip. auto. }
    iIntros ([|] _) "/=".
    - iDestruct "Hm" as "[$ _]".
    - iDestruct "Hm" as "[_ $]".
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [CAlloc]. *)
  Lemma imp_alloc2' {Φ : loc → iProp Σ} v :
    ▷ (∀ (l : loc), l ↦ₗ v ∗ meta_token l ⊤ -∗ Φ l) -∗
    EWP (alloc v) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    iApply imp_stop_alloc'.
    iIntros "!> %l Hl".
    iApply imp_ret; first encode.
    iApply ("H" with "Hl").
  Qed.

  Lemma imp_alloc2 {Φ : loc → iProp Σ} v :
    ▷ (∀ (l : loc), l ↦ₗ v -∗ Φ l) -∗
    EWP (alloc v) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    iApply imp_alloc2'.
    iIntros "!> %l (Hl & _)".
    iApply ("H" with "Hl").
  Qed.

  Lemma imp_alloc' v :
    ⊢ EWP (alloc v) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l, l ↦ₗ v ∗ meta_token l ⊤ }}.
  Proof.
    iApply (imp_alloc2').
    iIntros "!> %l $".
  Qed.

  Lemma imp_alloc v :
    ⊢ EWP (alloc v) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ l, l ↦ₗ v }}.
  Proof.
    iApply imp_alloc2.
    iIntros "!> %l $".
  Qed.

  Local Instance notval_locs : NotVal (list loc) := {}.

  (* Memory allocation rule for [n] locations at once. *)
  Lemma imp_allocn' `{Encode A} {Φ : list loc → iProp Σ} (xs : list A) :
    (▷^(List.length xs) ∀ (ls : list loc),
       ([∗ listZ] l;x ∈ ls;xs, l ↦ₗ #x ∗ meta_token l ⊤) -∗
       Φ ls) ⊢
    EWP (allocn ♯xs) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    iInduction xs as [|x xs] forall (Φ).
    - iApply imp_ret. reflexivity.
      iApply "H".
      by iApply (big_sepLZ2_nil).
    - simpl.
      iApply (imp_bind (A1:=loc) with "[H]").
      { set_postcondition (λ l, (l ↦ₗ #x ∗ meta_token l ⊤) ∗ (▷^_ _))%I.
        iApply imp_alloc2'. iNext. iIntros (l) "$".
        iExact "H". }
      iIntros (l) "(Hl & H)".
      iApply (imp_bind (A1:=list loc) with "[H]").
      {
        iApply "IHxs".
        iNext.
        iIntros (ls) "Hls".
        iCombine "H Hls" as "H".
        iExact "H". }
      iIntros (ls) "(H & Hls)".
      iApply imp_ret. encode.
      iApply "H".
      iApply big_sepLZ2_cons. iFrame.
  Qed.
  Lemma imp_allocn `{Encode A} {Φ : list loc → iProp Σ} (xs : list A) :
    ▷^(List.length xs) (∀ ls,
       ([∗ listZ] l;x ∈ ls;xs, l ↦ₗ #x) -∗ Φ ls) ⊢
    EWP (allocn ♯xs) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "H".
    iApply imp_allocn'.
    iIntros "!>" (ls) "Hls".
    iPoseProof (big_sepLZ2_sep with "Hls") as "[Hls _]".
    iApply "H". iFrame.
  Qed.
  (* [CAllocBlock]. *)
  Lemma imp_alloc_block2 {Φ : loc → iProp Σ} t ls :
    ⌜list_z.length ls ≤ max_array_length⌝ -∗
    ▷ (∀ (l : loc), blockTag l (DfracOwn 1) t -∗ blockLocs l ls -∗ Φ l) -∗
    impure E (alloc_block t ls) Ψ ζ Φ.
  Proof.
    iIntros "%Hbound H".
    iApply (imp_stop_alloc_block with "[%]"). assumption.
    iIntros "!>" (l) "Hl #Harr".
    iApply imp_ret; first encode.
    iApply ("H" with "Hl Harr").
  Qed.
  Lemma imp_alloc_block t ls :
    ⌜list_z.length ls ≤ max_array_length⌝ -∗
    impure E (alloc_block t ls) Ψ ζ (λ (l : loc), blockTag l (DfracOwn 1) t ∗ blockLocs l ls).
  Proof.
    iIntros "%Hbound".
    iApply (imp_alloc_block2 with "[%//]").
    iIntros "!>" (l) "$ #$".
  Qed.
  (* ------------------------------------------------------------------------ *)
  (* [CLoad]. *)
  Lemma imp_load' `{Encode A} {Φ : A → iProp Σ} l a dq :
    ▷ l ↦ₗ{dq} #a ⊢
    ▷ (l ↦ₗ{dq} #a -∗ Φ a) -∗
    EWP (load l) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply (imp_stop_load with "Hl").
    iIntros "!> Hl".
    iApply imp_ret; first encode.
    iApply ("HΦ" with "Hl").
  Qed.
  Lemma imp_load `{Encode A} l (a : A) dq :
    ▷ l ↦ₗ{dq} #a ⊢
    EWP (load l) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ a', ⌜a' = a⌝ ∗ l ↦ₗ{dq} #a }}.
  Proof.
    iIntros "Hl".
    iApply (imp_load' with "Hl").
    by iIntros "!> $".
  Qed.
  (* [CLoadBlock]. *)
  Instance notval_block : NotVal (mut_tag * list loc) := {}.
  Lemma imp_load_block' {Φ : (mut_tag * list loc) → iProp Σ} (l : loc) dq t ls :
    ▷ pointsto l dq (Block t ls) ⊢
    ▷ (pointsto l dq (Block t ls) -∗ Φ (t, ls)) -∗
    EWP (load_block l) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply (imp_stop_load_block with "Hl").
    iIntros "!> Hl".
    iApply imp_ret; first encode.
    iApply ("HΦ" with "Hl").
  Qed.
  Lemma imp_load_block (l : loc) dq t ls :
    ▷ pointsto l dq (Block t ls) ⊢
    EWP (load_block l) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (t', ls'), ⌜t' = t⌝ ∗ ⌜ls' = ls⌝ ∗ pointsto l dq (Block t ls) }}.
  Proof.
    iIntros "Hl".
    iApply (imp_load_block' with "Hl").
    by iIntros "!> $".
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [CExchange]. *)
  Lemma imp_exchange' `{Encode A} {Φ : A → iProp Σ} l a v' :
    ▷ l ↦ₗ #a ⊢
    ▷ (l ↦ₗ v' -∗ Φ a) -∗
    EWP (exchange l v') @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply (imp_stop_exchange with "Hl").
    iIntros "!> Hl".
    iApply imp_ret; first encode.
    iApply ("HΦ" with "Hl").
  Qed.
  Lemma imp_exchange `{Encode A} {Φ : A → iProp Σ} l a v' :
    ▷ l ↦ₗ #a ⊢
    EWP (exchange l v') @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (a' : A), ⌜a' = a⌝ ∗ l ↦ₗ v' }}.
  Proof.
    iIntros "Hl".
    iApply (imp_stop_exchange with "Hl").
    iIntros "!> Hl".
    iApply imp_ret; first encode.
    by iFrame.
  Qed.

  Lemma imp_store' {Φ : unit → iProp Σ} l v v' :
    ▷ l ↦ₗ v ⊢
    ▷ (l ↦ₗ v' -∗ Φ ()) -∗
    EWP (code.store l v') @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". unfold code.store.
    iApply (imp_stop_exchange with "Hl").
    iIntros "!> Hl".
    iApply imp_ret; first encode.
    iApply ("HΦ" with "Hl").
  Qed.
  Lemma imp_store l v v' :
    ▷ l ↦ₗ v ⊢
    EWP (code.store l v') @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (_ : unit), l ↦ₗ v' }}.
  Proof.
    iIntros "Hl".
    iApply (imp_store' with "Hl").
    iIntros "!> $".
  Qed.
  (* ------------------------------------------------------------------------ *)
  (* [CSetBlockTag]. *)
  Lemma imp_set_tag' {Φ : unit → iProp Σ} l t t' :
    ▷ blockTag l (DfracOwn 1) t ⊢
    ▷ (blockTag l (DfracOwn 1) t' -∗ Φ ()) -∗
    EWP (set_tag l t') @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply (imp_stop_set_tag with "Hl").
    iIntros "!> Hl".
    iApply imp_ret; first encode.
    iApply ("HΦ" with "Hl").
  Qed.
  Lemma imp_set_tag l t t' :
    ▷ blockTag l (DfracOwn 1) t ⊢
    EWP (set_tag l t') @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (_ : unit), blockTag l (DfracOwn 1) t' }}.
  Proof.
    iIntros "Hl".
    iApply (imp_set_tag' with "Hl").
    iIntros "!> $".
  Qed.
  (* ------------------------------------------------------------------------ *)
  (* [CCAS]. *)
  Lemma imp_cas `{PhysEqDec A} {Φ : bool → iProp Σ} l (seen v v' : A) :
    ▷ l ↦ₗ #v ⊢
    ▷ (l ↦ₗ (if phys_eq_val_ v seen then #v' else #v) -∗
       Φ (phys_eq_val_ v seen)) -∗
    EWP (cas l #seen #v') @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply (imp_stop_cas with "Hl").
    iIntros "!> Hl".
    iApply imp_ret; first encode.
    iApply ("HΦ" with "Hl").
  Qed.

  (* The [VTaggedRecord] variant of [imp_cas]; see [imp_stop_cas_inline]. *)
  Lemma imp_cas_inline {Φ : bool → iProp Σ} l (c cs : data) (r rs : record)
      (v' : val) dq1 dq2 t :
    ▷ l ↦ₗ VTaggedRecord c r -∗
    ▷ blockTag r dq1 t -∗
    ▷ blockTag rs dq2 Mut -∗
    ▷ (l ↦ₗ (if locations.eqb r rs then v' else VTaggedRecord c r) -∗
       blockTag r dq1 t -∗
       blockTag rs dq2 Mut -∗
       Φ (locations.eqb r rs)) -∗
    EWP (cas l (VTaggedRecord cs rs) v') @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hr Hrs HΦ".
    iApply (imp_stop_cas_inline with "Hl Hr Hrs").
    iIntros "!> Hl Hr Hrs".
    iApply imp_ret; first encode.
    iApply ("HΦ" with "Hl Hr Hrs").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [CFAA]. *)
  Lemma imp_faa {Φ : Z → iProp Σ} l (i j : Z) :
    ▷ l ↦ₗ #j ⊢
    ▷ (l ↦ₗ #(j + i) -∗ Φ j) -∗
    EWP (faa l ♯i) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply (imp_stop_faa with "Hl").
    iIntros "!> Hl".
    iApply imp_ret; first encode.
    iApply "HΦ".
    rewrite add_repr_repr.
    iApply "Hl".
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [CPerform]. *)
  Lemma imp_perform `{Encode A} {Φ : A → iProp Σ} (v : val) :
    Ψ allows perform v << (ilift (ireturns ζ) (ireturns Φ)) >> -∗
    EWP perform v @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hallows".
    iApply imp_stop_perform.
    iApply (monotonic_prot with "[] Hallows").
    iIntros (?) "H".
    iApply (ewp_outcome2 with "H").
  Qed.
  (* ------------------------------------------------------------------------ *)
  (* [CResume]. *)
  Lemma imp_resume `{Encode A} {Φ : A → iProp Σ} l o sk :
    isCont l sk ⊢
    (isShot l -∗ ▷ EWP (sk o) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}) -∗
    EWP (resume l o) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hl Hwp".
    iApply (imp_stop_resume with "Hl").
    iIntros "Hshot". rewrite try2_inject2_right.
    iApply ("Hwp" with "Hshot").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [CWrap]. *)

  Lemma imp_wrap_deep {Φ : loc → iProp Σ} l η bs :
    (∀ l',
      isCont l' (λ o, Handle (resume l o) (wrap_eval_branches η bs)) -∗
      ▷ Φ l') -∗
    EWP (wrap l η bs) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hwp".
    iApply imp_stop_wrap_deep.
    iIntros (l') "HisCont".
    iApply imp_ret; first encode.
    iApply ("Hwp" with "HisCont").
  Qed.

  Local Instance notval_outcome3 : NotVal (code.outcome3 val exn) := {}.

  Lemma imp_wrap_eval_branches `{Encode A} {Φ : A → iProp Σ} l η bs e :
    (∀ l',
       isCont l' (λ o, Handle (resume l o) (wrap_eval_branches η bs)) -∗
       ▷ impure E (eval_branches η (O3Perform e l') bs) Ψ ζ Φ) -∗
    impure E (wrap_eval_branches η bs (O3Perform e l)) Ψ ζ Φ.
  Proof.
    iIntros "Hwp".
    rewrite /wrap_eval_branches {2}seal_eq.
    iApply (imp_bind (A1:=code.outcome3 val exn) with "[Hwp]").
    { iApply (imp_bind (A1:=loc) with "[Hwp]").
      iApply imp_wrap_deep. iIntros (l') "Hcont".
      iSpecialize ("Hwp" with "Hcont").
      iExact "Hwp".
      iIntros (l') "Hwp".
      iApply imp_ret; first encode.
      instantiate (1:= (λ o, match o with
                            | O3Perform ep lp =>
                                ⌜ep = e⌝ ∗ impure E _ Ψ ζ Φ
                            | _ => False
                             end)%I).
      by iFrame. }
    iIntros ([ | | ]); try iIntros ([]).
    iIntros "(-> & $)".
  Qed.
  Lemma imp_wrap_shallow {Φ : loc → iProp Σ} l η bs :
    (∀ l',
      isCont l' (λ o, Handle (resume l o) (shallow_eval_branches η bs bs)) -∗
      ▷ Φ l') -∗
    EWP (shallow_wrap l η bs) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hwp".
    iApply imp_stop_wrap_shallow.
    iIntros (l') "HisCont".
    iApply imp_ret; first encode.
    iApply ("Hwp" with "HisCont").
  Qed.

End imp_combinators.

Section polymorphic_combinators.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ}.
  Context {X : Type} {Bx : Type} `{HobsB : Observe Bx X} {ζ : Bx → iProp Σ}.

  (* Ghost-based load_block: use [blockLocs] (persistent ghost entry) to load the block.
     Returns the tag [t] without requiring physical block ownership. *)
  Lemma imp_load_block_ghost' P (l : loc) ls :
    ▷ blockLocs l ls -∗
    ▷ P -∗
    EWP (load_block l) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ ((_, ls') : mut_tag * list loc), ⌜ls'=ls⌝ ∗ P }}.
  Proof.
    iIntros "Hblock P".
    iApply (imp_stop_load_block_ghost with "Hblock").
    iIntros "!>" (t).
    iApply imp_ret; first encode.
    iFrame. done.
  Qed.

  Lemma imp_load_block_ghost (l : loc) ls :
    ▷ blockLocs l ls -∗
    EWP (load_block l) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩
      {{ ((t', ls') : mut_tag * list loc), ⌜ls' = ls⌝ }}.
  Proof.
    iIntros "#Harr".
    iApply (imp_stop_load_block_ghost with "Harr").
    iIntros "!>" (t).
    iApply imp_ret; first encode.
    done.
  Qed.

End polymorphic_combinators.

Section imp_concurrent_combinators.

  Context `{!osirisGS Σ}.

  (* We don't provide a univesal [ζ] because we have some lemma reuse
     where the postcondition varies. *)
  Context {E : coPset} {Ψ : iEff Σ}.

  (* ------------------------------------------------------------------------ *)
  (* [CFork]. *)

  Lemma imp_fork `{HencBz : Encode Bz} {ζ : Bz → iProp Σ}
    `{Encode B} `{HencBμ : Encode Bμ} {Φ : thread → iProp Σ}
    (μ : Bμ → iProp Σ) (φ : B → iProp Σ) v1 v2 :
    ▷ (∀ ι',
         isThread ι' μ φ -∗
         EWP call v1 v2 ⟨⟨ e, □ μ e ⟩⟩ {{ o, □ φ o }} ∗
         Φ ι') -∗
    EWP (fork v1 v2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply (imp_stop_fork' (B:=B) (Bμ:=Bμ)).
    iIntros "!>" (ι') "Hvalid"; iDestruct ("HΦ" with "Hvalid") as "[Hcall HΦ]"; iFrame.
    iApply ewp_ret.
    iExists ι'. auto.
  Qed.

  (* Rule for fork when the postcondition of the spawned thread is persistent *)
  Lemma imp_fork_persistent `{HencBz : Encode Bz} {ζ : Bz → iProp Σ}
    `{Encode B} {Φ : thread → iProp Σ} φ v1 v2 :
    ▷ (∀ ι',
          □ joinable B ι' φ -∗
          EWP call v1 v2 {{ (_ : B), □ φ }} ∗
          Φ ι') -∗
    EWP (fork v1 v2) @ E <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply (imp_fork (Bμ:=exn) (⊥ : exn → iProp Σ) (λ (_ : B), φ)).
    iIntros "!> %ι' #Hvalid".
    iDestruct ("HΦ" with "[]") as "(Hcall & $)".
    { iExists exn, _, _, _. iFrame "#".
      iModIntro.
      iIntros ([|]) "/=".
      - iIntros "(%b & _ & Hφ)". iModIntro. iNext. iApply "Hφ".
      - iIntros "(%b & _ & [])". }
    iApply (ewp_mono with "Hcall").
    iIntros ([|]); [ auto | iIntros "(%b & _ & [])" ].
  Qed.

  (* Rule for fork when the postcondition of the spawned thread is a list of
  resources that other threads can recover when joining. *)
  Lemma imp_fork_resourceful `{HencBz : Encode Bz} {ζ : Bz → iProp Σ}
    `{Encode B} {Φ : thread → iProp Σ} φs v1 v2 :
    ▷ (∀ ι',
          ([∗ list] φ ∈ φs, joinable B ι' φ) -∗
          EWP call v1 v2 {{ (_ : B), [∗] φs }} ∗
          Φ ι') -∗
    EWP (fork v1 v2) @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "HΦ".

    (* Given [φs], determine a suitable postcondition [ψ] for the spawned
    thread. This requires the ghost update modality because we allocate
    tokens that will be used to transfer resources. *)
    iApply fupd_ewp. iMod (fupd_mask_subseteq ∅) as "Hmod". set_solver.
    iDestruct (alloc_escrow_list joinN φs) as "> (%φ & #Hescrow_intro & Hescrow_elim)".

    (* In the postcondition of the spawned thread we can transfer the resources
    [φs] into [ψ] by the escrow mechanism *)
    iAssert (▷ ∀ ι, ([∗ list] φ ∈ φs, joinable B ι φ) -∗
      EWP call v1 v2 {{ (_ : B), □ φ }} ∗ Φ ι)%I
      with "[HΦ]" as "HΦ".
    {
      iIntros "!>" (ι') "Hjs".
      iDestruct ("HΦ" $! ι' with "Hjs") as "(Hcall & $)".
      iPoseProof (imp_mono_pers with "Hcall []") as "$".
      iIntros "!>" (_) "φs".
      iSpecialize ("Hescrow_intro" with "[φs]").
      by rewrite -big_sepL_later.
      iApply (fupd_mask_mono ∅). set_solver.
      iExact "Hescrow_intro".
    }
    iClear "Hescrow_intro".
    iMod "Hmod".

    (* Apply the basic rule for fork, recover [valid_thread] in the post *)
    iApply (imp_fork (B:=B) (Bμ:=exn)).
    iIntros "!> !> %ι' #Hvalid".
    iDestruct ("HΦ" $! ι' with "[Hescrow_elim]") as "(Hcall & $)".

    (* From the escrow elimination implication we prove the list of [joinable φ]s *)
    iApply (big_sepL_mono_pers
              (isThread ι' (⊥ : exn → iProp Σ) (λ (_ : B), φ)) with "[$]").
    iIntros (k φ' Hk) "(#? & Helim)". iExists exn, _, ⊥, _.
    iSplit; first auto.
    iIntros ([|]).
    - iIntros "(%v & _ & Hφ)". by iApply "Helim".
    - iIntros "(%b & _ & [])".

    - iApply (ewp_mono with "Hcall").
      iIntros ([|]); [ | iIntros "(%b & _ & [])" ].
      iIntros "(%v & Henc & Hφ)".
      iFrame.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (* [CJoin]. *)

  Lemma imp_join `{HencBz : Encode Bz} {ζ : Bz → iProp Σ}
    `{Encode A} `{HencBμ : Encode Bμ} {Φ : A → iProp Σ}
    ι' (μ : Bμ → iProp Σ) φ :
    isThread ι' μ φ -∗
    ▷ (∀ x, □ φ x -∗ Φ x) ∧ ▷ (∀ b, □ μ b -∗ ireturns ζ ♯b) -∗
    EWP (code.join ι') @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "Hvalid HΦ".
    iApply (imp_stop_join ι' inject2 with "Hvalid [HΦ]").
    iSplit.
    - iIntros "!>" (x) "#Hφ". rewrite /continue /=.
      iApply (@imp_ret _ _ A val). reflexivity. iApply ("HΦ" with "Hφ").
    - iIntros "!>" (b) "#Hμ". rewrite /discontinue /=.
      iSpecialize ("HΦ" with "Hμ").
      iApply ewp_throw. iApply "HΦ".
  Qed.

  (* Does not actually need to transfer resources, [φ] could be persistent. To
     be renamed when [joinable] subsumes [valid_thread], i.e. when it can talk
     about the outcome *)
  Lemma imp_join_resourceful {ζ : exn → iProp Σ}
    `{Encode A} {Φ : A → iProp Σ} ι' φ :
    ↑joinN ⊆ E →
    joinable A ι' φ -∗
    ▷ (▷ φ -∗ (∀ x, Φ x) ∧ (∀ e : exn, ζ e)) -∗
    EWP (code.join ι') @ E <| Ψ |> ⟨⟨ ζ ⟩⟩ {{ Φ }}.
  Proof.
    iIntros "%Hmask (%Bμ & %HencBμ & %μ & %φ' & Hthread & Hcont) Hφ".
    iApply (imp_fupd E (code.join ι')).
    iApply (imp_fupd_exn E (code.join ι')).
    iApply (imp_join with "Hthread"). iSplit; iNext.
    - iIntros (x) "#Hφ'".
      iSpecialize ("Hcont" $! (O2Ret ♯x) with "[]");
        first (iExists x; iSplit; done).
      iMod (fupd_mask_subseteq (↑joinN)); first assumption.
      iMod "Hcont".
      (* TODO: There should be a more straighforward to introduce the masks. *)
      iApply fupd_wand_l. iFrame. iIntros "_".
      iDestruct ("Hφ" with "Hcont") as "[Hφ _]".
      iApply "Hφ".
    - iIntros (b) "#Hμ".
      iSpecialize ("Hcont" $! (O2Throw ♯b) with "[]");
        first (iExists b; iSplit; done).
      iExists ♯b. iSplit; first (iPureIntro; apply solve_encode_val).
      iMod (fupd_mask_subseteq (↑joinN)); first assumption.
      iMod "Hcont".
      iApply fupd_wand_l. iFrame. iIntros "_".
      iDestruct ("Hφ" with "Hcont") as "[_ Hφ]".
      iApply "Hφ".
  Qed.

End imp_concurrent_combinators.
