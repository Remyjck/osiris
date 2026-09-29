(* The block ghost map: for each allocated block (array or record), its list
   of element locations.

   An entry never changes once it is written, so no fractional ownership is
   needed. The map is an authoritative map of agreements: a fragment
   [◯ {[a := to_agree ls]}] is persistent by construction, and two fragments
   for the same block agree on its locations. *)

From iris.algebra Require Import auth gmap agree.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import locations.

Definition block_mapUR : ucmra :=
  gmapUR locations.loc (agreeR (leibnizO (list locations.loc))).

Class blockMapG (Σ : gFunctors) := {
  #[global] block_map_inG :: inG Σ (authR block_mapUR);
}.

Definition blockMapΣ : gFunctors := #[ GFunctor (authR block_mapUR) ].

Global Instance subG_blockMapΣ {Σ} : subG blockMapΣ Σ → blockMapG Σ.
Proof. solve_inG. Qed.

Section block_map.
  Context `{!blockMapG Σ}.

  Definition block_map_auth (γ : gname) (m : gmap locations.loc (list locations.loc)) : iProp Σ :=
    own γ (● ((to_agree <$> m) : block_mapUR)).

  Definition block_map_elem (γ : gname) (a : locations.loc) (ls : list locations.loc) : iProp Σ :=
    own γ (◯ ({[a := to_agree ls]} : block_mapUR)).

  Global Instance block_map_elem_persistent γ a ls : Persistent (block_map_elem γ a ls).
  Proof. apply _. Qed.

  Global Instance block_map_elem_timeless γ a ls : Timeless (block_map_elem γ a ls).
  Proof. apply _. Qed.

  (* The shape the adequacy proof allocates the map in. *)
  Lemma block_map_auth_empty γ :
    block_map_auth γ ∅ ⊣⊢ own γ (● (∅ : block_mapUR)).
  Proof. by rewrite /block_map_auth fmap_empty. Qed.

  Lemma block_map_lookup γ m a ls :
    block_map_auth γ m -∗ block_map_elem γ a ls -∗ ⌜m !! a = Some ls⌝.
  Proof.
    iIntros "Hauth Helem".
    iDestruct (own_valid_2 with "Hauth Helem") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_l in Hincl as (y & Hy & Hincl).
    rewrite lookup_fmap in Hy. apply fmap_Some_equiv in Hy as (ls' & Hls' & Hy).
    rewrite Hy in Hincl. rewrite Hls'. f_equal.
    apply Some_included in Hincl as [Heq|Heq].
    - apply (inj to_agree), leibniz_equiv in Heq. by subst.
    - apply (to_agree_included (A := leibnizO (list locations.loc))),
        leibniz_equiv in Heq.
      by subst.
  Qed.

  Lemma block_map_elem_agree γ a ls1 ls2 :
    block_map_elem γ a ls1 -∗ block_map_elem γ a ls2 -∗ ⌜ls1 = ls2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. revert Hv.
    rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid.
    by intros ?%(to_agree_op_valid_L (A := leibnizO (list locations.loc))).
  Qed.

  Lemma block_map_insert γ m a ls :
    m !! a = None →
    block_map_auth γ m ==∗ block_map_auth γ (<[a := ls]> m) ∗ block_map_elem γ a ls.
  Proof.
    iIntros (Hfresh) "Hauth".
    rewrite /block_map_auth /block_map_elem -own_op.
    iApply (own_update with "Hauth").
    rewrite fmap_insert.
    apply auth_update_alloc.
    apply (alloc_singleton_local_update
             (A := agreeR (leibnizO (list locations.loc)))); last done.
    by rewrite lookup_fmap Hfresh.
  Qed.

End block_map.
