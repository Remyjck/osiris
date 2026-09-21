From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var.
From stdpp Require Import relations.

From osiris Require Import osiris.

Require Export UnionFind08DataConc UnionFind09SameClass UnionFind10ReprPred.

Local Abbreviation elem := record.

Definition ufN : namespace := nroot .@ "concurrent_uf".

(* The abstract state of the structure, as the client sees it:
   - a domain [D],
   - a representative function [R],
   - a value function [V]. *)

Definition uf_state : Type := gset elem * (elem → elem) * (elem → val).

(* ------------------------------------------------------------------------ *)
(* The representative function [R]. *)

(* The sequential development says this by exhibiting a disjoint set forest
   [F] and asking that [R] pick out the root of each tree
   ([rel_incl R (Repr F)], see [UnionFind.v]'s [Inv]). The concurrent
   structure cannot use that formulation, and does not need it.

   It cannot, because there is no single graph to point at: path
   compression rewrites parent pointers concurrently with everything else,
   so the pointers do not form a stable forest. It does not need to,
   because we only need four properties of [R]:

   - [repr_idem]: a representative is its own representative.
   - [repr_dom] / [repr_out]: [R] maps the structure into itself, and is
     the identity on everything else.
   - [repr_id_le]: a representative's identifier is at most its own
     vertex's. This is the argument we use for acyclicity: it shows
     that the vertex a linking CAS points into cannot already be
     represented by the vertex being linked away.

   [uf_inv] pairs these with [vertex_own]. *)

Record uf_repr (M : gmap elem Z) (R : elem → elem) : Prop := {
  repr_idem : ∀ x, R (R x) = R x;
  repr_out : ∀ x, x ∉ dom M → R x = x;
  repr_dom : ∀ x, x ∈ dom M → R x ∈ dom M;
  repr_id_le : ∀ x i j, M !! x = Some i → M !! (R x) = Some j → (j ≤ i)%Z;
}.

(* ------------------------------------------------------------------------ *)
(* The abstract state transitions. *)

(* We reuse [update_class] (UnionFind00Update.v) from the sequential
   development to do updates on whole equivalence classes.
   Every transition either operation makes is an instance:

     make    [V.[x -/R/> v]]
     set     [V.[x -/R/> v]]
     union   [R.[x -/R/> R y]] and [V.[x -/R/> V y]]

   The section below collects what [update_class] preserves when it is
   used in [union]: a root [a] linked into a vertex whose
   representative is [z], with [z]'s identifier strictly below [a]'s. *)

Section link_state.

(* In the following, [a] is a root about to be linked away and [z] is
   the representative of the class it is joining. *)

Context (M : gmap elem Z) (R : elem → elem) (a z : elem) (ia iz : Z).
Context (HR : uf_repr M R) (Hroot : R a = a) (Hz : R z = z).
Context (HMa : M !! a = Some ia) (HMz : M !! z = Some iz) (Hlt : (iz < ia)%Z).

Local Lemma link_z_ne_a : z ≠ a.
Proof.
  intros Heq. assert (Some iz = Some ia) as [= ?].
  { rewrite -HMz -HMa. by f_equal. }
  lia.
Qed.

(* [a] is a root, so naming its class by [a] is naming it by [R a]: the
   two forms of the update coincide, and this is what lets the proofs
   below case on [R u = a] directly. *)
Local Lemma link_unfold {B : Type} (f : elem → B) (b : B) u :
  f.[a -/R/> b] u = if decide (R u = a) then b else f u.
Proof. rewrite /update_class /fcupdate Hroot //. Qed.

(* Rootness is preserved outside of [a]. *)
Lemma uf_link_root_iff w : w ≠ a → (R.[a -/R/> z] w = w ↔ R w = w).
Proof.
  intros Hw. rewrite link_unfold. case_decide as Hcase; last done.
  split.
  - intros <-. exfalso. apply link_z_ne_a. by rewrite -Hcase Hz.
  - intros Hww. exfalso. apply Hw. by rewrite -Hww Hcase.
Qed.

Lemma uf_repr_link : uf_repr M R.[a -/R/> z].
Proof.
  destruct HR as [Hidem Hout Hdom Hle].
  pose proof link_z_ne_a as Hza.
  split; intros u; rewrite !link_unfold.
  - destruct (decide (R u = a)) as [Hu|Hu].
    + rewrite Hz. by destruct (decide (z = a)).
    + rewrite Hidem. by rewrite decide_False.
  - intros Hu. rewrite decide_False; first by apply Hout.
    rewrite Hout //. intros ->. apply Hu, elem_of_dom. by eexists.
  - intros Hu. case_decide; [by apply elem_of_dom; eexists | by apply Hdom].
  - intros iu j Hu. case_decide as Hcase.
    + rewrite HMz. intros [= <-].
      transitivity ia; first lia. by eapply Hle; [exact Hu | rewrite Hcase].
    + by eapply Hle.
Qed.

Lemma uf_link_value_coherent (V : elem → val) :
  (∀ u, V u = V (R u)) →
  ∀ u, V.[a -/R/> V z] u = V.[a -/R/> V z] (R.[a -/R/> z] u).
Proof.
  intros HV u. pose proof link_z_ne_a as Hza.
  destruct HR as [Hidem _ _ _].
  rewrite (link_unfold V (V z) u) (link_unfold R z u).
  destruct (decide (R u = a)) as [Hu|Hu].
  - rewrite (link_unfold V (V z) z) decide_False; [done | by rewrite Hz].
  - rewrite (link_unfold V (V z) (R u)) decide_False;
      [by apply HV | by rewrite Hidem].
Qed.

End link_state.

(* Acyclicity, in the form every step that links actually uses it: a
   vertex whose identifier is strictly below [z]'s cannot be represented
   by [z]. This is [repr_id_le] read backwards, and it is the reason
   [union] compares identifiers before it links. *)

Lemma uf_repr_ne M R (z y : elem) j k :
  uf_repr M R →
  M !! z = Some j → M !! y = Some k → (k < j)%Z →
  R y ≠ z.
Proof.
  intros HR HMz HMy Hk Hcontra.
  assert (Hy : y ∈ dom M) by (apply elem_of_dom; by eexists).
  pose proof (repr_dom _ _ HR y Hy) as Hry.
  apply elem_of_dom in Hry as [iy HMry].
  assert (Hle : (iy ≤ k)%Z) by (eapply (repr_id_le _ _ HR y); done).
  rewrite Hcontra HMz in HMry. simplify_eq. lia.
Qed.

Section uf_inv.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !ghost_varG Σ uf_state,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

Implicit Types x y z : elem.
Implicit Types i j : Z.
Implicit Types γ : uf_names.

(* ------------------------------------------------------------------------ *)
(* The abstract state. *)

(* The concurrent [UF γ D R V] plays the role of the sequential
   [UF D R V]: it is the client's exclusive handle on the state, and it
   is what the logically atomic specifications quantify over.

   We defined [UF γ D R V] as half of a ghost variable whose other half
   lives in the invariant. At its linearization point an operation
   opens the invariant, takes [UF] out of the client's atomic update,
   and either reads it or updates both halves at once.

   [UF] also carries [uf_val_congr] to enforce well-formedness of the
   state: the value function is constant on classes. *)

Definition uf_val_congr (Rp : elem → elem) (Vp : elem → val) : Prop :=
  ∀ u w, Rp u = Rp w → Vp u = Vp w.

(* [uf_val_congr] is preserved by the update to [V] and update to [R]
   and [V] that [set] and [union] produce. *)

Lemma uf_val_congr_set R V x v :
  uf_val_congr R V → uf_val_congr R V.[x -/R/> v].
Proof.
  intros HV u w Huw. unfold update_class, fcupdate.
  rewrite Huw. case_decide; [done | by apply HV].
Qed.

Lemma uf_val_congr_link R V b c :
  uf_val_congr R V → uf_val_congr R.[b -/R/> R c] V.[b -/R/> V c].
Proof.
  intros HV u w. unfold update_class, fcupdate.
  repeat case_decide; [done | by intros <-%HV | by intros ->%HV | by apply HV].
Qed.

(* [dethroned γ R]: every vertex that is not its own representative is
   a link, persistently. *)

Definition dethroned (γ : uf_names) (R : elem → elem) : iProp Σ :=
  □ (∀ (w : elem) (j : Z),
       vertex γ w j -∗ ⌜R w ≠ w⌝ -∗ ∃ rc lp, linked γ w rc lp).

Global Instance dethroned_persistent γ Rp : Persistent (dethroned γ Rp).
Proof. apply _. Qed.

(* Over the initial state every vertex is its own representative, so there
   is nothing to witness. *)

Lemma dethroned_id γ : ⊢ dethroned γ (λ x, x).
Proof. iIntros "!>" (w j) "_ %Hne". done. Qed.

(* Witnessing more dethroned roots when [union] links the root [b] into
   [c]'s tree. *)

Lemma dethroned_link γ R b c rc lp :
  R b = b →
  dethroned γ R -∗ linked γ b rc lp -∗ dethroned γ R.[b -/R/> R c].
Proof.
  iIntros (Hb) "#Hdeth #Hlk".
  iIntros "!>" (w j) "#Hw %Hne".
  rewrite /update_class /fcupdate in Hne.
  case_decide as Hcase.
  - (* [w] is in [b]'s old class. If it was a root it is [b]. *)
    destruct (decide (R w = w)) as [Hrw | Hrw].
    + rewrite -Hrw Hcase Hb. iExists rc, lp. iExact "Hlk".
    + iApply ("Hdeth" with "Hw"). iPureIntro. exact Hrw.
  - iApply ("Hdeth" with "Hw"). iPureIntro. exact Hne.
Qed.

Definition UF (γ : uf_names) (D : gset elem) (R : elem → elem)
    (V : elem → val) : iProp Σ :=
  ⌜uf_val_congr R V⌝ ∗
  ghost_var γ.(uf_abs) (1/2) (D, R, V) ∗
  dethroned γ R ∗
  ∃ S, ⌜same_class_sound S R⌝ ∗ own γ.(uf_class) (●{#1/2} S).

Lemma UF_dethroned γ D R V : UF γ D R V -∗ dethroned γ R.
Proof. by iIntros "(_ & _ & #$ & _)". Qed.

Global Instance UF_timeless γ D R V : Timeless (UF γ D R V).
Proof. apply _. Qed.

Lemma UF_agree γ D R V D' R' V' :
  UF γ D R V -∗ UF γ D' R' V' -∗ ⌜D = D' ∧ R = R' ∧ V = V'⌝.
Proof.
  iIntros "(_ & H1 & _) (_ & H2 & _)".
  by iDestruct (ghost_var_agree with "H1 H2") as %[= -> -> ->].
Qed.

Lemma UF_val_congr γ D R V : UF γ D R V -∗ ⌜uf_val_congr R V⌝.
Proof. by iIntros "($ & _)". Qed.

(* Reading a class fact against the state, from a handle alone. *)

Lemma UF_same_class_eq γ D R V u w :
  UF γ D R V -∗ same_class γ u w -∗ ⌜R u = R w⌝ ∗ UF γ D R V.
Proof.
  iIntros "(%Hcongr & Hvar & #Hdeth & (%S & %HS & HSauth)) #Hsc".
  iDestruct (same_class_eq with "HSauth Hsc") as %Heq; first exact HS.
  iFrame "Hvar Hdeth". iSplitR; first done. iSplitR; first done.
  iExists S. by iFrame "HSauth".
Qed.

(* Moving the state, we need both halves (aka two copies of [UF]). *)

Lemma UF_update_2 γ D R V D' R' V' :
  (∀ u w, R u = R w → R' u = R' w) →
  uf_val_congr R' V' →
  dethroned γ R' -∗
  UF γ D R V -∗ UF γ D R V ==∗ UF γ D' R' V' ∗ UF γ D' R' V'.
Proof.
  iIntros (Hmono Hcongr) "#Hdeth'
                          (_ & Hv1 & _ & (%S1 & %HS1 & Ha1))
                          (_ & Hv2 & _ & (%S2 & %HS2 & Ha2))".
  iMod (ghost_var_update_halves (D', R', V') with "Hv1 Hv2") as "[Hv1 Hv2]".
  iCombine "Ha1 Ha2" gives %[_ [->%leibniz_equiv _]]%auth_auth_dfrac_op_valid.
  iModIntro.
  iSplitL "Hv1 Ha1".
  - iSplitR; first done. iFrame "Hv1 Hdeth'". iExists S2. iFrame "Ha1".
    iPureIntro. by eapply same_class_sound_coarsen.
  - iSplitR; first done. iFrame "Hv2 Hdeth'". iExists S2. iFrame "Ha2".
    iPureIntro. by eapply same_class_sound_coarsen.
Qed.

(* Recording a new pair. *)

Lemma UF_same_class_update γ D R V u w :
  R u = R w →
  UF γ D R V -∗ UF γ D R V ==∗
  UF γ D R V ∗ UF γ D R V ∗ same_class γ u w.
Proof.
  iIntros (Huw) "($ & $ & $ & (%S1 & %HS1 & Ha1))
                 ($ & $ & $ & (%S2 & %HS2 & Ha2))".
  iCombine "Ha1 Ha2" gives %[_ [->%leibniz_equiv _]]%auth_auth_dfrac_op_valid.
  iCombine "Ha1 Ha2" as "Ha".
  iMod (same_class_update _ _ R u w with "Ha") as (S') "(Ha & #Hsc & %HS' & _)";
    [exact HS2 | exact Huw |].
  iModIntro. iFrame "Hsc".
  iDestruct "Ha" as "[Ha1 Ha2]".
  iSplitL "Ha1"; iExists S'; by iFrame.
Qed.

(* [in_uf γ x]: [x] is a vertex of the structure.
   This is the equivalent of stating [⌜x ∈ D⌝], which cannot be stated
   as a pure side condition here because [D] is only known at the
   linearization point. *)

Definition in_uf (γ : uf_names) (x : elem) : iProp Σ := ∃ i, vertex γ x i.

Global Instance in_uf_persistent γ x : Persistent (in_uf γ x).
Proof. apply _. Qed.
(* ------------------------------------------------------------------------ *)

(* The global invariant holds:
   - [γ.(uf_vert) 1 M]: the authoritative map of vertices with their
     physical footprints,
   - [γ.(uf_link) 1 L]: the registry of which vertices have been linked away,
   - [γ.(uf_ids) 1 N]: the identifier registry,
   - [UF γ (dom M) R V]: half of the abstract state.

   We require that [R] is a representative function via [uf_repr M R],
   and that [V] is conserved by [R] [V x = V (R x)].

   [id_tokens γ M] keeps a global view on the identifiers and ensures
   that they are injective.

   [L]'s domain is pinned to [M]'s to allow [make] to put a fresh
   vertex into it (we need to prove the key is absent). *)

Definition uf_inv (γ : uf_names) : iProp Σ :=
  ∃ (M : gmap elem Z) (L : gmap elem (option record)) (N : gmap Z unit)
    (R : elem → elem) (V : elem → val),
    ghost_map_auth γ.(uf_vert) 1 M ∗
    ghost_map_auth γ.(uf_link) 1 L ∗
    ghost_map_auth γ.(uf_ids) 1 N ∗
    UF γ (dom M) R V ∗
    ⌜dom L = dom M⌝ ∗
    ⌜∀ x i, M !! x = Some i → representable i⌝ ∗
    ⌜uf_repr M R⌝ ∗
    ⌜∀ x, V x = V (R x)⌝ ∗
    id_tokens γ M ∗
    ([∗ map] x ↦ i ∈ M, vertex_own γ R V x i).

Definition is_uf (γ : uf_names) : iProp Σ :=
  inv ufN (uf_inv γ).

(* Allocating an empty structure. *)

Lemma uf_alloc E (V0 : elem → val) :
  ⊢ |={E}=> ∃ γ, is_uf γ ∗ UF γ ∅ (λ x, x) V0.
Proof.
  iMod (ghost_map_alloc_empty (K:=elem) (V:=Z)) as (γv) "Hγ".
  iMod (ghost_map_alloc_empty (K:=elem) (V:=option record)) as (γl) "Hγl".
  iMod (ghost_map_alloc_empty (K:=Z) (V:=unit)) as (γn) "Hγn".
  iMod (own_alloc (● (∅ : gset (elem * elem)))) as (γc) "Hγe";
    first by apply auth_auth_valid.
  iMod (ghost_var_alloc (∅ : gset elem, (λ x : elem, x), V0)) as (γa) "[Hγs Hγs']".
  set (γ := UfNames γv γl γn γc γa).
  (* The class authority is split at once: half for the invariant's [UF],
     half for the client's. *)
  iDestruct "Hγe" as "[Hγe Hγe']".
  iAssert (UF γ ∅ (λ x, x) V0) with "[Hγs Hγe]" as "HUF".
  { iSplitR; first by iPureIntro; intros u w ->.
    iFrame "Hγs". iSplitR; first iApply dethroned_id.
    iExists ∅. iFrame "Hγe".
    iPureIntro. intros u w Huw. set_solver. }
  iAssert (UF γ ∅ (λ x, x) V0) with "[Hγs' Hγe']" as "HUF'".
  { iSplitR; first by iPureIntro; intros u w ->.
    iFrame "Hγs'". iSplitR; first iApply dethroned_id.
    iExists ∅. iFrame "Hγe'".
    iPureIntro. intros u w Huw. set_solver. }
  iMod (inv_alloc ufN _ (uf_inv γ) with "[Hγ Hγl Hγn HUF]") as "#Hinv".
  { iNext. iExists ∅, ∅, ∅, (λ x, x), V0.
    rewrite dom_empty_L. iFrame.
    iSplit; [by rewrite !dom_empty_L|].
    iSplit; [iPureIntro; intros x i; rewrite lookup_empty; discriminate|].
    iSplit; [iPureIntro; split; try done; intros x i j;
             rewrite lookup_empty; discriminate|].
    iSplit; [by iPureIntro|].
    rewrite /id_tokens. by rewrite !big_sepM_empty. }
  iModIntro. iExists γ. by iFrame "Hinv HUF'".
Qed.

(* ------------------------------------------------------------------------ *)
(* Accessing the invariant. *)

(* [uf_frame γ z j D R V] lets the single accessor below expose one
   vertex's cell and nothing else. *)

Definition uf_frame (γ : uf_names) z j
    (D : gset elem) (R : elem → elem) (V : elem → val) : iProp Σ :=
  ∃ (M : gmap elem Z) (L : gmap elem (option record)) (N : gmap Z unit),
    ⌜M !! z = Some j⌝ ∗ ⌜dom M = D⌝ ∗ ⌜dom L = dom M⌝ ∗
    ⌜∀ x i, M !! x = Some i → representable i⌝ ∗
    ⌜uf_repr M R⌝ ∗ ⌜∀ x, V x = V (R x)⌝ ∗
    ghost_map_auth γ.(uf_vert) 1 M ∗ ghost_map_auth γ.(uf_link) 1 L ∗
    ghost_map_auth γ.(uf_ids) 1 N ∗
    id_tokens γ M ∗
    ([∗ map] x ↦ i ∈ delete z M, vertex_own γ R V x i).

(* [uf_inv_split] singles out one vertex's footprint *)

Lemma uf_inv_split γ z j lzi lzc :
  z ↪[γ.(uf_vert)]□ j -∗
  blockLocs z [lzi; lzc] -∗
  ▷ uf_inv γ -∗
  ◇ ∃ (c : content) (D : gset elem) (R : elem → elem) (V : elem → val),
    ⌜z ∈ D⌝ ∗
    UF γ D R V ∗
    ▷ (lzc ↦ #c) ∗
    ▷ cell_own γ R V z j c ∗
    ▷ uf_frame γ z j D R V.
Proof.
  iIntros "#Hzfrag #Hzlocs H".
  iDestruct "H" as (M L N R V)
    "(>Hauth & >Hlauth & >Hnauth & >Hcont &
      >%HdomL & >%Hrep & >%HR & >%HV & Htoks & HM)".
  iDestruct (ghost_map_lookup with "Hauth Hzfrag") as %HMz.
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iDestruct "HM" as "[Hvo HM]".
  iDestruct "Hvo" as (li' lc' c) "(#Hzlocs' & Hlc & Hcell)".
  iAssert (▷ ⌜[lzi; lzc] = [li'; lc']⌝)%I with "[]" as ">%Heql".
  { iNext. iApply (blockLocs_valid with "Hzlocs' Hzlocs"). }
  simplify_eq.
  iExists c, (dom M), R, V.
  iModIntro.
  iSplitR; first by iPureIntro; eapply elem_of_dom_2.
  iFrame "Hcont Hlc Hcell".
  iNext. iExists M, L, N.
  do 6 (iSplitR; first done).
  iFrame "Hauth Hlauth Hnauth Htoks HM".
Qed.

Lemma uf_inv_reassemble γ z j lzi lzc c' D R V :
  UF γ D R V -∗
  blockLocs z [lzi; lzc] -∗
  lzc ↦ #c' -∗
  cell_own γ R V z j c' -∗
  uf_frame γ z j D R V -∗
  uf_inv γ.
Proof.
  iIntros "Hcont #Hzlocs Hlc Hcell Hframe".
  iDestruct "Hframe" as (M L N)
    "(%HMz & %HdomM & %HdomL & %Hrep & %HRp & %HVp &
      Hauth & Hlauth & Hnauth & Htoks & HM)".
  subst D.
  iExists M, L, N, R, V.
  iFrame "Hauth Hlauth Hnauth Hcont Htoks".
  do 4 (iSplitR; first done).
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iFrame "HM".
  iExists lzi, lzc, c'. iFrame "Hzlocs Hlc Hcell".
Qed.

(* Restate [uf_inv_split] but without an explicit [uf_frame]. *)

Lemma uf_inv_acc γ z j lzi lzc :
  z ↪[γ.(uf_vert)]□ j -∗
  blockLocs z [lzi;lzc] -∗
  ▷ uf_inv γ -∗
  ◇ ∃ c D R V,
    ⌜z ∈ D⌝ ∗
    UF γ D R V ∗
    ▷ (lzc ↦ #c) ∗
    ▷ cell_own γ R V z j c ∗
    ▷ (UF γ D R V -∗ lzc ↦ #c -∗ cell_own γ R V z j c -∗ uf_inv γ).
Proof.
  iIntros "#Hzfrag #Hzlocs Hinv".
  iPoseProof (uf_inv_split with "Hzfrag Hzlocs Hinv") as (c D R V)
    ">(%Hin & Hcont & Hlc & Hcell & Hframe)".
  iModIntro.
  iExists c, D, R, V.
  iFrame. iFrame "%". iModIntro.
  iIntros "HUF Hlzc Hcell".
  iApply (uf_inv_reassemble with "HUF Hzlocs Hlzc Hcell Hframe").
Qed.

(* ------------------------------------------------------------------------ *)
(* Accessing the invariant with the right to move the abstract state. *)

Definition uf_close (γ : uf_names) (z : elem) (j : Z) (lzc : locations.loc)
    (M : gmap elem Z) (R : elem → elem) (V : elem → val) : iProp Σ :=
  ∀ (c' : content) (R' : elem → elem) (V' : elem → val),
    ⌜uf_repr M R'⌝ -∗
    ⌜∀ x, V' x = V' (R' x)⌝ -∗
    ⌜∀ w, w ∈ dom M → w ≠ z → (R' w = w ↔ R w = w)⌝ -∗
    ⌜∀ w, w ∈ dom M → w ≠ z → R w = w → V' w = V w⌝ -∗
    UF γ (dom M) R' V' -∗
    lzc ↦ #c' -∗
    cell_own γ R' V' z j c' -∗
    uf_inv γ.

Lemma uf_close_intro γ z j lzi lzc M L N R V :
  M !! z = Some j →
  dom L = dom M →
  (∀ x i, M !! x = Some i → representable i) →
  blockLocs z [lzi; lzc] -∗
  ghost_map_auth γ.(uf_vert) 1 M -∗
  ghost_map_auth γ.(uf_link) 1 L -∗
  ghost_map_auth γ.(uf_ids) 1 N -∗
  id_tokens γ M -∗
  ([∗ map] x ↦ i ∈ delete z M, vertex_own γ R V x i) -∗
  uf_close γ z j lzc M R V.
Proof.
  iIntros (HMz HdomL Hrepr) "#Hzlocs Hauth Hlauth Hnauth Htoks HM".
  iIntros (c' R' V') "%HR' %HV' %Hroot %Hval HUF Hlc Hcell".
  iExists M, L, N, R', V'.
  iFrame "Hauth Hlauth Hnauth HUF Htoks".
  do 4 (iSplitR; first done).
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iSplitR "HM".
  { iExists lzi, lzc, c'. iFrame "Hzlocs Hlc Hcell". }
  iApply (vertex_own_reindex with "HM").
  - intros w i Hw. apply Hroot.
    + apply elem_of_dom. exists i.
      eapply lookup_weaken; [exact Hw | apply delete_subseteq].
    + intros ->. by rewrite lookup_delete_eq in Hw.
  - intros w i Hw Hrw. apply Hval; [| | exact Hrw].
    + apply elem_of_dom. exists i.
      eapply lookup_weaken; [exact Hw | apply delete_subseteq].
    + intros ->. by rewrite lookup_delete_eq in Hw.
Qed.

(* [uf_inv_acc_update] is [uf_inv_acc] with a closer that may move the
   state. Three things beyond [uf_inv_acc] come out of it, and each is a
   piece of ghost bookkeeping the caller would otherwise have to do with
   the invariant's authorities in hand:

   - the registry [M] itself, with [z]'s entry and the entry of one other
     vertex [y] the caller names up front. The linking CAS has to compare
     the two identifiers, so it needs [y]'s; and it cannot look it up
     itself, since the authority stays inside the closer.

   - the state facts [uf_repr M R] and the value coherence.

   - the right to link [z] away: the second branch consumes [z]'s root
     token, registers a fresh link record, and hands back the persistent
     [linked] witness, the ghost step that dethrones [z]. A caller that
     only reads, or whose CAS failed, takes the first branch and closes
     unchanged. *)

Lemma uf_inv_acc_update γ z j lzi lzc (y : elem) (k : Z) :
  z ↪[γ.(uf_vert)]□ j -∗
  y ↪[γ.(uf_vert)]□ k -∗
  blockLocs z [lzi; lzc] -∗
  ▷ uf_inv γ -∗
  ◇ ∃ (c : content) (M : gmap elem Z) (R : elem → elem) (V : elem → val),
    ⌜M !! z = Some j⌝ ∗ ⌜M !! y = Some k⌝ ∗
    ⌜uf_repr M R⌝ ∗ ⌜∀ x, V x = V (R x)⌝ ∗
    UF γ (dom M) R V ∗
    ▷ (lzc ↦ #c) ∗
    ▷ cell_own γ R V z j c ∗
    ▷ (uf_close γ z j lzc M R V
       ∧ (∀ (rc : record) (lp : locations.loc),
            blockLocs rc [lp] -∗ z ↪[γ.(uf_link)] None ==∗
            linked γ z rc lp ∗ uf_close γ z j lzc M R V)).
Proof.
  iIntros "#Hzfrag #Hyfrag #Hzlocs H".
  iDestruct "H" as (M L N R V)
    "(>Hauth & >Hlauth & >Hnauth & >Hcont &
      >%HdomL & >%Hrepr & >%HR & >%HV & Htoks & HM)".
  iDestruct (ghost_map_lookup with "Hauth Hzfrag") as %HMz.
  iDestruct (ghost_map_lookup with "Hauth Hyfrag") as %HMy.
  rewrite (big_sepM_delete _ M z j); last exact HMz.
  iDestruct "HM" as "[Hvo HM]".
  iDestruct "Hvo" as (li' lc' c) "(#Hzlocs' & Hlc & Hcell)".
  iAssert (▷ ⌜[lzi; lzc] = [li'; lc']⌝)%I with "[]" as ">%Heql".
  { iNext. iApply (blockLocs_valid with "Hzlocs' Hzlocs"). }
  simplify_eq.
  iExists c, M, R, V.
  iModIntro.
  iFrame "Hcont Hlc Hcell".
  do 4 (iSplitR; first done).
  iNext. iSplit.
  - iApply (uf_close_intro with "Hzlocs Hauth Hlauth Hnauth Htoks HM"); done.
  - iIntros (rc lp) "#Hlocs Htok".
    iDestruct (ghost_map_lookup with "Hlauth Htok") as %HLz.
    iMod (ghost_map_update (Some rc) with "Hlauth Htok") as "[Hlauth Htok]".
    iMod (ghost_map_elem_persist with "Htok") as "#Htok".
    assert (Hdom' : dom (<[z := Some rc]> L) = dom M).
    { rewrite dom_insert_lookup_L; [exact HdomL | by eexists]. }
    iModIntro. iSplitR; first by iFrame "Htok Hlocs".
    iApply (uf_close_intro with "Hzlocs Hauth Hlauth Hnauth Htoks HM"); done.
Qed.

(* Closing on the state one took: the two reindexing conditions are
   vacuous. *)

Lemma uf_close_id γ z j lzc M R V c :
  uf_repr M R →
  (∀ x, V x = V (R x)) →
  uf_close γ z j lzc M R V -∗
  UF γ (dom M) R V -∗ lzc ↦ #c -∗ cell_own γ R V z j c -∗ uf_inv γ.
Proof.
  iIntros (HR HV) "Hclose HUF Hlc Hcell".
  iApply ("Hclose" with "[%] [%] [%] [%] HUF Hlc Hcell"); [done | done | | ].
  - intros w _ _. reflexivity.
  - intros w _ _ _. reflexivity.
Qed.

(* Closing on the linking transition: [z], a root, is linked into [y],
   whose identifier is strictly below [z]'s, and its cell now holds the
   fresh link record [rc].

   This is where [union]'s state argument lives, and the whole of it is
   the [link_state] section above: the identifier ordering makes [R y]
   different from [z] ([uf_repr_ne]), which is what turns the update into
   a representative function again ([uf_repr_link]) rather than a cycle,
   keeps the value function coherent ([uf_link_value_coherent]), and
   leaves every other vertex's root-status alone ([uf_link_root_iff]). *)

Lemma uf_close_link γ z j lzc M R V (y : elem) k rc lp :
  M !! z = Some j →
  M !! y = Some k →
  (k < j)%Z →
  uf_repr M R →
  (∀ x, V x = V (R x)) →
  R z = z →
  uf_close γ z j lzc M R V -∗
  UF γ (dom M) R.[z -/R/> R y] V.[z -/R/> V y] -∗
  lzc ↦ #(CtLink rc) -∗
  linked γ z rc lp -∗
  link_field γ rc lp z j -∗
  uf_inv γ.
Proof.
  intros HMz HMy Hk HR HV Hroot.
  (* [y]'s representative: the vertex the class is re-hung under. *)
  assert (Hy : y ∈ dom M) by (apply elem_of_dom; by eexists).
  pose proof (repr_dom _ _ HR y Hy) as Hry.
  apply elem_of_dom in Hry as [iy HMry].
  assert (Hiy : (iy ≤ k)%Z) by (eapply (repr_id_le _ _ HR y); done).
  assert (Hlt : (iy < j)%Z) by lia.
  assert (Hne : R y ≠ z) by (eapply uf_repr_ne; done).
  pose proof (repr_idem _ _ HR y) as Hidem.
  (* Naming the class by [y] or by its representative is the same. *)
  assert (HeqV : V.[z -/R/> V y] = V.[z -/R/> V (R y)]) by (by rewrite (HV y)).
  rewrite HeqV.
  iIntros "Hclose HUF Hlc #Hlk Hlf".
  iApply ("Hclose" $! (CtLink rc) with "[%] [%] [%] [%] HUF Hlc [Hlf]").
  - eapply (uf_repr_link M R z (R y) j iy); done.
  - eapply (uf_link_value_coherent M R z (R y) j iy); done.
  - intros w _ Hwz. eapply (uf_link_root_iff M R z (R y) j iy); done.
  - intros w _ Hwz Hrw.
    rewrite lookup_update_class_ne //. by rewrite Hroot Hrw.
  - iExists lp. iFrame "Hlk Hlf". iPureIntro.
    rewrite lookup_update_class. exact Hne.
Qed.

(* Closing on the value transition: [z], a root, keeps its root-status
   and its class, and its cell swings to a freshly allocated [Root]
   record carrying [v].

   [R] does not move at all, so no vertex changes root-status and the two
   reindexing conditions are almost vacuous: the only one with content is
   that no other root's value moved, which holds because [z] is the sole
   root of the class the update touches ([lookup_update_class_ne], read
   at a root [w ≠ z]). Value coherence is [lookup_class_root]: assigning
   a whole class at once is exactly what keeps [V u = V (R u)]. *)

Lemma uf_close_set γ z j lzc M R V rc (v : val) :
  M !! z = Some j →
  uf_repr M R →
  (∀ x, V x = V (R x)) →
  R z = z →
  uf_close γ z j lzc M R V -∗
  UF γ (dom M) R V.[z -/R/> v] -∗
  lzc ↦ #(CtRoot rc) -∗
  z ↪[γ.(uf_link)] None -∗
  root_val rc v -∗
  uf_inv γ.
Proof.
  intros HMz HR HV Hroot.
  assert (Idempotent R) by (constructor; apply (repr_idem _ _ HR)).
  iIntros "Hclose HUF Hlc Htok Hrv".
  iApply ("Hclose" $! (CtRoot rc) with "[%] [%] [%] [%] HUF Hlc [Htok Hrv]").
  - exact HR.
  - intros u. apply lookup_class_root, HV.
  - intros w _ _. reflexivity.
  - intros w _ Hwz Hrw.
    rewrite lookup_update_class_ne //. by rewrite Hroot Hrw.
  - iSplitR; first done. iFrame "Htok".
    rewrite lookup_update_class. iFrame "Hrv".
Qed.

(* ------------------------------------------------------------------------ *)
(* The linearization point of [make]: registering a fresh vertex. *)

(* [make] allocates a vertex record and a [Root] content record, and
   then, in one ghost step, declares the result a vertex of the
   structure: the domain gains [x], and [x] takes the value [v]. *)

Lemma register_vertex  (Q : iProp Σ) γ (x : elem) i (rc : record)
    (v : val) :
  ⌜representable i⌝ -∗
  is_uf γ -∗
  i ↪[γ.(uf_ids)] () -∗
  x ⤇ {| vertex_id_f := i; vertex_content_f := CtRoot rc |} -∗
  rc ⤇ {| root_value := v |} -∗
  (∀ D (R : elem → elem) (V : elem → val),
     ⌜x ∉ D⌝ -∗ ⌜R x = x⌝ -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗
     UF γ (D ∪ {[x]}) R V.[x -/R/> v] ∗ Q) -∗
  |={⊤}=> vertex γ x i ∗ Q.
Proof.
  iIntros (Hrep) "#Hinv Htokn Hx Hrc Hhook".
  iInv "Hinv" as (M L N Rp Vp)
    "(>Hauth & >Hlauth & >Hnauth & >Hcont &
      >%HdomL & >%Hrepr & >%HRp & >%HVp & >Htoks & HM)" "Hclose".

  rewrite {1}/ownRecord /ownBlock /=.
  iDestruct "Hx" as (ls) "(#Hlocs & #HP & Hxs)".
  iDestruct (big_opLZ.big_sepLZ2_cons_inv_r with "Hxs")
    as (li ls') "(-> & Hli & Hxs)".
  iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs") as (lc) "[-> Hlc]".
  rewrite list_z.singleton_unfold.

  (* The allocated record is not a vertex yet: a vertex owns its content
     cell, and the caller is still holding this one. *)
  destruct (M !! x) as [j|] eqn:HMx.
  { iAssert (▷ False)%I with "[HM Hlc]" as ">[]".
    iNext. rewrite (big_sepM_lookup _ M x j) //.
    iApply (vertex_own_fresh_ne with "Hlocs Hlc HM"). }
  assert (HxD : x ∉ dom M) by (apply not_elem_of_dom; exact HMx).
  assert (HLx : L !! x = None)
    by (apply not_elem_of_dom; rewrite HdomL; exact HxD).
  (* Hence it is already its own representative, by [repr_out]. *)
  assert (Hroot : Rp x = x) by (by apply (repr_out _ _ HRp)).

  iMod (ghost_map_insert x i with "Hauth") as "[Hauth Hxfrag]"; first exact HMx.
  iMod (ghost_map_elem_persist with "Hxfrag") as "#Hxfrag".
  iMod (ghost_map_insert x None with "Hlauth") as "[Hlauth Htokl]";
    first exact HLx.
  iMod (gen_heap.pointsto_persist with "Hli") as "#Hli".
  iMod (root_val_alloc with "Hrc") as "#Hrv".

  (* The linearization point proper. *)
  iMod ("Hhook" $! (dom M) Rp Vp with "[//] [//] Hcont") as "[Hcont HQ]".

  iMod ("Hclose" with "[-HQ]") as "_".
  { iNext.
    iExists (<[x := i]> M), (<[x := None]> L), N, Rp, Vp.[x -/Rp/> v].
    iFrame "Hauth Hlauth Hnauth".
    rewrite dom_insert_L (union_comm_L {[x]} (dom M)). iFrame "Hcont".
    iSplitR; first (iPureIntro; rewrite dom_insert_L HdomL; set_solver).
    iSplitR.
    { iPureIntro. intros y k. destruct (decide (y = x)) as [->|Hne].
      - rewrite lookup_insert_eq. by intros [= <-].
      - rewrite lookup_insert_ne //. apply Hrepr. }
    iSplitR.
    { (* [R] has not moved, so all four properties are the old ones plus
         the new vertex's, and the new vertex is its own class. *)
      iPureIntro. destruct HRp as [Hidem Hout Hdom Hle]. split.
      - exact Hidem.
      - intros u Hu. apply Hout. rewrite dom_insert_L in Hu. set_solver.
      - intros u Hu. rewrite dom_insert_L. rewrite dom_insert_L in Hu.
        apply elem_of_union in Hu as [Hu|Hu].
        + apply elem_of_singleton in Hu as ->. rewrite Hroot. set_solver.
        + apply elem_of_union_r. by apply Hdom.
      - intros u iu ju Hu Hru.
        destruct (decide (u = x)) as [->|Hne].
        + rewrite lookup_insert_eq in Hu. rewrite Hroot lookup_insert_eq in Hru.
          simplify_eq. lia.
        + rewrite lookup_insert_ne // in Hu.
          (* [u]'s representative is an old vertex, so not the fresh one. *)
          assert (Hrux : Rp u ≠ x).
          { intros Habs. apply HxD. rewrite -Habs.
            apply Hdom, elem_of_dom. by eexists. }
          rewrite lookup_insert_ne // in Hru.
          by eapply Hle. }
    iSplitR.
    { iPureIntro.
      assert (Idempotent Rp) by (constructor; apply (repr_idem _ _ HRp)).
      intros u. apply lookup_class_root, HVp. }
    rewrite /id_tokens big_sepM_insert //.
    iFrame "Htokn Htoks".
    rewrite big_sepM_insert //.
    iSplitR "HM".
    - (* The fresh vertex's own footprint: a [Root] cell holding [v]. *)
      iExists li, lc, (CtRoot rc).
      iFrame "Hlocs Hlc".
      iSplitR; first (iPureIntro; exact Hroot).
      iFrame "Htokl".
      rewrite lookup_update_class //.
    - (* Every other vertex: no root-status changed, and no surviving
         root's value did either, the fresh vertex being nobody else's
         representative. *)
      iApply (vertex_own_reindex with "HM"); first done.
      intros w k Hw Hw'. rewrite lookup_update_class_ne //.
      rewrite Hroot Hw'. intros ->. by rewrite HMx in Hw. }
  iModIntro. iSplitR "HQ"; last iExact "HQ".
  iExists li, lc. by iFrame "Hxfrag Hlocs HP Hli".
Qed.

End uf_inv.

Section same_class.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !ghost_varG Σ uf_state,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

(* ------------------------------------------------------------------------ *)
(* The [same_class] API. *)

(* Observing that two vertices are in one class, against the abstract
   state, at a ghost instant.

   [union] needs this for the case where it has nothing to do: it has
   chased both arguments to a common vertex, so they are equivalent
   and it returns [None]. *)

Lemma uf_same_class_commit γ (u w c : elem) (Q : iProp Σ) :
  is_uf γ -∗
  same_class γ u c -∗
  same_class γ w c -∗
  (∀ D (R : elem → elem) (V : elem → val),
     ⌜R u = R w⌝ -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V ∗ Q) ={⊤}=∗ Q.
Proof.
  iIntros "#Hinv #Huc #Hwc Hk".
  iInv "Hinv" as (M L N Rp Vp)
    "(>Hauth & >Hlauth & >Hnauth & >Hcont &
      >%HdomL & >%Hrep & >%HRp & >%HVp & HM)" "Hclose".
  iDestruct (UF_same_class_eq with "Hcont Huc") as "[%Huc Hcont]".
  iDestruct (UF_same_class_eq with "Hcont Hwc") as "[%Hwc Hcont]".
  iMod ("Hk" $! (dom M) Rp Vp with "[%] Hcont") as "[Hcont HQ]".
  { by rewrite Huc Hwc. }
  iMod ("Hclose" with "[-HQ]") as "_".
  { iNext. iExists M, L, N, Rp, Vp.
    iFrame "Hauth Hlauth Hnauth Hcont HM".
    by do 3 (iSplitR; first done). }
  by iModIntro.
Qed.

Lemma same_class_sibling γ x y z :
  same_class γ x y -∗ same_class γ x z -∗ same_class γ y z.
Proof.
  iIntros "#Hxy #Hxz".
  iApply (same_class_trans with "[] Hxz").
  by iApply same_class_sym.
Qed.

End same_class.

(* ------------------------------------------------------------------------ *)
(* The vertex-level API used in the proof. *)

Section uf_api.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !ghost_varG Σ uf_state,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

Implicit Types x y z : elem.
Implicit Types rc : record.
Implicit Types i j : Z.
Implicit Types γ : uf_names.

(* Reading a vertex's content cell, and gives the cell straight back. *)

Lemma uf_vertex_content_acc γ z i lzi lzc (Φ : content → iProp Σ) :
  is_uf γ -∗
  vertex γ z i -∗
  blockLocs z [lzi; lzc] -∗
  ▷ (∀ c : content, content_info γ z c -∗ Φ c) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ c : content,
    ▷ (lzc ↦ #c) ∗ ▷ (lzc ↦ #c -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ c).
Proof.
  iIntros "#Hinv #Hz #Hzlocs HΦ".
  iDestruct (vertex_frag with "Hz") as "#Hzfrag".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_acc with "Hzfrag Hzlocs H") as (c D Rp Vp)
    "(_ & Hcont & Hlc & Hcell & Hframe)".
  iModIntro. iExists c. iFrame "Hlc".
  iIntros "!> Hlc".
  iDestruct (cell_own_info with "Hcell") as "(_ & #Hinfo & _ & Hcell)".
  iMod ("Hclose" with "[Hcont Hlc Hcell Hframe]") as "_".
  { iNext.
    iApply ("Hframe" with "Hcont Hlc Hcell"). }
  iModIntro. iApply ("HΦ" with "Hinfo").
Qed.

(* The same read, for a vertex already known to have been linked away. *)

Lemma uf_vertex_content_acc_linked γ z j lzi lzc rc lp (Φ : content → iProp Σ) :
  is_uf γ -∗
  vertex γ z j -∗
  blockLocs z [lzi; lzc] -∗
  linked γ z rc lp -∗
  ▷ (∀ c : content, ⌜c = CtLink rc⌝ -∗ content_info γ z c -∗ Φ c) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ c : content,
    ▷ (lzc ↦ #c) ∗ ▷ (lzc ↦ #c -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ c).
Proof.
  iIntros "#Hinv #Hz #Hzlocs #Hlk HΦ".
  iDestruct (vertex_frag with "Hz") as "#Hzfrag".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_acc with "Hzfrag Hzlocs H") as (c D Rp Vp)
    "(_ & Hcont & Hlc & Hcell & Hframe)".
  iModIntro. iExists c. iFrame "Hlc".
  iIntros "!> Hlc".
  iDestruct (cell_own_linked with "Hlk Hcell") as "(%Hc & Hcell)".
  iDestruct (cell_own_info with "Hcell") as "(_ & #Hinfo & _ & Hcell)".
  iMod ("Hclose" with "[Hcont Hlc Hcell Hframe]") as "_".
  { iNext.
    iApply ("Hframe" with "Hcont Hlc Hcell"). }
  iModIntro. iApply ("HΦ" with "[//] Hinfo").
Qed.

(* The same read once more, this time with the [linked] witness held by
   the caller inside a disjunction. *)

Lemma uf_vertex_content_acc_or_linked γ z j lzi lzc (P Q : iProp Σ)
    (Φ : content → iProp Σ) :
  is_uf γ -∗
  vertex γ z j -∗
  blockLocs z [lzi; lzc] -∗
  (P ∨ (∃ rc lp, linked γ z rc lp) ∗ Q) -∗
  ▷ (∀ c : content, content_info γ z c -∗
       (P ∨ ⌜content_root c = false⌝ ∗ Q) -∗ Φ c) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ c : content,
    ▷ (lzc ↦ #c) ∗ ▷ (lzc ↦ #c -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ c).
Proof.
  iIntros "#Hinv #Hz #Hzlocs HPQ HΦ".
  iDestruct (vertex_frag with "Hz") as "#Hzfrag".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_acc with "Hzfrag Hzlocs H") as (c D Rp Vp)
    "(_ & Hcont & Hlc & Hcell & Hframe)".
  iModIntro. iExists c. iFrame "Hlc".
  iIntros "!> Hlc".
  (* Refute the right branch, if that is the one the caller is in, against
     the cell the invariant currently holds. *)
  iAssert (cell_own γ Rp Vp z j c ∗ (P ∨ ⌜content_root c = false⌝ ∗ Q))%I
    with "[Hcell HPQ]" as "[Hcell HPQ]".
  { iDestruct "HPQ" as "[HP | [(%rc & %lp & #Hlk) HQ]]".
    - by iFrame "Hcell HP".
    - iDestruct (cell_own_linked with "Hlk Hcell") as "(%Hc & Hcell)".
      iFrame "Hcell". iRight. iFrame "HQ". by subst c. }
  iDestruct (cell_own_info with "Hcell") as "(_ & #Hinfo & _ & Hcell)".
  iMod ("Hclose" with "[Hcont Hlc Hcell Hframe]") as "_".
  { iApply ("Hframe" with "Hcont Hlc Hcell"). }
  iModIntro. iApply ("HΦ" with "Hinfo HPQ").
Qed.

(* ------------------------------------------------------------------------ *)
(* The linearization point of [find]. *)

(* This is [uf_vertex_content_acc] with the abstract state added: the
   continuation receives the invariant's half of [UF] with the fact
   that if the cell holds a root, then [z] is its own representative.

   The state is handed over read-only. *)

Lemma uf_find_content_acc γ (z : elem) j lzi lzc
    (Φ : content → iProp Σ) :
  is_uf γ -∗
  z ↪[γ.(uf_vert)]□ j -∗
  blockLocs z [lzi; lzc] -∗
  ▷ (∀ (c : content) D (R : elem → elem) (V : elem → val),
       ⌜z ∈ D⌝ -∗
       ⌜content_root c = true → R z = z⌝ -∗
       content_info γ z c -∗
       content_val V z c -∗
       UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V ∗ Φ c) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ c : content,
    ▷ (lzc ↦ #c) ∗ ▷ (lzc ↦ #c -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ c).
Proof.
  iIntros "#Hinv #Hzfrag #Hzlocs HΦ".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_split with "Hzfrag Hzlocs H") as (c D Rp Vp)
    "(%HzD & Hcont & Hlc & Hcell & Hframe)".
  iModIntro. iExists c. iFrame "Hlc".
  iIntros "!> Hlc".
  iDestruct (cell_own_info with "Hcell") as "(%Hiff & #Hinfo & #Hval & Hcell)".
  iMod ("HΦ" with "[//] [%] Hinfo Hval Hcont") as "[Hcont HΦ]".
  { by apply Hiff. }
  iMod ("Hclose" with "[Hcont Hlc Hcell Hframe]") as "_".
  { iNext.
    iApply (uf_inv_reassemble with "Hcont Hzlocs Hlc Hcell Hframe"). }
  by iModIntro.
Qed.

(* Distinct vertices have distinct identifiers. *)

Lemma vertex_ids_ne γ (a w : elem) ia iw :
  a ≠ w →
  is_uf γ -∗
  vertex γ a ia -∗
  vertex γ w iw -∗
  |={⊤}=> ⌜ia ≠ iw ∧ representable ia ∧ representable iw⌝.
Proof.
  iIntros (Hne) "#Hinv #Ha #Hw".
  iDestruct (vertex_frag with "Ha") as "#Hafrag".
  iDestruct (vertex_frag with "Hw") as "#Hwfrag".
  iInv "Hinv" as (M L N Rp Vp)
    "(>Hauth & >Hlauth & >Hnauth & >Hcont &
      >%HdomL & >%Hrep & >%HRp & >%HVp & >Htoks & HM)" "Hclose".
  iDestruct (ghost_map_lookup with "Hauth Hafrag") as %HMa.
  iDestruct (ghost_map_lookup with "Hauth Hwfrag") as %HMw.
  iDestruct (id_tokens_injective with "Htoks") as %Hij; [done..|].
  iMod ("Hclose" with "[Hauth Hlauth Hnauth Hcont Htoks HM]") as "_".
  { iNext. iExists M, L, N, Rp, Vp. by iFrame. }
  iModIntro. iPureIntro.
  split; [exact Hij | split; [exact (Hrep a ia HMa) | exact (Hrep w iw HMw)]].
Qed.

(* A single vertex's identifier is representable. *)

Lemma vertex_representable γ x i :
  is_uf γ -∗ vertex γ x i ={⊤}=∗ ⌜representable i⌝.
Proof.
  iIntros "#Hinv #Hx".
  iDestruct (vertex_frag with "Hx") as "#Hxfrag".
  iInv "Hinv" as (M L N Rp Vp)
    "(>Hauth & >Hlauth & >Hnauth & >Hcont &
      >%HdomL & >%Hrep & >%HRp & >%HVp & Htoks & HM)" "Hclose".
  iDestruct (ghost_map_lookup with "Hauth Hxfrag") as %HMx.
  iMod ("Hclose" with "[Hauth Hlauth Hnauth Hcont Htoks HM]") as "_".
  { iNext. iExists M, L, N, Rp, Vp. by iFrame. }
  iModIntro. iPureIntro. exact (Hrep _ _ HMx).
Qed.

End uf_api.

(* ------------------------------------------------------------------------ *)
(* Re-reading and rewriting the [parent] field of the link record a
   a vertex holds. *)

Section uf_acc.

Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !ghost_varG Σ uf_state,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

Implicit Types x y z : elem.
Implicit Types rc : record.
Implicit Types i j : Z.
Implicit Types γ : uf_names.


Lemma uf_link_field_acc γ h ih rc lp :
  is_uf γ -∗
  vertex γ h ih -∗
  linked γ h rc lp -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ (y : elem) jy,
    ▷ (lp ↦ #y) ∗
    ▷ (vertex γ y jy ∗ same_class γ h y ∗ ⌜(jy < ih)%Z⌝) ∗
    (∀ (z : elem) k, ⌜(k < ih)%Z⌝ -∗ vertex γ z k -∗ same_class γ h z -∗
       lp ↦ #z -∗ |={⊤ ∖ ↑ufN,⊤}=> True).
Proof.
  iIntros "#Hinv #Hh #Hlk".
  iDestruct (vertex_frag with "Hh") as "#Hhfrag".
  iDestruct "Hh" as (lhi lhc) "(_ & #Hhlocs & _ & _)".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_acc with "Hhfrag Hhlocs H") as (c D Rp Vp)
    "(_ & Hcont & Hlc & Hcell & Hframe)".
  (* [h] is linked, so its cell holds a [Link], and the record is [rc],
     since a vertex's link record is fixed once and for all. *)
  destruct c as [rc'|rc'].
  { (* A root's cell owns [h ↪[γ.(uf_link)] None], which [linked] refutes. *)
    iAssert (▷ False)%I with "[Hcell]" as ">[]".
    iNext. iDestruct "Hcell" as "(_ & Htok & _)".
    iApply (linked_not_root with "Hlk Htok"). }
  iDestruct "Hcell" as "(%lp' & >%Hnr & >#Hlk' & Hlf)".
  (* [linked] settles the record and its field's location in one step. *)
  iDestruct (linked_agree with "Hlk' Hlk") as %[-> ->].
  iDestruct "Hlf" as (y jy) "(#HP & Hlp & #Hy & >%Hjy & >#Hsc)".
  iModIntro. iExists y, jy.
  iFrame "Hlp".
  iSplitR; first by iNext; iFrame "Hy Hsc".
  iIntros (z k) "%Hk #Hz #Hhz Hlp".
  iMod ("Hclose" with "[Hcont Hlc Hlp Hframe]") as "_".
  { iNext.
    iApply ("Hframe" with "Hcont Hlc [Hlp]").
    iExists lp. iSplitR; first done. iFrame "Hlk".
    iExists z, k. by iFrame "HP Hlp Hz Hhz". }
  by iModIntro.
Qed.

Lemma uf_link_parent_acc γ h ih rc lp (Φ : elem → iProp Σ) :
  is_uf γ -∗
  vertex γ h ih -∗
  linked γ h rc lp -∗
  ▷ (∀ (y : elem) j, ⌜(j < ih)%Z⌝ -∗ same_class γ h y -∗ vertex γ y j -∗ Φ y) -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ y : elem, ▷ lp ↦ #y ∗ ▷ (lp ↦ #y -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ y).
Proof.
  iIntros "#Hinv #Hh #Hlk HΦ".
  iMod (uf_link_field_acc with "Hinv Hh Hlk")
    as (y jy) "(Hlp & Hy & Hback)".
  iModIntro. iExists y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iDestruct "Hy" as "(#Hyv & #Hhy & %Hjy)".
  iMod ("Hback" $! y jy with "[//] Hyv Hhy Hlp") as "_".
  iModIntro. iApply ("HΦ" with "[//] Hhy Hyv").
Qed.

(* Rerouting a link's [parent] field: the caller must show the vertex
   it is rerouting to is registered, sits below the holder's identifier,
   and is already in the holder's class. *)

Lemma uf_link_parent_set γ h ih rc lp (z : elem) k (Φ : iProp Σ) :
  (k < ih)%Z →
  is_uf γ -∗
  vertex γ h ih -∗
  linked γ h rc lp -∗
  vertex γ z k -∗
  same_class γ h z -∗
  ▷ Φ -∗
  |={⊤,⊤ ∖ ↑ufN}=> ∃ w, ▷ lp ↦ w ∗ ▷ (lp ↦ #z -∗ |={⊤ ∖ ↑ufN,⊤}=> Φ).
Proof.
  iIntros (Hk) "#Hinv #Hh #Hlk #Hz #Hhz HΦ".
  iMod (uf_link_field_acc with "Hinv Hh Hlk")
    as (y jy) "(Hlp & _ & Hback)".
  iModIntro. iExists #y.
  iSplitL "Hlp"; first by iFrame.
  iIntros "!> Hlp".
  iMod ("Hback" $! z k with "[//] Hz Hhz Hlp") as "_".
  by iModIntro.
Qed.

(* ------------------------------------------------------------------------ *)
(* The linearization point of [union]. *)

(* The only things that [compare_and_set_spec]'s premise needs is a
   vertex [a]'s content cell and the value going in is a fresh [Link]
   record pointing at [b].

   Two things carry the proof:
   - The identifier ordering [ib < ia] guarantees that the result is a
     representative function again rather than a cycle: [b]'s
     representative has an identifier at most [b]'s, hence below [a]'s,
     so it cannot be [a] itself.

   - If the cell's current content sits at the same record as the root
     the caller expects, it must be that [Root] is now one line: the
     caller holds [root_val], while a link record's field is owned
     exclusively by its holder's [cell_own], and one location cannot
     carry both ([link_field_root_val_excl]). *)

Lemma uf_cas_link_fupd γ (a b : elem) ia ib lac
    (rce rcn : record) (vexp : val) (P Ψ : iProp Σ) (Φ : bool → iProp Σ) :
  (ib < ia)%Z →
  is_uf γ -∗
  vertex γ a ia -∗
  (∃ li, blockLocs a [li; lac]) -∗
  root_val rce vexp -∗
  vertex γ b ib -∗
  rcn ⤇ {| link_parent := b |} -∗
  (* The caller's linearization resources. They are spent only if the CAS
     succeeds. *)
  P -∗
  (* The hook also yeilds the class fact at this instant. The two
     halves of the ownership of the set (the invariant's and the
     client's) meet here, inside the hook, where the client's atomic
     update is opened. *)
  (* The hook also receives [dethroned] for the state it is asked to move
     to. It is handed over already built, rather than as the [linked]
     witness, because the hook travels: [union_hook_rebase] re-bases a
     hook from one pair of vertices onto another, which [dethroned]
     survives (by [update_class_congr_class]). *)
  ▷ (∀ D (R : elem → elem) (V : elem → val),
       ⌜R a = a⌝ -∗ ⌜R a ≠ R b⌝ -∗ ⌜V a = vexp⌝ -∗
       dethroned γ R.[a -/R/> R b] -∗
       P -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗
       UF γ D R.[a -/R/> R b] V.[a -/R/> V b] ∗ same_class γ a b ∗ Ψ) -∗
  ▷ (∀ res : bool,
       (if res then Ψ else P ∗ rcn ⤇ {| link_parent := b |}) -∗ Φ res) -∗
  |={⊤,⊤ ∖ ↑ufN}=>
    ∃ (c : content) dq1 dq2 t,
      ▷ lac ↦ #c ∗ ▷ blockTag (content_loc c) dq1 t ∗ ▷ blockTag rce dq2 Mut ∗
      ▷ (lac ↦ #(if locations.eqb (content_loc c) rce then CtLink rcn else c) -∗
         blockTag (content_loc c) dq1 t -∗ blockTag rce dq2 Mut -∗
         |={⊤ ∖ ↑ufN,⊤}=> Φ (locations.eqb (content_loc c) rce)).
Proof.
  intros Hab.
  iIntros "#Hinv #Ha (%lai & #Halocs) #Hrv #Hb Hrcn HP Hhook HΦ".
  iDestruct (vertex_frag with "Ha") as "#Hafrag".
  iDestruct (vertex_frag with "Hb") as "#Hbfrag".
  iInv "Hinv" as "H" "Hclose".
  iMod (uf_inv_acc_update with "Hafrag Hbfrag Halocs H") as (c M Rp Vp)
    "(%HMa & %HMb & %HRp & %HVp & Hcont & Hlc & Hcell & Hframe)".
  iAssert (▷ (blockTag (content_loc c) DfracDiscarded Mut ∗
              cell_own γ Rp Vp a ia c))%I with "[Hcell]" as "[#HcP Hcell]".
  { iNext. iDestruct (cell_own_info with "Hcell") as "(_ & [#Hb1 _] & _ & $)".
    iExact "Hb1". }
  iModIntro.
  iExists c, DfracDiscarded, DfracDiscarded, Mut.
  iFrame "Hlc HcP".
  iSplitR; first by iDestruct "Hrv" as (lv) "(_ & $ & _)".
  iNext. iIntros "Hlc' _ _".
  destruct (locations.eqb_spec (content_loc c) rce) as [Heq|Hne]; last first.

  { (* CAS failure: the cell still holds [c]; close untouched and hand the
       fresh record back for the next attempt. *)
    iDestruct "Hframe" as "[Hframe _]".
    iMod ("Hclose" with "[Hcont Hlc' Hcell Hframe]") as "_".
    { iNext. iApply (uf_close_id with "Hframe Hcont Hlc' Hcell"); done. }
    iModIntro. iApply ("HΦ" $! false with "[$HP $Hrcn]"). }

  (* CAS success. The cell's content sits at the record the root
     describes, so it is that root. *)
  destruct c as [rc0|rc0]; simpl in Heq; subst rc0; last first.
  { iDestruct "Hcell" as "(%lp0 & _ & Hlk0 & Hlf)".
    iDestruct (linked_locs with "Hlk0") as "#Hlocs0".
    iDestruct (link_field_root_val_excl with "Hlocs0 Hlf Hrv") as "[]". }
  iDestruct "Hcell" as "(%Hroot & Htokl & #Hrv0)".
  iAssert ⌜Vp a = vexp⌝%I as %Hval.
  { iDestruct "Hrv" as (lv) "(#Hl1 & _ & #Hp1)".
    iDestruct "Hrv0" as (lv') "(#Hl2 & _ & #Hp2)".
    iDestruct (blockLocs_valid with "Hl1 Hl2") as %[= ->].
    by iDestruct (gen_heap.pointsto_agree with "Hp2 Hp1") as %[= ->]. }

  (* The two classes are distinct: [b]'s representative sits at or below
     [b]'s identifier, hence strictly below [a]'s. *)
  assert (Hne' : Rp b ≠ a) by (eapply uf_repr_ne; done).

  (* [a] is linked from now on: its record is fixed, and the registry
     records it.

     The fresh record is taken apart up front: [linked] needs its field's
     location here, [link_field] needs the field itself further down. *)
  iDestruct (link_record_split with "Hrcn") as (lpn) "(#Hlocsn & #HPn & Hlpn)".
  iDestruct "Hframe" as "[_ Hlink]".
  iMod ("Hlink" with "Hlocsn Htokl") as "[#Hlk Hframe]".

  (* The linearization point proper. The hook reports the transition at
     [b]; the invariant is re-closed at [b]'s root, and the two namings of
     the same class agree. *)
  iDestruct (UF_dethroned with "Hcont") as "#Hdeth".
  iDestruct (dethroned_link _ _ a b rcn lpn Hroot with "Hdeth Hlk")
    as "#Hdeth'".
  iMod ("Hhook" $! (dom M) Rp Vp with "[%//] [%] [%//] Hdeth' HP Hcont")
    as "(Hcont & #Hsab & HΨ)".
  { rewrite Hroot. by intros ->. }

  (* Re-close under the merged state: [uf_close_link] carries the whole of
     the state argument. *)
  iDestruct (link_field_intro _ _ _ a b ia ib with "HPn Hlpn Hb Hsab")
    as "Hlf"; first lia.
  iMod ("Hclose" with "[- HΨ HΦ]") as "_".
  { iNext.
    iApply (uf_close_link with "Hframe Hcont Hlc' Hlk Hlf"); done. }
  iModIntro. iApply ("HΦ" $! true with "HΨ").
Qed.

(* ------------------------------------------------------------------------ *)
(* The linearization point of [set]. *)

(* [set] swings the whole content cell to a freshly allocated [Root].

   Abstractly the step moves [V] and nothing else, by [update_class]: the
   whole of [x]'s class takes the new value at once, which is what keeps
   the invariant's [V u = V (R u)] true ([lookup_class_root]). *)

Lemma uf_cas_set_fupd γ (x : elem) i lxc
    (rce rcn : record) (vexp v : val) (P Ψ : iProp Σ) (Φ : bool → iProp Σ) :
  is_uf γ -∗
  vertex γ x i -∗
  (∃ li, blockLocs x [li; lxc]) -∗
  root_val rce vexp -∗
  rcn ⤇ {| root_value := v |} -∗
  (* The caller's linearization resources, spent only if the CAS
     succeeds; a failed CAS hands them back, which is what lets [set]
     retry. The fresh record comes back with them: it was never
     installed. *)
  P -∗
  ▷ (∀ D (R : elem → elem) (V : elem → val),
       ⌜R x = x⌝ -∗ ⌜V x = vexp⌝ -∗
       P -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗
       UF γ D R V.[x -/R/> v] ∗ Ψ) -∗
  ▷ (∀ res : bool,
       (if res then Ψ else P ∗ rcn ⤇ {| root_value := v |}) -∗ Φ res) -∗
  |={⊤,⊤ ∖ ↑ufN}=>
    ∃ c dq1 dq2 t,
      ▷ lxc ↦ #c ∗ ▷ blockTag (content_loc c) dq1 t ∗ ▷ blockTag rce dq2 Mut ∗
      ▷ (lxc ↦ #(if locations.eqb (content_loc c) rce then CtRoot rcn else c) -∗
         blockTag (content_loc c) dq1 t -∗ blockTag rce dq2 Mut -∗
         |={⊤ ∖ ↑ufN,⊤}=> Φ (locations.eqb (content_loc c) rce)).
Proof.
  iIntros "#Hinv #Hx (%lxi & #Hxlocs) #Hrv Hrcn HP Hhook HΦ".
  iDestruct (vertex_frag with "Hx") as "#Hxfrag".
  iInv "Hinv" as "H" "Hclose".
  (* [set] touches no vertex but [x], so there is no second registry entry
     to ask the accessor for: [x] plays the part of both. *)
  iMod (uf_inv_acc_update with "Hxfrag Hxfrag Hxlocs H") as (c M Rp Vp)
    "(%HMx & %_ & %HRp & %HVp & Hcont & Hlc & Hcell & Hframe)".
  iAssert (▷ (blockTag (content_loc c) DfracDiscarded Mut ∗
              cell_own γ Rp Vp x i c))%I with "[Hcell]" as "[#HcP Hcell]".
  { iNext. iDestruct (cell_own_info with "Hcell") as "(_ & [#Hb1 _] & _ & $)".
    iExact "Hb1". }
  iModIntro.
  iExists c, DfracDiscarded, DfracDiscarded, Mut.
  iFrame "Hlc HcP".
  iSplitR; first by iDestruct "Hrv" as (lv) "(_ & $ & _)".
  iNext. iIntros "Hlc' _ _".
  destruct (locations.eqb_spec (content_loc c) rce) as [Heq|Hne]; last first.

  { (* CAS failure: the cell still holds [c]; close untouched and hand the
       fresh record back for the next attempt. *)
    iDestruct "Hframe" as "[Hframe _]".
    iMod ("Hclose" with "[Hcont Hlc' Hcell Hframe]") as "_".
    { iNext. iApply (uf_close_id with "Hframe Hcont Hlc' Hcell"); done. }
    iModIntro. iApply ("HΦ" $! false with "[$HP $Hrcn]"). }

  (* CAS success. As in the linking case, the cell's content sits at the
     very record the expected [Root] describes, so it is that [Root]. *)
  destruct c as [rc0|rc0]; simpl in Heq; subst rc0; last first.
  { iDestruct "Hcell" as "(%lp0 & _ & Hlk0 & Hlf)".
    iDestruct (linked_locs with "Hlk0") as "#Hlocs0".
    iDestruct (link_field_root_val_excl with "Hlocs0 Hlf Hrv") as "[]". }
  iDestruct "Hcell" as "(%Hroot & Htokl & #Hrv0)".
  iAssert ⌜Vp x = vexp⌝%I as %Hval.
  { iDestruct "Hrv" as (lv) "(#Hl1 & _ & #Hp1)".
    iDestruct "Hrv0" as (lv') "(#Hl2 & _ & #Hp2)".
    iDestruct (blockLocs_valid with "Hl1 Hl2") as %[= ->].
    by iDestruct (gen_heap.pointsto_agree with "Hp2 Hp1") as %[= ->]. }

  (* The linearization point proper: [x] is a root, and its class is what
     moves. *)
  iMod ("Hhook" $! (dom M) Rp Vp with "[%//] [%//] HP Hcont") as "[Hcont HΨ]".

  (* The new record's payload is fixed from now on. *)
  iMod (root_val_alloc with "Hrcn") as "#Hrvn".

  (* Re-close under the new value function: [uf_close_set] carries the
     state argument. [x] keeps its root token. *)
  iDestruct "Hframe" as "[Hframe _]".
  iMod ("Hclose" with "[- HΨ HΦ]") as "_".
  { iNext. iApply (uf_close_set with "Hframe Hcont Hlc' Htokl Hrvn"); done. }
  iModIntro. iApply ("HΦ" $! true with "HΨ").
Qed.

End uf_acc.
