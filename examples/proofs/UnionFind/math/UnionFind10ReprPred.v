From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import ghost_map.
From osiris Require Import osiris.

Require Import UnionFind08DataConc UnionFind09SameClass.

(* ------------------------------------------------------------------------ *)
(* Representation predicates. *)
Section repr.
Local Abbreviation elem := record.
Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

(* [vertex γ x i] is the persistent knowledge that [x] is a vertex of the
   structure with identifier [i]. *)
Definition vertex (γ : uf_names) (x : elem) (i : Z) : iProp Σ :=
  ∃ (li lc : locations.loc),
    x ↪[γ.(uf_vert)]□ i ∗
    blockLocs x [li; lc] ∗
    blockTag x DfracDiscarded Mut ∗
    li ↦□ #i.
Global Instance vertex_persistent γ x i : Persistent (vertex γ x i).
Proof. apply _. Qed.

(* ------------------------------------------------------------------------ *)
(* The two shapes of content record. *)

(* A [Root] record, entirely persistently: its single [value] field holds
   [v] and always will. Never written after allocation, so the invariant
   discards its fraction once and hands the result to anyone who loads the
   record. Reading [root.value] then needs no accessor and no open. *)

Definition root_val (rc : record) (v : val) : iProp Σ :=
  ∃ lv : locations.loc,
    blockLocs rc [lv] ∗ blockTag rc DfracDiscarded Mut ∗ lv ↦□ v.

Global Instance root_val_persistent rc v : Persistent (root_val rc v).
Proof. apply _. Qed.

(* Turning a freshly allocated [Root] record into the persistent form the
   invariant keeps. This is a one-way step, and it is where the decision
   that a payload is immutable is actually taken: [set] and [update] CAS a
   whole new record in rather than writing the field, so nothing ever
   needs the exclusive points-to back. *)

Lemma root_val_alloc rc (v : val) :
  rc ⤇ {| root_value := v |} ==∗ root_val rc v.
Proof.
  iIntros "Hrec".
  rewrite /ownRecord /ownBlock /=.
  iDestruct "Hrec" as (ls) "(#Hlocs & #HP & Hxs)".
  iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs") as (lv) "[-> Hlv]".
  iEval (rewrite list_z.singleton_unfold) in "Hlocs".
  iMod (gen_heap.pointsto_persist with "Hlv") as "#Hlv".
  iModIntro. iExists lv. by iFrame "Hlocs HP Hlv".
Qed.

(* A [Link] record held by vertex [h], of identifier [i]. Its [parent]
   field *is* written (that is path compression), so it stays in the
   invariant, owned by [h]'s own entry.

   All it says of the vertex [y] the field holds: [y] is registered, has a
   strictly smaller identifier, and stays inside [h]'s class. Nothing says
   it is an edge; compression reroutes it freely, and that is exactly the
   property compression preserves. *)

Definition link_field (γ : uf_names) (rc : record) (lp : locations.loc)
    (h : elem) (i : Z) : iProp Σ :=
  ∃ (y : elem) jy,
    blockTag rc DfracDiscarded Mut ∗ lp ↦ #y ∗
    vertex γ y jy ∗ ⌜(jy < i)%Z⌝ ∗ same_class γ h y.

(* [linked γ x rc lp]: [x] holds the link record [rc], whose [parent] field
   lives at [lp]. *)

Definition linked (γ : uf_names) (x : elem) (rc : record)
    (lp : locations.loc) : iProp Σ :=
  x ↪[γ.(uf_link)]□ Some rc ∗ blockLocs rc [lp].

Global Instance linked_persistent γ x rc lp : Persistent (linked γ x rc lp).
Proof. apply _. Qed.

(* [linked]'s negation is a resource: a vertex that is still a root
   owns [x ↪[γ.(uf_link)] None] exclusively. *)

Lemma linked_not_root γ x rc lp :
  linked γ x rc lp -∗ x ↪[γ.(uf_link)] None -∗ False.
Proof.
  iIntros "[H1 _] H2".
  by iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hbad _].
Qed.

(* Both halves are timeless. The block map entry is applied explicitly: its
   key is a [loc], which the [elem] type hides from instance search. *)

Global Instance linked_timeless γ x rc lp : Timeless (linked γ x rc lp).
Proof.
  rewrite /linked /blockLocs. apply bi.sep_timeless; first apply _.
  apply bi.sep_timeless; last apply _.
  apply block_map_elem_timeless.
Qed.

Lemma linked_locs γ x rc lp : linked γ x rc lp -∗ blockLocs rc [lp].
Proof. by iIntros "[_ $]". Qed.

Lemma linked_agree γ x rc rc' lp lp' :
  linked γ x rc lp -∗ linked γ x rc' lp' -∗ ⌜rc = rc' ∧ lp = lp'⌝.
Proof.
  iIntros "[H1 #Hl1] [H2 #Hl2]".
  iDestruct (ghost_map_elem_agree with "H1 H2") as %[= ->].
  iDestruct (blockLocs_valid with "Hl1 Hl2") as %[= ->].
  done.
Qed.

(* ------------------------------------------------------------------------ *)

(* [cell_own γ R V x i c] is what the invariant owns and knows about
   vertex [x]'s content cell, given that it currently holds [c].

   The tag of [c] is [x]'s root-status: a cell holds a [Root] iff its
   vertex is its own representative. That equivalence is the entire
   coupling between the structure and its abstract state, and it is what
   makes an atomic read of a content cell a linearization point. *)

Definition cell_own (γ : uf_names) (R : elem → elem) (V : elem → val)
    (x : elem) (i : Z) (c : content) : iProp Σ :=
  match c with
  | CtRoot rc => ⌜R x = x⌝ ∗ x ↪[γ.(uf_link)] None ∗ root_val rc (V x)
  | CtLink rc =>
      ∃ lp, ⌜R x ≠ x⌝ ∗ linked γ x rc lp ∗ link_field γ rc lp x i
  end.

(* Root-ness is anti-monotone. Every CAS swings a [Root] value out of a
   cell, so a vertex linked away never becomes a root again. [linked] is
   the persistent witness of having been linked; a root's cell owns the
   [x ↪[γ.(uf_link)] None] that contradicts it. So a [linked] obtained at
   one instant refutes root-ness at every later one, against whatever
   [cell_own] the invariant holds now.

   This is what the [false] case of [eq] turns on: it must know, while
   still inside [findc y], how a later read of [x.content] will turn out.

   [linked]'s negation is a resource in the invariant, not a proposition a
   reader can carry away, so the refutation is stated against a [cell_own]
   rather than [content_info]. *)

Lemma cell_own_linked γ R V x i c rc lp :
  linked γ x rc lp -∗ cell_own γ R V x i c -∗
  ⌜c = CtLink rc⌝ ∗ cell_own γ R V x i c.
Proof.
  iIntros "#Hlk Hcell". destruct c as [rc'|rc'].
  - (* A root's cell owns the token [linked] refutes. *)
    iDestruct "Hcell" as "(%Hr & Htok & Hval)".
    iDestruct (linked_not_root with "Hlk Htok") as "[]".
  - iDestruct "Hcell" as "(%lp' & %Hr & #Hlk' & Hlf)".
    iDestruct (linked_agree with "Hlk' Hlk") as %[-> ->].
    iSplitR; first done. iExists lp. by iFrame "Hlk' Hlf".
Qed.

(* The invariant-owned footprint of vertex [x]: its content cell, plus
   whatever that cell's current content owns.

   The identifier registry token is deliberately not here. No step on a
   vertex's cell reads or moves it, so keeping it per-vertex made every
   accessor carry it in and out for nothing. It sits in [uf_inv] as one
   [id_tokens] conjunct instead: a single map from which injectivity is
   read off. *)

Definition vertex_own (γ : uf_names) (R : elem → elem) (V : elem → val)
    x i : iProp Σ :=
  ∃ (li lc : locations.loc) (c : content),
    blockLocs x [li; lc] ∗
    lc ↦ #c ∗
    cell_own γ R V x i c.

End repr.

(* ------------------------------------------------------------------------ *)
(* Working with the predicates. *)
Section repr_api.
Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !inG Σ (authR (gsetUR (elem * elem)%type))}.

(* Everything a reader of [x]'s content cell learns about the loaded value
   [c], all of it persistent: a [Root]'s payload is pinned by a persistent
   points-to, a [Link] is pinned to [x] by [linked]. Either way the reader
   may come back to the record later, when [x]'s cell may hold something
   else. *)

Definition content_info (γ : uf_names) (x : elem) (c : content) : iProp Σ :=
  blockTag (content_loc c) DfracDiscarded Mut ∗
  match c with
  | CtRoot rc => ∃ v, root_val rc v
  | CtLink rc => ∃ lp : locations.loc, linked γ x rc lp
  end.

Global Instance content_info_persistent γ x c : Persistent (content_info γ x c).
Proof. destruct c; apply _. Qed.

(* What [content_info] cannot state, since it mentions the abstract state:
   if the loaded value is a [Root], its payload is [x]'s value *at the
   instant of the read*. Available only at a linearization point, but
   persistent, so it outlives the open, which is what [get] needs: [get]
   commits at the content read and only then reads the field. *)

Definition content_val (V : elem → val) (x : elem) (c : content) : iProp Σ :=
  match c with
  | CtRoot rc => root_val rc (V x)
  | CtLink _ => True
  end.

Global Instance content_val_persistent V x c : Persistent (content_val V x c).
Proof. destruct c; apply _. Qed.

(* Read off the cell's own resources, handed straight back: all of
   [content_info] and [content_val] is persistent. A cell holds a [Root]
   exactly when its vertex is its own representative, which is what makes
   an atomic content read a linearization point. *)

Lemma cell_own_info γ R V x i c :
  cell_own γ R V x i c -∗
  ⌜content_root c = true ↔ R x = x⌝ ∗
  content_info γ x c ∗
  content_val V x c ∗
  cell_own γ R V x i c.
Proof.
  rewrite /content_info /content_val /cell_own.
  destruct c as [rc|rc]; simpl.
  - iIntros "(%Hroot & Htok & #Hrv)".
    iAssert (blockTag rc DfracDiscarded Mut) as "#HP".
    { by iDestruct "Hrv" as (lv) "(_ & $ & _)". }
    iSplitR; first by iPureIntro; split.
    iSplitR; [iSplitR; [iExact "HP" | by iExists (V x)] | ].
    iSplitR; first iExact "Hrv".
    by iFrame "Htok Hrv".
  - iIntros "(%lp & %Hroot & #Hlk & Hlf)".
    iDestruct "Hlf" as (y jy) "(#HP & Hlp & #Hy & %Hjy & #Hsc)".
    iSplitR; first by iPureIntro; split; [discriminate | done].
    iSplitR.
    { iFrame "HP". by iExists lp. }
    iSplitR; first done.
    iExists lp. iSplit; first done. iFrame "Hlk".
    iExists y, jy. by iFrame "HP Hlp Hy Hsc".
Qed.

(* A freshly allocated link record, taken apart into the pieces its two
   consumers need: [linked] wants the field's location, [link_field] wants
   the field itself. The CAS that installs the record mints the first
   before its hook runs and builds the second after, so the split has to
   happen once, up front. *)

Lemma link_record_split rc (y : elem) :
  rc ⤇ {| link_parent := y |} -∗
  ∃ lp, blockLocs rc [lp] ∗ blockTag rc DfracDiscarded Mut ∗ lp ↦ #y.
Proof.
  iIntros "Hrec".
  rewrite /ownRecord /ownBlock /=.
  iDestruct "Hrec" as (ls) "(#Hlocs & #HP & Hxs)".
  iDestruct (big_opLZ.big_sepLZ2_singleton_inv_r with "Hxs") as (lp) "[-> Hlp]".
  iEval (rewrite list_z.singleton_unfold) in "Hlocs".
  iExists lp. by iFrame "Hlocs HP Hlp".
Qed.

Lemma link_field_intro γ rc lp (h y : elem) i j :
  (j < i)%Z →
  blockTag rc DfracDiscarded Mut -∗
  lp ↦ #y -∗
  vertex γ y j -∗
  same_class γ h y -∗
  link_field γ rc lp h i.
Proof.
  iIntros (Hj) "#HP Hlp #Hy #Hsc".
  iExists y, j. by iFrame "HP Hlp Hy Hsc".
Qed.

Lemma link_field_root_val_excl γ rc lp h i v :
  blockLocs rc [lp] -∗ link_field γ rc lp h i -∗ root_val rc v -∗ False.
Proof.
  iIntros "#Hlocs Hlf (%lv & #Hlocs' & _ & #Hlv)".
  iDestruct "Hlf" as (y jy) "(_ & Hlp & _)".
  iDestruct (blockLocs_valid with "Hlocs' Hlocs") as %[= ->].
  by iCombine "Hlp Hlv" gives %[Hbad _].
Qed.

(* A registered vertex owns its own [content] cell, so a caller still
   holding that cell (as [make] does for a freshly allocated record) knows
   the vertex is not registered yet. *)

Lemma vertex_own_fresh_ne γ R V x i li lc w :
  blockLocs x [li; lc] -∗ lc ↦ w -∗ vertex_own γ R V x i -∗ False.
Proof.
  iIntros "#Hlocs Hlc Hvo".
  iDestruct "Hvo" as (li' lc' c) "(#Hlocs' & Hlc' & _)".
  iDestruct (blockLocs_valid with "Hlocs' Hlocs") as %[= -> ->].
  iCombine "Hlc Hlc'" gives %[Hbad _].
  exfalso. by eapply dfrac_full_exclusive.
Qed.

(* ------------------------------------------------------------------------ *)
(* The identifier registry. *)

Definition id_tokens (γ : uf_names) (M : gmap elem Z) : iProp Σ :=
  [∗ map] x ↦ i ∈ M, i ↪[γ.(uf_ids)] ().

Lemma id_tokens_injective γ M a w ia iw :
  a ≠ w →
  M !! a = Some ia →
  M !! w = Some iw →
  id_tokens γ M -∗ ⌜ia ≠ iw⌝.
Proof.
  iIntros (Hne HMa HMw) "HM".
  rewrite /id_tokens (big_sepM_delete _ M a ia) //.
  iDestruct "HM" as "[Ha HM]".
  rewrite (big_sepM_delete _ (delete a M) w iw);
    last by rewrite lookup_delete_ne.
  iDestruct "HM" as "[Hw _]".
  destruct (decide (ia = iw)) as [->|Hne']; last by iPureIntro.
  iCombine "Ha Hw" gives %[Hbad _].
  exfalso. by eapply dfrac_full_exclusive.
Qed.

(* [uf_inv]'s big [∗ map] of [vertex_own]s reads off the state only which
   vertices are roots and what value each root holds. So [union], the only
   operation that moves [R], may re-close the untouched vertices once it
   has shown it changed no other vertex's root-status and no surviving
   root's value. *)

Lemma vertex_own_reindex γ (R R' : elem → elem) (V V' : elem → val)
    (M' : gmap elem Z) :
  (∀ w i, M' !! w = Some i → (R' w = w ↔ R w = w)) →
  (∀ w i, M' !! w = Some i → R w = w → V' w = V w) →
  ([∗ map] w ↦ i ∈ M', vertex_own γ R V w i) -∗
  [∗ map] w ↦ i ∈ M', vertex_own γ R' V' w i.
Proof.
  iIntros (HR HV) "HM".
  iApply (big_sepM_impl with "HM").
  iIntros "!>" (w i Hw) "Hvo".
  iDestruct "Hvo" as (li lc c) "(Hlocs & Hlc & Hcell)".
  iExists li, lc, c. iFrame "Hlocs Hlc".
  destruct (HR w i Hw) as [Hfwd Hbwd].
  destruct c as [rc|rc]; simpl.
  - iDestruct "Hcell" as "(%Hroot & $ & Hrv)".
    rewrite (HV w i Hw Hroot). iFrame "Hrv". iPureIntro. by apply Hbwd.
  - iDestruct "Hcell" as "(%lp & %Hroot & Hlk & Hlf)".
    iExists lp. iFrame "Hlk Hlf". iPureIntro. by intros ?%Hfwd.
Qed.

(* ------------------------------------------------------------------------ *)
(* The vertex-level API: [vertex], [is_uf], [content_info], [linked]; never
   block locations or the invariant's internals. *)

Lemma vertex_frag γ x i : vertex γ x i -∗ x ↪[γ.(uf_vert)]□ i.
Proof. iIntros "(% & % & $ & _)". Qed.

Lemma vertex_mut γ x i : vertex γ x i -∗ blockTag x DfracDiscarded Mut.
Proof. iIntros "(% & % & _ & _ & $ & _)". Qed.

Lemma vertex_locs γ x i : vertex γ x i -∗ ∃ li lc, blockLocs x [li; lc].
Proof.
  iIntros "(%li & %lc & _ & Hlocs & _ & _)". iExists li, lc. iExact "Hlocs".
Qed.

End repr_api.
