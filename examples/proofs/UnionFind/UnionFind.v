From osiris Require Import osiris.
From osiris.examples Require Import og_UnionFindBasic.

Require Import UnionFind01Data UnionFind02EmptyCreate UnionFind03Link UnionFind04Compress
  UnionFind06Join UnionFind05IteratedCompression UnionFind07Reachable.

From Stdlib Require Import FunctionalExtensionality.

(* An object in the Union Find data structure is represented by a
   reference, that is, a one-field mutable record. *)
Abbreviation elem := record.

Record link `{Encode A} : Type := { parent : elem }.
Record root `{Encode A} : Type := { rank : Z; value : A }.

(* [root]/[link] are mutable OCaml records, so at the heap level a vertex's
   content (Root/Link) only stores a [record], i.e. a pointer to a *separate*
   heap block holding the record's own fields (rank/value, or parent). *)

(* Matching on a vertex's content is done directly on the loaded value
   (a [VInline "Root"/"Link"] tag wrapping the record pointer): the
   pattern rules read the record fields themselves, so no intermediate
   typed snapshot of the content is needed. *)

Instance root_record : RecordRepr (root (A:=val)) τ[Z; val] Mut :=
  { repr_to_types rt := (rt.(rank), rt.(value));
    types_to_repr := λ k v, {| rank := k; value := v |};
    repr_id := λ '(k, v), eq_refl }.

Instance link_record : RecordRepr (link (A:=val)) τ[elem] Mut :=
  { repr_to_types lk := lk.(parent);
    types_to_repr := λ y, {| parent := y |};
    repr_id := λ y, eq_refl }.

Section UnionFind.

Context `{!osirisGS Σ}.

Implicit Types x y r : elem.
Implicit Types ζ : exn → iProp Σ.
Implicit Types v : val.
Implicit Types D : gset elem.  (* domain *)
Implicit Types F : elem -> elem -> Prop.      (* edges *)
Implicit Types R : elem -> elem.     (* functional view of [is_repr F] *)
Implicit Types V : elem -> val.      (* data stored at the roots *)

(* -------------------------------------------------------------------------- *)

(* [fcupdate], [update_class] and its algebra live in
   UnionFind00Update.v, shared with the concurrent development. *)

(* The predicate [Inv ...] relates the mathematical graph encoded by [D/F] and
   the view that is exposed to the client, which is encoded by [D/R/V].
   In short,
   1. [D/F] form a disjoint set forest, as per [is_dsf];
   2. [R] is included in [is_repr F],
      which means that [R x = y] implies [is_repr F x y],
      or in other words, [R] agrees with [F];
   3. [V] agrees with [R]. *)

Record Inv D F R V : Prop := {
  Inv_dsf  : DSF F D;
  Inv_incl : rel_incl R (Repr F);
  Inv_data : forall x, V x = V (R x)
}.

Local Hint Resolve Inv_dsf Inv_incl Inv_data : core.

Global Instance Inv_idem_R `{Inv D F R V} : Idempotent R.
Proof. destruct Inv0. apply _. Qed.

(* -------------------------------------------------------------------------- *)

(* [ownRecord r qp a] owns the fields of the record block pointed to by [r]. *)

(* [lcontent] is the logical content of a vertex, as exposed to [Mem]/[Inv]
   - i.e. with the rank dropped and the record-pointer indirection hidden.

   [pointsto_M] below is what relates this logical view back to the actual
   two-level heap representation (vertex location -> content -> record block). *)

Inductive lcontent :=
| LRoot : val -> lcontent
| LLink : elem -> lcontent.

(* The heap-level description of a vertex: the location of the record block
   backing it, and its logical content. The memory of the whole structure is
   a single finite map [M : gmap elem vcell]. *)
Local Abbreviation vcell := (record * lcontent)%type.

(* [Mem ...] relates the mathematical graph encoded by [D/F/V] to the memory
   encoded by the finite map [M]:
    1. [M]'s domain is exactly [D], which is what lets us derive that a
       freshly-allocated vertex is not in [D];
    2. the links in [M] coincide with the links in [F];
    3. the data stored at a root in [M] agrees with [V]. The rank is not
       tracked, having dropped the complexity analysis it was for.
   [Mem] never inspects the record-location component of a [vcell]. *)

Definition Mem D F V (M : gmap elem vcell) : Prop :=
  dom M = D ∧
  ∀ x, match M !! x with
       | Some (_, LLink y) => F x y
       | Some (_, LRoot v) => Root F x /\ v = V x
       | None => True
       end.

(* [rec_repr lr lc] owns the record block at [lr] backing a vertex whose
   logical content is [lc]. A root's rank is not tracked, so it stays
   existential; a link stores its parent directly. *)

Definition rec_repr (lr : record) (lc : lcontent) : iProp Σ :=
  match lc with
  | LRoot v => ∃ k : Z, lr ⤇ ({| rank := k; value := v |} : root (A:=val))
  | LLink y => lr ⤇ ({| parent := y |} : link (A:=val))
  end.

(* The content *value* stored in [x]'s ref cell: a [Root]/[Link] tag wrapping
   the pointer [lr] to [x]'s record block. *)

Definition content_of (lr : record) (lc : lcontent) : val :=
  match lc with
  | LRoot _ => VInline "Root" lr
  | LLink _ => VInline "Link" lr
  end.

(* [vertex x lr lc] is the full heap footprint of one vertex [x]: its
   content cell, pointing at the record block [lr], and that block itself. *)

Definition vertex x (lr : record) (lc : lcontent) : iProp Σ :=
  (x ↦ content_of lr lc ∗ rec_repr lr lc)%I.

(* [pointsto_M M] asserts ownership of the whole two-level heap: [vertex x
   lr lc] for each entry [x ↦ (lr, lc)] of [M]. The record locations are
   part of [M] rather than existentially hidden per entry: since [find]
   only mutates record *fields*, the location skeleton [skel M] below is an
   invariant of [find], so [x]'s own record is recoverable by name after
   the recursive call. That is what lets [find] recurse on the *whole*
   structure, with no framing and no reachable-set restriction. *)

Definition pointsto_M (M : gmap elem vcell) : iProp Σ :=
  ([∗ map] x ↦ c ∈ M, vertex x c.1 c.2)%I.

(* The record-location skeleton of the memory. [find]'s inductive spec
   asserts [skel M' = skel M]: path compression rewrites record fields but
   never moves a vertex's record block. *)

Definition skel (M : gmap elem vcell) : gmap elem record := fst <$> M.

Lemma skel_insert M x lr lc lc' :
  M !! x = Some (lr, lc) ->
  skel (<[x:=(lr, lc')]> M) = skel M.
Proof.
  intros HM. rewrite /skel fmap_insert /=.
  apply insert_id. rewrite lookup_fmap HM //.
Qed.

Lemma skel_lookup M M' x lr lc :
  skel M' = skel M ->
  M !! x = Some (lr, lc) ->
  exists lc', M' !! x = Some (lr, lc').
Proof.
  intros Hskel HM.
  assert (Hx : skel M' !! x = Some lr) by (rewrite Hskel /skel lookup_fmap HM //).
  rewrite /skel lookup_fmap in Hx.
  destruct (M' !! x) as [[lr' lc']|]; simplify_eq/=; eauto.
Qed.

(* [UF D R V] is the representation predicate. It is an abstract predicate:
   the client uses this predicate, but does not know how it is defined. It
   quantifies existentially over [F/M], which therefore are not exposed to
   the client. *)

Definition UF D R V : iProp Σ :=
  (∃ F M,
  ⌜ Inv D F R V ⌝ ∗
  ⌜ Mem D F V M ⌝ ∗
  pointsto_M M)%I.

(* -------------------------------------------------------------------------- *)

(* The functions [V] and [R] are compatible with [R]. In other words, every
   member of an equivalence class must have the same image through [V] (see
   [Inv_data]) and through [R]. For this reason, when we wish to update one of
   these functions, we must update it not just at one point, but at a whole
   equivalence class. *)

(* Updating [x]'s class to [V (R x)] is a no-op on [V]. (The [R]
   counterpart, [update_class_R_diag], is in UnionFind00Update.v; this one
   stays here because it reads the invariant.) *)

Lemma update_class_V_diag D F R V x :
  Inv D F R V →
  V.[x -/R/> V (R x)] = V.
Proof.
  intros HI.
  unfold update_class, fcupdate.
  extensionality a.
  case_decide as Hcase; last reflexivity.
  rewrite -Hcase.
  erewrite <- Inv_data; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Exploitation and preservation lemmas for the invariant [Inv]. *)

(* If [x] is in the domain and [r] is its representative, then [r] is in the
   domain and [r] is its own representative. *)

Lemma Inv_root D F R V x r :
  Inv D F R V ->
  x ∈ D ->
  r = R x ->
  r ∈ D /\ R r = r.
Proof.
  intros [Hdsf Hincl Hdata] Hx ->.
  split.
  - eapply sticky_R; eauto.
  - eapply idempotent_R; eauto.
Qed.

(* The invariant is preserved when a new element [r] is created and the
   function [V] is updated at [r] in an arbitrary manner. *)

Lemma Inv_make D F R V D' V' r v :
  Inv D F R V ->
  r ∉ D ->
  D' = D ∪ {[r]} ->
  V' = V.[r -/R/> v] ->
  Inv D' F R V'.
Proof.
  intros [Hdsf Hincl Hdata] Hr -> ->.
  constructor.
  - apply is_dsf_create. exact Hdsf.
  - exact Hincl.
  - intros x.
    apply lookup_class_root, Hdata.
Qed.

(* The invariant is preserved by updating [V] at one equivalence class. *)

Lemma Inv_update_class D F R V x b :
  Inv D F R V ->
  Inv D F R V.[ x -/R/> b].
Proof.
  intros [Hdsf Hincl Hdata].
  constructor; [exact Hdsf | exact Hincl | ].
  intros.
  apply lookup_class_root, Hdata .
Qed.

Lemma unfold_link_R R x y :
  UnionFind03Link.link_R x y R =
  R.[x -/R/> y].
Proof.
  unfold UnionFind03Link.link_R, update_class, fcupdate.
  reflexivity.
Qed.

(* The invariant is preserved by a [link] operation. *)

(* The hypotheses is that the invariant holds and [x] and [y] are distinct
   roots in the domain. The conclusion is that the invariant holds again,
   with [x]'s equivalence class folded into [y]'s (so [y] becomes the new
   representative).

   The original picked whichever of [x]/[y] becomes the new representative
   based on rank, to keep the trees balanced for its complexity bound.
   We drop that as we do not need the logical model to be balanced. *)

Lemma Inv_link D F R V F' R' V' x y :
  Inv D F R V ->
  x ≠ y ->
  x ∈ D ->
  y ∈ D ->
  R x = x ->
  R y = y ->
  F' = UnionFind03Link.link F x y ->
  V' = V.[x -/R/> (V y)] ->
  R' = (UnionFind03Link.link_R x y R) ->
  Inv D F' R' V'.
Proof.
  intros HInv Hneq Hx Hy HRx HRy -> -> ->.
  constructor.
  - eapply is_dsf_link; eauto using R_self_is_root.
  - eapply link_R_link_agree; eauto using R_self_is_root.
  - intros w.
    unfold update_class, fcupdate, link_R.
    case_decide; [ case_decide; reflexivity | ].
    rewrite (idempotent (Idempotent:=@Inv_idem_R _ _ _ _ HInv)).
    case_decide; [ contradiction | ].
    eapply Inv_data; eassumption.
Qed.

(* -------------------------------------------------------------------------- *)

(* Exploitation and preservation lemmas for the invariant [Mem]. *)

(* If [x] is in the domain and is a root, then [M] maps [x] to [LRoot]
   with data [V x] (backed by some record block [r]). *)

Lemma Mem_root D F R V M x :
  Inv D F R V ->
  Mem D F V M ->
  x ∈ D ->
  R x = x ->
  exists lr, M !! x = Some (lr, LRoot (V x)).
Proof.
  intros HInv [Hdom HM] Dx Rxx.
  specialize (HM x).
  destruct (M !! x) as [[lr [w | y]] | ] eqn:Heq.
  - exists lr. destruct HM as [_ Hv]. congruence.
  - exfalso.
    assert (Root F x) by (eapply R_self_is_root; eauto).
    eapply is_root, HM.
  - exfalso. eapply (not_elem_of_dom M). apply Heq. by rewrite Hdom.
Qed.

(* Conversely, if [M] maps [x] to [LRoot], then [x] is a root whose data is
   as predicted by [M]. (We don't track a rank value at all anymore.) *)

Lemma Mem_root_inv D F R V M x lr vx :
  Mem D F V M ->
  M !! x = Some (lr, LRoot vx) ->
  Root F x /\ vx = V x.
Proof.
  intros [Hdom HM] HE.
  specialize (HM x). rewrite HE in HM. exact HM.
Qed.

(* [Mem] is preserved when a new element [r] is created and the function
   [V] is updated at [r] in an arbitrary manner. (The original also
   inserted rank 0 at [r]; since we don't track rank, there's nothing to
   record there beyond [LRoot v].) *)

Lemma Mem_make D F R V D' M r v lr :
  Inv D F R V ->
  Mem D F V M ->
  r ∉ D ->
  D' = D ∪ {[r]} ->
  Mem D' F V.[r -/R/> v] (<[r:=(lr, LRoot v)]>M).
Proof.
  intros HInv [Hdom HM] Hr ->.
  split.
  - rewrite dom_insert_L Hdom. set_solver.
  - intros x. destruct (decide (x = r)) as [->|Hne].
    + rewrite lookup_insert_eq. split.
      * eapply only_roots_outside_D; eauto.
      * by rewrite lookup_update_class.
    + rewrite lookup_insert_ne; [|congruence].
      specialize (HM x).
      destruct (M !! x) as [[lr0 [v0|y]]|] eqn:Heq; [|exact HM|exact HM].
      split; [tauto|].
      assert (Hx : x ∈ D) by (rewrite -Hdom; eapply elem_of_dom_2; eauto).
      unfold update_class, fcupdate. destruct (decide (R x = R r)) as [Heqr|Hner]; [|tauto].
      exfalso.
      assert (HRr : R r = r) by (eapply R_is_identity_outside_D; eauto).
      destruct HInv as [Hdsf Hincl _].
      assert (Hxd : R x ∈ D) by (eapply sticky_R; eauto).
      rewrite Heqr HRr in Hxd. set_solver.
Qed.

(* [Mem] is preserved by installing a link from a root [x] to a root [y]. *)

Lemma Mem_link D F R V V' M x y lr :
  Inv D F R V ->
  Mem D F V M ->
  x ∈ D ->
  x = R x ->
  y = R y ->
  V' = V.[y -/R/> (V y)].[ x -/R/> (V y)] ->
  Mem D (UnionFind03Link.link F x y) V' (<[x:=(lr, LLink y)]>M).
Proof.
  intros HInv [Hdom HM] Hx Hxr Hyr ->.
  split.
  - rewrite dom_insert_L. rewrite Hdom. set_solver.
  - intros a.
    specialize (HM a).
    destruct (decide (x = a)) as [<-|Hne].
    + rewrite lookup_insert_eq. apply link_appears.
    + rewrite lookup_insert_ne; [|congruence].
      destruct (M !! a) as [[lr0 [w|y']]|] eqn:Heq; [|apply link_previous; exact HM | exact HM].
      destruct HM as [Hroota Hva].
      split.
      * apply is_root_link; [exact Hroota | congruence].
      * rewrite {2}Hyr. erewrite update_class_V_diag; last eassumption.
        unfold update_class, fcupdate.
        assert (Hra : R a = a) by (eapply is_root_R_self; eauto).
        case_decide; congruence.
Qed.

(* [Mem] is preserved by installing a direct link from [x] to [y] during
   path compression. *)

Lemma Mem_compress D F V M x y lr :
  Mem D F V M ->
  x ∈ D ->
  Mem D (compress F x y) V (<[x:=(lr, LLink y)]>M).
Proof.
  intros [Hdom HM] Dx.
  split.
  - rewrite dom_insert_L. rewrite Hdom. set_solver.
  - intros a.
    specialize (HM a).
    destruct (decide (x = a)) as [<-|Hne].
    + rewrite lookup_insert_eq. apply compress_x_z.
    + rewrite lookup_insert_ne; [|congruence].
      destruct (M !! a) as [[lr0 [w|y']]|] eqn:Heq;
        [|apply compress_preserves_other_edges; [exact HM | congruence] | exact HM].
      destruct HM as [Hroota Hva]. split; [|exact Hva].
      apply compress_preserves_roots_other_than_x; [congruence | exact Hroota].
Qed.

(* [Mem] is preserved when [V] is updated at one equivalence class and [M]
   is updated at the representative element. *)

Lemma Mem_update D F R V M r x v lr :
  Inv D F R V ->
  Mem D F V M ->
  x ∈ D ->
  r = R x ->
  Mem D F V.[x -/R/> v] (<[r := (lr, LRoot v)]>M).
Proof.
  intros HInv [Hdom HM] Hx ->.
  assert (Hrr : R x ∈ D /\ R (R x) = R x) by (apply (Inv_root _ _ _ _ _ _ HInv Hx eq_refl)).
  destruct Hrr as [Hrd Hrr].
  split.
  - rewrite dom_insert_L. rewrite Hdom. set_solver.
  - intros a.
    specialize (HM a).
    destruct (decide (R x = a)) as [<-|Hne].
    + rewrite lookup_insert_eq. split.
      * eapply R_self_is_root; eauto.
      * assert (Idempotent R). apply (@Inv_idem_R _ _ _ _ HInv).
        rewrite <- lookup_class_root; eauto.
        by rewrite lookup_update_class.
    + rewrite lookup_insert_ne; [|exact Hne].
      destruct (M !! a) as [[lr0 [v0|y]]|] eqn:Heq; [|exact HM|exact HM].
      destruct HM as [Hroota Hva]. split; [exact Hroota|].
      rewrite lookup_update_class_ne; [ assumption | ].
      intros HeqR. apply Hne. rewrite -HeqR.
      eapply is_root_R_self; eauto.
Qed.

(* A vertex with no [LM] entry is, by [Mem]'s domain equation, not in [D]. *)

Lemma Mem_not_elem_of_dom D F V M x :
  Mem D F V M ->
  M !! x = None ->
  x ∉ D.
Proof.
  intros [Hdom _] Heq.
  rewrite -Hdom. eapply not_elem_of_dom_2. exact Heq.
Qed.

(* If [pointsto_M M] and [x ↦ v] are both owned, [x] cannot already be an
   [M] entry (otherwise we'd own [x] twice). Combined with [Mem]'s domain
   equation, this is how we show a freshly-allocated vertex is not in [D]. *)

Lemma pointsto_M_fresh (M : gmap elem vcell) x v :
  pointsto_M M -∗ x ↦ v -∗ ⌜M !! x = None⌝.
Proof.
  iIntros "HM Hx".
  destruct (M !! x) as [c|] eqn:Heq; [|done].
  iExFalso.
  iDestruct (big_sepM_lookup with "HM") as "[Hx' _]"; [exact Heq|].
  iDestruct (ref_pointsto_valid_2 with "Hx Hx'") as %[Hbad _].
  exfalso; eapply dfrac_full_exclusive; exact Hbad.
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [make]. *)

(* [record]/[ERecord] operations need the records they build to fit within
   [max_array_length] *)
Hypothesis Hmax2 : (2 ≤ max_array_length)%Z.

(* The function call [make v] requires [UF D R V]. It returns a new element
   [x]. It updates the data structure to [UF D' R V'], where:
   - [D'] is [D] extended with [x];
   - [V'] is [V] extended with a mapping of [x] to [v]. *)

Definition make_spec make : iProp Σ :=
  □ {{ ∀ D R V; UF D R V }}
  make v : val
  {{ RET (x : elem); UF (D ∪ {[x]}) R V.[x -/R/> v] ∗ ⌜(x ∉ D) ∧ R x = x⌝ }}.

Lemma imp_make η :
  ⊢ EWP (eval η (EAnonFun __make)) {{ make_spec }}.
Proof.
  unfold make_spec.
  iApply imp_EAnon_pers.
  iIntros "!>" (v).
  iIntros (D R V) "HUF".
  iApply imp_please; iNext.
  (* Goal: [ ref (Root { rank = 0; value = v }) ] *)
  imp_ref'.

  simpl.
  iIntros "!>" (x r) "(% & % & Hown & -> & ->) Hr".

  iDestruct "HUF" as (F LM) "(%HInv & %HMem & HptM)".
  iDestruct (pointsto_M_fresh with "HptM Hr") as %HxLM.
  iSplitL.
  - (* extend [LM] at the fresh vertex [x] with its just-allocated record. *)
    iExists F, (<[r:=(x, LRoot v)]>LM).
    iSplit; [iPureIntro; eapply Inv_make; eauto using Mem_not_elem_of_dom |].
    iSplit; [iPureIntro; eapply Mem_make; eauto using Mem_not_elem_of_dom |].
    rewrite /pointsto_M big_sepM_insert; [|exact HxLM].
    simpl. iFrame.
  - iPureIntro. split; [ eapply Mem_not_elem_of_dom; eassumption | ].
    eapply R_is_identity_outside_D; eauto using Mem_not_elem_of_dom.
Qed.

(* -------------------------------------------------------------------------- *)

(* Private lemmas about the representation predicate [pointsto_M]. *)

(* [pointsto_M_acc] gives access to a single [vertex], plus a wand to put a
   vertex back and recover [pointsto_M] at the updated map. *)

Lemma pointsto_M_acc M x lr lc :
  M !! x = Some (lr, lc) ->
  pointsto_M M -∗
    vertex x lr lc ∗
    (∀ lr' lc', vertex x lr' lc' -∗ pointsto_M (<[x:=(lr', lc')]> M)).
Proof.
  intros HM. iIntros "HM".
  iDestruct (big_sepM_insert_acc _ _ _ _ HM with "HM") as "[$ HM]".
  iIntros (lr' lc') "Hv". iApply ("HM" $! (lr', lc') with "Hv").
Qed.

(* A read-only variant. *)

Lemma pointsto_M_acc_same M x lr lc :
  M !! x = Some (lr, lc) ->
  pointsto_M M -∗
    vertex x lr lc ∗ (vertex x lr lc -∗ pointsto_M M).
Proof.
  intros HM. iIntros "HM".
  iDestruct (big_sepM_lookup_acc _ _ _ _ HM with "HM") as "[$ HM]".
  iIntros "Hv". iApply ("HM" with "Hv").
Qed.

(* Every vertex is a reference; physical equality needs to know it. *)

Lemma pointsto_M_is_ref M x :
  x ∈ dom M ->
  pointsto_M M -∗ is_ref x ∗ pointsto_M M.
Proof.
  intros [[lr lc] Hx]%elem_of_dom. iIntros "HM".
  iDestruct (pointsto_M_acc_same _ _ _ _ Hx with "HM") as "([Hx Hrec] & Hback)".
  iDestruct (ref_pointsto_is_ref with "Hx") as "[#$ Hx]".
  iApply "Hback". iFrame.
Qed.

(* A generic two-key variant of [big_sepM_insert_acc]: simultaneous access
   to two distinct entries, with a wand to put both back.
   Needed for expressions like [!x, !y] that read both sides "in parallel". *)

Lemma big_sepM_insert_acc_2 `{Countable K} {A} (Φ : K → A → iProp Σ)
    (m : gmap K A) (i j : K) (x y : A) :
  i ≠ j ->
  m !! i = Some x ->
  m !! j = Some y ->
  ([∗ map] k↦a ∈ m, Φ k a) -∗
    Φ i x ∗ Φ j y ∗
    (∀ (x' y' : A), Φ i x' -∗ Φ j y' -∗ [∗ map] k↦a ∈ <[i:=x']> (<[j:=y']> m), Φ k a).
Proof.
  intros Hne Hi Hj. iIntros "Hm".
  iDestruct (big_sepM_delete _ m i x Hi with "Hm") as "[$ Hm]".
  assert (Hj' : (delete i m) !! j = Some y)
    by (rewrite lookup_delete_ne; [exact Hj | exact Hne]).
  iDestruct (big_sepM_delete _ (delete i m) j y Hj' with "Hm") as "[$ Hm]".
  iIntros (x' y') "Hi Hj".
  rewrite -(insert_delete_eq (<[j:=y']> m) i x').
  rewrite (delete_insert_ne m i j y' Hne).
  rewrite -(insert_delete_eq (delete i m) j y').
  rewrite (big_sepM_insert _ (<[j:=y']> (delete j (delete i m))) i x').
  2: { apply lookup_insert_None.
       split.
       - rewrite lookup_delete_ne; [apply lookup_delete_eq | exact (not_eq_sym Hne)].
       - exact (not_eq_sym Hne). }
  iFrame "Hi".
  rewrite (big_sepM_insert _ (delete j (delete i m)) j y'); [|apply lookup_delete_eq].
  iFrame.
Qed.

(* The two-location variant of [pointsto_M_acc]. *)

Lemma pointsto_M_acc2 M x y rx ry lcx lcy :
  x ≠ y ->
  M !! x = Some (rx, lcx) ->
  M !! y = Some (ry, lcy) ->
  pointsto_M M -∗
    vertex x rx lcx ∗ vertex y ry lcy ∗
    (∀ rx' ry' lcx' lcy',
       vertex x rx' lcx' -∗ vertex y ry' lcy' -∗
       pointsto_M (<[x:=(rx', lcx')]> (<[y:=(ry', lcy')]> M))).
Proof.
  intros Hne Hx Hy. iIntros "HM".
  iDestruct (big_sepM_insert_acc_2 _ _ _ _ _ _ Hne Hx Hy with "HM")
    as "($ & $ & HM)".
  iIntros (rx' ry' lcx' lcy') "Hvx Hvy".
  iApply ("HM" $! (rx', lcx') (ry', lcy') with "Hvx Hvy").
Qed.

(* -------------------------------------------------------------------------- *)

(* Program rules for operating on a vertex. *)

Lemma imp_vertex_load {η E Ψ ζ} x lr lc (e : expr) :
  vertex x lr lc -∗
  impure E (eval η e) Ψ ζ (λ l', ⌜l' = x⌝) -∗
  impure E (eval η (ELoad e)) Ψ ζ
    (λ v : val, ⌜v = content_of lr lc⌝ ∗ vertex x lr lc).
Proof.
  iIntros "[Hx Hrec] He".
  iApply (imp_wand with "[Hx He]").
  { iApply (imp_deref (A:=val) with "Hx He"). }
  iIntros (c) "[-> Hx]". by iFrame.
Qed.

Lemma imp_vertex_read_parent {η E Ψ ζ} x lr y (e : expr) :
  vertex x lr (LLink y) -∗
  impure E (eval η e) Ψ ζ (λ r' : record, ⌜r' = lr⌝) -∗
  impure E (eval η (ERecordAccess e 0)) Ψ ζ
    (λ z : elem, ⌜z = y⌝ ∗ vertex x lr (LLink y)).
Proof.
  iIntros "[Hx Hrec] He".
  iApply (imp_wand with "[Hrec He]").
  { iApply (imp_record_access with "Hrec"); [split; simpl; lia|iExact "He"]. }
  iIntros (z) "[-> Hrec]". by iFrame.
Qed.

Lemma imp_vertex_write_parent {η E Ψ ζ} x lr y (e1 e2 : expr) Φ :
  vertex x lr (LLink y) -∗
  impure E (eval η e1) Ψ ζ (λ r' : record, ⌜r' = lr⌝) -∗
  impure E (eval η e2) Ψ ζ Φ -∗
  impure E (eval η (ERecordSet e1 0 e2)) Ψ ζ
    (λ _ : unit, ∃ z : elem, Φ z ∗ vertex x lr (LLink z)).
Proof.
  iIntros "[Hx Hrec] He1 He2".
  iApply (imp_wand with "[Hrec He1 He2]").
  { iApply (imp_record_update with "Hrec [He1] [He2]");
      [split; simpl; lia|iExact "He1"|iExact "He2"]. }
  iIntros (?) "(%z & HΦ & Hrec)". iExists z. by iFrame.
Qed.

Lemma imp_vertex_read_value {η E Ψ ζ} x lr v (e : expr) :
  vertex x lr (LRoot v) -∗
  impure E (eval η e) Ψ ζ (λ r' : record, ⌜r' = lr⌝) -∗
  impure E (eval η (ERecordAccess e 1)) Ψ ζ
    (λ w : val, ⌜w = v⌝ ∗ vertex x lr (LRoot v)).
Proof.
  iIntros "[Hx (%k & Hrec)] He".
  iApply (imp_wand with "[Hrec He]").
  { iApply (imp_record_access with "Hrec"); [split; simpl; lia|iExact "He"]. }
  iIntros (w) "[-> Hrec]". by iFrame.
Qed.

Lemma imp_vertex_write_value {η E Ψ ζ} x lr v (e1 e2 : expr) Φ :
  vertex x lr (LRoot v) -∗
  impure E (eval η e1) Ψ ζ (λ r' : record, ⌜r' = lr⌝) -∗
  impure E (eval η e2) Ψ ζ Φ -∗
  impure E (eval η (ERecordSet e1 1 e2)) Ψ ζ
    (λ _ : unit, ∃ w : val, Φ w ∗ vertex x lr (LRoot w)).
Proof.
  iIntros "[Hx (%k & Hrec)] He1 He2".
  iApply (imp_wand with "[Hrec He1 He2]").
  { iApply (imp_record_update with "Hrec [He1] [He2]");
      [split; simpl; lia|iExact "He1"|iExact "He2"]. }
  iIntros (?) "(%w & HΦ & Hrec)". iExists w. by iFrame.
Qed.

Lemma imp_vertex_read_rank {η E Ψ ζ} x lr v (e : expr) :
  vertex x lr (LRoot v) -∗
  impure E (eval η e) Ψ ζ (λ r' : record, ⌜r' = lr⌝) -∗
  impure E (eval η (ERecordAccess e 0)) Ψ ζ
    (λ _ : Z, vertex x lr (LRoot v)).
Proof.
  iIntros "[Hx (%k & Hrec)] He".
  iApply (imp_wand with "[Hrec He]").
  { iApply (imp_record_access with "Hrec"); [split; simpl; lia|iExact "He"]. }
  iIntros (w) "[-> Hrec]". by iFrame.
Qed.

Lemma imp_vertex_write_rank {η E Ψ ζ} x lr v (e1 e2 : expr) Φ :
  vertex x lr (LRoot v) -∗
  impure E (eval η e1) Ψ ζ (λ r' : record, ⌜r' = lr⌝) -∗
  impure E (eval η e2) Ψ ζ Φ -∗
  impure E (eval η (ERecordSet e1 0 e2)) Ψ ζ
    (λ _ : unit, ∃ k : Z, Φ k ∗ vertex x lr (LRoot v)).
Proof.
  iIntros "[Hx (%k & Hrec)] He1 He2".
  iApply (imp_wand with "[Hrec He1 He2]").
  { iApply (imp_record_update with "Hrec [He1] [He2]");
      [split; simpl; lia|iExact "He1"|iExact "He2"]. }
  iIntros (?) "(%k' & HΦ & Hrec)". iExists k'. by iFrame.
Qed.

(* -------------------------------------------------------------------------- *)

(* Public lemmas about the representation predicate. *)

(* If [UF D R V] holds, then [R] is idempotent. *)

Theorem UF_idempotent : forall D R V,
  UF D R V -∗ ⌜Idempotent R ⌝.
Proof using.
  iIntros (D R V) "HUF". iDestruct "HUF" as (F LM HInv HMem) "HM". destruct HInv as [Hdsf Hincl Hdata].
  iPureIntro. apply _.
Qed.

(* If [UF D R V] holds, then [R] preserves [D]. *)

Theorem UF_image : forall D R V x, x ∈ D ->
  UF D R V -∗ ⌜ R x ∈ D ⌝.
Proof using.
  iIntros (D R V x Hx) "HUF". iDestruct "HUF" as (F LM HInv HMem) "HM". destruct HInv as [Hdsf Hincl Hdata].
  iPureIntro. eapply sticky_R; eauto.
Qed.

(* If [UF D R V] holds, then [R] is the identity outside of [D]. *)

Theorem UF_identity : forall D R V x, x ∉ D ->
  UF D R V -∗ ⌜ R x = x ⌝.
Proof using.
  iIntros (D R V x Hx) "HUF". iDestruct "HUF" as (F LM HInv HMem) "HM". destruct HInv as [Hdsf Hincl Hdata].
  iPureIntro. eapply R_is_identity_outside_D; eauto.
Qed.

(* If [UF D R V] holds, then [V] is compatible with [R]. *)

Theorem UF_compatible : forall D R V x, x ∈ D ->
  UF D R V -∗ ⌜ V x = V (R x) ⌝.
Proof using.
  iIntros (D R V x Hx) "HUF". iDestruct "HUF" as (F LM HInv HMem) "HM". destruct HInv as [Hdsf Hincl Hdata].
  iPureIntro. apply Hdata.
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [find]. *)

(* Because [find] is a recursive function, we must begin with a specification
   that is amenable to an inductive proof. [find_spec'] states that [find]
   implements the mathematical predicate [bw_ipc]. If [bw_ipc F x d F'] holds,
   which means that path compression at [x] requires [d] steps and changes the
   graph from [F] to [F'], then [find] changes the memory from [M] to some [M']
   that agrees with [F']. Furthermore, the value [r] returned by [find] is the
   representative of [x]. *)


Definition find_spec' ( e : elem) (m : microvx) : iProp Σ :=
  ∀ d D R F F' M V,
    ⌜Inv D F R V⌝ -∗
    ⌜Mem D F V M⌝ -∗
    ⌜e ∈ D⌝ -∗
    ⌜bw_ipc F e d F'⌝ -∗
    pointsto_M M -∗
    EWP m {{ (x : elem), ∃ M',
      ⌜x = R e⌝ ∗ ⌜skel M' = skel M⌝ ∗ pointsto_M M' ∗ ⌜Mem D F' V M'⌝ }}.

(* -------------------------------------------------------------------------- *)

(* Pure lemmas backing [find_spec_inductive]'s reasoning about the iterated
   path compression derivation [bw_ipc]. *)

(* At a root, compression does nothing. *)

Lemma bw_ipc_at_root F e d F' :
  Root F e ->
  bw_ipc F e d F' ->
  F' = F.
Proof.
  intros * His_root Hbw_ipc.
  inversion Hbw_ipc; subst; [reflexivity|].
  exfalso; eapply His_root; eauto.
Qed.

(* At a link [F e y], the derivation necessarily steps to [y]: it recurses
   on [y] (an element of [D]) and finishes by compressing [e] directly to
   the representative [R y]. *)

Lemma bw_ipc_at_link D F R V e y d F' :
  Inv D F R V ->
  F e y ->
  bw_ipc F e d F' ->
  y ∈ D /\
  ∃ l Fres, bw_ipc F y l Fres /\ F' = compress Fres e (R y).
Proof.
  intros * HInv Hlc Hbw_ipc.
  pose proof (Inv_dsf _ _ _ _ HInv) as Hdsf.
  split. { destruct Hdsf. eapply confined, Hlc. }
  inversion Hbw_ipc as [? Hroot | ]; subst.
  - exfalso. apply (is_root y), Hlc.
  - assert (y0 = y) as -> by (destruct Hdsf; eapply functional; eauto).
    assert (z = R y) as -> by
      (eapply functional_is_repr; [exact Hdsf | eassumption | eapply (Inv_incl _ _ _ _ HInv)]).
    eauto 10.
Qed.

(* Compression starting at [e]'s parent [y] never reaches back to [e],
   so [e]'s entry is unchanged. *)

Lemma link_untouched_by_ipc D F V M M' Fres e re y l :
  DSF F D ->
  F e y ->
  bw_ipc F y l Fres ->
  Mem D Fres V M' ->
  skel M' = skel M ->
  M !! e = Some (re, LLink y) ->
  M' !! e = Some (re, LLink y).
Proof.
  intros Hdsf Hlc Hipc HMem' Hskel Heq.
  destruct (skel_lookup _ _ _ _ _ Hskel Heq) as (lc' & Heq').
  assert (HF0ey : Fres e y).
  { eapply (bw_ipc_outside_unchanged _ _ _).
    - apply Hipc.
    - intro Hc. eapply edge_no_return_path. exact Hdsf. exact Hlc. exact Hc.
    - apply Hlc. }
  destruct HMem' as [_ HMem']. specialize (HMem' e). rewrite Heq' in HMem'.
  destruct lc' as [v2|y2].
  { exfalso. eapply HMem'. apply HF0ey. }
  rewrite Heq'. repeat f_equal.
  assert (HyD : y ∈ D) by (destruct Hdsf; eapply confined; eauto).
  assert (DSF Fres D) as [_ Hdsf0 _]
    by (eapply is_dsf_bw_ipc; eauto).
  eapply functional; eauto.
Qed.

(* One step up the forest does not change the representative. *)

Lemma R_of_parent : forall D F R V e y,
  Inv D F R V ->
  F e y ->
  R e = R y.
Proof.
  intros * [Hdsf Hincl _] Hlc.
  eapply is_equiv_incl_same_R.
  - apply Hdsf.
  - exact Hincl.
  - eapply path_is_equiv; eauto using rtc_l, rtc_refl.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma find_spec_inductive η :
  ▷ in_env "find" (λ find, □ iSpec τ[elem] find find_spec') η -∗
  (* [fun_spec.] disambiguates the program-logic (iProp-valued) predicate
     from its pure-logic (Prop-valued) namesake. *)
  fun_spec.predicate_over_function_body τ[elem] find_spec' η
      (EAnonFun (AnonFun "x" (EMatch (ELoad (EPath ["x"])) __find_branches))).
Proof.
  iIntros "#IH".
  iIntros (e).
  unfold find_spec' at 2.
  iIntros (d D R F F' M V HInv HMem Hin Hbw_ipc) "HM".
  iApply imp_please; iNext.
  (* Read [e]'s content cell with the *read-only* accessor: since [find]
     recurses on the whole structure, [e] stays in the heap and is put back
     unchanged by [Hback]. [Hlc] is the [Mem] fact about [e]'s content. *)
  destruct (M !! e) as [[re lc]|] eqn:Heq;
    pose proof (proj2 HMem e) as Hlc; rewrite Heq in Hlc;
    [|destruct (Mem_not_elem_of_dom _ _ _ _ _ HMem Heq Hin)].
  iDestruct (pointsto_M_acc_same _ _ _ _ Heq with "HM") as "(Hv & Hback)".

  (* Goal: [ match !x with ... ] *)
  imp_match val with "[Hv]".
  { iApply (imp_vertex_load with "Hv"). imp_path. }
  iIntros "[-> Hv]".
  (* The loaded value is [content_of re lc]: matching is decided by [lc],
     so destruct it first; in each case the branches process
     deterministically (the non-matching one is refuted outright). *)
  destruct lc as [v|y]; simpl.

  { (* [Root _ -> x]: [e] is its own representative *)
    next_branch.
    imp_path.
    iDestruct ("Hback" with "Hv") as "$". iPureIntro.
    destruct Hlc as [His_root HV].
    split_and!.
    - symmetry. eapply is_root_R_self; eauto.
    - reflexivity.
    - assert (F' = F) as -> by (eapply bw_ipc_at_root; eauto).
      assumption. }

  { (* [Link ({ parent = y } as link) -> ...]: recurse on [e]'s parent [y],
       bound by the pattern itself, then compress [e]'s record in place. *)
    next_branch.
    (* The Root branch is refuted; matching the [Link] record pattern
       reads the [parent] field, so expose the record ownership before
       walking it. *)
    iDestruct "Hv" as "[He Hre]". simpl.
    next_branch.

    (* Decompose the iterated-compression derivation at [e]: it steps to [y]
       (an element of [D]) and recurses, with [F' = compress F0 e (R y)]. *)
    destruct (bw_ipc_at_link _ _ _ _ _ _ _ _ HInv Hlc Hbw_ipc)
      as (HyD & l0 & F0 & Hipc0 & HFeq0).
    iDestruct ("Hback" with "[$He $Hre]") as "HM".

    (* Goal: [ let z = find y in ... ] *)
    iApply (imp_ELet_var (B:=elem) with "[HM]").
    { iApply (imp_EApp τ[elem]). { imp_path. } { imp_path. }
      simpl. iIntros (x) "-> %m Hm".
      iApply ("Hm" with "[%//] [%//] [%//] [%//] HM"). }
    simpl.
    iIntros (z) "(%M2' & -> & %Hskel & HM' & %HMem')".
    (* Comparing [R y] with [y] needs both to be references. *)
    iDestruct (pointsto_M_is_ref _ y with "HM'") as "[#Hy HM']".
    { rewrite (proj1 HMem'). exact HyD. }
    iDestruct (pointsto_M_is_ref _ (R y) with "HM'") as "[#HRy HM']".
    { rewrite (proj1 HMem'). destruct HInv. eapply sticky_R; eauto. }

    (* The recursion never touches [e] ([e] is not reachable from [y]), so [e]
       is still a [Link] to [y] in the returned [M2'], with the same record
       [re] (by skeleton preservation). *)
    assert (Heq2 : M2' !! e = Some (re, LLink y))
      by (eapply link_untouched_by_ipc; eauto).

    iDestruct (pointsto_M_acc with "HM'") as "(Hv & Hback)".
    { eassumption. }

    (* Goal: [ if z != y then ... else ...; z ] *)
    iApply (imp_ESeq with "[-]").
    imp_if.
    { set_postcondition (λ b, ⌜b = negb (locations.eqb (R y) y)⌝)%I.
      iApply imp_EBoolNeg.
      iApply (imp_EOpPhysEq_ref _ _ _ (λ r, ⌜r = R y⌝)%I (λ r, ⌜r = y⌝)%I
        with "[] []").
      { iApply imp_wand. imp_path. iIntros (?) "->". by iFrame "#". }
      { iApply imp_wand. imp_path. iIntros (?) "->". by iFrame "#". }
      iIntros "!>" (l1 l2) "-> -> //". }

    + (* [R y ≠ y]: perform [link.parent <- R y]. *)
      iIntros "%Heqb".
      destruct (locations.eqb_spec (R y) y) as [HRy|HRy]; first discriminate.
      iApply (imp_wand with "[Hv]").
      { iApply (imp_vertex_write_parent with "Hv [] []"); [imp_path|imp_path]. }
      iIntros (?) "(%w & -> & Hv)".
      iApply ("Hback" $! re (LLink (R y)) with "Hv").

    + (* [R y = y]: no write; [e]'s record already points to [y = R y]. *)
      iIntros "%Heqb".
      destruct (locations.eqb_spec (R y) y) as [HRy|HRy]; last discriminate.
      rewrite HRy. iApply ("Hback" $! re (LLink y) with "Hv").

    + (* Continuation: [e] and [y] share a representative, and the updated heap
         is a [Mem] for [F' = compress F0 e (R y)] directly by [Mem_compress]. *)
      iIntros "HMfinal". imp_path.
      iExists (<[e:=(re, LLink (R y))]> M2'). iFrame "HMfinal". iPureIntro.
      split_and!.
      { symmetry. eapply R_of_parent; eauto. }
      { erewrite skel_insert; [exact Hskel | exact Heq2]. }
      rewrite HFeq0. apply Mem_compress; [exact HMem' | exact Hin]. }
Qed.

Definition find_spec find : iProp Σ :=
  □ {{ ∀ D R V; ⌜e ∈ D⌝ ∗ UF D R V }}
  find e : elem
  {{ RET (x : elem); ⌜x = R e⌝ ∗ UF D R V }}.

Lemma find_proof :
  ∀ find, □ iSpec τ[elem] find find_spec' -∗ find_spec find.
Proof.
  iIntros (find) "#Hspec' !>".
  iApply (iSpec_mono with "Hspec'").
  iIntros (x m) "Hspec".
  unfold find_spec', tapp.
  iIntros (D R V) "(%Hin & HUF)".
  iDestruct "HUF" as "(%F & %LM & %HInv & %HMem & Hpointsto)".
  pose proof (Inv_dsf D F R V HInv) as Hdsf.
  edestruct (ipc_defined D F x Hdsf) as (d & F' & Hipc).
  iSpecialize ("Hspec" with "[//] [//] [//] [//] Hpointsto").
  iApply (imp_wand with "Hspec").
  iIntros (y) "(%M' & -> & %Hskel & Hpointsto & %HMem')".
  iSplit; first done.
  iFrame "∗%". iPureIntro.
  split; eauto.
  eapply is_dsf_bw_ipc; eauto.
  eapply bw_ipc_preserves_RF_agreement; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Verification of [is_representative]. *)

(* [is_representative x] reads [x]'s content cell and reports whether it is a
   [Root]. Being a root is exactly being one's own representative, so the
   answer is [bool_decide (R x = x)]. No call to [find] is involved, and the
   data structure is left untouched. *)

Definition is_representative_spec is_representative : iProp Σ :=
  □ {{ ∀ D R V; ⌜e ∈ D⌝ ∗ UF D R V }}
  is_representative e : elem
  {{ RET (b : bool); ⌜b = bool_decide (R e = e)⌝ ∗ UF D R V }}.

Lemma is_representative_proof η :
  ⊢ EWP (eval η (EAnonFun __is_representative)) {{ is_representative_spec }}.
Proof.
  unfold is_representative_spec.
  iApply imp_EAnon_pers.
  iIntros "!>" (e).
  iIntros (D R V) "(%Hin & HUF)".
  iDestruct "HUF" as (F M) "(%HInv & %HMem & HM)".
  iApply imp_please; iNext.
  destruct (M !! e) as [[re lc]|] eqn:Heq;
    pose proof (proj2 HMem e) as Hlc; rewrite Heq in Hlc;
    [|destruct (Mem_not_elem_of_dom _ _ _ _ _ HMem Heq Hin)].
  iDestruct (pointsto_M_acc_same _ _ _ _ Heq with "HM") as "(Hv & Hback)".

  (* Goal: [ match !x with ... ] *)
  imp_match val with "[Hv]".
  { iApply (imp_vertex_load with "Hv"). imp_path. }
  iIntros "[-> Hv]".
  destruct lc as [v|y]; simpl.

  { (* [Root _ -> true]: a root is its own representative. *)
    next_branch.
    iApply (imp_wand _ _ _ _ (λ b : bool, ⌜b = true⌝)%I with "[]").
    { imp_step. }
    iIntros (b) "->".
    iSplitR.
    { iPureIntro. symmetry. apply bool_decide_eq_true_2.
      destruct Hlc as [Hroot _]. eapply is_root_R_self; eauto. }
    iExists F, M. iFrame "%". iApply ("Hback" with "Hv"). }

  { (* [Link _ -> false]: [e] has a parent, so it is not a root, and
       [R e = e] would make it one. *)
    next_branch.
    next_branch.
    iApply (imp_wand _ _ _ _ (λ b : bool, ⌜b = false⌝)%I with "[]").
    { imp_step. }
    iIntros (b) "->".
    iSplitR.
    { iPureIntro. symmetry. apply bool_decide_eq_false_2.
      intros HRe.
      assert (Hroot : Root F e) by (eapply R_self_is_root; eauto).
      eapply Hroot; eauto. }
    iExists F, M. iFrame "%". iApply ("Hback" with "Hv"). }
Qed.

(* -------------------------------------------------------------------------- *)

Definition get_spec get : iProp Σ :=
  □ {{ ∀ D R V; ⌜e ∈ D⌝ ∗ UF D R V }}
  get e : elem
  {{ RET (x : val); ⌜x = V e⌝ ∗ UF D R V }}.

Lemma get_proof η :
  in_env "find" find_spec η -∗
  EWP (eval η (EAnonFun __get)) {{ get_spec }}.
Proof.
  iIntros "#Hfind".
  unfold get_spec.
  iApply imp_EAnon_pers.
  iIntros "!>" (e).
  iIntros (D R V) "(%Hin & HUF)".
  iApply imp_please; iNext.

  iApply (imp_ELet_var (B:=elem) with "[HUF]").
  { imp_app τ[elem].
    iIntros "Hm". iApply ("Hm" with "[$HUF //]"). }
  iIntros (?) "(-> & HUF)".
  iPoseProof (UF_image with "HUF") as "%HRD"; first eassumption.
  iPoseProof (UF_idempotent with "HUF") as "%HRidem".
  iPoseProof (UF_compatible with "HUF") as "%HRV"; first apply Hin.
  iDestruct "HUF" as (F M HI HM) "HM".
  assert (exists lr, M !! (R e) = Some (lr, LRoot (V (R e)))) as (lr & Heq).
  { eapply Mem_root; eauto using idempotent. }
  iDestruct (pointsto_M_acc_same _ _ _ _ Heq with "HM") as "(Hv & Hback)".

  imp_match val with "[Hv]".
  { iApply (imp_vertex_load with "Hv"). imp_path. }
  iIntros "(-> & Hv)".
  simpl.
  (* [Root { value = v; _ } -> v]: matching reads the [value] field, so
     the record ownership must be exposed before entering the branch. *)
  iDestruct "Hv" as "[He Hlr]". iDestruct "Hlr" as (k) "Hlr".
  next_branch.
  imp_path.
  iSplit. { iPureIntro. by rewrite HRV. }
  iSpecialize ("Hback" with "[$He Hlr]").
  { iExists k. iFrame. }
  iFrame "∗%".
Qed.

(* -------------------------------------------------------------------------- *)

Definition set_spec set : iProp Σ :=
  □ {{ ∀ D R V; ⌜e ∈ D⌝ ∗ UF D R V }}
  set e v : elem val
  {{ RET (x : unit); UF D R V.[ e -/R/> v] }}.

Lemma set_proof η :
  in_env "find" find_spec η -∗
  EWP (eval η (EAnonFun __set)) {{ set_spec }}.
Proof.
  iIntros "#Hfind".
  unfold set_spec.
  iApply imp_EAnon_pers.
  iIntros "!>" (e v).
  iIntros (D R V) "(%Hin & HUF)".
  iApply imp_please; iNext.

  iApply (imp_ELet_var (B:=elem) with "[HUF]").
  { imp_app τ[elem].
    iIntros "Hm". iApply ("Hm" with "[$HUF //]"). }
  iIntros (?) "(-> & HUF)".
  iPoseProof (UF_image with "HUF") as "%HRD"; first eassumption.
  iPoseProof (UF_idempotent with "HUF") as "%HRidem".
  iPoseProof (UF_compatible with "HUF") as "%HRV"; first apply Hin.
  iDestruct "HUF" as (F M HI HM) "HM".
  assert (exists lr, M !! (R e) = Some (lr, LRoot (V (R e)))) as (lr & Heq).
  { eapply Mem_root; eauto using idempotent. }
  iDestruct (pointsto_M_acc _ _ _ _ Heq with "HM") as "(Hv & Hback)".

  imp_match val with "[Hv]".
  { iApply (imp_vertex_load with "Hv"). imp_path. }
  iIntros "(-> & Hv)".
  next_branch.

  { iApply (imp_wand with "[Hv]").
    { iApply (imp_vertex_write_value with "Hv [] []"); [imp_path|imp_path]. }
    iIntros ([]) "(% & -> & Hv) /=".

    iSpecialize ("Hback" $! lr (LRoot _) with "Hv").
    iFrame "Hback". iPureIntro.
    eauto using Inv_update_class, Mem_update. }
Qed.

(* -------------------------------------------------------------------------- *)

Definition union_spec union : iProp Σ :=
  □ {{ ∀ D R V; ⌜x ∈ D⌝ ∗ ⌜y ∈ D⌝ ∗ UF D R V }}
  union x y : elem elem
  {{ RET z; UF D R.[y -/R/> z].[x -/R/> z] V.[y -/R/> (V z)].[x -/R/> (V z)] ∗
              ⌜z = R x ∨ z = R y⌝ }}.

Lemma union_proof η :
  in_env "find" find_spec η -∗
  EWP (eval η (EAnonFun __union)) {{ union_spec }}.
Proof.
  iIntros "#Hfind".
  unfold union_spec.
  iApply imp_EAnon_pers.
  iIntros "!>" (x y).
  iIntros (D R V) "(%Hin_x & %Hin_y & HUF)".
  iApply imp_please; iNext.
  iApply (imp_ELet_var (B:=elem) with "[HUF]").
  { imp_app τ[elem].
    iIntros "Hm". iApply ("Hm" with "[$HUF //]"). }
  iIntros (?) "(-> & HUF)".
  iApply (imp_ELet_var (B:=elem) with "[HUF]").
  { imp_app τ[elem].
    iIntros "Hm". iApply ("Hm" with "[$HUF //]"). }
  iIntros (?) "(-> & HUF)".

  (* Comparing [R x] with [R y] needs both to be references. *)
  iAssert (is_ref (R x) ∗ is_ref (R y))%I as "#[HRx HRy]".
  { iDestruct "HUF" as (F M HI HM) "HM".
    assert (R x ∈ dom M ∧ R y ∈ dom M) as [HRxM HRyM].
    { rewrite (proj1 HM). destruct HI. split; eapply sticky_R; eauto. }
    iDestruct (pointsto_M_is_ref _ _ HRxM with "HM") as "[$ HM]".
    iDestruct (pointsto_M_is_ref _ _ HRyM with "HM") as "[$ HM]". }
  imp_if.
  { set_postcondition (λ b, ⌜b = locations.eqb (R x) (R y)⌝)%I.
    iApply (imp_EOpPhysEq_ref _ _ _ (λ r, ⌜r = R x⌝)%I (λ r, ⌜r = R y⌝)%I
      with "[] []").
    { iApply imp_wand. imp_path. iIntros (?) "->". by iFrame "#". }
    { iApply imp_wand. imp_path. iIntros (?) "->". by iFrame "#". }
    iIntros "!>" (??) "-> -> //". }

  { iIntros "%Heq".
    iClear "HRx HRy".
    imp_path.
    iSplit; last (iPureIntro; tauto).
    iDestruct "HUF" as "(%F & %M & %HI & %HM & Hpts)".
    destruct (locations.eqb_spec (R x) (R y)) as [HReq|HRne]; [|congruence].
    rewrite {1 3} HReq.
    rewrite !update_class_R_diag.
    erewrite !update_class_V_diag; try eassumption.
    iFrame "∗%". }

  iIntros "%Hneq".
  iPoseProof (UF_image with "HUF") as "%HRD_x"; first apply Hin_x.
  iPoseProof (UF_image with "HUF") as "%HRD_y"; first apply Hin_y.
  iPoseProof (UF_idempotent with "HUF") as "%HRidem".
  iDestruct "HUF" as (F M HI HM) "HM".
  assert (exists rx, M !! (R x) = Some (rx, LRoot (V (R x)))) as (rx & Heq_x).
  { eapply Mem_root; eauto using idempotent. }
  assert (exists ry, M !! (R y) = Some (ry, LRoot (V (R y)))) as (ry & Heq_y).
  { eapply Mem_root; eauto using idempotent. }

  destruct (locations.eqb_spec (R x) (R y)) as [HReq|HRne]; [ congruence | ].

  iPoseProof (pointsto_M_acc2 with "HM") as "(Hvx & Hvy & Hback)"; eauto.

  imp_match (val * val)%type with "[Hvx Hvy]".
  { imp_tuple with "[Hvx] [Hvy]".
    - iApply (imp_vertex_load with "Hvx"). imp_path.
    - iApply (imp_vertex_load with "Hvy"). imp_path. }

  destruct a as [??].
  iIntros "((-> & Hvx) & (-> & Hvy))".

  (* The first branch destructures the two [Root] records inside the
     pattern itself: matching must read the rank fields from the record
     blocks, so the branch is processed with the Iris-level pattern rules
     ([next_branch]); the field sub-patterns go back down to the pure
     judgement ([fpatterns]). *)
  iDestruct "Hvx" as "[Hx Hrx]". iDestruct "Hrx" as (kx) "Hrx".
  iDestruct "Hvy" as "[Hy Hry]". iDestruct "Hry" as (ky) "Hry".
  next_branch.
  iAssert (vertex (R x) rx (LRoot (V (R x)))) with "[Hx Hrx]" as "Hvx".
  { iFrame "Hx". iExists kx. iFrame. }
  iAssert (vertex (R y) ry (LRoot (V (R y)))) with "[Hy Hry]" as "Hvy".
  { iFrame "Hy". iExists ky. iFrame. }

  iApply (imp_EIfThenElse).
  { iApply imp_EOpLt_Z_weak. imp_path. imp_path. }
  iIntros ([|]) "_".

  { (* [R x]'s record block is replaced wholesale: take the content cell out
       of the vertex and drop the old record block. *)
    iDestruct "Hvx" as "[Hx _]".
    iApply (imp_ESeq with "[Hx]").
    { (* Goal:= [ x := Link { parent = y } ] *)
      imp_store' (R x) $! (∃ (r : record), r ⤇ {| parent := R y |} ∗ R x ↦ VInline "Link" r)%I.
      iIntros "!>" (r) "HΦ Hl".
      iDestruct "HΦ" as (z) "(Hown & ->) /=".
      iExists r. iFrame. }
    iIntros "(% & Hown_link & Hlink)".
    iSpecialize ("Hback" $! _ _ (LLink (R y)) with "[$Hlink $Hown_link] Hvy").
    imp_path. iSplit; last (iPureIntro; tauto).

    rewrite update_class_R_diag. erewrite update_class_V_diag; last eassumption.
    (* Goal: prove ownership of a [UF] data structure with the class of [x]
       updated to [R y]: [UF D R.[x -/R/> R y] V.[x -/R/> V (R y)]. *)
    unfold UF. iFrame "Hback".
    iExists (UnionFind03Link.link F (R x) (R y)).
    iPureIntro.
    rewrite (insert_id M); last assumption.
    split.
    - eapply Inv_link; eauto using idempotent.
      rewrite update_class_root; eauto.
      rewrite unfold_link_R update_class_root; eauto.
    - eapply Mem_link; eauto. by rewrite idempotent. by rewrite idempotent.
      rewrite !update_class_root; eauto.
      erewrite update_class_V_diag; eauto. }

  iApply imp_EIfThenElse. { iApply imp_EOpGt_Z_weak. imp_path. imp_path. }
  iIntros ([|]) "_".

   { (* Same record-block replacement, this time on [R y]'s side. *)
    iDestruct "Hvy" as "[Hy _]".
    iApply (imp_ESeq with "[Hy]").
    { imp_store' (R y) $! (∃ (r : record), r ⤇ {| parent := R x |} ∗ R y ↦ VInline "Link" r)%I.
      iIntros "!>" (r) "HΦ Hl".
      iDestruct "HΦ" as (z) "(Hown & ->)".
      simpl. iExists r. iFrame. }
    iIntros "(%r & Hown_link & Hlink)".
    iSpecialize ("Hback" $! _ r _ (LLink (R x))
      with "Hvx [$Hlink $Hown_link]").
    imp_path. iSplit; last (iPureIntro; tauto).

    rewrite update_classes_comm update_class_R_diag.
    rewrite update_classes_comm; erewrite update_class_V_diag; last eassumption.
    (* Goal: prove ownership of a [UF] data structure with the class of [y]
       updated to [R x]: [UF D R.[y -/R/> R x] V.[y -/R/> V (R x)]. *)
    unfold UF. iFrame "Hback".
    iExists (UnionFind03Link.link F (R y) (R x)).
    iPureIntro.
    rewrite insert_insert_ne; last (assumption).
    rewrite (insert_id M); last assumption.
    split.
    - eapply (Inv_link _ _ _ _ _ _ _ (R y)); eauto using idempotent.
      rewrite update_class_root; eauto.
      rewrite unfold_link_R update_class_root; eauto.
    - eapply Mem_link; eauto. by rewrite idempotent. by rewrite idempotent.
      rewrite !update_class_root; eauto.
      erewrite update_class_V_diag; eauto. }

  iDestruct "Hvy" as "[Hy _]".
  iApply (imp_ESeq with "[Hy]").
    { imp_store' (R y) $! (∃ (r : record), r ⤇ {| parent := R x |} ∗ R y ↦ VInline "Link" r)%I.
      iIntros "!>" (r) "HΦ Hl".
      iDestruct "HΦ" as (z) "(Hown & ->)".
      simpl. iExists r. iFrame. }
    iIntros "(%r & Hown_link & Hlink)".
    iApply (imp_ESeq with "[Hvx]").
    { iApply (imp_vertex_write_rank with "Hvx [] []"); [imp_path|imp_arith]. }
    iIntros "(% & % & Hvx) /=".
    iSpecialize ("Hback" $! _ r _ (LLink (R x)) with "Hvx [$Hlink $Hown_link]").
    imp_path. iSplit; last (iPureIntro; tauto).

    rewrite update_classes_comm update_class_R_diag.
    rewrite update_classes_comm; erewrite update_class_V_diag; last eassumption.
    (* Goal: prove ownership of a [UF] data structure with the class of [y]
       updated to [R x]: [UF D R.[y -/R/> R x] V.[y -/R/> V (R x)]. *)
    unfold UF. iFrame "Hback".
    iExists (UnionFind03Link.link F (R y) (R x)).
    iPureIntro.
    rewrite insert_insert_ne; last (assumption).
    rewrite (insert_id M); last assumption.
    split.
    - eapply (Inv_link _ _ _ _ _ _ _ (R y)); eauto using idempotent.
      rewrite update_class_root; eauto.
      rewrite unfold_link_R update_class_root; eauto.
    - eapply Mem_link; eauto.
      by rewrite idempotent. by rewrite idempotent.
      rewrite !update_class_root; eauto.
      erewrite update_class_V_diag; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Module-level specification. *)

Definition UnionFind_names : gset var :=
  {["make"; "find"; "is_representative"; "eq"; "get"; "set"; "union"; "merge"]}.

(* Resolve the name "find" in the current environment, which binds it under
   an arbitrary number of later (differently named) bindings. This is the
   [in_env] premise that [get_proof], [set_proof] and [union_proof] expect,
   and it is what [imp_path] consumes at the recursive call sites. *)

Local Ltac find_in_env :=
  repeat (iApply (in_env_cons (Φ := find_spec)); [reflexivity|]);
  iApply (in_env_here (Φ := find_spec) with "Hfind");
  reflexivity.

Theorem UnionFind_module_proof η :
  ⊢ EWP (eval_mexpr η __main)
    {{ context [
         var_spec "make"  make_spec;
         var_spec "find"  find_spec;
         var_spec "is_representative" is_representative_spec;
         var_spec "get"   get_spec;
         var_spec "set"   set_spec;
         var_spec "union" union_spec
       ] UnionFind_names }}.
Proof.
  iApply imp_module.

  (* [let make v = ref (Root { rank = 0; value = v })] *)
  iApply (imp_sitems_let make_spec).
  { iApply imp_make. }
  iIntros (make) "#Hmake".

  (* [let rec find x = ...]: the Löb induction happens inside
     [imp_sitems_letrec_iSpec]; all we owe is the body, under the assumption
     that "find" is bound (one step later) to a value satisfying
     [find_spec']. *)
  iApply (imp_sitems_letrec_iSpec τ[elem] find_spec').
  { iIntros "!> #IH".
    iApply find_spec_inductive.
    iNext.
    iApply (in_env_here (Φ := λ c : val, (□ iSpec τ[elem] c find_spec')%I) with "IH").
    reflexivity. }
  iIntros (find) "#Hfind'".

  (* Weaken [find]'s inductive specification to its user-facing one. *)
  iAssert (find_spec find) as "#Hfind".
  { iApply (find_proof with "Hfind'"). }

  (* [let is_representative x = ...] *)
  iApply (imp_sitems_let is_representative_spec).
  { iApply is_representative_proof. }
  iIntros (is_representative) "#Hisrep".

  (* [let eq x y = ...]: unverified, evaluated for its binding only. *)
  iApply (imp_sitems_let (λ _ : val, True)%I).
  { iApply imp_wand; [ iApply imp_EAnon_literal | auto ]. }
  iIntros (eq) "_".

  (* [let get x = ...] *)
  iApply (imp_sitems_let get_spec).
  { iApply get_proof. find_in_env. }
  iIntros (get) "#Hget".

  (* [let set x v = ...] *)
  iApply (imp_sitems_let set_spec).
  { iApply set_proof. find_in_env. }
  iIntros (set) "#Hset".

  (* [let union x y = ...] *)
  iApply (imp_sitems_let union_spec).
  { iApply union_proof. find_in_env. }
  iIntros (union) "#Hunion".

  (* [let merge f x y = ...]: likewise unverified. *)
  iApply (imp_sitems_let (λ _ : val, True)%I).
  { iApply imp_wand; [ iApply imp_EAnon_literal | auto ]. }
  iIntros (merge) "_".

  (* Conclude: read every exported specification back out of the
     environment that the structure has built. *)
  iApply imp_sitems_nil.
  rewrite /context /UnionFind_names /=.
  iSplit.
  { iPureIntro. rewrite /dom /dom_env /=. set_solver. }
  (* [vm_compute] resolves both the [lookup_name] chain and the (identity)
     encoding of a [val]. *)
  repeat iSplit; try done;
    iExists _; (iSplit; [ iPureIntro; vm_compute; reflexivity | ]);
    iModIntro; iFrame "#".
Qed.

End UnionFind.
