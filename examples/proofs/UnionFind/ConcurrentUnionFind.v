From iris.algebra Require Import auth gset.
From iris.base_logic.lib Require Import invariants ghost_map ghost_var proph_map.
From stdpp Require Import relations.

From osiris Require Import osiris.
From osiris.program_logic Require Import atomic.
From osiris.stdlib.proofs Require Import atomic.
From osiris.examples Require Import og_ConcurrentUnionFind.

Require Import UnionFind12GhostInv.

(** * Concurrent union-find

    This file contains the verification of the concurrent union-find data
    structure. *)

(* A vertex is a two-field record { id; content }. *)
Abbreviation elem := record.

(* Field offsets of the vertex record. *)
Abbreviation id_field := 0%Z (only parsing).
Abbreviation content_field := 1%Z (only parsing).

Section ConcurrentUnionFind.

(* Resource algebras used by the [is_uf] invariant. *)
Context `{!osirisGS Σ,
          !ghost_mapG Σ elem Z,
          !ghost_mapG Σ elem (option record),
          !ghost_mapG Σ Z unit,
          !ghost_varG Σ uf_state,
          !inG Σ (authR (gsetUR (elem * elem)))}.

Implicit Types x y z : elem.
Implicit Types rc : record.
Implicit Types i j : Z.
Implicit Types γ : uf_names.

(* ------------------------------------------------------------------------ *)
(* Resoning rules for reading the [id] and [content] fields of an [elem]. *)

(* Atomically reading a vertex's content cell: the caller receives the
   loaded value's [content_info] snapshot. *)

Lemma read_vertex {ζ : exn → iProp Σ} {Ψ η} γ z j e :
  is_uf γ -∗
  vertex γ z j -∗
  EWP (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (z' : elem), ⌜z' = z⌝ }} -∗
  EWP (eval η (ERecordAccess e content_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ (c : content), content_info γ z c }}.
Proof.
  iIntros "#Hinv #Hz He".
  iDestruct (vertex_locs with "Hz") as (lzi lzc) "#Hzlocs".
  iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ z _
            with "[] He []").
  { iModIntro. iApply (blockLocs_field_at with "Hzlocs"). list_z.length; lia. }
  iNext.
  iApply (uf_vertex_content_acc with "Hinv Hz Hzlocs").
  iIntros "!>" (c) "$".
Qed.

(* The same read, for a vertex already known to have been linked away.
   Root-ness is anti-monotone, so the load cannot report a [Root]: whenever
   it happens, the answer is the record [linked] names.

   This is the structural half of [eq]'s [false] case. That case has to
   know, while it is still inside [findc y], how the later [x.content]
   read will turn out; if [x] was seen linked at any earlier instant, this
   settles it outright, and only otherwise does the prophecy have to
   speak. *)

Lemma read_vertex_linked {ζ : exn → iProp Σ} {Ψ η} γ z j rc lp e :
  is_uf γ -∗
  vertex γ z j -∗
  linked γ z rc lp -∗
  EWP (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (z' : elem), ⌜z' = z⌝ }} -∗
  EWP (eval η (ERecordAccess e content_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ (c : content), ⌜c = CtLink rc⌝ ∗ content_info γ z c }}.
Proof.
  iIntros "#Hinv #Hz #Hlk He".
  iDestruct (vertex_locs with "Hz") as (lzi lzc) "#Hzlocs".
  iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ z _
            with "[] He []").
  { iModIntro. iApply (blockLocs_field_at with "Hzlocs"). list_z.length; lia. }
  iNext.
  iApply (uf_vertex_content_acc_linked with "Hinv Hz Hzlocs Hlk").
  iIntros "!>" (c) "%Hc #Hinfo". by iFrame "Hinfo".
Qed.

(* The same read, for a caller holding the [linked] witness inside a
   disjunction rather than outright. What comes back is the same
   disjunction with the right branch weakened to a pure statement about
   the value just loaded. See [uf_vertex_content_acc_or_linked]. *)

Lemma read_vertex_or_linked {ζ : exn → iProp Σ} {Ψ η} γ z j (P Q : iProp Σ) e :
  is_uf γ -∗
  vertex γ z j -∗
  (P ∨ (∃ rc lp, linked γ z rc lp) ∗ Q) -∗
  EWP (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (z' : elem), ⌜z' = z⌝ }} -∗
  EWP (eval η (ERecordAccess e content_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ (c : content),
         content_info γ z c ∗ (P ∨ ⌜content_root c = false⌝ ∗ Q) }}.
Proof.
  iIntros "#Hinv #Hz HPQ He".
  iDestruct (vertex_locs with "Hz") as (lzi lzc) "#Hzlocs".
  iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ z _
            with "[] He [HPQ]").
  { iModIntro. iApply (blockLocs_field_at with "Hzlocs"). list_z.length; lia. }
  iNext.
  iApply (uf_vertex_content_acc_or_linked with "Hinv Hz Hzlocs HPQ").
  iIntros "!>" (c) "#Hinfo HPQ". by iFrame "Hinfo HPQ".
Qed.

(* The same read, annotated with [@resolve p v]: the prophecy is resolved
   at the load of the content field, and its head is the content read. *)

Lemma read_vertex_or_linked_resolve {ζ : exn → iProp Σ} {Ψ η} γ z j (P Q : iProp Σ) e
    ep ev (p : proph_id) v pvs (Φ : content → iProp Σ) :
  lookup_path η ep = Some #p →
  eval_proph_arg η ev = Some v →
  is_uf γ -∗
  vertex γ z j -∗
  (P ∨ (∃ rc lp, linked γ z rc lp) ∗ Q) -∗
  proph p pvs -∗
  EWP (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (z' : elem), ⌜z' = z⌝ }} -∗
  (∀ (c : content) pvs', ⌜pvs = (♯c, v) :: pvs'⌝ -∗ proph p pvs' -∗
     content_info γ z c ∗ (P ∨ ⌜content_root c = false⌝ ∗ Q) -∗ Φ c) -∗
  EWP (eval η (EResolve (ERecordAccess e content_field) ep ev)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ Φ }}.
Proof.
  iIntros (Hp Hv) "#Hinv #Hz HPQ Hproph He Hcont".
  iDestruct (vertex_locs with "Hz") as (lzi lzc) "#Hzlocs".
  iApply (imp_EResolve_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ z _ _ _ _ _ _
            (λ c : content, content_info γ z c ∗ (P ∨ ⌜content_root c = false⌝ ∗ Q))%I
            with "[] Hproph He [HPQ] Hcont"); [ exact Hp | exact Hv | | ].
  { iModIntro. iApply (blockLocs_field_at with "Hzlocs"). list_z.length; lia. }
  iNext.
  iApply (uf_vertex_content_acc_or_linked with "Hinv Hz Hzlocs HPQ").
  iIntros "!>" (c) "#Hinfo HPQ". by iFrame "Hinfo HPQ".
Qed.

(* Reading a vertex's immutable [id] field, through the persistent
   points-to that [vertex] carries. *)

Lemma read_vertex_id {ζ : exn → iProp Σ} {Ψ η} γ z i e :
  vertex γ z i -∗
  EWP (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (z' : elem), ⌜z' = z⌝ }} -∗
  EWP (eval η (ERecordAccess e id_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ (n : Z), ⌜n = i⌝ }}.
Proof.
  iIntros "#Hz He".
  iDestruct "Hz" as (li lc) "(_ & #Hlocs & _ & #Hli)".
  iApply (imp_ERecordAccess_pers id_field _ _ _ i with "[] He [] []").
  { iModIntro. iApply (blockLocs_field_at with "Hlocs"). by vm_compute. }
  { iExact "Hli". }
  { iIntros "!> _". done. }
Qed.

(* The location of a vertex's content field as a first-class value. *)

Lemma vertex_content_ptr {ζ : exn → iProp Σ} {Ψ η} γ z i e :
  vertex γ z i -∗
  EWP (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (z' : elem), ⌜z' = z⌝ }} -∗
  EWP (eval η (EAtomicLoc e content_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ (l : locations.loc), ∃ li, blockLocs z [li; l] }}.
Proof.
  iIntros "#Hz He".
  iDestruct "Hz" as (li lc) "(_ & #Hlocs & _ & _)".
  iApply (imp_EAtomicLoc content_field z _ with "[] He []").
  { iModIntro. iApply (blockLocs_field_at with "Hlocs"). list_z.length; lia. }
  iNext. iExists li. iExact "Hlocs".
Qed.


(* ------------------------------------------------------------------------ *)
(* The [cas] top-level alias. *)

Lemma cas_proof η :
  in_env "Atomic" atomic_module_spec η -∗
  EWP (eval η (EPath ["Atomic"; "Loc"; "compare_and_set"]))
    {{ cas, compare_and_set_spec cas }}.
Proof.
  iIntros "HAtomic".
  iDestruct (atomic_cas_path_spec with "HAtomic") as (cas Hcas) "#Hspec".
  iApply (imp_EPath (A:=val) cas).
  { exact Hcas. }
  iExact "Hspec".
Qed.

(* The same read, at the one place where it is a linearization point.
   The caller hands over a resource [P] (in practice the atomic update
   it is running under) together with a hook saying what to do with it
   if the loaded content turns out to be a [Root]. If the content is a
   [Link] instead, nothing has been linearized and we get [P] back. *)

Lemma read_vertex_lp {ζ : exn → iProp Σ} {Ψ η} (Q : content → iProp Σ) (P : iProp Σ)
  γ (x : elem) i e
  :
  is_uf γ -∗
  vertex γ x i -∗
  P -∗
  ▷ (∀ (c : content) D (R : elem → elem) (V : elem → val),
       ⌜content_root c = true⌝ -∗ ⌜R x = x⌝ -∗
       content_info γ x c -∗ content_val V x c -∗
       P -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗
       UF γ D R V ∗ Q c) -∗
  EWP (eval η e) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩ {{ (z' : elem), ⌜z' = x⌝ }} -∗
  EWP (eval η (ERecordAccess e content_field)) @ ⊤ <|Ψ|> ⟨⟨ ζ ⟩⟩
    {{ (c : content),
         if content_root c then Q c else content_info γ x c ∗ P }}.
Proof.
  iIntros "#Hinv #Hx HP Hhook He".
  iDestruct "Hx" as (lxi lxc) "(#Hxfrag & #Hxlocs & #HxP & #Hxli)".
  iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ x _
            with "[] He [HP Hhook]").
  { iModIntro. iApply (blockLocs_field_at with "Hxlocs"). list_z.length; lia. }
  iNext.
  iApply (uf_find_content_acc with "Hinv Hxfrag Hxlocs").
  iNext. iIntros (c D R V) "_ %Hroot #Hinfo #Hval Hst".
  destruct (content_root c) eqn:Hc; last by iFrame "Hst Hinfo HP".
  pose proof (Hroot eq_refl) as HRx.
  iMod ("Hhook" $! c D R V with "[//] [//] Hinfo Hval HP Hst") as "[$ $]". done.
Qed.

(* ------------------------------------------------------------------------ *)
(* Specification of [G.fresh]. *)

(* [G.fresh]'s specification is strengthened to hand back exclusive
   ownership of the returned identifier [i].

   As it stands, this specification is too strong and not provable,
   as we may overflow and return an identifier which is not fresh. *)

Definition fresh_spec (γ : uf_names) fresh : iProp Σ :=
  {{ is_uf γ }}
  fresh u : unit
  {{ RET (i : Z); i ↪[γ.(uf_ids)] () ∗ ⌜representable i⌝ }}.

(* ------------------------------------------------------------------------ *)
(* Verification of [make]. *)

(* Ownership of a freshly allocated, not-yet-installed [Root] record
   holding [v]. *)
Definition fresh_root (cx : content) (v : val) : iProp Σ :=
  match cx with
  | CtRoot rc => rc ⤇ {| root_value := v |}
  | CtLink _ => False
  end.

(* [make v] returns a fresh vertex of the structure, of value [v] and
   its own class.

   We state [make]'s specification via a logically atomic triple. At
   the linearization point, we get the structure [UF γ D R V], and add
   a new vertex [x] to the domain, such that the value associated to
   [x] is [v]. We do not need to update the representative function [R]
   because [R] is the identity function outside of the domain [D], so
   [x] is already its own representative. *)

Definition make_spec (γ : uf_names) (v : val) (m : microvx) : iProp Σ :=
  is_uf γ -∗
  <<{ ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    m @ ↑ufN
  <<{ ∃∃ x : elem, ⌜(x ∉ D) ∧ R x = x⌝ ∗ UF γ (D ∪ {[x]}) R V.[x -/R/> v]
    | RET x; in_uf γ x }>>.

(* Records allocated by this module must fit within [max_array_length]. *)
Hypothesis Hmax1 : (1 ≤ max_array_length)%Z.
Hypothesis Hmax2 : (2 ≤ max_array_length)%Z.

Lemma make_proof γ η :
  path_spec ["G"; "fresh"] (fresh_spec γ)%I η -∗
  EWP (eval η (EAnonFun __make)) {{ c, □ iSpec τ[val] c (make_spec γ) }}.
Proof.
  iIntros "#HG".
  iApply imp_EAnon_pers.
  iIntros "!>" (v).
  unfold make_spec.
  (* We are proving a logically atomic triple: introduce the atomic
     update [AU] and the abstract postcondition [Φ]. *)
  iIntros "#Hinv" (Φ) "AU".
  iApply imp_please; iNext.

  (* [let id = G.fresh() and content = Root { value = v } in ...].
     We specify the two postconditions upfront. *)
  imp_let $! (λ i : Z, i ↪[γ.(uf_ids)] () ∗ ⌜representable i⌝)%I
          $! (λ c : content, ∃ rc, ⌜c = CtRoot rc⌝ ∗ rc ⤇ {| root_value := v |})%I.
  { (* [G.fresh()]. *)
    imp_app τ[unit].
    iIntros "Hm".
    iApply ("Hm" with "Hinv"). }
  { (* [Root { value = v }]. *)
    imp_record $! root_fields.
    simpl. iIntros (c) "(%r & -> & % & Hown & ->)".
    by iFrame "Hown". }
  iIntros (a cx) "[Htok %Hrepa] (%rc & -> & Hrecord)".

  (* [{ id; content }]. *)
  iApply imp_fupd.
  iApply (imp_wand with "[]").
  { imp_record. }
  iIntros (x) "(%i & %c & Hown & -> & ->) /=".

  (* Establish the postcondition [|={⊤}=> Φ x] with the atomic update *)
  iMod (register_vertex (in_uf γ x -∗ Φ x)%I $! Hrepa
          with "Hinv Htok Hown Hrecord [AU]") as "[#Hv HΦ]".
  { (* The linearization point: commit the atomic update. *)
    iIntros (D R V) "%HxD %Hroot Hst".
    iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
    iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
    iDestruct (UF_val_congr with "Hst") as %Hcongr.
    iDestruct (UF_dethroned with "Hst") as "#Hdeth".
    iMod (UF_update_2 _ _ _ _ (D ∪ {[x]}) R V.[x -/R/> v]
            with "Hdeth Hst Hcl") as "[Hst Hcl]";
      [done | by apply uf_val_congr_set |].
    iMod ("Hcommit" $! x with "[$Hcl]") as "HΦ"; first done.
    by iFrame "Hst HΦ". }
  iModIntro. iApply "HΦ". by iExists a.
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [find]. *)

(* [find x] returns the representative of [x] as of the instant of its
   own last read.

   Consider the sequential [find_spec] (UnionFind.v):

     ∀ D R V, ⌜e ∈ D⌝ -∗ UF D R V -∗
       EWP m {{ (z : elem), ⌜z = R e⌝ ∗ UF D R V }}

   The concurrent version below is the same statement with the state
   quantified atomically instead of owned by the caller throughout, and
   with the pure precondition [⌜e ∈ D⌝] replaced by the persistent
   [in_uf γ x]. *)

Definition find_spec (γ : uf_names) x (m : microvx) : iProp Σ :=
  is_uf γ -∗
  in_uf γ x -∗
  <<{ ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    m @ ↑ufN
  <<{ ∃∃ z : elem, ⌜z = R x⌝ ∗ UF γ D R V
    | RET z; in_uf γ z ∗ same_class γ x z }>>.

(* ------------------------------------------------------------------------ *)

(* A stronger specification for [find] using a hook to pass around the
   atomic update. *)

Definition find_hook (γ : uf_names) (x : elem) (Ψ : elem → iProp Σ) : iProp Σ :=
  ∀ D (R : elem → elem) (V : elem → val),
    UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V ∗ Ψ (R x).

Lemma find_hook_rebase γ x z Ψ :
  same_class γ x z -∗ find_hook γ x Ψ -∗ find_hook γ z Ψ.
Proof.
  iIntros "#Hxz Hhook" (D R V) "Hst".
  iDestruct (UF_same_class_eq with "Hst Hxz") as "[%Heq Hst]".
  rewrite -Heq. iApply ("Hhook" with "Hst").
Qed.

Definition find_aux_spec (γ : uf_names) (x : elem) (m : microvx) : iProp Σ :=
  ∀ (Ψ : elem → iProp Σ),
    is_uf γ -∗
    in_uf γ x -∗
    find_hook γ x Ψ -∗
    EWP m {{ (z : elem), Ψ z ∗ in_uf γ z ∗ same_class γ x z }}.

(* A weaker specification for [find], which isn't atomic at all. *)

Lemma find_observe γ x m :
  find_aux_spec γ x m -∗
  is_uf γ -∗
  in_uf γ x -∗
  EWP m {{ (z : elem), in_uf γ z ∗ same_class γ x z }}.
Proof.
  iIntros "Hspec #Hinv #Hx".
  iSpecialize ("Hspec" $! (λ _, True)%I with "Hinv Hx []").
  { iIntros (D R V) "$". by iModIntro. }
  iApply (imp_wand with "Hspec").
  iIntros (z) "(_ & $ & $)".
Qed.

Lemma find_atomic_spec γ x m :
  find_aux_spec γ x m -∗ find_spec γ x m.
Proof.
  iIntros "Hspec #Hinv #Hx".
  unfold find_spec. iIntros (Φ) "AU".
  iSpecialize ("Hspec" $! (λ z, in_uf γ z ∗ same_class γ x z -∗ Φ z)%I
                 with "Hinv Hx [AU]").
  { iIntros (D R V) "Hst".
    iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
    iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
    iMod ("Hcommit" $! (R x) with "[$Hcl]") as "HΦ"; first done.
    by iFrame. }
  iApply (imp_wand with "Hspec").
  iIntros (z) "(HΦ & #Hin & #Hsc)". iApply "HΦ". by iFrame "Hin Hsc".
Qed.

Lemma find_atomic_iSpec γ c :
  iSpec τ[elem] c (find_aux_spec γ) -∗ iSpec τ[elem] c (find_spec γ).
Proof.
  iIntros "Hspec".
  iApply (iSpec_mono with "Hspec").
  iIntros (x m) "Hm". by iApply find_atomic_spec.
Qed.

Lemma find_proof γ η :
  ▷ in_env "find" (λ find, □ iSpec τ[elem] find (find_aux_spec γ)) η -∗
  □ fun_spec.predicate_over_function_body τ[elem] (find_aux_spec γ) η
      (EAnonFun (AnonFun "x"
        (EMatch (ERecordAccess (EPath ["x"]) content_field) __find_branches))).
Proof.
  iIntros "#IH".
  iIntros "!>" (x).
  unfold find_aux_spec at 2.
  iIntros (Ψ) "#Hinv #Hx Hhook".
  iDestruct "Hx" as (i) "#Hxv".
  iApply imp_please; iNext.

  (* Goal: [ match x.content with ... ]. The scrutinee read carries the
     hook: on a [Root] it is run there and then, and the branch's whole
     postcondition comes back in its place. *)
  imp_match content with "[Hhook]".
  { iApply (read_vertex_lp (λ _, Ψ x ∗ in_uf γ x ∗ same_class γ x x)%I
              with "Hinv Hxv Hhook [] []"); last first.
    { imp_path. }
    iNext. iIntros (c D R V) "_ %HRx _ _ Hhook Hst".
    (* The linearization point: [x] is its own representative in the
       state the accessor exposes. *)
    iMod ("Hhook" with "Hst") as "[$ HΨ]".
    iEval (rewrite HRx) in "HΨ".
    iFrame "HΨ Hxv". iApply same_class_refl. }
  iIntros "Hc".

  (* Branches of the match. TODO: Make the iris-level pattern-matching
     machinery able to give us Hoare-style postconditions on this type
     of match. *)
  destruct a as [rc|rc]; simpl.

  { (* [Root _ -> x]: nothing left to do, the branch returns [x]. *)
    rewrite (@encode_encode' content).
    next_branch. imp_path. }

  (* [Link { parent = y } -> find y]: the hook was handed back untouched,
     together with the loaded value's [content_info]. *)
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  iDestruct "Hc" as "[(_ & (%lp & #Hlk)) Hhook]".
  iDestruct (linked_locs with "Hlk") as "#Hlocs".
  iApply (ipat_PRecord_atomic (A:=elem) (⊤ ∖ ↑ufN) ⊤
            with "[] [Hhook]").
  { iModIntro. iApply (blockLocs_field_at with "Hlocs"). done. }
  iNext.
  iApply (uf_link_parent_acc with "Hinv Hxv Hlk [Hhook]").
  iNext.
  iIntros (y j Hj) "#Hxy #Hy".

  (* Recursive call [find y]. *)
  imp_app τ[elem].
  iIntros "Hm".
  iSpecialize ("Hm" $! Ψ with "Hinv [$] [Hhook]").
  { iApply (find_hook_rebase with "Hxy Hhook"). }
  (* Show that the found ancestor of the parent [y] is also an ancestor
     of the original vertex. *)
  iApply (imp_wand with "Hm").
  iIntros (z) "($ & $ & #Hyz)".
  iApply (same_class_trans with "Hxy Hyz").
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [compress]. *)

(* [compress x z] walks the path out of [x], rerouting each link it passes
   to point directly at [z], and returns [z].

   It has no other observable effect as it preserves the
   datastructure's invariant. *)

Definition compress_spec (γ : uf_names) (x z : elem) (m : microvx) : iProp Σ :=
  ∀ i k,
    is_uf γ -∗
    vertex γ x i -∗
    vertex γ z k -∗
    same_class γ x z -∗
    EWP m {{ (w : elem), ⌜w = z⌝ }}.

Lemma compress_proof γ η :
  ▷ in_env "compress"
      (λ compress, □ iSpec τ[elem; elem] compress (compress_spec γ)) η -∗
  □ fun_spec.predicate_over_function_body τ[elem; elem] (compress_spec γ) η
      (EAnonFun (AnonFun "x" (EAnonFun __compress_fun))).
Proof.
  iIntros "#IH".
  iIntros "!> /=".
  iIntros (x z).
  unfold compress_spec at 2.
  iIntros (i k) "#Hinv #Hx #Hz #Hxz".
  (* Both identifiers are compared by machine instructions below. *)
  iMod (vertex_representable with "Hinv Hx") as %Hrepi.
  iMod (vertex_representable with "Hinv Hz") as %Hrepk.
  iApply imp_please; iNext.

  (* [match x.content with ...], read atomically. *)
  imp_match content.
  { iApply (read_vertex with "Hinv Hx"). imp_path. }
  iIntros "#Hc".
  destruct a as [rc|rc]; simpl.

  { (* [Root _ -> z]: [x] is a root, nothing to compress. *)
    rewrite (@encode_encode' content). next_branch.
    imp_path. }

  (* [Link link -> ...]. *)
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.

  (* [let y = link.parent in ...]. *)
  iApply (imp_ELet_var (B:=elem)
    (λ y : elem, ∃ jy, ⌜(jy < i)%Z⌝ ∗ same_class γ x y ∗ vertex γ y jy)%I).
  { iDestruct "Hc" as "(_ & (%lp & #Hlk))".
    iDestruct (linked_locs with "Hlk") as "#Hlocs".
    iApply (imp_ERecordAccess_atomic (⊤ ∖ ↑ufN) with "[] [] []").
    { iModIntro. iApply (blockLocs_field_at with "Hlocs"). list_z.length; lia. }
    { imp_path. }
    iNext.
    iApply (uf_link_parent_acc with "Hinv Hx Hlk []").
    iNext.
    iIntros (y jy Hjy) "$ $ //". }
  iIntros (y) "(%jy & %Hjy & #Hsxy & #Hy)".
  iMod (vertex_representable with "Hinv Hy") as %Hrepjy.

  (* [assert (x.id > y.id)]: discharged by the link field's own bound,
     [jy < i]. *)
  iApply (imp_ESeq (λ _ : unit, True)%I).
  { iApply imp_EAssert.
    iSplit; first done.
    iApply (imp_wand with "[]").
    { iApply (imp_EOpGt_Z _ _ _ i jy); try assumption.
      - iApply (read_vertex_id with "Hx"). imp_path.
      - iApply (read_vertex_id with "Hy"). imp_path. }
    iIntros (b0) "->". iPureIntro. lia. }
  iIntros "_".

  (* [if y.id > z.id then ...]. *)
  imp_if.
  { iApply (imp_EOpGt_Z _ _ _ jy k); try assumption.
    - iApply (read_vertex_id with "Hy"). imp_path.
    - iApply (read_vertex_id with "Hz"). imp_path. }

  {
    iIntros "%Hcmp".
    assert (Hkjy : (k < jy)%Z) by lia.

    imp_match unit with "[]".
    { (* [assert (x.id > z.id)]. *)
      iApply (imp_EAssert (R:=True%I)).
      iSplit; first done.
      iApply (imp_wand with "[]").
      { iApply (imp_EOpGt_Z _ _ _ i k); try assumption.
        - iApply (read_vertex_id with "Hx"). imp_path.
        - iApply (read_vertex_id with "Hz"). imp_path. }
      iIntros (b0) "->". iPureIntro. lia. }
    iIntros "_".
    destruct a; next_branch.

    (* [link.parent <- z]: the compression write. The link field's
       conjuncts are re-established from [vertex γ z k], the bound
       [k < jy < i], and the caller's [same_class γ x z]. *)
    iApply (imp_ESeq (λ _ : unit, True)%I).
    { iDestruct "Hc" as "(_ & (%lp & #Hlk))".
      iDestruct (linked_locs with "Hlk") as "#Hlocs".
      iApply (imp_ERecordSet_atomic (⊤ ∖ ↑ufN) ⊤ _ _ _ _ rc _ (λ w : elem, ⌜w = z⌝)%I
                with "[] [] [] []").
      { iModIntro. iApply (blockLocs_field_at with "Hlocs"). list_z.length; lia. }
      { imp_path. }
      { imp_path. }
      iNext.
      iIntros (a) "->".
      iApply (uf_link_parent_set with "Hinv Hx Hlk Hz Hxz []").
      { lia. }
      done. }
    iIntros "_".

    (* [compress y z]: the recursive call's precondition. *)
    iDestruct (same_class_sibling with "Hsxy Hxz") as "#Hyz".
    imp_app τ[elem; elem].
    iIntros "Hm".
    iApply ("Hm" $! jy k with "Hinv Hy Hz Hyz"). }

  (* [else z]: compression would not lower the identifier, so stop. *)
  { iIntros "%Hcmp". imp_path. }
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [findc]. *)

(* [findc] satisfies [find]'s specification: the compression is invisible.

   [findc] is [find] followed by [compress], and its linearization point
   is inside the [find], at the instant [find] reports its answer.
   So [findc] hands its client's atomic update straight to [find]. *)

Lemma findc_proof γ η :
  in_env "find" (λ find, □ iSpec τ[elem] find (find_aux_spec γ)) η -∗
  in_env "compress"
    (λ compress, □ iSpec τ[elem; elem] compress (compress_spec γ)) η -∗
  EWP (eval η (EAnonFun __findc))
    {{ c, □ iSpec τ[elem] c (find_aux_spec γ) }}.
Proof.
  iIntros "#IFind #ICompress".
  iApply imp_EAnon_pers.
  iIntros "!>" (x).
  unfold find_aux_spec at 2.
  iIntros (Ψ) "#Hinv #Hx Hhook".
  iDestruct "Hx" as (i) "#Hxv".
  iApply imp_please; iNext.

  (* [match x.content with ...]. *)
  imp_match content with "[Hhook]".
  { iApply (read_vertex_lp (λ _, Ψ x ∗ in_uf γ x ∗ same_class γ x x)%I
              with "Hinv Hxv Hhook [] []"); last first.
    { imp_path. }
    iNext. iIntros (c D R V) "_ %HRx _ _ Hhook Hst".
    iMod ("Hhook" with "Hst") as "[$ HΨ]".
    iEval (rewrite HRx) in "HΨ".
    iFrame "HΨ".
    iSplitR; [by iExists i | iApply same_class_refl]. }
  iIntros "Hc".
  destruct a as [rc|rc]; simpl.

  { (* [Root _ -> x]. *)
    rewrite (@encode_encode' content). next_branch.
    imp_path. }

  (* [Link { parent = y } -> let z = find y in compress x z]. *)
  iDestruct "Hc" as "[(_ & (%lp & #Hlk)) Hhook]".
  iDestruct (linked_locs with "Hlk") as "#Hlocs".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  iApply (ipat_PRecord_atomic (A:=elem) (⊤ ∖ ↑ufN) ⊤
            with "[] [Hhook]").
  { iModIntro. iApply (blockLocs_field_at with "Hlocs"). done. }
  iNext.
  iApply (uf_link_parent_acc with "Hinv Hxv Hlk [Hhook]").
  iNext.
  iIntros (y jy Hjy) "#Hxy #Hy".

  (* [let z = find y in ...]: the call is on [y], but the hook [findc]
     holds is about [x], so it is transported across [same_class γ x y]
     by [find_hook_rebase]. *)
  iApply (imp_ELet_var (B:=elem)
    (λ z : elem, Ψ z ∗ in_uf γ z ∗ same_class γ x z)%I with "[Hhook]").
  { imp_app τ[elem].
    iIntros "Hm".
    iSpecialize ("Hm" $! Ψ with "Hinv [$] [Hhook]").
    { iApply (find_hook_rebase with "Hxy Hhook"). }
    iApply (imp_wand with "Hm").
    iIntros (z) "($ & $ & #Hyz)".
    iApply (same_class_trans with "Hxy Hyz"). }
  iIntros (z) "(HΨ & #Hz & #Hxz)".

  (* [compress x z]. *)
  iDestruct "Hz" as (k) "#Hzv".
  imp_app τ[elem; elem].
  iIntros "Hm".
  unfold compress_spec.
  iSpecialize ("Hm" $! i k with "Hinv Hxv Hzv Hxz").
  iApply (imp_wand with "Hm").
  iIntros (w) "->".
  iFrame "HΨ Hxz Hzv".
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [get]. *)

Definition get_hook (γ : uf_names) (x : elem) (Ψ : val → iProp Σ) : iProp Σ :=
  ∀ D (R : elem → elem) (V : elem → val),
    UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V ∗ Ψ (V (R x)).

Lemma get_hook_rebase γ x z Ψ :
  same_class γ x z -∗ get_hook γ x Ψ -∗ get_hook γ z Ψ.
Proof.
  iIntros "#Hxz Hhook" (D R V) "Hst".
  iDestruct (UF_same_class_eq with "Hst Hxz") as "[%Heq Hst]".
  rewrite -Heq. iApply ("Hhook" with "Hst").
Qed.

Definition get_aux_spec (γ : uf_names) (x : elem) (m : microvx) : iProp Σ :=
  ∀ (Ψ : val → iProp Σ),
    is_uf γ -∗
    in_uf γ x -∗
    get_hook γ x Ψ -∗
    EWP m {{ Ψ }}.

Definition get_spec (γ : uf_names) (x : elem) (m : microvx) : iProp Σ :=
  is_uf γ -∗
  in_uf γ x -∗
  <<{ ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    m @ ↑ufN
  <<{ UF γ D R V | RET (V (R x)) }>>.

Lemma get_atomic_spec γ x m :
  get_aux_spec γ x m -∗ get_spec γ x m.
Proof.
  iIntros "Hspec #Hinv #Hx" (Φ) "AU".
  iApply ("Hspec" $! Φ with "Hinv Hx [AU]").
  (* The hook: the state the client's atomic update offers is the state at
     the linearization point, so this is where it is committed. *)
  iIntros (D R V) "Hst".
  iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
  iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
  iMod ("Hcommit" with "Hcl") as "HΦ".
  by iFrame "Hst HΦ".
Qed.

Lemma get_proof γ η :
  ▷ in_env "get" (λ get, □ iSpec τ[elem] get (get_aux_spec γ)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (find_aux_spec γ)) η -∗
  □ fun_spec.predicate_over_function_body τ[elem] (get_aux_spec γ) η
      (EAnonFun (AnonFun "x"
        (ELet [Binding (PVar "x") (EApp (EPath ["findc"]) (EPath ["x"]))]
              __get_exp))).
Proof.
  iIntros "#IGet #IFindc".
  iIntros "!>" (x).
  unfold get_aux_spec at 2.
  iIntros (Ψ) "#Hinv #Hx Hhook".
  iApply imp_please; iNext.

  (* [let x = findc x in ...].
     This is just an observer call as the traversal is not [get]'s
     linearization point. *)
  iApply (imp_ELet_var (B:=elem)
    (λ z : elem, in_uf γ z ∗ same_class γ x z)%I with "[]").
  { imp_app τ[elem].
    iIntros "Hm".
    iApply (find_observe with "Hm Hinv Hx"). }
  iIntros (z) "[#Hz #Hxz]".
  iDestruct "Hz" as (j) "#Hzv".

  (* From here on everything is stated at [z], so the hook moves there
     once and for all. *)
  iDestruct (get_hook_rebase with "Hxz Hhook") as "Hhook".

  (* [match x.content with ...]: [get]'s linearization point. *)
  imp_match content with "[Hhook]".
  { iApply (read_vertex_lp
              (λ c : content, match c with
                              | CtRoot rc => ∃ v : val, root_val rc v ∗ Ψ v
                              | CtLink _ => False
                              end)%I
              with "Hinv Hzv Hhook [] []"); last first.
    { imp_path. }
    iNext. iIntros (c D R V) "%Hroot %HRz _ #Hval Hhook Hst".
    destruct c as [rc|rc]; last discriminate.
    iMod ("Hhook" $! D R V with "Hst") as "[Hst HΨ]".
    (* [z] is its own representative in the state just committed, so the
       value that state assigns to it is the payload of this record. *)
    rewrite HRz. by iFrame "Hst Hval HΨ". }
  iIntros "Hc".
  destruct a as [rc|rc]; simpl.

  { (* [Root root -> root.value]. *)
    rewrite (@encode_encode' content).
    next_branch.
    iDestruct "Hc" as (v) "[#Hrv HΨ]".
    iDestruct "Hrv" as (lv) "(#Hrclocs & _ & #Hlv)".
    iApply (imp_ERecordAccess_pers 0%Z rc _ _ v with "[] [] [] [HΨ]").
    { iModIntro. iApply (blockLocs_field_at with "Hrclocs"). list_z.length; lia. }
    { imp_path. }
    { iExact "Hlv". }
    { iIntros "!> _". iExact "HΨ". } }

  (* [Link _ -> get x]: [z] was linked away between [findc] and the read,
     so nothing was linearized; retry from [z]. *)
  iDestruct "Hc" as "[_ Hhook]".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem].
  iIntros "Hm".
  iApply ("Hm" $! Ψ with "Hinv [$] Hhook").
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [set]. *)

(* [set x v] writes [v] as the value of [x]'s equivalence class.

   [set] does not write the payload field: it allocates a fresh
   [Root { value = v }] and CASes the whole content cell. The
   linearization point is the successful CAS. *)

Definition set_hook (γ : uf_names) (x : elem) (v : val)
    (Ψ : iProp Σ) : iProp Σ :=
  ∀ D (R : elem → elem) (V : elem → val),
    UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V.[x -/R/> v] ∗ Ψ.

(* Re-basing, for the retry, as in [get]. Here, naming a class by one
   member or another is literally the same function. *)

Lemma set_hook_rebase γ x z v Ψ :
  same_class γ x z -∗ set_hook γ x v Ψ -∗ set_hook γ z v Ψ.
Proof.
  iIntros "#Hxz Hhook" (D R V) "Hst".
  iDestruct (UF_same_class_eq with "Hst Hxz") as "[%Heq Hst]".
  rewrite -(update_class_congr_class R x z V v Heq).
  iApply ("Hhook" with "Hst").
Qed.

Definition set_content_spec (γ : uf_names) (x : elem) (cx' : content)
    (m : microvx) : iProp Σ :=
  ∀ (v : val) (Ψ : iProp Σ),
    is_uf γ -∗
    in_uf γ x -∗
    fresh_root cx' v -∗
    set_hook γ x v Ψ -∗
    EWP m {{ (_ : unit), Ψ }}.

Definition set_aux_spec (γ : uf_names) (x : elem) (v : val)
    (m : microvx) : iProp Σ :=
  ∀ (Ψ : iProp Σ),
    is_uf γ -∗
    in_uf γ x -∗
    set_hook γ x v Ψ -∗
    EWP m {{ (_ : unit), Ψ }}.

(* The specification as a client sees it. *)

Definition set_spec (γ : uf_names) (x : elem) (v : val)
    (m : microvx) : iProp Σ :=
  is_uf γ -∗
  in_uf γ x -∗
  <<{ ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    m @ ↑ufN
  <<{ UF γ D R V.[x -/R/> v] | RET tt }>>.

Lemma set_atomic_spec γ x v m :
  set_aux_spec γ x v m -∗ set_spec γ x v m.
Proof.
  iIntros "Hspec #Hinv #Hx" (Φ) "AU".
  iApply (imp_wand _ _ _ _ (λ _ : unit, Φ tt)%I _ with "[Hspec AU]"); last first.
  { iIntros ([]) "H". iExact "H". }
  iApply ("Hspec" $! (Φ tt) with "Hinv Hx [AU]").
  (* The hook: here both halves of the abstract state move together. *)
  iIntros (D R V) "Hst".
  iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
  iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
  iDestruct (UF_val_congr with "Hst") as %Hcongr.
  iDestruct (UF_dethroned with "Hst") as "#Hdeth".
  iMod (UF_update_2 _ _ _ _ D R V.[x -/R/> v]
          with "Hdeth Hst Hcl") as "[Hst Hcl]";
    [done | by apply uf_val_congr_set |].
  iMod ("Hcommit" with "Hcl") as "HΦ".
  by iFrame "Hst HΦ".
Qed.

Lemma set_proof γ η :
  ▷ in_env "set"
      (λ set, □ iSpec τ[elem; content] set (set_content_spec γ)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (find_aux_spec γ)) η -∗
  in_env "cas"
    compare_and_set_spec η -∗
  □ fun_spec.predicate_over_function_body τ[elem; content] (set_content_spec γ) η
      (EAnonFun (AnonFun "x" (EAnonFun __set_fun))).
Proof.
  iIntros "#ISet #IFindc #Hcas".
  iIntros "!> /=".
  iIntros (x cx' v Ψ).
  iIntros "#Hinv #Hx Hcx' Hhook".
  (* The caller's record is a [Root]. *)
  destruct cx' as [rcn|rcn]; last by iDestruct "Hcx'" as "[]".
  iApply imp_please; iNext.

  (* [let x = findc x in ...]: an observer call, as in [get]. *)
  iApply (imp_ELet_var (B:=elem)
    (λ z : elem, in_uf γ z ∗ same_class γ x z)%I with "[]").
  { imp_app τ[elem].
    iIntros "Hm".
    iApply (find_observe with "Hm Hinv Hx"). }
  iIntros (z) "[#Hz #Hxz]".
  iDestruct "Hz" as (j) "#Hzv".
  iDestruct (set_hook_rebase with "Hxz Hhook") as "Hhook".

  (* [let cx = x.content in ...]. *)
  iApply (imp_ELet_var (B:=content) (λ c : content, content_info γ z c)%I).
  { iApply (read_vertex with "Hinv Hzv"). imp_path. }
  iIntros (cx) "#Hcx".

  (* Re-match on the already-loaded [cx]: a plain path lookup. *)
  imp_match content with "[]".
  destruct cx as [rc|rc]; simpl.

  { (* [Root _ -> if cas x.content cx cx' then () else set x cx']. *)
    iDestruct "Hcx" as "(#HrcP & (%vexp & #Hrv))".
    rewrite {2}(@encode_encode' content).
    next_branch.

    (* [if cas [%atomic.loc x.content] cx cx']. *)
    imp_if with "[Hcx' Hhook]".
    { set_postcondition (λ res : bool,
        if res then Ψ else set_hook γ z v Ψ ∗ rcn ⤇ {| root_value := v |})%I.
      imp_app τ[loc;content;content].
      { iApply (vertex_content_ptr with "Hzv"). imp_path. }
      iIntros "Hptr Hm".
      iApply ("Hm" $! (⊤ ∖ ↑ufN)).
      iNext.
      iApply (uf_cas_set_fupd _ z j _ rc rcn vexp v (set_hook γ z v Ψ) Ψ
                (λ res : bool,
                   if res then Ψ
                   else set_hook γ z v Ψ ∗ rcn ⤇ {| root_value := v |})%I
                with "Hinv Hzv Hptr Hrv Hcx' Hhook [] []").
      { (* Handover from set's hook to CAS' hook. *)
        iNext. iIntros (D R V) "%Hax %Hval Hhook Hst".
        iMod ("Hhook" $! D R V with "Hst") as "[Hst HΨ]".
        by iFrame "Hst HΨ". }
      { iIntros "!> % $". } }

    { (* CAS succeeded: the hook has already produced the postcondition. *)
      iIntros "HΨ". iApply (imp_EUnit with "HΨ"). }
    { (* CAS failed: retry on the vertex [findc] found, with the hook and
         the fresh record handed back. *)
      iIntros "[Hhook Hcx']".
      imp_app τ[elem; content].
      iIntros "Hm".
      iApply ("Hm" $! v Ψ with "Hinv [$] Hcx' Hhook"). } }

  (* [_ -> set x cx']: the cell raced ahead of us; retry likewise. *)
  rewrite {2}(@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem; content].
  iIntros "Hm".
  iApply ("Hm" $! v Ψ with "Hinv [$] Hcx' Hhook").
Qed.

(* The public, one-argument [set x v]: allocates the fresh
   [Root { value = v }] and calls the helper above. *)

Lemma set_wrapper_proof γ η :
  in_env "set"
    (λ setv, □ iSpec τ[elem; content] setv (set_content_spec γ)) η -∗
  EWP (eval η (EAnonFun __set))
    {{ c, □ iSpec τ[elem; val] c (set_aux_spec γ) }}.
Proof.
  iIntros "#ISet".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x v Ψ).
  iIntros "#Hinv #Hx Hhook".
  iApply imp_please; iNext.

  (* [let cx' = Root { value = v } in set x cx']. *)
  imp_let $! (λ c, fresh_root c v)%I.
  { imp_record $! root_fields.
    simpl. iIntros (c) "H".
    iDestruct "H" as (r) "(-> & %xs & Hown & ->)".
    iApply "Hown". }
  iIntros (cx') "Hco".
  imp_app τ[elem; content].
  iIntros "Hm".
  iApply ("Hm" $! v Ψ with "Hinv Hx Hco Hhook").
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [update]. *)

(* [update x f] replaces the value of [x]'s class by [f] applied to it.

   [f] is described by an arbitrary relation [Φf] between its argument
   and its result. Its specification must be persistent. *)

Definition update_hook (γ : uf_names) (x : elem)
    (Φf : val → val → iProp Σ) (Ψ : iProp Σ) : iProp Σ :=
  ∀ D (R : elem → elem) (V : elem → val) (w : val),
    Φf (V x) w -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V.[x -/R/> w] ∗ Ψ.

Lemma update_hook_rebase γ x z Φf Ψ :
  same_class γ x z -∗ update_hook γ x Φf Ψ -∗ update_hook γ z Φf Ψ.
Proof.
  iIntros "#Hxz Hhook" (D R V w) "HΦf Hst".
  iDestruct (UF_same_class_eq with "Hst Hxz") as "[%Heq Hst]".
  iDestruct (UF_val_congr with "Hst") as %Hcongr.
  rewrite -(update_class_congr_class R x z V w Heq).
  iApply ("Hhook" with "[HΦf] Hst").
  rewrite (Hcongr x z Heq). iExact "HΦf".
Qed.

Definition update_aux_spec (γ : uf_names) (x : elem) (f : val)
    (m : microvx) : iProp Σ :=
  ∀ (Φf : val → val → iProp Σ) (Ψ : iProp Σ),
    □ iSpec τ[val] f (λ v m', EWP m' {{ (w : val), Φf v w }}) -∗
    is_uf γ -∗
    in_uf γ x -∗
    update_hook γ x Φf Ψ -∗
    EWP m {{ (_ : unit), Ψ }}.

Definition update_spec (γ : uf_names) (x : elem) (f : val)
    (m : microvx) : iProp Σ :=
  ∀ (Φf : val → val → iProp Σ),
    □ iSpec τ[val] f (λ v m', EWP m' {{ (w : val), Φf v w }}) -∗
    is_uf γ -∗
    in_uf γ x -∗
    <<{ ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
      m @ ↑ufN
    <<{ ∃∃ w : val, Φf (V x) w ∗ UF γ D R V.[x -/R/> w] | RET tt }>>.

Lemma update_atomic_spec γ x f m :
  update_aux_spec γ x f m -∗ update_spec γ x f m.
Proof.
  iIntros "Hspec" (Φf) "#Hf #Hinv #Hx".
  iIntros (Φ) "AU".
  iApply (imp_wand _ _ _ _ (λ _ : unit, Φ tt)%I _ with "[Hspec AU]"); last first.
  { iIntros ([]) "H". iExact "H". }
  iApply ("Hspec" $! Φf (Φ tt) with "Hf Hinv Hx [AU]").
  iIntros (D R V w) "HΦf Hst".
  iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
  iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
  iDestruct (UF_val_congr with "Hst") as %Hcongr.
  iDestruct (UF_dethroned with "Hst") as "#Hdeth".
  iMod (UF_update_2 _ _ _ _ D R V.[x -/R/> w] with "Hdeth Hst Hcl") as "[Hst Hcl]";
    [done | by apply uf_val_congr_set |].
  iMod ("Hcommit" $! w with "[$HΦf $Hcl]") as "HΦ".
  by iFrame "Hst HΦ".
Qed.

Lemma update_proof γ η :
  ▷ in_env "update"
      (λ update, □ iSpec τ[elem; val] update (update_aux_spec γ)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (find_aux_spec γ)) η -∗
  in_env "cas"
    compare_and_set_spec η -∗
  □ fun_spec.predicate_over_function_body τ[elem; val] (update_aux_spec γ) η
      (EAnonFun (AnonFun "x" (EAnonFun __update_fun))).
Proof.
  iIntros "#IUpdate #IFindc #Hcas".
  iIntros "!> /=".
  iIntros (x f).
  unfold update_aux_spec at 2.
  iIntros (Φf Ψ) "#Hf #Hinv #Hx Hhook".
  iApply imp_please; iNext.

  (* [let x = findc x in ...]: an observer call, as in [get] and [set]. *)
  iApply (imp_ELet_var (B:=elem)
    (λ z : elem, in_uf γ z ∗ same_class γ x z)%I with "[]").
  { imp_app τ[elem].
    iIntros "Hm".
    iApply (find_observe with "Hm Hinv Hx"). }
  iIntros (z) "[#Hz #Hxz]".
  iDestruct "Hz" as (j) "#Hzv".
  iDestruct (update_hook_rebase with "Hxz Hhook") as "Hhook".

  (* [let cx = x.content in ...]. *)
  imp_let $! (λ c : content, content_info γ z c)%I.
  { iApply (read_vertex with "Hinv Hzv"). imp_path. }
  iIntros (cx) "#Hcx".

  imp_match content with "[]".
  destruct cx as [rc|rc]; simpl.

  { (* [Root { value = v } -> ...] *)
    iDestruct "Hcx" as "(#HrcP & (%v & #Hrv))".
    rewrite {3}(@encode_encode' content).
    next_branch.
    iDestruct "Hrv" as (lv) "(#Hrclocs & _ & #Hlv)".
    iApply (ipat_PRecord_pers ⊤ _ _ _ 0%Z rc _ _ v with "[] Hlv [Hhook]");
      first (iModIntro; iApply (blockLocs_field_at with "Hrclocs"); done).
    iNext. iIntros "_".

    (* [if cas [%atomic.loc x.content] cx (Root { value = f v})]. *)
    imp_if with "[Hhook]".
    { set_postcondition
        (λ res : bool, if res then Ψ else update_hook γ z Φf Ψ)%I.
      imp_app τ[loc;content;content].
      { iApply (vertex_content_ptr with "Hzv"). imp_path. }
      { (* The CAS's third argument: call [f] and wrap its result in a
           fresh [Root]. This is where the attempt's [Φf v w] is born. *)
        set_postcondition
          (λ c : content, ∃ (rcn : record) (w : val),
             ⌜c = CtRoot rcn⌝ ∗ rcn ⤇ {| root_value := w |} ∗ Φf v w)%I.
        imp_record $! root_fields.
        { set_postcondition (λ w : val, Φf v w)%I.
          imp_app τ[val].
          iIntros "Hm". iApply "Hm". }
        iIntros (c) "(%r' & -> & %xs & Hown & HΦf)".
        iExists r', xs. iSplit; first done. iFrame "HΦf Hown". }
      iIntros "Hptr (%rcn & %w & -> & Hrcn & HΦf) Hm".
      iApply ("Hm" $! (⊤ ∖ ↑ufN)).
      iNext.
      (* The attempt's [Φf v w] rides along with the hook as the CAS's
         linearization resources: spent together on success, dropped
         together on failure. *)
      iApply (uf_cas_set_fupd _ z j _ rc rcn v w
                (update_hook γ z Φf Ψ ∗ Φf v w)%I Ψ
                (λ res : bool, if res then Ψ else update_hook γ z Φf Ψ)%I
                with "Hinv Hzv Hptr [] Hrcn [Hhook HΦf] [] []").
      { by iFrame "Hrclocs Hlv". }
      { by iFrame "Hhook HΦf". }
      { (* The main difference with the proof of [set]: the CAS reports
           [V z = v] against the state at the linearization point. *)
        iIntros "!>" (D R V) "%Hroot %Hval [Hhook HΦf] Hst".
        iApply ("Hhook" $! D R V w with "[HΦf] Hst").
        rewrite Hval. iExact "HΦf". }
      { iIntros "!>" ([|]) "H";
          [iExact "H" | by iDestruct "H" as "[[$ _] _]"]. } }

    { (* CAS succeeded: the hook has already produced the postcondition. *)
      iIntros "HΨ". iApply (imp_EUnit with "HΨ"). }
    { (* CAS failed: retry on the vertex [findc] found, with the hook
         handed back. *)
      iIntros "Hhook".
      imp_app τ[elem; val].
      iIntros "Hm".
      iApply ("Hm" $! Φf Ψ with "Hf Hinv [$] Hhook"). } }

  (* [_ -> update x f]: the cell raced ahead of us; retry likewise. *)
  rewrite {3}(@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem; val].
  iIntros "Hm".
  iApply ("Hm" $! Φf Ψ with "Hf Hinv [$] Hhook").
Qed.

(* ------------------------------------------------------------------------ *)
(* Specification of [union]. *)

(* The abstract transition mirrors the sequential [union_spec]
   (UnionFind.v), which redirects both classes to a common root and
   reports [⌜z = R x ∨ z = R y⌝]. *)

Definition union_post (γ : uf_names) (D : gset elem) (R : elem → elem)
    (V : elem → val) (x y : elem) (o : option val) : iProp Σ :=
  match o with
  | None => ⌜R x = R y⌝ ∗ UF γ D R V
  | Some v =>
      ∃ b c : elem,
        ⌜(b = x ∧ c = y) ∨ (b = y ∧ c = x)⌝ ∗
        ⌜R x ≠ R y⌝ ∗ ⌜v = V b⌝ ∗
        UF γ D R.[b -/R/> R c] V.[b -/R/> V c]
  end.

(* Here, there is a pair of linearization points as hooks, one per
   outcome. *)

Definition union_hook (γ : uf_names) (x y : elem)
    (Ψ : option val → iProp Σ) : iProp Σ :=
  (* Nothing to do: the two are already in one class. *)
  (∀ D (R : elem → elem) (V : elem → val), ⌜R x = R y⌝ -∗
     UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V ∗ Ψ None)
  ∧
  (* The merge: [dethroned] for the state being moved to. *)
  (∀ D (R : elem → elem) (V : elem → val) b c,
     ⌜(b = x ∧ c = y) ∨ (b = y ∧ c = x)⌝ -∗ ⌜R x ≠ R y⌝ -∗
     dethroned γ R.[b -/R/> R c] -∗
     UF γ D R V ={⊤ ∖ ↑ufN}=∗
     UF γ D R.[b -/R/> R c] V.[b -/R/> V c] ∗
     same_class γ b c ∗ Ψ (Some (V b))).

Definition union_aux_spec (γ : uf_names) (x y : elem) (m : microvx) : iProp Σ :=
  ∀ (Ψ : option val → iProp Σ),
    is_uf γ -∗
    in_uf γ x -∗ in_uf γ y -∗
    union_hook γ x y Ψ -∗
    EWP m {{ Ψ }}.

(* Re-basing a hook onto other members of the same two classes:
   after an unsuccesfful CAS the call restarts on the vertices its
   traversals reached, and the hook it is carrying speaks of the
   original arguments. *)

Lemma union_hook_rebase γ x y a b Ψ :
  same_class γ x a -∗ same_class γ y b -∗
  union_hook γ x y Ψ -∗ union_hook γ a b Ψ.
Proof.
  iIntros "#Hxa #Hyb Hhook".
  iSplit.
  - iIntros (D R V) "%Hab Hst".
    iDestruct (UF_same_class_eq with "Hst Hxa") as "[%Hx Hst]".
    iDestruct (UF_same_class_eq with "Hst Hyb") as "[%Hy Hst]".
    iDestruct "Hhook" as "[Hnone _]".
    iApply ("Hnone" with "[%] Hst"). congruence.
  - iIntros (D R V b' c') "%Hdir %Hne #Hdeth' Hst".
    iDestruct (UF_same_class_eq with "Hst Hxa") as "[%Hx Hst]".
    iDestruct (UF_same_class_eq with "Hst Hyb") as "[%Hy Hst]".
    iDestruct (UF_val_congr with "Hst") as %Hcongr.
    iDestruct "Hhook" as "[_ Hsome]".
    assert (Hne' : R x ≠ R y) by congruence.
    destruct Hdir as [[-> ->] | [-> ->]].
    + rewrite -(update_class_congr_class R x a R (R b) Hx).
      rewrite -(update_class_congr_class R x a V (V b) Hx).
      rewrite -Hy -(Hcongr y b Hy) -(Hcongr x a Hx).
      iMod ("Hsome" $! D R V x y with "[%] [%] Hdeth' Hst")
        as "(Hst & #Hxy & HΨ)"; [by left | done |].
      iModIntro. iFrame "Hst HΨ".
      iDestruct (same_class_sym with "Hxa") as "#Hax".
      iDestruct (same_class_trans with "Hax Hxy") as "#Hay".
      iApply (same_class_trans with "Hay Hyb").
    + rewrite -(update_class_congr_class R y b R (R a) Hy).
      rewrite -(update_class_congr_class R y b V (V a) Hy).
      rewrite -Hx -(Hcongr x a Hx) -(Hcongr y b Hy).
      iMod ("Hsome" $! D R V y x with "[%] [%] Hdeth' Hst")
        as "(Hst & #Hyx & HΨ)"; [by right | done |].
      iModIntro. iFrame "Hst HΨ".
      iDestruct (same_class_sym with "Hyb") as "#Hby".
      iDestruct (same_class_trans with "Hby Hyx") as "#Hbx".
      iApply (same_class_trans with "Hbx Hxa").
Qed.

(* The specification as a client sees it. *)

Definition union_spec (γ : uf_names) (x y : elem) (m : microvx) : iProp Σ :=
  is_uf γ -∗
  in_uf γ x -∗ in_uf γ y -∗
  <<{ ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    m @ ↑ufN
  <<{ ∃∃ o : option val, union_post γ D R V x y o | RET o }>>.

Lemma union_atomic_spec γ x y m :
  union_aux_spec γ x y m -∗ union_spec γ x y m.
Proof.
  iIntros "Hspec #Hinv #Hx #Hy" (Φ) "AU".
  iApply ("Hspec" $! Φ with "Hinv Hx Hy").
  iSplit.
  - (* [None]: the state does not move, so the atomic update is committed
       with the state it was offered. *)
    iIntros (D R V) "%Heq Hst".
    iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
    iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
    iMod ("Hcommit" $! None with "[$Hcl]") as "HΦ"; first done.
    by iFrame "Hst HΦ".
  - iIntros (D R V b c) "%Hdir %Hne #Hdeth' Hst".
    iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
    iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
    iDestruct (UF_val_congr with "Hst") as %Hcongr.
    iMod (UF_update_2 _ _ _ _ D R.[b -/R/> R c] V.[b -/R/> V c]
            with "Hdeth' Hst Hcl") as "[Hst Hcl]".
    { intros u w. apply update_class_R_congr. }
    { by apply uf_val_congr_link. }
    iMod (UF_same_class_update _ _ _ _ b c with "Hst Hcl")
      as "(Hst & Hcl & #Hbc)".
    { rewrite /update_class /fcupdate; repeat case_decide; done. }
    iMod ("Hcommit" $! (Some (V b)) with "[Hcl]") as "HΦ".
    { iExists b, c. by iFrame "Hcl". }
    by iFrame "Hst Hbc HΦ".
Qed.

Lemma union_proof γ η :
  ▷ in_env "union"
      (λ union, □ iSpec τ[elem; elem] union (union_aux_spec γ)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (find_aux_spec γ)) η -∗
  in_env "cas"
    compare_and_set_spec η -∗
  □ fun_spec.predicate_over_function_body τ[elem; elem] (union_aux_spec γ) η
      (EAnonFun (AnonFun "x" (EAnonFun __union_fun))).
Proof.
  iIntros "#IUnion #IFindc #Hcas".
  iIntros "!> /=".
  iIntros (x y).
  unfold union_aux_spec at 2.
  iIntros (Ψ) "#Hinv #Hx #Hy Hhook".
  iApply imp_please; iNext.

  (* [let x = findc x and y = findc y in ...] *)
  imp_let $! (λ z : elem, in_uf γ z ∗ same_class γ x z)%I
          $! (λ z : elem, in_uf γ z ∗ same_class γ y z)%I.
  { imp_app τ[elem].
    iIntros "Hm".
    iApply (find_observe with "Hm Hinv Hx"). }
  { imp_app τ[elem].
    iIntros "Hm".
    iApply (find_observe with "Hm Hinv Hy"). }
  iIntros (a b) "[#Ha #Hxa] [#Hb #Hyb]".
  iDestruct "Ha" as (i') "#Hav".
  iDestruct "Hb" as (j') "#Hbv".

  (* Re-base the hook onto the vertices the traversals reached. *)
  iDestruct (union_hook_rebase with "Hxa Hyb Hhook") as "Hhook".
  iDestruct (vertex_mut with "Hav") as "#HaP".
  iDestruct (vertex_mut with "Hbv") as "#HbP".
  iClear "Hx Hxa Hy Hyb".

  (* [if x == y then None else ...]. *)
  imp_if.
  { (* [x == y]. *)
    set_postcondition
    (λ res : bool, if res then ⌜a = b⌝ else ⌜a ≠ b⌝)%I.
    iApply (imp_EOpPhysEq_record _ _ _ (λ l : record, ⌜l = a⌝)%I
                                       (λ l : record, ⌜l = b⌝)%I _ Mut Mut).
    { auto. }
    { imp_path. equality. }
    { imp_path. equality. }
    { iIntros "!>" (l1 l2) "-> ->".
      by destruct (locations.eqb_spec a b) as [->|Hneq]. } }

  { (* Case: [a = b]. The two arguments were already equivalent and
       nothing needs to happen. *)
    iIntros "->".
    iDestruct "Hhook" as "[Hnone _]".
    iMod (uf_same_class_commit with "Hinv [] [] Hnone") as "HΨ";
      [iApply same_class_refl | iApply same_class_refl |].
    iApply (imp_EConstant' with "[HΨ]"). iExact "HΨ". }

  (* Case: [a ≠ b]. *)
  iIntros "%Heq".
  (* [assert (x.id <> y.id)]. *)
  iMod (vertex_ids_ne with "Hinv Hav Hbv") as %(Hij & Hrepi & Hrepj);
    first exact Heq.

  imp_match unit with "[]".
  { iApply (imp_EAssert (R:=True%I)).
    iSplit; first done.
    iApply (imp_wand with "[]").
    iApply (imp_EOpNe_Z _ _ _ i' j' with "[Hav] [Hbv]"); try eassumption.
    - iApply (read_vertex_id with "Hav"). imp_path.
    - iApply (read_vertex_id with "Hbv"). imp_path.
    - iPureIntro. simpl. intros b' Hneq. split; last done.
      destruct b'; lia. }
  iIntros "%HR".
  destruct a0. next_branch.

  (* [if x.id > y.id then ...]. *)
  imp_if.
  { iApply (imp_EOpGt_Z _ _ _ i' j'); try assumption.
    { iApply (read_vertex_id with "Hav"). imp_path. }
    { iApply (read_vertex_id with "Hbv"). imp_path. } }

  { iIntros "%Hcmp2".
    assert (Hlt : (j' < i')%Z) by lia.
    imp_let $! (λ c, content_info γ a c).
    { iApply (read_vertex with "Hinv Hav"). imp_path. }
    iIntros (cx) "#Hcx".

    (* [match cx with ...]. *)
    imp_match content with "[]".
    destruct cx as [rc|rc]; simpl.

    { (* [Root {v} -> if cas x.content cx (Link {parent = y}) ...] *)
      iDestruct "Hcx" as "(#HrcP & (%v & #Hrv))".
      rewrite {3}(@encode_encode' content). next_branch.

      (* Read the absorbed root's payload. Its field is immutable and the
         invariant has discarded its fraction, so this opens nothing. *)
      iDestruct "Hrv" as (lv) "(#Hrclocs & _ & #Hlv)".
      iApply (ipat_PRecord_pers ⊤ _ _ _ 0%Z rc _ _ v with "[] Hlv [Hhook]");
        first (iModIntro; iApply (blockLocs_field_at with "Hrclocs"); done).
      iNext. iIntros "_".

      imp_if with "[Hhook]".
      { set_postcondition
          (λ res : bool, if res then Ψ (Some v) else union_hook γ a b Ψ)%I.
        imp_app τ[loc;content;content].
        { iApply (vertex_content_ptr with "Hav"). imp_path. }
        { set_postcondition
            (λ c : content, ∃ rcn, ⌜c = CtLink rcn⌝ ∗
                                   rcn ⤇ {| link_parent := b |})%I.
          imp_record $! link_fields.
          iIntros (c) "(%r' & -> & %xs & Hown & ->)".
          by iFrame "Hown". }
        iIntros "Hptr (%rcn & -> & Hrcn) Hm".
        iApply ("Hm" $! (⊤ ∖ ↑ufN)).
        iNext.
        iApply (uf_cas_link_fupd _ a b i' j' _ rc rcn v
                  (union_hook γ a b Ψ) (Ψ (Some v))
                  (λ res : bool, if res then Ψ (Some v) else union_hook γ a b Ψ)
                  with "Hinv Hav Hptr [] Hbv Hrcn Hhook [] []").
        { lia. }
        { iExists lv. by iFrame "Hrclocs Hlv". }
        { (* Hook and CAS now speak of the same two vertices, so this is a
             hand-over with nothing to re-index. *)
          iNext. iIntros (D R V) "%Hax %Hne %Hval #Hdeth' Hhook Hst".
          iDestruct "Hhook" as "[_ Hsome]".
          iMod ("Hsome" $! D R V a b with "[%] [%] Hdeth' Hst")
            as "($ & #Hab & HΨ)".
          { by left. }
          { done. }
          iFrame "Hab". rewrite Hval. by iModIntro. }
        { iNext. iIntros ([|]) "H"; [iExact "H" | by iDestruct "H" as "[$ _]"]. } }

      { iIntros "HΨ".
        (* CAS succeeded: the hook has already produced the whole
           postcondition, for the value the [Root] record held. *)
        imp_data.
        2: { iIntros (w) "H". iExact "H". }
        iExact "HΨ". }
      { iIntros "Hhook".
        (* CAS failed: retry on the vertices [findc] found. *)
        imp_app τ[elem; elem].
        iIntros "Hm3".
        iApply ("Hm3" $! Ψ with "Hinv [] [] Hhook").
        { by iExists i'. }
        { by iExists j'. } } }

    { (* [_ -> union x y]: the cell raced ahead of us. *)
      rewrite {3}(@encode_encode' content).
      next_branch.
      next_branch.
      imp_app τ[elem; elem].
      iIntros "Hm3".
      iApply ("Hm3" $! Ψ with "Hinv [] [] Hhook").
      { by iExists i'. }
      { by iExists j'. } } }

  { (* [x.id <= y.id]: the mirror image. *)
    iIntros "%Hcmp2".
    assert (Hlt : (i' < j')%Z) by lia.
    imp_let $! (λ c : content, content_info γ b c).
    { iApply (read_vertex with "Hinv Hbv"). imp_path. }
    iIntros (cy) "#Hcy".

    imp_match content with "[]".
    destruct cy as [rc|rc]; simpl.

    { iDestruct "Hcy" as "(#HrcP & (%v & #Hrv))".
      rewrite {3}(@encode_encode' content).
      next_branch.

      iDestruct "Hrv" as (lv) "(#Hrclocs & _ & #Hlv)".
      iApply (ipat_PRecord_pers ⊤ _ _ _ 0%Z rc _ _ v with "[] Hlv [Hhook]");
        first (iModIntro; iApply (blockLocs_field_at with "Hrclocs"); done).
      iNext. iIntros "_".

      imp_if with "[Hhook]".
      { set_postcondition
          (λ res : bool, if res then Ψ (Some v) else union_hook γ a b Ψ)%I.
        imp_app τ[loc;content;content].
        { iApply (vertex_content_ptr with "Hbv"). imp_path. }
        { set_postcondition
            (λ c : content, ∃ rcn, ⌜c = CtLink rcn⌝ ∗
                                   rcn ⤇ {| link_parent := a |})%I.
          imp_record $! link_fields.
          iIntros (c) "(%r' & -> & %xs & Hown & ->)".
          iExists r'. iSplit; first done. iApply "Hown". }
        iIntros "Hptr (%rcn & -> & Hrcn) Hm".
        iApply ("Hm" $! (⊤ ∖ ↑ufN)).
        iNext.
        iApply (uf_cas_link_fupd _ b a j' i' _ rc rcn v
                  (union_hook γ a b Ψ) (Ψ (Some v))
                  (λ res : bool, if res then Ψ (Some v) else union_hook γ a b Ψ)
                  with "Hinv Hbv Hptr [] Hav Hrcn Hhook [] []").
        { lia. }
        { iExists lv. by iFrame "Hrclocs Hlv". }
        { (* The mirror image: here it is [b]'s class that is absorbed. *)
          iNext. iIntros (D R V) "%Hby %Hne %Hval #Hdeth' Hhook Hst".
          iDestruct "Hhook" as "[_ Hsome]".
          iMod ("Hsome" $! D R V b a with "[%] [%] Hdeth' Hst")
            as "($ & #Hba & HΨ)".
          { by right. }
          { by intros ?. }
          iFrame "Hba". rewrite Hval. by iModIntro. }
        { iNext. iIntros ([|]) "H"; [iExact "H" | by iDestruct "H" as "[$ _]"]. } }

      { iIntros "HΨ".
        imp_data.
        2: { iIntros (w) "H". iExact "H". }
        iExact "HΨ". }
      { iIntros "Hhook".
        imp_app τ[elem; elem].
        iIntros "Hm3".
        iApply ("Hm3" $! Ψ with "Hinv [] [] Hhook").
        { by iExists i'. }
        { by iExists j'. } } }

    { rewrite (@encode_encode' content).
      next_branch.
      next_branch.
      imp_app τ[elem; elem].
      iIntros "Hm3".
      iApply ("Hm3" $! Ψ with "Hinv [] [] Hhook").
      { by iExists i'. }
      { by iExists j'. } } }
Qed.

(* The public wrapper:
   [union x y = if x == y then None else union x y]. *)

Lemma union_wrapper_proof γ η :
  in_env "union" (λ union, □ iSpec τ[elem; elem] union (union_spec γ)) η -∗
  EWP (eval η (EAnonFun __union))
    {{ c, □ iSpec τ[elem; elem] c (union_spec γ) }}.
Proof.
  iIntros "#IUnion".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x y).
  unfold union_spec.
  iIntros "#Hinv #Hx #Hy".
  iIntros (Φ) "AU".
  iApply imp_please; iNext.
  iDestruct "Hx" as (i) "#Hxv".
  iDestruct "Hy" as (j) "#Hyv".
  iDestruct (vertex_mut with "Hxv") as "#HxP".
  iDestruct (vertex_mut with "Hyv") as "#HyP".
  iApply imp_fupd.
  imp_if.
  { set_postcondition
      (λ res : bool, if res then ⌜x = y⌝ else ⌜x ≠ y⌝)%I.
    iApply (imp_EOpPhysEq_record _ _ _ (λ l : record, ⌜l = x⌝)%I
                                       (λ l : record, ⌜l = y⌝)%I _ Mut Mut).
    { auto. }
    { imp_path. equality. }
    { imp_path. equality. }
    { iIntros "!>" (l1 l2) "-> ->".
      by destruct (locations.eqb_spec x y) as [->|Hneq]. } }

  { (* [x == y]: the two arguments are one vertex, so they are equivalent
       and nothing has to happen. *)
    iIntros "->".
    iApply (imp_wand with "[]").
    { imp_constant. }
    iIntros (v) "->". simpl.
    iMod "AU" as (D R V) "[Hst [_ Hcommit]]".
    iMod ("Hcommit" $! None with "[$Hst]") as "HΦ"; first done.
    by iModIntro. }

  iIntros "%Hne".
  imp_app τ[elem; elem].
  iIntros "Hm".
  iApply ("Hm" with "Hinv [] [] [AU]").
  { by iExists i. }
  { by iExists j. }

  iApply (atomic_update_mono with "[] AU").
  iIntros "!>" (D R V o) "H". by iModIntro.
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [eq]. *)

(* [eq x y] decides whether [x] and [y] are in the same class.

   We prove the following specification:

     RET b, with ⌜b = true ↔ R x = R y⌝.

   [eq] has a future-dependent linearization point (at the second call
   to [findc]). Iris's tool for future-dependent linearization points
   is a prophecy variables. We instrument the OCaml source with one per
   iteration, created before the two traversals. We resolve the
   prophecy with the value the [x.content] read returns.

   The proof consults the prediction and commits [false] only in the
   branch the resolution will later confirm.

   Three things have to line up for that commit, and each is decided
   against the state the callee exposes at its own linearization point:

   - [a ≠ findc y], which we decide by a physical equality test.
   - the prediction says [Root], so the run will indeed answer [false]
     here rather than loop.
   - [R a = a], so that [R x = R a = a ≠ z = R y]. If instead [R a ≠ a],
     the state's own [dethroned] hands over a [linked γ a rc lp], and the
     run will loop and the update is kept.

   In the other case, where [x = findc y], we just commit [true] after
   the [a == b] test. *)

(* The prophecy's prediction, in the form the linearization point needs:
   will the [x.content] read that is still to come report a [Root]?

   [proph_root_content] ties it to the value the read actually returns. *)

Definition proph_root (pvs : list (val * val)) : bool :=
  match pvs with
  | (VInline t _, _) :: _ => bool_decide (t = "Root")
  | _ => false
  end.

Lemma proph_root_content (c : content) (v : val) pvs :
  proph_root ((#c, v) :: pvs) = content_root c.
Proof. destruct c; rewrite encode_encode'; by vm_compute. Qed.

(* The specification as a client sees it. *)

Definition eq_au (γ : uf_names) (x y : elem) (Φ : bool → iProp Σ) : iProp Σ :=
  AU <{ ∃∃ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>
    @ ⊤ ∖ ↑ufN, ∅
  <{ ∀∀ b : bool, ⌜b = true ↔ R x = R y⌝ ∗ UF γ D R V , COMM Φ b }>.

Definition eq_spec (γ : uf_names) (x y : elem) (m : microvx) : iProp Σ :=
  is_uf γ -∗
  in_uf γ x -∗ in_uf γ y -∗
  <<{ ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    m @ ↑ufN
  <<{ ∃∃ b : bool, ⌜b = true ↔ R x = R y⌝ ∗ UF γ D R V | RET b }>>.

Definition eq_kont (γ : uf_names) (a z : elem) (pvs : list (val * val))
    (P : iProp Σ) (Φ : bool → iProp Σ) : iProp Σ :=
  (⌜a ≠ z⌝ ∗ ⌜proph_root pvs = true⌝ ∗ Φ false)
  ∨ ((⌜a = z⌝ ∨ ⌜proph_root pvs = false⌝ ∨ ∃ rc lp, linked γ a rc lp) ∗ P).

(*
   Proof outline:
   1. [let p = Proph.create ()]: create a fresh prediction, before the
      traversals, so that it is in hand at [findc y]'s linearization
      point.
   2. [let x = findc x]: just a read.
   3. [let y = findc y]: the linearization point of a [false] answer. The
      update is handed down and, if the three conditions above line up,
      we commit the update and we get [eq_kont] back.
   4. [x == y || ...]: if they are equal the two chains have met,
      [eq_kont]'s committed branch is refuted by its own [a ≠ z],
      and the update is commited to [true].
   5. [Root _ -> false]: the answer was committed in step 3.
   6. [Link { parent = x } -> eq x y]: in case of interference we retry
      from [x]'s parent. *)

Lemma eq_proof γ η :
  ▷ in_env "eq" (λ eq, □ iSpec τ[elem; elem] eq (eq_spec γ)) η -∗
  ▷ in_env "findc" (λ findc, □ iSpec τ[elem] findc (find_spec γ)) η -∗
  □ fun_spec.predicate_over_function_body τ[elem; elem] (eq_spec γ) η
      (EAnonFun (AnonFun "x" (EAnonFun __eq_fun))).
Proof.
  iIntros "#IEq #IFindc".
  iIntros "!> /=".
  iIntros (x y).
  unfold eq_spec at 2.
  iIntros "#Hinv #Hx #Hy".
  iIntros (Φ) "AU".
  iApply imp_please; iNext.

  (* [let p = Proph.create () in ...] *)
  imp_let $! (λ q : proph_id, ∃ pvs, proph q pvs)%I.
  { iApply imp_ENewProph. iIntros "!>" (q pvs) "$". }
  iIntros (p) "[%pvs Hp]".

  (* [let x = findc x in ...]. *)
  iApply (imp_ELet_var (B:=elem)
    (λ z : elem, (in_uf γ z ∗ same_class γ x z) ∗ eq_au γ x y Φ)%I
    with "[AU]").
  { imp_app τ[elem]. iIntros "Hm".
    iApply ("Hm" with "Hinv Hx [AU]").
    iAuIntro.
    iApply (aacc_aupd with "AU"); first done.
    iIntros (D R V) "Hst".
    iAaccIntro with "Hst".
    { iIntros "Hst !>". iFrame "Hst". iIntros "AU !>". iFrame. }
    iIntros (z) "[-> Hst] !>".
    iLeft. iFrame "Hst". iIntros "AU !>". iIntros "[#Hin #Hsc]".
    iFrame "Hin Hsc". iFrame. }
  iIntros (a) "[[#Ha #Hxa] AU]".

  (* [let y = findc y in ...]: the potential lineraization point of the
     [false] case. *)
  iApply (imp_ELet_var
    (λ z : elem, (in_uf γ z ∗ same_class γ y z) ∗
                 proph p pvs ∗ eq_kont γ a z pvs (eq_au γ x y Φ) Φ)%I
    with "[AU Hp]").
  { imp_app τ[elem]. iIntros "Hm".
    iApply ("Hm" with "Hinv Hy [AU Hp]").
    iAuIntro.
    iApply (aacc_aupd with "AU"); first done.
    iIntros (D R V) "Hst".
    iAaccIntro with "Hst".
    { iIntros "Hst !>". iFrame "Hst". iIntros "AU !>". iFrame. }
    iIntros (z) "[-> Hst] !>".
    (* [R y] is the vertex the call is about to return. *)
    iDestruct (UF_same_class_eq with "Hst Hxa") as "[%Hxa' Hst]".
    destruct (decide (a = R y)) as [Heqz | Hnez].
    { (* The two traversals are in the same class: this iteration will
         answer [true]. Keep the update. *)
      iLeft. iFrame "Hst". iIntros "AU !>". iIntros "[#Hin #Hsc]".
      iFrame "Hin Hsc Hp". iRight. iFrame "AU". by iLeft. }
    destruct (proph_root pvs) eqn:Hpr; last first.
    { (* The read is predicted not to report a [Root], so this iteration
         will loop. Keep the update. *)
      iLeft. iFrame "Hst". iIntros "AU !>". iIntros "[#Hin #Hsc]".
      iFrame "Hin Hsc Hp". iRight. iFrame "AU". iRight. by iLeft. }
    destruct (decide (R a = a)) as [Hroot | Hnroot]; last first.
    { (* [a] has already been linked away. Root-ness being anti-monotone,
         the read cannot report a [Root] whatever the prediction says, so
         this iteration will loop too; keep the update and carry the
         witness that settles the read. *)
      iDestruct (UF_dethroned with "Hst") as "#Hdeth".
      iDestruct "Ha" as (ia) "#Hav".
      iDestruct ("Hdeth" with "Hav [//]") as "#Hlk".
      iLeft. iFrame "Hst". iIntros "AU !>". iIntros "[#Hin #Hsc]".
      iFrame "Hin Hsc Hp". iRight. iFrame "AU". iRight. iRight.
      iExact "Hlk". }
    (* Finally: [a] is a root of this state and [R y] is
       another, so [R x = R a = a ≠ R y]. Commit [false] here. *)
    iRight. iExists false.
    iSplitL "Hst".
    { iFrame "Hst". iPureIntro. split; first discriminate.
      intros Hbad. destruct Hnez. by rewrite -Hroot -Hxa' Hbad. }
    iIntros "HΦ !>". iIntros "[#Hin #Hsc]".
    iFrame "Hin Hsc Hp". iLeft. by iFrame "HΦ". }
  iIntros (b) "[[#Hb #Hyb] [Hp Hkont]]".
  iDestruct "Ha" as (i') "#Hav".
  iDestruct "Hb" as (j') "#Hbv".

  (* Put the postcondition under a fupd. *)
  iApply imp_fupd.

  (* [x == y || ...].  *)
  iDestruct (vertex_mut with "Hav") as "#HaP".
  iDestruct (vertex_mut with "Hbv") as "#HbP".
  iApply (imp_EBoolDisj _ (λ bb : bool, if bb then ⌜a = b⌝ else ⌜a ≠ b⌝)%I).
  { iApply (imp_EOpPhysEq_record _ _ _ (λ l : record, ⌜l = a⌝)%I
                                       (λ l : record, ⌜l = b⌝)%I _ Mut Mut).
    { auto. }
    { imp_path. equality. }
    { imp_path. equality. }
    { iIntros "!>" (l1 l2) "-> ->".
      by destruct (locations.eqb_spec a b) as [->|Hneq]. } }
  iIntros ([|]) "Hcmp".

  { (* Case [a = b]. *)
    iDestruct "Hcmp" as %->.
    iDestruct "Hkont" as "[(%Hbad & _) | [_ AU]]"; first done.
    iDestruct (same_class_sym with "Hyb") as "#Hby".
    iDestruct (same_class_trans with "Hxa Hby") as "#Hxy".
    iMod "AU" as (D R V) "[Hst [_ Hcommit]]".
    iDestruct (UF_same_class_eq with "Hst Hxy") as "[%Heq Hst]".
    iMod ("Hcommit" $! true with "[$Hst]") as "HΦ".
    { iPureIntro. by rewrite Heq. }
    by iModIntro. }

  iDestruct "Hcmp" as %Hne.

  (* Re-shape what the linearization point left behind. *)
  iAssert (((⌜proph_root pvs = true⌝ ∗ Φ false)
            ∨ (⌜proph_root pvs = false⌝ ∗ eq_au γ x y Φ))
           ∨ (∃ rc lp, linked γ a rc lp) ∗ eq_au γ x y Φ)%I
    with "[Hkont]" as "Hkont".
  { iDestruct "Hkont" as "[(_ & %Hpr & HΦ) | [Hwhy AU]]".
    - iLeft. iLeft. by iFrame "HΦ".
    - iDestruct "Hwhy" as "[%Hab | [%Hpr | Hlk]]".
      + done.
      + iLeft. iRight. by iFrame "AU".
      + iRight. by iFrame "Hlk AU". }

  (* [match (x.content [@resolve p ()]) with]. *)
  imp_match content
    $! (λ c : content, content_info γ a c ∗
                       (if content_root c then Φ false else eq_au γ x y Φ))%I
    with "[Hp Hkont]".
  { (* [x.content [@resolve p ()]]: the resolution happens at the load of
       the content field. *)
    iApply (read_vertex_or_linked_resolve with "Hinv Hav Hkont Hp [] []").
    (* [p] and [()] are read off the environment, in no step. *)
    { reflexivity. } { reflexivity. }
    { imp_path. }
    iIntros (c pvs') "%Heqp _ [$ Hres]".
    assert (content_root c = proph_root pvs) as ->
           by (rewrite Heqp; symmetry; apply proph_root_content).
    iDestruct "Hres" as "[[Hres|Hres] | Hres]".
    - iDestruct "Hres" as "(-> & $)".
    - iDestruct "Hres" as "(-> & $)".
    - iDestruct "Hres" as "(-> & $)". }

  iIntros "Hc".
  destruct a0 as [rc|rc]; simpl.

  { (* [Root _ -> false]: the answer was committed at [findc y]'s
       linearization point. *)
    rewrite (@encode_encode' content). next_branch.
    iApply (imp_wand with "[]").
    { imp_constant. }
    iIntros (v) "-> !>". simpl. iDestruct "Hc" as "[_ $]". }

  (* [Link { parent = x } -> eq x y]. *)
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  iDestruct "Hc" as "[(_ & (%lp & #Hlk)) AU]".
  iDestruct (linked_locs with "Hlk") as "#Hlocs".
  iApply (ipat_PRecord_atomic (A:=elem) (⊤ ∖ ↑ufN)
            with "[] [AU]").
  { iModIntro. iApply (blockLocs_field_at with "Hlocs"). done. }
  iNext.
  iApply (uf_link_parent_acc with "Hinv Hav Hlk [AU]").
  iNext.
  iIntros (x' jx' Hjx') "#Hax' #Hx'v".
  iDestruct (same_class_trans with "Hxa Hax'") as "#Hxx'".
  imp_app τ[elem; elem].
  iIntros "Hm".
  iApply ("Hm" with "Hinv [] [] [AU]").
  { by iExists jx'. }
  { by iExists j'. }
  (* The recursive call is on [x'] and on the vertex [findc y] reached,
     while the atomic update is about [x] and [y]; both ends are
     conciled via equivalence class facts. *)
  iAuIntro.
  iApply (aacc_aupd with "AU"); first done.
  iIntros (D R V) "Hst".
  iDestruct (UF_same_class_eq with "Hst Hxx'") as "[%Heqx Hst]".
  iDestruct (UF_same_class_eq with "Hst Hyb") as "[%Heqy Hst]".
  iAaccIntro with "Hst".
  { iIntros "Hst !>". iFrame "Hst". iIntros "AU". by iModIntro. }
  iIntros (bb) "[%Hiff Hst] !>".
  iRight. iExists bb.
  iSplitL "Hst";
    first (iFrame "Hst"; iPureIntro; by rewrite Heqx Heqy).
  iIntros "H !> !>". iExact "H".
Qed.

(* The public wrapper [eq x y = x == y || eq x y]. *)

Lemma eq_wrapper_proof γ η :
  in_env "eq" (λ eq, □ iSpec τ[elem; elem] eq (eq_spec γ)) η -∗
  EWP (eval η (EAnonFun __eq))
    {{ c, □ iSpec τ[elem; elem] c (eq_spec γ) }}.
Proof.
  iIntros "#IEq".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x y).
  unfold eq_spec.
  iIntros "#Hinv #Hx #Hy".
  iIntros (Φ) "AU".
  iApply imp_please; iNext.
  iDestruct "Hx" as (i) "#Hxv".
  iDestruct "Hy" as (j) "#Hyv".
  iDestruct (vertex_mut with "Hxv") as "#HxP".
  iDestruct (vertex_mut with "Hyv") as "#HyP".
  iApply imp_fupd.
  iApply (imp_EBoolDisj _ (λ bb : bool, if bb then ⌜x = y⌝ else ⌜x ≠ y⌝)%I).
  { iApply (imp_EOpPhysEq_record _ _ _ (λ l : record, ⌜l = x⌝)%I
                                       (λ l : record, ⌜l = y⌝)%I _ Mut Mut).
    { auto. }
    { imp_path. equality. }
    { imp_path. equality. }
    { iIntros "!>" (l1 l2) "-> ->".
      by destruct (locations.eqb_spec x y) as [->|Hneq]. } }
  iIntros ([|]) "Hcmp".
  { iDestruct "Hcmp" as %<-.
    iMod "AU" as (D R V) "[Hst [_ Hcommit]]".
    iMod ("Hcommit" $! true with "[$Hst]") as "HΦ"; first done.
    by iModIntro. }
  iDestruct "Hcmp" as %Hne.
  imp_app τ[elem; elem].
  iIntros "Hm".
  iApply ("Hm" with "Hinv [] [] [AU]").
  { by iExists i. }
  { by iExists j. }

  iApply (atomic_update_mono with "[] AU").
  iIntros "!>" (D R V bb) "H". by iModIntro.
Qed.

(* ------------------------------------------------------------------------ *)
(* Module-level specification. *)

(* [G], the generator of unique identifiers: it uses [Sys.word_size],
   [Random.int]. Currently, the translator emits [MUnsupported] for it

   Its specification is therefore admitted here. We assume that [G]
   binds "fresh" to a function satisfying [fresh_spec], i.e. returning
   a unique identifier. This specification is unfortunately false, as
   finite machine integers means the identifier space could eventually
   be saturated. As this is quite an unrealistic means of failure, we
   simply admit the incorrect spec for now. *)

Lemma G_module_proof γ (η : env) :
  ⊢ EWP (eval_mexpr η MUnsupported)
    {{ (δ : env),
         in_env "fresh" (fresh_spec γ) δ }}.
Proof.
Admitted.

(* Weakening the composable specifications to the client-facing atomic
   triples. *)

Lemma get_atomic_iSpec γ c :
  iSpec τ[elem] c (get_aux_spec γ) -∗ iSpec τ[elem] c (get_spec γ).
Proof.
  iIntros "Hspec".
  iApply (iSpec_mono with "Hspec").
  iIntros (x m) "Hm". by iApply get_atomic_spec.
Qed.

Lemma set_atomic_iSpec γ c :
  iSpec τ[elem; val] c (set_aux_spec γ) -∗ iSpec τ[elem; val] c (set_spec γ).
Proof.
  iIntros "Hspec".
  iApply (iSpec_mono with "Hspec").
  iIntros (x v m) "Hm". by iApply set_atomic_spec.
Qed.

Lemma update_atomic_iSpec γ c :
  iSpec τ[elem; val] c (update_aux_spec γ) -∗ iSpec τ[elem; val] c (update_spec γ).
Proof.
  iIntros "Hspec".
  iApply (iSpec_mono with "Hspec").
  iIntros (x f m) "Hm". by iApply update_atomic_spec.
Qed.

Lemma union_atomic_iSpec γ c :
  iSpec τ[elem; elem] c (union_aux_spec γ) -∗ iSpec τ[elem; elem] c (union_spec γ).
Proof.
  iIntros "Hspec".
  iApply (iSpec_mono with "Hspec").
  iIntros (x y m) "Hm". by iApply union_atomic_spec.
Qed.

Definition ConcurrentUnionFind_names : gset var :=
  {["cas"; "SharedGeneratorOfUniqueIds"; "G"; "make"; "find"; "compress";
    "findc"; "get"; "set"; "update"; "union"; "eq"]}.

Theorem ConcurrentUnionFind_module_proof γ η :
  in_env "Atomic" atomic_module_spec η -∗
  EWP (eval_mexpr η __main)
    {{ context [
         var_spec "make"   (λ make,   □ iSpec τ[val] make (make_spec γ));
         var_spec "find"   (λ find,   □ iSpec τ[elem] find (find_spec γ));
         var_spec "findc"  (λ findc,  □ iSpec τ[elem] findc (find_spec γ));
         var_spec "get"    (λ get,    □ iSpec τ[elem] get (get_spec γ));
         var_spec "set"    (λ set,    □ iSpec τ[elem; val] set (set_spec γ));
         var_spec "update" (λ update, □ iSpec τ[elem; val] update (update_spec γ));
         var_spec "union"  (λ union,  □ iSpec τ[elem; elem] union (union_spec γ));
         var_spec "eq"     (λ eq,     □ iSpec τ[elem; elem] eq (eq_spec γ))
       ] ConcurrentUnionFind_names }}.
Proof.
  iIntros "#HAtomic".
  iApply imp_module.

  (* [let cas = Atomic.Loc.compare_and_set] *)
  iApply (imp_sitems_let compare_and_set_spec).
  { iApply cas_proof. iFrame "#". }
  iIntros (cas) "#Hcas".

  (* [module SharedGeneratorOfUniqueIds]: evaluated for its bindings only.
     It is [G] that [make] calls, and [G] shadows this [fresh]. *)
  iApply (imp_sitems_module (λ _ : env, True)%I).
  { iApply imp_module.
    iApply (imp_sitems_let (λ _ : record, True)%I).
    { iApply (imp_ref2' (λ _ : Z, True)%I).
      { iApply imp_wand; [ iApply imp_EInt | auto ]. }
      iIntros "!>" (a l) "_ _". done. }
    iIntros (next) "_".
    iApply (imp_sitems_let (λ _ : val, True)%I).
    { iApply imp_wand; [ iApply imp_EAnon_literal | auto ]. }
    iIntros (fresh) "_".
    iApply imp_sitems_nil. done. }
  iIntros (δS) "_".

  iApply (imp_sitems_module
            (λ δ : env,
               in_env "fresh" (fresh_spec γ) δ)%I).
  { iApply G_module_proof. }
  iIntros (δG) "HG".
  iDestruct "HG" as (fresh) "[%Hfresh #Hfresh]".

  (* [let make v = ...]: the only consumer of [G.fresh]. *)
  iApply (imp_sitems_let (λ make : val, □ iSpec τ[val] make (make_spec γ))%I).
  { iApply make_proof. iFrame "#". auto. }
  iIntros (make) "#Hmake".

  iApply (imp_sitems_letrec_iSpec τ[elem] (find_aux_spec γ)).
  { iIntros "!> #IH".
    iApply bi.intuitionistically_elim.
    iApply find_proof. iFrame "#". auto. }
  iIntros (find) "#Hfind".

  (* [let rec compress x z = ...] *)
  iApply (imp_sitems_letrec_iSpec τ[elem; elem] (compress_spec γ)).
  { iIntros "!> #IH".
    iApply bi.intuitionistically_elim.
    iApply compress_proof. iFrame "#". auto. }
  iIntros (compress) "#Hcompress".

  (* [let findc x = ...] *)
  iApply (imp_sitems_let (λ findc : val, □ iSpec τ[elem] findc (find_aux_spec γ))%I).
  { iApply findc_proof; (iFrame "#"; auto). }
  iIntros (findc) "#Hfindc".

  (* [let rec get x = ...] *)
  iApply (imp_sitems_letrec_iSpec τ[elem] (get_aux_spec γ)).
  { iIntros "!> #IH".
    iApply bi.intuitionistically_elim.
    iApply get_proof; (iFrame "#"; auto). }
  iIntros (get) "#Hget".

  (* [let rec set x cx' = ...] *)
  iApply (imp_sitems_letrec_iSpec τ[elem; content] (set_content_spec γ)).
  { iIntros "!> #IH".
    iApply bi.intuitionistically_elim.
    iApply set_proof; (iFrame "#"; auto). }
  iIntros (setc) "#Hsetc".

  (* [let set x v = ...]: the wrapper, which shadows the name. *)
  iApply (imp_sitems_let (λ set : val, □ iSpec τ[elem; val] set (set_aux_spec γ))%I).
  { iApply set_wrapper_proof; (iFrame "#"; auto). }
  iIntros (set) "#Hset".

  (* [let rec update x f = ...] *)
  iApply (imp_sitems_letrec_iSpec τ[elem; val] (update_aux_spec γ)).
  { iIntros "!> #IH".
    iApply bi.intuitionistically_elim.
    iApply update_proof; (iFrame "#"; auto). }
  iIntros (update) "#Hupdate".

  (* [let rec union x y = ...] *)
  iApply (imp_sitems_letrec_iSpec τ[elem; elem] (union_aux_spec γ)).
  { iIntros "!> #IH".
    iApply bi.intuitionistically_elim.
    iApply union_proof; (iFrame "#"; auto). }
  iIntros (unionr) "#Hunionr".

  (* The wrapper is stated against the atomic triple, so the recursive
     [union] is weakened to it first, putting a hypothesis of the
     premise's shape in context. *)
  iAssert (□ iSpec τ[elem; elem] unionr (union_spec γ))%I as "#Hunionr'".
  { iModIntro. by iApply union_atomic_iSpec. }

  (* [let union x y = if x == y then None else union x y] *)
  iApply (imp_sitems_let (λ union : val, □ iSpec τ[elem; elem] union (union_spec γ))%I).
  { iApply union_wrapper_proof; (iFrame "#"; auto). }
  iIntros (union) "#Hunion".

  (* [eq] is the one caller that hands its own update down, so it wants
     [findc] at the atomic triple. *)
  iAssert (□ iSpec τ[elem] findc (find_spec γ))%I as "#Hfindc'".
  { iModIntro. by iApply find_atomic_iSpec. }

  (* [let rec eq x y = ...] *)
  iApply (imp_sitems_letrec_iSpec τ[elem; elem] (eq_spec γ)).
  { iIntros "!> #IH".
    iApply bi.intuitionistically_elim.
    iApply eq_proof; (iFrame "#"; auto). }
  iIntros (eqr) "#Heqr".

  (* [let eq x y = x == y || eq x y] *)
  iApply (imp_sitems_let (λ eq : val, □ iSpec τ[elem; elem] eq (eq_spec γ))%I).
  { iApply eq_wrapper_proof; (iFrame "#"; auto). }
  iIntros (eq) "#Heq".

  (* The four remaining composable specifications are weakened to the
     triples the module exports. *)
  iAssert (□ iSpec τ[elem] find (find_spec γ))%I as "#Hfind'".
  { iModIntro. by iApply find_atomic_iSpec. }
  iAssert (□ iSpec τ[elem] get (get_spec γ))%I as "#Hget'".
  { iModIntro. by iApply get_atomic_iSpec. }
  iAssert (□ iSpec τ[elem; val] set (set_spec γ))%I as "#Hset'".
  { iModIntro. by iApply set_atomic_iSpec. }
  iAssert (□ iSpec τ[elem; val] update (update_spec γ))%I as "#Hupdate'".
  { iModIntro. by iApply update_atomic_iSpec. }

  (* Conclude: frame every exported specification out of the context.
     The hypothesis is named at each conjunct because [find] and [findc]
     satisfy the same specification, so [iFrame "#"] alone would pick
     whichever it met first and leave an impossible lookup behind. *)
  iApply imp_sitems_nil.
  rewrite /context /ConcurrentUnionFind_names /=.
  iSplit.
  { iPureIntro. rewrite /dom /dom_env /=. set_solver. }
  repeat iSplit;
    [ iFrame "Hmake" | iFrame "Hfind'" | iFrame "Hfindc'" | iFrame "Hget'"
    | iFrame "Hset'" | iFrame "Hupdate'" | iFrame "Hunion" | iFrame "Heq"
    | done ];
    auto.
Qed.

End ConcurrentUnionFind.
