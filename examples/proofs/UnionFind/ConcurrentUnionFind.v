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

Definition fresh_spec fresh : iProp Σ :=
  □ {{ ∀ γ; is_uf γ }}
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

Definition make_spec make : iProp Σ :=
  □ <<{ ∀ γ; is_uf γ
    | ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    make v : val @ ↑ufN
  <<{ ∃∃ x : elem, ⌜(x ∉ D) ∧ R x = x⌝ ∗ UF γ (D ∪ {[x]}) R V.[x -/R/> v]
    | RET x; in_uf γ x }>>.

(* Records allocated by this module must fit within [max_array_length]. *)
Hypothesis Hmax1 : (1 ≤ max_array_length)%Z.
Hypothesis Hmax2 : (2 ≤ max_array_length)%Z.

Lemma make_proof η :
  path_spec ["G"; "fresh"] fresh_spec η -∗
  EWP (eval η (EAnonFun __make)) {{ make_spec }}.
Proof.
  iIntros "#HG".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (v γ) "#Hinv".
  (* We are proving a logically atomic triple: introduce the atomic
     update [AU] and the abstract postcondition [Φ]. *)
  iIntros (Φ) "AU".
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

Definition find_spec find : iProp Σ :=
  □ <<{ ∀ γ; is_uf γ ∗ in_uf γ x
    | ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
    find x : elem @ ↑ufN
  <<{ ∃∃ z : elem, ⌜z = R x⌝ ∗ UF γ D R V
    | RET z; in_uf γ z ∗ same_class γ x z }>>.

(* Stating the triple as [UF γ D R V | RET (R x); …], with no [∃∃] binder
   and no equation, would make its atomic update literally the one
   [find_au] below asks for, and [find_atomic_spec] a bare [iExact "AU"].
   With the [∃∃] form the two have different shapes, so the triple has to
   re-package the update. *)

(* ------------------------------------------------------------------------ *)

(* The specification [find] is proved against, and the one its callers
   use: they are the same. What a caller hands over is its own atomic
   update, [find_au]; an observing caller, which linearizes nothing, hands
   over nothing. The two cases are the [op] parameter, after Zoo's
   [operation] variant (zoo_saturn/queue_mpmc_1.v:419). *)

Definition find_au (γ : uf_names) (x : elem) (Ψ : elem → iProp Σ) : iProp Σ :=
  AU <{ ∃∃ D (R : elem → elem) (V : elem → val), UF γ D R V }>
     @ ⊤ ∖ ↑ufN, ∅
  <{ UF γ D R V, COMM Ψ (R x) }>.

Definition find_pre (γ : uf_names) (x : elem)
    (op : option (elem → iProp Σ)) : iProp Σ :=
  match op with
  | None => True
  | Some Ψ => find_au γ x Ψ
  end.

Definition find_post (z : elem) (op : option (elem → iProp Σ)) : iProp Σ :=
  match op with
  | None => True
  | Some Ψ => Ψ z
  end.

(* At a linearization point the atomic update is committed against the
   state the accessor exposes, which is where the one-shot fupd the
   accessors consume comes from. It is internal to the proofs: no
   specification mentions it. *)

Lemma find_au_commit γ x Ψ D R V :
  find_au γ x Ψ -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V ∗ Ψ (R x).
Proof.
  iIntros "AU Hst".
  iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
  iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
  iMod ("Hcommit" with "Hcl") as "HΨ".
  by iFrame.
Qed.

(* Re-basing onto another member of the same class: the recursive call
   speaks of the vertex the traversal reached. Unlike a one-shot fupd, an
   atomic update has to be re-packaged, but [UF_same_class_eq] is still
   all the argument needs. *)

Lemma find_au_rebase γ x z Ψ :
  same_class γ x z -∗ find_au γ x Ψ -∗ find_au γ z Ψ.
Proof.
  iIntros "#Hxz AU". rewrite /find_au. iAuIntro.
  iApply (aacc_aupd with "AU"); first done.
  iIntros (D R V) "Hst".
  iDestruct (UF_same_class_eq with "Hst Hxz") as "[%Heq Hst]".
  iAaccIntro with "Hst".
  { iIntros "Hst !>". iFrame "Hst". iIntros "AU". by iModIntro. }
  iIntros "Hst !>". iRight. iFrame "Hst".
  iIntros "HΨ !>". by rewrite Heq.
Qed.

Lemma find_pre_rebase γ x z op :
  same_class γ x z -∗ find_pre γ x op -∗ find_pre γ z op.
Proof.
  iIntros "#Hxz Hop". destruct op as [Ψ|]; simpl; last done.
  iApply (find_au_rebase with "Hxz Hop").
Qed.

Definition find_aux_spec find : iProp Σ :=
  □ {{ ∀ γ op; is_uf γ ∗ in_uf γ x ∗ find_pre γ x op }}
  find x : elem
  {{ RET (z : elem); find_post z op ∗ in_uf γ z ∗ same_class γ x z }}.

(* The observing caller: [op] is [None], so it hands over nothing and
   learns only where the traversal ended. *)

Lemma find_observe find :
  find_aux_spec find -∗
  □ {{ ∀ γ; is_uf γ ∗ in_uf γ x }}
  find x : elem
  {{ RET (z : elem); in_uf γ z ∗ same_class γ x z }}.
Proof.
  iIntros "#Hspec !>".
  iApply (iSpec_mono with "Hspec"). simpl.
  iIntros (x m) "Hspec'". iIntros (γ) "(#Hinv & #Hin)".
  iApply (imp_wand with "[Hspec']").
  { iApply ("Hspec'" $! γ None). by iFrame "#". }
  iIntros (z) "(_ & $ & $)".
Qed.

(* The linearizing caller: [op] is [Some Ψ], with [Ψ] the continuation
   folding in the private postcondition (compare
   [nextｰspecｰpop (λ o, _ -∗ Φ o)], queue_mpmc_1.v:876).

   The re-packaging below is only there because [find_spec]'s atomic
   postcondition has an [∃∃] binder while [find_au]'s does not; stating
   the triple as [UF γ D R V | RET (R x); …] would make it [iExact "AU"],
   as in [get_atomic_spec]. *)

Lemma find_atomic_spec find :
  find_aux_spec find -∗ find_spec find.
Proof.
  iIntros "Hspec".
  iApply (iSpec_mono_pers with "Hspec").
  iIntros "!>" (x m) "Hm". iIntros (γ) "[#Hinv #Hx]". iIntros (Φ) "AU".
  iApply (imp_wand with "[Hm AU]").
  { iApply ("Hm" $! γ (Some (λ z, in_uf γ z ∗ same_class γ x z -∗ Φ z)%I)).
    iFrame "Hinv Hx".
    rewrite /find_pre /find_au. iAuIntro.
    iApply (aacc_aupd with "AU"); first done.
    iIntros (D R V) "Hst".
    iAaccIntro with "Hst".
    { iIntros "Hst !>". iFrame "Hst". iIntros "AU". by iModIntro. }
    iIntros "Hst !>". iRight. iExists (R x).
    iSplitL "Hst"; first by iFrame "Hst".
    iIntros "HΦ !>". iExact "HΦ". }
  iIntros (z) "(HΦ & #Hin & #Hsc)". iApply "HΦ". by iFrame "Hin Hsc".
Qed.

Lemma find_proof η :
  ▷ in_env "find" find_aux_spec η -∗
  closure_spec η (EAnonFun (AnonFun "x"
    (EMatch (ERecordAccess (EPath ["x"]) content_field) __find_branches)))
    find_aux_spec.
Proof.
  iIntros "#IH". iApply closure_spec_intro.
  iIntros "!> /=" (x γ op) "(#Hinv & #Hx & Hop)".
  iDestruct "Hx" as (i) "#Hxv".
  iApply imp_please; iNext.

  (* Goal: [ match x.content with ... ]. The scrutinee read carries what
     the caller handed over: on a [Root] its atomic update is committed
     there and then, and the branch's whole postcondition comes back in
     its place. *)
  imp_match content with "[Hop]".
  { iApply (read_vertex_lp (λ _, find_post x op ∗ in_uf γ x ∗ same_class γ x x)%I
              with "Hinv Hxv Hop [] []"); last first.
    { imp_path. }
    iNext. iIntros (c D R V) "_ %HRx _ _ Hop Hst".
    (* The linearization point: [x] is its own representative in the
       state the accessor exposes. An observing caller has nothing to
       commit. *)
    destruct op as [Ψ|]; simpl.
    - iMod (find_au_commit with "Hop Hst") as "[$ HΨ]".
      iEval (rewrite HRx) in "HΨ".
      iFrame "HΨ Hxv". iApply same_class_refl.
    - iFrame "Hst Hxv". iModIntro. iApply same_class_refl. }
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
  iDestruct "Hc" as "[(_ & (%lp & #Hlk)) Hop]".
  iDestruct (linked_locs with "Hlk") as "#Hlocs".
  iApply (ipat_PRecord_atomic (A:=elem) (⊤ ∖ ↑ufN) ⊤
            with "[] [Hop]").
  { iModIntro. iApply (blockLocs_field_at with "Hlocs"). done. }
  iNext.
  iApply (uf_link_parent_acc with "Hinv Hxv Hlk [Hop]").
  iNext.
  iIntros (y j Hj) "#Hxy #Hy".

  (* Recursive call [find y]. *)
  imp_app τ[elem].
  iIntros "Hm".
  iSpecialize ("Hm" $! γ op with "[$Hinv $Hy Hop]").
  { iApply (find_pre_rebase with "Hxy Hop"). }
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

Definition compress_spec compress : iProp Σ :=
  □ {{ ∀ γ i k; is_uf γ ∗ vertex γ x i ∗ vertex γ z k ∗ same_class γ x z }}
  compress x z : elem elem
  {{ RET (w : elem); ⌜w = z⌝ }}.

Lemma compress_proof η :
  ▷ in_env "compress" compress_spec η -∗
  closure_spec η (EAnonFun (AnonFun "x" (EAnonFun __compress_fun)))
    compress_spec.
Proof.
  iIntros "#IH". iApply closure_spec_intro.
  iIntros "!> /=" (x z γ i k) "(#Hinv & #Hx & #Hz & #Hxz)".
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
    iApply ("Hm" $! γ jy k with "[$Hinv $Hy $Hz $Hyz]"). }
  (* [else z]: compression would not lower the identifier, so stop. *)
  { iIntros "%Hcmp". imp_path. }
Qed.
(* ------------------------------------------------------------------------ *)
(* Verification of [findc]. *)
(* [findc] satisfies [find]'s specification: the compression is invisible.
   [findc] is [find] followed by [compress], and its linearization point
   is inside the [find], at the instant [find] reports its answer.
   So [findc] hands its client's atomic update straight to [find]. *)
Lemma findc_proof η :
  in_env "find" find_aux_spec η -∗
  in_env "compress" compress_spec η -∗
  EWP (eval η (EAnonFun __findc)) {{ findc, find_aux_spec findc }}.
Proof.
  iIntros "#IFind #ICompress".
  iApply imp_EAnon_pers.
  iIntros "!> /=" (x γ op) "(#Hinv & #Hx & Hop)".
  iDestruct "Hx" as (i) "#Hxv".
  iApply imp_please; iNext.

  (* [match x.content with ...]. *)
  imp_match content with "[Hop]".
  { iApply (read_vertex_lp (λ _, find_post x op ∗ in_uf γ x ∗ same_class γ x x)%I
              with "Hinv Hxv Hop [] []"); last first.
    { imp_path. }
    iNext. iIntros (c D R V) "_ %HRx _ _ Hop Hst".
    destruct op as [Ψ|]; simpl.
    - iMod (find_au_commit with "Hop Hst") as "[$ HΨ]".
      iEval (rewrite HRx) in "HΨ".
      iFrame "HΨ".
      iSplitR; [by iExists i | iApply same_class_refl].
    - iFrame "Hst". iModIntro. iSplitR; first done.
      iSplitR; [by iExists i | iApply same_class_refl]. }
  iIntros "Hc".
  destruct a as [rc|rc]; simpl.

  { (* [Root _ -> x]. *)
    rewrite (@encode_encode' content). next_branch.
    imp_path. }

  (* [Link { parent = y } -> let z = find y in compress x z]. *)
  iDestruct "Hc" as "[(_ & (%lp & #Hlk)) Hop]".
  iDestruct (linked_locs with "Hlk") as "#Hlocs".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  iApply (ipat_PRecord_atomic (A:=elem) (⊤ ∖ ↑ufN) ⊤
            with "[] [Hop]").
  { iModIntro. iApply (blockLocs_field_at with "Hlocs"). done. }
  iNext.
  iApply (uf_link_parent_acc with "Hinv Hxv Hlk [Hop]").
  iNext.
  iIntros (y jy Hjy) "#Hxy #Hy".

  (* [let z = find y in ...]: the call is on [y], but what [findc] holds
     is about [x], so it is transported across [same_class γ x y] by
     [find_pre_rebase]. *)
  iApply (imp_ELet_var (B:=elem)
    (λ z : elem, find_post z op ∗ in_uf γ z ∗ same_class γ x z)%I with "[Hop]").
  { imp_app τ[elem].
    iIntros "Hm".
    iSpecialize ("Hm" $! γ op with "[$Hinv $Hy Hop]").
    { iApply (find_pre_rebase with "Hxy Hop"). }
    iApply (imp_wand with "Hm").
    iIntros (z) "($ & $ & #Hyz)".
    iApply (same_class_trans with "Hxy Hyz"). }
  iIntros (z) "(HΨ & #Hz & #Hxz)".

  (* [compress x z]. *)
  iDestruct "Hz" as (k) "#Hzv".
  imp_app τ[elem; elem].
  iIntros "Hm".
  iSpecialize ("Hm" $! γ i k with "[$Hinv $Hxv $Hzv $Hxz]").
  iApply (imp_wand with "Hm").
  iIntros (w) "->".
  iFrame "HΨ Hxz Hzv".
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [get]. *)

(* [get] is only ever called by a client that linearizes, so it needs no
   observing mode: what it is handed is always an atomic update. *)

Definition get_au (γ : uf_names) (x : elem) (Ψ : val → iProp Σ) : iProp Σ :=
  AU <{ ∃∃ D (R : elem → elem) (V : elem → val), UF γ D R V }>
     @ ⊤ ∖ ↑ufN, ∅
  <{ UF γ D R V, COMM Ψ (V (R x)) }>.

Lemma get_au_commit γ x Ψ D R V :
  get_au γ x Ψ -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V ∗ Ψ (V (R x)).
Proof.
  iIntros "AU Hst".
  iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
  iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
  iMod ("Hcommit" with "Hcl") as "HΨ".
  by iFrame.
Qed.

Lemma get_au_rebase γ x z Ψ :
  same_class γ x z -∗ get_au γ x Ψ -∗ get_au γ z Ψ.
Proof.
  iIntros "#Hxz AU". rewrite /get_au. iAuIntro.
  iApply (aacc_aupd with "AU"); first done.
  iIntros (D R V) "Hst".
  iDestruct (UF_same_class_eq with "Hst Hxz") as "[%Heq Hst]".
  iAaccIntro with "Hst".
  { iIntros "Hst !>". iFrame "Hst". iIntros "AU". by iModIntro. }
  iIntros "Hst !>". iRight. iFrame "Hst".
  iIntros "HΨ !>". by rewrite Heq.
Qed.

Definition get_aux_spec get : iProp Σ :=
  □ {{ ∀ γ Ψ; is_uf γ ∗ in_uf γ x ∗ get_au γ x Ψ }}
  get x : elem
  {{ RET v; Ψ v }}.

Definition get_spec get : iProp Σ :=
  □ <<{ ∀ γ; is_uf γ ∗ in_uf γ x
    | ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
  get x : elem @ ↑ufN
  <<{ UF γ D R V | RET (V (R x)) }>>.

(* [get_spec]'s atomic postcondition has no [∃∃] binder and its return
   value is [V (R x)], so it is exactly what [get_au] asks for: the
   client's atomic update is passed on as it stands. *)

Lemma get_atomic_spec get :
  get_aux_spec get -∗ get_spec get.
Proof.
  iIntros "Hspec".
  iApply (iSpec_mono_pers with "Hspec").
  iIntros "!>" (x m) "Hm /=".
  iIntros (γ) "(#Hinv & #Hx) %Φ AU".
  iApply ("Hm" $! γ Φ with "[$Hinv $Hx AU]").
  iExact "AU".
Qed.

Lemma get_proof η :
  ▷ in_env "get" get_aux_spec η -∗
  ▷ in_env "findc" find_aux_spec η -∗
  closure_spec η
    (EAnonFun (AnonFun "x"
        (ELet [Binding (PVar "x") (EApp (EPath ["findc"]) (EPath ["x"]))]
              __get_exp)))
    get_aux_spec.
Proof.
  iIntros "#IGet #IFindc".
  iApply closure_spec_intro.
  simpl.
  iIntros "!>" (x γ Ψ) "(#Hinv & #Hx & AU)".
  iApply imp_please; iNext.

  (* [let x = findc x in ...].
     This is just an observer call as the traversal is not [get]'s
     linearization point. *)
  imp_let $! (λ z : elem, in_uf γ z ∗ same_class γ x z)%I.
  { iPoseProof (in_env_mono with "IFindc []") as "IFindc'".
    { iIntros (find). iApply find_observe. }
    iClear "IFindc".
    imp_app τ[elem].
    iIntros "Hm". iApply "Hm". iFrame "#". }
  iIntros (z) "[#Hz #Hxz]".
  iDestruct "Hz" as (j) "#Hzv".

  (* From here on everything is stated at [z], so the atomic update moves
     there once and for all. *)
  iDestruct (get_au_rebase with "Hxz AU") as "AU".

  (* [match x.content with ...]: [get]'s linearization point. *)
  imp_match content with "[AU]".
  { iApply (read_vertex_lp
              (λ c : content, match c with
                              | CtRoot rc => ∃ v : val, root_val rc v ∗ Ψ v
                              | CtLink _ => False
                              end)%I
              with "Hinv Hzv AU [] []"); last first.
    { imp_path. }
    iNext. iIntros (c D R V) "%Hroot %HRz _ #Hval AU Hst".
    destruct c as [rc|rc]; last discriminate.
    iMod (get_au_commit with "AU Hst") as "[Hst HΨ]".
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
     so nothing was linearized; the atomic update comes back unspent and
     the call retries from [z]. *)
  iDestruct "Hc" as "[_ AU]".
  rewrite (@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem].
  iIntros "Hm /=".
  iApply ("Hm" $! γ Ψ with "[$]").
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [set]. *)

(* [set x v] writes [v] as the value of [x]'s equivalence class.

   [set] does not write the payload field: it allocates a fresh
   [Root { value = v }] and CASes the whole content cell. The
   linearization point is the successful CAS. *)

Definition set_au (γ : uf_names) (x : elem) (v : val)
    (Ψ : iProp Σ) : iProp Σ :=
  AU <{ ∃∃ D (R : elem → elem) (V : elem → val), UF γ D R V }>
     @ ⊤ ∖ ↑ufN, ∅
  <{ UF γ D R V.[x -/R/> v], COMM Ψ }>.

(* Committing at the linearization point. Unlike [find] and [get], both
   halves of the abstract state move here, so the commit also updates the
   invariant's half. *)

Lemma set_au_commit γ x v Ψ D R V :
  set_au γ x v Ψ -∗ UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V.[x -/R/> v] ∗ Ψ.
Proof.
  iIntros "AU Hst".
  iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
  iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
  iDestruct (UF_val_congr with "Hst") as %Hcongr.
  iDestruct (UF_dethroned with "Hst") as "#Hdeth".
  iMod (UF_update_2 _ _ _ _ D R V.[x -/R/> v]
          with "Hdeth Hst Hcl") as "[Hst Hcl]";
    [done | by apply uf_val_congr_set |].
  iMod ("Hcommit" with "Hcl") as "HΨ".
  by iFrame "Hst HΨ".
Qed.

(* Re-basing, for the retry, as in [get]. Here, naming a class by one
   member or another is literally the same function. *)

Lemma set_au_rebase γ x z v Ψ :
  same_class γ x z -∗ set_au γ x v Ψ -∗ set_au γ z v Ψ.
Proof.
  iIntros "#Hxz AU". rewrite /set_au. iAuIntro.
  iApply (aacc_aupd with "AU"); first done.
  iIntros (D R V) "Hst".
  iDestruct (UF_same_class_eq with "Hst Hxz") as "[%Heq Hst]".
  iAaccIntro with "Hst".
  { iIntros "Hst !>". iFrame "Hst". iIntros "AU". by iModIntro. }
  iIntros "Hst !>". iRight.
  rewrite (update_class_congr_class R x z V v Heq).
  iFrame "Hst". iIntros "HΨ !>". iExact "HΨ".
Qed.

Definition set_content_spec set : iProp Σ :=
  □ {{ ∀ γ v Ψ; is_uf γ ∗ in_uf γ x ∗ fresh_root cx' v ∗ set_au γ x v Ψ }}
  set x cx' : elem content
  {{ RET (); Ψ }}.

Definition set_aux_spec set : iProp Σ :=
  □ {{ ∀ γ Ψ; is_uf γ ∗ in_uf γ x ∗ set_au γ x v Ψ }}
  set x v : elem val
  {{ RET (); Ψ }}.

(* The specification as a client sees it. *)

Definition set_spec set : iProp Σ :=
  □ <<{ ∀ γ; is_uf γ ∗ in_uf γ x
    | ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
  set x v : elem val @ ↑ufN
  <<{ UF γ D R V.[x -/R/> v] | RET () }>>.

Lemma set_atomic_spec :
  (∀ set, set_aux_spec set -∗ set_spec set).
Proof.
  iIntros (set) "Hspec".
  iApply (iSpec_mono_pers with "Hspec").
  iIntros "!>" (x v m) "Hm /=".
  iIntros (γ) "(#Hinv & #Hx) %Φ AU".
  iSpecialize ("Hm" $! γ (Φ ()) with "[$Hinv $Hx AU]").
  { iExact "AU". }
  iApply (imp_wand with "Hm"). iIntros ([]) "$".
Qed.

Lemma set_proof η :
  ▷ in_env "set" set_content_spec η -∗
  ▷ in_env "findc" find_aux_spec η -∗
  in_env "cas" compare_and_set_spec η -∗
  closure_spec η (EAnonFun (AnonFun "x" (EAnonFun __set_fun))) set_content_spec.
Proof.
  iIntros "#ISet #IFindc #Hcas".
  iApply closure_spec_intro.
  iIntros "!> /=".
  iIntros (x cx' γ v Ψ).
  iIntros "(#Hinv & #Hx & Hcx' & AU)".
  (* The caller's record is a [Root]. *)
  destruct cx' as [rcn|rcn]; last by iDestruct "Hcx'" as "[]".
  iApply imp_please; iNext.

  (* [let x = findc x in ...]: an observer call, as in [get]. *)
  imp_let $! (λ z, in_uf γ z ∗ same_class γ x z)%I.
  { iPoseProof (in_env_mono with "IFindc []") as "IFindc'".
    { iIntros (find) "H". iApply (find_observe with "H"). }
    iClear "IFindc".
    imp_app τ[elem].
    iIntros "Hm". iApply "Hm". iFrame "#". }
  iIntros (z) "[#Hz #Hxz]".
  iDestruct "Hz" as (j) "#Hzv".
  iDestruct (set_au_rebase with "Hxz AU") as "AU".

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
    imp_if with "[Hcx' AU]".
    { set_postcondition (λ res : bool,
        if res then Ψ else set_au γ z v Ψ ∗ rcn ⤇ {| root_value := v |})%I.
      imp_app τ[loc;content;content].
      { iApply (vertex_content_ptr with "Hzv"). imp_path. }
      iIntros "Hptr Hm".
      iApply ("Hm" $! (⊤ ∖ ↑ufN)).
      iNext.
      iApply (uf_cas_set_fupd _ z j _ rc rcn vexp v (set_au γ z v Ψ) Ψ
                (λ res : bool,
                   if res then Ψ
                   else set_au γ z v Ψ ∗ rcn ⤇ {| root_value := v |})%I
                with "Hinv Hzv Hptr Hrv Hcx' AU [] []").
      { (* The CAS is the linearization point: commit there. *)
        iNext. iIntros (D R V) "%Hax %Hval AU Hst".
        iMod (set_au_commit with "AU Hst") as "[Hst HΨ]".
        by iFrame "Hst HΨ". }
      { iIntros "!> % $". } }

    { (* CAS succeeded: the hook has already produced the postcondition. *)
      iIntros "HΨ". iApply imp_EUnit. iFrame. }
    { (* CAS failed: retry on the vertex [findc] found, with the atomic
         update and the fresh record handed back. *)
      iIntros "[AU Hcx']".
      imp_app τ[elem; content].
      iIntros "Hm /=". iApply "Hm".
      iFrame "∗#". } }

  (* [_ -> set x cx']: the cell raced ahead of us; retry likewise. *)
  rewrite {2}(@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem; content].
  iIntros "Hm /=". iApply "Hm".
  iFrame "∗#".
Qed.

(* The public, one-argument [set x v]: allocates the fresh
   [Root { value = v }] and calls the helper above. *)

Lemma set_wrapper_proof η :
  in_env "set" set_content_spec η -∗
  EWP (eval η (EAnonFun __set)) {{ set_aux_spec }}.
Proof.
  iIntros "#ISet".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x v γ Ψ).
  iIntros "(#Hinv & #Hx & AU)".
  iApply imp_please; iNext.

  (* [let cx' = Root { value = v } in set x cx']. *)
  imp_let $! (λ c, fresh_root c v)%I.
  { imp_record $! root_fields.
    simpl. iIntros (c) "H".
    iDestruct "H" as (r) "(-> & %xs & Hown & ->)".
    iApply "Hown". }
  iIntros (cx') "Hco".
  imp_app τ[elem; content].
  iIntros "Hm". iApply "Hm".
  iFrame. iFrame "#".
Qed.

(* ------------------------------------------------------------------------ *)
(* Verification of [update]. *)

(* [update x f] replaces the value of [x]'s class by [f] applied to it.

   [f] is described by an arbitrary relation [Φf] between its argument
   and its result. Its specification must be persistent. *)

Definition update_au (γ : uf_names) (x : elem)
    (Φf : val → val → iProp Σ) (Ψ : iProp Σ) : iProp Σ :=
  AU <{ ∃∃ D (R : elem → elem) (V : elem → val), UF γ D R V }>
     @ ⊤ ∖ ↑ufN, ∅
  <{ ∀∀ w : val, Φf (V x) w ∗ UF γ D R V.[x -/R/> w], COMM Ψ }>.

(* The value the attempt computed is what the commit reports, so unlike
   the other operations this one consumes [Φf (V x) w] as well. *)

Lemma update_au_commit γ x Φf Ψ D R V w :
  update_au γ x Φf Ψ -∗ Φf (V x) w -∗
  UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V.[x -/R/> w] ∗ Ψ.
Proof.
  iIntros "AU HΦf Hst".
  iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
  iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
  iDestruct (UF_val_congr with "Hst") as %Hcongr.
  iDestruct (UF_dethroned with "Hst") as "#Hdeth".
  iMod (UF_update_2 _ _ _ _ D R V.[x -/R/> w]
          with "Hdeth Hst Hcl") as "[Hst Hcl]";
    [done | by apply uf_val_congr_set |].
  iMod ("Hcommit" $! w with "[$HΦf $Hcl]") as "HΨ".
  by iFrame "Hst HΨ".
Qed.

Lemma update_au_rebase γ x z Φf Ψ :
  same_class γ x z -∗ update_au γ x Φf Ψ -∗ update_au γ z Φf Ψ.
Proof.
  iIntros "#Hxz AU". rewrite /update_au. iAuIntro.
  iApply (aacc_aupd with "AU"); first done.
  iIntros (D R V) "Hst".
  iDestruct (UF_same_class_eq with "Hst Hxz") as "[%Heq Hst]".
  iDestruct (UF_val_congr with "Hst") as %Hcongr.
  iAaccIntro with "Hst".
  { iIntros "Hst !>". iFrame "Hst". iIntros "AU". by iModIntro. }
  iIntros (w) "[HΦf Hst] !>". iRight. iExists w.
  rewrite (update_class_congr_class R x z V w Heq) (Hcongr x z Heq).
  iFrame "HΦf Hst". iIntros "HΨ !>". iExact "HΨ".
Qed.

Definition update_aux_spec update : iProp Σ :=
  □ {{ ∀ γ Φf Ψ; is_uf γ ∗ in_uf γ x ∗
     □ {{ True }} f v : val {{ RET w; Φf v w }} ∗
     update_au γ x Φf Ψ }}
  update x f : elem val
  {{ RET (); Ψ }}.

Definition update_spec update : iProp Σ :=
  □ <<{ ∀ γ Φf; □ {{ True }} f v : val {{ RET w; Φf v w }} ∗ is_uf γ ∗ in_uf γ x
     |  ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
  update x f : elem val @ ↑ufN
  <<{ ∃∃ w : val, Φf (V x) w ∗ UF γ D R V.[x -/R/> w] | RET () }>>.

Lemma update_atomic_spec :
  (∀ update, update_aux_spec update -∗ update_spec update).
Proof.
  iIntros (update) "Hspec".
  iApply (iSpec_mono_pers with "Hspec").
  iIntros "!>" (x f m) "Hm /=".
  iIntros (γ Φf) "(#Hf & #Hinv & #Hx)".
  iIntros (Φ) "AU".
  iSpecialize ("Hm" $! γ Φf (Φ ()) with "[$Hinv $Hx $Hf AU]").
  { iExact "AU". }
  iApply (imp_wand with "Hm"). iIntros ([]) "$".
Qed.

Lemma update_proof η :
  ▷ in_env "update" update_aux_spec η -∗
  ▷ in_env "findc" find_aux_spec η -∗
  in_env "cas" compare_and_set_spec η -∗
  closure_spec η (EAnonFun (AnonFun "x" (EAnonFun __update_fun))) update_aux_spec.
Proof.
  iIntros "#IUpdate #IFindc #Hcas".
  iApply closure_spec_intro.
  iIntros "!> /=".
  iIntros (x f γ Φf Ψ).
  iIntros "(#Hinv & #Hx & #Hf & AU)".
  iApply imp_please; iNext.

  (* [let x = findc x in ...]: an observer call, as in [get] and [set]. *)
  imp_let $! (λ z, in_uf γ z ∗ same_class γ x z)%I.
  { iPoseProof (in_env_mono with "IFindc []") as "IFindc'".
    { iIntros (find) "Hfind". iApply (find_observe with "Hfind"). }
    iClear "IFindc".
    imp_app τ[elem].
    iIntros "Hm". iApply "Hm".
    iFrame "#". }
  iIntros (z) "[#Hz #Hxz]".
  iDestruct "Hz" as (j) "#Hzv".
  iDestruct (update_au_rebase with "Hxz AU") as "AU".

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
    iApply (ipat_PRecord_pers ⊤ _ _ _ 0%Z rc _ _ v with "[] Hlv [AU]");
      first (iModIntro; iApply (blockLocs_field_at with "Hrclocs"); done).
    iNext. iIntros "_".
    (* [if cas [%atomic.loc x.content] cx (Root { value = f v})]. *)
    imp_if with "[AU]".
    { set_postcondition
        (λ res : bool, if res then Ψ else update_au γ z Φf Ψ)%I.
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
          iIntros "Hm". by iApply "Hm". }
        iIntros (c) "(%r' & -> & %xs & Hown & HΦf)".
        iExists r', xs. iSplit; first done. iFrame "HΦf Hown". }
      iIntros "Hptr (%rcn & %w & -> & Hrcn & HΦf) Hm".
      iApply ("Hm" $! (⊤ ∖ ↑ufN)).
      iNext.
      (* The attempt's [Φf v w] rides along with the atomic update as the
         CAS's linearization resources: spent together on success, dropped
         together on failure. *)
      iApply (uf_cas_set_fupd _ z j _ rc rcn v w
                (update_au γ z Φf Ψ ∗ Φf v w)%I Ψ
                (λ res : bool, if res then Ψ else update_au γ z Φf Ψ)%I
                with "Hinv Hzv Hptr [] Hrcn [AU HΦf] [] []").
      { by iFrame "Hrclocs Hlv". }
      { by iFrame "AU HΦf". }
      { (* The main difference with the proof of [set]: the CAS reports
           [V z = v] against the state at the linearization point. *)
        iIntros "!>" (D R V) "%Hroot %Hval [AU HΦf] Hst".
        iApply (update_au_commit with "AU [HΦf] Hst").
        rewrite Hval. iExact "HΦf". }
      { iIntros "!>" ([|]) "H";
          [iExact "H" | by iDestruct "H" as "[[$ _] _]"]. } }

    { (* CAS succeeded: the hook has already produced the postcondition. *)
      iIntros "HΨ". iApply imp_EUnit. iApply "HΨ". }
    { (* CAS failed: retry on the vertex [findc] found, with the atomic
         update handed back. *)
      iIntros "AU".
      imp_app τ[elem; val].
      iIntros "Hm". iApply "Hm".
      iFrame. iFrame "#". } }

  (* [_ -> update x f]: the cell raced ahead of us; retry likewise. *)
  rewrite {3}(@encode_encode' content).
  next_branch.
  next_branch.
  imp_app τ[elem; val].
  iIntros "Hm". iApply "Hm".
  iFrame. iFrame "#".
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

(* [union] has a pair of linearization points, one per outcome, and the
   caller's atomic update covers both: its atomic postcondition is
   [union_post], which is a match on the outcome. *)

Definition union_au (γ : uf_names) (x y : elem)
    (Ψ : option val → iProp Σ) : iProp Σ :=
  AU <{ ∃∃ D (R : elem → elem) (V : elem → val), UF γ D R V }>
     @ ⊤ ∖ ↑ufN, ∅
  <{ ∀∀ o : option val, union_post γ D R V x y o, COMM Ψ o }>.

Definition union_aux_spec union : iProp Σ :=
  □ {{ ∀ γ Ψ; is_uf γ ∗ in_uf γ x ∗ in_uf γ y ∗ union_au γ x y Ψ }}
  union x y : elem elem
  {{ RET o; Ψ o }}.

(* The two commits. [None]: the state does not move, so the update is
   committed with the state it was offered. [Some]: the merge, whose
   [same_class] is minted at the instant both halves of the class
   authority are in hand. *)

Lemma union_au_none γ x y Ψ :
  union_au γ x y Ψ -∗
  ∀ D (R : elem → elem) (V : elem → val), ⌜R x = R y⌝ -∗
    UF γ D R V ={⊤ ∖ ↑ufN}=∗ UF γ D R V ∗ Ψ None.
Proof.
  iIntros "AU" (D R V) "%Heq Hst".
  iMod "AU" as (D' R' V') "[Hcl [_ Hcommit]]".
  iDestruct (UF_agree with "Hst Hcl") as %(<- & <- & <-).
  iMod ("Hcommit" $! None with "[$Hcl]") as "HΨ"; first done.
  by iFrame "Hst HΨ".
Qed.

Lemma union_au_some γ x y Ψ :
  union_au γ x y Ψ -∗
  ∀ D (R : elem → elem) (V : elem → val) b c,
    ⌜(b = x ∧ c = y) ∨ (b = y ∧ c = x)⌝ -∗ ⌜R x ≠ R y⌝ -∗
    dethroned γ R.[b -/R/> R c] -∗
    UF γ D R V ={⊤ ∖ ↑ufN}=∗
    UF γ D R.[b -/R/> R c] V.[b -/R/> V c] ∗
    same_class γ b c ∗ Ψ (Some (V b)).
Proof.
  iIntros "AU" (D R V b c) "%Hdir %Hne #Hdeth' Hst".
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
  iMod ("Hcommit" $! (Some (V b)) with "[Hcl]") as "HΨ".
  { iExists b, c. by iFrame "Hcl". }
  by iFrame "Hst Hbc HΨ".
Qed.

(* Re-basing onto other members of the same two classes: after an
   unsuccessful CAS the call restarts on the vertices its traversals
   reached, while the update it carries speaks of the original
   arguments. *)

Lemma union_au_rebase γ x y a b Ψ :
  same_class γ x a -∗ same_class γ y b -∗
  union_au γ x y Ψ -∗ union_au γ a b Ψ.
Proof.
  iIntros "#Hxa #Hyb AU". rewrite /union_au. iAuIntro.
  iApply (aacc_aupd with "AU"); first done.
  iIntros (D R V) "Hst".
  iDestruct (UF_same_class_eq with "Hst Hxa") as "[%Hx Hst]".
  iDestruct (UF_same_class_eq with "Hst Hyb") as "[%Hy Hst]".
  iDestruct (UF_val_congr with "Hst") as %Hcongr.
  iAaccIntro with "Hst".
  { iIntros "Hst !>". iFrame "Hst". iIntros "AU". by iModIntro. }
  iIntros (o) "Hpost !>". iRight. iExists o.
  iSplitL "Hpost"; last by iIntros "HΨ !>".
  destruct o as [v|]; simpl.
  - iDestruct "Hpost" as (b' c') "(%Hdir & %Hne & -> & Hst)".
    destruct Hdir as [[-> ->] | [-> ->]].
    + iExists x, y. iSplit; first by iLeft.
      iSplit; first (iPureIntro; congruence).
      rewrite (Hcongr x a Hx). iSplit; first done.
      rewrite Hy (update_class_congr_class R x a R (R b) Hx).
      rewrite (Hcongr y b Hy) (update_class_congr_class R x a V (V b) Hx).
      iExact "Hst".
    + iExists y, x. iSplit; first by iRight.
      iSplit; first (iPureIntro; congruence).
      rewrite (Hcongr y b Hy). iSplit; first done.
      rewrite Hx (update_class_congr_class R y b R (R a) Hy).
      rewrite (Hcongr x a Hx) (update_class_congr_class R y b V (V a) Hy).
      iExact "Hst".
  - iDestruct "Hpost" as "[%Hab $]". iPureIntro. congruence.
Qed.

(* The specification as a client sees it. *)

Definition union_spec union : iProp Σ :=
  □ <<{ ∀ γ; is_uf γ ∗ in_uf γ x ∗ in_uf γ y
    | ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
  union x y : elem elem @ ↑ufN
  <<{ ∃∃ o : option val, union_post γ D R V x y o | RET o }>>.

Lemma union_atomic_spec :
  (∀ union, union_aux_spec union -∗ union_spec union).
Proof.
  iIntros (union) "Hspec".
  iApply (iSpec_mono_pers with "Hspec").
  iIntros "!>" (x y m) "Hm /=".
  iIntros (γ) "(#Hinv & #Hx & #Hy) %Φ AU".
  iApply ("Hm" $! γ Φ). iFrame "Hinv Hx Hy". iExact "AU".
Qed.

Lemma union_proof η :
  ▷ in_env "union" union_aux_spec η -∗
  ▷ in_env "findc" find_aux_spec η -∗
  in_env "cas" compare_and_set_spec η -∗
  closure_spec η (EAnonFun (AnonFun "x" (EAnonFun __union_fun))) union_aux_spec.
Proof.
  iIntros "#IUnion #IFindc #Hcas".
  iApply closure_spec_intro.
  iIntros "!> /=".
  iIntros (x y γ Φ) "(#Hinv & #Hx & #Hy & AU)".
  iApply imp_please; iNext.

  (* Weaken the specification of [findc]. *)
  iPoseProof (in_env_mono with "IFindc []") as "IFindc'".
  { iIntros (find) "Hfind". iApply (find_observe with "Hfind"). }

  (* [let x = findc x and y = findc y in ...] *)
  imp_let $! (λ z : elem, in_uf γ z ∗ same_class γ x z)%I
          $! (λ z : elem, in_uf γ z ∗ same_class γ y z)%I.
  { imp_app τ[elem].
    iIntros "Hm". iApply "Hm". iFrame "#". }
  { imp_app τ[elem].
    iIntros "Hm". iApply "Hm". iFrame "#". }
  iIntros (a b) "[#Ha #Hxa] [#Hb #Hyb]".
  iDestruct "Ha" as (i') "#Hav".
  iDestruct "Hb" as (j') "#Hbv".

  (* Re-base the hook onto the vertices the traversals reached. *)
  iDestruct (union_au_rebase with "Hxa Hyb AU") as "AU".
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
    iPoseProof (union_au_none with "AU") as "Hnone".
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
      iApply (ipat_PRecord_pers ⊤ _ _ _ 0%Z rc _ _ v with "[] Hlv [AU]");
        first (iModIntro; iApply (blockLocs_field_at with "Hrclocs"); done).
      iNext. iIntros "_".

      imp_if with "[AU]".
      { set_postcondition
          (λ res : bool, if res then Φ (Some v) else union_au γ a b Φ)%I.
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
                  (union_au γ a b Φ) (Φ (Some v))
                  (λ res : bool, if res then Φ (Some v) else union_au γ a b Φ)
                  with "Hinv Hav Hptr [] Hbv Hrcn AU [] []").
        { lia. }
        { iExists lv. by iFrame "Hrclocs Hlv". }
        { (* The update and the CAS now speak of the same two vertices, so
             this is a hand-over with nothing to re-index. *)
          iNext. iIntros (D R V) "%Hax %Hne %Hval #Hdeth' AU Hst".
          iPoseProof (union_au_some with "AU") as "Hsome".
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
      { iIntros "AU".
        (* CAS failed: retry on the vertices [findc] found. *)
        imp_app τ[elem; elem].
        iIntros "Hm3". iApply "Hm3". iFrame. iFrame "Hinv".
        iSplit.
        { by iExists i'. }
        { by iExists j'. } } }

    { (* [_ -> union x y]: the cell raced ahead of us. *)
      rewrite {3}(@encode_encode' content).
      next_branch.
      next_branch.
      imp_app τ[elem; elem].
      iIntros "Hm3". iApply "Hm3". iFrame. iFrame "Hinv".
      iSplit.
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
      iApply (ipat_PRecord_pers ⊤ _ _ _ 0%Z rc _ _ v with "[] Hlv [AU]");
        first (iModIntro; iApply (blockLocs_field_at with "Hrclocs"); done).
      iNext. iIntros "_".

      imp_if with "[AU]".
      { set_postcondition
          (λ res : bool, if res then Φ (Some v) else union_au γ a b Φ)%I.
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
                  (union_au γ a b Φ) (Φ (Some v))
                  (λ res : bool, if res then Φ (Some v) else union_au γ a b Φ)
                  with "Hinv Hbv Hptr [] Hav Hrcn AU [] []").
        { lia. }
        { iExists lv. by iFrame "Hrclocs Hlv". }
        { (* The mirror image: here it is [b]'s class that is absorbed. *)
          iNext. iIntros (D R V) "%Hby %Hne %Hval #Hdeth' AU Hst".
          iPoseProof (union_au_some with "AU") as "Hsome".
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
      { iIntros "AU".
        imp_app τ[elem; elem].
        iIntros "Hm3". iApply "Hm3". iFrame. iFrame "Hinv".
        iSplit.
        { by iExists i'. }
        { by iExists j'. } } }

    { rewrite (@encode_encode' content).
      next_branch.
      next_branch.
      imp_app τ[elem; elem].
      iIntros "Hm3". iApply "Hm3". iFrame "∗ Hinv".
      iSplit.
      { by iExists i'. }
      { by iExists j'. } } }
Qed.

(* The public wrapper:
   [union x y = if x == y then None else union x y]. *)

Lemma union_wrapper_proof η :
  in_env "union" union_spec η -∗
  EWP (eval η (EAnonFun __union)) {{ union_spec }}.
Proof.
  iIntros "#IUnion".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x y γ) "(#Hinv & #Hx & #Hy)".
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
  iIntros "Hm". iApply ("Hm" with "[$Hinv]").
  { iSplit.
    - by iExists i.
    - by iExists j. }

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

Definition eq_spec eq : iProp Σ :=
  □ <<{ ∀ γ; is_uf γ ∗ in_uf γ x ∗ in_uf γ y
    | ∀∀ (D : gset elem) (R : elem → elem) (V : elem → val), UF γ D R V }>>
  eq x y : elem elem @ ↑ufN
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

Lemma eq_proof η :
  ▷ in_env "eq" eq_spec η -∗
  ▷ in_env "findc" find_spec η -∗
  closure_spec η (EAnonFun (AnonFun "x" (EAnonFun __eq_fun))) eq_spec.
Proof.
  iIntros "#IEq #IFindc".
  iApply closure_spec_intro.
  iIntros "!> /=".
  iIntros (x y γ) "(#Hinv & #Hx & #Hy)".
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
    iApply ("Hm" with "[$] [AU]").
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
    iApply ("Hm" with "[$]").
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
  iIntros "Hm". iApply ("Hm" with "[$Hinv]").
  { iSplit.
    - by iExists jx'.
    - by iExists j'. }
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

Lemma eq_wrapper_proof η :
  in_env "eq" eq_spec η -∗
  EWP (eval η (EAnonFun __eq)) {{ eq_spec }}.
Proof.
  iIntros "#IEq".
  iApply imp_EAnon_pers.
  iIntros "!> /=".
  iIntros (x y γ) "(#Hinv & #Hx & #Hy)".
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
  iIntros "Hm". iApply ("Hm" with "[$Hinv]").
  { iSplit.
    - by iExists i.
    - by iExists j. }

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

Lemma G_module_proof (η : env) :
  ⊢ EWP (eval_mexpr η MUnsupported) {{ in_env "fresh" fresh_spec }}.
Proof.
Admitted.

(* Weakening the composable specifications to the client-facing atomic
   triples. *)


Definition ConcurrentUnionFind_names : gset var :=
  {["cas"; "SharedGeneratorOfUniqueIds"; "G"; "make"; "find"; "compress";
    "findc"; "get"; "set"; "update"; "union"; "eq"]}.

Theorem ConcurrentUnionFind_module_proof (η : env) :
  in_env "Atomic" atomic_module_spec η -∗
  EWP (eval_mexpr η __main)
    {{ context [
         var_spec "make"   make_spec;
         var_spec "find"   find_spec;
         var_spec "findc"  find_spec;
         var_spec "get"    get_spec;
         var_spec "set"    set_spec;
         var_spec "update" update_spec;
         var_spec "union"  union_spec;
         var_spec "eq"     eq_spec
       ] ConcurrentUnionFind_names }}.
Proof.
  iIntros "#HAtomic".
  iApply imp_module.

  (* [let cas = Atomic.Loc.compare_and_set] *)
  iApply (imp_sitems_let compare_and_set_spec).
  { iApply cas_proof; solve_env. }
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

  iApply (imp_sitems_module (in_env "fresh" fresh_spec)).
  { iApply G_module_proof. }
  iIntros (δG) "#HG".

  (* [let make v = ...]: the only consumer of [G.fresh]. *)
  iApply (imp_sitems_let make_spec)%I.
  { iApply make_proof; solve_env. }
  iIntros (make) "#Hmake".

  (* [let rec find x = ...] *)
  iApply imp_sitems_letrec_spec.
  { iIntros "!>" (c) "#IH". iApply find_proof. solve_env. }
  iIntros (find) "#Hfind".

  (* [let rec compress x z = ...] *)
  iApply imp_sitems_letrec_spec.
  { iIntros "!>" (c) "#IH". iApply compress_proof. solve_env. }
  iIntros (compress) "#Hcompress".

  (* [let findc x = ...] *)
  iApply (imp_sitems_let find_aux_spec).
  { iApply findc_proof; solve_env. }
  iIntros (findc) "#Hfindc".

  (* [let rec get x = ...] *)
  iApply imp_sitems_letrec_spec.
  { iIntros "!>" (c) "#IH". iApply get_proof; solve_env. }
  iIntros (get) "#Hget".

  (* [let rec set x cx' = ...] *)
  iApply imp_sitems_letrec_spec.
  { iIntros "!>" (c) "#IH". iApply set_proof; solve_env. }
  iIntros (setc) "#Hsetc".

  (* [let set x v = ...]: the wrapper, which shadows the name. *)
  iApply (imp_sitems_let set_aux_spec).
  { iApply set_wrapper_proof; solve_env. }
  iIntros (set) "#Hset".

  (* [let rec update x f = ...] *)
  iApply imp_sitems_letrec_spec.
  { iIntros "!>" (c) "#IH". iApply update_proof; solve_env. }
  iIntros (update) "#Hupdate".

  (* [let rec union x y = ...] *)
  iApply imp_sitems_letrec_spec.
  { iIntros "!>" (c) "#IH". iApply union_proof; solve_env. }
  iIntros (unionr) "#Hunionr".

  (* The wrapper is stated against the atomic triple, so the recursive
     [union] is weakened to it first, putting a hypothesis of the
     premise's shape in context. *)
  iDestruct (union_atomic_spec with "Hunionr") as "#Hunionr'".

  (* [let union x y = if x == y then None else union x y] *)
  iApply (imp_sitems_let union_spec).
  { iApply union_wrapper_proof; solve_env. }
  iIntros (union) "#Hunion".

  (* [eq] is the one caller that hands its own update down, so it wants
     [findc] at the atomic triple. *)
  iDestruct (find_atomic_spec with "Hfindc") as "#Hfindc'".

  (* [let rec eq x y = ...] *)
  iApply imp_sitems_letrec_spec.
  { iIntros "!>" (c) "#IH". iApply eq_proof; solve_env. }
  iIntros (eqr) "#Heqr".

  (* [let eq x y = x == y || eq x y] *)
  iApply (imp_sitems_let eq_spec).
  { iApply eq_wrapper_proof; solve_env. }
  iIntros (eq) "#Heq".

  (* The four remaining composable specifications are weakened to the
     triples the module exports. *)
  iDestruct (find_atomic_spec with "Hfind") as "#Hfind'".
  iDestruct (get_atomic_spec with "Hget") as "#Hget'".
  iDestruct (set_atomic_spec with "Hset") as "#Hset'".
  iDestruct (update_atomic_spec with "Hupdate") as "#Hupdate'".

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
