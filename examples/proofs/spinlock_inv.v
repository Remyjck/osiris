From iris.base_logic.lib Require Import invariants token.

From osiris Require Import osiris.
From osiris.examples Require Import og_spinlock.

(** * Invariant-based spinlock specification

    We follow the CMRA from Iris' [spin_lock] example, where we have:

    – [lock_inv γ r R]: the lock bit, an [Atomic.t] (a reference [r]),
      together with the user resource [R] and an exclusive token; the
      resource lives behind [▷].
    – [is_lock γ r R ≔ is_ref r ∗ inv N (lock_inv γ r R)]: a *persistent*
      handle handed to every caller.
    – [locked γ ≔ token γ]: the exclusive ghost token held by the holder.
 *)

Definition spinlock_N : namespace := nroot .@ "spinlock".

Section spinlock_inv_proof.

Context `{!osirisGS Σ, !na_invG Σ}.

(* ------------------------------------------------------------------ *)
(* Ghost predicates *)


(** Invariant content.  When the lock is free ([b = false]) it stores
    [token γ ∗ ▷R]; the [▷] absorbs the later introduced by [iInv]. *)
Definition lock_inv (γ : gname) (r : record) (R : iProp Σ) : iProp Σ :=
  r ↦ #true ∨ (r ↦ #false ∗ token γ ∗ ▷R).

(* [is_ref r] is kept outside the invariant: the CAS and the store find the
   field of [r] in a step of their own, before the atomic one. *)
Definition is_lock (γ : gname) (r : record) (R : iProp Σ) : iProp Σ :=
  is_ref r ∗ inv spinlock_N (lock_inv γ r R).

Definition locked (γ : gname) : iProp Σ := token γ.

(* ------------------------------------------------------------------ *)
(* Specifications *)


(* [create ()] allocates [Atomic.make false] and exposes the lock.  The
   caller may initialise it with any [▷R] to receive [is_lock γ r R]. *)
Definition create_spec create : iProp Σ :=
  {{ True }}
  create u : unit
  {{ RET (r : record); ∀ (R : iProp Σ), ▷R ={⊤}=∗ ∃ γ, is_lock γ r R }}.

(* Acquiring the lock transfers ownership of [locked γ] and [▷R]. *)
Definition acquire_spec acquire : iProp Σ :=
  {{ ∀ γ (R : iProp Σ); is_lock γ r R }}
  acquire r : record
  {{ RET (_ : unit); locked γ ∗ ▷R }}.

(* Releasing requires the holder to give back [locked γ] and [▷R]. *)
Definition release_spec release : iProp Σ :=
  {{ ∀ γ (R : iProp Σ); is_lock γ r R ∗ locked γ ∗ ▷R }}
  release r : record
  {{ RET (_ : unit); True }}.

(* ------------------------------------------------------------------ *)
(* Module-level theorem *)

Lemma spinlock_inv_proof η :
  ⊢ EWP (eval_mexpr η __main)
    {{ context [
         var_spec "create"  create_spec;
         var_spec "acquire" acquire_spec;
         var_spec "release" release_spec
       ] {["create"; "acquire"; "release"]} }}.
Proof.
  iApply imp_module.

  (* ------------------------------------------------------------------ *)
  (* Subgoal: [let create () = Atomic.make false] *)

  iApply (imp_sitems_let create_spec).
  { unfold create_spec.
    iApply (imp_EAnon_pers τ[unit]).
    iIntros "!>" ([]) "_".
    iApply imp_please; iNext.
    imp_match.
    (* After [Atomic.make false] we have [r ↦ #false]; use it to build the
       invariant. *)
    iApply (imp_wand).
    { imp_ref false. }
    iIntros (r) "Hr".
    iDestruct (ref_pointsto_is_ref with "Hr") as "[#Href Hr]".
    (* Goal: ∀ R, ▷R ={⊤}=∗ ∃ γ, is_lock γ r R *)
    iIntros (R) "HR".
    iMod token_alloc as "(%γ & Htok)".
    iMod (inv_alloc spinlock_N _ (lock_inv γ r R) with "[Hr Htok HR]") as "#Hinv".
    { (* Provide ▷ (lock_inv γ r R) with b = false via [later_intro]. *)
      iNext. iRight. iFrame. }
    iModIntro. iExists γ. iFrame "#". }

  iIntros (create) "#Hcreate".

  (* ------------------------------------------------------------------ *)
  (* Subgoal: [let acquire lk = while not (Atomic.compare_and_set lk false true) do () done] *)

  iApply (imp_sitems_let acquire_spec).
  { unfold acquire_spec.
    iApply (imp_EAnon_pers τ[record]).
    (* After introducing [r : record], the spec universally quantifies over
       [γ] and [R]; we introduce them here. *)
    iIntros "!>" (r).
    iIntros (γ R) "#[Href Hinv]".
    iApply imp_please; iNext.

    (* Subgoal: [while not (Atomic.compare_and_set lk false true) do () done] *)
    iApply (imp_EWhile (λ b, if b then True else locked γ ∗ ▷ R)%I).
    - (* I true *)
      done.
    - (* Condition: the CAS on the field of [r] *)
      iIntros "!> _".
      iApply imp_EBoolNeg.

      iApply (imp_CAS_ref_inv (A:=bool) with "Hinv Href"); try imp_step. set_solver.
      iIntros "!>" (??) "-> -> [Hl | (Hl & Htok & HR) ]".

      + (* Subcase: the CAS returned true. *)
        iFrame.
        iIntros "!> Hl".
        iSplitL. { iLeft. iApply "Hl". } done.

      + (* Subcase: the CAS returned false. *)
        iFrame.
        iIntros "!> Hl".
        simpl. iFrame.

    - (* Evaluating the body. *)
      iIntros "!> _".
      by iApply imp_EUnit. }

  iIntros (acquire) "#Hacquire".

  (* ------------------------------------------------------------------ *)
  (* Subgoal: [let release lk = lk := false] *)
  iApply (imp_sitems_let release_spec).
  { unfold release_spec.
    iApply (imp_EAnon_pers τ[record]).
    iIntros "!>" (r).
    iIntros (γ R) "(#[Href Hinv] & Htok & HR)".
    iApply imp_please; iNext.
    (* Open the invariant around the store: get [r ↦ #b] in hand, store
       [false], then close with [r ↦ #false ∗ token γ ∗ ▷R]. *)
    iApply (imp_assign_inv (A:=bool) with "Hinv Href"); try imp_step. set_solver.
    iIntros "!>" (?) "-> Hopened".
    iDestruct "Hopened" as "[ $ | ($ & >Htok' & HR') ]".
    - iIntros "!> Hl".
      iSplitL. { iRight. iFrame. }
      done.
    - (* This case is impossible: we own [token γ],
         so the lock cannot have been open. *)
      iPoseProof (token_exclusive with "Htok Htok'") as "[]". }

  iIntros (release) "#Hrelease".

  (* ------------------------------------------------------------------ *)
  (* Conclude                                                            *)
  iApply imp_sitems_nil.
  iFrame "#"; simpl. auto.
Qed.

End spinlock_inv_proof.
