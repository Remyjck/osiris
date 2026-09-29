From iris.base_logic.lib Require Import invariants token.

From osiris Require Import osiris.
From osiris.examples Require Import og_spinlock.

(** * Invariant-based spinlock specification

    We follow the CMRA from Iris' [spin_lock] example, where we have:

    – [lock_inv γ l R]: the physical lock bit together with the user
      resource [R] and an exclusive token; the resource lives behind [▷].
    – [is_lock γ l R ≔ inv N (lock_inv γ l R)]: a *persistent* handle
      handed to every caller.
    – [locked γ ≔ token γ]: the exclusive ghost token held by the holder.
 *)

Definition spinlock_N : namespace := nroot .@ "spinlock".

Section spinlock_inv_proof.

Context `{!osirisGS Σ, !na_invG Σ}.

(* ------------------------------------------------------------------ *)
(* Ghost predicates *)


(** Invariant content.  When the lock is free ([b = false]) it stores
    [token γ ∗ ▷R]; the [▷] absorbs the later introduced by [iInv]. *)
Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
  l ↦ #true ∨ (l ↦ #false ∗ token γ ∗ ▷R).

Definition is_lock (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
  inv spinlock_N (lock_inv γ l R).

Definition locked (γ : gname) : iProp Σ := token γ.

(* ------------------------------------------------------------------ *)
(* Specifications *)


(* [create ()] allocates [ref false] and exposes the lock.  The caller
   may initialise it with any [▷R] to receive [is_lock γ l R]. *)
Definition create_spec create : iProp Σ :=
  {{ True }}
  create u : unit
  {{ RET (l : loc); ∀ (R : iProp Σ), ▷R ={⊤}=∗ ∃ γ, is_lock γ l R }}.

(* Acquiring the lock transfers ownership of [locked γ] and [▷R]. *)
Definition acquire_spec acquire : iProp Σ :=
  {{ ∀ γ (R : iProp Σ); is_lock γ l R }}
  acquire l : loc
  {{ RET (_ : unit); locked γ ∗ ▷R }}.

(* Releasing requires the holder to give back [locked γ] and [▷R]. *)
Definition release_spec release : iProp Σ :=
  {{ ∀ γ (R : iProp Σ); is_lock γ l R ∗ locked γ ∗ ▷R }}
  release l : loc
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
  (* Subgoal: [let create () = ref false] *)

  iApply (imp_sitems_let create_spec).
  { unfold create_spec.
    iApply (imp_EAnon_pers τ[unit]).
    iIntros "!>" ([]) "_".
    iApply imp_please; iNext.
    imp_match.
    (* After [ref false] we have [l ↦ #false]; use it to build the invariant. *)
    iApply (imp_wand).
    { imp_ref false. }
    iIntros (l) "Hl".
    (* Goal: ∀ R, ▷R ={⊤}=∗ ∃ γ, is_lock γ l R *)
    iIntros (R) "HR".
    iMod token_alloc as "(%γ & Htok)".
    iMod (inv_alloc spinlock_N _ (lock_inv γ l R) with "[Hl Htok HR]") as "#Hinv".
    { (* Provide ▷ (lock_inv γ l R) with b = false via [later_intro]. *)
      iNext. iRight. iFrame. }
    iModIntro. iExists γ. iExact "Hinv". }

  iIntros (create) "#Hcreate".

  (* ------------------------------------------------------------------ *)
  (* Subgoal: [let acquire lk = while !lk do () done; lk := true] *)

  iApply (imp_sitems_let acquire_spec).
  { unfold acquire_spec.
    iApply (imp_EAnon_pers τ[loc]).
    (* After introducing [l : loc], the spec universally quantifies over [γ] and
       [R]; we introduce them here. *)
    iIntros "!>" (l).
    iIntros (γ R) "#Hinv".
    iApply imp_please; iNext.

    (* Subgoal: [while not (Atomic.set_and_compare lk false true) do () done] *)
    iApply (imp_EWhile (λ b, if b then True else locked γ ∗ ▷ R)%I).
    - (* I true *)
      done.
    - (* Condition: load [!lk] directly from [l ↦ #b'] *)
      iIntros "!> _".
      iApply imp_EBoolNeg.

      iApply (imp_CAS_inv (A:=bool) with "Hinv"); try imp_step. set_solver.
      iIntros "!>" (???) "-> -> -> [Hl | (Hl & Htok & HR) ]".

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
    iApply (imp_EAnon_pers τ[loc]).
    iIntros "!>" (l).
    iIntros (γ R) "(#Hinv & Htok & HR)".
    iApply imp_please; iNext.
    (* Open invariant non-atomically: get [l ↦ #b] in hand, store [false],
       then close with [l ↦ #false ∗ token γ ∗ ▷R]. *)
    iApply (imp_store_inv (A:=bool) with "Hinv"); try imp_step. set_solver.
    iIntros "!>" (??) "-> -> Hopened".
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
