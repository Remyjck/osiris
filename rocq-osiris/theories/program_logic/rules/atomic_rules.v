From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants proph_map.

(* [big_opLZ] is imported here, ahead of the osiris modules: it
   re-exports stdpp's [x ← _ ; _] notation, which would otherwise
   shadow the [micro] one that this file's statements are written in. *)
From osiris.utils Require Import big_opLZ.

From osiris.lang Require Import lang.
Require Import osiris_utils.
Require Import subjective_step ewp tactics.
Require Import basic_rules impure_rules stop_rules record_rules ref_rules ipattern_rules proph_rules.
From osiris.utils Require Import list_z.

Import ewp_rules_tactics.

(** This file provides atomicity instances for memory operations and derived [EWP] rules for atomic access. *)

Instance crash_atomic {V X} :
  subjective_step.Atomic (@Crash V X).
Proof. constructor. inversion H; subst. inversion H4. Qed.

Global Instance load_atomic {E} l :
  subjective_step.Atomic (load (E:=E) l).
Proof.
  unfold subjective_step.Atomic. intros.

  destruct_subjective_step.
  unfold step_load_2.
  case_location_lookup; by econstructor.
Qed.

Global Instance efieldload_atomic η p :
  subjective_step.Atomic (eval η (EFieldLoad (EPath p))).
Proof.
  simpl_eval.
  destruct (lookup_path η p); last apply _.
  destruct v; simpl; try (rewrite bind_crash; apply _).
  apply _.
Qed.

Global Instance exchange_atomic l v' :
  subjective_step.Atomic (exchange l v').
Proof.
  unfold subjective_step.Atomic. intros.

  destruct_subjective_step.
  unfold step_exchange_2.
  case_location_lookup; by econstructor.
Qed.

Global Instance store_atomic l v :
  subjective_step.Atomic (code.store l v).
Proof.
  unfold subjective_step.Atomic. intros.

  destruct_subjective_step.
  unfold step_exchange_2.
  case_location_lookup; by econstructor.
Qed.

Global Instance cas_atomic l seen v' :
  subjective_step.Atomic (cas l seen v').
Proof.
  unfold subjective_step.Atomic. intros.

  destruct_subjective_step.
  unfold step_cas_2.
  case_location_lookup; try by econstructor.
  destruct (phys_eq_val_store _ _ _) as [ [|] | ]; by econstructor.
Qed.

Global Instance faa_atomic l i :
  subjective_step.Atomic (faa l i).
Proof.
  unfold subjective_step.Atomic. intros.

  destruct_subjective_step.
  unfold step_faa_2.
  case_location_lookup; try by econstructor.
  rewrite /continue /=.
  destruct v; try by constructor.
  by econstructor.
Qed.

(* TCEq instances for to_eff and to_join: all concrete atomic operations
   are neither [Stop CPerf] nor [Stop CJoin], so both projections return [None]. *)

Global Instance to_eff_crash {V X} : TCEq (to_eff (@Crash V X)) None.
Proof. constructor. Qed.
Global Instance to_join_crash {V X} : TCEq (to_join (@Crash V X)) None.
Proof. constructor. Qed.

Global Instance to_eff_load {E} l : TCEq (to_eff (load (E:=E) l)) None.
Proof. constructor. Qed.
Global Instance to_join_load {E} l : TCEq (to_join (load (E:=E) l)) None.
Proof. constructor. Qed.

Global Instance to_eff_exchange l v : TCEq (to_eff (exchange l v)) None.
Proof. constructor. Qed.
Global Instance to_join_exchange l v : TCEq (to_join (exchange l v)) None.
Proof. constructor. Qed.

Global Instance to_eff_store l v : TCEq (to_eff (code.store l v)) None.
Proof. constructor. Qed.
Global Instance to_join_store l v : TCEq (to_join (code.store l v)) None.
Proof. constructor. Qed.

Global Instance to_eff_cas l seen v : TCEq (to_eff (cas l seen v)) None.
Proof. constructor. Qed.
Global Instance to_join_cas l seen v : TCEq (to_join (cas l seen v)) None.
Proof. constructor. Qed.

Global Instance to_eff_faa l i : TCEq (to_eff (faa l i)) None.
Proof. constructor. Qed.
Global Instance to_join_faa l i : TCEq (to_join (faa l i)) None.
Proof. constructor. Qed.

Section imp_atomic_rules.

  Context `{!osirisGS Σ}.
  Context {Ψ : iEff Σ} {ζ : exn → iProp Σ}.

  (* [imp_loadn] and the record rules are stated at this instance;
     without it, [list val] postconditions do not typecheck here. *)
  Local Instance notval_listval : NotVal (list val) := {}.

  (* [EFieldLoad e]. The evaluation of [e] is not part of the atomic step,
     so the mask-changing update is only entered once the location is
     known. *)
  Lemma imp_field_load_atomic `{Encode A} (E2 E1 : coPset) η e (Φ1 : loc → _) (Φ : A → _) :
    impure E1 (eval η e) Ψ ζ Φ1 -∗
    (∀ l, Φ1 l -∗
          |={E1,E2}=> ∃ dq a, ▷ l ↦ₗ{dq} #a ∗
                              ▷ (l ↦ₗ{dq} #a -∗ |={E2,E1}=> Φ a)) -∗
    impure E1 (eval η (EFieldLoad e)) Ψ ζ Φ.
  Proof.
    iIntros "He Hload". simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_loc with "He"). }
    iIntros (l) "HΦ1".
    iApply (imp_atomic' E1 E2).
    iMod ("Hload" with "HΦ1") as "(%dq & %a & Hl & Hload)".
    iApply (imp_load' with "Hl Hload").
  Qed.

  (* [EExchange e1 e2]: the exchanged-out value is handed to the closing
     wand. *)
  Lemma imp_exchange_atomic `{Encode A} (E2 E1 : coPset) η e1 e2
      (Φ1 : loc → _) (Φ2 : A → _) (Φ : A → _) :
    impure E1 (eval η e1) Ψ ζ Φ1 -∗
    impure E1 (eval η e2) Ψ ζ Φ2 -∗
    ▷ (|={E1,E2}=>
         ∀ l x, Φ1 l -∗ Φ2 x -∗
                ∃ a : A, ▷ l ↦ₗ #a ∗
                         ▷ (l ↦ₗ #x -∗ |={E2,E1}=> Φ a)) -∗
    impure E1 (eval η (EExchange e1 e2)) Ψ ζ Φ.
  Proof.
    iIntros "He1 He2 Hex". simpl_eval.
    iApply (imp_bind_par with "[He1] He2").
    { iApply (imp_as_loc with "He1"). }
    iIntros (l x) "HΦ1 HΦ2 !>".
    iApply (imp_atomic' E1 E2).
    iMod ("Hex" with "HΦ1 HΦ2") as "(%a & Hl & Hex)".
    iApply (imp_exchange' with "Hl Hex").
  Qed.

  (* [EFAA e1 e2]. *)
  Lemma imp_faa_atomic (E2 E1 : coPset) η e1 e2
      (Φ1 : loc → _) (Φ2 : Z → _) (Φ : Z → _) :
    impure E1 (eval η e1) Ψ ζ Φ1 -∗
    impure E1 (eval η e2) Ψ ζ Φ2 -∗
    ▷ (|={E1,E2}=>
         ∀ l i, Φ1 l -∗ Φ2 i -∗
                ∃ j : Z, ▷ l ↦ₗ #j ∗
                         ▷ (l ↦ₗ #(j + i) -∗ |={E2,E1}=> Φ j)) -∗
    impure E1 (eval η (EFAA e1 e2)) Ψ ζ Φ.
  Proof.
    iIntros "He1 He2 Hfaa". simpl_eval.
    iApply (imp_bind_par with "[He1] [He2]").
    { iApply (imp_as_loc with "He1"). }
    { iApply (imp_as_int with "He2"). }
    iIntros (l i) "HΦ1 HΦ2 !>".
    iApply (imp_atomic' E1 E2).
    iMod ("Hfaa" with "HΦ1 HΦ2") as "(%j & Hl & Hfaa)".
    iApply (imp_faa with "Hl Hfaa").
  Qed.

  Lemma imp_cas_atomic `{PhysEqDec A} (E2 E1 : coPset) η e1 e2 e3 (Φ1 : loc → _) (Φ2 Φ3 : A → _) (Φ : bool → _) :
    impure E1 (eval η e1) Ψ ζ Φ1 -∗
    impure E1 (eval η e2) Ψ ζ Φ2 -∗
    impure E1 (eval η e3) Ψ ζ Φ3 -∗
    ▷ (|={E1,E2}=>
         ∀ l seen v',
         Φ1 l -∗ Φ2 seen -∗ Φ3 v' -∗
         ∃ v, ▷ l ↦ₗ #v ∗
              ▷ (l ↦ₗ (if phys_eq_val_ v seen then #v' else #v) -∗
                 |={E2,E1}=> Φ (phys_eq_val_ v seen))) -∗
    impure E1 (eval η (ECAS e1 e2 e3)) Ψ ζ Φ.
  Proof.
    iIntros "He1 He2 He3 Hcas".
    simpl_eval.
    iApply (imp_bind_par (A1:=loc * A) with "[He1 He2] He3").
    { iApply (imp_par with "[He1] He2").
      iApply (imp_as_loc with "He1"). }
    iIntros ((l & seen) x) "(HΦ1 & HΦ2) HΦ3 !>".
    iApply (imp_atomic' E1 E2).
    iMod ("Hcas" with "HΦ1 HΦ2 HΦ3") as "(%v & Hl & Hcas)".
    iApply (imp_cas with "Hl Hcas").
  Qed.

  Lemma imp_EResolve_ECAS_atomic `{PhysEqDec A} (E2 E1 : coPset) η e1 e2 e3
      (ep : path) (ev : proph_arg)
      (p : proph_id) (v : val) (pvs : list (val * val))
      (Φ1 : loc → _) (Φ2 Φ3 : A → _) (Φ : bool → _) :
    lookup_path η ep = Some #p →
    eval_proph_arg η ev = Some v →
    impure E1 (eval η e1) Ψ ζ Φ1 -∗
    impure E1 (eval η e2) Ψ ζ Φ2 -∗
    impure E1 (eval η e3) Ψ ζ Φ3 -∗
    proph p pvs -∗
    ▷ (|={E1,E2}=>
         ∀ l seen v',
         Φ1 l -∗ Φ2 seen -∗ Φ3 v' -∗
         ∃ w, ▷ l ↦ₗ #w ∗
              ▷ (∀ pvs', ⌜pvs = (♯(phys_eq_val_ w seen), v) :: pvs'⌝ -∗
                   proph p pvs' -∗
                   l ↦ₗ (if phys_eq_val_ w seen then #v' else #w) -∗
                   |={E2,E1}=> Φ (phys_eq_val_ w seen))) -∗
    impure E1 (eval η (EResolve (ECAS e1 e2 e3) ep ev)) Ψ ζ Φ.
  Proof.
    iIntros (Hp Hv) "He1 He2 He3 Hproph Hcas".
    simpl_eval.
    rewrite (bind_proph_args Hp Hv).
    iApply (imp_bind_par (A1:=loc * A) with "[He1 He2] He3").
    { iApply (imp_par with "[He1] He2").
      iApply (imp_as_loc with "He1"). }
    iIntros ((l & seen) x) "(HΦ1 & HΦ2) HΦ3 !>".
    rewrite /resolve.
    (* [resolve_atomic]: the resolution is still a single thread step, so
       the invariant may stay open across it. *)
    iApply (imp_atomic' E1 E2).
    iMod ("Hcas" with "HΦ1 HΦ2 HΦ3") as "(%w & Hl & Hcas)".
    iModIntro.
    iApply (ewp_resolve with "Hproph"); first apply call_is_atomic_cas.
    iApply (imp_stop_cas with "Hl"). iIntros "!> Hl".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    iIntros (pvs2) "%Heq2 Hp2".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    iApply ("Hcas" with "[//] Hp2 Hl").
  Qed.

  Lemma imp_EResolve_EExchange_atomic `{Encode A} (E2 E1 : coPset) η e1 e2
      (ep : path) (ev : proph_arg)
      (p : proph_id) (v : val) (Φ1 : loc → _) (Φ2 : A → _) (Φ : A → _) :
    lookup_path η ep = Some #p →
    eval_proph_arg η ev = Some v →
    impure E1 (eval η e1) Ψ ζ Φ1 -∗
    impure E1 (eval η e2) Ψ ζ Φ2 -∗
    ▷ (|={E1,E2}=>
         ∀ l x, Φ1 l -∗ Φ2 x -∗
                ∃ (a : A) (pvs : list (val * val)),
                  ▷ l ↦ₗ #a ∗ proph p pvs ∗
                  ▷ (∀ pvs', ⌜pvs = (#a, v) :: pvs'⌝ -∗ proph p pvs' -∗
                       l ↦ₗ #x -∗ |={E2,E1}=> Φ a)) -∗
    impure E1 (eval η (EResolve (EExchange e1 e2) ep ev)) Ψ ζ Φ.
  Proof.
    iIntros (Hp Hv) "He1 He2 Hex".
    simpl_eval.
    rewrite (bind_proph_args Hp Hv).
    iApply (imp_bind_par with "[He1] He2").
    { iApply (imp_as_loc with "He1"). }
    iIntros (l x) "HΦ1 HΦ2 !>".
    rewrite /resolve.
    iApply (imp_atomic' E1 E2).
    iMod ("Hex" with "HΦ1 HΦ2") as "(%a & %pvs & Hl & Hproph & Hex)".
    iModIntro.
    iApply (ewp_resolve with "Hproph"); first apply call_is_atomic_exchange.
    iApply (imp_stop_exchange with "Hl"). iIntros "!> Hl".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    iIntros (pvs2) "%Heq2 Hp2".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    iApply ("Hex" with "[//] Hp2 Hl").
  Qed.

  (* The [VInline] variant of [imp_cas_atomic]; see [imp_stop_cas_inline].
     The expected value [seen] must be an inline record, and the physical
     comparison is resolved by the [blockTag] fractions provided for the
     current and expected blocks. *)
  Lemma imp_cas_inline_atomic (E2 E1 : coPset) η e1 e2 e3
      (Φ1 : loc → _) (Φ2 Φ3 : val → _) (Φ : bool → _) :
    impure E1 (eval η e1) Ψ ζ Φ1 -∗
    impure E1 (eval η e2) Ψ ζ Φ2 -∗
    impure E1 (eval η e3) Ψ ζ Φ3 -∗
    ▷ (|={E1,E2}=>
         ∀ l seen v',
         Φ1 l -∗ Φ2 seen -∗ Φ3 v' -∗
         ∃ c cs (r rs : record) dq1 dq2 t,
           ⌜seen = VInline cs rs⌝ ∗
           ▷ l ↦ₗ VInline c r ∗ ▷ blockTag r dq1 t ∗ ▷ blockTag rs dq2 Mut ∗
           ▷ (l ↦ₗ (if locations.eqb r rs then v' else VInline c r) -∗
              blockTag r dq1 t -∗ blockTag rs dq2 Mut -∗
              |={E2,E1}=> Φ (locations.eqb r rs))) -∗
    impure E1 (eval η (ECAS e1 e2 e3)) Ψ ζ Φ.
  Proof.
    iIntros "He1 He2 He3 Hcas".
    simpl_eval.
    iApply (imp_bind_par (A1:=loc * val) with "[He1 He2] He3").
    { iApply (imp_par with "[He1] He2").
      iApply (imp_as_loc with "He1"). }
    iIntros ((l & seen) x) "(HΦ1 & HΦ2) HΦ3 !>".
    iApply (imp_atomic' E1 E2).
    iMod ("Hcas" with "HΦ1 HΦ2 HΦ3")
      as "(%c & %cs & %r & %rs & %dq1 & %dq2 & %t & -> & Hl & Hr & Hrs & Hcas)".
    iApply (imp_cas_inline with "Hl Hr Hrs Hcas").
  Qed.

  (* Atomically reading a record field. The evaluation of [ERecordAccess]
     finds the location [l] of the field (via the persistent [field_at]
     knowledge), then performs a single atomic load of [l]. Ownership of
     [l] is only required inside the atomic step, which allows it to come
     from an invariant. *)
  Lemma imp_ERecordAccess_atomic `{Encode A} (E2 E1 : coPset) η e f (r : record) l
      (Φ : A → _) :
    ▷ field_at r f l -∗
    impure E1 (eval η e) Ψ ζ (λ r' : record, ⌜r' = r⌝) -∗
    ▷ (|={E1,E2}=> ∃ a, ▷ l ↦ₗ #a ∗ ▷ (l ↦ₗ #a -∗ |={E2,E1}=> Φ a)) -∗
    impure E1 (eval η (ERecordAccess e f)) Ψ ζ Φ.
  Proof.
    rewrite {1}/field_at.
    iIntros "(%ls & #Hblock & >%Hf) He Hload".
    simpl_eval.
    iApply (imp_bind with "[He]").
    { iApply (imp_as_record with "He"). }
    iIntros (?) "->".
    iApply (imp_bind (A1:=(mut_tag * list loc)) with "[Hload]").
    { iApply (imp_load_block_ghost' with "Hblock Hload"). }
    iIntros ((? & ?)) "(-> & Hload) /=".
    rewrite Hf.
    iApply (imp_atomic' E1 E2).
    iMod "Hload" as "(%v & Hl & Hload)".
    iApply (imp_load' with "Hl Hload").
  Qed.

  (* A resolved field read, [e.f [@resolve p v]]. The prophecy is resolved
     at the load of the field, which is the read's linearization point. The
     atomic update is that of [imp_ERecordAccess_atomic]; the prophecy's
     head is handed to [Hcont] together with what the update produced. *)
  Lemma imp_EResolve_ERecordAccess_atomic `{Encode A} (E2 E1 : coPset) η e f (r : record) l
      (ep : path) (ev : proph_arg) (p : proph_id) (v : val) pvs (Φe Φ : A → _) :
    lookup_path η ep = Some #p →
    eval_proph_arg η ev = Some v →
    ▷ field_at r f l -∗
    proph p pvs -∗
    impure E1 (eval η e) Ψ ζ (λ r' : record, ⌜r' = r⌝) -∗
    ▷ (|={E1,E2}=> ∃ a, ▷ l ↦ₗ #a ∗ ▷ (l ↦ₗ #a -∗ |={E2,E1}=> Φe a)) -∗
    (∀ a pvs', ⌜pvs = (♯a, v) :: pvs'⌝ -∗ proph p pvs' -∗ Φe a -∗ Φ a) -∗
    impure E1 (eval η (EResolve (ERecordAccess e f) ep ev)) Ψ ζ Φ.
  Proof.
    rewrite {1}/field_at.
    iIntros (Hp Hv) "(%ls & #Hblock & >%Hf) Hproph He Hload Hcont".
    simpl_eval.
    rewrite (bind_proph_args Hp Hv).
    iApply (imp_bind with "[He]").
    { iApply (imp_as_record with "He"). }
    iIntros (?) "->".
    iApply (imp_bind (A1:=(mut_tag * list loc)) with "[Hload]").
    { iApply (imp_load_block_ghost' with "Hblock Hload"). }
    iIntros ((? & ?)) "(-> & Hload) /=".
    rewrite Hf /resolve.
    iApply (imp_atomic' E1 E2).
    iMod "Hload" as (a) "[Hl Hload]".
    iModIntro.
    iApply (ewp_resolve with "Hproph"); first apply call_is_atomic_load.
    iApply (imp_stop_load with "Hl"). iIntros "!> Hl".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    iIntros (pvs2) "%Heq2 Hp2".
    rewrite /continue /=. iApply imp_ret; [ encode | ].
    iMod ("Hload" with "Hl") as "HΦe".
    iModIntro. iApply ("Hcont" with "[//] Hp2 HΦe").
  Qed.

  Lemma imp_ERecordSet_atomic `{Encode A} (E2 E1 : coPset) η e1 e2 f (r : record) l
      (Φ2 : A → _) (Φ : unit → _) :
    ▷ field_at r f l -∗
    impure E1 (eval η e1) Ψ ζ (λ r' : record, ⌜r' = r⌝) -∗
    impure E1 (eval η e2) Ψ ζ Φ2 -∗
    ▷ (∀ a, Φ2 a -∗
            |={E1,E2}=> ∃ v, ▷ l ↦ₗ v ∗ ▷ (l ↦ₗ #a -∗ |={E2,E1}=> Φ ())) -∗
    impure E1 (eval η (ERecordSet e1 f e2)) Ψ ζ Φ.
  Proof.
    rewrite {1}/field_at.
    iIntros "(%ls & #Hblock & >%Hf) He1 He2 Hstore".
    simpl_eval.
    iApply (imp_bind_par with "[He1] He2").
    { iApply (imp_as_record with "He1"). }
    iIntros (r' a) "-> HΦ2".
    iNext.
    iApply (imp_bind (A1:=(mut_tag * list loc)) with "[Hstore]").
    { iApply (imp_load_block_ghost' with "Hblock Hstore"). }
    iIntros ((? & ?)) "(-> & Hstore) /=".
    rewrite Hf.
    iApply (imp_atomic' E1 E2).
    iMod ("Hstore" with "HΦ2") as (v) "[Hl Hstore]".
    iApply (imp_store' with "Hl Hstore").
  Qed.

  (* The same two rules, with the field's cell seen through its record:
     the atomic update is stated with [r ↦[f] _]. *)
  Lemma imp_ERecordAccess_field_atomic `{Encode A} (E2 E1 : coPset) η e f (r : record) l
      (Φ : A → _) :
    ▷ field_at r f l -∗
    impure E1 (eval η e) Ψ ζ (λ r' : record, ⌜r' = r⌝) -∗
    ▷ (|={E1,E2}=> ∃ a, ▷ r ↦[f] #a ∗ ▷ (r ↦[f] #a -∗ |={E2,E1}=> Φ a)) -∗
    impure E1 (eval η (ERecordAccess e f)) Ψ ζ Φ.
  Proof.
    iIntros "#Hf He Hload".
    iApply (imp_ERecordAccess_atomic with "Hf He").
    iIntros "!>". iMod "Hload" as (a) "[Ha Hload]".
    iModIntro. iExists a. iSplitL "Ha".
    { iNext. iDestruct (field_pointsto_at with "Hf") as "[Hto _]". by iApply "Hto". }
    iIntros "!> Hl". iApply "Hload".
    iDestruct (field_pointsto_at _ _ _ _ #a with "Hf") as "[_ Hfrom]".
    by iApply "Hfrom".
  Qed.

  Lemma imp_ERecordSet_field_atomic `{Encode A} (E2 E1 : coPset) η e1 e2 f (r : record) l
      (Φ2 : A → _) (Φ : unit → _) :
    ▷ field_at r f l -∗
    impure E1 (eval η e1) Ψ ζ (λ r' : record, ⌜r' = r⌝) -∗
    impure E1 (eval η e2) Ψ ζ Φ2 -∗
    ▷ (∀ a, Φ2 a -∗
            |={E1,E2}=> ∃ v, ▷ r ↦[f] v ∗ ▷ (r ↦[f] #a -∗ |={E2,E1}=> Φ ())) -∗
    impure E1 (eval η (ERecordSet e1 f e2)) Ψ ζ Φ.
  Proof.
    iIntros "#Hf He1 He2 Hstore".
    iApply (imp_ERecordSet_atomic with "Hf He1 He2").
    iIntros "!>" (a) "HΦ2". iMod ("Hstore" with "HΦ2") as (v) "[Hv Hstore]".
    iModIntro. iExists v. iSplitL "Hv".
    { iNext. iDestruct (field_pointsto_at with "Hf") as "[Hto _]". by iApply "Hto". }
    iIntros "!> Hl". iApply "Hstore".
    iDestruct (field_pointsto_at _ _ _ _ #a with "Hf") as "[_ Hfrom]".
    by iApply "Hfrom".
  Qed.

  (* Atomic operations on a reference: [!e] and [e1 := e2]. Finding the
     field is a separate step from the access, so the shape of [r] is
     required up front; only the points-to is needed inside the atomic
     step. *)
  Lemma imp_deref_atomic `{Encode A} (E2 E1 : coPset) η e (r : record) (Φ : A → _) :
    ▷ is_ref r -∗
    impure E1 (eval η e) Ψ ζ (λ r' : record, ⌜r' = r⌝) -∗
    ▷ (|={E1,E2}=> ∃ a, ▷ r ↦ #a ∗ ▷ (r ↦ #a -∗ |={E2,E1}=> Φ a)) -∗
    impure E1 (eval η (ELoad e)) Ψ ζ Φ.
  Proof.
    rewrite eval_ELoad.
    iIntros ">#Hr He Hload".
    iDestruct (is_ref_field_at with "Hr") as (l) "[Hf Hls]".
    iApply (imp_ERecordAccess_atomic with "Hf He").
    iNext. iMod "Hload" as (a) "[Ha Hload]".
    iModIntro. iExists a. iSplitL "Ha".
    { iNext. iDestruct (ref_pointsto_at with "Hls") as "[Hto _]".
      iDestruct ("Hto" with "Ha") as "[_ $]". }
    iIntros "!> Hl". iApply "Hload".
    iDestruct (ref_pointsto_at _ _ _ #a with "Hls") as "[_ Hfrom]".
    iApply "Hfrom". rewrite /is_ref. iDestruct "Hr" as "[$ _]". iFrame.
  Qed.

  (* A resolved lookup [!e [@resolve p v]]: the prophecy is resolved at the
     load of the reference's field. See [imp_EResolve_ERecordAccess_atomic]. *)
  Lemma imp_EResolve_ELoad_atomic `{Encode A} (E2 E1 : coPset) η e (r : record)
      (ep : path) (ev : proph_arg) (p : proph_id) (v : val) pvs (Φe Φ : A → _) :
    lookup_path η ep = Some #p →
    eval_proph_arg η ev = Some v →
    ▷ is_ref r -∗
    proph p pvs -∗
    impure E1 (eval η e) Ψ ζ (λ r' : record, ⌜r' = r⌝) -∗
    ▷ (|={E1,E2}=> ∃ a, ▷ r ↦ #a ∗ ▷ (r ↦ #a -∗ |={E2,E1}=> Φe a)) -∗
    (∀ a pvs', ⌜pvs = (♯a, v) :: pvs'⌝ -∗ proph p pvs' -∗ Φe a -∗ Φ a) -∗
    impure E1 (eval η (EResolve (ELoad e) ep ev)) Ψ ζ Φ.
  Proof.
    rewrite eval_EResolve_ELoad.
    iIntros (Hp Hv) ">#Hr Hproph He Hload Hcont".
    iDestruct (is_ref_field_at with "Hr") as (l) "[Hf Hls]".
    iApply (imp_EResolve_ERecordAccess_atomic with "Hf Hproph He [Hload] Hcont");
      [ exact Hp | exact Hv | ].
    iNext. iMod "Hload" as (a) "[Ha Hload]".
    iModIntro. iExists a. iSplitL "Ha".
    { iNext. iDestruct (ref_pointsto_at with "Hls") as "[Hto _]".
      iDestruct ("Hto" with "Ha") as "[_ $]". }
    iIntros "!> Hl". iApply "Hload".
    iDestruct (ref_pointsto_at _ _ _ #a with "Hls") as "[_ Hfrom]".
    iApply "Hfrom". rewrite /is_ref. iDestruct "Hr" as "[$ _]". iFrame.
  Qed.

  Lemma imp_assign_atomic `{Encode A} (E2 E1 : coPset) η e1 e2 (r : record)
      (Φ2 : A → _) (Φ : unit → _) :
    ▷ is_ref r -∗
    impure E1 (eval η e1) Ψ ζ (λ r' : record, ⌜r' = r⌝) -∗
    impure E1 (eval η e2) Ψ ζ Φ2 -∗
    ▷ (∀ a, Φ2 a -∗
            |={E1,E2}=> ∃ v, ▷ r ↦ v ∗ ▷ (r ↦ #a -∗ |={E2,E1}=> Φ ())) -∗
    impure E1 (eval η (EStore e1 e2)) Ψ ζ Φ.
  Proof.
    rewrite eval_EStore.
    iIntros ">#Hr He1 He2 Hstore".
    iDestruct (is_ref_field_at with "Hr") as (l) "[Hf Hls]".
    iApply (imp_ERecordSet_atomic with "Hf He1 He2").
    iIntros "!>" (a) "HΦ2".
    iMod ("Hstore" with "HΦ2") as (v) "[Hv Hstore]".
    iModIntro. iExists v. iSplitL "Hv".
    { iNext. iDestruct (ref_pointsto_at with "Hls") as "[Hto _]".
      iDestruct ("Hto" with "Hv") as "[_ $]". }
    iIntros "!> Hl". iApply "Hstore".
    iDestruct (ref_pointsto_at _ _ _ #a with "Hls") as "[_ Hfrom]".
    iApply "Hfrom". rewrite /is_ref. iDestruct "Hr" as "[$ _]". iFrame.
  Qed.

  (* A [CLoad] instruction followed by a pure continuation is atomic. *)
  Lemma stop_load_atomic_outcome {A X} (l : loc) (k : outcome2 val exn → micro A X) :
    (∀ o, is_outcome3 (k o)) →
    subjective_step.Atomic (Stop CLoad l k).
  Proof.
    intros Hk. unfold subjective_step.Atomic. intros.
    destruct_subjective_step.
    unfold step_load_2.
    case_location_lookup; try apply Hk; by econstructor.
  Qed.

  Global Instance to_eff_stop_load {A X} (l : loc) (k : outcome2 val exn → micro A X) :
    TCEq (to_eff (Stop CLoad l k)) None.
  Proof. constructor. Qed.
  Global Instance to_join_stop_load {A X} (l : loc) (k : outcome2 val exn → micro A X) :
    TCEq (to_join (Stop CLoad l k)) None.
  Proof. constructor. Qed.

  (* [bind_stop], generalized to a [Stop] whose code error type differs
     from the monad's error type. Holds by definitional unfolding. *)
  Lemma bind_stop_gen {A B E X Y E'} (c : C.code X Y E') (x : X)
      (k : outcome2 Y E' → micro A E) (f : A → micro B E) :
    ('a ← Stop c x k; f a) = Stop c x (λ o, 'a ← k o; f a).
  Proof. reflexivity. Qed.

  (* Atomically matching a record pattern [{ f = x }] that binds one
     field to a variable. Since a record pattern reads only the fields
     it mentions, matching this one is a single [load] followed by pure
     code so the field's points-to need not be held by the caller: it
     may come from an invariant, which the caller opens for the
     duration of that step. *)

  Lemma ipat_PRecord_atomic `{Encode A} (E2 E1 : coPset) η δ x (f : field) (r : record)
      (l : loc) (dq : dfrac) (Φ : env → iProp Σ) (ψ : iProp Σ) :
    ▷ field_at r f l -∗
    ▷ (|={E1,E2}=> ∃ (v : A), ▷ l ↦ₗ{dq} #v ∗
         ▷ (l ↦ₗ{dq} #v -∗ |={E2,E1}=> Φ ((x, #v) :: δ))) -∗
    ipattern (E:=E1) (Ψ:=Ψ) η δ (PRecord [(f, PVar x)]) (VRecord r) Φ ψ.
  Proof.
    rewrite {1}/field_at.
    iIntros "(%ls & #Hlocs & >%Hf) Hload".
    rewrite /ipattern. simpl_eval_pat.
    iApply (imp_bind (A1:=(mut_tag * list loc)) with "[Hload]").
    { iApply (imp_load_block_ghost' with "Hlocs Hload"). }
    iIntros ((t & ls')) "(-> & Hload) /=".
    rewrite Hf.
    rewrite bind_bind {1}/load bind_stop_gen.
    match goal with
    | |- context [ Stop CLoad ?l ?k ] =>
        pose proof (stop_load_atomic_outcome l k) as Hat
    end.
    specialize (Hat ltac:(intros [?|?];
      [ eapply subjective_step.is_ret
      | eapply subjective_step.is_crash ]; reflexivity)).
    iApply (imp_atomic' E1 E2).
    iMod "Hload" as "(%v & Hl & Hload)".
    iApply (imp_stop_load with "Hl").
    iModIntro. iIntros "!> Hl".
    iApply imp_ret; first done.
    iApply ("Hload" with "Hl").
  Qed.

  (* The same single-field pattern read, when the field's points-to is
     held by the caller at some fraction. *)

  Lemma ipat_PRecord_pers `{Encode A} (E1 : coPset) η δ x (f : field) (r : record)
      (l : loc) (dq : dfrac) (v : A) (Φ : env → iProp Σ) (ψ : iProp Σ) :
    ▷ field_at r f l -∗
    ▷ l ↦ₗ{dq} #v -∗
    ▷ (l ↦ₗ{dq} #v -∗ Φ ((x, #v) :: δ)) -∗
    ipattern (E:=E1) (Ψ:=Ψ) η δ (PRecord [(f, PVar x)]) (VRecord r) Φ ψ.
  Proof.
    iIntros "#Hf Hl HΦ".
    iApply (ipat_PRecord_atomic (A:=A) E1 E1 with "Hf [Hl HΦ]").
    iNext. iModIntro. iExists v. iFrame "Hl".
    iIntros "!> Hl". iModIntro. by iApply "HΦ".
  Qed.

End imp_atomic_rules.

Section imp_inv_rules.

  Context `{!osirisGS Σ}.
  Context {E : coPset} {Ψ : iEff Σ} {ζ : exn → iProp Σ}.
  Context {N : namespace} {P : iProp Σ}.

  Lemma imp_assign_inv `{Encode A} η e1 e2 (r : record) (Φ2 : A → _) (Φ : () → _) :
    ↑N ⊆ E →
    inv N P -∗
    ▷ is_ref r -∗
    impure E (eval η e1) Ψ ζ (λ r' : record, ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    (▷ ∀ x, Φ2 x -∗
            ▷ P -∗
            ∃ v, ▷ r ↦ v ∗
                 ▷ (r ↦ #x -∗ ▷ P ∗ Φ ())) -∗
    impure E (eval η (EStore e1 e2)) Ψ ζ Φ.
  Proof.
    iIntros (Hsubset) "#Hinv Hr He1 He2 Hstore".
    iApply (imp_assign_atomic (E ∖ ↑N) with "Hr He1 He2").
    iIntros "!>" (x) "HΦ2".
    iMod (inv_acc with "Hinv") as "[HP HClose]"; first assumption.
    iDestruct ("Hstore" with "HΦ2 HP") as "(% & $ & Hstore)".
    iIntros "!> !> Hl".
    iDestruct ("Hstore" with "Hl") as "[HP HΦ]".
    iMod ("HClose" with "HP").
    iApply "HΦ".
  Qed.

  Lemma imp_CAS_inv `{PhysEqDec A} η e1 e2 e3 (Φ1 : loc → _) (Φ2 Φ3 : A → _) (Φ : bool → _) :
    ↑N ⊆ E →
    inv N P -∗
    impure E (eval η e1) Ψ ζ Φ1 -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    impure E (eval η e3) Ψ ζ Φ3 -∗
    (▷ ∀ l seen v',
       Φ1 l -∗ Φ2 seen -∗ Φ3 v' -∗
       ▷ P -∗
       ∃ v, ▷ l ↦ₗ #v ∗
            ▷ (l ↦ₗ (if phys_eq_val_ v seen then #v' else #v) -∗
               ▷ P ∗ Φ (phys_eq_val_ v seen))) -∗
    impure E (eval η (ECAS e1 e2 e3)) Ψ ζ Φ.
  Proof.
    iIntros (Hsubset) "#Hinv He1 He2 He3 Hcas".
    iApply (imp_cas_atomic (E ∖ ↑N) with "He1 He2 He3").
    iNext.
    iPoseProof (inv_acc with "Hinv") as ">[HP HClose]". assumption.
    iIntros "!>" (l seen v') "HΦ1 HΦ2 HΦ3".
    iDestruct ("Hcas" with "HΦ1 HΦ2 HΦ3 HP") as "(% & $ & Hcas)".
    iIntros "!> Hl".
    iDestruct ("Hcas" with "Hl") as "[HP HΦ]".
    iMod ("HClose" with "HP").
    iApply "HΦ".
  Qed.

  Lemma imp_deref_inv `{Encode A} η e (r : record) (Φ : A → _) :
    ↑N ⊆ E →
    inv N P -∗
    ▷ is_ref r -∗
    impure E (eval η e) Ψ ζ (λ r' : record, ⌜r' = r⌝) -∗
    ▷ (▷ P -∗ ∃ a, ▷ r ↦ #a ∗ ▷ (r ↦ #a -∗ ▷ P ∗ Φ a)) -∗
    impure E (eval η (ELoad e)) Ψ ζ Φ.
  Proof.
    iIntros (Hsubset) "#Hinv Hr He Hload".
    iApply (imp_deref_atomic (E ∖ ↑N) with "Hr He").
    iNext.
    iMod (inv_acc with "Hinv") as "[HP HClose]"; first assumption.
    iDestruct ("Hload" with "HP") as (a) "[Ha Hk]".
    iModIntro. iExists a. iFrame "Ha".
    iIntros "!> Ha".
    iDestruct ("Hk" with "Ha") as "[HP HΦ]".
    iMod ("HClose" with "HP").
    by iModIntro.
  Qed.

  (* [Atomic.compare_and_set e1 e2 e3] on a reference [r], that is, a CAS
     on the location of its field. *)
  Lemma imp_CAS_ref_inv `{PhysEqDec A} η e1 e2 e3 (r : record) (Φ2 Φ3 : A → _) (Φ : bool → _) :
    ↑N ⊆ E →
    inv N P -∗
    ▷ is_ref r -∗
    impure E (eval η e1) Ψ ζ (λ r' : record, ⌜r' = r⌝) -∗
    impure E (eval η e2) Ψ ζ Φ2 -∗
    impure E (eval η e3) Ψ ζ Φ3 -∗
    (▷ ∀ seen v',
       Φ2 seen -∗ Φ3 v' -∗
       ▷ P -∗
       ∃ v, ▷ r ↦ #v ∗
            ▷ (r ↦ (if phys_eq_val_ v seen then #v' else #v) -∗
               ▷ P ∗ Φ (phys_eq_val_ v seen))) -∗
    impure E (eval η (ECAS (EAtomicLoc e1 0) e2 e3)) Ψ ζ Φ.
  Proof.
    iIntros (Hsubset) "#Hinv >#Hr He1 He2 He3 Hcas".
    iDestruct (is_ref_field_at with "Hr") as (l) "[Hf Hls]".
    iApply (imp_CAS_inv with "Hinv [He1] He2 He3"); first assumption.
    { by iApply (imp_EAtomicLoc (Φ := λ l', ⌜l' = l⌝%I) 0 r l with "Hf He1"). }
    iIntros "!>" (l' seen v') "-> H2 H3 HP".
    iDestruct ("Hcas" with "H2 H3 HP") as (v) "[Hv Hk]".
    iExists v. iSplitL "Hv".
    { iNext. iDestruct (ref_pointsto_at r l with "Hls") as "[Hto _]".
      iDestruct ("Hto" with "Hv") as "[_ $]". }
    iIntros "!> Hl". iApply "Hk".
    iDestruct (ref_pointsto_at r l _ (if phys_eq_val_ v seen then #v' else #v)
      with "Hls") as "[_ Hfrom]".
    iApply "Hfrom". rewrite /is_ref. iDestruct "Hr" as "[$ _]". iFrame.
  Qed.

End imp_inv_rules.
