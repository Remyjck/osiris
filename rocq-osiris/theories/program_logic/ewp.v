From iris.base_logic.lib Require Import own gen_heap ghost_map invariants saved_prop token proph_map.
From iris.base_logic Require Import ghost_map.
From iris.algebra Require Import gmap_view dfrac gset auth excl ofe.
From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import proofmode.

From osiris Require Import base.
From osiris.lang Require Import thread_ids syntax locations encode.
From osiris.semantics Require Import semantics.
Require Import subjective_step.
Require Export ghost_state block_resources field_loc.
Require Export protocols.

Definition discrete_fun2 {A B} := λ (C : A -> B → ofe), ∀ (x : A) (y : B), C x y.

Section discrete_fun2.

  Context {A B : Type} {C : A -> B -> ofe}.
  Implicit Types f g : discrete_fun2 C.

  Global Instance discrete_fun2_dist : Dist (discrete_fun2 C) :=
    λ n (f g : discrete_fun2 C), ∀ (x : A) (y : B), f x y ≡{n}≡ g x y.

  Global Instance discrete_fun2_equiv : Equiv (discrete_fun2 C) :=
    λ (f g : discrete_fun2 C), ∀ (x : A) (y : B), f x y ≡ g x y.

  Definition discrete_fun2_ofe_mixin : OfeMixin (discrete_fun2 C).
  Proof.
    split.
    - split; [ intros Hequiv n | intros Hdist ].
      + rewrite /dist /discrete_fun2_dist.
        intros x' y'. specialize (Hequiv x' y'). by rewrite Hequiv.
      + rewrite /equiv /discrete_fun2_equiv.
        intros x' y'. apply equiv_dist. intros n.
        specialize (Hdist n x' y'). apply Hdist.
    - intros n. rewrite /dist. split.
      + intros f x y. auto.
      + intros f g Hdist x y.
        symmetry.
        apply Hdist.
      + intros f g h Hdistfg Hdistgh.
        rewrite /discrete_fun2_dist in Hdistfg Hdistgh |-*.
        intros x y.
        transitivity (g x y); auto.
    - intros n m f g Hdist Hlt.
      rewrite /dist /discrete_fun2_dist. intros x y.
      eapply dist_le. apply Hdist. apply Hlt.
  Qed.

  Canonical Structure discrete_fun2O : ofe := Ofe (discrete_fun2 C) discrete_fun2_ofe_mixin.

  Program Definition discrete_fun2_chain (c : chain discrete_fun2O)
    (x : A) (y : B) : chain (C x y) := {| chain_car n := c n x y |}.
  Next Obligation. intros c x y n i ?. by apply (chain_cauchy c). Qed.

  Program Definition discrete_fun2_bchain {n} (c : bchain discrete_fun2O n)
    (x : A) (y : B) : bchain (C x y) n := {| bchain_car n Hn := c n Hn x y |}.
  Next Obligation. intros n c x y m p Hm Hp Hmp. by apply (bchain_cauchy n c). Qed.

  Global Program Instance discrete_fun2_cofe `{∀ x y, Cofe (C x y)} :
      Cofe discrete_fun2O := {
    compl c x y := compl (discrete_fun2_chain c x y);
    lbcompl n Hn c x y := lbcompl Hn (discrete_fun2_bchain c x y)
  }.
  Next Obligation.
    intros ? n c x y.
    apply (conv_compl n (discrete_fun2_chain c x y)).
  Qed.
  Next Obligation. intros ? n Hn c m Hm x y. by rewrite (conv_lbcompl _ _ Hm). Qed.
  Next Obligation.
    intros ? n Hn c1 c2 m Hc x y. apply lbcompl_ne=> ?? /=. by apply Hc.
  Qed.

  Global Instance discrete_fun2_inhabited `{∀ x y, Inhabited (C x y)} : Inhabited discrete_fun2O :=
    populate (λ _, inhabitant).

End discrete_fun2.

(* -------------------------------------------------------------------------- *)

(** The ghost state, the resources built on it, and the state interpretation
    now live in [ghost_state.v], which this file re-exports. *)

(* ========================================================================== *)

(** *Effect-aware Weakest Precondition *)

(* The type [ewp_case A E] represents computations that are handled
   differently by [ewp]:

      Either
      (1) a terminated computation with result of type (outcome2 A E),
      (2) a performed effect
      (3) a computation that must take a step
      (4) a join

   A crash falls under (3): it is never [reducible], as in Iris.
 *)

Inductive ewp_case (A E : Type) : Type :=
  WPOutcome : (outcome2 A E) → ewp_case A E
| WPPerform : C.eff -> (outcome2 val exn -> micro A E) → ewp_case A E
| WPStep : ewp_case A E
| WPJoin : thread → (outcome2 val exn → micro A E) → ewp_case A E.

Arguments ewp_case {A E}.

Arguments WPOutcome {A E}.
Arguments WPPerform {A E}.
Arguments WPStep {A E}.
Arguments WPJoin {A E}.

(* Determine which [ewp_case] a given [m] is. *)
Definition is_ewp_case {A X} (m : micro A X) : ewp_case :=
  match m with
  | Ret v => WPOutcome (O2Ret v)
  | Throw e => WPOutcome (O2Throw e)
  | Stop CPerf e k => WPPerform e k
  | Stop CJoin ι' k => WPJoin ι' k
  | _ => WPStep
  end.

Lemma subjective_step_is_WPStep {A X} σ π (m m' : micro A X) σ' μ κ :
  subjective_step (σ, m, π) κ (σ', m', μ) ->
  is_ewp_case m = WPStep.
Proof.
  intros Hwp.
  destruct_subjective_step; reflexivity.
Qed.

Lemma inv_is_ewp_case_outcome {A X} (m : micro A X) o :
  is_ewp_case m = WPOutcome o →
  m = inject2 o.
Proof. destruct m; try by inversion 1. destruct c; discriminate 1. Qed.

(* -------------------------------------------------------------------------- *)

(** *Definition of the effectful weakest precondition *)

Section ewp_def.

  Context `{!osirisGS Σ}.

  (* [ewp] takes four parameters:
     - [ι]: the identifier of the current thread
     - [E]: the mask i.e. set of names we may open.
     - [m]: the ongoing computation, an element of the [micro] monad.
     - [Ψ]: the current protocol (in the sense of Hazel)
     - [φ]: the postcondition
   *)

  Definition ewp_pre
    (ewp : ∀ {A X}, coPset -d> micro A X -d> (iEff Σ) -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :
    (∀ {A X}, coPset -d> micro A X -d> (iEff Σ) -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ) :=
    λ A X E m Ψ φ,
      (match is_ewp_case m with
       (* [EWP1]: Returned values and raised exceptions. *)
       | WPOutcome o => |={E}=> φ o
       (* [EWP2]: Effectful case
          The effect [e] satisfies protocol Ψ and the permitted replies
          satisfy the [ewp] when continued with the continuation [k]. *)
       | WPPerform e k =>
           |={E}=> Ψ allows perform e << λ o, ▷ ewp E (k o) Ψ φ >>
       (* [EWP3]: Everything else must be [reducible]. A crash never is,
          so it needs no case of its own. *)
       | WPStep =>
           ∀ σ κ κs π,
             state_interp (σ, κ ++ κs, π) ={E, ∅}=∗
             ⌜reducible m σ (dom π)⌝ ∗
             ∀ σ' m' μ,
               ⌜subjective_step (σ, m, dom π) κ (σ', m', μ)⌝ ={∅}=∗ ▷ (|={∅,E}=>
               ewp E m' Ψ φ ∗
               match μ with
               | None => state_interp (σ', κs, π)
               | Some (ι', mforked) =>
                   ∃ φ', state_interp (σ', κs, <[ι' := φ']> π) ∗
                         ewp ⊤ mforked ⊥ (λ o, □ φ' o)
               end)
       (* [EWP4]: A request to join a thread [ι']. *)
       | WPJoin ι' k =>
           ∀ σ κs π,
             state_interp (σ, κs, π) ={E, ∅}=∗
             match π !! ι' with
             | None => |={∅, E}=> ▷ False
             | Some φ' =>
                 ▷ (∀ o, □ φ' o ={∅}=∗ |={∅,E}=>
                    ewp E (k o) Ψ φ ∗ state_interp (σ, κs, π))
             end
       end)%I.

  Local Instance ewp_pre_contractive : Contractive ewp_pre.
  Proof.
    rewrite /ewp_pre /= => n ewp ewp' Hwp A X E m Ψ φ.
    f_equiv. do 2 f_equiv. intro o. f_contractive. apply Hwp.
    - repeat (f_contractive || f_equiv || apply Hwp).
    - repeat (f_contractive || f_equiv || apply Hwp).
  Qed.

  Definition ewp_def : ∀ A X, coPset -> micro A X -d> (iEff Σ) -d> (outcome2 A X -d> iPropO Σ) -d> iPropO Σ :=
    @fixpoint _ _ discrete_fun2_cofe _ ewp_pre ewp_pre_contractive.

  Local Definition ewp_aux : seal (@ewp_def). Proof. by eexists. Qed.
  Definition ewp' := ewp_aux.(unseal).

  Global Arguments ewp' {E e Ψ Φ} : rename.
  Global Arguments ewp_def {A X}.

End ewp_def.

(* -------------------------------------------------------------------------- *)

Section ewp_properties.

Context {A X P : Type}.
Context `{osirisGS Σ}.
Implicit Type Ψ : iEff Σ.
Implicit Type φ : outcome2 A X → iProp Σ.
Implicit Type a : val.
Implicit Type m : micro A X.

(* Notation wp := (wp (PROP:=iProp Σ)). *)

Lemma ewp_unfold {E} {Ψ} {φ} (m : micro A X)  :
  ewp_def E m Ψ φ ⊣⊢ ewp_pre (@ewp_def Σ _) E m Ψ φ.
Proof.
  rewrite {1}/ewp_def.
  apply (@fixpoint_unfold _ _ discrete_fun2_cofe _ ewp_pre).
Qed.

Local Ltac ewp_unfold_all :=
  rewrite !ewp_unfold /ewp_pre /=.

Global Instance ewp_ne E m n Ψ :
  Proper (pointwise_relation _ (dist n) ==> (dist n)) (ewp_def E m Ψ).
Proof.
  induction (lt_wf n) as [n _ IH] in m, Ψ |-* => Φ Ψ' HΦ.
  ewp_unfold_all.
  f_equiv. f_equiv.
  - do 8 f_equiv.
  - repeat f_equiv. intro o. f_contractive.
    apply IH; auto; intro; auto.
    eapply dist_lt; eauto.
  - do 20 (f_contractive || f_equiv).
    do 2 f_equiv.
    apply IH; eauto.
    f_equiv.
    eapply dist_lt; eauto.
  - f_equiv; intro σ. f_equiv; intro κs. f_equiv; intro π.
    f_equiv.
    destruct (π !! t) as [φ'|]; last done.
    f_equiv. f_contractive.
    f_equiv; intro o. do 4 f_equiv.
    apply IH; eauto. intros o'. eapply dist_lt; eauto.
Qed.

Global Instance ewp_proper E m Ψ:
  Proper
    (pointwise_relation _ (≡) ==> (≡))
    (ewp_def E m Ψ).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ewp_ne=>v; apply equiv_dist.
Qed.

Global Instance ewp_contractive E m Ψ n:
  TCEq (is_ewp_case m) WPStep →
  Proper
    (pointwise_relation _ (dist_later n) ==> dist n)
    (ewp_def E m Ψ).
Proof.
  intros He Φ Ψ' HΦ. ewp_unfold_all. rewrite He /=.
  repeat (f_contractive || f_equiv).
Qed.

End ewp_properties.


(* ========================================================================== *)

Definition impure {A V X} `{osirisGS Σ} `{Observe A V}
  (E : coPset) (m : micro V X) (Ψ : iEff Σ) :
  ∀ {B} `{Observe B X}, (B → iProp Σ) → (A → iProp Σ) → iProp Σ :=
  λ B _ ζ Φ, ewp_def E m Ψ (ilift (ireturns ζ) (ireturns Φ)).

(* ========================================================================== *)

(** *Notation *)

(* Bottom instance for function types, needed for the ⊥ in notations *)
Global Instance bottom_fun {Σ} {A : Type} : Bottom (A → iProp Σ) := λ _, False%I.

(* Notation for [impure] *)

(* Notations with explicit exceptional postcondition.
   The exception postcondition comes before the return postcondition
   so the parser can distinguish from the short form. *)

Notation "'EWP' e ⟨⟨ ζ ⟩⟩ {{ Φ } }" :=
  (impure ⊤ e%E ⊥ ζ%I Φ%I)
    (at level 0, e, Φ, ζ at level 200,
      format "'[' 'EWP'  e  '/' '[ '  ⟨⟨  ζ  ⟩⟩  {{  Φ  } } ']' ']'")
    : bi_scope.

Notation "'EWP' e @ E ⟨⟨ ζ ⟩⟩ {{ Φ } }" :=
  (impure E e%E ⊥ ζ%I Φ%I)
    (at level 0, e, Φ, ζ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  ⟨⟨  ζ  ⟩⟩  {{  Φ  } } ']' ']'")
    : bi_scope.

Notation "'EWP' e <| Ψ '|>' ⟨⟨ ζ ⟩⟩ {{ Φ } }" :=
  (impure ⊤ e%E Ψ%I ζ%I Φ%I)
    (at level 0, e, Ψ, Φ, ζ at level 200,
      format "'[hv' 'EWP'  e  '/' <| Ψ '|>'  ⟨⟨  ζ  ⟩⟩  {{  '[' Φ  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E <| Ψ '|>' ⟨⟨ ζ ⟩⟩ {{ Φ } }" :=
  (impure E e%E Ψ%I ζ%I Φ%I)
    (at level 0, e, Ψ, Φ, ζ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  <|  Ψ  '|>'  ⟨⟨  ζ  ⟩⟩  {{  Φ  } } ']' ']'")
    : bi_scope.

(* Notations without exceptional postcondition (uses ⊥) *)

Notation "'EWP' e {{ Φ } }" :=
  (impure ⊤ e%E ⊥ (⊥ : exn → iProp _) Φ%I)
    (at level 0, e, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' {{  Φ  } } ']' ']'")
    : bi_scope.

Notation "'EWP' e @ E {{ Φ } }" :=
  (impure E e%E ⊥ (⊥ : exn → iProp _) Φ%I)
    (at level 0, e, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  {{  Φ  } } ']' ']'")
    : bi_scope.

Notation "'EWP' e <| Ψ '|>' {{ Φ } }" :=
  (impure ⊤ e%E Ψ%I (⊥ : exn → iProp _) Φ%I)
    (at level 0, e, Ψ, Φ at level 200,
      format "'[hv' 'EWP'  e  '/' <| Ψ '|>'  {{  '[' Φ  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E <| Ψ |> {{ Φ } }" :=
  (impure E e%E Ψ%I (⊥ : exn → iProp _) Φ%I)
    (at level 0, e, Ψ, Φ at level 200,
      format "'[' 'EWP'  e  '/' '[ ' @  E  <|  Ψ  '|>'  {{  Φ  } } ']' ']'")
    : bi_scope.

(* Notations taking the postconditions as a binder and a body, the analogue of
   Iris' [WP e {{ v, Q }}]. Either postcondition may be written in either style,
   so each of the four [@ E] / [<| Ψ |>] shapes comes in four flavours.

   These come after the predicate notations above, and printing picks the most
   recently declared match, so they are the ones used for printing. As in Iris,
   that means an opaque postcondition prints eta-expanded, as [{{ v, Φ v }}].

   The general approach for the formats: an outer '[hv' to switch between
   "horizontal mode" where it all fits on one line, and "vertical mode" where
   each '/' becomes a line break; then a nested box around each postcondition so
   that it stays maximally horizontal and suitably indented. *)

(* Binder on the return postcondition, exceptional postcondition given. *)

Notation "'EWP' e ⟨⟨ ζ ⟩⟩ {{ v , Q } }" :=
  (impure ⊤ e%E ⊥ ζ%I (λ v, Q%I))
    (at level 0, e, ζ, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' ⟨⟨  ζ  ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E ⟨⟨ ζ ⟩⟩ {{ v , Q } }" :=
  (impure E e%E ⊥ ζ%I (λ v, Q%I))
    (at level 0, e, ζ, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  ⟨⟨  ζ  ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e <| Ψ '|>' ⟨⟨ ζ ⟩⟩ {{ v , Q } }" :=
  (impure ⊤ e%E Ψ%I ζ%I (λ v, Q%I))
    (at level 0, e, Ψ, ζ, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' <|  Ψ  |>  ⟨⟨  ζ  ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E <| Ψ '|>' ⟨⟨ ζ ⟩⟩ {{ v , Q } }" :=
  (impure E e%E Ψ%I ζ%I (λ v, Q%I))
    (at level 0, e, Ψ, ζ, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  <|  Ψ  |>  ⟨⟨  ζ  ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

(* Binder on the exceptional postcondition only. *)

Notation "'EWP' e ⟨⟨ w , R ⟩⟩ {{ Φ } }" :=
  (impure ⊤ e%E ⊥ (λ w, R%I) Φ%I)
    (at level 0, e, R, Φ at level 200, w at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  Φ  } } ']'")
    : bi_scope.

Notation "'EWP' e @ E ⟨⟨ w , R ⟩⟩ {{ Φ } }" :=
  (impure E e%E ⊥ (λ w, R%I) Φ%I)
    (at level 0, e, R, Φ at level 200, w at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  Φ  } } ']'")
    : bi_scope.

Notation "'EWP' e <| Ψ '|>' ⟨⟨ w , R ⟩⟩ {{ Φ } }" :=
  (impure ⊤ e%E Ψ%I (λ w, R%I) Φ%I)
    (at level 0, e, Ψ, R, Φ at level 200, w at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' <|  Ψ  |>  ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  Φ  } } ']'")
    : bi_scope.

Notation "'EWP' e @ E <| Ψ '|>' ⟨⟨ w , R ⟩⟩ {{ Φ } }" :=
  (impure E e%E Ψ%I (λ w, R%I) Φ%I)
    (at level 0, e, Ψ, R, Φ at level 200, w at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  <|  Ψ  |>  ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  Φ  } } ']'")
    : bi_scope.

(* Binders on both postconditions. *)

Notation "'EWP' e ⟨⟨ w , R ⟩⟩ {{ v , Q } }" :=
  (impure ⊤ e%E ⊥ (λ w, R%I) (λ v, Q%I))
    (at level 0, e, R, Q at level 200,
     w at level 200 as pattern, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E ⟨⟨ w , R ⟩⟩ {{ v , Q } }" :=
  (impure E e%E ⊥ (λ w, R%I) (λ v, Q%I))
    (at level 0, e, R, Q at level 200,
     w at level 200 as pattern, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e <| Ψ '|>' ⟨⟨ w , R ⟩⟩ {{ v , Q } }" :=
  (impure ⊤ e%E Ψ%I (λ w, R%I) (λ v, Q%I))
    (at level 0, e, Ψ, R, Q at level 200,
     w at level 200 as pattern, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' <|  Ψ  |>  ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E <| Ψ '|>' ⟨⟨ w , R ⟩⟩ {{ v , Q } }" :=
  (impure E e%E Ψ%I (λ w, R%I) (λ v, Q%I))
    (at level 0, e, Ψ, R, Q at level 200,
     w at level 200 as pattern, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  <|  Ψ  |>  ⟨⟨  '[' w ,  '/' R  ']' ⟩⟩  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

(* Binder on the return postcondition, no exceptional postcondition.

   These must come last: for a computation whose exceptional postcondition is
   [⊥], the notations above also match (printing [⊥] eta-expanded as
   [⟨⟨ w, ⊥ w ⟩⟩]), and printing picks the most recently declared match. *)

Notation "'EWP' e {{ v , Q } }" :=
  (impure ⊤ e%E ⊥ (⊥ : exn → iProp _) (λ v, Q%I))
    (at level 0, e, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E {{ v , Q } }" :=
  (impure E e%E ⊥ (⊥ : exn → iProp _) (λ v, Q%I))
    (at level 0, e, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e <| Ψ '|>' {{ v , Q } }" :=
  (impure ⊤ e%E Ψ%I (⊥ : exn → iProp _) (λ v, Q%I))
    (at level 0, e, Ψ, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' <|  Ψ  |>  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

Notation "'EWP' e @ E <| Ψ '|>' {{ v , Q } }" :=
  (impure E e%E Ψ%I (⊥ : exn → iProp _) (λ v, Q%I))
    (at level 0, e, Ψ, Q at level 200, v at level 200 as pattern,
      format "'[hv' 'EWP'  e  '/' @  E  <|  Ψ  |>  '/' {{  '[' v ,  '/' Q  ']' } } ']'")
    : bi_scope.

(* Both binders are parsed [as pattern], so either postcondition may destructure
   its result directly: [{{ (x, y), Q }}], [⟨⟨ (i, j), R ⟩⟩]. Write the pattern
   without a leading [']: a quoted [{{ '(x, y), Q }}] would send the parser into
   stdpp's ["' x ← y ; z"] (monadic bind) rule and fail asking for [←]. This is
   also the form Rocq prints back, so the notation round-trips. *)

(* Texan triples for [EWP] are declared in [program_logic/triples.v]. *)

(* N.B. A slight hack to control the namespace of constructs that have the same
  name in [stdpp] and [osiris]. *)
From osiris.lang Require Export syntax.
From osiris.semantics Require Export code micro step.
