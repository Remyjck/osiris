(** This file is a modified version of the [protocols.v] file of the Hazel
 project, authored by Vilhena & Pottier. *)

(* protocols.v *)

(* This file introduces the notion of _protocols_. A protocol describes
   the effects that a program may perform. It does so by describing a relation
   between a value and a predicate. Intuitively, such a value corresponds to
   the _payload_ of an effect (i.e. the value [v] in [do v]) and such a
   predicate corresponds to the condition upon which the paused computation
   can be resumed. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic Require Export lib.iprop.

From osiris.lang Require Import syntax encode.
From osiris.semantics Require Import semantics.
Set Default Proof Using "Type".

(* ========================================================================== *)
(** * Protocols. *)

(* -------------------------------------------------------------------------- *)
(** Definition of the Domain of Protocols. *)

Section iEff.
Set Primitive Projections.
Record iEff Σ := IEff { iEff_car : val -d> (outcome2 val exn -d> iPropO Σ) -n> iPropO Σ }.
End iEff.
Arguments IEff {_} _.
Arguments iEff_car {_} _.

Declare Scope ieff_scope.
Delimit Scope ieff_scope with ieff.
Bind Scope ieff_scope with iEff.
Local Open Scope ieff.


(* -------------------------------------------------------------------------- *)
(** Inhabited. *)

Global Instance iEff_inhabited {Σ} : Inhabited (iEff Σ) := populate (IEff inhabitant).

(* -------------------------------------------------------------------------- *)
(** OFE Structure. *)

Section ieff_ofe.
  Context {Σ : gFunctors}.
  Global Instance iEff_equiv : Equiv (iEff Σ) := λ e1 e2,
    iEff_car e1 ≡ iEff_car e2.
  Global Instance iEff_dist : Dist (iEff Σ) := λ n e1 e2,
    iEff_car e1 ≡{n}≡ iEff_car e2.
  Lemma iEff_ofe_mixin : OfeMixin (iEff Σ).
  Proof. by apply (iso_ofe_mixin iEff_car). Qed.
  Canonical Structure iEffO := Ofe (iEff Σ) iEff_ofe_mixin.
  Global Instance iEff_cofe : Cofe iEffO.
  Proof. by apply (iso_cofe IEff iEff_car). Qed.
End ieff_ofe.


(* -------------------------------------------------------------------------- *)
(** Non-expansiveness of Projections. *)

Global Instance IEff_ne {Σ} : NonExpansive (IEff (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance IEff_proper {Σ} : Proper ((≡) ==> (≡)) (IEff (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance iEff_car_ne {Σ} : NonExpansive (iEff_car (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance iEff_car_proper {Σ} : Proper ((≡) ==> (≡)) (iEff_car (Σ:=Σ)).
Proof. by intros ???. Qed.


(* -------------------------------------------------------------------------- *)
(** Protocol-Equivalence Principles. *)

Lemma iEff_equivI' {Σ} `{Sbi SPROP} (e1 e2 : iEff Σ) :
  e1 ≡ e2 ⊣⊢@{SPROP} iEff_car e1 ≡ iEff_car e2.
Proof.
  apply (anti_symm _).
  - by apply f_equivI, iEff_car_ne.
  - destruct e1; destruct e2. simpl.
    by apply f_equivI, IEff_ne.
Qed.

Lemma iEff_equivI {Σ} `{Sbi SPROP} (e1 e2 : iEff Σ) :
  e1 ≡ e2 ⊣⊢@{SPROP} ∀ v q, iEff_car e1 v q ≡ iEff_car e2 v q.
Proof.
  trans (iEff_car e1 ≡ iEff_car e2 : SPROP)%I.
  - by apply iEff_equivI'.
  - rewrite discrete_fun_equivI. f_equiv=>v.
    by apply ofe_morO_equivI.
Qed.


(* ========================================================================== *)
(** * Notions of Protocol Monotonicity. *)

Section protocol_monotonicity.
  (* Context `{!irisGS eff_lang Σ}. *)

  (* Monotonic Protocol. *)
  Class MonoProt {Σ} (Ψ : iEff Σ) := {
    monotonic_prot v Φ Φ' :
      (∀ w, Φ w -∗ Φ' w) -∗ Ψ.(iEff_car) v Φ -∗ Ψ.(iEff_car) v Φ'
  }.

  (* Persistently Monotonic Protocol. *)
  Class PersMonoProt {Σ} (Ψ : iEff Σ) := {
    pers_monotonic_prot v Φ Φ' :
      □ (∀ v, Φ v -∗ Φ' v) -∗ Ψ.(iEff_car) v Φ -∗ Ψ.(iEff_car) v Φ'
  }.

End protocol_monotonicity.


(* ========================================================================== *)
(** * Upward Closure. *)

(* -------------------------------------------------------------------------- *)
(** Definition of the Upward Closure. *)

(* The _upward closure_ of a protocol [Ψ] is the smallest monotonic protocol
   that is greater than [Ψ] according to the _protocol ordering_ (defined in
   the remainder of this theory).

   The _persistently upward closure_ of a protocol [Ψ] is the smallest
   persistently monotonic protocol that is greater than [Ψ].

   Terminology:
   - [upcl OS Ψ]: Upward closure.
   - [upcl MS Ψ]: Persistent upward closure. *)

Program Definition upcl {Σ} (Ψ : iEff Σ) : iEff Σ :=
  IEff (λ v, λne Φ', ∃ Φ, iEff_car Ψ v Φ ∗ (∀ w, Φ w -∗ Φ' w))%I.
Next Obligation.
  repeat intro. by repeat f_equiv.
Defined.
Arguments upcl _ _%_ieff.


(* -------------------------------------------------------------------------- *)
(** Properties of the Upward Closure. *)

(* Non-expansiveness. *)
Global Instance upcl_ne {Σ} n : Proper ((dist n) ==> (dist n)) (upcl (Σ:=Σ)).
Proof. by intros ?? Hne ??; simpl; repeat (apply Hne || f_equiv). Qed.
Global Instance upcl_proper {Σ} : Proper ((≡) ==> (≡)) (upcl (Σ:=Σ)).
Proof.
  intros ????. apply equiv_dist=>n.
  apply upcl_ne; by apply equiv_dist.
Qed.

(* The upward closure is monotonic. *)
Global Instance upcl_mono_prot {Σ} (Ψ : iEff Σ) : MonoProt (upcl Ψ).
Proof.
  constructor.
  iIntros (v Φ Φ') "HΦ (% & $ & HΦ')".
  iIntros (?) "?".
  by iApply "HΦ"; iApply "HΦ'".
Qed.

(* The upward closure has no action over monotonic protocols. *)
Lemma upcl_id {Σ} (Ψ : iEff Σ) `{!MonoProt Ψ} : upcl Ψ ≡ Ψ.
Proof.
  iIntros (v Φ'). iSplit.
  - iIntros "(%Φ & HΨ & HΦ')".
    by iApply (monotonic_prot with "HΦ'").
  - iIntros "HΨ".
    iExists Φ'. iFrame. by iIntros (?) "$".
Qed.

(* ========================================================================== *)
(** * Construction of Protocols. *)

(* -------------------------------------------------------------------------- *)
(** Protocol Operators. *)

(* Bottom protocol. *)
Global Instance iEff_bottom {Σ} : Bottom (iEff Σ) := IEff (λ _, λne _, False%I).

(* Pre/post protocol.
   - Precondition is given by the pair of [v] and [P].
   - Postcondition is given by the predicate [Φ]. *)
Program Definition iEffPre_base_def {Σ}
  (v : val) (P : iProp Σ) (Φ : outcome2 val exn -d> iPropO Σ) : iEff Σ :=
  IEff (λ v', λne Φ', ⌜ v = v' ⌝ ∗ P ∗ (∀ w, Φ w -∗ Φ' w))%I.
Next Obligation. by repeat intro; simpl; repeat f_equiv. Qed.
Definition iEffPre_base_aux : seal (@iEffPre_base_def). by eexists. Qed.
Definition iEffPre_base := iEffPre_base_aux.(unseal).
Definition iEffPre_base_eq : @iEffPre_base = @iEffPre_base_def :=
  iEffPre_base_aux.(seal_eq).
Arguments iEffPre_base {_} _ _%_I _%_ieff.
Global Instance: Params (@iEffPre_base) 4 := {}.

(* Close a protocol with an existential quantifier. *)
Program Definition iEffPre_exist_def {Σ A} (e : A → iEff Σ) : iEff Σ :=
  IEff (λ v', λne q', ∃ a, iEff_car (e a) v' q')%I.
Next Obligation. solve_proper. Qed.
Definition iEffPre_exist_aux : seal (@iEffPre_exist_def). by eexists. Qed.
Definition iEffPre_exist := iEffPre_exist_aux.(unseal).
Definition iEffPre_exist_eq : @iEffPre_exist = @iEffPre_exist_def :=
  iEffPre_exist_aux.(seal_eq).
Arguments iEffPre_exist {_ _} _%_ieff.
Global Instance: Params (@iEffPre_exist) 3 := {}.

(* Iterate the existential closure. *)
Definition iEffPre_texist {Σ} {TT : tele} (e : TT → iEff Σ) : iEff Σ :=
  tele_fold (@iEffPre_exist Σ) (λ x, x) (tele_bind e).
Arguments iEffPre_texist {_ _} _%_ieff /.

(* Construct a predicate from a pair of a value [w] and an assertion [Q]. *)
Definition iEffPost_base_def {Σ} (w : outcome2 val exn) (Q : iProp Σ) :
  outcome2 val exn -d> iPropO Σ
  := (λ w', ⌜ w = w' ⌝ ∗ Q)%I.
Definition iEffPost_base_aux : seal (@iEffPost_base_def). by eexists. Qed.
Definition iEffPost_base := iEffPost_base_aux.(unseal).
Definition iEffPost_base_eq : @iEffPost_base = @iEffPost_base_def :=
  iEffPost_base_aux.(seal_eq).
Arguments iEffPost_base {_} _ _%_I.
Global Instance: Params (@iEffPost_base) 2 := {}.

(* Close a predicate with an existential quantifier. *)
Program Definition iEffPost_exist_def {Σ A}
  (e : A → outcome2 val exn -d> iPropO Σ) : outcome2 val exn -d> iPropO Σ :=
  (λ w', ∃ a, e a w')%I.
Definition iEffPost_exist_aux : seal (@iEffPost_exist_def). by eexists. Qed.
Definition iEffPost_exist := iEffPost_exist_aux.(unseal).
Definition iEffPost_exist_eq : @iEffPost_exist = @iEffPost_exist_def :=
  iEffPost_exist_aux.(seal_eq).
Arguments iEffPost_exist {_ _} _%_ieff.
Global Instance: Params (@iEffPost_exist) 2 := {}.

Definition iEffPost_texist {Σ} {TT : tele}
  (e : TT → (outcome2 val exn -d> iPropO Σ)) : outcome2 val exn -d> iPropO Σ :=
  tele_fold (@iEffPost_exist Σ) (λ x, x) (tele_bind e).
Arguments iEffPost_texist {_ _} _%_ieff /.

(* Protocol marked by a function [f]. *)
Program Definition iEff_marker_def {Σ} (f : val → val) (e : iEff Σ) : iEff Σ :=
  IEff (λ v', λne q', ∃ w', ⌜ v' = f w' ⌝ ∗ iEff_car e w' q')%I.
Next Obligation. solve_proper. Qed.
Definition iEff_marker_aux : seal (@iEff_marker_def). by eexists. Qed.
Definition iEff_marker := iEff_marker_aux.(unseal).
Definition iEff_marker_eq : @iEff_marker = @iEff_marker_def :=
  iEff_marker_aux.(seal_eq).
Arguments iEff_marker {_} _ _%_ieff.
Global Instance: Params (@iEff_marker) 3 := {}.

(* Extend a given protocol with the constraint
   that the sent values satisfy [P]. *)
Program Definition iEff_filter_def {Σ} (P : val → Prop) (e : iEff Σ) : iEff Σ :=
  IEff (λ v', λne q', ⌜ P v' ⌝ ∗ iEff_car e v' q')%I.
Next Obligation. solve_proper. Qed.
Definition iEff_filter_aux : seal (@iEff_filter_def). by eexists. Qed.
Definition iEff_filter := iEff_filter_aux.(unseal).
Definition iEff_filter_eq : @iEff_filter = @iEff_filter_def :=
  iEff_filter_aux.(seal_eq).
Arguments iEff_filter {_} _ _%_ieff.
Global Instance: Params (@iEff_marker) 3 := {}.

(* Protocol sum. *)
Program Definition iEff_sum_def {Σ} (e1 e2 : iEff Σ) : iEff Σ :=
  IEff (λ w', λne q', (iEff_car e1 w' q') ∨ (iEff_car e2 w' q'))%I.
Next Obligation. solve_proper. Qed.
Definition iEff_sum_aux : seal (@iEff_sum_def). by eexists. Qed.
Definition iEff_sum := iEff_sum_aux.(unseal).
Definition iEff_sum_eq : @iEff_sum = @iEff_sum_def :=
  iEff_sum_aux.(seal_eq).
Arguments iEff_sum {_} _%_ieff _%_ieff.
Global Instance: Params (@iEff_sum) 3 := {}.


(* -------------------------------------------------------------------------- *)
(** Notation. *)

(* Notation for send/recv protocols. *)

Notation "'!' v {{ P } } ; Q" := (iEffPre_base v P Q)
  (at level 200, v at level 20, right associativity,
     format "'!' v {{  P  } } ; Q") : ieff_scope.

Notation "'?' w {{ Q } }" := (iEffPost_base w Q)
  (at level 200, w at level 20, right associativity,
   format "'?' w  {{  Q  } }") : ieff_scope.

Notation ">> x .. y >> e" :=
  (iEffPre_exist (λ x, .. (iEffPre_exist (λ y, e)) .. )%ieff)
  (at level 200, x binder, y binder, right associativity,
   format ">>  x  ..  y >>  e") : ieff_scope.

Notation "<< x .. y << e" :=
  (iEffPost_exist (λ x, .. (iEffPost_exist (λ y, e)) .. )%ieff)
  (at level 200, x binder, y binder, right associativity,
   format "<<  x  ..  y <<  e") : ieff_scope.

Notation "'>>..' x .. y >> e" :=
  (iEffPre_texist (λ x, .. (iEffPre_texist (λ y, e)) .. )%ieff)
  (at level 200, x binder, y binder, right associativity,
   format ">>..  x  ..  y  >>  e") : ieff_scope.

Notation "'<<..' x .. y << e" :=
  (iEffPost_texist (λ x, .. (iEffPost_texist (λ y, e)) .. )%ieff)
  (at level 200, x binder, y binder, right associativity,
   format "<<..  x  ..  y <<  e") : ieff_scope.

(* Notation for protocol sum and marked protocol. *)

Notation "Ψ1 '<+>' Ψ2"  := (iEff_sum Ψ1 Ψ2)
  (at level 20, right associativity,
   format "Ψ1 <+> Ψ2") : ieff_scope.

Notation "f '#>' Ψ"  := (iEff_marker f Ψ)
  (at level 15, right associativity,
   format "f #> Ψ") : ieff_scope.

Notation "P '?>' Ψ"  := (iEff_filter P Ψ)
  (at level 15, right associativity,
   format "P ?> Ψ") : ieff_scope.

(* Test. *)
(* Check (λ Σ P Q, (>> v >> ! v {{ P }} ; << w << ? w {{ Q }} @ MS)). *)


(* -------------------------------------------------------------------------- *)
(** Unfolding Principles. *)

Lemma iEffPre_texist_eq {Σ} {TT : tele} v p (e : TT → iEff Σ) :
  iEff_car (>>.. x >> (e x))%ieff v p ⊣⊢ (∃.. x, iEff_car (e x) v p).
Proof.
  rewrite /iEffPre_texist iEffPre_exist_eq.
  induction TT as [|T TT IH]; simpl; [done|]. f_equiv=> x. by apply IH.
Qed.

Lemma iEffPost_texist_eq {Σ} {TT : tele} w (e : TT → _ -d> iPropO Σ) :
  (<<.. y << (e y))%ieff w ⊣⊢ (∃.. y, (e y) w).
Proof.
  rewrite /iEffPost_texist iEffPost_exist_eq.
  induction TT as [|T TT IH]; simpl; [done|].
  rewrite /iEffPost_exist_def. f_equiv=>x. by apply IH.
Qed.

(* This lemma allows the unfolding of the definition of a
   send/recv protocol at once; that is, the arbitrary
   number of binders are correspondingly interpreted as
   existential/universal quantifiers. *)
Lemma iEff_tele_eq {Σ} {TT1 TT2 : tele}
  (v : TT1 →       val) (P : TT1 →       iProp Σ)
  (w : TT1 → TT2 → outcome2 val exn) (Q : TT1 → TT2 → iProp Σ) v' Φ' :
    iEff_car (>>.. x >> ! (v x  ) {{ P x   }};
              <<.. y << ? (w x y) {{ Q x y }}) v' Φ'
   ⊣⊢
    (∃.. x, ⌜ v x = v' ⌝ ∗ P x ∗
       (∀.. y, Q x y -∗ Φ' (w x y)))%I.
Proof.
  rewrite iEffPre_texist_eq iEffPre_base_eq. do 2 f_equiv.
  iSplit; iIntros "(-> & HP & HΦ)"; iSplit; try done; iFrame.
  { iIntros (y) "HQ".
    iApply "HΦ". rewrite iEffPost_texist_eq.
    iExists y. rewrite iEffPost_base_eq. by iFrame. }
  { iIntros (y) "HQ". rewrite iEffPost_texist_eq iEffPost_base_eq.
    iDestruct "HQ" as (w') "(<- & HQ)". by iApply "HΦ". }
Qed.

(* -------------------------------------------------------------------------- *)
(** Properties of Protocol Operators. *)

Section protocol_operators_properties.
  Context {Σ : gFunctors}.
  Implicit Types Ψ : iEff Σ.

  (* Algebraic properties. *)

  Global Instance iEff_sum_comm : Comm (≡) (iEff_sum (Σ:=Σ)).
  Proof.
    intros e1 e2 v q. rewrite iEff_sum_eq /iEff_sum_def //=.
    iSplit; iIntros "H"; iDestruct "H" as "[H|H]".
    { by iRight. } { by iLeft. } { by iRight. } { by iLeft. }
  Qed.
  Global Instance iEff_sum_assoc : Assoc (≡) (iEff_sum (Σ:=Σ)).
  Proof.
    intros e1 e2 e3 v q. rewrite iEff_sum_eq /iEff_sum_def //=.
    iSplit; iIntros "H";
    [ iDestruct "H" as "[H|[H|H]]"
    | iDestruct "H" as "[[H|H]|H]" ].
    { by iLeft; iLeft. } { by iLeft; iRight. } { by iRight. }
    { by iLeft. } { by iRight; iLeft. } { by iRight; iRight. }
  Qed.
  Global Instance iEff_sum_left_id : LeftId (≡) (⊥) (iEff_sum (Σ:=Σ)).
  Proof.
    intros e v q. rewrite iEff_sum_eq /iEff_sum_def //=.
    iSplit; iIntros "H"; [iDestruct "H" as "[H|H]"|]; by iFrame.
  Qed.
  Global Instance iEff_sum_right_id : RightId (≡) (⊥) (iEff_sum (Σ:=Σ)).
  Proof. intros e. rewrite iEff_sum_comm. by apply iEff_sum_left_id. Qed.

  Lemma iEff_filter_bottom P : (P ?> ⊥ ≡ (⊥ : iEff Σ))%ieff.
  Proof.
    intros v q. rewrite iEff_filter_eq /iEff_filter_def //=.
    by iSplit; [iIntros "[_ H]"|].
  Qed.
  Lemma iEff_filter_true (Ψ : iEff Σ) : ((λ _, True) ?> Ψ ≡ Ψ)%ieff.
  Proof.
    intros v q. rewrite iEff_filter_eq /iEff_filter_def //=.
    iSplit; [iIntros "[_ H]"|iIntros "H"]; by auto.
  Qed.
  Lemma iEff_filter_false (Ψ : iEff Σ) : ((λ _, False) ?> Ψ ≡ (⊥ : iEff Σ))%ieff.
  Proof.
    intros v q. rewrite iEff_filter_eq /iEff_filter_def //=.
    iSplit; [iIntros "[H _]"|iIntros "H"]; by auto.
  Qed.
  Lemma iEff_filter_filter P Q (Ψ : iEff Σ) :
    (P ?> (Q ?> Ψ) ≡ (λ (v : val), P v ∧ Q v) ?> Ψ)%ieff.
  Proof.
    intros v q. rewrite iEff_filter_eq /iEff_filter_def //=.
    iSplit; [iIntros "(% & % & H)"|iIntros "[[% %] H]"]; by auto.
  Qed.
  Lemma iEff_filter_filter_l (P Q : val → Prop) (Ψ : iEff Σ) :
    (∀ v, P v → Q v) → (P ?> (Q ?> Ψ) ≡ P ?> Ψ)%ieff.
  Proof.
    intros H v q. rewrite iEff_filter_eq /iEff_filter_def //=.
    iSplit; [iIntros "(% & % & H)"|iIntros "[% H]"]; by auto.
  Qed.
  Lemma iEff_filter_filter_r (P Q : val → Prop) Ψ :
    (∀ v, Q v → P v) → (P ?> (Q ?> Ψ) ≡ Q ?> Ψ)%ieff.
  Proof.
    intros H v q. rewrite iEff_filter_eq /iEff_filter_def //=.
    iSplit; [iIntros "(% & % & H)"|iIntros "[% H]"]; by auto.
  Qed.

  Lemma iEff_filter_sum_distr P Ψ1 Ψ2 :
    ((P ?> (Ψ1 <+> Ψ2)) ≡ (P ?> Ψ1) <+> (P ?> Ψ2))%ieff.
  Proof.
    intros v q. rewrite iEff_sum_eq iEff_filter_eq /iEff_sum_def /iEff_filter_def.
    simpl. iSplit; [iIntros "[% [H|H]]"|iIntros "[[% H]|[% H]]"]; by auto.
  Qed.

  Lemma iEff_sum_filter_eq (P : val → Prop) `{!∀ v, Decision (P v)} Ψ :
    (Ψ ≡ (P ?> Ψ) <+> ((λ v, ¬ P v) ?> Ψ))%ieff.
  Proof.
    intros v q. rewrite iEff_sum_eq iEff_filter_eq /iEff_sum_def /iEff_filter_def.
    simpl. iSplit; [iIntros "H"|iIntros "[[% H]|[% H]]"]; iFrame.
    iPureIntro. case (decide (P v)); by auto.
  Qed.

  Lemma iEff_marker_bottom f : (f #> ⊥ ≡ (⊥ : iEff Σ))%ieff.
  Proof.
    intros v q. rewrite iEff_marker_eq /iEff_marker_def //=.
    iSplit; iIntros "H"; [iDestruct "H" as (w) "[_ H]"|]; done.
  Qed.

  Lemma iEff_marker_sum_distr f (Ψ1 Ψ2 : iEff Σ) :
    ((f #> (Ψ1 <+> Ψ2)) ≡ (f #> Ψ1) <+> (f #> Ψ2))%ieff.
  Proof.
    intros v q. rewrite iEff_sum_eq iEff_marker_eq /iEff_sum_def /iEff_marker_def.
    simpl. iSplit; iIntros "H".
    - iDestruct "H" as (w') "[-> [H|H]]"; by eauto.
    - iDestruct "H" as "[H|H]"; iDestruct "H" as (w') "[-> H]"; by eauto.
  Qed.

  Lemma iEff_marker_compose f g (Ψ : iEff Σ) :
    ((f #> (g #> Ψ)) ≡ ((f ∘ g) #> Ψ))%ieff.
  Proof.
    intros v q. rewrite iEff_marker_eq /iEff_marker_def.
    simpl. iSplit; iIntros "H".
    - iDestruct "H" as (u') "[-> H]"; iDestruct "H" as (w') "[-> H]"; by eauto.
    - iDestruct "H" as (w') "[-> H]"; by eauto.
  Qed.

  Lemma iEff_marker_tele {TT1 TT2 : tele} f
  (v : TT1 →       val) (P : TT1 →       iProp Σ)
  (w : TT1 → TT2 → outcome2 val exn) (Q : TT1 → TT2 → iProp Σ) :
    (f #> (>>.. x >> !    (v x  )  {{ P x }};
           <<.. y << ?    (w x y)  {{ Q x y }}))
   ≡
          (>>.. x >> ! (f (v x  )) {{ P x }};
           <<.. y << ? (  (w x y)) {{ Q x y }}).
  Proof.
    intros u' q'. iSplit; rewrite iEff_marker_eq /iEff_marker_def //=.
    { iIntros "H". iDestruct "H" as (u) "[-> H]".
      rewrite !iEffPre_texist_eq iEffPre_base_eq //=.
      iDestruct "H" as (x) "(<- & HP & Hk)". iExists x. by iFrame. }
    { iIntros "H". rewrite !iEffPre_texist_eq iEffPre_base_eq //=.
      iDestruct "H" as (u) "(<- & HP & Heq)". iExists (v u).
      iSplit; [done|]. rewrite iEffPre_texist_eq. iExists u. by iFrame. }
  Qed.
  Lemma iEff_marker_tele' (TT1 TT2 : tele) f
  (v : TT1 -t>         val) (P : TT1 -t>         iProp Σ)
  (w : TT1 -t> TT2 -t> outcome2 val exn) (Q : TT1 -t> TT2 -t> iProp Σ) :
    (f #> (>>.. x >> !           (tele_app v x)
                     {{          (tele_app P x)   }};
           <<.. y << ? (tele_app (tele_app w x) y)
                     {{ tele_app (tele_app Q x) y }}))
   ≡
          (>>.. x >> !        (f (tele_app v x))
                     {{          (tele_app P x)   }};
           <<.. y << ? (tele_app (tele_app w x) y)
                     {{ tele_app (tele_app Q x) y }}).
  Proof. by rewrite (iEff_marker_tele _ (tele_app v) (tele_app P)
                  (λ x y, tele_app (tele_app w x) y)
                  (λ x y, tele_app (tele_app Q  x) y)).
  Qed.


  Global Instance send_recv_mono_prot {TT1 TT2 : tele}
    (v' : TT1 →       val) (P : TT1 →       iProp Σ)
    (w' : TT1 → TT2 → outcome2 val exn) (Q : TT1 → TT2 → iProp Σ) :
      MonoProt (>>.. x >> ! (v' x)   {{ P x   }};
                <<.. y << ? (w' x y) {{ Q x y }}).
  Proof.
    constructor.
    iIntros (v Φ Φ') "HΦ". rewrite !iEff_tele_eq.
    iIntros "[%x [%Heq [HP HΦ']]]". iExists x.
    iFrame. iSplit; [done|]. simpl. iIntros (y) "HQ".
    iApply "HΦ". by iApply "HΦ'".
  Qed.

  (* Properties related to the upward closure. *)

  Lemma upcl_bottom v Φ : iEff_car (upcl (⊥ : iEff Σ)) v Φ ≡ False%I.
  Proof. by iSplit; [iIntros "[%Q [H _]]"|iIntros "H"]. Qed.

  Lemma upcl_tele {TT1 TT2 : tele}
    (v' : TT1 →       val) (P : TT1 →       iProp Σ)
    (w' : TT1 → TT2 → outcome2 val exn) (Q : TT1 → TT2 → iProp Σ) v Φ :
    iEff_car (upcl
      (>>.. x >> ! (v' x)   {{ P x   }};
       <<.. y << ? (w' x y) {{ Q x y }})) v Φ ≡
    (∃.. x, ⌜ v = v' x ⌝ ∗ P x ∗
      (∀.. y, Q x y -∗ Φ (w' x y)))%I.
  Proof.
    rewrite /upcl. iSplit.
    - iIntros "H". iDestruct "H" as (Q') "[HP HQ']".
      rewrite iEffPre_texist_eq iEffPre_base_eq /iEffPre_base_def.
      iDestruct "HP" as (x) "(<- & HP & HΦ)". iExists x. iFrame.
      iSplit; [done|].
      iIntros (y) "HQ".
      iApply "HQ'". iApply "HΦ".
      rewrite iEffPost_texist_eq iEffPost_base_eq /iEffPost_base_def.
      iExists y. by iFrame.
    - iIntros "H". iDestruct "H" as (x) "(-> & HP & HQ)".
      iExists (<<.. y << ? (w' x y) {{ Q x y }})%ieff.
      rewrite iEffPre_texist_eq. iSplitL "HP".
      + iExists x. rewrite iEffPre_base_eq /iEffPre_base_def //=. iFrame.
        by simpl; auto.
      + iIntros (w) "HQ'".
        rewrite iEffPost_texist_eq iEffPost_base_eq.
        iDestruct "HQ'" as (y) "[<- HQ']". by iApply "HQ".
  Qed.

  Lemma upcl_tele' (TT1 TT2 : tele)
    (v' : TT1 -t>         val) (P : TT1 -t>         iProp Σ)
    (w' : TT1 -t> TT2 -t> outcome2 val exn) (Q : TT1 -t> TT2 -t> iProp Σ) v Φ :
    iEff_car (upcl
      (>>.. x >> !           (tele_app v' x)
                 {{          (tele_app P  x)   }};
       <<.. y << ? (tele_app (tele_app w' x) y)
                 {{ tele_app (tele_app Q  x) y }})) v Φ ≡
    (∃.. x, ⌜ v = tele_app v' x ⌝ ∗ tele_app P x ∗
       (∀.. y, tele_app (tele_app Q  x) y -∗
               Φ (tele_app (tele_app w' x) y)))%I.
  Proof. by rewrite (upcl_tele (tele_app v') (tele_app P)
                    (λ x y, tele_app (tele_app w' x) y)
                    (λ x y, tele_app (tele_app Q  x) y)).
  Qed.

  Lemma upcl_marker_tele {TT1 TT2 : tele} f
    (v' : TT1 →       val) (P : TT1 →       iProp Σ)
    (w' : TT1 → TT2 → outcome2 val exn) (Q : TT1 → TT2 → iProp Σ) :
    upcl
      (f #> (>>.. x >> !    (v' x  )  {{ P x   }};
             <<.. y << ?    (w' x y)  {{ Q x y }})) ≡
    upcl
            (>>.. x >> ! (f (v' x  )) {{ P x   }};
             <<.. y << ? (  (w' x y)) {{ Q x y }}).
  Proof. by rewrite iEff_marker_tele. Qed.

  Lemma upcl_marker_intro f v Ψ Φ :
    iEff_car (upcl Ψ) v Φ ⊢ iEff_car (upcl (f #> Ψ)) (f v) Φ.
  Proof.
    rewrite /upcl iEff_marker_eq.
    iIntros "H". iDestruct "H" as (Q) "[He HQ]".
    iExists Q. iFrame. done.
  Qed.

  Lemma upcl_marker_elim f {Hf: Inj (=) (=) f} v Ψ Φ :
    iEff_car (upcl (f #> Ψ)) (f v) Φ ⊢ iEff_car (upcl Ψ) v Φ.
  Proof.
    iIntros "H". rewrite iEff_marker_eq /upcl //=.
    iDestruct "H" as (Q) "[HP HQ]".
    iDestruct "HP" as (w') "[% HP]". rewrite (Hf _ _ H).
    iExists Q. by iFrame.
  Qed.

  Lemma upcl_marker_elim' f v Ψ Φ :
    iEff_car (upcl (f #> Ψ)) v Φ ⊢ ∃ w, ⌜ v = f w ⌝ ∗ iEff_car (upcl Ψ) w Φ.
  Proof.
    iIntros "H". rewrite iEff_marker_eq /upcl //=.
    iDestruct "H" as (Q) "[HP HQ]". iDestruct "HP" as (w) "[-> HP]".
    iExists w. iSplit; [done|]. iExists Q. by iFrame.
  Qed.

  Lemma upcl_filter v P Ψ Φ :
    iEff_car (upcl (P ?> Ψ)) v Φ ⊣⊢ ⌜ P v ⌝ ∗ iEff_car (upcl Ψ) v Φ.
  Proof.
    rewrite iEff_filter_eq /upcl //=. iSplit.
    - iIntros "H". iDestruct "H" as (Q) "[[% HP] HQ]".
      iSplit; [done|]. by eauto with iFrame.
    - iIntros "[% H]". iDestruct "H" as (Q) "[HP HQ]".
      by eauto with iFrame.
  Qed.

  Lemma upcl_sum_assoc v Ψ1 Ψ2 Ψ3 Φ :
    iEff_car (upcl (Ψ1 <+> (Ψ2 <+> Ψ3))) v Φ ≡
      iEff_car (upcl ((Ψ1 <+> Ψ2) <+> Ψ3)) v Φ.
  Proof. by apply iEff_car_proper; rewrite iEff_sum_assoc. Qed.

  Lemma upcl_sum_comm v Ψ1 Ψ2 Φ :
    iEff_car (upcl (Ψ2 <+> Ψ1)) v Φ ≡ iEff_car (upcl (Ψ1 <+> Ψ2)) v Φ.
  Proof. by apply iEff_car_proper; rewrite iEff_sum_comm. Qed.

  Lemma upcl_sum_intro_l v Ψ1 Ψ2 Φ :
    iEff_car (upcl Ψ1) v Φ ⊢ iEff_car (upcl (Ψ1 <+> Ψ2)) v Φ.
  Proof.
    rewrite /upcl iEff_sum_eq.
    iIntros "H". iDestruct "H" as (Q) "[He HQ]". iExists Q. by iFrame.
  Qed.

  Lemma upcl_sum_intro_r v Ψ1 Ψ2 Φ :
    iEff_car (upcl Ψ2) v Φ ⊢ iEff_car (upcl (Ψ1 <+> Ψ2)) v Φ.
  Proof.
    iIntros "H". rewrite upcl_sum_comm.
    by iApply upcl_sum_intro_l.
  Qed.

  Lemma upcl_sum_elim v Ψ1 Ψ2 Φ :
    iEff_car (upcl (Ψ1 <+> Ψ2)) v Φ ⊢
      (iEff_car (upcl Ψ1) v Φ) ∨ (iEff_car (upcl Ψ2) v Φ).
  Proof.
    iIntros "H". iDestruct "H" as (Q) "[HP HQ]".
    rewrite iEff_sum_eq. iDestruct "HP" as "[HP|HP]".
    { iLeft;  iExists Q; by iFrame. }
    { iRight; iExists Q; by iFrame. }
  Qed.

  Lemma upcl_sum v Ψ1 Ψ2 Φ :
    iEff_car (upcl (Ψ1 <+> Ψ2)) v Φ ≡
      ((iEff_car (upcl Ψ1) v Φ) ∨ (iEff_car (upcl Ψ2) v Φ))%I.
  Proof.
    iSplit; [iApply upcl_sum_elim|].
    by iIntros "[?|?]"; [iApply upcl_sum_intro_l|iApply upcl_sum_intro_r].
  Qed.

End protocol_operators_properties.


(* ========================================================================== *)
(** * Protocol Ordering. *)

(* -------------------------------------------------------------------------- *)
(** Definition of Protocol Ordering. *)

Program Definition iEff_le {Σ} : iEffO -n> iEffO -n> iPropO Σ :=
  (λne Ψ1 Ψ2, □ (∀ v Φ, Ψ1.(iEff_car) v Φ -∗ Ψ2.(iEff_car) v Φ))%I.
Next Obligation.
  intros ??????. repeat (apply iEff_car_ne || f_equiv); done.
Defined.
Next Obligation.
  intros ??????. simpl. repeat (apply iEff_car_ne || f_equiv); done.
Defined.

Infix "⊑" := (iEff_le) (at level 70, only parsing) : ieff_scope.


(* -------------------------------------------------------------------------- *)
(** Properties of Protocol Ordering. *)

Section protocol_ordering_properties.
  Context {Σ : gFunctors}.
  Implicit Types Ψ : iEff Σ.

  (* Non-expansiveness. *)
  Global Instance iEff_le_ne n :
    Proper ((dist n) ==> (dist n)) (iEff_le (Σ:=Σ)).
  Proof.
    rewrite /iEff_le. intros ????.
    repeat (apply iEff_car_ne || f_equiv); done.
  Qed.
  Global Instance iEff_le_proper :  Proper ((≡) ==> (≡)) (iEff_le (Σ:=Σ)).
  Proof.
    intros ????. apply equiv_dist=>n; apply iEff_le_ne; by apply equiv_dist.
  Qed.

  (* (⊑) is a preorder. *)
  Lemma iEff_le_refl Ψ : ⊢ (Ψ ⊑ Ψ)%ieff.
  Proof. iModIntro. by iIntros (v Φ) "H". Qed.
  Lemma iEff_le_trans Ψ1 Ψ2 Ψ3 : (Ψ1 ⊑ Ψ2 -∗ Ψ2 ⊑ Ψ3 -∗ Ψ1 ⊑ Ψ3)%ieff.
  Proof.
    iIntros "#H12 #H23". iModIntro. iIntros (v Φ) "H1".
    iApply "H23". by iApply "H12".
  Qed.

  (* Bottom protocol is the bottom element of (⊑). *)
  Lemma iEff_le_bottom Ψ : ⊢ (⊥ ⊑ Ψ)%ieff.
  Proof. iModIntro. by iIntros (v Φ) "H". Qed.

  Lemma iEff_le_sum_l Ψ1 Ψ2 : ⊢ (Ψ1 ⊑ Ψ1 <+> Ψ2)%ieff.
  Proof. iModIntro. iIntros (v Φ) "H". by rewrite iEff_sum_eq //=; iLeft. Qed.
  Lemma iEff_le_sum_r Ψ1 Ψ2 : ⊢ (Ψ2 ⊑ Ψ1 <+> Ψ2)%ieff.
  Proof. rewrite (iEff_sum_comm Ψ1 Ψ2). by iApply iEff_le_sum_l. Qed.

  Lemma iEff_le_sum Ψ1 Ψ2 Ψ1' Ψ2' :
    (Ψ1 ⊑ Ψ1' -∗ Ψ2 ⊑ Ψ2' -∗ Ψ1 <+> Ψ2 ⊑ Ψ1' <+> Ψ2')%ieff.
  Proof.
    iIntros "#HΨ1 #HΨ2". iModIntro. iIntros (v Φ).
    rewrite !iEff_sum_eq //=.
    by iIntros "[Hprot|Hprot]"; [iLeft; iApply "HΨ1"| iRight; iApply "HΨ2"].
  Qed.

  Lemma iEff_le_marker f Ψ1 Ψ2 : (Ψ1 ⊑ Ψ2 -∗ (f #> Ψ1) ⊑ (f #> Ψ2))%ieff.
  Proof.
    iIntros "#HΨ". iModIntro. iIntros (v Φ).
    rewrite iEff_marker_eq //=. iIntros "[%w [-> Hprot]]".
    iExists w. iSplit; [done|]. by iApply "HΨ".
  Qed.

  Lemma iEff_le_upcl Ψ1 Ψ2 : (Ψ1 ⊑ Ψ2 -∗ (upcl Ψ1) ⊑ (upcl Ψ2))%ieff.
  Proof.
    iIntros "#Hle" (v Φ) "!# [%Φ' [HΨ1 HΦ']]".
    iExists Φ'. iSplitL "HΨ1"; [by iApply "Hle"|by iApply "HΦ'"].
  Qed.

End protocol_ordering_properties.

(* Custom unfolding setting for [iEff]; we don't want to see the concrete
   implementation on protocols. *)

(* -------------------------------------------------------------------------- *)

Definition prot {Σ} Ψ v Φ :=
  (iEff_car (Σ := Σ) (upcl Ψ) v Φ).

(** Non-expansiveness of Protocols. *)

Global Instance prot_car_ne {Σ} v P :  NonExpansive (prot (Σ:=Σ) v P).
Proof. intros ????. solve_proper. Qed.
Global Instance prot_car_proper {Σ} : Proper ((≡) ==> (≡)) (iEff_car (Σ:=Σ)).
Proof. by intros ???. Qed.

(* -------------------------------------------------------------------------- *)

(* Notation for protocols. *)

Notation "Ψ 'allows' 'perform' v << Φ >>" :=
  (prot Ψ v Φ)
    (left associativity, Φ at level 200, at level 12,
      format "'[' Ψ  'allows'  'perform'  v  '/' '<<'  '[' Φ  ']' '>>' ']'") : bi_scope.

Arguments prot : simpl never.
Arguments iEff_car : simpl never.
(* -------------------------------------------------------------------------- *)
