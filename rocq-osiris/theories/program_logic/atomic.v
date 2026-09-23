From stdpp Require Import namespaces.
Require Import ewp rules.basic_rules rules.impure_rules rules.proph_rules fun_spec.
From iris.base_logic.lib Require Import proph_map.
From osiris.lang Require Import encode.
From iris.bi Require Import telescopes.
From iris.bi.lib Require Export atomic.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import proofmode classes.
(** This file declares notation for logically atomic Hoare triples, and some
generic lemmas about them. To enable the definition of a shared theory applying
to triples with any number of binders, the triples themselves are defined via telescopes, but as a user
you need not be concerned with that. You can just use the following notation:

  <<{ ∀∀ x, atomic_precondition }>>
    code @ E
  <<{ ∃∃ y, atomic_postcondition | z, RET return_value; private_postcondition }>>

Here, [x] (which can be any number of binders, including 0) is bound in all of
the atomic pre- and postcondition and the private (non-atomic) postcondition and
the return value, [y] (which can be any number of binders, including 0) is bound
in both postconditions and the return value, and [z] (which can be any number of
binders, including 0) is bound in the return value and the private
postcondition.

Note that atomic triples are *not* implicitly persistent, unlike Texan triples.
If you need a private (non-atomic) precondition, you can use a magic wand:

  private_precondition -∗
  <<{ ∀∀ x, atomic_precondition }>>
    code @ E
  <<{ ∃∃ y, atomic_postcondition
    | z, RET return_value; private_postcondition }>>

If you don't need a private postcondition, you can leave it away, e.g.:

  <<{ ∀∀ x, atomic_precondition }>>
    code @ E
  <<{ ∃∃ y, atomic_postcondition | RET return_value }>>

Note that due to combinatorial explosion and because Rocq does not have a
facility to declare such notation in a compositional way, not *all* variants of
this notation exist: if you have binders before the [RET] (which is very
uncommon), you must have a private postcondition (it can be [True]), and you
must have [∀∀] and [∃∃] binders (they can be [_: ()]).

For an example for how to prove and use logically atomic specifications, see
[iris_heap_lang/lib/increment.v].

*)

(* This warning is misleading for Hoare triple style notation where the first
terminal can also occur in the middle of a notation. *)
Local Set Warnings "-closed-notation-not-level-0".

(* This hard-codes the inner mask to be empty, because we have yet to find an
example where we want it to be anything else.

For the non-atomic post-condition, we use an [option PROP], combined with a
[-∗?]. This is to avoid introducing spurious [True -∗] into proofs that do not
need a non-atomic post-condition (which is most of them). *)
Definition atomic_ewp `{!osirisGS Σ} `{Observe A V} {TA TB TP : tele}
  (m: micro V exn) (* computation *)
  (E : coPset) (* *implementation* mask *)
  (α: TA → iProp Σ) (* atomic pre-condition *)
  (β: TA → TB → iProp Σ) (* atomic post-condition *)
  (POST: TA → TB → TP → option (iProp Σ)) (* non-atomic post-condition *)
  (f: TA → TB → TP → A) (* Turn the return data into the return value *)
  : iProp Σ :=
    ∀ (Φ : A → iProp Σ),
            (* The (outer) user mask is what is left after the implementation
            opened its things. *)
            atomic_update (⊤∖E) ∅ α β (λ.. x y, ∀.. z, POST x y z -∗? Φ (f x y z)) -∗
            EWP m {{ Φ }}.

(** We avoid '<<{'/'}>>' since those can also reasonably be infix operators
(and in fact Autosubst uses the latter). *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' z1 .. zn , 'RET' v ; POST '}>>'" :=
(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
  (atomic_ewp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleS (λ z1, .. (TeleS (λ zn, TeleO)) .. ))
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, Some POST%I) ..
                                  ) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, v%V) ..
                                  ) ..
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder, z1 binder, zn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' z1  ..  zn ,  RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* There are overall 16 of possible variants of this notation:
- with and without ∀∀ binders
- with and without ∃∃ binders
- with and without RET binders
- with and without POST

However we don't support the case where RET binders are present but anything
else is missing. Below we declare the 8 notations that involve no RET binders.
*)

(* No RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (atomic_ewp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ v%V) ..
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∃∃ binders, no RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (atomic_ewp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ tele_app $ Some POST%I
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ tele_app $ v%V
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no RET binders *)
Notation "'<<{' α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (atomic_ewp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app $ α%I)
             (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ v%V) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no ∃∃ binders, no RET binders *)
Notation "'<<{' α '}>>' e @ E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (atomic_ewp (TA:=TeleO)
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app $ α%I)
             (tele_app $ tele_app β%I)
             (tele_app $ tele_app $ tele_app $ Some POST%I)
             (tele_app $ tele_app $ tele_app $ v%V)
  )
  (at level 20, E, β, α, v, POST at level 200,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No RET binders, no POST *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (atomic_ewp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app None) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app v%V) ..
                        ) .. )
  )
  (at level 20, E, β, α, v at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∃∃ binders, no RET binders, no POST *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' β '|' 'RET' v '}>>'" :=
  (atomic_ewp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app None) .. )
             (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app v%V) .. )
  )
  (at level 20, E, β, α, v at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no RET binders, no POST *)
Notation "'<<{' α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (atomic_ewp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app α%I)
             (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app None) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app v%V) .. )
  )
  (at level 20, E, β, α, v at level 200, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no ∃∃ binders, no RET binders, no POST *)
Notation "'<<{' α '}>>' e @ E '<<{' β '|' 'RET' v '}>>'" :=
  (atomic_ewp (TA:=TeleO)
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app α%I)
             (tele_app $ tele_app β%I)
             (tele_app $ tele_app $ tele_app None)
             (tele_app $ tele_app $ tele_app v%V)
  )
  (at level 20, E, β, α, v at level 200,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(** Theory *)
Section lemmas.
  Context `{!osirisGS Σ} {TA TB TP : tele}.
  Abbreviation iProp := (iProp Σ).
  Context `{Observe A V}.
  Implicit Types (α : TA → iProp) (β : TA → TB → iProp) (POST : TA → TB → TP → option iProp) (f : TA → TB → TP → A).

  (* Atomic triples imply sequential triples. *)
  Lemma atomic_ewp_seq e E α β POST f :
    atomic_ewp e E α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ EWP e {{ Φ }}.
  Proof.
    iIntros "Hwp" (Φ x) "Hα HΦ".
    iApply (imp_frame_wand with "HΦ"). iApply "Hwp".
    iAuIntro. iAaccIntro with "Hα"; first by eauto. iIntros (y) "Hβ !>".
    (* FIXME: Using ssreflect rewrite does not work, see Rocq bug #7773. *)
    rewrite ->!tele_app_bind. iIntros (z) "Hpost HΦ". iApply ("HΦ" with "Hβ Hpost").
  Qed.

  (** This version matches the Texan triple, i.e., with a later in front of the
  [(∀.. y, β x y -∗ Φ (f x y))]. *)
  Lemma atomic_ewp_seq_step (e : micro V exn) E α β POST f :
    TCEq (is_ewp_case e) WPStep →
    atomic_ewp e E α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗ ▷ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ EWP e {{ Φ }}.
  Proof.
    iIntros (?) "H"; iIntros (Φ x) "Hα HΦ".
    iApply (imp_step_fupd (B:=exn) ⊤ ⊤ _ _ (∀.. y : TB, _)
      with "[$HΦ //]"); first done.
    iApply (atomic_ewp_seq with "H Hα").
    iIntros "%y Hβ %z Hpost HΦ". iApply ("HΦ" with "Hβ Hpost").
  Qed.

  (* Sequential triples with the empty mask for a physically atomic [e] are atomic. *)
  Lemma atomic_seq_ewp_atomic (e : micro V exn) E α β POST f
      `{!subjective_step.Atomic e}
      `{!TCEq (to_eff e) None}
      `{!TCEq (to_join e) None} :
    (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) -∗ EWP e @ ∅ {{ Φ }}) -∗
    atomic_ewp e E α β POST f.
  Proof.
    iIntros "Hwp" (Φ) "AU". iMod "AU" as (x) "[Hα [_ Hclose]]".
    iApply ("Hwp" with "Hα"). iIntros "%y Hβ %z Hpost".
    iMod ("Hclose" with "Hβ") as "HΦ".
    rewrite ->!tele_app_bind. iApply "HΦ". done.
  Qed.

  (** Sequential triples with a persistent precondition and no initial quantifier
  are atomic. *)
  Lemma persistent_seq_ewp_atomic (e : micro V exn) E
      (α : [tele] → iProp) (β : [tele] → TB → iProp)
      (POST : [tele] → TB → TP → option iProp) (f : [tele] → TB → TP → A)
      {HP : Persistent (α [tele_arg])} :
    (∀ Φ, α [tele_arg] -∗ (∀.. y, β [tele_arg] y -∗ ∀.. z, POST [tele_arg] y z -∗? Φ (f [tele_arg] y z)) -∗ EWP e {{ Φ }}) -∗
    atomic_ewp e E α β POST f.
  Proof.
    simpl in HP. iIntros "Hwp" (Φ) "HΦ". iApply fupd_imp.
    iMod ("HΦ") as "[#Hα [Hclose _]]". iMod ("Hclose" with "Hα") as "HΦ".
    iApply imp_fupd. iApply ("Hwp" with "Hα"). iIntros "!> %y Hβ %z Hpost".
    iMod ("HΦ") as "[_ [_ Hclose]]". iMod ("Hclose" with "Hβ") as "HΦ".
    (* FIXME: Using ssreflect rewrite does not work, see Rocq bug #7773. *)
    rewrite ->!tele_app_bind. iApply "HΦ". done.
  Qed.

  Lemma atomic_update_mono Eo Ei α β (Φ1 Φ2 : TA → TB → iProp) :
    □ (∀.. x y, Φ1 x y -∗ Φ2 x y) -∗
    atomic_update Eo Ei α β Φ1 -∗
    atomic_update Eo Ei α β Φ2.
  Proof.
    iIntros "#HΦ HAU". iAuIntro.
    iApply (atomic_acc_wand with "[] [HAU]"); last by iApply aupd_aacc.
    iSplit; [by iIntros "$" | iApply "HΦ"].
  Qed.

  Lemma atomic_ewp_mask_weaken (e : micro V exn) E1 E2 α β POST f :
    E1 ⊆ E2 → atomic_ewp e E1 α β POST f -∗ atomic_ewp e E2 α β POST f.
  Proof.
    iIntros (HE) "Hwp". iIntros (Φ) "AU". iApply "Hwp".
    iApply atomic_update_mask_weaken; last done. set_solver.
  Qed.

  (** We can open invariants around atomic triples.
      (Just for demonstration purposes; we always use [iInv] in proofs.) *)
  Lemma atomic_ewp_inv (e : micro V exn) E α β POST f N I :
    ↑N ⊆ E →
    atomic_ewp e (E ∖ ↑N) (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) POST f -∗
    inv N I -∗ atomic_ewp e E α β POST f.
  Proof.
    intros ?. iIntros "Hwp #Hinv" (Φ) "AU". iApply "Hwp". iAuIntro.
    iInv N as "HI". iApply (aacc_aupd with "AU"); first solve_ndisj.
    iIntros (x) "Hα". iAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
    - (* abort *)
      iIntros "[HI $]". by eauto with iFrame.
    - (* commit *)
      iIntros (y). rewrite ->!tele_app_bind. iIntros "[HI Hβ]". iRight.
      iExists y. rewrite ->!tele_app_bind. by eauto with iFrame.
  Qed.

End lemmas.

(** Logically atomic specification triples *)

(* [ipostA] is the atomic counterpart of [ipost] (fun_spec.v): a private
   precondition [P], followed by a logically atomic triple. Like [ipost], it
   is the body of an [iSpec], so an atomic specification of a function is
   an ordinary function specification, written

     <<{ ∀ x .. y; P | ∀∀ x1 .. xn, α }>>
       c a .. b : τ1 .. τn @ E
     <<{ ∃∃ y1 .. yn, β | RET v; POST }>>

   where [x .. y] are ghost binders (as in [{{ ∀ x .. y; P }}]), [P] is the
   private precondition, and the rest reads as in [atomic_ewp]. The ghost
   binders, the [∃∃] binders and [POST] may each be omitted. Like
   [{{ P }} c a .. b : τ {{ RET v; Q }}], these triples are persistent. *)

Definition ipostA `{!osirisGS Σ} `{Observe A val} {TA TB TP : tele}
  (P : iProp Σ) (E : coPset)
  (α : TA → iProp Σ) (β : TA → TB → iProp Σ)
  (POST : TA → TB → TP → option (iProp Σ)) (f : TA → TB → TP → A)
  (m : microvx) : iProp Σ :=
  P -∗ atomic_ewp m E α β POST f.

Global Arguments ipostA {_ _ _ _ _ _ _} _ _ _ _ _ _ _ /.

Section ipostA_lemmas.
  Context `{!osirisGS Σ} {TA TB TP : tele}.
  Context `{Observe A val}.
  Implicit Types (α : TA → iProp Σ) (β : TA → TB → iProp Σ)
    (POST : TA → TB → TP → option (iProp Σ)) (f : TA → TB → TP → A).

  (* Rule of consequence: strengthen the private precondition and enlarge
     the implementation mask. Combined with [iSpec_mono_pers], it derives
     one atomic triple from another. *)

  Lemma ipostA_mono (P P' : iProp Σ) E E' α β POST f m :
    E ⊆ E' →
    ipostA P E α β POST f m -∗
    (P' -∗ P) -∗
    ipostA P' E' α β POST f m.
  Proof.
    iIntros (HE) "H HP HP'".
    iApply (atomic_ewp_mask_weaken with "(H (HP HP'))"). done.
  Qed.

End ipostA_lemmas.

(* The notations below come in 16 variants: with and without ghost binders
   [∀ x .. y;], with one or several argument types, with and without [∃∃]
   binders, with and without [POST]. The [∀∀] binders are mandatory (they
   can be [_ : ()]) and there are no binders before [RET]. *)

(* Ghost binders, one argument type. *)

Notation "'<<{' ∀ x .. y ; P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ '@' E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (□ iSpec (type_nel.Tbase τ) c
     (λ a, .. (λ b, iforall (λ x, .. (iforall (λ y,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ v%V) ..) ..)
     )) ..)) ..))%I
  (at level 20, x closed binder, y closed binder, x1 binder, xn binder,
   y1 binder, yn binder, a closed binder, b closed binder,
   τ, c at level 9, E, α, β, v, POST at level 200)
  : bi_scope.

Notation "'<<{' ∀ x .. y ; P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ '@' E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (□ iSpec (type_nel.Tbase τ) c
     (λ a, .. (λ b, iforall (λ x, .. (iforall (λ y,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app None) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app v%V) ..) ..)
     )) ..)) ..))%I
  (at level 20, x closed binder, y closed binder, x1 binder, xn binder,
   y1 binder, yn binder, a closed binder, b closed binder,
   τ, c at level 9, E, α, β, v at level 200)
  : bi_scope.

Notation "'<<{' ∀ x .. y ; P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ '@' E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (□ iSpec (type_nel.Tbase τ) c
     (λ a, .. (λ b, iforall (λ x, .. (iforall (λ y,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleO)
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ Some POST%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ v%V) ..)
     )) ..)) ..))%I
  (at level 20, x closed binder, y closed binder, x1 binder, xn binder,
   a closed binder, b closed binder,
   τ, c at level 9, E, α, β, v, POST at level 200)
  : bi_scope.

Notation "'<<{' ∀ x .. y ; P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ '@' E '<<{' β '|' 'RET' v '}>>'" :=
  (□ iSpec (type_nel.Tbase τ) c
     (λ a, .. (λ b, iforall (λ x, .. (iforall (λ y,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleO)
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app None) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app v%V) ..)
     )) ..)) ..))%I
  (at level 20, x closed binder, y closed binder, x1 binder, xn binder,
   a closed binder, b closed binder,
   τ, c at level 9, E, α, β, v at level 200)
  : bi_scope.

(* Ghost binders, several argument types. *)

Notation "'<<{' ∀ x .. y ; P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ1 .. τn τm '@' E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (□ iSpec (type_nel.Tcons τ1 (.. (type_nel.Tcons τn (type_nel.Tbase τm)) ..)) c
     (λ a, .. (λ b, iforall (λ x, .. (iforall (λ y,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ v%V) ..) ..)
     )) ..)) ..))%I
  (at level 20, x closed binder, y closed binder, x1 binder, xn binder,
   y1 binder, yn binder, a closed binder, b closed binder,
   τ1, τn, τm, c at level 9, E, α, β, v, POST at level 200)
  : bi_scope.

Notation "'<<{' ∀ x .. y ; P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ1 .. τn τm '@' E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (□ iSpec (type_nel.Tcons τ1 (.. (type_nel.Tcons τn (type_nel.Tbase τm)) ..)) c
     (λ a, .. (λ b, iforall (λ x, .. (iforall (λ y,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app None) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app v%V) ..) ..)
     )) ..)) ..))%I
  (at level 20, x closed binder, y closed binder, x1 binder, xn binder,
   y1 binder, yn binder, a closed binder, b closed binder,
   τ1, τn, τm, c at level 9, E, α, β, v at level 200)
  : bi_scope.

Notation "'<<{' ∀ x .. y ; P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ1 .. τn τm '@' E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (□ iSpec (type_nel.Tcons τ1 (.. (type_nel.Tcons τn (type_nel.Tbase τm)) ..)) c
     (λ a, .. (λ b, iforall (λ x, .. (iforall (λ y,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleO)
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ Some POST%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ v%V) ..)
     )) ..)) ..))%I
  (at level 20, x closed binder, y closed binder, x1 binder, xn binder,
   a closed binder, b closed binder,
   τ1, τn, τm, c at level 9, E, α, β, v, POST at level 200)
  : bi_scope.

Notation "'<<{' ∀ x .. y ; P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ1 .. τn τm '@' E '<<{' β '|' 'RET' v '}>>'" :=
  (□ iSpec (type_nel.Tcons τ1 (.. (type_nel.Tcons τn (type_nel.Tbase τm)) ..)) c
     (λ a, .. (λ b, iforall (λ x, .. (iforall (λ y,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleO)
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app None) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app v%V) ..)
     )) ..)) ..))%I
  (at level 20, x closed binder, y closed binder, x1 binder, xn binder,
   a closed binder, b closed binder,
   τ1, τn, τm, c at level 9, E, α, β, v at level 200)
  : bi_scope.

(* No ghost binders, one argument type. *)

Notation "'<<{' P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ '@' E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (□ iSpec (type_nel.Tbase τ) c
     (λ a, .. (λ b,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ v%V) ..) ..)
     ) ..))%I
  (at level 20, x1 binder, xn binder,
   y1 binder, yn binder, a closed binder, b closed binder,
   τ, c at level 9, E, α, β, v, POST at level 200)
  : bi_scope.

Notation "'<<{' P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ '@' E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (□ iSpec (type_nel.Tbase τ) c
     (λ a, .. (λ b,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app None) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app v%V) ..) ..)
     ) ..))%I
  (at level 20, x1 binder, xn binder,
   y1 binder, yn binder, a closed binder, b closed binder,
   τ, c at level 9, E, α, β, v at level 200)
  : bi_scope.

Notation "'<<{' P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ '@' E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (□ iSpec (type_nel.Tbase τ) c
     (λ a, .. (λ b,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleO)
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ Some POST%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ v%V) ..)
     ) ..))%I
  (at level 20, x1 binder, xn binder, a closed binder, b closed binder,
   τ, c at level 9, E, α, β, v, POST at level 200)
  : bi_scope.

Notation "'<<{' P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ '@' E '<<{' β '|' 'RET' v '}>>'" :=
  (□ iSpec (type_nel.Tbase τ) c
     (λ a, .. (λ b,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleO)
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app None) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app v%V) ..)
     ) ..))%I
  (at level 20, x1 binder, xn binder, a closed binder, b closed binder,
   τ, c at level 9, E, α, β, v at level 200)
  : bi_scope.

(* No ghost binders, several argument types. *)

Notation "'<<{' P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ1 .. τn τm '@' E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (□ iSpec (type_nel.Tcons τ1 (.. (type_nel.Tcons τn (type_nel.Tbase τm)) ..)) c
     (λ a, .. (λ b,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app $ v%V) ..) ..)
     ) ..))%I
  (at level 20, x1 binder, xn binder,
   y1 binder, yn binder, a closed binder, b closed binder,
   τ1, τn, τm, c at level 9, E, α, β, v, POST at level 200)
  : bi_scope.

Notation "'<<{' P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ1 .. τn τm '@' E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (□ iSpec (type_nel.Tcons τ1 (.. (type_nel.Tcons τn (type_nel.Tbase τm)) ..)) c
     (λ a, .. (λ b,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) ..))
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, β%I) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app None) ..) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ λ y1, .. (λ yn, tele_app v%V) ..) ..)
     ) ..))%I
  (at level 20, x1 binder, xn binder,
   y1 binder, yn binder, a closed binder, b closed binder,
   τ1, τn, τm, c at level 9, E, α, β, v at level 200)
  : bi_scope.

Notation "'<<{' P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ1 .. τn τm '@' E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (□ iSpec (type_nel.Tcons τ1 (.. (type_nel.Tcons τn (type_nel.Tbase τm)) ..)) c
     (λ a, .. (λ b,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleO)
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ Some POST%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app $ v%V) ..)
     ) ..))%I
  (at level 20, x1 binder, xn binder, a closed binder, b closed binder,
   τ1, τn, τm, c at level 9, E, α, β, v, POST at level 200)
  : bi_scope.

Notation "'<<{' P '|' ∀∀ x1 .. xn , α '}>>' c a .. b ':' τ1 .. τn τm '@' E '<<{' β '|' 'RET' v '}>>'" :=
  (□ iSpec (type_nel.Tcons τ1 (.. (type_nel.Tcons τn (type_nel.Tbase τm)) ..)) c
     (λ a, .. (λ b,
        ipostA (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) ..))
               (TB:=TeleO)
               (TP:=TeleO)
               P E
               (tele_app $ λ x1, .. (λ xn, α%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app β%I) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app None) ..)
               (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app v%V) ..)
     ) ..))%I
  (at level 20, x1 binder, xn binder, a closed binder, b closed binder,
   τ1, τn, τm, c at level 9, E, α, β, v at level 200)
  : bi_scope.

(** Prophecy resolution at a linearization point *)

(* [resolved p v w pvs] is what a caller learns once a resolution has
   fired: the prophecy's head was the pair of the value the call returned
   and the tag [v], and the rest of the prediction is [pvs']. *)

Definition resolved `{!osirisGS Σ} (p : proph_id) (v w : val)
    (pvs : list (val * val)) : iProp Σ :=
  ∃ pvs', ⌜pvs = (w, v) :: pvs'⌝ ∗ proph p pvs'.

Section proph_lemmas.
  Context `{!osirisGS Σ} {TA TB TP : tele}.
  Abbreviation iProp := (iProp Σ).
  Context `{Observe A val}.
  Implicit Types (α : TA → iProp) (β : TA → TB → iProp)
    (POST : TA → TB → TP → option iProp) (f : TA → TB → TP → A).

  (* A resolution may be attached to an operation that already satisfies a
     logically atomic triple, provided the operation is a single call. The
     triple is unchanged (same atomic pre- and postcondition, same return
     value), except that the caller additionally learns the prediction.

     The observation is emitted at the call's own step, which is the
     linearization point, so the prediction is available exactly where the
     atomic update commits. That is the point of fusing: a resolution one
     step later could be separated from the commit by another thread. *)

  Lemma atomic_ewp_resolve {Y} (c : code Y val exn) (y : Y)
      (p : proph_id) (v : val) (pvs : list (val * val)) E α β POST f :
    call_is_atomic c y →
    proph p pvs -∗
    atomic_ewp (stop c y) E α β POST f -∗
    atomic_ewp (resolve c y p v) E α β
      (λ.. a b z, Some (resolved p v (♯(f a b z)) pvs ∗ default emp (POST a b z)))
      f.
  Proof.
    iIntros (Hat) "Hproph Hwp". iIntros (Φ) "AU".
    rewrite /atomic_ewp.
    iApply (ewp_resolve with "Hproph"); first exact Hat.
    (* Run the call against a postcondition that expects the prediction, and
       weaken the client's atomic update to match: the commit now also has
       to produce [resolved], which the resolution's own equation and the
       leftover [proph] supply. *)
    iAssert (EWP stop c y {{ a : A,
        ∀ pvs', ⌜pvs = (♯a, v) :: pvs'⌝ -∗ proph p pvs' -∗
          EWP (continue inject2 (♯a : val)) {{ Φ }} }})%I with "[Hwp AU]" as "H".
    { iApply "Hwp". iApply (atomic_update_mono with "[] AU").
      iIntros "!>" (a b) "HΦ".
      rewrite ->!tele_app_bind. iIntros (z). iSpecialize ("HΦ" $! z).
      rewrite ->!tele_app_bind.
      destruct (POST a b z) as [P|] eqn:HP; simpl.
      - iIntros "HP" (pvs2) "%Heq2 Hp2".
        rewrite /continue /=. iApply imp_ret; [ encode | ].
        iApply "HΦ". iFrame "HP". iExists pvs2. by iFrame.
      - iIntros (pvs2) "%Heq2 Hp2".
        rewrite /continue /=. iApply imp_ret; [ encode | ].
        iApply "HΦ". iSplitR ""; last done. iExists pvs2. by iFrame. }
    (* [ewp_resolve] states the call's postcondition over [val]; the triple
       states it over [A]. The two agree under [♯], and the call cannot
       throw, so its exception clause weakens to anything. *)
    iApply (imp_wand_exn with "[H] []").
    - iApply (imp_wand_observe (A2:=val) with "H").
      iIntros (a) "HΦ0". iExists (♯a). by iSplit.
    - iIntros (e) "[]".
  Qed.

  Lemma atomic_ewp_resolve_return (m : micro val exn)
      (p : proph_id) (v : val) (pvs : list (val * val)) E α β POST f :
    proph p pvs -∗
    atomic_ewp m E α β POST f -∗
    atomic_ewp (bind m (λ w, resolve CReturn w p v)) E α β
      (λ.. a b z, Some (resolved p v (♯(f a b z)) pvs ∗ default emp (POST a b z)))
      f.
  Proof.
    iIntros "Hproph Hwp". iIntros (Φ) "AU".
    rewrite /atomic_ewp.
    iApply (imp_bind (A1:=A)
      (λ a, ∀ pvs', ⌜pvs = (♯a, v) :: pvs'⌝ -∗ proph p pvs' -∗
              EWP (continue inject2 (♯a : val)) {{ Φ }})%I with "[Hwp AU]").
    { iApply "Hwp". iApply (atomic_update_mono with "[] AU").
      iIntros "!>" (a b) "HΦ".
      rewrite ->!tele_app_bind. iIntros (z). iSpecialize ("HΦ" $! z).
      rewrite ->!tele_app_bind.
      destruct (POST a b z) as [P|] eqn:HP; simpl.
      - iIntros "HP" (pvs2) "%Heq2 Hp2".
        rewrite /continue /=. iApply imp_ret; [ encode | ].
        iApply "HΦ". iFrame "HP". iExists pvs2. by iFrame.
      - iIntros (pvs2) "%Heq2 Hp2".
        rewrite /continue /=. iApply imp_ret; [ encode | ].
        iApply "HΦ". iSplitR ""; last done. iExists pvs2. by iFrame. }
    iIntros (a) "HΦ0".
    iApply (ewp_resolve_return with "Hproph").
    iIntros (pvs2) "%Heq2 Hp2".
    by iApply ("HΦ0" with "[//] Hp2").
  Qed.

End proph_lemmas.
