From iris.proofmode Require Import proofmode environments ltac_tactics.

From Ltac2 Require Import Ltac2.

(* -------------------------------------------------------------------------- *)

(** *Ltac2 bindings for Iris Proofmode tactics *)

Ltac2 iapply (lem : constr) (sel : constr option) :=
  match sel with
  | None => ltac1:(lem |- iApply lem) (Ltac1.of_constr lem)
  | Some sel =>
      ltac1:(lem sel |- iApply (lem with sel))
              (Ltac1.of_constr lem) (Ltac1.of_constr sel)
  end.

Ltac2 Notation "iApply" "(" lem(open_constr) "with" sel(constr) ")" := iapply lem (Some sel).
Ltac2 Notation "iApply" lem(open_constr) := iapply lem None.

Ltac2 iintros (pat : constr) :=
  ltac1:(pat |- iIntros pat) (Ltac1.of_constr pat).

Ltac2 Notation "iIntros" pat(constr) := iintros pat.

Ltac2 iframe (sel : constr option) :=
  match sel with
  | None => ltac1:(iFrame)
  | Some sel => ltac1:(sel |- iFrame sel) (Ltac1.of_constr sel)
  end.
Ltac2 Notation "iFrame" := iframe None.
Ltac2 Notation "iFrame" sel(constr) := iframe (Some sel).

Ltac2 iSplit () := ltac1:(iSplit).
Ltac2 Notation "iSplit" := iSplit ().

Ltac2 iSplitL (selpat : constr) := ltac1:(selpat |- iSplitL selpat) (Ltac1.of_constr selpat).
Ltac2 Notation "iSplitL" pat(constr) := iSplitL pat.

Ltac2 iSplitR (selpat : constr) := ltac1:(selpat |- iSplitR selpat) (Ltac1.of_constr selpat).
Ltac2 Notation "iSplitR" pat(constr) := iSplitR pat.

Ltac2 iDestruct (lem : constr) (pat : constr) :=
  ltac1:(lem pat |- iDestruct (lem) as pat)
    (Ltac1.of_constr lem) (Ltac1.of_constr pat).
Ltac2 Notation "iDestruct" "(" lem(constr) ")" "as" pat(constr) := iDestruct lem pat.

Ltac2 iRevert (h : constr) :=
  ltac1:(h |- iRevert h) (Ltac1.of_constr h).
Ltac2 Notation "iRevert" h(constr) := iRevert h.

Ltac2 iPureIntro () := ltac1:(iPureIntro).
Ltac2 Notation "iPureIntro" := iPureIntro ().

Ltac2 iStartProof () := ltac1:(iStartProof).
Ltac2 Notation "iStartProof" := iStartProof ().

Ltac2 iModIntro () := ltac1:(iModIntro).
Ltac2 Notation "iModIntro" := iModIntro ().

Ltac2 iAssumption () := ltac1:(iAssumption).
Ltac2 Notation "iAssumption" := iAssumption ().

Ltac2 iExact (h : constr) := ltac1:(h |- iExact h) (Ltac1.of_constr h).
Ltac2 Notation "iExact" h(constr) := iExact h.
