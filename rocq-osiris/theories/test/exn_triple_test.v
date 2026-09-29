From iris Require Import gen_heap proofmode.proofmode.
From osiris Require Import osiris lang.
From osiris.program_logic Require Import ewp fun_spec.

Section test_exn_triples.
  Context `{!osirisGS Σ}.

  Definition raise_spec_untyped c : iProp Σ :=
    □ {{ True }}
    c a : Z
    {{ RET (n : Z) ; ⌜n = a⌝ | EXN (w : exn) ; ⌜w = #0%Z⌝ }}.

  Inductive myexn := Overflow | Underflow.

  Global Instance encode_myexn : Encode myexn :=
    { encode' e := match e with
                   | Overflow => VConstant "Overflow"
                   | Underflow => VConstant "Underflow"
                   end }.

  Definition raise_spec_typed c : iProp Σ :=
    □ {{ True }}
    c a : Z
    {{ RET (n : Z) ; ⌜n = a⌝ | EXN (e : myexn) ; ⌜e = Overflow⌝ }}.

  Definition raise_spec_typed_E c E Ψ : iProp Σ :=
    □ {{ ∀ (k : Z) ; ⌜k = 0⌝ }}
    c a : Z @ E <| Ψ |>
    {{ RET (n : Z) ; ⌜n = (a + k)%Z⌝ | EXN (e : myexn) ; ⌜e = Underflow⌝ }}.

End test_exn_triples.
