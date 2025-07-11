From refinedc.typing Require Import typing.
From VST.typing.examples.test_f_temps Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/test_f_temps.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Function [main] has been skipped. *)

  (* Specifications for function [f_temps]. *)
  Definition type_of_f_temps :=
    fn(∀ () : (); True) → ∃ n : Z, (n @ (int (tint))); ⌜n = 42⌝.
End spec.
