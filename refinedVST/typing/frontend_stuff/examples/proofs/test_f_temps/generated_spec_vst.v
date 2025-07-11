From VST.typing Require Import typing.
From VST.typing.examples.test_f_temps Require Import generated_code_vst.
Set Default Proof Using "Type".
Notation int := VST.typing.int.int.

(* Generated from [examples/test_f_temps.c]. *)
Section spec.
  Context `{!typeG OK_ty Σ} {cs : compspecs} `{!externalGS OK_ty Σ}.

  (* Function [main] has been skipped. *)

  (* Specifications for function [f_temps]. *)
  Definition type_of_f_temps :=
    fn(∀ () : (); <affine> True)
      → ∃ n : Z, (n @ (int (tint))); ⌜n = 42⌝.
End spec.
