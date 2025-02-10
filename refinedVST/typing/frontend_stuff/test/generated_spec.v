From refinedc.typing Require Import typing.
From refinedc.tutorial.test Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/test.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Function [main] has been skipped. *)

  (* Specifications for function [f_temps]. *)
  Definition type_of_f_temps :=
    fn(∀ () : (); True) → ∃ n : Z, (n @ (int (tint))); ⌜n = 42⌝.
End spec.
