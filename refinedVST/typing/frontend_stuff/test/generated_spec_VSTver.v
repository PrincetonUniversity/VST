(* The VST spec would look like this *)
From VST.typing Require Import automation.
From VST.typing Require Import automation_test.
Set Default Proof Using "Type".
From VST.typing Require Import function.
(* Generated from [tutorial/test.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Ke: don't mind this one *)
  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Function [main] has been skipped. *)

  (* Specifications for function [f_temps]. *)
  Definition type_of_f_temps :=
    fn(∀ () : (); emp) → ∃ n : Z, (n @ (int (tint))); ⌜n = 42⌝.
End spec.
