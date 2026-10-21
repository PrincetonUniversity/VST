
From VST.typing Require Import typing.
From VST.typing Require Import automation_test_expr.
Require Import VST.veric.make_compspecs.

  Section f_test1.
    Context `{!typeG OK_ty Σ} {cs : compspecs}.

    Definition spec_f_ret_expr :=
      fn(∀ x : (); emp) → ∃ z : Z, (z @ ( int tint )); ⌜z = 3⌝.
    Instance CompSpecs : compspecs. make_compspecs prog. Defined.

    Goal forall Espec ge, ⊢ typed_function Espec ge f_f_ret_expr spec_f_ret_expr.
    Proof.
      start_function "f" ( x ).
      start_function2.
      repeat liRStep.
      type_function_end.
    Qed.
  End f_test1. 

  Section f_test2.
    Context `{!typeG OK_ty Σ} {cs : compspecs}.

    Definition spec_f_temps :=
      fn(∀ x : (); emp) → ∃ z : Z, (z @ (int tint)) ; ⌜z=42⌝.

    Goal forall Espec ge, ⊢ typed_function Espec ge f_f_temps spec_f_temps.
    Proof.
      start_function "f" ( x ).
      start_function2.
      repeat liRStep.
      type_function_end.
    Qed.

  End f_test2.