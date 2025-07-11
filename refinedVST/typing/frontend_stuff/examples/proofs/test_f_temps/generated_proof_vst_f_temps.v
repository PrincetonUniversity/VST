From VST.typing Require Import typing.
From VST.typing.examples.test_f_temps Require Import generated_code_vst_clight.
From VST.typing.examples.test_f_temps Require Import generated_spec_vst.
Set Default Proof Using "Type".

(* Generated from [examples/test_f_temps.c]. *)
Section proof_f_temps.
   Context `{!typeG OK_ty Σ} {cs : compspecs}.

  (* Typing proof for [f_temps]. *)
  Lemma type_f_temps Espec ge :
    ⊢ typed_function(A := ConstType _) Espec ge f_f_temps type_of_f_temps.
  Proof.
    Local Open Scope printing_sugar.
    type_function "f_temps" ( x ).
    
    - repeat liRStep; liShow. type_function_end.
      all: print_typesystem_goal "f_temps" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "f_temps".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "f_temps".
  Qed.
End proof_f_temps.
