From refinedc.typing Require Import typing.
From refinedc.tutorial.test Require Import generated_code.
From refinedc.tutorial.test Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/test.c]. *)
Section proof_f_temps.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [f_temps]. *)
  Lemma type_f_temps :
    ⊢ typed_function impl_f_temps type_of_f_temps.
  Proof.
    Local Open Scope printing_sugar.
    start_function "f_temps" ([]) => local_b local_a.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "f_temps" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "f_temps".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "f_temps".
  Qed.
End proof_f_temps.
