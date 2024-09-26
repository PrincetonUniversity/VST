(* The VST proof would look like this *)
From VST.typing Require Import automation.
From (* some path, maybe start with putting the files in progs64/ *) Require Import generated_code.
From (* some path, maybe start with putting the files in progs64/ *) Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/test.c]. *)
Section proof_f_temps.
  Context `{!typeG Σ} {cs : compspecs} `{!externalGS OK_ty Σ}.

  (* Typing proof for [f_temps]. *)
  Lemma type_f_temps :
    ⊢ typed_function(A := ConstType _) Espec Delta (rc_func_to_cl_func impl_f_temps) type_of_f_temps.
  Proof.
    (* TBD *)
  Qed.
End proof_f_temps.
