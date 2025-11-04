From VST.typing Require Import typing.
From VST.typing Require Import automation_test_loop automation_test_loop_spec.
Require Import VST.veric.make_compspecs.

Section proof_append.

Context `{!typeG OK_ty Σ} {cs : compspecs}.
    Local Open Scope printing_sugar.

    (* Instance CompSpecs : compspecs. make_compspecs prog. Defined. *)
    Lemma type_append Espec ge :
    ⊢ typed_function Espec ge f_append type_of_append.

        start_function "f_append" ([[p xs] ys]) => arg_l arg_k.
        start_function2.
        
        do 13 liRStep; liShow.
        (* FIXME need `ty_own arg_l` *)
        
        type_function_end.
    Qed.

End proof_append.