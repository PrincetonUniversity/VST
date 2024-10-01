From VST.typing Require Import typing.
From VST.typing.examples.test_f_temps Require Import generated_code_vst_clight.
From VST.typing.examples.test_f_temps Require Import generated_spec_vst.
From VST.typing.frontend_stuff Require Import function_convertor.
Set Default Proof Using "Type".

(* Generated from [examples/test_f_temps.c]. *)
Section proof_f_temps.
   Context `{!typeG Σ} {cs : compspecs} `{!externalGS OK_ty Σ}.

  (* Typing proof for [f_temps]. *)
  Lemma type_f_temps:
    forall Espec Delta,
    ⊢ typed_function(A := ConstType _) Espec Delta (rcfun_to_clfun impl_f_temps) type_of_f_temps.
  Proof.
    Local Open Scope printing_sugar.
    unfold rcfun_to_clfun, impl_f_temps. simpl.
    
    simpl match.
    hnf.
    unfold stmt_convertor.rcstmt_to_clstmt. simpl.
    intros;
    repeat iIntros "#?";
    rewrite /typed_function.
    iIntros ( x ). (* computes the ofe_car in x *) hnf in x. destruct x.
     (* simpl. *)
    iSplit.
    { iPureIntro; simpl. repeat constructor. }

    let lsa := fresh "lsa" in
    let lsb := fresh "lsb" in
    iIntros "!#" (lsa lsb). inv_vec lsb. inv_vec lsa.

    iPureIntro.
    iIntros "(?&?&?&?)".
    cbn.
    
    repeat liRStep.

    

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
