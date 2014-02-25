Require Import MirrorShard.Expr MirrorShard.Env.
Require Import List.
Require Import do_computation.
Require Import types.
Require Import functions.
Require Import Prover.

Local Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Set Implicit Arguments.
Set Strict Implicit.

Section ComputationProver.
  Variable user_types : list type.
  Let all_types := (all_types_r user_types).
  Variable user_functions : list (signature all_types).
  Let functions := (our_functions user_types) ++ user_functions.
Check all_types_r.
  (* trivial summarization *)
  Definition computation_summary : Type := list (expr all_types).
  Definition computationSummarize (hyps : list (expr all_types)) : computation_summary := hyps.

  (* Completely ignore hyps; just see if we can "compute away" the goal *)
  Check do_computation_equal.
  Check our_functions.
  Definition computationProve (hyps : computation_summary)
             (goal : expr all_types) : bool :=
    do_computation_equal user_types user_functions goal.

  Definition computationLearn (sum : computation_summary) (hyps : list (expr all_types)) : computation_summary :=
    sum ++ hyps.

  Definition computationValid (uvars vars : env all_types) (sum : computation_summary) : Prop :=
    AllProvable functions uvars vars sum.

  Lemma computationValid_extensible : forall uv v sum uv' v',
                                        computationValid uv v sum -> computationValid (uv ++ uv') (v ++ v') sum.
  Proof.
    unfold computationValid. eauto using AllProvable_weaken.
  Qed.

  Lemma computationSummarizeCorrect : forall uvars vars hyps,
                                        AllProvable functions uvars vars hyps ->
                                        computationValid uvars vars (computationSummarize hyps).
  Proof.
    auto.
  Qed.

  Lemma computationLearnCorrect : forall uvars vars sum,
                                    computationValid uvars vars sum ->
                                    forall hyps, AllProvable functions uvars vars hyps ->
                                                 computationValid uvars vars (computationLearn sum hyps).
  Proof.
    unfold computationLearn, computationValid. intuition.
    apply AllProvable_app; auto.
  Qed.


  Theorem computationProverCorrect : ProverCorrect functions computationValid computationProve.
  Proof.
    apply ProverCorrect_ProverCorrect'.
    t.
    destruct goal; try (solve [inversion H0]).
    unfold computationProve in H0.
    apply do_computation_equal_correct in H0.
    inversion H0. inversion H2.
    eapply do_computation_correct in H3.
    eapply do_computation_correct in H4.
    inversion H1.
    rewrite H3 in H6. rewrite H4 in H6. inversion H6.
    reflexivity.
  Qed.

  Definition computationProver : ProverT all_types :=
    {| Facts := computation_summary
       ; Summarize := computationSummarize
       ; Learn := computationLearn
       ; Prove := computationProve
    |}.

  Definition computationProver_correct : ProverT_correct computationProver functions.
    eapply Build_ProverT_correct with (Valid := computationValid);
    eauto using computationValid_extensible, computationSummarizeCorrect, computationLearnCorrect, computationProverCorrect.
  Qed.

End ComputationProver.

Print nil_Repr.
Print Repr.
Print Default_signature.
Print signature.

Check all_types_r.
Check ProverFuncs.

Check listToRepr.
Check nil_Repr.
Check Default_signature.

Check computationProver_correct.
Check Default_signature.
SearchAbout signature.
Print functions.
Check all_types_r.
Check computationProver_correct.
Print functions.

(*Definition ComputationProver : ProverPackage :=
  {| ProverTypes := nil
     ; ProverFuncs := nil
     ; Prover_correct := nil |}.*)

Print nil_Repr.
SearchAbout Repr.
SearchAbout repr.
SearchAbout (_ -> Repr _).
SearchAbout (list (signature _)).
Check all_types_r.
Check computationProver_correct.
Check Prover_correct.
Check ProverFuncs.
SearchAbout (_ -> Repr _).
SearchAbout (_ -> signature _).

Definition herp := listToRepr (our_functions nil) (Default_signature _).
Check herp.

(* As in ILEnv.v, WordProver.v in bedrock-mirror-shard *)
Definition cp_types_r : Repr type :=
  Eval cbv beta iota zeta delta [ listToRepr ] in 
    listToRepr (all_types_r nil) EmptySet_type.

Definition cp_funcs_r types' (*: Repr (signature (repr cp_types_r (all_types_r types')))*) :=
  Eval cbv beta iota zeta delta [ listToRepr ] in 
    listToRepr (our_functions types') (Default_signature _).

Check (fun ts fs => (repr (cp_funcs_r ts) fs)).
Check (fun ts fs => our_functions ts ++ fs).

Eval vm_compute in (fun ts fs => (repr (cp_funcs_r ts) fs)).

Definition ComputationProver : ProverPackage :=
  {| ProverTypes := cp_types_r
     ; ProverFuncs := cp_funcs_r
     ; Prover_correct := computationProver_correct
  |}.
