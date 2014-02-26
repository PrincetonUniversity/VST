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
  Variable all_types : list type.
  Variable all_functions : functions all_types.

  (* trivial summarization *)
  Definition computation_summary : Type := list (expr all_types).
  Definition computationSummarize (hyps : list (expr all_types)) : computation_summary := hyps.

  (* Completely ignore hyps; just see if we can "compute away" the goal *)
Check our_functions.
  Definition computationProve (hyps : computation_summary)
             (goal : expr all_types) : bool :=
    do_computation_equal all_types (our_functions all_types) goal.

  Definition computationLearn (sum : computation_summary) (hyps : list (expr all_types)) : computation_summary :=
    sum ++ hyps.

  Definition computationValid (uvars vars : env all_types) (sum : computation_summary) : Prop :=
    AllProvable all_functions uvars vars sum.

  Lemma computationValid_extensible : forall uv v sum uv' v',
                                        computationValid uv v sum -> computationValid (uv ++ uv') (v ++ v') sum.
  Proof.
    unfold computationValid. eauto using AllProvable_weaken.
  Qed.

  Lemma computationSummarizeCorrect : forall uvars vars hyps,
                                        AllProvable all_functions uvars vars hyps ->
                                        computationValid uvars vars (computationSummarize hyps).
  Proof.
    auto.
  Qed.

  Lemma computationLearnCorrect : forall uvars vars sum,
                                    computationValid uvars vars sum ->
                                    forall hyps, AllProvable all_functions uvars vars hyps ->
                                                 computationValid uvars vars (computationLearn sum hyps).
  Proof.
    unfold computationLearn, computationValid. intuition.
    apply AllProvable_app; auto.
  Qed.

  Check ProverCorrect.
  Check ProverT_correct.

  Theorem computationProverCorrect : ProverCorrect all_functions computationValid computationProve.
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

  Definition computationProver_correct : ProverT_correct (types := all_types) computationProver all_functions.
    eapply Build_ProverT_correct with (Valid := computationValid);
    eauto using computationValid_extensible, computationSummarizeCorrect, computationLearnCorrect, computationProverCorrect.
  Qed.

End ComputationProver.
Check computationProver_correct.
Check computationProverCorrect.
Check computationProve.
Definition ComputationProver : ProverPackage :=
  {| ProverTypes := nil_Repr EmptySet_type
     ; ProverFuncs := fun ts => nil_Repr (Default_signature ts)
     ; Prover_correct := fun ts fs => computationProver_correct fs
  |}.
