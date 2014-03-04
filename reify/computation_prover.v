Require Import MirrorShard.Expr MirrorShard.Env.
Require Import List.
Require Import do_computation.
Require Import ExtLib.Tactics. (* for forward *)
Require Import types.
Require Import functions.
Require Import Prover.

Local Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Set Implicit Arguments.
Set Strict Implicit.

Section ComputationProver.
  Variable repr_types : Repr type.
  Variable list_functions : forall ts : list type, list (signature (repr repr_types ts)).
  Check listToRepr.
  Let repr_functions := fun ts => listToRepr (list_functions ts) (Default_signature _).

  Variable all_types' : list type.
  Let all_types := repr repr_types all_types'.

  Variable all_functions' : functions all_types.
  Let all_functions := repr (repr_functions all_types') all_functions'.

  (* trivial summarization *)
  Definition computation_summary : Type := list (expr all_types).
  Definition computationSummarize (hyps : list (expr all_types)) : computation_summary := hyps.

  (* Completely ignore hyps; just see if we can "compute away" the goal *)
  Check our_functions.
  Definition computationProve (hyps : computation_summary)
             (goal : expr all_types) : bool :=
    do_computation_equal all_types (repr (repr_functions all_types') nil) goal.

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

  Lemma exprD_functions_extend_special : forall ts fs fs',
                                           (forall n v, nth_error fs n = Some v -> nth_error fs' n = Some v) ->
                                           forall us vs e t val,
                                             @exprD ts fs us vs e t = Some val ->
                                             @exprD ts fs' us vs e t = Some val.
  Proof.
    induction e; intros; auto.
    (* func case - induction on functions list *)
    simpl. simpl in H1.
    remember (nth_error fs f) as nerr_fs. symmetry in Heqnerr_fs.
    destruct nerr_fs. apply H in Heqnerr_fs.
    rewrite Heqnerr_fs.
    destruct (equiv_dec (Range s) t).
    destruct e.
    eapply applyD_impl_Forall.
    apply H1.
    apply H0.
    auto.
    inversion H1. inversion H1.

    (* not and equal *)
    simpl in *; forward.
    apply IHe1 in H1.
    apply IHe2 in H2.
    rewrite H1, H2. assumption.
    simpl in *; forward.
    apply IHe in H1. rewrite H1. assumption.
  Qed.

  Lemma repr_listToRepr_extend :
    forall T n l l2 t v, nth_error l n = Some v ->
                         nth_error (repr (@listToRepr T l t) l2 ) n = Some v.
  Proof.
    induction n.
    intros. simpl in H.
    unfold listToRepr.
    destruct l. inversion H.
    inversion H. auto.

    intros.
    simpl in H.
    unfold listToRepr.
    destruct l. inversion H.
    eapply IHn in H. eapply H.
  Qed.

  Lemma repr_listToRepr_nil :
    forall A (l : list A) n, (Env.repr (Env.listToRepr l n) nil) = l.
  Proof.
    induction l; intros; auto.
    simpl in *; rewrite IHl; auto.
  Qed.

  Theorem computationProverCorrect : ProverCorrect all_functions computationValid computationProve.
  Proof.
    apply ProverCorrect_ProverCorrect'.
    t.
    destruct goal; try (solve [inversion H0]).
    (* equal case *)
    unfold computationProve in H0.
    apply do_computation_equal_correct in H0.
    inversion H0.
    inversion H2.
    eapply do_computation_correct in H3.
    eapply do_computation_correct in H4.
    eapply exprD_functions_extend_special in H3.
    eapply exprD_functions_extend_special in H4.
    inversion H1.
    erewrite H3 in H6.
    erewrite H4 in H6.
    inversion H6.
    reflexivity.

    (* take care of the requirement that funcs can be extended appropriately *)
    intros.
    apply repr_listToRepr_extend.
    unfold repr_functions in H5.
    rewrite repr_listToRepr_nil in H5.
    apply H5.

    intros.
    apply repr_listToRepr_extend.
    unfold repr_functions in H5.
    rewrite repr_listToRepr_nil in H5.
    apply H5.
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

  (*Variable repr_types : Repr type.
  Variable list_functions : forall ts : list type, list (signature (repr repr_types ts)).*)

  Definition ComputationProver (rts : Repr type) (lfs : forall ts : list type, list (signature (repr rts ts))) : ProverPackage.
    refine ({| ProverTypes := rts
               ; ProverFuncs := fun ts => listToRepr (lfs ts) (Default_signature _)
               ; Prover := @computationProver rts lfs
               ; Prover_correct := _
            |}).
    intros.
    eapply computationProver_correct.
  Defined.
