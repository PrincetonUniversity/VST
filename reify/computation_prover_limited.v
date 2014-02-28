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

  Check ProverCorrect.
  Check ProverT_correct.
  Require Import ExtLib.Tactics. (* for forward *)

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

  (* also need a proof about repr (listToRepr)
     if we have an extension, repr of listToRepr of the list
     if we apply nth_error, works like in exprD_functions_extend_special *)
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
    
    Theorem computationProverCorrect : ProverCorrect all_functions computationValid computationProve.
    Proof.
      apply ProverCorrect_ProverCorrect'.
      Opaque repr.
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
      clear H2 H0.
      unfold repr_functions in H5.
      SearchAbout listToRepr.
      unfold listToRepr in H5.
      unfold repr in H5.
      eapply repr_listToRepr_extend.
      unfold repr_functions in H5.
      unfold repr in H5.
      simpl in H5.

      simpl in H6.

      assert (do_computation_equal all_types all_functions' (Equal t goal1 goal2) = true).
      Focus 2.
      inversion H1.      
      apply do_computation_equal_correct in H5.
      inversion H5.
      inversion H6.
      
      eapply do_computation_correct in H8.
      eapply do_computation_correct in H9.

      rewrite H8 in H7.

      remember ( exprD
           (repr
              (listToRepr (list_functions all_types')
                 (Default_signature (repr repr_types all_types')))
              all_functions') uvars vars goal1 t) as hepr.
      destruct hepr.
      eapply exprD_functions_extend_special in H1.

      SearchAbout exprD.
      apply do_computation_equal_correct in H5.
      inversion H5.
      inversion H6.
      unfold do_computation in H7, H8.
      
      eapply do_computation_correct in H7.
      eapply do_computation_correct in H8.
      
      unfold do_computation in H7, H8.
      
      
      inversion H5.
      simpl. unfold do_computation. 
      Check exprD_weaken.
      destruct (is_const all_types goal1).
      rewrite -> H3.
      apply do_computation_correct.
      inversion H1.

      un

      apply

      Check do_computation_equal_correct.
      pose (do_computation_equal_correct all_types (repr (repr_functions all_types') nil) t goal1 goal2 H0).
      inversion e. inversion H2.
      

      unfold do_computation_equal in H0.
      unfold do_computation in H0.
      erewrite exprD_functions_extend_special in H0.
      inversion H0.
      apply exprD_functions_extend_special with (fs' := all_functions') in H3.
      apply do_computation_equal_correct in H0.
      inversion H0. inversion H2.
      apply do_computation_correct with (uvars := uvars) (vars := vars) in H3.
      eapply do_computation_correct with (uvars := uvars) (vars := vars) in H4.
      clear H2; clear H0.
      unfold repr_functions in H3.
      unfold do_computation_equal in H0.
      apply exprD_functions_extend_special with (fs' := all_functions') in H3.

      Check exprD_functions_extend_special.

      

      unfold exprD in H2.
    (* rewrite H3 in H6. rewrite H4 in H6. inversion H6.
    reflexivity. *)
    Admitted.

    Transparent repr.

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
Set Printing All.
Check computationProver_correct.
Print computationProve.
Print computationProve.
Definition ComputationProver (rts : Repr type) (rfs : forall ts, Repr (signature (repr rts ts))) : ProverPackage.
  refine ({| ProverTypes := rts
             ; ProverFuncs := rfs
             ; Prover := fun ts => @computationProver rts rfs ts
             ; Prover_correct := _
          |}).
  intros.
  eapply computationProver_correct.
Defined.
