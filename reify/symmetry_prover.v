Require Import List.
Require Import MirrorShard.Expr MirrorShard.Env.
Require Import Prover.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(** * The Symmetry Prover **)

Section SymmetryProver.
  Variable types : list type.
  Variable fs : functions types.

  Definition symmetry_summary : Type := list (expr types).

  Definition symmetrySummarize (hyps : list (expr types)) : symmetry_summary := hyps.


  Fixpoint symmetryProve (hyps : symmetry_summary)
    (goal : expr types) : bool :=
    match hyps with
      | nil => false
      | exp :: b => 
        match exp with 
        | Equal types l r => 
          if orb (expr_seq_dec exp goal) (expr_seq_dec (Equal types r l) goal) 
          then true
          else symmetryProve b goal
        | _ => 
          if expr_seq_dec exp goal 
          then true
          else symmetryProve b goal
        end
    end.

  Definition symmetryLearn (sum : symmetry_summary) (hyps : list (expr types)) : symmetry_summary :=
    sum ++ hyps.

  Definition symmetryValid (uvars vars : env types) (sum : symmetry_summary) : Prop :=
    AllProvable fs uvars vars sum.

  Lemma symmetryValid_extensible : forall u g f ue ge,
    symmetryValid u g f -> symmetryValid (u ++ ue) (g ++ ge) f.
  Proof.
    unfold symmetryValid. eauto using AllProvable_weaken.
  Qed.

  Lemma symmetrySummarizeCorrect : forall uvars vars hyps,
    AllProvable fs uvars vars hyps ->
    symmetryValid uvars vars (symmetrySummarize hyps).
  Proof.
    auto.
  Qed.

  Lemma symmetryLearnCorrect : forall uvars vars sum,
    symmetryValid uvars vars sum -> forall hyps, 
    AllProvable fs uvars vars hyps ->
    symmetryValid uvars vars (symmetryLearn sum hyps).
  Proof.
    unfold symmetryLearn, symmetryValid. intuition.
    apply AllProvable_app; auto.
  Qed.

  Theorem symmetryProverCorrect : ProverCorrect fs symmetryValid symmetryProve.
    apply ProverCorrect_ProverCorrect'.
    t. induction sum. 
    inversion H0.
    simpl in H. destruct H. intuition. simpl in H0.
    destruct a, goal; try solve[inversion H0];
    match type of H0 with 
    | (if ?X then _ else _) = _  => remember X as o; destruct o; symmetry in Heqo; 
                                    try apply expr_seq_dec_correct in Heqo  end; intuition;
    rewrite <- Heqo in *; unfold Provable in H;
    try solve [match goal with
    [ H : ?X = Some x |- _] => try (destruct X; try inversion H; auto; inversion H1; subst; auto) end].
    clear H0.
   rewrite Bool.orb_true_iff in Heqo. destruct Heqo. apply expr_seq_dec_correct in H0.
   rewrite <- H0 in *. remember (exprD fs uvars vars (Equal t a1 a2) tvProp); 
   destruct o; try inversion H. inversion H1; subst; auto.
   repeat (apply Bool.andb_true_iff in H0; destruct H0).
   apply expr_seq_dec_correct in H5.
   apply expr_seq_dec_correct in H4.
   apply tvar_seqb_correct in H0. subst.
   remember (exprD fs uvars vars (Equal t0 goal2 goal1) tvProp); destruct o; try inversion H; subst; auto. t.
Qed.
   

  Definition symmetryProver : ProverT types :=
  {| Facts := symmetry_summary
   ; Summarize := symmetrySummarize
   ; Learn := symmetryLearn
   ; Prove := symmetryProve
   |}.

  Definition symmetryProver_correct : ProverT_correct (types := types) symmetryProver fs.
  eapply Build_ProverT_correct with (Valid := symmetryValid);
    eauto using symmetryValid_extensible, symmetrySummarizeCorrect, symmetryLearnCorrect, symmetryProverCorrect.
  Qed.

End SymmetryProver.

Definition SymmetryProver : ProverPackage :=
{| ProverTypes := nil_Repr EmptySet_type
 ; ProverFuncs := fun ts => nil_Repr (Default_signature ts)
 ; Prover_correct := fun ts fs => symmetryProver_correct fs
|}.
