Require Import mc_reify.symexe.

Lemma THEN_sound : forall t1 t2 tbl,
rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) t1 -> rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) t2 -> rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) (THEN t1 t2). 
intros. unfold THEN.
unfold THEN'. 
apply THEN_sound; auto.
apply runOnGoals_sound; auto;
rtac_derive_soundness.
apply INSTANTIATE_sound.
apply runOnGoals_sound. auto.
Qed.


Lemma SYMEXE_STEP_SOUND : forall tbl, rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) (SYMEXE_STEP tbl).
intros. eapply AT_GOAL_sound.
intros. destruct (get_delta_statement e);
repeat match goal with
         | |- context [ match ?X with _ => _ end ] =>
           destruct X; try apply FAIL_sound
       end.
+ unfold APPLY_SKIP.
  generalize APPLY_sound.

; eauto with typeclass_instances.
  - apply ExprLift.vars_to_uvars_exprD'.
  - intros. 
    generalize (@exprUnify_sound subst typ func (RType_typ) _ (func_defs.RSym_sym tbl) _ _ _ _ _ _ _ 10).
    unfold ExprUnify_common.unify_sound, ExprUnify_common.unify_sound_ind, LemmaApply.unify_sound.
 admit.
  - unfold skip_lemma. 
    unfold lemmaD. simpl. intros. 
    unfold ExprDsimul.ExprDenote.exprT_App.
    simpl.
    unfold exprT_Inj. apply semax_skip.
+ apply THEN_sound.
  - unfold APPLY_SET'.
    apply EAPPLY_sound; eauto with typeclass_instances.
      * apply ExprLift.vars_to_uvars_exprD'.
      * admit.
      * admit. (*red. simpl.
        unfold lemmaD'. simpl.
        unfold exprD'_typ0. simpl. unfold ExprDsimul.ExprDenote.exprD'.
        simpl. simpl. *)
  - 
        


Lemma THEN'_sound : forall t1 t2, rtac_sound t1 -> rtac_sound t2 -> rtac_sound (THEN' t1 t2).

