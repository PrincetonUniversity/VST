Require Import floyd.proofauto.
Require Import MirrorCore.RTac.Repeat.
Require Import MirrorCore.RTac.Then.
Require Import MirrorCore.RTac.Try.
Require Import MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Simplify.
Require Import mc_reify.symexe.
Require Import MirrorCore.RTac.RTac.
Require Import mc_reify.types.
Require Import mc_reify.funcs.
Require Import mc_reify.func_defs.
Locate THEN.


Section tbled.

Parameter tbl : SymEnv.functions RType_typ.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.


Let Expr_expr_fs := Expr_expr_fs tbl.
Existing Instance Expr_expr_fs.

Let Expr_ok_fs := Expr_ok_fs tbl.
Existing Instance Expr_ok_fs.

Let ExprVar_expr := @ExprVariables.ExprVar_expr.
Existing Instance ExprVar_expr.

Existing Instance MA.
SearchAbout MentionsAnyOk.

Instance MentionsAnyOk : MentionsAnyOk MA _ _.
Admitted.

Lemma THEN_sound : forall t1 t2,
rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) t1 -> rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) t2 -> rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) (THEN t1 t2). 
intros. unfold THEN.
unfold THEN'. 
apply THEN_sound; auto.
apply runOnGoals_sound; auto;
rtac_derive_soundness.
apply INSTANTIATE_sound.
apply runOnGoals_sound. auto.
Qed.

Definition APPLY_sound := (@APPLY_sound _ (expr typ func) _ _ _ _ _ _ _ _ _ _ _ _ (fun (subst : Type)
                                 (SS : Subst subst (expr typ func))
                                 (SU : SubstUpdate subst (expr typ func))
                                 (tus tvs : tenv typ) 
                                 (n : nat) (l r : expr typ func) 
                                 (t3 : typ) (s1 : subst) =>
                               @ExprUnify_simul.exprUnify subst typ func
                                 RType_typ (func_defs.RSym_sym symexe.tbl)
                                 Typ2_tyArr SS SU
                                 (S (S (S (S (S (S (S (S (S (S O))))))))))
                                 tus tvs n l r t3 s1) (ExprLift.vars_to_uvars_exprD')).

Definition EAPPLY_sound := (@EAPPLY_sound _ (expr typ func) _ _ _ _ _ _ _ _ _ _ _ _ (fun (subst : Type)
                                 (SS : Subst subst (expr typ func))
                                 (SU : SubstUpdate subst (expr typ func))
                                 (tus tvs : tenv typ) 
                                 (n : nat) (l r : expr typ func) 
                                 (t3 : typ) (s1 : subst) =>
                               @ExprUnify_simul.exprUnify subst typ func
                                 RType_typ (func_defs.RSym_sym symexe.tbl)
                                 Typ2_tyArr SS SU
                                 (S (S (S (S (S (S (S (S (S (S O))))))))))
                                 tus tvs n l r t3 s1) (ExprLift.vars_to_uvars_exprD')).

Lemma SYMEXE_STEP_SOUND : rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) (SYMEXE_STEP).
intros. eapply AT_GOAL_sound.
intros. destruct (get_delta_statement e);
repeat match goal with
         | |- context [ match ?X with _ => _ end ] =>
           destruct X; try apply FAIL_sound
       end.
+ unfold APPLY_SKIP.
  apply APPLY_sound. 
  admit.
  - unfold skip_lemma. 
    unfold Lemma.lemmaD. simpl. intros. 
    unfold ExprDsimul.ExprDenote.exprT_App.
    simpl.
    unfold exprT_Inj. apply semax_skip.
+ apply THEN_sound.
  - unfold APPLY_SET'.
    apply EAPPLY_sound; eauto with typeclass_instances.
      * admit.
      * Print set_lemma. unfold Lemma.lemmaD, set_lemma. unfold split_env.
        unfold Lemma.lemmaD'.
        Require Import MirrorCore.Util.ListMapT.
        unfold Lemma.vars, Lemma.premises, Lemma.concl.
        do 3 rewrite list_mapT_cons.
        simpl exprD'_typ0. simpl.
        Lemma exprD'_App_R_rw
        : forall tus tvs td t e1 e2 e1D e2D,
            typeof_expr tus tvs e2 = Some td ->
            exprD' tus tvs td e2 = Some e2D ->
            exprD' tus tvs (typ2 td t) e1 = Some e1D ->
            exprD' tus tvs t (App e1 e2) = Some (exprT_App e1D e2D).
        Proof.
          admit.
        Qed.
        unfold exprD'_typ0, ExprI.exprD'. simpl. erewrite exprD'_App_R_rw.
        2: reflexivity. 2: reflexivity.
        Lemma exprD'_App_L_rw
        : forall tus tvs td t e1 e2 e1D e2D,
            typeof_expr tus tvs e1 = Some (typ2 td t) ->
            exprD' tus tvs (typ2 td t) e1 = Some e1D ->
            exprD' tus tvs td e2 = Some e2D ->
            exprD' tus tvs t (App e1 e2) = Some (exprT_App e1D e2D).
        Proof.
          admit.
        Qed.
        Require Import get_set_reif_soundness.
        2: eapply exprD'_App_L_rw; [ reflexivity | reflexivity | eapply set_reif_eq2 ].


        Opaque Traversable.mapT HList.hlist_app Lemma.foralls.
        simpl.

        destruct ( @exprD'_typ0 typ (expr typ func) RType_typ Expr_expr_fs Prop
                 Typ0_tyProp (@nil typ)
                 (@cons typ (tyArr tyenviron tympred)
                    (@cons typ (typtree tyfunspec)
                       (@cons typ (tylist tympred)
                          (@cons typ tyOracleKind
                             (@cons typ (typtree (typrod tyc_type tyval))
                                (@cons typ (typtree tyval)
                                   (@cons typ tyval (@nil typ))))))))
                 (@App typ func
                    (@App typ func
                       (@Inj typ func
                          (@inr
                             (sum
                                (sum SymEnv.func
                                   (ModularFunc.ILogicFunc.ilfunc typ))
                                (BILogicFunc.bilfunc typ)) func'
                             (Other (feq (tyoption tyval)))))
                       (set_reif.rmsubst_eval_expr
                          (@Var typ func (S (S (S (S (S O))))))
                          (@Var typ func (S (S (S (S O))))) e0))
                    (@App typ func
                       (@Inj typ func
                          (@inr
                             (sum
                                (sum SymEnv.func
                                   (ModularFunc.ILogicFunc.ilfunc typ))
                                (BILogicFunc.bilfunc typ)) func'
                             (Other (fsome tyval))))
                       (@Var typ func (S (S (S (S (S (S O)))))))))) eqn:?. simpl.

destruct (exprD'_typ0 []
                   [tyArr tyenviron tympred; typtree tyfunspec;
                   tylist tympred; tyOracleKind;
                   typtree (typrod tyc_type tyval); 
                   typtree tyval; tyval]
                   (App
                      (App
                         (Inj (inr (Other (feq (tyArr tyenviron tympred)))))
                         (App
                            (App
                               (App (Inj (inr (Smx fassertD)))
                                  (Inj (inr (Data (..)))))
                               (App
                                  (App (Inj (inr (..)))
                                     (get_set_reif.set_reif i 
                                        (Var 6%nat) 
                                        (Var 5%nat))) 
                                  (Var 4%nat))) (Var 2%nat))) 
                      (Var 0%nat))).
  - 
        


Lemma THEN'_sound : forall t1 t2, rtac_sound t1 -> rtac_sound t2 -> rtac_sound (THEN' t1 t2).

