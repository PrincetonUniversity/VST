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
Require Import mc_reify.app_lemmas.


Section tbled.

Variable tbl : SymEnv.functions RType_typ.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.


Let Expr_expr_fs := Expr_expr_fs tbl.
Existing Instance Expr_expr_fs.

Let Expr_ok_fs := Expr_ok_fs tbl.
Existing Instance Expr_ok_fs.

Let ExprVar_expr := @ExprVariables.ExprVar_expr typ func.
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

Check @APPLY_sound.
Definition x: (ExprVar (expr typ func)) := _.
Print x.

Check APPLY_sound.
(*Definition APPLY_sound := (@APPLY_sound _ (expr typ func) _ _ _ _ _ _ _ _ _ _ _ _ (fun (subst : Type)
                                 (SS : Subst subst (expr typ func))
                                 (SU : SubstUpdate subst (expr typ func))
                                 (tus tvs : tenv typ) 
                                 (n : nat) (l r : expr typ func) 
                                 (t3 : typ) (s1 : subst) =>
                               @ExprUnify_simul.exprUnify subst typ func
                                 RType_typ (func_defs.RSym_sym symexe.tbl)
                                 Typ2_tyArr SS SU
                                 (S (S (S (S (S (S (S (S (S (S O))))))))))
                                 tus tvs n l r t3 s1) _ (* (ExprLift.vars_to_uvars_exprD')*)).*)

(*Definition EAPPLY_sound := (@EAPPLY_sound _ (expr typ func) _ _ _ _ _ _ _ _ _ _ _ _ (fun (subst : Type)
                                 (SS : Subst subst (expr typ func))
                                 (SU : SubstUpdate subst (expr typ func))
                                 (tus tvs : tenv typ) 
                                 (n : nat) (l r : expr typ func) 
                                 (t3 : typ) (s1 : subst) =>
                               @ExprUnify_simul.exprUnify subst typ func
                                 RType_typ (func_defs.RSym_sym symexe.tbl)
                                 Typ2_tyArr SS SU
                                 (S (S (S (S (S (S (S (S (S (S O))))))))))
                                 tus tvs n l r t3 s1) (ExprLift.vars_to_uvars_exprD')).*)

Lemma SYMEXE_STEP_sound : rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) (SYMEXE_STEP tbl).
Admitted. (*
intros. eapply AT_GOAL_sound.
intros. destruct (get_delta_statement e);
repeat match goal with
         | |- context [ match ?X with _ => _ end ] =>
           destruct X; try apply FAIL_sound
       end.
+ unfold APPLY_SKIP.
  apply (@APPLY_sound typ (expr typ func)). 
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
      * unfold Lemma.lemmaD, set_lemma. unfold split_env.
        unfold Lemma.lemmaD'.
        Require Import MirrorCore.Util.ListMapT.
        unfold Lemma.vars, Lemma.premises, Lemma.concl.
        do 3 rewrite list_mapT_cons.
        simpl exprD'_typ0. simpl.
        unfold exprD'_typ0, ExprI.exprD'. simpl. erewrite exprD'_App_R_rw.
        2: reflexivity. 2: reflexivity.
(*        Focus 2. eapply exprD'_App_L_rw; try reflexivity.*) 
Admitted. *)

Lemma THEN'_sound : forall t1 t2, rtac_sound t1 -> rtac_sound t2 -> rtac_sound (THEN' t1 t2).
intros. unfold THEN'. apply Then.THEN_sound. auto.
apply runOnGoals_sound. auto.
Qed.

Theorem SYMEXE_sound : rtac_sound (SYMEXE_TAC tbl).
unfold SYMEXE_TAC.
apply THEN_sound.
admit. (*jesper*)
apply REPEAT_sound.
apply SYMEXE_STEP_sound.
Qed.

End tbled.

Require Import denote_tac.


Ltac run_rtac reify term_table tac_sound :=
  match type of tac_sound with
    | forall t, @rtac_sound _ _ _ _ _ _ (?tac _) =>
	  let name := fresh "e" in
	  match goal with
	    | |- ?P => 
	      reify_aux reify term_table P name;
              let tbl := get_tbl in
	      let t := eval vm_compute in (@typeof_expr _ _ _ _ (RSym_sym tbl) nil nil name) in
	      let goal := eval unfold name in name in
	      match t with
	        | Some ?t =>
	          let goal_result := constr:(run_tac' (tac tbl) (GGoal name)) in 
	          let result := eval vm_compute in goal_result in
	          match result with
	            | More_ ?s ?g => 
	              cut (goalD_Prop nil nil g); [
	                let goal_resultV := g in
	               (* change (goalD_Prop nil nil goal_resultV -> exprD_Prop nil nil name);*)
	                exact_no_check (@run_rtac_More tbl (tac tbl) _ _ _ (tac_sound tbl)
	                	(@eq_refl (Result (CTop nil nil)) (More_ s goal_resultV) <:
	                	   run_tac' (tac tbl) (GGoal goal) = (More_ s goal_resultV)))
	                | cbv_denote
	              ]
	            | Solved ?s =>
	              exact_no_check (@run_rtac_Solved tbl (tac tbl) s name (tac_sound tbl) 
	                (@eq_refl (Result (CTop nil nil)) (Solved s) <: run_tac' (tac tbl) (GGoal goal) = Solved s))
	            | Fail => idtac "Tactic" tac "failed."
	            | _ => idtac "Error: run_rtac could not resolve the result from the tactic :" tac
	          end
	        | None => idtac "expression " goal "is ill typed" t
	      end
	  end
	| _ => idtac tac_sound "is not a soudness theorem."
  end.

Ltac rforward := run_rtac reify_vst term_table SYMEXE_sound.


Print Ltac run_rtac.
Check run_tac'.

Lemma skip_triple : forall p e,
@semax e empty_tycontext
     p
      Sskip 
     (normal_ret_assert p).
Proof. 
intros.
unfold empty_tycontext.
Time rforward.
Qed.

Fixpoint lots_of_skips n :=
match n with 
| O => Sskip
| S n' => Ssequence Sskip (lots_of_skips n')
end.

Lemma seq_triple : forall p es,
@semax es empty_tycontext p (Ssequence Sskip Sskip) (normal_ret_assert p).
Proof.
unfold empty_tycontext.
rforward.
Qed.

Lemma seq_triple_lots : forall p es,
@semax es empty_tycontext p (lots_of_skips 100) (normal_ret_assert p).
Proof.
unfold empty_tycontext.
rforward.
Qed.

Require Import reverse_defs.
Existing Instance NullExtension.Espec.

Goal
forall  (contents : list val), exists (PO : environ -> mpred), 
   (semax
     (remove_global_spec Delta) (*empty_tycontext*)
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))         
     (normal_ret_assert PO)).
intros.
unfold empty_tycontext, Delta, remove_global_spec. change PTree.tree with PTree.t.
rforward.
Qed.

Goal
forall  (contents : list val), exists PO, 
   (semax
     (remove_global_spec Delta)
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                Sskip)
     (normal_ret_assert PO)).
intros.
unfold remove_global_spec,Delta.
rforward.
Qed.

Fixpoint lots_temps' n p :=
match n with 
| O => PTree.set p (tptr t_struct_list, true) (PTree.empty _)
| S n' =>  PTree.set p (tptr t_struct_list, true) (lots_temps' n' (Psucc p))
end.

Definition lots_temps (n : nat) : PTree.t (type * bool) := lots_temps' (S n) (1%positive).

Fixpoint lots_of_sets' n p :=
match n with 
| O => (Sset p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
| S n' => Ssequence (Sset p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))) (lots_of_sets' n' (Psucc p))
end.

Definition lots_of_sets n := lots_of_sets' n 1%positive.


Goal
forall  (contents : list val), exists PO, 
   (semax
     (mk_tycontext (lots_temps 50) (PTree.empty type) Tvoid
     (PTree.empty type) (PTree.empty funspec))
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (lots_of_sets 50)
     (normal_ret_assert PO)).
intros.
unfold empty_tycontext, Delta, remove_global_spec. change PTree.tree with PTree.t.
rforward.
Qed.






