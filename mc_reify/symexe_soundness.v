Require Import floyd.proofauto.
Require Import MirrorCore.RTac.Repeat.
Require Import MirrorCore.RTac.Then.
Require Import MirrorCore.RTac.Try.
Require Import MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Simplify.
Require Import mc_reify.rtac_base.
Require Import mc_reify.symexe.
Require Import MirrorCore.RTac.RTac.
Require Import mc_reify.types.
Require Import mc_reify.funcs.
Require Import mc_reify.func_defs.
Require Import mc_reify.app_lemmas.
Require Import MirrorCore.LemmaApply.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.ListMapT.

Section tbled.
Variable n : nat.
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

Definition APPLY_sound := (@APPLY_sound _ (expr typ func) _ _ _ _ _ _ _ _ _ _ _ ). 
(*Definition APPLY_sound := 
  (@APPLY_sound _ (expr typ func) _ _ _ _ _ _ _ _ _ _ _ _
 (fun (subst : Type)
                                 (SS : Subst subst (expr typ func))
                                 (SU : SubstUpdate subst (expr typ func))
                                 (tus tvs : tenv typ) 
                                 (n : nat) (l r : expr typ func) 
                                 (t3 : typ) (s1 : subst) =>
                               @ExprUnify_simul.exprUnify subst typ func
                                 RType_typ (_)
                                 Typ2_tyArr SS SU
                                 (S (S (S (S (S (S (S (S (S (S O))))))))))
                                 tus tvs n l r t3 s1) _ (ExprLift.vars_to_uvars_exprD')).*)
(*

 (fun (subst : Type)
                                 (SS : Subst subst (expr typ func))
                                 (SU : SubstUpdate subst (expr typ func))
                                 (tus tvs : tenv typ) 
                                 (n : nat) (l r : expr typ func) 
                                 (t3 : typ) (s1 : subst) =>
                               @ExprUnify_simul.exprUnify subst typ func
                                 RType_typ (_)
                                 Typ2_tyArr SS SU
                                 (S (S (S (S (S (S (S (S (S (S O))))))))))
                                 tus tvs n l r t3 s1) _ (* (ExprLift.vars_to_uvars_exprD')*)).*)

Definition EAPPLY_sound := 
  (@EAPPLY_sound _ (expr typ func) _ _ _ _ _ _ _ _ _ _). (*_ _ (fun (subst : Type)
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

Axiom set_reif_eq2 :
forall i tus tvs typ vr tr val,
exprD' tus tvs (typtree typ) tr = Some val ->
exprD' tus tvs (typtree typ) (App (App (Inj (inr (Data (fset typ i)))) vr) tr)  =
exprD' tus tvs (typtree typ) (get_set_reif.set_reif i vr tr typ).


Lemma SIMPL_DELTA_sound : rtac_sound SIMPL_DELTA.
Proof.
unfold SIMPL_DELTA.
apply SIMPLIFY_sound.
intros.
forward.
SearchAbout RedAll.beta_all.
admit.
Qed.

Lemma SYMEXE_STEP_sound : rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) (SYMEXE_STEP tbl).
(*Admitted. *)
intros.
apply Then.THEN_sound.
Focus 1. { apply INSTANTIATE_sound. } Unfocus.
apply runOnGoals_sound.
eapply AT_GOAL_sound.
intros.
destruct (get_arguments e);
repeat match goal with
         | |- context [ match ?X with _ => _ end ] =>
           destruct X; try apply FAIL_sound
       end.
+ apply THEN_sound.
  - unfold APPLY_SET'.
    apply EAPPLY_sound; eauto with typeclass_instances.
      * admit.
      * admit.
      * unfold Lemma.lemmaD, set_lemma. unfold split_env.
        unfold Lemma.lemmaD'.
        unfold Lemma.vars, Lemma.premises, Lemma.concl.
        do 3 rewrite list_mapT_cons.
        simpl exprD'_typ0. 
        unfold exprD'_typ0, ExprI.exprD', Expr_expr_fs.
        unfold func_defs.Expr_expr_fs. 
        unfold ExprD.Expr_expr. 
        simpl. 
Set Printing Depth 100. simpl.
simpl (exprD' []
               ([tyArr tyenviron tympred; typtree tyfunspec; 
                tylist tympred; tyOracleKind;
                typtree (typrod tyc_type tyval); typtree tyval; tyval] ++ 
                []) (typ0 (F:=Prop))
               (App
                  (App (Inj (inr (Other (feq tybool))))
                     (App
                        (App (Inj (inr (Smx ftc_expr_b_norho)))
                           (App (Inj (inr (Smx (ftycontext t2 t1 t0 t))))
                              (Var 1%nat))) (Inj (inr (Const (fCexpr e0))))))
                  (Inj (inr (Const (fbool true)))))).
        erewrite exprD'_App_R_rw; try reflexivity.
        Focus 2.
        erewrite exprD'_App_L_rw; try reflexivity.
        erewrite exprD'_App_R_rw; try reflexivity.
        erewrite exprD'_App_L_rw; try reflexivity.
        erewrite exprD'_App_R_rw; try reflexivity.
        erewrite exprD'_App_L_rw; try reflexivity.
        
        erewrite <- set_reif_eq2. reflexivity. reflexivity. 
        simpl. unfold exprT_App, exprT_Inj. simpl. intros.
        eapply set_reif.semax_set_localD; eauto.
  - apply TRY_sound. apply FIRST_sound. 
    repeat constructor.
      * admit (*reflexivity msusbst_sound*).
      * apply REFLEXIVITY_BOOL_sound.
      * apply REFLEXIVITYTAC_sound.
+ unfold APPLY_SEQ.
  apply THEN_sound.
  unfold APPLY_SEQ'.
  apply EAPPLY_sound; auto with typeclass_instances.
  admit. admit.
  unfold Lemma.lemmaD. unfold split_env. simpl.
  unfold exprT_App, exprT_Inj. simpl.
  intros.
  eapply semax_seq'. eauto. eauto.
  apply SIMPL_DELTA_sound.
+ unfold APPLY_SKIP.
  apply APPLY_sound. 
  admit.
  admit.
  - unfold skip_lemma. 
    unfold Lemma.lemmaD, split_env. simpl. intros. 
    unfold ExprDsimul.ExprDenote.exprT_App.
    simpl.
    unfold exprT_Inj. apply semax_skip.
Qed.

Theorem SYMEXE_sound : rtac_sound (SYMEXE_TAC_n n tbl ).
apply THEN_sound.
admit. (*jesper*)
apply REPEAT_sound.
apply SYMEXE_STEP_sound.
Qed.

End tbled.

Require Import denote_tac.

Ltac clear_tbl :=
match goal with
[ t := ?V : FMapPositive.PositiveMap.tree (SymEnv.function RType_typ) |- _ ] => clear t
end.

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
	              cut (goalD_Prop tbl nil nil g); [
	                let goal_resultV := g in
	               (* change (goalD_Prop nil nil goal_resultV -> exprD_Prop nil nil name);*)
	                exact_no_check (@run_rtac_More tbl (tac tbl) _ _ _ (tac_sound tbl)
	                	(@eq_refl (Result (CTop nil nil)) (More_ s goal_resultV) <:
	                	   run_tac' (tac tbl) (GGoal goal) = (More_ s goal_resultV)))
	                | cbv_denote; repeat (try eexists; eauto) 
	              ]
	            | Solved ?s =>
	              exact_no_check (@run_rtac_Solved tbl (tac tbl) s name (tac_sound tbl) 
	                (@eq_refl (Result (CTop nil nil)) (Solved s) <: run_tac' (tac tbl) (GGoal goal) = Solved s))
	            | Fail => idtac "Tactic" tac "failed."
	            | _ => idtac "Error: run_rtac could not resolve the result from the tactic :" tac
	          end
	        | None => idtac "expression " goal "is ill typed" t
	      end
	  end; try (clear name; clear_tbl)
	| _ => idtac tac_sound "is not a soudness theorem."
  end.

Ltac rforward := run_rtac reify_vst term_table (SYMEXE_sound 1000).

Local Open Scope logic.

Lemma skip_triple : forall sh v e,
@semax e empty_tycontext
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) 
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])
      Sskip 
     (normal_ret_assert (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) 
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])).
Proof. 
intros. 
unfold empty_tycontext.
rforward.
Qed.

Fixpoint lots_of_skips n :=
match n with 
| O => Sskip
| S n' => Ssequence Sskip (lots_of_skips n')
end.

Lemma seq_triple : forall sh v e,
@semax e empty_tycontext
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) 
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])
       (Ssequence Sskip Sskip)
     (normal_ret_assert (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) 
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])).
Proof.
intros.
unfold empty_tycontext.
rforward.
Qed.

Fixpoint MY_REPEAT 
  (n : nat) tac := 
  match n with
  | O => tac
  | S n0 => THEN tac (MY_REPEAT n0 tac)
  end.

Lemma seq_triple_lots : forall sh v e,
@semax e empty_tycontext
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) 
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])
      (lots_of_skips 100)
     (normal_ret_assert (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) 
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])).
Proof.
intros.
unfold empty_tycontext.
rforward. (* Take about 9 seconds. *)

(*
reify_expr_tac.

Time let x := (eval vm_compute in (run_tac (MY_REPEAT 2000 (SYMEXE_STEP tbl)) e0)) in idtac.

Time let x := (eval vm_compute in (run_tac (REPEAT 2000 (SYMEXE_STEP tbl)) e0)) in idtac.

(* this comparison shows that they takes almost the same amount of time. *)
*)
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

reify_expr_tac.

Fixpoint get_arguments (e : expr typ func) :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) _) Delta) Pre) CCmd) _ =>
  (get_arguments_delta Delta,
   Some Pre,
   get_arguments_statement CCmd)
| App _ e 
| Abs _ e => get_arguments e
| _ => (None, None, None)
end.

Eval vm_compute in (get_arguments e).

Goal forall n, n = (get_arguments_pre (App
            (App
               (App (Inj (inr (Smx fassertD)))
                  (Inj (inr (Data (fnil typrop)))))
               (App
                  (App (Inj (inr (Smx flocalD)))
                     (Inj (inr (Data (fempty tyval)))))
                  (Inj (inr (Data (fempty (typrod tyc_type tyval)))))))
            (Inj (inr (Data (fnil tympred)))))).
intros.
unfold get_arguments_pre.

Eval vm_compute in match get_arguments e with
         | (Some Delta, Some Pre, Some s) =>  
           Some s
         | _ => None
         end.


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

Lemma seq_more : forall p es,
@semax es empty_tycontext p (Ssequence Sskip (Sgoto _p)) (normal_ret_assert p).
Proof.
unfold empty_tycontext.
intros.
rforward. 
Abort.

