Require Import VST.floyd.proofauto.
Require Import MirrorCore.RTac.Repeat.
Require Import MirrorCore.RTac.Then.
Require Import MirrorCore.RTac.Try.
Require Import MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.RTac.RTac.
Require Import mc_reify.types.
Require Import mc_reify.funcs.
Require Import mc_reify.func_defs.
Require Import mc_reify.app_lemmas.
Require Import MirrorCore.LemmaApply.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.ListMapT.
Require Import MirrorCharge.RTac.Instantiate.
Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.Apply.
Require Import MirrorCharge.RTac.EApply.
Require Import mc_reify.rtac_base.
Require Import mc_reify.reified_ltac_lemmas.
Require Import mc_reify.hoist_later_in_pre.
Require Import mc_reify.set_load_store.
Require Import mc_reify.symexe.

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

Existing Instance rtac_base.MentionsAnyOk.

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
admit.
Qed.

Lemma replace_set_sound : forall tus tvs e,
exprD' tus tvs typrop e = exprD' tus tvs typrop (replace_set e).
intros.
destruct e; auto. simpl.
repeat
match goal with
| [ |- context [match ?e with _ => _ end] ] => destruct e; auto
end.
admit.
Admitted.
(* Qed. (* :( *) *)

Lemma SIMPL_SET_sound : rtac_sound SIMPL_SET.
Proof.
apply SIMPLIFY_sound. intros.
forward. subst.
unfold propD in *. simpl. unfold exprD'_typ0 in *. simpl. simpl in H3.
rewrite <- replace_set_sound. forward. fold func in *. inv H3.
unfold RSym_sym.
rewrite H.
intros.
eapply Pure_pctxD. eauto. intros. eauto.
Qed.

Lemma FORWARD_SET_sound: forall Delta Pre s, rtac_sound (FORWARD_SET tbl Delta Pre s).
Proof.
  intros.
  unfold FORWARD_SET.
  apply THEN_sound.
  + destruct (compute_hlip_arg (Delta, Pre, s)) as [[[[[? ?] ?] ?] ?] ?].
    apply HLIP_sound.
  + destruct (compute_set_arg (Delta, Pre, s)) as [[[[[[[? ?] ?] ?] ?] ?] ?]|]; [| apply FAIL_sound].
    apply THEN_sound.
    - eapply EAPPLY_sound; auto with typeclass_instances.
      * apply APPLY_condition1.
      * apply APPLY_condition2.
      * unfold Lemma.lemmaD, split_env. simpl. intros.
        unfold ExprDsimul.ExprDenote.exprT_App.
        simpl.
        unfold exprT_App, exprT_Inj, Rcast_val, Rcast in *. simpl in *.
        unfold BILogicFunc.typ2_cast_bin in *. simpl in *.
        eapply semax_set_localD; eauto.
    - apply TRY_sound.
      apply FIRST_sound; repeat constructor.
      * apply REFLEXIVITY_OP_CTYPE_sound.
      * admit (*reflexivity msusbst_sound*).
      * apply REFLEXIVITY_BOOL_sound.
      * apply AFTER_SET_LOAD_sound (*after_set*).
      * apply REFLEXIVITYTAC_sound.
Qed.

Lemma FORWARD_LOAD_sound: forall Struct_env Delta Pre s, rtac_sound (FORWARD_LOAD tbl Struct_env Delta Pre s).
Proof.
  intros.
  unfold FORWARD_LOAD.
  apply THEN_sound.
  + destruct (compute_hlip_arg (Delta, Pre, s)) as [[[[[? ?] ?] ?] ?] ?].
    apply HLIP_sound.
  + destruct (compute_load_arg (Delta, Pre, s)) as [[[[[[[[[[[[[? ?] ?] ?] ?] ?] ?] ?] ?] ?] ?] ?] ?]|]; [| apply FAIL_sound].
    apply THEN_sound.
    - apply APPLY_sound_load_lemma.
    - apply THEN_sound; apply TRY_sound; [apply FIRST_sound; repeat constructor | repeat apply THEN_sound].
      * apply REFLEXIVITY_OP_CTYPE_sound.
      * apply REFLEXIVITY_BOOL_sound.
      * apply REFLEXIVITY_CEXPR_sound.
      * apply AFTER_SET_LOAD_sound.
      * apply REFLEXIVITYTAC_sound.
      * admit (*reflexivity msusbst_sound*).
      * admit (*reflexivity msusbst_efield_sound*).
      * admit (*reflexivity nth_error_sound*).
      * admit. (* INTROS *)
      * apply APPLY_sound_prop_right.
      * apply REFLEXIVITYTAC_sound.
Qed.

Lemma FORWARD_STORE_sound: forall Struct_env Delta Pre s, rtac_sound (FORWARD_STORE tbl Struct_env Delta Pre s).
Proof.
  intros.
  unfold FORWARD_STORE.
  apply THEN_sound.
  + destruct (compute_hlip_arg (Delta, Pre, s)) as [[[[[? ?] ?] ?] ?] ?].
    apply HLIP_sound.
  + destruct (compute_store_arg (Delta, Pre, s)) as [[[[[[[[[[[[[? ?] ?] ?] ?] ?] ?] ?] ?] ?] ?] ?] ?]|]; [| apply FAIL_sound].
    apply THEN_sound.
    - apply APPLY_sound_store_lemma.
    - apply THEN_sound; apply TRY_sound; [apply FIRST_sound; repeat constructor | repeat apply THEN_sound].
      * apply REFLEXIVITY_CTYPE_sound.
      * apply REFLEXIVITY_BOOL_sound.
      * apply REFLEXIVITY_CEXPR_sound.
      * admit (*after_store*).
      * apply REFLEXIVITYTAC_sound.
      * apply FIRST_sound; repeat constructor.
        apply APPLY_sound_writable_Tsh.
        apply APPLY_sound_writable_Ews.
      * admit (*reflexivity msusbst_sound*).
      * admit (*reflexivity msusbst_efield_sound*).
      * admit (*reflexivity nth_error_sound*).
      * admit. (* INTROS *)
      * apply APPLY_sound_prop_right.
      * apply REFLEXIVITYTAC_sound.
Qed.

Lemma SYMEXE_STEP_sound: forall Struct_env, rtac_sound (SYMEXE_STEP tbl Struct_env).
Proof.
intros.
unfold SYMEXE_STEP.
apply Then.THEN_sound; [apply INSTANTIATE_sound |].
apply runOnGoals_sound.
apply Then.THEN_sound.
eapply AT_GOAL_sound.
intros.
destruct (get_arguments e);
repeat match goal with
         | |- context [ match ?X with _ => _ end ] =>
           destruct X; try apply FAIL_sound
       end.
+ apply FORWARD_SET_sound.
+ apply FORWARD_LOAD_sound.
+ apply FORWARD_STORE_sound.
+ unfold APPLY_SEQ.
  apply THEN_sound.
  unfold APPLY_SEQ'.
  apply EAPPLY_sound; auto with typeclass_instances.
  apply APPLY_condition1.
  apply APPLY_condition2.
  unfold Lemma.lemmaD. unfold split_env. simpl.
  unfold exprT_App, exprT_Inj. simpl.
  intros.
  eapply semax_seq'. eauto. eauto.
  apply SIMPL_DELTA_sound.
+ unfold APPLY_SKIP.
  apply APPLY_sound.
  apply APPLY_condition1.
  apply APPLY_condition2.
  - unfold skip_lemma.
    unfold Lemma.lemmaD, split_env. simpl. intros.
    unfold ExprDsimul.ExprDenote.exprT_App.
    simpl.
    unfold exprT_Inj. apply semax_skip.
+ admit.
Qed.

Theorem SYMEXE_sound : rtac_sound (SYMEXE_TAC_n n tbl).
Proof.
  apply Then.THEN_sound.
  + repeat apply THEN_sound.
    - admit. (*jesper*)
    - apply APPLY_sound_semax_post'.
    - apply TRY_sound.
      eapply AT_GOAL_sound.
      intros.
      destruct (get_arguments e) as [[[[[[[? ?] ?] ?] ?]|] ?] ?]; [| apply FAIL_sound].
      apply REPEAT_sound.
      apply SYMEXE_STEP_sound.
    - apply TRY_sound.
      apply THEN_sound.
      * admit. (* INTROS *)
      * apply APPLY_sound_derives_refl.
  + admit (* MINIFY *).
Qed.

End tbled.

Require Import denote_tac.
Require Import Timing.

Ltac clear_tbl :=
match goal with
[ t := ?V : FMapPositive.PositiveMap.tree (SymEnv.function RType_typ) |- _ ] => clear t
end.

Require Import Timing.
Ltac run_rtac reify term_table tac_sound reduce :=
start_timer "total";
start_timer "02 match_tactic";
  lazymatch type of tac_sound with
    | forall t, @rtac_sound _ _ _ _ _ _ (?tac _) =>
	  let namee := fresh "e" in
	  match goal with
	    | |- ?P =>
              stop_timer "02 match_tactic";
              start_timer "03 reification";
	      reify_aux reify term_table P namee;
              stop_timer "03 reification";
              start_timer "04 match type";
              let tbl := get_tbl in
	      let t :=  constr:(Some typrop) in
	      let goal := namee in
	      match t with
	        | Some ?t =>
	          let goal_result := constr:(run_tac' (tac tbl) (GGoal namee)) in
                  stop_timer"04 match type";
                  start_timer "05 vm_compute";
	          let result := eval vm_compute in goal_result in
                  stop_timer "05 vm_compute";
                  start_timer "06 match result";
	          match result with
	            | More_ ?s ?g =>
                      set (g' := g);
                      set (sv := s);
                      stop_timer "06 match result";
                      start_timer "07 goalD";
                      let gd_prop :=
                          constr:(goalD_Prop tbl nil nil g') in
                      stop_timer "07 goalD";
                      start_timer "08 reduce";
                      let gd' :=
                        reduce g' gd_prop in
                      stop_timer "08 reduce";
                      start_timer "09 cut1";
	              cut (gd');  [ stop_timer "09 cut1";
                                    start_timer "10 change";
                          change (gd_prop ->
                                  exprD_Prop tbl nil nil namee);

                          stop_timer "10 change";
                          start_timer "11 cut2";
	                  cut (goal_result = More_ sv g');
                          [ stop_timer "11 cut2";
                            start_timer "12 exact";
                            (*set (pf := *)
                             exact_no_check
                               (@run_rtac_More tbl (tac tbl)
                                 sv g' namee (tac_sound tbl))
                           (*;
                            exact pf*)
                           | stop_timer "12 exact";
                             start_timer "13 VM_CAST";
                             vm_cast_no_check
                               (@eq_refl _ (More_ sv g'))
                             ]
	                | stop_timer "13 VM_CAST"; clear (*g'*) sv ]
	            | Solved ?s =>
	              exact_no_check (@run_rtac_Solved tbl (tac tbl) s namee (tac_sound tbl)
	                (@eq_refl (Result (CTop nil nil)) (Solved s) <: run_tac' (tac tbl) (GGoal goal) = Solved s))
	            | Fail => idtac "Tactic" tac "failed."
	            | _ => idtac "Error: run_rtac could not resolve the result from the tactic :" tac
	          end
	        | None => idtac "expression " goal "is ill typed" t
	      end
	  end; try (clear namee; clear_tbl)
	| _ => idtac tac_sound "is not a soudness theorem."
  end; stop_timer "total".

Ltac rforward := run_rtac reify_vst term_table (SYMEXE_sound 1000) cbv_denote.

Ltac rforward_admit := run_rtac reify_vst term_table (SYMEXE_sound 1000) admit.

Local Open Scope logic.


Require Import reverse_defs.
Existing Instance NullExtension.Espec.


Fixpoint lots_of_sets' n p :=
match n with
| O => (Sset p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
| S n' => Ssequence (Sset p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))) (lots_of_sets' n' (Psucc p))
end.

Definition lots_of_sets n := lots_of_sets' (pred n) 1%positive.

Fixpoint lots_temps' n p :=
match n with
| O => (PTree.empty _)
| S n' =>  PTree.set p (tptr t_struct_list, true) (lots_temps' n' (Psucc p))
end.

Definition lots_temps (n : nat) : PTree.t (type * bool) := lots_temps' (n) (1%positive).

Fixpoint lots_locals' n p :=
match n with
| O => (PTree.empty _)
| S n' =>  PTree.set p (Vint (Int.repr 0%Z)) (lots_locals' n' (Psucc p))
end.

Definition lots_locals (n : nat):= lots_locals' (n) (1%positive).

Fixpoint lots_vars' n p :=
match n with
| O => (PTree.empty _)
| S n' =>  PTree.set p (tptr t_struct_list, Vint (Int.repr 0%Z)) (lots_vars' n' (Psucc p))
end.

Definition lots_vars (n : nat):= lots_vars' (n) (1%positive).


Fixpoint lots_data_at n sh v :=
match n with
| O => nil
| S n' => data_at sh t_struct_list (Vundef, Vint Int.zero) (force_ptr v) ::
                  lots_data_at n' sh v
end.


Definition test_semax sets temps_tycon temps_local vars_local seps :=
forall post v sh,  (semax
     (mk_tycontext (lots_temps temps_tycon) (PTree.empty type) Tvoid
                   (PTree.empty type) (PTree.empty funspec))
     (assertD [] (localD (lots_locals temps_local) (lots_vars vars_local))
       (lots_data_at seps sh v))
      (lots_of_sets sets)
     (normal_ret_assert  post)).


Definition sets := 1%nat.
Definition temps_tycon := sets.
Definition temps_local := 10%nat.
Definition vars_local := temps_local.
Definition seps := vars_local.

Clear Timing Profile.
Ltac forward := start_timer "LTac"; repeat forward.forward; stop_timer "LTac".

(*Goal test_semax sets temps_tycon temps_local vars_local seps.
cbv [ sets temps_tycon temps_local vars_local seps
      test_semax lots_temps lots_temps' PTree.empty
      lots_of_sets lots_of_sets' lots_data_at Pos.succ PTree.set
      lots_locals lots_locals' lots_vars lots_vars' pred].
cbv [localD LocalD assertD PTree.fold PTree.xfold map liftx].
intros.
forward.
Abort.*)

Goal test_semax sets temps_tycon temps_local vars_local seps.
cbv [ sets temps_tycon temps_local vars_local seps
      test_semax lots_temps lots_temps' PTree.empty
      lots_of_sets lots_of_sets' lots_data_at Pos.succ PTree.set
      lots_locals lots_locals' lots_vars lots_vars' pred].
intros.
rforward.
admit.
Time Qed. (*33 s original*)
(* 36s change*)

Print Timing Profile.

(*


(* 02 match_tactic:	(total:0.003328, mean:0.003328, runs:1, sigma2:0.000000)
03 reification:	(total:1.787002, mean:1.787002, runs:1, sigma2:0.000000)
04 match type:	(total:0.007306, mean:0.007306, runs:1, sigma2:0.000000)
05 vm_compute:	(total:0.690385, mean:0.690385, runs:1, sigma2:0.000000)
06 match result:	(total:0.015118, mean:0.015118, runs:1, sigma2:0.000000)
  07 goalD:	(total:0.083754, mean:0.083754, runs:1, sigma2:0.000000)
 08 reduce:	(total:0.306093, mean:0.306093, runs:1, sigma2:0.000000)
   09 cut1:	(total:0.154493, mean:0.154493, runs:1, sigma2:0.000000)
 10 change:	(total:0.000002, mean:0.000002, runs:1, sigma2:0.000000)
   11 cut2:	(total:0.619691, mean:0.619691, runs:1, sigma2:0.000000)
  12 exact:	(total:0.326034, mean:0.326034, runs:1, sigma2:0.000000)
13 VM_CAST:	(total:0.255638, mean:0.255638, runs:1, sigma2:0.000000)
     total:	(total:4.307944, mean:4.307944, runs:1, sigma2:0.000000) *)

(* for a small goal:
(fun (post : environ -> mpred) (v : val) (sh : Share.t) =>
 let tbl :=
   FMapPositive.PositiveMap.Node
     (FMapPositive.PositiveMap.Node
        (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ))
        (Some (elem_ctor (tyArr tyenviron tympred) post))
        (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ)))
     (Some (elem_ctor tyOracleKind NullExtension.Espec))
     (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ)) in
 let e :=
   App
     (App
        (App
           (App (App (Inj (inr (Smx fsemax))) (Ext 1%positive))
              (App
                 (Inj
                    (inr
                       (Smx
                          (ftycontext
                             (PTree.Node PTree.Leaf
                                (Some (tptr t_struct_list, true)) PTree.Leaf)
                             PTree.Leaf Tvoid PTree.Leaf))))
                 (Inj (inr (Data (fleaf tyfunspec))))))
           (App
              (App
                 (App (Inj (inr (Smx fassertD)))
                    (Inj (inr (Data (fnil typrop)))))
                 (App
                    (App (Inj (inr (Smx flocalD)))
                       (Inj (inr (Data (fleaf tyval)))))
                    (Inj (inr (Data (fleaf (typrod tyc_type tyval)))))))
              (Inj (inr (Data (fnil tympred))))))
        (Inj
           (inr
              (Smx
                 (fstatement
                    (Sset 1%positive
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))))))
     (App (Inj (inr (Smx fnormal_ret_assert))) (Ext 2%positive)) in
 let sv := TopSubst (expr typ func) [] [] in
 (fun
    H : forall x : environ,
        assertD []
          (localD
             (PTree.set 1
                (eval_cast
                   (Tint I32 Signed
                      {| attr_volatile := false; attr_alignas := None |})
                   (Tpointer Tvoid
                      {| attr_volatile := false; attr_alignas := None |})
                   (Vint
                      {|
                      Int.intval := 0;
                      Int.intrange := Int.Z_mod_modulus_range' 0 |}))
                PTree.Leaf) PTree.Leaf) [] x |-- post x =>
  (fun
     H0 : run_tac'
            (SYMEXE_TAC_n 1000
               (FMapPositive.PositiveMap.Node
                  (FMapPositive.PositiveMap.Node
                     (FMapPositive.PositiveMap.Leaf
                        (SymEnv.function RType_typ))
                     (Some (elem_ctor (tyArr tyenviron tympred) post))
                     (FMapPositive.PositiveMap.Leaf
                        (SymEnv.function RType_typ)))
                  (Some (elem_ctor tyOracleKind NullExtension.Espec))
                  (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ))))
            (GGoal e) =
          More_ sv
            (GGoal
               (App
                  (Inj
                     (inl
                        (inl
                           (inr
                              (ModularFunc.ILogicFunc.ilf_forall tyenviron
                                 typrop)))))
                  (Abs tyenviron
                     (App
                        (App
                           (Inj
                              (inl
                                 (inl
                                    (inr
                                       (ModularFunc.ILogicFunc.ilf_entails
                                          tympred)))))
                           (App
                              (App
                                 (App
                                    (App (Inj (inr (Smx fassertD)))
                                       (Inj (inr (Data (fnil typrop)))))
                                    (App
                                       (App (Inj (inr (Smx flocalD)))
                                          (App
                                             (App
                                                (Inj
                                                  (inr (Data (fset tyval 1))))
                                                (App
                                                  (Inj (inr (Eval_f (..))))
                                                  (App
                                                  (Inj (inr (..)))
                                                  (Inj (inr (..))))))
                                             (Inj (inr (Data (fleaf tyval))))))
                                       (Inj
                                          (inr
                                             (Data
                                                (fleaf
                                                  (typrod tyc_type tyval)))))))
                                 (Inj (inr (Data (fnil tympred)))))
                              (Var 0%nat)))
                        (App (Inj (inl (inl (inl 2%positive)))) (Var 0%nat)))))) =>
   run_rtac_More
     (FMapPositive.PositiveMap.Node
        (FMapPositive.PositiveMap.Node
           (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ))
           (Some (elem_ctor (tyArr tyenviron tympred) post))
           (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ)))
        (Some (elem_ctor tyOracleKind NullExtension.Espec))
        (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ)))
     (SYMEXE_TAC_n 1000
        (FMapPositive.PositiveMap.Node
           (FMapPositive.PositiveMap.Node
              (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ))
              (Some (elem_ctor (tyArr tyenviron tympred) post))
              (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ)))
           (Some (elem_ctor tyOracleKind NullExtension.Espec))
           (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ)))) sv
     (GGoal
        (App
           (Inj
              (inl
                 (inl
                    (inr (ModularFunc.ILogicFunc.ilf_forall tyenviron typrop)))))
           (Abs tyenviron
              (App
                 (App
                    (Inj
                       (inl
                          (inl
                             (inr
                                (ModularFunc.ILogicFunc.ilf_entails tympred)))))
                    (App
                       (App
                          (App
                             (App (Inj (inr (Smx fassertD)))
                                (Inj (inr (Data (fnil typrop)))))
                             (App
                                (App (Inj (inr (Smx flocalD)))
                                   (App
                                      (App (Inj (inr (Data (fset tyval 1))))
                                         (App
                                            (Inj
                                               (inr
                                                  (Eval_f
                                                  (feval_cast
                                                  (Tint I32 Signed ..)
                                                  (Tpointer Tvoid ..)))))
                                            (App (Inj (inr (Value fVint)))
                                               (Inj (inr (Const (fint ..)))))))
                                      (Inj (inr (Data (fleaf tyval))))))
                                (Inj
                                   (inr
                                      (Data (fleaf (typrod tyc_type tyval)))))))
                          (Inj (inr (Data (fnil tympred)))))
                       (Var 0%nat)))
                 (App (Inj (inl (inl (inl 2%positive)))) (Var 0%nat)))))) e
     (SYMEXE_sound 1000
        (FMapPositive.PositiveMap.Node
           (FMapPositive.PositiveMap.Node
              (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ))
              (Some (elem_ctor (tyArr tyenviron tympred) post))
              (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ)))
           (Some (elem_ctor tyOracleKind NullExtension.Espec))
           (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ)))) H0)
    (eq_refl
     <:run_tac'
         (SYMEXE_TAC_n 1000
            (FMapPositive.PositiveMap.Node
               (FMapPositive.PositiveMap.Node
                  (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ))
                  (Some (elem_ctor (tyArr tyenviron tympred) post))
                  (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ)))
               (Some (elem_ctor tyOracleKind NullExtension.Espec))
               (FMapPositive.PositiveMap.Leaf (SymEnv.function RType_typ))))
         (GGoal e) =
       More_ sv
         (GGoal
            (App
               (Inj
                  (inl
                     (inl
                        (inr
                           (ModularFunc.ILogicFunc.ilf_forall tyenviron
                              typrop)))))
               (Abs tyenviron
                  (App
                     (App
                        (Inj
                           (inl
                              (inl
                                 (inr
                                    (ModularFunc.ILogicFunc.ilf_entails
                                       tympred)))))
                        (App
                           (App
                              (App
                                 (App (Inj (inr (Smx fassertD)))
                                    (Inj (inr (Data (fnil typrop)))))
                                 (App
                                    (App (Inj (inr (Smx flocalD)))
                                       (App
                                          (App
                                             (Inj (inr (Data (fset tyval 1))))
                                             (App
                                                (Inj
                                                  (inr
                                                  (Eval_f
                                                  (feval_cast (..) (..)))))
                                                (App
                                                  (Inj (inr (Value fVint)))
                                                  (Inj (inr (Const (..)))))))
                                          (Inj (inr (Data (fleaf tyval))))))
                                    (Inj
                                       (inr
                                          (Data
                                             (fleaf (typrod tyc_type tyval)))))))
                              (Inj (inr (Data (fnil tympred)))))
                           (Var 0%nat)))
                     (App (Inj (inl (inl (inl 2%positive)))) (Var 0%nat)))))))
    H) ?139) *)
(*
admit.
Time Qed. (*109 seconds with change for 100 vars
            123 seconds without change for 100 vars
            310 seconds without change for 300 vars
            297 seconds with change for 300 vars
           *)

Lemma skip_triple : forall sh v e,
@semax e empty_tycontext
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val)))
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])
      Sskip  (normal_ret_assert (assertD [] (localD (PTree.empty val) (PTree.empty (type * val)))
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])).
Proof.
intros.
Unset Ltac Debug.
unfold empty_tycontext.
rforward.
Time Qed. (*.8 seconds*)

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

Lemma seq_triple' : forall sh v e,
@semax e empty_tycontext
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val)))
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])
       (Ssequence Sskip Sskip)
     (normal_ret_assert (assertD [] (localD (PTree.empty val) (PTree.empty (type * val)))
       [])).
Proof.
intros.
Locate tint.
unfold empty_tycontext.
Set Printing Depth 500.
rforward.
Abort.

Lemma seq_triple_lots : forall sh v e,
@semax e empty_tycontext
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val)))
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])
      (lots_of_skips 20)
     (normal_ret_assert (assertD [] (localD (PTree.empty val) (PTree.empty (type * val)))
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])).
Proof.
intros.
unfold empty_tycontext.
rforward.
Qed.


Goal
forall {Espec : OracleKind} (contents : list val),
   (semax
     (remove_global_spec Delta) (*empty_tycontext*)
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
       (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
     (normal_ret_assert (assertD [] (localD (PTree.set _p (Values.Vint Int.zero) (PTree.empty val)) (PTree.empty (type * val))) []))).
intros.
unfold empty_tycontext, Delta, remove_global_spec.
rforward.
intros.
apply derives_refl.
Qed.

Notation "'NOTATION_T1' v" := (PTree.Node PTree.Leaf None
         (PTree.Node PTree.Leaf None
            (PTree.Node
               (PTree.Node PTree.Leaf None
                  (PTree.Node
                     (PTree.Node PTree.Leaf
                        (Some v)
                        PTree.Leaf) None PTree.Leaf)) None PTree.Leaf))) (at level 50).


Goal
forall {Espec : OracleKind} (sh:Share.t) (contents : list val) (v: val) ,
   (semax
     (remove_global_spec Delta) (*empty_tycontext*)
     (assertD [] (localD (NOTATION_T1 v) (PTree.empty (type * val)))
       [data_at sh t_struct_list (Vundef, Vint Int.zero) (force_ptr v)])
     (Sset _t
            (Efield (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list)
              _tail (tptr t_struct_list)))
     (normal_ret_assert      (assertD [] (localD (NOTATION_T1 v) (PTree.empty (type * val)))
       [data_at sh t_struct_list (default_val _) (force_ptr v)])
)).
intros.
unfold empty_tycontext, Delta, remove_global_spec.
unfold t_struct_list.

rforward.
split.
+ intros.
  admit.
+ intros.
  simpl.
  simpl typeof.
  unfold proj_val, proj_reptype.
  simpl.
  apply seplog.andp_right; [ apply prop_right; auto |].
  apply prop_right.
  solve_legal_nested_field.
Qed.

Goal (semax
     (remove_global_spec Delta) (*empty_tycontext*)
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
       (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence (Sset _p (Etempvar _p (tptr tvoid)))
       (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence (Sset _p (Etempvar _p (tptr tvoid)))
       (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence (Sset _p (Etempvar _p (tptr tvoid)))
       (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence (Sset _p (Etempvar _p (tptr tvoid)))
       (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence (Sset _p (Etempvar _p (tptr tvoid)))
       (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence (Sset _p (Etempvar _p (tptr tvoid)))
       (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence (Sset _p (Etempvar _p (tptr tvoid)))
       (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence (Sset _p (Etempvar _p (tptr tvoid)))
       (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence (Sset _p (Etempvar _p (tptr tvoid)))
       (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence (Sset _p (Etempvar _p (tptr tvoid)))
                Sskip))))))))))))))))))))
     (normal_ret_assert (assertD [] (localD (PTree.set _p (Values.Vint Int.zero) ((PTree.empty val))) (PTree.empty (type * val))) []))).
intros.
unfold remove_global_spec,Delta. simpl PTree.set.
rforward.
intros.
apply derives_refl.
Qed.

Goal
forall {Espec : OracleKind} (contents : list val) (v: val) ,
   (semax
     (remove_global_spec Delta) (*empty_tycontext*)
     (assertD [] (localD (NOTATION_T1 v) (PTree.empty (type * val)))
       [data_at Tsh t_struct_list (Values.Vundef, Values.Vint Int.zero) (force_ptr v)])
     (Sassign
            (Efield (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list)
              _tail (tptr t_struct_list))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
     (normal_ret_assert      (assertD [] (localD (NOTATION_T1 v) (PTree.empty (type * val)))
       [data_at Tsh t_struct_list (Vundef, Vint Int.zero) (force_ptr v)])
)).
intros.
unfold empty_tycontext, Delta, remove_global_spec.
unfold t_struct_list.
rforward.
split.
+ unfold reptype_reptyp. simpl.
  auto.
+ intros.
  apply prop_right.
  solve_legal_nested_field.
Qed.

(*
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
Eval compute in (lots_of_sets 50).
Qed.


Lemma seq_more :
forall  (contents : list val), exists PO,
   (semax
     (remove_global_spec Delta)
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
     (Ssequence Sskip (*(Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))*)
                (Sgoto _p))
     (normal_ret_assert PO)).
Proof.
unfold Delta, remove_global_spec.
intros.
rforward.
Abort.
*)

*) *)