Require Import floyd.proofauto.
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
SearchAbout RedAll.beta_all.
admit.
Qed.
Check propD.

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
      * apply REFLEXIVITYTAC_sound.
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
apply THEN_sound; [apply SIMPL_SET_sound |].
eapply AT_GOAL_sound.
intros.
destruct (get_arguments e);
repeat match goal with
         | |- context [ match ?X with _ => _ end ] =>
           destruct X; try apply FAIL_sound
       end.
+ apply FORWARD_SET_sound.
+ apply FORWARD_LOAD_sound.
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
Qed.

Theorem SYMEXE_sound : rtac_sound (SYMEXE_TAC_n n tbl).
Proof.
  repeat apply THEN_sound.
  + admit. (*jesper*)
  + apply APPLY_sound_semax_post'.
  + apply TRY_sound.
    eapply AT_GOAL_sound.
    intros.
    destruct (get_arguments e) as [[[[[[[? ?] ?] ?] ?]|] ?] ?]; [| apply FAIL_sound].
    apply REPEAT_sound.
    apply SYMEXE_STEP_sound.
  + apply TRY_sound.
    apply THEN_sound.
    - admit. (* INTROS *)
    - apply APPLY_sound_derives_refl.
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
      Sskip  (normal_ret_assert (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) 
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])).
Proof. 
intros.
unfold empty_tycontext.
rforward.
Qed.

Lemma skip_triple' : forall sh v e,
@semax e empty_tycontext
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) 
       [data_at sh (tptr tint) (default_val _) (force_ptr v)])
      Sskip  (normal_ret_assert (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) 
       [])).
Proof. 
intros.
unfold empty_tycontext.
rforward.
(*
1 subgoals, subgoal 1 (ID 1060)
  
  sh : Share.t
  v : val
  e : OracleKind
  ============================
   (let (typeof_sym, symD, _) as RSym
        return
          (forall f : ModularFunc.ILogicFunc.ilfunc typ,
           match (let (typeof_sym, _, _) := RSym in typeof_sym) f with
           | Some t =>
               (fix typD (t0 : typ) : Type :=
                  match t0 with
                  | tyArr a b => typD a -> typD b
                  | tytycontext => tycontext
                  | tyc_expr => Clight.expr
                  | tyc_type => type
                  | tyenviron => environ
                  | tyval => val
                  | tyshare => share
                  | tyident => ident
                  | tylist t1 => list (typD t1)
                  | tyint => int
                  | tyZ => Z
                  | tynat => nat
                  | typositive => positive
                  | tybool => bool
                  | tycomparison => comparison
                  | tytc_assert => tc_assert
                  | tyint64 => int64
                  | tyfloat => float
                  | tyfloat32 => float32
                  | tyattr => attr
                  | tysignedness => signedness
                  | tyintsize => intsize
                  | tyfloatsize => floatsize
                  | tytypelist => typelist
                  | tyfieldlist => fieldlist
                  | tybinary_operation => Cop.binary_operation
                  | tyunary_operation => Cop.unary_operation
                  | tyN => N
                  | tyoption t1 => option (typD t1)
                  | typrop => Prop
                  | tympred => mpred
                  | tysum t1 t2 => (typD t1 + typD t2)%type
                  | typrod t1 t2 => (typD t1 * typD t2)%type
                  | tyunit => unit
                  | tyOracleKind => OracleKind
                  | tystatement => statement
                  | tyret_assert => ret_assert
                  | tyexitkind => exitkind
                  | typtree t1 => PTree.t (typD t1)
                  | tygfield => gfield
                  | tyfunspec => funspec
                  | tyefield => efield
                  | tytype_id_env => type_id_env
                  | tyllrr => LLRR
                  end) t
           | None => unit
           end) := RSym_ilfunc in
    symD) (ModularFunc.ILogicFunc.ilf_forall tyenviron typrop)
     (fun x : environ =>
      (let (typeof_sym, symD, _) as RSym
           return
             (forall f : ModularFunc.ILogicFunc.ilfunc typ,
              match (let (typeof_sym, _, _) := RSym in typeof_sym) f with
              | Some t =>
                  (fix typD (t0 : typ) : Type :=
                     match t0 with
                     | tyArr a b => typD a -> typD b
                     | tytycontext => tycontext
                     | tyc_expr => Clight.expr
                     | tyc_type => type
                     | tyenviron => environ
                     | tyval => val
                     | tyshare => share
                     | tyident => ident
                     | tylist t1 => list (typD t1)
                     | tyint => int
                     | tyZ => Z
                     | tynat => nat
                     | typositive => positive
                     | tybool => bool
                     | tycomparison => comparison
                     | tytc_assert => tc_assert
                     | tyint64 => int64
                     | tyfloat => float
                     | tyfloat32 => float32
                     | tyattr => attr
                     | tysignedness => signedness
                     | tyintsize => intsize
                     | tyfloatsize => floatsize
                     | tytypelist => typelist
                     | tyfieldlist => fieldlist
                     | tybinary_operation => Cop.binary_operation
                     | tyunary_operation => Cop.unary_operation
                     | tyN => N
                     | tyoption t1 => option (typD t1)
                     | typrop => Prop
                     | tympred => mpred
                     | tysum t1 t2 => (typD t1 + typD t2)%type
                     | typrod t1 t2 => (typD t1 * typD t2)%type
                     | tyunit => unit
                     | tyOracleKind => OracleKind
                     | tystatement => statement
                     | tyret_assert => ret_assert
                     | tyexitkind => exitkind
                     | typtree t1 => PTree.t (typD t1)
                     | tygfield => gfield
                     | tyfunspec => funspec
                     | tyefield => efield
                     | tytype_id_env => type_id_env
                     | tyllrr => LLRR
                     end) t
              | None => unit
              end) := RSym_ilfunc in
       symD) (ModularFunc.ILogicFunc.ilf_entails tympred)
        (assertD [] (localD PTree.Leaf PTree.Leaf)
           [data_at sh
              (Tpointer
                 (Tint I32 Signed
                    {| attr_volatile := false; attr_alignas := None |})
                 {| attr_volatile := false; attr_alignas := None |})
              (reptyp_reptype
                 (Tpointer
                    (Tint I32 Signed
                       {| attr_volatile := false; attr_alignas := None |})
                    {| attr_volatile := false; attr_alignas := None |})
                 (default_val (tptr tint))) (force_ptr v)] x)
        (assertD [] (localD PTree.Leaf PTree.Leaf) [] x))

*)

Abort.

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
rforward.
Qed.

Require Import reverse_defs.
Existing Instance NullExtension.Espec.

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
(*
1 subgoals, subgoal 1 (ID 2205)
  
  Espec : OracleKind
  contents : list val
  ============================
   (let (typeof_sym, symD, _) as RSym
        return
          (forall f : ModularFunc.ILogicFunc.ilfunc typ,
           match (let (typeof_sym, _, _) := RSym in typeof_sym) f with
           | Some t =>
               (fix typD (t0 : typ) : Type :=
                  match t0 with
                  | tyArr a b => typD a -> typD b
                  | tytycontext => tycontext
                  | tyc_expr => Clight.expr
                  | tyc_type => type
                  | tyenviron => environ
                  | tyval => val
                  | tyshare => share
                  | tyident => ident
                  | tylist t1 => list (typD t1)
                  | tyint => int
                  | tyZ => Z
                  | tynat => nat
                  | typositive => positive
                  | tybool => bool
                  | tycomparison => comparison
                  | tytc_assert => tc_assert
                  | tyint64 => int64
                  | tyfloat => float
                  | tyfloat32 => float32
                  | tyattr => attr
                  | tysignedness => signedness
                  | tyintsize => intsize
                  | tyfloatsize => floatsize
                  | tytypelist => typelist
                  | tyfieldlist => fieldlist
                  | tybinary_operation => Cop.binary_operation
                  | tyunary_operation => Cop.unary_operation
                  | tyN => N
                  | tyoption t1 => option (typD t1)
                  | typrop => Prop
                  | tympred => mpred
                  | tysum t1 t2 => (typD t1 + typD t2)%type
                  | typrod t1 t2 => (typD t1 * typD t2)%type
                  | tyunit => unit
                  | tyOracleKind => OracleKind
                  | tystatement => statement
                  | tyret_assert => ret_assert
                  | tyexitkind => exitkind
                  | typtree t1 => PTree.t (typD t1)
                  | tygfield => gfield
                  | tyfunspec => funspec
                  | tyefield => efield
                  | tytype_id_env => type_id_env
                  | tyllrr => LLRR
                  end) t
           | None => unit
           end) := RSym_ilfunc in
    symD) (ModularFunc.ILogicFunc.ilf_forall tyenviron typrop)
     (fun x : environ =>
      (let (typeof_sym, symD, _) as RSym
           return
             (forall f : ModularFunc.ILogicFunc.ilfunc typ,
              match (let (typeof_sym, _, _) := RSym in typeof_sym) f with
              | Some t =>
                  (fix typD (t0 : typ) : Type :=
                     match t0 with
                     | tyArr a b => typD a -> typD b
                     | tytycontext => tycontext
                     | tyc_expr => Clight.expr
                     | tyc_type => type
                     | tyenviron => environ
                     | tyval => val
                     | tyshare => share
                     | tyident => ident
                     | tylist t1 => list (typD t1)
                     | tyint => int
                     | tyZ => Z
                     | tynat => nat
                     | typositive => positive
                     | tybool => bool
                     | tycomparison => comparison
                     | tytc_assert => tc_assert
                     | tyint64 => int64
                     | tyfloat => float
                     | tyfloat32 => float32
                     | tyattr => attr
                     | tysignedness => signedness
                     | tyintsize => intsize
                     | tyfloatsize => floatsize
                     | tytypelist => typelist
                     | tyfieldlist => fieldlist
                     | tybinary_operation => Cop.binary_operation
                     | tyunary_operation => Cop.unary_operation
                     | tyN => N
                     | tyoption t1 => option (typD t1)
                     | typrop => Prop
                     | tympred => mpred
                     | tysum t1 t2 => (typD t1 + typD t2)%type
                     | typrod t1 t2 => (typD t1 * typD t2)%type
                     | tyunit => unit
                     | tyOracleKind => OracleKind
                     | tystatement => statement
                     | tyret_assert => ret_assert
                     | tyexitkind => exitkind
                     | typtree t1 => PTree.t (typD t1)
                     | tygfield => gfield
                     | tyfunspec => funspec
                     | tyefield => efield
                     | tytype_id_env => type_id_env
                     | tyllrr => LLRR
                     end) t
              | None => unit
              end) := RSym_ilfunc in
       symD) (ModularFunc.ILogicFunc.ilf_entails tympred)
        (assertD []
           (localD
              (PTree.set 37
                 (eval_cast
                    (Tint I32 Signed
                       {| attr_volatile := false; attr_alignas := None |})
                    (Tpointer Tvoid
                       {| attr_volatile := false; attr_alignas := None |})
                    (Vint
                       {|
                       Int.intval := 0;
                       Int.intrange := Int.Z_mod_modulus_range' 0 |}))
                 PTree.Leaf) PTree.Leaf) [] x)
        (assertD []
           (localD (PTree.set 37 (Vint Int.zero) PTree.Leaf) PTree.Leaf) 
           [] x))

*)
(* Hey Joey, maybe this proof helps you with the white list. *)
unfold RSym_ilfunc.
simpl.
unfold ModularFunc.ILogicFunc.typ2_cast_quant.
simpl.
intros.
apply derives_refl.
Qed.

(* The reason that derives_refl in Rtac does not solve the goal is that
(eval_cast _ _ _) is reified one side and remains unreified on the other side. *)

Goal (semax
     (remove_global_spec Delta) (*empty_tycontext*)
     (assertD [] (localD (PTree.empty val) (PTree.empty (type * val))) [])
       (Ssequence (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence (Sset _p (Etempvar _p (tptr tvoid)))
                Sskip))
     (normal_ret_assert (assertD [] (localD (PTree.set _p (Values.Vint Int.zero) ((PTree.empty val))) (PTree.empty (type * val))) []))).

intros.
unfold remove_global_spec,Delta. simpl PTree.set.
rforward.
unfold RSym_ilfunc.
simpl.
unfold ModularFunc.ILogicFunc.typ2_cast_quant.
simpl.
intros.
apply derives_refl.
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
