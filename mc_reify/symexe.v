Require Export mc_reify.reify.
Import VST.floyd.proofauto.
Require Export mc_reify.bool_funcs.
Require Import mc_reify.set_reif.
Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import mc_reify.update_tycon.
Require Export MirrorCore.RTac.Repeat.
Require Import MirrorCore.RTac.Then.
Require Export MirrorCore.RTac.Try.
Require Export MirrorCore.RTac.First.
Require Import MirrorCore.RTac.Fail.
Require Import MirrorCore.RTac.Simplify.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.RTac.Instantiate.
Require Import MirrorCharge.RTac.Intro.
Require Import MirrorCharge.RTac.Apply.
Require Import MirrorCharge.RTac.EApply.
Require Export mc_reify.funcs.
Require Import mc_reify.types.
Require Import mc_reify.typ_eq.
Require Export mc_reify.reflexivity_tacs.
Require Import mc_reify.func_defs.
Require Import MirrorCharge.RTac.Cancellation.
Require Import mc_reify.rtac_base.
Require Import mc_reify.reified_ltac_lemmas.
Require Import mc_reify.hoist_later_in_pre.
Require Import mc_reify.set_load_store.

Local Open Scope logic.

(************************************************

Rtac definition

************************************************)

Ltac reify_expr_tac :=
match goal with
| [ |- ?trm] => reify_vst trm
end.

Ltac do_local2ptree := do 2 (erewrite local2ptree_soundness; [ | repeat constructor ]);
repeat rewrite LocalD_to_localD.
(* Should change to new tactic, not constructor here.     -- Qinxiang *)

Ltac pull_sep_lift R :=
match R with
| ((`?H) :: ?T) => let rest := pull_sep_lift T in constr:(cons H rest)
| (@nil _) => constr:(@nil mpred)
end.

Ltac extract_sep_lift_semax :=
  match goal with
      [ |- context [semax _ (*(PROP (?P1) (LOCALx ?Q1 SEP (?R1)))*)
                 (PROPx ?P1 (LOCALx ?Q1 (SEPx ?R1))) _
                 (normal_ret_assert (*(PROPx ?P2 (LOCALx ?Q2 (SEPx ?R2))))*) _)]] =>
      let R1' := pull_sep_lift R1 in
      (*let R2' := pull_sep_lift R2 in*)
      try (change (PROPx (P1) (LOCALx Q1 (SEPx (R1))))
      with (assertD nil Q1 R1'))(*;
      try  (change (PROPx (P2) (LOCALx Q2 (SEPx (R2))))
      with (assertD nil Q2 R2'))*)
end.

Ltac hnf_tycontext :=
match goal with
[ |- context [semax ?s _ _ _] ] => let ss := eval hnf in s in change s with ss
end.

Ltac prepare_reify :=
do_local2ptree;
extract_sep_lift_semax;
hnf_tycontext.


Definition remove_global_spec (t : tycontext) :=
match t with
| mk_tycontext t v r gt gs => mk_tycontext t v r gt (PTree.empty _)
end.

(************************************************

Pre-rtac computations

************************************************)

Definition is_array_type (t: Ctypes.type) : bool :=
  match t with
  | Tarray _ _ _ => true
  | _ => false
  end.

Fixpoint no_load_expr_bool (e: Clight.expr) : bool :=
  match e with
  | Econst_int _ _ => true
  | Econst_float _ _ => true
  | Econst_single _ _ => true
  | Econst_long _ _ => true
  | Evar _ t => is_array_type t
  | Etempvar _ _ => true
  | Ederef _ _ => false
  | Eaddrof e0 _ => no_load_lvalue_bool e0
  | Eunop _ e0 _ => no_load_expr_bool e0
  | Ebinop _ e0 e1 _ => (no_load_expr_bool e0 && no_load_expr_bool e1)%bool
  | Ecast e0 _ => no_load_expr_bool e0
  | Efield e0 _ t => (is_array_type t && no_load_lvalue_bool e0)%bool
  end
with no_load_lvalue_bool (e: Clight.expr) : bool :=
  match e with
  | Econst_int _ _ => false
  | Econst_float _ _ => false
  | Econst_single _ _ => false
  | Econst_long _ _ => false
  | Evar _ _ => true
  | Etempvar _ _ => false
  | Ederef _ _ => false
  | Eaddrof _ _ => false
  | Eunop _ _ _ => false
  | Ebinop _ _ _ _ => false
  | Ecast _ _ => false
  | Efield e0 _ _ => no_load_lvalue_bool e0
  end.

Inductive ForwardRule : Type :=
| ForwardSet
| ForwardLoad
| ForwardCastLoad
| ForwardStore
| ForwardSeq: statement -> statement -> ForwardRule
| ForwardSkip.

Definition compute_forward_rule (s: statement) : option ForwardRule :=
  match s with
  | Sskip => Some ForwardSkip
  | Ssequence s1 s2 => Some (ForwardSeq s1 s2)
  | Sassign _ _ => Some ForwardStore
  | Sset _ e =>
    if no_load_expr_bool e
    then Some ForwardSet
    else match e with
         | Ecast _ _ => Some ForwardCastLoad
         | _ => Some ForwardLoad
         end
  | _ => None
  end.

Definition get_arguments_delta (e : expr typ func) :=
  match e with
  | App (Inj (inr (Smx (ftycontext t v r gt)))) gf => Some (t, v, r, gt, gf)
  | _ => None
  end.

Definition get_arguments_pre (e : expr typ func) :=
  match e with
  | App (App (App (Inj (inr (Smx fassertD))) P)
      (App (App (Inj (inr (Smx flocalD))) T1) T2)) R => Some (P, T1, T2, R, rstrip_1_later_sep R)
  | _ => None
  end.

Definition get_arguments_statement (e : expr typ func) :=
  match e with
  | Inj (inr (Smx (fstatement s))) => Some s
  | _ => None
  end.

Fixpoint get_arguments (e : expr typ func) :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) _) Delta) Pre) CCmd) _ =>
  (get_arguments_delta Delta,
   get_arguments_pre Pre,
   get_arguments_statement CCmd)
| App _ e
| Abs _ e => get_arguments e
| _ => (None, None, None)
end.

Definition compute_hlip_arg (arg:
         (PTree.t (type * bool) * PTree.t type * type * PTree.t type *
          expr typ func) *
       (expr typ func * expr typ func * expr typ func * expr typ func * expr typ func) *
       statement) :=
  match arg with
  | ((t, v, r, gt, _), (_, _, _, R, _), s) => (t, v, r, gt, s, R)
  end.

Definition compute_set_arg (arg:
         (PTree.t (type * bool) * PTree.t type * type * PTree.t type *
          expr typ func) *
       (expr typ func * expr typ func * expr typ func * expr typ func * expr typ func) *
       statement) :=
  match arg with
  | ((t, v, r, gt, _), _, s) =>
    match s with
    | Sset i e0 =>
      match t ! i with
      | Some (ty, _) => Some (t, v, r, gt, i, e0, ty)
      | _ => None
      end
    | _ => None
    end
  end.

Section empty_RSym_sym.

Instance RSym_SymEnv_fun : RSym SymEnv.func := {
  typeof_sym := fun _ => None;
  symD := fun _ => tt;
  sym_eqb := fun x y => Some (Pos.eqb x y)
}.

Instance RSymOk_SymEnv_fun : RSymOk RSym_SymEnv_fun.
split.
intros.
simpl.
pose proof Pos.eqb_eq a b.
destruct (a =? b)%positive; intros.
+ apply H; auto.
+ intro.
  apply H in H0.
  congruence.
Defined.

Definition sem_eqb_func := @sym_eqb _ _ _ (SymSum.RSym_sum
  (SymSum.RSym_sum (SymSum.RSym_sum RSym_SymEnv_fun RSym_ilfunc) RSym_bilfunc)
  RSym_Func').

Fixpoint expr_beq (e1 e2: expr typ func) : bool :=
  match e1, e2 with
  | Var i1, Var i2 => beq_nat i1 i2
  | Inj f1, Inj f2 =>
    match sem_eqb_func f1 f2 with
    | Some true => true
    | _ => false
    end
  | App e11 e12, App e21 e22 => andb (expr_beq e11 e21) (expr_beq e12 e22)
  | Abs ty1 e11, Abs ty2 e21 => andb (expr_beq e11 e21) (typ_beq ty1 ty2)
  | UVar i1, UVar i2 => beq_nat i1 i2
  | _, _ => false
  end.

End empty_RSym_sym.

Fixpoint nth_solver_rec (R: expr typ func) (p: expr typ func) (n: nat) :=
match R with
| Inj (inr (Data (fnil tympred))) => None
| App (App (Inj (inr (Data (fcons tympred)))) hd) tl =>
  match hd with
  | App (App (App (Inj (inr (Sep (fdata_at t_root)))) sh) v) p' =>
      if (expr_beq p p')
      then Some (t_root, n)
      else nth_solver_rec tl p (S n)
  | _ => nth_solver_rec tl p (S n)
  end
| _ => None
end.

Definition nth_solver R p := nth_solver_rec R p 0.

Definition compute_load_arg (arg:
         (PTree.t (type * bool) * PTree.t type * type * PTree.t type *
          expr typ func) *
       (expr typ func * expr typ func * expr typ func * expr typ func * expr typ func) *
       statement) :=
  match arg with
  | ((t, v, r, gt, _), (_, T1, T2, _, R'), s) =>
    match s with
    | Sset i e0 =>
      match t ! i, compute_nested_efield e0 with
      | Some (ty, _), (e1, efs, tts) =>
        let lr := compute_lr e1 efs in
        match rmsubst_eval_LR T1 T2 e1 lr with
        | App (Inj (inr (Other (fsome tyval)))) p =>
          match nth_solver R' p with
          | Some (t_root, n) =>
              Some (t, v, r, gt, i, ty, t_root, e0, e1, efs, tts, lr, n)
          | _ => None
          end
        | _ => None
        end
      | _, _ => None
      end
    | _ => None
    end
  end.

Definition compute_store_arg (arg:
         (PTree.t (type * bool) * PTree.t type * type * PTree.t type *
          expr typ func) *
       (expr typ func * expr typ func * expr typ func * expr typ func * expr typ func) *
       statement) :=
  match arg with
  | ((t, v, r, gt, _), (_, T1, T2, _, R'), s) =>
    match s with
    | Sassign e0 e2 =>
      match compute_nested_efield e0 with
      | (e1, efs, tts) =>
        let ty := typeof e0 in
        let lr := compute_lr e1 efs in
        match rmsubst_eval_LR T1 T2 e1 lr with
        | App (Inj (inr (Other (fsome tyval)))) p =>
          match nth_solver R' p with
          | Some (t_root, n) =>
              Some (t, v, r, gt, ty, t_root, e0, e1, e2, efs, tts, lr, n)
          | _ => None
          end
        | _ => None
        end
      end
    | _ => None
    end
  end.

Section tbled.

Variable n : nat.
Variable tbl : SymEnv.functions RType_typ.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.

Lemma semax_seq_reif c1 c2 : forall  (Espec : OracleKind)
         (P : environ -> mpred)  (P' : environ -> mpred)
          (Q : ret_assert) (Delta : tycontext) ,
       @semax Espec Delta P c1 (normal_ret_assert P') ->
       @semax Espec (update_tycon Delta c1) P' c2 Q ->
       @semax Espec Delta P (Ssequence c1 c2) Q.
intros.
eapply semax_seq'; eauto.
Qed.

Definition skip_lemma : my_lemma.
reify_lemma reify_vst
@semax_skip.
Defined.

Definition seq_lemma (s1 s2: statement)  : my_lemma.
reify_lemma reify_vst (semax_seq_reif s1 s2).
Defined.

Definition replace_set (e : expr typ func) : expr typ func :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) es)
                     Delta) pre) s) post =>
  let newpre :=
      match pre with
        |  App (App (App (Inj (inr (Smx fassertD))) P)
                    (App (App (Inj (inr (Smx flocalD)))
                              T1) T2)) R =>
           let newT1 := match T1 with
                          | App (App
                                    (Inj (inr (Data (fset tyval n))))
                                    val) T1' =>
                            get_set_reif.set_reif n val T1' tyval
                          | _ => T1
                        end in
           App (App (App (Inj (inr (Smx fassertD))) P)
                    (App (App (Inj (inr (Smx flocalD)))
                              newT1) T2)) R
        | _ => pre
      end in
  App (App (App (App (App (Inj (inr (Smx fsemax))) es)
                     Delta) newpre) s) post
| _ => e
end.

Definition SIMPL_SET : rtac typ (ExprCore.expr typ func) :=
SIMPLIFY (fun _ _ _ _ => replace_set).

Definition update_tycon_tac (l : list (option (expr typ func)))
(e : expr typ func) (args : list (expr typ func))
	: expr typ func :=
match e with
    | (Inj (inr (Smx (fupdate_tycon)))) =>
      match args with
          | [App (Inj (inr (Smx (ftycontext t v r gt)))) gs; (Inj (inr (Smx (fstatement s))))] =>
            App (Inj (inr (Smx (ftycontext (update_temp t s) v r gt)))) gs
          | _ =>  AppN.apps e args
      end
    | _ => AppN.apps e args
end.

Definition SIMPL_DELTA : rtac typ (ExprCore.expr typ func) :=
SIMPLIFY (fun _ _ _ _=>beta_all update_tycon_tac).

Definition INTROS := (REPEAT 10 (INTRO typ func)).

Definition APPLY_SKIP :=  (APPLY typ func  skip_lemma).

Definition run_tac (t: rtac typ (ExprCore.expr typ func)) e :=
  t nil nil 0%nat 0%nat (CTop nil nil) (ctx_empty (expr := expr typ func)) e.

Definition run_tac_intros e :=
run_tac (THEN INTROS e).

Definition APPLY_SEQ' s1 s2 := (EAPPLY typ func (seq_lemma s1 s2)).

Definition APPLY_SEQ s1 s2 := THEN (APPLY_SEQ' s1 s2) (SIMPL_DELTA).
(*
Definition APPLY_SET' id e t v r gt:=
EAPPLY typ func  (set_lemma id e t v r gt).
*)

Definition FORWARD_SET Delta Pre s :=
  let _HLIP :=
  match compute_hlip_arg (Delta, Pre, s) with
  | (temp, var, ret, gt, s, R) => HLIP tbl temp var ret gt R s
  end in
  let _APPLY_SET :=
  match compute_set_arg (Delta, Pre, s) with
  | Some (temp, var, ret, gt, i, e0, ty) =>
      THEN (EAPPLY typ func (set_lemma temp var ret gt i e0 ty))
           (TRY (FIRST [REFLEXIVITY_OP_CTYPE tbl;
                        REFLEXIVITY_MSUBST tbl;
                        REFLEXIVITY_BOOL tbl;
                        AFTER_SET_LOAD tbl;
                        REFLEXIVITY tbl]))
  | _ => FAIL
  end in
  THEN _HLIP _APPLY_SET.

Definition FORWARD_LOAD Struct_env Delta Pre s :=
  let _HLIP :=
  match compute_hlip_arg (Delta, Pre, s) with
  | (temp, var, ret, gt, s, R) => HLIP tbl temp var ret gt R s
  end in
  let _APPLY_LOAD :=
  match compute_load_arg (Delta, Pre, s) with
  | Some (t, v, r, gt, i, ty, t_root, e0, e1, efs, tts, lr, n) =>
            (THEN (EAPPLY typ func (load_lemma t v r gt i ty t_root e0 e1 efs tts Struct_env lr n))
            (THEN (TRY (FIRST [REFLEXIVITY_OP_CTYPE tbl;
                               REFLEXIVITY_BOOL tbl;
                               REFLEXIVITY_CEXPR tbl;
                               AFTER_SET_LOAD tbl;
                               REFLEXIVITY tbl;
                               REFLEXIVITY_MSUBST tbl;
                               REFLEXIVITY_MSUBST_EFIELD tbl;
                               REFLEXIVITY_NTH_ERROR tbl]))
                  (TRY (THEN INTROS
                       (THEN (EAPPLY typ func reify_prop_right)
                             (REFLEXIVITY tbl))))))
  | _ => FAIL
  end in
  THEN _HLIP _APPLY_LOAD.

Definition FORWARD_STORE Struct_env Delta Pre s :=
  let _HLIP :=
  match compute_hlip_arg (Delta, Pre, s) with
  | (temp, var, ret, gt, s, R) => HLIP tbl temp var ret gt R s
  end in
  let _APPLY_STORE :=
  match compute_store_arg (Delta, Pre, s) with
  | Some (t, v, r, gt, ty, t_root, e0, e1, e2, efs, tts, lr, n) =>
            (THEN (EAPPLY typ func (store_lemma t v r gt ty t_root e0 e1 e2 efs tts Struct_env lr n))
            (THEN (TRY (FIRST [REFLEXIVITY_CTYPE tbl;
                               REFLEXIVITY_BOOL tbl;
                               REFLEXIVITY_CEXPR tbl;
                               AFTER_STORE tbl;
                               REFLEXIVITY tbl;
                               FIRST [APPLY typ func writable_Tsh_lemma; APPLY typ func writable_Ews_lemma];
                               REFLEXIVITY_MSUBST tbl;
                               REFLEXIVITY_MSUBST_EFIELD tbl;
                               REFLEXIVITY_NTH_ERROR tbl]))
                  (TRY (THEN INTROS
                       (THEN (EAPPLY typ func reify_prop_right)
                             (REFLEXIVITY tbl))))))
  | _ => FAIL
  end in
  THEN _HLIP _APPLY_STORE.

Definition SYMEXE_STEP Struct_env
: rtac typ (expr typ func)  :=
  THEN' (INSTANTIATE typ func)
  (Then.THEN (AT_GOAL
    (fun c s e =>
         match (get_arguments e) with
         | (Some Delta, Some Pre, Some s) =>
           match compute_forward_rule s with
           | Some ForwardSkip => APPLY_SKIP
           | Some (ForwardSeq s1 s2) => APPLY_SEQ s1 s2
           | Some ForwardSet => FORWARD_SET Delta Pre s
           | Some ForwardLoad => FORWARD_LOAD Struct_env Delta Pre s
           | Some ForwardStore => FORWARD_STORE Struct_env Delta Pre s
           | _ => FAIL
           end
         | _ => FAIL
         end)) (@RTac.Minify.MINIFY typ (expr typ func) _)).

Existing Instance func_defs.Expr_ok_fs.

Definition SYMEXE_TAC_n :=
  Then.THEN (
  THEN
   (THEN INTROS
   (THEN (EAPPLY typ func reify_semax_post')
         (TRY (AT_GOAL
                (fun c s e =>
                   match (get_arguments e) with
                   | (Some (A, B, C, D, _), _, _) =>
                     (REPEAT n (SYMEXE_STEP (compute_type_id_env (mk_tycontext A B C D (PTree.empty funspec)))))
                   | _ => FAIL
                   end)))))
   (TRY (THEN INTROS (EAPPLY typ func reify_derives_refl)))) (@RTac.Minify.MINIFY typ (expr typ func) _).

(*Definition SYMEXE_TAC := SYMEXE_TAC_n 1000.

Definition SYMEXE1_TAC := SYMEXE_TAC_n 1.*)

Definition rreflexivity e :=
run_tac (REFLEXIVITY tbl) e.

Definition test_lemma :=
  @lemmaD typ (expr typ func) RType_typ ExprD.Expr_expr (expr typ func)
          (fun tus tvs e => ExprDsimul.ExprDenote.exprD' tus tvs typrop e)
          _
          nil nil.

Fixpoint is_pure (e : expr typ func) :=
match e with
| App e1 e2 => is_pure e1
| (Inj (inr (Sep fprop))) => true
| _ => false
end.

Definition CANCEL e := run_tac (THEN INTROS (CANCELLATION typ func tympred is_pure)) e.

Let Expr_expr := (Expr_expr_fs tbl).
Existing Instance Expr_expr.

Definition run_tac' tac goal :=
  runOnGoals tac nil nil 0 0 (CTop nil nil)
    (ctx_empty (typ := typ) (expr := expr typ func)) goal.

Lemma run_rtac_More tac s goal e
  (Hsound : rtac_sound tac)
  (Hres : run_tac' tac (GGoal e) = More_ s goal) :
  goalD_Prop tbl nil nil goal -> exprD_Prop tbl nil nil e.
Proof.
  intros He'.
  apply runOnGoals_sound_ind with (g := GGoal e) (ctx := CTop nil nil)
  	(s0 := TopSubst (expr typ func) nil nil) in Hsound.
  unfold rtac_spec in Hsound. simpl in Hsound.
  unfold run_tac' in Hres. simpl in Hres.
  rewrite Hres in Hsound.
  assert (WellFormed_Goal nil nil (GGoal (typ := typ) e)) as H1 by constructor.
  assert (WellFormed_ctx_subst (TopSubst (expr typ func) nil (@nil typ))) as H2 by constructor.
  specialize (Hsound H1 H2).
  destruct Hsound as [Hwfs [Hwfg Hsound]].
  unfold propD, exprD'_typ0 in Hsound.
  simpl in Hsound. unfold exprD_Prop, exprD; simpl.
  Require Import ExtLib.Tactics.
  forward; inv_all; subst.

  destruct Hsound.
  inversion Hwfs; subst.
  simpl in H0; inv_all; subst.
  unfold pctxD in H0; inv_all; subst.
  apply H5.
  unfold goalD_Prop in He'. simpl in He'.
  destruct (goalD [] [] goal); congruence.
Qed.

Lemma run_rtac_Solved tac s e
  (Hsound : rtac_sound tac)
  (Hres : run_tac' tac (GGoal e) = Solved s) :
  exprD_Prop tbl nil nil e.
Proof.
  unfold run_tac' in Hres.
  unfold rtac_sound in Hsound.
  assert (WellFormed_Goal nil nil (GGoal (typ := typ) e)) as H1 by constructor.
  assert (WellFormed_ctx_subst (TopSubst (expr typ func) nil (@nil typ))) as H2 by constructor.
  specialize (Hsound _ _ _ _ Hres H1 H2).
  destruct Hsound as [Hwfs Hsound].
  simpl in Hsound.
  unfold propD, exprD'_typ0 in Hsound.
  unfold exprD_Prop.

  simpl in Hsound. unfold exprD. simpl. forward.
  destruct Hsound.
  inversion Hwfs; subst. simpl in H8. inv_all; subst.
  simpl in *.
  admit.
Qed.

End tbled.

Definition symexe tbl e :=
run_tac (SYMEXE_TAC_n 1000 tbl) e .

Definition symexe1 tbl e  :=
run_tac (SYMEXE_TAC_n 1 tbl ) e.
(*
Require Import reverse_defs.
Existing Instance NullExtension.Espec.

Notation "'NOTATION_T1' v" := (PTree.Node PTree.Leaf None
         (PTree.Node PTree.Leaf None
            (PTree.Node
               (PTree.Node PTree.Leaf None
                  (PTree.Node
                     (PTree.Node PTree.Leaf
                        (Some v)
                        PTree.Leaf) None PTree.Leaf)) None PTree.Leaf))) (at level 50).

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
       [data_at Tsh t_struct_list (default_val _) (force_ptr v)])
)).
intros.
unfold empty_tycontext, Delta, remove_global_spec.
unfold t_struct_list.

(*
hoist_later_in_pre.
eapply semax_post'.
Focus 2.
Check semax_store_localD.
eapply semax_store_localD with (lr := LLLL) (e1 := Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list)
  (efs := [eStructField _tail]) (tts := [tptr t_struct_list]) (e := Struct_env) (t_root := t_struct_list)
 (gfs := [StructField _tail]) (sh := Tsh).
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
*)
reify_expr_tac.
Set Printing Depth 200.
Set Printing All.
Eval vm_compute in (run_tac
        (match (get_arguments e) with
         | (Some Delta, Some Pre, Some s) =>
             THEN (INTROS) (FORWARD_STORE tbl Struct_env Delta Pre s)
         | _ => FAIL
         end) e).
*)

Goal forall (sh : share) (v1 v2 : val), False.
intros.
reify_vst (data_at sh tint v1 v2).
Abort.

Goal forall sh v1 v2, (data_at sh tint v1 v2) |-- (data_at sh tint v1 v2).
intros. simpl reptype in *.
reify_expr_tac.
Eval vm_compute in CANCEL tbl e.
Abort.

Goal forall P Q b,  !!b && P * Q |-- !!b && Q * P .
reify_expr_tac.
Abort.

Goal forall (sh : share), sh = sh.
reify_expr_tac.
Eval vm_compute in run_tac (THEN INTROS (REFLEXIVITYTAC tbl)) e.
Abort.

Existing Instance NullExtension.Espec.

Definition replace_set2 (e : expr typ func) : expr typ func :=
match e with
| App (App (App (App (App (Inj (inr (Smx fsemax))) es)
                     Delta) pre) s) post =>
  let newpre :=
      match pre with
        |  App (App (App (Inj (inr (Smx fassertD))) P)
                    (App (App (Inj (inr (Smx flocalD)))
                              T1) T2)) R =>
           let newT1 := match T1 with
                          | App (App
                                    (Inj (inr (Data (fset tyval n))))
                                    val) T1' =>
                            get_set_reif.set_reif n val T1' tyval
                          | _ => T1
                        end in
           App (App (App (Inj (inr (Smx fassertD))) P)
                    (App (App (Inj (inr (Smx flocalD)))
                              newT1) T2)) R
        | _ => pre
      end in
  App (App (App (App (App (Inj (inr (Smx fsemax))) es)
                     Delta) newpre) s) post
| _ => e
end.

Goal forall sh ty v1 v2, mapsto sh ty v1 v2 = mapsto sh ty v1 v2.
reify_expr_tac.
Eval vm_compute in run_tac (THEN INTROS (REFLEXIVITYTAC tbl)) e.
Abort.

