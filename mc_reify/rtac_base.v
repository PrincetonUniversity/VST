Require Import MirrorCore.Lemma.
Require Import MirrorCharge.RTac.ReifyLemma.
Require Import mc_reify.update_tycon.
Require Import MirrorCore.RTac.Then.
Require Import MirrorCore.Lambda.RedAll.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCharge.RTac.Instantiate.
Require Import mc_reify.funcs.
Require Import mc_reify.types.
Require Import mc_reify.typ_eq.
Require Import mc_reify.func_defs.
Require Import MirrorCore.LemmaApply.
Require Import ExtLib.Tactics.
Require Import MirrorCore.Util.ListMapT.

Definition rtacP := sigT (fun tac: rtac typ (expr typ func) =>
  forall tbl: SymEnv.functions RType_typ, rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) tac).

(************************************************

Rtac Part

************************************************)

Definition my_lemma := lemma typ (ExprCore.expr typ func) (ExprCore.expr typ func).

Definition THEN' (r1 r2 : rtac typ (expr typ func)) := THEN r1 (runOnGoals r2).

Definition THEN (r1 r2 : rtac typ (expr typ func)) :=
  THEN' r1 (THEN' (INSTANTIATE typ func) r2).

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


Lemma APPLY_condition1: vars_to_uvars_spec vars_to_uvars.
apply vars_to_uvars_exprD'.
Qed.

Lemma APPLY_condition2:
 forall (subst : Type) (S : Subst subst (expr typ func))
   (SO : SubstOk S) (SU : SubstUpdate subst (expr typ func))
   (SUO : SubstUpdateOk SU SO),
 UnifyI.unify_sound
   (fun (tus tvs : tenv typ) (n : nat) (l r : expr typ func)
      (t : typ) (s : subst) => exprUnify 10 tus tvs n l r t s).
intros.
change (UnifyI.unify_sound (exprUnify 10)).
unfold UnifyI.unify_sound.
generalize (exprUnify_sound).
unfold ExprUnify_common.unify_sound, ExprUnify_common.unify_sound_ind. intros. forward_reason.
Admitted. (*new version!*)

End tbled.

Definition thenP (t1 t2: rtacP) : rtacP :=
  match t1, t2 with
  | existT tac1 p1, existT tac2 p2 =>
      @existT (rtac typ (expr typ func))
        (fun tac => forall tbl, rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) tac)
   (THEN tac1 tac2) (fun tbl => THEN_sound tbl _ _ (p1 tbl) (p2 tbl))
  end.

Definition repeatP (n: nat) (t: rtacP) : rtacP :=
  match t with
  | existT tac p =>
      @existT (rtac typ (expr typ func))
        (fun tac => forall tbl, rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) tac)
        (REPEAT n tac)
        (fun tbl => @REPEAT_sound _ _ _ _ _ (Expr_ok_fs tbl) _ _ _ n _ (p tbl))
  end.







