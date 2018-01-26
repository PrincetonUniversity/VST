Require Import MirrorCharge.ModularFunc.ILogicFunc.
Require Import MirrorCharge.ModularFunc.BILogicFunc.
Require Import MirrorCharge.SynSepLog.
Require Import MirrorCharge.SepLogFold.
Require Export MirrorCore.RTac.RTac.
Require Export MirrorCore.RTac.Core.
(*Require Import MirrorCore.STac.STac.*)
Require Export mc_reify.bool_funcs.
Require MirrorCore.syms.SymEnv.
Require MirrorCore.syms.SymSum.
Require Import MirrorCore.Subst.FMapSubst.
(*Require Import MirrorCharge.RTac.ReifyLemma.*)
Require Import VST.floyd_funcs.
Require Export MirrorCore.Lambda.Expr.
Require Export mc_reify.types.
Require Export mc_reify.func_eq.
Require Export mc_reify.funcs.

Definition typeof_func_opt t := Some (typeof_func t).

Definition eqb_sym a b := match func_beq a b with
                        | true => Some true
                        | false => None
end.

Global Instance RSym_Func' : SymI.RSym func' := {
   typeof_sym := typeof_func_opt;
   symD := funcD;
   sym_eqb := eqb_sym
}.

Global Instance RSymOk_Func' : SymI.RSymOk RSym_Func'.
constructor.
intros. unfold sym_eqb. simpl. unfold eqb_sym. simpl.
destruct (func_beq a b) eqn :?. apply func_beq_sound. auto.
auto.
Qed.


Definition appR (e1 : func') e2 :=
App (@Inj typ func (inr e1)) (e2).
Definition injR (e1 : func') := @Inj typ func (inr e1).

Instance ILogicOps_mpred : ILogic.ILogicOps expr.mpred := {
lentails := derives;
ltrue := TT;
lfalse := FF;
land := andp;
lor := orp;
limpl := imp;
lforall := @allp mpred _;
lexists := @exp mpred _
}.

Instance ILogic_mpred : ILogic.ILogic mpred.
Proof.
split; intros.
+ split.
  * intro x; apply derives_refl.
  * intros x y z Hxy Hyz; apply derives_trans with y; assumption.
+ apply prop_right. apply I.
+ apply prop_left. intro H; destruct H.
+ apply allp_left with x; assumption.
+ apply allp_right; apply H.
+ apply exp_left; apply H.
+ apply exp_right with x; apply H.
+ apply andp_left1; apply H.
+ apply andp_left2; apply H.
+ apply orp_right1; apply H.
+ apply orp_right2; apply H.
+ apply andp_right; [apply H | apply H0].
+ apply orp_left; [apply H | apply H0].
+ apply imp_andp_adjoint. apply H.
+ apply imp_andp_adjoint. apply H.
Qed.

Instance BILOperators_mpred : BILogic.BILOperators mpred := {
  empSP := emp;
  sepSP := sepcon;
  wandSP := wand
}.

Instance BILogic_mpred : BILogic.BILogic mpred.
Proof.
split; intros.
+ apply _.
+ unfold BILogic.sepSP; simpl; rewrite sepcon_comm; apply derives_refl.
+ unfold BILogic.sepSP; simpl; rewrite sepcon_assoc; apply derives_refl.
+ apply wand_sepcon_adjoint.
+ apply sepcon_derives; [apply H | apply derives_refl].
+ unfold BILogic.sepSP; simpl; rewrite sepcon_emp; reflexivity.
Qed.


Definition ilops : @logic_ops _ RType_typ :=
fun t =>
  match t
          return option (ILogic.ILogicOps (typD t))
  with
  | tympred => Some _
  | typrop => Some _
  | _ => None
end.

Definition bilops : @bilogic_ops _ RType_typ :=
fun t =>
  match t
          return option (BILogic.BILOperators (typD t))
  with
  | tympred => Some _
  | _ => None
end.

Instance RSym_ilfunc : RSym (@ilfunc typ) :=
	RSym_ilfunc _ _ ilops.
Instance RSym_bilfunc : RSym (@bilfunc typ) :=
	RSym_bilfunc _ bilops.

Existing Instance SymSum.RSym_sum.
Existing Instance SymSum.RSymOk_sum.

Definition subst : Type :=
  FMapSubst.SUBST.raw (expr typ func).
Instance SS : SubstI.Subst subst (expr typ func) :=
  @FMapSubst.SUBST.Subst_subst _.
(*Instance SU : SubstI.SubstUpdate subst (expr typ func) :=
  FMapSubst.SUBST.SubstUpdate_subst (@instantiate typ func).
Instance SO : SubstI.SubstOk SS :=
  @FMapSubst.SUBST.SubstOk_subst typ RType_typ (expr typ func) _ _.
*)

Definition RSym_sym fs := SymSum.RSym_sum
  (SymSum.RSym_sum (SymSum.RSym_sum (SymEnv.RSym_func fs) RSym_ilfunc) RSym_bilfunc)
  RSym_Func'.


SearchAbout Expr.
Definition Expr_expr_fs fs: ExprI.Expr _ (ExprCore.expr typ func) := @ExprD.Expr_expr typ func _ _ (RSym_sym fs).
Definition Expr_ok_fs fs: @ExprI.ExprOk typ RType_typ (ExprCore.expr typ func) (Expr_expr_fs fs) := ExprD.ExprOk_expr.

Definition reflect ft tus tvs e (ty : typ)
 := @exprD _ _ _ (Expr_expr_fs ft) tus tvs e ty.

Definition reflect_prop tbl e := reflect tbl nil nil e (typrop).

Definition reflect_prop' tbl e := match (reflect tbl nil nil e typrop) with
| Some p => p
| None => False
end.

Definition node l o r t : expr typ func :=
(App (App (App (Inj (inr (Data (fnode t)))) l) o) r).

Definition leaf t : expr typ func:=
(Inj (inr (Data (fleaf t)))).

Definition some_reif e t : expr typ func :=
(App (Inj (inr (Other (fsome t)))) e).

Definition none_reif t : expr typ func :=
(Inj (inr (Other (fnone t)))).

Instance MA : MentionsAny (expr typ func) := {
  mentionsAny := ExprCore.mentionsAny
}.

Let elem_ctor : forall x : typ, typD x -> @SymEnv.function typ _ :=
  @SymEnv.F _ _.

Let Ext x := @ExprCore.Inj typ func (inl (inl (inl x))).

Section tbled.

Variable tbl : SymEnv.functions RType_typ.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.
Let Expr_expr := Expr_expr_fs tbl.
Existing Instance Expr_expr.
Existing Instance Expr_ok_fs.

Definition exprD_Prop (uvar_env var_env : EnvI.env) (e : expr typ func) :=
  match exprD uvar_env var_env e typrop with
    | Some e' => e'
    | None => True
  end.

Definition goalD_Prop (uvar_env var_env : EnvI.env) goal :=
  let (tus, us) := split_env uvar_env in
  let (tvs, vs) := split_env var_env in
  match goalD tus tvs goal with
    | Some e => e us vs
    | None => False
  end.

Definition goalD_aux tus tvs goal (us : HList.hlist typD tus) (vs : HList.hlist typD tvs) :=
  match goalD tus tvs goal with
    | Some e => Some (e us vs)
    | None => None
  end.

End tbled.

