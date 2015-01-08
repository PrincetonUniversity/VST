Require Import mc_reify.func_defs.
Require Import mc_reify.list_ctype_eq.
Require Import MirrorCore.Lambda.ExprUnify_simul.
Require Import MirrorCore.RTac.RTac.
Require Import MirrorCore.Lemma.
Require Import MirrorCore.RTac.Core.
(*Require Import MirrorCharge.RTac.ReifyLemma.*)
Require Import mc_reify.update_tycon.
Require Import mc_reify.set_reif.

Section tbled.

Existing Instance SubstUpdate_ctx_subst.

Variable tbl : SymEnv.functions RType_typ.

Instance SS : SubstI.Subst subst (expr typ func) :=
  @FMapSubst.SUBST.Subst_subst _.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.



Definition REFLEXIVITYTAC : rtac typ (expr typ func) :=
fun tus tvs n m c s e => 
  match e with 
| (App (App (Inj (inr (Other (feq ty)))) l) r) =>
  match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
                                 tus tvs 0 l r ty s with
    | Some s => RTac.Core.Solved s 
    | None =>  RTac.Core.Fail
  end
| _ => RTac.Core.Fail
end.

Lemma REFLEXIVITYTAC_sound  :
rtac_sound (Expr_expr := func_defs.Expr_expr_fs tbl) REFLEXIVITYTAC.
unfold rtac_sound.
intros.
 unfold rtac_spec.
simpl in *.
Admitted.

Definition REFLEXIVITY := REFLEXIVITYTAC.

Definition REFLEXIVITYTAC_msubst : rtac typ (expr typ func) :=
fun tus tvs n m c s e => 
  match e with 
| (App (App (Inj (inr (Other (feq ty)))) l) r) =>
  match l with
  | App
      (App
         (App
            (App (Inj (inr (Smx fmsubst_eval_LR))) T1) T2) 
         (Inj (inr (Const (fCexpr e1)))))
      (Inj (inr (Const (fllrr lr)))) =>
    let l' := rmsubst_eval_LR T1 T2 e1 lr in
    match @exprUnify (ctx_subst c) typ func _ _ _ _ _ 3
                                 tus tvs 0 l' r ty s with
    | Some s => RTac.Core.Solved s 
    | None =>  RTac.Core.Fail
    end
  | _ => RTac.Core.Fail
  end
| _ => RTac.Core.Fail
end.

Definition REFLEXIVITY_MSUBST := REFLEXIVITYTAC_msubst.

Definition REFLEXIVITY_DENOTE (rtype : typ) {H: @RelDec.RelDec (typD rtype) eq}
{H0: RelDec.RelDec_Correct H} tbl : rtac typ (expr typ func) := 
   fun tus tvs lus lvs c s e => (
match e with
| (App (App (Inj (inr (Other (feq _)))) l) r) =>
  match reflect tbl nil nil l rtype, reflect tbl nil nil r rtype with
  | Some v1, Some v2 => if @RelDec.rel_dec _ eq H v1 v2 then Solved s else Fail
  | _, _ => Fail
  end
| _ => Fail
end).

Definition REFLEXIVITY_BOOL := REFLEXIVITY_DENOTE tybool.

Definition REFLEXIVITY_CEXPR := REFLEXIVITY_DENOTE tyc_expr.

Instance RelDec_op_ctypes_beq : @RelDec.RelDec (option Ctypes.type) eq :=
  Option.RelDec_eq_option RelDec_ctype_beq.

Instance RelDec_Correct_op_ctypes_beq : RelDec.RelDec_Correct RelDec_op_ctypes_beq :=
  Option.RelDec_Correct_eq_option RelDec_Correct_ctype_beq.

Definition REFLEXIVITY_OP_CTYPE := REFLEXIVITY_DENOTE (tyoption tyc_type).

End tbled.
