Require Import ExtLib.Data.Positive.
Require Import funcs.
Require Import typ_eq.
Require Import statement_eq.
Require Import Coq.Arith.EqNat.
Require Import clight_expr_eq.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.List.
Require Import ExtLib.Core.RelDec.

Definition const_beq a b :=
match a, b with
| N c1, N c2 => beq_nat c1 c2
| Z c1, Z c2 => Zbool.Zeq_bool c1 c2
| Pos c1, Pos c2 =>  BinPos.Pos.eqb c1 c2
| Ctype c1, Ctype c2 => expr.eqb_type c1 c2
| Cexpr c1, Cexpr c2 => expr_beq c1 c2
| _, _ => false
end.


Definition beq_z_true : forall a b, Zbool.Zeq_bool a b = true -> a = b.
Proof.
intros. apply Zbool.Zeq_bool_eq in H. subst.
auto.
Qed.

Hint Resolve beq_nat_true : expr_beq.
Hint Resolve beq_z_true : expr_beq.

Lemma const_beq_sound : forall a b, const_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound. 
Qed.

Hint Resolve const_beq_sound : expr_beq.

Definition z_op_beq a b : bool := 
match a, b with
| fZ_lt, fZ_lt 
| fZ_le, fZ_le 
| fZ_gt, fZ_gt 
| fZ_ge, fZ_ge 
| fZ_add, fZ_add 
| fZ_sub, fZ_sub 
| fZ_mul, fZ_mul 
| fZ_div, fZ_div 
| fZ_mod, fZ_mod 
| fZ_max, fZ_max 
| fZ_opp, fZ_opp  => true
| _, _ => false
end.

Hint Resolve beq_nat_true : expr_beq.

Lemma z_op_beq_sound : forall a b, z_op_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound. 
Qed.

Hint Resolve z_op_beq_sound : expr_beq.

Definition int_op_beq a b : bool :=
match a, b with
| fint_add, fint_add 
| fint_lt, fint_lt 
| fint_ltu, fint_ltu 
| fint_mul, fint_mul 
| fint_neg, fint_neg 
| fint_sub, fint_sub 
| fint_cmp, fint_cmp 
| fint_cmpu, fint_cmpu 
| fint_repr, fint_repr 
| fint_signed, fint_signed 
| fint_unsigned, fint_unsigned 
| fint_max_unsigned, fint_max_unsigned 
| fint64_repr, fint64_repr => true
| _, _ => false
end.

Lemma int_op_beq_sound : forall a b, int_op_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound. 
Qed.

Hint Resolve int_op_beq_sound : expr_beq.

Definition values_beq a b:=
match a, b with
| fVint, fVint 
| fVfloat, fVfloat 
| fVlong, fVlong 
| fVptr, fVptr 
| fVundef, fVundef => true
| _, _ => false
end. 


Lemma values_beq_sound : forall a b, values_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound. 
Qed.

Hint Resolve values_beq_sound : expr_beq.

Definition eval_beq a b :=
match a,b with 
| feval_cast, feval_cast 
| fderef_noload, fderef_noload 
| feval_field, feval_field 
| feval_binop, feval_binop 
| feval_unop, feval_unop 
| feval_id, feval_id => true
| _, _ => false
end. 

Lemma eval_beq_sound : forall a b, eval_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound. 
Qed.

Hint Resolve eval_beq_sound : expr_beq.

Definition other_beq a b :=
match a, b with
| ftwo_power_nat, ftwo_power_nat 
| fforce_ptr, fforce_ptr 
| fand, fand 
| falign, falign 
| ftyped_true, ftyped_true => true 
| feq t1, feq t2 => typ_beq t1 t2
| _, _ => false
end
.

Hint Resolve typ_beq_sound : expr_beq.

Lemma other_beq_sound : forall a b, other_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound. 
Qed.

Hint Resolve other_beq_sound : expr_beq.


Definition lst_beq a b :=
match a, b with
| fnil t1, fnil t2
| fcons t1, fcons t2
| fappend t1, fappend t2 => typ_beq t1 t2
| fmap ta1 tb1, fmap ta2 tb2 
| ffold_right ta1 tb1, ffold_right ta2 tb2 
| ffold_left ta1 tb1, ffold_left ta2 tb2 => andb (typ_beq ta1 ta2) (typ_beq tb1 tb2)
| _ , _ => false
end.

Lemma lst_beq_sound : forall a b, lst_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound. 
Qed.

Hint Resolve lst_beq_sound : expr_beq.

Definition sep_beq a b :=
match a, b with
| flocal, flocal 
| fprop, fprop => true
| fdata_at ty1, fdata_at ty2 => expr.eqb_type ty1 ty2
| ffield_at ty1 li1, ffield_at ty2 li2 => andb (expr.eqb_type ty1 ty2) 
                                               (li1 ?[eq] li2)
| flseg t1 i1 _, flseg t2 i2 _ => andb (expr.eqb_type t1 t2) (BinPos.Pos.eqb i1 i2)
| _, _ => false
end 
.

Lemma sep_beq_sound : forall a b, sep_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound. SearchAbout rel_dec.
rewrite (rel_dec_correct) in H0. auto.
assert (t = t0) by auto with expr_beq.
assert (i = i0) by auto with expr_beq.
assert (X := types.listspec_ext). subst.
 specialize (X t0 i0 l l0).
subst; auto.
Qed.

Hint Resolve sep_beq_sound : expr_beq.



Definition triple_beq a b :=
match a, b with
| fsemax, fsemax
| fPROPx, fPROPx
| fLOCALx, fLOCALx
| fSEPx, fSEPx
| fnormal_ret_assert, fnormal_ret_assert => true
| flocalD _ _ _ , _=> false (*TODO*)
| fstatement s1, fstatement s2 => statement_beq s1 s2
| ftycontext _, ftycontext _ => false
| _, _ => false
end.

Hint Resolve statement_beq_sound : expr_beq.

Lemma triple_beq_sound : forall a b, triple_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound. 
Qed.

Hint Resolve triple_beq_sound : expr_beq.

Definition func_beq a b :=
match a, b with
| Const f1, Const f2 => const_beq f1 f2
| Zop f1, Zop f2 => z_op_beq f1 f2
| Intop f1, Intop f2 => int_op_beq f1 f2
| Value f1, Value f2 => values_beq f1 f2
| Eval_f f1, Eval_f f2 => eval_beq f1 f2
| Other f1, Other f2 => other_beq f1 f2
| Sep f1, Sep f2 => sep_beq f1 f2
| Lst f1, Lst f2 => lst_beq f1 f2
| Triple f1, Triple f2 => triple_beq f1 f2
| _, _ => false
end.

Lemma func_beq_sound : forall a b, func_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound. 
Qed.

Hint Resolve lst_beq_sound : expr_beq.
