Require Import ExtLib.Data.Positive.
Require Import mc_reify.funcs.
Require Import mc_reify.typ_eq.
Require Import mc_reify.statement_eq.
Require Import Coq.Arith.EqNat.
Require Import mc_reify.clight_expr_eq.
Require Import mc_reify.list_ctype_eq.
Require Import mc_reify.list_efield_eq.
Require Import ExtLib.Tactics.
Require Import ExtLib.Data.List.
Require Import ExtLib.Core.RelDec.

Fixpoint ptree_cmp {T : Type} (p1 p2: Maps.PTree.tree T)
         (e : T -> T -> bool) :=
match p1, p2 with
| Maps.PTree.Leaf, Maps.PTree.Leaf => true
| Maps.PTree.Node l1 i1 r1, Maps.PTree.Node l2 i2 r2 =>
  match i1, i2 with
    | Some v1, Some v2 => andb (e v1 v2)
                               (andb (ptree_cmp l1 l2 e)
                                     (ptree_cmp r1 r2 e))
    | None, None => (andb (ptree_cmp l1 l2 e)
                          (ptree_cmp r1 r2 e))
    | _, _ => false
  end
| _, _ => false
end.

Lemma ptree_cmp_sound : forall T p1 p2 e,
(forall (i1 i2 : T), e i1 i2 = true -> i1 = i2) ->
ptree_cmp p1 p2 e = true ->
p1 = p2.
Proof.
intros.
generalize dependent p2. induction p1; intros; destruct p2; auto;
simpl in *; try congruence.
destruct o, o0. simpl in *.
consider (e t t0); intros. specialize (H _ _ H0).
 subst.
consider (ptree_cmp p1_1 p2_1 e); intros.
apply IHp1_1 in H. apply IHp1_2 in H1. subst.
auto.
simpl in *; congruence.
simpl in *; congruence.
congruence. congruence.
consider (ptree_cmp p1_1 p2_1 e); intros.
apply IHp1_1 in H0. apply IHp1_2 in H1.
subst; auto.
simpl in *; congruence.
Qed.

Definition const_beq a b :=
match a, b with
| fN c1, fN c2 => beq_nat c1 c2
| fZ c1, fZ c2 => Zbool.Zeq_bool c1 c2
| fPos c1, fPos c2 =>  BinPos.Pos.eqb c1 c2
| fCtype c1, fCtype c2 => expr.eqb_type c1 c2
| fCexpr c1, fCexpr c2 => expr_beq c1 c2
| fenv c1, fenv c2 => ptree_cmp c1 c2 expr.eqb_type
| fllrr c1, fllrr c2 => match c1, c2 with | efield_lemmas.LLLL, efield_lemmas.LLLL | efield_lemmas.RRRR, efield_lemmas.RRRR => true | _, _ => false end
| _, _ => false
end.

Instance const_rel_dec : RelDec (@eq const) := { rel_dec := const_beq }.

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
+ eapply ptree_cmp_sound; [| exact H].
  intros; solve_expr_beq_sound.
+ destruct l, l0; try inversion H; reflexivity.
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
| fZ_land, fZ_land
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
| fint_and, fint_and
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
| feval_cast t1_1 t2_1 , feval_cast t1_2 t2_2 => andb (expr.eqb_type t1_1 t1_2)
                                                      (expr.eqb_type t2_1 t2_2)
| fderef_noload t1, fderef_noload t2 => expr.eqb_type t1 t2
| feval_field t1 id1 , feval_field t2 id2 =>  andb (expr.eqb_type t1 t2)
                                                   (BinPos.Pos.eqb id1 id2)
| feval_binop op1 t1_1 t2_1, feval_binop op2 t1_2 t2_2 =>
              andb (andb (binary_op_beq op1 op2)
                   (expr.eqb_type t1_1 t1_2))
                   (expr.eqb_type t2_1 t2_2)
| feval_unop op1 t1 , feval_unop op2 t2 =>
              andb (unary_op_beq op1 op2)
                   (expr.eqb_type t1 t2)
| feval_id id1, feval_id id2 => BinPos.Pos.eqb id1 id2
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
| fnone t1, fnone t2
| fsome t1, fsome t2
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


Definition data_beq a b :=
match a, b with
| fnil t1, fnil t2
| fcons t1, fcons t2
| fappend t1, fappend t2 => typ_beq t1 t2
| fnth_error t1 n1, fnth_error t2 n2
| freplace_nth t1 n1, freplace_nth t2 n2 => andb (beq_nat n1 n2) (typ_beq t1 t2)
| fmap ta1 tb1, fmap ta2 tb2
| ffold_right ta1 tb1, ffold_right ta2 tb2
| ffold_left ta1 tb1, ffold_left ta2 tb2 => andb (typ_beq ta1 ta2) (typ_beq tb1 tb2)
| fleaf t, fleaf t'
| fnode t, fnode t'
| fempty t, fempty t' => typ_beq t t'
| _ , _ => false
end.

Lemma data_beq_sound : forall a b, data_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound.
Qed.

Hint Resolve data_beq_sound : expr_beq.

Definition sep_beq a b :=
match a, b with
| flocal, flocal
| fprop, fprop => true
| fdata_at ty1, fdata_at ty2 => expr.eqb_type ty1 ty2
| fproj_val ty1, fproj_val ty2 => expr.eqb_type ty1 ty2
| fupd_val ty1, fupd_val ty2 => expr.eqb_type ty1 ty2
(*| ffield_at ty1 li1, ffield_at ty2 li2 => andb (expr.eqb_type ty1 ty2)
                                               (li1 ?[eq] li2)
| flseg t1 i1 _, flseg t2 i2 _ => andb (expr.eqb_type t1 t2) (BinPos.Pos.eqb i1 i2)*)
| _, _ => false
end
.

Lemma sep_beq_sound : forall a b, sep_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound.
Qed. (*
rewrite (rel_dec_correct) in H0. auto.
assert (t = t0) by auto with expr_beq.
assert (i = i0) by auto with expr_beq.
assert (X := types.listspec_ext). subst.
 specialize (X t0 i0 l l0).
subst; auto.
Qed. *)

Hint Resolve sep_beq_sound : expr_beq.

Definition type_bool_eq (a b : Ctypes.type * bool) :=
match a, b with
| (t1, b1), (t2, b2) => andb (expr.eqb_type t1 t2)
                             match b1, b2 with
                               | true, true | false, false => true
                               | _, _ => false
                             end
end.

Definition type_bool_eq_sound : forall a b,
type_bool_eq a b = true-> a = b.
intros. destruct a, b.
solve_expr_beq_sound.
destruct b, b0; simpl in H0; congruence.
Qed.

Definition smx_beq a b :=
match a, b with
| fsemax, fsemax
| fnormal_ret_assert, fnormal_ret_assert
| fassertD, fassertD => true
| flocalD , flocalD => true
| fstatement s1, fstatement s2 => statement_beq s1 s2
| ftycontext t1 l1 r1 gt1, ftycontext t2 l2 r2 gt2  =>
  andb (ptree_cmp t1 t2 type_bool_eq)
       (andb (ptree_cmp l1 l2 expr.eqb_type)
             (andb (expr.eqb_type r1 r2)
                   (ptree_cmp gt1 gt2 expr.eqb_type)))
| flater, flater => true
| flater_lift, flater_lift => true
| fnested_field_type2, fnested_field_type2 => true
| fis_neutral_cast, fis_neutral_cast => true
| fmsubst_efield_denote efs1, fmsubst_efield_denote efs2 => list_eqb RelDec_efield_beq efs1 efs2
| flegal_nested_efield tts1, flegal_nested_efield tts2 => list_eqb RelDec_ctype_beq tts1 tts2
| fmsubst_eval_LR, fmsubst_eval_LR => true
| ftc_LR_b_norho, ftc_LR_b_norho => true
| ftc_environ, ftc_environ => true
| ftc_efield_b_norho efs1, ftc_efield_b_norho efs2 => list_eqb RelDec_efield_beq efs1 efs2
| fnested_efield, fnested_efield => true
| ftypeof_temp, ftypeof_temp => true
| ftc_val, ftc_val => true
| flegal_nested_field, flegal_nested_field => true
| fstruct_field, fstruct_field => true
| funion_field, funion_field => true
| farray_subsc, farray_subsc => true
| fwritable_share, fwritable_share => true
| fTsh, fTsh => true
| fEws, fEws => true
| ftype_is_by_value, ftype_is_by_value => true
| _, _ => false
end.

Hint Resolve statement_beq_sound : expr_beq.

Lemma smx_beq_sound : forall a b, smx_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound.
apply ptree_cmp_sound in H; auto.
intros. apply type_bool_eq_sound in H3. auto.
apply ptree_cmp_sound in H0;
solve_expr_beq_sound.
apply ptree_cmp_sound in H2;
solve_expr_beq_sound.
Qed.

Hint Resolve smx_beq_sound : expr_beq.

Definition func_beq a b :=
match a, b with
| Const f1, Const f2 => const_beq f1 f2
| Zop f1, Zop f2 => z_op_beq f1 f2
| Intop f1, Intop f2 => int_op_beq f1 f2
| Value f1, Value f2 => values_beq f1 f2
| Eval_f f1, Eval_f f2 => eval_beq f1 f2
| Other f1, Other f2 => other_beq f1 f2
| Sep f1, Sep f2 => sep_beq f1 f2
| Data f1, Data f2 => data_beq f1 f2
| Smx f1, Smx f2 => smx_beq f1 f2
| _, _ => false
end.

Lemma func_beq_sound : forall a b, func_beq a b = true -> a = b.
Proof.
intros.
destruct a, b; auto; solve_expr_beq_sound.
Qed.

Hint Resolve data_beq_sound : expr_beq.
