Require Import types.
Require Import floyd.proofauto.
Require Import sep.
Require Import progs.list_dt.
Require Import MirrorShard.Expr.


Definition tc_environ_signature :=
Expr.Sig all_types (cons tycontext_tv (cons environ_tv nil)) tvProp tc_environ.

Definition eq_val_signature :=
Expr.Sig all_types (cons val_tv (cons val_tv nil))
tvProp (@eq val).


Definition force_ptr_signature := 
Expr.Sig all_types (cons val_tv nil) val_tv
force_ptr.

Definition app_val_signature :=
Expr.Sig all_types (cons list_val_tv (cons list_val_tv nil))
list_val_tv (@app val).

Definition eval_id_signature :=
Expr.Sig all_types (cons ident_tv (cons environ_tv nil))
val_tv eval_id.

Definition and_signature :=
Expr.Sig all_types (cons tvProp (cons tvProp nil))
tvProp and.

Definition eq_list_val_signature :=
Expr.Sig all_types (cons list_val_tv (cons list_val_tv nil))
tvProp (@eq (list val)).

Definition align_signature :=
Expr.Sig all_types (Z_tv :: Z_tv :: nil) Z_tv align.

Definition cons_val_signature :=
Expr.Sig all_types (cons val_tv (cons list_val_tv nil))
list_val_tv (@cons val).

Definition make_environ_signature (rho:environ) :=
Expr.Sig all_types nil environ_tv rho.

Definition make_share_signature (sh : share) :=
Expr.Sig all_types nil share_tv sh.

Definition make_list_int_signature (li :list int) :=
Expr.Sig all_types nil list_int_tv li.

Definition make_int_signature i :=
Expr.Sig all_types nil int_tv i.

Definition make_val_signature v :=
Expr.Sig all_types nil val_tv v.

Definition int_sub_signature :=
Expr.Sig all_types (int_tv :: int_tv :: nil) int_tv Int.sub.

Definition Vint_signature :=
Expr.Sig all_types (int_tv :: nil) val_tv Vint.

Definition map_Vint_signature := 
Expr.Sig all_types (list_int_tv :: nil) list_val_tv (map Vint).

Definition typed_true_signature :=
Expr.Sig all_types (c_type_tv :: val_tv :: nil) tvProp typed_true.

Definition int_add_signature :=
Expr.Sig all_types (int_tv :: int_tv :: nil) int_tv Int.add.

Definition O_signature :=
Expr.Sig all_types nil nat_tv O.

Definition S_signature :=
Expr.Sig all_types (nat_tv :: nil) nat_tv S.

Definition Z_lt_signature :=
Expr.Sig all_types (Z_tv :: Z_tv :: nil) tvProp Z.lt.

Definition Z_le_signature :=
Expr.Sig all_types (Z_tv :: Z_tv :: nil) tvProp Z.le.

Definition Z_gt_signature :=
Expr.Sig all_types (Z_tv :: Z_tv :: nil) tvProp Z.gt.

Definition Z_ge_signature :=
Expr.Sig all_types (Z_tv :: Z_tv :: nil) tvProp Z.ge.

Definition Zpos_signature :=
Expr.Sig all_types (positive_tv :: nil) Z_tv Zpos.

Definition Zneg_signature :=
Expr.Sig all_types (positive_tv :: nil) Z_tv Zneg.

Definition Z0_signature :=
Expr.Sig all_types nil Z_tv Z0.

Definition xI_signature :=
Expr.Sig all_types (positive_tv :: nil) positive_tv xI.

Definition xO_signature :=
Expr.Sig all_types (positive_tv :: nil) positive_tv xO.

Definition xH_signature :=
Expr.Sig all_types nil positive_tv xH.

Definition int_lt_signature :=
Expr.Sig all_types (int_tv :: int_tv :: nil) bool_tv Int.lt.

Definition int_ltu_signature :=
Expr.Sig all_types (int_tv :: int_tv :: nil) bool_tv Int.ltu.

Definition int_mul_signature :=
Expr.Sig all_types (int_tv :: int_tv :: nil) int_tv Int.mul.

Definition int_neg_signature :=
Expr.Sig all_types (int_tv :: nil) int_tv Int.neg.

Definition Z_add_signature :=
Expr.Sig all_types (Z_tv :: Z_tv :: nil) Z_tv Z.add.

Definition Z_sub_signature :=
Expr.Sig all_types (Z_tv :: Z_tv :: nil) Z_tv Z.sub.

Definition Z_mul_signature :=
Expr.Sig all_types (Z_tv :: Z_tv :: nil) Z_tv Z.mul.

Definition Z_div_signature :=
Expr.Sig all_types (Z_tv :: Z_tv :: nil) Z_tv Z.div.

Definition Z_mod_signature :=
Expr.Sig all_types (Z_tv :: Z_tv :: nil) Z_tv Zmod.

Definition Z_max_signature :=
Expr.Sig all_types (Z_tv :: Z_tv :: nil) Z_tv Z.max.

Definition Z_opp_signature :=
Expr.Sig all_types (Z_tv :: nil) Z_tv Z.opp.

Definition Ceq_signature :=
Expr.Sig all_types nil comparison_tv Ceq.

Definition Cne_signature :=
Expr.Sig all_types nil comparison_tv Cne.

Definition Clt_signature :=
Expr.Sig all_types nil comparison_tv Clt.

Definition Cle_signature :=
Expr.Sig all_types nil comparison_tv Cle.

Definition Cgt_signature :=
Expr.Sig all_types nil comparison_tv Cgt.

Definition Cge_signature :=
Expr.Sig all_types nil comparison_tv Cge.

Definition int_cmp_signature :=
Expr.Sig all_types (comparison_tv :: int_tv :: int_tv :: nil) bool_tv Int.cmp.

Definition int_cmpu_signature :=
Expr.Sig all_types (comparison_tv :: int_tv :: int_tv :: nil) bool_tv Int.cmpu.

Definition int_repr_signature :=
Expr.Sig all_types (Z_tv :: nil) int_tv Int.repr.

Definition int_signed_signature :=
Expr.Sig all_types (int_tv :: nil) Z_tv Int.signed.

Definition int_unsigned_signature :=
Expr.Sig all_types (int_tv :: nil) Z_tv Int.unsigned.

Definition two_power_nat_signature :=
Expr.Sig all_types (nat_tv :: nil) Z_tv two_power_nat.

Definition int_max_unsigned_signature :=
Expr.Sig all_types nil Z_tv Int.max_unsigned.

Definition True_signature :=
Expr.Sig all_types nil tvProp True.

(* Our types. Let's see which of these we want to have equalities for *)
(*
                       (cons val_type done
                       (cons list_val_type done
                       (cons list_int_type  
                       (cons int_type
                       (cons Z_type
                       (cons nat_type
                       (cons positive_type
                       (cons bool_type
                       (cons comparison_type nil
                       ))))))))))))))).
*)

(* This way we don't have to deal with tons of close-parens at the end 
 * Important, since functions is a long list. *)
Import ListNotations.

Definition computable_functions :=
[ two_power_nat_signature 
; O_signature
; force_ptr_signature
; app_val_signature
; int_max_unsigned_signature 
; and_signature
; align_signature
; cons_val_signature 
; int_sub_signature 
; Vint_signature 
; map_Vint_signature 
; typed_true_signature 
; int_add_signature
; S_signature
; Z_lt_signature
; Z_le_signature
; Z_gt_signature
; Z_ge_signature
; Zpos_signature
; Zneg_signature
; Z0_signature
; xI_signature
; xO_signature
; xH_signature
; int_lt_signature
; int_ltu_signature
; int_mul_signature
; int_neg_signature
; Z_add_signature
; Z_sub_signature
; Z_mul_signature
; Z_div_signature
; Z_mod_signature
; Z_max_signature
; Z_opp_signature
; Ceq_signature
; Cne_signature
; Clt_signature
; Cle_signature
; Cgt_signature
; Cge_signature
; int_cmp_signature
; int_cmpu_signature
; int_repr_signature
; int_signed_signature
; int_unsigned_signature
].

Definition non_computable_functions :=
[ tc_environ_signature
; eval_id_signature
; True_signature
].

Definition functions := computable_functions ++ non_computable_functions.
Definition computable_prefix_length := length computable_functions.

Definition two_power_nat_f := 0%nat.
Definition O_f := 1%nat.
Definition force_ptr_f := 2%nat.
Definition app_val_f := 3%nat.
Definition int_max_unsigned_f := 4%nat.
Definition and_f := 5%nat.
Definition align_f := 6%nat.
Definition cons_val_f := 7%nat.
Definition int_sub_f := 8%nat.
Definition vint_f := 9%nat.
Definition map_Vint_f := 10%nat.
Definition typed_true_f := 11%nat.
Definition int_add_f := 12%nat.
Definition S_f := 13%nat.
Definition Z_lt_f := 14%nat.
Definition Z_le_f := 15%nat.
Definition Z_gt_f := 16%nat.
Definition Z_ge_f := 17%nat.
Definition Zpos_f := 18%nat.
Definition Zneg_f := 19%nat.
Definition Z0_f := 20%nat.
Definition xI_f := 21%nat.
Definition xO_f := 22%nat.
Definition xH_f := 23%nat.
Definition int_lt_f := 24%nat.
Definition int_ltu_f := 25%nat.
Definition int_mul_f := 26%nat.
Definition int_neg_f := 27%nat.
Definition Z_add_f := 28%nat.
Definition Z_sub_f := 29%nat.
Definition Z_mul_f := 30%nat.
Definition Z_div_f := 31%nat.
Definition Z_mod_f := 32%nat.
Definition Z_max_f := 33%nat.
Definition Z_opp_f := 34%nat.
Definition Ceq_f := 35%nat.
Definition Cne_f := 36%nat.
Definition Clt_f := 37%nat.
Definition Cle_f := 38%nat.
Definition Cgt_f := 39%nat.
Definition Cge_f := 40%nat.
Definition int_cmp_f := 41%nat.
Definition int_cmpu_f := 42%nat.
Definition int_repr_f := 43%nat.
Definition int_signed_f := 44%nat.
Definition int_unsigned_f := 45%nat.

(* Past this point are functions that should not compute into Consts *)
Definition tc_environ_f := length computable_functions.
Definition eval_id_f := S (tc_environ_f).
Definition True_f := S (eval_id_f).


(*Separation Logic predicates *)
Definition field_at_f :=
Sep.PSig all_types (share_tv :: c_type_tv :: ident_tv :: val_tv :: val_tv :: nil)
field_at.

Definition sep_predicates : list (Sep.predicate all_types) := field_at_f :: nil.

Definition field_at_p := 0%nat.

(*functions to build Exprs *)
Definition eval_id_func id rho :=
@Expr.Func all_types eval_id_f 
(cons id (cons rho nil)).

(* Definition val_eq v1 v2 :=
@Expr.Func all_types eq_val_f (cons v1 (cons v2 nil)). *)

Definition and_func p1 p2 :=
@Expr.Func all_types and_f (cons p1 (cons p2 nil)).

Definition nullary_func f :=
@Expr.Func all_types f nil.

Definition vint_func i :=
@Expr.Func all_types vint_f (i :: nil).

Definition int_sub_func i1 i2 :=
@Expr.Func all_types int_sub_f (i1 :: i2 :: nil).

Definition int_add_func i1 i2 :=
@Expr.Func all_types int_add_f (i1 :: i2 :: nil).


Definition tc_environ_func delta rho :=
@Expr.Func all_types tc_environ_f (delta :: rho :: nil).

Definition map_vint_func i :=
@Expr.Func all_types map_Vint_f (i :: nil).

Definition typed_true_func t v :=
@Expr.Func all_types typed_true_f (t :: v :: nil).

Definition field_at_func sh ty id v1 v2:= @Sep.Func all_types field_at_p
(sh :: ty :: id :: v1 :: v2 :: nil).

