Require Import types.
Require Import floyd.proofauto.
Require Import sep.
Require Import progs.list_dt.
Require Import MirrorShard.Expr.

Module funcs (uk : unknown_types).
Import uk.

Module ut_module <: unknown_types.
Definition unknown_types := unknown_types.
End ut_module.

Module all_types := our_types ut_module.
Import all_types.

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

Check typed_true.

Definition typed_true_signature :=
Expr.Sig all_types (c_type_tv :: val_tv :: nil) tvProp typed_true.

Definition int_add_signature :=
Expr.Sig all_types (int_tv :: int_tv :: nil) int_tv Int.add.



Definition functions :=
 cons tc_environ_signature
(cons eq_val_signature
(cons force_ptr_signature
(cons app_val_signature
(cons eval_id_signature
(cons and_signature
(cons eq_list_val_signature
(cons cons_val_signature 
(cons int_sub_signature 
(cons Vint_signature 
(cons map_Vint_signature 
(cons typed_true_signature 
(cons int_add_signature nil
)))))))))))).

Definition tc_environ_f := 0%nat.
Definition eq_val_f := 1%nat.
Definition force_ptr_f := 2%nat.
Definition app_val_f := 3%nat.
Definition eval_id_f := 4%nat.
Definition and_f := 5%nat.
Definition eq_list_val_f := 6%nat.
Definition cons_val_f := 7%nat.
Definition int_sub_f := 8%nat.
Definition vint_f := 9%nat.
Definition map_Vint_f := 10%nat.
Definition typed_true_f := 11%nat.
Definition int_add_f := 12%nat.

Check field_at.
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

Definition val_eq v1 v2 :=
@Expr.Func all_types eq_val_f (cons v1 (cons v2 nil)).

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


End funcs.
