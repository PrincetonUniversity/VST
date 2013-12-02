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

Definition functions :=
 cons tc_environ_signature
(cons eq_val_signature
(cons force_ptr_signature
(cons app_val_signature
(cons eval_id_signature
(cons and_signature
(cons eq_list_val_signature
(cons cons_val_signature nil
))))))).

Definition tc_environ_f := 0%nat.
Definition eq_val_f := 1%nat.
Definition force_ptr_f := 2%nat.
Definition app_val_f := 3%nat.
Definition eval_id_f := 4%nat.
Definition and_f := 5%nat.
Definition eq_list_val_f := 6%nat.
Definition cons_val_f := 7%nat.

(*Separation Logic predicates *)
Definition sep_predicates : list (Sep.predicate all_types) := nil.

(*Some common functions *)
Definition eval_id_func id rho :=
@Expr.Func all_types eval_id_f 
(cons id (cons rho nil)).

Definition val_eq v1 v2 :=
@Expr.Func all_types eq_val_f (cons v1 (cons v2 nil)).

Definition and_func p1 p2 :=
@Expr.Func all_types and_f (cons p1 (cons p2 nil)).

Definition nullary_func f :=
@Expr.Func all_types f nil.


End funcs.
