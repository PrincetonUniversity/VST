Require Import floyd.proofauto.
Require Import sep.
Import Sep.

(*Type definitions in this file are defined by us before reifier runs*)

Definition no_eqb_type : forall (t:Type), Expr.type.
intros.
refine ({| Expr.Impl := t
     ; Expr.Eqb := fun _ _ => false
     ; Expr.Eqb_correct := _ |}).
intros; inv H.
Defined.


Definition tycontext_type := no_eqb_type tycontext.

Definition c_expr_type := no_eqb_type tycontext.

Definition c_type_type := 
 ({| Expr.Impl := type
     ; Expr.Eqb := type_eq
     ; Expr.Eqb_correct := environ_lemmas.type_eq_true |}).

Definition environ_type : Expr.type := no_eqb_type environ.

Definition val_type : Expr.type := no_eqb_type val. 
(*TODO: might want equality here*)


Definition share_type : Expr.type := no_eqb_type share.

Definition ident_type :=
 ({| Expr.Impl := ident
     ; Expr.Eqb := Peqb
     ; Expr.Eqb_correct := Peqb_true_eq |}).

Definition list_val_type : Expr.type := no_eqb_type (list val).

Definition list_int_type := no_eqb_type (list int).

Definition int_type := no_eqb_type int.

Definition Z_type := no_eqb_type Z.

Definition nat_type := no_eqb_type nat.

Definition positive_type := no_eqb_type positive.

Definition bool_type := no_eqb_type bool.

Definition comparison_type := no_eqb_type comparison.

Module Type unknown_types.
Parameter (unknown_types : (list Expr.type)).
End unknown_types.

Module our_types (uk : unknown_types).
Import uk.

Definition our_types :=(cons tycontext_type
                       (cons c_expr_type 
                       (cons c_type_type 
                       (cons environ_type 
                       (cons val_type 
                       (cons share_type 
                       (cons ident_type
                       (cons list_val_type 
                       (cons list_int_type  
                       (cons int_type
                       (cons Z_type
                       (cons nat_type
                       (cons positive_type
                       (cons bool_type
                       (cons comparison_type nil
                       ))))))))))))))).

Definition all_types := our_types ++ unknown_types.


Definition tycontext_tv := Expr.tvType 0.
Definition c_expr_tv := Expr.tvType 1.
Definition c_type_tv := Expr.tvType 2.
Definition environ_tv := Expr.tvType 3.
Definition val_tv := Expr.tvType 4.
Definition share_tv := Expr.tvType 5.
Definition ident_tv := Expr.tvType 6.
Definition list_val_tv := Expr.tvType 7.
Definition list_int_tv := Expr.tvType 8.
Definition int_tv := Expr.tvType 9.
Definition Z_tv := Expr.tvType 10.
Definition nat_tv := Expr.tvType 11.
Definition positive_tv := Expr.tvType 12.
Definition bool_tv := Expr.tvType 13.
Definition comparison_tv := Expr.tvType 14.

(*Some common consts *)
Definition our_const tv val :=
@Expr.Const all_types tv val.

Definition share_const sh :=
  our_const share_tv sh.

Definition c_type_const ty :=
our_const c_type_tv ty.

Definition id_const id :=
our_const ident_tv id.

Definition val_const val :=
our_const val_tv val.

Definition environ_const rho :=
our_const environ_tv rho.

Definition list_int_const li :=
our_const list_int_tv li.

Definition prop_const p :=
our_const Expr.tvProp p.

Definition tycontext_const Delta :=
our_const tycontext_tv Delta.

End our_types.


