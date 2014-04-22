Require Import floyd.proofauto.
Require Import sep.
Require Import msl.Axioms.
Require Import val_eq.
Import Sep.

(*Type definitions in this file are defined by us before reifier runs*)

Definition no_eqb_type : forall (t:Type), Expr.type.
intros.
refine ({| Expr.Impl := t
     ; Expr.Eqb := fun _ _ => false
     ; Expr.Eqb_correct := _ |}).
abstract ( intros; inv H).
Defined.

Definition tycontext_type := no_eqb_type tycontext.


Definition c_type_type := 
 ({| Expr.Impl := type
     ; Expr.Eqb := eqb_type
     ; Expr.Eqb_correct := eqb_type_true |}).

Definition environ_type : Expr.type := no_eqb_type environ.

Definition val_type : Expr.type.
refine ({| Expr.Impl := val
         ; Expr.Eqb := beq_val
         ; Expr.Eqb_correct := beq_val_true |}).
Defined. 

Definition share_type : Expr.type := no_eqb_type share.

Definition ident_type :=
 ({| Expr.Impl := ident
     ; Expr.Eqb := Peqb
     ; Expr.Eqb_correct := Peqb_true_eq |}).

Definition list_val_type : Expr.type := no_eqb_type (list val).

Definition int_type : Expr.type.
  refine ({| Expr.Impl := int
             ; Expr.Eqb := beq_int
             ; Expr.Eqb_correct := beq_int_true |}).
Defined.

Definition list_int_type : Expr.type := list_eqb_type beq_int_true.

Definition Z_type :=
  ({| Expr.Impl := Z
      ; Expr.Eqb := Zeq_bool
      ; Expr.Eqb_correct := Zeq_bool_eq |}).

Definition nat_type := 
  ({| Expr.Impl := nat
      ; Expr.Eqb := beq_nat
      ; Expr.Eqb_correct := beq_nat_true |}).

Definition positive_type := 
  ({| Expr.Impl := positive
      ; Expr.Eqb := Pos.eqb
      ; Expr.Eqb_correct := Peqb_true_eq |}).

Definition bool_type := 
  ({| Expr.Impl := bool
      ; Expr.Eqb := eqb
      ; Expr.Eqb_correct := eqb_prop |}).

(* TODO fix this dependency problem more sanely *)
Require Import progs.list_dt.
Require Import progs.reverse.
Instance sample_ls: listspec t_struct_list _tail.
Proof. eapply mk_listspec; reflexivity. Defined.

Definition list_elemtype_sample_ls_type := no_eqb_type (list (elemtype sample_ls)).

(* equality for comparisons; apparently doesn't exist? *)
Definition eqb_comparison (c1 c2 : comparison) : bool :=
  match (c1, c2) with
    | (Ceq, Ceq) => true
    | (Cne, Cne) => true
    | (Clt, Clt) => true
    | (Cle, Cle) => true
    | (Cgt, Cgt) => true
    | (Cge, Cge) => true
    | _ => false
  end.

Definition comparison_type : Expr.type.
  refine ({| Expr.Impl := comparison
             ; Expr.Eqb := eqb_comparison
             ; Expr.Eqb_correct := _ |}).
  intros.
  destruct x; destruct y; inversion H; reflexivity.
Defined.

Definition c_expr_type := no_eqb_type expr.

Definition tc_assert_type := no_eqb_type tc_assert.

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
                       (cons comparison_type
                       (cons tc_assert_type
                       (cons list_elemtype_sample_ls_type nil
                       ))))))))))))))))).

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
Definition tc_assert_tv := Expr.tvType 15.
Definition list_elemtype_sample_ls_tv := Expr.tvType 16.