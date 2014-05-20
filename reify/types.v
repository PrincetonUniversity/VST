Require Import floyd.proofauto.
Require Import sep.
Require Import msl.Axioms.
Require Import val_eq.
Import Sep.
Import ListNotations.

(*Type definitions in this file are defined by us before reifier runs*)

Definition type_from_eq {T} {f : T -> T -> bool} (p : forall a b, f a b = true -> a=b) :=
{| Expr.Impl := T
   ; Expr.Eqb := f
   ; Expr.Eqb_correct := p |}.

Definition no_eqb_type : forall (t:Type), Expr.type.
intros.
refine ({| Expr.Impl := t
     ; Expr.Eqb := fun _ _ => false
     ; Expr.Eqb_correct := _ |}).
abstract ( intros; inv H).
Defined.

Definition tycontext_type := no_eqb_type tycontext.

Definition c_type_type := type_from_eq eqb_type_true.

Definition environ_type : Expr.type := no_eqb_type environ.

Definition val_type : Expr.type := type_from_eq beq_val_true.

Definition share_type : Expr.type := no_eqb_type share.

Definition ident_type := @type_from_eq ident _ Peqb_true_eq.

Definition list_val_type : Expr.type := no_eqb_type (list val).

Definition int_type := type_from_eq beq_int_true.

Definition int64_type :=type_from_eq beq_long_true.

Definition float_type := type_from_eq beq_float_dec_true.

Definition list_int_type : Expr.type := list_eqb_type beq_int_true.

Definition Z_type := type_from_eq Zeq_bool_eq.

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

Definition val_map_type  :=
no_eqb_type  (Z -> val).

Definition lift_prop_type :=
no_eqb_type (environ -> Prop).

Definition lift_mpred_type :=
no_eqb_type (environ -> mpred).

Definition attr_type : Expr.type.
refine
  ({| Expr.Impl := attr
      ; Expr.Eqb := eqb_attr
      ; Expr.Eqb_correct := _ |}).
intros. erewrite eqb_attr_spec in *. auto.
Defined.

Definition signedness_type : Expr.type.
refine {| Expr.Impl := signedness
          ; Expr.Eqb := eqb_signedness
       |}.
intros. erewrite eqb_signedness_spec in *. auto.
Defined.

Definition intsize_type : Expr.type.
refine {| Expr.Impl := intsize
          ; Expr.Eqb := eqb_intsize
       |}.
intros. erewrite eqb_intsize_spec in *. auto.
Defined.

Definition floatsize_type : Expr.type.
refine {| Expr.Impl := floatsize
          ; Expr.Eqb := eqb_floatsize
       |}.
intros. erewrite eqb_floatsize_spec in *. auto.
Defined.

Definition typelist_type := type_from_eq eqb_typelist_true.

Definition fieldlist_type := type_from_eq eqb_fieldlist_true.

Definition beq_binary_operation a b:= 
match a,b with
  | Oadd, Oadd 
  | Osub, Osub => true
  | Omul, Omul
  | Odiv, Odiv
  | Omod, Omod
  | Oand, Oand
  | Oor, Oor
  | Oxor, Oxor
  | Oshl, Oshl
  | Oshr, Oshr
  | Oeq, Oeq
  | One, One
  | Olt, Olt
  | Ogt, Ogt
  | Ole, Ole
  | Oge, Oge => true
  | _, _ => false
end.

Lemma beq_binary_operation_true a b : beq_binary_operation a b = true -> a=b.
destruct a; destruct b; simpl in *; congruence.
Qed.

Definition beq_unary_operation a b :=
  match a, b with
    | Onotbool, Onotbool | Onotint, Onotint | Oneg, Oneg  => true
    | _, _ => false 
end.

Lemma beq_unary_operation_true a b : beq_unary_operation a b = true -> a=b.
destruct a; destruct b; simpl in *; congruence.
Qed.


Definition binary_operation_type := type_from_eq beq_binary_operation_true.

Definition unary_operation_type := type_from_eq beq_unary_operation_true.

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

Definition beq_true {T} (beq : T -> T -> bool) :=
forall a b, beq a b = true -> a = b.

Definition beq_N n1 n2:=
match n1, n2 with
  |  N0, N0 => true
  | (Npos a), (Npos b)=> Pos.eqb a b
  | _, _ => false
end.

Lemma beq_N_true : beq_true beq_N.
hnf; intros.
destruct a, b; simpl in *; try congruence.
apply Peqb_true_eq in H. congruence.
Qed.

Definition N_type := type_from_eq beq_N_true.

Definition beq_option {T} f (a b : option T):=
match a, b with
    Some a', Some b' => f a' b'
  | None, None => true
  | _, _ => false
end.

Lemma beq_option_true {T} {f} (l : beq_true f) (a b :option T) : beq_option f a b = true -> a = b.
intros. destruct a; destruct b; simpl in *; try congruence.
unfold beq_true in l. apply l in H. auto.
Qed.

Definition option_N_type := type_from_eq (beq_option_true beq_N_true).

Definition val_mpred_type := no_eqb_type (val -> mpred).

Definition our_types :=[tycontext_type
;c_expr_type 
;c_type_type 
;environ_type 
;val_type 
;share_type 
;ident_type
;list_val_type 
;list_int_type  
;int_type
;Z_type
;nat_type
;positive_type
;bool_type
;comparison_type
;tc_assert_type 
;val_map_type 
;lift_prop_type 
;lift_mpred_type 
;int64_type 
;float_type 
;attr_type 
;signedness_type 
;intsize_type 
;floatsize_type
;typelist_type
;fieldlist_type
;binary_operation_type
;unary_operation_type
;N_type
;option_N_type
;val_mpred_type
].



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
Definition val_map_tv := Expr.tvType 16.
Definition lift_prop_tv := Expr.tvType 17.
Definition lift_mpred_tv := Expr.tvType 18.
Definition int64_tv := Expr.tvType 19.
Definition float_tv := Expr.tvType 20.
Definition attr_tv := Expr.tvType 21.
Definition signedness_tv := Expr.tvType 22. 
Definition intsize_tv := Expr.tvType 23.
Definition floatsize_tv := Expr.tvType 24.
Definition typelist_tv := Expr.tvType 25.
Definition fieldlist_tv := Expr.tvType 26.
Definition binary_operation_tv := Expr.tvType 27.
Definition unary_operation_tv := Expr.tvType 28.
Definition N_tv := Expr.tvType 29.
Definition option_N_tv := Expr.tvType 30.
Definition val_mpred_tv := Expr.tvType 31.