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
(* but we might have to define it ourselves... *)


Definition share_type : Expr.type := no_eqb_type share.

Definition ident_type :=
 ({| Expr.Impl := ident
     ; Expr.Eqb := Peqb
     ; Expr.Eqb_correct := Peqb_true_eq |}).

Definition list_val_type : Expr.type := no_eqb_type (list val).

Definition int_type : Expr.type.
  refine ({| Expr.Impl := int
             ; Expr.Eqb := Int.eq
             ; Expr.Eqb_correct := _ |}).
  (* have to reverse arguments to this lemma *)
  intros. symmetry in H. apply binop_lemmas.int_eq_true in H.
  assumption.
Defined.

(* Generic equality procedure for lists of things *)
(* I'll do this later if it looks like it will actually be necessary *)
(*Fixpoint lists_exact_zip (T1 T2 T3 : Type)
         (f : T1 -> T2 -> T3) (l1 : list T1) (l2 : list T2) : option T3 := 
match l1 with
  | h1
  | (cons h1 t1) =>
    match l2 with
      | (cons h2 t2) =>
        (cons (f h1 h2) (lists_exact_zip T1 T2 T3 f t1 t2))
      | nil => nil
    end
  | nil => nil
end.

Definition make_list_eqb (T : Type) (beq : (T -> T -> bool)) (l1 l2 : list T) : bool :=
  let each_equal := lists_zip T T bool beq l1 l2 in
  fold_right andb true each_equal.
*)
Fixpoint beq_list_int (l1 l2 : list int) : bool :=
  match l1 with
    | nil => 
      match l2 with
        | nil => true
        | _ => false
      end
    | (cons h1 t1) =>
      match l2 with
        | nil => false
        | (cons h2 t2) =>
          (andb (Int.eq h1 h2) (beq_list_int t1 t2))
      end
  end.  

Definition list_int_type : Expr.type.
  refine ({| Expr.Impl := list int
             ; Expr.Eqb := beq_list_int
             ; Expr.Eqb_correct := _ |}).
  intro x. induction x.
  - intros.
    destruct y.
    + reflexivity.
    + inversion H.
  - intros.
    destruct y.
    + inversion H.
    + inversion H.
      symmetry in H1.
      apply andb_true_eq in H1. inversion H1.
      symmetry in H2.
      apply IHx in H2. 
      symmetry in H0.
      apply int_eq_e in H0.
      rewrite H0. rewrite H2. reflexivity.
Defined.

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


