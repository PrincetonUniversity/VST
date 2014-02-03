Require Import ssreflect ssrbool ssrnat ssrfun eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import JMeq.

(* This file defines cast operations and lemmas useful for doing rewrites *)
(* in dependent types.                                                    *)

Definition cast_ty (T1 T2 : Type) (pf : T1=T2) : T1 -> T2 :=
  eq_rect_r (fun y : Type => y -> T2) id pf.

Lemma cast_ty_erefl T1 (x : T1) : cast_ty (erefl T1) x = x.
Proof. by rewrite/cast_ty. Qed.

Lemma cast_ty_JMeq T1 T2 (pf : T1=T2) (x : T1) : JMeq (cast_ty pf x) x.
Proof. by rewrite <-pf; rewrite -(cast_ty_erefl x). Qed.

Section lift.

Variable A : Type.
Variable lift_ty : A -> Type.

Lemma lift_eq i j (pf : i = j) : lift_ty i = lift_ty j.
Proof. by elim: pf. Defined.

End lift.

Section ind.

Variable T : Type -> Type.
Variables A B : Type.
Variable P : forall A : Type, T A -> Type.

Lemma cast_ind (x : T A) (eq : A=B) (pf : P x) : P (cast_ty (lift_eq T eq) x).
Proof. by rewrite <-eq; rewrite (cast_ty_erefl x). Qed.

Lemma cast_ind' (x : T A) (eq : A=B) (pf : P (cast_ty (lift_eq T eq) x)) : P x.
Proof. 
by move: pf; rewrite <-eq; rewrite (cast_ty_erefl x). 
Qed.

End ind.

Section ind_natdep.

Variable N : nat.
Variable T : 'I_N -> Type.
Variables i j : 'I_N.
Variable P : forall i : 'I_N, T i -> Type.

Lemma cast_indnatdep
  (x : T i) (eq : i=j) (pf : P x) : P (cast_ty (lift_eq T eq) x).
Proof. by rewrite <-eq; rewrite (cast_ty_erefl x). Qed.

Lemma cast_indnatdep'
  (x : T i) (eq : i=j) (pf : P (cast_ty (lift_eq T eq) x)) : P x.
Proof. 
by move: pf; rewrite <-eq; rewrite (cast_ty_erefl x). 
Qed.

End ind_natdep.

Section ind_natdep2.

Variable N : nat.
Variables T : 'I_N -> Type.
Variables i j : 'I_N.
Variable P : forall i : 'I_N, T i -> T i -> Type.
Variable x : T i.
Variable y : T j.

Lemma cast_indnatdep2 (eq : j = i) : 
  P (cast_ty (lift_eq T (sym_eq eq)) x) y -> 
  P x (cast_ty (lift_eq T eq) y).
Proof. destruct eq=> //. Qed.

End ind_natdep2.

Notation cast F pf x := (cast_ty (lift_eq F pf) x).

Lemma cast_cast_eq A F (i j : A) (pf : i = j) (x : F i) : 
  cast F (sym_eq pf) (cast F pf x)  = x.
Proof. 
have EQ: JMeq (cast F (sym_eq pf) (cast F pf x)) x 
  by do 2 rewrite cast_ty_JMeq.
by rewrite EQ.
Qed.

