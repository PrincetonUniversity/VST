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

Section cast_f.

Variable N : nat.
Variable T U : 'I_N -> Type.
Variable i j : 'I_N.
Variable f : forall i : 'I_N, T i -> U i.

Lemma cast_f (x : T i) (eq : i=j) : 
  f (cast_ty (lift_eq T eq) x) = cast_ty (lift_eq U eq) (f x).
Proof. by rewrite <-eq; rewrite !cast_ty_erefl. Qed.

End cast_f.

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

Lemma cast_indnatdep''
  (x : T i) (eq : j = i) (pf : P (cast_ty (lift_eq T (sym_eq eq)) x)) : P x.
Proof. 
by move: pf; subst j; rewrite (cast_ty_erefl x). 
Qed.

End ind_natdep.

Section ind_natdep2.

Variable N : nat.
Variable T : 'I_N -> Type.
Variable U : 'I_N -> Type.
Variable i j : 'I_N.
Variable P : forall i : 'I_N, T i -> U i -> Type.
Variable x : T i.
Variable y : U j.

Lemma cast_indnatdep2 (eq : j = i) : 
  P (cast_ty (lift_eq T (sym_eq eq)) x) y -> 
  P x (cast_ty (lift_eq U eq) y).
Proof. destruct eq=> //. Qed.

End ind_natdep2.

Section ind_natdep_general.

Variable N : nat.
Variable T : 'I_N -> Type.
Variable U : 'I_N -> Type.
Variable V : 'I_N -> Type.
Variable i j k : 'I_N.
Variable P : forall i : 'I_N, T i -> U i -> V i -> Type.
Variable x : T i.
Variable y : U j.
Variable z : V k.

Lemma cast_indnatdep_general (eq_ij : i = j) (eq_ik : i = k) :
  P x 
    (cast_ty (lift_eq U (sym_eq eq_ij)) y) 
    (cast_ty (lift_eq V (sym_eq eq_ik)) z) -> 

  P (cast_ty (lift_eq T eq_ik) x) 
    (cast_ty (lift_eq U (eq_trans (sym_eq eq_ij) eq_ik)) y) 
    z.
Proof. destruct eq_ij; destruct eq_ik=> //. Qed.

End ind_natdep_general.

Section ind_natdep31.

Variable N : nat.
Variable T : 'I_N -> Type.
Variable U : 'I_N -> Type.
Variable V : 'I_N -> Type.
Variable i j : 'I_N.
Variable P : forall i : 'I_N, T i -> U i -> V i -> Type.
Variable x : T i.
Variable y : U i.
Variable z : V j.

Lemma cast_indnatdep31 (eq : i = j) :
  P x y (cast_ty (lift_eq V (sym_eq eq)) z) -> 
  P (cast_ty (lift_eq T eq) x) (cast_ty (lift_eq U eq) y) z.
Proof. destruct eq=> //. Qed.

End ind_natdep31.

Section ind_natdep32.

Variable N : nat.
Variable T : 'I_N -> Type.
Variable U : 'I_N -> Type.
Variable V : 'I_N -> Type.
Variable i j : 'I_N.
Variable P : forall i : 'I_N, T i -> U i -> V i -> Type.
Variable x : T i.
Variable y : U i.
Variable z : V j.

Lemma cast_indnatdep32 (eq : j = i) :
  P (cast_ty (lift_eq T (sym_eq eq)) x) (cast_ty (lift_eq U (sym_eq eq)) y) z -> 
  P x y (cast_ty (lift_eq V eq) z).
Proof. destruct eq=> //. Qed.

End ind_natdep32.

Section ind_natdep33.

Variable N : nat.
Variable T : 'I_N -> Type.
Variable U : 'I_N -> Type.
Variable V : 'I_N -> Type.
Variable i j : 'I_N.
Variable P : forall i : 'I_N, T i -> U i -> V i -> Type.
Variable x : T i.
Variable y : U j.
Variable z : V i.

Lemma cast_indnatdep33 (eq : i = j) :
  P x (cast_ty (lift_eq U (sym_eq eq)) y) z -> 
  P (cast_ty (lift_eq T eq) x) y (cast_ty (lift_eq V eq) z).
Proof. destruct eq=> //. Qed.

Lemma cast_indnatdep33' (eq : j = i) :
  P x (cast_ty (lift_eq U eq) y) z -> 
  P (cast_ty (lift_eq T (sym_eq eq)) x) y (cast_ty (lift_eq V (sym_eq eq)) z).
Proof. destruct eq=> //. Qed.

End ind_natdep33.

Notation cast F pf x := (cast_ty (lift_eq F pf) x).

Lemma cast_cast_eq A F (i j : A) (pf : i = j) (x : F i) : 
  cast F (sym_eq pf) (cast F pf x)  = x.
Proof. 
have EQ: JMeq (cast F (sym_eq pf) (cast F pf x)) x 
  by do 2 rewrite cast_ty_JMeq.
by rewrite EQ.
Qed.

Lemma cast_cast_eq' A F (i j : A) (pf1 : j = i) (pf2 : i = j) (x : F i) : 
  cast F pf1 (cast F pf2 x)  = x.
Proof. 
have EQ: JMeq (cast F pf1 (cast F pf2 x)) x 
  by do 2 rewrite cast_ty_JMeq.
by rewrite EQ.
Qed.

