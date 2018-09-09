(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
(* a type class and other definitions for decidable equality *)

Set Implicit Arguments.
Require Import Bvector.
Require Import Arith.

Definition eq_dec(A : Set) := forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}.

Class EqDec (A : Set) := {
  eqb : A -> A -> bool ;
  eqb_leibniz : forall x y, eqb x y = true <-> x = y 
}.

Infix "?=" := eqb (at level 70) : eq_scope.
Infix "!=" := (fun x y => negb (eqb x y)) (at level 70) : eq_scope.

Theorem eqb_refl : forall (A : Set)(pf : EqDec A)(a : A),
  eqb a a = true.
  
  intuition.
  eapply eqb_leibniz.
  trivial.
Qed.

Theorem eqb_symm : 
  forall (A : Set){eqd : EqDec A}(x y : A),
    eqb x y = eqb y x.
  
  intuition.
  case_eq (eqb x y); intuition.
  rewrite eqb_leibniz in H.
  subst.
  rewrite eqb_refl.
  trivial.
  
  case_eq (eqb y x); intuition.
  rewrite eqb_leibniz in H0; subst.
  rewrite eqb_refl in H.
  discriminate.
  
Qed.

Theorem EqDec_dec : forall A,
  EqDec A ->
  forall (a b : A), {a = b} + {a <> b}.

  intuition.
  remember (eqb a b) as x.
  destruct x.
  left.
  eapply eqb_leibniz.
  auto.

  right.
  intuition.
  subst.
  assert (eqb b b = true -> False).
  intuition.
  congruence.
  eapply H0.
  eapply eqb_leibniz.
  trivial.
Qed.

Theorem dec_EqDec : forall (A : Set)(eqd : eq_dec A),
  EqDec A.

  intuition.
  eapply (Build_EqDec (fun a1 a2 => if (eqd a1 a2) then true else false)).
  intuition.
  destruct (eqd x y); trivial.
  discriminate.

  destruct (eqd x y); trivial.
  congruence.

Qed.

Lemma vector_0 : forall (A : Set)(v : Vector.t A 0),
  v = Vector.nil A.

  intuition.
  eapply (Vector.case0 (fun v => v = [])).
  trivial.
Qed.

Lemma vector_S : forall (A : Set)(n : nat)(v : Vector.t A (S n)),
  exists a : _, exists v' : _,
    v = Vector.cons _ a _ v'.
  
  intuition.
  induction n, v using Vector.rectS.
  econstructor. econstructor. eauto.
  
  econstructor. econstructor. eauto.
    
Qed.
  
Definition eqb_vector(A : Set)(eqd : EqDec A)(n : nat)(v1 v2 : Vector.t A n) :=
  Vector.fold_left2 (fun b a1 a2 => b && (eqb a1 a2)) true v1 v2.

Theorem eqb_vector_refl : 
  forall (A : Set)(eqd : EqDec A)(n : nat)(v : Vector.t A n),
    eqb_vector _ v v = true.

  induction n; intuition; simpl in *.
  rewrite (vector_0 v).
  unfold eqb_vector.
  simpl.
  trivial.

  destruct (vector_S v).
  destruct H.
  subst.
  unfold eqb_vector.
  simpl.
  rewrite eqb_refl.
  eapply IHn.

Qed.

Theorem vector_fold_false : 
  forall (A : Set)(f : A -> A -> bool)(n : nat)(v1 v2 : Vector.t A n),
    Vector.fold_left2 (fun b a1 a2 => b && (f a1 a2)) false v1 v2 = false.
  
  induction n; intuition; simpl in *.
  rewrite (vector_0 v1).
  rewrite (vector_0 v2).
  simpl.
  trivial.
  
  destruct (vector_S v1).
  destruct (vector_S v2).
  destruct H.
  destruct H0.
  subst.
  simpl.
  eapply IHn.
  
Qed.

Theorem eqb_vector_leibniz:
  forall (A : Set)(eqd : EqDec A)(n : nat)(v1 v2 : Vector.t A n),
    eqb_vector _ v1 v2 = true -> v1 = v2.


  induction n; intuition; simpl in *.
  rewrite (vector_0 v1).
  rewrite (vector_0 v2).
  trivial.

  destruct (vector_S v1).
  destruct (vector_S v2).
  destruct H0.
  destruct H1.
  subst.
  unfold eqb_vector in H.
  simpl in *.
  case_eq (eqb x x0); intuition.
  rewrite eqb_leibniz in H0.
  subst.
  f_equal.
  rewrite eqb_refl in H.
  eapply IHn.
  eapply H.
  
  rewrite H0 in H.
  rewrite vector_fold_false in H.
  discriminate.
Qed.

Section Vector_EqDec.

  Variable A : Set.
  Context `{eqd_A : EqDec A}.

  Instance Vector_EqDec : 
    forall (n : nat),
      EqDec (Vector.t A n).
  
  intuition.
  eapply (Build_EqDec (@eqb_vector A eqd_A n)).
  intuition.
  eapply eqb_vector_leibniz.
  trivial.
  subst.
  apply eqb_vector_refl.
  
  Qed.
End Vector_EqDec.

(*
Fixpoint BvIsZero n (v : Bvector n) : bool  :=
  match v with
    | Vector.nil => true
    | Vector.cons b _ v' =>
      (andb (if (bool_dec b false) then true else false) (BvIsZero v'))
  end.
*)

Instance unit_EqDec : EqDec unit := {eqb := (fun x y => true)}.

intuition.
destruct x.
destruct y.
trivial.

Qed.

Instance bool_EqDec : EqDec bool := {eqb := Bool.eqb}.
eapply eqb_true_iff.
Qed.

(* Bvector decidable equality was added before Vector.t decidable equality.  Definitions remain for compatibility. *)
Definition eqbBvector n (v1 v2 : Bvector n) : bool :=
  (eqb_vector _ v1 v2).

Theorem eqbBvector_sound : forall n (v1 v2 : Bvector n),
  eqbBvector v1 v2 = true -> v1 = v2.

  intuition.
  unfold eqbBvector in *.
  eapply eqb_vector_leibniz.
  trivial.
Qed.

Theorem eqbBvector_complete : forall n (v : Bvector n),
  eqbBvector v v = true.

  intuition.
  unfold eqbBvector.
  apply eqb_vector_refl.
Qed.
 
Instance Bvector_EqDec : forall n, EqDec (Bvector n) := {eqb := (@eqbBvector n)}.
intuition.
eapply eqbBvector_sound; auto.
intuition.
subst.
eapply eqbBvector_complete; eauto.
Defined.


Instance nat_EqDec : EqDec nat := {eqb := (fun x y => (leb x y) && (leb y x))}.

intuition.
apply andb_true_iff in H.
intuition.
eapply le_antisym;
eapply leb_iff; eauto.

apply andb_true_iff.
intuition;
eapply leb_iff; subst; eapply le_refl.
Qed.


Definition eqbPair (A B : Set)(dA : EqDec A)(dB : EqDec B)(p1 p2 : (A*B)) :=
  (eqb (fst p1) (fst p2)) && (eqb (snd p1) (snd p2)).

Instance pair_EqDec : forall (A B : Set)(dA : EqDec A)(dB : EqDec B), EqDec (prod A B) := {eqb := (@eqbPair A B dA dB)}.

intuition; unfold eqbPair in *; simpl in *.
apply andb_true_iff in H.
intuition.
f_equal;
eapply eqb_leibniz; trivial.

inversion H; subst; clear H.
apply andb_true_iff; intuition;
eapply eqb_leibniz; trivial.
Defined.

Definition eqbSum(A B : Set)(dA : EqDec A)(dB : EqDec B)(s1 s2 : (A + B)) :=
  match s1 with
    | inl a1 =>
    match s2 with
      | inl a2 => eqb a1 a2
      | inr b2 => false
    end
    | inr b1 =>
    match s2 with
      | inl a2 => false
      | inr b2 => eqb b1 b2
    end
  end.

Instance sum_EqDec : forall (A B : Set)(dA : EqDec A)(dB : EqDec B), 
    EqDec (sum A B) := {eqb := (@eqbSum A B dA dB)}.

intuition; unfold eqbSum in *; try
match goal with
  | [H : eqb _ _ = true |-_] => rewrite eqb_leibniz in H
  | [H : inl _ = inl _ |-_] => inversion H
  | [H : inr _ = inr _ |-_] => inversion H
end; subst; try rewrite eqb_refl; trivial; try discriminate.

Defined.


Definition eqbOption (A : Set)(dA : EqDec A)(o1 o2 : option A) :=
  match o1 with
    | None => 
      match o2 with
        | None => true
        | Some _ => false
      end
    | Some a1 =>
      match o2 with
        | None => false
        | Some a2 => (eqb a1 a2)
      end
  end.

Instance option_EqDec : forall (A : Set)(dA : EqDec A), EqDec (option A) := {eqb := (@eqbOption A dA )}.

intuition; unfold eqbOption in *; simpl in *.
destruct x.
destruct y.
f_equal.
eapply eqb_leibniz; trivial.
discriminate.
destruct y.
discriminate.
trivial.

subst.

destruct y.
eapply eqb_leibniz; trivial.
trivial.
Qed.

Local Open Scope list_scope.
Fixpoint eqbList(A : Set)(eqd : EqDec A)(ls1 ls2 : list A) :=
  match ls1 with
    | nil => 
      match ls2 with
        | nil => true
        | _ :: _ => false
      end
    | a1 :: ls1' =>
      match ls2 with
        | nil => false 
        | a2 :: ls2' =>
          (eqb a1 a2) && (eqbList _ ls1' ls2')
      end
  end.

Lemma eqbList_correct1 : forall (A : Set)(eqd : EqDec A) ls1 ls2,
  eqbList eqd ls1 ls2 = true -> 
  ls1 = ls2.

  induction ls1; destruct ls2; intuition; simpl in *; try discriminate.
  apply andb_true_iff in H.
  intuition.
  f_equal.
  eapply eqb_leibniz.
  trivial.
  eauto.
Qed.

Lemma eqbList_correct2 : forall (A : Set)(eqd : EqDec A) ls1 ls2,
  ls1 = ls2 -> 
  eqbList eqd ls1 ls2 = true.
  
  induction ls1; destruct ls2; intuition; simpl in *; try discriminate.
  inversion H; clear H; subst.

  apply andb_true_iff.
  intuition.
  eapply eqb_leibniz.
  trivial.
Qed.

Instance list_EqDec : forall (A : Set)(dA : EqDec A), EqDec (list A) := {eqb := (@eqbList A dA )}.

intuition.
eapply eqbList_correct1; trivial.
eapply eqbList_correct2; trivial.
Qed.

Theorem eqb_false_iff : 
  forall (A : Set)(eqd : EqDec A)(a1 a2 : A),
    eqb a1 a2 = false <->
    a1 <> a2.
  
  intuition.
  subst.
  rewrite eqb_refl in H.
  discriminate.
  
  case_eq (eqb a1 a2); intuition.
  rewrite eqb_leibniz in H0.
  intuition.
  
Qed.

Theorem eqbPair_symm : 
  forall (A B : Set)(eqda : EqDec A)(eqdb : EqDec B) (p1 p2 : (A * B)),
    eqbPair _ _ p1 p2 = eqbPair _ _ p2 p1.
  
  intuition.
  unfold eqbPair in *.
  simpl.
  rewrite eqb_symm.
  rewrite (eqb_symm b b0).
  trivial.
  
Qed.