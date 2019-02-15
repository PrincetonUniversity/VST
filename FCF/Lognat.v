(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* This file contains the definition of the base 2 logarithm function (rounded down) over natural numbers. *)

(* Some of the definitions and theory in this file were added to Coq 8.4, so we should refactor this at some point. *)

Set Implicit Arguments.

Require Import ZArith.

(* log2 is like log_inf except it returns nat, so I don't have to reason about an unnecessary conversion. This function is only used to implement lognat below.*)
Fixpoint log2(n : positive) : nat :=
  match n with 
    | xH => 0
    | xO n' | xI n' => (S (log2 n'))
  end.

Lemma log2_prod_sum : forall(a : positive),
  (S (log2 a)) = (log2 (Pmult 2 a)).
  
  intros. auto.
Qed.


Lemma le_s : forall a b,
  (a <= b) -> S a <= S b.

  intros. omega.
Qed.



Lemma log2_monotonic_b : forall(a : positive),
  (log2 a) <= (log2 (Pos.succ a)).

  induction a; 
  simpl in *; try apply le_s; auto.
Qed.

Lemma log2_ge_monotonic : forall(a : positive),
  (log2 (Pos.succ a)) >= (log2 a).

  induction a; 
  simpl in *; try apply le_s; auto.
Qed.


Definition nat_to_pos (n : nat) : (n <> 0) -> positive :=
  fun _ => (P_of_succ_nat (pred n)).

Lemma double_nat_nz : forall(a : nat)(pf : a <> 0),
  ((2 * a) <> 0).
  intros. omega.
Qed.
Lemma s_nat_nz : forall(a : nat)(pf : a <> 0),
  ((S a) <> 0).
  intros. omega.
Qed.

Lemma factor_s_conv : forall(a : nat)(pf1 : (a <> 0))(pf2 : (S a) <> 0),
  (nat_to_pos (pf2)) = (Pos.succ (nat_to_pos pf1)).
  
  intros. 
  destruct a.
  congruence.

  unfold nat_to_pos in *.
  simpl in *.
  intros. auto.
Qed.

Lemma add_s_r : forall a b,
  a + (S b) = S (a + b).
  intros. omega.
Qed.

Lemma factor_double_s : forall a,
  (2 * (S a)) = (S (S (2 * a))).

  intros. omega.
Qed.

Lemma factor_double_conv : forall(a : nat)(pf1 : (a <> 0))(pf2 : (2 * a) <> 0),
  (nat_to_pos pf2) = (Pmult 2 (nat_to_pos pf1)).

  induction a; intros; simpl in *.
  congruence.

  destruct (eq_nat_dec a 0).
  subst. 
  unfold nat_to_pos.
  auto.

  assert (a + S (a + 0) <> 0) by omega.
  specialize (factor_s_conv H). intros. 
  unfold nat_to_pos in *.

  rewrite (H0 pf2). clear H0.  clear pf2.
  assert (a + S (a + 0) = S (a + (a + 0))) by omega.
  rewrite H0.  
  assert (a + (a + 0) <> 0) by omega.
  specialize (factor_s_conv H1). intros. 
  
  unfold nat_to_pos in H2.
  rewrite <- H0 in H2.
  rewrite <- H0.
  rewrite (H2 H). clear H. clear H2.
  
  rewrite (IHa n). clear IHa.
  simpl.
  destruct a. intros. destruct n. auto.

  auto.
  omega. 
Qed.

Definition lognat(n : nat) : (n <> 0) -> nat := 
  fun pf => (log2 (nat_to_pos pf)).


Theorem lognat_prod_sum : forall(a : nat)(pf1 : (a <> 0))(pf2: (2 * a) <> 0),
  (S (lognat pf1)) = (lognat pf2).
  
  intros. 
  unfold lognat in *.
  rewrite (factor_double_conv pf1 pf2).
  eapply log2_prod_sum.
Qed.  

Theorem lognat_monotonic_b : forall(a : nat)(pf1 : (a <> 0))(pf2: (S a) <> 0),
  (lognat pf1) <= (lognat pf2).
  
  induction a.
  intros. 
  destruct pf1. auto.

  intros. 
  unfold lognat in *.
  rewrite (factor_s_conv pf1).
  apply log2_monotonic_b.
Qed.

(* for good measure, we will define exponentiation for nat and prove that lognat is correct *)
Fixpoint expnat(a e : nat) : nat :=
  match e with
    | 0 => 1
    | (S e') => a * (expnat a e')
  end.

Lemma mult_ne : forall a b,
  a <> 0 -> b <> 0 -> a * b <> 0.

  intros. 
  destruct a. omega. 
  destruct b. omega. 
  simpl. 
  remember (b + a * (S b)) as c.
  omega. 
Qed.
  

Theorem expnat_nz : forall a e,
  (a <> 0) -> (expnat a e) <> 0.

  induction e.
  simpl. auto.

  simpl. 
  intros. 
  eapply mult_ne; eauto.
Qed.

Lemma nz_2 : 2 <> 0.
  omega.
Qed.

Theorem expnat_2_nz: forall e,
  (expnat 2 e) <> 0.
  
  intros. 
  apply (expnat_nz e nz_2).
Qed.

Theorem expnat_2_monotonic : forall e1 e2,
  e1 <= e2 ->
  (expnat 2 e1 <= expnat 2 e2).
  
  induction e1.
  intros.
  simpl.
  specialize (expnat_2_nz e2). intros.
  omega.

  induction e2;
  intros.
  omega.

  simpl. 
  specialize (IHe1 e2).
  omega.
Qed.

Theorem lognat_correct_eq : forall(b : nat)(pf : (expnat 2 b) <> 0),
  (lognat pf) = b.

  induction b.
  intros. simpl in *. auto.
  
  intros. 
  specialize (lognat_prod_sum (expnat_2_nz b)). intros. 
  specialize (IHb (expnat_2_nz b)). 
  rewrite IHb in H.
  symmetry in H.
  simpl in *.
  apply H.
Qed.


Lemma fold_add : forall a,
  a + (a + 0) = 2*a.
  intros. omega.
Qed.

Theorem lognat_ge_monotonic_b : forall(a : nat)(pf1 : (a <> 0))(pf2: (S a) <> 0),
  (lognat pf2) >= (lognat pf1).
  
  induction a.
  intros. 
  destruct pf1. auto.

  intros. 
  unfold lognat in *.
  rewrite (factor_s_conv pf1).
  apply log2_monotonic_b.
Qed.

Lemma ge_trans : forall a b c,
  a >= b -> b >= c -> a >= c.
  intuition.
Qed.

Lemma lognat_ge_monotonic_h : forall (c a b : nat)(pfa : a <> 0)(pfb : b <> 0), 
    a >= b -> c = (a - b) -> (lognat pfa) >= (lognat pfb).

  induction c.
  intros. 
  assert (a = b) by intuition.
  subst. auto.

  intros. 
  assert (a >= (S b)) by omega. 
  assert (c = a - (S b)) by omega.
  eapply ge_trans.
  apply (IHc a (S b) pfa (s_nat_nz pfb)).
  apply H1.
  apply H2.
  apply lognat_ge_monotonic_b.
Qed.

Lemma lognat_ge_monotonic : forall (a b : nat)(pfa : a <> 0)(pfb : b <> 0), 
    a >= b -> (lognat pfa) >= (lognat pfb).

  intros.
  remember (a - b) as c.
  apply (@lognat_ge_monotonic_h c); auto.
Qed.

Lemma lognat_monotonic : forall (a b : nat)(pfa : a <> 0)(pfb : b <> 0), 
    a <= b -> (lognat pfa) <= (lognat pfb).

  intros.
  remember (b - a) as c.
  apply (@lognat_ge_monotonic_h c); auto.
Qed.

Theorem mt : forall P Q: Prop, (P -> Q) -> (~Q -> ~P).
  unfold not in *.
  intros. 
  apply H0.
  apply H.
  apply H1.
Qed.

Lemma ge_not : forall a b,
  ~(a >= b) -> a < b.
  intuition.
Qed.

Lemma lognat_ge_monotonic_mt : forall (a b : nat)(pfa : a <> 0)(pfb : b <> 0), 
    (lognat pfa) < (lognat pfb) -> a < b.

  intros. 
  specialize (lognat_ge_monotonic pfa pfb).
  intros. 
  specialize (mt H0).
  intros. 
  apply ge_not. omega.
Qed.

Lemma lognat_correct2 : forall(a : nat)(pf : a <> 0),
  a < (expnat 2 (S (lognat pf))).
  
  intros. 

  simpl.
  rewrite fold_add.
  assert (expnat 2 (lognat pf) <> 0). apply expnat_nz. auto.
  assert (2 * (expnat 2 (lognat pf)) <> 0). omega. 
  eapply (lognat_ge_monotonic_mt pf H0). 
  rewrite <- (lognat_prod_sum H).
  rewrite lognat_correct_eq.
  omega.
Qed.

Lemma lognat_odd : forall(a : nat)(pf1 : (2 * a) <> 0)(pf2 : (S (2 * a)) <> 0),
  ((lognat pf2) = (lognat pf1)).

  intros. 
  unfold lognat in *.
  rewrite (factor_s_conv pf1 pf2).
  assert (a <> 0). omega.
  rewrite (factor_double_conv H pf1).
  simpl. 
  auto.
Qed.

Lemma double_s : forall a, (S (S (2 * a))) = 2 * (S a).
  intros. omega.
Qed.


Lemma lognat_double_eq : forall a b (pf1: 2 * a <> 0)(pf2: 2 * b <> 0)(pf3 : a <> 0) (pf4: b <> 0),
  lognat pf3 = lognat pf4 -> 
  lognat pf1 = lognat pf2.

  intros. 
  rewrite <- (lognat_prod_sum pf3).
  rewrite <- (lognat_prod_sum pf4).
  omega.
Qed.

Lemma nat_comp : forall(a : nat),
  exists x : nat,
  (a = (2 * x) \/ a = (S (2 * x))).

  induction a.
  exists 0. simpl.  auto.

  elim IHa. clear IHa.
  intros. 
  destruct H.
  subst. simpl.
  exists x.
  right. auto.

  subst. simpl. 
  exists (S x).
  left.
  simpl. 
  omega. 
Qed.

Lemma lognat_correct1 : forall(b a : nat)(pf : a <> 0),
  (lognat pf) = b -> 
  (expnat 2 b) <= a.

  induction b.

  intros. simpl in *. omega.

  intros. 
  elim (nat_comp a). intros. 
  destruct H0.
  subst. 
  destruct (eq_nat_dec x 0).
  subst. omega. 
  rewrite <- (lognat_prod_sum n pf) in H.
  inversion H. clear H.
  rewrite H1.
  apply IHb in H1.
  simpl in *. omega. 

  subst. 
  destruct (eq_nat_dec x 0).
  subst. unfold lognat in H. simpl in *. omega. 
  assert ((2 * x) <> 0). omega.
  rewrite (lognat_odd x H0 pf) in H.
  
  rewrite <- (lognat_prod_sum n H0) in H.
  inversion H.
  rewrite H2.
  apply IHb in H2.
  simpl. 
  omega.
Qed.  
  
  
Theorem lognat_correct : forall(a : nat)(pf : a <> 0),
  (expnat 2 (lognat pf)) <= a < (expnat 2 (S (lognat pf))).

  intros.
  split.
  remember (lognat pf) as b.
  apply (lognat_correct1 pf). auto.
  apply lognat_correct2.
Qed.

Lemma lognat_prod_sum_gen_h : forall (a' a b: nat)(pf1 : (a <> 0))(pf2 : (b <> 0))(pf3 : a * b <> 0), 
  lognat pf1 = a' ->
  a' + lognat pf2 <= lognat pf3.
 
  induction a'; intros. 
  simpl. 
  eapply lognat_monotonic. 
  induction a.
  congruence.
  simpl. 
  intuition.

  destruct (nat_comp a).
  destruct H0.
  subst.
  assert (x <> 0). omega.
  assert (x * b <> 0). destruct x; destruct b; simpl; congruence.
  rewrite <- (lognat_prod_sum H0) in H.
  assert (lognat pf3 = S (lognat H1)). 
  generalize pf3.
  rewrite mult_assoc_reverse.
  intros. 
  rewrite (lognat_prod_sum _ pf0).
  trivial.

  rewrite H2.
  inversion H.
  specialize (IHa' x b H0 pf2 H1 H4).
  subst.
  omega. 

  destruct (eq_nat_dec x 0).
  subst.
  unfold lognat in *.
  simpl in *.
  discriminate.

  assert (2 * x <> 0). omega. 
  assert (x * b <> 0). destruct x; destruct b; simpl; congruence.
  assert (2 * x * b <> 0). rewrite mult_assoc_reverse. omega.
  subst.
  rewrite (lognat_odd _ H1) in H.
  rewrite <- (lognat_prod_sum n) in H.
  inversion H.
  subst. 
  assert (lognat n = lognat n). trivial.
  specialize (IHa' x b n pf2 H2 H0).

  generalize pf3.
  assert (S (2 * x) * b = b + 2 * x * b). intuition.
  rewrite H4.
  intros. 
  eapply le_trans.
  2:{
    eapply (lognat_monotonic H3). intuition.
  }
  generalize H3.
  rewrite mult_assoc_reverse.
  intros. 
  rewrite <- (lognat_prod_sum H2).
  omega.
Qed.

Theorem lognat_prod_sum_gen : forall (a b: nat)(pf1 : (a <> 0))(pf2 : (b <> 0))(pf3 : a * b <> 0), 
  lognat pf1 + lognat pf2 <= lognat pf3.

  intros.
  eapply lognat_prod_sum_gen_h.
  eauto.
Qed.

Lemma lognat_0_1 : forall n (pf : n <> 0),
  lognat pf = 0 -> n = 1.

  intros. 
  destruct n.
  omega.
  
  destruct n.
  trivial.

  assert (2 <> 0). omega.
  assert (lognat pf >= lognat H0).
  eapply lognat_ge_monotonic.
  omega. 

  unfold lognat in *.
  simpl in *.
  omega.
Qed.

Lemma lognat_succ_h : forall a n (pf1 : n <> 0)(pf2: (S n) <> 0),
  a = lognat pf1 -> 
    lognat pf2 = a \/
    lognat pf2 = S (a).

  induction a; intros. 
  assert (n = 1). 
  apply (lognat_0_1 pf1).
  auto.
  subst. 
  unfold lognat.
  simpl. 
  auto.

  destruct (nat_comp n).
  destruct H0.
  subst. 
  assert (x <> 0). omega.
  rewrite <- (lognat_prod_sum H0) in H.
  inversion H.
  subst. 
  rewrite (lognat_odd _ pf1).
  rewrite <- (lognat_prod_sum H0).
  auto.

  subst.
  destruct (eq_nat_dec x 0).
  subst. 
  unfold lognat in *.
  simpl in *.
  omega. 

  generalize pf2.
  assert (S (S (2 * x)) = 2 * (S x)). omega.
  rewrite H0.
  intros. 
  assert (S x <> 0). omega. 
  assert (2 * x <> 0). omega.
  rewrite (lognat_odd _ H2) in H.
  rewrite <- (lognat_prod_sum n) in H.
  inversion H.
  rewrite <- (lognat_prod_sum H1).
  specialize (IHa x n H1 H4). 
  destruct IHa.
  subst. 
  rewrite H4.
  auto.
  subst. 
  right.
  rewrite H3.
  auto.

Qed.

Lemma lognat_succ : forall n (pf1 : n <> 0)(pf2: (S n) <> 0),
  lognat pf2 = lognat pf1 \/
  lognat pf2 = S (lognat pf1).

  intros.
  eapply lognat_succ_h.
  eauto.
Qed.

Lemma logn_ge_1 : forall n (pf : n <> 0),
  n > 1 -> lognat pf >= 1.

  intros. 
  destruct n.
  congruence.
  
  destruct n.
  omega.

  assert (2 <> 0).
  omega.

  assert (forall n (pf1 : S (S n) <> 0)(pf2 : 2 <> 0), lognat pf1 >= lognat pf2).
  intros.
  eapply lognat_ge_monotonic.
  omega.

  assert (forall (pf : 2 <> 0), 1 = lognat pf).
  intros. 
  unfold lognat. 
  auto.

  rewrite (H2 H0).
  eauto.

Qed.