(* Lemmas that DO NOT depend on CompCert or Verifiable C *)

Require Import Integers.
Require Import List. 
Require Import Coqlib.

Import ListNotations.


  Lemma skipn_list_repeat:
   forall A k n (a: A),
     (k <= n)%nat -> skipn k (list_repeat n a) = list_repeat (n-k) a.
Proof.
 induction k; destruct n; simpl; intros; auto.
 apply IHk; auto. omega.
Qed.

Definition Forall_tl (A : Type) (P : A -> Prop) (a : A) (l : list A) 
           (H : Forall P (a :: l)): Forall P l.
Proof. inversion H. assumption. Defined. 

Lemma Zlength_length:
  forall A (al: list A) (n: Z),
    0 <= n ->
    (Zlength al = n <-> length al = Z.to_nat n).
Proof.
intros. rewrite Zlength_correct.
split; intro.
rewrite <- (Z2Nat.id n) in H0 by omega.
apply Nat2Z.inj in H0; auto.
rewrite H0.
apply Z2Nat.inj; try omega.
rewrite Nat2Z.id; auto.
Qed.

Lemma firstn_exact : 
  forall {A : Type} (l1 l2 : list A) (n : nat),
    (length l1 = n)%nat -> firstn n (l1 ++ l2) = l1.
Proof.
  induction l1; destruct n; intros; simpl; try reflexivity; inversion H.
  * f_equal. apply IHl1. reflexivity.
Qed.    

Lemma skipn_exact :
  forall {A : Type} (l1 l2 : list A) (n : nat),
    (length l1 = n)%nat -> skipn n (l1 ++ l2) = l2.
Proof.
  induction l1; destruct n; intros; simpl; try reflexivity; inversion H.
  * apply IHl1. reflexivity.
Qed.

Lemma length_not_emp :
  forall {A B : Type} (l : list A) (z y : B),
    (Datatypes.length l > 0)%nat -> match l with [] => z | _ => y end = y.
Proof.
  intros.
  induction l as [ | x xs].
  - inversion H.
  - reflexivity.
Qed.

Lemma list_splitLength {A}: forall n (l:list A) m, 
      length l = (n + m)%nat -> exists l1 l2, l = l1 ++ l2 /\ length l1 = n /\ length l2 = m.
Proof. intros n.
  induction n; simpl; intros.
  exists [], l; eauto.
  destruct l; simpl in H; inversion H. clear H.
  destruct (IHn _ _ H1) as [l1 [l2 [L [L1 L2]]]]. clear IHn H1. subst.
  exists (a :: l1), l2; auto.
Qed.

Lemma skipn_short {A}: forall n (l:list A), (length l <= n)%nat -> skipn n l = nil.
Proof. induction n; simpl; intros. 
  destruct l; trivial. simpl in H. omega.
  destruct l; trivial.
  apply IHn. simpl in H. omega.
Qed.

Lemma skipn_app2:
 forall A n (al bl: list A),
  (n >= length al)%nat ->
  skipn n (al++bl) = skipn (n-length al) bl.
Proof.
intros. revert al H;
induction n; destruct al; intros; simpl in *; try omega; auto.
apply IHn; omega.
Qed. 

Lemma firstn_app1: forall {A} n (p l: list A),
  (n <= Datatypes.length p)%nat ->
   firstn n (p ++ l) = firstn n p.
Proof. intros A n.
induction n; simpl; intros. trivial.
  destruct p; simpl in H. omega.
  apply le_S_n in H. simpl. f_equal. auto. 
Qed.  

Lemma firstn_app2: forall {A} n (p l: list A),
  (n > Datatypes.length p)%nat ->
   firstn n (p ++ l) = p ++ (firstn (n-Datatypes.length p) l).
Proof. intros A n.
induction n; simpl; intros. 
  destruct p; simpl in *. trivial. omega.
  destruct p; simpl in *. trivial.
  rewrite IHn. trivial. omega. 
Qed.  

Lemma firstn_map {A B} (f:A -> B): forall n l, 
      firstn n (map f l) = map f (firstn n l).
Proof. intros n.
induction n; simpl; intros. trivial.
  destruct l; simpl. trivial.
  rewrite IHn. trivial.
Qed.

Lemma firstn_combine {A}: forall n (l k: list A), 
      firstn n (combine l k) = combine (firstn n l) (firstn n k).
Proof. intros n.
induction n; simpl; intros. trivial.
  destruct l; simpl. trivial.
  destruct k; simpl. trivial.
  rewrite IHn. trivial.
Qed.

Lemma firstn_precise {A}: forall n (l:list A), length l = n -> 
      firstn n l = l.
Proof. intros n. 
  induction n; intros; destruct l; simpl in *; trivial.
    inversion H.
    rewrite IHn; trivial. inversion H; trivial.
Qed. 

Lemma mapnth': forall {A B : Type} (f : A -> B) (l : list A) (d : A) (n : nat) fd,
      fd = f d -> nth n (map f l) fd = f (nth n l d).
Proof. intros; subst. apply map_nth. Qed.

Lemma Ztest_Bytetest:
 forall a, Z.testbit (Byte.unsigned a) = Byte.testbit a.
Proof. reflexivity. Qed.
Hint Rewrite Ztest_Bytetest : testbit.

Lemma nthD_1 {A B}: forall (f: A ->B) n l d fx dd, (n < length l)%nat ->
      nth n (map f l) d = fx -> 
      exists x, In x l /\ nth n l dd = x /\ f x = fx.
Proof. intros f n.
  induction n; simpl; intros.
    destruct l; simpl in *. omega.
      exists a; split. left; trivial. split; trivial.
    destruct l; simpl in *. omega. 
    destruct (IHn l d fx dd) as [? [? [? ?]]]. omega. trivial.
    exists x; eauto.
Qed.

Lemma nth_list_repeat' {A}: forall (a d:A) k i (Hik: (i <k)%nat),
      nth i (list_repeat k a) d = a.
Proof. intros a d k. induction k; simpl; trivial. intros. omega.
 intros. destruct i; simpl; trivial. rewrite IHk. trivial. omega. Qed.

Lemma minus_lt_compat_r: forall n m p : nat,
      (n < m)%nat -> (p <= n)%nat -> (n - p < m - p)%nat.
Proof. intros. unfold lt in *. omega. Qed.

Lemma map_nth_error_inv {A B}: forall n (l:list A) (f: A -> B) fd,
    nth_error (map f l) n = Some fd -> exists d, nth_error l n = Some d /\ fd = f d.
  Proof. intros n.
    induction n; intros l.
     destruct l; simpl; intros. inversion H.
       inversion H. exists a. split; trivial.
     destruct l; simpl; intros. inversion H.
       eapply IHn. apply H.
  Qed.

Lemma nth_error_app {A}: forall n (l:list A) d,
    nth_error l n = Some d -> forall ll, nth_error (l ++ ll) n = Some d.
  Proof. intros n.
    induction n; intros l.
     destruct l; simpl; intros. inversion H. trivial.
     destruct l; simpl; intros. inversion H.
       eapply IHn. apply H.
  Qed.

Lemma Forall_app {A} p (l1 l2: list A): Forall p (l1 ++ l2) <-> (Forall p l1 /\ Forall p l2).
Proof. intros. repeat  rewrite Forall_forall. 
  split; intros.
    split; intros; apply H; apply in_or_app. left; trivial. right; trivial.
  apply in_app_or in H0. destruct H. destruct H0; eauto.
Qed. 

Lemma Zlength_nonneg {A}: forall (l:list A), 0 <= Zlength l.
Proof.
 intros. 
 rewrite Zlength_correct.
 induction l; simpl. omega. rewrite Zpos_P_of_succ_nat. omega.
Qed.

Lemma Zlength_max_zero {A} (l:list A): Z.max 0 (Zlength l) = Zlength l.
Proof. rewrite Z.max_r. trivial. apply Zlength_nonneg. Qed.


Theorem xor_inrange : forall (x y : Z),
                        x = x mod Byte.modulus
                        -> y = y mod Byte.modulus
                        -> Z.lxor x y = (Z.lxor x y) mod Byte.modulus.
Proof.
  intros. symmetry. apply Byte.equal_same_bits. intros.
  assert (ZZ: Z.lxor x y mod Byte.modulus =
        Z.lxor x y mod two_p (Z.of_nat Byte.wordsize)).
        rewrite Byte.modulus_power. reflexivity.
  rewrite ZZ; clear ZZ.     
  rewrite Byte.Ztestbit_mod_two_p; try omega.
  destruct (zlt i (Z.of_nat Byte.wordsize)); trivial. 
  symmetry. rewrite Z.lxor_spec.
  assert (BB: Byte.modulus = two_p (Z.of_nat Byte.wordsize)).
    apply Byte.modulus_power. 
  rewrite BB in H, H0.

  rewrite H; clear H; rewrite H0; clear H0 BB.
   rewrite Byte.Ztestbit_mod_two_p; try omega.
   rewrite Byte.Ztestbit_mod_two_p; try omega.
   destruct (zlt i (Z.of_nat Byte.wordsize)); trivial. omega.
Qed.