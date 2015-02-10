(* Lemmas that DO NOT depend on CompCert or Verifiable C *)

Require Import Integers.
Require Import List. 
Require Import Coqlib.
Require Import common_lemmas. 

Import ListNotations.

Lemma length_nonneg {A} (l:list A): (0 <= length l)%nat.
 Proof. destruct l; omega. Qed.

Lemma skipn_0 {A} (l:list A): skipn 0 l = l. reflexivity. Qed.

Lemma skipn_list_repeat {A}(a:A): forall m n, skipn n (list_repeat m a) = list_repeat (m-n) a.
Proof. induction m; simpl; intros. apply skipn_nil.
  simpl. 
  destruct n. simpl. trivial. 
  simpl.  apply IHm.
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

