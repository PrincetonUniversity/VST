(* Lemmas that DO NOT depend on CompCert or Verifiable C *)

Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import Vector.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.

Definition Vector_0_is_nil (T : Type) (v : Vector.t T 0) : v = Vector.nil T :=
  match v with Vector.nil => eq_refl end.

Lemma VectorToList_cons A n: forall (a:A) l,
      Vector.to_list (Vector.cons A a n l) =
      List.cons a (Vector.to_list l).
Proof. intros. reflexivity. Qed.

Lemma VectorToList_length {A}: forall n (v: Vector.t A n), length (Vector.to_list v) = n.
Proof.
  apply Vector.t_rec. reflexivity.
  intros. rewrite VectorToList_cons. simpl. rewrite H. trivial.
Qed.

Lemma VectorToList_combine A n: forall (a:A) b v1 v2,
     combine (Vector.to_list (Vector.cons A a n v1))
             (Vector.to_list (Vector.cons A b n v2))
   = (a,b) :: combine (Vector.to_list v1) (Vector.to_list v2).
Proof. intros. simpl. f_equal. Qed.

Theorem VectorToList_append {A}:
        forall (m:nat) (v2:Vector.t A m) (n : nat) (v1 : Vector.t A n),
                   (Vector.to_list v1) ++ (Vector.to_list v2) =
                   Vector.to_list (Vector.append v1 v2).
Proof. intros m v2.
  eapply Vector.t_rec.
  reflexivity.
  intros. simpl. rewrite (VectorToList_cons _ _ h). f_equal. rewrite <- H. f_equal.
Qed.

Lemma Forall2_map {A B} (f:A -> B): forall l m,
      Forall2 (fun x y => y = f x) l m -> map f l = m.
Proof. intros.
  induction H; simpl. reflexivity.
  subst y. f_equal. trivial.
Qed.

Lemma app_inv_length1 {A}: forall (l1 m1 l2 m2:list A),
  l1++l2 = m1++m2 -> length l1 = length m1 -> l1=m1 /\ l2=m2.
Proof.
induction l1; simpl; intros.
{ destruct m1; simpl in *. split; trivial. omega. }
{ destruct m1; simpl in *. discriminate.
  inversion H; clear H; subst a0.
  destruct (IHl1 _ _ _ H3). omega.
  subst. split; trivial. }
Qed.

Lemma app_inv_length2 {A}: forall (l1 m1 l2 m2:list A),
  l1++l2 = m1++m2 -> length l2 = length m2 -> l1=m1 /\ l2=m2.
Proof.
induction l1; simpl; intros.
{ destruct m1; simpl in *. split; trivial.
  assert (length l2 = length (a :: m1 ++ m2)). rewrite <- H; trivial.
  rewrite H1 in H0; clear H H1. simpl in H0. rewrite app_length in H0. omega. }
{ assert (length (a :: l1 ++ l2) = length (m1 ++ m2)). rewrite <- H; trivial.
  simpl in H1. do 2 rewrite app_length in H1. rewrite H0 in H1.
  destruct m1; simpl in *. omega.
  inversion H; clear H. subst a0.
  destruct (IHl1 _ _ _ H4 H0). subst. split; trivial. }
Qed.

Lemma cons_inv {A}: forall (a1 a2:A) t1 t2, a1::t1 = a2::t2 -> a1=a2 /\ t1=t2.
  intros. inversion H; split; trivial. Qed.

Lemma mod_exists a b c: a mod b = c -> b<> 0 -> exists k, k*b+c=a.
Proof. intros. specialize (Zmod_eq_full a b H0). intros.
  exists (a/b). rewrite H in H1; clear H H0. subst c. omega. Qed.

Lemma app_inj1 {A} l2 m2: forall (l1 m1:list A) (H:l1++l2=m1++m2),
      length l1=length m1 -> l1=m1 /\ l2=m2.
Proof. induction l1.
  destruct m1; simpl; intros. split; trivial. discriminate.
  destruct m1; simpl; intros. discriminate.
  inversion H; subst.
  destruct (IHl1 _ H3). omega.
  subst. split; trivial.
Qed.
Lemma max_unsigned_modulus: Int.max_unsigned + 1 = Int.modulus.
Proof. reflexivity. Qed.

Lemma int_max_unsigned_eq: Int.max_unsigned = 4294967295.
Proof. reflexivity. Qed.

Lemma ptrofs_max_unsigned_eq: Ptrofs.max_unsigned = 4294967295.
Proof. reflexivity. Qed.

Lemma IntModulus32: Int.modulus = 2^32. reflexivity. Qed.

Lemma Intsize_monotone a b: 0 <= Int.unsigned (Int.repr a) <= Int.unsigned (Int.repr b) ->
                          Int.size (Int.repr a) <= Int.size (Int.repr b).
Proof. apply Int.Zsize_monotone. Qed.

Lemma list_nil {A} l (L:@length A l = 0%nat): l = nil.
Proof. destruct l; simpl in *; eauto. inv L. Qed.

Lemma nth_mapIn {A}: forall i (l:list A) d (Hi: (0 <= i < length l)%nat),
  exists n, nth i l d = n /\ In n l.
Proof. intros i.
  induction i; simpl; intros.
    destruct l; simpl in *. omega. exists a. split; trivial. left; trivial.
    destruct l; simpl in *. omega.
      destruct (IHi l d) as [? [? ?]]. omega. rewrite H. exists x; split; trivial. right; trivial.
Qed.

Lemma skipn_list_repeat:
   forall A k n (a: A),
     (k <= n)%nat -> skipn k (list_repeat n a) = list_repeat (n-k) a.
Proof.
 induction k; destruct n; simpl; intros; auto.
 apply IHk; auto. omega.
Qed.

Lemma skipn_length:
  forall {A} n (al: list A),
    (length al >= n)%nat ->
    (length (skipn n al) = length al - n)%nat.
Proof.
 induction n; destruct al; simpl; intros; auto.
 apply IHn. omega.
Qed.

Lemma fold_left_cons {A B} (f: A -> B -> A) l b x:
      fold_left f (x :: l) b = fold_left f l (f b x).
Proof. reflexivity. Qed.

Definition Forall_tl (A : Type) (P : A -> Prop) (a : A) (l : list A)
           (H : Forall P (a :: l)): Forall P l.
Proof. inversion H. assumption. Defined.
(*Now in sublist
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
*)
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
(*now in floyd_sublist
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
Qed.  *)

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

Lemma length_mul_split A k (K:(0<k)%nat) n (N:(0<n)%nat): forall (l:list A), length l = (k * n)%nat ->
      exists l1, exists l2, l=l1++l2 /\ length l1=n /\ length l2 = ((k-1) * n)%nat.
Proof.
  intros.
  assert ((k * n = n + (k-1) * n)%nat). rewrite mult_minus_distr_r. simpl. rewrite plus_0_r.
      rewrite le_plus_minus_r. (* NPeano.Nat.add_sub_assoc. rewrite minus_plus. *) trivial.
      specialize (mult_le_compat_r 1 k n). simpl; rewrite plus_0_r. simpl; intros. apply H0. omega.
  rewrite H0 in H; clear H0.
  apply (list_splitLength _ _ _ H).
Qed.
