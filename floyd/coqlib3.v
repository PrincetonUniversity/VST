Require Recdef.
Require Import Coqlib.
Require Import Integers.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Integers.
Require Import List.
Require Import msl.Coqlib2.

(**************************************************

List lemmas

**************************************************)

Lemma firstn_app:
 forall {A} n m (al: list A), firstn n al ++ firstn m (skipn n al) =
  firstn (n+m) al.
Proof. induction n; destruct al; intros; simpl; auto.
destruct m; reflexivity.
f_equal; auto.
Qed.

Lemma nth_skipn:
  forall {A} i n data (d:A),
       nth i (skipn n data) d = nth (i+n) data d.
Proof.
intros.
revert i data; induction n; simpl; intros.
f_equal; omega.
destruct data; auto.
destruct i; simpl; auto.
rewrite IHn.
replace (i + S n)%nat with (S (i + n))%nat by omega; auto.
Qed.

Lemma skipn_skipn: forall {A} n m (xs: list A),
  skipn n (skipn m xs) = skipn (m + n) xs.
Proof.
  intros.
  revert xs; induction m; intros.
  + reflexivity.
  + simpl.
    destruct xs.
    - destruct n; reflexivity.
    - apply IHm.
Qed.

Lemma firstn_exact_length: forall {A} (xs: list A), firstn (length xs) xs = xs.
Proof.
  intros.
  induction xs.
  + reflexivity.
  + simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Lemma skipn_exact_length: forall {A} (xs: list A), skipn (length xs) xs = nil.
Proof.
  intros.
  induction xs.
  + reflexivity.
  + simpl.
    rewrite IHxs.
    reflexivity.
Qed.

Lemma len_le_1_rev: forall {A} (contents: list A),
  (length contents <= 1)%nat ->
  contents = rev contents.
Proof.
  intros.
  destruct contents.
  + reflexivity.
  + destruct contents.
    - reflexivity.
    - simpl in H. omega.
Qed.

Lemma firstn_firstn: forall {A} (contents: list A) n m,
  (n <= m)%nat ->
  firstn n (firstn m contents) = firstn n contents.
Proof.
  intros.
  revert n m H;
  induction contents;
  intros.
  + destruct n, m; reflexivity.
  + destruct n, m; try solve [omega].
    - simpl; reflexivity.
    - simpl; reflexivity.
    - simpl.
      rewrite IHcontents by omega.
      reflexivity.
Qed.

Lemma firstn_1_skipn: forall {A} n (ct: list A) d,
  (n < length ct)%nat ->
  nth n ct d :: nil = firstn 1 (skipn n ct).
Proof.
  intros.
  revert ct H; induction n; intros; destruct ct.
  + simpl in H; omega.
  + simpl. reflexivity.
  + simpl in H; omega.
  + simpl in H |- *.
    rewrite IHn by omega.
    reflexivity.
Qed.

Lemma skipn_length: forall {A} (contents: list A) n,
  length (skipn n contents) = (length contents - n)%nat.
Proof.
  intros.
  revert n;
  induction contents;
  intros.
  + destruct n; reflexivity.
  + destruct n; simpl.
    - reflexivity.
    - apply IHcontents.
Qed.

Lemma nth_firstn: forall {A} (contents: list A) n m d,
  (n < m)%nat ->
  nth n (firstn m contents) d = nth n contents d.
Proof.
  intros.
  revert n m H;
  induction contents;
  intros.
  + destruct n, m; reflexivity.
  + destruct n, m; try omega.
    - simpl. reflexivity.
    - simpl. apply IHcontents. omega.
Qed.

(**************************************************

Int type lemmas

**************************************************)

Lemma add_repr: forall i j, Int.add (Int.repr i) (Int.repr j) = Int.repr (i+j).
Proof. intros.
  rewrite Int.add_unsigned.
 apply Int.eqm_samerepr.
 unfold Int.eqm.
 apply Int.eqm_add; apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.

Lemma mul_repr:
 forall x y, Int.mul (Int.repr x) (Int.repr y) = Int.repr (x * y).
Proof.
intros. unfold Int.mul.
apply Int.eqm_samerepr.
repeat rewrite Int.unsigned_repr_eq.
apply Int.eqm_mult; unfold Int.eqm; apply Int.eqmod_sym;
apply Int.eqmod_mod; compute; congruence.
Qed.

Lemma sub_repr: forall i j,
  Int.sub (Int.repr i) (Int.repr j) = Int.repr (i-j).
Proof.
  intros.
 unfold Int.sub.
 apply Int.eqm_samerepr.
 unfold Int.eqm.
 apply Int.eqm_sub; apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.

Lemma Zland_two_p:
 forall i n, (0 <= n)%Z -> Z.land i (Z.ones n) = i mod (2 ^ n).
Proof.
intros.
rewrite Z.land_ones by auto.
reflexivity.
Qed.

Lemma and_repr
     : forall i j : Z, Int.and (Int.repr i) (Int.repr j) = Int.repr (Z.land i j).
Proof.
  intros.
  unfold Int.and.
  rewrite <- (Int.repr_unsigned (Int.repr (Z.land i j))).
  rewrite !Int.unsigned_repr_eq.
  change Int.modulus with (2 ^ 32).
  rewrite <- !Zland_two_p by omega.
  f_equal.
  rewrite <- !Z.land_assoc.
  f_equal.
  rewrite (Z.land_comm (Z.ones 32)).
  rewrite <- !Z.land_assoc.
  f_equal.
Qed.

Lemma or_repr
     : forall i j : Z, Int.or (Int.repr i) (Int.repr j) = Int.repr (Z.lor i j).
Proof.
  intros.
  unfold Int.or.
  rewrite <- (Int.repr_unsigned (Int.repr (Z.lor i j))).
  rewrite !Int.unsigned_repr_eq.
  change Int.modulus with (2 ^ 32).
  rewrite <- !Zland_two_p by omega.
  f_equal.
  rewrite <- Z.land_lor_distr_l.
  reflexivity.
Qed.

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

Lemma skipn_length_short:
  forall {A} n (al: list A), 
    (length al <= n)%nat -> 
    (length (skipn n al) = 0)%nat.
Proof.
 induction n; destruct al; simpl; intros; auto.
 omega.
 apply IHn. omega.
Qed.

Lemma skipn_short:
   forall {A} n (al: list A), (n >= length al)%nat -> skipn n al = nil.
Proof.
intros.
pose proof (skipn_length_short n al).
spec H0; [auto | ].
destruct (skipn n al); inv H0; auto.
Qed.

Arguments Int.unsigned n : simpl never.
Arguments Pos.to_nat !x / .
