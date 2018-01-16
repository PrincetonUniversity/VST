Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import compcert.lib.Integers.
Require Import VST.msl.Coqlib2.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.sublist.


Local Open Scope nat.

Fixpoint map2 {A B C: Type} (f: A -> B -> C) (al: list A) (bl: list B) : list C :=
 match al, bl with
  | a::al', b::bl' => f a b :: map2 f al' bl'
  | _, _ => nil
  end.

Lemma length_map2:
 forall A B C (f: A -> B -> C) al bl n,
  length al = n -> length bl = n ->
  length (map2 f al bl) = n.
Proof.
induction al; destruct bl,n; simpl; intros; auto.
inv H.
Qed.

Lemma list_repeat_injective {A} (a a':A) n: (0<n)%nat ->
      list_repeat n a = list_repeat n a' -> a=a'.
  Proof. intros.
    destruct n. omega. simpl in H0. inversion H0. trivial.
  Qed.

Local Open Scope Z.

Definition roundup (a b : Z) := (a + (b-1))/b*b.

Lemma roundup_minus:
   forall a b,  b > 0 -> roundup a b - a = (- a) mod b.
Proof.
unfold roundup; intros.
replace (a+(b-1)) with (a-1+1*b) by omega.
rewrite Z_div_plus_full by omega.
rewrite Z.mul_add_distr_r.
assert (H4 := Zmod_eq a b H).
assert (a mod b = 0 \/ a mod b <> 0) by omega.
destruct H0; [rewrite Z.mod_opp_l_z | rewrite Z.mod_opp_l_nz]; try omega.
rewrite H0 in H4.
assert (a = a/b*b) by omega.
rewrite H1 at 1.
replace (a/b*b-1) with (a/b*b+ -1) by omega.
rewrite Z_div_plus_full_l by omega.
rewrite Z.mul_add_distr_r.
rewrite <- H1.
assert (b=1 \/ b>1) by omega.
destruct H2.
subst b. simpl. omega.
rewrite (Z_div_nz_opp_full 1) by (rewrite Z.mod_small; omega).
rewrite  Z.div_small by omega.
omega.
rewrite H4.
assert ( (a-1)/b*b = a/b*b); [ | omega].
f_equal.
assert (a = a mod b + a/b*b) by omega.
replace (a-1) with (a mod b - 1 + a/b*b) by omega.
rewrite Z_div_plus_full by omega.
rewrite Z.div_small; try omega.
pose proof (Z_mod_lt a b H).
omega.
Qed.

Definition isbyteZ (i: Z) := (0 <= i < 256)%Z.

Definition Shr b x := Int.shru x (Int.repr b).

Lemma isbyteZ_testbit:
  forall i j, 0 <= i < 256 -> j >= 8 -> Z.testbit i j = false.
Proof.
intros; erewrite Byte.Ztestbit_above with (n:=8%nat); auto.
Qed.

Fixpoint intlist_to_Zlist (l: list int) : list Z :=
 match l with
 | nil => nil
 | i::r =>
     Int.unsigned (Shr 24 i) ::
     Int.unsigned (Int.and (Shr 16 i) (Int.repr 255)) ::
     Int.unsigned (Int.and (Shr 8 i) (Int.repr 255)) ::
     Int.unsigned (Int.and i (Int.repr 255)) ::
     intlist_to_Zlist r
 end.

(*combining four Z into a Integer*)
Definition Z_to_Int (a b c d : Z) : Int.int :=
  Int.or (Int.or (Int.or (Int.shl (Int.repr a) (Int.repr 24)) (Int.shl (Int.repr b) (Int.repr 16)))
            (Int.shl (Int.repr c) (Int.repr 8))) (Int.repr d).

Fixpoint Zlist_to_intlist (nl: list Z) : list int :=
  match nl with
  | h1::h2::h3::h4::t => Z_to_Int h1 h2 h3 h4 :: Zlist_to_intlist t
  | _ => nil
  end.

Lemma int_min_signed_eq: Int.min_signed = -2147483648.
Proof. reflexivity. Qed.

Lemma int_max_signed_eq: Int.max_signed = 2147483647.
Proof. reflexivity. Qed.

Lemma int_max_unsigned_eq: Int.max_unsigned = 4294967295.
Proof. reflexivity. Qed.


Ltac rep_omega' :=
   pose proof int_min_signed_eq;
   pose proof int_max_signed_eq;
   pose proof int_max_unsigned_eq;
   omega.

Hint Rewrite Int.bits_or using omega : testbit.
Hint Rewrite Int.bits_shl using omega : testbit.
Hint Rewrite Int.bits_and using omega : testbit.
Hint Rewrite Int.bits_shru using omega : testbit.
Hint Rewrite Int.unsigned_repr using omega : testbit.
Hint Rewrite Int.testbit_repr using omega : testbit.
Hint Rewrite if_false using omega : testbit.
Hint Rewrite if_true using omega : testbit.
Hint Rewrite Z.ones_spec_low using omega : testbit.
Hint Rewrite Z.ones_spec_high using omega : testbit.
Hint Rewrite orb_false_r orb_true_r andb_false_r andb_true_r : testbit.
Hint Rewrite orb_false_l orb_true_l andb_false_l andb_true_l : testbit.
Hint Rewrite Z.add_simpl_r : testbit.
Hint Rewrite Int.unsigned_repr using rep_omega' : testbit.

Lemma Ztest_Inttest:
 forall a, Z.testbit (Int.unsigned a) = Int.testbit a.
Proof. reflexivity. Qed.
Hint Rewrite Ztest_Inttest : testbit.

Definition swap (i: int) : int :=
 Int.or (Int.shl (Int.and i (Int.repr 255)) (Int.repr 24))
   (Int.or (Int.shl (Int.and (Shr 8 i) (Int.repr 255)) (Int.repr 16))
      (Int.or (Int.shl (Int.and (Shr 16 i) (Int.repr 255)) (Int.repr 8))
         (Shr 24 i))).

Lemma swap_swap: forall w, swap (swap w) = w.
Proof.
unfold swap, Shr; intros.
apply Int.same_bits_eq; intros.
assert (Int.zwordsize=32) by reflexivity.
change 255 with (Z.ones 8).
assert (32 < Int.max_unsigned) by (compute; auto).
autorewrite with testbit.
if_tac; [if_tac; [if_tac | ] | ]; autorewrite with testbit; f_equal; omega.
Qed.

Lemma map_swap_involutive:
 forall l, map swap (map swap l)  = l.
Proof. intros.
 rewrite map_map.
 replace (fun x => swap (swap x)) with (@Datatypes.id int).
 apply map_id. extensionality x. symmetry; apply swap_swap.
Qed.

Lemma length_intlist_to_Zlist:
  forall l, length (intlist_to_Zlist l) = (4 * length l)%nat.
Proof.
induction l.
simpl. reflexivity. simpl. omega.
Qed.


Lemma intlist_to_Zlist_Z_to_int_cons:
  forall a b c d l,
      isbyteZ a -> isbyteZ b -> isbyteZ c -> isbyteZ d ->
     intlist_to_Zlist (Z_to_Int a b c d :: l) =
     a::b::c::d:: intlist_to_Zlist l.
Proof.
intros. simpl.
unfold isbyteZ in *.
assert (Int.zwordsize=32)%Z by reflexivity.
unfold Z_to_Int, Shr; simpl.
change 255%Z with (Z.ones 8).
repeat f_equal; auto;
match goal with |- _ = ?A => transitivity (Int.unsigned (Int.repr A));
   [f_equal | apply Int.unsigned_repr; rep_omega']
end;
apply Int.same_bits_eq; intros;
autorewrite with testbit.
*
if_tac; autorewrite with testbit; [ | symmetry; apply isbyteZ_testbit; omega].
rewrite (isbyteZ_testbit b) by omega.
rewrite (isbyteZ_testbit c) by omega.
rewrite (isbyteZ_testbit d) by omega.
autorewrite with testbit; auto.
*
if_tac; autorewrite with testbit; [ | symmetry; apply isbyteZ_testbit; omega].
if_tac; autorewrite with testbit; [ | symmetry; apply isbyteZ_testbit; omega].
rewrite (isbyteZ_testbit c) by omega.
rewrite (isbyteZ_testbit d) by omega.
autorewrite with testbit; auto.
*
if_tac; autorewrite with testbit; [ | symmetry; apply isbyteZ_testbit; omega].
if_tac; autorewrite with testbit; [ | symmetry; apply isbyteZ_testbit; omega].
if_tac; autorewrite with testbit; [ | symmetry; apply isbyteZ_testbit; omega].
rewrite (isbyteZ_testbit d) by omega.
autorewrite with testbit; auto.
*
destruct (zlt i 8); autorewrite with testbit;  [ | symmetry; apply isbyteZ_testbit; omega].
auto.
Qed.

Lemma intlist_to_Zlist_to_intlist:
  forall il: list int,
   Zlist_to_intlist (intlist_to_Zlist il) = il.
Proof.
induction il.
reflexivity.
simpl.
f_equal; auto. clear.
assert (Int.zwordsize=32)%Z by reflexivity.
unfold Z_to_Int, Shr; simpl.
change 255%Z with (Z.ones 8).
apply Int.same_bits_eq; intros.
rewrite Int.repr_unsigned.
autorewrite with testbit.
if_tac; autorewrite with testbit; [ | f_equal; omega].
if_tac; autorewrite with testbit; [ | f_equal; omega].
if_tac; autorewrite with testbit; [ | f_equal; omega].
auto.
Qed.

Lemma intlist_to_Zlist_app:
 forall al bl, intlist_to_Zlist (al++bl) = intlist_to_Zlist al ++ intlist_to_Zlist bl.
Proof. intros; induction al; simpl; auto. repeat f_equal; auto. Qed.
Local Open Scope nat.


Local Open Scope Z.

Lemma isbyte_intlist_to_Zlist : forall l, Forall isbyteZ (intlist_to_Zlist l).
Proof.
induction l; simpl; intros.
constructor.
assert (forall i, Int.unsigned (Int.and i (Int.repr 255)) < 256).
clear; intro.
eapply Z.lt_le_trans.
apply (Int.and_interval i (Int.repr (Z.ones 8))).
change (Int.size  (Int.repr (Z.ones 8))) with 8.
rewrite Zmin_spec.
if_tac.
eapply Z.le_trans with (two_p 8).
apply two_p_monotone.
split; [ | omega].
apply Int.size_range.
compute; congruence.
compute; congruence.
unfold Shr, isbyteZ; repeat constructor; try apply Int.unsigned_range; auto; clear IHl.
rewrite <- (Int.divu_pow2 a (Int.repr (2 ^ 24)) (Int.repr 24) (eq_refl _)).
unfold Int.divu.
rewrite Int.unsigned_repr.
rewrite Int.unsigned_repr by (compute; split; congruence).
apply Z.div_lt_upper_bound.
compute; congruence.
change (2 ^ 24 * 256)%Z with (Int.modulus).
apply Int.unsigned_range.
assert (0 < 2 ^ 24)
 by (apply Z.pow_pos_nonneg; clear; omega).
rewrite Int.unsigned_repr by (compute; split; congruence).
split.
apply Z.div_pos; auto.
apply Int.unsigned_range.
apply Z.div_le_upper_bound; auto.
apply Z.le_trans with (Int.modulus+1).
destruct (Int.unsigned_range a).
omega.
compute; congruence.
Qed.

Lemma isbyte_intlist_to_Zlist' : forall l,
   Forall isbyteZ (map Int.unsigned (map Int.repr (intlist_to_Zlist l))).
Proof.
intro.
replace (map Int.unsigned (map Int.repr (intlist_to_Zlist l))) with (intlist_to_Zlist l).
apply isbyte_intlist_to_Zlist.
induction l; simpl; auto.
repeat f_equal; auto; symmetry; apply Int.repr_unsigned.
Qed.

Lemma Forall_isbyte_repr_unsigned:
 forall l: list int, map Int.repr (map Int.unsigned l) = l.
Proof.
induction l; intros.
reflexivity.
simpl.
f_equal; auto.
apply Int.repr_unsigned.
Qed.

Lemma map_unsigned_repr_isbyte:
  forall l : list Z , Forall isbyteZ l -> map Int.unsigned (map Int.repr l) = l.
Proof. induction l; simpl; intros; auto.
  inv H. f_equal; auto. unfold isbyteZ in H2; apply Int.unsigned_repr.
 assert (Int.max_unsigned > 256)%Z by (compute; congruence).
 omega.
Qed.

Lemma int_unsigned_inj: forall a b, Int.unsigned a = Int.unsigned b -> a=b.
Proof.
intros.
rewrite <- (Int.repr_unsigned a); rewrite <- (Int.repr_unsigned b).
congruence.
Qed.

Lemma intlist_to_Zlist_inj: forall al bl, intlist_to_Zlist al = intlist_to_Zlist bl -> al=bl.
Proof.
induction al; destruct bl; intros; auto.
inv H.
inv H.
simpl in H.
injection H; intros.
f_equal; auto.
clear - H1 H2 H3 H4.
rename i into b.
apply int_unsigned_inj in H1.
apply int_unsigned_inj in H2.
apply int_unsigned_inj in H3.
apply int_unsigned_inj in H4.
unfold Shr in *.
apply Int.same_bits_eq; intros.
assert (Int.zwordsize=32)%Z by reflexivity.
change 255%Z with (Z.ones 8) in *.
destruct (zlt i 8).
transitivity (Int.testbit (Int.and a (Int.repr (Z.ones 8))) i).
autorewrite with testbit; auto.
rewrite H1. autorewrite with testbit; auto.
destruct (zlt i 16).
transitivity (Int.testbit (Int.and (Int.shru a (Int.repr 8)) (Int.repr (Z.ones 8))) (i-8)).
autorewrite with testbit.
change (Int.unsigned (Int.repr 8)) with 8%Z.
rewrite Z.sub_add; auto.
rewrite H2.
autorewrite with testbit.
rewrite Z.sub_add. auto.
destruct (zlt i 24).
transitivity (Int.testbit (Int.and (Int.shru a (Int.repr 16)) (Int.repr (Z.ones 8))) (i-16)).
autorewrite with testbit.
change (Int.unsigned (Int.repr 16)) with 16%Z.
rewrite Z.sub_add. auto.
rewrite H3.
autorewrite with testbit.
change (Int.unsigned (Int.repr 16)) with 16%Z.
rewrite Z.sub_add. auto.
transitivity (Int.testbit (Int.shru a (Int.repr 24)) (i-24)).
autorewrite with testbit.
change (Int.unsigned (Int.repr 24)) with 24%Z.
rewrite Z.sub_add. auto.
rewrite H4.
autorewrite with testbit.
change (Int.unsigned (Int.repr 24)) with 24%Z.
rewrite Z.sub_add. auto.
Qed.

Lemma Zlength_intlist_to_Zlist_app:
 forall al bl,  Zlength (intlist_to_Zlist (al++bl)) =
    (Zlength (intlist_to_Zlist al) + Zlength (intlist_to_Zlist bl))%Z.
Proof.
induction al; simpl; intros; auto.
repeat rewrite Zlength_cons.
rewrite IHal.
omega.
Qed.

Local Open Scope Z.

Lemma Forall_isbyteZ_unsigned_repr:
 forall l, Forall isbyteZ l -> Forall isbyteZ (map Int.unsigned (map Int.repr l)).
Proof. induction 1. constructor.
constructor. rewrite Int.unsigned_repr; auto.
unfold isbyteZ in H; rep_omega'.
apply IHForall.
Qed.

Lemma divide_length_app:
 forall {A} n (al bl: list A),
      (n | Zlength al) ->
      (n | Zlength bl) ->
      (n | Zlength (al++bl)).
Proof.
 intros. destruct H,H0. exists (x+x0)%Z.
 rewrite Zlength_app,H,H0;
 rewrite Z.mul_add_distr_r; omega.
Qed.

Lemma nth_list_repeat: forall A i n (x :A),
    nth i (list_repeat n x) x = x.
Proof.
 induction i; destruct n; simpl; auto.
Qed.

Lemma map_list_repeat:
  forall A B (f: A -> B) n x,
     map f (list_repeat n x) = list_repeat n (f x).
Proof. induction n; simpl; intros; f_equal; auto.
Qed.

Lemma isbyteZ_sublist data lo hi: Forall isbyteZ data -> Forall isbyteZ (sublist lo hi data).
Proof. intros. destruct (Forall_forall isbyteZ data) as [F _].
   apply Forall_forall. intros. apply (F H x). eapply sublist_In. apply H0.
Qed.

Lemma map_IntReprOfBytes_injective: forall l m, Forall isbyteZ  l -> 
  Forall isbyteZ m -> map Int.repr l = map Int.repr m -> l=m.
Proof. induction l; intros.
+ destruct m; simpl in *; inv H1; trivial.
+ destruct m; simpl in *. inv H1.
  assert (Int.repr a = Int.repr z /\  map Int.repr l = map Int.repr m).
  { forget (Int.repr a) as q. forget (Int.repr z) as w. inv H1; split; trivial. }
  clear H1. destruct H2. inv H. inv H0.
  rewrite (IHl m); trivial. f_equal.
  clear IHl H2 H6 H7.
  unfold isbyteZ in *. simpl in *.
  rewrite <- (Int.unsigned_repr a), <- (Int.unsigned_repr z), H1; trivial;
  rewrite int_max_unsigned_eq; omega.
Qed.
