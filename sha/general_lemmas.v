Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import compcert.lib.Integers.
Require Import VST.msl.Coqlib2.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.sublist.
Require Import VST.floyd.functional_base.

(*
Definition Vubyte (c: Byte.int) : val :=
  Vint (Int.repr (Byte.unsigned c)).

Lemma Znth_map_Vubyte: forall (i : Z) (l : list byte),
  0 <= i < Zlength l -> Znth i (map Vubyte l)  = Vubyte (Znth i l).
Proof.
  intros i l.
  apply Znth_map.
Qed.
Locate Znth_map_Vubyte.
Hint Rewrite Znth_map_Vubyte using list_solve : norm entailer_rewrite.
*)
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

(*Definition isbyteZ (i: Z) := (0 <= i < 256)%Z. *)

Definition Shr b x := Int.shru x (Int.repr b).

Lemma byte_testbit:
  forall i j, j >= 8 -> Z.testbit (Byte.unsigned i) j = false.
Proof.
intros. 
apply (Byte.Ztestbit_above 8).
apply Byte.unsigned_range.
apply H.
Qed.

Fixpoint intlist_to_bytelist (l: list int) : list byte :=
 match l with
 | nil => nil
 | i::r =>
     Byte.repr (Int.unsigned (Shr 24 i)) ::
     Byte.repr (Int.unsigned (Shr 16 i)) ::
     Byte.repr (Int.unsigned (Shr 8 i)) ::
     Byte.repr (Int.unsigned i) ::
     intlist_to_bytelist r
 end.

Definition bytes_to_Int (a b c d : byte) : Int.int :=
  Int.or (Int.or (Int.or 
       (Int.shl (Int.repr (Byte.unsigned a)) (Int.repr 24))
      (Int.shl (Int.repr (Byte.unsigned b)) (Int.repr 16)))
       (Int.shl (Int.repr (Byte.unsigned c)) (Int.repr 8)))
         (Int.repr (Byte.unsigned d)).

Fixpoint bytelist_to_intlist (nl: list byte) : list int :=
  match nl with
  | h1::h2::h3::h4::t => bytes_to_Int h1 h2 h3 h4 :: bytelist_to_intlist t
  | _ => nil
  end.

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
Hint Rewrite Int.unsigned_repr using rep_omega : testbit.
Hint Rewrite Byte.testbit_repr using rep_omega : testbit.
Hint Rewrite Byte.bits_above using rep_omega : testbit.

Lemma Ztest_Inttest:
 forall a, Z.testbit (Int.unsigned a) = Int.testbit a.
Proof. reflexivity. Qed.
Hint Rewrite Ztest_Inttest : testbit.

Lemma Ztest_Bytetest:
 forall a, Z.testbit (Byte.unsigned a) = Byte.testbit a.
Proof. reflexivity. Qed.
Hint Rewrite Ztest_Bytetest : testbit.

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

Lemma length_intlist_to_bytelist:
  forall l, length (intlist_to_bytelist l) = (4 * length l)%nat.
Proof.
induction l.
simpl. reflexivity. simpl. omega.
Qed.


Lemma intlist_to_bytelist_bytes_to_int_cons:
  forall a b c d l,
     intlist_to_bytelist (bytes_to_Int a b c d :: l) =
     a::b::c::d:: intlist_to_bytelist l.
Proof.
intros. simpl.
assert (Int.zwordsize=32)%Z by reflexivity.
unfold bytes_to_Int, Shr; simpl.
change 255%Z with (Z.ones 8).
assert (Byte.zwordsize = 8) by reflexivity.
assert (Int.zwordsize = 32) by reflexivity.
repeat f_equal; auto;
apply Byte.same_bits_eq; intros;
assert (0 <= i < Int.zwordsize) by omega;
rewrite Byte.testbit_repr by auto;
autorewrite with testbit.
*
rewrite (Byte.bits_above b) by omega.
rewrite (Byte.bits_above c) by omega.
rewrite !orb_false_r. auto.
*
rewrite (Byte.bits_above c) by omega.
rewrite !orb_false_r. auto.
*
auto.
*
auto.
Qed.

Lemma intlist_to_bytelist_to_intlist:
  forall il: list int,
   bytelist_to_intlist (intlist_to_bytelist il) = il.
Proof.
induction il.
reflexivity.
simpl.
f_equal; auto. clear.
assert (Byte.zwordsize = 8) by reflexivity.
assert (Int.zwordsize=32)%Z by reflexivity.
unfold bytes_to_Int, Shr; simpl.
apply Int.same_bits_eq; intros.
autorewrite with testbit.
destruct (zlt i 8); simpl.
rewrite !if_true by omega; simpl.
autorewrite with testbit; auto.
destruct (zlt i 16); simpl.
rewrite !if_true by omega; simpl.
autorewrite with testbit.
f_equal; omega.
destruct (zlt i 24); simpl.
autorewrite with testbit.
f_equal; omega.
autorewrite with testbit.
f_equal; omega.
Qed.

Lemma intlist_to_bytelist_app:
 forall al bl, intlist_to_bytelist (al++bl) = intlist_to_bytelist al ++ intlist_to_bytelist bl.
Proof. intros; induction al; simpl; auto. repeat f_equal; auto. Qed.
Local Open Scope nat.

Local Open Scope Z.

(*
Lemma isbyte_intlist_to_Zlist' : forall l,
   Forall isbyteZ (map Int.unsigned (map Int.repr (intlist_to_Zlist l))).
Proof.
intro.
replace (map Int.unsigned (map Int.repr (intlist_to_Zlist l))) with (intlist_to_Zlist l).
apply isbyte_intlist_to_Zlist.
induction l; simpl; auto.
repeat f_equal; auto; symmetry; apply Int.repr_unsigned.
Qed.
*)

(*
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
*)

Lemma int_unsigned_inj: forall a b, Int.unsigned a = Int.unsigned b -> a=b.
Proof.
intros.
rewrite <- (Int.repr_unsigned a); rewrite <- (Int.repr_unsigned b).
congruence.
Qed.

Lemma intlist_to_bytelist_inj: forall al bl, intlist_to_bytelist al = intlist_to_bytelist bl -> al=bl.
Proof.
induction al; destruct bl; intros; auto.
inv H.
inv H.
simpl in H.
match type of H with ?a::?b::?c::?d::?e = ?A::?B::?C::?D::?E =>
  assert (a=A /\ b=B /\ c=C /\ d=D /\ e=E)
  by (repeat split; congruence)
end. decompose [and] H0; clear H H0.
f_equal; auto.
clear - H1 H2 H3 H4.
rename i into b.
apply Int.same_bits_eq; intros.
assert (Byte.zwordsize = 8) by reflexivity.
assert (Int.zwordsize=32)%Z by reflexivity.
destruct (zlt i 8); [ | destruct (zlt i 16); [ | destruct (zlt i 24)]].
*
rewrite <- ?Ztest_Inttest.
rewrite <- ?Byte.testbit_repr by rep_omega.
congruence.
*
pose proof (Int.bits_shru a (Int.repr 8) (i-8)).
spec H6; [rep_omega|].
rewrite !Int.unsigned_repr in H6 by rep_omega.
rewrite Z.sub_add in H6.
rewrite if_true in H6 by omega.
pose proof (Int.bits_shru b (Int.repr 8) (i-8)).
spec H7; [rep_omega|].
rewrite !Int.unsigned_repr in H7 by rep_omega.
rewrite Z.sub_add in H7.
rewrite if_true in H7 by omega.
rewrite <- H6. rewrite <- H7.
rewrite <- ?Ztest_Inttest.
rewrite <- ?Byte.testbit_repr by rep_omega.
f_equal. apply H2.
*
pose proof (Int.bits_shru a (Int.repr 16) (i-16)).
spec H6; [rep_omega|].
rewrite !Int.unsigned_repr in H6 by rep_omega.
rewrite Z.sub_add in H6.
rewrite if_true in H6 by omega.
pose proof (Int.bits_shru b (Int.repr 16) (i-16)).
spec H7; [rep_omega|].
rewrite !Int.unsigned_repr in H7 by rep_omega.
rewrite Z.sub_add in H7.
rewrite if_true in H7 by omega.
rewrite <- H6. rewrite <- H7.
rewrite <- ?Ztest_Inttest.
rewrite <- ?Byte.testbit_repr by rep_omega.
f_equal. apply H3.
*
pose proof (Int.bits_shru a (Int.repr 24) (i-24)).
spec H6; [rep_omega|].
rewrite !Int.unsigned_repr in H6 by rep_omega.
rewrite Z.sub_add in H6.
rewrite if_true in H6 by omega.
pose proof (Int.bits_shru b (Int.repr 24) (i-24)).
spec H7; [rep_omega|].
rewrite !Int.unsigned_repr in H7 by rep_omega.
rewrite Z.sub_add in H7.
rewrite if_true in H7 by omega.
rewrite <- H6. rewrite <- H7.
rewrite <- ?Ztest_Inttest.
rewrite <- ?Byte.testbit_repr by rep_omega.
f_equal. apply H1.
Qed.

Lemma Zlength_intlist_to_bytelist_app:
 forall al bl,  Zlength (intlist_to_bytelist (al++bl)) =
    (Zlength (intlist_to_bytelist al) + Zlength (intlist_to_bytelist bl))%Z.
Proof.
induction al; simpl; intros; auto.
repeat rewrite Zlength_cons.
rewrite IHal.
omega.
Qed.

Local Open Scope Z.

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
