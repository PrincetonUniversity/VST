Require Import List. Import ListNotations.
Require Import ZArith.
Local Open Scope Z_scope.
Require Import Integers.
Require Import floyd.sublist.
Require Import aes.sbox.
Require Import aes.GF_ops_LL.

Fixpoint repeat_op_table_nat{T: Type}(n: nat)(start: T)(op: T -> T): list T := match n with
| O => []
| S m => (repeat_op_table_nat m start op) ++ [repeat_op_nat m start op]
end.

Definition repeat_op_table{T: Type}(n: Z)(start: T)(op: T -> T): list T :=
  repeat_op_table_nat (Z.to_nat n) start op.

Lemma repeat_op_table_step: forall {T: Type} (i: Z) (start: T) (op: T -> T),
  0 <= i ->
  repeat_op_table (i + 1) start op = (repeat_op_table i start op) ++ [repeat_op i start op].
Proof.
  intros. unfold repeat_op_table. rewrite Z2Nat.inj_add by omega.
  rewrite Nat.add_1_r. simpl. reflexivity.
Qed.

Lemma repeat_op_table_nat_length: forall {T: Type} (i: nat) (x: T) (f: T -> T),
  length (repeat_op_table_nat i x f) = i.
Proof.
  intros. induction i. reflexivity. simpl. rewrite app_length. simpl.
  rewrite IHi. omega.
Qed.

Lemma repeat_op_table_length: forall {T: Type} (i: Z) (x: T) (f: T -> T),
  0 <= i ->
  Zlength (repeat_op_table i x f) = i.
Proof.
  intros. unfold repeat_op_table.
  rewrite Zlength_correct. rewrite repeat_op_table_nat_length.
  apply Z2Nat.id. assumption.
Qed.

Lemma repeat_op_nat_id: forall {T: Type} (n: nat) (v: T),
  repeat_op_nat n v id = v.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Lemma repeat_op_table_nat_id_app: forall {T: Type} (len1 len2: nat) (v: T),
  repeat_op_table_nat (len1 + len2) v id 
  = repeat_op_table_nat len1 v id ++ repeat_op_table_nat len2 v id.
Proof.
  intros. induction len2.
  - simpl. replace (len1 + 0)%nat with len1 by omega. rewrite app_nil_r. reflexivity.
  - replace (len1 + S len2)%nat with (S (len1 + len2)) by omega. simpl.
    rewrite IHlen2. rewrite <- app_assoc. f_equal. f_equal. do 2 rewrite repeat_op_nat_id.
    reflexivity.
Qed.

Lemma sublist_repeat_op_table_id: forall {T: Type} (lo n: Z) (v: T),
  0 <= lo ->
  0 <= n ->
  sublist lo (lo + n) (repeat_op_table (lo + n) v id) = repeat_op_table n v id.
Proof.
  intros.
  replace (lo + n) with (Zlength (repeat_op_table (lo + n) v id)) at 1
    by (apply repeat_op_table_length; omega).
  rewrite sublist_skip by omega.
  unfold repeat_op_table at 1. rewrite Z2Nat.inj_add by omega.
  rewrite repeat_op_table_nat_id_app.
  rewrite Zskipn_app1 by (
    rewrite Zlength_correct;
    rewrite repeat_op_table_nat_length;
    rewrite Z2Nat.id; omega
  ).
  rewrite skipn_short; [ reflexivity | ].
  rewrite repeat_op_table_nat_length. omega.
Qed.

Fixpoint fill_list_nat{T: Type}(n: nat)(f: nat -> T): list T := match n with
| O => []
| S m => (fill_list_nat m f) ++ [f m]
end.

Definition fill_list{T: Type}(n: Z)(f: Z -> T): list T :=
  fill_list_nat (Z.to_nat n) (fun i => f (Z.of_nat i)).

Lemma fill_list_step: forall {T: Type} (n: Z) (f: Z -> T),
  0 <= n ->
  fill_list (n + 1) f = fill_list n f ++ [f n].
Proof.
  intros. unfold fill_list. rewrite Z2Nat.inj_add by omega.
  rewrite Nat.add_1_r. simpl. rewrite Z2Nat.id by omega. reflexivity.
Qed.

Definition rot8(i: int): int := 
  Int.or (Int.and (Int.shl i (Int.repr 8)) (Int.repr (-1))) (Int.shru i (Int.repr 24)).

Definition FSb := map Int.repr sbox.
Definition RSb := map Int.repr inv_sbox.

Definition calc_FT0(i: Z): int :=
  (Int.xor (Int.xor (Int.xor 
     (times2 (Znth i FSb Int.zero)) 
     (Int.shl (Znth i FSb Int.zero) (Int.repr 8)))
     (Int.shl (Znth i FSb Int.zero) (Int.repr 16)))
     (Int.shl (Int.and (Int.xor (times2 (Znth i FSb Int.zero)) (Znth i FSb Int.zero))
                       (Int.repr 255))
              (Int.repr 24))).
Definition calc_FT1(i: Z): int := rot8 (calc_FT0 i).
Definition calc_FT2(i: Z): int := rot8 (calc_FT1 i).
Definition calc_FT3(i: Z): int := rot8 (calc_FT2 i).
Definition calc_RT0(i: Z): int :=
  Int.xor (Int.xor (Int.xor
           (mul (Int.repr 14) (Int.repr (Int.unsigned (Znth i RSb Int.zero))))
  (Int.shl (mul (Int.repr  9) (Int.repr (Int.unsigned (Znth i RSb Int.zero)))) (Int.repr  8)))
  (Int.shl (mul (Int.repr 13) (Int.repr (Int.unsigned (Znth i RSb Int.zero)))) (Int.repr 16)))
  (Int.shl (mul (Int.repr 11) (Int.repr (Int.unsigned (Znth i RSb Int.zero)))) (Int.repr 24)).
Definition calc_RT1(i: Z): int := rot8 (calc_RT0 i).
Definition calc_RT2(i: Z): int := rot8 (calc_RT1 i).
Definition calc_RT3(i: Z): int := rot8 (calc_RT2 i).

Global Opaque calc_FT0 calc_FT1 calc_FT2 calc_FT2 calc_RT0 calc_RT1 calc_RT2 calc_RT3.

Definition FT0 := fill_list 256 calc_FT0.
Definition FT1 := fill_list 256 calc_FT1.
Definition FT2 := fill_list 256 calc_FT2.
Definition FT3 := fill_list 256 calc_FT3.
Definition RT0 := fill_list 256 calc_RT0.
Definition RT1 := fill_list 256 calc_RT1.
Definition RT2 := fill_list 256 calc_RT2.
Definition RT3 := fill_list 256 calc_RT3.
Definition RCON := repeat_op_table 10 Int.one times2.

(* If entailer! and go_lower unfold these, they become too slow *)
Global Opaque FSb FT0 FT1 FT2 FT3 RSb RT0 RT1 RT2 RT3 RCON.

(* TODO Can we achieve the same with "Arguments"?
   "Arguments FSb : simpl never." (etc) does not seem to work *)
