Require Export List. Export ListNotations.
Require Import ZArith.
Local Open Scope Z_scope.
Require Import VST.floyd.sublist.

Fixpoint repeat_op_nat{T: Type}(n: nat)(start: T)(op: T -> T): T := match n with
| O => start
| S m => op (repeat_op_nat m start op)
end.

Definition repeat_op{T: Type}(n: Z)(start: T)(op: T -> T): T := repeat_op_nat (Z.to_nat n) start op.

Lemma repeat_op_step: forall {T: Type} (i: Z) (start: T) (op: T -> T),
  0 <= i ->
  repeat_op (i + 1) start op = op (repeat_op i start op).
Proof.
  intros. unfold repeat_op. rewrite Z2Nat.inj_add by omega.
  rewrite Nat.add_1_r. simpl. reflexivity.
Qed.

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

Ltac eval_list l :=
  let l' := eval hnf in l in lazymatch l' with
  | ?h :: ?tl => let tl' := eval_list tl in constr:(h :: tl')
  | (@nil ?T) => constr:(@nil T)
  end.
