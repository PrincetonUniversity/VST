Require Import compcert.lib.Integers.
Require Import Recdef.
Require Import Bvector.
Require Import List. Import ListNotations.
Require Import Arith.
Require Import compcert.lib.Coqlib.
Require Import sha.general_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.XorCorrespondence.
Require Import sha.ByteBitRelations.
Import List.

Definition concat {A : Type} (l : list (list A)) : list A :=
  flat_map id l.

Lemma concat_length {A}: forall L (l:list A), In l L -> (length (concat L) >= length l)%nat.
Proof.  unfold concat. induction L; simpl; intros. contradiction.
  rewrite app_length.
  destruct H; subst. unfold id. omega.
  specialize (IHL _ H). omega.
Qed.

Lemma concat_InBlocks b: forall l (F: Forall (fun x : list bool => length x = b) l),
      InBlocks b (concat l).
induction l; simpl; intros. constructor.
econstructor. 2: reflexivity.
 apply Forall_inv in F; trivial.
 apply IHl. apply Forall_tl in F; trivial.
Qed.

Lemma concat_app {A} (l1 l2:list A): l1 ++ l2 = l1 ++ concat (l2 :: nil).
Proof.
  unfold concat. simpl.
  rewrite -> app_nil_r. reflexivity.
Qed.

(* Replacing splitVector *)
Definition splitList {A : Type} (n : nat) (l : list A) : (list A * list A) :=
  (firstn n l, skipn n l).

Lemma split_append_id : forall {A : Type} (len : nat) (l1 l2 : list A),
                               length l1 = len -> length l2 = len ->
                               splitList len (l1 ++ l2) = (l1, l2).
Proof.
  induction len; intros l1 l2 len1 len2.
  - apply list_nil in len1; apply list_nil in len2.
    subst. reflexivity.
  - unfold splitList.
    rewrite -> firstn_exact. rewrite -> skipn_exact.
    * reflexivity. * assumption. * assumption.
Qed.

(* Replacing BVxor *)
Definition BLxor (xs : Blist) (ys : Blist) :=
  map (fun p => xorb (fst p) (snd p)) (combine xs ys).

Lemma BLxor_length: forall n l1 l2
      (len1: length l1 = n) (len2: length l2 = n), length (BLxor l1 l2) = n.
Proof.
  induction n as [ | n']; intros.
  - apply list_nil in len1. apply list_nil in len2.
    subst. reflexivity.
  - destruct l1; destruct l2; inversion len1; inversion len2.
    simpl.
    rewrite -> map_length.
    rewrite -> combine_length.
    rewrite H0. rewrite H1. simpl.
    f_equal.
    apply min_l.
    omega.
Qed.

Theorem xor_eq : forall (n : nat) (v1 v2 : Bvector.Bvector n),
                   BLxor (Vector.to_list v1) (Vector.to_list v2) =
                   Vector.to_list (Bvector.BVxor n v1 v2).
Proof.
  eapply Vector.rect2.
  reflexivity.
  intros. simpl. rewrite (VectorToList_cons _ _ (xorb a b)).
   rewrite <- H. clear H. unfold BLxor.
   rewrite VectorToList_combine. reflexivity.
Qed.

Lemma inner_general_mapByte : forall (ip : Blist) (IP_list : list byte) (k : Blist) (K : list byte),
                            bytes_bits_lists ip IP_list ->
                            bytes_bits_lists k K ->
     bytes_bits_lists (BLxor k ip)
                          (map (fun p0 : byte * byte => Byte.xor (fst p0) (snd p0))
                                (combine K IP_list)).
Proof.
  intros ip IP_list k K ip_eq k_eq.
  unfold BLxor. simpl.
  generalize dependent IP_list. generalize dependent ip.
  induction k_eq.
  - simpl; intros. constructor.
  - intros. inv ip_eq.
    + constructor.
    + simpl. constructor; auto.
        unfold Byte.xor.
        apply xor_correspondence; auto.
Qed.

Function hash_blocks_bits (b:nat) (B:(0<b)%nat) (hash_block_bit : Blist -> Blist -> Blist) (r: Blist)
         (msg: Blist) {measure length msg} : Blist :=
  match msg with
  | nil => r
  | _ => hash_blocks_bits b B hash_block_bit (hash_block_bit r (firstn b msg)) (skipn b msg)
  end.
Proof. intros.
 destruct (lt_dec (length msg) b).
 rewrite skipn_short. simpl; omega. rewrite <- teq; omega.
 rewrite skipn_length; rewrite <- teq; omega.
Defined.

Lemma add_blocksize_length l n: 0<=n ->
      BinInt.Z.add n (Zcomplements.Zlength l) = Zcomplements.Zlength ((Coqlib.list_repeat (Z.to_nat n) true) ++ l).
Proof. intros. do 2 rewrite Zlength_correct.
  rewrite app_length, length_list_repeat, Nat2Z.inj_add, Z2Nat.id; trivial.
Qed.

Lemma hash_blocks_bits_len c b (B:(0<b)%nat) h
          (HH: forall x y, length x = c -> length y = b -> length (h x y)  = c)
          r l: length r = c ->
      InBlocks b l ->
      length (hash_blocks_bits b B h r l) = c.
Proof.
  apply hash_blocks_bits_ind.
  intros. trivial.
  intros. destruct _x. contradiction. subst msg; clear y.
  inv H1.
  apply H; clear H. rewrite HH. trivial. trivial.
    rewrite H3, firstn_exact; trivial.
    rewrite H3, skipn_exact; trivial.
Qed.
