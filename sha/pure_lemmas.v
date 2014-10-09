(* THIS FILE CONTAINS
   Lemmas that DO NOT depend on CompCert or Verifiable C,
   and that are used in the proof of the C program but are not
   used in the proof of functional_prog.v.
*)

Require Recdef.
Require Import Integers.
Require Coq.Strings.String.
Require Coq.Strings.Ascii.
Require Import Coqlib.
Require Import List. Import ListNotations.
Require Import sha.SHA256.
Require Import msl.Coqlib2.
Require Export sha.common_lemmas.
Require Psatz.

Global Opaque CBLOCKz LBLOCKz.


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

Lemma int_min_signed_eq: Int.min_signed = -2147483648.
Proof. reflexivity. Qed.

Lemma int_max_signed_eq: Int.max_signed = 2147483647.
Proof. reflexivity. Qed.

Lemma int_max_unsigned_eq: Int.max_unsigned = 4294967295.
Proof. reflexivity. Qed.

Ltac repable_signed := 
   pose proof int_min_signed_eq; 
   pose proof int_max_signed_eq; 
   pose proof int_max_unsigned_eq; 
(*   unfold repable_signed in *; *)
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
Hint Rewrite Int.unsigned_repr using repable_signed : testbit.

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

Lemma isbyteZ_testbit:
  forall i j, 0 <= i < 256 -> j >= 8 -> Z.testbit i j = false.
Proof.
intros; erewrite Byte.Ztestbit_above with (n:=8%nat); auto.
Qed.

Lemma length_intlist_to_Zlist:
  forall l, length (intlist_to_Zlist l) = (4 * length l)%nat.
Proof.
induction l.
simpl. reflexivity. simpl. omega.
Qed.

Lemma Zlength_intlist_to_Zlist: forall l,
  Zlength (intlist_to_Zlist l) = WORD*Zlength l.
Proof.
intros. repeat rewrite Zlength_correct. rewrite length_intlist_to_Zlist.
rewrite Nat2Z.inj_mul. reflexivity.
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
   [f_equal | apply Int.unsigned_repr; repable_signed]
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

Lemma Zlist_to_intlist_to_Zlist:
  forall nl: list Z, 
  NPeano.divide (Z.to_nat WORD) (length nl) ->
  Forall isbyteZ nl ->
  intlist_to_Zlist (Zlist_to_intlist nl) = nl.
Proof.
intros nl [k H].
revert nl H; induction k; intros.
destruct nl; inv H; reflexivity.
simpl in H.
destruct nl as [ | a [ | b [ | c [ | d ?]]]]; inv H.
inv H0. inv H4. inv H5. inv H6.
unfold Zlist_to_intlist; fold Zlist_to_intlist.
rewrite intlist_to_Zlist_Z_to_int_cons by auto.
repeat f_equal; auto.
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


Lemma length_Zlist_to_intlist: forall n l, 
       length l = (Z.to_nat WORD * n)%nat -> 
       length (Zlist_to_intlist l) = n.
Proof.
induction n; intros.
destruct l; inv H; reflexivity.
replace (S n) with (1 + n)%nat in H by omega.
rewrite mult_plus_distr_l in H.
destruct l as [|i0 l]; [ inv H |].
destruct l as [|i1 l]; [ inv H |].
destruct l as [|i2 l]; [ inv H |].
destruct l as [|i3 l]; [ inv H |].
simpl. f_equal. apply IHn. forget (Z.to_nat WORD * n)%nat as A. inv H; auto.
Qed.

Lemma big_endian_integer_ext:
 forall f f', (forall z, (0 <= z < WORD)%Z -> f z = f' z) ->
    big_endian_integer f = big_endian_integer f'.
Proof.
unfold big_endian_integer;
intros.
repeat f_equal; intros; apply H; repeat split; compute; auto; congruence.
Qed.


Local Open Scope nat.

Definition LBLOCK : nat := Z.to_nat LBLOCKz.   
Definition CBLOCK : nat := Z.to_nat CBLOCKz.
Opaque LBLOCK CBLOCK.

Lemma LBLOCK_zeq: Z.of_nat LBLOCK = 16%Z.
Proof. reflexivity. Qed.

Lemma CBLOCK_zeq: (Z.of_nat CBLOCK = 64%Z).
Proof. reflexivity. Qed.

Lemma LBLOCKz_nonneg: (0 <= LBLOCKz)%Z.
Proof. change LBLOCKz with 16%Z; omega. Qed.
Hint Resolve LBLOCKz_nonneg.

Lemma LBLOCKz_pos: (0 < LBLOCKz)%Z.
Proof. change LBLOCKz with 16%Z; omega. Qed.
Hint Resolve LBLOCKz_pos.

Lemma CBLOCKz_nonneg: (0 <= CBLOCKz)%Z.
Proof. change CBLOCKz with 64%Z; omega. Qed.
Hint Resolve CBLOCKz_nonneg.

Lemma CBLOCKz_pos: (0 < CBLOCKz)%Z.
Proof. change CBLOCKz with 64%Z; omega. Qed.
Hint Resolve CBLOCKz_pos.

Lemma intlist_to_Zlist_app:
 forall al bl, intlist_to_Zlist (al++bl) = intlist_to_Zlist al ++ intlist_to_Zlist bl.
Proof. intros; induction al; simpl; auto. repeat f_equal; auto. Qed.

Lemma firstn_app:
 forall {A} n m (al: list A), firstn n al ++ firstn m (skipn n al) =
  firstn (n+m) al.
Proof. induction n; destruct al; intros; simpl; auto.
destruct m; reflexivity.
f_equal; auto.
Qed.

Lemma nth_skipn:
  forall A i n data (d:A),
       nth i (skipn n data) d = nth (i+n) data d.
Proof.
intros.
revert i data; induction n; simpl; intros.
f_equal; omega.
destruct data; auto.
destruct i; simpl; auto.
rewrite IHn.
replace (i + S n) with (S (i + n)) by omega; auto.
Qed.

Lemma Forall_app :
forall {A} P (l1 l2 :list A),
Forall P (l1 ++ l2) <->
Forall P l1 /\ Forall P l2.
intros.
split; induction l1; intros.
inv H. destruct l2; inv H0. auto.
split. auto. simpl in H2. inv H2.
constructor; auto.
split. inv H. constructor; auto. apply IHl1 in H3.
intuition.
inv H. apply IHl1 in H3. intuition.
simpl. intuition.
simpl. constructor.
destruct H. inv H. auto.
apply IHl1. intuition.
inv H0; auto.
Qed.

Lemma firstn_firstn: forall {A} lo n (data: list A), firstn lo (firstn (lo + n) data) = firstn lo data.
Proof.
  intros.
  revert data; induction lo; intros.
  + reflexivity.
  + destruct data; simpl; [reflexivity |].
    rewrite IHlo.
    reflexivity.
Qed.

Lemma skipn_firstn: forall {A} lo n (data: list A), skipn lo (firstn (lo + n) data) = firstn n (skipn lo data).
Proof.
  intros.
  revert data; induction lo; intros.
  + reflexivity.
  + destruct data; simpl.
    - destruct n; reflexivity.
    - apply IHlo.
Qed.

Lemma Zlength_app: forall T (al bl: list T),
    Zlength (al++bl) = (Zlength al + Zlength bl)%Z.
Proof. induction al; intros. simpl app; rewrite Zlength_nil; omega.
 simpl app; repeat rewrite Zlength_cons; rewrite IHal; omega.
Qed.
Lemma Zlength_rev: forall T (vl: list T), Zlength (rev vl) = Zlength vl.
Proof. induction vl; simpl; auto. rewrite Zlength_cons. rewrite <- IHvl.
rewrite Zlength_app. rewrite Zlength_cons. rewrite Zlength_nil; omega.
Qed.

Lemma Zlength_map: forall A B (f: A -> B) l, Zlength (map f l) = Zlength l.
Proof. induction l; simpl; auto. repeat rewrite Zlength_cons. f_equal; auto.
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

Lemma Forall_firstn:
  forall A (f: A -> Prop) n l, Forall f l -> Forall f (firstn n l).
Proof.
induction n; destruct l; intros.
constructor. constructor. constructor.
inv H. simpl. constructor; auto.
Qed.

Lemma Forall_skipn:
  forall A (f: A -> Prop) n l, Forall f l -> Forall f (skipn n l).
Proof.
induction n; destruct l; intros.
constructor. inv H; constructor; auto. constructor.
inv H. simpl.  auto.
Qed.

Local Open Scope Z.

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

Lemma hilo_lemma:
  forall hi lo, [Int.repr (hilo hi lo / Int.modulus); Int.repr (hilo hi lo)] = [hi; lo].
Proof.
unfold hilo; intros.
rewrite Z.div_add_l by (compute; congruence).
rewrite Zdiv_small by apply Int.unsigned_range.
rewrite Z.add_0_r.
rewrite Int.repr_unsigned.
f_equal.
f_equal.
rewrite <- add_repr.
rewrite <- mul_repr.
replace (Int.repr Int.modulus) with (Int.repr 0).
rewrite Int.mul_zero. rewrite Int.add_zero_l. apply Int.repr_unsigned.
apply Int.eqm_samerepr.
unfold Int.eqm.
change 0 with (Int.modulus mod Int.modulus).
apply Int.eqmod_sym.
apply Int.eqmod_mod.
compute; congruence.
Qed.

Lemma Forall_isbyteZ_unsigned_repr:
 forall l, Forall isbyteZ l -> Forall isbyteZ (map Int.unsigned (map Int.repr l)).
Proof. induction 1. constructor.
constructor. rewrite Int.unsigned_repr; auto.
unfold isbyteZ in H; repable_signed.
apply IHForall.
Qed.

Lemma divide_hashed:
 forall (bb: list int), 
    NPeano.divide LBLOCK (length bb) <->
    (LBLOCKz | Zlength bb).
Proof.
intros; split; intros [n ?].
exists (Z.of_nat n). rewrite Zlength_correct, H.
rewrite Nat2Z.inj_mul; auto.
exists (Z.to_nat n).
rewrite Zlength_correct in H.
assert (0 <= n).
assert (0 <= n * LBLOCKz) by omega.
apply Z.mul_nonneg_cancel_r in H0; auto.
rewrite <- (Z2Nat.id (n*LBLOCKz)%Z) in H by omega.
apply Nat2Z.inj in H. rewrite H.
change LBLOCK with (Z.to_nat LBLOCKz).
rewrite Z2Nat.inj_mul; auto.
Qed.

Lemma hash_blocks_equation' : forall (r : registers) (msg : list int),
       hash_blocks r msg =
       match msg with
       | [] => r
       | _ :: _ => hash_blocks (hash_block r (firstn LBLOCK msg)) (skipn LBLOCK msg)
       end.
Proof. exact hash_blocks_equation. Qed.

Lemma CBLOCK_eq: CBLOCK=64%nat.
Proof. reflexivity. Qed.
Lemma LBLOCK_eq: LBLOCK=16%nat.
Proof. reflexivity. Qed.

Lemma hash_blocks_last:
 forall a bl c, 
              Zlength a = 8 ->
              (LBLOCKz | Zlength bl) -> 
              Zlength c = LBLOCKz ->
   hash_block (hash_blocks a bl) c = hash_blocks a (bl++ c).
Proof.
intros.
assert (POS: (0 < LBLOCK)%nat) by (rewrite LBLOCK_eq; omega).
apply divide_hashed in H0.
destruct H0 as [n ?].
rewrite Zlength_correct in H,H1.
change 8 with (Z.of_nat 8) in H.
(*change LBLOCK with 16%nat in H0.*)
change LBLOCKz with (Z.of_nat LBLOCK) in H1.
apply Nat2Z.inj in H. 
apply Nat2Z.inj in H1.
revert a bl H H0; induction n; intros.
destruct bl; inv H0.
rewrite hash_blocks_equation'. 
simpl. rewrite hash_blocks_equation'.
destruct c eqn:?. inv H1.
rewrite <- Heql in *; clear i l Heql.
rewrite firstn_same by omega.
replace (skipn LBLOCK c) with (@nil int).
rewrite hash_blocks_equation'; reflexivity.
pose proof (skipn_length LBLOCK c).
spec H0; [omega |]. rewrite H1 in H0.
destruct (skipn LBLOCK c); try reflexivity; inv H0.
replace (S n * LBLOCK)%nat with (n * LBLOCK + LBLOCK)%nat  in H0 by
  (simpl; omega).
rewrite hash_blocks_equation'.
destruct bl.
simpl in H0.
Psatz.lia.
forget (i::bl) as bl'; clear i bl. rename bl' into bl.
rewrite IHn.
symmetry.
rewrite hash_blocks_equation.
destruct bl.
simpl in H0; Psatz.lia.
unfold app at 1; fold app.
forget (i::bl) as bl'; clear i bl. rename bl' into bl.
f_equal.
f_equal.
apply firstn_app1.
Psatz.nia.
apply skipn_app1.
Psatz.nia.
apply length_hash_block; auto. (* fixme *) change 16%nat with LBLOCK.
rewrite firstn_length. apply min_l.
Psatz.nia.
rewrite skipn_length.
apply plus_reg_l with LBLOCK.
rewrite plus_comm. 
rewrite NPeano.Nat.sub_add by Psatz.lia.
omega.
(*Psatz.lia.*)
rewrite H0. assert (Hn: (n*LBLOCK >= 0)%nat).
  remember ((n * LBLOCK)%nat). clear. omega.
  omega. 
Qed.

Lemma length_hash_blocks: forall regs blocks,
  length regs = 8%nat ->
  (LBLOCKz | Zlength blocks) ->
  length (hash_blocks regs blocks) = 8%nat.
Proof.
intros.
destruct H0 as [n ?].
rewrite Zlength_correct in H0.
assert (POS := LBLOCKz_pos).
change LBLOCKz with (Z.of_nat LBLOCK) in *.
rewrite <- (Z2Nat.id n) in H0 
 by (apply -> Z.mul_nonneg_cancel_r ; [ | apply POS]; omega).
rewrite <- Nat2Z.inj_mul in H0.
apply Nat2Z.inj in H0.
revert regs blocks H H0; induction (Z.to_nat n); intros.
  destruct blocks; inv H0.
rewrite hash_blocks_equation'; auto.
destruct blocks.
destruct LBLOCK; inv POS; inv H0.
rewrite hash_blocks_equation'; auto.
forget (i::blocks) as bb.
apply IHn0; auto.
apply length_hash_block; auto. (* fixme *) change 16%nat with LBLOCK.
rewrite firstn_length. apply min_l. simpl in H0. Psatz.nia.
rewrite skipn_length. rewrite H0; clear - POS.  simpl.
rewrite plus_comm. rewrite NPeano.Nat.add_sub. auto.
simpl in H0. rewrite H0; clear - POS. Psatz.lia.
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

Lemma Forall_list_repeat:
  forall A (f: A -> Prop) n (x: A),
     f x -> Forall f (list_repeat n x).
Proof.
 intros; induction n; simpl; auto.
Qed.

Lemma ZtoNat_Zlength: 
 forall {A} (l: list A), Z.to_nat (Zlength l) = length l.
Proof.
intros. rewrite Zlength_correct. apply Nat2Z.id.
Qed.
Hint Rewrite @ZtoNat_Zlength : norm.

Lemma Zlength_nonneg:
 forall {A} (l: list A), 0 <= Zlength l.
Proof.
intros. rewrite Zlength_correct. omega.
Qed.




