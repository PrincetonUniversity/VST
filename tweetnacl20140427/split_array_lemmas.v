Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.

Require Import general_lemmas.

(*Require Import spec_sha.*)
Require Import sha_lemmas.  (*For Lemma split_offset_array_at -should be put in floyd! *)

Require Import hmac_pure_lemmas. (*For Lemma max_unsigned_modulus*)

(*generalizes Lemma data_at_lemmas.memory_block_data_at__aux1*)
Lemma Arith_aux1: forall i pos z,
  0 <= pos /\ pos + z <= Int.modulus - Int.unsigned i ->
  Int.unsigned (Int.add i (Int.repr pos)) + z <= Int.modulus.
Proof. 
  intros. 
  destruct H.
  rewrite (unsigned_add i pos H).
  cut ((Int.unsigned i + pos) mod Int.modulus <= Int.unsigned i + pos).
    { intros. omega. }
  pose proof Int.modulus_pos.
  pose proof Int.unsigned_range i.
  apply Z.mod_le; omega.
Qed.

Lemma offset_in_range_0 v: offset_in_range 0 v.
  destruct v; simpl; trivial. rewrite Z.add_0_r.
  specialize (Int.unsigned_range i); intros. omega.
Qed.
Lemma offset_in_range_le n m d:
      offset_in_range n d -> 0<=m<=n ->
      offset_in_range m d.
unfold offset_in_range; intros.
destruct d; simpl in *; trivial.
split; try omega.
apply Z.add_nonneg_nonneg. apply (Int.unsigned_range i). omega.
Qed.

Lemma offset_in_range_offset_val' n off v:
      offset_in_range (Int.unsigned off) v ->
      offset_in_range ((Int.unsigned off)+1) v ->
      offset_in_range n (offset_val off v) =
      offset_in_range (n+Int.unsigned off) v.
intros.
  destruct v; trivial. unfold offset_in_range, offset_val in *.
  rewrite  (Z.add_comm n), Z.add_assoc in *.
  rewrite Int.add_unsigned. 
  rewrite Int.unsigned_repr; trivial.
  rewrite <- max_unsigned_modulus in H0. omega. 
Qed.

Lemma offset_in_range_offset_val z1 z2 v
        (Z1: 0 <= z1) (Z2: 0 <= z2)
        (Off : offset_in_range (z1 + z2) v):
     offset_in_range z2 (offset_val (Int.repr z1) v).
Proof.
  unfold offset_val, offset_in_range in *. destruct v; trivial.
  split. apply Z.add_nonneg_nonneg; trivial. apply Int.unsigned_range. 
  apply Arith_aux1. omega.
Qed.

Lemma sizeof_Zlength_nonneg {A} t (d:list A): 0 <= sizeof t * Zlength d.
  specialize (Zlength_nonneg d). specialize (sizeof_pos t); intros.
  apply Z.mul_nonneg_nonneg; omega.
Qed.

Lemma split_offset_Tarray_at:
  forall n sh t len (contents: list (reptype t)) v,
  legal_alignas_type t = true ->
  (Z.of_nat n <= Zlength contents)%Z ->
  (Z.of_nat n <= len)%Z ->
  data_at sh (Tarray t len noattr) contents v =
  (!! (offset_in_range (sizeof t * 0) v) &&
   !! (offset_in_range (sizeof t * len) v) && 
  (data_at sh (Tarray t (Z.of_nat n) noattr) (firstn n contents) v * 
    data_at sh (Tarray t (len- Z.of_nat n) noattr) (skipn n contents) (offset_val (Int.repr (sizeof t * Z.of_nat n)) v)))%logic.
Proof. apply split_offset_array_at. Qed.

Lemma split3_offset_array_at
      t (A: legal_alignas_type t = true)
      lo n sh data d
      (N: (lo+n <= length data)%nat):
  data_at sh (tarray t (Zlength data)) data d = 
  (!! offset_in_range 0 d &&
   !! offset_in_range (sizeof t * Zlength data) d &&
  (data_at sh (tarray t (Z.of_nat lo)) (firstn lo data) d *
  data_at sh (tarray t (Z.of_nat n)) (firstn n (skipn lo data)) (offset_val (Int.repr (sizeof t * Z.of_nat lo)) d) *
  data_at sh (tarray t (Zlength data - Z.of_nat (lo+n)))
             (skipn (lo+n) data)  (offset_val (Int.repr (sizeof t * Z.of_nat (lo+n))) d)))%logic.
Proof.
  fold reptype in *.
  assert (Arith1: Zlength (firstn (lo + n) data) = Z.of_nat (lo + n)).
           repeat rewrite Zlength_correct. rewrite firstn_length, min_l; trivial.
  rewrite split_offset_array_at with (n := (lo + n)%nat); trivial. (* by omega.*)
  rewrite split_offset_array_at with (n := lo) (contents := firstn (lo + n) data); trivial.
    (* by
    (rewrite firstn_length; rewrite Min.min_l by omega; omega).*)
  assert (!!offset_in_range (sizeof t * Zlength data) d |-- 
    !! offset_in_range (sizeof t * Zlength (firstn (lo + n) data)) d)%logic.
    remember (sizeof t) as ST; normalize; subst ST.
    apply offset_in_range_mid with (lo := 0%Z) (hi := Zlength data); try assumption.
    rewrite !Zlength_correct.
    rewrite firstn_length; rewrite Min.min_l by omega. split; try omega.
    apply inj_le, N.
    rewrite Zmult_0_r.
    unfold offset_in_range; destruct d; auto.
    pose proof Int.unsigned_range i; omega.
  rewrite (add_andp _ _ H) at 2. repeat rewrite Zmult_0_r.
  normalize. 
  f_equal. f_equal. rewrite Arith1. apply prop_ext; intuition.
  f_equal.
  f_equal.
  rewrite firstn_firstn. trivial.
  rewrite skipn_firstn. trivial. 
  rewrite Nat2Z.inj_add, Zminus_plus; trivial.

  rewrite Arith1. apply inj_le. omega.
  apply inj_le. omega.
  rewrite Zlength_correct. apply inj_le; trivial.
  rewrite Zlength_correct. apply inj_le; trivial. 
Qed.

Lemma split3_offset_Tarray_at
      t (A: legal_alignas_type t = true)
      lo n sh data d
      (N: (lo+n <= length data)%nat):
  data_at sh (Tarray t (Zlength data) noattr) data d = 
  (!! offset_in_range 0 d &&
   !! offset_in_range (sizeof t * Zlength data) d &&
  (data_at sh (Tarray t (Z.of_nat lo) noattr) (firstn lo data) d *
  data_at sh (Tarray t (Z.of_nat n) noattr) (firstn n (skipn lo data)) (offset_val (Int.repr (sizeof t * Z.of_nat lo)) d) *
  data_at sh (Tarray t (Zlength data - Z.of_nat (lo+n)) noattr)
             (skipn (lo+n) data)  (offset_val (Int.repr (sizeof t * Z.of_nat (lo+n))) d)))%logic.
Proof. apply split3_offset_array_at; trivial. Qed.

Lemma append_split_Tarray_at:
  forall d t (data1 data2 data :list (reptype t)) sh,
  legal_alignas_type t = true ->
  data1 ++ data2 = data ->
  data_at sh (Tarray t (Zlength data) noattr) data d = 
  (!! offset_in_range (sizeof t * 0) d &&
   !! offset_in_range (sizeof t * (Zlength data)) d &&
  (data_at sh (Tarray t (Zlength data1) noattr) data1 d *
   data_at sh (Tarray t (Zlength data2) noattr) data2 
             (offset_val (Int.repr (sizeof t * Zlength data1)) d)))%logic. 
intros. subst.
rewrite (split_offset_Tarray_at (length data1) sh t (Zlength (data1++data2)) 
         (data1 ++ data2) d H); repeat rewrite Zlength_correct.
rewrite firstn_exact, skipn_exact; trivial.
rewrite app_length, Nat2Z.inj_add, Z.add_simpl_l; trivial.
rewrite app_length, Nat2Z.inj_add. omega.
rewrite app_length, Nat2Z.inj_add. omega.
Qed.

Lemma append_split3_Tarray_at
      t (data1 data2 data3 data :list (reptype t)) sh
      (A: legal_alignas_type t = true)
      (APP: data1 ++ data2 ++ data3 = data) d:
  data_at sh (Tarray t (Zlength data) noattr) data d = 
  (!! offset_in_range 0 d &&
   !! offset_in_range (sizeof t * (Zlength data)) d &&
  (data_at sh (Tarray t (Zlength data1) noattr) data1 d *
   data_at sh (Tarray t (Zlength data2) noattr) data2 
             (offset_val (Int.repr (sizeof t * Zlength data1)) d) *
   data_at sh (Tarray t (Zlength data3) noattr) data3
             (offset_val (Int.repr (sizeof t * (Zlength data1 + Zlength data2))) d)))%logic.
Proof. 
  subst.
  erewrite (split3_offset_Tarray_at t A (length data1) (length data2)).
  2: repeat rewrite app_length; omega.
  rewrite firstn_exact; trivial.
  rewrite skipn_exact; trivial. 
  rewrite firstn_exact; trivial.
  rewrite app_assoc, skipn_app2. 2: rewrite app_length; omega.
  assert (Arith1: (length data1 + length data2 - (length data1 + length data2) = 0)%nat) by omega.
  f_equal. repeat rewrite Zlength_correct. repeat rewrite app_length. 
  rewrite Arith1; clear Arith1. simpl.
  f_equal. repeat rewrite Nat2Z.inj_add. rewrite Z.mul_add_distr_l.
  assert (Arith: Z.of_nat (length data1) + Z.of_nat (length data2) +
      Z.of_nat (length data3) -
      (Z.of_nat (length data1) + Z.of_nat (length data2)) = Z.of_nat (length data3)). omega.
  rewrite Arith; clear Arith; trivial.
Qed. 

Definition Select_at t sh n data2 d :=
   data_at sh (Tarray t (Zlength data2) noattr) data2 
             (offset_val (Int.repr (sizeof t * n)) d).
Definition Unselect_at t sh (data1 data2 data3:list (reptype t)) d :=
   !! offset_in_range 0 d &&
   !! offset_in_range (sizeof t * (Zlength (data1 ++ data2 ++ data3))) d &&
  (data_at sh (Tarray t (Zlength data1) noattr) data1 d *
   data_at sh (Tarray t (Zlength data3) noattr) data3
             (offset_val (Int.repr (sizeof t * (Zlength data1 + Zlength data2))) d)).

Lemma Select_Unselect_Tarray_at t (A: legal_alignas_type t = true) sh data1 data2 data3 data d
  (DATA: (data1 ++ data2 ++ data3) = data)
  l (L: l = Zlength data):
  data_at sh (Tarray t l noattr) data d = 
  Select_at t sh (Zlength data1) data2 d * Unselect_at t sh data1 data2 data3 d.
Proof.
  fold reptype in *. subst l.
  erewrite append_split3_Tarray_at; try eassumption.
  unfold Select_at, Unselect_at. subst; normalize.
  f_equal; f_equal. rewrite sepcon_comm. f_equal.
Qed. 

Lemma Select_Unselect_tarray_at t (A: legal_alignas_type t = true) sh data1 data2 data3 data d
  (DATA: (data1 ++ data2 ++ data3) = data):
  data_at sh (tarray t (Zlength data)) data d = 
  Select_at t sh (Zlength data1) data2 d * Unselect_at t sh data1 data2 data3 d.
Proof. apply Select_Unselect_Tarray_at; trivial. Qed.

Lemma Select_Unselect_tuchararray_at sh data1 data2 data3 data d
  (DATA: (data1 ++ data2 ++ data3) = data):
  data_at sh (tarray tuchar (Zlength data)) data d = 
  Select_at tuchar sh (Zlength data1) data2 d * Unselect_at tuchar sh data1 data2 data3 d.
Proof. apply Select_Unselect_tarray_at; trivial. Qed.

Lemma Select_Unselect_tuchararray_at':
  forall l (sh : Share.t) (data1 data2 data3 data : list val) (d : val),
  data1 ++ data2 ++ data3 = data ->
  l = Zlength data ->
  data_at sh (tarray tuchar l) data d =
  Select_at tuchar sh (Zlength data1) data2 d *
  Unselect_at tuchar sh data1 data2 data3 d.
   Proof. intros. subst. apply Select_Unselect_tuchararray_at. trivial. Qed.
