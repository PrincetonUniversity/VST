From Stdlib Require Import Arith.EqNat Relations.Relations Lia.

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Set Implicit Arguments.

(*Open Scope Z.*)

Set Implicit Arguments.
Definition is_true (b: bool) :=
  match b with true => True | false => False end.

Definition force_val (v: option val) : val :=
 match v with Some v' => v' | None => Vundef end.

Definition force_val1 (f: val -> option val) (v: val) := force_val (f v).
Definition force_val2 (f: val -> val -> option val) (v1 v2: val) := force_val (f v1 v2).

Arguments force_val1 f v /.
Arguments force_val2 f v1 v2 /.

Definition force_int (v: val) :=
 match v with
 | Vint i => i | _ => Int.zero
 end.
Arguments force_int !v / .

Definition force_signed_int v := Int.signed (force_int v).
Arguments force_signed_int !v / .

Definition force_ptr (v: val) : val :=
              match v with Vptr l ofs => v | _ => Vundef  end.

Definition always {A B: Type} (b: B) (a: A) := b.

Definition offset_val (ofs: Z) (v: val) : val :=
  match v with
  | Vptr b z => Vptr b (Ptrofs.add z (Ptrofs.repr ofs))
  | _ => Vundef
 end.

Definition range_s32 (i: Z) : bool :=
   andb (Z.leb Int.min_signed i) (Z.leb i Int.max_signed).

Definition range_s64 (i: Z) : bool :=
   andb (Z.leb Int64.min_signed i) (Z.leb i Int64.max_signed).

Definition is_long (v: val) :=
 match v with Vlong i => True | _ => False end.
Definition is_float (v: val) :=
 match v with Vfloat i => True | _ => False end.
Definition is_single (v: val) :=
 match v with Vsingle i => True | _ => False end.

Definition is_pointer_or_null (v: val) :=
 match v with
 | Vint i => if Archi.ptr64 then False else  i = Int.zero
 | Vlong i => if Archi.ptr64 then i=Int64.zero else False
 | Vptr _ _ => True
 | _ => False
 end.

Definition is_pointer_or_integer (v: val) :=
 match v with
 | Vint i => if Archi.ptr64 then False else True
 | Vlong i => if Archi.ptr64 then True else False
 | Vptr _ _ => True
 | _ => False
 end.

Definition isptr v :=
   match v with | Vptr _ _ => True | _ => False end.

Lemma int_eq_e: forall i j, Int.eq i j = true -> i=j.
Proof. intros. pose proof (Int.eq_spec i j); rewrite H in H0; auto. Qed.

Lemma two_p_neg:
 forall n, n<0 -> two_p n = 0.
Proof.
destruct n; intros; simpl; auto; lia.
Qed.

Unset Implicit Arguments.

Lemma testbit_signed_neg:
 forall i j n,
   - two_p n <= Int.signed i < 0 ->
    0 <= n <= j ->
    j < Int.zwordsize ->
   Int.testbit i j = true.
Proof.
intros. rename H1 into Wj.
pose proof (Int.unsigned_range i).
unfold Int.signed in H.
if_tac in H. lia.
unfold Int.testbit.
forget (Int.unsigned i) as i'; clear i; rename i' into i.
rewrite <- (Z2Nat.id j) in * by lia.
unfold Int.half_modulus in *.
unfold Int.modulus in *.
unfold Int.zwordsize in Wj.
forget Int.wordsize as W.
assert (Z.to_nat j < W)%nat by (apply Nat2Z.inj_lt; auto).
clear Wj.
assert (W = Z.to_nat j + 1 + (W-Z.to_nat j-1))%nat by lia.
forget (W - Z.to_nat j - 1)%nat as K.
subst W.

clear H3.
rewrite <- (Z2Nat.id n) in H by lia.
rewrite <- (Z2Nat.id n) in H0 by lia.
rewrite <- two_power_nat_two_p in H.
assert (Z.to_nat n <= Z.to_nat j)%nat.
  apply Nat2Z.inj_le; lia.
clear H0.
forget (Z.to_nat n) as n'; clear n; rename n' into n.
forget (Z.to_nat j) as j'; clear j; rename j' into j.
destruct H as [H _].
revert n i H3 H2 H  H1; induction j; intros.
*
simpl (Z.of_nat) in *.
assert (n=0)%nat by lia. subst n.
simpl plus in *. clear H3.
change (- two_power_nat 0) with (-1) in H.
assert (i = (two_power_nat (S K) - 1)) by lia. subst i.
rewrite two_power_nat_S.
clear.
forget (two_power_nat K) as A.
replace A with ((A-1)+1) by lia.
rewrite Z.mul_add_distr_l.
replace (2 * (A - 1) + 2 * 1 - 1) with (2 * (A - 1) + 1) by lia.
apply Z.testbit_odd_0.
*
destruct n.
change (- two_power_nat 0)%Z with (-1) in H.
assert (i = two_power_nat (S j + 1 + K) - 1) by lia.
clear H H1 H2.
subst i.
replace (two_power_nat (S j + 1 + K) - 1) with (Z.ones (Z.of_nat (S j + 1 + K))).
apply Z.ones_spec_low. split; [lia | ].
apply Nat2Z.inj_lt. lia.
rewrite Z.ones_equiv.
rewrite two_power_nat_equiv.
lia.
rewrite inj_S.
rewrite Zbits.Ztestbit_succ by lia.
apply (IHj n); clear IHj.
+
lia.
+
rewrite Zdiv2_div.
apply Z_div_ge; try lia.
replace (S j + 1 + K)%nat with (S (j + 1 + K))%nat in H2 by lia.
rewrite two_power_nat_S in H2.
rewrite Z.mul_comm in H2.
rewrite Z_div_mult_full in H2 by lia. auto.
+
rewrite two_power_nat_S in H.
replace (S j + 1 + K)%nat with (S (j + 1 + K))%nat in H by lia.
rewrite two_power_nat_S in H.
rewrite (Zdiv2_odd_eqn i) in H.
destruct (Z.odd i) eqn:?H; lia.
+
replace (S j + 1 + K)%nat with (S (j + 1 + K))%nat in H1 by lia.
rewrite two_power_nat_S in H1.
rewrite (Zdiv2_odd_eqn i) in H1.
destruct (Z.odd i) eqn:?H; lia.
Qed.

(*
Lemma sign_ext_inrange:
  forall n i, - two_p (n-1) <= Int.signed i <= two_p (n-1) - 1 ->
       Int.sign_ext n i = i.
Proof.
intros.
destruct (zlt 0 n).
-
apply Int.same_bits_eq; intros j ?.
rewrite Int.bits_sign_ext; try lia.
if_tac; auto.
assert (Int.size i < n); [ | rewrite !Int.bits_size_2 by lia; auto].
pose proof (Int.size_interval_2 i (n-1)).
spec H2; [lia |].
spec H2; [ | lia].
clear H2.
assert (0 < n < Int.zwordsize) by lia.
clear l j H0 H1.
split; [apply Int.unsigned_range| ].
Search Int.unsigned Int.signed.
*)

Lemma sign_ext_inrange:
  forall n i, - two_p (n-1) <= Int.signed i <= two_p (n-1) - 1 ->
       Int.sign_ext n i = i.
Proof.
intros.
destruct (zlt n Int.zwordsize);
  [ | apply Int.sign_ext_above; auto].
destruct (zlt n 0).
assert (n-1 < 0) by lia.
repeat rewrite two_p_neg in H by lia.
lia.
destruct (zeq n 0).
subst n. simpl in H.
assert (Int.signed i = 0) by lia.
clear - H0.
rewrite <- (Int.repr_signed i).
rewrite H0. reflexivity.
assert (0 < n < Int.zwordsize) by lia.
clear - H H0.

apply Int.same_bits_eq; intros j ?.
rewrite (Int.bits_sign_ext n i j) by lia.
if_tac; auto.
destruct H1.
destruct (zlt (Int.signed i) 0).
* (* negative *)
assert (- two_p (n - 1) <= Int.signed i  < 0) by lia.
clear H.
rewrite (testbit_signed_neg i (n-1) (n-1)); auto; try lia.
rewrite (testbit_signed_neg i j (n-1)%Z); auto; lia.
* (* nonnegative *)
rewrite Int.signed_eq_unsigned in H by (apply Int.signed_positive; auto).
assert (Int.size i <= n-1);
  [ | rewrite !Int.bits_size_2 by lia; auto].
apply Z.ge_le.
apply Int.size_interval_2.
lia.
pose proof (Int.unsigned_range i); lia.
Qed.

Lemma zero_ext_inrange:
  forall n i, Int.unsigned i <= two_p n - 1 ->
       Int.zero_ext n i = i.
Proof.
intros.
destruct (zlt n Int.zwordsize);
  [ | apply Int.zero_ext_above; auto].
destruct (zlt n 0).
assert (n-1 < 0) by lia.
repeat rewrite two_p_neg in H by lia.
pose proof (Int.unsigned_range i).
lia.
destruct (zeq n 0).
subst n. simpl in H.
assert (Int.unsigned i = 0) by (pose proof (Int.unsigned_range i); lia).
clear - H0.
rewrite <- (Int.repr_unsigned i).
rewrite H0. reflexivity.
assert (0 < n < Int.zwordsize) by lia.
clear - H H0.
apply Int.same_bits_eq; intros j ?.
rewrite (Int.bits_zero_ext n i j) by lia.
if_tac; auto.
symmetry.
apply Int.bits_size_2.
apply Z.ge_le.
apply Int.size_interval_2.
lia.
split.
apply Int.unsigned_range.
assert (two_p n <= two_p j); try lia.
apply two_p_monotone.
lia.
Qed.

Lemma signed_inj : forall i1 i2, Int.signed i1 = Int.signed i2 -> i1 = i2.
Proof.
  intros.
  apply int_eq_e.
  rewrite Int.eq_signed, H.
  apply zeq_true.
Qed.

Lemma mods_repr : forall a b, 0 <= a <= Int.max_signed -> 0 < b <= Int.max_signed ->
  Int.mods (Int.repr a) (Int.repr b) = Int.repr (a mod b).
Proof.
  intros.
  unfold Int.mods.
  pose proof Int.min_signed_neg.
  rewrite Zquot.Zrem_Zmod_pos; repeat rewrite Int.signed_repr; auto; lia.
Qed.
