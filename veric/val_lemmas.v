Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relations.

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

Lemma force_Vint:  forall i, force_int (Vint i) = i.
Proof.  reflexivity. Qed.
Hint Rewrite force_Vint : norm.

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
destruct n; intros; simpl; auto; try omega.
pose proof (Zgt_pos_0 p); omega.
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
if_tac in H. omega.
unfold Int.testbit.
forget (Int.unsigned i) as i'; clear i; rename i' into i.
rewrite <- (Z2Nat.id j) in * by omega.
unfold Int.half_modulus in *.
unfold Int.modulus in *.
unfold Int.zwordsize in Wj.
forget Int.wordsize as W.
assert (Z.to_nat j < W)%nat by (apply Nat2Z.inj_lt; auto).
clear Wj.
assert (W = Z.to_nat j + 1 + (W-Z.to_nat j-1))%nat by omega.
forget (W - Z.to_nat j - 1)%nat as K.
subst W.

clear H3.
rewrite <- (Z2Nat.id n) in H by omega.
rewrite <- (Z2Nat.id n) in H0 by omega.
rewrite <- two_power_nat_two_p in H.
assert (Z.to_nat n <= Z.to_nat j)%nat.
  apply Nat2Z.inj_le; omega.
clear H0.
forget (Z.to_nat n) as n'; clear n; rename n' into n.
forget (Z.to_nat j) as j'; clear j; rename j' into j.
destruct H as [H _].
revert n i H3 H2 H  H1; induction j; intros.
*
simpl (Z.of_nat) in *.
assert (n=0)%nat by omega. subst n.
simpl plus in *. clear H3.
change (- two_power_nat 0) with (-1) in H.
assert (i = (two_power_nat (S K) - 1)) by omega. subst i.
rewrite two_power_nat_S.
clear.
forget (two_power_nat K) as A.
replace A with ((A-1)+1) by omega.
rewrite Z.mul_add_distr_l.
replace (2 * (A - 1) + 2 * 1 - 1) with (2 * (A - 1) + 1) by omega.
apply Z.testbit_odd_0.
*
destruct n.
change (- two_power_nat 0)%Z with (-1) in H.
assert (i = two_power_nat (S j + 1 + K) - 1) by omega.
clear H H1 H2.
subst i.
replace (two_power_nat (S j + 1 + K) - 1) with (Z.ones (Z.of_nat (S j + 1 + K))).
apply Z.ones_spec_low. split; [omega | ].
apply Nat2Z.inj_lt. omega.
rewrite Z.ones_equiv.
rewrite two_power_nat_equiv.
omega.
rewrite inj_S.
rewrite Int.Ztestbit_succ by omega.
apply (IHj n); clear IHj.
+
omega.
+
rewrite Zdiv2_div.
apply Z_div_ge; try omega.
replace (S j + 1 + K)%nat with (S (j + 1 + K))%nat in H2 by omega.
rewrite two_power_nat_S in H2.
rewrite Z.mul_comm in H2.
rewrite Z_div_mult_full in H2 by omega. auto.
+
rewrite two_power_nat_S in H.
replace (S j + 1 + K)%nat with (S (j + 1 + K))%nat in H by omega.
rewrite two_power_nat_S in H.
rewrite (Zdiv2_odd_eqn i) in H.
destruct (Z.odd i) eqn:?H; omega.
+
replace (S j + 1 + K)%nat with (S (j + 1 + K))%nat in H1 by omega.
rewrite two_power_nat_S in H1.
rewrite (Zdiv2_odd_eqn i) in H1.
destruct (Z.odd i) eqn:?H; omega.
Qed.

Lemma sign_ext_inrange:
  forall n i, - two_p (n-1) <= Int.signed i <= two_p (n-1) - 1 ->
       Int.sign_ext n i = i.
Proof.
intros.
destruct (zlt n Int.zwordsize);
  [ | apply Int.sign_ext_above; auto].
destruct (zlt n 0).
assert (n-1 < 0) by omega.
repeat rewrite two_p_neg in H by omega.
omega.
destruct (zeq n 0).
subst n. simpl in H.
assert (Int.signed i = 0) by omega.
clear - H0.
rewrite <- (Int.repr_signed i).
rewrite H0. reflexivity.
assert (0 < n < Int.zwordsize) by omega.
clear - H H0.

apply Int.same_bits_eq; intros j ?.
destruct H0.
rewrite (Int.bits_sign_ext n i j H1 H0).
if_tac; auto.
destruct H1.
destruct (zlt (Int.signed i) 0).
* (* negative *)
assert (- two_p (n - 1) <= Int.signed i  < 0) by omega.
clear H.
rewrite (testbit_signed_neg i (n-1) (n-1)); auto; try omega.
rewrite (testbit_signed_neg i j (n-1)%Z); auto; omega.
* (* nonnegative *)
rewrite Int.signed_eq_unsigned in H by (apply Int.signed_positive; auto).
unfold Int.testbit in *.
transitivity false.
apply (Int.Ztestbit_above (Z.to_nat (n-1))).
rewrite two_power_nat_two_p.
rewrite Z2Nat.id by omega.
pose proof (Int.unsigned_range i).
omega.
rewrite Z2Nat.id by omega.
omega.
symmetry.
apply (Int.Ztestbit_above (Z.to_nat (n-1))).
rewrite two_power_nat_two_p.
rewrite Z2Nat.id by omega.
pose proof (Int.unsigned_range i).
omega.
rewrite Z2Nat.id by omega.
omega.
Qed.

Lemma zero_ext_inrange:
  forall n i, Int.unsigned i <= two_p n - 1 ->
       Int.zero_ext n i = i.
Proof.
intros.
destruct (zlt n Int.zwordsize);
  [ | apply Int.zero_ext_above; auto].
destruct (zlt n 0).
assert (n-1 < 0) by omega.
repeat rewrite two_p_neg in H by omega.
pose proof (Int.unsigned_range i).
omega.
destruct (zeq n 0).
subst n. simpl in H.
assert (Int.unsigned i = 0) by (pose proof (Int.unsigned_range i); omega).
clear - H0.
rewrite <- (Int.repr_unsigned i).
rewrite H0. reflexivity.
assert (0 < n < Int.zwordsize) by omega.
clear - H H0.
apply Int.same_bits_eq; intros j ?.
rewrite (Int.bits_zero_ext n i j) by omega.
if_tac; auto.
symmetry.
unfold Int.testbit.
apply (Int.Ztestbit_above (Z.to_nat n));
 [ | rewrite Z2Nat.id by omega; omega].
rewrite two_power_nat_two_p.
rewrite Z2Nat.id by omega.
pose proof (Int.unsigned_range i); omega.
Qed.
