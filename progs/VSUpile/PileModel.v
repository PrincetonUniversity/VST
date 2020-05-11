Require Import VST.floyd.proofauto.

(*Model-level definitions and associated lemmas.*)

Definition sumlist : list Z -> Z := fold_right Z.add Z0.

Fixpoint decreasing (n: nat) :=
 match n with
 | O => nil
 | S n' => Z.of_nat n :: decreasing n'
 end.

Fixpoint triang (n: nat) :=
 match n with
 | O => 0
 | S n' => Z.of_nat n + triang n'
 end.

Lemma triangular_number:
  forall n, 0 <= n -> 
     sumlist (decreasing (Z.to_nat n)) = n*(n+1)/2.
Proof.
intros.
assert (2* sumlist (decreasing (Z.to_nat n)) = n * (n + 1))%Z.
2: rewrite <- H0, Z.mul_comm, Z.div_mul by lia; auto.
rewrite <- (Z2Nat.id n) at 2 3 by lia.
clear H.
induction (Z.to_nat n).
reflexivity.
rewrite inj_S.
unfold decreasing; fold decreasing.
change (sumlist (Z.of_nat (S n0) :: decreasing n0))
  with (Z.of_nat (S n0) + sumlist (decreasing n0)).
rewrite Z.mul_add_distr_l.
rewrite IHn0.
clear.
rewrite inj_S.
forget (Z.of_nat n0) as n.
unfold Z.succ.
rewrite !Z.mul_add_distr_l.
rewrite !Z.mul_add_distr_r.
lia.
Qed.

Lemma sumlist_decreasing_bound:
  forall n, 0 <= n < 1000 ->
  0 <= sumlist (decreasing (Z.to_nat n)) <= Int.max_signed.
Proof.
intros.
rewrite triangular_number by lia.
split.
apply Z.div_pos; try lia.
(*apply Z.mul_nonneg_nonneg; lia.*)
apply Z.div_le_upper_bound; try lia.
eapply Z.le_trans.
apply Z.mul_le_mono_nonneg; try lia.
instantiate (1:=1001); lia.
instantiate (1:=1001); lia.
computable.
Qed.

Lemma sumlist_nonneg: forall sigma, 
  Forall (Z.le 0) sigma -> 0 <= sumlist sigma.
Proof.
intros.
induction sigma; simpl. lia. inv H.
apply IHsigma in H3; lia.
Qed.

Lemma decreasing_inc i (I:0 <= i):
  i + 1 :: decreasing (Z.to_nat i) = decreasing (Z.to_nat (i + 1)).
Proof. 
    replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
    unfold decreasing; fold decreasing.
    + f_equal. rewrite inj_S. rewrite Z2Nat.id by lia. lia.
    + rewrite <- Z2Nat.inj_succ by lia. f_equal; lia.
Qed.