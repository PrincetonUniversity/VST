Require Import VST.floyd.proofauto.
Require Import linking.
Require Import triang.
Require Import spec_stdlib.
Require Import spec_pile.
Require Import spec_triang.

Definition Gprog : funspecs :=   
      spec_pile.specs ++ spec_triang.specs.

Fixpoint decreasing (n: nat) :=
 match n with
 | O => nil
 | S n' => Z.of_nat n :: decreasing n'
 end.

Lemma triangular_number:
  forall n, 0 <= n -> 
     sumlist (decreasing (Z.to_nat n)) = n*(n+1)/2.
Proof.
intros.
assert (2* sumlist (decreasing (Z.to_nat n)) = n * (n + 1))%Z.
2: rewrite <- H0, Z.mul_comm, Z.div_mul by omega; auto.
rewrite <- (Z2Nat.id n) at 2 3 by omega.
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
omega.
Qed.

Lemma sumlist_decreasing_bound:
  forall n, 0 <= n < 1000 ->
  0 <= sumlist (decreasing (Z.to_nat n)) <= Int.max_signed.
Proof.
intros.
rewrite triangular_number by omega.
split.
apply Z.div_pos; try omega.
apply Z.mul_nonneg_nonneg; omega.
apply Z.div_le_upper_bound; try omega.
eapply Z.le_trans.
apply Z.mul_le_mono_nonneg; try omega.
instantiate (1:=1001); omega.
instantiate (1:=1001); omega.
computable.
Qed.

Lemma body_Triang_nth: semax_body Vprog Gprog f_Triang_nth Triang_nth_spec.
Proof.
start_function.
forward_call gv.
Intros p.
forward_for_simple_bound n
  (EX i:Z,
   PROP() LOCAL(temp _p p; temp _n (Vint (Int.repr n)); gvars gv)
   SEP (pilerep (decreasing (Z.to_nat i)) p; pile_freeable p; mem_mgr gv)).
-
 entailer!.
- forward_call (p, i+1, decreasing(Z.to_nat i), gv).
rep_omega.
entailer!.
assert (Z.to_nat (i+1) = S (Z.to_nat i))
  by (rewrite <- Z2Nat.inj_succ by omega; f_equal).
rewrite H2.
unfold decreasing; fold decreasing.
rewrite inj_S.
rewrite Z2Nat.id by omega.
apply derives_refl.
-
forward_call (p, decreasing (Z.to_nat n)).
apply sumlist_decreasing_bound; auto.
forward_call (p, decreasing (Z.to_nat n), gv).
forward.
entailer!.
f_equal; f_equal.
clear.
induction (Z.to_nat n).
reflexivity.
simpl. congruence.
Qed.

Definition module := 
  [mk_body body_Triang_nth ].
