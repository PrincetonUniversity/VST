Require Stdlib.funind.Recdef.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
From Stdlib Require Import Strings.String Strings.Ascii.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Permutation.
Require Import VST.msl.Coqlib2.
Require Import VST.veric.coqlib4.

Lemma power_nat_one_divede_other: forall n m : nat,
  (two_power_nat n | two_power_nat m) \/ (two_power_nat m | two_power_nat n).
Proof.
  intros.
  pose proof Zle_0_nat n.
  pose proof Zle_0_nat m.
  rewrite !two_power_nat_two_p.
  destruct (zle (Z.of_nat n) (Z.of_nat m)).
  + left.
    exists (two_p (Z.of_nat m - Z.of_nat n)).
    rewrite <- two_p_is_exp by lia.
    f_equal.
    lia.
  + right.
    exists (two_p (Z.of_nat n - Z.of_nat m)).
    rewrite <- two_p_is_exp by lia.
    f_equal.
    lia.
Qed.

Lemma multiple_divide_mod: forall a b c, b > 0 -> ((a | b) \/ (b | a)) -> (a | (c * a mod b)).
Proof.
  intros.
  destruct H0.
  + apply Z.divide_add_cancel_r with (b * (c * a / b))%Z.
    apply Z.divide_mul_l; auto.
    rewrite <- Z_div_mod_eq_full; auto.
    apply Z.divide_mul_r, Z.divide_refl.
  + destruct H0.
    subst.
    rewrite Z.mul_assoc, Z_mod_mult.
    apply Z.divide_0_r.
Qed.

Lemma divide_align: forall x y: Z, x > 0 -> Z.divide x y -> align y x = y.
Proof.
  intros.
  unfold align.
  destruct H0.
  rewrite H0.
  pose proof Zdiv_unique (x0 * x + x - 1) x x0 (x - 1).
  assert (x0 * x + x - 1 = x0 * x + (x - 1)) by lia.
  assert (0 <= x - 1 < x) by lia.
  rewrite (H1 H2 H3).
  reflexivity.
Qed.

Lemma arith_aux00: forall a b, b <= a -> 0%nat = Z.to_nat (a - b) -> a - b = 0.
Proof.
  intros.
  pose proof Z2Nat.id (a - b).
  rewrite <- H0 in H1.
  simpl Z.of_nat in H1.
  lia.
Qed.

Lemma arith_aux01: forall a b n, S n = Z.to_nat (a - b) -> b < a.
Proof.
  intros.
  destruct (zlt a b); auto.
  + rewrite Z2Nat_neg in H by lia.
    inversion H.
  + pose proof Z2Nat.id (a - b).
    rewrite <- H in H0.
    spec H0; [lia |].
    rewrite Nat2Z.inj_succ in H0.
    lia.
Qed.

Lemma arith_aux02: forall n a b, S n = Z.to_nat (a - b) -> n = Z.to_nat (a - Z.succ b).
Proof.
  intros.
  pose proof arith_aux01 _ _ _ H.
  pose proof Z2Nat.id (a - b).
  spec H1; [lia |].
  rewrite <- H in H1.
  replace (a - Z.succ b) with (a - b - 1) by lia.
  rewrite <- H1.
  rewrite Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) by lia.
  rewrite Nat2Z.id.
  auto.
Qed.

Lemma arith_aux03: forall a b c,
  0 <= b ->
  0 <= a + b * c ->
  0 <= a + b * Z.succ c.
Proof.
  intros.
  assert (b * c <= b * Z.succ c) by (apply Zmult_le_compat_l; lia).
  lia.
Qed.

Lemma arith_aux04: forall a b c,
  0 <= b <= c ->
  (a | b) ->
  (a | b mod c).
Proof.
  intros.
  destruct (zlt b c).
  + rewrite Zmod_small by lia.
    auto.
  + assert (b = c) by lia.
    subst.
    rewrite Z_mod_same_full.
    apply Z.divide_0_r.
Qed.

Lemma arith_aux05: forall lo hi, 0 <= lo -> 0 <= hi ->
  0 <= Z.max 0 (hi - lo) <= hi.
Proof.
  intros.
  destruct (zle lo hi).
  + rewrite Z.max_r by lia.
    lia.
  + rewrite Z.max_l by lia.
    lia.
Qed.

Lemma arith_aux06: forall lo hi n, 0 <= lo <= n -> 0 <= hi <= n -> 0 <= lo + Z.max 0 (hi - lo) <= n.
Proof.
  intros.
  destruct (zle lo hi).
  + rewrite Z.max_r by lia.
    lia.
  + rewrite Z.max_l by lia.
    lia.
Qed.

Ltac inv_int i :=
  let ofs := fresh "ofs" in
  let H := fresh "H" in
  let H0 := fresh "H" in
  let H1 := fresh "H" in
 match type of i with
 | int =>
  pose proof Int.repr_unsigned i as H;
  pose proof Int.unsigned_range i as H0;
  remember (Int.unsigned i) as ofs eqn:H1;
  rewrite <- H in *;
  clear H H1; try clear i
 | ptrofs =>
  pose proof Ptrofs.repr_unsigned i as H;
  pose proof Ptrofs.unsigned_range i as H0;
  remember (Ptrofs.unsigned i) as ofs eqn:H1;
  rewrite <- H in *;
  clear H H1; try clear i
end.

(**************************************************

Solve_mod_modulus

**************************************************)

Definition int_modm x := x mod Int.modulus.

Lemma int_modm_mod_eq:
  forall x y, Zbits.eqmod Int.modulus x y -> x mod Int.modulus = int_modm y.
Proof.
  intros.
  apply Zbits.eqmod_mod_eq; auto.
  apply Int.modulus_pos.
Qed.

Lemma int_modm_mod_elim: forall x y, Zbits.eqmod Int.modulus x y -> Zbits.eqmod Int.modulus (x mod Int.modulus) y.
Proof.
  intros.
  eapply Zbits.eqmod_trans; eauto.
  apply Zbits.eqmod_sym, Zbits.eqmod_mod.
  apply Int.modulus_pos.
Qed.

Definition int_reprm := Int.repr.

Lemma int_modm_repr_eq: forall x y, Zbits.eqmod Int.modulus x y -> Int.repr x = int_reprm y.
Proof.
  intros.
  apply Int.eqm_samerepr; auto.
Qed.

Ltac int_simpl_mod A H :=
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  match A with
  | (?B + ?C)%Z =>
    int_simpl_mod B H0; int_simpl_mod C H1;
    pose proof Zbits.eqmod_add Int.modulus _ _ _ _ H0 H1 as H;
    clear H1 H0
  | (?B - ?C)%Z =>
    int_simpl_mod B H0; int_simpl_mod C H1;
    pose proof Zbits.eqmod_sub Int.modulus _ _ _ _ H0 H1 as H;
    clear H1 H0
  | (?B * ?C)%Z =>
    int_simpl_mod B H0; int_simpl_mod C H1;
    pose proof Zbits.eqmod_mult Int.modulus _ _ _ _ H0 H1 as H;
    clear H1 H0
  | (- ?B)%Z =>
    int_simpl_mod B H0;
    pose proof Zbits.eqmod_neg Int.modulus _ _ H0 as H;
    clear H0
  | ?B mod Int.modulus =>
    int_simpl_mod B H0;
    pose proof int_modm_mod_elim B _ H0 as H;
    clear H0
  | int_modm ?B =>
    int_simpl_mod B H0;
    pose proof int_modm_mod_elim B _ H0 as H;
    clear H0
  | _ =>
    pose proof Zbits.eqmod_refl Int.modulus A as H
  end.


Definition ptrofs_modm x := x mod Ptrofs.modulus.

Lemma ptrofs_modm_mod_eq: forall x y, Zbits.eqmod Ptrofs.modulus x y -> x mod Ptrofs.modulus = ptrofs_modm y.
Proof.
  intros.
  apply Zbits.eqmod_mod_eq; auto.
  apply Ptrofs.modulus_pos.
Qed.

Lemma ptrofs_modm_mod_elim: forall x y, Zbits.eqmod Ptrofs.modulus x y -> Zbits.eqmod Ptrofs.modulus (x mod Ptrofs.modulus) y.
Proof.
  intros.
  eapply Zbits.eqmod_trans; eauto.
  apply Zbits.eqmod_sym, Zbits.eqmod_mod.
  apply Ptrofs.modulus_pos.
Qed.

Definition ptrofs_reprm := Ptrofs.repr.

Lemma ptrofs_modm_repr_eq: forall x y, Zbits.eqmod Ptrofs.modulus x y -> Ptrofs.repr x = ptrofs_reprm y.
Proof.
  intros.
  apply Ptrofs.eqm_samerepr; auto.
Qed.

Ltac ptrofs_simpl_mod A H :=
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  match A with
  | (?B + ?C)%Z =>
    ptrofs_simpl_mod B H0; ptrofs_simpl_mod C H1;
    pose proof Zbits.eqmod_add Ptrofs.modulus _ _ _ _ H0 H1 as H;
    clear H1 H0
  | (?B - ?C)%Z =>
    ptrofs_simpl_mod B H0; ptrofs_simpl_mod C H1;
    pose proof Zbits.eqmod_sub Ptrofs.modulus _ _ _ _ H0 H1 as H;
    clear H1 H0
  | (?B * ?C)%Z =>
    ptrofs_simpl_mod B H0; ptrofs_simpl_mod C H1;
    pose proof Zbits.eqmod_mult Ptrofs.modulus _ _ _ _ H0 H1 as H;
    clear H1 H0
  | (- ?B)%Z =>
    ptrofs_simpl_mod B H0;
    pose proof Zbits.eqmod_neg Ptrofs.modulus _ _ H0 as H;
    clear H0
  | ?B mod Ptrofs.modulus =>
    ptrofs_simpl_mod B H0;
    pose proof ptrofs_modm_mod_elim B _ H0 as H;
    clear H0
  | ptrofs_modm ?B =>
    ptrofs_simpl_mod B H0;
    pose proof ptrofs_modm_mod_elim B _ H0 as H;
    clear H0
  | _ =>
    pose proof Zbits.eqmod_refl Ptrofs.modulus A as H
  end.

Ltac solve_mod_modulus :=
  unfold Int.add; rewrite ?Int.unsigned_repr_eq;
  unfold Ptrofs.add; rewrite ?Ptrofs.unsigned_repr_eq;
  repeat
  match goal with
  | |- context [?A mod Int.modulus] =>
         let H := fresh "H" in int_simpl_mod A H;
         rewrite (int_modm_mod_eq A _ H);
         clear H
  | |- context [Int.repr ?A] =>
         let H := fresh "H" in int_simpl_mod A H;
         rewrite (int_modm_repr_eq A _ H);
         clear H
  | |- context [?A mod Ptrofs.modulus] =>
         let H := fresh "H" in int_simpl_mod A H;
         rewrite (int_modm_mod_eq A _ H);
         clear H
  | |- context [Int.repr ?A] =>
         let H := fresh "H" in int_simpl_mod A H;
         rewrite (int_modm_repr_eq A _ H);
         clear H
  | |- context [?A mod Ptrofs.modulus] =>
         let H := fresh "H" in ptrofs_simpl_mod A H;
         rewrite (ptrofs_modm_mod_eq A _ H);
         clear H
  | |- context [Ptrofs.repr ?A] =>
         let H := fresh "H" in ptrofs_simpl_mod A H;
         rewrite (ptrofs_modm_repr_eq A _ H);
         clear H
  | |- context [?A mod Ptrofs.modulus] =>
         let H := fresh "H" in ptrofs_simpl_mod A H;
         rewrite (ptrofs_modm_mod_eq A _ H);
         clear H
  | |- context [Ptrofs.repr ?A] =>
         let H := fresh "H" in ptrofs_simpl_mod A H;
         rewrite (ptrofs_modm_repr_eq A _ H);
         clear H
  end;
  unfold int_modm, int_reprm, ptrofs_modm, ptrofs_reprm in *.

(**************************************************

List lemmas

**************************************************)

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
apply Int.eqm_mult; unfold Int.eqm; apply Zbits.eqmod_sym;
apply Zbits.eqmod_mod; compute; congruence.
Qed.

Lemma sub_repr: forall i j,
  Int.sub (Int.repr i) (Int.repr j) = Int.repr (i-j).
Proof.
  intros.
 unfold Int.sub.
 apply Int.eqm_samerepr.
 unfold Int.eqm.
 apply Int.eqm_sub; apply Int.eqm_sym; apply Int.eqm_unsigned_repr.
Qed.

Lemma ptrofs_add_repr: forall i j, Ptrofs.add (Ptrofs.repr i) (Ptrofs.repr j) = Ptrofs.repr (i+j).
Proof. intros.
  rewrite Ptrofs.add_unsigned.
 apply Ptrofs.eqm_samerepr.
 unfold Ptrofs.eqm.
 apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma ptrofs_mul_repr:
 forall x y, Ptrofs.mul (Ptrofs.repr x) (Ptrofs.repr y) = Ptrofs.repr (x * y).
Proof.
intros. unfold Ptrofs.mul.
apply Ptrofs.eqm_samerepr.
repeat rewrite Ptrofs.unsigned_repr_eq.
apply Ptrofs.eqm_mult; unfold Ptrofs.eqm; apply Zbits.eqmod_sym;
apply Zbits.eqmod_mod; compute; congruence.
Qed.

Lemma ptrofs_sub_repr: forall i j,
  Ptrofs.sub (Ptrofs.repr i) (Ptrofs.repr j) = Ptrofs.repr (i-j).
Proof.
  intros.
 unfold Ptrofs.sub.
 apply Ptrofs.eqm_samerepr.
 unfold Ptrofs.eqm.
 apply Ptrofs.eqm_sub; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma Zland_two_p:
 forall i n, (0 <= n)%Z -> Z.land i (Z.ones n) = i mod (2 ^ n).
Proof.
intros.
rewrite Z.land_ones by auto.
reflexivity.
Qed.

Lemma and_repr
     : forall i j : Z, Int.and (Int.repr i) (Int.repr j) = Int.repr (Z.land i j).
Proof.
  intros.
  unfold Int.and.
  rewrite <- (Int.repr_unsigned (Int.repr (Z.land i j))).
  rewrite !Int.unsigned_repr_eq.
  change Int.modulus with (2 ^ 32).
  rewrite <- !Zland_two_p by lia.
  f_equal.
  rewrite <- !Z.land_assoc.
  f_equal.
  rewrite (Z.land_comm (Z.ones 32)).
  rewrite <- !Z.land_assoc.
  f_equal.
Qed.

Lemma or_repr
     : forall i j : Z, Int.or (Int.repr i) (Int.repr j) = Int.repr (Z.lor i j).
Proof.
  intros.
  unfold Int.or.
  rewrite <- (Int.repr_unsigned (Int.repr (Z.lor i j))).
  rewrite !Int.unsigned_repr_eq.
  change Int.modulus with (2 ^ 32).
  rewrite <- !Zland_two_p by lia.
  f_equal.
  rewrite <- Z.land_lor_distr_l.
  reflexivity.
Qed.

Lemma add64_repr: forall i j, Int64.add (Int64.repr i) (Int64.repr j) = Int64.repr (i+j).
Proof. intros.
  rewrite Int64.add_unsigned.
 apply Int64.eqm_samerepr.
 unfold Int64.eqm.
 apply Int64.eqm_add; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma mul64_repr:
 forall x y, Int64.mul (Int64.repr x) (Int64.repr y) = Int64.repr (x * y).
Proof.
intros. unfold Int64.mul.
apply Int64.eqm_samerepr.
repeat rewrite Int64.unsigned_repr_eq.
apply Int64.eqm_mult; unfold Int64.eqm; apply Zbits.eqmod_sym;
apply Zbits.eqmod_mod; compute; congruence.
Qed.

Lemma sub64_repr: forall i j,
  Int64.sub (Int64.repr i) (Int64.repr j) = Int64.repr (i-j).
Proof.
 intros. unfold Int64.sub.
 apply Int64.eqm_samerepr.
 unfold Int64.eqm.
 apply Int64.eqm_sub; apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

Lemma and64_repr
     : forall i j : Z, Int64.and (Int64.repr i) (Int64.repr j) = Int64.repr (Z.land i j).
Proof.
  intros.
  unfold Int64.and.
  rewrite <- (Int64.repr_unsigned (Int64.repr (Z.land i j))).
  rewrite !Int64.unsigned_repr_eq.
  change Int64.modulus with (2 ^ 64).
  rewrite <- !Zland_two_p by lia.
  f_equal.
  rewrite <- !Z.land_assoc.
  f_equal.
  rewrite (Z.land_comm (Z.ones 64)).
  rewrite <- !Z.land_assoc.
  f_equal.
Qed.

Lemma or64_repr
     : forall i j : Z, Int64.or (Int64.repr i) (Int64.repr j) = Int64.repr (Z.lor i j).
Proof.
  intros.
  unfold Int64.or.
  rewrite <- (Int64.repr_unsigned (Int64.repr (Z.lor i j))).
  rewrite !Int64.unsigned_repr_eq.
  change Int64.modulus with (2 ^ 64).
  rewrite <- !Zland_two_p by lia.
  f_equal.
  rewrite <- Z.land_lor_distr_l.
  reflexivity.
Qed.

Lemma neg_repr: forall i, Int.neg (Int.repr i) = Int.repr (-i).
Proof.
intros. unfold Int.neg.
apply Int.eqm_samerepr.
apply Int.eqm_neg.
apply Int.eqm_unsigned_repr_l.
apply Int.eqm_refl.
Qed.

Lemma neg64_repr: forall i, Int64.neg (Int64.repr i) = Int64.repr (-i).
Proof.
intros. unfold Int64.neg.
apply Int64.eqm_samerepr.
apply Int64.eqm_neg.
apply Int64.eqm_unsigned_repr_l.
apply Int64.eqm_refl.
Qed.

Arguments Int.unsigned n : simpl never.
Arguments Ptrofs.unsigned n : simpl never.
Arguments Pos.to_nat !x / .

Lemma align_0: forall z,
    z > 0 -> align 0 z = 0.
Proof. unfold align; intros. rewrite Zdiv_small; lia.
Qed.
#[export] Hint Rewrite align_0 using lia : norm.

Lemma align_1: forall n, align n 1 = n.
Proof.  intros; unfold align. rewrite Z.div_1_r. rewrite Z.mul_1_r. lia.
Qed.
#[export] Hint Rewrite align_1 using lia : norm.

Lemma fold_right_andb: forall bl b, fold_right andb b bl = true -> forall b0, In b0 bl -> b0 = true.
Proof.
  intros.
  induction bl.
  + inversion H0.
  + destruct H0.
    - simpl in H.
      rewrite andb_true_iff in H.
      subst; tauto.
    - simpl in H.
      rewrite andb_true_iff in H.
      tauto.
Qed.

Lemma Z2Nat_inj_0: forall z, z >= 0 -> Z.to_nat z = 0%nat -> z = 0.
Proof.
  intros.
  destruct (zlt 0 z).
  + replace z with (1 + (z - 1)) in H0 by lia.
    rewrite Z2Nat.inj_add in H0 by lia.
    change (Z.to_nat 1) with (1%nat) in H0.
    inversion H0.
  + lia.
Qed.

Lemma Z2Nat_id': forall n, Z.of_nat (Z.to_nat n) = Z.max 0 n.
Proof.
intros.
 destruct (zlt n 0).
 rewrite Z2Nat_neg by auto. rewrite Z.max_l by lia; reflexivity.
 rewrite Z2Nat.id, Z.max_r by lia; lia.
Qed.

Lemma nil_or_non_nil: forall {A} (a: list A), {a = nil} + {a <> nil}.
Proof.
  intros.
  destruct a; [left | right]; congruence.
Qed.

Lemma Permutation_concat: forall {A} (P Q: list (list A)),
  Permutation P Q ->
  Permutation (concat P) (concat Q).
Proof.
  intros.
  induction H.
  + apply Permutation_refl.
  + simpl.
    apply Permutation_app_head; auto.
  + simpl.
    rewrite !app_assoc.
    apply Permutation_app_tail.
    apply Permutation_app_comm.
  + eapply Permutation_trans; eauto.
Qed.

Lemma proj_sumbool_is_false:
  forall (P: Prop) (a: {P}+{~P}), ~P -> proj_sumbool a = false.
Proof.
intros. destruct a; auto; contradiction.
Qed.
#[export] Hint Rewrite proj_sumbool_is_true using (solve [auto 3]) : norm.
#[export] Hint Rewrite proj_sumbool_is_false using (solve [auto 3]) : norm.

Lemma ptrofs_to_int_repr:
 forall x, (Ptrofs.to_int (Ptrofs.repr x)) = Int.repr x.
Proof.
intros.
destruct Archi.ptr64 eqn:Hp.
*
unfold Ptrofs.to_int.
apply Int.eqm_samerepr.
unfold Int.eqm.
rewrite Ptrofs.unsigned_repr_eq.
unfold Ptrofs.modulus.
unfold Ptrofs.wordsize.
unfold Wordsize_Ptrofs.wordsize.
rewrite Hp.
unfold Int.modulus.
unfold Int.wordsize.
unfold Wordsize_32.wordsize.
apply Zbits.eqmod_divides with (two_power_nat 64).
apply Zbits.eqmod_sym.
apply Zbits.eqmod_mod.
compute. auto.
exists (two_power_nat 32).
reflexivity.
*
erewrite Ptrofs.agree32_to_int_eq. reflexivity.
apply Ptrofs.agree32_repr.
auto.
Qed.

Lemma ptrofs_to_int64_repr:
 Archi.ptr64 = true ->
 forall x, (Ptrofs.to_int64 (Ptrofs.repr x)) = Int64.repr x.
Proof.
intros Hp x.
unfold Ptrofs.to_int64.
apply Int64.eqm_samerepr.
unfold Int64.eqm.
rewrite Ptrofs.unsigned_repr_eq.
unfold Ptrofs.modulus.
unfold Ptrofs.wordsize.
unfold Wordsize_Ptrofs.wordsize.
rewrite Hp.
unfold Int64.modulus.
unfold Int64.wordsize.
unfold Wordsize_64.wordsize.
apply Zbits.eqmod_divides with (two_power_nat 64).
apply Zbits.eqmod_sym.
apply Zbits.eqmod_mod.
compute. auto.
exists 1.
reflexivity.
Qed.

Lemma app_cons_assoc : forall {A} l1 (x : A) l2, l1 ++ x :: l2 = (l1 ++ (x :: nil)) ++ l2.
Proof.
  intros; rewrite <- app_assoc; auto.
Qed.

Lemma Zmod_smallish : forall x y, y <> 0 -> 0 <= x < 2 * y ->
  x mod y = x \/ x mod y = x - y.
Proof.
  intros.
  destruct (zlt x y); [left; apply Zmod_small; lia|].
  rewrite <- Z.mod_add with (b := -1) by auto.
  right; apply Zmod_small; lia.
Qed.

Lemma Zmod_plus_inv : forall a b c d (Hc : c > 0) (Heq : (a + b) mod c = (d + b) mod c),
  a mod c = d mod c.
Proof.
  intros; rewrite Zplus_mod, (Zplus_mod d) in Heq.
  pose proof (Z_mod_lt a c Hc).
  pose proof (Z_mod_lt b c Hc).
  pose proof (Z_mod_lt d c Hc).
  destruct (Zmod_smallish (a mod c + b mod c) c), (Zmod_smallish (d mod c + b mod c) c); lia.
Qed.

Lemma lt_le_1 : forall (i j: Z), i < j <-> i + 1 <= j.
Proof.
  intros; lia.
Qed.

Lemma Permutation_filter : forall {A} (f : A -> bool) l1 l2, Permutation l1 l2 ->
  Permutation (filter f l1) (filter f l2).
Proof.
  induction 1; simpl; auto.
  - destruct (f x); auto.
  - destruct (f x); auto. destruct (f y); auto.
    constructor.
  - etransitivity; eauto.
Qed.

Lemma Permutation_Zlength : forall {A} (l1 l2 : list A), Permutation l1 l2 ->
  Zlength l1 = Zlength l2.
Proof.
  intros. rewrite !Zlength_correct. f_equal.
  apply Permutation_length; auto.
Qed.
