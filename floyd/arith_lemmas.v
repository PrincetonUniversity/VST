Require Import Clightdefs.
Require Import msl.Extensionality.
Require Import Coqlib msl.Coqlib2 floyd.coqlib3.

Lemma divide_align: forall x y: Z, x > 0 -> Zdivide x y -> align y x = y.
Proof.
  intros.
  unfold align.
  destruct H0.
  rewrite H0.
  pose proof Zdiv_unique (x0 * x + x - 1) x x0 (x - 1).
  assert (x0 * x + x - 1 = x0 * x + (x - 1)) by omega.
  assert (0 <= x - 1 < x) by omega.
  rewrite (H1 H2 H3).
  reflexivity.
Qed.

Lemma Z2Nat_neg: forall i, i < 0 -> Z.to_nat i = 0%nat.
Proof.
  intros.
  destruct i; try reflexivity.
  pose proof Zgt_pos_0 p; omega.
Qed.

Lemma Int_unsigned_repr_le: forall a, 0 <= a -> Int.unsigned (Int.repr a) <= a.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  apply Z.mod_le; auto.
  cbv.
  auto.
Qed.

Lemma arith_aux00: forall a b, b <= a -> 0%nat = nat_of_Z (a - b) -> a - b = 0.
Proof.
  intros.
  pose proof Z2Nat.id (a - b).
  unfold nat_of_Z in H0.
  rewrite <- H0 in H1.
  simpl Z.of_nat in H1.
  omega.
Qed.

Lemma arith_aux01: forall a b n, S n = nat_of_Z (a - b) -> b < a.
Proof.
  intros.
  destruct (zlt a b); auto.
  + rewrite Z2Nat_neg in H by omega.
    inversion H.
  + pose proof Z2Nat.id (a - b).
    unfold nat_of_Z in H; rewrite <- H in H0.
    spec H0; [omega |].
    rewrite Nat2Z.inj_succ in H0.
    omega.
Qed.

Lemma arith_aux02: forall n a b, S n = nat_of_Z (a - b) -> n = nat_of_Z (a - Z.succ b).
Proof.
  intros.
  pose proof arith_aux01 _ _ _ H.
  unfold nat_of_Z in *.
  pose proof Z2Nat.id (a - b).
  spec H1; [omega |].
  rewrite <- H in H1.
  replace (a - Z.succ b) with (a - b - 1) by omega.
  rewrite <- H1.
  rewrite Nat2Z.inj_succ.
  replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) by omega.
  rewrite Nat2Z.id.
  auto.
Qed.

Lemma arith_aux03: forall a b c,
  0 <= b ->
  0 <= a + b * c ->
  0 <= a + b * Z.succ c.
Proof.
  intros.
  assert (b * c <= b * Z.succ c) by (apply Zmult_le_compat_l; omega).
  omega.
Qed.

Lemma arith_aux04: forall a b c,
  0 <= b <= c ->
  (a | b) ->
  (a | b mod c).
Proof.
  intros.
  destruct (zlt b c).
  + rewrite Zmod_small by omega.
    auto.
  + assert (b = c) by omega.
    subst.
    rewrite Z_mod_same_full.
    apply Z.divide_0_r.
Qed.

Ltac inv_int i :=
  let ofs := fresh "ofs" in
  let H := fresh "H" in
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  pose proof Int.repr_unsigned i as H;
  pose proof Int.unsigned_range i as H0;
  remember (Int.unsigned i) as ofs eqn:H1;
  rewrite <- H in *;
  clear H H1; try clear i.

Definition modm x := x mod Int.modulus.

Lemma modm_mod_eq: forall x y, Int.eqmod Int.modulus x y -> x mod Int.modulus = modm y.
Proof.
  intros.
  apply Int.eqmod_mod_eq; auto.
  apply Int.modulus_pos.
Qed.

Lemma modm_mod_elim: forall x y, Int.eqmod Int.modulus x y -> Int.eqmod Int.modulus (x mod Int.modulus) y.
Proof.
  intros.
  eapply Int.eqmod_trans; eauto.
  apply Int.eqmod_sym, Int.eqmod_mod.
  apply Int.modulus_pos.
Qed.

Definition reprm := Int.repr.

Lemma modm_repr_eq: forall x y, Int.eqmod Int.modulus x y -> Int.repr x = reprm y.
Proof.
  intros.
  apply Int.eqm_samerepr; auto.
Qed.

Ltac simpl_mod A H :=
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  match A with
  | (?B + ?C)%Z =>
    simpl_mod B H0; simpl_mod C H1;
    pose proof Int.eqmod_add Int.modulus _ _ _ _ H0 H1 as H;
    clear H1 H0
  | (?B - ?C)%Z =>
    simpl_mod B H0; simpl_mod C H1;
    pose proof Int.eqmod_sub Int.modulus _ _ _ _ H0 H1 as H;
    clear H1 H0
  | (?B * ?C)%Z =>
    simpl_mod B H0; simpl_mod C H1;
    pose proof Int.eqmod_mult Int.modulus _ _ _ _ H0 H1 as H;
    clear H1 H0
  | (- ?B)%Z =>
    simpl_mod B H0;
    pose proof Int.eqmod_neg Int.modulus _ _ H0 as H;
    clear H0
  | ?B mod Int.modulus =>
    simpl_mod B H0;
    pose proof modm_mod_elim B _ H0 as H;
    clear H0
  | modm ?B =>
    simpl_mod B H0;
    pose proof modm_mod_elim B _ H0 as H;
    clear H0
  | _ =>
    pose proof Int.eqmod_refl Int.modulus A as H
  end.

Ltac solve_mod_modulus :=
  try unfold Int.add; try rewrite !Int.unsigned_repr_eq;
  repeat
  match goal with
  | |- context [?A mod Int.modulus] =>
         let H := fresh "H" in simpl_mod A H;
         rewrite (modm_mod_eq A _ H);
         clear H
  | |- context [Int.repr ?A] =>
         let H := fresh "H" in simpl_mod A H;
         rewrite (modm_repr_eq A _ H);
         clear H
  end;
  try unfold modm in *;
  try unfold reprm in *.

Ltac pose_mod_le A :=
  let H := fresh "H" in
  pose proof Z.mod_le A Int.modulus;
  spec H; [try omega | spec H; [pose Int.modulus_pos; omega |]].

Ltac pose_mul_distr_l l r :=
  match r with
  | (?A + ?B)%Z => pose proof Z.mul_add_distr_l l A B;
                   pose_mul_distr_l l A;
                   pose_mul_distr_l l B
  | Z.succ ?A => let H := fresh "H" in
                 pose proof Z.mul_add_distr_l l A 1 as H;
                 replace (A + 1) with (Z.succ A) in H by omega;
                 pose_mul_distr_l l A
  | (?A - ?B)%Z => pose proof Z.mul_sub_distr_l l A B;
                   pose_mul_distr_l l A;
                   pose_mul_distr_l l B
  | _ => idtac
  end.


Ltac pose_size_mult' env t l :=
  match l with
  | nil => idtac
  | ?z :: ?l0 =>
    match l0 with
    | nil => pose_mul_distr_l (sizeof env t) z
    | ?z0 :: _ => pose_mul_distr_l (sizeof env t) z;
                  assert (sizeof env t * z <= sizeof env t * z0) by
                    (pose proof sizeof_pos env t; apply Zmult_le_compat_l; omega);
                  pose_size_mult' env t l0
    end
  end.

Ltac pose_size_mult env t l :=
  pose_size_mult' env t l;
  try rewrite !Z.mul_0_r in *;
  try rewrite !Z.mul_1_r in *.

Definition align_alignof a b := align a b.

Definition sizeof_struct_le := sizeof_struct.

Ltac pose_align_le :=
  repeat
  match goal with
  | |- context [align ?A (alignof ?env ?t)] =>
         assert (A <= align A (alignof env t)) by (apply align_le, alignof_pos);
         change (align A (alignof env t)) with (align_alignof A (alignof env t))
  | |- context [align ?A (co_alignof ?co)] =>
         let x := fresh "x" in
         assert (A <= align A (co_alignof co)) by (apply align_le; destruct (co_alignof_two_p co) as [x ?];
           pose proof two_power_nat_pos x; omega);
         change (align A (co_alignof co)) with (align_alignof A (co_alignof co))
  | |- context [sizeof_struct ?env ?A ?m] =>
         pose proof sizeof_struct_incr env m A;
         change (sizeof_struct env A m) with (sizeof_struct_le env A m)
  end;
  try unfold align_alignof in *;
  try unfold sizeof_struct_le in *.

Definition sizeofp := sizeof.

Ltac pose_sizeof_pos :=
  repeat
  match goal with
  | |- context [sizeof ?env ?t] =>
         pose proof sizeof_pos env t;
         change (sizeof env t) with (sizeofp env t)
  end;
  unfold sizeofp in *.

Lemma align_0: forall z, 
    z > 0 -> align 0 z = 0.
Proof. unfold align; intros. rewrite Zdiv_small; omega.
Qed.
Hint Rewrite align_0 using omega : norm.

Lemma align_1: forall n, align n 1 = n.
Proof.  intros; unfold align. rewrite Z.div_1_r. rewrite Z.mul_1_r. omega.
Qed.
Hint Rewrite align_1 using omega : norm.

