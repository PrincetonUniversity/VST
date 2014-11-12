Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.mapsto_memory_block.
Local Open Scope logic.

Definition Znth {X} n (xs: list X) (default: X) :=
  if (zlt n 0) then default else nth (Z.to_nat n) xs default.

Fixpoint rangespec' (lo: Z) (n: nat) (P: Z -> val -> mpred): val -> mpred :=
  match n with
  | O => fun _ => emp
  | S n' => P lo * rangespec' (Zsucc lo) n' P
 end.

Definition rangespec (lo hi: Z) (P: Z -> val -> mpred) : val -> mpred :=
  rangespec' lo (nat_of_Z (hi-lo)) P.

Fixpoint fold_range' {A: Type} (f: Z -> A -> A) (zero: A) (lo: Z) (n: nat) : A :=
 match n with
  | O => zero
  | S n' => f lo (fold_range' f  zero (Zsucc lo) n')
 end.

Definition fold_range {A: Type} (f: Z -> A -> A) (zero: A) (lo hi: Z) : A :=
  fold_range' f zero lo (nat_of_Z (hi-lo)).

Lemma rangespec'_shift_derives: forall lo lo' len P P' p p',
  (forall i i', lo <= i < lo + Z_of_nat len -> i - lo = i' - lo' -> P i p |-- P' i' p') -> 
  rangespec' lo len P p |-- rangespec' lo' len P' p'.
Proof.
  intros.
  revert lo lo' H; 
  induction len; intros.
  + simpl. auto.
  + simpl.
    apply sepcon_derives.
    - apply H; [| omega].
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_r.
      omega.
    - apply IHlen. intros.
      apply H; [| omega].
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_r.
      pose proof Zle_0_nat (S len).
      omega.
Qed.

Lemma rangespec'_ext_derives: forall lo len P P' p,
  (forall i, lo <= i < lo + Z_of_nat len -> P i p |-- P' i p) -> 
  rangespec' lo len P p |-- rangespec' lo len P' p.
Proof.
  intros.
  apply rangespec'_shift_derives.
  intros.
  assert (i = i') by omega.
  subst.
  apply H.
  auto.
Qed.

Lemma rangespec'_shift: forall lo lo' len P P' p p',
  (forall i i', lo <= i < lo + Z_of_nat len -> i - lo = i' - lo' -> P i p = P' i' p') -> 
  rangespec' lo len P p = rangespec' lo' len P' p'.
Proof.
  intros; apply pred_ext; apply rangespec'_shift_derives;
  intros.
  + erewrite H; eauto.
  + erewrite H; eauto.
    omega.
Qed.

Lemma rangespec'_ext: forall lo len P P' p,
  (forall i, lo <= i < lo + Z_of_nat len -> P i p = P' i p) -> 
  rangespec' lo len P p = rangespec' lo len P' p.
Proof.
  intros; apply pred_ext; apply rangespec'_ext_derives;
  intros; rewrite H; auto.
Qed.

Lemma rangespec_ext_derives: forall lo hi P P' p,
  (forall i, lo <= i < hi -> P i p |-- P' i p) -> 
  rangespec lo hi P p |-- rangespec lo hi P' p.
Proof.
  intros.
  unfold rangespec.
  apply rangespec'_ext_derives.
  intros.
  destruct (zlt lo hi).
  + apply H.
    rewrite nat_of_Z_max in H0.
    rewrite Z.max_l in H0 by omega.
    omega.
  + rewrite nat_of_Z_max in H0.
    rewrite Z.max_r in H0 by omega.
    omega.
Qed.

Lemma rangespec_ext: forall lo hi P P' p,
  (forall i, lo <= i < hi -> P i p = P' i p) -> 
  rangespec lo hi P p = rangespec lo hi P' p.
Proof.
  intros; apply pred_ext; apply rangespec_ext_derives;
  intros; rewrite H; auto.
Qed.

Lemma rangespec'_elim: forall lo len P i,
  lo <= i < lo + Z_of_nat len -> rangespec' lo len P |-- P i * TT.
Proof.
  intros. revert lo i H; induction len; intros.
  + simpl in H. omega.
  + simpl. intros; destruct (Z.eq_dec i lo).
    - subst. cancel.
    - replace (P i x * !!True) with (TT * (P i x * TT)) by (apply pred_ext; cancel).
      apply sepcon_derives; [cancel |].
      apply IHlen.
      rewrite Nat2Z.inj_succ in H.
      rewrite <- Z.add_1_l in *.
      omega.
Qed.

Lemma prop_false_andp {A}{NA :NatDed A}:
 forall P Q, ~P -> !! P && Q = FF.
Proof.
intros.
apply pred_ext; normalize.
Qed.
Lemma orp_FF {A}{NA: NatDed A}:
 forall Q, Q || FF = Q.
Proof.
intros. apply pred_ext. apply orp_left; normalize. apply orp_right1; auto.
Qed.
Lemma FF_orp {A}{NA: NatDed A}:
 forall Q, FF || Q = Q.
Proof.
intros. apply pred_ext. apply orp_left; normalize. apply orp_right2; auto.
Qed.

Lemma Znth_succ: forall {A} i lo (v: list A), Z.succ lo <= i -> Znth (i - lo) v = Znth (i - (Z.succ lo)) (skipn 1 v).
Proof.
  intros.
  extensionality default.
  unfold Znth.
  if_tac; [omega |].
  if_tac; [omega |].
  rewrite nth_skipn.
  f_equal.
  change 1%nat with (Z.to_nat 1).
  rewrite <- Z2Nat.inj_add by omega.
  f_equal.
  omega.
Qed.

Lemma Znth_skipn: forall {A} n xs (default: A),
  0 <= n ->
  Znth 0 (skipn (nat_of_Z n) xs) default = Znth n xs default.
Proof.
  intros.
  unfold Znth.
  if_tac; [omega |].
  if_tac; [omega |].
  rewrite nth_skipn.
  reflexivity.
Qed.

Lemma split3_full_length_list: forall {A} lo mid hi (ct: list A) d,
  lo <= mid < hi ->
  Zlength ct = hi - lo ->
  ct = firstn (Z.to_nat (mid - lo)) ct ++
       (Znth (mid - lo) ct d :: nil) ++
       skipn (Z.to_nat (mid - lo + 1)) ct.
Proof.
  intros.
  rewrite <- firstn_skipn with (l := ct) (n := Z.to_nat (mid - lo)) at 1.
  f_equal.
  rewrite Z2Nat.inj_add by omega.
  rewrite <- skipn_skipn.
  replace (Znth (mid - lo) ct d :: nil) with (firstn (Z.to_nat 1) (skipn (Z.to_nat (mid - lo)) ct)).
  + rewrite firstn_skipn; reflexivity.
  + unfold Znth.
    if_tac; [omega |].
    rewrite firstn_1_skipn; [reflexivity |].
    rewrite <- (Nat2Z.id (length ct)).
    apply Z2Nat.inj_lt.
    - omega.
    - omega.
    - rewrite Zlength_correct in H0.
      omega.
Qed.

