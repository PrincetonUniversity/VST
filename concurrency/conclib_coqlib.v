Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.ZArith.ZArith.

Require Import compcert.lib.Coqlib.
Require Import VST.msl.eq_dec.

Import ListNotations.
Local Open Scope Z.

Definition remove_at {A} i (l : list A) := firstn i l ++ skipn (S i) l.


Lemma app_cons_assoc : forall {A} l1 (x : A) l2, l1 ++ x :: l2 = (l1 ++ [x]) ++ l2.
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


Lemma eq_dec_refl : forall {A B} {A_eq : EqDec A} (a : A) (b c : B), (if eq_dec a a then b else c) = b.
Proof.
  intros; destruct (eq_dec a a); [|contradiction n]; auto.
Qed.
