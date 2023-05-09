From iris.algebra Require Import proofmode_classes big_op auth.
From VST.veric Require Export view.
From iris.prelude Require Import options.

Lemma auth_view_rel_order : ∀ {A : uora} (H : ∀n (x y : A), x ≼ₒ{n} y → x ≼{n} y) n (a x y : A),
  x ≼ₒ{n} y → auth_view_rel n a y → auth_view_rel n a x.
Proof.
  inversion 3; split=> //.
  trans y; auto.
Qed.

Definition authR (A : uora) (H : ∀n (x y : A), x ≼ₒ{n} y → x ≼{n} y) : ora := view.viewR (A:=A) (B:=A) auth_view_rel (auth_view_rel_order H).
Definition authUR (A : uora) (H : ∀n (x y : A), x ≼ₒ{n} y → x ≼{n} y) : uora :=
  (Uora' (auth A) (ofe_mixin (authO A)) (cmra_mixin (algebra.auth.authR A)) (ora_mixin (authR A H)) (view_ucmra_mixin auth_view_rel)).
