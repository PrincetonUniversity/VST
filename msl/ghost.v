Require Import VST.msl.sepalg.

Class Ghost := { G : Type; valid : G -> Prop;
  Join_G :> Join G; Sep_G :> Sep_alg G; Perm_G :> Perm_alg G;
  join_valid : forall a b c, join a b c -> valid c -> valid a }.

Section Update.

Context {RA: Ghost}.

Lemma core_valid: forall a, valid a -> valid (core a).
Proof.
  intros; eapply join_valid; eauto.
  apply core_unit.
Qed.

Definition valid_2 a b := exists c, join a b c /\ valid c.

Definition fp_update_ND a B := forall c, valid_2 a c -> exists b, B b /\ valid_2 b c.

Definition fp_update a b := forall c, valid_2 a c -> valid_2 b c.

Lemma fp_update_equiv: forall a b, fp_update a b <-> fp_update_ND a (eq b).
Proof.
  split; repeat intro.
  - exists b; split; eauto; constructor.
  - destruct (H _ H0) as (? & Hx & ?); inversion Hx; auto.
Qed.

End Update.
