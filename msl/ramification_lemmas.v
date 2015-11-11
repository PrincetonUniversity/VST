(* The spec and proof of the following rules are based on "The Ramifications  *)
(* of Sharing in Data Structures" by Aquinas Hobor and Jules Villard.         *)
(*    RAMIF_PLAIN.frame                                                       *)
(*    RAMIF_PLAIN.split                                                       *)
(* The following lemmas are found useful by Shengyi Wang, Qinxiang Cao and    *)
(* Aquinas Hobor in 2015 summer in Yale-NUS.                                  *)
(*    RAMIF_PLAIN.solve                                                       *)
(*    RAMIF_Q.reduce                                                          *)
(*    RAMIF_Q.solve                                                           *)
(*    RAMIF_Q.frame                                                           *)
(*    RAMIF_Q.split                                                           *)
(* The following lemmas are developed by Qinxiang Cao in 2015 in Princeton.   *)
(*    RAMIF_PLAIN.trans                                                       *)
(*    RAMIF_PLAIN.weak_ramif_spec                                             *)
(*    RAMIF_Q.trans                                                           *)
(*    RAMIF_Q.weak_ramif_spec                                                 *)
(*    RAMIF_Q.plain_spec                                                      *)

Require Import msl.base.
Require Import msl.simple_CCC.
Require Import msl.seplog.
Require Import msl.log_normalize.

Local Open Scope logic.

Module RAMIF_PLAIN.
Section RAMIF_PLAIN.

Context {A : Type}.
Context {ND : NatDed A}.
Context {SL : SepLog A}.

Lemma solve: forall g l g' l' F, g |-- l * F -> F * l' |-- g' -> g |-- l * (l' -* g').
Proof.
  intros.
  apply derives_trans with (l * F); auto.
  apply sepcon_derives; auto.
  apply wand_sepcon_adjoint.
  auto.
Qed.

Lemma weak_ramif_spec: forall g l g' l', g |-- l * (l' -* g') -> g |-- l * TT.
Proof.
  intros.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; auto.
  apply TT_right.
Qed.

Lemma trans: forall g m l g' m' l', g |-- m * (m' -* g') -> m |-- l * (l' -* m') -> g |-- l * (l' -* g').
Proof.
  intros.
  apply solve with ((l' -* m') * (m' -* g')).
  + eapply derives_trans; [exact H |].
    eapply derives_trans; [apply sepcon_derives; [exact H0 | apply derives_refl] |].
    rewrite sepcon_assoc; auto.
  + rewrite (sepcon_comm _ l'), <- sepcon_assoc.
    eapply derives_trans; [| apply modus_ponens_wand].
    apply sepcon_derives; [| apply derives_refl].
    apply modus_ponens_wand.
Qed.

Lemma frame: forall g l g' l' F, g |-- l * (l' -* g') -> g * F |-- l * (l' -* g' * F).
Proof.
  intros.
  apply solve with ((l' -* g') * F).
  + rewrite <- sepcon_assoc.
    apply sepcon_derives; auto.
  + rewrite (sepcon_comm _ l'), <- sepcon_assoc.
    apply sepcon_derives; [apply modus_ponens_wand | auto].
Qed.

Lemma split: forall g1 g2 l1 l2 g1' g2' l1' l2',
  g1 |-- l1 * (l1' -* g1') ->
  g2 |-- l2 * (l2' -* g2') ->
  g1 * g2 |-- (l1 * l2) * (l1' * l2' -* g1' * g2').
Proof.
  intros.
  apply solve with ((l1' -* g1') * (l2' -* g2')).
  + rewrite (sepcon_assoc l1), <- (sepcon_assoc l2), (sepcon_comm l2), (sepcon_assoc _ l2), <- (sepcon_assoc l1).
    apply sepcon_derives; auto.
  + eapply derives_trans; [apply sepcon_derives; [apply wand_sepcon_wand | apply derives_refl] |].
    rewrite sepcon_comm; apply modus_ponens_wand.
Qed.

End RAMIF_PLAIN.
End RAMIF_PLAIN.

Module RAMIF_Q.
Section RAMIF_Q.

Context {A : Type}.
Context {ND : NatDed A}.
Context {SL : SepLog A}.

Lemma reduce: forall {B} g l (g' l': B -> A),
  g |-- l * (allp (l' -* g')) ->
  g |-- l * (exp l' -* exp g').
Proof.
  intros.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; [auto |].
  apply wand_sepcon_adjoint.
  rewrite exp_sepcon2.
  apply exp_left; intro x; apply (exp_right x).
  apply wand_sepcon_adjoint.
  apply (allp_left _ x).
  auto.
Qed.

Lemma solve: forall {B} g l g' l' F,
  g |-- l * F ->
  (forall x: B, F * l' x |-- g' x) ->
  g |-- l * (allp (l' -* g')).
Proof.
  intros.
  apply derives_trans with (l * F); auto.
  apply sepcon_derives; auto.
  apply allp_right; intro x.
  simpl;
  apply wand_sepcon_adjoint.
  apply H0.
Qed.

Lemma weak_ramif_spec: forall {B} g l (g' l': B -> A),
  g |-- l * allp (l' -* g') -> g |-- l * TT.
Proof.
  intros.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; auto.
  apply TT_right.
Qed.

Lemma plain_spec: forall {B} g l g' l' (x: B),
  g |-- l * (allp (l' -* g')) ->
  g |-- l *  (l' x -* g' x).
Proof.
  intros.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; [auto |].
  apply (allp_left _ x); auto.
Qed.

Lemma trans: forall {B C} g m l g' mG' mL' l' (f: B -> C),
  (forall b, mL' b |-- mG' (f b)) ->
  g |-- m * allp (mG' -* g') ->
  m |-- l * allp (l' -* mL') ->
  g |-- l * allp (l' -* Basics.compose g' f).
Proof.
  intros.
  apply solve with (allp (l' -* mL') * allp (mG' -* g')); auto.
  + eapply derives_trans; [exact H0 |].
    eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl] |].
    rewrite sepcon_assoc; auto.
  + intro x.
    rewrite sepcon_assoc.
    apply wand_sepcon_adjoint.
    apply (allp_left _ x).
    apply wand_sepcon_adjoint.
    rewrite sepcon_comm, sepcon_assoc, sepcon_comm.
    apply wand_sepcon_adjoint.
    apply derives_trans with (mG' (f x)).
    - eapply derives_trans; [| apply H].
      simpl; apply modus_ponens_wand.
    - apply wand_sepcon_adjoint.
      rewrite sepcon_comm.
      apply wand_sepcon_adjoint.
      apply (allp_left _ (f x)).
      auto.
Qed.

Lemma frame: forall {B} g l (g' l': B -> A) F,
  g |-- l * allp (l' -* g') ->
  g * F |-- l * allp (l' -* g' * Basics.const F).
Proof.
  intros.
  apply solve with (allp (l' -* g') * F).
  + rewrite <- sepcon_assoc.
    apply sepcon_derives; auto.
  + intros x; unfold Basics.const; simpl.
    rewrite (sepcon_comm _ (l' x)), <- sepcon_assoc.
    apply sepcon_derives; [| auto].
    rewrite sepcon_comm; apply wand_sepcon_adjoint.
    apply (allp_left _ x); auto.
Qed.

Lemma split: forall {B} g1 g2 l1 l2 (g1' g2' l1' l2': B -> A),
  g1 |-- l1 * allp (l1' -* g1') ->
  g2 |-- l2 * allp (l2' -* g2') ->
  g1 * g2 |-- (l1 * l2) * allp (l1' * l2' -* g1' * g2').
Proof.
  intros.
  apply solve with (allp (l1' -* g1') * allp (l2' -* g2')).
  + rewrite (sepcon_assoc l1), <- (sepcon_assoc l2), (sepcon_comm l2), (sepcon_assoc _ l2), <- (sepcon_assoc l1).
    apply sepcon_derives; auto.
  + intros x.
    change ((l1' * l2') x) with (l1' x * l2' x).
    rewrite <- (sepcon_assoc _ (l1' x)), (sepcon_assoc _ _ (l1' x)), (sepcon_comm _ (l1' x)), <- (sepcon_assoc _ (l1' x)), (sepcon_assoc _ _ (l2' x)).
    apply sepcon_derives.
    - apply wand_sepcon_adjoint.
      apply (allp_left _ x); auto.
    - apply wand_sepcon_adjoint.
      apply (allp_left _ x).
      auto.
Qed.

End RAMIF_Q.
End RAMIF_Q.

Module RAMIF_Q'.
Section RAMIF_Q'.

Context {A : Type}.
Context {ND : NatDed A}.
Context {SL : SepLog A}.
Context {CoSL: CorableSepLog A}.

Lemma reduce: forall {B} g l p (g' l': B -> A),
  corable p ->
  g |-- l * (allp (p --> (l' -* g'))) ->
  g |-- l * (exp (p && l') -* exp (p && g')).
Proof.
  intros.
  eapply derives_trans; [exact H0 |].
  apply sepcon_derives; [auto |].
  apply wand_sepcon_adjoint.
  rewrite exp_sepcon2.
  apply exp_left; intro x; apply (exp_right x).
  apply wand_sepcon_adjoint.
  apply (allp_left _ x).
  simpl.
  apply wand_sepcon_adjoint.
  rewrite corable_sepcon_andp1 by auto.
  apply andp_right; [apply andp_left1; auto |].
  rewrite <- corable_andp_sepcon1 by auto.
  apply wand_sepcon_adjoint.
  apply modus_ponens.  
Qed.

Lemma solve: forall {B} g l p g' l' F,
  corable p ->
  g |-- l * F ->
  (forall x: B, (p x) && (F * l' x) |-- g' x) ->
  g |-- l * (allp (p --> (l' -* g'))).
Proof.
  intros.
  apply derives_trans with (l * F); auto.
  apply sepcon_derives; auto.
  apply allp_right; intro x.
  simpl.
  apply imp_andp_adjoint.
  apply wand_sepcon_adjoint.
  rewrite corable_andp_sepcon2 by auto.
  auto.
Qed.

Lemma weak_ramif_spec: forall {B} g l p (g' l': B -> A),
  g |-- l * allp (p --> l' -* g') -> g |-- l * TT.
Proof.
  intros.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; auto.
  apply TT_right.
Qed.

Lemma plain_spec: forall {B} g l p g' l' (x: B),
  corable p ->
  g |-- p x ->
  g |-- l * allp (p --> (l' -* g')) ->
  g |-- l * (l' x -* g' x).
Proof.
  intros.
  rewrite (add_andp _ _ H1).
  rewrite (add_andp _ _ H0).
  rewrite andp_assoc; apply andp_left2.
  rewrite <- corable_sepcon_andp1 by auto.
  apply sepcon_derives; [auto |].
  rewrite andp_comm; apply imp_andp_adjoint.
  apply (allp_left _ x); auto.
Qed.

Lemma trans: forall {B C} g m l pG pL g' mG' mL' l' (f: B -> C),
  corable pL ->
  corable pG ->
  (forall b, pL b && mL' b |-- pG (f b) && mG' (f b)) ->
  g |-- m * allp (pG --> (mG' -* g')) ->
  m |-- l * allp (pL --> (l' -* mL')) ->
  g |-- l * allp (pL --> (l' -* Basics.compose g' f)).
Proof.
  intros.
  apply solve with (allp (pL --> (l' -* mL')) * allp (pG --> (mG' -* g'))); auto.
  + eapply derives_trans; [exact H2 |].
    eapply derives_trans; [apply sepcon_derives; [exact H3 | apply derives_refl] |].
    rewrite sepcon_assoc; auto.
  + intro x.
    rewrite <- !corable_andp_sepcon1 by auto.
    rewrite sepcon_assoc.
    apply wand_sepcon_adjoint.
    rewrite andp_comm; apply imp_andp_adjoint.
    apply (allp_left _ x); apply imp_andp_adjoint.
    apply wand_sepcon_adjoint.
    rewrite sepcon_comm, sepcon_assoc, sepcon_comm.
    apply wand_sepcon_adjoint.
    apply derives_trans with (pG (f x) && mG' (f x)).
    - eapply derives_trans; [| apply H1].
      rewrite corable_sepcon_andp2 by auto.
      apply andp_right; [apply andp_left1; auto |].
      rewrite <- corable_sepcon_andp1 by auto.
      rewrite sepcon_comm.
      apply wand_sepcon_adjoint.
      simpl; apply modus_ponens.
    - apply wand_sepcon_adjoint.
      rewrite sepcon_comm.
      apply wand_sepcon_adjoint.
      apply (allp_left _ (f x)); simpl; unfold Basics.compose.
      apply wand_sepcon_adjoint.
      rewrite corable_sepcon_andp1, <- corable_andp_sepcon1 by auto.
      apply wand_sepcon_adjoint.
      apply modus_ponens.
Qed.

Lemma frame: forall {B} g l p g' l' F,
  (forall x: B, corable (p x)) ->
  g |-- l * allp (p --> (l' -* g')) ->
  g * F |-- l * allp (p --> (l' -* g' * Basics.const F)).
Proof.
  intros.
  apply solve with (allp (p --> (l' -* g')) * F).
  + auto.
  + rewrite <- sepcon_assoc.
    apply sepcon_derives; auto.
  + intros x; unfold Basics.const; simpl.
    rewrite <- !corable_andp_sepcon1 by auto.
    rewrite (sepcon_comm _ (l' x)), <- sepcon_assoc.
    apply sepcon_derives; [| auto].
    rewrite sepcon_comm; apply wand_sepcon_adjoint.
    rewrite andp_comm; apply imp_andp_adjoint; apply (allp_left _ x); apply imp_andp_adjoint.
    rewrite andp_comm; apply modus_ponens.
Qed.

Lemma split: forall {B} g1 g2 l1 l2 (p g1' g2' l1' l2': B -> A),
  (forall x: B, corable (p x)) ->
  g1 |-- l1 * allp (p --> (l1' -* g1')) ->
  g2 |-- l2 * allp (p --> (l2' -* g2')) ->
  g1 * g2 |-- (l1 * l2) * allp (p --> (l1' * l2' -* g1' * g2')).
Proof.
  intros.
  apply solve with (allp (p --> (l1' -* g1')) * allp (p --> (l2' -* g2'))).
  + auto.
  + rewrite (sepcon_assoc l1), <- (sepcon_assoc l2), (sepcon_comm l2), (sepcon_assoc _ l2), <- (sepcon_assoc l1).
    apply sepcon_derives; auto.
  + intros x.
    change ((l1' * l2') x) with (l1' x * l2' x).
    rewrite <- (sepcon_assoc _ (l1' x)), (sepcon_assoc _ _ (l1' x)), (sepcon_comm _ (l1' x)), <- (sepcon_assoc _ (l1' x)), (sepcon_assoc _ _ (l2' x)).
    rewrite <- (andp_dup (p x)), andp_assoc.
    rewrite <- corable_sepcon_andp1, <- corable_andp_sepcon1 by auto.
    rewrite <- !corable_sepcon_andp1 by auto.
    apply sepcon_derives.
    - apply wand_sepcon_adjoint.
      apply (allp_left _ x).
      apply wand_sepcon_adjoint.
      rewrite corable_sepcon_andp1, <- corable_andp_sepcon1 by auto.
      (eapply derives_trans; [apply sepcon_derives; [simpl; intros; apply modus_ponens | apply derives_refl] |]).
      apply wand_sepcon_adjoint; apply derives_refl.
    - apply wand_sepcon_adjoint.
      apply (allp_left _ x).
      apply wand_sepcon_adjoint.
      rewrite corable_sepcon_andp1, <- corable_andp_sepcon1 by auto.
      (eapply derives_trans; [apply sepcon_derives; [simpl; intros; apply modus_ponens | apply derives_refl] |]).
      apply wand_sepcon_adjoint; apply derives_refl.
Qed.

End RAMIF_Q'.
End RAMIF_Q'.

