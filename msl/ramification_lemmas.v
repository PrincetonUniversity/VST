(* This file is developed by Qinxiang Cao, Shengyi Wang and Aquinas Hobor in  *)
(* 2015 summer in Yale-NUS.                                                   *)
(* The spec and proof of ramify_frame and ramify_split is based on "The       *)
(* Ramifications of Sharing in Data Structures" by Aquinas Hobor and Jules    *)
(* Villard. Other lemmas are found useful during the research in that summer. *)

Require Import msl.base.
Require Import msl.simple_CCC.
Require Import msl.seplog.
Require Import msl.log_normalize.

Local Open Scope logic.

Section Ramification.

Context {A : Type}.
Context {ND : NatDed A}.
Context {SL : SepLog A}.
Context {CoSL: CorableSepLog A}.

Lemma solve_ramify: forall g l g' l' F, g |-- l * F -> F * l' |-- g' -> g |-- l * (l' -* g').
Proof.
  intros.
  apply derives_trans with (l * F); auto.
  apply sepcon_derives; auto.
  apply wand_sepcon_adjoint.
  auto.
Qed.

Lemma ramify_trans: forall g m l g' m' l', g |-- m * (m' -* g') -> m |-- l * (l' -* m') -> g |-- l * (l' -* g').
Proof.
  intros.
  apply solve_ramify with ((l' -* m') * (m' -* g')).
  + eapply derives_trans; [exact H |].
    eapply derives_trans; [apply sepcon_derives; [exact H0 | apply derives_refl] |].
    rewrite sepcon_assoc; auto.
  + rewrite (sepcon_comm _ l'), <- sepcon_assoc.
    eapply derives_trans; [| apply modus_ponens_wand].
    apply sepcon_derives; [| apply derives_refl].
    apply modus_ponens_wand.
Qed.

Lemma self_ramify_spec: forall g l, g |-- l * (l -* g) -> g |-- l * TT.
Proof.
  intros.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; auto.
  apply TT_right.
Qed.

Lemma ramify_frame: forall g l g' l' F, g |-- l * (l' -* g') -> g * F |-- l * (l' -* g' * F).
Proof.
  intros.
  apply solve_ramify with ((l' -* g') * F).
  + rewrite <- sepcon_assoc.
    apply sepcon_derives; auto.
  + rewrite (sepcon_comm _ l'), <- sepcon_assoc.
    apply sepcon_derives; [apply modus_ponens_wand | auto].
Qed.

Lemma split_ramify: forall g1 g2 l1 l2 g1' g2' l1' l2',
  g1 |-- l1 * (l1' -* g1') ->
  g2 |-- l2 * (l2' -* g2') ->
  g1 * g2 |-- (l1 * l2) * (l1' * l2' -* g1' * g2').
Proof.
  intros.
  apply solve_ramify with ((l1' -* g1') * (l2' -* g2')).
  + rewrite (sepcon_assoc l1), <- (sepcon_assoc l2), (sepcon_comm l2), (sepcon_assoc _ l2), <- (sepcon_assoc l1).
    apply sepcon_derives; auto.
  + eapply derives_trans; [apply sepcon_derives; [apply wand_sepcon_wand | apply derives_refl] |].
    rewrite sepcon_comm; apply modus_ponens_wand.
Qed.

End Ramification.
