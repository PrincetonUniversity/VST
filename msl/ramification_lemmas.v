(* The spec and proof of the following rules are based on `The Ramifications  *)
(* of Sharing in Data Structures' by Aquinas Hobor and Jules Villard.         *)
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
(*    RAMIF_PLAIN.exp_right                                                   *)
(*    RAMIF_Q.trans                                                           *)
(*    RAMIF_Q.simple_trans                                                    *)
(*    RAMIF_Q.weak_ramif_spec                                                 *)
(*    RAMIF_Q.plain_spec                                                      *)
(*    RAMIF_Q.exp_right                                                       *)

Require Import VST.msl.base.
Require Import VST.msl.Coqlib2.
Require Import VST.msl.simple_CCC.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.

Local Open Scope logic.

Lemma modus_ponens_wand' {A}{ND: NatDed A}{SL: SepLog A}:
                      forall P P' Q: A, P |-- P' ->  derives (sepcon P (wand P' Q)) Q.
Proof.
intros.
   eapply derives_trans; [apply sepcon_derives; [ | apply derives_refl] | apply modus_ponens_wand ].
  auto.
Qed.

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

Lemma trans: forall g m l g' m' l',
      g |-- m * (m' -* g') ->
      m |-- l * (l' -* m') ->
      g |-- l * (l' -* g').
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

Lemma trans':
   forall (m l g' m' l': A),
       m |-- l * (l' -* m') ->
       m * (m' -* g') |-- l * (l' -* g').
Proof.
  intros. eapply trans. apply derives_refl. auto.
Qed.

Lemma trans'':
   forall (p g' m' l': A),
       p |-- l' -* m' ->
       p * (m' -* g') |-- (l' -* g').
Proof.
  intros.
  rewrite -> wand_sepcon_adjoint.
  eapply derives_trans; [apply H | ]. clear H.
  rewrite <- wand_sepcon_adjoint.
  rewrite <- wand_sepcon_adjoint.
  pull_left l'. apply modus_ponens_wand'. apply modus_ponens_wand.
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

(* Using split to prove frame will lead to a simpler proof. *)
(* But it requires a unitary separation logic.              *)
Lemma frame: forall g l g' l' F, g |-- l * (l' -* g') -> g * F |-- l * (l' -* g' * F).
Proof.
  intros.
  apply solve with ((l' -* g') * F).
  + rewrite <- sepcon_assoc.
    apply sepcon_derives; auto.
  + rewrite (sepcon_comm _ l'), <- sepcon_assoc.
    apply sepcon_derives; [apply modus_ponens_wand | auto].
Qed.

Lemma frame_post: forall g l g' l' F, g |-- l * (l' -* g') -> g |-- l * (l' * F -* g' * F).
Proof.
  intros.
  apply solve with (l' -* g').
  + auto.
  + rewrite <- sepcon_assoc.
    apply sepcon_derives; [rewrite sepcon_comm; apply modus_ponens_wand | auto].
Qed.

Lemma frame_pre: forall g l g' l' F, g |-- l * (l' -* g') -> g * F |-- (l * F) * (l' -* g').
Proof.
  intros.
  apply solve with (l' -* g').
  + rewrite (sepcon_comm l F), sepcon_assoc, (sepcon_comm F).
    apply sepcon_derives; auto.
  + rewrite sepcon_comm; apply modus_ponens_wand.
Qed.

Lemma exp_right: forall {T} (a: T) g l g' l',
  g |-- l * (l' -* g' a) ->
  g |-- l * (l' -* exp g').
Proof.
  intros.
  apply solve with (l' -* g' a); auto.
  apply wand_sepcon_adjoint.
  apply wand_derives; auto.
  apply (exp_right a); auto.
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
  apply derives_refl.
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
  apply (allp_left _ x). apply derives_refl.
Qed.

Lemma trans: forall {B BG BL} g m l g' mG' mL' l' (fG: B -> BG) (fL: B -> BL),
  (forall b, mL' (fL b) |-- mG' (fG b)) ->
  g |-- m * allp (mG' -* g') ->
  m |-- l * allp (l' -* mL') ->
  g |-- l * allp (Basics.compose l' fL -* Basics.compose g' fG).
Proof.
  intros.
  apply solve with (allp (l' -* mL') * allp (mG' -* g')); auto.
  + eapply derives_trans; [exact H0 |].
    eapply derives_trans; [apply sepcon_derives; [exact H1 | apply derives_refl] |].
    rewrite sepcon_assoc; auto.
  + intro b.
    rewrite sepcon_assoc.
    apply wand_sepcon_adjoint.
    apply (allp_left _ (fL b)).
    apply wand_sepcon_adjoint.
    rewrite sepcon_comm, sepcon_assoc, sepcon_comm.
    apply wand_sepcon_adjoint.
    apply derives_trans with (mG' (fG b)).
    - eapply derives_trans; [| apply H].
      simpl; apply modus_ponens_wand.
    - apply wand_sepcon_adjoint.
      rewrite sepcon_comm.
      apply wand_sepcon_adjoint.
      apply (allp_left _ (fG b)).
      apply derives_refl.
Qed.

Lemma simple_trans: forall {B} g m l (g' m' l': B -> A),
  g |-- m * allp (m' -* g') ->
  m |-- l * allp (l' -* m') ->
  g |-- l * allp (l' -* g').
Proof.
  intros.
  eapply trans with (mL' := m') (mG' := m') (fL := id B) (fG := id B); eauto.
Qed.

Lemma trans'':
  forall {CS: ClassicalSep A}
     {B C: Type} (f: B->C) p l m g1 g2,
     g2 = g1 oo f ->
     p |-- allp (l -* m oo f) ->
     p * allp (m -* g1) |-- allp (l -* g2).
Proof.
   intros.
   subst g2.
   apply allp_right; intro x.
   simpl. rewrite <- wand_sepcon_adjoint.
   rewrite sepcon_assoc.
   eapply derives_trans; [apply sepcon_derives; [apply H0 | apply derives_refl] | ].
    rewrite -> wand_sepcon_adjoint.
  apply allp_left with x.
   rewrite <- wand_sepcon_adjoint.
   simpl.
   rewrite <- !sepcon_assoc.
   pull_left (l x).
   eapply derives_trans; [apply sepcon_derives; [ | apply derives_refl] | ].
   apply modus_ponens_wand.
   rewrite sepcon_comm.
   rewrite -> wand_sepcon_adjoint.
   apply allp_left with (f x). apply derives_refl.
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
      apply (allp_left _ x); apply derives_refl.
    - apply wand_sepcon_adjoint.
      apply (allp_left _ x).
      apply derives_refl.
Qed.

(* Using split to prove frame will lead to a simpler proof. *)
(* But it requires a unitary separation logic.              *)
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

Lemma frame_post: forall {B} g l (g' l' F: B -> A),
  g |-- l * allp (l' -* g') ->
  g |-- l * allp (l' * F -* g' * F).
Proof.
  intros.
  apply solve with (allp (l' -* g')).
  + auto.
  + intros x; simpl.
    rewrite <- sepcon_assoc.
    apply sepcon_derives; [rewrite sepcon_comm | auto].
    rewrite sepcon_comm; apply wand_sepcon_adjoint.
    apply (allp_left _ x); auto.
Qed.

Lemma frame_pre: forall {B} g l (g' l': B -> A) F,
  g |-- l * allp (l' -* g') ->
  g * F |-- (l * F) * allp (l' -* g').
Proof.
  intros.
  apply solve with (allp (l' -* g')).
  + rewrite (sepcon_comm l F), sepcon_assoc, (sepcon_comm F).
    apply sepcon_derives; auto.
  + intros x.
    apply wand_sepcon_adjoint.
    apply (allp_left _ x); apply derives_refl.
Qed.

Lemma exp_right: forall {T B} (a: B -> T) g l (g': T -> B -> A) (l': B -> A),
  g |-- l * allp (l' -* (fun b => g' (a b) b)) ->
  g |-- l * allp (l' -* exp g').
Proof.
  intros.
  apply solve with (allp (l' -* (fun b => g' (a b) b))); auto.
  intros.
  apply wand_sepcon_adjoint.
  apply (allp_left _ x).
  simpl.
  apply wand_derives; auto.
  apply (exp_right (a x)); auto.
Qed.

End RAMIF_Q.

Ltac formalize :=
  match goal with
  | |- @derives ?Pred _ ?g (?l * @allp ?Pred _ ?T ?Func) =>
      let g' := fresh "g'" in evar (g': T -> Pred);
      let l' := fresh "l'" in evar (l': T -> Pred);
      let x := fresh "x" in
      let H := fresh "H" in
      assert (Func = l' -* g') as H;
      [
        extensionality x; cbv beta;
        match goal with
        | |- ?L' -* exp ?G' = _ =>
             super_pattern L' x; super_pattern_in_func G' x
        | |- ?L' -* ?G' = _ =>
             super_pattern L' x; super_pattern G' x
        end;
        match goal with
        | |- ?L' _ -* exp (fun a => ?G' a _) = _ =>
             instantiate (1 := L') in (Value of l');
             instantiate (1 := exp G') in (Value of g')
        | |- ?L' _ -* ?G' _ = _ =>
             instantiate (1 := L') in (Value of l');
             instantiate (1 := G') in (Value of g')
        end;
        subst g' l';
        reflexivity
      | subst g' l'; rewrite H; clear H]
  end.

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
  apply (allp_left _ x); apply derives_refl.
Qed.

Lemma trans: forall {B BG BL} g m l p pG pL g' mG' mL' l' (fG: B -> BG) (fL: B -> BL),
  corable p ->
  corable pL ->
  corable pG ->
  g |-- m * allp (pG --> (mG' -* g')) ->
  m |-- l * allp (pL --> (l' -* mL')) ->
  (forall b, p b |-- pL (fL b)) ->
  (forall b, p b && mL' (fL b) |-- pG (fG b) && mG' (fG b)) ->
  g |-- l * allp (p --> (Basics.compose l' fL -* Basics.compose g' fG)).
Proof.
  intros.
  apply solve with (allp (pL --> (l' -* mL')) * allp (pG --> (mG' -* g'))).
  + simpl; unfold Basics.compose.
    auto.
  + eapply derives_trans; [exact H2 |].
    eapply derives_trans; [apply sepcon_derives; [exact H3 | apply derives_refl] |].
    rewrite sepcon_assoc; auto.
  + intro b.
    unfold Basics.compose.
    rewrite <- !corable_andp_sepcon1 by auto.
    rewrite sepcon_assoc.
    apply wand_sepcon_adjoint.
    rewrite andp_comm; apply imp_andp_adjoint.
    apply (allp_left _ (fL b)); apply imp_andp_adjoint.
    apply wand_sepcon_adjoint.
    rewrite sepcon_comm, sepcon_assoc, sepcon_comm.
    apply wand_sepcon_adjoint.
    apply derives_trans with (pG (fG b) && mG' (fG b)).
    - apply derives_trans with (p b && mL' (fL b)); [| apply H5].
      rewrite corable_sepcon_andp2 by auto.
      apply andp_right; [apply andp_left1; auto |].
      rewrite <- corable_sepcon_andp1 by auto.
      rewrite sepcon_comm.
      apply wand_sepcon_adjoint.
      simpl; eapply derives_trans; [| apply modus_ponens].
      apply andp_derives; [apply H4 | apply derives_refl].
    - apply wand_sepcon_adjoint.
      rewrite sepcon_comm.
      apply wand_sepcon_adjoint.
      apply (allp_left _ (fG b)); simpl.
      apply wand_sepcon_adjoint.
      rewrite corable_sepcon_andp1, <- corable_andp_sepcon1 by auto.
      apply wand_sepcon_adjoint.
      apply modus_ponens.
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

(* Using split to prove frame will lead to a simpler proof. *)
(* But it requires a unitary separation logic.              *)
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

Lemma frame_post: forall {B} g l (p g' l' F: B -> A),
  (forall x: B, corable (p x)) ->
  g |-- l * allp (p --> (l' -* g')) ->
  g |-- l * allp (p --> (l' * F -* g' * F)).
Proof.
  intros.
  apply solve with (allp (p --> (l' -* g'))).
  + auto.
  + auto.
  + intros x; simpl.
    rewrite <- !corable_andp_sepcon1 by auto.
    rewrite <- sepcon_assoc.
    apply sepcon_derives; [rewrite sepcon_comm | auto].
    rewrite sepcon_comm; apply wand_sepcon_adjoint.
    rewrite andp_comm; apply imp_andp_adjoint; apply (allp_left _ x); apply imp_andp_adjoint.
    rewrite andp_comm; apply modus_ponens.
Qed.

Lemma frame_pre: forall {B} g l (p g' l': B -> A) F,
  (forall x: B, corable (p x)) ->
  g |-- l * allp (p --> (l' -* g')) ->
  g * F |-- (l * F) * allp (p --> (l' -* g')).
Proof.
  intros.
  apply solve with (allp (p --> (l' -* g'))).
  + auto.
  + rewrite (sepcon_comm l F), sepcon_assoc, (sepcon_comm F).
    apply sepcon_derives; auto.
  + intros x; simpl.
    rewrite <- !corable_andp_sepcon1 by auto.
    apply wand_sepcon_adjoint.
    rewrite andp_comm; apply imp_andp_adjoint; apply (allp_left _ x); apply imp_andp_adjoint.
    rewrite andp_comm; apply modus_ponens.
Qed.

Lemma exp_right: forall {T B} (a: B -> T) p g l (g': T -> B -> A) (l': B -> A),
  corable p ->
  g |-- l * allp (p --> (l' -* (fun b => g' (a b) b))) ->
  g |-- l * allp (p --> (l' -* exp g')).
Proof.
  intros.
  apply solve with (allp (p --> (l' -* (fun b => g' (a b) b)))); auto.
  intros.
  rewrite <- corable_sepcon_andp1 by auto.
  apply wand_sepcon_adjoint.
  apply (allp_left _ x).
  simpl.
  apply wand_sepcon_adjoint.
  rewrite corable_sepcon_andp1 by auto.
  rewrite <- corable_andp_sepcon1 by auto.
  eapply derives_trans; [apply sepcon_derives; [apply modus_ponens | apply derives_refl] |].
  apply wand_sepcon_adjoint.
  apply wand_derives; auto.
  apply (exp_right (a x)); auto.
Qed.

End RAMIF_Q'.

Ltac formalize :=
  match goal with
  | |- @derives ?Pred _ ?g (?l * @allp ?Pred _ ?T ?Func) =>
      let p := fresh "p" in evar (p: T -> Pred);
      let g' := fresh "g'" in evar (g': T -> Pred);
      let l' := fresh "l'" in evar (l': T -> Pred);
      let x := fresh "x" in
      let H := fresh "H" in
      assert (Func = p --> (l' -* g'));
      [
        extensionality x; cbv beta;
        match goal with
        | |- ?P --> (?L' -* exp ?G') = _ =>
             super_pattern P x; super_pattern L' x; super_pattern_in_func G' x
        | |- ?P --> (?L' -* ?G') = _ =>
             super_pattern P x; super_pattern L' x; super_pattern G' x
        end;
        match goal with
        | |- ?P _ --> (?L' _ -* exp (fun a => ?G' a _)) = _ =>
             instantiate (1 := P) in (Value of p);
             instantiate (1 := L') in (Value of l');
             instantiate (1 := exp G') in (Value of g')
        | |- ?P _ --> (?L' _ -* ?G' _) = _ =>
             instantiate (1 := P) in (Value of p);
             instantiate (1 := L') in (Value of l');
             instantiate (1 := G') in (Value of g')
        end;
        subst p g' l';
        reflexivity
      | subst p g' l'; rewrite H; clear H]
  end.

End RAMIF_Q'.
