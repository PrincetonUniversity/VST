Require Import compcert.common.Memory.
Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.ageable.
Require Import VST.msl.age_to.
Require Import VST.veric.coqlib4.
Require Import VST.veric.compcert_rmaps.

Set Bullet Behavior "Strict Subproofs".

Lemma pred_hered {A} {_ : ageable A} (P : pred A) : hereditary age (app_pred P).
Proof.
  destruct P; auto.
Qed.

Lemma hereditary_necR {phi phi' : rmap} {P} :
  necR phi phi' ->
  hereditary age P ->
  P phi -> P phi'.
Proof.
  intros N H; induction N; auto.
  apply H; auto.
Qed.

Lemma anti_hereditary_necR {phi phi' : rmap} {P} :
  necR phi phi' ->
  hereditary (fun x y => age y x) P ->
  P phi' -> P phi.
Proof.
  intros N H; induction N; auto.
  apply H; auto.
Qed.

Lemma app_pred_age {R} {phi phi' : rmap} :
  age phi phi' ->
  app_pred R phi ->
  app_pred R phi'.
Proof.
  destruct R as [R HR]; simpl.
  apply HR.
Qed.

Lemma age_yes_sat {Phi Phi' phi phi' l z z' sh sh'} (R : pred rmap) :
  level Phi = level phi ->
  age Phi Phi' ->
  age phi phi' ->
  app_pred R phi ->
  Phi  @ l = YES sh sh' (LK z z') (SomeP rmaps.Mpred (fun _ => R)) ->
  app_pred (approx (S (level phi')) R) phi' /\
  Phi' @ l = YES sh sh' (LK z z') (SomeP rmaps.Mpred (fun _ => approx (level Phi') R)).
Proof.
  intros L A Au SAT AT.
  pose proof (app_pred_age Au SAT) as SAT'.
  split.
  - split.
    + apply age_level in A; apply age_level in Au. omega.
    + apply SAT'.
  - apply (necR_YES _ Phi') in AT.
    + rewrite AT.
      reflexivity.
    + constructor. assumption.
Qed.

Lemma age_resource_at {phi phi' loc} :
  age phi phi' ->
  phi' @ loc = resource_fmap (approx (level phi')) (approx (level phi')) (phi @ loc).
Proof.
  intros A.
  rewrite <- (age1_resource_at _ _ A loc (phi @ loc)).
  - reflexivity.
  - rewrite resource_at_approx. reflexivity.
Qed.

Lemma age_to_resource_at phi n loc : age_to n phi @ loc = resource_fmap (approx n) (approx n) (phi @ loc).
Proof.
  assert (D : (n <= level phi \/ n >= level phi)%nat) by omega.
  destruct D as [D | D]; swap 1 2.
  - rewrite age_to_ge; auto.
    rewrite <-resource_at_approx.
    match goal with
      |- _ = ?map ?f1 ?f2 (?map ?g1 ?g2 ?r) => transitivity (map (f1 oo g1) (g2 oo f2) r)
    end; swap 1 2.
    + destruct (phi @ loc); unfold "oo"; simpl; auto.
      * destruct p; auto.
        rewrite preds_fmap_fmap; auto.
      * destruct p; auto.
        rewrite preds_fmap_fmap; auto.
    + f_equal. rewrite approx'_oo_approx; auto.
      rewrite approx_oo_approx'; auto.
  - generalize (age_to_ageN n phi).
    generalize (age_to n phi); intros phi'.
    replace n with (level phi - (level phi - n))%nat at 2 3 by omega.
    generalize (level phi - n)%nat; intros k. clear n D.
    revert phi phi'; induction k; intros phi phi'.
    + unfold ageN in *; simpl.
      injection 1 as <-.
      simpl; replace (level phi - 0)%nat with (level phi) by omega.
      symmetry.
      apply resource_at_approx.
    + change (ageN (S k) phi) with
      (match age1 phi with Some w' => ageN k w' | None => None end).
      destruct (age1 phi) as [o|] eqn:Eo. 2:congruence.
      intros A; specialize (IHk _ _ A).
      rewrite IHk.
      pose proof age_resource_at Eo (loc := loc) as R.
      rewrite R.
      clear A R.
      rewrite (age_level _ _ Eo).
      simpl.
      match goal with
        |- ?map ?f1 ?f2 (?map ?g1 ?g2 ?r) = _ => transitivity (map (f1 oo g1) (g2 oo f2) r)
      end.
      * destruct (phi @ loc); unfold "oo"; simpl; auto.
        -- destruct p; auto.
           rewrite preds_fmap_fmap; auto.
        -- destruct p; auto.
           rewrite preds_fmap_fmap; auto.
      * f_equal. rewrite approx_oo_approx'; auto.
        omega.
        rewrite approx'_oo_approx; auto.
        omega.
Qed.

Lemma age_to_ghost_of phi n : ghost_of (age_to n phi) = ghost_fmap (approx n) (approx n) (ghost_of phi).
Proof.
  pose proof (age_to_ageN n phi).
  forget (age_to n phi) as phi'.
  remember (level phi - n) as n'.
  revert dependent n; revert dependent phi; induction n'; intros.
  - inv H.
    rewrite <- ghost_of_approx, ghost_fmap_fmap, approx'_oo_approx, approx_oo_approx' by omega; auto.
  - change (ageN (S n') phi) with
      (match age1 phi with Some w' => ageN n' w' | None => None end) in H.
    destruct (age1 phi) eqn: Hage; [|discriminate].
    pose proof (age_level _ _ Hage) as Hl.
    assert (n' = level r - n).
    { rewrite Hl, <- minus_Sn_m in Heqn' by omega; inversion Heqn'; auto. }
    rewrite (IHn' _ H n), (age1_ghost_of _ _ Hage) by (auto; omega).
    rewrite ghost_fmap_fmap, approx_oo_approx', approx'_oo_approx by omega; auto.
Qed.
