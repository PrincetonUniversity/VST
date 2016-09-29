Require Import msl.msl_standard.
Require Import msl.cjoins.
Require Import msl.Coqlib2.
Require Import msl.sepalg_list.
Require Import veric.rmaps.

Import MixVariantFunctor.
Import MixVariantFunctorLemmas.
Import MixVariantFunctorGenerator.

Module Rmaps_Lemmas (R: RMAPS).
Module R := R. 
Import R.

Hint Resolve (@subp_sepcon _ Join_rmap Perm_rmap Sep_rmap): contractive.

 Lemma approx_p  : forall (p:pred rmap) n w, approx n p w -> p w.
 Proof. unfold approx; simpl; intuition. Qed.

 Lemma approx_lt : forall (p:pred rmap) n w, lt (level w) n -> p w -> approx n p w.
 Proof. unfold approx; simpl; intuition. Qed.

 Lemma approx_ge : forall p n w, ge (level w) n -> approx n p w -> False.
 Proof. unfold approx; intros. destruct H0; auto. omega. Qed.

  Lemma ageN_level : forall n (phi1 phi2 : rmap),
    ageN n phi1 = Some phi2 -> level phi1 = (n + (level phi2))%nat.
  Proof.
    unfold ageN; induction n; simpl; intros.
    injection H; intros; subst; auto.
    revert H.
    repeat rewrite rmap_level_eq in *.
    intros. invSome.
    specialize (IHn _ _ H2).
    apply  age_level in H.  rewrite rmap_level_eq in *. omega. 
  Qed.

Lemma NO_identity: identity (NO Share.bot).
Proof.
  unfold identity; intros.
  inv H; f_equal;   apply join_unit1_e in RJ; auto.
Qed.

Lemma PURE_identity: forall k pds, identity (PURE k pds).
Proof.
  unfold identity; intros.
  inv H; auto.
Qed.

Lemma identity_NO:
  forall r, identity  r -> r = NO Share.bot \/ exists k, exists pds, r = PURE k pds.
Proof.
  destruct r; auto; intros.
  apply identity_unit_equiv in H. inv H.
  apply identity_unit_equiv in RJ. apply identity_share_bot in RJ. subst. auto.
  apply identity_unit_equiv in H. inv H.
  apply pshare_nonunit in H1. contradiction.
  right. exists k. exists p. trivial.
Qed.

Lemma age1_resource_at_identity:
  forall phi phi' loc, age1 phi = Some phi' -> 
               (identity (phi@loc) <-> identity (phi'@loc)).
Proof.
 split; intro.
 (* FORWARD DIRECTION *)
  generalize (identity_NO _ H0); clear H0; intro.
  unfold resource_at in *.
  rewrite rmap_age1_eq in *. 
  revert H H0; case_eq (unsquash phi); simpl; intros.
  destruct n; inv H0.
  rewrite unsquash_squash.
  simpl.
  destruct r. simpl in *.
  unfold compose; simpl. destruct H1 as [H1 | [k [pds H1]]]; rewrite H1; simpl; auto.
  apply NO_identity.
  apply PURE_identity.
 (* BACKWARD DIRECTION *)
  generalize (identity_NO _ H0); clear H0; intro.
  unfold resource_at in *. simpl in H.
  rewrite rmap_age1_eq in H.
  revert H H0; case_eq (unsquash phi); simpl; intros.
  destruct n; inv H0.
  rewrite unsquash_squash in H1. destruct r. simpl in *.
  unfold compose in H1; simpl in H1. 
  unfold resource_fmap in H1.
  destruct (x loc).
  destruct H1. inv H0;   apply NO_identity. destruct H0 as [? [? H0]]; inv H0.
  destruct H1 as [H1 | [k' [pds' H1]]]; inv H1.
  apply PURE_identity.
Qed.

Lemma necR_resource_at_identity:
  forall phi phi' loc, necR phi phi' -> 
         identity (phi@loc) ->
         identity (phi'@loc).
Proof.
  induction 1; auto.
  intro.
 apply -> (age1_resource_at_identity _ _ loc H); auto.
Qed.

Lemma make_rmap': forall f, AV.valid (fun l => res_option (f l)) -> 
          exists phi: rmap', proj1_sig phi = f.
Proof.
  intros.
  unfold rmap'.
  exists (exist valid f H).
  auto.
Qed.


Lemma make_rmap (f: AV.address -> resource) (V: AV.valid (res_option oo f)) 
    (n: nat) (H: resource_fmap (approx n) (approx n) oo f = f) :
  {phi: rmap | level phi = n /\ resource_at phi = f}.
Proof.
intros.
apply (exist _ (squash (n, @exist (AV.address -> resource) R.valid f V))).
simpl level; rewrite rmap_level_eq in *; unfold resource_at. rewrite unsquash_squash.
simpl; auto.
Qed.

Lemma make_rmap'':
    forall n (f: AV.address -> resource) ,
      AV.valid (fun l => res_option (f l)) ->
      exists phi:rmap, level phi = n /\ resource_at phi = resource_fmap (approx n) (approx n) oo f.
  Proof.
    intros.
    exists (squash (n, exist valid f H)).
    rewrite rmap_level_eq.
      unfold resource_at; rewrite unsquash_squash; simpl; split; auto.
Qed.

Lemma approx_oo_approx':
  forall n n', (n' >= n)%nat -> approx n oo approx n' = approx n.
Proof.
unfold compose; intros.
extensionality P.
 apply pred_ext; intros w ?; unfold approx; simpl in *; intuition.
Qed.

Lemma approx'_oo_approx:
  forall n n', (n' >= n)%nat -> approx n' oo approx n = approx n.
Proof.
unfold compose; intros.
extensionality P.
 apply pred_ext; intros w ?; unfold approx; simpl in *; intuition.
Qed.

Lemma approx_oo_approx: forall n, approx n oo approx n = approx n.
Proof.
intros; apply approx_oo_approx'; omega.
Qed.

Lemma resources_same_level:
   forall f phi,
     (forall l : AV.address, join_sub (f l) (phi @ l)) ->
        resource_fmap (approx (level phi)) (approx (level phi)) oo f = f.
Proof.
  intros.
  rewrite rmap_level_eq.
  unfold resource_fmap, resource_at in *.
  unfold compose; extensionality l. spec H l.
  destruct H as [g ?].
  revert H; case_eq (unsquash phi); intros n ? ?.
  generalize H; rewrite <- (squash_unsquash phi).
  rewrite H. rewrite unsquash_squash.
  simpl; intros. 
  injection H0. clear H0. intro.
  clear phi H.
  rewrite <- H0 in H1.
  clear H0.
  unfold rmap_fmap in *.
  destruct r.
  simpl in *.
  revert H1.
  unfold resource_fmap, compose.
  destruct (f l); destruct g; destruct (x l); simpl; intro; auto; inv H1.
  change (preds_fmap (approx n) (approx n) (preds_fmap (approx n) (approx n) p2))
  with ((preds_fmap (approx n) (approx n) oo preds_fmap (approx n) (approx n)) p2).
  rewrite preds_fmap_comp.
  rewrite approx_oo_approx; auto.
  change (preds_fmap (approx n) (approx n) (preds_fmap (approx n) (approx n) p4))
  with ((preds_fmap (approx n) (approx n) oo preds_fmap (approx n) (approx n)) p4).
  rewrite preds_fmap_comp.
  rewrite approx_oo_approx; auto.
  change (preds_fmap (approx n) (approx n) (preds_fmap (approx n) (approx n) p1))
  with ((preds_fmap (approx n) (approx n) oo preds_fmap (approx n) (approx n)) p1).
  rewrite preds_fmap_comp.
  rewrite approx_oo_approx; auto.
Qed.

Lemma deallocate: 
  forall (phi: rmap) (f g : AV.address -> resource),
  AV.valid (res_option oo f) -> AV.valid (res_option oo g) ->
  (forall l, join  (f l) (g l) (phi@l)) ->
   exists phi1, exists phi2, 
     join phi1 phi2 phi /\ resource_at phi1 = f.
Proof.
  intros until g. intros Hf Hg H0.
  generalize (resources_same_level f phi); intro.
  spec H. intro; econstructor; apply H0.
  generalize (resources_same_level g phi); intro.
  spec H1.
  intro. econstructor; eapply join_comm; eauto.
  generalize (make_rmap'' (level phi) f Hf); intros [phif [? Gf]].
  generalize (make_rmap'' (level phi) g Hg); intros [phig [? Gg]].
  exists phif; exists phig.
  split.
  rewrite rmap_level_eq in *.
  unfold resource_at in *.
  revert H0 H Gf H1 Gg H2 H3; 
  case_eq (unsquash phif); intros nf phif' ?.
  case_eq (unsquash phig); intros ng phig' ?.
  case_eq (unsquash phi); intros n phi' ?.
  simpl.
  intros; subst nf ng.
  rewrite join_unsquash.
  rewrite H; rewrite H0; rewrite H1.
  rewrite <- H1.
  revert H1; case_eq (unsquash phi); intros n' phi'' ?.
  intros.
  inversion H5.
  simpl. 
  split. 
  simpl; constructor; auto.
  subst n' phi''. 
  intro l; spec H2 l.
  simpl.
  rewrite Gf; rewrite Gg; clear Gf Gg.
  rewrite H3; rewrite H4.
  auto.
  rewrite Gf.
  auto.
Qed.

Lemma allocate:
     forall (phi : rmap) (f : AV.address -> resource),
     AV.valid (res_option oo f) ->
        resource_fmap (approx (level phi)) (approx (level phi)) oo f = f ->
       (forall l, {r' | join (phi@l) (f l) r'}) ->
       exists phi1 : rmap,
         exists phi2 : rmap,
           join phi phi1 phi2 /\ resource_at phi1 = f.
Proof.
 intros. rename X into H1.
 generalize (make_rmap'' (level phi) f H); intros [phif [? Gf]].
 pose (g loc := proj1_sig (H1 loc)).
 assert (H3: forall l, join (phi @ l) (f l) (g l))
   by (unfold g; intro; destruct (H1 l); simpl in *; auto).
 clearbody g.
 generalize (make_rmap'' (level phi) g); intro.
 spec H4.
   assert (AV.valid (fun l => res_option (phi @ l))).
     clear.
     unfold resource_at.
     case_eq (unsquash phi); intros.
     simpl.
     destruct r. simpl.
     apply v.
   eapply AV.valid_join. 2: apply H5. 2: apply H.
   clear - H3.
    unfold compose.
   intro l; spec H3 l.
   destruct (phi @ l); simpl in *.
   inv H3; constructor; auto.
   inv H3; constructor; auto.
   constructor; auto.
   inv H3; constructor; auto.
 destruct H4 as [phig [? ?]].
 exists phif; exists phig.
 split.
 2: congruence.
 rewrite join_unsquash.
 unfold resource_at in *.
 rewrite rmap_level_eq in *.
 revert H0 H1 H2 H3 H4 H5 Gf.
 case_eq (unsquash phif); intros nf phif' ?.
 case_eq (unsquash phig); intros ng phig' ?.
 case_eq (unsquash phi); intros n phi' ?.
 simpl.
 intros; subst nf ng.
 split. split; trivial.
 simpl.
 intro l.
 spec H6 l.
 assert (proj1_sig phig' l = g l).
   generalize (f_equal squash H2); intro.
   rewrite squash_unsquash in H5. 
   subst phi.
   rewrite unsquash_squash in H2.
   injection H2; clear H2; intro.
   rewrite <- H2 in H6.
   rewrite <- H3 in H6.
   rewrite H8.
   clear - H6.
   revert H6.
   unfold rmap_fmap, compose, resource_fmap.
   destruct phi'; simpl.
   destruct (x l); destruct (f l); destruct (g l); simpl; intros; auto; try inv H6;
              try change (preds_fmap (approx n) (approx n) (preds_fmap (approx n) (approx n) p0)) with
                ((preds_fmap (approx n) (approx n) oo preds_fmap (approx n) (approx n)) p0);
              try change (preds_fmap (approx n) (approx n) (preds_fmap (approx n) (approx n) p)) with
                ((preds_fmap (approx n) (approx n) oo preds_fmap (approx n) (approx n)) p);
                rewrite preds_fmap_comp; rewrite approx_oo_approx; auto.
 rewrite H5.
 rewrite Gf.
 rewrite H3.
 auto.
Qed.

  Lemma unsquash_inj : forall x y,
      unsquash x = unsquash y -> x = y.
  Proof.
    intros.
    rewrite <- (squash_unsquash x).
    rewrite <- (squash_unsquash y).
    rewrite H; auto.
  Qed.

  Lemma rmap_ext: forall phi1 phi2,
    level phi1 = level phi2 ->
    (forall l, phi1@l = phi2@l) ->
    phi1=phi2.
  Proof.
    intros.
    apply unsquash_inj.
    rewrite rmap_level_eq in *.
    unfold resource_at in *.
    rewrite <- (squash_unsquash phi1).
    rewrite <- (squash_unsquash phi2).
    destruct (unsquash phi1).
    destruct (unsquash phi2).
    simpl in H.
    rewrite H.
    rewrite unsquash_squash.
    rewrite unsquash_squash.
    simpl in H0.
    replace (rmap_fmap (approx n0) (approx n0) r) with (rmap_fmap (approx n0) (approx n0) r0); auto.
    destruct r; destruct r0.
    simpl in *.
    generalize (valid_res_map (approx n0) (approx n0) x0 v0).
    generalize (valid_res_map (approx n0) (approx n0) x v).
    replace (resource_fmap (approx n0) (approx n0) oo x0)
      with (resource_fmap (approx n0) (approx n0) oo x).
    intros v1 v2; replace v2 with v1 by apply proof_irr; auto.
    extensionality l.
    unfold compose.
    spec H0 l.
    subst n0.
    rewrite H0; auto.
  Qed.

  Lemma resource_at_join:
    forall phi1 phi2 phi3 loc,
      join phi1 phi2 phi3 ->
      join (phi1@loc) (phi2@loc) (phi3@loc).
  Proof.
    intros.
    revert H; rewrite join_unsquash; unfold resource_at.
    intros [? ?].
    apply H0.
  Qed.

  Lemma resource_at_join2:
    forall phi1 phi2 phi3,
      level phi1 = level phi3 -> level phi2 = level phi3 ->
      (forall loc, join (phi1@loc) (phi2@loc) (phi3@loc)) ->
      join phi1 phi2 phi3.
  Proof.
    intros ? ? ?.
    rewrite join_unsquash.
    rewrite rmap_level_eq in *.
    unfold resource_at.
    case_eq (unsquash phi1); case_eq (unsquash phi2); case_eq (unsquash phi3); simpl; intros.
    subst.
    split; auto.
  Qed.

Lemma all_resource_at_identity:
  forall w, (forall l, identity (w@l)) ->
         identity w.
Proof.
  intros.
  rewrite identity_unit_equiv.
  apply join_unsquash.
  split. split; auto.
  revert H. unfold resource_at.
  case_eq (unsquash w); simpl; intros.
  intro a. spec H0 a.
  rewrite identity_unit_equiv in H0.
  trivial.
Qed.

  Lemma ageN_squash : forall d n rm, le d n ->
    ageN d (squash (n, rm)) = Some (squash ((n - d)%nat, rm)).
  Proof.
    induction d; simpl; intros.
    unfold ageN; simpl.
    replace (n-0)%nat with n by omega; auto.
    unfold ageN; simpl.
    rewrite rmap_age1_eq in *.
    rewrite unsquash_squash.
    destruct n.
    inv H.
    replace (S n - S d)%nat with (n - d)%nat by omega.
    unfold ageN in IHd. rewrite rmap_age1_eq in IHd.
    rewrite IHd.
    2: omega.
    f_equal.
    apply unsquash_inj.
    rewrite !unsquash_squash.
    f_equal.
    change (rmap_fmap (approx (n - d)) (approx (n - d))
             (rmap_fmap (approx (S n)) (approx (S n)) rm)) with
           ((rmap_fmap (approx (n - d)) (approx (n - d)) oo
              rmap_fmap (approx (S n)) (approx (S n))) rm).
    rewrite rmap_fmap_comp.
    f_equal.
    + clear.
      assert (n-d <= (S n))%nat by omega.
      revert H; generalize (n-d)%nat (S n).
      clear.
      intros.
      extensionality p.
      apply pred_ext'.  extensionality w.
      unfold compose, approx.
      apply prop_ext; simpl; intuition.
    + clear.
      assert (n-d <= (S n))%nat by omega.
      revert H; generalize (n-d)%nat (S n).
      clear.
      intros.
      extensionality p.
      apply pred_ext'.  extensionality w.
      unfold compose, approx.
      apply prop_ext; simpl; intuition.
  Qed.

  Lemma unageN: forall n (phi': rmap),   exists phi, ageN n phi = Some phi'.
  Proof.
    intros n phi'.
    rewrite <- (squash_unsquash phi').
    destruct (unsquash phi'); clear phi'.
    exists (squash ((n+n0)%nat,r)).
    rewrite ageN_squash.
    replace (n + n0 - n)%nat with n0 by omega; auto.
    omega.
  Qed.


Lemma YES_join_full: 
   forall rsh n P r2 r3,
       join (R.YES rsh pfullshare n P) r2 r3 ->
       exists rsh2, r2 = NO rsh2.
Proof.
  intros.
  inv H. eauto.
  pfullshare_join.
Qed.

Lemma YES_not_identity:
  forall rsh sh k Q, ~ identity (YES rsh sh k Q).
Proof.
intros. intro.
rewrite identity_unit_equiv in H.
simpl in * |-.
unfold unit_for in H.
inv H.
apply no_units in H1; auto.
Qed.

Lemma YES_overlap:
forall rsh0 rsh1 (phi0 phi1: rmap) loc (sh : pshare) k k' p p',
  joins phi0 phi1 -> phi1@loc = R.YES rsh1 pfullshare k p -> 
               phi0@loc = R.YES rsh0 sh k' p' -> False.
Proof.
  intros.
  destruct H as [phi3 ?].
  generalize (resource_at_join _ _ _ loc H); intro.
  rewrite H1 in H2.
  rewrite H0 in H2.
  contradiction (YES_not_identity rsh0 sh k' p').
  apply join_comm in H2. apply YES_join_full in H2. destruct H2; discriminate.
Qed.

Lemma necR_NOx:
   forall phi phi' l rsh, necR phi phi' -> phi@l = NO rsh -> phi'@l = NO rsh.
Proof.
induction 1; eauto.
unfold age in H; simpl in H.
revert H; rewrite rmap_age1_eq; unfold resource_at.
destruct (unsquash x).
intros; destruct n; inv H.
rewrite unsquash_squash; simpl in *; auto.
destruct r; simpl in *.
unfold compose.
rewrite H0.
auto.
Qed.

Ltac do_map_arg :=
match goal with |- ?a = ?b =>
  match a with context [map ?x _] =>
    match b with context [map ?y _] => replace y with x; auto end end end.

Lemma preds_fmap_fmap: 
  forall f1 f2 g1 g2 pp, preds_fmap f1 f2 (preds_fmap g1 g2 pp) = preds_fmap (f1 oo g1) (g2 oo f2) pp.
Proof.
destruct pp; simpl; auto.
f_equal; extensionality i.
rewrite <- fmap_comp; auto.
Qed.

Lemma resource_fmap_fmap:  forall f1 f2 g1 g2 r, resource_fmap f1 f2 (resource_fmap g1 g2 r) = 
                                                                      resource_fmap (f1 oo g1) (g2 oo f2) r.
Proof.
destruct r; simpl; auto.
rewrite preds_fmap_fmap; auto.
rewrite preds_fmap_fmap; auto.
Qed.

Lemma resource_at_approx:
  forall phi l, 
      resource_fmap (approx (level phi)) (approx (level phi)) (phi @ l) = phi @ l.
Proof.
intros. symmetry. rewrite rmap_level_eq. unfold resource_at.
case_eq (unsquash phi); intros.
simpl.
destruct r; simpl in *.
assert (R.valid (resource_fmap (approx n) (approx n) oo x)).
apply valid_res_map; auto.
set (phi' := (squash (n, exist (fun m : AV.address -> resource => R.valid m) _ H0))).
generalize (unsquash_inj phi phi'); intro.
spec H1.
replace (unsquash phi) with (unsquash (squash (unsquash phi))).
2: rewrite squash_unsquash; auto.
rewrite H.
unfold phi'.
repeat rewrite unsquash_squash.
simpl.
replace (exist (fun m : AV.address -> resource => valid m)
  (resource_fmap (approx n) (approx n) oo x) (valid_res_map (approx n) (approx n) x v)) with
(exist (fun m : AV.address -> resource => valid m)
  (resource_fmap (approx n) (approx n) oo resource_fmap (approx n) (approx n) oo x)
  (valid_res_map (approx n) (approx n) (resource_fmap (approx n) (approx n) oo x) H0)); auto.
assert (Hex: forall A (F: A -> Prop) (x x': A) y y', x=x' -> exist F x y = exist F x' y') by auto with extensionality.
apply Hex.
unfold compose.
extensionality y.
rewrite resource_fmap_fmap.
rewrite approx_oo_approx; auto.
unfold phi' in *; clear phi'.
subst.
rewrite unsquash_squash in H.
injection H; clear H; intro.
pattern x at 1; rewrite <- H.
unfold compose.
rewrite resource_fmap_fmap.
rewrite approx_oo_approx; auto.
Qed.

Lemma necR_resource_at:
  forall phi phi' loc r,
        necR phi phi' ->
         phi @ loc = resource_fmap (approx (level phi)) (approx (level phi)) r ->
         phi' @ loc = resource_fmap (approx (level phi')) (approx (level phi')) r.
Proof.
intros.
revert r loc H0; induction H; intros; auto.
unfold age in H.
simpl in H.
revert H H0; rewrite rmap_level_eq, rmap_age1_eq; unfold resource_at.
 case_eq (unsquash x); intros.
destruct n; inv H0.
simpl in *.
rewrite unsquash_squash; simpl.
destruct r0; simpl in *.
unfold compose in *.
rewrite H1; clear H1.
rewrite resource_fmap_fmap.
rewrite approx_oo_approx'; auto.
rewrite approx'_oo_approx; auto.
Qed.

Lemma necR_YES:
  forall phi phi' loc rsh sh k pp,
        necR phi phi' ->
         phi @ loc = YES rsh sh k pp ->
         phi' @ loc = YES rsh sh k (preds_fmap (approx (level phi')) (approx (level phi')) pp).
Proof.
intros.
generalize (eq_sym (resource_at_approx phi loc)); 
pattern (phi @ loc) at 2; rewrite H0; intro.
apply (necR_resource_at _ _ _ _ H H1).
Qed.

Lemma necR_PURE:
  forall phi phi' loc k pp,
        necR phi phi' ->
         phi @ loc = PURE k pp ->
         phi' @ loc = PURE k (preds_fmap (approx (level phi')) (approx (level phi')) pp).
Proof.
  intros.
  generalize (eq_sym (resource_at_approx phi loc)); 
  pattern (phi @ loc) at 2; rewrite H0; intro.
  apply (necR_resource_at _ _ _ _ H H1).
Qed.

Lemma necR_NO:
   forall phi phi' l rsh, necR phi phi' -> 
   (phi@l = NO rsh <-> phi'@l = NO rsh).
Proof.
  intros; split.
  apply necR_NOx; auto.
  intros.
  case_eq (phi @ l); intros; auto.
   generalize (necR_NOx _ _ l t H H1); intro. congruence.
  generalize (necR_YES _ _ _ _ _ _ _ H H1); congruence.
  generalize (necR_PURE _ _ _ _ _ H H1); congruence.
Qed.

Lemma resource_at_empty: forall phi, identity phi -> forall l, (phi @ l = NO Share.bot \/ exists k, exists pds, phi @ l = PURE k pds).
Proof.
  intros.
  rewrite identity_unit_equiv in H.
  unfold unit_for in H.
  generalize (resource_at_join _ _ _ l H); intro.
  remember (phi @ l) as r.
  destruct r; inv H0; eauto.
  apply identity_unit_equiv in RJ; apply identity_share_bot in RJ; subst; auto.
  apply no_units in H2; contradiction.
Qed.
Implicit Arguments resource_at_empty.


Lemma rmap_valid: forall r, AV.valid (res_option oo resource_at r).
Proof.
unfold compose, resource_at; intros.
destruct (unsquash r).
destruct r0.
simpl.
apply v.
Qed.

Ltac inj_pair_tac := 
 match goal with H: (@existT ?U ?P ?p ?x = @existT _ _ _ ?y) |- _ =>
   generalize (@inj_pair2 U P p x y H); clear H; intro; try (subst x || subst y)
 end.

Lemma preds_fmap_NoneP:
  forall f1 f2, preds_fmap f1 f2 NoneP = NoneP.
Proof.
intros.
unfold NoneP.
auto.
Qed.

Lemma necR_YES': 
   forall phi phi' loc rsh sh k, 
         necR phi phi' -> (phi@loc = YES rsh sh k NoneP <-> phi'@loc = YES rsh sh k NoneP).
Proof.
intros.
induction H.
rename x into phi; rename y into phi'.
unfold age in H; simpl in H.
(* revert H; case_eq (age1 phi); intros; try discriminate. *)
inv H.
split; intros.
rewrite (necR_YES phi phi' loc rsh sh k NoneP); auto. constructor 1; auto.
rewrite rmap_age1_eq in *.
unfold resource_at in *.
revert H1; case_eq (unsquash phi); simpl; intros.
destruct n; inv H1.
rewrite unsquash_squash in H. simpl in H. destruct r; simpl in *.
unfold compose in H. 
revert H; destruct (x loc); simpl; intros; auto.
destruct p0; inv H.
inj_pair_tac. f_equal.
unfold NoneP; f_equal.
auto.
inv H.
intuition.
intuition.
Qed.

Lemma necR_YES'':
   forall phi phi' loc rsh sh k, 
         necR phi phi' -> 
    ((exists pp, phi@loc = YES rsh sh k pp) <-> 
    (exists pp, phi'@loc = YES rsh sh k pp)).
Proof.
intros.
induction H; try solve [intuition].
rename x into phi; rename y into phi'.
revert H; unfold age; case_eq (age1 phi); intros; try discriminate.
inv H0.
simpl in *.
split; intros [pp ?].
+ econstructor;
  apply (necR_YES phi phi' loc rsh sh k pp).
  constructor 1; auto. auto.
+ rename phi' into r.
  rewrite rmap_age1_eq in *.
  unfold resource_at in *.
  revert H; case_eq (unsquash phi); simpl; intros.
  destruct n; inv H1.
  rewrite unsquash_squash in H0. simpl in H0. destruct r0; simpl in *.
  unfold compose in H0. 
  revert H0; destruct (x loc); simpl; intros; auto.
  inv H0.
  inv H0.
  econstructor; eauto.
  inv H0.
Qed.

Lemma necR_PURE': 
   forall phi phi' loc k,
         necR phi phi' -> 
    ((exists pp, phi@loc = PURE k pp) <-> 
    (exists pp, phi'@loc = PURE k pp)).
Proof.
intros.
induction H; try solve [intuition].
rename x into phi; rename y into phi'.
revert H; unfold age; case_eq (age1 phi); intros; try discriminate.
inv H0.
simpl in *.
split; intros [pp ?].
+ econstructor;
  apply (necR_PURE phi phi' loc k pp).
  constructor 1; auto. auto.
+ rename phi' into r.
  rewrite rmap_age1_eq in *.
  unfold resource_at in *.
  revert H; case_eq (unsquash phi); simpl; intros.
  destruct n; inv H1.
  rewrite unsquash_squash in H0. simpl in H0. destruct r0; simpl in *.
  unfold compose in H0. 
  revert H0; destruct (x loc); simpl; intros; auto.
  inv H0.
  inv H0.
  econstructor; eauto.
  inv H0.
  eauto.
Qed.

Lemma resource_at_join_sub:
  forall phi1 phi2 l,
       join_sub phi1 phi2 -> join_sub (phi1@l) (phi2@l).
Proof.
intros.
destruct H as [phi ?].
generalize (resource_at_join _ _ _ l H); intro.
econstructor; eauto.
Qed.

Lemma age1_res_option: forall phi phi' loc,
     age1 phi = Some phi' -> res_option (phi @ loc) = res_option (phi' @ loc).
  Proof.
    unfold res_option, resource_at; simpl.
   rewrite rmap_age1_eq; intros phi1 phi2 l.
 case_eq (unsquash phi1); intros. destruct n; inv H0.
 rewrite unsquash_squash.
   destruct r; 
    simpl.
   unfold compose. destruct (x l); simpl; auto.
Qed.

Lemma necR_res_option:
  forall (phi phi' : rmap) (loc : AV.address),
  necR phi phi' -> res_option (phi @ loc) = res_option (phi' @ loc).
Proof.
  intros.
  case_eq (phi @ loc); intros.
  rewrite (necR_NO _ _ _ _ H) in H0. congruence.
  destruct p0.
  rewrite (necR_YES phi phi' loc _ _ _ _ H H0); auto.
  rewrite (necR_PURE phi phi' loc _ _ H H0); auto.
Qed.


Lemma age1_resource_at: 
     forall phi phi', 
          age1 phi = Some phi' ->
         forall loc r, 
          phi @ loc = resource_fmap (approx (level phi)) (approx (level phi)) r ->
          phi' @ loc = resource_fmap (approx (level phi')) (approx (level phi')) r.
Proof.
   unfold resource_at; rewrite rmap_age1_eq, rmap_level_eq.
intros until phi'; case_eq (unsquash phi); intros.
simpl in *.
destruct n; inv H0.
rewrite unsquash_squash.
destruct r; simpl in *.
unfold compose; rewrite H1.
rewrite resource_fmap_fmap.
rewrite approx_oo_approx'; auto.
rewrite approx'_oo_approx; auto.
Qed.


Lemma age1_YES: forall phi phi' l rsh sh k ,
  age1 phi = Some phi' -> (phi @ l = YES rsh sh k NoneP <-> phi' @ l = YES rsh sh k NoneP).
Proof.
intros.
apply necR_YES'.
constructor 1; auto.
Qed.

Lemma age1_YES': forall phi phi' l rsh sh k ,
  age1 phi = Some phi' -> ((exists P, phi @ l = YES rsh sh k P) <-> exists P, phi' @ l = YES rsh sh k P).
Proof.
intros.
apply necR_YES''.
constructor 1; auto.
Qed.

Lemma age1_NO: forall phi phi' l rsh,
  age1 phi = Some phi' -> (phi @ l = NO rsh <-> phi' @ l = NO rsh).
Proof.
intros.
apply necR_NO.
constructor 1; auto.
Qed.

Lemma age1_PURE: forall phi phi' l k ,
  age1 phi = Some phi' -> ((exists P, phi @ l = PURE k P) <-> exists P, phi' @ l = PURE k P).
Proof.
  intros.
  apply necR_PURE'.
  constructor 1; auto.
Qed.
  
Lemma empty_NO: forall r, identity r -> r = NO Share.bot \/ exists k, exists pds, r = PURE k pds.
Proof.
intros.
destruct r; auto.
left. f_equal. apply identity_unit_equiv in H. inv H.
  apply identity_unit_equiv in RJ. apply identity_share_bot in RJ. subst. auto.
unfold identity in H.
spec H (NO Share.bot) (YES t p k p0).
spec H.
apply res_join_NO2.
auto.
inv H.
right. exists k. exists p. trivial.
Qed.

Lemma level_age_fash:
  forall m m': rmap, level m = S (level m') -> exists m1, age m m1.
Proof.
  intros.
  case_eq (age1 m); intros.
  exists r. auto.
  elimtype False.
  eapply age1None_levelS_absurd in H0; eauto.
Qed.

Lemma level_later_fash:
 forall m m': rmap, (level m > level m')%nat  -> exists m1, laterR m m1 /\ level m1 = level m'.
Proof.
  intros.
  assert (exists k, level m = S k + level m')%nat.
    exists (level m - S (level m'))%nat.
    omega.
  clear H; destruct H0 as [k ?].
  revert m H; induction k; intros.
  simpl in H.
  destruct (level_age_fash _ _ H) as [m1 ?].
  exists m1; split; auto.
  constructor 1; auto.
  apply age_level in H0. rewrite H in H0. inv H0. trivial.
  case_eq (age1 m); intros.
  spec IHk r.
  rewrite <- ageN1 in H0.
  generalize (ageN_level _ _ _ H0); intro.
  spec IHk; try omega.
  destruct IHk as [m1 [? ?]].
  exists m1; split; auto.
  econstructor 2; eauto.
  rewrite ageN1 in H0.
  constructor 1.
  auto.
  elimtype False.
  eapply age1None_levelS_absurd in H0; eauto.
Qed.

Lemma resource_at_constructive_joins2:
  forall phi1 phi2,
       level phi1 = level phi2 ->
       (forall loc, constructive_joins (phi1 @ loc) (phi2 @ loc)) ->
         constructive_joins phi1 phi2.
Proof.
intros ? ? ? H0.
assert (AV.valid (res_option oo (fun loc => proj1_sig (H0 loc)))).
apply AV.valid_join with (res_option oo (resource_at phi1)) (res_option oo (resource_at phi2));
 try apply rmap_valid.
intro l.
unfold compose in *.
destruct (H0 l); simpl in *.
destruct (phi1 @ l). inv j; constructor.
inv j; constructor. split; auto. 
inv j; constructor.
(** End of CompCert_AV.valid proof **)
destruct (make_rmap _ H1 (level phi1)) as [phi' [? ?]].
clear H1.
unfold compose; extensionality loc.
spec H0 loc.
destruct H0 as [? H1].
simpl.
symmetry.
revert H1; case_eq (phi1 @ loc); intros.
inv H1. reflexivity.
pose proof (resource_at_approx phi2 loc). rewrite <- H4 in H1. simpl in H1.
injection H1; intros.
simpl; f_equal; auto. rewrite H; auto.
inv H1.
pose proof (resource_at_approx phi1 loc). rewrite H0 in H1. simpl in H1.
injection H1; intros.
simpl; f_equal; auto.
simpl; f_equal.
pose proof (resource_at_approx phi1 loc). rewrite H0 in H1. simpl in H1.
injection H1; intros; auto.
inv H1.
simpl; f_equal.
pose proof (resource_at_approx phi1 loc). rewrite H0 in H1. simpl in H1.
injection H1; intros; auto.
(*  End of make_rmap proof *)
exists phi'.
apply resource_at_join2; auto.
congruence.
intros.
rewrite H3.
destruct (H0 loc).
simpl; auto.
Qed.

Lemma resource_at_joins2:
  forall phi1 phi2,
       level phi1 = level phi2 ->
       (forall loc, constructive_joins (phi1 @ loc) (phi2 @ loc)) ->
         joins phi1 phi2.
Proof.
  intros.
  apply cjoins_joins.
  apply resource_at_constructive_joins2; trivial.
Qed.

Definition no_preds (r: resource) :=
   match r with NO _ => True | YES _ _ _ pp => pp=NoneP | PURE _ pp => pp=NoneP end.

Lemma remake_rmap:
  forall (f: AV.address -> resource),
       AV.valid (res_option oo f) ->
       forall n, 
       (forall l, (exists m, level m = n /\ f l = m @ l) \/ no_preds (f l)) ->
       {phi: rmap | level phi = n /\ resource_at phi = f}.
Proof.
  intros.
  apply make_rmap; auto.
  extensionality l.
  unfold compose.
  destruct (H0 l); clear H0.
  destruct H1 as [m [?  ?]].
  rewrite H1.
  subst.
  apply resource_at_approx.
  destruct (f l); simpl in *; auto;
  [destruct p0 | destruct p];
  rewrite H1;
  apply f_equal;
  apply preds_fmap_NoneP.
Qed.

Lemma rmap_unage_age:
  forall r, age (rmap_unage r) r.
Proof.
intros; unfold age, rmap_unage; simpl.
case_eq (unsquash r); intros.
rewrite rmap_age1_eq.
rewrite unsquash_squash.
f_equal.
apply unsquash_inj.
rewrite H.
rewrite unsquash_squash.
f_equal.
generalize (equal_f (rmap_fmap_comp (approx (S n)) (approx (S n)) (approx n) (approx n)) r0); intro.
unfold compose at 1 in H0.
rewrite H0.
rewrite approx_oo_approx'; auto.
rewrite approx'_oo_approx; auto.
clear - H.
generalize (unsquash_squash n r0); intros.
rewrite <- H in H0.
rewrite squash_unsquash in H0.
congruence.
Qed.

Lemma ageN_resource_at_eq:
  forall phi1 phi2 loc n phi1' phi2', 
          level phi1 = level phi2 ->
          phi1 @ loc = phi2 @ loc -> 
         ageN n phi1 = Some phi1' ->
         ageN n phi2 = Some phi2' ->
         phi1' @ loc = phi2' @ loc.
Proof.
intros ? ? ? ? ? ? Hcomp ? ? ?; revert phi1 phi2 phi1' phi2' Hcomp H H0 H1; induction n; intros.
inv H0; inv H1; auto.
unfold ageN in H0, H1.
simpl in *.
revert H0 H1; case_eq (age1 phi1); case_eq (age1 phi2); intros; try discriminate.
assert (level r = level r0) by (apply age_level in H0; apply age_level in H1; omega).
apply (IHn r0 r); auto.
rewrite (age1_resource_at _ _ H0 loc _ (eq_sym (resource_at_approx _ _))). 
rewrite (age1_resource_at _ _ H1 loc _ (eq_sym (resource_at_approx _ _))).
rewrite H. rewrite H4; auto.
Qed.


Lemma join_YES_pfullshare1:
    forall rsh1 pp k p x y, 
       join (YES rsh1 (mk_lifted Share.top pp) k p) x y -> 
        exists rsh2, exists rsh3, 
        (NO rsh2, YES rsh3 pfullshare k p) = (x,y).
Proof.
intros. inv H; try pfullshare_join; f_equal; auto.
  unfold pfullshare.
  exists rsh2, rsh3; f_equal; f_equal; f_equal. apply proof_irr.
Qed.

Lemma join_YES_pfullshare2:
    forall rsh2 pp k p x y, join x (YES rsh2 (mk_lifted Share.top pp) k p) y -> 
        exists rsh1, exists rsh3, 
        (NO rsh1, YES rsh3 pfullshare k p) = (x,y).
Proof.
intros. inv H; try pfullshare_join; f_equal; auto.
  unfold pfullshare.
  exists rsh1, rsh3; f_equal; f_equal; f_equal. apply proof_irr.
Qed.

Ltac inv H := ((apply join_YES_pfullshare1 in H; destruct H as [?rsh [?rsh H]]) 
                     || (apply join_YES_pfullshare2 in H ; destruct H as [?rsh [?rsh H]]) 
                     || idtac); 
                  (inversion H; clear H; subst).

  Definition empty_rmap' : rmap'.
    set (f:= fun _: AV.address => NO Share.bot).
    assert (R.valid f).
    red; unfold f; simpl.
    apply AV.valid_empty.
    exact (exist _ f H).
  Defined.

  Definition empty_rmap (n:nat) : rmap := R.squash (n, empty_rmap').

Lemma emp_empty_rmap: forall n, emp (empty_rmap n).
Proof. 
intros.
intro; intros.
apply rmap_ext.
Comp.
intros.
apply (resource_at_join _ _ _ l) in H.
unfold empty_rmap, empty_rmap', resource_at in *.
destruct (unsquash a); destruct (unsquash b).
simpl in *.
destruct r; destruct r0; simpl in *.
rewrite unsquash_squash in H.
simpl in *.
unfold compose in H.
inv H; auto; apply join_unit1_e in RJ; auto; subst; auto.
Qed.

Lemma empty_rmap_level:
  forall lev, level (empty_rmap lev) = lev.
Proof.
intros.
simpl.
rewrite rmap_level_eq.
unfold  empty_rmap.
rewrite unsquash_squash; auto.
Qed.

Lemma approx_FF: forall n, approx n FF = FF.
Proof.
intros.
apply pred_ext; auto.
unfold approx; intros ? ?.
hnf in H. destruct H; auto.
Qed.

Lemma resource_at_make_rmap: forall f V lev H, resource_at (proj1_sig (make_rmap f V lev H)) = f.
refine (fun f V lev H => match proj2_sig (make_rmap f V lev H) with
                           | conj _ RESOURCE_AT => RESOURCE_AT
                         end).
Qed.

Lemma level_make_rmap: forall f V lev H, @level rmap _ (proj1_sig (make_rmap f V lev H)) = lev.
refine (fun f V lev H => match proj2_sig (make_rmap f V lev H) with
                           | conj LEVEL _ => LEVEL
                         end).
Qed.

Instance Join_trace : Join (AV.address -> option (pshare * AV.kind)) :=
     (Join_fun AV.address (option (pshare * AV.kind))
                   (Join_lower (Join_prod pshare Join_pshare AV.kind (Join_equiv AV.kind)))).


 Lemma res_option_join:
    forall x y z, join x y z -> @join _ (@Join_lower (pshare * AV.kind)
     (Join_prod pshare Join_pshare AV.kind (Join_equiv AV.kind))) (res_option x) (res_option y) (res_option  z).
 Proof.
   intros.
  inv H; constructor.  split; auto. 
 Qed.

Lemma Cross_resource: Cross_alg resource.
Proof.
intro; intros.
destruct a as [ra | ra sa ka pa | ka pa ].
destruct b as [rb | rb sb kb pb | kb pb ]; try solve [elimtype False; inv H].
destruct z as [rz | rz sz kz pz | kz pz ]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc ]; try solve [elimtype False; inv H0].
destruct d as [rd | rd sd kd pd | kd pd ]; try solve [elimtype False; inv H0].
assert (J1: join ra rb rz) by (inv H; auto).
assert (J2: join rc rd rz) by (inv H0; auto).
destruct (share_cross_split _ _ _ _ _ J1 J2) as [[[[ac ad] bc] bd] [Ha [Hb [Hc Hd]]]].
exists (NO ac,NO ad, NO bc, NO bd); 
  repeat split; simpl; auto; constructor; auto.
destruct z as [rz | rz sz kz pz | kz pz ]; try solve [elimtype False; inv H].
destruct c as [rc | rc sc kc pc | kc pc ]; try solve [elimtype False; inv H0].
destruct d as [rd | rd sd kd pd | kd pd ]; try solve [elimtype False; inv H0].
assert (J1: join ra rb rz) by (inv H; auto).
assert (J2: join rc rd rz) by (inv H0; auto).
destruct (share_cross_split _ _ _ _ _ J1 J2) as [[[[ac ad] bc] bd] [Ha [Hb [Hc Hd]]]].
exists (NO ac, NO ad, NO bc, YES bd sb kb pb); inv H; inv H0;
  repeat split; simpl; auto; try constructor; auto.
assert (J1: join ra rb rz) by (inv H; auto).
destruct d as [rd | rd sd kd pd | kd pd ]; try solve [elimtype False; inv H0].
assert (J2: join rc rd rz) by (inv H0; auto).
destruct (share_cross_split _ _ _ _ _ J1 J2) as [[[[ac ad] bc] bd] [Ha [Hb [Hc Hd]]]].
exists (NO ac, NO ad, YES bc sb kb pb, NO bd); inv H; inv H0;
  repeat split; simpl; auto; try constructor; auto.
assert (J2: join rc rd rz) by (inv H0; auto).
destruct (share_cross_split _ _ _ _ _ J1 J2) as [[[[ac ad] bc] bd] [Ha [Hb [Hc Hd]]]].
exists (NO ac, NO ad, YES bc sc kb pb, YES bd sd kd pd); inv H; inv H0;
  repeat split; simpl; auto; try constructor; auto.
destruct b as [rb | rb sb kb pb | kb pb ]; try solve [elimtype False; inv H].
destruct z as [rz | rz sz kz pz | kz pz ]; try solve [elimtype False; inv H].
assert (J1: join ra rb rz) by (inv H; auto).
destruct c as [rc | rc sc kc pc | kc pc ]; try solve [elimtype False; inv H0].
destruct d as [rd | rd sd kd pd | kd pd ]; try solve [elimtype False; inv H0].
assert (J2: join rc rd rz) by (inv H0; auto).
destruct (share_cross_split _ _ _ _ _ J1 J2) as [[[[ac ad] bc] bd] [Ha [Hb [Hc Hd]]]].
exists (NO ac, YES ad sd kd pd, NO bc, NO bd); inv H; inv H0;
  repeat split; simpl; auto; try constructor; auto.
destruct d as [rd | rd sd kd pd | kd pd ]; try solve [elimtype False; inv H0].
assert (J2: join rc rd rz) by (inv H0; auto).
destruct (share_cross_split _ _ _ _ _ J1 J2) as [[[[ac ad] bc] bd] [Ha [Hb [Hc Hd]]]].
exists (YES ac sc kc pc, NO ad, NO bc, NO bd); inv H; inv H0;
  repeat split; simpl; auto; try constructor; auto.
assert (J2: join rc rd rz) by (inv H0; auto).
destruct (share_cross_split _ _ _ _ _ J1 J2) as [[[[ac ad] bc] bd] [Ha [Hb [Hc Hd]]]].
exists (YES ac sc kc pc, YES ad sd kd pd, NO bc, NO bd); inv H; inv H0;
  repeat split; simpl; auto; try constructor; auto.
destruct z as [rz | rz sz kz pz | kz pz ]; try solve [elimtype False; inv H].
assert (J1: join ra rb rz) by (inv H; auto).
destruct c as [rc | rc sc kc pc | kc pc ]; try solve [elimtype False; inv H0].
destruct d as [rd | rd sd kd pd | kd pd ]; try solve [elimtype False; inv H0].
assert (J2: join rc rd rz) by (inv H0; auto).
destruct (share_cross_split _ _ _ _ _ J1 J2) as [[[[ac ad] bc] bd] [Ha [Hb [Hc Hd]]]].
exists (NO ac, YES ad sa kd pd, NO bc, YES bd sb kd pd); inv H; inv H0;
  repeat split; simpl; auto; try constructor; auto.
destruct d as [rd | rd sd kd pd | kd pd ]; try solve [elimtype False; inv H0].
assert (J2: join rc rd rz) by (inv H0; auto).
destruct (share_cross_split _ _ _ _ _ J1 J2) as [[[[ac ad] bc] bd] [Ha [Hb [Hc Hd]]]].
exists (YES ac sa kc pc, NO ad, YES bc sb kb pb, NO bd); inv H; inv H0;
  repeat split; simpl; auto; try constructor; auto.
assert (J2: join rc rd rz) by (inv H0; auto).
destruct (share_cross_split _ _ _ _ _ J1 J2) as [[[[ac ad] bc] bd] [Ha [Hb [Hc Hd]]]].
assert (S1: join sa sb sz) by (inv H; auto).
assert (S2: join sc sd sz) by (inv H0; auto).
destruct (share_cross_split _ _ _ _ _ S1 S2) as [[[[ac' ad'] bc'] bd'] [Ha' [Hb' [Hc' Hd']]]].
destruct (dec_share_identity ac').
apply i in Ha'; apply i in Hc'. subst.
destruct (dec_share_identity bd').
apply join_comm in Hb'; apply join_comm in Hd'; apply i0 in Hb'; apply i0 in Hd'; subst.
apply lifted_eq in Hb'. apply lifted_eq in Hd'; subst sb sd.
exists (NO ac, YES ad sa ka pa, YES bc sc kc pc, NO bd); 
   inv H; inv H0; simpl; repeat split; auto;  constructor; auto.
apply nonidentity_nonunit in n.
exists (NO ac, YES ad sa ka pa, YES bc sc kc pc, YES bd (mk_lifted _ n) kd pd); 
   inv H; inv H0; simpl; repeat split; auto;  constructor; auto.
destruct (dec_share_identity ad').
apply join_comm in Ha'; apply i in Ha'; apply i in Hd'; subst bd' ac'.
clear n.
destruct (dec_share_identity bc').
apply join_comm in Hc'; apply i0 in Hb'; apply i0 in Hc'.  apply lifted_eq in Hb'; apply lifted_eq in Hc'; subst sd sc.
exists (YES ac sa ka pa, NO ad, NO bc, YES bd sb kb pb); 
   inv H; inv H0; simpl; repeat split; auto;  constructor; auto.
exists (YES ac sa ka pa, NO ad, YES bc (mk_lifted _ (nonidentity_nonunit n)) kc pc, YES bd sd kd pd);
    inv H; inv H0; simpl; repeat split; auto;  constructor; auto.
destruct (dec_share_identity bc').
apply join_comm in Hc'; apply i in Hb'; apply i in Hc'.  subst ac' bd'.
exists (YES ac sc kc pc, YES ad (mk_lifted _ (nonidentity_nonunit n0)) kc pc, NO bc, YES bd sb kb pb);
    inv H; inv H0; simpl; repeat split; auto;  constructor; auto.
destruct (dec_share_identity bd').
apply join_comm in Hb'; apply join_comm in Hd';
 apply i in Hb'; apply i in Hd'. subst bc' ad'.
exists (YES ac (mk_lifted _ (nonidentity_nonunit n)) ka pa,  YES ad sd kd pd, YES bc sb kb pb, NO bd);
    inv H; inv H0; simpl; repeat split; auto;  constructor; auto.
exists (YES ac (mk_lifted _ (nonidentity_nonunit n)) ka pa, YES ad (mk_lifted _ (nonidentity_nonunit n0)) ka pa, 
       YES bc (mk_lifted _ (nonidentity_nonunit n1)) ka pa,  YES bd (mk_lifted _ (nonidentity_nonunit n2)) ka pa);
    inv H; inv H0; simpl; repeat split; auto;  constructor; auto.
exists (PURE ka pa, PURE ka pa, PURE ka pa, PURE ka pa).
inv H. inv H0.
repeat split; constructor; auto.
Qed.

Definition res_retain (r: resource) : Share.t :=
 match r with
  | NO sh => sh
  | YES sh _ _ _ => sh
  | PURE _ _ => Share.bot
 end.

Definition fixup_trace (retain: AV.address -> Share.t)
                                    (trace: AV.address -> option (pshare * AV.kind))
                                    (f: AV.address -> resource) : AV.address -> resource :=
   fun x => match trace x, f x with
                   | None, PURE k pp => PURE k pp
                   | Some(sh,k), PURE _ pp => YES (retain x) sh k pp
                   | Some (sh,k), YES _ _ _ pp => YES (retain x) sh k pp
                   | Some (sh, k), NO _ => YES (retain x) sh k NoneP
                   | None, _ => NO (retain x)
                   end.

Lemma fixup_trace_valid: forall retain tr f, 
            AV.valid tr -> 
            AV.valid (res_option oo (fixup_trace retain tr f)).
 Proof. intros.
  replace (res_option oo fixup_trace retain tr f) with tr. auto.
  extensionality l. unfold compose. unfold fixup_trace.
  destruct (tr l); simpl; auto.
  destruct p. destruct (f l); simpl; auto.
  destruct (f l); reflexivity.
Qed.

Lemma fixup_trace_rmap:
    forall (retain: AV.address -> Share.t) (tr: sig AV.valid) (f: rmap),
        {phi: rmap | 
             level phi = level f 
            /\ resource_at phi = fixup_trace retain (proj1_sig tr) (resource_at f)}.
Proof.
 intros.
 apply make_rmap. apply fixup_trace_valid. destruct tr; simpl; auto.
 extensionality l.
 unfold compose, fixup_trace.
 destruct tr. simpl.
 destruct (x l); simpl; auto. destruct p. 
 case_eq (f @ l); intros.
 unfold resource_fmap. rewrite preds_fmap_NoneP; auto.
 generalize (resource_at_approx f l); intro.
 rewrite H in H0. symmetry in H0.
  simpl in H0. simpl.
   f_equal. injection H0; auto.
 generalize (resource_at_approx f l); intro.
 rewrite H in H0. symmetry in H0.
  simpl in H0. simpl.
   f_equal. injection H0; auto.
 case_eq (f @ l); intros; auto.
 generalize (resource_at_approx f l); intro.
 rewrite H in H0. symmetry in H0.
  simpl in H0. simpl.
   f_equal. injection H0; auto.
Qed.     

Lemma join_res_retain:
          forall a b c: rmap , 
              join a b c -> 
              join (res_retain oo resource_at a) (res_retain oo resource_at b) (res_retain oo resource_at c).
Proof.
 intros.
 intro loc; apply (resource_at_join _ _ _ loc) in H.
  unfold compose.
 inv H; auto.
Qed. 



Ltac crtac :=
 repeat  (solve [constructor; auto] ||
   match goal with
 | H: None = res_option ?A |- _ => destruct A; inv H  
 | H: Some _ = res_option ?A |- _ => destruct A; inv H
 | H: join (NO _) _ _ |- _ => inv H
 | H: join _ (NO _) _ |- _ => inv H
 | H: join (YES _ _ _ _) _ _ |- _ => inv H
 | H: join _ (YES _ _ _ _) _ |- _ => inv H
 | H: join (PURE _ _) _ _ |- _ => inv H
 | H: join _ (PURE _ _) _ |- _ => inv H
 | H: @join _ _ (Some _) _ _ |- _ => inv H
 | H: @join _ _ _ (Some _) _ |- _ => inv H
 | H: @join _ _ None _ _ |- _ => 
                apply join_unit1_e in H; [| apply None_identity]
 | H: @join _ _ _ None _ |- _ => 
                apply join_unit2_e in H; [| apply None_identity]
 | H:  prod pshare AV.kind |- _ => destruct H
 | H: @join _ (Join_equiv _) ?a ?b ?c |- _ => destruct H; try subst a; try subst b; try subst c 
 | H: @join _ (Join_prod _ _ _ _) (_,_) (_,_) (_,_) |- _ => destruct H; simpl fst in *; simpl snd in *
 end; auto).

Instance Cross_rmap: 
      @Cross_alg _ (Join_prop _ Join_trace AV.valid) ->
      Cross_alg rmap.
Proof.
  intro CAV.
  repeat intro.
  assert (Hz : valid (resource_at z)).
  unfold resource_at.
  case_eq (unsquash z); intros.
  simpl.
  destruct r; simpl; auto.
  specialize (CAV
          (exist AV.valid _ (rmap_valid a))
          (exist AV.valid _ (rmap_valid b))
          (exist AV.valid _ (rmap_valid c))
          (exist AV.valid _ (rmap_valid d))
          (exist AV.valid _ Hz)).
  destruct CAV as [[[[Vac Vad] Vbc] Vbd] [Va [Vb [Vc Vd]]]].
  intro l.  unfold compose. simpl.
  apply res_option_join. apply resource_at_join. auto.
  intro l.  simpl. unfold compose.
  apply res_option_join. apply resource_at_join. auto.
  assert (CAR: Cross_alg (AV.address -> Share.t)) by auto with typeclass_instances.
  specialize (CAR _ _ _ _ _ (join_res_retain _ _ _ H) (join_res_retain _ _ _ H0)).
  destruct CAR as [[[[Rac Rad] Rbc] Rbd] [Ra [Rb [Rc Rd]]]].
  destruct (fixup_trace_rmap  Rac Vac z) as [Mac [? ?]].
  destruct (fixup_trace_rmap Rad Vad z) as [Mad [? ?]].
  destruct (fixup_trace_rmap Rbc Vbc z) as [Mbc [? ?]].
  destruct (fixup_trace_rmap Rbd Vbd z) as [Mbd [? ?]].
  exists (Mac,Mad,Mbc,Mbd).
  destruct Vac as [ac ?]; destruct Vad as [ad ?]; destruct Vbc as [bc ?];
  destruct Vbd as [bd ?]; simpl in *.
  assert (LEVa: level a = level z) by (apply join_level in H; destruct H; auto).
  assert (LEVb: level b = level z) by (apply join_level in H; destruct H; auto).
  assert (LEVc: level c = level z) by (apply join_level in H0; destruct H0; auto).
  assert (LEVd: level d = level z) by (apply join_level in H0; destruct H0; auto).
  do 2 red in Va,Vb,Vc,Vd; simpl in *.
  unfold compose in *. clear Hz.
  split; [|split3];   apply resource_at_join2; try congruence; intro l;
  spec Va l; spec Vb l; spec Vc l; spec Vd l;
  apply (resource_at_join _ _ _ l) in H;
  apply (resource_at_join _ _ _ l) in H0;
  try rewrite H2; try rewrite H4; try rewrite H6; try rewrite H8;
  unfold fixup_trace; simpl in *;
  specialize (Ra l); specialize (Rb l); specialize (Rc l); specialize (Rd l); simpl in Ra,Rb,Rc,Rd;
  forget (a @ l) as al; forget (b @ l) as bl; forget (c @ l ) as cl;
  forget (d @ l) as dl; forget (z @ l) as zl;
   clear - Ra Rb Rc Rd Va Vb Vc Vd H H0.
  (* case 1 *)
  destruct (ac l); crtac. destruct (ad l); crtac.
  (* case 2 *)
  destruct (bc l); crtac. destruct (bd l); crtac.
  (* case 3 *)
  destruct (ac l); crtac. destruct (bc l); crtac.
  (* case 4 *)
  destruct (ad l); crtac. destruct (bd l); crtac.
Qed.
 
Lemma Cross_rmap_simple: (forall f, AV.valid f) -> Cross_alg rmap.
Proof.
  intro V.
   apply Cross_rmap.
   intros [a Ha] [b Hb] [c Hc] [d Hd] [e He] ? ?.
   do 2 red in H,H0. simpl in *.
   assert (Cross_alg (AV.address -> option (pshare * AV.kind))).
     apply (cross_split_fun  (option (pshare * AV.kind))).
   eapply (Cross_bij' _ _ _ _ (opposite_bij (option_bij (lift_prod_bij _ _)))).
   apply Cross_smash; auto with typeclass_instances.
   clear; intro. destruct x. destruct (dec_share_identity t); [left|right].
    apply identity_unit_equiv in i. apply identity_unit_equiv. split; auto.
    contradict n.
    apply identity_unit_equiv in n. apply identity_unit_equiv. destruct n; auto.
   clear. extensionality a b c. apply prop_ext.
   destruct a as [[[? ?] ?] | ]; destruct b  as [[[? ?] ?] | ]; destruct c as [[[? ?] ?] | ];
   split; simpl; intro H; inv H; simpl in *; try constructor; auto; hnf in  *; simpl in *;
   try proof_irr; try constructor;
   destruct H3; constructor; simpl; auto.
   destruct (X a b c d e H H0) as [[[[ac ad] bc] bd] [? [? [? ?]]]].
   exists (exist AV.valid ac (V _), exist AV.valid ad (V _), 
              exist AV.valid bc (V _), exist AV.valid bd (V _)).
   split; [ |split3]; simpl; auto.
Qed.

Lemma identity_resource: forall r: resource, identity r <->
    match r with YES _ _ _ _ => False | NO rsh => identity rsh | PURE _ _ => True end.
Proof.
 intros. destruct r.
 split; intro; apply identity_unit_equiv in H;  apply identity_unit_equiv.
 inv H; auto. constructor; auto.
 intuition. specialize (H (NO Share.bot) (YES t p k p0)).
 spec H. constructor. apply join_unit2; auto. inv H.
 intuition. intros  ? ? ?. inv H0. auto.
Qed.

Lemma resource_at_core_identity:  forall m i, identity (core m @ i).
Proof.
  intros.
  generalize (core_duplicable m); intro Hdup. apply (resource_at_join _ _ _ i) in Hdup.
  apply identity_resource.
  case_eq (core m @ i); intros; auto.
  rewrite H in Hdup. inv Hdup. apply identity_unit_equiv; auto.
  rewrite H in Hdup. inv Hdup.
   apply pshare_nonunit in H1. auto. 
Qed.

Lemma YES_inj: forall rsh sh k pp rsh' sh' k' pp',
           YES rsh sh k pp = YES rsh' sh' k' pp' ->
            (rsh,sh,k,pp) = (rsh',sh',k',pp').
Proof. intros. inv H. auto. Qed.

Lemma SomeP_inj1: forall t t' a a', SomeP t a = SomeP t' a' -> t=t'.
  Proof. intros. inv H; auto. Qed.
Lemma SomeP_inj2: forall t a a', SomeP t a = SomeP t a' -> a=a'.
  Proof. intros. inv H. apply inj_pair2 in H1. auto. Qed.
Lemma SomeP_inj:
   forall T a b, SomeP T a = SomeP T b -> a=b.
Proof. intros. inv H. apply inj_pair2 in H1. auto.
Qed.

Lemma PURE_inj: forall T x x' y y', PURE x (SomeP T y) = PURE x' (SomeP T y') -> x=x' /\ y=y'.
 Proof. intros. inv H. apply inj_pair2 in H2. subst; auto. 
 Qed.

Lemma core_resource_at: forall w i, core (w @ i) = core w @ i.
Proof.
 intros.
 generalize (core_unit w); intros.
 apply (resource_at_join _ _ _ i) in H.
 generalize (core_unit (w @ i)); unfold unit_for; intros.
 eapply join_canc; eauto.
Qed.

Lemma resource_at_identity: forall (m: rmap) (loc: AV.address), 
 identity m -> identity (m @ loc).
Proof.
  intros.
  destruct (@resource_at_empty m H loc) as [?|[? [? ?]]].
  rewrite H0. apply NO_identity.
  rewrite H0. apply PURE_identity.
Qed.

Lemma core_YES: forall rsh sh k pp, core (YES rsh sh k pp) = NO Share.bot.
Proof.
 intros. generalize (core_unit (YES rsh sh k pp)); unfold unit_for; intros. 
 inv H; auto.
 apply unit_identity in RJ. apply identity_share_bot in RJ. subst; auto.
 apply pshare_nonunit in H2. contradiction.
Qed.

Lemma core_NO: forall rsh, core (NO rsh) = NO Share.bot.
Proof.
 intros.  generalize (core_unit (NO rsh)); unfold unit_for; intros.
 inv H; auto.
 apply unit_identity in RJ. apply identity_share_bot in RJ. subst; auto.
Qed.

Lemma core_PURE: forall k pp, core (PURE k pp) = PURE k pp.
Proof.
 intros. generalize (core_unit (PURE k pp)); unfold unit_for; intros.
 inv H; auto.
Qed.


Lemma core_not_YES: forall {w loc rsh sh k pp},
   core w @ loc = YES rsh sh k pp -> False.
Proof.
intros.
rewrite <- core_resource_at in H.
destruct (w @ loc); [rewrite core_NO in H | rewrite core_YES in H | rewrite core_PURE in H]; inv H.
Qed.

Lemma resource_at_empty2:
 forall phi: rmap, (forall l, identity (phi @ l)) -> identity phi.
Proof.
intros.
assert (phi = core phi).
apply rmap_ext.
rewrite level_core. auto.
intro l; specialize (H l).
apply identity_unit_equiv in H; apply unit_core in H.
rewrite core_resource_at in *; auto.
rewrite H0.
apply core_identity.
Qed.

Lemma resource_fmap_core:
  forall w loc, resource_fmap (approx (level w)) (approx (level w)) (core (w @ loc)) = core (w @ loc).
Proof.
intros.
case_eq (w @ loc); intros;
 [rewrite core_NO | rewrite core_YES | rewrite core_PURE]; auto.
rewrite <- H. apply resource_at_approx.
Qed.

End Rmaps_Lemmas.
