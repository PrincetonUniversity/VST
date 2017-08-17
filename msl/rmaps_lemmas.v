Require Import VST.msl.msl_standard.
Require Import VST.msl.cjoins.
Require Import VST.msl.rmaps.
Require Import VST.msl.Coqlib2.
Require Import VST.msl.sepalg_list.

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

  Definition identity_rmap' : R.rmap' := exist valid (fun _: AV.address => R.NO) AV.valid_empty.
  Definition identity_rmap (n:nat) : rmap := R.squash (n, identity_rmap').

  Lemma identity_level : forall n, level (identity_rmap n) = n.
  Proof.
    intro n; unfold identity_rmap.
    rewrite rmap_level_eq. rewrite unsquash_squash. auto.
  Qed.

  Lemma snd_identity_map : forall n, proj1_sig (snd (R.unsquash (identity_rmap n))) = fun _ => R.NO .
    unfold identity_rmap; intros.
    rewrite R.unsquash_squash.
    simpl.
    apply extensionality; intro l.
    unfold compose; simpl; auto.
  Qed.

  Lemma comparable_level : forall phi1 phi2 : rmap ,
         comparable phi1 phi2 -> level phi1 = level phi2.
  Proof.
   intros.
   apply comparable_fashionR.
   trivial.
  Qed.

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

Lemma NO_identity: identity NO.
Proof.
  unfold identity; intros.
  inv H; auto.
Qed.

Lemma PURE_identity: forall k pds, identity (PURE k pds).
Proof.
  unfold identity; intros.
  inv H; auto.
Qed.

Lemma identity_NO:
  forall r, identity  r -> r = NO \/ exists k, exists pds, r = PURE k pds.
Proof.
  destruct r; auto; intros.
  left. symmetry; apply H.
  apply res_join_NO2.
  right. exists k. exists p. trivial.
Qed.

Lemma age1_resource_at_identity:
  forall phi phi' loc, age1 phi = Some phi' ->
               identity (phi@loc) ->
               identity (phi'@loc).
Proof.
  intros.
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
Qed.

Lemma unage1_resource_at_identity:
  forall phi phi' loc, age1 phi = Some phi' ->
               identity (phi'@loc) ->
               identity (phi@loc).
Proof.
  intros.
  generalize (identity_NO _ H0); clear H0; intro.
  unfold resource_at in *. simpl in H.
  rewrite rmap_age1_eq in H.
  revert H H0; case_eq (unsquash phi); simpl; intros.
  destruct n; inv H0.
  rewrite unsquash_squash in H1. destruct r. simpl in *.
  unfold compose in H1; simpl in H1.
  unfold resource_fmap in H1.
  destruct (x loc).
  apply NO_identity.
  destruct H1 as [H1 | [k' [pds' H1]]]; inv H1.
  apply PURE_identity.
Qed.

Lemma necR_resource_at_identity:
  forall phi phi' loc, necR phi phi' ->
         identity (phi@loc) ->
         identity (phi'@loc).
Proof.
  induction 1; auto.
  intro; eapply age1_resource_at_identity; eauto.
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
    (n: nat) (H: resource_fmap (approx n) oo f = f) :
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
      exists phi:rmap, level phi = n /\ resource_at phi = resource_fmap (approx n) oo f.
  Proof.
    intros.
    exists (squash (n, exist valid f H)).
    rewrite rmap_level_eq.
      unfold resource_at; rewrite unsquash_squash; simpl; split; auto.
Qed.

(*
Lemma make_simple_rmap:
    forall n (f: AV.address -> resource) ,
      AV.valid (fun l => res_option (f l)) ->
      (forall l, match f l with YES _ _ (SomeP _ _) => False | _ => True end) ->
      exists phi:rmap, level phi = n /\ resource_at phi = f.
Proof.
  intros; destruct (make_rmap'' n f H) as [phi [? ?]]; exists phi; split; auto.
  rewrite H2.
  extensionality l; unfold compose; simpl;  generalize (H0 l); destruct (f l); auto.
  destruct p0; intros; try contradiction.
Qed.
*)

Lemma approx_oo_approx':
  forall n n', (n' >= n)%nat -> approx n oo approx n' = approx n.
Proof.
unfold compose; intros.
extensionality P.
 apply pred_ext; intros w ?; unfold approx; simpl in *; intuition.
Qed.

Lemma approx_oo_approx: forall n, approx n oo approx n = approx n.
Proof.
intros; apply approx_oo_approx'; omega.
Qed.

Lemma approx_approx' n n' x :
  (n' >= n)%nat -> approx n (approx n' x) = approx n x.
Proof.
  intro H.
  change ((approx n oo approx n') x = approx n x).
  apply equal_f, approx_oo_approx', H.
Qed.

Lemma resources_same_level:
   forall f phi,
     (forall l : AV.address, join_sub (f l) (phi @ l)) ->
        resource_fmap (approx (level phi)) oo f = f.
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
  change (preds_fmap (approx n) (preds_fmap (approx n) p2))
  with ((preds_fmap (approx n) oo preds_fmap (approx n)) p2).
  rewrite preds_fmap_comp.
  rewrite approx_oo_approx; auto.
  change (preds_fmap (approx n) (preds_fmap (approx n) p4))
  with ((preds_fmap (approx n) oo preds_fmap (approx n)) p4).
  rewrite preds_fmap_comp.
  rewrite approx_oo_approx; auto.
  change (preds_fmap (approx n) (preds_fmap (approx n) p1))
  with ((preds_fmap (approx n) oo preds_fmap (approx n)) p1).
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
        resource_fmap (approx (level phi)) oo f = f ->
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
   intro l; spec H3 l.
   destruct (phi @ l); simpl in *.
   apply join_unit1_e in H3. unfold compose. rewrite H3. constructor. apply NO_identity.
   unfold compose at 1. unfold res_option.
   destruct (f l). apply join_unit2_e in H3; [ | apply NO_identity]. rewrite <- H3. constructor.
   destruct (g l). inv H3. inv H3.
   constructor; split; auto.
   inv H3. inv H3. inv H3. unfold compose, res_option. rewrite <- H. constructor.
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
              try change (preds_fmap (approx n) (preds_fmap (approx n) p0)) with
                ((preds_fmap (approx n) oo preds_fmap (approx n)) p0);
              try change (preds_fmap (approx n) (preds_fmap (approx n) p)) with
                ((preds_fmap (approx n) oo preds_fmap (approx n)) p);
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
    replace (rmap_fmap (approx n0) r) with (rmap_fmap (approx n0) r0); auto.
    destruct r; destruct r0.
    simpl in *.
    generalize (valid_res_map (approx n0) x0 v0).
    generalize (valid_res_map (approx n0) x v).
    replace (resource_fmap (approx n0) oo x0)
      with (resource_fmap (approx n0) oo x).
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
    replace (squash ((n - d)%nat, rmap_fmap (approx (S n)) rm))
       with (squash ((n - d)%nat, rm)); auto.
    apply unsquash_inj.
    rewrite unsquash_squash.
    rewrite unsquash_squash.
    replace (rmap_fmap (approx (n - d)) rm)
       with (rmap_fmap (approx (n - d) oo approx (S n)) rm); auto.
    rewrite <- rmap_fmap_comp.
    unfold compose; auto.
    replace (approx (n-d) oo approx (S n)) with (approx (n-d)).
    auto.
    clear.
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
   forall n P r2 r3,
       join (R.YES pfullshare n P) r2 r3 ->
       r2 = NO.
Proof.
  intros.
  simpl in H.
  inv H. trivial.
  pfullshare_join.
Qed.

Lemma YES_not_identity:
  forall sh k Q, ~ identity (YES sh k Q).
Proof.
intros. intro.
rewrite identity_unit_equiv in H.
simpl in * |-.
unfold unit_for in H.
inv H.
apply no_units in H1; auto.
Qed.

Lemma YES_overlap:
forall (phi0 phi1: rmap) loc (sh : pshare) k k' p p',
  joins phi0 phi1 -> phi1@loc = R.YES pfullshare k p ->
               phi0@loc = R.YES sh k' p' -> False.
Proof.
  intros.
  destruct H as [phi3 ?].
  generalize (resource_at_join _ _ _ loc H); intro.
  rewrite H1 in H2.
  rewrite H0 in H2.
  contradiction (YES_not_identity sh k' p').
  apply join_comm in H2. apply YES_join_full in H2. discriminate.
Qed.

Lemma necR_NOx:
   forall phi phi' l, necR phi phi' -> phi@l = NO -> phi'@l = NO.
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
  forall f g pp, preds_fmap f (preds_fmap g pp) = preds_fmap (f oo g) pp.
Proof.
destruct pp; simpl; auto.
Qed.

Lemma resource_fmap_fmap:  forall f g r, resource_fmap f (resource_fmap g r) =
                                                                      resource_fmap (f oo g) r.
Proof.
destruct r; simpl; auto.
rewrite preds_fmap_fmap; auto.
rewrite preds_fmap_fmap; auto.
Qed.

Lemma resource_at_approx:
  forall phi l,
      phi @ l = resource_fmap (approx (level phi)) (phi @ l).
Proof.
intros. rewrite rmap_level_eq. unfold resource_at.
case_eq (unsquash phi); intros.
simpl.
destruct r; simpl in *.
assert (R.valid (resource_fmap (approx n) oo x)).
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
  (resource_fmap (approx n) oo x) (valid_res_map (approx n) x v)) with
(exist (fun m : AV.address -> resource => valid m)
  (resource_fmap (approx n) oo resource_fmap (approx n) oo x)
  (valid_res_map (approx n) (resource_fmap (approx n) oo x) H0)); auto.
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
         phi @ loc = resource_fmap (approx (level phi)) r ->
         phi' @ loc = resource_fmap (approx (level phi')) r.
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
Qed.

Lemma necR_YES:
  forall phi phi' loc sh k pp,
        necR phi phi' ->
         phi @ loc = YES sh k pp ->
         phi' @ loc = YES sh k (preds_fmap (approx (level phi')) pp).
Proof.
intros.
generalize (resource_at_approx phi loc);
pattern (phi @ loc) at 2; rewrite H0; intro.
apply (necR_resource_at _ _ _ _ H H1).
Qed.

Lemma necR_PURE:
  forall phi phi' loc k pp,
        necR phi phi' ->
         phi @ loc = PURE k pp ->
         phi' @ loc = PURE k (preds_fmap (approx (level phi')) pp).
Proof.
  intros.
  generalize (resource_at_approx phi loc);
  pattern (phi @ loc) at 2; rewrite H0; intro.
  apply (necR_resource_at _ _ _ _ H H1).
Qed.

Lemma necR_NO:
   forall phi phi' l, necR phi phi' ->
   (phi@l = NO <-> phi'@l = NO).
Proof.
  intros; split.
  apply necR_NOx; auto.
  intros.
  case_eq (phi @ l); intros; auto.
  destruct p0.
  generalize (necR_YES _ _ _ _ _ _ H H1); rewrite H0; congruence.
  generalize (necR_PURE _ _ _ _ _ H H1); rewrite H0; congruence.
Qed.

Lemma resource_at_empty: forall phi, identity phi -> forall l, (phi @ l = NO \/ exists k, exists pds, phi @ l = PURE k pds).
Proof.
  intros.
  rewrite identity_unit_equiv in H.
  unfold unit_for in H.
  generalize (resource_at_join _ _ _ l H); intro.
  remember (phi @ l) as r.
  destruct r; inv H0; auto.
  apply no_units in H2; contradiction.
  right. exists k. exists p. trivial.
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
  forall f, preds_fmap f NoneP = NoneP.
Proof.
intros.
unfold NoneP.
simpl.
f_equal. extensionality x; destruct  x.
destruct v.
Qed.

Lemma necR_YES':
   forall phi phi' loc sh k,
         necR phi phi' -> (phi@loc = YES sh k NoneP <-> phi'@loc = YES sh k NoneP).
Proof.
intros.
induction H.
rename x into phi; rename y into phi'.
unfold age in H; simpl in H.
(* revert H; case_eq (age1 phi); intros; try discriminate. *)
inv H.
split; intros.
rewrite (necR_YES phi phi' loc sh k NoneP); auto; [ | constructor 1; auto].
f_equal.
apply preds_fmap_NoneP.
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
extensionality x'; destruct x'.
destruct v0.
inv H.
intuition.
intuition.
Qed.

Lemma necR_YES'':
   forall phi phi' loc sh k,
         necR phi phi' ->
    ((exists pp, phi@loc = YES sh k pp) <->
    (exists pp, phi'@loc = YES sh k pp)).
Proof.
intros.
induction H; try solve [intuition].
rename x into phi; rename y into phi'.
revert H; unfold age; case_eq (age1 phi); intros; try discriminate.
inv H0.
simpl in *.
split; intros [pp ?].
econstructor;
apply (necR_YES phi phi' loc sh k pp).
constructor 1; auto. auto.
rename phi' into r.
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
  rewrite (necR_NO _ _ _ H) in H0. congruence.
  destruct p0.
  rewrite (necR_YES phi phi' loc _ _ _ H H0); auto.
  rewrite (necR_PURE phi phi' loc _ _ H H0); auto.
Qed.


Lemma age1_resource_at:
     forall phi phi',
          age1 phi = Some phi' ->
         forall loc r,
          phi @ loc = resource_fmap (approx (level phi)) r ->
          phi' @ loc = resource_fmap (approx (level phi')) r.
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
Qed.


Lemma age1_YES: forall phi phi' l sh k ,
  age1 phi = Some phi' -> (phi @ l = YES sh k NoneP <-> phi' @ l = YES sh k NoneP).
Proof.
intros.
apply necR_YES'.
constructor 1; auto.
Qed.

Lemma empty_NO: forall r, identity r -> r = NO \/ exists k, exists pds, r = PURE k pds.
Proof.
intros.
destruct r; auto.
unfold identity in H.
spec H NO (YES p k p0).
spec H.
apply res_join_NO2.
auto.
right. exists k. exists p. trivial.
Qed.

Lemma YES_join_full':
  forall loc k P m1 m2 m3, join m1 m2 m3 -> m1@loc = YES pfullshare k P ->
                   m3 @ loc = YES pfullshare k P.
Proof.
  intros.
  generalize (resource_at_join _ _ _ loc H); rewrite H0; intro.
  generalize (YES_join_full _ _ _ _ H1); intro. rewrite H2 in H1.
  inv H1.
  trivial.
Qed.


Lemma level_age_fash:
  forall m m': rmap, level m = S (level m') -> exists m1, age m m1. (* /\ comparable m1 m'. *)
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
rewrite H2.
rewrite H; apply resource_at_approx.
inv H1. rewrite <- H0. apply resource_at_approx.
generalize (resource_at_approx phi1 loc); intro.
rewrite H0 in H1. simpl in H1.
simpl. f_equal. injection H1; auto.
inv H1.
generalize (resource_at_approx phi1 loc); intro.
rewrite H0 in H1. simpl in H1.
simpl. f_equal. injection H1; auto.
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
   match r with NO => True | YES _ _ pp => pp=NoneP | PURE _ pp => pp=NoneP end.

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
  symmetry; apply resource_at_approx.
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
generalize (equal_f (rmap_fmap_comp (approx (S n)) (approx n)) r0); intro.
unfold compose at 1 in H0.
rewrite H0.
rewrite approx_oo_approx'; auto.
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
rewrite (age1_resource_at _ _ H0 loc _ (resource_at_approx _ _)).
rewrite (age1_resource_at _ _ H1 loc _ (resource_at_approx _ _)).
rewrite H. rewrite H4; auto.
Qed.

Lemma join_YES_pfullshare1:
    forall pp k p x y, join (YES (mk_lifted Share.top pp) k p) x y -> (NO, YES pfullshare k p) = (x,y).
Proof.
intros. inv H; try pfullshare_join; f_equal; auto.
  f_equal. unfold pfullshare. f_equal. apply proof_irr.
Qed.

Lemma join_YES_pfullshare2:
    forall pp k p x y, join x (YES  (mk_lifted Share.top pp) k p) y -> (NO, YES pfullshare k p) = (x,y).
Proof.
intros. inv H; try pfullshare_join; f_equal; auto.
  f_equal. unfold pfullshare. f_equal. apply proof_irr.
Qed.

Ltac inv H := (apply join_YES_pfullshare1 in H || apply join_YES_pfullshare2 in H || idtac);
                  (inversion H; clear H; subst).

  Definition empty_rmap' : rmap'.
    set (f:= fun _: AV.address => NO).
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
inv H; auto.
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

Definition fixup_trace (trace: AV.address -> option (pshare * AV.kind))
                                    (f: AV.address -> resource) : AV.address -> resource :=
   fun x => match trace x, f x with
                   | None, PURE k pp => PURE k pp
                   | Some(sh,k), PURE _ pp => YES sh k pp
                   | Some (sh,k), YES _ _ pp => YES sh k pp
                   | Some (sh, k), NO => YES sh k NoneP
                   | None, _ => NO
                   end.

Lemma fixup_trace_valid: forall tr f, AV.valid tr -> AV.valid (res_option oo (fixup_trace tr f)).
 Proof. intros.
  replace (res_option oo fixup_trace tr f) with tr. auto.
  extensionality l. unfold compose. unfold fixup_trace.
  destruct (tr l); simpl; auto.
  destruct p. destruct (f l); simpl; auto.
  destruct (f l); reflexivity.
Qed.

Lemma fixup_trace_rmap:
    forall (tr: sig AV.valid) (f: rmap),
        {phi: rmap | level phi = level f /\ resource_at phi = fixup_trace (proj1_sig tr) (resource_at f)}.
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


Ltac crtac :=
 repeat  (solve [constructor; auto] ||
   match goal with
 | H: None = res_option ?A |- _ => destruct A; inv H
 | H: Some _ = res_option ?A |- _ => destruct A; inv H
 | H: join NO _ _ |- _ => inv H
 | H: join _ NO _ |- _ => inv H
 | H: join (YES _ _ _) _ _ |- _ => inv H
 | H: join _ (YES _ _ _) _ |- _ => inv H
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

Lemma Cross_resource: Cross_alg resource.
Proof.
intro; intros.
destruct a as [|a|a].
assert (b=z) by (inv H; auto). subst.
exists (NO,NO,c,d); split; simpl; auto; try constructor; auto.
inv H. inv H0; split; constructor. inv H0; split; constructor.
destruct b as [|b|b].
assert (z=YES a k p) by (inv H; auto). clear H; subst.
exists (c,d,NO,NO); split; simpl; auto.
inv H0; split3; constructor.
assert (Hz: k0=k /\ p0=p) by (inv H; auto). destruct Hz; subst.
destruct c as [|c|c].
assert (z=d) by (inv H0; auto). clear H0; subst.
exists (NO,(YES a k p),NO,(YES b k p)); simpl; split; auto.
constructor.
inv H; split3; constructor; auto.
destruct d as [|d|d].
assert (z=YES c k0 p0) by (inv H0; auto). clear H0; subst.
assert (Hz: k0=k /\ p0=p) by (inv H; auto); destruct Hz; subst.
exists (YES a k p, NO, YES b k p, NO); simpl; split; auto.
constructor. inv H; split3; constructor; auto.
destruct z as [|z|z].  elimtype False; inv H0.
assert (Hx: k=k2 /\ k0=k2 /\ k1=k2 /\ p=p2 /\ p0=p2 /\ p1=p2) by  (inv H0; inv H; auto 50).
destruct Hx as [? [? [? [? [? ?]]]]]; subst.
assert (join c d z) by (inv H0; auto).
assert (join a b z) by (inv H; auto).
clear H H0.
destruct (share_cross_split _ _ _ _ _ H2 H1) as [[[[ac ad] bc] bd] [Ha [Hb [Hc Hd]]]].
destruct (dec_share_identity ac).
apply i in Ha; apply i in Hc. subst.
destruct (dec_share_identity bd).
apply join_comm in Hb; apply join_comm in Hd; apply i0 in Hb; apply i0 in Hd; subst.
apply lifted_eq in Hb. apply lifted_eq in Hd; subst b d.
rename k2 into k; rename p2 into p.
exists (NO, YES a k p, YES c k p, NO); simpl; split; auto. constructor.
split3; constructor; auto.
rename k2 into k; rename p2 into p.
apply nonidentity_nonunit in n.
exists (NO, YES a k p, YES c k p, YES (mk_lifted _ n) k p); simpl; split; auto.
constructor. split3; constructor; auto.
destruct (dec_share_identity ad).
apply join_comm in Ha; apply i in Ha; apply i in Hd; subst bd ac.
clear n.
destruct (dec_share_identity bc).
apply join_comm in Hc; apply i0 in Hb; apply i0 in Hc.  apply lifted_eq in Hb; apply lifted_eq in Hc; subst d c.
rename k2 into k; rename p2 into p.
exists (YES a k p, NO, NO, YES b k p); simpl; split; auto.
constructor. split3; constructor; auto.
rename k2 into k; rename p2 into p.
exists (YES a k p, NO, YES (mk_lifted _ (nonidentity_nonunit n)) k p, YES d k p); simpl; split; auto.
constructor. split3; constructor; auto.
destruct (dec_share_identity bc).
apply join_comm in Hc; apply i in Hb; apply i in Hc.  subst ac bd.
rename k2 into k; rename p2 into p.
exists (YES c k p, YES (mk_lifted _ (nonidentity_nonunit n0)) k p, NO, YES b k p); simpl; split; auto.
constructor. auto. split3; constructor; auto.
destruct (dec_share_identity bd).
apply join_comm in Hb; apply join_comm in Hd;
 apply i in Hb; apply i in Hd. subst bc ad.
rename k2 into k; rename p2 into p.
exists (YES (mk_lifted _ (nonidentity_nonunit n)) k p,  YES d k p, YES b k p, NO); split; simpl; auto.
constructor; auto. split3; constructor; auto.
rename k2 into k; rename p2 into p.
exists (YES (mk_lifted _ (nonidentity_nonunit n)) k p, YES (mk_lifted _ (nonidentity_nonunit n0)) k p,
       YES (mk_lifted _ (nonidentity_nonunit n1)) k p,  YES (mk_lifted _ (nonidentity_nonunit n2)) k p); split; simpl; auto.
constructor; auto.  split3; constructor; auto.
elimtype False; inv H0.
elimtype False; inv H0.
elimtype False; inv H0; inv H.
elimtype False; inv H.
exists (PURE a p, PURE a p, PURE a p, PURE a p).
inv H. inv H0.
repeat split; constructor; auto.
Qed.

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
  destruct (fixup_trace_rmap Vac z) as [Mac [? ?]].
  destruct (fixup_trace_rmap Vad z) as [Mad [? ?]].
  destruct (fixup_trace_rmap Vbc z) as [Mbc [? ?]].
  destruct (fixup_trace_rmap Vbd z) as [Mbd [? ?]].
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
  unfold fixup_trace; simpl in *.
  forget (a @ l) as al; forget (b @ l) as bl; forget (c @ l ) as cl;
  forget (d @ l) as dl; forget (z @ l) as zl;
   clear - Va Vb Vc Vd H H0.
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
     destruct H3; constructor; simpl; auto. (* this line for compatibility with Coq 8.3 *)
   destruct (X a b c d e H H0) as [[[[ac ad] bc] bd] [? [? [? ?]]]].
   exists (exist AV.valid ac (V _), exist AV.valid ad (V _),
              exist AV.valid bc (V _), exist AV.valid bd (V _)).
   split; [ |split3]; simpl; auto.
Qed.

Lemma identity_resource: forall r: resource, identity r <->
    match r with YES _ _ _ => False | _ => True end.
Proof.
 intros. destruct r; intuition.
 apply NO_identity.
 specialize (H NO (YES p k p0)).
 spec H. constructor. inv H.
 intros  ? ? ?. inv H0. auto.
Qed.

Lemma resource_at_core_identity:  forall m i, identity (core m @ i).
Proof.
  intros.
  generalize (core_duplicable m); intro Hdup. apply (resource_at_join _ _ _ i) in Hdup.
  apply identity_resource.
  case_eq (core m @ i); intros; auto.
  rewrite H in Hdup. inv Hdup.
   apply pshare_nonunit in H1. auto.
Qed.

Lemma YES_inj: forall sh k pp sh' k' pp',
           YES sh k pp = YES sh' k' pp' ->
          sh=sh' /\ k=k' /\ pp=pp'.
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

End Rmaps_Lemmas.
