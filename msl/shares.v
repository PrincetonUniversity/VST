(*
 * Copyright (c) 2009-2016, Andrew Appel, Robert Dockins,
    Aquinas Hobor and Le Xuan Bach
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.sepalg.
Require Import VST.msl.psepalg.
Require Import VST.msl.sepalg_generators.
Require Import VST.msl.boolean_alg.
Require Import VST.msl.eq_dec.

Require VST.msl.tree_shares.

Module Share : SHARE_MODEL := tree_shares.Share.
Import Share.

Definition share : Type := Share.t.

Instance pa_share : Perm_alg share := Share.pa.
Instance sa_share : Sep_alg share := Share.sa.
Instance ca_share : Canc_alg share := Share.ca.
Definition emptyshare : share := Share.bot.
Definition fullshare : share := Share.top.

Theorem leq_join_sub : forall s1 s2:Share.t,
  s1 <= s2 <-> join_sub s1 s2.
Proof.
  split; intros.
  pose (s' := glb s2 (comp s1)).
  exists s'.
  simpl; split.
  subst s'.
  rewrite glb_commute.
  rewrite glb_assoc.
  rewrite (glb_commute (comp s1) s1).
  rewrite comp2.
  apply glb_bot.
  subst s'.
  rewrite distrib2.
  rewrite comp1.
  rewrite glb_top.
  rewrite <- ord_spec2; auto.

  destruct H as [s' H].
  destruct H.
  rewrite ord_spec2.
  rewrite <- H0.
  rewrite <- lub_assoc.
  rewrite lub_idem; auto.
Qed.

Lemma top_correct' : forall x:t, join_sub x top.
Proof.
  intros; rewrite <- leq_join_sub; auto with ba.
Qed.

Lemma bot_identity : identity bot.
Proof.
  hnf; intros.
  destruct H.
  rewrite lub_commute in H0.
  rewrite lub_bot in H0.
  auto.
Qed.

Hint Resolve bot_identity.

Lemma identity_share_bot : forall s,
  identity s -> s = bot.
Proof.
  intros.
  apply identities_unique; auto.
  exists s.
  apply join_comm.

  destruct (top_correct' s).
  assert (x = top).
  apply H; auto.
  subst x; auto.
  destruct (top_correct' bot).
  assert (x = top).
  apply bot_identity; auto.
  subst x; auto.
  apply join_comm in H1.
  destruct (join_assoc H0 H1); intuition.
  assert (x = top).
  apply H; auto.
  subst x.
  replace bot with s.
  rewrite identity_unit_equiv in H.
  trivial.
  eapply joins_units_eq; try apply H0. exists top; eauto.
  simpl. split. apply glb_bot. apply lub_bot.
Qed.

Lemma factoryOverlap' : forall f1 f2 n1 n2,
  isTokenFactory f1 n1 -> isTokenFactory f2 n2 -> joins f1 f2 -> False.
Proof.
  intros.
  destruct H1.
  destruct H1.
  apply (factoryOverlap f1 f2 n1 n2 H H0 H1).
Qed.

Lemma identityToken' : forall x, isToken x 0 <-> identity x.
Proof.
  intro x; destruct (identityToken x); split; intros.
  hnf; intros.
  rewrite H in H2; auto.
  apply H0.
  apply identity_share_bot; auto.
Qed.

Lemma nonidentityToken' : forall x n, (n > 0)%nat -> isToken x n -> nonidentity x.
Proof.
  intros.
  generalize (nonidentityToken x n H H0).
  repeat intro.
  apply H1.
  apply identity_share_bot; auto.
Qed.

Lemma nonidentityFactory' : forall x n, isTokenFactory x n -> nonidentity x.
Proof.
  intros.
  generalize (nonidentityFactory x n H); repeat intro.
  apply H0.
  apply identity_share_bot; auto.
Qed.

Lemma split_join : forall x1 x2 x,
  split x = (x1,x2) -> join x1 x2 x.
Proof.
  intros; split.
  apply split_disjoint with x; auto.
  apply split_together; auto.
Qed.

Lemma split_nontrivial' : forall x1 x2 x,
  split x = (x1, x2) ->
    (identity x1 \/ identity x2) ->
    identity x.
Proof.
  intros.
  rewrite (split_nontrivial x1 x2 x H).
  apply bot_identity.
  destruct H0.
  left; apply identity_share_bot; auto.
  right; apply identity_share_bot; auto.
Qed.

Lemma rel_leq : forall a x, join_sub (rel a x) a.
Proof.
  intros.
  rewrite <- leq_join_sub.

  intros.
  rewrite ord_spec1.
  pattern a at 3.
  replace a with (rel a top).
  rewrite <- rel_preserves_glb.
  rewrite glb_top.
  auto.
  apply rel_top1.
Qed.

Lemma rel_join : forall a x y z,
  join x y z ->
  join (rel a x) (rel a y) (rel a z).
Proof.
  simpl; intuition. inv H.
  constructor.
  rewrite <- rel_preserves_glb.
  replace bot with (rel a bot).
  replace (glb x y) with bot; auto.
  apply rel_bot1.
  rewrite <- rel_preserves_lub. auto.
Qed.

Lemma rel_join2 : forall a x y s,
  nonidentity a ->
  join (rel a x) (rel a y) s ->
  exists z, s = rel a z /\ join x y z.
Proof.
  simpl; intros.
  destruct H0.
  exists (lub x y).
  split.
  rewrite <- H1.
  symmetry.
  apply rel_preserves_lub.
  split; auto.
  rewrite <- rel_preserves_glb in H0.
  replace bot with (rel a bot) in H0.
  apply rel_inj_l with a; auto.
  hnf; intros; apply H.
  subst a; apply bot_identity.
  apply rel_bot1.
Qed.

Lemma rel_nontrivial : forall a x,
  identity (rel a x) ->
  (identity a \/ identity x).
Proof.
  intros a x H.
  destruct (eq_dec a bot); auto.
  subst a.
  left. apply bot_identity.

  right.
  assert (rel a x = bot).
  apply identity_share_bot; auto.
  assert (x = bot).
  replace bot with (rel a bot) in H0.
  apply rel_inj_l with a; auto.
  apply rel_bot1.
  subst x; apply bot_identity.
Qed.

Instance share_cross_split : Cross_alg t.
Proof.
  hnf; simpl; intuition. destruct H as [H1 H2]. destruct H0 as [H H3].
  exists (glb a c, glb a d, glb b c, glb b d); intuition; constructor.
  rewrite (glb_commute a d).
  rewrite glb_assoc.
  rewrite <- (glb_assoc c d a).
  rewrite H.
  rewrite (glb_commute bot a).
  rewrite glb_bot.
  rewrite glb_bot.
  auto.
  rewrite <- distrib1;  rewrite H3; rewrite <- H2; auto with ba.
  rewrite (glb_commute b d).
  rewrite glb_assoc.
  rewrite <- (glb_assoc c d b).
  rewrite H.
  rewrite (glb_commute bot b).
  rewrite glb_bot.
  rewrite glb_bot.
  auto.
  rewrite <- distrib1;  rewrite H3; rewrite <- H2; auto with ba.
  rewrite (glb_commute a c).
  rewrite glb_assoc.
  rewrite <- (glb_assoc a b c).
  rewrite H1.
  rewrite (glb_commute bot c).
  rewrite glb_bot.
  rewrite glb_bot.
  auto.
  rewrite (glb_commute a c).
  rewrite (glb_commute b c).
  rewrite <- distrib1; rewrite H2; rewrite <- H3; auto with ba.
  rewrite (glb_commute a d).
  rewrite glb_assoc.
  rewrite <- (glb_assoc a b d).
  rewrite H1.
  rewrite (glb_commute bot d).
  rewrite glb_bot.
  rewrite glb_bot.
  auto.
  rewrite (glb_commute a d).
  rewrite (glb_commute b d).
  rewrite <- distrib1; rewrite H2; rewrite <- H3; auto with ba.
Qed.

Lemma bot_correct' : forall x, join_sub bot x.
Proof.
  intros s.
  destruct (top_correct' s).
  exists s.
  destruct (top_correct' bot).
  assert (x0 = top).
  apply bot_identity; auto.
  subst x0.
  apply join_comm in H0.
  destruct (join_assoc H H0); intuition.
  apply join_comm in H2.
  destruct (join_assoc H1 H2); intuition.
  assert (s = x1).
  apply bot_identity; auto.
  subst x1; auto.
Qed.

Lemma top_share_nonidentity : nonidentity top.
Proof.
  hnf; intros.
  assert (top = bot).
  apply identity_share_bot; auto.
  apply nontrivial; auto.
Qed.

Lemma top_share_nonunit: nonunit top.
Proof.
  repeat intro. unfold unit_for in H.
  destruct H. rewrite glb_commute in H. rewrite glb_top in H. subst.
  rewrite lub_bot in H0. apply nontrivial; auto.
Qed.

Lemma bot_join_eq : forall x, join bot x x.
Proof.
  intros.
  destruct (join_ex_identities x); intuition.
  destruct H0.
  generalize (H _ _ H0).
  intros; subst; auto.
  replace bot with x0; auto.
  apply identity_share_bot; auto.
Qed.

Lemma join_bot_eq : forall x, join x bot x.
Proof.
  intros.
  apply join_comm, bot_join_eq.
Qed.

Lemma bot_joins : forall x, joins bot x.
Proof.
  intro x; exists x; apply bot_join_eq.
Qed.

Lemma dec_share_identity : forall x:t, { identity x } + { ~identity x }.
Proof.
  intro x.
  destruct (eq_dec x bot); subst.
  left; apply bot_identity.
  right; intro; elim n.
  apply identity_share_bot; auto.
Qed.

Lemma dec_share_nonunit : forall x:t, { nonunit x } + { ~ nonunit x }.
Proof.
  intro x.
  destruct (dec_share_identity x) as [H | H]; [right | left].
  + intro; revert H. apply nonunit_nonidentity; auto.
  + apply nonidentity_nonunit; auto.
Qed.

Lemma fullshare_full : full fullshare.
Proof.
  unfold full.
  intros.
  generalize (Share.top_correct);intros.
  destruct H as [sigma'' ?].
  specialize (H0 sigma'').
  rewrite leq_join_sub in H0.
  destruct H0.
  destruct (join_assoc H H0) as [s [H1 H2]].
  apply join_comm in H2. apply unit_identity in H2.
  eapply split_identity; eauto.
Qed.

Lemma join_sub_fullshare : forall sh,
  join_sub fullshare sh -> sh = fullshare.
Proof.
  intros.
  generalize fullshare_full; intro.
  apply full_maximal in H0.
  specialize ( H0 sh H).
  auto.
Qed.

Lemma dec_share_full : forall (sh : Share.t),
  {full sh} + {~full sh}.
Proof with auto.
  intro sh.
  destruct (eq_dec sh top); subst.
  left. apply fullshare_full.
  right. intro. apply n.
  generalize (Share.top_correct sh);intro.
  apply leq_join_sub in H0.
  destruct H0.
  specialize ( H x). spec H. exists top...
  specialize ( H sh top (join_comm H0))...
Qed.

Lemma rel_congruence : forall a x1 x2,
  join_sub x1 x2 ->
  join_sub (rel a x1) (rel a x2).
Proof.
  intros.
  destruct H.
  exists (rel a x).
  apply rel_join; auto.
Qed.

Lemma share_split_injective:
  forall sh1 sh2, Share.split sh1 = Share.split sh2 -> sh1=sh2.
Proof.
  intros sh1 sh2;
    case_eq (Share.split sh1); case_eq (Share.split sh2); intros.
  generalize (split_join _ _ _ H); intro.
  generalize (split_join _ _ _ H0); intro.
  inv H1.
  eapply join_eq; eauto.
Qed.

Lemma share_joins_constructive:
  forall sh1 sh2 : t , joins sh1 sh2 ->  {sh3 | join sh1 sh2 sh3}.
Proof.
  intros.
  exists (lub sh1 sh2).
  destruct H.
  destruct H; split; auto.
Qed.

Lemma share_join_sub_constructive:
  forall sh1 sh3 : t , join_sub sh1 sh3 ->  {sh2 | join sh1 sh2 sh3}.
Proof.
  intros.
  exists (glb sh3 (comp sh1)).
  destruct H.
  destruct H.
  split.
  rewrite (glb_commute sh3 (comp sh1)).
  rewrite <- glb_assoc.
  rewrite comp2.
  rewrite glb_commute.
  rewrite glb_bot.
  auto.
  rewrite distrib2.
  rewrite comp1.
  rewrite glb_top.
  rewrite <- ord_spec2.
  rewrite <- H0.
  apply lub_upper1.
Qed.

Lemma triple_join_exists_share : Trip_alg t.
Proof.
  repeat intro.
  destruct H; destruct H0; destruct H1.
  exists (lub a (lub b c)).
  split.
  rewrite <- H2.
  rewrite glb_commute.
  rewrite distrib1.
  rewrite glb_commute.
  rewrite H1.
  rewrite glb_commute.
  rewrite H0.
  rewrite lub_bot; auto.
  rewrite <- H2.
  apply lub_assoc.
Qed.

Lemma nonemp_split_neq1: forall sh sh1 sh2, nonidentity sh -> split sh = (sh1, sh2) -> sh1 <> sh.
Proof with auto.
  intros until sh2; intros H H0.
  destruct (dec_share_identity sh2).
  generalize (split_nontrivial' _ _ _ H0); intro.
  spec H1...
  destruct (eq_dec sh1 sh)...
  subst sh1.
  generalize (split_join _ _ _ H0); intro.
  apply join_comm in H1.
  apply unit_identity in H1...
Qed.

Lemma nonemp_split_neq2: forall sh sh1 sh2, nonidentity sh -> split sh = (sh1, sh2) -> sh2 <> sh.
Proof with auto.
  intros until sh2; intros H H0.
  destruct (dec_share_identity sh1).
  generalize (split_nontrivial' _ _ _ H0); intro.
  spec H1...
  destruct (eq_dec sh2 sh)...
  subst sh2.
  generalize (split_join _ _ _ H0); intro.
  apply unit_identity in H1...
Qed.

Lemma bot_unit: forall sh,
  join emptyshare sh sh.
Proof.
  intro sh.
  generalize (bot_joins sh); generalize bot_identity; intros.
  destruct H0.
  specialize ( H sh x H0). subst.
  trivial.
Qed.

Hint Resolve bot_unit.

Lemma join_bot: join emptyshare emptyshare emptyshare.
Proof.
  apply bot_unit.
Qed.


Lemma share_rel_nonidentity:
  forall {sh1 sh2}, nonidentity sh1 -> nonidentity sh2 -> nonidentity (Share.rel sh1 sh2).
Proof.
intros.
unfold nonidentity in *.
generalize (rel_nontrivial sh1 sh2); intro. intuition.
Qed.

Lemma share_rel_nonunit: forall {sh1 sh2: Share.t},
       nonunit sh1 -> nonunit sh2 -> nonunit (Share.rel sh1 sh2).
Proof. intros. apply nonidentity_nonunit. apply share_rel_nonidentity.
intro. apply (@identity_unit _ _ _ sh1 Share.bot) in H1. apply H in H1; auto.
apply joins_comm. apply bot_joins.
intro. apply (@identity_unit _ _ _ sh2 Share.bot) in H1. apply H0 in H1; auto.
apply joins_comm. apply bot_joins.
Qed.


Lemma decompose_bijection: forall sh1 sh2,
 sh1 = sh2 <-> decompose sh1 = decompose sh2.
Proof.
 intros.
 split;intros. subst;trivial.
 generalize (recompose_decompose sh1);intro.
 generalize (recompose_decompose sh2);intro.
 congruence.
Qed.

Module ShareMap.
Section SM.
  Variable A:Type.
  Variable EqDec_A : EqDec A.

  Variable B:Type.
  Variable JB: Join B.
  Variable paB : Perm_alg B.
  Variable saB : Sep_alg B.

  Definition map := fpm A (lifted Share.Join_ba * B).
  Instance Join_map : Join map := Join_fpm _.
  Instance pa_map : Perm_alg map := Perm_fpm _ _.
  Instance sa_map : Sep_alg map := Sep_fpm _ _.
  Instance ca_map {CA: Canc_alg B} : Canc_alg map := Canc_fpm _.
  Instance da_map {DA: Disj_alg B} : Disj_alg map := @Disj_fpm _ _ _ _ _ _.

  Definition map_share (a:A) (m:map) : share :=
    match lookup_fpm m a with
    | Some (sh,_) => lifted_obj sh
    | None => Share.bot
    end.

  Definition map_val (a:A) (m:map) : option B :=
    match lookup_fpm m a with
    | Some (_,b) => Some b
    | None => None
    end.

  Definition empty_map : map := empty_fpm _ _.

  Definition map_upd (a:A) (b:B) (m:map) : option map :=
    match lookup_fpm m a with
    | Some (sh,_) =>
        if eq_dec (lifted_obj sh) fullshare
           then Some (insert_fpm _ a (sh,b) m)
           else None
    | None => None
    end.

Lemma join_lifted {t} {J: Join t}:
    forall (a b c: lifted J), join a b c -> join (lifted_obj a) (lifted_obj b) (lifted_obj c).
Proof. destruct a; destruct b; destruct c; simpl; intros. apply H.
Qed.

  Lemma map_join_char : forall m1 m2 m3,
    join m1 m2 m3 <->
    (forall a,
       join (map_share a m1) (map_share a m2) (map_share a m3) /\
       join (map_val a m1) (map_val a m2) (map_val a m3)).
  Proof with auto.
    split; intros.
    hnf in H. specialize ( H a).
    unfold map_val, map_share, lookup_fpm.
    destruct (proj1_sig m1 a) as [[sh1 a1] | ];
    destruct (proj1_sig m2 a) as [[sh2 a2] | ];
    destruct (proj1_sig m3 a) as [[sh3 a3] | ]; inv H; try solve [inv H0]; simpl; auto.
    destruct H3; simpl in *; auto.
    split. apply join_lifted; auto. constructor; auto.
    split; apply join_unit2; auto.
    split; apply join_unit1; auto.
    split; apply join_unit1; auto.
    split; apply join_unit1; auto.

    intro a. specialize ( H a). destruct H.
        unfold map_val, map_share, lookup_fpm in *.
    destruct (proj1_sig m1 a) as [[sh1 a1] | ];
    destruct (proj1_sig m2 a) as [[sh2 a2] | ];
    destruct (proj1_sig m3 a) as [[sh3 a3] | ]; inv H0; try solve [inv H1]; auto.
    constructor. split; auto.
    apply join_unit2_e in H; auto. apply join_unit2; auto.
    repeat f_equal. destruct sh1; destruct sh3; simpl in *; subst.
    rewrite (proof_irr n n0); auto.
    apply join_unit1_e in H; auto. apply join_unit1; auto.
    repeat f_equal. destruct sh2; destruct sh3; simpl in *; subst.
    rewrite (proof_irr n n0); auto.
    constructor. constructor.
 Qed.

  Lemma empty_map_identity {CAB: Disj_alg B}: identity empty_map.
  Proof.
    rewrite identity_unit_equiv.
    intro x. simpl. auto. constructor.
  Qed.

  Lemma map_identity_unique {CAB: Disj_alg B}: forall m1 m2:map,
    identity m1 -> identity m2 -> m1 = m2.
  Proof.
    intros.
    destruct m1; destruct m2; simpl in *.
    cut (x = x0). intros. subst x0.
    replace f0 with f; auto.
    apply proof_irr; auto.
    rewrite identity_unit_equiv in H, H0.
    extensionality a.
    specialize ( H a); specialize ( H0 a).
    apply lower_inv in H.
    apply lower_inv in H0.
    destruct H; destruct H0; simpl in *.
    intuition; congruence.
    destruct s0 as [? [? [? [? [? [? ?]]]]]].
    rewrite H in H1. inv H1. rewrite H0 in H; inv H.
    destruct x3. destruct H2. simpl in *. apply no_units in H. contradiction.
    destruct s as [? [? [? [? [? [? ?]]]]]].
    rewrite H in H0; inv H0. rewrite H1 in H; inv H.
    destruct x2. destruct H2. simpl in *. apply no_units in H. contradiction.
    destruct s as [? [? [? [? [? [? ?]]]]]].
    rewrite H in H0; inv H0. rewrite H1 in H; inv H.
    destruct x2. destruct H2. simpl in *. apply no_units in H. contradiction.
  Qed.

  Lemma map_identity_is_empty  {CAB: Disj_alg B} : forall m,
    identity m -> m = empty_map.
  Proof.
    intros; apply map_identity_unique; auto.
    apply empty_map_identity.
  Qed.

  Lemma empty_map_join {CAB: Disj_alg B} : forall m,
    join empty_map m m.
  Proof.
    intro m. destruct (join_ex_units m).
    replace empty_map with x; auto.
    apply map_identity_is_empty.
    eapply unit_identity; eauto.
  Qed.

  Lemma map_val_bot  : forall a m,
    map_val a m = None <-> map_share a m = Share.bot.
  Proof.
    do 2 intro.
    unfold map_val, map_share, lookup_fpm.
    destruct (proj1_sig m a); intuition.
    disc.
    contradiction (no_units a0 a0). destruct a0. simpl in *. subst.
    contradiction (n bot). auto.
  Qed.

  Lemma map_upd_success : forall a v m,
    map_share a m = Share.top ->
    exists m', map_upd a v m = Some m'.
  Proof.
    intros.
    unfold map_upd. simpl.
    unfold map_share, lookup_fpm in*.
    destruct (proj1_sig  m a).
    destruct p.
    rewrite H.
    unfold fullshare.
    destruct (eq_dec top top).
    eauto.
    elim n; auto.
    elim Share.nontrivial; auto.
  Qed.

  Lemma map_set_share1 : forall a v m m',
    map_upd a v m = Some m' ->
    map_share a m = Share.top.
  Proof.
    unfold map_upd, map_share.
    intros.
    destruct (lookup_fpm m a); disc.
    destruct p.
    destruct (eq_dec (lifted_obj l) fullshare); disc; auto.
  Qed.

  Lemma map_set_share2 : forall a v m m',
    map_upd a v m = Some m' ->
    map_share a m' = Share.top.
  Proof.
    unfold map_upd, map_share.
    intros. destruct (lookup_fpm m a); disc.
    destruct p. destruct (eq_dec (lifted_obj l) fullshare); disc.
    inv H.
    rewrite fpm_gss. auto.
  Qed.

  Lemma map_set_share3 : forall a v m m',
    map_upd a v m = Some m' ->
    forall a',
      map_share a' m = map_share a' m'.
  Proof.
    unfold map_upd, map_share.
    intros a v m m'.
    case_eq (lookup_fpm m a); intros; disc.
    destruct p.
    destruct (eq_dec (lifted_obj l) fullshare); disc.
    inv H0.
    destruct (eq_dec a a'). subst.
    rewrite H.
    rewrite fpm_gss. auto.
    rewrite fpm_gso; auto.
  Qed.

  Lemma map_gss_val: forall a v m m',
        map_upd a v m = Some m' ->
        map_val a m' = Some v.
  Proof.
    unfold map_upd, map_val.
    intros a v m m'.
    case_eq (lookup_fpm m a); intros; disc.
    destruct p.
    destruct (eq_dec (lifted_obj l) fullshare); disc.
    inv H0.
    rewrite fpm_gss. auto.
  Qed.

  Lemma map_gso_val : forall i j v m m',
       i <> j ->
       map_upd j v m = Some m' ->
       map_val i m = map_val i m'.
  Proof.
    unfold map_upd, map_val.
    intros i j v m m'.
    case_eq (lookup_fpm m j); intros; disc.
    destruct p.
    destruct (eq_dec (lifted_obj l) fullshare); disc.
    inv H1.
    rewrite fpm_gso; auto.
  Qed.

  Lemma map_gso_share : forall i j v m m',
    i <> j ->
    map_upd j v m = Some m' ->
    map_share i m = map_share i m'.
  Proof.
    unfold map_upd, map_share.
    intros i j v m m'.
    case_eq (lookup_fpm m j); intros; disc.
    destruct p.
    destruct (eq_dec (lifted_obj l) fullshare); disc.
    inv H1.
    rewrite fpm_gso; auto.
  Qed.

  Lemma map_upd_join : forall m1 m2 m3 a v m1',
    map_upd a v m1 = Some m1' ->
    join m1 m2 m3 ->
    exists m3', map_upd a v m3 = Some m3' /\
      join m1' m2 m3'.
  Proof.
    intros.
    rewrite map_join_char in H0.
    destruct (H0 a).
    generalize H; intros.
    apply map_set_share1 in H.
    rewrite H in H1.
    destruct H1.
    rewrite glb_commute in H1.
    rewrite glb_top in H1.
    rewrite H1 in H4.
    rewrite lub_bot in H4.
    symmetry in H4.
    destruct (map_upd_success a v _ H4).
    exists x; split; auto.
    clear H2.
    rewrite map_join_char.
    intro a'.
    destruct (eq_dec a a').
    subst a'. split.
    apply map_set_share2 in H3. rewrite H3.
    apply map_set_share2 in H5. rewrite H5.
    rewrite H1. apply join_unit2; auto.
    erewrite map_gss_val; eauto.
    apply map_val_bot in H1. rewrite H1.
    erewrite map_gss_val; eauto. constructor.
    destruct (H0 a'). split.
    rewrite <- (map_gso_share a' a v m1 m1'); auto.
    rewrite <- (map_gso_share a' a v m3 x); auto.
    rewrite <- (map_gso_val a' a v m1 m1'); auto.
    rewrite <- (map_gso_val a' a v m3 x); auto.
  Qed.

  Definition build_map (l:list (A * B)) : map :=
     fold_right
      (fun (ab:A * B) m =>
        insert_fpm EqDec_A
           (fst ab)
           (mk_lifted fullshare top_share_nonunit,snd ab) m)
      empty_map l.

  Lemma build_map_results : forall (l:list (A*B)) a b,
    NoDup (List.map (@fst _ _) l) ->
    (In (a,b) l <->
    (map_val a (build_map l) = Some b /\
     map_share a (build_map l) = Share.top)).
  Proof.
    induction l; simpl.
    split; intros. elim H0.
    destruct H0.
    unfold build_map in H0. simpl in H0.
    unfold map_val in H0.
    simpl in H0. discriminate.
    intros. split; intros.
    destruct H0; subst.
    unfold build_map.
    simpl fold_right.
    split.
    unfold map_val.
    rewrite fpm_gss. simpl; auto.
    unfold map_share.
    rewrite fpm_gss. simpl; auto.
    generalize H0; intro H1.
    rewrite IHl in H0.
    inv H.
    assert (fst a <> a0).
    intro. subst a0.
    elim H4.
    clear -H1. induction l; simpl in *; intuition; subst; auto.
    destruct H0.
    unfold build_map. simpl fold_right.
    split.
    unfold map_val.
    rewrite fpm_gso; auto.
    unfold map_share.
    rewrite fpm_gso; auto.
    inv H. auto.
    inv H.
    destruct H0.
    destruct a.
    destruct (eq_dec a a0).
    subst a0.
    left. f_equal.
    unfold build_map in H.
    unfold map_val in H.
    simpl fold_right in H.
    rewrite fpm_gss in H.
    inv H. auto.
    right.
    rewrite IHl; auto.
    split.
    revert H.
    unfold build_map, map_val.
    simpl fold_right.
    rewrite fpm_gso; auto.
    revert H0.
    unfold build_map, map_share.
    simpl fold_right.
    rewrite fpm_gso; auto.
  Qed.

  Lemma build_map_join : forall (l1 l2:list (A * B)),
    NoDup (List.map (@fst _ _) (l1++l2)) ->
    join  (build_map l1)
          (build_map l2)
          (build_map (l1++l2)).
  Proof.
    induction l1; intros.
    simpl app.
    unfold build_map at 1.
    simpl fold_right.
    apply empty_fpm_join; auto with typeclass_instances.
    inv H.
    simpl app.
    unfold build_map.
    simpl fold_right.
    apply insert_fpm_join. auto with typeclass_instances.
    2: apply (IHl1 l2); auto.
    assert (~In (fst a) (List.map (@fst _ _) l2)).
    intro.
    elim H2.
    rewrite map_app.
    apply in_or_app.
    auto.
    clear -H.
    induction l2; simpl in *.
    auto.
    rewrite fpm_gso; auto.
  Qed.

End SM.
End ShareMap.

