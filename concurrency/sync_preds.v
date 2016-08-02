Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import msl.Coqlib2.
Require Import msl.eq_dec.
Require Import msl.seplog.
Require Import veric.initial_world.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.semax_prog.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.initial_world.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.semax_ext.
Require Import veric.semax_ext_oracle.
Require Import veric.res_predicates.
Require Import veric.mem_lessdef.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.event_semantics.
Require Import concurrency.coqlib5.
Require Import concurrency.semax_conc.
Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.
Require Import concurrency.addressFiniteMap.
Require Import concurrency.permissions.
Require Import concurrency.JuicyMachineModule.

Definition islock_pred R r := exists sh sh' z, r = YES sh sh' (LK z) (SomeP nil (fun _ => R)).

Lemma islock_pred_join_sub {r1 r2 R} : join_sub r1 r2 -> islock_pred R r1  -> islock_pred R r2.
Proof.
  intros [r0 J] [x [sh' [z ->]]].
  inversion J; subst; eexists; eauto.
Qed.

Definition LKspec_ext (R: pred rmap) : spec :=
   fun (rsh sh: Share.t) (l: AV.address)  =>
    allp (jam (adr_range_dec l lock_size)
                         (jam (eq_dec l) 
                            (yesat (SomeP nil (fun _ => R)) (LK lock_size) rsh sh)
                            (CTat l rsh sh))
                         (fun _ => TT)).

Definition LK_at R sh :=
  LKspec_ext R (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh).

Lemma resource_decay_LK {b phi phi' loc rsh sh n pp} :
  resource_decay b phi phi' ->
  phi @ loc = YES rsh sh (LK n) pp ->
  phi' @ loc = YES rsh sh (LK n) (preds_fmap (approx (level phi')) pp).
Proof.
  intros [L R] E.
  specialize (R loc).
  rewrite E in *.
  destruct R as [N [R|[R|[R|R]]]].
  - rewrite <- R.
    reflexivity.
  - destruct R as [sh' [v [v' [R H]]]]. simpl in R. congruence.
  - destruct R as [v [v' R]]. specialize (N ltac:(auto)). congruence.
  - destruct R as [v [pp' [R H]]]. congruence.
Qed.

Lemma resource_decay_CT {b phi phi' loc rsh sh n} :
  resource_decay b phi phi' ->
  phi @ loc = YES rsh sh (CT n) NoneP ->
  phi' @ loc = YES rsh sh (CT n) NoneP.
Proof.
  intros [L R] E.
  specialize (R loc).
  rewrite E in *.
  destruct R as [N [R|[R|[R|R]]]].
  - rewrite <- R.
    unfold resource_fmap in *; f_equal.
    apply preds_fmap_NoneP.
  - destruct R as [sh' [v [v' [R H]]]]. simpl in R. congruence.
  - destruct R as [v [v' R]]. specialize (N ltac:(auto)). congruence.
  - destruct R as [v [pp' [R H]]]. congruence.
Qed.

Lemma resource_decay_LK_inv {b phi phi' loc rsh sh n pp'} :
  resource_decay b phi phi' ->
  phi' @ loc = YES rsh sh (LK n) pp' ->
  exists pp,
    pp' = preds_fmap (approx (level phi')) pp /\
    phi @ loc = YES rsh sh (LK n) pp.
Proof.
  intros [L R] E.
  specialize (R loc).
  rewrite E in *.
  destruct R as [N [R|[R|[R|R]]]].
  - destruct (phi @ loc); simpl in R; try discriminate.
    eexists.
    injection R. intros; subst.
    split; reflexivity.
  - destruct R as [sh' [v [v' [R H]]]]; congruence.
  - destruct R as [v [v' R]]; congruence.
  - destruct R as [v [pp [R H]]]; congruence.
Qed.

Lemma resource_decay_identity {b phi phi' loc} :
  resource_decay b phi phi' ->
  (fst loc < b)%positive ->
  identity (phi @ loc) ->
  identity (phi' @ loc).
Proof.
  intros [lev RD] LT ID; specialize (RD loc).
  destruct RD as [N [RD|[RD|[RD|RD]]]].
  destruct (phi @ loc) as [t | t p k p0 | k p]; simpl in RD; try rewrite <- RD.
  - auto.
  - apply YES_not_identity in ID. tauto.
  - apply PURE_identity.
  - destruct RD as (? & sh & _ & E & _).
    destruct (phi @ loc); simpl in E; try discriminate.
    apply YES_not_identity in ID. tauto.
  - destruct RD. auto with *.
  - destruct RD as (? & ? & ? & ->).
    apply NO_identity.
Qed.

Lemma resource_decay_LK_at {b phi phi' R sh loc} :
  resource_decay b phi phi' ->
  (fst loc < b)%positive ->
  (LK_at R sh loc) phi ->
  (LK_at (approx (level phi) R) sh loc) phi'.
Proof.
  intros RD LT LKAT loc'.
  specialize (LKAT loc').
  destruct (adr_range_dec loc lock_size loc') as [range|notrange]; swap 1 2.
  - rewrite jam_false in *; auto.
  - rewrite jam_true in *; auto.
    destruct (eq_dec loc loc') as [<-|noteq].
    + rewrite jam_true in *; auto.
      destruct LKAT as [p E]; simpl in E.
      apply (resource_decay_LK RD) in E.
      eexists.
      hnf.
      rewrite E.
      reflexivity.
    + rewrite jam_false in *; auto.
      destruct LKAT as [p E]; simpl in E.
      eexists; simpl.
      apply (resource_decay_CT RD) in E.
      rewrite E.
      reflexivity.
Qed.

(* todo: maybe remove one of those lemmas *)

Lemma resource_decay_LK_at' {b phi phi' R sh loc} :
  resource_decay b phi phi' ->
  (fst loc < b)%positive ->
  (LK_at R sh loc) phi ->
  (LK_at (approx (level phi') R) sh loc) phi'.
Proof.
  intros RD LT LKAT loc'.
  specialize (LKAT loc').
  destruct (adr_range_dec loc lock_size loc') as [range|notrange]; swap 1 2.
  - rewrite jam_false in *; auto.
  - rewrite jam_true in *; auto.
    destruct (eq_dec loc loc') as [<-|noteq].
    + rewrite jam_true in *; auto.
      destruct LKAT as [p E]; simpl in E.
      apply (resource_decay_LK RD) in E.
      eexists.
      hnf.
      rewrite E.
      f_equal.
      simpl.
      rewrite <- compose_assoc.
      rewrite approx_oo_approx'. 2:apply RD.
      f_equal.
      extensionality.
      unfold "oo".
      change (approx (level phi')   (approx (level phi')  R))
      with  ((approx (level phi') oo approx (level phi')) R).
      rewrite approx_oo_approx.
      reflexivity.
    + rewrite jam_false in *; auto.
      destruct LKAT as [p E]; simpl in E.
      eexists; simpl.
      apply (resource_decay_CT RD) in E.
      rewrite E.
      reflexivity.
Qed.

Lemma resource_decay_PURE {b phi phi'} :
  resource_decay b phi phi' ->
  forall loc sh P,
    phi @ loc = PURE sh P ->
    phi' @ loc = PURE sh (preds_fmap (approx (level phi')) P).
Proof.
  intros [L RD] loc sh P PAT.
  specialize (RD loc).
  destruct RD as [N [RD|[RD|[RD|RD]]]].
  - rewrite PAT in RD; simpl in RD. rewrite RD; auto.
  - rewrite PAT in RD; simpl in RD. destruct RD as (?&?&?&?&?). congruence.
  - rewrite PAT in N. pose proof (N (proj1 RD)). congruence.
  - rewrite PAT in RD; simpl in RD. destruct RD as (?&?&?&?). congruence.
Qed.

Lemma resource_decay_PURE_inv {b phi phi'} :
  resource_decay b phi phi' ->
  forall loc sh P',
    phi' @ loc = PURE sh P' ->
    exists P,
      phi @ loc = PURE sh P /\
      P' = preds_fmap (approx (level phi')) P.
Proof.
  intros [L RD] loc sh P PAT.
  specialize (RD loc).
  destruct RD as [N [RD|[RD|[RD|RD]]]].
  all: rewrite PAT in *; destruct (phi @ loc); simpl in *.
  all: inversion RD; subst; eauto.
  all: repeat match goal with H : ex _ |- _ => destruct H end.
  all: repeat match goal with H : and _ _ |- _ => destruct H end.
  all: discriminate.
Qed.

Lemma resource_decay_func_at' {b phi phi'} :
  resource_decay b phi phi' ->
  forall loc fs,
    seplog.func_at' fs loc phi ->
    seplog.func_at' fs loc phi'.
Proof.
  intros RD loc [f cc A P Q] [pp E]; simpl.
  rewrite (resource_decay_PURE RD _ _ _ E).
  eexists. reflexivity.
Qed.

Lemma resource_decay_func_at'_inv {b phi phi'} :
  resource_decay b phi phi' ->
  forall loc fs,
    seplog.func_at' fs loc phi' ->
    seplog.func_at' fs loc phi.
Proof.
  intros RD loc [f cc A P Q] [pp E]; simpl.
  destruct (resource_decay_PURE_inv RD _ _ _ E) as [pp' [Ephi E']].
  pose proof resource_at_approx phi loc as H.
  rewrite Ephi in H at 1. rewrite <-H.
  eexists. reflexivity.
Qed.

Lemma hereditary_func_at' loc fs :
  hereditary age (seplog.func_at' fs loc).
Proof.
  intros x y a; destruct fs as [f cc A P Q]; simpl.
  intros [pp E].
  destruct (proj1 (age1_PURE _ _ loc (FUN f cc) a)) as [pp' Ey]; eauto.
  pose proof resource_at_approx y loc as H.
  rewrite Ey in H at 1; simpl in H.
  rewrite <-H.
  exists pp'.
  reflexivity.
Qed.

Lemma anti_hereditary_func_at' loc fs :
  hereditary (fun x y => age y x) (seplog.func_at' fs loc).
Proof.
  intros x y a; destruct fs as [f cc A P Q]; simpl.
  intros [pp E].
  destruct (proj2 (age1_PURE _ _ loc (FUN f cc) a)) as [pp' Ey]; eauto.
  pose proof resource_at_approx y loc as H.
  rewrite Ey in H at 1; simpl in H.
  rewrite <-H.
  exists pp'.
  reflexivity.
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

Definition resource_is_lock r := exists rsh sh n pp, r = YES rsh sh (LK n) pp.

Definition same_locks phi1 phi2 := 
  forall loc, resource_is_lock (phi1 @ loc) <-> resource_is_lock (phi2 @ loc).

Definition resource_is_lock_sized n r := exists rsh sh pp, r = YES rsh sh (LK n) pp.

Definition same_locks_sized phi1 phi2 := 
  forall loc n, resource_is_lock_sized n (phi1 @ loc) <-> resource_is_lock_sized n (phi2 @ loc).

Definition lockSet_block_bound lset b :=
  forall loc, isSome (AMap.find (elt:=option rmap) loc lset) -> (fst loc < b)%positive.

Lemma resource_decay_same_locks {b phi phi'} :
  resource_decay b phi phi' -> same_locks phi phi'.
Proof.
  intros R loc; split; intros (rsh & sh & n & pp & E).
  - repeat eexists. eapply resource_decay_LK in E; eauto.
  - destruct (resource_decay_LK_inv R E) as [pp' [E' ->]].
    repeat eexists.
Qed.

Lemma resource_decay_same_locks_sized {b phi phi'} :
  resource_decay b phi phi' -> same_locks_sized phi phi'.
Proof.
  intros R loc n; split; intros (rsh & sh & pp & E).
  - repeat eexists. eapply resource_decay_LK in E; eauto.
  - destruct (resource_decay_LK_inv R E) as [pp' [E' ->]].
    repeat eexists.
Qed.

Lemma app_pred_age {R} {phi phi' : rmap} :
  age phi phi' ->
  app_pred R phi ->
  app_pred R phi'.
Proof.
  destruct R as [R HR]; simpl.
  apply HR.
Qed.

Lemma age_yes_sat {Phi Phi' phi phi' l z sh sh'} (R : mpred) :
  level Phi = level phi ->
  age Phi Phi' ->
  age phi phi' ->
  app_pred R phi ->
  Phi  @ l = YES sh sh' (LK z) (SomeP nil (fun _ => R)) ->
  app_pred (approx (S (level phi')) R) phi' /\
  Phi' @ l = YES sh sh' (LK z) (SomeP nil (fun _ => approx (level Phi') R)).
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

Lemma isSome_find_map addr f lset :
  ssrbool.isSome (AMap.find (elt:=option rmap) addr (AMap.map f lset)) = 
  ssrbool.isSome (AMap.find (elt:=option rmap) addr lset).
Proof.
  match goal with |- _ ?a = _ ?b => destruct a eqn:E; destruct b eqn:F end; try reflexivity.
  - apply AMap_find_map_inv in E; destruct E as [x []]; congruence.
  - rewrite (AMap_find_map _ _ _ o F) in E. discriminate.
Qed.

Lemma interval_adr_range b start length i :
  Intv.In i (start, start + length) <->
  adr_range (b, start) length (b, i).
Proof.
  compute; intuition.
Qed.

Lemma join_YES_l {r1 r2 r3 sh1 sh1' k pp} :
  sepalg.join r1 r2 r3 ->
  r1 = YES sh1 sh1' k pp ->
  exists sh3 sh3',
    r3 = YES sh3 sh3' k pp.
Proof.
  intros J; inversion J; intros.
  all:try congruence.
  all:do 2 eexists; f_equal; try congruence.
Qed.

Lemma age_resource_at {phi phi' loc} :
  age phi phi' ->
  phi' @ loc = resource_fmap (approx (level phi')) (phi @ loc).
Proof.
  intros A.
  rewrite <- (age1_resource_at _ _ A loc (phi @ loc)).
  - reflexivity.
  - rewrite resource_at_approx. reflexivity.
Qed.

Lemma jstep_age_sim {G C} {csem : CoreSemantics G C mem} {ge c c' jm1 jm2 jm1'} :
  age jm1 jm2 ->
  jstep csem ge c jm1 c' jm1' ->
  level jm2 <> O ->
  exists jm2',
    age jm1' jm2' /\
    jstep csem ge c jm2 c' jm2'.
Proof.
  intros A [step [rd lev]] nz.
  destruct (age1 jm1') as [jm2'|] eqn:E.
  - exists jm2'. split; auto.
    split; [|split]; auto.
    + exact_eq step.
      f_equal; apply age_jm_dry; auto.
    + eapply (age_resource_decay _ (m_phi jm1) (m_phi jm1')).
      * exact_eq rd.
        f_equal. f_equal. apply age_jm_dry; auto.
      * apply age_jm_phi; auto.
      * apply age_jm_phi; auto.
      * rewrite level_juice_level_phi in *. auto.
    + apply age_level in E.
      apply age_level in A.
      omega.
  - apply age1_level0 in E.
    apply age_level in A.
    omega.
Qed.

Lemma pures_eq_unage {jm1 jm1' jm2}:
  ge (level jm1') (level jm2) ->
  age jm1 jm1' ->
  juicy_safety.pures_eq jm1' jm2 ->
  juicy_safety.pures_eq jm1 jm2.
Proof.
  intros L A [S P]; split; intros loc; [clear P; autospec S | clear S; autospec P ].
  all:apply age_jm_phi in A.
  all:repeat rewrite level_juice_level_phi in *.
  all:unfold m_phi in *.
  all:destruct jm1 as [_ p1 _ _ _ _].
  all:destruct jm1' as [_ p1' _ _ _ _].
  all:destruct jm2 as [_ p2 _ _ _ _].
  - rewrite (age_resource_at A) in S.
    destruct (p1 @ loc) eqn:E; auto.
    simpl in S.
    rewrite S.
    rewrite preds_fmap_fmap.
    rewrite approx_oo_approx'; auto.
  
  - destruct (p2 @ loc) eqn:E; auto.
    revert P.
    eapply age1_PURE. auto.
Qed.

Lemma jsafeN_age Z Jspec ge ora q n jm jmaged :
  ext_spec_stable age (JE_spec _ Jspec) ->
  age jm jmaged ->
  le n (level jmaged) ->
  @jsafeN Z Jspec ge n ora q jm ->
  @jsafeN Z Jspec ge n ora q jmaged.
Proof.
  intros heredspec A L Safe; revert jmaged A L.
  induction Safe as
      [ z c jm
      | n z c jm c' jm' step safe IH
      | n z c jm ef sig args x atex Pre Post
      | n z c jm v Halt Exit ]; intros jmaged A L.
  - constructor 1.
  - simpl in step.
    destruct (jstep_age_sim A step ltac:(omega)) as [jmaged' [A' step']].
    econstructor 2; eauto.
    apply IH; eauto.
    apply age_level in A'.
    apply age_level in A.
    destruct step as [_ [_ ?]].
    omega.
  - econstructor 3.
    + eauto.
    + eapply (proj1 heredspec); eauto.
    + intros ret jm' z' n' H rel post.
      destruct (Post ret jm' z' n' H) as (c' & atex' & safe'); eauto.
      unfold juicy_safety.Hrel in *.
      split;[|split]; try apply rel.
      * apply age_level in A; omega.
      * unshelve eapply (pures_eq_unage _ A), rel.
        omega.
  - econstructor 4. eauto.
    eapply (proj2 heredspec); eauto.
Qed.

Lemma jsafeN_age_to Z Jspec ge ora q n l jm :
  ext_spec_stable age (JE_spec _ Jspec) ->
  le n l ->
  @jsafeN Z Jspec ge n ora q jm ->
  @jsafeN Z Jspec ge n ora q (age_to l jm).
Proof.
  intros Stable nl.
  apply age_to_ind_refined.
  intros x y H L.
  apply jsafeN_age; auto.
  omega.
Qed.

Lemma m_dry_age_to n jm : m_dry (age_to n jm) = m_dry jm.
Proof.
  remember (m_dry jm) as m eqn:E; symmetry; revert E.
  apply age_to_ind; auto.
  intros x y H E ->. rewrite E; auto. clear E.
  apply age_jm_dry; auto.
Qed.

Lemma m_phi_age_to n jm : m_phi (age_to n jm) = age_to n (m_phi jm).
Proof.
  unfold age_to.
  rewrite level_juice_level_phi.
  generalize (level (m_phi jm) - n)%nat; clear n.
  intros n; induction n. reflexivity.
  simpl. rewrite <- IHn.
  clear IHn. generalize (age_by n jm); clear jm; intros jm.
  unfold age1'.
  destruct (age1 jm) as [jm'|] eqn:e.
  - rewrite (age1_juicy_mem_Some _ _ e). easy.
  - rewrite (age1_juicy_mem_None1 _ e). easy.
Qed.
