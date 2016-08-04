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
Require Import concurrency.age_to.
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

(** * Results related to resouce_decay *)

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

(** * Results related to aging  *)

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

(** * Results on cl_step *)

Lemma cl_step_decay ge c m c' m' : @cl_step ge c m c' m' -> @decay m m'.
Proof.
  intros step.
  induction step
    as [ ve te k m a1 a2 b ofs v2 v m' H H0 H1 H2 ASS | |
         ve te k m optid a al tyagrs tyres cc vf vargs f m'  ve' le' H H0 H1 H2 H3 H4 NRV ALLOC H6 
         | | | | | | | | | f ve te optexp optid k m v' m' ve' te'' k' H H0 FREE H2 H3 | | | ];
    try apply decay_refl || apply IHstep.
  
  - (* assign: no change in permission *)
    intros b' ofs'.
    split.
    + inversion ASS as [v0 chunk m'0 H3 BAD H5 H6 | b'0 ofs'0 bytes m'0 H3 H4 H5 H6 H7 BAD H9 H10]; subst.
      -- pose proof storev_valid_block_2 _ _ _ _ _ BAD b'. tauto.
      -- pose proof Mem.storebytes_valid_block_2 _ _ _ _ _ BAD b'. tauto.
    + intros V; right; intros kind.
      (* destruct m as [c acc nb max no def]. simpl in *. *)
      inversion ASS as [v0 chunk m'0 H3 STO H5 H6 | b'0 ofs'0 bytes m'0 H3 H4 H5 H6 H7 STO H9 H10]; subst.
      -- simpl in *.
         Transparent Mem.store.
         unfold Mem.store in *; simpl in *.
         destruct (Mem.valid_access_dec m chunk b (Int.unsigned ofs) Writable).
         2:discriminate.
         injection STO as <-. simpl.
         reflexivity.
      -- Transparent Mem.storebytes.
         unfold Mem.storebytes in *.
         destruct (Mem.range_perm_dec
                     m b (Int.unsigned ofs)
                     (Int.unsigned ofs + Z.of_nat (Datatypes.length bytes)) Cur Writable).
         2:discriminate.
         injection STO as <-. simpl.
         reflexivity.
  
  - (* internal call : allocations *)
    clear -ALLOC.
    induction ALLOC. now apply decay_refl.
    apply decay_trans with m1. 3:apply IHALLOC.
    
    + clear -H.
      Transparent Mem.alloc.
      unfold Mem.alloc in *.
      injection H as <- <-.
      intros b V.
      unfold Mem.valid_block in *. simpl.
      apply Coqlib.Plt_trans_succ, V.
      
    + clear -H.
      unfold Mem.alloc in *.
      injection H as E <-.
      intros b ofs.
      split.
      * intros N V.
        subst m1.
        simpl in *.
        rewrite PMap.gsspec.
        unfold Mem.valid_block in *; simpl in *.
        if_tac; subst; auto.
        -- if_tac; auto.
        -- destruct N.
           apply Coqlib.Plt_succ_inv in V.
           tauto.
      * intros V.
        right.
        intros k.
        subst.
        simpl.
        rewrite PMap.gsspec.
        if_tac.
        -- subst b. inversion V. rewrite Pos.compare_lt_iff in *. edestruct Pos.lt_irrefl; eauto.
        -- reflexivity.
  
  - (* return: free_list *)
    revert FREE; clear.
    generalize (blocks_of_env ge ve); intros l.
    revert m m'; induction l as [| [[b o] o'] l IHl]; intros m m'' E.
    + simpl. injection E as <- ; apply decay_refl.
    + simpl in E.
      destruct (Mem.free m b o o') as [m' |] eqn:F.
      2:discriminate.
      specialize (IHl _ _ E).
      Transparent Mem.free.
      unfold Mem.free in *.
      if_tac in F. rename H into G.
      2:discriminate.
      apply decay_trans with m'. 3:now apply IHl.
      * injection F as <-.
        intros.
        unfold Mem.unchecked_free, Mem.valid_block in *.
        simpl in *.
        assumption.
      
      * injection F as <-.
        clear -G.
        unfold Mem.unchecked_free in *.
        intros b' ofs; simpl. unfold Mem.valid_block; simpl.
        split.
        tauto.
        intros V.
        rewrite PMap.gsspec.
        if_tac; auto. subst b'.
        hnf in G.
        destruct (Coqlib.proj_sumbool (Coqlib.zle o ofs)&&Coqlib.proj_sumbool (Coqlib.zlt ofs o')) eqn:E.
        2: now auto.
        left. split; auto.
        destruct m as [co acc nb max noa def] eqn:Em; simpl in *.
        unfold Mem.perm in G; simpl in *.
        specialize (G ofs).
        cut (acc !! b ofs Cur = Some Freeable). {
          destruct k; auto.
          pose proof Mem.access_max m b ofs as M.
          subst m; simpl in M.
          intros A; rewrite A in M.
          destruct (acc !! b ofs Max) as [ [] | ]; inversion M; auto.
        }
        assert (R: (o <= ofs < o')%Z). {
          rewrite andb_true_iff in *. destruct E as [E F].
          apply Coqlib.proj_sumbool_true in E.
          apply Coqlib.proj_sumbool_true in F.
          auto.
        }
        autospec G.
        destruct (acc !! b ofs Cur) as [ [] | ]; inversion G; auto.
Qed.

Lemma cl_step_unchanged_on ge c m c' m' b ofs :
  @cl_step ge c m c' m' ->
  Mem.valid_block m b ->
  ~ Mem.perm m b ofs Cur Writable ->
  Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
  Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m')).
Proof.
  intros step.
  induction step
    as [ ve te k m a1 a2 b0 ofs0 v2 v m' H H0 H1 H2 ASS | |
         ve te k m optid a al tyagrs tyres cc vf vargs f m'  ve' le' H H0 H1 H2 H3 H4 NRV ALLOC H6 
         | | | | | | | | | f ve te optexp optid k m v' m' ve' te'' k' H H0 FREE H2 H3 | | | ];
    intros V NW; auto.
  
  - (* assign: some things are updated, but not the chunk in non-writable permission *)
    inversion ASS; subst.
    + inversion H4.
      unfold Mem.store in *.
      destruct (Mem.valid_access_dec m chunk b0 (Int.unsigned ofs0) Writable); [|discriminate].
      injection H6 as <- ; clear ASS H4.
      simpl.
      destruct (eq_dec b b0) as [e|n]; swap 1 2.
      * rewrite PMap.gso; auto.
      * subst b0. rewrite PMap.gss.
        generalize ((Mem.mem_contents m) !! b); intros t.
        destruct v0 as [v0 align].
        specialize (v0 ofs).
        {
          destruct (adr_range_dec (b, Int.unsigned ofs0) (size_chunk chunk) (b, ofs)) as [a|a].
          - simpl in a; destruct a as [_ a].
            autospec v0.
            tauto.
          - simpl in a.
            symmetry.
            apply Mem.setN_outside.
            rewrite encode_val_length.
            replace (Z_of_nat (size_chunk_nat chunk)) with (size_chunk chunk); swap 1 2.
            { unfold size_chunk_nat in *. rewrite Z2Nat.id; auto. destruct chunk; simpl; omega. }
            assert (a' : ~ (Int.unsigned ofs0 <= ofs < Int.unsigned ofs0 + size_chunk chunk)%Z) by intuition.
            revert a'; clear.
            generalize (Int.unsigned ofs0).
            generalize (size_chunk chunk).
            intros.
            omega.
        }
    
    + (* still the case of assignment (copying) *)
      unfold Mem.storebytes in *.
      destruct (Mem.range_perm_dec m b0 (Int.unsigned ofs0) (Int.unsigned ofs0 + Z.of_nat (Datatypes.length bytes)) Cur Writable); [ | discriminate ].
      injection H8 as <-; clear ASS; simpl.
      destruct (eq_dec b b0) as [e|n]; swap 1 2.
      * rewrite PMap.gso; auto.
      * subst b0. rewrite PMap.gss.
        generalize ((Mem.mem_contents m) !! b); intros t.
        specialize (r ofs).
        {
          destruct (adr_range_dec (b, Int.unsigned ofs0) (Z.of_nat (Datatypes.length bytes)) (b, ofs)) as [a|a].
          - simpl in a; destruct a as [_ a].
            autospec r.
            tauto.
          - simpl in a.
            symmetry.
            apply Mem.setN_outside.
            assert (a' : ~ (Int.unsigned ofs0 <= ofs < Int.unsigned ofs0 + Z.of_nat (Datatypes.length bytes))%Z) by intuition.
            revert a'; clear.
            generalize (Int.unsigned ofs0).
            intros.
            omega.
        }
  
  - (* internal call : things are allocated -- each time in a new block *)
    clear -V ALLOC.
    induction ALLOC. easy.
    rewrite <-IHALLOC; swap 1 2.
    + unfold Mem.alloc in *.
      injection H as <- <-.
      unfold Mem.valid_block in *.
      simpl.
      apply Plt_trans_succ.
      auto.
    + clear IHALLOC.
      unfold Mem.alloc in *.
      injection H as <- <- . simpl.
      f_equal.
      rewrite PMap.gso. auto.
      unfold Mem.valid_block in *.
      auto with *.
  
  - (* return: free_list *)
    revert FREE NW V; clear.
    generalize (blocks_of_env ge ve); intros l.
    revert m m'; induction l as [| [[b' o] o'] l IHl]; intros m m'' E NW V.
    + simpl. injection E as <- . easy.
    + simpl in E.
      destruct (Mem.free m b' o o') as [m' |] eqn:F.
      2:discriminate.
      specialize (IHl _ _ E).
      unfold Mem.free in *.
      if_tac in F. 2:discriminate.
      injection F as <- .
      rewrite <-IHl. easy.
      * unfold Mem.perm in *.
        unfold Mem.unchecked_free.
        simpl.
        rewrite PMap.gsspec.
        if_tac; [ | easy ].
        subst.
        unfold Mem.range_perm in *.
        destruct (zle o ofs); auto.
        destruct (zlt ofs o'); simpl; auto.
      * unfold Mem.unchecked_free, Mem.valid_block; simpl. auto.
Qed.


(** * Results related to machine predicates *)
   
(* Instantiation of modules *)
Import THE_JUICY_MACHINE.
Import JSEM.
Module Machine :=THE_JUICY_MACHINE.JTP.
Definition schedule := SCH.schedule.
Import JuicyMachineLemmas.
Import ThreadPool.

Lemma same_locks_juicyLocks_in_lockSet phi phi' lset :
  same_locks phi phi' ->
  juicyLocks_in_lockSet lset phi ->
  juicyLocks_in_lockSet lset phi'.
Proof.
  intros SL IN loc sh psh P n E.
  destruct (SL loc) as [_ (rsh & sh' & n' & pp & E')].
  { rewrite E. repeat eexists. }
  apply (IN loc _ _ _ _ E').
Qed.

Lemma resource_decay_lockSet_in_juicyLocks b phi phi' lset :
  resource_decay b phi phi' ->
  lockSet_block_bound lset b ->
  lockSet_in_juicyLocks lset phi ->
  lockSet_in_juicyLocks lset phi'.
Proof.
  intros RD LB IN loc IT.
  destruct (IN _ IT) as (rsh & sh & pp & E).
  (* assert (SL : same_locks phi phi') by (eapply resource_decay_same_locks; eauto). *)
  assert (SL : same_locks_sized phi phi') by (eapply resource_decay_same_locks_sized; eauto).
  destruct (SL loc LKSIZE) as [(rsh' & sh' & pp' &  E') _].
  { rewrite E. exists rsh, sh, pp. reflexivity. }
  destruct RD as [L RD].
  destruct (RD loc) as [NN [R|[R|[[P [v R]]|R]]]].
  + rewrite E in R. simpl in R; rewrite <- R.
    eauto.
  + rewrite E in R. destruct R as (sh'' & v & v' & R & H). discriminate.
  + specialize (LB loc).
    cut (fst loc < b)%positive. now intro; exfalso; eauto.
    apply LB. destruct (AMap.find (elt:=option rmap) loc lset).
    * apply I.
    * inversion IT.
  + destruct R as (v & v' & R & N').
    rewrite E'.
    exists rsh', sh', pp'.
    eauto.
Qed.

Lemma lockSet_Writable_lockSet_block_bound m lset  :
  lockSet_Writable lset m ->
  lockSet_block_bound lset (Mem.nextblock m).
Proof.
  simpl; intros LW.
  intros (b, ofs) IN; simpl.
  specialize (LW b ofs).
  destruct (AMap.find (elt:=option rmap) (b, ofs) lset). 2:inversion IN.
  specialize (LW eq_refl).
  cut (~ ~ (b < Mem.nextblock m)%positive). zify. omega. intros L.
  specialize (LW ofs).
  assert (Intv.In ofs (ofs, (ofs + LKSIZE)%Z)).
  { split; simpl; unfold LKSIZE in *; simpl; omega. }
  autospec LW.
  rewrite (Mem.nextblock_noaccess _ _ ofs Max L) in LW.
  inversion LW.
Qed.

Lemma join_all_age_updThread_level tp i (cnti : ThreadPool.containsThread tp i) c phi Phi :
  join_all (age_tp_to (level phi) (ThreadPool.updThread cnti c phi)) Phi ->
  level Phi = level phi.
Proof.
  intros J; symmetry.
  remember (level phi) as n.
  rewrite <- (level_age_to n phi). 2:omega.
  apply rmap_join_sub_eq_level.
  assert (cnti' : containsThread (updThread cnti c phi) i) by eauto with *.
  rewrite (@cnt_age _ _ n) in cnti'.
  pose proof compatible_threadRes_sub cnti' J as H.
  unshelve erewrite <-getThreadR_age in H; eauto with *.
  rewrite gssThreadRes in H.
  apply H.
Qed.

Lemma join_all_level_lset tp Phi l phi :
  join_all tp Phi ->
  AMap.find l (lset tp) = SSome phi ->
  level phi = level Phi.
Proof.
  intros J F.
  apply rmap_join_sub_eq_level.
  eapply compatible_lockRes_sub; eauto.
Qed.

Lemma lset_range_perm m tp b ofs
  (compat : mem_compatible tp m)
  (Efind : AMap.find (elt:=option rmap) (b, ofs) (lset tp) <> None) :
  Mem.range_perm
    (restrPermMap (mem_compatible_locks_ltwritable compat))
    b ofs (ofs + size_chunk Mint32) Cur Writable.
Proof.
  unfold Mem.range_perm in *.
  intros ofs0 range.
  unfold Mem.perm in *.
  pose proof restrPermMap_Cur as R.
  unfold permission_at in *.
  rewrite R.
  erewrite lockSet_spec_2.
  + constructor.
  + eauto.
  + unfold lockRes in *.
    unfold lockGuts in *.
    unfold LocksAndResources.lock_info in *.
    destruct (AMap.find (elt:=option rmap) (b, ofs) (lset tp)).
    * reflexivity.
    * tauto.
Qed.

Lemma age_to_updThread i tp n c phi cnti cnti' :
  age_tp_to n (@updThread i tp cnti c phi) =
  @updThread i (age_tp_to n tp) cnti' c (age_to n phi).
Proof.
  destruct tp; simpl.
  unfold updThread in *; simpl.
  f_equal. extensionality j.
  unfold "oo".
  do 2 match goal with
         |- context [if ?a then _ else _] =>
         let E := fresh "E" in
         destruct a eqn:E
       end.
  all:auto.
  all:cut (true = false); [ congruence | ].
  all:rewrite <-E, <-E0; repeat f_equal; apply proof_irr.
Qed.

Lemma lset_age_tp_to n tp :
  lset (age_tp_to n tp) = AMap.map (option_map (age_to n)) (lset tp).
Proof.
  destruct tp; reflexivity.
Qed.

Lemma getThreadC_fun i tp cnti cnti' x y :
  @getThreadC i tp cnti = x ->
  @getThreadC i tp cnti' = y ->
  x = y.
Proof.
  intros <- <-.
  unfold getThreadC, containsThread in *.
  repeat f_equal.
  apply proof_irr.
Qed.

Lemma getThreadR_fun i tp cnti cnti' x y :
  @getThreadR i tp cnti = x ->
  @getThreadR i tp cnti' = y ->
  x = y.
Proof.
  intros <- <-.
  unfold getThreadR, containsThread in *.
  repeat f_equal.
  apply proof_irr.
Qed.

Lemma lockSet_Writable_age n tp m :
  lockSet_Writable (lset tp) m ->
  lockSet_Writable (lset (age_tp_to n tp)) m.
Proof.
  rewrite lset_age_tp_to.
  intros L b ofs E ofs0 range.
  refine(L b ofs _ ofs0 range).
  exact_eq E; f_equal.
  apply isSome_find_map.
Qed.

Lemma juicyLocks_in_lockSet_age n tp phi :
  juicyLocks_in_lockSet (lset tp) phi ->
  juicyLocks_in_lockSet (lset (age_tp_to n tp)) (age_to n phi).
Proof.
  rewrite lset_age_tp_to.
  intros L loc sh sh' pp z E.
  pattern pp in E.
  pose proof ex_intro _ pp E as H.
  pattern (age_to n phi) in H.
  rewrite <-rewrite_age_to in H; swap 1 2.
  - intros; eapply age1_YES'; auto.
  - destruct H as (pp', E').
    specialize (L loc sh sh' pp' z E').
    exact_eq L; f_equal.
    symmetry.
    apply isSome_find_map.
Qed.

Lemma lockSet_in_juicyLocks_age n tp phi :
  lockSet_in_juicyLocks (lset tp) phi ->
  lockSet_in_juicyLocks (lset (age_tp_to n tp)) (age_to n phi).
Proof.
  rewrite lset_age_tp_to.
  intros L loc E.
  rewrite isSome_find_map in E.
  specialize (L loc E).
  destruct L as (sh & sh' & L). exists sh, sh'.
  pattern (age_to n phi).
  rewrite <-rewrite_age_to. easy.
  intros; eapply age1_YES'; auto.
Qed.

Definition same_except_cur (m m' : Mem.mem) :=
  Mem.mem_contents m = Mem.mem_contents m' /\
  max_access_at m = max_access_at m' /\
  Mem.nextblock m = Mem.nextblock m'.

Lemma mem_cohere_same_except_cur m m' phi :
  same_except_cur m m' ->
  mem_cohere' m phi ->
  mem_cohere' m' phi.
Proof.
  intros (ECo & EMa & EN) [Co Ac Ma N]; constructor.
  - hnf in *.
    unfold contents_at in *.
    rewrite <-ECo. auto.
  - unfold access_cohere' in *.
    unfold max_access_at in *.
    intros.
    apply equal_f with (x := loc) in EMa.
    rewrite <-EMa.
    auto.
  - unfold max_access_cohere in *. intros loc.
    apply equal_f with (x := loc) in EMa.
    rewrite <-EMa, <-EN.
    apply Ma.
  - hnf in *. rewrite <-EN.
    auto.
Qed.
  
Lemma mem_compatible_with_same_except_cur tp m m' phi :
  same_except_cur m m' ->
  mem_compatible_with tp m phi ->
  mem_compatible_with tp m' phi.
Proof.
  intros E [J AC LW LJ JL]; constructor; auto.
  - eapply mem_cohere_same_except_cur. apply E. apply AC.
  - destruct E as (ECo & EMa & EN).
    intros b ofs Ef ofs0 Ran.
    specialize (LW b ofs Ef ofs0 Ran).
    unfold max_access_cohere in *.
    apply equal_f with (x := (b, ofs0)) in EMa.
    unfold max_access_at in *.
    simpl in *.
    rewrite <-EMa.
    auto.
Qed.
