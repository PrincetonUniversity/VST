Require Import VST.veric.juicy_base.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.shares.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.juicy_mem. (*VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.*)

Require Import VST.veric.ghost_PCM. (*avoids doing Require Import VST.veric.initial_world.*)
Require Import VST.veric.own.
Require Import VST.veric.invariants.
Require Import VST.veric.tycontext.

Require Import VST.veric.age_to_resource_at.

Local Open Scope nat_scope.
Local Open Scope pred.

Record juicy_ext_spec (Z: Type) := {
  JE_spec:> external_specification juicy_mem external_function Z;
  JE_pre_hered: forall e t ge_s typs args z, hereditary age (ext_spec_pre JE_spec e t ge_s typs args z);
  JE_pre_ext: forall e t ge_s typs args z a a', ext_order a a' ->
    joins (ghost_of (m_phi a')) (Some (ext_ref z, NoneP) :: nil) ->
    ext_spec_pre JE_spec e t ge_s typs args z a ->
    ext_spec_pre JE_spec e t ge_s typs args z a';
  JE_post_hered: forall e t ge_s tret rv z, hereditary age (ext_spec_post JE_spec e t ge_s tret rv z);
  JE_post_ext: forall e t ge_s tret rv z, hereditary ext_order (ext_spec_post JE_spec e t ge_s tret rv z);
  JE_exit_hered: forall rv z, hereditary age (ext_spec_exit JE_spec rv z);
  JE_exit_ext: forall rv z, hereditary ext_order (ext_spec_exit JE_spec rv z)
}.

Class OracleKind := {
  OK_ty : Type;
  OK_spec: juicy_ext_spec OK_ty
}.

(*! The void ext_spec *)
Definition void_spec T : external_specification juicy_mem external_function T :=
    Build_external_specification
      juicy_mem external_function T
      (fun ef => False)
      (fun ef Hef ge tys vl m z => False)
      (fun ef Hef ge ty vl m z => False)
      (fun rv m z => False).

Definition ok_void_spec (T : Type) : OracleKind.
 refine (Build_OracleKind T (Build_juicy_ext_spec _ (void_spec T) _ _ _ _ _ _)).
Proof.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros; intros ? ? ? ?; contradiction.
  simpl; intros; intros ? ? ? ?; contradiction.
Defined.

Definition j_initial_core {C} (csem: @CoreSemantics C mem)
     (n: nat) (m: juicy_mem) (q: C) (m': juicy_mem) (v: val) (args: list val) 
     : Prop :=
  m' = m /\
  semantics.initial_core csem n (m_dry m) q (m_dry m') v args.

Definition j_at_external {C} (csem: @CoreSemantics C mem)
   (q: C) (jm: juicy_mem) : option (external_function * list val) :=
   semantics.at_external csem q (m_dry jm).

Definition j_after_external {C} (csem: @CoreSemantics C mem)
    (ret: option val) (q: C) (jm: juicy_mem) :=
   semantics.after_external csem ret q (m_dry jm).

Definition jstep {C} (csem: @CoreSemantics C mem)
  (q: C) (jm: juicy_mem) (q': C) (jm': juicy_mem) : Prop :=
 corestep csem q (m_dry jm) q' (m_dry jm') /\ 
 resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\
 level jm = S (level jm') /\
 ghost_of (m_phi jm') = ghost_approx jm' (ghost_of (m_phi jm)).

Definition j_halted {C} (csem: @CoreSemantics C mem)
       (c: C) (i: int): Prop :=
     halted csem c i.

Lemma jstep_not_at_external {C} (csem: @CoreSemantics C mem):
  forall m q m' q', jstep csem q m q' m' -> at_external csem q (m_dry m) = None.
Proof.
  intros.
  destruct H as (? & ? & ? & ?). eapply corestep_not_at_external; eauto.
Qed.

Lemma jstep_not_halted  {C} (csem: @CoreSemantics C mem):
  forall m q m' q' i, jstep csem q m q' m' -> ~j_halted csem q i.
Proof.
  intros. destruct H as (? & ? & ? & ?). eapply corestep_not_halted; eauto.
Qed.

(*Lenb: removed here. To be moved a more CLight-specific place
Record jm_init_package: Type := {
  jminit_m: Memory.mem;
  jminit_prog: program;
  jminit_G: tycontext.funspecs;
  jminit_lev: nat;
  jminit_init_mem: Genv.init_mem jminit_prog = Some jminit_m;
  jminit_defs_no_dups:   list_norepet (prog_defs_names jminit_prog);
  jminit_fdecs_match: match_fdecs (prog_funct jminit_prog) jminit_G
}.

Definition init_jmem {G} (ge: G) (jm: juicy_mem) (d: jm_init_package) :=
  jm = initial_jm (jminit_prog d) (jminit_m d) (jminit_G d) (jminit_lev d)
         (jminit_init_mem d) (jminit_defs_no_dups d) (jminit_fdecs_match d).
*)
Definition juicy_core_sem
  {C} (csem: @CoreSemantics C mem) :
   @CoreSemantics C juicy_mem :=
  @Build_CoreSemantics _ juicy_mem
    (j_initial_core csem)
    (j_at_external csem)
    (j_after_external csem)
    (j_halted csem)
    (jstep csem)
    (jstep_not_halted csem)
    (jstep_not_at_external csem)
(*  (j_at_external_halted_excl csem)*).

Section upd_exit.
  Context {Z : Type}.
  Variable spec : juicy_ext_spec Z.

  Definition upd_exit' (Q_exit : option val -> Z -> juicy_mem -> Prop) :=
  {| ext_spec_type := ext_spec_type spec
   ; ext_spec_pre := ext_spec_pre spec
   ; ext_spec_post := ext_spec_post spec
   ; ext_spec_exit := Q_exit |}.

  Definition upd_exit'' (ef : external_function) (x : ext_spec_type spec ef) ge :=
    upd_exit' (ext_spec_post spec ef x ge (sig_res (ef_sig ef))).

  Program Definition upd_exit {ef : external_function} (x : ext_spec_type spec ef) ge
   : juicy_ext_spec Z :=
    Build_juicy_ext_spec _ (upd_exit'' _ x ge) _ _ _ _ _ _.
  Next Obligation. intros. eapply JE_pre_hered; eauto. Qed.
  Next Obligation. intros. eapply JE_pre_ext; eauto. Qed.
  Next Obligation. intros. eapply JE_post_hered; eauto. Qed.
  Next Obligation. intros. eapply JE_post_ext; eauto. Qed.
  Next Obligation. intros. eapply JE_post_hered; eauto. Qed. 
  Next Obligation. intros. eapply JE_post_ext; eauto. Qed.
End upd_exit.

Obligation Tactic := Tactics.program_simpl.

Program Definition juicy_mem_op (P : pred rmap) : pred juicy_mem :=
  fun jm => P (m_phi jm).
 Next Obligation.
  split; repeat intro.
  apply age1_juicy_mem_unpack in H.
  destruct H.
  eapply pred_hereditary; eauto.

  destruct H; eapply pred_upclosed; eauto.
 Qed.

Lemma age_resource_decay:
   forall b jm1 jm2 jm1' jm2',
        resource_decay b jm1 jm2 ->
        age jm1 jm1' -> age jm2 jm2' ->
        level jm1 = S (level jm2) ->
        resource_decay b jm1' jm2'.
Proof.
  unfold resource_decay; intros.
  rename H2 into LEV.
  destruct H as [H' H].
  split.
  {
    clear H.
    apply age_level in H0; apply age_level in H1.
    rewrite H0 in *; rewrite H1 in *. inv LEV. rewrite H2.
    clear. forget (level jm2') as n. lia.
  }
  intro l.
  specialize (H l).
  destruct H.
  split.
  {
    intro.
    specialize (H H3).
    erewrite <- necR_NO; eauto.  constructor 1; auto.
  }
  destruct H2 as [?|[?|[?|?]]].
  + left.
    clear H. unfold age in *.
    rewrite (age1_resource_at _ _ H0 l (jm1 @ l)); [ | symmetry; apply resource_at_approx].
    rewrite (age1_resource_at _ _ H1 l (jm2 @ l)); [ | symmetry; apply resource_at_approx].
    rewrite <- H2.
    rewrite resource_fmap_fmap.
    rewrite resource_fmap_fmap.
    f_equal.
    - change R.approx with approx.
      rewrite approx_oo_approx'; [rewrite approx_oo_approx'; auto |].
      * apply age_level in H0; apply age_level in H1.
        unfold rmap  in *;
        forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
        subst; lia.
      * apply age_level in H0; apply age_level in H1.
        unfold rmap in *.
        forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
        subst; lia.
    - change R.approx with approx.
      rewrite approx'_oo_approx; [rewrite approx'_oo_approx; auto |].
      * apply age_level in H0; apply age_level in H1.
        unfold rmap  in *;
        forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
        subst; lia.
      * apply age_level in H0; apply age_level in H1.
        unfold rmap in *.
        forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
        subst; lia.
  + right.
    destruct H2 as [sh [wsh [v [v' [? ?]]]]].
    left; exists sh, wsh, v,v'.
    split.
    - apply age_level in H1.
      unfold rmap in *.
      forget (@level R.rmap R.ag_rmap jm2) as j2.
      forget (@level R.rmap R.ag_rmap jm2') as j2'. subst j2.
      clear - H2 H0 LEV.
      revert H2; case_eq (jm1 @ l); intros; inv H2.
      pose proof (necR_YES jm1 jm1' l sh r (VAL v) p (rt_step _ _ _ _ H0) H).
      rewrite H1.
      simpl. rewrite preds_fmap_fmap.
      apply age_level in H0.
      rewrite approx_oo_approx'.
        2: rewrite H0 in *; inv LEV; lia.
      rewrite approx'_oo_approx.
        2: rewrite H0 in *; inv LEV; lia.
      f_equal. apply proof_irr.
      rewrite H5.
      rewrite <- (approx_oo_approx' j2' (S j2')) at 1 by auto.
      rewrite <- (approx'_oo_approx j2' (S j2')) at 2 by auto.
      rewrite <- preds_fmap_fmap; rewrite H5. rewrite preds_fmap_NoneP. auto. 
    - pose proof (age1_YES _ _ l sh (writable0_readable wsh) (VAL v') H1).
      rewrite H4 in H3. auto.
  + destruct H2 as [? [v ?]]; right; right; left.
    split; auto. exists v.   apply (age1_YES _ _ l _ _ _ H1) in H3. auto.
  + right; right; right.
    destruct H2 as [v [pp [? ?]]]. exists v. econstructor; split; auto. 
    pose proof (age1_resource_at _ _ H0 l (YES Share.top readable_share_top(VAL v) pp)).
    rewrite H4.
    simpl. reflexivity.
    rewrite <- (resource_at_approx jm1 l).
    rewrite H2. reflexivity.
    assert (necR jm2 jm2'). apply laterR_necR. constructor. auto.
    apply (necR_NO _ _ l Share.bot bot_unreadable H4). auto.
Qed.

Lemma necR_PURE' phi0 phi k p adr :
  necR phi0 phi ->
  phi @ adr = PURE k p ->
  (*a stronger theorem is possible -- this one doesn't relate p, pp*)
  exists pp, phi0 @ adr = PURE k pp.
Proof.
  intros Hnec H.
  case_eq (phi0 @ adr). 
  { intros. eapply necR_NO in Hnec; try eassumption. 
    rewrite Hnec in H0. rewrite H0 in H. congruence. }
  { intros. eapply necR_YES in Hnec; eauto. rewrite Hnec in H. congruence. }
  { generalize (necR_level _ _ Hnec); intros Hlev.
    intros. eapply necR_PURE in Hnec; eauto.
    rewrite Hnec in H. inversion H. subst. eexists. eauto. }
Qed.

Definition jm_update m m' := m_dry m' = m_dry m /\ level m' = level m /\
  resource_at (m_phi m') = resource_at (m_phi m).

Lemma jm_update_age: forall m1 m2 m1', jm_update m1 m2 -> age m1 m1' ->
  exists m2', jm_update m1' m2' /\ age m2 m2'.
Proof.
  intros ??? (? & ? & ?) Hage.
  pose proof (age_level _ _ Hage).
  destruct (levelS_age m2 (level m1')) as (m2' & Hage2 & ?); [lia|].
  exists m2'; repeat split; auto.
  - rewrite <- (age_jm_dry Hage), <- (age_jm_dry Hage2); auto.
  - extensionality l.
    apply age_jm_phi in Hage; apply age_jm_phi in Hage2.
    rewrite (age_resource_at Hage), (age_resource_at Hage2).
    rewrite <- !level_juice_level_phi; congruence.
Qed.

Definition has_ext {Z} (ora : Z) : mpred.mpred := @own (ext_PCM _) 0 (Some (Tsh, Some ora), None) NoneP.

Definition jm_bupd {Z} (ora : Z) P m := forall C : ghost,
  (* use the external state to restrict the ghost moves *)
  join_sub (Some (ext_ref ora, NoneP) :: nil) C ->
  joins (ghost_of (m_phi m)) (ghost_approx m C) ->
  exists m' : juicy_mem, joins (ghost_of (m_phi m')) ((ghost_approx m) C) /\
    jm_update m m' /\ P m'.

Lemma jm_bupd_ora : forall {Z} (ora : Z) (P : juicy_mem -> Prop) m,
  (joins (ghost_of (m_phi m)) (Some (ext_ref ora, NoneP) :: nil) -> jm_bupd ora P m) ->
  jm_bupd ora P m.
Proof.
  repeat intro.
  apply H; auto.
  eapply joins_comm, join_sub_joins_trans, joins_comm, H1.
  destruct H0 as [? J]; eapply ghost_fmap_join in J; eexists; eauto.
Qed.

Lemma jm_bupd_intro: forall {Z} (ora : Z) (P : juicy_mem -> Prop) m, P m -> jm_bupd ora P m.
Proof.
  repeat intro.
  eexists; split; eauto; repeat split; auto.
Qed.

Lemma jm_bupd_intro_strong: forall {Z} (ora : Z) (P : juicy_mem -> Prop) m, 
  (joins (ghost_of (m_phi m)) (Some (ext_ref ora, NoneP) :: nil) -> P m) -> jm_bupd ora P m.
Proof.
  intros; apply jm_bupd_ora.
  intros; apply jm_bupd_intro; auto.
Qed.

Lemma jm_bupd_mono_strong : forall {Z} (ora : Z) (P1 P2 : juicy_mem -> Prop) m, jm_bupd ora P1 m ->
  (forall m', jm_update m m' -> joins (ghost_of (m_phi m')) (Some (ext_ref ora, NoneP) :: nil) -> P1 m' -> P2 m') ->
  jm_bupd ora P2 m.
Proof.
  intros ?????? Hmono.
  intros ? HC J.
  destruct (H _ HC J) as (? & J' & ? & ?).
  do 2 eexists; eauto; split; auto.
  apply Hmono; auto.
  eapply joins_comm, join_sub_joins_trans, joins_comm, J'.
  destruct HC as [? Je]; eapply ghost_fmap_join in Je; eexists; eauto.
Qed.

Lemma jm_bupd_mono : forall {Z} (ora : Z) (P1 P2 : juicy_mem -> Prop) m, jm_bupd ora P1 m ->
  (forall m', jm_update m m' -> P1 m' -> P2 m') -> jm_bupd ora P2 m.
Proof.
  intros; eapply jm_bupd_mono_strong; eauto.
Qed.

Lemma ext_join_approx : forall {Z} (z : Z) n g,
  joins g (Some (ghost_PCM.ext_ref z, NoneP) :: nil) ->
  joins (ghost_fmap (approx n) (approx n) g) (Some (ghost_PCM.ext_ref z, NoneP) :: nil).
Proof.
  intros.
  destruct H.
  change (Some (ghost_PCM.ext_ref z, NoneP) :: nil) with
    (ghost_fmap (approx n) (approx n) (Some (ghost_PCM.ext_ref z, NoneP) :: nil)).
  eexists; apply ghost_fmap_join; eauto.
Qed.

Lemma ext_join_sub_approx : forall {Z} (z : Z) n g,
  join_sub (Some (ghost_PCM.ext_ref z, NoneP) :: nil) g ->
  join_sub (Some (ghost_PCM.ext_ref z, NoneP) :: nil) (ghost_fmap (approx n) (approx n) g).
Proof.
  intros.
  destruct H.
  change (Some (ghost_PCM.ext_ref z, NoneP) :: nil) with
    (ghost_fmap (approx n) (approx n) (Some (ghost_PCM.ext_ref z, NoneP) :: nil)).
  eexists; apply ghost_fmap_join; eauto.
Qed.

Lemma ext_join_unapprox : forall {Z} (z : Z) n g,
  joins (ghost_fmap (approx n) (approx n) g) (Some (ghost_PCM.ext_ref z, NoneP) :: nil) ->
  joins g (Some (ghost_PCM.ext_ref z, NoneP) :: nil).
Proof.
  intros.
  destruct H as (g' & J).
  destruct g; [eexists; constructor|].
  inv J.
  exists (a3 :: g); repeat constructor.
  destruct o; inv H4; constructor.
  destruct p; inv H1; constructor; simpl in *; auto.
  destruct p; simpl in *.
  inv H0.
  inv H1.
  inj_pair_tac.
  constructor; auto.
  unfold NoneP; f_equal; auto.
Qed.

Lemma jm_bupd_ext : forall {Z} (ora : Z) (P : juicy_mem -> Prop) m m', jm_bupd ora P m ->
  ext_order m m' ->
  (forall a b, level a = level m -> ext_order a b -> joins (ghost_of (m_phi b)) (Some (ext_ref ora, NoneP) :: nil) ->
      P a -> P b) ->
  jm_bupd ora P m'.
Proof.
  intros ????? H [? Hext] Hclosed ? Hora H1.
  apply rmap_order in Hext as (Hl & Hr & [? J]).
  destruct H1 as [d J'].
  destruct (join_assoc J J') as (c' & ? & Jc').
  eapply ghost_fmap_join in Jc'; rewrite ghost_of_approx in Jc'.
  destruct (H c') as (m'' & Jm'' & (? & Hl'' & ?) & ?).
  { eapply ext_join_sub_approx in Hora.
    eapply join_sub_trans; eauto.
    eexists; eauto. }
  { rewrite level_juice_level_phi; eauto. }
  assert (level m'' = level m') as Hl'.
  { rewrite <- !level_juice_level_phi in *; congruence. }
  exists m''; repeat split; auto; try congruence.
  eapply join_sub_joins'; eauto.
  { apply join_sub_refl. }
  eapply ghost_fmap_join in H1; rewrite ghost_fmap_fmap, 2approx_oo_approx in H1.
  rewrite <- Hl'', Hl'; eexists; eauto.
Qed.

Lemma make_join_ext : forall {Z} (ora : Z) a c n,
  join_sub (Some (ext_ref ora, NoneP) :: nil) c ->
  joins (ghost_fmap (approx n) (approx n) a) (ghost_fmap (approx n) (approx n) c) ->
  join_sub (Some (ext_ref ora, NoneP) :: nil) (make_join a c).
Proof.
  destruct a; auto; simpl.
  intros ?? [? HC] [? J].
  inv J.
  { destruct c; inv H1; inv HC. }
  destruct c; inv H1.
  inv H2.
  { destruct o; inv H0; inv HC.
    * eexists; constructor; constructor.
    * eexists; constructor; eauto; constructor. }
  { destruct o0; inv H1; inv HC.
    inv H3. }
  destruct o as [[]|], o0 as [[]|]; inv H; inv H0.
  destruct a0; inv H1; simpl in *.
  inv H0.
  assert (@ghost.valid (ext_PCM Z) (None, None)) as Hv.
  { simpl; auto. }
  inv HC.
  - eexists; constructor; constructor.
    destruct p; inv H1; inj_pair_tac.
    instantiate (1 := (existT _ (ext_PCM Z) (exist _ _ Hv), _)); repeat constructor; simpl.
    rewrite <- H0; auto.
  - inv H6.
    + destruct p; inv H1; inj_pair_tac.
      eexists; constructor; constructor.
      instantiate (1 := (existT _ (ext_PCM Z) (exist _ _ Hv), _)); repeat constructor; simpl.
      rewrite <- H0; auto.
    + destruct a0; inv H5; simpl in *.
      inv H2.
      destruct p; inv H1; inj_pair_tac.
      eexists; constructor; constructor.
      instantiate (1 := (_, _)); constructor; eauto; simpl.
      constructor; eauto.
      unfold NoneP; f_equal.
      rewrite <- H1; auto.
Qed.

Lemma jm_bupd_age : forall {Z} (ora : Z) (P : juicy_mem -> Prop) m m', jm_bupd ora P m ->
  age m m' -> jm_bupd ora (fun m => exists m0, age m0 m /\ P m0) m'.
Proof.
  unfold jm_bupd; intros.
  rewrite (age1_ghost_of _ _ (age_jm_phi H0)) in H2.
  apply ghost_joins_approx in H2 as [J ?].
  rewrite <- (age_level _ _ H0) in *.
  rewrite level_juice_level_phi, ghost_of_approx in J.
  apply H in J as (b & ? & ? & ?).
  apply H2 in H3.
  eapply jm_update_age in H4 as (b' & ? & Hage'); eauto.
  exists b'; split; eauto.
  rewrite (age1_ghost_of _ _ (age_jm_phi Hage')).
  rewrite <- level_juice_level_phi; destruct H4 as (? & -> & _); auto.
  { eapply make_join_ext; eauto. }
Qed.

Lemma ext_join_sub : forall (a b : rmap), ext_order a b -> join_sub a b.
Proof.
  intros.
  rewrite rmap_order in H.
  destruct H as (? & ? & g & ?).
  destruct (make_rmap (resource_at (core a)) (own.ghost_approx a g) (level a)) as (c & Hl & Hr & Hg).
  { extensionality l; unfold compose.
    rewrite <- level_core.
    apply resource_at_approx. }
  { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
  exists c; apply resource_at_join2; auto.
  - congruence.
  - intros; rewrite Hr, <- core_resource_at, H0.
    apply join_comm, core_unit.
  - rewrite Hg, <- (ghost_of_approx a), <- (ghost_of_approx b), <- H.
    apply ghost_fmap_join; auto.
Qed.

Lemma necR_jm_dry : forall m1 m2, necR m1 m2 -> m_dry m1 = m_dry m2.
Proof.
  induction 1; auto.
  - apply age_jm_dry; auto.
  - congruence.
Qed.

Lemma age_to_dry : forall n m, m_dry (age_to.age_to n m) = m_dry m.
Proof.
  intros.
  unfold age_to.age_to.
  remember (level _ - _) as a eqn: Ha; clear Ha.
  revert m; induction a; simpl; auto; intros.
  unfold age_to.age1'; simpl.
  destruct (age1_juicy_mem _) eqn: Hage; auto.
  apply age1_juicy_mem_unpack in Hage as [? <-]; auto.
Qed.

Lemma age_to_phi : forall n m, m_phi (age_to.age_to n m) = age_to.age_to n (m_phi m).
Proof.
  intros.
  unfold age_to.age_to.
  rewrite level_juice_level_phi.
  remember (level _ - _) as a eqn: Ha; clear Ha.
  revert m; induction a; simpl; auto; intros.
  rewrite <- IHa.
  unfold age_to.age1'; simpl.
  destruct (age1 (m_phi _)) eqn: Hage.
  - edestruct can_age1_juicy_mem as [? Hage']; eauto.
    setoid_rewrite Hage'.
    apply age_jm_phi in Hage'.
    unfold age in Hage'; congruence.
  - rewrite age1_juicy_mem_None2; auto.
Qed.

Lemma necR_jm_phi : forall m1 m2, necR m1 m2 <-> m_dry m1 = m_dry m2 /\ necR (m_phi m1) (m_phi m2).
Proof.
  split.
  - intros; split; [apply necR_jm_dry; auto|].
    induction H; auto.
    + constructor; apply age_jm_phi; auto.
    + eapply rt_trans; eauto.
  - intros [].
    remember (m_phi m1) as jm1; remember (m_phi m2) as jm2.
    revert dependent m2; revert dependent m1.
    induction H0; intros; subst; auto.
    + constructor.
      apply age1_juicy_mem_unpack''; auto.
    + erewrite juicy_mem_ext; [apply rt_refl | ..]; auto.
    + assert (m_phi (age_to.age_to (level y) m1) = y).
      { rewrite age_to_phi.
        symmetry; apply age_to.necR_age_to; auto. }
      eapply rt_trans; [apply (IHclos_refl_trans1 _ eq_refl (age_to.age_to (level y) m1)) | apply IHclos_refl_trans2]; auto;
        rewrite age_to_dry; auto.
Qed.

(* Just like we reserve ghost name 0 for the external ghost, we reserve 1-3 for invariants/world satisfaction.
  We'll have to prove that this isn't vacuous somewhere in the soundness proof.
  We could delay the instantiation and be generic in inv_names, but since we know we'll always need it and we get to allocate it
  before the program starts, there's no reason to delay it. *)
#[(*export, after Coq 8.13*)global] Instance inv_names : invG := { g_inv := 1%nat; g_en := 2%nat; g_dis := 3%nat}.

Definition jm_fupd {Z} (ora : Z) (E1 E2 : Ensembles.Ensemble gname) P m :=
  forall m' w z, necR m m' -> join (m_phi m') w (m_phi z) -> mem_sub (m_dry m') (m_dry z) ->
    app_pred (wsat * ghost_set g_en E1) w ->
  jm_bupd ora (fun z2 => level z2 = 0 \/ exists m2 w2, join (m_phi m2) w2 (m_phi z2) /\
    mem_sub (m_dry m2) (m_dry z2) /\
    app_pred (wsat * ghost_set g_en E2) w2 /\ P m2) z.

Lemma jm_fupd_ora : forall {Z} (ora : Z) E1 E2 (P : juicy_mem -> Prop) m,
  (joins (ghost_of (m_phi m)) (Some (ext_ref ora, NoneP) :: nil) -> jm_fupd ora E1 E2 P m) ->
  jm_fupd ora E1 E2 P m.
Proof.
  intros ??????????????.
  apply jm_bupd_ora; intros J.
  eapply H; eauto.
  eapply join_sub_joins_trans in J; [|eexists; apply ghost_of_join; eauto].
  erewrite necR_ghost_of in J by (apply necR_jm_phi; eauto).
  apply ext_join_unapprox in J; auto.
Qed.

Lemma jm_fupd_intro: forall {Z} (ora : Z) E (P : juicy_mem -> Prop) m (HP : forall a b, P a -> necR a b -> P b),
  P m -> jm_fupd ora E E P m.
Proof.
  intros.
  intros ???????.
  apply jm_bupd_intro; eauto 8.
Qed.

Lemma jm_fupd_intro_strong: forall {Z} (ora : Z) E (P : juicy_mem -> Prop) m (HP : forall a b, P a -> necR a b -> P b),
  (joins (ghost_of (m_phi m)) (Some (ext_ref ora, NoneP) :: nil) -> P m) -> jm_fupd ora E E P m.
Proof.
  intros.
  apply jm_fupd_ora; intros.
  apply jm_fupd_intro; auto.
Qed.

Lemma jm_fupd_age : forall {Z} (ora : Z) E1 E2 (P : juicy_mem -> Prop) m m', jm_fupd ora E1 E2 P m ->
  age m m' -> jm_fupd ora E1 E2 P m'.
Proof.
  intros.
  intros ???????.
  eapply H; [| eauto | eauto | eauto].
  eapply necR_trans; [|eauto].
  constructor; auto.
Qed.

Lemma jm_fupd_mono_strong : forall {Z} (ora : Z) E1 E2 (P1 P2 : juicy_mem -> Prop) m, jm_fupd ora E1 E2 P1 m ->
  (forall m', level m' <= level m -> joins (ghost_of (m_phi m')) (Some (ext_ref ora, NoneP) :: nil) -> P1 m' -> P2 m') ->
  jm_fupd ora E1 E2 P2 m.
Proof.
  intros ???????? Hmono.
  intros ??? Hlater J ? HW.
  eapply H in HW; eauto.
  eapply jm_bupd_mono_strong; eauto.
  intros ?? J' [|(? & ? & J2 & ? & ? & ?)]; eauto.
  right; do 3 eexists; eauto; split; auto; split; auto.
  apply Hmono; auto.
  - apply necR_level in Hlater.
    apply join_level in J as [Hl ?].
    rewrite <- !level_juice_level_phi in Hl.
    apply join_level in J2 as [Hl2 ?].
    rewrite <- !level_juice_level_phi in Hl2.
    destruct H1; lia.
  - eapply join_sub_joins_trans; eauto.
    eexists; apply ghost_of_join; eauto.
Qed.

Lemma jm_fupd_mono : forall {Z} (ora : Z) E1 E2 (P1 P2 : juicy_mem -> Prop) m, jm_fupd ora E1 E2 P1 m ->
  (forall m', level m' <= level m -> P1 m' -> P2 m') -> jm_fupd ora E1 E2 P2 m.
Proof.
  intros; eapply jm_fupd_mono_strong; eauto.
Qed.

Lemma jm_fupd_ext : forall {Z} (ora : Z) E1 E2 (P : juicy_mem -> Prop) m m', jm_fupd ora E1 E2 P m ->
  ext_order m m' ->
  (forall a b, level a <= level m -> ext_order a b -> joins (ghost_of (m_phi b)) (Some (ext_ref ora, NoneP) :: nil) ->
      P a -> P b) ->
  jm_fupd ora E1 E2 P m'.
Proof.
  intros ??????? H [? Hext] Hclosed ??? Hnec Hj ? Hwsat.
  assert (exists z0, join (m_phi (age_to.age_to (level m'0) m)) w (m_phi z0) /\ ext_order z0 z) as (z0 & Hz0 & ?).
  - eapply nec_ext_commut in Hext as [? Hext' Hnec']; [|apply necR_jm_phi; eauto].
    eapply join_ext_commut in Hj as (z0 & ? & Hext''); eauto.
    destruct (juicy_mem_resource z z0) as (jz0 & ? & ?); subst.
    { apply rmap_order in Hext'' as (? & ? & ?); auto. }
    apply age_to.necR_age_to in Hnec'.
    apply rmap_order in Hext' as (Hl' & _); rewrite Hl' in Hnec'; subst.
    rewrite age_to_phi in *.
    exists jz0; split; auto; split; auto.
  - assert (mem_sub (m_dry (age_to.age_to (level m'0) m)) (m_dry z0)) as Hmem'.
    { rewrite age_to_dry; destruct H2 as [->].
      erewrite H0, necR_jm_dry; eauto. }
    specialize (H _ _ _ (age_to.age_to_necR _ _) Hz0 Hmem' Hwsat).
    eapply jm_bupd_ext; [eapply H; eauto | eauto |].
    apply rmap_order in Hext as (Hl & _); intros ??? [Hdry Hext] ? [? | (? & ? & Hsub & ? & ? & HP)].
    { rewrite level_juice_level_phi in *.
      apply rmap_order in Hext as (<- & ? & ?); auto. }
    pose proof (ext_join_sub _ _ Hext) as [g Hsub'].
    apply rmap_order in Hext as (_ & Hr' & _).
    destruct (join_assoc (join_comm Hsub) Hsub') as (? & J' & ?%join_comm).
    assert (forall c d, join c g d -> resource_at c = resource_at d) as Hid.
    { intros ?? J1; extensionality l.
      apply (resource_at_join _ _ _ l) in J1.
      apply (resource_at_join _ _ _ l) in Hsub'.
      rewrite Hr' in Hsub'.
      apply join_comm, unit_identity in Hsub'.
      eapply Hsub'; eauto. }
    destruct (juicy_mem_resource x x1) as (? & ? & Hmem''); subst.
    { symmetry; apply Hid; auto. }
    right; do 3 eexists; eauto; split; auto.
    { rewrite <- Hdry, Hmem''; auto. }
    split; auto.
    eapply Hclosed, HP.
    + rewrite !level_juice_level_phi in *; rewrite Hl.
      apply join_level in Hj as [].
      destruct H2 as [? Hext]; apply rmap_order in Hext as (? & _).
      apply join_level in Hsub as [].
      apply necR_level in Hnec.
      rewrite !level_juice_level_phi in *; lia.
    + split; auto.
      apply rmap_order.
      split; [apply join_level in J' as []; auto|].
      split; [|eexists; apply ghost_of_join; eauto]; auto.
    + eapply join_sub_joins_trans; [eexists; apply ghost_of_join; eauto | auto].
Qed.

Section juicy_safety.
  Context {G C Z:Type}.
  Context {genv_symb: G -> injective_PTree block}.
  Context (Hcore:@CoreSemantics C mem).
  Variable (Hspec : juicy_ext_spec Z).
  Variable ge : G.

  Definition Hrel m m' :=
    (level m' < level m)%nat /\
    pures_eq (m_phi m) (m_phi m').

  (* try without N, using level instead *)
  Inductive jsafeN_:
    Z -> C -> juicy_mem -> Prop :=
  | jsafeN_0: forall z c m, level m = 0 -> jsafeN_ z c m
  (* c.f. iRC11's language, in which NA reads and writes are atomic
     and can access invariants. All our concurrency features are
     outside corestep/jstep, so they can provide their own specs
     if they want to access invariants. So we just need to allow
     fupds between steps. *)
  | jsafeN_step:
      forall z c m c' m',
      jstep Hcore c m c' m' ->
        (* For full generality, we'd parameterize by a mask E here, but that would
           have to propagate all the way up to semax. *)
        jm_fupd z Ensembles.Full_set Ensembles.Full_set (jsafeN_ z c') m' ->
      jsafeN_ z c m
  | jsafeN_external:
      forall z c m e args x,
      j_at_external Hcore c m = Some (e,args) ->
      ext_spec_pre Hspec e x (genv_symb ge) (sig_args (ef_sig e)) args z m ->
      (forall ret m' z'
         (Hargsty : Val.has_type_list args (sig_args (ef_sig e)))
         (Hretty : Builtins0.val_opt_has_rettype  ret (sig_res (ef_sig e))),
         Hrel m m' ->
         ext_spec_post Hspec e x (genv_symb ge) (sig_res (ef_sig e)) ret z' m' ->
         exists c',
           semantics.after_external Hcore ret c (m_dry m') = Some c' /\
           jm_fupd z' Ensembles.Full_set Ensembles.Full_set (jsafeN_ z' c') m') ->
      jsafeN_ z c m
  | jsafeN_halted:
      forall z c m i,
      semantics.halted Hcore c i ->
      ext_spec_exit Hspec (Some (Vint i)) z m ->
      jsafeN_ z c m.

Lemma age_jstep : forall c m c' m' m1, jstep Hcore c m c' m' ->
  age m m1 -> level m1 <> 0 -> exists m1', age m' m1' /\ jstep Hcore c m1 c' m1'.
Proof.
  unfold jstep.
  intros ????? (? & ? & ? & Hg) Hage Hl.
  destruct (level m') eqn: Hm'.
  { apply age_level in Hage; lia. }
  symmetry in Hm'; destruct (levelS_age _ _ Hm') as (m1' & Hage' & ?); subst.
  exists m1'; split; auto.
  rewrite <- (age_jm_dry Hage), <- (age_jm_dry Hage'); split; auto.
  split; [|split].
  - eapply age_resource_decay; eauto; try (apply age_jm_phi; auto).
    rewrite <- !level_juice_level_phi; lia.
  - apply age_level in Hage; lia.
  - rewrite (age1_ghost_of _ _ (age_jm_phi Hage')), (age1_ghost_of _ _ (age_jm_phi Hage)), Hg.
    rewrite !ghost_fmap_fmap.
    apply age_level in Hage.
    rewrite approx_oo_approx', approx'_oo_approx, approx_oo_approx', approx'_oo_approx; rewrite <- level_juice_level_phi; try lia; auto.
Qed.

Lemma age_pures_eq : forall m1 m2, age m1 m2 -> pures_eq m1 m2.
Proof.
  split; [unfold pures_sub|]; intros l; erewrite (age1_resource_at _ _ H); try (symmetry; apply resource_at_approx);
    destruct (m1 @ l); simpl; eauto.
Qed.

Lemma age_safe:
  forall jm jm0, age jm0 jm ->
  forall ora c,
   jsafeN_ ora c jm0 ->
   jsafeN_ ora c jm.
Proof.
  intros.
  remember (level jm) as N.
  revert c jm0 jm HeqN H H0; induction N; intros.
  { constructor; auto. }
  inv H0.
  + apply age_level in H; congruence.
  + edestruct age_jstep as (m1' & ? & Hstep); eauto.
    { lia. }
    eapply jsafeN_step; eauto.
    eapply jm_fupd_mono; [eapply jm_fupd_age; eauto | auto].
  + eapply jsafeN_external; eauto.
    { unfold j_at_external in *.
      rewrite <- (age_jm_dry H); eauto. }
    { eapply JE_pre_hered; eauto. }
    intros.
    destruct (H3 ret m' z') as [c' [? ?]]; auto.
    - assert (level (m_phi jm) < level (m_phi jm0)).
      {
        apply age_level in H.
        do 2 rewrite <-level_juice_level_phi.
        destruct H0.
        rewrite H; lia.
      }
      destruct H0 as (?&?).
      split; [do 2 rewrite <-level_juice_level_phi in H5; lia |].
      eapply pures_eq_trans, H6.
      { rewrite <- !level_juice_level_phi; lia. }
      apply age_pures_eq, age_jm_phi; auto.
    - exists c'; split; auto.
  + unfold j_halted in *.
    eapply jsafeN_halted; eauto.
    eapply JE_exit_hered; eauto.
Qed.

Lemma resource_decay_resource : forall b x x' y, resource_decay b x x' ->
  level x = level y -> resource_at x = resource_at y ->
  exists y', resource_decay b y y' /\ level y' = level x' /\
    resource_at x' = resource_at y' /\ ghost_of y' = own.ghost_approx y' (ghost_of y).
Proof.
  intros.
  destruct (make_rmap (resource_at x') (own.ghost_approx (level x') (ghost_of y)) (level x')) as (y' & Hl & Hr & Hg).
  { extensionality; apply resource_at_approx. }
  { rewrite ghost_fmap_fmap, !approx_oo_approx; reflexivity. }
  rewrite <- Hl in Hg.
  exists y'; split; [|repeat split; auto].
  unfold resource_decay in *.
  destruct H.
  rewrite Hr, <- H1, Hl, <- H0; auto.
Qed.

Lemma ext_jstep : forall c m c' m' m1, jstep Hcore c m c' m' ->
  ext_order m m1 -> exists m1', ext_order m' m1' /\ jstep Hcore c m1 c' m1'.
Proof.
  unfold jstep.
  intros ????? (? & Hr & ? & Hg) [Hdry Hext].
  apply rmap_order in Hext as (Hl1 & Hr1 & ? & Hg1).
  eapply resource_decay_resource in Hr as (m1' & ? & Hl' & Hr' & Hg'); eauto.
  symmetry in Hr'; destruct (juicy_mem_resource _ _ Hr') as (jm' & ? & Hdry'); subst.
  exists jm'.
  rewrite <- Hdry, Hdry'; split.
  { split; [congruence|].
    apply rmap_order; split; auto.
    split; auto.
    rewrite Hg, Hg', Hl', level_juice_level_phi.
    eexists; apply ghost_fmap_join; eauto. }
  split; auto; split; auto; split; auto.
  rewrite !level_juice_level_phi in *; lia.
Qed.

Lemma ext_safe:
  forall jm jm0, ext_order jm0 jm ->
  forall ora c,
   joins (ghost_of (m_phi jm)) (Some (ext_ref ora, NoneP) :: nil) ->
   jsafeN_ ora c jm0 ->
   jsafeN_ ora c jm.
Proof.
  intros ????? Hext ?.
  remember (level jm0) as N.
  revert dependent c; revert dependent jm0; revert dependent jm; induction N as [? IHN] using lt_wf_ind; intros.
  inv H0.
  - constructor. destruct H as [_ H]; apply rmap_order in H as [? _].
    rewrite <- !level_juice_level_phi in *; congruence.
  - eapply ext_jstep in H as (? & ? & ?); eauto.
    eapply jsafeN_step; eauto.
    eapply jm_fupd_ext; eauto; intros.
    eapply IHN; eauto.
    destruct H1 as (_ & _ & ? & _).
    rewrite !level_juice_level_phi in *; lia.
  - eapply jsafeN_external; eauto.
    + unfold j_at_external in *.
      destruct H as [<-]; eauto.
    + eapply JE_pre_ext; eauto.
    + intros.
      apply H3; auto.
      unfold Hrel in *.
      destruct H0 as (? & ?).
      destruct H as [_ H]; apply rmap_order in H as (? & Hr & _).
      split; [rewrite !level_juice_level_phi in *; lia|].
      unfold pures_eq, pures_sub in *.
      rewrite Hr; auto.
  - eapply jsafeN_halted; eauto.
    eapply JE_exit_ext; eauto.
Qed.

Lemma necR_safe : forall jm jm0, necR jm0 jm ->
  forall ora c,
   jsafeN_ ora c jm0 ->
   jsafeN_ ora c jm.
Proof.
  induction 1; auto.
  apply age_safe; auto.
Qed.


Lemma jsafe_corestep_backward:
    forall c m c' m' z,
    jstep Hcore c m c' m' ->
    jsafeN_ z c' m' -> jsafeN_ z c m.
  Proof.
    intros; eapply jsafeN_step; eauto.
    apply jm_fupd_intro; auto.
    intros; eapply necR_safe; eauto.
  Qed.

(*  Lemma jsafe_corestepN_forward:
    corestep_fun Hcore ->
    forall z c m c' m' n n0,
      semantics_lemmas.corestepN (juicy_core_sem Hcore) ge n0 c m c' m' ->
      jsafeN_ (n + S n0) z c m ->
      jm_bupd (jsafeN_ n z c') m'.
  Proof.
    intros.
    revert c m c' m' n H0 H1.
    induction n0; intros; auto.
    simpl in H0; inv H0.
    apply jm_bupd_intro.
    eapply jsafe_downward in H1; eauto. lia.
    simpl in H0. destruct H0 as [c2 [m2 [STEP STEPN]]].
    assert (Heq: (n + S (S n0) = S (n + S n0))%nat) by lia.
    rewrite Heq in H1.
    eapply jsafe_corestep_forward in H1; eauto.
    specialize (H1 nil); spec H1.
    { eexists; simpl; erewrite <- ghost_core.
      apply join_comm, core_unit. }
    destruct H1 as (? & ? & ? & ?).
    eapply (IHn0 _ _ _ _ n).
  Qed.*)

  Lemma jsafe_step'_back2 :
    forall
      {ora st m st' m'},
      jstep Hcore st m st' m' ->
      jsafeN_ ora st' m' ->
      jsafeN_ ora st m.
  Proof.
    intros.
    eapply jsafe_corestep_backward; eauto.
  Qed.

  Lemma jsafe_corestepN_backward:
    forall z c m c' m' n0,
      semantics_lemmas.corestepN (juicy_core_sem Hcore) n0 c m c' m' ->
      jsafeN_ z c' m' ->
      jsafeN_ z c m.
  Proof.
    simpl; intros.
    revert c m c' m' H H0.
    induction n0; intros; auto.
    simpl in H; inv H; auto.
    simpl in H. destruct H as [c2 [m2 [STEP STEPN]]].
    specialize (IHn0 _ _ _ _ STEPN H0).
    solve[eapply jsafe_step'_back2; eauto].
  Qed.

  Lemma convergent_controls_jsafe :
    forall m q1 q2,
      (j_at_external Hcore q1 m = j_at_external Hcore q2 m) ->
      (forall ret m q', semantics.after_external Hcore ret q1 m = Some q' ->
                      semantics.after_external Hcore ret q2 m = Some q') ->
      (semantics.halted Hcore q1 = semantics.halted Hcore q2) ->
      (forall q' m', jstep Hcore q1 m q' m' ->
                     jstep Hcore q2 m q' m') ->
      (forall z, jsafeN_ z q1 m -> jsafeN_ z q2 m).
  Proof.
    intros.
    inv H3.
    + constructor; auto.
    + eapply jsafeN_step; eauto.
    + eapply jsafeN_external; eauto.
      rewrite <-H; eauto.
      intros ??? Hargsty Hretty ? H8.
      specialize (H6 _ _ _ Hargsty Hretty H3 H8).
      destruct H6 as [c' [? ?]].
      exists c'; split; auto.
    + eapply jsafeN_halted; eauto.
      rewrite <-H1; auto.
  Qed.

  Lemma wlog_jsafeN_gt0 : forall
    z q m,
    (level m > 0 -> jsafeN_ z q m) ->
    jsafeN_ z q m.
  Proof.
    intros. destruct (level m) eqn: Hl. constructor; auto.
    apply H. lia.
  Qed.

  Lemma jm_fupd_intro' : forall (ora : Z) E (c : C) m,
    jsafeN_ ora c m ->
    jm_fupd ora E E (jsafeN_ ora c) m.
  Proof.
    intros; apply jm_fupd_intro; auto.
    intros; eapply necR_safe; eauto.
  Qed.

  Lemma jm_fupd_intro_strong' : forall (ora : Z) E (c : C) m,
    (joins (ghost_of (m_phi m)) (Some (ext_ref ora, NoneP) :: nil) -> jsafeN_ ora c m) ->
    jm_fupd ora E E (jsafeN_ ora c) m.
  Proof.
    intros; apply jm_fupd_intro_strong; auto.
    intros; eapply necR_safe; eauto.
  Qed.

End juicy_safety.

Lemma juicy_core_sem_preserves_corestep_fun
  {C} (csem: @CoreSemantics C mem) :
  corestep_fun csem ->
  corestep_fun (juicy_core_sem csem).
Proof.
  intros determinism jm q jm1 q1 jm2 q2 step1 step2.
  destruct step1 as [step1 [[ll1 rd1] [l1 g1]]].
  destruct step2 as [step2 [[ll2 rd2] [l2 g2]]].
  pose proof determinism _ _ _ _ _ _ step1 step2 as E.
  injection E as <- E; f_equal.
  apply juicy_mem_ext; auto.
  assert (El: level jm1 = level jm2) by (clear -l1 l2; lia).
  apply rmap_ext. now do 2 rewrite <-level_juice_level_phi; auto.
  intros l.
  specialize (rd1 l); specialize (rd2 l).
  rewrite level_juice_level_phi in *.
  destruct jm  as [m  phi  jmc  jmacc  jmma  jmall ].
  destruct jm1 as [m1 phi1 jmc1 jmacc1 jmma1 jmall1].
  destruct jm2 as [m2 phi2 jmc2 jmacc2 jmma2 jmall2].
  simpl in *.
  subst m2; rename m1 into m'.
  destruct rd1 as [jmno [E1 | [[sh1 [rsh1 [v1 [v1' [E1 E1']]]]] | [[pos1 [v1 E1]] | [v1 [pp1 [E1 E1']]]]]]];
  destruct rd2 as [_    [E2 | [[sh2 [rsh2 [v2 [v2' [E2 E2']]]]] | [[pos2 [v2 E2]] | [v2 [pp2 [E2 E2']]]]]]];
  try pose proof jmno pos1 as phino; try pose proof (jmno pos2) as phino; clear jmno;
    remember (phi  @ l) as x ;
    remember (phi1 @ l) as x1;
    remember (phi2 @ l) as x2;
    subst.

  - (* phi1: same   | phi2: same   *)
    congruence.

  - (* phi1: same   | phi2: update *)
    rewrite <- E1, El.
    rewrite El in E1.
    rewrite E1 in E2.
    destruct (jmc1 _ _ _ _ _ E2).
    destruct (jmc2 _ _ _ _ _ E2').
    congruence.

  - (* phi1: same   | phi2: alloc  *)
    exfalso.
    rewrite phino in E1. simpl in E1.
    specialize (jmacc1 l).
    rewrite <- E1 in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    specialize (jmacc2 l).
    rewrite E2 in jmacc2.
    simpl in jmacc2.
    rewrite jmacc1 in jmacc2.
    clear -jmacc2. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; try congruence. contradiction Share.nontrivial.
  - (* phi1: same   | phi2: free   *)
    exfalso.
    rewrite E2 in E1.
    simpl in E1.
    specialize (jmacc1 l).
    rewrite <- E1 in jmacc1.
    simpl in jmacc1.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc1 in jmacc2.
    clear -jmacc2. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; try congruence. contradiction Share.nontrivial.
  - (* phi1: update | phi2: same   *)
    rewrite <- E2, <-El.
    rewrite <-El in E2.
    rewrite E2 in E1.
    destruct (jmc1 _ _ _ _ _ E1').
    destruct (jmc2 _ _ _ _ _ E1).
    congruence.

  - (* phi1: update | phi2: update *)
    destruct (jmc1 _ _ _ _ _ E1').
    destruct (jmc2 _ _ _ _ _ E2').
    rewrite E1', E2'.
    destruct (phi@l); inv E1; inv E2.
    f_equal. apply proof_irr.
  - (* phi1: update | phi2: alloc  *)
    rewrite phino in E1.
    simpl in E1.
    inversion E1.

  - (* phi1: update | phi2: free   *)
    exfalso.
    rewrite E2 in E1.
    simpl in E1.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc1 in jmacc2.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; try congruence.  
  - (* phi1: alloc  | phi2: same   *)
    exfalso.
    rewrite phino in E2. simpl in E2.
    specialize (jmacc2 l).
    rewrite <- E2 in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    specialize (jmacc1 l).
    rewrite E1 in jmacc1.
    simpl in jmacc1.
    rewrite jmacc2 in jmacc1.
    clear -jmacc1.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; try congruence. contradiction Share.nontrivial. 
  - (* phi1: alloc  | phi2: update *)
    rewrite phino in E2.
    simpl in E2.
    inversion E2.

  - (* phi1: alloc  | phi2: alloc  *)
    destruct (jmc1 _ _ _ _ _ E1).
    destruct (jmc2 _ _ _ _ _ E2).
    congruence.

  - (* phi1: alloc  | phi2: free   *)
    congruence.

  - (* phi2: free   | phi2: same   *)
    exfalso.
    rewrite E1 in E2.
    simpl in E2.
    specialize (jmacc2 l).
    rewrite <- E2 in jmacc2.
    simpl in jmacc2.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc2 in jmacc1.
    clear -jmacc1. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; try congruence. contradiction Share.nontrivial.  
  - (* phi2: free   | phi2: update *)
    exfalso.
    rewrite E1 in E2.
    simpl in E2.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc2 in jmacc1.
    clear -jmacc1 rsh2.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; try congruence.
  - (* phi2: free   | phi2: alloc  *)
    congruence.

  - (* phi2: free   | phi2: free   *)
    congruence.
  - congruence.
Qed.
