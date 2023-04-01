From iris.bi Require Export derived_connectives.
Require Import VST.veric.juicy_base.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.shares.
(*Require Import VST.veric.juicy_safety.*)
Require Import VST.veric.ghost_map.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.external_state.

Require Import VST.veric.tycontext.

Local Open Scope nat_scope.

Section mpred.

Context `{!heapGS Σ}.

(* predicates on juicy memories *)
Global Instance mem_inhabited : Inhabited Memory.mem := {| inhabitant := Mem.empty |}.
Definition mem_index : biIndex := {| bi_index_type := mem |}.

Definition jmpred := monPred mem_index (iPropI Σ).

(*Program Definition jmpred_of (P : juicy_mem -> Prop) : jmpred := {| monPred_at m := P |}.*)
(* Do we need to explicitly include the step-index in the jm? *)

(* Should we track the current memory, or re-quantify over one consistent with the rmap? *)
Record juicy_mem := { level : nat; m_dry : mem; m_phi : rmap }.

Definition jm_mono (P : juicy_mem -> Prop) := forall jm n2 x2, P jm -> m_phi jm ≼ₒ{level jm} x2 ->
  n2 <= level jm -> P {| level := n2; m_dry := m_dry jm; m_phi := x2 |}.

Definition jmpred_of P (Hmono : jm_mono P) : jmpred.
Proof.
  unshelve eexists.
  intros m; unshelve eexists.
  exact (λ n phi, P {| level := n; m_dry := m; m_phi := phi |} ).
  - simpl; intros.
    eapply Hmono in H; eauto.
  - apply _.
Defined.

Record juicy_ext_spec (Z: Type) := {
  JE_spec :> external_specification juicy_mem external_function Z;
  JE_pre_mono: forall e t ge_s typs args z, jm_mono (ext_spec_pre JE_spec e t ge_s typs args z);
  JE_post_mono: forall e t ge_s tret rv z, jm_mono (ext_spec_post JE_spec e t ge_s tret rv z);
  JE_exit_mono: forall rv z, jm_mono (ext_spec_exit JE_spec rv z)
}.

Definition ext_jmpred_pre Z JE_spec e t ge_s typs args z : jmpred := jmpred_of _ (JE_pre_mono Z JE_spec e t ge_s typs args z).
Definition ext_jmpred_post Z JE_spec e t ge_s tret rv z : jmpred := jmpred_of _ (JE_post_mono Z JE_spec e t ge_s tret rv z).
Definition ext_jmpred_exit Z JE_spec rv z : jmpred := jmpred_of _ (JE_exit_mono Z JE_spec rv z).

Class OracleKind := {
  OK_ty : Type;
  OK_spec: juicy_ext_spec OK_ty
}.

(*! The void ext_spec *)
Definition void_spec T : external_specification juicy_mem external_function T :=
    Build_external_specification
      juicy_mem external_function T
      (fun ef => False%type)
      (fun ef Hef ge tys vl m z => False%type)
      (fun ef Hef ge ty vl m z => False%type)
      (fun rv m z => False%type).

Definition ok_void_spec (T : Type) : OracleKind.
 refine (Build_OracleKind T (Build_juicy_ext_spec _ (void_spec T) _ _ _)).
Proof.
  simpl; intros; contradiction.
  simpl; intros; contradiction.
  simpl; intros ???; contradiction.
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

(*Definition jstep {C} (csem: @CoreSemantics C mem)
  (q: C) (q': C) (jm': juicy_mem) (jm : juicy_mem) : Prop :=
 corestep csem q (m_dry jm) q' (m_dry jm') /\
 resource_decay (level jm') (nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\
 level jm = S (level jm') (*/\
  Really, what we want is "nothing has changed in the rmap except the changes related to the mem ops".
  We can state this by indexing into the rmap, but...
 ghost_of (m_phi jm') = ghost_approx jm' (ghost_of (m_phi jm))*).*)

(*Definition jstep {C} (csem: @CoreSemantics C mem)
  (q: C) (q': C) (jm': juicy_mem) (jm : juicy_mem) : Prop :=
 corestep csem q (m_dry jm) q' (m_dry jm').*)

Definition j_halted {C} (csem: @CoreSemantics C mem)
       (c: C) (i: int): Prop :=
     halted csem c i.

(*Lemma jstep_not_at_external {C} (csem: @CoreSemantics C mem):
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
*)

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
    Build_juicy_ext_spec _ (upd_exit'' _ x ge) _ _ _.
  Next Obligation. intros. eapply JE_pre_mono; eauto. Qed.
  Next Obligation. intros. eapply JE_post_mono; eauto. Qed.
  Next Obligation. intros. eapply JE_post_mono; eauto. Qed.
End upd_exit.

Obligation Tactic := Tactics.program_simpl.

(*Program Definition juicy_mem_op (P : pred rmap) : pred juicy_mem :=
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
Qed.*)

(*Definition jm_bupd {Z} (ora : Z) P m := forall C : ghost,
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
Qed.*)

Section juicy_safety.
  Context {G C Z:Type}.
  Context {genv_symb: G -> injective_PTree block}.
  Context (Hcore:@CoreSemantics C mem).
  Variable (Hspec : juicy_ext_spec Z).
  Variable ge : G.

  Context `{!externalGS Z Σ}.

(*  Definition Hrel m m' :=
    (level m' < level m)%nat /\
    pures_eq (m_phi m) (m_phi m'). *)

(*Definition auth_heap phi := ghost_map_auth(H0 := gen_heapGpreS_heap(gen_heapGpreS := gen_heap_inG)) (gen_heap_name heapGS_gen_heapGS) Tsh phi.*)

(* The closest match to the Iris approach would be for auth_heap to hold the true full CompCert mem,
   and to run the underlying semantics without any permissions. But that's a poor fit for VST's approach
   to soundness. Instead, our "authoritative" state is still just the current thread's view of the state. *)

(* Hypothesis: we don't actually need juicy_mem here, and can requantify over the plain mem at every step. *)
(* Hypothesis 2: we don't really need the authoritative rmap either! The point is just that the thread's owned resources
   need to be consistent with the state that steps, which we can get from coherent_with.
   If this is true, then we should probably move away from gen_heap entirely
   and just have the gmap side in heapGS. *)

Definition state_interp m z := mem_auth m ∗ ext_auth z.

Program Definition jsafe_pre
    (jsafe : coPset -d> Z -d> C -d> iPropO Σ) : coPset -d> Z -d> C -d> iPropO Σ := λ E z c,
  |={E}=> ∀ m, state_interp m z -∗
      (∃ i, ⌜halted Hcore c i⌝ ∧ ext_jmpred_exit Z Hspec (Some (Vint i)) z m) ∨
      (▷ ∃ c' m', ⌜corestep Hcore c m c' m'⌝ ∧ |={E}=> state_interp m' z ∗ jsafe E z c') ∨
      (∃ e args x, ⌜at_external Hcore c m = Some (e, args)⌝ ∧ ext_jmpred_pre Z Hspec e x (genv_symb ge) (sig_args (ef_sig e)) args z m ∗
         ▷ □ (∀ ret m' z', ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
          ((ext_jmpred_post Z Hspec e x (genv_symb ge) (sig_res (ef_sig e)) ret z' m') ={E}=∗
          ∃ c', ⌜after_external Hcore ret c m' = Some c'⌝ ∧ state_interp m' z' ∗ jsafe E z' c'))).

Local Instance jsafe_pre_contractive : Contractive jsafe_pre.
Proof.
  rewrite /jsafe_pre => n jsafe jsafe' Hsafe E z c.
  do 6 f_equiv.
  - f_contractive; repeat f_equiv. apply Hsafe.
  - do 8 f_equiv. f_contractive; repeat f_equiv. apply Hsafe.
Qed.

(*Local Definition jsafe_def : Wp (iProp Σ) (expr Λ) (val Λ) stuckness :=
  λ s : stuckness, fixpoint (jsafe_pre s).
It's possible that we could massage this into Iris's WP framework, but it would involve moving z into
the state interpretation and turning ext_spec_exit into a postcondition.
*) 
Local Definition jsafe_def : coPset -> Z -> C -> mpred := fixpoint jsafe_pre.
Local Definition jsafe_aux : seal (@jsafe_def). Proof. by eexists. Qed.
Definition jsafe := jsafe_aux.(unseal).
Local Lemma jsafe_unseal : jsafe = jsafe_def.
Proof. rewrite -jsafe_aux.(seal_eq) //. Qed.

(* basic facts following iris.program_logic.weakestpre *)
Lemma jsafe_unfold E z c : jsafe E z c ⊣⊢ jsafe_pre jsafe E z c.
Proof. rewrite jsafe_unseal. apply (fixpoint_unfold jsafe_pre). Qed.

Lemma fupd_jsafe E z c : (|={E}=> jsafe E z c) ⊢ jsafe E z c.
Proof.
  rewrite jsafe_unfold /jsafe_pre. iIntros ">$".
Qed.

Lemma jsafe_mask_mono E1 E2 z c : E1 ⊆ E2 → jsafe E1 z c ⊢ jsafe E2 z c.
Proof.
  iIntros (?) "H". iLöb as "IH" forall (z c).
  rewrite !jsafe_unfold /jsafe_pre.
  iMod (fupd_mask_subseteq E1) as "Hclose"; iMod "H"; iMod "Hclose" as "_".
  iIntros "!>" (?) "?"; iSpecialize ("H" with "[$]"); iDestruct "H" as "[H | [H | H]]".
  - by iLeft.
  - iRight; iLeft.
    iNext; iDestruct "H" as (???) "H"; iExists _, _; iSplit; first done.
    iMod (fupd_mask_subseteq E1) as "Hclose"; iMod ("H") as "[$ ?]"; iMod "Hclose" as "_".
    by iApply "IH".
  - iRight; iRight.
    iDestruct "H" as (????) "[Hext H]".
    iExists _, _, _; iSplit; first done; iFrame "Hext".
    iIntros "!>"; iDestruct "H" as "#H"; iIntros "!>" (????) "Hext".
    iMod (fupd_mask_subseteq E1) as "Hclose"; iMod ("H" with "[%] Hext") as "H'"; first done; iMod "Hclose" as "_".
    iIntros "!>".
    iDestruct "H'" as (??) "[??]"; iExists _; iFrame "%"; iFrame.
    by iApply "IH".
Qed.

(** Proofmode class instances *)
Section proofmode_classes.
  Implicit Types P Q : iProp Σ.

  Global Instance is_except_0_jsafe E z c : IsExcept0 (jsafe E z c).
  Proof. by rewrite /IsExcept0 -{2}fupd_jsafe -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_jsafe p P E z c :
    ElimModal Logic.True p false (|==> P) P (jsafe E z c) (jsafe E z c).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_jsafe.
  Qed.

  Global Instance elim_modal_fupd_jsafe p P E z c :
    ElimModal Logic.True p false (|={E}=> P) P (jsafe E z c) (jsafe E z c).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_jsafe.
  Qed.

  Global Instance add_modal_fupd_jsafe P E z c :
    AddModal (|={E}=> P) P (jsafe E z c).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_jsafe. Qed.

End proofmode_classes.

Lemma jsafe_local_step:
  forall E ora s1 s2,
  (forall m, corestep Hcore s1 m s2 m) ->
  ▷jsafe E ora s2 ⊢
  jsafe E ora s1.
Proof.
  intros Hfun ????; iIntros "H".
  rewrite (jsafe_unfold _ _ s1) /jsafe_pre.
  iIntros "!>" (?) "?".
  iRight; iLeft.
  iIntros "!>".
  iExists _, _; iSplit; first done.
  by iFrame.
Qed.

Definition jstep E z c c' : mpred := ∀ m, state_interp m z -∗ ◇ ∃ m', ⌜corestep Hcore c m c' m'⌝ ∧ ▷ |={E}=> state_interp m' z ∗ jsafe E z c'.

Lemma jstep_mono : forall E z c1 c2 c', (forall m m', corestep Hcore c1 m c' m' -> corestep Hcore c2 m c' m') ->
  jstep E z c1 c' ⊢ jstep E z c2 c'.
Proof.
  intros; rewrite /jstep.
  iIntros "H" (?) "?".
  iMod ("H" with "[$]") as (??) "?".
  iExists _; iFrame; iPureIntro; split; auto.
Qed.

Lemma jsafe_step_backward:
  forall c c' E z,
  jstep E z c c' ⊢ jsafe E z c.
Proof.
  intros; iIntros "H".
  rewrite jsafe_unfold /jsafe_pre /jstep.
  iIntros "!>" (m) "[m ?]".
  iRight; iLeft.
  iDestruct ("H" with "[$]") as ">(% & %& H)"; eauto.
Qed.

Lemma jsafe_step_forward:
  forall c c1 E z (Hc1 : forall m c' m', corestep Hcore c m c' m' -> c' = c1)
    (Hhalt : forall i, ~halted Hcore c i) (Hext : forall m, at_external Hcore c m = None),
    jsafe E z c ⊢ |={E}=> jstep E z c c1.
Proof.
  intros; iIntros "H".
  rewrite jsafe_unfold /jsafe_pre.
  iMod "H".
  rewrite /jstep; iIntros "!>" (m1) "?".
  iDestruct ("H" with "[$]") as "[H | [H | H]]".
  { iDestruct "H" as (??) "?"; exfalso; eapply Hhalt; eauto. }
  rewrite bi.later_exist_except_0; iMod "H" as (?) "H".
  rewrite bi.later_exist_except_0; iMod "H" as (?) "H".
  rewrite bi.later_and; iDestruct "H" as "[>%Hstep H]".
  rewrite -(Hc1 _ _ _ Hstep).
  iIntros "!>"; iExists _; iSplit; done.
  { iDestruct "H" as (????) "?".
    by rewrite Hext in H. }
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
  Qed.

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
  Qed.*)

  (* The most equivalent thing would be to existentially quantify over steps. They're equivalent in a deterministic language, but should we assume that? *)
(*  Lemma convergent_controls_jsafe :
    forall m q1 q2
      (Hat_ext : at_external Hcore q1 m = at_external Hcore q2 m)
      (Hafter_ext : forall ret m q', after_external Hcore ret q1 m = Some q' ->
                                     after_external Hcore ret q2 m = Some q')
      (Hhalted : halted Hcore q1 = semantics.halted Hcore q2)
      (Hstep : forall q' m', corestep Hcore q1 m q' m' ->
                             corestep Hcore q2 m q' m'),
      (forall E z, jsafe E z q1 ⊢ jsafe E z q2).
  Proof.
    intros.
    rewrite !jsafe_unfold /jsafe_pre.
    rewrite Hhalted.
    iIntros ">[H | H]"; first by iLeft.
    iRight; iDestruct "H" as (?) "H"; iIntros "!>".
    iSplit; first done.
    iIntros (?) "??"; iMod ("H" with "[$] [$]") as "H".
    iIntros "!>" (?); iApply (bi.impl_mono with "H"); first done.
    iIntros "H"; iSplit.
    - iIntros "!>" (???) "?".
rewrite Hstep.
    - iLeft. by rewrite Hhalted.
    - iDestruct ""

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
  Qed.*)

(*  Lemma jm_fupd_intro_strong' : forall (ora : Z) E (c : C) m,
    (joins (ghost_of (m_phi m)) (Some (ext_ref ora, NoneP) :: nil) -> jsafeN_ ora c m) ->
    jm_fupd ora E E (jsafeN_ ora c) m.
  Proof.
    intros; apply jm_fupd_intro_strong; auto.
    intros; eapply necR_safe; eauto.
  Qed. *)

End juicy_safety.

(*Lemma juicy_core_sem_preserves_corestep_fun
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
Qed.*)

End mpred.
