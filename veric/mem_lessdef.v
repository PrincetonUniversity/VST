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
Require Import veric.res_predicates.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.event_semantics.
Require Import sepcomp.structured_injections.
Require Import sepcomp.extspec.

Definition mem_lessdef m1 m2 :=
  (forall b ofs len v,
      Mem.loadbytes m1 b ofs len = Some v ->
      exists v',
        Mem.loadbytes m2 b ofs len = Some v' /\
        list_forall2 memval_lessdef v v'
  ) /\
  (forall b ofs k p,
      Mem.perm m1 b ofs k p ->
      Mem.perm m2 b ofs k p) /\
  Mem.nextblock m1 =
  Mem.nextblock m2.

Definition mem_equiv m1 m2 :=
  Mem.loadbytes m1 = Mem.loadbytes m2 /\
  Mem.perm m1 = Mem.perm m2 /\
  Mem.nextblock m1 = Mem.nextblock m2.

Lemma val_inject_antisym v1 v2 :
  val_inject inject_id v1 v2 ->
  val_inject inject_id v2 v1 ->
  v1 = v2.
Proof.
  destruct v1, v2; intros A B; auto.
  all: inversion A; subst; inversion B; try subst; try congruence.
  unfold inject_id in *.
  f_equal. congruence.
  replace delta with 0%Z by congruence.
  symmetry; apply Int.add_zero.
Qed.

Lemma memval_lessdef_antisym v1 v2 : memval_lessdef v1 v2 -> memval_lessdef v2 v1 -> v1 = v2.
Proof.
  destruct v1, v2; intros A B; auto.
  all: inversion A; subst; inversion B; subst; try congruence.
  f_equal. apply val_inject_antisym; auto.
Qed.

Lemma mem_lessdef_equiv m1 m2 : mem_lessdef m1 m2 -> mem_lessdef m2 m1 ->  mem_equiv m1 m2.
Proof.
  intros (L1 & P1 & N1) (L2 & P2 & N2); repeat split.
  - clear -L1 L2.
    extensionality b ofs z.
    match goal with |- ?a = ?b => destruct a as [v1|] eqn:E1; destruct b as [v2|] eqn:E2 end;
      try destruct (L1 _ _ _ _ E1) as (v2' & E1' & l1);
      try destruct (L2 _ _ _ _ E2) as (v1' & E2' & l2);
      try congruence.
    assert (v1' = v1) by congruence; assert (v2' = v2) by congruence; subst; f_equal.
    clear -l1 l2.
    revert v2 l1 l2; induction v1; intros v2 l1 l2; inversion l1; subst; auto.
    inversion l2; subst.
    f_equal; auto.
    apply memval_lessdef_antisym; auto.
  - repeat extensionality.
    apply prop_ext; split; auto.
  - apply N1.
Qed.

Lemma mem_equiv_refl m : mem_equiv m m.
Proof.
  split3; hnf; auto.
Qed.

Lemma mem_equiv_refl' m m' : m = m' -> mem_equiv m m'.
Proof.
  intros <-; apply mem_equiv_refl.
Qed.

Lemma mem_equiv_sym m1 m2 : mem_equiv m1 m2 -> mem_equiv m2 m1.
Proof.
  intros []; split; intuition.
Qed.

Lemma mem_equiv_trans m1 m2 m3 :
  mem_equiv m1 m2 ->
  mem_equiv m2 m3 ->
  mem_equiv m1 m3.
Proof.
  unfold mem_equiv in *.
  intros (-> & -> & ->) (-> & -> & ->); auto.
Qed.

Lemma mem_equiv_lessdef m1 m2 : mem_equiv m1 m2 -> mem_lessdef m1 m2.
Proof.
  intros (L1 & P1 & N1); repeat split.
  - rewrite L1; auto.
    intros b ofs len v H.
    exists v; intuition.
    clear.
    induction v; constructor; auto.
    apply memval_lessdef_refl.
  - rewrite P1; auto.
  - rewrite N1; auto.
Qed.

Lemma cl_step_mem_lessdef_sim {ge c m1 c' m1' m2} :
  mem_lessdef m1 m2 ->
  @cl_step ge c m1 c' m1' ->
  exists m2',
    mem_lessdef m1' m2' /\
    @cl_step ge c m2 c' m2'.
Admitted.
 
Lemma cl_step_mem_equiv_sim {ge c m1 c' m1' m2} :
  mem_equiv m1 m2 ->
  @cl_step ge c m1 c' m1' ->
  exists m2',
    mem_equiv m1' m2' /\
    @cl_step ge c m2 c' m2'.
Proof.
  intros E S1.
  pose proof mem_equiv_lessdef _ _ E as L12.
  pose proof mem_equiv_lessdef _ _ (mem_equiv_sym _ _ E) as L21.
  destruct (cl_step_mem_lessdef_sim L12 S1) as (m2' & L12' & S2).
  destruct (cl_step_mem_lessdef_sim L21 S2) as (m1'' & L21' & S1').
  exists m2'; split; auto.
  apply mem_lessdef_equiv; auto.
  cut (m1'' = m1'). intros <-; auto.
  pose proof semax_lemmas.cl_corestep_fun' ge _ _ _ _ _ _ S1 S1'.
  congruence.
Qed.

Definition juicy_mem_equiv jm1 jm2 := mem_equiv (m_dry jm1) (m_dry jm2) /\ m_phi jm1 = m_phi jm2.

Lemma mem_equiv_juicy_mem_equiv jm1 m2 :
  mem_equiv (m_dry jm1) m2 ->
  exists jm2,
    m_dry jm2 = m2 /\
    juicy_mem_equiv jm1 jm2.
Proof.
  intros E.
  refine (ex_intro _ (mkJuicyMem m2 (m_phi jm1) _ _ _ _) _); repeat (split; auto).
  Unshelve.
  all: destruct jm1 as [m1 phi Con Acc Max All]; simpl in *.
  all: destruct E as (Load & Perm & Next).
    (* I'll admit this for now. It should take less time to prove once
    the new mem interface is there. *)
Admitted.

Lemma juicy_step_mem_equiv_sim {ge c jm1 c' jm1' jm2} :
  juicy_mem_equiv jm1 jm2 ->
  corestep (juicy_core_sem cl_core_sem) ge c jm1 c' jm1' ->
  exists jm2',
    juicy_mem_equiv jm1' jm2' /\
    corestep (juicy_core_sem cl_core_sem) ge c jm2 c' jm2'.
Proof.
  intros [Ed Ew] [step [rd lev]].
  destruct (cl_step_mem_equiv_sim Ed step) as [m2' [Ed' Sd']].
  destruct (mem_equiv_juicy_mem_equiv jm1' m2' Ed') as (jm2', (<-, [Hd Hw])).
  exists jm2'.
  split; split; auto. split.
  - cut (Mem.nextblock (m_dry jm1) = Mem.nextblock (m_dry jm2)). congruence.
    apply Ed.
  - repeat rewrite level_juice_level_phi in *.
    congruence.
Qed.

Definition ext_spec_stable {M E Z} (R : M -> M -> Prop)
           (spec : external_specification M E Z) :=
  (forall e x b tl vl z m1 m2,
    R m1 m2 ->
    ext_spec_pre spec e x b tl vl z m1 ->
    ext_spec_pre spec e x b tl vl z m2) /\
  (forall e v m1 m2,
    R m1 m2 ->
    ext_spec_exit spec e v m1 ->
    ext_spec_exit spec e v m2).

Lemma jsafeN_mem_equiv {Z Jspec ge n z c jm1 jm2} :
  juicy_mem_equiv jm1 jm2 ->
  ext_spec_stable juicy_mem_equiv (JE_spec _ Jspec) ->
  @jsafeN Z Jspec ge n z c jm1 ->
  @jsafeN Z Jspec ge n z c jm2.
Proof.
  intros E [Spre Sexit] S1.
  revert jm2 E.
  induction S1 as
      [ z c jm1
      | n z c jm1 c' jm1' step safe IH
      | n z c jm1 ef args x atex Pre Post
      | n z c jm1 v Halt Exit ]; intros jm2 E.
  
  - constructor 1.
  
  - destruct (juicy_step_mem_equiv_sim E step) as (jm2' & E' & step').
    econstructor 2; eauto.
    apply IH, E'.
  
  - econstructor 3 with (x := x); eauto.
    intros ret jm2' z' n' Hargsty Hretty Hn [-> [lev pure]] post.
    destruct (Post ret jm2' z' _ Hargsty Hretty Hn) as (c' & atex' & safe'); auto.
    + split; auto.
      destruct E as [Ed Ew].
      unfold juicy_safety.pures_eq in *.
      unfold juicy_safety.pures_sub in *.
      split.
      * repeat rewrite level_juice_level_phi in *.
        congruence.
      * revert pure.
        rewrite Ew.
        auto.
    + exists c'; split; auto.
  
  - econstructor 4; eauto.
Qed.

Lemma mem_ext m1 m2 :
  Mem.mem_contents m1 = Mem.mem_contents m2 ->
  Mem.mem_access m1 = Mem.mem_access m2 ->
  Mem.nextblock m1 = Mem.nextblock m2 ->
  m1 = m2.
Proof.
  destruct m1, m2; simpl in *.
  intros <- <- <- .
  f_equal; apply proof_irr.
Qed.
