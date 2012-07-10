Require Import veric.base.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.extspec.
Require Import veric.step_lemmas.

Local Open Scope nat_scope.
Local Open Scope pred.
Require Import veric.forward_simulations.

Record juicy_ext_spec (Z: Type) := {
  JE_spec:> external_specification juicy_mem external_function Z;
  JE_pre_hered: forall e t sig args z, hereditary age (ext_spec_pre JE_spec e t sig args z);
  JE_post_hered: forall e t sig args z, hereditary age (ext_spec_post JE_spec e t sig args z)
}.
 
Definition jstep {G C} (csem: CoreSemantics G C mem external_function)
  (ge: G)  (q: C) (jm: juicy_mem) (q': C) (jm': juicy_mem) : Prop :=
 corestep csem ge q (m_dry jm) q' (m_dry jm') /\
 resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\
 level jm = S (level jm').

Definition j_safely_halted {G C} (csem: CoreSemantics G C mem external_function)
       (ge: G) (c: C) (jm: juicy_mem) : option val :=
     safely_halted csem ge c (m_dry jm).


Lemma jstep_not_at_external {G C} (csem: CoreSemantics G C mem external_function):
  forall ge m q m' q', jstep csem ge q m q' m' -> at_external csem q = None.
Proof.
  intros.
  destruct H. eapply corestep_not_at_external; eauto.
Qed.

Lemma jstep_not_halted  {G C} (csem: CoreSemantics G C mem external_function):
  forall ge m q m' q', jstep csem ge q m q' m' -> j_safely_halted csem ge q m = None.
Proof.
  intros. destruct H. eapply corestep_not_halted; eauto.
Qed.

Lemma j_at_external_halted_excl {G C} (csem: CoreSemantics G C mem external_function):
  forall (ge : G) (q : C) (m : juicy_mem),
  at_external csem q = None \/ j_safely_halted csem ge q m = None.
Proof.
 intros.
 destruct (at_external_halted_excl csem ge q (m_dry m)); [left | right]; auto.
Qed.


Definition juicy_core_sem  {G C} (csem: CoreSemantics G C mem external_function) :
   CoreSemantics G C juicy_mem external_function :=
  @Build_CoreSemantics _ _ _ _
    (make_initial_core csem)
    (at_external csem)
    (after_external csem)
    (j_safely_halted csem)
    (jstep csem)
    (jstep_not_at_external csem)
    (jstep_not_halted csem)
    (j_at_external_halted_excl csem).

Program Definition juicy_mem_op (P : pred rmap) : pred juicy_mem :=
  fun jm => P (m_phi jm).
 Next Obligation.
  apply age1_juicy_mem_unpack in H.  
  destruct H.
  eapply pred_hereditary; eauto.
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
 split. clear H.
 apply age_level in H0; apply age_level in H1.
  rewrite H0 in *; rewrite H1 in *. inv LEV. rewrite H2.
  clear. forget (level jm2') as n. omega.
  intro l. 
 specialize (H l).
  destruct H.
  split.
  intro.
  specialize (H H3).
  erewrite <- necR_NO; eauto.  constructor 1; auto.
  destruct H2 as [?|[?|[?|?]]].
  left.
  clear H. unfold age in *.
  rewrite (age1_resource_at _ _ H0 l (jm1 @ l)); [ |  apply resource_at_approx].
  rewrite (age1_resource_at _ _ H1 l (jm2 @ l)); [ |  apply resource_at_approx].
  rewrite <- H2.
  rewrite resource_fmap_fmap.
  rewrite resource_fmap_fmap.
  f_equal. change R.approx with approx.
 rewrite approx_oo_approx'.
 rewrite approx_oo_approx'.
  auto.
 apply age_level in H0; apply age_level in H1.
 forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
 subst. omega.
 apply age_level in H0; apply age_level in H1.
 forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
 subst. omega.
 right.
  destruct H2 as [rsh [v [v' [? ?]]]].
  left; exists rsh, v,v'.
  split.
  apply age_level in H1.
  forget (level jm2) as j2. forget (level jm2') as j2'. subst j2.
  clear - H2 H0 LEV.
  revert H2; case_eq (jm1 @ l); intros; inv H2.
  pose proof (necR_YES jm1 jm1' l rsh pfullshare (VAL v) p0 (rt_step _ _ _ _ H0) H).
  rewrite H1.
  simpl. rewrite preds_fmap_fmap.
 apply age_level in H0.
  rewrite approx_oo_approx'.
 2: rewrite H0 in *; inv LEV; omega.
 f_equal.
  rewrite H6.
  rewrite <- (approx_oo_approx' j2' (S j2')) by auto.
  rewrite <- preds_fmap_fmap; rewrite H6. rewrite preds_fmap_NoneP. auto. 
  pose proof (age1_YES _ _ l rsh pfullshare (VAL v') H1).
  rewrite H4 in H3. auto.
  destruct H2 as [? [v ?]]; right; right; left.
  split; auto. exists v.   apply (age1_YES _ _ l _ _ _ H1) in H3. auto.
  right; right; right.
  erewrite <- necR_NO; try eassumption. constructor; auto.
Qed.

Lemma age_safe {G}{C}(csem: CoreSemantics G C mem external_function){Z}  (Hspec : juicy_ext_spec Z):
  forall jm jm0, age jm0 jm -> 
  forall ge ora c, 
   safeN (juicy_core_sem csem) Hspec ge (level jm0) ora c jm0 ->
   safeN (juicy_core_sem csem) Hspec ge (level jm) ora c jm.
Proof.
  intros. rename H into H2.
   rewrite (age_level _ _ H2) in H0.
   remember (level jm) as N.
   revert c jm0 jm HeqN H2 H0; induction N; intros.
   simpl. auto.
   simpl.
  remember (S N) as SN.
   simpl in H0. subst SN.
   revert H0; case_eq (at_external csem c); intros.
   destruct p. destruct p.
   unfold j_safely_halted in *.
   rewrite <- (age_jm_dry H2).
   destruct (safely_halted csem ge c (m_dry jm0)); [contradiction | ].
  destruct H0 as [x ?]. exists x.
   intros z' H1; specialize (H0 z' H1).
  destruct H0; split; auto.
  clear - H2 H0.
  eapply JE_pre_hered; eauto.
   intros.
   destruct (H3 ret m' z'') as [c' [? ?]].
   auto.
   exists c'; split; auto.
   eapply safe_downward; try eassumption. 
  omega.
   unfold j_safely_halted in *.
   rewrite <- (age_jm_dry H2).
   destruct (safely_halted csem ge c (m_dry jm0)); auto.
   destruct H0 as [c' [jm' [[? [? ?]] ?]]].
   pose proof (age_level _ _ H2).
   assert (level jm' > 0) by omega.
   assert (exists i, level jm' = S i).
   destruct (level jm'). omegaContradiction. eauto.
   destruct H7 as [i ?].
   apply levelS_age1 in H7. destruct H7 as [jm1' ].
   exists c', jm1'.
   split.
   split.
   replace (m_dry jm) with (m_dry jm0) by (decompose [and] (age1_juicy_mem_unpack _ _ H2); auto).
   replace (m_dry jm1') with (m_dry jm') by (decompose [and] (age1_juicy_mem_unpack _ _ H7); auto).
   auto.
   split.
   replace (m_dry jm) with (m_dry jm0) by (decompose [and] (age1_juicy_mem_unpack _ _ H2); auto).
   eapply age_resource_decay; try eassumption.
   destruct (age1_juicy_mem_unpack _ _ H2); auto.
   destruct (age1_juicy_mem_unpack _ _ H7); auto.
   apply age_level in H7.  rewrite <- H7.
   omega.
   eapply IHN; try eassumption.
  apply age_level in H7;   omega.
Qed.
