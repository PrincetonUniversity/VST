Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clight_base.
(*Require Import VST.concurrency.common.Clight_core.*)
Require Import VST.concurrency.common.core_semantics.


Section CoreSem. (* build a core semantics from CompCert's sem*)
Lemma cl_corestep_not_halted : forall ge m q m' q' i,
  step2corestep (part_semantics2 ge) q m q' m' -> ~final_state q i.
Proof.
  repeat intro.
  inv H0. inv H. inv H0.
Qed.

Definition cl_core_sem (ge : genv) := sem2coresem (part_semantics2 ge) (cl_corestep_not_halted ge).

End CoreSem.


Lemma alloc_variables_mem_step: forall cenv vars m e e2 m'
      (M: alloc_variables cenv e m vars e2 m'), mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  eapply semantics.mem_step_trans.
    eapply semantics.mem_step_alloc; eassumption. eassumption.
Qed.

Lemma assign_loc_mem_step g t m b z v m' (A:assign_loc g t m b z v m'):
    mem_step m m'.
Proof.
  inv A.
  { simpl in H0. eapply mem_step_storebytes. eapply Mem.store_storebytes; eauto. }
  { eapply mem_step_storebytes; eauto. }
Qed.

Lemma bind_parameters_mem_step: forall cenv e m pars vargs m'
      (M: bind_parameters cenv e m pars vargs m'), semantics.mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  inv H0.
+ eapply semantics.mem_step_trans; try eassumption. simpl in H2.
  eapply mem_step_store; eassumption.
+ eapply semantics.mem_step_trans; try eassumption.
  eapply semantics.mem_step_storebytes; eassumption.
Qed.

Lemma inline_assembly_memstep:
  forall text sg g vargs m t vres m'
    (IA:Events.inline_assembly_sem text sg g vargs m t vres m'),
    mem_step m m'.
Proof.
  intros.
  
(* EXPLANATION: this should comes from an assumption:
   Either we add an axiom saying our semantics only calls such externals OR
   we add this to the properties of external funtioncs.
   
   Either way, make sure it's not already assumed somwehre else.
same as: 
   + concurrency/common/ClightSemanticsForMachines/extcall_ev_elim
   + concurrency/common/Clightcore_coop/inline_assembly_memstep  
   + concurrency/common/Clightcore_coop/extcall_sem_mem_step
   + extcall_sem_mem_step bellow
 *)
  
Admitted. (*Maybe include mem_step in Events.extcall_properties.?*)

Lemma extcall_sem_mem_step:
  forall name sg g vargs m t vres m'
    (E:Events.external_functions_sem name sg g vargs m t vres m'),
    mem_step m m'.
Proof.
  pose proof Clight_core.inline_external_call_mem_events.
  unfold Events.external_call,ef_inline in *.

  intros.
  specialize (X (EF_builtin name sg) g vargs m t vres m' ltac:(reflexivity)).
  simpl in X.
  eapply X in E.
  inv E.
  eapply ev_elim_mem_step; eauto.
Qed.

Lemma extcall_mem_step g: forall ef vargs m t vres m' (E:Events.external_call ef g vargs m t vres m'),
  mem_step m m'.
Proof.
  destruct ef; simpl; intros; try solve [inv E; apply mem_step_refl].
  { eapply extcall_sem_mem_step; eassumption. }
  { eapply extcall_sem_mem_step; eassumption. }
  { eapply extcall_sem_mem_step; eassumption. }
  { inv E. inv H. eapply mem_step_refl.
    apply Mem.store_storebytes in H1. eapply mem_step_storebytes. eassumption. }
  { inv E. apply Mem.store_storebytes in H0.
    eapply mem_step_trans. eapply mem_step_alloc; eassumption.
    eapply mem_step_storebytes; eassumption. }
  { inv E. eapply mem_step_free; eassumption. }
  { inv E. eapply mem_step_storebytes. eassumption. }
  { eapply inline_assembly_memstep; eassumption. }
Qed.
  
Lemma CLC_corestep_mem:
  forall (g : genv) c (m : mem) c'  (m' : mem),
    semantics.corestep (cl_core_sem g) c m c' m' ->
    semantics.mem_step m m'.
Proof.
  simpl; intros.
  destruct H.
  destruct s1, s2; inv H; simpl in *;  try apply mem_step_refl.
  - eapply assign_loc_mem_step; eauto.
  - inv H15. apply extcall_mem_step in H1; auto.
  - eapply mem_step_freelist; eauto.
  - eapply mem_step_freelist; eauto.
  - eapply mem_step_freelist; eauto.
  - inv H6.
   eapply alloc_variables_mem_step; eauto.
  - apply extcall_mem_step in H6; auto.
Qed. 

Program Definition CLC_memsem  (ge : Clight.genv) :
  @MemSem state.
apply Build_MemSem with (csem := cl_core_sem ge).
eapply CLC_corestep_mem.
Defined.


(*
Lemma assign_loc_forward:
      forall cenv t m b ofs v m'
      (A: assign_loc cenv t m b ofs v m'),
      mem_forward m m'.
Proof.
intros.
induction A.
 unfold Mem.storev in H0.
 eapply store_forward; eassumption.
 eapply storebytes_forward; eassumption.
Qed.

Lemma alloc_variables_forward: forall cenv vars m e e2 m'
      (M: alloc_variables cenv e m vars e2 m'),
      mem_forward m m'.
Proof. intros.
  induction M.
  apply mem_forward_refl.
  apply alloc_forward in H.
  eapply mem_forward_trans; eassumption.
Qed.

Lemma cln_forward: forall (g : genv) (c : corestate)
  (m : mem) (c' : corestate) (m' : mem),
  corestep cl_core_sem g c m c' m' -> mem_forward m m'.
Proof.
intros.
induction H; try apply mem_forward_refl; trivial.
  eapply assign_loc_forward; eassumption.
  eapply alloc_variables_forward; eassumption.
  eapply freelist_forward; eassumption.
Qed.
Program Definition CLN_coop_sem :
  CoopCoreSem Clight.genv (*(Genv.t fundef type)*) corestate.
apply Build_CoopCoreSem with (coopsem := cl_core_sem).
apply cln_forward.
adm it. (*This is the new readonly condition which should be easy to prove.*)
Adm itted.
*)
