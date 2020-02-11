Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.veric.Clight_base.
(*Require Import VST.concurrency.common.Clight_core.*)
Require Import VST.concurrency.common.core_semantics.

Lemma inline_assembly_memstep:
  forall text sg g vargs m t vres m'
    (IA:Events.inline_assembly_sem text sg g vargs m t vres m'),
    mem_step m m'.
Admitted. (*Maybe include mem_step in Events.extcall_properties.?*)

Lemma extcall_sem_mem_step:
  forall name sg g vargs m t vres m'
    (E:Events.external_functions_sem name sg g vargs m t vres m'),
  mem_step m m'.
Admitted. (*Maybe include mem_step in Events.extcall_properties.?*)

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