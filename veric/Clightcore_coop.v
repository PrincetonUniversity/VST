Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
Require Import sepcomp.mem_lemmas.
Require Import veric.base.
Require Import veric.Clight_core.

Lemma alloc_variables_mem_step: forall cenv vars m e e2 m'
      (M: alloc_variables cenv e m vars e2 m'), mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  eapply mem_step_trans.
    eapply mem_step_alloc; eassumption. eassumption.
Qed.

Lemma bind_parameters_mem_step: forall cenv e m pars vargs m'
      (M: bind_parameters cenv e m pars vargs m'), mem_step m m'.
Proof. intros.
  induction M.
  apply mem_step_refl.
  inv H0.
+ eapply mem_step_trans; try eassumption. simpl in H2.
  eapply mem_step_store; eassumption.
+ eapply mem_step_trans; try eassumption.
  eapply mem_step_storebytes; eassumption.
Qed.

Lemma CLC_corestep_mem:
  forall (g : genv) (c : CC_core) (m : mem) (c' : CC_core) (m' : mem),
    corestep cl_core_sem g c m c' m' -> mem_step m m'.
Admitted.


Program Definition CLC_memsem :
  @MemSem Clight.genv (*(Genv.t fundef type)*) CC_core.
apply Build_MemSem with (csem := cl_core_sem).
exact CLC_corestep_mem.
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
admit. (*This is the new readonly condition which should be easy to prove.*)
Admitted.
*)
