Require Import sepcomp.core_semantics.
Require Import sepcomp.mem_lemmas.
Require Import veric.base.
Require Import veric.Clight_new.

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
Defined.
