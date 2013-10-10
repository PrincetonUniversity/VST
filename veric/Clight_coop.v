Require Import sepcomp.core_semantics.
Require Import sepcomp.mem_lemmas.
Require Import veric.base.
Require Import veric.Clight_new.

(*two trivial elimination lemmas*)
Lemma if_E_false: forall {A} (b:bool) (v u:A) 
       (H: (if b then None else Some v) = Some u), v=u.
Proof. intros. destruct b; inv H. trivial. Qed.

Lemma if_E_true: forall {A} (b:bool) (v u:A) 
       (H: (if b then Some v else None) = Some u), v=u.
Proof. intros. destruct b; inv H. trivial. Qed.

Lemma assign_loc_forward: 
      forall t m b ofs v m' 
      (A: assign_loc t m b ofs v m'),
      mem_forward m m'.
Proof.
intros.
induction A.
 unfold Mem.storev in H0.
 eapply store_forward; eassumption.
 eapply storebytes_forward; eassumption.
Qed.

Lemma alloc_variables_forward: forall vars m e e2 m'
      (M: alloc_variables e m vars e2 m'),
      mem_forward m m'.
Proof. intros.
  induction M.
  apply mem_forward_refl.
  apply alloc_forward in H.
  eapply mem_forward_trans; eassumption. 
Qed.
(*mem_wd deprecated
Lemma alloc_variables_mem_wd: forall vars m e e2 m'
      (M: alloc_variables e m vars e2 m')
      (WD: mem_wd m), mem_wd m'.
Proof. intros.
  induction M; trivial.
  apply IHM.
  eapply mem_wd_alloc; eassumption.
Qed.

Lemma deref_loc_val_valid: forall  m e b ofs v
  (LVal: Mem.valid_block m b)
  (DL: deref_loc (typeof e) m b ofs v)
  (WD : mem_wd m),
  val_valid v m.
Proof. intros.
  destruct DL; simpl in *; trivial.
    eapply mem_wd_load; eassumption.
Qed.
*)

Lemma cl_forward: forall (g : Genv.t fundef type) (c : corestate) 
  (m : mem) (c' : corestate) (m' : mem), 
  corestep cl_core_sem g c m c' m' -> mem_forward m m'.
Proof.
intros.
induction H; try apply mem_forward_refl; trivial.
  eapply assign_loc_forward; eassumption.
  eapply alloc_variables_forward; eassumption.
  eapply freelist_forward; eassumption.
Qed.

Definition coopstep (g : Genv.t fundef type) (c : corestate) 
  (m : mem) (c' : corestate) (m' : mem) :=
   cl_step g c m c' m'.

Lemma cl_coopstep_not_at_external: forall ge m q m' q',
  coopstep ge q m q' m' -> cl_at_external q = None.
Proof.
  intros.
  eapply cl_corestep_not_at_external. apply H.
Qed.

Lemma cl_coopstep_not_halted :
  forall ge m q m' q', coopstep ge q m q' m' -> cl_halted q = None.
Proof.
  intros.
  simpl; auto.
Qed.

Program Definition cl_coop_core_sem : 
  CoreSemantics (Genv.t fundef type) corestate mem :=
  @Build_CoreSemantics _ _ _ (*_*)
    (*cl_init_mem*)
    cl_initial_core
    cl_at_external
    cl_after_external
    cl_halted
    coopstep
    cl_coopstep_not_at_external
    cl_coopstep_not_halted _
    cl_after_at_external_excl.

Lemma coop_forward: forall (g : Genv.t fundef type) (c : corestate) 
  (m : mem) (c' : corestate) (m' : mem), 
  coopstep g c m c' m' -> mem_forward m m'.
Proof.
intros.
eapply cl_forward; eassumption.
Qed.

Program Definition cl_coop_sem : 
  CoopCoreSem (Genv.t fundef type) corestate.
apply Build_CoopCoreSem with (coopsem := cl_coop_core_sem).
  apply coop_forward.
Qed.
