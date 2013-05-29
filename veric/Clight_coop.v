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


(**** preservation of val_valid by arithmetic, comparison etc operations.
      Could eventually be moved to mem_lemmas, or to compcert/cfrontend/Cop.v*)

Lemma sem_cast_val_valid: forall w t1 t2 v m
  (CAST: Cop.sem_cast w t2 t1 = Some v)
  (W:  val_valid w m), val_valid v m.
Proof. intros.
  unfold Cop.sem_cast in CAST.
  remember (Cop.classify_cast t2 t1) as d.
  destruct d; 
    try (destruct w; inv CAST; simpl in *; trivial).
    remember (Cop.cast_float_int si2 f) as q.
      destruct q; inv H0; simpl in *; trivial.
    remember (Cop.cast_float_long si2 f) as q.
      destruct q; inv H0; simpl in *; trivial.
    remember (ident_eq id1 id2 && fieldlist_eq fld1 fld2) as q.
      destruct q; inv H0; simpl in *; trivial.
    remember (ident_eq id1 id2 && fieldlist_eq fld1 fld2) as q.
      destruct q; inv H0; simpl in *; trivial.
Qed.

Lemma notbool_val_valid: forall w t v m
  (COP: Cop.sem_notbool w t = Some v),
  val_valid v m.
Proof. intros.
 rewrite Cop.notbool_bool_val in COP.
 remember (Cop.bool_val w t) as d.
 destruct d; inv COP; simpl.
 unfold Val.of_bool.
 case_eq (negb b); simpl; intros; trivial.
Qed.

Lemma notint_val_valid: forall w t v m
  (COP: Cop.sem_notint w t = Some v),
  val_valid v m.
Proof. intros.
 unfold Cop.sem_notint in COP.
 remember (Cop.classify_notint t) as d.
 destruct d; destruct w; inv COP; simpl in *; trivial.
Qed.

Lemma neg_val_valid: forall w t v m
  (COP: Cop.sem_neg w t = Some v),
  val_valid v m.
Proof. intros.
 unfold Cop.sem_neg in COP.
 remember (Cop.classify_neg t) as d.
 destruct d; destruct w; inv COP; simpl in *; trivial.
Qed.


Lemma unary_operation_val_valid: forall op w t v m
  (OP: Cop.sem_unary_operation op w t = Some v)
  (W : val_valid w m),
  val_valid v m.
Proof.
  intros op.
  destruct op; simpl; intros.
  eapply notbool_val_valid; eassumption.
  eapply notint_val_valid; eassumption.
  eapply neg_val_valid; eassumption.
Qed.

Lemma sem_binarith_val_valid: forall
   m sem_int sem_long sem_float 
   (Hsemint: forall s i1 i2 u, sem_int s i1 i2 = Some u -> val_valid u m)
   (Hsemlong: forall s i1 i2 u, sem_long s i1 i2 = Some u -> val_valid u m)
   (Hsemfloat: forall f1 f2 u, sem_float f1 f2 = Some u -> val_valid u m)
   v1 t1 v2 t2 v, 
   Cop.sem_binarith sem_int sem_long sem_float v1 t1 v2 t2 = Some v ->
   val_valid v m.
Proof. intros.
  unfold Cop.sem_binarith in *.
  set (c := Cop.classify_binarith t1 t2) in *.
  set (t := Cop.binarith_type c) in *.
  destruct (Cop.sem_cast v1 t1 t) as [w1|] eqn:C1; try discriminate.
  destruct (Cop.sem_cast v2 t2 t) as [w2|] eqn:C2; try discriminate.
  destruct c.
    destruct w1; inv H.
    destruct w2; inv H1.
    apply (Hsemint _ _ _ _ H0).

    destruct w1; inv H.
    destruct w2; inv H1.
    apply (Hsemlong _ _ _ _ H0).

    destruct w1; inv H.
    destruct w2; inv H1.
    apply (Hsemfloat _ _ _ H0).
  inv H.
Qed.

Lemma sem_add_val_valid: forall v1 t1 v2 t2 v m
  (OP: Cop.sem_add v1 t1 v2 t2 = Some v)
  (V1 : val_valid v1 m)
  (V2 : val_valid v2 m),
  val_valid v m.
Proof. intros.
  unfold Cop.sem_add in OP.
  remember (Cop.classify_add t1 t2) as d.
  destruct d; destruct v1; destruct v2; try inv OP; simpl in *; trivial;

  try solve [eapply sem_binarith_val_valid; try eassumption; 
       try solve[intros; simpl in *; inv H; simpl; trivial]].
Qed.

Lemma sem_sub_val_valid: forall v1 t1 v2 t2 v m
  (OP: Cop.sem_sub v1 t1 v2 t2 = Some v)
  (V1 : val_valid v1 m)
  (V2 : val_valid v2 m),
  val_valid v m.
Proof. intros.
  unfold Cop.sem_sub in OP.
  remember (Cop.classify_sub t1 t2) as d.
  destruct d; destruct v1; destruct v2; try inv OP; simpl in *; trivial;

  try solve [eapply sem_binarith_val_valid; try eassumption; 
       try solve[intros; simpl in *; inv H; simpl; trivial]].
  remember (zeq b b0) as s.
  destruct s; subst; clear Heqs; try inv H0.
    remember (Int.eq (Int.repr (sizeof ty)) Int.zero) as p.
    destruct p; inv H1; simpl. trivial.
Qed.

Lemma sem_mul_val_valid: forall v1 t1 v2 t2 v m
  (OP: Cop.sem_mul v1 t1 v2 t2 = Some v)
  (V1 : val_valid v1 m)
  (V2 : val_valid v2 m),
  val_valid v m.
Proof. intros.
  unfold Cop.sem_mul in OP.
  try solve [eapply sem_binarith_val_valid; try eassumption; 
       try solve[intros; simpl in *; inv H; simpl; trivial]].
Qed.

Lemma sem_div_val_valid: forall v1 t1 v2 t2 v m
  (OP: Cop.sem_div v1 t1 v2 t2 = Some v)
  (V1 : val_valid v1 m)
  (V2 : val_valid v2 m),
  val_valid v m.
Proof. intros.
  unfold Cop.sem_div in OP.
  eapply sem_binarith_val_valid; try eassumption.
    intros; simpl in *.
     destruct s. apply if_E_false in H. subst. simpl; trivial.
     apply if_E_false in H. subst. simpl; trivial. 
    intros; simpl in *.
     destruct s. apply if_E_false in H. subst. simpl; trivial.
     apply if_E_false in H. subst. simpl; trivial. 
    intros; simpl in *. inv H. simpl; trivial.
Qed.

Lemma sem_mod_val_valid: forall v1 t1 v2 t2 v m
  (OP: Cop.sem_mod v1 t1 v2 t2 = Some v)
  (V1 : val_valid v1 m)
  (V2 : val_valid v2 m),
  val_valid v m.
Proof. intros.
  unfold Cop.sem_mod in OP.
  eapply sem_binarith_val_valid; try eassumption.
    intros; simpl in *.
     destruct s. apply if_E_false in H. subst. simpl; trivial.
     apply if_E_false in H. subst. simpl; trivial. 
    intros; simpl in *.
     destruct s. apply if_E_false in H. subst. simpl; trivial.
     apply if_E_false in H. subst. simpl; trivial. 
    intros; simpl in *. inv H.
Qed.

Lemma sem_shift_val_valid: forall m
   v1 t1 v2 t2 v sg1 sg2, 
   Cop.sem_shift sg1 sg2 v1 t1 v2 t2 = Some v ->
   val_valid v m.
Proof. intros.
  unfold Cop.sem_shift in *.
  set (c := Cop.classify_shift t1 t2) in *.
  destruct c.
    destruct v1; inv H.
    destruct v2; inv H1.
    apply if_E_true in H0. subst. simpl; trivial. 

    destruct v1; inv H.
    destruct v2; inv H1.
    apply if_E_true in H0. subst. simpl; trivial. 

    destruct v1; inv H.
    destruct v2; inv H1.
    apply if_E_true in H0. subst. simpl; trivial. 

    destruct v1; inv H.
    destruct v2; inv H1.
    apply if_E_true in H0. subst. simpl; trivial. 

    inv H.
Qed.

Lemma sem_cmp_val_valid: forall m
   v1 t1 v2 t2 v ce, 
   Cop.sem_cmp ce v1 t1 v2 t2 m = Some v ->
   val_valid v m.
Proof. intros.
  unfold Cop.sem_cmp in *.
  set (c := Cop.classify_cmp t1 t2) in *.
  destruct c.
    unfold option_map in H.
    remember (Val.cmpu_bool (Mem.valid_pointer m) ce v1 v2) as d.
    destruct d; inv H. 
     destruct b; simpl; trivial. 

    destruct v2; inv H.
    unfold option_map in H1.
    remember (Val.cmpu_bool (Mem.valid_pointer m) ce v1
         (Vint (Int.repr (Int64.unsigned i)))) as d.
    destruct d; inv H1. 
     destruct b; simpl; trivial. 

    destruct v1; inv H.
    unfold option_map in H1.
    destruct v2; inv H1.
      remember (Int.cmpu ce (Int.repr (Int64.unsigned i)) i0) as d.
      destruct d; simpl; trivial.

      remember (if Int.eq (Int.repr (Int64.unsigned i)) Int.zero
        then Val.cmp_different_blocks ce
        else None) as d.
      destruct d; inv H0.   
      destruct b0; simpl; trivial. 
    eapply sem_binarith_val_valid; try eassumption; clear H.
      intros; simpl in *; inv H; simpl; trivial.
      destruct s; simpl.
      destruct (Int.cmp ce i1 i2); simpl; trivial. 
      destruct (Int.cmpu ce i1 i2); simpl; trivial. 

      intros; simpl in *; inv H; simpl; trivial.
      destruct s; simpl.
      destruct (Int64.cmp ce i1 i2); simpl; trivial. 
      destruct (Int64.cmpu ce i1 i2); simpl; trivial.

      intros; simpl in *; inv H; simpl; trivial.
      destruct (Float.cmp ce f1 f2); simpl; trivial. 
Qed.

Lemma binary_operation_val_valid: forall op v1 v2 t1 t2 v m
  (OP: Cop.sem_binary_operation op v1 t1 v2 t2 m = Some v)
  (V1 : val_valid v1 m) (V2 : val_valid v2 m),
  val_valid v m.
Proof.
  intros op.
  destruct op; simpl; intros.
    eapply sem_add_val_valid; eassumption.
    eapply sem_sub_val_valid; eassumption.
    eapply sem_mul_val_valid; eassumption.
    eapply sem_div_val_valid; eassumption.
    eapply sem_mod_val_valid; eassumption.
  eapply sem_binarith_val_valid; try eassumption;
    intros; simpl in *; inv H; simpl; trivial.
  eapply sem_binarith_val_valid; try eassumption;
    intros; simpl in *; inv H; simpl; trivial.
  eapply sem_binarith_val_valid; try eassumption;
    intros; simpl in *; inv H; simpl; trivial.
  eapply sem_shift_val_valid; try eassumption;
    intros; simpl in *; inv H; simpl; trivial.
  eapply sem_shift_val_valid; try eassumption;
    intros; simpl in *; inv H; simpl; trivial.
  eapply sem_cmp_val_valid; try eassumption.
  eapply sem_cmp_val_valid; try eassumption.
  eapply sem_cmp_val_valid; try eassumption.
  eapply sem_cmp_val_valid; try eassumption.
  eapply sem_cmp_val_valid; try eassumption.
  eapply sem_cmp_val_valid; try eassumption.
Qed.

(************* end of val_valid preservation lemmas for operations*****)

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

   
Definition valid_env (e:env) (m:mem) :=
  forall i b z , e!i = Some (b,z) -> Mem.valid_block m b. 

Definition valid_tempenv (t:temp_env) (m:mem) :=
  forall i v , t!i = Some v -> val_valid v m. 

Lemma eval_expr_lvalue_valid_aux:
  forall ge e te m
    (VE: valid_env e m) (GE: valid_genv ge m)
    (TE: valid_tempenv te m) (WD : mem_wd m),
    (forall a v, eval_expr ge e te m a v -> val_valid v m) /\
    (forall a b i, eval_lvalue ge e te m a b i -> Mem.valid_block m b). 
Proof.
 intros.
 apply (eval_expr_lvalue_ind); 
 intros; simpl in *; trivial.
    apply (TE _ _ H).
    eapply unary_operation_val_valid; try eassumption.
    eapply binary_operation_val_valid; try eassumption.
    eapply sem_cast_val_valid; try eassumption.
    eapply deref_loc_val_valid; try eassumption.
    apply (VE _ _ _ H).
    apply (GE _ _ H0).
Qed.

Lemma eval_expr_val_valid:
  forall ge e te m
    (VE: valid_env e m) (GE: valid_genv ge m)
    (TE: valid_tempenv te m) (WD : mem_wd m),
    (forall a v, eval_expr ge e te m a v -> val_valid v m). 
Proof.
 intros.
 eapply eval_expr_lvalue_valid_aux; eassumption.
Qed.

Lemma eval_lvalue_val_valid:
  forall ge e te m
    (VE: valid_env e m) (GE: valid_genv ge m)
    (TE: valid_tempenv te m) (WD : mem_wd m),
    (forall a b i, eval_lvalue ge e te m a b i -> Mem.valid_block m b). 
Proof.
 intros.
 eapply eval_expr_lvalue_valid_aux; eassumption.
Qed.

Lemma eval_deref_loc_val_valid: forall g ve te m e b ofs v
  (LVal: eval_lvalue g ve te m e b ofs)
  (DL: deref_loc (typeof e) m b ofs v)
  (VE: valid_env ve m) (GE: valid_genv g m)
  (TE: valid_tempenv te m) (WD : mem_wd m),
  val_valid v m.
Proof. intros.
  destruct DL; simpl in *.
    eapply mem_wd_load; eassumption.
    eapply eval_lvalue_val_valid; try eassumption.
    eapply eval_lvalue_val_valid; try eassumption.
Qed.


Lemma assign_loc_mem_wd: forall 
  t1 m loc ofs v m'
  (Assign : assign_loc t1 m loc ofs v m')
  (g : Genv.t fundef type)
  ve te a1 a2 v2 
  (NV : type_is_volatile (typeof a1) = false)
  (Eval1 : eval_lvalue g ve te m a1 loc ofs)
  (Eval2 : eval_expr g ve te m a2 v2)
  (Cast : Cop.sem_cast v2 (typeof a2) (typeof a1) = Some v)
  (VE: valid_env ve m) (GE: valid_genv g m)
  (TE: valid_tempenv te m) 
  (WD : mem_wd m),
  t1 = typeof a1 -> mem_wd m'.
Proof.
  intros t1 m loc ofs v m' Assign.
  induction Assign; simpl; intros; subst.
  (*storev*)
    unfold Mem.storev in H0.
    eapply mem_wd_store; try eassumption.
    eapply sem_cast_val_valid; try eassumption.
     eapply eval_expr_val_valid; try eassumption.
  (*storebytes*)
     eapply mem_wd_storebytes; try eassumption.
     intros. eapply loadbytes_valid; eassumption. 
Qed. 


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

Definition valid_corestate (c:corestate) (m:mem) : Prop :=
  match c with
   veric.Clight_new.State ve te k => valid_env ve m /\ valid_tempenv te m
 | ExtCall ef sig args lid ve te k =>
            (forall v, In v args -> val_valid v m)
            /\ valid_env ve m /\ valid_tempenv te m
  end.

(*It'd be cice to use the following, but the type of coopstep requires cores
and memory to be disctinct parameters...)
Record coop_state {m} :=
  { cstate :> corestate; 
    state_valid : valid_corestate cstate m
  }.
*)

Definition coopstep (g : Genv.t fundef type) (c : corestate) 
  (m : mem) (c' : corestate) (m' : mem) :=
   valid_genv g m /\ (*valid_genv g m' /\*)
   valid_corestate c m /\ (*valid_corestate c' m' /\*)
   cl_step g c m c' m'.

Lemma cl_coopstep_not_at_external: forall ge m q m' q',
  coopstep ge q m q' m' -> cl_at_external q = None.
Proof.
  intros.
  eapply cl_corestep_not_at_external. apply H.
Qed.

Lemma cl_coopstep_not_halted :
  forall ge m q m' q', coopstep ge q m q' m' -> cl_safely_halted q = None.
Proof.
  intros.
  simpl; auto.
Qed.

Program Definition cl_coop_core_sem : 
  CoreSemantics (Genv.t fundef type) corestate mem  (list (ident * globdef fundef type)) :=
  @Build_CoreSemantics _ _ _ _
    cl_init_mem
    cl_initial_core
    cl_at_external
    cl_after_external
    cl_safely_halted
    coopstep
    cl_coopstep_not_at_external
    cl_coopstep_not_halted _
    cl_after_at_external_excl.

Lemma coop_mem_wd: forall (g : Genv.t fundef type) (c : corestate) 
  (m : mem) (c' : corestate) (m' : mem)
  (Step: coopstep g c m c' m') (WD: mem_wd m), mem_wd m'.
Proof. intros.
  destruct Step as [g_valid [c_valid step]].
(*  destruct Step as [g_valid [g_valid' c_valid [c_valid' step]]]].*)
  induction step; simpl in *; try eauto.
    destruct c_valid.
      eapply assign_loc_mem_wd; try eassumption.
        trivial.
    eapply alloc_variables_mem_wd; eassumption.
  eapply freelist_mem_wd; eassumption.
Qed.

Lemma coop_forward: forall (g : Genv.t fundef type) (c : corestate) 
  (m : mem) (c' : corestate) (m' : mem), 
  coopstep g c m c' m' -> mem_forward m m'.
Proof.
intros.
destruct H as [g_valid [c_valid step]].
eapply cl_forward; eassumption.
Qed.

Program Definition cl_coop_sem : 
  CoopCoreSem (Genv.t fundef type) corestate  (list (ident * globdef fundef type)).
apply Build_CoopCoreSem with (coopsem := cl_coop_core_sem).
  apply coop_forward.
  apply coop_mem_wd.
  intros. simpl in H. admit. (* TODO: cl_init_mem is not yet defined in Clight_new*)
Qed.
