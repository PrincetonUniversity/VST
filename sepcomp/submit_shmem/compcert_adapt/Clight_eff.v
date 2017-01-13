Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Export Maps.
Require Import Events.
Require Import Globalenvs.

Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.

Require Import Cop. (*for sem_cast*)
Require Import Ctypes. (*for access_mode*)
Require Import Clight.
Require Import Clight_coop.

Definition assign_loc_Effect (ty:type) (b: block) (ofs: int) v : (block -> Z -> bool)  :=
  match access_mode ty with
     By_value chunk => fun b' z' => eq_block b b'
              && zle (Int.unsigned ofs) z'
              && zlt z' ((Int.unsigned ofs) + Z.of_nat (length (encode_val chunk v)))
   | By_copy => fun b' z' => eq_block b' b
              && zle (Int.unsigned ofs) z'
              && zlt z' ((Int.unsigned ofs) + (sizeof ty))
   | _ => fun b' z' => false
  end.

Lemma assign_loc_Effect_Sound: forall a m loc ofs v m'
      (AL: assign_loc (typeof a) m loc ofs v m'),
     Mem.unchanged_on (fun b z => assign_loc_Effect (typeof a)
                            loc ofs v b z = false) m m'.
Proof. intros. inv AL.
inv H0.
(*access_mode (typeof a) = By_value chunk*)
  split; intros.
  (*perm*)
    split; intros.
    eapply Mem.perm_store_1; eassumption.
    eapply Mem.perm_store_2; eassumption.
  (*memcontents*)
    rewrite (Mem.store_mem_contents _ _ _ _ _ _ H2).
    unfold assign_loc_Effect in H0; rewrite H in H0.
    destruct (eq_block loc b); subst; simpl in H0.
      rewrite PMap.gss. rewrite andb_false_iff in H0.
      apply Mem.setN_other. intros; intros N. subst.
      destruct H3.
      destruct (zle (Int.unsigned ofs) ofs0); simpl in *.
        destruct H0; try discriminate.
        destruct (zlt ofs0 (Int.unsigned ofs + Z.of_nat (length (encode_val chunk v)))); simpl in *. discriminate.
        omega.
      omega.
    rewrite PMap.gso; trivial. intros N; subst; apply n; trivial.
(*access_mode (typeof a) = By_copy*)
  split; intros.
  (*perm*)
    split; intros.
    eapply Mem.perm_storebytes_1; eassumption.
    eapply Mem.perm_storebytes_2; eassumption.
  (*memcontents*)
    rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H4).
    unfold assign_loc_Effect in H5; rewrite H in H5.
    destruct (eq_block b loc); subst; simpl in H5.
      rewrite PMap.gss. rewrite andb_false_iff in H5.
      apply Mem.setN_other. intros; intros N. subst.
      destruct H7.
      destruct (zle (Int.unsigned ofs) ofs0); simpl in *.
        destruct H5; try discriminate.
        destruct (zlt ofs0 (Int.unsigned ofs + sizeof (typeof a))); simpl in *. discriminate.
        apply Mem.loadbytes_length in H3. rewrite H3 in H8.
          rewrite nat_of_Z_eq in H8. omega.
          assert (ZZZ:= sizeof_pos (typeof a)). omega.
      omega.
    rewrite PMap.gso; trivial.
Qed.

Lemma alloc_variables_unchanged_on:
      forall P args env m e m' (H:alloc_variables env m args e m'),
      Mem.unchanged_on P m m'.
Proof. intros P args.
  induction args; simpl; intros; inv H.
    apply Mem.unchanged_on_refl.
  apply IHargs  in H7.
  specialize (alloc_forward _ _ _ _ _ H4). intros.
  eapply unchanged_on_trans;  try eassumption.
  eapply Mem.alloc_unchanged_on. eassumption.
Qed.

Lemma alloc_variables_freshblocks: forall vars E m e m1
      (AL: alloc_variables E m vars e m1)
      id b t (Hid: e!id = Some (b,t)),
      E!id = Some (b,t) \/ ~Mem.valid_block m b.
Proof. intros vars.
  induction vars; simpl; intros; inv AL; simpl in *.
    left; trivial.
  destruct (IHvars _ _ _ _ H6 _ _ _ Hid); clear IHvars.
    rewrite PTree.gsspec in H.
    destruct (peq id id0); subst.
      inv H. right. eapply Mem.fresh_block_alloc; eassumption.
      left; trivial.
    right. intros N; elim H; clear H.
      eapply Mem.valid_block_alloc; eassumption.
Qed.

Lemma assign_loc_forward: forall ty m b ofs v m1
      (A: assign_loc ty m b ofs v m1),
      mem_forward m m1.
Proof. intros.
  inv A.
   inv H0. eapply (store_forward _ _ _ _ _ _ H2).
   eapply (storebytes_forward _ _ _ _ _ H4).
Qed.

Section EFFSEM.
Variable FE:function -> list val -> mem -> env -> temp_env -> mem -> Prop.

Inductive clight_effstep (ge:genv): (block -> Z -> bool) ->
            CL_core -> mem -> CL_core -> mem -> Prop :=
  | clight_effstep_assign:   forall f a1 a2 k e le m loc ofs v2 v m',
      eval_lvalue ge e le m a1 loc ofs ->
      eval_expr ge e le m a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) = Some v ->
      assign_loc (typeof a1) m loc ofs v m' ->
      clight_effstep ge (assign_loc_Effect (typeof a1) loc ofs v)
        (CL_State f (Sassign a1 a2) k e le) m
        (CL_State f Sskip k e le) m'

  | clight_effstep_set:   forall f id a k e le m v,
      eval_expr ge e le m a v ->
      clight_effstep ge EmptyEffect (CL_State f (Sset id a) k e le) m
        (CL_State f Sskip k e (PTree.set id v le)) m

  | clight_effstep_call:   forall f optid a al k e le m tyargs tyres vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres ->
      eval_expr ge e le m a vf ->
      eval_exprlist ge e le m al tyargs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres ->
      clight_effstep ge EmptyEffect (CL_State f (Scall optid a al) k e le) m
        (CL_Callstate fd vargs (Kcall optid f e le k)) m

(* WE DO NOT TREAT BUILTINS
  | clight_effstep_builtin:   forall f optid ef tyargs al k e le m vargs t vres m',
      eval_exprlist ge e le m al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      clight_effstep ge (BuiltinEffect ge (ef_sig ef) vargs m)
         (CL_State f (Sbuiltin optid ef tyargs al) k e le) m
         (CL_State f Sskip k e (set_opttemp optid vres le)) m'
*)
  | clight_effstep_seq:  forall f s1 s2 k e le m,
      clight_effstep ge EmptyEffect (CL_State f (Ssequence s1 s2) k e le) m
        (CL_State f s1 (Kseq s2 k) e le) m

  | clight_effstep_skip_seq: forall f s k e le m,
      clight_effstep ge EmptyEffect (CL_State f Sskip (Kseq s k) e le) m
        (CL_State f s k e le) m
  | clight_effstep_continue_seq: forall f s k e le m,
      clight_effstep ge EmptyEffect
        (CL_State f Scontinue (Kseq s k) e le) m
        (CL_State f Scontinue k e le) m

  | clight_effstep_break_seq: forall f s k e le m,
      clight_effstep ge EmptyEffect (CL_State f Sbreak (Kseq s k) e le) m
        (CL_State f Sbreak k e le) m

  | clight_effstep_ifthenelse:  forall f a s1 s2 k e le m v1 b,
      eval_expr ge e le m a v1 ->
      bool_val v1 (typeof a) = Some b ->
      clight_effstep ge EmptyEffect
        (CL_State f (Sifthenelse a s1 s2) k e le) m
        (CL_State f (if b then s1 else s2) k e le) m

  | clight_effstep_loop: forall f s1 s2 k e le m,
      clight_effstep ge EmptyEffect
        (CL_State f (Sloop s1 s2) k e le) m
        (CL_State f s1 (Kloop1 s1 s2 k) e le) m
  | clight_effstep_skip_or_continue_loop1:  forall f s1 s2 k e le m x,
      x = Sskip \/ x = Scontinue ->
      clight_effstep ge EmptyEffect
        (CL_State f x (Kloop1 s1 s2 k) e le) m
        (CL_State f s2 (Kloop2 s1 s2 k) e le) m
  | clight_effstep_break_loop1:  forall f s1 s2 k e le m,
      clight_effstep ge EmptyEffect
        (CL_State f Sbreak (Kloop1 s1 s2 k) e le) m
        (CL_State f Sskip k e le) m
  | clight_effstep_skip_loop2: forall f s1 s2 k e le m,
      clight_effstep ge EmptyEffect
        (CL_State f Sskip (Kloop2 s1 s2 k) e le) m
        (CL_State f (Sloop s1 s2) k e le) m
  | clight_effstep_break_loop2: forall f s1 s2 k e le m,
      clight_effstep ge EmptyEffect
        (CL_State f Sbreak (Kloop2 s1 s2 k) e le) m
        (CL_State f Sskip k e le) m

  | clight_effstep_return_0: forall f k e le m m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      clight_effstep ge (FreelistEffect m (blocks_of_env e))
        (CL_State f (Sreturn None) k e le) m
        (CL_Returnstate Vundef (call_cont k)) m'
  | clight_effstep_return_1: forall f a k e le m v v' m',
      eval_expr ge e le m a v ->
      sem_cast v (typeof a) f.(fn_return) = Some v' ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      clight_effstep ge (FreelistEffect m (blocks_of_env e))
        (CL_State f (Sreturn (Some a)) k e le) m
        (CL_Returnstate v' (call_cont k)) m'
  | clight_effstep_skip_call: forall f k e le m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      clight_effstep ge (FreelistEffect m (blocks_of_env e))
        (CL_State f Sskip k e le) m
        (CL_Returnstate Vundef k) m'

  | clight_effstep_switch: forall f a sl k e le m n,
      eval_expr ge e le m a (Vint n) ->
      clight_effstep ge EmptyEffect
       (CL_State f (Sswitch a sl) k e le) m
        (CL_State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch k) e le) m
  | clight_effstep_skip_break_switch: forall f x k e le m,
      x = Sskip \/ x = Sbreak ->
      clight_effstep ge EmptyEffect
        (CL_State f x (Kswitch k) e le) m
        (CL_State f Sskip k e le) m
  | clight_effstep_continue_switch: forall f k e le m,
      clight_effstep ge EmptyEffect
        (CL_State f Scontinue (Kswitch k) e le) m
        (CL_State f Scontinue k e le) m

  | clight_effstep_label: forall f lbl s k e le m,
      clight_effstep ge EmptyEffect
        (CL_State f (Slabel lbl s) k e le) m
        (CL_State f s k e le) m

  | clight_effstep_goto: forall f lbl k e le m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      clight_effstep ge EmptyEffect
        (CL_State f (Sgoto lbl) k e le) m
        (CL_State f s' k' e le) m

  | clight_effstep_internal_function: forall f vargs k m e le m',
      FE f vargs m e le m' ->
      clight_effstep ge EmptyEffect
        (CL_Callstate (Internal f) vargs k) m
        (CL_State f f.(fn_body) k e le) m'
(*no external step
  | step_external_function: forall ef targs tres vargs k m vres t m',
      external_call ef ge vargs m t vres m' ->
      clight_effstep (CL_Callstate (External ef targs tres) vargs k) m
         (CL_Returnstate vres k) m'
*)

  | clight_effstep_returnstate: forall v optid f e le k m,
      clight_effstep ge EmptyEffect
        (CL_Returnstate v (Kcall optid f e le k)) m
        (CL_State f Sskip k e (set_opttemp optid v le)) m

  | clight_effstep_sub_val: forall E EE c m c' m',
      (forall b ofs, Mem.valid_block m b ->
                     E b ofs = true -> EE b ofs = true) ->
      clight_effstep ge E c m c' m' ->
      clight_effstep ge EE c m c' m'.

Variable FE_FWD: forall f vargs m e le m', FE f vargs m e le m' -> mem_forward m m'.
Variable FE_UNCH: forall f vargs m e le m', FE f vargs m e le m'->
         Mem.unchanged_on (fun b z => EmptyEffect b z = false) m m'.

Lemma clightstep_effax1: forall (M : block -> Z -> bool) ge c m c' m'
      (H: clight_effstep ge M c m c' m'),
       corestep (CL_coop_sem FE FE_FWD) ge c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m'.
Proof.
intros.
  induction H.
  split. econstructor; try eassumption.
         eapply assign_loc_Effect_Sound; eassumption.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
(*  split. econstructor; try eassumption.
         eapply ec_builtinEffectPolymorphic; eassumption.*)
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         eapply FreelistEffect_freelist; eassumption.
  split. econstructor; try eassumption.
         eapply FreelistEffect_freelist; eassumption.
  split. econstructor; try eassumption.
         eapply FreelistEffect_freelist; eassumption.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         eapply FE_UNCH; eassumption.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  (*effstep_sub_val*)
    destruct IHclight_effstep.
    split; trivial.
    eapply unchanged_on_validblock; try eassumption.
    intros; simpl. remember (E b ofs) as d.
    destruct d; trivial. apply eq_sym in Heqd.
    rewrite (H _ _ H3 Heqd) in H4. discriminate.
Qed.

Lemma clightstep_effax2: forall ge c m c' m',
      corestep (CL_coop_sem FE FE_FWD) ge c m c' m' ->
      exists M, clight_effstep ge M c m c' m'.
Proof.
intros. inv H.
  eexists. eapply clight_effstep_assign; eassumption.
  eexists. eapply clight_effstep_set; eassumption.
  eexists. eapply clight_effstep_call; eassumption.
(*  eexists. eapply clight_effstep_builtin; eassumption.*)
  eexists. eapply clight_effstep_seq; eassumption.
  eexists. eapply clight_effstep_skip_seq; eassumption.
  eexists. eapply clight_effstep_continue_seq; eassumption.
  eexists. eapply clight_effstep_break_seq; eassumption.
  eexists. eapply clight_effstep_ifthenelse; eassumption.
  eexists. eapply clight_effstep_loop; eassumption.
  eexists. eapply clight_effstep_skip_or_continue_loop1; eassumption.
  eexists. eapply clight_effstep_break_loop1; eassumption.
  eexists. eapply clight_effstep_skip_loop2; eassumption.
  eexists. eapply clight_effstep_break_loop2; eassumption.
  eexists. eapply clight_effstep_return_0; eassumption.
  eexists. eapply clight_effstep_return_1; eassumption.
  eexists. eapply clight_effstep_skip_call; eassumption.
  eexists. eapply clight_effstep_switch; eassumption.
  eexists. eapply clight_effstep_skip_break_switch; eassumption.
  eexists. eapply clight_effstep_continue_switch; eassumption.
  eexists. eapply clight_effstep_label; eassumption.
  eexists. eapply clight_effstep_goto; eassumption.
  eexists. eapply clight_effstep_internal_function; eassumption.
  eexists. eapply clight_effstep_returnstate; eassumption.
Qed.

Definition clight_eff_sem
  :  @EffectSem Clight.genv CL_core.
eapply Build_EffectSem with (sem := CL_coop_sem _ FE_FWD)
         (effstep:=clight_effstep).
eapply clightstep_effax1.
apply clightstep_effax2.
apply clight_effstep_sub_val.
Defined.
End EFFSEM.

Lemma function_entry1_UNCH: forall f vargs m e le m',
      function_entry1 f vargs m e le m'->
      Mem.unchanged_on (fun b z => EmptyEffect b z = false) m m'.
Proof. intros. inv H.
  assert (FRESH: forall id b ty,
           e ! id = Some (b, ty) -> ~ Mem.valid_block m b).
    intros.
    destruct (alloc_variables_freshblocks _ _ _ _ _ H1 _ _ _ H); trivial.
      rewrite PTree.gempty in H3. discriminate.
  clear H0.
  apply unchanged_on_validblock with (V:= fun b z => Mem.valid_block m b /\ EmptyEffect b z = false).
    simpl; intros. split; trivial.
  specialize (alloc_variables_forward _ _ _ _ _ H1).
  eapply unchanged_on_trans; try eassumption.
    eapply alloc_variables_unchanged_on; eassumption.
  clear H1. remember (fn_params f) as pars. clear Heqpars.
  generalize dependent m1. generalize dependent vargs.
  induction pars; simpl; intros.
    inv H2. apply Mem.unchanged_on_refl.
    inv H2. specialize (IHpars _ _ H7).
    apply FRESH in H1.
    eapply unchanged_on_trans; try eassumption;
      try (eapply assign_loc_forward; eassumption).
    clear H7 IHpars FRESH.
    inv H4.
      inv H0.
      split; intros.
        split; intros.
          eapply Mem.perm_store_1; eassumption.
          eapply Mem.perm_store_2; eassumption.
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ H3).
        rewrite PMap.gso. trivial.
        destruct H0. intros N; subst. contradiction.
    split; intros.
      split; intros.
        eapply Mem.perm_storebytes_1; eassumption.
        eapply Mem.perm_storebytes_2; eassumption.
      rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H6).
        rewrite PMap.gso. trivial.
        destruct H4. intros N; subst. contradiction.
Qed.

Lemma function_entry2_UNCH: forall f vargs m e le m',
      function_entry2 f vargs m e le m'->
      Mem.unchanged_on (fun b z => EmptyEffect b z = false) m m'.
Proof. intros. inv H.
    eapply alloc_variables_unchanged_on; eassumption.
Qed.

Definition CL_eff_sem1: @EffectSem Clight.genv CL_core.
  eapply (clight_eff_sem function_entry1).
  apply function_entry1_forward.
  apply function_entry1_UNCH.
Defined.

Definition CL_eff_sem2: @EffectSem Clight.genv CL_core.
  eapply (clight_eff_sem function_entry2).
  apply function_entry2_forward.
  apply function_entry2_UNCH.
Defined.
