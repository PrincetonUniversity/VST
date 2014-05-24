Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Export Maps.
Require Import Events.
Require Import Globalenvs.

Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Stacklayout.

Require Import Mach. 
Require Import Mach_coop. 

Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import BuiltinEffects.

Notation "a ## b" := (List.map a b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

Section EFFSEM.
Variable return_address_offset: function -> code -> int -> Prop.

Variable ge: genv.

Inductive mach_effstep: (block -> Z -> bool) -> 
                        Mach_core -> mem -> Mach_core -> mem -> Prop :=
  | Mach_effexec_Mlabel:
      forall s f sp lbl c rs m,
      mach_effstep EmptyEffect 
        (Mach_State s f sp (Mlabel lbl :: c) rs) m
        (Mach_State s f sp c rs) m
  | Mach_effexec_Mgetstack:
      forall s f sp ofs ty dst c rs m v,
      load_stack m sp ty ofs = Some v ->
      mach_effstep EmptyEffect 
        (Mach_State s f sp (Mgetstack ofs ty dst :: c) rs) m
        (Mach_State s f sp c (rs#dst <- v)) m
  | Mach_effexec_Msetstack:
      forall s f sp src ofs ty c rs m m' rs',
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      mach_effstep 
        (StoreEffect (Val.add sp (Vint ofs)) (encode_val (chunk_of_type ty) (rs src)))
        (Mach_State s f sp (Msetstack src ofs ty :: c) rs) m
        (Mach_State s f sp c rs') m'
  | Mach_effexec_Mgetparam:
      forall s fb f sp ofs ty dst c rs m v rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m sp Tint f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (parent_sp s) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      mach_effstep EmptyEffect 
        (Mach_State s fb sp (Mgetparam ofs ty dst :: c) rs) m
        (Mach_State s fb sp c rs') m
  | Mach_effexec_Mop:
      forall s f sp op args res c rs m v rs',
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      mach_effstep EmptyEffect 
        (Mach_State s f sp (Mop op args res :: c) rs) m
        (Mach_State s f sp c rs') m
  | Mach_effexec_Mload:
      forall s f sp chunk addr args dst c rs m a v rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      mach_effstep EmptyEffect 
        (Mach_State s f sp (Mload chunk addr args dst :: c) rs) m
        (Mach_State s f sp c rs') m
  | Mach_effexec_Mstore:
      forall s f sp chunk addr args src c rs m m' a rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      mach_effstep 
        (StoreEffect a (encode_val chunk (rs src)))
        (Mach_State s f sp (Mstore chunk addr args src :: c) rs) m
        (Mach_State s f sp c rs') m'
  | Mach_effexec_Mcall_internal:
      forall s fb sp sig ros c rs m f f' ra callee,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      (*NEW: check that the block f' actually contains a function:*)
         Genv.find_funct_ptr ge f' = Some (Internal callee) ->
      mach_effstep EmptyEffect 
        (Mach_State s fb sp (Mcall sig ros :: c) rs) m
        (Mach_Callstate (Stackframe fb sp (Vptr fb ra) c :: s)
                       f' rs) m
  | Mach_effexec_Mcall_external:
      forall s fb sp sig ros c rs m f f' ra callee args,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      (*NEW: check that the block f' actually contains a (external) function, and perform the "extra step":*)
         Genv.find_funct_ptr ge f' = Some (External callee) ->
      extcall_arguments rs m (parent_sp (Stackframe fb sp (Vptr fb ra) c ::s))
        (ef_sig callee) args ->
      mach_effstep EmptyEffect
         (Mach_State s fb sp (Mcall sig ros :: c) rs) m
         (Mach_CallstateArgs (Stackframe fb sp (Vptr fb ra) c :: s) f' callee args rs) m
  | Mach_effexec_Mtailcall_internal:
      forall s fb stk soff sig ros c rs m f f' m' callee,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      (*NEW: check that the block f' actually contains a function:*)
         Genv.find_funct_ptr ge f' = Some (Internal callee) ->
      mach_effstep (FreeEffect m 0 (f.(fn_stacksize)) stk)
        (Mach_State s fb (Vptr stk soff) (Mtailcall sig ros :: c) rs) m
        (Mach_Callstate s f' rs) m'
  | Mach_effexec_Mtailcall_external:
      forall s fb stk soff sig ros c rs m f f' m' callee args,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      (*NEW: check that the block f' actually contains a function:*)
         Genv.find_funct_ptr ge f' = Some (External callee) ->
      extcall_arguments rs m' (parent_sp s) (ef_sig callee) args ->
      mach_effstep (FreeEffect m 0 (f.(fn_stacksize)) stk)
         (Mach_State s fb (Vptr stk soff) (Mtailcall sig ros :: c) rs) m
         (Mach_CallstateArgs s f' callee args rs) m'
  | Mach_effexec_Mbuiltin:
      forall s f sp rs m ef args res b t vl rs' m',
      external_call' ef ge rs##args m t vl m' ->
      rs' = set_regs res vl (undef_regs (destroyed_by_builtin ef) rs) ->
      mach_effstep 
         (BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) (rs##args)) m)
         (Mach_State s f sp (Mbuiltin ef args res :: b) rs) m
         (Mach_State s f sp b rs') m'
(*NO SUPPORT FOR ANNOT YET
  | Mach_effexec_Mannot:
      forall s f sp rs m ef args b vargs t v m',
      annot_arguments rs m sp args vargs ->
      external_call' ef ge vargs m t v m' ->
      mach_effstep (Mach_State s f sp (Mannot ef args :: b) rs) m
         t (Mach_State s f sp b rs) m'*)
  | Mach_effexec_Mgoto:
      forall s fb f sp lbl c rs m c',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      mach_effstep EmptyEffect 
        (Mach_State s fb sp (Mgoto lbl :: c) rs) m
        (Mach_State s fb sp c' rs) m
  | Mach_effexec_Mcond_true:
      forall s fb f sp cond args lbl c rs m c' rs',
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      mach_effstep EmptyEffect 
        (Mach_State s fb sp (Mcond cond args lbl :: c) rs) m
        (Mach_State s fb sp c' rs') m
  | Mach_effexec_Mcond_false:
      forall s f sp cond args lbl c rs m rs',
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      mach_effstep EmptyEffect 
        (Mach_State s f sp (Mcond cond args lbl :: c) rs) m
        (Mach_State s f sp c rs') m
  | Mach_effexec_Mjumptable:
      forall s fb f sp arg tbl c rs m n lbl c' rs',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      mach_effstep EmptyEffect 
        (Mach_State s fb sp (Mjumptable arg tbl :: c) rs) m
        (Mach_State s fb sp c' rs') m
  | Mach_effexec_Mreturn:
      forall s fb stk soff c rs m f m',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      mach_effstep (FreeEffect m 0 (f.(fn_stacksize)) stk)
        (Mach_State s fb (Vptr stk soff) (Mreturn :: c) rs) m
        (Mach_Returnstate s (sig_res (fn_sig f)) rs) m'
  | Mach_effexec_function_internal:
      forall s fb rs m f m1 m2 m3 stk rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      let sp := Vptr stk Int.zero in
      store_stack m1 sp Tint f.(fn_link_ofs) (parent_sp s) = Some m2 ->
      store_stack m2 sp Tint f.(fn_retaddr_ofs) (parent_ra s) = Some m3 ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      mach_effstep EmptyEffect 
        (Mach_Callstate s fb rs) m
        (Mach_State s fb sp f.(fn_code) rs') m3
(*auxiliary step that extracts call arguments and invoked external function,
  in accordance with the core semantics interface
  | Mach_effexec_function_external:
      forall s fb rs m ef args,
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      extcall_arguments rs m (parent_sp s) (ef_sig ef) args ->
      mach_effstep EmptyEffect 
        (Mach_Callstate s fb rs) m
        (Mach_CallstateArgs s (*(parent_sp s)*) fb ef args rs) m*)
(*NO RULE FOR EXTERNAL CALLS
  | Mach_effexec_function_external:
      forall s fb rs m t rs' ef args res m',
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      extcall_arguments rs m (parent_sp s) (ef_sig ef) args ->
      external_call' ef ge args m t res m' ->
      rs' = set_regs (loc_result (ef_sig ef)) res rs ->
      mach_effstep (Callstate s fb rs) m
         t (Mach_Returnstate s rs') m'*)
  | Mach_effexec_return:
      forall s f sp ra c retty rs m,
      mach_effstep EmptyEffect 
        (Mach_Returnstate (Stackframe f sp ra c :: s) retty rs) m
        (Mach_State s f sp c rs) m.

End EFFSEM.

Section MACH_EFFSEM.
Variable return_address_offset: function -> code -> int -> Prop.

Lemma machstep_effax1: forall (M : block -> Z -> bool) g c m c' m',
      mach_effstep return_address_offset g M c m c' m' ->
      (corestep (Mach_coop_sem return_address_offset) g c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m').
Proof. 
intros.
  induction H.
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; eassumption.
         unfold store_stack in H.
         eapply StoreEffect_Storev; eassumption. 
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; eassumption.
         eapply StoreEffect_Storev; eassumption. 
  split. eapply Mach_exec_Mcall_internal; eassumption.
         apply Mem.unchanged_on_refl.
  split. eapply Mach_exec_Mcall_external; eassumption.
         apply Mem.unchanged_on_refl.
  split. eapply Mach_exec_Mtailcall_internal; eassumption.
         eapply FreeEffect_free; eassumption.
  split. eapply Mach_exec_Mtailcall_external; eassumption.
         eapply FreeEffect_free; eassumption.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         inv H.
         eapply BuiltinEffect_unchOn. eassumption.
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. eapply Mach_exec_Mcond_true; eassumption.
         apply Mem.unchanged_on_refl.
  split. eapply Mach_exec_Mcond_false; eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; eassumption.
         eapply FreeEffect_free; eassumption.
  split. econstructor; eassumption. subst sp.
    subst. 
    unfold store_stack, Val.add in *. rewrite Int.add_zero_l in *.
    simpl in *. 
    remember (Int.unsigned (fn_link_ofs f)) as z1.
    remember (Int.unsigned (fn_retaddr_ofs f)) as z2.
    remember (parent_sp s) as v1. 
    remember (parent_ra s) as v2. 
    clear Heqz1 H Heqz2 Heqv1 Heqv2.
    split; intros.
      split; intros.
        eapply Mem.perm_store_1; try eassumption.
        eapply Mem.perm_store_1; try eassumption.
        eapply Mem.perm_alloc_1; eassumption.
      apply (Mem.perm_store_2 _ _ _ _ _ _ H2) in H4.
        apply (Mem.perm_store_2 _ _ _ _ _ _ H1) in H4.
        eapply Mem.perm_alloc_4; try eassumption.
         intros N; subst. apply Mem.fresh_block_alloc in H0. contradiction.
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ H2).
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ H1).
        assert (BB: b <> stk). intros N. subst. apply Mem.fresh_block_alloc in H0. apply Mem.perm_valid_block in H3. contradiction.
        rewrite PMap.gso; trivial. 
        rewrite PMap.gso; trivial. 
        eapply EmptyEffect_alloc; eassumption.
(*  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.*)
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
Qed.

Lemma  machstep_effax2: forall  g c m c' m',
      corestep (Mach_coop_sem return_address_offset) g c m c' m' ->
      exists M, mach_effstep return_address_offset g M c m c' m'.
Proof.
  intros. unfold corestep, coopsem in H; simpl in H.
  inv H.
    eexists. eapply Mach_effexec_Mlabel; eassumption.
    eexists. eapply Mach_effexec_Mgetstack; try eassumption; trivial.
    eexists. eapply Mach_effexec_Msetstack; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mgetparam; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mop; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mload; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mstore; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mcall_internal; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mcall_external; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mtailcall_internal; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mtailcall_external; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mbuiltin; try eassumption; trivial.
(*    eexists. eapply Mach_effexec_Mannot; try eassumption; trivial.*)
    eexists. eapply Mach_effexec_Mgoto; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mcond_true; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mcond_false; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mjumptable; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mreturn; try eassumption; trivial.
    eexists. eapply Mach_effexec_function_internal; try eassumption; trivial.
(*    eexists. eapply Mach_effexec_function_external; try eassumption; trivial.*)
    eexists. eapply Mach_effexec_return; try eassumption; trivial.
Qed.

Lemma mach_effstep_valid: forall (M : block -> Z -> bool) g c m c' m',
      mach_effstep return_address_offset g M c m c' m' ->
       forall b z, M b z = true -> Mem.valid_block m b.
Proof.
intros.
  induction H; try (solve [inv H0]).

  unfold store_stack in H.
  apply StoreEffectD in H0. destruct H0 as [i [VADDR ARITH]]; subst.
  destruct sp; inv H. unfold Val.add in VADDR. inv VADDR.
  apply Mem.store_valid_access_3 in H1.
  eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies; try eassumption. constructor.

  apply StoreEffectD in H0. destruct H0 as [ofs [VADDR ARITH]]; subst.
  inv H1. apply Mem.store_valid_access_3 in H2.
  eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies; try eassumption. constructor.

  eapply FreeEffect_validblock; eassumption.
  eapply FreeEffect_validblock; eassumption.
  eapply BuiltinEffect_valid_block; eassumption.
  eapply FreeEffect_validblock; eassumption.
Qed.

Program Definition Mach_eff_sem : 
  @EffectSem genv Mach_core.
eapply Build_EffectSem with 
 (sem := Mach_coop_sem return_address_offset).
apply machstep_effax1.
apply machstep_effax2.
apply mach_effstep_valid. 
Defined.

End MACH_EFFSEM.