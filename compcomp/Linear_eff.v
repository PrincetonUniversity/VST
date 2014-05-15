Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Export Maps.
Require Import Events.
Require Import Globalenvs.

Require Import Op.
Require Import Locations.
Require Import LTL. (*for undef_regs etc*)

Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.

Require Import Linear.
Require Import Linear_coop.
Require Import BuiltinEffects.

Section EFFSEM.

Variable ge: genv.

Inductive linear_effstep: (block -> Z -> bool) -> Linear_core -> mem -> Linear_core -> mem -> Prop :=
  | lin_effexec_Lgetstack:
      forall s f sp sl ofs ty dst b rs m rs',
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
      linear_effstep EmptyEffect 
        (Linear_State s f sp (Lgetstack sl ofs ty dst :: b) rs) m
        (Linear_State s f sp b rs') m
  | lin_effexec_Lsetstack:
      forall s f sp src sl ofs ty b rs m rs',
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
      linear_effstep EmptyEffect 
        (Linear_State s f sp (Lsetstack src sl ofs ty :: b) rs) m
        (Linear_State s f sp b rs') m
  | lin_effexec_Lop:
      forall s f sp op args res b rs m v rs',
      eval_operation ge sp op (reglist rs args) m = Some v ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      linear_effstep EmptyEffect 
        (Linear_State s f sp (Lop op args res :: b) rs) m
        (Linear_State s f sp b rs') m
  | lin_effexec_Lload:
      forall s f sp chunk addr args dst b rs m a v rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      linear_effstep EmptyEffect 
        (Linear_State s f sp (Lload chunk addr args dst :: b) rs) m
        (Linear_State s f sp b rs') m
  | lin_effexec_Lstore:
      forall s f sp chunk addr args src b rs m m' a rs',
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      linear_effstep (StoreEffect a (encode_val chunk (rs (R src))))
        (Linear_State s f sp (Lstore chunk addr args src :: b) rs) m
        (Linear_State s f sp b rs') m'
  | lin_effexec_Lcall:
      forall s f sp sig ros b rs m f',
      find_function ge ros rs = Some f' ->
      sig = funsig f' ->
      linear_effstep EmptyEffect 
        (Linear_State s f sp (Lcall sig ros :: b) rs) m
        (Linear_Callstate (Stackframe f sp rs b:: s) f' rs) m
  | lin_effexec_Ltailcall:
      forall s f stk sig ros b rs m rs' f' m',
      rs' = return_regs (parent_locset s) rs ->
      find_function ge ros rs' = Some f' ->
      sig = funsig f' ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      linear_effstep (FreeEffect m 0 (f.(fn_stacksize)) stk)
        (Linear_State s f (Vptr stk Int.zero) (Ltailcall sig ros :: b) rs) m
        (Linear_Callstate s f' rs') m'
  | lin_effexec_Lbuiltin:
      forall s f sp rs m ef args res b t vl rs' m',
      external_call' ef ge (reglist rs args) m t vl m' ->
      rs' = Locmap.setlist (map R res) vl (undef_regs (destroyed_by_builtin ef) rs) ->
      linear_effstep (BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) (reglist rs args)) m)
         (Linear_State s f sp (Lbuiltin ef args res :: b) rs) m
         (Linear_State s f sp b rs') m'
(*NO ANNOTS YET
  | lin_effexec_Lannot:
      forall s f sp rs m ef args b t v m',
      external_call' ef ge (map rs args) m t v m' ->
      linear_effstep (Linear_State s f sp (Lannot ef args :: b) rs) m
         (Linear_State s f sp b rs) m'*)
  | lin_effexec_Llabel:
      forall s f sp lbl b rs m,
      linear_effstep EmptyEffect 
        (Linear_State s f sp (Llabel lbl :: b) rs) m
        (Linear_State s f sp b rs) m
  | lin_effexec_Lgoto:
      forall s f sp lbl b rs m b',
      find_label lbl f.(fn_code) = Some b' ->
      linear_effstep EmptyEffect 
        (Linear_State s f sp (Lgoto lbl :: b) rs) m
        (Linear_State s f sp b' rs) m
  | lin_effexec_Lcond_true:
      forall s f sp cond args lbl b rs m rs' b',
      eval_condition cond (reglist rs args) m = Some true ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      find_label lbl f.(fn_code) = Some b' ->
      linear_effstep EmptyEffect 
        (Linear_State s f sp (Lcond cond args lbl :: b) rs) m
        (Linear_State s f sp b' rs') m
  | lin_effexec_Lcond_false:
      forall s f sp cond args lbl b rs m rs',
      eval_condition cond (reglist rs args) m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      linear_effstep EmptyEffect 
        (Linear_State s f sp (Lcond cond args lbl :: b) rs) m
        (Linear_State s f sp b rs') m
  | lin_effexec_Ljumptable:
      forall s f sp arg tbl b rs m n lbl b' rs',
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl f.(fn_code) = Some b' ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      linear_effstep EmptyEffect 
        (Linear_State s f sp (Ljumptable arg tbl :: b) rs) m
        (Linear_State s f sp b' rs') m
  | lin_effexec_Lreturn:
      forall s f stk b rs m m',
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      linear_effstep (FreeEffect m 0 (f.(fn_stacksize)) stk)
        (Linear_State s f (Vptr stk Int.zero) (Lreturn :: b) rs) m
        (Linear_Returnstate s (sig_res (fn_sig f)) (return_regs (parent_locset s) rs)) m'
  | lin_effexec_function_internal:
      forall s f rs m rs' m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      linear_effstep EmptyEffect 
        (Linear_Callstate s (Internal f) rs) m
        (Linear_State s f (Vptr stk Int.zero) f.(fn_code) rs') m'
(*NO RULE FOR EXTERNAL CALLS
  | lin_effexec_function_external:
      forall s ef args res rs1 rs2 m t m',
      args = map rs1 (loc_arguments (ef_sig ef)) ->
      external_call' ef ge args m t res m' ->
      rs2 = Locmap.setlist (map R (loc_result (ef_sig ef))) res rs1 ->
      linear_effstep (Linear_Callstate s (External ef) rs1) m
          (Linear_Returnstate s rs2) m'*)
  | lin_effexec_return:
      forall s f sp rs0 c retty rs m,
      linear_effstep EmptyEffect 
        (Linear_Returnstate (Stackframe f sp rs0 c :: s) retty rs) m
        (Linear_State s f sp c rs) m.

End EFFSEM.

Lemma linearstep_effax1: forall (M : block -> Z -> bool) g c m c' m',
      linear_effstep g M c m c' m' ->
      (corestep Linear_coop_sem g c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m').
Proof. 
intros.
  induction H.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         eapply StoreEffect_Storev; eassumption. 
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         eapply FreeEffect_free; eassumption.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         inv H.
         eapply BuiltinEffect_unchOn. eassumption.
(*  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         inv H. eapply ec_builtinEffectPolymorphic; eassumption.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         inv H. eapply ec_builtinEffectPolymorphic; eassumption.*)
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl.
         eapply lin_exec_Lcond_true; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl.
         eapply lin_exec_Lcond_false; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         eapply FreeEffect_free; eassumption. 
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         eapply Mem.alloc_unchanged_on; eassumption. 
  (*no external call*) 
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
Qed.

Lemma linearstep_effax2: forall  g c m c' m',
      corestep Linear_coop_sem g c m c' m' ->
      exists M, linear_effstep g M c m c' m'.
Proof.
intros. unfold corestep, coopsem in H; simpl in H.
  inv H.
    eexists. eapply lin_effexec_Lgetstack; try eassumption. trivial.
    eexists. eapply lin_effexec_Lsetstack; try eassumption. trivial. 
    eexists. eapply lin_effexec_Lop; try eassumption; trivial.
    eexists. eapply lin_effexec_Lload; try eassumption; trivial.
    eexists. eapply lin_effexec_Lstore; try eassumption; trivial.
    eexists. eapply lin_effexec_Lcall; try eassumption; trivial.    
    eexists. eapply lin_effexec_Ltailcall; try eassumption; trivial. 
    eexists. eapply lin_effexec_Lbuiltin; try eassumption; trivial. 
(*    eexists. eapply linear_effstep_Lannot; eassumption.*)
    eexists. eapply lin_effexec_Llabel; try eassumption; trivial.
    eexists. eapply lin_effexec_Lgoto; try eassumption; trivial.
    eexists. eapply lin_effexec_Lcond_true; try eassumption; trivial.
    eexists. eapply lin_effexec_Lcond_false; try eassumption; trivial.
    eexists. eapply lin_effexec_Ljumptable; try eassumption; trivial.
    eexists. eapply lin_effexec_Lreturn; eassumption.
    eexists. eapply lin_effexec_function_internal; try eassumption; trivial.
    eexists. eapply lin_effexec_return.
Qed.

Lemma linear_effstep_valid: forall (M : block -> Z -> bool) g c m c' m',
      linear_effstep g M c m c' m' ->
       forall b z, M b z = true -> Mem.valid_block m b.
Proof.
intros.
  induction H; try (solve [inv H0]).

  apply StoreEffectD in H0. destruct H0 as [ofs [VADDR ARITH]]; subst.
  inv H1. apply Mem.store_valid_access_3 in H2.
  eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies; try eassumption. constructor.

  eapply FreeEffect_validblock; eassumption.
  eapply BuiltinEffect_valid_block; eassumption.
  eapply FreeEffect_validblock; eassumption.
Qed.

Program Definition Linear_eff_sem : 
  @EffectSem genv Linear_core.
eapply Build_EffectSem with (sem := Linear_coop_sem)(effstep:=linear_effstep).
apply linearstep_effax1.
apply linearstep_effax2.
apply linear_effstep_valid.
(*intros. eapply linear_effstep_sub_val; eassumption.*)
Defined.
