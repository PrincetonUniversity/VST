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
Require Import Op.
Require Import Registers.

Require Import sepcomp.RTL.
Require Import sepcomp.RTL_coop.

Inductive RTL_effstep (ge:genv):  (block -> Z -> bool) ->
            RTL_core -> mem -> RTL_core -> mem -> Prop :=
  | rtl_effstep_exec_Inop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Inop pc') ->
      RTL_effstep ge EmptyEffect (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' rs) m
  | rtl_effstep_exec_Iop:
      forall s f sp pc rs m op args res pc' v,
      (fn_code f)!pc = Some(Iop op args res pc') ->
      eval_operation ge sp op rs##args m = Some v ->
      RTL_effstep ge EmptyEffect (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' (rs#res <- v)) m
  | rtl_effstep_exec_Iload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      RTL_effstep ge EmptyEffect (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' (rs#dst <- v)) m
  | rtl_effstep_exec_Istore:
      forall s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      RTL_effstep ge (StoreEffect a (encode_val chunk (rs#src)))
        (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' rs) m'
  | rtl_effstep_exec_Icall:
      forall s f sp pc rs m sig ros args res pc' fd,
      (fn_code f)!pc = Some(Icall sig ros args res pc') ->
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      RTL_effstep ge EmptyEffect
        (RTL_State s f sp pc rs) m
        (RTL_Callstate (Stackframe res f sp pc' rs :: s) fd rs##args) m
  | rtl_effstep_exec_Itailcall:
      forall s f stk pc rs m sig ros args fd m',
      (fn_code f)!pc = Some(Itailcall sig ros args) ->
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      RTL_effstep ge (FreeEffect m 0 (f.(fn_stacksize)) stk)
        (RTL_State s f (Vptr stk Int.zero) pc rs) m
        (RTL_Callstate s fd rs##args) m'

(* WE DO NOT TREAT BUILTINS
  | rtl_effstep_exec_Ibuiltin:
      forall s f sp pc rs m ef args res pc' t v m',
      (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      external_call ef ge rs##args m t v m' ->
      RTL_effstep ge
         (BuiltinEffect ge (ef_sig ef) (rs##args) m)
         (RTL_State s f sp pc rs) m
         (RTL_State s f sp pc' (rs#res <- v)) m'
*)
  | rtl_effstep_exec_Icond:
      forall s f sp pc rs m cond args ifso ifnot b pc',
      (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      RTL_effstep ge EmptyEffect
        (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' rs) m
  | rtl_effstep_exec_Ijumptable:
      forall s f sp pc rs m arg tbl n pc',
      (fn_code f)!pc = Some(Ijumptable arg tbl) ->
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      RTL_effstep ge EmptyEffect
        (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' rs) m
  | rtl_effstep_exec_Ireturn:
      forall s f stk pc rs m or m',
      (fn_code f)!pc = Some(Ireturn or) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      RTL_effstep ge (FreeEffect m 0 (f.(fn_stacksize)) stk)
        (RTL_State s f (Vptr stk Int.zero) pc rs) m
        (RTL_Returnstate s (regmap_optget or Vundef rs)) m'
  | rtl_effstep_exec_function_internal:
      forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      RTL_effstep ge EmptyEffect
        (RTL_Callstate s (Internal f) args) m
        (RTL_State s
                  f
                  (Vptr stk Int.zero)
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params)))
        m'
(*no external calls
  | rtl_effstep_exec_function_external:
      forall s ef args res t m m',
      external_call ef ge args m t res m' ->
      RTL_effstep ge (Callstate s (External ef) args) m
         t (Returnstate s res m')*)
  | rtl_effstep_exec_return:
      forall res f sp pc rs s vres m,
      RTL_effstep ge EmptyEffect
        (RTL_Returnstate (Stackframe res f sp pc rs :: s) vres) m
        (RTL_State s f sp pc (rs#res <- vres)) m

  | rtl_effstep_sub_val: forall E EE c m c' m',
      (forall b ofs, Mem.valid_block m b ->
                     E b ofs = true -> EE b ofs = true) ->
      RTL_effstep ge E c m c' m' ->
      RTL_effstep ge EE c m c' m'.

Lemma rtl_eff_exec_Iload':
  forall ge s f sp pc rs m chunk addr args dst pc' rs' a v,
  (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
  Op.eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  rs' = (rs#dst <- v) ->
  RTL_effstep ge EmptyEffect
      (RTL_State s f sp pc rs) m
      (RTL_State  s f sp pc' rs') m.
Proof.
  intros. subst rs'. eapply rtl_effstep_exec_Iload; eauto.
Qed.

Lemma rtl_eff_exec_Iop':
  forall g s f sp pc rs m op args res pc' rs' v,
  (fn_code f)!pc = Some(Iop op args res pc') ->
  Op.eval_operation g sp op rs##args m = Some v ->
  rs' = (Registers.Regmap.set res v rs) ->
  RTL_effstep g EmptyEffect (RTL_State s f sp pc rs) m
    (RTL_State s f sp pc' rs') m.
Proof.
  intros. subst rs'. eapply rtl_effstep_exec_Iop; eauto.
Qed.

Lemma rtl_effax1: forall (M : block -> Z -> bool) g c m c' m',
      RTL_effstep g M c m c' m' ->
      (corestep rtl_coop_sem g c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m').
Proof.
intros.
  induction H.
  split. unfold corestep, coopsem; simpl.
         eapply rtl_corestep_exec_Inop; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl.
         eapply rtl_corestep_exec_Iop; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl.
         eapply rtl_corestep_exec_Iload; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl.
         eapply rtl_corestep_exec_Istore; eassumption.
         eapply StoreEffect_Storev; eassumption.
  split. unfold corestep, coopsem; simpl.
         eapply rtl_corestep_exec_Icall; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl.
         eapply rtl_corestep_exec_Itailcall; eassumption.
         eapply FreeEffect_free; eassumption.
(*  split. unfold corestep, coopsem; simpl.
         eapply rtl_corestep_exec_Ibuiltin; eassumption.
         eapply ec_builtinEffectPolymorphic; eassumption.*)
  split. unfold corestep, coopsem; simpl.
         eapply rtl_corestep_exec_Icond; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl.
         eapply rtl_corestep_exec_Ijumptable; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep, coopsem; simpl.
         eapply rtl_corestep_exec_Ireturn; eassumption.
         eapply FreeEffect_free; eassumption.
  split. unfold corestep, coopsem; simpl.
         eapply rtl_corestep_exec_function_internal; eassumption.
         eapply Mem.alloc_unchanged_on; eassumption.
  split. unfold corestep, coopsem; simpl.
         eapply rtl_corestep_exec_return; eassumption.
         apply Mem.unchanged_on_refl.
  (*effstep_sub_val*)
    destruct IHRTL_effstep.
    split; trivial.
    eapply unchanged_on_validblock; try eassumption.
    intros; simpl. remember (E b ofs) as d.
    destruct d; trivial. apply eq_sym in Heqd.
    rewrite (H _ _ H3 Heqd) in H4. discriminate.
Qed.

Lemma rtl_effax2: forall  g c m c' m',
      corestep rtl_coop_sem g c m c' m' ->
      exists M, RTL_effstep g M c m c' m'.
Proof.
intros. inv H.
    eexists. eapply rtl_effstep_exec_Inop; eassumption.
    eexists. eapply rtl_effstep_exec_Iop; eassumption.
    eexists. eapply rtl_effstep_exec_Iload; eassumption.
    eexists. eapply rtl_effstep_exec_Istore; eassumption.
    eexists. eapply rtl_effstep_exec_Icall; try eassumption. trivial.
    eexists. eapply rtl_effstep_exec_Itailcall; try eassumption. trivial.
   (* eexists. eapply rtl_effstep_exec_Ibuiltin; eassumption.*)
    eexists. eapply rtl_effstep_exec_Icond; try eassumption. trivial.
    eexists. eapply rtl_effstep_exec_Ijumptable; eassumption.
    eexists. eapply rtl_effstep_exec_Ireturn; eassumption.
    eexists. eapply rtl_effstep_exec_function_internal; eassumption.
    eexists. eapply rtl_effstep_exec_return.
Qed.

(*
Lemma RTL_effstep_sub: forall g U V c m c' m'
         (UV: forall b ofs, U b ofs = true -> V b ofs = true),
         (RTL_effstep g U c m c' m' -> RTL_effstep g V c m c' m').
Qed.
*)
(*
Definition cmin_effstep ge (E:block -> Z -> bool)
   (c : RTL_core) m (c' : RTL_core) m': Prop :=
   coopstep g c m c' m' /\ Mem.unchanged_on (fun b ofs => E b ofs = false) m m'.
*)

Program Definition rtl_eff_sem :
  @EffectSem genv RTL_core.
eapply Build_EffectSem with (sem := rtl_coop_sem)(effstep:=RTL_effstep).
apply rtl_effax1.
apply rtl_effax2.
intros.
eapply rtl_effstep_sub_val; eassumption.
Defined.

