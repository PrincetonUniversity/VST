Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.
Require Import ccc26x86.Locations.
(*Require Import Stacklayout.*)
Require Import ccc26x86.Conventions.

Require Import ccc26x86.Asm.
(*LENB: In CompComp, we used a modified Asm.v, called Asm.comp.v*)

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.semantics.
Require Import sepcomp.semantics_lemmas.
Require Import sepcomp.val_casted.
Require Import ccc26x86.BuiltinEffects.
Require Import ccc26x86.load_frame.

Notation SP := ESP (only parsing).

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

Inductive load_frame: Type :=
| mk_load_frame:
    forall (sp: block)           (**r pointer to argument frame *)
           (retty: option typ),  (**r return type *)
    load_frame.

Section ASM_MEM.
Variable hf : I64Helpers.helper_functions.

Section RELSEM.
Variable ge: genv.

Inductive state: Type :=
  | State: 
      forall (rs: regset)
             (loader: load_frame),     (**r program loader frame *)
        state

  (*Auxiliary state: for marshalling arguments INTO memory*)
  | Asm_CallstateIn: 
      forall (f: block)                (**r pointer to function to call *)
             (args: list val)          (**r arguments passed to initial_core *)
             (tys: list typ)           (**r argument types *)
             (retty: option typ),      (**r return type *)       
        state

  (*Auxiliary state: for marshalling arguments OUT OF memory*)
  | Asm_CallstateOut: 
      forall (f: external_function)    (**r external function to be called *)
             (vals: list val)          (**r at_external arguments *)
             (rs: regset)              (**r register state *)
             (loader: load_frame),     (**r program loader frame *)
        state.

Inductive asm_step: state -> mem -> state -> mem -> Prop :=
  | asm_exec_step_internal:
      forall b ofs (f:function) i rs m rs' m' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      exec_instr ge f(*(fn_code f)*) i rs m = Next rs' m' ->
      asm_step (State rs lf) m (State rs' lf) m'
  | asm_exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs ESP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      ~ observableEF (*hf*) ef ->
      rs' = nextinstr_nf
             (set_res res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      asm_step (State rs lf) m (State rs' lf) m'
(*
  | asm_exec_step_builtin:
      forall b ofs f ef args res rs m t vres rs' m' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some (Pbuiltin ef args res) ->
      external_call' ef ge (map rs args) m t vl m' ->
      ~ observableEF hf ef ->
      rs' = nextinstr_nf 
             (set_regs res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      asm_step (State rs lf) m (State rs' lf) m'step (State rs m) t (State rs' m')*)
  | asm_exec_step_to_external:
      forall b ef args rs m lf,
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      asm_step (State rs lf) m (Asm_CallstateOut ef args rs lf) m
  | asm_exec_step_external:
      forall b callee args res rs m t rs' m' lf
      (OBS: EFisHelper (*hf*) callee),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External callee) ->
      external_call' callee ge args m t res m' ->
      rs' = (set_regs (loc_external_result (ef_sig callee)) res rs) #PC <- (rs RA) ->
      asm_step (Asm_CallstateOut callee args rs lf) m (State rs' lf) m'
  (*NOTE [loader]*)
  | asm_exec_initialize_call: 
      forall m args tys retty m1 stk m2 fb z,
      args_len_rec args tys = Some z -> 
      Mem.alloc m 0 (4*z) = (m1, stk) ->
      store_args m1 stk args tys = Some m2 -> 
      let rs0 := (Pregmap.init Vundef) 
                  #PC <- (Vptr fb Int.zero)
                  #RA <- Vzero 
                  # ESP <- (Vptr stk Int.zero) in
      asm_step (Asm_CallstateIn fb args tys retty) m 
               (State rs0 (mk_load_frame stk retty)) m2.

(*TODO 2.6
Lemma asm_step_det c m c' m' c'' m'' :
  asm_step c m c' m' ->   
  asm_step c m c'' m'' -> 
  c'=c'' /\ m'=m''.
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros H H0.
(* determ *)
  inv H; inv H0; Equalities.
  + split. constructor. auto.
  + discriminate.
  + discriminate.
  + eapply eval_builtin_args_determ in H10; try eassumption. subst vargs0.
    case_eq (is_I64_helper'_dec hf ef0); intros X _.
    assert (t=t0).
    { specialize EC'_i64_helper_determ. eapply EC'_i64_helper_determ in H4. ; eauto. } subst t0.
  inv H4; inv H10.
  eapply external_call_deterministic in H; eauto. destruct H; subst. split; auto.
  assert (t=t0).
  { eapply EC'_determ in H10; eauto. }
  inv H10; inv H4.
  eapply external_call_deterministic in H0; eauto. destruct H0; subst. auto. split; auto.
  eapply extcall_arguments_determ in H3; eauto. subst. auto.
  case_eq (is_I64_helper'_dec hf callee); intros X _.
  assert (t=t0).
  { eapply EC'_i64_helper_determ in H3; eauto. eapply EFhelpers; eauto. } subst t0.
  inv H3; inv H12.
  eapply external_call_deterministic in H; eauto. destruct H; subst. split; auto.
  assert (t=t0).
  { eapply EC'_determ in H12; eauto. } subst t0.
  inv H3; inv H12.
  eapply external_call_deterministic in H; eauto. destruct H; subst. auto. 
  rewrite H11 in H2; inversion H2. subst m2. inversion H2. rewrite H0 in H12.
  rewrite H12 in H3; inversion H3. subst m''. split; auto. 
  f_equal; auto.
  unfold rs0, rs1; rewrite H4; auto.
Qed.

Lemma asm_step_det c m c' m' c'' m'' :
  asm_step c m c' m' ->   
  asm_step c m c'' m'' -> 
  c'=c'' /\ m'=m''.
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros H H0.
(* determ *)
  inv H; inv H0; Equalities.
  split. constructor. auto.
  discriminate.
  discriminate.
  case_eq (is_I64_helper'_dec hf ef0); intros X _.
  assert (t=t0).
  { eapply eval_builtin_args_determ in H10; try eassumption. subst vargs0.
    eapply EC'_i64_helper_determ in H5. ; eauto. } subst t0.
  inv H4; inv H10.
  eapply external_call_deterministic in H; eauto. destruct H; subst. split; auto.
  assert (t=t0).
  { eapply EC'_determ in H10; eauto. }
  inv H10; inv H4.
  eapply external_call_deterministic in H0; eauto. destruct H0; subst. auto. split; auto.
  eapply extcall_arguments_determ in H3; eauto. subst. auto.
  case_eq (is_I64_helper'_dec hf callee); intros X _.
  assert (t=t0).
  { eapply EC'_i64_helper_determ in H3; eauto. eapply EFhelpers; eauto. } subst t0.
  inv H3; inv H12.
  eapply external_call_deterministic in H; eauto. destruct H; subst. split; auto.
  assert (t=t0).
  { eapply EC'_determ in H12; eauto. } subst t0.
  inv H3; inv H12.
  eapply external_call_deterministic in H; eauto. destruct H; subst. auto. 
  rewrite H11 in H2; inversion H2. subst m2. inversion H2. rewrite H0 in H12.
  rewrite H12 in H3; inversion H3. subst m''. split; auto. 
  f_equal; auto.
  unfold rs0, rs1; rewrite H4; auto.
Qed.
*)
End RELSEM.

Definition Asm_at_external (c: state):
          option (external_function * signature * list val) :=
  match c with
    Asm_CallstateOut ef args rs lf =>
      if observableEF_dec (*hf*) ef
      then Some(ef, ef_sig ef, decode_longs (sig_args (ef_sig ef)) args)
      else None
  | _ => None
  end.

Definition Asm_after_external (vret: option val)(c: state) : option state :=
  match c with 
    Asm_CallstateOut ef args rs lf => 
      match vret with
         None => Some (State ((set_regs (loc_external_result (ef_sig ef)) 
                               (encode_long (sig_res (ef_sig ef)) Vundef) rs) #PC <- (rs RA))
                      lf)
       | Some res => Some (State ((set_regs (loc_external_result (ef_sig ef)) 
                               (encode_long (sig_res (ef_sig ef)) res) rs) #PC <- (rs RA))
                          lf) 
      end
  | _ => None
  end.

Definition Asm_initial_core (ge:genv) (v: val) (args:list val): option state :=
  match v with
     | Vptr b i => 
          if Int.eq_dec i Int.zero 
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => 
                    match f with Internal fi =>
                     let tyl := sig_args (fn_sig fi) in
                     let res := sig_res (fn_sig fi) in
                     if val_has_type_list_func args tyl
                        && vals_defined args
                        && zlt (4*(2*(Zlength args))) Int.max_unsigned
                     then Some (Asm_CallstateIn b args tyl res)
                     else None
                   | External _ => None
                   end
               end
          else None
     | _ => None
    end.

Definition Asm_halted (q : state): option val :=
    match q with
      State rs (mk_load_frame b retty) => 
        if Val.cmp_bool Ceq (rs#PC) Vzero 
                  then match retty 
                       with Some Tlong =>
                          match decode_longs (Tlong::nil) ((rs#EDX)::(rs#EAX)::nil) with
                                | v :: nil => Some v
                                | _ => None
                          end
                       | Some Tfloat => Some(rs#ST0)
                       | Some Tsingle => Some(rs#ST0)
                       | Some _ => Some(rs#EAX)
                       | None => Some(rs#EAX)
                       end 
                  else None
    | _ => None
    end.

Section ASM_CORESEM.
Lemma Asm_at_external_halted_excl :
       forall q, Asm_at_external q = None \/ Asm_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma Asm_after_at_external_excl : forall retv q q',
      Asm_after_external retv q = Some q' -> Asm_at_external q' = None.
  Proof. intros.
    destruct q; simpl in *; try inv H.
    destruct retv; inv H1; simpl; trivial.
  Qed.

Lemma Asm_corestep_not_at_external:
       forall ge m q m' q', asm_step ge q m q' m' -> 
              Asm_at_external q = None.
  Proof. intros. inv H; try reflexivity. 
  simpl. destruct (observableEF_dec (*hf*) callee); simpl; trivial. 
  exfalso. eapply EFhelpers; eassumption. 
Qed.

Lemma Asm_corestep_not_halted : forall ge m q m' q', 
       asm_step ge q m q' m' -> 
       Asm_halted q = None.
  Proof. intros. inv H; simpl in *.
    rewrite H0; simpl. trivial. destruct lf; auto.
    rewrite H0; simpl. trivial. destruct lf; auto.
    rewrite H0; simpl. trivial. destruct lf; auto.
    trivial.
    auto.
  Qed.
 
Definition Asm_core_sem : CoreSemantics genv state mem.
Proof.
  eapply (@Build_CoreSemantics _ _ _ 
            Asm_initial_core
            Asm_at_external
            Asm_after_external
            Asm_halted
            asm_step).
    apply Asm_corestep_not_at_external.
    apply Asm_corestep_not_halted.
    apply Asm_at_external_halted_excl.
Defined.
End ASM_CORESEM.

Section ASM_MEMSEM.

Lemma exec_load_mem_step g ch m a rs rd rs' m': forall 
      (EI: exec_load g ch m a rs rd = Next rs' m'),
      mem_step m m'.
Proof. intros.
  unfold exec_load in EI.
  remember (Mem.loadv ch m (eval_addrmode g a rs) ).
  symmetry in Heqo; destruct o; inv EI. apply mem_step_refl.
Qed.

Lemma exec_store_mem_step g ch m a rs rs0 vals rs' m': forall
      (ES: exec_store g ch m a rs rs0 vals = Next rs' m'),
      mem_step m m'.
Proof. intros.
  unfold exec_store in ES.
  remember (Mem.storev ch m (eval_addrmode g a rs) (rs rs0)).
  symmetry in Heqo; destruct o; inv ES.
  remember (eval_addrmode g a rs). destruct v; inv Heqo.
  eapply mem_step_store; eassumption.
Qed.

Lemma goto_label_mem_step c0 l rs m rs' m': forall
      (G: goto_label c0 l rs m = Next rs' m'),
      mem_step m m'.
Proof. intros.
   unfold goto_label in G. 
   destruct (label_pos l 0 (fn_code c0)); inv G.
   destruct (rs PC); inv H0. 
   apply mem_step_refl.
Qed.

Lemma exec_instr_mem_step g c i rs m rs' m': forall 
      (EI: exec_instr g c i rs m = Next rs' m'),
      mem_step m m'.
Proof. intros.
   destruct i; simpl in *; inv EI; try apply mem_step_refl;
   try (eapply exec_load_mem_step; eassumption);
   try (eapply exec_store_mem_step; eassumption).

   destruct (Val.divu (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
   destruct (Val.modu (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
   apply mem_step_refl.

   destruct (Val.divs (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
   destruct (Val.mods (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
   apply mem_step_refl.

   destruct (eval_testcond c0 rs); inv H0.
   destruct b; inv H1; apply mem_step_refl.
   apply mem_step_refl.

   eapply goto_label_mem_step; eassumption. 

   destruct (eval_testcond c0 rs); inv H0.
   destruct b; inv H1.
   eapply goto_label_mem_step; eassumption. 
   apply mem_step_refl.

   destruct (eval_testcond c1 rs); inv H0.
   destruct b. 
     destruct (eval_testcond c2 rs); inv H1.
     destruct b; inv H0. 
     eapply goto_label_mem_step; eassumption.
   apply mem_step_refl.

     destruct (eval_testcond c2 rs); inv H1.
     apply mem_step_refl.
     destruct (rs r); inv H0.
     destruct (list_nth_z tbl (Int.unsigned i)); inv H1. 
     eapply goto_label_mem_step; eassumption.
  remember (Mem.alloc m 0 sz) as d; apply eq_sym in Heqd.
    destruct d; inv H0.
    remember (Mem.store Mint32 m0 b (Int.unsigned (Int.add Int.zero ofs_link))
         (rs ESP)) as q.
    apply eq_sym in Heqq; destruct q; inv H1.
    remember (Mem.store Mint32 m1 b (Int.unsigned (Int.add Int.zero ofs_ra))
         (rs RA)) as w.
    destruct w; apply eq_sym in Heqw; inv H0.
    eapply mem_step_trans.
      eapply mem_step_alloc; eassumption.
    eapply mem_step_trans.
      eapply mem_step_store; eassumption.
      eapply mem_step_store; eassumption.
  destruct (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))); inv H0.  
    destruct (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))); inv H1.  
    destruct (rs ESP); inv H0.
    remember (Mem.free m b 0 sz) as t.
    destruct t; inv H1; apply eq_sym in Heqt. 
    eapply mem_step_free; eassumption. 
Qed.

Lemma asm_mem_step : forall g c m c' m' (CS: asm_step g c m c' m'), mem_step m m'.
Proof. intros.
  inv CS; simpl in *; try apply mem_step_refl.
+ eapply exec_instr_mem_step; eassumption. 
+ (*inv H2.*) admit. (*eapply extcall_mem_step; eassumption.*)
+ inv H1. apply EFhelpers in OBS. admit. (* eapply extcall_mem_step; eassumption.*)
+ eapply mem_step_trans. 
  eapply mem_step_alloc; eassumption.
  eapply store_args_mem_step; try eassumption.
Admitted.

Program Definition Asm_mem_sem : @MemSem genv state.
Proof.
apply Build_MemSem with (csem := Asm_core_sem).
  apply asm_mem_step.
Defined.

Lemma exec_instr_forward g c i rs m rs' m': forall 
      (EI: exec_instr g c i rs m = Next rs' m'),
      mem_forward m m'.
Proof. intros.
    apply mem_forward_preserve.
    eapply exec_instr_mem_step; eassumption.
Qed.

End ASM_MEMSEM.

End ASM_MEM.



