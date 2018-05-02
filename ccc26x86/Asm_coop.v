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
Require Import compcert.backend.Locations.
(*Require Import Stacklayout.*)
Require Import compcert.backend.Conventions.

Require Import compcert.x86.Asm.
(*LENB: In CompComp, we used a modified Asm.v, called Asm.comp.v*)

Require Import VST.sepcomp.mem_lemmas.
Require Import VST.concurrency.core_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.val_casted.
Require Import VST.ccc26x86.BuiltinEffects.
(*Require Import VST.ccc26x86.load_frame.*)

(*Notation SP := ESP (only parsing).

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

Inductive load_frame: Type :=
| mk_load_frame:
    forall (sp: block)           (**r pointer to argument frame *)
           (retty: option typ),  (**r return type *)
    load_frame.*)

Section ASM_MEM.
(*Variable hf : I64Helpers.helper_functions.*)

(*Section RELSEM.
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
      forall b ofs (f:function) i rs m rs' m' lf
      (*(HFD: helper_functions_declared ge hf)*),
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      exec_instr ge f(*(fn_code f)*) i rs m = Next rs' m' ->
      asm_step (State rs lf) m (State rs' lf) m'
  | asm_exec_step_builtin:
      False -> (*We don't support builtins/helpers/vload/vstore etc yet*)
      forall b ofs f ef args res rs m vargs t vres rs' m' lf
        (*(HFD: helper_functions_declared ge hf)*)
         (NASS: ~ isInlinedAssembly ef)  (*NEW; we don't support inlined assembly yet*),
      False -> (*We don't support builtins/helpers/vload/vstore etc yet*)
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
  | asm_exec_step_to_external:
      forall b ef args rs m lf
      (*(HFD: helper_functions_declared ge hf)*),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      asm_step (State rs lf) m (Asm_CallstateOut ef args rs lf) m
  | asm_exec_step_external:
      False -> (*We don't support builtins/helpers/vload/vstore etc yet*)
      forall b callee args res rs m t rs' m' lf
      (*(HFD: helper_functions_declared ge hf)*)
      (OBS: EFisHelper (*hf*) callee),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External callee) ->
      extcall_arguments rs m (ef_sig callee) args ->
      external_call callee ge args m t res m' ->
      rs' = (set_pair (loc_external_result (ef_sig callee)) res rs) #PC <- (rs RA) ->
      asm_step (Asm_CallstateOut callee args rs lf) m (State rs' lf) m'
  (*NOTE [loader]*)
  | asm_exec_initialize_call:
      forall m args tys retty m1 stk m2 fb z
      (*(HFD: helper_functions_declared ge hf)*),
      args_len_rec args tys = Some z ->
      Mem.alloc m 0 (4*z) = (m1, stk) ->
      store_args m1 stk args tys = Some m2 ->
      let rs0 := (Pregmap.init Vundef)
                  #PC <- (Vptr fb Int.zero)
                  #RA <- Vzero
                  # ESP <- (Vptr stk Int.zero) in
      asm_step (Asm_CallstateIn fb args tys retty) m
               (State rs0 (mk_load_frame stk retty)) m2.

Lemma EFisHelper_dec ef : {EFisHelper ef} + {~EFisHelper ef}.
destruct ef; simpl; try solve [right; intros N; assumption].
  apply I64Helpers.is_I64_helperS_dec.
  apply is_I64_builtinS_dec.
Qed.

Lemma extcall_arg_det rs m a b1 b2 (EA1: extcall_arg rs m a b1) (EA2: extcall_arg rs m a b2):b1=b2.
inv EA1; inv EA2; trivial.
remember (Val.add (rs ESP) (Vint (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs)))). clear Heqv.
destruct v; inv H0; inv H4. rewrite H0 in H1. inv H1; trivial.
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
  inv H; inv H0; Equalities; try contradiction.
  + split. constructor. auto.
  (*+ discriminate.*)
  (*+ discriminate.*)
  (*+ eapply eval_builtin_args_determ in H11; try eassumption. subst vargs0. red in H4.
    destruct (EFisHelper_dec ef0).
    - exploit (EC_determ ge). apply H5. apply H12. trivial. intros [? [? ?]]; subst. split; trivial.
    - destruct ef0; simpl in *; try solve [elim H13; trivial].
      * (*malloc*) exploit ec_determ. apply extcall_malloc_ok. apply H5. apply H12.
        intros [? ?]. inv H5. inv H12. destruct H0; trivial. subst. inv H0. split; trivial.
      * (*free*) exploit ec_determ. apply extcall_free_ok. apply H5. apply H12.
        intros [? ?]. inv H5. inv H12. destruct H0; trivial. subst. split; trivial.
      * (*memcpy*) exploit ec_determ. apply extcall_memcpy_ok. apply H5. apply H12.
        intros [? ?]. inv H5. inv H12. destruct H0; trivial. subst. split; trivial.*)
  + specialize (extcall_arguments_determ _ _ _ _ _ H3 H10); intros; subst. split; trivial.
  (*+ exploit (EC'_determ ge). apply H3. apply H12. trivial. intros [? [? ?]]; subst. split; trivial.*)
  + split; trivial.
Qed.

End RELSEM.

Definition Asm_at_external (c: state):
          option (external_function * list val) :=
  match c with
    Asm_CallstateOut ef args rs lf =>
      if observableEF_dec (*hf*) ef
      then Some(ef, decode_longs (sig_args (ef_sig ef)) args)
      else None
  | _ => None
  end.
(*In compcomp, had encode_long
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
*)
Definition Asm_after_external (vret: option val)(c: state) : option state :=
  match c with
    Asm_CallstateOut ef args rs lf =>
      match vret with
         None => Some (State ((set_pair (loc_external_result (ef_sig ef))
                               Vundef rs) #PC <- (rs RA))
                      lf)
       | Some res => Some (State ((set_pair (loc_external_result (ef_sig ef))
                               res rs) #PC <- (rs RA))
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
    end.*)

Section ASM_CORESEM.

(* Ask Santiago whether we can replace the program argument to semantics with a genv. *)
Program Definition Asm_core_sem prog : CoreSemantics _ _ _ := sem2coresem (semantics prog) _.
Next Obligation.
  inv H; simpl in *.
  intro H; inv H.
  unfold Vnullptr in *.
  inv H0; destruct Archi.ptr64; congruence.
Defined.

End ASM_CORESEM.

Section ASM_MEMSEM.

Lemma exec_load_mem_step ge ch m a rs rd rs' m': forall
      (EI: exec_load ge ch m a rs rd = Next rs' m'),
      mem_step m m'.
Proof. intros.
  unfold exec_load in EI.
  remember (Mem.loadv ch m (eval_addrmode ge a rs) ).
  symmetry in Heqo; destruct o; inv EI. apply mem_step_refl.
Qed.

Lemma exec_store_mem_step ge ch m a rs rs0 vals rs' m': forall
      (ES: exec_store ge ch m a rs rs0 vals = Next rs' m'),
      mem_step m m'.
Proof. intros.
  unfold exec_store in ES.
  remember (Mem.storev ch m (eval_addrmode ge a rs) (rs rs0)).
  symmetry in Heqo; destruct o; inv ES.
  remember (eval_addrmode ge a rs). destruct v; inv Heqo.
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

Lemma exec_instr_mem_step ge c i rs m rs' m': forall
      (EI: exec_instr ge c i rs m = Next rs' m'),
      mem_step m m'.
Proof. intros.
   destruct i; inv EI; try apply mem_step_refl;
   try (eapply exec_load_mem_step; eassumption);
   try (eapply exec_store_mem_step; eassumption).

   destruct (rs RDX); try discriminate.
   destruct (rs RAX); try discriminate.
   destruct (rs r1); try discriminate.
   destruct (Int.divmodu2 _ _ _) as [[]|]; inv H0.
   apply mem_step_refl.

   destruct (rs RDX); try discriminate.
   destruct (rs RAX); try discriminate.
   destruct (rs r1); try discriminate.
   destruct (Int64.divmodu2 _ _ _) as [[]|]; inv H0.
   apply mem_step_refl.

   destruct (rs RDX); try discriminate.
   destruct (rs RAX); try discriminate.
   destruct (rs r1); try discriminate.
   destruct (Int.divmods2 _ _ _) as [[]|]; inv H0.
   apply mem_step_refl.

   destruct (rs RDX); try discriminate.
   destruct (rs RAX); try discriminate.
   destruct (rs r1); try discriminate.
   destruct (Int64.divmods2 _ _ _) as [[]|]; inv H0.
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
    remember (Mem.store Mptr m0 b (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero ofs_link))
         (rs RSP)) as q.
    apply eq_sym in Heqq; destruct q; inv H1.
    remember (Mem.store Mptr m1 b (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero ofs_ra))
         (rs RA)) as w.
    destruct w; apply eq_sym in Heqw; inv H0.
    eapply mem_step_trans.
      eapply mem_step_alloc; eassumption.
    eapply mem_step_trans.
      eapply mem_step_store; eassumption.
      eapply mem_step_store; eassumption.
  destruct (Mem.loadv Mptr m (Val.offset_ptr (rs RSP) ofs_ra)); inv H0.
    destruct (Mem.loadv Mptr m (Val.offset_ptr (rs RSP) ofs_link)); inv H1.
    destruct (rs RSP); inv H0.
    remember (Mem.free m b 0 sz) as t.
    destruct t; inv H1; apply eq_sym in Heqt.
    eapply mem_step_free; eassumption.
Qed.

Lemma asm_mem_step : forall prog c m t c' m' (CS: step (Genv.globalenv prog) (State c m) t (State c' m'))
  (Hext : Asm.at_external prog (State c m) = None), mem_step m m'.
Proof. intros.
  inv CS; simpl in *.
+ eapply exec_instr_mem_step; eassumption.
(*+ eapply extcall_mem_step; eassumption. *)
(*+ inv H1. eapply extcall_mem_step; try eassumption. apply EFhelpers in OBS; assumption.
  destruct callee; simpl in *; solve [intros NN; trivial].*)
+ admit. (* builtin *)
+ rewrite H3 in Hext.
  destruct (Ptrofs.eq_dec _ _); [|contradiction].
  rewrite H4 in Hext.
(*eapply mem_step_trans.
  eapply mem_step_alloc; eassumption.
  eapply store_args_mem_step; try eassumption.
Qed.*)
Admitted.

(*Lemma ple_exec_load:
    forall g ch m a rs rd rs' m'
       m1 (PLE: perm_lesseq m m1),
       exec_load g ch m a rs rd = Next rs' m' ->
       m'=m /\ exec_load g ch m1 a rs rd = Next rs' m1.
Proof.
  intros.
  unfold exec_load in *.
  destruct (Mem.loadv ch m (eval_addrmode g a rs)) eqn:?; inv H.
  split; auto.
  eapply ple_load in Heqo; eauto. rewrite Heqo. auto.
Qed.


Lemma ple_exec_store:
  forall g ch m a rs rs0 rsx rs' m' m1
   (PLE: perm_lesseq m m1),
   exec_store g ch m a rs rs0 rsx = Next rs' m' ->
  exists m1',
    perm_lesseq m' m1' /\ exec_store g ch m1 a rs rs0 rsx = Next rs' m1'.
Proof.
intros.
 unfold exec_store in *.
 destruct (Mem.storev ch m (eval_addrmode g a rs) (rs rs0)) eqn:?; inv H.
 destruct (ple_store _ _ _ _ _ _ PLE Heqo) as [m1' [? ?]].
 exists m1'; split; auto.
 rewrite H0. auto.
Qed.

Lemma asm_inc_perm: forall (g : genv) c m c' m' (CS:corestep Asm_core_sem g c m c' m')
      m1 (PLE: perm_lesseq m m1),
      exists m1', corestep Asm_core_sem g c m1 c' m1' /\ perm_lesseq m' m1'.
Proof.
intros; inv CS; simpl in *; try contradiction.
+ destruct i; simpl in *; inv H2;
     try solve [
      exists m1; split; trivial; econstructor; try eassumption; reflexivity
     | destruct (ple_exec_load _ _ _ _ _ _ _ _ _ PLE H4); subst m';
        exists m1; split; simpl; auto; econstructor; eassumption
     | destruct (ple_exec_store _ _ _ _ _ _ _ _ _ _ PLE H4) as [m1' [? ?]];
        exists m1'; split; auto; econstructor; eassumption
    |  exists m1; split; [ econstructor; try eassumption; simpl | ];
       repeat match type of H4 with match ?A with Some _ => _ | None => _ end = _ =>
         destruct A; try now inv H4 end;
       eassumption
    ].
 - (* Pcmp_rr case fails! *)
(*+ exists m1; split; trivial. econstructor; try eassumption. admit.
+ admit.
*)
Abort.*)

Program Definition Asm_mem_sem prog : @MemSem genv state := {| csem := Asm_core_sem prog |}.
Next Obligation.
Proof.
  inv CS; simpl in *.
  destruct c, c'; simpl in H.
  eapply asm_mem_step; eauto.
(*Defined.*)
Admitted. (* need to connect prog and genv *)

Lemma exec_instr_forward g c i rs m rs' m': forall
      (EI: exec_instr g c i rs m = Next rs' m'),
      mem_forward m m'.
Proof. intros.
    apply mem_forward_preserve.
    eapply exec_instr_mem_step; eassumption.
Qed.

End ASM_MEMSEM.

End ASM_MEM.

(*Lemma load_frame_store_args_rec_nextblock:
  forall args m m2 stk ofs tys
    (Hload_frame: load_frame.store_args_rec m stk ofs args tys = Some m2),
    Mem.nextblock m2 = Mem.nextblock m.
Proof.
  intro args.
  induction args; intros; simpl in *.
  destruct tys; inv Hload_frame; auto.
  destruct tys; try discriminate;
  destruct t;
  repeat match goal with
         | [H: match ?Expr with _ => _ end = _ |- _] =>
           destruct Expr eqn:?; try discriminate;
             unfold load_frame.store_stack in *
         | [H: Mem.storev _ _ _ _ = _ |- _] =>
           eapply nextblock_storev in H
         | [H: ?Expr = ?Expr2 |- context[?Expr2]] =>
           rewrite <- H
         end;
  eauto.
Qed.

Lemma load_frame_store_nextblock:
  forall m m2 stk args tys
    (Hload_frame: load_frame.store_args m stk args tys = Some m2),
    Mem.nextblock m2 = Mem.nextblock m.
Proof.
  intros.
  unfold load_frame.store_args in *.
  eapply load_frame_store_args_rec_nextblock; eauto.
Qed.*)
