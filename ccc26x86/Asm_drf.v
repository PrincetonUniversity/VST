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
Require Import sepcomp.drf_semantics.
Require Import ccc26x86.Asm_coop.
(*
Notation SP := ESP (only parsing).

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

Inductive load_frame: Type :=
| mk_load_frame:
    forall (sp: block)           (**r pointer to argument frame *)
           (retty: option typ),  (**r return type *)
    load_frame.
*)
Section ASM_drf.
Variable hf : I64Helpers.helper_functions.

Lemma exec_load_dstep ge ch m a rs rd rs' m': forall 
      (EI: exec_load ge ch m a rs rd = Next rs' m'),
      drf_step m m'.
Proof. intros.
  unfold exec_load in EI.
  remember (Mem.loadv ch m (eval_addrmode ge a rs) ).
  symmetry in Heqo; destruct o; inv EI. apply drf_step_refl. (*unless we do "Defined", it probably doesn't matter wether we sue drf_load - but maybe that's why the defintiino of drf_sem that's based on effsem rather than memsem is more useful?*)
Qed.

Lemma exec_store_dstep ge ch m a rs rs0 vals rs' m': forall
      (ES: exec_store ge ch m a rs rs0 vals = Next rs' m'),
      drf_step m m'.
Proof. intros.
  unfold exec_store in ES.
  remember (Mem.storev ch m (eval_addrmode ge a rs) (rs rs0)).
  symmetry in Heqo; destruct o; inv ES.
  remember (eval_addrmode ge a rs). destruct v; inv Heqo.
  eapply drf_step_store; eassumption.
Qed.

Lemma goto_label_dstep c0 l rs m rs' m': forall
      (G: goto_label c0 l rs m = Next rs' m'),
      drf_step m m'.
Proof. intros.
   unfold goto_label in G. 
   destruct (label_pos l 0 (fn_code c0)); inv G.
   destruct (rs PC); inv H0. 
   apply drf_step_refl.
Qed.

Lemma exec_instr_dstep ge c i rs m rs' m': forall 
      (EI: exec_instr ge c i rs m = Next rs' m'),
      drf_step m m'.
Proof. intros.
   destruct i; simpl in *; inv EI; try apply drf_step_refl;
   try (eapply exec_load_dstep; eassumption);
   try (eapply exec_store_dstep; eassumption).

   destruct (Val.divu (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
   destruct (Val.modu (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
   apply drf_step_refl.

   destruct (Val.divs (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
   destruct (Val.mods (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
   apply drf_step_refl.

   destruct (eval_testcond c0 rs); inv H0.
   destruct b; inv H1; apply drf_step_refl.
   apply drf_step_refl.

   eapply goto_label_dstep; eassumption. 

   destruct (eval_testcond c0 rs); inv H0.
   destruct b; inv H1.
   eapply goto_label_dstep; eassumption. 
   apply drf_step_refl.

   destruct (eval_testcond c1 rs); inv H0.
   destruct b. 
     destruct (eval_testcond c2 rs); inv H1.
     destruct b; inv H0. 
     eapply goto_label_dstep; eassumption.
   apply drf_step_refl.

     destruct (eval_testcond c2 rs); inv H1.
     apply drf_step_refl.
     destruct (rs r); inv H0.
     destruct (list_nth_z tbl (Int.unsigned i)); inv H1. 
     eapply goto_label_dstep; eassumption.
  remember (Mem.alloc m 0 sz) as d; apply eq_sym in Heqd.
    destruct d; inv H0.
    remember (Mem.store Mint32 m0 b (Int.unsigned (Int.add Int.zero ofs_link))
         (rs ESP)) as q.
    apply eq_sym in Heqq; destruct q; inv H1.
    remember (Mem.store Mint32 m1 b (Int.unsigned (Int.add Int.zero ofs_ra))
         (rs RA)) as w.
    destruct w; apply eq_sym in Heqw; inv H0.
    eapply drf_step_trans.
      eapply drf_step_alloc; eassumption.
    eapply drf_step_trans.
      eapply drf_step_store; eassumption.
      eapply drf_step_store; eassumption.
  destruct (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))); inv H0.  
    destruct (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))); inv H1.  
    destruct (rs ESP); inv H0.
    remember (Mem.free m b 0 sz) as t.
    destruct t; inv H1; apply eq_sym in Heqt. 
    eapply drf_step_free; eassumption. 
Qed.

Lemma store_stack_drf m sp ty ofs v m'
        (ST: store_stack m sp ty ofs v = Some m'): 
      drf_step m m'.
Proof. intros. 
 unfold store_stack in ST. destruct sp; simpl in ST; inv ST.
 eapply drf_step_store; eassumption.
Qed.

Lemma store_args_drf sp ofs args tys m m' :
  store_args_rec m sp ofs args tys = Some m' -> 
  drf_step m m'.
Proof.
revert args ofs m; induction tys.
+ destruct args.
  - intros ofs. inversion 1; subst. apply drf_step_refl.
  - intros ofs m. simpl. inversion 1.
+ destruct args; try solve[inversion 1]. 
  destruct a; simpl; intros ofs m. 
  - case_eq (store_stack m (Vptr sp Int.zero) Tint
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
    * intros. 
      eapply drf_step_trans. 
       apply (store_stack_drf _ _ _ _ _ _ H).
       eapply IHtys; eassumption.
    * intros; congruence.
  - case_eq (store_stack m (Vptr sp Int.zero) Tfloat
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
    * intros.
      eapply drf_step_trans. 
       apply (store_stack_drf _ _ _ _ _ _ H).
       eapply IHtys; eassumption.
    * intros; congruence. 
  - destruct v; try solve[congruence].
    case_eq (store_stack m (Vptr sp Int.zero) Tint
           (Int.repr match ofs+1 with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                      | Z.neg y' => Z.neg y'~0~0 end)
        (Vint (Int64.hiword i))).
    * intros.
       remember (store_stack m0 (Vptr sp Int.zero) Tint
        (Int.repr
           match ofs with
           | 0 => 0
           | Z.pos y' => Z.pos y'~0~0
           | Z.neg y' => Z.neg y'~0~0
           end) (Vint (Int64.loword i))).
       symmetry in Heqo; destruct o; inv H0.
      eapply drf_step_trans. 
       apply (store_stack_drf _ _ _ _ _ _ H).
      eapply drf_step_trans. 
       apply (store_stack_drf _ _ _ _ _ _ Heqo).
      eapply IHtys; eassumption.
    * intros; congruence.
  - intros.
    remember (store_stack m (Vptr sp Int.zero) Tsingle
        (Int.repr
           match ofs with
           | 0 => 0
           | Z.pos y' => Z.pos y'~0~0
           | Z.neg y' => Z.neg y'~0~0
           end) v).
       symmetry in Heqo; destruct o; inv H.
      eapply drf_step_trans. 
       apply (store_stack_drf _ _ _ _ _ _ Heqo).
       eapply IHtys; eassumption.
  - intros.
    remember (store_stack m (Vptr sp Int.zero) Tany32
        (Int.repr
           match ofs with
           | 0 => 0
           | Z.pos y' => Z.pos y'~0~0
           | Z.neg y' => Z.neg y'~0~0
           end) v).
       symmetry in Heqo; destruct o; inv H.
      eapply drf_step_trans. 
       apply (store_stack_drf _ _ _ _ _ _ Heqo).
       eapply IHtys; eassumption.
  - intros.
    remember (store_stack m (Vptr sp Int.zero) Tany64
        (Int.repr
           match ofs with
           | 0 => 0
           | Z.pos y' => Z.pos y'~0~0
           | Z.neg y' => Z.neg y'~0~0
           end) v).
       symmetry in Heqo; destruct o; inv H.
      eapply drf_step_trans. 
       apply (store_stack_drf _ _ _ _ _ _ Heqo).
       eapply IHtys; eassumption.
Qed.

Lemma store_args_drf_step m stk args tys m':
  store_args m stk args tys = Some m' -> drf_step m m'.
Proof. intros. unfold store_args in H.
  apply store_args_rec_only_stores in H.
  remember (encode_longs tys args). clear Heql.
  induction H. apply drf_step_refl.
  eapply drf_step_trans; try eassumption.
  eapply drf_step_store; eassumption.
Qed.


Lemma asm_dstep : forall ge c m c' m' (CS: asm_step hf ge c m c' m'), drf_step m m'.
Proof. intros.
  inv CS; simpl in *; try apply drf_step_refl.
+ eapply exec_instr_dstep; eassumption. 
+ admit. (*external callseapply extcall_drf_step; eassumption. *)
+ admit. (*another external call -inv H1. eapply extcall_dstep; try eassumption. apply EFhelpers in OBS; assumption.
  destruct callee; simpl in *; solve [intros NN; trivial].*)
+ eapply drf_step_trans. 
  eapply drf_step_alloc; eassumption.
  eapply store_args_drf_step; try eassumption.
Admitted.

Program Definition Asm_drf_sem : @DrfSem genv state.
Proof.
apply Build_DrfSem with (csem := Asm_core_sem hf).
  apply (asm_dstep).
Defined.

End ASM_drf.

Section ASM_DRF.
Variable hf : I64Helpers.helper_functions.
Require Import sepcomp.effect_semantics. Print StoreEffect. Check encode_val.
Definition drf_instr (ge:genv) (c: code) (i: instruction) (rs: regset) (m: mem) 
           : option drf_event  :=
  match i with
  | Pfstps_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => Some (Write b (Int.unsigned ofs) (encode_val Mfloat32 (rs ST0)))
                  | _ => None
                 end
  | Pfstpl_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => Some (Write b (Int.unsigned ofs) (encode_val Mfloat64 (rs ST0)))
                  | _ => None
                 end
  | Pmovss_mf a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some (Write b (Int.unsigned ofs) (encode_val Mfloat32 (rs r1)))
                  | _ => None
                 end
  | Pmov_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some (Write b (Int.unsigned ofs) (encode_val Mint32 (rs r1)))
                  | _ => None
                 end
  | Pmov_mr_a a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some (Write b (Int.unsigned ofs) (encode_val Many32 (rs r1)))
                  | _ => None
                 end
  | Pmovsd_mf a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some (Write b (Int.unsigned ofs) (encode_val Mfloat64 (rs r1)))
                  | _ => None
                 end
  | Pmovsd_mf_a a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some (Write b (Int.unsigned ofs)  (encode_val Many64 (rs r1)))
                  | _ => None
                 end
  | Pmovb_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some (Write b (Int.unsigned ofs) (encode_val Mint8unsigned (rs r1)))
                  | _ => None
                 end
  | Pmovw_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some (Write b (Int.unsigned ofs) (encode_val Mint16unsigned (rs r1)))
                  | _ => None
                 end
(*  | Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_ra)) with
      | None => EmptyEffect 
      | Some ra =>
          match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_link)) with
          | None => EmptyEffect 
          | Some sp =>
              match rs#ESP with
              | Vptr stk ofs =>
                  match Mem.free m stk 0 sz with
                  | None => EmptyEffect
                  | Some m' => (FreeEffect m 0 sz stk) 
                  end
              | _ => EmptyEffect
              end
          end
      end
  | Pbuiltin ef args res => EmptyEffect
(*     (BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) (map rs args)) m)*)
(*  | Pannot ef args =>
      EmptyEffect *)*)
(*  | Pmov_rr _ _ => Some Arith*)
  | _ => Some Arith
  end. 

Parameter ExtEvent : external_function-> list val -> drf_event.

Inductive asm_drf ge : drf_event -> 
                       state -> mem -> state -> mem -> Prop :=
  | asm_drf_step_internal:
      forall b ofs f i rs m rs' m' lf T,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      exec_instr ge f i rs m = Next rs' m' ->
      drf_instr ge (fn_code f) i rs m = Some T ->
      asm_drf ge T (State rs lf) m (State rs' lf) m'
  | asm_drf_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m' lf
        (HFD: helper_functions_declared ge hf)
         (NASS: ~ isInlinedAssembly ef)  (*NEW; we don't support inlined assembly yet*),
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs ESP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      ~ observableEF (*hf*) ef ->
      rs' = nextinstr_nf
             (set_res res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      asm_drf ge Arith (State rs lf) m (State rs' lf) m' 
  | asm_drf_step_to_external:
      forall b ef args rs m lf
      (HFD: helper_functions_declared ge hf),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      asm_drf ge Arith (State rs lf) m (Asm_CallstateOut ef args rs lf) m
  | asm_drf_step_external:
      forall b callee args res rs m t rs' m' lf
      (HFD: helper_functions_declared ge hf)
      (OBS: EFisHelper (*hf*) callee),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External callee) ->
      external_call' callee ge args m t res m' ->
      rs' = (set_regs (loc_external_result (ef_sig callee)) res rs) #PC <- (rs RA) ->
      asm_drf ge (ExtEvent callee args) (Asm_CallstateOut callee args rs lf) m (State rs' lf) m'
  (*NOTE [loader]*)
  | asm_drf_initialize_call: 
      forall m args tys retty m1 stk m2 fb z
      (HFD: helper_functions_declared ge hf),
      args_len_rec args tys = Some z -> 
      Mem.alloc m 0 (4*z) = (m1, stk) ->
      store_args m1 stk args tys = Some m2 -> 
      let rs0 := (Pregmap.init Vundef) 
                  #PC <- (Vptr fb Int.zero)
                  #RA <- Vzero 
                  # ESP <- (Vptr stk Int.zero) in
      asm_drf ge Arith (Asm_CallstateIn fb args tys retty) m 
               (State rs0 (mk_load_frame stk retty)) m2.

Lemma asm_DRF_store (g : genv) c m c' m' b ofs bytes (W: asm_drf g (Write b ofs bytes) c m c' m'):
Mem.storebytes m b ofs bytes = Some m' /\
(forall mm : Mem.mem',
 (exists n : Z,
    0 <= n < Zlength bytes /\ Mem.perm_order'' (Some Readable) ((Mem.mem_access mm) !! b (ofs + n) Cur)) ->
 Mem.storebytes mm b ofs bytes = None).
Proof. inv W.
+ destruct i; simpl in *; try discriminate.
  - unfold exec_store in H2.
    remember (eval_addrmode g a rs). destruct v; inv H3. simpl in H2.
    remember (Mem.store Mint32 m b (Int.unsigned i) (rs rs0)) as p. destruct p; inv H2.
    split; intros.
    * symmetry in Heqp. apply Mem.store_storebytes; trivial.
    * destruct H2 as [n [N M]].
      remember (Mem.storebytes mm b (Int.unsigned i) (encode_val Mint32 (rs rs0))) as q.
      destruct q; trivial. symmetry in Heqq.
      apply Mem.storebytes_range_perm in Heqq. specialize (Heqq (Int.unsigned i+n)).
      rewrite <- Zlength_correct in Heqq.
      unfold Mem.perm in Heqq. 
      remember ((Mem.mem_access mm) !! b (Int.unsigned i + n) Cur) as w.
      destruct w; simpl in Heqq. 
       assert (P: perm_order Readable Writable).
         eapply perm_order_trans. eassumption. apply Heqq. omega. inv P.
      elim Heqq. omega.
  - unfold exec_store in H2.
    remember (eval_addrmode g a rs). destruct v; inv H3. simpl in H2.
    remember (Mem.store  Mfloat64 m b (Int.unsigned i) (rs r1)) as p. destruct p; inv H2.
    split; intros.
    * symmetry in Heqp. apply Mem.store_storebytes; trivial.
    * destruct H2 as [n [N M]].
      remember (Mem.storebytes mm b (Int.unsigned i) (encode_val Mfloat64 (rs r1))) as q.
      destruct q; trivial. symmetry in Heqq.
      apply Mem.storebytes_range_perm in Heqq. specialize (Heqq (Int.unsigned i+n)).
      rewrite <- Zlength_correct in Heqq.
      unfold Mem.perm in Heqq. 
      remember ((Mem.mem_access mm) !! b (Int.unsigned i + n) Cur) as w.
      destruct w; simpl in Heqq. 
       assert (P: perm_order Readable Writable).
         eapply perm_order_trans. eassumption. apply Heqq. omega. inv P.
      elim Heqq. omega.
  - unfold exec_store in H2.
    remember (eval_addrmode g a rs). destruct v; inv H3. simpl in H2.
    remember (Mem.store Mfloat32 m b (Int.unsigned i) (rs r1) ) as p. destruct p; inv H2.
    split; intros.
    * symmetry in Heqp. apply Mem.store_storebytes; trivial.
    * destruct H2 as [n [N M]].
      remember (Mem.storebytes mm b (Int.unsigned i) (encode_val Mfloat32 (rs r1))) as q.
      destruct q; trivial. symmetry in Heqq.
      apply Mem.storebytes_range_perm in Heqq. specialize (Heqq (Int.unsigned i+n)).
      rewrite <- Zlength_correct in Heqq.
      unfold Mem.perm in Heqq. 
      remember ((Mem.mem_access mm) !! b (Int.unsigned i + n) Cur) as w.
      destruct w; simpl in Heqq. 
       assert (P: perm_order Readable Writable).
         eapply perm_order_trans. eassumption. apply Heqq. omega. inv P.
      elim Heqq. omega.
  - unfold exec_store in H2.
    remember (eval_addrmode g a rs). destruct v; inv H3. simpl in H2.
    remember (Mem.store Mfloat64 m b (Int.unsigned i) (rs ST0) ) as p. destruct p; inv H2.
    split; intros.
    * symmetry in Heqp. apply Mem.store_storebytes; trivial.
    * destruct H2 as [n [N M]].
      remember (Mem.storebytes mm b (Int.unsigned i) (encode_val Mfloat64 (rs ST0))) as q.
      destruct q; trivial. symmetry in Heqq.
      apply Mem.storebytes_range_perm in Heqq. specialize (Heqq (Int.unsigned i+n)).
      rewrite <- Zlength_correct in Heqq.
      unfold Mem.perm in Heqq. 
      remember ((Mem.mem_access mm) !! b (Int.unsigned i + n) Cur) as w.
      destruct w; simpl in Heqq. 
       assert (P: perm_order Readable Writable).
         eapply perm_order_trans. eassumption. apply Heqq. omega. inv P.
      elim Heqq. omega.
  - unfold exec_store in H2.
    remember (eval_addrmode g a rs). destruct v; inv H3. simpl in H2.
    remember (Mem.store Mfloat32 m b (Int.unsigned i) (rs ST0) ) as p. destruct p; inv H2.
    split; intros.
    * symmetry in Heqp. apply Mem.store_storebytes; trivial.
    * destruct H2 as [n [N M]].
      remember (Mem.storebytes mm b (Int.unsigned i) (encode_val Mfloat32 (rs ST0))) as q.
      destruct q; trivial. symmetry in Heqq.
      apply Mem.storebytes_range_perm in Heqq. specialize (Heqq (Int.unsigned i+n)).
      rewrite <- Zlength_correct in Heqq.
      unfold Mem.perm in Heqq. 
      remember ((Mem.mem_access mm) !! b (Int.unsigned i + n) Cur) as w.
      destruct w; simpl in Heqq. 
       assert (P: perm_order Readable Writable).
         eapply perm_order_trans. eassumption. apply Heqq. omega. inv P.
      elim Heqq. omega.
  - unfold exec_store in H2.
    remember (eval_addrmode g a rs). destruct v; inv H3. simpl in H2.
    remember (Mem.store Mint8unsigned  m b (Int.unsigned i) (rs rs0) ) as p. destruct p; inv H2.
    split; intros.
    * symmetry in Heqp. apply Mem.store_storebytes; trivial.
    * destruct H2 as [n [N M]].
      remember (Mem.storebytes mm b (Int.unsigned i) (encode_val Mint8unsigned (rs rs0))) as q.
      destruct q; trivial. symmetry in Heqq.
      apply Mem.storebytes_range_perm in Heqq. specialize (Heqq (Int.unsigned i+n)).
      rewrite <- Zlength_correct in Heqq.
      unfold Mem.perm in Heqq. 
      remember ((Mem.mem_access mm) !! b (Int.unsigned i + n) Cur) as w.
      destruct w; simpl in Heqq. 
       assert (P: perm_order Readable Writable).
         eapply perm_order_trans. eassumption. apply Heqq. omega. inv P.
      elim Heqq. omega.
  - unfold exec_store in H2.
    remember (eval_addrmode g a rs). destruct v; inv H3. simpl in H2.
    remember (Mem.store Mint16unsigned m b (Int.unsigned i) (rs rs0) ) as p. destruct p; inv H2.
    split; intros.
    * symmetry in Heqp. apply Mem.store_storebytes; trivial.
    * destruct H2 as [n [N M]].
      remember (Mem.storebytes mm b (Int.unsigned i) (encode_val Mint16unsigned (rs rs0))) as q.
      destruct q; trivial. symmetry in Heqq.
      apply Mem.storebytes_range_perm in Heqq. specialize (Heqq (Int.unsigned i+n)).
      rewrite <- Zlength_correct in Heqq.
      unfold Mem.perm in Heqq. 
      remember ((Mem.mem_access mm) !! b (Int.unsigned i + n) Cur) as w.
      destruct w; simpl in Heqq. 
       assert (P: perm_order Readable Writable).
         eapply perm_order_trans. eassumption. apply Heqq. omega. inv P.
      elim Heqq. omega.
  - unfold exec_store in H2.
    remember (eval_addrmode g a rs). destruct v; inv H3. simpl in H2.
    remember (Mem.store Many32 m b (Int.unsigned i) (rs rs0) ) as p. destruct p; inv H2.
    split; intros.
    * symmetry in Heqp. apply Mem.store_storebytes; trivial.
    * destruct H2 as [n [N M]].
      remember (Mem.storebytes mm b (Int.unsigned i) (encode_val Many32 (rs rs0))) as q.
      destruct q; trivial. symmetry in Heqq.
      apply Mem.storebytes_range_perm in Heqq. specialize (Heqq (Int.unsigned i+n)).
      rewrite <- Zlength_correct in Heqq.
      unfold Mem.perm in Heqq. 
      remember ((Mem.mem_access mm) !! b (Int.unsigned i + n) Cur) as w.
      destruct w; simpl in Heqq. 
       assert (P: perm_order Readable Writable).
         eapply perm_order_trans. eassumption. apply Heqq. omega. inv P.
      elim Heqq. omega.
  - unfold exec_store in H2.
    remember (eval_addrmode g a rs). destruct v; inv H3. simpl in H2.
    remember (Mem.store Many64 m b (Int.unsigned i) (rs r1) ) as p. destruct p; inv H2.
    split; intros.
    * symmetry in Heqp. apply Mem.store_storebytes; trivial.
    * destruct H2 as [n [N M]].
      remember (Mem.storebytes mm b (Int.unsigned i) (encode_val Many64 (rs r1))) as q.
      destruct q; trivial. symmetry in Heqq.
      apply Mem.storebytes_range_perm in Heqq. specialize (Heqq (Int.unsigned i+n)).
      rewrite <- Zlength_correct in Heqq.
      unfold Mem.perm in Heqq. 
      remember ((Mem.mem_access mm) !! b (Int.unsigned i + n) Cur) as w.
      destruct w; simpl in Heqq. 
       assert (P: perm_order Readable Writable).
         eapply perm_order_trans. eassumption. apply Heqq. omega. inv P.
      elim Heqq. omega.
+ admit. (*external call stuff*)
Admitted.

Lemma corestep2drf g: forall c m c' m' (CS:corestep (Asm_mem_sem hf) g c m c' m'),
   exists T : drf_event, asm_drf g T c m c' m'.
Proof. induction 1.
+ destruct i; inv H2;
  try solve [eexists; eapply asm_drf_step_internal; try eassumption; reflexivity].
  - unfold exec_store in H4.
    remember (Mem.storev Mint32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; inv H4.
    remember (eval_addrmode g a rs) as q.
    destruct q; inv Heqp.
    eexists; eapply asm_drf_step_internal; try eassumption. simpl. unfold exec_store.
    rewrite <- Heqq. simpl. rewrite <- H3. reflexivity. simpl. rewrite <- Heqq. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; inv H4.
    remember (eval_addrmode g a rs) as q.
    destruct q; inv Heqp.
    eexists; eapply asm_drf_step_internal; try eassumption. simpl. unfold exec_store.
    rewrite <- Heqq. simpl. rewrite <- H3. reflexivity. simpl. rewrite <- Heqq. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; inv H4.
    remember (eval_addrmode g a rs) as q.
    destruct q; inv Heqp.
    eexists; eapply asm_drf_step_internal; try eassumption. simpl. unfold exec_store.
    rewrite <- Heqq. simpl. rewrite <- H3. reflexivity. simpl. rewrite <- Heqq. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; inv H4.
    remember (eval_addrmode g a rs) as q.
    destruct q; inv Heqp.
    eexists; eapply asm_drf_step_internal; try eassumption. simpl. unfold exec_store.
    rewrite <- Heqq. simpl. rewrite <- H3. reflexivity. simpl. rewrite <- Heqq. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; inv H4.
    remember (eval_addrmode g a rs) as q.
    destruct q; inv Heqp.
    eexists; eapply asm_drf_step_internal; try eassumption. simpl. unfold exec_store.
    rewrite <- Heqq. simpl. rewrite <- H3. reflexivity. simpl. rewrite <- Heqq. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mint8unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; inv H4.
    remember (eval_addrmode g a rs) as q.
    destruct q; inv Heqp.
    eexists; eapply asm_drf_step_internal; try eassumption. simpl. unfold exec_store.
    rewrite <- Heqq. simpl. rewrite <- H3. reflexivity. simpl. rewrite <- Heqq. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mint16unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; inv H4.
    remember (eval_addrmode g a rs) as q.
    destruct q; inv Heqp.
    eexists; eapply asm_drf_step_internal; try eassumption. simpl. unfold exec_store.
    rewrite <- Heqq. simpl. rewrite <- H3. reflexivity. simpl. rewrite <- Heqq. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Many32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; inv H4.
    remember (eval_addrmode g a rs) as q.
    destruct q; inv Heqp.
    eexists; eapply asm_drf_step_internal; try eassumption. simpl. unfold exec_store.
    rewrite <- Heqq. simpl. rewrite <- H3. reflexivity. simpl. rewrite <- Heqq. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Many64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; inv H4.
    remember (eval_addrmode g a rs) as q.
    destruct q; inv Heqp.
    eexists; eapply asm_drf_step_internal; try eassumption. simpl. unfold exec_store.
    rewrite <- Heqq. simpl. rewrite <- H3. reflexivity. simpl. rewrite <- Heqq. reflexivity.
+ admit. (*builtin*) 
+ eexists. econstructor; eassumption. 
+ admit. (*extcall*)
+ eexists. econstructor; try eassumption. (*case needs more more*)
Admitted.

Program Definition Asm_DRFSem : @DRFSem genv state.
Proof.
eapply Build_DRFSem with (msem := Asm_mem_sem hf) (drfstep:=asm_drf).
+ intros. inv H.
  - eapply asm_exec_step_internal; try eassumption. admit. (*helper_functions declared*)
  - eapply asm_exec_step_builtin; try eassumption. trivial.
  - eapply asm_exec_step_to_external; try eassumption.
  - eapply asm_exec_step_external; try eassumption. trivial.
  - eapply asm_exec_initialize_call; try eassumption. 
+ apply corestep2drf. 
+ intros. inv H; inv H0.
  - rewrite H1 in H7; inv H7. rewrite  H2 in H8; inv H8.
    rewrite H3 in H9; inv H9. rewrite H15 in H5; inv H5. trivial.
  - rewrite H1 in H7; inv H7. rewrite  H2 in H8; inv H8.
    rewrite H3 in H9; inv H9. simpl in H5. inv H5; trivial. 
  - rewrite H1 in H7; inv H7. rewrite  H2 in H9; inv H9. 
  - rewrite H1 in H8; inv H8. rewrite  H2 in H9; inv H9. 
    rewrite H3 in H10; inv H10. discriminate. 
  - rewrite H1 in H8; inv H8. rewrite  H2 in H9; inv H9. 
    rewrite H3 in H10; inv H10. exploit eval_builtin_args_determ. apply H11. apply H4. intros; subst. trivial. 
  - trivial.
  - rewrite H1 in H5; inv H5. rewrite  H2 in H6; inv H6.
  - trivial.
  - trivial.
  - trivial.
  - trivial. 
+ apply asm_DRF_store.
+ intros. inv H. 
  - destruct i; simpl in *; try discriminate; remember (eval_addrmode g a rs); destruct v; inv H4.
  - admit. (*external/builtin*) 
+ intros. inv H. 
  - destruct i; simpl in *; try discriminate;
    remember (eval_addrmode g a rs); destruct v; inv H4.
  - admit. (*external/builtin*) 
+ intros. inv H. 
  - admit. (*TODOdestruct i; simpl in *; try inv H4; try inv H3.
    split; trivial. intros. econstructor.
    remember (eval_addrmode g a rs); destruct v; inv H4.*)
  - admit. (*TODO*)
  - admit. (*TODO*)
  - admit. (*TODO*)
  - admit. (*TODO*)
Admitted.


