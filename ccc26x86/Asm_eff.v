Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.lib.Integers.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Export compcert.lib.Maps.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.
Require Import ccc26x86.Locations.
Require Import ccc26x86.Stacklayout.
Require Import ccc26x86.Conventions.

(*LENB: again, in Compcomp we imported the modified Asm_comp*)
Require Import ccc26x86.Asm. 
Require Import ccc26x86.Asm_coop. 

Require Import sepcomp.mem_lemmas. (*for mem_forward*)
Require Import sepcomp.semantics.
Require Import sepcomp.effect_semantics.
Require Import ccc26x86.BuiltinEffects.
Require Import ccc26x86.load_frame.

Notation SP := ESP (only parsing).

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

Section ASM_EFF.
Variable hf : I64Helpers.helper_functions.

(*A computational variant of eval_builtin_arg*)
Section CEVAL_BUILTIN_ARG_COMPUTE.

Variable A: Type.
Variable ge: Senv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Fixpoint ceval_builtin_arg (a:builtin_arg A): option val :=
  match a with
    BA x => Some (e x)
  | BA_int n => Some (Vint n)
  | BA_long n => Some (Vlong n)
  | BA_float n => Some (Vfloat n)
  | BA_single n => Some (Vsingle n)
  | BA_loadstack chunk ofs =>
      Mem.loadv chunk m (Val.add sp (Vint ofs))
  | BA_addrstack ofs => Some (Val.add sp (Vint ofs))
  | BA_loadglobal chunk id ofs =>
      Mem.loadv chunk m (Senv.symbol_address ge id ofs) 
  | BA_addrglobal id ofs => Some (Senv.symbol_address ge id ofs)
  | BA_splitlong hi lo => 
     match ceval_builtin_arg hi, ceval_builtin_arg lo
     with Some vhi, Some vlo => Some (Val.longofwords vhi vlo)
          | _, _ => None
     end
  end.

Lemma ceval_builtin_arg_char1: forall a v, 
  ceval_builtin_arg a = Some v -> eval_builtin_arg ge e sp m a v.
Proof.
  induction a; simpl; intros; inv H; try constructor; trivial.
  destruct (ceval_builtin_arg a1); inv H1.
  destruct (ceval_builtin_arg a2); inv H0.
  econstructor; eauto.
Qed.

Lemma ceval_builtin_arg_char2: forall a v, 
  eval_builtin_arg ge e sp m a v -> ceval_builtin_arg a = Some v.
Proof.
  induction a; simpl; intros; inv H; trivial.
  rewrite (IHa1 _ H2). rewrite (IHa2 _ H4); trivial.
Qed.

Definition ceval_builtin_args (args:list (builtin_arg A)): option (list val) :=
fold_right (fun a vals => match ceval_builtin_arg a, vals with 
                 Some v, Some vs => Some (v::vs)
               | _, _ => None end) 
          (Some nil) args.

Lemma ceval_builtin_args_char: forall args vals, 
  ceval_builtin_args args = Some vals <-> eval_builtin_args ge e sp m args vals.
Proof. 
induction args; simpl; intros.
  split; intros; inv H. constructor. trivial.
split; intros.
+ remember (ceval_builtin_arg a) as p; symmetry in Heqp.
  destruct p; inv H.
  remember (ceval_builtin_args args) as q; symmetry in Heqq.
  destruct q; inv H1. constructor. 
  eapply ceval_builtin_arg_char1. eassumption.
  apply IHargs. trivial.
+ inv H; simpl in *. apply ceval_builtin_arg_char2 in H2. 
  apply IHargs in H4. rewrite H2, H4. trivial.
Qed.
End CEVAL_BUILTIN_ARG_COMPUTE.

Section EFFSEM.

Definition effect_instr (ge:genv) (c: code) (i: instruction) 
                 (rs: regset) (m: mem)
           : (block -> Z -> bool)  := EmptyEffect.
(*
Definition effect_instr (ge:genv) (e: preg -> val) (sp:val) (*(c: code)*) (i: instruction) 
                 (*(rs: regset)*) (m: mem) 
           : (block -> Z -> bool)  := (*EmptyEffect.*)
  match i with
  Pbuiltin ef args res =>
     match ceval_builtin_args preg (Genv.to_senv ge) e sp m args with 
       None => EmptyEffect
     | Some vals => (BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) vals) m)
     end
 (*    (BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) (map rs args)) m)*)
  | _ => EmptyEffect
  end. (*
(decode_longs (sig_args (ef_sig callee)) args)

  (** Moves *)
  | Pmov_rr rd r1 => EmptyEffect
  | Pmov_ri rd n => EmptyEffect
  | Pmov_ra rd id => EmptyEffect
  | Pmov_rm rd a => EmptyEffect
  | Pmov_mr a r1 => (StoreEffect (eval_addrmode ge a rs) (encode_val Mint32 (rs r1)))
  | Pmovsd_ff rd r1 => EmptyEffect
  | Pmovsd_fi rd n => EmptyEffect
  | Pmovsd_fm rd a => EmptyEffect
(*in Compcomp:  | Pmovsd_mf a r1 => (StoreEffect (eval_addrmode ge a rs) (encode_val Mfloat64al32 (rs r1)))*)
  | Pmovsd_mf a r1 => (StoreEffect (eval_addrmode ge a rs) (encode_val Mfloat64 (rs r1)))
  | Pfld_f r1 => EmptyEffect
  | Pfld_m a => EmptyEffect
  | Pfstp_f rd => EmptyEffect
  | Pfstp_m a => StoreEffect (eval_addrmode ge a rs) (encode_val Mfloat64al32 (rs ST0))
  | Pxchg_rr r1 r2 => EmptyEffect

  (** Moves with conversion *)
  | Pmovb_mr a r1 => StoreEffect (eval_addrmode ge a rs) (encode_val Mint8unsigned (rs r1))
  | Pmovw_mr a r1 => StoreEffect (eval_addrmode ge a rs) (encode_val Mint16unsigned (rs r1))
  | Pmovzb_rr rd r1 => EmptyEffect
  | Pmovzb_rm rd a => EmptyEffect
  | Pmovsb_rr rd r1 => EmptyEffect
  | Pmovsb_rm rd a => EmptyEffect
  | Pmovzw_rr rd r1 => EmptyEffect
  | Pmovzw_rm rd a => EmptyEffect
  | Pmovsw_rr rd r1 => EmptyEffect
  | Pmovsw_rm rd a => EmptyEffect
  | Pcvtss2sd_fm rd a => EmptyEffect
  | Pcvtsd2ss_ff rd r1 => EmptyEffect
  | Pcvtsd2ss_mf a r1 => StoreEffect (eval_addrmode ge a rs) (encode_val Mfloat32 (rs r1))
  | Pcvttsd2si_rf rd r1 => EmptyEffect
  | Pcvtsi2sd_fr rd r1 => EmptyEffect

  (** Integer arithmetic *)
  | Plea rd a => EmptyEffect
  | Pneg rd => EmptyEffect
  | Psub_rr rd r1 => EmptyEffect
  | Pimul_rr rd r1 => EmptyEffect
  | Pimul_ri rd n => EmptyEffect
  | Pimul_r r1 => EmptyEffect
  | Pmul_r r1 => EmptyEffect
  | Pdiv r1 =>  EmptyEffect
  | Pidiv r1 => EmptyEffect
  | Pand_rr rd r1 => EmptyEffect
  | Pand_ri rd n => EmptyEffect
  | Por_rr rd r1 => EmptyEffect
  | Por_ri rd n => EmptyEffect
  | Pxor_r rd => EmptyEffect
  | Pxor_rr rd r1 => EmptyEffect
  | Pxor_ri rd n => EmptyEffect
  | Psal_rcl rd => EmptyEffect
  | Psal_ri rd n => EmptyEffect
  | Pshr_rcl rd => EmptyEffect
  | Pshr_ri rd n => EmptyEffect
  | Psar_rcl rd => EmptyEffect
  | Psar_ri rd n => EmptyEffect
  | Pshld_ri rd r1 n => EmptyEffect
  | Pror_ri rd n => EmptyEffect
  | Pcmp_rr r1 r2 => EmptyEffect
  | Pcmp_ri r1 n => EmptyEffect
  | Ptest_rr r1 r2 => EmptyEffect
  | Ptest_ri r1 n => EmptyEffect
  | Pcmov c rd r1 => EmptyEffect
  | Psetcc c rd => EmptyEffect

  (** Arithmetic operations over floats *)
  | Paddd_ff rd r1 => EmptyEffect
  | Psubd_ff rd r1 => EmptyEffect
  | Pmuld_ff rd r1 => EmptyEffect
  | Pdivd_ff rd r1 => EmptyEffect
  | Pnegd rd => EmptyEffect
  | Pabsd rd => EmptyEffect
  | Pcomisd_ff r1 r2 => EmptyEffect
  | Pxorpd_f rd => EmptyEffect

  (** Branches and calls *)
  | Pjmp_l lbl => EmptyEffect
  | Pjmp_s id => EmptyEffect
  | Pjmp_r r => EmptyEffect
  | Pjcc cond lbl => EmptyEffect
  | Pjcc2 cond1 cond2 lbl => EmptyEffect
  | Pjmptbl r tbl => EmptyEffect
  | Pcall_s id => EmptyEffect
  | Pcall_r r => EmptyEffect
  | Pret => EmptyEffect
  (** Pseudo-instructions *)
  | Plabel lbl => EmptyEffect
  | Pallocframe sz ofs_ra ofs_link => EmptyEffect
  | Pfreeframe sz ofs_ra ofs_link =>
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
  | Pbuiltin ef args res =>
     (BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) (map rs args)) m)
  | Pannot ef args =>
      EmptyEffect 
  end.*)
*)
Variable ge: genv.

Inductive asm_effstep: (block -> Z -> bool) -> 
                       state -> mem -> state -> mem -> Prop :=
  | asm_effexec_step_internal:
      forall b ofs f i rs m rs' m' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      exec_instr ge f i rs m = Next rs' m' ->
      asm_effstep (effect_instr ge (fn_code f) i rs m) (State rs lf) m (State rs' lf) m'
  | asm_effexec_step_builtin:
      forall b ofs f ef args res rs m vargs t E vres rs' m' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs ESP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      ~ observableEF (*hf*) ef ->
      rs' = nextinstr_nf 
             (set_res res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      E = BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) vargs) m ->
      asm_effstep E (State rs lf) m (State rs' lf) m'
(*WAS  | asm_effexec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs ESP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      ~ observableEF hf ef ->
      rs' = nextinstr_nf 
             (set_res res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      asm_effstep (effect_instr ge (fn_code f) (Pbuiltin ef args res) rs m) 
                  (State rs lf) m (State rs' lf) m'*)
  | asm_effexec_step_to_external:
      forall b ef args rs m lf,
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      asm_effstep EmptyEffect (State rs lf) m (Asm_CallstateOut ef args rs lf) m
  | asm_effexec_step_external:
      forall b callee args res rs m t rs' m' lf
      (OBS: EFisHelper (*hf*) callee),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External callee) ->
      external_call' callee ge args m t res m' ->
      rs' = (set_regs (loc_external_result (ef_sig callee)) res rs) #PC <- (rs RA) ->
      asm_effstep  (BuiltinEffect ge callee args m)
         (Asm_CallstateOut callee args rs lf) m (State rs' lf) m'
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
      asm_effstep EmptyEffect 
               (Asm_CallstateIn fb args tys retty) m 
               (State rs0 (mk_load_frame stk retty)) m2.

End EFFSEM.

Section ASM_EFFSEM.

Lemma exec_load_unchanged_on: forall g chunk m a rs rd rs' m' P,
   exec_load g chunk m a rs rd = Next rs' m' ->
   Mem.unchanged_on P m m'.
Proof. intros.
  unfold exec_load in H. 
  remember (Mem.loadv chunk m (eval_addrmode g a rs)) as d.
  destruct d; inv H. apply Mem.unchanged_on_refl.
Qed.

Lemma exec_store_unchanged_on: forall g chunk m a rs rs1 pregs rs' m',
  exec_store g chunk m a rs rs1 pregs = Next rs' m' ->
  Mem.unchanged_on (fun b z => StoreEffect (eval_addrmode g a rs) 
                     (encode_val chunk (rs rs1)) b z = false)
                   m m'.
Proof. intros. unfold exec_store in H.
  remember (Mem.storev chunk m (eval_addrmode g a rs) (rs rs1)) as d.
  destruct d; inv H. apply eq_sym in Heqd.
  eapply StoreEffect_Storev; eassumption. 
Qed.

Lemma goto_label_unchanged_on: forall c0 l rs m rs' m' P,
      goto_label c0 l rs m = Next rs' m' -> 
   Mem.unchanged_on P m m'.
Proof. intros.
  unfold goto_label in H.
   destruct (label_pos l 0 (fn_code c0)); inv H.
   destruct (rs PC); inv H1. 
   apply Mem.unchanged_on_refl. 
Qed. 

Lemma exec_instr_unchanged_on g f i rs m rs' m': forall
      (EI: exec_instr g f i rs m = Next rs' m'),
     Mem.unchanged_on (fun b ofs => effect_instr g (fn_code f) i rs m b ofs = false) m m'.
Proof. intros. Admitted.
(*    destruct i; 
    try solve [inv EI;
                try solve [apply Mem.unchanged_on_refl];
                try solve [eapply exec_load_unchanged_on; eauto];
                try solve [eapply exec_store_unchanged_on; eauto];
                try solve [eapply goto_label_unchanged_on; eauto]].  
    inv EI. 
      destruct (Val.divu (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
      destruct (Val.modu (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
      apply Mem.unchanged_on_refl.
    inv EI.
      destruct (Val.divs (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
      destruct (Val.mods (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
      apply Mem.unchanged_on_refl.
    inv EI.
      destruct (eval_testcond c0 rs); inv H0.
        destruct b; inv H1; apply Mem.unchanged_on_refl.
      apply Mem.unchanged_on_refl.
    inv EI.
      destruct (eval_testcond c0 rs); inv H0.
        destruct b; inv H1. eapply goto_label_unchanged_on; eauto.
      apply Mem.unchanged_on_refl.
    inv EI.
      destruct (eval_testcond c1 rs); inv H0.
        destruct b; inv H1.
          destruct (eval_testcond c2 rs); inv H0.
            destruct b; inv H1. eapply goto_label_unchanged_on; eauto.
            apply Mem.unchanged_on_refl.
          destruct (eval_testcond c2 rs); inv H0.
            apply Mem.unchanged_on_refl.
    inv EI.
      destruct (rs r); inv H0.
        destruct (list_nth_z tbl (Int.unsigned i)); inv H1.
        eapply goto_label_unchanged_on; eauto.
    inv EI.
      remember (Mem.alloc m 0 sz) as d. 
      destruct d; apply eq_sym in Heqd; inv H0.
      remember (Mem.store Mint32 m0 b (Int.unsigned (Int.add Int.zero ofs_link)) (rs ESP)) as q.
      apply eq_sym in Heqq; destruct q; inv H1.
      remember (Mem.store Mint32 m1 b (Int.unsigned (Int.add Int.zero ofs_ra)) (rs RA)) as w.
      destruct w; apply eq_sym in Heqw; inv H0.
      simpl. 
      split; intros. 
        split; intros. 
        eapply Mem.perm_store_1; try eassumption.
        eapply Mem.perm_store_1; try eassumption.
        eapply Mem.perm_alloc_1; eassumption.
      apply (Mem.perm_store_2 _ _ _ _ _ _ Heqw) in H1.
        apply (Mem.perm_store_2 _ _ _ _ _ _ Heqq) in H1.
        eapply Mem.perm_alloc_4; try eassumption.
         intros N; subst. apply Mem.fresh_block_alloc in Heqd. contradiction.
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ Heqw).
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ Heqq).
        assert (BB: b0 <> b). intros N. subst. apply Mem.fresh_block_alloc in Heqd. apply Mem.perm_valid_block in H0. contradiction.
        rewrite PMap.gso; trivial. 
        rewrite PMap.gso; trivial. 
        eapply EmptyEffect_alloc; eassumption.
    inv EI.
      remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))) as d.
      destruct d; inv H0.
      remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))) as q.
      destruct q; inv H1.
      remember (rs ESP) as w.
      destruct w; inv H0.
      remember (Mem.free m b 0 sz) as t.
      destruct t; inv H1; apply eq_sym in Heqt.
      eapply unchanged_on_validblock.
      Focus 2. eapply FreeEffect_free; eassumption.
      intuition. unfold effect_instr in H0.
        rewrite <- Heqw, <- Heqd, <- Heqq, Heqt in H0. trivial.
Qed.*)

(*Axiom EE1: forall g c ef res rs m b ofs,
    effect_instr g c (Pbuiltin ef nil res) rs m b ofs = BuiltinEffect g ef nil m b ofs.
*)

Lemma decode_longs_nil: forall tys, decode_longs tys nil = nil.
induction tys. trivial.  simpl in *. destruct a; trivial. Qed.
Require Import msl.Extensionality.
(*
Lemma BuiltinEffect_decode: forall F V (ge: Genv.t F V) ef vargs,
 BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) vargs)=
 BuiltinEffect ge ef vargs.
Proof. intros.
  unfold BuiltinEffect. extensionality m. 
  destruct ef; trivial.
  + unfold free_Effect. simpl.
    destruct vargs; simpl. reflexivity. destruct v; try reflexivity.
    destruct vargs. reflexivity.
    destruct (Mem.load Mint32 m b (Int.unsigned i - 4)); try reflexivity.
    destruct v0; try reflexivity. 
    extensionality bb. extensionality z.
    destruct (eq_block bb b); simpl; trivial. subst.
    destruct (zlt 0 (Int.unsigned i0)); simpl; trivial.
    destruct (zle (Int.unsigned i - 4) z ); simpl; trivial.
    destruct (zlt z (Int.unsigned i + Int.unsigned i0)); simpl; trivial. omega.
Qed.

 BuiltinEffect ge ef (map tls (loc_arguments (ef_sig ef))) =
 BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef))
           (map tls (loc_arguments (ef_sig ef)))).
Proof. intros.
  unfold BuiltinEffect. extensionality m. 
  destruct ef; trivial.
Qed.
*)
Lemma asmstep_effax1: forall (M : block -> Z -> bool) g c m c' m',
      asm_effstep g M c m c' m' ->
      (asm_step (*hf*) g c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m').
Proof. Admitted.
 (*Proof.
intros.
destruct H.
+ split. eapply asm_exec_step_internal; eassumption.
  clear -H2 hf. eapply exec_instr_unchanged_on; eassumption.
+ split. eapply asm_exec_step_builtin; eassumption.
  simpl. Locate BuiltinEffect_decode. in H6. subst. eapply BuiltinEffect_unchOn. eassumption. eassumption. inv H2.
  - rewrite decode_longs_nil. eapply BuiltinEffect_unchOn; eassumption.
  - eapply BuiltinEffect_unchOn. eassumption. eassumption. 
  assert (EE1: effect_instr g (fn_code f) (Pbuiltin ef nil res) rs m b0 ofs0 = BuiltinEffect g ef nil m b0 ofs0).
         eapply BuiltinEffect_unchOn; eassumption. 
  admit. (*
  split. econstructor; eauto.
       apply Mem.unchanged_on_refl. *)
+ split. econstructor; eauto.
       apply Mem.unchanged_on_refl.
+ split. econstructor; eauto.
  inv H1.
       exploit @BuiltinEffect_unchOn. 
         eapply EFhelpers; eassumption.
         eapply H3. 
       unfold BuiltinEffect; simpl.
         destruct callee; simpl; trivial; contradiction.
+ split. econstructor; eassumption. 
  { assert (sp_fresh: ~Mem.valid_block m stk).
    { eapply Mem.fresh_block_alloc; eauto. }
    eapply mem_unchanged_on_sub_strong.
    eapply unchanged_on_trans with (m2 := m1).
    solve[eapply Mem.alloc_unchanged_on; eauto].
    solve[eapply store_args_unch_on; eauto].
    solve[apply alloc_forward in H0; auto].
    simpl. intros b ofs H2 _ H3. subst. 
    solve[apply sp_fresh; auto]. }
Admitted.       
*)
Lemma asmstep_effax2: forall  g c m c' m',
      asm_step (*hf*) g c m c' m' ->
      exists M, asm_effstep g M c m c' m'.
Proof. Admitted. (*
intros. (*unfold corestep, Asm_coop_sem in H; simpl in H.*)
  inv H.
+ destruct i;
    try solve [eexists; econstructor; try eassumption].
+ eexists. eapply asm_effexec_step_builtin; try eassumption. trivial.
+ eexists. econstructor; eassumption.
+ eexists. econstructor; eauto.
+ eexists. econstructor; eauto.
Qed.*)

Lemma exec_store_curWR ge ch m1 a rs1 rs rs2 m2 b z l:
   exec_store ge ch m1 a rs1 rs l = Next rs2 m2 ->
    StoreEffect (eval_addrmode ge a rs1)
         (encode_val ch (rs1 rs)) b z = true ->
   Mem.perm m1 b z Cur Writable.
Proof.
intros. apply StoreEffectD in H0. destruct H0 as [i [? [? ?]]].
  unfold exec_store in H. rewrite H0 in *. simpl in H. 
  remember (Mem.store ch m1 b (Int.unsigned i) (rs1 rs)) as q.
  destruct q; inv H. symmetry in Heqq. 
  eapply (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq). 
  rewrite encode_val_length, <- size_chunk_conv in H2. omega.
Qed.

Lemma free_curWR bb lo hi b z: forall m m',
      Mem.free m bb lo hi = Some m' ->
      FreeEffect m lo hi bb b z = true ->
      Mem.perm m b z Cur Writable.
Proof. clear.
  intros.
  apply FreeEffectD in H0. destruct H0 as [? [? ?]]; subst bb.
  eapply Mem.perm_implies. 
  eapply Mem.free_range_perm; eassumption. constructor.
Qed.

Lemma exec_instr_curWR ge f i rs1 m1 rs2 m2: forall
      (EI: exec_instr ge f i rs1 m1 = Next rs2 m2) b z
      (EFFI: effect_instr ge (fn_code f) i rs1 m1 b z = true),
      Mem.perm m1 b z Cur Writable.
Proof. intros.
  destruct i; simpl in *; try discriminate.
(*+ eapply exec_store_curWR; eauto. 
+ eapply exec_store_curWR; eauto. 
+ eapply exec_store_curWR; eauto. 
+ eapply exec_store_curWR; eauto. 
+ eapply exec_store_curWR; eauto. 
+ eapply exec_store_curWR; eauto. 
+ remember (Mem.loadv Mint32 m1 (Val.add (rs1 ESP) (Vint ofs_ra))) as q.
  destruct q; try discriminate.
  remember (Mem.loadv Mint32 m1 (Val.add (rs1 ESP) (Vint ofs_link))) as p. 
  destruct p; try discriminate. 
  remember (rs1 ESP) as u.
  destruct u; try discriminate.
  remember (Mem.free m1 b0 0 sz) as d.
  destruct d; try discriminate. 
  symmetry in Heqd. eapply free_curWR; eassumption.*)
Qed.

Lemma asm_effstep_curWR: forall (M : block -> Z -> bool) g c m c' m',
      asm_effstep g M c m c' m' ->
      forall b z, M b z = true -> Mem.perm m b z Cur Writable.
Proof. Admitted. (*
  intros.
  induction H; try (solve [inv H0]).
+ eapply exec_instr_curWR; eauto.
+ unfold effect_instr in H0.
  destruct ef; simpl in *; try discriminate.
  - inv H3. simpl in *.
    destruct args; simpl in *. discriminate.
    inv H6. rewrite <- H3 in *.
    remember (Mem.load Mint32 m b1 (Int.unsigned lo - 4)) as u. 
    destruct u; try discriminate.
    destruct v; try discriminate. inv H5.
    destruct (eq_block b b1); simpl in *; try discriminate. subst b1.
    destruct (zlt 0 (Int.unsigned sz)); simpl in *; try discriminate.
    destruct (zle (Int.unsigned lo - 4) z); simpl in *; try discriminate.
    destruct (zlt z (Int.unsigned lo + Int.unsigned sz)); simpl in *; try discriminate.
    eapply Mem.perm_implies. 
    eapply Mem.free_range_perm. eassumption. omega. constructor.
  - inv H3. simpl in *.
    destruct args; simpl in *. discriminate.
    inv H6. rewrite <- H3 in *.
    destruct args; simpl in *. discriminate. inv H5. rewrite <- H14 in *.
    destruct (eq_block b bdst); simpl in *; try discriminate. subst bdst.
    destruct (zle (Int.unsigned odst) z); simpl in *; try discriminate.
    destruct (zlt z (Int.unsigned odst + sz)); simpl in *; try discriminate.
    eapply Mem.storebytes_range_perm. eassumption. 
    apply Mem.loadbytes_length in H13. rewrite H13, nat_of_Z_eq; omega.
+ unfold BuiltinEffect in H0. 
  destruct callee; try discriminate.
  - inv H2. inv H4. eapply free_curWR. eassumption.
    destruct args; inv H2.
    unfold free_Effect in H0. unfold FreeEffect. destruct args; try discriminate.
    rewrite H3 in *.
    destruct (eq_block b b1); subst; simpl in *; try discriminate.
        destruct (zlt 0 (Int.unsigned sz)); simpl in *; try discriminate.
        destruct (zle (Int.unsigned lo - 4) z); simpl in *; try discriminate. 
        destruct (zlt z (Int.unsigned lo + Int.unsigned sz)); simpl in *; try discriminate.
    apply Mem.load_valid_access in H3.
    destruct (valid_block_dec m b1); trivial. 
    elim n. eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies. eassumption. constructor.
  - clear - H0 H2. inv H2. inv H. 
    unfold memcpy_Effect in H0.
    destruct args; inv H1. 
    destruct args; inv H0. inv H11.
    destruct args; inv H1.
    destruct (eq_block b bdst); subst; simpl in *; try discriminate.
    destruct (zle (Int.unsigned odst) z); simpl in *; try discriminate.
    destruct (zlt z (Int.unsigned odst + sz)); simpl in *; try discriminate. 
    eapply Mem.storebytes_range_perm. eassumption. 
    apply Mem.loadbytes_length in H8. rewrite H8, nat_of_Z_eq; omega.
Qed.
*)
Lemma exec_store_valid: forall g chunk m a rs rs1 pregs rs' m' b z,
  exec_store g chunk m a rs rs1 pregs = Next rs' m' ->
  StoreEffect (eval_addrmode g a rs) (encode_val chunk (rs rs1)) b z =
              true ->
  Mem.valid_block m b.
Proof. intros. eapply Mem.perm_valid_block. eapply exec_store_curWR; eassumption. Qed.
(*
Lemma exec_instr_valid_block ge fn i rs1 m1 rs2 m2: forall
      (EI: exec_instr ge fn i rs1 m1 = Next rs2 m2) b z
      (EFFI: effect_instr ge fn i rs1 m1 b z = true),
      Mem.valid_block m1 b.
Proof. intros. eapply Mem.perm_valid_block. eapply exec_instr_curWR; eassumption. Qed.
*)
Lemma asm_effstep_valid: forall (M : block -> Z -> bool) g c m c' m',
      asm_effstep g M c m c' m' ->
       forall b z, M b z = true -> Mem.valid_block m b.
Proof. intros. eapply Mem.perm_valid_block. eapply asm_effstep_curWR; eassumption. Qed.

Program Definition Asm_eff_sem : 
  @EffectSem genv state.
Proof.
eapply Build_EffectSem with (sem := Asm_mem_sem hf).
apply asmstep_effax1.
apply asmstep_effax2.
apply asm_effstep_curWR.
Defined.

Lemma Asm_eff_sem_det : semantics_lemmas.corestep_fun Asm_eff_sem.
Proof.
intros m m' m'' ge c c' c'' step1 step2.
simpl in step1, step2.
admit. (*eapply asm_step_det in step1; eauto.*)
(*destruct step1; subst; auto.*)
Admitted.

End ASM_EFFSEM.

End ASM_EFF.
