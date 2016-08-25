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

Require Import msl.Extensionality.

Notation SP := ESP (only parsing).

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

Section ASM_EFF.
(*Variable hf : I64Helpers.helper_functions.*)

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

Definition effect_instr (ge:genv) (c: code) (i: instruction) (rs: regset) (m: mem) 
           : (block -> Z -> bool)  :=
  match i with
  | Pfstps_m a => (StoreEffect (eval_addrmode ge a rs) (encode_val Mfloat32 (rs ST0)))
  | Pfstpl_m a => (StoreEffect (eval_addrmode ge a rs) (encode_val Mfloat64 (rs ST0)))
  | Pmovss_mf a r1 => (StoreEffect (eval_addrmode ge a rs) (encode_val Mfloat32 (rs r1)))
  | Pmov_mr a r1 => (StoreEffect (eval_addrmode ge a rs) (encode_val Mint32 (rs r1)))
  | Pmov_mr_a a r1 => (StoreEffect (eval_addrmode ge a rs) (encode_val Many32 (rs r1)))
  | Pmovsd_mf a r1 => (StoreEffect (eval_addrmode ge a rs) (encode_val Mfloat64 (rs r1)))
  | Pmovsd_mf_a a r1 => (StoreEffect (eval_addrmode ge a rs) (encode_val Many64 (rs r1)))
  | Pmovb_mr a r1 => StoreEffect (eval_addrmode ge a rs) (encode_val Mint8unsigned (rs r1))
  | Pmovw_mr a r1 => StoreEffect (eval_addrmode ge a rs) (encode_val Mint16unsigned (rs r1))
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
  | Pbuiltin ef args res => EmptyEffect
(*     (BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) (map rs args)) m)*)
(*  | Pannot ef args =>
      EmptyEffect *)
  | _ => EmptyEffect
  end. 
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
      False -> (*We don't support builtins/helpers/vload/vstore etc yet*)
      forall b ofs f ef args res rs m vargs t E vres rs' m' lf
         (NASS: ~ isInlinedAssembly ef)  (*NEW; we don't support inlined assembly yet*),
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs ESP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      ~ observableEF (*hf*) ef ->
      rs' = nextinstr_nf 
             (set_res res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
(*in compcomp:      E = BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) vargs) m ->*)
      E = BuiltinEffect ge ef vargs m ->
      asm_effstep E (State rs lf) m (State rs' lf) m'

  | asm_effexec_step_to_external:
      forall b ef args rs m lf,
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      asm_effstep EmptyEffect (State rs lf) m (Asm_CallstateOut ef args rs lf) m
  | asm_effexec_step_external:
      False -> (*We don't support builtins/helpers/vload/vstore etc yet*)
      forall b callee args res rs m t rs' m' lf
      (OBS: EFisHelper (*hf*) callee),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External callee) ->
      extcall_arguments rs m (ef_sig callee) args ->
      external_call callee ge args m t res m' ->
      rs' = (set_pair (loc_external_result (ef_sig callee)) res rs) #PC <- (rs RA) ->
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
Proof. intros. 
 destruct i;
    try solve [inv EI;
                try solve [apply Mem.unchanged_on_refl];
                try solve [eapply exec_load_unchanged_on; eauto];
                try solve [eapply exec_store_unchanged_on; eauto];
                try solve [eapply goto_label_unchanged_on; eauto]].
+ (*Pdiv r1*) inv EI.
  destruct (Val.divu (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
  destruct (Val.modu (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
  apply Mem.unchanged_on_refl.
+ (*Pidiv r1*) inv EI.
  destruct (Val.divs (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
  destruct (Val.mods (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
  apply Mem.unchanged_on_refl.
+ (*Pcmov c rd r1*) inv EI.
      destruct (eval_testcond c rs); inv H0.
        destruct b; inv H1; apply Mem.unchanged_on_refl.
      apply Mem.unchanged_on_refl.
+ (*Pjcc c l*) inv EI.
      destruct (eval_testcond c rs); inv H0.
        destruct b; inv H1. eapply goto_label_unchanged_on; eauto.
      apply Mem.unchanged_on_refl.
+ (*Pjcc2 c1 c2 l*) inv EI.
      destruct (eval_testcond c1 rs); inv H0.
        destruct b; inv H1.
          destruct (eval_testcond c2 rs); inv H0.
            destruct b; inv H1. eapply goto_label_unchanged_on; eauto.
            apply Mem.unchanged_on_refl.
          destruct (eval_testcond c2 rs); inv H0.
            apply Mem.unchanged_on_refl.
+  (*Pjmptbl r tbl*) inv EI.
      destruct (rs r); inv H0.
        destruct (list_nth_z tbl (Int.unsigned i)); inv H1.
        eapply goto_label_unchanged_on; eauto.
+ (* Pallocframe sz ofs_ra ofs_link *) inv EI.
      remember (Mem.alloc m 0 sz) as d. 
      destruct d; apply eq_sym in Heqd; inv H0.
      remember (Mem.store Mint32 m0 b (Int.unsigned (Int.add Int.zero ofs_link)) (rs ESP)) as q.
      apply eq_sym in Heqq; destruct q; inv H1.
      remember (Mem.store Mint32 m1 b (Int.unsigned (Int.add Int.zero ofs_ra)) (rs RA)) as w.
      destruct w; apply eq_sym in Heqw; inv H0.
      simpl. 
      split; intros. 
      - rewrite (Mem.nextblock_store _ _ _ _ _ _ Heqw).
        rewrite (Mem.nextblock_store _ _ _ _ _ _ Heqq).
        rewrite (Mem.nextblock_alloc _ _ _ _ _ Heqd). xomega.
      - split; intros. 
        * eapply Mem.perm_store_1; try eassumption.
          eapply Mem.perm_store_1; try eassumption.
          eapply Mem.perm_alloc_1; eassumption.
        * apply (Mem.perm_store_2 _ _ _ _ _ _ Heqw) in H1.
          apply (Mem.perm_store_2 _ _ _ _ _ _ Heqq) in H1.
          eapply Mem.perm_alloc_4; try eassumption.
          intros N; subst. apply Mem.fresh_block_alloc in Heqd. contradiction.
      - rewrite (Mem.store_mem_contents _ _ _ _ _ _ Heqw).
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ Heqq).
        assert (BB: b0 <> b). intros N. subst. apply Mem.fresh_block_alloc in Heqd. apply Mem.perm_valid_block in H0. contradiction.
        rewrite PMap.gso; trivial. 
        rewrite PMap.gso; trivial. 
        eapply EmptyEffect_alloc; eassumption.
+ (* Pfreeframe sz ofs_ra ofs_link *) inv EI.
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
Qed.
(*
Lemma decode_longs_nil: forall tys, decode_longs tys nil = nil.
induction tys. trivial.  simpl in *. destruct a; trivial. Qed.

Lemma BuiltinEffect_decode: forall F V (ge: Genv.t F V) ef vargs,
 BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) vargs)=
 BuiltinEffect ge ef vargs. 
Proof. intros. 
  destruct ef; trivial. 
  + unfold free_Effect. simpl.
    destruct vargs; simpl. reflexivity. destruct v; try reflexivity.
   (* destruct vargs. reflexivity.
    extensionality m. Locate decode_longs. simpl.
    destruct (Mem.load Mint32 m b (Int.unsigned i - 4)); try reflexivity.
    destruct v0; try reflexivity. 
    extensionality bb. extensionality z.
    destruct (eq_block bb b); simpl; trivial. subst.
    destruct (zlt 0 (Int.unsigned i0)); simpl; trivial.
    destruct (zle (Int.unsigned i - 4) z ); simpl; trivial.
    destruct (zlt z (Int.unsigned i + Int.unsigned i0)); simpl; trivial.*)
  + extensionality m. extensionality bb. extensionality z.
    remember (BuiltinEffect ge (EF_memcpy sz al) vargs m bb z) as r.
    remember (BuiltinEffect ge (EF_memcpy sz al) (decode_longs (sig_args (ef_sig (EF_memcpy sz al))) vargs) m bb z) as l.
    symmetry in Heql; symmetry in Heqr.
    destruct r.
    - specialize (BuiltinEffect_valid_block _ _ _ _ _ _ Heqr); intros.
      destruct Heql;  simpl in *; trivial.
      destruct vargs; simpl in *; try discriminate.
      destruct v; simpl in *; try discriminate. 
      destruct vargs; simpl in *; try discriminate.
      destruct v; simpl in *; try discriminate.
      destruct vargs; simpl in *; try discriminate. trivial. trivial.
    - destruct l; trivial. specialize (BuiltinEffect_valid_block _ _ _ _ _ _ Heql); intros.
      simpl in *. 
      destruct vargs; simpl in *; try discriminate.
      destruct v; simpl in *; try discriminate. 
      destruct vargs; simpl in *; try discriminate.
      destruct v; simpl in *; try discriminate.
      destruct vargs; simpl in *; try discriminate. 
      * rewrite Heqr in Heql. discriminate.
      * exfalso. rewrite Heql in Heqr. discriminate. 
Qed.
*)
Lemma asmstep_effax1: forall (M : block -> Z -> bool) g c m c' m'
      (*(HF: helper_functions_declared g hf)*),
      asm_effstep g M c m c' m' ->
      (asm_step (*hf*) g c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m').
Proof. 
intros.
destruct H; try contradiction. 
+ split. eapply asm_exec_step_internal; try eassumption. 
  (*clear -H2 hf.*) eapply exec_instr_unchanged_on; eassumption.
(*+ rewrite BuiltinEffect_decode in H6.
  split. eapply asm_exec_step_builtin; try eassumption. 
  subst E. eapply BuiltinEffect_unchOn; eassumption.*)
+ split. econstructor; eauto.
       apply Mem.unchanged_on_refl.
(*+ split. econstructor; eauto.
  inv H1.
       exploit @BuiltinEffect_unchOn. eassumption.
         eapply EFhelpers; eassumption.
         eapply H3. 
       rewrite BuiltinEffect_decode; trivial. *)
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
Qed.

Lemma asmstep_effax2: forall  g c m c' m',
      asm_step (*hf*) g c m c' m' ->
      exists M, asm_effstep g M c m c' m'.
Proof.
intros. (*unfold corestep, Asm_coop_sem in H; simpl in H.*)
  inv H; try contradiction.
+ destruct i;
    try solve [eexists; econstructor; try eassumption].
(*+ eexists. eapply asm_effexec_step_builtin; try eassumption. trivial. reflexivity.*)
+ eexists. econstructor; eassumption.
(*+ eexists. econstructor; eauto.*)
+ eexists. econstructor; eauto.
Qed.

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
+ eapply exec_store_curWR; eauto. 
+ eapply exec_store_curWR; eauto. 
+ eapply exec_store_curWR; eauto. 
+ eapply exec_store_curWR; eauto. 
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
  symmetry in Heqd. eapply free_curWR; eassumption.
Qed.

Lemma asm_effstep_curWR: forall (M : block -> Z -> bool) g c m c' m',
      asm_effstep g M c m c' m' ->
      forall b z, M b z = true -> Mem.perm m b z Cur Writable.
Proof.
  intros.
  induction H; try (solve [inv H0]); try contradiction.
+ eapply exec_instr_curWR; eauto.
(*+ rewrite BuiltinEffect_decode in *; subst E.
  eapply nonobs_extcall_curWR; eassumption.*)
(*+ apply EFhelpers in OBS. inv H2.
  eapply nonobs_extcall_curWR. eassumption. eassumption.
  rewrite BuiltinEffect_decode; trivial.*)
Qed.

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
eapply Build_EffectSem with (sem := Asm_mem_sem (*hf*)).
apply asmstep_effax1.
apply asmstep_effax2.
apply asm_effstep_curWR.
Defined.

Lemma Asm_eff_sem_det : semantics_lemmas.corestep_fun Asm_eff_sem.
Proof.
intros m m' m'' ge c c' c'' step1 step2.
simpl in step1, step2.
eapply asm_step_det in step1; eauto.
destruct step1; subst; auto.
Qed.

End ASM_EFFSEM.

End ASM_EFF.
