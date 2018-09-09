Require Import compcert.lib.Coqlib.
Require Import ZArith List.
Import ListNotations.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import compcert.common.Events.
Require Import compcert.x86.Asm.
Require Import compcert.common.Values.
Import AST.

(*To prove memsem*)
Require Import VST.concurrency.common.core_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.mem_lemmas.

(*
Definition empty_function : function := 
  mkfunction (mksignature nil None cc_default) nil.

Definition funsig (fd: Asm.fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.
*)

Lemma Asm_corestep_not_halted :
  forall ge m q m' q' i, step2corestep (part_semantics ge) q m q' m' -> ~final_state q i.
Proof.
  repeat intro.
  inv H0.
  inv H.
  inv H0.
  - rewrite H1 in H5; inv H5.
  - rewrite H1 in H5; inv H5.
  - rewrite H1 in H5; inv H5.
Qed.

(*Program Definition Asm_core_sem (ge : genv) :
  @CoreSemantics regset mem :=
  @Build_CoreSemantics _ _
    (fun _ => Asm_initial_core ge)
    (Asm_at_external ge)
    (fun v q m => Asm_after_external ge v q)
    (fun _ _ => False)
    (Asm_step ge)
    _
    (Asm_corestep_not_at_external ge).*)

Definition Asm_core_sem (ge : genv) := sem2coresem (part_semantics ge) (Asm_corestep_not_halted ge).

Section ASM_MEMSEM.

Lemma exec_load_mem_step ge ch m a rs rd rs' m': forall
      (EI: exec_load ge ch m a rs rd = Next rs' m'),
      mem_step m m'.
Proof. intros.
  unfold exec_load in EI.
  remember (Mem.loadv ch m (eval_addrmode ge a rs) ).
  symmetry in Heqo; destruct o; inversion EI; clear EI; subst. apply mem_step_refl.
Qed.

Lemma exec_store_mem_step ge ch m a rs rs0 vals rs' m': forall
      (ES: exec_store ge ch m a rs rs0 vals = Next rs' m'),
      mem_step m m'.
Proof. intros.
  unfold exec_store in ES.
  remember (Mem.storev ch m (eval_addrmode ge a rs) (rs rs0)).
  symmetry in Heqo; destruct o; inversion ES; clear ES; subst.
  remember (eval_addrmode ge a rs). destruct v; inversion Heqo; clear Heqo; subst.
  eapply mem_step_store; eassumption.
Qed.

Lemma goto_label_mem_same c0 l rs m rs' m': forall
      (G: goto_label c0 l rs m = Next rs' m'), m=m'.
Proof. intros.
   unfold goto_label in G.
   destruct (label_pos l 0 (fn_code c0)); inversion G; clear G; subst.
   destruct (rs PC); inversion H0; clear H0; subst. auto.
Qed.

Lemma goto_label_mem_step c0 l rs m rs' m': forall
      (G: goto_label c0 l rs m = Next rs' m'),
      mem_step m m'.
Proof. intros.
  apply goto_label_mem_same in G. subst; apply mem_step_refl.
Qed.

Lemma exec_instr_mem_step ge c i rs m rs' m': forall
      (EI: exec_instr ge c i rs m = Next rs' m'),
      mem_step m m'.
Proof. intros.
   destruct i; simpl in *; inversion EI; clear EI; subst; try apply mem_step_refl;
   try (eapply exec_load_mem_step; eassumption);
   try (eapply exec_store_mem_step; eassumption).

   destruct (rs RDX); inv H0.
   destruct (rs RAX); inv H1.
   destruct (rs r1); inv H0.
   destruct (Int.divmodu2 _ _ _) as [[]|]; inv H1.
   apply mem_step_refl.

   destruct (rs RDX); inv H0.
   destruct (rs RAX); inv H1.
   destruct (rs r1); inv H0.
   destruct (Int64.divmodu2 _ _ _) as [[]|]; inv H1.
   apply mem_step_refl.

   destruct (rs RDX); inv H0.
   destruct (rs RAX); inv H1.
   destruct (rs r1); inv H0.
   destruct (Int.divmods2 _ _ _) as [[]|]; inv H1.
   apply mem_step_refl.

   destruct (rs RDX); inv H0.
   destruct (rs RAX); inv H1.
   destruct (rs r1); inv H0.
   destruct (Int64.divmods2 _ _ _) as [[]|]; inv H1.
   apply mem_step_refl.

   destruct (eval_testcond c0 rs); inversion H0; clear H0; subst.
   destruct b; inversion H1; clear H1; subst; apply mem_step_refl.
   apply mem_step_refl.

   eapply goto_label_mem_step; eassumption.

   destruct (eval_testcond c0 rs); inversion H0; clear H0; subst.
   destruct b; inversion H1; clear H1; subst.
   eapply goto_label_mem_step; eassumption.
   apply mem_step_refl.

   destruct (eval_testcond c1 rs); inversion H0; clear H0; subst.
   destruct b.
     destruct (eval_testcond c2 rs); inversion H1; clear H1; subst.
     destruct b; inversion H0; clear H0; subst.
     eapply goto_label_mem_step; eassumption.
   apply mem_step_refl.

     destruct (eval_testcond c2 rs); inversion H1; clear H1; subst.
     apply mem_step_refl.
     destruct (rs r); inversion H0; clear H0; subst.
     destruct (list_nth_z tbl (Int.unsigned i)); inversion H1; clear H1; subst.
     eapply goto_label_mem_step; eassumption.
  remember (Mem.alloc m 0 sz) as d; apply eq_sym in Heqd.
    destruct d; inv H0.
    remember (Mem.store Mptr m0 b (Ptrofs.unsigned (Ptrofs.add Ptrofs.zero ofs_link))
         (rs RSP)) as q.
    apply eq_sym in Heqq; destruct q; inversion H1; clear H1; subst.
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

Lemma ev_elim_mem_step: forall t m m', ev_elim m t m' -> mem_step m m'.
Proof.
induction t; simpl; intros.
subst. apply mem_step_refl.
destruct a.
destruct H as [m'' [? ?]].
eapply mem_step_trans; [ | eauto].
eapply mem_step_storebytes; eauto.
destruct H as [? ?].
eapply mem_step_trans; [ | eauto].
apply mem_step_refl.
destruct H as [m'' [? ?]].
eapply mem_step_trans; [ | eauto].
eapply mem_step_alloc; eauto.
destruct H as [m'' [? ?]].
eapply mem_step_trans; [ | eauto].
eapply mem_step_freelist; eauto.
Qed.

Lemma get_extcall_arg_spec : forall r m l v,
  get_extcall_arg r m l = Some v <-> extcall_arg r m l v.
Proof.
  split; intro.
  - destruct l; simpl in *.
    + inv H; constructor.
    + destruct sl; try discriminate.
      econstructor; eauto.
  - inv H; auto.
Qed.

Lemma get_extcall_arguments_spec : forall r m sig args,
  get_extcall_arguments r m (Conventions1.loc_arguments sig) = Some args <->
  extcall_arguments r m sig args.
Proof.
  unfold extcall_arguments; split; intro.
  - revert dependent args; induction (Conventions1.loc_arguments sig); simpl; intros.
    { inv H; constructor. }
    destruct a.
    + destruct (get_extcall_arg _ _ _) eqn: Hget; [|discriminate].
      destruct (get_extcall_arguments _ _ _); inv H.
      constructor; auto.
      constructor; apply get_extcall_arg_spec; auto.
    + destruct (get_extcall_arg _ _ _) eqn: Hget1; [|discriminate].
      destruct (get_extcall_arg _ _ rlo) eqn: Hget2; [|discriminate].
      destruct (get_extcall_arguments _ _ _); inv H.
      constructor; auto.
      constructor; apply get_extcall_arg_spec; auto.
  - induction H; auto; simpl.
    rewrite IHlist_forall2.
    inv H; repeat match goal with H : extcall_arg _ _ _ _ |- _ =>
      apply get_extcall_arg_spec in H; rewrite H end; auto.
Qed.

(* A safe genv only marks as Internal functions that either have known semantics or don't touch
   memory. 
   The false conjuct in the second case essentially gives us that the program has no
   builtins other than malloc, free, memcpy (which is true for the programs supported by VST).
   In the future (right now it's not done because our imports would be affected),
   we could generalize the property to be compatible with our stack of proofs:
   1. Supporting externals whose semantics are preserved by alpha renaming 
      forall f m2 vargs2, mem_obs_eq f m m2 -> val_obs_eq_list f vargs vargs ->
                          external_call ef (Genv.to_senv ge) vargs m t vres m ->
                          exists vres, external_call ef (Genv.to_senv ge) vargs2 m2 t vres' m2 /\
                                       val_obs_eq f vres vres'
   2. and whose semantics are preserved by permission erasure:
      forall m2 vargs2, mem_erasure m m2 -> val_erasure_list vargs vargs ->
                          external_call ef (Genv.to_senv ge) vargs m t vres m ->
                          exists vres, external_call ef (Genv.to_senv ge) vargs2 m2 t vres' m2 /\
                                       val_erasure vres vres'
      
*)
Definition safe_genv (ge : genv) :=
  forall b ofs f ef args res r m vargs t vres m', Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some (Pbuiltin ef args res) ->
    eval_builtin_args (Genv.to_senv ge) r (r (IR RSP)) m args vargs ->
    external_call ef (Genv.to_senv ge) vargs m t vres m' ->
  match ef with
  | EF_malloc | EF_free | EF_memcpy _ _ => True
  | _ => m' = m /\ (forall mm, external_call ef (Genv.to_senv ge) vargs mm t vres mm) /\ False
  end.

Lemma asm_mem_step : forall ge c m c' m' (CS: corestep (Asm_core_sem ge) c m c' m')
  (Hsafe : safe_genv ge), mem_step m m'.
Proof. intros.
  inv CS.
  destruct c, c'; simpl in *.
  inv H; simpl in *; try apply mem_step_refl; try contradiction.
 + eapply exec_instr_mem_step; try eassumption.
 + exploit Hsafe; eauto.
   destruct ef; try solve [intros []; subst; apply mem_step_refl]; intros _.
   * (* malloc *) inv H10.
     eapply mem_step_trans.
     -- eapply mem_step_alloc; eauto.
     -- eapply mem_step_storebytes, Mem.store_storebytes; eauto.
   * (* free *) inv H10.
     eapply mem_step_free; eauto.
   * (* memcpy *) inv H10.
     eapply mem_step_storebytes; eauto.
 + rewrite H5 in H0.
   destruct (Ptrofs.eq_dec _ _); [|contradiction].
   rewrite H6 in H0.
   apply get_extcall_arguments_spec in H8; rewrite H8 in H0; discriminate.
Qed.

Lemma ple_exec_load:
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

Program Definition Asm_mem_sem (ge : genv) (Hsafe : safe_genv ge) : @MemSem state.
Proof.
apply Build_MemSem with (csem := Asm_core_sem ge).
intros; eapply asm_mem_step; eauto.
Defined.

Lemma exec_instr_forward g c i rs m rs' m': forall
      (EI: exec_instr g c i rs m = Next rs' m'),
      mem_forward m m'.
Proof. intros.
    apply mem_forward_preserve.
    eapply exec_instr_mem_step; eassumption.
Qed.

End ASM_MEMSEM.
