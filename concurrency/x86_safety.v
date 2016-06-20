Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

(*
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
*)

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.mem_obs_eq.
Require Import concurrency.x86_inj.
Require Import concurrency.compcert_threads_lemmas.
Require Import concurrency.dry_context.
Require Import sepcomp.closed_safety.

Import dry_context SEM mySchedule DryMachine DryMachine.ThreadPool.

(** ** Safety for X86 interleaving semantics *)
Module X86Safe.

  Module SimDefs := SimDefs X86Inj.
  Module SimProofs := SimProofs X86Inj.
  Import SimDefs SimProofs X86Inj dry_machine_lemmas.
  Import Renamings MemObsEq ValObsEq.

Section CSPEC.
  Context {cspec: CoreLanguage.corestepSpec}.

  Definition csafe (tp : thread_pool) m sched :=
    forall n, safeN coarse_semantics the_ge n (sched,tp) m.

  Definition fsafe (tp : thread_pool) m sched :=
    forall n, safeN fine_semantics the_ge n (sched,tp) m.

  Import Asm Asm_coop.

Require Import Coqlib.
Require Import msl.Coqlib2.

Lemma x86_corestep_fun:  corestep_fun Sem.
Proof.
hnf; intros.
inv H; inv H0;
repeat 
  match goal with
  | H: ?A = _, H':?A=_ |- _ => inversion2 H H' 
  | H: ?A, H': ?A |- _ => clear H'
  end;
 try congruence; try now (split; auto).
* {
 pose proof (eval_builtin_args_determ H4 H11).
 subst vargs0. clear H11.
 assert (H99: vres=vres0 /\ m'=m''); [ | destruct H99; subst; auto].
 clear - HFD NASS H4 H5 H6 H12.
 destruct (external_call_determ _ _ _ _ _ _ _ _ _ _ H5 H12).
 inv H; auto.
 admit.
 admit.
 }
* {
 pose proof (extcall_arguments_determ _ _ _ _ _ H3 H10).
 subst args0; auto.
 }
*
 assert (H99: res=res0 /\ m'=m''); [ | destruct H99; subst; auto].
 destruct (external_call_determ' H3 H12).
 apply H0.
 inv H; auto.
 admit.
 admit.
Admitted.
(*
 destruct ef; simpl in NASS; try now (simpl in NASS; contradiction NASS; auto).
 simpl in H6.
 
Focus 10.
contradiction NASS; auto.
contradiction.
 destruct ef; simpl in *.
  +

*)

Lemma mem_step_nextblock:
  forall m m',
     mem_step m m' ->
   (Mem.nextblock m <= Mem.nextblock m')%positive.
Proof.
 induction 1.
 apply Mem.nextblock_storebytes in H; 
   rewrite H; apply Pos.le_refl.
 apply Mem.nextblock_alloc in H.
 rewrite H. clear.
 apply Pos.lt_eq_cases. left. apply Pos.lt_succ_r. apply Pos.le_refl.
 apply effect_properties.nextblock_freelist in H.
   rewrite H; apply Pos.le_refl.
 eapply Pos.le_trans; eassumption.
Qed.

Lemma mem_step_decay:
  forall m m',
     mem_step m m' ->
    decay m m'.
Proof.
 induction 1.
*
 split; intros.
 contradiction H0; clear H0.
 eapply Mem.storebytes_valid_block_2; eauto.
 right. intros.
 apply Mem.storebytes_access in H.
 rewrite H; auto.
*
{
 split; intros.
 assert (b=b').
 pose proof (Mem.nextblock_alloc _ _ _ _ _ H).
 apply Mem.alloc_result in H. subst.
 unfold Mem.valid_block in *.
 rewrite H2 in *; clear H2.
 apply Plt_succ_inv in H1. destruct H1; auto.
 contradiction. subst b'.
 destruct (base.range_dec lo ofs hi); [left | right]; intros.
 pose proof (Mem.perm_alloc_2 _ _ _ _ _ H ofs k a).
 admit.
 pose proof (Mem.perm_alloc_3 _ _ _ _ _ H ofs k).
 admit.
 assert (b<>b').
 intro. subst b'. apply Mem.alloc_result in H. subst b.
 unfold Mem.valid_block in H0. apply Plt_ne in H0.
 contradiction H0; auto.
 right. intro.
 admit.
}
* 
 admit.
*
 apply decay_trans with m''; auto.
 apply mem_step_nextblock in H.
 unfold Mem.valid_block; intros.
 eapply Plt_Ple_trans; try apply H1. apply H.
Admitted.

Lemma x86_exec_instr_obeys_cur:
 forall (the_ge : genv) (m m' : mem) (b : block) 
  (ofs : Z) (f : function) (i : instruction) 
  (rs : preg -> val) (rs' : regset),
~ Mem.perm m b ofs Cur Writable ->
exec_instr the_ge f i rs m = Next rs' m' ->
ZMap.get ofs (PMap.get b (Mem.mem_contents m)) =
ZMap.get ofs (PMap.get b (Mem.mem_contents m')).
Admitted.

Instance x86Spec : CoreLanguage.corestepSpec.
  Proof.
    split.
    intros m m' m'' ge c c' c'' Hstep Hstep'.
    (*TODO: The proofs. *)
 *
   eapply x86_corestep_fun; eauto.
 * {
   intros.
   hnf in Hstep.
   inv Hstep.
 + (* asm_exec_step_internal *)
   clear - H2 Hstable cspec.
   eapply x86_exec_instr_obeys_cur; eauto.
 + (* asm_exec_step_builtin *)
  admit.
 + (* asm_exec_step_to_external *)
   reflexivity.
 + (* asm_exec_step_external *)
  admit.
 + (* asm_exec_initialize_call*)
  clear - H0 H1 Hstable.
  admit. (* problem! *)
 }
 * 
  intros.
  apply mem_step_decay.
 apply asm_mem_step in H; auto.
 *
  intros.
 apply mem_step_nextblock.
 apply asm_mem_step in H; auto.
Admitted.


End CSPEC.
End X86Safe.
  
  


  