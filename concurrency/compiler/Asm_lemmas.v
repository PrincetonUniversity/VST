
Require Import Omega.
Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.lib.tactics.
Require Import VST.concurrency.common.permissions. Import permissions.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.advanced_permissions.
Require Import VST.concurrency.compiler.diagrams.
Require Import VST.concurrency.compiler.synchronisation_steps_semantics.

Require Import VST.concurrency.lib.Coqlib3.
Import BinNums.
Import BinInt.
Import List.
Import Integers.
Import Ptrofs.
Import Basics.
Import FunctionalExtensionality.

Require Import VST.concurrency.compiler.Asm_self_simulation.
Require Import VST.concurrency.common.mem_equiv.
Require Import VST.concurrency.lib.pair.
Set Nested Proofs Allowed.
Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.
Import bounded_maps.

Instance Asm_get_extcall_arg:
  Proper (Logic.eq ==> mem_equiv ==> Logic.eq ==> Logic.eq) Asm.get_extcall_arg.
Proof.                      
  intros ??? ??? ???; subst.
  destruct y1; auto.
  destruct sl; auto.
  simpl.
  eapply loadv_Proper; auto.             
Qed.
Instance Asm_get_extcall_arguments:
  Proper (Logic.eq ==> mem_equiv ==> Logic.eq ==> Logic.eq) Asm.get_extcall_arguments.
Proof.
  intros ??? ??? ???; subst.
  induction y1; auto.
  destruct a; simpl.
  rewrite IHy1; try rewrite H0; reflexivity.
  rewrite IHy1; repeat rewrite H0.
  destruct (Asm.get_extcall_arg y y0 rhi); auto.
  rewrite H0; reflexivity.
Qed.
Instance  Asm_at_external_proper Asm_g:
  Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
         (semantics.at_external (Asm_core.Asm_core_sem Asm_g)).
Proof.
  intros ??? ???; subst.
  unfold semantics.at_external,
  Asm_core.Asm_core_sem,
  core_semantics.sem2coresem.
  simpl.
  unfold Asm.at_external; destruct y; simpl.
  repeat (match_case; auto); [| |];
    rewrite H0 in Heqo0; rewrite Heqo0 in Heqo1; inv Heqo1; auto.
Qed.

Lemma asm_step_determ:
  forall p s1 lev s2 s2',
    Asm.step (Genv.globalenv p) s1 lev s2 -> 
    Asm.step (Genv.globalenv p) s1 lev s2' ->
    s2 = s2'.
Proof.
  intros.
  exploit Smallstep.sd_determ;
    try eapply Asm.semantics_determinate.
  3:{ intros (?&?); eapply H2; reflexivity. }
  all: simpl; eassumption.
Qed.

Instance Asm_get_extcall_arg_visible:
    Proper (Logic.eq ==> same_visible ==> Logic.eq ==> Logic.eq)
           Asm.get_extcall_arg.
  Proof.
    intros ??? ??? ???; subst.
    destruct y1; auto.
    destruct sl; auto. simpl.
    rewrite H0; auto.
  Qed.
    
  
  

  Instance Asm_get_extcall_arguments_visible:
    Proper (Logic.eq ==> same_visible ==> Logic.eq ==> Logic.eq)
           Asm.get_extcall_arguments.
  Proof.
    intros ??? ??? ???; subst.
    induction y1; auto.
    destruct a; simpl.
    rewrite IHy1. try rewrite H0; reflexivity.
    rewrite IHy1; repeat rewrite H0.
    destruct (Asm.get_extcall_arg y y0 rhi); auto.
    rewrite H0; reflexivity.
  Qed.

    
  Lemma after_x_mem:
    forall ge code2 m s2',
      Asm.after_external ge None code2 m = Some s2' ->
      Asm.get_mem s2' = m.
  Proof.
    unfold Asm.after_external, Asm.get_mem.
    intros.
    destruct code2.
    destruct (Asm.after_external_regset ge None r);
      try discriminate.
    inv H. reflexivity.
  Qed.
  Lemma asm_set_mem_get_mem:
    forall s,
      Asm.set_mem s (Asm.get_mem s) = s.
  Proof. intros; destruct s; reflexivity. Qed.


  Lemma thread_step_from_external:
    forall ge c2 m args c2' rel_trace2 m' FUN
      (Hfun_dsnt_ret: (AST.sig_res (AST.ef_sig FUN)) = None)
      (Hat_x : Asm.at_external ge (Asm.set_mem c2 m) =
               Some (FUN, args))
      (Hafter_x : Asm.after_external
                    ge None c2 (Asm.get_mem c2') = Some c2')
      (Hext_rel: Events.external_call FUN
                                      ge args m
                                      rel_trace2 Vundef m'),
      Asm.step ge (Asm.set_mem c2 m) rel_trace2
               (Asm.set_mem c2' m').
  Proof.
    intros.
    unfold Asm.after_external in *.
    unfold Asm.after_external_regset in *.
    destruct c2.
    destruct c2' eqn:Hs2'; simpl.
    unfold Asm.at_external in *.
    simpl in Hat_x.
    destruct (r Asm.PC) eqn:rPC; try discriminate.
    destruct (eq_dec i zero) eqn:i0_0; try discriminate.
    (*unfold Asm_g. *) 
    destruct (Genv.find_funct_ptr ge b)
             eqn:func_lookup; try discriminate.
    destruct f; try discriminate.
    unfold Asm.after_external.
    unfold Asm.after_external_regset.
    match type of Hat_x with
    | match ?x with _ => _ end = _ =>
      destruct x eqn:HH; try discriminate
    end.
    invert Hat_x; subst i.
    eapply Asm.exec_step_external; eauto.
    - apply Asm_core.get_extcall_arguments_spec; eauto.
    - inv Hafter_x; f_equal.
      unfold Asm.loc_external_result, Conventions1.loc_result.
      rewrite Archi.splitlong_ptr32.
      unfold Conventions1.loc_result_32.
      rewrite Hfun_dsnt_ret; simpl. reflexivity.
      reflexivity.
  Qed.
  
  
  Lemma asm_after_external_when_external_step:
    forall (ge:Asm.genv) c2 m ev c2' args FUN name sig
      (HeqFUN: FUN = (AST.EF_external name sig))
      (HnoReturn : AST.sig_res sig = None)
      (Hno_return: doesnt_return FUN)
      (Hstep: Asm.step ge (Asm.set_mem c2 m) (ev::nil) c2')
      (Hat_x: Asm.at_external ge (Asm.set_mem c2 m) = Some (FUN, args)),
      Asm.after_external ge None c2 (Asm.get_mem c2') = Some c2'.
  Proof.
    intros.
    
    (*Build the after_external, from the at_external. *)
    unfold Asm.at_external in *.
    destruct c2 eqn:Code.
    simpl in Hat_x.
    destruct (r Asm.PC) eqn:rPC; try discriminate.
    destruct (eq_dec i zero) eqn:i0_0; try discriminate.
    (*unfold Asm_g. *) 
    destruct (Genv.find_funct_ptr ge b) eqn:func_lookup; try discriminate.
    destruct f; try discriminate.
    unfold Asm.after_external.
    unfold Asm.after_external_regset.
    rewrite rPC, i0_0, func_lookup.
    
    (* subst rel_trace2;*)

    inversion Hstep; subst; try solve[inversion H4].
    - unfold Asm.at_external in Hat_x.
      rewrite rPC in H1; inversion H1; subst.
      rewrite func_lookup in H2.
      inversion H2; discriminate.
    - rename m' into m21'''.
      unfold Asm.loc_external_result,Conventions1.loc_result.
      replace Archi.ptr64 with false by reflexivity; simpl. 
      

      (* NOTE: 
                       - the s2' (i.e. target state) in comp_match, 
                       results from inverting the step.
                       - the st'2 (i.e. target state) in the goal,
                       results from Asm.after_external. 
       *)
      (* Show that target program is executing the same function*)
      
      assert (FUNeq: e0 = ef ).
      { assert (BB0: b0 = b)
          by (rewrite rPC in H1; inversion H1; reflexivity).
        subst b0. 
        rewrite func_lookup in H2; inversion H2; reflexivity.
      } subst e0.
      
      (* Show that the function is UNLOCK*)
      match type of Hat_x with
      | match ?x with _ => _ end = _ =>
        destruct x eqn:HH; try discriminate
      end.

      inv Hat_x.
      erewrite (Hno_return res) by eauto.
      simpl. unfold Conventions1.loc_result_32.
      rewrite HnoReturn.
      reflexivity.
  Qed.