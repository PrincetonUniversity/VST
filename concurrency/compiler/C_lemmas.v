
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

Require Import VST.concurrency.compiler.Clight_self_simulation.
Require Import VST.concurrency.common.mem_equiv.
Require Import VST.concurrency.lib.pair.
Set Nested Proofs Allowed.
Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.
Import bounded_maps.


Instance C_at_external_proper Clight_g:
  Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
         (semantics.at_external (Clight_core.cl_core_sem Clight_g)).
Proof.
  intros ??? ???; subst; simpl.
  unfold Clight.at_external.
  destruct y; simpl; auto.
Qed.


  Lemma C_large_step_as_compcert_step:
    forall Clight_g code1 m1 rel_trace s1' m1''' args
      func fname fsig
      (Hfunc: func = AST.EF_external fname fsig)
      (Hexternal_step: Events.external_call
                         func (Clight.genv_genv Clight_g)
                         args m1 rel_trace Vundef m1''')
      (Hafter_ext: Clight.after_external None code1 m1''' = Some s1')
      (Hat_external1: Clight.at_external (Clight.set_mem code1 m1) =
                      Some (func, args)),
      Clight.step2 (Clight_g)
                   (Clight.set_mem code1 m1)
                   rel_trace
                   (Clight.set_mem s1' m1''').
  Proof.
    intros.
    unfold Clight.after_external in Hafter_ext.
    unfold Clight.at_external in Hat_external1.
    simpl.
    do 2 match_case in Hafter_ext.
    do 3 match_case in Hat_external1.
    (*destruct code1 eqn:Hcallstate; try discriminate.
        destruct fd eqn:Hext_func; try discriminate.*)
    inversion Hat_external1.
    inversion Hafter_ext.
    subst e0 args. simpl in *. inv Heqs0.
    eapply Clight.step_external_function; eauto.
  Qed.