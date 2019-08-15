
(** Erasure Safety *)

(** Derive safety from the simulations.
    Erasure proven in [erasure_proof.v] and [erasure_signature.v]
    is stated as a simulation. Here we prove that the simulation
    implies safety.
 *)

(** *Imports*)

(* This file uses Proof Irrelevance: 
   forall (P : Prop) (p1 p2 : P), p1 = p2. *)
Require Import ProofIrrelevance.

(* CompCert imports*)
Require Import compcert.common.Memory.

(* VST imports *)
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(* Concurrency Imports *)
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.juicy.juicy_machine. Import Concur.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.common.permissions.
(*Erasure simulation*)
Require Import VST.concurrency.juicy.erasure_signature.
Require Import VST.concurrency.juicy.erasure_proof.
Require Import VST.concurrency.juicy.Clight_safety.
Import addressFiniteMap.

(*SSReflect*)
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype seq.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Require Import VST.concurrency.common.ssromega. (*omega in ssrnat *)
From mathcomp.ssreflect Require Import ssreflect seq.

(*The simulations*)
(* Require Import VST.concurrency.common.machine_simulation.*)

Set Bullet Behavior "Strict Subproofs".

Module ErasureSafety.

  Module ErasureProof := erasure_proof.Parching.
  Module Erasure := ErasureFnctr ErasureProof.
  Import ErasureProof.
  Import Erasure.

  Section ErasureSafety.

  Context (initU: HybridMachineSig.schedule).
  Context (init_rmap : @res JR).
  Context (init_pmap : @res DR).
  Context (init_rmap_perm:  match_rmap_perm init_rmap init_pmap).

  (*Definition local_erasure:= erasure initU init_rmap init_pmap init_rmap_perm.*)
  Definition step_diagram:= ErasureProof.core_diagram.

  Import JuicyMachineModule.THE_JUICY_MACHINE.
  Import ClightMachine.Clight_newMachine.DMS.

  Existing Instance DMS.

  Lemma erasure_safety': forall n ge sch js jtr ds dtr m,
      ErasureProof.match_st ge js ds ->
      DryHybridMachine.invariant ds ->
    jm_csafe (sch, jtr, js) m n ->
    HybridMachineSig.HybridCoarseMachine.csafe (sch, dtr, ds) m n.
  Proof.
    induction n.
    intros. constructor.
    intros. inversion H1.
    - constructor; simpl. unfold HybridMachineSig.halted_machine; simpl.
      unfold JuicyMachine.halted_machine in H2; simpl in H2.
      change JuicyMachine.schedPeek with
      HybridMachineSig.schedPeek in H2.
      destruct ( HybridMachineSig.schedPeek sch ) eqn:AA;
      inversion H; auto.
    - { simpl in Hstep.
        unfold JuicyMachine.MachStep in Hstep; simpl in Hstep.
        assert (step_diagram:=step_diagram).
        specialize (step_diagram ge m initU sch sch (Some init_rmap) (Some init_pmap)).
        specialize (step_diagram ds dtr js tp' jtr tr' m').
        unfold corestep in step_diagram; simpl in step_diagram.
        unfold JuicyMachine.MachStep in step_diagram; simpl in step_diagram.
        eapply step_diagram in Hstep; try eassumption.
        destruct Hstep as [ds' [dinv' [MATCH' [dtr' stp']]]].
        destruct Hsafe as [[? [Hphi Hext]] Hsafe].
        specialize (Hsafe _ Hphi [:: Some (ghost_PCM.ext_ref tt, NoneP)])
          as (? & ? & ? & ? & Hr & ? & Hsafe); auto.
        { apply join_sub_refl. }
        eapply MTCH_tp_update in MATCH'; eauto.
        eapply IHn in Hsafe; eauto.
        econstructor 3; eauto.
        apply stp'. }
    - { simpl in Hstep.
        unfold JuicyMachine.MachStep in Hstep; simpl in Hstep.
        assert (step_diagram:=step_diagram).
        specialize (step_diagram ge m initU sch (HybridMachineSig.schedSkip sch) (Some init_rmap) (Some init_pmap)).
        specialize (step_diagram ds dtr js tp' jtr tr' m').
        unfold corestep in step_diagram; simpl in step_diagram.
        unfold JuicyMachine.MachStep in step_diagram; simpl in step_diagram.
        eapply step_diagram in Hstep; try eassumption.
        destruct Hstep as [ds' [dinv' [MATCH' [dtr' stp']]]].
        econstructor 4; eauto.
        { apply stp'. }
        intro U''; specialize (Hsafe U'').
        destruct Hsafe as [[? [Hphi Hext]] Hsafe].
        specialize (Hsafe _ Hphi [:: Some (ghost_PCM.ext_ref tt, NoneP)])
          as (? & ? & ? & ? & Hr & ? & Hsafe); auto.
        { apply join_sub_refl. }
        eapply MTCH_tp_update in MATCH'; eauto. }
Qed.


  Theorem erasure_safety: forall ge cd j js ds m n,
      Erasure.match_state ge cd j js m ds m ->
      jm_csafe js m n ->
      HybridMachineSig.HybridCoarseMachine.csafe ds m n.
  Proof.
    intros ? ? ? ? ? ? ? MATCH jsafe.
    inversion MATCH. subst.
    eapply erasure_safety'; eauto.
  Qed.

  (*there is something weird about this theorem.*)
  (*The injection is trivial... but it shouldn't*)
(*  Theorem initial_safety:
    forall genv (U : HybridMachineSig.schedule) (js : jstate genv)
      (vals : seq Values.val) m
      (rmap0 : rmap) (pmap : access_map * access_map) main h,
      match_rmap_perm rmap0 pmap ->
      no_locks_perm rmap0 ->
      initial_core (JMachineSem U (Some rmap0)) h
         m (U, [::], js) main vals  ->
      exists (ds : dstate genv),
        initial_core (ClightMachineSem U (Some pmap)) h
                     m (U, [::], ds) main vals /\
        invariant ds /\ match_st genv js ds.
  Proof.
    intros ? ? ? ? ? ? ? ? ? mtch_perms no_locks init.
    destruct (init_diagram genv (fun _ => None) U js vals m rmap0 pmap main h)
    as [ds [dinit [dinv MTCH]]]; eauto.
    unfold init_inj_ok; intros b b' ofs H. inversion H.
  Qed.*)

  End ErasureSafety.

End ErasureSafety.

Require Import VST.concurrency.juicy.semax_to_juicy_machine.

Lemma no_locks_no_locks_perm : forall r, Parching.no_locks_perm r <-> initial_world.no_locks r.
Proof.
  unfold Parching.no_locks_perm, initial_world.no_locks, perm_of_res_lock; split; intros.
  - destruct addr as (b, ofs); specialize (H b ofs).
    destruct (r @ (b, ofs)); try discriminate.
    destruct (perm_of_sh (Share.glb Share.Rsh sh0)) eqn: Hsh.
    destruct k; discriminate.
    { contradiction r0.
      apply perm_of_empty_inv in Hsh as ->; auto. }
  - specialize (H (b, ofs)).
    destruct (r @ (b, ofs)); auto.
    specialize (H sh r0).
    destruct k; auto. specialize (H n i p).  contradiction; auto.
Qed.

(* unused *)
Lemma juice2Perm_match : forall m r, access_cohere' m r ->
  Parching.match_rmap_perm r (juice2Perm r m, empty_map).
Proof.
  split; auto; simpl.
  intros; apply juic2Perm_correct; auto.
Qed.

Section DrySafety.
(* combining results from semax_to_juicy_machine and erasure_proof *)

  Variable (CPROOF : CSL_proof).

  Instance Sem : Semantics := ClightSemanticsForMachines.Clight_newSem (Clight.globalenv CPROOF.(CSL_prog)).
  Definition ge := Clight.globalenv CPROOF.(CSL_prog).
  Instance DTP : threadPool.ThreadPool.ThreadPool := Parching.DTP ge.
  Instance DMS : HybridMachineSig.MachineSig := Parching.DMS ge.
  Definition init_mem := proj1_sig (init_mem CPROOF).
  Definition init_rmap n := m_phi (initial_jm CPROOF n).

  Lemma init_match n : Parching.match_rmap_perm (init_rmap n) (getCurPerm init_mem, empty_map).
  Proof.
    split; auto; simpl.
    unfold init_rmap, initial_jm, spr.
    destruct (semax_prog.semax_prog_rule' _ _ _ _ _ _ _ _) as (? & ? & ? & s); simpl.
    destruct (s n tt) as (jm & ? & ? & ? & ? & ? & ?); simpl.
    destruct jm; simpl in *; subst; intros.
    rewrite <- (JMaccess (b, ofs)).
    unfold access_at, PMap.get; simpl.
    rewrite PTree.gmap1.
    fold init_mem; destruct ((snd (Mem.mem_access init_mem)) ! b); auto.
  Qed.

  Lemma init_no_locks n : Parching.no_locks_perm (init_rmap n).
  Proof.
    apply no_locks_no_locks_perm.
    unfold init_rmap, initial_jm, spr.
    destruct (semax_prog.semax_prog_rule' _ _ _ _ _ _ _ _) as (? & ? & ? & s); simpl.
    destruct (s n tt) as (jm & ? & ? & ? & ? & ? & ?); auto.
  Qed.


  (**  Theorem to export.
       Explanation: 
       
   *)
  Theorem dry_safety_initial_state (sch : HybridMachineSig.schedule) (n : nat) :
    HybridMachineSig.HybridCoarseMachine.csafe
      (sch, [::],
      DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm init_mem)
        (initial_corestate CPROOF)) init_mem n.
  Proof.
    eapply (ErasureSafety.erasure_safety sch (init_rmap n)
      (juice2Perm (init_rmap n) init_mem, empty_map)) with (cd := tt)(j := fun _ => None),
      (* Note that any injection will work here. *)
      safety_initial_state.
    constructor.
    { apply dry_machine_lemmas.ThreadPoolWF.initial_invariant0. }
    apply Parching.MTCH_initial with (pmap := (getCurPerm init_mem, empty_map)).
    - apply init_match.
    - apply init_no_locks.
  Qed.

  Context {SW : spawn_wrapper CPROOF}.

  Notation ClightSem:= ClightSemanticsForMachines.ClightSem.
  Theorem Clight_initial_safe (sch : HybridMachineSig.schedule) (n : nat) :
    HybridMachineSig.HybridCoarseMachine.csafe
      (Sem := ClightSem ge)
      (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
      (machineSig:= HybridMachine.DryHybridMachine.DryHybridMachineSig)
      (sch, nil,
       DryHybridMachine.initial_machine(Sem := ClightSem ge)
                                       (permissions.getCurPerm init_mem)
                                       (initial_Clight_state CPROOF)) init_mem n.
  Proof.
    apply Clight_new_Clight_safety; auto.
    apply dry_safety_initial_state.
  Qed.

  (*Print Assumptions Clight_initial_safe.*)
End DrySafety.


