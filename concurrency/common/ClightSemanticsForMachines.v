(* Clight SEmantics for Machines*)

(*
  We define event semantics for 
  - Clight_new: the core semantics defined by VST
  - Clightcore: the core semantics derived from 
    CompCert's Clight
*)

Require Import compcert.common.Memory.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

Require Import List. Import ListNotations.

(* The concurrent machinery*)
(*Require Import VST.concurrency.common.core_semantics.*)
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.concurrency.memsem_lemmas.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.dry_machine_lemmas.

Import Ctypes. 
Require Import compcert.cfrontend.Clight.
Import Cop.
Arguments sizeof {env} !t / .

(*Semantics*)
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop.
Require Import VST.sepcomp.event_semantics.
Require Import VST.veric.Clight_evsem.

Set Bullet Behavior "Strict Subproofs".

Lemma at_external_SEM_eq:
   forall ge c m, semantics.at_external (CLC_evsem ge) c m =
   match c with
   | Callstate (External ef _ _ _) args _ => 
       if ef_inline ef then None else Some (ef, args)
   | _ => None
 end.
Proof. auto. Qed.

#[export] Instance ClightSem ge : Semantics :=
  { semG := G; semC := C; semSem := CLC_evsem ge; the_ge := ge }.

Lemma CLC_step_decay: forall g c m tr c' m',
      event_semantics.ev_step (CLC_evsem g) c m tr c' m' ->
      decay m m'.
Proof.
intros.
pose proof (msem_decay (CLC_memsem g) c m c' m').
apply H0. clear H0.
simpl in *.
apply CLC_evstep_ax1 in H.
auto.
Qed.

#[export] Instance ClightAxioms ge : @CoreLanguage.SemAxioms (ClightSem ge).
Proof.
  constructor.
  - intros.
    apply mem_step_obeys_cur_write; auto.
    eapply corestep_mem; eauto.
  - intros.
    apply ev_step_ax2 in H as [].
    eapply CLC_step_decay; simpl in *; eauto.
  - intros.
    apply mem_forward_nextblock, mem_step_forward.
    eapply corestep_mem; eauto.
  - intros; simpl.
    destruct q; auto.
  - intros.
    destruct Hstep as (? & ->); done. (* Do we need initial_core to allocate the arguments? *)
(*    inv Hstep.
    inv H; simpl.
    apply mem_step_obeys_cur_write; auto.
  (* apply memsem_lemmas.mem_step_refl. *)
    eapply mem_step_alloc; eauto. *)
  - intros.
    destruct H as (? & ->).
    apply strong_decay_refl.
(*    inv H.
    inv H0; simpl.
    split; intros.
    + (*contradiction. *)
      eapply juicy_mem.fullempty_after_alloc in H8.
      admit. 
      (* destruct H8; [right|left].
     
       should be able to prove that 
                1. b = Mem.nextblock m
                which satisfies the goal at all offsets.
              *)
        
    + auto. inv H8.
      simpl.
      Transparent Mem.alloc.
      unfold Mem.alloc; simpl.
      admit.
      
  - intros.
    inv H.
    inv H0; simpl.
    erewrite (Mem.nextblock_alloc _ _ _ _ _ H8).
    xomega.*)
  - intros.
    destruct H as (? & ->); done.
Qed.
