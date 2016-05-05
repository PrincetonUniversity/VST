Require Import compcert.common.AST.

(*THREADS*)
Module Type ThreadID.
  Parameter tid: Set.
  Axiom eq_tid_dec: forall (i j: tid), {i=j} + {i<>j}.
End ThreadID.

Module NatTID <: ThreadID.
  Definition tid:= nat.
  Lemma eq_tid_dec: forall (i j: tid), {i=j} + {i<>j}.
  Proof. intros; apply Peano_dec.eq_nat_dec. Qed.
End NatTID.

(*SCHEDULERS*)
Module Type Scheduler.
  Declare Module TID: ThreadID.
  Import TID.
  Parameter schedule : Type.
  Parameter empty : schedule.
  Parameter schedPeek: schedule -> option tid.
  Parameter schedSkip: schedule -> schedule.
  Parameter buildSched: list tid -> schedule.
End Scheduler.

Module ListScheduler (TID:ThreadID) <: Scheduler with Module TID:= TID.
  Module TID:= TID.
  Import TID.
  Definition schedule:= list tid.
  Definition empty : schedule := nil.
  Definition schedPeek (sc:schedule):= @List.hd_error tid sc.
  Definition schedSkip (sc:schedule): schedule:= @List.tl tid sc.
  Definition buildSched (ls : list tid) : schedule := ls.
End ListScheduler.