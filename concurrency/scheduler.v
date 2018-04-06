Require Import compcert.common.AST.

(*THREADS*)
Module Type ThreadID.
  Parameter tid: Set.
  (*I don't like the fact that this breaks abstraction*)
  (*This is added for the hybrid machine. A better way of 
     handeling this is making the machine have multiple semantics.
    Instead of the sum of two semantics. *)
  Parameter tid2nat: tid -> nat.
  Axiom eq_tid_dec: forall (i j: tid), {i=j} + {i<>j}.
End ThreadID.

Module NatTID <: ThreadID.
  Definition tid:= nat.
  Definition tid2nat: tid -> nat:= id.
  Lemma eq_tid_dec: forall (i j: tid), {i=j} + {i<>j}.
  Proof. intros; apply Peano_dec.eq_nat_dec. Qed.
End NatTID.

(*SCHEDULERS*)
Module Type Scheduler.
  Declare Module TID: ThreadID.
  Import TID.
  Parameter schedule : Type.
  Parameter empty : schedule.
  Parameter Empty : schedule -> bool.
  Parameter schedPeek: schedule -> option tid.
  Parameter schedSkip: schedule -> schedule.
  Parameter buildSched: list tid -> schedule.
  Parameter sch_dec: forall (sch sch': schedule), {sch = sch'} + {sch <> sch'}.
  Parameter end_of_sch: forall U, U = schedSkip U <-> schedPeek U = None.
End Scheduler.

Module ListScheduler (TID:ThreadID) <: Scheduler with Module TID:= TID.
  Module TID:= TID.
  Import TID.
  Definition schedule:= list tid.
  Definition empty : schedule := nil.
  Definition schedPeek (sc:schedule):= @List.hd_error tid sc.
  Definition Empty : schedule -> bool := fun sch => if schedPeek sch then false else true.
  Definition schedSkip (sc:schedule): schedule:= @List.tl tid sc.
  Definition buildSched (ls : list tid) : schedule := ls.
  Lemma sch_dec: forall (sch sch': schedule), {sch = sch'} + {sch <> sch'}.
  Proof.
    induction sch.
    - intro sch'; destruct sch'; [left | right]; auto; apply List.nil_cons.
    - intro sch'; destruct sch'; [right|].
      + intros HH. apply (@List.nil_cons _ a sch); symmetry; assumption.
      + destruct (TID.eq_tid_dec a t).
        destruct (IHsch sch').
        * subst; left; auto.
        * subst; right. intros HH; apply n. inversion HH; auto.
        * right. intros HH; apply n. inversion HH; auto.
  Qed.
  Lemma end_of_sch: forall U, U = schedSkip U <-> schedPeek U = None.
  Proof.
    unfold schedPeek, schedSkip.
    split; simpl; intros HH; destruct U; inversion HH; try reflexivity.
    simpl in HH.
    contradict HH.
    generalize t; clear; induction U.
    - intros t HH. apply (@List.nil_cons _ t nil). symmetry; assumption.
    - intros t HH. inversion HH. apply (IHU a); assumption.
  Qed.
End ListScheduler.
