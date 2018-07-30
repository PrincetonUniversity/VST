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
