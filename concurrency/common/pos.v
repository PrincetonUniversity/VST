From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool ssrnat eqtype fintype.
Set Implicit Arguments.

Require Import compcert.lib.Axioms.

Record pos := mkPos { n :> nat ; N_pos : (0 < n)%coq_nat }.

Lemma is_pos (p : pos) : 0 < p.
Proof. by case: p=> m pf; apply/ltP. Qed.

Definition i0 (p : pos) : 'I_p := Ordinal (is_pos p).

Require Import Omega.
Lemma is_pos_incr (n : nat) : (0 < n.+1)%coq_nat.
Proof. omega. Qed.

Definition pos_incr (p : pos) : pos := mkPos (is_pos_incr p).

Lemma pos_incr_lt (p : pos) : p < pos_incr p.
Proof. by []. Qed.

Definition ordinal_pos_incr (p : pos) : 'I_(pos_incr p) := Ordinal (pos_incr_lt p).

Section PosEqType.

Definition pos_eq := [rel u v : pos | n u == n v].

Lemma pos_eqP : Equality.axiom pos_eq.
Proof.
move=> /=; case=> n0 pf0; case=> n1 pf1.
case Heq: (n0 == n1).
{ move: (eqP Heq) pf0 pf1=> -> pf0 pf1.
   have ->: pf0 = pf1 by apply: proof_irr.
   by apply: ReflectT.
}
{ apply: ReflectF; case=> Heq1.
   by move: Heq; rewrite Heq1; move/eqP; apply.
}
Qed.

Definition pos_eqMixin := EqMixin pos_eqP.
Canonical pos_eqType := Eval hnf in EqType pos pos_eqMixin.

Lemma pos_eqE : pos_eq = eq_op :> rel _. Proof. by []. Qed.

End PosEqType.

