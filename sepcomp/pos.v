Require Import ssreflect ssrbool ssrnat fintype.
Set Implicit Arguments.

Record pos := mkPos { n :> nat ; N_pos : (0 < n)%coq_nat }.

Lemma is_pos (p : pos) : 0 < p.
Proof. by case: p=> m pf; apply/ltP. Qed.

Definition i0 (p : pos) : 'I_p := Ordinal (is_pos p).
