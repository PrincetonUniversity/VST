Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* I'm probably missing these in the ssreflect libraries ... *)

Section pred_lems.

Context {T} {pTy : predType T} (p q r : pTy).

Lemma predI0 : [predI p & pred0] =i pred0.
Proof. by rewrite/eq_mem/=/in_mem/=/andb=> x; case: (x \in p). Qed.

Lemma predIT : [predI predT & p] =i p.
Proof. by rewrite/eq_mem/=/in_mem/=/andb/in_mem => x. Qed.

Lemma predIC : [predI p & q] =i [predI q & p].
Proof. 
by rewrite/eq_mem/in_mem/=/andb=> x; case: (x \in p); case: (x \in q).
Qed.

Lemma in_predI b : b \in [predI p & q] = [&& b \in p & b \in q].
Proof. by rewrite/in_mem. Qed.

Lemma in_pred0 (b : T) : b \in pred0 = false.
Proof. by rewrite/pred0/in_mem. Qed.

Lemma eq_mem_trans : p =i q -> q =i r -> p =i r.
Proof. 
by rewrite/eq_mem/in_mem/= => H H2 x; rewrite -(H2 x) (H x). 
Qed.

Lemma my_subset_trans : 
  {subset p <= q} -> {subset q <= r} -> {subset p <= r}.
Proof. by move=> A B b C; apply: B; apply: A. Qed.

Lemma subsetI :
  {subset p <= q} -> {subset p <= r} -> {subset p <= [predI q & r]}.
Proof.
move=> A B b C; apply/andP=> /=; split; first by apply: A.
by apply: B.
Qed.

End pred_lems.
