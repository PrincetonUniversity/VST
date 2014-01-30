Require Import Bool.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import msl.Axioms.

(* A small library of lemmas on Ssreflect boolean predicates, all assuming 
   function extensionality so we can state the lemmas in rewrite form. *)

Notation Disjoint p q := ([predI p & q] = pred0).

Notation Disjoint_ext p q := ([predI p & q] =i pred0).
 
Section pred_lems.

Variable T : Type.

Lemma pred_ext (p q : pred T) : p = q <-> p =i q.
Proof. 
split=> A; first by move=> b; rewrite A.
by extensionality b; apply: (A b).
Qed.

Lemma pred_eta (p : pred T) : p = [pred x | p x].
Proof. by extensionality a. Qed.

Lemma pred_exteta (p q : pred T) :
  [pred x | p x] = [pred x | q x] <-> [pred x | p x] =i [pred x | q x].
Proof. 
split=> A; first by move=> b; rewrite A.
by f_equal; extensionality b; apply: (A b).
Qed.

Lemma predIC (p q : pred T) : [predI p & q] = [predI q & p].
Proof. by rewrite/predI; f_equal; extensionality a; rewrite andb_comm. Qed.

Lemma predIA (p q r : pred T) : 
  [predI p & [predI q & r]] = [predI [predI p & q] & r].
Proof.
rewrite/predI/in_mem/=; f_equal; extensionality a.
by rewrite/in_mem/=; case: (p a); case: (q a); case: (r a).
Qed.

Lemma predI02 (p : pred T) : [predI pred0 & p] = pred0.
Proof. by rewrite/predI/pred0; f_equal; extensionality a=> /=. Qed.

Lemma predI01 (p : pred T) : [predI p & pred0] = pred0.
Proof. by rewrite predIC predI02. Qed.

Lemma predIT2 (p : pred T) : [predI predT & p] = [pred x | p x].
Proof. by []. Qed.

Lemma predIT1 (p : pred T) : [predI p & predT] = [pred x | p x].
Proof. by rewrite predIC predIT2. Qed.

Lemma predI_sub1 (p q r : pred T) : 
  {subset p <= [predI q & r]} -> 
  {subset p <= q} /\ {subset p <= r}.
Proof.
by move=> A; split=> a B; move: (A a B); rewrite/in_mem/=; move/andP=> [].
Qed.

Lemma predI_sub2 (p q : pred T) : 
  [predI p & q] = [pred x | p x] -> {subset p <= q}.
Proof.
rewrite pred_exteta=> A a; move: (A a); rewrite/in_mem/=; move/andP.
by rewrite/in_mem/=; case: (p a)=> // [][].
Qed.

Lemma predI_sub3 (p p' q : pred T) : 
  [predI p & q] = [pred x | p x] -> 
  {subset p' <= p} -> 
  [predI p' & q] = [pred x | p' x].
Proof.
rewrite !pred_exteta=> A B a; move: (A a) (B a); rewrite/in_mem/=.
move/andP; rewrite/in_mem/=. 
case: (p a); case: (p' a); case: (q a)=> //; first by case.
by move=> _; move/(_ erefl).
Qed.

Lemma in_predI (p q : pred T) b : 
  b \in [predI p & q] = [&& b \in p & b \in q].
Proof. by rewrite/in_mem. Qed.

Lemma predUC (p q : pred T) : [predU p & q] = [predU q & p].
Proof. by rewrite/predU; f_equal; extensionality a; rewrite orb_comm. Qed.

Lemma predUA (p q r : pred T) : 
  [predU p & [predU q & r]] = [predU [predU p & q] & r].
Proof.
rewrite/predU/in_mem/=; f_equal; extensionality a.
by rewrite/in_mem/=; case: (p a); case: (q a); case: (r a).
Qed.

Lemma predU02 (p : pred T) : [predU pred0 & p] = [pred x | p x].
Proof. by rewrite/predU/pred0; f_equal; extensionality a=> /=. Qed.

Lemma predU01 (p : pred T) : [predU p & pred0] = [pred x | p x].
Proof. by rewrite predUC predU02. Qed.

Lemma predUT2 (p : pred T) : [predU predT & p] = predT.
Proof. by []. Qed.

Lemma predUT1 (p : pred T) : [predU p & predT] = predT.
Proof. by rewrite predUC predUT2. Qed.

Lemma in_predU (p q : pred T) b : 
  b \in [predU p & q] = [|| b \in p | b \in q].
Proof. by rewrite/in_mem. Qed.

Lemma predD02 (p : pred T) : [predD pred0 & p] = pred0.
Proof. 
rewrite/predD/pred0; f_equal; extensionality a=>/=.
by rewrite/in_mem/=; rewrite andb_false_r.
Qed.

Lemma predD01 (p : pred T) : [predD p & pred0] = [pred x | p x].
Proof. by []. Qed.

Lemma predDT2 (p : pred T) : [predD predT & p] = [pred x | ~~p x].
Proof. 
rewrite/predD/predT; f_equal; extensionality a=>/=.
by rewrite/in_mem/=; rewrite andb_true_r.
Qed.

Lemma predDT1 (p : pred T) : [predD p & predT] = pred0.
Proof. by []. Qed.

Lemma predDI1 (p q : pred T) : [predI [predD p & q] & q] = pred0.
Proof.
rewrite/predI/predD/pred0/=; f_equal; extensionality a.
by rewrite/in_mem/= andb_comm andb_assoc andb_negb_r.
Qed.

Lemma predDI2 (p q : pred T) : [predI q & [predD p & q]] = pred0.
Proof. by rewrite predIC predDI1. Qed.

Lemma predDU1 (p q : pred T) : [predU [predD p & q] & q] = [predU p & q].
Proof.
rewrite/predU/predD/=; f_equal; extensionality a.
by rewrite/in_mem/=; case: (p a); case: (q a).
Qed.

Lemma predDU2 (p q : pred T) : [predU q & [predD p & q]] = [predU p & q].
Proof. by rewrite (predUC q) predDU1. Qed.

Lemma predDidem (p q : pred T) : 
  [predD [predD p & q] & q] = [predD p & q].
Proof.
rewrite/predD; f_equal; extensionality a=>/=.
by rewrite/in_mem/= -{3}(andb_diag (~~ q a)) andb_assoc.
Qed.

Lemma in_predD (p q : pred T) b : 
  b \in [predD p & q] = [&& b \in p & b \notin q].
Proof. by rewrite/in_mem/=/in_mem/= andb_comm. Qed.

Lemma DisjointIn1 (p q : pred T) : 
  [predD p & q]=[pred x | p x] -> Disjoint p q.
Proof.
move=> A; change ([predI [pred x | p x] & q] = pred0).
by rewrite -A predDI1.
Qed.

Lemma DisjointInD (p q : pred T) : Disjoint [predD p & q] q.
Proof. by apply: DisjointIn1; rewrite predDidem. Qed.

Lemma DisjointInE (p q : pred T) : 
  Disjoint p q <-> Disjoint_ext p q.
Proof. 
rewrite/predI/pred0/=; split=> A; f_equal; first by rewrite A.
by extensionality a; apply: (A a).
Qed.

Lemma DisjointInI (p q : pred T) : Disjoint [predI p & q] [pred a | ~~ q a].
Proof. 
rewrite DisjointInE=> a; rewrite/predI/pred0/=/in_mem/=.
by case: (p a); case: (q a)=> //.
Qed.

Lemma DisjointC (p q : pred T) : Disjoint p q <-> Disjoint q p.
Proof. by split=> A; rewrite predIC. Qed.

Lemma DisjointP (p q : pred T) : Disjoint p q <-> forall a, ~ p a \/ ~ q a.
Proof.
rewrite DisjointInE; split;
move=> A a; move: (A a); rewrite in_predI /in_mem/=.
by rewrite andb_false_iff; case=> ->; [left|right].
rewrite andb_false_iff; case=> B; [left|right].
by move: B; case: (p a).
by move: B; case: (q a).
Qed.

Lemma DisjointInU (p q r : pred T) :
  Disjoint p q -> Disjoint p r -> Disjoint p [predU q & r].
Proof.
move/DisjointP=> A; move/DisjointP=> B; apply/DisjointP=> a.
move: (A a) (B a)=> /=; rewrite/in_mem/=.
by case: (p a); case: (q a); case: (r a).
Qed.

Lemma Disjoint_incr (p q r : pred T) : 
  Disjoint p q -> 
  Disjoint p [predD r & q] -> 
  Disjoint p r.
Proof.
move/DisjointP=> A; move/DisjointP=> B; rewrite DisjointP=> a.
move: (A a) (B a); case; first by left.
move=> C; case=> D; first by left.
move: C D; rewrite/predD/=/in_mem/=. 
by case: (q a)=> //; case: (r a)=> //; right.
Qed.

Lemma Disjoint_sub1 (p q q' : pred T) :
  Disjoint p q -> 
  {subset q' <= q} -> 
  Disjoint p q'.
Proof.
move/DisjointP=> A B; rewrite DisjointP=> a; move: (A a) (B a).
rewrite/in_mem/=; case: (p a); case: (q a); case: (q' a);
try solve[by left|by right|by case].
by move=> _; elim=> //; left.
Qed.

Lemma Disjoint_sub2 (p p' q : pred T) :
  Disjoint p q -> 
  {subset p' <= p} -> 
  Disjoint p' q.
Proof.
move/DisjointP=> A B; rewrite DisjointP=> a; move: (A a) (B a).
rewrite/in_mem/=; case: (p a); case: (q a); case: (p' a);
try solve[by left|by right|by case].
by move=> _; elim=> //; left.
Qed.

Lemma in_pred0 (b : T) : b \in pred0 = false.
Proof. by rewrite/pred0/in_mem. Qed.

Lemma subset_trans' (p q r : pred T) : 
  {subset p <= q} -> {subset q <= r} -> {subset p <= r}.
Proof. by move=> A B b C; apply: B; apply: A. Qed.

Lemma subsetI (p q r : pred T) :
  {subset p <= q} -> {subset p <= r} -> {subset p <= [predI q & r]}.
Proof.
move=> A B b C; apply/andP=> /=; split; first by apply: A.
by apply: B.
Qed.

End pred_lems.
