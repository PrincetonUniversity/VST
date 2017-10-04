Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.semantics_lemmas.

(** * Cooperating Interaction Semantics *)

(** Cooperating semantics impose additional constraints; in particular, they
   specialize interaction semantics to CompCert memories and require that the
   memories produced by coresteps are [forward] wrt. the initial memory. See
   [core/mem_lemmas.v] for the defn. of [mem_forward]. *)

Require Import VST.compcert.common.Memory.
Require Import VST.sepcomp.mem_lemmas.
Record CoopCoreSem {G C} :=
  { coopsem :> CoreSemantics G C mem
  ; corestep_fwd :
      forall g c m c' m' (CS: corestep coopsem g c m c' m'),
      mem_forward m m'
  ; corestep_rdonly:
      forall g c m c' m' (CS: corestep coopsem g c m c' m') b,
      Mem.valid_block m b -> readonly m b m'}.

Implicit Arguments CoopCoreSem [].


Definition MemSem2CoopCoreSem {G C} (s:@MemSem G C): @CoopCoreSem G C.
Proof.
eapply Build_CoopCoreSem with (coopsem := s).
apply semantics_lemmas.corestep_fwd.
apply semantics_lemmas.corestep_rdonly.
Defined.

Section CoopCoreSemLemmas.
Context {G C: Type}.
Variable coopsem: CoopCoreSem G C.

Lemma corestepN_fwd: forall ge c m c' m' n,
  corestepN coopsem ge n c m c' m' ->
  mem_forward m m'.
Proof.
intros until n; revert c m.
induction n; simpl; auto.
inversion 1; apply mem_forward_refl; auto.
intros c m [c2 [m2 [? ?]]].
apply mem_forward_trans with (m2 := m2).
apply corestep_fwd in H; auto.
eapply IHn; eauto.
Qed.

Lemma corestep_star_fwd: forall g c m c' m'
  (CS:corestep_star coopsem g c m c' m'),
  mem_forward m m'.
Proof.
  intros. destruct CS.
  eapply corestepN_fwd.
  apply H.
Qed.

Lemma corestep_plus_fwd: forall g c m c' m'
  (CS:corestep_plus coopsem g c m c' m'),
  mem_forward m m'.
Proof.
   intros. destruct CS.
   eapply corestepN_fwd.
   apply H.
Qed.

Lemma corestepN_rdonly: forall ge c m c' m' n,
  corestepN coopsem ge n c m c' m' -> forall b
  (VB: Mem.valid_block m b), readonly m b m'.
Proof.
intros until n; revert c m.
induction n; simpl; auto.
inversion 1; intros. apply readonly_refl.
intros c m [c2 [m2 [? ?]]].
intros. apply readonly_trans with (m2 := m2).
eapply corestep_rdonly; eauto.
eapply IHn; eauto. eapply corestep_fwd; eauto.
Qed.

Lemma corestep_plus_rdonly ge c m c' m'
  (CS: corestep_plus coopsem ge c m c' m') b
  (VB: Mem.valid_block m b): readonly m b m'.
Proof.
  destruct CS. eapply corestepN_rdonly; eauto.
Qed.

Lemma corestep_star_rdonly ge c m c' m'
  (CS: corestep_star coopsem ge c m c' m') b
  (VB: Mem.valid_block m b): readonly m b m'.
Proof.
  destruct CS. eapply corestepN_rdonly; eauto.
Qed.

End CoopCoreSemLemmas.
