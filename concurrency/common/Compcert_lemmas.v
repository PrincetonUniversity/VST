
Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Lemma list_inject_weaken: 
  forall j lev1 lev2,
    Events.list_inject_mem_effect_strong j lev1 lev2 ->
    Events.list_inject_mem_effect j lev1 lev2.
Proof.
  intros. inversion H; subst; constructor.
Admitted.

Lemma list_inject_mem_effect_cat:
  forall j l1 l1' l2 l2',
    Events.list_inject_mem_effect j l1 l2 ->
    Events.list_inject_mem_effect j l1' l2' ->
    Events.list_inject_mem_effect j (l1++l1') (l2++l2').
Proof.
Admitted.