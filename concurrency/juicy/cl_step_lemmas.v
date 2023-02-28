Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory. Import Memory.
Require Import compcert.common.Memdata. Import Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.seplog.
Require Import VST.veric.Clight_core.
Require Import VST.veric.coqlib4.
Require Import VST.sepcomp.Address.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.concurrency.common.permissions.

Set Bullet Behavior "Strict Subproofs".

(** * Results on cl_step *)

Lemma cl_step_decay ge c m c' m' : @cl_step ge c m c' m' -> @decay m m'.
Proof.
  intros.
  eapply (msem_decay (CLC_memsem ge)), H.
Qed.

Lemma cl_step_unchanged_on ge c m c' m' b ofs :
  @cl_step ge c m c' m' ->
  Mem.valid_block m b ->
  ~ Mem.perm m b ofs Cur Writable ->
  Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
  Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m')).
Proof.
  intros.
  apply (semantics.corestep_mem (CLC_memsem ge)) in H.
  apply semantics_lemmas.mem_step_obeys_cur_write; auto.
Qed.
