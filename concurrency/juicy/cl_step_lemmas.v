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
Lemma mem_step_decay:
  forall m m', semantics.mem_step m m' -> decay m m'.
Proof.
intros.
induction H.
eapply storebytes_decay; eauto.
eapply alloc_decay; eauto.
eapply free_list_decay; eauto.
 apply decay_trans with m''; auto.
 apply semantics_lemmas.mem_step_nextblock' in H.
 apply semantics_lemmas.mem_step_nextblock' in H0.
 pose proof (Pos.le_trans _ _ _ H H0).
 intros.
 red in H2|-*.
  unfold Plt in *.
  eapply Pos.lt_le_trans; eauto.
Qed.

Lemma cl_step_decay ge c m c' m' : @cl_step ge c m c' m' -> @decay m m'.
intros.
apply (msem_decay (CLN_memsem ge)) in H.
auto.
Qed.

Lemma cl_step_unchanged_on ge c m c' m' b ofs :
  @cl_step ge c m c' m' ->
  Mem.valid_block m b ->
  ~ Mem.perm m b ofs Cur Writable ->
  Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m)) =
  Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m')).
Proof.
intros.
apply (CLN_memsem ge) in H.
eapply semantics_lemmas.mem_step_obeys_cur_write in H; try eassumption.
Qed.

