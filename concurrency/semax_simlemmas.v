Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import msl.Coqlib2.
Require Import msl.eq_dec.
Require Import msl.seplog.
Require Import veric.initial_world.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.semax_prog.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.initial_world.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.semax_ext.
Require Import veric.res_predicates.
Require Import veric.mem_lessdef.
Require Import floyd.coqlib3.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.event_semantics.
Require Import concurrency.coqlib5.
Require Import concurrency.semax_conc.
Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.
Require Import concurrency.addressFiniteMap.
Require Import concurrency.permissions.
Require Import concurrency.JuicyMachineModule.
Require Import concurrency.age_to.
Require Import concurrency.sync_preds_defs.
Require Import concurrency.sync_preds.
Require Import concurrency.join_lemmas.
Require Import concurrency.aging_lemmas.
Require Import concurrency.cl_step_lemmas.
Require Import concurrency.resource_decay_lemmas.
Require Import concurrency.resource_decay_join.
Require Import concurrency.semax_invariant.
(* Require Import concurrency.sync_preds. *)

Set Bullet Behavior "Strict Subproofs".

(** Lemmas common to both parts of the progress/preservation simulation results *)

Lemma lock_coherence_align lset Phi m b ofs :
  lock_coherence lset Phi m ->
  AMap.find (elt:=option rmap) (b, ofs) lset <> None ->
  (align_chunk Mint32 | ofs).
Proof.
  intros lock_coh find.
  specialize (lock_coh (b, ofs)).
  destruct (AMap.find (elt:=option rmap) (b, ofs) lset) as [[o|]|].
  + destruct lock_coh as [L _]; revert L; clear.
    unfold load_at; simpl.
    Transparent Mem.load.
    unfold Mem.load.
    if_tac. destruct H; auto. discriminate.
  + destruct lock_coh as [L _]; revert L; clear.
    unfold load_at; simpl.
    unfold Mem.load.
    if_tac. destruct H; auto. discriminate.
  + tauto.
Qed.

Lemma lset_valid_access m m_any tp Phi b ofs
  (compat : mem_compatible_with tp m Phi) :
  lock_coherence (lset tp) Phi m_any ->
  AMap.find (elt:=option rmap) (b, ofs) (lset tp) <> None ->
  Mem.valid_access (restrPermMap (mem_compatible_locks_ltwritable (mem_compatible_forget compat))) Mint32 b ofs Writable.
Proof.
  intros C F.
  split.
  - intros ofs' r. eapply lset_range_perm; eauto.
    unfold size_chunk in *.
    unfold lksize.LKSIZE in *.
    omega.
  - eapply lock_coherence_align; eauto.
Qed.

Lemma join_sub_to_joining {A} {J : Join A}
      {_ : Perm_alg A} {_ : Sep_alg A} {_ : Canc_alg A} {_ : Disj_alg A}
  (a b e : A) :
    join_sub e a ->
    join_sub e b ->
    joins a b ->
    identity e.
Proof.
  intros la lb ab.
  eapply join_sub_joins_identity with b; auto.
  apply (@join_sub_joins_trans _ _ _ _ _ a); auto.
Qed.

Lemma join_sub_join {A} {J : Join A}
      {PA : Perm_alg A} {SA : Sep_alg A} {_ : Canc_alg A} {DA : Disj_alg A} {CA : Cross_alg A} 
      (a b c x : A) :
  join a b c ->
  join_sub a x ->
  join_sub b x ->
  join_sub c x.
Proof.
  intros j (d, ja) (e, jb).
  destruct (@cross_split _ _ _ _ _ _ _ _ ja jb)
    as ((((ab, ae), bd), de) & ha & hd & hb & he).
  exists de.
  assert (Iab : identity ab)
    by (apply join_sub_to_joining with a b; eexists; eauto).
  pose proof join_unit1_e ae a Iab ha. subst ae. clear ha.
  pose proof join_unit1_e bd b Iab hb. subst bd. clear hb.
  apply join_comm in ja.
  apply join_comm in hd.
  destruct (join_assoc hd ja) as (c' & abc' & dec'x).
  apply join_comm in abc'.
  assert (c = c'). eapply join_eq. apply j. apply abc'. subst c'.
  apply join_comm; auto.
Qed.

Ltac join_sub_tac :=
  try
    match goal with
      c : mem_compatible_with ?tp ?m ?Phi |- _ =>
      match goal with
      | cnt1 : containsThread tp _,
        cnt2 : containsThread tp _,
        cnt3 : containsThread tp _,
        cnt4 : containsThread tp _ |- _ =>
        assert (join_sub (getThreadR cnt1) Phi) by (apply compatible_threadRes_sub, c);
        assert (join_sub (getThreadR cnt2) Phi) by (apply compatible_threadRes_sub, c);
        assert (join_sub (getThreadR cnt3) Phi) by (apply compatible_threadRes_sub, c);
        assert (join_sub (getThreadR cnt4) Phi) by (apply compatible_threadRes_sub, c)
      | cnt1 : containsThread tp _,
        cnt2 : containsThread tp _,
        cnt3 : containsThread tp _ |- _ =>
        assert (join_sub (getThreadR cnt1) Phi) by (apply compatible_threadRes_sub, c);
        assert (join_sub (getThreadR cnt2) Phi) by (apply compatible_threadRes_sub, c);
        assert (join_sub (getThreadR cnt3) Phi) by (apply compatible_threadRes_sub, c)
      | cnt1 : containsThread tp _,
        cnt2 : containsThread tp _ |- _ =>
        assert (join_sub (getThreadR cnt1) Phi) by (apply compatible_threadRes_sub, c);
        assert (join_sub (getThreadR cnt2) Phi) by (apply compatible_threadRes_sub, c)
      | cnt1 : containsThread tp _ |- _ =>
        assert (join_sub (getThreadR cnt1) Phi) by (apply compatible_threadRes_sub, c)
      end
    end;
  try
    match goal with
    | F : AMap.find (elt:=option rmap) ?loc (lset ?tp) = SSome ?phi,
          c : mem_compatible_with ?tp _ ?Phi |- _
      => assert (join_sub phi Phi) by eapply (@compatible_lockRes_sub tp loc phi F), c
    end;
  try
    match goal with
    | j : join ?a ?b ?c |- join_sub ?c _ => try apply (join_sub_join j)
    end;
  eauto using join_sub_trans, join_sub_join.
