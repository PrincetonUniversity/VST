Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop.
Require Import VST.veric.semax.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.coqlib4.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.juicy.semax_conc.
Require Import VST.concurrency.juicy.juicy_machine.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.semantics.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.common.lksize.
Import threadPool.

Set Bullet Behavior "Strict Subproofs".

(** * Results related to resource_decay *)

(* todo: maybe remove one of those lemmas *)

Lemma isSome_find_map addr f lset :
  ssrbool.isSome (AMap.find (elt:=option rmap) addr (AMap.map f lset)) =
  ssrbool.isSome (AMap.find (elt:=option rmap) addr lset).
Proof.
  match goal with |- _ ?a = _ ?b => destruct a eqn:E; destruct b eqn:F end; try reflexivity.
  - apply AMap_find_map_inv in E; destruct E as [x []]; congruence.
  - rewrite (AMap_find_map _ _ _ o F) in E. discriminate.
Qed.

Lemma interval_adr_range b start length i :
  Intv.In i (start, start + length)%Z <->
  adr_range (b, start) length (b, i).
Proof.
  compute; intuition.
Qed.

(*Lemma join_YES_l {r1 r2 r3 sh1 sh1' k pp} :
  sepalg.join r1 r2 r3 ->
  r1 = YES sh1 sh1' k pp ->
  exists sh3 sh3',
    r3 = YES sh3 sh3' k pp.
Proof.
  intros J; inversion J; intros.
  all:try congruence.
  all:do 2 eexists; f_equal; try congruence.
Qed.*)


Local Open Scope nat_scope.

(** * Results related to machine predicates *)

(* Instantiation of modules *)
Import THE_JUICY_MACHINE.
Import Concur OrdinalPool ThreadPool.

Section Machine.

Context (ge : genv).

Lemma fst_snd0: forall loc: address,
   (fst loc, (snd loc + 0)%Z) = loc.
Proof.
intros.
 pose proof (LKSIZE_pos). destruct loc; simpl; f_equal; auto. lia.
Qed.

(*
Lemma same_locks_juicyLocks_in_lockSet phi phi' lset :
  same_locks phi phi' ->
  juicyLocks_in_lockSet lset phi ->
  juicyLocks_in_lockSet lset phi'.
Proof.
  intros SL IN loc E.
  apply (IN loc); intros. specialize (E _ H).
  destruct E as [sh [psh [P ?]]].
  specialize (SL (fst loc, (snd loc + i)%Z) LKSIZE i).  destruct SL as [_ SL].
  rewrite H0 in SL. spec SL; [split; auto|].
  destruct (phi @ (fst loc, (snd loc + i)%Z)); try destruct k; try contradiction.
  destruct SL; subst. do 3 eexists; reflexivity.
Qed.

Lemma lockSet_Writable_lockSet_block_bound m lset  :
  lockSet_Writable lset m ->
  lockSet_block_bound lset (Mem.nextblock m).
Proof.
  simpl; intros LW.
  intros (b, ofs) IN; simpl.
  specialize (LW b ofs).
  simpl in *.
  destruct (AMap.find (elt:=option rmap) (b, ofs) lset). 2:inversion IN.
  specialize (LW eq_refl).
  cut (~ ~ (b < Mem.nextblock m)%positive). zify. lia. intros L.
  specialize (LW ofs).
  assert (Intv.In ofs (ofs, (ofs + LKSIZE)%Z)).
  { split; simpl; pose proof LKSIZE_pos; lia. }
  autospec LW.
  rewrite (Mem.nextblock_noaccess _ _ ofs Max L) in LW.
  inversion LW.
Qed.*)

Lemma lset_range_perm m (tp : jstate ge) b ofs
  (compat : mem_compatible tp m)
  (Efind : AMap.find (elt:=option rmap) (b, ofs) (lset tp) <> None) :
  Mem.range_perm
    (restrPermMap (mem_compatible_locks_ltwritable compat))
    b ofs (ofs + LKSIZE) Cur Writable.
Proof.
  unfold Mem.range_perm in *.
  intros ofs0 range.
  unfold Mem.perm in *.
  pose proof restrPermMap_Cur as R.
  unfold permission_at in *.
  rewrite R.
  erewrite lockSet_spec_2.
  + constructor.
  + eauto.
  + simpl in *.
    unfold OrdinalPool.lockRes in *.
    unfold OrdinalPool.lockGuts in *.
    change lock_info with (option rmap).
    destruct (AMap.find (elt:=option rmap) (b, ofs) (lset tp)).
    * reflexivity.
    * tauto.
Qed.

Lemma getThreadC_fun i (tp : jstate ge) cnti cnti' x y :
  @getThreadC _ _ _ i tp cnti = x ->
  @getThreadC _ _ _ i tp cnti' = y ->
  x = y.
Proof.
  intros <- <-.
  unfold getThreadC, containsThread in *.
  repeat f_equal.
  apply proof_irr.
Qed.

Lemma getThreadR_fun i (tp : jstate ge) cnti cnti' x y :
  @getThreadR _ _ _ i tp cnti = x ->
  @getThreadR _ _ _ i tp cnti' = y ->
  x = y.
Proof.
  intros <- <-.
  unfold getThreadR, containsThread in *.
  repeat f_equal.
  apply proof_irr.
Qed.

Definition same_except_cur (m m' : Mem.mem) :=
  Mem.mem_contents m = Mem.mem_contents m' /\
  max_access_at m = max_access_at m' /\
  Mem.nextblock m = Mem.nextblock m'.

Lemma mem_cohere_same_except_cur m m' phi :
  same_except_cur m m' ->
  mem_cohere' m phi ->
  mem_cohere' m' phi.
Proof.
  intros (ECo & EMa & EN) [Co Ma N]; constructor.
  - hnf in *.
    unfold juicy_mem.contents_cohere, contents_at in *.
    rewrite <-ECo. auto.
  - unfold max_access_cohere, juicy_mem.max_access_cohere in *. intros loc.
    apply equal_f with (x := loc) in EMa.
    rewrite <-EMa.
    apply Ma.
  - hnf in *. rewrite <-EN.
    auto.
Qed.

Lemma mem_compatible_with_same_except_cur (tp : jstate ge) m m' phi :
  same_except_cur m m' ->
  mem_compatible_with tp m phi ->
  mem_compatible_with tp m' phi.
Proof.
  intros E [J AC LW LJ JL]; constructor; auto.
  - eapply mem_cohere_same_except_cur. apply E. apply AC.
  - destruct E as (ECo & EMa & EN).
    intros b ofs Ef ofs0 Ran.
    specialize (LW b ofs Ef ofs0 Ran).
    unfold max_access_cohere in *.
    apply equal_f with (x := (b, ofs0)) in EMa.
    unfold max_access_at, access_at in *.
    simpl in *.
    rewrite <-EMa.
    auto.
Qed.

(*Lemma resource_at_joins phi1 phi2 loc :
  joins phi1 phi2 -> joins (phi1 @ loc) (phi2 @ loc).
Proof.
  intros (phi3, j).
  apply resource_at_join with (loc := loc) in j.
  hnf; eauto.
Qed.*)

Lemma juicyRestrict_Max b ofs phi m (coh : access_cohere' m phi):
  PMap.get b (Mem.mem_access (juicyRestrict coh)) ofs Max =
  PMap.get b (Mem.mem_access m) ofs Max.
Proof.
  symmetry.
  apply (juicyRestrictMax coh (b, ofs)).
Qed.

Lemma juicyRestrict_Cur b ofs phi m (coh : access_cohere' m phi):
  PMap.get b (Mem.mem_access (juicyRestrict coh)) ofs Cur =
  perm_of_res (phi @ (b, ofs)).
Proof.
  apply (juicyRestrictCurEq coh (b, ofs)).
Qed.

Lemma same_perm_spec m1 m2 :
  Mem.perm m1 = Mem.perm m2 <->
  (forall k x, access_at m1 x k = access_at m2 x k).
Proof.
  split.
  - intros E k (b, ofs).
    apply equal_f with (x := b) in E.
    apply equal_f with (x := ofs) in E.
    apply equal_f with (x := k) in E.
    match type of E with ?a = ?b => assert (L : forall p, a p -> b p) by congruence end.
    match type of E with ?a = ?b => assert (R : forall p, b p -> a p) by congruence end. clear E.
    unfold Mem.perm in *.
    unfold access_at in *.
    simpl.
    destruct (PMap.get b (Mem.mem_access m1) ofs k) as [[]|], (PMap.get b (Mem.mem_access m2) ofs k) as [[]|].
    all: simpl in *.
    all: auto || exfalso.
    all: try specialize (L _ (perm_refl _)).
    all: try specialize (R _ (perm_refl _)).
    all: try inv L; inv R.
  - unfold access_at in *.
    intros E. extensionality b ofs k p.
    unfold Mem.perm.
    specialize (E k (b, ofs)); simpl in E.
    rewrite E.
    auto.
Qed.

Lemma juicyRestrictCur_ext m phi phi'
      (coh : access_cohere' m phi)
      (coh' : access_cohere' m phi')
      (same : forall loc, perm_of_res (phi @ loc) = perm_of_res (phi' @ loc)) :
  Mem.mem_access (juicyRestrict coh) =
  Mem.mem_access (juicyRestrict coh').
Proof.
  unfold juicyRestrict in *.
  unfold restrPermMap in *; simpl.
  f_equal.
  apply PTree.extensionality; intros.
  rewrite !PTree.gmap; f_equal.
  extensionality f ofs k.
  destruct k; auto.
  unfold juice2Perm.
  repeat f_equal.
  extensionality b a o; auto.
Qed.

Lemma PTree_map_self (A : Type) (f : positive -> A -> A) t :
  (forall b a, t !! b = Some a -> f b a = a) ->
  PTree.map f t = t.
Proof.
  intros H.
  apply PTree.extensionality; intros.
  rewrite PTree.gmap.
  specialize (H i); destruct (t !! i); auto; simpl.
  rewrite H; auto.
Qed.

Lemma juicyRestrictCur_unchanged m phi
      (coh : access_cohere' m phi)
      (pres : forall loc, perm_of_res (phi @ loc) = access_at m loc Cur) :
  Mem.mem_access (juicyRestrict coh) = Mem.mem_access m.
Proof.
  unfold juicyRestrict in *.
  unfold restrPermMap in *; simpl.
  unfold access_at in *.
  destruct (Mem.mem_access m) as (a, t) eqn:Eat.
  simpl.
  apply f_equal2.
  - extensionality ofs k.
    destruct k. auto.
    pose proof Mem_canonical_useful m as H.
    rewrite Eat in H.
    auto.
  - apply PTree.extensionality; intros.
    rewrite PTree.gmap.
    destruct (t !! i) eqn: Hi; auto; simpl.
    f_equal; extensionality ofs k.
    destruct k; auto.
    rewrite <- juic2Perm_correct; auto.
    rewrite pres; simpl.
    unfold PMap.get; simpl.
    rewrite Hi; auto.
Qed.

Lemma ZIndexed_index_surj p : { z : Z | ZIndexed.index z = p }.
Proof.
  destruct p.
  exists (Z.neg p); reflexivity.
  exists (Z.pos p); reflexivity.
  exists Z0; reflexivity.
Qed.

(*Lemma self_join_pshare_false (psh psh' : pshare) : ~sepalg.join psh psh psh'.
Proof.
  intros j; inv j.
  destruct psh as (sh, n); simpl in *.
  destruct psh' as (sh', n'); simpl in *.
  eapply share_joins_self.
  - exists sh'; auto. constructor; eauto.
  - auto.
Qed.*)

(*Lemma lock_inv_at sh v R phi :
  app_pred (lock_inv sh v R) phi ->
  exists b ofs, v = Vptr b ofs /\ exists R, islock_pred R (phi @ (b, Ptrofs.unsigned ofs)).
Proof.
  intros (b & ofs & Ev & lk).
  exists b, ofs. split. now apply Ev.
  specialize (lk (b, Ptrofs.unsigned ofs)).
  exists (approx (level phi) R).
  simpl in lk.
  if_tac in lk; swap 1 2. {
    exfalso.
    apply H.
    unfold adr_range in *.
    intuition.
    pose proof LKSIZE_pos.
    lia.
  }
  destruct lk as [p lk].
  rewrite lk.
  do 3 eexists.
  rewrite Z.sub_diag.
  reflexivity.
Qed.*)

End Machine.
