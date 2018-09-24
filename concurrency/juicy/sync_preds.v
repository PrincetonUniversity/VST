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
Require Import VST.msl.seplog.
Require Import VST.msl.age_to.
Require Import VST.veric.aging_lemmas.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.age_to_resource_at.
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

(** * Results related to resouce_decay *)

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
  Intv.In i (start, start + length) <->
  adr_range (b, start) length (b, i).
Proof.
  compute; intuition.
Qed.

Lemma join_YES_l {r1 r2 r3 sh1 sh1' k pp} :
  sepalg.join r1 r2 r3 ->
  r1 = YES sh1 sh1' k pp ->
  exists sh3 sh3',
    r3 = YES sh3 sh3' k pp.
Proof.
  intros J; inversion J; intros.
  all:try congruence.
  all:do 2 eexists; f_equal; try congruence.
Qed.


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
 pose proof (LKSIZE_pos). destruct loc; simpl; f_equal; auto. omega.
Qed.


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
  cut (~ ~ (b < Mem.nextblock m)%positive). zify. omega. intros L.
  specialize (LW ofs).
  assert (Intv.In ofs (ofs, (ofs + LKSIZE)%Z)).
  { split; simpl; pose proof LKSIZE_pos; omega. }
  autospec LW.
  rewrite (Mem.nextblock_noaccess _ _ ofs Max L) in LW.
  inversion LW.
Qed.

Lemma join_all_age_updThread_level (tp : jstate ge) i (cnti : ThreadPool.containsThread tp i) c phi Phi :
  join_all (age_tp_to (level phi) (ThreadPool.updThread cnti c phi)) Phi ->
  level Phi = level phi.
Proof.
  intros J; symmetry.
  remember (level phi) as n.
  rewrite <- (level_age_to n phi). 2:omega.
  apply rmap_join_sub_eq_level.
  assert (cnti' : containsThread (updThread cnti c phi) i) by eauto with *.
  rewrite (cnt_age_iff (n := n)) in cnti'.
  pose proof compatible_threadRes_sub cnti' J as H.
  unshelve erewrite <-getThreadR_age in H; eauto with *.
  rewrite gssThreadRes in H.
  apply H.
Qed.

Lemma join_all_level_lset (tp : jstate ge) Phi l phi :
  join_all tp Phi ->
  AMap.find l (lset tp) = Some (Some phi) ->
  level phi = level Phi.
Proof.
  intros J F.
  apply rmap_join_sub_eq_level.
  eapply compatible_lockRes_sub; eauto; simpl; eauto.
Qed.

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
    simpl in *.
    destruct (AMap.find (elt:=option rmap) (b, ofs) (lset tp)).
    * reflexivity.
    * tauto.
Qed.

Lemma age_to_updThread i (tp : jstate ge) n c phi cnti cnti' :
  age_tp_to n (@updThread _ _ _ i tp cnti c phi) =
  @updThread _ _ _ i (age_tp_to n tp) cnti' c (age_to n phi).
Proof.
  destruct tp; simpl.
  unfold OrdinalPool.updThread in *; simpl.
  f_equal. extensionality j.
  unfold "oo".
  do 2 match goal with
         |- context [if ?a then _ else _] =>
         let E := fresh "E" in
         destruct a eqn:E
       end.
  all:auto.
  all:cut (true = false); [ congruence | ].
  all:rewrite <-E, <-E0; repeat f_equal; apply proof_irr.
Qed.

Lemma lset_age_tp_to n (tp : jstate ge) :
  lset (age_tp_to n tp) = AMap.map (option_map (age_to n)) (lset tp).
Proof.
  destruct tp; reflexivity.
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

Lemma lockSet_Writable_age n (tp : jstate ge) m :
  lockSet_Writable (lset tp) m ->
  lockSet_Writable (lset (age_tp_to n tp)) m.
Proof.
  rewrite lset_age_tp_to.
  intros L b ofs E ofs0 range.
  refine(L b ofs _ ofs0 range).
  exact_eq E; f_equal.
  apply isSome_find_map.
Qed.

Lemma lockSet_age_to n (tp : jstate ge) :
  lockSet (age_tp_to n tp) = lockSet tp.
Proof.
  destruct tp as [num thds phis lset].
  unfold lockSet in *.
  simpl.
  apply A2PMap_option_map.
Qed.

Lemma juicyLocks_in_lockSet_age n (tp : jstate ge) phi :
  juicyLocks_in_lockSet (lset tp) phi ->
  juicyLocks_in_lockSet (lset (age_tp_to n tp)) (age_to n phi).
Proof.
  rewrite lset_age_tp_to.
  intros L loc E.
  specialize (L loc).
  spec L. { intros. specialize (E _ H). destruct E as [sh [psh E]]. exists sh, psh.
   pattern (age_to n phi) in E. apply age_to_ind_opp  in E. auto.
   intros. 
  eapply age1_YES'; eauto.
  }
  rewrite isSome_find_map; auto.
Qed.

Lemma lockSet_in_juicyLocks_age n (tp : jstate ge) phi :
  lockSet_in_juicyLocks (lset tp) phi ->
  lockSet_in_juicyLocks (lset (age_tp_to n tp)) (age_to n phi).
Proof.
  rewrite lset_age_tp_to.
  intros L loc E.
  rewrite isSome_find_map in E.
  specialize (L loc E).
  destruct L as (sh & L). exists sh.
  pattern (age_to n phi).
  apply age_to_ind; auto. clear L.
  intros ? ? ? ? ? ?. specialize (H0 _ H1).
  destruct H0 as [sh2 [psh2 H0]]. exists sh2, psh2.
  assert (join_sub sh sh2 /\ exists P, x @ (fst loc, (snd loc + i)%Z) = YES sh2 psh2 (LK LKSIZE i) P).
  destruct H0 as [P [? ?]]; split; eauto.  clear H0; destruct H2.
  assert (H3: exists P, y @ (fst loc, (snd loc + i)%Z) = YES sh2 psh2 (LK LKSIZE i) P); [| destruct H3 as [P ?]; exists P; auto].
  rewrite <- age1_YES'; eauto.
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
    unfold contents_at in *.
    rewrite <-ECo. auto.
  - unfold max_access_cohere in *. intros loc.
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

Lemma resource_at_joins phi1 phi2 loc :
  joins phi1 phi2 -> joins (phi1 @ loc) (phi2 @ loc).
Proof.
  intros (phi3, j).
  apply resource_at_join with (loc := loc) in j.
  hnf; eauto.
Qed.

Lemma juicyRestrict_Max b ofs phi m (coh : access_cohere' m phi):
  (Mem.mem_access (juicyRestrict coh)) !! b ofs Max =
  (Mem.mem_access m) !! b ofs Max.
Proof.
  symmetry.
  apply (juicyRestrictMax coh (b, ofs)).
Qed.

Lemma juicyRestrict_Cur b ofs phi m (coh : access_cohere' m phi):
  (Mem.mem_access (juicyRestrict coh)) !! b ofs Cur =
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
    destruct ((Mem.mem_access m1) !! b ofs k) as [[]|], ((Mem.mem_access m2) !! b ofs k) as [[]|].
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

Lemma PTree_xmap_ext (A B : Type) (f f' : positive -> A -> B) t :
  (forall a, f a = f' a) ->
  PTree.xmap f t = PTree.xmap f' t.
Proof.
  intros E.
  induction t as [ | t1 IH1 [a|] t2 IH2 ].
  - reflexivity.
  - simpl.
    extensionality p.
    rewrite IH1, IH2, E.
    reflexivity.
  - simpl.
    rewrite IH1, IH2.
    reflexivity.
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
  unfold PTree.map in *.
  eapply equal_f.
  apply PTree_xmap_ext.
  intros b.
  extensionality f ofs k.
  destruct k; auto.
  unfold juice2Perm in *.
  unfold mapmap in *.
  simpl.
  unfold PTree.map in *.
  eapply equal_f.
  f_equal.
  f_equal.
  eapply equal_f.
  apply PTree_xmap_ext.
  intros.
  extensionality c ofs0.
  apply same.
Qed.

Lemma PTree_xmap_self A f (m : PTree.t A) i :
  (forall p a, m ! p = Some a -> f (PTree.prev_append i p) a = a) ->
  PTree.xmap f m i = m.
Proof.
  revert i.
  induction m; intros i E.
  - reflexivity.
  - simpl.
    f_equal.
    + apply IHm1.
      intros p a; specialize (E (xO p) a).
      apply E.
    + specialize (E xH).
      destruct o eqn:Eo; auto.
    + apply IHm2.
      intros p a; specialize (E (xI p) a).
      apply E.
Qed.

Lemma PTree_map_self (A : Type) (f : positive -> A -> A) t :
  (forall b a, t ! b = Some a -> f b a = a) ->
  PTree.map f t = t.
Proof.
  intros H.
  apply PTree_xmap_self, H.
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
  f_equal.
  - extensionality ofs k.
    destruct k. auto.
    pose proof Mem_canonical_useful m as H.
    rewrite Eat in H.
    auto.
  - apply PTree_xmap_self.
    intros b f E.
    extensionality ofs k.
    destruct k; auto.
    specialize (pres (b, ofs)).
    unfold "!!" in pres.
    simpl in pres.
    rewrite E in pres.
    rewrite <-pres.
    simpl.
    unfold juice2Perm in *.
    unfold mapmap in *.
    unfold "!!".
    simpl.
    rewrite Eat; simpl.
    rewrite PTree.gmap.
    rewrite PTree.gmap1.
    rewrite E.
    simpl.
    reflexivity.
Qed.

Lemma ZIndexed_index_surj p : { z : Z | ZIndexed.index z = p }.
Proof.
  destruct p.
  exists (Z.neg p); reflexivity.
  exists (Z.pos p); reflexivity.
  exists Z0; reflexivity.
Qed.

Lemma self_join_pshare_false (psh psh' : pshare) : ~sepalg.join psh psh psh'.
Proof.
  intros j; inv j.
  destruct psh as (sh, n); simpl in *.
  destruct psh' as (sh', n'); simpl in *.
  eapply share_joins_self.
  - exists sh'; auto. constructor; eauto.
  - auto.
Qed.

Lemma approx_eq_app_pred {P1 P2 : mpred} x n :
  level x < n ->
  @approx n P1 = approx n P2 ->
  app_pred P1 x ->
  app_pred P2 x.
Proof.
  intros l E s1.
  apply approx_p with n; rewrite <-E.
  split; auto.
Qed.

Lemma exclusive_approx R n : exclusive_mpred R -> exclusive_mpred (approx n R).
Proof.
  unfold exclusive_mpred; intros.
  eapply seplog.derives_trans, H.
  apply seplog.sepcon_derives; apply approx_derives.
Qed.

Import shares.

Lemma exclusive_joins_false R phi1 phi2 :
  exclusive_mpred R ->
  app_pred R phi1 ->
  app_pred R phi2 ->
  joins phi1 phi2 ->
  False.
Proof.
  unfold exclusive_mpred; intros.
  change (predicates_hered.derives (R * R) FF) in H.
  destruct H2.
  eapply H.
  do 3 eexists; eauto.
Qed.

Lemma weak_exclusive_joins_false R phi phi1 phi2 :
  level phi = level phi1 ->
  app_pred (weak_exclusive_mpred R) phi ->
  app_pred R phi1 ->
  app_pred R phi2 ->
  joins phi1 phi2 ->
  False.
Proof.
  intros.
  simpl in H0.
  change (predicates_hered.derives (approx (S (level phi)) R * approx (S (level phi)) R) FF) in H0.
  destruct H3.
  eapply H0.
  do 3 eexists; eauto.
  apply join_level in H3.
  repeat split; auto; omega.
Qed.

(*
Lemma isLKCT_rewrite r :
  (forall sh sh' z P,
      r <> YES sh sh' (LK z) P /\
      r <> YES sh sh' (CT z) P)
  <-> ~isLK r /\ ~isCT r.
Proof.
  unfold isLK, isCT; split.
  - intros H; split; intros (sh & sh' & z & P & E); do 4 autospec H; intuition.
  - intros (A & B). intros sh sh' z P; split; intros ->; eauto 40.
Qed.
*)

(*
Lemma isLK_rewrite r :
  (forall (sh : Share.t) Psh (z : Z) (P : preds), r <> YES sh Psh (LK z) P)
  <->
  ~ isLK r.
Proof.
  destruct r as [t0 | t0 p [] p0 | k p]; simpl; unfold isLK in *; split.
  all: try intros H ?; intros; breakhyps.
  intros E; injection E; intros; subst.
  apply H; eauto.
Qed.
*)

Lemma isLK_age_to n phi loc : isLK (age_to n phi @ loc) = isLK (phi @ loc).
Proof.
  unfold isLK in *.
  rewrite age_to_resource_at.
  destruct (phi @ loc); simpl; auto.
  - apply prop_ext; split;
      intros (shi & shi' & zi & Pi & Ei);
      injection Ei; intros; subst; eauto.
  - repeat (f_equal; extensionality).
    apply prop_ext; split; congruence.
Qed.

(*
Lemma isCT_age_to n phi loc : isCT (age_to n phi @ loc) = isCT (phi @ loc).
Proof.
  unfold isCT in *.
  rewrite age_to_resource_at.
  destruct (phi @ loc); simpl; auto.
  - apply prop_ext; split;
      intros (shi & shi' & zi & Pi & Ei);
      injection Ei; intros; subst; eauto.
  - repeat (f_equal; extensionality).
    apply prop_ext; split; congruence.
Qed.
*)

Lemma predat_inj {phi loc R1 R2} :
  predat phi loc R1 ->
  predat phi loc R2 ->
  R1 = R2.
Proof.
  unfold predat in *.
  intros.
  breakhyps.
  rewr (phi @ loc) in H.
  pose proof (YES_inj _ _ _ _ _ _ _ _ H).
  assert (snd ((x, LK x1 0, SomeP rmaps.Mpred (fun _ : list Type => R2: pred rmap))) =
          snd  (x2, LK x4 0, SomeP rmaps.Mpred (fun _ : list Type => R1))) by (f_equal; auto).
  simpl in H2.
  apply SomeP_inj in H2.
  pose proof equal_f_dep H2 nil.
  auto.
Qed.

Lemma predat1 {phi loc} {R: mpred} {z sh psh} :
  phi @ loc = YES sh psh (LK z 0) (SomeP rmaps.Mpred (fun _ => R)) ->
  predat phi loc (approx (level phi) R).
Proof.
  intro E; hnf; eauto.
  pose proof resource_at_approx phi loc as M.
  rewrite E in M at 1; simpl in M.
  rewrite <-M. unfold "oo"; simpl.
  eauto.
Qed.

Lemma predat2 {phi loc R sh } :
  LKspec_ext R sh loc phi ->
  predat phi loc (approx (level phi) R).
Proof.
  intros lk; specialize (lk loc); simpl in lk.
  if_tac in lk. 2:range_tac.
  hnf. unfold "oo" in *; simpl in *; destruct lk. 
  exists sh, x, LKSIZE. rewrite Z.sub_diag in H0. auto.
Qed.

Lemma predat3 {phi loc R sh} :
  LK_at R sh loc phi ->
  predat phi loc (approx (level phi) R).
Proof.
  apply predat2.
Qed.

Lemma predat4 {phi b ofs sh R} :
  app_pred (lock_inv sh (Vptr b ofs) R) phi ->
  predat phi (b, Ptrofs.unsigned ofs) (approx (level phi) R).
Proof.
  unfold lock_inv in *.
  intros (b' & ofs' & E & lk & _).
  injection E as <- <-.
  specialize (lk (b, Ptrofs.unsigned ofs)); simpl in lk.
  if_tac in lk. 2:range_tac.
  hnf. unfold "oo" in *; simpl in *; destruct lk; eauto.
  exists sh, x, LKSIZE. rewrite Z.sub_diag in H0. auto.
Qed.

Lemma predat5 {phi loc R} :
  islock_pred R (phi @ loc) ->
  predat phi loc R.
Proof.
  intros H; apply H.
Qed.

Lemma predat6 {R loc phi} : lkat R loc phi -> predat phi loc (approx (level phi) R).
Proof.
  unfold predat in *.
  unfold lkat in *.
  intros H. specialize (H loc).
  spec H.
  { destruct loc. split; auto; pose proof LKSIZE_pos; omega. }
  destruct H as (sh & rsh & ->).
  do 3 eexists. rewrite Z.sub_diag; 
  eauto.
Qed.

Lemma predat_join_sub {phi1 phi2 loc R} :
  join_sub phi1 phi2 ->
  predat phi1 loc R ->
  predat phi2 loc R.
Proof.
  intros (phi3, j) (sh & sh' & z & E). pose proof j as J.
  apply resource_at_join with (loc := loc) in j.
  hnf.
  apply join_level in J.
  rewrite E in j; inv j; eauto.
Qed.

Lemma lock_inv_at sh v R phi :
  app_pred (lock_inv sh v R) phi ->
  exists b ofs, v = Vptr b ofs /\ exists R, islock_pred R (phi @ (b, Ptrofs.unsigned ofs)).
Proof.
  intros (b & ofs & Ev & lk & _).
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
    omega.
  }
  destruct lk as [p lk].
  rewrite lk.
  do 3 eexists.
  rewrite Z.sub_diag.
  reflexivity.
Qed.

Lemma lkat_hered R loc : hereditary age (lkat R loc).
Proof.
  intros phi phi' A lk a r. specialize (lk a r).
  destruct lk as (sh & rsh & E); exists sh, rsh.
  erewrite age_resource_at; eauto.
  rewrite E.
  simpl; f_equal.
  unfold sync_preds_defs.pack_res_inv in *.
  f_equal. extensionality Ts.
  pose proof approx_oo_approx' (level phi') (level phi) as RR.
  spec RR. apply age_level in A. omega.
  unfold "oo" in *.
  apply (equal_f RR R).
Qed.

End Machine.
