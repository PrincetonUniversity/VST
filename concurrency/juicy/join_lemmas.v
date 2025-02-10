Require Import Lia.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Require Import compcert.lib.Coqlib.

Require Import VST.msl.Coqlib2.
Require Import VST.veric.coqlib4.
Require Import VST.concurrency.common.threadPool.

Set Bullet Behavior "Strict Subproofs".

(** * Other list functions *)

Fixpoint listoption_inv {A} (l : list (option A)) : list A :=
  match l with
  | Some x :: l => x :: listoption_inv l
  | None :: l => listoption_inv l
  | nil => nil
  end.

Lemma map_listoption_inv {A B} (f : A -> B) (l : list (option A)) :
  map f (listoption_inv l) = listoption_inv (map (option_map f) l).
Proof.
  induction l as [ | [a|] l]; simpl; f_equal; auto.
Qed.

Fixpoint all_but (i : nat) {A} (l : list A) : list A :=
  match i with
    O => tl l
  | S i =>
    match l with
      nil => nil
    | x :: l => x :: all_but i l
    end
  end.

Lemma all_but_app {A} i (l l' : list A) :
  lt i (List.length l) ->
  all_but i (l ++ l') = all_but i l ++ l'.
Proof.
  revert l l'; induction i; intros [ | x l ] l' len; simpl; auto.
  all: try solve [inversion len].
  f_equal. apply IHi. simpl in *; lia.
Qed.

Lemma all_but_map {A B} (f : A -> B) i l :
  all_but i (map f l) = map f (all_but i l).
Proof.
  revert l; induction i; simpl.
  - destruct l; auto.
  - intros [|x l]; simpl; f_equal; auto.
Qed.

Lemma permutation_all_but {A} i (l : list A) x :
  nth_error l i = Some x ->
  Permutation l (x :: all_but i l).
Proof.
  revert l; induction i; simpl; intros [ | y l] E; try discriminate.
  - injection E as ->; simpl. constructor. auto with *.
  - specialize (IHi _ E).
    transitivity (y :: x :: all_but i l); auto.
    constructor.
Qed.

Fixpoint upd (i : nat) {A} new (l : list A) : option (list A) :=
  match i, l with
  | O, _ :: l => Some (new :: l)
  | _, nil => None
  | S i, x :: l =>
    match upd i new l with
    | Some l' => Some (x :: l')
    | None => None
    end
  end.

Lemma permutation_upd {A} i (l l' : list A) x :
  upd i x l = Some l' ->
  Permutation l' (x :: all_but i l).
Proof.
  revert l l'; induction i; simpl; intros [|y l] l' E;
    try discriminate.
  - injection E as <-; simpl. auto.
  - destruct (upd i x l) eqn:F'; try discriminate.
    injection E as <-.
    transitivity (y :: x :: all_but i l); auto.
    constructor.
Qed.

Lemma upd_lt {A} i x l : @upd i A x l <> None <-> lt i (List.length l).
Proof.
  revert i; induction l; intros i.
  - split.
    + destruct i; tauto.
    + inversion 1.
  - destruct i.
    + simpl; split.
      * auto with *.
      * congruence.
    + specialize (IHl i).
      transitivity (lt i (List.length l)).
      * rewrite <- IHl; clear IHl.
        simpl. destruct (upd i x l); split; congruence.
      * simpl; split; lia.
Qed.

Lemma upd_app_Some {A} i x (l1 l1' l2 : list A) :
  upd i x l1 = Some l1' ->
  upd i x (l1 ++ l2) = Some (l1' ++ l2).
Proof.
  revert i l1'; induction l1; intros i l1'.
  - destruct i; simpl; congruence.
  - destruct i; simpl.
    + injection 1 as <-. reflexivity.
    + destruct (upd i x l1) eqn:E. 2:congruence.
      injection 1 as <-.
      rewrite (IHl1 _ _ E).
      reflexivity.
Qed.

Lemma upd_app_None {A} i x (l1 l2 : list A) :
  upd i x l1 = None ->
  upd i x (l1 ++ l2) =
  option_map (app l1) (upd (i - List.length l1) x l2).
Proof.
  revert i; induction l1; intros i.
  - simpl. intros _. replace (i - 0)%nat with i by lia.
    destruct (upd i x l2); auto.
  - destruct i; simpl; intros E. discriminate.
    destruct (upd i x l1) as [o|] eqn:Eo. discriminate.
    rewrite (IHl1 _ Eo).
    destruct (upd (i - List.length l1) x l2); reflexivity.
Qed.

Lemma upd_last {A} i l (a x : A) :
  i = List.length l ->
  upd i x (l ++ a :: nil) = Some (l ++ x :: nil).
Proof.
  revert l a x; induction i; intros l a x.
  - destruct l. reflexivity. simpl. lia.
  - destruct l. simpl; lia. simpl.
    injection 1 as ->. rewrite IHi; auto.
Qed.

Lemma upd_rev {A} i x (l : list A) :
  (i < List.length l)%nat ->
  upd i x (rev l) = option_map (@rev A) (upd (List.length l - 1 - i) x l).
Proof.
  revert i; induction l; intros i li.
  - destruct i; auto.
  - simpl rev; simpl List.length.
    destruct (eq_dec i (List.length l)).
    + subst i. simpl. replace (List.length l - 0 - List.length l)%nat with O by lia.
      simpl.
      apply upd_last. symmetry. apply List.rev_length.
    + simpl in li.
      assert (U : (i < List.length l)%nat) by lia.
      pose proof U as Hi.
      rewrite <- List.rev_length in U.
      rewrite <-(upd_lt _ x) in U.
      destruct (upd i x (rev l)) as [o|] eqn:Eo. 2:tauto. clear U.
      specialize (IHl i Hi).
      rewrite Eo in IHl.
      replace (S (List.length l) - 1 - i)%nat with (S (List.length l - 1 - i)) by lia.
      simpl.
      destruct (upd (List.length l - 1 - i) x l) as [o'|] eqn:Eo'. 2: discriminate.
      simpl in *.
      apply upd_app_Some. congruence.
Qed.

Require Import VST.veric.res_predicates.
Require Import VST.concurrency.common.enums_equality.
Require Import VST.concurrency.juicy.juicy_machine.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.juicy.JuicyMachineModule.

(*! Instantiation of modules *)
Import THE_JUICY_MACHINE.
Import Concur.
Import OrdinalPool threadPool.ThreadPool.

Set Bullet Behavior "Strict Subproofs".

(** * join_all and permutations *)

Section Machine.

Context {ge : Clight.genv} {Σ : gFunctors}.

Definition getLocksR (tp : jstate ge) := listoption_inv (map snd (AMap.elements (lset tp))).

Definition maps tp := (getThreadsR tp ++ getLocksR tp ++ (extraRes tp :: nil))%list.

Lemma all_but_maps i tp (cnti : containsThread tp i) :
  all_but i (maps tp) = all_but i (getThreadsR tp) ++ getLocksR tp ++ (extraRes tp :: nil).
Proof.
  unfold maps. generalize (getLocksR tp); intros l.
  apply all_but_app.
  destruct tp as [[n] th ph lset]; simpl in *.
  unfold getThreadsR in *.
  unfold containsThread in *.
  simpl in *.
  rewrite List.map_length.
  clear -cnti.
  rewrite length_enum.
  pose proof @ssrnat.ltP i n.
  rewrite cnti in H.
  inversion H; auto.
Qed.

(** * Results about handling threads' rmaps *)

Lemma seq_pmap_decent {A B} (f : A -> option B) l :
  seq.pmap f l = listoption_inv (map f l).
Proof.
  induction l; simpl. reflexivity.
  destruct (f a); rewrite IHl; reflexivity.
Qed.

Lemma minus_plus a b c : a - (b + c) = a - b - c.
Proof.
  lia.
Qed.

Lemma nth_error_enum_from n m i Hn Hi :
  (i < n)%nat ->
  nth_error (@enum_from n m Hn) i = Some (@fintype.Ordinal m (n - 1 - i) Hi).
Proof.
  revert i Hi;  induction n; intros i Hi Hin.
  - simpl. inv Hin.
  - destruct i.
    + f_equal.
      simpl minus in *.
      revert Hi.
      rewrite -> Nat.sub_0_r in *.
      rewrite -> Nat.sub_0_r in *.
      intros Hi.
      simpl.
      f_equal.
      f_equal.
      apply proof_irr.
    + simpl minus in *.
      revert Hi.
      rewrite -> Nat.sub_0_r in *.
      intros Hi.
      simpl.
      unshelve erewrite IHn.
      * exact_eq Hi.
        f_equal.
        f_equal.
        f_equal.
        rewrite <- Nat.sub_add_distr.
        reflexivity.
      * f_equal.
        rewrite <- Nat.sub_add_distr.
        simpl.
        f_equal.
        apply proof_irr.
      * lia.
Qed.

Lemma nth_error_enum n i pr :
  nth_error (enum n) i = Some (@fintype.Ordinal n i pr).
Proof.
  unfold enum.
  rewrite initial_world.nth_error_rev; swap 1 2.
  - rewrite length_enum_from.
    apply (ssrbool.elimT ssrnat.leP pr).
  - rewrite length_enum_from.
    unshelve erewrite nth_error_enum_from.
    + pose proof pr as H.
      exact_eq H. do 2 f_equal.
      pose proof (ssrbool.elimT ssrnat.leP pr).
      lia.
    + match goal with
        |- Some (fintype.Ordinal (n:=n) (m:=n - 1 - (n - i - 1)) ?H) = _ =>
        generalize H
      end.
      pose proof (ssrbool.elimT ssrnat.leP pr).
      assert (R : (n - 1 - (n - i - 1) = i)%nat) by lia.
      rewrite -> R in *.
      intros pr'.
      do 2 f_equal.
      apply proof_irr.
    + pose proof (ssrbool.elimT ssrnat.leP pr).
      lia.
Qed.

Instance JSem : Semantics := ClightSemanticsForMachines.ClightSem ge.

Lemma getThreadR_nth i tp cnti :
  nth_error (getThreadsR tp) i = Some (@getThreadR _ _ _ i tp cnti).
Proof.
  simpl.
  unfold OrdinalPool.getThreadR in *.
  unfold getThreadsR in *.
  rewrite list_map_nth.
  match goal with
    |- option_map ?f ?x = Some (?f ?y) =>
    cut (x = Some y)
  end.
  intros ->; reflexivity.
  unfold containsThread in *.
  revert cnti.
  destruct tp as [n]; simpl. clear.
  apply nth_error_enum.
Qed.

Lemma getThreadsR_but i tp cnti :
  Permutation
    (getThreadsR tp)
    (@getThreadR _ _ _ i tp cnti :: all_but i (getThreadsR tp)).
Proof.
  apply permutation_all_but, getThreadR_nth.
Qed.

Lemma eqtype_refl n i cnti cntj :
  @eqtype.eq_op
    (fintype.ordinal_eqType n)
    (@fintype.Ordinal n i cnti)
    (@fintype.Ordinal n i cntj)
  = true.
Proof.
  compute; induction i; auto.
Qed.

Lemma eqtype_refl' n i j cnti cntj :
  i = j ->
  @eqtype.eq_op
    (fintype.ordinal_eqType n)
    (@fintype.Ordinal n i cnti)
    (@fintype.Ordinal n j cntj)
  = true.
Proof.
  intros <-; apply eqtype_refl.
Qed.

Lemma eqtype_neq n i j cnti cntj :
  i <> j ->
  @eqtype.eq_op
    (fintype.ordinal_eqType n)
    (@fintype.Ordinal n i cnti)
    (@fintype.Ordinal n j cntj)
  = false.
Proof.
  revert j cntj.
  induction i; intros [|j] cntj d.
  all:try tauto.
  unshelve eapply IHi; auto with *.
Qed.

Lemma updThreadR_but i tp cnti phi :
  Permutation
    (getThreadsR (@updThreadR _ _ _ i tp cnti phi))
    (phi :: all_but i (getThreadsR tp)).
Proof.
  apply permutation_upd.
  simpl.
  unfold OrdinalPool.updThreadR, getThreadsR.
  simpl in *.
  unfold OrdinalPool.containsThread in *.
  destruct tp as [[n] thds phis lset]; simpl in *.
  unfold enum.
  clear thds lset.
  rewrite map_rev.
  rewrite map_rev.
  assert (li : lt i n). {
    apply (ssrbool.elimT ssrnat.leP cnti).
  }
  rewrite upd_rev; auto.
  2:now rewrite map_length length_enum_from; auto.
  rewrite List.map_length length_enum_from.
  match goal with
    |- _ = Some (?a ?x) =>
    change (Some (a x)) with (option_map a (Some x))
  end.
  f_equal.
  generalize (Nat.le_refl n) as pr.
  rename n into m.
  assert (Ei : (i = (m - 1 - (m - 1 - i)))%nat). {
    pose proof (ssrbool.elimT ssrnat.leP cnti).
    rewrite <- !Nat.sub_add_distr, Nat.add_comm, Nat.sub_add_distr.
    replace (m - (m - (1 + i)))%nat with (S i); lia.
  }
  assert (cnti' : is_true (ssrnat.leq (S (m - 1 - (m - 1 - i))) m))
    by congruence.
  replace (@fintype.Ordinal m i cnti)
  with (@fintype.Ordinal m (m - 1 - (m - 1 - i)) cnti')
    by (revert cnti'; rewrite <-Ei; intros; f_equal; apply proof_irr).
  assert (li' : (m - 1 - i < m)%nat) by (clear -li; lia).
  clear cnti Ei. revert li' cnti'.
  generalize (m - 1 - i)%nat; clear i li; intros i.
  generalize m at 1 2 4 7 13 14; intros n; revert i.
  induction n; intros i li cnti Hnm. now inversion li.
  match goal with |- _ = Some (map ?F _) => set (f := F) end.
  destruct i.
  - simpl.
    f_equal.
    f_equal.
    + unfold f; simpl.
      rewrite eqtype_refl'. reflexivity. lia.
    + clear.
      unfold f; clear f. simpl in cnti.
      simpl.
      revert cnti; replace (n - 0 - 0)%nat with n by lia; intros cnti.
      revert cnti; assert (H : le n n) by auto; revert H.
      generalize n at 2 3 9; intros a la cnta.
      induction n. auto.
      simpl; f_equal.
      * rewrite eqtype_neq. 2:lia.
        auto.
      * unshelve erewrite IHn. 2:lia.
        auto.
  - simpl.
    erewrite IHn.
    2:lia.
    f_equal.
    f_equal.
    + unfold f.
      simpl.
      rewrite eqtype_neq. 2:lia.
      reflexivity.
    + unfold f.
      f_equal.
      extensionality x.
      destruct x as [j lj].
      destruct (eq_dec j (n - 1 - i)%nat).
      * rewrite eqtype_refl'; auto.
        rewrite eqtype_refl'; auto.
        lia.
      * rewrite eqtype_neq; auto.
        rewrite eqtype_neq; auto.
        lia.
  Unshelve. (* unshelving at "erewrite IHn." above makes the proof fail *)
  clear -cnti. exact_eq cnti; do 3 f_equal. lia.
Qed.

Lemma updThread_but i tp cnti c phi :
  Permutation
    (getThreadsR (@updThread _ _ _ i tp cnti c phi))
    (phi :: all_but i (getThreadsR tp)).
Proof.
  pose proof (updThreadR_but i tp cnti phi) as H; revert H.
  unfold updThreadR, updThread, getThreadsR; simpl.
  auto.
Qed.

(** * Results about handling locks *)

Lemma getLocksR_updLockSet_Some tp addr phi :
  Permutation
    (getLocksR (updLockSet(resources:=LocksAndResources) tp addr (Some phi)))
    (phi :: getLocksR (remLockSet tp addr)).
Proof.
  unfold lockRes, getLocksR, remLockSet, lset.
  destruct tp as [n th ph lset]; simpl. clear.
  destruct lset as [l S].
  unfold AMap.Raw.t, AMap.find in *; simpl. clear S.
  induction l as [|[addr' x] l]; simpl. reflexivity.
  destruct (AddressOrdered.compare addr addr'); simpl; try reflexivity.
  destruct x; simpl; rewrite IHl; auto.
  apply perm_swap.
Qed.

Lemma getLocksR_updLockSet_None (tp : jstate ge) addr :
  getLocksR (updLockSet tp addr None) = getLocksR (remLockSet tp addr).
Proof.
  unfold lockRes, getLocksR, remLockSet, lset.
  destruct tp as [n th ph lset]; simpl. clear.
  destruct lset as [l S].
  unfold AMap.Raw.t, AMap.find in *; simpl. clear S.
  induction l as [|[addr' x] l]; simpl. reflexivity.
  destruct (AddressOrdered.compare addr addr'); simpl; try reflexivity.
  destruct x; simpl; rewrite IHl; auto.
Qed.

Lemma getLocksR_SSome (tp : jstate ge) addr phi :
  lockRes tp addr = Some (Some phi) ->
  Permutation
    (getLocksR tp)
    (phi :: getLocksR (remLockSet tp addr)).
Proof.
  simpl.
  unfold OrdinalPool.lockRes, getLocksR, remLockSet, lset.
  destruct tp as [n th ph lset]; simpl. clear.
  destruct lset as [l S].
  unfold AMap.Raw.t, AMap.find in *; simpl. clear S.
  induction l as [|[addr' x] l]; simpl; intros F. inversion F.
  destruct (AddressOrdered.compare addr addr'); inversion F; auto.
  destruct x; simpl; rewrite IHl; auto.
  apply perm_swap.
Qed.


Lemma getLocksR_SNone (tp : jstate ge) addr :
  lockRes tp addr = Some None ->
  getLocksR (remLockSet tp addr) = getLocksR tp.
Proof.
  simpl.
  unfold OrdinalPool.lockRes, getLocksR, remLockSet, lset.
  destruct tp as [n th ph lset]; simpl. clear.
  destruct lset as [l S].
  unfold AMap.Raw.t, AMap.find in *; simpl. clear S.
  induction l as [|[addr' x] l]; simpl; intros F; auto.
  destruct (AddressOrdered.compare addr addr'); try inversion F; auto.
  destruct x; simpl; rewrite IHl; auto.
Qed.

Lemma getLocksR_None (tp : jstate ge) addr :
  lockRes tp addr = None ->
  getLocksR (remLockSet tp addr) = getLocksR tp.
Proof.
  simpl.
  unfold OrdinalPool.lockRes, getLocksR, remLockSet, lset.
  destruct tp as [n th ph lset]; simpl. clear.
  destruct lset as [l S].
  unfold AMap.Raw.t, AMap.find in *; simpl. clear S.
  induction l as [|[addr' x] l]; simpl; intros F; auto.
  destruct (AddressOrdered.compare addr addr'); try inversion F; auto.
  destruct x; simpl; rewrite IHl; auto.
Qed.

(** * All of those results in terms of [maps] *)

Lemma maps_getthread i tp cnti :
  Permutation (maps tp)
              (@getThreadR _ _ _ i tp cnti :: all_but i (maps tp)).
Proof.
  rewrite all_but_maps; auto.
  match goal with |-context[?a :: ?b ++ ?c] => change (a :: b ++ c) with ((a :: b) ++ c) end.
  rewrite <- getThreadsR_but; reflexivity.
Qed.

Lemma maps_updthread i tp cnti c phi :
  Permutation (maps (@updThread _ _ _ i tp cnti c phi))
              (phi :: all_but i (maps tp)).
Proof.
  rewrite all_but_maps; auto.
  unfold maps. rewrite updThread_but.
  apply Permutation_refl.
Qed.

Lemma maps_updthreadR i tp cnti phi :
  Permutation (maps (@updThreadR _ _ _ i tp cnti phi))
              (phi :: all_but i (maps tp)).
Proof.
  rewrite all_but_maps; auto.
  unfold maps. rewrite updThreadR_but.
  apply Permutation_refl.
Qed.

Lemma maps_updlock1 (tp : jstate ge) addr :
  maps (updLockSet tp addr None) = maps (remLockSet tp addr).
Proof.
  unfold maps; do 2 f_equal.
  apply getLocksR_updLockSet_None.
Qed.

Lemma maps_updlock2 (tp : jstate ge) addr phi :
  Permutation (maps (updLockSet tp addr (Some phi)))
              (phi :: maps (remLockSet tp addr)).
Proof.
  unfold maps.
  rewrite getLocksR_updLockSet_Some.
  symmetry.
  apply Permutation_cons_app; auto.
Qed.

Lemma maps_getlock1 tp addr :
  lockRes tp addr = None ->
  maps (remLockSet tp addr) = maps tp.
Proof.
  unfold maps; f_equal; intro.
  rewrite getLocksR_None; auto.
Qed.

Lemma maps_getlock2 (tp : jstate ge) addr :
  lockRes tp addr = Some None ->
  maps (remLockSet tp addr) = maps tp.
Proof.
  unfold maps; f_equal; intro.
  rewrite getLocksR_SNone; auto.
Qed.

Lemma maps_getlock3 (tp : jstate ge) addr phi :
  lockRes tp addr = Some (Some phi) ->
  Permutation (maps tp) (phi :: maps (remLockSet tp addr)).
Proof.
  unfold maps; f_equal; intro.
  rewrite getLocksR_SSome; eauto.
  symmetry.
  apply Permutation_cons_app; auto.
Qed.

Lemma maps_addthread tp v1 v2 phi :
  Permutation (maps (addThread tp v1 v2 phi))
              (phi :: maps tp).
Proof.
  unfold maps.
  match goal with |-context[?a :: ?b ++ ?c] => change (a :: b ++ c) with ((a :: b) ++ c) end.
  apply Permutation_app_tail.
  rewrite Permutation_cons_append.
  rewrite getThreadsR_addThread.
  apply Permutation_refl.
Qed.

Lemma maps_remLockSet_updThread i tp addr cnti c phi :
  maps (remLockSet (@updThread _ _ _ i tp cnti c phi) addr) =
  maps (@updThread _ _ _ i (remLockSet tp addr) cnti c phi).
Proof.
  reflexivity.
Qed.

End Machine.
