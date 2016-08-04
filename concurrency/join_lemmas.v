Require Import Coq.omega.Omega.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Require Import compcert.lib.Coqlib.

Require Import msl.Coqlib2.
Require Import msl.seplog.
Require Import msl.sepalg.
Require Import veric.mem_lessdef.
Require Import concurrency.coqlib5.

(** * Results on joining lists and the necessary algebras *)

Fixpoint joinlist {A} {JA : Join A} (l : list A) (x : A) :=
  match l with
  | nil => identity x
  | h :: l => exists y, joinlist l y /\ join h y x
  end.

(* joinlist is injective (for non-empty lists) *)
Lemma joinlist_inj {A} {JA : Join A} {PA : Perm_alg A} l r1 r2 :
  l <> nil ->
  joinlist l r1 ->
  joinlist l r2 ->
  r1 = r2.
Proof.
  revert r1 r2; induction l; intros r1 r2 n j1 j2. tauto. clear n.
  destruct j1 as (r1' & j1 & h1).
  destruct j2 as (r2' & j2 & h2).
  destruct l; simpl in *.
  - apply join_comm in h1; apply join_comm in h2.
    pose proof join_unit1_e _ _ j1 h1.
    pose proof join_unit1_e _ _ j2 h2.
    congruence.
  - cut (r1' = r2').
    + intros <-.
      eapply join_eq; eauto.
    + eapply IHl; eauto.
      congruence.
Qed.

Lemma joinlist_permutation {A} {JA : Join A} {PA : Perm_alg A} l1 l2 r :
  Permutation l1 l2 ->
  joinlist l1 r ->
  joinlist l2 r.
Proof.
  intros p; revert r; induction p; intros r; auto.
  - intros (r' & jl & j).
    exists r'; split; auto.
  - simpl.
    intros (a & (b & jb & ja) & jr).
    apply join_comm in jr.
    destruct (join_assoc ja jr) as (d & jd & jr').
    eauto.
Qed.

Instance Permutation_length' A {JA : Join A} {PA : Perm_alg A} :
  Proper (@Permutation A ==> @eq A ==> Logic.iff) joinlist | 10.
Proof.
  intros l1 l2 p x y <-; split; apply joinlist_permutation; auto.
  apply Permutation_sym, p.
Qed.

Lemma joinlist_app {A} {JA : Join A} {PA : Perm_alg A} l1 l2 x1 x2 x :
  joinlist l1 x1 ->
  joinlist l2 x2 ->
  join x1 x2 x ->
  joinlist (l1 ++ l2) x.
Proof.
  revert l2 x1 x2 x; induction l1; intros l2 x1 x2 x j1 j2 j; simpl in *.
  - erewrite <-join_unit1_e; eauto.
  - destruct j1 as (x1' & jl & jx1).
    destruct (join_assoc jx1 j) as (r & ? & ?).
    exists r; split; eauto.
Qed.

Lemma app_joinlist {A} {JA : Join A} {SA : Sep_alg A} {PA : Perm_alg A} {CA : Canc_alg A} l1 l2 x :
  joinlist (l1 ++ l2) x ->
  exists x1 x2,
    joinlist l1 x1 /\
    joinlist l2 x2 /\
    join x1 x2 x.
Proof.
  revert l2 x; induction l1; intros l2 x j; simpl in *.
  - exists (core x), x; split.
    + apply core_identity.
    + split; auto. apply core_unit.
  - destruct j as (y & h & ayx).
    destruct (IHl1 _ _ h) as (x1 & x2 & h1 & h2 & j).
    apply join_comm in j.
    apply join_comm in ayx.
    destruct (join_assoc j ayx) as (r & ? & ?).
    exists r, x2. eauto.
Qed.

Lemma joinlist_merge {A} {JA : Join A} {PA : Perm_alg A} (a b c x : A) l :
  join a b c -> joinlist (a :: b :: l) x <-> joinlist (c :: l) x.
Proof.
  intros j; split; intros h; swap 1 2.
  - destruct h as (rl & hl & jx).
    destruct (join_assoc j jx) as (bl & jbl & jabx).
    simpl. eauto.
  - rename c into ab, x into abc, j into a_b.
    destruct h as (bc & hl & a_bc).
    destruct hl as (c & hl & b_c).
    exists c; split; auto.
    clear hl l.
    apply join_comm in b_c.
    apply join_comm in a_bc.
    destruct (join_assoc b_c a_bc) as (ab' & a_b' & ab_c).
    apply join_comm in ab_c.
    exact_eq ab_c; f_equal.
    eapply join_eq; eauto.
Qed.

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
  f_equal. apply IHi. simpl in *; omega.
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

Require Import msl.ageable.
Require Import msl.age_sepalg.

Lemma joinlist_age1' {A} `{agA : ageable A} {J : Join A} {_ : Age_alg A} {_ : Perm_alg A} (l : list A) (x : A) :
  joinlist l x ->
  joinlist (map age1' l) (age1' x).
Proof.
  revert x; induction l; intros x h.
  - simpl in *. unfold age1'.
    destruct (age1 x) eqn:E; auto.
    eapply age_identity. apply E. apply h.
  - destruct h as (y & h & j).
    exists (age1' y); split. auto.
    unfold age1'.
    destruct (age1 a) eqn:Ea.
    + destruct (age1_join _ j Ea) as (y' & z' & j' & -> & ->). auto.
    + rewrite age1_level0 in Ea.
      pose proof (join_level _ _ _ j).
      assert (Ex : age1 x = None). apply age1_level0. intuition; congruence.
      assert (Ey : age1 y = None). apply age1_level0. intuition; congruence.
      rewrite Ex, Ey. auto.
Qed.

Lemma joinlist_age_to {A} `{agA : ageable A} {J : Join A} {_ : Age_alg A} {_ : Perm_alg A} n (l : list A) (x : A) :
  joinlist l x ->
  joinlist (map (age_to n) l) (age_to n x).
Proof.
  intros h.
  unfold age_to at 2.
  replace (map (age_to n) l) with (map (age_by (level x - n)) l).
  - generalize (level x - n)%nat; clear n; intros n; induction n.
    + exact_eq h; f_equal.
      induction l; auto. rewrite IHl at 1. reflexivity.
    + apply joinlist_age1' in IHn.
      exact_eq IHn; f_equal. clear.
      induction l; simpl; auto. f_equal; auto.
  - revert x h; induction l; auto; intros y (x & h & j); simpl.
    apply join_level in j.
    f_equal.
    + unfold age_to. do 2 f_equal. intuition.
    + rewrite <-IHl with x; auto. do 3 f_equal. intuition.
Qed.


Require Import veric.compcert_rmaps.
Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.
Require Import concurrency.addressFiniteMap.
Require Import concurrency.permissions.
Require Import concurrency.JuicyMachineModule.

(*! Instantiation of modules *)
Import THE_JUICY_MACHINE.
Import JSEM.
Import ThreadPool.
Import JuicyMachineLemmas.
Module Machine :=THE_JUICY_MACHINE.JTP.

Set Bullet Behavior "Strict Subproofs".

(** * join_all and permutations *)

Definition getLocksR tp := listoption_inv (map snd (AMap.elements (lset tp))).

Definition maps tp := (getThreadsR tp ++ getLocksR tp)%list.

Fixpoint atoi n := match n with O => nil | S n => n :: atoi n end.

Lemma iota_spec n : seq.iota 0 n = seq.rev (atoi n).
Proof.
  induction n. reflexivity.
  simpl.
Admitted.

(* ridiculously large proofs about simple things *)
Lemma length_ord_enum n : seq.size (fintype.ord_enum n) = n.
Proof.
  unfold fintype.ord_enum in *.
  rewrite iota_spec.
  rewrite seq.size_pmap.
  match goal with |- _ ?P ?L = _ => assert (len : seq.size L = n) end.
  { rewrite seq.size_rev. induction n; simpl; auto. }
  match goal with |- _ ?P ?L = _ => pose (p := P); assert (A : seq.all p L = true) end.
  { rewrite seq.all_rev. clear len.
    cut (forall m, le m n -> seq.all p (atoi m) = true). intuition.
    intros m; induction m; intros le. auto.
    simpl. rewrite IHm. 2:omega.
    cut (p m = true). intros ->; auto.
    unfold p. clear -le.
    destruct (eqtype.insub m) eqn:E. reflexivity.
    cut (n < S m). omega.
    unfold eqtype.insub in *.
    destruct ssrbool.idP . discriminate. clear E le.    
    destruct (ssrnat.leq (S m) n) eqn:F. destruct n0. reflexivity.
    pose proof @ssrnat.ltP m n.
    inversion H. congruence.
    omega.
  }
  fold p.
  rewrite <-len at 2. clear len.
  revert A. generalize (seq.rev (atoi n)).
  intros l A.
  pose proof seq.all_count p l as C.
  rewrite A in C; symmetry in C.
  rewrite <-ssrnat.eqnE in C.
  clear -C.
  match goal with
    |- ?a = ?b => revert C; generalize b; generalize a
  end; intros x y.
  pose proof @ssrnat.eqnP x y.
  intros E; rewrite E in H.
  inversion H; auto.
Qed.

Lemma all_but_maps i tp (cnti : containsThread tp i) :
  all_but i (maps tp) = all_but i (getThreadsR tp) ++ getLocksR tp.
Proof.
  unfold maps. generalize (getLocksR tp); intros l.
  apply all_but_app.
  destruct tp as [[n] th ph lset]; simpl in *.
  unfold getThreadsR in *.
  unfold containsThread in *.
  simpl in *.
  rewrite map_length.
  clear -cnti.
  rewrite length_ord_enum.
  pose proof @ssrnat.ltP i n.
  rewrite cnti in H.
  inversion H; auto.
Qed.

Lemma join_list_joinlist : join_list = joinlist.
Proof.
  extensionality l; induction l; extensionality phi; simpl; auto.
  f_equal. extensionality r. apply prop_ext.
  split; intros []; split; auto; congruence.
Qed.

Lemma join_list'_None l : join_list' l None <-> listoption_inv l = nil.
Proof.
  induction l. simpl. split; auto.
  simpl.
  split; destruct a as [r|].
  - intros (r' & j & h). inversion j.
  - intros (r' & j & h). inversion j; subst; tauto.
  - congruence.
  - rewrite <-IHl. intro. exists None; split; auto. constructor.
Qed.

Lemma join_list'_Some l phi : join_list' l (Some phi) -> joinlist (listoption_inv l) phi.
Proof.
  revert phi; induction l; intros phi. simpl. congruence.
  intros (r & j & h).
  simpl.
  destruct a.
  - inversion j; subst.
    + apply join_list'_None in h.
      rewrite h.
      simpl.
      exists (core phi).
      split.
      * apply core_identity.
      * apply join_comm, core_unit.
    + inversion j; subst; simpl; eauto.
  - inversion j; subst; simpl; eauto.
Qed.

Lemma join_list'_Some' l phi : listoption_inv l <> nil -> joinlist (listoption_inv l) phi -> join_list' l (Some phi).
Proof.
  revert phi; induction l; intros phi. simpl; congruence.
  destruct a as [r|]; simpl.
  - intros _ (y & h & j).
    unfold LocksAndResources.res in *.
    assert (D:forall l:list rmap, l = nil \/ l <> nil)
      by (intros []; [left|right]; congruence).
    destruct (D (listoption_inv l)) as [E|E].
    + rewrite E in *.
      rewrite <-join_list'_None in E.
      exists None; split; auto.
      simpl in h.
      pose proof join_unit2_e _ _ h j. subst.
      constructor.
    + exists (Some y). split; auto.
      constructor; auto.
  - unfold LocksAndResources.res in *.
    intros n j; specialize (IHl _ n j).
    exists (Some phi); split; eauto. constructor.
Qed.

Lemma join_all_joinlist tp : join_all tp = joinlist (maps tp).
Proof.
  extensionality phi. apply prop_ext. split.
  - intros J. inversion J as [? rt rl ? jt jl j]; subst.
    destruct rl as [rl|].
    + inversion j; subst.
      apply joinlist_app with (x1 := rt) (x2 := rl); auto.
      * rewrite <-join_list_joinlist.
        apply jt.
      * apply join_list'_Some.
        apply jl.
    + inversion j; subst.
      rewrite <-join_list_joinlist.
      apply join_list'_None in jl.
      unfold maps.
      cut (join_list (getThreadsR tp ++ nil) phi).
      { intro H; exact_eq H. f_equal. f_equal. symmetry. apply jl. }
      rewrite app_nil_r.
      apply jt.
  - intros j.
    unfold maps in j.
    apply app_joinlist in j.
    destruct j as (rt & rl & jt & jl & j).
    set (l' := getLocksR tp).
    assert (D:l' = nil \/ l' <> nil)
      by (destruct l'; [left|right]; congruence).
    destruct D as [D|D].
    + exists rt None; unfold l' in *; unfold LocksAndResources.lock_info in *.
      * hnf. rewrite join_list_joinlist. apply jt.
      * hnf. unfold l' in D.
        unfold LocksAndResources.lock_info in *.
        rewrite join_list'_None.
        unfold LocksAndResources.res in *.
        rewrite <-D.
        reflexivity.
      * rewrite D in jl.
        simpl in jl.
        pose proof join_unit2_e _ _ jl j. subst.
        constructor.
    + exists rt (Some rl).
      * hnf. rewrite join_list_joinlist. apply jt.
      * hnf. apply join_list'_Some'; auto.
      * constructor; auto.
Qed.

(** * Results about handling threads' rmaps *)

Lemma seq_pmap_decent {A B} (f : A -> option B) l :
  seq.pmap f l = listoption_inv (map f l).
Proof.
  induction l; simpl. reflexivity.
  destruct (f a); rewrite IHl; reflexivity.
Qed.

Lemma nth_error_fintype i n :
  forall pr : is_true (ssrnat.leq (S i) n),
  nth_error (fintype.ord_enum n) i =
  Some (fintype.Ordinal (n:=n) (m:=i) pr).
Proof.
  intros.
  unfold fintype.ord_enum in *.
  transitivity (@eqtype.insub nat (fun x : nat => ssrnat.leq (S x) n) (fintype.ordinal_subType n) i).
  - assert (lt i n).
    { pose proof @ssrnat.ltP i n. rewrite pr in H. inversion H; auto. }
    assert (E : n = S i + (n - S i)) by omega.
    set (k := n - S i). fold k in E. clearbody k.
    subst n. clear H.
    (* ? *)
    admit.
  - unfold eqtype.insub in *.
    destruct ssrbool.idP; try tauto.
    unfold eqtype.Sub, fintype.ordinal_subType.
    repeat f_equal; apply proof_irr.
Admitted.

Lemma getThreadR_nth i tp cnti :
  nth_error (getThreadsR tp) i = Some (@getThreadR i tp cnti).
Proof.
  unfold getThreadR in *.
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
  apply nth_error_fintype.
Qed.

Lemma getThreadsR_but i tp cnti :
  Permutation
    (getThreadsR tp)
    (@getThreadR i tp cnti :: all_but i (getThreadsR tp)).
Proof.
  apply permutation_all_but, getThreadR_nth.
Qed.

Lemma updThreadR_but i tp cnti phi :
  Permutation
    (getThreadsR (@updThreadR i tp cnti phi))
    (phi :: all_but i (getThreadsR tp)).
Proof.
  unfold LocksAndResources.res in *.
  apply permutation_upd.
  unfold updThreadR, getThreadsR.
  simpl.
  unfold containsThread in *.
  destruct tp as [[n] thds phis]; simpl in *.
  (* ?  why redundancy *)
Admitted.

Lemma updThread_but i tp cnti c phi :
  Permutation
    (getThreadsR (@updThread i tp cnti c phi))
    (phi :: all_but i (getThreadsR tp)).
Proof.
  pose proof (updThreadR_but i tp cnti phi) as H; revert H.
  unfold LocksAndResources.res in *.
  unfold updThreadR, updThread, getThreadsR; simpl.
  auto.
Qed.

(** * Results about handling locks *)

Lemma getLocksR_updLockSet_Some tp addr phi :
  Permutation
    (getLocksR (updLockSet tp addr (Some phi)))
    (phi :: getLocksR (remLockSet tp addr)).
Proof.
  unfold lockRes, getLocksR, remLockSet, lset.
  destruct tp as [n th ph lset]; simpl. clear.
  destruct lset as [l S].
  unfold AMap.Raw.t, AMap.find in *; simpl. clear S.
  unfold LocksAndResources.lock_info in *.
  induction l as [|[addr' x] l]; simpl. reflexivity.
  destruct (AddressOrdered.compare addr addr'); simpl; try reflexivity.
  destruct x; simpl; rewrite IHl; auto.
  apply perm_swap.
Qed.

Lemma getLocksR_updLockSet_None tp addr :
  getLocksR (updLockSet tp addr None) = getLocksR (remLockSet tp addr).
Proof.
  unfold lockRes, getLocksR, remLockSet, lset.
  destruct tp as [n th ph lset]; simpl. clear.
  destruct lset as [l S].
  unfold AMap.Raw.t, AMap.find in *; simpl. clear S.
  unfold LocksAndResources.lock_info in *.
  induction l as [|[addr' x] l]; simpl. reflexivity.
  destruct (AddressOrdered.compare addr addr'); simpl; try reflexivity.
  destruct x; simpl; rewrite IHl; auto.
Qed.

Lemma getLocksR_SSome tp addr phi :
  lockRes tp addr = Some (Some phi) ->
  Permutation
    (getLocksR tp)
    (phi :: getLocksR (remLockSet tp addr)).
Proof.
  unfold lockRes, getLocksR, remLockSet, lset.
  destruct tp as [n th ph lset]; simpl. clear.
  destruct lset as [l S].
  unfold AMap.Raw.t, AMap.find in *; simpl. clear S.
  unfold LocksAndResources.lock_info in *.
  induction l as [|[addr' x] l]; simpl; intros F. inversion F.
  destruct (AddressOrdered.compare addr addr'); inversion F; auto.
  destruct x; simpl; rewrite IHl; auto.
  apply perm_swap.
Qed.


Lemma getLocksR_SNone tp addr :
  lockRes tp addr = Some None ->
  getLocksR (remLockSet tp addr) = getLocksR tp.
Proof.
  unfold lockRes, getLocksR, remLockSet, lset.
  destruct tp as [n th ph lset]; simpl. clear.
  destruct lset as [l S].
  unfold AMap.Raw.t, AMap.find in *; simpl. clear S.
  unfold LocksAndResources.lock_info in *.
  induction l as [|[addr' x] l]; simpl; intros F; auto. 
  destruct (AddressOrdered.compare addr addr'); try inversion F; auto.
  destruct x; simpl; rewrite IHl; auto.
Qed.

Lemma getLocksR_None tp addr :
  lockRes tp addr = None ->
  getLocksR (remLockSet tp addr) = getLocksR tp.
Proof.
  unfold lockRes, getLocksR, remLockSet, lset.
  destruct tp as [n th ph lset]; simpl. clear.
  destruct lset as [l S].
  unfold AMap.Raw.t, AMap.find in *; simpl. clear S.
  unfold LocksAndResources.lock_info in *.
  induction l as [|[addr' x] l]; simpl; intros F; auto. 
  destruct (AddressOrdered.compare addr addr'); try inversion F; auto.
  destruct x; simpl; rewrite IHl; auto.
Qed.

(** * All of those results in terms of [maps] *)

Lemma maps_getthread i tp cnti :
  Permutation (maps tp)
              (@getThreadR i tp cnti :: all_but i (maps tp)).
Proof.
  rewrite all_but_maps; auto.
  transitivity
    ((getThreadR cnti :: all_but i (getThreadsR tp)) ++ getLocksR tp); auto.
  rewrite <-getThreadsR_but. reflexivity.
Qed.

Lemma maps_updthread i tp cnti c phi :
  Permutation (maps (@updThread i tp cnti c phi))
              (phi :: all_but i (maps tp)).
Proof.
  rewrite all_but_maps; auto.
  unfold maps. rewrite updThread_but.
  apply Permutation_refl.
Qed.

Lemma maps_updthreadR i tp cnti phi :
  Permutation (maps (@updThreadR i tp cnti phi))
              (phi :: all_but i (maps tp)).
Proof.
  rewrite all_but_maps; auto.
  unfold maps. rewrite updThreadR_but.
  apply Permutation_refl.
Qed.

Lemma maps_updlock1 tp addr :
  maps (updLockSet tp addr None) = maps (remLockSet tp addr).
Proof.
  unfold maps; f_equal.
  apply getLocksR_updLockSet_None.
Qed.

Lemma maps_updlock2 tp addr phi :
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

Lemma maps_getlock2 tp addr :
  lockRes tp addr = Some None ->
  maps (remLockSet tp addr) = maps tp.
Proof.
  unfold maps; f_equal; intro.
  rewrite getLocksR_SNone; auto.
Qed.

Lemma maps_getlock3 tp addr phi :
  lockRes tp addr = Some (Some phi) ->
  Permutation (maps tp) (phi :: maps (remLockSet tp addr)).
Proof.
  unfold maps; f_equal; intro.
  rewrite getLocksR_SSome; eauto.
  symmetry.
  apply Permutation_cons_app; auto.
Qed.

Lemma maps_age_to i tp :
  maps (age_tp_to i tp) = map (age_to i) (maps tp).
Proof.
  destruct tp as [n th ph ls]; simpl.
  unfold maps, getThreadsR, getLocksR in *.
  rewrite map_app.
  f_equal.
  - apply map_compose.
  - unfold lset.
    rewrite AMap_map.
    rewrite map_listoption_inv.
    reflexivity.
Qed.

Lemma maps_remLockSet_updThread i tp addr cnti c phi :
  maps (remLockSet (@updThread i tp cnti c phi) addr) =
  maps (@updThread i (remLockSet tp addr) cnti c phi).
Proof.
  reflexivity.
Qed.

