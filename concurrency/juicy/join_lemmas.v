Require Import Coq.omega.Omega.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.

Require Import compcert.lib.Coqlib.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.seplog.
Require Import VST.msl.sepalg.
Require Import VST.msl.age_to.
Require Import VST.veric.coqlib4.
Require Import VST.concurrency.common.threadPool.

Set Bullet Behavior "Strict Subproofs".

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

Lemma app_joinlist {A} {JA : Join A} {SA : Sep_alg A} {PA : Perm_alg A} l1 l2 x :
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

Lemma joinlist_swap {A} {JA : Join A} {PA : Perm_alg A} (a b x : A) l :
  joinlist (a :: b :: l) x =
  joinlist (b :: a :: l) x.
Proof.
  apply prop_ext; split; apply joinlist_permutation; constructor.
Qed.

Lemma joinlist_join_sub {A} {JA : Join A} {PA : Perm_alg A} (x phi : A) l :
  joinlist l phi ->
  In x l -> join_sub x phi.
Proof.
  revert x phi; induction l; simpl. tauto.
  intros x phi (b & jb & ab) [-> | i].
  - exists b; auto.
  - specialize (IHl _ _ jb i); auto.
    destruct IHl as (c, xc).
    apply sepalg.join_comm in ab.
    destruct (sepalg.join_assoc xc ab) as (d, H).
    exists d; intuition.
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

Lemma upd_lt {A} i x l : @upd i A x l <> None <-> lt i (length l).
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
      transitivity (lt i (length l)).
      * rewrite <- IHl; clear IHl.
        simpl. destruct (upd i x l); split; congruence.
      * simpl; split; omega.
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
  option_map (app l1) (upd (i - length l1) x l2).
Proof.
  revert i; induction l1; intros i.
  - simpl. intros _. replace (i - 0)%nat with i by omega.
    destruct (upd i x l2); auto.
  - destruct i; simpl; intros E. discriminate.
    destruct (upd i x l1) as [o|] eqn:Eo. discriminate.
    rewrite (IHl1 _ Eo).
    destruct (upd (i - length l1) x l2); reflexivity.
Qed.

Lemma upd_last {A} i l (a x : A) :
  i = length l ->
  upd i x (l ++ a :: nil) = Some (l ++ x :: nil).
Proof.
  revert l a x; induction i; intros l a x.
  - destruct l. reflexivity. simpl. omega.
  - destruct l. simpl; omega. simpl.
    injection 1 as ->. rewrite IHi; auto.
Qed.

Lemma upd_rev {A} i x (l : list A) :
  (i < length l)%nat ->
  upd i x (rev l) = option_map (@rev A) (upd (length l - 1 - i) x l).
Proof.
  revert i; induction l; intros i li.
  - destruct i; auto.
  - simpl rev; simpl length.
    destruct (eq_dec i (length l)).
    + subst i. simpl. replace (length l - 0 - length l)%nat with O by omega.
      simpl.
      apply upd_last. symmetry. apply rev_length.
    + simpl in li.
      assert (U : (i < length l)%nat) by omega.
      pose proof U as Hi.
      rewrite <-rev_length in U.
      rewrite <-(upd_lt _ x) in U.
      destruct (upd i x (rev l)) as [o|] eqn:Eo. 2:tauto. clear U.
      specialize (IHl i Hi).
      rewrite Eo in IHl.
      replace (S (length l) - 1 - i)%nat with (S (length l - 1 - i)) by omega.
      simpl.
      destruct (upd (length l - 1 - i) x l) as [o'|] eqn:Eo'. 2: discriminate.
      simpl in *.
      apply upd_app_Some. congruence.
Qed.

Require Import VST.msl.ageable.
Require Import VST.msl.age_sepalg.

Lemma age_by_overflow {A} {_ : ageable A} {JA: Join A} (x : A) n : le (level x) n -> age_by n x = age_by (level x) x.
Proof.
  intros l.
  replace n with ((n - level x) + level x)%nat by omega.
  generalize (n - level x)%nat; intros k. clear n l.
  revert x; induction k; intros x. reflexivity.
  simpl. rewrite IHk.
  unfold age1' in *.
  destruct (age1 (age_by (level x) x)) eqn:E. 2:reflexivity. exfalso.
  eapply age1_level0_absurd. eauto.
  rewrite level_age_by. omega.
Qed.

Lemma age_by_minusminus {A} {_ : ageable A} {JA: Join A} (x : A) n : age_by (level x - (level x - n)) x = age_by n x.
Proof.
  assert (D : le (level x) n \/ lt n (level x)). omega.
  destruct D as [D|D].
  - replace (level x - (level x - n))%nat with (level x) by omega.
    symmetry; apply age_by_overflow, D.
  - f_equal; omega.
Qed.

Lemma age_by_join {A} {JA: Join A} {PA: Perm_alg A} {agA: ageable A} {AgeA: Age_alg A} :
  forall k x1 x2 x3,
    join x1 x2 x3 ->
    join (age_by k x1) (age_by k x2) (age_by k x3).
Proof.
  intros k x1 x2 x3 H.
  pose proof age_to_join_eq (level x3 - k) x1 x2 x3 H ltac:(omega) as G.
  pose proof join_level _ _ _ H as [e1 e2].
  exact_eq G; f_equal; unfold age_to.
  - rewrite <-e1; apply age_by_minusminus.
  - rewrite <-e2; apply age_by_minusminus.
  - apply age_by_minusminus.
Qed.

(* this generalizes [age_to_join_eq], but we do use [age_to_join_eq] inside this proof *)
Lemma age_to_join {A} {JA: Join A} {PA: Perm_alg A} {agA: ageable A} {AgeA: Age_alg A} :
  forall k x1 x2 x3,
    join x1 x2 x3 ->
    join (age_to k x1) (age_to k x2) (age_to k x3).
Proof.
  intros k x1 x2 x3 J.
  unfold age_to in *.
  pose proof age_by_join ((level x1 - k)%nat) _ _ _ J as G.
  exact_eq G; do 3 f_equal.
  all: apply join_level in J; destruct J; congruence.
Qed.

Lemma age_by_joins {A} {JA: Join A} {PA: Perm_alg A} {agA: ageable A} {AgeA: Age_alg A} :
  forall k x1 x2,
    joins x1 x2 ->
    joins (age_by k x1) (age_by k x2).
Proof.
  intros k x1 x2 [].
  eexists; apply age_by_join; eauto.
Qed.

Lemma age_to_joins {A} {JA: Join A} {PA: Perm_alg A} {agA: ageable A} {AgeA: Age_alg A} :
  forall k x1 x2,
    joins x1 x2 ->
    joins (age_to k x1) (age_to k x2).
Proof.
  intros k x1 x2 [].
  eexists; apply age_to_join; eauto.
Qed.

Lemma age_to_join_sub {A} {JA: Join A} {PA: Perm_alg A} {agA: ageable A} {AgeA: Age_alg A} :
  forall k x1 x2,
    join_sub x1 x2 ->
    join_sub (age_to k x1) (age_to k x2).
Proof.
  intros k x1 x3 [].
  eexists; apply age_to_join; eauto.
Qed.

Lemma joinlist_level {A} `{agA : ageable A} {J : Join A} {_ : Perm_alg A} {_ : Age_alg A} (x : A) l Phi :
  joinlist l Phi ->
  In x l -> level x = level Phi.
Proof.
  intros j i.
  destruct (joinlist_join_sub x Phi l j i) as (y, Hy).
  apply join_level in Hy. apply Hy.
Qed.

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

Require Import VST.veric.compcert_rmaps.
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

Context {ge : Clight.genv}.

Definition getLocksR (tp : jstate ge) := listoption_inv (map snd (AMap.elements (lset tp))).

Definition maps tp := (getThreadsR tp ++ getLocksR tp)%list.

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
  rewrite length_enum.
  pose proof @ssrnat.ltP i n.
  rewrite cnti in H.
  inversion H; auto.
Qed.

Lemma join_list_joinlist : join_list = joinlist.
Proof.
  extensionality l; induction l; extensionality phi; simpl; auto.
  f_equal. extensionality r. apply prop_ext.
  split; intros []; split; auto; simpl in *; congruence.
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
      simpl in *; rewrite h.
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
    simpl in *.
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
  - intros n j; specialize (IHl _ n j).
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
    + exists rt None; unfold l' in *; simpl in *.
      * hnf. rewrite join_list_joinlist. apply jt.
      * hnf. unfold l' in D.
        rewrite join_list'_None.
        simpl in *.
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

Lemma minus_plus a b c : a - (b + c) = a - b - c.
Proof.
  omega.
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
      rewrite <-minus_n_O in *.
      rewrite <-minus_n_O in *.
      intros Hi.
      simpl.
      f_equal.
      f_equal.
      apply proof_irr.
    + simpl minus in *.
      revert Hi.
      rewrite <-minus_n_O in *.
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
        reflexivity.
      * omega.
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
      omega.
    + match goal with
        |- Some (fintype.Ordinal (n:=n) (m:=n - 1 - (n - i - 1)) ?H) = _ =>
        generalize H
      end.
      pose proof (ssrbool.elimT ssrnat.leP pr).
      assert (R : (n - 1 - (n - i - 1) = i)%nat) by omega.
      rewrite R in *.
      intros pr'.
      do 2 f_equal.
      apply proof_irr.
    + pose proof (ssrbool.elimT ssrnat.leP pr).
      omega.
Qed.

Instance JSem : Semantics := ClightSemanticsForMachines.Clight_newSem ge.

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
  2:now rewrite map_length, length_enum_from; auto.
  rewrite map_length, length_enum_from.
  match goal with
    |- _ = Some (?a ?x) =>
    change (Some (a x)) with (option_map a (Some x))
  end.
  f_equal.
  Set Printing Implicit.
  generalize (Nat.le_refl n) as pr.
  rename n into m.
  assert (Ei : (i = (m - 1 - (m - 1 - i)))%nat). {
    pose proof (ssrbool.elimT ssrnat.leP cnti).
    rewrite <- !Nat.sub_add_distr, Nat.add_comm, Nat.sub_add_distr.
    replace (m - (m - (1 + i)))%nat with (S i); omega.
  }
  assert (cnti' : is_true (ssrnat.leq (S (m - 1 - (m - 1 - i))) m))
    by congruence.
  replace (@fintype.Ordinal m i cnti)
  with (@fintype.Ordinal m (m - 1 - (m - 1 - i)) cnti')
    by (revert cnti'; rewrite <-Ei; intros; f_equal; apply proof_irr).
  assert (li' : (m - 1 - i < m)%nat) by (clear -li; omega).
  clear cnti Ei. revert li' cnti'.
  generalize (m - 1 - i)%nat; clear i li; intros i.
  generalize m at 1 2 4 7 13 14; intros n; revert i.
  induction n; intros i li cnti Hnm. now inversion li.
  match goal with |- _ = Some (map ?F _) => set (f := F) end.
  Unset Printing Implicit.
  destruct i.
  - simpl.
    f_equal.
    f_equal.
    + unfold f; simpl.
      rewrite eqtype_refl'. reflexivity. omega.
    + clear.
      unfold f; clear f. simpl in cnti.
      simpl.
      revert cnti; replace (n - 0 - 0)%nat with n by omega; intros cnti.
      revert cnti; assert (H : le n n) by auto; revert H.
      generalize n at 2 3 9; intros a la cnta.
      induction n. auto.
      simpl; f_equal.
      * rewrite eqtype_neq. 2:omega.
        auto.
      * unshelve erewrite IHn. 2:omega.
        auto.
  - simpl.
    erewrite IHn.
    2:omega.
    f_equal.
    f_equal.
    + unfold f.
      simpl.
      rewrite eqtype_neq. 2:omega.
      reflexivity.
    + unfold f.
      f_equal.
      extensionality x.
      destruct x as [j lj].
      destruct (eq_dec j (n - 1 - i)%nat).
      * rewrite eqtype_refl'; auto.
        rewrite eqtype_refl'; auto.
        omega.
      * rewrite eqtype_neq; auto.
        rewrite eqtype_neq; auto.
        omega.
  Unshelve. (* unshelving at "erewrite IHn." above makes the proof fail *)
  clear -cnti. exact_eq cnti; do 3 f_equal. omega.
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
  transitivity
    ((getThreadR cnti :: all_but i (getThreadsR tp)) ++ getLocksR tp); auto.
  rewrite <-getThreadsR_but. reflexivity.
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
  unfold maps; f_equal.
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
  change (phi :: getThreadsR tp ++ getLocksR tp)
  with ((phi :: getThreadsR tp) ++ getLocksR tp).
  apply Permutation_app_tail.
  rewrite Permutation_cons_append.
  rewrite getThreadsR_addThread.
  apply Permutation_refl.
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
  maps (remLockSet (@updThread _ _ _ i tp cnti c phi) addr) =
  maps (@updThread _ _ _ i (remLockSet tp addr) cnti c phi).
Proof.
  reflexivity.
Qed.

Lemma getThread_level i tp cnti Phi :
  join_all tp Phi ->
  level (@getThreadR _ _ _ i tp cnti) = level Phi.
Proof.
  intros j.
  apply juicy_mem.rmap_join_sub_eq_level, compatible_threadRes_sub, j.
Qed.

Lemma join_sub_level {A} `{JA : sepalg.Join A} `{_ : ageable A} {_ : Perm_alg A} {_ : Age_alg A} :
  forall x y : A, join_sub x y -> level x = level y.
Proof.
  intros x y (z, j).
  apply (join_level _ _ _ j).
Qed.

Lemma joins_level {A} `{JA : sepalg.Join A} `{_ : ageable A} {_ : Perm_alg A} {_ : Age_alg A} :
  forall x y : A, joins x y -> level x = level y.
Proof.
  intros x y (z, j).
  destruct (join_level _ _ _ j); congruence.
Qed.

End Machine.
