Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

Require Import VST.zlist.sublist.
Require Import VST.floyd.base2.

Import ListNotations.
Local Open Scope Z.

Corollary Znth_app1 : forall {A}{d: Inhabitant A} l1 (x : A) l2 i,
     Zlength l1 = i -> Znth i (l1 ++ x :: l2) = x.
(* should use app_Znth2 instead *)
Proof.
  intros. list_solve.
Qed.

Lemma in_insert_iff : forall {A} (x y : A) l1 l2, In x (l1 ++ y :: l2) <-> x = y \/ In x (l1 ++ l2).
(* should use in_elt or in_elt_inv instead *)
Proof.
  intros; rewrite !in_app; split; simpl; intros [|[|]]; auto.
Qed.

Lemma nth_last : forall {A} (d : A) l, nth (length l - 1) l d = last l d.
Proof.
  induction l; auto.
  simpl nth.
  destruct (length l) eqn: Hlen.
  { destruct l; simpl in *; [auto | lia]. }
  rewrite last_cons; simpl in *; [|intro; subst; discriminate].
  rewrite NPeano.Nat.sub_0_r in IHl; auto.
Qed.

Lemma last_app : forall {A} l1 l2 (d : A), l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
  induction l1; auto; intros.
  setoid_rewrite last_cons; eauto.
  intro X; apply app_eq_nil in X; tauto.
Qed.

Lemma Forall2_In_l : forall {A B} (P : A -> B -> Prop) x l1 l2, Forall2 P l1 l2 -> In x l1 ->
  exists y, In y l2 /\ P x y.
Proof.
  induction 1; intro Hin; destruct Hin; simpl.
  - subst; eauto.
  - destruct IHForall2 as (? & ? & ?); eauto.
Qed.

Lemma Forall2_In_r : forall {A B} (P : A -> B -> Prop) x l1 l2, Forall2 P l1 l2 -> In x l2 ->
  exists y, In y l1 /\ P y x.
Proof.
  induction 1; intro Hin; destruct Hin; simpl.
  - subst; eauto.
  - destruct IHForall2 as (? & ? & ?); eauto.
Qed.

Lemma Znth_last : forall {A}{d: Inhabitant A} (l: list A), Znth (Zlength l - 1) l = last l default.
Proof.
  intros; unfold Znth.
  destruct (Z_lt_dec (Zlength l - 1) 0).
  - destruct l; auto.
    rewrite Zlength_correct in *; simpl length in *.
    rewrite Nat2Z.inj_succ in *; lia.
  - rewrite Z2Nat.inj_sub; [|lia].
    rewrite Zlength_correct, Nat2Z.id; simpl.
    apply nth_last.
Qed.

Definition rotate {A} (l : list A) n m := sublist (m - n) (Zlength l) l ++
  sublist 0 (m - n) l.

Lemma upd_rotate : forall {A} i (l : list A) n m x (Hl : Zlength l = m) (Hlt : 0 <= n <= m)
  (Hi : 0 <= i < Zlength l),
  upd_Znth i (rotate l n m) x = rotate (upd_Znth ((i - n) mod m) l x) n m.
Proof.
  intros; unfold rotate.
  rewrite upd_Znth_Zlength by (subst; apply Z_mod_lt; lia).
  destruct (zlt i (Zlength l - (m - n))).
  - rewrite upd_Znth_app1 by (rewrite Zlength_sublist; lia).
    assert ((i - n) mod m = m + i - n) as Hmod.
    { rewrite <- Z.mod_add with (b := 1) by lia.
      rewrite Zmod_small; lia. }
    rewrite Hmod, sublist_upd_Znth_lr, sublist_upd_Znth_l by (auto; lia).
    replace (m + i - n - (m - n)) with i by lia; auto.
  - rewrite upd_Znth_app2; rewrite ?Zlength_sublist; try lia.
    assert ((i - n) mod m = i - n) as Hmod.
    { rewrite Zmod_small; lia. }
    rewrite Hmod, sublist_upd_Znth_r, sublist_upd_Znth_lr by lia.
    replace (i - (Zlength l - (m - n))) with (i - n - 0) by lia; auto.
Qed.

Lemma Znth_rotate : forall {A} {d : Inhabitant A} i (l: list A) n,
    0 <= n <= Zlength l -> 0 <= i < Zlength l ->
  Znth i (rotate l n (Zlength l)) = Znth ((i - n) mod Zlength l) l.
Proof.
  intros; unfold rotate.
  destruct (zlt i n).
  - rewrite app_Znth1 by (rewrite Zlength_sublist; lia).
    rewrite Znth_sublist by lia.
    rewrite <- Z_mod_plus with (b := 1), Zmod_small by lia.
    f_equal; lia.
  - rewrite app_Znth2; (rewrite Zlength_sublist; try lia).
    rewrite Znth_sublist by lia.
    rewrite Zmod_small by lia.
    f_equal; lia.
Qed.

Lemma rotate_nil : forall {A} n m, rotate (@nil A) n m = [].
Proof.
  intros; unfold rotate; rewrite !sublist_of_nil; auto.
Qed.

Lemma Forall_sublist_le : forall {A} {d : Inhabitant A} (P : A -> Prop) i j l
  (Hrangei : 0 <= i) (Hrangej : j <= Zlength l) (Hi : ~P (Znth i l)) (Hj : Forall P (sublist 0 j l)),
  j <= i.
Proof.
  intros.
  destruct (Z_le_dec j i); auto.
  pose proof (proj1 (Forall_Znth _ _) Hj i).
  rewrite Zlength_sublist in H by lia.
  rewrite Znth_sublist, Z.add_0_r in H by lia.
  contradiction Hi; apply H. lia.
Qed.

Corollary Forall_sublist_first : forall {A} {d : Inhabitant A} (P : A -> Prop) i j l
  (Hrangei : 0 <= i <= Zlength l) (Hi : Forall P (sublist 0 i l)) (Hi' : ~P (Znth i l))
  (Hrangej : 0 <= j <= Zlength l) (Hj : Forall P (sublist 0 j l)) (Hj' : ~P (Znth j l)),
  i = j.
Proof.
  intros.
  apply Z.le_antisymm; eapply Forall_sublist_le; eauto; lia.
Qed.

Lemma rotate_In : forall {A} (x : A) n m l, 0 <= m - n <= Zlength l -> In x (rotate l n m) <-> In x l.
Proof.
  unfold rotate; intros.
  replace l with (sublist 0 (m - n) l ++ sublist (m - n) (Zlength l) l) at 4
    by (rewrite sublist_rejoin, sublist_same; auto; lia).
  rewrite !in_app; tauto.
Qed.

Lemma rotate_map : forall {A B} (f : A -> B) n m l, rotate (map f l) n m = map f (rotate l n m).
Proof.
  intros; unfold rotate.
  rewrite !sublist_map, Zlength_map, map_app; auto.
Qed.

Lemma Forall_rotate : forall {A} P (l : list A) n m, Forall P l ->
  Forall P (rotate l m n).
Proof.
  intros; unfold rotate.
  rewrite Forall_app; split; apply Forall_sublist; auto.
Qed.

Definition complete MAX l := l ++ Zrepeat (Vptrofs (Ptrofs.repr 0)) (MAX - Zlength l).

Lemma upd_complete : forall l x MAX, Zlength l < MAX ->
  upd_Znth (Zlength l) (complete MAX l) x = complete MAX (l ++ [x]).
Proof.
  intros. unfold complete.
  list_solve.
Qed.

Lemma Znth_complete : forall n l MAX, n < Zlength l ->
     Znth n (complete MAX l) = Znth n l.
Proof.
  intros; apply app_Znth1; auto.
Qed.

Lemma remove_complete : forall l x MAX, Zlength l < MAX ->
  upd_Znth (Zlength l) (complete MAX (l ++ [x])) (Vptrofs (Ptrofs.repr 0)) = complete MAX l.
Proof.
  intros; unfold complete.
  list_solve.
Qed.

Lemma Forall_complete : forall P l m, Forall P l -> P (Vptrofs (Ptrofs.repr 0)) ->
  Forall P (complete m l).
Proof.
  intros; unfold complete.
  rewrite Forall_app; split; [|apply Forall_repeat]; auto.
Qed.

Lemma rotate_inj : forall {A} (l1 l2 : list A) n m, rotate l1 n m = rotate l2 n m ->
  length l1 = length l2 -> 0 <= n <= m -> m <= Zlength l1 -> l1 = l2.
Proof.
  unfold rotate; intros.
  destruct (list_append_injective_l _ _ _ _ H) as (Hskip & Hfirst).
  { unfold sublist; repeat rewrite skipn_length, firstn_length.
    repeat rewrite Zlength_correct; rewrite H0; lia. }
  erewrite <- sublist_same with (al := l1), <- sublist_rejoin with (mid := m - n); auto; try lia.
  rewrite Hfirst, Hskip, sublist_rejoin, sublist_same; auto; try lia.
  repeat rewrite Zlength_correct in *; rewrite H0 in *; lia.
Qed.

Lemma complete_inj : forall l1 l2 m, complete m l1 = complete m l2 ->
  length l1 = length l2 -> l1 = l2.
Proof.
  unfold complete; intros.
  destruct (list_append_injective_l _ _ _ _ H); auto.
Qed.

Lemma length_complete : forall l m, Zlength l <= m -> length (complete m l) = Z.to_nat m.
Proof.
  intros; unfold complete.
  rewrite <- ZtoNat_Zlength.
  f_equal.
  list_solve.
Qed.

Lemma Zlength_rotate : forall {A} (l : list A) n m, 0 <= n <= m -> m <= Zlength l ->
  Zlength (rotate l n m) = Zlength l.
Proof.
  intros; unfold rotate.
  rewrite Zlength_app; repeat rewrite Zlength_sublist; lia.
Qed.

Lemma Zlength_complete : forall l m, Zlength l <= m -> Zlength (complete m l) = m.
Proof.
  intros; unfold complete.
  list_solve.
Qed.

Lemma combine_eq : forall {A B} (l : list (A * B)), combine (map fst l) (map snd l) = l.
Proof.
  induction l; auto; simpl.
  destruct a; rewrite IHl; auto.
Qed.

Lemma signed_inj : forall i1 i2, Int.signed i1 = Int.signed i2 -> i1 = i2.
Proof.
  intros.
  apply int_eq_e.
  rewrite Int.eq_signed, H.
  apply zeq_true.
Qed.

Lemma mods_repr : forall a b, 0 <= a <= Int.max_signed -> 0 < b <= Int.max_signed ->
  Int.mods (Int.repr a) (Int.repr b) = Int.repr (a mod b).
Proof.
  intros.
  unfold Int.mods.
  pose proof Int.min_signed_neg.
  rewrite Zquot.Zrem_Zmod_pos; repeat rewrite Int.signed_repr; auto; lia.
Qed.

Lemma Znth_head : forall reqs head m, Zlength reqs <= m -> 0 <= head < m ->
  Zlength reqs > 0 ->
  Znth head (rotate (complete m reqs) head m) = Znth 0 reqs.
Proof.
  intros; unfold rotate.
  assert (Zlength (sublist (m - head) (Zlength (complete m reqs)) (complete m reqs)) = head) as Hlen.
  {
rewrite Zlength_sublist; rewrite Zlength_complete; lia. }
  rewrite app_Znth2; rewrite Hlen; [|lia].
  rewrite Zminus_diag.
  rewrite Znth_sublist; try lia.
  rewrite Znth_complete; auto; lia.
Qed.

Lemma Znth_repeat : forall {A} {x : Inhabitant A} n i, Znth i (@repeat A default n) = default.
Proof.
  induction n; simpl; intro.
  - apply Znth_nil.
  - destruct (Z_lt_dec i 0); [apply Znth_underflow; auto|].
    destruct (eq_dec i 0); [subst; apply Znth_0_cons | rewrite Znth_pos_cons; eauto; lia].
Qed.

Lemma Znth_repeat' : forall {A} {d: Inhabitant A} (x : A) n i,
    0 <= i < Z.of_nat n -> Znth i (repeat x n)  = x.
Proof.
  intros. pose proof (Znth_repeat_inrange i (Z.of_nat n) x H). now rewrite Nat2Z.id in H0.
Qed.

Lemma rotate_1 : forall v l n m, 0 <= n < m -> Zlength l < m ->
  rotate (upd_Znth 0 (complete m (v :: l)) (Vptrofs (Ptrofs.repr 0))) n m =
  rotate (complete m l) ((n + 1) mod m) m.
Proof.
  intros.
  unfold complete, rotate.
  destruct (eq_dec n (m-1)).
  - subst n.
    replace (m - 1 + 1) with m by lia.
    replace (m mod m) with 0 by (rewrite Z_mod_same_full; auto).
    list_solve.
  - replace ((n+1) mod m) with (n+1) by (rewrite Z.mod_small; lia).
    list_solve.
Qed.

Lemma upd_complete_gen : forall {A} (l : list A) x n y, Zlength l < n ->
  upd_Znth (Zlength l) (l ++ repeat y (Z.to_nat (n - Zlength l))) x =
  (l ++ [x]) ++ repeat y (Z.to_nat (n - Zlength (l ++ [x]))).
Proof.
  intros.
  rewrite upd_Znth_app2, Zminus_diag.
  destruct (Z.to_nat (n - Zlength l)) eqn: Hn.
  - apply Z2Nat.inj with (m := 0) in Hn; lia.
  - simpl; rewrite upd_Znth0.
    rewrite <- app_assoc, Zlength_app, Zlength_cons, Zlength_nil; simpl.
    rewrite Z.sub_add_distr, Z2Nat.inj_sub, Hn by computable; simpl.
    rewrite Nat.sub_0_r; auto.
  - pose proof (Zlength_nonneg (repeat y (Z.to_nat (n - Zlength l)))); lia.
Qed.

Lemma upd_complete_gen' : forall {A B} (f : A -> B) (l : list A) x n y, Zlength l < n ->
  upd_Znth (Zlength l) (map f l ++ repeat y (Z.to_nat (n - Zlength l))) (f x) =
  map f (l ++ [x]) ++ repeat y (Z.to_nat (n - Zlength (l ++ [x]))).
Proof.
  intros.
  rewrite <- (Zlength_map _ _ f l), upd_complete_gen, map_app, !Zlength_app; rewrite Zlength_map; auto.
Qed.

Lemma upd_init : forall {A} (l : list A) i b v v', i < b -> Zlength l = i ->
  upd_Znth i (l ++ repeat v (Z.to_nat (b - i))) v' = l ++ v' :: repeat v (Z.to_nat (b - (i + 1))).
Proof.
  intros.
  rewrite upd_Znth_app2; rewrite ?Zlength_repeat, ?Z2Nat.id; try lia.
  subst; rewrite Zminus_diag, upd_Znth0_old. 2 : {
    rewrite Zlength_repeat; lia. }
  destruct (Z.to_nat (b - Zlength l)) eqn: Hi.
  { change O with (Z.to_nat 0) in Hi; apply Z2Nat.inj in Hi; lia. }
  simpl; rewrite sublist_1_cons, sublist_same; try rewrite Zlength_cons, !coqlib4.Zlength_repeat; try lia.
  replace (Z.to_nat (b - (Zlength l + 1))) with n; auto.
  lia.
Qed.

Corollary upd_init_const : forall {A} i b (v v' : A), 0 <= i < b ->
  upd_Znth i (repeat v' (Z.to_nat i) ++ repeat v (Z.to_nat (b - i))) v' =
  repeat v' (Z.to_nat (i + 1)) ++ repeat v (Z.to_nat (b - (i + 1))).
Proof.
  intros.
  rewrite upd_init; try rewrite coqlib4.Zlength_repeat, Z2Nat.id; auto; try lia.
  rewrite Z2Nat.inj_add, repeat_app, <- app_assoc; auto; lia.
Qed.

Lemma list_Znth_eq : forall {A}{d: Inhabitant A} (l : list A),
    l = map (fun j => Znth j l) (upto (length l)).
Proof.
  induction l; simpl; intros; auto.
  rewrite Znth_0_cons, IHl, map_map, map_length, upto_length.
  f_equal; apply map_ext_in; intros.
  rewrite Znth_pos_cons, <- IHl.
  unfold Z.succ; rewrite Z.add_simpl_r; auto.
  { rewrite In_upto in *; lia. }
Qed.

Arguments eq_dec _ _ _ _ : simpl never.

Lemma upd_Znth_eq : forall {A} {EqDec : EqDec A} {d: Inhabitant A} (x : A) (l : list A) i, 0 <= i < Zlength l ->
  upd_Znth i l x = map (fun j => if eq_dec j i then x else Znth j l) (upto (length l)).
Proof.
  induction l; simpl; intros.
  { rewrite Zlength_nil in *; lia. }
  destruct (eq_dec 0 i).
  - subst; rewrite upd_Znth0.
    rewrite (list_Znth_eq l) at 1.
    rewrite map_map.
    f_equal; apply map_ext_in; intros.
    rewrite In_upto in *.
    destruct (eq_dec (Z.succ a0) 0); [lia|].
    rewrite Znth_pos_cons; [|lia].
    f_equal; lia.
  - rewrite Znth_0_cons, upd_Znth_cons; [|lia].
    rewrite Zlength_cons in *.
    rewrite IHl, map_map; [|lia].
    f_equal; apply map_ext_in; intros.
    rewrite In_upto in *.
    destruct (eq_dec a0 (i - 1)), (eq_dec (Z.succ a0) i); try lia; auto.
    rewrite Znth_pos_cons; [|lia].
    f_equal; lia.
Qed.

Lemma Permutation_Zlength : forall {A} (l1 l2 : list A), Permutation.Permutation l1 l2 ->
  Zlength l1 = Zlength l2.
Proof.
  intros; apply Z2Nat.inj; try apply Zlength_nonneg.
  rewrite !ZtoNat_Zlength; apply Permutation.Permutation_length; auto.
Qed.

Lemma Permutation_filter : forall {A} (f : A -> bool) l1 l2, Permutation.Permutation l1 l2 ->
  Permutation.Permutation (filter f l1) (filter f l2).
Proof.
  induction 1; simpl; auto.
  - destruct (f x); auto.
  - destruct (f x); auto. destruct (f y); auto.
    constructor.
  - etransitivity; eauto.
Qed.

Lemma NoDup_add : forall {A} l1 l2 (x : A), NoDup (l1 ++ l2) -> ~In x (l1 ++ l2) -> NoDup (l1 ++ x :: l2).
Proof.
  induction l1; simpl; intros.
  - constructor; auto.
  - inv H; constructor; auto.
    rewrite in_app in *; simpl; intros [? | [? | ?]]; subst; tauto.
Qed.

Lemma list_in_count : forall {A} {A_eq : EqDec A} (l l' : list A), NoDup l' ->
  (length (filter (fun x => if in_dec eq_dec x l then true else false) l') <= length l)%nat.
Proof.
  intros.
  apply NoDup_incl_length; [apply NoDup_filter; auto|].
  intros ? Hin.
  rewrite filter_In in Hin; destruct Hin.
  destruct (in_dec eq_dec a l); [auto | discriminate].
Qed.

Lemma Zlength_concat_le : forall {A} (l : list (list A)) n,
  Forall (fun l => Zlength l <= n) l -> Zlength (concat l) <= n * Zlength l.
Proof.
  intros; rewrite Zlength_concat.
  rewrite <- (Z.add_0_l (n * Zlength l)).
  forget 0 as m; revert m.
  induction H; simpl; intro.
  - rewrite Zlength_nil; lia.
  - rewrite Zlength_cons, Z.mul_succ_r.
    specialize (IHForall m); lia.
Qed.

Lemma NoDup_upto : forall n, NoDup (upto n).
Proof.
  induction n; simpl; constructor.
  - rewrite in_map_iff.
    intros (? & ? & ?); rewrite In_upto in *; lia.
  - apply FinFun.Injective_map_NoDup; auto.
    intros ???; lia.
Qed.

Lemma In_remove : forall {A} {A_eq : EqDec A} (x y : A) l, In x (remove A_eq y l) <-> In x l /\ x <> y.
Proof.
  induction l; simpl; intros; [tauto|].
  destruct (A_eq y a); simpl; rewrite IHl; repeat split; try tauto.
  - destruct H as [[|]]; auto; subst; contradiction.
  - destruct H as [|[]]; subst; auto.
Qed.

Lemma remove_NoDup : forall {A} {A_eq : EqDec A} (x : A) l, NoDup l -> NoDup (remove A_eq x l).
Proof.
  induction 1; simpl.
  - constructor.
  - if_tac; auto.
    constructor; auto.
    intro X; apply In_remove in X; destruct X; contradiction.
Qed.

Lemma remove_from_NoDup : forall {A} {A_eq : EqDec A} (x : A) l1 l2, NoDup (l1 ++ x :: l2) ->
  remove A_eq x (l1 ++ x :: l2) = l1 ++ l2.
Proof.
  induction l1; simpl; intros.
  - if_tac; [|contradiction].
    inv H; apply notin_remove; auto.
  - inversion H as [|?? Hx]; subst.
    rewrite IHl1 by auto.
    if_tac; auto.
    subst; contradiction Hx; rewrite in_app; simpl; auto.
Qed.

Lemma incl_remove_add : forall {A} {A_eq : EqDec A} (x : A) l1 l2, incl l1 l2 -> incl l1 (x :: remove A_eq x l2).
Proof.
  intros; intros ? Hin; specialize (H _ Hin).
  simpl; rewrite In_remove.
  destruct (eq_dec a x); auto.
Qed.

Lemma list_pigeonhole : forall l n, Zlength l < n -> exists a, 0 <= a < n /\ ~In a l.
Proof.
  intros.
  pose proof (filter_length (fun x => if in_dec eq_dec x l then true else false) (upto (Z.to_nat n))) as Hlen.
  rewrite upto_length in Hlen.
  assert (length (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n))) > 0)%nat.
  { exploit (list_in_count l (upto (Z.to_nat n))).
    { apply NoDup_upto. }
    rewrite Zlength_correct in H. lia. }
  destruct (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n))) eqn: Hfilter;
    [simpl in *; lia|].
  assert (In z (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n)))) as Hin
    by (rewrite Hfilter; simpl; auto).
  rewrite filter_In, In_upto, Z2Nat.id in Hin; [|rewrite Zlength_correct in *; lia].
  destruct Hin; destruct (in_dec eq_dec z l); try discriminate; eauto.
Qed.

Lemma sublist_prefix : forall {A} i j (l : list A), sublist 0 i (sublist 0 j l) = sublist 0 (Z.min i j) l.
 (* should really use sublist_sublist00 if possible *)
Proof.
  intros.
  destruct (Z_le_dec i 0).
  { rewrite !sublist_nil_gen; auto.
    rewrite Z.min_le_iff; auto. }
  destruct (Z.min_spec i j) as [(? & ->) | (? & ->)].
  - rewrite sublist_sublist, !Z.add_0_r by lia; auto.
  - apply sublist_same_gen; auto.
    destruct (Z_le_dec j 0); [rewrite sublist_nil_gen; auto; rewrite Zlength_nil; lia|].
    destruct (Z_le_dec j (Zlength l)).
    rewrite Zlength_sublist; try lia.
    { pose proof (sublist_max_length 0 j l); lia. }
Qed.

Lemma sublist_suffix : forall {A} i j (l : list A), 0 <= i -> 0 <= j ->
  sublist i (Zlength l - j) (sublist j (Zlength l) l) = sublist (i + j) (Zlength l) l.
Proof.
  intros.
  destruct (Z_le_dec (Zlength l - j) i).
  { rewrite !sublist_nil_gen; auto; lia. }
  rewrite sublist_sublist by lia.
  rewrite Z.sub_simpl_r; auto.
Qed.

Lemma sublist_parts1 : forall {A} i j (l : list A), 0 <= i -> sublist i j l = sublist i j (sublist 0 j l).
Proof.
  intros.
  destruct (Z_le_dec j i).
  { rewrite !sublist_nil_gen; auto. }
  rewrite sublist_sublist by lia.
  rewrite !Z.add_0_r; auto.
Qed.

Lemma sublist_parts2 : forall {A} i j (l : list A), 0 <= i -> j <= Zlength l ->
  sublist i j l = sublist 0 (j - i) (sublist i (Zlength l) l).
Proof.
  intros.
  destruct (Z_le_dec j i).
  { rewrite !sublist_nil_gen; auto; lia. }
  rewrite sublist_sublist; try lia.
  rewrite Z.add_0_l, Z.sub_simpl_r; auto.
Qed.

Lemma Forall_Forall2 : forall {A} (P : A -> Prop) Q l1 l2 (HP : Forall P l1) (HQ : Forall2 Q l1 l2)
  (Htransfer : forall x y, P x -> Q x y -> P y), Forall P l2.
Proof.
  induction 2; auto; intros.
  inv HP.
  constructor; eauto.
Qed.

Lemma Forall_suffix_max : forall {A} (P : A -> Prop) l1 l2 i j
  (Hi : 0 <= i <= Zlength l1) (Hj : 0 <= j <= Zlength l1)
  (Hl1 : Forall P (sublist j (Zlength l1) l1))
  (Hl2 : sublist i (Zlength l1) l1 = sublist i (Zlength l2) l2),
  Forall P (sublist (Z.max i j) (Zlength l2) l2).
Proof.
  intros.
  destruct (eq_dec i (Zlength l1)).
  { subst; rewrite sublist_nil in Hl2.
    rewrite Z.max_l by lia.
    rewrite <- Hl2; auto. }
  assert (Zlength l1 = Zlength l2) as Heq.
  { assert (Zlength (sublist i (Zlength l1) l1) = Zlength (sublist i (Zlength l2) l2)) as Heq by congruence.
    destruct (Z_le_dec (Zlength l2) i).
    { rewrite (sublist_nil_gen l2), Zlength_nil in Heq; auto.
      rewrite !Zlength_sublist in Heq; lia. }
    rewrite !Zlength_sublist in Heq; lia. }
  intros; destruct (Z.max_spec i j) as [(? & ->) | (? & ->)].
  - replace (sublist _ _ _) with (sublist (j - i) (Zlength l2 - i) (sublist i (Zlength l2) l2)).
    rewrite <- Hl2, sublist_sublist, !Z.sub_simpl_r by lia.
    rewrite <- Heq; auto.
    { rewrite sublist_sublist, !Z.sub_simpl_r by lia; auto. }
  - rewrite <- Hl2.
    replace (sublist _ _ _) with (sublist (i - j) (Zlength l1 - j) (sublist j (Zlength l1) l1)).
    apply Forall_sublist; auto.
    { rewrite sublist_sublist, !Z.sub_simpl_r; auto; lia. }
Qed.

Fixpoint extend {A} (l : list A) ls :=
  match l, ls with
  | x :: xs, y :: ys => (x :: y) :: extend xs ys
  | _, _ => ls
  end.

Lemma Zlength_extend : forall {A} (l : list A) ls, Zlength (extend l ls) = Zlength ls.
Proof.
  induction l; destruct ls; auto; simpl.
  rewrite !Zlength_cons, IHl; auto.
Qed.

Lemma Znth_extend_in : forall {A}{d: Inhabitant A}  (l : list A) ls i, 0 <= i < Zlength l -> Zlength l <= Zlength ls ->
  Znth i (extend l ls) = Znth i l :: Znth i ls.
Proof.
  induction l; destruct ls; simpl; intros; try rewrite Zlength_nil in *; try lia.
  rewrite !Zlength_cons in *.
  destruct (eq_dec i 0); subst; auto.
  rewrite !Znth_pos_cons; try lia.
  apply IHl; lia.
Qed.

Lemma Znth_extend_ge : forall {A}{d: Inhabitant A}  (l : list A) ls i, Zlength l <= i ->
  Znth i (extend l ls) = Znth i ls.
Proof.
  induction l; destruct ls; auto; simpl; intros.
  destruct (zlt i 0); [rewrite !Znth_underflow; auto|].
  rewrite Zlength_cons in *.
  destruct (eq_dec i 0); [rewrite Zlength_correct in *; lia|].
  rewrite !Znth_pos_cons; try lia.
  apply IHl; lia.
Qed.

Fixpoint extendr {A} (l : list A) ls :=
  match l, ls with
  | x :: xs, y :: ys => (y ++ [x]) :: extendr xs ys
  | _, _ => ls
  end.

Lemma Zlength_extendr : forall {A} (l : list A) ls, Zlength (extendr l ls) = Zlength ls.
Proof.
  induction l; destruct ls; auto; simpl.
  rewrite !Zlength_cons, IHl; auto.
Qed.

Lemma Znth_extendr_in : forall {A}{d: Inhabitant A}  (l : list A) ls i, 0 <= i < Zlength l -> Zlength l <= Zlength ls ->
  Znth i (extendr l ls) = Znth i ls ++ [Znth i l].
Proof.
  induction l; destruct ls; simpl; intros; try rewrite Zlength_nil in *; try lia.
  rewrite !Zlength_cons in *.
  destruct (eq_dec i 0); subst; auto.
  rewrite !Znth_pos_cons; try lia.
  apply IHl; lia.
Qed.

Lemma Znth_extendr_ge : forall {A}{d: Inhabitant A}  (l : list A) ls i, Zlength l <= i ->
  Znth i (extendr l ls) = Znth i ls.
Proof.
  induction l; destruct ls; auto; simpl; intros.
  destruct (zlt i 0); [rewrite !Znth_underflow; auto|].
  rewrite Zlength_cons in *.
  destruct (eq_dec i 0); [rewrite Zlength_correct in *; lia|].
  rewrite !Znth_pos_cons; try lia.
  apply IHl; lia.
Qed.

Lemma extend_nil : forall {A} (l : list A), extend l [] = [].
Proof.
  destruct l; auto.
Qed.

Lemma extend_cons : forall {A} (l : list A) l1 ls, extend l (l1 :: ls) =
  match l with [] => l1 :: ls | a :: l' => (a :: l1) :: extend l' ls end.
Proof.
  destruct l; auto.
Qed.

Lemma sublist_extend : forall {A} (l : list A) ls i j,
  sublist i j (extend l ls) = extend (sublist i j l) (sublist i j ls).
Proof.
  induction l; simpl; intros.
  - unfold sublist; rewrite firstn_nil, skipn_nil; auto.
  - destruct ls.
    + unfold sublist; rewrite firstn_nil, skipn_nil, extend_nil; auto.
    + destruct (Z_le_dec j 0); [rewrite !sublist_nil_gen'; auto|].
      destruct (Z_le_dec i 0).
      * subst; rewrite !sublist_0_cons'; try lia.
        rewrite IHl; auto.
      * rewrite !sublist_S_cons; auto; lia.
Qed.

Lemma extendr_nil : forall {A} (l : list A), extendr l [] = [].
Proof.
  destruct l; auto.
Qed.

Lemma extendr_cons : forall {A} (l : list A) l1 ls, extendr l (l1 :: ls) =
  match l with [] => l1 :: ls | a :: l' => (l1 ++ [a]) :: extendr l' ls end.
Proof.
  destruct l; auto.
Qed.

Lemma sublist_extendr : forall {A} (l : list A) ls i j,
  sublist i j (extendr l ls) = extendr (sublist i j l) (sublist i j ls).
Proof.
  induction l; simpl; intros.
  - unfold sublist; rewrite firstn_nil, skipn_nil; auto.
  - destruct ls.
    + unfold sublist; rewrite firstn_nil, skipn_nil, extendr_nil; auto.
    + destruct (Z_le_dec j 0); [rewrite !sublist_nil_gen'; auto|].
      destruct (Z_le_dec i 0).
      * subst; rewrite !sublist_0_cons'; try lia.
        rewrite IHl; auto.
      * rewrite !sublist_S_cons; auto; lia.
Qed.

Lemma sublist_over : forall {A} (l : list A) i j, Zlength l <= i -> sublist i j l = [].
Proof.
  intros. assert (i >= 0) by rep_lia; unfold_sublist_old.
  rewrite skipn_short, firstn_nil; auto.
  rewrite Zlength_correct in *; rep_lia.
Qed.
