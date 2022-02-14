Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

Require Import VST.floyd.sublist.
Require Import VST.floyd.proofauto.

Import ListNotations.
Local Open Scope Z.

(* rewrite is really annoying to fix in a backwards compatible way so just set the option. *)
Local Set Apply With Renaming.

Lemma Forall_forall_Znth : forall {A}{d: Inhabitant A} (P : A -> Prop) l,
  Forall P l <-> forall i, 0 <= i < Zlength l -> P (Znth i l).
Proof.
  split; intros; [apply Forall_Znth; auto|].
  induction l; auto.
  rewrite Zlength_cons in *.
  constructor.
  - specialize (H 0); rewrite Znth_0_cons in H; apply H.
    pose proof (Zlength_nonneg l); lia.
  - apply IHl; intros.
    specialize (H (i + 1)).
    rewrite Znth_pos_cons, Z.add_simpl_r in H by lia.
    apply H; lia.
Qed.

Lemma Znth_app : forall {A}{d: Inhabitant A} (l1 l2 : list A) i,
      Zlength l1 = i -> Znth i (l1 ++ l2) = Znth 0 l2.
Proof.
  intros; subst; rewrite app_Znth2, Zminus_diag; auto; lia.
Qed.

Corollary Znth_app1 : forall {A}{d: Inhabitant A} l1 (x : A) l2 i,
     Zlength l1 = i -> Znth i (l1 ++ x :: l2) = x.
Proof.
  intros; rewrite Znth_app, Znth_0_cons; auto.
Qed.

Lemma Forall_upd_Znth : forall {A} (P : A -> Prop) x l i, Forall P l -> P x ->
  Forall P (upd_Znth i l x).
Proof.
  intros; unfold upd_Znth; if_tac; auto;
  rewrite Forall_app; split; [|constructor; auto]; apply Forall_sublist; auto.
Qed.

Lemma Forall_app : forall {A} (P : A -> Prop) l1 l2,
  Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  induction l1; split; auto; intros.
  - destruct H; auto.
  - inversion H as [|??? H']; subst.
    rewrite IHl1 in H'; destruct H'; split; auto.
  - destruct H as (H & ?); inv H; constructor; auto.
    rewrite IHl1; split; auto.
Qed.

Lemma Forall_incl : forall {A} (P : A -> Prop) l1 l2 (Hall : Forall P l2) (Hincl : incl l1 l2),
  Forall P l1.
Proof.
  intros; rewrite Forall_forall in *; eauto.
Qed.

Lemma repeat_plus : forall {A} (x : A) i j, repeat x (i + j) = repeat x i ++ repeat x j.
Proof.
  induction i; auto; simpl; intro.
  rewrite IHi; auto.
Qed.

Lemma in_insert_iff : forall {A} (x y : A) l1 l2, In x (l1 ++ y :: l2) <-> x = y \/ In x (l1 ++ l2).
Proof.
  intros; rewrite !in_app; split; simpl; intros [|[|]]; auto.
Qed.


Lemma Forall_firstn : forall {A} (P : A -> Prop) l i, Forall P l ->
  Forall P (firstn i l).
Proof.
  intros; rewrite Forall_forall in *.
  intros ? Hin; pose proof (firstn_In _ _ _ Hin); auto.
Qed.

Lemma Forall_skipn : forall {A} (P : A -> Prop) l i, Forall P l ->
  Forall P (skipn i l).
Proof.
  intros; rewrite Forall_forall in *.
  intros ? Hin; pose proof (skipn_In _ _ _ Hin); auto.
Qed.

Lemma last_cons : forall {A} (d : A) l x, l <> [] -> last (x :: l) d = last l d.
Proof.
  intros.
  destruct l; auto.
  contradiction H; auto.
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

Lemma nat_sorted_list_eq : forall d n l (Hl : forall i, (i < n)%nat <-> In i l) (Hlen : length l = n)
  (Hsorted : forall i j, (i < j < n -> nth i l d < nth j l d)%nat) i (Hi : (i < n)%nat), nth i l d = i.
Proof.
  induction n; intros; [lia|].
  destruct (eq_dec l []); [subst; discriminate|].
  destruct (exists_last n0) as (l' & x & ?); subst.
  rewrite app_length in Hlen; simpl in Hlen.
  assert (length l' = n) by lia.
  assert (x = n).
  { assert (x < S n)%nat.
    { specialize (Hl x); destruct Hl as (_ & Hl); apply Hl.
      rewrite in_app; simpl; auto. }
    destruct (lt_dec x n); [|lia].
    assert (n < S n)%nat as Hlt by lia; rewrite Hl in Hlt.
    rewrite in_app in Hlt; destruct Hlt as [Hin | [? | ?]]; [| lia | contradiction].
    apply In_nth with (d := d) in Hin; destruct Hin as (j & ? & ?).
    exploit (Hsorted j (length l')); [lia|].
    rewrite app_nth1, app_nth2, minus_diag by auto; simpl; lia. }
  destruct (eq_dec i n); subst.
  - rewrite app_nth2, minus_diag by lia; auto.
  - rewrite app_nth1 by lia; apply IHn; auto; try lia.
    + intro j; specialize (Hl j); split; intro Hin.
      * destruct Hl as (Hl & _); exploit Hl; [lia|].
        rewrite in_app; intros [? | [? | ?]]; [auto | lia | contradiction].
      * destruct Hl as (_ & Hl); exploit Hl; [rewrite in_app; auto | intro].
        apply In_nth with (d := d) in Hin; destruct Hin as (i' & ? & ?).
        exploit (Hsorted i' (length l')); [lia|].
        rewrite app_nth1, app_nth2, minus_diag by auto; simpl; lia.
    + intros i' j' ?; exploit (Hsorted i' j'); [lia|].
      rewrite !app_nth1 by lia; auto.
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

Lemma last_snoc : forall {A} (d : A) x l, last (l ++ [x]) d = x.
Proof.
  induction l; auto; simpl.
  destruct (l ++ [x]) eqn: Heq; auto.
  contradiction (app_cons_not_nil l [] x); auto.
Qed.

Lemma sublist_0_cons : forall {A} j x (l : list A), j > 0 ->
  sublist 0 j (x :: l) = x :: sublist 0 (j - 1) l.
Proof.
  intros. unfold_sublist_old.
  destruct (Z.to_nat (j - 0)) eqn: Hminus.
  - apply Z.gt_lt in H; rewrite Z2Nat.inj_lt in H; lia.
  - simpl; repeat f_equal.
    rewrite Z.sub_0_r in *.
    rewrite Z2Nat.inj_sub, Hminus; simpl; lia.
Qed.

Lemma sublist_S_cons : forall {A} i j x (l : list A), i > 0 ->
  sublist i j (x :: l) = sublist (i - 1) (j - 1) l.
Proof.
  intros; unfold_sublist_old.
  destruct (Z.to_nat i) eqn: Hi.
  - apply Z.gt_lt in H; rewrite Z2Nat.inj_lt in H; lia.
  - simpl.
    f_equal; f_equal; lia.
Qed.

Lemma Znth_last : forall {A}{d: Inhabitant A} l, Znth (Zlength l - 1) l = last l default.
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

Lemma Znth_cons_eq : forall {A}{d : Inhabitant A} i x l, 
   Znth i (x :: l) = if eq_dec i 0 then x else Znth (i - 1) l.
Proof.
  intros.
  destruct (eq_dec i 0); [subst; apply Znth_0_cons|].
  destruct (zlt i 0); [rewrite !Znth_underflow; auto; lia|].
  apply Znth_pos_cons; lia.
Qed.

Lemma Znth_rotate : forall {A} {d : Inhabitant A} i l n, 
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
  eapply Forall_Znth with (i0 := i) in Hj; [|rewrite Zlength_sublist; lia].
  rewrite Znth_sublist, Z.add_0_r in Hj by lia.
  contradiction Hi; eauto.
Qed.

Corollary Forall_sublist_first : forall {A} {d : Inhabitant A} (P : A -> Prop) i j l
  (Hrangei : 0 <= i <= Zlength l) (Hi : Forall P (sublist 0 i l)) (Hi' : ~P (Znth i l))
  (Hrangej : 0 <= j <= Zlength l) (Hj : Forall P (sublist 0 j l)) (Hj' : ~P (Znth j l)),
  i = j.
Proof.
  intros.
  apply Z.le_antisymm; eapply Forall_sublist_le; eauto; lia.
Qed.

Lemma NoDup_Znth_inj : forall {A} {d : Inhabitant A} l i j (HNoDup : NoDup l)
  (Hi : 0 <= i < Zlength l) (Hj : 0 <= j < Zlength l) (Heq : Znth i l = Znth j l ),
  i = j.
Proof.
  induction l; intros.
  { rewrite Zlength_nil in *; lia. }
  inv HNoDup.
  rewrite Zlength_cons in *.
  rewrite !Znth_cons_eq in Heq.
  destruct (eq_dec i 0), (eq_dec j 0); subst; auto.
  - contradiction H1; apply Znth_In; lia.
  - contradiction H1; apply Znth_In; lia.
  - exploit (IHl (i - 1) (j - 1)); auto; lia.
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

Lemma combine_app : forall {A B} (l1 l2 : list A) (l1' l2' : list B), length l1 = length l1' ->
  combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  induction l1; destruct l1'; intros; try discriminate; auto; simpl in *.
  rewrite IHl1; auto.
Qed.

Lemma combine_app' : forall {A B} (l1 l2 : list A) (l1' l2' : list B), Zlength l1 = Zlength l1' ->
  combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  intros; apply combine_app.
  rewrite !Zlength_correct in *; lia.
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

Lemma app_eq_inv : forall {A} (l1 l2 l3 l4 : list A)
  (Heq : l1 ++ l2 = l3 ++ l4) (Hlen : length l1 = length l3), l1 = l3 /\ l2 = l4.
Proof.
  induction l1; simpl; intros; destruct l3; try discriminate; auto.
  inv Heq; inv Hlen.
  exploit IHl1; eauto; intros (? & ?); subst; auto.
Qed.

Lemma rotate_inj : forall {A} (l1 l2 : list A) n m, rotate l1 n m = rotate l2 n m ->
  length l1 = length l2 -> 0 <= n <= m -> m <= Zlength l1 -> l1 = l2.
Proof.
  unfold rotate; intros.
  destruct (app_eq_inv _ _ _ _ H) as (Hskip & Hfirst).
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
  destruct (app_eq_inv _ _ _ _ H); auto.
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

(*
Lemma repeat_list_repeat : forall {A} n (x : A), repeat x n = list_repeat n x.
Proof.
  induction n; auto; simpl; intro.
  rewrite IHn; auto.
Qed.
*)

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

Lemma Znth_repeat : forall {A} {x : Inhabitant A} n i, Znth i (repeat default n) = default.
Proof.
  induction n; simpl; intro.
  - apply Znth_nil.
  - destruct (Z_lt_dec i 0); [apply Znth_underflow; auto|].
    destruct (eq_dec i 0); [subst; apply Znth_0_cons | rewrite Znth_pos_cons; eauto; lia].
Qed.

Lemma Znth_repeat' : forall {A} {d: Inhabitant A} (x : A) n i, 
    0 <= i < Z.of_nat n -> Znth i (repeat x n)  = x.
Proof.
  induction n; intros; [simpl in *; lia|].
  rewrite Nat2Z.inj_succ in H; simpl.
  destruct (eq_dec i 0).
  - subst; apply Znth_0_cons.
  - rewrite Znth_pos_cons by lia; apply IHn; lia.
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

Lemma upd_complete' : forall l x n, (length l < n)%nat ->
  upd_Znth (Zlength l) (map Vint (map Int.repr l) ++ repeat Vundef (n - length l)) (Vint (Int.repr x)) =
  map Vint (map Int.repr (l ++ [x])) ++ repeat Vundef (n - length (l ++ [x])).
Proof.
  intros.
  rewrite upd_Znth_app2; [|repeat rewrite Zlength_map; repeat rewrite Zlength_correct; lia].
  repeat rewrite Zlength_map.
  rewrite Zminus_diag.
  rewrite app_length; simpl plus.
  destruct (n - length l)%nat eqn: Hminus; [lia|].
  replace (n - (length l + 1))%nat with n0 by lia.
  simpl.
  rewrite upd_Znth0, !map_app, <- app_assoc; auto.
Qed.

(*
Lemma Znth_indep : forall {A} i (l : list A) d d', 
   0 <= i < Zlength l -> Znth i l d = Znth i l d'.
Proof.
  intros; unfold Znth.
  destruct (zlt i 0); [lia|].
  apply nth_indep.
  rewrite Zlength_correct in *; rep_lia.
Qed.
*)

Fixpoint upto n :=
  match n with
  | O => []
  | S n' => 0 :: map Z.succ (upto n')
  end.

Opaque Z.of_nat.

Lemma upto_app : forall n m, upto (n + m) = upto n ++ map (fun i => Z.of_nat n + i) (upto m).
Proof.
  induction n; simpl; intro.
  - rewrite map_id; auto.
  - rewrite IHn, map_app, map_map, Nat2Z.inj_succ; f_equal; f_equal.
    apply map_ext; intro; lia.
Qed.

Lemma upto_length : forall n, length (upto n) = n.
Proof.
  induction n; auto; simpl.
  rewrite map_length, IHn; auto.
Qed.

Corollary Zlength_upto : forall n, Zlength (upto n) = Z.of_nat n.
Proof.
  intro; rewrite Zlength_correct, upto_length; auto.
Qed.

Lemma skipn_cons : forall {A}{d: Inhabitant A} n (l : list A), (length l > n)%nat ->
  skipn n l = Znth (Z.of_nat n) l :: skipn (S n) l.
Proof.
  induction n; intros; simpl; destruct l; simpl in *; try lia; auto.
  rewrite Nat2Z.inj_succ.
  rewrite Znth_pos_cons; [|lia].
  unfold Z.succ; rewrite Z.add_simpl_r.
  erewrite IHn; auto; lia.
Qed.

(*
Lemma Znth_map' : forall {A B} i (f : A -> B) al b,
           Znth i (map f al) (f b) = f (Znth i al b).
Proof.
  unfold Znth; intros.
  destruct (zlt i 0); auto.
  apply map_nth.
Qed.
*)

Lemma Znth_upto : forall d m n, 
  0 <= n < Z.of_nat m -> @Znth _ d n (upto m) = n.
Proof.
  induction m; simpl; intros.
  - rewrite Znth_nil; simpl in *; rewrite Nat2Z.inj_0 in *; lia.
  - destruct (eq_dec n 0).
    + subst; apply Znth_0_cons.
    + rewrite Nat2Z.inj_succ in *.
      rewrite Znth_pos_cons by lia.
      rewrite Znth_map. rewrite IHm. lia. lia.
      rewrite Zlength_upto. lia.
Qed.

Transparent Z.of_nat.

Lemma In_Znth : forall {A} {d: Inhabitant A} (l : list A) x,
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l = x.
Proof.
  unfold Znth; intros.
  apply In_nth with (d := d) in H; destruct H as (n & ? & ?).
  exists (Z.of_nat n); split.
  - rewrite Zlength_correct; lia.
  - destruct (Z_lt_dec (Z.of_nat n) 0); [lia|].
    rewrite Nat2Z.id; auto.
Qed.

Lemma In_upd_Znth_old : forall {A}{d: Inhabitant A} i (x y : A) l, In x l -> x <> Znth i l -> 0 <= i <= Zlength l ->
  In x (upd_Znth i l y).
Proof.
  intros.
  destruct (Z_lt_dec i (Zlength l)).
  - unfold_upd_Znth_old.
    apply In_Znth in H; destruct H as (j & ? & ?); subst.
    destruct (eq_dec j i); [subst; contradiction|].
    rewrite in_app; simpl.
    destruct (zlt j i); [left | right; right].
    + erewrite <- (Z.add_0_r j), <- Znth_sublist; [apply Znth_In; rewrite Zlength_sublist| |]; auto; lia.
    + erewrite <- (Z.sub_simpl_r _ (i + 1)), <- Znth_sublist; [apply Znth_In; rewrite Zlength_sublist| |]; lia.
  - rewrite upd_Znth_out_of_range; auto.
Qed.

Lemma Znth_combine : forall {A B} {a: Inhabitant A} {b: Inhabitant B} i (l1: list A) (l2: list B), 
   Zlength l1 = Zlength l2 ->
  Znth i (combine l1 l2) = (Znth i l1, Znth i l2).
Proof.
  intros; unfold Znth.
  destruct (Z_lt_dec i 0); auto.
  apply combine_nth.
  rewrite !Zlength_correct in *; rep_lia.
Qed.

Lemma Zlength_combine : forall {A B} (l : list A) (l' : list B),
  Zlength (combine l l') = Z.min (Zlength l) (Zlength l').
Proof.
  intros; rewrite !Zlength_correct, combine_length, Nat2Z.inj_min; auto.
Qed.

Lemma nth_Znth : forall {A}{d: Inhabitant A} i l, nth i l default = Znth (Z.of_nat i) l.
Proof.
  intros; unfold Znth.
  destruct (Z_lt_dec (Z.of_nat i) 0); [lia|].
  rewrite Nat2Z.id; auto.
Qed.

Lemma upd_Znth_cons : forall {A} i a l (x : A), i > 0 ->
  upd_Znth i (a :: l) x = a :: upd_Znth (i - 1) l x.
Proof.
  intros. destruct (zle i (Zlength l)).
  - unfold_upd_Znth_old; unfold_sublist_old.
    repeat rewrite Z.sub_0_r.
    destruct (Z.to_nat i) eqn: Hi.
    { exploit Z2Nat_inj_0; eauto; lia. }
    rewrite Zlength_cons; repeat rewrite Z2Nat.inj_add; try lia.
    repeat rewrite Z2Nat.inj_sub; try lia.
    rewrite Hi; simpl.
    rewrite Nat.sub_0_r.
    do 4 f_equal.
    rewrite Z2Nat.inj_succ; [|rewrite Zlength_correct; lia].
    lia.
  - rewrite !upd_Znth_out_of_range; auto. lia. rewrite Zlength_cons; lia.
Qed.

Lemma upd_Znth_triv : forall {A}{d: Inhabitant A} i (l : list A) x (Hi : 0 <= i < Zlength l),
  Znth i l = x -> upd_Znth i l x = l.
Proof.
  (* This cannot be solve by list_solve because list_solve cannot handle congruence like i = j -> Znth i l = Znth j l. *)
  intros; unfold_upd_Znth_old.
  setoid_rewrite <- (firstn_skipn (Z.to_nat i) l) at 4.
  erewrite skipn_cons, Z2Nat.id, H; try lia; [|rewrite Zlength_correct in *; rep_lia].
  unfold_sublist_old.
  rewrite Z.sub_0_r, Z2Nat.inj_add, NPeano.Nat.add_1_r; try lia.
  setoid_rewrite firstn_same at 2; auto.
  rewrite Z2Nat.inj_sub, Zlength_correct, Nat2Z.id, Z2Nat.inj_add, skipn_length; simpl; lia.
Qed.

Lemma combine_upd_Znth : forall {A B} (l1 : list A) (l2 : list B) i x1 x2, 0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 -> combine (upd_Znth i l1 x1) (upd_Znth i l2 x2) = upd_Znth i (combine l1 l2) (x1, x2).
Proof.
  induction l1; simpl; intros; [rewrite Zlength_nil in *; lia|].
  destruct l2; [rewrite Zlength_nil in *; lia|].
  rewrite !Zlength_cons in *.
  destruct (eq_dec i 0).
  - subst; rewrite !upd_Znth0. auto.
  - rewrite !upd_Znth_cons; try lia; simpl.
    rewrite IHl1; auto; lia.
Qed.

Corollary combine_upd_Znth1 : forall {A B}{d: Inhabitant B} (l1 : list A) (l2 : list B) i x,
   0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 ->
   combine (upd_Znth i l1 x) l2 = upd_Znth i (combine l1 l2) (x, Znth i l2).
Proof.
  intros; rewrite <- combine_upd_Znth by auto.
  erewrite upd_Znth_triv with (l := l2); eauto; lia.
Qed.

Corollary combine_upd_Znth2 : forall {A B}{d: Inhabitant A} (l1 : list A) (l2 : list B) i x, 0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 -> combine l1 (upd_Znth i l2 x) = upd_Znth i (combine l1 l2) (Znth i l1, x).
Proof.
  intros; rewrite <- combine_upd_Znth by auto.
  erewrite upd_Znth_triv with (l := l1); eauto; lia.
Qed.

Lemma in_concat : forall {A} (l : list (list A)) x, In x (concat l) <-> exists l1, In x l1 /\ In l1 l.
Proof.
  induction l; simpl; intros.
  - split; [|intros (? & ? & ?)]; contradiction.
  - rewrite in_app, IHl; split.
    + intros [? | (? & ? & ?)]; eauto.
    + intros (? & ? & [? | ?]); subst; eauto.
Qed.

Lemma length_concat : forall {A} (l : list (list A)), length (concat l) = fold_right plus O (map (@length A) l).
Proof.
  induction l; auto; simpl.
  rewrite app_length, IHl; auto.
Qed.

Lemma length_concat_min : forall {A}{d: Inhabitant A} (l : list (list A)) i (Hi : 0 <= i < Zlength l),
  (length (Znth i l) <= length (concat l))%nat.
Proof.
  induction l; simpl; intros; [rewrite Zlength_nil in *; lia|].
  rewrite app_length; destruct (eq_dec i 0).
  - subst; rewrite Znth_0_cons; lia.
  - rewrite Znth_pos_cons by lia.
    rewrite Zlength_cons in *; etransitivity; [apply IHl|]; lia.
Qed.

Lemma length_concat_upd : forall {A} {d: Inhabitant A} l i (l' : list A) (Hi : 0 <= i < Zlength l),
  length (concat (upd_Znth i l l')) = (length (concat l) + length l' - length (Znth i l))%nat.
Proof.
  induction l; intros; [rewrite Zlength_nil in *; lia|].
  destruct (eq_dec i 0).
  - subst; rewrite upd_Znth0, Znth_0_cons.
    simpl; rewrite !app_length; lia.
  - rewrite upd_Znth_cons, Znth_pos_cons by lia; simpl.
    rewrite Zlength_cons in *.
    rewrite !app_length, IHl by lia.
    exploit (length_concat_min l (i - 1)); lia.
Qed.


Lemma incl_nil : forall {A} (l : list A), incl [] l.
Proof.
  repeat intro; contradiction.
Qed.
#[export] Hint Resolve incl_nil : core.

Lemma incl_cons_out : forall {A} (a : A) l1 l2, incl l1 (a :: l2) -> ~In a l1 -> incl l1 l2.
Proof.
  intros; intros ? Hin; specialize (H _ Hin); destruct H; auto; subst; contradiction.
Qed.

Lemma In_upto : forall n i, In i (upto n) <-> 0 <= i < Z.of_nat n.
Proof.
  induction n; intro.
  - simpl; split; try contradiction; lia.
  - rewrite Nat2Z.inj_succ; simpl.
    rewrite in_map_iff; split.
    + intros [? | ?]; [lia|].
      destruct H as (? & ? & ?); subst; rewrite IHn in *; lia.
    + intro; destruct (eq_dec i 0); [auto | right].
      exists (i - 1); rewrite IHn; lia.
Qed.

Lemma combine_fst : forall {A B} (l : list A) (l' : list B), length l = length l' ->
  map fst (combine l l') = l.
Proof.
  induction l; destruct l'; try discriminate; auto; intros.
  inv H; simpl; rewrite IHl; auto.
Qed.

Lemma combine_snd : forall {A B} (l : list A) (l' : list B), length l = length l' ->
  map snd (combine l l') = l'.
Proof.
  induction l; destruct l'; try discriminate; auto; intros.
  inv H; simpl; rewrite IHl; auto.
Qed.

Lemma rev_combine : forall {A B} (l1 : list A) (l2 : list B), length l1 = length l2 ->
  rev (combine l1 l2) = combine (rev l1) (rev l2).
Proof.
  induction l1; destruct l2; try discriminate; auto; simpl; intros.
  inv H; rewrite combine_app; [|rewrite !rev_length; auto].
  rewrite IHl1; auto.
Qed.

Lemma combine_map_snd : forall {A B C} (l1 : list A) (l2 : list B) (f : B -> C),
  combine l1 (map f l2) = map (fun x => let '(a, b) := x in (a, f b)) (combine l1 l2).
Proof.
  induction l1; auto; simpl; intros.
  destruct l2; auto; simpl.
  rewrite IHl1; auto.
Qed.

Lemma combine_const1 : forall {A B} (l1 : list A) (x : B) n, Z.of_nat n >= Zlength l1 ->
  combine l1 (repeat x n) = map (fun a => (a, x)) l1.
Proof.
  induction l1; auto; simpl; intros.
  rewrite Zlength_cons in *; destruct n; [rewrite Zlength_correct in *; simpl in *; lia | simpl].
  rewrite IHl1; auto.
  rewrite Nat2Z.inj_succ in *; lia.
Qed.

Lemma combine_const2 : forall {A B} (x : A) n (l2 : list B), Z.of_nat n >= Zlength l2 ->
  combine (repeat x n) l2 = map (fun b => (x, b)) l2.
Proof.
  induction n; destruct l2; auto; intros; rewrite ?Nat2Z.inj_succ, ?Zlength_nil, ?Zlength_cons in *;
    simpl in *; try (rewrite Zlength_correct in *; lia).
  rewrite IHn; auto; lia.
Qed.

Lemma map_const: forall {A B} (c : A) (l : list B), map (fun _ => c) l = repeat c (length l).
Proof.
  induction l; auto; simpl.
  rewrite IHl; auto.
Qed.

Lemma In_upd_Znth : forall {A} i l (x y : A), In x (upd_Znth i l y) -> x = y \/ In x l.
Proof.
  unfold upd_Znth; intros *; if_tac; auto; intros. clear H. rename H0 into H.
  rewrite in_app in H; destruct H as [? | [? | ?]]; auto; right; eapply sublist_In; eauto.
Qed.

Lemma upd_Znth_In : forall {A} i l (x : A), 0 <= i < Zlength l -> In x (upd_Znth i l x).
Proof.
  intros; unfold_upd_Znth_old.
  rewrite in_app; simpl; auto.
Qed.

Lemma NoDup_Znth_iff : forall {A}{d: Inhabitant A} (l : list A),
  NoDup l <-> forall i j (Hi : 0 <= i < Zlength l)
                            (Hj : 0 <= j < Zlength l), Znth i l = Znth j l -> i = j.
Proof.
  split; intros; [eapply NoDup_Znth_inj; eauto|].
  induction l; rewrite ?Zlength_cons in *; constructor.
  - intro Hin; eapply In_Znth in Hin; destruct Hin as (j & ? & Hj).
    exploit (H 0 (j + 1)); try lia.
    rewrite !Znth_cons_eq; simpl.
    if_tac; [lia|].
    rewrite Z.add_simpl_r; eauto.
  - apply IHl; intros.
    exploit (H (i + 1) (j + 1)); try lia.
    rewrite !Znth_cons_eq, !Z.add_simpl_r.
    if_tac; [lia|].
    if_tac; [lia | auto].
Qed.

Lemma concat_less_incl : forall {A} l i (l1 l2 : list A) (Hi : 0 <= i < Zlength l)
  (Hless : Znth i l = l1 ++ l2), incl (concat (upd_Znth i l l1)) (concat l).
Proof.
  intros.
  intros ? Hin.
  rewrite in_concat in Hin; rewrite in_concat.
  destruct Hin as (? & ? & Hin).
  apply In_upd_Znth in Hin; destruct Hin; eauto; subst.
  do 2 eexists; [rewrite in_app; left; eauto|].
  rewrite <- Hless; apply Znth_In; auto.
Qed.

Lemma NoDup_app : forall {A} (l1 l2 : list A), NoDup (l1 ++ l2) ->
  NoDup l1 /\ NoDup l2 /\ forall x, In x l1 -> ~In x l2.
Proof.
  induction l1; intros.
  - repeat split; auto; constructor.
  - inv H.
    exploit IHl1; eauto; intros (? & ? & ?).
    rewrite in_app in *.
    repeat split; auto.
    + constructor; auto.
    + intros ? [? | ?]; auto; subst; auto.
Qed.

Lemma NoDup_app_iff : forall {A} (l1 l2 : list A), NoDup (l1 ++ l2) <->
  NoDup l1 /\ NoDup l2 /\ forall x, In x l1 -> ~In x l2.
Proof.
  intros; split; [apply NoDup_app|].
  intros (? & ? & Hsep); induction l1; auto.
  inv H; simpl; constructor.
  - rewrite in_app_iff; intros [? | ?]; [contradiction|].
    eapply Hsep; simpl; eauto.
  - apply IHl1; auto.
    intros; apply Hsep; simpl; auto.
Qed.

Corollary NoDup_app_swap : forall {A} (l1 l2 : list A), NoDup (l1 ++ l2) <-> NoDup (l2 ++ l1).
Proof.
  intros; rewrite !NoDup_app_iff; split; intros (? & ? & Hsep); repeat split; auto; repeat intro; eapply Hsep;
    eauto.
Qed.

Lemma NoDup_concat_less : forall {A} l i (l1 l2 : list A) (Hl : NoDup (concat l))
  (Hi : 0 <= i < Zlength l) (Hless : Znth i l = l1 ++ l2),
  NoDup (concat (upd_Znth i l l1)).
Proof.
  induction l; simpl; intros; [rewrite Zlength_nil in *; lia|].
  rewrite Zlength_cons in *.
  destruct (eq_dec i 0).
  - subst; rewrite upd_Znth0.
    rewrite Znth_0_cons in Hless; subst.
    rewrite <- app_assoc, NoDup_app_swap, <- app_assoc, NoDup_app_iff, NoDup_app_swap in Hl; tauto.
  - rewrite upd_Znth_cons by lia; simpl.
    rewrite Znth_pos_cons in Hless by lia.
    rewrite NoDup_app_iff in Hl; rewrite NoDup_app_iff.
    destruct Hl as (? & ? & Hsep).
    split; [auto|]; split.
    + eapply IHl; eauto; lia.
    + intros ?? Hin; eapply Hsep; eauto.
      eapply concat_less_incl; eauto; lia.
Qed.

Lemma Forall2_Znth : forall {A B}{d1: Inhabitant A}{d2: Inhabitant B} (P : A -> B -> Prop) l1 l2 (Hall : Forall2 P l1 l2) i
  (Hi : 0 <= i < Zlength l1), P (Znth i l1) (Znth i l2).
Proof.
  induction 1; intros.
  { rewrite Zlength_nil in *; lia. }
  rewrite Zlength_cons in *.
  destruct (eq_dec i 0).
  - subst; rewrite !Znth_0_cons; auto.
  - rewrite !Znth_pos_cons; try lia.
    apply IHHall; lia.
Qed.

Lemma Forall2_app_inv : forall {A B} (P : A -> B -> Prop) l1 l2 l3 l4 (Hlen : length l1 = length l3),
  Forall2 P (l1 ++ l2) (l3 ++ l4) -> Forall2 P l1 l3 /\ Forall2 P l2 l4.
Proof.
  induction l1; destruct l3; try discriminate; auto; intros.
  inv H; inv Hlen.
  exploit IHl1; eauto; intros (? & ?); split; [constructor|]; auto.
Qed.

Lemma Forall2_firstn : forall {A B} (P : A -> B -> Prop) l1 l2 n, Forall2 P l1 l2 ->
  Forall2 P (firstn n l1) (firstn n l2).
Proof.
  intros; revert n; induction H; intro.
  - rewrite !firstn_nil; auto.
  - destruct n; simpl; auto.
Qed.

Lemma Forall2_upd_Znth : forall {A B} (P : A -> B -> Prop) l1 l2 i x1 x2, Forall2 P l1 l2 ->
  P x1 x2 -> 0 <= i <= Zlength l1 -> Forall2 P (upd_Znth i l1 x1) (upd_Znth i l2 x2).
Proof.
  intros.
  pose proof (mem_lemmas.Forall2_Zlength H) as Hlen.
  destruct (zlt i (Zlength l1)).
  - unfold_upd_Znth_old.
    erewrite <- sublist_same with (al := l1), sublist_split with (mid := i) in H; auto; try lia.
    erewrite <- sublist_same with (al := l2), sublist_split with (al := l2)(mid := i) in H; auto; try lia.
    apply Forall2_app_inv in H.
    destruct H as (? & Hall); apply Forall2_app; auto.
    constructor; auto.
    destruct (eq_dec i (Zlength l1)).
    + rewrite !sublist_nil_gen; auto; lia.
    + rewrite Z.add_comm.
      replace (Zlength l1) with (Zlength l1 - i + i) by lia.
      replace (Zlength l2) with (Zlength l2 - i + i) by lia.
      erewrite <- !sublist_sublist with (j := Zlength l1); try lia.
      inversion Hall as [Hl1 Hl2 | ?????? Hl1 Hl2].
      * rewrite !Hlen, <- Hl2.
        unfold sublist; rewrite !firstn_nil, !skipn_nil; auto.
      * rewrite sublist_1_cons, !Hlen, <- Hl2, sublist_1_cons.
        unfold sublist; simpl; apply Forall2_firstn; auto.
    + apply Nat2Z.inj; rewrite <- !Zlength_correct.
      autorewrite with sublist; auto.
  - rewrite !upd_Znth_out_of_range by lia. auto.
Qed.

Lemma Forall2_impl' : forall {A B} (P Q : A -> B -> Prop) l1 l2,
  (forall a b, In a l1 -> In b l2 -> P a b -> Q a b) -> Forall2 P l1 l2 -> Forall2 Q l1 l2.
Proof.
  induction 2; simpl in *; auto.
Qed.

Lemma Forall2_impl : forall {A B} (P Q : A -> B -> Prop), (forall a b, P a b -> Q a b) ->
  forall l1 l2, Forall2 P l1 l2 -> Forall2 Q l1 l2.
Proof.
  induction 2; auto.
Qed.

Lemma map_id_eq : forall {A} (l : list A), map (@id A) l = l.
Proof.
  induction l; auto.
  simpl; apply f_equal; auto.
Qed.

Lemma Forall2_map : forall {A B C D} (P : A -> B -> Prop) (f1 : C -> A) (f2 : D -> B) l1 l2,
  Forall2 P (map f1 l1) (map f2 l2) <-> Forall2 (fun a b => P (f1 a) (f2 b)) l1 l2.
Proof.
  induction l1.
  - split; intro H.
    + destruct l2; auto; inv H.
    + inv H; simpl; auto.
  - split; intro H.
    + destruct l2; inv H.
      rewrite IHl1 in *; constructor; auto.
    + inv H; simpl; constructor; auto.
      rewrite IHl1; auto.
Qed.

Corollary Forall2_map1 : forall {A B C} (P : A -> B -> Prop) (f : C -> A) l1 l2, Forall2 P (map f l1) l2 <->
  Forall2 (fun a b => P (f a) b) l1 l2.
Proof.
  intros; rewrite <- (map_id_eq l2) at 1; apply Forall2_map.
Qed.

Corollary Forall2_map2 : forall {A B C} (P : A -> B -> Prop) (f : C -> B) l1 l2, Forall2 P l1 (map f l2) <->
  Forall2 (fun a b => P a (f b)) l1 l2.
Proof.
  intros; rewrite <- (map_id_eq l1) at 1; apply Forall2_map.
Qed.

Lemma firstn_max_length : forall {A} n (al : list A), Zlength (firstn n al) <= Zlength al.
Proof.
  intros; revert n; induction al; intros.
  - rewrite firstn_nil. list_solve.
  - destruct n.
    + simpl. list_solve.
    + simpl. specialize (IHal n). list_solve.
Qed.

Lemma skipn_max_length : forall {A} n (al : list A), Zlength (skipn n al) <= Zlength al.
Proof.
  intros; revert n; induction al; intros.
  - rewrite skipn_nil. list_solve.
  - destruct n.
    + simpl. list_solve.
    + simpl. specialize (IHal n). list_solve.
Qed.

Lemma sublist_max_length : forall {A} i j (al : list A), Zlength (sublist i j al) <= Zlength al.
Proof.
  intros; unfold sublist.
  rewrite skipn_max_length.
  apply firstn_max_length.
Qed.

Lemma Forall2_sublist : forall {A B} (P : A -> B -> Prop) l1 l2 i j, Forall2 P l1 l2 -> 0 <= i ->
  Forall2 P (sublist i j l1) (sublist i j l2).
Proof.
  intros; revert j; revert dependent i; induction H; intros.
  - rewrite !sublist_of_nil; constructor.
  - destruct (Z_le_dec j i); [rewrite !sublist_nil_gen; auto; constructor|].
    destruct (eq_dec i 0).
    + subst; rewrite !sublist_0_cons by lia.
      constructor; auto.
    + rewrite !sublist_S_cons by lia.
      apply IHForall2; lia.
Qed.

Lemma Forall_last : forall {A} (P : A -> Prop) d l, Forall P l -> P d -> P (last l d).
Proof.
  destruct l; auto.
  exploit (@app_removelast_last _ (a :: l) d); [discriminate | intro Hlast].
  intros; rewrite Forall_forall in H; apply H.
  rewrite Hlast at 2; rewrite in_app; simpl; auto.
Qed.

Lemma last_map : forall {A B} (f : A -> B) d l, f (last l d) = last (map f l) (f d).
Proof.
  induction l; auto; simpl.
  destruct l; auto.
Qed.

Lemma In_removelast : forall {A} (l : list A) x, In x (removelast l) -> In x l.
Proof.
  induction l; auto; simpl; intros.
  destruct l; auto.
  destruct H; auto.
Qed.

Definition nil_dec {A} (l : list A) : {l = []} + {l <> []}.
Proof.
  destruct l; auto.
  right; discriminate.
Qed.

Lemma Forall2_upd_Znth_l : forall {A B}{d: Inhabitant B} (P : A -> B -> Prop) l1 l2 i x, Forall2 P l1 l2 ->
  P x (Znth i l2) -> 0 <= i < Zlength l1 -> Forall2 P (upd_Znth i l1 x) l2.
Proof.
  intros.
  erewrite <- upd_Znth_triv with (l := l2)(i0 := i); eauto.
  apply Forall2_upd_Znth; eauto; lia.
  apply mem_lemmas.Forall2_Zlength in H; lia.
Qed.

Lemma Forall2_upd_Znth_r : forall {A B}{d: Inhabitant A} (P : A -> B -> Prop) l1 l2 i x, Forall2 P l1 l2 ->
  P (Znth i l1) x -> 0 <= i < Zlength l1 -> Forall2 P l1 (upd_Znth i l2 x).
Proof.
  intros.
  erewrite <- upd_Znth_triv with (l := l1)(i0 := i) by (eauto; lia).
  apply Forall2_upd_Znth; eauto.
  apply mem_lemmas.Forall2_Zlength in H; lia.
Qed.

Lemma Forall2_eq_upto : forall {A B}{d1: Inhabitant A}{d2: Inhabitant B} (P : A -> B -> Prop) l1 l2, Forall2 P l1 l2 <->
  Zlength l1 = Zlength l2 /\ Forall (fun i => P (Znth i l1) (Znth i l2)) (upto (Z.to_nat (Zlength l1))).
Proof.
  induction l1; destruct l2; rewrite ?Zlength_cons, ?Zlength_nil; try solve [split; intro H; inv H;
    try (rewrite Zlength_correct in *; lia)]; simpl.
  - change (upto 0) with (@nil Z); split; auto.
  - rewrite Z2Nat.inj_succ by (apply Zlength_nonneg).
    rewrite <- Nat.add_1_l, upto_app, Forall_app, Forall_map.
    change (upto 1) with [0]; split; intro H.
    + inversion H as [|????? Hall]; subst.
      rewrite IHl1 in Hall; destruct Hall as (? & Hall).
      split; [congruence|].
      split; auto.
      rewrite Forall_forall in *; intros ? Hin.
      specialize (Hall _ Hin); simpl.
      rewrite In_upto in Hin.
      rewrite !Znth_pos_cons, Z.add_simpl_l by lia; auto.
    + destruct H as (? & Ha & Hall); inversion Ha as [|?? HP]; subst.
      rewrite !Znth_0_cons in HP.
      constructor; auto.
      rewrite IHl1; split; [lia|].
      rewrite Forall_forall in *; intros ? Hin.
      specialize (Hall _ Hin); simpl in *.
      rewrite In_upto in Hin.
      rewrite !Znth_pos_cons, Z.add_simpl_l in Hall by lia; auto.
Qed.

Lemma Forall2_forall_Znth : forall {A B}{d1: Inhabitant A}{d2: Inhabitant B}  (P : A -> B -> Prop) l1 l2,
  Forall2 P l1 l2 <->
  Zlength l1 = Zlength l2 /\ (forall i, 0 <= i < Zlength l1 -> P (Znth i l1) (Znth i l2)).
Proof.
  intros; rewrite Forall2_eq_upto, Forall_forall.
  setoid_rewrite In_upto.
  rewrite Z2Nat.id by (apply Zlength_nonneg).
  reflexivity.
Qed.

Lemma Znth_inbounds : forall {A}{d: Inhabitant A} i (l : list A), 
    Znth i l <> default -> 0 <= i < Zlength l.
Proof.
  intros.
  destruct (zlt i 0); [contradiction H; apply Znth_underflow; auto|].
  destruct (Z_lt_dec i (Zlength l)); [lia|].
  rewrite Znth_overflow in H; [contradiction H; auto | lia].
Qed.

Lemma sublist_next : forall {A}{d: Inhabitant A} i j l,
      0 <= i < j -> j <= Zlength l ->
  sublist i j l = Znth i l :: sublist (i + 1) j l.
Proof.
  intros.
  rewrite Znth_cons_sublist; [|lia].
  apply sublist_split; lia.
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
  rewrite Z2Nat.inj_add, repeat_plus, <- app_assoc; auto; lia.
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
    rewrite list_Znth_eq with (l0 := l) at 1.
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

Lemma upd_Znth_diff' : forall {A}{d: Inhabitant A} i j l (u : A),
    0 <= j < Zlength l -> i <> j ->
  Znth i (upd_Znth j l u) = Znth i l.
Proof.
  intros.
  destruct (zlt i 0).
  { rewrite !Znth_underflow; auto. }
  destruct (zlt i (Zlength l)).
  apply upd_Znth_diff; auto; lia.
  { rewrite !Znth_overflow; auto.
    rewrite upd_Znth_Zlength; auto. }
Qed.

Lemma list_nth_error_eq : forall {A} (l1 l2 : list A)
  (Heq : forall j, nth_error l1 j = nth_error l2 j), l1 = l2.
Proof.
  induction l1; destruct l2; auto; intros; try (specialize (Heq O); simpl in Heq; discriminate).
  erewrite IHl1.
  - specialize (Heq O); inv Heq; eauto.
  - intro j; specialize (Heq (S j)); auto.
Qed.

Lemma list_Znth_eq' : forall {A} {d: Inhabitant A} (l1 l2 : list A)
  (Hlen : Zlength l1 = Zlength l2)
  (Heq : forall j, 0 <= j < Zlength l1 -> Znth j l1 = Znth j l2), l1 = l2.
Proof.
  induction l1; destruct l2; intros; rewrite ?Zlength_cons in *; rewrite ?Zlength_nil in *;
    auto; try (rewrite Zlength_correct in *; lia).
  exploit (Heq 0); [rewrite Zlength_correct; lia|].
  rewrite !Znth_0_cons; intro; subst.
  f_equal; apply IHl1; [lia|].
  intros; specialize (Heq (j + 1)); rewrite !Znth_pos_cons in Heq; try lia.
  rewrite !Z.add_simpl_r in *; apply Heq; lia.
Qed.

Corollary upd_Znth_eq' : forall {A}{d: Inhabitant A} x (l1 l2 : list A) i (Hi : 0 <= i < Zlength l1)
  (Hlen : Zlength l1 = Zlength l2)
  (Heq : forall j, 0 <= j < Zlength l1 -> j <> i -> Znth j l1 = Znth j l2),
  upd_Znth i l1 x = upd_Znth i l2 x.
Proof.
  intros.
  assert (Zlength (upd_Znth i l1 x) = Zlength (upd_Znth i l2 x)).
  { rewrite !upd_Znth_Zlength; auto; lia. }
  apply list_Znth_eq'; auto.
  intros ? Hj; destruct (eq_dec j i).
  - subst; rewrite !upd_Znth_same; auto; lia.
  - rewrite !upd_Znth_diff'; rewrite upd_Znth_Zlength in Hj; auto; lia.
Qed.

Lemma upd_Znth_twice : forall {A} i l (x y : A), 0 <= i < Zlength l ->
  upd_Znth i (upd_Znth i l x) y = upd_Znth i l y.
Proof.
  intros. list_solve.
Qed.

Lemma hd_Znth : forall {A}{d: Inhabitant A} (l : list A), hd default l = Znth 0 l.
Proof.
  destruct l; auto.
Qed.

Lemma NoDup_filter : forall {A} (f : A -> bool) l, NoDup l -> NoDup (filter f l).
Proof.
  induction l; simpl; intros; auto.
  inv H.
  destruct (f a); auto.
  constructor; auto.
  rewrite filter_In; intros (? & ?); contradiction.
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

Lemma filter_length : forall {A} (f : A -> bool) l,
  length l = (length (filter f l) + length (filter (fun x => negb (f x)) l))%nat.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl.
  destruct (f a); simpl; lia.
Qed.

Lemma Zlength_filter : forall {A} f (l : list A), Zlength (filter f l) <= Zlength l.
Proof.
  intros.
  setoid_rewrite Zlength_correct at 2.
  rewrite filter_length with (f0 := f).
  rewrite Nat2Z.inj_add.
  rewrite <- Zlength_correct; lia.
Qed.

Lemma Zlength_concat : forall {A} (l : list (list A)),
  Zlength (concat l) = fold_right Z.add 0 (map (@Zlength A) l).
Proof.
  intros.
  rewrite Zlength_correct, length_concat.
  change 0 with (Z.of_nat O).
  forget O as n.
  revert n; induction l; auto; simpl; intros.
  rewrite Nat2Z.inj_add, IHl, Zlength_correct; auto.
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

Lemma filter_app : forall {A} (f : A -> bool) l1 l2, filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1; auto; intros; simpl.
  rewrite IHl1. destruct (f a); auto.
Qed.

Lemma filter_concat : forall {A} f (l : list (list A)),
  filter f (concat l) = concat (map (filter f) l).
Proof.
  induction l; auto; simpl.
  rewrite filter_app, IHl; auto.
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

Lemma remove_out : forall {A} {A_eq : EqDec A} (x : A) l, ~In x l -> remove A_eq x l = l.
Proof.
  induction l; auto; simpl; intros.
  rewrite IHl by auto.
  if_tac; auto; subst; tauto.
Qed.

Lemma remove_from_NoDup : forall {A} {A_eq : EqDec A} (x : A) l1 l2, NoDup (l1 ++ x :: l2) ->
  remove A_eq x (l1 ++ x :: l2) = l1 ++ l2.
Proof.
  induction l1; simpl; intros.
  - if_tac; [|contradiction].
    inv H; apply remove_out; auto.
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

Lemma In_sublist_upto : forall n x i j, In x (sublist i j (upto n)) -> 0 <= i ->
  i <= x < j /\ x < Z.of_nat n.
Proof.
  induction n; intros.
  - unfold sublist in H; simpl in H; rewrite firstn_nil, skipn_nil in H; contradiction.
  - rewrite Nat2Z.inj_succ; simpl in *.
    destruct (zlt 0 j).
    destruct (eq_dec i 0).
    + subst; rewrite sublist_0_cons in H; try lia; destruct H; [lia|].
      rewrite sublist_map, in_map_iff in H; destruct H as (? & ? & H); subst.
      destruct (zlt 0 (j - 1)).
      exploit IHn; eauto; lia.
      { rewrite sublist_nil_gen in H; [contradiction | lia]. }
    + rewrite sublist_S_cons in H; [|lia].
      rewrite sublist_map, in_map_iff in H; destruct H as (? & ? & H); subst.
      destruct (zlt 0 (j - 1)).
      exploit IHn; eauto; lia.
      { rewrite sublist_nil_gen in H; [contradiction | lia]. }
    + rewrite sublist_nil_gen in H; [contradiction | lia].
Qed.

Lemma incl_cons_iff : forall {A} (a : A) b c, incl (a :: b) c <-> In a c /\ incl b c.
Proof.
  split; intro.
  - split; [|eapply incl_cons_inv; eauto].
    specialize (H a); apply H; simpl; auto.
  - destruct H; intros ? [? | ?]; subst; auto.
Qed.

Lemma lt_le_1 : forall i j, i < j <-> i + 1 <= j.
Proof.
  intros; lia.
Qed.

Lemma firstn_all : forall {A} n (l : list A), (length l <= n)%nat -> firstn n l = l.
Proof.
  induction n; destruct l; auto; simpl; intros; try lia.
  rewrite IHn; auto; lia.
Qed.

Lemma sublist_all : forall {A} i (l : list A), Zlength l <= i -> sublist 0 i l = l.
Proof.
  intros; unfold_sublist_old; simpl.
  apply firstn_all.
  rewrite Zlength_correct in *; rep_lia.
Qed.

Lemma sublist_prefix : forall {A} i j (l : list A), sublist 0 i (sublist 0 j l) = sublist 0 (Z.min i j) l.
Proof.
  intros.
  destruct (Z_le_dec i 0).
  { rewrite !sublist_nil_gen; auto.
    rewrite Z.min_le_iff; auto. }
  destruct (Z.min_spec i j) as [(? & ->) | (? & ->)].
  - rewrite sublist_sublist, !Z.add_0_r by lia; auto.
  - apply sublist_all.
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
    { rewrite sublist_nil_gen with (l0 := l2), Zlength_nil in Heq; auto.
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


Lemma sublist_0_cons' : forall {A} i j (x : A) l, i <= 0 -> j > 0 -> sublist i j (x :: l) =
  x :: sublist i (j - 1) l.
Proof.
  intros; unfold sublist.
  replace (Z.to_nat i) with O; simpl.
  assert (Z.to_nat j > 0)%nat by (apply (Z2Nat.inj_lt 0 j); lia).
  destruct (Z.to_nat j) eqn: Hj; [lia|].
  simpl; f_equal; f_equal.
  rewrite Z2Nat.inj_sub; simpl; lia.
  destruct (eq_dec i 0); subst; auto.
  rewrite Z2Nat_neg; auto; lia.
Qed.

(* locally overwriting sublist_nil_gen *)
Local Lemma sublist_nil_gen : forall {A} (l : list A) i j, j <= 0 -> sublist i j l = [].
Proof.
  intros.
  unfold sublist.
  replace (Z.to_nat j) with O by (symmetry; apply Z_to_nat_neg; auto).
  rewrite skipn_nil.
  auto.
Qed.

Lemma sublist_combine : forall {A B} (l1 : list A) (l2 : list B) i j,
  sublist i j (combine l1 l2) = combine (sublist i j l1) (sublist i j l2).
Proof.
  induction l1; simpl; intros.
  - unfold sublist; rewrite !firstn_nil, !skipn_nil; auto.
  - destruct l2.
    + unfold sublist at 1 3; rewrite !firstn_nil, !skipn_nil.
      destruct (sublist i j (a :: l1)); auto.
    + destruct (Z_le_dec j 0); [rewrite !sublist_nil_gen; auto|].
      destruct (Z_le_dec i 0).
      * subst; rewrite !sublist_0_cons'; try lia.
        simpl; rewrite IHl1; auto.
      * rewrite !sublist_S_cons; try lia.
        apply IHl1; lia.
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
    + destruct (Z_le_dec j 0); [rewrite !sublist_nil_gen; auto|].
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
    + destruct (Z_le_dec j 0); [rewrite !sublist_nil_gen; auto|].
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


Definition remove_Znth {A} i (al : list A) := sublist 0 i al ++ sublist (i + 1) (Zlength al) al.

Lemma remove_Znth0 : forall {A} (l : list A), remove_Znth 0 l = sublist 1 (Zlength l) l.
Proof.
  intros; unfold remove_Znth.
  rewrite sublist_nil; auto.
Qed.

Lemma remove_Znth_cons : forall {A} i a (l : list A), i > 0 ->
  remove_Znth i (a :: l) = a :: remove_Znth (i - 1) l.
Proof.
  intros; unfold remove_Znth.
  rewrite sublist_0_cons, sublist_S_cons, Zlength_cons; auto; try lia.
  simpl; f_equal; f_equal; f_equal; lia.
Qed.

Lemma Zlength_remove_Znth : forall {A} i (l : list A), 0 <= i < Zlength l ->
  Zlength (remove_Znth i l) = Zlength l - 1.
Proof.
  intros; unfold remove_Znth.
  rewrite Zlength_app, !Zlength_sublist; lia.
Qed.

Lemma remove_upd_Znth: forall {A} i l (a : A), 0 <= i < Zlength l ->
  remove_Znth i (upd_Znth i l a) = remove_Znth i l.
Proof.
  intros; unfold remove_Znth.
  rewrite upd_Znth_Zlength, sublist_upd_Znth_l, sublist_upd_Znth_r; auto; lia.
Qed.

Lemma remove_Znth_map: forall {A B} (f : A -> B) i l,
  remove_Znth i (map f l) = map f (remove_Znth i l).
Proof.
  intros; unfold remove_Znth.
  rewrite map_app, Zlength_map, !sublist_map; auto.
Qed.

Lemma remove_Znth_combine: forall {A B} i (l1 : list A) (l2 : list B),
  0 <= i < Zlength l1 -> Zlength l1 = Zlength l2 ->
  remove_Znth i (combine l1 l2) = combine (remove_Znth i l1) (remove_Znth i l2).
Proof.
  intros; unfold remove_Znth.
  rewrite !sublist_combine, combine_app' by (rewrite !Zlength_sublist; lia).
  rewrite Zlength_combine, Z.min_l by lia.
  congruence.
Qed.

Lemma In_remove_upto : forall i j k, 0 <= j -> In i (remove_Znth j (upto k)) ->
  0 <= i < Z.of_nat k /\ i <> j.
Proof.
  unfold remove_Znth; intros ???? Hin%in_app.
  destruct Hin as [Hin | Hin]; apply In_sublist_upto in Hin; lia.
Qed.

Lemma In_remove_upto' : forall i j k, 0 <= j < Z.of_nat k -> In i (remove_Znth j (upto k)) <->
  0 <= i < Z.of_nat k /\ i <> j.
Proof.
  unfold remove_Znth; split.
  - intros Hin%in_app.
    destruct Hin as [Hin | Hin]; apply In_sublist_upto in Hin; lia.
  - intros []; rewrite Zlength_upto.
    rewrite !sublist_upto by lia; simpl.
    rewrite Nat2Z.id, Nat.sub_0_r, !Nat.min_r by rep_lia.
    rewrite in_app_iff; destruct (zlt i j); [left | right]; rewrite in_map_iff; do 2 eexists; rewrite ?In_upto.
    + rewrite Z.add_0_l; reflexivity.
    + rep_lia.
    + apply Zplus_minus.
    + rep_lia.
Qed.

Lemma remove_Znth_app : forall {A} i (l1 l2 : list A), 0 <= i < Zlength l1 + Zlength l2 -> remove_Znth i (l1 ++ l2) =
  if zlt i (Zlength l1) then remove_Znth i l1 ++ l2 else l1 ++ remove_Znth (i - Zlength l1) l2.
Proof.
  intros; unfold remove_Znth.
  rewrite sublist_app by lia.
  rewrite Z.min_l, Z.max_r by rep_lia.
  rewrite Zlength_app, sublist_app by lia.
  rewrite Z.add_simpl_l, (Z.min_r (_ + Zlength l2)), (Z.max_l (Zlength l2)) by rep_lia.
  if_tac.
  - rewrite Z.min_l, Z.max_r, sublist_nil, app_nil_r by rep_lia.
    rewrite Z.min_l, Z.max_r by rep_lia.
    rewrite app_assoc, (sublist_same _ _ l2) by lia; auto.
  - rewrite Z.min_r, Z.max_l, sublist_same by lia.
    rewrite Z.min_r, Z.max_l, sublist_nil by lia; simpl.
    rewrite app_assoc; f_equal; f_equal; lia.
Qed.

Lemma In_remove_upto2: forall (i j k : Z) (l : nat), 0 <= j < Z.of_nat l -> 0 <= k < Z.of_nat l -> j <> k ->
  In i (remove_Znth (if zlt j k then j else j - 1) (remove_Znth k (upto l))) -> 0 <= i < Z.of_nat l /\ i <> j /\ i <> k.
Proof.
  unfold remove_Znth at 2; intros ??????? Hin.
  assert (Zlength (sublist 0 k (upto l)) = k) as Hk.
  { rewrite Zlength_sublist; rewrite ?Zlength_upto; lia. }
  rewrite remove_Znth_app in Hin; rewrite Hk, Zlength_upto in *.
  destruct (zlt j k).
  - rewrite if_true in Hin by auto.
    apply in_app_iff in Hin as [Hin|Hin].
    + rewrite sublist_upto, remove_Znth_map, in_map_iff in Hin by lia; destruct Hin as (? & ? & ?%In_remove_upto); try lia.
    + rewrite sublist_upto, in_map_iff in Hin by lia; destruct Hin as (? & ? & ?%In_upto); try lia.
  - rewrite if_false in Hin by lia.
    apply in_app_iff in Hin as [Hin|Hin].
    + rewrite sublist_upto, in_map_iff in Hin by lia; destruct Hin as (? & ? & ?%In_upto); try lia.
    + rewrite sublist_upto, remove_Znth_map, in_map_iff in Hin by lia; destruct Hin as (? & ? & ?%In_remove_upto); try lia.
  - rewrite Zlength_sublist by (rewrite ?Zlength_upto; lia).
    if_tac; lia.
Qed.

