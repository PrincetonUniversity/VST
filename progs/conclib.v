Require Import VST.veric.ghost_PCM.
Require Export VST.msl.iter_sepcon.
Require Export VST.concurrency.semax_conc_pred.
Require Export VST.concurrency.semax_conc.
Require Export VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Export VST.floyd.sublist.
Import LiftNotation.

(* general list lemmas *)
Notation vint z := (Vint (Int.repr z)).
Notation vptrofs z := (Vptrofs (Ptrofs.repr z)).

Lemma app_cons_assoc : forall {A} l1 (x : A) l2, l1 ++ x :: l2 = (l1 ++ [x]) ++ l2.
Proof.
  intros; rewrite <- app_assoc; auto.
Qed.

Lemma Forall_forall_Znth : forall {A}{d: Inhabitant A} (P : A -> Prop) l,
  Forall P l <-> forall i, 0 <= i < Zlength l -> P (Znth i l).
Proof.
  split; intros; [apply Forall_Znth; auto|].
  induction l; auto.
  rewrite Zlength_cons in *.
  constructor.
  - specialize (H 0); rewrite Znth_0_cons in H; apply H.
    pose proof (Zlength_nonneg l); omega.
  - apply IHl; intros.
    specialize (H (i + 1)).
    rewrite Znth_pos_cons, Z.add_simpl_r in H by omega.
    apply H; omega.
Qed.

Lemma Zmod_smallish : forall x y, y <> 0 -> 0 <= x < 2 * y ->
  x mod y = x \/ x mod y = x - y.
Proof.
  intros.
  destruct (zlt x y); [left; apply Zmod_small; omega|].
  rewrite <- Z.mod_add with (b := -1) by auto.
  right; apply Zmod_small; omega.
Qed.

Lemma Zmod_plus_inv : forall a b c d (Hc : c > 0) (Heq : (a + b) mod c = (d + b) mod c),
  a mod c = d mod c.
Proof.
  intros; rewrite Zplus_mod, (Zplus_mod d) in Heq.
  pose proof (Z_mod_lt a c Hc).
  pose proof (Z_mod_lt b c Hc).
  pose proof (Z_mod_lt d c Hc).
  destruct (Zmod_smallish (a mod c + b mod c) c), (Zmod_smallish (d mod c + b mod c) c); omega.
Qed.

Lemma Znth_app : forall {A}{d: Inhabitant A} (l1 l2 : list A) i,
      Zlength l1 = i -> Znth i (l1 ++ l2) = Znth 0 l2.
Proof.
  intros; subst; rewrite app_Znth2, Zminus_diag; auto; omega.
Qed.

Corollary Znth_app1 : forall {A}{d: Inhabitant A} l1 (x : A) l2 i,
     Zlength l1 = i -> Znth i (l1 ++ x :: l2) = x.
Proof.
  intros; rewrite Znth_app, Znth_0_cons; auto.
Qed.

Lemma repable_0 : repable_signed 0.
Proof.
  split; computable.
Qed.
Hint Resolve repable_0.

Definition complete MAX l := l ++ repeat (vptrofs 0) (Z.to_nat MAX - length l).

Lemma upd_complete : forall l x MAX, Zlength l < MAX ->
  upd_Znth (Zlength l) (complete MAX l) x = complete MAX (l ++ [x]).
Proof.
  intros; unfold complete.
  rewrite upd_Znth_app2, Zminus_diag.
  rewrite app_length; simpl plus.
  rewrite Zlength_correct, Z2Nat.inj_lt, Nat2Z.id in H; try omega.
  destruct (Z.to_nat MAX - length l)%nat eqn: Hminus; [omega|].
  replace (Z.to_nat MAX - (length l + 1))%nat with n by omega.
  unfold upd_Znth, sublist; simpl.
  rewrite Zlength_cons.
  unfold Z.succ; rewrite Z.add_simpl_r.
  rewrite Zlength_correct, Nat2Z.id, firstn_exact_length.
  rewrite <- app_assoc; auto.
  { repeat rewrite Zlength_correct; omega. }
Qed.

Lemma Znth_complete : forall n l MAX, n < Zlength l -> 
     Znth n (complete MAX l) = Znth n l.
Proof.
  intros; apply app_Znth1; auto.
Qed.

Lemma remove_complete : forall l x MAX, Zlength l < MAX ->
  upd_Znth (Zlength l) (complete MAX (l ++ [x])) (vptrofs 0) = complete MAX l.
Proof.
  intros; unfold complete.
  rewrite upd_Znth_app1 by (rewrite Zlength_app, ?Zlength_cons; rep_omega).
  rewrite app_length; simpl plus.
  rewrite upd_Znth_app2, Zminus_diag; [|rewrite Zlength_cons; simpl; omega].
  unfold upd_Znth, sublist.sublist.
  rewrite Zminus_diag; simpl firstn.
  rewrite Zlength_correct, Z2Nat.inj_lt, Nat2Z.id in H; try omega.
  destruct (Z.to_nat MAX - length l)%nat eqn: Hminus; [omega|].
  replace (Z.to_nat MAX - (length l + 1))%nat with n by omega.
  simpl.
  rewrite <- app_assoc; auto.
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

Definition remove_at {A} i (l : list A) := firstn i l ++ skipn (S i) l.

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

Lemma Forall_upd_Znth : forall {A} (P : A -> Prop) x l i, Forall P l -> P x ->
  Forall P (upd_Znth i l x).
Proof.
  intros; unfold upd_Znth.
  rewrite Forall_app; split; [|constructor; auto]; apply Forall_sublist; auto.
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
  { destruct l; simpl in *; [auto | omega]. }
  rewrite last_cons; simpl in *; [|intro; subst; discriminate].
  rewrite NPeano.Nat.sub_0_r in IHl; auto.
Qed.

Lemma Znth_last : forall {A}{d: Inhabitant A} l, Znth (Zlength l - 1) l = last l default.
Proof.
  intros; unfold Znth.
  destruct (zlt (Zlength l - 1) 0).
  - destruct l; auto.
    rewrite Zlength_correct in *; simpl length in *.
    rewrite Nat2Z.inj_succ in *; omega.
  - rewrite Z2Nat.inj_sub; [|omega].
    rewrite Zlength_correct, Nat2Z.id; simpl.
    apply nth_last.
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
  induction n; intros; [omega|].
  destruct (eq_dec l []); [subst; discriminate|].
  destruct (exists_last n0) as (l' & x & ?); subst.
  rewrite app_length in Hlen; simpl in Hlen.
  assert (length l' = n) by omega.
  assert (x = n).
  { assert (x < S n)%nat.
    { specialize (Hl x); destruct Hl as (_ & Hl); apply Hl.
      rewrite in_app; simpl; auto. }
    destruct (lt_dec x n); [|omega].
    assert (n < S n)%nat as Hlt by omega; rewrite Hl in Hlt.
    rewrite in_app in Hlt; destruct Hlt as [Hin | [? | ?]]; [| omega | contradiction].
    apply In_nth with (d := d) in Hin; destruct Hin as (j & ? & ?).
    exploit (Hsorted j (length l')); [omega|].
    rewrite app_nth1, app_nth2, minus_diag by auto; simpl; omega. }
  destruct (eq_dec i n); subst.
  - rewrite app_nth2, minus_diag by omega; auto.
  - rewrite app_nth1 by omega; apply IHn; auto; try omega.
    + intro j; specialize (Hl j); split; intro Hin.
      * destruct Hl as (Hl & _); exploit Hl; [omega|].
        rewrite in_app; intros [? | [? | ?]]; [auto | omega | contradiction].
      * destruct Hl as (_ & Hl); exploit Hl; [rewrite in_app; auto | intro].
        apply In_nth with (d := d) in Hin; destruct Hin as (i' & ? & ?).
        exploit (Hsorted i' (length l')); [omega|].
        rewrite app_nth1, app_nth2, minus_diag by auto; simpl; omega.
    + intros i' j' ?; exploit (Hsorted i' j'); [omega|].
      rewrite !app_nth1 by omega; auto.
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

Lemma iter_sepcon_sepcon: forall {A} f g1 g2 l, (forall b : A, f b = g1 b * g2 b) ->
  iter_sepcon f l = iter_sepcon g1 l * iter_sepcon g2 l.
Proof.
  intros; induction l; simpl; normalize.
  rewrite H, IHl; apply pred_ext; cancel.
Qed.

Lemma sepcon_app : forall l1 l2, fold_right sepcon emp (l1 ++ l2) =
  fold_right sepcon emp l1 * fold_right sepcon emp l2.
Proof.
  induction l1; simpl; intros.
  - rewrite emp_sepcon; auto.
  - rewrite IHl1, sepcon_assoc; auto.
Qed.

Definition rotate {A} (l : list A) n m := sublist (m - n) (Zlength l) l ++
  sublist 0 (m - n) l.

Lemma sublist_of_nil : forall {A} i j, sublist i j (@nil A) = [].
Proof.
  intros; unfold sublist.
  rewrite skipn_nil, firstn_nil; auto.
Qed.

Lemma sublist_0_cons : forall {A} j x (l : list A), j > 0 ->
  sublist 0 j (x :: l) = x :: sublist 0 (j - 1) l.
Proof.
  intros; unfold sublist; simpl.
  destruct (Z.to_nat (j - 0)) eqn: Hminus.
  - apply Z.gt_lt in H; rewrite Z2Nat.inj_lt in H; try omega.
    rewrite Z2Nat.inj_sub in Hminus; omega.
  - simpl; repeat f_equal.
    rewrite Z.sub_0_r in *.
    rewrite Z2Nat.inj_sub, Hminus; simpl; omega.
Qed.

Lemma sublist_S_cons : forall {A} i j x (l : list A), i > 0 ->
  sublist i j (x :: l) = sublist (i - 1) (j - 1) l.
Proof.
  intros; unfold sublist; simpl.
  destruct (Z.to_nat i) eqn: Hi.
  - apply Z.gt_lt in H; rewrite Z2Nat.inj_lt in H; omega.
  - simpl.
    f_equal; f_equal; try omega.
    rewrite Z2Nat.inj_sub, Hi; simpl; omega.
Qed.

Lemma upd_rotate : forall {A} i (l : list A) n m x (Hl : Zlength l = m) (Hlt : 0 <= n <= m)
  (Hi : 0 <= i < Zlength l),
  upd_Znth i (rotate l n m) x = rotate (upd_Znth ((i - n) mod m) l x) n m.
Proof.
  intros; unfold rotate.
  rewrite upd_Znth_Zlength by (subst; apply Z_mod_lt; omega).
  destruct (zlt i (Zlength l - (m - n))).
  - rewrite upd_Znth_app1 by (rewrite Zlength_sublist; omega).
    assert ((i - n) mod m = m + i - n) as Hmod.
    { rewrite <- Z.mod_add with (b := 1) by omega.
      rewrite Zmod_small; omega. }
    rewrite Hmod, sublist_upd_Znth_lr, sublist_upd_Znth_l by (auto; omega).
    replace (m + i - n - (m - n)) with i by omega; auto.
  - rewrite upd_Znth_app2; rewrite ?Zlength_sublist; try omega.
    assert ((i - n) mod m = i - n) as Hmod.
    { rewrite Zmod_small; omega. }
    rewrite Hmod, sublist_upd_Znth_r, sublist_upd_Znth_lr by omega.
    replace (i - (Zlength l - (m - n))) with (i - n - 0) by omega; auto.
Qed.

Lemma Znth_cons_eq : forall {A}{d : Inhabitant A} i x l, 
   Znth i (x :: l) = if eq_dec i 0 then x else Znth (i - 1) l.
Proof.
  intros.
  destruct (eq_dec i 0); [subst; apply Znth_0_cons|].
  destruct (zlt i 0); [rewrite !Znth_underflow; auto; omega|].
  apply Znth_pos_cons; omega.
Qed.

Lemma Znth_rotate : forall {A} {d : Inhabitant A} i l n, 
    0 <= n <= Zlength l -> 0 <= i < Zlength l ->
  Znth i (rotate l n (Zlength l)) = Znth ((i - n) mod Zlength l) l.
Proof.
  intros; unfold rotate.
  destruct (zlt i n).
  - rewrite app_Znth1 by (rewrite Zlength_sublist; omega).
    rewrite Znth_sublist by omega.
    rewrite <- Z_mod_plus with (b := 1), Zmod_small by omega.
    f_equal; omega.
  - rewrite app_Znth2; (rewrite Zlength_sublist; try omega).
    rewrite Znth_sublist by omega.
    rewrite Zmod_small by omega.
    f_equal; omega.
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
  eapply Forall_Znth with (i0 := i) in Hj; [|rewrite Zlength_sublist; omega].
  rewrite Znth_sublist, Z.add_0_r in Hj by omega.
  contradiction Hi; eauto.
Qed.

Corollary Forall_sublist_first : forall {A} {d : Inhabitant A} (P : A -> Prop) i j l
  (Hrangei : 0 <= i <= Zlength l) (Hi : Forall P (sublist 0 i l)) (Hi' : ~P (Znth i l))
  (Hrangej : 0 <= j <= Zlength l) (Hj : Forall P (sublist 0 j l)) (Hj' : ~P (Znth j l)),
  i = j.
Proof.
  intros.
  apply Z.le_antisymm; eapply Forall_sublist_le; eauto; omega.
Qed.

Lemma NoDup_Znth_inj : forall {A} {d : Inhabitant A} l i j (HNoDup : NoDup l)
  (Hi : 0 <= i < Zlength l) (Hj : 0 <= j < Zlength l) (Heq : Znth i l = Znth j l ),
  i = j.
Proof.
  induction l; intros.
  { rewrite Zlength_nil in *; omega. }
  inv HNoDup.
  rewrite Zlength_cons in *.
  rewrite !Znth_cons_eq in Heq.
  destruct (eq_dec i 0), (eq_dec j 0); subst; auto.
  - contradiction H1; apply Znth_In; omega.
  - contradiction H1; apply Znth_In; omega.
  - exploit (IHl (i - 1) (j - 1)); auto; omega.
Qed.

Lemma rotate_In : forall {A} (x : A) n m l, 0 <= m - n <= Zlength l -> In x (rotate l n m) <-> In x l.
Proof.
  unfold rotate; intros.
  replace l with (sublist 0 (m - n) l ++ sublist (m - n) (Zlength l) l) at 4
    by (rewrite sublist_rejoin, sublist_same; auto; omega).
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
  rewrite !Zlength_correct in *; omega.
Qed.

Lemma Forall_rotate : forall {A} P (l : list A) n m, Forall P l ->
  Forall P (rotate l m n).
Proof.
  intros; unfold rotate.
  rewrite Forall_app; split; apply Forall_sublist; auto.
Qed.

Lemma Forall_repeat : forall {A} (P : A -> Prop) x n, P x -> Forall P (repeat x n).
Proof.
  induction n; simpl; auto.
Qed.

Lemma Forall_complete : forall P l m, Forall P l -> P (vptrofs 0) ->
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
  { unfold sublist; repeat rewrite firstn_length, skipn_length.
    repeat rewrite Zlength_correct; rewrite H0; omega. }
  erewrite <- sublist_same with (al := l1), <- sublist_rejoin with (mid := m - n); auto; try omega.
  rewrite Hfirst, Hskip, sublist_rejoin, sublist_same; auto; try omega.
  repeat rewrite Zlength_correct in *; rewrite H0 in *; omega.
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
  rewrite app_length, repeat_length; rewrite Zlength_correct in H.
  rep_omega.
Qed.

Lemma Zlength_rotate : forall {A} (l : list A) n m, 0 <= n <= m -> m <= Zlength l ->
  Zlength (rotate l n m) = Zlength l.
Proof.
  intros; unfold rotate.
  rewrite Zlength_app; repeat rewrite Zlength_sublist; omega.
Qed.

Lemma Zlength_repeat : forall {A} (x : A) n, Zlength (repeat x n) = Z.of_nat n.
Proof.
  intros; rewrite Zlength_correct, repeat_length; auto.
Qed.

Lemma Zlength_complete : forall l m, Zlength l <= m -> Zlength (complete m l) = m.
Proof.
  intros; unfold complete.
  rewrite Zlength_app, Zlength_repeat; rewrite Zlength_correct in *; rep_omega.
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
  rewrite Zquot.Zrem_Zmod_pos; repeat rewrite Int.signed_repr; auto; omega.
Qed.

Lemma repeat_list_repeat : forall {A} n (x : A), repeat x n = list_repeat n x.
Proof.
  induction n; auto; simpl; intro.
  rewrite IHn; auto.
Qed.

Lemma sublist_repeat : forall {A} i j k (v : A), 0 <= i -> i <= j <= k ->
  sublist i j (repeat v (Z.to_nat k)) = repeat v (Z.to_nat (j - i)).
Proof.
  intros; repeat rewrite repeat_list_repeat; apply sublist_list_repeat; auto.
Qed.

Lemma Znth_head : forall reqs head m, Zlength reqs <= m -> 0 <= head < m ->
  Zlength reqs > 0 ->
  Znth head (rotate (complete m reqs) head m) = Znth 0 reqs.
Proof.
  intros; unfold rotate.
  assert (Zlength (sublist (m - head) (Zlength (complete m reqs)) (complete m reqs)) = head) as Hlen.
  { 
rewrite Zlength_sublist; rewrite Zlength_complete; omega. }
  rewrite app_Znth2; rewrite Hlen; [|omega].
  rewrite Zminus_diag.
  rewrite Znth_sublist; try omega.
  rewrite Znth_complete; auto; omega.
Qed.

Lemma Znth_repeat : forall {A} {x : Inhabitant A} n i, Znth i (repeat default n) = default.
Proof.
  induction n; simpl; intro.
  - apply Znth_nil.
  - destruct (Z_lt_dec i 0); [apply Znth_underflow; auto|].
    destruct (eq_dec i 0); [subst; apply Znth_0_cons | rewrite Znth_pos_cons; eauto; omega].
Qed.

Lemma Znth_repeat' : forall {A} {d: Inhabitant A} (x : A) n i, 
    0 <= i < Z.of_nat n -> Znth i (repeat x n)  = x.
Proof.
  induction n; intros; [simpl in *; omega|].
  rewrite Nat2Z.inj_succ in H; simpl.
  destruct (eq_dec i 0).
  - subst; apply Znth_0_cons.
  - rewrite Znth_pos_cons by omega; apply IHn; omega.
Qed.

Lemma rotate_1 : forall v l n m, 0 <= n < m -> Zlength l < m ->
  rotate (upd_Znth 0 (complete m (v :: l)) (vptrofs 0)) n m =
  rotate (complete m l) ((n + 1) mod m) m.
Proof.
  intros.
  unfold complete at 1; simpl.
  unfold upd_Znth; simpl.
  rewrite Zlength_cons; simpl.
  rewrite sublist_1_cons, sublist_same; auto; [|omega].
  unfold rotate.
  rewrite Zlength_cons; simpl.
  rewrite sublist_S_cons; [|omega].
  rewrite sublist_0_cons; [|omega].
  destruct (eq_dec (n + 1) m).
  - subst; rewrite Z.mod_same; [|omega].
    autorewrite with sublist.
    rewrite Zlength_complete, sublist_nil; [|omega].
    rewrite sublist_same; auto; [|rewrite Zlength_complete; omega].
    rewrite <- app_assoc; unfold complete.
    repeat rewrite Z2Nat.inj_add; try omega.
    rewrite NPeano.Nat.add_sub_swap with (p := length l); [|rewrite Zlength_correct in *; rep_omega].
    rewrite repeat_plus; simpl; do 3 f_equal; omega.
  - rewrite Zmod_small; [|omega].
    rewrite (sublist_split (m - (n + 1)) (Zlength (complete m l) - 1)); try rewrite Zlength_complete; try omega.
    rewrite <- app_assoc, (sublist_one (m - 1)); try rewrite Zlength_complete; try omega; simpl.
    assert (length l < Z.to_nat m)%nat by (rewrite Zlength_correct in *; rep_omega).
    unfold complete.
    replace (Z.to_nat m - length l)%nat with (Z.to_nat m - S (length l) + 1)%nat; [|omega].
    rewrite repeat_plus, app_assoc; simpl.
    repeat rewrite Zlength_app.
    assert (m - 1 = Zlength l + Zlength (repeat (vptrofs 0) (Z.to_nat m - S (Datatypes.length l)))) as Heq.
    { rewrite Zlength_repeat, Nat2Z.inj_sub, Z2Nat.id, Nat2Z.inj_succ, <- Zlength_correct; omega. }
    rewrite (sublist_app1 _ _ _ (_ ++ _)%list); rewrite ?Zlength_app; try omega.
    rewrite (sublist_app1 _ _ _ (_ ++ _)%list); try rewrite Zlength_app; try omega.
    f_equal; f_equal; try omega.
    + rewrite app_Znth2, Zlength_app, Heq, Zminus_diag, Znth_0_cons; auto.
      rewrite Zlength_app; omega.
    + f_equal; omega.
Qed.

Lemma upd_complete_gen : forall {A} (l : list A) x n y, Zlength l < n ->
  upd_Znth (Zlength l) (l ++ repeat y (Z.to_nat (n - Zlength l))) x =
  (l ++ [x]) ++ repeat y (Z.to_nat (n - Zlength (l ++ [x]))).
Proof.
  intros.
  rewrite upd_Znth_app2, Zminus_diag.
  destruct (Z.to_nat (n - Zlength l)) eqn: Hn.
  - apply Z2Nat.inj with (m := 0) in Hn; omega.
  - simpl; rewrite upd_Znth0, Zlength_cons, sublist_1_cons.
    unfold Z.succ; rewrite Z.add_simpl_r, sublist_same; auto.
    rewrite <- app_assoc, Zlength_app, Zlength_cons, Zlength_nil; simpl.
    rewrite Z.sub_add_distr, Z2Nat.inj_sub, Hn by computable; simpl.
    rewrite Nat.sub_0_r; auto.
  - pose proof (Zlength_nonneg (repeat y (Z.to_nat (n - Zlength l)))); omega.
Qed.

Lemma upd_complete' : forall l x n, (length l < n)%nat ->
  upd_Znth (Zlength l) (map Vint (map Int.repr l) ++ repeat Vundef (n - length l)) (Vint (Int.repr x)) =
  map Vint (map Int.repr (l ++ [x])) ++ repeat Vundef (n - length (l ++ [x])).
Proof.
  intros.
  rewrite upd_Znth_app2; [|repeat rewrite Zlength_map; repeat rewrite Zlength_correct; omega].
  repeat rewrite Zlength_map.
  rewrite Zminus_diag.
  rewrite app_length; simpl plus.
  destruct (n - length l)%nat eqn: Hminus; [omega|].
  replace (n - (length l + 1))%nat with n0 by omega.
  rewrite upd_Znth0, !map_app, <- app_assoc; simpl.
  rewrite sublist_1_cons, Zlength_cons, sublist_same; auto; omega.
Qed.

(*
Lemma Znth_indep : forall {A} i (l : list A) d d', 
   0 <= i < Zlength l -> Znth i l d = Znth i l d'.
Proof.
  intros; unfold Znth.
  destruct (zlt i 0); [omega|].
  apply nth_indep.
  rewrite Zlength_correct in *; rep_omega.
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
    apply map_ext; intro; omega.
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
  induction n; intros; simpl; destruct l; simpl in *; try omega; auto.
  { inversion H. }
  rewrite Nat2Z.inj_succ.
  rewrite Znth_pos_cons; [|omega].
  unfold Z.succ; rewrite Z.add_simpl_r.
  erewrite IHn; auto; omega.
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
  - rewrite Znth_nil; simpl in *; rewrite Nat2Z.inj_0 in *; omega.
  - destruct (eq_dec n 0).
    + subst; apply Znth_0_cons.
    + rewrite Nat2Z.inj_succ in *.
      rewrite Znth_pos_cons by omega.
      rewrite Znth_map. rewrite IHm. omega. omega.
      rewrite Zlength_upto. omega.
Qed.

Transparent Z.of_nat.

Lemma In_Znth : forall {A} {d: Inhabitant A} (l : list A) x,
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l = x.
Proof.
  unfold Znth; intros.
  apply In_nth with (d := d) in H; destruct H as (n & ? & ?).
  exists (Z.of_nat n); split.
  - rewrite Zlength_correct; omega.
  - destruct (zlt (Z.of_nat n) 0); [omega|].
    rewrite Nat2Z.id; auto.
Qed.

Lemma In_upd_Znth_old : forall {A}{d: Inhabitant A} i (x y : A) l, In x l -> x <> Znth i l -> 0 <= i <= Zlength l ->
  In x (upd_Znth i l y).
Proof.
  intros.
  apply In_Znth in H; destruct H as (j & ? & ?); subst.
  unfold upd_Znth.
  destruct (eq_dec j i); [subst; contradiction|].
  rewrite in_app; simpl.
  destruct (zlt j i); [left | right; right].
  - erewrite <- (Z.add_0_r j), <- Znth_sublist; [apply Znth_In; rewrite Zlength_sublist| |]; auto; omega.
  - erewrite <- (Z.sub_simpl_r _ (i + 1)), <- Znth_sublist; [apply Znth_In; rewrite Zlength_sublist| |]; omega.
Qed.

Lemma Znth_combine : forall {A B} {a: Inhabitant A} {b: Inhabitant B} i (l1: list A) (l2: list B), 
   Zlength l1 = Zlength l2 ->
  Znth i (combine l1 l2) = (Znth i l1, Znth i l2).
Proof.
  intros; unfold Znth.
  destruct (zlt i 0); auto.
  apply combine_nth.
  rewrite !Zlength_correct in *; rep_omega.
Qed.

Lemma Zlength_combine : forall {A B} (l : list A) (l' : list B),
  Zlength (combine l l') = Z.min (Zlength l) (Zlength l').
Proof.
  intros; rewrite !Zlength_correct, combine_length, Nat2Z.inj_min; auto.
Qed.

Lemma nth_Znth : forall {A}{d: Inhabitant A} i l, nth i l default = Znth (Z.of_nat i) l.
Proof.
  intros; unfold Znth.
  destruct (zlt (Z.of_nat i) 0); [omega|].
  rewrite Nat2Z.id; auto.
Qed.

Lemma upd_Znth_cons : forall {A} i a l (x : A), i > 0 ->
  upd_Znth i (a :: l) x = a :: upd_Znth (i - 1) l x.
Proof.
  intros; unfold upd_Znth, sublist.sublist; simpl.
  repeat rewrite Z.sub_0_r.
  destruct (Z.to_nat i) eqn: Hi.
  { exploit Z2Nat_inj_0; eauto; omega. }
  rewrite Zlength_cons; repeat rewrite Z2Nat.inj_add; try omega.
  repeat rewrite Z2Nat.inj_sub; try omega.
  rewrite Hi; simpl.
  rewrite Nat.sub_0_r.
  do 4 f_equal.
  rewrite Z2Nat.inj_succ; [|rewrite Zlength_correct; omega].
  repeat rewrite Z2Nat.inj_add; try omega.
  rewrite Z2Nat.inj_sub; try omega.
  simpl plus; omega.
Qed.

Lemma upd_Znth_triv : forall {A}{d: Inhabitant A} i (l : list A) x (Hi : 0 <= i < Zlength l),
  Znth i l = x -> upd_Znth i l x = l.
Proof.
  intros; unfold upd_Znth.
  setoid_rewrite <- (firstn_skipn (Z.to_nat i) l) at 4.
  erewrite skipn_cons, Z2Nat.id, H; try omega; [|rewrite Zlength_correct in *; rep_omega].
  unfold sublist.
  rewrite Z.sub_0_r, Z2Nat.inj_add, NPeano.Nat.add_1_r; try omega.
  setoid_rewrite firstn_same at 2; auto.
  rewrite Z2Nat.inj_sub, Zlength_correct, Nat2Z.id, Z2Nat.inj_add, skipn_length; simpl; omega.
Qed.

Lemma combine_upd_Znth : forall {A B} (l1 : list A) (l2 : list B) i x1 x2, 0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 -> combine (upd_Znth i l1 x1) (upd_Znth i l2 x2) = upd_Znth i (combine l1 l2) (x1, x2).
Proof.
  induction l1; simpl; intros; [rewrite Zlength_nil in *; omega|].
  destruct l2; [rewrite Zlength_nil in *; omega|].
  rewrite !Zlength_cons in *.
  destruct (eq_dec i 0).
  - subst; rewrite !upd_Znth0, !Zlength_cons, !sublist_1_cons, !sublist_same; auto; omega.
  - rewrite !upd_Znth_cons; try omega; simpl.
    rewrite IHl1; auto; omega.
Qed.

Corollary combine_upd_Znth1 : forall {A B}{d: Inhabitant B} (l1 : list A) (l2 : list B) i x,
   0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 ->
   combine (upd_Znth i l1 x) l2 = upd_Znth i (combine l1 l2) (x, Znth i l2).
Proof.
  intros; rewrite <- combine_upd_Znth by auto.
  erewrite upd_Znth_triv with (l := l2); eauto; omega.
Qed.

Corollary combine_upd_Znth2 : forall {A B}{d: Inhabitant A} (l1 : list A) (l2 : list B) i x, 0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 -> combine l1 (upd_Znth i l2 x) = upd_Znth i (combine l1 l2) (Znth i l1, x).
Proof.
  intros; rewrite <- combine_upd_Znth by auto.
  erewrite upd_Znth_triv with (l := l1); eauto; omega.
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
  induction l; simpl; intros; [rewrite Zlength_nil in *; omega|].
  rewrite app_length; destruct (eq_dec i 0).
  - subst; rewrite Znth_0_cons; omega.
  - rewrite Znth_pos_cons by omega.
    rewrite Zlength_cons in *; etransitivity; [apply IHl|]; omega.
Qed.

Lemma length_concat_upd : forall {A} {d: Inhabitant A} l i (l' : list A) (Hi : 0 <= i < Zlength l),
  length (concat (upd_Znth i l l')) = (length (concat l) + length l' - length (Znth i l))%nat.
Proof.
  induction l; intros; [rewrite Zlength_nil in *; omega|].
  destruct (eq_dec i 0).
  - subst; rewrite upd_Znth0, Znth_0_cons, sublist_1_cons.
    rewrite Zlength_cons in *; rewrite sublist_same by (auto; omega); simpl.
    rewrite !app_length; omega.
  - rewrite upd_Znth_cons, Znth_pos_cons by omega; simpl.
    rewrite Zlength_cons in *.
    rewrite !app_length, IHl by omega.
    exploit (length_concat_min l (i - 1)); omega.
Qed.

Lemma sepcon_rev : forall l, fold_right sepcon emp (rev l) = fold_right sepcon emp l.
Proof.
  induction l; simpl; auto.
  rewrite sepcon_app; simpl.
  rewrite sepcon_emp, sepcon_comm, IHl; auto.
Qed.

Lemma incl_nil : forall {A} (l : list A), incl [] l.
Proof.
  repeat intro; contradiction.
Qed.
Hint Resolve incl_nil.

Lemma incl_cons_out : forall {A} (a : A) l1 l2, incl l1 (a :: l2) -> ~In a l1 -> incl l1 l2.
Proof.
  intros; intros ? Hin; specialize (H _ Hin); destruct H; auto; subst; contradiction.
Qed.

Lemma In_upto : forall n i, In i (upto n) <-> 0 <= i < Z.of_nat n.
Proof.
  induction n; intro.
  - simpl; split; try contradiction; omega.
  - rewrite Nat2Z.inj_succ; simpl.
    rewrite in_map_iff; split.
    + intros [? | ?]; [omega|].
      destruct H as (? & ? & ?); subst; rewrite IHn in *; omega.
    + intro; destruct (eq_dec i 0); [auto | right].
      exists (i - 1); rewrite IHn; omega.
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
  rewrite Zlength_cons in *; destruct n; [rewrite Zlength_correct in *; simpl in *; omega | simpl].
  rewrite IHl1; auto.
  rewrite Nat2Z.inj_succ in *; omega.
Qed.

Lemma combine_const2 : forall {A B} (x : A) n (l2 : list B), Z.of_nat n >= Zlength l2 ->
  combine (repeat x n) l2 = map (fun b => (x, b)) l2.
Proof.
  induction n; destruct l2; auto; intros; rewrite ?Nat2Z.inj_succ, ?Zlength_nil, ?Zlength_cons in *;
    simpl in *; try (rewrite Zlength_correct in *; omega).
  rewrite IHn; auto; omega.
Qed.

Lemma map_const: forall {A B} (c : A) (l : list B), map (fun _ => c) l = repeat c (length l).
Proof.
  induction l; auto; simpl.
  rewrite IHl; auto.
Qed.

Lemma In_upd_Znth : forall {A} i l (x y : A), In x (upd_Znth i l y) -> x = y \/ In x l.
Proof.
  unfold upd_Znth; intros.
  rewrite in_app in H; destruct H as [? | [? | ?]]; auto; right; eapply sublist_In; eauto.
Qed.

Lemma upd_Znth_In : forall {A} i l (x : A), In x (upd_Znth i l x).
Proof.
  intros; unfold upd_Znth.
  rewrite in_app; simpl; auto.
Qed.

Lemma NoDup_Znth_iff : forall {A}{d: Inhabitant A} (l : list A),
  NoDup l <-> forall i j (Hi : 0 <= i < Zlength l)
                            (Hj : 0 <= j < Zlength l), Znth i l = Znth j l -> i = j.
Proof.
  split; intros; [eapply NoDup_Znth_inj; eauto|].
  induction l; rewrite ?Zlength_cons in *; constructor.
  - intro Hin; eapply In_Znth in Hin; destruct Hin as (j & ? & Hj).
    exploit (H 0 (j + 1)); try omega.
    rewrite !Znth_cons_eq; simpl.
    if_tac; [omega|].
    rewrite Z.add_simpl_r; eauto.
  - apply IHl; intros.
    exploit (H (i + 1) (j + 1)); try omega.
    rewrite !Znth_cons_eq, !Z.add_simpl_r.
    if_tac; [omega|].
    if_tac; [omega | auto].
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
  induction l; simpl; intros; [rewrite Zlength_nil in *; omega|].
  rewrite Zlength_cons in *.
  destruct (eq_dec i 0).
  - subst; rewrite upd_Znth0, Zlength_cons, sublist_1_cons, sublist_same by (auto; omega); simpl.
    rewrite Znth_0_cons in Hless; subst.
    rewrite <- app_assoc, NoDup_app_swap, <- app_assoc, NoDup_app_iff, NoDup_app_swap in Hl; tauto.
  - rewrite upd_Znth_cons by omega; simpl.
    rewrite Znth_pos_cons in Hless by omega.
    rewrite NoDup_app_iff in Hl; rewrite NoDup_app_iff.
    destruct Hl as (? & ? & Hsep).
    split; [auto|]; split.
    + eapply IHl; eauto; omega.
    + intros ?? Hin; eapply Hsep; eauto.
      eapply concat_less_incl; eauto; omega.
Qed.

Lemma Forall2_Znth : forall {A B}{d1: Inhabitant A}{d2: Inhabitant B} (P : A -> B -> Prop) l1 l2 (Hall : Forall2 P l1 l2) i
  (Hi : 0 <= i < Zlength l1), P (Znth i l1) (Znth i l2).
Proof.
  induction 1; intros.
  { rewrite Zlength_nil in *; omega. }
  rewrite Zlength_cons in *.
  destruct (eq_dec i 0).
  - subst; rewrite !Znth_0_cons; auto.
  - rewrite !Znth_pos_cons; try omega.
    apply IHHall; omega.
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
  intros; unfold upd_Znth.
  pose proof (mem_lemmas.Forall2_Zlength H) as Hlen.
  erewrite <- sublist_same with (al := l1), sublist_split with (mid := i) in H; auto; try omega.
  erewrite <- sublist_same with (al := l2), sublist_split with (al := l2)(mid := i) in H; auto; try omega.
  apply Forall2_app_inv in H.
  destruct H as (? & Hall); apply Forall2_app; auto.
  constructor; auto.
  destruct (eq_dec i (Zlength l1)).
  - rewrite !sublist_nil_gen; auto; omega.
  - rewrite Z.add_comm.
    replace (Zlength l1) with (Zlength l1 - i + i) by omega.
    replace (Zlength l2) with (Zlength l2 - i + i) by omega.
    erewrite <- !sublist_sublist with (j := Zlength l1); try omega.
    inversion Hall as [Hl1 Hl2 | ?????? Hl1 Hl2].
    + rewrite !Hlen, <- Hl2.
      unfold sublist; rewrite !skipn_nil, !firstn_nil; auto.
    + rewrite sublist_1_cons, !Hlen, <- Hl2, sublist_1_cons.
      unfold sublist; simpl; apply Forall2_firstn; auto.
  - apply Nat2Z.inj; rewrite <- !Zlength_correct.
    autorewrite with sublist; auto.
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

Lemma sublist_max_length : forall {A} i j (al : list A), Zlength (sublist i j al) <= Zlength al.
Proof.
  intros; unfold sublist.
  rewrite Zlength_firstn, Zlength_skipn.
  rewrite Z.min_le_iff; right.
  pose proof (Zlength_nonneg al).
  apply Z.max_lub; try omega.
  rewrite <- Z.le_sub_nonneg; apply Z.le_max_l.
Qed.

Lemma Forall2_sublist : forall {A B} (P : A -> B -> Prop) l1 l2 i j, Forall2 P l1 l2 -> 0 <= i ->
  Forall2 P (sublist i j l1) (sublist i j l2).
Proof.
  intros; revert j; revert dependent i; induction H; intros.
  - rewrite !sublist_of_nil; constructor.
  - destruct (Z_le_dec j i); [rewrite !sublist_nil_gen; auto; constructor|].
    destruct (eq_dec i 0).
    + subst; rewrite !sublist_0_cons by omega.
      constructor; auto.
    + rewrite !sublist_S_cons by omega.
      apply IHForall2; omega.
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
  apply Forall2_upd_Znth; eauto; omega.
  apply mem_lemmas.Forall2_Zlength in H; omega.
Qed.

Lemma Forall2_upd_Znth_r : forall {A B}{d: Inhabitant A} (P : A -> B -> Prop) l1 l2 i x, Forall2 P l1 l2 ->
  P (Znth i l1) x -> 0 <= i < Zlength l1 -> Forall2 P l1 (upd_Znth i l2 x).
Proof.
  intros.
  erewrite <- upd_Znth_triv with (l := l1)(i0 := i) by (eauto; omega).
  apply Forall2_upd_Znth; eauto.
  apply mem_lemmas.Forall2_Zlength in H; omega.
Qed.

Lemma Forall2_eq_upto : forall {A B}{d1: Inhabitant A}{d2: Inhabitant B} (P : A -> B -> Prop) l1 l2, Forall2 P l1 l2 <->
  Zlength l1 = Zlength l2 /\ Forall (fun i => P (Znth i l1) (Znth i l2)) (upto (Z.to_nat (Zlength l1))).
Proof.
  induction l1; destruct l2; rewrite ?Zlength_cons, ?Zlength_nil; try solve [split; intro H; inv H;
    try (rewrite Zlength_correct in *; omega)]; simpl.
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
      rewrite !Znth_pos_cons, Z.add_simpl_l by omega; auto.
    + destruct H as (? & Ha & Hall); inversion Ha as [|?? HP]; subst.
      rewrite !Znth_0_cons in HP.
      constructor; auto.
      rewrite IHl1; split; [omega|].
      rewrite Forall_forall in *; intros ? Hin.
      specialize (Hall _ Hin); simpl in *.
      rewrite In_upto in Hin.
      rewrite !Znth_pos_cons, Z.add_simpl_l in Hall by omega; auto.
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
  destruct (Z_lt_dec i (Zlength l)); [omega|].
  rewrite Znth_overflow in H; [contradiction H; auto | omega].
Qed.

Lemma sublist_next : forall {A}{d: Inhabitant A} i j l,
      0 <= i < j -> j <= Zlength l ->
  sublist i j l = Znth i l :: sublist (i + 1) j l.
Proof.
  intros.
  rewrite Znth_cons_sublist; [|omega].
  apply sublist_split; omega.
Qed.

Lemma upd_init : forall {A} (l : list A) i b v v', i < b -> Zlength l = i ->
  upd_Znth i (l ++ repeat v (Z.to_nat (b - i))) v' = l ++ v' :: repeat v (Z.to_nat (b - (i + 1))).
Proof.
  intros.
  rewrite upd_Znth_app2; rewrite ?Zlength_repeat, ?Z2Nat.id; try omega.
  subst; rewrite Zminus_diag, upd_Znth0.
  destruct (Z.to_nat (b - Zlength l)) eqn: Hi.
  { change O with (Z.to_nat 0) in Hi; apply Z2Nat.inj in Hi; omega. }
  simpl; rewrite sublist_1_cons, sublist_same; try rewrite Zlength_cons, !Zlength_repeat; try omega.
  replace (Z.to_nat (b - (Zlength l + 1))) with n; auto.
  rewrite Z.sub_add_distr, Z2Nat.inj_sub; try omega.
  setoid_rewrite Hi; simpl; omega.
Qed.

Corollary upd_init_const : forall {A} i b (v v' : A), 0 <= i < b ->
  upd_Znth i (repeat v' (Z.to_nat i) ++ repeat v (Z.to_nat (b - i))) v' =
  repeat v' (Z.to_nat (i + 1)) ++ repeat v (Z.to_nat (b - (i + 1))).
Proof.
  intros.
  rewrite upd_init; try rewrite Zlength_repeat, Z2Nat.id; auto; try omega.
  rewrite Z2Nat.inj_add, repeat_plus, <- app_assoc; auto; omega.
Qed.

Lemma list_Znth_eq : forall {A}{d: Inhabitant A} (l : list A),
    l = map (fun j => Znth j l) (upto (length l)).
Proof.
  induction l; simpl; intros; auto.
  rewrite Znth_0_cons, IHl, map_map, map_length, upto_length.
  f_equal; apply map_ext_in; intros.
  rewrite Znth_pos_cons, <- IHl.
  unfold Z.succ; rewrite Z.add_simpl_r; auto.
  { rewrite In_upto in *; omega. }
Qed.

Arguments eq_dec _ _ _ _ : simpl never.

Lemma upd_Znth_eq : forall {A} {EqDec : EqDec A} {d: Inhabitant A} (x : A) (l : list A) i, 0 <= i < Zlength l ->
  upd_Znth i l x = map (fun j => if eq_dec j i then x else Znth j l) (upto (length l)).
Proof.
  induction l; simpl; intros.
  { rewrite Zlength_nil in *; omega. }
  destruct (eq_dec 0 i).
  - subst; rewrite upd_Znth0, Zlength_cons, sublist_1_cons, sublist_same; auto; try omega.
    rewrite list_Znth_eq with (l0 := l) at 1.
    rewrite map_map.
    f_equal; apply map_ext_in; intros.
    rewrite In_upto in *.
    destruct (eq_dec (Z.succ a0) 0); [omega|].
    rewrite Znth_pos_cons; [|omega].
    f_equal; omega.
  - rewrite Znth_0_cons, upd_Znth_cons; [|omega].
    rewrite Zlength_cons in *.
    rewrite IHl, map_map; [|omega].
    f_equal; apply map_ext_in; intros.
    rewrite In_upto in *.
    destruct (eq_dec a0 (i - 1)), (eq_dec (Z.succ a0) i); try omega; auto.
    rewrite Znth_pos_cons; [|omega].
    f_equal; omega.
Qed.

Lemma upd_Znth_diff' : forall {A}{d: Inhabitant A} i j l (u : A),
    0 <= j < Zlength l -> i <> j ->
  Znth i (upd_Znth j l u) = Znth i l.
Proof.
  intros.
  destruct (zlt i 0).
  { rewrite !Znth_underflow; auto. }
  destruct (zlt i (Zlength l)).
  apply upd_Znth_diff; auto; omega.
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
    auto; try (rewrite Zlength_correct in *; omega).
  exploit (Heq 0); [rewrite Zlength_correct; omega|].
  rewrite !Znth_0_cons; intro; subst.
  f_equal; apply IHl1; [omega|].
  intros; specialize (Heq (j + 1)); rewrite !Znth_pos_cons in Heq; try omega.
  rewrite !Z.add_simpl_r in *; apply Heq; omega.
Qed.

Corollary upd_Znth_eq' : forall {A}{d: Inhabitant A} x (l1 l2 : list A) i (Hi : 0 <= i < Zlength l1)
  (Hlen : Zlength l1 = Zlength l2)
  (Heq : forall j, 0 <= j < Zlength l1 -> j <> i -> Znth j l1 = Znth j l2),
  upd_Znth i l1 x = upd_Znth i l2 x.
Proof.
  intros.
  assert (Zlength (upd_Znth i l1 x) = Zlength (upd_Znth i l2 x)).
  { rewrite !upd_Znth_Zlength; auto; omega. }
  apply list_Znth_eq'; auto.
  intros ? Hj; destruct (eq_dec j i).
  - subst; rewrite !upd_Znth_same; auto; omega.
  - rewrite !upd_Znth_diff'; rewrite upd_Znth_Zlength in Hj; auto; omega.
Qed.

Lemma upd_Znth_twice : forall {A} i l (x y : A), 0 <= i < Zlength l ->
  upd_Znth i (upd_Znth i l x) y = upd_Znth i l y.
Proof.
  intros; unfold upd_Znth.
  rewrite !sublist_app; rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_sublist; try omega.
  rewrite 2Z.min_l, 2Z.min_r, 2Z.max_r, 2Z.max_l; try omega.
  rewrite !sublist_nil, app_nil_r; simpl.
  rewrite sublist_S_cons, !sublist_sublist; try omega.
  f_equal; f_equal; [|f_equal]; omega.
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
  destruct (f a); simpl; omega.
Qed.

Lemma Zlength_filter : forall {A} f (l : list A), Zlength (filter f l) <= Zlength l.
Proof.
  intros.
  setoid_rewrite Zlength_correct at 2.
  rewrite filter_length with (f0 := f).
  rewrite Nat2Z.inj_add.
  rewrite <- Zlength_correct; omega.
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
  - rewrite Zlength_nil; omega.
  - rewrite Zlength_cons, Z.mul_succ_r.
    specialize (IHForall m); omega.
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
    intros (? & ? & ?); rewrite In_upto in *; omega.
  - apply FinFun.Injective_map_NoDup; auto.
    intros ???; omega.
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
    rewrite Zlength_correct in H.
    apply Z2Nat.inj_lt in H; try omega.
    rewrite Nat2Z.id in H; omega. }
  destruct (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n))) eqn: Hfilter;
    [simpl in *; omega|].
  assert (In z (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n)))) as Hin
    by (rewrite Hfilter; simpl; auto).
  rewrite filter_In, In_upto, Z2Nat.id in Hin; [|rewrite Zlength_correct in *; omega].
  destruct Hin; destruct (in_dec eq_dec z l); try discriminate; eauto.
Qed.

Lemma In_sublist_upto : forall n x i j, In x (sublist i j (upto n)) -> 0 <= i ->
  i <= x < j /\ x < Z.of_nat n.
Proof.
  induction n; intros.
  - unfold sublist in H; rewrite skipn_nil, firstn_nil in H; contradiction.
  - rewrite Nat2Z.inj_succ; simpl in *.
    destruct (zlt 0 j).
    destruct (eq_dec i 0).
    + subst; rewrite sublist_0_cons in H; try omega; destruct H; [omega|].
      rewrite sublist_map, in_map_iff in H; destruct H as (? & ? & H); subst.
      destruct (zlt 0 (j - 1)).
      exploit IHn; eauto; omega.
      { rewrite sublist_nil_gen in H; [contradiction | omega]. }
    + rewrite sublist_S_cons in H; [|omega].
      rewrite sublist_map, in_map_iff in H; destruct H as (? & ? & H); subst.
      destruct (zlt 0 (j - 1)).
      exploit IHn; eauto; omega.
      { rewrite sublist_nil_gen in H; [contradiction | omega]. }
    + rewrite sublist_nil_gen in H; [contradiction | omega].
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
  intros; omega.
Qed.

Lemma firstn_all : forall {A} n (l : list A), (length l <= n)%nat -> firstn n l = l.
Proof.
  induction n; destruct l; auto; simpl; intros; try omega.
  rewrite IHn; auto; omega.
Qed.

Lemma sublist_all : forall {A} i (l : list A), Zlength l <= i -> sublist 0 i l = l.
Proof.
  intros; unfold sublist; simpl.
  apply firstn_all.
  rewrite Zlength_correct in *; rep_omega.
Qed.

Lemma sublist_prefix : forall {A} i j (l : list A), sublist 0 i (sublist 0 j l) = sublist 0 (Z.min i j) l.
Proof.
  intros.
  destruct (Z_le_dec i 0).
  { rewrite !sublist_nil_gen; auto.
    rewrite Z.min_le_iff; auto. }
  destruct (Z.min_spec i j) as [(? & ->) | (? & ->)].
  - rewrite sublist_sublist, !Z.add_0_r by omega; auto.
  - apply sublist_all.
    destruct (Z_le_dec j 0); [rewrite sublist_nil_gen; auto; rewrite Zlength_nil; omega|].
    destruct (Z_le_dec j (Zlength l)).
    rewrite Zlength_sublist; try omega.
    { pose proof (sublist_max_length 0 j l); omega. }
Qed.

Lemma sublist_suffix : forall {A} i j (l : list A), 0 <= i -> 0 <= j ->
  sublist i (Zlength l - j) (sublist j (Zlength l) l) = sublist (i + j) (Zlength l) l.
Proof.
  intros.
  destruct (Z_le_dec (Zlength l - j) i).
  { rewrite !sublist_nil_gen; auto; omega. }
  rewrite sublist_sublist by omega.
  rewrite Z.sub_simpl_r; auto.
Qed.

Lemma sublist_parts1 : forall {A} i j (l : list A), 0 <= i -> sublist i j l = sublist i j (sublist 0 j l).
Proof.
  intros.
  destruct (Z_le_dec j i).
  { rewrite !sublist_nil_gen; auto. }
  rewrite sublist_sublist by omega.
  rewrite !Z.add_0_r; auto.
Qed.

Lemma sublist_parts2 : forall {A} i j (l : list A), 0 <= i -> j <= Zlength l ->
  sublist i j l = sublist 0 (j - i) (sublist i (Zlength l) l).
Proof.
  intros.
  destruct (Z_le_dec j i).
  { rewrite !sublist_nil_gen; auto; omega. }
  rewrite sublist_sublist; try omega.
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
    rewrite Z.max_l by omega.
    rewrite <- Hl2; auto. }
  assert (Zlength l1 = Zlength l2) as Heq.
  { assert (Zlength (sublist i (Zlength l1) l1) = Zlength (sublist i (Zlength l2) l2)) as Heq by congruence.
    destruct (Z_le_dec (Zlength l2) i).
    { rewrite sublist_nil_gen with (l0 := l2), Zlength_nil in Heq; auto.
      rewrite !Zlength_sublist in Heq; omega. }
    rewrite !Zlength_sublist in Heq; omega. }
  intros; destruct (Z.max_spec i j) as [(? & ->) | (? & ->)].
  - replace (sublist _ _ _) with (sublist (j - i) (Zlength l2 - i) (sublist i (Zlength l2) l2)).
    rewrite <- Hl2, sublist_sublist, !Z.sub_simpl_r by omega.
    rewrite <- Heq; auto.
    { rewrite sublist_sublist, !Z.sub_simpl_r by omega; auto. }
  - rewrite <- Hl2.
    replace (sublist _ _ _) with (sublist (i - j) (Zlength l1 - j) (sublist j (Zlength l1) l1)).
    apply Forall_sublist; auto.
    { rewrite sublist_sublist, !Z.sub_simpl_r; auto; omega. }
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
  induction l; destruct ls; simpl; intros; try rewrite Zlength_nil in *; try omega.
  rewrite !Zlength_cons in *.
  destruct (eq_dec i 0); subst; auto.
  rewrite !Znth_pos_cons; try omega.
  apply IHl; omega.
Qed.

Lemma Znth_extend_ge : forall {A}{d: Inhabitant A}  (l : list A) ls i, Zlength l <= i ->
  Znth i (extend l ls) = Znth i ls.
Proof.
  induction l; destruct ls; auto; simpl; intros.
  destruct (zlt i 0); [rewrite !Znth_underflow; auto|].
  rewrite Zlength_cons in *.
  destruct (eq_dec i 0); [rewrite Zlength_correct in *; omega|].
  rewrite !Znth_pos_cons; try omega.
  apply IHl; omega.
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
  induction l; destruct ls; simpl; intros; try rewrite Zlength_nil in *; try omega.
  rewrite !Zlength_cons in *.
  destruct (eq_dec i 0); subst; auto.
  rewrite !Znth_pos_cons; try omega.
  apply IHl; omega.
Qed.

Lemma Znth_extendr_ge : forall {A}{d: Inhabitant A}  (l : list A) ls i, Zlength l <= i ->
  Znth i (extendr l ls) = Znth i ls.
Proof.
  induction l; destruct ls; auto; simpl; intros.
  destruct (zlt i 0); [rewrite !Znth_underflow; auto|].
  rewrite Zlength_cons in *.
  destruct (eq_dec i 0); [rewrite Zlength_correct in *; omega|].
  rewrite !Znth_pos_cons; try omega.
  apply IHl; omega.
Qed.

Lemma list_join_eq : forall (b : list share) a c c'
  (Hc : sepalg_list.list_join a b c) (Hc' : sepalg_list.list_join a b c'), c = c'.
Proof.
  induction b; intros; inv Hc; inv Hc'; auto.
  assert (w0 = w1) by (eapply sepalg.join_eq; eauto).
  subst; eapply IHb; eauto.
Qed.

Lemma readable_share_list_join : forall sh shs sh', sepalg_list.list_join sh shs sh' ->
  readable_share sh \/ Exists readable_share shs -> readable_share sh'.
Proof.
  induction 1; intros [? | Hexists]; try inv Hexists; auto.
  - apply IHfold_rel; left; eapply readable_share_join; eauto.
  - apply IHfold_rel; left; eapply readable_share_join; eauto.
Qed.

Lemma sublist_0_cons' : forall {A} i j (x : A) l, i <= 0 -> j > i -> sublist i j (x :: l) =
  x :: sublist i (j - 1) l.
Proof.
  intros; unfold sublist.
  replace (Z.to_nat i) with O; simpl.
  assert (0 < j - i) as Hgt by omega.
  rewrite Z2Nat.inj_lt in Hgt; try omega.
  destruct (Z.to_nat (j - i)) eqn: Hj; [omega|].
  simpl; f_equal; f_equal.
  replace (j - 1 - i) with (j - i - 1) by omega.
  rewrite Z2Nat.inj_sub; simpl; omega.
  destruct (eq_dec i 0); subst; auto.
  rewrite Z2Nat_neg; auto; omega.
Qed.

Lemma sublist_combine : forall {A B} (l1 : list A) (l2 : list B) i j,
  sublist i j (combine l1 l2) = combine (sublist i j l1) (sublist i j l2).
Proof.
  induction l1; simpl; intros.
  - unfold sublist; rewrite !skipn_nil, !firstn_nil; auto.
  - destruct l2.
    + unfold sublist at 1 3; rewrite !skipn_nil, !firstn_nil.
      destruct (sublist i j (a :: l1)); auto.
    + destruct (Z_le_dec j i); [rewrite !sublist_nil_gen; auto|].
      destruct (Z_le_dec i 0).
      * subst; rewrite !sublist_0_cons'; try omega.
        simpl; rewrite IHl1; auto.
      * rewrite !sublist_S_cons; try omega.
        apply IHl1; omega.
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
  - unfold sublist; rewrite skipn_nil, firstn_nil; auto.
  - destruct ls.
    + unfold sublist; rewrite skipn_nil, firstn_nil, extend_nil; auto.
    + destruct (Z_le_dec j i); [rewrite !sublist_nil_gen; auto|].
      destruct (Z_le_dec i 0).
      * subst; rewrite !sublist_0_cons'; try omega.
        rewrite IHl; auto.
      * rewrite !sublist_S_cons; auto; omega.
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
  - unfold sublist; rewrite skipn_nil, firstn_nil; auto.
  - destruct ls.
    + unfold sublist; rewrite skipn_nil, firstn_nil, extendr_nil; auto.
    + destruct (Z_le_dec j i); [rewrite !sublist_nil_gen; auto|].
      destruct (Z_le_dec i 0).
      * subst; rewrite !sublist_0_cons'; try omega.
        rewrite IHl; auto.
      * rewrite !sublist_S_cons; auto; omega.
Qed.

Lemma sublist_over : forall {A} (l : list A) i j, Zlength l <= i -> sublist i j l = [].
Proof.
  intros; unfold sublist.
  rewrite skipn_short, firstn_nil; auto.
  rewrite Zlength_correct in *; rep_omega.
Qed.

Lemma make_tycontext_s_distinct : forall a l (Ha : In a l) (Hdistinct : NoDup (map fst l)),
  (make_tycontext_s l) ! (fst a) = Some (snd a).
Proof.
  intros a l. unfold make_tycontext_s.
  change (@ptree_set) with (@PTree.set).
  induction l; simpl; intros. 
  contradiction.
  inv Hdistinct. destruct a0. simpl in *.
  destruct Ha. subst.
  simpl. rewrite PTree.gss. auto.
  rewrite PTree.gso.
  apply IHl; auto.
  intro; subst.
  apply H1; apply in_map. auto.
Qed.

Lemma lookup_distinct : forall {A B} (f : A -> B) a l t (Ha : In a l) (Hdistinct : NoDup (map fst l)),
  (fold_right (fun v : ident * A => PTree.set (fst v) (f (snd v))) t l) ! (fst a) =
  Some (f (snd a)).
Proof.
  induction l; simpl; intros; [contradiction|].
  inv Hdistinct.
  rewrite PTree.gsspec.
  destruct (peq (fst a) (fst a0)) eqn: Heq; setoid_rewrite Heq.
  - destruct Ha; [subst; auto|].
    contradiction H1; rewrite in_map_iff; eauto.
  - apply IHl; auto.
    destruct Ha; auto; subst.
    contradiction n; auto.
Qed.

Lemma lookup_out : forall {A B} (f : A -> B) a l t (Ha : ~In a (map fst l)),
  (fold_right (fun v : ident * A => PTree.set (fst v) (f (snd v))) t l) ! a = t ! a.
Proof.
  induction l; simpl; intros; auto.
  rewrite PTree.gsspec.
  destruct (peq a (fst a0)) eqn: Heq; setoid_rewrite Heq.
  - contradiction Ha; auto.
  - apply IHl.
    intro; contradiction Ha; auto.
Qed.

Lemma data_at__eq : forall {cs : compspecs} sh t p, data_at_ sh t p = data_at sh t (default_val t) p.
Proof.
  intros; unfold data_at_, data_at, field_at_; auto.
Qed.

Lemma func_tycontext_sub : forall f V G A V2 G2 (HV : incl V V2) (HG : incl G G2)
  (Hdistinct : NoDup (map fst V2 ++ map fst G2)),
  tycontext_sub (func_tycontext f V G A) (func_tycontext f V2 G2 A).
Proof.
  intros.
  unfold func_tycontext, make_tycontext, tycontext_sub; simpl.
  apply NoDup_app in Hdistinct; destruct Hdistinct as (? & ? & Hdistinct); auto.
  repeat split; auto; intro.
  - destruct (PTree.get _ _); auto.
  - unfold make_tycontext_g.
    revert dependent G2; revert dependent V2; revert V; induction G; simpl.
    + induction V; simpl; intros.
      * rewrite PTree.gempty; simpl; auto.
      * rewrite incl_cons_iff in HV; destruct HV.
        rewrite PTree.gsspec.
        destruct (peq id (fst a)); eauto; subst; simpl.
        rewrite lookup_out.
        apply lookup_distinct with (f0:=@id type); auto.
        { apply Hdistinct.
          rewrite in_map_iff; eexists; split; eauto. }
    + intros.
      rewrite incl_cons_iff in HG; destruct HG.
      rewrite PTree.gsspec.
      destruct (peq id (fst a)); eauto; subst; simpl.
      apply lookup_distinct; auto.
  - unfold make_tycontext_s.
    revert dependent G2; induction G; simpl; intros.
    + rewrite PTree.gempty; simpl; auto.
    + destruct a; simpl. hnf.
      change @ptree_set with @PTree.set in * at 1.
      rewrite incl_cons_iff in HG; destruct HG.
      rewrite PTree.gsspec.
      change (@PTree.set) with @ptree_set in IHG.
      fold make_tycontext_s in *.
      destruct (peq id i); eauto; subst; simpl.
      * exists f0; split; [ | apply funspec_sub_si_refl].
        apply make_tycontext_s_distinct with (a:=(i,f0)); auto.
      * apply IHG; auto.
  - apply Annotation_sub_refl.
Qed.

(* This lets us use a library as a client. *)
Lemma semax_body_mono : forall V G {cs : compspecs} f s V2 G2
  (HV : incl V V2) (HG : incl G G2) (Hdistinct : NoDup (map fst V2 ++ map fst G2)),
  semax_body V G f s -> semax_body V2 G2 f s.
Proof.
  unfold semax_body; intros.
  destruct s, f0.
  intros; eapply semax_Delta_subsumption, H.
  apply func_tycontext_sub; auto.
Qed.

(* We could also consider an alpha-renaming axiom, although this may be unnecessary. *)

(* exclusive *)
Lemma weak_exclusive_conflict : forall P,
  predicates_hered.derives ((weak_exclusive_mpred P && emp) * P * P) FF.
Proof.
  intros ?? (r1 & r2 & ? & (? & ? & Hj & [Hexclusive Hemp] & ?) & ?).
  destruct (age_sepalg.join_level _ _ _ H), (age_sepalg.join_level _ _ _ Hj).
  apply Hemp in Hj; subst.
  simpl in Hexclusive.
  match goal with H : exclusive_mpred ?P |- _ => change (predicates_hered.derives (P * P) FF) in H end.
  apply Hexclusive.
  do 3 eexists; eauto; repeat split; auto; omega.
Qed.

Lemma exclusive_sepcon1 : forall (P Q : mpred) (HP : exclusive_mpred P), exclusive_mpred (P * Q).
Proof.
  unfold exclusive_mpred; intros.
  eapply derives_trans, sepcon_FF_derives' with (P := Q * Q), HP; cancel.
Qed.

Lemma exclusive_sepcon2 : forall (P Q : mpred) (HP : exclusive_mpred Q), exclusive_mpred (P * Q).
Proof.
  intros; rewrite sepcon_comm; apply exclusive_sepcon1; auto.
Qed.

Lemma exclusive_andp1 : forall P Q (HP : exclusive_mpred P), exclusive_mpred (P && Q).
Proof.
  unfold exclusive_mpred; intros.
  eapply derives_trans, HP.
  apply sepcon_derives; apply andp_left1; auto.
Qed.

Lemma exclusive_andp2 : forall P Q (HQ : exclusive_mpred Q), exclusive_mpred (P && Q).
Proof.
  intros; rewrite andp_comm; apply exclusive_andp1; auto.
Qed.

Lemma lock_inv_exclusive : forall v sh R, exclusive_mpred (lock_inv sh v R).
Proof.
  intros; unfold exclusive_mpred, lock_inv.
  Transparent mpred. Intros b1 ofs1 b2 ofs2. Opaque mpred.
  subst.
  inv H0.
  match goal with |- ?P |-- ?Q => change (predicates_hered.derives P Q) end.
  intros ? (? & ? & ? & Hlock1 & Hlock2).
  exploit (res_predicates.LKspec_precise _ _ _ _ a _ _ Hlock1 Hlock2); try (eexists; eauto).
  intros; subst.
  destruct Hlock1 as [Hlock1 _]; simpl in Hlock1.
  specialize (Hlock1 (b2, Ptrofs.unsigned ofs2)).
  rewrite if_true in Hlock1 by (split; auto; pose proof lksize.LKSIZE_pos; omega).
  destruct Hlock1 as [? Hl1].
  apply compcert_rmaps.RML.resource_at_join with (loc := (b2, Ptrofs.unsigned ofs2)) in H.
  rewrite Hl1 in H; inv H.
  apply sepalg.join_self in RJ.
  eapply readable_not_identity; eauto.
Qed.

Lemma selflock_exclusive : forall R sh v, exclusive_mpred R -> exclusive_mpred (selflock R v sh).
Proof.
  intros.
  rewrite selflock_eq.
  apply exclusive_sepcon1; auto.
Qed.

Lemma exclusive_FF : exclusive_mpred FF.
Proof.
  unfold exclusive_mpred.
  rewrite FF_sepcon; auto.
Qed.

Lemma derives_exclusive : forall P Q (Hderives : P |-- Q) (HQ : exclusive_mpred Q),
  exclusive_mpred P.
Proof.
  unfold exclusive_mpred; intros.
  eapply derives_trans, HQ.
  apply sepcon_derives; auto.
Qed.

Lemma mapsto_exclusive : forall (sh : Share.t) (t : type) (v : val),
  sepalg.nonunit sh -> exclusive_mpred (EX v2 : _, mapsto sh t v v2).
Proof.
  intros; unfold exclusive_mpred.
  Intros v1 v2; apply mapsto_conflict; auto.
Qed.

Lemma field_at__exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) (p : val),
  sepalg.nonidentity sh ->
  0 < sizeof (nested_field_type t fld) -> exclusive_mpred (field_at_ sh t fld p).
Proof.
  intros; apply field_at__conflict; auto.
Qed.

Lemma ex_field_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) (p : val),
  sepalg.nonidentity sh ->
  0 < sizeof (nested_field_type t fld) -> exclusive_mpred (EX v : _, field_at sh t fld v p).
Proof.
  intros; unfold exclusive_mpred.
  Intros v v'; apply field_at_conflict; auto.
Qed.

Corollary field_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) v (p : val),
  sepalg.nonidentity sh -> 0 < sizeof (nested_field_type t fld) -> exclusive_mpred (field_at sh t fld v p).
Proof.
  intros; eapply derives_exclusive, ex_field_at_exclusive; eauto.
  Exists v; apply derives_refl.
Qed.

Lemma ex_data_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (EX v : _, data_at sh t v p).
Proof.
  intros; unfold exclusive_mpred.
  Intros v v'; apply data_at_conflict; auto.
Qed.

Corollary data_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) v (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (data_at sh t v p).
Proof.
  intros; eapply derives_exclusive, ex_data_at_exclusive; eauto.
  Exists v; apply derives_refl.
Qed.

Corollary data_at__exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (data_at_ sh t p).
Proof.
  intros; eapply derives_exclusive, data_at_exclusive; eauto.
  apply data_at__data_at; eauto.
Qed.

Lemma cond_var_exclusive : forall {cs} sh p, sepalg.nonidentity sh ->
  exclusive_mpred (@cond_var cs sh p).
Proof.
  intros; apply data_at__exclusive; auto.
  unfold tcond; simpl; omega.
Qed.

Lemma lock_inv_isptr : forall sh v R, lock_inv sh v R = !!isptr v && lock_inv sh v R.
Proof.
  intros.
  eapply local_facts_isptr with (P := fun v => lock_inv sh v R); eauto.
  Transparent mpred.
  unfold lock_inv; Intros b o.
  subst; simpl. apply prop_right; auto.
  Opaque mpred.
Qed.

Lemma cond_var_isptr : forall {cs} sh v, @cond_var cs sh v = !! isptr v && cond_var sh v.
Proof.
  intros; apply data_at__isptr.
Qed.
Hint Resolve lock_inv_isptr cond_var_isptr : saturate_local.

Lemma cond_var_share_join : forall {cs} sh1 sh2 sh v (Hjoin : sepalg.join sh1 sh2 sh),
  @cond_var cs sh1 v * cond_var sh2 v = cond_var sh v.
Proof.
  intros; unfold cond_var; apply data_at__share_join; auto.
Qed.

(* Sometimes, in order to prove precise, we actually need to know that the data is the same as well. *)
(* Do we still need this? Probably not.
Lemma mapsto_inj : forall sh t v1 v2 p r1 r2 r
  (Hsh : readable_share sh)
  (Hp1 : predicates_hered.app_pred (mapsto sh t p v1) r1)
  (Hp2 : predicates_hered.app_pred (mapsto sh t p v2) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hdef1 : v1 <> Vundef) (Hdef2 : v2 <> Vundef),
  r1 = r2 /\ v1 = v2.
Proof.
  unfold mapsto; intros.
  destruct (access_mode t); try contradiction.
  destruct (type_is_volatile t); [contradiction|].
  destruct p; try contradiction.
  destruct (readable_share_dec sh); [|contradiction n; auto].
  destruct Hp1 as [(? & ?) | (? & ?)]; [|contradiction Hdef1; auto].
  destruct Hp2 as [(? & ?) | (? & ?)]; [|contradiction Hdef2; auto].
  assert (r1 = r2); [|split; auto].
  - eapply ex_address_mapsto_precise; eauto; eexists; eauto.
  - subst; eapply res_predicates.address_mapsto_value_cohere'; eauto.
Qed.

Lemma data_at_int_array_inj : forall {cs} sh z a1 a2 p r1 r2 r
  (Hsh : readable_share sh)
  (Hp1 : predicates_hered.app_pred (@data_at_rec cs sh (tarray tint z) a1 p) r1)
  (Hp2 : predicates_hered.app_pred (@data_at_rec cs sh (tarray tint z) a2 p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hdef1 : Forall (fun v => v <> Vundef) a1) (Hdef2 : Forall (fun v => v <> Vundef) a2)
  (Hlen1 : Zlength a1 = z) (Hlen2 : Zlength a2 = z),
  r1 = r2 /\ a1 = a2.
Proof.
  intros until z.
  remember (Z.to_nat z) as l; revert dependent z.
  induction l; intros.
  - destruct a1; [|rewrite <- Hlen1, Zlength_cons, Zlength_correct, Z2Nat.inj_succ in Heql; omega].
    rewrite Zlength_nil in Hlen1.
    destruct a2; [split; auto | rewrite Zlength_cons, Zlength_correct in Hlen2; omega].
    rewrite <- Hlen1 in *.
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite array_pred_len_0 in Hp1, Hp2; auto.
    apply sepalg.same_identity with (a := r); auto.
    + destruct Hr1 as (? & H); specialize (Hp1 _ _ H); subst; auto.
    + destruct Hr2 as (? & H); specialize (Hp2 _ _ H); subst; auto.
  - destruct a1 as [|x1 l1].
    { rewrite <- Hlen1, Zlength_nil in Heql; discriminate. }
    destruct a2 as [|x2 l2].
    { rewrite <- Hlen2, Zlength_nil in Heql; discriminate. }
    unfold tarray in *.
    rewrite Zlength_cons in *.
    assert (0 <= 1 <= z).
    { rewrite Zlength_correct in *; omega. }
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite split_array_pred with (mid := 1) in Hp1; auto; [| rewrite Z.max_r by omega; auto | rewrite Z.max_r by omega; rewrite Zlength_cons; omega].
    rewrite split_array_pred with (mid := 1) in Hp2; auto; [| rewrite Z.max_r by omega; auto | rewrite Z.max_r by omega; rewrite Zlength_cons; omega].
    destruct Hp1 as (r1a & ? & ? & Hh1 & Ht1), Hp2 as (r2a & ? & ? & Hh2 & Ht2).
    repeat rewrite Z.sub_0_r in *.
    rewrite sublist_one, array_pred_len_1 in Hh1, Hh2; auto; try rewrite Zlength_cons; try omega.
    rewrite sublist_1_cons in Ht1, Ht2.
    unfold Znth in *; simpl in *.
    unfold at_offset in Hh1, Hh2.
    assert (Zlength l1 = z - 1) by omega.
    assert (Zlength l2 = z - 1) by omega.
    rewrite sublist_same in Ht1, Ht2; try rewrite Z.max_r by omega; auto.
    inv Hdef1; inv Hdef2.
    exploit (IHl (Zlength l1)); try assumption.
    { subst.
      rewrite Z2Nat.inj_succ in *; omega. }
    { rewrite data_at_rec_eq; simpl.
      instantiate (2 := offset_val 4 p).
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l1).
      erewrite array_pred_shift; try simple apply Ht1;
      try rewrite !Z.max_r by omega; auto; try omega.
      intros; unfold at_offset.      
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { rewrite data_at_rec_eq; simpl.
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l2).
      erewrite array_pred_shift; try simple apply Ht2;
      try rewrite !Z.max_r by omega;
      auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { auto. }
    { auto. }
    { auto. }
    { omega. }
    intros (? & ?); subst.
    rewrite by_value_data_at_rec_nonvolatile in Hh1, Hh2; auto.
    exploit (mapsto_inj sh tint x1 x2); eauto.
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    intros (? & ?); subst.
    split; [eapply sepalg.join_eq|]; auto.
Qed.

Lemma data_at_ptr_array_inj : forall {cs} sh t z a1 a2 p r1 r2 r
  (Hsh : readable_share sh)
  (Hp1 : predicates_hered.app_pred (@data_at_rec cs sh (tarray (tptr t) z) a1 p) r1)
  (Hp2 : predicates_hered.app_pred (@data_at_rec cs sh (tarray (tptr t) z) a2 p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hdef1 : Forall (fun v => v <> Vundef) a1) (Hdef2 : Forall (fun v => v <> Vundef) a2)
  (Hlen1 : Zlength a1 = z) (Hlen2 : Zlength a2 = z),
  r1 = r2 /\ a1 = a2.
Proof.
  intros until z.
  remember (Z.to_nat z) as l; revert dependent z.
  induction l; intros.
  - destruct a1; [|rewrite <- Hlen1, Zlength_cons, Zlength_correct, Z2Nat.inj_succ in Heql; omega].
    rewrite Zlength_nil in Hlen1.
    destruct a2; [split; auto | rewrite Zlength_cons, Zlength_correct in Hlen2; omega].
    rewrite <- Hlen1 in *.
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite array_pred_len_0 in Hp1, Hp2; auto.
    apply sepalg.same_identity with (a := r); auto.
    + destruct Hr1 as (? & H); specialize (Hp1 _ _ H); subst; auto.
    + destruct Hr2 as (? & H); specialize (Hp2 _ _ H); subst; auto.
  - destruct a1 as [|x1 l1].
    { rewrite <- Hlen1, Zlength_nil in Heql; discriminate. }
    destruct a2 as [|x2 l2].
    { rewrite <- Hlen2, Zlength_nil in Heql; discriminate. }
    unfold tarray in *.
    rewrite Zlength_cons in *.
    assert (0 <= 1 <= z).
    { rewrite Zlength_correct in *; omega. }
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite split_array_pred with (mid := 1) in Hp1; auto; [| rewrite Z.max_r by omega; auto | rewrite Z.max_r by omega; rewrite Zlength_cons; omega].
    rewrite split_array_pred with (mid := 1) in Hp2; auto; [| rewrite Z.max_r by omega; auto | rewrite Z.max_r by omega; rewrite Zlength_cons; omega].
    destruct Hp1 as (r1a & ? & ? & Hh1 & Ht1), Hp2 as (r2a & ? & ? & Hh2 & Ht2).
    repeat rewrite Z.sub_0_r in *.
    rewrite sublist_one, array_pred_len_1 in Hh1, Hh2; auto; try rewrite Zlength_cons; try omega.
    rewrite sublist_1_cons in Ht1, Ht2.
    unfold Znth in *; simpl in *.
    unfold at_offset in Hh1, Hh2.
    assert (Zlength l1 = z - 1) by omega.
    assert (Zlength l2 = z - 1) by omega.
    rewrite sublist_same in Ht1, Ht2; try rewrite Z.max_r by omega; auto.
    inv Hdef1; inv Hdef2.
    exploit (IHl (Zlength l1)); try assumption.
    { subst.
      rewrite Z2Nat.inj_succ in *; omega. }
    { rewrite data_at_rec_eq; simpl.
      instantiate (2 := offset_val 4 p).
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l1).
      erewrite array_pred_shift; try simple apply Ht1;
      try rewrite !Z.max_r by omega; auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { rewrite data_at_rec_eq; simpl.
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l2).
      erewrite array_pred_shift; try simple apply Ht2;
      try rewrite !Z.max_r by omega; auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { auto. }
    { auto. }
    { auto. }
    { omega. }
    intros (? & ?); subst.
    rewrite by_value_data_at_rec_nonvolatile in Hh1, Hh2; auto.
    exploit (mapsto_inj sh (tptr t) x1 x2); eauto.
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    intros (? & ?); subst.
    split; [eapply sepalg.join_eq|]; auto.
Qed. *)

Hint Resolve lock_inv_exclusive selflock_exclusive cond_var_exclusive data_at_exclusive
  data_at__exclusive field_at_exclusive field_at__exclusive selflock_rec.

Lemma eq_dec_refl : forall {A B} {A_eq : EqDec A} (a : A) (b c : B), (if eq_dec a a then b else c) = b.
Proof.
  intros; destruct (eq_dec a a); [|contradiction n]; auto.
Qed.

(* shares *)
Lemma LKspec_readable lock_size :
  0 < lock_size ->
  forall R sh p, predicates_hered.derives (res_predicates.LKspec lock_size R sh p)
  (!!(readable_share sh)).
Proof.
  intros pos R sh p a [H _].
  specialize (H p); simpl in H.
  destruct (adr_range_dec p lock_size p).
  destruct (eq_dec p p); [|contradiction n; auto].
  destruct H; auto.
  { contradiction n; unfold adr_range.
    destruct p; split; auto.
    omega. }
Qed.

Lemma lock_inv_share_join : forall sh1 sh2 sh v R (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2)
  (Hjoin : sepalg.join sh1 sh2 sh),
  lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R.
Proof.
  intros; unfold lock_inv.
  rewrite exp_sepcon1; f_equal; extensionality b.
  rewrite exp_sepcon1; f_equal; extensionality o.
  destruct v; try solve [repeat rewrite prop_false_andp; try discriminate; rewrite FF_sepcon; auto].
  destruct (eq_dec b0 b); [|repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n; auto);
    rewrite FF_sepcon; auto].
  destruct (eq_dec i o); [subst | repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n; auto);
    rewrite FF_sepcon; auto].
  repeat rewrite prop_true_andp; auto.
  evar (P : mpred); replace (exp _) with P.
  - subst P; apply slice.LKspec_share_join; eauto.
  - subst P.
    erewrite exp_uncurry, exp_congr, <- exp_andp1, exp_prop, prop_true_andp; eauto.
    { instantiate (1 := fun x => Vptr b o = Vptr (fst x) (snd x)); exists (b, o); auto. }
    intros (?, ?); simpl.
    destruct (eq_dec b0 b); [subst |
      repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n); auto].
    destruct (eq_dec i o); [|repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n); auto].
    subst; repeat rewrite prop_true_andp; auto.
Qed.

Lemma comp_join_top : forall sh, sepalg.join sh (Share.comp sh) Tsh.
Proof.
  intro; pose proof (Share.comp1 sh).
  apply comp_parts_join with (L := sh)(R := Share.comp sh); auto;
    rewrite Share.glb_idem, Share.glb_top.
  - rewrite Share.comp2; auto.
  - rewrite Share.glb_commute, Share.comp2; auto.
Qed.

Lemma unreadable_bot : ~readable_share Share.bot.
Proof.
  unfold readable_share, nonempty_share, sepalg.nonidentity.
  rewrite Share.glb_bot; auto.
Qed.
Hint Resolve unreadable_bot.

Definition join_Bot := join_Bot.

Lemma join_Tsh : forall a b, sepalg.join Tsh a b -> b = Tsh /\ a = Share.bot.
Proof.
  intros ?? (? & ?).
  rewrite Share.glb_commute, Share.glb_top in H; subst; split; auto.
  apply Share.lub_bot.
Qed.

(* It's often useful to split Tsh in half. *)
Definition gsh1 := fst (slice.cleave Tsh).
Definition gsh2 := snd (slice.cleave Tsh).

Lemma readable_gsh1 : readable_share gsh1.
Proof.
  apply slice.cleave_readable1; auto.
Qed.

Lemma readable_gsh2 : readable_share gsh2.
Proof.
  apply slice.cleave_readable2; auto.
Qed.

Lemma gsh1_gsh2_join : sepalg.join gsh1 gsh2 Tsh.
Proof.
  apply slice.cleave_join; unfold gsh1, gsh2; destruct (slice.cleave Tsh); auto.
Qed.

Hint Resolve readable_gsh1 readable_gsh2 gsh1_gsh2_join.

Lemma gsh1_not_bot : gsh1 <> Share.bot.
Proof.
  intro X; contradiction unreadable_bot; rewrite <- X; auto.
Qed.

Lemma gsh2_not_bot : gsh2 <> Share.bot.
Proof.
  intro X; contradiction unreadable_bot; rewrite <- X; auto.
Qed.
Hint Resolve gsh1_not_bot gsh2_not_bot.

(*
Lemma data_at_Tsh_conflict : forall {cs : compspecs} sh t v v' p, sepalg.nonidentity sh -> 0 < sizeof t ->
  data_at Tsh t v p * data_at sh t v' p |-- FF.
Proof.
  intros.
  assert_PROP (field_compatible t [] p) by entailer!.
  pose proof (comp_join_top sh).
  erewrite <- data_at_share_join by eauto.
  rewrite sepcon_comm, <- sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives, derives_refl | rewrite FF_sepcon; auto].
  apply data_at_conflict; auto.
  split; auto.
  unfold field_compatible in *; tauto.
Qed.
*)

Lemma split_readable_share sh :
  readable_share sh ->
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 sh.
Proof.
  intros.
  pose proof (slice.cleave_readable1 _ H); pose proof (slice.cleave_readable2 _ H).
  destruct (slice.cleave sh) as (sh1, sh2) eqn: Hsplit.
  exists sh1, sh2; split; [|split]; auto.
  replace sh1 with (fst (slice.cleave sh)) by (rewrite Hsplit; auto).
  replace sh2 with (snd (slice.cleave sh)) by (rewrite Hsplit; auto).
  apply slice.cleave_join; auto.
Qed.

Lemma split_Ews :
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 Ews.
Proof.
  apply split_readable_share; auto.
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
  rewrite sublist_0_cons, sublist_S_cons, Zlength_cons; auto; try omega.
  simpl; f_equal; f_equal; f_equal; omega.
Qed.

Lemma Zlength_remove_Znth : forall {A} i (l : list A), 0 <= i < Zlength l ->
  Zlength (remove_Znth i l) = Zlength l - 1.
Proof.
  intros; unfold remove_Znth.
  rewrite Zlength_app, !Zlength_sublist; omega.
Qed.

Lemma remove_upd_Znth: forall {A} i l (a : A), 0 <= i < Zlength l ->
  remove_Znth i (upd_Znth i l a) = remove_Znth i l.
Proof.
  intros; unfold remove_Znth.
  rewrite upd_Znth_Zlength, sublist_upd_Znth_l, sublist_upd_Znth_r; auto; omega.
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
  rewrite !sublist_combine, combine_app' by (rewrite !Zlength_sublist; omega).
  rewrite Zlength_combine, Z.min_l by omega.
  congruence.
Qed.

Lemma iter_sepcon_Znth: forall {A} {d : Inhabitant A} f (l : list A) i, 0 <= i < Zlength l ->
  iter_sepcon f l = f (Znth i l) * iter_sepcon f (remove_Znth i l).
Proof.
  intros; unfold remove_Znth.
  rewrite <- sublist_same at 1 by auto.
  rewrite sublist_split with (mid := i) by omega.
  rewrite sublist_next with (i0 := i) by omega.
  rewrite !iter_sepcon_app; simpl; apply pred_ext; cancel.
Qed.

Lemma iter_sepcon2_Znth: forall {A B} {d1 : Inhabitant A} {d2 : Inhabitant B}
  f (l1 : list A) (l2 : list B) i, 0 <= i < Zlength l1 -> Zlength l1 = Zlength l2 ->
  iter_sepcon2 f l1 l2 =
  f (Znth i l1) (Znth i l2) * iter_sepcon2 f (remove_Znth i l1) (remove_Znth i l2).
Proof.
  intros; rewrite !iter_sepcon2_spec.
  apply pred_ext; Intros l; subst.
  - rewrite Zlength_map in *.
    rewrite !remove_Znth_map, !Znth_map, iter_sepcon_Znth with (i0 := i) by auto.
    unfold uncurry at 1.
    Exists (remove_Znth i l); entailer!.
  - Exists (combine l1 l2).
    rewrite combine_fst, combine_snd
      by (rewrite <- !ZtoNat_Zlength; apply Nat2Z.inj; rewrite !Z2Nat.id; omega).
    rewrite iter_sepcon_Znth with (i0 := i)(l0 := combine _ _)
      by (rewrite Zlength_combine, Z.min_l; omega).
    rewrite Znth_combine, remove_Znth_combine by auto.
    rewrite H1, H2, combine_eq; unfold uncurry; entailer!.
    apply derives_refl.
Qed.

Instance Inhabitant_share : Inhabitant share := Share.bot. (* TODO: remove this, it's already in sublist.v *) 
Instance Inhabitant_mpred : Inhabitant mpred := @FF mpred Nveric. (* TODO: remove this, it's already in sublist.v *) 

Lemma join_shares_nth : forall shs sh1 sh i, sepalg_list.list_join sh1 shs sh -> 0 <= i < Zlength shs ->
  exists sh', sepalg_list.list_join (Znth i shs) (remove_Znth i shs) sh' /\ sepalg.join sh1 sh' sh.
Proof.
  induction shs; simpl; intros.
  { rewrite Zlength_nil in *; omega. }
  inv H.
  destruct (eq_dec i 0).
  - subst; rewrite remove_Znth0, sublist_1_cons, Zlength_cons, sublist_same, Znth_0_cons; auto; try omega.
    eapply sepalg_list.list_join_assoc1; eauto.
  - rewrite Zlength_cons in *; exploit (IHshs w1 sh (i - 1)); auto; try omega.
    intros (sh2 & ? & ?).
    rewrite Znth_pos_cons, remove_Znth_cons; try omega.
    exploit (sepalg.join_sub_joins_trans(a := a)(b := sh2)(c := w1)); eauto.
    { eexists; eapply sepalg.join_comm; eauto. }
    intros (sh' & ?); exists sh'; split.
    + exploit (sepalg_list.list_join_assoc2(a := a)(b := Znth (i - 1) shs)
        (cl := remove_Znth (i - 1) shs)(e := sh')(f := sh2)); auto.
      intros (d & ? & ?).
      econstructor; eauto.
    + pose proof (sepalg.join_assoc(a := sh1)(b := a)(c := sh2)(d := w1)(e := sh)) as X.
      repeat match goal with X : ?a -> _, H : ?a |- _ => specialize (X H) end.
      destruct X as (f & Ha' & ?).
      assert (f = sh') by (eapply sepalg.join_eq; eauto).
      subst; auto.
Qed.

Lemma list_join_comm : forall (l1 l2 : list share) a b, sepalg_list.list_join a (l1 ++ l2) b ->
  sepalg_list.list_join a (l2 ++ l1) b.
Proof.
  induction l1; intros; [rewrite app_nil_r; auto|].
  inversion H as [|????? H1 H2]; subst.
  apply IHl1, sepalg_list.list_join_unapp in H2.
  destruct H2 as (c & Hl2 & Hl1).
  apply sepalg.join_comm in H1.
  destruct (sepalg_list.list_join_assoc1 H1 Hl2) as (? & ? & ?).
  eapply sepalg_list.list_join_app; eauto.
  econstructor; eauto.
Qed.

(* Split a share into an arbitrary number of subshares. *)
Lemma split_shares : forall n sh, readable_share sh ->
  exists sh1 shs, Zlength shs = Z.of_nat n /\ readable_share sh1 /\ Forall readable_share shs /\
                  sepalg_list.list_join sh1 shs sh.
Proof.
  induction n; intros.
  - exists sh, []; repeat split; auto.
    apply sepalg_list.fold_rel_nil.
  - destruct (split_readable_share _ H) as (sh1 & sh2 & H1 & ? & ?).
    destruct (IHn _ H1) as (sh1' & shs & ? & ? & ? & ?).
    exists sh1', (shs ++ [sh2]).
    rewrite Nat2Z.inj_succ, Zlength_app, Zlength_cons, Zlength_nil; split; [omega|].
    rewrite Forall_app; repeat split; auto.
    eapply sepalg_list.list_join_app; eauto.
    rewrite <- sepalg_list.list_join_1; auto.
Qed.

Lemma data_at_shares_join : forall {cs} sh t v p shs sh1 (Hsplit : sepalg_list.list_join sh1 shs sh),
  @data_at cs sh1 t v p * fold_right sepcon emp (map (fun sh => data_at sh t v p) shs) =
  data_at sh t v p.
Proof.
  induction shs; intros; simpl.
  - inv Hsplit.
    rewrite sepcon_emp; auto.
  - inv Hsplit.
    erewrite <- sepcon_assoc, data_at_share_join; eauto.
Qed.

(* These lemmas should probably be in veric. *)
Lemma exp_comm : forall {A B} P,
  (EX x : A, EX y : B, P x y) = EX y : B, EX x : A, P x y.
Proof.
  intros; apply seplog.pred_ext; Intros x y; Exists y x; auto.
Qed.

Lemma mapsto_value_eq: forall sh1 sh2 t p v1 v2, readable_share sh1 -> readable_share sh2 ->
  v1 <> Vundef -> v2 <> Vundef -> mapsto sh1 t p v1 * mapsto sh2 t p v2 |-- !!(v1 = v2).
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try solve [entailer!].
  destruct (type_is_volatile t); try solve [entailer!].
  destruct p; try solve [entailer!].
  destruct (readable_share_dec sh1); [|contradiction n; auto].
  destruct (readable_share_dec sh2); [|contradiction n; auto].

  Transparent mpred.
  rewrite !prop_false_andp with (P := v1 = Vundef), !orp_FF; auto; Intros.
  rewrite !prop_false_andp with (P := v2 = Vundef), !orp_FF; auto; Intros.
  Opaque mpred.
  apply res_predicates.address_mapsto_value_cohere.
Qed.

Lemma mapsto_value_cohere: forall sh1 sh2 t p v1 v2, readable_share sh1 ->
  mapsto sh1 t p v1 * mapsto sh2 t p v2 |-- mapsto sh1 t p v1 * mapsto sh2 t p v1.
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try simple apply derives_refl.
  destruct (type_is_volatile t); try simple apply derives_refl.
  destruct p; try simple apply derives_refl.
  destruct (readable_share_dec sh1); [|contradiction n; auto].
  destruct (eq_dec v1 Vundef).
  Transparent mpred.
  - subst; rewrite !prop_false_andp with (P := tc_val t Vundef), !FF_orp, prop_true_andp; auto;
      try apply tc_val_Vundef.
    cancel.
    rewrite prop_true_andp with (P := Vundef = Vundef); auto.
    if_tac.
    + apply orp_left; Intros; auto.
      Exists v2; auto.
    + normalize. apply andp_right; auto. apply prop_right; split; auto. hnf; intros. contradiction H3; auto.
  - rewrite !prop_false_andp with (P := v1 = Vundef), !orp_FF; auto; Intros.
    apply andp_right; [apply prop_right; auto|].
    if_tac.
    eapply derives_trans with (Q := _ * EX v2' : val,
      res_predicates.address_mapsto m v2' _ _);
      [apply sepcon_derives; [apply derives_refl|]|].
    + destruct (eq_dec v2 Vundef).
      * subst; rewrite prop_false_andp with (P := tc_val t Vundef), FF_orp;
          try apply tc_val_Vundef.
        rewrite prop_true_andp with (P := Vundef = Vundef); auto.  apply derives_refl.
      * rewrite prop_false_andp with (P := v2 = Vundef), orp_FF; auto; Intros.
        Exists v2; auto.
    + Intro v2'.
      assert_PROP (v1 = v2') by (apply res_predicates.address_mapsto_value_cohere).
      subst. apply sepcon_derives; auto. apply andp_right; auto.
      apply prop_right; auto.
    + apply sepcon_derives; auto.
      normalize. apply andp_right; auto.
      apply prop_right; split; auto.
      intro; auto. 
Opaque mpred.
Qed.

Lemma struct_pred_value_cohere : forall {cs : compspecs} m sh1 sh2 p t f off v1 v2
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2)
  (IH : Forall (fun it : ident * type => forall v1 v2 (p : val),
        readable_share sh1 -> readable_share sh2 ->
        data_at_rec sh1 (t it) v1 p * data_at_rec sh2 (t it) v2 p |--
        data_at_rec sh1 (t it) v1 p * data_at_rec sh2 (t it) v1 p) m),
  struct_pred m (fun (it : ident * type) v =>
    withspacer sh1 (f it + sizeof (t it)) (off it) (at_offset (data_at_rec sh1 (t it) v) (f it))) v1 p *
  struct_pred m (fun (it : ident * type) v =>
    withspacer sh2 (f it + sizeof (t it)) (off it) (at_offset (data_at_rec sh2 (t it) v) (f it))) v2 p |--
  struct_pred m (fun (it : ident * type) v =>
    withspacer sh1 (f it + sizeof (t it)) (off it) (at_offset (data_at_rec sh1 (t it) v) (f it))) v1 p *
  struct_pred m (fun (it : ident * type) v =>
    withspacer sh2 (f it + sizeof (t it)) (off it) (at_offset (data_at_rec sh2 (t it) v) (f it))) v1 p.
Proof.
  intros.
  revert v1 v2; induction m; auto; intros.
  apply derives_refl.
  destruct a; inv IH.
  destruct m.
  - unfold withspacer, at_offset; simpl.
    if_tac; auto.
    match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) |-- _ => apply derives_trans with (Q := (P1 * P2) * (Q1 * Q2));
      [cancel|] end.
    eapply derives_trans; [apply sepcon_derives, derives_refl|].
    { apply H1; auto. }
    cancel.
  - rewrite !struct_pred_cons2.
    match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) |-- _ => apply derives_trans with (Q := (P1 * P2) * (Q1 * Q2));
      [cancel|] end.
    match goal with |- _ |-- (?P1 * ?Q1) * (?P2 * ?Q2) => apply derives_trans with (Q := (P1 * P2) * (Q1 * Q2));
      [|cancel] end.
    apply sepcon_derives; [|auto].
    unfold withspacer, at_offset; simpl.
    if_tac; auto.
    match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) |-- _ => apply derives_trans with (Q := (P1 * P2) * (Q1 * Q2));
      [cancel|] end.
    eapply derives_trans; [apply sepcon_derives, derives_refl|].
    { apply H1; auto. }
    cancel.
Qed.

Lemma data_at_value_cohere : forall {cs : compspecs} sh1 sh2 t v1 v2 p, readable_share sh1 ->
  type_is_by_value t = true -> type_is_volatile t = false ->
  data_at sh1 t v1 p * data_at sh2 t v2 p |--
  data_at sh1 t v1 p * data_at sh2 t v1 p.
Proof.
  intros; unfold data_at, field_at, at_offset; Intros.
  apply andp_right; [apply prop_right; auto|].
  rewrite !by_value_data_at_rec_nonvolatile by auto.
  apply mapsto_value_cohere; auto.
Qed.

Lemma data_at_array_value_cohere : forall {cs : compspecs} sh1 sh2 t z a v1 v2 p, readable_share sh1 ->
  type_is_by_value t = true -> type_is_volatile t = false ->
  data_at sh1 (Tarray t z a) v1 p * data_at sh2 (Tarray t z a) v2 p |--
  data_at sh1 (Tarray t z a) v1 p * data_at sh2 (Tarray t z a) v1 p.
Proof.
  intros; unfold data_at, field_at, at_offset; Intros.
  apply andp_right; [apply prop_right; auto|].
  rewrite !data_at_rec_eq; simpl.
  unfold array_pred, aggregate_pred.array_pred; Intros.
  apply andp_right; [apply prop_right; auto|].
  rewrite Z.sub_0_r in *.
  erewrite aggregate_pred.rangespec_ext by (intros; rewrite Z.sub_0_r; apply f_equal; auto).
  setoid_rewrite aggregate_pred.rangespec_ext at 2; [|intros; rewrite Z.sub_0_r; apply f_equal; auto].
  setoid_rewrite aggregate_pred.rangespec_ext at 4; [|intros; rewrite Z.sub_0_r; apply f_equal; auto].
  clear H3 H4.
  rewrite Z2Nat_max0 in *.
  forget (offset_val 0 p) as p'; forget (Z.to_nat z) as n; forget 0 as lo; revert dependent lo; induction n; auto; simpl; intros.
 apply derives_refl.
  match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) |-- _ =>
    eapply derives_trans with (Q := (P1 * P2) * (Q1 * Q2)); [cancel|] end.
  eapply derives_trans; [apply sepcon_derives|].
  - unfold at_offset.
    rewrite 2by_value_data_at_rec_nonvolatile by auto.
    apply mapsto_value_cohere; auto.
  - apply IHn.
  - unfold at_offset; rewrite 2by_value_data_at_rec_nonvolatile by auto; cancel.
Qed.

(* This isn't true if the type contains any unions, since in fact the type of the data could be different.
Lemma data_at_rec_value_cohere : forall {cs : compspecs} sh1 sh2 t v1 v2 p,
  readable_share sh1 -> readable_share sh2 ->
  data_at_rec sh1 t v1 p * data_at_rec sh2 t v2 p |--
  data_at_rec sh1 t v1 p * data_at_rec sh2 t v1 p.
Proof.
  intros until t; type_induction.type_induction t; intros; rewrite !data_at_rec_eq; simpl; auto;
    try solve [destruct (type_is_volatile _); [cancel | apply mapsto_value_cohere; auto]].
  - unfold array_pred, aggregate_pred.array_pred.
    rewrite sepcon_andp_prop, !sepcon_andp_prop'.
    repeat (apply derives_extract_prop; intro); entailer'.
    rewrite Z.sub_0_r in *.
    set (lo := 0) at 1 3 5 7; clearbody lo.
    forget (Z.to_nat z) as n; revert lo; induction n; simpl; intro; [cancel|].
    rewrite !sepcon_assoc, <- (sepcon_assoc _ (at_offset _ _ _)), (sepcon_comm _ (at_offset _ _ _)).
    rewrite <- (sepcon_assoc _ (at_offset _ _ _)), (sepcon_comm _ (at_offset _ _ _)).
    rewrite !sepcon_assoc, <- !(sepcon_assoc (at_offset _ _ _) (at_offset _ _ _)).
    apply sepcon_derives; unfold at_offset; auto.
  - apply struct_pred_value_cohere; auto.
  - 
Qed.

Corollary field_at_value_cohere : forall {cs : compspecs} sh1 sh2 t gfs v1 v2 p, readable_share sh1 ->
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v2 p |--
  field_at sh1 t gfs v1 p * field_at sh2 t gfs v1 p.
Proof.
  intros; destruct (readable_share_dec sh2).
  - unfold field_at, at_offset; Intros; entailer'.
    apply data_at_rec_value_cohere; auto.
  - assert_PROP (value_fits (nested_field_type t gfs) v1 /\ value_fits (nested_field_type t gfs) v2)
      by entailer!.
    setoid_rewrite nonreadable_field_at_eq at 2; eauto; tauto.
Qed.

Corollary data_at_value_cohere : forall {cs : compspecs} sh1 sh2 t v1 v2 p, readable_share sh1 ->
  data_at sh1 t v1 p * data_at sh2 t v2 p |--
  data_at sh1 t v1 p * data_at sh2 t v1 p.
Proof.
  intros; apply field_at_value_cohere; auto.
Qed.

Corollary data_at__cohere : forall {cs : compspecs} sh1 sh2 t v p, readable_share sh1 ->
  data_at sh1 t v p * data_at_ sh2 t p =
  data_at sh1 t v p * data_at sh2 t v p.
Proof.
  intros; apply mpred_ext.
  - rewrite data_at__eq; apply data_at_value_cohere; auto.
  - entailer!.
Qed.

Lemma data_at__shares_join : forall {cs} sh t v p shs sh1 (Hsplit : sepalg_list.list_join sh1 shs sh)
  (Hreadable1 : readable_share sh1) (Hreadable : Forall readable_share shs),
  @data_at cs sh1 t v p * fold_right sepcon emp (map (fun sh => data_at_ sh t p) shs) |--
  data_at sh t v p.
Proof.
  induction shs; intros; simpl.
  - inv Hsplit.
    rewrite sepcon_emp; auto.
  - inv Hsplit.
    inv Hreadable.
    rewrite <- sepcon_assoc, data_at__cohere; auto.
    erewrite data_at_share_join; eauto.
    apply IHshs; auto.
    eapply readable_share_join; eauto.
Qed.*)

Lemma extract_nth_sepcon : forall l i, 0 <= i < Zlength l ->
  fold_right sepcon emp l = Znth i l * fold_right sepcon emp (upd_Znth i l emp).
Proof.
  intros.
  erewrite <- sublist_same with (al := l) at 1; auto.
  rewrite sublist_split with (mid := i); try omega.
  rewrite sublist_next with (i0 := i); try omega.
  rewrite sepcon_app; simpl.
  rewrite <- sepcon_assoc, (sepcon_comm _ (Znth i l)).
  unfold upd_Znth; rewrite sepcon_app, sepcon_assoc; simpl.
  rewrite emp_sepcon; auto.
Qed.

Lemma replace_nth_sepcon : forall P l i, P * fold_right sepcon emp (upd_Znth i l emp) =
  fold_right sepcon emp (upd_Znth i l P).
Proof.
  intros; unfold upd_Znth.
  rewrite !sepcon_app; simpl.
  rewrite emp_sepcon, <- !sepcon_assoc, (sepcon_comm P); auto.
Qed.

Lemma sepcon_derives_prop : forall P Q R, P |-- !!R -> P * Q |-- !!R.
Proof.
  intros; eapply derives_trans; [apply saturate_aux20 with (Q' := True); eauto|].
  - entailer!.
  - apply prop_left; intros (? & ?); apply prop_right; auto.
Qed.

Lemma sepcon_map : forall {A} P Q (l : list A), fold_right sepcon emp (map (fun x => P x * Q x) l) =
  fold_right sepcon emp (map P l) * fold_right sepcon emp (map Q l).
Proof.
  induction l; simpl.
  - rewrite sepcon_emp; auto.
  - rewrite !sepcon_assoc, <- (sepcon_assoc (fold_right _ _ _) (Q a)), (sepcon_comm (fold_right _ _ _) (Q _)).
    rewrite IHl; rewrite sepcon_assoc; auto.
Qed.

Lemma sepcon_list_derives : forall l1 l2 (Hlen : Zlength l1 = Zlength l2)
  (Heq : forall i, 0 <= i < Zlength l1 -> Znth i l1 |-- Znth i l2),
  fold_right sepcon emp l1 |-- fold_right sepcon emp l2.
Proof.
  induction l1; destruct l2; auto; simpl; intros; rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite Zlength_correct in *; omega).
  apply sepcon_derives.
  - specialize (Heq 0); rewrite !Znth_0_cons in Heq; apply Heq.
    rewrite Zlength_correct; omega.
  - apply IHl1; [omega|].
    intros; specialize (Heq (i + 1)); rewrite !Znth_pos_cons, !Z.add_simpl_r in Heq; try omega.
    apply Heq; omega.
Qed.

Lemma sepcon_rotate : forall lP m n, 0 <= n - m < Zlength lP ->
  fold_right sepcon emp lP = fold_right sepcon emp (rotate lP m n).
Proof.
  intros.
  unfold rotate.
  rewrite sepcon_app, sepcon_comm, <- sepcon_app, sublist_rejoin, sublist_same by omega; auto.
Qed.

(* wand lemmas *)
Lemma wand_eq : forall P Q R, P = Q * R -> P = Q * (Q -* P).
Proof.
  intros.
  apply seplog.pred_ext, modus_ponens_wand.
  subst; cancel.
  rewrite <- wand_sepcon_adjoint; auto.
  rewrite sepcon_comm; auto.
Qed.

Lemma wand_twice : forall P Q R, P -* Q -* R = P * Q -* R.
Proof.
  intros; apply seplog.pred_ext.
  - rewrite <- wand_sepcon_adjoint.
    rewrite <- sepcon_assoc, wand_sepcon_adjoint.
    rewrite sepcon_comm; apply modus_ponens_wand.
  - rewrite <- !wand_sepcon_adjoint.
    rewrite sepcon_assoc, sepcon_comm; apply modus_ponens_wand.
Qed.

Lemma sepcon_In : forall l P, In P l -> exists Q, fold_right sepcon emp l = P * Q.
Proof.
  induction l; [contradiction|].
  intros ? [|]; simpl; subst; eauto.
  destruct (IHl _ H) as [? ->].
  rewrite sepcon_comm, sepcon_assoc; eauto.
Qed.

Lemma extract_wand_sepcon : forall l P, In P l ->
  fold_right sepcon emp l = P * (P -* fold_right sepcon emp l).
Proof.
  intros.
  destruct (sepcon_In _ _ H).
  eapply wand_eq; eauto.
Qed.

Lemma wand_sepcon_map : forall {A} (R : A -> mpred) l P Q
  (HR : forall i, In i l -> R i = P i * Q i),
  fold_right sepcon emp (map R l) = fold_right sepcon emp (map P l) *
    (fold_right sepcon emp (map P l) -* fold_right sepcon emp (map R l)).
Proof.
  intros; eapply wand_eq.
  erewrite map_ext_in, sepcon_map; eauto.
  apply HR.
Qed.

Lemma wand_frame : forall P Q R, P -* Q |-- P * R -* Q * R.
Proof.
  intros.
  rewrite <- wand_sepcon_adjoint; cancel.
  rewrite sepcon_comm; apply modus_ponens_wand.
Qed.

Lemma semax_extract_later_prop'':
  forall {CS : compspecs} {Espec: OracleKind},
    forall (Delta : tycontext) (PP : Prop) P Q R c post P1 P2,
      P2 |-- !!PP ->
      (PP -> semax Delta (PROPx P (LOCALx Q (SEPx (P1 && |>P2 :: R)))) c post) ->
      semax Delta (PROPx P (LOCALx Q (SEPx (P1 && |>P2 :: R)))) c post.
Proof.
  intros.
  erewrite (add_andp P2) by eauto.
  apply semax_pre0 with (P' := |>!!PP && PROPx P (LOCALx Q (SEPx (P1 && |>P2 :: R)))).
  { go_lowerx.
    rewrite later_andp, <- andp_assoc, andp_comm, corable_andp_sepcon1; auto.
    apply corable_later; auto. }
  apply semax_extract_later_prop; auto.
Qed.

Lemma field_at_array_inbounds : forall {cs : compspecs} sh t z a i v p,
  field_at sh (Tarray t z a) [ArraySubsc i] v p |-- !!(0 <= i < z).
Proof.
  intros; entailer!.
  destruct H as (_ & _ & _ & _ & _ & ?); auto.
Qed.

Lemma valid_pointer_isptr : forall v, valid_pointer v |-- !!(is_pointer_or_null v).
Proof.
Transparent mpred.
Transparent predicates_hered.pred.
  destruct v; simpl; auto; try apply derives_refl.
  apply prop_right; auto.
Opaque mpred. Opaque predicates_hered.pred.
Qed.

Hint Resolve valid_pointer_isptr : saturate_local.

Lemma approx_imp : forall n P Q, compcert_rmaps.RML.R.approx n (predicates_hered.imp P Q) =
  compcert_rmaps.RML.R.approx n (predicates_hered.imp (compcert_rmaps.RML.R.approx n P)
    (compcert_rmaps.RML.R.approx n Q)).
Proof.
  intros; apply predicates_hered.pred_ext; intros ? (? & Himp); split; auto; intros ? Ha' HP.
  - destruct HP; split; auto.
  - apply Himp; auto; split; auto.
    pose proof (ageable.necR_level _ _ Ha'); omega.
Qed.

Definition super_non_expansive' {A} P := forall n ts x, compcert_rmaps.RML.R.approx n (P ts x) =
  compcert_rmaps.RML.R.approx n (P ts (functors.MixVariantFunctor.fmap (rmaps.dependent_type_functor_rec ts A)
        (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) x)).

Lemma approx_sepcon_list: forall n lP, lP <> [] ->
  compcert_rmaps.RML.R.approx n (fold_right sepcon emp lP) =
  fold_right sepcon emp (map (compcert_rmaps.RML.R.approx n) lP).
Proof.
  induction lP; [contradiction | intros].
  destruct lP; simpl in *.
  - simpl; rewrite !sepcon_emp; auto.
  - rewrite approx_sepcon, IHlP; auto; discriminate.
Qed.

Corollary approx_sepcon_list' : forall n lP P,
  compcert_rmaps.RML.R.approx n (fold_right sepcon emp lP)  * compcert_rmaps.RML.R.approx n P =
  fold_right sepcon emp (map (compcert_rmaps.RML.R.approx n) lP) * compcert_rmaps.RML.R.approx n P.
Proof.
  intros.
  rewrite <- !approx_sepcon, !(sepcon_comm (fold_right _ _ _)).
  setoid_rewrite approx_sepcon_list with (lP := _ :: _); auto; discriminate.
Qed.

Lemma approx_FF : forall n, compcert_rmaps.RML.R.approx n FF = FF.
Proof.
  intro; apply predicates_hered.pred_ext; intros ??; try contradiction.
  destruct H; contradiction.
Qed.

Lemma later_nonexpansive : nonexpansive (@later mpred _ _).
Proof.
  apply contractive_nonexpansive, later_contractive.
  intros ??; auto.
Qed.

Lemma eqp_refl : forall (G : Triv) P, G |-- P <=> P.
Proof.
  intros; rewrite andp_dup; apply subp_refl.
Qed.

Lemma eqp_sepcon : forall (G : Triv) (P P' Q Q' : mpred)
  (HP : G |-- P <=> P') (HQ : G |-- Q <=> Q'), G |-- P * Q <=> P' * Q'.
Proof.
  intros.
  rewrite fash_andp in HP, HQ |- *.
  apply andp_right; apply subp_sepcon; auto; intros ? Ha; destruct (HP _ Ha), (HQ _ Ha); auto.
Qed.

Lemma eqp_andp : forall (G : Triv) (P P' Q Q' : mpred)
  (HP : G |-- P <=> P') (HQ : G |-- Q <=> Q'), G |-- P && Q <=> P' && Q'.
Proof.
  intros.
  rewrite fash_andp in HP, HQ |- *.
  apply andp_right; apply subp_andp; auto; intros ? Ha; destruct (HP _ Ha), (HQ _ Ha); auto.
Qed.

Lemma eqp_exp : forall (A : Type) (NA : NatDed A) (IA : Indir A) (RecIndir : RecIndir A)
    (G : Triv) (B : Type) (X Y : B -> A),
  (forall x : B, G |-- X x <=> Y x) ->
  G |-- (EX x : _, X x) <=> (EX x : _, Y x).
Proof.
  intros.
  rewrite fash_andp; apply andp_right; apply subp_exp; intro x; specialize (H x); rewrite fash_andp in H;
    intros ? Ha; destruct (H _ Ha); auto.
Qed.

Lemma fold_right_sepcon_nonexpansive : forall lP1 lP2, Zlength lP1 = Zlength lP2 ->
  (ALL i : Z, Znth i lP1 <=> Znth i lP2) |--
  fold_right sepcon emp lP1 <=> fold_right sepcon emp lP2.
Proof.
  induction lP1; intros.
  - symmetry in H; apply Zlength_nil_inv in H; subst.
    apply eqp_refl.
  - destruct lP2; [apply Zlength_nil_inv in H; discriminate|].
    rewrite !Zlength_cons in H.
    simpl fold_right; apply eqp_sepcon.
    + apply allp_left with 0.
      rewrite !Znth_0_cons; auto.
    + eapply derives_trans, IHlP1; [|omega].
      apply allp_right; intro i.
      apply allp_left with (i + 1).
      destruct (zlt i 0).
      { rewrite !(Znth_underflow _ _ l); apply eqp_refl. }
      rewrite !Znth_pos_cons, Z.add_simpl_r by omega; auto.
Qed.

(* tactics *)
Lemma void_ret : ifvoid tvoid (` (PROP ( )  LOCAL ()  SEP ()) (make_args [] []))
  (EX v : val, ` (PROP ( )  LOCAL ()  SEP ()) (make_args [ret_temp] [v])) = emp.
Proof.
  extensionality; simpl.
  unfold liftx, lift, PROPx, LOCALx, SEPx; simpl; normalize.
Qed.

(*
Lemma malloc_compat : forall {cs : compspecs} sh t p,
  complete_legal_cosu_type t = true ->
  natural_aligned natural_alignment t = true ->
  malloc_token sh (sizeof t) p = !!field_compatible t [] p && malloc_token sh (sizeof t) p.
Proof.
  intros; rewrite andp_comm; apply add_andp; entailer!.
  apply malloc_compatible_field_compatible; auto.
Qed.
*)

Ltac lock_props := rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
  [repeat apply andp_right; auto; eapply derives_trans;
   try (apply exclusive_weak_exclusive || (apply rec_inv_weak_rec_inv; try apply selflock_rec)); auto |
   try timeout 20 cancel].

Ltac join_sub := repeat (eapply sepalg.join_sub_trans;
  [eexists; first [eassumption | simple eapply sepalg.join_comm; eassumption]|]); eassumption.

Ltac join_inj := repeat match goal with H1 : sepalg.join ?a ?b ?c, H2 : sepalg.join ?a ?b ?d |- _ =>
    pose proof (sepalg.join_eq H1 H2); clear H1 H2; subst; auto end.

Ltac fast_cancel := rewrite ?sepcon_emp, ?emp_sepcon; rewrite ?sepcon_assoc;
  repeat match goal with
    | |- ?P |-- ?P => apply derives_refl
    | |- ?P * _ |-- ?P * _ => apply sepcon_derives; [apply derives_refl|]
    | |- _ |-- ?P * _ => rewrite <- !sepcon_assoc, (sepcon_comm _ P), !sepcon_assoc end;
  try cancel_frame.

(*Ltac forward_malloc t n := forward_call (sizeof t); [simpl; try computable |
  Intros n; rewrite malloc_compat by (auto; reflexivity); Intros;
  rewrite memory_block_data_at_ by auto].
*)

Lemma semax_fun_id'' id f gv Espec {cs} Delta P Q R Post c :
  (var_types Delta) ! id = None ->
  (glob_specs Delta) ! id = Some f ->
  (glob_types Delta) ! id = Some (type_of_funspec f) ->
  snd (local2ptree Q) = Some gv ->
  @semax cs Espec Delta
    (PROPx P
      (LOCALx Q
      (SEPx ((func_ptr' f (gv id)) :: R)))) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros V G GS HGV SA.
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply SA; clear SA;
 intros; try apply ENTAIL_refl.
destruct (local2ptree Q) as [[[T1 T2] Res] GV] eqn:?H.
simpl in HGV; subst GV.
erewrite (local2ptree_soundness P) by eauto.
erewrite (local2ptree_soundness P) by eauto.
go_lowerx.
entailer.
  unfold func_ptr'.
  rewrite <- andp_left_corable by (apply corable_func_ptr).
  rewrite andp_comm; apply andp_derives; auto.
  erewrite <- gvars_eval_var; [apply derives_refl | eauto ..].
  pose proof LocalD_sound_gvars gv T1 T2 _ eq_refl.
  clear - H2 H3.
  revert H3.
  generalize (gvars gv).
  rewrite <- Forall_forall.
  induction (LocalD T1 T2 (Some gv)); [constructor |].
  simpl in H2.
  destruct H2; constructor; auto.
Qed.

Ltac get_global_function'' _f :=
eapply (semax_fun_id'' _f); try reflexivity.

(* revised start_function that mostly works for dependent specs *)
Ltac start_dep_function := 
  match goal with |- semax_body ?V ?G ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s;
    match goal with
    | s :=  (DECLARE _ WITH _ : globals
               PRE  [] main_pre _ nil _
               POST [ tint ] main_post _ nil _) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end;
 let DependedTypeList := fresh "DependedTypeList" in
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>
   match Pre with 
   | (fun x => match _ with (a,b) => _ end) => intros Espec DependedTypeList [a b] 
   | (fun i => _) => intros Espec DependedTypeList i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 simplify_func_tycontext;
 repeat match goal with 
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 process_stackframe_of;
 repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;
 repeat (apply semax_extract_PROP; 
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH 
                 | Share.t => intros ?SH 
                 | _ => intro
                 end
               | |- _ => intro
               end);
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
 abbreviate_semax.

(* Notations for dependent funspecs *)
Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2) =>
     match x with (x1,x2) => P%assert end)
  (fun (ts: list Type) (x: t1*t2) =>
     match x with (x1,x2) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3) =>
     match x with (x1,x2,x3) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3) =>
     match x with (x1,x2,x3) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4) =>
     match x with (x1,x2,x3,x4) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4) =>
     match x with (x1,x2,x3,x4) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5) =>
     match x with (x1,x2,x3,x4,x5) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5) =>
     match x with (x1,x2,x3,x4,x5) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6) =>
     match x with (x1,x2,x3,x4,x5,x6) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6) =>
     match x with (x1,x2,x3,x4,x5,x6) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7) =>
     match x with (x1,x2,x3,x4,x5,x6,x7) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7) =>
     match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             P at level 100, Q at level 100).

(* automation for dependent funspecs moved to call_lemmas and forward.v*)

Lemma PROP_into_SEP : forall P Q R, PROPx P (LOCALx Q (SEPx R)) =
  PROPx [] (LOCALx Q (SEPx (!!fold_right and True P && emp :: R))).
Proof.
  intros; unfold PROPx, LOCALx, SEPx; extensionality; simpl.
  rewrite <- andp_assoc, (andp_comm _ (fold_right_sepcon R)), <- andp_assoc.
  rewrite prop_true_andp by auto.
  rewrite andp_comm; f_equal.
  rewrite andp_comm.
  rewrite sepcon_andp_prop', emp_sepcon; auto.
Qed.

Ltac cancel_for_forward_spawn :=
  eapply symbolic_cancel_setup;
   [ construct_fold_right_sepcon
   | construct_fold_right_sepcon
   | fold_abnormal_mpred
   | cbv beta iota delta [before_symbol_cancel]; cancel_for_forward_call].

Ltac forward_spawn id arg wit :=
  match goal with gv : globals |- _ =>
  make_func_ptr id; let f := fresh "f_" in set (f := gv id);
  match goal with |- context[func_ptr' (NDmk_funspec _ _ (val * ?A) ?Pre _) f] =>
    let y := fresh "y" in let Q := fresh "Q" in let R := fresh "R" in
    evar (y : ident); evar (Q : A -> globals); evar (R : A -> val -> mpred);
    replace Pre with (fun '(a, w) => PROPx [] (LOCALx (temp y a :: gvars (Q w) :: nil) (SEPx [R w a])));
    [|let x := fresh "x" in extensionality x; destruct x as (?, x);
      instantiate (1 := fun w a => _ w) in (Value of R);
      repeat (destruct x as (x, ?);
        instantiate (1 := fun '(a, b) => _ a) in (Value of Q);
        instantiate (1 := fun '(a, b) => _ a) in (Value of R));
      etransitivity; [|symmetry; apply PROP_into_SEP]; f_equal; f_equal ; [instantiate (1 := fun _ => _) in (Value of Q); subst y Q; f_equal; simpl; f_equal |
       unfold SEPx; extensionality; simpl; rewrite sepcon_emp; instantiate (1 := fun _ => _); reflexivity]];
  forward_call [A] funspec_sub_refl (f, arg, Q, wit, R); subst Q R; [ .. | subst y f]; try (Exists y; subst y f; simpl; cancel_for_forward_spawn) end end.
