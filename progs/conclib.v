Require Export msl.predicates_sl.
Require Export concurrency.semax_conc_pred.
Require Export concurrency.xsemax_conc.
Require Export floyd.proofauto.
Require Import floyd.library.
Require Export floyd.sublist.

(* general list lemmas *)
Notation vint z := (Vint (Int.repr z)).

Definition complete MAX l := l ++ repeat (vint 0) (Z.to_nat MAX - length l).

Lemma upd_complete : forall l x MAX, Zlength l < MAX -> 
  upd_Znth (Zlength l) (complete MAX l) x = complete MAX (l ++ [x]).
Proof.
  intros; unfold complete.
  rewrite upd_Znth_app2, Zminus_diag.
  rewrite app_length; simpl plus.
  rewrite Zlength_correct, Z2Nat.inj_lt, Nat2Z.id in H; try omega.
  destruct (Z.to_nat MAX - length l)%nat eqn: Hminus; [omega|].
  replace (Z.to_nat MAX - (length l + 1))%nat with n by omega.
  unfold upd_Znth, sublist.sublist; simpl.
  rewrite Zlength_cons.
  unfold Z.succ; rewrite Z.add_simpl_r.
  rewrite Zlength_correct, Nat2Z.id, firstn_exact_length.
  rewrite <- app_assoc; auto.
  { repeat rewrite Zlength_correct; omega. }
Qed.

Lemma Znth_complete : forall n l d MAX, n < Zlength l -> Znth n (complete MAX l) d = Znth n l d.
Proof.
  intros; apply app_Znth1; auto.
Qed.

Lemma remove_complete : forall l x MAX, Zlength l < MAX -> 
  upd_Znth (Zlength l) (complete MAX (l ++ [x])) (vint 0) = complete MAX l.
Proof.
  intros; unfold complete.
  rewrite upd_Znth_app1; [|repeat rewrite Zlength_correct; rewrite app_length; simpl; Omega0].
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

Lemma Forall_app : forall A (P : A -> Prop) l1 l2,
  Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  induction l1; split; auto; intros.
  - destruct H; auto.
  - inversion H as [|??? H']; subst.
    rewrite IHl1 in H'; destruct H'; split; auto.
  - destruct H as (H & ?); inv H; constructor; auto.
    rewrite IHl1; split; auto.
Qed.

Lemma repeat_plus : forall A (x : A) i j, repeat x (i + j) = repeat x i ++ repeat x j.
Proof.
  induction i; auto; simpl; intro.
  rewrite IHi; auto.
Qed.

Definition remove_at {A} i (l : list A) := firstn i l ++ skipn (S i) l.

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

Lemma Forall_sublist : forall {A} (P : A -> Prop) l i j, Forall P l ->
  Forall P (sublist.sublist i j l).
Proof.
  intros; unfold sublist.sublist.
  apply Forall_firstn; apply Forall_skipn; auto.
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

Lemma Znth_last : forall {A} l (d : A), Znth (Zlength l - 1) l d = last l d.
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

Lemma sepcon_app : forall l1 l2, fold_right sepcon emp (l1 ++ l2) =
  fold_right sepcon emp l1 * fold_right sepcon emp l2.
Proof.
  induction l1; simpl; intros.
  - rewrite emp_sepcon; auto.
  - rewrite IHl1, sepcon_assoc; auto.
Qed.

Definition rotate {A} (l : list A) n m := sublist (m - n) (Zlength l) l ++
  sublist 0 (m - n) l.

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

Lemma upd_rotate : forall {A} i (l : list A) n m x (Hl : Zlength l = m) (Hlt : 0 <= n < m)
  (Hi : 0 <= i < Zlength l),
  upd_Znth i (rotate l n m) x = rotate (upd_Znth ((i - n) mod m) l x) n m.
Proof.
  intros; unfold upd_Znth, rotate.
  subst; autorewrite with sublist.
  exploit (Z_mod_lt (i - n) (Zlength l)); [omega|].
  intro; repeat rewrite Zlength_sublist; try omega.
  rewrite sublist_app; try omega.
  autorewrite with sublist.
  rewrite Z.min_l, sublist_sublist; try omega.
  rewrite sublist_sublist; try omega.
  rewrite sublist_app; try omega; repeat rewrite Zlength_sublist; try omega.
  autorewrite with sublist.
  rewrite (Z.min_r (n + _) n), sublist_sublist; try omega.
  rewrite (Z.max_l (Zlength l - _) 0); [|omega].
  rewrite sublist_app; try omega; try rewrite Zlength_cons; repeat rewrite Zlength_sublist; try omega.
  autorewrite with sublist.
  rewrite (Z.max_l (Z.succ _)); [|omega].
  rewrite sublist_app; try omega; try rewrite Zlength_cons; repeat rewrite Zlength_sublist; try omega.
  rewrite (Z.max_r (0 - _)); [|omega].
  assert (i < n /\ (i - n) mod Zlength l = Zlength l + i - n \/
          i >= n /\ (i - n) mod Zlength l = i - n) as Hcase.
  { destruct (Z_lt_dec i n); [left | right]; split; try omega.
    - rewrite Zmod_eq; [|omega].
      replace (_ / _) with (-1); try Omega0.
      replace (_ - _) with (- (n - i)); [|omega].
      rewrite Z_div_nz_opp_full, Zdiv_small; try omega.
      rewrite Zmod_small; omega.
    - apply Zmod_small; omega. }
  destruct Hcase as [(? & Heq) | (? & Heq)]; rewrite Heq; autorewrite with sublist.
  - rewrite Z.min_l, Z.min_l, Z.min_l, Z.min_r, Z.min_l; try omega.
    autorewrite with sublist.
    rewrite sublist_0_cons; [|omega].
    autorewrite with sublist.
    rewrite <- app_assoc; simpl; do 2 f_equal; try omega.
    do 2 f_equal; omega.
  - rewrite Z.min_r, Z.max_l, Z.min_r, Z.max_l, Z.min_r, Z.min_r, Z.max_l, Z.min_l; try omega.
    autorewrite with sublist.
    rewrite (sublist_nil (i - n)); simpl.
    rewrite sublist_0_cons; [simpl | omega].
    rewrite sublist_S_cons; [|omega].
    autorewrite with sublist.
    rewrite <- app_assoc; do 2 f_equal; try omega.
    f_equal.
    rewrite sublist_nil; simpl; f_equal; omega.
  - split; [rewrite Z.min_glb_iff | rewrite Z.min_le_iff]; omega.
  - split; [|rewrite Z.max_le_iff]; omega.
  - rewrite Z.max_lub_iff; omega.
  - split; [|rewrite Z.min_glb_iff]; omega.
  - rewrite Z.min_le_iff; omega.
  - repeat rewrite Zlength_sublist; omega.
Qed.

Lemma combine_app : forall {A B} (l1 l2 : list A) (l1' l2' : list B), length l1 = length l1' ->
  combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  induction l1; destruct l1'; intros; try discriminate; auto; simpl in *.
  rewrite IHl1; auto.
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

Lemma Forall_complete : forall P l m, Forall P l -> P (vint 0) ->
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
  rewrite app_length, repeat_length; rewrite Zlength_correct in H; Omega0.
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
  rewrite Zlength_app, Zlength_repeat; rewrite Zlength_correct in *; Omega0.
Qed.

Lemma combine_eq : forall {A B} (l : list (A * B)), combine (map fst l) (map snd l) = l.
Proof.
  induction l; auto; simpl.
  destruct a; rewrite IHl; auto.
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

Lemma Znth_head : forall reqs head m d, Zlength reqs <= m -> 0 <= head < m ->
  Zlength reqs > 0 ->
  Znth head (rotate (complete m reqs) head m) d = Znth 0 reqs d.
Proof.
  intros; unfold rotate.
  assert (Zlength (sublist (m - head) (Zlength (complete m reqs)) (complete m reqs)) = head) as Hlen.
  { rewrite Zlength_sublist; rewrite Zlength_complete; omega. }
  rewrite app_Znth2; rewrite Hlen; [|omega].
  rewrite Zminus_diag.
  rewrite Znth_sublist; try omega.
  rewrite Znth_complete; auto; omega.
Qed.

Lemma Znth_repeat : forall {A} (x : A) n i, Znth i (repeat x n) x = x.
Proof.
  induction n; simpl; intro.
  - apply Znth_nil.
  - destruct (Z_lt_dec i 0); [apply Znth_underflow; auto|].
    destruct (eq_dec i 0); [subst; apply Znth_0_cons | rewrite Znth_pos_cons; eauto; omega].
Qed.

Lemma rotate_1 : forall v l n m, 0 <= n < m -> Zlength l < m ->
  rotate (upd_Znth 0 (complete m (v :: l)) (vint 0)) n m =
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
    rewrite NPeano.Nat.add_sub_swap with (p := length l); [|rewrite Zlength_correct in *; Omega0].
    rewrite repeat_plus; simpl; do 3 f_equal; omega.
  - rewrite Zmod_small; [|omega].
    rewrite (sublist_split (m - (n + 1)) (Zlength (complete m l) - 1)); try rewrite Zlength_complete; try omega.
    rewrite <- app_assoc, (sublist_one (m - 1)) with (d := vint 0); try rewrite Zlength_complete; try omega; simpl.
    assert (length l < Z.to_nat m)%nat by (rewrite Zlength_correct in *; Omega0).
    unfold complete.
    replace (Z.to_nat m - length l)%nat with (Z.to_nat m - S (length l) + 1)%nat; [|omega].
    rewrite repeat_plus, app_assoc; simpl.
    repeat rewrite Zlength_app.
    assert (m - 1 = Zlength l + Zlength (repeat (vint 0) (Z.to_nat m - S (Datatypes.length l)))) as Heq.
    { rewrite Zlength_repeat, Nat2Z.inj_sub, Z2Nat.id, Nat2Z.inj_succ, <- Zlength_correct; omega. }
    rewrite (sublist_app1 _ _ _ (_ ++ _)); try rewrite Zlength_app; try omega.
    rewrite (sublist_app1 _ _ _ (_ ++ _)); try rewrite Zlength_app; try omega.
    f_equal; f_equal; try omega.
    + rewrite app_Znth2, Zlength_app, Heq, Zminus_diag, Znth_0_cons; auto.
      rewrite Zlength_app; omega.
    + f_equal; omega.
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

Lemma Znth_indep : forall {A} i (l : list A) d d', 0 <= i < Zlength l -> Znth i l d = Znth i l d'.
Proof.
  intros; unfold Znth.
  destruct (zlt i 0); [omega|].
  apply nth_indep.
  rewrite Zlength_correct in *; Omega0.
Qed.

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

Lemma skipn_cons : forall {A} n (l : list A) d, (length l > n)%nat ->
  skipn n l = Znth (Z.of_nat n) l d :: skipn (S n) l.
Proof.
  induction n; intros; simpl; destruct l; simpl in *; try omega; auto.
  { inversion H. }
  rewrite Nat2Z.inj_succ.
  rewrite Znth_pos_cons; [|omega].
  unfold Z.succ; rewrite Z.add_simpl_r.
  erewrite IHn; auto; omega.
Qed.

Lemma Znth_map' : forall {A B} i (f : A -> B) al b, Znth i (map f al) (f b) = f (Znth i al b).
Proof.
  unfold Znth; intros.
  destruct (zlt i 0); auto.
  apply map_nth.
Qed.

Lemma Znth_upto : forall m n, 0 <= n <= Z.of_nat m -> Znth n (upto m) (Z.of_nat m) = n.
Proof.
  induction m; simpl; intros.
  - rewrite Znth_nil; simpl in *; rewrite Nat2Z.inj_0 in *; omega.
  - destruct (eq_dec n 0).
    + subst; apply Znth_0_cons.
    + rewrite Nat2Z.inj_succ in *.
      erewrite Znth_pos_cons, Znth_map', IHm; try omega.
Qed.

Transparent Z.of_nat.

Lemma nth_Znth : forall {A} i l (d : A), nth i l d = Znth (Z.of_nat i) l d.
Proof.
  intros; unfold Znth.
  destruct (zlt (Z.of_nat i) 0); [omega|].
  rewrite Nat2Z.id; auto.
Qed.

Lemma Znth_combine : forall {A B} i l1 l2 (a : A) (b : B), Zlength l1 = Zlength l2 ->
  Znth i (combine l1 l2) (a, b) = (Znth i l1 a, Znth i l2 b).
Proof.
  intros; unfold Znth.
  destruct (zlt i 0); auto.
  apply combine_nth.
  rewrite !Zlength_correct in *; Omega0.
Qed.

Lemma combine_upd_Znth1 : forall {A B} (l1 : list A) (l2 : list B) i x d, 0 <= i < Zlength l1 ->
  Zlength l1 = Zlength l2 -> combine (upd_Znth i l1 x) l2 = upd_Znth i (combine l1 l2) (x, Znth i l2 d).
Proof.
  induction l1; simpl; intros; [rewrite Zlength_nil in *; omega|].
  destruct l2; [rewrite Zlength_nil in *; omega|].
  rewrite !Zlength_cons in *.
  destruct (eq_dec i 0).
  - subst; rewrite !upd_Znth0, !Zlength_cons, !sublist_1_cons, !sublist_same; try omega; simpl.
    rewrite Znth_0_cons; auto.
  - rewrite !upd_Znth_cons; try omega; simpl.
    erewrite IHl1; try omega.
    rewrite Znth_pos_cons; auto; omega.
Qed.

Lemma Zlength_combine : forall {A B} (l : list A) (l' : list B),
  Zlength (combine l l') = Z.min (Zlength l) (Zlength l').
Proof.
  intros; rewrite !Zlength_correct, combine_length, Nat2Z.inj_min; auto.
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

Lemma upd_Znth_triv : forall {A} i (l : list A) x d (Hi : 0 <= i < Zlength l),
  Znth i l d = x -> upd_Znth i l x = l.
Proof.
  intros; unfold upd_Znth.
  setoid_rewrite <- (firstn_skipn (Z.to_nat i) l) at 4.
  erewrite skipn_cons, Z2Nat.id, H; try omega; [|rewrite Zlength_correct in *; Omega0].
  unfold sublist.
  rewrite Z.sub_0_r, Z2Nat.inj_add, NPeano.Nat.add_1_r; try omega.
  setoid_rewrite firstn_same at 2; auto.
  rewrite Z2Nat.inj_sub, Zlength_correct, Nat2Z.id, Z2Nat.inj_add, skipn_length; simpl; omega.
Qed.

Lemma Znth_In : forall {A} i l (d : A), 0 <= i < Zlength l -> In (Znth i l d) l.
Proof.
  intros; unfold Znth.
  destruct (zlt i 0); [omega|].
  apply nth_In; rewrite Zlength_correct in *; Omega0.
Qed.

Lemma In_Znth : forall {A} l (x d : A), In x l ->
  exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros.
  destruct (In_nth _ _ d H) as (n & ? & ?).
  exists (Z.of_nat n); unfold Znth.
  split; [rewrite Zlength_correct; Omega0|].
  rewrite Nat2Z.id; destruct (zlt (Z.of_nat n) 0); auto; omega.
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

Lemma Forall2_Znth : forall {A B} (P : A -> B -> Prop) l1 l2 d1 d2 (Hall : Forall2 P l1 l2) i
  (Hi : 0 <= i < Zlength l1), P (Znth i l1 d1) (Znth i l2 d2).
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

Lemma sublist_nil_gen : forall {A} (l : list A) i j, j <= i -> sublist i j l = [].
Proof.
  intros; unfold sublist.
  replace (Z.to_nat (j - i)) with O; auto.
  destruct (eq_dec (j - i) 0); try Omega0.
  rewrite Z2Nat_neg; auto; omega.
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

Lemma sublist_next : forall {A} i j l (d : A), 0 <= i < j -> j <= Zlength l ->
  sublist i j l = Znth i l d :: sublist (i + 1) j l.
Proof.
  intros.
  rewrite Znth_cons_sublist; [|omega].
  apply sublist_split; omega.
Qed.

Lemma data_at__eq : forall {cs : compspecs} sh t p, data_at_ sh t p = data_at sh t (default_val t) p.
Proof.
  intros; unfold data_at_, data_at, field_at_; auto.
Qed.

Lemma incl_cons_iff : forall A (a : A) b c, incl (a :: b) c <-> In a c /\ incl b c.
Proof.
  split; intro.
  - split; [|eapply incl_cons_inv; eauto].
    specialize (H a); apply H; simpl; auto.
  - destruct H; intros ? [? | ?]; subst; auto.
Qed.

Lemma lookup_distinct : forall A B (f : A -> B) a l t (Ha : In a l) (Hdistinct : NoDup (map fst l)),
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

Lemma lookup_out : forall A B (f : A -> B) a l t (Ha : ~In a (map fst l)),
  (fold_right (fun v : ident * A => PTree.set (fst v) (f (snd v))) t l) ! a = t ! a.
Proof.
  induction l; simpl; intros; auto.
  rewrite PTree.gsspec.
  destruct (peq a (fst a0)) eqn: Heq; setoid_rewrite Heq.
  - contradiction Ha; auto.
  - apply IHl.
    intro; contradiction Ha; auto.
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

Lemma func_tycontext_sub : forall f V G V2 G2 (HV : incl V V2) (HG : incl G G2)
  (Hdistinct : NoDup (map fst V2 ++ map fst G2)),
  tycontext_sub (func_tycontext f V G) (func_tycontext f V2 G2).
Proof.
  intros.
  unfold func_tycontext, make_tycontext, tycontext_sub; simpl.
  apply NoDup_app in Hdistinct; destruct Hdistinct as (? & ? & Hdistinct); auto.
  repeat split; auto; intro.
  - destruct (PTree.get _ _); auto.
    destruct p; rewrite orb_comm, orb_negb_r; auto.
  - unfold make_tycontext_g.
    revert dependent G2; revert dependent V2; revert V; induction G; simpl.
    + induction V; simpl; intros.
      * rewrite PTree.gempty; simpl; auto.
      * rewrite incl_cons_iff in HV; destruct HV.
        rewrite PTree.gsspec.
        destruct (peq id (fst a)); eauto; subst; simpl.
        rewrite lookup_out.
        apply lookup_distinct with (f := id); auto.
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
    + intros.
      rewrite incl_cons_iff in HG; destruct HG.
      rewrite PTree.gsspec.
      destruct (peq id (fst a)); eauto; subst; simpl.
      apply lookup_distinct with (f := id); auto.
Qed.

(* This lets us use a library as a client. *)
Lemma semax_body_mono : forall V G {cs : compspecs} f s V2 G2
  (HV : incl V V2) (HG : incl G G2) (Hdistinct : NoDup (map fst V2 ++ map fst G2)),
  semax_body V G f s -> semax_body V2 G2 f s.
Proof.
  unfold semax_body; intros.
  destruct s, f0.
  intros; eapply semax_extensionality_Delta, H.
  apply func_tycontext_sub; auto.
Qed.

(* We could also consider an alpha-renaming axiom, although this may be unnecessary. *)

(* precise and positive *)
Lemma precise_sepcon : forall (P Q : mpred) (HP : precise P) (HQ : precise Q), precise (P * Q).
Proof.
  unfold precise; intros ??????? (l1 & r1 & Hjoin1 & HP1 & HQ1) (l2 & r2 & Hjoin2 & HP2 & HQ2)
    Hsub1 Hsub2.
  specialize (HP w _ _ HP1 HP2); specialize (HQ w _ _ HQ1 HQ2).
  rewrite HP, HQ in Hjoin1.
  eapply sepalg.join_eq; eauto.
  - apply sepalg.join_sub_trans with (b := w1); auto.
    eapply sepalg.join_join_sub'; eauto.
  - apply sepalg.join_sub_trans with (b := w2); auto.
    eapply sepalg.join_join_sub'; eauto.
  - apply sepalg.join_sub_trans with (b := w1); auto.
    eapply sepalg.join_join_sub; eauto.
  - apply sepalg.join_sub_trans with (b := w2); auto.
    eapply sepalg.join_join_sub; eauto.
Qed.

Lemma precise_andp1 : forall P Q (HP : precise P), precise (P && Q).
Proof.
  intros ?????? (? & ?) (? & ?) ??; eauto.
Qed.

Lemma precise_andp2 : forall P Q (HQ : precise Q), precise (P && Q).
Proof.
  intros ?????? (? & ?) (? & ?) ??; eauto.
Qed.

Lemma ex_address_mapsto_precise: forall ch rsh sh l,
  precise (EX v : val, res_predicates.address_mapsto ch v rsh sh l).
Proof.
  intros.
  eapply derives_precise, res_predicates.VALspec_range_precise.
  repeat intro.
  destruct H.
  eapply res_predicates.address_mapsto_VALspec_range; eauto.
Qed.

Lemma lock_inv_precise : forall v sh R, precise (lock_inv sh v R).
Proof.
  intros ?????? (b1 & o1 & Hv1 & Hlock1) (b2 & o2 & Hv2 & Hlock2) ??.
  rewrite Hv2 in Hv1; inv Hv1.
  eapply res_predicates.LKspec_precise; eauto.
Qed.

Lemma lock_inv_positive : forall sh v R,
  positive_mpred (lock_inv sh v R).
Proof.
  repeat intro.
  destruct H as (b & o & Hv & Hlock).
  simpl in Hlock.
  specialize (Hlock (b, Int.unsigned o)).
  if_tac [r|nr] in Hlock.
  - if_tac [e|ne] in Hlock.
    + destruct Hlock; eauto 6.
    + contradiction ne; auto.
  - contradiction nr; unfold adr_range; split; auto.
    unfold lksize.LKSIZE in *.
    omega.
Qed.

Lemma selflock_precise : forall R sh v, precise R ->
  precise (selflock R v sh).
Proof.
  intros.
  rewrite selflock_eq.
  apply precise_sepcon; auto.
  apply lock_inv_precise.
Qed.

Lemma positive_sepcon1 : forall P Q (HP : positive_mpred P),
  positive_mpred (P * Q).
Proof.
  repeat intro.
  destruct H as (? & ? & ? & HP1 & ?).
  specialize (HP _ HP1).
  destruct HP as (l & sh & rsh & k & p & HP).
  apply compcert_rmaps.RML.resource_at_join with (loc := l) in H.
  rewrite HP in H; inversion H; eauto 6.
Qed.

Lemma positive_sepcon2 : forall P Q (HQ : positive_mpred Q),
  positive_mpred (P * Q).
Proof.
  repeat intro.
  destruct H as (? & ? & ? & ? & HQ1).
  specialize (HQ _ HQ1).
  destruct HQ as (l & sh & rsh & k & p & HQ).
  apply compcert_rmaps.RML.resource_at_join with (loc := l) in H.
  rewrite HQ in H; inversion H; eauto 6.
Qed.

Lemma positive_andp1 : forall P Q (HP : positive_mpred P),
  positive_mpred (P && Q).
Proof.
  intros ???? (? & ?); auto.
Qed.

Lemma positive_andp2 : forall P Q (HQ : positive_mpred Q),
  positive_mpred (P && Q).
Proof.
  intros ???? (? & ?); auto.
Qed.

Lemma selflock_positive : forall R sh v, positive_mpred R ->
  positive_mpred (selflock R v sh).
Proof.
  intros.
  rewrite selflock_eq.
  apply positive_sepcon1; auto.
Qed.

Lemma later_positive : forall P, positive_mpred P -> positive_mpred (|> P)%logic.
Proof.
(* !! I'm not sure this is true, but it seems plausible that a resource doesn't disappear in a later map. *)
Admitted.

Lemma positive_FF : positive_mpred FF.
Proof.
  repeat intro; contradiction.
Qed.

Lemma derives_positive : forall P Q (Hderives : P |-- Q) (HQ : positive_mpred Q), positive_mpred P.
Proof.
  repeat intro.
  specialize (Hderives _ H); auto.
Qed.

Lemma ex_address_mapsto_positive: forall ch rsh sh l,
  positive_mpred (EX v : val, res_predicates.address_mapsto ch v rsh sh l).
Proof.
  intros ????? (? & ? & ? & Hp); simpl in Hp.
  specialize (Hp l); destruct (adr_range_dec _ _ _).
  destruct Hp; eauto 6.
  { contradiction n; unfold adr_range.
    destruct l; repeat split; auto; try omega.
    destruct ch; simpl; omega. }
Qed.

Corollary mapsto_positive : forall sh t p v, readable_share sh -> positive_mpred (mapsto sh t p v).
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try apply positive_FF.
  destruct (type_is_volatile t); try apply positive_FF.
  destruct p; try apply positive_FF.
  destruct (readable_share_dec sh); [|contradiction n; auto].
  eapply derives_positive, ex_address_mapsto_positive.
  apply orp_left; entailer.
  - Exists v; eauto.
  - Exists v2'; auto.
Qed.

Corollary data_at__positive : forall {cs} sh t p (Hsh : readable_share sh)
  (Hval : type_is_by_value t = true) (Hvol : type_is_volatile t = false),
  positive_mpred (@data_at_ cs sh t p).
Proof.
  intros; unfold data_at_, field_at_, field_at, at_offset; rewrite by_value_data_at_rec_nonvolatile; auto;
    simpl.
  rewrite repinject_default_val.
  apply positive_andp2, mapsto_positive; auto.
Qed.

Corollary data_at_positive : forall {cs} sh t v p (Hsh : readable_share sh)
  (Hval : type_is_by_value t = true) (Hvol : type_is_volatile t = false),
  positive_mpred (@data_at cs sh t v p).
Proof.
  intros; eapply derives_positive, data_at__positive; eauto.
  apply data_at_data_at_.
Qed.

Lemma ex_positive : forall t P, (forall x, positive_mpred (P x)) -> positive_mpred (EX x : t, P x).
Proof.
  intros ???? (? & ?).
  eapply H; eauto.
Qed.

Lemma precise_emp : precise emp.
Proof.
  apply precise_emp.
Qed.

Lemma derives_precise' : forall (P Q : mpred), P |-- Q -> precise Q -> precise P.
Proof.
  intros; eapply derives_precise; [|eassumption]; auto.
Qed.

Lemma precise_FF : precise FF.
Proof.
  repeat intro; contradiction.
Qed.

Hint Resolve precise_emp precise_FF.

Lemma mapsto_precise : forall sh t p v, precise (mapsto sh t p v).
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); auto.
  destruct (type_is_volatile t); auto.
  destruct p; auto.
  destruct (readable_share_dec sh).
  - eapply derives_precise, ex_address_mapsto_precise; intros ? [(? & ?) | (? & ? & ?)]; eexists; eauto.
  - apply precise_andp2, res_predicates.nonlock_permission_bytes_precise.
Qed.
Hint Resolve mapsto_precise.

Corollary memory_block_precise : forall sh n v, precise (memory_block sh n v).
Proof.
  destruct v; auto; apply precise_andp2.
  forget (Int.unsigned i) as o; forget (nat_of_Z n) as z; revert o; induction z; intro; simpl.
  - apply precise_emp.
  - apply precise_sepcon; auto.
    apply mapsto_precise.
Qed.
Hint Resolve memory_block_precise.

Corollary field_at__precise : forall {cs : compspecs} sh t gfs p,
  precise (field_at_ sh t gfs p).
Proof.
  intros; rewrite field_at__memory_block; auto.
Qed.
Hint Resolve field_at__precise.

Corollary data_at__precise : forall {cs : compspecs} sh t p, precise (data_at_ sh t p).
Proof.
  intros; unfold data_at_; auto.
Qed.
Hint Resolve data_at__precise.

Corollary field_at_precise : forall {cs : compspecs} sh t gfs v p,
  precise (field_at sh t gfs v p).
Proof.
  intros; eapply derives_precise, field_at__precise; apply field_at_field_at_.
Qed.
Hint Resolve field_at_precise.

Corollary data_at_precise : forall {cs : compspecs} sh t v p, precise (data_at sh t v p).
Proof.
  intros; unfold data_at; auto.
Qed.
Hint Resolve data_at_precise.

Lemma cond_var_precise : forall {cs} sh p, readable_share sh ->
  precise (@cond_var cs sh p).
Proof.
  intros; apply data_at__precise; auto.
Qed.

Lemma cond_var_positive : forall {cs} sh p, readable_share sh ->
  positive_mpred (@cond_var cs sh p).
Proof.
  intros; unfold cond_var, data_at_, field_at_, field_at, at_offset; simpl.
  destruct p; try (rewrite prop_false_andp; [|intros (? & ?); contradiction]; apply positive_FF).
  apply positive_andp2.
  rewrite data_at_rec_eq; simpl.
  apply mapsto_positive; auto.
Qed.

Lemma lock_inv_isptr : forall sh v R, lock_inv sh v R = !!isptr v && lock_inv sh v R.
Proof.
  intros.
  eapply local_facts_isptr with (P := fun v => lock_inv sh v R); eauto.
  unfold lock_inv; Intros b o.
  subst; simpl; entailer.
Qed.

Lemma cond_var_isptr : forall {cs} sh v, @cond_var cs sh v = !! isptr v && cond_var sh v.
Proof.
  intros; apply data_at__isptr.
Qed.

Lemma cond_var_share_join : forall {cs} sh1 sh2 sh v (Hjoin : sepalg.join sh1 sh2 sh),
  @cond_var cs sh1 v * cond_var sh2 v = cond_var sh v.
Proof.
  intros; unfold cond_var; apply data_at__share_join; auto.
Qed.

Lemma precise_fold_right : forall l, Forall precise l -> precise (fold_right sepcon emp l).
Proof.
  induction l; simpl; auto; intros.
  inv H; apply precise_sepcon; auto.
Qed.

Lemma precise_False : precise (!!False).
Proof.
  repeat intro.
  inversion H.
Qed.

(* Sometimes, in order to prove precise, we actually need to know that the data is the same as well. *)
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
    rewrite split_array_pred with (mid := 1) in Hp1; auto; [|rewrite Zlength_cons; omega].
    rewrite split_array_pred with (mid := 1) in Hp2; auto; [|rewrite Zlength_cons; omega].
    destruct Hp1 as (r1a & ? & ? & Hh1 & Ht1), Hp2 as (r2a & ? & ? & Hh2 & Ht2).
    repeat rewrite Z.sub_0_r in *.
    rewrite sublist_one with (d := x1), array_pred_len_1 in Hh1, Hh2; auto; try rewrite Zlength_cons; try omega.
    rewrite sublist_1_cons in Ht1, Ht2.
    unfold Znth in *; simpl in *.
    unfold at_offset in Hh1, Hh2.
    assert (Zlength l1 = z - 1) by omega.
    assert (Zlength l2 = z - 1) by omega.
    rewrite sublist_same in Ht1, Ht2; auto.
    inv Hdef1; inv Hdef2.
    exploit (IHl (Zlength l1)); try assumption.
    { subst.
      rewrite Z2Nat.inj_succ in *; omega. }
    { rewrite data_at_rec_eq; simpl.
      instantiate (2 := offset_val 4 p).
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l1).
      erewrite array_pred_shift; try simple apply Ht1; auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { rewrite data_at_rec_eq; simpl.
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l2).
      erewrite array_pred_shift; try simple apply Ht2; auto; try omega.
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
    rewrite split_array_pred with (mid := 1) in Hp1; auto; [|rewrite Zlength_cons; omega].
    rewrite split_array_pred with (mid := 1) in Hp2; auto; [|rewrite Zlength_cons; omega].
    destruct Hp1 as (r1a & ? & ? & Hh1 & Ht1), Hp2 as (r2a & ? & ? & Hh2 & Ht2).
    repeat rewrite Z.sub_0_r in *.
    rewrite sublist_one with (d := x1), array_pred_len_1 in Hh1, Hh2; auto; try rewrite Zlength_cons; try omega.
    rewrite sublist_1_cons in Ht1, Ht2.
    unfold Znth in *; simpl in *.
    unfold at_offset in Hh1, Hh2.
    assert (Zlength l1 = z - 1) by omega.
    assert (Zlength l2 = z - 1) by omega.
    rewrite sublist_same in Ht1, Ht2; auto.
    inv Hdef1; inv Hdef2.
    exploit (IHl (Zlength l1)); try assumption.
    { subst.
      rewrite Z2Nat.inj_succ in *; omega. }
    { rewrite data_at_rec_eq; simpl.
      instantiate (2 := offset_val 4 p).
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l1).
      erewrite array_pred_shift; try simple apply Ht1; auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { rewrite data_at_rec_eq; simpl.
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l2).
      erewrite array_pred_shift; try simple apply Ht2; auto; try omega.
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
Qed.

Hint Resolve lock_inv_precise lock_inv_positive selflock_precise selflock_positive
  cond_var_precise cond_var_positive positive_FF mapsto_precise mapsto_positive
  data_at_precise data_at_positive data_at__precise data_at__positive selflock_rec.

(* shares *)
Lemma LKspec_nonunit lock_size :
  0 < lock_size ->
  forall R rsh sh p, predicates_hered.derives (res_predicates.LKspec lock_size R rsh sh p)
  (!!(sepalg.nonunit sh)).
Proof.
  intros pos R rsh sh p a H.
  specialize (H p); simpl in H.
  destruct (adr_range_dec p lock_size p).
  destruct (EqDec_address p p).
  destruct H; auto.
  { contradiction n; auto. }
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
  - subst P; apply res_predicates.LKspec_share_join; auto.
    + apply readable_share_unrel_Rsh; auto.
    + apply readable_share_unrel_Rsh; eauto.
    + apply Share.unrel_join; eauto.
    + apply Share.unrel_join; eauto.
  - subst P.
    erewrite exp_uncurry, exp_congr, <- exp_andp1, exp_prop, prop_true_andp; eauto.
    { instantiate (1 := fun x => Vptr b o = Vptr (fst x) (snd x)); exists (b, o); auto. }
    intros (?, ?); simpl.
    destruct (eq_dec b0 b); [subst |
      repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n); auto].
    destruct (eq_dec i o); [|repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n); auto].
    subst; repeat rewrite prop_true_andp; auto.
Qed.

Lemma split_readable_share sh :
  readable_share sh ->
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 sh.
Admitted.

Lemma split_Ews :
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 Ews.
Proof.
  apply split_readable_share; auto.
Qed.

(* Split a share into an arbitrary number of subshares. *)
Lemma split_shares : forall n sh, readable_share sh ->
  exists shs, Zlength shs = Z.of_nat n /\ forall i, 0 <= i < Z.of_nat n ->
  let '(a, b) := Znth i shs (sh, sh) in
    readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) shs (sh, sh))).
Proof.
  induction n; intros.
  - exists []; split; auto; intros; Omega0.
  - destruct (split_readable_share _ H) as (sh1 & sh2 & H1 & ? & ?).
    destruct (IHn _ H1) as (shs & ? & IH).
    exists (shs ++ [(sh1, sh2)]); split;
      [rewrite Zlength_app, Zlength_cons, Zlength_nil, Nat2Z.inj_succ; omega | intros].
    destruct (zlt i (Z.of_nat n)).
    + rewrite app_Znth1; [|omega].
      specialize (IH i).
      rewrite Znth_indep with (d' := (sh1, sh1)); [|omega].
      destruct (Znth i shs (sh1, sh1)).
      destruct (zlt (i + 1) (Zlength shs)).
      * rewrite app_Znth1; auto.
        erewrite Znth_indep; [apply IH|]; omega.
      * replace (i + 1) with (Zlength shs) in * by omega; rewrite app_Znth2, Zminus_diag; auto; simpl.
        rewrite Znth_overflow in IH; auto; apply IH; omega.
    + rewrite Nat2Z.inj_succ in *.
      assert (i = Zlength shs) by omega; subst.
      rewrite app_Znth2, Zminus_diag; auto; simpl; [|omega].
      rewrite Znth_overflow; auto.
      rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
Qed.

Lemma data_at_shares_join : forall {cs} sh t v p shs (Hsplit : forall i, 0 <= i < Zlength shs ->
  let '(a, b) := Znth i shs (sh, sh) in
  readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) shs (sh, sh)))),
  @data_at cs (fst (Znth 0 shs (sh, sh))) t v p *
  fold_right_sepcon (map (fun sh => data_at sh t v p) (map snd shs)) =
  data_at sh t v p.
Proof.
  induction shs; intros.
  - rewrite Znth_nil; simpl; normalize.
  - rewrite Znth_0_cons; simpl.
    rewrite Zlength_cons in Hsplit.
    erewrite <- sepcon_assoc, data_at_share_join.
    apply IHshs.
    + intros; specialize (Hsplit (i + 1)).
      rewrite !Znth_pos_cons, !Z.add_simpl_r in Hsplit; try omega.
      apply Hsplit; omega.
    + specialize (Hsplit 0).
      rewrite Znth_0_cons, Znth_pos_cons, Z.add_simpl_r in Hsplit; [|omega].
      destruct a; apply Hsplit; rewrite Zlength_correct; omega.
Qed.

(* These lemmas should probably be in veric. *)
Lemma mapsto_value_cohere: forall sh1 sh2 t p v1 v2,
  readable_share sh1 -> readable_share sh2 ->
  mapsto sh1 t p v1 * mapsto sh2 t p v2 |-- mapsto sh1 t p v1 * mapsto sh2 t p v1.
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try simple apply derives_refl.
  destruct (type_is_volatile t); try simple apply derives_refl.
  destruct p; try simple apply derives_refl.
  destruct (readable_share_dec sh1); [|contradiction n; auto].
  destruct (readable_share_dec sh2); [|contradiction n; auto].
  destruct (eq_dec v1 Vundef).
  - subst; rewrite !prop_false_andp with (P := tc_val t Vundef), !FF_orp, prop_true_andp; auto;
      try apply tc_val_Vundef.
    cancel.
    rewrite prop_true_andp with (P := Vundef = Vundef); auto.
    apply orp_left; Intros; auto.
    Exists v2; auto.
  - rewrite !prop_false_andp with (P := v1 = Vundef), !orp_FF; auto; Intros.
    apply andp_right; [apply prop_right; auto|].
    eapply derives_trans with (Q := _ * EX v2' : val,
      res_predicates.address_mapsto m v2' _ _ _);
      [apply sepcon_derives; [apply derives_refl|]|].
    + destruct (eq_dec v2 Vundef).
      * subst; rewrite prop_false_andp with (P := tc_val t Vundef), FF_orp;
          try apply tc_val_Vundef.
        rewrite prop_true_andp with (P := Vundef = Vundef); auto.
      * rewrite prop_false_andp with (P := v2 = Vundef), orp_FF; auto; Intros.
        Exists v2; auto.
    + Intro v2'.
      assert_PROP (v1 = v2') by (apply res_predicates.address_mapsto_value_cohere).
      subst; auto.
Qed.

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
  - admit.
  - admit.
Admitted.

Corollary data_at_value_cohere : forall {cs : compspecs} sh1 sh2 t v1 v2 p,
  readable_share sh1 -> readable_share sh2 ->
  data_at sh1 t v1 p * data_at sh2 t v2 p |--
  data_at sh1 t v1 p * data_at sh2 t v1 p.
Proof.
  intros; unfold data_at, field_at, at_offset; Intros; entailer'.
  apply data_at_rec_value_cohere; auto.
Qed.

Corollary data_at__cohere : forall {cs : compspecs} sh1 sh2 t v p,
  readable_share sh1 -> readable_share sh2 ->
  data_at sh1 t v p * data_at_ sh2 t p |--
  data_at sh1 t v p * data_at sh2 t v p. (* Could this be an equality? *)
Proof.
  intros; rewrite data_at__eq; apply data_at_value_cohere; auto.
Qed.

Lemma data_at__shares_join : forall {cs} sh t v p shs
  (Hsplit : forall i, 0 <= i < Zlength shs ->
    let '(a, b) := Znth i shs (sh, sh) in
    readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) shs (sh, sh)))),
  @data_at cs (fst (Znth 0 shs (sh, sh))) t v p *
  fold_right sepcon emp (map (fun sh => data_at_ sh t p) (map snd shs)) |--
  data_at sh t v p.
Proof.
  induction shs; intros.
  - rewrite Znth_nil; simpl; normalize.
  - rewrite Znth_0_cons; simpl.
    rewrite Zlength_cons in Hsplit.
    exploit (Hsplit 0); [rewrite Zlength_correct; omega|].
    rewrite Znth_0_cons, Znth_pos_cons, Z.add_simpl_r; [|omega].
    destruct a; intros (? & ? & ?).
    rewrite <- sepcon_assoc; eapply derives_trans; [apply sepcon_derives;
      [apply data_at__cohere; auto | apply derives_refl]|].
    erewrite data_at_share_join; eauto.
    apply IHshs.
    intros; specialize (Hsplit (i + 1)).
    rewrite !Znth_pos_cons, !Z.add_simpl_r in Hsplit; try omega.
    apply Hsplit; omega.
Qed.

(* tactics *)
Lemma void_ret : ifvoid tvoid (` (PROP ( )  LOCAL ()  SEP ()) (make_args [] []))
  (EX v : val, ` (PROP ( )  LOCAL ()  SEP ()) (make_args [ret_temp] [v])) = emp.
Proof.
  extensionality; simpl.
  unfold liftx, lift, PROPx, LOCALx, SEPx; simpl; normalize.
Qed.

Lemma malloc_compat : forall {cs : compspecs} sh t p, legal_alignas_type t = true ->
  legal_cosu_type t = true ->
  complete_type cenv_cs t = true -> (alignof t | natural_alignment) ->
  malloc_token sh (sizeof t) p = !!field_compatible t [] p && malloc_token sh (sizeof t) p.
Proof.
  intros; rewrite andp_comm; apply add_andp; entailer!.
  apply malloc_compatible_field_compatible; auto.
Qed.

Ltac lock_props := rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
  [repeat apply andp_right; auto; eapply derives_trans;
   try (apply precise_weak_precise || apply positive_weak_positive || apply rec_inv_weak_rec_inv); auto |
   try timeout 20 cancel].

Ltac join_sub := repeat (eapply sepalg.join_sub_trans;
  [eexists; first [eassumption | simple eapply sepalg.join_comm; eassumption]|]); eassumption.

Ltac join_inj := repeat match goal with H1 : sepalg.join ?a ?b ?c, H2 : sepalg.join ?a ?b ?d |- _ =>
    pose proof (sepalg.join_eq H1 H2); clear H1 H2; subst; auto end.

Ltac forward_spawn sig wit := let Frame := fresh "Frame" in evar (Frame : list mpred);
  try match goal with |- semax _ _ (Scall _ _ _) _ => rewrite -> semax_seq_skip end;
  rewrite <- ?seq_assoc; eapply semax_seq';
  [match goal with |- semax _ (PROP () (LOCALx ?locals _)) _ _ => eapply semax_pre, semax_call_id0 with
      (argsig := [(_f, tptr voidstar_funtype); (xsemax_conc._args, tptr tvoid)])(P := [])
      (Q := locals)(R := Frame)(ts := [sig])
      (A := rmaps.ProdType (rmaps.ProdType (rmaps.ConstType (val * val)) (rmaps.DependentType 0))
            (rmaps.ArrowType (rmaps.DependentType 0) (rmaps.ArrowType (rmaps.ConstType val) rmaps.Mpred)))
      (x := wit); try reflexivity end |
   after_forward_call; unfold spawn_post; rewrite void_ret; subst Frame; normalize].

Lemma semax_fun_id'' id f Espec {cs} Delta P Q R Post c :
  (var_types Delta) ! id = None ->
  (glob_specs Delta) ! id = Some f ->
  (glob_types Delta) ! id = Some (type_of_funspec f) ->
  @semax cs Espec Delta
    (EX v : val, PROPx P
      (LOCALx (gvar id v :: Q)
      (SEPx ((func_ptr' f v) :: R)))) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros V G GS SA.
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply SA; [ clear SA |
  intros; simpl; unfold local, lift1; entailer! ].
go_lowerx.
apply exp_right with (eval_var id (type_of_funspec f) rho).
entailer.
apply andp_right.
- (* about gvar *)
  apply prop_right.
  unfold gvar_denote, eval_var, Map.get.
  destruct H as (_ & _ & DG & DS).
  destruct (DS id _ GS) as [-> | (t & E)]; [ | congruence].
  destruct (DG id _ GS) as (? & -> & ?); auto.
- (* about func_ptr/func_ptr' *)
  unfold func_ptr'.
  rewrite <- andp_left_corable, andp_comm; auto.
  apply corable_func_ptr.
Qed.

Ltac get_global_function'' _f :=
eapply (semax_fun_id'' _f); try reflexivity.
