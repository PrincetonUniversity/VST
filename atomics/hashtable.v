Require Import VST.progs.conclib.
Require Import VST.floyd.sublist.

Set Bullet Behavior "Strict Subproofs".

(* Maps are represented as partial association lists, with entries with key 0 considered to be empty. *)
Fixpoint index_of (m : list (Z * Z)) (k : Z) :=
  match m with
  | [] => None
  | (k1, v1) :: rest => if eq_dec k1 k then Some 0
                        else option_map Z.succ (index_of rest k)
  end.

Lemma index_of_spec : forall k m, match index_of m k with
  | Some i => 0 <= i < Zlength m /\ fst (Znth i m) = k /\ Forall (fun x => fst x <> k) (sublist 0 i m)
  | None => ~In k (map fst m) end.
Proof.
  induction m; simpl; auto; intros.
  destruct a.
  rewrite Zlength_cons.
  pose proof (Zlength_nonneg m).
  destruct (eq_dec z k).
  { split; [omega|].
    rewrite sublist_nil; auto. }
  destruct (index_of m k); simpl.
  - destruct IHm as (? & ? & ?); unfold Z.succ.
    rewrite Znth_cons_eq, Z.add_simpl_r.
    if_tac; [omega|].
    split; [omega|].
    split; auto.
    rewrite sublist_0_cons, Z.add_simpl_r by omega; constructor; auto.
  - tauto.
Qed.

(* Abstract properties of hashtables *)
Class hash_fun := { size : Z; hash : Z -> Z; size_pos : size > 0; hash_range : forall i, 0 <= hash i < size }.

Section Hashtable.

Context {hf : hash_fun}.
Hint Resolve size_pos hash_range.

Definition rebase {A} (m : list A) i := rotate m (Zlength m - i) (Zlength m).

Definition well_chained (m : list (Z * Z)) := forall k i, index_of (rebase m (hash k)) k = Some i ->
  Forall (fun x => fst x <> 0) (sublist 0 i (rebase m (hash k))).

Definition wf_map (m : list (Z * Z)) := NoDup (map fst m).

Definition indices i j := (map (fun x => (i + x) mod size) (upto (Z.to_nat ((j - i) mod size)))).

Fixpoint index_of' (m : list (Z * Z)) k :=
  match m with
  | [] => None
  | (k1, v1) :: rest => if eq_dec k1 0 then Some 0 else
                        if eq_dec k1 k then Some 0
                        else option_map Z.succ (index_of' rest k)
  end.

Definition lookup (m : list (Z * Z)) (k : Z) :=
  option_map (fun i => (i + hash k) mod size) (index_of' (rebase m (hash k)) k).

Definition set m k v := option_map (fun i => upd_Znth i m (k, v)) (lookup m k).

Definition get m k := match lookup m k with Some i => let '(k', v') := Znth i m in
  if eq_dec k' 0 then None else Some v' | None => None end.

Lemma rebase_0 : forall {A} {d : Inhabitant A} (m : list A) i, 0 <= i < Zlength m -> Znth 0 (rebase m i) = Znth i m.
Proof.
  intros; unfold rebase.
  destruct (eq_dec (Zlength m) 0).
  { apply Zlength_nil_inv in e; subst.
    rewrite rotate_nil, !Znth_nil; auto. }
  pose proof (Zlength_nonneg m).
  rewrite Znth_rotate; try omega.
  f_equal.
  rewrite <- Z.mod_add with (b := 1) by auto.
  replace (0 - (Zlength m - i) + 1 * Zlength m) with i by omega.
  apply Zmod_small; auto.
Qed.

Lemma index_of'_spec : forall k m, match index_of' m k with
  | Some i => 0 <= i < Zlength m /\ (fst (Znth i m) = k \/ fst (Znth i m) = 0) /\
              Forall (fun x => fst x <> 0 /\ fst x <> k) (sublist 0 i m)
  | None => ~In k (map fst m) /\ ~In 0 (map fst m)
  end.
Proof.
  induction m; simpl; auto; intros.
  destruct a.
  rewrite Zlength_cons.
  pose proof (Zlength_nonneg m).
  destruct (eq_dec z 0).
  { subst; split; [omega|].
    rewrite sublist_nil, Znth_cons_eq; split; auto. }
  destruct (eq_dec z k).
  { subst; split; [omega|].
    rewrite sublist_nil, Znth_cons_eq; split; auto. }
  destruct (index_of' m k); simpl.
  - destruct IHm as (? & ? & ?); unfold Z.succ; rewrite Znth_cons_eq, Z.add_simpl_r.
    split; [omega|].
    if_tac; [omega|].
    split; auto.
    rewrite sublist_0_cons, Z.add_simpl_r by omega; constructor; auto.
  - tauto.
Qed.

Lemma Znth_rebase : forall {A} {d : Inhabitant A} (m : list A) i j, 0 <= i < Zlength m -> 0 <= j < Zlength m ->
  Znth i (rebase m j) = Znth ((i + j) mod Zlength m) m.
Proof.
  intros; unfold rebase.
  destruct (eq_dec (Zlength m) 0); [omega|].
  rewrite Znth_rotate by omega; f_equal.
  rewrite Z.sub_sub_distr, <- Z.add_sub_swap.
  replace (i + j - Zlength m) with (i + j + (-1 * Zlength m)) by omega.
  rewrite Z.mod_add; auto.
Qed.

Corollary Znth_rebase' : forall {A} {d : Inhabitant A} (m : list A) i j, 0 <= i < Zlength m -> 0 <= j < Zlength m ->
  Znth ((i - j) mod Zlength m) (rebase m j) = Znth i m.
Proof.
  intros; rewrite Znth_rebase; auto.
  - rewrite Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small; auto.
  - apply Z_mod_lt; omega.
Qed.

Lemma index_of'_upd : forall m k v i (Hrange : 0 <= i < Zlength m)
  (Hi : fst (Znth i m) = k \/ fst (Znth i m) = 0),
  index_of' (upd_Znth i m (k, v)) k = index_of' m k.
Proof.
  intros.
  pose proof (index_of'_spec k m) as Hk; pose proof (index_of'_spec k (upd_Znth i m (k, v))) as Hk'.
  destruct (index_of' m k), (index_of' (upd_Znth i m (k, v)) k); auto.
  - rewrite upd_Znth_Zlength in Hk' by auto.
    destruct Hk as (? & Hk & ?).
    destruct Hk' as (? & Hz & Hall).
    destruct (zlt i z0).
    { rewrite sublist_upd_Znth_lr in Hall by omega.
      rewrite Forall_forall in Hall; specialize (Hall _ (upd_Znth_In _ _ _)); tauto. }
    rewrite sublist_upd_Znth_l in Hall by omega.
    f_equal; destruct (eq_dec i z0); [subst | rewrite upd_Znth_diff' in Hz by auto];
      eapply (Forall_sublist_first(A := Z * Z)); eauto; omega.
  - rewrite <- upd_Znth_map in Hk'; destruct Hk' as (Hk' & _); contradiction Hk'.
    apply upd_Znth_In.
  - destruct Hk as (Hk & Hz); destruct Hi; [contradiction Hk | contradiction Hz]; rewrite in_map_iff;
      do 2 eexists; eauto; apply Znth_In; auto.
Qed.

Lemma Zlength_rebase : forall {A} (m : list A) i, 0 <= i < Zlength m -> Zlength (rebase m i) = Zlength m.
Proof.
  intros; unfold rebase; rewrite Zlength_rotate; auto; omega.
Qed.

Lemma rebase_upd : forall {A} (m : list A) i j x, 0 <= i < Zlength m -> 0 <= j < Zlength m ->
  rebase (upd_Znth i m x) j = upd_Znth ((i - j) mod Zlength m) (rebase m j) x.
Proof.
  intros; unfold rebase.
  destruct (eq_dec (Zlength m) 0); [omega|].
  rewrite upd_rotate; auto; try omega.
  rewrite upd_Znth_Zlength by auto.
  f_equal; f_equal.
  rewrite Zminus_mod_idemp_l.
  replace (i - j - (Zlength m - j)) with (i + (-1 * Zlength m)) by omega.
  rewrite Z.mod_add, Zmod_small; auto.
  { apply Z_mod_lt; omega. }
Qed.

Corollary rebase_upd' : forall {A} (m : list A) i j x, 0 <= i < Zlength m -> 0 <= j < Zlength m ->
  rebase (upd_Znth ((i + j) mod Zlength m) m x) j = upd_Znth i (rebase m j) x.
Proof.
  intros; rewrite rebase_upd; auto.
  - rewrite Zminus_mod_idemp_l, Z.add_simpl_r, Zmod_small; auto.
  - apply Z_mod_lt; omega.
Qed.

Lemma lookup_set : forall m k v m', set m k v = Some m' -> Zlength m = size -> lookup m' k = lookup m k.
Proof.
  unfold set; intros.
  destruct (lookup m k) eqn: Hlookup; [inv H | discriminate].
  unfold lookup in *.
  pose proof (hash_range k).
  pose proof (index_of'_spec k (rebase m (hash k))) as Hspec.
  destruct (index_of' (rebase m (hash k)) k) eqn: Hindex; [|discriminate].
  simpl in Hlookup; inv Hlookup.
  rewrite Zlength_rebase in Hspec by omega; destruct Hspec as (? & Hz & ?).
  replace size with (Zlength m); rewrite rebase_upd' by (auto; omega).
  rewrite index_of'_upd, Hindex; auto.
  { rewrite Zlength_rebase; omega. }
Qed.

Lemma lookup_range : forall m k i, lookup m k = Some i -> Zlength m = size -> 0 <= i < Zlength m.
Proof.
  unfold lookup; intros.
  pose proof (index_of'_spec k (rebase m (hash k))) as Hspec.
  destruct (index_of' (rebase m (hash k)) k); [inv H | discriminate].
  replace (Zlength m) with size; apply Z_mod_lt; auto.
Qed.

Lemma index_of'_upd2 : forall m k i k' v' (Hrange : 0 <= i < Zlength m)
  (Hi : index_of' m k <> Some i) (Hdiff : k' <> k /\ k' <> 0),
  index_of' (upd_Znth i m (k', v')) k = index_of' m k.
Proof.
  intros.
  pose proof (index_of'_spec k m) as Hk; pose proof (index_of'_spec k (upd_Znth i m (k', v'))) as Hk'.
  destruct (index_of' m k), (index_of' (upd_Znth i m (k', v')) k); auto.
  - rewrite upd_Znth_Zlength in Hk' by auto.
    destruct Hk as (? & Hk & ?).
    destruct Hk' as (? & Hz & Hall).
    destruct (eq_dec z0 i).
    { subst; rewrite upd_Znth_same in Hz by auto; tauto. }
    rewrite upd_Znth_diff' in Hz by auto.
    f_equal; apply Z.le_antisymm.
    + eapply (Forall_sublist_le(A := Z * Z)); try eassumption; simpl; try omega.
      { rewrite upd_Znth_Zlength; auto; omega. }
      rewrite upd_Znth_diff' by auto.
      destruct Hk as [-> | ->]; tauto.
    + eapply (Forall_sublist_le(A := Z * Z)); try eassumption; omega.
  - destruct Hk as (? & Hk & ?).
    erewrite <- upd_Znth_diff' with (j := i) in Hk by auto.
    destruct Hk' as (Hk' & Hz'); destruct Hk; [contradiction Hk' | contradiction Hz'];
      rewrite in_map_iff; do 2 eexists; eauto; apply Znth_In; rewrite upd_Znth_Zlength; auto.
  - destruct Hk' as (Hrange' & Hz & ?).
    destruct (eq_dec z i).
    { subst; rewrite upd_Znth_same in Hz by auto; tauto. }
    rewrite upd_Znth_Zlength in Hrange' by auto.
    rewrite upd_Znth_diff' in Hz by auto.
    destruct Hk as (Hk' & Hz'); destruct Hz; [contradiction Hk' | contradiction Hz'];
      rewrite in_map_iff; do 2 eexists; eauto; apply Znth_In; auto.
Qed.

Lemma lookup_upd_same : forall m k i v', lookup m k = Some i -> Zlength m = size -> 0 <= i < Zlength m ->
  lookup (upd_Znth i m (k, v')) k = lookup m k.
Proof.
  unfold lookup; intros.
  pose proof (hash_range k).
  rewrite rebase_upd by (auto; omega).
  rewrite index_of'_upd; auto.
  - rewrite Zlength_rebase by omega.
    apply Z_mod_lt; omega.
  - pose proof (index_of'_spec k (rebase m (hash k))) as Hspec.
    destruct (index_of' (rebase m (hash k)) k); inv H.
    replace size with (Zlength m).
    rewrite Zminus_mod_idemp_l, Z.add_simpl_r.
    destruct Hspec as (Hz & ? & ?).
    rewrite Zlength_rebase in Hz by omega.
    rewrite Zmod_small; auto.
Qed.

Lemma lookup_upd_diff : forall m k i k' v', lookup m k <> Some i -> Zlength m = size -> 0 <= i < Zlength m ->
  k' <> k /\ k' <> 0 ->
  lookup (upd_Znth i m (k', v')) k = lookup m k.
Proof.
  unfold lookup; intros.
  pose proof (hash_range k).
  rewrite rebase_upd by (auto; omega).
  rewrite index_of'_upd2; auto.
  - rewrite Zlength_rebase by omega.
    apply Z_mod_lt; omega.
  - intro X; rewrite X in H; simpl in H.
    replace size with (Zlength m) in H.
    rewrite Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small in H by omega; contradiction H; auto.
Qed.

Lemma Zlength_set : forall m k v m', set m k v = Some m' -> Zlength m = size ->
  Zlength m' = size.
Proof.
  unfold set; intros.
  destruct (lookup m k) eqn: Hlookup; inv H.
  rewrite upd_Znth_Zlength; auto.
  eapply lookup_range; eauto.
Qed.

Lemma get_set_same : forall m k v m', set m k v = Some m' -> Zlength m = size -> k <> 0 ->
  get m' k = Some v.
Proof.
  intros.
  exploit lookup_set; eauto; intro Heq.
  unfold set, get in *.
  destruct (lookup m k) eqn: Hlookup; [inv H | discriminate].
  exploit (lookup_range _ _ _ Hlookup); auto; intro.
  rewrite Heq, upd_Znth_same by auto.
  if_tac; [absurd (k = 0)|]; auto.
Qed.

Lemma get_override : forall m k v m' v', set m k v = Some m' -> Zlength m = size -> set m' k v' = set m k v'.
Proof.
  intros; unfold set.
  exploit lookup_set; eauto; intros ->.
  unfold set in H.
  destruct (lookup m k) eqn: Hlookup; auto; inv H; simpl.
  exploit lookup_range; eauto; intro.
  rewrite upd_Znth_twice; auto.
Qed.

Lemma index_of_app : forall k m1 m2, index_of (m1 ++ m2) k =
  match index_of m1 k with Some i => Some i | None => option_map (Z.add (Zlength m1)) (index_of m2 k) end.
Proof.
  induction m1; simpl; intros.
  - destruct (index_of m2 k); auto.
  - destruct a.
    destruct (eq_dec z k); auto.
    rewrite IHm1; destruct (index_of m1 k); auto; simpl.
    destruct (index_of m2 k); auto; simpl.
    rewrite Zlength_cons; f_equal; omega.
Qed.

Lemma index_of_out : forall k m, Forall (fun x => fst x <> k) m -> index_of m k = None.
Proof.
  intros.
  pose proof (index_of_spec k m) as Hk.
  destruct (index_of m k); auto.
  destruct Hk as (? & ? & ?); eapply Forall_Znth in H; eauto.
  subst; contradiction H; eauto.
Qed.

Lemma index_of_sublist : forall m a b i k (HNoDup : NoDup (map fst m))
  (Hi : index_of (sublist a b m) k = Some i) (Ha : 0 <= a) (Hb : b <= Zlength m),
  index_of m k = Some (i + a).
Proof.
  intros.
  destruct (Z_le_dec b a); [rewrite sublist_nil_gen in Hi by auto; discriminate|].
  assert (m = sublist 0 a m ++ sublist a b m ++ sublist b (Zlength m) m) as Hm.
  { rewrite !sublist_rejoin, sublist_same; auto; omega. }
  rewrite Hm, index_of_app, index_of_out, index_of_app, Hi; simpl.
  rewrite Zlength_sublist by omega.
  f_equal; omega.
  { rewrite Hm, !map_app in HNoDup; apply NoDup_app in HNoDup.
    destruct HNoDup as (_ & _ & HNoDup).
    rewrite Forall_forall; intros ???.
    exploit (HNoDup k); try contradiction.
    * rewrite in_map_iff; eauto.
    * rewrite in_app; left.
      pose proof (index_of_spec k (sublist a b m)) as Hspec; rewrite Hi in Hspec.
      destruct Hspec as (? & ? & ?).
      rewrite in_map_iff; do 2 eexists; eauto.
      apply Znth_In; auto. }
Qed.

Lemma index_of_rotate : forall m n k, 0 <= n <= Zlength m -> NoDup (map fst m) ->
  index_of (rotate m n (Zlength m)) k = option_map (fun i => (i + n) mod Zlength m) (index_of m k).
Proof.
  intros.
  destruct (eq_dec (Zlength m) 0).
  { apply Zlength_nil_inv in e; subst.
    unfold rotate; rewrite !sublist_of_nil; auto. }
  unfold rotate; rewrite !index_of_app.
  destruct (index_of (sublist (Zlength m - n) (Zlength m) m) k) eqn: Hk2.
  - pose proof (index_of_spec k (sublist (Zlength m - n) (Zlength m) m)) as Hspec.
    rewrite Hk2 in Hspec; destruct Hspec as (Hrange & ?).
    apply index_of_sublist in Hk2; auto; try omega.
    rewrite Hk2; simpl.
    rewrite Zlength_sublist in Hrange by omega.
    replace (z + _ + _) with (z + Zlength m) by omega.
    rewrite Z.add_mod, Z_mod_same_full, Z.add_0_r, Zmod_mod by auto.
    rewrite Zmod_small; auto; omega.
  - replace (index_of m k) with
      (index_of (sublist 0 (Zlength m - n) m ++ sublist (Zlength m - n) (Zlength m) m) k)
      by (rewrite sublist_rejoin, sublist_same; auto; omega).
    rewrite index_of_app, Hk2.
    pose proof (index_of_spec k (sublist 0 (Zlength m - n) m)) as Hspec.
    destruct (index_of (sublist 0 (Zlength m - n) m) k); auto; simpl.
    rewrite Zlength_sublist in Hspec by omega.
    rewrite Zlength_sublist, Zmod_small by omega.
    f_equal; omega.
Qed.

Corollary index_of_rebase : forall m n k, 0 <= n <= Zlength m -> NoDup (map fst m) ->
  index_of (rebase m n) k = option_map (fun i => (i - n) mod Zlength m) (index_of m k).
Proof.
  intros; unfold rebase.
  destruct (eq_dec (Zlength m) 0).
  { apply Zlength_nil_inv in e; subst.
    rewrite rotate_nil; auto. }
  rewrite index_of_rotate by (auto; omega).
  destruct (index_of m k); auto; simpl.
  replace (z + (Zlength m - n)) with (z - n + (1 * Zlength m)) by omega.
  rewrite Z.mod_add; auto.
Qed.

Lemma index_of'_succeeds : forall k m i (Hi : 0 <= i < Zlength m)
  (Hnz : Forall (fun x => fst x <> 0 /\ fst x <> k) (sublist 0 i m))
  (Hk : fst (Znth i m) = k \/ fst (Znth i m) = 0), index_of' m k = Some i.
Proof.
  intros.
  pose proof (index_of'_spec k m).
  destruct (index_of' m k).
  - destruct H as (? & Hz & Hnz').
    f_equal; eapply (Forall_sublist_first(A := Z * Z)); eauto; omega.
  - destruct H as (Hk' & Hz'); destruct Hk; [contradiction Hk' | contradiction Hz'];
      rewrite in_map_iff; do 2 eexists; eauto; apply Znth_In; auto.
Qed.

Lemma lookup_spec : forall m k (Hwf : wf_map m) (Hchain : well_chained m) (Hlen : Zlength m = size)
  (Hnz : k <> 0) (Hin : In k (map fst m)), lookup m k = index_of m k.
Proof.
  intros.
  destruct (eq_dec (Zlength m) 0).
  { apply Zlength_nil_inv in e; subst; contradiction. }
  specialize (Hchain k).
  pose proof (hash_range k).
  assert (0 <= hash k <= Zlength m) by omega.
  rewrite index_of_rebase in Hchain by auto.
  unfold lookup.
  pose proof (index_of_spec k m) as Hspec; destruct (index_of m k) eqn: Hk; [|contradiction].
  specialize (Hchain _ eq_refl).
  destruct Hspec as (? & Hz & ?).
  assert (0 <= (z - hash k) mod Zlength m < Zlength m) by (apply Z_mod_lt; omega).
  assert (((z - hash k) mod Zlength m + hash k) mod Zlength m = z) as Hmod.
  { rewrite Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small; auto. }
  assert (fst (Znth ((z - hash k) mod Zlength m) (rebase m (hash k))) = k).
  { rewrite Znth_rebase, Hmod; auto; omega. }
  erewrite index_of'_succeeds; eauto; simpl.
  rewrite <- Hlen, Hmod; auto.
  + rewrite Zlength_rebase; auto; omega.
  + rewrite Forall_forall; intros ? Hin'.
    split; [rewrite Forall_forall in Hchain; apply Hchain; rewrite !Hlen in *; auto|].
    intro Heq; apply In_Znth in Hin' as (i & Hi & ?); subst x.
    rewrite Zlength_sublist in Hi; try omega.
    rewrite Znth_sublist, Znth_rebase, Z.add_0_r in Heq by omega.
    eapply NoDup_Znth_inj with (i0 := z)(j := (i + hash k) mod (Zlength m)) in Hwf.
    subst z.
    rewrite Zminus_mod_idemp_l, Z.add_simpl_r, Z.sub_0_r, Zmod_small in Hi; try omega.
    * destruct Hi; split; auto.
      etransitivity; eauto.
      apply Z_mod_lt; omega.
    * rewrite Zlength_map; auto.
    * rewrite Zlength_map; apply Z_mod_lt; omega.
    * rewrite !Znth_map; subst k; eauto.
      apply Z_mod_lt; omega.
    * rewrite Zlength_rebase; omega.
Qed.

End Hashtable.

Lemma sepcon_rebase : forall l m, 0 <= m <= Zlength l ->
  fold_right sepcon emp l = fold_right sepcon emp (rebase l m).
Proof.
  intros; unfold rebase, rotate.
  rewrite sepcon_app, subsub1, sepcon_comm, <- sepcon_app, sublist_rejoin, sublist_same by omega; auto.
Qed.

Lemma rebase_map : forall {A B} (f : A -> B) l m, rebase (map f l) m = map f (rebase l m).
Proof.
  intros; unfold rebase.
  rewrite Zlength_map; apply rotate_map.
Qed.
