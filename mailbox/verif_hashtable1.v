Require Import mailbox.verif_atomics.
Require Import progs.ghost.
Require Import progs.conclib.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.hashtable1.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition surely_malloc_spec :=
 DECLARE _surely_malloc
   WITH n:Z
   PRE [ _n OF tuint ]
       PROP (0 <= n <= Int.max_unsigned)
       LOCAL (temp _n (Vint (Int.repr n)))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (malloc_token Tsh n p * memory_block Tsh n p).

Definition integer_hash_spec :=
 DECLARE _integer_hash
  WITH i : Z
  PRE [ _i OF tint ]
   PROP () LOCAL (temp _i (vint i)) SEP ()
  POST [ tint ]
   PROP () LOCAL (temp ret_temp (vint (i * 654435761))) SEP ().
(* One might think it should just return an unknown number, but in fact it needs to follow a known hash
   function at the logic level to be useful. *)

Definition tentry := Tstruct _entry noattr.

Definition entry_hists entries hists := fold_right sepcon emp (map (fun i =>
  let '(hp, e) := (Znth i hists ([], []), Znth i entries Vundef) in
    ghost_hist (fst hp) (field_address tentry [StructField _key] e) *
    ghost_hist (snd hp) (field_address tentry [StructField _value] e)) (upto 32)).

(* Maps are represented as partial association lists, with entries with key 0 considered to be empty. *)
Fixpoint index_of (m : list (Z * Z)) (k : Z) :=
  match m with
  | [] => None
  | (k1, v1) :: rest => if eq_dec k1 k then Some 0
                        else option_map Z.succ (index_of rest k)
  end.

Lemma index_of_spec : forall k m, match index_of m k with
  | Some i => 0 <= i < Zlength m /\ fst (Znth i m (0, 0)) = k /\ Forall (fun x => fst x <> k) (sublist 0 i m)
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

(* Abstract properties of hashtables (of length 32) *)
Definition hash i := (i * 654435761) mod 32.

Definition rebase (m : list (Z * Z)) i := rotate m (Zlength m - i) (Zlength m).

Lemma rebase_0 : forall m i d, 0 <= i < Zlength m -> Znth 0 (rebase m i) d = Znth i m d.
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

Definition well_chained (m : list (Z * Z)) := forall k i, index_of (rebase m (hash k)) k = Some i ->
  Forall (fun x => fst x <> 0) (sublist 0 i (rebase m (hash k))).

Definition wf_map (m : list (Z * Z)) := NoDup (map fst m).

Definition indices i j := (map (fun x => (i + x) mod 32) (upto (Z.to_nat ((j - i) mod 32)))).

Fixpoint index_of' (m : list (Z * Z)) k :=
  match m with
  | [] => None
  | (k1, v1) :: rest => if eq_dec k1 0 then Some 0 else
                        if eq_dec k1 k then Some 0
                        else option_map Z.succ (index_of' rest k)
  end.

Lemma index_of'_spec : forall k m, match index_of' m k with
  | Some i => 0 <= i < Zlength m /\ (fst (Znth i m (0, 0)) = k \/ fst (Znth i m (0, 0)) = 0) /\
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

Lemma Znth_rebase : forall m i j d, 0 <= i < Zlength m -> 0 <= j < Zlength m ->
  Znth i (rebase m j) d = Znth ((i + j) mod Zlength m) m d.
Proof.
  intros; unfold rebase.
  destruct (eq_dec (Zlength m) 0); [omega|].
  rewrite Znth_rotate by omega; f_equal.
  rewrite Z.sub_sub_distr, <- Z.add_sub_swap.
  replace (i + j - Zlength m) with (i + j + (-1 * Zlength m)) by omega.
  rewrite Z.mod_add; auto.
Qed.

Corollary Znth_rebase' : forall m i j d, 0 <= i < Zlength m -> 0 <= j < Zlength m ->
  Znth ((i - j) mod Zlength m) (rebase m j) d = Znth i m d.
Proof.
  intros; rewrite Znth_rebase; auto.
  - rewrite Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small; auto.
  - apply Z_mod_lt; omega.
Qed.

Definition lookup (m : list (Z * Z)) (k : Z) :=
  option_map (fun i => (i + hash k) mod 32) (index_of' (rebase m (hash k)) k).

Definition set m k v := option_map (fun i => upd_Znth i m (k, v)) (lookup m k).

Definition get m k := match lookup m k with Some i => let '(k', v') := Znth i m (0, 0) in
  if eq_dec k' 0 then None else Some v' | None => None end.

Lemma index_of'_upd : forall m k v i (Hrange : 0 <= i < Zlength m)
  (Hi : fst (Znth i m (0, 0)) = k \/ fst (Znth i m (0, 0)) = 0),
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
      eapply Forall_sublist_first; eauto; simpl; try omega.
    + destruct Hi as [-> | ->]; tauto.
    + destruct Hk as [-> | ->]; tauto.
    + destruct Hz as [-> | ->]; tauto.
    + destruct Hk as [-> | ->]; tauto.
  - rewrite <- upd_Znth_map in Hk'; destruct Hk' as (Hk' & _); contradiction Hk'.
    apply upd_Znth_In.
  - destruct Hk as (Hk & Hz); destruct Hi; [contradiction Hk | contradiction Hz]; rewrite in_map_iff;
      do 2 eexists; eauto; apply Znth_In; auto.
Qed.

Lemma hash_range : forall i, 0 <= hash i < 32.
Proof.
  intro; apply Z_mod_lt; computable.
Qed.

Lemma Zlength_rebase : forall m i, 0 <= i < Zlength m -> Zlength (rebase m i) = Zlength m.
Proof.
  intros; unfold rebase; rewrite Zlength_rotate; auto; omega.
Qed.

Lemma rebase_upd : forall m i j x, 0 <= i < Zlength m -> 0 <= j < Zlength m ->
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

Corollary rebase_upd' : forall m i j x, 0 <= i < Zlength m -> 0 <= j < Zlength m ->
  rebase (upd_Znth ((i + j) mod Zlength m) m x) j = upd_Znth i (rebase m j) x.
Proof.
  intros; rewrite rebase_upd; auto.
  - rewrite Zminus_mod_idemp_l, Z.add_simpl_r, Zmod_small; auto.
  - apply Z_mod_lt; omega.
Qed.

Lemma lookup_set : forall m k v m', set m k v = Some m' -> Zlength m = 32 -> lookup m' k = lookup m k.
Proof.
  unfold set; intros.
  destruct (lookup m k) eqn: Hlookup; [inv H | discriminate].
  unfold lookup in *.
  pose proof (hash_range k).
  pose proof (index_of'_spec k (rebase m (hash k))) as Hspec.
  destruct (index_of' (rebase m (hash k)) k) eqn: Hindex; [|discriminate].
  simpl in Hlookup; inv Hlookup.
  rewrite Zlength_rebase in Hspec by omega; destruct Hspec as (? & Hz & ?).
  replace 32 with (Zlength m); rewrite rebase_upd' by (auto; omega).
  rewrite index_of'_upd, Hindex; auto.
  { rewrite Zlength_rebase; omega. }
Qed.

Lemma lookup_range : forall m k i, lookup m k = Some i -> Zlength m = 32 -> 0 <= i < Zlength m.
Proof.
  unfold lookup; intros.
  pose proof (index_of'_spec k (rebase m (hash k))) as Hspec.
  destruct (index_of' (rebase m (hash k)) k); [inv H | discriminate].
  replace (Zlength m) with 32; apply Z_mod_lt; computable.
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
    + eapply Forall_sublist_le; try eassumption; simpl; try omega.
      { rewrite upd_Znth_Zlength; auto; omega. }
      rewrite upd_Znth_diff' by auto.
      destruct Hk as [-> | ->]; tauto.
    + eapply Forall_sublist_le; try eassumption; simpl; try omega.
      destruct Hz as [-> | ->]; tauto.
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

Lemma lookup_upd_diff : forall m k i k' v', lookup m k <> Some i -> Zlength m = 32 -> 0 <= i < Zlength m ->
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
    replace 32 with (Zlength m) in H.
    rewrite Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small in H by omega; contradiction H; auto.
Qed.

Lemma get_set_same : forall m k v m', set m k v = Some m' -> Zlength m = 32 -> k <> 0 ->
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

Lemma get_override : forall m k v m' v', set m k v = Some m' -> Zlength m = 32 -> set m' k v' = set m k v'.
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
  (Hk : fst (Znth i m (0, 0)) = k \/ fst (Znth i m (0, 0)) = 0), index_of' m k = Some i.
Proof.
  intros.
  pose proof (index_of'_spec k m).
  destruct (index_of' m k).
  - destruct H as (? & Hz & Hnz').
    f_equal; eapply Forall_sublist_first with (d := (0, 0)); eauto; omega.
  - destruct H as (Hk' & Hz'); destruct Hk; [contradiction Hk' | contradiction Hz'];
      rewrite in_map_iff; do 2 eexists; eauto; apply Znth_In; auto.
Qed.

Lemma lookup_spec : forall m k (Hwf : wf_map m) (Hchain : well_chained m) (Hlen : Zlength m = 32)
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
  assert (fst (Znth ((z - hash k) mod Zlength m) (rebase m (hash k)) (0, 0)) = k).
  { rewrite Znth_rebase, Hmod; auto; omega. }
  erewrite index_of'_succeeds; eauto; simpl.
  rewrite <- Hlen, Hmod; auto.
  + rewrite Zlength_rebase; auto; omega.
  + rewrite Forall_forall; intros ? Hin'.
    split; [rewrite Forall_forall in Hchain; apply Hchain; rewrite !Hlen in *; auto|].
    intro Heq; apply In_Znth with (d := (0, 0)) in Hin'.
    destruct Hin' as (i & Hi & ?); subst x.
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
    * rewrite !Znth_map'; subst k; eauto.
    * rewrite Zlength_rebase; omega.
Qed.

(* Some of these should probably go up to ghost, or at least atomics. *)
Definition value_of e :=
  match e with
  | Load v => v
  | Store v => v
  | CAS r c w => if eq_dec r c then w else r
  end.

Definition last_value (h : hist) v :=
  (* initial condition *)
  (h = [] /\ v = vint 0) \/
  exists n e, In (n, e) h /\ value_of e = v /\ Forall (fun x => let '(m, _) := x in m <= n)%nat h.

Definition newer (l : hist) t := Forall (fun x => fst x < t)%nat l.

Lemma last_value_new : forall h n e, newer h n ->
  last_value (h ++ [(n, e)]) (value_of e).
Proof.
  right.
  do 3 eexists; [rewrite in_app; simpl; eauto|].
  rewrite Forall_app; repeat constructor.
  eapply Forall_impl; [|eauto]; intros.
  destruct a; simpl in *; omega.
Qed.

Definition ordered_hist h := forall i j (Hi : 0 <= i < j) (Hj : j < Zlength h),
  (fst (Znth i h (O, Store (vint 0))) < fst (Znth j h (O, Store (vint 0))))%nat.

Lemma ordered_cons : forall t e h, ordered_hist ((t, e) :: h) ->
  Forall (fun x => let '(m, _) := x in t < m)%nat h /\ ordered_hist h.
Proof.
  unfold ordered_hist; split.
  - rewrite Forall_forall; intros (?, ?) Hin.
    apply In_Znth with (d := (O, Store (vint 0))) in Hin.
    destruct Hin as (j & ? & Hj).
    exploit (H 0 (j + 1)); try omega.
    { rewrite Zlength_cons; omega. }
    rewrite Znth_0_cons, Znth_pos_cons, Z.add_simpl_r, Hj by omega; auto.
  - intros; exploit (H (i + 1) (j + 1)); try omega.
    { rewrite Zlength_cons; omega. }
    rewrite !Znth_pos_cons, !Z.add_simpl_r by omega; auto.
Qed.

Lemma ordered_last : forall t e h (Hordered : ordered_hist h) (Hin : In (t, e) h)
  (Ht : Forall (fun x => let '(m, _) := x in m <= t)%nat h), last h (O, Store (vint 0)) = (t, e).
Proof.
  induction h; [contradiction | simpl; intros].
  destruct a; apply ordered_cons in Hordered; destruct Hordered as (Ha & ?).
  inversion Ht as [|??? Hp]; subst.
  destruct Hin as [Hin | Hin]; [inv Hin|].
  - destruct h; auto.
    inv Ha; inv Hp; destruct p; omega.
  - rewrite IHh; auto.
    destruct h; auto; contradiction.
Qed.

Definition value_of_hist (h : hist) := value_of (snd (last h (O, Store (vint 0)))).

Lemma ordered_last_value : forall h v (Hordered : ordered_hist h), last_value h v <-> value_of_hist h = v.
Proof.
  unfold last_value, value_of_hist; split; intro.
  - destruct H as [(? & ?) | (? & ? & ? & ? & ?)]; subst; auto.
    erewrite ordered_last; eauto; auto.
  - destruct h; [auto | right].
    destruct (last (p :: h) (O, Store (vint 0))) as (t, e) eqn: Hlast.
    exploit (@app_removelast_last _ (p :: h)); [discriminate | intro Heq].
    rewrite Hlast in Heq.
    exists t; exists e; repeat split; auto.
    + rewrite Heq, in_app; simpl; auto.
    + unfold ordered_hist in Hordered.
      rewrite Forall_forall; intros (?, ?) Hin.
      apply In_Znth with (d := (O, Store (vint 0))) in Hin.
      destruct Hin as (i & ? & Hi).
      rewrite <- Znth_last in Hlast.
      destruct (eq_dec i (Zlength (p :: h) - 1)).
      * subst; rewrite Hlast in Hi; inv Hi; auto.
      * exploit (Hordered i (Zlength (p :: h) - 1)); try omega.
        rewrite Hlast, Hi; simpl; omega.
Qed.

Lemma newer_trans : forall l t1 t2, newer l t1 -> (t1 <= t2)%nat -> newer l t2.
Proof.
  intros.
  eapply Forall_impl, H; simpl; intros; omega.
Qed.

Corollary newer_snoc : forall l t1 e t2, newer l t1 -> (t1 < t2)%nat -> newer (l ++ [(t1, e)]) t2.
Proof.
  unfold newer; intros.
  rewrite Forall_app; split; [|repeat constructor; auto].
  eapply newer_trans; eauto; omega.
Qed.

Lemma ordered_snoc : forall h t e, ordered_hist h -> newer h t -> ordered_hist (h ++ [(t, e)]).
Proof.
  repeat intro.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hj.
  rewrite app_Znth1 by omega.
  destruct (eq_dec j (Zlength h)).
  - rewrite Znth_app1; auto.
    apply Forall_Znth; auto; omega.
  - specialize (H i j).
    rewrite app_Znth1 by omega; apply H; auto; omega.
Qed.

Definition int_op e :=
  match e with
  | Load v | Store v => tc_val tint v
  | CAS r c w => tc_val tint r /\ tc_val tint c /\ tc_val tint w
  end.

(* Once set, a key is never reset. *)
Definition k_R (h : list hist_el) (v : val) := !!(Forall int_op h /\
  forall e, In e h -> value_of e <> vint 0 -> v = value_of e) && emp.

Definition v_R (h : list hist_el) (v : val) := emp.

Definition atomic_entry sh p := !!(field_compatible tentry [] p) && EX lkey : val, EX lval : val,
  field_at sh tentry [StructField _lkey] lkey p *
  atomic_loc sh lkey (field_address tentry [StructField _key] p) (vint 0) Tsh k_R *
  field_at sh tentry [StructField _lvalue] lval p *
  atomic_loc sh lval (field_address tentry [StructField _value] p) (vint 0) Tsh v_R.

(* Entries are no longer consecutive. *)
Definition wf_hists h := Forall (fun x => (ordered_hist (fst x) /\ Forall int_op (map snd (fst x))) /\
  (ordered_hist (snd x) /\ Forall int_op (map snd (snd x)))) h.

Definition make_int v := match v with Vint i => Int.signed i | _ => 0 end.

Lemma make_int_spec : forall v, tc_val tint v -> vint (make_int v) = v.
Proof.
  destruct v; try contradiction; simpl.
  rewrite Int.repr_signed; auto.
Qed.

Lemma make_int_repable : forall v, repable_signed (make_int v).
Proof.
  destruct v; simpl; try (split; computable).
  apply Int.signed_range.
Qed.

Definition make_map h :=
  map (fun hs => (make_int (value_of_hist (fst hs)), make_int (value_of_hist (snd hs)))) h.

Lemma make_map_eq : forall h h', Forall2 (fun a b => value_of_hist (fst a) = value_of_hist (fst b) /\
  value_of_hist (snd a) = value_of_hist (snd b)) h h' -> make_map h = make_map h'.
Proof.
  induction 1; auto; simpl.
  destruct x, y; simpl in *.
  destruct H as (-> & ->); rewrite IHForall2; auto.
Qed.

Lemma int_op_value : forall e, int_op e -> tc_val tint (value_of e).
Proof.
  destruct e; auto; simpl.
  intros (? & ? & ?); destruct (eq_dec r c); auto.
Qed.

Corollary int_op_value_of_hist : forall h, Forall int_op (map snd h) -> tc_val tint (value_of_hist h).
Proof.
  intros; unfold value_of_hist.
  apply Forall_last; simpl; auto.
  rewrite Forall_map in H; eapply Forall_impl; [|eauto].
  simpl; intros; apply int_op_value; auto.
Qed.

Lemma make_map_no_key : forall h k (Hout : Forall (fun x => make_int (value_of_hist (fst x)) <> k) h),
  Forall (fun x => fst x <> k) (make_map h).
Proof.
  induction h; simpl; auto; intros.
  destruct a.
  inv Hout.
  constructor; auto.
Qed.

Definition failed_CAS k (a b : hist * hist) := exists t r, newer (fst a) t /\
  (fst b = fst a ++ [(t, Load (Vint r))] \/
   exists t1, (t < t1)%nat /\ fst b = fst a ++ [(t, Load (vint 0)); (t1, CAS (Vint r) (vint 0) (vint k))]) /\
  r <> Int.zero /\ r <> Int.repr k /\ snd b = snd a /\
  (let v := value_of_hist (fst a) in v <> vint 0 -> v = Vint r).

Definition set_item_trace (h : list (hist * hist)) k v i h' := Zlength h' = Zlength h /\
  0 <= i < Zlength h /\
  (let '(hk, hv) := Znth i h ([], []) in exists t r tv, newer hk t /\ newer hv tv /\
     (fst (Znth i h' ([], [])) = hk ++ [(t, Load (vint k))] /\ r = vint k \/
      exists t1, (t < t1)%nat /\
        fst (Znth i h' ([], [])) = hk ++ [(t, Load (vint 0)); (t1, CAS r (vint 0) (vint k))] /\
        (r = vint 0 \/ r = vint k)) /\
     snd (Znth i h' ([], [])) = hv ++ [(tv, Store (vint v))] /\
     (let v := value_of_hist hk in v <> vint 0 -> v = r)) /\
  forall j, (In j (indices (hash k) i) -> failed_CAS k (Znth j h ([], [])) (Znth j h' ([], []))) /\
    (~In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], [])).

Definition map_incl (m m' : list (Z * Z)) := forall k v i, k <> 0 -> Znth i m (0, 0) = (k, v) ->
  Znth i m' (0, 0) = (k, v).

(* It would be nice if we could maintain the invariant that the map has no duplicates and is well-chained,
   and indeed, the algorithm should maintain these properties. However, the per-slot histories do not obviously
   present a way to prove this: if a new key has "mysteriously appeared" (i.e., been added by another thread),
   we don't have a good way of knowing that it's well-chained. *)
(* We can, however, allow for the possibility that there is garbage in the map, and consider the abstract map
   to be those elements that can be successfully looked up, rather than all pairs in the map. In practice, this
   *should* come down to the same thing, but how could we prove it? *)
Lemma set_item_trace_map : forall h k v i h' (Hwf : wf_hists h) (Hlenh : Zlength h = 32)
  (Htrace : set_item_trace h k v i h') (Hk : k <> 0) (Hrepk : repable_signed k) (Hrepv : repable_signed v),
  wf_hists h' /\ let m' := make_map (upd_Znth i h' (Znth i h ([], []))) in
    map_incl (make_map h) m' /\ set m' k v = Some (make_map h').
Proof.
  intros.
  destruct Htrace as (Hlen & Hbounds & Hi & Hrest).
  destruct (Znth i h ([], [])) as (hk, hv) eqn: Hhi.
  destruct Hi as (t & r & tv & Ht & Htv & Hi1 & Hi2 & Hr0).
  assert (i <= Zlength h') by (rewrite Hlen; destruct Hbounds; apply Z.lt_le_incl; auto).
  assert (0 <= i + 1 <= Zlength h').
  { rewrite Hlen; destruct Hbounds; split; [|rewrite <- lt_le_1]; auto; omega. }
  assert (vint k <> vint 0).
  { intro; contradiction Hk; apply repr_inj_signed; auto.
    { split; computable. }
    { congruence. }}
  assert (r = vint 0 \/ r = vint k) as Hr.
  { destruct Hi1 as [(? & ?) | (? & ? & ? & ?)]; auto. }
  assert ((if eq_dec r (vint 0) then vint k else r) = vint k) as Hif.
  { if_tac; auto.
    destruct Hr; [absurd (r = vint 0)|]; auto. }
  assert (value_of_hist (fst (Znth i h' ([], []))) = vint k) as Hk'.
  { destruct Hi1 as [(-> & ?) | (? & ? & -> & ?)].
    - unfold value_of_hist; rewrite last_snoc; auto.
    - rewrite app_cons_assoc; unfold value_of_hist; rewrite last_snoc; auto. }
  assert (wf_hists h') as Hwf'; [|split; auto; split].
  - unfold wf_hists; rewrite Forall_forall_Znth; intros j ?.
    apply (Forall_Znth _ _ j ([], [])) in Hwf; [destruct Hwf as ((? & ?) & ? & ?) | omega].
    destruct (eq_dec j i); [|specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i))].
    + subst; rewrite Hhi in *.
      split; [|rewrite Hi2, map_app, Forall_app; repeat constructor; auto; apply ordered_snoc; auto].
      destruct Hi1 as [(-> & _) | (? & ? & -> & _)]; rewrite map_app, Forall_app; repeat constructor;
        auto; try (apply ordered_snoc; auto).
      * rewrite app_cons_assoc; apply ordered_snoc; [apply ordered_snoc; auto|].
        apply newer_snoc; auto.
      * destruct Hr; subst; simpl; auto.
    + destruct Hrest as ((? & ? & ? & Hcase & ? & ? & -> & ?) & _); auto; simpl in *.
      split; auto.
      destruct Hcase as [-> | (? & ? & ->)]; rewrite map_app, Forall_app; repeat constructor; auto.
      * apply ordered_snoc; auto.
      * rewrite app_cons_assoc; apply ordered_snoc; [apply ordered_snoc; auto|].
        apply newer_snoc; auto.
    + destruct Hrest as (_ & ->); auto.
  - intros k0 v0 j Hk0 Hj.
    exploit (Znth_inbounds j (make_map h) (0, 0)).
    { rewrite Hj; intro X; inv X; contradiction Hk0; auto. }
    intro; unfold make_map in *; rewrite <- upd_Znth_map.
    rewrite Zlength_map in *.
    rewrite Znth_map with (d' := ([], [])) in Hj by auto; inv Hj.
    destruct (eq_dec j i); [subst; rewrite upd_Znth_same, Hhi; auto | rewrite upd_Znth_diff'];
      rewrite ?Zlength_map in *; auto; try omega.
    rewrite Znth_map with (d' := ([], [])) by omega.
    specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i));
      [|destruct Hrest as (_ & ->); auto].
    destruct Hrest as ((? & r1 & ? & Hcase & ? & ? & -> & Heq) & _); auto; simpl in *.
    assert (value_of_hist (fst (Znth j h ([], []))) <> vint 0).
    { intro X; rewrite X in Hk0; contradiction Hk0; auto. }
    destruct Hcase as [-> | (? & ? & ->)].
    + unfold value_of_hist at 1; rewrite last_snoc, Heq; auto.
    + rewrite app_cons_assoc; unfold value_of_hist at 1; rewrite last_snoc, Heq; auto; simpl.
      destruct (eq_dec (Vint r1) (vint 0)); auto.
      absurd (r1 = Int.zero); auto; inv e; auto.
  - assert (0 <= i < Zlength h') by (rewrite Hlen; auto).
    unfold set.
    assert (lookup (make_map (upd_Znth i h' (hk, hv))) k = Some i) as ->.
    + unfold lookup, make_map.
      assert (i = ((i - hash k) mod 32 + hash k) mod 32) as Hmod.
      { rewrite Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small by omega; auto. }
      pose proof (hash_range k).
      assert (Zlength (map (fun hs => (make_int (value_of_hist (fst hs)), make_int (value_of_hist (snd hs))))
              (upd_Znth i h' (hk, hv))) = 32) as Hlen1.
      { rewrite Zlength_map, upd_Znth_Zlength; auto; omega. }
      erewrite index_of'_succeeds; simpl.
      f_equal; symmetry; apply Hmod.
      { rewrite Zlength_rebase; rewrite ?Zlength_map, ?upd_Znth_Zlength; auto; try omega.
        replace (Zlength h') with 32; [apply Z_mod_lt; computable | omega]. }
      { rewrite Forall_forall; intros x Hin.
        apply In_Znth with (d := (0, 0)) in Hin; destruct Hin as (j & Hj & Hx).
        exploit (Z_mod_lt (i - hash k) 32); [computable | intro].
        rewrite Zlength_sublist in Hj; rewrite ?Zlength_rebase; rewrite ?Hlen1; try omega.
        rewrite Znth_sublist, Z.add_0_r in Hx by (auto; omega).
        rewrite Znth_rebase in Hx by omega.
        rewrite Hlen1, Znth_map with (d' := ([], [])) in Hx.
        subst x; simpl.
        specialize (Hrest ((j + hash k) mod 32)); destruct Hrest as ((? & r1 & ? & Hcase & ? & ? & ?) & _).
        { unfold indices; rewrite in_map_iff.
          exists j; split; [rewrite Z.add_comm; auto|].
          rewrite In_upto, Z2Nat.id; omega. }
        rewrite upd_Znth_diff'; auto.
        destruct Hcase as [-> | (? & ? & ->)]; [|rewrite app_cons_assoc]; unfold value_of_hist;
          rewrite last_snoc; simpl.
        * split; intro X; [absurd (r1 = Int.zero) | absurd (r1 = Int.repr k)]; auto; apply signed_inj; auto.
          rewrite Int.signed_repr; auto.
        * destruct (eq_dec (Vint r1) (vint 0)); [absurd (r1 = Int.zero); auto; inversion e; auto | simpl].
          split; intro X; [absurd (r1 = Int.zero) | absurd (r1 = Int.repr k)]; auto; apply signed_inj; auto.
          rewrite Int.signed_repr; auto.
        * intro X; rewrite <- X, Zminus_mod_idemp_l, Z.add_simpl_r, Z.sub_0_r, Zmod_small in Hj; try omega.
          destruct Hj; split; auto; etransitivity; eauto; apply Z_mod_lt; computable.
        * rewrite upd_Znth_Zlength by auto.
          replace (Zlength h') with 32 by omega; apply Z_mod_lt; computable. }
      { rewrite <- Hlen1, Znth_rebase', Znth_map with (d' := ([], [])); simpl;
          rewrite ?Zlength_map, ?upd_Znth_Zlength; auto; try omega.
        rewrite upd_Znth_same by auto; simpl.
        destruct (eq_dec (value_of_hist hk) (vint 0)); [rewrite e; auto|].
        rewrite Hr0; auto; destruct Hr; subst r; auto; simpl.
        rewrite Int.signed_repr; auto. }
    + simpl; unfold make_map; erewrite <- upd_Znth_map, upd_Znth_twice, upd_Znth_triv; rewrite ?Zlength_map;
        auto.
      rewrite Znth_map', Hk', Hi2.
      unfold value_of_hist; rewrite last_snoc; simpl.
      rewrite !Int.signed_repr; auto.
Qed.

(* What can a thread know?
   At least certain keys exist, and whatever it did last took effect.
   It can even rely on the indices of known keys. *)
Definition set_item_spec :=
 DECLARE _set_item
  WITH key : Z, value : Z, p : val, sh : share, entries : list val, h : list (hist * hist)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; repable_signed value; readable_share sh; key <> 0; Forall isptr entries;
         Zlength h = 32; wf_hists h)
   LOCAL (temp _key (vint key); temp _value (vint value); gvar _m_entries p)
   SEP (data_at sh (tarray (tptr tentry) 32) entries p;
        fold_right sepcon emp (map (atomic_entry sh) entries);
        entry_hists entries h)
  POST [ tvoid ]
   EX i : Z, EX h' : list (hist * hist),
   PROP (set_item_trace h key value i h')
   LOCAL ()
   SEP (data_at sh (tarray (tptr tentry) 32) entries p;
        fold_right sepcon emp (map (atomic_entry sh) entries);
        entry_hists entries h').
(* set_item_trace_map describes the properties on the resulting map. *)

(*Lemma index_of_iff_out : forall m k, index_of m k = None <-> ~In k (map fst m).
Proof.
  split; intro.
  - induction m; auto; simpl in *.
    destruct a.
    destruct (eq_dec z k); [discriminate|].
    destruct (index_of m k); [discriminate|].
    intros [? | ?]; auto.
    contradiction IHm.
  - apply index_of_out.
    rewrite Forall_forall; repeat intro; contradiction H.
    rewrite in_map_iff; eauto.
Qed.

Corollary get_fail_iff : forall m k, get m k = None <-> ~In k (map fst m).
Proof.
  intros; unfold get; rewrite <- index_of_iff_out.
  destruct (index_of m k); simpl; split; auto; discriminate.
Qed.*)

Definition failed_load k (a b : hist * hist) := exists t r, newer (fst a) t /\
  fst b = fst a ++ [(t, Load (Vint r))] /\ r <> Int.zero /\ r <> Int.repr k /\ snd b = snd a /\
  (let v := value_of_hist (fst a) in v <> vint 0 -> v = Vint r).

(* get_item can return 0 in two cases: if the key is not in the map, or if its value is 0.
   In correct use, the latter should only occur if the value has not been initialized.
   Conceptually, this is still linearizable because we could have just checked before the key was added,
   but at a finer-grained level we can tell the difference from the history, so we might as well keep
   this information. *)
Definition get_item_trace (h : list (hist * hist)) k v i h' := Zlength h' = Zlength h /\
  0 <= i < Zlength h /\
  (let '(hk, hv) := Znth i h ([], []) in exists t r, newer hk t /\
     fst (Znth i h' ([], [])) = hk ++ [(t, Load (vint r))] /\
     (v = 0 /\ r = 0 /\ snd (Znth i h' ([], [])) = hv \/
      r = k /\ exists tv, Forall (fun x => fst x < tv)%nat hv /\
        snd (Znth i h' ([], [])) = hv ++ [(tv, Load (vint v))]) /\
    (let v := value_of_hist hk in v <> vint 0 -> v = vint r)) /\
  forall j, (In j (indices (hash k) i) -> failed_load k (Znth j h ([], [])) (Znth j h' ([], []))) /\
    (~In j (indices (hash k) i) -> j <> i -> Znth j h' ([], []) = Znth j h ([], [])).

Lemma get_item_trace_map : forall h k v i h' (Hwf : wf_hists h) (Hlenh : Zlength h = 32)
  (Htrace : get_item_trace h k v i h') (Hk : k <> 0) (Hrepk : repable_signed k) (Hrepv : repable_signed v),
  wf_hists h' /\ match get (make_map h') k with
  | Some v' => v' = v /\ map_incl (upd_Znth i (make_map h) (k, v)) (make_map h')
  | None => v = 0 /\ map_incl (make_map h) (make_map h') end.
Proof.
  intros.
  destruct Htrace as (Hlen & Hbounds & Hi & Hrest).
  destruct (Znth i h ([], [])) as (hk, hv) eqn: Hhi.
  destruct Hi as (t & r & Ht & Hi1 & Hi2 & Hr0).
  assert (i <= Zlength h') by (rewrite Hlen; destruct Hbounds; apply Z.lt_le_incl; auto).
  assert (0 <= i + 1 <= Zlength h').
  { rewrite Hlen; destruct Hbounds; split; [|rewrite <- lt_le_1]; auto; omega. }
  assert (vint k <> vint 0).
  { intro; contradiction Hk; apply repr_inj_signed; auto.
    { split; computable. }
    { congruence. }}
  assert (wf_hists h') as Hwf'; [|split; auto].
  - unfold wf_hists; rewrite Forall_forall_Znth; intros j ?.
    apply (Forall_Znth _ _ j ([], [])) in Hwf; [destruct Hwf as ((? & ?) & ? & ?) | omega].
    destruct (eq_dec j i); [|specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i))].
    + subst; rewrite Hhi in *.
      split; [rewrite Hi1, map_app, Forall_app; repeat constructor; auto; apply ordered_snoc; auto|].
      destruct Hi2 as [(? & ? & ->) | (? & ? & ? & ->)]; auto.
      rewrite map_app, Forall_app; repeat constructor; auto; apply ordered_snoc; auto.
    + destruct Hrest as ((? & ? & ? & -> & ? & ? & -> & ?) & _); auto; simpl in *.
      split; auto.
      rewrite map_app, Forall_app; repeat constructor; auto.
      apply ordered_snoc; auto.
    + destruct Hrest as (_ & ->); auto.
  - unfold get, lookup.
    pose proof (index_of'_spec k (rebase (make_map h') (hash k))) as Hspec.
    destruct (index_of' (rebase (make_map h') (hash k)) k) eqn: Hindex; simpl.
    unfold make_map at 1; rewrite Znth_map with (d' := ([], [])).
    pose proof (hash_range k).
    assert ((z + hash k) mod 32 = i) as Hz.
    { destruct Hspec as (Hz & Hcase & Hall).
      assert (Zlength (make_map h') = Zlength h') as Hlenm by (unfold make_map; rewrite Zlength_map; auto).
      assert (z <= (i - hash k) mod Zlength (make_map h')) as Hle.
      { eapply Forall_sublist_le; try apply Hall; simpl.
        { apply Z_mod_lt; omega. }
        { omega. }
        rewrite Znth_rebase' by omega.
        unfold make_map; rewrite Znth_map'.
        rewrite Hi1; unfold value_of_hist; rewrite last_snoc; simpl.
        destruct Hi2 as [(? & ? & ?) | (? & ?)]; subst; [|rewrite Int.signed_repr by auto]; tauto. }
      rewrite Zlength_rebase in Hz by omega.
      rewrite Znth_rebase, Hlenm in Hcase by omega.
      unfold make_map in Hcase; rewrite Znth_map with (d' := ([], [])) in Hcase; simpl in Hcase.
      destruct (eq_dec ((z + hash k) mod 32) i); auto.
      specialize (Hrest ((z + hash k) mod 32)); destruct Hrest as ((? & r1 & ? & Hfst & ? & ? & ?) & _).
      { unfold indices.
        rewrite in_map_iff.
        exists z; split; [rewrite Z.add_comm; auto|].
        rewrite In_upto, Z2Nat.id.
        rewrite Hlenm in Hle; replace (Zlength h') with 32 in Hle by omega.
        destruct (eq_dec z ((i - hash k) mod 32)); [|omega].
        contradiction n; rewrite e, Zplus_mod_idemp_l, Z.sub_simpl_r, Zmod_small; auto; omega.
        { apply Z_mod_lt; computable. } }
      replace (Zlength h') with 32 in Hcase by omega.
      rewrite Hfst in Hcase; unfold value_of_hist in Hcase; rewrite last_snoc in Hcase; simpl in Hcase.
      destruct Hcase; [absurd (r1 = Int.repr k) | absurd (r1 = Int.zero)]; auto; apply signed_inj; auto.
      rewrite Int.signed_repr; auto.
      { apply Z_mod_lt; omega. } }
    rewrite Hz, Hi1.
    replace (value_of_hist (hk ++ _)) with (vint r) by (unfold value_of_hist; rewrite last_snoc; auto); simpl.
    destruct Hi2 as [(? & ? & Hi2) | (? & ? & ? & Hi2)]; rewrite Hi2; clear dependent z; subst; simpl.
    + split; auto.
      intros k0 v0 j Hk0 Hj.
      exploit (Znth_inbounds j (make_map h) (0, 0)).
      { rewrite Hj; intro X; inv X; contradiction Hk0; auto. }
      unfold make_map in *; rewrite Zlength_map; intro;
        rewrite Znth_map with (d' := ([], [])) in Hj by auto; inv Hj.
      rewrite Znth_map with (d' := ([], [])) by omega.
      destruct (eq_dec j i).
      { subst; rewrite Hhi in *; simpl in *; contradiction Hk0.
        destruct (eq_dec (value_of_hist hk) (vint 0)); [rewrite e; auto|].
        rewrite Hr0; auto. }
      specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i)).
      * destruct Hrest as ((? & ? & ? & -> & ? & ? & -> & Heq) & _); auto.
        unfold value_of_hist at 1; rewrite last_snoc; simpl.
        destruct (eq_dec (value_of_hist (fst (Znth j h ([], [])))) (vint 0));
          [contradiction Hk0; rewrite e; auto|].
        rewrite Heq; auto.
      * destruct Hrest as (_ & ->); auto.
    + unfold value_of_hist; rewrite last_snoc; simpl.
      rewrite !Int.signed_repr by auto.
      if_tac; [contradiction Hk; auto|].
      split; auto.
      intros k0 v0 j Hk0 Hj.
      exploit (Znth_inbounds j (upd_Znth i (make_map h) (k, v)) (0, 0)).
      { rewrite Hj; intro X; inv X; contradiction Hk0; auto. }
      unfold make_map in *; rewrite upd_Znth_Zlength; rewrite Zlength_map; auto.
      intro; rewrite Znth_map with (d' := ([], [])) by omega.
      destruct (eq_dec j i).
      { subst; rewrite upd_Znth_same in Hj by (rewrite Zlength_map; auto).
        inv Hj; rewrite Hi1, Hi2.
        unfold value_of_hist; rewrite !last_snoc; simpl.
        rewrite !Int.signed_repr; auto. }
      rewrite upd_Znth_diff' in Hj; rewrite ?Zlength_map; auto.
      rewrite Znth_map with (d' := ([], [])) in Hj by auto; inv Hj.
      specialize (Hrest j); destruct (in_dec Z_eq_dec j (indices (hash k) i)).
      * destruct Hrest as ((? & ? & ? & -> & ? & ? & -> & Heq) & _); auto.
        unfold value_of_hist at 1; rewrite last_snoc; simpl.
        destruct (eq_dec (value_of_hist (fst (Znth j h ([], [])))) (vint 0));
          [contradiction Hk0; rewrite e; auto|].
        rewrite Heq; auto.
      * destruct Hrest as (_ & ->); auto.
    + replace (Zlength h') with 32 by omega; apply Z_mod_lt; computable.
    + assert (In r (map fst (rebase (make_map h') (hash k)))).
      { rewrite in_map_iff.
        unfold rebase, make_map; eexists; rewrite rotate_In, in_map_iff.
        split; [|do 2 eexists; eauto; apply Znth_In with (i0 := i); omega].
        rewrite Hi1; unfold value_of_hist; rewrite last_snoc; simpl.
        apply Int.signed_repr; destruct Hi2 as [(? & ? & ?) | (? & ?)]; subst; auto.
        { pose proof (hash_range k).
          rewrite Zlength_map; omega. } }
      destruct Hspec as (Hnk & Hnz), Hi2 as [(? & ? & ?) | (? & ?)]; subst;
        [contradiction Hnz | contradiction Hnk].
Qed.

(* Read the most recently written value. *)
Definition get_item_spec :=
 DECLARE _get_item
  WITH key : Z, p : val, sh : share, entries : list val, h : list (hist * hist)
  PRE [ _key OF tint, _value OF tint ]
   PROP (repable_signed key; readable_share sh; key <> 0; Forall isptr entries; Zlength h = 32; wf_hists h)
   LOCAL (temp _key (vint key); gvar _m_entries p)
   SEP (data_at sh (tarray (tptr tentry) 32) entries p;
        fold_right sepcon emp (map (atomic_entry sh) entries);
        entry_hists entries h)
  POST [ tint ]
   EX value : Z, EX i : Z, EX h' : list (hist * hist),
   PROP (repable_signed value; get_item_trace h key value i h')
   LOCAL (temp ret_temp (vint value))
   SEP (data_at sh (tarray (tptr tentry) 32) entries p;
        fold_right sepcon emp (map (atomic_entry sh) entries);
        entry_hists entries h').

Definition Gprog : funspecs := ltac:(with_library prog [surely_malloc_spec; atomic_CAS_spec; atomic_load_spec;
  atomic_store_spec; integer_hash_spec; set_item_spec; get_item_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call n.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh n p * memory_block Tsh n p)).
  - if_tac; entailer!.
  - forward_call tt.
    contradiction.
  - if_tac.
    + forward. subst p. discriminate.
    + Intros. forward. entailer!.
  - forward. Exists p; entailer!.
Qed.

Lemma body_integer_hash: semax_body Vprog Gprog f_integer_hash integer_hash_spec.
Proof.
  start_function.
  forward.
Qed.

Opaque upto.

Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.

Ltac entailer_for_return ::= go_lower; entailer'.

Lemma apply_int_ops : forall v h i (Hv : verif_atomics.apply_hist (Vint i) h = Some v)
  (Hints : Forall int_op h), tc_val tint v.
Proof.
  induction h; simpl; intros.
  - inv Hv; eauto.
  - inversion Hints as [|?? Ha]; subst.
    destruct a.
    + destruct (eq_dec v0 (Vint i)); [eapply IHh; eauto | discriminate].
    + destruct v0; try contradiction; eapply IHh; eauto.
    + destruct (eq_dec r (Vint i)); [|discriminate].
      destruct Ha as (? & ? & ?).
      destruct w; try contradiction.
      destruct (eq_dec c (Vint i)); eapply IHh; eauto.
Qed.

Lemma failed_CAS_fst : forall v h h', Forall2 (failed_CAS v) h h' -> map snd h' = map snd h.
Proof.
  induction 1; auto.
  destruct H as (? & ? & ? & ? & ? & ? & ? & ?); simpl; f_equal; auto.
Qed.

Lemma indices_next : forall i j, ((j - i) mod 32) < 31 -> indices i (j + 1) = indices i j ++ [j mod 32].
Proof.
  intros; unfold indices.
  exploit (Z_mod_lt (j - i) 32); [computable | intro].
  rewrite Z.add_sub_swap, <- Zplus_mod_idemp_l, Zmod_small by omega.
  rewrite Z2Nat.inj_add by omega.
  rewrite upto_app, map_app; simpl.
  change (upto 1) with [0]; simpl.
  rewrite Z2Nat.id, Z.add_0_r by omega.
  rewrite Zplus_mod_idemp_r, Zplus_minus; auto.
Qed.

Lemma body_set_item : semax_body Vprog Gprog f_set_item set_item_spec.
Proof.
  start_function.
  forward_call key.
  eapply semax_pre with (P' := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
    PROP (Zlength h' = Zlength h; i1 mod 32 = (i + hash key) mod 32; 0 <= i < 32;
          forall j, (In j (indices (hash key) (i + hash key)) -> failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
    LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
    SEP (data_at sh (tarray (tptr tentry) 32) entries p; fold_right sepcon emp (map (atomic_entry sh) entries);
         entry_hists entries h')).
  { Exists 0 (key * 654435761)%Z h; entailer!.
    unfold hash at 1; rewrite Zmod_mod; split; auto.
    unfold indices; rewrite Zminus_diag; split; auto; contradiction. }
  eapply semax_loop.
  - Intros i i1 h'; forward.
    forward.
    rewrite sub_repr, and_repr; simpl.
    rewrite Zland_two_p with (n := 5) by omega.
    change (2 ^ 5) with 32.
    exploit (Z_mod_lt i1 32); [omega | intro Hi1].
    assert (0 <= i1 mod 32 < Zlength h') by omega.
    assert_PROP (Zlength entries = 32) as Hentries by entailer!.
    rewrite <- Hentries in Hi1 at 3.
    assert (isptr (Znth (i1 mod 32) entries Vundef)).
    { apply Forall_Znth; auto. }
    forward.
    forward.
    assert (i <= Zlength h') by omega.
    rewrite extract_nth_sepcon with (i := i1 mod 32), Znth_map with (d' := Vundef); try rewrite Zlength_map;
      auto.
    unfold entry_hists; erewrite extract_nth_sepcon with (i := i1 mod 32)(l := map _ _), Znth_map, Znth_upto; simpl;
      auto; rewrite ?Zlength_map, ?Zlength_upto; simpl; try omega.
    unfold atomic_entry; Intros lkey lval.
    rewrite atomic_loc_isptr.
    forward.
    destruct (Znth (i1 mod 32) h' ([], [])) as (hki, hvi) eqn: Hhi.
    assert (~ In (i1 mod 32) (indices (hash key) (i + hash key))) as Hnew.
    { unfold indices; rewrite in_map_iff; intros (? & Heq & Hin).
      rewrite Z.add_simpl_r, In_upto, Z2Nat.id in Hin by (apply Z_mod_lt; computable).
      replace (i1 mod 32) with ((i + hash key) mod 32) in Heq.
      rewrite Z.add_comm in Heq; apply Zmod_plus_inv in Heq; [|computable].
      rewrite Zmod_small in Heq; [omega|].
      destruct Hin; split; auto; etransitivity; eauto; apply Z_mod_lt; computable. }
    assert (Znth (i1 mod 32) h ([], []) = Znth (i1 mod 32) h' ([], [])) as Heq.
    { match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => symmetry; apply H; auto end. }
    assert (ordered_hist hki).
    { match goal with H : wf_hists h |- _ => eapply Forall_Znth with (i0 := i1 mod 32) in H; [|omega];
      rewrite Heq, Hhi in H; tauto end. }
    forward_call (Tsh, sh, field_address tentry [StructField _key] (Znth (i1 mod 32) entries Vundef), lkey, vint 0,
      hki, fun (h : hist) => !!(h = hki) && emp, k_R,
      fun (h : hist) (v : val) => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> v = v0) && emp).
    { entailer!.
      rewrite field_address_offset; simpl.
      rewrite isptr_offset_val_zero; auto.
      { rewrite field_compatible_cons; simpl.
        split; [unfold in_members; simpl|]; auto. } }
    { repeat (split; auto).
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
        apply apply_int_ops in Hvx; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        specialize (Hhist _ _ Hin); apply nth_error_In in Hhist; subst; auto.
      + apply andp_right; auto.
        eapply derives_trans, precise_weak_precise, precise_andp2; auto. }
    Intros x; destruct x as (t, v); simpl in *.
    destruct v; try contradiction.
    focus_SEP 1.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
      forward_if (EX hki' : hist, PROP (hki' = hki ++ [(t, Load (vint key))] /\ i0 = Int.repr key \/
        exists r t', newer (hki ++ [(t, Load (Vint i0))]) t' /\
          hki' = hki ++ [(t, Load (vint 0)); (t', CAS (Vint r) (vint 0) (vint key))] /\
            (r = Int.zero \/ r = Int.repr key) /\
          forall v0 : val, last_value hki v0 -> v0 <> vint 0 -> Vint r = v0)
      (LOCALx Q (SEPx (ghost_hist hki' (field_address tentry [StructField _key] (Znth (i1 mod 32) entries Vundef)) :: R))))
    end.
    + match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP (i0 = Int.zero) (LOCALx Q (SEPx R))) end.
      { eapply semax_pre; [|apply semax_continue].
        unfold POSTCONDITION, abbreviate, overridePost.
        destruct (eq_dec EK_continue EK_normal); [discriminate|].
        unfold loop1_ret_assert.
        instantiate (1 := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
          PROP (Zlength h' = Zlength h; i1 mod 32 = (i + hash key) mod 32; 0 <= i < 32;
          forall j, (In j (indices (hash key) ((i + 1) + hash key)) -> failed_CAS key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
          LOCAL (temp _idx (vint i1); temp _key (vint key); temp _value (vint value); gvar _m_entries p)
          SEP (data_at sh (tarray (tptr tentry) 32) entries p; fold_right sepcon emp (map (atomic_entry sh) entries);
               entry_hists entries h')).
        Exists i (i1 mod 32) (upd_Znth (i1 mod 32) h' (fst (Znth (i1 mod 32) h' ([], [])) ++ [(t, Load (Vint i0))], snd (Znth (i1 mod 32) h' ([], [])))).
        go_lower.
        apply andp_right.
        { apply prop_right; split.
          { rewrite upd_Znth_Zlength; auto; omega. }
          rewrite Zmod_mod.
          split; auto; split; auto; split; auto.
          intro; rewrite <- Z.add_assoc, (Z.add_comm 1), Z.add_assoc, indices_next, in_app.
          split.
          * intros [Hin | Hin].
            { rewrite upd_Znth_diff'; auto.
              match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
              { intro; contradiction Hnew; subst; auto. } }
            simpl in Hin; destruct Hin; [subst | contradiction].
            replace ((i + hash key) mod 32) with (i1 mod 32).
            rewrite upd_Znth_same by auto.
            rewrite Heq, Hhi; repeat eexists; eauto; auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint i0 = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * intro Hout; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl; auto. }
          * admit. (* list is long enough *) }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        rewrite (sepcon_comm (ghost_hist _ _)).
        rewrite !sepcon_assoc, <- 4sepcon_assoc; apply sepcon_derives.
        * rewrite replace_nth_sepcon; apply sepcon_list_derives.
          { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
          rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
          destruct (eq_dec i2 (i1 mod 32)).
          subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
          rewrite Znth_map with (d' := Vundef) by auto.
          unfold atomic_entry.
          Exists lkey lval; entailer!.
          { rewrite upd_Znth_diff'; rewrite ?Zlength_map; auto. }
        * rewrite (sepcon_comm _ (ghost_hist _ _)), <- sepcon_assoc, replace_nth_sepcon.
          apply sepcon_list_derives.
          { rewrite upd_Znth_Zlength; rewrite !Zlength_map, Zlength_upto; auto; simpl; omega. }
          rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
          destruct (eq_dec i2 (i1 mod 32)).
          subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
          erewrite Znth_map, Znth_upto; simpl; auto; try omega.
          rewrite upd_Znth_same; auto; simpl.
          rewrite Hhi.
          rewrite sepcon_comm; auto.
          { rewrite upd_Znth_diff'; auto.
            rewrite Zlength_upto in *.
            erewrite !Znth_map, !Znth_upto; auto; try omega.
            rewrite upd_Znth_diff'; auto.
            { rewrite Zlength_map, Zlength_upto; simpl; omega. } }
          { rewrite Zlength_upto; simpl; omega. } }
      { forward.
        entailer!. }
      Intros; subst.
      forward_call (Tsh, sh, field_address tentry [StructField _key] (Znth (i1 mod 32) entries Vundef), lkey, vint 0,
        vint key, vint 0, hki ++ [(t, Load (vint 0))],
        fun (h : hist) c v => !!(c = vint 0 /\ v = vint key /\ h = hki ++ [(t, Load (vint 0))]) && emp,
        k_R, fun (h : hist) (v : val) => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> v = v0) && emp).
      { entailer!.
        rewrite field_address_offset; simpl.
        rewrite isptr_offset_val_zero; auto.
        { rewrite field_compatible_cons; simpl.
          split; [unfold in_members; simpl|]; auto. } }
      { repeat (split; auto).
        intros ?????????????? Ha.
        unfold k_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        repeat split.
        + rewrite Forall_app; repeat constructor; auto.
          apply apply_int_ops in Hvx; auto.
        + intros ? Hin; rewrite in_app in Hin.
          destruct Hin as [? | [? | ?]]; [| |contradiction].
          * intros.
            replace vx with (value_of e) by (symmetry; auto).
            if_tac; auto; absurd (value_of e = vint 0); auto.
          * subst; simpl; intros.
            if_tac; if_tac; auto; absurd (vx = vint 0); auto.
        + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
          exploit Hhist.
          { rewrite in_app; eauto. }
          intro X; apply nth_error_In in X; subst; auto.
        + apply andp_right; auto.
          eapply derives_trans, precise_weak_precise, precise_andp2; auto. }
      Intros x; destruct x as (t', v); simpl in *.
      destruct v; try contradiction.
      match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP () (LOCALx (temp _t'4 (vint (if eq_dec i0 Int.zero then 0
          else if eq_dec i0 (Int.repr key) then 0 else 1)) :: Q) (SEPx R))) end.
      { forward.
        destruct (eq_dec i0 Int.zero); [absurd (i0 = Int.zero); auto|]; simpl force_val.
        destruct (Int.eq i0 (Int.repr key)) eqn: Hi0; [apply int_eq_e in Hi0 | apply int_eq_false_e in Hi0];
           simpl force_val.
        + destruct (eq_dec i0 (Int.repr key)); [apply drop_tc_environ | absurd (i0 = Int.repr key); auto].
        + destruct (eq_dec i0 (Int.repr key)); [absurd (i0 = Int.repr key); auto | apply drop_tc_environ]. }
      { forward.
        subst; rewrite eq_dec_refl; apply drop_tc_environ. }
      match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP (i0 = Int.zero \/ i0 = Int.repr key) (LOCALx Q (SEPx R))) end.
      { destruct (eq_dec i0 Int.zero); [absurd (Int.zero = Int.zero); auto|].
        destruct (eq_dec i0 (Int.repr key)); [absurd (Int.zero = Int.zero); auto|].
        eapply semax_pre; [|apply semax_continue].
        unfold POSTCONDITION, abbreviate, overridePost.
        destruct (eq_dec EK_continue EK_normal); [discriminate|].
        unfold loop1_ret_assert.
        go_lower.
        Exists i (i1 mod 32) (upd_Znth (i1 mod 32) h' (fst (Znth (i1 mod 32) h' ([], [])) ++
          [(t, Load (vint 0)); (t', CAS (Vint i0) (vint 0) (vint key))], snd (Znth (i1 mod 32) h' ([], [])))).
        apply andp_right.
        { apply prop_right; split.
          { rewrite upd_Znth_Zlength; auto; omega. }
          rewrite Zmod_mod.
          split; auto; split; auto; split; auto.
          intro; rewrite <- Z.add_assoc, (Z.add_comm 1), Z.add_assoc, indices_next, in_app.
          split.
          * intros [Hin | Hin].
            { rewrite upd_Znth_diff'; auto.
              match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
              { intro; contradiction Hnew; subst; auto. } }
            simpl in Hin; destruct Hin; [subst | contradiction].
            replace ((i + hash key) mod 32) with (i1 mod 32).
            rewrite upd_Znth_same by auto.
            match goal with H : Forall _ (hki ++ _) |- _ => rewrite Forall_app in H; destruct H as (? & Ht);
              inv Ht end.
            simpl in *; rewrite Heq, Hhi; do 3 eexists; simpl; [|split; eauto]; repeat split; auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint i0 = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * intro Hout; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl; auto. }
          * admit. (* list is long enough *) }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        rewrite (sepcon_comm (ghost_hist _ _)).
        rewrite !sepcon_assoc, <- 4sepcon_assoc; apply sepcon_derives.
        * rewrite replace_nth_sepcon; apply sepcon_list_derives.
          { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
          rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
          destruct (eq_dec i2 (i1 mod 32)).
          subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
          rewrite Znth_map with (d' := Vundef) by auto.
          unfold atomic_entry.
          Exists lkey lval; entailer!.
          { rewrite upd_Znth_diff'; rewrite ?Zlength_map; auto. }
        * rewrite (sepcon_comm _ (ghost_hist _ _)), <- sepcon_assoc, replace_nth_sepcon.
          apply sepcon_list_derives.
          { rewrite upd_Znth_Zlength; rewrite !Zlength_map, Zlength_upto; auto; simpl; omega. }
          rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
          destruct (eq_dec i2 (i1 mod 32)).
          subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
          erewrite Znth_map, Znth_upto; simpl; auto; try omega.
          rewrite upd_Znth_same; auto; simpl.
          rewrite Hhi.
          rewrite <- app_assoc, sepcon_comm; auto.
          { rewrite upd_Znth_diff'; auto.
            rewrite Zlength_upto in *.
            erewrite !Znth_map, !Znth_upto; auto; try omega.
            rewrite upd_Znth_diff'; auto.
            { rewrite Zlength_map, Zlength_upto; simpl; omega. } }
          { rewrite Zlength_upto; simpl; omega. } }
      { forward.
        entailer!.
        destruct (eq_dec i0 Int.zero); auto.
        destruct (eq_dec i0 (Int.repr key)); auto; discriminate. }
      intros.
      unfold exit_tycon, overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert, overridePost.
      rewrite eq_dec_refl.
      go_lower.
      apply andp_right; [apply prop_right; auto|].
      rewrite <- app_assoc; Exists (hki ++ [(t, Load (vint 0)); (t', CAS (Vint i0) (vint 0) (vint key))]);
        entailer!.
      right; do 3 eexists; eauto.
    + forward.
      Exists (hki ++ [(t, Load (Vint i0))]); entailer!.
    + rewrite (atomic_loc_isptr _ lval).
      Intros hki'.
      forward.
      forward.
      forward_call (Tsh, sh, field_address tentry [StructField _value] (Znth (i1 mod 32) entries Vundef), lval,
        vint value, vint 0, hvi, fun (h : hist) v => !!(v = vint value) && emp, v_R, fun (h : hist) => emp).
      { entailer!.
        rewrite field_address_offset; auto.
        { rewrite field_compatible_cons; simpl.
          split; [unfold in_members; simpl|]; auto. } }
      { repeat (split; auto).
        intros ????????????? Ha.
        unfold v_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        apply andp_right; auto.
        eapply derives_trans, precise_weak_precise; auto. }
      Intros t'.
      forward.
      Exists (i1 mod 32) (upd_Znth (i1 mod 32) h' (hki', hvi ++ [(t', Store (vint value))])).
      apply andp_right; auto.
      apply andp_right.
      { apply prop_right; split; auto.
        split.
        { rewrite upd_Znth_Zlength; auto. }
        split; [omega|].
        rewrite Heq, Hhi; simpl.
        rewrite upd_Znth_same by auto; simpl; split.
        - match goal with H : _ \/ _ |- _ => destruct H as [(? & ?) | (? & ? & ? & ? & ? & ?)]; subst end.
          + do 4 eexists; eauto; split; eauto; split; eauto; split; auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          + do 4 eexists; eauto; split; eauto.
            split.
            * simpl; right; do 2 eexists; [|split; [eauto|]].
              { match goal with H : newer (_ ++ _) _ |- _ => unfold newer in H; rewrite Forall_app in H;
                  destruct H as (_ & Ht); inv Ht; auto end. }
              match goal with H : _ \/ _ |- _ => destruct H; subst; auto end.
            * split; auto.
              match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint x = v0 |- _ =>
                symmetry; apply H; auto end.
              rewrite ordered_last_value; auto.
        - assert (indices (hash key) (i + hash key) = indices (hash key) (i1 mod 32)) as Hindex.
          { unfold indices.
            replace (i1 mod 32) with ((i + hash key) mod 32).
            rewrite Zminus_mod_idemp_l; auto. }
          split.
          + intro Hin.
            rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            rewrite Hindex; auto.
            { intro; contradiction Hnew; subst.
              rewrite Hindex; auto. }
          + intros Hout ?; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl.
              rewrite <- Hindex; auto. } }
      apply andp_right; auto.
      fast_cancel.
      rewrite (sepcon_comm (ghost_hist _ _)).
      rewrite (sepcon_comm (ghost_hist _ _)).
      rewrite !sepcon_assoc, <- 4sepcon_assoc; apply sepcon_derives.
      * rewrite replace_nth_sepcon; apply sepcon_list_derives.
        { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
        rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
        destruct (eq_dec i2 (i1 mod 32)).
        subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
        rewrite Znth_map with (d' := Vundef) by auto.
        unfold atomic_entry.
        Exists lkey lval; entailer!.
        { rewrite upd_Znth_diff'; rewrite ?Zlength_map; auto. }
      * rewrite sepcon_comm, replace_nth_sepcon.
        assert (0 <= i < Zlength h') by omega.
        apply sepcon_list_derives.
        { rewrite upd_Znth_Zlength; rewrite !Zlength_map, Zlength_upto; simpl; omega. }
        rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
        destruct (eq_dec i2 (i1 mod 32)).
        subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
        erewrite Znth_map, Znth_upto; simpl; auto; try omega.
        rewrite upd_Znth_same; auto; simpl.
        { rewrite upd_Znth_diff'; auto.
          rewrite Zlength_upto in *.
          erewrite !Znth_map, !Znth_upto; auto; try omega.
          rewrite upd_Znth_diff'; auto.
          rewrite Zlength_map, Zlength_upto; simpl; omega. }
        { rewrite Zlength_upto; simpl; omega. }
  - Intros i i1 h'.
    forward.
    unfold loop2_ret_assert.
    Exists (i + 1) (i1 + 1) h'; entailer!.
    split.
    { rewrite <- Zplus_mod_idemp_l.
      replace (i1 mod 32) with ((i + hash key) mod 32).
      rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto. }
    admit. (* list is long enough *)
Admitted.

Lemma failed_load_fst : forall v h h', Forall2 (failed_load v) h h' -> map snd h' = map snd h.
Proof.
  induction 1; auto.
  destruct H as (? & ? & ? & ? & ? & ? & ? & ?); simpl; f_equal; auto.
Qed.

Lemma body_get_item : semax_body Vprog Gprog f_get_item get_item_spec.
Proof.
  start_function.
  forward_call key.
  eapply semax_pre with (P' := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
    PROP (Zlength h' = Zlength h; i1 mod 32 = (i + hash key) mod 32; 0 <= i < 32;
          forall j, (In j (indices (hash key) (i + hash key)) -> failed_load key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) (i + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
    LOCAL (temp _idx (vint i1); temp _key (vint key); gvar _m_entries p)
    SEP (data_at sh (tarray (tptr tentry) 32) entries p; fold_right sepcon emp (map (atomic_entry sh) entries);
         entry_hists entries h')).
  { Exists 0 (key * 654435761)%Z h; entailer!.
    unfold hash at 1; rewrite Zmod_mod; split; auto.
    unfold indices; rewrite Zminus_diag; split; auto; contradiction. }
  eapply semax_loop.
  - Intros i i1 h'; forward.
    forward.
    rewrite sub_repr, and_repr; simpl.
    rewrite Zland_two_p with (n := 5) by omega.
    change (2 ^ 5) with 32.
    exploit (Z_mod_lt i1 32); [omega | intro Hi1].
    assert (0 <= i1 mod 32 < Zlength h') by omega.
    assert_PROP (Zlength entries = 32) as Hentries by entailer!.
    rewrite <- Hentries in Hi1 at 3.
    assert (isptr (Znth (i1 mod 32) entries Vundef)).
    { apply Forall_Znth; auto. }
    forward.
    forward.
    assert (i <= Zlength h') by omega.
    rewrite extract_nth_sepcon with (i := i1 mod 32), Znth_map with (d' := Vundef); try rewrite Zlength_map;
      auto.
    unfold entry_hists; erewrite extract_nth_sepcon with (i := i1 mod 32)(l := map _ _), Znth_map, Znth_upto; simpl;
      auto; rewrite ?Zlength_map, ?Zlength_upto; simpl; try omega.
    unfold atomic_entry; Intros lkey lval.
    rewrite atomic_loc_isptr.
    forward.
    destruct (Znth (i1 mod 32) h' ([], [])) as (hki, hvi) eqn: Hhi.
    assert (~ In (i1 mod 32) (indices (hash key) (i + hash key))) as Hnew.
    { unfold indices; rewrite in_map_iff; intros (? & Heq & Hin).
      rewrite Z.add_simpl_r, In_upto, Z2Nat.id in Hin by (apply Z_mod_lt; computable).
      replace (i1 mod 32) with ((i + hash key) mod 32) in Heq.
      rewrite Z.add_comm in Heq; apply Zmod_plus_inv in Heq; [|computable].
      rewrite Zmod_small in Heq; [omega|].
      destruct Hin; split; auto; etransitivity; eauto; apply Z_mod_lt; computable. }
    assert (Znth (i1 mod 32) h ([], []) = Znth (i1 mod 32) h' ([], [])) as Heq.
    { match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => symmetry; apply H; auto end. }
    assert (ordered_hist hki).
    { match goal with H : wf_hists h |- _ => eapply Forall_Znth with (i0 := i1 mod 32) in H; [|omega];
      rewrite Heq, Hhi in H; tauto end. }
    forward_call (Tsh, sh, field_address tentry [StructField _key] (Znth (i1 mod 32) entries Vundef), lkey, vint 0,
      hki, fun h => !!(h = hki) && emp, k_R,
      fun (h : hist) (v : val) => !!(forall v0, last_value hki v0 -> v0 <> vint 0 -> v = v0) && emp).
    { entailer!.
      rewrite field_address_offset; simpl.
      rewrite isptr_offset_val_zero; auto.
      { rewrite field_compatible_cons; simpl.
        split; [unfold in_members; simpl|]; auto. } }
    { repeat (split; auto).
      intros ???????????? Ha.
      unfold k_R in *; simpl in *.
      eapply semax_pre, Ha.
      go_lowerx; entailer!.
      repeat split.
      + rewrite Forall_app; repeat constructor; auto.
        apply apply_int_ops in Hvx; auto.
      + intros ? Hin; rewrite in_app in Hin.
        destruct Hin as [? | [? | ?]]; subst; auto; contradiction.
      + intros ? [(? & ?) | (? & ? & Hin & ? & ?)] Hn; [contradiction Hn; auto|].
        specialize (Hhist _ _ Hin); apply nth_error_In in Hhist; subst; auto.
      + apply andp_right; auto.
        eapply derives_trans, precise_weak_precise, precise_andp2; auto. }
    Intros x; destruct x as (t, v); simpl in *.
    destruct v; try contradiction.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROP (i0 <> Int.repr key) (LOCALx Q (SEPx R))) end.
    + rewrite (atomic_loc_isptr _ lval).
      forward.
      forward.
      forward_call (Tsh, sh, field_address tentry [StructField _value] (Znth (i1 mod 32) entries Vundef), lval, vint 0,
        snd (Znth (i1 mod 32) h' ([], [])), fun (h : hist) => emp, v_R, fun (h : hist) (v : val) => emp).
      { entailer!.
        rewrite field_address_offset; auto.
        { rewrite field_compatible_cons; simpl.
          split; [unfold in_members; simpl|]; auto. } }
      { rewrite Hhi; fast_cancel. }
      { repeat (split; auto).
        intros ???????????? Ha.
        unfold v_R in *; simpl in *.
        eapply semax_pre, Ha.
        go_lowerx; entailer!.
        apply andp_right; auto.
        eapply derives_trans, precise_weak_precise; auto. }
      Intros x; destruct x as (t', v); simpl in *.
      forward.
      Exists (Int.signed v) (i1 mod 32) (upd_Znth (i1 mod 32) h' (fst (Znth (i1 mod 32) h' ([], [])) ++ [(t, Load (vint key))],
        snd (Znth (i1 mod 32) h' ([], [])) ++ [(t', Load (Vint v))])).
      apply andp_right.
      { apply prop_right.
        split; [apply Int.signed_range|].
        split; auto.
        split.
        { rewrite upd_Znth_Zlength; auto. }
        split; [omega|].
        rewrite Heq, Hhi in *; simpl in *.
        rewrite upd_Znth_same by auto; simpl; split.
        - do 3 eexists; eauto; split; eauto; split; eauto; [rewrite Int.repr_signed; eauto|].
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint key = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
        - assert (indices (hash key) (i + hash key) = indices (hash key) (i1 mod 32)) as Hindex.
          { unfold indices.
            replace (i1 mod 32) with ((i + hash key) mod 32).
            rewrite Zminus_mod_idemp_l; auto. }
          split.
          + intro Hin.
            rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            rewrite Hindex; auto.
            { intro; contradiction Hnew; subst.
              rewrite Hindex; auto. }
          + intros Hout ?; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl.
              rewrite <- Hindex; auto. } }
      apply andp_right; [apply prop_right; rewrite Int.repr_signed; auto|].
      fast_cancel.
      rewrite (sepcon_comm (ghost_hist _ _)).
      rewrite (sepcon_comm (ghost_hist _ _)).
      rewrite !sepcon_assoc, <- 4sepcon_assoc; apply sepcon_derives.
      * rewrite replace_nth_sepcon; apply sepcon_list_derives.
        { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
        rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
        destruct (eq_dec i0 (i1 mod 32)).
        subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
        rewrite Znth_map with (d' := Vundef) by auto.
        unfold atomic_entry.
        Exists lkey lval; entailer!.
        { rewrite upd_Znth_diff'; rewrite ?Zlength_map; auto. }
      * rewrite sepcon_comm, replace_nth_sepcon.
        rewrite Hhi; apply sepcon_list_derives.
        { rewrite upd_Znth_Zlength; rewrite !Zlength_map, Zlength_upto; simpl; omega. }
        rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
        destruct (eq_dec i0 (i1 mod 32)).
        subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
        erewrite Znth_map, Znth_upto; simpl; auto; try omega.
        rewrite upd_Znth_same; auto; simpl.
        { rewrite upd_Znth_diff'; auto.
          rewrite Zlength_upto in *.
          erewrite !Znth_map, !Znth_upto; auto; try omega.
          rewrite upd_Znth_diff'; auto.
          rewrite Zlength_map, Zlength_upto; simpl; omega. }
        { rewrite Zlength_upto; simpl; omega. }
    + forward.
      entailer!.
    + Intros; match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
        forward_if (PROP (i0 <> Int.zero) (LOCALx Q (SEPx R))) end.
      * forward.
        Exists 0 (i1 mod 32) (upd_Znth (i1 mod 32) h' (fst (Znth (i1 mod 32) h' ([], [])) ++ [(t, Load (vint 0))], snd (Znth (i1 mod 32) h' ([], [])))).
        apply andp_right.
        { apply prop_right.
          split; [split; computable|].
          split; auto.
        split.
        { rewrite upd_Znth_Zlength; auto. }
        split; [omega|].
        rewrite Heq, Hhi in *; simpl in *.
        rewrite upd_Znth_same by auto; simpl; split.
        - do 3 eexists; eauto; split; eauto; split; eauto.
          match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> vint 0 = v0 |- _ =>
            symmetry; apply H; auto end.
          rewrite ordered_last_value; auto.
        - assert (indices (hash key) (i + hash key) = indices (hash key) (i1 mod 32)) as Hindex.
          { unfold indices.
            replace (i1 mod 32) with ((i + hash key) mod 32).
            rewrite Zminus_mod_idemp_l; auto. }
          split.
          + intro Hin.
            rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            rewrite Hindex; auto.
            { intro; contradiction Hnew; subst.
              rewrite Hindex; auto. }
          + intros Hout ?; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl.
              rewrite <- Hindex; auto. } }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        rewrite (sepcon_comm (ghost_hist _ _)).
        rewrite (sepcon_comm (ghost_hist _ _)).
        rewrite !sepcon_assoc, <- 4sepcon_assoc; apply sepcon_derives.
        -- rewrite replace_nth_sepcon; apply sepcon_list_derives.
           { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
           rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
           destruct (eq_dec i0 (i1 mod 32)).
           subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
           rewrite Znth_map with (d' := Vundef) by auto.
           unfold atomic_entry.
           Exists lkey lval; entailer!.
           { rewrite upd_Znth_diff'; rewrite ?Zlength_map; auto. }
        -- rewrite sepcon_comm, replace_nth_sepcon.
           rewrite Hhi; apply sepcon_list_derives.
           { rewrite upd_Znth_Zlength; rewrite !Zlength_map, Zlength_upto; simpl; omega. }
           rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
           destruct (eq_dec i0 (i1 mod 32)).
           subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
           erewrite Znth_map, Znth_upto; simpl; auto; try omega.
           rewrite upd_Znth_same; auto; simpl.
           rewrite sepcon_comm; auto.
           { rewrite upd_Znth_diff'; auto.
             rewrite Zlength_upto in *.
             erewrite !Znth_map, !Znth_upto; auto; try omega.
             rewrite upd_Znth_diff'; auto.
             rewrite Zlength_map, Zlength_upto; simpl; omega. }
          { rewrite Zlength_upto; simpl; omega. }
      * forward.
        entailer!.
      * intros.
        unfold exit_tycon, overridePost.
        destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
        Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert.
        instantiate (1 := EX i : Z, EX i1 : Z, EX h' : list (hist * hist),
          PROP (Zlength h' = Zlength h; i1 mod 32 = (i + hash key) mod 32; 0 <= i < 32;
          forall j, (In j (indices (hash key) ((i + 1) + hash key)) -> failed_load key (Znth j h ([], [])) (Znth j h' ([], []))) /\
            (~In j (indices (hash key) ((i + 1) + hash key)) -> Znth j h' ([], []) = Znth j h ([], [])))
          LOCAL (temp _idx (vint i1); temp _key (vint key); gvar _m_entries p)
          SEP (data_at sh (tarray (tptr tentry) 32) entries p; fold_right sepcon emp (map (atomic_entry sh) entries);
               entry_hists entries h')).
        Exists i (i1 mod 32) (upd_Znth (i1 mod 32) h' (fst (Znth (i1 mod 32) h' ([], [])) ++ [(t, Load (Vint i0))], snd (Znth (i1 mod 32) h' ([], [])))).
        go_lower.
        apply andp_right.
        { apply prop_right; split.
          { rewrite upd_Znth_Zlength; auto; omega. }
          rewrite Zmod_mod.
          split; auto; split; auto; split; auto.
          intro; rewrite <- Z.add_assoc, (Z.add_comm 1), Z.add_assoc, indices_next, in_app.
          split.
          * intros [Hin | Hin].
            { rewrite upd_Znth_diff'; auto.
              match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
              { intro; contradiction Hnew; subst; auto. } }
            simpl in Hin; destruct Hin; [subst | contradiction].
            replace ((i + hash key) mod 32) with (i1 mod 32).
            rewrite upd_Znth_same by auto.
            rewrite Heq, Hhi; repeat eexists; eauto; auto.
            match goal with H : forall v0, last_value hki v0 -> v0 <> vint 0 -> Vint i0 = v0 |- _ =>
              symmetry; apply H; auto end.
            rewrite ordered_last_value; auto.
          * intro Hout; rewrite upd_Znth_diff'; auto.
            match goal with H : forall j, (In j _ -> _) /\ (~In j _ -> _) |- _ => apply H; auto end.
            { intro; contradiction Hout; subst; simpl; auto. }
          * admit. (* list is long enough *) }
        apply andp_right; [apply prop_right; auto|].
        fast_cancel.
        rewrite (sepcon_comm (ghost_hist _ _)).
        rewrite !sepcon_assoc, <- 4sepcon_assoc; apply sepcon_derives.
        -- rewrite replace_nth_sepcon; apply sepcon_list_derives.
           { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto. }
           rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
           destruct (eq_dec i2 (i1 mod 32)).
           subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
           rewrite Znth_map with (d' := Vundef) by auto.
           unfold atomic_entry.
           Exists lkey lval; entailer!.
           { rewrite upd_Znth_diff'; rewrite ?Zlength_map; auto. }
        -- rewrite (sepcon_comm _ (ghost_hist _ _)), <- sepcon_assoc, replace_nth_sepcon.
           rewrite Hhi; apply sepcon_list_derives.
           { rewrite upd_Znth_Zlength; rewrite !Zlength_map, Zlength_upto; simpl; omega. }
           rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
           destruct (eq_dec i2 (i1 mod 32)).
           subst; rewrite upd_Znth_same by (rewrite Zlength_map; auto).
           erewrite Znth_map, Znth_upto; simpl; auto; try omega.
           rewrite upd_Znth_same; auto; simpl.
           rewrite sepcon_comm; auto.
           { rewrite upd_Znth_diff'; auto.
             rewrite Zlength_upto in *.
             erewrite !Znth_map, !Znth_upto; auto; try omega.
             rewrite upd_Znth_diff'; auto.
             rewrite Zlength_map, Zlength_upto; simpl; omega. }
           { rewrite Zlength_upto; simpl; omega. }
  - Intros i i1 h'.
    forward.
    unfold loop2_ret_assert.
    Exists (i + 1) (i1 + 1) h'; entailer!.
    split.
    { rewrite <- Zplus_mod_idemp_l.
      replace (i1 mod 32) with ((i + hash key) mod 32).
      rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm _ 1), Z.add_assoc; auto. }
    admit. (* list is long enough *)
Admitted.
