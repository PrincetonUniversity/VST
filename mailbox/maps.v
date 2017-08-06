Require Import progs.conclib.
Require Import progs.ghost.
Require Import RelationClasses.

Section Maps.

Context {A B : Type} {A_eq : EqDec A}.

Implicit Types (k : A) (v : B) (m : A -> option B).

Definition map_upd m k v k' := if eq_dec k' k then Some v else m k'.

Lemma map_upd_triv : forall m k v, m k = Some v -> map_upd m k v = m.
Proof.
  intros; extensionality; unfold map_upd.
  if_tac; subst; auto.
Qed.

Fixpoint map_upd_list m l :=
  match l with
  | [] => m
  | (k, v) :: rest => map_upd_list (map_upd m k v) rest
  end.

Definition map_add m1 m2 k := match m1 k with Some v' => Some v' | None => m2 k end.

Definition empty_map k : option B := None.

Definition singleton k v k1 := if eq_dec k1 k then Some v else None.

Definition map_incl m1 m2 := forall k v, m1 k = Some v -> m2 k = Some v.

Global Instance map_incl_refl : Reflexive map_incl.
Proof.
  repeat intro; auto.
Qed.

Global Instance map_incl_antisym : Antisymmetric _ _ map_incl.
Proof.
  intros x y Hx Hy a.
  specialize (Hx a); specialize (Hy a).
  destruct (x a); [erewrite Hx; eauto|].
  destruct (y a); auto.
Qed.

Global Instance map_incl_trans : Transitive map_incl.
Proof.
  repeat intro; auto.
Qed.

Lemma map_add_incl_compat : forall m1 m2 m3, map_incl m1 m2 -> map_incl (map_add m3 m1) (map_add m3 m2).
Proof.
  unfold map_add; repeat intro.
  destruct (m3 k); auto.
Qed.

Definition compatible m1 m2 := forall k v1 v2, m1 k = Some v1 -> m2 k = Some v2 -> v1 = v2.

Global Instance compatible_comm : Symmetric compatible.
Proof.
  repeat intro.
  symmetry; eauto.
Qed.

Lemma map_add_comm : forall m1 m2, compatible m1 m2 -> map_add m1 m2 = map_add m2 m1.
Proof.
  intros; extensionality x; unfold map_add.
  destruct (m1 x) eqn: Hm1, (m2 x) eqn: Hm2; eauto.
Qed.

Instance fmap_PCM : PCM (A -> option B) :=
  { join a b c := forall k v, c k = Some v <-> a k = Some v \/ b k = Some v }.
Proof.
  - intros.
    rewrite Hjoin; tauto.
  - intros.
    exists (fun k => match b k with Some v' => Some v' | None => d k end).
    assert (forall k v1 v2, b k = Some v1 -> d k = Some v2 -> v1 = v2) as Hbd.
    { intros ??? Hb Hd.
      specialize (Hjoin1 k v1).
      destruct Hjoin1 as (_ & Hc); lapply Hc; auto; intro Hc'.
      generalize (Hjoin2 k v1); intros (_ & He); lapply He; auto; intro He1.
      specialize (Hjoin2 k v2); destruct Hjoin2 as (_ & Hjoin2); lapply Hjoin2; auto; intro He2.
      rewrite He1 in He2; inv He2; auto. }
    split; intros; specialize (Hjoin1 k v); specialize (Hjoin2 k v).
    + destruct (b k) eqn: Hb; split; auto; intros [|]; auto; try discriminate.
      exploit Hbd; eauto.
    + rewrite Hjoin2, Hjoin1.
      destruct (b k) eqn: Hb; split; auto; intros [|]; auto.
      * specialize (Hbd _ _ _ Hb H); subst; auto.
      * destruct H; auto; discriminate.
Defined.

Lemma map_join_spec : forall m1 m2 m3, join m1 m2 m3 <-> compatible m1 m2 /\ m3 = map_add m1 m2.
Proof.
  simpl; split; intros.
  - split.
    + repeat intro.
      assert (m3 k = Some v1) as Hk by (rewrite H; auto).
      replace (m3 k) with (Some v2) in Hk by (symmetry; rewrite H; auto).
      inv Hk; auto.
    + extensionality x; unfold map_add.
      destruct (m1 x) eqn: Hm1; [rewrite H; auto|].
      destruct (m2 x) eqn: Hm2; [rewrite H; auto|].
      destruct (m3 x) eqn: Hm3; auto.
      rewrite H in Hm3; destruct Hm3 as [Hm3 | Hm3]; rewrite Hm3 in *; discriminate.
  - destruct H as [Hcompat]; subst; unfold map_add.
    destruct (m1 k) eqn: Hm1; split; auto; intros [?|?]; eauto; discriminate.
Qed.

Instance fmap_order : PCM_order map_incl.
Proof.
  constructor.
  - apply map_incl_refl.
  - apply map_incl_trans.
  - intros ??? Ha Hb; exists (map_add a b); split; simpl.
    + intros; unfold map_add; destruct (a k) eqn: Hk; split; auto; intros [|]; auto; try discriminate.
      specialize (Ha _ _ Hk); specialize (Hb _ _ H); rewrite Ha in Hb; auto.
    + unfold map_add; intros ???.
      destruct (a k) eqn: Hk; auto.
      inv H; auto.
  - split; repeat intro; specialize (H k v); rewrite H; auto.
  - split; auto; intros [|]; auto.
Defined.

Lemma map_snap_join : forall m1 m2 p,
  ghost_snap m1 p * ghost_snap m2 p = !!(compatible m1 m2) && ghost_snap (map_add m1 m2) p.
Proof.
  intros; rewrite ghost_snap_join'.
  apply mpred_ext.
  - Intros m.
    rewrite map_join_spec in H; destruct H; subst; entailer!.
  - Intros; Exists (map_add m1 m2).
    rewrite map_join_spec; entailer!.
Qed.

Lemma map_upd_list_app : forall l1 l2 m, map_upd_list m (l1 ++ l2) = map_upd_list (map_upd_list m l1) l2.
Proof.
  induction l1; auto; simpl; intros.
  destruct a; auto.
Qed.

Lemma map_upd_list_out : forall l m k, m k = None -> ~In k (map fst l) -> map_upd_list m l k = None.
Proof.
  induction l; auto; simpl; intros.
  destruct a; apply IHl.
  - unfold map_upd; if_tac; auto.
    subst; simpl in *; tauto.
  - tauto.
Qed.

Lemma compatible_incl : forall m1 m2 m (Hcompat : compatible m2 m) (Hincl : map_incl m1 m2), compatible m1 m.
Proof.
  repeat intro; eauto.
Qed.

Lemma compatible_k : forall m1 m2 (Hcompat : compatible m1 m2) k v, m2 k = Some v -> map_add m1 m2 k = Some v.
Proof.
  unfold compatible; intros.
  unfold map_add.
  destruct (m1 k) eqn: Hk; eauto.
Qed.

Lemma map_join_incl_compat : forall m1 m2 m' m'' (Hincl : map_incl m1 m2) (Hjoin : join m2 m' m''),
  exists m, join m1 m' m /\ map_incl m m''.
Proof.
  intros; apply join_comm in Hjoin.
  rewrite map_join_spec in Hjoin; destruct Hjoin as [Hjoin]; subst.
  do 2 eexists; [|apply map_add_incl_compat; eauto].
  symmetry in Hjoin; eapply compatible_incl in Hjoin; eauto.
  rewrite map_join_spec; split; auto.
  rewrite <- map_add_comm; auto.
Qed.

Lemma map_add_empty : forall m, map_add m empty_map = m.
Proof.
  intros; extensionality; unfold map_add, empty_map.
  destruct (m x); auto.
Qed.

Lemma map_add_assoc : forall m1 m2 m3, map_add (map_add m1 m2) m3 = map_add m1 (map_add m2 m3).
Proof.
  intros; extensionality; unfold map_add.
  destruct (m1 x); auto.
Qed.

Lemma map_incl_add : forall m1 m2, map_incl m1 (map_add m1 m2).
Proof.
  repeat intro; unfold map_add.
  rewrite H; auto.
Qed.

Lemma map_upd_incl : forall m1 m2 k v, map_incl m1 m2 ->
  m2 k = Some v -> map_incl (map_upd m1 k v) m2.
Proof.
  unfold map_upd; repeat intro.
  destruct (eq_dec k0 k); [congruence | auto].
Qed.

Lemma map_add_single : forall m k v, map_add (singleton k v) m = map_upd m k v.
Proof.
  intros; extensionality; unfold map_add, singleton, map_upd; if_tac; auto.
Qed.

Lemma compatible_add_assoc : forall m1 m2 m3, compatible m1 m2 ->
  compatible (map_add m1 m2) m3 -> compatible m1 (map_add m2 m3).
Proof.
  unfold compatible, map_add; intros.
  repeat match goal with H : forall _, _ |- _ => specialize (H k) end.
  replace (m1 k) with (Some v1) in *.
  destruct (m2 k); auto.
Qed.

Lemma map_incl_compatible : forall m1 m2 m3 (Hincl1 : map_incl m1 m3) (Hincl2 : map_incl m2 m3), compatible m1 m2.
Proof.
  intros; intros ??? Hk1 Hk2.
  apply Hincl1 in Hk1; apply Hincl2 in Hk2.
  rewrite Hk1 in Hk2; inv Hk2; auto.
Qed.

Lemma map_add_incl : forall m1 m2 m3, map_incl m1 m3 -> map_incl m2 m3 -> map_incl (map_add m1 m2) m3.
Proof.
  unfold map_add; intros.
  intros ?? Hk.
  destruct (m1 k) eqn: Hk1; auto.
  inv Hk; auto.
Qed.

Lemma incl_compatible : forall m1 m2, map_incl m1 m2 -> compatible m1 m2.
Proof.
  intros; intros ??? Hk1 Hk2.
  specialize (H _ _ Hk1); rewrite H in Hk2; inv Hk2; auto.
Qed.

Lemma map_add_redundant : forall m1 m2, map_incl m1 m2 -> map_add m1 m2 = m2.
Proof.
  intros; unfold map_add; extensionality k.
  destruct (m1 k) eqn: Hk; auto; symmetry; auto.
Qed.

Lemma empty_map_incl : forall m, map_incl empty_map m.
Proof.
  repeat intro; discriminate.
Qed.

End Maps.

Hint Resolve empty_map_incl.

Section ListMaps.

Context {A B : Type} {A_eq : EqDec A}.

Definition map_Znth i (L : A -> option (list B)) d k := option_map (fun v => Znth i v d) (L k).

Lemma map_Znth_single : forall i (k : A) (v : list B) d,
  map_Znth i (singleton k v) d = singleton k (Znth i v d).
Proof.
  intros; unfold map_Znth, singleton; extensionality.
  if_tac; auto.
Qed.

Lemma map_Znth_add : forall (m1 m2 : A -> option (list B)) i d,
  map_Znth i (map_add m1 m2) d = map_add (map_Znth i m1 d) (map_Znth i m2 d).
Proof.
  intros; unfold map_add, map_Znth; extensionality.
  destruct (m1 x); auto.
Qed.

Lemma map_Znth_eq : forall (L : A -> option (list B)) k vs d (Hlength : forall vs', L k = Some vs' -> Zlength vs' = Zlength vs)
  (Hnz : vs <> []) (Hall : forall i, 0 <= i < Zlength vs -> map_Znth i L d k = Some (Znth i vs d)),
  L k = Some vs.
Proof.
  intros.
  destruct (L k) eqn: Hk.
  specialize (Hlength _ eq_refl).
  apply f_equal, list_Znth_eq' with (d0 := d); auto.
  rewrite Hlength; intros j Hj; specialize (Hall _ Hj).
  unfold map_Znth in Hall; rewrite Hk in Hall; inv Hall; auto.
  { lapply (Hall 0).
    unfold map_Znth; rewrite Hk; discriminate.
    { pose proof (Zlength_nonneg vs).
      destruct (eq_dec (Zlength vs) 0); [|omega].
      apply Zlength_nil_inv in e; subst; contradiction. } }
Qed.

Lemma map_Znth_upd : forall (m : A -> option (list B)) k v i d,
  map_Znth i (map_upd m k v) d = map_upd (map_Znth i m d) k (Znth i v d).
Proof.
  intros; unfold map_Znth, map_upd; extensionality.
  if_tac; auto.
Qed.

Lemma map_incl_Znth : forall (m1 m2 : A -> option (list B)) i d, map_incl m1 m2 ->
  map_incl (map_Znth i m1 d) (map_Znth i m2 d).
Proof.
  unfold map_Znth; repeat intro.
  destruct (m1 k) eqn: Hm1; [|discriminate].
  rewrite (H _ _ Hm1); auto.
Qed.

End ListMaps.

Section Logs.
(* A log is a map from Z, and a finite log has a latest element. *)

Context {B : Type}.

Definition log_latest s (v1 : Z) (v2 : B) := s v1 = Some v2 /\ forall v', v1 < v' -> s v' = None.

Lemma log_latest_singleton : forall v1 v2, log_latest (singleton v1 v2) v1 v2.
Proof.
  unfold singleton; split.
  - rewrite eq_dec_refl; auto.
  - intros; if_tac; auto; omega.
Qed.

Lemma log_incl_latest : forall k1 k2 v1 v2 log1 log2 (Hincl : map_incl log1 log2)
  (Hv1 : log1 k1 = Some v1) (Hlatest : log_latest log2 k2 v2), k1 <= k2.
Proof.
  intros.
  destruct (zlt k2 k1); [|omega].
  destruct Hlatest as (? & Hlatest).
  specialize (Hlatest _ l).
  specialize (Hincl _ _ Hv1); rewrite Hincl in Hlatest; discriminate.
Qed.

Lemma log_latest_upd : forall log v1 v2 v1' v2', log_latest log v1 v2 -> v1 < v1' ->
  map_incl log (map_upd log v1' v2') /\ log_latest (map_upd log v1' v2') v1' v2'.
Proof.
  intros; destruct H as (? & Hlast); unfold map_upd; split.
  - repeat intro; if_tac; auto.
    subst; rewrite (Hlast v1') in *; auto; discriminate.
  - split; [rewrite eq_dec_refl; auto|].
    intros v' ?; lapply (Hlast v'); [|omega].
    intro; if_tac; auto; omega.
Qed.

Lemma log_latest_inj : forall log v1 v2 v1' v2' (H1 : log_latest log v1 v2) (H1' : log_latest log v1' v2'),
  v1 = v1' /\ v2 = v2'.
Proof.
  intros.
  assert (log v1 = Some v2) as Hv1 by (apply H1).
  assert (log v1' = Some v2') as Hv1' by (apply H1').
  pose proof (log_incl_latest _ _ _ _ _ _ (map_incl_refl log) Hv1 H1').
  pose proof (log_incl_latest _ _ _ _ _ _ (map_incl_refl log) Hv1' H1).
  assert (v1 = v1') by omega; subst.
  destruct H1 as [H1 _], H1' as [H1' _].
  rewrite H1 in H1'; inv H1'; auto.
Qed.

Lemma log_latest_add : forall m1 m2 k1 k2 (v1 v2 : B)
  (Hlatest1 : log_latest m1 k1 v1) (Hlatest2 : log_latest m2 k2 v2),
  log_latest (map_add m1 m2) (Z.max k1 k2) (if zlt k1 k2 then v2 else v1).
Proof.
  unfold log_latest, map_add; intros.
  destruct Hlatest1 as (Hv1 & Hk1), Hlatest2 as (Hv2 & Hk2).
  destruct (zlt k1 k2).
  - rewrite Z.max_r by omega.
    rewrite Hk1 by auto; split; auto.
    intros; rewrite Hk1, Hk2; auto; omega.
  - rewrite Z.max_l, Hv1 by omega; split; auto.
    intros; rewrite Hk1, Hk2; auto; omega.
Qed.

Lemma log_latest_upd_list : forall l (m : Z -> option B) k v k' v' (Hm : log_latest m k v)
  (Hlast : last l (k, v) = (k', v')) (Hlt : k <= k') (Hordered : Forall (fun '(k, v) => k <= k') l),
  log_latest (map_upd_list m l) k' v'.
Proof.
  intros.
  destruct (nil_dec l).
  { subst; inv Hlast; auto. }
  rewrite (app_removelast_last (k, v) n).
  rewrite map_upd_list_app; simpl.
  rewrite Hlast; split.
  - unfold map_upd; rewrite eq_dec_refl; auto.
  - intros; unfold map_upd.
    if_tac; [omega|].
    apply map_upd_list_out.
    + eapply Hm; omega.
    + rewrite in_map_iff; intros ((?, ?) & ? & ?); simpl in *; subst.
      rewrite Forall_forall in Hordered; exploit Hordered; [apply In_removelast; eauto|].
      simpl; omega.
Qed.

End Logs.

Lemma map_Znth_log_latest : forall {B} m k (v : list B) i d, log_latest m k v ->
  log_latest (map_Znth i m d) k (Znth i v d).
Proof.
  unfold log_latest, map_Znth; intros.
  destruct H as [-> H]; split; auto.
  intros; rewrite H; auto.
Qed.
