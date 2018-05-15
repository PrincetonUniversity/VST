Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import RelationClasses.

Section ListMaps.

Context {A B : Type} {A_eq : EqDec A} {d : Inhabitant B}.

Definition map_Znth i (L : A -> option (list B)) k := option_map (fun v => Znth i v) (L k).

Lemma map_Znth_single : forall i (k : A) (v : list B),
  map_Znth i (singleton k v) = singleton k (Znth i v).
Proof.
  intros; unfold map_Znth, singleton; extensionality.
  if_tac; auto.
Qed.

Lemma map_Znth_add : forall (m1 m2 : A -> option (list B)) i,
  map_Znth i (map_add m1 m2) = map_add (map_Znth i m1) (map_Znth i m2).
Proof.
  intros; unfold map_add, map_Znth; extensionality.
  destruct (m1 x); auto.
Qed.

Lemma map_Znth_eq : forall (L : A -> option (list B)) k vs (Hlength : forall vs', L k = Some vs' -> Zlength vs' = Zlength vs)
  (Hnz : vs <> []) (Hall : forall i, 0 <= i < Zlength vs -> map_Znth i L k = Some (Znth i vs)),
  L k = Some vs.
Proof.
  intros.
  destruct (L k) eqn: Hk.
  specialize (Hlength _ eq_refl).
  apply f_equal, list_Znth_eq'; auto.
  rewrite Hlength; intros j Hj; specialize (Hall _ Hj).
  unfold map_Znth in Hall; rewrite Hk in Hall; inv Hall; auto.
  { lapply (Hall 0).
    unfold map_Znth; rewrite Hk; discriminate.
    { pose proof (Zlength_nonneg vs).
      destruct (eq_dec (Zlength vs) 0); [|omega].
      apply Zlength_nil_inv in e; subst; contradiction. } }
Qed.

Lemma map_Znth_upd : forall (m : A -> option (list B)) k v i,
  map_Znth i (map_upd m k v) = map_upd (map_Znth i m) k (Znth i v).
Proof.
  intros; unfold map_Znth, map_upd; extensionality.
  if_tac; auto.
Qed.

Lemma map_incl_Znth : forall (m1 m2 : A -> option (list B)) i, map_incl m1 m2 ->
  map_incl (map_Znth i m1) (map_Znth i m2).
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

Lemma map_Znth_log_latest : forall {B} {d : Inhabitant B} m k (v : list B) i, log_latest m k v ->
  log_latest (map_Znth i m) k (Znth i v).
Proof.
  unfold log_latest, map_Znth; intros.
  destruct H as [-> H]; split; auto.
  intros; rewrite H; auto.
Qed.
