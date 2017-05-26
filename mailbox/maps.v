Require Import progs.conclib.
Require Import progs.ghost.
Require Import RelationClasses.

Section Maps.

Context {A B : Type} {A_eq : EqDec A}.

Definition map_upd (H : A -> option B) k v k' := if eq_dec k' k then Some v else H k'.

Lemma map_upd_triv : forall m k v, m k = Some v -> map_upd m k v = m.
Proof.
  intros; extensionality; unfold map_upd.
  if_tac; subst; auto.
Qed.

Fixpoint map_upd_list (m : A -> option B) l :=
  match l with
  | [] => m
  | (k, v) :: rest => map_upd_list (map_upd m k v) rest
  end.

Definition map_add (m1 m2 : A -> option B) v := match m1 v with Some v' => Some v' | None => m2 v end.

Definition empty_map (k : A) : option B := None.

Definition singleton v1 (v2 : B) (v : A) := if eq_dec v v1 then Some v2 else None.

Definition map_incl (a b : A -> option B) := forall v1 v2, a v1 = Some v2 -> b v1 = Some v2.

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
  destruct (m3 v1); auto.
Qed.

Instance fmap_PCM : PCM (A -> option B) := { join a b c :=
  forall v1 v2, c v1 = Some v2 <-> a v1 = Some v2 \/ b v1 = Some v2 }.
Proof.
  - intros.
    rewrite Hjoin; tauto.
  - intros.
    exists (fun v => match b v with Some v' => Some v' | None => d v end).
    assert (forall v v1 v2, b v = Some v1 -> d v = Some v2 -> v1 = v2) as Hbd.
    { intros ??? Hb Hd.
      specialize (Hjoin1 v v1).
      destruct Hjoin1 as (_ & Hc); lapply Hc; auto; intro Hc'.
      generalize (Hjoin2 v v1); intros (_ & He); lapply He; auto; intro He1.
      specialize (Hjoin2 v v2); destruct Hjoin2 as (_ & Hjoin2); lapply Hjoin2; auto; intro He2.
      rewrite He1 in He2; inv He2; auto. }
    split; intros; specialize (Hjoin1 v1 v2); specialize (Hjoin2 v1 v2).
    + destruct (b v1) eqn: Hb; split; auto; intros [|]; auto; try discriminate.
      exploit Hbd; eauto.
    + rewrite Hjoin2, Hjoin1.
      destruct (b v1) eqn: Hb; split; auto; intros [|]; auto.
      * specialize (Hbd _ _ _ Hb H); subst; auto.
      * destruct H; auto; discriminate.
Defined.

Lemma map_join_spec : forall m1 m2 m3, join m1 m2 m3 -> m3 = map_add m1 m2.
Proof.
  simpl; intros.
  extensionality x; unfold map_add.
  destruct (m1 x) eqn: Hm1.
  - rewrite H; auto.
  - destruct (m2 x) eqn: Hm2.
    + rewrite H; auto.
    + destruct (m3 x) eqn: Hm3; auto.
      rewrite H in Hm3; destruct Hm3 as [Hm3 | Hm3]; rewrite Hm3 in *; discriminate.
Qed.

Instance fmap_order : PCM_order map_incl.
Proof.
  constructor.
  - apply map_incl_refl.
  - apply map_incl_trans.
  - intros ??? Ha Hb; exists (map_add a b); split; simpl.
    + intros; unfold map_add; destruct (a v1) eqn: Hv1; split; auto; intros [|]; auto; try discriminate.
      specialize (Ha _ _ Hv1); specialize (Hb _ _ H); rewrite Ha in Hb; auto.
    + unfold map_add; intros ???.
      destruct (a v1) eqn: Hv1; auto.
      inv H; auto.
  - split; repeat intro; specialize (H v1 v2); rewrite H; auto.
  - split; auto; intros [|]; auto.
Defined.

Lemma map_upd_list_app : forall l1 l2 (m : A -> option B),
  map_upd_list m (l1 ++ l2) = map_upd_list (map_upd_list m l1) l2.
Proof.
  induction l1; auto; simpl; intros.
  destruct a; auto.
Qed.

Lemma map_upd_list_out : forall l (m : A -> option B) k,
  m k = None -> ~In k (map fst l) -> map_upd_list m l k = None.
Proof.
  induction l; auto; simpl; intros.
  destruct a; apply IHl.
  - unfold map_upd; if_tac; auto.
    subst; simpl in *; tauto.
  - tauto.
Qed.

End Maps.

Section ListMaps.

Context {A B : Type} {A_eq : EqDec A}.

Definition map_Znth i (L : A -> option (list B)) d k := option_map (fun v => Znth i v d) (L k).

Lemma map_Znth_single : forall i (k : A) (v : list B) d,
  map_Znth i (singleton k v) d = singleton k (Znth i v d).
Proof.
  intros; unfold map_Znth, singleton; extensionality.
  if_tac; auto.
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