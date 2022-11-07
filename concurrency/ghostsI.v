Require Import VST.veric.compcert_rmaps.
Require Export VST.concurrency.ghosts.
Require Import VST.concurrency.conclib.
Require Import VST.veric.bi.
Require Import VST.msl.sepalg.
Import List.

(* Lemmas about ghost state, proved with Iris bupd *)

#[export] Instance unfash_persistent P : Persistent (alg_seplog.unfash P).
Proof.
  change unfash with (@subtypes.unfash rmap _ _).
  constructor; intros ??; hnf.
  unfold bi_persistently; simpl.
  unfold unfash in *; simpl in *.
  rewrite level_core; auto.
Qed.

Section ghost.

Context {RA: Ghost}.

Lemma own_alloc_strong : forall P (a : G) (pp : preds), ghost_seplog.pred_infinite P -> valid a ->
  emp |-- (|==> EX g : own.gname, !!(P g) && own g a pp)%I.
Proof.
  exact own_alloc_strong.
Qed.

Lemma own_alloc : forall (a : G) (pp : preds), valid a -> emp%I |-- (|==> EX g : own.gname, own g a pp)%I.
Proof.
  exact own_alloc.
Qed.

Global Instance own_dealloc g a pp : Affine (own g a pp).
Proof.
  unfold Affine.
  apply own_dealloc.
Qed.

Lemma own_update : forall g a b pp, fp_update a b -> own g a pp |-- (|==> own g b pp)%I.
Proof.
  exact own_update.
Qed.

Lemma own_update_ND : forall g a B pp, fp_update_ND a B -> own g a pp |-- (|==> EX b : G, !! B b && own g b pp)%I.
Proof.
  exact own_update_ND.
Qed.

Lemma own_list_alloc : forall la lp, Forall valid la -> length lp = length la ->
  emp |-- (|==> (EX lg : _, !!(Zlength lg = Zlength la) &&
    iter_sepcon (fun '(g, a, p) => own g a p) (combine (combine lg la) lp)))%I.
Proof.
  exact own_list_alloc.
Qed.

Corollary own_list_alloc' : forall a pp i, 0 <= i -> valid a ->
  emp |-- (|==> (EX lg : _, !!(Zlength lg = i) && iter_sepcon (fun g => own g a pp) lg))%I.
Proof.
  exact own_list_alloc'.
Qed.

Lemma own_list_dealloc : forall {A} f (l : list A),
  (forall b, exists g a pp, f b |-- own g a pp) ->
  iter_sepcon f l |-- (emp)%I.
Proof.
  intros; apply own_list_dealloc; auto.
Qed.

Lemma own_list_dealloc' : forall {A} g a p (l : list A),
  iter_sepcon (fun x => own (g x) (a x) (p x)) l |-- (emp)%I.
Proof.
  intros; apply own_list_dealloc'.
Qed.

Lemma core_persistent : forall g a p, a = core a -> Persistent (own g a p).
Proof.
  intros; unfold Persistent.
  constructor.
  intros ??; unfold bi_persistently; simpl.
  apply own.own_core; auto.
Qed.

End ghost.

Lemma exclusive_update : forall {A} (v v' : A) p, excl p v |-- (|==> excl p v')%I.
Proof.
  intros; apply exclusive_update.
Qed.

Section Snapshot.

Context `{ORD : PCM_order}.

Lemma master_update : forall v v' p, ord v v' -> ghost_master Tsh v p |-- (|==> ghost_master Tsh v' p)%I.
Proof.
  exact master_update.
Qed.

Lemma make_snap : forall (sh : share) v p, ghost_master sh v p |-- (|==> ghost_snap v p * ghost_master sh v p)%I.
Proof.
  exact make_snap.
Qed.

Lemma ghost_snap_forget : forall v1 v2 p, ord v1 v2 -> ghost_snap v2 p |-- (|==> ghost_snap v1 p)%I.
Proof.
  exact ghost_snap_forget.
Qed.

Lemma ghost_snap_choose : forall v1 v2 p, ghost_snap v1 p * ghost_snap v2 p |-- (|==> ghost_snap v1 p)%I.
Proof.
  exact ghost_snap_choose.
Qed.

Lemma snap_master_update1 : forall v1 v2 p v', ord v2 v' ->
  ghost_snap v1 p * ghost_master1 v2 p |-- (|==> ghost_snap v' p * ghost_master1 v' p)%I.
Proof.
  exact snap_master_update1.
Qed.

Global Instance snap_persistent v p : Persistent (ghost_snap v p).
Proof.
  apply core_persistent; auto.
Qed.

End Snapshot.

Section Reference.

Context {P : Ghost}.

Lemma part_ref_update : forall g sh a r a' r'
  (Ha' : forall b, join a b r -> join a' b r' /\ (a = r -> a' = r')),
  ghost_part_ref sh a r g |-- (|==> ghost_part_ref sh a' r' g).
Proof.
  exact part_ref_update.
Qed.

Lemma ref_add : forall g sh a r b a' r'
  (Ha : join a b a') (Hr : join r b r'),
  ghost_part_ref sh a r g |-- (|==> ghost_part_ref sh a' r' g)%I.
Proof.
  exact ref_add.
Qed.

End Reference.

Section GVar.

Context {A : Type}.

Notation ghost_var := (@ghost_var A).

Lemma ghost_var_update : forall v p v', ghost_var Tsh v p |-- (|==> ghost_var Tsh v' p)%I.
Proof.
  exact ghost_var_update.
Qed.

Lemma ghost_var_update' : forall g (v1 v2 v : A), ghost_var gsh1 v1 g * ghost_var gsh2 v2 g |--
  |==> !!(v1 = v2) && (ghost_var gsh1 v g * ghost_var gsh2 v g).
Proof.
  exact ghost_var_update'.
Qed.

End GVar.

Section PVar.

Lemma snap_master_update' : forall (v1 v2 : nat) p v', (v2 <= v')%nat ->
  ghost_snap v1 p * ghost_master1 v2 p |-- (|==> ghost_snap v' p * ghost_master1 v' p)%I.
Proof.
  intros; apply snap_master_update1; auto.
Qed.

End PVar.

Section Reference.

Context {P : Ghost}.

Lemma ref_update : forall g a r a',
  ghost_part_ref Tsh a r g |-- (|==> ghost_part_ref Tsh a' a' g)%I.
Proof.
  exact ref_update.
Qed.

End Reference.

Section GHist.

(* Ghost histories in the style of Nanevsky *)
Context {hist_el : Type}.

Notation hist_part := (nat -> option hist_el).

Lemma hist_add : forall (sh : share) (h h' : hist_part) e p t' (Hfresh : h' t' = None),
  ghost_hist_ref sh h h' p |-- (|==> ghost_hist_ref sh (map_upd h t' e) (map_upd h' t' e) p)%I.
Proof.
  exact hist_add.
Qed.

Notation ghost_hist := (@ghost_hist hist_el).

Lemma hist_add' : forall sh h h' e p, sh <> Share.bot ->
  ghost_hist sh h p * ghost_ref h' p |-- (|==>
  ghost_hist sh (map_upd h (length h') e) p * ghost_ref (h' ++ [e]) p)%I.
Proof.
  exact hist_add'.
Qed.

End GHist.

(* speed up destructs of the form [% H] *)
#[export] Existing Instance class_instances.into_sep_and_persistent_l.

Require Import iris.algebra.gmap.

(* universe inconsistency, reflecting a real difference in expressive power
#[local] Program Instance RA_ghost (A : cmra) : Ghost := { G := cmra_car A; Join_G a b c := cmra_op A a b = c }.
*)

Section gmap_ghost.

Context {K} `{Countable K} {A : Ghost}.

Program Instance gmap_ghost : Ghost := { G := gmap K G; Join_G a b c := forall k, sepalg.join (a !! k) (b !! k) (c !! k);
  valid a := True%type }.
Next Obligation.
Proof.
  exists (fun m => gmap_fmap _ _ sepalg.core m); intros.
  - intros k.
    rewrite lookup_fmap.
    destruct (t !! k); constructor.
    apply core_unit.
  - exists (gmap_fmap _ _ sepalg.core c); intros k.
    rewrite !lookup_fmap.
    specialize (H0 k); inv H0; try constructor.
    + destruct (a !! k); constructor.
      apply core_duplicable.
    + eapply core_sub_join, join_core_sub, H4.
  - apply map_eq; intros k.
    rewrite !lookup_fmap.
    destruct (a !! k); auto; simpl.
    rewrite core_idem; auto.
Defined.
Next Obligation.
Proof.
  constructor; intros.
  - apply map_eq; intros k.
    specialize (H0 k); specialize (H1 k).
    inv H0; inv H1; auto; try congruence.
    rewrite <- H2 in H0; inv H0.
    rewrite <- H3 in H6; inv H6.
    f_equal; eapply join_eq; eauto.
  - exists (map_imap (fun k _ => projT1 (join_assoc (H0 k) (H1 k))) (b ∪ c)).
    split; intros k; pose proof (H0 k) as Hj1; pose proof (H1 k) as Hj2;
      rewrite map_lookup_imap lookup_union; destruct (join_assoc (H0 k) (H1 k)) as (? & ? & ?);
      destruct (b !! k) eqn: Hb; simpl; auto.
    + inv j; constructor; auto.
    + inv j; [|constructor].
      destruct (c !! k); constructor.
    + inv j; auto.
    + inv j; auto.
      destruct (c !! k); auto.
  - intros k; specialize (H0 k).
    apply sepalg.join_comm; auto.
  - apply map_eq; intros k.
    specialize (H0 k); specialize (H1 k).
    inv H0; inv H1; try congruence.
    rewrite <- H2 in H7; inv H7.
    rewrite <- H0 in H4; inv H4.
    f_equal; eapply join_positivity; eauto.
Qed.
Next Obligation.
Proof.
  auto.
Qed.

Context `{A_order : PCM_order(P := A)}.

Lemma map_included_option_ord : forall (a b : gmap K G), map_included ord a b -> forall k, option_ord(ord := ord) (a !! k) (b !! k).
Proof.
  intros.
  specialize (H0 k); destruct (a !! k), (b !! k); simpl; auto.
Qed.

#[export] Instance gmap_order : PCM_order (map_included ord).
Proof.
  constructor.
  - apply (map_included_preorder(M := gmap K)), _.
  - intros.
    pose proof (map_included_option_ord _ _ H0) as Ha.
    pose proof (map_included_option_ord _ _ H1) as Hb.
    exists (map_imap (fun k _ => proj1_sig (ord_lub(PCM_order := option_order(ORD := A_order)) _ _ _ (Ha k) (Hb k))) (map_union a b)).
    split; intros k; pose proof (H0 k) as Hj1; pose proof (H1 k) as Hj2;
      rewrite map_lookup_imap lookup_union; destruct (ord_lub _ _ _ (Ha k) (Hb k)) as (? & ? & ?); simpl;
      destruct (a !! k) eqn: Ha1; rewrite Ha1 in j |- *; simpl; auto.
    + destruct (b !! k) eqn: Hb1; rewrite Hb1 in j |- *; simpl; auto.
    + destruct (b !! k) eqn: Hb1; rewrite Hb1 in j |- *; simpl; auto; constructor.
    + destruct (b !! k) eqn: Hb1; rewrite Hb1 in j |- *;
        destruct x, (c !! k) eqn: Hc; rewrite Hc in o |- *; simpl; auto.
    + destruct (b !! k) eqn: Hb1; rewrite Hb1 in j |- *;
        destruct x, (c !! k) eqn: Hc; rewrite Hc in o |- *; simpl; auto.
  - split; intros k; specialize (H0 k); inv H0; simpl; auto.
    + destruct (b !! k) eqn: Hb; rewrite Hb; auto.
    + destruct (a !! k) eqn: Ha; rewrite Ha; simpl; auto.
      reflexivity.
    + apply join_ord in H4 as []; auto.
    + destruct (b !! k) eqn: Hb; rewrite Hb; simpl; auto.
      reflexivity.
    + destruct (a !! k) eqn: Ha; rewrite Ha; auto.
    + apply join_ord in H4 as []; auto.
  - intros ??? k.
    specialize (H0 k).
    destruct (b !! k) eqn: Hb; rewrite Hb in H0 |- *; [|constructor].
    destruct (a !! k) eqn: Ha; rewrite Ha in H0 |- *; [|contradiction].
    constructor; apply ord_join; auto.
Qed.


End gmap_ghost.
