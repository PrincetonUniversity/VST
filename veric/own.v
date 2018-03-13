Require Import VST.msl.log_normalize.
Require Import VST.msl.ghost.
Require Import VST.msl.ghost_seplog.
Require Export VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.

Import RML. Import R.
Local Open Scope pred.

Notation ghost_approx m := (ghost_fmap (approx (level m)) (approx (level m))).

(* Ghost state construction drawn from "Iris from the ground up", Jung et al. *)
Program Definition ghost_is {I} {RAs: I -> Ghost} g pds dom: pred rmap :=
  fun m => exists Hv, ghost_of m = ghost_approx m (GHOST _ _ g pds Hv dom).
Next Obligation.
  intros ???????? (? & Hg).
  rewrite (age1_ghost_of _ _ H), Hg.
  pose proof (age_level _ _ H).
  rewrite ghost_fmap_fmap, approx_oo_approx', approx'_oo_approx by omega; eauto.
Qed.

Definition Own {I} {RAs: I -> Ghost} g pds dom: pred rmap := allp noat && ghost_is g pds dom.

Lemma Own_valid: forall {I} {RAs: I -> Ghost} g pds dom,
  Own g pds dom |-- !!ghost.valid g.
Proof.
  intros.
  intros ??.
  destruct H as (? & ? & ?); auto.
Qed.

Lemma Own_op: forall {I} {RAs: I -> Ghost} a b c pdsa pdsb pdsc doma domb domc,
  join a b c -> join pdsa pdsb pdsc ->
  Own c pdsc domc = Own a pdsa doma * Own b pdsb domb.
Proof.
  intros; apply pred_ext.
  - intros w (Hno & ? & Hg).
    assert (ghost.valid a) as Hva by (eapply join_valid; eauto).
    assert (ghost.valid b) as Hvb by (eapply join_valid; eauto).
    destruct (make_rmap (resource_at w) (ghost_approx w (GHOST _ _ _ _ Hva doma)) (rmap_valid w) (level w))
      as (wa & Hla & Hra & Hga).
    { extensionality; apply resource_at_approx. }
    { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
    destruct (make_rmap (resource_at w) (ghost_approx w (GHOST _ _ _ _ Hvb domb)) (rmap_valid w) (level w))
      as (wb & Hlb & Hrb & Hgb).
    { extensionality; apply resource_at_approx. }
    { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
    exists wa, wb; split.
    + apply resource_at_join2; auto.
      * intro; rewrite Hra, Hrb.
        apply identity_unit', Hno.
      * rewrite Hg, Hga, Hgb.
        apply ghost_fmap_join; constructor; auto.
    + simpl; rewrite Hla, Hlb, Hra, Hrb, Hga, Hgb; simpl; eauto 6.
  - intros w (w1 & w2 & J & (Hnoa & ? & Hga) & (Hnob & ? & Hgb)).
    split.
    + intro l; apply (resource_at_join _ _ _ l) in J.
      simpl in *; rewrite <- (Hnoa _ _ _ J); auto.
    + destruct (join_level _ _ _ J) as [Hl1 Hl2].
      apply ghost_of_join in J.
      rewrite Hga, Hgb in J; inv J; repeat inj_pair_tac.
      assert (c1 = c) by (eapply join_eq; eauto); subst.
      simpl; rewrite <- H9.
      eexists; apply ghost_ext; auto.
      eapply join_eq; eauto.
      rewrite Hl1, Hl2.
      intros i n; specialize (H0 i n); inv H0; constructor.
      inv H6; auto.
  Unshelve.
  apply Hvc.
Qed.

Lemma preds_join_i: forall {I} a b, (forall i n x y, a i n = Some x -> b i n = Some y -> x = y) ->
  preds_join I a b (fun i n => match a i n with Some x => Some x | _ => b i n end).
Proof.
  intros.
  intros i n; specialize (H i n).
  destruct (a i n); [|constructor].
  destruct (b i n); constructor.
  specialize (H _ _ eq_refl eq_refl); subst; auto.
Qed.

Lemma ghost_joins_approx: forall n a c,
  joins (ghost_fmap (approx n) (approx n) a) (ghost_fmap (approx n) (approx n) c) ->
  exists c', joins (ghost_fmap (approx (S n)) (approx (S n)) a) (ghost_fmap (approx (S n)) (approx (S n)) c') /\
    forall b, joins b (ghost_fmap (approx (S n)) (approx (S n)) c') ->
      joins (ghost_fmap (approx n) (approx n) b) (ghost_fmap (approx n) (approx n) c).
Proof.
  intros.
  destruct a as [?? ga pdsa], c as [?? gc pdsc], H as [? H]; inv H; repeat inj_pair_tac.
  assert (forall i n pp, match pdsa i n, pdsc i n with Some x, Some _ => Some x | _, _ => pdsc i n end = Some pp ->
    exists a, finmap_get (gc i) n = Some a) as dom'.
  { intros; destruct (pdsa i n0) eqn: Hi; eauto.
    destruct (pdsc i n0) eqn: Hi'; inv H; eauto. }
  eexists (GHOST _ _ gc _ Hv0 dom'); split.
  - eexists; constructor; eauto.
    apply preds_join_i; intros.
    destruct (pdsa i n0); inv H.
    destruct (pdsc i n0); inv H0; auto.
  - intros [?? gb pdsb] [? J]; inv J; repeat inj_pair_tac.
    eexists; constructor; eauto.
    apply preds_join_i; intros.
    specialize (H10 i n0); specialize (H11 i n0); simpl in *.
    destruct (pdsb i n0); inv H.
    destruct (pdsc i n0); inv H0.
    destruct (pdsa i n0); inv H10; inv H11.
    + inv H2; inv H4.
      rewrite <- H, preds_fmap_fmap, approx_oo_approx', approx'_oo_approx; auto.
    + inv H3.
      rewrite preds_fmap_fmap, approx_oo_approx', approx'_oo_approx; auto.
  Unshelve.
  apply Hvc.
  simpl; intros.
  specialize (H9 i); apply finmap_get_join with (i0 := n0) in H9.
  destruct (finmap_get (c0 i) n0); eauto.
  destruct (pdsa i n0) eqn: Hi; inv H.
  destruct (dom _ _ _ Hi) as [? Hget]; rewrite Hget in H9.
  destruct (finmap_get (gc i) n0); inv H9.
  destruct (pdsc i n0) eqn: Hi'; inv H1.
  destruct (dom0 _ _ _ Hi') as [? Hget]; rewrite Hget in H9.
  destruct (finmap_get (ga i) n0); inv H9.
  apply Hvc0.
  simpl; intros.
  specialize (H8 i); apply finmap_get_join with (i0 := n0) in H8.
  destruct (finmap_get (c1 i) n0); eauto.
  destruct (pdsb i n0) eqn: Hi; inv H.
  destruct (dom1 _ _ _ Hi) as [? Hget]; rewrite Hget in H8.
  destruct (finmap_get (gc i) n0); inv H8.
  destruct (pdsc i n0) eqn: Hi'; inv H1.
  destruct (dom0 _ _ _ Hi') as [? Hget]; rewrite Hget in H8.
  destruct (finmap_get (gb i) n0); inv H8.
Qed.

Program Definition bupd (P: pred rmap): pred rmap :=
  fun m => forall c, joins (ghost_of m) (ghost_approx m c) ->
    exists b, joins b (ghost_approx m c) /\
    exists m', level m' = level m /\ resource_at m' = resource_at m /\ ghost_of m' = b /\ P m'.
Next Obligation.
Proof.
  repeat intro.
  rewrite (age1_ghost_of _ _ H) in H1.
  rewrite <- ghost_of_approx in H0.
  destruct (ghost_joins_approx _ _ _ H1) as (c0 & J0 & Hc0).
  rewrite <- (age_level _ _ H) in *.
  specialize (H0 _ J0); destruct H0 as (b & J & Hrb).
  pose proof (age_level _ _ H).
  exists (ghost_approx a' b); split; auto.
  destruct Hrb as (m' & Hl' & Hr' & Hg' & HP).
  destruct (levelS_age m' (level a')) as (m'' & Hage' & Hl'').
  { congruence. }
  exists m''; repeat split; auto.
  + extensionality l.
    erewrite (age1_resource_at _ _ H l) by (symmetry; apply resource_at_approx).
    erewrite (age1_resource_at _ _ Hage' l) by (symmetry; apply resource_at_approx).
    congruence.
  + rewrite (age1_ghost_of _ _ Hage').
    rewrite Hg', <- Hl''; auto.
  + eapply (proj2_sig P); eauto.
Qed.

Lemma bupd_intro: forall P, P |-- bupd P.
Proof.
  repeat intro; eauto 7.
Qed.

Lemma bupd_mono: forall P Q, P |-- Q -> bupd P |-- bupd Q.
Proof.
  repeat intro.
  simpl in *.
  destruct (H0 _ H1) as (b & ? & m' & ? & ? & ? & ?).
  exists b; split; auto.
  exists m'; repeat split; auto.
Qed.

Lemma bupd_frame_r: forall P Q, bupd P * Q |-- bupd (P * Q).
Proof.
  repeat intro.
  destruct H as (w1 & w2 & J & HP & HQ).
  destruct (join_level _ _ _ J) as [Hl1 Hl2].
  pose proof (ghost_of_join _ _ _ J) as Jg.
  destruct H0 as [? J'].
  destruct (join_assoc Jg J') as (c' & J1 & J2).
  erewrite <- (ghost_same_level_gen (level a) (ghost_of w2) c c') in J2, J1
    by (rewrite <- Hl2 at 1 2; rewrite ghost_of_approx; auto).
  destruct (HP c') as (? & [? J1'] & w1' & ? & Hr' & ? & HP'); subst.
  { rewrite Hl1; eauto. }
  rewrite Hl1 in J1'; destruct (join_assoc (join_comm J1) (join_comm J1')) as (w' & ? & ?).
  exists w'; split; [eexists; apply join_comm; eauto|].
  destruct (make_rmap _ w' (rmap_valid a) (level a)) as (m' & ? & Hr'' & ?); subst.
  { extensionality l; apply resource_at_approx. }
  { eapply ghost_same_level_gen.
    rewrite <- (ghost_of_approx w2), <- (ghost_of_approx w1'), H, Hl1, Hl2 in H0.
    apply join_comm; eauto. }
  exists m'; repeat split; auto.
  exists w1', w2; repeat split; auto.
  apply resource_at_join2; auto; try omega.
  intro; rewrite Hr', Hr''.
  apply resource_at_join; auto.
Qed.

Lemma bupd_frame_l: forall P Q, P * bupd Q |-- bupd (P * Q).
Proof.
  intros; rewrite sepcon_comm, (sepcon_comm P Q); apply bupd_frame_r.
Qed.

Lemma bupd_trans: forall P, bupd (bupd P) |-- bupd P.
Proof.
  repeat intro.
  destruct (H _ H0) as (b & J & a' & Hl & Hr & ? & Ha'); subst.
  rewrite <- Hl in J; destruct (Ha' _ J) as (b' & ? & Hm').
  rewrite <- Hl, <- Hr; eauto.
Qed.

Definition ghost_fp_update_ND a B :=
  forall n c, joins (ghost_fmap (approx n) (approx n) a) c ->
    exists b, B b /\ joins (ghost_fmap (approx n) (approx n) b) c.

Lemma Own_update_ND: forall {I} {RAs: I -> Ghost} a pds Hv dom B,
  ghost_fp_update_ND (GHOST _ _ a pds Hv dom) B ->
  Own a pds dom |-- bupd (EX b : _, EX pdsb : _, EX Hvb : _, EX domb : _,
    !!(B (GHOST _ _ b pdsb Hvb domb)) && Own b pdsb domb).
Proof.
  repeat intro.
  destruct H0 as (Hno & Hv' & Hg).
  rewrite Hg in H1.
  destruct H1 as [? J].
  replace Hv' with Hv in J by apply proof_irr.
  destruct (H (level a0) (ghost_approx a0 c)) as (g' & ? & J').
  { eexists; eauto. }
  exists (ghost_fmap (approx (level a0)) (approx (level a0)) g'); split; auto.
  destruct (make_rmap (resource_at a0)
    (ghost_fmap (approx (level a0)) (approx (level a0)) g') (rmap_valid a0) (level a0))
    as (m' & Hl & Hr & Hg').
  { extensionality; apply resource_at_approx. }
  { rewrite ghost_fmap_fmap, approx_oo_approx; auto. }
  exists m'; repeat split; auto.
  destruct g' as [?? b pdsb Hvb domb].
  destruct c; inv J; repeat inj_pair_tac.
  destruct J' as [? J']; inv J'; repeat inj_pair_tac; subst.
  exists b, pdsb, Hvb, domb; repeat split; auto.
  - simpl in *; intro; rewrite Hr; auto.
  - simpl; rewrite Hg', Hl; simpl; eauto.
Qed.

Definition ghost_fp_update (a b : ghost) :=
  forall n c, joins (ghost_fmap (approx n) (approx n) a) c ->
               joins (ghost_fmap (approx n) (approx n) b) c.

Instance ghost_fp_update_preorder: RelationClasses.PreOrder ghost_fp_update.
Proof.
  split; repeat intro; auto.
Qed.

Lemma ghost_fp_update_approx: forall a b n, ghost_fp_update a b ->
  ghost_fp_update (ghost_fmap (approx n) (approx n) a) (ghost_fmap (approx n) (approx n) b).
Proof.
  intros; intros m c J.
  rewrite ghost_fmap_fmap in *.
  replace (approx m oo approx n) with (approx (min m n)) in *.
  replace (approx n oo approx m) with (approx (min m n)) in *.
  auto.
  { destruct (Min.min_spec m n) as [[? ->] | [? ->]];
      [rewrite approx'_oo_approx | rewrite approx_oo_approx']; auto; omega. }
  { destruct (Min.min_spec m n) as [[? ->] | [? ->]];
      [rewrite approx_oo_approx' | rewrite approx'_oo_approx]; auto; omega. }
Qed.

Lemma Own_update: forall {I} {RAs: I -> Ghost} a pds Hv dom b pdsb Hvb domb,
  ghost_fp_update (GHOST _ _ a pds Hv dom) (GHOST _ _ b pdsb Hvb domb) ->
  Own a pds dom |-- bupd (Own b pdsb domb).
Proof.
  intros; eapply derives_trans.
  - eapply (Own_update_ND _ _ _ _ (Ensembles.Singleton _ _)).
    repeat intro.
    eexists; split; [constructor|].
    apply H; eauto.
  - apply bupd_mono.
    repeat (apply exp_left; intro).
    apply prop_andp_left; intro X; inv X; repeat inj_pair_tac.
    replace x2 with domb by apply proof_irr; auto.
Qed.

Lemma Own_unit: emp |-- EX a : _, !!(identity a) && match a with GHOST _ _ a pds _ dom =>
  Own a pds dom end.
Proof.
  intros w ?; simpl in *.
  exists (ghost_of w); destruct (ghost_of w) eqn: Hw; split; [|split].
  - rewrite <- Hw; apply ghost_of_identity; auto.
  - intro; apply resource_at_identity; auto.
  - eexists; rewrite <- Hw.
    rewrite ghost_of_approx; auto.
Qed.

Definition gname := {I : Type & I * nat}%type.

Definition singleton {A} k (x : A) : finmap A := repeat None k ++ Some x :: nil.

Lemma singleton_get: forall {A} k (x : A) j,
  finmap_get (singleton k x) j = if eq_dec j k then Some x else None.
Proof.
  intros; unfold finmap_get, singleton.
  destruct (eq_dec j k).
  - subst; rewrite app_nth2; rewrite repeat_length; [|omega].
    rewrite minus_diag; auto.
  - destruct (lt_dec j k).
    + rewrite app_nth1 by (rewrite repeat_length; auto).
      apply nth_repeat.
    + rewrite app_nth2; rewrite repeat_length; [|omega].
      destruct (j - k)%nat eqn: Hd; [omega|].
      simpl; apply nth_nil.
Qed.

Program Definition single_ghost {I} {_ : EqDec I} {RAs} {RA} n {H: RAs (fst n) = RA} (a: @G RA) :
  @G Global_Ghost := fun j => if eq_dec j (fst n) then singleton (snd n) _ else nil.
Next Obligation.
Proof.
  intros; subst; auto.
Defined.

Definition single_pred {I} {_ : EqDec I} (n: I * nat) (pp: preds) :=
  fun j m => if eq_dec j (fst n) then if eq_dec m (snd n) then Some pp else None else None.

Lemma single_dom {I} {_ : EqDec I} {RAs} {RA} n (H: RAs (fst n) = RA) (a: @G RA) pp :
  forall i m p, single_pred n pp i m = Some p ->
  exists x, finmap_get (single_ghost(H := H) n a i) m = Some x.
Proof.
  unfold single_pred, single_ghost; intros.
  destruct (eq_dec _ _); [|discriminate].
  rewrite singleton_get.
  if_tac; inv H0; eauto.
Qed.

Definition own {RA: Ghost} (n: gname) (a: G) (pp: preds) :=
  match n with existT A n =>
    EX _ : EqDec A, EX RAs : _, EX H : RAs (fst n) = RA, Own _ _ (single_dom n H a pp) end.

(* Because the type of the ghost state is existentially quantified in the rmap, inG has to be a
   state predicate instead of a pure assertion. *)
Program Definition inG (RA: Ghost): pred rmap :=
  (fun m => match ghost_of m with GHOST A RAs g _ _ _ =>
    exists A_eq : EqDec A, exists inG : {i | RAs i = RA}, True end) && emp.
Next Obligation.
  repeat intro.
  subst filtered_var program_branch_0; simpl in *.
  rewrite (age1_ghost_of _ _ H).
  destruct (ghost_of a) eqn: Ha; auto.
Qed.

Lemma inG_emp: forall RA, inG RA |-- emp.
Proof.
  intro; apply andp_left2; auto.
Qed.

Lemma andp_emp_derives_dup : forall P, P && emp |-- P && emp * (P && emp).
Proof.
  intros ???.
  exists a; exists a; split; auto.
  apply sepalg.identity_unit'; destruct H; auto.
Qed.

Corollary andp_emp_dup : forall P, P && emp = (P && emp) * (P && emp).
Proof.
  intro; apply pred_ext.
  - apply andp_emp_derives_dup.
  - apply andp_right.
    + eapply derives_trans; [apply sepcon_derives, andp_left2, derives_refl; apply andp_left1, derives_refl |].
      rewrite sepcon_emp; auto.
    + eapply derives_trans; [apply sepcon_derives; apply andp_left2, derives_refl |].
      rewrite sepcon_emp; auto.
Qed.

Lemma inG_dup: forall RA, inG RA |-- inG RA * inG RA.
Proof.
  intro; setoid_rewrite <- andp_emp_dup; auto.
Qed.

Lemma skipn_all: forall {A} (n : nat) (l : list A), (length l <= n)%nat -> skipn n l = nil.
Proof.
  induction n; destruct l; auto; simpl; intros; try omega.
  apply IHn; omega.
Qed.

Opaque skipn.

Lemma join_fresh: forall {A} {J: Join A} (m : finmap A) v,
  join (singleton (fresh m) v) m (finmap_set m (fresh m) v).
Proof.
  intros; unfold singleton, finmap_set, fresh; simpl.
  rewrite firstn_all, minus_diag, skipn_all by omega; simpl.
  induction m; simpl; constructor; auto.
  constructor.
Qed.


Lemma single_valid: forall {I} {I_eq : EqDec I} {RAs: I -> Ghost} {RA} n (H: RAs (fst n) = RA)
  (a: @G RA), ghost.valid a -> ghost.valid (single_ghost(H := H) n a).
Proof.
  unfold single_ghost; repeat intro.
  destruct (eq_dec i (fst n)); [|rewrite finmap_get_empty in H1; discriminate].
  rewrite singleton_get in H1.
  destruct (eq_dec i0 (snd n)); inv H1; auto.
Qed.

Lemma ghost_alloc: forall {RA: Ghost} a pp,
  ghost.valid a ->
  inG RA |-- bupd (EX g: gname, own g a pp).
Proof.
  repeat intro; simpl in *.
  destruct H1; inv H1.
  rewrite <- H2 in H0.
  destruct H0 as [(? & [i e] & _) Hemp].
  eexists (ghost_approx (level a0) (GHOST _ RA0 (fun j => match eq_dec j i with
    | left H => singleton (fresh (b j)) ((fun _ _ => _) e H) | _ => nil end)
    (fun j n => if eq_dec j i then if eq_dec n (fresh (b j)) then Some pp
                 else None else None) _ _)).
  set (g' := ghost_approx _ _).
  split.
  - eexists; constructor.
    + instantiate (1 := fun j => if eq_dec j i then _ else _).
      hnf; intro j.
      destruct (eq_dec _ _); [|constructor].
      apply join_fresh.
    + instantiate (1 := fun j n => if eq_dec j i then if eq_dec n (fresh (b j)) then _ else _ else _).
      intros j n.
      destruct (eq_dec _ _); [|constructor].
      destruct (eq_dec _ _); [|constructor].
      assert (pdsb j n = None) as ->; [|constructor].
      destruct (pdsb j n) eqn: Hj; auto.
      destruct (domb _ _ _ Hj) as [? Hget]; subst j n.
      rewrite fresh_spec in Hget; discriminate.
  - destruct (make_rmap (resource_at a0) g' (rmap_valid a0) (level a0)) as (m' & Hl & Hr & Hg).
    { extensionality; apply resource_at_approx. }
    { subst g'; rewrite ghost_fmap_fmap, !approx_oo_approx; auto. }
    exists m'; repeat split; auto.
    exists (existT _ A (i, fresh (b i))).
    exists _, _, e; split; simpl.
    + intro; rewrite Hr; apply resource_at_identity; auto.
    + rewrite Hl, Hg; subst g'.
      eexists; apply ghost_ext.
      * extensionality j.
        unfold single_ghost; simpl.
        destruct (eq_dec _ _); auto.
        rewrite e0; auto.
      * extensionality j n.
        unfold single_pred; simpl.
        destruct (eq_dec _ _); subst; auto.
  Unshelve.
  { repeat intro.
    destruct (eq_dec i0 i); [|rewrite finmap_get_empty in H0; discriminate].
    rewrite singleton_get in H0.
    destruct (eq_dec i1 (fresh _)); inv H0; auto. }
  { simpl; intros.
    destruct (eq_dec _ _); [|discriminate].
    rewrite singleton_get.
    destruct (eq_dec _ _); inv H0; eauto. }
  { repeat intro.
    clear H3; specialize (Hvb i0).
    destruct (eq_dec i0 i); eauto.
    rewrite finmap_get_set in H0.
    destruct (eq_dec i1 (fresh _)); inv H0; eauto. }
  { simpl; intros.
    destruct (eq_dec _ _); [|eauto].
    rewrite finmap_get_set.
    destruct (eq_dec _ _); eauto. }
  { apply single_valid; auto. }
Qed.

Lemma singleton_join: forall {A} {J: Join A} a b c k,
  join (singleton k a) (singleton k b) (singleton k c) <-> join a b c.
Proof.
  unfold singleton; induction k; simpl.
  - split.
    + inversion 1; subst.
      inv H3; auto.
    + repeat constructor; auto.
  - rewrite <- IHk.
    split; [inversion 1 | repeat constructor]; auto.
Qed.

Lemma single_ghost_join: forall I (I_eq : EqDec I) (RAs: I -> Ghost) RA n
  (H : RAs (fst n) = RA) a b c, join a b c ->
  join (single_ghost(H := H) n a) (single_ghost(H := H) n b) (single_ghost(H := H) n c).
Proof.
  repeat intro; unfold single_ghost.
  destruct (eq_dec _ _); [|constructor].
  apply singleton_join; subst; auto.
Qed.

Lemma preds_join_refl: forall I a, preds_join I a a a.
Proof.
  repeat intro.
  destruct (a _ _); constructor; auto.
Qed.

Lemma eq_dec_irr: forall {A} (e1: EqDec A) (e2: EqDec A), e1 = e2.
Proof.
  intros; extensionality a b.
  destruct (e1 a b), (e2 a b); try contradiction; f_equal; apply proof_irr.
Qed.

Lemma ghost_op: forall {RA: Ghost} g (a1 a2 a3: G) pp,
  join a1 a2 a3 ->
  own g a3 pp = own g a1 pp * own g a2 pp.
Proof.
  intros; apply pred_ext.
  - destruct g.
    repeat (apply exp_left; intro).
    erewrite Own_op by ((apply single_ghost_join, H) || apply preds_join_refl).
    apply sepcon_derives; repeat eapply exp_right; eauto.
  - destruct g.
    intros ? (w1 & w2 & J & (? & ? & ? & ? & ? & Hg1) & (? & ? & ? & ? & ? & Hg2)).
    pose proof (ghost_of_join _ _ _ J) as Jg.
    rewrite Hg1, Hg2 in Jg; inversion Jg.
    repeat inj_pair_tac.
    do 3 eexists.
    erewrite Own_op by ((apply single_ghost_join, H) || apply preds_join_refl).
    exists w1, w2; repeat split; auto.
    + replace x4 with x0 by apply eq_dec_irr.
      eexists; apply Hg1.
    + replace x2 with x6 by apply proof_irr.
      eexists; apply Hg2.
Qed.

Lemma singleton_join_inv: forall {A} {J: Join A} k a b c,
  join (singleton k a) (singleton k b) c -> exists c', join a b c' /\ c = singleton k c'.
Proof.
  unfold singleton; induction k; inversion 1; subst.
  - assert (m3 = nil) by (inv H6; auto).
    inv H5; eauto.
  - assert (a3 = None) by (inv H5; auto); subst.
    edestruct IHk as (? & ? & ?); eauto; subst; eauto.
Qed.

Lemma ghost_valid_2: forall {RA: Ghost} g a1 a2 pp,
  own g a1 pp * own g a2 pp |-- !!ghost.valid_2 a1 a2.
Proof.
  intros.
  destruct g as [? [i]].
  intros w (? & ? & J%ghost_of_join & (? & ? & ? & ? & ? & Hg1) & (? & ? & e1 & ? & ? & Hg2)).
  rewrite Hg1, Hg2 in J.
  inv J; repeat inj_pair_tac.
  specialize (H3 i); apply finmap_get_join with (i0 := n) in H3.
  clear H9; specialize (Hvc i n).
  unfold single_ghost in H3; simpl in H3.
  destruct (eq_dec i i); [|contradiction].
  rewrite singleton_get in H3.
  destruct (eq_dec n n); [|contradiction].
  destruct (eq_dec i i); [|contradiction].
  rewrite singleton_get in H3.
  destruct (eq_dec n n); [|contradiction].
  destruct (finmap_get (c0 i) n); [|contradiction].
  subst; simpl in *.
  eexists; split; eauto.
  rewrite (UIP_refl _ _ e), (UIP_refl _ _ e1), (UIP_refl _ _ e2) in H3; auto.
Qed.

Corollary ghost_valid: forall {RA: Ghost} g a pp,
  own g a pp |-- !!ghost.valid a.
Proof.
  intros.
  rewrite <- (normalize.andp_TT (!!_)).
  erewrite ghost_op by apply core_unit.
  eapply derives_trans; [apply andp_right, derives_refl; apply ghost_valid_2|].
  apply prop_andp_left; intros (? & J & ?); apply prop_andp_right; auto.
  apply core_identity in J; subst; auto.
Qed.

Lemma singleton_join_some: forall {A} {J: Join A} k (a b c: A) m
  (Hget: finmap_get m k = Some b) (Hjoin: join a b c),
  join (singleton k a) m (finmap_set m k c).
Proof.
  unfold finmap_get; induction k; intros.
  - destruct m; [rewrite nth_nil in Hget; discriminate|].
    simpl in *; subst; repeat constructor; auto.
  - destruct m; [discriminate|].
    repeat constructor; eapply IHk; eauto.
Qed.

Lemma singleton_join_none: forall {A} {J: Join A} k (a: A) m (Hget: finmap_get m k = None),
  join (singleton k a) m (finmap_set m k a).
Proof.
  unfold finmap_get; induction k; intros.
  - destruct m; simpl in *; subst; repeat constructor.
  - destruct m; repeat constructor; eapply IHk; eauto.
Qed.

Lemma ghost_update_ND: forall {RA: Ghost} g (a: G) B pp,
  fp_update_ND a B -> own g a pp |-- bupd (EX b : _, !!(B b) && own g b pp).
Proof.
  intros.
  eapply derives_trans; [apply andp_right, derives_refl; apply ghost_valid|].
  apply prop_andp_left; intro Hva.
  destruct g as [? [i n]].
  repeat (apply exp_left; intro).
  eapply derives_trans.
  - apply Own_update_ND with (Hv := single_valid (i, n) x2 a Hva)
      (B0 := fun g => exists b (Hv: ghost.valid b), B b /\ g = GHOST _ _ _ _ (single_valid (i, n) x2 b Hv) (single_dom (i, n) x2 b pp)).
    intros ?? [? J].
    inv J; repeat inj_pair_tac.
    pose proof (H6 i) as J; specialize (Hvc i n).
    apply finmap_get_join with (i0 := n) in J.
    unfold single_ghost in J; simpl in J.
    destruct (eq_dec i i); [|contradiction].
    rewrite singleton_get, if_true in J by auto.
    destruct (finmap_get (b0 i) n) eqn: Hb.
    + destruct (finmap_get (c1 i) n); [|contradiction].
      rewrite (UIP_refl _ _ e) in J.
      lapply (H g); [|eexists; eauto].
      intros (b & ? & g' & J' & Hvg'); simpl in *.
      pose proof (singleton_join_some _ _ _ _ _ Hb J').
      pose proof (join_valid _ _ _ J' Hvg') as Hvb'.
      eexists; split; [exists b, Hvb'; eauto|].
      eexists; constructor; eauto; simpl.
      instantiate (1 := fun j => match eq_dec j i with
        left H => finmap_set (b0 j) n (eq_rect_r (fun j => @G (x1 j)) g' H) | _ => b0 j end).
      unfold single_ghost; simpl.
      intro j; destruct (eq_dec j i); [|constructor].
      subst; auto.
    + lapply (H (core a)).
      intros (b & ? & ? & J' & ?).
      apply join_valid in J'; auto.
      eexists; split; [exists b, J'; eauto|].
      eexists; constructor; eauto; simpl.
      instantiate (1 := fun j => match eq_dec j i with
        left H => _ | _ => b0 j end).
      unfold single_ghost; simpl.
      intro j; destruct (eq_dec j i); [|constructor].
      apply singleton_join_none; subst; auto.
      { eexists; split; eauto; apply join_comm, core_unit. }
  - apply bupd_mono.
    repeat (apply exp_left; intro); apply prop_andp_left; intros (? & ? & ? & Hg).
    inv Hg; repeat inj_pair_tac.
    eapply exp_right, andp_right; [repeat intro; simpl; eauto|].
    repeat eapply exp_right.
    replace x6 with (single_dom (i, n) (eq_refl _) x7 pp) by apply proof_irr; auto.
  Unshelve.
  { intros j m ??; specialize (Hvb j m).
    destruct (eq_dec j i); auto.
    rewrite finmap_get_set in H2.
    destruct (eq_dec m n); inv H2; auto. }
  { intros j m ??; specialize (H7 j m); unfold single_pred in H7; simpl in *.
    destruct (eq_dec _ _); [|eapply domb; inv H7; rewrite H2 in *; eauto].
    rewrite finmap_get_set; destruct (eq_dec _ _); eauto.
    eapply domb; inv H7; rewrite H2 in *; eauto. }
  { intros j m ??; specialize (Hvb j m).
    destruct (eq_dec j i); auto.
    rewrite finmap_get_set in H2.
    destruct (eq_dec m n); inv H2; auto. }
  { intros j m ??; specialize (H7 j m); unfold single_pred in H7; simpl in *.
    destruct (eq_dec _ _); [|eapply domb; inv H7; rewrite H2 in *; eauto].
    rewrite finmap_get_set; destruct (eq_dec _ _); eauto.
    eapply domb; inv H7; rewrite H2 in *; eauto. }
Qed.

Lemma ghost_update: forall {RA: Ghost} g (a b: G) pp,
  fp_update a b -> own g a pp |-- bupd (own g b pp).
Proof.
  intros; eapply derives_trans.
  - apply (ghost_update_ND g a (Ensembles.Singleton _ b)).
    intros ? J; destruct (H _ J).
    do 2 eexists; [constructor | eauto].
  - apply bupd_mono.
    apply exp_left; intro; apply prop_andp_left; intro X; inv X; auto.
Qed.
