Require Export veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.slice.
Require Import veric.Clight_lemmas.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.shares.
Require Import veric.address_conflict.

Import RML. Import R. 
Open Local Scope pred.

Lemma empty_rmap_valid:
  forall ephi, 
   identity ephi ->
    R.valid (resource_at ephi).
Proof.
intros.
unfold R.valid.
replace (res_option oo resource_at ephi) with 
            (fun l : address => @None (pshare * kind)).
apply CompCert_AV.valid_empty.
extensionality l.
unfold compose; simpl.
destruct (resource_at_empty H l) as [?|[? [? ?]]]; rewrite H0; simpl; auto.
Qed.

Program Definition kind_at (k: kind) (l: address) : pred rmap := 
   fun m => exists rsh, exists sh, exists pp, m @ l = YES rsh sh k pp.
 Next Obligation.
   try intro; intros.
   destruct H0 as [rsh [sh [pp ?]]].
   generalize (eq_sym (resource_at_approx a l)); intro.
   generalize (age1_resource_at a a'  H l (a@l) H1); intro.
   rewrite H0 in H2. simpl in H2. eauto.
 Qed.

Definition spec : Type :=  forall (rsh: Share.t) (sh: Share.t) (l: AV.address), pred rmap.

Program Definition yesat_raw (pp: preds) (k: kind) 
                           (rsh: share) (sh: pshare) (l: address) : pred rmap :=
   fun phi => phi @ l = YES rsh sh k (preds_fmap (approx (level phi)) pp).
  Next Obligation.
   try intro; intros.
   apply (age1_resource_at a a' H l (YES rsh sh k pp) H0).
  Qed.

Obligation Tactic := idtac.

Program Definition yesat (pp: preds) (k: kind) : spec :=
 fun rsh (sh: Share.t) (l: AV.address) (m: rmap) =>
  exists p, yesat_raw pp k rsh (mk_lifted sh p) l m.
  Next Obligation.
    intros; intro; intros.
    destruct H0 as [p ?]; exists p.
    apply pred_hereditary with a; auto.
  Qed.

Program Definition pureat (pp: preds) (k: kind) (l: AV.address): pred rmap :=
       fun phi => phi @ l = PURE k (preds_fmap (approx (level phi)) pp).
  Next Obligation.
    intros; intro; intros.
   apply (age1_resource_at a a' H l (PURE k pp) H0).
  Qed.

Ltac do_map_arg :=
match goal with |- ?a = ?b =>
  match a with context [map ?x _] =>
    match b with context [map ?y _] => replace y with x; auto end end end.


Lemma yesat_raw_eq_aux: 
  forall pp k rsh sh l, 
    hereditary age
    (fun phi : rmap =>
     resource_fmap (approx (level phi)) (phi @ l) =
     resource_fmap (approx (level phi)) (YES rsh sh k pp)).
Proof.
 intros.
  intro; intros.
  generalize (resource_at_approx a l); intro.
  generalize (resource_at_approx a' l); intro.
  rewrite H2.
  rewrite H1 in H0.
  apply (age1_resource_at a a'  H); auto.
Qed.
   
Lemma yesat_raw_eq: yesat_raw = 
  fun pp k rsh sh l =>
  ((exist (hereditary age)
   (fun phi => 
   resource_fmap (approx (level phi)) (phi @ l) = 
   resource_fmap (approx (level phi)) (YES rsh sh k pp)) 
   (yesat_raw_eq_aux pp k rsh sh l)) : pred rmap).
Proof.
unfold yesat_raw.
extensionality pp k; extensionality rsh sh l.
apply exist_ext.
extensionality phi.
apply prop_ext; split; intros.
rewrite H.
simpl.
f_equal.
rewrite preds_fmap_fmap.
rewrite approx_oo_approx.
auto.
simpl in H.
revert H; case_eq (phi @ l); simpl; intros; inv H0.
revert H5; destruct p0; destruct pp; simpl; intros; auto; inv H5.
clear - H.
repeat f_equal.
revert H; unfold resource_at.  rewrite rmap_level_eq.
case_eq (unsquash phi); simpl; intros.
destruct r as [f v]; simpl in *.
assert (R.valid (fun l' => if eq_dec l' l 
       then YES rsh sh k (SomeP A0 (approx n oo p)) else f l')).
clear - v H0.
unfold R.valid, compose, CompCert_AV.valid.
intros b ofs.
destruct l as [bl zl].
case (eq_dec (b,ofs) (bl,zl)); simpl; intros; auto.
symmetry in e; inv e.
generalize (v b ofs); unfold compose; intros. rewrite H0 in H. simpl in H.
destruct k; auto.
intros; rewrite if_false; auto.
intro.  inversion H2. omega.
destruct H as [n' [? ?]]; exists n'; split; auto.
rewrite if_false. auto. intro. inversion H2; omega.
generalize (v b ofs); unfold compose; intros.
destruct (f (b,ofs)); simpl in *; auto.
destruct k0; simpl in *; auto.
intros. spec H i H1.
case (eq_dec (b,ofs+i) (bl,zl)); intros.
simpl. rewrite e in H; rewrite H0 in H; inv H; auto.
auto.
destruct H as [n' [? ?]]; exists n'; split; auto.
case (eq_dec (b,ofs-z) (bl,zl)); intros; auto.
rewrite e in H1; rewrite H0 in H1; auto.
(**  end of R.valid proof **)
set (phi' := ((exist (fun m : AV.address -> resource => R.valid m) _ H1): rmap')).
assert (phi = squash (n,phi')).
apply unsquash_inj.
replace (unsquash phi) with (unsquash (squash (unsquash phi))).
2: rewrite squash_unsquash; auto.
rewrite H.
do 2 rewrite unsquash_squash.
f_equal.
unfold phi'.
clear - H0.
simpl.
apply exist_ext.
unfold compose.
extensionality x.
if_tac; auto.
subst.
rewrite H0.
simpl.
do 2 apply f_equal.
transitivity ((approx n oo approx n) oo p).
rewrite approx_oo_approx; auto.
auto.
subst phi.
unfold phi' in H.
rewrite unsquash_squash in H.
injection H; clear H; intros.
generalize (equal_f H l); intro.
rewrite H0 in H2.
clear - H2.
unfold compose in H2. rewrite if_true in H2; auto.
simpl in H2.
assert (p = approx n oo (fun x => approx n (p x))).
injection H2; clear H2; intro.
apply inj_pair2 in H. auto.
transitivity ((approx n oo approx n) oo p).
apply H.
rewrite approx_oo_approx. auto.
Qed.

Lemma yesat_eq_aux: 
  forall pp k rsh sh l, 
    hereditary age
    (fun m : rmap =>
      exists p, 
     resource_fmap (approx (level m)) (m @ l) =
     resource_fmap (approx (level m)) (YES rsh (mk_lifted sh p) k pp)).
Proof.
 intros.
  intro; intros.
  destruct H0 as [p ?]; exists p.
  rewrite resource_at_approx.
  rewrite resource_at_approx in H0.
  apply (age1_resource_at a a' H); auto.
Qed.

Lemma yesat_eq: yesat = fun pp k rsh sh l =>
 exist (hereditary age)
  (fun m => 
  exists p, 
   resource_fmap (approx (level m)) (m @ l) = 
   resource_fmap (approx (level m)) (YES rsh (mk_lifted sh p) k pp))
   (yesat_eq_aux pp k rsh sh l).
Proof.
unfold yesat.
extensionality pp k; extensionality rsh sh l.
apply exist_ext. extensionality w.
apply exists_ext; intro p.
rewrite yesat_raw_eq.
auto.
Qed.

Lemma map_compose_approx_succ_e:
  forall A n pp pp',
       map (compose (A:=A) (approx (S n))) pp =
    map (compose (A:=A) (approx (S n))) pp' ->
  map (compose (A:=A) (approx n)) pp = map (compose (A:=A) (approx n)) pp'.
Proof.
induction pp; intros.
destruct pp'; inv H; auto.
destruct pp'; inv H; auto.
simpl.
rewrite <- (IHpp pp'); auto.
replace (approx n oo a) with (approx n oo p); auto.
clear - H1.
extensionality x. 
apply pred_ext'. extensionality w.
generalize (equal_f H1 x); clear H1; intro.
unfold compose in *.
assert (approx (S n) (a x) w <-> approx (S n) (p x) w).
rewrite H; intuition.
simpl.
apply and_ext'; auto; intros.
apply prop_ext.
intuition.
destruct H3; auto.
split; auto.
destruct H2; auto.
split; auto.
Qed.

(* NOT TRUE, because the shares might not match 
Lemma extensionally_yesat: forall pp k sh l, extensionally (yesat pp k sh l) = yesat pp k sh l.
*)

Program Definition noat (l: AV.address) : pred rmap := 
    fun m => identity (m @ l).
 Next Obligation.
    intros; intro; intros.
    apply (age1_resource_at_identity _ _ l H); auto.
 Qed.

Definition ct_count (k: kind) : Z := 
  match k with LK n => n-1 | _ =>  0 end.

Definition resource_share (r: resource) : option share :=
 match r with
 | YES rsh sh _ _ => Some (Share.splice rsh (pshare_sh sh))
 | NO sh => Some (Share.rel Share.Lsh sh)
 | PURE _ _ => None
 end.

Definition nonlock (r: resource) : Prop :=
 match r with
 | YES _ _ k _ => isVAL k \/ isFUN k
 | _ => True
 end.

Lemma age1_nonlock: forall phi phi' l,
  age1 phi = Some phi' -> (nonlock (phi @ l) <-> nonlock (phi' @ l)).
Proof.
  intros.
  destruct (phi @ l) as [rsh | rsh sh k P |] eqn:?H.
  + pose proof (age1_NO phi phi' l rsh H).
    rewrite H1 in H0.
    rewrite H0.
    reflexivity.
  + pose proof (age1_YES' phi phi' l rsh sh k H).
    destruct H1 as [? _].
    spec H1; [eauto |].
    destruct H1 as [P' ?].
    rewrite H1.
    reflexivity.
  + pose proof (age1_PURE phi phi' l k H).
    destruct H1 as [? _].
    spec H1; [eauto |].
    destruct H1 as [P' ?].
    rewrite H1.
    reflexivity.
Qed.

Lemma age1_resource_share: forall phi phi' l,
  age1 phi = Some phi' -> (resource_share (phi @ l) = resource_share (phi' @ l)).
Proof.
  intros.
  destruct (phi @ l) as [rsh | rsh sh k P |] eqn:?H.
  + pose proof (age1_NO phi phi' l rsh H).
    rewrite H1 in H0.
    rewrite H0.
    reflexivity.
  + pose proof (age1_YES' phi phi' l rsh sh k H).
    destruct H1 as [? _].
    spec H1; [eauto |].
    destruct H1 as [P' ?].
    rewrite H1.
    reflexivity.
  + pose proof (age1_PURE phi phi' l k H).
    destruct H1 as [? _].
    spec H1; [eauto |].
    destruct H1 as [P' ?].
    rewrite H1.
    reflexivity.
Qed.

Lemma resource_share_join_exists: forall r1 r2 r sh1 sh2,
  resource_share r1 = Some sh1 ->
  resource_share r2 = Some sh2 ->
  join r1 r2 r ->
  exists sh, join sh1 sh2 sh /\ resource_share r = Some sh.
Proof.
  intros.
  destruct r1, r2; try solve [inversion H | inversion H0];
  inv H; inv H0; inv H1;
  eexists; split.
  (* NO - NO *)
  + apply rel_join; eauto.
  + reflexivity.
  (* NO - YES *)
  + rewrite <- splice_bot2.
    apply join_splice; eauto.
  + reflexivity.
  (* YES - NO *)
  + rewrite <- splice_bot2.
    apply join_splice; eauto.
  + reflexivity.
  (* YES - YES *)
  + apply join_splice; eauto.
  + reflexivity.
Qed.

Lemma resource_share_join: forall r1 r2 r sh1 sh2 sh,
  resource_share r1 = Some sh1 ->
  resource_share r2 = Some sh2 ->
  join r1 r2 r ->
  join sh1 sh2 sh ->
  resource_share r = Some sh.
Proof.
  intros.
  destruct (resource_share_join_exists _ _ _ _ _ H H0 H1) as [sh' [? ?]].
  rewrite H4.
  f_equal.
  eapply join_eq; eauto.
Qed.

Lemma resource_share_joins: forall r1 r2 sh1 sh2,
  resource_share r1 = Some sh1 ->
  resource_share r2 = Some sh2 ->
  joins r1 r2 ->
  joins sh1 sh2.
Proof.
  intros.
  destruct H1 as [r ?].
  destruct (resource_share_join_exists _ _ _ _ _ H H0 H1) as [sh [? ?]].
  exists sh.
  auto.
Qed.

Lemma nonlock_join: forall r1 r2 r,
  nonlock r1 ->
  nonlock r2 ->
  join r1 r2 r ->
  nonlock r.
Proof.
  intros.
  destruct r1, r2; inv H1; auto.
Qed.

Program Definition nonlockat (l: AV.address): pred rmap :=
  fun m => nonlock (m @ l).
 Next Obligation.
    intros; intro; intros.
    unfold resource_share in *.
    destruct (a @ l) eqn:?H.
    + rewrite (necR_NO a a' l t) in H1 by (constructor; auto).
      rewrite H1; assumption.
    + eapply necR_YES in H1; [ | constructor; eassumption].
      rewrite H1; assumption.
    + eapply necR_PURE in H1; [ | constructor; eassumption].
      rewrite H1; assumption.
 Qed.

Program Definition shareat (l: AV.address) (sh: share): pred rmap :=
  fun m => resource_share (m @ l) = Some sh.
 Next Obligation.
    intros; intro; intros.
    unfold resource_share in *.
    destruct (a @ l) eqn:?H.
    + rewrite (necR_NO a a' l t) in H1 by (constructor; auto).
      rewrite H1; assumption.
    + eapply necR_YES in H1; [ | constructor; eassumption].
      rewrite H1; assumption.
    + inv H0.
 Qed.

Program Definition jam {A} {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A} {B: Type} {S': B -> Prop} (S: forall l, {S' l}+{~ S' l}) (P Q: B -> pred A) : B -> pred A :=
  fun (l: B) m => if S l then P l m else Q l m.
 Next Obligation.
    intros; intro; intros.
  if_tac; try (eapply pred_hereditary; eauto).
 Qed.

Lemma allp_noat_emp: allp noat = emp.
Proof.
  apply pred_ext; unfold derives; intros; simpl in *.
  + apply all_resource_at_identity.
    exact H.
  + intros. apply compcert_rmaps.RML.resource_at_identity.
    exact H.
Qed.    

Lemma jam_true: forall A JA PA agA AgeA B (S': B -> Prop) S P Q loc, S' loc -> @jam A JA PA agA AgeA B S' S P Q loc = P loc.
Proof.
intros.
apply pred_ext'.
extensionality m; unfold jam.
simpl. rewrite if_true; auto.
Qed.

Lemma jam_false: forall A JA PA agA AgeA B (S': B -> Prop) S P Q loc, ~ S' loc -> @jam A JA PA agA AgeA B S' S P Q loc = Q loc.
Proof.
intros.
apply pred_ext'.
extensionality m; unfold jam.
simpl; rewrite if_false; auto.
Qed.

Lemma boxy_jam:  forall (m: modality) A (S': A -> Prop) S P Q, 
      (forall (x: A), boxy m (P x)) -> 
      (forall x, boxy m (Q x)) -> 
      forall x, boxy m (@jam rmap _ _ _ _ A S' S P Q x).
Proof.
  intros.
   unfold boxy in *.
   apply pred_ext; intros w ?.
   unfold jam in *.
   simpl in *; if_tac. rewrite <- H . simpl. apply H1.
   rewrite <- H0; simpl; apply H1.
   simpl in *; if_tac.
    rewrite <- H in H1; auto.
   rewrite <- H0 in H1; auto.
Qed.

Definition extensible_jam: forall A (S': A -> Prop) S (P Q: A -> pred rmap), 
      (forall (x: A), boxy extendM (P x)) -> 
      (forall x, boxy extendM (Q x)) -> 
      forall x, boxy extendM  (@jam _ _ _ _ _ _ S' S P Q x).
Proof.
  apply boxy_jam; auto.
Qed.

Definition jam_vacuous: 
  forall A JA PA agA AgeA B S S' P Q, (forall x:B, ~ S x) -> @jam A JA PA agA AgeA B S S' P Q = Q.
Proof.
intros.
extensionality l; apply pred_ext'; extensionality w.
unfold jam.
simpl; rewrite if_false; auto.
Qed.
Implicit Arguments jam_vacuous.

Lemma make_sub_rmap: forall w (P: address -> Prop) (P_DEC: forall l, {P l} + {~ P l}),
  (forall l sh k, P l -> res_option (w @ l) = Some (sh, k) -> isVAL k \/ isFUN k) ->
  {w' | level w' = level w /\ compcert_rmaps.R.resource_at w' =
       (fun l => if P_DEC l then w @ l else core (w @ l))}.
Proof.
  intros.
  apply remake_rmap.
  + apply VAL_or_FUN_valid.
    intros.
    unfold compose in H0.
    specialize (H l sh k).
    if_tac in H0.
    - auto. 
    - destruct (w @ l); rewrite ?core_NO, ?core_YES, ?core_PURE in H0; inv H0.
  + intros.
    if_tac; [left; eauto |].
    destruct (w @ l) eqn:?H; rewrite ?core_NO, ?core_YES, ?core_PURE; simpl; auto.
    left.
    exists w; split; auto.
Qed.

Definition is_resource_pred (p: address -> pred rmap) (q: resource -> nat -> Prop) :=
  forall l w, (p l) w = q (w @ l) (level w).

Definition resource_stable (p: address -> pred rmap) :=
  forall l w w', w @ l = w' @ l -> level w = level w' -> (p l) w = (p l) w'.

Lemma is_resource_pred_resource_stable: forall {p},
  (exists q, is_resource_pred p q) -> resource_stable p.
Proof.
  unfold is_resource_pred, resource_stable.
  intros.
  destruct H as [q ?]; rewrite !H.
  rewrite H0; auto.
Qed.

(* This is about split one segment into two segments. *)
Lemma allp_jam_split2: forall (P Q R: address -> Prop) (p q r: address -> pred rmap)
  (P_DEC: forall l, {P l} + {~ P l})
  (Q_DEC: forall l, {Q l} + {~ Q l})
  (R_DEC: forall l, {R l} + {~ R l}),
  (exists resp, is_resource_pred p resp) ->
  (exists resp, is_resource_pred q resp) ->
  (exists resp, is_resource_pred r resp) ->
  Ensemble_join Q R P ->
  (forall l, Q l -> p l = q l) ->
  (forall l, R l -> p l = r l) ->
  (forall l m sh k, P l -> (p l) m -> res_option (m @ l) = Some (sh, k) -> isVAL k \/ isFUN k) ->
  allp (jam P_DEC p noat) = allp (jam Q_DEC q noat) * allp (jam R_DEC r noat).
Proof.
  intros until R_DEC.
  intros ST_P ST_Q ST_R.
  intros [? ?] ? ? ?.
  apply pred_ext; intros w; simpl; intros.
  + destruct (make_sub_rmap w Q Q_DEC) as [w1 [? ?]].
    Focus 1. {
      intros. eapply H3; [| | eauto].
      + firstorder.
      + specialize (H4 l); if_tac in H4; [auto | firstorder].
    } Unfocus.
    destruct (make_sub_rmap w R R_DEC) as [w2 [? ?]].
    Focus 1. {
      intros. eapply H3; [| | eauto].
      + firstorder.
      + specialize (H4 l); if_tac in H4; [auto | firstorder].
    } Unfocus.
    exists w1, w2.
    split3; auto.
    - apply resource_at_join2; try congruence.
      intro l.
      rewrite H6, H8.
      pose proof core_unit (w @ l).
      destruct (Q_DEC l), (R_DEC l).
      * firstorder.
      * apply join_comm; auto.
      * auto.
      * specialize (H4 l).
        rewrite if_false in H4 by firstorder.
        apply identity_unit_equiv in H4.
        pose proof unit_core H4.
        rewrite <- H10; auto.
    - intros l.
      specialize (H4 l).
      if_tac.
      * rewrite <- H1 by auto.
        rewrite if_true in H4 by firstorder.
        erewrite <- (is_resource_pred_resource_stable ST_P); [eauto | | auto].
        rewrite H6, if_true by auto; auto.
      * rewrite H6, if_false by auto.
        apply core_identity.
    - intros l.
      specialize (H4 l).
      if_tac.
      * rewrite <- H2 by auto.
        rewrite if_true in H4 by firstorder.
        erewrite <- (is_resource_pred_resource_stable ST_P); [eauto | | auto].
        rewrite H8, if_true by auto; auto.
      * rewrite H8, if_false by auto.
        apply core_identity.
  + destruct H4 as [y [z [? [? ?]]]].
    specialize (H5 b); specialize (H6 b).
    if_tac.
    - if_tac in H5; if_tac in H6.
      * firstorder.
      * rewrite H1 by auto.
        erewrite (is_resource_pred_resource_stable ST_Q); [eauto | | apply join_level in H4; symmetry; tauto].
        apply resource_at_join with (loc := b) in H4.
        apply join_comm, H6 in H4.
        auto.
      * rewrite H2 by auto; auto.
        erewrite (is_resource_pred_resource_stable ST_R); [eauto | | apply join_level in H4; symmetry; tauto].
        apply resource_at_join with (loc := b) in H4.
        apply H5 in H4.
        auto.
      * firstorder.
    - rewrite if_false in H5 by firstorder.
      rewrite if_false in H6 by firstorder.
      apply resource_at_join with (loc := b) in H4.
      apply H5 in H4; rewrite <- H4; auto.
Qed.

Definition general_slice_resource (sh: share) (r: resource) : resource.
  refine (match r with
          | NO _ => NO (Share.unrel Share.Lsh sh)
          | YES _ _ k pp => _
          | PURE k pp => PURE k pp
          end).
  destruct (dec_share_identity (Share.unrel Share.Rsh sh)).
  + exact (NO (Share.unrel Share.Lsh sh)).
  + apply nonidentity_nonunit in n.
    refine (YES (Share.unrel Share.Lsh sh) (mk_pshare _ n) k pp).
Defined.

Lemma general_slice_resource_resource_share: forall r sh sh',
  resource_share r = Some sh ->
  join_sub sh' sh ->
  resource_share (general_slice_resource sh' r) = Some sh'.
Proof.
  intros.
  destruct r; inv H; unfold general_slice_resource; simpl.
  + f_equal.
    apply share_rel_unrel.
    pose proof rel_leq Share.Lsh t.
    eapply join_sub_trans; eauto.
  + destruct (dec_share_identity (Share.unrel Share.Rsh sh')); simpl.
    - f_equal.
      apply share_rel_unrel.
      apply share_sub_Lsh; auto.
    - f_equal.
      apply splice_unrel_unrel.
Qed.

Lemma general_slice_resource_nonlock: forall r sh sh',
  resource_share r = Some sh ->
  join_sub sh' sh ->
  nonlock r ->
  nonlock (general_slice_resource sh' r).
Proof.
  intros.
  destruct r; inv H; unfold general_slice_resource; simpl; auto.
  destruct (dec_share_identity (Share.unrel Share.Rsh sh')); simpl; auto.
Qed.

Lemma join_sub_is_general_slice_resource: forall r r' sh',
  join_sub r' r ->
  resource_share r' = Some sh' ->
  r' = general_slice_resource sh' r.
Proof.
  intros.
  destruct H as [r'' ?].
  destruct r, r'; inv H; inv H0; simpl.
  + f_equal.
    rewrite <- splice_bot2.
    symmetry; apply Share.unrel_splice_L.
  + rewrite <- splice_bot2.
    rewrite Share.unrel_splice_R.
    destruct (dec_share_identity Share.bot); [| pose proof bot_identity; exfalso; tauto].
    f_equal.
    symmetry; apply Share.unrel_splice_L.
  + rewrite Share.unrel_splice_R.
    destruct (dec_share_identity (pshare_sh p)); [exfalso; eapply pshare_not_identity; eauto |].
    rewrite mk_share_pshare_sh.
    f_equal.
    symmetry; apply Share.unrel_splice_L.
  + rewrite Share.unrel_splice_R.
    destruct (dec_share_identity (pshare_sh p1)); [exfalso; eapply pshare_not_identity; eauto |].
    rewrite mk_share_pshare_sh.
    f_equal.
    symmetry; apply Share.unrel_splice_L.
Qed.

Definition resource_share_split (p q r: address -> pred rmap): Prop :=
  exists p' q' r' p_sh q_sh r_sh,
    is_resource_pred p p' /\
    is_resource_pred q q' /\
    is_resource_pred r r' /\
    join q_sh r_sh p_sh /\
    (forall res n, p' res n ->
      resource_share res = Some p_sh /\
      q' (general_slice_resource q_sh res) n /\
      r' (general_slice_resource r_sh res) n) /\
    (forall p_res q_res r_res n,
      join q_res r_res p_res ->
      q' q_res n ->
      r' r_res n ->
      p' p_res n).

Lemma allp_jam_share_split: forall (P: address -> Prop) (p q r: address -> pred rmap)
  (P_DEC: forall l, {P l} + {~ P l}),
  resource_share_split p q r ->
  allp (jam P_DEC p noat) = allp (jam P_DEC q noat) * allp (jam P_DEC r noat).
Admitted.
(* We should use this lemma to prove all share_join lemmas, also all splittable lemmas. *)

Lemma allp_jam_overlap: forall (P Q: address -> Prop) (p q: address -> pred rmap)
  (P_DEC: forall l, {P l} + {~ P l})
  (Q_DEC: forall l, {Q l} + {~ Q l}),
  (exists resp, is_resource_pred p resp) ->
  (exists resp, is_resource_pred q resp) ->
  (forall l w1 w2, p l w1 -> q l w2 -> joins w1 w2 -> False) ->
  (exists l, P l /\ Q l) ->
  allp (jam P_DEC p noat) * allp (jam Q_DEC q noat) |-- FF.
Proof.
  intros.
  intro w; simpl; intros.
  destruct H3 as [w1 [w2 [? [? ?]]]].
  destruct H2 as [l ?].
  specialize (H4 l).
  specialize (H5 l).
  rewrite if_true in H4, H5 by tauto.
  apply (H1 l w1 w2); auto.
  eauto.
Qed.

Lemma yesat_join_diff:
  forall pp pp' k k' rsh rsh' sh sh' l w, k <> k' -> 
                  yesat pp k rsh sh l w -> yesat pp' k' rsh' sh' l w -> False.
Proof.
unfold yesat, yesat_raw; intros.
destruct H0 as [p ?]. destruct H1 as [p' ?].
simpl in *; inversion2 H0 H1.
contradiction H; auto.
Qed.

Lemma yesat_raw_join:
  forall pp k (rsh1 rsh2 rsh3: Share.t) (sh1 sh2 sh3: pshare) l phi1 phi2 phi3,
   join rsh1 rsh2 rsh3 ->
   join (proj1_sig sh1) (proj1_sig sh2) (proj1_sig sh3) ->   
   yesat_raw pp k rsh1 sh1 l phi1 ->
   yesat_raw pp k rsh2 sh2 l phi2 ->
   join phi1 phi2 phi3 ->
   yesat_raw pp k rsh3 sh3 l phi3.
Proof.
unfold yesat_raw; 
intros until 1; rename H into HR; intros.
simpl in H0,H1|-*.
assert (level phi2 = level phi3) by (apply join_level in H2; intuition).
rewrite H3 in *; clear H3.
assert (level phi1 = level phi3) by  (apply join_level in H2; intuition).
rewrite H3 in *; clear H3.
generalize (resource_at_join _ _ _ l H2); clear H2.
revert H0 H1.
case_eq (phi1 @ l); intros.
inv H1.
revert H2 H3; case_eq (phi2 @ l); intros.
inv H3.
generalize H.
inv H4. inv H1. inv H3.  intro. f_equal.
eapply join_eq; eauto.
eapply join_eq; eauto.
 inv H4.
inv H1.
Qed.

Lemma nonunit_join: forall A {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A} (x y z: A), 
  nonunit x -> join x y z -> nonunit z.
Proof.
intros.
intro; intro.
apply unit_identity in H1.
apply split_identity in H0; auto.
apply nonunit_nonidentity in H. 
contradiction.
Qed.

Lemma yesat_join:
  forall pp k rsh1 rsh2 rsh3 sh1 sh2 sh3 l m1 m2 m3,
   join rsh1 rsh2 rsh3 ->   
   join sh1 sh2 sh3 ->   
   yesat pp k rsh1 sh1 l m1 ->
   yesat pp k rsh2 sh2 l m2 ->
   join m1 m2 m3 ->
   yesat pp k rsh3 sh3 l m3.
Proof.
intros.
destruct H1 as [p1 ?].
destruct H2 as [p2 ?].
assert (p3: nonunit sh3).
apply nonunit_join in H0; eauto with typeclass_instances.
exists p3.
eapply yesat_raw_join with (phi1 := m1); eauto.
auto.
Qed.

Definition spec_parametric (Q: address -> spec) : Prop :=
   forall l l', exists pp, exists ok,
             forall rsh sh m,
           Q l rsh sh l' m = 
            (exists p, exists k, ok k /\ m @ l' = 
                 YES rsh (mk_lifted sh p) k (preds_fmap (approx (level m)) pp)).

Lemma jam_noat_splittable_aux:
  forall S' S Q (PARAMETRIC: spec_parametric Q)
           (rsh1 rsh2 rsh3: Share.t)
           (sh1 sh2 sh3: pshare) l
           (HR: join rsh1 rsh2 rsh3)
           (H: join (proj1_sig sh1) (proj1_sig sh2) (proj1_sig sh3))
           w (H0: allp (@jam _ _ _ _ _ _ (S' l) (S l) (Q l rsh3 (pshare_sh sh3)) noat) w)
           f (Hf: resource_at f = fun loc => slice_resource (if S l loc then rsh1 else Share.bot) sh1 (w @ loc))
           g (Hg: resource_at g = fun loc => slice_resource (if S l loc then rsh2 else Share.bot) sh2 (w @ loc))
           (H1: join f g w),
           allp (jam (S l) (Q l rsh1 (pshare_sh sh1)) noat) f.
Proof.
intros.
intro l'.
spec H0 l'.
unfold jam in H0 |- *.
simpl in H0|-*.
if_tac.
destruct (PARAMETRIC l l') as [pp [ok ?]]; clear PARAMETRIC.
rewrite H3 in H0 |- *; clear H3.
destruct H0 as [p3 [k [? ?]]].
exists (proj2_sig sh1); exists k; split; auto.
destruct sh3 as [sh3 p3']. proof_irr.
clear H0.
case_eq (w @ l'); intros.
inversion2 H0 H3. 
destruct p0.
inversion2 H0 H3.
generalize (resource_at_join _ _ _ l' H1); intro.
generalize (f_equal (resource_at f) (refl_equal l')); intro.
pattern f at 1 in H4; rewrite Hf in H4.
rewrite H0 in H4.
replace (@mk_lifted Share.t _ (pshare_sh sh1) (proj2_sig sh1)) with sh1.
replace (level f) with (level w). 
rewrite H4.
simpl.
rewrite H8.
rewrite if_true in H4|-* by auto.
auto.
apply join_level in H1; intuition.
destruct sh1; auto.
congruence.
(* noat case *)
generalize (resource_at_join _ _ _ l' H1); intro.
apply split_identity in H3; auto.
Qed.

Definition splittable {A} {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A} (Q: Share.t -> Share.t -> pred A) := 
  forall (rsh1 rsh2 rsh3: Share.t) (sh1 sh2 sh3: pshare),
     join rsh1 rsh2 rsh3 ->
    join sh1 sh2 sh3 ->
    Q rsh1 (pshare_sh sh1) * Q rsh2 (pshare_sh sh2) = Q rsh3 (pshare_sh sh3).

Lemma jam_noat_splittable:
  forall (S': address -> address -> Prop) S
           (Q: address -> spec)
     (PARAMETRIC: spec_parametric Q),
    forall l, splittable (fun rsh sh => allp (@jam _ _ _ _ _ _ (S' l) (S l) (Q l rsh sh) noat)).
Proof.
unfold splittable; intros. rename H into HR; rename H0 into H.
apply pred_ext; intro w; simpl.
+ intros [w1 [w2 [? [? ?]]]].
  intro l'. spec H1 l'; spec H2 l'.
  unfold jam in *.
  revert H1 H2.
  if_tac.
  - intros.
    specialize (PARAMETRIC l l').
    destruct PARAMETRIC as [pp [ok ?]].
    rewrite H4 in H2. destruct H2 as [p2 [k2 [G2 H2]]]. 
    rewrite H4 in H3; destruct H3 as [p3 [k3 [G3 H3]]]. 
    rewrite H4.
    destruct sh3.
    simpl in  H2, H3.
    exists n.
    exists k2.
    generalize (resource_at_join _ _ _ l' H0); rewrite H2; rewrite H3; intro Hx.
    generalize H; clear H.
    inv Hx. 
    split; auto.
    simpl.
    replace (level w1) with (level w) by (apply join_level in H0; intuition).
    destruct sh4.
    do 3 red in H.
    generalize (join_eq H H5); intro.
    simpl in H6.
    subst x0.
    generalize (join_eq HR RJ); intro; subst rsh5.
    f_equal; auto.
  - intros.
    generalize (resource_at_join _ _ _ l' H0); intro.
    apply H2 in H4. rewrite H4 in H3; auto.
+ intros.
  pose (rslice (rsh : Share.t) (loc: address) := if S l loc then rsh else Share.bot).
  pose (f loc := slice_resource (rslice rsh1 loc) sh1 (w @ loc)).
  assert (Vf: CompCert_AV.valid (res_option oo f)) by apply slice_resource_valid.
  destruct (make_rmap _ Vf (level w)) as [phi [Gf Hf]].
  Focus 1. {
    extensionality loc; unfold compose, f.
    specialize (PARAMETRIC l loc).
    destruct PARAMETRIC as [pp [ok Jf]].
    spec H0 loc.
    destruct (S l loc).
    rewrite Jf in H0.
    destruct H0 as [p3 [k3 [G0 H0]]].
    generalize (resource_at_approx w loc); intro.
    rewrite H0 in H1.
    inversion H1; clear H1; auto.
    rewrite H0.
    simpl. f_equal. auto.
    apply  identity_resource in H0.
    revert H0; case_eq (w @ loc); intros; try contradiction; simpl; f_equal; auto.
    generalize (resource_at_approx w loc); intro.
    rewrite H0 in H2. unfold resource_fmap in H2.
    change compcert_rmaps.R.PURE with PURE in  H2.
    destruct p. apply PURE_inj in H2. simpl. f_equal. destruct H2. auto.
  } Unfocus.
  pose (g loc := slice_resource (rslice rsh2 loc) sh2 (w @ loc)).
  assert (Vg: CompCert_AV.valid (res_option oo g)) by apply slice_resource_valid.
  destruct (make_rmap _ Vg (level w)) as [phi' [Gg Hg]].
  Focus 1. {
    extensionality loc; unfold compose, g.
    specialize (PARAMETRIC l loc).
    destruct PARAMETRIC as [pp [k Jg]].
    spec H0 loc.
    unfold jam in H0.
    rewrite Jg in H0.
    destruct (S l loc).
    destruct H0 as [p3 [k3 [G0 H0]]].
    generalize (resource_at_approx w loc); intro.
    rewrite H0 in H1.
    inversion H1; clear H1; auto.
    rewrite H0.
    simpl. f_equal. auto.
    apply  identity_resource in H0.
    revert H0; case_eq (w @ loc); intros; try contradiction; simpl; f_equal; auto.
    generalize (resource_at_approx w loc); intro.
    rewrite H0 in H2. unfold resource_fmap in H2.
    change compcert_rmaps.R.PURE with PURE in  H2.
    destruct p. apply PURE_inj in H2. simpl. f_equal. destruct H2. auto.
  } Unfocus.
  unfold f,g in *; clear f g.
  rename phi into f; rename phi' into g.
  assert (join f g w).
  apply resource_at_join2; auto.
  intro.
  rewrite Hf; rewrite Hg.
  clear - PARAMETRIC HR H H0.
  spec H0 loc.
  unfold jam in H0.
  if_tac in H0.
  destruct (PARAMETRIC l loc) as [pp [ok ?]]; clear PARAMETRIC.
  rewrite H2 in H0.
  destruct H0 as [? [? [? ?]]].
  rewrite H3.
  generalize (preds_fmap (approx (level w)) pp); intro.
  simpl.
  constructor; auto.
  unfold rslice. repeat rewrite if_true by auto.
  destruct sh3 as [sh3 p3]; auto.
  unfold rslice.  repeat rewrite if_false by auto.
  apply identity_resource in H0.
  revert H0; case_eq (w @ loc); intros; try contradiction; constructor.
  apply identity_share_bot in H2. subst.
  apply join_unit1; auto.
  (**)
  econstructor; econstructor; split; [apply H1|].
  split.
  eapply jam_noat_splittable_aux; eauto.
  simpl; auto.
  eapply jam_noat_splittable_aux.
  auto. eapply join_comm; apply HR. eauto. 2: eauto. 2: eauto.
  simpl; eauto. apply join_comm; auto.
Qed.

(****** Specific specs  ****************)

Definition VALspec : spec :=
       fun (rsh sh: Share.t) (l: address) =>
          allp (jam (eq_dec l)
                                  (fun l' => EX v: memval, 
                                                yesat NoneP (VAL v) rsh sh l')
                                  noat).

Definition VALspec_range (n: Z) : spec :=
     fun (rsh sh: Share.t) (l: address) =>
          allp (jam (adr_range_dec l n)
                                  (fun l' => EX v: memval, 
                                                yesat NoneP (VAL v) rsh sh l')
                                  noat).

Definition nonlock_permission_bytes (sh: share) (a: address) (n: Z) : pred rmap :=
  allp (jam (adr_range_dec a n) (fun i => shareat i sh && nonlockat i) noat).

Definition nthbyte (n: Z) (l: list memval) : memval :=
     nth (nat_of_Z n) l Undef.

(*  Unfortunately address_mapsto_old, while a more elegant definition than
   address_mapsto, is not quite right.  For example, it doesn't uniquely determine v *)
Definition address_mapsto_old (ch: memory_chunk) (v: val) : spec :=
        fun (rsh sh: Share.t) (l: AV.address)  => 
             allp (jam (adr_range_dec l (size_chunk ch)) 
                              (fun l' => yesat NoneP (VAL (nthbyte (snd l' - snd l) (encode_val ch v))) rsh sh l')
                           noat).

Definition address_mapsto (ch: memory_chunk) (v: val) : spec :=
        fun (rsh sh: Share.t) (l: AV.address) =>
           EX bl: list memval, 
               !! (length bl = size_chunk_nat ch  /\ decode_val ch bl = v /\ (align_chunk ch | snd l))  &&
                allp (jam (adr_range_dec l (size_chunk ch))
                                    (fun loc => yesat NoneP (VAL (nth (nat_of_Z (snd loc - snd l)) bl Undef)) rsh sh loc)
                                    noat).

Definition address_mapsto' ch v rsh sh loc bl :=
  !!(length bl = size_chunk_nat ch /\ decode_val ch bl = v /\ (align_chunk ch | snd loc)) &&
  allp
  (jam (adr_range_dec loc (size_chunk ch))
    (fun loc' : address =>
      yesat NoneP
      (VAL (nth (nat_of_Z (snd loc' - snd loc)) bl Undef)) rsh sh loc') noat).

Lemma address_mapsto'_mapsto: forall ch v rsh sh loc bl phi,
  address_mapsto' ch v rsh sh loc bl phi -> address_mapsto ch v rsh sh loc phi.
Proof.
intros until phi; intro H.
unfold address_mapsto' in H; unfold address_mapsto.
exists bl; auto.
Qed.

Lemma address_mapsto_fun:
  forall ch rsh sh rsh' sh' l v v',
          (address_mapsto ch v rsh sh l * TT) && (address_mapsto ch v' rsh' sh' l * TT) |-- !!(v=v').
Proof.
intros.
intros m [? ?]. unfold prop.
destruct H as [m1 [m2 [J [[bl [[Hlen [? _]] ?]] _]]]].
destruct H0 as [m1' [m2' [J' [[bl' [[Hlen' [? _]] ?]] _]]]].
subst.
assert (forall i, nth_error bl i = nth_error bl' i).
intro i; spec H1 (fst l, snd l + Z_of_nat i); spec H2 (fst l, snd l + Z_of_nat i).
unfold jam in *.
destruct l as [b z].
simpl in *.
if_tac in H1.
destruct H as [_ ?].
replace (z + Z_of_nat i - z) with (Z_of_nat i) in * by omega.
assert ((i < length bl)%nat).
rewrite Hlen.
rewrite size_chunk_conv in H.
omega.
rewrite <- Hlen' in Hlen.
rewrite nat_of_Z_eq in *.
destruct H1; destruct H2.
unfold yesat_raw in *.
repeat rewrite preds_fmap_NoneP in *.
assert (H5: nth i bl Undef = nth i bl' Undef).
apply (resource_at_join _ _ _ (b,z + Z_of_nat i)) in J.
apply (resource_at_join _ _ _ (b,z + Z_of_nat i)) in J'.
rewrite H1 in J; rewrite H2 in J'; clear H1 H2. 
inv J; inv J'; try congruence.
clear - Hlen H0 H5.
revert bl bl' Hlen H0 H5; induction i; destruct bl; destruct bl'; simpl; intros; auto; try omegaContradiction.
apply IHi; auto.
omega.
assert (~ (i < length bl)%nat).
contradict H.
split; auto.
rewrite Hlen in H.
rewrite size_chunk_conv.
omega.
assert (i >= length bl)%nat by omega.
destruct (nth_error_length i bl).
rewrite H5; auto.
destruct (nth_error_length i bl').
rewrite H7; auto.
omega.
clear - H.
assert (bl=bl'); [| subst; auto].
revert bl' H; induction bl; destruct bl'; intros; auto.
specialize (H 0%nat); simpl in H. inv H.
specialize (H 0%nat); simpl in H. inv H.
f_equal.
specialize (H 0%nat); simpl in H. inv H. auto.
apply IHbl.
intro.
spec H (S i).
simpl in H.
auto.
simpl; auto.
Qed.

Definition lock_size : Z := 4.

Program Definition CTat (base: address) (rsh sh: Share.t) (l: address) : pred rmap :=
 fun m => exists p, m @ l = YES rsh (mk_lifted sh p) (CT (snd l - snd base)) NoneP.
 Next Obligation.
    intros; intro; intros.
    destruct H0 as [p ?]; exists p.
    apply (age1_YES a a'); auto.
  Qed.

Definition LKspec (R: pred rmap) : spec :=
   fun (rsh sh: Share.t) (l: AV.address)  =>
    allp (jam (adr_range_dec l lock_size)
                         (jam (eq_dec l) 
                            (yesat (SomeP nil (fun _ => R)) (LK lock_size) rsh sh)
                            (CTat l rsh sh))
                    noat).

Definition boolT : Type := bool.
Definition unitT : Type := unit.

Definition packPQ {A: Type} (P Q: A -> environ -> pred rmap) := 
  (fun xy : (A*(boolT*(environ * unitT))) => 
    if fst (snd xy) then P (fst xy) (fst (snd (snd xy))) else Q (fst xy) (fst (snd (snd xy)))).

Definition TTat (l: address) : pred rmap := TT.

Definition FUNspec (fml: funsig) (A: Type) (P Q: A -> environ -> pred rmap)(l: address): pred rmap :=
          allp (jam (eq_dec l) (pureat (SomeP (A::boolT::environ::nil) (packPQ P Q)) (FUN fml)) TTat).

(***********)

Lemma ewand_lem1x:
  forall S P: mpred,
          S |-- P * TT ->
          S |-- P * (ewand P S).
Proof.
intros.
intros w ?. specialize (H w H0).
destruct H as [w1 [w2 [? [? _]]]].
exists w1; exists w2; split3; auto.
exists w1; exists w; split3; auto.
Qed.

Lemma address_mapsto_old_parametric: forall ch v, 
   spec_parametric (fun l rsh sh l' => yesat NoneP (VAL (nthbyte (snd l' - snd l) (encode_val ch v))) rsh sh l').
Proof.
intros.
exists NoneP. exists (fun k => k= VAL (nthbyte (snd l' - snd l) (encode_val ch v))).
intros.
unfold yesat.
apply exists_ext; intro p.
unfold yesat_raw.
simpl.
apply prop_ext; split; intros.
econstructor; split; [reflexivity | ]. 
rewrite H; f_equal.

simpl.
eauto.
destruct H as [k [? ?]].
subst; auto.
Qed.

Lemma VALspec_parametric: 
  spec_parametric (fun l rsh sh l' => EX v: memval,  yesat NoneP (VAL v) rsh sh l').
Proof.
intros.
exists NoneP.
exists (fun k => exists v, k=VAL v).
intros.
unfold yesat.
apply prop_ext; split; intros.
destruct H as [v [p ?]].
exists p.
exists (VAL v).
split; eauto.
destruct H as [p [k [[v ?] ?]]].
subst.
exists v.
exists p.
auto.
Qed.

Lemma LKspec_parametric: forall R,
  spec_parametric (fun l rsh sh => jam (eq_dec l) 
                            (yesat (SomeP nil (fun _ => R)) (LK lock_size) rsh sh)
                            (CTat l rsh sh)).
Proof.
intros.
unfold jam.
intro; intros.
simpl.
destruct (eq_dec l l').
unfold yesat, yesat_raw.
exists (SomeP nil (fun _ : unit => R)).
exists (fun k => k = LK lock_size).
intros.
apply exists_ext; intro p.
unfold yesat_raw.
apply prop_ext; split; intros.
econstructor; eauto.
destruct H as [k [? ?]].
subst; auto.
exists NoneP.
exists (fun k => k = CT (snd l' - snd l)).
intros.
apply exists_ext; intro p.
apply prop_ext; split; intros.
rewrite preds_fmap_NoneP.
eauto.
rewrite preds_fmap_NoneP in H.
destruct H as [k [? ?]].
simpl in *.
subst; auto.
Qed.

Lemma FUNspec_parametric: forall fml A P Q, 
   spec_parametric (fun l sh => yesat (SomeP (A::boolT::environ::nil) (packPQ P Q)) (FUN fml) sh).
Proof.
intros.
exists (SomeP (A::boolT::environ::nil) (packPQ P Q)).
exists (fun k => k=FUN fml).
intros.
simpl.
apply exists_ext; intro p.
unfold yesat_raw.
apply prop_ext; split; intros.
econstructor; eauto.
destruct H as [k [? ?]].
subst; auto.
Qed.

Lemma address_mapsto_splittable:
      forall ch v l, splittable (fun rsh sh => address_mapsto ch v rsh sh l).
Proof.
intros.
unfold splittable.
intros until 1; rename H into HR; intros.
apply pred_ext; intros ? ?.
destruct H0 as [m1 [m2 [? [? ?]]]].
unfold address_mapsto in *.
destruct H1 as [bl1 [[LEN1 DECODE1] ?]]; destruct H2 as [bl2 [[LEN2 DECODE2] ?]].
exists bl1; split; auto.
simpl; auto.
intro loc; spec H1 loc; spec H2 loc.
unfold jam in *.
apply (resource_at_join _ _ _ loc) in H0.
hnf in H1, H2|-*.
if_tac.
destruct sh1 as [sh1 p1]; destruct sh2 as [sh2 p2]; destruct sh3 as [sh3 p3].
hnf in H1,H2.
destruct H1; destruct H2.
hnf.
exists p3.
unfold yesat_raw in *.
hnf in H1,H2|-*.
rewrite preds_fmap_NoneP in *.
repeat proof_irr.
rewrite H1 in H0; rewrite H2 in H0; clear H1 H2.
unfold yesat_raw.
inv H0.
f_equal.
eapply join_eq; eauto.
eapply join_eq; eauto.
apply H1 in H0. do 3 red in H2|-*. rewrite <- H0; auto.
(************* backwards direction *********************)
rename a into m.
hnf in H0|-*.
destruct H0 as [bl [[? [? Halign]] ?]].
pose (rslice (rsh : Share.t) (loc: address) := if adr_range_dec l (size_chunk ch) loc then rsh else Share.bot).
exists (slice_rmap (rslice rsh1) sh1 m); exists (slice_rmap (rslice rsh2) sh2 m).
split3.
pattern m at 3; replace m with (slice_rmap (rslice rsh3) sh3 m).
apply slice_rmap_join; auto.
unfold rslice.
intro loc. if_tac; auto.
apply rmap_ext.
apply slice_rmap_level.
intro loc.
rewrite resource_at_slice.
unfold rslice, slice_resource.
specialize (H2 loc).
hnf in H2.
if_tac. destruct H2. rewrite H2. f_equal. destruct sh3; simpl. apply exist_ext; auto.
do 3 red in H2.
apply identity_resource in H2.
revert H2; 
case_eq (m @ loc); intros; auto; try contradiction.
apply identity_share_bot in H4; subst; auto.
exists bl; repeat split; auto.
intro loc; spec H2 loc; unfold jam in *;  hnf in H2|-*; if_tac; auto.
destruct H2; exists (proj2_sig sh1).
unfold yesat_raw in *.
hnf.
rewrite resource_at_slice.
rewrite H2.
repeat rewrite preds_fmap_NoneP.
simpl.
unfold rslice; rewrite if_true by auto.
f_equal.
apply lifted_eq; simpl; auto.
do 3 red in H2|-*.
rewrite resource_at_slice.
unfold rslice; rewrite if_false by auto.
apply identity_resource in H2; destruct (m @ loc); try contradiction; simpl; auto.
apply NO_identity. apply PURE_identity.
exists bl; repeat split; auto.
intro loc; spec H2 loc; unfold jam in *;  hnf in H2|-*; if_tac; auto.
destruct H2; exists (proj2_sig sh2).
unfold yesat_raw in *.
hnf; rewrite resource_at_slice.
rewrite H2.
repeat rewrite preds_fmap_NoneP.
simpl.
unfold rslice; rewrite if_true by auto.
f_equal.
apply lifted_eq; simpl; auto.
do 3 red in H2|-*.
rewrite resource_at_slice.
unfold rslice; rewrite if_false by auto.
apply identity_resource in H2; destruct (m @ loc); try contradiction; simpl; auto.
apply NO_identity. apply PURE_identity.
Qed.

Lemma VALspec_splittable: forall l, splittable (fun rsh sh => VALspec rsh sh l).
Proof.
apply jam_noat_splittable.
apply VALspec_parametric.
Qed.

Lemma LKspec_splittable: forall R l, splittable (fun rsh sh => LKspec R rsh sh l).
Proof.
intro.
apply jam_noat_splittable.
apply LKspec_parametric.
Qed.

Definition val2address (v: val) : option AV.address := 
  match v with Vptr b ofs => Some (b, Int.signed ofs) | _ => None end.

Definition fun_assert (fml: funsig) (A: Type) (P Q: A -> environ -> pred rmap) (v: val)  : pred rmap :=
 (EX b : block, !! (v = Vptr b Int.zero) && FUNspec fml A P Q (b, 0))%pred.

Definition LK_at l w := exists n, kind_at (LK n) l w.

Lemma VALspec_readable:
  forall l rsh sh w,  (VALspec rsh sh l * TT) %pred w -> readable l w.
(* The converse is not quite true, because "readable" does constraint to NoneP *)
Proof.
unfold VALspec, readable;
intros.
destruct H as [w1 [w2 [? [? _]]]].
spec H0 l.
unfold jam in H0.
hnf in H0|-*; rewrite if_true in H0 by auto.
destruct H0 as [v [p ?]].
unfold yesat_raw in H0.
generalize (resource_at_join _ _ _ l H); rewrite H0; intro Hx.
inv Hx; auto.
Qed.


(* NOT TRUE, because of CompCert_AV.valid problems.  
Lemma jam_con: forall A (S: A -> Prop) P Q, 
     allp (jam S P Q) |-- allp (jam S P (fun _ => emp)) * (allp (jam S (fun _ => emp) Q)).
*)

Lemma address_mapsto_VALspec:
  forall ch v rsh sh l i, 0 <= i < size_chunk ch ->
        address_mapsto ch v rsh sh l |-- VALspec rsh sh (adr_add l i) * TT.
Proof.
intros. intros w ?.
pose (f l' := if eq_dec (adr_add l i) l' then w @ l' 
                   else if adr_range_dec l (size_chunk ch) l' then NO Share.bot else w @ l').
pose (g l' := if eq_dec (adr_add l i) l' then NO Share.bot else w @ l').
exploit (deallocate (w) f g); intros.
unfold f; clear - H0 H; intro; intros.
unfold compose in *.
destruct (eq_dec (adr_add l i) (b,ofs)); try inv H1.
destruct H0 as [bl [H0' ?]].
spec H0 (b,ofs).
unfold jam in H0.
hnf in H0; if_tac in H0.
destruct H0.
unfold yesat_raw in H0.
rewrite H0.  simpl; auto.
do 3 red in H0. apply identity_resource in H0.
revert H0; case_eq (w @ (b,ofs)); intros; try contradiction; auto.
apply identity_share_bot in H2; subst t.
simpl. auto.
if_tac. simpl; auto.
destruct H0 as [d [? ?]]. specialize (H2 (b,ofs)). rewrite jam_false in H2; auto.
do 3 red in H2. apply identity_resource in H2; destruct (w @ (b,ofs)); try contradiction; simpl; auto.
unfold g; clear - H0 H; intro; intros.
unfold compose in *.
destruct (eq_dec (adr_add l i) (b,ofs)); simpl; auto.
destruct H0 as [bl [H0' ?]].
spec H0 (b,ofs).
unfold jam in H0.
hnf in H0; if_tac in H0.
destruct H0.
unfold yesat_raw in H0.
rewrite H0; simpl; auto.
do 3 red in H0. apply identity_resource in H0.
revert H0; case_eq (w @ (b,ofs)); intros; try contradiction; auto.
apply identity_share_bot in H2; subst t.
simpl; auto.
unfold f,g; clear f g.
destruct H0 as [b [? ?]]. specialize (H1 l0).  hnf in H1.
if_tac in H1. destruct H1.  hnf in H1. if_tac; rewrite H1; constructor.
apply join_unit2; auto.
apply join_unit1; auto.
if_tac.
contradiction H2. unfold adr_add in H3; destruct l; destruct l0; simpl in H3. inv H3. 
split; auto. omega.
do 3 red in H1. apply identity_unit_equiv in H1. auto.
destruct H1 as [phi1 [phi2 [? ?]]].
destruct (join_ex_identities w) as [e [? ?]].
exists phi1; exists phi2.
split; auto.
split; auto.
unfold VALspec.
intro l'.
unfold jam in *.
destruct H0 as [bl [H0' ?]].
spec H0 l'.
unfold jam in H0.
hnf in H0|-*; if_tac.
subst l'.
rewrite if_true in H0.
destruct H0.
unfold yesat_raw in H0.
generalize (refl_equal (phi1 @ adr_add l i)); 
pattern phi1 at 1; rewrite H2; unfold f; intro.
rewrite if_true in H5.
rewrite H0 in H5.
exists (nth (nat_of_Z (snd (adr_add l i) - snd l)) bl Undef).
exists x.
unfold yesat_raw.
hnf in H0|-*.
repeat rewrite preds_fmap_NoneP in *.
auto.
destruct l; unfold adr_range, adr_add. split; auto.
destruct l; unfold adr_range, adr_add. split; auto.
simpl; omega.
do 3 red.
rewrite H2. unfold f.
rewrite if_false; auto.
if_tac. apply NO_identity. apply H0.
Qed.


Lemma address_mapsto_exists:
  forall ch v rsh (sh: pshare) loc w0
      (RESERVE: forall l', adr_range loc (size_chunk ch) l' -> w0 @ l' = NO Share.bot),
      (align_chunk ch | snd loc) ->
      exists w, address_mapsto ch (decode_val ch (encode_val ch v)) rsh (pshare_sh sh) loc w 
                    /\ core w = core w0.
Proof.
intros. rename H into Halign.
unfold address_mapsto.
pose (f l' := if adr_range_dec loc (size_chunk ch) l'
                     then YES rsh sh (VAL (nthbyte (snd l' - snd loc) (encode_val ch v))) NoneP
                     else core w0 @ l').
assert (CompCert_AV.valid (res_option oo f)).
apply VAL_valid.
unfold compose, f; intros.
if_tac in H.
simpl in H.
injection H;intros; subst k; auto.
rewrite <- core_resource_at in H.
generalize (core_identity (w0 @ l)); intro.
rewrite core_resource_at in *.
apply identity_resource in H1.
revert H H1; destruct (core w0 @ l); intros; try contradiction; inv H.
destruct (make_rmap f H (level w0)) as [phi [? ?]].
extensionality l; unfold f, compose; simpl.
if_tac; simpl; auto.
f_equal.
unfold NoneP. f_equal. unfold compose. extensionality x.
apply pred_ext; unfold approx, FF, prop; intros ? ?;  simpl; intuition.
rewrite <- level_core.
apply resource_at_approx.
exists phi.
split.
Focus 2.
apply rmap_ext. do 2 rewrite level_core. auto.
intro l; specialize (RESERVE l). 
rewrite <- core_resource_at. rewrite H1. unfold f.
if_tac.
 rewrite core_YES.
 rewrite <- core_resource_at. rewrite RESERVE; auto.
 rewrite core_NO; auto.
 rewrite <- core_resource_at; rewrite core_idem; auto.
exists (encode_val ch v).
split.
split; auto.
apply encode_val_length.
intro l'.
unfold jam.
hnf.
unfold yesat, yesat_raw, noat.
unfold app_pred, proj1_sig. rewrite H1; clear H H1.
unfold f; clear f.
if_tac.
destruct sh; simpl in *.
exists n.
f_equal.
unfold NoneP; f_equal.
extensionality xx.  apply pred_ext; intros ? ?.
contradiction H1.
simpl in H1. intuition.
rewrite <- core_resource_at.
apply core_identity.
Qed.

(*  NOT TRUE, because readable doesn't constraint NoneP ...
Lemma readable_VAL: 
 forall w l, readable l (w_m w) <-> exists sh, (VALspec sh l * TT) w.

*)

Lemma VALspec_range_splittable: forall n l, splittable (fun rsh sh => VALspec_range n rsh sh l).
Proof.
intro.
apply jam_noat_splittable.
apply VALspec_parametric.
Qed.

Lemma VALspec1: VALspec_range 1 = VALspec.
Proof.
unfold VALspec, VALspec_range.
extensionality rsh sh l.
f_equal.
unfold jam.
extensionality l'.
apply exist_ext; extensionality m.
symmetry.
if_tac.
 subst l'. rewrite if_true; auto.
destruct l; split; auto; omega.
rewrite if_false; auto.
destruct l; destruct l'; unfold block in *; intros [? ?]; try omega.
subst.
contradict H. f_equal; omega.
Qed.

Definition share_oblivious (P: pred rmap) :=
  forall w w',
   (forall l, match w' @ l , w @ l with
                 | NO _, NO _ => True
                 | YES _ sh1 k1 p1 , YES _ sh2 k2 p2 => k1=k2 /\ p1=p2
                 | PURE k1 p1, PURE k2 p2 => k1=k2 /\ p1=p2
                 | _ , _ => False
                 end) ->
     P w' -> P w.

Lemma intersection_splittable:
    forall (S': address -> address -> Prop) S P Q, 
         spec_parametric P -> 
         (forall l, share_oblivious (Q l)) ->
    forall l, splittable (fun rsh sh => allp (@jam _ _ _ _ _ _ (S' l) (S l) (P l rsh sh) noat) && Q l).
Proof.
intros.
intro; intros. rename H1 into HR; rename H2 into H1.
generalize (jam_noat_splittable S' S _ H); intro.
rewrite <- (H2  _ _ _  _ _ _ _ HR H1).
apply pred_ext; intros w ?.
destruct H3 as [w1 [w2 [? [[? ?] [? ?]]]]].
split.
exists w1; exists w2; auto.
eapply H0; eauto.
intro.
generalize (resource_at_join _ _ _ l0 H3).
case_eq (w2 @ l0); case_eq (w @ l0); intros; auto; try solve [inv H10].
case_eq (w1 @ l0); intros.
rewrite H11 in H10; inv H10. 
rewrite H11 in H10; inv H10.
specialize (H4 l0).
specialize (H6 l0).
hnf in H4,H6.
if_tac in H4; auto.
specialize (H l l0).
destruct H as [pp [ok ?]].
rewrite H in H4; rewrite H in H6.
destruct H4 as [? [? [? ?]]].
destruct H6 as [? [? [? ?]]].
inversion2 H11 H12.
inversion2 H9 H13.
do 3 red in H4. rewrite H11 in H4.
contradiction (YES_not_identity _ _ _ _ H4).
rewrite H11 in H10; inv H10.
destruct (w1 @ l0); inv H10; auto.
inv H10; auto.
destruct H3 as [[w1 [w2 [? [? ?]]]] ?].
exists w1; exists w2.
split; auto.
split; split; auto.
apply (H0 l w1 w).
intro l0; generalize (resource_at_join _ _ _ l0 H3).
case_eq (w @ l0); case_eq (w1 @ l0); intros; auto; try solve [inv H9].
case_eq (w2 @ l0); intros.
rewrite H10 in H9; inv H9. 
rewrite H10 in H9; inv H9.
specialize (H l l0).
destruct H as [pp [ok ?]].
specialize (H4 l0).
specialize (H5 l0).
hnf in H4,H5.
if_tac in H4.
rewrite H in H4,H5.
destruct H4 as [? [? [? ?]]].
destruct H5 as [? [? [? ?]]].
congruence.
do 3 red in H5. rewrite H10 in H5. 
contradiction (YES_not_identity _ _ _ _ H5).
rewrite H10 in H9; inv H9.
inv H9; auto.
inv H9; auto.
auto.
apply (H0 l w2 w ).
intro l0; generalize (resource_at_join _ _ _ l0 H3).
case_eq (w @ l0); case_eq (w2 @ l0); intros; auto; try solve [inv H9].
inv H9.
specialize (H l l0).
destruct H as [pp [ok ?]].
specialize (H4 l0).
specialize (H5 l0).
hnf in H4,H5.
if_tac in H4.
rewrite H in H4,H5.
destruct H4 as [? [? [? ?]]].
destruct H5 as [? [? [? ?]]].
congruence.
do 3 red in H4. rewrite <- H11 in H4.
contradiction (YES_not_identity _ _ _ _ H4).
inv H9; auto. inv H9; auto.
auto.
Qed.

Lemma VALspec_range_exp_address_mapsto:
  forall ch rsh sh l,
    (align_chunk ch | snd l) ->
    VALspec_range (size_chunk ch) rsh sh l |-- EX v: val, address_mapsto ch v rsh sh l.
Proof.
  intros.
  intros w ?.
  unfold VALspec_range in H0.
  simpl in H0 |- *.
  cut (exists (b0 : list memval),
     length b0 = size_chunk_nat ch /\
     (forall b1 : address,
      if adr_range_dec l (size_chunk ch) b1
      then
       exists p : nonunit sh,
         w @ b1 =
         YES rsh (mk_lifted sh p)
           (VAL (nth (nat_of_Z (snd b1 - snd l)) b0 Undef))
           (SomeP ((Void:Type) :: nil)
              (approx (level w) oo (fun _ : Void * unit => FF)))
      else identity (w @ b1))).
  Focus 1. {
    intros.
    destruct H1 as [b0 [? ?]].
    exists (decode_val ch b0), b0.
    tauto.
  } Unfocus.
  rewrite !size_chunk_conv in *.
  forget (size_chunk_nat ch) as n; clear - H0.
  
  cut (exists b0 : list memval,
     length b0 = n /\
     (forall b1 : address,
        adr_range l (Z.of_nat n) b1 ->
       exists p : nonunit sh,
         w @ b1 =
         YES rsh (mk_lifted sh p)
           (VAL (nth (nat_of_Z (snd b1 - snd l)) b0 Undef))
           (SomeP ((Void:Type) :: nil)
              (approx (level w) oo (fun _ : Void * unit => FF))))).
  Focus 1. {
    intros.
    destruct H as [b0 H].
    exists b0.
    split; [tauto |].
    intros b; specialize (H0 b).
    if_tac; [apply (proj2 H) |]; auto.
  } Unfocus.

  assert (forall b : address,
    adr_range l (Z.of_nat n) b ->
        exists (b0 : memval) (p : nonunit sh),
          w @ b =
          YES rsh (mk_lifted sh p) (VAL b0)
            (SomeP ((Void:Type) :: nil)
               (approx (level w) oo (fun _ : Void * unit => FF)))).
  Focus 1. {
    intros.
    specialize (H0 b).
    if_tac in H0; tauto.
  } Unfocus.
  clear H0.

  destruct l as [bl ofs].
  revert ofs H; induction n; intros.
  + exists nil.
    split; auto.
    intros b.
    specialize (H b).
    auto.
    intros.
    apply adr_range_non_zero in H0.
    simpl in H0; omega.
  + specialize (IHn (ofs + 1)).
    spec IHn.
    - clear - H; intros b; specialize (H b).
      intros; spec H; auto.
      apply adr_range_shift_1; auto.
    - assert (adr_range (bl, ofs) (Z.of_nat (S n)) (bl, ofs))
        by (rewrite Nat2Z.inj_succ; repeat split; auto; omega).
      destruct (H _ H0) as [b_hd ?H]; clear H0.
      destruct IHn as [b_tl ?H].
      exists (b_hd :: b_tl).
      split; [simpl; omega |]; destruct H0 as [_ ?].
      intros.
      apply adr_range_S_split in H2.
      destruct H2.
      * destruct (H0 b1 H2) as [p ?H].
        destruct b1; destruct H2 as [_ ?].
        exists p; clear - H2 H3.
        unfold snd in *.
        replace (nat_of_Z (z - ofs)) with (S (nat_of_Z (z - (ofs + 1)))); [exact H3 |].
        unfold nat_of_Z.
        replace (z - ofs) with (Z.succ (z - (ofs + 1))) by omega.
        rewrite Z2Nat.inj_succ; auto.
        omega.
      * subst. rewrite Z.sub_diag. simpl nth.
        exact H1.
Qed.

Lemma address_mapsto_VALspec_range:
  forall ch v rsh sh l,
        address_mapsto ch v rsh sh l |-- VALspec_range (size_chunk ch) rsh sh l.
Proof.
intros.
intros w ?. unfold VALspec_range.
destruct H as [bl [Hbl ?]].
intro l'.
spec H l'.
unfold jam in *.
hnf in H|-*. if_tac; auto.
exists (nth (nat_of_Z (snd l' - snd l)) bl Undef).
destruct H as [p ?].
exists p.
auto.
Qed.

Lemma approx_eq_i:
  forall (P Q: pred rmap) (w: rmap),
      (|> ! (P <=> Q)) w -> approx (level w) P = approx (level w) Q.
Proof.
intros.
apply pred_ext'; extensionality m'.
unfold approx.
apply and_ext'; auto; intros.
destruct (level_later_fash _ _ H0) as [m1 [? ?]].
specialize (H _ H1).
specialize (H m'). 
spec H.
rewrite H2; auto.
destruct H; apply prop_ext. intuition.
Qed.

Lemma level_later {A} `{H : ageable A}: forall {w: A} {n': nat}, 
         laterR (level w) n' ->
       exists w', laterR w w' /\ n' = level w'.
Proof.
intros.
remember (level w) as n.
revert w Heqn; induction H0; intros; subst.
case_eq (age1 w); intros.
exists a; split. constructor; auto.
symmetry; unfold age in H0; simpl in H0. 
  unfold natAge1 in H0; simpl in H0. revert H0; case_eq (level w); intros; inv H2.
  apply age_level in H1. congruence. rewrite age1_level0 in H1.
   rewrite H1 in H0. inv H0.
 specialize (IHclos_trans1 _ (refl_equal _)).
  destruct IHclos_trans1 as [w2 [? ?]].
  subst.
  specialize (IHclos_trans2 _ (refl_equal _)).
  destruct IHclos_trans2 as [w3 [? ?]].
  subst.
  exists w3; split; auto. econstructor 2; eauto.
Qed.


Lemma fun_assert_contractive:
   forall fml A (P Q: pred rmap -> A -> environ -> pred rmap) v, 
       (forall x vl, nonexpansive (fun R => P R x vl)) ->
      (forall x vl, nonexpansive (fun R => Q R x vl)) ->
      contractive (fun R : pred rmap => fun_assert fml A (P R) (Q R) v).
Proof.
intros.
assert (H': forall xvl: A * environ, nonexpansive (fun R => P R (fst xvl) (snd xvl)))
  by auto; clear H; rename H' into H.
assert (H': forall xvl: A * environ, nonexpansive (fun R => Q R (fst xvl) (snd xvl)))
  by auto; clear H0; rename H' into H0.
intro; intros.
rename H0 into H'.
intro; intros.
intro; intros; split; intros ? ? H7; simpl in H1.
assert (a >= level a')%nat.
 apply necR_level in H2. clear - H1 H2. apply le_trans with (level y); auto.
 clear y H1 H2. rename H3 into H2.
hnf.
destruct H7 as [loc H7].
hnf in H7. destruct H7 as [H1 H3].  hnf in H1.
exists loc.
apply prop_andp_i; auto.
split; auto.
hnf in H3|-*.
intro; spec H3 b.
hnf in H3|-*.
if_tac; auto.
subst b.
hnf in H3|-*.
rewrite H3; clear H3.
f_equal.
simpl.
f_equal.
extensionality xy.
unfold compose.
destruct xy as [x [y [vl [ ] ]]].
unfold packPQ.
simpl.
if_tac.
(* P proof *)
spec H (x,vl) P0 Q0.
apply approx_eq_i.
apply (later_derives (unfash_derives H)); clear H.
rewrite later_unfash.
unfold unfash.
red. red. 
apply pred_nec_hereditary with a; auto.
apply nec_nat; auto.
(* Q proof *)
clear H; rename H' into H.
spec H (x,vl) P0 Q0.
apply approx_eq_i.
apply (later_derives (unfash_derives H)); clear H.
rewrite later_unfash.
red. red. red.
apply pred_nec_hereditary with a; auto.
apply nec_nat; auto.
(* Part 2 *)
assert (a >= level a')%nat.
 apply necR_level in H2. clear - H1 H2. apply le_trans with (level y); auto.
 clear y H1 H2. rename H3 into H2.
unfold fun_assert.
destruct H7 as [loc H7].
hnf in H7. destruct H7 as [H1 H3].  hnf in H1.
exists loc.
apply prop_andp_i; auto.
split; auto.
hnf.
intro.
spec H3 b.
hnf in H3|-*.
if_tac; auto.
subst b.
hnf in H3|-*.
unfold yesat_raw in *.
rewrite H3; clear H3.
f_equal.
simpl.
f_equal.
unfold compose.
extensionality xy; destruct xy as [x [y [vl [ ] ]]].
unfold packPQ.
simpl.
if_tac.
(* P proof *)
spec H (x,vl) P0 Q0.
symmetry.
apply approx_eq_i.
apply (later_derives (unfash_derives H)); clear H.
rewrite later_unfash.
red. red. red.
apply pred_nec_hereditary with a; auto.
apply nec_nat; auto.
(* Q proof *)
clear H; rename H' into H.
spec H (x,vl) P0 Q0.
symmetry.
apply approx_eq_i.
apply (later_derives (unfash_derives H)); clear H.
rewrite later_unfash.
red. red. red.
apply pred_nec_hereditary with a; auto.
apply nec_nat; auto.
Qed.

Lemma VALspec_range_bytes_readable:
  forall n rsh sh loc m, VALspec_range n rsh sh loc m -> bytes_readable loc n m.
Proof.
intros; intro; intros.
unfold VALspec_range in H.
spec H (adr_add loc i).
hnf in H.
rewrite if_true in H.
destruct H as [v [p ?]].
hnf in H.
red. red. red.
rewrite H; auto.
destruct loc; split; unfold adr_add; auto.
simpl. omega.
Qed.

Lemma VALspec_range_bytes_writable:
  forall n rsh loc m, VALspec_range n rsh Share.top loc m -> bytes_writable loc n m.
Proof.
intros; intro; intros.
unfold VALspec_range in H.
spec H (adr_add loc i).
hnf in H.
rewrite if_true in H.
destruct H as [v [p ?]].
hnf in H.
do 3 red.
rewrite H; auto.
destruct loc; split; unfold adr_add; auto.
simpl. omega.
Qed.

Lemma yesat_join_sub:
  forall pp k l rsh sh m m',
          join_sub m m' ->
          yesat pp k rsh sh l m ->
         exists rsh', exists sh', yesat pp k rsh' sh' l m'.
Proof.
intros.
destruct H0.
unfold yesat_raw in H0.
generalize (resource_at_join_sub _ _ l H); rewrite H0; intro.
assert (level m = level m').
destruct H; apply join_level in H; intuition.
destruct H1.
destruct x0; case_eq (m' @ l); intros; rewrite H3 in H1; inv H1.
do 3 econstructor. unfold yesat_raw. simpl. rewrite <- H2.  eapply H3.
destruct p1.
exists t0,x0.
unfold yesat. exists n.
unfold yesat_raw. simpl. rewrite <- H2. rewrite H3.
subst; f_equal; auto.
Qed.

Lemma VALspec_range_precise: forall n rsh sh l,  precise (VALspec_range n rsh sh l).
Proof.
intros.
intro; intros.
apply rmap_ext; auto.
1: destruct H1,H2; apply join_level in H1; apply join_level in H2; intuition.
intro.
specialize (H l0); specialize (H0 l0).
unfold jam in *.
hnf in H, H0. if_tac in H.
+ destruct H as [v [p ?]].
  destruct H0 as [v' [p' ?]].
  unfold yesat_raw in *.
  generalize (resource_at_join_sub _ _ l0 H1); rewrite H; clear H1; intro.
  generalize (resource_at_join_sub _ _ l0 H2); rewrite H0; clear H2; intro.
  f_equal. auto.
  clear - H1 H2.
  destruct H1; destruct H2.
  simpl in *.
  f_equal.
  inv H0; inv H; congruence.
  repeat rewrite preds_fmap_NoneP; auto.
+ do 3 red in H,H0.
  destruct H1.
  destruct H2.
  apply (resource_at_join _ _ _ l0) in H1.
  apply (resource_at_join _ _ _ l0) in H2.
  assert (x0 @ l0 = x @ l0).
  apply H in H1.
  apply H0 in H2.
  congruence.
  rewrite H4 in *. eapply join_canc; eauto.
Qed.

Lemma nonlock_permission_bytes_precise: forall sh p n,
  precise (nonlock_permission_bytes sh p n).
Proof.
  intros.
  intro; intros.
  apply rmap_ext; auto.
  1: destruct H1,H2; apply join_level in H1; apply join_level in H2; intuition.
  intro.
  specialize (H l); specialize (H0 l).
  unfold jam in *.
  hnf in H, H0. if_tac in H.
  + unfold shareat, nonlockat in H, H0; simpl in H, H0.
    apply (resource_at_join_sub _ _ l) in H1.
    apply (resource_at_join_sub _ _ l) in H2.
    destruct H as [? _], H0 as [? _].
    apply (join_sub_is_general_slice_resource _ _ _ H1) in H.
    apply (join_sub_is_general_slice_resource _ _ _ H2) in H0.
    congruence.
  + do 3 red in H,H0.
    destruct H1.
    destruct H2.
    apply (resource_at_join _ _ _ l) in H1.
    apply (resource_at_join _ _ _ l) in H2.
    assert (x0 @ l = x @ l).
    apply H in H1.
    apply H0 in H2.
    congruence.
    rewrite H4 in *. eapply join_canc; eauto.
Qed.

Lemma address_mapsto_precise: forall ch v rsh sh l, precise (address_mapsto ch v rsh sh l).
Proof.
intros.
apply (derives_precise _ _ (address_mapsto_VALspec_range ch v rsh sh l)).
apply VALspec_range_precise.
Qed.

Program Definition core_load (ch: memory_chunk) (l: address) (v: val): pred rmap :=
  EX bl: list memval, 
  !!(length bl = size_chunk_nat ch /\ decode_val ch bl = v /\ (align_chunk ch | snd l)) &&
    allp (jam (adr_range_dec l (size_chunk ch))
      (fun l' phi => exists rsh, exists sh, exists p, phi @ l' 
        = YES rsh (mk_lifted sh p) (VAL (nth (nat_of_Z (snd l' - snd l)) bl Undef)) NoneP)
      (fun _ _ => True)).
 Next Obligation.
    intros; intro; intros.
  destruct H0 as [rsh [sh [p ?]]]; exists rsh, sh, p.
    apply (age1_YES a a'); auto.
  Qed.
  Next Obligation.     intros; intro; intros. auto. 
  Qed.

Program Definition core_load' (ch: memory_chunk) (l: address) (v: val) (bl: list memval)
  : pred rmap := 
  !!(length bl = size_chunk_nat ch /\ decode_val ch bl = v /\ (align_chunk ch | snd l)) &&
    allp (jam (adr_range_dec l (size_chunk ch))
      (fun l' phi => exists rsh, exists sh, exists p, phi @ l' 
        = YES rsh (mk_lifted sh p) (VAL (nth (nat_of_Z (snd l' - snd l)) bl Undef)) NoneP)
      (fun _ _ => True)).
 Next Obligation.
    intros; intro; intros.
  destruct H0 as [rsh [sh [p ?]]]; exists rsh, sh; exists p.
    apply (age1_YES a a'); auto.
  Qed.
  Next Obligation.     intros; intro; intros. auto. 
  Qed.

Lemma VALspec_range_0: forall rsh sh loc, VALspec_range 0 rsh sh loc = emp.
  Proof.
   intros.
   apply pred_ext.
   intros ? ?. simpl in H.
   do 3 red.
   apply all_resource_at_identity.
   intro l. specialize (H l).
   rewrite if_false in H; auto.
   destruct loc, l; intros [? ?]; simpl in *; omega.
   intros ? ?. intro b. rewrite jam_false.
   do 3 red. apply resource_at_identity; auto.
   destruct loc, b; intros [? ?]; simpl in *; omega.
Qed.
Hint Resolve VALspec_range_0: normalize.

Lemma nonlock_permission_bytes_0: forall sh a, nonlock_permission_bytes sh a 0 = emp.
Proof.
  intros.
  apply pred_ext.
  + intros ? ?. simpl in H.
    do 3 red.
    apply all_resource_at_identity.
    intro l. specialize (H l).
    rewrite if_false in H; auto.
    destruct a, l; intros [? ?]; simpl in *; omega.
  + intros ? ?. intro b. rewrite jam_false.
    do 3 red. apply resource_at_identity; auto.
    destruct a, b; intros [? ?]; simpl in *; omega.
Qed.

Lemma nonlock_permission_bytes_not_nonunit: forall sh p n,
  ~ nonunit sh ->
  nonlock_permission_bytes sh p n |-- emp.
Proof.
  intros.
  assert (sh = Share.bot).
  Focus 1. {
    destruct (dec_share_identity sh).
    + apply identity_share_bot; auto.
    + apply nonidentity_nonunit in n0; tauto.
  } Unfocus.
  subst.
  intros ? ?. simpl in H.
  do 3 red.
  apply all_resource_at_identity.
  intro l.
  specialize (H0 l); simpl in H0.
  if_tac in H0; [| auto].
  destruct H0.
  destruct (a @ l); inv H0.
  + rewrite <- splice_bot2 in H4.
    rewrite <- (Share.unrel_splice_L t Share.bot), H4, unrel_bot.
    apply NO_identity.
  + assert (pshare_sh p0 = Share.bot) by
      (rewrite <- (Share.unrel_splice_R t (pshare_sh p0)), H4, unrel_bot; auto).
    pose proof pshare_not_identity p0.
    pose proof bot_identity.
    rewrite H0 in H3; tauto.
Qed.

Lemma is_resource_pred_YES_VAL rsh sh:
  is_resource_pred
    (fun l' => EX  v: memval, yesat NoneP (VAL v) rsh sh l')
    (fun r n => (exists b0 p, r = YES rsh (mk_lifted sh p) (VAL b0)
        (SomeP ((Void:Type) :: nil) (approx n oo (fun _ : Void * unit => FF))))).
Proof. hnf; intros. reflexivity. Qed.

Lemma is_resource_pred_nonlock_shareat sh:
  is_resource_pred
    (fun i : address => shareat i sh && nonlockat i)
    (fun r _ => resource_share r = Some sh /\ nonlock r).
Proof. hnf; intros. reflexivity. Qed.

Lemma VALspec_range_split2:
  forall (n m r: Z) (rsh sh: Share.t) (b: block) (ofs: Z),
    r = n + m -> n >= 0 -> m >= 0 ->
    VALspec_range r rsh sh (b, ofs) = 
    VALspec_range n rsh sh (b, ofs) * VALspec_range m rsh sh (b, ofs + n).
Proof.
  intros.
  assert (exists resp, is_resource_pred (fun l' => EX  v: memval, yesat NoneP (VAL v) rsh sh l') resp) by (eexists; apply is_resource_pred_YES_VAL).
  apply allp_jam_split2; auto.
  + split; intros [? ?]; unfold adr_range.
    - assert (ofs <= z < ofs + r <-> ofs <= z < ofs + n \/ ofs + n <= z < ofs + n + m) by omega.
      tauto.
    - omega.
  + intros.
    simpl in H4.
    destruct (m0 @ l); try solve [inversion H5; simpl; auto].
    destruct H4 as [? [? ?]].
    inversion H4; subst.
    inversion H5; subst.
    auto.
Qed.

Lemma nonlock_permission_bytes_split2:
  forall (n m r: Z) (sh: Share.t) (b: block) (ofs: Z),
    r = n + m -> n >= 0 -> m >= 0 ->
    nonlock_permission_bytes sh (b, ofs) r = 
    nonlock_permission_bytes sh (b, ofs) n *
    nonlock_permission_bytes sh (b, ofs + n) m.
Proof.
  intros.
  assert (exists resp, is_resource_pred (fun i : address => shareat i sh && nonlockat i) resp) by (eexists; apply is_resource_pred_nonlock_shareat).
  apply allp_jam_split2; auto.
  + split; intros [? ?]; unfold adr_range.
    - assert (ofs <= z < ofs + r <-> ofs <= z < ofs + n \/ ofs + n <= z < ofs + n + m) by omega.
      tauto.
    - omega.
  + intros.
    destruct H4 as [_ ?].
    simpl in H4.   
    destruct (m0 @ l); inv H5.
    simpl in H4; auto.
Qed.

Lemma VALspec_range_VALspec:
  forall (n : Z) (v : val) (rsh sh : Share.t) (l : address) (i : Z),
       0 <= i < n ->
       VALspec_range n rsh sh l
       |-- VALspec rsh sh (adr_add l i) * TT.
Proof.
 intros.
  destruct l as [b ofs].
  rewrite (VALspec_range_split2 i (n-i) n rsh sh b ofs); try omega.
  rewrite (VALspec_range_split2 1 (n-i-1) (n-i) rsh sh b (ofs+i)); try omega.
  change (VALspec_range 1) with (VALspec_range 1).
  rewrite VALspec1.
  rewrite <- sepcon_assoc.
  rewrite (sepcon_comm (VALspec_range i rsh sh (b, ofs))).
  rewrite sepcon_assoc.
  apply sepcon_derives; auto.
Qed.

Lemma VALspec_range_overlap': forall rsh sh p1 p2 n1 n2,
  adr_range p1 n1 p2 ->
  n2 > 0 ->
  VALspec_range n1 rsh sh p1 * VALspec_range n2 rsh sh p2 |-- FF.
Proof.
  intros.
  intros w [w1 [w2 [? [? ?]]]].
  spec H2 p2.
  spec H3 p2.
  rewrite jam_true in H2 by auto.
  rewrite jam_true in H3 by (destruct p2; simpl; split; auto; omega).
  destruct H2; destruct H3. hnf in H2,H3.
  apply (resource_at_join _ _ _ p2) in H1.
  destruct H2, H3.
  rewrite H2, H3 in H1.
  clear - x1 H1; simpl in H1.
  inv H1.
  do 3 red in H0. simpl in H0.
  generalize (join_self H0); intro.
  rewrite <- H in H0.
  apply x2 in H0. contradiction.
Qed.

Lemma address_mapsto_overlap':
  forall rsh sh ch1 v1 ch2 v2 a1 a2,
     adr_range a1 (size_chunk ch1) a2 ->
     address_mapsto ch1 v1 rsh sh a1 * address_mapsto ch2 v2 rsh sh a2 |-- FF.
Proof.
  intros.
  eapply derives_trans; [eapply sepcon_derives | apply VALspec_range_overlap'].
  + apply address_mapsto_VALspec_range.
  + apply address_mapsto_VALspec_range.
  + auto.
  + apply size_chunk_pos.
Qed.

Lemma VALspec_range_overlap: forall rsh sh l1 n1 l2 n2,
  range_overlap l1 n1 l2 n2 ->
  VALspec_range n1 rsh sh l1 * VALspec_range n2 rsh sh l2 |-- FF.
Proof.
  intros.
  pose proof range_overlap_non_zero _ _ _ _ H.
  apply range_overlap_spec in H; try tauto.
  destruct H.
  + apply VALspec_range_overlap'; tauto.
  + rewrite sepcon_comm.
    apply VALspec_range_overlap'; tauto.
Qed.

Lemma address_mapsto_overlap: forall rsh sh l1 ch1 v1 l2 ch2 v2,
  range_overlap l1 (size_chunk ch1) l2 (size_chunk ch2) ->
  address_mapsto ch1 v1 rsh sh l1 * address_mapsto ch2 v2 rsh sh l2 |-- FF.
Proof.
  intros.
  apply range_overlap_spec in H; try apply size_chunk_pos.
  destruct H.
  + apply address_mapsto_overlap'; auto.
  + rewrite sepcon_comm.
    apply address_mapsto_overlap'; auto.
Qed.

Lemma share_joins_self: forall sh: share, joins sh sh -> nonunit sh -> False.
Proof.
  intros.
  destruct H as [sh' ?].
  pose proof join_self H.
  subst.
  apply H0 in H.
  auto.
Qed.

Lemma nonlock_permission_bytes_overlap:
  forall sh n1 n2 p1 p2,
  nonunit sh ->
  range_overlap p1 n1 p2 n2 ->
  nonlock_permission_bytes sh p1 n1 * nonlock_permission_bytes sh p2 n2 |-- FF.
Proof.
  intros.
  apply allp_jam_overlap.
  + eexists. apply is_resource_pred_nonlock_shareat.
  + eexists. apply is_resource_pred_nonlock_shareat.
  + unfold shareat; simpl; intros.
    destruct H3 as [w ?].
    apply (resource_at_join _ _ _ l) in H3.
    pose proof resource_share_joins (w1 @ l) (w2 @ l) sh sh.
    do 2 (spec H4; [tauto |]).
    spec H4; [firstorder |].
    apply (share_joins_self sh); auto.
  + auto.
Qed.

Lemma VALspec_range_nonlock_permission_bytes_overlap: forall rsh sh sh' p1 p2 n1 n2,
  range_overlap p1 n1 p2 n2 ->
  ~ joins (Share.splice rsh sh) sh' ->
  VALspec_range n1 rsh sh p1 * nonlock_permission_bytes sh' p2 n2 |-- FF.
Abort.

Lemma nonlock_permission_bytes_share_join:
 forall sh1 sh2 sh a n,
  join sh1 sh2 sh ->
  nonlock_permission_bytes sh1 a n *
  nonlock_permission_bytes sh2 a n =
  nonlock_permission_bytes sh a n.
Proof.
  intros.
  symmetry.
  apply allp_jam_share_split.
  do 3 eexists.
  exists sh, sh1, sh2.
  split; [| split; [| split; [| split; [| split]]]].
  + apply is_resource_pred_nonlock_shareat.
  + apply is_resource_pred_nonlock_shareat.
  + apply is_resource_pred_nonlock_shareat.
  + auto.
  + simpl; intros.
    destruct H0.
    split; [auto |].
    split; split.
    - eapply general_slice_resource_resource_share; [eauto | eexists; eauto].
    - eapply general_slice_resource_nonlock; [eauto | eexists; eauto | auto].
    - eapply general_slice_resource_resource_share; [eauto | eexists; eapply join_comm; eauto].
    - eapply general_slice_resource_nonlock; [eauto | eexists; eapply join_comm; eauto | auto].
  + simpl; intros.
    destruct H1, H2.
    split.
    - eapply (resource_share_join q_res r_res); eauto.
    - eapply (nonlock_join q_res r_res); eauto.
Qed.

Lemma address_mapsto_share_join:
 forall (rsh1 rsh2 rsh sh1 sh2 sh : share) ch v a,
   sepalg.join rsh1 rsh2 rsh ->
   sepalg.join sh1 sh2 sh ->
   address_mapsto ch v rsh1 sh1 a * address_mapsto ch v rsh2 sh2 a 
    = address_mapsto ch v rsh sh a.
Proof.
intros.
Admitted. 

Lemma nonlock_permission_bytes_address_mapsto_join:
 forall (sh1 sh2 sh : share) ch v a,
   sepalg.join sh1 sh2 sh ->
   nonlock_permission_bytes sh1 a (Memdata.size_chunk ch)
     * address_mapsto ch v (Share.unrel Share.Lsh sh2) (Share.unrel Share.Rsh sh2) a 
    = address_mapsto ch v (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) a.
Proof.
Admitted.

Lemma address_mapsto_value_cohere:
  forall ch v1 v2 rsh1 sh1 rsh2 sh2 a,
 address_mapsto ch v1 rsh1 sh1 a * address_mapsto ch v2 rsh2 sh2 a |-- !! (v1=v2).
Proof.
Admitted. 
