Require Import VST.msl.log_normalize.
Require Export VST.veric.base.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.  
Require Import VST.veric.shares. 
Require Import VST.veric.address_conflict.

Import RML. Import R.
Local Open Scope pred.


Program Definition kind_at (k: kind) (l: address) : pred rmap :=
   fun m => exists rsh, exists sh, exists pp, m @ l = YES rsh sh k pp.
 Next Obligation.
   try intro; intros.
   destruct H0 as [rsh [sh [pp ?]]].
   generalize (eq_sym (resource_at_approx a l)); intro.
   generalize (age1_resource_at a a'  H l (a@l) H1); intro.
   rewrite H0 in H2. simpl in H2. eauto.
 Qed.

Definition spec : Type :=  forall (sh: Share.t) (l: AV.address), pred rmap.

Program Definition yesat_raw (pp: preds) (k: kind) 
                           (sh: share) (rsh: readable_share sh) (l: address) : pred rmap :=
   fun phi => phi @ l = YES sh rsh k (preds_fmap (approx (level phi)) (approx (level phi)) pp).
  Next Obligation.
   try intro; intros.
   apply (age1_resource_at a a' H l (YES sh rsh k pp) H0).
  Qed.

Obligation Tactic := idtac.

Program Definition yesat (pp: preds) (k: kind) : spec :=
 fun (sh: share) (l: AV.address) (m: rmap) =>
  exists rsh, yesat_raw pp k sh rsh l m.
  Next Obligation.
    intros; intro; intros.
    destruct H0 as [p ?]; exists p.
    apply pred_hereditary with a; auto.
  Qed.

Program Definition pureat (pp: preds) (k: kind) (l: AV.address): pred rmap :=
       fun phi => phi @ l = PURE k (preds_fmap (approx (level phi)) (approx (level phi)) pp).
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
     resource_fmap (approx (level phi)) (approx (level phi)) (phi @ l) =
     resource_fmap (approx (level phi)) (approx (level phi)) (YES rsh sh k pp)).
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
   resource_fmap (approx (level phi)) (approx (level phi)) (phi @ l) =
   resource_fmap (approx (level phi)) (approx (level phi)) (YES rsh sh k pp))
   (yesat_raw_eq_aux pp k rsh sh l)) : pred rmap).
Proof.
unfold yesat_raw.
extensionality pp k rsh sh l.
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
f_equal; try apply proof_irr.
revert H4; destruct p as [?A ?p]; destruct pp as [?A ?p]; simpl; intros; auto; inv H4.
clear - H.
repeat f_equal.
revert H; unfold resource_at.  rewrite rmap_level_eq.
case_eq (unsquash phi); simpl; intros.
rename r0 into f.
pose proof I.
set (phi' := ((fun l' => if eq_dec l' l 
       then YES rsh r k (SomeP A0 (fun i => fmap _ (approx n) (approx n) (p i))) else fst f l', snd f)): rmap').
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
unfold rmap_fmap.
unfold compose.
f_equal.
extensionality x.
simpl.
if_tac; auto.
subst.
rewrite H0.
simpl.
do 2 apply f_equal.
extensionality.
rewrite fmap_app.
rewrite approx_oo_approx; auto.
subst phi.
unfold phi' in H.
rewrite unsquash_squash in H.
injection H; clear H; intros.
destruct f; simpl in *; inv H.
generalize (equal_f H3 l); intro.
rewrite H0 in H.
clear - H.
unfold compose in H. rewrite if_true in H; auto.
simpl in H.
revert H; generalize p at 2 3.
intros q ?H.
apply YES_inj in H.
match goal with
| H: ?A = ?B |- _ =>
  assert (snd A = snd B)
end.
rewrite H; auto.
simpl in H0.
apply SomeP_inj2 in H0.
subst q.
extensionality i.
rewrite fmap_app.
rewrite approx_oo_approx. auto.
Qed.

Lemma yesat_eq_aux: 
  forall pp k sh l, 
    hereditary age
    (fun m : rmap =>
      exists rsh, 
     resource_fmap (approx (level m)) (approx (level m)) (m @ l) =
     resource_fmap (approx (level m)) (approx (level m)) (YES sh rsh k pp)).
Proof.
 intros.
  intro; intros.
  destruct H0 as [p ?]; exists p.
  rewrite resource_at_approx.
  rewrite resource_at_approx in H0.
  apply (age1_resource_at a a' H); auto.
Qed.

Lemma yesat_eq: yesat = fun pp k sh l =>
 exist (hereditary age)
  (fun m => 
  exists rsh, 
   resource_fmap (approx (level m)) (approx (level m)) (m @ l) = 
   resource_fmap (approx (level m)) (approx (level m)) (YES sh rsh k pp))
   (yesat_eq_aux pp k sh l).
Proof.
unfold yesat.
extensionality pp k sh l.
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

Definition resource_share (r: resource) : option share :=
 match r with
 | YES sh _ _ _ => Some sh
 | NO sh _ => Some sh
 | PURE _ _ => None
 end.

Definition nonlock (r: resource) : Prop :=
 match r with
 | YES _ _ k _ => isVAL k \/ isFUN k
 | NO _ _ => True
 | PURE _ _ => False
 end.

Lemma age1_nonlock: forall phi phi' l,
  age1 phi = Some phi' -> (nonlock (phi @ l) <-> nonlock (phi' @ l)).
Proof.
  intros.
  destruct (phi @ l) as [rsh | rsh sh k P |] eqn:?H.
  + pose proof (age1_NO phi phi' l rsh n H).
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
  + pose proof (age1_NO phi phi' l rsh n H).
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
  eexists; split; eauto.
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
    + rewrite (necR_NO a a' l _ n) in H1 by (constructor; auto).
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
    + rewrite (necR_NO a a' l _ n) in H1 by (constructor; auto).
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

(*Lemma allp_noat_emp: allp noat = emp.
Proof.
  apply pred_ext; unfold derives; intros; simpl in *.
  + apply all_resource_at_identity.
    exact H.
  + intros. apply resource_at_identity.
    exact H.
Qed.*)

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
(*
Implicit Arguments jam_vacuous.
*)
Lemma make_sub_rmap: forall w (P: address -> Prop) (P_DEC: forall l, {P l} + {~ P l}),
  (forall l sh k, P l -> res_option (w @ l) = Some (sh, k) -> isVAL k \/ isFUN k) ->
  {w' | level w' = level w /\ resource_at w' =
       (fun l => if P_DEC l then w @ l else core (w @ l)) /\ ghost_of w' = ghost_of w}.
Proof.
  intros.
  apply remake_rmap.
  intros.
    if_tac; [left; eauto |].
    destruct (w @ l) eqn:?H; rewrite ?core_NO, ?core_YES, ?core_PURE; simpl; auto.
    left.
    exists w; split; auto.
    apply ghost_of_approx.
Qed.

Definition is_resource_pred (p: address -> pred rmap) (q: resource -> address -> nat -> Prop) :=
  forall l w, (p l) w = q (w @ l) l (level w).

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

Program Definition noghost : pred rmap := fun m => identity (ghost_of m).
Next Obligation.
Proof.
  intros ????.
  rewrite (age1_ghost_of _ _ H), (identity_core H0), ghost_core; simpl.
  rewrite <- (ghost_core nil); apply core_identity.
Defined.

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
  allp (jam P_DEC p noat) && noghost =
  (allp (jam Q_DEC q noat) && noghost) * (allp (jam R_DEC r noat) && noghost).
Proof.
  intros until R_DEC.
  intros ST_P ST_Q ST_R.
  intros [? ?] ? ? ?.
  apply pred_ext; intros w; simpl; intros.
  + destruct (make_sub_rmap w Q Q_DEC) as [w1 [? ?]].
    {
      intros. eapply H3; [| | eauto].
      + firstorder.
      + destruct H4; specialize (H4 l); if_tac in H4; [auto | firstorder].
    }
    destruct (make_sub_rmap w R R_DEC) as [w2 [? ?]].
    {
      intros. eapply H3; [| | eauto].
      + firstorder.
      + destruct H4; specialize (H4 l); if_tac in H4; [auto | firstorder].
    }
    exists w1, w2.
    split3; auto.
    - apply resource_at_join2; try congruence.
      intro l.
      destruct H6, H8.
      rewrite H6, H8.
      pose proof core_unit (w @ l).
      destruct (Q_DEC l), (R_DEC l).
      * firstorder.
      * apply join_comm; auto.
      * auto.
      * destruct H4; specialize (H4 l).
        rewrite if_false in H4 by firstorder.
        rewrite identity_core by auto.
        apply core_duplicable.
      * destruct H6 as [_ ->], H8 as [_ ->].
        destruct H4; apply identity_unit'; auto.
    - split.
      intros l.
      destruct H4; specialize (H4 l).
      if_tac.
      * rewrite <- H1 by auto.
        rewrite if_true in H4 by firstorder.
        erewrite <- (is_resource_pred_resource_stable ST_P); [eauto | | auto].
        destruct H6; rewrite H6, if_true by auto; auto.
      * destruct H6; rewrite H6, if_false by auto.
        apply core_identity.
      * destruct H4, H6 as [_ ->]; auto.
    - split.
      intros l.
      destruct H4; specialize (H4 l).
      if_tac.
      * rewrite <- H2 by auto.
        rewrite if_true in H4 by firstorder.
        erewrite <- (is_resource_pred_resource_stable ST_P); [eauto | | auto].
        destruct H8; rewrite H8, if_true by auto; auto.
      * destruct H8; rewrite H8, if_false by auto.
        apply core_identity.
      * destruct H4, H8 as [_ ->]; auto.
  + destruct H4 as [y [z [? [[? Hg1] [? Hg2]]]]].
    split; intros.
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
    - apply ghost_of_join in H4.
      rewrite <- (Hg1 _ _ H4); auto.
Qed.


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
  forall pp pp' k k' sh sh' l w, k <> k' -> 
                  yesat pp k sh l w -> yesat pp' k' sh' l w -> False.
Proof.
unfold yesat, yesat_raw; intros.
destruct H0 as [p ?]. destruct H1 as [p' ?].
simpl in *; inversion2 H0 H1.
contradiction H; auto.
Qed.

Lemma yesat_raw_join:
  forall pp k (sh1 sh2 sh3: Share.t) rsh1 rsh2 rsh3 l phi1 phi2 phi3,
   join sh1 sh2 sh3 ->
   yesat_raw pp k sh1 rsh1 l phi1 ->
   yesat_raw pp k sh2 rsh2 l phi2 ->
   join phi1 phi2 phi3 ->
   yesat_raw pp k sh3 rsh3 l phi3.
Proof.
unfold yesat_raw;
intros until 1; rename H into HR; intros.
simpl in H,H0|-*.
assert (level phi2 = level phi3) by (apply join_level in H1; intuition).
rewrite H2 in *; clear H2.
assert (level phi1 = level phi3) by  (apply join_level in H1; intuition).
rewrite H2 in *; clear H2.
generalize (resource_at_join _ _ _ l H1); clear H1.
revert H H0.
case_eq (phi1 @ l); intros; try discriminate.
inv H0.
revert H1 H2; case_eq (phi2 @ l); intros; try discriminate.
inv H1.
inv H2.
inv H0.
pose proof (join_eq HR RJ). subst sh5. clear RJ.
repeat proof_irr. auto.
Qed.

Lemma nonunit_join: forall A {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Disj_alg A} (x y z: A),
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
  forall pp k sh1 sh2 sh3 l m1 m2 m3,
   join sh1 sh2 sh3 ->   
   yesat pp k sh1 l m1 ->
   yesat pp k sh2 l m2 ->
   join m1 m2 m3 ->
   yesat pp k sh3 l m3.
Proof.
intros.
destruct H0 as [p1 ?].
destruct H1 as [p2 ?].
assert (p3: readable_share sh3).
eapply join_readable1; eauto.
exists p3.
eapply yesat_raw_join with (phi1 := m1); eauto.
Qed.

Definition spec_parametric (Q: address -> spec) : Prop :=
   forall l l', exists pp, exists ok,
             forall sh m,
           Q l sh l' m = 
            (exists p, exists k, ok k /\ m @ l' = 
                 YES sh p k (preds_fmap (approx (level m)) (approx (level m)) pp)).

Lemma YES_ext:
  forall sh sh' rsh rsh' k p, sh=sh' -> YES sh rsh k p = YES sh' rsh' k p.
Proof.
intros. subst. f_equal. apply proof_irr.
Qed.

(****** Specific specs  ****************)

(* Memory predicates need to explicitly not capture any ghost state. *)
Definition VALspec : spec :=
       fun (sh: Share.t) (l: address) =>
          allp (jam (eq_dec l)
                                  (fun l' => EX v: memval, 
                                                yesat NoneP (VAL v) sh l')
                                  noat) && noghost.

Definition VALspec_range (n: Z) : spec :=
     fun (sh: Share.t) (l: address) =>
          andp (allp (jam (adr_range_dec l n)
                                  (fun l' => EX v: memval, 
                                                yesat NoneP (VAL v) sh l')
                                  noat)) noghost.

Definition nonlock_permission_bytes (sh: share) (a: address) (n: Z) : pred rmap :=
  andp (allp (jam (adr_range_dec a n) (fun i => shareat i sh && nonlockat i) noat)) noghost.

Definition nthbyte (n: Z) (l: list memval) : memval :=
     nth (nat_of_Z n) l Undef.

(*  Unfortunately address_mapsto_old, while a more elegant definition than
   address_mapsto, is not quite right.  For example, it doesn't uniquely determine v *)
Definition address_mapsto_old (ch: memory_chunk) (v: val) : spec :=
        fun (sh: Share.t) (l: AV.address)  => 
             allp (jam (adr_range_dec l (size_chunk ch)) 
                              (fun l' => yesat NoneP (VAL (nthbyte (snd l' - snd l) (encode_val ch v))) sh l')
                           noat).

Definition address_mapsto (ch: memory_chunk) (v: val) : spec :=
        fun (sh: Share.t) (l: AV.address) =>
           EX bl: list memval, 
               !! (length bl = size_chunk_nat ch  /\ decode_val ch bl = v /\ (align_chunk ch | snd l))  &&
                (allp (jam (adr_range_dec l (size_chunk ch))
                                    (fun loc => yesat NoneP (VAL (nth (nat_of_Z (snd loc - snd l)) bl Undef)) sh loc)
                                    noat)) && noghost.

Lemma address_mapsto_align: forall ch v sh l,
  address_mapsto ch v sh l = address_mapsto ch v sh l && !! (align_chunk ch | snd l).
Proof.
  intros.
  pose proof (@add_andp (pred rmap) _); simpl in H. apply H; clear H.
  unfold address_mapsto.
  apply exp_left; intro.
  do 2 apply andp_left1.
  intros ? [? [? ?]].
  auto.
Qed.

Lemma address_mapsto_fun:
  forall ch sh sh' l v v',
          (address_mapsto ch v sh l * TT) && (address_mapsto ch v' sh' l * TT) |-- !!(v=v').
Proof.
intros.
intros m [? ?]. unfold prop.
destruct H as [m1 [m2 [J [[bl [[[Hlen [? _]] ?] Hg]] _]]]].
destruct H0 as [m1' [m2' [J' [[bl' [[[Hlen' [? _]] ?] Hg']] _]]]].
subst.
assert (forall i, nth_error bl i = nth_error bl' i).
intro i; specialize( H1 (fst l, snd l + Z_of_nat i)); specialize( H2 (fst l, snd l + Z_of_nat i)).
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
specialize( H (S i)).
simpl in H.
auto.
simpl; auto.
Qed.

Definition LKspec lock_size (R: pred rmap) : spec :=
   fun (sh: Share.t) (l: AV.address)  =>
    allp (jam (adr_range_dec l lock_size)
               (fun l' => yesat (SomeP Mpred (fun _ => R)) (LK lock_size (snd l' - snd l)) sh l')
               noat) && noghost.

(*Lenb: moved to veric/seplog.v
Definition packPQ {A: rmaps.TypeTree}
  (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)):
  forall ts, dependent_type_functor_rec ts (SpecTT A) (pred rmap) :=
  fun ts a b => if b then P ts a else Q ts a.
*)
Definition TTat (l: address) : pred rmap := TT.

(*
Definition FUNspec (fml: funsig) cc (A: TypeTree)
  (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap))
  (l: address): pred rmap :=
  allp (jam (eq_dec l)
         (pureat (SomeP (SpecTT A) (packPQ P Q)) (FUN fml cc)) TTat).

Definition fun_assert (fml: funsig) cc (A: TypeTree)
  (P Q: forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap))
  (v: val)  : pred rmap :=
 (EX b : block, !! (v = Vptr b Int.zero) && FUNspec fml cc A P Q (b, 0))%pred.
*)

(***********)

(*Lenb: dead?
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
Qed.*)

Lemma address_mapsto_old_parametric: forall ch v, 
   spec_parametric (fun l sh l' => yesat NoneP (VAL (nthbyte (snd l' - snd l) (encode_val ch v))) sh l').
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
  spec_parametric (fun l sh l' => EX v: memval,  yesat NoneP (VAL v) sh l').
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

Lemma LKspec_parametric lock_size: forall R: pred rmap,
  spec_parametric (fun l sh l' => yesat (SomeP Mpred (fun _ => R)) (LK lock_size (snd l' - snd l)) sh l').
Proof.
intros.
unfold jam.
intro; intros.
simpl.
exists (SomeP Mpred (fun _ => R)).
exists (fun k => k = LK lock_size (snd l' - snd l)).
intros.
apply exists_ext; intro p.
apply prop_ext; split; intros.
rewrite H.
econstructor.  split; eauto.

destruct H as [k [? ?]].
subst; auto.
Qed.

(*
Lemma FUNspec_parametric: forall fml cc A P Q,
   spec_parametric (fun l sh => yesat (SomeP (SpecTT A) (packPQ P Q)) (FUN fml cc) sh).
Proof.
intros.
exists (SomeP (SpecTT A) (packPQ P Q)).
exists (fun k => k=FUN fml cc).
intros.
simpl.
apply exists_ext; intro p.
unfold yesat_raw.
apply prop_ext; split; intros.
econstructor; eauto.
destruct H as [k [? ?]].
subst; auto.
Qed.
*)
Definition val2address (v: val) : option AV.address := 
  match v with Vptr b ofs => Some (b, Ptrofs.signed ofs) | _ => None end.

Lemma VALspec_readable:
  forall l sh w,  (VALspec sh l * TT) %pred w -> readable l w.
(* The converse is not quite true, because "readable" does constraint to NoneP *)
Proof.
unfold VALspec, readable;
intros.
destruct H as [w1 [w2 [? [[? ?] _]]]].
specialize ( H0 l).
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
  forall ch v sh l i, 0 <= i < size_chunk ch ->
        address_mapsto ch v sh l |-- VALspec sh (adr_add l i) * TT.
Proof.
intros. intros w ?.
pose (f l' := if eq_dec (adr_add l i) l' then w @ l' 
                   else if adr_range_dec l (size_chunk ch) l' then NO Share.bot bot_unreadable else w @ l').
pose (g l' := if eq_dec (adr_add l i) l' then NO Share.bot bot_unreadable else w @ l').
exploit (deallocate (w) f g); intros.
*
unfold f,g; clear f g.
destruct H0 as [b [[? ?] Hg]]. specialize (H1 l0).  hnf in H1.
if_tac in H1. destruct H1.  hnf in H1. if_tac; rewrite H1; constructor.
apply join_unit2; auto.
apply join_unit1; auto.
if_tac.
contradiction H2. unfold adr_add in H3; destruct l; destruct l0; simpl in H3. inv H3.
split; auto. omega.
do 3 red in H1. apply identity_unit' in H1. auto.
*
apply join_comm, core_unit.
*
destruct H1 as [phi1 [phi2 [? ?]]].
destruct (join_ex_identities w) as [e [? ?]].
exists phi1; exists phi2.
split; auto.
split; auto.
unfold VALspec; split.
intro l'.
unfold jam in *.
destruct H0 as [bl [[H0' ?] Hg]].
specialize ( H0 l').
unfold jam in H0.
hnf in H0|-*; if_tac.
subst l'.
rewrite if_true in H0.
destruct H0.
unfold yesat_raw in H0.
destruct H2 as [H2 _].
pose proof (equal_f H2 (adr_add l i)).
unfold f in H5.
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
destruct H2 as [-> _]. unfold f.
rewrite if_false; auto.
if_tac. apply NO_identity. apply H0.
simpl; destruct H2 as [_ ->].
destruct H0 as [bl [[H0' ?] Hg]]; auto.
Qed.


Lemma address_mapsto_exists:
  forall ch v sh (rsh: readable_share sh) loc w0
      (RESERVE: forall l', adr_range loc (size_chunk ch) l' -> w0 @ l' = NO Share.bot bot_unreadable)
      (Hg: identity (ghost_of w0)),
      (align_chunk ch | snd loc) ->
      exists w, address_mapsto ch (decode_val ch (encode_val ch v)) sh loc w 
                    /\ core w = core w0.
Proof.
intros. rename H into Halign.
unfold address_mapsto.
pose (f l' := if adr_range_dec loc (size_chunk ch) l'
                     then YES sh rsh (VAL (nthbyte (snd l' - snd loc) (encode_val ch v))) NoneP
                     else core w0 @ l').
pose proof I.
destruct (make_rmap f (ghost_of w0) (level w0)) as [phi [? ?]].
extensionality l; unfold f, compose; simpl.
if_tac; simpl; auto.
rewrite <- level_core.
apply resource_at_approx.
{ apply ghost_of_approx. }
exists phi.
split.
+ exists (encode_val ch v).
  split; [split|].
  split; auto.
  apply encode_val_length.
  intro l'.
  unfold jam.
  hnf.
  unfold yesat, yesat_raw, noat.
  unfold app_pred, proj1_sig. destruct H1; rewrite H1; clear H H1.
  unfold f; clear f.
  if_tac.
  exists rsh.
  f_equal.
  rewrite <- core_resource_at.
  apply core_identity.
  simpl.
  destruct H1 as [_ ->]; auto.
+ apply rmap_ext. do 2 rewrite level_core. auto.
  intro l; specialize (RESERVE l).
  rewrite <- core_resource_at. destruct H1. rewrite H1. unfold f.
  if_tac.
  rewrite core_YES.
  rewrite <- core_resource_at. rewrite RESERVE; auto.
  rewrite core_NO; auto.
  rewrite <- core_resource_at; rewrite core_idem; auto.
  { rewrite <- core_ghost_of.
    destruct H1 as [_ ->].
    rewrite core_ghost_of; auto. }
Qed.

(*  NOT TRUE, because readable doesn't constraint NoneP ...
Lemma readable_VAL:
 forall w l, readable l (w_m w) <-> exists sh, (VALspec sh l * TT) w.

*)

Lemma VALspec1: VALspec_range 1 = VALspec.
Proof.
unfold VALspec, VALspec_range.
extensionality sh l.
f_equal; f_equal.
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

Lemma VALspec_range_exp_address_mapsto:
  forall ch sh l,
    (align_chunk ch | snd l) ->
    VALspec_range (size_chunk ch) sh l |-- EX v: val, address_mapsto ch v sh l.
Proof.
  intros.
  intros w ?.
  destruct H0 as [H0 Hg].
  simpl in H0 |- *.
  cut (exists (b0 : list memval),
     length b0 = size_chunk_nat ch /\
     (forall b1 : address,
      if adr_range_dec l (size_chunk ch) b1
      then
       exists rsh: readable_share sh,
         w @ b1 =
         YES sh rsh
           (VAL (nth (nat_of_Z (snd b1 - snd l)) b0 Undef))
           (SomeP (ConstType unit) (fun _ => tt))
      else identity (w @ b1))).
  {
    intros.
    destruct H1 as [b0 [? ?]].
    exists (decode_val ch b0), b0.
    tauto.
  }
  rewrite !size_chunk_conv in *.
  forget (size_chunk_nat ch) as n; clear - H0.

  cut (exists b0 : list memval,
     length b0 = n /\
     (forall b1 : address,
        adr_range l (Z.of_nat n) b1 ->
       exists rsh: readable_share sh,
         w @ b1 =
         YES sh rsh
           (VAL (nth (nat_of_Z (snd b1 - snd l)) b0 Undef))
           (SomeP (ConstType unit) (fun _ => tt)))).
  {
    intros.
    destruct H as [b0 H].
    exists b0.
    split; [tauto |].
    intros b; specialize (H0 b).
    if_tac; [apply (proj2 H) |]; auto.
  }

  assert (forall b : address,
    adr_range l (Z.of_nat n) b ->
        exists (b0 : memval) (rsh : readable_share sh),
          w @ b =
          YES sh rsh (VAL b0)
            (SomeP (ConstType unit) (fun _ => tt))).
  {
    intros.
    specialize (H0 b).
    if_tac in H0; tauto.
  }
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
  forall ch v sh l,
        address_mapsto ch v sh l |-- VALspec_range (size_chunk ch) sh l.
Proof.
intros.
intros w ?. unfold VALspec_range.
destruct H as [bl [[Hbl ?] Hg]].
split; auto.
intro l'.
specialize ( H l').
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

(* TODO: resume this lemma. *)
(*
Lemma fun_assert_contractive:
   forall fml cc (A: TypeTree)
     (P Q: pred rmap -> forall ts, dependent_type_functor_rec ts (AssertTT A) (pred rmap)) v,
      (forall ts x rho, nonexpansive (fun R => P R ts x rho)) ->
      (forall ts x rho, nonexpansive (fun R => Q R ts x rho)) ->
      contractive (fun R : pred rmap => fun_assert fml cc A (P R) (Q R) v).
Proof.
  intros.
  (*
  assert (H': forall xvl: A * environ, nonexpansive (fun R => P R (fst xvl) (snd xvl)))
    by auto; clear H; rename H' into H.
  assert (H': forall xvl: A * environ, nonexpansive (fun R => Q R (fst xvl) (snd xvl)))
    by auto; clear H0; rename H' into H0.
  *)
  intro; intros.
  rename H0 into H'.
  intro; intros.
  intro; intros; split; intros ? ? H7; simpl in H1.
  + assert (a >= level a')%nat.
    {
      apply necR_level in H2. clear - H1 H2.
      apply le_trans with (level y); auto.
    }
    clear y H1 H2. rename H3 into H2.
    hnf.
    destruct H7 as [loc H7].
    hnf in H7. destruct H7 as [H1 H3].  hnf in H1.
    exists loc.
    apply prop_andp_i; auto.
    split; auto.
    hnf in H3|-*.
    intro; specialize ( H3 b).
    hnf in H3|-*.
    if_tac; auto.
    subst b.
    hnf in H3|-*.
    rewrite H3; clear H3.
    f_equal.
    simpl.
    f_equal.
    extensionality ts.
    extensionality x.
    extensionality b.
    extensionality rho.
    unfold packPQ.
    simpl.
    if_tac.
    - (* P proof *)
      specialize ( H ts x rho P0 Q0).
Check approx_eq_i.
      apply approx_eq_i.
pose proof (later_derives (unfash_derives H)).
      apply (later_derives (unfash_derives H)); clear H.
      rewrite later_unfash.
      unfold unfash.
      red. red.
      apply pred_nec_hereditary with a; auto.
      apply nec_nat; auto.
(* Q proof *)
clear H; rename H' into H.
specialize ( H (x,vl) P0 Q0).
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
specialize ( H3 b).
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
specialize ( H (x,vl) P0 Q0).
symmetry.
apply approx_eq_i.
apply (later_derives (unfash_derives H)); clear H.
rewrite later_unfash.
red. red. red.
apply pred_nec_hereditary with a; auto.
apply nec_nat; auto.
(* Q proof *)
clear H; rename H' into H.
specialize ( H (x,vl) P0 Q0).
symmetry.
apply approx_eq_i.
apply (later_derives (unfash_derives H)); clear H.
rewrite later_unfash.
red. red. red.
apply pred_nec_hereditary with a; auto.
apply nec_nat; auto.
Qed.
*)
Lemma VALspec_range_bytes_readable:
  forall n sh loc m, VALspec_range n sh loc m -> bytes_readable loc n m.
Proof.
intros; intro; intros.
destruct H.
specialize ( H (adr_add loc i)).
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
  forall n sh loc m, writable_share sh -> VALspec_range n sh loc m -> bytes_writable loc n m.
Proof.
intros; intro; intros.
destruct H0.
specialize ( H0 (adr_add loc i)).
hnf in H0.
rewrite if_true in H0.
destruct H0 as [v [p ?]].
hnf in H0.
do 3 red.
rewrite H0; auto with extensionality.
destruct loc; split; unfold adr_add; auto.
simpl. omega.
Qed.

Lemma yesat_join_sub:
  forall pp k l sh m m',
          join_sub m m' ->
          yesat pp k sh l m ->
         exists sh', yesat pp k sh' l m'.
Proof.
intros.
destruct H0.
unfold yesat_raw in H0.
generalize (resource_at_join_sub _ _ l H); rewrite H0; intro.
assert (level m = level m').
destruct H; apply join_level in H; intuition.
destruct H1.
destruct x0; case_eq (m' @ l); intros; rewrite H3 in H1; inv H1.
do 2 econstructor. unfold yesat_raw. simpl. rewrite <- H2.  eapply H3.
exists sh1.
unfold yesat. simpl.
exists r0.
rewrite <- H2. rewrite H3.
subst; f_equal; auto.
Qed.

Lemma VALspec_range_precise: forall n sh l,  precise (VALspec_range n sh l).
Proof.
intros.
intro; intros.
apply rmap_ext; auto.
1: destruct H1,H2; apply join_level in H1; apply join_level in H2; intuition.
intro.
destruct H as [H Hg], H0 as [H0 Hg0].
specialize (H l0); specialize (H0 l0).
unfold jam in *.
hnf in H, H0. if_tac in H.
+ destruct H as [v [p ?]].
  destruct H0 as [v' [p' ?]].
  unfold yesat_raw in *.
  generalize (resource_at_join_sub _ _ l0 H1); rewrite H; clear H1; intro.
  generalize (resource_at_join_sub _ _ l0 H2); rewrite H0; clear H2; intro.
  f_equal. auto with extensionality.
  clear - H1 H2.
  destruct H1; destruct H2.
  simpl in *.
  f_equal.
  inv H0; inv H; congruence.
+ do 3 red in H,H0.
  apply (resource_at_join_sub _ _ l0) in H1.
  eapply join_sub_same_identity; eauto.
  * apply identity_unit'; auto.
  * apply (resource_at_join_sub _ _ l0) in H2.
    eapply join_sub_unit_for; eauto.
    apply identity_unit'; auto.
+ destruct H as [H Hg], H0 as [H0 Hg0].
  eapply same_identity; auto.
  * destruct H1 as [? H1%ghost_of_join].
    rewrite (Hg _ _ H1) in H1; eauto.
  * destruct H2 as [? H2%ghost_of_join].
    rewrite (Hg0 _ _ H2) in H2; eauto.
Qed.

Lemma nonlock_permission_bytes_precise: forall sh p n,
  precise (nonlock_permission_bytes sh p n).
Proof.
  intros.
  intro; intros.
  destruct H as [H Hg], H0 as [H0 Hg0].
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
    clear - H H0 H1 H2.
    destruct H1 as [b1 H1], H2 as [b2 H2].
    destruct (w1 @ l), (w2 @ l); inv H1; inv H2; simpl in *;
    repeat match goal with H: Some _ = Some _ |- _ => inv H end;
    repeat f_equal; try apply proof_irr; try congruence;
    try contradiction.
  + do 3 red in H,H0.
    apply (resource_at_join_sub _ _ l) in H1.
    eapply join_sub_same_identity; eauto.
    * apply identity_unit'; auto.
    * apply (resource_at_join_sub _ _ l) in H2.
      eapply join_sub_unit_for; eauto.
      apply identity_unit'; auto.
  + eapply same_identity; auto.
    * destruct H1 as [? H1%ghost_of_join].
      rewrite (Hg _ _ H1) in H1; eauto.
    * destruct H2 as [? H2%ghost_of_join].
      rewrite (Hg0 _ _ H2) in H2; eauto.
Qed.

Lemma address_mapsto_precise: forall ch v sh l, precise (address_mapsto ch v sh l).
Proof.
intros.
apply (derives_precise _ _ (address_mapsto_VALspec_range ch v sh l)).
apply VALspec_range_precise.
Qed.

Lemma LKspec_precise lock_size: forall R sh l, precise (LKspec lock_size R sh l).
Proof.
intros.
intro; intros.
assert (level w1 = level w2) as Hlevel.
{ destruct H1,H2; apply join_level in H1; apply join_level in H2; intuition. }
destruct H as [H Hg], H0 as [H0 Hg0].
apply rmap_ext; auto; intros.
-
specialize (H l0); specialize (H0 l0).
simpl in *.
if_tac in H0.
destruct H. destruct H0. rewrite H,H0.
f_equal. proof_irr. auto.
rewrite Hlevel; auto.
apply (resource_at_join_sub _ _ l0) in H1.
  eapply join_sub_same_identity; eauto.
  * apply identity_unit'; auto.
  * apply (resource_at_join_sub _ _ l0) in H2.
    eapply join_sub_unit_for; eauto.
    apply identity_unit'; auto.
-
 eapply same_identity; auto.
    * destruct H1 as [? H1%ghost_of_join].
      rewrite (Hg _ _ H1) in H1; eauto.
    * destruct H2 as [? H2%ghost_of_join].
      rewrite (Hg0 _ _ H2) in H2; eauto.
Qed.

Program Definition core_load (ch: memory_chunk) (l: address) (v: val): pred rmap :=
  EX bl: list memval,
  !!(length bl = size_chunk_nat ch /\ decode_val ch bl = v /\ (align_chunk ch | snd l)) &&
    allp (jam (adr_range_dec l (size_chunk ch))
      (fun l' phi => exists sh, exists rsh, phi @ l' 
        = YES sh rsh (VAL (nth (nat_of_Z (snd l' - snd l)) bl Undef)) NoneP)
      (fun _ _ => True)).
 Next Obligation.
    intros; intro; intros.
  destruct H0 as [sh [rsh ?]]; exists sh, rsh.
    apply (age1_YES a a'); auto.
  Qed.
  Next Obligation.     intros; intro; intros. auto.
  Qed.

Program Definition core_load' (ch: memory_chunk) (l: address) (v: val) (bl: list memval)
  : pred rmap :=
  !!(length bl = size_chunk_nat ch /\ decode_val ch bl = v /\ (align_chunk ch | snd l)) &&
    allp (jam (adr_range_dec l (size_chunk ch))
      (fun l' phi => exists sh, exists rsh, phi @ l' 
        = YES sh rsh (VAL (nth (nat_of_Z (snd l' - snd l)) bl Undef)) NoneP)
      (fun _ _ => True)).
 Next Obligation.
    intros; intro; intros.
  destruct H0 as [sh [rsh ?]]; exists sh, rsh.
    apply (age1_YES a a'); auto.
  Qed.
  Next Obligation.     intros; intro; intros. auto.
  Qed.

Lemma VALspec_range_0: forall sh loc, VALspec_range 0 sh loc = emp.
Proof.
 intros.
 apply pred_ext.
 - intros ? [? ?]. simpl in H.
   do 3 red.
   apply all_resource_at_identity; auto.
   intro l. specialize (H l).
   rewrite if_false in H; auto.
   destruct loc, l; intros [? ?]; simpl in *; omega.
 - intros ? ?. split. intro b. rewrite jam_false.
   do 3 red. apply resource_at_identity; auto.
   destruct loc, b; intros [? ?]; simpl in *; omega.
   apply ghost_of_identity; auto.
Qed.
Hint Resolve VALspec_range_0: normalize.

Lemma nonlock_permission_bytes_0: forall sh a, nonlock_permission_bytes sh a 0 = emp.
Proof.
  intros.
  apply pred_ext.
  + intros ? [? ?]. simpl in H.
    do 3 red.
    apply all_resource_at_identity; auto.
    intro l. specialize (H l).
    rewrite if_false in H; auto.
    destruct a, l; intros [? ?]; simpl in *; omega.
  + intros ? ?. split. intro b. rewrite jam_false.
    do 3 red. apply resource_at_identity; auto.
    destruct a, b; intros [? ?]; simpl in *; omega.
    apply ghost_of_identity; auto.
Qed.

Lemma nonlock_permission_bytes_not_nonunit: forall sh p n,
  ~ nonunit sh ->
  nonlock_permission_bytes sh p n |-- emp.
Proof.
  intros.
  assert (sh = Share.bot).
  {
    destruct (dec_share_identity sh).
    + apply identity_share_bot; auto.
    + apply nonidentity_nonunit in n0; tauto.
  }
  subst.
  intros ? ?. simpl in H.
  do 3 red.
  destruct H0.
  apply all_resource_at_identity; auto.
  intro l.
  specialize (H0 l); simpl in H0.
  if_tac in H0; [| auto].
  destruct H0.
  destruct (a @ l); inv H0.
  + apply NO_identity. 
  + contradiction (bot_unreadable r).
Qed.

Lemma is_resource_pred_YES_VAL sh:
  is_resource_pred
    (fun l' => EX  v: memval, yesat NoneP (VAL v) sh l')
    (fun r _ n => (exists b0 rsh, r = YES sh rsh (VAL b0)
        (SomeP (ConstType unit) (fun _ => tt)))).
Proof. hnf; intros. reflexivity. Qed.

Lemma is_resource_pred_YES_VAL' sh v:
  is_resource_pred
    (fun l' => yesat NoneP (VAL (v l')) sh l')
    (fun r l n => (exists rsh, r = YES sh rsh (VAL (v l))
        (SomeP (ConstType unit) (fun _ => tt)))).
Proof. hnf; intros. reflexivity. Qed.

Lemma is_resource_pred_nonlock_shareat sh:
  is_resource_pred
    (fun i : address => shareat i sh && nonlockat i)
    (fun r _ _ => resource_share r = Some sh /\ nonlock r).
Proof. hnf; intros. reflexivity. Qed.

Lemma VALspec_range_split2:
  forall (n m r: Z) (sh: Share.t) (b: block) (ofs: Z),
    r = n + m -> n >= 0 -> m >= 0 ->
    VALspec_range r sh (b, ofs) = 
    VALspec_range n sh (b, ofs) * VALspec_range m sh (b, ofs + n).
Proof.
  intros.
  assert (exists resp, is_resource_pred (fun l' => EX  v: memval, yesat NoneP (VAL v) sh l') resp) by (eexists; apply is_resource_pred_YES_VAL).
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
  forall (n : Z) (v : val) (sh : Share.t) (l : address) (i : Z),
       0 <= i < n ->
       VALspec_range n sh l
       |-- VALspec sh (adr_add l i) * TT.
Proof.
 intros.
  destruct l as [b ofs].
  rewrite (VALspec_range_split2 i (n-i) n sh b ofs); try omega.
  rewrite (VALspec_range_split2 1 (n-i-1) (n-i) sh b (ofs+i)); try omega.
  change (VALspec_range 1) with (VALspec_range 1).
  rewrite VALspec1.
  rewrite <- sepcon_assoc.
  rewrite (sepcon_comm (VALspec_range i sh (b, ofs))).
  rewrite sepcon_assoc.
  apply sepcon_derives; auto.
Qed.

Lemma VALspec_range_overlap': forall sh p1 p2 n1 n2,
  adr_range p1 n1 p2 ->
  n2 > 0 ->
  VALspec_range n1 sh p1 * VALspec_range n2 sh p2 |-- FF.
Proof.
  intros.
  intros w [w1 [w2 [? [[? Hg1] [? Hg2]]]]].
  specialize ( H2 p2).
  specialize ( H3 p2).
  rewrite jam_true in H2 by auto.
  rewrite jam_true in H3 by (destruct p2; simpl; split; auto; omega).
  destruct H2; destruct H3. hnf in H2,H3.
  apply (resource_at_join _ _ _ p2) in H1.
  destruct H2, H3.
  rewrite H2, H3 in H1.
  clear - x1 H1; simpl in H1.
  inv H1.
  clear - x1 RJ.
  generalize (join_self' RJ); intro. subst sh3.
  apply readable_nonidentity in x1.
  apply x1. apply identity_unit_equiv. apply RJ.
Qed.

Lemma address_mapsto_overlap':
  forall sh ch1 v1 ch2 v2 a1 a2,
     adr_range a1 (size_chunk ch1) a2 ->
     address_mapsto ch1 v1 sh a1 * address_mapsto ch2 v2 sh a2 |-- FF.
Proof.
  intros.
  eapply derives_trans; [eapply sepcon_derives | apply VALspec_range_overlap'].
  + apply address_mapsto_VALspec_range.
  + apply address_mapsto_VALspec_range.
  + auto.
  + apply size_chunk_pos.
Qed.

Lemma VALspec_range_overlap: forall sh l1 n1 l2 n2,
  range_overlap l1 n1 l2 n2 ->
  VALspec_range n1 sh l1 * VALspec_range n2 sh l2 |-- FF.
Proof.
  intros.
  pose proof range_overlap_non_zero _ _ _ _ H.
  apply range_overlap_spec in H; try tauto.
  destruct H.
  + apply VALspec_range_overlap'; tauto.
  + rewrite sepcon_comm.
    apply VALspec_range_overlap'; tauto.
Qed.

Lemma address_mapsto_overlap: forall sh l1 ch1 v1 l2 ch2 v2,
  range_overlap l1 (size_chunk ch1) l2 (size_chunk ch2) ->
  address_mapsto ch1 v1 sh l1 * address_mapsto ch2 v2 sh l2 |-- FF.
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
  apply nonunit_nonidentity in H0; contradiction H0.
  eapply join_self; eauto.
Qed.

Lemma nonlock_permission_bytes_overlap:
  forall sh n1 n2 p1 p2,
  nonunit sh ->
  range_overlap p1 n1 p2 n2 ->
  nonlock_permission_bytes sh p1 n1 * nonlock_permission_bytes sh p2 n2 |-- FF.
Proof.
  intros.
  eapply derives_trans; [apply sepcon_derives; apply andp_left1, derives_refl|].
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

Lemma address_mapsto_value_cohere':
  forall ch v1 v2 sh1 sh2 a r
 (Hmaps1 : address_mapsto ch v1 sh1 a r)
 (Hmaps2 : address_mapsto ch v2 sh2 a r), v1=v2.
Proof.
 intros.
 destruct Hmaps1 as [b1 [[[Hlen1 [? ?]] Hall1] Hg1]].
 destruct Hmaps2 as [b2 [[[Hlen2 [? ?]] Hall2] Hg2]].
 assert (b1 = b2); [ | subst; auto].
 clear - Hlen1 Hlen2 Hall1 Hall2.
 rewrite size_chunk_conv in *.
 forget (size_chunk_nat ch) as n. clear ch.
 assert (forall i, nth_error b1 i = nth_error b2 i).
 intro.
 destruct a as [b z].
 specialize (Hall1 (b, (z+Z.of_nat i))).
 specialize (Hall2 (b, (z+Z.of_nat i))).
 hnf in Hall1,Hall2. if_tac in Hall1. destruct H as [_ [_ ?]].
 destruct Hall1 as (? & Hall1), Hall2 as (? & Hall2). simpl in Hall1, Hall2.
 rewrite Hall1 in Hall2; inversion Hall2.
 replace (z + Z.of_nat i - z) with (Z.of_nat i) in H2 by omega.
 rewrite Nat2Z.id in H2.
 rewrite nth_error_nth with (z:=Undef) by omega.
 rewrite nth_error_nth with (z:=Undef) by omega.
 f_equal; auto.
 assert (~(i<n)%nat).
 contradict H. split; auto. omega.
 transitivity (@None memval); [ | symmetry];
 apply nth_error_length; omega.
 clear - H Hlen1 Hlen2.
 revert b1 b2 Hlen1 Hlen2 H.
 induction n; destruct b1,b2; intros; auto; inv Hlen1; inv Hlen2.
 f_equal.
 specialize (H O). simpl in H. inv H; auto.
 apply IHn; auto.
 intro i; specialize (H (S i)); apply H.
Qed.

Lemma address_mapsto_value_cohere:
  forall ch v1 v2 sh1 sh2 a,
 address_mapsto ch v1 sh1 a * address_mapsto ch v2 sh2 a |-- !! (v1=v2).
Proof.
 intros.
 intros w [w1 [w2 [? [? ?]]]]. hnf.
 destruct H0 as [b1 [[[? [? ?]] ?] Hg1]].
 destruct H1 as [b2 [[[? [? ?]] ?] Hg2]].
 assert (b1 = b2); [ | subst; auto].
 clear - H H0 H4 H1 H7.
 rewrite size_chunk_conv in *.
 forget (size_chunk_nat ch) as n. clear ch.
 assert (forall i, nth_error b1 i = nth_error b2 i).
 intro.
 destruct a as [b z].
 specialize (H4 (b, (z+Z.of_nat i))).
 specialize (H7 (b, (z+Z.of_nat i))).
 hnf in H4,H7. if_tac in H4. destruct H2 as [_ [_ ?]].
 destruct H4, H7. hnf in H3,H4.
 apply (resource_at_join _ _ _ (b, z + Z.of_nat i)) in H.
 rewrite H3,H4 in H. inv  H.
 clear - H2 H10 H1.
 replace (z + Z.of_nat i - z) with (Z.of_nat i) in H10 by omega.
 rewrite Nat2Z.id in H10.
 rewrite nth_error_nth with (z:=Undef) by omega.
 rewrite nth_error_nth with (z:=Undef) by omega.
 f_equal; auto.
 assert (~(i<n)%nat).
 contradict H2. split; auto. omega.
 transitivity (@None memval); [ | symmetry];
 apply nth_error_length; omega.
 clear - H2 H0 H1.
 revert b1 b2 H0 H1 H2.
 induction n; destruct b1,b2; intros; auto; inv H0; inv H1.
 f_equal.
 specialize (H2 O). simpl in H2. inv H2; auto.
 apply IHn; auto.
 intro i; specialize (H2 (S i)); apply H2.
Qed.

Definition almost_empty rm: Prop:=
  forall loc sh psh k P, rm @ loc = YES sh psh k P -> forall val, ~ k = VAL val.

(*Lenb: moved here from veric.initial_world.v*)
Definition no_locks phi :=
  forall addr sh sh' z z' P,
phi @ addr <> YES sh sh' (LK z z') P.

(*Lenb: moved here from veric.initial_world.v
Definition no_locks phi :=
  forall addr sh sh' z P,
    phi @ addr <> YES sh sh' (LK z) P /\
    phi @ addr <> YES sh sh' (CT z) P.

Definition func_at (f: funspec): address -> pred rmap :=
  match f with
   | mk_funspec fsig cc A P Q _ _ => pureat (SomeP (SpecTT A) (packPQ P Q)) (FUN fsig cc)
  end.

Definition func_at' (f: funspec) (loc: address) : pred rmap :=
  match f with
   | mk_funspec fsig cc _ _ _ _ _ => EX pp:_, pureat pp (FUN fsig cc) loc
  end.
*)
