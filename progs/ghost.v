Require Import VST.progs.conclib.

(* Axiomatization of view shifts, PCMs, and ghost state *)

Class PCM (A : Type) :=
  { join : A -> A -> A -> Prop;
    join_comm : forall a b c (Hjoin : join a b c), join b a c;
    join_assoc : forall a b c d e (Hjoin1 : join a b c) (Hjoin2 : join c d e),
                 exists c', join b d c' /\ join a c' e }.

Section Ghost.

Context {CS : compspecs}.

(* This is an overapproximation of IRIS's concept of view shift. *)
Definition view_shift A B := forall (Espec : OracleKind) D P Q R C P',
  semax D (PROPx P (LOCALx Q (SEPx (B :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (A :: R)))) C P'.

Section ViewShift.

Axiom view_shift_super_non_expansive : forall n P Q, compcert_rmaps.RML.R.approx n (!!view_shift P Q) =
  compcert_rmaps.RML.R.approx n (!!view_shift (compcert_rmaps.RML.R.approx n P) (compcert_rmaps.RML.R.approx n Q)).

Axiom view_shift_later : forall P Q, view_shift P Q -> view_shift (|>P) (|>Q).

Global Instance view_shift_refl : RelationClasses.Reflexive view_shift.
Proof.
  repeat intro; auto.
Qed.

Global Instance view_shift_trans : RelationClasses.Transitive view_shift.
Proof.
  repeat intro; apply H; auto.
Qed.

Lemma derives_view_shift : forall P Q, P |-- Q -> view_shift P Q.
Proof.
  repeat intro; eapply semax_pre; [|eauto].
  go_lowerx; cancel.
Qed.

Lemma view_shift_sepcon : forall P Q P' Q' (HP : view_shift P P') (HQ : view_shift Q Q'),
  view_shift (P * Q) (P' * Q').
Proof.
  repeat intro.
  rewrite flatten_sepcon_in_SEP in *; apply HP.
  focus_SEP 1; apply HQ.
  focus_SEP 1; auto.
Qed.

Corollary view_shift_sepcon1 : forall P Q P' (HP : view_shift P P'), view_shift (P * Q) (P' * Q).
Proof.
  intros; apply view_shift_sepcon; auto; reflexivity.
Qed.

Corollary view_shift_sepcon2 : forall P Q Q' (HQ : view_shift Q Q'), view_shift (P * Q) (P * Q').
Proof.
  intros; apply view_shift_sepcon; auto; reflexivity.
Qed.

Lemma view_shift_sepcon_list : forall l1 l2 (Hlen : Zlength l1 = Zlength l2)
  (Hall : forall i, 0 <= i < Zlength l1 -> view_shift (Znth i l1) (Znth i l2)),
  view_shift (fold_right sepcon emp l1) (fold_right sepcon emp l2).
Proof.
  induction l1; intros.
  - symmetry in Hlen; apply Zlength_nil_inv in Hlen; subst; reflexivity.
  - destruct l2; [apply Zlength_nil_inv in Hlen; discriminate|].
    rewrite !Zlength_cons in *.
    simpl; apply view_shift_sepcon, IHl1; try omega; intros.
    + lapply (Hall 0); [|pose proof (Zlength_nonneg l1); omega].
      rewrite !Znth_0_cons; auto.
    + lapply (Hall (i + 1)); [|omega].
      rewrite !Znth_pos_cons, Z.add_simpl_r by omega; auto.
Qed.

Lemma view_shift_exists : forall {A} (P : A -> mpred) Q,
  (forall x, view_shift (P x) Q) -> view_shift (EX x : _, P x) Q.
Proof.
  repeat intro.
  rewrite extract_exists_in_SEP; Intro x.
  apply H; auto.
Qed.

Lemma view_shift_prop : forall (P1 : Prop) P Q,
  (P1 -> view_shift P Q) -> view_shift (!!P1 && P) Q.
Proof.
  repeat intro.
  erewrite extract_prop_in_SEP with (n := O); [|simpl; eauto].
  Intros; simpl; apply H; auto.
Qed.

Lemma view_shift_assert : forall P Q PP, P |-- !!PP -> (PP -> view_shift P Q) -> view_shift P Q.
Proof.
  intros.
  rewrite (add_andp P (!!PP)) by auto.
  rewrite andp_comm; apply view_shift_prop; auto.
Qed.

Lemma view_shift_assert_later : forall P Q PP (HPP : P |-- |>!!PP) (Hshift : PP -> view_shift P Q),
  view_shift P Q.
Proof.
  intros.
  rewrite (add_andp _ _ HPP).
  repeat intro.
   eapply semax_extract_later_prop''; eauto.
  apply prop_derives.
  intro X; apply (Hshift X) in H.
  rewrite <- add_andp; auto.
Qed.

Lemma view_shift_prop_right : forall (P1 : Prop) P Q, P1 -> view_shift P Q -> view_shift P (!!P1 && Q).
Proof.
  intros.
  etransitivity; eauto.
  apply derives_view_shift; entailer!.
Qed.

End ViewShift.

(* General PCM-based ghost state *)

Parameter ghost : forall {A} {P : PCM A} (g : A) (p : val), mpred.

Section PCM.
Context {A: Type}.
Context {M : PCM A}.
Context {defa: Inhabitant A}.

Definition joins a b := exists c, join a b c.

Definition update a b := forall c, joins a c -> joins b c.

(* subject to change *)
(* We need to make sure we can't allocate invalid ghost state (which would immediately entail False). *)
Axiom ghost_alloc : forall (g : A) P, (exists g', joins g g') -> view_shift P (EX p : val, ghost g p * P).
Axiom ghost_dealloc : forall (g : A) p, view_shift (ghost g p) emp.

Axiom ghost_join : forall g1 g2 g p, join g1 g2 g -> ghost g1 p * ghost g2 p = ghost g p.
Axiom ghost_conflict : forall g1 g2 p, ghost g1 p * ghost g2 p |-- !!joins g1 g2.
Axiom ghost_update : forall g g' p, update g g' -> view_shift (ghost g p) (ghost g' p).
Axiom ghost_inj : forall p g1 g2 r1 r2 r
  (Hp1 : predicates_hered.app_pred (ghost g1 p) r1)
  (Hp1 : predicates_hered.app_pred (ghost g2 p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r),
  r1 = r2 /\ g1 = g2.

Lemma ghost_join' : forall g1 g2 p, ghost g1 p * ghost g2 p = EX g : A, !!(join g1 g2 g) && ghost g p.
Proof.
  intros.
  apply mpred_ext.
  - assert_PROP (joins g1 g2) as Hjoin by (apply ghost_conflict).
    destruct Hjoin as (g & ?); Exists g; entailer!.
    erewrite ghost_join; eauto.  apply derives_refl.
  - Intros g.
    erewrite ghost_join; eauto.  apply derives_refl.
Qed.

Lemma ex_ghost_precise : forall p, precise (EX g : A, ghost g p).
Proof.
  intros ???? (? & ?) (? & ?) ??.
  eapply ghost_inj; eauto.
Qed.

Corollary ghost_precise : forall g p, precise (ghost g p).
Proof.
  intros.
  eapply derives_precise, ex_ghost_precise.
  intros ??; exists g; eauto.
Qed.

Lemma ghost_list_alloc : forall lg P, Forall (fun g => exists g', joins g g') lg ->
  view_shift P (EX lp : list val, !!(Zlength lp = Zlength lg) &&
    fold_right sepcon emp (map (fun i => ghost (Znth i lg) (Znth i lp)) (upto (Z.to_nat (Zlength lg)))) * P).
Proof.
  induction 1.
  - apply derives_view_shift; Exists (@nil val); simpl; entailer!.
  - etransitivity; eauto.
    apply view_shift_exists; intro lp.
    etransitivity; [apply ghost_alloc; eauto|].
    apply derives_view_shift; Intros p.
    Exists (p :: lp); rewrite !Zlength_cons, Z2Nat.inj_succ by apply Zlength_nonneg.
    rewrite (upto_app 1), map_app, sepcon_app; simpl.
    rewrite !Znth_0_cons; entailer!.
    erewrite map_map, map_ext_in; eauto; intros; simpl.  apply derives_refl.
    rewrite In_upto in *; rewrite !Znth_pos_cons by omega.
    rewrite Z.add_comm, Z.add_simpl_r; auto.
Qed.

Corollary ghost_list_alloc' : forall g i P, 0 <= i -> (exists g', joins g g') ->
  view_shift P (EX lp : list val, !!(Zlength lp = i) &&
    fold_right sepcon emp (map (fun i => ghost g (Znth i lp)) (upto (Z.to_nat i))) * P).
Proof.
  intros.
  etransitivity; [apply ghost_list_alloc with (lg := repeat g (Z.to_nat i))|].
  { apply Forall_repeat; auto. }
  apply derives_view_shift; Intros lp; Exists lp.
  rewrite Zlength_repeat, Z2Nat.id in H1 |- * by auto; entailer!.
  erewrite map_ext_in; eauto; intros; simpl.  apply derives_refl.
  rewrite Znth_repeat'; auto.
  apply In_upto in H1. omega.
Qed.

End PCM.

(* operations on PCMs *)

Section Ops.

Context {A B : Type} {MA : PCM A} {MB : PCM B}.

Instance prod_PCM : PCM (A * B) := { join a b c := join (fst a) (fst b) (fst c) /\ join (snd a) (snd b) (snd c) }.
Proof.
  - intros ??? (? & ?); split; apply join_comm; auto.
  - intros ????? (? & ?) (HA & HB).
    eapply join_assoc in HA; eauto.
    eapply join_assoc in HB; eauto.
    destruct HA as (c'a & ? & ?), HB as (c'b & ? & ?); exists (c'a, c'b); split; split; auto.
Defined.

(* Two different ways of adding a unit to a PCM. *)
Instance option_PCM : PCM (option A) := { join a b c :=
  match a, b, c with
  | Some a', Some b', Some c' => join a' b' c'
  | Some a', None, Some c' => c' = a'
  | None, Some b', Some c' => c' = b'
  | None, None, None => True
  | _, _, _ => False
  end }.
Proof.
  - destruct a, b, c; auto.
    apply join_comm.
  - destruct a, b, c, d, e; try contradiction; intros; subst;
      try solve [eexists (Some _); split; auto; auto]; try solve [exists None; split; auto].
    eapply join_assoc in Hjoin2; eauto.
    destruct Hjoin2 as (c' & ? & ?); exists (Some c'); auto.
Defined.

Instance exclusive_PCM : PCM (option A) := { join a b c := a = c /\ b = None \/ b = c /\ a = None }.
Proof.
  - tauto.
  - intros ????? [(? & ?) | (? & ?)]; subst; eauto.
Defined.

Lemma exclusive_update : forall v v' p, view_shift (ghost (Some v) p) (ghost (Some v') p).
Proof.
  intros; apply ghost_update; intros ? (? & [[]|[]]); try discriminate; subst.
  eexists; simpl; eauto.
Qed.

End Ops.

Global Instance share_PCM : PCM share := { join := sepalg.join }.
Proof.
  - intros; apply sepalg.join_comm; auto.
  - intros.
    eapply sepalg.join_assoc in Hjoin2; eauto.
    destruct Hjoin2; eauto.
Defined.

Class PCM_order `{P : PCM} (ord : A -> A -> Prop) := { ord_refl :> RelationClasses.Reflexive ord;
  ord_trans :> RelationClasses.Transitive ord;
  ord_lub : forall a b c, ord a c -> ord b c -> exists c', join a b c' /\ ord c' c;
  join_ord : forall a b c, join a b c -> ord a c /\ ord b c; ord_join : forall a b, ord b a -> join a b a }.

Class lub_ord {A} (ord : A -> A -> Prop) := { lub_ord_refl :> RelationClasses.Reflexive ord;
  lub_ord_trans :> RelationClasses.Transitive ord;
  has_lub : forall a b c, ord a c -> ord b c -> exists c', ord a c' /\ ord b c' /\
    forall d, ord a d -> ord b d -> ord c' d }.

Global Instance ord_PCM `{lub_ord} : PCM A := { join a b c := ord a c /\ ord b c /\
  forall c', ord a c' -> ord b c' -> ord c c' }.
Proof.
  - intros ??? (? & ? & ?); eauto.
  - intros ????? (? & ? & Hc) (? & ? & He).
    destruct (has_lub b d e) as (c' & ? & ? & Hlub); try solve [etransitivity; eauto].
    exists c'; repeat split; auto.
    + etransitivity; eauto.
    + apply Hlub; auto; transitivity c; auto.
    + intros.
      apply He.
      * apply Hc; auto; etransitivity; eauto.
      * etransitivity; eauto.
Defined.

Global Instance ord_PCM_ord `{lub_ord} : PCM_order ord.
Proof.
  constructor.
  - apply lub_ord_refl.
  - apply lub_ord_trans.
  - intros ??? Ha Hb.
    destruct (has_lub _ _ _ Ha Hb) as (c' & ? & ? & ?).
    exists c'; simpl; eauto.
  - simpl; intros; tauto.
  - intros; simpl.
    repeat split; auto.
    reflexivity.
Defined.

(* Instances of ghost state *)
Section Snapshot.
(* One common kind of PCM is one in which a central authority has a reference copy, and clients pass around
   partial knowledge. *)

Context `{ORD : PCM_order}.

Lemma join_refl : forall v, join v v v.
Proof.
  intros; apply ord_join; reflexivity.
Qed.

Lemma join_compat : forall v1 v2 v' v'', join v2 v' v'' -> ord v1 v2 -> exists v0, join v1 v' v0 /\ ord v0 v''.
Proof.
  intros.
  destruct (join_ord _ _ _ H).
  apply ord_lub; auto; etransitivity; eauto.
Qed.

Lemma join_ord_eq : forall a b, ord a b <-> exists c, join a c b.
Proof.
  split.
  - intros; exists b.
    apply ord_join in H.
    apply join_comm; auto.
  - intros (? & H); apply join_ord in H; tauto.
Qed.

(* The master-snapshot PCM in the RCU paper divides the master into shares, which is useful for having both
   an authoritative writer and an up-to-date invariant. *)
(* This generalizes both ghost_var and master-snapshot. *)

Global Instance snap_PCM : PCM (share * A) :=
  { join a b c := sepalg.join (fst a) (fst b) (fst c) /\
      if eq_dec (fst a) Share.bot then if eq_dec (fst b) Share.bot then join (snd a) (snd b) (snd c)
        else ord (snd a) (snd b) /\ snd c = snd b else snd c = snd a /\
          if eq_dec (fst b) Share.bot then ord (snd b) (snd a) else snd c = snd b }.
Proof.
  - intros ??? [? Hjoin].
    if_tac; if_tac; try destruct Hjoin; auto.
    split; auto; apply join_comm; auto.
  - intros.
    destruct Hjoin1 as [Hsh1 Hjoin1], Hjoin2 as [Hsh2 Hjoin2].
    destruct (sepalg.join_assoc Hsh1 Hsh2) as [sh' []].
    destruct (eq_dec (fst b) Share.bot).
    + assert (fst c = fst a) as Hc.
      { eapply sepalg.join_eq; eauto.
        rewrite e0; apply join_bot_eq. }
      rewrite Hc in *.
      assert (sh' = fst d) as Hd.
      { eapply sepalg.join_eq; eauto.
        rewrite e0; apply bot_join_eq. }
      rewrite Hd in *.
      destruct (eq_dec (fst d) Share.bot).
      * destruct (eq_dec (fst a) Share.bot).
        -- destruct (join_assoc _ _ _ _ _ Hjoin1 Hjoin2) as [c' []].
           exists (Share.bot, c'); simpl; rewrite eq_dec_refl; rewrite ?e2, ?e0, ?e1 in *; auto.
        -- destruct Hjoin1 as [Hc' ?]; rewrite Hc' in *.
           destruct Hjoin2; exploit (ord_lub (snd b) (snd d)); eauto; intros [c' []].
           exists (Share.bot, c'); simpl; rewrite eq_dec_refl; rewrite ?e0, ?e1 in *; auto.
      * exists d.
        destruct (eq_dec (fst a) Share.bot); if_tac; try contradiction.
        -- destruct Hjoin2.
           apply join_ord in Hjoin1; destruct Hjoin1.
           split; split; auto; split; auto; etransitivity; eauto.
        -- destruct Hjoin2 as [He1 He2]; rewrite He1, He2 in *.
           destruct Hjoin1 as [Hd' ?]; rewrite Hd' in *; auto.
    + exists (sh', snd b); simpl.
      destruct (eq_dec (fst c) Share.bot).
      { rewrite e0 in Hsh1; apply join_Bot in Hsh1; destruct Hsh1; contradiction. }
      destruct (eq_dec sh' Share.bot).
      { subst; apply join_Bot in H; destruct H; contradiction. }
      destruct Hjoin2 as [He ?]; rewrite He in *; split; auto; split; auto; split; auto.
      replace (snd b) with (snd c) by (destruct (eq_dec (fst a) Share.bot); tauto); auto.
Defined.

Definition ghost_snap (a : A) p := ghost (Share.bot, a) p.

Lemma ghost_snap_join : forall v1 v2 p v, join v1 v2 v ->
  ghost_snap v1 p * ghost_snap v2 p = ghost_snap v p.
Proof.
  intros; apply ghost_join; simpl.
  rewrite !eq_dec_refl; auto.
Qed.

Lemma ghost_snap_conflict : forall v1 v2 p, ghost_snap v1 p * ghost_snap v2 p |-- !!(joins v1 v2).
Proof.
  intros; eapply derives_trans; [apply ghost_conflict|].
  apply prop_left; intros ((?, a) & ? & Hj); simpl in Hj.
  rewrite !eq_dec_refl in Hj.
  apply prop_right; exists a; auto.
Qed.

Lemma ghost_snap_join' : forall v1 v2 p,
  ghost_snap v1 p * ghost_snap v2 p = EX v : _, !!(join v1 v2 v) && ghost_snap v p.
Proof.
  intros; apply mpred_ext.
  - assert_PROP (joins v1 v2) as H by apply ghost_snap_conflict.
    destruct H as [v]; Exists v; entailer!.
    erewrite ghost_snap_join; eauto.  apply derives_refl.
  - Intros v; erewrite ghost_snap_join; eauto.  apply derives_refl.
Qed.

Lemma snap_master_join : forall v1 sh v2 p, sh <> Share.bot ->
  ghost_snap v1 p * ghost (sh, v2) p = !!(ord v1 v2) && ghost (sh, v2) p.
Proof.
  intros; apply mpred_ext.
  - eapply derives_trans; [apply prop_and_same_derives, ghost_conflict|].
    apply derives_extract_prop; intros ((sh', ?) & Hj).
    setoid_rewrite ghost_join; eauto.
    simpl in Hj.
    rewrite eq_dec_refl in Hj; destruct Hj as [Hsh Hj].
    unfold share in Hj; destruct (eq_dec sh Share.bot); [contradiction|].
    assert (sh' = sh) by (eapply sepalg.join_eq; eauto; apply bot_join_eq).
    destruct Hj; subst; entailer!.
  - Intros; setoid_rewrite ghost_join; eauto.  apply derives_refl.
    simpl; rewrite eq_dec_refl; split.
    + apply bot_join_eq.
    + if_tac; auto; contradiction.
Qed.

Lemma master_update : forall v v' p, ord v v' -> view_shift (ghost (Tsh, v) p) (ghost (Tsh, v') p).
Proof.
  intros; apply ghost_update.
  intros ? (x & Hj); simpl in Hj.
  exists (Tsh, v'); simpl.
  destruct (eq_dec Tsh Share.bot); [contradiction Share.nontrivial|].
  destruct Hj as [Hsh [? Hc']]; apply join_Tsh in Hsh; destruct Hsh as [? Hc]; rewrite Hc in *.
  rewrite eq_dec_refl in Hc' |- *; split; auto; split; auto.
  etransitivity; eauto.
Qed.

Lemma master_init : forall (a : A), exists g', joins (Tsh, a) g'.
Proof.
  intros; exists (Share.bot, a), (Tsh, a); simpl.
  split; auto.
  if_tac; [contradiction Share.nontrivial|].
  rewrite eq_dec_refl; split; reflexivity.
Qed.

Lemma make_snap : forall (sh : share) v p, view_shift (ghost (sh, v) p) (ghost_snap v p * ghost (sh, v) p).
Proof.
  intros; destruct (eq_dec sh Share.bot).
  - subst; setoid_rewrite ghost_snap_join; [unfold ghost_snap; reflexivity | apply join_refl].
  - rewrite snap_master_join by auto.
    apply derives_view_shift; entailer!.
Qed.

Lemma ghost_snap_forget : forall v1 v2 p, ord v1 v2 -> view_shift (ghost_snap v2 p) (ghost_snap v1 p).
Proof.
  intros; apply ghost_update.
  intros (shc, c) [(shx, x) [? Hj]]; simpl in *.
  rewrite eq_dec_refl in Hj.
  assert (shx = shc) by (eapply sepalg.join_eq; eauto); subst.
  unfold share in Hj; destruct (eq_dec shc Share.bot); subst.
  - destruct (join_compat _ _ _ _ Hj H) as [x' []].
    exists (Share.bot, x'); simpl.
    rewrite !eq_dec_refl; auto.
  - destruct Hj; subst.
    exists (shc, c); simpl.
    rewrite eq_dec_refl; if_tac; [contradiction|].
    split; auto; split; auto.
    etransitivity; eauto.
Qed.

Lemma ghost_snap_choose : forall v1 v2 p, view_shift (ghost_snap v1 p * ghost_snap v2 p) (ghost_snap v1 p).
Proof.
  intros.
  eapply view_shift_assert.
  { apply ghost_conflict. }
  intros [x [? Hj]]; simpl in *.
  rewrite !eq_dec_refl in Hj.
  erewrite ghost_snap_join by eauto; apply join_ord in Hj; destruct Hj.
  apply ghost_snap_forget; eauto.
Qed.

Lemma master_share_join : forall sh1 sh2 sh v p, sepalg.join sh1 sh2 sh ->
  ghost (sh1, v) p * ghost (sh2, v) p = ghost (sh, v) p.
Proof.
  intros; apply ghost_join; simpl; split; auto.
  if_tac; if_tac; try split; auto; try apply ord_refl; apply join_refl.
Qed.

Lemma master_inj : forall sh1 sh2 v1 v2 p, readable_share sh1 -> readable_share sh2 ->
  ghost (sh1, v1) p * ghost (sh2, v2) p |-- !!(v1 = v2).
Proof.
  intros.
  eapply derives_trans; [apply ghost_conflict|].
  apply prop_left; intros ((?, ?) & Hj); simpl in Hj.
  destruct (eq_dec sh1 Share.bot); [subst; contradiction unreadable_bot|].
  destruct (eq_dec sh2 Share.bot); [subst; contradiction unreadable_bot|].
  destruct Hj as [? []]; subst; apply prop_right; auto.
Qed.

Lemma master_share_join' : forall sh1 sh2 sh v1 v2 p, readable_share sh1 -> readable_share sh2 ->
  sepalg.join sh1 sh2 sh ->
  ghost (sh1, v1) p * ghost (sh2, v2) p = !!(v1 = v2) && ghost (sh, v2) p.
Proof.
  intros; apply mpred_ext.
  - assert_PROP (v1 = v2) by (apply master_inj; auto).
    subst; erewrite master_share_join; eauto; entailer!.
  - Intros; subst.
    erewrite master_share_join; eauto.  apply derives_refl.
Qed.

(* useful when we only want to deal with full masters *)
Definition ghost_master (a : A) p := ghost (Tsh, a) p.

Lemma snap_master_join1 : forall v1 v2 p,
  ghost_snap v1 p * ghost_master v2 p = !!(ord v1 v2) && ghost_master v2 p.
Proof.
  intros; apply snap_master_join, Share.nontrivial.
Qed.

Lemma snap_master_update1 : forall v1 v2 p v', ord v2 v' ->
  view_shift (ghost_snap v1 p * ghost_master v2 p) (ghost_snap v' p * ghost_master v' p).
Proof.
  intros; rewrite !snap_master_join1.
  etransitivity.
  - apply view_shift_prop; intro.
    apply master_update; eauto.
  - apply derives_view_shift; entailer!. apply derives_refl.
Qed.

End Snapshot.

Section GVar.

Context {A : Type}.

Instance univ_PCM : PCM A := { join a b c := True }.
Proof.
  - auto.
  - eauto.
Defined.

Instance univ_order : PCM_order (fun _ _ => True).
Proof.
  constructor; auto.
  intros; exists a; auto.
Defined.

Definition ghost_var (sh : share) (v : A) p := ghost (sh, v) p.

Lemma ghost_var_share_join : forall sh1 sh2 sh v p, sepalg.join sh1 sh2 sh ->
  ghost_var sh1 v p * ghost_var sh2 v p = ghost_var sh v p.
Proof.
  apply master_share_join.
Qed.

Lemma ghost_var_inj : forall sh1 sh2 v1 v2 p, readable_share sh1 -> readable_share sh2 ->
  ghost_var sh1 v1 p * ghost_var sh2 v2 p |-- !!(v1 = v2).
Proof.
  apply master_inj.
Qed.

Lemma ghost_var_share_join' : forall sh1 sh2 sh v1 v2 p, readable_share sh1 -> readable_share sh2 ->
  sepalg.join sh1 sh2 sh ->
  ghost_var sh1 v1 p * ghost_var sh2 v2 p = !!(v1 = v2) && ghost_var sh v2 p.
Proof.
  apply master_share_join'.
Qed.

Lemma ghost_var_update : forall v p v', view_shift (ghost_var Tsh v p) (ghost_var Tsh v' p).
Proof.
  intros; apply master_update; auto.
Qed.

Lemma ghost_var_precise : forall sh p, precise (EX v : A, ghost_var sh v p).
Proof.
  intros; apply derives_precise' with (EX g : share * A, ghost g p), ex_ghost_precise.
  Intro v; Exists (sh, v); auto.  apply derives_refl.
Qed.

Lemma ghost_var_precise' : forall sh v p, precise (ghost_var sh v p).
Proof.
  intros; apply derives_precise with (Q := EX v : A, ghost_var sh v p);
    [exists v; auto | apply ghost_var_precise].
Qed.

Lemma ghost_var_init : forall (g : share * A), exists g', joins g g'.
Proof.
  intros (sh, a); exists (Share.bot, a), (sh, a); simpl.
  split; auto.
  rewrite !eq_dec_refl; if_tac; auto.
Qed.

End GVar.

Section Reference.
(* One common kind of PCM is one in which a central authority has a reference copy, and clients pass around
   partial knowledge. When a client recovers all pieces, it can gain full knowledge. *)
(* This is related to the snapshot PCM, but the snapshots aren't duplicable. *)

Context `{P : PCM}.

Instance pos_PCM : PCM (option (share * A)) := { join a b c :=
  match a, b, c with
  | Some (sha, a'), Some (shb, b'), Some (shc, c') =>
      sha <> Share.bot /\ shb <> Share.bot /\ sepalg.join sha shb shc /\ join a' b' c'
  | Some (sha, a'), None, Some c' => sha <> Share.bot /\ c' = (sha, a')
  | None, Some (shb, b'), Some c' => shb <> Share.bot /\ c' = (shb, b')
  | None, None, None => True
  | _, _, _ => False
  end }.
Proof.
  - destruct a as [(?, ?)|], b as [(?, ?)|], c as [(?, ?)|]; auto.
    intros (? & ? & ? & ?); repeat (split; auto); apply join_comm; auto.
  - destruct a as [(?, ?)|], b as [(?, ?)|], c as [(?, ?)|], d as [(?, ?)|], e as [(?, ?)|]; try contradiction;
      intros; decompose [and] Hjoin1; decompose [and] Hjoin2;
      repeat match goal with H : (_, _) = (_, _) |- _ => inv H end;
      try solve [eexists (Some _); split; auto; auto]; try solve [exists None; split; auto].
    + destruct (@sepalg.join_assoc _ _ _ s s0 s2 s1 s3) as (sh' & ? & ?); auto.
      destruct (join_assoc a a0 a1 a2 a3) as (a' & ? & ?); auto.
      exists (Some (sh', a')); repeat (split; auto).
      intro; subst.
      exploit join_Bot; eauto; tauto.
    + exists (Some (s2, a2)); repeat (split; auto).
      intro; subst.
      exploit join_Bot; eauto; tauto.
Defined.

Definition completable a r := exists x, join a x (Some (Tsh, r)).

Global Instance ref_PCM : PCM (option (share * A) * option A) :=
  { join a b c := join (fst a) (fst b) (fst c) /\ @join _ exclusive_PCM (snd a) (snd b) (snd c) /\
      match snd c with Some r => completable (fst c) r | None => True end }.
Proof.
  - intros ??? (Hfst & Hsnd & ?).
    split; [|split]; try apply join_comm; auto.
  - intros ????? (Hfst1 & Hsnd1 & Hcase1) (Hfst2 & Hsnd2 & Hcase2).
    destruct (join_assoc _ _ _ _ _ Hfst1 Hfst2) as (c'1 & ? & Hc'1).
    destruct (join_assoc _ _ _ _ _ Hsnd1 Hsnd2) as (c'2 & ? & Hc'2).
    exists (c'1, c'2).
    destruct Hc'2 as [(He & ?) | (? & ?)]; subst; [repeat split; simpl; auto|].
    repeat split; try solve [simpl; auto].
    simpl snd; destruct (snd e); auto.
    unfold completable.
    destruct Hcase2 as (? & Hcase2).
    apply join_comm in Hc'1.
    destruct (join_assoc _ _ _ _ _ Hc'1 Hcase2) as (? & ? & ?); eauto.
Defined.

Lemma ref_sub : forall (sh : share) (a b : A) p,
  ghost (Some (sh, a), @None A) p * ghost (@None (share * A), Some b) p |--
    !!(if eq_dec sh Tsh then a = b else exists x, join a x b).
Proof.
  intros.
  eapply derives_trans; [apply ghost_conflict|].
  apply prop_left; intros (c & Hjoin & [(? & ?) | (Hc & ?)] & Hcompat); [discriminate | apply prop_right].
  rewrite <- Hc in Hcompat; destruct Hcompat as (c' & Hsub).
  simpl in Hjoin.
  destruct (fst c); [|contradiction].
  destruct Hjoin; subst.
  simpl in Hsub.
  destruct c' as [(?, ?)|].
  - destruct Hsub as (? & ? & Hsh & ?).
    if_tac; eauto; subst.
    apply join_Tsh in Hsh; tauto.
  - destruct Hsub as (? & Hsub); inv Hsub.
    rewrite eq_dec_refl; auto.
Qed.

End Reference.

Section PVar.
(* Like ghost variables, but the partial values may be out of date. *)

Instance max_PCM : PCM Z := { join a b c := c = Z.max a b }.
Proof.
  - intros; rewrite Z.max_comm; auto.
  - intros; do 2 eexists; eauto; subst.
    rewrite Z.max_assoc; auto.
Defined.

Global Instance max_order : PCM_order Z.le.
Proof.
  constructor; simpl; intros.
  - intro; omega.
  - intros ???; omega.
  - do 2 eexists; eauto; apply Z.max_lub; auto.
  - subst; split; [apply Z.le_max_l | apply Z.le_max_r].
  - rewrite Z.max_l; auto.
Defined.

Lemma ghost_snap_join_Z : forall v1 v2 p, ghost_snap v1 p * ghost_snap v2 p = ghost_snap (Z.max v1 v2) p.
Proof.
  intros; apply ghost_snap_join; simpl; auto.
Qed.

Lemma snap_master_join' : forall v1 v2 p,
  ghost_snap v1 p * ghost_master v2 p = !!(v1 <= v2) && ghost_master v2 p.
Proof.
  intros; apply snap_master_join1.
Qed.

Lemma snap_master_update' : forall (v1 v2 : Z) p v', v2 <= v' ->
  view_shift (ghost_snap v1 p * ghost_master v2 p) (ghost_snap v' p * ghost_master v' p).
Proof.
  intros; apply snap_master_update1; auto.
Qed.

End PVar.

Section ListMap.

Require Import Sorting.Permutation.

Context {A B : Type}.

Definition disjoint (h1 h2 : list (A * B)) := forall n e, In (n, e) h1 -> forall e', ~In (n, e') h2.

Lemma disjoint_nil : forall l, disjoint l [].
Proof.
  repeat intro; contradiction.
Qed.
Hint Resolve disjoint_nil.

Lemma disjoint_comm : forall a b, disjoint a b -> disjoint b a.
Proof.
  intros ?? Hdisj ?? Hin ? Hin'.
  eapply Hdisj; eauto.
Qed.

Lemma disjoint_app : forall a b c, disjoint (a ++ b) c <-> disjoint a c /\ disjoint b c.
Proof.
  split.
  - intro; split; repeat intro; eapply H; eauto; rewrite in_app; eauto.
  - intros (Ha & Hb) ?????.
    rewrite in_app in H; destruct H; [eapply Ha | eapply Hb]; eauto.
Qed.

Require Import Morphisms.

Global Instance Permutation_disjoint :
  Proper (@Permutation _ ==> @Permutation _ ==> iff) disjoint.
Proof.
  intros ?? Hp1 ?? Hp2.
  split; intro Hdisj; repeat intro.
  - eapply Hdisj; [rewrite Hp1 | rewrite Hp2]; eauto.
  - eapply Hdisj; [rewrite <- Hp1 | rewrite <- Hp2]; eauto.
Qed.

Global Instance map_PCM : PCM (list (A * B)) := { join a b c := disjoint a b /\ Permutation (a ++ b) c }.
Proof.
  - intros ??? (Hdisj & ?); split.
    + apply disjoint_comm; auto.
    + etransitivity; [|eauto].
      apply Permutation_app_comm.
  - intros ????? (Hd1 & Hc) (Hd2 & He).
    rewrite <- Hc, disjoint_app in Hd2; destruct Hd2 as (Hd2 & Hd3).
    exists (b ++ d); repeat split; auto.
    + apply disjoint_comm; rewrite disjoint_app; split; apply disjoint_comm; auto.
    + etransitivity; [|eauto].
      rewrite app_assoc; apply Permutation_app_tail; auto.
Defined.

Lemma ghost_map_init : exists g', joins (@nil (A * B)) g'.
Proof.
  exists []; exists []; simpl; auto.
Qed.

End ListMap.
Hint Resolve disjoint_nil.

Section GHist.

(* Ghost histories in the style of Nanevsky *)
Context {hist_el : Type}.

Notation hist_part := (list (nat * hist_el)).

Definition hist_sub sh (h : hist_part) hr := if eq_dec sh Tsh then h = hr
  else sh <> Share.bot /\ exists h', disjoint h h' /\ Permutation (h ++ h') hr.

Lemma completable_alt : forall sh h hr, completable (Some (sh, h)) hr <-> hist_sub sh h hr.
Proof.
  unfold completable, hist_sub; intros; simpl; split.
  - intros ([(?, ?)|] & Hcase).
    + destruct Hcase as (? & ? & Hsh & ? & ?).
      if_tac; eauto.
      subst; apply join_Tsh in Hsh; tauto.
    + destruct Hcase as (? & Heq); inv Heq.
      rewrite eq_dec_refl; auto.
  - if_tac.
    + intro; subst; exists None; split; auto.
      apply Share.nontrivial.
    + intros (? & h' & ?); exists (Some (Share.comp sh, h')).
      split; auto.
      split.
      { intro Hbot; contradiction H.
        rewrite <- Share.comp_inv at 1.
        rewrite Hbot; apply comp_bot. }
      split; [apply comp_join_top | auto].
Qed.

Lemma hist_sub_snoc : forall sh h hr t' e (Hsub : hist_sub sh h hr) (Hfresh : ~In t' (map fst hr)),
  hist_sub sh (h ++ [(t', e)]) (hr ++ [(t', e)]).
Proof.
  unfold hist_sub; intros.
  if_tac; subst; auto.
  destruct Hsub as (? & h' & ? & Hperm); split; auto.
  exists h'; split.
  - rewrite disjoint_app; split; auto.
    intros ?? [Heq | ?]; [inv Heq | contradiction].
    intros ??; contradiction Hfresh; rewrite in_map_iff.
    do 2 eexists; [|rewrite <- Hperm, in_app; eauto]; auto.
  - rewrite <- app_assoc; etransitivity; [apply Permutation_app_head, Permutation_app_comm|].
    rewrite app_assoc; apply Permutation_app; auto.
Qed.

Definition ghost_hist (sh : share) (h : hist_part) p := (ghost (Some (sh, h), @None hist_part) p).

Lemma ghost_hist_join : forall sh1 sh2 sh h1 h2 h p (Hsh : sepalg.join sh1 sh2 sh)
  (Hh : Permutation (h1 ++ h2) h) (Hsh1 : sh1 <> Share.bot) (Hsh2 : sh2 <> Share.bot),
  ghost_hist sh1 h1 p * ghost_hist sh2 h2 p = !!(disjoint h1 h2) && ghost_hist sh h p.
Proof.
  intros; unfold ghost_hist.
  apply mpred_ext.
  - assert_PROP (disjoint h1 h2).
    { eapply derives_trans; [apply ghost_conflict|].
      apply prop_left; intros (x & ? & ?); simpl in *.
      apply prop_right; destruct (fst x) as [(?, ?)|]; [tauto | contradiction]. }
    erewrite ghost_join; [entailer!; apply derives_refl | ].
    repeat (split; simpl; auto). 
  - Intros.
    erewrite ghost_join; eauto.  apply derives_refl.
    repeat (split; simpl; auto).
Qed.

Definition hist_incl (h : hist_part) l := forall t e, In (t, e) h -> nth_error l t = Some e.

Definition hist_list (h : hist_part) l := NoDup h /\ forall t e, In (t, e) h <-> nth_error l t = Some e.

Lemma hist_list_inj : forall h l1 l2 (Hl1 : hist_list h l1) (Hl2 : hist_list h l2), l1 = l2.
Proof.
  unfold hist_list; intros; apply list_nth_error_eq.
  destruct Hl1 as (? & Hl1), Hl2 as (? & Hl2).
  intro j; specialize (Hl1 j); specialize (Hl2 j).
  destruct (nth_error l1 j).
  - symmetry; rewrite <- Hl2, Hl1; auto.
  - destruct (nth_error l2 j); auto.
    specialize (Hl2 h0); rewrite Hl1 in Hl2; tauto.
Qed.

Lemma hist_list_nil_inv1 : forall l, hist_list [] l -> l = [].
Proof.
  unfold hist_list; intros.
  destruct l; auto.
  destruct H as (_ & H).
  specialize (H O h); destruct H; simpl in *; contradiction.
Qed.

Lemma hist_list_nil_inv2 : forall h, hist_list h [] -> h = [].
Proof.
  unfold hist_list; intros.
  destruct h as [|(t, e)]; auto.
  destruct H as (_ & H).
  specialize (H t e); destruct H as (H & _).
  exploit H; [simpl; auto | rewrite nth_error_nil; discriminate].
Qed.

Lemma NoDup_remove_0 : forall {A} (l : list (nat * A)), NoDup (map fst l) -> ~In O (map fst l) ->
  NoDup (map fst (map (fun '(t, e) => ((t - 1)%nat, e)) l)).
Proof.
  induction l; auto; simpl; intros.
  inv H.
  constructor; auto.
  destruct a.
  rewrite in_map_iff; intros ((?, ?) & Heq & Hin); simpl in *; inv Heq.
  rewrite in_map_iff in Hin; destruct Hin as ((?, ?) & Heq & ?); inv Heq.
  assert (In n (map fst l)); [|contradiction].
  rewrite in_map_iff; do 2 eexists; eauto.
  destruct n; [tauto|].
  destruct n0; [|simpl in *; omega].
  assert (In O (map fst l)); [|tauto].
  rewrite in_map_iff; do 2 eexists; eauto; auto.
Qed.

Lemma NoDup_remove_0' : forall {A} (l : list (nat * A)), NoDup l -> ~In O (map fst l) ->
  NoDup (map (fun '(t, e) => ((t - 1)%nat, e)) l).
Proof.
  induction l; auto; simpl; intros.
  inv H.
  constructor; auto.
  destruct a.
  rewrite in_map_iff; intros ((?, ?) & Heq & Hin); simpl in *; inv Heq.
  destruct n; [tauto|].
  destruct n0; [|simpl in *; assert (n0 = n) by omega; subst; contradiction].
  assert (In O (map fst l)); [|tauto].
  rewrite in_map_iff; do 2 eexists; eauto; auto.
Qed.

Lemma remove_0_inj : forall {A} (l : list (nat * A)), ~In O (map fst l) ->
  map fst (map (fun '(t, e) => ((t - 1)%nat, e)) l) = map (fun t => t - 1)%nat (map fst l).
Proof.
  induction l; auto; simpl; intros.
  destruct a; rewrite IHl; auto.
Qed.

Lemma hist_list_NoDup : forall l h (Hl : hist_list h l), NoDup (map fst h).
Proof.
  induction l; intros; [apply hist_list_nil_inv2 in Hl; subst; constructor|].
  destruct Hl as (Hd & Hl).
  assert (In (O, a) h) as Hin.
  { unfold hist_list in Hl; rewrite Hl; auto. }
  exploit in_split; eauto; intros (h1 & h2 & ?); subst.
  apply NoDup_remove in Hd; destruct Hd as (? & Hn).
  assert (~In O (map fst (h1 ++ h2))) as HO.
  { rewrite in_map_iff; intros ((?, e) & ? & ?); simpl in *; subst.
    specialize (Hl O e); destruct Hl as (Hl & _); exploit Hl.
    { rewrite in_app in *; simpl; tauto. }
    simpl; intro X; inv X; contradiction. }
  exploit (IHl (map (fun x => let '(t, e) := x in ((t - 1)%nat, e)) (h1 ++ h2))).
  { split.
    { apply NoDup_remove_0'; auto. }
    intros t e.
    rewrite in_map_iff; split.
    + intros ((?, ?) & Heq & ?); inv Heq.
      specialize (Hl n e).
      destruct Hl as (Hl & _); exploit Hl.
      { rewrite in_app in *; simpl; tauto. }
      destruct n; simpl; [|rewrite Nat.sub_0_r; auto].
      contradiction HO.
      rewrite in_map_iff; do 2 eexists; eauto; auto.
    + intro Ht; specialize (Hl (S t) e); simpl in Hl.
      destruct Hl as (_ & Hl); specialize (Hl Ht).
      exists (S t, e); split; [simpl; rewrite Nat.sub_0_r; auto|].
      rewrite in_app in *; destruct Hl as [? | [Heq | ?]]; auto.
      inv Heq. }
  intro Hd; rewrite map_app; simpl; apply NoDup_add; rewrite <- map_app; auto.
  rewrite remove_0_inj in Hd; auto.
  eapply NoDup_map_inv; eauto.
Qed.

Lemma hist_list_length : forall l h (Hl : hist_list h l), Zlength h = Zlength l.
Proof.
  induction l; intros.
  - apply hist_list_nil_inv2 in Hl; subst; auto.
  - pose proof (hist_list_NoDup _ _ Hl) as Hdisj; destruct Hl as (? & Hl).
    assert (In (O, a) h) as Hin.
    { unfold hist_list in Hl; rewrite Hl; auto. }
    exploit in_split; eauto; intros (h1 & h2 & ?); subst.
    rewrite map_app in Hdisj; simpl in Hdisj; apply NoDup_remove in Hdisj.
    destruct Hdisj as (Hdisj & Hn).
    exploit (IHl (map (fun x => let '(t, e) := x in ((t - 1)%nat, e)) (h1 ++ h2))).
    { split.
      { apply NoDup_remove in H; destruct H.
        apply NoDup_remove_0'; auto.
        rewrite map_app; auto. }
      intros t e.
      rewrite in_map_iff; split.
      + intros ((?, ?) & Heq & ?); inv Heq.
        specialize (Hl n e).
        destruct Hl as (Hl & _); exploit Hl.
        { rewrite in_app in *; simpl; tauto. }
        destruct n; simpl; [|rewrite Nat.sub_0_r; auto].
        contradiction Hn.
        rewrite <- map_app, in_map_iff; do 2 eexists; eauto; auto.
      + intro Ht; specialize (Hl (S t) e); simpl in Hl.
        destruct Hl as (_ & Hl); specialize (Hl Ht).
        exists (S t, e); split; [simpl; rewrite Nat.sub_0_r; auto|].
        rewrite in_app in *; destruct Hl as [? | [Heq | ?]]; auto.
        inv Heq. }
    rewrite Zlength_map, !Zlength_app, !Zlength_cons; omega.
Qed.

Definition ghost_ref l p := EX hr : hist_part, !!(hist_list hr l) &&
  ghost (@None (share * hist_part), Some hr) p.

Lemma hist_next : forall h l (Hlist : hist_list h l), ~In (length l) (map fst h).
Proof.
  intros; rewrite in_map_iff; intros ((?, ?) & ? & Hin); simpl in *; subst.
  destruct Hlist as (? & Hlist); rewrite Hlist in Hin.
  pose proof (nth_error_Some l (length l)) as (Hlt & _).
  exploit Hlt; [|omega].
  rewrite Hin; discriminate.
Qed.

Lemma hist_add : forall (sh : share) (h h' : hist_part) e p t' (Hfresh : ~In t' (map fst h')),
  view_shift (ghost (Some (sh, h), Some h') p) (ghost (Some (sh, h ++ [(t', e)]), Some (h' ++ [(t', e)])) p).
Proof.
  intros; apply ghost_update.
  intros (c1, c2) ((d1, d2) & Hjoin1 & [(<- & ?) | (? & ?)] & Hcompat); try discriminate.
  simpl in *.
  destruct c1 as [(shc, hc)|], d1 as [(?, ?)|]; try contradiction.
  - destruct Hjoin1 as (? & ? & ? & Hdisj & Hperm).
    rewrite completable_alt in Hcompat; unfold hist_sub in Hcompat.
    destruct (eq_dec s Tsh).
    + subst; exists (Some (Tsh, h' ++ [(t', e)]), Some (h' ++ [(t', e)])).
      repeat (split; simpl; auto).
      * rewrite disjoint_app; split; auto.
        intros ?? [Heq | ?]; [inv Heq | contradiction].
        intros ??; contradiction Hfresh; rewrite in_map_iff.
        do 2 eexists; [|rewrite <- Hperm, in_app; eauto]; auto.
      * rewrite <- app_assoc.
        etransitivity; [apply Permutation_app_head, Permutation_app_comm|].
        rewrite app_assoc; apply Permutation_app; auto.
      * rewrite completable_alt; apply hist_sub_snoc; auto.
        unfold hist_sub; rewrite eq_dec_refl; auto.
    + destruct Hcompat as (? & l' & ? & Hperm').
      exists (Some (s, h ++ hc ++ [(t', e)]), Some (h' ++ [(t', e)])); repeat (split; simpl; auto).
      * rewrite disjoint_app; split; auto.
        intros ?? [Heq | ?]; [inv Heq | contradiction].
        intros ??; contradiction Hfresh; rewrite in_map_iff.
        do 2 eexists; [|rewrite <- Hperm', in_app, <- Hperm, in_app; eauto]; auto.
      * rewrite <- app_assoc; apply Permutation_app_head, Permutation_app_comm.
      * rewrite completable_alt, app_assoc; apply hist_sub_snoc; auto.
        unfold hist_sub; if_tac; [contradiction n; auto|].
        split; auto; exists l'; split.
        { eapply Permutation_disjoint; eauto. }
        etransitivity; [|eauto].
        apply Permutation_app; auto.
  - simpl in H; destruct Hjoin1 as (? & Hjoin1); inv Hjoin1.
    exists (Some (sh, h ++ [(t', e)]), Some (h' ++ [(t', e)])); simpl; repeat (split; auto).
    rewrite completable_alt in *; apply hist_sub_snoc; auto.
Qed.

Lemma hist_incl_nil : forall h, hist_incl [] h.
Proof.
  repeat intro; contradiction.
Qed.

Lemma hist_list_nil : hist_list [] [].
Proof.
  split; [constructor|].
  split; [contradiction | rewrite nth_error_nil; discriminate].
Qed.

Lemma hist_list_snoc : forall h l e, hist_list h l -> hist_list (h ++ [(length l, e)]) (l ++ [e]).
Proof.
  unfold hist_list; intros.
  destruct H as (Hd & H).
  assert (~In (length l, e) h).
  { rewrite H; intro Hnth.
    assert (length l < length l)%nat; [|omega].
    rewrite <- nth_error_Some, Hnth; discriminate. }
  split.
  { apply NoDup_app_iff; repeat constructor; auto.
    intros ?? [? | ?]; subst; contradiction. }
  intros; rewrite in_app; split.
  - intros [Hin | [Heq | ?]]; try contradiction.
    + rewrite H in Hin.
      rewrite nth_error_app1; auto.
      rewrite <- nth_error_Some, Hin; discriminate.
    + inv Heq; rewrite nth_error_app2, minus_diag; auto.
  - destruct (lt_dec t (length l)).
    + rewrite nth_error_app1 by auto.
      rewrite <- H; auto.
    + rewrite nth_error_app2 by omega.
      destruct (eq_dec t (length l)).
      * subst; rewrite minus_diag.
        intro Heq; inv Heq; simpl; auto.
      * destruct (t - length l)%nat eqn: Hminus; [omega | simpl; rewrite nth_error_nil; discriminate].
Qed.

Lemma hist_incl_permute : forall h1 h2 h' (Hincl : hist_incl h1 h') (Hperm : Permutation h1 h2),
  hist_incl h2 h'.
Proof.
  repeat intro.
  rewrite <- Hperm in H; auto.
Qed.

Lemma hist_sub_incl : forall sh h h', hist_sub sh h h' -> incl h h'.
Proof.
  unfold hist_sub; intros.
  destruct (eq_dec sh Tsh); [subst; apply incl_refl|].
  destruct H as (? & ? & ? & Hperm); repeat intro.
  rewrite <- Hperm, in_app; auto.
Qed.

Corollary hist_sub_list_incl : forall sh h h' l (Hsub : hist_sub sh h h') (Hlist : hist_list h' l),
  hist_incl h l.
Proof.
  unfold hist_list, hist_incl; intros.
  destruct Hlist as (_ & <-); eapply hist_sub_incl; eauto.
Qed.

Lemma hist_sub_Tsh : forall h h', hist_sub Tsh h h' = (h = h').
Proof.
  intros; unfold hist_sub; rewrite eq_dec_refl; auto.
Qed.

Lemma hist_ref_join : forall sh h l p, sh <> Share.bot ->
  ghost_hist sh h p * ghost_ref l p =
  EX h' : hist_part, !!(hist_list h' l /\ hist_sub sh h h') && ghost (Some (sh, h), Some h') p.
Proof.
  unfold ghost_hist, ghost_ref; intros; apply mpred_ext.
  - Intros hr; Exists hr.
    eapply derives_trans; [apply prop_and_same_derives, ghost_conflict|].
    apply derives_extract_prop; intros (x & Hj1 & Hj2 & Hcompat).
    destruct Hj2 as [(? & ?) | (Hsnd & ?)]; [discriminate|].
    rewrite <- Hsnd in Hcompat; simpl in *.
    destruct (fst x); [destruct Hj1 as (_ & Heq); inv Heq | contradiction].
    assert (hist_sub sh h hr) by (rewrite <- completable_alt; auto).
    entailer!.
    erewrite ghost_join; eauto.  apply derives_refl.
    simpl; auto.
  - Intros h'.
    Exists h'; entailer!.
    erewrite ghost_join; eauto.  apply derives_refl.
    repeat (split; simpl; auto).
    rewrite completable_alt; auto.
Qed.

Corollary hist_ref_join_nil : forall sh p, sh <> Share.bot ->
  ghost_hist sh [] p * ghost_ref [] p = ghost (Some (sh, [] : hist_part), Some ([] : hist_part)) p.
Proof.
  intros; rewrite hist_ref_join by auto.
  apply mpred_ext; entailer!.
  - destruct h' as [|(t, e)]; auto.
    match goal with H : hist_list _ _ |- _ => destruct H as (_ & H);
      specialize (H t e); destruct H as (Hin & _) end.
    exploit Hin; [simpl; auto | rewrite nth_error_nil; discriminate].
  - Exists ([] : hist_part); entailer!.
    split; [apply hist_list_nil|].
    unfold hist_sub; if_tac; auto.
    split; auto; exists []; auto.
Qed.

Lemma hist_ref_incl : forall sh h h' p, sh <> Share.bot ->
  ghost_hist sh h p * ghost_ref h' p |-- !!hist_incl h h'.
Proof.
  intros; rewrite hist_ref_join by auto.
  Intros l; eapply prop_right, hist_sub_list_incl; eauto.
Qed.

Lemma hist_add' : forall sh h h' e p, sh <> Share.bot ->
  view_shift (ghost_hist sh h p * ghost_ref h' p)
  (ghost_hist sh (h ++ [(length h', e)]) p * ghost_ref (h' ++ [e]) p).
Proof.
  intros; rewrite hist_ref_join by auto.
  repeat intro.
  rewrite extract_exists_in_SEP; Intro hr.
  erewrite extract_prop_in_SEP with (n := O); simpl; eauto; Intros.
  match goal with H : hist_list _ _ |- _ => pose proof (hist_next _ _ H) end.
  apply hist_add with (e := e)(t' := length h'); auto.
  eapply semax_pre; [|eauto].
  go_lowerx; rewrite hist_ref_join by auto.
  Exists (hr ++ [(length h', e)]); entailer!.
  split; [apply hist_list_snoc | apply hist_sub_snoc]; auto.
Qed.

Definition newer (l : hist_part) t := Forall (fun x => fst x < t)%nat l.

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

Lemma hist_incl_lt : forall h l, hist_incl h l -> newer h (length l).
Proof.
  unfold hist_incl; intros.
  unfold newer; rewrite Forall_forall; intros (?, ?) Hin.
  erewrite <- nth_error_Some, H; eauto; discriminate.
Qed.

Context {d: Inhabitant hist_el}.

Definition ordered_hist h := forall i j (Hi : 0 <= i < j) (Hj : j < Zlength h),
  (fst (Znth i h) < fst (Znth j h))%nat.

Lemma ordered_nil : ordered_hist [].
Proof.
  repeat intro.
  rewrite Zlength_nil in *; omega.
Qed.

Lemma ordered_cons : forall t e h, ordered_hist ((t, e) :: h) ->
  Forall (fun x => let '(m, _) := x in t < m)%nat h /\ ordered_hist h.
Proof.
  unfold ordered_hist; split.
  - rewrite Forall_forall; intros (?, ?) Hin.
    apply In_Znth in Hin.
    destruct Hin as (j & ? & Hj).
    exploit (H 0 (j + 1)); try omega.
    { rewrite Zlength_cons; omega. }
    rewrite Znth_0_cons, Znth_pos_cons, Z.add_simpl_r, Hj by omega; auto.
  - intros; exploit (H (i + 1) (j + 1)); try omega.
    { rewrite Zlength_cons; omega. }
    rewrite !Znth_pos_cons, !Z.add_simpl_r by omega; auto.
Qed.

Lemma ordered_last : forall t e h (Hordered : ordered_hist h) (Hin : In (t, e) h)
  (Ht : Forall (fun x => let '(m, _) := x in m <= t)%nat h), last h (O, d) = (t, e).
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

Lemma ordered_hist_list : forall l h i (Hordered : ordered_hist h) (Hl : hist_list h l)
  (Hi : 0 <= i < Zlength l), Znth i h = (Z.to_nat i, Znth i l).
Proof.
  intros.
  pose proof (hist_list_length _ _ Hl) as Hlen.
  destruct Hl as (? & Hl).
  assert (nth (Z.to_nat i) (map fst h) (fst (O, d)) = Z.to_nat i) as Ht.
  { assert (length h = length l) as Hlen'
      by (rewrite Zlength_length, ZtoNat_Zlength in Hlen by (apply Zlength_nonneg); auto).
    apply nat_sorted_list_eq with (n := length h).
    - intro j; specialize (Hl j).
      split; intro Hin.
      + specialize (Hl (nth j l d)).
        erewrite nth_error_nth in Hl by omega.
        destruct Hl as (_ & Hl); rewrite in_map_iff; do 2 eexists; [|apply Hl]; eauto.
      + rewrite in_map_iff in Hin; destruct Hin as ((?, e) & ? & Hin); simpl in *; subst.
        rewrite Hl in Hin; rewrite Hlen', <- nth_error_Some, Hin; discriminate.
    - apply map_length.
    - intros i' j' ?.
      exploit (Hordered (Z.of_nat i') (Z.of_nat j')).
      { split; [omega|].
        apply Nat2Z.inj_lt; tauto. }
      { rewrite Zlength_correct; apply Nat2Z.inj_lt; tauto. }
       unfold Znth. rewrite !if_false by omega. rewrite !Nat2Z.id.
       simpl. rewrite <- map_nth. rewrite <- (map_nth _ _ _ j'). simpl. auto.
    - rewrite Hlen'. clear - Hi. rewrite <- ZtoNat_Zlength; apply Z2Nat.inj_lt; omega. }
  simpl in Ht.
  assert (Znth i (map fst h) = Z.to_nat i). rewrite <- Ht.
  rewrite <- (Z2Nat.id i) at 1 by omega. symmetry; apply nth_Znth.
  clear Ht; rename H0 into Ht.
  erewrite Znth_map in Ht by omega.
  destruct (Znth i h) as (t, e) eqn: Heq.
  specialize (Hl t e); rewrite <- Heq in Hl.
  destruct Hl as (Hl & _); exploit Hl.
  { apply Znth_In; omega. }
  intro Hnth.
  rewrite nth_error_nth with (d := d) in Hnth.
  inv Hnth. simpl in Ht. subst. f_equal. change d with default. rewrite nth_Znth.
  rewrite Z2Nat.id; auto. omega.
  simpl in Ht. subst.
(*  rewrite <- (Z2Nat.id i) by omega. *)
  destruct Hi.
  apply Z2Nat.inj_lt in H1; try list_solve.
  rewrite Zlength_correct in H1. rewrite Nat2Z.id in H1. auto.
Qed.

(* We want to be able to remove irrelevant operations from a history, leading to a slightly weaker
   correspondence between history and list of operations. *)
Inductive hist_list' : hist_part -> list hist_el -> Prop :=
| hist_list'_nil : hist_list' [] []
| hist_list'_snoc : forall h l t e h1 h2 (He : h = h1 ++ (t, e) :: h2)
    (Hlast : newer (h1 ++ h2) t) (Hrest : hist_list' (h1 ++ h2) l),
    hist_list' h (l ++ [e]).
Hint Resolve hist_list'_nil.

Lemma hist_list'_in : forall h l (Hl : hist_list' h l) e, (exists t, In (t, e) h) <-> In e l.
Proof.
  induction 1.
  - split; [intros (? & ?)|]; contradiction.
  - intro; subst; split.
    + intros (? & Hin); rewrite in_app in *.
      destruct Hin as [? | [Heq | ?]]; try solve [left; rewrite <- IHHl; eexists; rewrite in_app; eauto].
      inv Heq; simpl; auto.
    + rewrite in_app; intros [Hin | [Heq | ?]]; [| inv Heq | contradiction].
      * rewrite <- IHHl in Hin; destruct Hin as (? & ?).
        eexists; rewrite in_app in *; simpl; destruct H; eauto.
      * eexists; rewrite in_app; simpl; eauto.
Qed.

Lemma hist_list_weak : forall l h (Hl : hist_list h l), hist_list' h l.
Proof.
  induction l using rev_ind; intros.
  - apply hist_list_nil_inv2 in Hl; subst; auto.
  - pose proof (hist_list_NoDup _ _ Hl) as HNoDup.
    destruct Hl as (Hd & Hl).
    destruct (Hl (length l) x) as (_ & H); exploit H.
    { rewrite nth_error_app2, minus_diag by omega; auto. }
    intro; exploit in_split; eauto; intros (h1 & h2 & ?).
    subst; rewrite map_app in HNoDup; simpl in HNoDup; apply NoDup_remove in HNoDup.
    rewrite <- map_app in HNoDup.
    assert (hist_list (h1 ++ h2) l) as Hl'.
    { split.
      { apply NoDup_remove in Hd; tauto. }
      intros t e; specialize (Hl t e).
      split; intro Hin.
      + destruct Hl as (Hl & _); exploit Hl.
        { rewrite in_app in *; simpl; tauto. }
        intro Hnth; assert (t < length (l ++ [x]))%nat.
        { rewrite <- nth_error_Some, Hnth; discriminate. }
        rewrite app_length in *; simpl in *.
        rewrite nth_error_app1 in Hnth; auto.
        destruct (eq_dec t (length l)); [|omega].
        destruct HNoDup as (? & HNoDup); contradiction HNoDup.
        rewrite in_map_iff; do 2 eexists; eauto; auto.
      + assert (t < length l)%nat.
        { rewrite <- nth_error_Some, Hin; discriminate. }
        destruct Hl as (_ & Hl); exploit Hl.
        { rewrite nth_error_app1; auto. }
        rewrite !in_app; intros [? | [Heq | ?]]; auto; inv Heq; omega. }
    econstructor; eauto.
    subst; unfold newer; rewrite Forall_forall; intros (t, e) Hin.
    rewrite <- nth_error_Some.
    destruct Hl' as (? & Hl').
    destruct (Hl' t e) as (Hnth & _); simpl; rewrite Hnth by auto; discriminate.
Qed.

Lemma hist_list'_NoDup : forall h l, hist_list' h l -> NoDup (map fst h).
Proof.
  induction 1.
  - constructor.
  - subst; rewrite map_app in *; simpl.
    apply NoDup_add; auto.
    rewrite <- map_app, in_map_iff; intros ((?, ?) & ? & ?); subst.
    unfold newer in Hlast; rewrite Forall_forall in Hlast.
    exploit Hlast; eauto; omega.
Qed.

Lemma hist_list'_perm : forall h l, hist_list' h l -> Permutation.Permutation (map snd h) l.
Proof.
  induction 1; auto; subst.
  rewrite map_app; simpl.
  symmetry; etransitivity; [apply Permutation.Permutation_app_comm|].
  apply Permutation.Permutation_cons_app; symmetry.
  rewrite map_app in *; auto.
Qed.

Corollary hist_list_perm : forall h l, hist_list h l -> Permutation.Permutation (map snd h) l.
Proof.
  intros; apply hist_list'_perm, hist_list_weak; auto.
Qed.

Lemma ghost_hist_init : exists g', joins (Some (Tsh, ([] : hist_part)), Some ([] : hist_part)) g'.
Proof.
  exists (None, None), (Some (Tsh, []), Some []); simpl.
  pose proof Share.nontrivial.
  unfold completable; repeat split; auto.
  exists None; simpl.
  split; auto.
Qed.

Inductive add_events h : list hist_el -> hist_part -> Prop :=
| add_events_nil : add_events h [] h
| add_events_snoc : forall le h' t e (Hh' : add_events h le h') (Ht : newer h' t),
    add_events h (le ++ [e]) (h' ++ [(t, e)]).
Hint Resolve add_events_nil.

Lemma add_events_1 : forall h t e (Ht : newer h t), add_events h [e] (h ++ [(t, e)]).
Proof.
  intros; apply (add_events_snoc _ []); auto.
Qed.

Lemma add_events_trans : forall h le h' le' h'' (H1 : add_events h le h') (H2 : add_events h' le' h''),
  add_events h (le ++ le') h''.
Proof.
  induction 2.
  - rewrite app_nil_r; auto.
  - rewrite app_assoc; constructor; auto.
Qed.

Lemma add_events_add : forall h le h', add_events h le h' -> exists h2, h' = h ++ h2 /\ map snd h2 = le.
Proof.
  induction 1.
  - eexists; rewrite app_nil_r; auto.
  - destruct IHadd_events as (? & -> & ?).
    rewrite <- app_assoc; do 2 eexists; eauto.
    subst; rewrite map_app; auto.
Qed.

Corollary add_events_snd : forall h le h', add_events h le h' -> map snd h' = map snd h ++ le.
Proof.
  intros; apply add_events_add in H.
  destruct H as (? & ? & ?); subst.
  rewrite map_app; auto.
Qed.

Corollary add_events_incl : forall h le h', add_events h le h' -> incl h h'.
Proof.
  intros; apply add_events_add in H.
  destruct H as (? & ? & ?); subst.
  apply incl_appl, incl_refl.
Qed.

Corollary add_events_newer : forall h le h' t, add_events h le h' -> newer h' t -> newer h t.
Proof.
  intros; eapply Forall_incl, add_events_incl; eauto.
Qed.

Lemma add_events_in : forall h le h' e, add_events h le h' -> In e le -> exists t, newer h t /\ In (t, e) h'.
Proof.
  induction 1; [contradiction|].
  rewrite in_app; intros [? | [? | ?]]; try contradiction.
  - destruct IHadd_events as (? & ? & ?); auto.
    do 2 eexists; [|rewrite in_app]; eauto.
  - subst; do 2 eexists; [|rewrite in_app; simpl; eauto].
    eapply add_events_newer; eauto.
Qed.

Lemma add_events_ordered : forall h le h', add_events h le h' -> ordered_hist h -> ordered_hist h'.
Proof.
  induction 1; auto; intros.
  apply ordered_snoc; auto.
Qed.

Lemma add_events_last : forall h le h', add_events h le h' -> le <> [] -> snd (last h' (O, d)) = last le d.
Proof.
  intros; apply add_events_add in H.
  destruct H as (? & ? & ?); subst.
  rewrite last_app.
  setoid_rewrite last_map at 2; auto.
  { intro; subst; contradiction. }
Qed.

Lemma add_events_NoDup : forall h le h', add_events h le h' -> NoDup (map fst h) -> NoDup (map fst h').
Proof.
  induction 1; auto; intros.
  rewrite map_app, NoDup_app_iff.
  split; auto.
  split; [repeat constructor; simpl; auto|].
  simpl; intros ? Hin [? | ?]; [subst | contradiction].
  unfold newer in Ht.
  rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
  rewrite Forall_forall in Ht; specialize (Ht _ Hin); omega.
Qed.

End GHist.

Section AEHist.

(* These histories should be usable for any atomically accessed location. *)
Inductive AE_hist_el := AE (r : val) (w : val).

Fixpoint apply_hist a h :=
  match h with
  | [] => Some a
  | AE r w :: h' => if eq_dec r a then apply_hist w h' else None
  end.

Arguments eq_dec _ _ _ _ : simpl never.

Lemma apply_hist_app : forall h1 i h2, apply_hist i (h1 ++ h2) =
  match apply_hist i h1 with Some v => apply_hist v h2 | None => None end.
Proof.
  induction h1; auto; simpl; intros.
  destruct a.
  destruct (eq_dec r i); auto.
Qed.

End AEHist.

Notation AE_hist := (list (nat * AE_hist_el)).

End Ghost.

Hint Resolve disjoint_nil hist_incl_nil hist_list_nil ordered_nil hist_list'_nil add_events_nil.
Hint Resolve ghost_var_precise ghost_var_precise'.
Hint Resolve ghost_var_init master_init ghost_map_init ghost_hist_init : init.

Ltac view_shift_intro a := repeat rewrite ?exp_sepcon1, ?exp_sepcon2, ?sepcon_andp_prop, ?sepcon_andp_prop';
  repeat match goal with
    | |-view_shift (exp _) _ => apply view_shift_exists; intro a
    | |-view_shift (!!_ && _) _ => apply view_shift_prop; fancy_intros false
  end.

Ltac view_shift_intros := repeat rewrite ?exp_sepcon1, ?exp_sepcon2, ?sepcon_andp_prop, ?sepcon_andp_prop';
  repeat match goal with
    | |-view_shift (!!_ && _) _ => apply view_shift_prop; fancy_intros false
  end.
