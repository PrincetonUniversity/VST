(* This probably doesn't belong in progs. Talk to Santiago about where it should go. *)
Require Import progs.conclib.

Class PCM (A : Type) :=
  { join : A -> A -> A -> Prop;
    join_comm : forall a b c (Hjoin : join a b c), join b a c;
    join_assoc : forall a b c d e (Hjoin1 : join a b c) (Hjoin2 : join c d e),
                 exists c', join b d c' /\ join a c' e }.

Section Ghost.

Context {CS : compspecs}.

Section PCM.

Context `{M : PCM}.

(* This is an overapproximation of IRIS's concept of view shift. *)
Definition view_shift A B := forall (Espec : OracleKind) D P Q R C P',
  semax D (PROPx P (LOCALx Q (SEPx (B :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (A :: R)))) C P'.

Axiom view_shift_super_non_expansive : forall n P Q, compcert_rmaps.RML.R.approx n (!!view_shift P Q) =
  compcert_rmaps.RML.R.approx n (!!view_shift (compcert_rmaps.RML.R.approx n P) (compcert_rmaps.RML.R.approx n Q)).

Definition joins a b := exists c, join a b c.

Definition update a b := forall c, joins a c -> joins b c.

(* General PCM-based ghost state *)
Parameter ghost : forall (g : A) (p : val), mpred.

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

End Ops.

Global Instance share_PCM : PCM share := { join := sepalg.join }.
Proof.
  - intros; apply sepalg.join_comm; auto.
  - intros.
    eapply sepalg.join_assoc in Hjoin2; eauto.
    destruct Hjoin2; eauto.
Defined.

(* Instances of ghost state *)
Section GVar.

Context {A : Type}.

Lemma join_Bot : forall a b, sepalg.join a b Share.bot -> a = Share.bot /\ b = Share.bot.
Proof.
  intros ?? (? & ?).
  apply lub_bot_e; auto.
Qed.

Global Instance Var_PCM : PCM (share * A) := { join a b c := sepalg.join (fst a) (fst b) (fst c) /\
  (fst a = Share.bot /\ c = b \/ fst b = Share.bot /\ c = a \/ snd a = snd b /\ snd b = snd c) }.
Proof.
  - intros ??? (? & Hcase); split; [apply sepalg.join_comm; auto|].
    destruct Hcase as [? | [? | (-> & ?)]]; auto.
  - intros ????? (? & Hcase1) (Hj2 & Hcase2).
    eapply sepalg.join_assoc in Hj2; eauto.
    destruct Hj2 as (sh & Hj1' & Hj2').
    destruct Hcase2 as [(Hbot & ?) | [(Hbot & ?) | (? & He)]]; subst.
    + rewrite Hbot in H; apply join_Bot in H; destruct H as (Ha & Hb); rewrite Ha in *.
      assert (fst d = sh).
      { eapply sepalg.join_eq; eauto. }
      exists (sh, snd d); split; split; auto; destruct d; subst; auto.
    + rewrite Hbot in *; assert (fst b = sh).
      { eapply sepalg.join_eq; eauto. }
      exists (sh, snd b); split; split; auto; destruct b; subst; auto.
    + destruct Hcase1 as [(Hbot & ?) | [(Hbot & ?) | (? & ?)]]; subst.
      * exists (sh, snd b); split; split; auto; destruct b; subst; auto.
        rewrite Hbot in *; assert (fst e = sh).
        { eapply sepalg.join_eq; eauto. }
        destruct e; subst; simpl in *.
        rewrite He in *; auto.
      * exists (sh, snd d); split; split; auto.
        rewrite Hbot in *; assert (fst d = sh).
        { eapply sepalg.join_eq; eauto. }
        destruct d; auto.
      * rewrite <- He.
        exists (sh, snd d); split; split; auto; destruct d; simpl in *; subst; auto.
        replace (snd a) with (snd b) in *; auto.
Defined.

Lemma joins_id : forall a b, sepalg.joins (fst a) (fst b) -> snd a = snd b -> joins a b.
Proof.
  intros ?? (sh & ?) ?.
  exists (sh, snd a); simpl; auto.
Qed.

Definition ghost_var (sh : share) (v : A) p := ghost (sh, v) p.

Lemma ghost_var_share_join : forall sh1 sh2 sh v p, sepalg.join sh1 sh2 sh ->
  ghost_var sh1 v p * ghost_var sh2 v p = ghost_var sh v p.
Proof.
  intros; apply ghost_join; simpl; auto.
Qed.

Lemma ghost_var_inj : forall sh1 sh2 v1 v2 p, readable_share sh1 -> readable_share sh2 ->
  ghost_var sh1 v1 p * ghost_var sh2 v2 p |-- !!(v1 = v2).
Proof.
  intros.
  eapply derives_trans; [apply ghost_conflict|].
  apply prop_left; intros (? & ? & [(? & ?) | [(? & ?) | (? & ?)]]); simpl in *; subst;
    try (exploit unreadable_bot; eauto; contradiction).
  apply prop_right; auto.
Qed.

Lemma join_Tsh : forall a b, sepalg.join Tsh a b -> b = Tsh /\ a = Share.bot.
Proof.
  intros ?? (? & ?).
  rewrite Share.glb_commute, Share.glb_top in H; subst; split; auto.
  apply Share.lub_bot.
Qed.

Lemma ghost_var_update : forall v p v', view_shift (ghost_var Tsh v p) (ghost_var Tsh v' p).
Proof.
  intros; apply ghost_update; intros ? (? & ? & Hcase); simpl in *.
  apply join_Tsh in H; destruct H as (? & Hbot).
  exists (Tsh, v'); simpl; split; auto.
  rewrite Hbot; auto.
Qed.

Lemma ghost_var_precise : forall sh p, precise (EX v : A, ghost_var sh v p).
Proof.
  intros; eapply derives_precise, ex_ghost_precise.
  intros ? (x & ?); exists (sh, x); eauto.
Qed.

Lemma ghost_var_precise' : forall sh v p, precise (ghost_var sh v p).
Proof.
  intros; apply derives_precise with (Q := EX v : A, ghost_var sh v p);
    [exists v; auto | apply ghost_var_precise].
Qed.

Lemma ghost_var_init : forall (g : share * A), exists g', joins g g'.
Proof.
  intros (sh, a); exists (Share.bot, a), (sh, a); simpl; auto.
Qed.

End GVar.

Section Reference.
(* One common kind of PCM is one in which a central authority has a reference copy, and clients pass around
   partial knowledge. When a client recovers all pieces, it can gain full knowledge. *)
(* This is related to the snapshot PCM, but the parts have different types. *)

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

Class PCM_order `{P : PCM} (ord : A -> A -> Prop) := { ord_refl :> RelationClasses.Reflexive ord;
  ord_trans :> RelationClasses.Transitive ord;
  join_ord : forall a b c, join a b c -> ord a c /\ ord b c; ord_join : forall a b, ord b a -> join a b a }.

Section Snapshot.
(* One common kind of PCM is one in which a central authority has a reference copy, and clients pass around
   partial knowledge. *)

Context `{ORD : PCM_order}.

Definition lift_ord a b := match a with Some a => ord a b | None => True end.

Lemma join_lift_ord : forall a b c, @join _ option_PCM a b (Some c) -> lift_ord a c /\ lift_ord b c.
Proof.
  simpl; intros.
  destruct a, b; subst; simpl; try apply join_ord; try split; auto; reflexivity.
Qed.

Global Instance snap_PCM : PCM (option A * option A) :=
  { join a b c := @join _ option_PCM (fst a) (fst b) (fst c) /\ @join _ exclusive_PCM (snd a) (snd b) (snd c) /\
      match snd c with Some r => lift_ord (fst c) r | None => True end }.
Proof.
  - intros ??? (Hfst & Hsnd & ?).
    split; [|split]; try apply join_comm; auto.
  - intros ????? (Hfst1 & Hsnd1 & Hcase1) (Hfst2 & Hsnd2 & Hcase2).
    destruct (join_assoc _ _ _ _ _ Hfst1 Hfst2) as (c'1 & ? & Hc'1).
    destruct (join_assoc _ _ _ _ _ Hsnd1 Hsnd2) as (c'2 & ? & Hc'2).
    exists (c'1, c'2).
    destruct Hc'2 as [(He & ?) | (? & ?)]; subst; [repeat split; simpl; auto|].
    repeat split; try solve [simpl; auto].
    simpl snd; destruct (snd e); auto; simpl.
    destruct c'1; simpl; auto.
    destruct (fst e).
    apply join_lift_ord in Hc'1; destruct Hc'1.
    eapply ord_trans; eauto.
    { destruct (fst a); contradiction. }
Defined.

Definition ghost_snap (a : A) p := ghost (Some a, @None A) p.
Definition ghost_master (a : A) p := ghost (@None A, Some a) p.

Lemma ghost_snap_join : forall v1 v2 p v, join v1 v2 v ->
  ghost_snap v1 p * ghost_snap v2 p = ghost_snap v p.
Proof.
  intros; apply ghost_join; simpl; auto.
Qed.

Lemma snap_master_join : forall v1 v2 p,
  ghost_snap v1 p * ghost_master v2 p = !!(ord v1 v2) && ghost (Some v1, Some v2) p.
Proof.
  unfold ghost_snap, ghost_master; intros; apply mpred_ext.
  - eapply derives_trans; [apply prop_and_same_derives, ghost_conflict|].
    apply derives_extract_prop; intros (x & Hj1 & Hj2 & Hcompat).
    assert (ord v1 v2).
    { destruct Hj2 as [(? & ?) | (Hsnd & ?)]; [discriminate|].
      rewrite <- Hsnd in Hcompat; simpl in *.
      destruct (fst x); [subst; auto | contradiction]. }
    erewrite ghost_join; [entailer!|].
    simpl; auto.
  - Intros; erewrite ghost_join; eauto.
    simpl; auto.
Qed.

Lemma snap_master_update : forall v1 v2 p v', ord v2 v' ->
  view_shift (ghost_snap v1 p * ghost_master v2 p) (ghost_snap v' p * ghost_master v' p).
Proof.
  intros; rewrite !snap_master_join.
  repeat intro.
  erewrite extract_prop_in_SEP with (n := O); simpl; eauto; Intros.
  apply ghost_update with (g' := (Some v', Some v')).
  { unfold update; intros ? (? & Hfst & Hcase & Hcompat); simpl in *.
    destruct Hcase as [(Hx & ?) | (? & ?)]; [|discriminate].
    rewrite <- Hx in Hcompat.
    eexists (Some v', Some v'); simpl; repeat split; eauto; simpl; try reflexivity.
    destruct (fst c), (fst x); auto; try contradiction.
    apply join_ord in Hfst; destruct Hfst.
    eapply ord_join, ord_trans; eauto.
    eapply ord_trans; eauto. }
  eapply semax_pre; [|eauto].
  go_lowerx; entailer!.
Qed.

Lemma snap_master_init : forall (a : A), exists g', joins (Some a, Some a) g'.
Proof.
  intros; exists (None, None), (Some a, Some a); simpl.
  repeat (split; auto); reflexivity.
Qed.

End Snapshot.

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
  - subst; split; [apply Z.le_max_l | apply Z.le_max_r].
  - rewrite Z.max_l; auto.
Defined.

Lemma ghost_snap_join' : forall v1 v2 p, ghost_snap v1 p * ghost_snap v2 p = ghost_snap (Z.max v1 v2) p.
Proof.
  intros; apply ghost_snap_join; simpl; auto.
Qed.

Lemma snap_master_join' : forall v1 v2 p,
  ghost_snap v1 p * ghost_master v2 p = !!(v1 <= v2) && ghost (Some v1, Some v2) p.
Proof.
  intros; apply snap_master_join.
Qed.

Lemma snap_master_update' : forall (v1 v2 : Z) p v', v2 <= v' ->
  view_shift (ghost_snap v1 p * ghost_master v2 p) (ghost_snap v' p * ghost_master v' p).
Proof.
  intros; apply snap_master_update; auto.
Qed.

Lemma snap_master_init' : forall (v : Z), exists g', joins (Some v, Some v) g'.
Proof.
  intro; apply snap_master_init.
Qed.

End PVar.

Section GHist.

(* Ghost histories in the style of Nanevsky *)
Context {hist_el : Type}.

Notation hist_part := (list (nat * hist_el)).

Require Import Sorting.Permutation.

Definition disjoint (h1 h2 : hist_part) := forall n e, In (n, e) h1 -> forall e', ~In (n, e') h2.

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

Instance map_PCM : PCM hist_part := { join a b c := disjoint a b /\ Permutation (a ++ b) c }.
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

Definition hist_sub sh h hr := if eq_dec sh Tsh then h = hr
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
    erewrite ghost_join; [entailer!|].
    repeat (split; simpl; auto).
  - Intros.
    erewrite ghost_join; eauto.
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
    erewrite ghost_join; eauto.
    simpl; auto.
  - Intros h'.
    Exists h'; entailer!.
    erewrite ghost_join; eauto.
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

Variable (d : hist_el).

Definition ordered_hist h := forall i j (Hi : 0 <= i < j) (Hj : j < Zlength h),
  (fst (Znth i h (O, d)) < fst (Znth j h (O, d)))%nat.

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
    apply In_Znth with (d0 := (O, d)) in Hin.
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
  (Hi : 0 <= i < Zlength l), Znth i h (O, d) = (Z.to_nat i, Znth i l d).
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
      rewrite !map_nth, !nth_Znth; auto.
    - rewrite <- ZtoNat_Zlength; apply Z2Nat.inj_lt; omega. }
  rewrite nth_Znth, Z2Nat.id in Ht by tauto.
  erewrite Znth_map with (d' := (O, d)) in Ht by omega.
  destruct (Znth i h (O, d)) as (t, e) eqn: Heq.
  specialize (Hl t e); rewrite <- Heq in Hl.
  destruct Hl as (Hl & _); exploit Hl.
  { apply Znth_In; omega. }
  intro Hnth; rewrite nth_error_nth with (d := d) in Hnth by (rewrite <- nth_error_Some, Hnth; discriminate).
  simpl in *; inv Hnth.
  rewrite nth_Znth, Z2Nat.id; tauto.
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

Lemma ghost_hist_init : exists g', joins (Some (Tsh, []), Some []) g'.
Proof.
  exists (None, None), (Some (Tsh, []), Some []); simpl.
  pose proof Share.nontrivial.
  unfold completable; repeat split; auto.
  exists None; simpl.
  split; auto.
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

Hint Resolve disjoint_nil hist_incl_nil hist_list_nil ordered_nil hist_list'_nil.
Hint Resolve ghost_var_precise ghost_var_precise'.
Hint Resolve ghost_var_init snap_master_init' ghost_hist_init : init.
