Require Import veric.rmaps.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.general_atomics.

Set Bullet Behavior "Strict Subproofs".

(* Invariants are unsound under RA. But maybe if it's just on writes... *)

Definition gsh1 := fst (Share.split Tsh).
Definition gsh2 := snd (Share.split Tsh).

Lemma readable_gsh1 : readable_share gsh1.
Proof.
  apply slice.split_YES_ok1; auto.
Qed.

Lemma readable_gsh2 : readable_share gsh2.
Proof.
  apply slice.split_YES_ok2; auto.
Qed.

Lemma gsh1_gsh2_join : sepalg.join gsh1 gsh2 Tsh.
Proof.
  apply split_join; unfold gsh1, gsh2; destruct (Share.split Tsh); auto.
Qed.

Hint Resolve readable_gsh1 readable_gsh2 gsh1_gsh2_join.

Lemma gsh1_not_bot : gsh1 <> Share.bot.
Proof.
  intro X; contradiction unreadable_bot; rewrite <- X; auto.
Qed.

Lemma gsh2_not_bot : gsh2 <> Share.bot.
Proof.
  intro X; contradiction unreadable_bot; rewrite <- X; auto.
Qed.

Hint Resolve gsh1_not_bot gsh2_not_bot.

Section atomics.

Context {CS : compspecs}.

Definition duplicable P := view_shift P (P * P).

Lemma emp_duplicable : duplicable emp.
Proof.
  repeat intro.
  rewrite sepcon_emp in H; auto.
Qed.
Hint Resolve emp_duplicable : dup.

Lemma sepcon_duplicable : forall P Q, duplicable P -> duplicable Q -> duplicable (P * Q).
Proof.
  intros; unfold duplicable.
  rewrite <- sepcon_assoc, (sepcon_comm (_ * Q)), <- sepcon_assoc, sepcon_assoc.
  apply view_shift_sepcon; auto.
Qed.
Hint Resolve sepcon_duplicable : dup.

Lemma sepcon_list_duplicable : forall lP, Forall duplicable lP -> duplicable (fold_right sepcon emp lP).
Proof.
  induction 1; simpl; auto with dup.
Qed.

Lemma invariant_duplicable : forall P, duplicable (invariant P).
Proof.
  intros; unfold duplicable; rewrite invariant_duplicable at 1; reflexivity.
Qed.
Hint Resolve invariant_duplicable : dup.

Lemma ghost_snap_duplicable : forall `{_ : PCM_order} (s : A) p, duplicable (ghost_snap s p).
Proof.
  intros; unfold duplicable.
  erewrite ghost_snap_join; [reflexivity|].
  apply ord_join; reflexivity.
Qed.
Hint Resolve ghost_snap_duplicable : dup.

Lemma prop_duplicable : forall P Q, duplicable Q -> duplicable (!!P && Q).
Proof.
  intros.
  apply view_shift_prop; intro.
  etransitivity; eauto.
  apply derives_view_shift; entailer!.
Qed.
Hint Resolve prop_duplicable : dup.

Lemma exp_duplicable : forall {A} (P : A -> mpred), (forall x, duplicable (P x)) -> duplicable (exp P).
Proof.
  unfold duplicable; intros.
  view_shift_intro x.
  etransitivity; eauto.
  apply derives_view_shift; Exists x x; auto.
Qed.

Lemma duplicable_super_non_expansive : forall n P, compcert_rmaps.RML.R.approx n (!!duplicable P) =
  compcert_rmaps.RML.R.approx n (!!duplicable (compcert_rmaps.RML.R.approx n P)).
Proof.
  intros; unfold duplicable.
  rewrite view_shift_super_non_expansive, approx_sepcon; auto.
Qed.

Section protocols.

Context {state : Type}.

(* Iris-weak gives a more in-depth encoding of protocol assertions in terms of invariants and ghost state. This
   simpler one is probably still sound and almost as powerful. *)
Definition protocol_inv (ord : state -> state -> Prop) T l g := EX v : Z, EX s : state,
  !!(repable_signed v) && data_at Tsh tint (vint v) l * ghost (gsh1, s) g * T s v.

Definition protocol_piece (sh : share) l g (s : state) ord T :=
  invariant (protocol_inv ord T l g) * ghost (sh, s) g.

Definition protocol_R := protocol_piece Share.bot.
Definition protocol_W := protocol_piece gsh2.

Lemma protocol_inv_super_non_expansive : forall n ord T l g,
  compcert_rmaps.RML.R.approx n (protocol_inv ord T l g) =
  compcert_rmaps.RML.R.approx n (protocol_inv ord (fun s v => compcert_rmaps.RML.R.approx n (T s v)) l g).
Proof.
  intros; unfold protocol_inv.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_exp; apply f_equal; extensionality s.
  rewrite !approx_sepcon, !approx_andp, approx_idem; auto.
Qed.

Lemma protocol_piece_super_non_expansive : forall n sh l g s ord T,
  compcert_rmaps.RML.R.approx n (protocol_piece sh l g s ord T) =
  compcert_rmaps.RML.R.approx n (protocol_piece sh l g s ord (fun s v => compcert_rmaps.RML.R.approx n (T s v))).
Proof.
  intros; unfold protocol_piece.
  rewrite !approx_sepcon; f_equal.
  rewrite invariant_super_non_expansive; setoid_rewrite invariant_super_non_expansive at 2.
  rewrite protocol_inv_super_non_expansive; auto.
Qed.

Context `{PCM_order state}.

Lemma make_protocol_R : forall sh l g s T,
  view_shift (protocol_piece sh l g s ord T) (protocol_piece sh l g s ord T * protocol_R l g s ord T).
Proof.
  intros; unfold protocol_W, protocol_R, protocol_piece.
  rewrite <- sepcon_assoc, (sepcon_comm _ (invariant _)), <- sepcon_assoc, <- general_atomics.invariant_duplicable.
  rewrite sepcon_assoc, !(sepcon_comm (invariant _)); apply invariant_view_shift.
  unfold protocol_inv.
  etransitivity; [apply view_shift_sepcon1, make_snap|].
  rewrite (sepcon_comm _ (ghost _ _)); reflexivity.
Qed.

Corollary protocol_R_duplicable : forall l g s T, duplicable (protocol_R l g s ord T).
Proof.
  intros; apply make_protocol_R.
Qed.

Corollary protocol_W_R : forall l g s T,
  view_shift (protocol_W l g s ord T) (protocol_W l g s ord T * protocol_R l g s ord T).
Proof.
  intros; apply make_protocol_R.
Qed.

Lemma protocol_R_absorb : forall sh l g s s' T, sh <> Share.bot ->
  view_shift (protocol_piece sh l g s ord T * protocol_R l g s' ord T) (!!(ord s' s) && protocol_piece sh l g s ord T).
Proof.
  intros; unfold protocol_R, protocol_piece.
  rewrite <- sepcon_assoc, (sepcon_comm _ (invariant _)), <- sepcon_assoc, <- general_atomics.invariant_duplicable.
  rewrite <- sepcon_andp_prop.
  rewrite sepcon_assoc, !(sepcon_comm (invariant _)); apply invariant_view_shift.
  unfold protocol_inv.
  rewrite !(later_exp' _ 0); view_shift_intro v.
  rewrite !(later_exp' _ s); view_shift_intro s0.
  rewrite (sepcon_comm _ (ghost _ _)); setoid_rewrite snap_master_join; auto.
  apply derives_view_shift; Exists v; entailer!.
  apply sepcon_derives; auto.
  apply later_derives; Exists s0; entailer!.
Qed.

Corollary protocol_R_W : forall l g s s' T,
  view_shift (protocol_W l g s ord T * protocol_R l g s' ord T) (!!(ord s' s) && protocol_W l g s ord T).
Proof.
  intros; apply protocol_R_absorb.
  intro X; contradiction unreadable_bot; rewrite <- X; auto.
Qed.

Lemma protocol_R_join : forall l g s1 s2 s T, join s1 s2 s ->
  protocol_R l g s1 ord T * protocol_R l g s2 ord T = protocol_R l g s ord T.
Proof.
  intros; unfold protocol_R, protocol_piece.
  rewrite <- sepcon_assoc, (sepcon_comm _ (invariant _)), <- sepcon_assoc, <- general_atomics.invariant_duplicable.
  rewrite sepcon_assoc; setoid_rewrite ghost_snap_join; eauto; reflexivity.
Qed.

Corollary protocol_R_R : forall l g s1 s2 T, ord s1 s2 ->
  protocol_R l g s1 ord T * protocol_R l g s2 ord T = protocol_R l g s2 ord T.
Proof.
  intros; apply protocol_R_join.
  apply join_comm, ord_join; auto.
Qed.

Lemma protocol_R_join' : forall l g s1 s2 T,
  protocol_R l g s1 ord T * protocol_R l g s2 ord T |--
  EX s : _, !!(join s1 s2 s) && protocol_R l g s ord T.
Proof.
  intros.
  assert_PROP (joins s1 s2) as Hs;
    [|destruct Hs as (s & ?); Exists s; entailer!; erewrite protocol_R_join; eauto].
  unfold protocol_R, protocol_piece; rewrite <- sepcon_assoc, (sepcon_comm _ (invariant _)), <- sepcon_assoc,
    <- general_atomics.invariant_duplicable, sepcon_assoc, sepcon_comm.
  apply sepcon_derives_prop.
  eapply derives_trans; [apply ghost_conflict|].
  apply prop_left; intros ((s', ?) & ? & Hjoin); simpl in *; apply prop_right.
  rewrite !eq_dec_refl in Hjoin; eexists; eauto.
Qed.

Lemma make_protocol' : forall l g v s T, repable_signed v ->
  view_shift (data_at Tsh tint (vint v) l * ghost_master s g * T s v) (protocol_W l g s ord T).
Proof.
  intros.
  setoid_rewrite <- ghost_var_share_join; eauto.
  unfold protocol_W.
  rewrite !sepcon_assoc, (sepcon_comm (ghost_var gsh2 _ _)), <- !sepcon_assoc.
  apply view_shift_sepcon1, make_inv.
  unfold protocol_inv.
  Exists v s; entailer!.
Qed.

Lemma make_protocol : forall l v s T, repable_signed v ->
  view_shift (data_at Tsh tint (vint v) l * T s v) (EX g : val, protocol_W l g s ord T).
Proof.
  intros.
  etransitivity; [apply ghost_alloc with (g := (Tsh, s)), master_init|].
  view_shift_intro g; etransitivity; [etransitivity; [|apply make_protocol'; eauto]|].
  - apply derives_view_shift; cancel.
  - apply derives_view_shift; Exists g; auto.
Qed.

Lemma protocol_R_forget : forall l g s1 s2 T
  (Hcompat : forall s' s'', ord s1 s2 -> join s2 s' s'' -> exists s0, join s1 s' s0 /\ ord s0 s''),
  ord s1 s2 -> view_shift (protocol_R l g s2 ord T) (protocol_R l g s1 ord T).
Proof.
  intros; unfold protocol_R.
  apply view_shift_sepcon2, ghost_snap_forget; auto.
Qed.

Lemma protocol_R_choose : forall l g s1 s2 T
  (Hcompat : forall s2 s' s'', ord s1 s2 -> join s2 s' s'' -> exists s0, join s1 s' s0 /\ ord s0 s''),
  view_shift (protocol_R l g s1 ord T * protocol_R l g s2 ord T) (protocol_R l g s1 ord T).
Proof.
  intros; unfold protocol_R, protocol_piece.
  rewrite <- sepcon_assoc, (sepcon_comm _ (invariant _)), <- sepcon_assoc, <- general_atomics.invariant_duplicable.
  rewrite sepcon_assoc; apply view_shift_sepcon2, ghost_snap_choose; auto.
Qed.

Lemma protocol_piece_share_join : forall sh1 sh2 sh l g s1 s2 T (Hsh : sepalg.join sh1 sh2 sh)
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2),
  protocol_piece sh1 l g s1 ord T * protocol_piece sh2 l g s2 ord T =
  !!(s1 = s2) && protocol_piece sh l g s1 ord T.
Proof.
  intros; unfold protocol_piece.
  rewrite <- sepcon_assoc, (sepcon_comm _ (invariant _)), <- sepcon_assoc, <- general_atomics.invariant_duplicable.
  rewrite sepcon_assoc; setoid_rewrite ghost_var_share_join'; eauto.
  apply mpred_ext; entailer!.
Qed.

End protocols.

Existing Instance max_PCM.

Lemma protocol_R_choose' : forall l g s1 s2 T,
  view_shift (protocol_R l g s1 Z.le T * protocol_R l g s2 Z.le T) (protocol_R l g s1 Z.le T).
Proof.
  intros; apply protocol_R_choose; simpl; intros; subst.
  do 2 eexists; eauto; apply Z.max_le_compat_r; auto.
Qed.

Definition OrdType s := ArrowType s (ArrowType s (ConstType Prop)).
Definition PredType s := ArrowType s (ArrowType (ConstType Z) Mpred).

Definition LA_type := ProdType (ProdType (ProdType (ProdType (ProdType (ConstType (val * val))
  (DependentType 0)) (OrdType (DependentType 0))) (PredType (DependentType 0))) Mpred)
  (PredType (DependentType 0)).

Program Definition load_acq_spec := TYPE LA_type
  WITH l : val, g : val, s : _, ord : _ -> _ -> Prop, T : _ -> Z -> mpred, P : mpred, Q : _ -> Z -> mpred
  PRE [ 1%positive OF tptr tint ]
   PROP (forall s' v, ord s s' -> repable_signed v -> view_shift (P * T s' v) (P * T s' v * Q s' v)%logic;
         forall s' v, duplicable (Q s' v))
   LOCAL (temp 1%positive l)
   SEP (protocol_R l g s ord T; P)
  POST [ tint ]
   EX v : Z, EX s' : _,
   PROP (repable_signed v; ord s s')
   LOCAL (temp ret_temp (vint v))
   SEP (protocol_R l g s' ord T; P; Q s' v).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((?, ?), s), ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  - rewrite !prop_and, !approx_andp; f_equal.
    + rewrite !prop_forall, !(approx_allp _ _ _ s); f_equal; extensionality s'.
      rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
      rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
      setoid_rewrite approx_imp; do 2 apply f_equal.
      rewrite view_shift_super_non_expansive, !approx_sepcon; auto.
    + f_equal.
      rewrite !prop_forall, !(approx_allp _ _ _ s); f_equal; extensionality s'.
      rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
      apply duplicable_super_non_expansive.
  - unfold LOCALx; simpl; rewrite !approx_andp; apply f_equal.
    unfold SEPx, protocol_R; simpl; rewrite !approx_sepcon, protocol_piece_super_non_expansive, approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((?, ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  rewrite !approx_exp; apply f_equal; extensionality s'.
  unfold PROPx; simpl; rewrite !approx_andp; apply f_equal.
  unfold LOCALx; simpl; rewrite !approx_andp; apply f_equal.
  unfold SEPx, protocol_R; simpl; rewrite !approx_sepcon, protocol_piece_super_non_expansive, !approx_idem; auto.
Qed.

Definition SR_type := ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType
  (ConstType (val * Z * val)) (DependentType 0)) (DependentType 0)) (OrdType (DependentType 0))) (PredType (DependentType 0)))
  Mpred) (ArrowType (ConstType Z) Mpred)) (ConstType (list Z))) Mpred) Mpred.

(* single_writer version - multi-writer version uses protocol_R and requires that for all s',
   ord s s' -> ord s' s''. *)
(* Using the stronger version from iGPS that allows the writer to pass its own protocol_W assertion into the
   protocol invariant. *)
(* Hypothesis: in the single-writer case, it's sound to allow the writer to interact with invariants. *)
Program Definition store_rel_spec := TYPE SR_type
  WITH l : val, v : Z, g : val, s : _, s'' : _, st_ord : _ -> _ -> Prop, T : _ -> Z -> mpred,
       P : mpred, II : Z -> mpred, lI : list Z, P' : mpred, Q : mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v;
         view_shift (fold_right sepcon emp (map (fun p => |>II p) lI) * P)
                    (protocol_W l g s st_ord T * P');
         forall v0, repable_signed v0 ->
           view_shift (T s v0 * protocol_W l g s'' st_ord T * P')%logic
           (T s'' v * fold_right sepcon emp (map (fun p => |>II p) lI) * Q)%logic; st_ord s s'')
   LOCAL (temp 1%positive l; temp 2%positive (vint v))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); P)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); Q).
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  - rewrite !prop_and, !approx_andp; f_equal; f_equal; [|f_equal].
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
      * unfold protocol_W; rewrite !approx_sepcon, approx_idem, protocol_piece_super_non_expansive; auto.
    + rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
      rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2.
      unfold protocol_W; rewrite !sepcon_assoc, !approx_sepcon, !approx_sepcon_list', protocol_piece_super_non_expansive, !approx_idem.
      erewrite !map_map, map_ext; eauto.
      intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
  - unfold LOCALx; simpl; rewrite !approx_andp; apply f_equal.
    unfold SEPx; simpl; rewrite !sepcon_emp, !approx_sepcon, !approx_idem, !approx_sepcon_list'.
    erewrite !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  rewrite !approx_sepcon_list'.
  erewrite !map_map, map_ext; eauto.
  intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.

Definition CRA_type := ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ConstType (val * Z * Z * val))
  (DependentType 0)) (DependentType 0)) (OrdType (DependentType 0))) (PredType (DependentType 0))) Mpred)
  (ArrowType (ConstType Z) Mpred).

Program Definition CAS_RA_spec := TYPE CRA_type
  WITH l : val, c : Z, v : Z, g : val, s : _, s'' : _, ord : _ -> _ -> Prop, T : _ -> Z -> mpred,
       P : mpred, Q : Z -> mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint, 3%positive OF tint ]
   PROP (repable_signed c; repable_signed v; forall v0, repable_signed v0 ->
     view_shift (P * T s v0) ((if eq_dec v0 c then T s'' v else T s v0) * Q v0); ord s s'')
   LOCAL (temp 1%positive l; temp 2%positive (vint c); temp 3%positive (vint v))
   SEP (protocol_W l g s ord T; P)
  POST [ tint ]
   EX v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (Val.of_bool (if eq_dec v' c then true else false)))
   SEP (protocol_W l g (if eq_dec v' c then s'' else s) ord T; Q v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  - rewrite !prop_and, !approx_andp; do 2 apply f_equal; f_equal.
    rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
    rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
    rewrite view_shift_super_non_expansive, !approx_sepcon; if_tac; auto.
  - unfold LOCALx; simpl; rewrite !approx_andp; f_equal.
    unfold SEPx, protocol_W; simpl.
    rewrite !approx_sepcon, protocol_piece_super_non_expansive, approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  unfold LOCALx; simpl; rewrite !approx_andp; f_equal.
  unfold SEPx, protocol_W; simpl; rewrite !approx_sepcon, protocol_piece_super_non_expansive, approx_idem; auto.
Qed.

End atomics.

Hint Resolve emp_duplicable sepcon_duplicable invariant_duplicable ghost_snap_duplicable prop_duplicable : dup.
