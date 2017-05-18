Require Import veric.rmaps.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.general_atomics.

Set Bullet Behavior "Strict Subproofs".

(* Invariants are probably unsound under RA. How can we prove linearizability of RA programs, then? *)

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
Definition protocol_inv (ord : state -> state -> Prop) T l g g' := EX v : Z, EX s : state,
  !!(field_compatible tint [] l /\ repable_signed v) &&
  mapsto Tsh tint l (vint v) * ghost_master s g * ghost_var gsh1 s g' * T s v.

Definition protocol_R l g g' (s : state) ord T := invariant (protocol_inv ord T l g g') * ghost_snap s g.

Definition protocol_W l g g' (s : state) ord T := invariant (protocol_inv ord T l g g') * ghost_var gsh2 s g'.

Lemma protocol_inv_super_non_expansive : forall n ord T l g g',
  compcert_rmaps.RML.R.approx n (protocol_inv ord T l g g') =
  compcert_rmaps.RML.R.approx n (protocol_inv ord (fun s v => compcert_rmaps.RML.R.approx n (T s v)) l g g').
Proof.
  intros; unfold protocol_inv.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_exp; apply f_equal; extensionality s.
  rewrite !approx_sepcon, !approx_andp, approx_idem; auto.
Qed.

Lemma protocol_R_super_non_expansive : forall n l g g' s ord T,
  compcert_rmaps.RML.R.approx n (protocol_R l g g' s ord T) =
  compcert_rmaps.RML.R.approx n (protocol_R l g g' s ord (fun s v => compcert_rmaps.RML.R.approx n (T s v))).
Proof.
  intros; unfold protocol_R.
  rewrite !approx_sepcon; f_equal.
  rewrite invariant_super_non_expansive; setoid_rewrite invariant_super_non_expansive at 2.
  rewrite protocol_inv_super_non_expansive; auto.
Qed.

Lemma protocol_W_super_non_expansive : forall n l g g' s ord T,
  compcert_rmaps.RML.R.approx n (protocol_W l g g' s ord T) =
  compcert_rmaps.RML.R.approx n (protocol_W l g g' s ord (fun s v => compcert_rmaps.RML.R.approx n (T s v))).
Proof.
  intros; unfold protocol_W.
  rewrite !approx_sepcon; f_equal.
  rewrite invariant_super_non_expansive; setoid_rewrite invariant_super_non_expansive at 2.
  rewrite protocol_inv_super_non_expansive; auto.
Qed.

Context `{PCM_order state}.

Lemma protocol_R_duplicable : forall l g g' s ord T, duplicable (protocol_R l g g' s ord T).
Proof.
  intros; unfold protocol_R.
  apply sepcon_duplicable; auto with dup.
  apply ghost_snap_duplicable.
Qed.

End protocols.

Definition OrdType s := ArrowType s (ArrowType s (ConstType Prop)).

Definition LA_type := ProdType (ProdType (ProdType (ProdType (ProdType (ConstType (val * val * val))
  (DependentType 0)) (OrdType (DependentType 0)))
  (ArrowType (DependentType 0) (ArrowType (ConstType Z) Mpred))) Mpred) (ArrowType (ConstType Z) Mpred).

Program Definition load_acq_spec := TYPE LA_type
  WITH l : val, g : val, g' : val, s : _, ord : _ -> _ -> Prop, T : _ -> Z -> mpred, P : mpred, Q : Z -> mpred
  PRE [ 1%positive OF tptr tint ]
   PROP (forall s' v, ord s s' -> repable_signed v -> view_shift (P * T s' v) (Q v); forall v, duplicable (Q v))
   LOCAL (temp 1%positive l)
   SEP (protocol_R l g g' s ord T; P)
  POST [ tint ]
   EX v : Z, EX s' : _,
   PROP (repable_signed v; ord s s')
   LOCAL (temp ret_temp (vint v))
   SEP (protocol_R l g g' s' ord T; Q v).
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((?, ?), ?), s), ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  - rewrite !prop_and, !approx_andp; f_equal.
    + rewrite !prop_forall, !(approx_allp _ _ _ s); f_equal; extensionality s'.
      rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
      rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
      setoid_rewrite approx_imp; do 2 apply f_equal.
      rewrite view_shift_super_non_expansive, !approx_sepcon; auto.
    + f_equal.
      rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
      apply duplicable_super_non_expansive.
  - unfold LOCALx; simpl; rewrite !approx_andp; apply f_equal.
    unfold SEPx; simpl; rewrite !approx_sepcon, protocol_R_super_non_expansive, approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((?, ?), ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  rewrite !approx_exp; apply f_equal; extensionality s'.
  unfold PROPx; simpl; rewrite !approx_andp; apply f_equal.
  unfold LOCALx; simpl; rewrite !approx_andp; apply f_equal.
  unfold SEPx; simpl; rewrite !approx_sepcon, protocol_R_super_non_expansive, approx_idem; auto.
Qed.

Definition SR_type := ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ConstType (val * Z * val * val))
  (DependentType 0)) (DependentType 0)) (OrdType (DependentType 0)))
  (ArrowType (DependentType 0) (ArrowType (ConstType Z) Mpred))) Mpred) Mpred.

Program Definition store_rel_spec := TYPE SR_type
  WITH l : val, v : Z, g : val, g' : val, s : _, s'' : _, st_ord : _ -> _ -> Prop, T : _ -> Z -> mpred, P : mpred, Q : mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v; forall v0, repable_signed v0 -> view_shift (P * T s v0) (T s'' v * Q); st_ord s s'')
   LOCAL (temp 1%positive l; temp 2%positive (vint v))
   SEP (protocol_W l g g' s st_ord T; P)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (protocol_W l g g' s'' st_ord T; Q).
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  - rewrite !prop_and, !approx_andp; f_equal; f_equal.
    rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
    rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
    rewrite view_shift_super_non_expansive, !approx_sepcon; auto.
  - unfold LOCALx; simpl; rewrite !approx_andp; apply f_equal.
    unfold SEPx; simpl; rewrite !approx_sepcon, protocol_W_super_non_expansive, approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; apply f_equal.
  unfold LOCALx; simpl; rewrite !approx_andp; apply f_equal.
  unfold SEPx; simpl; rewrite !approx_sepcon, protocol_W_super_non_expansive, approx_idem; auto.
Qed.

Definition CRA_type := ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ConstType (val * Z * Z * val * val))
  (DependentType 0)) (DependentType 0)) (OrdType (DependentType 0)))
  (ArrowType (DependentType 0) (ArrowType (ConstType Z) Mpred))) Mpred) (ArrowType (ConstType Z) Mpred).

Program Definition CAS_RA_spec := TYPE CRA_type
  WITH l : val, c : Z, v : Z, g : val, g' : val, s : _, s'' : _, ord : _ -> _ -> Prop, T : _ -> Z -> mpred,
       P : mpred, Q : Z -> mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint, 3%positive OF tint ]
   PROP (repable_signed c; repable_signed v; forall v0, repable_signed v0 ->
     view_shift (P * T s v0) ((if eq_dec v0 c then T s'' v else T s v0) * Q v0); ord s s'')
   LOCAL (temp 1%positive l; temp 2%positive (vint c); temp 3%positive (vint v))
   SEP (protocol_W l g g' s ord T; P)
  POST [ tint ]
   EX v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (Val.of_bool (if eq_dec v' c then true else false)))
   SEP (protocol_W l g g' (if eq_dec v' c then s'' else s) ord T; Q v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  - rewrite !prop_and, !approx_andp; do 2 apply f_equal; f_equal.
    rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
    rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
    rewrite view_shift_super_non_expansive, !approx_sepcon; if_tac; auto.
  - unfold LOCALx; simpl; rewrite !approx_andp; f_equal.
    unfold SEPx; simpl.
    rewrite !approx_sepcon, protocol_W_super_non_expansive, approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  unfold LOCALx; simpl; rewrite !approx_andp; f_equal.
  unfold SEPx; simpl; rewrite !approx_sepcon, protocol_W_super_non_expansive, approx_idem; auto.
Qed.

End atomics.

Hint Resolve emp_duplicable sepcon_duplicable invariant_duplicable ghost_snap_duplicable prop_duplicable : dup.
