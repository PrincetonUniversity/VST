Require Import VST.veric.rmaps.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.cancelable_invariants.
Require Import VST.concurrency.ghosts. 
Require Import VSTlib.locks.
Require Import VSTlib.spec_malloc.
Import FashNotation.

(* lock invariants should be exclusive *)
Definition exclusive_mpred P := P * P |-- FF.

Program Definition weak_exclusive_mpred (P: mpred): mpred :=
  unfash (fash ((P * P) --> FF)).

Lemma corable_weak_exclusive R : seplog.corable (weak_exclusive_mpred R).
Proof.
  apply assert_lemmas.corable_unfash, _.
Qed.

Lemma exclusive_mpred_nonexpansive : nonexpansive weak_exclusive_mpred.
Proof.
  unfold weak_exclusive_mpred, nonexpansive; intros.
  apply @subtypes.eqp_unfash, @subtypes.eqp_subp_subp, eqp_refl.
  apply eqp_sepcon; apply predicates_hered.derives_refl.
Qed.

Lemma exclusive_mpred_super_non_expansive:
  forall R n, compcert_rmaps.RML.R.approx n (weak_exclusive_mpred R) =
    compcert_rmaps.RML.R.approx n (weak_exclusive_mpred (compcert_rmaps.RML.R.approx n R)).
Proof.
  apply nonexpansive_super_non_expansive, exclusive_mpred_nonexpansive.
Qed.

Lemma exclusive_weak_exclusive1: forall R P,
  exclusive_mpred R ->
  P |-- weak_exclusive_mpred R.
Proof.
  intros; unfold weak_exclusive_mpred; unfold exclusive_mpred in H.
  unseal_derives; apply derives_unfash_fash; auto.
Qed.

Lemma exclusive_weak_exclusive: forall R,
  exclusive_mpred R ->
  emp |-- weak_exclusive_mpred R && emp.
Proof.
  intros; apply andp_right; auto; apply exclusive_weak_exclusive1; auto.
Qed.

Lemma weak_exclusive_conflict : forall P,
  (weak_exclusive_mpred P && emp) * P * P |-- FF.
Proof.
  intros.
  rewrite sepcon_assoc, <- andp_left_corable by (apply corable_weak_exclusive).
  unseal_derives; intros ? [].
  unfold weak_exclusive_mpred in H; specialize (H a ltac:(lia) _ _ (ageable.necR_refl _) (predicates_hered.ext_refl _)).
  apply H; auto.
Qed.

Lemma exclusive_sepcon1 : forall P Q (HP : exclusive_mpred P), exclusive_mpred (P * Q).
Proof.
  unfold exclusive_mpred; intros.
  eapply derives_trans, sepcon_FF_derives' with (P := Q * Q), HP; cancel; apply derives_refl.
Qed.

Lemma exclusive_sepcon2 : forall P Q (HP : exclusive_mpred Q), exclusive_mpred (P * Q).
Proof.
  intros; rewrite sepcon_comm; apply exclusive_sepcon1; auto.
Qed.

Lemma exclusive_andp1 : forall P Q (HP : exclusive_mpred P), exclusive_mpred (P && Q).
Proof.
  unfold exclusive_mpred; intros.
  eapply derives_trans, HP.
  apply sepcon_derives; apply andp_left1; auto.
Qed.

Lemma exclusive_andp2 : forall P Q (HQ : exclusive_mpred Q), exclusive_mpred (P && Q).
Proof.
  intros; rewrite andp_comm; apply exclusive_andp1; auto.
Qed.

Lemma exclusive_FF : exclusive_mpred FF.
Proof.
  unfold exclusive_mpred.
  rewrite FF_sepcon; auto.
Qed.

Lemma derives_exclusive : forall P Q (Hderives : P |-- Q) (HQ : exclusive_mpred Q),
  exclusive_mpred P.
Proof.
  unfold exclusive_mpred; intros.
  eapply derives_trans, HQ.
  apply sepcon_derives; auto.
Qed.

Lemma mapsto_exclusive : forall (sh : Share.t) (t : type) (v : val),
  sepalg.nonunit sh -> exclusive_mpred (EX v2 : _, mapsto sh t v v2).
Proof.
  intros; unfold exclusive_mpred.
  Intros v1 v2; apply mapsto_conflict; auto.
Qed.

Lemma field_at__exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) (p : val),
  sepalg.nonidentity sh ->
  0 < sizeof (nested_field_type t fld) -> exclusive_mpred (field_at_ sh t fld p).
Proof.
  intros; apply field_at__conflict; auto.
Qed.

Lemma ex_field_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) (p : val),
  sepalg.nonidentity sh ->
  0 < sizeof (nested_field_type t fld) -> exclusive_mpred (EX v : _, field_at sh t fld v p).
Proof.
  intros; unfold exclusive_mpred.
  Intros v v'; apply field_at_conflict; auto.
Qed.

Corollary field_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) v (p : val),
  sepalg.nonidentity sh -> 0 < sizeof (nested_field_type t fld) -> exclusive_mpred (field_at sh t fld v p).
Proof.
  intros; eapply derives_exclusive, ex_field_at_exclusive; eauto.
  Exists v; apply derives_refl.
Qed.

Lemma ex_data_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (EX v : _, data_at sh t v p).
Proof.
  intros; unfold exclusive_mpred.
  Intros v v'; apply data_at_conflict; auto.
Qed.

Corollary data_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) v (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (data_at sh t v p).
Proof.
  intros; eapply derives_exclusive, ex_data_at_exclusive; eauto.
  Exists v; apply derives_refl.
Qed.

Corollary data_at__exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (data_at_ sh t p).
Proof.
  intros; eapply derives_exclusive, data_at_exclusive; eauto.
  apply data_at__data_at; eauto.
Qed.

Definition lock_handle : Type := val * invariants.iname * ghosts.gname.

Definition ptr_of (h: lock_handle) : val := let '(v, i, g) := h in v.

  (* We can use self_part sh h * R instead of selflock sh h R. *)
Definition self_part sh (h : val * invariants.iname * ghosts.gname) := let '(v, i, g) := h in cinv_own g sh.

Lemma self_part_exclusive : forall sh h, sh <> Share.bot -> exclusive_mpred (self_part sh h).
  Proof.
    intros; unfold exclusive_mpred, self_part; destruct h as ((?, ?), ?).
    unfold cinv_own; rewrite own_op'; Intros ?.
    apply sepalg.join_self, identity_share_bot in H0; contradiction.
  Qed.

#[export] Hint Resolve self_part_exclusive : core.


Class lockAPD := {
  t_lock : type := Tstruct _atom_int noattr;
  inv_for_lock: forall (v: val) (R: mpred), mpred;
  inv_for_lock_nonexpansive : forall v, nonexpansive (inv_for_lock v)
}.

Definition lock_inv {L: lockAPD} (sh: share) (h: lock_handle)  (R: mpred) :=
   let '(v, i, g) := h in !!(sh <> Share.bot /\ isptr v) && cinvariant i g (inv_for_lock v R) * cinv_own g sh.

Lemma lock_inv_nonexpansive {L: lockAPD}  : forall sh h, nonexpansive (lock_inv sh h).
  Proof.
   intros.
    unfold lock_inv. destruct h as [[? ?] ?].
    apply sepcon_nonexpansive, const_nonexpansive.
    apply @conj_nonexpansive; [apply const_nonexpansive|].
    apply cinvariant_nonexpansive2, inv_for_lock_nonexpansive.
  Qed.

Lemma lock_inv_share_join {L: lockAPD} : forall sh1 sh2 sh3 h R, sh1 <> Share.bot -> sh2 <> Share.bot ->
    sepalg.join sh1 sh2 sh3 -> lock_inv sh1 h R * lock_inv sh2 h R = lock_inv sh3 h R.
  Proof.
    unfold lock_inv. destruct h as [[??]?]. intros.
    destruct (isptr_dec v).
    rewrite !prop_true_andp; auto.
    rewrite <- !sepcon_assoc, (sepcon_comm (_ * cinv_own _ _)), !sepcon_assoc.
    unfold cinv_own at 1 2; erewrite <- own_op by eauto.
    rewrite <- sepcon_assoc; f_equal.
    symmetry; apply cinvariant_dup.
    { split; auto; intros ?; subst. apply join_Bot in H1 as []; contradiction. }
    { rewrite prop_false_andp, !FF_sepcon, prop_false_andp, FF_sepcon; auto; intros []; contradiction. }
  Qed.

Lemma lock_inv_exclusive  {L: lockAPD} : forall sh h R, exclusive_mpred (lock_inv sh h R).
  Proof.
    intros. destruct h as [[??]?].
    unfold exclusive_mpred, lock_inv; Intros.
    unfold cinv_own. sep_apply @own_op'.
    Intros ?; Intros.
    apply sepalg.join_self, identity_share_bot in H0; contradiction.
  Qed.

Lemma lock_inv_share  {L: lockAPD} : forall sh h R, lock_inv sh h R |-- !!(sh <> Share.bot /\ isptr (ptr_of h)).
  Proof.
    intros.
    unfold lock_inv. destruct h as [[??]?]. entailer!. 
Qed.

#[export] Hint Resolve lock_inv_share : saturate_local.

#[export] Hint Resolve lock_inv_exclusive data_at_exclusive data_at__exclusive field_at_exclusive field_at__exclusive : core.

Lemma self_part_eq  {L: lockAPD} : forall 
    (sh1 sh2: share)
   (h: val * invariants.iname * ghosts.gname) R, 
   sh2 <> Share.bot -> 
    lock_inv sh1 h (self_part sh2 h * R) * self_part sh2 h =
    lock_inv sh1 h (self_part sh2 h * R) * lock_inv sh2 h (self_part sh2 h * R).
  Proof.
    intros.
    simpl; unfold self_part, lock_inv; destruct h as ((?, ?), ?).
    destruct (eq_dec sh1 Share.bot).
    { rewrite prop_false_andp, !FF_sepcon; auto; intros []; contradiction. }
    destruct (isptr_dec v).
    rewrite !prop_true_andp by auto.
    rewrite cinvariant_dup at 1.
    rewrite <- !sepcon_assoc; f_equal.
    rewrite (sepcon_comm (_ * _) (cinvariant _ _ _)), <- sepcon_assoc; reflexivity.
    { rewrite prop_false_andp, !FF_sepcon; auto; intros []; contradiction. }
  Qed.

Ltac lock_props := match goal with |-context[weak_exclusive_mpred ?P && emp] => sep_apply (exclusive_weak_exclusive P); [auto with share | try timeout 20 cancel] end.

Section lock_specs.

  Context {M: MallocAPD} {L : lockAPD}.

  Definition selflock R sh h := self_part sh h * R.

  Lemma lock_inv_isptr : forall sh h R, lock_inv sh h R |-- !! isptr (ptr_of h).
  Proof. intros. entailer!. Qed.

  Lemma lock_inv_nonexpansive2 : forall {A} (P Q : A -> mpred) sh p x, (ALL x : _, |> (P x <=> Q x) |--
    |> lock_inv sh p (P x) <=> |> lock_inv sh p (Q x))%logic.
  Proof.
    intros.
    apply allp_left with x.
    eapply derives_trans, eqp_later1; apply later_derives.
    apply nonexpansive_entail; apply lock_inv_nonexpansive.
  Qed.

  Lemma lock_inv_super_non_expansive : forall sh h R n,
    compcert_rmaps.RML.R.approx n (lock_inv sh h R) = compcert_rmaps.RML.R.approx n (lock_inv sh h (compcert_rmaps.RML.R.approx n R)).
  Proof.
    intros; apply nonexpansive_super_non_expansive, lock_inv_nonexpansive.
  Qed.

  Notation InvType := Mpred.

  (* R should be able to take the lock_handle as an argument, with subspecs for plain and selflock *)
  Program Definition makelock_spec :=
    TYPE (ProdType (ConstType globals) (ArrowType (ConstType lock_handle) InvType)) WITH gv: _, R : _
    PRE [ ]
       PROP ()
       PARAMS () GLOBALS (gv)
       SEP (M.(mem_mgr) gv)
    POST [ tptr t_lock ] EX h,
       PROP ()
       RETURN (ptr_of h)
       SEP (M.(mem_mgr) gv; lock_inv Tsh h (R h)).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x; simpl.
    reflexivity.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x; simpl.
    rewrite !approx_exp; f_equal; extensionality.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal; apply lock_inv_super_non_expansive.
  Qed.

  Program Definition freelock_spec :=
    TYPE (ProdType (ProdType (ConstType _) InvType) Mpred)
    WITH h : _, R : _, P : _
    PRE [ tptr t_lock ]
     PROP ()
     PARAMS (ptr_of h)
     SEP (lock_inv Tsh h R; P; (P * lock_inv Tsh h R * R -* FF) && emp)
   POST[ tvoid ]
     PROP ()
     LOCAL ()
     SEP (P).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    { apply lock_inv_super_non_expansive. }
    f_equal.
    rewrite !approx_andp; f_equal.
    setoid_rewrite wand_nonexpansive; rewrite !approx_sepcon; do 2 f_equal; rewrite !approx_idem; auto.
    do 2 f_equal; apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    reflexivity.
  Qed.

  Program Definition freelock_spec_simple :=
    TYPE (ProdType (ConstType _) InvType)
    WITH h : _, R : _
    PRE [ tptr t_lock ]
     PROP ()
     PARAMS (ptr_of h)
     SEP (weak_exclusive_mpred R && emp; lock_inv Tsh h R; R)
   POST[ tvoid ]
     PROP ()
     LOCAL ()
     SEP (R).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x; simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    { rewrite !approx_andp; f_equal.
      apply exclusive_mpred_super_non_expansive. }
    f_equal. apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x; simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    reflexivity.
  Qed.

  Lemma freelock_simple : funspec_sub freelock_spec freelock_spec_simple.
  Proof.
    unfold funspec_sub; simpl.
    split; auto; intros ? (h, R) ?; Intros.
    eapply derives_trans, fupd_intro.
    Exists (nil : list Type) (h, R, R) emp; entailer!.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; entailer!.
    apply andp_right, andp_left2; auto.
    rewrite <- wand_sepcon_adjoint; sep_apply weak_exclusive_conflict; auto.
    rewrite FF_sepcon; auto.
  Qed.

  Program Definition acquire_spec :=
    TYPE (ProdType (ConstType _) InvType)
    WITH sh : _, h : _, R : _
    PRE [ tptr t_lock ]
       PROP (sh <> Share.bot)
       PARAMS (ptr_of h)
       SEP (lock_inv sh h R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_inv sh h R; R).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal. apply lock_inv_super_non_expansive.
  Qed.

  Program Definition release_spec :=
    TYPE (ProdType (ProdType (ProdType (ConstType _) InvType) Mpred) Mpred)
    WITH sh : _, h : _, R : _, P : _, Q : _
    PRE [ tptr t_lock ]
       PROP (sh <> Share.bot)
       PARAMS (ptr_of h)
       SEP (weak_exclusive_mpred R && emp; |> lock_inv sh h R; P; lock_inv sh h R * P -* Q * R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (Q).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((((?, ?), ?), ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    { rewrite !approx_andp; f_equal.
      apply exclusive_mpred_super_non_expansive. }
    f_equal.
    { setoid_rewrite later_nonexpansive; do 2 f_equal.
      apply lock_inv_super_non_expansive. }
    f_equal.
    setoid_rewrite wand_nonexpansive; rewrite !approx_sepcon; do 2 f_equal; rewrite !approx_idem; f_equal.
    apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((((?, ?), ?), ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    reflexivity.
  Qed.

  Program Definition release_spec_simple :=
    TYPE (ProdType (ConstType _) InvType)
    WITH sh : _, h : _, R : _
    PRE [ tptr t_lock ]
       PROP (sh <> Share.bot)
       PARAMS (ptr_of h)
       SEP (weak_exclusive_mpred R && emp; lock_inv sh h R; R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_inv sh h R).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    { rewrite !approx_andp; f_equal.
      apply exclusive_mpred_super_non_expansive. }
    f_equal.
    apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    apply lock_inv_super_non_expansive.
  Qed.

  Lemma release_simple : funspec_sub release_spec release_spec_simple.
  Proof.
    unfold funspec_sub; simpl.
    split; auto; intros ? ((sh, h), R) ?; Intros.
    eapply derives_trans, fupd_intro.
    Exists (nil : list Type) (sh, h, R, R, lock_inv sh h R) emp; entailer!.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; entailer!.
    apply wand_refl_cancel_right.
  Qed.

(* freelock and release specialized for self_part *)
Program Definition freelock_spec_self :=
  TYPE (ProdType (ConstType _) Mpred)
  WITH sh1 : _, sh2 : _, h : _, R : _
  PRE [ tptr t_lock ]
     PROP (sh2 <> Share.bot; sepalg.join sh1 sh2 Tsh)
     PARAMS (ptr_of h)
     SEP (lock_inv sh1 h (self_part sh2 h * R); self_part sh2 h)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP ().
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((?, ?), ?), ?); simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  f_equal.
  setoid_rewrite lock_inv_super_non_expansive; do 2 f_equal.
  rewrite !approx_sepcon, approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((?, ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
Qed.

Program Definition release_spec_self :=
  TYPE (ProdType (ConstType _) Mpred)
  WITH sh : _, h : _, R : _
  PRE [ tptr t_lock ]
     PROP ()
     PARAMS (ptr_of h)
     SEP (lock_inv sh h (self_part sh h * R); R)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP ().
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((?, ?), ?); simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  f_equal.
  setoid_rewrite lock_inv_super_non_expansive; do 2 f_equal.
  rewrite !approx_sepcon, approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((?, ?), ?); simpl.
  reflexivity.
Qed.

Lemma release_self : funspec_sub release_spec release_spec_self.
Proof.
  unfold funspec_sub; simpl.
  split; auto; intros ? ((sh, h), R) ?; Intros.
  eapply derives_trans, fupd_intro.
  Exists (nil : list Type) (sh, h, self_part sh h * R, R, emp) emp; entailer!.
  { intros; unfold PROPx, LOCALx, SEPx; simpl; entailer!. }
  unfold lock_inv; destruct h as ((?, ?), ?).
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; entailer!.
  lock_props.
  { apply exclusive_sepcon1.
     apply (self_part_exclusive sh (v,i,g)); auto.
 }
  rewrite <- sepcon_emp at 1; apply sepcon_derives; [apply now_later|].
  rewrite <- wand_sepcon_adjoint, emp_sepcon; cancel.
  apply inv_dealloc.
Qed.

Lemma freelock_self : funspec_sub freelock_spec freelock_spec_self.
Proof.
  unfold freelock_spec, freelock_spec_self.
  unfold funspec_sub; simpl.
  split; auto; intros ? (((sh1, sh2), h), R) ?; Intros.
  eapply derives_trans, fupd_intro.
  Exists (nil : list Type) (h, self_part sh2 h * R, emp) emp; entailer!.
  { intros; unfold PROPx, LOCALx, SEPx; simpl; entailer!. }
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
  set (P := _ * _); entailer!; subst P.
  rewrite sepcon_emp; setoid_rewrite self_part_eq; auto.
  saturate_local.
  erewrite lock_inv_share_join by eauto; simpl; cancel.
  apply andp_right; auto.
  rewrite <- wand_sepcon_adjoint, emp_sepcon.
  destruct h as ((p, i), g); simpl; Intros.
  sep_apply cinv_own_excl.
  rewrite FF_sepcon; auto.
Qed.

Opaque lock_handle.
Opaque ptr_of.
Opaque lock_inv.
Opaque self_part.
Arguments ptr_of : simpl never.
Arguments lock_inv : simpl never.

Definition LockASI:funspecs := [
   (_makelock, makelock_spec);
   (_freelock, freelock_spec);
   (_acquire, acquire_spec);
   (_release, release_spec)
].

End lock_specs.
