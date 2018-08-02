Require Import VST.veric.rmaps.
Require Import VST.progs.conclib.
Require Import VST.progs.ghost.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import atomics.sim_atomics.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).

Definition surely_malloc_spec :=
 DECLARE _surely_malloc
   WITH n:Z
   PRE [ _n OF tuint ]
       PROP (0 <= n <= Int.max_unsigned)
       LOCAL (temp _n (Vint (Int.repr n)))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (malloc_token Tsh n p * memory_block Tsh n p).

(* lock invariant for atomic locations *)
Definition tatomic := Tstruct _atomic_loc noattr.

Definition A_inv p l R := EX v : Z, !!(repable_signed v) &&
  (field_at Tsh tatomic [StructField _val] (vint v) p * R v *
   (weak_precise_mpred (R v) && emp) * malloc_token Tsh (sizeof tatomic) p * malloc_token Tsh (sizeof tlock) l).

Definition atomic_loc sh p R := !!(field_compatible tatomic [] p) &&
  (EX lock : val, field_at sh tatomic [StructField _lock] lock p * lock_inv sh lock (A_inv p lock R)).

Lemma A_inv_super_non_expansive : forall n p l R,
  compcert_rmaps.RML.R.approx n (A_inv p l R) =
  compcert_rmaps.RML.R.approx n (A_inv p l (fun v => compcert_rmaps.RML.R.approx n (R v))).
Proof.
  intros; unfold A_inv.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_andp, !approx_sepcon, !approx_andp.
  rewrite approx_idem.
  rewrite (nonexpansive_super_non_expansive (fun R => weak_precise_mpred R))
    by (apply precise_mpred_nonexpansive); auto.
Qed.

Lemma atomic_loc_super_non_expansive : forall n sh p R,
  compcert_rmaps.RML.R.approx n (atomic_loc sh p R) =
  compcert_rmaps.RML.R.approx n (atomic_loc sh p (fun v => compcert_rmaps.RML.R.approx n (R v))).
Proof.
  intros; unfold atomic_loc.
  rewrite !approx_andp; apply f_equal.
  rewrite !approx_exp; apply f_equal; extensionality l.
  rewrite !approx_sepcon.
  rewrite (nonexpansive_super_non_expansive (fun R => lock_inv sh l R)) by (apply nonexpansive_lock_inv).
  setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv sh l R)) at 2;
    [|apply nonexpansive_lock_inv].
  rewrite A_inv_super_non_expansive; auto.
Qed.

Definition MA_spec i P (R : Z -> mpred) Q := view_shift P (R i * (weak_precise_mpred (R i) && emp) * Q).

Definition MA_type := ProdType (ProdType (ProdType (ConstType Z) Mpred) (ArrowType (ConstType Z) Mpred)) Mpred.

Program Definition make_atomic_spec := DECLARE _make_atomic TYPE MA_type
  WITH i : Z, P : mpred, R : Z -> mpred, Q : mpred
  PRE [ _i OF tint ]
   PROP (MA_spec i P R Q; repable_signed i)
   LOCAL (temp _i (vint i))
   SEP (P)
  POST [ tptr tatomic ]
   EX p : val,
   PROP ()
   LOCAL (temp ret_temp p)
   SEP (atomic_loc Tsh p R; Q).
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((?, ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; [rewrite ?prop_and, ?approx_andp |
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem]; auto.
  f_equal; unfold MA_spec.
  rewrite view_shift_super_non_expansive.
  setoid_rewrite view_shift_super_non_expansive at 2.
  rewrite !approx_sepcon, !approx_idem, !approx_andp.
  rewrite (nonexpansive_super_non_expansive weak_precise_mpred) by (apply precise_mpred_nonexpansive); auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((?, ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality p.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, atomic_loc_super_non_expansive; auto.
Qed.

Program Definition free_atomic_spec := DECLARE _free_atomic
  TYPE ProdType (ConstType val) (ArrowType (ConstType Z) Mpred)
  WITH p : val, R : Z -> mpred
  PRE [ _tgt OF tptr tatomic ]
   PROP ()
   LOCAL (temp _tgt p)
   SEP (atomic_loc Tsh p R)
  POST [ tint ]
   EX v : Z,
   PROP (repable_signed v)
   LOCAL (temp ret_temp (vint v))
   SEP (R v).
Next Obligation.
Proof.
  repeat intro.
  destruct x; simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal; rewrite !sepcon_emp.
  apply atomic_loc_super_non_expansive.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x; simpl.
  rewrite !approx_exp; apply f_equal; extensionality v.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp, !sepcon_emp, ?approx_idem; auto.
Qed.

Definition AL_spec P (R : Z -> mpred) Q := forall vx, repable_signed vx -> view_shift (R vx * P) (R vx * Q vx).

Definition AL_type := ProdType (ProdType (ProdType (ConstType (share * val))
  Mpred) (ArrowType (ConstType Z) Mpred)) (ArrowType (ConstType Z) Mpred).

(* One obvious restriction on this rule that might be needed for soundness (but maybe not for SC?) is that
   the footprint of P be empty, and vice versa for store. *)
(* For this to work with load_acquire, Q needs to be somehow future-proof: it should be okay even if v wasn't
   actually the latest value of tgt. For instance, Q might only get a history that's some prefix of the
   latest state. *)
Program Definition load_SC_spec := DECLARE _load_SC TYPE AL_type
  WITH sh : share, tgt : val, P : mpred, R : Z -> mpred, Q : Z -> mpred
  PRE [ _tgt OF tptr tatomic ]
   PROP (AL_spec P R Q; readable_share sh)
   LOCAL (temp _tgt tgt)
   SEP (atomic_loc sh tgt R; P)
  POST [ tint ]
   EX v : Z,
   PROP (repable_signed v)
   LOCAL (temp ret_temp (vint v))
   SEP (atomic_loc sh tgt R; Q v).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; [rewrite ?prop_and, ?approx_andp |
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, atomic_loc_super_non_expansive; auto].
  f_equal; unfold AL_spec.
  rewrite !prop_forall, !(approx_allp _ _ _ 0); apply f_equal; extensionality vx.
  rewrite !prop_impl.
  setoid_rewrite approx_imp; do 2 apply f_equal.
  rewrite view_shift_super_non_expansive, !approx_sepcon; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, atomic_loc_super_non_expansive; auto.
Qed.

Definition AS_spec v P (R : Z -> mpred) Q := forall vx, repable_signed vx ->
  view_shift (R vx * P)
  (R v * (weak_precise_mpred (R v) && emp) * Q).

Definition AS_type := ProdType (ProdType (ProdType
  (ConstType (share * val * Z)) Mpred) (ArrowType (ConstType Z) Mpred)) Mpred.

Program Definition store_SC_spec := DECLARE _store_SC
  TYPE AS_type WITH sh : share, tgt : val, v : Z, P : mpred, R : Z -> mpred, Q : mpred
  PRE [ _tgt OF tptr tatomic, _v OF tint ]
   PROP (AS_spec v P R Q; readable_share sh; repable_signed v)
   LOCAL (temp _tgt tgt; temp _v (vint v))
   SEP (atomic_loc sh tgt R; P)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (atomic_loc sh tgt R; Q).
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; [rewrite ?prop_and, ?approx_andp |
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, atomic_loc_super_non_expansive; auto].
  f_equal; unfold AS_spec.
  rewrite !prop_forall, !(approx_allp _ _ _ 0); apply f_equal; extensionality vx.
  rewrite !prop_impl.
  setoid_rewrite approx_imp; do 2 apply f_equal.
  rewrite view_shift_super_non_expansive.
  setoid_rewrite view_shift_super_non_expansive at 2.
  rewrite !approx_sepcon, !approx_andp, !approx_idem.
  rewrite (nonexpansive_super_non_expansive weak_precise_mpred) by (apply precise_mpred_nonexpansive); auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, atomic_loc_super_non_expansive; auto.
Qed.

Definition ACAS_spec c v P (R Q : Z -> mpred) := forall vx, repable_signed vx ->
  view_shift (R vx * P)
  (R (if eq_dec c vx then v else vx) * (weak_precise_mpred (R (if eq_dec c vx then v else vx)) && emp) * Q vx).

Definition ACAS_type := ProdType (ProdType (ProdType
  (ConstType (share * val * Z * Z)) Mpred)
  (ArrowType (ConstType Z) Mpred))
  (ArrowType (ConstType Z) Mpred).

Program Definition CAS_SC_spec := DECLARE _CAS_SC
  TYPE ACAS_type WITH sh : share, tgt : val, c : Z, v : Z, P : mpred, R : Z -> mpred, Q : Z -> mpred
  PRE [ _tgt OF tptr tatomic, _c OF tint, _v OF tint ]
   PROP (ACAS_spec c v P R Q; readable_share sh; repable_signed c; repable_signed v)
   LOCAL (temp _tgt tgt; temp _c (vint c); temp _v (vint v))
   SEP (atomic_loc sh tgt R; P)
  POST [ tint ]
   EX v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (if eq_dec c v' then vint 1 else vint 0))
   SEP (atomic_loc sh tgt R; Q v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((?, ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; [rewrite ?prop_and, ?approx_andp |
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, atomic_loc_super_non_expansive; auto].
  f_equal; unfold ACAS_spec.
  rewrite !prop_forall, !(approx_allp _ _ _ 0); apply f_equal; extensionality vx.
  rewrite !prop_impl.
  setoid_rewrite approx_imp.
  do 2 apply f_equal.
  rewrite view_shift_super_non_expansive.
  setoid_rewrite view_shift_super_non_expansive at 2.
  rewrite !approx_sepcon, !approx_andp, !approx_idem.
  rewrite (nonexpansive_super_non_expansive weak_precise_mpred) by (apply precise_mpred_nonexpansive); auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((?, ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality v'.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, atomic_loc_super_non_expansive; auto.
Qed.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; freelock_spec;
  surely_malloc_spec; make_atomic_spec; free_atomic_spec; load_SC_spec; store_SC_spec; CAS_SC_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call n.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh n p * memory_block Tsh n p)).
  - if_tac; entailer!.
  - forward_call tt.
    contradiction.
  - if_tac.
    + forward. subst p. discriminate.
    + Intros. forward. entailer!.
  - forward. Exists p; entailer!.
Qed.

Lemma A_inv_positive : forall x l R, positive_mpred (A_inv x l R).
Proof.
  unfold A_inv; intros.
  apply ex_positive; intro.
  apply positive_andp2; repeat apply positive_sepcon1.
  apply positive_andp2; unfold at_offset; rewrite data_at_rec_eq; simpl; auto.
Qed.
Hint Resolve A_inv_positive.

Lemma A_inv_precise : forall x l R,
  predicates_hered.derives TT (weak_precise_mpred (A_inv x l R)).
Proof.
  intros ??? rho _ ???
    (? & v1 & ? & ? & ? & Hj1 & (? & ? & Hj'1 & (? & ? & Hj''1 & (? & r1 & Hj'''1 &
      (? & Hv1) & Hr1) & HR & Hemp1) & Hma1) & Hml1)
    (? & v2 & ? & ? & ? & Hj2 & (? & ? & Hj'2 & (? & ? & Hj''2 & (? & r2 & Hj'''2 &
      (? & Hv2) & Hr2) & _ & Hemp2) & Hma2) & Hml2)
    Hw1 Hw2.
  unfold at_offset in *; simpl in *; rewrite data_at_rec_eq in Hv1, Hv2; simpl in *.
  exploit (malloc_token_precise _ _ _ w _ _ Hma1 Hma2); try join_sub; intro; subst.
  exploit (malloc_token_precise _ _ _ w _ _ Hml1 Hml2); try join_sub; intro; subst.
  assert (readable_share Tsh) as Hsh by auto.
  exploit (mapsto_inj _ _ _ _ _ _ _ w Hsh Hv1 Hv2); auto; try join_sub; unfold unfold_reptype; simpl; try discriminate.
  intros (? & ?); subst.
  assert (v1 = v2) by (apply repr_inj_signed; auto; congruence); subst.
  pose proof (juicy_mem.rmap_join_sub_eq_level _ _ Hw1);
    pose proof (juicy_mem.rmap_join_sub_eq_level _ _ Hw2).
  destruct (age_sepalg.join_level _ _ _ Hj1), (age_sepalg.join_level _ _ _ Hj2),
    (age_sepalg.join_level _ _ _ Hj'1), (age_sepalg.join_level _ _ _ Hj'2),
    (age_sepalg.join_level _ _ _ Hj''1), (age_sepalg.join_level _ _ _ Hj''2),
    (age_sepalg.join_level _ _ _ Hj'''1), (age_sepalg.join_level _ _ _ Hj'''2).
  exploit (HR w r1 r2); try (split; auto; omega); try join_sub.
  intro; subst; join_inj.
  apply sepalg.join_comm in Hj''1; apply sepalg.join_comm in Hj''2.
  match goal with H1 : predicates_hered.app_pred emp ?a,
    H2 : predicates_hered.app_pred emp ?b |- _ => assert (a = b);
      [eapply sepalg.same_identity; auto;
        [match goal with H : sepalg.join a ?x ?y |- _ =>
           specialize (Hemp1 _ _ H); instantiate (1 := x); subst; auto end |
         match goal with H : sepalg.join b ?x ?y |- _ =>
           specialize (Hemp2 _ _ H); subst; auto end] | subst] end.
  join_inj.
Qed.

Lemma body_make_atomic : semax_body Vprog Gprog f_make_atomic make_atomic_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as (((i, P), R), Q).
  forward_call (sizeof tatomic).
  { simpl; computable. }
  Intros p.
  rewrite malloc_compat; auto; Intros.
  rewrite memory_block_data_at_; auto.
  forward_call (sizeof tlock).
  { simpl; computable. }
  Intros l.
  rewrite malloc_compat; auto; Intros.
  rewrite memory_block_data_at_; auto.
  forward.
  forward.
  forward_call (l, Tsh, A_inv p l R).
  focus_SEP 4; apply H.
  forward_call (l, Tsh, A_inv p l R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply A_inv_precise; auto. }
    unfold A_inv.
    unfold_field_at 1%nat.
    Exists i; simpl; entailer!. }
  forward.
  unfold atomic_loc.
  Exists p l; entailer!.
  { exists 2; auto. }
  { exists 2; auto. }
Qed.

Lemma body_free_atomic : semax_body Vprog Gprog f_free_atomic free_atomic_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as (p, R).
  unfold atomic_loc; Intros l.
  rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (l, Tsh, A_inv p l R).
  forward_call (l, Tsh, A_inv p l R).
  { rewrite <- emp_sepcon at 1; apply sepcon_derives; [|cancel].
    apply andp_right; auto; apply andp_right.
    - eapply derives_trans, A_inv_precise; auto.
    - eapply derives_trans, positive_weak_positive, A_inv_positive; auto. }
  unfold A_inv; Intros v.
  forward_call (l, sizeof tlock).
  { rewrite data_at__memory_block; entailer!. }
  forward.
  gather_SEP 0 4.
  forward_call (p, sizeof tatomic).
  { rewrite sepcon_assoc.
    apply sepcon_derives; [|cancel].
    eapply derives_trans; [apply sepcon_derives; apply field_at_field_at_|].
    rewrite !field_at__memory_block; simpl.
    rewrite !field_compatible_field_address by (rewrite field_compatible_cons; unfold in_members; simpl; auto); simpl.
    replace 8 with (4 + 4) by omega.
    exploit field_compatible_isptr; eauto; intro.
    destruct p; try contradiction.
    rewrite <- (Int.repr_unsigned i), memory_block_split; try computable.
    simpl; entailer!.
    { match goal with H : field_compatible _ _ _ |- _ => destruct H as (? & ? & ? & ? & ? & Hsize & ?) end.
      pose proof (Int.unsigned_range i).
      simpl in Hsize; omega. } }
  forward.
  Exists v; entailer!.
  apply andp_left2; auto.
Qed.

Lemma body_load_SC : semax_body Vprog Gprog f_load_SC load_SC_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as ((((sh, tgt), P), R), Q).
  unfold atomic_loc.
  Intros l.
  rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (l, sh, A_inv tgt l R).
  unfold A_inv at 2; Intros v.
  forward.
  gather_SEP 2 7; apply H; auto.
  forward_call (l, sh, A_inv tgt l R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply A_inv_precise; auto. }
    unfold A_inv.
    Exists v; simpl; entailer!. }
  forward.
  Exists v; unfold atomic_loc; Exists l; entailer!.
Qed.

Lemma body_store_SC : semax_body Vprog Gprog f_store_SC store_SC_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as (((((sh, tgt), v), P), R), Q).
  unfold atomic_loc.
  Intros l.
  rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (l, sh, A_inv tgt l R).
  unfold A_inv at 2; Intros v'.
  forward.
  gather_SEP 2 7; apply H; auto.
  forward_call (l, sh, A_inv tgt l R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply A_inv_precise; auto. }
    unfold A_inv.
    Exists v; simpl; entailer!. }
  forward.
  unfold atomic_loc; Exists l; entailer!.
  apply andp_left2; auto.
Qed.

Lemma body_CAS_SC : semax_body Vprog Gprog f_CAS_SC CAS_SC_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as ((((((sh, tgt), c), v), P), R), Q).
  unfold atomic_loc.
  Intros l.
  rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (l, sh, A_inv tgt l R).
  unfold A_inv at 2; Intros v'.
  forward.
  focus_SEP 1.
  match goal with |- semax _ (PROP () (LOCALx (temp _x (vint v') :: ?Q)
    (SEPx (field_at Tsh tatomic ?f (vint v') tgt :: ?R)))) _ _ =>
    forward_if (PROP ( ) (LOCALx (temp _x (if eq_dec c v' then vint 1 else vint 0) :: Q)
               (SEPx (field_at Tsh tatomic f (vint (if eq_dec c v' then v else v')) tgt :: R)))) end.
  { forward.
    forward.
    subst; rewrite !eq_dec_refl; entailer!. }
  { forward.
    if_tac; [absurd (c = v'); auto|].
    entailer!. }
  gather_SEP 2 7; apply H; auto.
  forward_call (l, sh, A_inv tgt l R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply A_inv_precise; auto. }
    unfold A_inv.
    Exists (if eq_dec c v' then v else v'); entailer!.
    if_tac; auto. }
  forward.
  Exists v'; unfold atomic_loc; Exists l; entailer!.
  apply andp_left2; auto.
Qed.

Lemma atomic_loc_isptr : forall sh p R, atomic_loc sh p R = !!isptr p && atomic_loc sh p R.
Proof.
  intros; eapply local_facts_isptr with (P := fun p => atomic_loc sh p R); eauto.
  unfold atomic_loc; entailer!.
Qed.
Hint Resolve atomic_loc_isptr : saturate_local.

Lemma atomic_loc_precise : forall sh p R, readable_share sh -> precise (atomic_loc sh p R).
Proof.
  intros; unfold atomic_loc.
  intros ??? (? & l1 & r1 & r1' & ? & (? & Hl1) & ?) (? & l2 & r2 & r2' & ? & (? & Hl2) & ?) ??.
  unfold at_offset in *.
  rewrite data_at_rec_eq in Hl1, Hl2; simpl in *.
  unfold unfold_reptype in *; simpl in *.
  rewrite lock_inv_isptr in *; repeat match goal with H : predicates_hered.app_pred (!!_ && _) _ |- _ =>
    destruct H end.
  exploit (mapsto_inj sh (tptr (Tstruct sim_atomics._lock_t noattr)) l1 l2 (offset_val 4 p) r1 r2 w);
    auto; try join_sub.
  { intro; subst; contradiction. }
  { intro; subst; contradiction. }
  intros (? & ?); subst.
  assert (r1' = r2').
  { eapply lock_inv_precise; eauto; join_sub. }
  subst; join_inj.
Qed.

Lemma atomic_loc_join : forall sh1 sh2 sh p R (Hjoin : sepalg.join sh1 sh2 sh)
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2),
  atomic_loc sh1 p R * atomic_loc sh2 p R = atomic_loc sh p R.
Proof.
  intros; unfold atomic_loc.
  rewrite sepcon_andp_prop', sepcon_andp_prop.
  rewrite <- andp_assoc, andp_dup.
  apply f_equal.
  apply mpred_ext.
  - Intros l1 l2.
    match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) |-- _ =>
      apply derives_trans with (Q := (Q1 * Q2) * (P1 * P2)); [cancel|] end.
    rewrite (lock_inv_isptr sh1), (lock_inv_isptr sh2); Intros.
    unfold field_at, at_offset; Intros.
    rewrite !data_at_rec_eq; unfold unfold_reptype; simpl.
    rewrite sepcon_comm.
    assert_PROP (l1 = l2) by (apply sepcon_derives_prop, mapsto_value_eq; auto; intro; subst; contradiction).
    Exists l1; subst.
    erewrite mapsto_share_join, lock_inv_share_join; eauto; entailer!.
  - Intros l; Exists l l.
    erewrite <- field_at_share_join, <- (lock_inv_share_join sh1 sh2); eauto; cancel.
Qed.

(* Now, we can specialize these to the history PCM. *)
Inductive hist_el := Load (v : val) | Store (v : val) | CAS (r : val) (c : val) (w : val).

Instance EqDec_hist_el : EqDec hist_el.
Proof.
  unfold EqDec; decide equality; apply EqDec_val.
Qed.

Fixpoint apply_hist a h :=
  match h with
  | [] => Some a
  | Load v :: h' => if eq_dec v a then apply_hist a h' else None
  | Store v :: h' => apply_hist v h'
  | CAS r c w :: h' => if eq_dec r a then if eq_dec c a then apply_hist w h' else apply_hist a h' else None
  end.

Notation hist := (list (nat * hist_el)).

Lemma apply_hist_app : forall h1 i h2, apply_hist i (h1 ++ h2) =
  match apply_hist i h1 with Some v => apply_hist v h2 | None => None end.
Proof.
  induction h1; auto; simpl; intros.
  destruct a; auto.
  - destruct (eq_dec v i); auto.
  - destruct (eq_dec r i); auto.
    destruct (eq_dec c i); auto.
Qed.

Definition writes e v :=
  match e with
  | Load _ => False
  | Store v' => v' = v
  | CAS r c v' => r = c /\ v' = v
  end.

Lemma change_implies_write : forall v h i, apply_hist i h = Some v -> v <> i ->
  exists e, In e h /\ writes e v.
Proof.
  induction h; simpl; intros.
  - inv H; contradiction.
  - destruct a.
    + destruct (eq_dec v0 i); [|discriminate].
      exploit IHh; eauto; intros (? & ? & ?); eauto.
    + destruct (eq_dec v v0).
      * subst; do 2 eexists; eauto; simpl; auto.
      * exploit IHh; eauto; intros (? & ? & ?); eauto.
    + destruct (eq_dec r i); [|discriminate].
      destruct (eq_dec c i).
      * destruct (eq_dec v w); [subst; do 2 eexists; eauto; simpl; auto|].
        exploit IHh; eauto; intros (? & ? & ?); eauto.
      * exploit IHh; eauto; intros (? & ? & ?); eauto.
Qed.

Definition value_of e :=
  match e with
  | Load v => v
  | Store v => v
  | CAS r c w => if eq_dec r c then w else r
  end.

Lemma apply_one_value : forall i a v, apply_hist i [a] = Some v -> value_of a = v.
Proof.
  destruct a; simpl; intros.
  - destruct (eq_dec v i); inv H; auto.
  - inv H; auto.
  - destruct (eq_dec r i); [|discriminate].
    destruct (eq_dec c i); inv H.
    + rewrite eq_dec_refl; auto.
    + destruct (eq_dec v c); auto; contradiction n; auto.
Qed.

Definition last_value (h : hist) v :=
  (* initial condition *)
  (h = [] /\ v = vint 0) \/
  exists n e, In (n, e) h /\ value_of e = v /\ Forall (fun x => let '(m, _) := x in m <= n)%nat h.

Lemma last_value_new : forall h n e, newer h n ->
  last_value (h ++ [(n, e)]) (value_of e).
Proof.
  right.
  do 3 eexists; [rewrite in_app; simpl; eauto|].
  rewrite Forall_app; repeat constructor.
  eapply Forall_impl; [|eauto]; intros.
  destruct a; simpl in *; omega.
Qed.

Definition value_of_hist (h : hist) := value_of (snd (last h (O, Store (vint 0)))).

Lemma value_of_hist_snoc : forall h t e, value_of_hist (h ++ [(t, e)]) = value_of e.
Proof.
  intros; unfold value_of_hist; rewrite last_snoc; auto.
Qed.

Notation ordered_hist := (ordered_hist (Store (vint 0))).

Lemma ordered_last_value : forall h v (Hordered : ordered_hist h), last_value h v <-> value_of_hist h = v.
Proof.
  unfold last_value, value_of_hist; split; intro.
  - destruct H as [(? & ?) | (? & ? & ? & ? & ?)]; subst; auto.
    erewrite ordered_last; eauto; auto.
  - destruct h; [auto | right].
    destruct (last (p :: h) (O, Store (vint 0))) as (t, e) eqn: Hlast.
    exploit (@app_removelast_last _ (p :: h)); [discriminate | intro Heq].
    rewrite Hlast in Heq.
    exists t; exists e; repeat split; auto.
    + rewrite Heq, in_app; simpl; auto.
    + unfold ordered_hist in Hordered.
      rewrite Forall_forall; intros (?, ?) Hin.
      apply In_Znth with (d := (O, Store (vint 0))) in Hin.
      destruct Hin as (i & ? & Hi).
      rewrite <- Znth_last in Hlast.
      destruct (eq_dec i (Zlength (p :: h) - 1)).
      * subst; rewrite Hlast in Hi; inv Hi; auto.
      * exploit (Hordered i (Zlength (p :: h) - 1)); try omega.
        rewrite Hlast, Hi; simpl; omega.
Qed.

Lemma hist_list_value : forall h l v (Horder : ordered_hist h) (Hl : hist_list h l)
  (Hv : apply_hist (vint 0) l = Some v), value_of_hist h = v.
Proof.
  intros.
  destruct Hl as (Hd & Hl).
  destruct (eq_dec (Zlength l) 0).
  { apply Zlength_nil_inv in e; subst; inv Hv.
    destruct h as [|(t, e)]; auto.
    specialize (Hl t e); rewrite nth_error_nil in Hl; simpl in Hl.
    destruct Hl as (Hl & _); exploit Hl; [auto | discriminate]. }
  assert (l <> []) by (intro; subst; contradiction).
  pose proof (Hl (length l - 1)%nat (last l (Store (vint 0)))) as Hlast.
  assert (length l > 0)%nat by (destruct l; [contradiction | simpl; omega]).
  erewrite nth_error_nth, nth_last in Hlast by omega.
  destruct Hlast as (_ & Hlast); exploit Hlast; eauto.
  intro Hin; unfold value_of_hist.
  rewrite app_removelast_last with (l := l)(d := Store (vint 0)), apply_hist_app in Hv by auto.
  destruct (apply_hist (vint 0) (removelast l)) eqn: Hh; [|discriminate].
  apply apply_one_value in Hv.
  assert (hist_list h l) as Hlist by (split; auto).
  pose proof (hist_list_length _ _ Hlist) as Hlen.
  erewrite <- Znth_last, ordered_hist_list; eauto; simpl; rewrite Hlen.
  rewrite Znth_last; eauto.
  { pose proof (Zlength_nonneg h); omega. }
Qed.

Definition full_hist h v := exists l, hist_list h l /\ apply_hist (vint 0) l = Some (vint v).

Definition full_hist' h v := exists l, hist_list' h l /\ apply_hist (vint 0) l = Some v.

Lemma full_hist_weak : forall h v (Hl : full_hist h v), full_hist' h (vint v).
Proof.
  intros ?? (l & ? & ?); exists l; split; auto.
  apply hist_list_weak; auto.
Qed.

Lemma full_hist'_drop : forall h h' v (Hh : full_hist' h v)
  (Hh' : incl h' h) (HNoDup : NoDup (map fst h'))
  (Hdiff : forall t e, In (t, e) h -> ~In (t, e) h' -> forall v, ~writes e v),
  full_hist' h' v.
Proof.
  intros ??? (l & Hl & Hv) ?.
  revert dependent h'; revert dependent v; revert dependent h; induction l using rev_ind; intros.
  - inv Hl; simpl in *.
    destruct h'.
    exists []; auto.
    { specialize (Hh' p); simpl in Hh'; contradiction Hh'; auto. }
    { exploit app_cons_not_nil; [symmetry; eauto | contradiction]. }
  - pose proof (hist_list'_NoDup _ _ Hl) as Hh.
    inv Hl.
    { exploit app_cons_not_nil; [symmetry; eauto | contradiction]. }
    apply app_inj_tail in H1; destruct H1; subst.
    rewrite map_app in Hh; simpl in Hh; apply NoDup_remove in Hh; rewrite <- map_app in Hh.
    rewrite apply_hist_app in Hv.
    destruct (apply_hist (vint 0) l) eqn: Hl; [|discriminate].
    destruct (in_dec (EqDec_prod _ _ _ _) (t, x) h').
    + exploit in_split; eauto; intros (h1' & h2' & ?); subst.
      rewrite map_app in HNoDup; simpl in HNoDup; apply NoDup_remove in HNoDup; rewrite <- map_app in HNoDup.
      assert (incl (h1' ++ h2') (h1 ++ h2)).
      { intros (t', e') Hin.
        specialize (Hh' (t', e')); exploit Hh'.
        { rewrite in_app in *; simpl; tauto. }
        rewrite !in_app; intros [? | [Heq | ?]]; auto; inv Heq.
        destruct HNoDup as (? & HNoDup); contradiction HNoDup.
        rewrite in_map_iff; do 2 eexists; eauto; auto. }
      exploit IHl; eauto.
      { tauto. }
      { intros t' e' ? Hin2 ??.
        eapply (Hdiff t' e'); eauto.
        { rewrite in_app in *; simpl; tauto. }
        { intro Hin; contradiction Hin2.
          rewrite in_app in *; destruct Hin as [? | [Heq | ?]]; auto; inv Heq.
          destruct Hh as (_ & Hh); contradiction Hh.
          rewrite in_map_iff; do 2 eexists; [|rewrite in_app; eauto]; auto. } }
      intros (l' & ? & Hl').
      exists (l' ++ [x]); split; [|rewrite apply_hist_app, Hl'; auto].
      econstructor; eauto.
      eapply Forall_incl; eauto.
    + eapply IHl; eauto.
      * specialize (Hdiff t x).
        rewrite in_app in Hdiff; simpl in Hdiff.
        specialize (Hdiff (or_intror (or_introl eq_refl)) n).
        destruct x; simpl in *.
        { destruct (eq_dec v1 v0); inv Hv; auto. }
        { specialize (Hdiff _ eq_refl); contradiction. }
        { destruct (eq_dec r v0); [|discriminate].
          destruct (eq_dec c v0); inv Hv; auto.
          exploit Hdiff; eauto; contradiction. }
      * intros ? Hin; specialize (Hh' _ Hin).
        rewrite in_app in *; destruct Hh' as [? | [? | ?]]; auto; subst; contradiction.
      * intros t' e' ????; eapply (Hdiff t' e'); eauto.
        rewrite in_app in *; simpl; tauto.
Qed.

Lemma full_hist'_nil : forall n l, Forall2 full_hist' (repeat [] n) l -> l = repeat (vint 0) n.
Proof.
  intros.
  assert (Zlength l = Z.of_nat n).
  { rewrite <- (mem_lemmas.Forall2_Zlength H), Zlength_repeat; auto. }
  intros; eapply list_Znth_eq'.
  { rewrite Zlength_repeat; auto. }
  intros; rewrite Znth_repeat.
  eapply Forall2_Znth with (i := j)(d2 := vint 0) in H; [|rewrite Zlength_repeat; omega].
  destruct H as (? & Hl & Hv).
  rewrite Znth_repeat in Hl; inv Hl; inv Hv; auto.
  apply app_cons_not_nil in He; contradiction.
Qed.

Corollary full_hist_nil' : forall n l (Hfull : Forall2 full_hist' (repeat [] n) (map (fun x => vint x) l))
  (Hrep : Forall repable_signed l), l = repeat 0 n.
Proof.
  intros; apply full_hist'_nil in Hfull.
  revert dependent l; induction n; destruct l; auto; try discriminate; simpl; intros.
  inv Hrep; f_equal; [|apply IHn; inv Hfull; auto].
  apply repr_inj_signed; auto; congruence.
Qed.

Corollary full_hist_nil : forall n l (Hfull : Forall2 full_hist (repeat [] n) l)
  (Hrep : Forall repable_signed l), l = repeat 0 n.
Proof.
  intros; apply full_hist_nil'; auto.
  eapply Forall2_map2, Forall2_impl', Hfull.
  intros ?? Hin ??; apply full_hist_weak; auto.
Qed.

Definition int_op e :=
  match e with
  | Load v | Store v => tc_val tint v
  | CAS r c w => tc_val tint r /\ tc_val tint c /\ tc_val tint w
  end.

Definition make_int v := match v with Vint i => Int.signed i | _ => 0 end.

Lemma make_int_spec : forall v, tc_val tint v -> vint (make_int v) = v.
Proof.
  destruct v; try contradiction; simpl.
  rewrite Int.repr_signed; auto.
Qed.

Lemma make_int_repable : forall v, repable_signed (make_int v).
Proof.
  destruct v; simpl; try (split; computable).
  apply Int.signed_range.
Qed.

Lemma int_op_value : forall e, int_op e -> tc_val tint (value_of e).
Proof.
  destruct e; auto; simpl.
  intros (? & ? & ?); destruct (eq_dec r c); auto.
Qed.

Corollary int_op_value_of_hist : forall h, Forall int_op (map snd h) -> tc_val tint (value_of_hist h).
Proof.
  intros; unfold value_of_hist.
  apply Forall_last; simpl; auto.
  rewrite Forall_map in H; eapply Forall_impl; [|eauto].
  simpl; intros; apply int_op_value; auto.
Qed.

Lemma apply_int_ops : forall v h i (Hv : apply_hist (Vint i) h = Some v)
  (Hints : Forall int_op h), tc_val tint v.
Proof.
  induction h; simpl; intros.
  - inv Hv; eauto.
  - inversion Hints as [|?? Ha]; subst.
    destruct a.
    + destruct (eq_dec v0 (Vint i)); [eapply IHh; eauto | discriminate].
    + destruct v0; try contradiction; eapply IHh; eauto.
    + destruct (eq_dec r (Vint i)); [|discriminate].
      destruct Ha as (? & ? & ?).
      destruct w; try contradiction.
      destruct (eq_dec c (Vint i)); eapply IHh; eauto.
Qed.

Definition hist_R g i R v := EX h : _, !!(apply_hist (vint i) h = Some (vint v)) && ghost_ref h g * R h v.

Definition atomic_loc_hist sh p g i R (h : hist) := atomic_loc sh p (hist_R g i R) * ghost_hist sh h g.

Lemma atomic_loc_hist_isptr : forall sh p g i R h,
  atomic_loc_hist sh p g i R h = !!(isptr p) && atomic_loc_hist sh p g i R h.
Proof.
  intros; eapply local_facts_isptr with (P := fun p => atomic_loc_hist sh p g i R h); eauto.
  unfold atomic_loc_hist; rewrite atomic_loc_isptr; entailer!.
Qed.
Hint Resolve atomic_loc_hist_isptr : saturate_local.

Lemma hist_R_precise : forall p i R v, precise (EX h : _, R h v) -> precise (hist_R p i R v).
Proof.
  intros; unfold hist_R; apply derives_precise' with
    (Q := (EX g : option (share * hist) * option hist, ghost g p) * EX h : _, R h v).
  - unfold ghost_ref; Intros h hr; Exists (@None (share * hist), Some hr) h; auto.
  - apply precise_sepcon; auto; apply ex_ghost_precise.
Qed.
Hint Resolve hist_R_precise.

Lemma atomic_loc_hist_precise : forall sh p g i R, readable_share sh ->
  precise (EX h : _, atomic_loc_hist sh p g i R h).
Proof.
  intros; unfold atomic_loc_hist.
  eapply derives_precise' with
    (Q := atomic_loc _ _ _ * EX g' : option (share * hist) * option hist, ghost g' g).
  - Intro h; Exists (Some (sh, h), @None hist); entailer!.
  - apply precise_sepcon; [apply atomic_loc_precise | apply ex_ghost_precise]; auto.
Qed.

Notation init_hist := (Some (Tsh, [] : hist), Some ([] : hist)).

(* The user must make the init_hist before calling make_atomic, so that the ghost location is known. *)
Notation MA_witness g i R :=
  (i%Z, ghost init_hist g * R%function [] i%Z, hist_R g i R, ghost_hist Tsh ([] : hist) g).
Lemma MA_hist_spec : forall g i R, precise (EX h : _, R h i) ->
  MA_spec i (ghost init_hist g * R [] i) (hist_R g i R) (ghost_hist Tsh ([] : hist) g).
Proof.
  repeat intro.
  eapply semax_pre; [|eauto].
  unfold hist_R; go_lowerx.
  Exists (@nil hist_el); entailer!.
  rewrite sepcon_comm, <- !sepcon_assoc, hist_ref_join_nil by (apply Share.nontrivial).
  unfold share; cancel.
  apply andp_right; auto.
  eapply derives_trans, precise_weak_precise, hist_R_precise; auto.
Qed.

Inductive add_events h : list hist_el -> hist -> Prop :=
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

Lemma add_events_last : forall h le h', add_events h le h' -> le <> [] ->
  value_of_hist h' = value_of (last le (Store (vint 0))).
Proof.
  intros; apply add_events_add in H.
  destruct H as (? & ? & ?); subst.
  unfold value_of_hist.
  rewrite last_app, last_map; auto.
  intro; subst; contradiction.
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

(* FCSL takes the approach that h is always empty, and the previous history is framed out and then combined
   with the new event by hist join. We can do that, but whether it's preferable might be a matter of taste. *)
Notation AL_witness sh p g i R h P Q :=
  (sh%logic, p%logic, (ghost_hist sh h g * P)%logic, hist_R g%logic i R,
   EX h' : hist, fun v => !!(add_events h [Load (vint v)] h') && ghost_hist sh h' g * Q v).
Lemma AL_hist_spec : forall sh g i R h P Q
  (HPQR : forall h' v (Hhist : hist_incl h h'), apply_hist (vint i) h' = Some (vint v) -> repable_signed v ->
    view_shift (R h' v * P) (R (h' ++ [Load (vint v)]) v * Q v)) (Hsh : sh <> Share.bot),
  AL_spec (ghost_hist sh h g * P) (hist_R g i R)
    (EX h' : hist, fun v => !!(add_events h [Load (vint v)] h') && ghost_hist sh h' g * Q v).
Proof.
  repeat intro.
  unfold hist_R.
  rewrite exp_sepcon1, extract_exists_in_SEP; Intro h'.
  erewrite !sepcon_andp_prop', extract_prop_in_SEP with (n := O); simpl; eauto; Intros.
  rewrite <- sepcon_assoc, (sepcon_comm _ (ghost_hist _ _ _)), <- sepcon_assoc.
  rewrite sepcon_assoc, flatten_sepcon_in_SEP.
  assert_PROP (hist_incl h h').
  { go_lowerx; apply sepcon_derives_prop.
    rewrite hist_ref_join by auto; Intros l.
    eapply prop_right, hist_sub_list_incl; eauto. }
  apply hist_add' with (e := Load (vint vx)); auto.
  focus_SEP 1; apply HPQR; auto.
  eapply semax_pre; [|eauto].
  unfold hist_R; go_lowerx.
  Exists (h' ++ [Load (vint vx)]) (h ++ [(length h', Load (vint vx))]); entailer!.
  split; [|apply add_events_1, hist_incl_lt; auto].
  rewrite apply_hist_app; simpl.
  replace (apply_hist (vint i) h') with (Some (vint vx)); rewrite eq_dec_refl; auto.
Qed.

Notation AS_witness sh p g i R h v P Q :=
  (sh%logic, p%logic, v%Z%logic, (ghost_hist sh h g * P)%logic, hist_R g%logic i R,
   EX h' : hist, !!(add_events h [Store (vint v)] h') && ghost_hist sh h' g * Q).
Lemma AS_hist_spec : forall sh g i R h v P Q
  (HPQR : forall h' v' (Hhist : hist_incl h h'), apply_hist (vint i) h' = Some (vint v') -> repable_signed v' ->
     view_shift (R h' v' * P) (R (h' ++ [Store (vint v)]) v * Q)) (Hsh : sh <> Share.bot)
  (Hprecise : precise (EX h : _, R h v)),
  AS_spec v (ghost_hist sh h g * P) (hist_R g i R)
    (EX h' : hist, !!(add_events h [Store (vint v)] h') && ghost_hist sh h' g * Q).
Proof.
  repeat intro.
  unfold hist_R.
  rewrite exp_sepcon1, extract_exists_in_SEP; Intro h'.
  erewrite !sepcon_andp_prop', extract_prop_in_SEP with (n := O); simpl; eauto; Intros.
  rewrite <- sepcon_assoc, (sepcon_comm _ (ghost_hist _ _ _)), <- sepcon_assoc.
  rewrite sepcon_assoc, flatten_sepcon_in_SEP.
  assert_PROP (hist_incl h h').
  { go_lowerx; apply sepcon_derives_prop.
    rewrite hist_ref_join by auto; Intros l.
    eapply prop_right, hist_sub_list_incl; eauto. }
  apply hist_add' with (e := Store (vint v)); auto.
  focus_SEP 1; apply HPQR; auto.
  eapply semax_pre; [|eauto].
  unfold hist_R; go_lowerx.
  Exists (h' ++ [Store (vint v)]) (h ++ [(length h', Store (vint v))]); entailer!.
  split; [|apply add_events_1, hist_incl_lt; auto].
  rewrite apply_hist_app; simpl.
  replace (apply_hist (vint i) h') with (Some (vint vx)); auto.
  { apply andp_right; auto.
    eapply derives_trans, precise_weak_precise, hist_R_precise; auto. }
Qed.

Notation ACAS_witness sh p g i R h c v P Q :=
  (sh%logic, p%logic, c%Z%logic, v%Z%logic, (ghost_hist sh h g * P)%logic, hist_R g%logic i R,
   fun v' => EX h' : hist, !!(add_events h [CAS (vint v') (vint c) (vint v)] h') &&
     ghost_hist sh h' g * Q v').
Lemma ACAS_hist_spec : forall sh g i R h v c P Q
  (HPQR : forall h' v' (Hhist : hist_incl h h'), apply_hist (vint i) h' = Some (vint v') -> repable_signed v' ->
    view_shift (R h' v' * P) (R (h' ++ [CAS (vint v') (vint c) (vint v)]) (if eq_dec c v' then v else v') * Q v'))
  (Hsh : sh <> Share.bot) (Hc : repable_signed c) (Hprecise : forall v, precise (EX h : _, R h v)),
  ACAS_spec c v (ghost_hist sh h g * P) (hist_R g i R)
    (fun v' => EX h' : hist, !!(add_events h [CAS (vint v') (vint c) (vint v)] h') && ghost_hist sh h' g * Q v').
Proof.
  repeat intro.
  unfold hist_R.
  rewrite exp_sepcon1, extract_exists_in_SEP; Intro h'.
  erewrite !sepcon_andp_prop', extract_prop_in_SEP with (n := O); simpl; eauto; Intros.
  rewrite <- sepcon_assoc, (sepcon_comm _ (ghost_hist _ _ _)), <- sepcon_assoc.
  rewrite sepcon_assoc, flatten_sepcon_in_SEP.
  assert_PROP (hist_incl h h').
  { go_lowerx; apply sepcon_derives_prop.
    rewrite hist_ref_join by auto; Intros l.
    eapply prop_right, hist_sub_list_incl; eauto. }
  apply hist_add' with (e := CAS (vint vx) (vint c) (vint v)); auto.
  focus_SEP 1; apply HPQR; auto.
  eapply semax_pre; [|eauto].
  unfold hist_R; go_lowerx.
  Exists (h' ++ [CAS (vint vx) (vint c) (vint v)]) (h ++ [(length h', CAS (vint vx) (vint c) (vint v))]);
    entailer!.
  split; [|apply add_events_1, hist_incl_lt; auto].
  rewrite apply_hist_app; simpl.
  replace (apply_hist (vint i) h') with (Some (vint vx)); rewrite eq_dec_refl.
  if_tac.
  - assert (c = vx) by (apply repr_inj_signed; auto; congruence).
    subst; rewrite eq_dec_refl; auto.
  - if_tac; [absurd (vint c = vint vx); subst; auto | auto].
  - apply andp_right; auto.
    eapply derives_trans, precise_weak_precise, hist_R_precise; auto.
Qed.

Lemma atomic_loc_hist_join : forall sh1 sh2 sh p g i R h1 h2 h (Hjoin : sepalg.join sh1 sh2 sh)
  (Hh : Permutation.Permutation (h1 ++ h2) h) (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2),
  atomic_loc_hist sh1 p g i R h1 * atomic_loc_hist sh2 p g i R h2 =
  !!(disjoint h1 h2) && atomic_loc_hist sh p g i R h.
Proof.
  intros; unfold atomic_loc_hist.
  assert (sh1 <> Share.bot) by (intro; subst; contradiction unreadable_bot).
  assert (sh2 <> Share.bot) by (intro; subst; contradiction unreadable_bot).
  match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) = _ =>
    transitivity ((P1 * P2) * (Q1 * Q2)); [apply mpred_ext; cancel|] end.
  erewrite ghost_hist_join, atomic_loc_join; eauto.
  rewrite sepcon_andp_prop; auto.
Qed.
