Require Import veric.rmaps.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.atomic_exchange.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.

Notation hist := (list (nat * AE_hist_el)).

Definition AE_inv x g i R := EX h : list AE_hist_el, EX v : val,
  !!(apply_hist i h = Some v /\ tc_val tint v) &&
  (data_at Tsh tint v x * ghost_ref h g * R h v * (weak_precise_mpred (R h v) && emp)).

Lemma AE_inv_positive : forall x g i R, positive_mpred (AE_inv x g i R).
Proof.
  unfold AE_inv; intros.
  do 2 (apply ex_positive; intro).
  apply positive_andp2, positive_sepcon1, positive_sepcon1, positive_sepcon1; auto.
Qed.
Hint Resolve AE_inv_positive.

Lemma AE_inv_precise : forall x g i R,
  predicates_hered.derives TT (weak_precise_mpred (AE_inv x g i R)).
Proof.
  intros ???? rho _ ???
    (? & h1 & v1 & (Hh1 & ?) & ? & ? & Hj1 & (? & r1 & Hj'1 & (? & ? & ? & (? & Hv1) & ? & Hr1 & Hg1) & HR1) & (HR & Hemp1))
    (? & h2 & v2 & (Hh2 & ?) & ? & ? & Hj2 & (? & r2 & Hj'2 & (? & ? & ? & (? & Hv2) & ? & Hr2 & Hg2) & HR2) & (_ & Hemp2))
    Hw1 Hw2.
  unfold at_offset in *; simpl in *; rewrite data_at_rec_eq in Hv1, Hv2; simpl in *.
  assert (readable_share Tsh) as Hsh by auto.
  exploit (mapsto_inj _ _ _ _ _ _ _ w Hsh Hv1 Hv2); auto; try join_sub; unfold unfold_reptype; simpl.
  { intro; subst; contradiction. }
  { intro; subst; contradiction. }
  intros (? & Hv); subst.
  exploit (ghost_inj _ _ _ _ _ w Hg1 Hg2); try join_sub.
  intros (? & Heq); inv Heq.
  pose proof (hist_list_inj _ _ _ Hr1 Hr2); subst.
  destruct (age_sepalg.join_level _ _ _ Hj1), (age_sepalg.join_level _ _ _ Hj2),
    (age_sepalg.join_level _ _ _ Hj'1), (age_sepalg.join_level _ _ _ Hj'2).
  pose proof (juicy_mem.rmap_join_sub_eq_level _ _ Hw1);
    pose proof (juicy_mem.rmap_join_sub_eq_level _ _ Hw2).
  exploit (HR w r1 r2); try (split; auto; omega); try join_sub.
  intro; subst; join_inj.
  apply sepalg.join_comm in Hj1; apply sepalg.join_comm in Hj2.
  match goal with H1 : predicates_hered.app_pred emp ?a,
    H2 : predicates_hered.app_pred emp ?b |- _ => assert (a = b);
      [eapply sepalg.same_identity; auto;
        [match goal with H : sepalg.join a ?x ?y |- _ =>
           specialize (Hemp1 _ _ H); instantiate (1 := x); subst; auto end |
         match goal with H : sepalg.join b ?x ?y |- _ =>
           specialize (Hemp2 _ _ H); subst; auto end] | subst] end.
  join_inj.
Qed.

Definition AE_loc sh l p g i R (h : hist) := lock_inv sh l (AE_inv p g i R) * ghost_hist sh h g.

Lemma AE_inv_super_non_expansive : forall n p g i R,
  compcert_rmaps.RML.R.approx n (AE_inv p g i R) =
  compcert_rmaps.RML.R.approx n (AE_inv p g i (fun h v => compcert_rmaps.RML.R.approx n (R h v))).
Proof.
  intros; unfold AE_inv.
  rewrite !approx_exp; apply f_equal; extensionality h.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_andp, !approx_sepcon, !approx_andp.
  rewrite approx_idem.
  rewrite (nonexpansive_super_non_expansive (fun R => weak_precise_mpred R))
    by (apply precise_mpred_nonexpansive); auto.
Qed.

Lemma AE_loc_super_non_expansive : forall n sh l p g i R h,
  compcert_rmaps.RML.R.approx n (AE_loc sh l p g i R h) =
  compcert_rmaps.RML.R.approx n (AE_loc sh l p g i (fun h v => compcert_rmaps.RML.R.approx n (R h v)) h).
Proof.
  intros; unfold AE_loc.
  rewrite !approx_sepcon.
  rewrite (nonexpansive_super_non_expansive (fun R => lock_inv sh l R)) by (apply nonexpansive_lock_inv).
  setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv sh l R)) at 2;
    [|apply nonexpansive_lock_inv].
  rewrite AE_inv_super_non_expansive; auto.
Qed.

(* Can we always provide a clunky function such that P and Q are a single function? *)
(* Compare and contrast with magic wand proof of bin tree *)
Definition AE_spec i P R Q := forall hc hx vc vx (Hvx : apply_hist i hx = Some vx) (Hhist : hist_incl hc hx),
  view_shift (R hx vx * P hc vc)
  (R (hx ++ [AE vx vc]) vc * (weak_precise_mpred (R (hx ++ [AE vx vc]) vc) && emp) *
   Q (hc ++ [(length hx, AE vx vc)]) vx).

Definition AE_type := ProdType (ProdType (ProdType
  (ConstType (share * val * val * val * val * val * hist))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType (list AE_hist_el)) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0,
             P at level 100, Q at level 100).

(* It would be nice to be able to store any kind of data in the location, but that won't typecheck. *)
Program Definition atomic_exchange_spec := DECLARE _simulate_atomic_exchange
  TYPE AE_type WITH lsh : share, tgt : val, g : val, l : val,
    i : val, v : val, h : hist, P : hist -> val -> mpred, R : list AE_hist_el -> val -> mpred, Q : hist -> val -> mpred
  PRE [ _tgt OF tptr tint, _l OF tptr (Tstruct _lock_t noattr), _v OF tint ]
   PROP (tc_val tint v; readable_share lsh; AE_spec i P R Q)
   LOCAL (temp _tgt tgt; temp _l l; temp _v v)
   SEP (AE_loc lsh l tgt g i R h; P h v)
  POST [ tint ]
   EX t : nat, EX v' : val,
   PROP (tc_val tint v'; Forall (fun x => fst x < t)%nat h)
   LOCAL (temp ret_temp v')
   SEP (AE_loc lsh l tgt g i R (h ++ [(t, AE v' v)]); Q (h ++ [(t, AE v' v)]) v').
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type)
    (x : share * val * val * val * val * val * hist *
         (hist -> val -> mpred) * (list AE_hist_el -> val -> mpred) * (hist -> val -> mpred)) rho =>
    PROP (let '(lsh, tgt, g, l, i, v, h, P, R, Q) := x in tc_val tint v /\ readable_share lsh /\ AE_spec i P R Q)
    LOCAL (let '(lsh, tgt, g, l, i, v, h, P, R, Q) := x in temp _tgt tgt;
           let '(lsh, tgt, g, l, i, v, h, P, R, Q) := x in temp _l l;
           let '(lsh, tgt, g, l, i, v, h, P, R, Q) := x in temp _v v)
    SEP (let '(lsh, tgt, g, l, i, v, h, P, R, Q) := x in
         AE_loc lsh l tgt g i R h * P h v) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive AE_type [fun _ => _] [fun _ => _; fun _ => _; fun _ => _]
    [fun _ => _]); repeat constructor; hnf; intros;
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto; simpl.
  - rewrite !prop_and, !approx_andp; apply f_equal; apply f_equal.
    unfold AE_spec.
    rewrite !prop_forall, !(approx_allp _ _ _ []); apply f_equal; extensionality hc.
    rewrite !prop_forall, !(approx_allp _ _ _ []); apply f_equal; extensionality hv.
    rewrite !prop_forall, !(approx_allp _ _ _ Vundef); apply f_equal; extensionality vc.
    rewrite !prop_forall, !(approx_allp _ _ _ Vundef); apply f_equal; extensionality vx.
    rewrite !prop_impl.
    setoid_rewrite approx_imp at 1.
    setoid_rewrite approx_imp at 2.
    setoid_rewrite approx_imp at 3.
    setoid_rewrite approx_imp at 4.
    rewrite view_shift_super_non_expansive.
    setoid_rewrite view_shift_super_non_expansive at 2.
    rewrite !approx_sepcon, !approx_andp.
    rewrite (nonexpansive_super_non_expansive weak_precise_mpred) by (apply precise_mpred_nonexpansive).
    apply predicates_hered.pred_ext; intros ? (? & Himp); split; auto; intros ? Ha1 (? & ?);
      split; auto; intros ? Ha2 (? & ?); split; auto;
      change prop with (@predicates_hered.prop compcert_rmaps.RML.R.rmap _) in *;
      intros ??????? X; rewrite !approx_idem in *.
    + exploit (Himp _ Ha1); [split; auto|].
      intros (? & Himp'); exploit (Himp' _ Ha2); [split; auto|].
      intros (? & Hshift).
      eapply semax_pre, Hshift, semax_pre, X; apply drop_tc_environ.
    + exploit (Himp _ Ha1); [split; auto|].
      intros (? & Himp'); exploit (Himp' _ Ha2); [split; auto|].
      intros (? & Hshift).
      eapply semax_pre, Hshift, semax_pre, X; apply drop_tc_environ.
  - rewrite !approx_sepcon, approx_idem, AE_loc_super_non_expansive; auto.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc; f_equal.
    apply f_equal; apply prop_ext; tauto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type)
    (x : share * val * val * val * val * val * hist *
         (hist -> val -> mpred) * (list AE_hist_el -> val -> mpred) * (hist -> val -> mpred)) rho =>
    EX t : nat, EX v' : val,
      PROP (let '(lsh, tgt, g, l, i, v, h, P, R, Q) := x in
            tc_val tint v' /\ Forall (fun x => (fst x < t)%nat) h)
      LOCAL (let '(lsh, tgt, g, l, i, v, h, P, R, Q) := x in temp ret_temp v')
      SEP (let '(lsh, tgt, g, l, i, v, h, P, R, Q) := x in
           AE_loc lsh l tgt g i R (h ++ [(t, AE v' v)]) * Q (h ++ [(t, AE v' v)]) v') rho).
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality t.
  rewrite !approx_exp; apply f_equal; extensionality v'.
  pose proof (PROP_LOCAL_SEP_super_non_expansive AE_type
    [fun ts x => let '(_, _, _, _, _, _, h, _, _, _) := x in tc_val tint v' /\ Forall (fun x => (fst x < t)%nat) h]
    [fun ts x => let '(_, _, _, _, _, _, _, _, _, _) := x in temp ret_temp v']
    [fun ts x => let '(lsh, tgt, g, l, i, v, h, P, R, Q) := x in
       AE_loc lsh l tgt g i R (h ++ [(t, AE v' v)]) * Q (h ++ [(t, AE v' v)]) v'])
    as Heq; apply Heq; repeat constructor; hnf; intros;
      destruct x0 as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto; simpl.
  - rewrite !approx_sepcon, approx_idem, AE_loc_super_non_expansive; auto.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto.
    apply f_equal; extensionality.
    apply f_equal; extensionality.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc; f_equal.
    apply f_equal; apply prop_ext; tauto.
Qed.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; atomic_exchange_spec]).

Lemma body_atomic_exchange : semax_body Vprog Gprog f_simulate_atomic_exchange atomic_exchange_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as (((((((((lsh, tgt), g), l), i), v), h), P), R), Q).
  unfold AE_loc; rewrite lock_inv_isptr; Intros.
  forward_call (l, lsh, AE_inv tgt g i R).
  unfold AE_inv at 2; Intros h' v'.
  assert (lsh <> Share.bot).
  { intro; subst; contradiction unreadable_bot. }
  forward.
  forward.
  assert (apply_hist i (h' ++ [AE v' v]) = Some v) as Hh'.
  { rewrite apply_hist_app.
    replace (apply_hist i h') with (Some v'); simpl.
    apply eq_dec_refl. }
  gather_SEP 5 2; assert_PROP (hist_incl h h') as Hincl.
  { go_lower; apply sepcon_derives_prop.
    rewrite hist_ref_join by auto.
    Intros hr.
    apply prop_right; eapply hist_sub_list_incl; eauto. }
  apply hist_add' with (e := AE v' v); auto.
  gather_SEP 3 5; simpl.
  match goal with H : AE_spec _ _ _ _ |- _ => apply H; auto end.
  forward_call (l, lsh, AE_inv tgt g i R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply AE_inv_precise; auto. }
    unfold AE_inv.
    Exists (h' ++ [AE v' v]) v; entailer!.
    cancel. }
  forward.
  Exists (length h') (Vint v'); unfold AE_loc; entailer!.
  - rewrite Forall_forall; intros (?, ?) Hin.
    specialize (Hincl _ _ Hin).
    simpl; rewrite <- nth_error_Some, Hincl; discriminate.
  - apply andp_left2; auto.
Qed.

Lemma AE_loc_join : forall sh1 sh2 sh l p g i R h1 h2 h (Hjoin : sepalg.join sh1 sh2 sh)
  (Hh : Permutation.Permutation (h1 ++ h2) h) (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2)
  (Hdisj : disjoint h1 h2),
  AE_loc sh1 l p g i R h1 * AE_loc sh2 l p g i R h2 = AE_loc sh l p g i R h.
Proof.
  intros; unfold AE_loc.
  match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) = _ => transitivity ((P1 * P2) * (Q1 * Q2));
    [apply mpred_ext; cancel|] end.
  erewrite lock_inv_share_join, ghost_hist_join by (eauto; intro; subst; contradiction unreadable_bot).
  rewrite prop_true_andp; auto.
Qed.
