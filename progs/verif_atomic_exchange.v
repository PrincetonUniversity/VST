Require Import veric.rmaps.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import progs.atomic_exchange.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.

Definition hist := AE_hist.

Definition AE_inv x i sh R := EX h : list AE_hist_el, EX v : val,
  !!(apply_hist i h = Some v /\ tc_val tint v) &&
  (data_at sh tint v x * ghost ([] : hist, Some h) x * R h v * (weak_precise_mpred (R h v) && emp)).

Lemma AE_inv_positive : forall x i sh R, readable_share sh -> positive_mpred (AE_inv x i sh R).
Proof.
  unfold AE_inv; intros.
  do 2 (apply ex_positive; intro).
  apply positive_andp2, positive_sepcon1, positive_sepcon1, positive_sepcon1; auto.
Qed.
Hint Resolve AE_inv_positive.

Lemma AE_inv_precise : forall x i sh R (Hsh : readable_share sh),
  predicates_hered.derives TT (weak_precise_mpred (AE_inv x i sh R)).
Proof.
  intros ????? rho _ ???
    (? & h1 & v1 & (Hh1 & ?) & ? & ? & Hj1 & (? & r1 & Hj'1 & (? & ? & ? & (? & Hv1) & Hg1) & HR1) & (HR & Hemp1))
    (? & h2 & v2 & (Hh2 & ?) & ? & ? & Hj2 & (? & r2 & Hj'2 & (? & ? & ? & (? & Hv2) & Hg2) & HR2) & (_ & Hemp2))
    Hw1 Hw2.
  unfold at_offset in *; simpl in *; rewrite data_at_rec_eq in Hv1, Hv2; simpl in *.
  exploit (mapsto_inj _ _ _ _ _ _ _ w Hsh Hv1 Hv2); auto; try join_sub; unfold unfold_reptype; simpl.
  { intro; subst; contradiction. }
  { intro; subst; contradiction. }
  intros (? & Hv); subst.
  exploit (ghost_inj _ _ _ _ _ w Hg1 Hg2); try join_sub.
  intros (? & Heq); inv Heq.
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

(* Can we always provide a clunky function such that P and Q are a single function? *)
(* Compare and contrast with magic wand proof of bin tree *)
Definition AE_spec i P R Q := forall hc hx vc vx (Hvx : apply_hist i hx = Some vx) (Hhist : hist_incl _ hc hx),
  view_shift (R hx vx * P hc vc)
  (R (hx ++ [AE vx vc]) vc * (weak_precise_mpred (R (hx ++ [AE vx vc]) vc) && emp) *
   Q (hc ++ [(length hx, AE vx vc)]) vx).

Definition AE_type := ProdType (ProdType (ProdType
  (ConstType (share * share * val * val * val * val * hist))
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

Definition ghost_hist (h : hist) p := ghost (h, @None (list AE_hist_el)) p.

(* It would be nice to be able to store any kind of data in the location, but that won't typecheck. *)
Program Definition atomic_exchange_spec := DECLARE _simulate_atomic_exchange
  TYPE AE_type WITH ish : share, lsh : share, tgt : val, l : val,
    i : val, v : val, h : hist, P : hist -> val -> mpred, R : list AE_hist_el -> val -> mpred, Q : hist -> val -> mpred
  PRE [ _tgt OF tptr tint, _l OF tptr (Tstruct _lock_t noattr), _v OF tint ]
   PROP (tc_val tint v; readable_share lsh; writable_share ish; AE_spec i P R Q)
   LOCAL (temp _tgt tgt; temp _l l; temp _v v)
   SEP (lock_inv lsh l (AE_inv tgt i ish R); ghost_hist h tgt; P h v)
  POST [ tint ]
   EX t : nat, EX v' : val,
   PROP (tc_val tint v'; Forall (fun x => fst x < t)%nat h)
   LOCAL (temp ret_temp v')
   SEP (lock_inv lsh l (AE_inv tgt i ish R); ghost_hist (h ++ [(t, AE v' v)]) tgt;
        Q (h ++ [(t, AE v' v)]) v').
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type)
    (x : share * share * val * val * val * val * hist *
         (hist -> val -> mpred) * (list AE_hist_el -> val -> mpred) * (hist -> val -> mpred)) rho =>
    PROP (let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in tc_val tint v /\ readable_share lsh /\
      writable_share ish /\ AE_spec i P R Q)
    LOCAL (let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in temp _tgt tgt;
           let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in temp _l l;
           let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in temp _v v)
    SEP (let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in
         lock_inv lsh l (AE_inv tgt i ish R) * ghost_hist h tgt * P h v) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive AE_type [fun _ => _] [fun _ => _; fun _ => _; fun _ => _]
    [fun _ => _]); repeat constructor; hnf; intros;
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto; simpl.
  - unfold AE_spec.
    (* This is probably provable for derives, but might need to be assumed for view shift. *)
    admit.
  - rewrite !approx_sepcon.
    replace (compcert_rmaps.RML.R.approx n (P h v2)) with
      (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) (P h v2)) at 1
      by (rewrite compcert_rmaps.RML.approx_oo_approx; auto).
    evar (rhs : mpred); replace (compcert_rmaps.RML.R.approx _ _) with rhs; subst rhs; [reflexivity|].
    rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
    setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
    f_equal; f_equal.
    unfold AE_inv; rewrite !approx_exp; f_equal; extensionality l'.
    rewrite !approx_exp; f_equal; extensionality z'.
    rewrite !approx_andp, !approx_sepcon; f_equal; f_equal.
    * replace (compcert_rmaps.RML.R.approx n (R l' z')) with
        (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) (R l' z')) at 2
        by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
    * rewrite !approx_andp; f_equal.
      setoid_rewrite nonexpansive_super_non_expansive at 2; [|apply precise_mpred_nonexpansive]; auto.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc; f_equal.
    f_equal; apply prop_ext; tauto.
Admitted.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type)
    (x : share * share * val * val * val * val * hist *
         (hist -> val -> mpred) * (list AE_hist_el -> val -> mpred) * (hist -> val -> mpred)) rho =>
    EX t : nat, EX v' : val,
      PROP (let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in
            tc_val tint v' /\ Forall (fun x => (fst x < t)%nat) h)
      LOCAL (let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in temp ret_temp v')
      SEP (let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in
           lock_inv lsh l (AE_inv tgt i ish R) * ghost_hist (h ++ [(t, AE v' v)]) tgt *
           Q (h ++ [(t, AE v' v)]) v') rho).
  repeat intro.
  rewrite !approx_exp; f_equal; extensionality t.
  rewrite !approx_exp; f_equal; extensionality v'.
  pose proof (PROP_LOCAL_SEP_super_non_expansive AE_type
    [fun ts x => let '(_, _, _, _, _, _, h, _, _, _) := x in tc_val tint v' /\ Forall (fun x => (fst x < t)%nat) h]
    [fun ts x => let '(_, _, _, _, _, _, _, _, _, _) := x in temp ret_temp v']
    [fun ts x => let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in
       lock_inv lsh l (AE_inv tgt i ish R) * ghost_hist (h ++ [(t, AE v' v)]) tgt *
       Q (h ++ [(t, AE v' v)]) v'])
    as Heq; apply Heq; repeat constructor; hnf; intros;
      destruct x0 as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto; simpl.
  - rewrite !approx_sepcon; f_equal.
    + rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
      f_equal.
      setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
      f_equal; f_equal.
      unfold AE_inv; rewrite !approx_exp; f_equal; extensionality l'.
      rewrite !approx_exp; f_equal; extensionality z'.
      rewrite !approx_andp, !approx_sepcon; f_equal; f_equal.
      * replace (compcert_rmaps.RML.R.approx n0 (R l' z')) with
          (base.compose (compcert_rmaps.R.approx n0) (compcert_rmaps.R.approx n0) (R l' z')) at 1
          by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
      * rewrite !approx_andp; f_equal.
        apply (nonexpansive_super_non_expansive), precise_mpred_nonexpansive.
    + replace (compcert_rmaps.RML.R.approx n0 (Q _ v')) with
        (base.compose (compcert_rmaps.R.approx n0) (compcert_rmaps.R.approx n0) (Q (h ++ [(t, AE v' v2)]) v')) at 1
        by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto.
    f_equal; extensionality.
    f_equal; extensionality.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc; f_equal.
    f_equal; apply prop_ext; tauto.
Qed.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; atomic_exchange_spec]).

Lemma body_atomic_exchange : semax_body Vprog Gprog f_simulate_atomic_exchange atomic_exchange_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as (((((((((ish, lsh), tgt), l), i), v), h), P), R), Q).
  rewrite lock_inv_isptr; Intros.
  forward_call (l, lsh, AE_inv tgt i ish R).
  unfold AE_inv at 2; Intros h' v'.
  gather_SEP 2 5; rewrite sepcon_comm.
  assert_PROP (join (h, None) ([], Some h') (h, Some h')) as Hjoin.
  { go_lowerx; apply sepcon_derives_prop.
    eapply derives_trans; [apply ghost_conflict|].
    apply prop_left; intros (? & (_ & Hh) & ([(? & ?) | (<- & _)] & Hincl)); try discriminate; simpl in *.
    apply prop_right; rewrite app_nil_r in *; repeat split; auto.
    repeat intro; apply Hincl.
    rewrite <- Hh; auto. }
  unfold ghost_hist; rewrite (ghost_join _ _ _ _ Hjoin).
  forward.
  forward.
  assert (apply_hist i (h' ++ [AE v' v]) = Some v) as Hh'.
  { rewrite apply_hist_app.
    replace (apply_hist i h') with (Some v'); simpl.
    apply eq_dec_refl. }
  apply hist_add with (e := AE v' v).
  destruct Hjoin as (? & ? & Hincl); simpl in Hincl.
  erewrite <- ghost_join; [|apply hist_sep_join].
  gather_SEP 3 5; simpl.
  match goal with H : AE_spec _ _ _ _ |- _ => apply H; auto end.
  forward_call (l, lsh, AE_inv tgt i ish R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply AE_inv_precise; auto. }
    unfold AE_inv.
    Exists (h' ++ [AE v' v]) v; entailer!.
    cancel.
    rewrite (sepcon_comm (_ * _) (ghost _ _)), !sepcon_assoc; apply sepcon_derives; auto; cancel. }
  forward.
  Exists (length h') (Vint v'); entailer!.
  - rewrite Forall_forall; intros (?, ?) Hin.
    specialize (Hincl _ _ Hin).
    simpl; rewrite <- nth_error_Some, Hincl; discriminate.
  - rewrite <- (sepcon_emp (ghost_hist _ _)).
    apply sepcon_derives; auto.
    apply andp_left2; auto.
  - intros ?? Hin.
    rewrite in_app in Hin; destruct Hin as [Hin | [X | ?]]; [| inv X | contradiction].
    + specialize (Hincl _ _ Hin); rewrite nth_error_app1; auto.
      rewrite <- nth_error_Some, Hincl; discriminate.
    + rewrite nth_error_app2, minus_diag; auto.
Qed.
