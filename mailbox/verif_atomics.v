Require Import veric.rmaps.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.atomics.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.

Inductive hist_el := Load (v : val) | Store (v : val) | CAS (r : val) (c : val) (w : val).

Fixpoint apply_hist a h :=
  match h with
  | [] => Some a
  | Load v :: h' => if eq_dec v a then apply_hist a h' else None
  | Store v :: h' => apply_hist v h'
  | CAS r c w :: h' => if eq_dec r a then if eq_dec c a then apply_hist w h' else apply_hist a h' else None
  end.

Definition hist := hist_part hist_el.

Definition ghost_hist (h : hist) p := ghost (h, @None (list hist_el)) p.

Definition A_inv x i sh R := EX h : list hist_el, EX v : val,
  !!(apply_hist i h = Some v /\ tc_val tint v) &&
  (data_at sh tint v x * ghost ([] : hist, Some h) x * R h v * (weak_precise_mpred (R h v) && emp)).

Lemma A_inv_positive : forall x i sh R, readable_share sh -> positive_mpred (A_inv x i sh R).
Proof.
  unfold A_inv; intros.
  do 2 (apply ex_positive; intro).
  apply positive_andp2, positive_sepcon1, positive_sepcon1, positive_sepcon1; auto.
Qed.
Hint Resolve A_inv_positive.

Lemma A_inv_precise : forall x i sh R (Hsh : readable_share sh),
  predicates_hered.derives TT (weak_precise_mpred (A_inv x i sh R)).
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

Definition atomic_loc lsh l x i ish R := lock_inv lsh l (A_inv x i ish R).

Lemma atomic_loc_isptr : forall sh l x i ish R,
  atomic_loc sh l x i ish R = !!isptr l && atomic_loc sh l x i ish R.
Proof.
  unfold atomic_loc; intros; apply lock_inv_isptr.
Qed.

(* Is it useful to just take the same approach? *)
Definition AL_spec i P R Q := forall hc hx vx (Hvx : apply_hist i hx = Some vx) (Hhist : hist_incl _ hc hx),
  view_shift (R hx vx * P hc)
  (R (hx ++ [Load vx]) vx * (weak_precise_mpred (R (hx ++ [Load vx]) vx) && emp) *
   Q (hc ++ [(length hx, Load vx)]) vx).

Definition AL_type := ProdType (ProdType (ProdType
  (ConstType (share * share * val * val * val * hist))
  (ArrowType (ConstType hist) Mpred))
  (ArrowType (ConstType (list hist_el)) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100).

Program Definition atomic_load_spec := DECLARE _simulate_atomic_load
  TYPE AL_type WITH ish : share, lsh : share, tgt : val, l : val,
    i : val, h : hist, P : hist -> mpred, R : list hist_el -> val -> mpred, Q : hist -> val -> mpred
  PRE [ _tgt OF tptr tint, _l OF tptr (Tstruct _lock_t noattr) ]
   PROP (readable_share lsh; readable_share ish; AL_spec i P R Q)
   LOCAL (temp _tgt tgt; temp _l l)
   SEP (atomic_loc lsh l tgt i ish R; ghost_hist h tgt; P h)
  POST [ tint ]
   EX t : nat, EX v : val,
   PROP (tc_val tint v; Forall (fun x => fst x < t)%nat h)
   LOCAL (temp ret_temp v)
   SEP (atomic_loc lsh l tgt i ish R; ghost_hist (h ++ [(t, Load v)]) tgt; Q (h ++ [(t, Load v)]) v).
Next Obligation.
Proof.
(*  replace _ with (fun (_ : list Type)
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
  - rewrite !prop_and, !approx_andp; apply f_equal; apply f_equal; apply f_equal.
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
  - rewrite !approx_sepcon, approx_idem.
    evar (rhs : mpred); replace (compcert_rmaps.RML.R.approx _ _) with rhs; subst rhs; [reflexivity|].
    rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
    setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
    apply f_equal; apply f_equal.
    unfold AE_inv; rewrite !approx_exp; apply f_equal; extensionality l'.
    rewrite !approx_exp; apply f_equal; extensionality z'.
    rewrite !approx_andp, !approx_sepcon, approx_idem; apply f_equal; f_equal.
    rewrite !approx_andp; f_equal.
    setoid_rewrite nonexpansive_super_non_expansive at 2; [|apply precise_mpred_nonexpansive]; auto.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc; f_equal.
    apply f_equal; apply prop_ext; tauto.
Qed.*) Admitted.
Next Obligation.
Proof.
(*  replace _ with (fun (_ : list Type)
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
  rewrite !approx_exp; apply f_equal; extensionality t.
  rewrite !approx_exp; apply f_equal; extensionality v'.
  pose proof (PROP_LOCAL_SEP_super_non_expansive AE_type
    [fun ts x => let '(_, _, _, _, _, _, h, _, _, _) := x in tc_val tint v' /\ Forall (fun x => (fst x < t)%nat) h]
    [fun ts x => let '(_, _, _, _, _, _, _, _, _, _) := x in temp ret_temp v']
    [fun ts x => let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in
       lock_inv lsh l (AE_inv tgt i ish R) * ghost_hist (h ++ [(t, AE v' v)]) tgt *
       Q (h ++ [(t, AE v' v)]) v'])
    as Heq; apply Heq; repeat constructor; hnf; intros;
      destruct x0 as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto; simpl.
  - rewrite !approx_sepcon, approx_idem; f_equal.
    rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
    f_equal.
    setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
    apply f_equal; apply f_equal.
    unfold AE_inv; rewrite !approx_exp; apply f_equal; extensionality l'.
    rewrite !approx_exp; apply f_equal; extensionality z'.
    rewrite !approx_andp, !approx_sepcon, approx_idem; apply f_equal; apply f_equal.
    rewrite !approx_andp; f_equal.
    apply (nonexpansive_super_non_expansive), precise_mpred_nonexpansive.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto.
    apply f_equal; extensionality.
    apply f_equal; extensionality.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc; f_equal.
    apply f_equal; apply prop_ext; tauto.
Qed.*) Admitted.

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0,
             P at level 100, Q at level 100).

Definition AS_spec i P R Q := forall hc hx vc vx (Hvx : apply_hist i hx = Some vx) (Hhist : hist_incl _ hc hx),
  view_shift (R hx vx * P hc vc)
  (R (hx ++ [Store vc]) vc * (weak_precise_mpred (R (hx ++ [Store vc]) vc) && emp) *
   Q (hc ++ [(length hx, Store vc)])).

Definition AS_type := ProdType (ProdType (ProdType
  (ConstType (share * share * val * val * val * val * hist))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType (list hist_el)) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType hist) Mpred).

Program Definition atomic_store_spec := DECLARE _simulate_atomic_store
  TYPE AS_type WITH ish : share, lsh : share, tgt : val, l : val, v : val,
    i : val, h : hist, P : hist -> val -> mpred, R : list hist_el -> val -> mpred, Q : hist -> mpred
  PRE [ _tgt OF tptr tint, _l OF tptr (Tstruct _lock_t noattr), _v OF tint ]
   PROP (tc_val tint v; readable_share lsh; writable_share ish; AS_spec i P R Q)
   LOCAL (temp _tgt tgt; temp _l l; temp _v v)
   SEP (atomic_loc lsh l tgt i ish R; ghost_hist h tgt; P h v)
  POST [ tvoid ]
   EX t : nat,
   PROP (Forall (fun x => fst x < t)%nat h)
   LOCAL ()
   SEP (atomic_loc lsh l tgt i ish R; ghost_hist (h ++ [(t, Store v)]) tgt; Q (h ++ [(t, Store v)])).
Next Obligation.
Proof.
(*  replace _ with (fun (_ : list Type)
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
  - rewrite !prop_and, !approx_andp; apply f_equal; apply f_equal; apply f_equal.
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
  - rewrite !approx_sepcon, approx_idem.
    evar (rhs : mpred); replace (compcert_rmaps.RML.R.approx _ _) with rhs; subst rhs; [reflexivity|].
    rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
    setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
    apply f_equal; apply f_equal.
    unfold AE_inv; rewrite !approx_exp; apply f_equal; extensionality l'.
    rewrite !approx_exp; apply f_equal; extensionality z'.
    rewrite !approx_andp, !approx_sepcon, approx_idem; apply f_equal; f_equal.
    rewrite !approx_andp; f_equal.
    setoid_rewrite nonexpansive_super_non_expansive at 2; [|apply precise_mpred_nonexpansive]; auto.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc; f_equal.
    apply f_equal; apply prop_ext; tauto.
Qed.*) Admitted.
Next Obligation.
Proof.
(*  replace _ with (fun (_ : list Type)
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
  rewrite !approx_exp; apply f_equal; extensionality t.
  rewrite !approx_exp; apply f_equal; extensionality v'.
  pose proof (PROP_LOCAL_SEP_super_non_expansive AE_type
    [fun ts x => let '(_, _, _, _, _, _, h, _, _, _) := x in tc_val tint v' /\ Forall (fun x => (fst x < t)%nat) h]
    [fun ts x => let '(_, _, _, _, _, _, _, _, _, _) := x in temp ret_temp v']
    [fun ts x => let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in
       lock_inv lsh l (AE_inv tgt i ish R) * ghost_hist (h ++ [(t, AE v' v)]) tgt *
       Q (h ++ [(t, AE v' v)]) v'])
    as Heq; apply Heq; repeat constructor; hnf; intros;
      destruct x0 as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto; simpl.
  - rewrite !approx_sepcon, approx_idem; f_equal.
    rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
    f_equal.
    setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
    apply f_equal; apply f_equal.
    unfold AE_inv; rewrite !approx_exp; apply f_equal; extensionality l'.
    rewrite !approx_exp; apply f_equal; extensionality z'.
    rewrite !approx_andp, !approx_sepcon, approx_idem; apply f_equal; apply f_equal.
    rewrite !approx_andp; f_equal.
    apply (nonexpansive_super_non_expansive), precise_mpred_nonexpansive.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto.
    apply f_equal; extensionality.
    apply f_equal; extensionality.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc; f_equal.
    apply f_equal; apply prop_ext; tauto.
Qed.*) Admitted.

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100).

Definition ACAS_spec i P R Q := forall hc hx vc wc vx (Hvx : apply_hist i hx = Some vx)
  (Hhist : hist_incl _ hc hx),
  view_shift (R hx vx * P hc vc wc)
  (R (hx ++ [CAS vx vc wc]) (if eq_dec vc vx then wc else vx) *
  (weak_precise_mpred (R (hx ++ [CAS vx vc wc]) (if eq_dec vc vx then wc else vx)) && emp) *
   Q (hc ++ [(length hx, CAS vx vc wc)]) vx).

Definition ACAS_type := ProdType (ProdType (ProdType
  (ConstType (share * share * val * val * val * val * val * hist))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) (ArrowType (ConstType val) Mpred))))
  (ArrowType (ConstType (list hist_el)) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)).

Program Definition atomic_CAS_spec := DECLARE _simulate_atomic_CAS
  TYPE ACAS_type WITH ish : share, lsh : share, tgt : val, l : val, c : val, v : val,
    i : val, h : hist, P : hist -> val -> val -> mpred, R : list hist_el -> val -> mpred, Q : hist -> val -> mpred
  PRE [ _tgt OF tptr tint, _l OF tptr (Tstruct _lock_t noattr), _c OF tint, _v OF tint ]
   PROP (tc_val tint v; readable_share lsh; writable_share ish; ACAS_spec i P R Q)
   LOCAL (temp _tgt tgt; temp _l l; temp _c c; temp _v v)
   SEP (atomic_loc lsh l tgt i ish R; ghost_hist h tgt; P h c v)
  POST [ tint ]
   EX t : nat, EX v' : val,
   PROP (tc_val tint v'; Forall (fun x => fst x < t)%nat h)
   LOCAL (temp ret_temp v')
   SEP (atomic_loc lsh l tgt i ish R; ghost_hist (h ++ [(t, CAS v' c v)]) tgt; Q (h ++ [(t, CAS v' c v)]) v').
Next Obligation.
Proof.
(*  replace _ with (fun (_ : list Type)
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
  - rewrite !prop_and, !approx_andp; apply f_equal; apply f_equal; apply f_equal.
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
  - rewrite !approx_sepcon, approx_idem.
    evar (rhs : mpred); replace (compcert_rmaps.RML.R.approx _ _) with rhs; subst rhs; [reflexivity|].
    rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
    setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
    apply f_equal; apply f_equal.
    unfold AE_inv; rewrite !approx_exp; apply f_equal; extensionality l'.
    rewrite !approx_exp; apply f_equal; extensionality z'.
    rewrite !approx_andp, !approx_sepcon, approx_idem; apply f_equal; f_equal.
    rewrite !approx_andp; f_equal.
    setoid_rewrite nonexpansive_super_non_expansive at 2; [|apply precise_mpred_nonexpansive]; auto.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc; f_equal.
    apply f_equal; apply prop_ext; tauto.
Qed.*) Admitted.
Next Obligation.
Proof.
(*  replace _ with (fun (_ : list Type)
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
  rewrite !approx_exp; apply f_equal; extensionality t.
  rewrite !approx_exp; apply f_equal; extensionality v'.
  pose proof (PROP_LOCAL_SEP_super_non_expansive AE_type
    [fun ts x => let '(_, _, _, _, _, _, h, _, _, _) := x in tc_val tint v' /\ Forall (fun x => (fst x < t)%nat) h]
    [fun ts x => let '(_, _, _, _, _, _, _, _, _, _) := x in temp ret_temp v']
    [fun ts x => let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in
       lock_inv lsh l (AE_inv tgt i ish R) * ghost_hist (h ++ [(t, AE v' v)]) tgt *
       Q (h ++ [(t, AE v' v)]) v'])
    as Heq; apply Heq; repeat constructor; hnf; intros;
      destruct x0 as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto; simpl.
  - rewrite !approx_sepcon, approx_idem; f_equal.
    rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
    f_equal.
    setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
    apply f_equal; apply f_equal.
    unfold AE_inv; rewrite !approx_exp; apply f_equal; extensionality l'.
    rewrite !approx_exp; apply f_equal; extensionality z'.
    rewrite !approx_andp, !approx_sepcon, approx_idem; apply f_equal; apply f_equal.
    rewrite !approx_andp; f_equal.
    apply (nonexpansive_super_non_expansive), precise_mpred_nonexpansive.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto.
    apply f_equal; extensionality.
    apply f_equal; extensionality.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc; f_equal.
    apply f_equal; apply prop_ext; tauto.
Qed.*) Admitted.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; atomic_load_spec;
  atomic_store_spec]).

Lemma apply_hist_app : forall h1 i h2, apply_hist i (h1 ++ h2) =
  match apply_hist i h1 with Some v => apply_hist v h2 | None => None end.
Proof.
  induction h1; auto; simpl; intros.
  destruct a; auto.
  - destruct (eq_dec v i); auto.
  - destruct (eq_dec r i); auto.
    destruct (eq_dec c i); auto.
Qed.

Lemma body_atomic_load : semax_body Vprog Gprog f_simulate_atomic_load atomic_load_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as ((((((((ish, lsh), tgt), l), i), h), P), R), Q).
  unfold atomic_loc; rewrite lock_inv_isptr; Intros.
  forward_call (l, lsh, A_inv tgt i ish R).
  unfold A_inv at 2; Intros h' v.
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
  assert (apply_hist i (h' ++ [Load v]) = Some v) as Hh'.
  { rewrite apply_hist_app.
    replace (apply_hist i h') with (Some v); simpl.
    apply eq_dec_refl. }
  apply hist_add with (e := Load v).
  destruct Hjoin as (? & ? & Hincl); simpl in Hincl.
  erewrite <- ghost_join; [|apply hist_sep_join].
  gather_SEP 3 5; simpl.
  match goal with H : AL_spec _ _ _ _ |- _ => apply H; auto end.
  forward_call (l, lsh, A_inv tgt i ish R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply A_inv_precise; auto. }
    unfold A_inv.
    Exists (h' ++ [Load v]) v; entailer!.
    rewrite (sepcon_comm (_ * _) (ghost _ _)), !sepcon_assoc; apply sepcon_derives; auto; cancel. }
  forward.
  Exists (length h') (Vint v); unfold atomic_loc; entailer!.
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

Lemma body_atomic_store : semax_body Vprog Gprog f_simulate_atomic_store atomic_store_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as (((((((((ish, lsh), tgt), l), v), i), h), P), R), Q).
  unfold atomic_loc; rewrite lock_inv_isptr; Intros.
  forward_call (l, lsh, A_inv tgt i ish R).
  unfold A_inv at 2; Intros h' v'.
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
  assert (apply_hist i (h' ++ [Store v]) = Some v) as Hh'.
  { rewrite apply_hist_app.
    replace (apply_hist i h') with (Some v'); auto. }
  apply hist_add with (e := Store v).
  destruct Hjoin as (? & ? & Hincl); simpl in Hincl.
  erewrite <- ghost_join; [|apply hist_sep_join].
  gather_SEP 3 5; simpl.
  match goal with H : AS_spec _ _ _ _ |- _ => apply H; auto end.
  forward_call (l, lsh, A_inv tgt i ish R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply A_inv_precise; auto. }
    unfold A_inv.
    Exists (h' ++ [Store v]) v; entailer!.
    entailer!.
    rewrite (sepcon_comm (_ * _) (ghost _ _)), !sepcon_assoc; apply sepcon_derives; auto; cancel. }
  forward.
  Exists (length h'); unfold atomic_loc; entailer!.
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

Lemma body_atomic_CAS : semax_body Vprog Gprog f_simulate_atomic_CAS atomic_CAS_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as ((((((((((ish, lsh), tgt), l), c), v), i), h), P), R), Q).
  unfold atomic_loc; rewrite lock_inv_isptr; Intros.
  forward_call (l, lsh, A_inv tgt i ish R).
  unfold A_inv at 2; Intros h' v'.
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
  forward_if (PROP ( ) LOCAL (temp _x v'; temp _tgt tgt; temp _l l; temp _c c; temp _v v)
    SEP (ghost (h, Some h') tgt; lock_inv lsh l (A_inv tgt i ish R);
         data_at ish tint (if eq_dec c v' then v else v') tgt;
         R h' v'; weak_precise_mpred (R h' v') && emp; P h c v)).
  { forward.
    entailer!.
    exploit int_eq_e; eauto; intro; subst.
    rewrite eq_dec_refl; auto. }
  { forward.
    entailer!.
    destruct (eq_dec (Vint c) (Vint v')); auto.
    exploit int_eq_false_e; eauto; [congruence | contradiction]. }
  assert (apply_hist i (h' ++ [CAS v' c v]) = Some (if eq_dec c v' then v else v')) as Hh'.
  { rewrite apply_hist_app.
    replace (apply_hist i h') with (Some v'); simpl.
    rewrite eq_dec_refl; destruct (eq_dec c v'); auto. }
  apply hist_add with (e := CAS v' c v).
  destruct Hjoin as (? & ? & Hincl); simpl in Hincl.
  erewrite <- ghost_join; [|apply hist_sep_join].
  gather_SEP 3 5; simpl.
  match goal with H : ACAS_spec _ _ _ _ |- _ => apply H; auto end.
  forward_call (l, lsh, A_inv tgt i ish R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply A_inv_precise; auto. }
    unfold A_inv.
    Exists (h' ++ [CAS v' c v]) (if eq_dec c v' then v else v'); entailer!.
    { destruct (eq_dec c v'); auto. }
    rewrite (sepcon_comm (_ * _) (ghost _ _)), !sepcon_assoc; apply sepcon_derives; auto; cancel. }
  forward.
  Exists (length h') (Vint v'); unfold atomic_loc; entailer!.
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
