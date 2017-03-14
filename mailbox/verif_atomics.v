Require Import veric.rmaps.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.sim_atomics.

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

(* ghost state setup *)
Inductive hist_el := Load (v : val) | Store (v : val) | CAS (r : val) (c : val) (w : val).

Fixpoint apply_hist a h :=
  match h with
  | [] => Some a
  | Load v :: h' => if eq_dec v a then apply_hist a h' else None
  | Store v :: h' => apply_hist v h'
  | CAS r c w :: h' => if eq_dec r a then if eq_dec c a then apply_hist w h' else apply_hist a h' else None
  end.

Notation hist := (list (nat * hist_el)).

(*Definition ghost_hist (h : hist) p := ghost (h, @None (list hist_el)) p.*)

(* lock invariant for atomic locations *)
Definition tatomic := Tstruct _atomic_loc noattr.

Definition A_inv p l i R := EX h : list hist_el, EX v : val,
  !!(apply_hist i h = Some v /\ tc_val tint v) &&
  (field_at Tsh tatomic [StructField _val] v p * ghost_ref h p * R h v *
   (weak_precise_mpred (R h v) && emp) * malloc_token Tsh (sizeof tatomic) p * malloc_token Tsh (sizeof tlock) l).

Lemma A_inv_positive : forall x l i R, positive_mpred (A_inv x l i R).
Proof.
  unfold A_inv; intros.
  do 2 (apply ex_positive; intro).
  apply positive_andp2; repeat apply positive_sepcon1.
  apply positive_andp2; unfold at_offset; rewrite data_at_rec_eq; simpl; auto.
Qed.
Hint Resolve A_inv_positive.

Lemma A_inv_precise : forall x l i R,
  predicates_hered.derives TT (weak_precise_mpred (A_inv x l i R)).
Proof.
  intros ???? rho _ ???
    (? & h1 & v1 & (Hh1 & ?) & ? & ? & Hj1 & (? & ? & Hj'1 & (? & ? & Hj''1 & (? & r1 & Hj'''1 &
      (? & ? & ? & (? & Hv1) & ? & Hr1 & Hg1) & ?) & HR & Hemp1) & Hma1) & Hml1)
    (? & h2 & v2 & (Hh2 & ?) & ? & ? & Hj2 & (? & ? & Hj'2 & (? & ? & Hj''2 & (? & r2 & Hj'''2 &
      (? & ? & ? & (? & Hv2) & ? & Hr2 & Hg2) & ?) & _ & Hemp2) & Hma2) & Hml2)
    Hw1 Hw2.
  unfold at_offset in *; simpl in *; rewrite data_at_rec_eq in Hv1, Hv2; simpl in *.
  exploit (malloc_token_precise _ _ _ w _ _ Hma1 Hma2); try join_sub; intro; subst.
  exploit (malloc_token_precise _ _ _ w _ _ Hml1 Hml2); try join_sub; intro; subst.
  assert (readable_share Tsh) as Hsh by auto.
  exploit (mapsto_inj _ _ _ _ _ _ _ w Hsh Hv1 Hv2); auto; try join_sub; unfold unfold_reptype; simpl.
  { intro; subst; contradiction. }
  { intro; subst; contradiction. }
  intros (? & Hv); subst.
  exploit (ghost_inj _ _ _ _ _ w Hg1 Hg2); try join_sub.
  intros (? & Heq); inv Heq.
  pose proof (hist_list_inj _ _ _ Hr1 Hr2); subst.
  destruct (age_sepalg.join_level _ _ _ Hj1), (age_sepalg.join_level _ _ _ Hj2),
    (age_sepalg.join_level _ _ _ Hj'1), (age_sepalg.join_level _ _ _ Hj'2),
    (age_sepalg.join_level _ _ _ Hj''1), (age_sepalg.join_level _ _ _ Hj''2),
    (age_sepalg.join_level _ _ _ Hj'''1), (age_sepalg.join_level _ _ _ Hj'''2).
  pose proof (juicy_mem.rmap_join_sub_eq_level _ _ Hw1);
    pose proof (juicy_mem.rmap_join_sub_eq_level _ _ Hw2).
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

Definition atomic_loc sh p i R (h : hist) := !!(field_compatible tatomic [] p) &&
  (EX lock : val, field_at sh tatomic [StructField _lock] lock p * lock_inv sh lock (A_inv p lock i R) *
   ghost_hist sh h p).

Lemma A_inv_super_non_expansive : forall n p l i R,
  compcert_rmaps.RML.R.approx n (A_inv p l i R) =
  compcert_rmaps.RML.R.approx n (A_inv p l i (fun h v => compcert_rmaps.RML.R.approx n (R h v))).
Proof.
  intros; unfold A_inv.
  rewrite !approx_exp; apply f_equal; extensionality h.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_andp, !approx_sepcon, !approx_andp.
  rewrite approx_idem.
  rewrite (nonexpansive_super_non_expansive (fun R => weak_precise_mpred R))
    by (apply precise_mpred_nonexpansive); auto.
Qed.

Lemma atomic_loc_super_non_expansive : forall n sh p i R h,
  compcert_rmaps.RML.R.approx n (atomic_loc sh p i R h) =
  compcert_rmaps.RML.R.approx n (atomic_loc sh p i (fun h v => compcert_rmaps.RML.R.approx n (R h v)) h).
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

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2) => match x with (x1,x2) => P%assert end)
  (fun (ts: list Type) (x: t1*t2) => match x with (x1,x2) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, P at level 100, Q at level 100).

Definition A_inv_Type := ArrowType (ConstType (list hist_el)) (ArrowType (ConstType val) Mpred).

Program Definition make_atomic_spec := DECLARE _make_atomic TYPE ProdType (ConstType Z) A_inv_Type
  WITH i : Z, R : list hist_el -> val -> mpred
  PRE [ _i OF tint ]
   PROP ()
   LOCAL (temp _i (vint i))
   SEP (R [] (vint i); weak_precise_mpred (R [] (vint i)) && emp)
  POST [ tptr tatomic ]
   EX p : val,
   PROP ()
   LOCAL (temp ret_temp p)
   SEP (atomic_loc Tsh p (vint i) R []).
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : Z * (list hist_el -> val -> mpred)) rho =>
    PROP () LOCAL (let '(i, R) := x in temp _i (vint i))
    SEP (let '(i, R) := x in R [] (vint i) * (weak_precise_mpred (R [] (vint i)) && emp)) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive (ProdType (ConstType Z) A_inv_Type) [] [fun _ => _] [fun _ => _]);
    repeat constructor; hnf; intros; destruct x as (i, R); [auto | simpl].
  - rewrite !approx_sepcon, !approx_andp.
    rewrite approx_idem, nonexpansive_super_non_expansive by (apply precise_mpred_nonexpansive); auto.
  - extensionality ts x rho.
    destruct x; unfold SEPx; simpl.
    rewrite !sepcon_emp; auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : Z * (list hist_el -> val -> mpred)) rho =>
    EX p : val, PROP () LOCAL (let '(i, R) := x in temp ret_temp p)
                SEP (let '(i, R) := x in atomic_loc Tsh p (vint i) R []) rho).
  - repeat intro.
    rewrite !approx_exp; apply f_equal; extensionality p.
    apply (PROP_LOCAL_SEP_super_non_expansive (ProdType (ConstType Z) A_inv_Type) []
      [fun ts x => let '(i, R) := x in temp ret_temp p]
      [fun ts x => let '(i, R) := x in atomic_loc Tsh p (vint i) R []]); repeat constructor; hnf; intros;
      destruct x0 as (i, R); [auto | simpl].
    apply atomic_loc_super_non_expansive.
  - extensionality ts x rho.
    destruct x; auto.
Qed.

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4) =>
     match x with (x1,x2,x3,x4) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4) =>
     match x with (x1,x2,x3,x4) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             P at level 100, Q at level 100).

Program Definition free_atomic_spec := DECLARE _free_atomic
  TYPE ProdType (ConstType (val * val * hist)) A_inv_Type
  WITH p : val, i : val, h : hist, R : list hist_el -> val -> mpred
  PRE [ _tgt OF tptr tatomic ]
   PROP ()
   LOCAL (temp _tgt p)
   SEP (atomic_loc Tsh p i R h)
  POST [ tint ]
   EX h' : list hist_el, EX v : Z,
   PROP (hist_list h h'; apply_hist i h' = Some (vint v))
   LOCAL (temp ret_temp (vint v))
   SEP (R h' (vint v)).
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : val * val * hist * (list hist_el -> val -> mpred)) rho =>
    PROP () LOCAL (let '(p, i, h, R) := x in temp _tgt p)
    SEP (let '(p, i, h, R) := x in atomic_loc Tsh p i R h) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive (ProdType (ConstType (val * val * hist)) A_inv_Type) []
    [fun _ x => let '(((p, i), h), R) := x in _] [fun _ x => let '(((p, i), h), R) := x in _]);
    repeat constructor; hnf; intros; destruct x as (((p, i), h), R); [auto|].
  - apply atomic_loc_super_non_expansive.
  - extensionality ts x rho.
    destruct x as (((?, ?), ?), ?); auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : val * val * hist * (list hist_el -> val -> mpred)) rho =>
    EX h' : list hist_el, EX v : Z, PROP (let '(p, i, h, R) := x in hist_list h h' /\ apply_hist i h' = Some (vint v))
      LOCAL (let '(p, i, h, R) := x in temp ret_temp (vint v)) SEP (let '(p, i, h, R) := x in R h' (vint v)) rho).
  - repeat intro.
    rewrite !approx_exp; apply f_equal; extensionality h'.
    rewrite !approx_exp; apply f_equal; extensionality v.
    apply (PROP_LOCAL_SEP_super_non_expansive (ProdType (ConstType (val * val * hist)) A_inv_Type)
      [fun ts x => let '(p, i, h, R) := x in _] [fun ts x => let '(p, i, h, R) := x in _]
      [fun ts x => let '(p, i, h, R) := x in _]); repeat constructor; hnf; intros;
      destruct x0 as (((p, i), h), R); auto; simpl.
    rewrite approx_idem; auto.
  - extensionality ts x rho.
    destruct x as (((?, ?), ?), ?); auto.
    do 2 (apply f_equal; extensionality).
    unfold PROPx; simpl; f_equal; f_equal.
    apply prop_ext; tauto.
Qed.

Definition AL_spec i P R Q := forall hc hx vx (Hvx : apply_hist i hx = Some vx) (Hhist : hist_incl hc hx),
  view_shift (R hx vx * P hc)
  (R (hx ++ [Load vx]) vx * (weak_precise_mpred (R (hx ++ [Load vx]) vx) && emp) *
   Q (hc ++ [(length hx, Load vx)]) vx).

Definition AL_type := ProdType (ProdType (ProdType (ConstType (share * val * val * hist))
  (ArrowType (ConstType hist) Mpred)) A_inv_Type) (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7) =>
     match x with (x1,x2,x3,x4,x5,x6,x7) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7) =>
     match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0,
             P at level 100, Q at level 100).

Program Definition load_SC_spec := DECLARE _load_SC TYPE AL_type
  WITH sh : share, tgt : val, i : val, h : hist,
    P : hist -> mpred, R : list hist_el -> val -> mpred, Q : hist -> val -> mpred
  PRE [ _tgt OF tptr tatomic ]
   PROP (readable_share sh; AL_spec i P R Q)
   LOCAL (temp _tgt tgt)
   SEP (atomic_loc sh tgt i R h; P h)
  POST [ tint ]
   EX t : nat, EX v : val,
   PROP (tc_val tint v; Forall (fun x => fst x < t)%nat h)
   LOCAL (temp ret_temp v)
   SEP (atomic_loc sh tgt i R (h ++ [(t, Load v)]); Q (h ++ [(t, Load v)]) v).
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

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0,
             P at level 100, Q at level 100).

Definition AS_spec i P R Q := forall hc hx vc vx (Hvx : apply_hist i hx = Some vx) (Hhist : hist_incl hc hx),
  view_shift (R hx vx * P hc vc)
  (R (hx ++ [Store vc]) vc * (weak_precise_mpred (R (hx ++ [Store vc]) vc) && emp) *
   Q (hc ++ [(length hx, Store vc)])).

Definition AS_type := ProdType (ProdType (ProdType
  (ConstType (share * val * val * val * hist))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType (list hist_el)) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType hist) Mpred).

Program Definition store_SC_spec := DECLARE _store_SC
  TYPE AS_type WITH sh : share, tgt : val, v : val, i : val, h : hist,
    P : hist -> val -> mpred, R : list hist_el -> val -> mpred, Q : hist -> mpred
  PRE [ _tgt OF tptr tatomic, _v OF tint ]
   PROP (tc_val tint v; readable_share sh; AS_spec i P R Q)
   LOCAL (temp _tgt tgt; temp _v v)
   SEP (atomic_loc sh tgt i R h; P h v)
  POST [ tvoid ]
   EX t : nat,
   PROP (Forall (fun x => fst x < t)%nat h)
   LOCAL ()
   SEP (atomic_loc sh tgt i R (h ++ [(t, Store v)]); Q (h ++ [(t, Store v)])).
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

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100).

Definition ACAS_spec i P R Q := forall hc hx vc wc vx (Hvx : apply_hist i hx = Some vx)
  (Hhist : hist_incl hc hx),
  view_shift (R hx vx * P hc vc wc)
  (R (hx ++ [CAS vx vc wc]) (if eq_dec vc vx then wc else vx) *
  (weak_precise_mpred (R (hx ++ [CAS vx vc wc]) (if eq_dec vc vx then wc else vx)) && emp) *
   Q (hc ++ [(length hx, CAS vx vc wc)]) vx).

Definition ACAS_type := ProdType (ProdType (ProdType
  (ConstType (share * val * val * val * val * hist))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) (ArrowType (ConstType val) Mpred))))
  (ArrowType (ConstType (list hist_el)) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)).

Program Definition CAS_SC_spec := DECLARE _CAS_SC
  TYPE ACAS_type WITH sh : share, tgt : val, c : val, v : val, i : val, h : hist,
    P : hist -> val -> val -> mpred, R : list hist_el -> val -> mpred, Q : hist -> val -> mpred
  PRE [ _tgt OF tptr tatomic, _c OF tint, _v OF tint ]
   PROP (tc_val tint v; readable_share sh; ACAS_spec i P R Q)
   LOCAL (temp _tgt tgt; temp _c c; temp _v v)
   SEP (atomic_loc sh tgt i R h; P h c v)
  POST [ tint ]
   EX t : nat, EX v' : val,
   PROP (tc_val tint v'; Forall (fun x => fst x < t)%nat h)
   LOCAL (temp ret_temp (if eq_dec c v' then vint 1 else vint 0))
   SEP (atomic_loc sh tgt i R (h ++ [(t, CAS v' c v)]); Q (h ++ [(t, CAS v' c v)]) v').
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

Lemma body_make_atomic : semax_body Vprog Gprog f_make_atomic make_atomic_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as (i, R).
  forward_call (sizeof tatomic).
  { simpl; computable. }
  Intros p.
  rewrite malloc_compat; auto; Intros.
  rewrite memory_block_data_at_; auto.
  forward_call (sizeof tlock).
  { admit. }
  { simpl; computable. }
  Intros l.
  rewrite malloc_compat; auto; Intros.
  rewrite memory_block_data_at_; auto.
  forward.
  forward.
  match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply semax_pre with (P' := PROP () (LOCALx Q (SEPx (ghost (Some (Tsh, [] : hist), Some ([] : hist)) p :: R)))) end.
  { admit. } (* allocate ghost *)
  replace_SEP 0 (ghost_hist Tsh ([] : hist) p * ghost_ref (@nil hist_el) p).
  { go_lowerx.
    pose proof Share.nontrivial.
    rewrite sepcon_emp, hist_ref_join by auto.
    Exists ([] : hist); entailer!.
    split; [apply hist_list_nil|].
    unfold hist_sub; rewrite eq_dec_refl; auto. }
  forward_call (l, Tsh, A_inv p l (vint i) R).
  forward_call (l, Tsh, A_inv p l (vint i) R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply A_inv_precise; auto. }
    unfold A_inv.
    unfold_field_at 1%nat.
    Exists (@nil hist_el) (vint i); simpl; entailer!. }
  forward.
  unfold atomic_loc.
  Exists p l; entailer!.
  { exists 2; auto. }
  { exists 2; auto. }
Admitted.

Lemma body_free_atomic : semax_body Vprog Gprog f_free_atomic free_atomic_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as (((p, i), h), R).
  unfold atomic_loc; Intros l.
  rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (l, Tsh, A_inv p l i R).
  forward_call (l, Tsh, A_inv p l i R).
  { rewrite <- emp_sepcon at 1; apply sepcon_derives; [|cancel].
    apply andp_right; auto; apply andp_right.
    - eapply derives_trans, A_inv_precise; auto.
    - eapply derives_trans, positive_weak_positive, A_inv_positive; auto. }
  unfold A_inv; Intros h' v.
  forward_call (l, sizeof tlock).
  { rewrite data_at__memory_block; entailer!. }
  forward.
  gather_SEP 0 5.
  forward_call (p, sizeof tatomic).
  { entailer!.
    rewrite 3sepcon_assoc.
    apply sepcon_derives; [|cancel].
    eapply derives_trans; [apply sepcon_derives; apply field_at_field_at_|].
    rewrite !field_at__memory_block; simpl.
    rewrite !field_compatible_field_address by auto; simpl.
    replace 8 with (4 + 4) by omega.
    exploit field_compatible_isptr; eauto; intro.
    destruct p; try contradiction.
    rewrite <- (Int.repr_unsigned i0), memory_block_split; try computable.
    simpl; entailer!.
    { match goal with H : field_compatible _ _ _ |- _ => destruct H as (? & ? & ? & ? & ? & Hsize & ?) end.
      pose proof (Int.unsigned_range i0).
      simpl in Hsize; omega. } }
  gather_SEP 0 3.
  pose proof Share.nontrivial.
  rewrite sepcon_comm, hist_ref_join by auto.
  Intros h''.
  match goal with H : hist_sub _ _ _ |- _ => unfold hist_sub in H; rewrite eq_dec_refl in H; subst end.
  forward.
  Exists h' (Int.signed v); rewrite Int.repr_signed; entailer!.
  admit. (* deallocate ghost *)
Admitted.

Lemma apply_hist_app : forall h1 i h2, apply_hist i (h1 ++ h2) =
  match apply_hist i h1 with Some v => apply_hist v h2 | None => None end.
Proof.
  induction h1; auto; simpl; intros.
  destruct a; auto.
  - destruct (eq_dec v i); auto.
  - destruct (eq_dec r i); auto.
    destruct (eq_dec c i); auto.
Qed.

Lemma body_load_SC : semax_body Vprog Gprog f_load_SC load_SC_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as ((((((sh, tgt), i), h), P), R), Q).
  unfold atomic_loc.
  Intros l.
  rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (l, sh, A_inv tgt l i R).
  unfold A_inv at 2; Intros h' v.
  assert (sh <> Share.bot).
  { intro; subst; contradiction unreadable_bot. }
  gather_SEP 2 8; rewrite sepcon_comm, hist_ref_join by auto.
  Intros hr.
  forward.
  assert (apply_hist i (h' ++ [Load v]) = Some v) as Hh'.
  { rewrite apply_hist_app.
    replace (apply_hist i h') with (Some v); simpl.
    apply eq_dec_refl. }
  match goal with H : hist_list _ _ |- _ => pose proof (hist_next _ _ H) end.
  eapply hist_add with (e := Load v); eauto.
  replace_SEP 0 (ghost_hist sh (h ++ [(length h', Load v)]) tgt * ghost_ref (h' ++ [Load v]) tgt).
  { go_lowerx; rewrite sepcon_emp, hist_ref_join by auto.
    Exists (hr ++ [(length h', Load v)]); entailer!.
    split; [apply hist_list_snoc | apply hist_sub_snoc]; auto. }
  assert (hist_incl h h') as Hincl.
  { eapply hist_sub_list_incl; eauto. }
  gather_SEP 3 8; simpl.
  match goal with H : AL_spec _ _ _ _ |- _ => apply H; auto end.
  forward_call (l, sh, A_inv tgt l i R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply A_inv_precise; auto. }
    unfold A_inv.
    Exists (h' ++ [Load v]) v; simpl; entailer!. }
  forward.
  Exists (length h') (Vint v); unfold atomic_loc; Exists l; entailer!.
  - rewrite Forall_forall; intros (?, ?) Hin.
    specialize (Hincl _ _ Hin).
    simpl; rewrite <- nth_error_Some, Hincl; discriminate.
  - apply andp_left2; auto.
Qed.

Lemma body_store_SC : semax_body Vprog Gprog f_store_SC store_SC_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as (((((((sh, tgt), v), i), h), P), R), Q).
  unfold atomic_loc.
  Intros l.
  rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (l, sh, A_inv tgt l i R).
  unfold A_inv at 2; Intros h' v'.
  assert (sh <> Share.bot).
  { intro; subst; contradiction unreadable_bot. }
  gather_SEP 2 8; rewrite sepcon_comm, hist_ref_join by auto.
  Intros hr.
  forward.
  assert (apply_hist i (h' ++ [Store v]) = Some v) as Hh'.
  { rewrite apply_hist_app.
    replace (apply_hist i h') with (Some v'); auto. }
  match goal with H : hist_list _ _ |- _ => pose proof (hist_next _ _ H) end.
  eapply hist_add with (e := Store v); eauto.
  replace_SEP 0 (ghost_hist sh (h ++ [(length h', Store v)]) tgt * ghost_ref (h' ++ [Store v]) tgt).
  { go_lowerx; rewrite sepcon_emp, hist_ref_join by auto.
    Exists (hr ++ [(length h', Store v)]); entailer!.
    split; [apply hist_list_snoc | apply hist_sub_snoc]; auto. }
  gather_SEP 3 8; simpl.
  assert (hist_incl h h') as Hincl.
  { eapply hist_sub_list_incl; eauto. }
  match goal with H : AS_spec _ _ _ _ |- _ => apply H; auto end.
  forward_call (l, sh, A_inv tgt l i R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply A_inv_precise; auto. }
    unfold A_inv.
    Exists (h' ++ [Store v]) v; simpl; entailer!.
    entailer!. }
  forward.
  Exists (length h'); unfold atomic_loc; Exists l; entailer!.
  - rewrite Forall_forall; intros (?, ?) Hin.
    specialize (Hincl _ _ Hin).
    simpl; rewrite <- nth_error_Some, Hincl; discriminate.
  - apply andp_left2; auto.
Qed.

Lemma body_CAS_SC : semax_body Vprog Gprog f_CAS_SC CAS_SC_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as ((((((((sh, tgt), c), v), i), h), P), R), Q).
  unfold atomic_loc.
  Intros l.
  rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (l, sh, A_inv tgt l i R).
  unfold A_inv at 2; Intros h' v'.
  assert (sh <> Share.bot).
  { intro; subst; contradiction unreadable_bot. }
  gather_SEP 2 8; rewrite sepcon_comm, hist_ref_join by auto.
  Intros hr.
  forward.
  focus_SEP 2.
  match goal with |- semax _ (PROP () (LOCALx (temp _x v' :: ?Q)
    (SEPx (field_at Tsh tatomic ?f v' tgt :: ?R)))) _ _ =>
    forward_if (PROP ( ) (LOCALx (temp _x (if eq_dec c v' then vint 1 else vint 0) :: Q)
               (SEPx (field_at Tsh tatomic f (if eq_dec c v' then v else v') tgt :: R)))) end.
  { forward.
    forward.
    destruct v'; try contradiction.
    destruct c; try discriminate.
    exploit typed_true_of_bool.
    { simpl in *; eauto. }
    intro X; apply int_eq_e in X; subst.
    rewrite !eq_dec_refl; entailer!. }
  { forward.
    destruct (eq_dec c v'); [subst | entailer!].
    destruct v'; try contradiction; simpl in *.
    exploit typed_false_of_bool; eauto.
    intro X; apply int_eq_false_e in X; contradiction X; auto. }
  assert (apply_hist i (h' ++ [CAS v' c v]) = Some (if eq_dec c v' then v else v')) as Hh'.
  { rewrite apply_hist_app.
    replace (apply_hist i h') with (Some v'); simpl.
    rewrite eq_dec_refl; destruct (eq_dec c v'); auto. }
  focus_SEP 1.
  match goal with H : hist_list _ _ |- _ => pose proof (hist_next _ _ H) end.
  eapply hist_add with (e := CAS v' c v); eauto.
  replace_SEP 0 (ghost_hist sh (h ++ [(length h', CAS v' c v)]) tgt * ghost_ref (h' ++ [CAS v' c v]) tgt).
  { go_lowerx; rewrite sepcon_emp, hist_ref_join by auto.
    Exists (hr ++ [(length h', CAS v' c v)]); entailer!.
    split; [apply hist_list_snoc | apply hist_sub_snoc]; auto. }
  gather_SEP 3 8; simpl.
  assert (hist_incl h h') as Hincl.
  { eapply hist_sub_list_incl; eauto. }
  match goal with H : ACAS_spec _ _ _ _ |- _ => apply H; auto end.
  forward_call (l, sh, A_inv tgt l i R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply A_inv_precise; auto. }
    unfold A_inv.
    Exists (h' ++ [CAS v' c v]) (if eq_dec c v' then v else v'); simpl; entailer!.
    { destruct (eq_dec c v'); auto. } }
  forward.
  Exists (length h') v'; unfold atomic_loc; Exists l; entailer!.
  - rewrite Forall_forall; intros (?, ?) Hin.
    specialize (Hincl _ _ Hin).
    simpl; rewrite <- nth_error_Some, Hincl; discriminate.
  - apply andp_left2; auto.
Qed.

(* Useful functions for working with atomic histories *)
Definition value_of e :=
  match e with
  | Load v => v
  | Store v => v
  | CAS r c w => if eq_dec r c then w else r
  end.

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

Lemma atomic_loc_isptr : forall sh p i R h, atomic_loc sh p i R h = !!isptr p && atomic_loc sh p i R h.
Proof.
  intros; eapply local_facts_isptr with (P := fun p => atomic_loc sh p i R h); eauto.
  unfold atomic_loc; entailer!.
Qed.