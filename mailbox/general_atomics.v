Require Import veric.rmaps.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.

Set Bullet Behavior "Strict Subproofs".

Parameter invariant : mpred -> val -> mpred.

Axiom invariant_duplicable : forall P p, invariant P p = invariant P p * invariant P p.

Axiom invariant_precise : forall P p, precise (invariant P p).

(* I think this is sound, and follows from Iris's rules... *)
Axiom invariant_view_shift : forall {CS : compspecs} P Q R p, view_shift (P * R) (Q * R) ->
  view_shift (P * invariant R p) (Q * invariant R p).

Axiom invariant_super_non_expansive : forall n P p, compcert_rmaps.RML.R.approx n (invariant P p) =
compcert_rmaps.RML.R.approx n (invariant (compcert_rmaps.RML.R.approx n P) p).

Arguments view_shift {_} A%logic B%logic.

Section atomics.

Context {CS : compspecs}.

Axiom new_inv : forall P, view_shift (|>P) (EX p : val, invariant P p).

Corollary new_inv' : forall P, view_shift P (EX p : val, invariant P p).
Proof.
  intro; etransitivity; [apply derives_view_shift, now_later | apply new_inv].
Qed.

Corollary make_inv : forall P Q, P |-- Q -> view_shift P (EX p : val, invariant Q p).
Proof.
  intros.
  etransitivity; [apply derives_view_shift | apply new_inv']; auto.
Qed.

Definition AL_type := ProdType (ProdType (ProdType (ProdType (ProdType (ConstType val) Mpred)
  (ConstType (list val))) (ArrowType (ConstType val) Mpred))
  (ArrowType (ConstType share) (ArrowType (ConstType Z) Mpred))) (ArrowType (ConstType Z) Mpred).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6) =>
     match x with (x1,x2,x3,x4,x5,x6) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6) =>
     match x with (x1,x2,x3,x4,x5,x6) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0,
             P at level 100, Q at level 100).

(* One obvious restriction on this rule that might be needed for soundness (but maybe not for SC?) is that
   the footprint of P be empty, and vice versa for store. *)
(* For this to work with load_acquire, Q needs to be somehow future-proof: it should be okay even if v wasn't
   actually the latest value of tgt. For instance, Q might only get a history that's some prefix of the
   latest state, or only get knowledge. *)
Program Definition load_SC_spec := TYPE AL_type
  WITH p : val, P : mpred, lI : list val, II : val -> mpred, P' : share -> Z -> mpred, Q : Z -> mpred
  PRE [ 1%positive OF tptr tint ]
   PROP (view_shift (fold_right sepcon emp (map (fun p => |>II p) lI) * P)
           (EX sh : share, EX v : Z, !!(readable_share sh /\ repable_signed v) &&
              data_at sh tint (vint v) p * P' sh v);
         forall sh v, view_shift (!!(readable_share sh /\ repable_signed v) &&
           data_at sh tint (vint v) p * P' sh v) (fold_right sepcon emp (map (fun p => |>II p) lI) * Q v))
   LOCAL (temp 1%positive p)
   SEP (fold_right sepcon emp (map (fun p => invariant (II p) p) lI); P)
  POST [ tint ]
   EX v : Z,
   PROP (repable_signed v)
   LOCAL (temp ret_temp (vint v))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p) p) lI); Q v).
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : _) rho =>
    PROP (let '(p, P, lI, II, P', Q) := x in view_shift (fold_right sepcon emp (P :: map (fun p => |>II p) lI))
           (EX sh : share, EX v : Z, !!(readable_share sh /\ repable_signed v) &&
              data_at sh tint (vint v) p * P' sh v) /\
         forall sh v, view_shift (!!(readable_share sh /\ repable_signed v) &&
           data_at sh tint (vint v) p * P' sh v) (fold_right sepcon emp (Q v :: map (fun p => |>II p) lI)))
    LOCAL (let '(p, P, lI, II, P', Q) := x in temp 1%positive p)
    SEP (let '(p, P, lI, II, P', Q) := x in fold_right sepcon emp (P :: map (fun p => invariant (II p) p) lI))
    rho).
  apply (PROP_LOCAL_SEP_super_non_expansive AL_type [fun _ => _] [fun _ => _] [fun _ => _]);
    repeat constructor; hnf; intros; destruct x as (((((?, ?), ?), ?), ?), ?); auto; cbn -[fold_right].
  - rewrite !prop_and, !approx_andp; f_equal.
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon_list by discriminate; simpl.
        rewrite approx_idem; apply f_equal.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
      * rewrite !approx_exp; apply f_equal; extensionality sh.
        rewrite !approx_exp; apply f_equal; extensionality v.
        rewrite !approx_sepcon, approx_idem; auto.
    + rewrite !prop_forall, !(approx_allp _ _ _ Share.bot); apply f_equal; extensionality sh.
      rewrite !prop_forall, !(approx_allp _ _ _ 0); apply f_equal; extensionality v.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, approx_idem; auto.
      * rewrite !approx_sepcon_list by discriminate; simpl.
        rewrite approx_idem; apply f_equal.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
  - rewrite !approx_sepcon_list by discriminate; simpl.
    erewrite approx_idem, !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
  - extensionality ts x rho.
    destruct x as (((((?, ?), ?), ?), ?), Q); simpl.
    rewrite !(sepcon_comm m); unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc, !sepcon_emp; f_equal.
    rewrite and_assoc, !prop_and; apply f_equal; f_equal.
    rewrite !prop_forall; apply f_equal; extensionality sh.
    rewrite !prop_forall; apply f_equal; extensionality v'.
    rewrite (sepcon_comm (Q _)); auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : val * mpred * _ * _ * (share -> Z -> mpred) * _) rho =>
    EX v : Z,
      PROP (let '(p, P, lI, II, P', Q) := x in repable_signed v)
      LOCAL (let '(p, P, lI, II, P', Q) := x in temp ret_temp (vint v))
      SEP (let '(p, P, lI, II, P', Q) := x in
        fold_right sepcon emp (Q v :: map (fun p => invariant (II p) p) lI)) rho).
  - repeat intro.
    rewrite !approx_exp; apply f_equal; extensionality v.
    apply (PROP_LOCAL_SEP_super_non_expansive AL_type [fun _ '(p, P, lI, II, P', Q) => _]
      [fun _ '(p, P, lI, II, P', Q) => _] [fun _ '(p, P, lI, II, P', Q) => _]);
      repeat constructor; hnf; intros; destruct x0 as (((((?, ?), ?), ?), ?), ?); auto; cbn -[fold_right].
    rewrite !approx_sepcon_list by discriminate; simpl.
    erewrite approx_idem, !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
  - extensionality ts x rho.
    destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
    apply f_equal; extensionality.
    rewrite sepcon_comm; unfold SEPx; simpl; rewrite !sepcon_assoc; auto.
Qed.

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7) =>
     match x with (x1,x2,x3,x4,x5,x6,x7) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7) =>
     match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0,
             P at level 100, Q at level 100).

Definition AS_type := ProdType (ProdType (ProdType (ProdType (ProdType (ConstType (val * Z)) Mpred)
  (ConstType (list val))) (ArrowType (ConstType val) Mpred)) (ArrowType (ConstType share) Mpred))
  (Mpred).

Program Definition store_SC_spec := TYPE AS_type
  WITH p : val, v : Z, P : mpred, lI : list val, II : val -> mpred, P' : share -> mpred, Q : mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v;
         view_shift (fold_right sepcon emp (map (fun p => |>II p) lI) * P)
           (EX sh : share, !!(writable_share sh) && data_at_ sh tint p * P' sh);
         forall sh, view_shift (!!(writable_share sh) && data_at sh tint (vint v) p * P' sh)
           (fold_right sepcon emp (map (fun p => |>II p) lI) * Q))
   LOCAL (temp 1%positive p; temp 2%positive (vint v))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p) p) lI); P)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (fold_right sepcon emp (map (fun p => invariant (II p) p) lI); Q).
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : _) rho =>
    PROP (let '(p, v, P, lI, II, P', Q) := x in repable_signed v /\
         view_shift (fold_right sepcon emp (P :: map (fun p => |>II p) lI))
           (EX sh : share, !!(writable_share sh) && data_at_ sh tint p * P' sh) /\
         forall sh, view_shift (!!(writable_share sh) && data_at sh tint (vint v) p * P' sh)
           (fold_right sepcon emp (Q :: map (fun p => |>II p) lI)))
    LOCAL (let '(p, v, P, lI, II, P', Q) := x in temp 1%positive p;
           let '(p, v, P, lI, II, P', Q) := x in temp 2%positive (vint v))
    SEP (let '(p, v, P, lI, II, P', Q) := x in fold_right sepcon emp (P :: map (fun p => invariant (II p) p) lI))
    rho).
  apply (PROP_LOCAL_SEP_super_non_expansive AS_type [fun _ => _] [fun _ => _; fun _ => _] [fun _ => _]);
    repeat constructor; hnf; intros; destruct x as ((((((?, ?), ?), ?), ?), ?), ?); auto; cbn -[fold_right].
  - rewrite !prop_and, !approx_andp; apply f_equal; f_equal.
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon_list by discriminate; simpl.
        rewrite approx_idem; apply f_equal.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
      * rewrite !approx_exp; apply f_equal; extensionality sh.
        rewrite !approx_sepcon, approx_idem; auto.
    + rewrite !prop_forall, !(approx_allp _ _ _ Share.bot); apply f_equal; extensionality sh.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, approx_idem; auto.
      * rewrite !approx_sepcon_list by discriminate; simpl.
        rewrite approx_idem; apply f_equal.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
  - rewrite !approx_sepcon_list by discriminate; simpl.
    erewrite approx_idem, !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
  - extensionality ts x rho.
    destruct x as ((((((?, ?), ?), ?), ?), ?), Q); simpl.
    rewrite !(sepcon_comm m); unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc, !sepcon_emp; f_equal.
    rewrite !and_assoc, !prop_and; do 2 apply f_equal; f_equal.
    rewrite !prop_forall; apply f_equal; extensionality sh.
    rewrite (sepcon_comm Q); auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : val * Z * mpred * _ * _ * (share -> mpred) * _) rho =>
      PROP () LOCAL ()
      SEP (let '(p, v, P, lI, II, P', Q) := x in
        fold_right sepcon emp (Q :: map (fun p => invariant (II p) p) lI)) rho).
  - repeat intro.
    apply (PROP_LOCAL_SEP_super_non_expansive AS_type [] [] [fun _ '(p, v, P, lI, II, P', Q) => _]);
      repeat constructor; hnf; intros; destruct x0 as ((((((?, ?), ?), ?), ?), ?), ?); auto; cbn -[fold_right].
    rewrite !approx_sepcon_list by discriminate; simpl.
    erewrite approx_idem, !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
  - extensionality ts x rho.
    destruct x as ((((((?, ?), ?), ?), ?), ?), ?); simpl.
    rewrite sepcon_comm; unfold SEPx; simpl; rewrite !sepcon_assoc; auto.
Qed.

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0,
             P at level 100, Q at level 100).

Definition ACAS_type := ProdType (ProdType (ProdType (ProdType (ProdType (ConstType (val * Z * Z)) Mpred)
  (ConstType (list val))) (ArrowType (ConstType val) Mpred))
  (ArrowType (ConstType share) (ArrowType (ConstType Z) Mpred)))
  (ArrowType (ConstType Z) Mpred).

Program Definition CAS_SC_spec := TYPE ACAS_type
  WITH p : val, c : Z, v : Z, P : mpred, lI : list val, II : val -> mpred, P' : share -> Z -> mpred,
       Q : Z -> mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint, 3%positive OF tint ]
   PROP (repable_signed c; repable_signed v;
         view_shift (fold_right sepcon emp (map (fun p => |>II p) lI) * P)
           (EX sh : share, EX v0 : Z, !!(writable_share sh /\ repable_signed v0) &&
              data_at sh tint (vint v0) p * P' sh v0);
         forall sh v0, view_shift (!!(writable_share sh /\ repable_signed v0) &&
           data_at sh tint (vint (if eq_dec v0 c then v else v0)) p * P' sh v0)
           (fold_right sepcon emp (map (fun p => |>II p) lI) * Q v0))
   LOCAL (temp 1%positive p; temp 2%positive (vint c); temp 3%positive (vint v))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p) p) lI); P)
  POST [ tint ]
   EX v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p) p) lI); Q v').
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : _) rho =>
    PROP (let '(p, c, v, P, lI, II, P', Q) := x in repable_signed c /\ repable_signed v /\
         view_shift (fold_right sepcon emp (P :: map (fun p => |>II p) lI))
           (EX sh : share, EX v0 : Z, !!(writable_share sh /\ repable_signed v0) &&
              data_at sh tint (vint v0) p * P' sh v0) /\
         forall sh v0, view_shift (!!(writable_share sh /\ repable_signed v0) &&
           data_at sh tint (vint (if eq_dec v0 c then v else v0)) p * P' sh v0)
           (fold_right sepcon emp (Q v0 :: map (fun p => |>II p) lI)))
    LOCAL (let '(p, c, v, P, lI, II, P', Q) := x in temp 1%positive p;
           let '(p, c, v, P, lI, II, P', Q) := x in temp 2%positive (vint c);
           let '(p, c, v, P, lI, II, P', Q) := x in temp 3%positive (vint v))
    SEP (let '(p, c, v, P, lI, II, P', Q) := x in fold_right sepcon emp (P :: map (fun p => invariant (II p) p) lI))
    rho).
  apply (PROP_LOCAL_SEP_super_non_expansive ACAS_type [fun _ => _] [fun _ => _; fun _ => _; fun _ => _]
    [fun _ => _]); repeat constructor; hnf; intros; destruct x as (((((((?, ?), ?), ?), ?), ?), ?), ?); auto;
    cbn -[fold_right].
  - rewrite !prop_and, !approx_andp; do 2 apply f_equal; f_equal.
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon_list by discriminate; simpl.
        rewrite approx_idem; apply f_equal.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
      * rewrite !approx_exp; apply f_equal; extensionality sh.
        rewrite !approx_exp; apply f_equal; extensionality v0.
        rewrite !approx_sepcon, approx_idem; auto.
    + rewrite !prop_forall, !(approx_allp _ _ _ Share.bot); apply f_equal; extensionality sh.
      rewrite !prop_forall, !(approx_allp _ _ _ 0); apply f_equal; extensionality v0.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, approx_idem; auto.
      * rewrite !approx_sepcon_list by discriminate; simpl.
        rewrite approx_idem; apply f_equal.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
  - rewrite !approx_sepcon_list by discriminate; simpl.
    erewrite approx_idem, !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
  - extensionality ts x rho.
    destruct x as (((((((?, ?), ?), ?), ?), ?), ?), Q); simpl.
    rewrite !(sepcon_comm m); unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc, !sepcon_emp; f_equal.
    rewrite !and_assoc, !prop_and; do 3 apply f_equal; f_equal.
    rewrite !prop_forall; apply f_equal; extensionality sh.
    rewrite !prop_forall; apply f_equal; extensionality v0.
    rewrite (sepcon_comm (Q _)); auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : val * Z * Z * mpred * _ * _ * (share -> Z -> mpred) * _) rho =>
    EX v' : Z,
      PROP (let '(p, c, v, P, lI, II, P', Q) := x in repable_signed v')
      LOCAL (let '(p, c, v, P, lI, II, P', Q) := x in temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
      SEP (let '(p, c, v, P, lI, II, P', Q) := x in
        fold_right sepcon emp (Q v' :: map (fun p => invariant (II p) p) lI)) rho).
  - repeat intro.
    rewrite !approx_exp; apply f_equal; extensionality v.
    apply (PROP_LOCAL_SEP_super_non_expansive ACAS_type [fun _ '(p, c, v, P, lI, II, P', Q) => _]
      [fun _ '(p, c, v, P, lI, II, P', Q) => _] [fun _ '(p, c, v, P, lI, II, P', Q) => _]);
      repeat constructor; hnf; intros; destruct x0 as (((((((?, ?), ?), ?), ?), ?), ?), ?); auto; cbn -[fold_right].
    rewrite !approx_sepcon_list by discriminate; simpl.
    erewrite approx_idem, !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
  - extensionality ts x rho.
    destruct x as (((((((?, ?), ?), ?), ?), ?), ?), ?); simpl.
    apply f_equal; extensionality.
    rewrite sepcon_comm; unfold SEPx; simpl; rewrite !sepcon_assoc; auto.
Qed.

Section atomicity.

(* The logical atomicity of Iris, with TaDa's private part. *)
Definition view_shift_iff P Q := view_shift P Q /\ view_shift Q P.

(* Do we need this, or the timeless view shift in atomic_shift, for soundness? *)
Axiom ghost_timeless : forall {A} (g : A) p, view_shift (|>ghost g p) (ghost g p).

Definition atomic_shift {A B} P (a R : A -> mpred) E (b Q : A -> B -> mpred) :=
  view_shift (|>P) P /\
  view_shift_iff (fold_right sepcon emp (map later E) * P) (EX x : A, a x * R x) /\
  forall x v, view_shift (b x v * R x) (fold_right sepcon emp (map later E) * Q x v).

Definition atomic_spec_type A W T := ProdType (ProdType (ProdType (ProdType (ProdType W Mpred)
  ((ArrowType (ConstType A) (ArrowType (ConstType T) Mpred)))) (ArrowType (ConstType A) Mpred))
  (ConstType (list val))) (ArrowType (ConstType val) Mpred).

Definition super_non_expansive_a {A W} (a : forall ts : list Type, functors.MixVariantFunctor._functor
  (dependent_type_functor_rec ts W) (predicates_hered.pred compcert_rmaps.RML.R.rmap) ->
    A -> predicates_hered.pred compcert_rmaps.RML.R.rmap) :=
  forall n ts w x, compcert_rmaps.RML.R.approx n (a ts w x) =
  compcert_rmaps.RML.R.approx n (a ts (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W)
        (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) w) x).

Definition super_non_expansive_b {A B W} (b : forall ts : list Type, functors.MixVariantFunctor._functor
  (dependent_type_functor_rec ts W) (predicates_hered.pred compcert_rmaps.RML.R.rmap) ->
    A -> B -> predicates_hered.pred compcert_rmaps.RML.R.rmap) :=
  forall n ts w x y, compcert_rmaps.RML.R.approx n (b ts w x y) =
  compcert_rmaps.RML.R.approx n (b ts (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W)
        (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) w) x y).

Definition super_non_expansive_la {W} la := forall n ts w rho,
  Forall (fun l => compcert_rmaps.RML.R.approx n (!! locald_denote (l ts w) rho) =
    compcert_rmaps.RML.R.approx n (!! locald_denote (l ts
           (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W)
              (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) w)) rho)) la.

Definition super_non_expansive_lb {B W} lb := forall n ts w (v : B) rho,
  Forall (fun l => compcert_rmaps.RML.R.approx n (!! locald_denote (l ts w v) rho) =
    compcert_rmaps.RML.R.approx n (!! locald_denote (l ts
           (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W)
              (compcert_rmaps.RML.R.approx n) (compcert_rmaps.RML.R.approx n) w) v) rho)) lb.

(* A is the type of the abstract data. T is the type quantified over in the postcondition.
   W is the TypeTree of the witness for the rest of the function. *)
Program Definition atomic_spec {A T} W (a0 : A) args tz la Pp a (t : T) lb Qp b
  (Hla : super_non_expansive_la la) (HPp : super_non_expansive' Pp) (Ha : super_non_expansive_a a)
  (Hlb : super_non_expansive_lb lb) (HQp : super_non_expansive_b Qp) (Hb : super_non_expansive_b b) :=
  mk_funspec (pair args tz) cc_default (atomic_spec_type A W T)
  (fun (ts: list Type) '(w, P, Q, R, lI, II) =>
    PROP (atomic_shift P (a ts w) R (map II lI) (b ts w) Q)
    (LOCALx (map (fun l => l ts w) la)
    (SEP (Pp ts w; fold_right sepcon emp (map (fun p => invariant (II p) p) lI); P))))
  (fun (ts: list Type) '(w, P, Q, R, lI, II) => EX v : T, EX x : A,
    PROP () (LOCALx (map (fun l => l ts w v) lb)
    (SEP (Qp ts w x v; fold_right sepcon emp (map (fun p => invariant (II p) p) lI); Q x v)))) _ _.
Next Obligation.
Proof.
  replace _ with (fun (ts : list Type) (x : _ * mpred * (A -> T -> mpred) * (A -> mpred) * _ * _) rho =>
    PROP (let '(x, P, Q, R, lI, II) := x in atomic_shift P (a ts x) R (map II lI) (b ts x) Q)
    (LOCALx (map (fun Q0 => Q0 ts x) (map (fun l ts x => let '(x, P, Q, R, lI, II) := x in l ts x) la))
     SEP (let '(x, P, Q, R, lI, II) := x in
          Pp ts x * fold_right sepcon emp (map (fun p => invariant (II p) p) lI) * P)) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive (atomic_spec_type A W T) [fun _ => _]
    (map (fun l ts x => let '(x, P, Q, R, lI, II) := x in l ts x) la) [fun _ => _]);
    repeat constructor; hnf; intros; try destruct x as (((((x, P), Q), R), lI), II); auto; simpl.
  - unfold atomic_shift.
    rewrite !prop_and, !approx_andp; f_equal; [|f_equal].
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2.
      rewrite approx_idem, (nonexpansive_super_non_expansive later) by (apply later_nonexpansive); auto.
    + rewrite sepcon_comm, (sepcon_comm _ (_ _ P)).
      unfold view_shift_iff.
      rewrite !prop_and, !approx_andp; f_equal; rewrite view_shift_super_non_expansive;
        setoid_rewrite view_shift_super_non_expansive at 2.
      * setoid_rewrite (approx_sepcon_list _ (P :: _)); [|discriminate].
        setoid_rewrite (approx_sepcon_list _ (_ _ P :: _)); [|discriminate]; simpl.
        rewrite approx_idem; do 2 apply f_equal; f_equal.
        { erewrite !map_map, map_ext; eauto.
          intros; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto. }
        rewrite !approx_exp; apply f_equal; extensionality; rewrite !approx_sepcon, !approx_idem, Ha; auto.
      * setoid_rewrite (approx_sepcon_list _ (P :: _)); [|discriminate].
        setoid_rewrite (approx_sepcon_list _ (_ _ P :: _)); [|discriminate]; simpl.
        rewrite approx_idem; do 2 apply f_equal; f_equal.
        rewrite !approx_exp; apply f_equal; extensionality; rewrite !approx_sepcon, !approx_idem, Ha; auto.
        { erewrite !map_map, map_ext; eauto.
          intros; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto. }
    + rewrite !prop_forall, !approx_allp by auto.
      apply f_equal; extensionality.
      rewrite !prop_forall, !approx_allp by auto.
      apply f_equal; extensionality.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2.
      rewrite (sepcon_comm _ (Q _ _)), (sepcon_comm _ (_ _ (Q _ _))).
      setoid_rewrite (approx_sepcon_list _ (Q _ _ :: _)); [|discriminate].
      setoid_rewrite (approx_sepcon_list _ (_ _ (Q _ _) :: _)); [|discriminate]; simpl.
      erewrite !approx_sepcon, !approx_idem, Hb, !map_map, map_ext; eauto.
      intros; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
  - rewrite Forall_forall; intros ? Hin.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    intros ?? (((((x, P), Q), R), ?), ?) ?.
    specialize (Hla n ts x rho); rewrite Forall_forall in Hla; apply (Hla _ Hin).
  - rewrite !sepcon_assoc, !(approx_sepcon (Pp _ _)), HPp; apply f_equal.
    rewrite sepcon_comm, (sepcon_comm _ (_ _ P)).
    setoid_rewrite (approx_sepcon_list _ (P :: _)); [|discriminate].
    setoid_rewrite (approx_sepcon_list _ (_ _ P :: _)); [|discriminate]; simpl.
    erewrite approx_idem, !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
  - extensionality ts x rho.
    destruct x as (((((?, ?), ?), ?), ?), ?).
    unfold SEPx; simpl; rewrite map_map, !sepcon_assoc; auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (ts : list Type)
    (w : _ * mpred * (A -> T -> mpred) * (A -> mpred) * list val * (val -> mpred)) rho =>
    EX v : T, EX x : A, PROP ()
    (LOCALx (map (fun Q0 => Q0 ts w) (map (fun l ts w => let '(w, P, Q, R, lI, II) := w in l ts w v) lb))
     SEP (let '(w, P, Q, R, lI, II) := w in
          Qp ts w x v * fold_right sepcon emp (map (fun p => invariant (II p) p) lI) * Q x v)) rho).
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_exp; apply f_equal; extensionality x1.
  apply (PROP_LOCAL_SEP_super_non_expansive (atomic_spec_type A W T) []
    (map (fun l ts w => let '(w, P, Q, R, lI, II) := w in l ts w v) lb)
    [fun ts w => let '(w, P, Q, R, lI, II) := w in
       Qp ts w x1 v * fold_right sepcon emp (map (fun p => invariant (II p) p) lI) * Q x1 v]);
    repeat constructor; hnf; intros; try destruct x0 as (((((x0, P), Q), R), ?), ?); auto; simpl.
  - rewrite Forall_forall; intros ? Hin.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    intros ?? (((((x', P), Q), R), ?), ?) ?.
    specialize (Hlb n0 ts0 x' v rho0); rewrite Forall_forall in Hlb; apply (Hlb _ Hin).
  - rewrite !sepcon_assoc, !(approx_sepcon (Qp _ _ _ _)), HQp; apply f_equal.
    rewrite sepcon_comm, (sepcon_comm _ (_ _ (Q _ _))).
    setoid_rewrite (approx_sepcon_list _ (Q _ _ :: _)); [|discriminate].
    setoid_rewrite (approx_sepcon_list _ (_ _ (Q _ _) :: _)); [|discriminate]; simpl.
    erewrite approx_idem, !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
  - extensionality ts x rho.
    destruct x as (((((?, ?), ?), ?), ?), ?).
    apply f_equal; extensionality.
    apply f_equal; extensionality.
    unfold SEPx; simpl; rewrite map_map, !sepcon_assoc; auto.
Qed.

End atomicity.

End atomics.

Ltac start_atomic_function :=
  match goal with |- semax_body ?V ?G ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s;
    match goal with
    | s :=  (DECLARE _ WITH u : unit
               PRE  [] main_pre _ nil u
               POST [ tint ] main_post _ nil u) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end; unfold atomic_spec;
 let DependedTypeList := fresh "DependedTypeList" in
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>
   match Pre with 
   | (fun x => match x with (a,b) => _ end) => intros Espec DependedTypeList [a b] 
   | (fun i => _) => intros Espec DependedTypeList (((((x, P), Q), R), lI), II)
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 simplify_func_tycontext;
 repeat match goal with 
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 process_stackframe_of;
 repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;
 repeat (apply semax_extract_PROP; 
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH 
                 | Share.t => intros ?SH 
                 | _ => intro
                 end
               | |- _ => intro
               end);
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
 abbreviate_semax; simpl.
