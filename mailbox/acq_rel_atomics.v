Require Import veric.rmaps.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.general_atomics.

Set Bullet Behavior "Strict Subproofs".

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
Context {state : Type} `{state_ord : PCM_order state}.
Variable (s0 : state).

(* Iris-weak gives a more in-depth encoding of protocol assertions in terms of invariants and ghost state. This
   simpler one is probably still sound and almost as powerful. *)
Definition protocol_inv T l g g' := EX v : Z, EX s : state, !!(field_compatible tint [] l /\ repable_signed v) &&
  mapsto Tsh tint l (vint v) * ghost_master s g * ghost_var gsh1 s g' * T s v.

Definition protocol_R l g g' (s : state) T := invariant (protocol_inv T l g g') * ghost_snap s g.

Definition protocol_W l g g' (s : state) T := invariant (protocol_inv T l g g') * ghost_var gsh2 s g'.

Lemma protocol_inv_super_non_expansive : forall n T l g g',
  compcert_rmaps.RML.R.approx n (protocol_inv T l g g') =
  compcert_rmaps.RML.R.approx n (protocol_inv (fun s v => compcert_rmaps.RML.R.approx n (T s v)) l g g').
Proof.
  intros; unfold protocol_inv.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_exp; apply f_equal; extensionality s.
  rewrite !approx_sepcon, !approx_andp, approx_idem; auto.
Qed.

Lemma protocol_R_super_non_expansive : forall n l g g' s T,
  compcert_rmaps.RML.R.approx n (protocol_R l g g' s T) =
  compcert_rmaps.RML.R.approx n (protocol_R l g g' s (fun s v => compcert_rmaps.RML.R.approx n (T s v))).
Proof.
  intros; unfold protocol_R.
  rewrite !approx_sepcon; f_equal.
  rewrite invariant_super_non_expansive; setoid_rewrite invariant_super_non_expansive at 2.
  rewrite protocol_inv_super_non_expansive; auto.
Qed.

Lemma protocol_W_super_non_expansive : forall n l g g' s T,
  compcert_rmaps.RML.R.approx n (protocol_W l g g' s T) =
  compcert_rmaps.RML.R.approx n (protocol_W l g g' s (fun s v => compcert_rmaps.RML.R.approx n (T s v))).
Proof.
  intros; unfold protocol_W.
  rewrite !approx_sepcon; f_equal.
  rewrite invariant_super_non_expansive; setoid_rewrite invariant_super_non_expansive at 2.
  rewrite protocol_inv_super_non_expansive; auto.
Qed.

(* Can we also open general invariants at an atomic, since they won't involve the current values of RA locations? *)

Definition duplicable P := view_shift P (P * P).

Lemma duplicable_super_non_expansive : forall n P, compcert_rmaps.RML.R.approx n (!!duplicable P) =
  compcert_rmaps.RML.R.approx n (!!duplicable (compcert_rmaps.RML.R.approx n P)).
Proof.
  intros; unfold duplicable.
  rewrite view_shift_super_non_expansive, approx_sepcon; auto.
Qed.

Definition LA_type := ProdType (ProdType (ProdType (ConstType (val * val * val * state))
  (ArrowType (ConstType state) (ArrowType (ConstType Z) Mpred))) Mpred) (ArrowType (ConstType Z) Mpred).

Program Definition load_acq_spec := TYPE LA_type
  WITH l : val, g : val, g' : val, s : state, T : state -> Z -> mpred, P : mpred, Q : Z -> mpred
  PRE [ 1%positive OF tptr tint ]
   PROP (forall s' v, ord s s' -> repable_signed v -> view_shift (P * T s' v) (Q v); forall v, duplicable (Q v))
   LOCAL (temp 1%positive l)
   SEP (protocol_R l g g' s T; P)
  POST [ tint ]
   EX v : Z, EX s' : state,
   PROP (repable_signed v; ord s s')
   LOCAL (temp ret_temp (vint v))
   SEP (protocol_R l g g' s' T; Q v).
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : _) rho =>
    PROP (let '(l, g, g', s, T, P, Q) := x in (forall s' v, ord s s' -> repable_signed v ->
      view_shift (P * T s' v) (Q v)) /\ forall v, duplicable (Q v))
    LOCAL (let '(l, g, g', s, T, P, Q) := x in temp 1%positive l)
    SEP (let '(l, g, g', s, T, P, Q) := x in protocol_R l g g' s T * P) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive LA_type [fun _ => _] [fun _ => _] [fun _ => _]);
    repeat constructor; hnf; intros; destruct x as ((((((?, ?), ?), ?), ?), ?), ?); auto; simpl.
  - rewrite !prop_and, !approx_andp; f_equal.
    + rewrite !prop_forall, !(approx_allp _ _ _ s0); f_equal; extensionality s'.
      rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
      rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
      setoid_rewrite approx_imp; do 2 apply f_equal.
      rewrite view_shift_super_non_expansive, !approx_sepcon; auto.
    + rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
      apply duplicable_super_non_expansive.
  - rewrite !approx_sepcon, protocol_R_super_non_expansive, approx_idem; auto.
  - extensionality ts x rho.
    destruct x as ((((((?, ?), ?), ?), ?), ?), Q); simpl.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc, !and_assoc; auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : _ * mpred * _) rho =>
    EX v : Z, EX s' : state,
      PROP (let '(l, g, g', s, T, P, Q) := x in repable_signed v /\ ord s s')
      LOCAL (let '(l, g, g', s, T, P, Q) := x in temp ret_temp (vint v))
      SEP (let '(l, g, g', s, T, P, Q) := x in protocol_R l g g' s' T * Q v) rho).
  - repeat intro.
    rewrite !approx_exp; apply f_equal; extensionality v.
    rewrite !approx_exp; apply f_equal; extensionality s'.
    apply (PROP_LOCAL_SEP_super_non_expansive LA_type [fun _ '(l, g, g', s, T, P, Q) => _]
      [fun _ '(l, g, g', s, T, P, Q) => _] [fun _ '(l, g, g', s, T, P, Q) => _]);
      repeat constructor; hnf; intros; destruct x0 as ((((((?, ?), ?), ?), ?), ?), ?); auto; simpl.
    rewrite !approx_sepcon, protocol_R_super_non_expansive, approx_idem; auto.
  - extensionality ts x rho.
    destruct x as ((((((?, ?), ?), ?), ?), ?), ?); simpl.
    apply f_equal; extensionality.
    apply f_equal; extensionality.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc, !and_assoc; auto.
Qed.

Definition SR_type := ProdType (ProdType (ProdType (ConstType (val * Z * val * val * state * state))
  (ArrowType (ConstType state) (ArrowType (ConstType Z) Mpred))) Mpred) Mpred.

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100).

Program Definition store_rel_spec := TYPE SR_type
  WITH l : val, v : Z, g : val, g' : val, s : state, s'' : state, T : state -> Z -> mpred, P : mpred, Q : mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v; forall v0, repable_signed v0 -> view_shift (P * T s v0) (T s'' v * Q); ord s s'')
   LOCAL (temp 1%positive l; temp 2%positive (vint v))
   SEP (protocol_W l g g' s T; P)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (protocol_W l g g' s'' T; Q).
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : _) rho =>
    PROP (let '(l, v, g, g', s, s'', T, P, Q) := x in repable_signed v /\ (forall v0, repable_signed v0 ->
      view_shift (P * T s v0) (T s'' v * Q)) /\ ord s s'')
    LOCAL (let '(l, v, g, g', s, s'', T, P, Q) := x in temp 1%positive l;
           let '(l, v, g, g', s, s'', T, P, Q) := x in temp 2%positive (vint v))
    SEP (let '(l, v, g, g', s, s'', T, P, Q) := x in protocol_W l g g' s T * P) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive SR_type [fun _ => _] [fun _ => _; fun _ => _] [fun _ => _]);
    repeat constructor; hnf; intros; destruct x as ((((((((?, ?), ?), ?), ?), ?), ?), ?), ?); auto; simpl.
  - rewrite !prop_and, !approx_andp; f_equal; f_equal.
    rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
    rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
    rewrite view_shift_super_non_expansive, !approx_sepcon; auto.
  - rewrite !approx_sepcon, protocol_W_super_non_expansive, approx_idem; auto.
  - extensionality ts x rho.
    destruct x as ((((((((?, ?), ?), ?), ?), ?), ?), ?), ?); simpl.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc, !and_assoc; auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : _ * Z * _ * _ * state * _ * _ * mpred * _) rho =>
    PROP ()
    LOCAL ()
    SEP (let '(l, v, g, g', s, s'', T, P, Q) := x in protocol_W l g g' s'' T * Q) rho).
  - repeat intro.
    apply (PROP_LOCAL_SEP_super_non_expansive SR_type [] [] [fun _ '(l, v, g, g', s, s'', T, P, Q) => _]);
      repeat constructor; hnf; intros; destruct x0 as ((((((((?, ?), ?), ?), ?), ?), ?), ?), ?); auto; simpl.
    rewrite !approx_sepcon, protocol_W_super_non_expansive, approx_idem; auto.
  - extensionality ts x rho.
    destruct x as ((((((((?, ?), ?), ?), ?), ?), ?), ?), ?); simpl.
    unfold SEPx; simpl; rewrite !sepcon_assoc; auto.
Qed.

Definition CRA_type := ProdType (ProdType (ProdType (ConstType (val * Z * Z * val * val * state * state))
  (ArrowType (ConstType state) (ArrowType (ConstType Z) Mpred))) Mpred) (ArrowType (ConstType Z) Mpred).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0,
             P at level 100, Q at level 100).

Program Definition CAS_RA_spec := TYPE CRA_type
  WITH l : val, c : Z, v : Z, g : val, g' : val, s : state, s'' : state, T : state -> Z -> mpred, P : mpred, Q : Z -> mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint, 3%positive OF tint ]
   PROP (repable_signed c; repable_signed v; forall v0, repable_signed v0 ->
     view_shift (P * T s v0) ((if eq_dec v0 c then T s'' v else T s v0) * Q v0); ord s s'')
   LOCAL (temp 1%positive l; temp 2%positive (vint c); temp 3%positive (vint v))
   SEP (protocol_W l g g' s T; P)
  POST [ tint ]
   EX v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (Val.of_bool (if eq_dec v' c then true else false)))
   SEP (protocol_W l g g' (if eq_dec v' c then s'' else s) T; Q v').
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : _) rho =>
    PROP (let '(l, c, v, g, g', s, s'', T, P, Q) := x in repable_signed c /\ repable_signed v /\
          (forall v0, repable_signed v0 -> view_shift (P * T s v0) ((if eq_dec v0 c then T s'' v else T s v0) * Q v0))
          /\ ord s s'')
    LOCAL (let '(l, c, v, g, g', s, s'', T, P, Q) := x in temp 1%positive l;
           let '(l, c, v, g, g', s, s'', T, P, Q) := x in temp 2%positive (vint c);
           let '(l, c, v, g, g', s, s'', T, P, Q) := x in temp 3%positive (vint v))
    SEP (let '(l, c, v, g, g', s, s'', T, P, Q) := x in protocol_W l g g' s T * P) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive CRA_type [fun _ => _] [fun _ => _; fun _ => _; fun _ => _] [fun _ => _]);
    repeat constructor; hnf; intros; destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?); auto; simpl.
  - rewrite !prop_and, !approx_andp; do 2 apply f_equal; f_equal.
    rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
    rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
    rewrite view_shift_super_non_expansive, !approx_sepcon; if_tac; auto.
  - rewrite !approx_sepcon, protocol_W_super_non_expansive, approx_idem; auto.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc, !and_assoc; auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : _ * _ * Z * _ * _ * _ * _ * _ * mpred * _) rho =>
    EX v' : Z,
      PROP (let '(l, c, v, g, g', s, s'', T, P, Q) := x in repable_signed v')
      LOCAL (let '(l, c, v, g, g', s, s'', T, P, Q) := x in temp ret_temp (Val.of_bool (if eq_dec v' c then true else false)))
      SEP (let '(l, c, v, g, g', s, s'', T, P, Q) := x in protocol_W l g g' (if eq_dec v' c then s'' else s) T *
           Q v') rho).
  - repeat intro.
    rewrite !approx_exp; apply f_equal; extensionality v'.
    apply (PROP_LOCAL_SEP_super_non_expansive CRA_type [fun _ '(l, c, v, g, g', s, s'', T, P, Q) => _]
      [fun _ '(l, c, v, g, g', s, s'', T, P, Q) => _] [fun _ '(l, c, v, g, g', s, s'', T, P, Q) => _]);
      repeat constructor; hnf; intros; destruct x0 as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?); auto; simpl.
    rewrite !approx_sepcon, protocol_W_super_non_expansive, approx_idem; auto.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
    apply f_equal; extensionality.
    unfold SEPx; simpl; rewrite !sepcon_assoc; auto.
Qed.

End atomics.