Require Import veric.rmaps.
Require Import veric.compcert_rmaps.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.general_atomics.

Set Bullet Behavior "Strict Subproofs".

Section atomics.

Context {CS : compspecs}.

Section protocols.

Context {state : Type}.

Class protocol {state : Type} (Iread Ifull : state -> Z -> mpred) :=
  { full_read s v : view_shift (Ifull s v) (Ifull s v * Iread s v); read_dup s v : duplicable (Iread s v) }.

Global Instance dup_protocol {state} (T : state -> Z -> mpred) (Ht : forall s v, duplicable (T s v)) :
  protocol T T.
Proof.
  split; auto.
Qed.

Parameter protocol_A : val -> state -> (state -> state -> Prop) ->
  ((state -> Z -> mpred) * (state -> Z -> mpred)) -> mpred.

Context `{PCM_order state} (Tread Tfull : state -> Z -> mpred).

Axiom protocol_A_nonexpansive : forall l s ord Tread1 Tfull1 Tread2 Tfull2,
  (ALL s : state, ALL v : Z, (Tread1 s v <=> Tread2 s v) && (Tfull1 s v <=> Tfull2 s v)) |--
  protocol_A l s ord (Tread1, Tfull1) <=> protocol_A l s ord (Tread2, Tfull2).

Lemma protocol_A_super_non_expansive : forall n l s ord Tread Tfull,
  approx n (protocol_A l s ord (Tread, Tfull)) =
  approx n (protocol_A l s ord (fun s v => approx n (Tread s v), fun s v => approx n (Tfull s v))).
Proof.
  intros.
  apply approx_eq_i'.
  intros m ?.
  apply protocol_A_nonexpansive.
  intros ??; split; apply fash_equiv_approx; auto.
Qed.

Notation T := (Tread, Tfull).

Axiom protocol_A_duplicable : forall l s, duplicable (protocol_A l s ord T).

Axiom protocol_A_join : forall l s1 s2 s, join s1 s2 s ->
  protocol_A l s1 ord T * protocol_A l s2 ord T = protocol_A l s ord T.

Corollary protocol_A_absorb : forall l s1 s2, ord s1 s2 ->
  protocol_A l s1 ord T * protocol_A l s2 ord T = protocol_A l s2 ord T.
Proof.
  intros; apply protocol_A_join.
  apply join_comm, ord_join; auto.
Qed.

Axiom protocol_A_join' : forall l s1 s2,
  protocol_A l s1 ord T * protocol_A l s2 ord T |--
  EX s : _, !!(join s1 s2 s) && protocol_A l s ord T.

Axiom make_protocol : forall {P : protocol Tread Tfull} l v s, repable_signed v ->
  view_shift (data_at Tsh tint (vint v) l * Tfull s v) (protocol_A l s ord T).

Axiom protocol_A_forget : forall l s1 s2, ord s1 s2 ->
  view_shift (protocol_A l s2 ord T) (protocol_A l s1 ord T).

Corollary protocol_A_choose : forall l s1 s2,
  view_shift (protocol_A l s1 ord T * protocol_A l s2 ord T) (protocol_A l s1 ord T).
Proof.
  intros.
  etransitivity; [apply derives_view_shift, protocol_A_join'|].
  view_shift_intro s; view_shift_intros.
  match goal with H : join _ _ _ |- _ => apply join_ord in H; destruct H end.
  apply protocol_A_forget; auto.
Qed.

Axiom protocol_A_later : forall l s,
  protocol_A l s ord (|>Tread, |>Tfull) |-- |>protocol_A l s ord T.

Axiom protocol_A_delay : forall l s,
  protocol_A l s ord T |-- protocol_A l s ord (|>Tread, |>Tfull).

End protocols.

Definition OrdType s := ArrowType s (ArrowType s (ConstType Prop)).
Definition PredType s := ArrowType s (ArrowType (ConstType Z) Mpred).

Definition LA_type := ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType
  (ConstType val) (DependentType 0)) (OrdType (DependentType 0)))
  (ProdType (PredType (DependentType 0)) (PredType (DependentType 0))))
  Mpred) (ArrowType (ConstType Z) Mpred)) (ConstType (list Z))) Mpred) (PredType (DependentType 0)).

Program Definition load_acq_spec := TYPE LA_type
  WITH l : val, s : _, st_ord : _ -> _ -> Prop, T : ((_ -> Z -> mpred) * (_ -> Z -> mpred)),
       P : mpred, II : Z -> mpred, lI : list Z, P' : mpred, Q : _ -> Z -> mpred
  PRE [ 1%positive OF tptr tint ]
   PROP (view_shift (fold_right sepcon emp (map (fun p => |>II p) lI) * P)
                    (protocol_A l s st_ord T * P');
         forall s' v, st_ord s s' -> repable_signed v ->
           view_shift (fst T s' v * protocol_A l s' st_ord T * P')%logic
           (fold_right sepcon emp (map (fun p => |>II p) lI) * Q s' v))
   LOCAL (temp 1%positive l)
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); P)
  POST [ tint ]
   EX v : Z, EX s' : _,
   PROP (repable_signed v; st_ord s s')
   LOCAL (temp ret_temp (vint v))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); Q s' v).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((((?, s), ?), (?, ?)), P), ?), ?), ?), Q); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  - rewrite !prop_and, !approx_andp; f_equal; [|f_equal].
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
      * rewrite !approx_sepcon, approx_idem, protocol_A_super_non_expansive; auto.
    + rewrite !prop_forall, !(approx_allp _ _ _ s); f_equal; extensionality s'.
      rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
      rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
      setoid_rewrite approx_imp; do 2 apply f_equal.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2.
      rewrite !approx_sepcon, !approx_sepcon_list', protocol_A_super_non_expansive, !approx_idem.
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
  destruct x as ((((((((?, ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality v'.
  rewrite !approx_exp; apply f_equal; extensionality s'.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  rewrite !approx_sepcon_list'.
  erewrite !map_map, map_ext; eauto.
  intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.

Definition SR_type := ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType
  (ConstType (val * Z)) (DependentType 0)) (DependentType 0)) (OrdType (DependentType 0)))
  (ProdType (PredType (DependentType 0)) (PredType (DependentType 0))))
  Mpred) (ArrowType (ConstType Z) Mpred)) (ConstType (list Z))) Mpred) Mpred.

Program Definition store_rel_spec := TYPE SR_type
  WITH l : val, v : Z, s : _, s'' : _, st_ord : _ -> _ -> Prop, T : ((_ -> Z -> mpred) * (_ -> Z -> mpred)),
       P : mpred, II : Z -> mpred, lI : list Z, Q' : mpred, Q : mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v; forall s', st_ord s' s'';
         view_shift (fold_right sepcon emp (map (fun p => |>II p) lI) * P)
                    (protocol_A l s st_ord T * snd T s'' v * Q')%logic;
         view_shift (protocol_A l s'' st_ord T * Q')
                    (fold_right sepcon emp (map (fun p => |>II p) lI) * Q)%logic)
   LOCAL (temp 1%positive l; temp 2%positive (vint v))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); P)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); Q).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((((((?, ?), ?), ?), ?), (?, ?)), ?), ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  - rewrite !prop_and, !approx_andp; f_equal; f_equal; f_equal; [|f_equal].
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
      * rewrite !approx_sepcon, !approx_idem, protocol_A_super_non_expansive; auto.
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2.
      rewrite !approx_sepcon, !approx_sepcon_list', protocol_A_super_non_expansive, !approx_idem.
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
  destruct x as ((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  rewrite !approx_sepcon_list'.
  erewrite !map_map, map_ext; eauto.
  intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.

(*Definition SR_type' := ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType
  (ConstType (val * Z)) (DependentType 0)) (OrdType (DependentType 0)))
  (ProdType (PredType (DependentType 0)) (PredType (DependentType 0))))
  Mpred) (ArrowType (ConstType Z) Mpred)) (ConstType (list Z))) (ArrowType (DependentType 0) Mpred))
  (ArrowType (DependentType 0) Mpred).

(* The GPS/iGPS store_rel rule is only really useful when we have a single writer, only write once
   to a location, only really want to maintain an invariant, or otherwise aren't really doing anything
   with write-write races. The final-state restriction is partially to ensure that the target state is
   reachable, and partly to deal with the fact that the logic doesn't assume mo-coherence (which RA should
   supply) and thus a write may be placed "before" a write that's already been observed. This more relaxed
   rule can probably be proven from base Iris, but it would involve completely redoing the core GPS invariant. *)
Program Definition store_rel_spec := TYPE SR_type'
  WITH l : val, v : Z, s : _, st_ord : _ -> _ -> Prop, T : ((_ -> Z -> mpred) * (_ -> Z -> mpred)),
       P : mpred, II : Z -> mpred, lI : list Z, Q' : _ -> mpred, Q : _ -> mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v;
         view_shift (fold_right sepcon emp (map (fun p => |>II p) lI) * P)
                    (protocol_A l s st_ord T * P');
         forall s' v', repable_signed v' -> st_ord s s' ->
         view_shift (P' * snd T s' v')
                    (EX s'' : _, !!(st_ord s' s'') && snd T s'' v * Q' s'')%logic;
         forall s', st_ord s s' ->
         view_shift (protocol_A l s' st_ord T * Q' s')
                    (fold_right sepcon emp (map (fun p => |>II p) lI) * Q s')%logic)
   LOCAL (temp 1%positive l; temp 2%positive (vint v))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); P)
  POST [ tvoid ]
   EX s' : _,
   PROP (st_ord s s')
   LOCAL ()
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); Q s').
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((((?, ?), s), ?), (?, ?)), ?), ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  - rewrite !prop_and, !approx_andp; f_equal; f_equal; [|f_equal].
    + rewrite !prop_forall, !(approx_allp _ _ _ s); apply f_equal; extensionality s'.
      rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
      * rewrite !approx_sepcon, protocol_A_super_non_expansive; apply f_equal.
        rewrite !approx_exp; apply f_equal; extensionality s''.
        rewrite !approx_sepcon, !approx_andp, !approx_idem; auto.
    + rewrite !prop_forall, !(approx_allp _ _ _ s); apply f_equal; extensionality s'.
      rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2.
      do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, !approx_idem, protocol_A_super_non_expansive; auto.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
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
  destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality s'.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  rewrite !approx_sepcon_list'.
  erewrite !map_map, map_ext; eauto.
  intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.*)

Definition CRA_type := ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType
  (ProdType (ProdType (ConstType (val * Z * Z)) (DependentType 0)) (OrdType (DependentType 0)))
  (ProdType (PredType (DependentType 0)) (PredType (DependentType 0)))) Mpred)
  (ArrowType (ConstType Z) Mpred)) (ConstType (list Z))) Mpred) (ArrowType (DependentType 0) Mpred))
  (PredType (DependentType 0))) (PredType (DependentType 0)).

Program Definition CAS_RA_spec := TYPE CRA_type
  WITH l : val, c : Z, v : Z, s : _, st_ord : _ -> _ -> Prop, T : ((_ -> Z -> mpred) * (_ -> Z -> mpred)),
       P : mpred, II : Z -> mpred, lI : list Z, P' : mpred, Q' : _ -> mpred, R' : _ -> Z -> mpred, Q : _ -> Z -> mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint, 3%positive OF tint ]
   PROP (repable_signed c; repable_signed v;
         view_shift (fold_right sepcon emp (map (fun p => |>II p) lI) * P)
                    (protocol_A l s st_ord T * P');
         forall s', st_ord s s' ->
           view_shift (P' * snd T s' c) (EX s'' : _, !!(st_ord s' s'') && snd T s'' v * Q' s'');
         forall s' v', repable_signed v' -> v' <> c -> st_ord s s' -> view_shift (P' * fst T s' v') (R' s' v');
         forall s' v', repable_signed v' -> st_ord s s' ->
           view_shift (protocol_A l s' st_ord T * (if eq_dec v' c then Q' s' else R' s' v'))
                      (fold_right sepcon emp (map (fun p => |>II p) lI) * Q s' v'))
   LOCAL (temp 1%positive l; temp 2%positive (vint c); temp 3%positive (vint v))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); P)
  POST [ tint ]
   EX v' : Z, EX s' : _,
   PROP (repable_signed v'; st_ord s s')
   LOCAL (temp ret_temp (Val.of_bool (if eq_dec v' c then true else false)))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); Q s' v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((((((((?, ?), ?), s), ?), (?, ?)), ?), ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  - rewrite !prop_and, !approx_andp; do 2 apply f_equal; f_equal; [|f_equal; [|f_equal]].
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
      * rewrite !approx_sepcon, !approx_idem, protocol_A_super_non_expansive; auto.
    + rewrite !prop_forall, !(approx_allp _ _ _ s); f_equal; extensionality s'.
      rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, !approx_idem; auto.
      * rewrite !approx_exp; apply f_equal; extensionality s''.
        rewrite !approx_sepcon, !approx_andp, !approx_idem; auto.
    + rewrite !prop_forall, !(approx_allp _ _ _ s); f_equal; extensionality s'.
      rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
      rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
      setoid_rewrite approx_imp; do 2 apply f_equal.
      setoid_rewrite approx_imp; do 2 apply f_equal.
      rewrite view_shift_super_non_expansive, !approx_sepcon; auto.
    + f_equal.
      rewrite !prop_forall, !(approx_allp _ _ _ s); f_equal; extensionality s'.
      rewrite !prop_forall, !(approx_allp _ _ _ 0); f_equal; extensionality v'.
      rewrite !prop_impl; setoid_rewrite approx_imp; do 2 apply f_equal.
      setoid_rewrite approx_imp; do 2 apply f_equal.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, protocol_A_super_non_expansive; apply f_equal.
        if_tac; rewrite approx_idem; auto.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite nonexpansive_super_non_expansive by (apply later_nonexpansive); auto.
  - unfold LOCALx; simpl; rewrite !approx_andp; f_equal.
    unfold SEPx; simpl; rewrite !sepcon_emp, !approx_sepcon, !approx_idem, !approx_sepcon_list'.
    erewrite !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality v'.
  rewrite !approx_exp; apply f_equal; extensionality s'.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  unfold LOCALx; simpl; rewrite !approx_andp; f_equal.
  unfold SEPx; simpl; rewrite !sepcon_emp, !approx_sepcon, !approx_idem, !approx_sepcon_list'.
  erewrite !map_map, map_ext; eauto.
  intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.

End atomics.

(* Witnesses for common use cases *)
Definition load_acq_witness {state} l (s : state) st_ord T P Q := (l, s, st_ord, T, protocol_A l s st_ord T * P,
  fun _ : Z => FF, @nil Z, P, fun s' (v' : Z) => protocol_A l s' st_ord T * Q s' v').

Definition store_rel_witness {state} l (v : Z) (s : state) st_ord T P Q := (l, v, s, st_ord, T,
  protocol_A l s st_ord T * P, fun _ : Z => FF, @nil Z, Q, fun s' => protocol_A l s' st_ord T * Q s').

Definition CAS_RA_witness {state} l (c v : Z) (s : state) st_ord T P Q R := (l, c, v, s, st_ord, T,
  protocol_A l s st_ord T * P, fun _ : Z => FF, @nil Z, P, Q, R,
  fun s' v' => protocol_A l s' st_ord T * (if eq_dec v' c then Q s' else R s' v')).
