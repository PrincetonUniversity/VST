Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.general_atomics.

Set Bullet Behavior "Strict Subproofs".

Section atomics.

Context {CS : compspecs}.

Section protocols.

Class protocol {state : Type} (Iread Ifull : state -> Z -> mpred) :=
  { full_read s v : Ifull s v |-- |==> Ifull s v * Iread s v; read_dup s v : duplicable (Iread s v) }.

Global Instance dup_protocol {state} (T : state -> Z -> mpred) (Ht : forall s v, duplicable (T s v)) :
  protocol T T.
Proof.
  split; auto.
Qed.

Context {state : Type}.

Parameter protocol_A : val -> state -> (state -> state -> Prop) ->
  ((state -> Z -> mpred) * (state -> Z -> mpred)) -> mpred.

Context (ord : state -> state -> Prop) `{RelationClasses.PreOrder _ ord}
  (Tread Tfull : state -> Z -> mpred).

Axiom ex_protocol_A_precise : forall l ord Tread Tfull, precise (EX s : _, protocol_A l s ord (Tread, Tfull))%logic.

Corollary protocol_A_precise : forall l s ord Tread Tfull, precise (protocol_A l s ord (Tread, Tfull)).
Proof.
  intros; eapply derives_precise', ex_protocol_A_precise.
  Exists s; apply derives_refl.
Qed.

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

Axiom protocol_A_join' : forall l s1 s2,
  protocol_A l s1 ord T * protocol_A l s2 ord T |--
  EX s : _, !!(ord s1 s /\ ord s2 s) && protocol_A l s ord T.

Axiom make_protocol : forall {P : protocol Tread Tfull} l v s, repable_signed v ->
  data_at Tsh tint (vint v) l * |> Tfull s v |-- |==> protocol_A l s ord T.

Axiom protocol_A_later : forall l s,
  protocol_A l s ord (|>Tread, |>Tfull) |-- |>protocol_A l s ord T.

Axiom protocol_A_delay : forall l s,
  protocol_A l s ord T |-- protocol_A l s ord (|>Tread, |>Tfull).

End protocols.

Lemma approx_later : forall n P, approx (S n) (|> P) = |> approx n P.
Proof.
  intros; apply predicates_hered.pred_ext.
  - intros ? [].
    change ((|> approx n P)%pred a); intros ??; split; auto.
    apply laterR_level in H1; omega.
  - intros ??.
    destruct (level a) eqn: Hl.
    + split; [omega|].
      intros ??.
      apply laterR_level in H0; omega.
    + destruct (levelS_age _ _ (eq_sym Hl)) as (a' & ? & ?); subst.
      destruct (H a').
      { constructor; auto. }
      split; [omega|].
      intros ? HL; apply (H _ HL).
Qed.

Lemma approx_0 : forall P, approx 0 P = FF.
Proof.
  intros; apply predicates_hered.pred_ext.
  - intros ? []; omega.
  - intros ??; contradiction.
Qed.

Definition OrdType s := ArrowType s (ArrowType s (ConstType Prop)).
Definition PredType s := ArrowType s (ArrowType (ConstType Z) Mpred).

Definition LA_type := ProdType (ProdType (ProdType (ProdType (ProdType (ProdType
  (ConstType val) (DependentType 0)) (OrdType (DependentType 0)))
  (ProdType (PredType (DependentType 0)) (PredType (DependentType 0))))
  Mpred) (ConstType (namespace -> Prop))) (PredType (DependentType 0)).

Program Definition load_acq_spec := TYPE LA_type
  WITH l : val, s : _, st_ord : _ -> _ -> Prop, T : ((_ -> Z -> mpred) * (_ -> Z -> mpred)),
       P : mpred, E : Ensemble namespace, Q : _ -> Z -> mpred
  PRE [ 1%positive OF tptr tint ]
   PROP ()
   LOCAL (temp 1%positive l)
   SEP (ALL s' : _, !!(st_ord s s') --> ALL v : _,
          weak_fview_shift E E (fst T s' v * P * protocol_A l s' st_ord T) (Q s' v) && emp;
        P; protocol_A l s st_ord T)
  POST [ tint ]
   EX v : Z, EX s' : _,
   PROP (repable_signed v; st_ord s s')
   LOCAL (temp ret_temp (vint v))
   SEP (Q s' v).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((?, s), ?), (?, ?)), P), ?), Q); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  rewrite protocol_A_super_non_expansive; f_equal.
  rewrite !approx_allp by auto; f_equal; extensionality.
  setoid_rewrite approx_imp; f_equal; f_equal.
  rewrite !(approx_allp _ _ _ 0); f_equal; extensionality.
  rewrite !approx_andp; f_equal.
  rewrite fview_shift_nonexpansive.
  setoid_rewrite fview_shift_nonexpansive at 2.
  rewrite !approx_sepcon, !approx_idem, protocol_A_super_non_expansive; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((?, ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality.
  rewrite !approx_exp; apply f_equal; extensionality.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Definition SR_type := ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType
  (ConstType (val * Z)) (DependentType 0)) (DependentType 0)) (OrdType (DependentType 0)))
  (ProdType (PredType (DependentType 0)) (PredType (DependentType 0))))
  Mpred) (ConstType (namespace -> Prop))) Mpred.

(*Program Definition store_rel_spec := TYPE SR_type
  WITH l : val, v : Z, s : _, s'' : _, st_ord : _ -> _ -> Prop, T : ((_ -> Z -> mpred) * (_ -> Z -> mpred)),
       P : mpred, II : Z -> mpred, lI : list Z, Q' : mpred, Q : mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v; forall s', st_ord s' s'';
         view_shift (fold_right sepcon emp (map II lI) * P)
                    (protocol_A l s st_ord T * snd T s'' v * Q')%logic;
         view_shift (protocol_A l s'' st_ord T * Q')
                    (fold_right sepcon emp (map II lI) * Q)%logic)
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
        intro; simpl; rewrite approx_idem; auto.
      * rewrite !approx_sepcon, !approx_idem, protocol_A_super_non_expansive; auto.
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2.
      rewrite !approx_sepcon, !approx_sepcon_list', protocol_A_super_non_expansive, !approx_idem.
      erewrite !map_map, map_ext; eauto.
      intro; simpl; rewrite approx_idem; auto.
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
Qed.*)

(*Definition SR_type' := ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType (ProdType
  (ConstType (val * Z)) (DependentType 0)) (OrdType (DependentType 0)))
  (ProdType (PredType (DependentType 0)) (PredType (DependentType 0))))
  Mpred) (ArrowType (ConstType Z) Mpred)) (ConstType (list Z))) (ArrowType (DependentType 0) Mpred))
  (ArrowType (DependentType 0) Mpred).

(* The GPS/iGPS store_rel rule is only really useful when we have a single writer, only write once
   to a location, only really want to maintain an invariant, or otherwise aren't really doing anything
   with write-write races. The final-state restriction is partially to ensure that the target state is
   reachable, and partly to deal with the fact that the logic doesn't assume mo-coherence
   and thus a write may be placed "before" a write that's already been observed. This more relaxed
   rule is probably unsound. *)
Program Definition store_rel_spec := TYPE SR_type'
  WITH l : val, v : Z, s : _, st_ord : _ -> _ -> Prop, T : ((_ -> Z -> mpred) * (_ -> Z -> mpred)),
       P : mpred, II : Z -> mpred, lI : list Z, Q' : _ -> mpred, Q : _ -> mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v;
         view_shift (fold_right sepcon emp (map II lI) * P)
                    (protocol_A l s st_ord T * P');
         forall s' v', repable_signed v' -> st_ord s s' ->
         view_shift (P' * snd T s' v')
                    (EX s'' : _, !!(st_ord s' s'') && snd T s'' v * Q' s'')%logic;
         forall s', st_ord s s' ->
         view_shift (protocol_A l s' st_ord T * Q' s')
                    (fold_right sepcon emp (map II lI) * Q s')%logic)
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
        intro; simpl; rewrite approx_idem; auto.
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
        intro; simpl; rewrite approx_idem; auto.
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

Definition CRA_type := ProdType (ProdType (ProdType (ProdType (ProdType
  (ProdType (ProdType (ConstType (val * Z * Z)) (DependentType 0)) (OrdType (DependentType 0)))
  (ProdType (PredType (DependentType 0)) (PredType (DependentType 0)))) Mpred)
  (ConstType (namespace -> Prop))) (ArrowType (DependentType 0) Mpred))
  (PredType (DependentType 0)).

Program Definition CAS_RA_spec := TYPE CRA_type
  WITH l : val, c : Z, v : Z, s : _, st_ord : _ -> _ -> Prop, T : ((_ -> Z -> mpred) * (_ -> Z -> mpred)),
       P : mpred, E : _, Q : _ -> mpred, R : _ -> Z -> mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint, 3%positive OF tint ]
   PROP (repable_signed c; repable_signed v)
   LOCAL (temp 1%positive l; temp 2%positive (vint c); temp 3%positive (vint v))
   SEP (ALL s' : _, !!(st_ord s s') --> weak_fview_shift E E (snd T s' c * P)
          (EX s'' : _, !!(st_ord s' s'') && |> snd T s'' v *
           weak_fview_shift E E (protocol_A l s'' st_ord T) (Q s'')) && emp;
        ALL s' : _, ALL v' : _, !!(st_ord s s' /\ repable_signed v' /\ v <> c) -->
          weak_fview_shift E E (|> fst T s' v' * protocol_A l s' st_ord T * P) (R s' v') && emp;
        protocol_A l s st_ord T; P)
  POST [ tint ]
   EX v' : Z, EX s' : _,
   PROP (repable_signed v'; st_ord s s')
   LOCAL (temp ret_temp (Val.of_bool (if eq_dec v' c then true else false)))
   SEP (if eq_dec v' c then Q s' else R s' v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((((?, ?), ?), s), ?), (?, ?)), ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  unfold LOCALx; simpl; rewrite !approx_andp; f_equal.
  unfold SEPx; simpl; rewrite !sepcon_emp, !approx_sepcon, !approx_idem.
  f_equal; [|rewrite protocol_A_super_non_expansive; f_equal].
  - rewrite !approx_allp by auto; f_equal; extensionality.
    setoid_rewrite approx_imp; f_equal; f_equal.
    rewrite !approx_andp; f_equal.
    rewrite fview_shift_nonexpansive.
    setoid_rewrite fview_shift_nonexpansive at 2.
    rewrite !approx_sepcon, !approx_idem; f_equal; f_equal.
    rewrite !approx_exp; f_equal; extensionality.
    rewrite !approx_sepcon, !approx_andp; f_equal.
    + f_equal.
      destruct n; [rewrite !approx_0; auto|].
      setoid_rewrite approx_later.
      etransitivity; [rewrite <- approx_oo_approx' with (n' := S n)|]; auto.
    + rewrite fview_shift_nonexpansive.
      setoid_rewrite fview_shift_nonexpansive at 2.
      rewrite !approx_idem, protocol_A_super_non_expansive; auto.
  - rewrite !approx_allp by auto; f_equal; extensionality.
    rewrite !approx_allp by auto; f_equal; extensionality.
    setoid_rewrite approx_imp; f_equal; f_equal.
    rewrite !approx_andp; f_equal.
    rewrite fview_shift_nonexpansive.
    setoid_rewrite fview_shift_nonexpansive at 2.
    rewrite !approx_sepcon, !approx_idem; f_equal; f_equal.
    rewrite protocol_A_super_non_expansive; f_equal; f_equal.
    destruct n; [rewrite !approx_0; auto|].
    setoid_rewrite approx_later.
    etransitivity; [rewrite <- approx_oo_approx' with (n' := S n)|]; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality.
  rewrite !approx_exp; apply f_equal; extensionality.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  unfold LOCALx; simpl; rewrite !approx_andp; f_equal.
  unfold SEPx; simpl; rewrite !sepcon_emp; if_tac; rewrite approx_idem; auto.
Qed.

End atomics.
