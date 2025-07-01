Require Import VST.veric.rmaps.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.ghosts.
Require Import VST.floyd.library.
Require Import VST.zlist.sublist.
Require Import VST.concurrency.lock_specs.
Require Import VST.atomics.verif_lock.
Require Import mailbox.atomic_exchange.
From Stdlib Require Import Lia.

(* standard VST prelude *)
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Section AEHist.

(* These histories should be usable for any atomically accessed location. *)
Inductive AE_hist_el := AE (r : val) (w : val).

Fixpoint apply_hist a h :=
  match h with
  | [] => Some a
  | AE r w :: h' => if eq_dec r a then apply_hist w h' else None
  end.

Arguments eq_dec _ _ _ _ : simpl never.

Lemma apply_hist_app : forall h1 i h2, apply_hist i (h1 ++ h2) =
  match apply_hist i h1 with Some v => apply_hist v h2 | None => None end.
Proof.
  induction h1; auto; simpl; intros.
  destruct a.
  destruct (eq_dec r i); auto.
Qed.

End AEHist.

Notation hist := (nat -> option AE_hist_el).

(* the lock invariant used to encode an atomic invariant *)
Definition AE_inv x g i R := EX h : list AE_hist_el, EX v : val,
  !!(apply_hist i h = Some v /\ tc_val tint v) &&
  (data_at Ews tint v x * ghost_ref h g * R h v).

Lemma AE_inv_exclusive : forall x g i R, exclusive_mpred (AE_inv x g i R).
Proof.
  unfold AE_inv; intros.
  eapply derives_exclusive, exclusive_sepcon1 with (Q := EX h : list AE_hist_el, EX v : val, _),
    data_at__exclusive with (sh := Ews)(t := tint); auto; simpl; try lia.
  Intros h v; rewrite sepcon_assoc; apply sepcon_derives; [cancel|].
  Exists h v; apply derives_refl.
Qed.
#[export] Hint Resolve AE_inv_exclusive : core.

Definition AE_loc sh l p g i R (h : hist) := lock_inv sh l (AE_inv p g i R) * ghost_hist sh h g.

Lemma AE_inv_super_non_expansive : forall n p g i R,
  compcert_rmaps.RML.R.approx n (AE_inv p g i R) =
  compcert_rmaps.RML.R.approx n (AE_inv p g i (fun h v => compcert_rmaps.RML.R.approx n (R h v))).
Proof.
  intros; unfold AE_inv.
  rewrite !approx_exp; apply f_equal; extensionality h.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_andp, !approx_sepcon.
  rewrite approx_idem; auto.
Qed.

Lemma AE_loc_super_non_expansive : forall n sh l p g i R h,
  compcert_rmaps.RML.R.approx n (AE_loc sh l p g i R h) =
  compcert_rmaps.RML.R.approx n (AE_loc sh l p g i (fun h v => compcert_rmaps.RML.R.approx n (R h v)) h).
Proof.
  intros; unfold AE_loc.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite lock_inv_super_non_expansive; do 2 f_equal.
  rewrite AE_inv_super_non_expansive; auto.
Qed.

(* This predicate describes the valid pre- and postconditions for a given atomic invariant R. *)
Definition AE_spec i P R Q := ALL hc : _, ALL hx : _, ALL vc : _, ALL vx : _,
  !!(apply_hist i hx = Some vx /\ hist_incl hc hx) -->
  ((R hx vx * P hc vc) -* (|==> R (hx ++ [AE vx vc]) vc *
    Q (map_upd hc (length hx) (AE vx vc)) vx)).

Lemma AE_spec_super_non_expansive : forall n i P R Q, compcert_rmaps.RML.R.approx n (AE_spec i P R Q) =
  compcert_rmaps.RML.R.approx n (AE_spec i (fun h v => compcert_rmaps.RML.R.approx n (P h v))
                                           (fun h v => compcert_rmaps.RML.R.approx n (R h v))
                                           (fun h v => compcert_rmaps.RML.R.approx n (Q h v))).
Proof.
  intros; unfold AE_spec.
  rewrite !(approx_allp _ _ _ empty_map); apply f_equal; extensionality.
  rewrite !(approx_allp _ _ _ []); apply f_equal; extensionality.
  rewrite !(approx_allp _ _ _ Vundef); apply f_equal; extensionality.
  rewrite !(approx_allp _ _ _ Vundef); apply f_equal; extensionality.
  setoid_rewrite approx_imp; f_equal; f_equal.
  rewrite view_shift_nonexpansive, !approx_sepcon; auto.
Qed.

Definition AE_type := ProdType (ProdType (ProdType
  (ConstType (share * val * gname * lock_handle * val * val * hist))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType (list AE_hist_el)) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)).

(* specification of atomic exchange *)
Program Definition atomic_exchange_spec := DECLARE _simulate_atomic_exchange
  TYPE AE_type WITH lsh : share, tgt : val, g : gname, l : lock_handle,
    i : val, v : val, h : hist, P : hist -> val -> mpred, R : list AE_hist_el -> val -> mpred, Q : hist -> val -> mpred
  PRE [ tptr tint, tptr t_lock, tint ]
   PROP (tc_val tint v; readable_share lsh)
   PARAMS (tgt; ptr_of l; v) GLOBALS ()
   SEP (AE_loc lsh l tgt g i R h; P h v; AE_spec i P R Q)
  POST [ tint ]
   EX t : nat, EX v' : val,
   PROP (tc_val tint v'; newer h t)
   LOCAL (temp ret_temp v')
   SEP (AE_loc lsh l tgt g i R (map_upd h t (AE v' v)); Q (map_upd h t (AE v' v)) v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; f_equal; f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  rewrite AE_loc_super_non_expansive; do 3 f_equal.
  apply AE_spec_super_non_expansive.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); simpl.
  rewrite !approx_exp; apply f_equal; extensionality t.
  rewrite !approx_exp; apply f_equal; extensionality v'.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem, AE_loc_super_non_expansive; auto.
Qed.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; atomic_exchange_spec]).

(* proof of the lock-based implementation of atomic exchange *)
Lemma body_atomic_exchange : semax_body Vprog Gprog f_simulate_atomic_exchange atomic_exchange_spec.
Proof. 
  start_dep_function.
  unfold AE_loc; Intros.
  forward_call (lsh, l, AE_inv tgt g i R).
  unfold AE_inv at 2; Intros h' v'.
  assert (lsh <> Share.bot).
  { intro; subst; contradiction unreadable_bot. }
  forward.
  forward.
  assert (apply_hist i (h' ++ [AE v' v]) = Some v) as Hh'.
  { rewrite apply_hist_app.
    replace (apply_hist i h') with (Some v'); simpl.
    apply eq_dec_refl. }
  gather_SEP (ghost_hist _ _ _) (ghost_ref _ _).
  assert_PROP (hist_incl h h') as Hincl.
  { go_lower; apply sepcon_derives_prop.
    rewrite hist_ref_join by auto.
    Intros hr.
    apply prop_right; eapply hist_sub_list_incl; eauto. }
  viewshift_SEP 0
    (ghost_hist lsh (map_upd h (length h') (AE v' v)) g * ghost_ref (h' ++ [AE v' v]) g)
    by (go_lower; eapply derives_trans, bupd_fupd; apply hist_add').
  gather_SEP (AE_spec _ _ _ _) (R h' v') (P h v); rewrite sepcon_assoc; simpl.
  viewshift_SEP 0 (R (h' ++ [AE v' v]) v * Q (map_upd h (length h') (AE v' v)) v').
  { go_lower; unfold AE_spec.
    eapply derives_trans, bupd_fupd.
    eapply derives_trans; [apply allp_sepcon1 | apply allp_left with h].
    eapply derives_trans; [apply allp_sepcon1 | apply allp_left with h'].
    eapply derives_trans; [apply allp_sepcon1 | apply allp_left with (Vint v)].
    eapply derives_trans; [apply allp_sepcon1 | apply allp_left with (Vint v')].
    rewrite prop_imp by auto.
    rewrite sepcon_comm; apply modus_ponens_wand. }
  forward_call release_simple (lsh, l, AE_inv tgt g i R).
  { lock_props.
    unfold AE_inv.
    Exists (h' ++ [AE v' v]) v; entailer!; cancel.
  }
  forward.
  Exists (length h') (Vint v'). unfold AE_loc; entailer!.
  apply hist_incl_lt; auto.
Qed.

Lemma AE_loc_join : forall sh1 sh2 sh l p g i R h1 h2 (Hjoin : sepalg.join sh1 sh2 sh)
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2) (Hcompat : disjoint h1 h2),
  AE_loc sh1 l p g i R h1 * AE_loc sh2 l p g i R h2 = AE_loc sh l p g i R (map_add h1 h2).
Proof.
  intros; unfold AE_loc.
  match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) = _ => transitivity ((P1 * P2) * (Q1 * Q2));
    [apply pred_ext; cancel|] end.
  erewrite lock_inv_share_join, ghost_hist_join by (eauto; intro; subst; contradiction unreadable_bot).
  rewrite prop_true_andp; auto.
Qed.
