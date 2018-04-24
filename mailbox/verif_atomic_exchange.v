Require Import VST.veric.rmaps.
Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.atomic_exchange.

Set Bullet Behavior "Strict Subproofs".

(* standard VST prelude *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* import funspecs from concurrency library *)
Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.

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
(*  exploit (ghost_inj _ _ _ _ _ w Hg1 Hg2); try join_sub.
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
Qed.*)
Admitted.

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

(* This predicate describes the valid pre- and postconditions for a given atomic invariant R. *)
Definition AE_spec i P R Q := ALL hc : _, ALL hx : _, ALL vc : _, ALL vx : _,
  !!(apply_hist i hx = Some vx /\ hist_incl hc hx) -->
  weak_view_shift (R hx vx * P hc vc) (R (hx ++ [AE vx vc]) vc * (weak_precise_mpred (R (hx ++ [AE vx vc]) vc) && emp) *
    Q (map_upd hc (length hx) (AE vx vc)) vx) && emp.

Definition AE_type := ProdType (ProdType (ProdType
  (ConstType (share * val * gname * val * val * val * hist))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType (list AE_hist_el)) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)).

(* specification of atomic exchange *)
Program Definition atomic_exchange_spec := DECLARE _simulate_atomic_exchange
  TYPE AE_type WITH lsh : share, tgt : val, g : gname, l : val,
    i : val, v : val, h : hist, P : hist -> val -> mpred, R : list AE_hist_el -> val -> mpred, Q : hist -> val -> mpred
  PRE [ _tgt OF tptr tint, _l OF tptr (Tstruct _lock_t noattr), _v OF tint ]
   PROP (tc_val tint v; readable_share lsh)
   LOCAL (temp _tgt tgt; temp _l l; temp _v v)
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
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  rewrite AE_loc_super_non_expansive; f_equal; f_equal.
  unfold AE_spec.
  rewrite !(approx_allp _ _ _ empty_map); apply f_equal; extensionality hc.
  rewrite !(approx_allp _ _ _ []); apply f_equal; extensionality hv.
  rewrite !(approx_allp _ _ _ Vundef); apply f_equal; extensionality vc.
  rewrite !(approx_allp _ _ _ Vundef); apply f_equal; extensionality vx.
  setoid_rewrite approx_imp; f_equal; f_equal.
  rewrite !approx_andp; f_equal.
  rewrite view_shift_nonexpansive.
  setoid_rewrite view_shift_nonexpansive at 2.
  rewrite !approx_sepcon, !approx_andp, !approx_idem.
  rewrite (nonexpansive_super_non_expansive weak_precise_mpred) by (apply precise_mpred_nonexpansive); auto.
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
  simpl; destruct ts as (((((((((lsh, tgt), g), l), i), v), h), P), R), Q).
  unfold AE_loc; Intros.
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
  viewshift_SEP 0
    (ghost_hist lsh (map_upd h (length h') (AE v' v)) g * ghost_ref (h' ++ [AE v' v]) g)
    by (go_lower; apply hist_add').
  gather_SEP 6 3 5; simpl.
  viewshift_SEP 0 (R (h' ++ [AE v' v]) v * (weak_precise_mpred (R (h' ++ [AE v' v]) v) && emp) *
    Q (map_upd h (length h') (AE v' v)) v').
  { go_lower; unfold AE_spec.
    eapply derives_trans; [apply allp_sepcon1 | apply allp_left with h].
    eapply derives_trans; [apply allp_sepcon1 | apply allp_left with h'].
    eapply derives_trans; [apply allp_sepcon1 | apply allp_left with (Vint v)].
    eapply derives_trans; [apply allp_sepcon1 | apply allp_left with (Vint v')].
    rewrite prop_imp by auto.
    apply apply_view_shift. }
  forward_call (l, lsh, AE_inv tgt g i R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply AE_inv_precise; auto. }
    unfold AE_inv.
    Exists (h' ++ [AE v' v]) v; entailer!.
    cancel. }
  forward.
  Exists (length h') (Vint v'). unfold AE_loc; entailer!.
  - apply hist_incl_lt; auto.
  - apply andp_left2; auto.
Qed.

Lemma AE_loc_join : forall sh1 sh2 sh l p g i R h1 h2 (Hjoin : sepalg.join sh1 sh2 sh)
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2) (Hcompat : compatible h1 h2),
  AE_loc sh1 l p g i R h1 * AE_loc sh2 l p g i R h2 = AE_loc sh l p g i R (map_add h1 h2).
Proof.
  intros; unfold AE_loc.
  match goal with |- (?P1 * ?Q1) * (?P2 * ?Q2) = _ => transitivity ((P1 * P2) * (Q1 * Q2));
    [apply pred_ext; cancel|] end.
  erewrite lock_inv_share_join, ghost_hist_join by (eauto; intro; subst; contradiction unreadable_bot).
  rewrite prop_true_andp; auto.
Qed.
