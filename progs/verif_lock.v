Require Import progs.verif_atomic_exchange.
Require Import veric.rmaps.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import progs.lock.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.

Definition lock_R R (h : list AE_hist_el) v := EX z : Z, !!(repable_signed z /\ v = vint z) &&
  (weak_precise_mpred R && emp) * (weak_positive_mpred R && emp) * if eq_dec z 0 then R else emp.

Definition my_lock sh l p R := lock_inv sh l (AE_inv p (vint 1) Tsh (lock_R R)) *
  EX h : hist, ghost_hist h p.

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4) =>
     match x with (x1,x2,x3,x4) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4) =>
     match x with (x1,x2,x3,x4) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             P at level 100, Q at level 100).

Definition lock_sig := (ProdType (ConstType (share * val * val)) Mpred).

Lemma lock_R_super_non_expansive : forall n R h v, compcert_rmaps.RML.R.approx n (lock_R R h v) =
  compcert_rmaps.RML.R.approx n (lock_R (compcert_rmaps.RML.R.approx n R) h v).
Proof.
  unfold lock_R; intros.
  rewrite !approx_exp; f_equal; extensionality z.
  rewrite !approx_sepcon, !approx_andp; f_equal.
  - rewrite nonexpansive_super_non_expansive by (apply precise_mpred_nonexpansive).
    rewrite (nonexpansive_super_non_expansive (fun R => weak_positive_mpred R))
      by (apply positive_mpred_nonexpansive); auto.
  - destruct (eq_dec z 0); auto.
    replace (compcert_rmaps.RML.R.approx n R) with
      (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) R) at 1
      by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
Qed.

Lemma my_lock_super_non_expansive : forall n sh l p R, compcert_rmaps.RML.R.approx n (my_lock sh l p R) =
  compcert_rmaps.RML.R.approx n (my_lock sh l p (compcert_rmaps.RML.R.approx n R)).
Proof.
  unfold my_lock; intros.
  rewrite !approx_sepcon.
  rewrite (nonexpansive_super_non_expansive (fun R => lock_inv sh l R)) by (apply nonexpansive_lock_inv).
  setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv sh l R)) at 2;
    [|apply nonexpansive_lock_inv].
  evar (rhs : mpred).
  replace (compcert_rmaps.RML.R.approx n (AE_inv _ _ _ _)) with rhs; subst rhs; [reflexivity|].
  unfold AE_inv.
  rewrite !approx_exp; f_equal; extensionality h.
  rewrite !approx_exp; f_equal; extensionality v.
  rewrite !approx_andp; f_equal.
  rewrite !approx_sepcon; f_equal.
  - f_equal.
    symmetry; apply lock_R_super_non_expansive.
  - rewrite !approx_andp; f_equal.
    rewrite nonexpansive_super_non_expansive by (apply precise_mpred_nonexpansive).
    setoid_rewrite nonexpansive_super_non_expansive at 2; [|apply precise_mpred_nonexpansive].
    setoid_rewrite lock_R_super_non_expansive at 2; auto.
Qed.

Program Definition my_acquire_spec :=
 DECLARE _my_acquire TYPE lock_sig
  WITH sh : share, l : val, p : val, R : mpred
  PRE [ _l OF tptr tint, _ll OF tptr (Tstruct _lock_t noattr) ]
   PROP (readable_share sh)
   LOCAL (temp _l p; temp _ll l)
   SEP (my_lock sh l p R)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (my_lock sh l p R; R).
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : share * val * val * mpred) rho =>
    PROP (let '(sh, _, _, _) := x in readable_share sh)
    LOCAL (let '(_, _, p, _) := x in temp _l p;
           let '(_, l, _, _) := x in temp _ll l)
    SEP (let '(sh, l, p, R) := x in my_lock sh l p R) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive lock_sig [fun _ => _] [fun _ => _; fun _ => _]
    [fun _ => _]); repeat constructor; hnf; intros; destruct x as (((?, ?), ?), R); simpl; try timeout 1 reflexivity.
  - apply my_lock_super_non_expansive.
  - extensionality ts x rho.
    destruct x as (((?, ?), ?), ?); auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : share * val * val * mpred) rho =>
    PROP () LOCAL () SEP (let '(sh, l, p, R) := x in my_lock sh l p R * R) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive lock_sig [] [] [fun _ => _]); repeat constructor; hnf; intros;
    destruct x as (((?, ?), ?), R); simpl; try timeout 1 reflexivity.
  - rewrite !approx_sepcon, my_lock_super_non_expansive.
    replace (compcert_rmaps.RML.R.approx n R) with
      (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) R) at 2
      by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
  - extensionality ts x rho.
    destruct x as (((?, ?), ?), ?); auto.
    unfold SEPx; simpl; rewrite !sepcon_assoc; auto.
Qed.

Program Definition my_release_spec :=
 DECLARE _my_release TYPE (ProdType (ConstType (share * val * val)) Mpred)
  WITH sh : share, l : val, p : val, R : mpred
  PRE [ _l OF tptr tint, _ll OF tptr (Tstruct _lock_t noattr) ]
   PROP (readable_share sh)
   LOCAL (temp _l p; temp _ll l)
   SEP (my_lock sh l p R; R)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (my_lock sh l p R).
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : share * val * val * mpred) rho =>
    PROP (let '(sh, _, _, _) := x in readable_share sh)
    LOCAL (let '(_, _, p, _) := x in temp _l p;
           let '(_, l, _, _) := x in temp _ll l)
    SEP (let '(sh, l, p, R) := x in my_lock sh l p R * R) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive lock_sig [fun _ => _] [fun _ => _; fun _ => _]
    [fun _ => _]); repeat constructor; hnf; intros;
    destruct x as (((?, ?), ?), R); simpl; try timeout 1 reflexivity.
  - rewrite !approx_sepcon, my_lock_super_non_expansive.
    replace (compcert_rmaps.RML.R.approx n R) with
      (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) R) at 2
      by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
  - extensionality ts x rho.
    destruct x as (((?, ?), ?), ?); auto.
    unfold SEPx; simpl; rewrite !sepcon_assoc; auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type) (x : share * val * val * mpred) rho =>
    PROP () LOCAL () SEP (let '(sh, l, p, R) := x in my_lock sh l p R) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive lock_sig [] [] [fun _ => _]); repeat constructor; hnf; intros;
    destruct x as (((?, ?), ?), R); simpl; try timeout 1 reflexivity.
  - apply my_lock_super_non_expansive.
  - extensionality ts x rho.
    destruct x as (((?, ?), ?), ?); auto.
Qed.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; atomic_exchange_spec;
  my_acquire_spec; my_release_spec]).

Lemma weak_precise_lock_R : forall R h v, predicates_hered.derives
  (weak_precise_mpred R && emp) (weak_precise_mpred (lock_R R h v) && emp).
Proof.
  unfold lock_R; intros ???? (Hprecise & ?).
  split; auto.
  intros ??? (? & v1 & ? & ? & ? & (? & ? & ? & ((? & ?) & (? & ?)) & (? & ?)) & ?)
    (? & v2 & ? & ? & ? & (? & ? & ? & ((? & ?) & (? & ?)) & (? & ?)) & ?) ??; subst.
  exploit (repr_inj_signed v1 v2); auto; [congruence | intro; subst].
  repeat match goal with H : predicates_hered.app_pred emp ?r, H' : sepalg.join ?r _ _ |- _ =>
    specialize (H _ _ H'); subst end.
  destruct (eq_dec v2 0).
  - apply (Hprecise w); auto; split; auto.
  - repeat match goal with H : predicates_hered.app_pred emp ?r, H' : sepalg.join_sub ?r _ |- _ =>
      destruct H' as (? & H'); specialize (H _ _ H'); subst end.
    eapply sepalg.same_unit; eauto.
Qed.

Lemma body_my_acquire : semax_body Vprog Gprog f_my_acquire my_acquire_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as (((sh, l), p), R).
  forward.
  eapply semax_seq'.
  eapply semax_pre with (P' := EX z : Z, PROP (repable_signed z) LOCAL (temp _r (vint z); temp _l p; temp _ll l)
    SEP (my_lock sh l p R; if eq_dec z 0 then R else emp)).
  { Exists 1; entailer!.
    split; computable. }
  eapply semax_loop; [|forward; apply drop_tc_environ].
  - Intros z.
    forward_if (PROP () LOCAL (temp _r (vint z); temp _l p; temp _ll l) SEP (my_lock sh l p R)).
    + forward.
      destruct (eq_dec z 0); [subst; absurd (Int.repr 0 = Int.zero); auto|].
      entailer!.
    + forward.
      assert (z = 0).
      { apply repr_inj_signed; auto.
        split; computable. }
      subst; rewrite eq_dec_refl; apply drop_tc_environ.
    + unfold my_lock; Intros h.
      forward_call (Tsh, sh, p, l, vint 1, vint 1, h, fun (h : hist) (v : val) => !!(v = vint 1) && emp, lock_R R,
        fun (h : hist) (v : val) => EX z : Z, !!(repable_signed z /\ v = vint z) &&
          if eq_dec z 0 then R else emp).
      { entailer!. }
      { repeat (split; auto).
        intros ????????????? Ha.
        unfold lock_R in *.
        rewrite flatten_sepcon_in_SEP.
        rewrite extract_exists_in_SEP; Intro z'.
        rewrite <- flatten_sepcon_in_SEP.
        rewrite !sepcon_andp_prop', !sepcon_andp_prop.
        erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
        erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
        Intros; subst.
        eapply semax_pre, Ha; clear Ha.
        go_lowerx.
        rewrite andp_emp_dup at 1.
        Exists 1 z'; entailer!.
        { split; computable. }
        apply weak_precise_lock_R with (h := []). }
      Intros x z'; destruct x as (t, v); simpl in *.
      forward.
      go_lower.
      Exists z'; entailer!.
      unfold my_lock.
      Exists (h ++ [(t, AE (vint z') (vint 1))]); auto.
  - unfold MORE_COMMANDS, abbreviate; forward.
Qed.

Lemma body_my_release : semax_body Vprog Gprog f_my_release my_release_spec.
Proof.
  start_dep_function.
  simpl; destruct ts as (((sh, l), p), R).
  unfold my_lock; Intros h.
  forward_call (Tsh, sh, p, l, vint 1, vint 0, h, fun (h : hist) (v : val) => !!(v = vint 0) && R,
    lock_R R, fun (h : hist) (v : val) => EX z' : Z, !!(v = vint z' /\ repable_signed z' /\ z' <> 0) && emp).
  { entailer!. }
  { repeat (split; auto).
    intros ????????????? Ha.
    unfold lock_R in *.
    rewrite flatten_sepcon_in_SEP.
    rewrite extract_exists_in_SEP; Intro z'.
    rewrite <- flatten_sepcon_in_SEP.
    rewrite !sepcon_andp_prop', !sepcon_andp_prop.
    erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
    erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
    Intros; subst.
    eapply semax_pre, Ha; clear Ha.
    go_lowerx.
    destruct (eq_dec z' 0).
    { apply derives_trans with (Q0 := FF * TT); [|entailer!].
      apply sepcon_derives; [|auto].
      apply weak_precise_positive_conflict. }
    rewrite andp_emp_dup at 1.
    Exists 0 z'; rewrite eq_dec_refl; entailer!.
    { split; computable. }
    apply weak_precise_lock_R with (h := []). }
  Intros x z'; destruct x as (t, v); simpl in *.
  forward.
  unfold my_lock.
  Exists (h ++ [(t, AE (vint z') (vint 0))]); auto.
Qed.