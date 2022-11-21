Require Import VST.msl.predicates_hered.
Require Import VST.veric.ghosts.
Require Import VST.veric.invariants.
Require Import VST.veric.fupd.
Require Export VST.veric.slice.
Require Export VST.msl.iter_sepcon.
Require Import VST.msl.ageable.
Require Import VST.msl.age_sepalg.
Require Export VST.concurrency.semax_conc_pred.
Require Export VST.concurrency.semax_conc.
Require Export VST.floyd.proofauto.
Require Export VST.zlist.sublist.

Import FashNotation.
Import LiftNotation.
Import compcert.lib.Maps.

(* Require Export VST.concurrency.conclib_veric. *)

Notation vint z := (Vint (Int.repr z)).
Notation vptrofs z := (Vptrofs (Ptrofs.repr z)).

Open Scope logic.

Lemma wsat_fupd : forall E P Q, (wsat * P |-- |==> wsat * Q) -> P |-- fupd.fupd E E Q.
Proof.
  intros; unfold fupd.
  unseal_derives.
  rewrite <- predicates_sl.wand_sepcon_adjoint.
  rewrite <- predicates_sl.sepcon_assoc; eapply predicates_hered.derives_trans.
  { apply predicates_sl.sepcon_derives, predicates_hered.derives_refl.
    rewrite predicates_sl.sepcon_comm; apply H. }
  eapply predicates_hered.derives_trans; [apply own.bupd_frame_r | apply own.bupd_mono].
  apply predicates_hered.orp_right2.
  setoid_rewrite (predicates_sl.sepcon_comm _ Q).
  rewrite <- predicates_sl.sepcon_assoc; apply predicates_hered.derives_refl.
Qed.

Lemma wsat_alloc_dep : forall P, (wsat * ALL i, |> P i) |-- |==> wsat * EX i : _, invariant i (P i).
Proof.
  intros; unseal_derives; apply wsat_alloc_dep.
Qed.

Lemma wsat_alloc : forall P, wsat * |> P |-- |==> wsat * EX i : _, invariant i P.
Proof.
  intros; unseal_derives; apply wsat_alloc.
Qed.

Lemma wsat_alloc_strong : forall P Pi (Hfresh : forall n, exists i, (n <= i)%nat /\ Pi i),
  (wsat * |> P) |-- |==> wsat * EX i : _, !!(Pi i) && invariant i P.
Proof.
  intros; unseal_derives; apply wsat_alloc_strong; auto.
Qed.

Lemma inv_alloc_dep : forall E P, ALL i, |> P i |-- |={E}=> EX i : _, invariant i (P i).
Proof.
  intros.
  apply wsat_fupd, wsat_alloc_dep.
Qed.

Lemma inv_alloc : forall E P, |> P |-- |={E}=> EX i : _, invariant i P.
Proof.
  intros.
  apply wsat_fupd, wsat_alloc.
Qed.

Lemma inv_alloc_strong : forall E P Pi (Hfresh : forall n, exists i, (n <= i)%nat /\ Pi i),
  |> P |-- |={E}=> EX i : _, !!(Pi i) && invariant i P.
Proof.
  intros.
  apply wsat_fupd, wsat_alloc_strong; auto.
Qed.

Lemma inv_open : forall E i P, Ensembles.In E i ->
  invariant i P |-- |={E, Ensembles.Subtract E i}=> |> P * (|>P -* |={Ensembles.Subtract E i, E}=> emp).
Proof.
  intros; unseal_derives; apply inv_open; auto.
Qed.

Lemma inv_dealloc : forall i P, invariant i P |-- emp.
Proof.
  intros; unseal_derives; apply invariant_dealloc.
Qed.

Lemma fupd_timeless : forall E (P : mpred), timeless' P -> |> P |-- |={E}=> P.
Proof.
  intros; unseal_derives; apply fupd_timeless; auto.
Qed.

Ltac join_sub := repeat (eapply sepalg.join_sub_trans;
  [eexists; first [eassumption | simple eapply sepalg.join_comm; eassumption]|]); eassumption.

Ltac join_inj := repeat match goal with H1 : sepalg.join ?a ?b ?c, H2 : sepalg.join ?a ?b ?d |- _ =>
    pose proof (sepalg.join_eq H1 H2); clear H1 H2; subst; auto end.

Ltac fast_cancel := rewrite ?sepcon_emp, ?emp_sepcon; rewrite ?sepcon_assoc;
  repeat match goal with
    | |- ?P |-- ?P => apply derives_refl
    | |- ?P * _ |-- ?P * _ => apply sepcon_derives; [apply derives_refl|]
    | |- _ |-- ?P * _ => rewrite <- !sepcon_assoc, (sepcon_comm _ P), !sepcon_assoc end;
  try cancel_frame.

(*Ltac forward_malloc t n := forward_call (sizeof t); [simpl; try computable |
  Intros n; rewrite malloc_compat by (auto; reflexivity); Intros;
  rewrite memory_block_data_at_ by auto].
*)

Lemma semax_fun_id'' id f gv Espec {cs} Delta P Q R Post c :
  (var_types Delta) ! id = None ->
  (glob_specs Delta) ! id = Some f ->
  (glob_types Delta) ! id = Some (type_of_funspec f) ->
  snd (local2ptree Q) = Some gv ->
  @semax cs Espec Delta
    (PROPx P
      (LOCALx Q
      (SEPx ((func_ptr' f (gv id)) :: R)))) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros V G GS HGV SA.
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply SA; clear SA;
 intros; try apply ENTAIL_refl.
destruct (local2ptree Q) as [[[T1 T2] Res] GV] eqn:?H.
simpl in HGV; subst GV.
erewrite (local2ptree_soundness P) by eauto.
erewrite (local2ptree_soundness P) by eauto.
go_lowerx.
entailer.
  unfold func_ptr'.
  rewrite <- andp_left_corable by (apply corable_func_ptr).
  rewrite andp_comm; apply andp_derives; auto.
  erewrite <- gvars_eval_var; [apply derives_refl | eauto ..].
  pose proof LocalD_sound_gvars gv T1 T2 _ eq_refl.
  clear - H2 H3.
  revert H3.
  generalize (gvars gv).
  rewrite <- Forall_forall.
  induction (LocalD T1 T2 (Some gv)); [constructor |].
  simpl in H2.
  destruct H2; constructor; auto.
Qed.

Ltac get_global_function'' _f :=
eapply (semax_fun_id'' _f); try reflexivity.

(* legacy *)
Ltac start_dep_function := start_function.

(* automation for dependent funspecs moved to call_lemmas and forward.v*)

Lemma PROP_into_SEP : forall P Q R, PROPx P (LOCALx Q (SEPx R)) =
  PROPx [] (LOCALx Q (SEPx (!!fold_right and True P && emp :: R))).
Proof.
  intros; unfold PROPx, LOCALx, SEPx; extensionality; simpl.
  rewrite <- andp_assoc, (andp_comm _ (fold_right_sepcon R)), <- andp_assoc.
  rewrite prop_true_andp by auto.
  rewrite andp_comm; f_equal.
  rewrite andp_comm.
  rewrite sepcon_andp_prop', emp_sepcon; auto.
Qed.

Lemma PROP_into_SEP_LAMBDA : forall P U Q R, PROPx P (LAMBDAx U Q (SEPx R)) =
  PROPx [] (LAMBDAx U Q (SEPx (!!fold_right and True P && emp :: R))).
Proof.
  intros; unfold PROPx, LAMBDAx, GLOBALSx, LOCALx, SEPx, argsassert2assert;
  extensionality; simpl.
  apply pred_ext; entailer!; apply derives_refl.
Qed.

Ltac cancel_for_forward_spawn :=
  eapply symbolic_cancel_setup;
   [ construct_fold_right_sepcon
   | construct_fold_right_sepcon
   | fold_abnormal_mpred
   | cbv beta iota delta [before_symbol_cancel]; cancel_for_forward_call].

Ltac forward_spawn id arg wit :=
  match goal with gv : globals |- _ =>
  make_func_ptr id; let f := fresh "f_" in set (f := gv id);
  match goal with |- context[func_ptr' (NDmk_funspec _ _ (val * ?A) ?Pre _) f] =>
    let Q := fresh "Q" in let R := fresh "R" in

    evar (Q : A -> globals); evar (R : A -> val -> mpred);
    replace Pre with (fun '(a, w) => PROPx [] (PARAMSx (a::nil)
                                                       (GLOBALSx ((Q w) :: nil) (SEPx [R w a]))));
    [ | let x := fresh "x" in extensionality x; destruct x as (?, x);
        instantiate (1 := fun w a => _ w) in (value of R);
        repeat (destruct x as (x, ?);
        instantiate (1 := fun '(a, b) => _ a) in (value of Q);
        instantiate (1 := fun '(a, b) => _ a) in (value of R));
        etransitivity; [|symmetry; apply PROP_into_SEP_LAMBDA]; f_equal; f_equal; f_equal;
        [ instantiate (1 := fun _ => _) in (value of Q); subst Q; f_equal; simpl; reflexivity
        | unfold SEPx; extensionality; simpl; rewrite sepcon_emp;
          unfold R; instantiate (1 := fun _ => _);
          reflexivity]
  ];
  forward_call [A] funspec_sub_refl (f, arg, Q, wit, R); subst Q R;
           [ .. | subst f]; try (subst f; simpl; cancel_for_forward_spawn)
  end end.

#[export] Hint Resolve unreadable_bot : core.

(* The following lemma is used in atomics/verif_ptr_atomics.v which is
   not in the Makefile any more. So I comment out the
   lemma. Furthermore, it should be replaced by
   valid_pointer_is_pointer_or_null. *)

(* Lemma valid_pointer_isptr : forall v, valid_pointer v |-- !!(is_pointer_or_null v). *)
(* Proof. *)
(* Transparent mpred. *)
(* Transparent predicates_hered.pred. *)
(*   destruct v; simpl; try apply derives_refl. *)
(*   apply prop_right; auto. *)
(* Opaque mpred. Opaque predicates_hered.pred. *)
(* Qed. *)

(* #[export] Hint Resolve valid_pointer_isptr : saturate_local. *)

Definition exclusive_mpred P := P * P |-- FF.

Program Definition weak_exclusive_mpred (P: mpred): mpred :=
  unfash (fash ((P * P) --> FF)).

Lemma corable_weak_exclusive R : seplog.corable (weak_exclusive_mpred R).
Proof.
  apply assert_lemmas.corable_unfash, _.
Qed.

Lemma exclusive_mpred_nonexpansive : nonexpansive weak_exclusive_mpred.
Proof.
  unfold weak_exclusive_mpred, nonexpansive; intros.
  apply @subtypes.eqp_unfash, @subtypes.eqp_subp_subp, eqp_refl.
  apply eqp_sepcon; apply predicates_hered.derives_refl.
Qed.

Lemma exclusive_mpred_super_non_expansive:
  forall R n, compcert_rmaps.RML.R.approx n (weak_exclusive_mpred R) =
    compcert_rmaps.RML.R.approx n (weak_exclusive_mpred (compcert_rmaps.RML.R.approx n R)).
Proof.
  apply nonexpansive_super_non_expansive, exclusive_mpred_nonexpansive.
Qed.

Lemma exclusive_weak_exclusive1: forall R P,
  exclusive_mpred R ->
  P |-- weak_exclusive_mpred R.
Proof.
  intros; unfold weak_exclusive_mpred; unfold exclusive_mpred in H.
  unseal_derives; apply derives_unfash_fash; auto.
Qed.

Lemma exclusive_weak_exclusive: forall R,
  exclusive_mpred R ->
  emp |-- weak_exclusive_mpred R && emp.
Proof.
  intros; apply andp_right; auto; apply exclusive_weak_exclusive1; auto.
Qed.

Lemma weak_exclusive_conflict : forall P,
  (weak_exclusive_mpred P && emp) * P * P |-- FF.
Proof.
  intros.
  rewrite sepcon_assoc, <- andp_left_corable by (apply corable_weak_exclusive).
  unseal_derives; intros ? [].
  unfold weak_exclusive_mpred in H; specialize (H a ltac:(lia) _ _ (ageable.necR_refl _) (predicates_hered.ext_refl _)).
  apply H; auto.
Qed.

Lemma exclusive_sepcon1 : forall P Q (HP : exclusive_mpred P), exclusive_mpred (P * Q).
Proof.
  unfold exclusive_mpred; intros.
  eapply derives_trans, sepcon_FF_derives' with (P := Q * Q), HP; cancel; apply derives_refl.
Qed.

Lemma exclusive_sepcon2 : forall P Q (HP : exclusive_mpred Q), exclusive_mpred (P * Q).
Proof.
  intros; rewrite sepcon_comm; apply exclusive_sepcon1; auto.
Qed.

Lemma exclusive_andp1 : forall P Q (HP : exclusive_mpred P), exclusive_mpred (P && Q).
Proof.
  unfold exclusive_mpred; intros.
  eapply derives_trans, HP.
  apply sepcon_derives; apply andp_left1; auto.
Qed.

Lemma exclusive_andp2 : forall P Q (HQ : exclusive_mpred Q), exclusive_mpred (P && Q).
Proof.
  intros; rewrite andp_comm; apply exclusive_andp1; auto.
Qed.

Lemma exclusive_FF : exclusive_mpred FF.
Proof.
  unfold exclusive_mpred.
  rewrite FF_sepcon; auto.
Qed.

Lemma derives_exclusive : forall P Q (Hderives : P |-- Q) (HQ : exclusive_mpred Q),
  exclusive_mpred P.
Proof.
  unfold exclusive_mpred; intros.
  eapply derives_trans, HQ.
  apply sepcon_derives; auto.
Qed.

Lemma mapsto_exclusive : forall (sh : Share.t) (t : type) (v : val),
  sepalg.nonunit sh -> exclusive_mpred (EX v2 : _, mapsto sh t v v2).
Proof.
  intros; unfold exclusive_mpred.
  Intros v1 v2; apply mapsto_conflict; auto.
Qed.

Lemma field_at__exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) (p : val),
  sepalg.nonidentity sh ->
  0 < sizeof (nested_field_type t fld) -> exclusive_mpred (field_at_ sh t fld p).
Proof.
  intros; apply field_at__conflict; auto.
Qed.

Lemma ex_field_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) (p : val),
  sepalg.nonidentity sh ->
  0 < sizeof (nested_field_type t fld) -> exclusive_mpred (EX v : _, field_at sh t fld v p).
Proof.
  intros; unfold exclusive_mpred.
  Intros v v'; apply field_at_conflict; auto.
Qed.

Corollary field_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) v (p : val),
  sepalg.nonidentity sh -> 0 < sizeof (nested_field_type t fld) -> exclusive_mpred (field_at sh t fld v p).
Proof.
  intros; eapply derives_exclusive, ex_field_at_exclusive; eauto.
  Exists v; apply derives_refl.
Qed.

Lemma ex_data_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (EX v : _, data_at sh t v p).
Proof.
  intros; unfold exclusive_mpred.
  Intros v v'; apply data_at_conflict; auto.
Qed.

Corollary data_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) v (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (data_at sh t v p).
Proof.
  intros; eapply derives_exclusive, ex_data_at_exclusive; eauto.
  Exists v; apply derives_refl.
Qed.

Corollary data_at__exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (data_at_ sh t p).
Proof.
  intros; eapply derives_exclusive, data_at_exclusive; eauto.
  apply data_at__data_at; eauto.
Qed.


