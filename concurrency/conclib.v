Require Import VST.msl.predicates_hered.
Require Import VST.veric.ghosts.
Require Import VST.veric.invariants.
Require Import VST.veric.fupd.
Require Export VST.msl.iter_sepcon.
Require Import VST.msl.ageable.
Require Import VST.msl.age_sepalg.
Require Export VST.concurrency.semax_conc_pred.
Require Export VST.concurrency.semax_conc.
Require Export VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Export VST.zlist.sublist.
Import FashNotation.
Import LiftNotation.
Import compcert.lib.Maps.

Require Export VST.concurrency.conclib_coqlib.
Require Export VST.concurrency.conclib_sublist.
Require Export VST.concurrency.conclib_veric.

(*Lemma cond_var_isptr : forall {cs} sh v, @cond_var cs sh v = !! isptr v && cond_var sh v.
Proof.
  intros; apply data_at__isptr.
Qed.
#[export] Hint Resolve lock_inv_isptr cond_var_isptr : saturate_local.

Lemma cond_var_share_join : forall {cs} sh1 sh2 sh v (Hjoin : sepalg.join sh1 sh2 sh),
  @cond_var cs sh1 v * cond_var sh2 v = cond_var sh v.
Proof.
  intros; unfold cond_var; apply data_at__share_join; auto.
Qed.*)

(* Sometimes, in order to prove precise, we actually need to know that the data is the same as well. *)
(* Do we still need this? Probably not.
Lemma mapsto_inj : forall sh t v1 v2 p r1 r2 r
  (Hsh : readable_share sh)
  (Hp1 : predicates_hered.app_pred (mapsto sh t p v1) r1)
  (Hp2 : predicates_hered.app_pred (mapsto sh t p v2) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hdef1 : v1 <> Vundef) (Hdef2 : v2 <> Vundef),
  r1 = r2 /\ v1 = v2.
Proof.
  unfold mapsto; intros.
  destruct (access_mode t); try contradiction.
  destruct (type_is_volatile t); [contradiction|].
  destruct p; try contradiction.
  destruct (readable_share_dec sh); [|contradiction n; auto].
  destruct Hp1 as [(? & ?) | (? & ?)]; [|contradiction Hdef1; auto].
  destruct Hp2 as [(? & ?) | (? & ?)]; [|contradiction Hdef2; auto].
  assert (r1 = r2); [|split; auto].
  - eapply ex_address_mapsto_precise; eauto; eexists; eauto.
  - subst; eapply res_predicates.address_mapsto_value_cohere'; eauto.
Qed.

Lemma data_at_int_array_inj : forall {cs} sh z a1 a2 p r1 r2 r
  (Hsh : readable_share sh)
  (Hp1 : predicates_hered.app_pred (@data_at_rec cs sh (tarray tint z) a1 p) r1)
  (Hp2 : predicates_hered.app_pred (@data_at_rec cs sh (tarray tint z) a2 p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hdef1 : Forall (fun v => v <> Vundef) a1) (Hdef2 : Forall (fun v => v <> Vundef) a2)
  (Hlen1 : Zlength a1 = z) (Hlen2 : Zlength a2 = z),
  r1 = r2 /\ a1 = a2.
Proof.
  intros until z.
  remember (Z.to_nat z) as l; revert dependent z.
  induction l; intros.
  - destruct a1; [|rewrite <- Hlen1, Zlength_cons, Zlength_correct, Z2Nat.inj_succ in Heql; lia].
    rewrite Zlength_nil in Hlen1.
    destruct a2; [split; auto | rewrite Zlength_cons, Zlength_correct in Hlen2; lia].
    rewrite <- Hlen1 in *.
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite array_pred_len_0 in Hp1, Hp2; auto.
    apply sepalg.same_identity with (a := r); auto.
    + destruct Hr1 as (? & H); specialize (Hp1 _ _ H); subst; auto.
    + destruct Hr2 as (? & H); specialize (Hp2 _ _ H); subst; auto.
  - destruct a1 as [|x1 l1].
    { rewrite <- Hlen1, Zlength_nil in Heql; discriminate. }
    destruct a2 as [|x2 l2].
    { rewrite <- Hlen2, Zlength_nil in Heql; discriminate. }
    unfold tarray in *.
    rewrite Zlength_cons in *.
    assert (0 <= 1 <= z).
    { rewrite Zlength_correct in *; lia. }
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite split_array_pred with (mid := 1) in Hp1; auto; [| rewrite Z.max_r by lia; auto | rewrite Z.max_r by lia; rewrite Zlength_cons; lia].
    rewrite split_array_pred with (mid := 1) in Hp2; auto; [| rewrite Z.max_r by lia; auto | rewrite Z.max_r by lia; rewrite Zlength_cons; lia].
    destruct Hp1 as (r1a & ? & ? & Hh1 & Ht1), Hp2 as (r2a & ? & ? & Hh2 & Ht2).
    repeat rewrite Z.sub_0_r in *.
    rewrite sublist_one, array_pred_len_1 in Hh1, Hh2; auto; try rewrite Zlength_cons; try lia.
    rewrite sublist_1_cons in Ht1, Ht2.
    unfold Znth in *; simpl in *.
    unfold at_offset in Hh1, Hh2.
    assert (Zlength l1 = z - 1) by lia.
    assert (Zlength l2 = z - 1) by lia.
    rewrite sublist_same in Ht1, Ht2; try rewrite Z.max_r by lia; auto.
    inv Hdef1; inv Hdef2.
    exploit (IHl (Zlength l1)); try assumption.
    { subst.
      rewrite Z2Nat.inj_succ in *; lia. }
    { rewrite data_at_rec_eq; simpl.
      instantiate (2 := offset_val 4 p).
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l1).
      erewrite array_pred_shift; try simple apply Ht1;
      try rewrite !Z.max_r by lia; auto; try lia.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; lia. }
    { rewrite data_at_rec_eq; simpl.
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l2).
      erewrite array_pred_shift; try simple apply Ht2;
      try rewrite !Z.max_r by lia;
      auto; try lia.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; lia. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { auto. }
    { auto. }
    { auto. }
    { lia. }
    intros (? & ?); subst.
    rewrite by_value_data_at_rec_nonvolatile in Hh1, Hh2; auto.
    exploit (mapsto_inj sh tint x1 x2); eauto.
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    intros (? & ?); subst.
    split; [eapply sepalg.join_eq|]; auto.
Qed.

Lemma data_at_ptr_array_inj : forall {cs} sh t z a1 a2 p r1 r2 r
  (Hsh : readable_share sh)
  (Hp1 : predicates_hered.app_pred (@data_at_rec cs sh (tarray (tptr t) z) a1 p) r1)
  (Hp2 : predicates_hered.app_pred (@data_at_rec cs sh (tarray (tptr t) z) a2 p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hdef1 : Forall (fun v => v <> Vundef) a1) (Hdef2 : Forall (fun v => v <> Vundef) a2)
  (Hlen1 : Zlength a1 = z) (Hlen2 : Zlength a2 = z),
  r1 = r2 /\ a1 = a2.
Proof.
  intros until z.
  remember (Z.to_nat z) as l; revert dependent z.
  induction l; intros.
  - destruct a1; [|rewrite <- Hlen1, Zlength_cons, Zlength_correct, Z2Nat.inj_succ in Heql; lia].
    rewrite Zlength_nil in Hlen1.
    destruct a2; [split; auto | rewrite Zlength_cons, Zlength_correct in Hlen2; lia].
    rewrite <- Hlen1 in *.
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite array_pred_len_0 in Hp1, Hp2; auto.
    apply sepalg.same_identity with (a := r); auto.
    + destruct Hr1 as (? & H); specialize (Hp1 _ _ H); subst; auto.
    + destruct Hr2 as (? & H); specialize (Hp2 _ _ H); subst; auto.
  - destruct a1 as [|x1 l1].
    { rewrite <- Hlen1, Zlength_nil in Heql; discriminate. }
    destruct a2 as [|x2 l2].
    { rewrite <- Hlen2, Zlength_nil in Heql; discriminate. }
    unfold tarray in *.
    rewrite Zlength_cons in *.
    assert (0 <= 1 <= z).
    { rewrite Zlength_correct in *; lia. }
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite split_array_pred with (mid := 1) in Hp1; auto; [| rewrite Z.max_r by lia; auto | rewrite Z.max_r by lia; rewrite Zlength_cons; lia].
    rewrite split_array_pred with (mid := 1) in Hp2; auto; [| rewrite Z.max_r by lia; auto | rewrite Z.max_r by lia; rewrite Zlength_cons; lia].
    destruct Hp1 as (r1a & ? & ? & Hh1 & Ht1), Hp2 as (r2a & ? & ? & Hh2 & Ht2).
    repeat rewrite Z.sub_0_r in *.
    rewrite sublist_one, array_pred_len_1 in Hh1, Hh2; auto; try rewrite Zlength_cons; try lia.
    rewrite sublist_1_cons in Ht1, Ht2.
    unfold Znth in *; simpl in *.
    unfold at_offset in Hh1, Hh2.
    assert (Zlength l1 = z - 1) by lia.
    assert (Zlength l2 = z - 1) by lia.
    rewrite sublist_same in Ht1, Ht2; try rewrite Z.max_r by lia; auto.
    inv Hdef1; inv Hdef2.
    exploit (IHl (Zlength l1)); try assumption.
    { subst.
      rewrite Z2Nat.inj_succ in *; lia. }
    { rewrite data_at_rec_eq; simpl.
      instantiate (2 := offset_val 4 p).
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l1).
      erewrite array_pred_shift; try simple apply Ht1;
      try rewrite !Z.max_r by lia; auto; try lia.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; lia. }
    { rewrite data_at_rec_eq; simpl.
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l2).
      erewrite array_pred_shift; try simple apply Ht2;
      try rewrite !Z.max_r by lia; auto; try lia.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; lia. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { auto. }
    { auto. }
    { auto. }
    { lia. }
    intros (? & ?); subst.
    rewrite by_value_data_at_rec_nonvolatile in Hh1, Hh2; auto.
    exploit (mapsto_inj sh (tptr t) x1 x2); eauto.
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    intros (? & ?); subst.
    split; [eapply sepalg.join_eq|]; auto.
Qed. *)

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

(* shares *)
(*Lemma LKspec_readable lock_size :
  0 < lock_size ->
  forall R sh p, predicates_hered.derives (res_predicates.LKspec lock_size R sh p)
  (!!(readable_share sh)).
Proof.
  intros pos R sh p a H.
  specialize (H p); simpl in H.
  destruct (adr_range_dec p lock_size p).
  destruct (eq_dec p p); [|contradiction n; auto].
  destruct H; auto.
  { contradiction n; unfold adr_range.
    destruct p; split; auto.
    lia. }
Qed.

Lemma lock_inv_share_join : forall sh1 sh2 sh v R (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2)
  (Hjoin : sepalg.join sh1 sh2 sh),
  lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R.
Proof.
  intros; unfold lock_inv.
  rewrite exp_sepcon1; f_equal; extensionality b.
  rewrite exp_sepcon1; f_equal; extensionality o.
  destruct v; try solve [repeat rewrite prop_false_andp; try discriminate; rewrite FF_sepcon; auto].
  destruct (eq_dec b0 b); [|repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n; auto);
    rewrite FF_sepcon; auto].
  destruct (eq_dec i o); [subst | repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n; auto);
    rewrite FF_sepcon; auto].
  repeat rewrite prop_true_andp; auto.
  evar (P : mpred); replace (exp _) with P.
  - subst P; apply slice.LKspec_share_join; eauto.
  - subst P.
    erewrite exp_uncurry, exp_congr, <- exp_andp1, exp_prop, prop_true_andp; eauto.
    { instantiate (1 := fun x => Vptr b o = Vptr (fst x) (snd x)); exists (b, o); auto. }
    intros (?, ?); simpl.
    destruct (eq_dec b0 b); [subst |
      repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n); auto].
    destruct (eq_dec i o); [|repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n); auto].
    subst; repeat rewrite prop_true_andp; auto.
Qed.*)

(*Ltac lock_props := rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
  [repeat apply andp_right; auto; eapply derives_trans;
   try (apply exclusive_weak_exclusive || (apply rec_inv_weak_rec_inv; try apply selflock_rec)); auto with share exclusive |
   try timeout 20 cancel].*)

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

(* Notations for dependent funspecs *)
Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) cc_default A
  (fun (ts: list Type) (x: t1*t2) =>
     match x with (x1,x2) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2) =>
     match x with (x1,x2) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2) =>
     match x with (x1,x2) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2) =>
     match x with (x1,x2) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3) =>
     match x with (x1,x2,x3) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3) =>
     match x with (x1,x2,x3) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3) =>
     match x with (x1,x2,x3) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3) =>
     match x with (x1,x2,x3) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4) =>
     match x with (x1,x2,x3,x4) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4) =>
     match x with (x1,x2,x3,x4) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5) =>
     match x with (x1,x2,x3,x4,x5) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5) =>
     match x with (x1,x2,x3,x4,x5) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6) =>
     match x with (x1,x2,x3,x4,x5,x6) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6) =>
     match x with (x1,x2,x3,x4,x5,x6) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7) =>
     match x with (x1,x2,x3,x4,x5,x6,x7) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7) =>
     match x with (x1,x2,x3,x4,x5,x6,x7) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0,
             P at level 100, Q at level 100).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%type .. (cons v%type nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => P%argsassert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0, x13 at level 0, x14 at level 0,
             P at level 100, Q at level 100).

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
        | unfold SEPx; extensionality; simpl; rewrite sepcon_emp; instantiate (1 := fun _ => _);
          reflexivity]
  ];
  forward_call [A] funspec_sub_refl (f, arg, Q, wit, R); subst Q R;
           [ .. | subst f]; try (subst f; simpl; cancel_for_forward_spawn)
  end end.
(*
Ltac forward_spawn id arg wit :=
  match goal with gv : globals |- _ =>
  make_func_ptr id; let f := fresh "f_" in set (f := gv id);
  match goal with |- context[func_ptr' (NDmk_funspec _ _ (val * ?A) ?Pre _) f] =>
    let y := fresh "y" in let Q := fresh "Q" in let R := fresh "R" in
    evar (y : ident); evar (Q : A -> globals); evar (R : A -> val -> mpred);
    (*replace Pre with (fun '(a, w) => PROPx [] (LOCALx (temp y a :: gvars (Q w) :: nil) (SEPx [R w a])));*)
    replace Pre with (fun '(a, w) => PROPx [] (LAMBDAx ((Q w) :: nil) (a:: nil) (SEPx [R w a])));
    [|let x := fresh "x" in extensionality x; destruct x as (?, x);
      instantiate (1 := fun w a => _ w) in (value of R);
      repeat (destruct x as (x, ?);
        instantiate (1 := fun '(a, b) => _ a) in (value of Q);
        instantiate (1 := fun '(a, b) => _ a) in (value of R));
      etransitivity; [|symmetry; apply PROP_into_SEP]; f_equal; f_equal ; [instantiate (1 := fun _ => _) in (value of Q); subst y Q; f_equal; simpl; f_equal |
       unfold SEPx; extensionality; simpl; rewrite sepcon_emp; instantiate (1 := fun _ => _); reflexivity]];
  forward_call [A] funspec_sub_refl (f, arg, Q, wit, R); subst Q R; [ .. | subst y f]; try (Exists y; subst y f; simpl; cancel_for_forward_spawn) end end.*)
