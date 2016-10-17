Require Export msl.predicates_sl.
Require Import concurrency.semax_conc.
Require Import floyd.proofauto.

Lemma precise_sepcon : forall (P Q : mpred) (HP : precise P) (HQ : precise Q), precise (P * Q).
Proof.
  unfold precise; intros ??????? (l1 & r1 & Hjoin1 & HP1 & HQ1) (l2 & r2 & Hjoin2 & HP2 & HQ2)
    Hsub1 Hsub2.
  specialize (HP w _ _ HP1 HP2); specialize (HQ w _ _ HQ1 HQ2).
  rewrite HP, HQ in Hjoin1.
  eapply sepalg.join_eq; eauto.
  - apply sepalg.join_sub_trans with (b := w1); auto.
    eapply sepalg.join_join_sub'; eauto.
  - apply sepalg.join_sub_trans with (b := w2); auto.
    eapply sepalg.join_join_sub'; eauto.
  - apply sepalg.join_sub_trans with (b := w1); auto.
    eapply sepalg.join_join_sub; eauto.
  - apply sepalg.join_sub_trans with (b := w2); auto.
    eapply sepalg.join_join_sub; eauto.
Qed.

Lemma precise_andp1 : forall P Q (HP : precise P), precise (P && Q).
Proof.
  intros ?????? (? & ?) (? & ?) ??; eauto.
Qed.

Lemma precise_andp2 : forall P Q (HQ : precise Q), precise (P && Q).
Proof.
  intros ?????? (? & ?) (? & ?) ??; eauto.
Qed.

Lemma ex_address_mapsto_precise: forall ch rsh sh l,
  precise (EX v : val, res_predicates.address_mapsto ch v rsh sh l).
Proof.
  intros.
  eapply derives_precise, res_predicates.VALspec_range_precise.
  repeat intro.
  destruct H.
  eapply res_predicates.address_mapsto_VALspec_range; eauto.
Qed.

Lemma mapsto_undef_precise : forall sh t b o (Hsh : readable_share sh)
  (Hval : type_is_by_value t = true) (Hvol : type_is_volatile t = false),
  precise (mapsto sh t (Vptr b o) Vundef).
Proof.
  intros; unfold mapsto.
  destruct (access_mode_by_value _ Hval) as (? & Heq); rewrite Heq, Hvol.
  destruct (readable_share_dec _); [|contradiction].
  pose proof (tc_val_Vundef t).
  intros ??? [(? & _) | (_ & HP1)] [(? & _) | (_ & HP2)]; normalize.
  eapply ex_address_mapsto_precise; eauto.
Qed.

Lemma lock_inv_precise : forall v sh R, precise (lock_inv sh v R).
Proof.
  intros ?????? (b1 & o1 & Hv1 & Hlock1) (b2 & o2 & Hv2 & Hlock2) ??.
  rewrite Hv2 in Hv1; inv Hv1.
  eapply res_predicates.LKspec_precise; eauto.
Qed.

Lemma lock_inv_positive : forall sh v R,
  positive_mpred (lock_inv sh v R).
Proof.
  repeat intro.
  destruct H as (b & o & Hv & Hlock).
  simpl in Hlock.
  specialize (Hlock (b, Int.unsigned o)).
  destruct (adr_range_dec (b, Int.unsigned o) res_predicates.lock_size (b, Int.unsigned o)).
  destruct (EqDec_address (b, Int.unsigned o) (b, Int.unsigned o)); [|contradiction n; auto].
  destruct Hlock; eauto 6.
  { contradiction n; unfold adr_range, res_predicates.lock_size; split; auto; omega. }
Qed.

Lemma selflock_precise : forall R sh v, precise R ->
  precise (selflock R v sh).
Proof.
  intros.
  rewrite selflock_eq.
  apply precise_sepcon; auto.
  apply lock_inv_precise.
Qed.

Lemma positive_sepcon1 : forall P Q (HP : positive_mpred P),
  positive_mpred (P * Q).
Proof.
  repeat intro.
  destruct H as (? & ? & ? & HP1 & ?).
  specialize (HP _ HP1).
  destruct HP as (l & sh & rsh & k & p & HP).
  apply compcert_rmaps.RML.resource_at_join with (loc := l) in H.
  rewrite HP in H; inversion H; eauto 6.
Qed.

Lemma positive_sepcon2 : forall P Q (HQ : positive_mpred Q),
  positive_mpred (P * Q).
Proof.
  repeat intro.
  destruct H as (? & ? & ? & ? & HQ1).
  specialize (HQ _ HQ1).
  destruct HQ as (l & sh & rsh & k & p & HQ).
  apply compcert_rmaps.RML.resource_at_join with (loc := l) in H.
  rewrite HQ in H; inversion H; eauto 6.
Qed.

Lemma selflock_positive : forall R sh v, positive_mpred R ->
  positive_mpred (selflock R v sh).
Proof.
  intros.
  rewrite selflock_eq.
  apply positive_sepcon1; auto.
Qed.

Lemma later_positive : forall P, positive_mpred P -> positive_mpred (|> P)%logic.
Proof.
  admit.
Admitted.

Lemma semax_fun_id'' id f Espec {cs} Delta P Q R Post c :
  (var_types Delta) ! id = None ->
  (glob_specs Delta) ! id = Some f ->
  (glob_types Delta) ! id = Some (type_of_funspec f) ->
  @semax cs Espec Delta
    (EX v : val, PROPx P
      (LOCALx (gvar id v :: Q)
      (SEPx ((func_ptr' f v) :: R)))) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros V G GS SA.
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply SA; [ clear SA |
  intros; simpl; unfold local, lift1; entailer! ].
go_lowerx.
apply exp_right with (eval_var id (type_of_funspec f) rho).
entailer.
apply andp_right.
- (* about gvar *)
  apply prop_right.
  unfold gvar_denote, eval_var, Map.get.
  destruct H as (_ & _ & DG & DS).
  destruct (DS id _ GS) as [-> | (t & E)]; [ | congruence].
  destruct (DG id _ GS) as (? & -> & ?); auto.
- (* about func_ptr/func_ptr' *)
  unfold func_ptr'.
  rewrite <- andp_left_corable, andp_comm; auto.
  apply corable_func_ptr.
Qed.

Ltac get_global_function'' _f :=
eapply (semax_fun_id'' _f); try reflexivity.

Lemma LKspec_nonunit : forall R rsh sh p, predicates_hered.derives (res_predicates.LKspec R rsh sh p)
  (!!(sepalg.nonunit sh)).
Proof.
  repeat intro.
  specialize (H p); simpl in H.
  destruct (adr_range_dec p res_predicates.lock_size p).
  destruct (EqDec_address p p).
  destruct H; auto.
  { contradiction n; auto. }
  { contradiction n; unfold adr_range.
    destruct p; split; auto.
    unfold res_predicates.lock_size; omega. }
Qed.

Lemma lock_inv_join : forall sh1 sh2 sh v R (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2)
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
  - subst P; apply res_predicates.LKspec_share_join; auto.
    + apply readable_share_unrel_Rsh; auto.
    + apply readable_share_unrel_Rsh; eauto.
    + apply Share.unrel_join; eauto.
    + apply Share.unrel_join; eauto.
  - subst P.
    erewrite exp_uncurry, exp_congr, <- exp_andp1, exp_prop, prop_true_andp; eauto.
    { instantiate (1 := fun x => Vptr b o = Vptr (fst x) (snd x)); exists (b, o); auto. }
    intros (?, ?); simpl.
    destruct (eq_dec b0 b); [subst |
      repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n); auto].
    destruct (eq_dec i o); [|repeat rewrite prop_false_andp; try (intro X; inv X; contradiction n); auto].
    subst; repeat rewrite prop_true_andp; auto.
Qed.

Lemma split_readable_share sh :
  readable_share sh ->
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 sh.
Admitted.

Lemma split_Ews :
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 Ews.
Proof.
  apply split_readable_share; auto.
Qed.

Lemma emp_almost_empty : forall phi, predicates_hered.app_pred emp phi -> juicy_machine.almost_empty phi.
Proof.
  intros ? Hp ????? Hr ??; subst.
  pose proof (compcert_rmaps.RML.resource_at_identity _ loc Hp) as H.
  rewrite Hr in H.
  destruct (compcert_rmaps.RML.identity_NO _ H) as [|(? & ? & ?)]; discriminate.
Qed.

Lemma lock_inv_almost_empty : forall sh v R phi, predicates_hered.app_pred (lock_inv sh v R) phi ->
  juicy_machine.almost_empty phi.
Proof.
  intros ???? (b & o & ? & Hp) ????? Hr ??; subst.
  specialize (Hp loc); simpl in Hp.
  destruct (adr_range_dec _ _ _).
  - destruct (EqDec_address _ _); destruct Hp as (? & Hp); rewrite Hp in Hr; inv Hr.
  - rewrite Hr in Hp; destruct (compcert_rmaps.RML.identity_NO _ Hp) as [|(? & ? & ?)]; discriminate.
Qed.

Lemma almost_empty_join : forall phi1 phi2 phi
  (Hphi1 : juicy_machine.almost_empty phi1)
  (Hphi2 : juicy_machine.almost_empty phi2)
  (Hjoin : sepalg.join phi1 phi2 phi),
  juicy_machine.almost_empty phi.
Proof.
  repeat intro.
  apply compcert_rmaps.RML.resource_at_join with (loc := loc) in Hjoin.
  rewrite H in Hjoin; inv Hjoin.
  - eapply Hphi1; eauto.
  - eapply Hphi2; eauto.
  - eapply Hphi1; eauto.
Qed.

Lemma cond_var_precise : forall {cs} sh b o, readable_share sh ->
  precise (@cond_var cs sh (Vptr b o)).
Proof.
  intros; unfold cond_var, data_at_, field_at_, field_at, at_offset; simpl.
  apply precise_andp2.
  rewrite data_at_rec_eq; simpl.
  apply mapsto_undef_precise; auto.
Qed.

Lemma lock_inv_isptr : forall sh v R, lock_inv sh v R = !!isptr v && lock_inv sh v R.
Proof.
  intros.
  eapply local_facts_isptr with (P := fun v => lock_inv sh v R); eauto.
  unfold lock_inv; Intros b o.
  subst; simpl; entailer.
Qed.

Lemma cond_var_isptr : forall {cs} sh v, @cond_var cs sh v = !! isptr v && cond_var sh v.
Proof.
  intros; apply data_at__isptr.
Qed.

Lemma cond_var_almost_empty : forall {cs} sh v phi, predicates_hered.app_pred (@cond_var cs sh v) phi ->
  juicy_machine.almost_empty phi.
Proof.
  intros ???? Hp ????? Hr ??; subst.
  unfold cond_var in Hp.
  destruct Hp as (? & Hp); simpl in Hp.
  rewrite data_at_rec_eq in Hp; unfold at_offset in Hp; simpl in Hp.
  unfold mapsto in Hp; simpl in Hp.
  destruct v; try contradiction; simpl in Hp.
  destruct (readable_share_dec sh).
  destruct Hp as [(? & ?) | (? & ? & ? & ? & Hp)]; [contradiction|].
  simpl in Hp.
  specialize (Hp loc).
  destruct (adr_range_dec _ _ _).
  - destruct Hp as (? & Hp); rewrite Hp in Hr; inv Hr.
Admitted.
(* This is currently untrue, since cond_vars are data. On the other hand, we don't want them to be locks,
   because that means something in the underlying model. Eventually we should figure something out for this. *)

Lemma cond_var_join : forall {cs} sh1 sh2 sh v (Hjoin : sepalg.join sh1 sh2 sh),
  @cond_var cs sh1 v * cond_var sh2 v = cond_var sh v.
Proof.
  intros; unfold cond_var; apply data_at__share_join; auto.
Qed.

Definition complete MAX l := l ++ repeat (Vint (Int.repr 0)) (MAX - length l).

Lemma upd_complete : forall l x MAX, (length l < MAX)%nat -> 
  upd_Znth (Zlength l) (complete MAX l) x = complete MAX (l ++ [x]).
Proof.
  intros; unfold complete.
  rewrite upd_Znth_app2, Zminus_diag.
  rewrite app_length; simpl plus.
  destruct (MAX - length l)%nat eqn: Hminus; [omega|].
  replace (MAX - (length l + 1))%nat with n by omega.
  unfold upd_Znth, sublist.sublist; simpl.
  rewrite Zlength_cons.
  unfold Z.succ; rewrite Z.add_simpl_r.
  rewrite Zlength_correct, Nat2Z.id, firstn_exact_length.
  rewrite <- app_assoc; auto.
  { repeat rewrite Zlength_correct; omega. }
Qed.

Lemma Znth_complete : forall n l d MAX, n < Zlength l -> Znth n (complete MAX l) d = Znth n l d.
Proof.
  intros; apply app_Znth1; auto.
Qed.

Lemma remove_complete : forall l x MAX, (length l < MAX)%nat -> 
  upd_Znth (Zlength l) (complete MAX (l ++ [x])) (Vint (Int.repr 0)) = complete MAX l.
Proof.
  intros; unfold complete.
  rewrite upd_Znth_app1; [|repeat rewrite Zlength_correct; rewrite app_length; simpl; Omega0].
  rewrite app_length; simpl plus.
  rewrite upd_Znth_app2, Zminus_diag; [|rewrite Zlength_cons; simpl; omega].
  unfold upd_Znth, sublist.sublist.
  rewrite Zminus_diag; simpl firstn.
  destruct (MAX - length l)%nat eqn: Hminus; [omega|].
  replace (MAX - (length l + 1))%nat with n by omega.
  simpl.
  rewrite <- app_assoc; auto.
Qed.

Lemma Forall_app : forall A (P : A -> Prop) l1 l2,
  Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  induction l1; split; auto; intros.
  - destruct H; auto.
  - inversion H as [|??? H']; subst.
    rewrite IHl1 in H'; destruct H'; split; auto.
  - destruct H as (H & ?); inv H; constructor; auto.
    rewrite IHl1; split; auto.
Qed.

Lemma repeat_plus : forall A (x : A) i j, repeat x (i + j) = repeat x i ++ repeat x j.
Proof.
  induction i; auto; simpl; intro.
  rewrite IHi; auto.
Qed.

Definition remove_at {A} i (l : list A) := firstn i l ++ skipn (S i) l.

Lemma upd_Znth_cons : forall {A} i a l (x : A), i > 0 ->
  upd_Znth i (a :: l) x = a :: upd_Znth (i - 1) l x.
Proof.
  intros; unfold upd_Znth, sublist.sublist; simpl.
  repeat rewrite Z.sub_0_r.
  destruct (Z.to_nat i) eqn: Hi.
  { exploit Z2Nat_inj_0; eauto; omega. }
  rewrite Zlength_cons; repeat rewrite Z2Nat.inj_add; try omega.
  repeat rewrite Z2Nat.inj_sub; try omega.
  rewrite Hi; simpl.
  rewrite Nat.sub_0_r.
  do 4 f_equal.
  rewrite Z2Nat.inj_succ; [|rewrite Zlength_correct; omega].
  repeat rewrite Z2Nat.inj_add; try omega.
  rewrite Z2Nat.inj_sub; try omega.
  simpl plus; omega.
Qed.

Lemma Forall_firstn : forall {A} (P : A -> Prop) l i, Forall P l ->
  Forall P (firstn i l).
Proof.
  intros; rewrite Forall_forall in *.
  intros ? Hin; pose proof (firstn_In _ _ _ Hin); auto.
Qed.

Lemma Forall_skipn : forall {A} (P : A -> Prop) l i, Forall P l ->
  Forall P (skipn i l).
Proof.
  intros; rewrite Forall_forall in *.
  intros ? Hin; pose proof (skipn_In _ _ _ Hin); auto.
Qed.

Lemma Forall_sublist : forall {A} (P : A -> Prop) l i j, Forall P l ->
  Forall P (sublist.sublist i j l).
Proof.
  intros; unfold sublist.sublist.
  apply Forall_firstn; apply Forall_skipn; auto.
Qed.

Lemma Forall_upd_Znth : forall {A} (P : A -> Prop) x l i, Forall P l -> P x ->
  Forall P (upd_Znth i l x).
Proof.
  intros; unfold upd_Znth.
  rewrite Forall_app; split; [|constructor; auto]; apply Forall_sublist; auto.
Qed.

Lemma last_cons : forall {A} (d : A) l x, l <> [] -> last (x :: l) d = last l d.
Proof.
  intros.
  destruct l; auto.
  contradiction H; auto.
Qed.

Lemma nth_last : forall {A} (d : A) l, nth (length l - 1) l d = last l d.
Proof.
  induction l; auto.
  simpl nth.
  destruct (length l) eqn: Hlen.
  { destruct l; simpl in *; [auto | omega]. }
  rewrite last_cons; simpl in *; [|intro; subst; discriminate].
  rewrite NPeano.Nat.sub_0_r in IHl; auto.
Qed.

Lemma Znth_last : forall {A} l (d : A), Znth (Zlength l - 1) l d = last l d.
Proof.
  intros; unfold Znth.
  destruct (zlt (Zlength l - 1) 0).
  - destruct l; auto.
    rewrite Zlength_correct in *; simpl length in *.
    rewrite Nat2Z.inj_succ in *; omega.
  - rewrite Z2Nat.inj_sub; [|omega].
    rewrite Zlength_correct, Nat2Z.id; simpl.
    apply nth_last.
Qed.

Lemma sepcon_app : forall l1 l2, fold_right sepcon emp (l1 ++ l2) =
  fold_right sepcon emp l1 * fold_right sepcon emp l2.
Proof.
  induction l1; simpl; intros.
  - rewrite emp_sepcon; auto.
  - rewrite IHl1, sepcon_assoc; auto.
Qed.

Definition rotate {A} (l : list A) n m := skipn (m - n) l ++ firstn (m - n) l.

Lemma data_at_int_array_inj : forall {cs} sh z a1 a2 p r1 r2 r
  (Hsh : readable_share sh)
  (Hp1 : predicates_hered.app_pred (@data_at cs sh (tarray tint z) a1 p) r1)
  (Hp2 : predicates_hered.app_pred (@data_at cs sh (tarray tint z) a2 p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hdef1 : Forall (fun v => v <> Vundef) a1) (Hdef2 : Forall (fun v => v <> Vundef) a2),
  r1 = r2 /\ a1 = a2.
Proof.
  intros until z.
  remember (Z.to_nat z) as l; revert dependent z.
  induction l; intros.
  - destruct Hp1 as (Hf & (Hz1 & Hp1)), Hp2 as (_ & (Hz2 & Hp2)); simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite Z.sub_0_r in *.
    destruct a1.
    rewrite Zlength_nil in Hz1; rewrite <- Hz1 in Hz2.
    destruct a2.
    split; auto.
    assert (z = 0) by auto; subst; simpl in *.
    apply sepalg.same_identity with (a := r); auto.
    { destruct Hr1 as (? & H); specialize (Hp1 _ _ H); subst; auto. }
    { destruct Hr2 as (? & H); specialize (Hp2 _ _ H); subst; auto. }
    { rewrite Zlength_cons in Hz2; rewrite Zlength_correct in Hz2.
      assert (Z.succ (Z.of_nat (length a2)) = 0) by auto; omega. }
    { rewrite Zlength_cons in Hz1; rewrite Zlength_correct in Hz1.
      assert (Z.to_nat (Z.succ (Z.of_nat (length a1))) = Z.to_nat z)
        by (rewrite Hz1; auto).
      rewrite <- Heql, Z2Nat.inj_succ in *; omega. }
  - assert (z = Zlength a1) as Hlen1.
    { destruct Hp1 as (? & ? & ?).
      rewrite Z.sub_0_r in *; auto. }
    assert (z = Zlength a2) as Hlen2.
    { destruct Hp2 as (? & ? & ?).
      rewrite Z.sub_0_r in *; auto. }
    destruct a1 as [|x1 l1].
    { rewrite Zlength_nil in Hlen1; rewrite Hlen1 in Heql; discriminate. }
    destruct a2 as [|x2 l2].
    { rewrite Zlength_nil in Hlen2; rewrite Hlen2 in Heql; discriminate. }
    unfold tarray in *.
    rewrite Zlength_cons in *.
    assert (0 <= 1 <= z).
    { split; [omega|].
      destruct (Z_le_dec z 0); [|omega].
      destruct (eq_dec z 0); [subst; rewrite Zlength_correct in *; omega|].
      rewrite Z2Nat_neg in Heql; omega. }
    rewrite split2_data_at_Tarray with (t := tint)(n1 := 1)(v' := x1 :: l1)
      (v1 := [x1])(v2 := l1) in Hp1; auto.
    rewrite split2_data_at_Tarray with (t := tint)(n1 := 1)(v' := x2 :: l2)
      (v1 := [x2])(v2 := l2) in Hp2; auto.
    destruct Hp1 as (r1a & ? & ? & Hh1 & Ht1), Hp2 as (r2a & ? & ? & Hh2 & Ht2).
    inv Hdef1; inv Hdef2.
    unfold Z.succ in *; rewrite Z.add_simpl_r in *.
    exploit (IHl (Zlength l1)); try assumption.
    { rewrite Z2Nat.inj_add in *; simpl in *; omega. }
    { apply Ht1. }
    { apply Ht2. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { auto. }
    { auto. }
    intros (? & ?); subst.
    unfold data_at, field_at in Hh1, Hh2.
    rewrite data_at_rec_eq in Hh1, Hh2; simpl in Hh1, Hh2.
    unfold at_offset, array_pred, aggregate_pred.array_pred in Hh1, Hh2.
    simpl in Hh1, Hh2.
    destruct Hh1 as (? & ? & Hh1), Hh2 as (? & ? & Hh2).
    rewrite sepcon_emp, by_value_data_at_rec_nonvolatile in Hh1, Hh2; auto.
    unfold mapsto in *; simpl in *.
    destruct p; try contradiction; simpl in *.
    destruct (readable_share_dec sh); [|contradiction].
    destruct Hh1 as [(? & Hmaps1) | (? & ?)];
      [|unfold Znth in *; simpl in *; contradiction].
    destruct Hh2 as [(? & Hmaps2) | (? & ?)];
      [|unfold Znth in *; simpl in *; contradiction].
    assert (r1a = r2a).
    { eapply ex_address_mapsto_precise.
      { exists x1; eauto. }
      { exists x2; eauto. }
      { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
      { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. } }
    subst; split; [eapply sepalg.join_eq; auto|].
    f_equal.
    eapply res_predicates.address_mapsto_value_cohere'; eauto.
    { rewrite sublist_same; auto.
      rewrite Zlength_cons; auto. }
    { rewrite sublist_1_cons, sublist_same; auto.
      rewrite Hlen2; unfold Z.succ; apply Z.add_simpl_r. }
    { rewrite sublist_same; auto.
      rewrite Zlength_cons; auto. }
    { rewrite sublist_1_cons, sublist_same; auto.
      rewrite Hlen1; unfold Z.succ; apply Z.add_simpl_r. }
Qed.

Lemma data_at_ptr_array_inj : forall {cs} sh t z a1 a2 p r1 r2 r
  (Hsh : readable_share sh)
  (Hp1 : predicates_hered.app_pred (@data_at cs sh (tarray (tptr t) z) a1 p) r1)
  (Hp2 : predicates_hered.app_pred (@data_at cs sh (tarray (tptr t) z) a2 p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hdef1 : Forall (fun v => v <> Vundef) a1) (Hdef2 : Forall (fun v => v <> Vundef) a2),
  r1 = r2 /\ a1 = a2.
Proof.
  intros until z.
  remember (Z.to_nat z) as l; revert dependent z.
  induction l; intros.
  - destruct Hp1 as (Hf & (Hz1 & Hp1)), Hp2 as (_ & (Hz2 & Hp2)); simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite Z.sub_0_r in *.
    destruct a1.
    rewrite Zlength_nil in Hz1; rewrite <- Hz1 in Hz2.
    destruct a2.
    split; auto.
    assert (z = 0) by auto; subst; simpl in *.
    apply sepalg.same_identity with (a := r); auto.
    { destruct Hr1 as (? & H); specialize (Hp1 _ _ H); subst; auto. }
    { destruct Hr2 as (? & H); specialize (Hp2 _ _ H); subst; auto. }
    { rewrite Zlength_cons in Hz2; rewrite Zlength_correct in Hz2.
      assert (Z.succ (Z.of_nat (length a2)) = 0) by auto; omega. }
    { rewrite Zlength_cons in Hz1; rewrite Zlength_correct in Hz1.
      assert (Z.to_nat (Z.succ (Z.of_nat (length a1))) = Z.to_nat z)
        by (rewrite Hz1; auto).
      rewrite <- Heql, Z2Nat.inj_succ in *; omega. }
  - assert (z = Zlength a1) as Hlen1.
    { destruct Hp1 as (? & ? & ?).
      rewrite Z.sub_0_r in *; auto. }
    assert (z = Zlength a2) as Hlen2.
    { destruct Hp2 as (? & ? & ?).
      rewrite Z.sub_0_r in *; auto. }
    destruct a1 as [|x1 l1].
    { rewrite Zlength_nil in Hlen1; rewrite Hlen1 in Heql; discriminate. }
    destruct a2 as [|x2 l2].
    { rewrite Zlength_nil in Hlen2; rewrite Hlen2 in Heql; discriminate. }
    unfold tarray in *.
    rewrite Zlength_cons in *.
    assert (0 <= 1 <= z).
    { split; [omega|].
      destruct (Z_le_dec z 0); [|omega].
      destruct (eq_dec z 0); [subst; rewrite Zlength_correct in *; omega|].
      rewrite Z2Nat_neg in Heql; omega. }
    rewrite split2_data_at_Tarray with (t0 := tptr t)(n1 := 1)(v' := x1 :: l1)
      (v1 := [x1])(v2 := l1) in Hp1; auto.
    rewrite split2_data_at_Tarray with (t0 := tptr t)(n1 := 1)(v' := x2 :: l2)
      (v1 := [x2])(v2 := l2) in Hp2; auto.
    destruct Hp1 as (r1a & ? & ? & Hh1 & Ht1), Hp2 as (r2a & ? & ? & Hh2 & Ht2).
    inv Hdef1; inv Hdef2.
    unfold Z.succ in *; rewrite Z.add_simpl_r in *.
    exploit (IHl (Zlength l1)); try assumption.
    { rewrite Z2Nat.inj_add in *; simpl in *; omega. }
    { apply Ht1. }
    { apply Ht2. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { auto. }
    { auto. }
    intros (? & ?); subst.
    unfold data_at, field_at in Hh1, Hh2.
    rewrite data_at_rec_eq in Hh1, Hh2; simpl in Hh1, Hh2.
    unfold at_offset, array_pred, aggregate_pred.array_pred in Hh1, Hh2.
    simpl in Hh1, Hh2.
    destruct Hh1 as (? & ? & Hh1), Hh2 as (? & ? & Hh2).
    rewrite sepcon_emp, by_value_data_at_rec_nonvolatile in Hh1, Hh2; auto.
    unfold mapsto in *; simpl in *.
    destruct p; try contradiction; simpl in *.
    destruct (readable_share_dec sh); [|contradiction].
    destruct Hh1 as [(? & Hmaps1) | (? & ?)];
      [|unfold Znth in *; simpl in *; contradiction].
    destruct Hh2 as [(? & Hmaps2) | (? & ?)];
      [|unfold Znth in *; simpl in *; contradiction].
    assert (r1a = r2a).
    { eapply ex_address_mapsto_precise.
      { exists x1; eauto. }
      { exists x2; eauto. }
      { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
      { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. } }
    subst; split; [eapply sepalg.join_eq; auto|].
    f_equal.
    eapply res_predicates.address_mapsto_value_cohere'; eauto.
    { rewrite sublist_same; auto.
      rewrite Zlength_cons; auto. }
    { rewrite sublist_1_cons, sublist_same; auto.
      rewrite Hlen2; unfold Z.succ; apply Z.add_simpl_r. }
    { rewrite sublist_same; auto.
      rewrite Zlength_cons; auto. }
    { rewrite sublist_1_cons, sublist_same; auto.
      rewrite Hlen1; unfold Z.succ; apply Z.add_simpl_r. }
Qed.

Lemma Forall_rotate : forall {A} P (l : list A) n m, Forall P l ->
  Forall P (rotate l m n).
Proof.
  intros; unfold rotate.
  rewrite Forall_app; split; [apply Forall_skipn | apply Forall_firstn]; auto.
Qed.

Lemma Forall_repeat : forall {A} (P : A -> Prop) x n, P x -> Forall P (repeat x n).
Proof.
  induction n; simpl; auto.
Qed.

Lemma Forall_complete : forall P l m, Forall P l -> P (Vint (Int.repr 0)) ->
  Forall P (complete m l).
Proof.
  intros; unfold complete.
  rewrite Forall_app; split; [|apply Forall_repeat]; auto.
Qed.

Lemma app_eq_inv : forall {A} (l1 l2 l3 l4 : list A)
  (Heq : l1 ++ l2 = l3 ++ l4) (Hlen : length l1 = length l3), l1 = l3 /\ l2 = l4.
Proof.
  induction l1; simpl; intros; destruct l3; try discriminate; auto.
  inv Heq; inv Hlen.
  exploit IHl1; eauto; intros (? & ?); subst; auto.
Qed.

Lemma rotate_inj : forall {A} (l1 l2 : list A) n m, rotate l1 n m = rotate l2 n m ->
  length l1 = length l2 -> l1 = l2.
Proof.
  unfold rotate; intros.
  destruct (app_eq_inv _ _ _ _ H) as (Hskip & Hfirst).
  { repeat rewrite skipn_length; omega. }
  rewrite <- (firstn_skipn (m - n) l1), <- (firstn_skipn (m - n) l2), Hfirst, Hskip;
    auto.
Qed.

Lemma complete_inj : forall l1 l2 m, complete m l1 = complete m l2 ->
  length l1 = length l2 -> l1 = l2.
Proof.
  unfold complete; intros.
  destruct (app_eq_inv _ _ _ _ H); auto.
Qed.

Lemma length_complete : forall l m, (length l <= m)%nat -> length (complete m l) = m.
Proof.
  intros; unfold complete.
  rewrite app_length, repeat_length; omega.
Qed.
