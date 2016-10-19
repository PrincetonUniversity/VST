Require Export msl.predicates_sl.
Require Export concurrency.semax_conc.
Require Export floyd.proofauto.
Require Export floyd.sublist.

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

Lemma positive_andp1 : forall P Q (HP : positive_mpred P),
  positive_mpred (P && Q).
Proof.
  intros ???? (? & ?); auto.
Qed.

Lemma positive_andp2 : forall P Q (HQ : positive_mpred Q),
  positive_mpred (P && Q).
Proof.
  intros ???? (? & ?); auto.
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

Lemma positive_FF : positive_mpred FF.
Proof.
  repeat intro; contradiction.
Qed.

Lemma derives_positive : forall P Q (Hderives : P |-- Q) (HQ : positive_mpred Q), positive_mpred P.
Proof.
  repeat intro.
  specialize (Hderives _ H); auto.
Qed.

Lemma ex_address_mapsto_positive: forall ch rsh sh l,
  positive_mpred (EX v : val, res_predicates.address_mapsto ch v rsh sh l).
Proof.
  intros ????? (? & ? & ? & Hp); simpl in Hp.
  specialize (Hp l); destruct (adr_range_dec _ _ _).
  destruct Hp; eauto 6.
  { contradiction n; unfold adr_range.
    destruct l; repeat split; auto; try omega.
    destruct ch; simpl; omega. }
Qed.

Corollary mapsto_positive : forall sh t p v, readable_share sh -> positive_mpred (mapsto sh t p v).
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try apply positive_FF.
  destruct (type_is_volatile t); try apply positive_FF.
  destruct p; try apply positive_FF.
  destruct (readable_share_dec sh); [|contradiction n; auto].
  eapply derives_positive, ex_address_mapsto_positive.
  apply orp_left; entailer.
  - Exists v; eauto.
  - Exists v2'; auto.
Qed.

Lemma ex_positive : forall t P, (forall x, positive_mpred (P x)) -> positive_mpred (EX x : t, P x).
Proof.
  intros ???? (? & ?).
  eapply H; eauto.
Qed.

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

(*Lemma emp_almost_empty : forall phi, predicates_hered.app_pred emp phi -> juicy_machine.almost_empty phi.
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
  (Hjoin : sepalg.join phi1 phi2 phi)
  (Hphi1 : juicy_machine.almost_empty phi1)
  (Hphi2 : juicy_machine.almost_empty phi2),
  juicy_machine.almost_empty phi.
Proof.
  repeat intro.
  apply compcert_rmaps.RML.resource_at_join with (loc := loc) in Hjoin.
  rewrite H in Hjoin; inv Hjoin.
  - eapply Hphi1; eauto.
  - eapply Hphi2; eauto.
  - eapply Hphi1; eauto.
Qed.*)

Lemma precise_FF : precise FF.
Proof.
  repeat intro; contradiction.
Qed.

Lemma cond_var_precise : forall {cs} sh p, readable_share sh ->
  precise (@cond_var cs sh p).
Proof.
  intros; unfold cond_var, data_at_, field_at_, field_at, at_offset; simpl.
  destruct p; try (rewrite prop_false_andp; [|intros (? & ?); contradiction]; apply precise_FF).
  apply precise_andp2.
  rewrite data_at_rec_eq; simpl.
  apply mapsto_undef_precise; auto.
Qed.

Lemma cond_var_positive : forall {cs} sh p, readable_share sh ->
  positive_mpred (@cond_var cs sh p).
Proof.
  intros; unfold cond_var, data_at_, field_at_, field_at, at_offset; simpl.
  destruct p; try (rewrite prop_false_andp; [|intros (? & ?); contradiction]; apply positive_FF).
  apply positive_andp2.
  rewrite data_at_rec_eq; simpl.
  apply mapsto_positive; auto.
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

(*Lemma cond_var_almost_empty : forall {cs} sh v phi, predicates_hered.app_pred (@cond_var cs sh v) phi ->
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
   because that means something in the underlying model. Eventually we should figure something out for this. *)*)

Lemma cond_var_share_join : forall {cs} sh1 sh2 sh v (Hjoin : sepalg.join sh1 sh2 sh),
  @cond_var cs sh1 v * cond_var sh2 v = cond_var sh v.
Proof.
  intros; unfold cond_var; apply data_at__share_join; auto.
Qed.

Definition complete MAX l := l ++ repeat (Vint (Int.repr 0)) (Z.to_nat MAX - length l).

Lemma upd_complete : forall l x MAX, Zlength l < MAX -> 
  upd_Znth (Zlength l) (complete MAX l) x = complete MAX (l ++ [x]).
Proof.
  intros; unfold complete.
  rewrite upd_Znth_app2, Zminus_diag.
  rewrite app_length; simpl plus.
  rewrite Zlength_correct, Z2Nat.inj_lt, Nat2Z.id in H; try omega.
  destruct (Z.to_nat MAX - length l)%nat eqn: Hminus; [omega|].
  replace (Z.to_nat MAX - (length l + 1))%nat with n by omega.
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

Lemma remove_complete : forall l x MAX, Zlength l < MAX -> 
  upd_Znth (Zlength l) (complete MAX (l ++ [x])) (Vint (Int.repr 0)) = complete MAX l.
Proof.
  intros; unfold complete.
  rewrite upd_Znth_app1; [|repeat rewrite Zlength_correct; rewrite app_length; simpl; Omega0].
  rewrite app_length; simpl plus.
  rewrite upd_Znth_app2, Zminus_diag; [|rewrite Zlength_cons; simpl; omega].
  unfold upd_Znth, sublist.sublist.
  rewrite Zminus_diag; simpl firstn.
  rewrite Zlength_correct, Z2Nat.inj_lt, Nat2Z.id in H; try omega.
  destruct (Z.to_nat MAX - length l)%nat eqn: Hminus; [omega|].
  replace (Z.to_nat MAX - (length l + 1))%nat with n by omega.
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

Definition rotate {A} (l : list A) n m := sublist (m - n) (Zlength l) l ++
  sublist 0 (m - n) l.

Lemma sublist_0_cons : forall {A} j x (l : list A), j > 0 ->
  sublist 0 j (x :: l) = x :: sublist 0 (j - 1) l.
Proof.
  intros; unfold sublist; simpl.
  destruct (Z.to_nat (j - 0)) eqn: Hminus.
  - apply Z.gt_lt in H; rewrite Z2Nat.inj_lt in H; try omega.
    rewrite Z2Nat.inj_sub in Hminus; omega.
  - simpl; repeat f_equal.
    rewrite Z.sub_0_r in *.
    rewrite Z2Nat.inj_sub, Hminus; simpl; omega.
Qed.

Lemma sublist_S_cons : forall {A} i j x (l : list A), i > 0 ->
  sublist i j (x :: l) = sublist (i - 1) (j - 1) l.
Proof.
  intros; unfold sublist; simpl.
  destruct (Z.to_nat i) eqn: Hi.
  - apply Z.gt_lt in H; rewrite Z2Nat.inj_lt in H; omega.
  - simpl.
    f_equal; f_equal; try omega.
    rewrite Z2Nat.inj_sub, Hi; simpl; omega.
Qed.

Lemma upd_rotate : forall {A} i (l : list A) n m x (Hl : Zlength l = m) (Hlt : 0 <= n < m)
  (Hi : 0 <= i < Zlength l),
  upd_Znth i (rotate l n m) x = rotate (upd_Znth ((i - n) mod m) l x) n m.
Proof.
  intros; unfold upd_Znth, rotate.
  subst; autorewrite with sublist.
  exploit (Z_mod_lt (i - n) (Zlength l)); [omega|].
  intro; repeat rewrite Zlength_sublist; try omega.
  rewrite sublist_app; try omega.
  autorewrite with sublist.
  rewrite Z.min_l, sublist_sublist; try omega.
  rewrite sublist_sublist; try omega.
  rewrite sublist_app; try omega; repeat rewrite Zlength_sublist; try omega.
  autorewrite with sublist.
  rewrite (Z.min_r (n + _) n), sublist_sublist; try omega.
  rewrite (Z.max_l (Zlength l - _) 0); [|omega].
  rewrite sublist_app; try omega; try rewrite Zlength_cons; repeat rewrite Zlength_sublist; try omega.
  autorewrite with sublist.
  rewrite (Z.max_l (Z.succ _)); [|omega].
  rewrite sublist_app; try omega; try rewrite Zlength_cons; repeat rewrite Zlength_sublist; try omega.
  rewrite (Z.max_r (0 - _)); [|omega].
  assert (i < n /\ (i - n) mod Zlength l = Zlength l + i - n \/
          i >= n /\ (i - n) mod Zlength l = i - n) as Hcase.
  { destruct (Z_lt_dec i n); [left | right]; split; try omega.
    - rewrite Zmod_eq; [|omega].
      replace (_ / _) with (-1); try Omega0.
      replace (_ - _) with (- (n - i)); [|omega].
      rewrite Z_div_nz_opp_full, Zdiv_small; try omega.
      rewrite Zmod_small; omega.
    - apply Zmod_small; omega. }
  destruct Hcase as [(? & Heq) | (? & Heq)]; rewrite Heq; autorewrite with sublist.
  - rewrite Z.min_l, Z.min_l, Z.min_l, Z.min_r, Z.min_l; try omega.
    autorewrite with sublist.
    rewrite sublist_0_cons; [|omega].
    autorewrite with sublist.
    rewrite <- app_assoc; simpl; do 2 f_equal; try omega.
    do 2 f_equal; omega.
  - rewrite Z.min_r, Z.max_l, Z.min_r, Z.max_l, Z.min_r, Z.min_r, Z.max_l, Z.min_l; try omega.
    autorewrite with sublist.
    rewrite (sublist_nil (i - n)); simpl.
    rewrite sublist_0_cons; [simpl | omega].
    rewrite sublist_S_cons; [|omega].
    autorewrite with sublist.
    rewrite <- app_assoc; do 2 f_equal; try omega.
    f_equal.
    rewrite sublist_nil; simpl; f_equal; omega.
  - split; [rewrite Z.min_glb_iff | rewrite Z.min_le_iff]; omega.
  - split; [|rewrite Z.max_le_iff]; omega.
  - rewrite Z.max_lub_iff; omega.
  - split; [|rewrite Z.min_glb_iff]; omega.
  - rewrite Z.min_le_iff; omega.
  - repeat rewrite Zlength_sublist; omega.
Qed.

Lemma combine_app : forall {A B} (l1 l2 : list A) (l1' l2' : list B), length l1 = length l1' ->
  combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  induction l1; destruct l1'; intros; try discriminate; auto; simpl in *.
  rewrite IHl1; auto.
Qed.

Lemma mapsto_inj : forall sh t v1 v2 p r1 r2 r
  (Hsh : readable_share sh)
  (Hp1 : predicates_hered.app_pred (mapsto sh t p v1) r1)
  (Hp2 : predicates_hered.app_pred (mapsto sh t p v2) r2)
  (Hval : type_is_by_value t = true)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hdef1 : v1 <> Vundef) (Hdef2 : v2 <> Vundef),
  r1 = r2 /\ v1 = v2.
Proof.
  unfold mapsto; intros.
  destruct (access_mode_by_value _ Hval) as (? & Hby); rewrite Hby in *.
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
  - destruct a1; [|rewrite <- Hlen1, Zlength_cons, Zlength_correct, Z2Nat.inj_succ in Heql; omega].
    rewrite Zlength_nil in Hlen1.
    destruct a2; [split; auto | rewrite Zlength_cons, Zlength_correct in Hlen2; omega].
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
    { rewrite Zlength_correct in *; omega. }
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite split_array_pred with (mid := 1) in Hp1; auto; [|rewrite Zlength_cons; omega].
    rewrite split_array_pred with (mid := 1) in Hp2; auto; [|rewrite Zlength_cons; omega].
    destruct Hp1 as (r1a & ? & ? & Hh1 & Ht1), Hp2 as (r2a & ? & ? & Hh2 & Ht2).
    repeat rewrite Z.sub_0_r in *.
    rewrite sublist_one with (d := x1), array_pred_len_1 in Hh1, Hh2; auto; try rewrite Zlength_cons; try omega.
    rewrite sublist_1_cons in Ht1, Ht2.
    unfold Znth in *; simpl in *.
    unfold at_offset in Hh1, Hh2.
    assert (Zlength l1 = z - 1) by omega.
    assert (Zlength l2 = z - 1) by omega.
    rewrite sublist_same in Ht1, Ht2; auto.
    inv Hdef1; inv Hdef2.
    exploit (IHl (Zlength l1)); try assumption.
    { subst.
      rewrite Z2Nat.inj_succ in *; omega. }
    { rewrite data_at_rec_eq; simpl.
      instantiate (2 := offset_val 4 p).
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l1).
      erewrite array_pred_shift; try simple apply Ht1; auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { rewrite data_at_rec_eq; simpl.
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l2).
      erewrite array_pred_shift; try simple apply Ht2; auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { auto. }
    { auto. }
    { auto. }
    { omega. }
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
  - destruct a1; [|rewrite <- Hlen1, Zlength_cons, Zlength_correct, Z2Nat.inj_succ in Heql; omega].
    rewrite Zlength_nil in Hlen1.
    destruct a2; [split; auto | rewrite Zlength_cons, Zlength_correct in Hlen2; omega].
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
    { rewrite Zlength_correct in *; omega. }
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in *.
    unfold unfold_reptype in *; simpl in *.
    rewrite split_array_pred with (mid := 1) in Hp1; auto; [|rewrite Zlength_cons; omega].
    rewrite split_array_pred with (mid := 1) in Hp2; auto; [|rewrite Zlength_cons; omega].
    destruct Hp1 as (r1a & ? & ? & Hh1 & Ht1), Hp2 as (r2a & ? & ? & Hh2 & Ht2).
    repeat rewrite Z.sub_0_r in *.
    rewrite sublist_one with (d := x1), array_pred_len_1 in Hh1, Hh2; auto; try rewrite Zlength_cons; try omega.
    rewrite sublist_1_cons in Ht1, Ht2.
    unfold Znth in *; simpl in *.
    unfold at_offset in Hh1, Hh2.
    assert (Zlength l1 = z - 1) by omega.
    assert (Zlength l2 = z - 1) by omega.
    rewrite sublist_same in Ht1, Ht2; auto.
    inv Hdef1; inv Hdef2.
    exploit (IHl (Zlength l1)); try assumption.
    { subst.
      rewrite Z2Nat.inj_succ in *; omega. }
    { rewrite data_at_rec_eq; simpl.
      instantiate (2 := offset_val 4 p).
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l1).
      erewrite array_pred_shift; try simple apply Ht1; auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { rewrite data_at_rec_eq; simpl.
      setoid_rewrite at_offset_array_pred.
      instantiate (2 := l2).
      erewrite array_pred_shift; try simple apply Ht2; auto; try omega.
      intros; unfold at_offset.
      rewrite offset_offset_val; do 2 f_equal; omega. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { auto. }
    { auto. }
    { auto. }
    { omega. }
    intros (? & ?); subst.
    rewrite by_value_data_at_rec_nonvolatile in Hh1, Hh2; auto.
    exploit (mapsto_inj sh (tptr t) x1 x2); eauto.
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    intros (? & ?); subst.
    split; [eapply sepalg.join_eq|]; auto.
Qed.

Lemma Forall_rotate : forall {A} P (l : list A) n m, Forall P l ->
  Forall P (rotate l m n).
Proof.
  intros; unfold rotate.
  rewrite Forall_app; split; apply Forall_sublist; auto.
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
  length l1 = length l2 -> 0 <= n <= m -> m <= Zlength l1 -> l1 = l2.
Proof.
  unfold rotate; intros.
  destruct (app_eq_inv _ _ _ _ H) as (Hskip & Hfirst).
  { unfold sublist; repeat rewrite firstn_length, skipn_length.
    repeat rewrite Zlength_correct; rewrite H0; omega. }
  erewrite <- sublist_same with (al := l1), <- sublist_rejoin with (mid := m - n); auto; try omega.
  rewrite Hfirst, Hskip, sublist_rejoin, sublist_same; auto; try omega.
  repeat rewrite Zlength_correct in *; rewrite H0 in *; omega.
Qed.

Lemma complete_inj : forall l1 l2 m, complete m l1 = complete m l2 ->
  length l1 = length l2 -> l1 = l2.
Proof.
  unfold complete; intros.
  destruct (app_eq_inv _ _ _ _ H); auto.
Qed.

Lemma length_complete : forall l m, Zlength l <= m -> length (complete m l) = Z.to_nat m.
Proof.
  intros; unfold complete.
  rewrite app_length, repeat_length; rewrite Zlength_correct in H; Omega0.
Qed.

Lemma Zlength_rotate : forall {A} (l : list A) n m, 0 <= n <= m -> m <= Zlength l ->
  Zlength (rotate l n m) = Zlength l.
Proof.
  intros; unfold rotate.
  rewrite Zlength_app; repeat rewrite Zlength_sublist; omega.
Qed.

Lemma Zlength_repeat : forall {A} (x : A) n, Zlength (repeat x n) = Z.of_nat n.
Proof.
  intros; rewrite Zlength_correct, repeat_length; auto.
Qed.

Lemma Zlength_complete : forall l m, Zlength l <= m -> Zlength (complete m l) = m.
Proof.
  intros; unfold complete.
  rewrite Zlength_app, Zlength_repeat; rewrite Zlength_correct in *; Omega0.
Qed.

Lemma combine_eq : forall {A B} (l : list (A * B)), combine (map fst l) (map snd l) = l.
Proof.
  induction l; auto; simpl.
  destruct a; rewrite IHl; auto.
Qed.

Lemma precise_emp : precise emp.
Proof.
  apply precise_emp.
Qed.

Hint Resolve precise_emp lock_inv_precise lock_inv_positive selflock_precise selflock_positive
  cond_var_precise cond_var_positive precise_FF positive_FF.