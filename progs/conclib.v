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

Lemma lock_inv_precise : forall v sh R, predicates_sl.precise (lock_inv sh v R).
Proof.
  repeat intro.
  destruct H as (b & o & ? & Hlock).
  admit.
Admitted.

Lemma lock_inv_positive : forall v sh R,
  positive_mpred (lock_inv v sh R).
Proof.
  admit.
Admitted.

Lemma selflock_precise : forall R sh v, predicates_sl.precise R ->
  predicates_sl.precise (selflock R v sh).
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
  destruct HP as (l & sh & rsh & k & p & HP); exists l, sh, rsh, k, p.
  admit.
Admitted.

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

Lemma lock_inv_join : forall sh1 sh2 sh v R (Hjoin : sepalg.join sh1 sh2 sh),
  lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R.
Proof.
  admit.
Admitted.

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
  repeat intro; subst.
(*  Check compcert_rmaps.RML.resource_at_join.*)
  admit.
Admitted.

Lemma prop_almost_empty : forall P phi, predicates_hered.app_pred (prop P) phi -> juicy_machine.almost_empty phi.
Proof.
  admit.
Admitted.

Lemma lock_inv_almost_empty : forall sh v R phi, predicates_hered.app_pred (lock_inv sh v R) phi ->
  juicy_machine.almost_empty phi.
Proof.
  admit.
Admitted.

Lemma almost_empty_join : forall phi1 phi2 phi
  (Hphi1 : juicy_machine.almost_empty phi1)
  (Hphi2 : juicy_machine.almost_empty phi2)
  (Hjoin : sepalg.join phi1 phi2 phi),
  juicy_machine.almost_empty phi.
Proof.
  repeat intro.
  specialize (Hphi1 loc sh psh k P); specialize (Hphi2 loc sh psh k P).
  pose proof (compcert_rmaps.RML.resource_at_join _ _ _ loc Hjoin) as Hsum.
  rewrite H in Hsum.
(*  SearchAbout sepalg.join compcert_rmaps.RML.R.YES.*)
  admit.
Admitted.

Lemma data_at_precise : forall {cs} b o,
  precise (@data_at_ cs Ews (tarray tint 1) (Vptr b o)).
Proof.
  intros; unfold data_at_, field_at_, field_at, at_offset; simpl.
  apply precise_andp2.
  rewrite data_at_rec_eq; unfold withspacer, at_offset; simpl.
  unfold array_pred, aggregate_pred.array_pred; simpl.
  unfold Zlength, Znth; simpl.
  apply precise_andp2.
  rewrite data_at_rec_eq; simpl.
  apply precise_sepcon; [apply mapsto_undef_precise | apply precise_emp]; auto.
Qed.

Lemma cond_var_precise : forall {cs} sh b o, readable_share sh ->
  precise (@cond_var cs sh (Vptr b o)).
Proof.
  intros; unfold cond_var, data_at_, field_at_, field_at, at_offset; simpl.
  apply precise_andp2.
  rewrite data_at_rec_eq; simpl.
  apply mapsto_undef_precise; auto.
Qed.

Lemma positive_sepcon2 : forall P Q (HQ : positive_mpred Q),
  positive_mpred (P * Q).
Proof.
  repeat intro.
  destruct H as (? & ? & ? & ? & HQ1).
  specialize (HQ _ HQ1).
  destruct HQ as (l & sh & rsh & k & p & HQ); exists l, sh, rsh, k, p.
  admit.
Admitted.

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
  admit.
Admitted.

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

(*Lemma lock_precise : forall {cs} sh b o, readable_share sh -> precise (@data_at_ cs sh tlock (Vptr b o)).
Proof.
  intros.
  unfold data_at_, field_at_, field_at, at_offset; simpl.
  apply precise_andp2.
  rewrite data_at_rec_eq; unfold withspacer, at_offset; simpl.
  unfold tlock, default_val; simpl.
  unfold reptype_gen.
  simpl.
  
Print reptype_gen.
Print default_val.
  rewrite data_at_rec_eq; unfold withspacer, at_offset; simpl.
  rewrite data_at_rec_eq; unfold withspacer, at_offset; simpl.
  unfold array_pred, aggregate_pred.array_pred; simpl.
  unfold Zlength, Znth; simpl.
  rewrite data_at_rec_eq; simpl.
  rewrite data_at_rec_eq; simpl.
  apply precise_sepcon; apply precise_andp2; repeat apply precise_sepcon; try apply precise_emp;
    apply mapsto_undef_precise; auto.
Qed.

*)