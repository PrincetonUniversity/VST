Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.progs.incrN.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.

Notation sum := (fold_right Z.add 0).

Definition cptr_lock_inv lg ctr := EX z : Z, data_at Ews tuint (Vint (Int.repr z)) ctr *
  EX lv : list Z, !!(z = sum lv) && iter_sepcon2 (fun g v => ghost_var gsh1 v g) lg lv.

Definition init_ctr_spec :=
 DECLARE _init_ctr
  WITH N : Z, gv: globals
  PRE [ ]
         PROP  (0 <= N)
         LOCAL (gvars gv)
         SEP   (data_at_ Ews tuint (gv _ctr); data_at_ Ews tlock (gv _ctr_lock))
  POST [ tvoid ]
    EX lg : list gname,
         PROP (Zlength lg = N)
         LOCAL ()
         SEP (lock_inv Ews (gv _ctr_lock) (cptr_lock_inv lg (gv _ctr));
              iter_sepcon (ghost_var gsh2 0) lg).

Definition dest_ctr_spec :=
 DECLARE _dest_ctr
  WITH lg : list gname, lv : list Z, gv: globals
  PRE [ ]
         PROP  ()
         LOCAL (gvars gv)
         SEP   (lock_inv Ews (gv _ctr_lock) (cptr_lock_inv lg (gv _ctr));
                iter_sepcon2 (fun g v => ghost_var gsh2 v g) lg lv)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (data_at Ews tuint (vint (sum lv)) (gv _ctr);
              data_at_ Ews tlock (gv _ctr_lock)).

Definition incr_spec :=
 DECLARE _incr
  WITH sh : share, lg : list gname, i : Z, n : Z, gv: globals
  PRE [ ]
         PROP  (readable_share sh; 0 <= i < Zlength lg)
         LOCAL (gvars gv)
         SEP   (lock_inv sh (gv _ctr_lock) (cptr_lock_inv lg (gv _ctr)); ghost_var gsh2 n (Znth i lg))
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (lock_inv sh (gv _ctr_lock) (cptr_lock_inv lg (gv _ctr)); ghost_var gsh2 (n+1) (Znth i lg)).


Definition thread_lock_R sh lg i ctr lockc :=
  lock_inv sh lockc (cptr_lock_inv lg ctr) * ghost_var gsh2 1 (Znth i lg).

Definition thread_lock_inv tsh sh lg i ctr lockc lockt :=
  selflock (thread_lock_R sh lg i ctr lockc) tsh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * share * list gname * Z * val * globals
  PRE [ _args OF (tptr tvoid) ]
         let '(tsh, sh, lg, i, l, gv) := x in
         PROP  (readable_share tsh; readable_share sh; 0 <= i < Zlength lg)
         LOCAL (temp _args y; gvars gv)
         SEP   (lock_inv sh (gv _ctr_lock) (cptr_lock_inv lg (gv _ctr));
                ghost_var gsh2 0 (Znth i lg);
                lock_inv tsh y (thread_lock_inv tsh sh lg i (gv _ctr) (gv _ctr_lock) y))
  POST [ tptr tvoid ]
         PROP ()
         LOCAL ()
         SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ] main_post prog nil gv.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; init_ctr_spec; dest_ctr_spec; incr_spec; thread_func_spec; main_spec]).

Lemma ctr_inv_exclusive : forall lg p,
  exclusive_mpred (cptr_lock_inv lg p).
Proof.
  intros; unfold cptr_lock_inv.
  eapply derives_exclusive, exclusive_sepcon1 with (Q := EX lv : list Z, _),
    data_at__exclusive with (sh := Ews)(t := tuint); auto; simpl; try omega.
  Intro z; apply sepcon_derives; [cancel|].
  Intros lv; Exists lv; apply derives_refl.
Qed.
Hint Resolve ctr_inv_exclusive.

Lemma thread_inv_exclusive : forall tsh sh lg i ctr lock lockt,
  exclusive_mpred (thread_lock_inv tsh sh lg i ctr lock lockt).
Proof.
  intros; apply selflock_exclusive.
  unfold thread_lock_R.
  apply exclusive_sepcon1; auto.
Qed.
Hint Resolve thread_inv_exclusive.

Lemma sum_repeat: forall i n, sum (repeat i n) = (i * Z.of_nat n)%Z.
Proof.
  induction n.
  - symmetry; apply Z.mul_0_r.
  - rewrite Nat2Z.inj_succ; simpl.
    rewrite IHn.
    unfold Z.succ; rewrite (Z.add_comm _ 1).
    apply Zred_factor2.
Qed.

Corollary sum_0: forall n, sum (repeat 0 n) = 0.
Proof.
  intros; rewrite sum_repeat, Z.mul_0_l; auto.
Qed.

Corollary sum_1: forall n, sum (repeat 1 n) = Z.of_nat n.
Proof.
  intros; rewrite sum_repeat, Z.mul_1_l; auto.
Qed.

Lemma body_init_ctr: semax_body Vprog Gprog f_init_ctr init_ctr_spec.
Proof.
  start_function.
  forward.
  forward.
  ghosts_alloc (ghost_var Tsh 0) N.
  Intros lg.
  forward_call (gv _ctr_lock, Ews, cptr_lock_inv lg (gv _ctr)).
  forward_call (gv _ctr_lock, Ews, cptr_lock_inv lg (gv _ctr)).
  { lock_props.
    unfold cptr_lock_inv.
    Exists 0 (repeat 0 (length lg)); entailer!.
    { symmetry; apply sum_0. }
    rewrite iter_sepcon_sepcon with (g1 := ghost_var gsh1 0)(g2 := ghost_var gsh2 0)
      by (intro; erewrite ghost_var_share_join; auto).
    rewrite iter_sepcon2_spec.
    Exists (map (fun g => (g, 0)) lg); entailer!.
    { rewrite !map_map; simpl.
      rewrite map_id_eq, map_const; auto. }
    apply sepcon_derives; [|cancel].
    clear; induction lg; unfold uncurry; simpl; entailer!. }
  forward.
  Exists lg; entailer!.
Qed.

Lemma body_dest_ctr: semax_body Vprog Gprog f_dest_ctr dest_ctr_spec.
Proof.
  start_function.
  forward.
  forward_call (gv _ctr_lock, Ews, cptr_lock_inv lg (gv _ctr)).
  forward_call (gv _ctr_lock, Ews, cptr_lock_inv lg (gv _ctr)).
  { lock_props. }
  unfold cptr_lock_inv.
  Intros z lv'.
  gather_SEP 2 3; replace_SEP 0 (!!(lv' = lv) && iter_sepcon2 (fun g v => ghost_var Tsh v g) lg lv).
  { go_lower; clear.
    rewrite !iter_sepcon2_spec.
    Intros l1 l2; subst.
    revert dependent l2; induction l1; destruct l2; simpl; inversion 1.
    - Exists (@nil (gname * Z)); simpl; entailer!.
    - sep_apply (IHl1 l2); auto.
      Intros l.
      destruct a as (g, v), p as (g', v'); simpl in *; subst.
      unfold uncurry at 2 3; simpl.
      erewrite ghost_var_share_join' by eauto; Intros; subst.
      Exists ((g', v') :: l); simpl; entailer!.
      { repeat split; congruence. }
      apply derives_refl. }
  Intros; subst.
  viewshift_SEP 0 emp.
  { go_lower.
    rewrite iter_sepcon2_spec.
    Intros l; apply own_list_dealloc'. }
  forward.
  cancel.
Qed.

Lemma sum_add: forall l n, fold_right Z.add n l = sum l + n.
Proof.
  induction l; simpl; intros.
  - symmetry; apply Z.add_0_l.
  - rewrite IHl, Z.add_assoc; auto.
Qed.

Lemma upd_Znth_sum: forall l i n, 0 <= i < Zlength l ->
  sum (upd_Znth i l n) = sum l + n - Znth i l.
Proof.
  intros.
  rewrite <- sublist_same with (al := l) at 2 by auto.
  rewrite sublist_split with (mid := i) by omega.
  rewrite sublist_next with (i0 := i) by omega.
  unfold upd_Znth; rewrite !fold_right_app; simpl.
  rewrite !sum_add with (n := _ + _); omega.
Qed.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (gv _ctr_lock, sh, cptr_lock_inv lg (gv _ctr)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z lv.
  assert_PROP (Zlength lv = Zlength lg).
  { rewrite iter_sepcon2_spec; Intros l; subst.
    rewrite !Zlength_map; entailer!. }
  forward.
  forward.
  gather_SEP 2 3.
  viewshift_SEP 0 (!!(Znth i lv = n) && ghost_var Tsh (n+1) (Znth i lg) *
    iter_sepcon2 (fun g v => ghost_var gsh1 v g) (remove_Znth i lg) (remove_Znth i lv)).
  { go_lower.
    rewrite iter_sepcon2_Znth with (i0 := i) by auto.
    rewrite sepcon_comm, <- sepcon_assoc, (sepcon_comm _ (ghost_var _ _ _)).
    erewrite ghost_var_share_join' by eauto; Intros; subst.
    rewrite prop_true_andp by auto; eapply derives_trans, bupd_frame_r.
    apply sepcon_derives, derives_refl.
    apply ghost_var_update. }
  Intros; forward_call (gv _ctr_lock, sh, cptr_lock_inv lg (gv _ctr)).
  { lock_props.
    unfold cptr_lock_inv; Exists (z + 1).
    erewrite <- ghost_var_share_join by eauto.
    Exists (upd_Znth i lv (n+1)); entailer!.
    { rewrite upd_Znth_sum; omega. }
    rewrite iter_sepcon2_Znth with (i0 := i)(l2 := upd_Znth _ _ _)
      by (rewrite ?upd_Znth_Zlength; auto; omega).
    rewrite upd_Znth_same, remove_upd_Znth by omega.
    rewrite !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
    rewrite sepcon_comm; apply sepcon_derives; [apply derives_refl | cancel]. }
  forward.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (sh, lg, i, 0, gv).
  simpl.
  forward_call (y, tsh, thread_lock_R sh lg i (gv _ctr) (gv _ctr_lock), thread_lock_inv tsh sh lg i (gv _ctr) (gv _ctr_lock) y).
  { lock_props.
    unfold thread_lock_inv, thread_lock_R.
    rewrite selflock_eq at 2; cancel.
    rewrite <- sepcon_emp at 1; apply sepcon_derives; [apply derives_refl | cancel]. }
  forward.
Qed.

(*Ltac cancel_for_forward_call ::=
  match goal with
  | gv: globals |- _ =>
    repeat
    match goal with
    | x := gv ?i |- context [gv ?i] =>
        change (gv i) with x
    end
  | _ => idtac
  end;
  cancel_for_evar_frame.*)

Definition N := 5.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  fold N.
  forward_call (N, gv).
  { rewrite sepcon_comm; apply sepcon_derives; [apply derives_refl | cancel]. }
  { unfold N; omega. }
  Intros lg.
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  destruct (split_shares (Z.to_nat N) Ews) as (sh0 & shs & ? & ? & ? & Hshs); auto.
  rewrite Z2Nat.id in * by (unfold N; computable).
  assert_PROP (field_compatible (tarray tlock N) [] (gv _thread_lock)) by entailer!.
  set (thread_lock i := offset_val (sizeof tlock * i) (gv _thread_lock)).
  forward_for_simple_bound N (EX i : Z, EX sh : share,
    PROP (sepalg_list.list_join sh0 (sublist i N shs) sh) LOCAL (gvars gv)
    SEP (lock_inv sh (gv _ctr_lock) (cptr_lock_inv lg (gv _ctr));
         iter_sepcon (ghost_var gsh2 0) (sublist i N lg);
         iter_sepcon (fun j => lock_inv sh2 (thread_lock j)
           (thread_lock_inv sh1 (Znth j shs) lg j (gv _ctr) (gv _ctr_lock) (thread_lock j)))
           (upto (Z.to_nat i));
         data_at_ Ews (tarray tlock (N - i)) (thread_lock i))).
  { unfold N; computable. }
  { Exists Ews.
    subst thread_lock.
    rewrite !sublist_same by auto; entailer!.
    apply derives_refl. }
  { (* first loop *)
    forward.
    replace (force_val _) with (thread_lock i) by (simpl; rewrite sem_add_pi_ptr_special; auto).
    rewrite data_at__tarray.
    destruct (Z.to_nat (N - i)) eqn: Hi.
    { rewrite Z2Nat.inj_sub, Nat.sub_0_le in Hi by omega.
      apply Z2Nat.inj_le in Hi; omega. }
    simpl.
    setoid_rewrite split2_data_at_Tarray_app with (v1 := [default_val tlock]);
      rewrite ?Zlength_cons, ?Zlength_nil, ?Zlength_list_repeat'; auto.
    erewrite data_at_singleton_array_eq by eauto.
    forward_call (thread_lock i, Ews, thread_lock_inv sh1 (Znth i shs) lg i
      (gv _ctr) (gv _ctr_lock) (thread_lock i)).
    { cancel. }
    rewrite sublist_next in H7 by omega.
    inv H7.
    assert (readable_share (Znth i shs)) by (apply Forall_Znth; auto; omega).
    destruct (sepalg_list.list_join_assoc1 (sepalg.join_comm H11) H13) as (sh' & ? & Hsh').
    forward_spawn _thread_func (thread_lock i) (sh1, Znth i shs, lg, i, thread_lock i, gv).
    { erewrite <- lock_inv_share_join; try apply Hsh; auto.
      unshelve erewrite <- (lock_inv_share_join _ _ _ _ _ _ _ Hsh'); auto.
      { eapply readable_share_list_join; eauto. }
      rewrite sublist_next by omega; simpl.
      entailer!. }
    { subst thread_lock; simpl.
      apply isptr_is_pointer_or_null; rewrite isptr_offset_val; auto. }
    Exists sh'; entailer!.
    apply sepcon_derives.
    - rewrite Z2Nat.inj_add, upto_app by omega.
      rewrite iter_sepcon_app; simpl.
      rewrite Z2Nat.id, Z.add_0_r by omega; cancel.
    - rewrite <- Z.sub_add_distr.
      subst thread_lock.
      rewrite field_address0_offset, offset_offset_val.
      rewrite Z.mul_succ_r with (m := i); cancel.
      { rewrite field_compatible0_cons.
        split; [omega|].
        destruct H5 as (? & ? & ? & ? & ?).
        repeat split; auto.
        + hnf.
          destruct (gv _thread_lock); try contradiction; simpl in *.
          rewrite Z.max_r by omega.
          rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr;
            rewrite Ptrofs.unsigned_repr; unfold N in *; try rep_omega.
        + destruct (gv _thread_lock); try contradiction; simpl in *.
          inv H17; try discriminate.
          constructor.
          intros; rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr;
            rewrite Ptrofs.unsigned_repr; unfold N in *; try rep_omega.
          simpl; rewrite <- Z.add_assoc, Zred_factor4.
          apply H23; omega. }
    - apply Z2Nat.inj; try omega.
      rewrite Nat2Z.id, Z2Nat.inj_sub by omega; simpl; omega. }
  rewrite !sublist_nil, Zminus_diag; Intros shx.
  inv H6.
  forward_for_simple_bound N (EX i : Z, EX sh : share,
    PROP (sepalg_list.list_join shx (sublist 0 i shs) sh) LOCAL (gvars gv)
    SEP (lock_inv sh (gv _ctr_lock) (cptr_lock_inv lg (gv _ctr));
         iter_sepcon (ghost_var gsh2 1) (sublist 0 i lg);
         iter_sepcon (fun j => lock_inv sh2 (thread_lock j)
           (thread_lock_inv sh1 (Znth j shs) lg j (gv _ctr) (gv _ctr_lock) (thread_lock j)))
           (sublist i N (upto (Z.to_nat N)));
         data_at_ Ews (tarray tlock i) (gv _thread_lock))).
  { unfold N; computable. }
  { rewrite !sublist_nil; Exists shx; entailer!.
    { constructor. }
    rewrite !data_at__eq, !data_at_zero_array_eq; auto. }
  { (* second loop *)
    forward.
    replace (force_val _) with (thread_lock i) by (simpl; rewrite sem_add_pi_ptr_special; auto).
    Opaque upto.
    rewrite sublist_next with (i0 := i) by (auto; rewrite Zlength_upto, Z2Nat.id; omega); simpl.
    rewrite Znth_upto by (simpl; unfold N in *; omega).
    forward_call (thread_lock i, sh2, thread_lock_inv sh1 (Znth i shs) lg i
      (gv _ctr) (gv _ctr_lock) (thread_lock i)).
    { cancel. }
    unfold thread_lock_inv at 2; unfold thread_lock_R.
    rewrite selflock_eq; Intros.
    forward_call (thread_lock i, Ews, sh1, thread_lock_R (Znth i shs) lg i (gv _ctr) (gv _ctr_lock),
      thread_lock_inv sh1 (Znth i shs) lg i (gv _ctr) (gv _ctr_lock) (thread_lock i)).
    { lock_props.
      unfold thread_lock_inv, thread_lock_R.
      erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel. }
    erewrite <- sublist_same with (al := shs) in Hshs by eauto.
    rewrite sublist_split with (mid := i) in Hshs by omega.
    rewrite sublist_next with (i0 := i) in Hshs by omega.
    rewrite app_cons_assoc in Hshs.
    apply sepalg_list.list_join_unapp in Hshs as (sh' & Hshs1 & ?).
    apply sepalg_list.list_join_unapp in Hshs1 as (? & J & J1).
    apply list_join_eq with (c := x) in J; auto; subst.
    rewrite <- sepalg_list.list_join_1 in J1.
    gather_SEP 3 1; erewrite lock_inv_share_join; eauto.
    rewrite !(sublist_split 0 i (i + 1)), !sublist_len_1 by omega.
    rewrite iter_sepcon_app.
    Exists sh'; entailer!.
    { eapply sepalg_list.list_join_app; eauto.
      econstructor; eauto; constructor. }
    rewrite (sepcon_comm _ (ghost_var _ _ _)), !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
    rewrite sepcon_comm, sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
    rewrite !data_at__tarray.
    rewrite Z2Nat.inj_add, <- list_repeat_app by omega.
    erewrite split2_data_at_Tarray_app by (rewrite Zlength_list_repeat; auto; omega).
    rewrite Z.add_simpl_l; cancel.
    simpl; erewrite data_at_singleton_array_eq by eauto.
    rewrite field_address0_offset.
    cancel.
    { rewrite field_compatible0_cons; split; auto; try omega.
      apply field_compatible_array_smaller0 with (n' := N); auto; omega. }
    { eapply readable_share_list_join; eauto. }
    { apply Forall_Znth; auto; omega. } }
  Intros sh'.
  eapply list_join_eq in Hshs; [|erewrite <- (sublist_same 0 N shs) by auto; eauto]; subst.
  rewrite sublist_nil, sublist_same by auto.
  forward_call (lg, repeat 1 (length lg), gv).
  { rewrite iter_sepcon2_spec.
    Exists (map (fun g => (g, 1)) lg); entailer!.
    { rewrite !map_map; simpl.
      rewrite map_id, map_const; auto. }
    apply sepcon_derives; [|cancel].
    clear; unfold uncurry; induction lg; simpl; entailer!. }
  forward.
  rewrite sum_1, <- Zlength_correct, H.
  (* We've proved that t is N! *)
  forward.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons body_init_ctr.
semax_func_cons body_dest_ctr.
semax_func_cons body_incr.
semax_func_cons body_thread_func.
semax_func_cons body_main.
Qed.
