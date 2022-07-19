Require Import VST.concurrency.conclib.
Require Import VST.concurrency.lock_specs.
Require Import VST.atomics.verif_lock.
Require Import VST.concurrency.ghosts.
Require Import VST.progs64.incrN.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition t_counter := Tstruct _counter noattr.

Notation sum := (fold_right Z.add 0).

Definition cptr_lock_inv lg ctr := EX z : Z, field_at Ews t_counter [StructField _ctr] (Vint (Int.repr z)) ctr *
  EX lv : list Z, !!(z = sum lv) && iter_sepcon2 (fun g v => ghost_var gsh1 v g) lg lv.

Definition init_ctr_spec :=
 DECLARE _init_ctr
  WITH N : Z, gv: globals
  PRE [ ]
         PROP  (0 <= N)
         PARAMS ()
         GLOBALS (gv)
         SEP   (library.mem_mgr gv; data_at_ Ews t_counter (gv _c))
  POST [ tvoid ]
    EX h : lock_handle, EX lg : list gname,
         PROP (Zlength lg = N)
         LOCAL ()
         SEP (library.mem_mgr gv;
              field_at Ews t_counter [StructField _lock] (ptr_of h) (gv _c); spacer Ews 4 8 (gv _c);
              lock_inv Tsh h (cptr_lock_inv lg (gv _c));
              iter_sepcon (ghost_var gsh2 0) lg).

Definition dest_ctr_spec :=
 DECLARE _dest_ctr
  WITH h : lock_handle, lg : list gname, lv : list Z, gv: globals
  PRE [ ]
         PROP  ()
         PARAMS ()
         GLOBALS (gv)
         SEP   (field_at Ews t_counter [StructField _lock] (ptr_of h) (gv _c); spacer Ews 4 8 (gv _c);
                lock_inv Tsh h (cptr_lock_inv lg (gv _c));
                iter_sepcon2 (fun g v => ghost_var gsh2 v g) lg lv)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (data_at Ews t_counter (vint (sum lv), ptr_of h) (gv _c)).

Definition incr_spec :=
 DECLARE _incr
  WITH sh1 : share, sh : share, h : lock_handle, lg : list gname, i : Z, n : Z, gv: globals
  PRE [ ]
         PROP  (readable_share sh1; sh <> Share.bot; 0 <= i < Zlength lg)
         PARAMS ()
         GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c);
                lock_inv sh h (cptr_lock_inv lg (gv _c)); ghost_var gsh2 n (Znth i lg))
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c);
              lock_inv sh h (cptr_lock_inv lg (gv _c)); ghost_var gsh2 (n+1) (Znth i lg)).


Definition thread_lock_R sh1 sh lg i ctr lockc :=
  field_at sh1 t_counter [StructField _lock] (ptr_of lockc) ctr *
  lock_inv sh lockc (cptr_lock_inv lg ctr) * ghost_var gsh2 1 (Znth i lg).

Definition thread_lock_inv sh1 tsh sh lg i ctr lockc lockt :=
  selflock (thread_lock_R sh1 sh lg i ctr lockc) tsh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * share * share * lock_handle * lock_handle * list gname * Z * val * globals
  PRE [ tptr tvoid ]
         let '(sh1, tsh, sh, h, ht, lg, i, l, gv) := x in
         PROP  (readable_share sh1; tsh <> Share.bot; sh <> Share.bot; ptr_of ht = y; 0 <= i < Zlength lg)
         PARAMS (y)
         GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c);
                lock_inv sh h (cptr_lock_inv lg (gv _c));
                ghost_var gsh2 0 (Znth i lg);
                lock_inv tsh ht (thread_lock_inv sh1 tsh sh lg i (gv _c) h ht))
  POST [ tint ]
         PROP ()
         RETURN (Vint Int.zero)
         SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  freelock_spec; spawn_spec; init_ctr_spec; dest_ctr_spec; incr_spec; thread_func_spec; main_spec]).

Lemma ctr_inv_exclusive : forall lg p,
  exclusive_mpred (cptr_lock_inv lg p).
Proof.
  intros; unfold cptr_lock_inv.
  eapply derives_exclusive, exclusive_sepcon1 with (Q := EX lv : list Z, _),
    field_at__exclusive with (sh := Ews)(t := t_counter); auto; simpl; try lia.
  Intro z; apply sepcon_derives; [cancel|].
  Intros lv; Exists lv; apply derives_refl.
  { simpl; lia. }
Qed.
#[export] Hint Resolve ctr_inv_exclusive : core.

Lemma thread_inv_exclusive : forall sh1 sh lg i ctr lock,
  exclusive_mpred (thread_lock_R sh1 sh lg i ctr lock).
Proof.
  intros; unfold thread_lock_R.
  apply exclusive_sepcon2; auto with exclusive.
Qed.

#[export] Hint Resolve thread_inv_exclusive : core.

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
  ghosts_alloc (ghost_var Tsh 0) N.
  Intros lg.
  forward_call (gv, fun _ : lock_handle => cptr_lock_inv lg (gv _c)).
  Intros h.
  forward.
  forward.
  forward_call release_simple (Tsh, h, cptr_lock_inv lg (gv _c)).
  { lock_props.
    unfold cptr_lock_inv.
    Exists 0 (repeat 0 (length lg)); entailer!.
    { symmetry; apply sum_0. }
    rewrite iter_sepcon_sepcon with (g1 := ghost_var gsh1 0)(g2 := ghost_var gsh2 0)
      by (intro; erewrite ghost_var_share_join; auto with share).
    rewrite iter_sepcon2_spec.
    Exists (map (fun g => (g, 0)) lg); entailer!.
    { rewrite !map_map; simpl.
      rewrite map_id_eq, map_const; auto. }
    rewrite <- iter_sepcon_map; unfold uncurry; simpl.
    change (fun x => ghost_var gsh1 0 x) with (ghost_var gsh1 0).
    unfold_data_at (data_at _ _ _ _); cancel. }
  Exists h lg; entailer!.
Qed.

Lemma body_dest_ctr: semax_body Vprog Gprog f_dest_ctr dest_ctr_spec.
Proof.
  start_function.
  forward.
  forward_call (Tsh, h, cptr_lock_inv lg (gv _c)).
  forward.
  forward_call freelock_simple (h, cptr_lock_inv lg (gv _c)).
  { lock_props. }
  unfold cptr_lock_inv.
  Intros z lv'.
  gather_SEP (iter_sepcon2 _ _ _) (iter_sepcon2 _ _ _); replace_SEP 0 (!!(lv' = lv) && iter_sepcon2 (fun g v => ghost_var Tsh v g) lg lv).
  { go_lower; clear.
    rewrite !iter_sepcon2_spec.
    Intros l1 l2; subst.
    revert dependent l2; induction l1; destruct l2; simpl; inversion 1.
    - Exists (@nil (gname * Z)); simpl; entailer!.
    - sep_apply (IHl1 l2); auto.
      Intros l.
      destruct a as (g, v), p as (g', v'); simpl in *; subst.
      unfold uncurry at 2 3; simpl.
      erewrite ghost_var_share_join' by (eauto with share); Intros; subst.
      Exists ((g', v') :: l); simpl; entailer!.
      apply derives_refl. }
  Intros; subst.
  entailer!.
  unfold_data_at (data_at _ _ _ _); cancel.
  rewrite iter_sepcon2_spec.
  Intros l; apply own_list_dealloc'.
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
  rewrite sublist_split with (mid := i) by lia.
  rewrite sublist_next with (i := i) by lia.
  rewrite upd_Znth_unfold, !fold_right_app by auto; simpl.
  rewrite !sum_add with (n := _ + _); lia.
Qed.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (sh, h, cptr_lock_inv lg (gv _c)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z lv.
  assert_PROP (Zlength lv = Zlength lg).
  { rewrite iter_sepcon2_spec; Intros l; subst.
    rewrite !Zlength_map; entailer!. }
  forward.
  forward.
  forward.
  gather_SEP (iter_sepcon2 _ _ _) (ghost_var _ _ _).
  viewshift_SEP 0 (!!(Znth i lv = n) && ghost_var Tsh (n+1) (Znth i lg) *
    iter_sepcon2 (fun g v => ghost_var gsh1 v g) (remove_Znth i lg) (remove_Znth i lv)).
  { go_lower.
    rewrite iter_sepcon2_Znth with (i := i) by auto.
    rewrite sepcon_comm, <- sepcon_assoc, (sepcon_comm _ (ghost_var _ _ _)).
    erewrite ghost_var_share_join' by eauto; Intros; subst.
    rewrite prop_true_andp by auto; eapply derives_trans, fupd_frame_r.
    apply sepcon_derives, derives_refl.
    eapply derives_trans, bupd_fupd; apply ghost_var_update. }
  Intros; forward_call release_simple (sh, h, cptr_lock_inv lg (gv _c)).
  { lock_props.
    unfold cptr_lock_inv; Exists (z + 1).
    erewrite <- ghost_var_share_join by eauto.
    Exists (upd_Znth i lv (n+1)); entailer!.
    { rewrite upd_Znth_sum; lia. }
    rewrite iter_sepcon2_Znth with (i := i)(l2 := upd_Znth _ _ _)
      by (rewrite ?upd_Znth_Zlength; auto; lia).
    rewrite upd_Znth_same, remove_upd_Znth by lia.
    cancel. }
  forward.
  cancel.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (sh1, sh, h, lg, i, 0, gv).
  simpl.
  forward_call release_self (tsh, ht, thread_lock_R sh1 sh lg i (gv _c) h).
  { unfold thread_lock_inv, thread_lock_R, selflock; cancel. }
  forward.
Qed.

Definition N := 5.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  fold N.
  sep_apply (library.create_mem_mgr gv).
  forward_call (N, gv).
  Intros x; destruct x as (lock, lg); simpl.
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  destruct (split_shares (Z.to_nat N) Ews) as (sh01 & shs1 & ? & ? & ? & Hshs1); auto.
  destruct (split_shares (Z.to_nat N) Tsh) as (sh0 & shs & ? & ? & ? & Hshs); auto.
  rewrite Z2Nat.id in * by (unfold N; computable).
  assert_PROP (field_compatible (tarray (tptr t_lock) N) [] v_thread_lock) by entailer!.
  set (thread_lock i := offset_val (sizeof (tptr t_lock) * i) v_thread_lock).
  forward_for_simple_bound N (EX i : Z, EX sh : share, EX fsh : share, EX lh : list lock_handle,
    PROP (sepalg_list.list_join sh0 (sublist i N shs) sh;
          sepalg_list.list_join sh01 (sublist i N shs1) fsh;
          forall j, 0 <= j < i -> ptr_of (Znth j lh) = thread_lock j)
    LOCAL (lvar _thread_lock (tarray (tptr (Tstruct _atom_int noattr)) N) v_thread_lock; gvars gv)
    SEP (library.mem_mgr gv; @field_at CompSpecs fsh t_counter (DOT _lock) (ptr_of lock) (gv _c);
         spacer Ews 4 8 (gv _c); lock_inv sh lock (cptr_lock_inv lg (gv _c));
         iter_sepcon (ghost_var gsh2 0) (sublist i N lg);
         iter_sepcon (fun j => lock_inv gsh2 (Znth j lh)
           (thread_lock_inv (Znth j shs1) (Znth j shs) gsh2 lg j (gv _c) lock (Znth j lh)))
           (upto (Z.to_nat i));
         data_at_ Tsh (tarray (tptr t_lock) (N - i)) (thread_lock i);
         has_ext tt)).
  { unfold N; computable. }
  { Exists Tsh Ews (@nil lock_handle).
    subst thread_lock.
    rewrite !sublist_same by auto; entailer!. }
  { (* first loop *)
    forward_call (gv, thread_lock_inv (Znth i shs1) (Znth i shs) gsh2 lg i (gv _ctr) lock).
    Intros hi.
    forward.
    (*replace (force_val _) with (thread_lock i) by (simpl; rewrite sem_add_pi_ptr_special; auto).*)
    rewrite data_at__tarray.
    destruct (Z.to_nat (N - i)) eqn: Hi.
    { rewrite Z2Nat.inj_sub, Nat.sub_0_le in Hi by lia.
      apply Z2Nat.inj_le in Hi; lia. }
    simpl.
    setoid_rewrite split2_data_at_Tarray_app with (v1 := [default_val tlock]);
      rewrite ?Zlength_cons, ?Zlength_nil, ?Zlength_list_repeat'; auto.
    erewrite data_at_singleton_array_eq by eauto.
    forward_call (thread_lock i, Ews, thread_lock_inv sh1 (Znth i shs) lg i
      (gv _ctr) (gv _ctr_lock) (thread_lock i)).
    { cancel. }
    rewrite sublist_next in H7 by lia.
    inv H7.
    assert (readable_share (Znth i shs)) by (apply Forall_Znth; auto; lia).
    destruct (sepalg_list.list_join_assoc1 (sepalg.join_comm H11) H13) as (sh' & ? & Hsh').
    forward_spawn _thread_func (thread_lock i) (sh1, Znth i shs, lg, i, thread_lock i, gv).
    { erewrite <- lock_inv_share_join; try apply Hsh; auto.
      unshelve erewrite <- (lock_inv_share_join _ _ _ _ _ _ _ Hsh'); auto.
      { eapply readable_share_list_join; eauto. }
      rewrite sublist_next by lia; simpl.
      entailer!. }
    { subst thread_lock; simpl.
      apply isptr_is_pointer_or_null; rewrite isptr_offset_val; auto. }
    Exists sh'; entailer!.
    apply sepcon_derives.
    - rewrite Z2Nat.inj_add, upto_app by lia.
      rewrite iter_sepcon_app; simpl.
      rewrite Z2Nat.id, Z.add_0_r by lia; cancel.
    - rewrite <- Z.sub_add_distr.
      subst thread_lock.
      rewrite field_address0_offset, offset_offset_val.
      rewrite Z.mul_succ_r with (m := i); cancel.
      { rewrite field_compatible0_cons.
        split; [lia|].
        destruct H5 as (? & ? & ? & ? & ?).
        repeat split; auto.
        + hnf.
          destruct (gv _thread_lock); try contradiction; simpl in *.
          rewrite Z.max_r by lia.
          rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr;
            rewrite Ptrofs.unsigned_repr; unfold N in *; try rep_lia.
        + destruct (gv _thread_lock); try contradiction; simpl in *.
          inv H17; try discriminate.
          constructor.
          intros; rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr;
            rewrite Ptrofs.unsigned_repr; unfold N in *; try rep_lia.
          simpl; rewrite <- Z.add_assoc, Zred_factor4.
          apply H23; lia. }
    - apply Z2Nat.inj; try lia.
      rewrite Nat2Z.id, Z2Nat.inj_sub by lia; simpl; lia. }
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
    rewrite !data_at__eq, !data_at_zero_array_eq; auto. simpl; cancel. }
  { (* second loop *)
    forward.
    (*replace (force_val _) with (thread_lock i) by (simpl; rewrite sem_add_pi_ptr_special; auto).*)
    Opaque upto.
    rewrite sublist_next with (i0 := i) by (auto; rewrite Zlength_upto, Z2Nat.id; lia); simpl.
    rewrite Znth_upto by (simpl; unfold N in *; lia).
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
    rewrite sublist_split with (mid := i) in Hshs by lia.
    rewrite sublist_next with (i0 := i) in Hshs by lia.
    rewrite app_cons_assoc in Hshs.
    apply sepalg_list.list_join_unapp in Hshs as (sh' & Hshs1 & ?).
    apply sepalg_list.list_join_unapp in Hshs1 as (? & J & J1).
    apply list_join_eq with (c := sh) in J; auto; subst.
    rewrite <- sepalg_list.list_join_1 in J1.
    gather_SEP 3 1; erewrite lock_inv_share_join; eauto.
    rewrite !(sublist_split 0 i (i + 1)), !sublist_len_1 by lia.
    rewrite iter_sepcon_app.
    Exists sh'; entailer!.
    { eapply sepalg_list.list_join_app; eauto.
      econstructor; eauto; constructor. }
    simpl; cancel.
    rewrite !data_at__tarray.
    rewrite Z2Nat.inj_add, <- list_repeat_app by lia.
    erewrite split2_data_at_Tarray_app by (rewrite Zlength_list_repeat; auto; lia).
    rewrite Z.add_simpl_l; cancel.
    simpl; erewrite data_at_singleton_array_eq by eauto.
    rewrite field_address0_offset.
    unfold thread_lock_inv, thread_lock_R; cancel.
    { rewrite field_compatible0_cons; split; auto; try lia.
      apply field_compatible_array_smaller0 with (n' := N); auto; lia. }
    { eapply readable_share_list_join; eauto. }
    { apply Forall_Znth; auto; lia. } }
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
#[export] Existing Instance Espec.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
do 7 semax_func_cons_ext.
semax_func_cons body_init_ctr.
semax_func_cons body_dest_ctr.
semax_func_cons body_incr.
semax_func_cons body_thread_func.
semax_func_cons body_main.
(*   repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
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
semax_func_cons body_main.*)
Qed.
