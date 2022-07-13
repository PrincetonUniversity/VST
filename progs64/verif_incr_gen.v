(* Inspired by:
   Subjective Auxiliary State for Coarse-Grained Concurrency, Ley-Wild and Nanevski, POPL 2013. *)

Require Import VST.concurrency.conclib.
Require Import VST.concurrency.lock_specs.
Require Import VST.atomics.verif_lock.
Require Import VST.concurrency.ghosts.
Require Import VST.progs64.incrN.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition spawn_spec := DECLARE _spawn spawn_spec.

#[local] Program Instance sum_ghost : Ghost :=
  { G := nat; valid g := True; Join_G a b c := c = (a + b)%nat }.
Next Obligation.
Proof.
  exists (fun _ => O).
  - intros; hnf; auto.
  - intros; eexists; hnf; eauto.
  - auto.
Defined.
Next Obligation.
Proof.
  constructor.
  - intros; hnf in *.
    subst; auto.
  - intros; hnf in *.
    exists (b + c)%nat; split; hnf; lia.
  - intros; hnf in *.
    lia.
  - intros; hnf in *.
    lia.
Qed.

#[local] Instance ctr_ghost : Ghost := ref_PCM sum_ghost.

Definition ghost_ref n g := ghost_reference(P := sum_ghost) n g.
Definition ghost_part sh n g := ghost_part(P := sum_ghost) sh n g.
Definition ghost_both sh n1 n2 g := ghost_part_ref(P := sum_ghost) sh n1 n2 g.

Definition t_counter := Tstruct _counter noattr.

Definition cptr_lock_inv g ctr :=
  EX z : nat, field_at Ews t_counter [StructField _ctr] (Vint (Int.repr (Z.of_nat z))) ctr * ghost_ref z g.

Definition init_ctr_spec :=
 DECLARE _init_ctr
  WITH gv: globals
  PRE [ ]
         PROP  ()
         PARAMS ()
         GLOBALS (gv)
         SEP   (library.mem_mgr gv; data_at_ Ews t_counter (gv _c))
  POST [ tvoid ]
    EX h : lock_handle, EX g : gname,
         PROP ()
         LOCAL ()
         SEP (library.mem_mgr gv;
              field_at Ews t_counter [StructField _lock] (ptr_of h) (gv _c); spacer Ews 4 8 (gv _c);
              lock_inv Tsh h (cptr_lock_inv g (gv _c)); ghost_part Tsh O g).

Definition dest_ctr_spec :=
 DECLARE _dest_ctr
  WITH h : lock_handle, g : gname, v : nat, gv : globals
  PRE [ ]
         PROP  ()
         PARAMS ()
         GLOBALS (gv)
         SEP (field_at Ews t_counter [StructField _lock] (ptr_of h) (gv _c); spacer Ews 4 8 (gv _c);
              lock_inv Tsh h (cptr_lock_inv g (gv _c)); ghost_part Tsh v g)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (data_at Ews t_counter (vint (Z.of_nat v), ptr_of h) (gv _c)).

Definition incr_spec :=
 DECLARE _incr
  WITH sh1 : share, sh : share, h : lock_handle, gsh : share, g : gname, n : nat, gv: globals
  PRE [ ]
         PROP  (readable_share sh1; sh <> Share.bot; gsh <> Share.bot)
         PARAMS ()
         GLOBALS (gv)
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv g (gv _c)); ghost_part gsh n g)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv g (gv _c)); ghost_part gsh (S n) g).


Definition thread_lock_R sh1 sh gsh g ctr lockc :=
  field_at sh1 t_counter [StructField _lock] (ptr_of lockc) ctr * lock_inv sh lockc (cptr_lock_inv g ctr) * ghost_part gsh 1%nat g.

Definition thread_lock_inv sh1 tsh sh gsh g ctr lockc lockt :=
  selflock (thread_lock_R sh1 sh gsh g ctr lockc) tsh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * share * lock_handle * share * lock_handle * share * gname * val * globals
  PRE [ tptr tvoid ]
         let '(sh1, tsh, ht, sh, h, gsh, g, l, gv) := x in
         PROP  (readable_share sh1; tsh <> Share.bot; sh <> Share.bot; gsh <> Share.bot)
         PARAMS (ptr_of ht)
         GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); 
                lock_inv sh h (cptr_lock_inv g (gv _c));
                ghost_part gsh O g;
                lock_inv tsh ht (thread_lock_inv sh1 tsh sh gsh g (gv _c) h ht))
  POST [ tint ]
         PROP ()
         LOCAL ()
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
  eapply derives_exclusive, exclusive_sepcon1 with (Q := EX z : nat, _),
    field_at__exclusive with (sh := Ews)(t := t_counter); auto; simpl; try lia.
  Intro z; apply sepcon_derives; [cancel|].
  Exists z; apply derives_refl.
  { simpl; lia. }
Qed.
#[export] Hint Resolve ctr_inv_exclusive : core.

Lemma thread_inv_exclusive : forall sh1 sh gsh g ctr lock,
  exclusive_mpred (thread_lock_R sh1 sh gsh g ctr lock).
Proof.
  intros; unfold thread_lock_R.
  apply exclusive_sepcon2; unfold exclusive_mpred.
  unfold ghost_part, ghosts.ghost_part; rewrite own_op'; Intros x.
  destruct H as [H _]; hnf in H.
  destruct x as ([(?, ?)|], ?); try contradiction; simpl in H.
  destruct H as (? & _ & J & _); apply sepalg.join_self, identity_share_bot in J; contradiction.
Qed.
#[export] Hint Resolve thread_inv_exclusive : core.

Lemma body_init_ctr: semax_body Vprog Gprog f_init_ctr init_ctr_spec.
Proof.
  start_function.
  forward.
  ghost_alloc (ghost_both Tsh O O).
  { split; auto.
    apply (@self_completable sum_ghost). }
  Intros g.
  forward_call (gv, fun _ : lock_handle => cptr_lock_inv g (gv _c)).
  Intros h.
  forward.
  forward.
  forward_call release_simple (Tsh, h, cptr_lock_inv g (gv _c)).
  { lock_props.
    unfold cptr_lock_inv.
    unfold ghost_both; rewrite <- ghost_part_ref_join.
    unfold_data_at (data_at _ _ _ _).
    unfold ghost_ref; Exists O; entailer!. }
  unfold ghost_part; Exists h g; entailer!.
Qed.

Lemma body_dest_ctr: semax_body Vprog Gprog f_dest_ctr dest_ctr_spec.
Proof.
  start_function.
  forward.
  forward_call (Tsh, h, cptr_lock_inv g (gv _c)).
  forward.
  forward_call freelock_simple (h, cptr_lock_inv g (gv _c)).
  { lock_props. }
  unfold cptr_lock_inv.
  Intros z.
  entailer!.
  unfold ghost_part, ghost_ref; sep_apply (ref_sub(P := sum_ghost)).
  rewrite eq_dec_refl; Intros; subst.
  unfold_data_at (data_at _ _ _ _); cancel.
  rewrite <- sepcon_emp; apply sepcon_derives; apply own_dealloc.
Qed.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (sh, h, cptr_lock_inv g (gv _c)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z.
  forward.
  forward.
  forward.
  gather_SEP (ghost_part _ _ _) (ghost_ref _ _).
  viewshift_SEP 0 (ghost_part gsh (S n) g * ghost_ref (S z) g).
  { go_lower.
    unfold ghost_part, ghost_ref; rewrite !ghost_part_ref_join.
    eapply derives_trans, bupd_fupd.
    apply ref_add with (b := 1%nat); try (hnf; lia). }
  Intros; forward_call release_simple (sh, h, cptr_lock_inv g (gv _c)).
  { lock_props.
    unfold cptr_lock_inv; Exists (S z).
    rewrite Nat2Z.inj_succ.
    entailer!. }
  forward.
  cancel.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (sh1, sh, h, gsh, g, O, gv).
  forward_call release_self (tsh, ht, thread_lock_R sh1 sh gsh g (gv _c) h).
  { unfold thread_lock_inv, selflock, thread_lock_R; cancel. }
  forward.
Qed.

Definition N := 5.

Lemma ghost_part_share_join : forall g sh1 sh2 sh n1 n2, sh1 <> Share.bot -> sh2 <> Share.bot ->
  sepalg.join sh1 sh2 sh ->
  ghost_part sh1 n1 g * ghost_part sh2 n2 g = ghost_part sh (n1 + n2)%nat g.
Proof.
  intros.
  symmetry; apply own_op.
  hnf; simpl.
  repeat (split; auto).
  constructor.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  fold N.
  sep_apply (library.create_mem_mgr gv).
  forward_call gv.
  Intros x; destruct x as (h, g); simpl.
  (* need to split off shares for the locks and ghost here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  destruct (split_shares (Z.to_nat N) Ews) as (sh0 & shs & ? & ? & ? & Hshs); auto.
  destruct (split_shares (Z.to_nat N) Tsh) as (gsh0 & gshs & ? & ? & ? & Hgshs); auto.
  rewrite Z2Nat.id in * by (unfold N; computable).
  assert_PROP (field_compatible (tarray (tptr t_lock) N) [] v_thread_lock) by entailer!.
  set (thread_lock i := offset_val (sizeof (tptr t_lock) * i) v_thread_lock).
  forward_for_simple_bound N (EX i : Z, EX sh : share, EX gsh : share,
    PROP (sepalg_list.list_join sh0 (sublist i N shs) sh;
          sepalg_list.list_join gsh0 (sublist i N gshs) gsh) LOCAL (gvars gv)
    SEP (lock_inv sh (gv _ctr_lock) (cptr_lock_inv g (gv _ctr));
         ghost_part g gsh O;
         iter_sepcon (fun j => lock_inv sh2 (thread_lock j)
           (thread_lock_inv sh1 (Znth j shs) (Znth j gshs) g (gv _ctr) (gv _ctr_lock) (thread_lock j)))
           (upto (Z.to_nat i));
         data_at_ Ews (tarray tlock (N - i)) (thread_lock i))).
  { unfold N; computable. }
  { Exists Ews Tsh.
    subst thread_lock.
    rewrite !sublist_same by auto; entailer!.
    apply derives_refl. }
  { (* first loop *)
    forward.
    simpl sem_binary_operation'.
    replace (force_val _) with (thread_lock i)
      by (rewrite sem_add_pi_ptr_special; auto; unfold N in *; rep_lia).
    rewrite data_at__tarray.
    destruct (Z.to_nat (N - i)) eqn: Hi.
    { rewrite Z2Nat.inj_sub, Nat.sub_0_le in Hi by lia.
      apply Z2Nat.inj_le in Hi; lia. }
    simpl.
    setoid_rewrite split2_data_at_Tarray_app with (v1 := [default_val tlock]);
      rewrite ?Zlength_cons, ?Zlength_nil, ?Zlength_list_repeat'; auto.
    erewrite data_at_singleton_array_eq by eauto.
    forward_call (thread_lock i, Ews, thread_lock_inv sh1 (Znth i shs) (Znth i gshs) g
      (gv _ctr) (gv _ctr_lock) (thread_lock i)).
    { cancel. }
    rewrite sublist_next in H9, H10 by lia.
    inv H9; inv H10.
    assert (readable_share (Znth i shs)) by (apply Forall_Znth; auto; lia).
    assert (Znth i gshs <> Share.bot).
    { intro X; contradiction bot_unreadable.
      rewrite <- X; apply Forall_Znth; auto; lia. }
    destruct (sepalg_list.list_join_assoc1 (sepalg.join_comm H14) H16) as (sh' & ? & Hsh').
    destruct (sepalg_list.list_join_assoc1 (sepalg.join_comm H13) H17) as (gsh' & ? & Hgsh').
    forward_spawn _thread_func (thread_lock i) (sh1, Znth i shs, Znth i gshs, g, thread_lock i, gv).
    { erewrite <- lock_inv_share_join; try apply Hsh; auto.
      unshelve erewrite <- (lock_inv_share_join _ _ _ _ _ _ _ Hsh'); auto.
      { eapply readable_share_list_join; eauto. }
      unshelve erewrite <- (ghost_part_share_join _ _ _ _ O O _ _ Hgsh'); auto.
      { intro; subst.
        contradiction bot_unreadable.
        eapply readable_share_list_join; eauto. }
      entailer!. }
    { subst thread_lock; simpl.
      apply isptr_is_pointer_or_null; rewrite isptr_offset_val; auto. }
    Exists sh' gsh'; entailer!.
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
        destruct H7 as (? & ? & ? & ? & ?).
        repeat split; auto.
        + hnf.
          destruct (gv _thread_lock); try contradiction; simpl in *.
          rewrite Z.max_r by lia.
          rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr;
            rewrite Ptrofs.unsigned_repr; unfold N in *; try rep_lia.
        + destruct (gv _thread_lock); try contradiction; simpl in *.
          inv H23; try discriminate.
          constructor.
          intros; rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr;
            rewrite Ptrofs.unsigned_repr; unfold N in *; try rep_lia.
          simpl; rewrite <- Z.add_assoc, Zred_factor4.
          apply H29; lia. }
    - apply Z2Nat.inj; try lia.
      rewrite Nat2Z.id, Z2Nat.inj_sub by lia; simpl; lia. }
  rewrite !sublist_nil, Zminus_diag; Intros shx gshx.
  inv H8; inv H9.
  forward_for_simple_bound N (EX i : Z, EX sh : share, EX gsh : share,
    PROP (sepalg_list.list_join shx (sublist 0 i shs) sh;
          sepalg_list.list_join gshx (sublist 0 i gshs) gsh) LOCAL (gvars gv)
    SEP (lock_inv sh (gv _ctr_lock) (cptr_lock_inv g (gv _ctr));
         ghost_part g gsh (Z.to_nat i);
         iter_sepcon (fun j => lock_inv sh2 (thread_lock j)
           (thread_lock_inv sh1 (Znth j shs) (Znth j gshs) g (gv _ctr) (gv _ctr_lock) (thread_lock j)))
           (sublist i N (upto (Z.to_nat N)));
         data_at_ Ews (tarray tlock i) (gv _thread_lock))).
  { unfold N; computable. }
  { rewrite !sublist_nil; Exists shx gshx; entailer!.
    { split; constructor. }
    rewrite !data_at__eq, !data_at_zero_array_eq; auto. simpl; cancel. }
  { (* second loop *)
    forward.
    replace (force_val _) with (thread_lock i)
      by (simpl; rewrite sem_add_pi_ptr_special; auto; unfold N in *; simpl in *; rep_lia).
    Opaque upto.
    rewrite sublist_next with (i0 := i) by (auto; rewrite Zlength_upto, Z2Nat.id; lia); simpl.
    rewrite Znth_upto by (simpl; unfold N in *; lia).
    forward_call (thread_lock i, sh2, thread_lock_inv sh1 (Znth i shs) (Znth i gshs) g
      (gv _ctr) (gv _ctr_lock) (thread_lock i)).
    { cancel. }
    unfold thread_lock_inv at 2; unfold thread_lock_R.
    rewrite selflock_eq; Intros.
    forward_call (thread_lock i, Ews, sh1, thread_lock_R (Znth i shs) (Znth i gshs) g (gv _ctr) (gv _ctr_lock),
      thread_lock_inv sh1 (Znth i shs) (Znth i gshs) g (gv _ctr) (gv _ctr_lock) (thread_lock i)).
    { lock_props.
      unfold thread_lock_inv, thread_lock_R.
      erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel. }
    erewrite <- sublist_same with (al := shs) in Hshs by eauto.
    erewrite <- sublist_same with (al := gshs) in Hgshs by eauto.
    rewrite sublist_split with (mid := i) in Hshs, Hgshs by lia.
    rewrite sublist_next with (i0 := i) in Hshs by lia.
    rewrite sublist_next with (i0 := i) in Hgshs by lia.
    rewrite app_cons_assoc in Hshs, Hgshs.
    apply sepalg_list.list_join_unapp in Hshs as (sh' & Hshs1 & ?).
    apply sepalg_list.list_join_unapp in Hgshs as (gsh' & Hgshs1 & ?).
    apply sepalg_list.list_join_unapp in Hshs1 as (? & J & J1).
    apply sepalg_list.list_join_unapp in Hgshs1 as (? & Jg & Jg1).
    apply list_join_eq with (c := sh) in J; auto; subst.
    apply list_join_eq with (c := gsh) in Jg; auto; subst.
    rewrite <- sepalg_list.list_join_1 in J1, Jg1.
    gather_SEP 3 1; erewrite lock_inv_share_join; eauto.
    gather_SEP 3 2; erewrite ghost_part_share_join; eauto.
    rewrite !(sublist_split 0 i (i + 1)), !sublist_len_1 by lia.
    Exists sh' gsh'; entailer!.
    { split; eapply sepalg_list.list_join_app; eauto; econstructor; eauto; constructor. }
    rewrite Z2Nat.inj_add by lia.
    rewrite !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
    rewrite sepcon_comm, sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
    rewrite !data_at__tarray.
    rewrite Z2Nat.inj_add, <- list_repeat_app by lia.
    erewrite split2_data_at_Tarray_app by (rewrite Zlength_list_repeat; auto; lia).
    rewrite Z.add_simpl_l; cancel.
    simpl; erewrite data_at_singleton_array_eq by eauto.
    rewrite field_address0_offset.
    cancel.
    { rewrite field_compatible0_cons; split; auto; try lia.
      apply field_compatible_array_smaller0 with (n' := N); auto; lia. }
    { intro X; contradiction unreadable_bot.
      rewrite <- X; eapply readable_share_list_join; eauto. }
    { intro X; contradiction unreadable_bot.
      rewrite <- X; apply Forall_Znth; auto; lia. }
    { eapply readable_share_list_join; eauto. }
    { apply Forall_Znth; auto; lia. } }
  Intros sh' gsh'.
  eapply list_join_eq in Hshs; [|erewrite <- (sublist_same 0 N shs) by auto; eauto].
  eapply list_join_eq in Hgshs; [|erewrite <- (sublist_same 0 N gshs) by auto; eauto].
  subst.
  forward_call (g, Z.to_nat N, gv).
  forward.
  rewrite Z2Nat.id; [|unfold N; computable].
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
Qed.

