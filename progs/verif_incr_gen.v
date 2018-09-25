(* Inspired by:
   Subjective Auxiliary State for Coarse-Grained Concurrency, Ley-Wild and Nanevski, POPL 2013. *)

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

Instance sum_ghost : Ghost :=
  { G := nat; valid g := True; Join_G a b c := c = (a + b)%nat }.
Proof.
  - exists (fun _ => O).
    + intros.
      hnf.
      auto.
    + auto.
  - constructor.
    + intros; hnf in *.
      subst; auto.
    + intros; hnf in *.
      exists (b + c)%nat; split; hnf; omega.
    + intros; hnf in *.
      omega.
    + intros; hnf in *.
      omega.
  - auto.
Defined.

Instance ctr_ghost : Ghost := ref_PCM sum_ghost.

Definition ghost_ref g n := ghost_reference(P := sum_ghost) g n.
Definition ghost_part g sh n := ghost_part(P := sum_ghost) g sh n.
Definition ghost_both g sh n1 n2 := ghost_part_ref(P := sum_ghost) g sh n1 n2.

Definition cptr_lock_inv g ctr :=
  EX z : nat, data_at Ews tuint (Vint (Int.repr (Z.of_nat z))) ctr * ghost_ref g z.

Definition init_ctr_spec :=
 DECLARE _init_ctr
  WITH gv: globals
  PRE [ ]
         PROP  ()
         LOCAL (gvars gv)
         SEP   (data_at_ Ews tuint (gv _ctr); data_at_ Ews tlock (gv _ctr_lock))
  POST [ tvoid ]
    EX g : gname,
         PROP ()
         LOCAL ()
         SEP (lock_inv Ews (gv _ctr_lock) (cptr_lock_inv g (gv _ctr));
              ghost_part g Tsh O).

Definition dest_ctr_spec :=
 DECLARE _dest_ctr
  WITH g : gname, v : nat, gv: globals
  PRE [ ]
         PROP  ()
         LOCAL (gvars gv)
         SEP   (lock_inv Ews (gv _ctr_lock) (cptr_lock_inv g (gv _ctr));
                ghost_part g Tsh v)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (data_at Ews tuint (vint (Z.of_nat v)) (gv _ctr);
              data_at_ Ews tlock (gv _ctr_lock)).

Definition incr_spec :=
 DECLARE _incr
  WITH sh : share, gsh : share, g : gname, n : nat, gv: globals
  PRE [ ]
         PROP  (readable_share sh; gsh <> Share.bot)
         LOCAL (gvars gv)
         SEP   (lock_inv sh (gv _ctr_lock) (cptr_lock_inv g (gv _ctr)); ghost_part g gsh n)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (lock_inv sh (gv _ctr_lock) (cptr_lock_inv g (gv _ctr)); ghost_part g gsh (S n)).


Definition thread_lock_R sh gsh g ctr lockc :=
  lock_inv sh lockc (cptr_lock_inv g ctr) * ghost_part g gsh 1%nat.

Definition thread_lock_inv tsh sh gsh g ctr lockc lockt :=
  selflock (thread_lock_R sh gsh g ctr lockc) tsh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * share * share * gname * val * globals
  PRE [ _args OF (tptr tvoid) ]
         let '(tsh, sh, gsh, g, l, gv) := x in
         PROP  (readable_share tsh; readable_share sh; gsh <> Share.bot)
         LOCAL (temp _args y; gvars gv)
         SEP   (lock_inv sh (gv _ctr_lock) (cptr_lock_inv g (gv _ctr));
                ghost_part g gsh O;
                lock_inv tsh y (thread_lock_inv tsh sh gsh g (gv _ctr) (gv _ctr_lock) y))
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
  eapply derives_exclusive, exclusive_sepcon1 with (Q := EX z : nat, _),
    data_at__exclusive with (sh := Ews)(t := tuint); auto; simpl; try omega.
  Intro z; apply sepcon_derives; [cancel|].
  Exists z; apply derives_refl.
Qed.
Hint Resolve ctr_inv_exclusive.

Lemma thread_inv_exclusive : forall tsh sh gsh g ctr lock lockt,
  exclusive_mpred (thread_lock_inv tsh sh gsh g ctr lock lockt).
Proof.
  intros; apply selflock_exclusive.
  unfold thread_lock_R.
  apply exclusive_sepcon1; auto.
Qed.
Hint Resolve thread_inv_exclusive.

Lemma body_init_ctr: semax_body Vprog Gprog f_init_ctr init_ctr_spec.
Proof.
  start_function.
  forward.
  forward.
  ghost_alloc (fun g => ghost_both g Tsh O O).
  { split; auto.
    apply self_completable. }
  Intros g.
  forward_call (gv _ctr_lock, Ews, cptr_lock_inv g (gv _ctr)).
  forward_call (gv _ctr_lock, Ews, cptr_lock_inv g (gv _ctr)).
  { lock_props.
    unfold cptr_lock_inv.
    unfold ghost_both; rewrite <- ghost_part_ref_join.
    unfold ghost_ref; Exists O; entailer!. }
  forward.
  unfold ghost_part; Exists g; entailer!.
Qed.

Lemma body_dest_ctr: semax_body Vprog Gprog f_dest_ctr dest_ctr_spec.
Proof.
  start_function.
  forward.
  forward_call (gv _ctr_lock, Ews, cptr_lock_inv g (gv _ctr)).
  forward_call (gv _ctr_lock, Ews, cptr_lock_inv g (gv _ctr)).
  { lock_props. }
  unfold cptr_lock_inv.
  Intros z.
  gather_SEP 2 3. replace_SEP 0 (!!(z = v) && ghost_both g Tsh v v).
  { go_lower; clear.
    rewrite sepcon_comm.
    erewrite (add_andp (_ * _)) by apply (ref_sub(P := sum_ghost)).
    rewrite if_true by auto; entailer!.
    unfold ghost_part, ghost_ref; rewrite ghost_part_ref_join; apply derives_refl. }
  Intros; subst.
  viewshift_SEP 0 emp.
  { go_lower.
    apply own_dealloc. }
  forward.
  cancel.
Qed.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (gv _ctr_lock, sh, cptr_lock_inv g (gv _ctr)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z.
  forward.
  forward.
  gather_SEP 2 3.
  viewshift_SEP 0 (ghost_part g gsh (S n) * ghost_ref g (S z)).
  { go_lower.
    rewrite sepcon_comm.
    unfold ghost_part, ghost_ref; rewrite !ghost_part_ref_join.
    apply ref_add with (b := 1%nat); try (hnf; omega).
    intros; exists (c + 1)%nat; hnf; auto. }
  Intros; forward_call (gv _ctr_lock, sh, cptr_lock_inv g (gv _ctr)).
  { lock_props.
    unfold cptr_lock_inv; Exists (S z).
    rewrite Nat2Z.inj_succ.
    entailer!. }
  forward.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (sh, gsh, g, O, gv).
  forward_call (y, tsh, thread_lock_R sh gsh g (gv _ctr) (gv _ctr_lock),
                thread_lock_inv tsh sh gsh g (gv _ctr) (gv _ctr_lock) y).
  { lock_props.
    unfold thread_lock_inv, thread_lock_R.
    rewrite selflock_eq at 2; cancel. }
  forward.
Qed.

Definition N := 5.

Lemma ghost_part_share_join : forall g sh1 sh2 sh n1 n2, sh1 <> Share.bot -> sh2 <> Share.bot ->
  sepalg.join sh1 sh2 sh ->
  ghost_part g sh1 n1 * ghost_part g sh2 n2 = ghost_part g sh (n1 + n2)%nat.
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
  forward_call gv.
  { rewrite sepcon_comm; apply sepcon_derives; [apply derives_refl | cancel]. }
  Intros g.
  (* need to split off shares for the locks and ghost here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  destruct (split_shares (Z.to_nat N) Ews) as (sh0 & shs & ? & ? & ? & Hshs); auto.
  destruct (split_shares (Z.to_nat N) Tsh) as (gsh0 & gshs & ? & ? & ? & Hgshs); auto.
  rewrite Z2Nat.id in * by (unfold N; computable).
  assert_PROP (field_compatible (tarray tlock N) [] (gv _thread_lock)) by entailer!.
  set (thread_lock i := offset_val (sizeof tlock * i) (gv _thread_lock)).
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
      by (rewrite sem_add_pi_ptr_special; auto; unfold N in *; rep_omega).
    rewrite data_at__tarray.
    destruct (Z.to_nat (N - i)) eqn: Hi.
    { rewrite Z2Nat.inj_sub, Nat.sub_0_le in Hi by omega.
      apply Z2Nat.inj_le in Hi; omega. }
    simpl.
    setoid_rewrite split2_data_at_Tarray_app with (v1 := [default_val tlock]);
      rewrite ?Zlength_cons, ?Zlength_nil, ?Zlength_list_repeat'; auto.
    erewrite data_at_singleton_array_eq by eauto.
    forward_call (thread_lock i, Ews, thread_lock_inv sh1 (Znth i shs) (Znth i gshs) g
      (gv _ctr) (gv _ctr_lock) (thread_lock i)).
    { cancel. }
    rewrite sublist_next in H9, H10 by omega.
    inv H9; inv H10.
    assert (readable_share (Znth i shs)) by (apply Forall_Znth; auto; omega).
    assert (Znth i gshs <> Share.bot).
    { intro X; contradiction bot_unreadable.
      rewrite <- X; apply Forall_Znth; auto; omega. }
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
    - rewrite Z2Nat.inj_add, upto_app by omega.
      rewrite iter_sepcon_app; simpl.
      rewrite Z2Nat.id, Z.add_0_r by omega; cancel.
    - rewrite <- Z.sub_add_distr.
      subst thread_lock.
      rewrite field_address0_offset, offset_offset_val.
      rewrite Z.mul_succ_r with (m := i); cancel.
      { rewrite field_compatible0_cons.
        split; [omega|].
        destruct H7 as (? & ? & ? & ? & ?).
        repeat split; auto.
        + hnf.
          destruct (gv _thread_lock); try contradiction; simpl in *.
          rewrite Z.max_r by omega.
          rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr;
            rewrite Ptrofs.unsigned_repr; unfold N in *; try rep_omega.
        + destruct (gv _thread_lock); try contradiction; simpl in *.
          inv H23; try discriminate.
          constructor.
          intros; rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr;
            rewrite Ptrofs.unsigned_repr; unfold N in *; try rep_omega.
          simpl; rewrite <- Z.add_assoc, Zred_factor4.
          apply H29; omega. }
    - apply Z2Nat.inj; try omega.
      rewrite Nat2Z.id, Z2Nat.inj_sub by omega; simpl; omega. }
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
    rewrite !data_at__eq, !data_at_zero_array_eq; auto. }
  { (* second loop *)
    forward.
    replace (force_val _) with (thread_lock i)
      by (simpl; rewrite sem_add_pi_ptr_special; auto; unfold N in *; simpl in *; rep_omega).
    Opaque upto.
    rewrite sublist_next with (i0 := i) by (auto; rewrite Zlength_upto, Z2Nat.id; omega); simpl.
    rewrite Znth_upto by (simpl; unfold N in *; omega).
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
    rewrite sublist_split with (mid := i) in Hshs, Hgshs by omega.
    rewrite sublist_next with (i0 := i) in Hshs by omega.
    rewrite sublist_next with (i0 := i) in Hgshs by omega.
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
    rewrite !(sublist_split 0 i (i + 1)), !sublist_len_1 by omega.
    Exists sh' gsh'; entailer!.
    { split; eapply sepalg_list.list_join_app; eauto; econstructor; eauto; constructor. }
    rewrite Z2Nat.inj_add by omega.
    rewrite !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
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
    { intro X; contradiction unreadable_bot.
      rewrite <- X; eapply readable_share_list_join; eauto. }
    { intro X; contradiction unreadable_bot.
      rewrite <- X; apply Forall_Znth; auto; omega. }
    { eapply readable_share_list_join; eauto. }
    { apply Forall_Znth; auto; omega. } }
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
