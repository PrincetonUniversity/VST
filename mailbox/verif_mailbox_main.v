Require Import mailbox.verif_atomic_exchange.
Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.
Set Bullet Behavior "Strict Subproofs".

Opaque upto.

Lemma gvar_denote_env_set:
  forall rho i vi j vj, gvar_denote i vi (env_set rho j vj) = gvar_denote i vi rho.
Proof.
intros.
unfold gvar_denote.
simpl. auto.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  simpl readonly2share.  (* TODO: delete this line when possible *)
  assert_gvar _bufs. assert_gvar _lock. assert_gvar _comm. assert_gvar _reading.
  assert_gvar _last_read. assert_gvar _last_taken. assert_gvar _writing.
  assert_gvar _last_given.
  forget (gv _bufs) as buf.
  forget (gv _lock) as lock.
  forget (gv _comm) as comm.
  forget (gv _reading) as reading.
  forget (gv _last_read) as last_read.
  forget (gv _last_taken) as last_taken.
  forget (gv _writing) as writing.
  forget (gv _last_given) as last_given.
(*
  set (buf := gv _bufs).
  set (lock := gv _lock).
  set (comm := gv _comm).
  set (reading := gv _reading).
  set (last_read := gv _last_read).
  set (last_taken := gv _last_taken).
  set (writing := gv _writing).
  set (last_given := gv _last_given).
*)  
  exploit (split_shares (Z.to_nat N) Tsh); auto; intros (sh0 & shs & ? & ? & ? & ?).
  rewrite (data_at__eq _ (tarray (tptr (Tstruct _lock_t noattr)) N)), lock_struct_array.
  forward_call (comm, lock, buf, reading, last_read, sh0, shs).
  { fast_cancel. }
  Intros x; destruct x as ((((((((comms, locks), bufs), reads), lasts), g), g0), g1), g2).
  assert_PROP (Zlength comms = N).
  { go_lowerx; apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold N; omega|].
    unfold unfold_reptype; simpl.
    apply prop_left; intros (? & ? & ?); apply prop_right; auto. }
  simpl fst in *. simpl snd in *.
  exploit (split_shares (Z.to_nat N) Ews); auto; intros (sh1 & shs1 & ? & ? & ? & ?).
  assert_PROP (Zlength bufs = B).
  { go_lowerx; rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ buf)), !sepcon_assoc.
    apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold B, N; omega|].
    unfold unfold_reptype; simpl.
    apply prop_left; intros (? & ? & ?); apply prop_right; auto. }
  forward_spawn _writer (vint 0) (writing, last_given, last_taken, lock, comm, buf, locks, comms,
                                  bufs, sh1, gsh1, sh0, shs, g, g0, g1, g2).
  { rewrite !sepcon_andp_prop'.
    apply andp_right; [apply prop_right; repeat (split; auto)|].
    unfold comm_loc; erewrite map_ext;
      [|intro; erewrite <- AE_loc_join with (h1 := empty_map)(h2 := empty_map);
        try apply incl_compatible; eauto; reflexivity].
    rewrite !sepcon_map.
    do 3 (erewrite <- (data_at_shares_join Ews); eauto).
    rewrite (extract_nth_sepcon (map (data_at _ _ _) (sublist 1 _ bufs)) 0), Znth_map;
      rewrite ?Zlength_map, ?Zlength_sublist; try (unfold B, N in *; omega).
    erewrite <- (data_at_shares_join Tsh) by eauto.
    rewrite (sepcon_comm (data_at sh0 _ _ (Znth 0  (sublist _ _ bufs)))),
      (sepcon_assoc _ (data_at sh0 _ _ (Znth 0  (sublist _ _ bufs)))).
    rewrite replace_nth_sepcon.
    fast_cancel.
    rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at sh0 _ _ _)).
    rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right sepcon emp (upd_Znth 0 _ _))), !sepcon_assoc.
    rewrite <- sepcon_assoc; apply sepcon_derives; [|cancel_frame].
    assert (Zlength (data_at sh0 tbuffer (vint 0) (Znth 0 bufs)
         :: upd_Znth 0 (map (data_at Tsh tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs))
              (data_at sh0 tbuffer (vint 0) (Znth 0 (sublist 1 (Zlength bufs) bufs)))) = B) as Hlen.
    { rewrite Zlength_cons, upd_Znth_Zlength; rewrite Zlength_map, Zlength_sublist, ?Zlength_upto;
        simpl; unfold B, N in *; omega. }
    rewrite sepcon_comm; apply sepcon_list_derives with (l1 := _ :: _).
    { rewrite Zlength_map; auto. }
    intros; rewrite Hlen in *.
    erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; simpl; try (unfold B, N in *; omega).
    destruct (eq_dec i 0); [|destruct (eq_dec i 1)].
    - subst; rewrite Znth_0_cons.
      Exists sh0 0; entailer'.
    - subst; rewrite Znth_pos_cons, Zminus_diag, upd_Znth_same; rewrite ?Zlength_map, ?Zlength_sublist; try omega.
      rewrite Znth_sublist; try omega.
      Exists sh0 0; entailer'.
    - rewrite Znth_pos_cons, upd_Znth_diff; rewrite ?Zlength_map, ?Zlength_sublist; try omega.
      erewrite Znth_map; [|rewrite Zlength_sublist; omega].
      rewrite Znth_sublist; try omega.
      rewrite Z.sub_simpl_r.
      Exists Tsh 0; entailer'. }
  rewrite Znth_sublist; try (unfold B, N in *; omega).
  rewrite <- seq_assoc.
  assert_PROP (Zlength reads = N) by entailer!.
  assert_PROP (Zlength lasts = N) by entailer!.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (gvar _last_given last_given; gvar _writing writing; gvar _last_taken last_taken;
          gvar _last_read last_read; gvar _reading reading; gvar _comm comm; gvar _lock lock;
          gvar _bufs buf; gvar _reader (gv _reader))
   SEP (EX sh' : share, !!(sepalg_list.list_join sh1 (sublist i N shs1) sh') &&
          data_at sh' (tarray (tptr tint) N) lasts last_read * data_at sh' (tarray (tptr tint) N) reads reading;
        fold_right sepcon emp (map (fun sh => data_at sh (tarray (tptr tint) N) comms comm) (sublist i N shs1));
        fold_right sepcon emp (map (fun sh => data_at sh (tarray (tptr tlock) N) locks lock) (sublist i N shs1));
        fold_right sepcon emp (map (fun sh => data_at sh (tarray (tptr tbuffer) B) bufs buf) (sublist i N shs1));
        fold_right sepcon emp (map (fun x => comm_loc gsh2 (Znth x locks) (Znth x comms)
          (Znth x g) (Znth x g0) (Znth x g1) (Znth x g2) bufs (Znth x shs) gsh2
          empty_map) (sublist i N (upto (Z.to_nat N))));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) (sublist i N g0));
        fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i N reads));
        fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i N lasts));
        fold_right sepcon emp (map (malloc_token Tsh tint) comms);
        fold_right sepcon emp (map (malloc_token Tsh tlock) locks);
        fold_right sepcon emp (map (malloc_token Tsh tbuffer) bufs);
        fold_right sepcon emp (map (malloc_token Tsh tint) reads);
        fold_right sepcon emp (map (malloc_token Tsh tint) lasts);
        fold_right sepcon emp (map (fun sh => @data_at CompSpecs sh tbuffer (vint 0) (Znth 1 bufs)) (sublist i N shs)))).
  { unfold N; computable. }
  { Exists Ews; rewrite !sublist_same; auto; unfold N; entailer!. apply derives_refl. }
  { Intros sh'.
    forward_call tint. split3; simpl; auto; computable. Intros d.
    forward.
    match goal with H : sepalg_list.list_join sh1 _ sh' |- _ => rewrite sublist_next in H;
      auto; [inversion H as [|????? Hj1 Hj2]; subst |
      match goal with H : Zlength shs1 = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; omega end] end.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh1' & ? & Hj').
    assert_PROP (isptr d) by entailer!.
    forward_spawn _reader d (i, reading, last_read, lock, comm, buf, reads, lasts, locks, comms,
      bufs, Znth i shs1, gsh2, Znth i shs, Znth i g, Znth i g0, Znth i g1, Znth i g2).
    - rewrite !sepcon_andp_prop'.
      apply andp_right; [apply prop_right; repeat (split; auto)|].
      { apply Forall_Znth; auto; match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; auto end. }
      { apply Forall_Znth; auto; match goal with H : Zlength shs1 = _ |- _ => setoid_rewrite H; auto end. }
      { apply Forall_Znth; auto; match goal with H : Zlength comms = _ |- _ => setoid_rewrite H; auto end. }
      rewrite <- !(data_at_share_join _ _ _ _ _ _ Hj').
      rewrite (@sublist_next Share.t _ i); auto;
        [simpl | match goal with H : Zlength shs1 = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; omega end].
      simpl in *; rewrite !(@sublist_next val _ i); auto; try omega; simpl;
        try (unfold N in *; omega).
      simpl in *; rewrite !(@sublist_next gname _ i); auto; try omega; simpl;
        try (unfold N in *; omega).
      rewrite (@sublist_next Z N i); rewrite ?Znth_upto; auto; rewrite? Zlength_upto; simpl;
        try (unfold N in *; omega).
      rewrite (@sublist_next Share.t _ i); auto; simpl.
      Exists 0; cancel.
      { match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; unfold N; omega end. }
    - (* Why didn't forward_call_dep discharge this? *) apply isptr_is_pointer_or_null; auto.
    - Exists sh1'; entailer!. }
    forward_loop (PROP()LOCAL()(SEP(TT))) break: (@FF (environ->mpred) _).
    entailer!.
    forward. entailer!.
Qed.
