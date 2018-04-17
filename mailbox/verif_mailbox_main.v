Require Import mailbox.verif_atomic_exchange.
Require Import VST.progs.conclib.
Require Import VST.progs.ghost.
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
  set (writer_ := gv _writer).
  make_func_ptr _writer.
(*  get_global_function'' _writer; Intros. 
  apply extract_exists_pre; intros writer_. *)
  exploit (split_shares (Z.to_nat N) Ews); auto; intros (sh1 & shs1 & ? & ? & ? & ?).
  assert_PROP (Zlength bufs = B).
  { go_lowerx; rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ buf)), !sepcon_assoc.
    apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold B, N; omega|].
    unfold unfold_reptype; simpl.
    apply prop_left; intros (? & ? & ?); apply prop_right; auto. }
  forward_spawn (val * val * val * val * val * val * list val * list val * list val *
                 share * share * share * list share * list gname * list gname * list gname * list gname)%type
    (writer_, vint 0, fun x : (val * val * val * val * val * val * list val * list val * list val * share * share *
      share * list share * list gname * list gname * list gname * list gname) =>
      let '(writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs,
            g, g0, g1, g2) := x in
      [(_writing, writing); (_last_given, last_given); (_last_taken, last_taken);
       (_lock, lock); (_comm, comm); (_bufs, buf)],
    (writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, gsh1, sh0, shs,
                       g, g0, g1, g2),
    fun (x : (val * val * val * val * val * val * list val * list val * list val *
              share * share * share * list share * list gname * list gname * list gname * list gname)%type)
        (arg : val) =>
    let '(writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs,
          g, g0, g1, g2) := x in
      fold_right sepcon emp [!!(fold_right and True [Zlength shs = N; readable_share sh1; readable_share lsh;
        Forall readable_share shs; sepalg_list.list_join sh0 shs Tsh;
        Zlength g1 = N; Zlength g2 = N; Forall isptr comms]) && emp;
        data_at_ Ews tint writing; data_at_ Ews tint last_given; data_at_ Ews (tarray tint N) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
        fold_right sepcon emp (map (fun r => comm_loc lsh (Znth r locks) (Znth r comms)
          (Znth r g) (Znth r g0) (Znth r g1) (Znth r g2) bufs
          (Znth r shs) gsh2 empty_map) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2);
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i 0 then sh = sh0 else if eq_dec i 1 then sh = sh0 else sh = Tsh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs)) (upto (Z.to_nat B)))]).
  { apply andp_right.
    { entailer!. }
    unfold spawn_pre, PROPx, LOCALx, SEPx.
    go_lowerx.
    rewrite !sepcon_andp_prop, !sepcon_andp_prop'.
    apply andp_right; [apply prop_right; auto|].
    apply andp_right; [apply prop_right; repeat split; auto|].
    apply andp_right; [apply prop_right; repeat split; auto|].
    apply andp_right; [apply prop_right|].
    { unfold liftx; simpl; unfold lift, make_args'; simpl.
      rewrite ?gvar_denote_env_set. 
      rewrite eval_id_same, eval_id_other, eval_id_same; [|discriminate].
     repeat split; auto; try apply gvar_denote_global; auto.
     erewrite gvar_eval_var by eauto.
     erewrite !(force_val_sem_cast_neutral_gvar' _writer writer_) by eauto.
     auto.
      }
    Exists _arg.
    rewrite !sepcon_assoc; apply sepcon_derives.
    { apply derives_refl'.
      f_equal; f_equal; extensionality; destruct x as (?, x); repeat destruct x as (x, ?); simpl.
      rewrite !sepcon_andp_prop'; extensionality.
      rewrite <- andp_assoc, prop_true_andp with (P := True); auto.
      rewrite (andp_comm (!! _) (!! _)), andp_assoc; f_equal; f_equal.
      rewrite emp_sepcon, !sepcon_emp; auto. }
    rewrite sepcon_andp_prop'.
    apply andp_right; [apply prop_right; repeat (split; auto)|].
    unfold comm_loc; erewrite map_ext;
      [|intro; erewrite <- AE_loc_join with (h1 := empty_map)(h2 := empty_map);
        try apply incl_compatible; eauto; reflexivity].
    rewrite !sepcon_map.
    do 3 (erewrite <- (data_at_shares_join Ews); eauto).
    rewrite (extract_nth_sepcon (map (data_at _ _ _) (sublist 1 _ bufs)) 0), Znth_map;
      rewrite ?Zlength_map, ?Zlength_sublist; try (unfold B, N in *; omega).
    erewrite <- (data_at_shares_join Tsh); eauto.
    rewrite (sepcon_comm (data_at sh0 _ _ (Znth 0  (sublist _ _ bufs)))),
      (sepcon_assoc _ (data_at sh0 _ _ _)).
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
          gvar _last_read last_read; gvar _reading reading; gvar _comm comm; gvar _lock lock; gvar _bufs buf)
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
    get_global_function'' _reader; Intros.
    apply extract_exists_pre; intros reader_.
    match goal with H : sepalg_list.list_join sh1 _ sh' |- _ => rewrite sublist_next in H;
      auto; [inversion H as [|????? Hj1 Hj2]; subst |
      match goal with H : Zlength shs1 = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; omega end] end.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh1' & ? & Hj').
    forward_spawn (Z * val * val * val * val * val * list val * list val * list val * list val * list val *
                   share * share * share * gname * gname * gname * gname)%type
      (reader_, d, fun x : (Z * val * val * val * val * val * list val * list val * list val * list val *
        list val * share * share * share * gname * gname * gname * gname) =>
        let '(r, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs, sh1, sh2, sh,
              g, g0, g1, g2) := x in
        [(_reading, reading); (_last_read, last_read); (_lock, lock); (_comm, comm); (_bufs, buf)],
      (i, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs,
                    Znth i shs1, gsh2, Znth i shs, Znth i g, Znth i g0, Znth i g1, Znth i g2),
      fun (x : (Z * val * val * val * val * val * list val * list val * list val * list val * list val *
                share * share * share * gname * gname * gname * gname)%type) (arg : val) =>
        let '(r, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs, sh1, sh2, sh,
              g, g0, g1, g2) := x in
        fold_right sepcon emp [!!(fold_right and True [readable_share sh; readable_share sh1; 
          readable_share sh2; isptr (Znth r comms)]) && emp;
          data_at Tsh tint (vint r) arg; malloc_token Tsh tint arg;
          data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
          data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
          data_at_ Tsh tint (Znth r reads); data_at_ Tsh tint (Znth r lasts);
          data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
          comm_loc sh2 (Znth r locks) (Znth r comms) g g0 g1 g2 bufs sh gsh2 empty_map;
          EX v : Z, data_at sh tbuffer (vint v) (Znth 1 bufs);
          ghost_var gsh1 (vint 1) g0]).
    - apply andp_right.
      { entailer!. }
      unfold spawn_pre. simpl fst in *. simpl snd in *.
      assert_PROP (isptr d) by (entailer!; eauto).
      unfold spawn_pre, PROPx, LOCALx, SEPx.
      go_lowerx.
      rewrite !sepcon_andp_prop, !sepcon_andp_prop'.
      apply andp_right; [apply prop_right; auto|].
      apply andp_right; [apply prop_right; repeat split; auto|].
      apply andp_right; [apply prop_right; repeat split; auto|].
      apply andp_right; [apply prop_right|].
      { unfold liftx; simpl; unfold lift, make_args'; simpl.
        erewrite gvar_eval_var, !(force_val_sem_cast_neutral_gvar' _ reader_) by eauto.
        rewrite eval_id_same, eval_id_other, eval_id_same; [|discriminate].
        replace (eval_id _d rho) with d.
        rewrite force_val_sem_cast_neutral_isptr'; rewrite force_val_sem_cast_neutral_isptr'; auto.
        repeat split; auto; apply gvar_denote_global; auto. }
      Exists _arg.
      rewrite !sepcon_assoc; apply sepcon_derives.
      { apply derives_refl'.
        f_equal; f_equal; extensionality; destruct x as (?, x); repeat destruct x as (x, ?); simpl.
        rewrite !sepcon_andp_prop'; extensionality.
        rewrite <- andp_assoc, prop_true_andp with (P := True); auto.
        rewrite (andp_comm (!! _) (!! _)), andp_assoc; f_equal; f_equal.
        rewrite emp_sepcon, !sepcon_emp; auto. }
      rewrite sepcon_andp_prop'.
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
    - Exists sh1'; entailer!. }
    forward_loop (PROP()LOCAL()(SEP(TT))) break: (@FF (environ->mpred) _).
    entailer!.
    forward. entailer!.
Qed.
