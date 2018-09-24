Require Import mailbox.verif_atomic_exchange.
Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.
Set Bullet Behavior "Strict Subproofs".

Opaque upto.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  simpl readonly2share.  (* TODO: delete this line when possible *)
  exploit (split_shares (Z.to_nat N) Ews); auto; intros (sh0 & shs & ? & ? & ? & ?).
  rewrite (data_at__eq _ (tarray (tptr (Tstruct _lock_t noattr)) N)), lock_struct_array.
  forward_call (sh0, shs, gv).
  { fast_cancel. }
  Intros x; destruct x as ((((((((comms, locks), bufs), reads), lasts), g), g0), g1), g2).
  assert_PROP (Zlength comms = N).
  { go_lowerx; apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold N; omega|].
    unfold unfold_reptype; simpl.
    apply prop_left; intros (? & ? & ?); apply prop_right; auto. }
  simpl fst in *. simpl snd in *.
  assert_PROP (Zlength bufs = B).
  { go_lowerx; rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ (gv _bufs))), !sepcon_assoc.
    apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold B, N; omega|].
    unfold unfold_reptype; simpl.
    apply prop_left; intros (? & ? & ?); apply prop_right; auto. }
  assert (exists sh2, sepalg.join sh0 sh2 Ews /\ readable_share sh2) as (sh2 & Hsh2 & Hrsh2).
  { destruct (sepalg_list.list_join_assoc1 (join_bot_eq _) H2) as (? & ? & ?).
    do 2 eexists; eauto.
    eapply readable_share_list_join; eauto.
    inv H1; auto; discriminate. }
  forward_spawn _writer (vint 0) (locks, comms, bufs, sh0, sh0, sh0, shs, g, g0, g1, g2, gv).
  { rewrite !sepcon_andp_prop'.
    apply andp_right; [apply prop_right; repeat (split; auto)|].
    unfold comm_loc; erewrite map_ext;
      [|intro; erewrite <- AE_loc_join with (h1 := empty_map)(h2 := empty_map);
        try apply incl_compatible; eauto; reflexivity].
    rewrite !sepcon_map.
    do 3 (erewrite <- (data_at_shares_join Ews); eauto).
    rewrite (extract_nth_sepcon (map (data_at _ _ _) (sublist 1 _ bufs)) 0), Znth_map;
      rewrite ?Zlength_map, ?Zlength_sublist; try (unfold B, N in *; omega).
    erewrite <- (data_at_shares_join Ews tbuffer) by eauto.
    rewrite (sepcon_comm (data_at sh0 _ _ (Znth 0 (sublist _ _ bufs)))),
      (sepcon_assoc _ (data_at sh0 _ _ (Znth 0 (sublist _ _ bufs)))).
    rewrite replace_nth_sepcon.
    fast_cancel.
    rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right sepcon emp (upd_Znth 0 _ _))), !sepcon_assoc.
    rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at sh0 tbuffer _ _)), !sepcon_assoc.
    rewrite <- sepcon_assoc; apply sepcon_derives; [|cancel].
    assert (Zlength (data_at sh0 tbuffer (vint 0) (Znth 0 bufs)
         :: upd_Znth 0 (map (data_at Ews tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs))
              (data_at sh0 tbuffer (vint 0) (Znth 0 (sublist 1 (Zlength bufs) bufs)))) = B) as Hlen.
    { rewrite Zlength_cons, upd_Znth_Zlength; rewrite Zlength_map, Zlength_sublist, ?Zlength_upto;
        simpl; unfold B, N in *; omega. }
    apply sepcon_list_derives with (l1 := _ :: _).
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
      Exists Ews 0; entailer'. }
  rewrite Znth_sublist; try (unfold B, N in *; omega).
  rewrite <- seq_assoc.
  assert_PROP (Zlength reads = N) by entailer!.
  assert_PROP (Zlength lasts = N) by entailer!.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (gvars gv)
   SEP (EX sh' : share, !!(sepalg_list.list_join sh0 (sublist i N shs) sh') &&
          data_at sh' (tarray (tptr tint) N) lasts (gv _last_read) * data_at sh' (tarray (tptr tint) N) reads (gv _reading);
        fold_right sepcon emp (map (fun sh => data_at sh (tarray (tptr tint) N) comms (gv _comm)) (sublist i N shs));
        fold_right sepcon emp (map (fun sh => data_at sh (tarray (tptr tlock) N) locks (gv _lock)) (sublist i N shs));
        fold_right sepcon emp (map (fun sh => data_at sh (tarray (tptr tbuffer) B) bufs (gv _bufs)) (sublist i N shs));
        fold_right sepcon emp (map (fun x => comm_loc sh2 (Znth x locks) (Znth x comms)
          (Znth x g) (Znth x g0) (Znth x g1) (Znth x g2) bufs (Znth x shs) gsh2
          empty_map) (sublist i N (upto (Z.to_nat N))));
        fold_right sepcon emp (map (ghost_hist(hist_el := AE_hist_el) Ish empty_map) g);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) (sublist i N g0));
        fold_right sepcon emp (map (data_at_ Ews tint) (sublist i N reads));
        fold_right sepcon emp (map (data_at_ Ews tint) (sublist i N lasts));
        fold_right sepcon emp (map (malloc_token Tsh tint) comms);
        fold_right sepcon emp (map (malloc_token Tsh tlock) locks);
        fold_right sepcon emp (map (malloc_token Tsh tbuffer) bufs);
        fold_right sepcon emp (map (malloc_token Tsh tint) reads);
        fold_right sepcon emp (map (malloc_token Tsh tint) lasts);
        fold_right sepcon emp (map (fun sh => @data_at CompSpecs sh tbuffer (vint 0) (Znth 1 bufs)) (sublist i N shs)))).
  { unfold N; computable. }
  { Exists Ews; rewrite !sublist_same; auto; unfold N; entailer!.
    apply derives_refl. }
  { Intros sh'.
    forward_call tint. split3; simpl; auto; computable. Intros d.
    forward.
    match goal with H : sepalg_list.list_join sh0 _ sh' |- _ => rewrite sublist_next in H;
      auto; [inversion H as [|????? Hj1 Hj2]; subst |
      match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; omega end] end.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh1' & ? & Hj').
    assert_PROP (isptr d) by entailer!.
    forward_spawn _reader d (i, reads, lasts, locks, comms,
      bufs, Znth i shs, sh2, Znth i shs, Znth i g, Znth i g0, Znth i g1, Znth i g2, gv).
    - rewrite !sepcon_andp_prop'.
      apply andp_right; [apply prop_right; repeat (split; auto)|].
      { apply Forall_Znth; auto; match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; auto end. }
      { apply Forall_Znth; auto; match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; auto end. }
      { apply Forall_Znth; auto; match goal with H : Zlength comms = _ |- _ => setoid_rewrite H; auto end. }
      rewrite <- !(data_at_share_join _ _ _ _ _ _ Hj').
      rewrite (@sublist_next Share.t _ i); auto;
        [simpl | match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; omega end].
      simpl in *; rewrite !(@sublist_next val _ i); auto; try omega; simpl;
        try (unfold N in *; omega).
      simpl in *; rewrite !(@sublist_next gname _ i); auto; try omega; simpl;
        try (unfold N in *; omega).
      rewrite (@sublist_next Z N i); rewrite ?Znth_upto; auto; rewrite? Zlength_upto; simpl;
        try (unfold N in *; omega).
      Exists 0; cancel.
    - (* Why didn't forward_call_dep discharge this? *) apply isptr_is_pointer_or_null; auto.
    - Exists sh1'; entailer!. }
    forward_loop (PROP()LOCAL()(SEP(TT))) break: (@FF (environ->mpred) _).
    entailer!.
    forward. entailer!.
Qed.
