Require Import mailbox.verif_atomic_exchange.
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.
Require Import VST.zlist.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.

Opaque upto.
Opaque eq_dec.

Section mpred.

Context `{!VSTGS unit Σ, AEGS0 : !AEGS t_atom_int, !inG Σ (excl_authR (leibnizO val))}.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  rename a into gv.
  sep_apply (create_mem_mgr gv).
  exploit (split_shares (Z.to_nat N) Ews); auto; intros (sh0 & shs & ? & ? & ? & ?).
  forward_call (sh0, shs, gv).
  Intros x; destruct x as (((((((comms, bufs), reads), lasts), g), g0), g1), g2).
  assert_PROP (Zlength comms = N).
  { go_lowerx; apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold N; lia|].
    unfold unfold_reptype; simpl.
    apply bi.pure_mono; tauto. }
  simpl fst in *. simpl snd in *.
  assert_PROP (Zlength bufs = B) by entailer!.
  assert (exists sh2, sepalg.join sh0 sh2 Ews /\ readable_share sh2) as (sh2 & Hsh2 & Hrsh2).
  { destruct (sepalg_list.list_join_assoc1 (join_bot_eq _) H2) as (? & ? & ?).
    do 2 eexists; eauto.
    eapply readable_share_list_join; eauto.
    inv H1; auto; discriminate. }
  forward_spawn _writer (vptrofs 0) (comms, bufs, sh0, (1/2)%Qp, gsh2, shs, g, g0, g1, g2, gv).
  { rewrite !sepcon_andp_prop'.
    apply andp_right; [apply prop_right; repeat (split; auto)|].
    erewrite (map_ext (fun r => comm_loc _ _ _ _ _ _ _ _ _ _ _));
      [|intro; unfold comm_loc; erewrite <- AE_loc_join with (h1 := empty_map)(h2 := empty_map);
        try apply incl_compatible; eauto; reflexivity].
    rewrite !sepcon_map.
    do 3 (erewrite <- (data_at_shares_join_old Ews); eauto).
    rewrite (extract_nth_sepcon (map (data_at _ _ _) (sublist 1 _ bufs)) 0), Znth_map;
      rewrite ?Zlength_map, ?Zlength_sublist; try (unfold B, N in *; lia).
    erewrite <- (data_at_shares_join Ews tbuffer) by eauto.
    rewrite (sepcon_comm (data_at sh0 _ _ (Znth 0 (sublist _ _ bufs)))),
      (sepcon_assoc _ (data_at sh0 _ _ (Znth 0 (sublist _ _ bufs)))).
    rewrite replace_nth_sepcon. 2 : {
      rewrite Zlength_map.
      rewrite Zlength_sublist; unfold B, N in *; lia.
    }
    unfold comm_loc; cancel.
    rewrite (sepcon_comm _ ([∗] (upd_Znth 0 _ _))), !sepcon_assoc.
    rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at sh0 tbuffer _ _)), !sepcon_assoc.
    rewrite <- sepcon_assoc; apply sepcon_derives; [|cancel].
    assert (Zlength (data_at sh0 tbuffer (vint 0) (Znth 0 bufs)
         :: upd_Znth 0 (map (data_at Ews tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs))
              (data_at sh0 tbuffer (vint 0) (Znth 0 (sublist 1 (Zlength bufs) bufs)))) = B) as Hlen.
    { rewrite Zlength_cons, upd_Znth_Zlength; rewrite Zlength_map, Zlength_sublist, ?Zlength_upto;
        simpl; unfold B, N in *; lia. }
    apply sepcon_list_derives with (l1 := _ :: _).
    { rewrite Zlength_map; auto. }
    intros; rewrite Hlen in *.
    erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; simpl; try (unfold B, N in *; lia).
    destruct (eq_dec i 0); [|destruct (eq_dec i 1)].
    - subst; rewrite Znth_0_cons.
      Exists sh0 0; entailer'.
    - subst; rewrite Znth_pos_cons, Zminus_diag, upd_Znth_same; rewrite ?Zlength_map, ?Zlength_sublist; try lia.
      rewrite Znth_sublist; try lia.
      Exists sh0 0; entailer'.
    - rewrite Znth_pos_cons, upd_Znth_diff; rewrite ?Zlength_map, ?Zlength_sublist; try lia.
      erewrite Znth_map; [|rewrite Zlength_sublist; lia].
      rewrite Znth_sublist; try lia.
      rewrite Z.sub_simpl_r.
      Exists Ews 0; entailer'. }
  rewrite Znth_sublist; try (unfold B, N in *; lia).
  rewrite <- seq_assoc.
  assert_PROP (Zlength reads = N) by entailer!.
  assert_PROP (Zlength lasts = N) by entailer!.
  forward_for_simple_bound N (∃ i : Z, PROP ( )
   LOCAL (gvars gv)
   SEP (∃ sh' : share, ⌜sepalg_list.list_join sh0 (sublist i N shs) sh'⌝ ∧
          data_at sh' (tarray (tptr tint) N) lasts (gv _last_read) * data_at sh' (tarray (tptr tint) N) reads (gv _reading);
        [∗] (map (fun sh => data_at sh (tarray (tptr t_atom_int) N) comms (gv _comm)) (sublist i N shs));
        [∗] (map (fun sh => data_at sh (tarray (tptr tbuffer) B) bufs (gv _bufs)) (sublist i N shs));
        [∗] (map (fun x => comm_loc gsh2 (Znth x comms)
          (Znth x g) (Znth x g0) (Znth x g1) (Znth x g2) bufs (Znth x shs) empty_map) (sublist i N (upto (Z.to_nat N))));
        [∗] (map (ghost_var gsh1 (vint 1)) (sublist i N g0));
        [∗] (map (data_at_ Ews tint) (sublist i N reads));
        [∗] (map (data_at_ Ews tint) (sublist i N lasts));
        [∗] (map (malloc_token Ews tbuffer) bufs);
        [∗] (map (malloc_token Ews tint) reads);
        [∗] (map (malloc_token Ews tint) lasts);
        [∗] (map (fun sh => data_at sh tbuffer (vint 0) (Znth 1 bufs)) (sublist i N shs));
        mem_mgr gv; has_ext tt)).
  { unfold N; computable. }
  { Exists Ews; rewrite !sublist_same; auto; unfold N.
  rewrite iter_sepcon_fold_right_sepcon.
    entailer!. apply derives_refl. }
  { Intros sh'.
    forward_call (tint, gv). Intros d.
    forward.
    match goal with H : sepalg_list.list_join sh0 _ sh' |- _ => rewrite sublist_next in H;
      auto; [inversion H as [|????? Hj1 Hj2]; subst |
      match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; lia end] end.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh1' & ? & Hj').
    assert_PROP (isptr d) by entailer!.
    forward_spawn _reader d (i, reads, lasts, comms,
      bufs, Znth i shs, Znth i shs, Znth i g, Znth i g0, Znth i g1, Znth i g2, gv).
    - rewrite !sepcon_andp_prop'.
      apply andp_right; [apply prop_right; repeat (split; auto)|].
      { apply Forall_Znth; auto; match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; auto end. }
      { apply Forall_Znth; auto; match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; auto end. }
      { apply Forall_Znth; auto; match goal with H : Zlength comms = _ |- _ => setoid_rewrite H; auto end. }
      rewrite <- !(data_at_share_join _ _ _ _ _ _ Hj').
      rewrite (@sublist_next Share.t _ i); auto;
        [simpl | match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; lia end].
      simpl in *; rewrite !(@sublist_next val _ i); auto; try lia; simpl;
        try (unfold N in *; lia).
      simpl in *; rewrite !(@sublist_next gname _ i); auto; try lia; simpl;
        try (unfold N in *; lia).
      rewrite (@sublist_next Z N i); rewrite ?Znth_upto; auto; rewrite? Zlength_upto; simpl;
        try (unfold N in *; lia).
      Exists 0; cancel.
    - (* Why didn't forward_call discharge this? *) apply isptr_is_pointer_or_null; auto.
    - Exists sh1'; entailer!. simpl; cancel. }
    forward_loop (PROP()LOCAL()(SEP(TT))) break: (@FF (environ->mpred) _).
    entailer!.
    forward. entailer!.
Qed.

End mpred.
