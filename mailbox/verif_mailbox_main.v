Require Import mailbox.verif_atomic_exchange.
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.
Require Import VST.zlist.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.

Opaque upto.
Opaque eq_dec.
Opaque N.

Section mpred.

Context `{!VSTGS unit Σ, AEGS0 : !AEGS t_atom_int, !inG Σ (excl_authR (leibnizO val))}.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  change 3 with N; change 5 with B.
  sep_apply (create_mem_mgr gv).
  exploit (split_shares (Z.to_nat N) Ews); auto; intros (sh0 & shs & ? & ? & ? & ?).
  forward_call (sh0, shs, gv).
  Intros x; destruct x as (((((((comms, bufs), reads), lasts), g), g0), g1), g2).
  assert_PROP (Zlength comms = N) by entailer!.
  simpl fst in *. simpl snd in *.
  assert_PROP (Zlength bufs = B) by entailer!.
  assert (exists sh2, sepalg.join sh0 sh2 Ews /\ readable_share sh2) as (sh2 & Hsh2 & Hrsh2).
  { destruct (sepalg_list.list_join_assoc1 (join_bot_eq _) H2) as (? & ? & ?).
    do 2 eexists; eauto.
    eapply readable_share_list_join; eauto.
    inv H1; auto; discriminate. }
  assert (B > 1) by done.
  forward_spawn _writer (vptrofs 0) (comms, bufs, sh0, (1/2)%Qp, sh0, shs, g, g0, g1, g2, gv).
  { entailer!.
    do 2 (erewrite <- (data_at_shares_join Ews); eauto).
    assert ([∗] map (fun r => comm_loc 1 (Znth r comms) (Znth r g) (Znth r g0)
            (Znth r g1) (Znth r g2) bufs (Znth r shs) ∅) (upto (Z.to_nat N)) ⊢
       [∗] map (fun r => comm_loc (1/2) (Znth r comms) (Znth r g) (Znth r g0)
           (Znth r g1) (Znth r g2) bufs (Znth r shs) ∅ ∗
           comm_loc (1/2) (Znth r comms) (Znth r g) (Znth r g0)
           (Znth r g1) (Znth r g2) bufs (Znth r shs) ∅) (upto (Z.to_nat N))) as ->.
    { f_equiv.
      rewrite Forall2_forall_Znth; split; first done.
      intros i Hi; rewrite Zlength_map in Hi; rewrite !Znth_map; [|done..].
      rewrite Zlength_upto in Hi; rewrite Znth_upto //; [|done..].
      rewrite /comm_loc AE_loc_join frac_op Qp.half_half //. }
    rewrite big_sep_map; cancel.
    assert (0 <= 0%nat < Zlength (sublist 1 (Zlength bufs) bufs)).
    { rewrite Zlength_sublist; lia. }
    rewrite (big_sepL_insert_acc _ (map _ (sublist 1 _ bufs)) (Z.to_nat O)).
    2: { apply Znth_lookup; rewrite Zlength_map //. }
    rewrite Znth_map; last done.
    erewrite <- (data_at_shares_join Ews tbuffer) by eauto.
    iIntros "(? & ? & ? & ? & ? & ? & ? & ? & ? & H0 & ((H1 & ?) & Hrest) & ?)";
      iSplitL "H0 H1 Hrest"; last by iStopProof; cancel.
    iSpecialize ("Hrest" with "H1").
    change (upto (Z.to_nat B)) with (0 :: map Z.succ (upto (Z.to_nat (B - 1)))); simpl map.
    iSplitL "H0"; first eauto.
    iStopProof; f_equiv.
    rewrite list_insert_upd; last rewrite Zlength_map //.
    rewrite Forall2_forall_Znth Zlength_upd_Znth !Zlength_map Zlength_upto Zlength_sublist; [|lia..].
    split; first lia.
    intros i Hi; rewrite !Znth_map; [|rewrite ?Zlength_map ?Zlength_upto; lia..].
    rewrite Znth_upto; [|lia].
    destruct (eq_dec (Z.succ i) 0); first lia.
    destruct (eq_dec i 0).
    - subst; rewrite upd_Znth_same; last by rewrite Zlength_map.
      if_tac; last done.
      rewrite Znth_sublist; [|lia..].
      Exists sh0 0; entailer!.
    - rewrite upd_Znth_diff; [|rewrite ?Zlength_map ?Zlength_sublist; lia..].
      rewrite Znth_map; [|rewrite Zlength_sublist; lia].
      rewrite Znth_sublist; [|lia..].
      Exists Ews 0; entailer!.
      if_tac; auto; lia. }
  rewrite Znth_sublist; [|lia..].
  rewrite <- seq_assoc.
  assert_PROP (Zlength reads = N) by entailer!.
  assert_PROP (Zlength lasts = N) by entailer!.
  forward_for_simple_bound N (∃ i : Z, PROP ( )
   LOCAL (gvars gv)
   SEP (∃ sh' : share, ⌜sepalg_list.list_join sh0 (sublist i N shs) sh'⌝ ∧
          data_at sh' (tarray (tptr tint) N) lasts (gv _last_read) ∗ data_at sh' (tarray (tptr tint) N) reads (gv _reading);
        [∗ list] sh ∈ sublist i N shs, data_at sh (tarray (tptr t_atom_int) N) comms (gv _comm);
        [∗ list] sh ∈ sublist i N shs, data_at sh (tarray (tptr tbuffer) B) bufs (gv _bufs);
        [∗] (map (fun x => comm_loc (1/2) (Znth x comms)
          (Znth x g) (Znth x g0) (Znth x g1) (Znth x g2) bufs (Znth x shs) ∅) (sublist i N (upto (Z.to_nat N))));
        [∗] (map (ghost_frag (vint 1)) (sublist i N g0));
        [∗] (map (data_at_ Ews tint) (sublist i N reads));
        [∗] (map (data_at_ Ews tint) (sublist i N lasts));
        [∗] (map (malloc_token Ews tbuffer) bufs);
        [∗] (map (malloc_token Ews tint) reads);
        [∗] (map (malloc_token Ews tint) lasts);
        [∗ list] sh ∈ sublist i N shs, data_at sh tbuffer (vint 0) (Znth 1 bufs);
        mem_mgr gv; has_ext tt)).
  { done. }
  { Exists Ews; rewrite !sublist_same; auto.
    entailer!. apply derives_refl. }
  Intros sh'.
  forward_call (tint, gv). Intros d.
  forward.
  match goal with H : sepalg_list.list_join sh0 _ sh' |- _ => rewrite sublist_next in H;
    auto; [inversion H as [|????? Hj1 Hj2]; subst |
    match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; lia end] end.
  apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh1' & ? & Hj').
  assert_PROP (isptr d) by entailer!.
  forward_spawn _reader d (i, reads, lasts, comms,
    bufs, Znth i shs, (1/2)%Qp, Znth i shs, Znth i g, Znth i g0, Znth i g1, Znth i g2, gv).
  - entailer!!.
    { split; apply Forall_Znth; auto; lia. }
    rewrite <- !(data_at_share_join _ _ _ _ _ _ Hj').
    rewrite (@sublist_next Share.t _ i); auto;
      [|match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; lia end].
    rewrite !(@sublist_next val _ i); [|lia..].
    rewrite !(@sublist_next gname _ i); [|lia..].
    rewrite (@sublist_next Z N i); rewrite ?Znth_upto; auto; rewrite ?Zlength_upto //.
    Exists 0; simpl; cancel.
  - (* Why didn't forward_call discharge this? *) apply isptr_is_pointer_or_null; auto.
  - Exists sh1'; entailer!. simpl; cancel.
  - forward_loop (True : assert) break: (False : assert); auto.
    forward. done.
Qed.

End mpred.
