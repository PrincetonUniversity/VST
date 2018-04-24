Require Import mailbox.general_atomics.
Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox_bad.
Require Import mailbox.verif_mailbox_bad_specs.

Set Bullet Behavior "Strict Subproofs".

Lemma body_initialize_reader : semax_body Vprog Gprog f_initialize_reader initialize_reader_spec.
Proof.
  start_function.
  rewrite (data_at__isptr _ tint); Intros.
  assert_PROP (Zlength reads = N) by entailer!.
  assert (0 <= r < N) as Hr.
  { exploit (Znth_inbounds r reads Vundef); [|omega].
    intro Heq; rewrite Heq in *; contradiction. }
  forward.
  forward.
  forward.
  forward.
  forward.
Qed.

Lemma body_start_read : semax_body Vprog Gprog f_start_read start_read_spec.
Proof.
  start_function.
  rewrite (data_at__isptr _ tint); Intros.
  assert_PROP (Zlength reads = N) by entailer!.
  assert (0 <= r < N) as Hr.
  { exploit (Znth_inbounds r reads Vundef); [|omega].
    intro Heq; rewrite Heq in *; contradiction. }
  forward.
  forward.
  forward.
  set (c := Znth r comms Vundef).
  forward_call (AEX_SC_witness c (-1)
    ((if good then EX v : _, data_at sh tbuffer (Vint v) (Znth b0 bufs Vundef) else emp) *
     ghost_var gsh1 (vint b0) g0 * ghost_hist sh2 h g)
    (fun _ : Z => comm_inv good c bufs sh g g0 g1 g2 gsh2) [0]
    (fun b => let b' := if (Z.leb 0 b && Z.ltb b B)%bool then b else b0 in
      !!(-1 <= b' < B /\ (good = true -> -1 <= b < B)) &&
      (if good then EX v : _, data_at sh tbuffer (Vint v) (Znth b' bufs Vundef) else emp) *
      ghost_var gsh1 (vint b') g0 *
      EX t : _, !!(newer h t) && ghost_hist sh2 (h ++ [(t, AE (vint b) Empty)]) g)).
  { simpl; unfold comm_loc; cancel. }
  { split; [split; computable|].
    apply wand_view_shifts2; simpl.
    assert (sh2 <> Share.bot) by (intro; subst; contradiction unreadable_bot).
    unfold comm_inv.
    view_shift_intro v0; view_shift_intros.
    if_tac.
    - view_shift_intro v'; view_shift_intro l.
      unfold comm_R at 1.
      view_shift_intro b1; view_shift_intro b2; view_shift_intros.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_ref _ _)).
      rewrite (sepcon_comm _ (ghost_hist _ _ _)).
      rewrite <- !sepcon_assoc, 7sepcon_assoc.
      apply view_shift_assert with (PP := hist_incl h l).
      { apply sepcon_derives_prop, hist_ref_incl; auto. }
      intros ?%hist_incl_lt.
      etransitivity; [apply view_shift_sepcon1, hist_add'; auto|].
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g0)).
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh1 _ g0)).
      erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto.
      view_shift_intros.
      exploit (repr_inj_signed b1 b0); auto.
      { apply repable_buf; omega. }
      intro; subst.
      rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1,
        ghost_var_update with (v'0 := vint (if eq_dec v0 (-1) then b0 else v0))|].
      erewrite <- ghost_var_share_join by eauto.
      apply derives_view_shift; Exists Tsh v0; entailer!.
      { apply repable_buf; auto. }
      rewrite <- wand_sepcon_adjoint.
      rewrite <- !exp_sepcon1, <- !exp_sepcon2.
      Exists (length l) (-1); entailer!.
      { if_tac; auto; omega. }
      rewrite <- !exp_sepcon1, <- !exp_sepcon2.
      Exists (l ++ [AE (vint v0) Empty]); unfold comm_R.
      rewrite rev_app_distr; simpl; rewrite last_two_reads_cons; simpl; cancel.
      rewrite prev_taken_cons; unfold last_write; simpl.
      assert (apply_hist (vint 0) (l ++ [AE (vint v0) Empty]) = Some Empty).
      { rewrite apply_hist_app; replace (apply_hist _ _) with (Some (vint v0)); simpl.
        apply eq_dec_refl. }
      if_tac.
      + subst; simpl.
        Exists b0 b2 v'; entailer!.
        { rewrite Forall_app; repeat (constructor; auto).
          exists (-1), (-1); repeat split; auto; omega. }
        rewrite sepcon_comm; auto.
      + destruct (eq_dec (vint v0) Empty).
        { apply Empty_inj in e; auto; contradiction. }
        Intros v''; Exists v'' v0 b0 v'.
        rewrite Zle_imp_le_bool, Fcore_Zaux.Zlt_bool_true by omega; simpl; entailer!.
        replace (last_two_reads _) with (vint b0, vint b2).
        rewrite Forall_app; repeat constructor; auto.
        exists v0, (-1); repeat split; auto; omega.
    - view_shift_intro l.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_ref _ _)).
      rewrite (sepcon_comm _ (ghost_hist _ _ _)).
      rewrite !sepcon_emp, <- !sepcon_assoc, 5sepcon_assoc.
      apply view_shift_assert with (PP := hist_incl h l).
      { apply sepcon_derives_prop, hist_ref_incl; auto. }
      intros ?%hist_incl_lt.
      etransitivity; [apply view_shift_sepcon1, hist_add'; auto|].
      view_shift_intro b0'.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g0)).
      rewrite <- !exp_sepcon1.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh1 _ g0)).
      erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto.
      rewrite !sepcon_andp_prop'; apply view_shift_prop; intro; subst.
      rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, ghost_var_update|].
      erewrite <- ghost_var_share_join by eauto.
      apply derives_view_shift; Exists Tsh (Int.signed (Int.repr v0)).
      rewrite sepcon_andp_prop'; apply andp_right.
      { entailer!.
        apply Int.signed_range. }
      rewrite Int.repr_signed; cancel.
      rewrite <- wand_sepcon_adjoint; cancel.
      set (v0' := Int.signed (Int.repr v0)).
      Exists (-1) (length l) (vint (if ((0 <=? v0') && (v0' <? B))%bool then v0' else b0))
        (l ++ [AE (vint v0) Empty]); entailer!.
      { rewrite <- and_assoc; split; [|discriminate].
        pose proof (Zle_cases 0 v0'); destruct (0 <=? v0'); simpl; try omega.
        pose proof (Zlt_cases v0' B); destruct (v0' <? B); omega. }
      rewrite (sepcon_comm _ (ghost_ref _ _)), !sepcon_assoc; apply sepcon_derives; auto; entailer!.
      rewrite sepcon_comm; auto. }
  Intros b.
  match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROP () (LOCALx (temp _t'2 (Val.of_bool (Z.leb 0 b && Z.ltb b B)) :: Q) (SEPx R))) end.
  { forward.
    entailer!.
    rewrite Zle_imp_le_bool by omega; simpl.
    unfold Int.lt, Int.add; simpl.
    rewrite !Int.signed_repr by (auto; computable).
    pose proof (Zlt_cases b B); if_tac; destruct (b <?B); auto; unfold B, N in *; omega. }
  { forward.
    entailer!.
    rewrite Fcore_Zaux.Zle_bool_false; auto. }
  set (b' := if ((0 <=? b) && (b <? B))%bool then b else b0) in * |- *.
  Intros t.
  forward_if (PROP () LOCAL (temp _b (vint b'); temp _rr (Znth r reads Vundef); temp _r (vint r);
      gvar _reading reading; gvar _last_read last_read; gvar _comm comm)
    SEP (comm_loc good sh2 c g g0 g1 g2 bufs sh gsh2 (h ++ [(t, AE (vint b) Empty)]);
         if good then EX v : _, data_at sh tbuffer (Vint v) (Znth b' bufs Vundef) else emp;
         ghost_var gsh1 (vint b') g0;
         data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
         data_at_ Tsh tint (Znth r reads Vundef); data_at Tsh tint (vint b') (Znth r lasts Vundef);
         data_at sh1 (tarray (tptr tint) N) comms comm)).
  - forward.
    replace b' with b by (subst b'; if_tac; auto; discriminate).
    entailer!.
  - forward.
    replace b' with b0 by (subst b'; if_tac; auto; discriminate).
    entailer!.
  - forward.
    forward.
    Exists b' t b; entailer!.
    split.
    + pose proof (Zle_cases 0 b); destruct (0 <=? b); subst b'; simpl; try if_tac; omega.
    + destruct (eq_dec b (-1)); subst.
      { rewrite latest_read_Empty; auto. }
      destruct ((0 <=? b) && (b <? B))%bool eqn: Hb; subst b'.
      * apply latest_read_new; auto; omega.
      * apply latest_read_bad; auto.
        rewrite andb_false_iff, Z.leb_nle, Z.ltb_nlt in Hb; omega.
Qed.

Lemma body_finish_read : semax_body Vprog Gprog f_finish_read finish_read_spec.
Proof.
  start_function.
  rewrite (data_at__isptr _ tint); Intros.
  assert_PROP (Zlength reads = N) by entailer!.
  assert (0 <= r < N) as Hr.
  { exploit (Znth_inbounds r reads Vundef); [|omega].
    intro Heq; rewrite Heq in *; contradiction. }
  forward.
  forward.
  forward.
Qed.
