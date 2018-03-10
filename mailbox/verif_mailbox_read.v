Require Import mailbox.verif_atomic_exchange.
Require Import VST.progs.conclib.
Require Import VST.progs.ghost.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.

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
  rewrite comm_loc_isptr; Intros.
  rewrite <- lock_struct_array.
  forward.
  forward.
  forward.
  set (c := Znth r comms Vundef).
  set (l := Znth r locks Vundef).
  forward_call (sh2, c, g, l, vint 0, Empty, h,
    fun h b => !!(b = Empty /\ latest_read h (vint b0)) &&
      (EX v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs Vundef)) * ghost_var gsh1 (vint b0) g0,
    comm_R bufs sh gsh2 g0 g1 g2, fun h b => EX b' : Z, !!((if eq_dec b Empty then b' = b0 else b = vint b') /\
      -1 <= b' < B /\ latest_read h (vint b')) &&
      (EX v : Z, data_at sh tbuffer (vint v) (Znth b' bufs Vundef)) * ghost_var gsh1 (vint b') g0).
  { repeat (split; auto); try computable.
    unfold AE_spec; intros.
    intros ??????? Ha.
    unfold comm_R; unfold comm_R at 1 in Ha.
    rewrite !rev_app_distr in Ha; simpl in Ha.
    rewrite !last_two_reads_cons, prev_taken_cons in Ha.
    unfold last_write in *; simpl in *.
    pose proof (last_two_reads_fst (rev hx)).
    rewrite flatten_sepcon_in_SEP.
    rewrite extract_exists_in_SEP; Intro b.
    rewrite extract_exists_in_SEP; Intro b1.
    rewrite extract_exists_in_SEP; Intro b2.
    rewrite <- flatten_sepcon_in_SEP.
    rewrite !sepcon_andp_prop', !sepcon_andp_prop.
    erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
    erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
    Intros; subst.
    assert (last_two_reads (rev hx) = (vint b1, vint b2)) as Hlast by assumption.
    rewrite <- sepcon_assoc, sepcon_comm, <- !sepcon_assoc, 3sepcon_assoc.
    assert_PROP (vint b1 = vint b0) as Hb1.
    { go_lowerx.
      do 2 apply sepcon_derives_prop.
      rewrite sepcon_comm; apply ghost_var_inj; auto. }
    rewrite Hb1 in *; erewrite ghost_var_share_join; eauto.
    rewrite flatten_sepcon_in_SEP.
    apply ghost_var_update with (v' := vint (if eq_dec (vint b) Empty then b0 else b)).
    eapply semax_pre, Ha.
    go_lowerx.
    assert (repable_signed b0) by (apply repable_buf; omega).
    rewrite (sepcon_comm _ (weak_precise_mpred _ && _)).
    rewrite <- emp_sepcon at 1; rewrite !sepcon_assoc; apply sepcon_derives.
    { apply andp_right; auto; eapply derives_trans; [|apply comm_R_precise]; auto. }
    Exists (-1) (if eq_dec (vint b) Empty then b0 else b) (if eq_dec (vint b) Empty then b2 else b0).
    rewrite !sepcon_andp_prop'.
    apply andp_right.
    { apply prop_right; repeat (split; [solve [auto; omega]|]).
      rewrite Forall_app; split; [split; [|constructor]; auto|].
      { repeat eexists; auto; omega. }
      destruct (eq_dec (vint b) Empty); rewrite Hlast; auto.
      split; [|split]; auto; apply repable_buf; auto. }
    erewrite <- ghost_var_share_join; eauto.
    rewrite eq_dec_refl; cancel.
    setoid_rewrite sepcon_comm at 3.
    Exists (if eq_dec (vint b) Empty then b0 else b).
    destruct (eq_dec (vint b) Empty).
    - assert (b = -1) by (apply Empty_inj; auto; apply repable_buf; auto).
      subst; rewrite eq_dec_refl; entailer!.
      rewrite latest_read_Empty; auto.
    - destruct (eq_dec b (-1)); [subst; contradiction n; auto|].
      entailer!.
      apply latest_read_new; auto.
      apply hist_incl_lt; auto. }
  Intros x b'; destruct x as (t, v). simpl fst in *; simpl snd in *.
  assert (exists b, v = vint b /\ -1 <= b < B /\ if eq_dec b (-1) then b' = b0 else b' = b) as (b & ? & ? & ?).
  { destruct (eq_dec v Empty); subst.
    - exists (-1); rewrite eq_dec_refl; split; auto; omega.
    - do 2 eexists; eauto; split; [omega|].
      destruct (eq_dec b' (-1)); [subst; contradiction n; auto | auto]. }
  exploit repable_buf; eauto; intro; subst.
  match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROP () (LOCALx (temp _t'2 (vint (if eq_dec b (-1) then 0 else 1)) :: Q) (SEPx R))) end.
  { forward.
    destruct (eq_dec b (-1)); [omega|].
    entailer!.
    destruct (Int.lt (Int.repr b) (Int.repr (3 + 2))) eqn: Hlt; auto.
    apply lt_repr_false in Hlt; auto; unfold repable_signed; try computable.
    unfold B, N in *; omega. }
  { forward.
    destruct (eq_dec b (-1)); [|omega].
    entailer!. }
  forward_if (PROP () LOCAL (temp _b (vint (if eq_dec b (-1) then b0 else b)); temp _rr (Znth r reads Vundef);
      temp _r (vint r); gvar _reading reading; gvar _last_read last_read; gvar _lock lock; gvar _comm comm)
    SEP (comm_loc sh2 l c g g0 g1 g2 bufs sh gsh2 (h ++ [(t, AE (vint b) Empty)]);
         EX v : Z, data_at sh tbuffer (vint v) (Znth (if eq_dec b (-1) then b0 else b) bufs Vundef);
         ghost_var gsh1 (vint b') g0;
         data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
         data_at_ Tsh tint (Znth r reads Vundef);
         data_at Tsh tint (vint (if eq_dec b (-1) then b0 else b)) (Znth r lasts Vundef);
         data_at sh1 (tarray (tptr tint) N) comms comm;
         data_at sh1 (tarray (tptr (Tstruct _lock_t noattr)) N) locks lock)).
  - forward.
    simpl eq_dec; destruct (eq_dec b (-1)); [match goal with H : _ <> _ |- _ => contradiction H; auto end|].
    entailer!. apply derives_refl.
  - forward.
    simpl eq_dec; destruct (eq_dec b (-1)); [|discriminate].
    entailer!. apply derives_refl.
  - forward.
    forward.
    Exists (if eq_dec b (-1) then b0 else b) t (vint b) v.
    apply andp_right.
    { apply prop_right.
      split; [destruct (eq_dec b (-1)); auto; omega|].
      destruct (eq_dec (vint b) Empty).
      + assert (b = -1) by (apply Empty_inj; auto).
        subst; rewrite eq_dec_refl; auto.
      + destruct (eq_dec b (-1)); [subst; contradiction n; auto|].
        split; auto; split; auto; apply latest_read_new; auto. }
    apply andp_right; [apply prop_right; auto|].
    rewrite lock_struct_array; subst c l; cancel.
    destruct (eq_dec b (-1)); subst; auto.
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
