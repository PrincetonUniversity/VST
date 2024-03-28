Require Import mailbox.verif_atomic_exchange.
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.
Require Import VST.zlist.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.

Opaque eq_dec.

Section mpred.

Context `{!VSTGS unit Σ, AEGS0 : !AEGS t_atom_int, !inG Σ (excl_authR (leibnizO val))}.

Lemma body_initialize_reader : semax_body Vprog Gprog f_initialize_reader initialize_reader_spec.
Proof.
  start_function.
  rewrite (data_at__isptr _ tint); Intros.
  assert_PROP (Zlength reads = N) by entailer!.
  assert (0 <= r < N) as Hr.
  { exploit (Znth_inbounds r reads); [|lia].
    intro Heq; rewrite -> Heq in *; contradiction. }
  assert (N < Int.max_signed) by computable.
  forward.
  forward.
  forward.
  forward.
  entailer!.
Qed.

Lemma body_start_read : semax_body Vprog Gprog f_start_read start_read_spec.
Proof.
  start_function.
  rewrite (data_at__isptr _ tint); Intros.
  assert_PROP (Zlength reads = N) by entailer!.
  assert (0 <= r < N) as Hr.
  { exploit (Znth_inbounds r reads); [|lia].
    intro Heq; rewrite -> Heq in *; contradiction. }
  assert (N < Int.max_signed) by computable.
  sep_apply comm_loc_isptr; Intros.
  forward.
  forward.
  forward.
  set (c := Znth r comms).
  forward_call AE_sub (sh2, c, g, vint 0, Empty, h,
    fun h b => ⌜b = Empty /\ latest_read h (vint b0)⌝ ∧
      (∃ v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs)) ∗ ghost_frag (vint b0) g0,
    comm_R bufs sh g0 g1 g2, fun h b => ∃ b' : Z, ⌜(if eq_dec b Empty then b' = b0 else b = vint b') /\
      -1 <= b' < B /\ latest_read h (vint b')⌝ ∧
      (∃ v : Z, data_at sh tbuffer (vint v) (Znth b' bufs)) ∗ ghost_frag (vint b') g0).
  { unfold comm_loc; entailer!.
    rewrite <- bi.emp_sep at 1; apply bi.sep_mono; last cancel.
    rewrite /AE_spec.
    iIntros "_" (???? (? & ? & Hincl)) "(>comm & (% & %) & buf & g0)".
    rewrite /comm_R.
    rewrite !rev_app_distr /= !last_two_reads_cons prev_taken_cons.
    unfold last_write in *; simpl in *.
    pose proof (last_two_reads_fst (rev hx)).
    iDestruct "comm" as (???) "(%Hcomm & a0 & a1 & a2 & buf')".
    destruct Hcomm as (-> & ? & Hhx & Hlast & ? & ?).
    iMod (ghost_var_update _ _ _ (vint (if eq_dec (vint b) Empty then b0 else b)) with "a0 g0") as "(%Heq & a0 & g0)".
    assert (repable_signed b0) by (apply repable_buf; lia).
    assert (b1 = b0) as -> by (apply repr_inj_signed; auto; congruence).
    lapply (repable_buf b); auto; intro.
    rewrite Hlast.
    iIntros "!>". rewrite -bi.later_intro.
    rewrite bi.sep_exist_r; iExists (-1).
    rewrite bi.sep_exist_r; iExists (if eq_dec (vint b) Empty then b0 else b).
    rewrite bi.sep_exist_r; iExists (if eq_dec (vint b) Empty then b2 else b0).
    iStopProof; entailer!.
    { split; [rewrite Forall_app; repeat constructor; auto|].
      { exists b, (-1); split; [|split]; auto; lia. }
      split; last by if_tac.
      if_tac; last done.
      if_tac; auto. }
    rewrite -!bi.sep_exist_l -!bi.sep_exist_r.
    setoid_rewrite (if_true (Empty = Empty)); [|done..].
    Exists (if eq_dec (vint b) Empty then b0 else b); cancel.
    apply hist_incl_lt in Hincl; last done.
    destruct (eq_dec (vint b) Empty).
    - assert (b = -1) by (apply Empty_inj; auto; apply repable_buf; auto).
      rewrite if_true //; entailer!.
      rewrite latest_read_Empty; auto.
    - destruct (eq_dec b (-1)); [subst; contradiction n; auto|].
      entailer!.
      apply latest_read_new; auto. }
  Intros x b'; destruct x as (t, v). simpl fst in *; simpl snd in *.
  assert (exists b, v = vint b /\ -1 <= b < B /\ if eq_dec b (-1) then b' = b0 else b' = b) as (b & ? & ? & ?).
  { destruct (eq_dec v Empty); subst.
    - exists (-1); if_tac; last done; split; auto; lia.
    - do 2 eexists; eauto; split; [lia|].
      destruct (eq_dec b' (-1)); [subst; contradiction n; auto | auto]. }
  exploit repable_buf; eauto; intro; subst.
  forward_if (temp _t'2 (bool2val (negb (eq_dec b (-1))))).
  { destruct (eq_dec b (-1)); try lia; subst.
    forward.
    entailer!!.
    destruct (zlt _ _); auto.
    unfold B, N in *; lia. }
  { forward.
    destruct (eq_dec b (-1)); [|lia].
    entailer!!. }
  forward_if (PROP () LOCAL (temp _b (vint (if eq_dec b (-1) then b0 else b)); temp _rr (Znth r reads);
      temp _r (vint r); gvars gv)
    SEP (comm_loc sh2 c g g0 g1 g2 bufs sh (<[t := Excl (AE (vint b) Empty)]>h);
         ∃ v : Z, data_at sh tbuffer (vint v) (Znth (if eq_dec b (-1) then b0 else b) bufs);
         ghost_frag (vint b') g0;
         data_at sh1 (tarray (tptr tint) N) reads (gv _reading); data_at sh1 (tarray (tptr tint) N) lasts (gv _last_read);
         data_at_ Ews tint (Znth r reads);
         data_at Ews tint (vint (if eq_dec b (-1) then b0 else b)) (Znth r lasts);
         data_at sh1 (tarray (tptr t_atom_int) N) comms (gv _comm))).
  - forward.
    destruct (eq_dec b (-1)); try done.
    entailer!!.
  - forward.
    destruct (eq_dec b (-1)); try done.
    entailer!!.
  - forward.
    forward.
    Exists (if eq_dec b (-1) then b0 else b) t (vint b) v.
    entailer!!.
    { split; [destruct (eq_dec b (-1)); auto; lia|].
      destruct (eq_dec (vint b) Empty).
      + assert (b = -1) by (apply Empty_inj; auto).
        if_tac; try done; subst; auto.
      + destruct (eq_dec b (-1)); [subst; contradiction n; auto|].
        split; auto; apply latest_read_new; auto. }
    subst c; cancel.
    destruct (eq_dec b (-1)); subst; apply derives_refl.
Qed.

Lemma body_finish_read : semax_body Vprog Gprog f_finish_read finish_read_spec.
Proof.
  start_function.
  rewrite (data_at__isptr _ tint); Intros.
  assert_PROP (Zlength reads = N) by entailer!.
  assert (0 <= r < N) as Hr.
  { exploit (Znth_inbounds r reads); [|lia].
    intro Heq; rewrite -> Heq in *; contradiction. }
  assert (N < Int.max_signed) by computable.
  forward.
  forward.
  entailer!.
Qed.

End mpred.
