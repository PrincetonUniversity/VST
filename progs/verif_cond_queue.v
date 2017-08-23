Require Import VST.progs.conclib.
Require Import VST.progs.cond_queue.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
(*Definition freelock_spec := DECLARE _freelock (freelock_spec _).*)
Definition spawn_spec := DECLARE _spawn spawn_spec.
(*Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.*)
Definition makecond_spec := DECLARE _makecond (makecond_spec _).
(*Definition freecond_spec := DECLARE _freecond (freecond_spec _).*)
Definition wait_spec := DECLARE _waitcond (wait_spec _).
Definition signal_spec := DECLARE _signalcond (signal_spec _).

Definition malloc_spec :=
 DECLARE _malloc
  WITH n: Z
  PRE [ 1%positive OF tuint ]
     PROP (4 <= n <= Int.max_unsigned)
     LOCAL (temp 1%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ]
     EX v: val,
     PROP (malloc_compatible n v)
     LOCAL (temp ret_temp v)
     SEP (memory_block Tsh n v).

Definition free_spec :=
 DECLARE _free
  WITH p : val , n : Z
  PRE [ 1%positive OF tptr tvoid ]
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() LOCAL (temp 1%positive p)
      SEP (memory_block Tsh n p)
  POST [ tvoid ]
    PROP () LOCAL () SEP ().

Definition trequest := Tstruct _request_t noattr.

Definition process_spec :=
 DECLARE _process
  WITH _ : unit
  PRE [ _data OF tint ] PROP () LOCAL () SEP ()
  POST [ tvoid ] PROP () LOCAL () SEP ().

Definition get_request_spec :=
 DECLARE _get_request
  WITH _ : unit
  PRE [ ] PROP () LOCAL () SEP ()
  POST [ tptr trequest ]
    EX v : val, EX data : Z, PROP () LOCAL (temp ret_temp v)
      SEP (data_at Tsh trequest (Vint (Int.repr data)) v).

Definition process_request_spec :=
 DECLARE _process_request
  WITH request : val, data : Z
  PRE [ _request OF (tptr trequest) ]
     PROP ()
     LOCAL (temp _request request)
     SEP (data_at Tsh trequest (Vint (Int.repr data)) request)
  POST [ tvoid ]
    PROP () LOCAL () SEP (emp).

Definition MAX := 10.

Definition add_spec :=
 DECLARE _add
  WITH request : val, buf : val, len : val, reqs : list val
  PRE [ _request OF (tptr trequest) ]
   PROP (Zlength reqs < MAX)
   LOCAL (temp _request request; gvar _buf buf; gvar _length len)
   SEP (data_at Ews (tarray (tptr trequest) MAX) (complete MAX reqs) buf;
        data_at Ews tint (Vint (Int.repr (Zlength reqs))) len)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (data_at Ews (tarray (tptr trequest) MAX) (complete MAX (reqs ++ [request])) buf;
        data_at Ews tint (Vint (Int.repr (Zlength reqs))) len).

Definition remove_spec :=
 DECLARE _remove
  WITH buf : val, len : val, reqs : list val, req : val
  PRE [ ]
   PROP (Zlength reqs < MAX; isptr req)
   LOCAL (gvar _buf buf; gvar _length len)
   SEP (data_at Ews (tarray (tptr trequest) MAX) (complete MAX (reqs ++ [req])) buf;
        data_at Ews tint (Vint (Int.repr (Zlength reqs + 1))) len)
  POST [ tptr trequest ]
   PROP ()
   LOCAL (temp ret_temp req)
   SEP (data_at Ews (tarray (tptr trequest) MAX) (complete MAX reqs) buf;
        data_at Ews tint (Vint (Int.repr (Zlength reqs + 1))) len).

Definition lock_pred buf len := Exp _ (fun reqs =>
  Pred_list (Data_at _ Ews (tarray (tptr trequest) MAX) (complete MAX reqs) buf ::
             Data_at _ Ews tint (Vint (Int.repr (Zlength reqs))) len ::
             Pred_prop (Forall isptr reqs /\ Zlength reqs <= MAX) ::
             map (fun r => Exp _ (fun data => Data_at _ Tsh trequest (Vint (Int.repr data)) r)) reqs)).

Definition producer_spec :=
 DECLARE _producer
  WITH y : val, x : val * val * share * val * val * val
  PRE [ _arg OF (tptr tvoid) ]
    let '(buf, len, sh, lock, cprod, ccon) := x in
    PROP  ()
    LOCAL (temp _arg y; gvar _buf buf; gvar _length len;
           gvar _requests_lock lock; gvar _requests_producer cprod; gvar _requests_consumer ccon)
    SEP   ((!!readable_share sh && emp);
           lock_inv sh lock (Interp (lock_pred buf len)); cond_var sh cprod; cond_var sh ccon)
  POST [ tptr tvoid ] PROP () LOCAL () SEP (emp).

Definition consumer_spec :=
 DECLARE _consumer
  WITH y : val, x : val * val * share * val * val * val
  PRE [ _arg OF (tptr tvoid) ]
    let '(buf, len, sh, lock, cprod, ccon) := x in
    PROP  ()
    LOCAL (temp _arg y; gvar _buf buf; gvar _length len;
           gvar _requests_lock lock; gvar _requests_producer cprod; gvar _requests_consumer ccon)
    SEP   ((!!readable_share sh && emp);
           lock_inv sh lock (Interp (lock_pred buf len)); cond_var sh cprod; cond_var sh ccon)
  POST [ tptr tvoid ] PROP () LOCAL () SEP (emp).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog [] u
  POST [ tint ] main_post prog [] u.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; release_spec; (*release2_spec;*) makelock_spec;
  (*freelock_spec; freelock2_spec;*) spawn_spec; makecond_spec; (*freecond_spec;*) wait_spec; signal_spec;
  malloc_spec; free_spec;
  process_spec; get_request_spec; process_request_spec; add_spec; remove_spec; producer_spec; consumer_spec;
  main_spec]).

Lemma body_process : semax_body Vprog Gprog f_process process_spec.
Proof.
  start_function.
  forward.
Qed.

Lemma body_get_request : semax_body Vprog Gprog f_get_request get_request_spec.
Proof.
  start_function.
  forward_call (sizeof trequest).
  { simpl; computable. }
  Intro p.
  rewrite memory_block_isptr; normalize.
  rewrite memory_block_size_compatible; [normalize | simpl; computable].
  unfold malloc_compatible in H.
  destruct p; try contradiction; destruct H.
  rewrite memory_block_data_at_.
  forward.
  eapply semax_pre; [|apply semax_return].
  go_lower; normalize.
  unfold POSTCONDITION, abbreviate.
  unfold frame_ret_assert, function_body_ret_assert; simpl; normalize.
  unfold PROPx, LOCALx, SEPx, local; simpl; normalize.
  unfold liftx; simpl; unfold lift.
  Exists (Vptr b i0); Exists 1; normalize.
  unfold lift1; entailer'.
  { unfold field_compatible; simpl; repeat split; auto.
    unfold align_attr; simpl.
    eapply Zdivides_trans; eauto; unfold natural_alignment; exists 2; omega. }
Qed.

Lemma body_process_request : semax_body Vprog Gprog f_process_request process_request_spec.
Proof.
  start_function.
  forward.
  forward_call tt.
  forward_call (request, sizeof trequest).
  { subst Frame; instantiate (1 := []); normalize.
    apply data_at_memory_block. }
  forward.
Qed.

Lemma body_add : semax_body Vprog Gprog f_add add_spec.
Proof.
  start_function.
  forward.
  unfold Znth; simpl.
  forward.
  { apply prop_right; split; auto; rewrite Zlength_correct; omega. }
  forward.
  cancel.
  rewrite upd_complete; auto.
Qed.

Lemma body_remove : semax_body Vprog Gprog f_remove remove_spec.
Proof.
  start_function.
  forward.
  assert (0 <= Zlength reqs + 1 - 1 < 10).
  { rewrite Z.add_simpl_r; split; auto; rewrite Zlength_correct; omega. }
  assert (Znth (Zlength reqs + 1 - 1) (complete MAX (reqs ++ [req])) Vundef = req) as Hnth.
  { rewrite Z.add_simpl_r, Znth_complete;
      [|repeat rewrite Zlength_correct; rewrite app_length; simpl; Omega0].
    rewrite app_Znth2, Zminus_diag; [auto | omega]. }
  forward.
  { entailer!.
    rewrite Hnth; auto. }
  forward.
  forward.
  cancel.
  rewrite Z.add_simpl_r, remove_complete; auto.
Qed.

Lemma all_ptrs : forall reqs,
  fold_right_sepcon (map Interp (map (fun r => Exp _ (fun data =>
    Data_at _ Tsh trequest (Vint (Int.repr data)) r)) reqs)) |--
  !!(Forall isptr reqs).
Proof.
  induction reqs; simpl; intros; entailer.
  rewrite data_at_isptr.
  eapply derives_trans; [apply saturate_aux20|].
  { apply andp_left1, derives_refl. }
  { apply IHreqs; auto. }
  normalize.
Qed.

Lemma precise_reqs : forall reqs, precise (fold_right_sepcon (map Interp (map (fun r => Exp _ (fun d =>
  Data_at _ Tsh trequest (Vint (Int.repr d)) r)) reqs))).
Proof.
  induction reqs; simpl; auto.
  apply precise_sepcon; auto.
  apply derives_precise with (Q := data_at_ Tsh trequest a);
    [intros ? (? & H); apply data_at_data_at_ in H; auto|].
  unfold data_at_, field_at_; unfold_field_at 1%nat; simpl.
  unfold field_at, at_offset; simpl.
  apply precise_andp2; rewrite by_value_data_at_rec_nonvolatile; auto.
Qed.

Lemma inv_precise : forall buf len, precise (Interp (lock_pred buf len)).
Proof.
  intros ????? (reqs1 & ? & ? & ? & Hbuf1 & ? & ? & ? & Hlen1 & ? & ? & ? & ((? & ?) & Hemp1) & Hdata1)
    (reqs2 & ? & ? & ? & Hbuf2 & ? & ? & ? & Hlen2 & ? & ? & ? & ((? & ?) & Hemp2) & Hdata2) ??.
  exploit (mapsto_inj Ews); auto.
  { apply Hlen1. }
  { apply Hlen2. }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { discriminate. }
  { discriminate. }
  simpl; intros (? & Heq); subst.
  assert (Zlength reqs1 = Zlength reqs2) as Hlen.
  { rewrite <- (Int.signed_repr (Zlength reqs1)), <- (Int.signed_repr (Zlength reqs2)).
    congruence.
    { pose proof Int.min_signed_neg; split; [rewrite Zlength_correct; omega|].
      transitivity MAX; [Omega0 | unfold MAX; computable]. }
    { pose proof Int.min_signed_neg; split; [rewrite Zlength_correct; omega|].
      transitivity MAX; [Omega0 | unfold MAX; computable]. } }
  pose proof (all_ptrs _ _ Hdata1) as Hptrs1.
  pose proof (all_ptrs _ _ Hdata2) as Hptrs2.
  exploit (data_at_ptr_array_inj Ews).
  { auto. }
  { destruct Hbuf1 as (? & Hbuf1); unfold at_offset in Hbuf1; apply Hbuf1. }
  { destruct Hbuf2 as (? & Hbuf2); unfold at_offset in Hbuf2; apply Hbuf2. }
  { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  { apply Forall_complete; [|discriminate].
    eapply Forall_impl; [|apply Hptrs1].
    destruct a; auto; discriminate. }
  { apply Forall_complete; [|discriminate].
    eapply Forall_impl; [|apply Hptrs2].
    destruct a; auto; discriminate. }
  { apply Zlength_complete; auto. }
  { apply Zlength_complete; auto. }
  intros (? & Hbufs); subst.
  assert (reqs1 = reqs2); [|subst].
  { repeat rewrite Zlength_correct in Hlen.
    eapply complete_inj; [eauto | omega]. }
  exploit (precise_reqs reqs2).
  { apply Hdata1. }
  { apply Hdata2. }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  intro; subst.
  match goal with H1 : predicates_hered.app_pred emp ?a,
    H2 : predicates_hered.app_pred emp ?b |- _ => assert (a = b);
      [eapply sepalg.same_identity; auto;
        [match goal with H : sepalg.join a ?x ?y |- _ =>
           specialize (Hemp1 _ _ H); subst; eauto end |
         match goal with H : sepalg.join b ?x ?y |- _ =>
           specialize (Hemp2 _ _ H); subst; eauto end] | subst] end.
  repeat match goal with H1 : sepalg.join ?a ?b ?c, H2 : sepalg.join ?a ?b ?d |- _ =>
    pose proof (sepalg.join_eq H1 H2); clear H1 H2; subst end; auto.
Qed.

Lemma inv_positive : forall buf len,
  positive_mpred (Interp (lock_pred buf len)).
Proof.
  intros; simpl.
  apply ex_positive; intro.
  apply positive_sepcon2, positive_sepcon1; auto.
Qed.

Lemma body_producer : semax_body Vprog Gprog f_producer producer_spec.
Proof.
  start_function.
  normalize.
  eapply semax_loop with (Q' := PROP ()
    LOCAL (temp _arg y; gvar _buf buf; gvar _length len; gvar _requests_lock lock;
           gvar _requests_producer cprod; gvar _requests_consumer ccon)
    SEP (lock_inv sh lock (Interp (lock_pred buf len)); cond_var sh cprod; cond_var sh ccon));
    [|forward; entailer].
  forward.
  forward_call tt.
  Intro x; destruct x as (r, data).
  forward_call (lock, sh, lock_pred buf len).
  { destruct lock; try contradiction; simpl; entailer'. }
  simpl.
  Intro reqs; normalize.
  forward.
  unfold Znth; simpl.
  forward_while (EX reqs : list val,
   PROP (Forall isptr reqs; Zlength reqs <= MAX)
   LOCAL (temp _len (Vint (Int.repr (Zlength reqs))); temp _request r; temp _arg y; gvar _buf buf;
          gvar _length len; gvar _requests_lock lock;
          gvar _requests_producer cprod; gvar _requests_consumer ccon)
   SEP (data_at Ews (tarray (tptr trequest) MAX) (complete MAX reqs) buf;
        data_at Ews tint (Vint (Int.repr (Zlength reqs))) len;
        fold_right_sepcon (map Interp (map (fun r => Exp _ (fun data =>
          Data_at CompSpecs Tsh trequest (Vint (Int.repr data)) r)) reqs));
        lock_inv sh lock (Interp (lock_pred buf len));
        @data_at CompSpecs Tsh trequest (Vint (Int.repr data)) r;
        cond_var sh cprod; cond_var sh ccon)).
  (* XX Delta now contains an equality involving unfold_reptype that causes a discriminate
     in fancy_intros (in saturate_local) to go into an infinite loop. *)
  - Exists reqs; go_lower; entailer'.
  - go_lower; entailer'.
  - forward_call (cprod, lock, sh, sh, lock_pred buf len).
    { destruct lock; try contradiction; simpl; entailer'. }
    { simpl.
      Exists reqs0; unfold fold_right at 3; cancel.
      entailer'; cancel. }
    simpl.
    Intro reqs'; normalize.
    forward.
    Exists reqs'; go_lower; entailer'; cancel.
  - assert (Zlength reqs0 < MAX).
    { rewrite Int.signed_repr in HRE; auto.
      pose proof Int.min_signed_neg; split; [rewrite Zlength_correct; omega|].
      transitivity MAX; [auto | unfold MAX; computable]. }
    forward_call (r, buf, len, reqs0).
    { simpl; cancel. }
    forward.
    rewrite data_at_isptr, field_at_isptr; normalize.
    rewrite (data_at_isptr _ trequest); normalize.
    forward_call (lock, sh, lock_pred buf len).
    { destruct lock; try contradiction; simpl; entailer'. }
    { simpl.
      Exists (reqs0 ++ [r]); cancel.
      unfold fold_right at 2; unfold fold_right at 1; cancel.
      repeat rewrite Zlength_correct; rewrite app_length; simpl.
      rewrite Nat2Z.inj_add.
      repeat rewrite map_app; simpl; rewrite sepcon_app; simpl.
      unfold fold_right at 1; cancel; entailer'.
      Exists data; cancel.
      eapply derives_trans; [|apply prop_and_same_derives']; [cancel|].
      split; [rewrite Forall_app; auto | rewrite Zlength_correct in *; omega]. }
    { split; auto; split; simpl.
      + apply inv_precise; auto.
      + apply inv_positive. }
    forward_call (ccon, sh).
    go_lower; entailer'; cancel.
Qed.

Lemma body_consumer : semax_body Vprog Gprog f_consumer consumer_spec.
Proof.
  start_function.
  normalize.
  eapply semax_loop with (Q' := PROP ()
    LOCAL (temp _arg y; gvar _buf buf; gvar _length len; gvar _requests_lock lock;
           gvar _requests_producer cprod; gvar _requests_consumer ccon)
    SEP (lock_inv sh lock (Interp (lock_pred buf len)); cond_var sh cprod; cond_var sh ccon));
    [|forward; entailer].
  forward.
  forward_call (lock, sh, lock_pred buf len).
  { destruct lock; try contradiction; simpl; entailer. }
  simpl.
  Intro reqs; normalize.
  forward.
  unfold Znth; simpl.
  forward_while (EX reqs : list val, PROP (Forall isptr reqs; Zlength reqs <= MAX)
   LOCAL (temp _len (Vint (Int.repr (Zlength reqs))); temp _arg y; gvar _buf buf;
          gvar _length len; gvar _requests_lock lock;
          gvar _requests_producer cprod; gvar _requests_consumer ccon)
   SEP (data_at Ews (tarray (tptr trequest) MAX) (complete MAX reqs) buf;
        data_at Ews tint (Vint (Int.repr (Zlength reqs))) len;
        fold_right_sepcon (map Interp (map (fun r => Exp _ (fun data =>
          Data_at CompSpecs Tsh trequest (Vint (Int.repr data)) r)) reqs));
        lock_inv sh lock (Interp (lock_pred buf len));
        cond_var sh cprod; cond_var sh ccon)).
  - Exists reqs; entailer.
  - entailer.
  - forward_call (ccon, lock, sh, sh, lock_pred buf len).
    { destruct lock; try contradiction; simpl; entailer. }
    { simpl.
      Exists reqs0; entailer!.
      unfold fold_right at 1; cancel. }
    simpl.
    Intro reqs'; normalize.
    forward.
    Exists reqs'; entailer!.
  - assert (reqs0 <> []) as Hreqs.
    { intro; subst; unfold Zlength in *; simpl in *; contradiction HRE; auto. }
    rewrite (app_removelast_last (Vint (Int.repr 0)) Hreqs) in *.
    rewrite Zlength_correct, app_length; simpl.
    rewrite Nat2Z.inj_add, <- Zlength_correct; simpl.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in *; simpl in *.
    match goal with H : Forall isptr (_ ++ _) |- _ =>
      rewrite Forall_app in H; destruct H as (? & Hlast); inv Hlast end.
    forward_call (buf, len, removelast reqs0, last reqs0 (Vint (Int.repr 0))).
    { simpl; cancel. }
    { split; auto; omega. }
    forward.
    rewrite data_at_isptr, field_at_isptr; normalize.
    forward_call (lock, sh, lock_pred buf len).
    { destruct lock; try contradiction; simpl; entailer. }
    { simpl.
      Exists (removelast reqs0); entailer!.
      rewrite Z.add_simpl_r.
      unfold fold_right at 1.
      repeat rewrite map_app; simpl; rewrite sepcon_app; cancel. }
    { split; auto; split; simpl.
      + apply inv_precise; auto.
      + apply inv_positive. }
    forward_call (cprod, sh).
    { simpl; cancel. }
    Intro data.
    forward_call (last reqs0 (Vint (Int.repr 0)), data).
    { simpl; cancel. }
    unfold fold_right; entailer!.
Qed.

Lemma lock_struct : forall p, data_at_ Ews (Tstruct _lock_t noattr) p |-- data_at_ Ews tlock p.
Proof.
  intros.
  unfold data_at_, field_at_; unfold_field_at 1%nat.
  unfold field_at, at_offset; simpl.
  rewrite field_compatible_cons; simpl; entailer.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  name lock _requests_lock.
  name len _length.
  name ccon _requests_consumer.
  name cprod _requests_producer.
  name buf _buf.
  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound 10 (EX i : Z, PROP ()
    LOCAL (gvar _buf buf; gvar _requests_producer cprod; gvar _requests_consumer ccon; gvar _length len;
                      gvar _requests_lock lock)
    SEP (data_at Ews (tarray (tptr trequest) MAX)
             (repeat (Vint (Int.repr 0)) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (10 - i))) buf;
         data_at_ Ews tint cprod; data_at_ Ews tint ccon;
         data_at_ Ews tint len; data_at_ Ews tlock lock)).
  { unfold trequest, _request_t; entailer!.
    apply sepcon_derives; [entailer | apply lock_struct]. }
  { forward.
    entailer!.
    assert (Zlength (repeat (Vint (Int.repr 0)) (Z.to_nat i)) = i) as Hlen.
    { rewrite Zlength_correct, repeat_length.
      apply Z2Nat.id; omega. }
    rewrite upd_Znth_app2; rewrite Hlen; [|rewrite Zlength_correct; Omega0].
    assert (0 < Z.to_nat (10 - i))%nat by Omega0.
    destruct (Z.to_nat (10 - i)) eqn: Hminus; [omega | simpl].
    rewrite Zminus_diag; unfold upd_Znth, sublist.sublist; simpl.
    rewrite Zlength_cons; unfold Z.succ; simpl.
    rewrite Z.add_simpl_r, Zlength_correct, Nat2Z.id, firstn_exact_length.
    rewrite Z2Nat.inj_add; try omega.
    rewrite repeat_plus; simpl.
    rewrite <- app_assoc; replace (Z.to_nat (10 - (i + 1))) with n; auto.
    rewrite Z.sub_add_distr.
    rewrite Z2Nat.inj_sub; [|omega].
    rewrite Hminus; simpl; omega. }
  forward.
  forward_call (lock, Ews, lock_pred buf len).
  { destruct lock; try contradiction; simpl; entailer. }
  rewrite (data_at_isptr _ (tarray _ _)), field_at_isptr; normalize.
  forward_call (lock, Ews, lock_pred buf len).
  { destruct lock; try contradiction; simpl; entailer. }
  { simpl.
    Exists ([] : list val); simpl; entailer!. }
  { split; auto; split.
    - apply inv_precise; auto.
    - apply inv_positive. }
  forward_call (cprod, Ews).
  { unfold tcond; cancel. }
  forward_call (ccon, Ews).
  { unfold tcond; cancel. }
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  get_global_function'' _consumer.
  normalize.
  apply extract_exists_pre; intros c_.
  forward_call (c_, Vint (Int.repr 0), existT (fun ty => ty * (ty -> val -> Pred))%type
   (val * val * share * val * val * val)%type ((buf, len, sh1, lock, cprod, ccon),
   fun (x : (val * val * share * val * val * val)) (_ : val) => let '(buf, len, sh, lock, cprod, ccon) := x in
     Pred_list [Pred_prop (readable_share sh); Lock_inv sh lock (lock_pred buf len);
                Cond_var _ sh cprod; Cond_var _ sh ccon])).
  { simpl; entailer.
    Exists _arg; entailer.
    Exists (fun x : val * val * share * val * val * val => let '(buf, len, sh, lock, cprod, ccon) := x in
      [(_buf, buf); (_length, len); (_requests_lock, lock); (_requests_producer, cprod);
       (_requests_consumer, ccon)]); entailer.
    subst Frame; instantiate (1 := [cond_var sh2 ccon; cond_var sh2 cprod;
      lock_inv sh2 lock (Interp (lock_pred buf len))]).
    evar (body : funspec); replace (WITH _ : _ PRE [_] _ POST [_] _) with body.
    repeat rewrite sepcon_assoc; apply sepcon_derives; subst body; [apply derives_refl|].
    simpl.
    erewrite <- (sepcon_assoc (cond_var sh1 ccon)), cond_var_share_join; eauto; cancel.
    repeat rewrite sepcon_assoc.
    erewrite <- (sepcon_assoc (cond_var sh1 cprod)), cond_var_share_join; eauto; cancel.
    erewrite lock_inv_share_join; eauto; cancel.
    subst body; f_equal.
    extensionality.
    destruct x as (?, (((((?, ?), ?), ?), ?), ?)); simpl.
    f_equal; f_equal.
    unfold SEPx; simpl; normalize. }
  forward_call (lock, sh2, lock_pred buf len).
  simpl.
  Intro reqs; normalize.
  forward.
  unfold Znth; simpl.
  forward_while (EX reqs : list val, PROP (Forall isptr reqs; Zlength reqs <= MAX)
   LOCAL (temp _len (Vint (Int.repr (Zlength reqs))); gvar _consumer c_; gvar _buf buf; gvar _requests_producer cprod;
   gvar _requests_consumer ccon; gvar _length len; gvar _requests_lock lock)
   SEP (data_at Ews (tarray (tptr trequest) MAX) (complete MAX reqs) buf;
   data_at Ews tint (Vint (Int.repr (Zlength reqs))) len;
   fold_right_sepcon
     (map Interp (map (fun r : val => Exp Z (fun data : Z => Data_at CompSpecs Tsh trequest (Vint (Int.repr data)) r)) reqs));
   lock_inv sh2 lock (Interp (lock_pred buf len));
   cond_var sh2 ccon; cond_var sh2 cprod)).
  { Exists reqs; entailer!. }
  { entailer. }
  { (* loop body *)
    forward_call (cprod, lock, sh2, sh2, lock_pred buf len).
    { destruct lock; try contradiction; simpl; entailer. }
    { simpl; cancel.
      Exists reqs0; unfold fold_right at 1; cancel; entailer!. }
    simpl; Intro reqs'; normalize.
    forward.
    Exists reqs'; entailer!. }
  forward_call (lock, sh2, lock_pred buf len).
  { destruct lock; try contradiction; simpl; entailer. }
  { simpl; Exists reqs0; cancel.
    unfold fold_right at 1; entailer!. }
  { split; auto; split; [apply inv_precise | apply inv_positive]; auto. }
  destruct (split_readable_share _ H0) as (sh2' & sh3 & ? & ? & Hsh').
  get_global_function'' _producer.
  normalize.
  apply extract_exists_pre; intros p_.
  forward_call (p_, Vint (Int.repr 0), existT (fun ty => ty * (ty -> val -> Pred))%type
   (val * val * share * val * val * val)%type ((buf, len, sh2', lock, cprod, ccon),
   fun (x : (val * val * share * val * val * val)) (_ : val) => let '(buf, len, sh, lock, cprod, ccon) := x in
     Pred_list [Pred_prop (readable_share sh); Lock_inv sh lock (lock_pred buf len);
                Cond_var _ sh cprod; Cond_var _ sh ccon])).
  { simpl; entailer.
    Exists _arg; entailer.
    Exists (fun x : val * val * share * val * val * val => let '(buf, len, sh, lock, cprod, ccon) := x in
      [(_buf, buf); (_length, len); (_requests_lock, lock); (_requests_producer, cprod);
       (_requests_consumer, ccon)]); entailer.
    subst Frame; instantiate (1 := [cond_var sh3 ccon; cond_var sh3 cprod;
      lock_inv sh3 lock (Interp (lock_pred buf len))]).
    evar (body : funspec); replace (WITH _ : _ PRE [_] _ POST [_] _) with body.
    repeat rewrite sepcon_assoc; apply sepcon_derives; subst body; [apply derives_refl|].
    simpl.
    erewrite <- (sepcon_assoc (cond_var sh2' ccon)), cond_var_share_join; eauto; cancel.
    repeat rewrite sepcon_assoc.
    erewrite <- (sepcon_assoc (cond_var sh2' cprod)), cond_var_share_join; eauto; cancel.
    erewrite lock_inv_share_join; eauto; cancel.
    subst body; f_equal.
    extensionality.
    destruct x as (?, (((((?, ?), ?), ?), ?), ?)); simpl.
    f_equal; f_equal.
    unfold SEPx; simpl; normalize. }
  rewrite <- seq_assoc.
  apply semax_seq' with (P' := PROP () LOCAL () SEP (FF)).
  { match goal with |- semax _ ?P _ _ => eapply semax_loop with (Q' := P) end;
      forward; entailer!. }
  forward.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity|]).
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
eapply semax_func_cons_ext; try reflexivity.
{ intros; entailer!. }
{ admit. }
eapply semax_func_cons_ext; try reflexivity.
{ admit. }
{ admit. }
semax_func_cons body_process.
semax_func_cons body_get_request.
semax_func_cons body_process_request.
semax_func_cons body_add.
semax_func_cons body_remove.
semax_func_cons body_producer.
semax_func_cons body_consumer.
semax_func_cons body_main.
Admitted.
