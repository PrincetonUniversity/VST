Require Import mailbox.verif_atomic_exchange.
Require Import VST.progs.conclib.
Require Import VST.progs.ghost.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.
Require Import mailbox.verif_mailbox_read.
Require Import mailbox.verif_mailbox_write.

Set Bullet Behavior "Strict Subproofs".

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (* p = malloc(n); *)
     t.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh t p * data_at_ Tsh t p)).
*
  if_tac.
    subst p. entailer!.
    entailer!.
*
    forward_call tt.
    contradiction.
*
    if_tac.
    + forward. subst p. congruence.
    + Intros. forward. entailer!.
*
  forward. Exists p; entailer!.
Qed.

Lemma body_memset : semax_body Vprog Gprog f_memset memset_spec.
Proof.
  start_function.
  forward.
  rewrite data_at__isptr; Intros.
  rewrite sem_cast_neutral_ptr; auto.
  pose proof (sizeof_pos t).
  assert_PROP (sizeof t <= Int.max_unsigned).
  { entailer!.
    destruct H3 as [? [_ [? _]]].
    destruct p; inv H3.
    simpl in H4.
    pose proof Ptrofs.unsigned_range i.
    rep_omega.
  }
  assert_PROP (vint n = force_val (sem_div tuint tint (vint (4 * n)) (vint 4))) as H4.
  { entailer!.
    unfold sem_div; simpl.
    unfold Int.divu.
    rewrite !Int.unsigned_repr; auto; try (split; auto; try computable; omega).
    rewrite Z.mul_comm, Z_div_mult; auto; computable. }
  forward_for_simple_bound n (EX i : Z, PROP ()
    LOCAL (temp _p p; temp _s p; temp _c (vint c); temp _n (vint (4 * n)))
    SEP (data_at sh (tarray tint n) (repeat (vint c) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (n - i))) p)).
  { entailer!.
    { rewrite H4; auto. }
    apply derives_trans with (Q := data_at_ sh (tarray tint n) p).
    - rewrite !data_at__memory_block; simpl.
      assert ((4 * Z.max 0 n)%Z = sizeof t) as Hsize.
      { rewrite Z.max_r; auto; omega. }
      setoid_rewrite Hsize; Intros; apply andp_right; [|simpl; apply derives_refl].
      apply prop_right; match goal with H : field_compatible _ _ _ |- _ =>
        destruct H as (? & ? & ? & ? & ?) end; repeat split; simpl; auto.
      + unfold size_compatible in *; simpl.
        destruct p; try contradiction.
        setoid_rewrite Hsize; auto.
      + destruct p; try contradiction.
        constructor; intros.
        econstructor; [reflexivity |].
        inv H0.
        inv H11.
        apply Z.divide_add_r; auto.
        apply Z.divide_mul_l.
        exists 1; auto.
    - rewrite data_at__eq.
      unfold default_val, reptype_gen; simpl.
      rewrite repeat_list_repeat, Z.sub_0_r; apply derives_refl. }
  - forward.
    rewrite upd_init_const; [|omega].
    entailer!.
    rewrite H4; auto.
  - forward.
    rewrite Zminus_diag, app_nil_r; apply derives_refl.
Qed.

Opaque upto.

Lemma malloc_compatible_isptr:
  forall {cs: compspecs} t p, malloc_compatible (sizeof t) p -> isptr p.
Proof.
intros.
hnf in H. destruct p; try contradiction; simpl; auto.
Qed.
Hint Resolve malloc_compatible_isptr.

Lemma body_initialize_channels : semax_body Vprog Gprog f_initialize_channels initialize_channels_spec.
Proof.
  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound B (EX i : Z, PROP ()
    LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs buf; gvar _reading reading; gvar _last_read last_read)
    SEP (data_at_ Ews (tarray (tptr tint) N) comm; data_at_ Ews (tarray (tptr tlock) N) lock;
         data_at_ Ews (tarray (tptr tint) N) reading; data_at_ Ews (tarray (tptr tint) N) last_read;
         EX bufs : list val, !!(Zlength bufs = i /\ Forall isptr bufs) &&
           data_at Ews (tarray (tptr tbuffer) B) (bufs ++ repeat Vundef (Z.to_nat (B - i))) buf *
           fold_right sepcon emp (map (@data_at CompSpecs Tsh tbuffer (vint 0)) bufs) *
           fold_right sepcon emp (map (malloc_token Tsh tbuffer) bufs))).
  { unfold B, N; computable. }
  { unfold B, N; computable. }
  { entailer!.
    Exists ([] : list val); simpl; entailer!. }
  { forward_call tbuffer.
    { split3; simpl; auto; computable. }
    Intros b bufs.
    assert_PROP (field_compatible tint [] b) by entailer!.
    forward_call (Tsh, tbuffer, b, 0, 1).
    { repeat split; simpl; auto; try computable.
      destruct H3 as [? [? [? [? ?]]]]; auto. }
    clear H3.
    forward.
    rewrite upd_init; auto; try omega.
    entailer!.
    Exists (bufs ++ [b]); rewrite Zlength_app, <- app_assoc, !map_app, !sepcon_app, Forall_app; simpl; entailer!.
    clear; unfold data_at, field_at, at_offset; Intros.
    rewrite !data_at_rec_eq; unfold withspacer; simpl.
    unfold array_pred, aggregate_pred.array_pred, unfold_reptype; simpl.
    entailer!.
    { destruct H as [? [? [? [? ?]]]].
      split; [| split; [| split; [| split]]]; auto.
      destruct b; inv H.
      inv H2. inv H.
      specialize (H7 0 ltac:(omega)).
      simpl.
      eapply align_compatible_rec_Tstruct; [reflexivity |].
      intros.
      inv H.
      if_tac in H5; [| inv H5].
      subst i0; inv H5; inv H2.
      econstructor.
      1: reflexivity.
      inv H7.
      inv H.
      rewrite Z.mul_0_r in H2.
      auto. } }
  Intros bufs; rewrite Zminus_diag, app_nil_r.
  forward_for_simple_bound N (EX i : Z, PROP ()
    LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs buf; gvar _reading reading; gvar _last_read last_read)
    SEP (EX locks : list val, EX comms : list val, EX g : list val, EX g0 : list val, EX g1 : list val,
         EX g2 : list val, !!(Zlength locks = i /\ Zlength comms = i /\ Forall isptr comms /\ Zlength g = i /\
           Zlength g0 = i /\ Zlength g1 = i /\ Zlength g2 = i) &&
          (data_at Ews (tarray (tptr tlock) N) (locks ++ repeat Vundef (Z.to_nat (N - i))) lock *
           data_at Ews (tarray (tptr tint) N) (comms ++ repeat Vundef (Z.to_nat (N - i))) comm *
           fold_right sepcon emp (map (fun r => comm_loc Tsh (Znth r locks Vundef) (Znth r comms Vundef)
             (Znth r g Vundef) (Znth r g0 Vundef) (Znth r g1 Vundef) (Znth r g2 Vundef) bufs
             (Znth r shs Tsh) gsh2 []) (upto (Z.to_nat i))) *
           fold_right sepcon emp (map (malloc_token Tsh tlock) locks)) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g0) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2) *
           fold_right sepcon emp (map (malloc_token Tsh tint) comms);
         EX reads : list val, !!(Zlength reads = i) &&
           data_at Ews (tarray (tptr tint) N) (reads ++ repeat Vundef (Z.to_nat (N - i))) reading *
           fold_right sepcon emp (map (data_at_ Tsh tint) reads) *
           fold_right sepcon emp (map (malloc_token Tsh tint) reads);
         EX lasts : list val, !!(Zlength lasts = i) &&
           data_at Ews (tarray (tptr tint) N) (lasts ++ repeat Vundef (Z.to_nat (N - i))) last_read *
           fold_right sepcon emp (map (data_at_ Tsh tint) lasts) *
           fold_right sepcon emp (map (malloc_token Tsh tint) lasts);
         @data_at CompSpecs Ews (tarray (tptr tbuffer) B) bufs buf;
         EX sh : share, !!(sepalg_list.list_join sh1 (sublist i N shs) sh) &&
           @data_at CompSpecs sh tbuffer (vint 0) (Znth 0 bufs Vundef);
         fold_right sepcon emp (map (@data_at CompSpecs Tsh tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs));
         fold_right sepcon emp (map (malloc_token Tsh tbuffer) bufs))).
  { unfold N; computable. }
  { Exists ([] : list val) ([] : list val) ([] : list val) ([] : list val) ([] : list val) ([] : list val)
      ([] : list val) ([] : list val) Tsh; rewrite !data_at__eq; entailer!.
    - rewrite sublist_same; auto; omega.
    - erewrite <- sublist_same with (al := bufs), sublist_next at 1; eauto; try (unfold B, N in *; omega).
      simpl; cancel. }
  { Intros locks comms g g0 g1 g2 reads lasts sh.
    forward_call tint.  split3; simpl; auto; computable. Intros c.
    forward.
    forward.
    forward_call tint.  split3; simpl; auto; computable. Intros rr.
    forward.
    forward_call tint.  split3; simpl; auto; computable. Intros ll.
    forward.
    forward_call tlock.  split3; simpl; auto; computable. Intros l.
    rewrite <- lock_struct_array.
    forward.
    eapply (ghost_alloc (Tsh, vint 1)); auto with init.
    eapply (ghost_alloc (Tsh, vint 0)); auto with init.
    eapply (ghost_alloc (Tsh, vint 1)); auto with init.
    eapply (ghost_alloc (Some (Tsh, [] : hist), Some ([] : hist))); auto with init.
    Intros g' g0' g1' g2'.
    forward_call (l, Tsh, AE_inv c g' (vint 0) (comm_R bufs (Znth i shs Tsh) gsh2 g0' g1' g2')).
    rewrite <- hist_ref_join_nil by (apply Share.nontrivial).
    fold (ghost_var Tsh (vint 1) g0') (ghost_var Tsh (vint 0) g1') (ghost_var Tsh (vint 1) g2').
    erewrite <- !ghost_var_share_join with (sh0 := Tsh) by eauto.
    match goal with H : sepalg_list.list_join sh1 (sublist i N shs) sh |- _ =>
      erewrite sublist_next in H; try omega; inversion H as [|????? Hj1 Hj2] end.
    apply sepalg.join_comm in Hj1; eapply sepalg_list.list_join_assoc1 in Hj2; eauto.
    destruct Hj2 as (sh' & ? & Hsh').
    erewrite <- data_at_share_join with (sh0 := sh) by (apply Hsh').
    forward_call (l, Tsh, AE_inv c g' (vint 0) (comm_R bufs (Znth i shs Tsh) gsh2 g0' g1' g2')).
    { entailer!. }
    { entailer!. }
    { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
        [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
      { apply AE_inv_precise; auto. }
      fast_cancel.
      unfold AE_inv.
      Exists (@nil AE_hist_el) (vint 0).
      unfold comm_R at 1.
      Exists 0 1 1; unfold last_two_reads, last_write, prev_taken; simpl.
      rewrite !sepcon_andp_prop', !sepcon_andp_prop, !sepcon_andp_prop'; apply andp_right;
        [apply prop_right; auto|].
      apply andp_right; [apply prop_right; repeat (split; auto); computable|].
      change_compspecs CompSpecs.
      Exists 0; fast_cancel.
      rewrite <- emp_sepcon at 1; apply sepcon_derives.
      { apply andp_right; auto; eapply derives_trans; [|apply comm_R_precise]; auto. }
      cancel_frame. }
    Exists (locks ++ [l]) (comms ++ [c]) (g ++ [g']) (g0 ++ [g0']) (g1 ++ [g1']) (g2 ++ [g2'])
      (reads ++ [rr]) (lasts ++ [ll]) sh'; rewrite !upd_init; try omega.
    rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; rewrite <- !app_assoc.
    go_lower.
    apply andp_right; [apply prop_right; split; auto; omega|].
    apply andp_right; [apply prop_right; repeat split; auto|].
    assert_PROP (isptr ll /\ isptr rr /\ isptr c /\ isptr l) by (entailer!; eauto).
    rewrite prop_true_andp
      by  (rewrite ?Forall_app; repeat split; auto; try omega; repeat constructor; intuition).
    rewrite !prop_true_andp
      by  (rewrite ?Forall_app; repeat split; auto; try omega; repeat constructor; intuition).
    rewrite Z2Nat.inj_add, upto_app, !map_app, !sepcon_app; try omega; simpl.
    change (upto 1) with [0]; simpl.
    rewrite Z2Nat.id, Z.add_0_r by omega.
    rewrite !Znth_app1 by auto.
    replace (Z.to_nat (N - (Zlength locks + 1))) with (Z.to_nat (N - (i + 1))) by (subst; clear; rep_omega).
    subst; rewrite Zlength_correct, Nat2Z.id.
    rewrite <- lock_struct_array; unfold AE_inv.
    rewrite !sem_cast_neutral_ptr by intuition.
    erewrite map_ext_in; [cancel|].
    { rewrite sepcon_comm; apply sepcon_derives; auto; apply derives_refl. }
    intros; rewrite In_upto, <- Zlength_correct in *.
    rewrite !app_Znth1; try omega; reflexivity. }
  Intros locks comms g g0 g1 g2 reads lasts sh.
  match goal with H : sepalg_list.list_join sh1 (sublist N N shs) sh |- _ =>
    rewrite sublist_nil in H; inv H end.
  forward.
  rewrite !app_nil_r.
  Exists comms locks bufs reads lasts g g0 g1 g2.
  (* entailer! is slow *)
  apply andp_right; [apply prop_right; repeat (split; auto)|].
  apply andp_right; auto; cancel.
Qed.

Ltac entailer_for_load_tac ::= unfold tc_efield; go_lower; entailer'.
Ltac entailer_for_store_tac ::= unfold tc_efield; go_lower; entailer'.

Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  start_function.
  rewrite (data_at_isptr _ tint); Intros.
  replace_SEP 0 (data_at Tsh tint (vint r) (force_val (sem_cast_pointer arg))).
  { rewrite sem_cast_neutral_ptr; auto; go_lowerx; cancel. }
  forward.
  forward_call (r, reading, last_read, reads, lasts, sh1).
(*  eapply semax_seq'; [|apply semax_ff]. *)
  set (c := Znth r comms Vundef).
  set (l := Znth r locks Vundef).
  forward_loop (EX b0 : Z, EX h : hist, PROP (0 <= b0 < B; latest_read h (vint b0))
    LOCAL (temp _r (vint r); temp _arg arg; gvar _reading reading; gvar _last_read last_read; 
           gvar _lock lock; gvar _comm comm; gvar _bufs buf)
    SEP (data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
         data_at Tsh tint Empty (Znth r reads Vundef); data_at Tsh tint (vint b0) (Znth r lasts Vundef);
         data_at Tsh tint (vint r) (force_val (sem_cast_pointer arg)); malloc_token Tsh tint arg;
         data_at sh1 (tarray (tptr tint) N) comms comm;
         data_at sh1 (tarray (tptr tlock) N) locks lock;
         data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
         comm_loc sh2 l c g g0 g1 g2 bufs sh gsh2 h;
         EX v : Z, @data_at CompSpecs sh tbuffer (vint v) (Znth b0 bufs Vundef);
         ghost_var gsh1 (vint b0) g0))
  break: (@FF (environ->mpred) _).
  { Exists 1 ([] : hist); entailer!. split. unfold B,N. computable.
    unfold latest_read; auto. }
  Intros b0 h.
  subst c l; subst; forward_call (r, reading, last_read, lock, comm, reads, lasts, locks, comms, bufs,
    sh, sh1, sh2, b0, g, g0, g1, g2, h).
  { cancel. }
  { repeat (split; auto). }
  Intros x; destruct x as (((b, t), e), v); simpl in *.
  rewrite (data_at_isptr _ tbuffer); Intros.
  forward.
  forward.
  forward_call (r, reading, reads, sh1).
  { cancel. }
  entailer!.
  Exists b (h ++ [(t, AE e Empty)]) v; entailer!.
Qed.

Lemma body_writer : semax_body Vprog Gprog f_writer writer_spec.
Proof.
  start_function.
  forward_call (writing, last_given, last_taken).
  forward.
  forward_loop (EX v : Z, EX b0 : Z, EX lasts : list Z, EX h : list hist,
   PROP (0 <= b0 < B; Forall (fun x => 0 <= x < B) lasts; Zlength h = N; ~In b0 lasts)
   LOCAL (temp _v (vint v); temp _arg arg; gvar _writing writing; gvar _last_given last_given;
   gvar _last_taken last_taken; gvar _lock lock; gvar _comm comm; gvar _bufs buf)
   SEP (data_at Ews tint Empty writing; data_at Ews tint (vint b0) last_given;
   data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken;
   data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
   data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
   fold_right sepcon emp (map (fun r0 => comm_loc lsh (Znth r0 locks Vundef) (Znth r0 comms Vundef)
     (Znth r0 g Vundef) (Znth r0 g0 Vundef) (Znth r0 g1 Vundef) (Znth r0 g2 Vundef) bufs
     (Znth r0 shs Tsh) gsh2 (Znth r0 h [])) (upto (Z.to_nat N)));
   fold_right sepcon emp (map (fun r0 => ghost_var gsh1 (vint b0) (Znth r0 g1 Vundef) *
     ghost_var gsh1 (vint (Znth r0 lasts (-1))) (Znth r0 g2 Vundef)) (upto (Z.to_nat N)));
   fold_right sepcon emp (map (fun i => EX sh : share, !! (if eq_dec i b0 then sh = sh0
     else sepalg_list.list_join sh0 (make_shares shs lasts i) sh) &&
     (EX v : Z, @data_at CompSpecs sh tbuffer (vint v) (Znth i bufs Vundef))) (upto (Z.to_nat B)))))
  break: (@FF (environ->mpred) _).
  { Exists 0 0 (repeat 1 (Z.to_nat N)) (repeat ([] : hist) (Z.to_nat N)); entailer!.
    { split. unfold B, N.  computable. repeat constructor; computable. }
    rewrite sepcon_map.
    apply derives_refl'.
    rewrite !sepcon_assoc; f_equal; f_equal; [|f_equal].
    - rewrite list_Znth_eq with (l := g1) at 1.
      replace (length g1) with (Z.to_nat N) by (symmetry; rewrite <- Zlength_length; auto; unfold N; computable).
      rewrite map_map; auto.
    - rewrite list_Znth_eq with (l := g2) at 1.
      replace (length g2) with (Z.to_nat N) by (symmetry; rewrite <- Zlength_length; auto; unfold N; computable).
      erewrite map_map, map_ext_in; eauto.
      intros; rewrite In_upto in *.
      match goal with |- context[Znth a ?l (-1)] => replace (Znth a l (-1)) with 1; auto end.
      apply Forall_Znth; auto.
    - erewrite map_ext_in; eauto.
      intros; rewrite In_upto in *.
      destruct (eq_dec a 0); auto.
      destruct (eq_dec a 1), (eq_dec 1 a); auto; try omega.
      { apply mpred_ext; Intros sh; Exists sh; entailer!.
        * constructor.
        * match goal with H : sepalg_list.list_join sh0 [] sh |- _ => inv H; auto end. }
      generalize (make_shares_out a (repeat 1 (Z.to_nat N)) shs); simpl; intro Heq.
      destruct (eq_dec 1 a); [contradiction n0; auto|].
       rewrite Heq; auto; [|omega].
      apply mpred_ext; Intros sh; Exists sh; entailer!.
      eapply list_join_eq; eauto. }
  Intros v b0 lasts h.
  rewrite sepcon_map; Intros.
  forward_call (writing, last_given, last_taken, b0, lasts).
  { cancel. }
  Intros b.
  rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat B))) b); [|rewrite Zlength_map; auto].
  erewrite Znth_map, Znth_upto; auto; rewrite ?Z2Nat.id; try omega.
  Intros sh v0.
  rewrite (data_at_isptr _ tbuffer); Intros.
  forward.
  destruct (eq_dec b b0); [absurd (b = b0); auto|].
  assert_PROP (Zlength lasts = N).
  { gather_SEP 2; go_lowerx; apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts|].
    apply prop_left; intros (_ & ? & _); apply prop_right.
    unfold unfold_reptype in *; simpl in *.
    rewrite Zlength_map in *; auto. }
  rewrite make_shares_out in *; auto; [|setoid_rewrite H; auto].
  assert (sh = Tsh) by (eapply list_join_eq; eauto); subst.
  forward.
  gather_SEP 7 8; rewrite <- sepcon_map.
  gather_SEP 8 9; replace_SEP 0 (fold_right sepcon emp (map (fun i => EX sh2 : share,
    !! (if eq_dec i b0 then sh2 = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts i) sh2) &&
    (EX v1 : Z, data_at sh2 tbuffer (vint v1) (Znth i bufs Vundef))) (upto (Z.to_nat B)))).
  { go_lowerx; eapply derives_trans with (Q := _ * _);
      [|erewrite replace_nth_sepcon, upd_Znth_triv; try apply derives_refl; eauto].
    rewrite Znth_map', Znth_upto; [|simpl; unfold B, N in *; omega].
    destruct (eq_dec b b0); [absurd (b = b0); auto|].
    rewrite make_shares_out; auto; [|setoid_rewrite H; auto].
    Exists Tsh v; entailer!. }
  forward_call (writing, last_given, last_taken, comm, lock, comms, locks, bufs, b, b0, lasts,
    sh1, lsh, shs, g, g0, g1, g2, h, sh0).
  { repeat (split; auto). }
  Intros x; destruct x as (lasts', h').
  rewrite sepcon_map; Intros.
  forward.
  Exists (v + 1) b lasts' h'; rewrite sepcon_map; entailer!.
  replace N with (Zlength h) by auto; symmetry; eapply mem_lemmas.Forall2_Zlength; eauto.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  name buf _bufs.
  name lock _lock.
  name comm _comm.
  name reading _reading.
  name last_read _last_read.
  name last_taken _last_taken.
  name writing _writing.
  name last_given _last_given.
  start_function.
  exploit (split_shares (Z.to_nat N) Tsh); auto; intros (sh0 & shs & ? & ? & ? & ?).
  rewrite (data_at__eq _ (tarray (tptr (Tstruct _lock_t noattr)) N)), lock_struct_array.
  forward_call (comm, lock, buf, reading, last_read, sh0, shs).
  Intros x; destruct x as ((((((((comms, locks), bufs), reads), lasts), g), g0), g1), g2).
  assert_PROP (Zlength comms = N).
  { go_lowerx; apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold N; omega|].
    unfold unfold_reptype; simpl.
    apply prop_left; intros (? & ? & ?); apply prop_right; auto. }
  get_global_function'' _writer; Intros.
  apply extract_exists_pre; intros writer_.
  exploit (split_shares (Z.to_nat N) Ews); auto; intros (sh1 & shs1 & ? & ? & ? & ?).
  assert_PROP (Zlength bufs = B).
  { go_lowerx; rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ buf)), !sepcon_assoc.
    apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold B, N; omega|].
    unfold unfold_reptype; simpl.
    apply prop_left; intros (? & ? & ?); apply prop_right; auto. }
  forward_spawn (val * val * val * val * val * val * list val * list val * list val *
                 share * share * share * list share * list val * list val * list val * list val)%type
    (writer_, vint 0, fun x : (val * val * val * val * val * val * list val * list val * list val * share * share *
      share * list share * list val * list val * list val * list val) =>
      let '(writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs,
            g, g0, g1, g2) := x in
      [(_writing, writing); (_last_given, last_given); (_last_taken, last_taken);
       (_lock, lock); (_comm, comm); (_bufs, buf)],
    (writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, gsh1, sh0, shs,
                       g, g0, g1, g2),
    fun (x : (val * val * val * val * val * val * list val * list val * list val *
              share * share * share * list share * list val * list val * list val * list val)%type)
        (arg : val) =>
    let '(writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs,
          g, g0, g1, g2) := x in
      fold_right sepcon emp [!!(fold_right and True [Zlength shs = N; readable_share sh1; readable_share lsh;
        Forall readable_share shs; sepalg_list.list_join sh0 shs Tsh;
        Zlength g1 = N; Zlength g2 = N; Forall isptr comms]) && emp;
        data_at_ Ews tint writing; data_at_ Ews tint last_given; data_at_ Ews (tarray tint N) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
        fold_right sepcon emp (map (fun r => comm_loc lsh (Znth r locks Vundef) (Znth r comms Vundef)
          (Znth r g Vundef) (Znth r g0 Vundef) (Znth r g1 Vundef) (Znth r g2 Vundef) bufs
          (Znth r shs Tsh) gsh2 []) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2);
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i 0 then sh = sh0 else if eq_dec i 1 then sh = sh0 else sh = Tsh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B)))]).
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
      erewrite gvar_eval_var, !(force_val_sem_cast_neutral_gvar' _ writer_) by eauto.
      rewrite eval_id_same, eval_id_other, eval_id_same; [|discriminate].
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
    unfold comm_loc; erewrite map_ext;
      [|intro; erewrite <- AE_loc_join with (h1 := [])(h2 := []); eauto; reflexivity].
    rewrite !sepcon_map.
    do 3 (erewrite <- (data_at_shares_join Ews); eauto).
    rewrite (extract_nth_sepcon (map (data_at _ _ _) (sublist 1 _ bufs)) 0), Znth_map with (d' := Vundef);
      rewrite ?Zlength_map, ?Zlength_sublist; try (unfold B, N in *; omega).
    erewrite <- (data_at_shares_join Tsh); eauto.
    rewrite (sepcon_comm (data_at sh0 _ _ (Znth 0  (sublist _ _ bufs) Vundef))),
      (sepcon_assoc _ (data_at sh0 _ _ _)).
    rewrite replace_nth_sepcon.
    fast_cancel.
    rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at sh0 _ _ _)).
    rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right sepcon emp (upd_Znth 0 _ _))), !sepcon_assoc.
    rewrite <- sepcon_assoc; apply sepcon_derives; [|cancel_frame].
    assert (Zlength (data_at sh0 tbuffer (vint 0) (Znth 0 bufs Vundef)
         :: upd_Znth 0 (map (data_at Tsh tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs))
              (data_at sh0 tbuffer (vint 0) (Znth 0 (sublist 1 (Zlength bufs) bufs) Vundef))) = B) as Hlen.
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
        fold_right sepcon emp (map (fun x => comm_loc gsh2 (Znth x locks Vundef) (Znth x comms Vundef)
          (Znth x g Vundef) (Znth x g0 Vundef) (Znth x g1 Vundef) (Znth x g2 Vundef) bufs (Znth x shs Tsh) gsh2
          []) (sublist i N (upto (Z.to_nat N))));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) (sublist i N g0));
        fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i N reads));
        fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i N lasts));
        fold_right sepcon emp (map (malloc_token Tsh tint) comms);
        fold_right sepcon emp (map (malloc_token Tsh tlock) locks);
        fold_right sepcon emp (map (malloc_token Tsh tbuffer) bufs);
        fold_right sepcon emp (map (malloc_token Tsh tint) reads);
        fold_right sepcon emp (map (malloc_token Tsh tint) lasts);
        fold_right sepcon emp (map (fun sh => @data_at CompSpecs sh tbuffer (vint 0) (Znth 1 bufs Vundef)) (sublist i N shs)))).
  { unfold N; computable. }
  { Exists Ews; rewrite !sublist_same; auto; unfold N; entailer!. }
  { Intros sh'.
    forward_call tint. split3; simpl; auto; computable. Intros d.
    forward.
    get_global_function'' _reader; Intros.
    apply extract_exists_pre; intros reader_.
    match goal with H : sepalg_list.list_join sh1 _ sh' |- _ => rewrite sublist_next with (d0 := Tsh) in H;
      auto; [inversion H as [|????? Hj1 Hj2]; subst |
      match goal with H : Zlength shs1 = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; omega end] end.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh1' & ? & Hj').
    forward_spawn (Z * val * val * val * val * val * list val * list val * list val * list val * list val *
                   share * share * share * val * val * val * val)%type
      (reader_, d, fun x : (Z * val * val * val * val * val * list val * list val * list val * list val *
        list val * share * share * share * val * val * val * val) =>
        let '(r, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs, sh1, sh2, sh,
              g, g0, g1, g2) := x in
        [(_reading, reading); (_last_read, last_read); (_lock, lock); (_comm, comm); (_bufs, buf)],
      (i, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs,
                    Znth i shs1 Tsh, gsh2, Znth i shs Tsh, Znth i g Vundef, Znth i g0 Vundef, Znth i g1 Vundef,
                    Znth i g2 Vundef),
      fun (x : (Z * val * val * val * val * val * list val * list val * list val * list val * list val *
                share * share * share * val * val * val * val)%type) (arg : val) =>
        let '(r, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs, sh1, sh2, sh,
              g, g0, g1, g2) := x in
        fold_right sepcon emp [!!(fold_right and True [readable_share sh; readable_share sh1; 
          readable_share sh2; isptr (Znth r comms Vundef)]) && emp;
          data_at Tsh tint (vint r) arg; malloc_token Tsh tint arg;
          data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
          data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
          data_at_ Tsh tint (Znth r reads Vundef); data_at_ Tsh tint (Znth r lasts Vundef);
          data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
          comm_loc sh2 (Znth r locks Vundef) (Znth r comms Vundef) g g0 g1 g2 bufs sh gsh2 [];
          EX v : Z, data_at sh tbuffer (vint v) (Znth 1 bufs Vundef);
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
      rewrite sublist_next with (d0 := Tsh); auto;
        [simpl | match goal with H : Zlength shs1 = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; omega end].
      simpl in *; rewrite !sublist_next with (i0 := i)(d0 := Vundef); auto; try omega; simpl.
      rewrite sublist_next with (d0 := N); rewrite ?Znth_upto; auto; rewrite? Zlength_upto; simpl;
        try (unfold N in *; omega).
      rewrite sublist_next with (i0 := i)(d0 := Tsh); auto; simpl.
      Exists 0; fast_cancel.
      { match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; unfold N; omega end. }
    - Exists sh1'; entailer!. }
    forward_loop (PROP()LOCAL()(SEP(TT))) break: (@FF (environ->mpred) _).
    entailer!.
    forward. entailer!.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

(* This lemma ties all the function proofs into a single proof for the entire program. *)
Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct, main_pre, main_post, prog_vars; simpl.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
repeat semax_func_cons_ext.
semax_func_cons body_malloc. apply semax_func_cons_malloc_aux.
repeat semax_func_cons_ext.
{ unfold PROPx, LOCALx, local, lift1, liftx, lift; simpl.
  unfold liftx, lift; simpl.
  Intros; subst.
  apply prop_right; unfold make_ext_rval, eval_id in *; simpl in *.
  destruct ret; auto. }
semax_func_cons body_surely_malloc.
semax_func_cons body_memset.
semax_func_cons body_initialize_channels.
semax_func_cons body_initialize_reader.
semax_func_cons body_start_read.
semax_func_cons body_finish_read.
semax_func_cons body_initialize_writer.
eapply semax_func_cons; [ reflexivity
           | repeat apply Forall_cons; try apply Forall_nil; simpl; auto; computable
           | unfold var_sizes_ok; repeat constructor; simpl; computable | reflexivity | precondition_closed
           | apply body_start_write |].
{ apply closed_wrtl_PROPx, closed_wrtl_LOCALx, closed_wrtl_SEPx.
  repeat constructor; apply closed_wrtl_gvar; unfold is_a_local; simpl; intros [? | ?];
    try contradiction; discriminate. }
semax_func_cons body_finish_write.
semax_func_cons body_reader.
semax_func_cons body_writer.
semax_func_cons body_main.
Qed.
