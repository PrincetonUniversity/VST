Require Import mailbox.general_atomics.
Require Import VST.progs.conclib.
Require Import VST.progs.ghost.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox_bad.
Require Import mailbox.verif_mailbox_bad_specs.
Require Import mailbox.verif_mailbox_bad_read.
Require Import mailbox.verif_mailbox_bad_write.

Set Bullet Behavior "Strict Subproofs".

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call n.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh n p * memory_block Tsh n p)).
  - if_tac; entailer!.
  - forward_call tt.
    contradiction.
  - if_tac.
    + forward. subst p. discriminate.
    + Intros. forward. entailer!.
  - forward. Exists p; entailer!.
Qed.

Lemma body_memset : semax_body Vprog Gprog f_memset memset_spec.
Proof.
  start_function.
  forward.
  rewrite data_at__isptr; Intros.
  rewrite sem_cast_neutral_ptr; auto.
  pose proof (sizeof_pos t).
  assert (vint n = force_val (sem_div tuint tint (vint (4 * n)) (vint 4))) as H4.
  { unfold sem_div; simpl.
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
        destruct H as (? & ? & ? & ? & ? & ? & ? & ?) end; repeat split; simpl; auto.
      + unfold legal_alignas_type, tarray, nested_pred, local_legal_alignas_type; simpl.
        rewrite andb_true_r, Z.leb_le; omega.
      + setoid_rewrite Hsize; auto.
      + unfold size_compatible in *; simpl.
        destruct p; try contradiction.
        setoid_rewrite Hsize; auto.
      + unfold align_compatible in *; simpl.
        unfold align_attr in *; simpl.
        destruct p; try contradiction.
        etransitivity; eauto.
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

Lemma body_initialize_channels : semax_body Vprog Gprog f_initialize_channels initialize_channels_spec.
Proof.
  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound B (EX i : Z, PROP ()
    LOCAL (gvar _comm comm; gvar _bufs buf; gvar _reading reading; gvar _last_read last_read)
    SEP (data_at_ Ews (tarray (tptr tint) N) comm;
         data_at_ Ews (tarray (tptr tint) N) reading; data_at_ Ews (tarray (tptr tint) N) last_read;
         EX bufs : list val, !!(Zlength bufs = i /\ Forall isptr bufs) &&
           data_at Ews (tarray (tptr tbuffer) B) (bufs ++ repeat Vundef (Z.to_nat (B - i))) buf *
           fold_right sepcon emp (map (@data_at CompSpecs Tsh tbuffer (vint 0)) bufs) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs))).
  { unfold B, N; computable. }
  { unfold B, N; computable. }
  { entailer!.
    Exists ([] : list val); simpl; entailer!. }
  { forward_call (sizeof tbuffer).
    { simpl; computable. }
    Intros b bufs.
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    assert_PROP (field_compatible tbuffer [] b) by entailer!.
    forward_call (Tsh, tbuffer, b, 0, 1).
    { repeat split; simpl; auto; try computable.
      apply Z.divide_refl. }
    forward.
    rewrite upd_init; auto; try omega.
    entailer!.
    Exists (bufs ++ [b]); rewrite Zlength_app, <- app_assoc, !map_app, !sepcon_app, Forall_app; simpl; entailer!.
    clear; unfold data_at, field_at, at_offset; Intros.
    rewrite !data_at_rec_eq; unfold withspacer; simpl.
    unfold array_pred, aggregate_pred.array_pred, unfold_reptype; simpl.
    entailer!.
    { exists 2; auto. } }
  Intros bufs; rewrite Zminus_diag, app_nil_r.
  forward_for_simple_bound N (EX i : Z, EX shi : share,
    PROP (sepalg_list.list_join shg (map snd (filter (fun '(b, _) => negb b)
      (sublist i N (combine lgood shs)))) shi)
    LOCAL (gvar _comm comm; gvar _bufs buf; gvar _reading reading; gvar _last_read last_read)
    SEP (EX comms : list val, EX g : list val, EX g0 : list val, EX g1 : list val,
         EX g2 : list val, !!(Zlength comms = i /\ Forall isptr comms /\ Forall isptr bufs /\
           Zlength g = i /\ Zlength g0 = i /\ Zlength g1 = i /\ Zlength g2 = i) &&
          (data_at Ews (tarray (tptr tint) N) (comms ++ repeat Vundef (Z.to_nat (N - i))) comm *
           fold_right sepcon emp (map (fun r => comm_loc (Znth r lgood false) Tsh (Znth r comms Vundef)
             (Znth r g Vundef) (Znth r g0 Vundef) (Znth r g1 Vundef) (Znth r g2 Vundef) bufs
             (Znth r shs Tsh) gsh2 []) (upto (Z.to_nat i))) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g0) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) comms));
         EX reads : list val, !!(Zlength reads = i) &&
           data_at Ews (tarray (tptr tint) N) (reads ++ repeat Vundef (Z.to_nat (N - i))) reading *
           fold_right sepcon emp (map (data_at_ Tsh tint) reads) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) reads);
         EX lasts : list val, !!(Zlength lasts = i) &&
           data_at Ews (tarray (tptr tint) N) (lasts ++ repeat Vundef (Z.to_nat (N - i))) last_read *
           fold_right sepcon emp (map (data_at_ Tsh tint) lasts) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) lasts);
         @data_at CompSpecs Ews (tarray (tptr tbuffer) B) bufs buf;
         EX sh : share, !!(sepalg_list.list_join sh1 (sublist i N shs) sh) &&
           @data_at CompSpecs sh tbuffer (vint 0) (Znth 0 bufs Vundef);
         fold_right sepcon emp (map (@data_at CompSpecs shi tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs));
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs))).
  { unfold N; computable. }
  { unfold N; computable. }
  { rewrite !sublist_same by (auto; rewrite Zlength_combine, Z.min_l; omega).
    Exists Tsh ([] : list val) ([] : list val) ([] : list val) ([] : list val) ([] : list val)
      ([] : list val) ([] : list val) Tsh; rewrite !data_at__eq; entailer!.
    - eapply list_join_minus; eauto; omega.
    - erewrite <- sublist_same with (al := bufs), sublist_next at 1; eauto; try (unfold B, N in *; omega).
      simpl; cancel. }
  { Intros comms g g0 g1 g2 reads lasts sh.
    forward_malloc tint c.
    forward.
    forward.
    forward_malloc tint rr.
    forward.
    forward_malloc tint ll.
    eapply (ghost_alloc (Tsh, vint 1)); auto with init.
    eapply (ghost_alloc (Tsh, vint 0)); auto with init.
    eapply (ghost_alloc (Tsh, vint 1)); auto with init.
    eapply (ghost_alloc (Some (Tsh, [] : hist), Some ([] : hist))); auto with init.
    Intros g' g0' g1' g2'.
    rewrite <- hist_ref_join_nil by apply Share.nontrivial.
    repeat match goal with |-context[ghost (Tsh, ?v) ?g] => fold (ghost_var Tsh v g) end.
    erewrite <- !ghost_var_share_join with (sh0 := Tsh) by eauto.
    match goal with H : sepalg_list.list_join sh1 (sublist i N shs) sh |- _ =>
      erewrite sublist_next in H; try omega; inversion H as [|????? Hj1 Hj2] end.
    apply sepalg.join_comm in Hj1; eapply sepalg_list.list_join_assoc1 in Hj2; eauto.
    destruct Hj2 as (sh' & ? & Hsh').
    erewrite <- data_at_share_join with (sh0 := sh) by (apply Hsh').
    assert (Zlength (combine lgood shs) = N) by (rewrite Zlength_combine, Z.min_l; omega).
    assert (exists sha x', sepalg_list.list_join shg
      (map snd (filter (fun '(b, _) => negb b) (sublist (i + 1) N (combine lgood shs)))) x' /\
      sepalg.join sha x' x /\ if Znth i lgood false then x' = x /\ sha = Share.bot else sha = a)
      as (sha & x' & ? & Hx & Hcase).
    { match goal with H : sepalg_list.list_join shg _ _ |- _ =>
        rewrite sublist_next with (d := (false, Tsh)), Znth_combine in H by omega; simpl in H end.
      destruct (Znth i lgood false); simpl in *; eauto 6.
      match goal with H : sepalg_list.list_join shg _ _ |- _ => inversion H as [|????? Hx1 Hx2]; subst end.
      destruct (sepalg_list.list_join_assoc1 (sepalg.join_comm Hx1) Hx2) as (? & ? & ?).
      do 3 eexists; eauto; split; eauto; discriminate. }
    replace (map (@data_at CompSpecs x tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs)) with
      (map (fun p => (if Znth i lgood false then emp else data_at sha tbuffer (vint 0) p) *
        data_at x' tbuffer (vint 0) p) (sublist 1 (Zlength bufs) bufs)).
    rewrite sepcon_map; Intros.
    gather_SEP 1 3 5 7 13 27 29; eapply make_inv with (Q := comm_inv (Znth i lgood false)
      c bufs (Znth i shs Tsh) g' g0' g1' g2' gsh2).
    { unfold comm_inv.
      Exists 0; cancel.
      destruct (Znth _ lgood false) eqn: Hgood.
      - Exists (@nil AE_hist_el); unfold comm_R.
        Exists 1 1; unfold last_two_reads, last_write, prev_taken; simpl; entailer!.
        Exists Int.zero; entailer!.
        rewrite fold_right_emp; auto.
        rewrite Forall_map, Forall_forall; auto.
      - Exists (@nil AE_hist_el) (vint 1) (vint 0) (vint 1); entailer!.
        assert (Zlength (data_at (Znth (Zlength comms) shs Tsh) tbuffer (vint 0) (Znth 0 bufs Vundef)
          :: map (fun x0 : val => data_at (Znth (Zlength comms) shs Tsh) tbuffer (vint 0) x0)
          (sublist 1 (Zlength bufs) bufs)) = B).
        { rewrite Zlength_cons, Zlength_map, Zlength_sublist; try omega.
          unfold B, N in *; omega. }
        apply sepcon_list_derives with (l1 := _ :: _).
        { rewrite Zlength_map; omega. }
        intros; erewrite Znth_map by omega.
        Exists Int.zero; destruct (eq_dec i 0).
        + subst; rewrite Znth_0_cons; auto.
        + rewrite Znth_pos_cons by omega.
          erewrite Znth_map, Znth_sublist, Z.sub_simpl_r; auto; try omega.
          rewrite Zlength_cons, Zlength_map in *; omega. }
    { unfold comm_inv, comm_R; prove_objective. }
    forward.
    Exists x' (comms ++ [c]) (g ++ [g']) (g0 ++ [g0']) (g1 ++ [g1']) (g2 ++ [g2'])
      (reads ++ [rr]) (lasts ++ [ll]) sh'; rewrite !upd_init; try omega.
    rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; rewrite <- !app_assoc.
    go_lower.
    apply andp_right; [apply prop_right; split; auto; omega|].
    apply andp_right; [apply prop_right; repeat split; auto|].
    rewrite !sepcon_andp_prop'; apply andp_right; [apply prop_right; rewrite Forall_app; repeat split; auto;
      omega|].
    rewrite !sepcon_andp_prop; repeat (apply andp_right; [apply prop_right; auto; try omega|]).
    rewrite Z2Nat.inj_add, upto_app, !map_app, !sepcon_app; try omega; simpl.
    change (upto 1) with [0]; simpl.
    rewrite Z2Nat.id, Z.add_0_r by omega.
    rewrite !Znth_app1 by auto.
    subst; rewrite Zlength_correct, Nat2Z.id.
    rewrite !sem_cast_neutral_ptr by auto.
    erewrite map_ext_in; [unfold comm_loc; cancel|].
    intros; rewrite In_upto, <- Zlength_correct in *.
    rewrite !app_Znth1; try omega; reflexivity. 
    { apply map_ext; intro.
      if_tac.
      - rewrite emp_sepcon; f_equal; tauto.
      - subst; apply data_at_share_join; auto. } }
  Intros x comms g g0 g1 g2 reads lasts sh.
  match goal with H : sepalg_list.list_join _ (sublist N N shs) _ |- _ =>
    rewrite sublist_nil in H; inv H end.
  match goal with H : sepalg_list.list_join shg _ _ |- _ =>
    rewrite sublist_nil in H; inv H end.
  forward.
  rewrite !app_nil_r.
  Exists comms bufs reads lasts g g0 g1 g2; entailer!.
Qed.

Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  start_function.
  rewrite (data_at_isptr _ tint); Intros.
  replace_SEP 0 (data_at Tsh tint (vint r) (force_val (sem_cast_neutral arg))).
  { rewrite sem_cast_neutral_ptr; auto; go_lowerx; cancel. }
  forward.
  forward_call (r, reading, last_read, reads, lasts, sh1).
  eapply semax_seq'; [|apply semax_ff].
  set (c := Znth r comms Vundef).
  eapply semax_pre with (P' := EX b0 : Z, EX h : hist, PROP (0 <= b0 < B; latest_read h b0)
    LOCAL (temp _r (vint r); temp _arg arg; gvar _reading reading; gvar _last_read last_read; 
           gvar _comm comm; gvar _bufs buf)
    SEP (data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
         data_at Tsh tint Empty (Znth r reads Vundef); data_at Tsh tint (vint b0) (Znth r lasts Vundef);
         data_at Tsh tint (vint r) (force_val (sem_cast_neutral arg)); malloc_token Tsh (sizeof tint) arg;
         data_at sh1 (tarray (tptr tint) N) comms comm;
         data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
         comm_loc good sh2 c g g0 g1 g2 bufs sh gsh2 h;
         if good then EX v : _, @data_at CompSpecs sh tbuffer (Vint v) (Znth b0 bufs Vundef) else emp;
         ghost_var gsh1 (vint b0) g0)).
  { Exists 1 ([] : hist); entailer!.
    unfold latest_read; auto. }
  eapply semax_loop; [|forward; apply ENTAIL_refl].
  Intros b0 h.
  forward.
  subst c; subst; forward_call (r, reading, last_read, comm, reads, lasts, good, comms, bufs,
    sh, sh1, sh2, b0, g, g0, g1, g2, h).
  { repeat (split; auto). }
  Intros x; destruct x as ((b, t), e); simpl in *.
  assert_PROP (Zlength bufs = B) as Hlen by entailer!.
  assert (isptr (Znth (if ((0 <=? e) && (e <? B))%bool then e else b0) bufs Vundef)).
  { apply Forall_Znth; auto; omega. }
  forward.
  forward_call (load_SC_witness (Znth b bufs Vundef)
    (if good then EX v : _, data_at sh tbuffer (Vint v) (Znth b bufs Vundef) else emp)
    (fun _ : Z => comm_inv good (Znth r comms Vundef) bufs sh g g0 g1 g2 gsh2) [0]
    (fun v' => if good then data_at sh tbuffer (vint v') (Znth b bufs Vundef) else emp)).
  { entailer!. }
  { simpl; unfold comm_loc; cancel. }
  { apply wand_view_shifts2.
    apply derives_view_shift.
    simpl; unfold comm_inv.
    Exists sh; Intros b'; destruct good.
    - Intros v; Exists (Int.signed v).
      unfold_data_at 2%nat.
      rewrite field_at_data_at'; simpl; rewrite Int.repr_signed, sepcon_andp_prop'; apply andp_right.
      { entailer!.
        apply Int.signed_range; auto. }
      entailer!.
      rewrite <- wand_sepcon_adjoint.
      Exists b' x; entailer!.
      unfold_data_at 2%nat.
      rewrite field_at_data_at'; simpl; entailer!; auto.
    - rewrite !sepcon_emp, <- !sepcon_assoc, sepcon_comm.
      rewrite extract_nth_sepcon with (i := b) by (rewrite Zlength_map; omega).
      erewrite Znth_map by omega; Intro v.
      Exists (Int.signed v); rewrite Int.repr_signed.
      rewrite !sepcon_assoc; apply sepcon_derives.
      { unfold_data_at 1%nat.
        rewrite field_at_data_at'; entailer!; eauto.
        apply Int.signed_range; auto. }
      rewrite <- wand_sepcon_adjoint.
      rewrite <- !exp_sepcon1; cancel.
      Exists b' v; entailer!.
      unfold_data_at 2%nat.
      rewrite field_at_data_at'; simpl; entailer!; auto. }
  Intros d.
  forward_call (r, reading, reads, sh1).
  go_lower.
  Exists b (h ++ [(t, AE (vint e) Empty)]); unfold comm_loc; entailer!.
  if_tac; auto; Exists (Int.repr d); auto.
Qed.

Lemma sepcon_filter_combine : forall {A} P (l : list A) l', Zlength l' = Zlength l ->
  fold_right sepcon emp (map P l) =
  fold_right sepcon emp (map P (map snd (filter fst (combine l' l)))) *
  fold_right sepcon emp (map P (map snd (filter (fun '(b, _) => negb b) (combine l' l)))).
Proof.
  induction l; intros.
  { rewrite combine_nil; simpl; rewrite sepcon_emp; auto. }
  destruct l'; [symmetry in H; apply Zlength_nil_inv in H; discriminate|].
  simpl.
  rewrite !Zlength_cons in *; rewrite (IHl l') by omega.
  destruct b; simpl; apply mpred_ext; cancel.
Qed.

Lemma data_at_shares_join' : forall {cs} sh v p shs sh1
  (Hsplit : sepalg_list.list_join sh1 shs sh), readable_share sh1 ->
  @data_at cs sh1 tint (Vint v) p *
    fold_right_sepcon (map (fun sh => EX v : _, data_at sh tint (Vint v) p) shs) =
  data_at sh tint (Vint v) p.
Proof.
  induction shs; intros; simpl.
  - inv Hsplit.
    rewrite sepcon_emp; auto.
  - inv Hsplit.
    erewrite <- IHshs; eauto.
    apply mpred_ext; cancel; rewrite <- (data_at_share_join sh1 a w1) by auto.
    + Intro v'; apply data_at_value_cohere; auto.
    + Exists v; auto.
    + eapply readable_share_join; eauto.
Qed.

Lemma map_snd_filter_fst : forall {A B C} f (g : B -> C) (l : list (A * B)),
  filter (fun '(a, _) => f a) (map (fun '(a, b) => (a, g b)) l) =
  map (fun '(a, b) => (a, g b)) (filter (fun '(a, _) => f a) l).
Proof.
  induction l; auto; simpl.
  destruct a.
  rewrite IHl; if_tac; auto.
Qed.

Lemma body_writer : semax_body Vprog Gprog f_writer writer_spec.
Proof.
  start_function.
  forward_call (writing, last_given, last_taken).
  forward.
  eapply semax_seq'; [|apply semax_ff].
  eapply semax_pre with (P' := EX v : Z, EX b0 : Z, EX lasts : list Z, EX h : list hist,
   PROP (0 <= b0 < B; Forall (fun x => 0 <= x < B) lasts; Zlength h = N; ~In b0 lasts)
   LOCAL (temp _v (vint v); temp _arg arg; gvar _writing writing; gvar _last_given last_given;
   gvar _last_taken last_taken; gvar _comm comm; gvar _bufs buf)
   SEP (data_at Ews tint Empty writing; data_at Ews tint (vint b0) last_given;
   data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken;
   data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
   fold_right sepcon emp (map (fun r0 => comm_loc (Znth r0 lgood false) lsh (Znth r0 comms Vundef)
     (Znth r0 g Vundef) (Znth r0 g0 Vundef) (Znth r0 g1 Vundef) (Znth r0 g2 Vundef) bufs
     (Znth r0 shs Tsh) gsh2 (Znth r0 h [])) (upto (Z.to_nat N)));
   fold_right sepcon emp (map (fun r0 => ghost_var gsh1 (vint b0) (Znth r0 g1 Vundef) *
     ghost_var gsh1 (vint (Znth r0 lasts (-1))) (Znth r0 g2 Vundef)) (upto (Z.to_nat N)));
   fold_right sepcon emp (map (fun i => EX sh : share, !! (if eq_dec i b0 then sh = sh0
     else sepalg_list.list_join sh0 (make_shares shs (combine lgood lasts) i) sh) &&
     (EX v : _, @data_at CompSpecs sh tbuffer (Vint v) (Znth i bufs Vundef))) (upto (Z.to_nat B))))).
  { Exists 0 0 (repeat 1 (Z.to_nat N)) (repeat ([] : hist) (Z.to_nat N)); entailer!.
    { split; [repeat constructor; computable | omega]. }
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
      replace (make_shares _ _ _) with
        (if eq_dec a 1 then [] else map snd (filter fst (combine lgood shs))).
      destruct (eq_dec a 1), (eq_dec 1 a); auto; try omega; apply mpred_ext; Intros sh; Exists sh;
        entailer!.
      + constructor.
      + match goal with H : sepalg_list.list_join sh0 [] sh |- _ => inv H; auto end.
      + eapply list_join_eq; eauto.
      + if_tac.
        * subst; destruct lgood; auto; simpl.
          rewrite orb_true_r; destruct lgood; auto; simpl.
          rewrite orb_true_r; destruct lgood; auto; simpl.
          rewrite orb_true_r, combine_nil; auto.
        * symmetry; apply make_shares_out; auto; [|unfold share in *; omega].
          intros [|[|[|]]]; auto. }
  eapply semax_loop; [|forward; apply ENTAIL_refl].
  Intros v b0 lasts h.
  rewrite sepcon_map; Intros.
  forward.
  forward_call (writing, last_given, last_taken, b0, lasts).
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
  rewrite make_shares_out in *; auto; unfold share in *; try omega.
  assert (sh = shg) by (eapply list_join_eq; eauto); subst.
  assert_PROP (Zlength bufs = B) by entailer!.
  forward_call (store_SC_witness (Znth b bufs Vundef) (Int.signed (Int.repr v))
    (data_at shg tbuffer (Vint v0) (Znth b bufs Vundef))
    (fun r => comm_inv (Znth r lgood false) (Znth r comms Vundef) bufs (Znth r shs Tsh)
      (Znth r g Vundef) (Znth r g0 Vundef) (Znth r g1 Vundef) (Znth r g2 Vundef) gsh2)
    (map snd (filter (fun '(b, _) => negb b) (combine lgood (upto (Z.to_nat N)))))
    (data_at shg tbuffer (vint v) (Znth b bufs Vundef))).
  { entailer!.
    rewrite Int.repr_signed; auto. }
  { unfold comm_loc; rewrite sepcon_map.
    rewrite sepcon_filter_combine with (l' := lgood) by auto; cancel. }
  { split; [apply Int.signed_range; auto|].
    apply wand_view_shifts.
    apply derives_view_shift.
    Exists Tsh; rewrite Int.repr_signed, !prop_true_andp by auto.
    unfold_data_at 1%nat.
    rewrite field_at_data_at'; simpl; Intros.
    erewrite wand_sepcon_map with
      (P := fun r => EX v : _, data_at (Znth r shs Tsh) tint (Vint v) (Znth b bufs Vundef)) at 1.
    rewrite data_at__eq.
    assert (Zlength lgood = Zlength shs) by omega.
    assert (readable_share shg) by (eapply readable_share_list_join; eauto).
    assert (map (fun sh => EX v1 : _, data_at sh tint (Vint v1) (Znth b bufs Vundef))
     (map snd (filter (fun '(b1, _) => negb b1) (combine lgood shs))) =
     map (fun r => EX v1 : _, data_at (Znth r shs Tsh) tint (Vint v1) (Znth b bufs Vundef))
     (map snd (filter (fun '(b1, _) => negb b1) (combine lgood (upto 3))))) as Heq.
    { setoid_rewrite (list_Znth_eq Tsh shs) at 1.
      rewrite <- ZtoNat_Zlength; unfold share in *; replace (Zlength shs) with N; unfold N; simpl.
      rewrite combine_map_snd, map_snd_filter_fst, !map_map.
      apply map_ext; intros (?, ?); auto. }
    rewrite sepcon_comm, <- sepcon_assoc; apply sepcon_derives.
    - apply derives_trans with (Q := data_at Tsh tint (Vint v0) (Znth b bufs Vundef)); [|cancel].
      erewrite <- data_at_shares_join' with (sh := Tsh) by (try eapply list_join_minus; eauto).
      unfold share; rewrite <- data_at_offset_zero, Heq; auto.
    - erewrite <- data_at_shares_join' with (sh := Tsh) by (try eapply list_join_minus; eauto).
      unfold_data_at 4%nat.
      rewrite field_at_data_at'; simpl.
      rewrite <- data_at_offset_zero, prop_true_andp by auto.
      unfold share; rewrite Heq, sepcon_comm; apply wand_frame.
    - intro; rewrite in_map_iff.
      intros ((good, ?) & ? & Hi); rewrite filter_In in Hi.
      destruct Hi as (Hi & ?); simpl in *; subst; destruct good; try discriminate.
      eapply In_Znth in Hi.
      destruct Hi as (? & Hrange & Hi).
      assert (Zlength lgood = Zlength (upto 3)) by auto.
      rewrite Zlength_combine, Z.min_r, Zlength_upto in Hrange by omega.
      rewrite Znth_combine with (a := false)(b1 := 3) in Hi by auto; inversion Hi as [Hbad].
      rewrite Znth_upto in * by omega; subst.
      rewrite !Hbad.
      unfold comm_inv.
      rewrite <- exp_sepcon1.
      rewrite sepcon_comm, (sepcon_comm _ (fold_right _ _ _)).
      rewrite extract_nth_sepcon with (i := b) by (rewrite Zlength_map; omega).
      erewrite Znth_map by omega.
      rewrite 2sepcon_assoc; f_equal; [|reflexivity].
      f_equal; extensionality.
      unfold_data_at 1%nat.
      rewrite field_at_data_at'; simpl.
      rewrite <- data_at_offset_zero, prop_true_andp by eauto; auto. }
  forward_call (writing, last_given, last_taken, comm, comms, bufs, lgood, b, b0, lasts,
    sh1, lsh, shs, g, g0, g1, g2, h, sh0).
  { unfold comm_loc; rewrite !sepcon_map; cancel.
    rewrite sepcon_filter_combine with (l := upto (Z.to_nat N))(l' := lgood) by auto; cancel.
    rewrite sepcon_assoc, (sepcon_comm (data_at sh1 _ _ _)), <- sepcon_assoc.
    apply sepcon_derives; [|cancel_frame].
    rewrite replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength; auto.
    rewrite Zlength_map; intros.
    destruct (eq_dec i b); [|rewrite upd_Znth_diff'; auto].
    subst; rewrite upd_Znth_same by auto.
    erewrite Znth_map, Znth_upto by (auto; simpl; unfold B, N in *; omega).
    if_tac; [contradiction|].
    rewrite make_shares_out by (auto; omega).
    Exists shg (Int.repr v); entailer!. }
  { repeat (split; auto). }
  Intros x; destruct x as (lasts', h').
  rewrite sepcon_map; Intros.
  forward.
  unfold loop2_ret_assert; Exists (v + 1) b lasts' h'; rewrite sepcon_map; entailer!.
  replace N with (Zlength h) by auto; symmetry; eapply mem_lemmas.Forall2_Zlength; eauto.
Qed.

Lemma comm_loc_share_join : forall good lsh1 lsh2 lsh comm g g0 g1 g2 bufs sh gsh h1 h2 h
  (Hsh : sepalg.join lsh1 lsh2 lsh) (Hh : Permutation.Permutation (h1 ++ h2) h)
  (Hsh1 : lsh1 <> Share.bot) (Hsh2 : lsh2 <> Share.bot) (Hdisj : disjoint h1 h2),
  comm_loc good lsh1 comm g g0 g1 g2 bufs sh gsh h1 *
  comm_loc good lsh2 comm g g0 g1 g2 bufs sh gsh h2 =
  comm_loc good lsh comm g g0 g1 g2 bufs sh gsh h.
Proof.
  intros; unfold comm_loc.
  rewrite !sepcon_assoc, (sepcon_comm _ (invariant _ * _)).
  rewrite <- !sepcon_assoc, <- invariant_duplicable.
  erewrite sepcon_assoc, (sepcon_comm (ghost_hist _ _ _)), ghost_hist_join by eauto.
  rewrite prop_true_andp; auto.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  exploit (split_shares (Z.to_nat N) Tsh); auto; intros (sh0 & shs & ? & ? & ? & Hshs).
  rewrite Z2Nat.id in H by (unfold N; omega).
  (* decide here which are good *)
  destruct (eq_dec shs nil).
  { subst; unfold N in *; rewrite Zlength_nil in *; omega. }
  destruct (exists_last n) as (shs' & sh2 & ?); subst.
  destruct (sepalg_list.list_join_unapp Hshs) as (shg & ? & ?).
  set (shs := shs' ++ [sh2]) in *.
  assert (shs' = map snd (filter fst (combine [true; true; false] shs))) as Hshg.
  { simpl.
    destruct shs eqn: Hshs'; [contradiction | simpl].
    unfold N in *; rewrite Zlength_cons in *; destruct l; [rewrite Zlength_nil in *; omega | simpl].
    rewrite Zlength_cons in *; destruct l; [rewrite Zlength_nil in *; omega | simpl].
    rewrite Zlength_cons in *; destruct l; [|rewrite Zlength_cons in *; pose proof (Zlength_nonneg l); omega].
    subst shs.
    destruct shs'; [discriminate | inv Hshs'].
    destruct shs'; [discriminate | match goal with H : _ = _ |- _ => inv H end].
    destruct shs'; match goal with H : _ ++ _ = _ |- _ => inv H; auto end.
    destruct shs'; discriminate. }
  rewrite Hshg in *.
  set (lgood := [true; true; false]) in *.
  forward_call (lgood, v_comm, v_bufs, v_reading, v_last_read, sh0, shs, shg).
  { unfold B, N, tbuffer, _buffer; simpl; cancel. }
  Intros x; destruct x as (((((((comms, bufs), reads), lasts), g), g0), g1), g2); simpl fst in *; simpl snd in *.
  assert_PROP (Zlength comms = N) by entailer!.
  get_global_function'' _writer; Intros.
  apply extract_exists_pre; intros writer_.
  exploit (split_shares (Z.to_nat N) Ews); auto; intros (sh1 & shs1 & ? & ? & ? & ?).
  assert_PROP (Zlength bufs = B) by entailer!.
  forward_spawn (list bool * val * val * val * val * val * list val * list val * share * share *
                      share * list share * share * list val * list val * list val * list val)%type
    (writer_, vint 0, fun x : (list bool * val * val * val * val * val * list val * list val * share * share *
                      share * list share * share * list val * list val * list val * list val) =>
      let '(lgood, v_writing, v_last_given, v_last_taken, v_comm, v_bufs, comms, bufs, sh1, lsh, sh0, shs, shg,
            g, g0, g1, g2) := x in
      [(_writing, v_writing); (_last_given, v_last_given); (_last_taken, v_last_taken); (_comm, v_comm); (_bufs, v_bufs)],
    (lgood, v_writing, v_last_given, v_last_taken, v_comm, v_bufs, comms, bufs, sh1, gsh1, sh0, shs, shg,
                       g, g0, g1, g2),
    fun (x : (list bool * val * val * val * val * val * list val * list val * share * share *
                      share * list share * share * list val * list val * list val * list val)%type)
        (arg : val) =>
    let '(lgood, v_writing, v_last_given, v_last_taken, v_comm, v_bufs, comms, bufs, sh1, lsh, sh0, shs, shg,
          g, g0, g1, g2) := x in
      fold_right sepcon emp [!!(fold_right and True [Zlength lgood = N; Zlength shs = N;
        readable_share sh1; readable_share lsh; readable_share sh0;
        Forall readable_share shs; sepalg_list.list_join sh0 shs Tsh;
        sepalg_list.list_join sh0 (map snd (filter fst (combine lgood shs))) shg;
        Zlength g1 = N; Zlength g2 = N; Forall isptr comms]) && emp;
        data_at_ Ews tint v_writing; data_at_ Ews tint v_last_given; data_at_ Ews (tarray tint N) v_last_taken;
        data_at sh1 (tarray (tptr tint) N) comms v_comm; data_at sh1 (tarray (tptr tbuffer) B) bufs v_bufs;
        fold_right sepcon emp (map (fun r => comm_loc (Znth r lgood false) lsh (Znth r comms Vundef)
          (Znth r g Vundef) (Znth r g0 Vundef) (Znth r g1 Vundef) (Znth r g2 Vundef) bufs
          (Znth r shs Tsh) gsh2 []) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2);
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i 0 then sh = sh0 else if eq_dec i 1 then sh = sh0 else sh = shg) &&
          EX v : _, data_at sh tbuffer (Vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B)))]).
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
    erewrite map_ext by (intro; erewrite <- comm_loc_share_join with (h1 := [])(h2 := []); eauto; reflexivity).
    rewrite !sepcon_map.
    do 2 (erewrite <- (data_at_shares_join Ews); eauto).
    rewrite (extract_nth_sepcon (map (data_at _ _ _) (sublist 1 _ bufs)) 0), Znth_map with (d' := Vundef);
      rewrite ?Zlength_map, ?Zlength_sublist; try (unfold B, N in *; omega).
    erewrite <- (data_at_shares_join shg) by eauto.
    rewrite (sepcon_comm (data_at sh0 _ _ (Znth 0  (sublist _ _ bufs) Vundef))),
      (sepcon_assoc _ (data_at sh0 _ _ _)).
    rewrite replace_nth_sepcon.
    fast_cancel.
    rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at sh0 _ _ _)).
    rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right sepcon emp (upd_Znth 0 _ _))), !sepcon_assoc.
    rewrite <- sepcon_assoc; apply sepcon_derives; [|cancel_frame].
    assert (Zlength (data_at sh0 tbuffer (vint 0) (Znth 0 bufs Vundef)
         :: upd_Znth 0 (map (data_at shg tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs))
              (data_at sh0 tbuffer (vint 0) (Znth 0 (sublist 1 (Zlength bufs) bufs) Vundef))) = B) as Hlen.
    { rewrite Zlength_cons, upd_Znth_Zlength; rewrite Zlength_map, Zlength_sublist, ?Zlength_upto;
        simpl; unfold B, N in *; omega. }
    rewrite sepcon_comm; apply sepcon_list_derives with (l1 := _ :: _).
    { rewrite Zlength_map; auto. }
    intros; rewrite Hlen in *.
    erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; simpl; try (unfold B, N in *; omega).
    destruct (eq_dec i 0); [|destruct (eq_dec i 1)].
    - subst i; rewrite Znth_0_cons.
      Exists sh0 Int.zero; entailer!.
    - subst i; rewrite Znth_pos_cons, Zminus_diag, upd_Znth_same; rewrite ?Zlength_map, ?Zlength_sublist; try omega.
      rewrite Znth_sublist; try omega.
      Exists sh0 Int.zero; entailer!.
    - rewrite Znth_pos_cons, upd_Znth_diff; rewrite ?Zlength_map, ?Zlength_sublist; try omega.
      erewrite Znth_map; [|rewrite Zlength_sublist; omega].
      rewrite Znth_sublist; try omega.
      rewrite Z.sub_simpl_r.
      Exists shg Int.zero; entailer!. }
  rewrite Znth_sublist; try (unfold B, N in *; omega).
  rewrite <- seq_assoc.
  assert_PROP (Zlength reads = N) by entailer!.
  assert_PROP (Zlength lasts = N) by entailer!.
  assert (Zlength lgood = N) by auto.
  clearbody lgood.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (gvar _last_given v_last_given; gvar _writing v_writing; gvar _last_taken v_last_taken;
          gvar _last_read v_last_read; gvar _reading v_reading; gvar _comm v_comm; gvar _bufs v_bufs)
   SEP (EX sh' : share, !!(sepalg_list.list_join sh1 (sublist i N shs1) sh') &&
          data_at sh' (tarray (tptr tint) N) lasts v_last_read * data_at sh' (tarray (tptr tint) N) reads v_reading;
        fold_right sepcon emp (map (fun sh => data_at sh (tarray (tptr tint) N) comms v_comm) (sublist i N shs1));
        fold_right sepcon emp (map (fun sh => data_at sh (tarray (tptr tbuffer) B) bufs v_bufs) (sublist i N shs1));
        fold_right sepcon emp (map (fun x => comm_loc (Znth x lgood false) gsh2 (Znth x comms Vundef)
          (Znth x g Vundef) (Znth x g0 Vundef) (Znth x g1 Vundef) (Znth x g2 Vundef) bufs (Znth x shs Tsh) gsh2
          []) (sublist i N (upto (Z.to_nat N))));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) (sublist i N g0));
        fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i N reads));
        fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i N lasts));
        fold_right sepcon emp (map (malloc_token Tsh 4) comms);
        fold_right sepcon emp (map (malloc_token Tsh 4) bufs);
        fold_right sepcon emp (map (malloc_token Tsh 4) reads);
        fold_right sepcon emp (map (malloc_token Tsh 4) lasts);
        fold_right sepcon emp (map (fun sh => @data_at CompSpecs sh tbuffer (vint 0) (Znth 1 bufs Vundef))
          (map snd (filter fst (sublist i N (combine lgood shs))))))).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists Ews; rewrite !sublist_same by (auto; rewrite Zlength_combine, Z.min_l; auto; omega).
    entailer!. }
  { Intros sh'.
    forward_malloc tint d.
    forward.
    get_global_function'' _reader; Intros.
    apply extract_exists_pre; intros reader_.
    rewrite Z2Nat.id in * by omega.
    match goal with H : sepalg_list.list_join sh1 _ sh' |- _ =>
      rewrite sublist_next with (d0 := Tsh) in H by (auto; omega); inversion H as [|????? Hj1 Hj2] end.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh1' & ? & Hj').
    forward_spawn (Z * bool * val * val * val * val * list val * list val * list val * list val *
                      share * share * share * val * val * val * val)%type
      (reader_, d, fun x : (Z * bool * val * val * val * val * list val * list val * list val * list val *
                      share * share * share * val * val * val * val) =>
        let '(r, good, v_reading, v_last_read, v_comm, v_bufs, reads, lasts, comms, bufs, sh1, sh2, sh,
              g, g0, g1, g2) := x in
        [(_reading, v_reading); (_last_read, v_last_read); (_comm, v_comm); (_bufs, v_bufs)],
      (i, Znth i lgood false, v_reading, v_last_read, v_comm, v_bufs, reads, lasts, comms, bufs,
                    Znth i shs1 Tsh, gsh2, Znth i shs Tsh, Znth i g Vundef, Znth i g0 Vundef, Znth i g1 Vundef,
                    Znth i g2 Vundef),
      fun (x : (Z * bool * val * val * val * val * list val * list val * list val * list val *
                      share * share * share * val * val * val * val)%type) (arg : val) =>
        let '(r, good, v_reading, v_last_read, v_comm, v_bufs, reads, lasts, comms, bufs, sh1, sh2, sh,
              g, g0, g1, g2) := x in
        fold_right sepcon emp [!!(fold_right and True [readable_share sh; readable_share sh1;
          readable_share sh2; isptr (Znth r comms Vundef); Forall isptr bufs]) && emp;
          data_at Tsh tint (vint r) arg; malloc_token Tsh (sizeof tint) arg;
          data_at sh1 (tarray (tptr tint) N) reads v_reading; data_at sh1 (tarray (tptr tint) N) lasts v_last_read;
          data_at sh1 (tarray (tptr tint) N) comms v_comm;
          data_at_ Tsh tint (Znth r reads Vundef); data_at_ Tsh tint (Znth r lasts Vundef);
          data_at sh1 (tarray (tptr tbuffer) B) bufs v_bufs;
          comm_loc good sh2 (Znth r comms Vundef) g g0 g1 g2 bufs sh gsh2 [];
          if good then EX v : _, data_at sh tbuffer (Vint v) (Znth 1 bufs Vundef) else emp;
          ghost_var gsh1 (vint 1) g0]).
    - apply andp_right.
      { entailer!. }
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
      rewrite sublist_next with (d0 := Tsh) by (auto; omega).
      rewrite sublist_next with (d0 := (false, Tsh)) by (auto; rewrite Zlength_combine, Z.min_l; omega).
      rewrite !sublist_next with (i0 := i)(d0 := Vundef) by (auto; omega).
      rewrite sublist_next with (d0 := N); simpl; rewrite ?Znth_upto; auto; rewrite ?Zlength_upto;
        simpl; try (unfold N in *; omega).
      fast_cancel.
      rewrite Znth_combine by omega.
      destruct (Znth i lgood false); simpl.
      + Exists Int.zero; cancel.
      + subst Frame; simpl; cancel.
    - Exists sh1'; entailer!. }
  eapply semax_seq'; [|apply semax_ff].
  eapply semax_loop; [|forward; apply ENTAIL_refl].
  forward.
  entailer!.
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
assert (forall m0 l m2 gx ret, step_lemmas.has_opttyp ret (opttyp_of_type tint) ->
 EX x : Z, (PROP (repable_signed x) LOCAL (temp ret_temp (vint x))
   SEP (fold_right sepcon emp (map (fun p : Z => invariant (m0 p)) l); m2 x)) 
  (make_ext_rval gx ret) |-- !! is_int I32 Signed (force_val ret)).
{ intros; unfold PROPx, LOCALx, local, lift1, liftx; simpl; unfold liftx, lift; simpl.
  Intros x; apply prop_right.
  unfold make_ext_rval, eval_id in *; simpl in *.
  destruct ret; auto; simpl in *.
  subst; auto. }
repeat semax_func_cons_ext.
{ simpl; auto. }
{ simpl; auto. }
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
