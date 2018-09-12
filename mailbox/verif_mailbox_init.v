Require Import mailbox.verif_atomic_exchange.
Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.

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
   SEP (malloc_token Tsh t p * data_at_ Ews t p)).
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
  pose proof (sizeof_pos t).
  assert_PROP (sizeof t <= Int.max_unsigned).
  { entailer!.
    destruct H2 as [? [_ [? _]]].
    destruct p; inv H2.
    simpl in H3.
    pose proof Ptrofs.unsigned_range i.
    rep_omega.
  }
  assert_PROP (Int.repr (Int.unsigned (Int.divu (Int.repr (4 * n)) (Int.repr 4))) = Int.repr n) as H4.
  { entailer!. 
    rewrite Int.repr_unsigned.
    unfold Int.divu.
    rewrite (Int.unsigned_repr 4) by rep_omega.
    rewrite (Int.unsigned_repr (4 * n)) by rep_omega.
    rewrite Z.mul_comm, Z_div_mult by omega.
    auto. }
  forward_for_simple_bound n (EX i : Z, PROP ()
    LOCAL (temp _p p; temp _s p; temp _c (vint c); temp _n (vint (4 * n)))
    SEP (data_at sh (tarray tint n) (repeat (vint c) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (n - i))) p)).
  { rewrite H4; auto. }
  { entailer!.
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
        inv H10.
        apply Z.divide_add_r; auto.
        apply Z.divide_mul_l.
        exists 1; auto.
    - rewrite data_at__eq.
      unfold default_val, reptype_gen; simpl.
      rewrite repeat_list_repeat, Z.sub_0_r; apply derives_refl. }
  - forward.
    rewrite upd_init_const; [|omega].
    entailer!.
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
    LOCAL (gvars gv)
    SEP (data_at_ Ews (tarray (tptr tint) N) (gv _comm); data_at_ Ews (tarray (tptr tlock) N) (gv _lock);
         data_at_ Ews (tarray (tptr tint) N) (gv _reading); data_at_ Ews (tarray (tptr tint) N) (gv _last_read);
         EX bufs : list val, !!(Zlength bufs = i /\ Forall isptr bufs) &&
           data_at Ews (tarray (tptr tbuffer) B) (bufs ++ repeat Vundef (Z.to_nat (B - i))) (gv _bufs) *
           fold_right sepcon emp (map (@data_at CompSpecs Ews tbuffer (vint 0)) bufs) *
           fold_right sepcon emp (map (malloc_token Tsh tbuffer) bufs))).
  { unfold B, N; computable. }
  { unfold B, N; computable. }
  { entailer!.
    Exists ([] : list val); simpl; entailer!. }
  { forward_call tbuffer.
    { split3; simpl; auto; computable. }
    Intros b bufs.
    assert_PROP (field_compatible tint [] b) by entailer!.
    forward_call (Ews, tbuffer, b, 0, 1).
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
      auto. }
      apply derives_refl. }
  Intros bufs; rewrite Zminus_diag, app_nil_r.
  forward_for_simple_bound N (EX i : Z, PROP ()
    LOCAL (gvars gv)
    SEP (EX locks : list val, EX comms : list val, EX g : list gname, EX g0 : list gname, EX g1 : list gname,
         EX g2 : list gname, !!(Zlength locks = i /\ Zlength comms = i /\ Forall isptr comms /\ Zlength g = i /\
           Zlength g0 = i /\ Zlength g1 = i /\ Zlength g2 = i) &&
          (data_at Ews (tarray (tptr tlock) N) (locks ++ repeat Vundef (Z.to_nat (N - i))) (gv _lock) *
           data_at Ews (tarray (tptr tint) N) (comms ++ repeat Vundef (Z.to_nat (N - i))) (gv _comm) *
           fold_right sepcon emp (map (fun r => comm_loc Ews (Znth r locks) (Znth r comms)
             (Znth r g) (Znth r g0) (Znth r g1) (Znth r g2) bufs
             (Znth r shs) gsh2 empty_map) (upto (Z.to_nat i))) *
           fold_right sepcon emp (map (ghost_hist(hist_el := AE_hist_el) Ish empty_map) g) *
           fold_right sepcon emp (map (malloc_token Tsh tlock) locks)) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g0) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2) *
           fold_right sepcon emp (map (malloc_token Tsh tint) comms);
         EX reads : list val, !!(Zlength reads = i) &&
           data_at Ews (tarray (tptr tint) N) (reads ++ repeat Vundef (Z.to_nat (N - i))) (gv _reading) *
           fold_right sepcon emp (map (data_at_ Ews tint) reads) *
           fold_right sepcon emp (map (malloc_token Tsh tint) reads);
         EX lasts : list val, !!(Zlength lasts = i) &&
           data_at Ews (tarray (tptr tint) N) (lasts ++ repeat Vundef (Z.to_nat (N - i))) (gv _last_read) *
           fold_right sepcon emp (map (data_at_ Ews tint) lasts) *
           fold_right sepcon emp (map (malloc_token Tsh tint) lasts);
         @data_at CompSpecs Ews (tarray (tptr tbuffer) B) bufs (gv _bufs);
         EX sh : share, !!(sepalg_list.list_join sh1 (sublist i N shs) sh) &&
           @data_at CompSpecs sh tbuffer (vint 0) (Znth 0 bufs);
         fold_right sepcon emp (map (@data_at CompSpecs Ews tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs));
         fold_right sepcon emp (map (malloc_token Tsh tbuffer) bufs))).
  { unfold N; computable. }
  { Exists ([] : list val) ([] : list val) ([] : list gname) ([] : list gname) ([] : list gname)
      ([] : list gname) ([] : list val) ([] : list val) Ews; rewrite !data_at__eq; entailer!.
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
    ghost_alloc (ghost_var Tsh (vint 1)).
    ghost_alloc (ghost_var Tsh (vint 0)).
    ghost_alloc (ghost_var Tsh (vint 1)).
    ghost_alloc (ghost_hist_ref(hist_el := AE_hist_el) Tsh empty_map empty_map).
    { apply ghost_hist_init. }
    Intros g' g0' g1' g2'.
    forward_call (l, Ews, AE_inv c g' (vint 0) (comm_R bufs (Znth i shs) gsh2 g0' g1' g2')).
    rewrite <- hist_ref_join_nil by apply Share.nontrivial; Intros.
    replace_SEP 1 (ghost_hist(hist_el := AE_hist_el) Ews empty_map g' * ghost_hist(hist_el := AE_hist_el) Ish empty_map g').
    { go_lower.
      erewrite ghost_hist_join, map_add_empty; try apply Ews_Ish_join; auto.
      entailer!.
      { intro X; contradiction unreadable_bot.
        rewrite <- X; auto. } }
    fold (ghost_var Tsh (vint 1) g0') (ghost_var Tsh (vint 0) g1') (ghost_var Tsh (vint 1) g2').
    erewrite <- !ghost_var_share_join with (sh0 := Tsh) by eauto.
    match goal with H : sepalg_list.list_join sh1 (sublist i N shs) sh |- _ =>
      erewrite sublist_next in H; try omega; inversion H as [|????? Hj1 Hj2] end.
    apply sepalg.join_comm in Hj1; eapply sepalg_list.list_join_assoc1 in Hj2; eauto.
    destruct Hj2 as (sh' & ? & Hsh').
    erewrite <- data_at_share_join with (sh0 := sh) by (apply Hsh').
    forward_call (l, Ews, AE_inv c g' (vint 0) (comm_R bufs (Znth i shs) gsh2 g0' g1' g2')).
(*    { entailer!. }
    { entailer!. }
*)
    { lock_props.
      fast_cancel.
      unfold AE_inv.
      Exists (@nil AE_hist_el) (vint 0).
      unfold comm_R at 1.
      Exists 0 1 1; unfold last_two_reads, last_write, prev_taken; simpl.
      rewrite !sepcon_andp_prop', !sepcon_andp_prop, !sepcon_andp_prop'; apply andp_right;
        [apply prop_right; auto|].
      apply andp_right; [apply prop_right; repeat (split; auto); computable|].
      change_compspecs CompSpecs.
      Exists 0; fast_cancel. }
    Exists (locks ++ [l]) (comms ++ [c]) (g ++ [g']) (g0 ++ [g0']) (g1 ++ [g1']) (g2 ++ [g2'])
      (reads ++ [rr]) (lasts ++ [ll]) sh'; rewrite !upd_init; try omega.
    rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; rewrite <- !app_assoc.
    go_lower.
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
    erewrite map_ext_in; [unfold comm_loc, AE_loc, AE_inv; cancel|].
    { apply derives_refl. }
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
  cancel.
Qed.
