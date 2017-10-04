Require Import VST.progs.conclib.
Require Import VST.progs.conc_queue.
Require Import VST.progs.conc_queue_specs.
Require Import VST.floyd.library.

Set Bullet Behavior "Strict Subproofs".

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition makecond_spec := DECLARE _makecond (makecond_spec _).
Definition freecond_spec := DECLARE _freecond (freecond_spec _).
Definition wait_spec := DECLARE _waitcond (wait2_spec _).
Definition signal_spec := DECLARE _signalcond (signal_spec _).

Definition surely_malloc_spec := DECLARE _surely_malloc surely_malloc_spec'.
Definition q_new_spec := DECLARE _q_new q_new_spec'.
Definition q_del_spec := DECLARE _q_del q_del_spec'.
Definition q_add_spec := DECLARE _q_add q_add_spec'.
Definition q_remove_spec := DECLARE _q_remove q_remove_spec'.
Definition q_tryremove_spec := DECLARE _q_tryremove q_tryremove_spec'.

Definition Gprog : funspecs := ltac:(with_library prog
  [surely_malloc_spec; acquire_spec; release_spec; makelock_spec; freelock_spec;
   makecond_spec; freecond_spec; wait_spec; signal_spec;
   q_new_spec; q_del_spec; q_add_spec; q_remove_spec; q_tryremove_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  unfold surely_malloc_spec, surely_malloc_spec'; start_function.
  forward_call (* p = malloc(n); *)
     n.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh n p * memory_block Tsh n p)).
*
  if_tac.
    subst p. entailer!.
    entailer!.
*
    forward_call tt.
    contradiction.
*
    if_tac.
    + forward. subst p. inv H0.
    + Intros. forward. entailer!.
*
  forward. Exists p; entailer!.
Qed.

Lemma body_q_new : semax_body Vprog Gprog f_q_new q_new_spec.
Proof.
  unfold q_new_spec, q_new_spec'; start_function.
  forward_call (sizeof tqueue_t).
  { simpl; computable. }
  Intros p.
  assert (alignof tqueue_t | natural_alignment).
  { simpl; unfold align_attr; simpl.
    exists 2; auto. }
  rewrite malloc_compat; auto; Intros.
  rewrite memory_block_data_at_; auto.
  forward.
  Intros.
  assert (field_compatible tqueue [] p /\ field_compatible (tptr tlock) [] (offset_val 60 p)) as (? & ?).
  { unfold field_compatible in *; repeat match goal with H : _ /\ _ |- _ => destruct H end.
    destruct p as [| | | | | b o]; try contradiction.
    assert (Int.unsigned (Int.add o (Int.repr 60)) = Int.unsigned o + 60) as Ho.
    { rewrite Int.unsigned_add_carry.
      unfold Int.add_carry.
      rewrite Int.unsigned_repr, Int.unsigned_zero; [|computable].
      destruct (zlt _ Int.modulus); simpl in *; omega. }
    repeat split; auto; simpl in *; try omega.
    rewrite Ho; unfold align_attr in *; simpl in *.
    apply Z.divide_add_r; auto.
    exists 15; auto. }
  forward_for_simple_bound MAX (EX i : Z, PROP () LOCAL (temp _q p; temp _newq p)
    SEP (malloc_token Tsh (sizeof tqueue_t) p;
         @data_at CompSpecs Tsh tqueue (repeat (vint 0) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (MAX - i)),
           (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))) p;
         @data_at_ CompSpecs Tsh (tptr tlock) (offset_val 60 p))).
  { unfold MAX; computable. }
  { unfold MAX; computable. }
  { entailer!.
    unfold data_at_, field_at_; unfold_field_at 1%nat.
    unfold data_at, field_at, at_offset; simpl; entailer. }
  { forward.
    go_lower.
    apply andp_right; [apply prop_right; split; auto; omega|].
    apply andp_right; [apply prop_right; auto|].
    cancel.
    rewrite upd_Znth_app2; repeat rewrite Zlength_repeat; repeat rewrite Z2Nat.id; try omega.
    rewrite Zminus_diag, upd_Znth0, sublist_repeat; try rewrite Zlength_repeat, Z2Nat.id; try omega.
    rewrite Z2Nat.inj_add, repeat_plus; try omega; simpl.
    rewrite <- app_assoc; replace (MAX - i - 1) with (MAX - (i + 1)) by omega; cancel. }
  rewrite Zminus_diag, app_nil_r.
  forward.
  forward.
  forward.
  forward_call (sizeof tint).
  { simpl; computable. }
  Intros addc.
  rewrite malloc_compat with (p0 := addc); auto; Intros.
  rewrite memory_block_data_at_; auto.
  forward_call (addc, Tsh).
  { unfold tcond; cancel. }
  forward.
  forward_call (sizeof tint).
  { simpl; computable. }
  Intros remc.
  rewrite malloc_compat with (p0 := remc); auto; Intros.
  rewrite memory_block_data_at_; auto.
  forward_call (remc, Tsh).
  { unfold tcond; cancel. }
  forward.
  forward_call (sizeof tlock).
  { admit. } (* lock size broken *)
  { simpl; computable. }
  Intros lock.
  rewrite malloc_compat with (p0 := lock); auto; Intros.
  rewrite memory_block_data_at_; auto.
  destruct Q as (t, P).
  forward_call (lock, Tsh, q_lock_pred t P p lock gsh2).
  gather_SEP 7 8; replace_SEP 0 (data_at Tsh tqueue_t (repeat (vint 0) (Z.to_nat MAX),
           (vint 0, (vint 0, (vint 0, (addc, remc)))), Vundef) p).
  { go_lowerx.
    unfold_data_at 1%nat.
    unfold data_at_, field_at_, field_at, at_offset; simpl.
    rewrite !sem_cast_neutral_ptr; auto.
    rewrite !field_compatible_cons; simpl; Intros.
    apply andp_right; [apply prop_right; unfold in_members; simpl; split; [|split; [|split]]; auto|].
    rewrite sepcon_emp, !isptr_offset_val_zero; auto. }
  apply new_ghost with (t' := reptype t).
  forward.
  forward_call (lock, Tsh, q_lock_pred t P p lock gsh2).
  { lock_props.
    unfold q_lock_pred, q_lock_pred'; simpl.
    Exists ([] : list (val * reptype t)) 0 addc remc ([] : hist (reptype t)).
    rewrite Zlength_nil; simpl; cancel.
    rewrite sepcon_andp_prop'.
    apply andp_right; [apply prop_right|].
    { repeat split; auto; unfold MAX; try omega; try computable. }
    cancel.
    subst Frame; instantiate (1 := [field_at Tsh tqueue_t [StructField _lock] lock p; ghost gsh1 (Tsh, []) p]);
      simpl.
    unfold_field_at 1%nat.
    erewrite <- ghost_share_join with (h1 := []); eauto.
    simpl; cancel.
    rewrite (sepcon_comm _ (@ghost _ (reptype t) _ _)), !sepcon_assoc; apply sepcon_derives; auto.
    unfold data_at, field_at; simpl.
    rewrite !field_compatible_cons; simpl; Intros.
    apply andp_right; [apply prop_right; unfold in_members; simpl; split; [|split]; auto|].
    rewrite sem_cast_neutral_ptr; auto. }
  forward.
  Exists p lock.
  unfold lqueue; simpl; entailer!; auto.
Admitted.

Lemma body_q_del : semax_body Vprog Gprog f_q_del q_del_spec.
Proof.
  unfold q_del_spec, q_del_spec'; start_function.
  destruct Q as (t, (P, h)).
  unfold lqueue; rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (lock, Tsh, q_lock_pred t P p lock gsh2).
  forward_call (lock, Tsh, q_lock_pred t P p lock gsh2).
  { lock_props. }
  unfold q_lock_pred, q_lock_pred'; Intros vals head addc remc h'.
  forward_call (lock, sizeof tlock).
  { simpl; cancel.
    rewrite !sepcon_assoc; apply sepcon_derives; [apply data_at__memory_block_cancel | cancel]. }
  forward.
  rewrite data_at_isptr, (cond_var_isptr _ addc), (cond_var_isptr _ remc); Intros.
  rewrite isptr_offset_val_zero; auto.
  forward.
  forward_call (addc, Tsh).
  forward_call (addc, sizeof tcond).
  { simpl; cancel.
    rewrite !sepcon_assoc; apply sepcon_derives; [apply data_at__memory_block_cancel | cancel]. }
  forward.
  forward_call (remc, Tsh).
  forward_call (remc, sizeof tcond).
  { simpl; cancel.
    repeat rewrite sepcon_assoc; apply sepcon_derives; [apply data_at__memory_block_cancel | cancel]. }
  gather_SEP 2 5; rewrite sepcon_comm.
  replace_SEP 0 (!!(h' = h) && ghost Tsh (Tsh, h) p).
  { go_lower.
    eapply derives_trans; [apply prop_and_same_derives, ghost_inj_Tsh|].
    Intros; subst.
    rewrite ghost_share_join; auto; entailer!. }
  Intros; subst.
  exploit (consistent_inj h [] [] vals); auto; intro; subst; simpl.
  rewrite Zlength_nil.
  gather_SEP 1 4; replace_SEP 0 (data_at Tsh tqueue_t (rotate (complete MAX []) head MAX,
     (vint 0, (vint head, (vint ((head + 0) mod MAX), (addc, remc)))), lock) p).
  { unfold_data_at 2%nat; entailer!.
    unfold data_at, field_at; Intros; simpl.
    apply andp_right; [|simple apply derives_refl].
    rewrite field_compatible_cons; unfold in_members; simpl; entailer!. }
  forward_call (p, sizeof tqueue_t).
  { rewrite (sepcon_comm (malloc_token _ _ _)).
    rewrite !sepcon_assoc; apply sepcon_derives; [apply data_at_memory_block | simpl; cancel]. }
  forward.
  (* Do we want to deallocate the ghost? *)
Admitted.

Lemma body_q_add : semax_body Vprog Gprog f_q_add q_add_spec.
Proof.
  unfold q_add_spec, q_add_spec'.
  start_function.
  destruct Q as (t, ((P, h), v)).
  unfold lqueue; rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (lock, sh, q_lock_pred t P p lock gsh2).
  unfold q_lock_pred at 2; unfold q_lock_pred'; Intros vals head addc remc h'.
  forward.
  rewrite data_at_isptr; Intros; rewrite isptr_offset_val_zero; auto.
  forward.
  forward_while (EX vals : _, EX head : Z, EX addc : val, EX remc : val, EX h' : hist (reptype t),
   PROP ()
   LOCAL (temp _len (vint (Zlength vals)); temp _q p; temp _l lock; temp _tgt p; temp _r e)
   SEP (lock_inv sh lock (q_lock_pred t P p lock gsh2);
        q_lock_pred' t P p vals head addc remc lock gsh2 h';
        @field_at CompSpecs sh tqueue_t [StructField _lock] lock p;
        @data_at CompSpecs Tsh t v e; malloc_token Tsh (sizeof t) e; ghost gsh1 (sh, h) p)).
  { Exists vals head addc remc h'.
    unfold q_lock_pred'; entailer!.
    apply derives_refl. }
  { go_lower; entailer'. }
  { unfold q_lock_pred'; Intros.
    forward.
    { go_lower.
      rewrite cond_var_isptr; Intros; entailer'. }
    forward_call (addc0, lock, Tsh, sh, q_lock_pred t P p lock gsh2).
    { unfold q_lock_pred; unfold q_lock_pred'; simpl.
      Exists vals0 head0 addc0 remc0 h'0.
      subst Frame; instantiate (1 := [field_at sh tqueue_t [StructField _lock] lock p;
        data_at Tsh t v e; malloc_token Tsh (sizeof t) e; ghost gsh1 (sh, h) p]); simpl.
      repeat rewrite sepcon_assoc; repeat (apply sepcon_derives; [apply derives_refl|]).
      entailer!.
      apply andp_right; cancel. }
    unfold q_lock_pred at 2; unfold q_lock_pred'; Intros vals1 head1 addc1 remc1 h'1.
    forward.
    Exists (vals1, head1, addc1, remc1, h'1).
    unfold q_lock_pred'; entailer!. }
  unfold q_lock_pred'; Intros.
  rewrite Int.signed_repr, Zlength_correct in HRE.
  freeze [0; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13] FR; forward.
  exploit (Z_mod_lt (head0 + Zlength vals0) MAX); [omega | intro].
  forward.
  forward.
  { go_lower.
    repeat apply andp_right; apply prop_right; auto.
    rewrite andb_false_intro2; simpl; auto. }
  forward.
  thaw FR.
  rewrite (cond_var_isptr _ remc0); Intros.
  forward.
  freeze [0; 1; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13] FR; forward_call (remc0, Tsh).
  thaw FR.
  rewrite upd_rotate; auto; try rewrite Zlength_complete; try rewrite Zlength_map; auto.
  rewrite Zminus_mod_idemp_l, Z.add_simpl_l, (Zmod_small (Zlength vals0));
    [|rewrite Zlength_correct; unfold MAX; omega].
  erewrite <- Zlength_map, upd_complete; [|rewrite Zlength_map, Zlength_correct; auto].
  gather_SEP 7 12.
  rewrite sepcon_comm; replace_SEP 0 (!!(list_incl h h'0) && ghost Tsh (Tsh, h'0) p).
  { go_lower.
    eapply derives_trans; [apply prop_and_same_derives, ghost_inj|].
    Intros; rewrite ghost_share_join; auto; entailer!. }
  exploit (consistent_snoc_add h'0 [] vals0 e v); auto; intro.
  Intros; apply hist_add with (e0 := QAdd e v); [eauto|].
  erewrite <- ghost_share_join with (h1 := h ++ [QAdd e v])(sh := sh); try eassumption.
  time forward_call (lock, sh, q_lock_pred t P p lock gsh2). (* 37s *)
  { lock_props.
    unfold q_lock_pred, q_lock_pred'.
    Exists (vals0 ++ [(e, v)]) head0 addc0 remc0 (h'0 ++ [QAdd e v]).
    rewrite data_at_isptr; Intros.
    rewrite map_app, Zlength_app, Zlength_cons, Zlength_nil.
    unfold sem_mod; simpl sem_binarith.
    unfold both_int; simpl force_val.
    rewrite andb_false_intro2; [|simpl; auto].
    simpl force_val.
    rewrite !add_repr, mods_repr; try computable.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    simpl; apply andp_right.
    { apply prop_right; split; [rewrite Zlength_correct; unfold MAX; omega|].
      split; [omega | auto]. }
    rewrite Zplus_mod_idemp_l, Z.add_assoc, Zlength_map.
    repeat rewrite map_app; repeat rewrite sepcon_app; simpl.
    rewrite sem_cast_neutral_ptr; auto; simpl.
    rewrite sepcon_andp_prop', !sepcon_andp_prop, sepcon_andp_prop'; apply andp_right;
      [apply prop_right; auto | cancel].
    { pose proof (Z_mod_lt (head0 + Zlength vals0) MAX).
      rewrite Zlength_map; split; try omega.
      transitivity MAX; simpl in *; [omega | unfold MAX; computable]. } }
  forward.
  { unfold lqueue; simpl; entailer!; auto. }
  { apply list_incl_app; auto. }
  { pose proof Int.min_signed_neg; split; [rewrite Zlength_correct; omega|].
    transitivity MAX; [auto | unfold MAX; computable]. }
Admitted.

Lemma body_q_remove : semax_body Vprog Gprog f_q_remove q_remove_spec.
Proof.
  unfold q_remove_spec, q_remove_spec'; start_function.
  destruct Q as (t, (P, h)).
  unfold lqueue; rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (lock, sh, q_lock_pred t P p lock gsh2).
  unfold q_lock_pred at 2; unfold q_lock_pred'; Intros vals head addc remc h'.
  forward.
  rewrite data_at_isptr; Intros; rewrite isptr_offset_val_zero; auto.
  forward.
  forward_while (EX vals : list _, EX head : Z, EX addc : val, EX remc : val, EX h' : hist (reptype t), PROP ()
   LOCAL (temp _len (vint (Zlength vals)); temp _q p; temp _l lock; temp _tgt p)
   SEP (lock_inv sh lock (q_lock_pred t P p lock gsh2);
        q_lock_pred' t P p vals head addc remc lock gsh2 h';
        @field_at CompSpecs sh tqueue_t [StructField _lock] lock p; ghost gsh1 (sh, h) p)).
  { Exists vals head addc remc h'; unfold q_lock_pred'; entailer!. }
  { go_lower; entailer'. }
  { unfold q_lock_pred'; rewrite (cond_var_isptr _ remc0); Intros.
    forward.
    forward_call (remc0, lock, Tsh, sh, q_lock_pred t P p lock gsh2).
    { unfold q_lock_pred; unfold q_lock_pred'; simpl.
      Exists vals0 head0 addc0 remc0 h'0.
      subst Frame; instantiate (1 := [field_at sh tqueue_t [StructField _lock] lock p;
        ghost gsh1 (sh, h) p]); simpl.
      repeat rewrite sepcon_assoc; repeat (apply sepcon_derives; [apply derives_refl|]).
      entailer!.
      apply andp_right; [Intros; entailer! | entailer!]. }
    unfold q_lock_pred at 2; unfold q_lock_pred'; Intros vals1 head1 addc1 remc1 h'1.
    forward.
    Exists (vals1, head1, addc1, remc1, h'1).
    unfold q_lock_pred'; entailer!. }
  unfold q_lock_pred'; Intros.
  assert (Zlength vals0 > 0).
  { rewrite Zlength_correct in *.
    destruct (length vals0); [|rewrite Nat2Z.inj_succ; omega].
    contradiction HRE; auto. }
  evar (R : mpred).
  replace_SEP 9 (!!(Forall isptr (map fst vals0)) && R); subst R.
  { go_lower; apply prop_and_same_derives, all_ptrs. }
  forward.
  forward.
  { go_lower; Intros.
    rewrite Znth_head; try rewrite Zlength_map; try omega.
    repeat apply andp_right; apply prop_right; auto.
    apply Forall_Znth; [rewrite Zlength_map; omega|].
    eapply Forall_impl; [|eauto].
    destruct a; auto. }
  forward.
  forward.
  { go_lower; simpl.
    repeat apply andp_right; apply prop_right; auto.
    rewrite andb_false_intro2; simpl; auto. }
  forward.
  rewrite cond_var_isptr; Intros.
  forward.
  freeze [0; 1; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] FR; forward_call (addc0, Tsh).
  thaw FR.
  rewrite upd_rotate; try rewrite Zlength_complete; try rewrite Zlength_map; auto.
  rewrite Zminus_diag, Zmod_0_l.
  destruct vals0; [contradiction HRE; auto|].
  rewrite Zlength_cons in *.
  simpl; rewrite rotate_1; try rewrite Zlength_map; try omega.
  unfold sem_mod; simpl sem_binarith.
  unfold both_int; simpl force_val.
  rewrite andb_false_intro2; [|simpl; auto].
  simpl force_val.
  rewrite !add_repr, mods_repr; try computable.
  destruct p0 as (e, v).
  exploit (consistent_cons_rem(t := reptype t)); eauto; intro.
  gather_SEP 8 11.
  rewrite sepcon_comm; replace_SEP 0 (!!(list_incl h h'0) && ghost Tsh (Tsh, h'0) p).
  { go_lower.
    eapply derives_trans; [apply prop_and_same_derives, ghost_inj|].
    Intros; rewrite ghost_share_join; auto; entailer!. }
  Intros; apply hist_add with (e0 := QRem e v); [eauto|].
  erewrite <- ghost_share_join with (h1 := h ++ [QRem e v])(sh := sh); try eassumption; try apply list_incl_app;
    auto.
  forward_call (lock, sh, q_lock_pred t P p lock gsh2).
  { lock_props.
    unfold q_lock_pred, q_lock_pred'; Exists vals0 ((head0 + 1) mod MAX) addc0 remc0 (h'0 ++ [QRem e v]).
    unfold Z.succ; rewrite sub_repr, Z.add_simpl_r, (Z.add_comm (Zlength vals0)), Z.add_assoc,
      Zplus_mod_idemp_l.
    simpl; entailer!.
    apply Z_mod_lt; omega. }
  forward.
  Exists e v; unfold lqueue; simpl; entailer!; auto.
  rewrite Znth_head; auto; rewrite Zlength_cons, Zlength_map; omega.
  { split; try omega.
    transitivity MAX; [omega | unfold MAX; computable]. }
Qed.

Lemma body_q_tryremove : semax_body Vprog Gprog f_q_tryremove q_tryremove_spec.
Proof.
  unfold q_tryremove_spec, q_tryremove_spec'; start_function.
  destruct Q as (t, (P, h)).
  unfold lqueue; rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (lock, sh, q_lock_pred t P p lock gsh2).
  unfold q_lock_pred at 2; unfold q_lock_pred'; Intros vals head addc remc h'.
  forward.
  rewrite data_at_isptr; Intros; rewrite isptr_offset_val_zero; auto.
  forward.
  forward_if (PROP (Zlength vals <> 0)
   LOCAL (temp _len (vint (Zlength vals)); temp _q p; temp _l lock; temp _tgt p)
   SEP (lock_inv sh lock (q_lock_pred t P p lock gsh2);
   data_at Tsh tqueue
     (rotate (complete MAX (map fst vals)) head MAX,
     (vint (Zlength vals), (vint head, (vint ((head + Zlength vals) mod MAX), (addc, remc))))) p;
   cond_var Tsh addc; cond_var Tsh remc; malloc_token Tsh (sizeof tqueue_t) p;
   malloc_token Tsh (sizeof tcond) addc; malloc_token Tsh (sizeof tcond) remc;
   malloc_token Tsh (sizeof tlock) lock; ghost gsh2 (Tsh, h') p;
   fold_right sepcon emp (map (fun x => let '(p, v) := x in
     !!(P v) && (data_at Tsh t v p * malloc_token Tsh (sizeof t) p)) vals);
   field_at sh tqueue_t [StructField _lock] lock p; ghost gsh1 (sh, h) p)).
  { forward_call (lock, sh, q_lock_pred t P p lock gsh2).
    { simpl; lock_props.
      unfold q_lock_pred, q_lock_pred'; Exists vals head addc remc h'; simpl; entailer!. }
    forward.
    Exists (vint 0); entailer!.
    destruct (Memory.EqDec_val (vint 0) nullval); [|contradiction n; auto].
    unfold lqueue; simpl; entailer!. }
  { forward.
    entailer!.
    congruence. }
  Intros.
  assert (Zlength vals > 0).
  { rewrite Zlength_correct in *.
    destruct (length vals); [omega | rewrite Nat2Z.inj_succ; omega]. }
  evar (R : mpred).
  replace_SEP 9 (!!(Forall isptr (map fst vals)) && R); subst R.
  { go_lower; apply prop_and_same_derives, all_ptrs. }
  forward.
  forward.
  { go_lower; Intros.
    rewrite Znth_head; try rewrite Zlength_map; try omega.
    repeat apply andp_right; apply prop_right; auto.
    apply Forall_Znth; [rewrite Zlength_map; omega|].
    eapply Forall_impl; [|eauto].
    destruct a; auto. }
  forward.
  forward.
  { go_lower; simpl.
    repeat apply andp_right; apply prop_right; auto.
    rewrite andb_false_intro2; simpl; auto. }
  forward.
  rewrite cond_var_isptr; Intros.
  forward.
  freeze [0; 1; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] FR; forward_call (addc, Tsh).
  thaw FR.
  rewrite upd_rotate; try rewrite Zlength_complete; try rewrite Zlength_map; auto.
  rewrite Zminus_diag, Zmod_0_l.
  destruct vals; [rewrite Zlength_nil in *; omega|].
  rewrite Zlength_cons in *.
  simpl; rewrite rotate_1; try rewrite Zlength_map; try omega.
  unfold sem_mod; simpl sem_binarith.
  unfold both_int; simpl force_val.
  rewrite andb_false_intro2; [|simpl; auto].
  simpl force_val.
  rewrite !add_repr, mods_repr; try computable.
  destruct p0 as (e, v).
  exploit (consistent_cons_rem(t := reptype t)); eauto; intro.
  gather_SEP 8 11.
  rewrite sepcon_comm; replace_SEP 0 (!!(list_incl h h') && ghost Tsh (Tsh, h') p).
  { go_lower.
    eapply derives_trans; [apply prop_and_same_derives, ghost_inj|].
    Intros; rewrite ghost_share_join; auto; entailer!. }
  Intros; apply hist_add with (e0 := QRem e v); [eauto|].
  erewrite <- ghost_share_join with (h1 := h ++ [QRem e v])(sh := sh); try eassumption; try apply list_incl_app;
    auto.
  forward_call (lock, sh, q_lock_pred t P p lock gsh2).
  { lock_props.
    unfold q_lock_pred, q_lock_pred'; Exists vals ((head + 1) mod MAX) addc remc (h' ++ [QRem e v]).
    unfold Z.succ; rewrite sub_repr, Z.add_simpl_r, (Z.add_comm (Zlength vals)), Z.add_assoc,
      Zplus_mod_idemp_l.
    simpl; entailer!.
    apply Z_mod_lt; omega. }
  forward.
  Exists e; entailer!.
  { rewrite Znth_head; auto; rewrite Zlength_cons, Zlength_map; omega. }
  destruct (Memory.EqDec_val e nullval).
  { rewrite data_at_isptr; Intros.
    subst; contradiction. }
  Exists v; unfold lqueue; simpl; entailer!; auto.
  { split; try omega.
    transitivity MAX; [omega | unfold MAX; computable]. }
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_exit.
semax_func_cons body_free.
semax_func_cons body_malloc. apply semax_func_cons_malloc_aux.
repeat semax_func_cons_ext.
semax_func_cons body_surely_malloc.
semax_func_cons body_q_new.
semax_func_cons body_q_del.
semax_func_cons body_q_add.
semax_func_cons body_q_tryremove.
semax_func_cons body_q_remove.
Qed.
