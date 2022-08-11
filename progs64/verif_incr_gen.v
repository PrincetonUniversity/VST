(* Inspired by:
   Subjective Auxiliary State for Coarse-Grained Concurrency, Ley-Wild and Nanevski, POPL 2013. *)

Require Import VST.concurrency.conclib.
Require Import VST.concurrency.lock_specs.
Require Import VST.atomics.verif_lock.
Require Import VST.concurrency.ghosts.
Require Import VST.progs64.incrN.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition spawn_spec := DECLARE _spawn spawn_spec.

#[local] Program Instance sum_ghost : Ghost :=
  { G := nat; valid g := True; Join_G a b c := c = (a + b)%nat }.
Next Obligation.
Proof.
  exists (fun _ => O).
  - intros; hnf; auto.
  - intros; eexists; hnf; eauto.
  - auto.
Defined.
Next Obligation.
Proof.
  constructor.
  - intros; hnf in *.
    subst; auto.
  - intros; hnf in *.
    exists (b + c)%nat; split; hnf; lia.
  - intros; hnf in *.
    lia.
  - intros; hnf in *.
    lia.
Qed.

#[local] Instance ctr_ghost : Ghost := ref_PCM sum_ghost.

Definition ghost_ref n g := ghost_reference(P := sum_ghost) n g.
Definition ghost_part sh n g := ghost_part(P := sum_ghost) sh n g.
Definition ghost_both sh n1 n2 g := ghost_part_ref(P := sum_ghost) sh n1 n2 g.

Definition t_counter := Tstruct _counter noattr.

Definition cptr_lock_inv g ctr :=
  EX z : nat, field_at Ews t_counter [StructField _ctr] (Vint (Int.repr (Z.of_nat z))) ctr * ghost_ref z g.

Definition ctr_handle sh h g ctr n := lock_inv sh h (cptr_lock_inv g ctr) * ghost_part sh n g.

Definition init_ctr_spec :=
 DECLARE _init_ctr
  WITH gv: globals
  PRE [ ]
         PROP  ()
         PARAMS ()
         GLOBALS (gv)
         SEP   (library.mem_mgr gv; data_at_ Ews t_counter (gv _c))
  POST [ tvoid ]
    EX h : lock_handle, EX g : gname,
         PROP ()
         LOCAL ()
         SEP (library.mem_mgr gv;
              field_at Ews t_counter [StructField _lock] (ptr_of h) (gv _c); spacer Ews 4 8 (gv _c);
              ctr_handle Tsh h g (gv _c) O).

Definition dest_ctr_spec :=
 DECLARE _dest_ctr
  WITH h : lock_handle, g : gname, v : nat, gv : globals
  PRE [ ]
         PROP  ()
         PARAMS ()
         GLOBALS (gv)
         SEP (field_at Ews t_counter [StructField _lock] (ptr_of h) (gv _c); spacer Ews 4 8 (gv _c);
              ctr_handle Tsh h g (gv _c) v)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (data_at Ews t_counter (vint (Z.of_nat v), ptr_of h) (gv _c)).

Definition incr_spec :=
 DECLARE _incr
  WITH sh1 : share, sh : share, h : lock_handle, g : gname, n : nat, gv: globals
  PRE [ ]
         PROP  (readable_share sh1; sh <> Share.bot)
         PARAMS ()
         GLOBALS (gv)
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c);
              ctr_handle sh h g (gv _c) n)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c);
              ctr_handle sh h g (gv _c) (S n)).


Definition thread_lock_R sh1 sh g ctr lockc :=
  field_at sh1 t_counter [StructField _lock] (ptr_of lockc) ctr * ctr_handle sh lockc g ctr 1%nat.

Definition thread_lock_inv sh1 tsh sh g ctr lockc lockt :=
  selflock (thread_lock_R sh1 sh g ctr lockc) tsh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * share * lock_handle * share * lock_handle * gname * globals
  PRE [ tptr tvoid ]
         let '(sh1, tsh, ht, sh, h, g, gv) := x in
         PROP  (readable_share sh1; tsh <> Share.bot; sh <> Share.bot; ptr_of ht = y)
         PARAMS (y)
         GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); 
                ctr_handle sh h g (gv _c) O;
                lock_inv tsh ht (thread_lock_inv sh1 tsh sh g (gv _c) h ht))
  POST [ tint ]
         PROP ()
         RETURN (Vint Int.zero)
         SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  freelock_spec; spawn_spec; init_ctr_spec; dest_ctr_spec; incr_spec; thread_func_spec; main_spec]).

Lemma ctr_inv_exclusive : forall lg p,
  exclusive_mpred (cptr_lock_inv lg p).
Proof.
  intros; unfold cptr_lock_inv.
  eapply derives_exclusive, exclusive_sepcon1 with (Q := EX z : nat, _),
    field_at__exclusive with (sh := Ews)(t := t_counter); auto; simpl; try lia.
  Intro z; apply sepcon_derives; [cancel|].
  Exists z; apply derives_refl.
  { simpl; lia. }
Qed.
#[export] Hint Resolve ctr_inv_exclusive : core.

Lemma ctr_handle_share_join : forall sh1 sh2 sh h g ctr v1 v2, sh1 <> Share.bot -> sh2 <> Share.bot -> sepalg.join sh1 sh2 sh ->
  ctr_handle sh1 h g ctr v1 * ctr_handle sh2 h g ctr v2 = ctr_handle sh h g ctr (v1 + v2)%nat.
Proof.
  intros; unfold ctr_handle.
  erewrite (sepcon_comm (lock_inv _ _ _)), <- sepcon_assoc, (sepcon_assoc (ghost_part _ _ _)), lock_inv_share_join by eauto.
  unfold ghost_part; erewrite (sepcon_comm (ghosts.ghost_part _ _ _)), sepcon_assoc, ghost_part_join; eauto.
  reflexivity.
Qed.

Lemma body_init_ctr: semax_body Vprog Gprog f_init_ctr init_ctr_spec.
Proof.
  start_function.
  forward.
  ghost_alloc (ghost_both Tsh O O).
  { split; auto.
    apply (@self_completable sum_ghost). }
  Intros g.
  forward_call (gv, fun _ : lock_handle => cptr_lock_inv g (gv _c)).
  Intros h.
  forward.
  forward.
  forward_call release_simple (Tsh, h, cptr_lock_inv g (gv _c)).
  { lock_props.
    unfold cptr_lock_inv.
    unfold ghost_both; rewrite <- ghost_part_ref_join.
    unfold_data_at (data_at _ _ _ _).
    unfold ghost_ref; Exists O; entailer!. }
  unfold ctr_handle, ghost_part; Exists h g; entailer!.
Qed.

Lemma body_dest_ctr: semax_body Vprog Gprog f_dest_ctr dest_ctr_spec.
Proof.
  start_function.
  unfold ctr_handle; Intros.
  forward.
  forward_call (Tsh, h, cptr_lock_inv g (gv _c)).
  forward.
  forward_call freelock_simple (h, cptr_lock_inv g (gv _c)).
  { lock_props. }
  unfold cptr_lock_inv.
  Intros z.
  entailer!.
  unfold ghost_part, ghost_ref; sep_apply (ref_sub(P := sum_ghost)).
  rewrite eq_dec_refl; Intros; subst.
  unfold_data_at (data_at _ _ _ _); cancel.
  rewrite <- sepcon_emp; apply sepcon_derives; apply own_dealloc.
Qed.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  unfold ctr_handle; Intros.
  forward.
  forward_call (sh, h, cptr_lock_inv g (gv _c)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z.
  forward.
  forward.
  forward.
  gather_SEP (ghost_part _ _ _) (ghost_ref _ _).
  viewshift_SEP 0 (ghost_part sh (S n) g * ghost_ref (S z) g).
  { go_lower.
    unfold ghost_part, ghost_ref; rewrite !ghost_part_ref_join.
    eapply derives_trans, bupd_fupd.
    apply ref_add with (b := 1%nat); try (hnf; lia). }
  Intros; forward_call release_simple (sh, h, cptr_lock_inv g (gv _c)).
  { lock_props.
    unfold cptr_lock_inv; Exists (S z).
    rewrite Nat2Z.inj_succ.
    entailer!. }
  forward.
  unfold ctr_handle; cancel.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (sh1, sh, h, g, O, gv).
  forward_call release_self (tsh, ht, thread_lock_R sh1 sh g (gv _c) h).
  { unfold thread_lock_inv, selflock, thread_lock_R; cancel. }
  forward.
Qed.

Definition N := 5.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  fold N.
  sep_apply (library.create_mem_mgr gv).
  forward_call gv.
  Intros x; destruct x as (h, g); simpl.
  (* need to split off shares for the locks and ghost here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  destruct (split_shares (Z.to_nat N) Ews) as (sh0 & shs & ? & ? & ? & Hshs); auto.
  destruct (split_shares (Z.to_nat N) Tsh) as (gsh0 & gshs & ? & ? & ? & Hgshs); auto.
  rewrite Z2Nat.id in * by (unfold N; computable).
  assert_PROP (field_compatible (tarray (tptr t_lock) N) [] v_thread_lock) by entailer!.
  assert (N <= Int.max_signed) by computable.
  forward_for_simple_bound N (EX i : Z, EX sh : share, EX gsh : share, EX ll : list lock_handle,
    PROP (sepalg_list.list_join sh0 (sublist i N shs) sh;
          sepalg_list.list_join gsh0 (sublist i N gshs) gsh;
          Zlength ll = i; Forall isptr (map ptr_of ll))
    LOCAL (lvar _thread_lock (tarray (tptr t_lock) N) v_thread_lock; gvars gv)
    SEP (library.mem_mgr gv; field_at sh t_counter (DOT _lock) (ptr_of h) (gv _c);
         spacer Ews 4 8 (gv _c); ctr_handle gsh h g (gv _c) O;
         iter_sepcon (fun j => lock_inv gsh1 (Znth j ll)
           (thread_lock_inv (Znth j shs) gsh2 (Znth j gshs) g (gv _c) h (Znth j ll)))
           (upto (Z.to_nat i));
         data_at Tsh (tarray (tptr t_lock) N) (map ptr_of ll ++ repeat Vundef (Z.to_nat (N - i))) v_thread_lock; has_ext tt))%assert.
  { Exists Ews Tsh (@nil lock_handle).
    rewrite !sublist_same by auto; entailer!.
    rewrite data_at__eq; apply derives_refl. }
  { (* first loop *)
    forward_call (gv, fun ht => thread_lock_inv (Znth i shs) gsh2 (Znth i gshs) g (gv _c) h ht).
    Intros ht.
    forward.
    assert_PROP (0 <= i < Zlength (map ptr_of ll ++ repeat Vundef (Z.to_nat (N - i)))) as Hi.
    { entailer!. rewrite Zlength_app, Zlength_map, Zlength_repeat, Zplus_minus by lia; auto. }
    forward.
    { rewrite upd_Znth_same by auto; entailer!. }
    rewrite upd_Znth_same by auto.
    assert (readable_share (Znth (Zlength ll) shs)) as Hshi by (apply Forall_Znth; auto; lia).
    rewrite sublist_next in H10, H11 by lia.
    inv H10; inv H11.
    destruct (sepalg_list.list_join_assoc1 (sepalg.join_comm H17) H19) as (sh' & ? & Hsh').
    destruct (sepalg_list.list_join_assoc1 (sepalg.join_comm H15) H18) as (gsh' & ? & Hgsh').
    assert (Znth (Zlength ll) gshs <> Share.bot).
    { intro X; contradiction bot_unreadable.
      rewrite <- X; apply Forall_Znth; auto; lia. }
    assert (gsh' <> Share.bot).
    { intro X; contradiction bot_unreadable.
      rewrite <- X; eapply readable_share_list_join; eauto. }
    sep_apply lock_inv_isptr; Intros.
    forward_spawn _thread_func (ptr_of ht) (Znth (Zlength ll) shs, gsh2, ht, Znth (Zlength ll) gshs, h, g, gv).
    { erewrite <- lock_inv_share_join; try apply gsh1_gsh2_join; auto.
      erewrite <- field_at_share_join; try apply Hsh'.
      change O with (O + O)%nat.
      erewrite <- ctr_handle_share_join; try apply Hgsh'; auto; simpl.
      entailer!. }
    { simpl; auto. }
    Exists sh' gsh' (ll ++ [ht]); entailer!.
    { split; [autorewrite with sublist; auto | rewrite map_app, Forall_app; repeat constructor; auto]. }
    apply sepcon_derives.
    - rewrite Z2Nat.inj_add, upto_app by lia.
      rewrite iter_sepcon_app; simpl.
      rewrite Z2Nat.id, Z.add_0_r, app_Znth2, Zminus_diag, Znth_0_cons by (tauto || lia); cancel.
      rewrite Zlength_correct, Nat2Z.id; apply iter_sepcon_derives; intros ??%In_upto.
      rewrite <- Zlength_correct in *; autorewrite with sublist; auto.
    - rewrite upd_complete_gen' by tauto; autorewrite with sublist; apply derives_refl. }
  rewrite !sublist_nil, Zminus_diag; Intros shx gshx ll.
  inv H9; inv H10.
  forward_for_simple_bound N (EX i : Z, EX sh : share, EX gsh : share,
    PROP (sepalg_list.list_join shx (sublist 0 i shs) sh;
          sepalg_list.list_join gshx (sublist 0 i gshs) gsh)
    LOCAL (lvar _thread_lock (tarray (tptr t_lock) N) v_thread_lock; gvars gv)
    SEP (library.mem_mgr gv; field_at sh t_counter (DOT _lock) (ptr_of h) (gv _c);
         spacer Ews 4 8 (gv _c); ctr_handle gsh h g (gv _c) (Z.to_nat i);
         iter_sepcon (fun j => lock_inv gsh1 (Znth j ll)
           (thread_lock_inv (Znth j shs) gsh2 (Znth j gshs) g (gv _c) h (Znth j ll)))
           (sublist i N (upto (Z.to_nat N)));
         data_at Tsh (tarray (tptr t_lock) N) (map ptr_of ll) v_thread_lock; has_ext tt))%assert.
  { rewrite !sublist_nil, sublist_same, app_nil_r by (auto; lia).
    Exists shx gshx; entailer!.
    { split; constructor. }
    apply derives_refl. }
  { (* second loop *)
    forward.
    { entailer!. apply isptr_is_pointer_or_null, Forall_Znth; auto.
      rewrite Zlength_map; simpl in *; replace (Zlength ll) with N; auto. }
    Opaque N.
    rewrite sublist_next; auto; simpl.
    rewrite Znth_upto by auto.
    forward_call (gsh1, Znth i ll, thread_lock_inv (Znth i shs) gsh2 (Znth i gshs) g (gv _c) h (Znth i ll)).
    { rewrite Znth_map by (simpl in *; lia); entailer!. }
    { cancel. }
    unfold thread_lock_inv at 2; unfold thread_lock_R, selflock; Intros.
    forward.
    unfold thread_lock_inv.
    forward_call freelock_self (gsh1, gsh2, Znth i ll, thread_lock_R (Znth i shs) (Znth i gshs) g (gv _c) h).
    { rewrite Znth_map by (simpl in *; lia); entailer!. }
    { unfold selflock; cancel. }
    erewrite <- sublist_same with (al := shs) in Hshs by eauto.
    erewrite <- sublist_same with (al := gshs) in Hgshs by eauto.
    rewrite sublist_split with (mid := i) in Hshs, Hgshs by lia.
    rewrite sublist_next with (i := i) in Hshs by lia.
    rewrite sublist_next with (i := i) in Hgshs by lia.
    rewrite app_cons_assoc in Hshs, Hgshs.
    apply sepalg_list.list_join_unapp in Hshs as (sh' & Hshs1 & ?).
    apply sepalg_list.list_join_unapp in Hgshs as (gsh' & Hgshs1 & ?).
    apply sepalg_list.list_join_unapp in Hshs1 as (? & J & J1).
    apply sepalg_list.list_join_unapp in Hgshs1 as (? & Jg & Jg1).
    apply list_join_eq with (c := sh) in J; auto; subst.
    apply list_join_eq with (c := gsh) in Jg; auto; subst.
    rewrite <- sepalg_list.list_join_1 in J1, Jg1.
    rewrite !(sublist_split 0 i (i + 1)), !sublist_len_1 by lia.
    Exists sh' gsh'; entailer!.
    { split; eapply sepalg_list.list_join_app; eauto; econstructor; eauto; constructor. }
    unfold thread_lock_R.
    sep_eapply field_at_share_join; [apply sepalg.join_comm; eauto|].
    sep_eapply ctr_handle_share_join; try (apply sepalg.join_comm; eauto).
    { intros X; contradiction unreadable_bot; rewrite <- X; apply Forall_Znth; auto; lia. }
    { intros X; contradiction unreadable_bot; rewrite <- X.
      eapply readable_share_list_join; eauto. }
    rewrite Z2Nat.inj_add, plus_comm by lia; simpl; unfold thread_lock_inv, thread_lock_R, selflock; cancel.
    { rewrite Zlength_upto; lia. } }
  Intros sh' gsh'.
  eapply list_join_eq in Hshs; [|erewrite <- (sublist_same 0 N shs) by auto; eauto].
  eapply list_join_eq in Hgshs; [|erewrite <- (sublist_same 0 N gshs) by auto; eauto].
  subst.
  forward_call (h, g, Z.to_nat N, gv).
  forward.
  rewrite Z2Nat.id by auto.
  (* We've proved that t is N! *)
  forward.
  { repeat sep_apply data_at_data_at_; cancel. }
Qed.

Definition extlink := ext_link_prog prog.
Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
#[export] Existing Instance Espec.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons_ext.
{ simpl.
  Intros h.
  unfold PROPx, LOCALx, SEPx, local, lift1; simpl; unfold liftx; simpl; unfold lift; Intros.
  destruct ret; unfold eval_id in H0; simpl in H0; subst; simpl; [|contradiction].
  saturate_local; apply prop_right; auto. }
do 4 semax_func_cons_ext.
semax_func_cons body_init_ctr.
semax_func_cons body_dest_ctr.
semax_func_cons body_incr.
semax_func_cons body_thread_func.
semax_func_cons body_main.
Qed.
