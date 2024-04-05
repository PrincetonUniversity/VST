Require Import mailbox.verif_atomic_exchange.
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.
Require Import VST.zlist.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.

Section mpred.

Context `{!VSTGS unit Σ, AEGS0 : !AEGS t_atom_int, !inG Σ (excl_authR (leibnizO val))}.
Existing Instance concurrent_ext_spec.

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call (* p = malloc(n); *)
     (t, gv).
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (mem_mgr gv; malloc_token Ews t p; data_at_ Ews t p)).
  * if_tac.
    subst p. entailer!.
    entailer!.
  * forward_call 1.
    contradiction.
  * if_tac.
    + forward. subst p. congruence.
    + Intros. forward. entailer!.
  * forward.
    Exists p; entailer!!.
Qed.

Lemma body_memset : semax_body Vprog Gprog f_memset memset_spec.
Proof.
  start_function.
  forward.
  rewrite data_at__isptr; Intros.
  pose proof (sizeof_pos t).
  assert_PROP (sizeof t <= Ptrofs.max_unsigned).
  { entailer!.
    destruct H2 as [? [_ [? _]]].
    destruct p; inv H2.
    simpl in H3.
    pose proof Ptrofs.unsigned_range i.
    simpl. rep_lia.
  }
  forward_for_simple_bound n (∃ i : Z, PROP ()
    LOCAL (temp _p p; temp _s p; temp _c (vint c); temp _n (vptrofs (4 * n)))
    SEP (data_at sh (tarray tint n) (repeat (vint c) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (n - i))) p)).
  { rewrite -> Z.mul_comm, Z_div_mult by lia; auto. }
  { entailer!.
    trans (data_at_ sh (tarray tint n) p).
    - rewrite !data_at__memory_block; simpl.
      assert ((4 * Z.max 0 n)%Z = sizeof t) as Hsize.
      { rewrite Z.max_r; auto; lia. }
      setoid_rewrite Hsize; Intros; entailer!!.
      match goal with H : field_compatible _ _ _ |- _ =>
        destruct H as (? & ? & ? & ? & ?) end; repeat split; simpl; auto.
      + unfold size_compatible in *; simpl.
        destruct p; try contradiction.
        setoid_rewrite Hsize; auto.
      + destruct p; try contradiction.
        constructor; intros.
        econstructor; [reflexivity |].
        inv H0.
        inv H9.
        apply Z.divide_add_r; auto.
        apply Z.divide_mul_l.
        exists 1; auto.
    - rewrite data_at__eq.
      unfold default_val, reptype_gen; simpl.
      apply derives_refl. }
  - forward.
    rewrite upd_init_const; [|lia].
    entailer!.
  - forward.
    rewrite Zminus_diag app_nil_r; apply derives_refl.
Qed.

Opaque upto.

Lemma malloc_compatible_isptr:
  forall {cs: compspecs} t p, malloc_compatible (sizeof t) p -> isptr p.
Proof.
intros.
hnf in H. destruct p; try contradiction; simpl; auto.
Qed.
#[local] Hint Resolve malloc_compatible_isptr : core.

Lemma body_initialize_channels : semax_body Vprog Gprog f_initialize_channels initialize_channels_spec.
Proof.
  start_function.
  assert (N < Int.max_signed) as HN by computable.
  assert (B < Int.max_signed) as HB by computable.
  forward_for_simple_bound B (∃ i : Z, PROP ()
    LOCAL (gvars gv)
    SEP (data_at_ Ews (tarray (tptr t_atom_int) N) (gv _comm);
         data_at_ Ews (tarray (tptr tint) N) (gv _reading); data_at_ Ews (tarray (tptr tint) N) (gv _last_read);
         ∃ bufs : list val, ⌜Zlength bufs = i /\ Forall isptr bufs⌝ ∧
           data_at Ews (tarray (tptr tbuffer) B) (bufs ++ repeat Vundef (Z.to_nat (B - i))) (gv _bufs) ∗
           [∗] (map (data_at Ews tbuffer (vint 0)) bufs) ∗
           [∗] (map (malloc_token Ews tbuffer) bufs);
          mem_mgr gv)).
  { unfold B, N; computable. }
  { entailer!.
    Exists ([] : list val); simpl; entailer!. }
  { forward_call (tbuffer, gv).
    Intros b bufs.
    assert_PROP (field_compatible tint [] b) by entailer!.
    forward_call (Ews, tbuffer, b, 0, 1).
    { destruct H3 as [? [? [? [? ?]]]]; auto. }
    clear H3.
    forward.
    rewrite upd_init; auto; try lia.
    entailer!.
    Exists (bufs ++ [b]); rewrite -> Zlength_app, <- app_assoc, !map_app, !big_sepL_app, Forall_app; simpl; entailer!.
    clear; unfold data_at, field_at, at_offset; Intros.
    rewrite !data_at_rec_eq; unfold withspacer; simpl.
    unfold array_pred, aggregate_pred.array_pred, unfold_reptype; simpl.
    rewrite Znth_0_cons; entailer!. clear H0.
    { destruct H as [? [? [? [? ?]]]].
      split; [| split; [| split; [| split]]]; auto.
      destruct b; inv H.
      inv H2.
      specialize (H7 0 ltac:(lia)).
      simpl.
      eapply align_compatible_rec_Tstruct; [reflexivity.. |].
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
  Intros bufs; rewrite Zminus_diag app_nil_r.
  forward_for_simple_bound N (∃ i : Z, PROP ()
    LOCAL (gvars gv)
    SEP (∃ comms : list val, ∃ g : list gname, ∃ g0 : list gname, ∃ g1 : list gname,
         ∃ g2 : list gname, ⌜Zlength comms = i /\ (*Forall isptr comms /\*) Zlength g = i /\
           Zlength g0 = i /\ Zlength g1 = i /\ Zlength g2 = i⌝ ∧
          (data_at Ews (tarray (tptr t_atom_int) N) (comms ++ repeat Vundef (Z.to_nat (N - i))) (gv _comm) ∗
           [∗] (map (fun r => comm_loc 1 (Znth r comms)
             (Znth r g) (Znth r g0) (Znth r g1) (Znth r g2) bufs
             (Znth r shs) ∅) (upto (Z.to_nat i)))) ∗
           [∗] (map (ghost_frag (vint 1)) g0) ∗
           [∗] (map (ghost_frag (vint 0)) g1) ∗
           [∗] (map (ghost_frag (vint 1)) g2);
         ∃ reads : list val, ⌜Zlength reads = i⌝ ∧
           data_at Ews (tarray (tptr tint) N) (reads ++ repeat Vundef (Z.to_nat (N - i))) (gv _reading) ∗
           [∗] (map (data_at_ Ews tint) reads) ∗
           [∗] (map (malloc_token Ews tint) reads);
         ∃ lasts : list val, ⌜Zlength lasts = i⌝ ∧
           data_at Ews (tarray (tptr tint) N) (lasts ++ repeat Vundef (Z.to_nat (N - i))) (gv _last_read) ∗
           [∗] (map (data_at_ Ews tint) lasts) ∗
           [∗] (map (malloc_token Ews tint) lasts);
         data_at Ews (tarray (tptr tbuffer) B) bufs (gv _bufs);
         ∃ sh : share, ⌜sepalg_list.list_join sh1 (sublist i N shs) sh⌝ ∧
           data_at sh tbuffer (vint 0) (Znth 0 bufs);
         [∗] (map (data_at Ews tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs));
         [∗] (map (malloc_token Ews tbuffer) bufs);
         mem_mgr gv)).
  { Exists ([] : list val) ([] : list gname) ([] : list gname) ([] : list gname)
      ([] : list gname) ([] : list val) ([] : list val) Ews. rewrite !data_at__eq. entailer!.
    - rewrite sublist_same; auto; lia.
    - erewrite <- sublist_same with (al := bufs), sublist_next at 1; eauto; try (unfold B, N in *; lia). }
  { Intros comms g g0 g1 g2 reads lasts sh.
    forward_call (vint 0). Intros c.
    forward.
    forward_call (tint, gv). Intros rr.
    forward.
    forward_call (tint, gv). Intros ll.
    ghost_alloc (fun g => own g (●E (vint 1) ⋅ ◯E (vint 1) : excl_authR (leibnizO val))).
    { apply excl_auth_valid. }
    ghost_alloc (fun g => own g (●E (vint 0) ⋅ ◯E (vint 0) : excl_authR (leibnizO val))).
    { apply excl_auth_valid. }
    ghost_alloc (fun g => own g (●E (vint 1) ⋅ ◯E (vint 1) : excl_authR (leibnizO val))).
    { apply excl_auth_valid. }
    ghost_alloc (ghost_hist_ref 1 ∅ ∅).
    Intros g' g0' g1' g2'.
    rewrite !own_op -hist_ref_join_nil.
    repeat match goal with |-context[own ?g (●E ?v)] => change (own g (●E v : excl_authR (leibnizO _))) with (ghost_auth v g) end.
    repeat match goal with |-context[own ?g (◯E ?v)] => change (own g (◯E v : excl_authR (leibnizO _))) with (ghost_frag v g) end.
    match goal with H : sepalg_list.list_join sh1 (sublist i N shs) sh |- _ =>
      erewrite sublist_next in H; try lia; inversion H as [|????? Hj1 Hj2] end.
    apply sepalg.join_comm in Hj1; eapply sepalg_list.list_join_assoc1 in Hj2; eauto.
    destruct Hj2 as (sh' & ? & Hsh').
    rewrite <- (data_at_share_join (Znth i shs) sh' sh) by (apply Hsh').
    Intros.
    gather_SEP (ghost_hist _ _ _) (ghost_ref _ _) (ghost_auth _ g0') (ghost_auth _ g1') (ghost_auth _ g2') (SC_atomics.atomic_int_at _ _ _)
      (data_at (Znth i shs) _ _ _);
      viewshift_SEP 0 (AE_loc 1 c g' (vint 0) (comm_R bufs (Znth i shs) g0' g1' g2') ∅).
    { go_lowerx.
      rewrite bi.sep_emp /AE_loc.
      sep_apply atomic_int_isptr; Intros; rewrite bi.pure_True // bi.True_and.
      iIntros "(? & $ & ? & ? & ? & ? & ?)"; iApply inv_alloc.
      rewrite /AE_inv; iNext.
      iExists [], (vint 0); iFrame.
      iSplit; first done.
      iExists 0, 1, 1; simpl.
      eauto with iFrame. }
    forward.
    Exists (comms ++ [c]) (g ++ [g']) (g0 ++ [g0']) (g1 ++ [g1']) (g2 ++ [g2'])
      (reads ++ [rr]) (lasts ++ [ll]) sh'; rewrite -> !upd_init by (rewrite -> ?Zlength_map in *; auto; lia).
    rewrite -> !Zlength_app, !Zlength_cons, !Zlength_nil; rewrite -> !map_app, <- !app_assoc.
    go_lower.
    rewrite bi.pure_True // bi.True_and.
    assert_PROP (isptr ll /\ isptr rr (*/\ isptr c*)) by (entailer!; eauto).
    rewrite !bi.pure_True; [|rewrite ?Forall_app; repeat split; auto; try lia; repeat constructor; intuition..].
    rewrite !bi.True_and.
    rewrite -> Z2Nat.inj_add, upto_app, !map_app, !big_sepL_app; try lia; simpl.
    change (upto 1) with [0]; simpl.
    rewrite -> Z2Nat.id, Z.add_0_r by lia.
    rewrite -> !Znth_app1 by auto.
    subst; rewrite Zlength_correct Nat2Z.id.
    unfold comm_loc, AE_loc; cancel.
    erewrite map_ext_in; [apply derives_refl|].
    intros; rewrite -> In_upto, <- Zlength_correct in *.
    rewrite !app_Znth1; (lia || tauto). }
  Intros comms g g0 g1 g2 reads lasts sh.
  match goal with H : sepalg_list.list_join sh1 (sublist N N shs) sh |- _ =>
    rewrite sublist_nil in H; inv H end.
  rewrite !app_nil_r.
  Exists comms bufs reads lasts g g0 g1 g2.
  (* cancel appears not to cancel enough because constr_eq is failing on identical
     terms, which I don't know how to fix. *)
  #[local] Ltac cancel_unify_tac ::= reflexivity.
  entailer!.
Qed.

End mpred.
