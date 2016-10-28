Require Import progs.conclib.
Require Import progs.conc_queue.
Require Import progs.conc_queue_specs.
Require Import SetoidList.
Require Import floyd.library.

(* This lets us use a library as a client. *)
Axiom semax_func_mono : forall {Espec : OracleKind} {C : compspecs} V G fs G' G2,
  semax_func V G fs G' -> incl G G2 -> semax_func V G2 fs G'.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition makecond_spec := DECLARE _makecond (makecond_spec _).
Definition freecond_spec := DECLARE _freecond (freecond_spec _).
Definition wait_spec := DECLARE _waitcond (wait2_spec _).
Definition signal_spec := DECLARE _signalcond (signal_spec _).

Definition q_new_spec := DECLARE _q_new q_new_spec'.
Definition q_del_spec := DECLARE _q_del q_del_spec'.
Definition q_add_spec := DECLARE _q_add q_add_spec'.
Definition q_remove_spec := DECLARE _q_remove q_remove_spec'.
Definition q_tryremove_spec := DECLARE _q_tryremove q_tryremove_spec'.

Definition Gprog : funspecs := ltac:(with_library prog
  [acquire_spec; release_spec; makelock_spec; freelock_spec;
   makecond_spec; freecond_spec; wait_spec; signal_spec;
   q_new_spec; q_del_spec; q_add_spec; q_remove_spec; q_tryremove_spec]).

Lemma all_ptrs : forall vals,
  fold_right sepcon emp (map (fun p => EX t : type, EX d : reptype t, data_at Tsh t d p) vals) |--
  !!(Forall isptr vals).
Proof.
  induction vals; simpl; intros; entailer.
  rewrite data_at_isptr.
  eapply derives_trans; [apply saturate_aux20|].
  { apply andp_left1, derives_refl. }
  { apply IHvals; auto. }
  normalize.
Qed.

Lemma reqs_precise : forall r vals r1 r2
  (Hvals1 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap) (fold_right sepcon emp
    (map (fun p => EX t : type, EX d : reptype t, data_at Tsh t d p) vals)) r1)
  (Hvals2 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap) (fold_right sepcon emp
    (map (fun p => EX t : type, EX d : reptype t, data_at Tsh t d p) vals)) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r), r1 = r2.
Proof.
  induction vals; simpl; intros.
  - apply sepalg.same_identity with (a := r); auto.
    { destruct Hr1 as (? & H); specialize (Hvals1 _ _ H); subst; auto. }
    { destruct Hr2 as (? & H); specialize (Hvals2 _ _ H); subst; auto. }
  - destruct Hvals1 as (r1a & r1b & ? & (? & ? & Hh1) & ?), Hvals2 as (r2a & r2b & ? & (? & ? & Hh2) & ?).
    assert (r1a = r2a); [|subst].
    { apply data_at_data_at_ in Hh1; apply data_at_data_at_ in Hh2.
SearchAbout precise.
(* Should the queue be restricted to holding simple (by-value and non-volatile) data? We need to be sure that
   it's precise. Maybe we should need to prove that the data is precise when we insert it...
   Or maybe data_at is always precise, and I just haven't figured out the conditions yet? *)
      eapply precise_request with (sh := Tsh); auto; eauto.
      { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
      { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. } }
    assert (r1b = r2b); [|subst].
    { eapply IHreqs; eauto.
      { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
      { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. } }
    eapply sepalg.join_eq; auto.
Qed.

Axiom ghost_precise : forall sh t p, precise (EX v : reptype t, ghost sh t v p).

Lemma ghosts_precise : forall sh r ghosts ns1 ns2 r1 r2
  (Hghosts1 : predicates_hered.app_pred (fold_right sepcon emp
    (map Interp (map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p))
    (combine ns1 ghosts)))) r1)
  (Hghosts2 : predicates_hered.app_pred (fold_right sepcon emp
    (map Interp (map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p))
    (combine ns2 ghosts)))) r2)
  (Hlen1 : length ns1 = length ghosts) (Hlen2 : length ns2 = length ghosts)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r), r1 = r2.
Proof.
  induction ghosts; destruct ns1, ns2; try discriminate; simpl; intros.
  - apply sepalg.same_identity with (a := r); auto.
    { destruct Hr1 as (? & H); specialize (Hghosts1 _ _ H); subst; auto. }
    { destruct Hr2 as (? & H); specialize (Hghosts2 _ _ H); subst; auto. }
  - inv Hlen1; inv Hlen2.
    destruct Hghosts1 as (r1a & r1b & ? & ? & ?), Hghosts2 as (r2a & r2b & ? & ? & ?).
    rewrite interp_ghost in *.
    assert (r1a = r2a); [|subst].
    { eapply ghost_precise.
      { eexists; eauto. }
      { eexists; eauto. }
      { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
      { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. } }
    assert (r1b = r2b); [|subst].
    { eapply IHghosts; eauto.
      { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
      { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. } }
    eapply sepalg.join_eq; auto.
Qed.*)

Lemma tqueue_inj : forall r buf1 buf2 len1 len2 head1 head2 tail1 tail2 (addc1 addc2 remc1 remc2 : val)
  p r1 r2
  (Hp1 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap)
     (data_at Tsh tqueue (buf1, (vint len1, (vint head1, (vint tail1, (addc1, remc1))))) p) r1)
  (Hp2 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap)
     (data_at Tsh tqueue (buf2, (vint len2, (vint head2, (vint tail2, (addc2, remc2))))) p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hbuf1 : Forall (fun v => v <> Vundef) buf1) (Hl1 : Zlength buf1 = MAX)
  (Hbuf2 : Forall (fun v => v <> Vundef) buf2) (Hl2 : Zlength buf2 = MAX)
  (Haddc1 : addc1 <> Vundef) (Haddc2 : addc2 <> Vundef) (Hremc1 : remc1 <> Vundef) (Hremc2 : remc2 <> Vundef),
  r1 = r2 /\ buf1 = buf2 /\ Int.repr len1 = Int.repr len2 /\ Int.repr head1 = Int.repr head2 /\
  Int.repr tail1 = Int.repr tail2 /\ addc1 = addc2 /\ remc1 = remc2.
Proof.
  intros.
  destruct Hp1 as (? & ? & ? & ? & Hb1 & ? & ? & ? & Hlen1 & ? & ? & ? & Hhead1 & ? & ? & ? & Htail1 & ? & ? & ?
    & Hadd1 & Hrem1); unfold withspacer, at_offset, eq_rect_r in *; simpl in *.
  destruct Hp2 as (? & ? & ? & ? & Hb2 & ? & ? & ? & Hlen2 & ? & ? & ? & Hhead2 & ? & ? & ? & Htail2 & ? & ? & ?
    & Hadd2 & Hrem2); unfold withspacer, at_offset, eq_rect_r in *; simpl in *.
  assert (readable_share Tsh) as Hread by auto.
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Hrem1 Hrem2); auto.
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Hadd1 Hadd2); auto.
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Htail1 Htail2); auto.
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { discriminate. }
  { discriminate. }
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Hhead1 Hhead2); auto.
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { discriminate. }
  { discriminate. }
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Hlen1 Hlen2); auto.
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { discriminate. }
  { discriminate. }
  exploit (data_at_ptr_array_inj _ _ _ _ _ _ _ _ r Hread Hb1 Hb2); auto.
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  intros (? & ?) (? & ?) (? & ?) (? & ?) (? & ?) (? & ?) (? & ?); subst; join_inj.
  repeat split; auto; congruence.
Qed.

Lemma q_inv_precise : forall p gsh2, precise (q_lock_pred p gsh2).
Proof.
  unfold q_lock_pred, q_lock_pred'; intros ????? H1 H2 Hw1 Hw2.
  destruct H1 as (vals1 & head1 & addc1 & remc1 & h1 & (? & ? & ?) & ? & ? & ? & (? & ? & ? & (? & ? & ? &
    (? & ? & ? & Hq1 & Haddc1) & Hremc1) & Hghost1) & Hvals1),
  H2 as (vals2 & head2 & addc2 & remc2 & h2 & (? & ? & ?) & ? & ? & ? & (? & ? & ? & (? & ? & ? &
    (? & ? & ? & Hq2 & Haddc2) & Hremc2) & Hghost2) & Hvals2).
  pose proof (all_ptrs _ _ Hvals1) as Hptrs1.
  pose proof (all_ptrs _ _ Hvals2) as Hptrs2.
  exploit (tqueue_inj w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hq1 Hq2).
  { eapply sepalg.join_sub_trans; [eexists|]; eauto. }
  { eapply sepalg.join_sub_trans; [eexists|]; eauto. }
  { apply Forall_rotate, Forall_complete; auto; [|discriminate].
    eapply Forall_impl; [|apply Hptrs1]; destruct a; try contradiction; discriminate. }
  { rewrite Zlength_rotate; try rewrite Zlength_complete; try omega; rewrite Zlength_map; auto. }
  { apply Forall_rotate, Forall_complete; auto; [|discriminate].
    eapply Forall_impl; [|apply Hptrs2]; destruct a; try contradiction; discriminate. }
  { rewrite Zlength_rotate; try rewrite Zlength_complete; try omega; rewrite Zlength_map; auto. }
  { rewrite cond_var_isptr in Haddc1; destruct Haddc1, addc1; try contradiction; discriminate. }
  { rewrite cond_var_isptr in Haddc2; destruct Haddc2, addc2; try contradiction; discriminate. }
  { rewrite cond_var_isptr in Hremc1; destruct Hremc1, remc1; try contradiction; discriminate. }
  { rewrite cond_var_isptr in Hremc2; destruct Hremc2, remc2; try contradiction; discriminate. }
  intros (? & ? & Hlen & ? & ? & ? & ? & ?); subst.
  exploit (ghosts_precise _ w _ _ _ _ _ Hghosts1 Hghosts2).
  { repeat rewrite Zlength_correct in *; omega. }
  { repeat rewrite Zlength_correct in *; omega. }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  intro; subst.
  rewrite <- (combine_eq reqs1) in Hreqs1.
  rewrite <- (combine_eq reqs2) in Hreqs2.
  assert (head1 = head2) as ->.
  { apply repr_inj_unsigned; auto; split; try omega; transitivity MAX; try omega; unfold MAX; computable. }
  assert (length reqs1 = length reqs2).
  { apply repr_inj_unsigned in Hlen; rewrite Zlength_correct in Hlen.
    rewrite Zlength_correct in Hlen; Omega0.
    - split; [rewrite Zlength_correct; omega|]; transitivity MAX; try omega; unfold MAX; computable.
    - split; [rewrite Zlength_correct; omega|]; transitivity MAX; try omega; unfold MAX; computable. }
  assert (map snd reqs1 = map snd reqs2) as Heq.
  { eapply complete_inj; [|repeat rewrite map_length; omega].
    eapply rotate_inj; eauto; try omega.
    repeat rewrite length_complete; auto; try (rewrite Zlength_map; auto).
    rewrite Zlength_complete; try rewrite Zlength_map; omega. }
  rewrite Heq in *.
  exploit (reqs_precise w _ _ _ _ _ Hreqs1 Hreqs2); repeat rewrite map_length; auto.
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  assert (readable_share Tsh) as Hread by auto.
  exploit (cond_var_precise _ _ Hread w _ _ Haddc1 Haddc2).
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  exploit (cond_var_precise _ _ Hread w _ _ Hremc1 Hremc2).
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  intros; subst; join_inj.
  match goal with H1 : predicates_hered.app_pred emp ?a,
    H2 : predicates_hered.app_pred emp ?b |- _ => assert (a = b);
      [eapply sepalg.same_identity; auto;
        [match goal with H : sepalg.join a ?x ?y |- _ =>
           specialize (Hemp1 _ _ H); instantiate (1 := x); subst; auto end |
         match goal with H : sepalg.join b ?x ?y |- _ =>
           specialize (Hemp2 _ _ H); subst; auto end] | subst] end.
  join_inj.
Qed.

Lemma q_inv_positive : forall p gsh2, positive_mpred (q_lock_pred p gsh2).
Proof.
  intros; simpl.
  repeat (apply ex_positive; intro).
  apply positive_sepcon2, positive_sepcon1; auto.
Qed.

Lemma body_q_new : semax_body Vprog Gprog f_q_new q_new_spec.
Proof.
  start_function.
  forward_call (sizeof tqueue_t).
  { simpl; computable. }
  Intro p; Intros.
  assert (align_attr noattr 4 | natural_alignment) by (exists 2; auto).
  assert (field_compatible tqueue_t [] p).
  { apply malloc_field_compatible; auto; simpl; computable. }
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
    SEP (@data_at CompSpecs Tsh tqueue (repeat (vint 0) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (MAX - i)),
           (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))) p;
         @data_at_ CompSpecs Tsh (tptr tlock) (offset_val 60 p))).
  { unfold MAX; computable. }
  { unfold MAX; computable. }
  { unfold fold_right; entailer!.
    unfold data_at_, field_at_; unfold_field_at 1%nat; simpl.
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
  forward.
  forward.
  forward.
  forward_call (sizeof tint).
  { simpl; computable. }
  Intro addc; Intros.
  rewrite memory_block_data_at_; [|apply malloc_field_compatible; auto; simpl; computable].
  forward_call (addc, Tsh).
  { unfold tcond; cancel. }
  forward.
  forward_call (sizeof tint).
  { simpl; computable. }
  Intro remc; Intros.
  rewrite memory_block_data_at_; [|apply malloc_field_compatible; auto; simpl; computable].
  forward_call (remc, Tsh).
  { unfold tcond; cancel. }
  forward.
  forward_call (sizeof tlock).
  { admit. } (* lock size broken *)
  { simpl; computable. }
  Intro lock; Intros.
  rewrite memory_block_data_at_; [|apply malloc_field_compatible; auto; simpl; try computable].
  forward_call (lock, Tsh, q_lock_pred p gsh2).
  eapply semax_pre with (P' := PROP () LOCAL (temp _l lock; temp _c remc; temp _i (vint MAX);
      temp _q p; temp _newq p)
    SEP (@data_at CompSpecs Tsh tqueue_t (repeat (vint 0) (Z.to_nat MAX),
           (vint 0, (vint 0, (vint 0, (addc, remc)))), Vundef) p;
         lock_inv Tsh lock (q_lock_pred p gsh2); cond_var Tsh remc; cond_var Tsh addc)).
  { go_lower.
    do 2 (apply andp_right; [apply prop_right; repeat split; auto|]); unfold fold_right; cancel.
    unfold_data_at 1%nat.
    unfold data_at_, field_at_, field_at, at_offset; simpl.
    destruct addc; try contradiction.
    destruct remc; try contradiction; simpl.
    rewrite !field_compatible_cons; simpl; normalize.
    apply andp_right; [apply prop_right; unfold in_members; simpl; split; [|split; [|split]]; auto|].
    simple apply derives_refl. }
  apply new_ghost.
  forward.
  forward_call (lock, Tsh, q_lock_pred p gsh2).
  { simpl.
    Exists ([] : list val) 0 addc remc ([] : hist).
    rewrite Zlength_nil; simpl; cancel.
    normalize.
    apply andp_right; [apply prop_right|].
    { repeat split; auto; unfold MAX; try omega; try computable. }
    subst Frame; instantiate (1 := [field_at Tsh tqueue_t [StructField _lock] lock p; ghost gsh1 (Tsh, []) p]);
      simpl.
    unfold_field_at 1%nat.
    rewrite sem_cast_neutral_ptr; [|destruct lock; simpl; auto; try contradiction].
    erewrite interp_ghost, <- ghost_share_join with (h1 := []); eauto.
    simpl; repeat cancel.
    unfold data_at, field_at; simpl.
    rewrite field_compatible_cons; simpl; entailer. }
  { split; auto; split; [apply q_inv_precise | apply q_inv_positive]. }
  forward.
  Exists p lock; Intros.
  apply andp_right; [apply prop_right; auto|].
  unfold lqueue; simpl; entailer!; auto.
Admitted.

Lemma list_incl_refl : forall {A} (l : list A), list_incl l l.
Proof.
  induction l; auto.
Qed.
Hint Resolve list_incl_refl.

Lemma consistent_inj : forall h a b b' (Hb : consistent h a b) (Hb' : consistent h a b'), b = b'.
Proof.
  induction h; simpl; intros.
  - subst; auto.
  - destruct a; eauto.
    destruct a0; [contradiction|].
    destruct Hb, Hb'; eauto.
Qed.

Lemma body_q_del : semax_body Vprog Gprog f_q_del q_del_spec.
Proof.
  start_function.
  unfold lqueue; rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (lock, Tsh, q_lock_pred p gsh2).
  forward_call (lock, Tsh, q_lock_pred p gsh2).
  { split; auto; apply q_inv_positive. }
  forward_call (lock, sizeof tlock).
  { repeat rewrite sepcon_assoc; apply sepcon_derives; [apply data_at__memory_block_cancel | cancel]. }
  forward.
  simpl; Intros vals head addc remc h'.
  rewrite data_at_isptr, (cond_var_isptr _ addc), (cond_var_isptr _ remc); Intros.
  rewrite isptr_offset_val_zero; auto.
  forward.
  forward_call (addc, Tsh).
  { simpl; cancel. }
  forward_call (addc, sizeof tcond).
  { repeat rewrite sepcon_assoc; apply sepcon_derives; [apply data_at__memory_block_cancel | cancel]. }
  forward.
  forward_call (remc, Tsh).
  forward_call (remc, sizeof tcond).
  { repeat rewrite sepcon_assoc; apply sepcon_derives; [apply data_at__memory_block_cancel | cancel]. }
  rewrite interp_ghost.
  gather_SEP 1 4; rewrite sepcon_comm.
  replace_SEP 0 (!!(h' = h) && ghost Tsh (Tsh, h) p).
  { go_lower.
    eapply derives_trans; [apply prop_and_same_derives, ghost_inj_Tsh|].
    Intros; subst.
    rewrite ghost_share_join; auto; entailer!. }
  Intros; subst.
  exploit (consistent_inj h [] [] vals); auto; intro; subst; simpl.
  rewrite Zlength_nil.
  gather_SEP 1 3; replace_SEP 0 (data_at Tsh tqueue_t ((rotate (complete MAX []) head MAX,
    (vint 0, (vint head, (vint ((head + 0) mod MAX), (addc, remc))))), lock) p).
  { unfold_data_at 2%nat; entailer!.
    unfold data_at, field_at; Intros; simpl.
    rewrite field_compatible_cons; unfold in_members; simpl; entailer!. }
  forward_call (p, sizeof tqueue_t).
  { apply sepcon_derives; [apply data_at_memory_block | cancel]. }
  forward.
  (* Do we want to deallocate the ghost? *)
Admitted.

Lemma consistent_trans : forall h1 h2 a b c, consistent h1 a b -> consistent h2 b c ->
  consistent (h1 ++ h2) a c.
Proof.
  induction h1; simpl; intros; subst; auto.
  destruct a; eauto.
  destruct a0; [contradiction | destruct H; eauto].
Qed.

Corollary consistent_snoc_add : forall h a b e, consistent h a b -> consistent (h ++ [QAdd e]) a (b ++ [e]).
Proof.
  intros; eapply consistent_trans; simpl; eauto.
Qed.

Corollary consistent_cons_rem : forall h a b e, consistent h a (e :: b) -> consistent (h ++ [QRem e]) a b.
Proof.
  intros; eapply consistent_trans; eauto; simpl; auto.
Qed.

Lemma list_incl_app2 : forall {A} (l l1 l2 : list A), list_incl l l2 -> list_incl l (l1 ++ l2).
Proof.
  induction l1; auto; intros.
  simpl; constructor; auto.
Qed.

Lemma list_incl_app : forall {A} (l1 l2 l1' l2' : list A), list_incl l1 l2 -> list_incl l1' l2' ->
  list_incl (l1 ++ l1') (l2 ++ l2').
Proof.
  induction 1; intros.
  - simpl; apply list_incl_app2; auto.
  - simpl; constructor; auto.
  - simpl; constructor 3; auto.
Qed.

Lemma body_q_add : semax_body Vprog Gprog f_q_add q_add_spec.
Proof.
  start_function.
  Intros t d.
  unfold lqueue; rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (lock, sh, q_lock_pred p gsh2).
  simpl; Intros vals head addc remc h'.
  forward.
  rewrite data_at_isptr; Intros; rewrite isptr_offset_val_zero; auto.
  forward.
  forward_while (EX vals : list val, EX head : Z, EX addc : val, EX remc : val, EX h' : hist, PROP ()
   LOCAL (temp _len (vint (Zlength vals)); temp _q p; temp _l lock; temp _tgt p; temp _r e)
   SEP (lock_inv sh lock (q_lock_pred p gsh2);
        q_lock_pred' p vals head addc remc gsh2 h';
        @field_at CompSpecs sh tqueue_t [StructField _lock] lock p;
        @data_at CompSpecs Tsh t d e; ghost gsh1 (sh, h) p)).
  { Exists vals head addc remc h'.
    entailer!.
    apply derives_refl. }
  { go_lower; entailer'. }
  { simpl; Intros.
    forward.
    { go_lower.
      rewrite cond_var_isptr; Intros; entailer'. }
    forward_call (addc0, lock, Tsh, sh, q_lock_pred p gsh2).
    { simpl.
      Exists vals0 head0 addc0 remc0 h'0.
      subst Frame; instantiate (1 := [field_at sh tqueue_t [StructField _lock] lock p;
        data_at Tsh t d e; ghost gsh1 (sh, h) p]); simpl.
      repeat rewrite sepcon_assoc; repeat (apply sepcon_derives; [apply derives_refl|]).
      entailer!.
      apply andp_right; [Intros; cancel | cancel]. }
    simpl; Intros vals1 head1 addc1 remc1 h'1.
    forward.
    Exists (vals1, head1, addc1, remc1, h'1).
    entailer!. }
  simpl; Intros.
  rewrite Int.signed_repr, Zlength_correct in HRE.
  freeze [0; 2; 3; 5; 6; 7; 8] FR; forward.
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
  freeze [0; 1; 3; 4; 5; 6; 7; 8] FR; forward_call (remc0, Tsh).
  thaw FR.
  rewrite upd_rotate; auto; try rewrite Zlength_complete; try rewrite Zlength_map; auto.
  rewrite Zminus_mod_idemp_l, Z.add_simpl_l, (Zmod_small (Zlength vals0));
    [|rewrite Zlength_correct; unfold MAX; omega].
  rewrite upd_complete; [|rewrite Zlength_correct; auto].
  rewrite interp_ghost; gather_SEP 3 8.
  rewrite sepcon_comm; replace_SEP 0 (!!(list_incl h h'0) && ghost Tsh (Tsh, h'0) p).
  { go_lower.
    eapply derives_trans; [apply prop_and_same_derives, ghost_inj|].
    Intros; rewrite ghost_share_join; auto; entailer!. }
  Intros; apply hist_add with (e := QAdd e).
  erewrite <- ghost_share_join with (h1 := h ++ [QAdd e])(sh := sh); try apply H.
  time forward_call (lock, sh, q_lock_pred p gsh2). (* 22s *)
  { simpl.
    Exists (vals0 ++ [e]) head0 addc0 remc0 (h'0 ++ [QAdd e]); unfold fold_right at 1; cancel.
    rewrite data_at_isptr; Intros.
    rewrite map_app, Zlength_app, Zlength_cons, Zlength_nil.
    unfold sem_mod; simpl sem_binarith.
    unfold both_int; simpl force_val.
    rewrite andb_false_intro2; [|simpl; auto].
    simpl force_val.
    rewrite !add_repr, mods_repr; try computable.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    rewrite interp_ghost; simpl; entailer!.
    { split; [rewrite Zlength_correct; unfold MAX; omega|].
      apply consistent_snoc_add; auto. }
    rewrite Zplus_mod_idemp_l, Z.add_assoc.
    repeat rewrite map_app; repeat rewrite sepcon_app; simpl.
    Exists t d; unfold fold_right at 1; cancel.
    { pose proof (Z_mod_lt (head0 + Zlength vals0) MAX).
      split; try omega.
      transitivity MAX; simpl in *; [omega | unfold MAX; computable]. } }
  { split; auto; split; [apply q_inv_precise | apply q_inv_positive]. }
  forward.
  { unfold lqueue; simpl; entailer!; auto. }
  { apply list_incl_app; auto. }
  { pose proof Int.min_signed_neg; split; [rewrite Zlength_correct; omega|].
    transitivity MAX; [auto | unfold MAX; computable]. }
Admitted.

Lemma all_ptrs : forall vals,
  fold_right sepcon emp (map Interp (map (fun p => Exp _ (fun t => Exp _ (fun d =>
    Data_at _ Tsh t d p))) vals)) |-- !!(Forall isptr vals).
Proof.
  induction vals; simpl; intros; entailer.
  rewrite data_at_isptr.
  eapply derives_trans; [apply saturate_aux20; eauto|].
  { apply andp_left1, derives_refl. }
  normalize.
Qed.

Lemma body_q_remove : semax_body Vprog Gprog f_q_remove q_remove_spec.
Proof.
  start_function.
  unfold lqueue; rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (lock, sh, q_lock_pred p gsh2).
  simpl; Intros vals head addc remc h'.
  forward.
  rewrite data_at_isptr; Intros; rewrite isptr_offset_val_zero; auto.
  forward.
  forward_while (EX vals : list val, EX head : Z, EX addc : val, EX remc : val, EX h' : hist, PROP ()
   LOCAL (temp _len (vint (Zlength vals)); temp _q p; temp _l lock; temp _tgt p)
   SEP (lock_inv sh lock (Interp (q_lock_pred p gsh2));
        Interp (q_lock_pred' p vals head addc remc gsh2 h');
        @field_at CompSpecs sh tqueue_t [StructField _lock] lock p; ghost gsh1 (sh, h) p)).
  { Exists vals head addc remc h'; entailer!. }
  { go_lower; entailer'. }
  { simpl; rewrite (cond_var_isptr _ remc0); Intros.
    forward.
    forward_call (remc0, lock, Tsh, sh, q_lock_pred p gsh2).
    { simpl.
      Exists vals0 head0 addc0 remc0 h'0.
      subst Frame; instantiate (1 := [field_at sh tqueue_t [StructField _lock] lock p;
        ghost gsh1 (sh, h) p]); simpl.
      repeat rewrite sepcon_assoc; repeat (apply sepcon_derives; [apply derives_refl|]).
      entailer!.
      apply andp_right; [Intros; entailer! | entailer!]. }
    simpl; Intros vals1 head1 addc1 remc1 h'1; Intros.
    forward.
    Exists (vals1, head1, addc1, remc1, h'1).
    entailer!. }
  simpl; Intros.
  assert (Zlength vals0 > 0).
  { rewrite Zlength_correct in *.
    destruct (length vals0); [|rewrite Nat2Z.inj_succ; omega].
    contradiction HRE; auto. }
  evar (P : mpred).
  replace_SEP 6 (!!(Forall isptr vals0) && P); subst P.
  { go_lower; apply prop_and_same_derives, all_ptrs. }
  forward.
  forward.
  { go_lower; Intros.
    rewrite Znth_head; try rewrite Zlength_map; try omega.
    repeat apply andp_right; apply prop_right; auto.
    apply Forall_Znth; [omega|].
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
  freeze [0; 1; 3; 4; 5; 6; 7] FR; forward_call (addc0, Tsh).
  thaw FR.
  rewrite upd_rotate; try rewrite Zlength_complete; auto.
  rewrite Zminus_diag, Zmod_0_l.
  destruct vals0; [contradiction HRE; auto|].
  rewrite Zlength_cons in *.
  simpl; rewrite rotate_1; try omega.
  unfold sem_mod; simpl sem_binarith.
  unfold both_int; simpl force_val.
  rewrite andb_false_intro2; [|simpl; auto].
  simpl force_val.
  rewrite !add_repr, mods_repr; try computable.
  Intros t d.
  exploit consistent_cons_rem; eauto; intro.
  rewrite interp_ghost; gather_SEP 4 8.
  rewrite sepcon_comm; replace_SEP 0 (!!(list_incl h h'0) && ghost Tsh (Tsh, h'0) p).
  { go_lower.
    eapply derives_trans; [apply prop_and_same_derives, ghost_inj|].
    Intros; rewrite ghost_share_join; auto; entailer!. }
  Intros; apply hist_add with (e := QRem v).
  erewrite <- ghost_share_join with (h1 := h ++ [QRem v])(sh := sh); try apply H; try apply list_incl_app; auto.
  forward_call (lock, sh, q_lock_pred p gsh2).
  { simpl.
    Exists vals0 ((head0 + 1) mod MAX) addc0 remc0 (h'0 ++ [QRem v]).
    unfold Z.succ; rewrite sub_repr, Z.add_simpl_r, (Z.add_comm (Zlength vals0)), Z.add_assoc,
      Zplus_mod_idemp_l, interp_ghost.
    unfold fold_right at 1 2; entailer!.
    apply Z_mod_lt; omega. }
  { split; auto; split; [apply q_inv_precise | apply q_inv_positive]. }
  forward.
  Exists v t d; unfold lqueue; simpl; entailer!; auto.
  rewrite Znth_head; auto; rewrite Zlength_cons; omega.
  { split; try omega.
    transitivity MAX; [omega | unfold MAX; computable]. }
Qed.

Lemma lock_precise : forall sh p lock (Hsh : readable_share sh),
  precise (field_at sh tqueue_t [StructField _lock] lock p).
Proof.
  intros.
  unfold field_at, at_offset; apply precise_andp2.
  rewrite data_at_rec_eq; simpl; auto.
Qed.

(*Lemma lock_struct : forall p, data_at_ Tsh (Tstruct _lock_t noattr) p |-- data_at_ Tsh tlock p.
Proof.
  intros.
  unfold data_at_, field_at_; unfold_field_at 1%nat; simpl.
  unfold field_at; simpl.
  rewrite field_compatible_cons; simpl; entailer.
Qed.

Lemma lock_struct_array : forall z p, data_at_ Tsh (tarray (Tstruct _lock_t noattr) z) p |--
  data_at_ Tsh (tarray tlock z) p.
Proof.
  intros.
  unfold data_at_, field_at_, field_at; simpl; entailer.
  unfold default_val, at_offset; simpl.
  do 2 rewrite data_at_rec_eq; simpl.
  unfold array_pred, aggregate_pred.array_pred, unfold_reptype; simpl; entailer.
  rewrite Z.sub_0_r; clear.
  forget (Z.to_nat z) as l; forget 0 as lo; revert lo; induction l; intros; simpl; auto.
  apply sepcon_derives.
  - unfold at_offset; rewrite data_at_rec_eq; simpl.
    unfold struct_pred, aggregate_pred.struct_pred, at_offset, withspacer; simpl; entailer.
  - eapply derives_trans; [apply aggregate_pred.rangespec_ext_derives |
      eapply derives_trans; [apply IHl | apply aggregate_pred.rangespec_ext_derives]]; simpl; intros;
      rewrite Znth_pos_cons; try omega; replace (i - lo - 1) with (i - Z.succ lo) by omega; auto.
Qed.*)

Lemma lqueue_share_join : forall sh1 sh2 sh p lock gsh1 gsh2 h1 h2
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2) (Hjoin : sepalg.join sh1 sh2 sh),
  lqueue sh1 p lock gsh1 gsh2 h1 * lqueue sh2 p lock gsh1 gsh2 h2 = lqueue sh p lock gsh1 gsh2 (h1 ++ h2).
Proof.
  intros; unfold lqueue; normalize.
  f_equal.
  - f_equal; apply prop_ext; tauto.
  - erewrite <- (field_at_share_join _ _ _ _ _ _ _ Hjoin), <- (lock_inv_share_join _ _ _ _ _ _ _ Hjoin),
      <- (hist_share_join _ _ _ _ _ Hjoin).
    rewrite <- !sepcon_assoc, !sepcon_assoc; f_equal.
    rewrite <- sepcon_assoc, sepcon_comm, sepcon_assoc; f_equal.
    rewrite sepcon_comm, sepcon_assoc; f_equal.
  
    SearchAbout mpred eq derives.
Search (_ /\ _ = _).
SearchAbout and eq.
  normalize.
  rewrite (sepcon_comm (field_at sh2 _ _ _ _)), sepcon_assoc, <- (sepcon_assoc (lock_inv _ _ _)).
  erewrite lock_inv_share_join; eauto.
  rewrite sepcon_comm, sepcon_assoc.
  erewrite field_at_share_join; eauto.
  rewrite sepcon_comm; auto.
Qed.

Lemma lqueue_shares_join : forall sh gsh p ghosts lock shs (Hsplit : forall i, 0 <= i < Zlength shs ->
  let '(a, b) := Znth i shs (sh, sh) in
  readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) shs (sh, sh)))),
  lqueue (fst (Znth 0 shs (sh, sh))) gsh p ghosts lock *
  fold_right sepcon emp (map (fun sh => lqueue sh gsh p ghosts lock) (map snd shs)) =
  lqueue sh gsh p ghosts lock.
Proof.
  induction shs; intros.
  - unfold lqueue.
    rewrite Znth_nil; simpl; normalize.
  - rewrite Znth_0_cons; simpl.
    rewrite Zlength_cons in Hsplit.
    exploit (Hsplit 0).
    { rewrite Zlength_correct; omega. }
    rewrite !Znth_0_cons; destruct a; intros (? & ? & ?).
    erewrite <- sepcon_assoc, lqueue_share_join; simpl; eauto.
    apply IHshs.
    intros; specialize (Hsplit (i + 1)).
    rewrite !Znth_pos_cons, !Z.add_simpl_r in Hsplit; try omega.
    apply Hsplit; omega.
Qed.