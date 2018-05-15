Require Import VST.progs.conclib.
Require Import VST.progs.ghost_queue.
Require Import SetoidList.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makecond_spec := DECLARE _makecond (makecond_spec _).
Definition freecond_spec := DECLARE _freecond (freecond_spec _).
Definition wait_spec := DECLARE _waitcond (wait2_spec _). (* lock invariant includes cond_var *)
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
Definition tqueue := Tstruct _queue noattr.
Definition tqueue_t := Tstruct _queue_t noattr.

(* Axiomatization of ghost variables with allocator *)
(* Could t be a Type instead? *)
Parameter ghost : forall (sh : share) (t : type) (v : reptype t) (p : val), mpred.
Parameter ghost_factory : mpred. (* Could be implemented with an existential, allowing it to change
                                    after each allocation. *)

Axiom ghost_alloc : forall Espec D P Q R C P',
  semax(Espec := Espec) D (PROPx P (LOCALx Q (SEPx (ghost_factory :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx R))) C P'.
Axiom new_ghost : forall Espec D P Q R C P' t v,
  semax(Espec := Espec) D (PROPx P (LOCALx Q (SEPx (ghost_factory ::
    (EX p : val, ghost Ews t v p) :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost_factory :: R)))) C P'.
Axiom alloc_conflict : ghost_factory * ghost_factory |-- FF.

Axiom ghost_share_join : forall sh1 sh2 sh t v p, sepalg.join sh1 sh2 sh ->
  ghost sh1 t v p * ghost sh2 t v p = ghost sh t v p.
Axiom change_ghost : forall Espec D P Q R C P' t v p v',
  semax(Espec := Espec) D (PROPx P (LOCALx Q (SEPx (ghost Ews t v' p :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost Ews t v p :: R)))) C P'.
Parameter Ghost : forall (sh : share) (t : type) (v : reptype t) (p : val), Pred.
Axiom interp_ghost : forall sh t v p, Interp (Ghost sh t v p) = ghost sh t v p.
Axiom ghost_inj : forall sh1 sh2 t v1 v2 p, ghost sh1 t v1 p * ghost sh2 t v2 p
  |-- !!(v1 = v2).
Axiom ghost_conflict : forall sh1 sh2 t1 t2 v1 v2 p,
  ghost sh1 t1 v1 p * ghost sh2 t2 v2 p |-- !!sepalg.joins sh1 sh2.


Definition MAX := 10.

(* Note that a writable share must include all readable shares. *)
Definition lock_pred' sh d reqs head next addc remc ghosts ns := Pred_list (
    Data_at _ Tsh tqueue (rotate (complete MAX (map snd reqs)) head MAX, (vint (Zlength reqs),
                          (vint head, (vint ((head + Zlength reqs) mod MAX), (vint next, (addc, remc)))))) d ::
    Cond_var _ Tsh addc :: Cond_var _ Tsh remc ::
    Pred_prop (Forall (fun t => Int.min_signed <= t < next /\ Forall (fun n => n < t) ns) (map fst reqs) /\
               Int.min_signed <= next <= Int.max_signed /\
               Forall (fun n => Int.min_signed <= n < next) ns /\
               Zlength reqs <= MAX /\ Zlength ns = Zlength ghosts /\ Sorted Z.lt (map fst reqs) /\
               0 <= head < MAX) ::
    map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p)) (combine ns ghosts) ++
    map (fun p => Exp _ (fun d => Data_at _ Tsh trequest (d, Vint (Int.repr (fst p))) (snd p))) reqs).

Definition lock_pred sh d ghosts := Exp _ (fun reqs => Exp _ (fun head =>
  Exp _ (fun next => Exp _ (fun addc => Exp _ (fun remc => Exp _ (fun ns =>
  lock_pred' sh d reqs head next addc remc ghosts ns)))))).

Definition get_request_spec :=
 DECLARE _get_request
  WITH _ : unit
  PRE [ ] PROP () LOCAL () SEP ()
  POST [ tptr trequest ]
    EX v : val, EX d : val, EX t : val,
    PROP ()
    LOCAL (temp ret_temp v)
    SEP (data_at Tsh trequest (d, t) v).

Definition process_request_spec :=
 DECLARE _process_request
  WITH request : val, d : val, t : Z
  PRE [ _request OF (tptr trequest) ]
     PROP ()
     LOCAL (temp _request request)
     SEP (data_at Tsh trequest (d, Vint (Int.repr t)) request)
  POST [ tint ]
    PROP () LOCAL (temp ret_temp (Vint (Int.repr t))) SEP (emp).

Definition lqueue lsh gsh p ghosts lock := field_at lsh tqueue_t [StructField _lock] lock p *
  lock_inv lsh lock (Interp (lock_pred gsh p ghosts)).

Definition q_new_spec :=
 DECLARE _q_new
  WITH sh1 : share, sh2 : share, ghosts : list val
  PRE [ ]
   PROP (sepalg.join sh1 sh2 Ews)
   LOCAL ()
  (SEPx (map (ghost Ews tint (vint (-1))) ghosts))
  POST [ tptr tqueue_t ]
   EX newq : val, EX lock : val,
   PROP () LOCAL (temp ret_temp newq)
   SEP (lqueue Tsh sh2 newq ghosts lock; fold_right_sepcon (map (ghost sh1 tint (vint (-1))) ghosts)).

Definition q_del_spec :=
 DECLARE _q_del
  WITH sh1 : share, sh2 : share, d : val, ghosts : list val, ns : list Z, lock : val
  PRE [ _tgt OF (tptr tqueue_t) ]
   PROP (sepalg.join sh1 sh2 Ews)
   LOCAL (temp _tgt d)
   SEP (lqueue Tsh sh2 d ghosts lock;
        fold_right_sepcon (map (fun p => ghost sh1 tint (vint (fst p)) (snd p)) (combine ns ghosts)))
  POST [ tvoid ]
   PROP () LOCAL ()
   SEP (fold_right_sepcon (map (fun p => ghost Ews tint (vint (fst p)) (snd p)) (combine ns ghosts))).

Definition q_add_spec :=
 DECLARE _q_add
  WITH sh : share, p : val, lock : val, request : val, d : val, t : val,
       ghosts : list val, gsh2 : share
  PRE [ _tgt OF (tptr tqueue_t), _request OF (tptr trequest) ]
   PROP (readable_share sh)
   LOCAL (temp _tgt p; temp _request request)
   SEP (lqueue sh gsh2 p ghosts lock; data_at Tsh trequest (d, t) request)
  POST [ tvoid ]
   PROP () LOCAL ()
   SEP (lqueue sh gsh2 p ghosts lock).

Definition q_remove_spec :=
 DECLARE _q_remove
  WITH sh : share, p : val, lock : val, t : Z, ghosts : list val, i : nat, g : val, gsh1 : share, gsh2 : share
  PRE [ _tgt OF (tptr tqueue_t) ]
   PROP (readable_share sh; Int.min_signed <= t <= Int.max_signed; sepalg.join gsh1 gsh2 Ews;
         nth_error ghosts i = Some g)
   LOCAL (temp _tgt p)
   SEP (lqueue sh gsh2 p ghosts lock; ghost gsh1 tint (Vint (Int.repr t)) g)
  POST [ tptr trequest ]
   EX t' : Z, EX req : val, EX d : val,
   PROP (t < t' <= Int.max_signed)
   LOCAL (temp ret_temp req)
   SEP (lqueue sh gsh2 p ghosts lock; data_at Tsh trequest (d, Vint (Int.repr t')) req;
        ghost gsh1 tint (Vint (Int.repr t')) g).

Definition f_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh2 :=
  Self_lock (Pred_list [Data_at _ gsh (tptr tqueue_t) p p';
    Field_at _ lsh tqueue_t [StructField _lock] lock p;
    Lock_inv lsh lock (lock_pred gsh2 p ghosts)]) tsh lockt.

Definition f_spec :=
 DECLARE _f
  WITH lockt : val, x : share * share * share * val * val * val * list val * share
  PRE [ _arg OF (tptr tvoid) ]
   let '(lsh, gsh, tsh, p', p, lock, ghosts, gsh2) := x in
   PROP ()
   LOCAL (temp _arg lockt; gvar _q0 p')
   SEP (!!(readable_share lsh /\ readable_share gsh /\ readable_share tsh) && emp;
        data_at gsh (tptr tqueue_t) p p';
        lqueue lsh gsh2 p ghosts lock;
        lock_inv tsh lockt (Interp (f_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh2)))
  POST [ tptr tvoid ] PROP () LOCAL () SEP (emp).

Definition g_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh1 gsh2 g :=
  Self_lock (Pred_list [Data_at _ gsh (tptr tqueue_t) p p';
    Field_at _ lsh tqueue_t [StructField _lock] lock p;
    Lock_inv lsh lock (lock_pred gsh2 p ghosts);
    Exp _ (fun n => Ghost gsh1 tint (Vint (Int.repr n)) g)]) tsh lockt.

Definition g_spec :=
 DECLARE _g
  WITH lockt : val, x : share * share * share * Z * val * val * val * list val * nat * val * share * share
  PRE [ _arg OF (tptr tvoid) ]
   let '(lsh, gsh, tsh, t, p', p, lock, ghosts, i, g, gsh1, gsh2) := x in
   PROP ()
   LOCAL (temp _arg lockt; gvar _q0 p')
   SEP (!!(readable_share lsh /\ readable_share gsh /\ readable_share tsh /\
           Int.min_signed <= t <= Int.max_signed /\ sepalg.join gsh1 gsh2 Ews /\ nth_error ghosts i = Some g) && emp;
        data_at gsh (tptr tqueue_t) p p';
        lqueue lsh gsh2 p ghosts lock;
        lock_inv tsh lockt (Interp (g_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh1 gsh2 g));
        ghost gsh1 tint (Vint (Int.repr t)) g)
  POST [ tptr tvoid ] PROP () LOCAL () SEP (emp).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog [] u
  POST [ tint ] main_post prog [] u.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; makecond_spec; freecond_spec; wait_spec; signal_spec;
  malloc_spec; free_spec; get_request_spec; process_request_spec;
  q_new_spec; q_del_spec; q_add_spec; q_remove_spec; f_spec; g_spec; main_spec]).

Lemma all_ptrs : forall reqs,
  fold_right_sepcon (map Interp (map (fun p => Exp val (fun d =>
    Data_at _ Tsh trequest (d, Vint (Int.repr (fst p))) (snd p))) reqs)) |--
  !!(Forall isptr (map snd reqs)).
Proof.
  induction reqs; simpl; intros; entailer.
  rewrite data_at_isptr.
  eapply derives_trans; [apply saturate_aux20|].
  { apply andp_left1, derives_refl. }
  { apply IHreqs; auto. }
  normalize.
Qed.

Lemma precise_request : forall sh p, readable_share sh ->
  precise (data_at_ sh trequest p).
Proof.
  intros; unfold data_at_, field_at_; unfold_field_at 1%nat.
  unfold field_at, at_offset; simpl.
  apply precise_sepcon; apply precise_andp2; rewrite by_value_data_at_rec_nonvolatile; auto.
Qed.

Lemma reqs_precise : forall r reqs ns1 ns2 r1 r2
  (Hreqs1 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap) (fold_right_sepcon
    (map Interp (map (fun p => Exp _ (fun d => Data_at _ Tsh trequest (d, Vint (Int.repr (fst p))) (snd p)))
    (combine ns1 reqs)))) r1)
  (Hreqs2 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap) (fold_right_sepcon
    (map Interp (map (fun p => Exp _ (fun d => Data_at _ Tsh trequest (d, Vint (Int.repr (fst p))) (snd p)))
    (combine ns2 reqs)))) r2)
  (Hlen1 : length ns1 = length reqs) (Hlen2 : length ns2 = length reqs)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r), r1 = r2.
Proof.
  induction reqs; destruct ns1, ns2; try discriminate; simpl; intros.
  - apply sepalg.same_identity with (a := r); auto.
    { destruct Hr1 as (? & H); specialize (Hreqs1 _ _ H); subst; auto. }
    { destruct Hr2 as (? & H); specialize (Hreqs2 _ _ H); subst; auto. }
  - inv Hlen1; inv Hlen2.
    destruct Hreqs1 as (r1a & r1b & ? & (? & Hh1) & ?), Hreqs2 as (r2a & r2b & ? & (? & Hh2) & ?).
    assert (r1a = r2a); [|subst].
    { apply data_at_data_at_ in Hh1; apply data_at_data_at_ in Hh2.
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
  (Hghosts1 : predicates_hered.app_pred (fold_right_sepcon
    (map Interp (map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p))
    (combine ns1 ghosts)))) r1)
  (Hghosts2 : predicates_hered.app_pred (fold_right_sepcon
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
Qed.

Lemma tqueue_inj : forall r buf1 buf2 len1 len2 head1 head2 tail1 tail2 next1 next2 addc1 addc2 remc1 remc2
  p r1 r2
  (Hp1 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap)
     (data_at Tsh tqueue (buf1, (vint len1, (vint head1, (vint tail1, (vint next1, (addc1, remc1)))))) p) r1)
  (Hp2 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap)
     (data_at Tsh tqueue (buf2, (vint len2, (vint head2, (vint tail2, (vint next2, (addc2, remc2)))))) p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r)
  (Hbuf1 : Forall (fun v => v <> Vundef) buf1) (Hl1 : Zlength buf1 = MAX)
  (Hbuf2 : Forall (fun v => v <> Vundef) buf2) (Hl2 : Zlength buf2 = MAX)
  (Haddc1 : addc1 <> Vundef) (Haddc2 : addc2 <> Vundef) (Hremc1 : remc1 <> Vundef) (Hremc2 : remc2 <> Vundef),
  r1 = r2 /\ buf1 = buf2 /\ Int.repr len1 = Int.repr len2 /\ Int.repr head1 = Int.repr head2 /\
  Int.repr tail1 = Int.repr tail2 /\ Int.repr next1 = Int.repr next2 /\ addc1 = addc2 /\ remc1 = remc2.
Proof.
  intros.
  destruct Hp1 as (? & ? & ? & ? & Hb1 & ? & ? & ? & Hlen1 & ? & ? & ? & Hhead1 & ? & ? & ? & Htail1 & ? & ? &
    ? & Hnext1 & ? & ? & ? & Hadd1 & Hrem1); unfold withspacer, at_offset, eq_rect_r in *; simpl in *.
  destruct Hp2 as (? & ? & ? & ? & Hb2 & ? & ? & ? & Hlen2 & ? & ? & ? & Hhead2 & ? & ? & ? & Htail2 & ? & ? &
    ? & Hnext2 & ? & ? & ? & Hadd2 & Hrem2); unfold withspacer, at_offset, eq_rect_r in *; simpl in *.
  assert (readable_share Tsh) as Hread by auto.
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Hrem1 Hrem2); auto.
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Hadd1 Hadd2); auto.
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  exploit (mapsto_inj _ _ _ _ _ _ _ r Hread Hnext1 Hnext2); auto.
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { repeat (eapply sepalg.join_sub_trans; [eexists|]; eauto). }
  { discriminate. }
  { discriminate. }
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

Lemma inv_precise : forall sh d ghosts, precise (Interp (lock_pred sh d ghosts)).
Proof.
  intros ?????? H1 H2 Hw1 Hw2; simpl in *.
  destruct H1 as (reqs1 & head1 & next1 & addc1 & remc1 & ns1 & ? & ? & ? & Hq1 &
    ? & ? & ? & Haddc1 & ? & ? & ? & Hremc1 & ? & ? & ? & ((? & ? & ? & ? & ? & ? & ? & ?) & Hemp1) & Hreqs1),
  H2 as (reqs2 & head2 & next2 & addc2 & remc2 & ns2 & ? & ? & ? & Hq2 &
    ? & ? & ? & Haddc2 & ? & ? & ? & Hremc2 & ? & ? & ? & ((? & ? & ? & ? & ? & ? & ? & ?) & Hemp2) & Hreqs2).
  rewrite map_app, sepcon_app in Hreqs1; destruct Hreqs1 as (? & ? & ? &
    Hghosts1 & Hreqs1).
  rewrite map_app, sepcon_app in Hreqs2; destruct Hreqs2 as (? & ? & ? &
    Hghosts2 & Hreqs2).
  pose proof (all_ptrs _ _ Hreqs1) as Hptrs1.
  pose proof (all_ptrs _ _ Hreqs2) as Hptrs2.
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

Lemma inv_positive : forall sh d ghosts, positive_mpred (Interp (lock_pred sh d ghosts)).
Proof.
  intros; simpl.
  repeat (apply ex_positive; intro).
  apply positive_sepcon2, positive_sepcon1; auto.
Qed.

Lemma nth_ghost : forall sh i ns ghosts g (Hlen : length ns = length ghosts)
  (Hg : nth_error ghosts i = Some g), exists n, nth_error ns i = Some n /\
  fold_right_sepcon (map Interp (map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p))
    (combine ns ghosts))) =
  fold_right_sepcon (map Interp (map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p))
    (combine (remove_at i ns) (remove_at i ghosts)))) * ghost sh tint (Vint (Int.repr n)) g.
Proof.
  induction i; simpl; intros.
  - destruct ghosts; inv Hg.
    destruct ns; [discriminate|].
    eexists; split; eauto; unfold remove_at; simpl.
    rewrite interp_ghost, sepcon_comm; auto.
  - destruct ghosts; [discriminate|].
    destruct ns; [discriminate|].
    inversion Hlen as [Hlen'].
    specialize (IHi _ _ _ Hlen' Hg); destruct IHi as (n & Hn & Heq).
    exists n; split; auto; unfold remove_at; simpl.
    rewrite Heq, sepcon_assoc; auto.
Qed.

Lemma add_nth_ghost : forall sh i ns ghosts g n (Hlen : length ns = length ghosts)
  (Hg : nth_error ghosts i = Some g),
  fold_right_sepcon (map Interp (map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p))
    (combine (remove_at i ns) (remove_at i ghosts)))) * ghost sh tint (Vint (Int.repr n)) g =
  fold_right_sepcon (map Interp (map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p))
    (combine (upd_Znth (Z.of_nat i) ns n) ghosts))).
Proof.
  induction i; intros.
  - destruct ghosts; inv Hg.
    destruct ns; [discriminate|].
    unfold remove_at; simpl.
    rewrite sublist_1_cons, Zlength_cons, sublist_same; auto; [|omega].
    rewrite interp_ghost, sepcon_comm; auto.
  - destruct ghosts; [discriminate|].
    destruct ns; [discriminate|].
    inversion Hlen as [Hlen'].
    rewrite Nat2Z.inj_succ, upd_Znth_cons; [|omega].
    unfold Z.succ; rewrite Z.add_simpl_r.
    unfold remove_at; simpl.
    rewrite sepcon_assoc; setoid_rewrite IHi; auto.
Qed.

Lemma body_get_request : semax_body Vprog Gprog f_get_request get_request_spec.
Proof.
  start_function.
  forward_call (sizeof trequest).
  { simpl; computable. }
  Intro p; Intros.
  rewrite memory_block_data_at_; [|apply malloc_field_compatible; auto; simpl; try computable].
  forward.
  forward.
  Exists p (Vint (Int.repr 1)) Vundef; entailer.
  { exists 2; auto. }
Qed.

Lemma body_process_request : semax_body Vprog Gprog f_process_request process_request_spec.
Proof.
  start_function.
  forward.
  forward_call (request, sizeof trequest).
  { subst Frame; instantiate (1 := []); normalize.
    apply data_at_memory_block. }
  forward.
Qed.

Lemma split_queue_t : forall (buf : list val) (len head tail next addc remc lock p : val) sh1 sh2
  (Hjoin : sepalg.join sh1 sh2 Tsh),
  data_at Tsh tqueue (buf, (len, (head, (tail, (next, (addc, remc)))))) p *
  field_at sh1 tqueue_t [StructField _lock] lock p =
  data_at sh1 tqueue_t (buf, (len, (head, (tail, (next, (addc, remc))))), lock) p *
  data_at sh2 tqueue (buf, (len, (head, (tail, (next, (addc, remc)))))) p.
Proof.
  intros.
  rewrite <- (data_at_share_join _ _ _ _ _ _ Hjoin).
  rewrite (sepcon_comm (data_at _ _ _ _)), sepcon_assoc, sepcon_comm; f_equal.
  unfold data_at at 2, field_at at 2; unfold at_offset.
  rewrite data_at_rec_eq; unfold withspacer, at_offset; simpl.
  unfold data_at, field_at, at_offset; simpl.
  rewrite sepcon_andp_prop', sepcon_andp_prop.
  rewrite <- andp_assoc, <- prop_and.
  destruct p; try (repeat rewrite prop_false_andp; auto; try intros ((? & ?) & ?); try intros (? & ?);
    contradiction).
  repeat rewrite offset_val_zero_Vptr.
  do 2 f_equal.
  apply prop_ext; split; unfold field_compatible; intro; decompose [and] H; repeat split; auto; simpl in *.
  - omega.
  - unfold in_members; simpl; auto.
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
  assert (field_compatible tqueue [] p /\ field_compatible (tptr tlock) [] (offset_val 64 p)) as (? & ?).
  { unfold field_compatible in *; repeat match goal with H : _ /\ _ |- _ => destruct H end.
    destruct p as [| | | | | b o]; try contradiction.
    assert (Int.unsigned (Int.add o (Int.repr 64)) = Int.unsigned o + 64) as Ho.
    { rewrite Int.unsigned_add_carry.
      unfold Int.add_carry.
      rewrite Int.unsigned_repr, Int.unsigned_zero; [|computable].
      destruct (zlt _ Int.modulus); simpl in *; omega. }
    repeat split; auto; simpl in *; try omega.
    rewrite Ho; unfold align_attr in *; simpl in *.
    apply Z.divide_add_r; auto.
    exists 16; auto. }
  forward_for_simple_bound MAX (EX i : Z, PROP () LOCAL (temp _q p; temp _newq p)
    SEP (@data_at CompSpecs Tsh tqueue (repeat (vint 0) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (MAX - i)),
           (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef)))))) p;
         @data_at_ CompSpecs Tsh (tptr tlock) (offset_val 64 p);
         fold_right_sepcon (map (ghost Ews tint (vint (-1))) ghosts))).
  { unfold MAX; computable. }
  { unfold MAX; computable. }
  { unfold fold_right; entailer!.
    unfold data_at_, field_at_; unfold_field_at 1%nat; simpl.
    unfold data_at, field_at, at_offset; simpl; entailer. }
  { forward.
    (*time entailer. XX This takes 88s, although it is a simple formula. *)
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
  forward.
  forward_call (sizeof tint).
  { simpl; cancel. }
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
  { simpl; computable. }
  Intro lock; Intros.
  rewrite memory_block_data_at_; [|apply malloc_field_compatible; auto; simpl; try computable].
  forward_call (lock, Tsh, lock_pred sh2 p ghosts).
  eapply semax_pre with (P' := PROP () LOCAL (temp _l lock; temp _c remc; temp _i (vint MAX);
      temp _q p; temp _newq p)
    SEP (lock_inv Tsh lock (Interp (lock_pred sh2 p ghosts)); cond_var Tsh remc; cond_var Tsh addc;
         @data_at CompSpecs Tsh tqueue_t (repeat (vint 0) (Z.to_nat MAX),
           (vint 0, (vint 0, (vint 0, (vint 0, (addc, remc))))), Vundef) p;
         fold_right_sepcon (map (ghost Ews tint (vint (-1))) ghosts))).
  { go_lower.
    do 2 (apply andp_right; [apply prop_right; repeat split; auto|]); unfold fold_right; cancel.
    unfold_data_at 1%nat.
    unfold data_at_, field_at_, field_at, at_offset; simpl.
    destruct addc; try contradiction.
    destruct remc; try contradiction; simpl.
    rewrite !field_compatible_cons; simpl; normalize.
    apply andp_right; [apply prop_right; unfold in_members; simpl; split; [|split; [|split]]; auto|].
    simple apply derives_refl. }
  forward.
  forward_call (lock, Tsh, lock_pred sh2 p ghosts).
  { simpl; cancel.
    Exists ([] : list (Z * val)) 0 0 addc remc (repeat (-1) (length ghosts)).
    rewrite Zlength_nil; simpl; cancel.
    normalize.
    apply andp_right; [apply prop_right|].
    { repeat split; auto; unfold MAX; try omega; try computable.
      - apply Forall_repeat; computable.
      - rewrite Zlength_repeat, Zlength_correct; auto. }
    rewrite sepcon_assoc, (sepcon_comm _ (fold_right_sepcon Frame)), <- sepcon_assoc.
    rewrite app_nil_r.
    subst Frame; instantiate (1 := field_at Tsh tqueue_t [StructField _lock] lock p ::
      map (ghost sh1 tint (vint (-1))) ghosts); simpl.
    do 2 rewrite sepcon_assoc; rewrite <- sepcon_assoc.
    apply sepcon_derives.
    - unfold_field_at 1%nat.
      unfold data_at, field_at; simpl.
      destruct lock; try contradiction; simpl.
      rewrite field_compatible_cons; simpl; entailer.
    - clear - SH; induction ghosts; simpl; [cancel|].
      rewrite sepcon_assoc, (sepcon_comm (fold_right _ _ _)).
      rewrite sepcon_assoc, <- sepcon_assoc; apply sepcon_derives; [|rewrite sepcon_comm; auto].
      repeat rewrite interp_ghost; erewrite ghost_share_join; eauto. }
  { split; auto; split; [apply inv_precise | apply inv_positive]. }
  forward.
  Exists p lock; Intros.
  apply andp_right; [apply prop_right; auto|].
  unfold lqueue; simpl; entailer!.
Qed.

Lemma body_q_del : semax_body Vprog Gprog f_q_del q_del_spec.
Proof.
  start_function.
  unfold lqueue; rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (lock, Tsh, lock_pred sh2 d ghosts).
  { simpl; cancel. }
  forward_call (lock, Tsh, lock_pred sh2 d ghosts).
  { split; auto; apply inv_positive. }
  forward_call (lock, sizeof tlock).
  { repeat rewrite sepcon_assoc; apply sepcon_derives; [apply data_at__memory_block_cancel | cancel]. }
  forward.
  simpl; Intros reqs head next addc remc ns'.
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
  (* We actually need to know that the queue is empty, but that would require more ghost state.
     Admitting for now. *)
(*  eapply semax_pre with (P' := PROP () LOCAL (temp _c remc; temp _q d; temp _l lock; temp _tgt d)
    SEP (data_at_ Tsh tqueue_t p; lock_inv Tsh lock (Interp (lock_pred sh2 p ghosts)); cond_var Tsh remc; cond_var Tsh addc;
         @data_at CompSpecs Tsh tqueue_t (repeat (vint 0) (Z.to_nat MAX),
           (vint 0, (vint 0, (vint 0, (vint 0, (addc, remc))))), Vundef) p;
         fold_right_sepcon (map (ghost Ews tint (vint (-1))) ghosts))).
  { go_lower.
    do 2 (apply andp_right; [apply prop_right; repeat split; auto|]); unfold fold_right; cancel.
    unfold data_at_, field_at_, data_at, field_at; Intros; simpl.
    rewrite (data_at_rec_eq _ tqueue_t); unfold withspacer, at_offset; simpl.
    repeat (rewrite isptr_offset_val_zero; [|auto]).
    destruct addc; try contradiction.
    destruct remc; try contradiction; simpl.
    simple apply derives_refl. }

  forward_call (d, sizeof tqueue_t).
  { repeat rewrite sepcon_assoc; apply sepcon_derives; [apply data_at_memory_block | cancel]. }
  forward.
  clear - SH; induction ns; simpl; auto.*)
Admitted.

Lemma body_q_add : semax_body Vprog Gprog f_q_add q_add_spec.
Proof.
  start_function.
  unfold lqueue; rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (lock, sh, lock_pred gsh2 p ghosts).
  simpl; Intros reqs head next addc remc ns.
  forward.
  rewrite data_at_isptr; Intros; rewrite isptr_offset_val_zero; auto.
  forward.
  forward_while (EX reqs : list (Z * val), EX head : Z, EX next : Z, EX addc : val, EX remc : val,
    EX ns : list Z, PROP ()
   LOCAL (temp _len (vint (Zlength reqs)); temp _q p; temp _l lock; temp _tgt p; temp _request request)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 p ghosts));
        Interp (lock_pred' gsh2 p reqs head next addc remc ghosts ns);
        @field_at CompSpecs sh tqueue_t [StructField _lock] lock p;
        @data_at CompSpecs Tsh trequest (d, t) request)).
  { Exists reqs head next addc remc ns.
    simpl Interp.
    (*timeout 70 entailer. XX times out *)
    go_lower.
    repeat (apply andp_right; [apply prop_right; repeat split; auto|]).
    unfold fold_right, app; cancel.
    apply andp_right; [apply prop_right; repeat split; auto; omega | cancel]. }
  { go_lower; entailer'. }
  { simpl; Intros.
    forward.
    { go_lower.
      rewrite cond_var_isptr; Intros; entailer'. }
    forward_call (addc0, lock, Tsh, sh, lock_pred gsh2 p ghosts).
    { simpl.
      Exists reqs0 head0 next0 addc0 remc0 ns0; cancel.
      subst Frame; instantiate (1 := [field_at sh tqueue_t [StructField _lock] lock p;
        data_at Tsh trequest (d, t) request]); simpl; cancel.
      repeat rewrite sepcon_assoc; repeat (apply sepcon_derives; [apply derives_refl|]).
      apply andp_right; [Intros; cancel | cancel].
      apply andp_right; [apply prop_right; repeat split; auto; omega | apply derives_refl]. }
    simpl; Intros reqs1 head1 next1 addc1 remc1 ns1.
    forward.
    Exists (reqs1, head1, next1, addc1, remc1, ns1).
    (* timeout 70 entailer. XX times out *)
    go_lower.
    apply andp_right; [apply prop_right; repeat split; auto |
      apply andp_right; [apply prop_right; repeat split; auto | entailer!]]. }
  simpl; Intros.
  rewrite Int.signed_repr, Zlength_correct in HRE.
  freeze [0; 2; 3; 5; 6] FR; forward.
  forward.
  forward.
  forward.
  exploit (Z_mod_lt (head0 + Zlength reqs0) MAX); [omega | intro].
  forward.
  forward.
  { go_lower.
    repeat apply andp_right; apply prop_right; auto.
    rewrite andb_false_intro2; simpl; auto. }
  forward.
  thaw FR.
  rewrite (cond_var_isptr _ remc0); Intros.
  forward.
  freeze [0; 1; 3; 4; 5; 6] FR; forward_call (remc0, Tsh).
  thaw FR.
  rewrite upd_rotate; auto; try rewrite Zlength_complete; try rewrite Zlength_map; auto.
  rewrite Zminus_mod_idemp_l, Z.add_simpl_l, (Zmod_small (Zlength reqs0));
    [|rewrite Zlength_correct; unfold MAX; omega].
  erewrite <- Zlength_map, upd_complete; [|rewrite Zlength_map, Zlength_correct; auto].
  time forward_call (lock, sh, lock_pred gsh2 p ghosts). (* 29s *)
  { simpl.
    Exists (reqs0 ++ [(next0, request)]) head0 (next0 + 1) addc0 remc0 ns0; unfold fold_right at 1; cancel.
    rewrite (field_at_isptr _ trequest); Intros.
    rewrite map_app, Zlength_app, Zlength_cons, Zlength_nil, Zlength_map.
    unfold sem_mod; simpl sem_binarith.
    unfold both_int; simpl force_val.
    rewrite andb_false_intro2; [|simpl; auto].
    simpl force_val.
    rewrite !add_repr, mods_repr; try computable.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    simpl.
    apply andp_right; [apply prop_right|].
    { repeat split; auto; try omega.
      - rewrite map_app, Forall_app; split.
        + eapply Forall_impl; [|eauto].
          intros ? (? & ?); split; auto; omega.
        + constructor; auto; simpl.
          repeat split; auto; try omega.
          eapply Forall_impl; [|eauto]; intros ? (? & ?); auto.
      - admit. (* Here's where we need to watch for overflow. *)
      - eapply Forall_impl; [|eauto]; intros; simpl in *; omega.
      - rewrite Zlength_correct; unfold MAX; omega.
      - rewrite map_app; apply SortA_app with (eqA := eq); auto.
        + repeat constructor; repeat intro; subst; auto.
        + simpl; constructor; auto.
        + intros ?? Hin Hn; inversion Hn; [|rewrite SetoidList.InA_nil in *; contradiction]; subst.
          rewrite SetoidList.InA_alt in Hin; destruct Hin as (? & ? & Hin); subst.
          match goal with H : Forall _ _ |- _ => rewrite Forall_forall in H; specialize (H _ Hin) end; omega. }
    rewrite Zplus_mod_idemp_l, Z.add_assoc.
    repeat rewrite map_app; repeat rewrite sepcon_app; simpl.
    Exists d; entailer!.
    { pose proof (Z_mod_lt (head0 + Zlength reqs0) MAX).
      split; try omega.
      transitivity MAX; simpl in *; [omega | unfold MAX; computable]. } }
  { split; auto; split; [apply inv_precise | apply inv_positive]. }
  forward.
  { unfold lqueue; simpl; cancel. }
  { pose proof Int.min_signed_neg; split; [rewrite Zlength_correct; omega|].
    transitivity MAX; [auto | unfold MAX; computable]. }
Admitted.

Lemma body_q_remove : semax_body Vprog Gprog f_q_remove q_remove_spec.
Proof.
  start_function.
  unfold lqueue; rewrite lock_inv_isptr; Intros.
  forward.
  forward_call (lock, sh, lock_pred gsh2 p ghosts).
  simpl; Intros reqs head next addc remc ns.
  forward.
  rewrite data_at_isptr; Intros; rewrite isptr_offset_val_zero; auto.
  forward.
  forward_while (EX reqs : list (Z * val), EX head : Z, EX next : Z, EX addc : val, EX remc : val,
    EX ns : list Z, PROP ()
   LOCAL (temp _len (vint (Zlength reqs)); temp _q p; temp _l lock; temp _tgt p)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 p ghosts));
        Interp (lock_pred' gsh2 p reqs head next addc remc ghosts ns);
        @field_at CompSpecs sh tqueue_t [StructField _lock] lock p; ghost gsh1 tint (Vint (Int.repr t)) g)).
  { Exists reqs head next addc remc ns; go_lower.
    apply andp_right; [apply prop_right; repeat split; auto |
      apply andp_right; [apply prop_right; repeat split; auto | entailer!]]. }
  { go_lower; entailer'. }
  { simpl; Intros.
    forward.
    { go_lower.
      rewrite (cond_var_isptr _ remc0); Intros; entailer'. }
    forward_call (remc0, lock, Tsh, sh, lock_pred gsh2 p ghosts).
    { simpl.
      Exists reqs0 head0 next0 addc0 remc0 ns0; cancel.
      subst Frame; instantiate (1 := [field_at sh tqueue_t [StructField _lock] lock p;
        ghost gsh1 tint (Vint (Int.repr t)) g]); simpl; cancel.
      repeat rewrite sepcon_assoc; repeat (apply sepcon_derives; [apply derives_refl|]).
      apply andp_right; [Intros; entailer! | entailer!]. }
    simpl; Intros reqs1 head1 next1 addc1 remc1 ns1; Intros.
    forward.
    Exists (reqs1, head1, next1, addc1, remc1, ns1).
    go_lower.
    apply andp_right; [apply prop_right; repeat split; auto |
      apply andp_right; [apply prop_right; repeat split; auto | entailer!]]. }
  simpl; Intros.
  assert (Zlength reqs0 > 0).
  { rewrite Zlength_correct in *.
    destruct (length reqs0); [|rewrite Nat2Z.inj_succ; omega].
    contradiction HRE; auto. }
  forward.
  forward.
  { go_lower; Intros.
    rewrite Znth_head; try rewrite Zlength_map; try omega.
    repeat rewrite <- sepcon_assoc.
    rewrite (sepcon_comm _ (_ (map _ _))).
    rewrite map_app, sepcon_app.
    repeat rewrite sepcon_assoc; rewrite sepcon_comm.
    rewrite sepcon_assoc.
    eapply derives_trans; [apply sepcon_derives; [apply prop_and_same_derives, all_ptrs; auto |
      apply derives_refl]|].
    Intros; apply prop_right.
    apply Forall_Znth.
    { rewrite Zlength_map; omega. }
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
  freeze [0; 1; 3; 4; 5] FR; forward_call (addc0, Tsh).
  thaw FR.
  rewrite upd_rotate; try rewrite Zlength_complete; auto; try rewrite Zlength_map; auto.
  rewrite Zminus_diag, Zmod_0_l.
  destruct reqs0; [contradiction HRE; auto|].
  rewrite Zlength_cons in *.
  simpl; rewrite rotate_1; try rewrite Zlength_map; try omega.
  unfold sem_mod; simpl sem_binarith.
  unfold both_int; simpl force_val.
  rewrite andb_false_intro2; [|simpl; auto].
  simpl force_val.
  rewrite !add_repr, mods_repr; try computable.
  rewrite map_app, sepcon_app; simpl.
  Intro d.
  assert (i < length ghosts)%nat as Hlt by (rewrite <- nth_error_Some; intro X; rewrite X in *; discriminate).
  assert (length ns0 = length ghosts) as Hlen by (repeat rewrite Zlength_correct in *; Omega0).
  replace (length ghosts) with (length ns0) in Hlt; auto.
  freeze [0; 1; 2; 3; 5; 6; 7] FR.
  exploit nth_ghost; eauto; intros (n2 & Hn2 & Heq); rewrite Heq.
  simpl in *; match goal with H : Forall _ (_ :: _) |- _ => inv H end.
  eapply semax_pre with (P' := PROP (t < fst p0 <= Int.max_signed)
   LOCAL (temp _r (Znth head0 (rotate (complete MAX (snd p0 :: map snd reqs0)) head0 MAX) Vundef);
     temp _h (vint head0); temp _len (vint (Zlength reqs0 + 1)); temp _q p; temp _l lock; temp _tgt p)
     (SEPx [_; _])).
  { go_lower.
    pose proof (nth_error_In _ _ Hn2) as Hin.
    match goal with X : Forall _ _ |- _ => rewrite Forall_forall in X; specialize (X _ Hin) end.
    do 2 rewrite <- sepcon_assoc.
    rewrite (sepcon_assoc _ (ghost _ _ _ _)).
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl|]|].
    { apply prop_and_same_derives, ghost_inj. }
    rewrite sepcon_andp_prop; apply derives_extract_prop; intro.
    assert (n2 = t).
    { rewrite <- (Int.signed_repr n2), <- (Int.signed_repr t); try omega; congruence. }
    subst; erewrite ghost_share_join; [|eauto].
    apply andp_right; [apply prop_right; split; auto; split; try omega|].
    { match goal with X : _ /\ Forall _ ns0 |- _ => destruct X as (? & X); rewrite Forall_forall in X;
        specialize (X _ Hin); auto end. }
    apply andp_right; [apply prop_right; repeat split; auto|].
    rewrite sepcon_comm; apply derives_refl. }
  Intros.
  apply change_ghost with (v' := Vint (Int.repr (fst p0))).
  erewrite <- ghost_share_join; eauto.
  thaw FR.
  forward_call (lock, sh, lock_pred gsh2 p ghosts).
  { simpl.
    Exists reqs0 ((head0 + 1) mod MAX) next0 addc0 remc0 (upd_Znth (Z.of_nat i) ns0 (fst p0)).
    normalize.
    apply andp_right; [apply prop_right|].
    { match goal with H : Sorted _ _ |- _ => inv H end.
      split; [|split; [|split; [|split; [|split; [|split]]]]]; auto; try omega.
      - rewrite Forall_forall in *; intros ? Hin.
        match goal with H : forall _, _ -> _ /\ _ |- _ => specialize (H _ Hin); destruct H; split; auto end.
        apply Forall_upd_Znth; auto.
        rewrite SetoidList.InfA_alt with (eqA := eq) in *; auto.
        match goal with H : forall _, _ -> _ |- _ => apply H end.
        rewrite SetoidList.InA_alt; eauto.
        { constructor; repeat intro; subst; auto. }
        { constructor; repeat intro; omega. }
        { repeat intro; omega. }
      - apply Forall_upd_Znth; auto; omega.
      - rewrite upd_Znth_Zlength; auto.
        rewrite Zlength_correct; Omega0.
      - apply Z_mod_lt; omega. }
    unfold Z.succ; rewrite Z.add_simpl_r.
    unfold fold_right at 1; cancel.
    rewrite (sepcon_comm (ghost _ _ _ _)), sepcon_comm.
    repeat rewrite <- sepcon_assoc.
    rewrite add_nth_ghost; auto.
    rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm 1).
    simpl; rewrite map_app, sepcon_app; unfold fold_right at 3; cancel. }
  { split; auto; split; [apply inv_precise | apply inv_positive]. }
  forward.
  Exists (fst p0) (snd p0) d; Intros.
  apply andp_right; [apply prop_right | unfold lqueue; simpl; cancel].
  repeat split; auto; try omega.
  rewrite Znth_head; auto; try (rewrite Zlength_cons, Zlength_map; omega).
  entailer!.
  { split; try omega.
    transitivity MAX; [omega | unfold MAX; computable]. }
Qed.

Opaque lock_pred.

Lemma lock_precise : forall sh p lock (Hsh : readable_share sh),
  precise (field_at sh tqueue_t [StructField _lock] lock p).
Proof.
  intros.
  unfold field_at, at_offset; apply precise_andp2.
  rewrite data_at_rec_eq; simpl; auto.
Qed.

Lemma f_inv_precise : forall lsh gsh tsh p' p lock lockt ghosts gsh2 (Hlsh : readable_share lsh)
  (Hgsh : readable_share gsh),
  precise (Interp (f_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh2)).
Proof.
  intros; simpl.
  apply selflock_precise; repeat apply precise_sepcon; auto.
  apply lock_precise; auto.
Qed.

Lemma f_inv_positive : forall lsh gsh tsh p' p lock lockt ghosts gsh2,
  positive_mpred (Interp (f_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh2)).
Proof.
  intros; apply selflock_positive.
  simpl; apply positive_sepcon2, positive_sepcon2, positive_sepcon1, lock_inv_positive.
Qed.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  rewrite (lock_inv_isptr _ lockt); Intros.
  unfold lqueue; rewrite field_at_isptr; Intros.
  forward.
  match goal with |-semax _ ?P _ _ => forward_for_simple_bound 3 (EX i : Z, P) end.
  { entailer. }
  { forward_call tt.
    Intro x; destruct x as ((req, d), t).
    forward_call (lsh, p, lock, req, d, t, ghosts, gsh2).
    { unfold lqueue; cancel. }
    unfold lqueue; entailer!. }
  forward_call (lockt, tsh, f_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh2).
  { simpl.
    rewrite selflock_eq at 2; cancel.
    subst Frame; instantiate (1 := []); normalize; apply lock_inv_later. }
  { split; auto; repeat split; [apply f_inv_precise | apply f_inv_positive | apply selflock_rec]; auto. }
  forward.
Qed.

Lemma g_inv_precise : forall lsh gsh tsh p' p lock lockt ghosts gsh1 gsh2 g
  (Hlsh : readable_share lsh) (Hgsh : readable_share gsh),
  precise (Interp (g_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh1 gsh2 g)).
Proof.
  intros; simpl.
  apply selflock_precise; repeat apply precise_sepcon; auto.
  - apply lock_precise; auto.
  - eapply derives_precise; [|apply ghost_precise].
    intros ? (? & ?).
    rewrite interp_ghost in *; eexists; eauto.
Qed.

Lemma g_inv_positive : forall lsh gsh tsh p' p lock lockt ghosts gsh1 gsh2 g,
  positive_mpred (Interp (g_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh1 gsh2 g)).
Proof.
  intros; apply selflock_positive.
  simpl; apply positive_sepcon2, positive_sepcon2, positive_sepcon1, lock_inv_positive.
Qed.

Lemma body_g : semax_body Vprog Gprog f_g g_spec.
Proof.
  start_function.
  rewrite (lock_inv_isptr _ lockt); Intros.
  unfold lqueue; rewrite field_at_isptr; Intros.
  forward.
  forward_for_simple_bound 3 (EX i : Z, PROP ()
      LOCAL (temp _q1 p; lvar _res (tarray tint 3) lvar0; temp _arg lockt; gvar _q0 p')
      SEP (EX n' : Z, EX ld : list Z, !! (Int.min_signed <= n' <= Int.max_signed /\
             Zlength ld = i /\ Sorted Z.lt ld /\ Forall (fun z => Int.min_signed <= z <= n') ld) &&
             data_at Tsh (tarray tint 3) (map Vint (map Int.repr ld) ++ repeat Vundef (3 - length ld)%nat) lvar0 *
             ghost gsh1 tint (Vint (Int.repr n')) g;
           @field_at CompSpecs lsh tqueue_t [StructField _lock] lock p; lock_inv lsh lock (Interp (lock_pred gsh2 p ghosts));
           @data_at CompSpecs gsh (tptr tqueue_t) p p';
           lock_inv tsh lockt (Interp (g_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh1 gsh2 g)))).
  { entailer.
    Exists t ([] : list Z); simpl; entailer!.
    unfold data_at_, data_at, field_at_; simpl; apply derives_refl. }
  { Intros n1 ld; Intros.
    forward_call (lsh, p, lock, n1, ghosts, i, g, gsh1, gsh2).
    { unfold lqueue; cancel. }
    Intro x; destruct x as ((t', req), d); simpl fst; simpl snd.
    forward_call (req, d, t').
    Intro v.
    forward.
    subst; simpl force_val.
    rewrite upd_complete'; [|rewrite Zlength_correct in *; omega].
    entailer.
    Exists t' (ld ++ [t']); unfold lqueue; entailer!.
    rewrite Zlength_app, Zlength_cons, Zlength_nil; simpl in *; split; [omega|]; split.
    - apply SetoidList.SortA_app with (eqA := eq); auto; intros.
      { repeat constructor; repeat intro; subst; auto. }
      rewrite SetoidList.InA_alt in *;
        repeat match goal with H : exists _, _ |- _ => destruct H as (? & ? & ?); subst end.
      match goal with H : In _ [_] |- _ => destruct H; [subst | contradiction] end.
      match goal with H : In _ _, H' : Forall _ _ |- _ => rewrite Forall_forall in H';
        specialize (H' _ H); omega end.
    - rewrite Forall_app; split; [|constructor; auto; omega].
      eapply Forall_impl; [|eauto]; intros; simpl in *; omega. }
  Intros n' ld; Intros.
  forward_call (lockt, tsh, g_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh1 gsh2 g).
  { simpl.
    rewrite selflock_eq at 2; cancel.
    Exists n'; rewrite interp_ghost; cancel.
    rewrite sepcon_comm; apply sepcon_derives; [apply lock_inv_later | cancel]. }
  { split; auto; repeat split; [apply g_inv_precise | apply g_inv_positive | apply selflock_rec]; auto. }
  forward.
  Exists lvar0; entailer!.
Qed.

Transparent lock_pred.

Lemma lock_struct : forall p, data_at_ Tsh (Tstruct _lock_t noattr) p |-- data_at_ Tsh tlock p.
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
Qed.

Lemma lqueue_share_join : forall sh1 sh2 sh gsh p ghosts lock
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2) (Hjoin : sepalg.join sh1 sh2 sh),
  lqueue sh1 gsh p ghosts lock * lqueue sh2 gsh p ghosts lock = lqueue sh gsh p ghosts lock.
Proof.
  intros; unfold lqueue.
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
  fold_right_sepcon (map (fun sh => lqueue sh gsh p ghosts lock) (map snd shs)) =
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

Lemma main_loop1 : forall {Espec : OracleKind} (q0 lvar0 : val) gsh1 gsh2 (Hgsh1 : readable_share gsh1) (Hgsh2 : readable_share gsh2)
  (Hgsh : sepalg.join gsh1 gsh2 Ews) g1 g2 g3 (ghosts := [g1; g2; g3]) p lock lshs1 (Hlenl1 : Zlength lshs1 = 3)
  (Hlshs1 : forall i : Z, 0 <= i < 3 -> let '(a, b) := Znth i lshs1 (Tsh, Tsh) in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) lshs1 (Tsh, Tsh))))
  gshs1 (Hglen1 : Zlength gshs1 = 3)
  (Hgshs1 : forall i : Z, 0 <= i < 3 -> let '(a, b) := Znth i gshs1 (Ews, Ews) in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) gshs1 (Ews, Ews))))
  sh1 sh2 (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2) (Hsh : sepalg.join sh1 sh2 Tsh)
  (f_lock := fun x : Z * val =>
          Lock_inv sh1 (snd x)
            (f_lock_pred (snd (Znth (2 - fst x) lshs1 (Tsh, Tsh))) (snd (Znth (2 - fst x) gshs1 (Ews, Ews))) sh2
               q0 p lock (snd x) ghosts gsh2)) i (Hi : 0 <= i < 3),
 semax (initialized_list [_i; _t'1] (func_tycontext f_main Vprog Gprog))
  (PROP ( )
   LOCAL (temp _i (vint i); temp _t'1 p; lvar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6) lvar0;
   gvar _q0 q0)
   SEP (ghost_factory; data_at (fst (Znth (3 - i) gshs1 (Ews, Ews))) (tptr tqueue_t) p q0;
   lqueue (fst (Znth (3 - i) lshs1 (Tsh, Tsh))) gsh2 p ghosts lock; ghost gsh1 tint (vint (-1)) g1;
   ghost gsh1 tint (vint (-1)) g2; ghost gsh1 tint (vint (-1)) g3;
   EX flocks : list val,
   !! (Zlength flocks = i) &&
   (data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6) (flocks ++ repeat Vundef (Z.to_nat (6 - i))) lvar0 *
    fold_right_sepcon (map Interp (map f_lock (combine (upto (Z.to_nat i)) flocks))))))
  (Ssequence
     (Ssequence
        (Scall (Some _t'2) (Evar _malloc (Tfunction (Ctypes.Tcons tuint Ctypes.Tnil) (tptr tvoid) cc_default))
           [Esizeof (Tstruct _lock_t noattr) tuint])
        (Sset _l (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr (Tstruct _lock_t noattr)))))
     (Ssequence
        (Sassign
           (Ederef
              (Ebinop Oadd (Evar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6))
                 (Etempvar _i tint) (tptr (tptr (Tstruct _lock_t noattr)))) (tptr (Tstruct _lock_t noattr)))
           (Etempvar _l (tptr (Tstruct _lock_t noattr))))
        (Ssequence
           (Scall None (Evar _makelock (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tvoid cc_default))
              [Ecast (Etempvar _l (tptr (Tstruct _lock_t noattr))) (tptr tvoid)])
           (Scall None
              (Evar _spawn
                 (Tfunction
                    (Ctypes.Tcons
                       (tptr (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) (tptr tvoid) cc_default))
                       (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil)) tvoid cc_default))
              [Ecast
                 (Eaddrof (Evar _f (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) (tptr tvoid) cc_default))
                    (tptr (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) (tptr tvoid) cc_default)))
                 (tptr tvoid); Ecast (Etempvar _l (tptr (Tstruct _lock_t noattr))) (tptr tvoid)]))))
  (normal_ret_assert
     (PROP (0 <= i + 1 <= 3)
      LOCAL (temp _i (vint i); temp _t'1 p; lvar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6) lvar0;
      gvar _q0 q0)
      SEP (ghost_factory; data_at (fst (Znth (3 - (i + 1)) gshs1 (Ews, Ews))) (tptr tqueue_t) p q0;
      lqueue (fst (Znth (3 - (i + 1)) lshs1 (Tsh, Tsh))) gsh2 p ghosts lock; ghost gsh1 tint (vint (-1)) g1;
      ghost gsh1 tint (vint (-1)) g2; ghost gsh1 tint (vint (-1)) g3;
      EX flocks : list val,
      !! (Zlength flocks = i + 1) &&
      (data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6) (flocks ++ repeat Vundef (Z.to_nat (6 - (i + 1))))
         lvar0 * fold_right_sepcon (map Interp (map f_lock (combine (upto (Z.to_nat (i + 1))) flocks))))))).
Proof.
  intros.
  forward_call (sizeof tlock).
  { simpl fold_right; cancel. }
  { simpl; computable. }
  Intros l flocks.
  forward.
  rewrite upd_Znth_app2; [|repeat rewrite Zlength_correct in *; abstract omega].
  replace (i - Zlength flocks) with 0 by abstract omega; rewrite upd_Znth0, sublist_repeat;
    try rewrite Zlength_repeat, Z2Nat.id; try abstract omega.
  assert (isptr l) by (destruct l; try contradiction; simpl; auto).
  forward_call (l, Tsh, f_lock_pred (snd (Znth (2 - i) lshs1 (Tsh, Tsh)))
    (snd (Znth (2 - i) gshs1 (Ews, Ews))) sh2 q0 p lock l ghosts gsh2).
  { rewrite !sem_cast_neutral_ptr; auto; apply prop_right; auto. }
  { repeat rewrite sepcon_assoc; apply sepcon_derives; [|cancel].
    rewrite memory_block_data_at_;
      [simpl; cancel | apply malloc_field_compatible; auto; simpl; try computable].
    exists 2; auto. }
  get_global_function'' _f; Intros.
  apply extract_exists_pre; intros f_.
  match goal with |-context[func_ptr' ?P] => set (spec := P) end.
  forward_call (f_, l, existT (fun ty => ty * (ty -> val -> Pred))%type
    (share * share * share * val * val * val * list val * share)%type
    ((snd (Znth (2 - i) lshs1 (Tsh, Tsh)), snd (Znth (2 - i) gshs1 (Ews, Ews)),
     sh2, q0, p, lock, ghosts, gsh2),
   fun (x : (share * share * share * val * val * val * list val * share)) (lockt : val) =>
   let '(lsh, gsh, tsh, p', p, lock, ghosts, gsh2) := x in
   Pred_list [Pred_prop (readable_share lsh /\ readable_share gsh /\ readable_share tsh);
     Data_at _ gsh (tptr tqueue_t) p p';
     Field_at _ lsh tqueue_t [StructField _lock] lock p;
     Lock_inv lsh lock (lock_pred gsh2 p ghosts);
     Lock_inv tsh lockt (f_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh2)])).
  { apply prop_right; destruct l; try contradiction; auto. }
  { Exists _arg (fun x : share * share * share * val * val * val * list val * share =>
      let '(_, _, _, p', _, _, _, _) := x in [(_q0, p')]).
    repeat rewrite sepcon_assoc; apply sepcon_derives.
    { apply derives_refl'.
      subst spec; f_equal; f_equal.
      extensionality.
      destruct x as (?, (((((((?, ?), ?), ?), ?), ?), ?), ?)); simpl.
      f_equal; f_equal.
      unfold SEPx, lqueue; simpl; normalize. }
    subst Frame; instantiate (1 := [ghost_factory;
      data_at (fst (Znth (2 - i) gshs1 (Ews, Ews))) (tptr tqueue_t) p q0;
      lqueue (fst (Znth (2 - i) lshs1 (Tsh, Tsh))) gsh2 p ghosts lock;
      ghost gsh1 tint (vint (-1)) g1; ghost gsh1 tint (vint (-1)) g2; ghost gsh1 tint (vint (-1)) g3;
      data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6) ((flocks ++ [l]) ++ repeat Vundef (Z.to_nat (6 - (i + 1)))) lvar0;
      fold_right_sepcon (map Interp (map f_lock (combine (upto (Z.to_nat (i + 1))) (flocks ++ [l]))))]).
    rewrite <- (lock_inv_share_join sh1 sh2 Tsh); auto.
    specialize (Hgshs1 (2 - i)); exploit Hgshs1; [abstract omega|].
    destruct (Znth (2 - i) gshs1 (Ews, Ews)) eqn: Hg1.
    replace (2 - i + 1) with (3 - i) by abstract omega.
    intros (? & ? & Hglsh); rewrite <- (data_at_share_join _ _ _ _ _ _ Hglsh); auto.
    specialize (Hlshs1 (2 - i)); exploit Hlshs1; [abstract omega|].
    destruct (Znth (2 - i) lshs1 (Tsh, Tsh)) eqn: Hl1.
    replace (2 - i + 1) with (3 - i) by abstract omega.
    intros (? & ? & Hllsh); rewrite <- (lqueue_share_join s s0 (fst (Znth (3 - i) lshs1 (Tsh, Tsh)))); auto.
    unfold lqueue; simpl; rewrite Z.sub_add_distr, <- app_assoc; simpl.
    repeat rewrite Hg1; repeat rewrite Hl1; simpl.
    repeat rewrite sepcon_andp_prop'; apply andp_right; [apply prop_right; auto | cancel].
    rewrite Z2Nat.inj_add, upto_app, combine_app; try abstract omega.
    simpl; repeat rewrite map_app; simpl.
    rewrite Z2Nat.id, Z.add_0_r, Hg1, Hl1; simpl; [|abstract omega].
    rewrite sem_cast_neutral_ptr; auto.
    rewrite sepcon_app; simpl; unfold fold_right at 2; cancel.
    { rewrite upto_length; rewrite Zlength_correct in *; Omega0. } }
  entailer!.
  replace (3 - (Zlength flocks + 1)) with (2 - Zlength flocks) by abstract omega.
  Exists (flocks ++ [l]); rewrite Zlength_app, Zlength_cons, Zlength_nil; entailer!.
Qed.

Lemma main_loop2 : forall {Espec : OracleKind} (q0 lvar0 : val) gsh1 gsh2 (Hgsh1 : readable_share gsh1) (Hgsh2 : readable_share gsh2)
  (Hgsh : sepalg.join gsh1 gsh2 Ews) g1 g2 g3 (ghosts := [g1; g2; g3]) p lock lshs1 (Hlenl1 : Zlength lshs1 = 3)
  (Hlshs1 : forall i : Z, 0 <= i < 3 -> let '(a, b) := Znth i lshs1 (Tsh, Tsh) in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) lshs1 (Tsh, Tsh))))
  gshs1 (Hglen1 : Zlength gshs1 = 3)
  (Hgshs1 : forall i : Z, 0 <= i < 3 -> let '(a, b) := Znth i gshs1 (Ews, Ews) in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) gshs1 (Ews, Ews))))
  sh1 sh2 (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2) (Hsh : sepalg.join sh1 sh2 Tsh)
  (f_lock := fun x : Z * val =>
          Lock_inv sh1 (snd x)
            (f_lock_pred (snd (Znth (2 - fst x) lshs1 (Tsh, Tsh))) (snd (Znth (2 - fst x) gshs1 (Ews, Ews))) sh2
               q0 p lock (snd x) ghosts gsh2)) flocks (Hflocks : Zlength flocks = 3)
  (lsh' := fst (Znth 0 lshs1 (Tsh, Tsh))) (gsh' := fst (Znth 0 gshs1 (Ews, Ews)))
  lshs2 (Hlenl2 : Zlength lshs2 = 3)
  (Hlshs2 : forall i : Z, 0 <= i < 3 -> let '(a, b) := Znth i lshs2 (lsh', lsh') in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) lshs2 (lsh', lsh'))))
  gshs2 (Hglen2 : Zlength gshs2 = 3)
  (Hgshs2 : forall i : Z, 0 <= i < 3 -> let '(a, b) := Znth i gshs2 (gsh', gsh') in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) gshs2 (gsh', gsh'))))
  (g_lock := fun x : Z * val => Lock_inv sh1 (snd x)
            (g_lock_pred (snd (Znth (2 - fst x) lshs2 (lsh', lsh'))) (snd (Znth (2 - fst x) gshs2 (gsh', gsh')))
               sh2 q0 p lock (snd x) ghosts gsh1 gsh2 (Znth (fst x) ghosts Vundef))) i (Hi : 0 <= i < 3),
semax (initialized_list [_i; _i__1; _t'1] (func_tycontext f_main Vprog Gprog))
  (PROP (Zlength flocks = 3)
   LOCAL (temp _i__1 (vint i); temp _t'1 p; lvar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6) lvar0;
   gvar _q0 q0)
   SEP (ghost_factory; data_at (fst (Znth (3 - i) gshs2 (gsh', gsh'))) (tptr tqueue_t) p q0;
   lqueue (fst (Znth (3 - i) lshs2 (lsh', lsh'))) gsh2 p ghosts lock;
   fold_right_sepcon (skipn (Z.to_nat i) (map (ghost gsh1 tint (vint (-1))) ghosts));
   fold_right_sepcon (map Interp (map f_lock (combine (upto 3) flocks)));
   EX glocks : list val,
   !! (Zlength glocks = i) &&
   (data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6) (flocks ++ glocks ++ repeat Vundef (Z.to_nat (3 - i)))
      lvar0 * fold_right_sepcon (map Interp (map g_lock (combine (upto (Z.to_nat i)) glocks))))))
  (Ssequence
     (Ssequence
        (Scall (Some _t'3) (Evar _malloc (Tfunction (Ctypes.Tcons tuint Ctypes.Tnil) (tptr tvoid) cc_default))
           [Esizeof (Tstruct _lock_t noattr) tuint])
        (Sset _l__1 (Ecast (Etempvar _t'3 (tptr tvoid)) (tptr (Tstruct _lock_t noattr)))))
     (Ssequence
        (Sassign
           (Ederef
              (Ebinop Oadd (Evar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6))
                 (Ebinop Oadd (Etempvar _i__1 tint) (Econst_int (Int.repr 3) tint) tint)
                 (tptr (tptr (Tstruct _lock_t noattr)))) (tptr (Tstruct _lock_t noattr)))
           (Etempvar _l__1 (tptr (Tstruct _lock_t noattr))))
        (Ssequence
           (Scall None (Evar _makelock (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tvoid cc_default))
              [Ecast (Etempvar _l__1 (tptr (Tstruct _lock_t noattr))) (tptr tvoid)])
           (Scall None
              (Evar _spawn
                 (Tfunction
                    (Ctypes.Tcons
                       (tptr (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) (tptr tvoid) cc_default))
                       (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil)) tvoid cc_default))
              [Ecast
                 (Eaddrof (Evar _g (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) (tptr tvoid) cc_default))
                    (tptr (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) (tptr tvoid) cc_default)))
                 (tptr tvoid); Ecast (Etempvar _l__1 (tptr (Tstruct _lock_t noattr))) (tptr tvoid)]))))
  (normal_ret_assert
     (PROP (0 <= i + 1 <= 3; Zlength flocks = 3)
      LOCAL (temp _i__1 (vint i); temp _t'1 p;
      lvar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6) lvar0; gvar _q0 q0)
      SEP (ghost_factory; data_at (fst (Znth (3 - (i + 1)) gshs2 (gsh', gsh'))) (tptr tqueue_t) p q0;
      lqueue (fst (Znth (3 - (i + 1)) lshs2 (lsh', lsh'))) gsh2 p ghosts lock;
      fold_right_sepcon (skipn (Z.to_nat (i + 1)) (map (ghost gsh1 tint (vint (-1))) ghosts));
      fold_right_sepcon (map Interp (map f_lock (combine (upto 3) flocks)));
      EX glocks : list val,
      !! (Zlength glocks = i + 1) &&
      (data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6)
         (flocks ++ glocks ++ repeat Vundef (Z.to_nat (3 - (i + 1)))) lvar0 *
       fold_right_sepcon (map Interp (map g_lock (combine (upto (Z.to_nat (i + 1))) glocks))))))).
Proof.
  intros.
  forward_call (sizeof tlock).
    { simpl fold_right; cancel. }
    { simpl; computable. }
    Intros l glocks.
    forward.
    rewrite app_assoc, upd_Znth_app2; [|rewrite Zlength_app, Zlength_repeat; abstract omega].
    rewrite Zlength_app; replace (i + 3 - (Zlength flocks + Zlength glocks)) with 0 by abstract omega.
    rewrite upd_Znth0, sublist_repeat; try rewrite Zlength_repeat, Z2Nat.id; try abstract omega.
    assert (isptr l) by (destruct l; try contradiction; simpl; auto).
    forward_call (l, Tsh, g_lock_pred (snd (Znth (2 - i) lshs2 (lsh', lsh')))
      (snd (Znth (2 - i) gshs2 (gsh', gsh'))) sh2 q0 p lock l ghosts gsh1 gsh2 (Znth i ghosts Vundef)).
    { repeat rewrite sem_cast_neutral_ptr; auto; apply prop_right; auto. }
    { repeat rewrite sepcon_assoc; apply sepcon_derives; [|cancel].
      rewrite memory_block_data_at_; [simpl; cancel | apply malloc_field_compatible; auto; simpl; try computable].
      exists 2; auto. }
    get_global_function'' _g; Intros.
    apply extract_exists_pre; intros g_.
    match goal with |-context[func_ptr' ?P] => set (spec := P) end.
    forward_call (g_, l, existT (fun ty => ty * (ty -> val -> Pred))%type
      (share * share * share * Z * val * val * val * list val * nat * val * share * share)%type
      ((snd (Znth (2 - i) lshs2 (lsh', lsh')), snd (Znth (2 - i) gshs2 (gsh', gsh')),
       sh2, -1, q0, p, lock, ghosts, Z.to_nat i, Znth i ghosts Vundef, gsh1, gsh2),
     fun (x : (share * share * share * Z * val * val * val * list val * nat * val * share * share)) (lockt : val) =>
     let '(lsh, gsh, tsh, t, p', p, lock, ghosts, i, g, gsh1, gsh2) := x in
     Pred_list [Pred_prop (readable_share lsh /\ readable_share gsh /\ readable_share tsh /\
         Int.min_signed <= t <= Int.max_signed /\ sepalg.join gsh1 gsh2 Ews /\ nth_error ghosts i = Some g);
       Data_at _ gsh (tptr tqueue_t) p p';
       Field_at _ lsh tqueue_t [StructField _lock] lock p;
       Lock_inv lsh lock (lock_pred gsh2 p ghosts);
       Lock_inv tsh lockt (g_lock_pred lsh gsh tsh p' p lock lockt ghosts gsh1 gsh2 g);
       Ghost gsh1 tint (vint t) g])).
    { apply prop_right; destruct l; try contradiction; auto. }
    { unfold fold_right at 1.
      Exists _arg (fun x : share * share * share * Z * val * val * val * list val * nat * val * share * share =>
        let '(_, _, _, _, p', _, _, _, _, _, _, _) := x in [(_q0, p')]).
      repeat rewrite sepcon_assoc; apply sepcon_derives.
      { apply derives_refl'.
        subst spec; f_equal; f_equal.
        extensionality.
        destruct x as (?, (((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?)); simpl.
        rewrite interp_ghost; f_equal; f_equal.
        unfold SEPx, lqueue; simpl; normalize. }
      subst Frame; instantiate (1 := [ghost_factory;
        data_at (fst (Znth (2 - i) gshs2 (gsh', gsh'))) (tptr tqueue_t) p q0;
        lqueue (fst (Znth (2 - i) lshs2 (lsh', lsh'))) gsh2 p ghosts lock;
        fold_right_sepcon (skipn (Z.to_nat (i + 1)) (map (ghost gsh1 tint (vint (-1))) ghosts));
        fold_right_sepcon (map Interp (map f_lock (combine (upto 3) flocks)));
        data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6) (flocks ++ (glocks ++ [l]) ++ repeat Vundef (Z.to_nat (3 - (i + 1)))) lvar0;
        fold_right_sepcon (map Interp (map g_lock (combine (upto (Z.to_nat (i + 1))) (glocks ++ [l]))))]).
      rewrite <- (lock_inv_share_join sh1 sh2 Tsh); auto.
      exploit (Hgshs2 (2 - i)); [abstract omega|].
      fold gsh'; destruct (Znth (2 - i) gshs2 (gsh', gsh')) eqn: Hg1.
      replace (2 - i + 1) with (3 - i) by abstract omega.
      intros (? & ? & Hglsh); rewrite <- (data_at_share_join _ _ _ _ _ _ Hglsh).
      exploit (Hlshs2 (2 - i)); [abstract omega|].
      fold lsh'; destruct (Znth (2 - i) lshs2 (lsh', lsh')) eqn: Hl1.
      replace (2 - i + 1) with (3 - i) by abstract omega.
      intros (? & ? & Hllsh); rewrite <- (lqueue_share_join s s0 (fst (Znth (3 - i) lshs2 (lsh', lsh'))));
        auto.
      unfold lqueue; simpl; rewrite Z.sub_add_distr, <- app_assoc; simpl.
      repeat rewrite Hg1; repeat rewrite Hl1; rewrite <- app_assoc; simpl.
      repeat rewrite sepcon_andp_prop'; apply andp_right; [apply prop_right | unfold fold_right; cancel].
      { split; [|split; [|split; [|split; [|split]]]]; auto; try computable.
        unfold Znth; destruct (zlt i 0); [abstract omega|].
        subst ghosts; erewrite nth_error_nth; simpl; eauto; Omega0. }
      rewrite Z2Nat.inj_add, upto_app, combine_app; try abstract omega.
      simpl; repeat rewrite map_app; simpl.
      rewrite Z.add_0_r, Z2Nat.id; simpl; [|abstract omega].
      rewrite sepcon_app; simpl; unfold fold_right; cancel.
      erewrite <- (firstn_skipn 1 (skipn (Z.to_nat i) _)), skipn_skipn,
        <- firstn_1_skipn with (d := ghost gsh1 tint (vint (-1)) Vundef), sepcon_app; [|Omega0].
      rewrite nth_Znth, Z2Nat.id; [simpl | abstract omega].
      rewrite Hg1, Hl1, sem_cast_neutral_ptr; auto.
      erewrite interp_ghost, <- Znth_map' with (f := ghost _ _ _); subst ghosts; simpl;
        unfold fold_right; cancel.
      { subst; rewrite Zlength_correct, Nat2Z.id, upto_length; auto. } }
    go_lower; Exists (glocks ++ [l]); entailer!.
    - rewrite Zlength_app, Zlength_cons, Zlength_nil; auto.
    - replace (3 - (Zlength glocks + 1)) with (2 - Zlength glocks) by abstract omega; apply derives_refl.
Qed.

Opaque upto.

Lemma main_loop3 : forall {Espec : OracleKind} (q0 lvar0 : val) gsh1 gsh2 (Hgsh1 : readable_share gsh1) (Hgsh2 : readable_share gsh2)
  (Hgsh : sepalg.join gsh1 gsh2 Ews) g1 g2 g3 (ghosts := [g1; g2; g3]) p lock lshs1 (Hlenl1 : Zlength lshs1 = 3)
  (Hlshs1 : forall i : Z, 0 <= i < 3 -> let '(a, b) := Znth i lshs1 (Tsh, Tsh) in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) lshs1 (Tsh, Tsh))))
  gshs1 (Hglen1 : Zlength gshs1 = 3)
  (Hgshs1 : forall i : Z, 0 <= i < 3 -> let '(a, b) := Znth i gshs1 (Ews, Ews) in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) gshs1 (Ews, Ews))))
  sh1 sh2 (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2) (Hsh : sepalg.join sh1 sh2 Tsh)
  (f_lock := fun x : Z * val =>
          Lock_inv sh1 (snd x)
            (f_lock_pred (snd (Znth (2 - fst x) lshs1 (Tsh, Tsh))) (snd (Znth (2 - fst x) gshs1 (Ews, Ews))) sh2
               q0 p lock (snd x) ghosts gsh2)) flocks (Hflocks : Zlength flocks = 3)
  (lsh' := fst (Znth 0 lshs1 (Tsh, Tsh))) (gsh' := fst (Znth 0 gshs1 (Ews, Ews)))
  lshs2 (Hlenl2 : Zlength lshs2 = 3)
  (Hlshs2 : forall i : Z, 0 <= i < 3 -> let '(a, b) := Znth i lshs2 (lsh', lsh') in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) lshs2 (lsh', lsh'))))
  gshs2 (Hglen2 : Zlength gshs2 = 3)
  (Hgshs2 : forall i : Z, 0 <= i < 3 -> let '(a, b) := Znth i gshs2 (gsh', gsh') in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) gshs2 (gsh', gsh'))))
  (g_lock := fun x : Z * val => Lock_inv sh1 (snd x)
            (g_lock_pred (snd (Znth (2 - fst x) lshs2 (lsh', lsh'))) (snd (Znth (2 - fst x) gshs2 (gsh', gsh')))
               sh2 q0 p lock (snd x) ghosts gsh1 gsh2 (Znth (fst x) ghosts Vundef)))
  glocks (Hglocks : Zlength glocks = 3) i (Hi : 0 <= i < 6),
semax (initialized_list [_i; _i__1; _i__2; _t'1] (func_tycontext f_main Vprog Gprog))
  (PROP (Forall isptr flocks; Forall isptr glocks)
   LOCAL (temp _i__2 (vint i); temp _t'1 p; lvar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6) lvar0;
   gvar _q0 q0)
   SEP (ghost_factory; data_at (fst (Znth 0 gshs2 (gsh', gsh'))) (tptr tqueue_t) p q0;
   fold_right_sepcon
     (firstn (Z.to_nat i)
        (map (fun sh : Share.t => data_at sh (tptr tqueue_t) p q0) (map snd (rev gshs1 ++ rev gshs2))));
   lqueue (fst (Znth 0 lshs2 (lsh', lsh'))) gsh2 p ghosts lock;
   fold_right_sepcon
     (firstn (Z.to_nat i)
        (map (fun sh : Share.t => lqueue sh gsh2 p ghosts lock) (map snd (rev lshs1 ++ rev lshs2))));
   EX ns : list Z,
   !! (Zlength ns = Zlength ghosts) &&
   fold_right_sepcon
     (firstn (Z.to_nat i - 3) (map (fun x : Z * val => ghost gsh1 tint (vint (fst x)) (snd x)) (combine ns ghosts)));
   fold_right_sepcon (skipn (Z.to_nat i) (map Interp (map f_lock (combine (upto 3) flocks))));
   fold_right_sepcon (skipn (Z.to_nat i - 3) (map Interp (map g_lock (combine (upto 3) glocks))));
   data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6) (flocks ++ glocks) lvar0))
  (Ssequence
     (Sset _l__2
        (Ederef
           (Ebinop Oadd (Evar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6))
              (Etempvar _i__2 tint) (tptr (tptr (Tstruct _lock_t noattr)))) (tptr (Tstruct _lock_t noattr))))
     (Ssequence
        (Scall None (Evar _acquire (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tvoid cc_default))
           [Ecast (Etempvar _l__2 (tptr (Tstruct _lock_t noattr))) (tptr tvoid)])
        (Ssequence
           (Scall None (Evar _freelock2 (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tvoid cc_default))
              [Ecast (Etempvar _l__2 (tptr (Tstruct _lock_t noattr))) (tptr tvoid)])
           (Scall None (Evar _free (Tfunction (Ctypes.Tcons (tptr tvoid) Ctypes.Tnil) tvoid cc_default))
              [Etempvar _l__2 (tptr (Tstruct _lock_t noattr))]))))
  (normal_ret_assert
     (PROP (0 <= i + 1 <= 6; Forall isptr flocks; Forall isptr glocks)
      LOCAL (temp _i__2 (vint i); temp _t'1 p; lvar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6) lvar0;
      gvar _q0 q0)
      SEP (ghost_factory; data_at (fst (Znth 0 gshs2 (gsh', gsh'))) (tptr tqueue_t) p q0;
      fold_right_sepcon
        (firstn (Z.to_nat (i + 1))
           (map (fun sh : Share.t => data_at sh (tptr tqueue_t) p q0) (map snd (rev gshs1 ++ rev gshs2))));
      lqueue (fst (Znth 0 lshs2 (lsh', lsh'))) gsh2 p ghosts lock;
      fold_right_sepcon
        (firstn (Z.to_nat (i + 1))
           (map (fun sh : Share.t => lqueue sh gsh2 p ghosts lock) (map snd (rev lshs1 ++ rev lshs2))));
      EX ns : list Z,
      !! (Zlength ns = Zlength ghosts) &&
      fold_right_sepcon
        (firstn (Z.to_nat (i + 1) - 3)
           (map (fun x : Z * val => ghost gsh1 tint (vint (fst x)) (snd x)) (combine ns ghosts)));
      fold_right_sepcon (skipn (Z.to_nat (i + 1)) (map Interp (map f_lock (combine (upto 3) flocks))));
      fold_right_sepcon (skipn (Z.to_nat (i + 1) - 3) (map Interp (map g_lock (combine (upto 3) glocks))));
      data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6) (flocks ++ glocks) lvar0))).
Proof.
  intros.
  Intro ns; Intros.
    forward.
    { go_lower.
      repeat apply andp_right; apply prop_right; auto.
      apply Forall_Znth.
      - rewrite Zlength_app; abstract omega.
      - rewrite Forall_app; split; eapply Forall_impl; try eassumption; auto. }
    destruct (Z_lt_dec i 3).
    - rewrite app_Znth1; [|abstract omega].
      forward_call (Znth i flocks Vundef, sh1, f_lock_pred (snd (Znth (2 - i) lshs1 (Tsh, Tsh)))
        (snd (Znth (2 - i) gshs1 (Ews, Ews))) sh2 q0 p lock (Znth i flocks Vundef) ghosts gsh2).
      { apply prop_right; rewrite eval_cast_neutral_is_pointer_or_null;
          rewrite eval_cast_neutral_is_pointer_or_null; auto. }
      { assert (length flocks = 3)%nat by (rewrite Zlength_correct in *; Omega0).
        erewrite skipn_cons, !Znth_map', Znth_combine; auto;
          [|rewrite !map_length, combine_length, Min.min_l; rewrite upto_length; Omega0].
        rewrite Z2Nat.id; [|omega].
        rewrite Znth_upto with (m := 3%nat); [|Omega0].
        rewrite <- (Nat.add_1_r (Z.to_nat i)).
        instantiate (1 := Vundef); simpl; cancel. }
      freeze [2; 3; 4; 5; 6; 7; 8; 9; 10] FR.
      forward_call (Znth i flocks Vundef, Tsh, Later (f_lock_pred (snd (Znth (2 - i) lshs1 (Tsh, Tsh)))
        (snd (Znth (2 - i) gshs1 (Ews, Ews))) sh2 q0 p lock (Znth i flocks Vundef) ghosts gsh2)).
      { apply prop_right; rewrite eval_cast_neutral_is_pointer_or_null;
          rewrite eval_cast_neutral_is_pointer_or_null; auto. }
      { simpl.
        rewrite selflock_eq at 2.
        rewrite (sepcon_comm (FRZL FR)); repeat rewrite sepcon_assoc.
        eapply derives_trans; [apply sepcon_derives; [apply lock_inv_later | apply derives_refl]|].
        rewrite <- (lock_inv_share_join sh1 sh2 Tsh); auto; cancel. }
      { split; auto; split; [apply later_positive, f_inv_positive | apply later_rec, selflock_rec]. }
      forward_call (Znth i flocks Vundef, sizeof tlock).
      { rewrite data_at__memory_block; simpl; entailer!. }
      Exists [0; 0; 0].
      go_lower.
      apply andp_right; [apply prop_right; repeat split; auto; abstract omega|].
      apply andp_right; [apply prop_right; repeat split; auto|].
      thaw FR.
      rewrite Z2Nat.inj_add; try abstract omega; simpl.
      assert (Z.to_nat i < 3)%nat by Omega0.
      replace (Z.to_nat i + 1 - 3)%nat with O by abstract omega;
        replace (Z.to_nat i - 3)%nat with O by abstract omega.
      erewrite <- !firstn_app, <- !firstn_1_skipn.
      rewrite !nth_Znth, !sepcon_app; simpl.
      rewrite Z2Nat.id; try abstract omega.
      rewrite !Znth_map', !app_Znth1; try (rewrite Zlength_rev; abstract omega).
      rewrite !Znth_rev; try abstract omega.
      rewrite Hglen1, Hlenl1.
      replace (3 - i - 1) with (2 - i) by abstract omega.
      unfold fold_right, lqueue; simpl; cancel.
      entailer!.
      apply derives_refl.
      { rewrite !map_length, app_length, !rev_length.
        rewrite Zlength_correct in *; Omega0. }
      { rewrite !map_length, app_length, !rev_length.
        rewrite Zlength_correct in *; Omega0. }
    - rewrite app_Znth2; [|abstract omega].
      replace (Zlength flocks) with 3 by auto.
      assert (3 <= Z.to_nat i < 6)%nat.
      { split; try Omega0.
        rewrite Nat2Z.inj_le, Z2Nat.id; simpl; abstract omega. }
      forward_call (Znth (i - 3) glocks Vundef, sh1, g_lock_pred (snd (Znth (2 - (i - 3)) lshs2 (lsh', lsh')))
        (snd (Znth (2 - (i - 3)) gshs2 (gsh', gsh'))) sh2 q0 p lock (Znth (i - 3) glocks Vundef)
        ghosts gsh1 gsh2 (Znth (i - 3) ghosts Vundef)).
      { apply prop_right; rewrite eval_cast_neutral_is_pointer_or_null;
          rewrite eval_cast_neutral_is_pointer_or_null; auto. }
      { assert (length glocks = 3)%nat by (rewrite Zlength_correct in *; Omega0).
        assert (3 > Z.to_nat i - 3)%nat by omega.
        setoid_rewrite skipn_cons at 2;
          [|rewrite !map_length, combine_length, Min.min_l; rewrite upto_length; auto; omega].
        rewrite !Znth_map', Znth_combine, !Nat2Z.inj_sub, Z2Nat.id; auto; try omega.
        rewrite Znth_upto with (m := 3%nat); [|simpl; omega].
        rewrite <- (Nat.add_1_r (_ - _)).
        instantiate (1 := Vundef); simpl; cancel. }
      freeze [2; 3; 4; 5; 6; 7; 8; 9; 10] FR.
      forward_call (Znth (i - 3) glocks Vundef, Tsh, Later (g_lock_pred
        (snd (Znth (2 - (i - 3)) lshs2 (lsh', lsh')))
        (snd (Znth (2 - (i - 3)) gshs2 (gsh', gsh'))) sh2 q0 p lock (Znth (i - 3) glocks Vundef)
        ghosts gsh1 gsh2 (Znth (i - 3) ghosts Vundef))).
      { apply prop_right; rewrite eval_cast_neutral_is_pointer_or_null;
          rewrite eval_cast_neutral_is_pointer_or_null; auto. }
      { simpl.
        rewrite selflock_eq at 2.
        rewrite (sepcon_comm (FRZL FR)); repeat rewrite sepcon_assoc.
        eapply derives_trans; [apply sepcon_derives; [apply lock_inv_later | apply derives_refl]|].
        rewrite <- (lock_inv_share_join sh1 sh2 Tsh); auto; cancel. }
      { split; auto; split; [apply later_positive, g_inv_positive | apply later_rec, selflock_rec]. }
      Intro x.
      forward_call (Znth (i - 3) glocks Vundef, sizeof tlock).
      { rewrite data_at__memory_block; simpl; entailer!. }
      go_lower.
      Exists (upd_Znth (i - 3) ns x).
      apply andp_right; [apply prop_right; repeat split; auto; abstract omega|].
      apply andp_right; [apply prop_right; repeat split; auto|].
      thaw FR.
      rewrite Z2Nat.inj_add; try abstract omega; simpl.
      assert (Z.to_nat i < length gshs1 + length gshs2)%nat.
      { rewrite Zlength_correct in *; Omega0. }
      assert (Z.to_nat i < length lshs1 + length lshs2)%nat.
      { rewrite Zlength_correct in *; Omega0. }
      replace (Z.to_nat i + 1 - 3)%nat with (Z.to_nat i - 3 + 1)%nat by abstract omega.
      assert (Zlength ns = 3).
      { subst ghosts; rewrite !Zlength_cons, Zlength_nil in *; abstract omega. }
      assert (length (upd_Znth (i - 3) ns x) = 3%nat).
      { apply Nat2Z.inj.
        rewrite <- Zlength_correct, upd_Znth_Zlength; simpl; abstract omega. }
      erewrite <- !firstn_app, <- !firstn_1_skipn; try rewrite !map_length; try rewrite app_length, !rev_length;
        try abstract omega.
      rewrite !nth_Znth, !sepcon_app; simpl.
      rewrite !Znth_map', !app_Znth2; try (rewrite Zlength_rev; abstract omega).
      rewrite Nat2Z.inj_sub, Z2Nat.id; try abstract omega.
      rewrite !Znth_rev; rewrite !Zlength_rev; try abstract omega.
      rewrite interp_ghost, Znth_combine; auto; simpl.
      instantiate (1 := Vundef); instantiate (1 := x).
      rewrite upd_Znth_same; [|abstract omega].
      assert (length flocks = 3%nat) by (rewrite Zlength_correct in *; Omega0).
      rewrite skipn_short;
        [|rewrite !map_length, combine_length, Min.min_l; rewrite upto_length; abstract omega].
      setoid_rewrite skipn_short at 2;
        [|rewrite !map_length, combine_length, Min.min_l; rewrite upto_length; abstract omega].
      replace (Z.to_nat i - 3 + 1)%nat with (S (Z.to_nat i - 3))%nat by abstract omega.
      rewrite Hglen1, Hlenl1, Hglen2, Hlenl2.
      replace (3 - (i - 3) - 1) with (2 - (i - 3)) by abstract omega.
      unfold fold_right, lqueue; simpl; cancel; entailer!.
      + rewrite upd_Znth_Zlength; auto; abstract omega.
      + rewrite sepcon_comm; apply sepcon_derives; [apply derives_refl|].
        apply derives_refl'; f_equal.
        replace (Z.to_nat i - 3)%nat with (Z.to_nat (i - 3)) by Omega0.
        rewrite combine_upd_Znth1 with (d := Vundef), <- upd_Znth_map; try abstract omega.
        rewrite <- !sublist_firstn, !sublist_upd_Znth_l; auto; try abstract omega.
        rewrite Zlength_map.
        rewrite Zlength_combine, Z.min_l; abstract omega.
      + rewrite upd_Znth_Zlength; auto; abstract omega.
      + rewrite combine_length, Min.min_r; subst ghosts; simpl; abstract omega.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  name q0 _q0.
  start_function.
  destruct split_Ews as (gsh1 & gsh2 & ? & ? & Hgsh).
  apply ghost_alloc.
  apply new_ghost with (t := tint)(v := Vint (Int.repr (-1))); Intro g1.
  apply new_ghost with (t := tint)(v := Vint (Int.repr (-1))); Intro g2.
  apply new_ghost with (t := tint)(v := Vint (Int.repr (-1))); Intro g3.
  set (ghosts := [g1; g2; g3]).
  forward_call (gsh1, gsh2, ghosts).
  { subst ghosts; simpl; cancel. }
  Intro x; destruct x as (p, lock); simpl.
  forward.
  rewrite <- seq_assoc.
  exploit (split_shares 3 Tsh); auto; intros (lshs1 & Hlenl1 & Hlshs1).
  exploit (split_shares 3 Ews); auto; intros (gshs1 & Hglen1 & Hgshs1); simpl in *.
  exploit (split_readable_share Tsh); auto; intros (sh1 & sh2 & ? & ? & Hsh).
  set (f_lock := fun x => Lock_inv sh1 (snd x) (f_lock_pred (snd (Znth (2 - fst x) lshs1 (Tsh, Tsh)))
    (snd (Znth (2 - fst x) gshs1 (Ews, Ews))) sh2 q0 p lock (snd x) ghosts gsh2)).
  forward_for_simple_bound 3 (EX i : Z,
    PROP ()
    LOCAL (temp _t'1 p; lvar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6) lvar0; gvar _q0 q0)
    SEP (ghost_factory; data_at (fst (Znth (3 - i) gshs1 (Ews, Ews))) (tptr tqueue_t) p q0;
         lqueue (fst (Znth (3 - i) lshs1 (Tsh, Tsh))) gsh2 p ghosts lock;
         ghost gsh1 tint (vint (-1)) g1; ghost gsh1 tint (vint (-1)) g2; ghost gsh1 tint (vint (-1)) g3;
         EX flocks : list val, (!!(Zlength flocks = i) &&
           (data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6) (flocks ++ repeat Vundef (Z.to_nat (6 - i))) lvar0 *
            fold_right_sepcon (map Interp (map f_lock (combine (upto (Z.to_nat i)) flocks))))))).
  { go_lower; simpl.
    Exists ([] : list val); entailer!.
    do 2 (rewrite Znth_overflow; [|abstract omega]).
    simpl; unfold data_at_, field_at_, data_at; entailer!. }
  { apply main_loop1; auto. }
  simpl; Intro flocks; Intros.
  rewrite <- seq_assoc.
  exploit (split_shares 3 (fst (Znth 0 lshs1 (Tsh, Tsh)))).
  { exploit (Hlshs1 0); [abstract omega|].
    destruct (Znth 0 lshs1 (Tsh, Tsh)); intros (? & ?); auto. }
  intros (lshs2 & Hlenl2 & Hlshs2).
  exploit (split_shares 3 (fst (Znth 0 gshs1 (Ews, Ews)))).
  { exploit (Hgshs1 0); [abstract omega|].
    destruct (Znth 0 gshs1 (Ews, Ews)) eqn: Hg; setoid_rewrite Hg; intros (? & ?); auto. }
  intros (gshs2 & Hglen2 & Hgshs2); simpl in *.
  set (lsh' := fst (Znth 0 lshs1 (Tsh, Tsh))).
  set (gsh' := fst (Znth 0 gshs1 (Ews, Ews))).
  set (g_lock := fun x => Lock_inv sh1 (snd x) (g_lock_pred
    (snd (Znth (2 - fst x) lshs2 (lsh', lsh')))
    (snd (Znth (2 - fst x) gshs2 (gsh', gsh')))
    sh2 q0 p lock (snd x) ghosts gsh1 gsh2 (Znth (fst x) ghosts Vundef))).
  forward_for_simple_bound 3 (EX i : Z,
    PROP (Zlength flocks = 3)
    LOCAL (temp _t'1 p; lvar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6) lvar0; gvar _q0 q0)
    SEP (ghost_factory; data_at (fst (Znth (3 - i) gshs2 (gsh', gsh'))) (tptr tqueue_t) p q0;
         lqueue (fst (Znth (3 - i) lshs2 (lsh', lsh'))) gsh2 p ghosts lock;
         fold_right_sepcon (skipn (Z.to_nat i) (map (ghost gsh1 tint (vint (-1))) ghosts));
         fold_right_sepcon (map Interp (map f_lock (combine (upto 3) flocks)));
         EX glocks : list val, (!!(Zlength glocks = i) &&
           (data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6) (flocks ++ glocks ++ repeat Vundef (Z.to_nat (3 - i))) lvar0 *
            fold_right_sepcon (map Interp (map g_lock (combine (upto (Z.to_nat i)) glocks))))))).
  { go_lower; simpl.
    Exists ([] : list val); entailer!.
    do 2 (rewrite Znth_overflow with (i := 3); [simpl; cancel | abstract omega]). }
  { apply main_loop2; auto. }
  simpl; Intro glocks; Intros.
  rewrite <- seq_assoc.
  forward_for_simple_bound 6 (EX i : Z,
    PROP (Forall isptr flocks; Forall isptr glocks)
    LOCAL (temp _t'1 p; lvar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6) lvar0; gvar _q0 q0)
    SEP (ghost_factory; data_at (fst (Znth 0 gshs2 (gsh', gsh'))) (tptr tqueue_t) p q0;
         fold_right_sepcon (firstn (Z.to_nat i) (map (fun sh => data_at sh (tptr tqueue_t) p q0) (map snd (rev gshs1 ++ rev gshs2))));
         lqueue (fst (Znth 0 lshs2 (lsh', lsh'))) gsh2 p ghosts lock;
         fold_right_sepcon (firstn (Z.to_nat i) (map (fun sh => lqueue sh gsh2 p ghosts lock) (map snd (rev lshs1 ++ rev lshs2))));
         EX ns : list Z, (!!(Zlength ns = Zlength ghosts) &&
           fold_right_sepcon (firstn (Z.to_nat i - 3) (map (fun x => ghost gsh1 tint (vint (fst x)) (snd x)) (combine ns ghosts))));
         fold_right_sepcon (skipn (Z.to_nat i) (map Interp (map f_lock (combine (upto 3) flocks))));
         fold_right_sepcon (skipn (Z.to_nat i - 3) (map Interp (map g_lock (combine (upto 3) glocks))));
         data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6) (flocks ++ glocks) lvar0)).
  { go_lower; apply andp_right; [|rewrite app_nil_r; Exists [0; 0; 0]; entailer!].
    Intros.
    do 3 (destruct flocks; [Omega0|]).
    do 3 (destruct glocks; [Omega0|]).
    repeat rewrite Zlength_cons in *; unfold Z.succ in *.
    assert (flocks = []) by (apply Zlength_nil_inv; abstract omega).
    assert (glocks = []) by (apply Zlength_nil_inv; abstract omega).
    Transparent upto.
    subst; simpl.
    rewrite (lock_inv_isptr _ v), (lock_inv_isptr _ v0), (lock_inv_isptr _ v1), (lock_inv_isptr _ v2),
      (lock_inv_isptr _ v3), (lock_inv_isptr _ v4).
    rewrite !sepcon_assoc, !sepcon_andp_prop', !sepcon_andp_prop.
    repeat (apply derives_extract_prop; intro).
    apply prop_right; repeat split; auto. }
  { apply main_loop3; auto. }
  Intro ns; Intros.
  rewrite !Zfirstn_same; try (rewrite !Zlength_map, Zlength_app, !Zlength_rev; abstract omega).
  rewrite !map_app, !sepcon_app, !map_rev, !sepcon_rev.
  rewrite sepcon_comm; gather_SEP 1 2.
  rewrite <- sepcon_assoc, data_at_shares_join; [|rewrite Hglen2; auto].
  subst gsh'; rewrite data_at_shares_join; [|rewrite Hglen1; auto].
  rewrite sepcon_comm; gather_SEP 2 3.
  rewrite <- sepcon_assoc, lqueue_shares_join; [|rewrite Hlenl2; auto].
  subst lsh'; rewrite lqueue_shares_join; [|rewrite Hlenl1; auto].
  forward.
  forward_call (gsh1, gsh2, p, ghosts, ns, lock).
  { replace (Z.to_nat 6 - 3)%nat with (Z.to_nat 3)%nat by Omega0.
    rewrite Zfirstn_same; simpl.
    unfold fold_right at 3; cancel.
    { rewrite Zlength_map, Zlength_combine, Z.min_l; try abstract omega.
      subst ghosts; rewrite !Zlength_cons, Zlength_nil in *; abstract omega. } }
  forward.
  Exists lvar0; entailer!.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity |]).
eapply semax_func_cons_ext; try reflexivity.
{ intros; entailer!. }
{ admit. }
eapply semax_func_cons_ext; try reflexivity.
{ admit. }
{ admit. }
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons body_get_request.
semax_func_cons body_process_request.
semax_func_cons body_q_new.
semax_func_cons body_q_del.
semax_func_cons body_q_add.
semax_func_cons body_q_remove.
semax_func_cons body_f.
(* XX For some reason, precondition_closed can't prove that all the gvars
   aren't local variables. *)
apply semax_func_cons;
 [ reflexivity
 | repeat apply Forall_cons; try apply Forall_nil; auto; computable
 | unfold var_sizes_ok; repeat constructor; simpl; computable | reflexivity
 | | apply body_g | ].
{ precondition_closed.
  apply closed_wrtl_PROPx, closed_wrtl_LOCALx, closed_wrtl_SEPx.
  repeat constructor; apply closed_wrtl_gvar; unfold is_a_local; simpl;
    intros [? | ?]; try contradiction; discriminate. }
(* Here it's just missing an auto. *)
apply semax_func_cons;
 [ reflexivity
 | repeat apply Forall_cons; try apply Forall_nil; (*here*)auto; computable
 | unfold var_sizes_ok; repeat constructor; simpl; computable | reflexivity
 | precondition_closed | apply body_main | ].
apply semax_func_nil.
Admitted.
