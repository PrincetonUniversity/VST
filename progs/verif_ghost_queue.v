Require Import progs.conclib.
Require Import progs.ghost_queue.
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

Notation vint z := (Vint (Int.repr z)).

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
   SEP (lqueue Tsh sh2 newq ghosts lock; fold_right sepcon emp (map (ghost sh1 tint (vint (-1))) ghosts)).

Definition q_del_spec :=
 DECLARE _q_del
  WITH sh1 : share, sh2 : share, d : val, ghosts : list val, ns : list Z, lock : val
  PRE [ _tgt OF (tptr tqueue_t) ]
   PROP (sepalg.join sh1 sh2 Ews)
   LOCAL (temp _tgt d)
   SEP (lqueue Tsh sh2 d ghosts lock;
        fold_right sepcon emp (map (fun p => ghost sh1 tint (vint (fst p)) (snd p)) (combine ns ghosts)))
  POST [ tvoid ]
   PROP () LOCAL ()
   SEP (fold_right sepcon emp (map (fun p => ghost Ews tint (vint (fst p)) (snd p)) (combine ns ghosts))).

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

Definition f_lock_pred lsh tsh p' p lock lockt ghosts gsh2 :=
  Self_lock (Pred_list [Data_at _ lsh (tptr tqueue_t) p p';
    Field_at _ lsh tqueue_t [StructField _lock] lock p;
    Lock_inv lsh lock (lock_pred gsh2 p ghosts)]) tsh lockt.

Definition f_spec :=
 DECLARE _f
  WITH lockt : val, x : share * share * val * val * val * list val * share
  PRE [ _arg OF (tptr tvoid) ]
   let '(sh, tsh, p', p, lock, ghosts, gsh2) := x in
   PROP ()
   LOCAL (temp _arg lockt; gvar _q0 p')
   SEP (!!(readable_share sh /\ readable_share tsh) && emp;
        data_at sh (tptr tqueue_t) p p';
        lqueue sh gsh2 p ghosts lock;
        lock_inv tsh lockt (Interp (f_lock_pred sh tsh p' p lock lockt ghosts gsh2)))
  POST [ tptr tvoid ] PROP () LOCAL () SEP (emp).

Definition g_lock_pred lsh tsh p' p lock lockt ghosts gsh1 gsh2 g :=
  Self_lock (Pred_list [Data_at _ lsh (tptr tqueue_t) p p';
    Field_at _ lsh tqueue_t [StructField _lock] lock p;
    Lock_inv lsh lock (lock_pred gsh2 p ghosts);
    Exp _ (fun n => Ghost gsh1 tint (Vint (Int.repr n)) g)]) tsh lockt.

Definition g_spec :=
 DECLARE _g
  WITH lockt : val, x : share * share * Z * val * val * val * list val * nat * val * share * share
  PRE [ _arg OF (tptr tvoid) ]
   let '(sh, tsh, t, p', p, lock, ghosts, i, g, gsh1, gsh2) := x in
   PROP ()
   LOCAL (temp _arg lockt; gvar _q0 p')
   SEP (!!(readable_share sh /\ readable_share tsh /\ Int.min_signed <= t <= Int.max_signed /\
           sepalg.join gsh1 gsh2 Ews /\ nth_error ghosts i = Some g) && emp;
        data_at sh (tptr tqueue_t) p p';
        lqueue sh gsh2 p ghosts lock;
        lock_inv tsh lockt (Interp (g_lock_pred sh tsh p' p lock lockt ghosts gsh1 gsh2 g));
        ghost gsh1 tint (Vint (Int.repr t)) g)
  POST [ tptr tvoid ] PROP () LOCAL () SEP (emp).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Gprog : funspecs := augment_funspecs prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; makecond_spec; freecond_spec; wait_spec; signal_spec;
  malloc_spec; free_spec; get_request_spec; process_request_spec;
  q_new_spec; q_del_spec; q_add_spec; q_remove_spec; f_spec; main_spec].

Lemma all_ptrs : forall reqs,
  fold_right sepcon emp (map Interp (map (fun p => Exp val (fun d =>
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

Lemma precise_fold_right : forall l, Forall precise l -> precise (fold_right sepcon emp l).
Proof.
  induction l; simpl; auto; intros.
  inv H; apply precise_sepcon; auto.
Qed.

Lemma precise_request : forall sh p, readable_share sh ->
  precise (data_at_ sh trequest p).
Proof.
  intros; unfold data_at_, field_at_; unfold_field_at 1%nat.
  unfold field_at, at_offset; simpl.
  apply precise_sepcon; apply precise_andp2; rewrite by_value_data_at_rec_nonvolatile; auto.
Qed.

Lemma reqs_precise : forall r reqs ns1 ns2 r1 r2
  (Hreqs1 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap) (fold_right sepcon emp
    (map Interp (map (fun p => Exp _ (fun d => Data_at _ Tsh trequest (d, Vint (Int.repr (fst p))) (snd p)))
    (combine ns1 reqs)))) r1)
  (Hreqs2 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap) (fold_right sepcon emp
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
Qed.

Ltac join_inj := repeat match goal with H1 : sepalg.join ?a ?b ?c, H2 : sepalg.join ?a ?b ?d |- _ =>
    pose proof (sepalg.join_eq H1 H2); clear H1 H2; subst; auto end.

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
  fold_right sepcon emp (map Interp (map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p))
    (combine ns ghosts))) =
  fold_right sepcon emp (map Interp (map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p))
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
  fold_right sepcon emp (map Interp (map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p))
    (combine (remove_at i ns) (remove_at i ghosts)))) * ghost sh tint (Vint (Int.repr n)) g =
  fold_right sepcon emp (map Interp (map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p))
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

Lemma malloc_field_compatible : forall t p,
  legal_alignas_type t = true ->
  legal_cosu_type t = true ->
  complete_type cenv_cs t = true ->
  sizeof t < Int.modulus ->
  (alignof t | natural_alignment)%Z ->
  malloc_compatible (sizeof t) p -> field_compatible t [] p.
Proof.
  unfold malloc_compatible, field_compatible; intros.
  destruct p; try contradiction.
  match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; auto; simpl.
  - apply Z.lt_le_incl; auto.
  - etransitivity; eauto.
Qed.

Lemma body_get_request : semax_body Vprog Gprog f_get_request get_request_spec.
Proof.
  start_function.
  forward_call (sizeof trequest).
  { simpl; computable. }
  Intro p; normalize.
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

Lemma mods_repr : forall a b, 0 <= a <= Int.max_signed -> 0 < b <= Int.max_signed ->
  Int.mods (Int.repr a) (Int.repr b) = Int.repr (a mod b).
Proof.
  intros.
  unfold Int.mods.
  pose proof Int.min_signed_neg.
  rewrite Zquot.Zrem_Zmod_pos; repeat rewrite Int.signed_repr; auto; omega.
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

Lemma repeat_list_repeat : forall {A} n (x : A), repeat x n = list_repeat n x.
Proof.
  induction n; auto; simpl; intro.
  rewrite IHn; auto.
Qed.

Lemma sublist_repeat : forall {A} i j k (v : A), 0 <= i -> i <= j <= k ->
  sublist i j (repeat v (Z.to_nat k)) = repeat v (Z.to_nat (j - i)).
Proof.
  intros; repeat rewrite repeat_list_repeat; apply sublist_list_repeat; auto.
Qed.

Lemma body_q_new : semax_body Vprog Gprog f_q_new q_new_spec.
Proof.
  start_function.
  forward_call (sizeof tqueue_t).
  { simpl; computable. }
  Intro p; normalize.
  assert (align_attr noattr 4 | natural_alignment) by (exists 2; auto).
  assert (field_compatible tqueue_t [] p).
  { apply malloc_field_compatible; auto; simpl; computable. }
  rewrite memory_block_data_at_; auto.
  forward.
  normalize.
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
         fold_right sepcon emp (map (ghost Ews tint (vint (-1))) ghosts))).
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
  Intro addc; normalize.
  rewrite memory_block_data_at_; [|apply malloc_field_compatible; auto; simpl; computable].
  forward_call (addc, Tsh).
  { unfold tcond; cancel. }
  forward.
  forward_call (sizeof tint).
  { simpl; computable. }
  Intro remc; normalize.
  rewrite memory_block_data_at_; [|apply malloc_field_compatible; auto; simpl; computable].
  forward_call (remc, Tsh).
  { unfold tcond; cancel. }
  forward.
  forward_call (sizeof tlock).
  { simpl; computable. }
  Intro lock; normalize.
  rewrite memory_block_data_at_; [|apply malloc_field_compatible; auto; simpl; try computable].
  forward_call (lock, Tsh, lock_pred sh2 p ghosts).
  eapply semax_pre with (P' := PROP () LOCAL (temp _l lock; temp _c remc; temp _i (vint MAX);
      temp _q p; temp _newq p)
    SEP (lock_inv Tsh lock (Interp (lock_pred sh2 p ghosts)); cond_var Tsh remc; cond_var Tsh addc;
         @data_at CompSpecs Tsh tqueue_t (repeat (vint 0) (Z.to_nat MAX),
           (vint 0, (vint 0, (vint 0, (vint 0, (addc, remc))))), Vundef) p;
         fold_right sepcon emp (map (ghost Ews tint (vint (-1))) ghosts))).
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
    rewrite sepcon_assoc, (sepcon_comm _ (fold_right sepcon emp Frame)), <- sepcon_assoc.
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
  Exists p lock; normalize.
  apply andp_right; [apply prop_right; auto|].
  unfold lqueue; simpl; cancel.
Qed.

Lemma body_q_del : semax_body Vprog Gprog f_q_del q_del_spec.
Proof.
  start_function.
  unfold lqueue; rewrite lock_inv_isptr; normalize.
  forward.
  forward_call (lock, Tsh, lock_pred sh2 d ghosts).
  { simpl; cancel. }
  forward_call (lock, Tsh, lock_pred sh2 d ghosts).
  { split; auto; apply inv_positive. }
  forward_call (lock, sizeof tlock).
  { repeat rewrite sepcon_assoc; apply sepcon_derives; [apply data_at__memory_block_cancel | cancel]. }
  forward.
  simpl; Intros reqs head next addc remc ns'.
  rewrite data_at_isptr, (cond_var_isptr _ addc), (cond_var_isptr _ remc); normalize.
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
         fold_right sepcon emp (map (ghost Ews tint (vint (-1))) ghosts))).
  { go_lower.
    do 2 (apply andp_right; [apply prop_right; repeat split; auto|]); unfold fold_right; cancel.
    unfold data_at_, field_at_, data_at, field_at; normalize; simpl.
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
  unfold lqueue; rewrite lock_inv_isptr; normalize.
  forward.
  forward_call (lock, sh, lock_pred gsh2 p ghosts).
  simpl; Intros reqs head next addc remc ns.
  forward.
  rewrite data_at_isptr; normalize.
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
    apply andp_right; [apply prop_right; repeat split; auto |
      apply andp_right; [apply prop_right; repeat split; auto | normalize; unfold fold_right, app; cancel]]. }
  { go_lower; entailer'. }
  { simpl; normalize.
    forward.
    { go_lower.
      rewrite cond_var_isptr; normalize; entailer'. }
    forward_call (addc0, lock, Tsh, sh, lock_pred gsh2 p ghosts).
    { simpl.
      Exists reqs0 head0 next0 addc0 remc0 ns0; cancel.
      subst Frame; instantiate (1 := [field_at sh tqueue_t [StructField _lock] lock p;
        data_at Tsh trequest (d, t) request]); simpl; cancel.
      apply andp_right; [normalize; cancel | cancel]. }
    simpl; Intros reqs1 head1 next1 addc1 remc1 ns1; normalize.
    forward.
    Exists (reqs1, head1, next1, addc1, remc1, ns1).
    (* timeout 70 entailer. XX times out *)
    go_lower.
    apply andp_right; [apply prop_right; repeat split; auto |
      apply andp_right; [apply prop_right; repeat split; auto | normalize; cancel]]. }
  simpl; normalize.
  rewrite Int.signed_repr, Zlength_correct in HRE.
  freeze [1; 2; 3; 4; 5] FR; forward.
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
  rewrite (cond_var_isptr _ remc0); normalize.
  forward.
  freeze [0; 2; 3; 4; 5; 6] FR; time forward_call (remc0, Tsh).
  thaw FR.
  rewrite upd_rotate; auto; try rewrite Zlength_complete; try rewrite Zlength_map; auto.
  rewrite Zminus_mod_idemp_l, Z.add_simpl_l, (Zmod_small (Zlength reqs0));
    [|rewrite Zlength_correct; unfold MAX; omega].
  erewrite <- Zlength_map, upd_complete; [|rewrite Zlength_map, Zlength_correct; auto].
  time forward_call (lock, sh, lock_pred gsh2 p ghosts). (* 29s *)
  { simpl.
    Exists (reqs0 ++ [(next0, request)]) head0 (next0 + 1) addc0 remc0 ns0; unfold fold_right at 1; cancel.
    rewrite (field_at_isptr _ trequest); normalize.
    rewrite map_app, Zlength_app, Zlength_cons, Zlength_nil, Zlength_map.
    unfold sem_mod; simpl sem_binarith.
    unfold both_int; simpl force_val.
    rewrite andb_false_intro2; [|simpl; auto].
    simpl force_val.
    rewrite mods_repr; try computable.
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
    Exists d; cancel.
    { pose proof (Z_mod_lt (head0 + Zlength reqs0) MAX).
      split; try omega.
      transitivity MAX; simpl in *; [omega | unfold MAX; computable]. } }
  { split; auto; split; [apply inv_precise | apply inv_positive]. }
  forward.
  { unfold lqueue; simpl; cancel. }
  { pose proof Int.min_signed_neg; split; [rewrite Zlength_correct; omega|].
    transitivity MAX; [auto | unfold MAX; computable]. }
Admitted.

Lemma Znth_head : forall reqs head m d, Zlength reqs <= m -> 0 <= head < m ->
  Zlength reqs > 0 ->
  Znth head (rotate (complete m reqs) head m) d = Znth 0 reqs d.
Proof.
  intros; unfold rotate.
  assert (Zlength (sublist (m - head) (Zlength (complete m reqs)) (complete m reqs)) = head) as Hlen.
  { rewrite Zlength_sublist; rewrite Zlength_complete; omega. }
  rewrite app_Znth2; rewrite Hlen; [|omega].
  rewrite Zminus_diag.
  rewrite Znth_sublist; try omega.
  rewrite Znth_complete; auto; omega.
Qed.

Lemma Znth_repeat : forall {A} (x : A) n i, Znth i (repeat x n) x = x.
Proof.
  induction n; simpl; intro.
  - apply Znth_nil.
  - destruct (Z_lt_dec i 0); [apply Znth_underflow; auto|].
    destruct (eq_dec i 0); [subst; apply Znth_0_cons | rewrite Znth_pos_cons; eauto; omega].
Qed.

Lemma rotate_1 : forall v l n m, 0 <= n < m -> Zlength l < m ->
  rotate (upd_Znth 0 (complete m (v :: l)) (Vint (Int.repr 0))) n m =
  rotate (complete m l) ((n + 1) mod m) m.
Proof.
  intros.
  unfold complete at 1; simpl.
  unfold upd_Znth; simpl.
  rewrite Zlength_cons; simpl.
  rewrite sublist_1_cons, sublist_same; auto; [|omega].
  unfold rotate.
  rewrite Zlength_cons; simpl.
  rewrite sublist_S_cons; [|omega].
  rewrite sublist_0_cons; [|omega].
  destruct (eq_dec (n + 1) m).
  - subst; rewrite Z.mod_same; [|omega].
    autorewrite with sublist.
    rewrite Zlength_complete, sublist_nil; [|omega].
    rewrite sublist_same; auto; [|rewrite Zlength_complete; omega].
    rewrite <- app_assoc; unfold complete.
    repeat rewrite Z2Nat.inj_add; try omega.
    rewrite NPeano.Nat.add_sub_swap with (p := length l); [|rewrite Zlength_correct in *; Omega0].
    rewrite repeat_plus; simpl; do 3 f_equal; omega.
  - rewrite Zmod_small; [|omega].
    rewrite (sublist_split (m - (n + 1)) (Zlength (complete m l) - 1)); try rewrite Zlength_complete; try omega.
    rewrite <- app_assoc, (sublist_one (m - 1)) with (d := vint 0); try rewrite Zlength_complete; try omega; simpl.
    assert (length l < Z.to_nat m)%nat by (rewrite Zlength_correct in *; Omega0).
    unfold complete.
    replace (Z.to_nat m - length l)%nat with (Z.to_nat m - S (length l) + 1)%nat; [|omega].
    rewrite repeat_plus, app_assoc; simpl.
    repeat rewrite Zlength_app.
    assert (m - 1 = Zlength l + Zlength (repeat (vint 0) (Z.to_nat m - S (Datatypes.length l)))) as Heq.
    { rewrite Zlength_repeat, Nat2Z.inj_sub, Z2Nat.id, Nat2Z.inj_succ, <- Zlength_correct; omega. }
    rewrite (sublist_app1 _ _ _ (_ ++ _)); try rewrite Zlength_app; try omega.
    rewrite (sublist_app1 _ _ _ (_ ++ _)); try rewrite Zlength_app; try omega.
    f_equal; f_equal; try omega.
    + rewrite app_Znth2, Zlength_app, Heq, Zminus_diag, Znth_0_cons; auto.
      rewrite Zlength_app; omega.
    + f_equal; omega.
Qed.

Lemma body_q_remove : semax_body Vprog Gprog f_q_remove q_remove_spec.
Proof.
  start_function.
  unfold lqueue; rewrite lock_inv_isptr; normalize.
  forward.
  forward_call (lock, sh, lock_pred gsh2 p ghosts).
  simpl; Intros reqs head next addc remc ns.
  forward.
  rewrite data_at_isptr; normalize.
  forward.
  forward_while (EX reqs : list (Z * val), EX head : Z, EX next : Z, EX addc : val, EX remc : val,
    EX ns : list Z, PROP ()
   LOCAL (temp _len (vint (Zlength reqs)); temp _q p; temp _l lock; temp _tgt p)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 p ghosts));
        Interp (lock_pred' gsh2 p reqs head next addc remc ghosts ns);
        @field_at CompSpecs sh tqueue_t [StructField _lock] lock p; ghost gsh1 tint (Vint (Int.repr t)) g)).
  { Exists reqs head next addc remc ns; go_lower.
    apply andp_right; [apply prop_right; repeat split; auto |
      apply andp_right; [apply prop_right; repeat split; auto | normalize; cancel]]. }
  { go_lower; entailer'. }
  { simpl; normalize.
    forward.
    { go_lower.
      rewrite (cond_var_isptr _ remc0); normalize; entailer'. }
    forward_call (remc0, lock, Tsh, sh, lock_pred gsh2 p ghosts).
    { simpl.
      Exists reqs0 head0 next0 addc0 remc0 ns0; cancel.
      subst Frame; instantiate (1 := [field_at sh tqueue_t [StructField _lock] lock p;
        ghost gsh1 tint (Vint (Int.repr t)) g]); simpl; cancel.
      apply andp_right; [normalize; cancel | cancel]. }
    simpl; Intros reqs1 head1 next1 addc1 remc1 ns1; normalize.
    forward.
    Exists (reqs1, head1, next1, addc1, remc1, ns1).
    go_lower.
    apply andp_right; [apply prop_right; repeat split; auto |
      apply andp_right; [apply prop_right; repeat split; auto | normalize; cancel]]. }
  simpl; normalize.
  assert (Zlength reqs0 > 0).
  { rewrite Zlength_correct in *.
    destruct (length reqs0); [|rewrite Nat2Z.inj_succ; omega].
    contradiction HRE; auto. }
  forward.
  forward.
  { go_lower; normalize.
    rewrite Znth_head; try rewrite Zlength_map; try omega.
    repeat rewrite <- sepcon_assoc.
    rewrite (sepcon_comm _ (_ (map _ _))).
    rewrite map_app, sepcon_app.
    repeat rewrite sepcon_assoc; rewrite sepcon_comm.
    rewrite sepcon_assoc.
    eapply derives_trans; [apply sepcon_derives; [apply prop_and_same_derives, all_ptrs; auto |
      apply derives_refl]|].
    normalize; apply prop_right.
    apply Forall_Znth.
    { rewrite Zlength_map; omega. }
    eapply Forall_impl; [|eauto].
    destruct a; auto. }
  forward.
  forward.
  { go_lower; normalize; simpl.
    apply prop_right; rewrite andb_false_intro2; simpl; auto. }
  forward.
  rewrite cond_var_isptr; normalize.
  forward.
  freeze [0; 2; 3; 4; 5] FR; forward_call (addc0, Tsh).
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
  rewrite mods_repr; try computable.
  unfold Z.succ; rewrite Z.add_simpl_r.
  rewrite map_app, sepcon_app; simpl.
  Intro d.
  assert (i < length ghosts)%nat as Hlt by (rewrite <- nth_error_Some; intro X; rewrite X in *; discriminate).
  assert (length ns0 = length ghosts) as Hlen by (repeat rewrite Zlength_correct in *; Omega0).
  replace (length ghosts) with (length ns0) in Hlt; auto.
  freeze [0; 1; 2; 4; 5; 6; 7] FR.
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
  normalize.
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
    unfold fold_right at 1; cancel.
    rewrite (sepcon_comm (ghost _ _ _ _)), sepcon_comm.
    repeat rewrite <- sepcon_assoc.
    rewrite add_nth_ghost; auto.
    rewrite Zplus_mod_idemp_l, <- Z.add_assoc, (Z.add_comm 1).
    simpl; rewrite map_app, sepcon_app; unfold fold_right at 3; cancel. }
  { split; auto; split; [apply inv_precise | apply inv_positive]. }
  forward.
  Exists (fst p0) (snd p0) d; normalize.
  apply andp_right; [apply prop_right | unfold lqueue; simpl; cancel].
  repeat split; auto; try omega.
  rewrite Znth_head; auto; rewrite Zlength_cons, Zlength_map; omega.
  { split; try omega.
    transitivity MAX; [omega | unfold MAX; computable]. }
Qed.

Opaque lock_pred.

(*Lemma upd_complete' : forall l x n, (length l < n)%nat -> 
  upd_Znth (Zlength l) (map Vint (map Int.repr l) ++ repeat Vundef (n - length l)) (Vint (Int.repr x)) =
  map Vint (map Int.repr (l ++ [x])) ++ repeat Vundef (n - length (l ++ [x])).
Proof.
  intros.
  rewrite upd_Znth_app2.
  repeat rewrite Zlength_correct; repeat rewrite map_length; repeat rewrite <- Zlength_correct.
  rewrite Zminus_diag.
  rewrite app_length; simpl plus.
  destruct (n - length l)%nat eqn: Hminus; [omega|].
  replace (n - (length l + 1))%nat with n0 by omega.
  unfold upd_Znth, sublist.sublist; simpl.
  rewrite Zlength_cons.
  unfold Z.succ; rewrite Z.add_simpl_r.
  rewrite Zlength_correct, Nat2Z.id, firstn_exact_length.
  repeat rewrite map_app; rewrite <- app_assoc; auto.
  { repeat rewrite Zlength_correct; repeat rewrite map_length; omega. }
Qed.*)

Lemma precise_False : precise (!!False).
Proof.
  repeat intro.
  inversion H.
Qed.

Lemma lock_precise : forall sh p lock (Hsh : readable_share sh),
  precise (field_at sh tqueue_t [StructField _lock] lock p).
Proof.
  intros.
  unfold field_at, at_offset; apply precise_andp2.
  rewrite data_at_rec_eq; simpl; auto.
Qed.

Lemma f_inv_precise : forall sh tsh p' p lock lockt ghosts gsh2 (Hsh : readable_share sh),
  precise (Interp (f_lock_pred sh tsh p' p lock lockt ghosts gsh2)).
Proof.
  intros; simpl.
  apply selflock_precise; repeat apply precise_sepcon; auto.
  apply lock_precise; auto.
Qed.

Lemma f_inv_positive : forall sh tsh p' p lock lockt ghosts gsh2,
  positive_mpred (Interp (f_lock_pred sh tsh p' p lock lockt ghosts gsh2)).
Proof.
  intros; apply selflock_positive.
  simpl; apply positive_sepcon2, positive_sepcon2, positive_sepcon1, lock_inv_positive.
Qed.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  rewrite (lock_inv_isptr _ lockt); normalize.
  unfold lqueue; rewrite field_at_isptr; normalize.
  forward.
  match goal with |-semax _ ?P _ _ => forward_for_simple_bound 3 (EX i : Z, P) end.
  { entailer. }
  { forward_call tt.
    Intro x; destruct x as ((req, d), t).
    forward_call (sh, p, lock, req, d, t, ghosts, gsh2).
    { unfold lqueue; cancel. }
    unfold lqueue; entailer. }
  forward_call (lockt, tsh, f_lock_pred sh tsh p' p lock lockt ghosts gsh2).
  { simpl.
    rewrite selflock_eq at 2; cancel.
    subst Frame; instantiate (1 := []); simpl; normalize; apply lock_inv_later. }
  { split; auto; repeat split; [apply f_inv_precise | apply f_inv_positive | apply selflock_rec]; auto. }
  forward.
Qed.

Lemma g_inv_precise : forall sh tsh p' p lock lockt ghosts gsh1 gsh2 g (Hsh : readable_share sh),
  precise (Interp (g_lock_pred sh tsh p' p lock lockt ghosts gsh1 gsh2 g)).
Proof.
  intros; simpl.
  apply selflock_precise; repeat apply precise_sepcon; auto.
  - apply lock_precise; auto.
  - eapply derives_precise; [|apply ghost_precise].
    intros ? (? & ?).
    rewrite interp_ghost in *; eexists; eauto.
Qed.

Lemma g_inv_positive : forall sh tsh p' p lock lockt ghosts gsh1 gsh2 g,
  positive_mpred (Interp (g_lock_pred sh tsh p' p lock lockt ghosts gsh1 gsh2 g)).
Proof.
  intros; apply selflock_positive.
  simpl; apply positive_sepcon2, positive_sepcon2, positive_sepcon1, lock_inv_positive.
Qed.

Lemma body_g : semax_body Vprog Gprog f_g g_spec.
Proof.
  start_function.
  rewrite (lock_inv_isptr _ lockt); normalize.
  unfold lqueue; rewrite field_at_isptr; normalize.
  forward.
  forward_for_simple_bound 3 (EX i : Z, PROP ()
      LOCAL (temp _q1 p; lvar _res (tarray tint 3) lvar0; temp _arg lockt; gvar _q0 p')
      SEP (EX n' : Z, EX ld : list Z, !! (Int.min_signed <= n' <= Int.max_signed /\
             Zlength ld = i /\ Sorted Z.lt ld /\ Forall (fun z => Int.min_signed <= z <= n') ld) &&
             data_at Tsh (tarray tint 3) (map Vint (map Int.repr ld) ++ repeat Vundef (3 - length ld)%nat) lvar0 *
             ghost gsh1 tint (Vint (Int.repr n')) g;
           @field_at CompSpecs sh tqueue_t [StructField _lock] lock p; lock_inv sh lock (Interp (lock_pred gsh2 p ghosts));
           @data_at CompSpecs sh (tptr tqueue_t) p p';
           lock_inv tsh lockt (Interp (g_lock_pred sh tsh p' p lock lockt ghosts gsh1 gsh2 g)))).
  { entailer.
    Exists t ([] : list Z); simpl; entailer!.
    unfold data_at_, data_at, field_at_; simpl; apply derives_refl. }
  { Intros n1 ld; normalize.
    forward_call (sh, n1, lock, buf, ends, len, next, cprod, ccon, ghosts, i, g, gsh1, gsh2).
    Intro x; destruct x as ((t', req), d).
    forward_call (req, d, t').
    Intro v.
    forward.
    subst; simpl force_val.
    rewrite upd_complete'; [|rewrite Zlength_correct in *; omega].
    entailer.
    Exists t' (ld ++ [t']); entailer!.
    rewrite Zlength_app; simpl in *; split; [omega|].
    split; auto; split.
    - apply SetoidList.SortA_app with (eqA := eq); auto; intros.
      rewrite SetoidList.InA_alt in *;
        repeat match goal with H : exists _, _ |- _ => destruct H as (? & ? & ?); subst end.
      match goal with H : In _ [_] |- _ => destruct H; [subst | contradiction] end.
      match goal with H : In _ _, H' : Forall _ _ |- _ => rewrite Forall_forall in H';
        specialize (H' _ H); omega end.
    - rewrite Forall_app; split; [|constructor; auto; omega].
      eapply Forall_impl; [|eauto]; intros; simpl in *; omega. }
  Intros n' ld; normalize.
  forward_call (Vptr lockt o, tsh, t_lock_pred sh tsh cprod ccon lock (Vptr lockt o)
                                               buf ends len next ghosts gsh1 gsh2 g).
  { simpl.
    rewrite selflock_eq at 2; cancel.
    Exists n'; rewrite interp_ghost; cancel.
    rewrite sepcon_comm; apply sepcon_derives; [apply lock_inv_later | cancel]. }
  { split; auto; repeat split; [apply t_inv_precise | apply t_inv_positive | apply selflock_rec]; auto. }
  (* timeout 70 forward. XX times out, despite being just a return *)
  eapply semax_pre; [|apply semax_return].
  subst POSTCONDITION; unfold abbreviate.
  go_lowerx; normalize.
  unfold frame_ret_assert; simpl; entailer'.
  Exists lvar0; normalize; cancel.
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

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  name q0 _q0.
  start_function.
  destruct split_Ews as (sh1 & sh2 & Hr1 & Hr2 & Hsh).
  apply ghost_alloc.
  apply new_ghost with (t := tint)(v := Vint (Int.repr (-1))); Intro g1.
  apply new_ghost with (t := tint)(v := Vint (Int.repr (-1))); Intro g2.
  apply new_ghost with (t := tint)(v := Vint (Int.repr (-1))); Intro g3.
  set (ghosts := [g1; g2; g3]).
  forward_call (sh1, sh2, ghosts).
  { subst ghosts; simpl; cancel. }
  Intro x; destruct x as (p, lock); simpl.
  forward.
  rewrite <- seq_assoc.
  destruct (split_readable_share _ Hr1) as (sh' & tsh2 & Hr' & ? & Hsh').
  destruct (split_readable_share _ Hr') as (sh0 & tsh3 & ? & ? & Htsh).
  (* break apart array into 3x data_at_ *)
  rewrite data_at__isptr; normalize.
  destruct lockt as [| | | | | b o]; try contradiction.
  eapply semax_pre with (P' := PROP ( )
    LOCAL (gvar _next next; gvar _buf buf; gvar _requests_producer cprod;
           gvar _requests_consumer ccon; gvar _ends ends; gvar _length len; gvar _thread_locks (Vptr b o);
           gvar _requests_lock lock)
    SEP (G'; cond_var Ews ccon; cond_var Ews cprod;
         lock_inv Ews lock (Interp (lock_pred sh2 buf ends len next ghosts));
         ghost sh1 tint (Vint (Int.repr (-1))) g3;
         ghost sh1 tint (Vint (Int.repr (-1))) g2;
         ghost sh1 tint (Vint (Int.repr (-1))) g1;
         data_at_ Ews tlock (Vptr b o); data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 16)));
         data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 32))))).
  { entailer!.
    unfold data_at_, field_at_, field_at, at_offset; simpl.
    rewrite int_add_repr_0_r.
    rewrite data_at_rec_eq; simpl.
    unfold array_pred, aggregate_pred.array_pred, at_offset, default_val, unfold_reptype, Znth; simpl.
    normalize.
    apply andp_right; [apply prop_right | apply derives_refl].
    unfold field_compatible in *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    pose proof (Int.unsigned_range_2 o); simpl in *.
    repeat rewrite <- (Int.repr_unsigned o), add_repr.
    repeat rewrite Int.unsigned_repr; unfold Int.max_unsigned; try omega.
    unfold align_attr, noattr; simpl.
    repeat split; auto; simpl in *; try omega; apply Z.divide_add_r; auto.
    - apply Zdivide_intro with (q := 8); auto.
    - apply Zdivide_intro with (q := 4); auto. }
  forward_for_simple_bound 3 (EX i : Z, let s1 := nth (Z.to_nat i) [Ews; sh1; sh'] sh0 in
    PROP ()
    LOCAL (gvar _next next; gvar _buf buf; gvar _requests_producer cprod; gvar _requests_consumer ccon;
           gvar _ends ends; gvar _length len; gvar _thread_locks (Vptr b o); gvar _requests_lock lock)
   (SEPx ([G'; cond_var s1 ccon; cond_var s1 cprod;
           lock_inv s1 lock (Interp (lock_pred sh2 buf ends len next ghosts))] ++
          firstn (Z.to_nat i) [lock_inv sh1 (Vptr b o) (Interp (t_lock_pred sh2 sh2 cprod ccon lock
              (Vptr b o) buf ends len next ghosts sh1 sh2 g1));
            lock_inv sh1 (Vptr b (Int.add o (Int.repr 16))) (Interp (t_lock_pred tsh2 sh2 cprod ccon lock
              (Vptr b (Int.add o (Int.repr 16))) buf ends len next ghosts sh1 sh2 g2));
            lock_inv sh1 (Vptr b (Int.add o (Int.repr 32))) (Interp (t_lock_pred tsh3 sh2 cprod ccon lock
              (Vptr b (Int.add o (Int.repr 32))) buf ends len next ghosts sh1 sh2 g3))] ++
          skipn (Z.to_nat i) (map (ghost sh1 tint (Vint (Int.repr (-1)))) [g1; g2; g3]) ++
          skipn (Z.to_nat i) [data_at_ Ews tlock (Vptr b o);
                              data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 16)));
                              data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 32)))]))).
  { go_lower; simpl.
    apply andp_right; [apply prop_right; auto|].
    apply andp_right; [apply prop_right; repeat split; auto | cancel]. }
  { set (lockt := Vptr b (Int.add o (Int.repr (16 * i)))).
    set (lsh := nth (Z.to_nat i) [sh2; tsh2; tsh3] sh0).
    set (s0 := nth (Z.to_nat i) [Ews; sh1; sh'] sh0). 
    set (s1 := nth (S (Z.to_nat i)) [Ews; sh1; sh'] sh0).
    set (g := nth (Z.to_nat i) ghosts (Vint (Int.repr 0))).
    assert (sepalg.join s1 lsh s0 /\ readable_share lsh) as (Hshi & ?).
    { destruct (eq_dec i 0); [|destruct (eq_dec i 1); [|assert (i = 2) by omega]]; subst;
        subst lsh s0 s1; auto. }
    eapply semax_seq'.
(* Modified forward_call without automatic typechecking *)
Ltac forward_call_id00_wow' witness := 
  let Frame := fresh "Frame" in evar (Frame: list (mpred));
      eapply (semax_call_id00_wow witness Frame);
 [ check_function_name | lookup_spec_and_change_compspecs CompSpecs
 | find_spec_in_globals | check_result_type | check_parameter_types
 | check_prove_local2ptree
 | (*check_typecheck*)
 | check_funspec_precondition
 | check_prove_local2ptree
 | check_cast_params | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right at 1 2; cancel
 | cbv beta iota; 
    repeat rewrite exp_uncurry;
    try rewrite no_post_exists0; 
    first [reflexivity | extensionality; simpl; reflexivity]
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto
 ].
    forward_call_id00_wow' (lockt, Ews, t_lock_pred lsh sh2 cprod ccon lock lockt
      buf ends len next ghosts sh1 sh2 g).
    { go_lowerx; unfold tc_exprlist; simpl.
      unfold liftx, lift_uncurry_open, lift in *; simpl in *.
      apply andp_right; apply prop_right.
      - eapply eval_var_isptr; eauto.
      - unfold gvar_denote, eval_var in *.
        destruct (Map.get (ve_of rho) _thread_locks) as [(?, ?)|]; [contradiction|].
        destruct (ge_of rho _thread_locks); [|contradiction].
        unfold sem_add_pi.
        replace (eval_id _i__1 rho) with (Vint (Int.repr i)) by auto; auto. }
    { subst Frame; instantiate (1 := [G'; cond_var s0 ccon; cond_var s0 cprod;
        lock_inv s0 lock (Interp (lock_pred sh2 buf ends len next ghosts))] ++
        firstn (Z.to_nat i) [lock_inv sh1 (Vptr b o)
        (Interp (t_lock_pred sh2 sh2 cprod ccon lock (Vptr b o) buf ends len next ghosts sh1 sh2 g1));
        lock_inv sh1 (Vptr b (Int.add o (Int.repr 16)))
        (Interp (t_lock_pred tsh2 sh2 cprod ccon lock (Vptr b (Int.add o (Int.repr 16))) buf ends len next ghosts sh1
             sh2 g2));
        lock_inv sh1 (Vptr b (Int.add o (Int.repr 32)))
        (Interp (t_lock_pred tsh3 sh2 cprod ccon lock (Vptr b (Int.add o (Int.repr 32))) buf ends len next ghosts sh1
             sh2 g3))] ++
        skipn (Z.to_nat i) (map (ghost sh1 tint (Vint (Int.repr (-1)))) [g1; g2; g3]) ++
        skipn (S (Z.to_nat i)) [data_at_ Ews tlock (Vptr b o);
          data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 16)));
          data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 32)))]).
      repeat rewrite sepcon_app; cancel.
      destruct (eq_dec i 0); [|destruct (eq_dec i 1); [|assert (i = 2) by omega]]; subst; subst lockt;
        simpl; cancel.
      rewrite Int.add_zero; auto. }
    Intro a.
    simpl; subst MORE_COMMANDS; unfold abbreviate.
    get_global_function'' _f; normalize.
    apply extract_exists_pre; intros f_.
    match goal with |-context[func_ptr' ?P] => set (spec := P) end.
    rewrite semax_seq_skip; eapply semax_seq'.
    forward_call_id00_wow' (f_, lockt, existT (fun ty => ty * (ty -> val -> Pred))%type
      (share * share * Z * val * val * val * val * val * val * val * list val * nat * val * share * share)%type
      ((lsh, sh2, -1, lock, buf, ends, len, next, cprod, ccon, ghosts, Z.to_nat i, g, sh1, sh2),
     fun (x : (share * share * Z * val * val * val * val * val * val * val * list val * nat * val * share * share)) (lockt : val) =>
     let '(sh, tsh, t, lock, buf, ends, len, next, cprod, ccon, ghosts, i, g, gsh1, gsh2) := x in
     Pred_list [Pred_prop (readable_share sh /\ readable_share tsh /\ Int.min_signed <= t <= Int.max_signed /\
                           sepalg.join gsh1 gsh2 Ews /\ nth_error ghosts i = Some g);
       Lock_inv sh lock (lock_pred gsh2 p ghosts);
       Lock_inv tsh lockt (t_lock_pred sh tsh cprod ccon lock lockt buf ends len next ghosts gsh1 gsh2 g);
       Cond_var _ sh cprod; Cond_var _ sh ccon; Ghost gsh1 tint (Vint (Int.repr t)) g])).
    + go_lowerx; unfold tc_exprlist; simpl.
      unfold liftx, lift_uncurry_open, lift in *; simpl in *.
      apply andp_right; apply prop_right.
      * eapply eval_var_isptr; eauto.
      * unfold gvar_denote, eval_var in *.
        destruct (Map.get (ve_of rho) _thread_locks) as [(?, ?)|]; [contradiction|].
        destruct (ge_of rho _thread_locks); [|contradiction].
        unfold sem_add_pi.
        replace (eval_id _i__1 rho) with (Vint (Int.repr i)) by auto; auto.
    + simpl.
      Exists _arg.
      Exists (fun x : share * share * Z * _ * _ * _ * _ * val * _ * _ * list val * nat * val * share * share =>
        let '(sh, tsh, t, lock, buf, ends, len, next, cprod, ccon, ghosts, i, g, gsh1, gsh2) := x in
        [(_buf, buf); (_ends, ends); (_length, len); (_next, next); (_requests_lock, lock);
         (_requests_producer, cprod); (_requests_consumer, ccon)]).
      subst Frame; instantiate (1 := [G'; cond_var s1 ccon; cond_var s1 cprod;
         lock_inv s1 lock (Interp (lock_pred sh2 buf ends len next ghosts))] ++
        firstn (Z.to_nat i) [lock_inv sh1 (Vptr b o) (Interp (t_lock_pred sh2 sh2 cprod ccon lock
            (Vptr b o) buf ends len next ghosts sh1 sh2 g1));
          lock_inv sh1 (Vptr b (Int.add o (Int.repr 16))) (Interp (t_lock_pred tsh2 sh2 cprod ccon lock
            (Vptr b (Int.add o (Int.repr 16))) buf ends len next ghosts sh1 sh2 g2));
          lock_inv sh1 (Vptr b (Int.add o (Int.repr 32))) (Interp (t_lock_pred tsh3 sh2 cprod ccon lock
            (Vptr b (Int.add o (Int.repr 32))) buf ends len next ghosts sh1 sh2 g3))] ++
        lock_inv sh1 lockt (Interp (t_lock_pred lsh sh2 cprod ccon lock lockt
            buf ends len next ghosts sh1 sh2 g)) ::
        skipn (S (Z.to_nat i)) (map (ghost sh1 tint (Vint (Int.repr (-1)))) [g1; g2; g3]) ++
        skipn (S (Z.to_nat i)) [data_at_ Ews tlock (Vptr b o);
                            data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 16)));
                            data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 32)))]).
      repeat rewrite sepcon_app; simpl.
      repeat rewrite sepcon_app; simpl.
      repeat rewrite sepcon_assoc; apply sepcon_derives.
      { evar (body : mpred); replace (func_ptr' _ _) with body; [subst body; apply derives_refl|].
        subst body spec; f_equal; f_equal.
        extensionality.
        destruct x as (?, ((((((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?)); simpl.
        f_equal; f_equal.
        unfold SEPx; simpl; normalize.
        rewrite interp_ghost; reflexivity. }
      rewrite <- (sepcon_emp (_ * _)), sepcon_comm; apply sepcon_derives.
      { apply andp_right; auto; apply prop_right; split; [|split; [|split; [|split]]]; auto; try computable.
        subst g; apply nth_error_nth.
        subst ghosts; simpl; Omega0. }
      rewrite interp_ghost; normalize.
      replace (fold_right sepcon emp (skipn _ (ghost _ _ _ _ :: _))) with
        (ghost sh1 tint (Vint (Int.repr (-1))) g * fold_right sepcon emp (skipn (Z.to_nat i)
         [ghost sh1 tint (Vint (Int.repr (-1))) g2;
          ghost sh1 tint (Vint (Int.repr (-1))) g3])).
      apply sepalg.join_comm in Hshi.
      rewrite <- (lock_inv_join _ _ _ _ _ Hshi).
      repeat rewrite <- (cond_var_join _ _ _ _ Hshi).
      erewrite <- lock_inv_join; eauto; cancel.
      rewrite sepcon_comm; apply derives_refl.
      { destruct (eq_dec i 0); [|destruct (eq_dec i 1); [|assert (i = 2) by omega]]; subst; subst g; auto. }
    + Intro x; forward.
      go_lower; normalize.
      apply andp_right; [apply prop_right; repeat split; auto; omega|].
      rewrite Z2Nat.inj_add; try omega.
      rewrite <- firstn_app, <- firstn_1_skipn with (d := FF); [|simpl; Omega0].
      repeat rewrite sepcon_app; simpl; rewrite sepcon_app.
      subst s1; repeat rewrite NPeano.Nat.add_1_r; try omega; simpl; cancel.
      destruct (eq_dec i 0); [|destruct (eq_dec i 1); [|assert (i = 2) by omega]]; subst; subst lockt;
        simpl; try rewrite Int.add_zero; auto. }
  rewrite <- seq_assoc.
  forward_for_simple_bound 3 (EX i : Z,
    PROP ()
    LOCAL (gvar _next next; gvar _buf buf; gvar _requests_producer cprod; gvar _requests_consumer ccon;
           gvar _ends ends; gvar _length len; gvar _thread_locks (Vptr b o); gvar _requests_lock lock)
   (SEPx (G' :: map (fun s1 => cond_var s1 ccon * cond_var s1 cprod *
                         lock_inv s1 lock (Interp (lock_pred sh2 buf ends len next ghosts)))
           (sh0 :: firstn (Z.to_nat i) [sh2; tsh2; tsh3]) ++
         skipn (Z.to_nat i) [lock_inv sh1 (Vptr b o) (Interp (t_lock_pred sh2 sh2 cprod ccon lock
           (Vptr b o) buf ends len next ghosts sh1 sh2 g1));
         lock_inv sh1 (Vptr b (Int.add o (Int.repr 16))) (Interp (t_lock_pred tsh2 sh2 cprod ccon lock
           (Vptr b (Int.add o (Int.repr 16))) buf ends len next ghosts sh1 sh2 g2));
         lock_inv sh1 (Vptr b (Int.add o (Int.repr 32))) (Interp (t_lock_pred tsh3 sh2 cprod ccon lock
           (Vptr b (Int.add o (Int.repr 32))) buf ends len next ghosts sh1 sh2 g3))] ++
         firstn (Z.to_nat i) (map (EX n : Z, ghost sh1 tint (Vint (Int.repr n))) [g1; g2; g3]) ++
         firstn (Z.to_nat i) [data_at_ Ews tlock (Vptr b o);
                              data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 16)));
                              data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 32)))]))).
  { go_lower; simpl.
    apply andp_right; [apply prop_right; auto|].
    apply andp_right; [apply prop_right; repeat split; auto |
      repeat rewrite sepcon_assoc; apply derives_refl]. }
  { set (lockt := Vptr b (Int.add o (Int.repr (16 * i)))).
    set (lsh := nth (Z.to_nat i) [sh2; tsh2; tsh3] sh0).
    set (g := nth (Z.to_nat i) ghosts (Vint (Int.repr 0))).
    eapply semax_seq'.
    forward_call_id00_wow' (lockt, sh1, t_lock_pred lsh sh2 cprod ccon lock lockt
      buf ends len next ghosts sh1 sh2 g).
    { go_lowerx; unfold tc_exprlist; simpl.
      unfold liftx, lift_uncurry_open, lift in *; simpl in *.
      apply andp_right; apply prop_right.
      - eapply eval_var_isptr; eauto.
      - unfold gvar_denote, eval_var in *.
        destruct (Map.get (ve_of rho) _thread_locks) as [(?, ?)|]; [contradiction|].
        destruct (ge_of rho _thread_locks); [|contradiction].
        unfold sem_add_pi.
        replace (eval_id _i__2 rho) with (Vint (Int.repr i)) by auto; auto. }
    { subst Frame; instantiate (1 := G' :: map (fun s1 => cond_var s1 ccon * cond_var s1 cprod *
         lock_inv s1 lock (Interp (lock_pred sh2 buf ends len next ghosts)))
        (sh0 :: firstn (Z.to_nat i) [sh2; tsh2; tsh3]) ++
        skipn (S (Z.to_nat i)) [lock_inv sh1 (Vptr b o) (Interp (t_lock_pred sh2 sh2 cprod ccon lock
          (Vptr b o) buf ends len next ghosts sh1 sh2 g1));
        lock_inv sh1 (Vptr b (Int.add o (Int.repr 16))) (Interp (t_lock_pred tsh2 sh2 cprod ccon lock
          (Vptr b (Int.add o (Int.repr 16))) buf ends len next ghosts sh1 sh2 g2));
        lock_inv sh1 (Vptr b (Int.add o (Int.repr 32))) (Interp (t_lock_pred tsh3 sh2 cprod ccon lock
          (Vptr b (Int.add o (Int.repr 32))) buf ends len next ghosts sh1 sh2 g3))] ++
        firstn (Z.to_nat i) (map (EX n : Z, ghost sh1 tint (Vint (Int.repr n))) [g1; g2; g3]) ++
        firstn (Z.to_nat i) [data_at_ Ews tlock (Vptr b o); data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 16)));
                             data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 32)))]).
      simpl; repeat rewrite sepcon_app; cancel.
      destruct (eq_dec i 0); [|destruct (eq_dec i 1); [|assert (i = 2) by omega]]; subst; subst lockt;
        simpl; try rewrite Int.add_zero; apply derives_refl. }
    Intro a.
    simpl; subst MORE_COMMANDS; unfold abbreviate.
    rewrite semax_seq_skip; eapply semax_seq'.
    forward_call_id00_wow' (lockt, Ews, Later (t_lock_pred lsh sh2 cprod ccon lock
      lockt buf ends len next ghosts sh1 sh2 g)).
    + go_lowerx; unfold tc_exprlist; simpl.
      unfold liftx, lift_uncurry_open, lift in *; simpl in *.
      apply andp_right; apply prop_right.
      * eapply eval_var_isptr; eauto.
      * unfold gvar_denote, eval_var in *.
        destruct (Map.get (ve_of rho) _thread_locks) as [(?, ?)|]; [contradiction|].
        destruct (ge_of rho _thread_locks); [|contradiction].
        unfold sem_add_pi.
        replace (eval_id _i__2 rho) with (Vint (Int.repr i)) by auto; auto.
    + setoid_rewrite selflock_eq at 2.
      repeat rewrite sepcon_assoc.
      eapply derives_trans; [apply sepcon_derives; [apply lock_inv_later | apply derives_refl]|]; simpl.
      rewrite <- (lock_inv_join _ _ _ _ _ Hsh); cancel.
    + split; auto; split; simpl.
      * apply later_positive, selflock_positive.
        apply positive_sepcon2, positive_sepcon2, positive_sepcon1, lock_inv_positive.
      * apply later_rec, selflock_rec.
    + Intro x; forward.
      go_lower; normalize.
      apply andp_right; [apply prop_right; repeat split; auto; omega|].
      rewrite Z2Nat.inj_add; try omega.
      assert (Z.to_nat i < 3)%nat by Omega0.
      rewrite <- firstn_app, <- firstn_1_skipn with (d := Ews); [|auto].
      do 2 (rewrite <- firstn_app, <- firstn_1_skipn with (d := FF); [|auto]).
      rewrite map_app.
      repeat rewrite sepcon_app; simpl.
      repeat rewrite NPeano.Nat.add_1_r; simpl; cancel.
      destruct (eq_dec i 0); [|destruct (eq_dec i 1); [|assert (i = 2) by omega]]; subst; subst lockt lsh g;
        simpl; try rewrite Int.add_zero; cancel; Exists x0; rewrite interp_ghost; auto. }
  simpl; normalize.
  freeze [12; 13; 14; 15; 16; 17; 18] FR.
  eapply semax_pre with (P' := PROP ( )
   LOCAL (temp _i__2 (Vint (Int.repr 3)); gvar _next next; gvar _buf buf; gvar _requests_producer cprod;
   gvar _requests_consumer ccon; gvar _ends ends; gvar _length len; gvar _thread_locks (Vptr b o);
   gvar _requests_lock lock)
   SEP (cond_var Ews ccon; cond_var Ews cprod;
     lock_inv Ews lock (Interp (lock_pred sh2 buf ends len next ghosts)); FRZL FR)).
  { go_lower.
    apply andp_right; [apply prop_right; auto|].
    apply andp_right; [apply prop_right; repeat split; auto|].
    rewrite <- 2(cond_var_join _ _ _ _ Hsh), <- (lock_inv_join _ _ _ _ _ Hsh).
    rewrite <- 2(cond_var_join _ _ _ _ Hsh'), <- (lock_inv_join _ _ _ _ _ Hsh').
    rewrite <- 2(cond_var_join _ _ _ _ Htsh), <- (lock_inv_join _ _ _ _ _ Htsh); cancel. }
  forward_call (lock, Ews, lock_pred sh2 buf ends len next ghosts).
  { destruct lock; try contradiction; apply prop_right; auto. }
  forward_call (lock, Ews, lock_pred sh2 buf ends len next ghosts).
  { destruct lock; try contradiction; apply prop_right; auto. }
  { split; auto; apply inv_positive. }
  forward_call (cprod, Ews).
  forward_call (ccon, Ews).
  eapply semax_pre; [|apply semax_return].
  thaw FR.
  (* timeout 80 entailer. XX times out, go_lower also times out *)
  go_lowerx; entailer'.
  subst POSTCONDITION; unfold abbreviate, frame_ret_assert, function_body_ret_assert.
  simpl; entailer.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | ]).
eapply semax_func_cons_ext; try reflexivity.
{ admit. }
{ admit. }
eapply semax_func_cons_ext; try reflexivity.
{ admit. }
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons body_get_request.
semax_func_cons body_process_request.
semax_func_cons body_q_add.
semax_func_cons body_q_remove.
(* XX For some reason, precondition_closed can't prove that all the gvars
   aren't local variables. *)
apply semax_func_cons; 
 [ reflexivity 
 | repeat apply Forall_cons; try apply Forall_nil; auto; computable
 | unfold var_sizes_ok; repeat constructor; simpl; computable | reflexivity
 | | apply body_f | ].
{ precondition_closed.
  apply closed_wrtl_PROPx, closed_wrtl_LOCALx, closed_wrtl_SEPx.
  repeat constructor; apply closed_wrtl_gvar; unfold is_a_local; simpl;
    intros [? | ?]; try contradiction; discriminate. }
semax_func_cons body_main.
Admitted.
