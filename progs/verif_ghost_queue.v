Require Import progs.conclib.
Require Import concurrency.semax_conc.
Require Import floyd.proofauto.
Require Import progs.ghost_queue.
Require Import Sorting.Sorted.

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

(* Axiomatization of ghost variables with allocator *)
Parameter ghost : forall (sh : share) (t : type) (v : reptype t) (p : val), mpred.
Parameter ghost_store : mpred -> Prop.

Axiom ghost_alloc : forall Espec D P Q R C P',
  semax(Espec := Espec) D (PROPx P (LOCALx Q (SEPx ((EX G : mpred, !!ghost_store G && G) :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx R))) C P'.
Axiom new_ghost : forall Espec D P Q G R C P' t v, ghost_store G ->
  semax(Espec := Espec) D (PROPx P (LOCALx Q (SEPx ((EX G' : mpred, !!ghost_store G' && G') ::
    (EX p : val, ghost Ews t v p) :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (G :: R)))) C P'.
Axiom alloc_compat : forall G1 G2, ghost_store G1 -> ghost_store G1 -> G1 * G2 |-- FF.

Axiom ghost_join : forall sh1 sh2 sh t v p, sepalg.join sh1 sh2 sh ->
  ghost sh1 t v p * ghost sh2 t v p = ghost sh t v p.
Axiom change_ghost : forall Espec D P Q R C P' t v p v',
  semax(Espec := Espec) D (PROPx P (LOCALx Q (SEPx (ghost Ews t v' p :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost Ews t v p :: R)))) C P'.
Parameter Ghost : forall (sh : share) (t : type) (v : reptype t) (p : val), Pred.
Axiom interp_ghost : forall sh t v p, Interp (Ghost sh t v p) = ghost sh t v p.
Axiom ghost_inj : forall sh1 sh2 t v1 v2 p, ghost sh1 t v1 p * ghost sh2 t v2 p
  |-- !!(v1 = v2).
Axiom ghost_compat : forall sh1 sh2 t1 t2 v1 v2 p,
  ghost sh1 t1 v1 p * ghost sh2 t2 v2 p |-- !!sepalg.joins sh1 sh2.


Definition MAX : nat := 10.

(* Note that a writable share must include all readable shares. *)
Definition lock_pred' sh buf ends len next ghosts reqs times head tail n ns := Pred_list (
    Data_at _ Ews (tarray (tptr trequest) (Z.of_nat MAX)) (rotate (complete MAX reqs) head MAX) buf ::
    Data_at _ Ews (tarray tint 2) [Vint (Int.repr (Z.of_nat head)); Vint (Int.repr (Z.of_nat tail))] ends ::
    Data_at _ Ews (tarray tint 1) [Vint (Int.repr (Zlength reqs))] len ::
    Pred_prop (Forall (fun d => Int.min_signed <= d < n /\ Forall (fun n => n < d) ns) times /\
               Int.min_signed <= n <= Int.max_signed /\ Forall (fun n' => Int.min_signed <= n' < n) ns /\
               (length reqs <= MAX /\ length times = length reqs /\ length ns = length ghosts)%nat /\
               Sorted Z.lt times /\
               (head < MAX)%nat /\ Z.of_nat tail = (Z.of_nat head + Zlength reqs) mod Z.of_nat MAX) ::
    Data_at _ Ews (tarray tint 1) [Vint (Int.repr n)] next ::
    map (fun p => Ghost sh tint (Vint (Int.repr (fst p))) (snd p)) (combine ns ghosts) ++
    map (fun p => Exp _ (fun d => Data_at _ Tsh trequest (d, Vint (Int.repr (fst p))) (snd p))) (combine times reqs)).

Definition lock_pred sh buf ends len next ghosts := Exp _ (fun reqs => Exp _ (fun times =>
  Exp _ (fun head => Exp _ (fun tail => Exp _ (fun n => Exp _ (fun ns =>
  lock_pred' sh buf ends len next ghosts reqs times head tail n ns)))))).

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

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0, x15 at level 0,
             P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0,
               x15 at level 0, x16 at level 0,
             P at level 100, Q at level 100).

Definition add_spec :=
 DECLARE _q_add
  WITH sh : share, lock : val, request : val, d : val, t : val, buf : val, ends : val, len : val, next : val,
       cprod : val, ccon : val, ghosts : list val, gsh2 : share
  PRE [ _request OF (tptr trequest) ]
   PROP (readable_share sh)
   LOCAL (temp _request request; gvar _buf buf; gvar _ends ends; gvar _length len; gvar _next next;
          gvar _requests_lock lock; gvar _requests_producer cprod; gvar _requests_consumer ccon)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf ends len next ghosts)); cond_var sh cprod; cond_var sh ccon;
        data_at Tsh trequest (d, t) request)
  POST [ tvoid ]
   PROP () LOCAL ()
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf ends len next ghosts)); cond_var sh cprod; cond_var sh ccon).

Definition remove_spec :=
 DECLARE _q_remove
  WITH sh : share, t : Z, lock : val, buf : val, ends : val, len : val, next : val, cprod : val, ccon : val,
       ghosts : list val, i : nat, g : val, gsh1 : share, gsh2 : share
  PRE [ ]
   PROP (readable_share sh; Int.min_signed <= t <= Int.max_signed; sepalg.join gsh1 gsh2 Ews;
         nth_error ghosts i = Some g)
   LOCAL (gvar _buf buf; gvar _ends ends; gvar _length len; gvar _requests_lock lock;
          gvar _requests_producer cprod; gvar _requests_consumer ccon)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf ends len next ghosts)); cond_var sh cprod; cond_var sh ccon;
        ghost gsh1 tint (Vint (Int.repr t)) g)
  POST [ tptr trequest ]
   EX t' : Z, EX req : val, EX d : val,
   PROP (t < t' <= Int.max_signed)
   LOCAL (temp ret_temp req)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf ends len next ghosts)); cond_var sh cprod; cond_var sh ccon;
        data_at Tsh trequest (d, Vint (Int.repr t')) req; ghost gsh1 tint (Vint (Int.repr t')) g).

Definition t_lock_pred sh tsh cprod ccon lock lockt buf ends len next ghosts gsh1 gsh2 g :=
  Self_lock (Pred_list [Cond_var _ sh cprod; Cond_var _ sh ccon;
    Lock_inv sh lock (lock_pred gsh2 buf ends len next ghosts);
    Exp _ (fun n => Ghost gsh1 tint (Vint (Int.repr n)) g)]) tsh lockt.

Definition f_spec :=
 DECLARE _f
  WITH lockt : val, x : share * share * Z * val * val * val * val * val * val * val * list val * nat * val * share * share
  PRE [ _arg OF (tptr tvoid) ]
   let '(sh, tsh, t, lock, buf, ends, len, next, cprod, ccon, ghosts, i, g, gsh1, gsh2) := x in
   PROP ()
   LOCAL (temp _arg lockt; gvar _buf buf; gvar _ends ends; gvar _length len; gvar _next next;
          gvar _requests_lock lock; gvar _requests_producer cprod; gvar _requests_consumer ccon)
   SEP (!!(readable_share sh /\ readable_share tsh /\ Int.min_signed <= t <= Int.max_signed /\
           sepalg.join gsh1 gsh2 Ews /\ nth_error ghosts i = Some g) && emp;
        lock_inv sh lock (Interp (lock_pred gsh2 buf ends len next ghosts));
        lock_inv tsh lockt (Interp (t_lock_pred sh tsh cprod ccon lock lockt buf ends len next ghosts gsh1 gsh2 g));
        cond_var sh cprod; cond_var sh ccon; ghost gsh1 tint (Vint (Int.repr t)) g)
  POST [ tptr tvoid ] PROP () LOCAL () SEP (emp).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Gprog : funspecs := augment_funspecs prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; makecond_spec; freecond_spec; wait_spec; signal_spec;
  malloc_spec; free_spec; get_request_spec; process_request_spec; add_spec; remove_spec; f_spec;
  main_spec].

Lemma all_ptrs : forall reqs times, length times = length reqs ->
  fold_right sepcon emp (map Interp (map (fun p => Exp val (fun d =>
    Data_at _ Tsh trequest (d, Vint (Int.repr (fst p))) (snd p))) (combine times reqs))) |--
  !!(Forall isptr reqs).
Proof.
  induction reqs; simpl; intros; entailer.
  destruct times; [discriminate | simpl].
  Intro d; rewrite data_at_isptr.
  eapply derives_trans; [apply saturate_aux20|].
  { apply andp_left1, derives_refl. }
  { apply IHreqs; auto. }
  normalize.
Qed.

Lemma reqs_inj : forall reqs times1 times2 r1 r2 r
  (Hlen1 : length times1 = length reqs)
  (Hlen2 : length times2 = length reqs)
  (Htimes1 : Forall (fun d => Int.min_signed <= d <= Int.max_signed) times1)
  (Htimes2 : Forall (fun d => Int.min_signed <= d <= Int.max_signed) times2)
  (Hreqs1 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap)
    (fold_right sepcon emp (map Interp (map (fun p => Exp val (fun d =>
     Data_at _ Tsh trequest (d, Vint (Int.repr (fst p))) (snd p)))
    (combine times1 reqs)))) r1)
  (Hreqs2 : predicates_hered.app_pred(A := compcert_rmaps.R.rmap)
    (fold_right sepcon emp (map Interp (map (fun p => Exp val (fun d =>
     Data_at _ Tsh trequest (d, Vint (Int.repr (fst p))) (snd p)))
    (combine times2 reqs)))) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r),
  r1 = r2 /\ times1 = times2.
Proof.
  induction reqs; destruct times1, times2; try discriminate; simpl; intros.
  - split; auto; apply sepalg.same_identity with (a := r); auto.
    { destruct Hr1 as (? & H); specialize (Hreqs1 _ _ H); subst; auto. }
    { destruct Hr2 as (? & H); specialize (Hreqs2 _ _ H); subst; auto. }
  - inv Hlen1; inv Hlen2; inv Htimes1; inv Htimes2.
    destruct Hreqs1 as (r1' & ? & ? & (? & Hp1) & ?),
      Hreqs2 as (r2' & ? & ? & (? & Hp2) & ?).
    exploit (IHreqs times1 times2); eauto.
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
    intros (? & ?); subst.
    unfold data_at, field_at, at_offset in Hp1, Hp2; simpl in Hp1, Hp2.
    destruct Hp1 as (? & Hp1), Hp2 as (? & Hp2).
    rewrite data_at_rec_eq in Hp1, Hp2; simpl in Hp1, Hp2.
    unfold withspacer, at_offset in Hp1, Hp2; simpl in Hp1, Hp2.
    destruct Hp1 as (r1a & r1b & ? & Hd1 & Ht1), Hp2 as (r2a & r2b & ? & Hd2 & Ht2).
    rewrite by_value_data_at_rec_nonvolatile in Hd1, Hd2, Ht1, Ht2; auto.
    unfold mapsto in *; simpl in *.
    destruct a; try contradiction; simpl in *.
    destruct (readable_share_dec Tsh); [|contradiction n; auto].
    assert (r1a = r2a); [|subst].
    { eapply ex_address_mapsto_precise.
      { destruct Hd1 as [(? & ?) | (? & ? & ?)]; eexists; eauto. }
      { destruct Hd2 as [(? & ?) | (? & ? & ?)]; eexists; eauto. }
      { eapply sepalg.join_sub_trans; [eexists; eauto |].
        eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
      { eapply sepalg.join_sub_trans; [eexists; eauto |].
        eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. } }
    destruct Ht1 as [(? & Ht1) | (? & ?)]; [|discriminate].
    destruct Ht2 as [(? & Ht2) | (? & ?)]; [|discriminate].
    assert (r1b = r2b); [|subst].
    { eapply ex_address_mapsto_precise.
      { eexists; eauto. }
      { eexists; eauto. }
      { eapply sepalg.join_sub_trans; [eexists; eauto |].
        eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
      { eapply sepalg.join_sub_trans; [eexists; eauto |].
        eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. } }
    assert (r1' = r2') by (eapply sepalg.join_eq; auto); subst.
    split; [eapply sepalg.join_eq; auto|].
    f_equal.
    exploit res_predicates.address_mapsto_value_cohere'.
    { apply Ht1. }
    { apply Ht2. }
    intro; rewrite <- (Int.signed_repr z), <- (Int.signed_repr z0); congruence.
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

Lemma inv_precise : forall gsh2 buf ends len next ghosts,
  precise (Interp (lock_pred gsh2 buf ends len next ghosts)).
Proof.
  intros ?????? w w1 w2 H1 H2 Hw1 Hw2; simpl in *.
  destruct H1 as (reqs1 & times1 & head1 & tail1 & n1 & ns1 & ? & ? & ? & Hbuf1 &
    ? & ? & ? & Hends1 & ? & ? & ? & Hlen1 & ? & ? & ? & ((? & ? & ? &
    (? & Htimes1 & ?) & ? & ? & ?) & Hemp1) & ? & ? & ? & Hnext1 & Hreqs1),
  H2 as (reqs2 & times2 & head2 & tail2 & n2 & ns2 & ? & ? & ? & Hbuf2 &
    ? & ? & ? & Hends2 & ? & ? & ? & Hlen2 & ? & ? & ? & ((? & ? & ? &
    (? & Htimes2 & ?) & ? & ? & ?) & Hemp2) & ? & ? & ? & Hnext2 & Hreqs2).
  exploit (data_at_int_array_inj Ews).
  { auto. }
  { apply Hlen1. }
  { apply Hlen2. }
  { eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  { eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  { repeat constructor; auto; discriminate. }
  { repeat constructor; auto; discriminate. }
  intros (? & Heq); subst.
  assert (Zlength reqs1 = Zlength reqs2) as Hlen.
  { rewrite <- (Int.signed_repr (Zlength reqs1)), <- (Int.signed_repr (Zlength reqs2)).
    congruence.
    { rewrite Zlength_correct; pose proof Int.min_signed_neg; split; [omega|].
      transitivity (Z.of_nat MAX); [Omega0 | simpl; computable]. }
    { rewrite Zlength_correct; pose proof Int.min_signed_neg; split; [omega|].
      transitivity (Z.of_nat MAX); [Omega0 | simpl; computable]. } }
  rewrite map_app, sepcon_app in Hreqs1; destruct Hreqs1 as (? & ? & ? &
    Hghosts1 & Hreqs1).
  rewrite map_app, sepcon_app in Hreqs2; destruct Hreqs2 as (? & ? & ? &
    Hghosts2 & Hreqs2).
  pose proof (all_ptrs _ _ Htimes1 _ Hreqs1) as Hptrs1.
  pose proof (all_ptrs _ _ Htimes2 _ Hreqs2) as Hptrs2.
  exploit (data_at_ptr_array_inj Ews).
  { auto. }
  { apply Hbuf1. }
  { apply Hbuf2. }
  { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  { eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  { apply Forall_rotate, Forall_complete; [|discriminate].
    eapply Forall_impl; [|apply Hptrs1].
    destruct a; auto; discriminate. }
  { apply Forall_rotate, Forall_complete; [|discriminate].
    eapply Forall_impl; [|apply Hptrs2].
    destruct a; auto; discriminate. }
  intros (? & Hbufs); subst.
  exploit (data_at_int_array_inj Ews).
  { auto. }
  { apply Hends1. }
  { apply Hends2. }
  { eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  { eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  { repeat constructor; auto; discriminate. }
  { repeat constructor; auto; discriminate. }
  intros (? & Hends).
  assert (head1 = head2); [|subst].
  { apply Nat2Z.inj.
    rewrite <- (Int.signed_repr (Z.of_nat head1)), <- (Int.signed_repr (Z.of_nat head2)).
    congruence.
    { pose proof Int.min_signed_neg; split; [omega|].
      transitivity (Z.of_nat MAX); [Omega0 | simpl; computable]. }
    { pose proof Int.min_signed_neg; split; [omega|].
      transitivity (Z.of_nat MAX); [Omega0 | simpl; computable]. } }
  assert (reqs1 = reqs2); [|subst].
  { repeat rewrite Zlength_correct in Hlen.
    eapply complete_inj; [|omega].
    eapply rotate_inj; eauto.
    repeat rewrite length_complete; auto. }
  exploit (reqs_inj reqs2 times1 times2); eauto.
  { eapply Forall_impl; [|eauto].
    intros ? (? & ?); omega. }
  { eapply Forall_impl; [|eauto].
    intros ? (? & ?); omega. }
  { eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  { eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  intros (? & ?); subst.
  exploit ghosts_precise.
  { apply Hghosts1. }
  { apply Hghosts2. }
  { auto. }
  { auto. }
  { eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  { eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  intro; subst.
  exploit (data_at_int_array_inj Ews).
  { auto. }
  { apply Hnext1. }
  { apply Hnext2. }
  { eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  { eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto|].
    eapply sepalg.join_sub_trans; [eexists; eauto | eauto]. }
  { repeat constructor; auto; discriminate. }
  { repeat constructor; auto; discriminate. }
  intros (? & ?); subst.
  repeat match goal with H1 : sepalg.join ?a ?b ?c, H2 : sepalg.join ?a ?b ?d |- _ =>
    pose proof (sepalg.join_eq H1 H2); clear H1 H2; subst end.
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

Lemma inv_positive : forall gsh2 buf ends len next ghosts,
  positive_mpred (Interp (lock_pred gsh2 buf ends len next ghosts)).
Proof.
Admitted.

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

Lemma body_get_request : semax_body Vprog Gprog f_get_request get_request_spec.
Proof.
  start_function.
  forward_call (sizeof trequest).
  { simpl; computable. }
  Intro p.
  rewrite memory_block_isptr; normalize.
  rewrite memory_block_size_compatible; [normalize | simpl; computable].
  unfold malloc_compatible in *.
  destruct p; try contradiction; match goal with H : _ /\ _ |- _ => destruct H end.
  rewrite memory_block_data_at_.
  forward.
  forward.
  Exists (Vptr b i0) (Vint (Int.repr 1)) Vundef; entailer.
  { unfold field_compatible; simpl; repeat split; auto.
    unfold align_attr; simpl.
    simpl in *.
    eapply Zdivides_trans; eauto; unfold natural_alignment; exists 2; omega. }
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

Lemma upd_rotate : forall {A} i (l : list A) n m x (Hl : length l = m) (Hlt : (n < m)%nat)
  (Hi : 0 <= i < Z.of_nat (length l)),
  upd_Znth i (rotate l n m) x = rotate (upd_Znth ((i - Z.of_nat n) mod Z.of_nat m) l x) n m.
Proof.
  intros; unfold upd_Znth, rotate.
  repeat rewrite sublist_firstn.
  assert (length (skipn (m - n) l) = n).
  { rewrite skipn_length; omega. }
  assert (Zlength (skipn (m - n) l ++ firstn (m - n) l) = Zlength l) as Hl'.
  { repeat rewrite Zlength_correct.
    rewrite app_length, skipn_length, firstn_length, Min.min_l; Omega0. }
  destruct (Z_lt_dec i (Z.of_nat n)).
  - replace ((i - Z.of_nat n) mod Z.of_nat m) with (Z.of_nat (m + Z.to_nat i - n))%nat.
    rewrite Nat2Z.id.
    rewrite firstn_app1; [|Omega0].
    assert (m - n <= Datatypes.length (firstn (m + Z.to_nat i - n) l))%nat.
    { rewrite firstn_length, Min.min_l; Omega0. }
    rewrite skipn_app1; auto.
    rewrite skipn_firstn.
    rewrite firstn_app1, firstn_firstn; auto; try omega.
    replace (m + Z.to_nat i - n - (m - n))%nat with (Z.to_nat i); [|omega].
    rewrite <- app_assoc; f_equal.
    simpl; f_equal.
    rewrite Hl', sublist.sublist_app; try (rewrite Zlength_correct; omega).
    assert (Zlength (skipn (m - n) l) = Z.of_nat n) as Hm' by (rewrite Zlength_correct; omega).
    repeat rewrite Hm'.
    rewrite Z.min_l; [|omega].
    rewrite Z.min_r; [|rewrite Zlength_correct; omega].
    rewrite Z.max_r; [|omega].
    rewrite sublist_firstn.
    rewrite Z.max_l; [|rewrite Zlength_correct; omega].
    unfold sublist.sublist.
    rewrite skipn_skipn.
    replace (Zlength l - (Z.of_nat (m + Z.to_nat i - n) + 1)) with (Z.of_nat n - (i + 1)).
    repeat rewrite Z2Nat.inj_add; try omega.
    rewrite Nat2Z.id.
    replace (m - _ + _)%nat with (m + Z.to_nat i - n + Z.to_nat 1)%nat by omega.
    f_equal.
    replace (Z.to_nat (Zlength l - Z.of_nat n)) with (m - n)%nat by (rewrite Zlength_correct; Omega0).
    rewrite firstn_firstn; auto.
    { rewrite Zlength_correct, Nat2Z.inj_sub, Nat2Z.inj_add, Z2Nat.id; omega. }
    { rewrite <- Hl', Zlength_app; omega. }
    { rewrite Zmod_eq; [|omega].
      replace (_ / _) with (-1); try Omega0.
      replace (_ - _) with (- (Z.of_nat n - i)); [|omega].
      rewrite Z_div_nz_opp_full, Zdiv_small; try omega.
      rewrite Zmod_small; omega. }
  - assert (n <= Z.to_nat i)%nat.
    { rewrite Nat2Z.inj_le, Z2Nat.id; omega. }
    rewrite firstn_app2; rewrite H; auto.
    destruct Hi as (? & Hi).
    assert (Z.to_nat i < length l)%nat.
    { rewrite Z2Nat.inj_lt, Nat2Z.id in Hi; omega. }
    assert (Z.to_nat i - n <= m - n)%nat by omega.
    rewrite firstn_firstn; auto.
    rewrite Zmod_small; [|omega].
    assert (length (firstn (Z.to_nat (i - Z.of_nat n)) l) = Z.to_nat (i - Z.of_nat n)) as Hl1.
    { rewrite firstn_length, Min.min_l; auto.
      rewrite Z2Nat.inj_sub, Nat2Z.id; omega. }
    assert (m - n >= Z.to_nat (i - Z.of_nat n))%nat.
    { rewrite Z2Nat.inj_sub, Nat2Z.id; omega. }
    rewrite skipn_app2; rewrite Hl1; auto.
    assert (m - n - Z.to_nat (i - Z.of_nat n) = m - Z.to_nat i)%nat as Hminus.
    { rewrite Z2Nat.inj_sub; [|omega].
      rewrite <- NPeano.Nat.sub_add_distr, Nat2Z.id, le_plus_minus_r; omega. }
    rewrite Hminus.
    destruct (m - Z.to_nat i)%nat eqn: Hi'; [omega | simpl].
    rewrite firstn_app2; rewrite Hl1; auto.
    rewrite Hminus; clear Hminus; simpl.
    unfold sublist.sublist at 2.
    rewrite skipn_firstn, skipn_skipn.
    assert (Z.to_nat (i - Z.of_nat n + 1) + n1 = m - n)%nat as Hminus'.
    { assert (m - Z.to_nat i + Z.to_nat i = S n1 + Z.to_nat i)%nat as Heq by (f_equal; auto).
      rewrite NPeano.Nat.sub_add in Heq; [|omega].
      rewrite Heq.
      rewrite Z2Nat.inj_add, Z2Nat.inj_sub, Nat2Z.id; simpl Z.to_nat; omega. }
    rewrite Hminus'.
    assert (n1 = Z.to_nat (Zlength l - (i + 1)))%nat.
    { rewrite Z2Nat.inj_sub, Zlength_correct, Nat2Z.id, Z2Nat.inj_add; simpl; omega. }
    subst n1.
    replace (Z.to_nat (Zlength l - _) - _)%nat with (length (skipn (m - n) l)).
    rewrite firstn_exact_length.
    rewrite <- app_assoc; f_equal.
    rewrite Z2Nat.inj_sub, Nat2Z.id; [|omega].
    repeat f_equal.
    unfold sublist.sublist.
    rewrite Hl'.
    assert (length l - (m - n) = n)%nat as Hskip by (subst m; clear - Hlt; omega).
    rewrite skipn_app2; rewrite skipn_length, Hskip.
    rewrite firstn_firstn.
    rewrite skipn_firstn, firstn_firstn.
    f_equal.
    replace (Z.to_nat (i + 1) - n)%nat with (Z.to_nat (i - Z.of_nat n + 1))%nat; auto.
    { clear - H1 H0 n0; rewrite Z2Nat.inj_add, Z2Nat.inj_sub; try omega.
      rewrite Nat2Z.id, Z2Nat.inj_add; omega. }
    { subst m; clear - H1 H0 n0; rewrite Z2Nat.inj_sub; [|omega].
      rewrite Zlength_correct, Nat2Z.id, Z2Nat.inj_add; omega. }
    { subst m; clear - H1 H0 n0; rewrite Z2Nat.inj_sub; try omega.
      rewrite Zlength_correct, Nat2Z.id; rewrite Z2Nat.inj_sub, Nat2Z.id; try omega.
      repeat rewrite Z2Nat.inj_add; simpl; try omega.
      rewrite Z2Nat.inj_sub; omega. }
    { clear - H1 H0; rewrite Z2Nat.inj_add; omega. }
    { subst m; clear - H1 H0 n0 Hi; rewrite skipn_length; repeat rewrite Z2Nat.inj_sub; try omega.
      repeat rewrite Zlength_correct, Nat2Z.id.
      repeat rewrite Z2Nat.inj_add; try omega.
      rewrite Z2Nat.inj_sub; try omega.
      rewrite Nat2Z.id.
      rewrite <- NPeano.Nat.sub_add_distr, plus_comm, <- Nat.add_sub_swap; [omega | Omega0]. }
Qed.

Lemma combine_app : forall {A B} (l1 l2 : list A) (l1' l2' : list B), length l1 = length l1' ->
  combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  induction l1; destruct l1'; intros; try discriminate; auto; simpl in *.
  rewrite IHl1; auto.
Qed.

Lemma body_add : semax_body Vprog Gprog f_q_add add_spec.
Proof.
  start_function.
  forward_call (lock, sh, lock_pred gsh2 buf ends len next ghosts).
  { destruct lock; try contradiction; simpl; apply prop_right; auto. }
  simpl; Intros reqs times head tail n ns.
  forward.
  unfold Znth; simpl.
  forward_while (EX reqs : list val, EX times : list Z, EX head : nat, EX tail : nat, EX n : Z, EX ns : list Z,
   PROP ()
   LOCAL (temp _len (Vint (Int.repr (Zlength reqs))); temp _request request; 
     gvar _buf buf; gvar _ends ends; gvar _next next; gvar _length len; gvar _requests_lock lock;
     gvar _requests_producer cprod; gvar _requests_consumer ccon)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf ends len next ghosts));
        Interp (lock_pred' gsh2 buf ends len next ghosts reqs times head tail n ns);
        cond_var sh cprod; cond_var sh ccon; @data_at CompSpecs Tsh trequest (d, t) request)).
  { Exists reqs times head tail n ns.
    simpl Interp.
    (*timeout 70 entailer. XX times out *)
    go_lower.
    apply andp_right; [apply prop_right; repeat split; auto |
      apply andp_right; [apply prop_right; repeat split; auto | normalize; cancel]]. }
  { go_lower; entailer'. }
  { forward_call (cprod, lock, sh, sh, lock_pred gsh2 buf ends len next ghosts).
    { destruct lock; try contradiction; simpl; apply prop_right; auto. }
    { simpl.
      Exists reqs0 times0 head0 tail0 n0 ns0; cancel. }
    simpl; Intros reqs1 times1 head1 tail1 n1 ns1.
    forward.
    Exists (reqs1, times1, head1, tail1, n1, ns1).
    (* timeout 70 entailer. XX times out *)
    go_lower; unfold Znth; simpl.
    apply andp_right; [apply prop_right; repeat split; auto |
      apply andp_right; [apply prop_right; repeat split; auto | normalize; cancel]]. }
  simpl; normalize.
  rewrite Int.signed_repr, Zlength_correct in HRE.
  freeze [0; 1; 2; 4; 5; 6; 7] FR; forward.
  unfold Znth; simpl.
  forward.
  forward; thaw FR.
  unfold upd_Znth; repeat rewrite sublist.sublist_nil; simpl.
  freeze [2; 3; 4; 5; 6; 7; 8] FR; forward.
  unfold Znth; simpl.
  time forward. (* 19s even with freeze *)
  { apply prop_right.
    replace (Z.of_nat tail0) with ((Z.of_nat head0 + Zlength reqs0) mod 10) by auto.
    apply Z_mod_lt; omega. }
  forward.
  { (* timeout 70 entailer. XX times out *)
    repeat apply andp_right.
    - go_lower; entailer'.
    - go_lower; simpl.
      apply prop_right.
      rewrite andb_false_intro2; simpl; auto.
    - go_lower; entailer'.
    - apply TT_right. }
  thaw FR.
  forward.
  forward_call (ccon, sh).
  assert (length reqs0 < MAX)%nat by (rewrite Nat2Z.inj_lt; auto).
  rewrite upd_rotate; auto.
  replace ((Z.of_nat tail0 - Z.of_nat head0) mod Z.of_nat MAX) with (Zlength reqs0).
  rewrite upd_complete; auto.
  unfold upd_Znth; simpl.
  repeat rewrite sublist.sublist_nil.
  repeat rewrite add_repr.
  rewrite (field_at_isptr _ _ _ _ buf), (field_at_isptr _ _ _ _ len), (field_at_isptr _ _ _ _ next),
    (field_at_isptr _ trequest); normalize.
  time forward_call (lock, sh, lock_pred gsh2 buf ends len next ghosts). (* 24s *)
  { destruct lock; try contradiction; simpl; apply prop_right; auto. }
  { simpl.
    Exists (reqs0 ++ [request]) (times0 ++ [n0]) head0 (Nat.modulo (tail0 + 1) MAX) (n0 + 1) ns0;
      unfold fold_right at 1; cancel.
    rewrite Zlength_app, Zlength_cons; simpl Z.succ; cancel.
    unfold sem_mod; simpl sem_binarith.
    unfold both_int; simpl force_val.
    rewrite andb_false_intro2; [|simpl; auto].
    simpl force_val.
    rewrite mods_repr; try computable.
    rewrite mod_Zmod, Nat2Z.inj_add; [cancel | omega].
    rewrite <- (sepcon_emp (_ * _)), sepcon_comm.
    match goal with H : _ /\ _ |- _ => destruct H as (? & ? & ?) end.
    rewrite (sepcon_assoc (_ && _)); apply sepcon_derives.
    { apply andp_right; auto; apply prop_right.
      repeat split; auto; try omega.
      - rewrite Forall_app; split.
        + eapply Forall_impl; [|eauto].
          intros ? (? & ?); split; auto; omega.
        + constructor; auto.
          repeat split; auto; try omega.
          eapply Forall_impl; [|eauto]; intros ? (? & ?); auto.
      - admit. (* Here's where we need to watch for overflow. *)
      - eapply Forall_impl; [|eauto]; intros; simpl in *; omega.
      - rewrite app_length; simpl; omega.
      - repeat rewrite app_length; simpl; omega.
      - apply SetoidList.SortA_app with (eqA := eq); auto.
        intros ?? Hin Hn; inversion Hn; [|rewrite SetoidList.InA_nil in *; contradiction]; subst.
        rewrite SetoidList.InA_alt in Hin; destruct Hin as (? & ? & Hin); subst.
        match goal with H : Forall _ _ |- _ => rewrite Forall_forall in H; specialize (H _ Hin) end; omega.
      - rewrite Z.add_assoc.
        replace (Z.of_nat tail0) with ((Z.of_nat head0 + Zlength reqs0) mod 10) by auto.
        rewrite Zplus_mod_idemp_l; auto. }
      rewrite combine_app; auto; simpl.
      repeat rewrite map_app; repeat rewrite sepcon_app; simpl.
      Exists d; cancel.
      { pose proof (Z_mod_lt (Z.of_nat head0 + Zlength reqs0) (Z.of_nat MAX)).
        split; try omega.
        transitivity (Z.of_nat MAX); simpl in *; [omega | computable]. } }
  { split; auto; split; [apply inv_precise | apply inv_positive]; auto. }
  forward.
  { cancel. }
  { replace (Z.of_nat tail0) with ((Z.of_nat head0 + Zlength reqs0) mod 10) by auto.
    rewrite Zminus_mod_idemp_l; auto.
    rewrite Z.add_simpl_l, Zmod_small; auto; simpl.
    rewrite Zlength_correct; omega. }
  { apply length_complete; omega. }
  { rewrite length_complete; [|omega].
    replace (Z.of_nat tail0) with ((Z.of_nat head0 + Zlength reqs0) mod 10) by auto.
    apply Z_mod_lt; omega. }
  { pose proof Int.min_signed_neg; rewrite Zlength_correct; split; try omega.
    match goal with H : _ /\ _ |- _ => destruct H as (? & ? & ?) end.
    transitivity (Z.of_nat MAX); [Omega0 | simpl; computable]. }
Admitted.

Lemma Znth_head : forall reqs head m d, (length reqs <= m)%nat -> (head < m)%nat ->
  (length reqs > 0)%nat ->
  Znth (Z.of_nat head) (rotate (complete m reqs) head m) d = Znth 0 reqs d.
Proof.
  intros; unfold rotate.
  assert (Zlength (skipn (m - head) (complete m reqs)) = Z.of_nat head) as Hlen.
  { rewrite Zlength_correct, skipn_length, length_complete; auto; Omega0. }
  rewrite app_Znth2; rewrite Hlen; [|omega].
  rewrite Zminus_diag.
  rewrite <- (Nat2Z.id (m - head)), Znth_firstn; [|Omega0].
  rewrite Znth_complete; auto.
  rewrite Zlength_correct; omega.
Qed.

Opaque Nat.modulo.

Lemma rotate_1 : forall v l n m, (n < m)%nat -> (length l < m)%nat ->
  rotate (upd_Znth 0 (complete m (v :: l)) (Vint (Int.repr 0))) n m =
  rotate (complete m l) (S n mod m) m.
Proof.
  intros.
  unfold complete at 1; simpl.
  unfold upd_Znth; simpl.
  rewrite Zlength_cons; unfold sublist.sublist; simpl.
  replace (Z.to_nat _) with (length (l ++ repeat (Vint (Int.repr 0)) (m - S (length l)))).
  rewrite firstn_exact_length.
  unfold rotate.
  destruct (m - n)%nat eqn: Hminus; [omega | simpl].
  destruct (eq_dec (S n) m).
  - rewrite e, NPeano.Nat.mod_same; [|omega].
    replace (m - 0)%nat with (length (complete m l)) by (rewrite length_complete; auto; omega).
    rewrite skipn_exact_length, firstn_exact_length; simpl.
    assert (n0 = O) by omega; subst; simpl.
    unfold complete.
    replace (S n - length l)%nat with (n - length l + 1)%nat by omega.
    rewrite repeat_plus, <- app_assoc; auto.
  - rewrite Nat.mod_small; [|omega].
    assert (n0 = m - S n)%nat by omega; subst.
    unfold complete.
    replace (m - length l)%nat with (m - S (length l) + 1)%nat by omega.
    rewrite repeat_plus; repeat rewrite app_assoc; simpl.
    assert (m - S n <= Datatypes.length (l ++ repeat (Vint (Int.repr 0)) (m - S (Datatypes.length l))))%nat.
    { rewrite app_length, repeat_length; omega. }
    setoid_rewrite skipn_app1 at 2; auto; setoid_rewrite firstn_app1 at 2; auto.
    rewrite <- app_assoc; auto.
  - rewrite Zlength_correct; Omega0.
Qed.

Lemma upd_Znth_length : forall {A} i (l : list A) x, 0 <= i < Z.of_nat (length l) ->
  length (upd_Znth i l x) = length l.
Proof.
  intros.
  rewrite <- (Nat2Z.id (length _)), <- Zlength_correct.
  rewrite upd_Znth_Zlength, Zlength_correct, Nat2Z.id; auto.
  rewrite Zlength_correct; omega.
Qed.

Lemma body_q_remove : semax_body Vprog Gprog f_q_remove remove_spec.
Proof.
  start_function.
  forward_call (lock, sh, lock_pred gsh2 buf ends len next ghosts).
  simpl; Intros reqs times head tail n ns.
  forward.
  unfold Znth; simpl.
  forward_while (EX reqs : list val, EX times : list Z, EX head : nat, EX tail : nat, EX n : Z, EX ns : list Z,
   PROP ()
   LOCAL (temp _len (Vint (Int.repr (Zlength reqs))); gvar _buf buf; gvar _ends ends; gvar _length len;
          gvar _requests_lock lock; gvar _requests_producer cprod; gvar _requests_consumer ccon)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf ends len next ghosts));
        Interp (lock_pred' gsh2 buf ends len next ghosts reqs times head tail n ns);
        cond_var sh cprod; cond_var sh ccon; ghost gsh1 tint (Vint (Int.repr t)) g)).
  { Exists reqs times head tail n ns; go_lower.
    apply andp_right; [apply prop_right; repeat split; auto |
      apply andp_right; [apply prop_right; repeat split; auto | normalize; cancel]]. }
  { go_lower; entailer'. }
  { forward_call (ccon, lock, sh, sh, lock_pred gsh2 buf ends len next ghosts).
    { destruct lock; try contradiction; simpl; apply prop_right; auto. }
    { simpl.
      Exists reqs0 times0 head0 tail0 n0 ns0; cancel. }
    simpl; Intros reqs1 times1 head1 tail1 n1 ns1.
    forward.
    Exists (reqs1, times1, head1, tail1, n1, ns1); go_lower; unfold Znth; simpl.
    apply andp_right; [apply prop_right; repeat split; auto |
      apply andp_right; [apply prop_right; repeat split; auto | normalize; cancel]]. }
  simpl; normalize.
  assert (length reqs0 > 0)%nat.
  { rewrite Zlength_correct in *.
    destruct (length reqs0); [|omega].
    contradiction HRE; auto. }
  match goal with H : _ /\ _ |- _ => destruct H as (? & ? & ?) end.
  assert (0 <= Z.of_nat head0 < Z.of_nat MAX) by Omega0.
  forward.
  unfold Znth; simpl.
  freeze [1; 2; 3; 4; 5; 6; 7; 8] FR.
  forward.
  { go_lower; normalize.
    rewrite Znth_head; auto.
    thaw FR.
    repeat rewrite <- sepcon_assoc.
    rewrite (sepcon_comm _ (_ (map _ _))).
    rewrite map_app, sepcon_app.
    repeat rewrite sepcon_assoc; rewrite sepcon_comm.
    rewrite sepcon_assoc.
    eapply derives_trans; [apply sepcon_derives; [apply prop_and_same_derives, all_ptrs; auto |
      apply derives_refl]|].
    normalize; apply prop_right.
    apply Forall_Znth.
    { rewrite Zlength_correct; omega. }
    eapply Forall_impl; [|eauto].
    destruct a; auto. }
  forward.
  thaw FR.
  freeze [2; 3; 4; 5; 6; 7; 8] FR.
  time forward. (* 26s *)
  { go_lower; normalize; simpl.
    apply prop_right; rewrite andb_false_intro2; simpl; auto. }
  forward.
  thaw FR.
  freeze [0; 1; 2; 4; 5; 6; 7; 8] FR.
  forward_call (cprod, sh).
  thaw FR.
  rewrite upd_rotate; auto.
  rewrite Zminus_diag, Zmod_0_l.
  destruct reqs0; [contradiction HRE; auto|].
  rewrite rotate_1; auto.
  repeat rewrite Zlength_correct; simpl length.
  repeat rewrite Nat2Z.inj_succ.
  unfold upd_Znth; unfold sublist.sublist; simpl.
  unfold sem_mod; simpl sem_binarith.
  unfold both_int; simpl force_val.
  rewrite andb_false_intro2; [|simpl; auto].
  simpl force_val.
  rewrite add_repr, mods_repr; try computable.
  rewrite sub_repr.
  unfold Z.succ; rewrite Z.add_simpl_r.
  destruct times0; [discriminate | rewrite map_app, sepcon_app; simpl].
  Intro d.
  rewrite field_at_isptr, (field_at_isptr _ (tarray tint 1)), data_at_isptr,
    (data_at_isptr _ trequest); normalize.
  assert (i < length ghosts)%nat as Hlt by (rewrite <- nth_error_Some; intro X; rewrite X in *; discriminate).
  replace (length ghosts) with (length ns0) in Hlt by auto.
  freeze [0; 1; 3; 4; 5; 6; 8; 9; 10; 11] FR.
  exploit nth_ghost; eauto; intros (n2 & Hn2 & Heq); rewrite Heq.
  match goal with H : Forall _ (_ :: _) |- _ => inv H end.
  eapply semax_pre with (P' := PROP (t < z <= Int.max_signed)
   LOCAL (temp _r (Znth (Z.of_nat head0) (rotate (complete MAX (v :: reqs0)) head0 MAX) Vundef);
     temp _head (Vint (Int.repr (Z.of_nat head0)));
     temp _len (Vint (Int.repr (Z.of_nat (Datatypes.length reqs0) + 1))); gvar _buf buf; 
     gvar _ends ends; gvar _length len; gvar _requests_lock lock; gvar _requests_producer cprod;
     gvar _requests_consumer ccon) (SEPx [_; _])).
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
    subst; erewrite ghost_join; [|eauto].
    apply andp_right; [apply prop_right; split; auto; split; try omega|].
    { match goal with X : _ /\ Forall _ ns0 |- _ => destruct X as (? & X); rewrite Forall_forall in X;
        specialize (X _ Hin); auto end. }
    apply andp_right; [apply prop_right; repeat split; auto|].
    rewrite sepcon_comm; apply derives_refl. }
  normalize.
  apply change_ghost with (v' := Vint (Int.repr z)).
  erewrite <- ghost_join; eauto.
  thaw FR.
  forward_call (lock, sh, lock_pred gsh2 buf ends len next ghosts).
  { destruct lock; try contradiction; simpl; apply prop_right; auto. }
  { simpl.
    Exists reqs0 times0 (Nat.modulo (S head0) MAX) tail0 n0 (upd_Znth (Z.of_nat i) ns0 z).
    rewrite mod_Zmod, Nat2Z.inj_succ; simpl; [|omega].
    normalize.
    apply andp_right.
    { apply prop_right.
      match goal with H : Sorted _ _ |- _ => inv H end.
      repeat split; auto; try omega.
      - rewrite Forall_forall in *; intros ? Hin.
        match goal with H : forall _, _ -> _ /\ _ |- _ => specialize (H _ Hin); destruct H; split; auto end.
        apply Forall_upd_Znth; auto.
        rewrite SetoidList.InfA_alt with (eqA := eq) in *; auto.
        match goal with H : forall _, _ -> _ |- _ => apply H end.
        rewrite SetoidList.InA_alt; eauto.
        { constructor; repeat intro; omega. }
        { repeat intro; omega. }
      - apply Forall_upd_Znth; auto; omega.
      - simpl in *; omega.
      - rewrite upd_Znth_length; auto; Omega0.
      - apply NPeano.Nat.mod_upper_bound; omega.
      - rewrite Zlength_cons in *.
        rewrite Zplus_mod_idemp_l; unfold Z.succ in *.
        rewrite <- Zplus_assoc, (Zplus_comm 1); auto. }
    rewrite <- Zlength_correct; unfold fold_right at 1; cancel.
    rewrite (sepcon_comm (ghost _ _ _ _)), sepcon_comm.
    repeat rewrite <- sepcon_assoc.
    rewrite add_nth_ghost; auto.
    simpl; rewrite map_app, sepcon_app; unfold fold_right at 3; cancel. }
  { split; auto; split; [apply inv_precise | apply inv_positive]; auto. }
  forward.
  Exists z v d; normalize.
  apply andp_right; [|cancel].
  apply prop_right; repeat split; auto; try omega.
  rewrite Znth_head; auto.
  - split; try omega.
    transitivity (Z.of_nat MAX); [omega | simpl; computable].
  - rewrite length_complete; auto.
  - rewrite length_complete; auto.
Qed.

Opaque lock_pred.

Lemma upd_complete' : forall l x n, (length l < n)%nat -> 
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
Qed.

Lemma precise_False : precise (!!False).
Proof.
  repeat intro.
  inversion H.
Qed.

Lemma t_inv_precise : forall sh tsh cprod ccon lock lockt buf ends len next ghosts gsh1 gsh2 g
  (Hsh : readable_share sh),
  precise (Interp (t_lock_pred sh tsh cprod ccon lock lockt buf ends len next ghosts gsh1 gsh2 g)).
Proof.
  intros; simpl.
  apply selflock_precise; repeat apply precise_sepcon.
  - rewrite cond_var_isptr.
    destruct cprod; simpl; try solve [apply precise_andp1, precise_False].
    apply precise_andp2, cond_var_precise; auto.
  - rewrite cond_var_isptr.
    destruct ccon; simpl; try solve [apply precise_andp1, precise_False].
    apply precise_andp2, cond_var_precise; auto.
  - apply lock_inv_precise.
  - eapply derives_precise; [|apply ghost_precise].
    intros ? (? & ?).
    rewrite interp_ghost in *; eexists; eauto.
  - apply precise_emp.
Qed.

Lemma t_inv_positive : forall sh tsh cprod ccon lock lockt buf ends len next ghosts gsh1 gsh2 g,
  positive_mpred (Interp (t_lock_pred sh tsh cprod ccon lock lockt buf ends len next ghosts gsh1 gsh2 g)).
Proof.
Admitted.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  rewrite (lock_inv_isptr _ lockt); normalize.
  destruct lockt as [| | | | |lockt o]; try contradiction; simpl.
  forward_for_simple_bound 3 (EX i : Z, PROP ()
      LOCAL (temp _arg (Vptr lockt o); lvar _res (tarray tint 3) lvar0; 
             gvar _buf buf; gvar _ends ends; gvar _length len; gvar _next next; gvar _requests_lock lock;
             gvar _requests_producer cprod; gvar _requests_consumer ccon)
      SEP (data_at_ Tsh (tarray tint 3) lvar0;
           lock_inv sh lock (Interp (lock_pred gsh2 buf ends len next ghosts));
           lock_inv tsh (Vptr lockt o) (Interp (t_lock_pred sh tsh cprod ccon lock (Vptr lockt o)
                                                            buf ends len next ghosts gsh1 gsh2 g));
           cond_var sh cprod; cond_var sh ccon; ghost gsh1 tint (Vint (Int.repr t)) g)).
  { entailer!. }
  { forward_call tt.
    Intro x; destruct x as ((req, d0), t0); simpl.
    forward_call (sh, lock, req, d0, t0, buf, ends, len, next, cprod, ccon, ghosts, gsh2).
    go_lower; entailer'; cancel. }
  forward_for_simple_bound 3 (EX i : Z, PROP ()
    LOCAL (temp _arg (Vptr lockt o); lvar _res (tarray tint 3) lvar0; 
           gvar _buf buf; gvar _ends ends; gvar _length len; gvar _next next; gvar _requests_lock lock;
           gvar _requests_producer cprod; gvar _requests_consumer ccon)
    SEP (EX n' : Z, EX ld : list Z, !! (Int.min_signed <= n' <= Int.max_signed /\
           Zlength ld = i /\ Sorted Z.lt ld /\ Forall (fun z => Int.min_signed <= z <= n') ld) &&
           data_at Tsh (tarray tint 3) (map Vint (map Int.repr ld) ++ repeat Vundef (3 - length ld)%nat) lvar0 *
         ghost gsh1 tint (Vint (Int.repr n')) g;
         lock_inv sh lock (Interp (lock_pred gsh2 buf ends len next ghosts));
         lock_inv tsh (Vptr lockt o) (Interp (t_lock_pred sh tsh cprod ccon lock (Vptr lockt o)
                                                          buf ends len next ghosts gsh1 gsh2 g));
         cond_var sh cprod; cond_var sh ccon)).
  { entailer!.
    Exists t ([] : list Z); simpl; entailer. }
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

Lemma lock_struct : forall p, data_at_ Ews (Tstruct _lock_t noattr) p |-- data_at_ Ews tlock p.
Proof.
  intros.
  unfold data_at_, field_at_, field_at; simpl; entailer.
  unfold default_val; simpl.
  rewrite data_at_rec_eq; simpl.
  unfold struct_pred, aggregate_pred.struct_pred, at_offset, withspacer; simpl; entailer.
Qed.

Lemma lock_struct_array : forall z p, data_at_ Ews (tarray (Tstruct _lock_t noattr) z) p |--
  data_at_ Ews (tarray tlock z) p.
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

Axiom ghost_almost_empty : forall sh t v p phi, predicates_hered.app_pred (ghost sh t v p) phi -> juicy_machine.almost_empty phi.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  rewrite <- (sepcon_emp (main_pre _ _)).
  rewrite main_pre_start; unfold prog_vars, prog_vars'; simpl globvars2pred.
  process_idstar.
  simpl init_data2pred'.
  rewrite <- (sepcon_emp (_ * _)).
  simple apply move_globfield_into_SEP.
  rewrite sepcon_emp.
  process_idstar.
  simpl init_data2pred'.
  rewrite <- (sepcon_emp (_ * _)).
  simple apply move_globfield_into_SEP.
  rewrite sepcon_emp.
  process_idstar.
  simpl init_data2pred'.
  rewrite <- (sepcon_emp (_ * _)).
  simple apply move_globfield_into_SEP.
  rewrite sepcon_emp.
  process_idstar.
  simpl init_data2pred'.
  rewrite <- (sepcon_emp (_ * _)).
  simple apply move_globfield_into_SEP.
  rewrite sepcon_emp.
  process_idstar.
  simpl init_data2pred'.
  rewrite <- (sepcon_emp (_ * _)).
  simple apply move_globfield_into_SEP.
  rewrite sepcon_emp.
  process_idstar.
  simpl init_data2pred'.
  rewrite <- (sepcon_emp (_ * _)).
  simple apply move_globfield_into_SEP.
  rewrite sepcon_emp.
  process_idstar.
  simpl init_data2pred'.
  rewrite <- (sepcon_emp (_ * _)).
  simple apply move_globfield_into_SEP.
  rewrite sepcon_emp.
  process_idstar.
  simpl init_data2pred'.
  rewrite <- (sepcon_emp (_ * _)).
  simple apply move_globfield_into_SEP.
  change (globvars2pred nil) with (@emp (environ->mpred) _ _).
  repeat rewrite sepcon_emp.
  rewrite <- seq_assoc.
  rename gvar7 into next, gvar6 into buf, gvar5 into cprod, gvar4 into ccon, gvar3 into ends, gvar2 into len,
    gvar1 into lockt, gvar0 into lock.
  forward_for_simple_bound 10 (EX i : Z, PROP ()
    LOCAL (gvar _next next; gvar _buf buf; gvar _requests_producer cprod; gvar _requests_consumer ccon;
           gvar _ends ends; gvar _length len; gvar _thread_locks lockt; gvar _requests_lock lock)
    SEP (data_at_ Ews (tarray tint 1) next;
         data_at Ews (tarray (tptr trequest) 10)
               (repeat (Vint (Int.repr 0)) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (10 - i))) buf;
         data_at_ Ews tint cprod; data_at_ Ews tint ccon; data_at_ Ews (tarray tint 2) ends;
         data_at_ Ews (tarray tint 1) len; data_at_ Ews (tarray tlock 3) lockt; data_at_ Ews tlock lock)).
  { unfold trequest, _request_t; entailer!.
    repeat rewrite sepcon_assoc; apply sepcon_derives; [entailer!|].
    apply sepcon_derives; [apply lock_struct_array | apply lock_struct]. }
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
  forward.
  forward.
  forward.
  unfold upd_Znth; repeat rewrite sublist.sublist_nil; simpl.
  destruct split_Ews as (sh1 & sh2 & Hr1 & Hr2 & Hsh).
  apply ghost_alloc; Intro G; normalize.
  apply new_ghost with (t := tint)(v := Vint (Int.repr (-1))); auto; Intros G1 g1; normalize.
  apply new_ghost with (t := tint)(v := Vint (Int.repr (-1))); auto; Intros G2 g2; normalize.
  apply new_ghost with (t := tint)(v := Vint (Int.repr (-1))); auto; Intros G' g3; normalize.
  set (ghosts := [g1; g2; g3]).
  forward_call (lock, Ews, lock_pred sh2 buf ends len next ghosts).
  { destruct lock; try contradiction; apply prop_right; auto. }
  forward_call (lock, Ews, lock_pred sh2 buf ends len next ghosts).
  { destruct lock; try contradiction; apply prop_right; auto. }
  { simpl.
    Exists ([] : list val) ([] : list Z) O O 0 [-1; -1; -1]; unfold complete, rotate; simpl;
      repeat rewrite interp_ghost; cancel; normalize.
    apply andp_right; [|repeat rewrite <- (ghost_join _ _ _ _ _ _ Hsh); cancel].
    apply prop_right; repeat split; auto; try omega; try computable.
    - repeat (constructor; [computable|]); auto.
    - unfold MAX; omega. }
  { split; auto; split; [apply inv_precise | apply inv_positive]; auto. }
  forward_call (cprod, Ews).
  { unfold tcond; cancel. }
  forward_call (ccon, Ews).
  { unfold tcond; cancel. }
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
       Lock_inv sh lock (lock_pred gsh2 buf ends len next ghosts);
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
    + simpl; intros ? (? & ? & ? & (? & ?) & Hp).
      eapply almost_empty_join; eauto.
      { apply emp_almost_empty; auto. }
      destruct Hp as (? & ? & ? & ? & Hp); eapply almost_empty_join; eauto.
      { eapply lock_inv_almost_empty; eauto. }
      destruct Hp as (? & ? & ? & ? & Hp); eapply almost_empty_join; eauto.
      { eapply lock_inv_almost_empty; eauto. }
      destruct Hp as (? & ? & ? & ? & Hp); eapply almost_empty_join; eauto.
      { eapply cond_var_almost_empty; eauto. }
      destruct Hp as (? & ? & ? & ? & Hp); eapply almost_empty_join; eauto.
      { eapply cond_var_almost_empty; eauto. }
      destruct Hp as (? & ? & ? & ? & Hp); eapply almost_empty_join; eauto.
      { rewrite interp_ghost in *; eapply ghost_almost_empty; eauto. }
      { apply emp_almost_empty; auto. }
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
semax_func_cons body_add.
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
