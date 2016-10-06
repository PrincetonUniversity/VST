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

Parameter ghost : forall (sh : share) (t : type) (v : reptype t) (p : val), mpred.
Axiom ghost_join : forall sh1 sh2 sh t v p, sepalg.join sh1 sh2 sh ->
  ghost sh1 t v p * ghost sh2 t v p = ghost sh t v p.
Axiom change_ghost : forall t v p v', ghost Ews t v p |-- ghost Ews t v' p.
Parameter Ghost : forall (sh : share) (t : type) (v : reptype t) (p : val), Pred.
Axiom interp_ghost : forall sh t v p, Interp (Ghost sh t v p) = ghost sh t v p.
Axiom ghost_inj : forall sh1 sh2 t v1 v2 p, ghost sh1 t v1 p * ghost sh2 t v2 p |-- !!(v1 = v2).

Definition MAX : nat := 10.

Definition rotate {A} (l : list A) n m := skipn (m - n) l ++ firstn (m - n) l.

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
  WITH sh : share, tsh : share, t : Z, lock : val, buf : val, ends : val, len : val, next : val, lockt : val,
       cprod : val, ccon : val, ghosts : list val, i : nat, g : val, gsh1 : share, gsh2 : share
  PRE [ _arg OF (tptr tvoid) ]
   PROP (readable_share sh; readable_share tsh; Int.min_signed <= t <= Int.max_signed;
         sepalg.join gsh1 gsh2 Ews; nth_error ghosts i = Some g)
   LOCAL (gvar _buf buf; gvar _ends ends; gvar _length len; gvar _next next; gvar _requests_lock lock;
          temp _arg lockt; gvar _requests_producer cprod; gvar _requests_consumer ccon)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf ends len next ghosts));
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

Lemma inv_precise : forall gsh2 buf ends len next ghosts (Hbuf : isptr buf) (Hlen : isptr len) (Hnext : isptr next),
  precise (Interp (lock_pred gsh2 buf ends len next ghosts)).
Proof.
  simpl.
(*  intros; apply derives_precise with (Q := data_at_ Tsh (tarray (tptr trequest) 10) buf *
    data_at_ Tsh (tarray tint 1) len * fold_right sepcon emp (map (data_at_ Tsh trequest) ).
       (map Interp
          (map (fun r : val => Exp Z (fun data : Z => Data_at CompSpecs Tsh trequest (Vint (Int.repr data)) r)) x))))).
  - intros ? (? & a1 & a2 & ? & Ha1 & ? & b & Hjoinb & Ha2 & Hemp).
    assert (predicates_hered.app_pred emp b) as Hb.
    { destruct Hemp as (? & ? & Hjoinb' & ((? & ?) & Hemp) & ?); simpl in *.
      specialize (Hemp _ _ Hjoinb'); subst; auto. }
    apply sepalg.join_comm in Hjoinb.
    specialize (Hb _ _ Hjoinb); subst.
    exists a1, a2; split; [auto|].
    split; [apply (data_at_data_at_ _ _ _ _ _ Ha1) | apply (data_at_data_at_ _ _ _ _ _ Ha2)].
  - destruct buf, len; try contradiction.
    apply precise_sepcon; [|(*apply data_at_precise; auto*)admit].
    intros; unfold data_at_, field_at_, field_at, at_offset; simpl.
    apply precise_andp2.
    rewrite data_at_rec_eq; unfold withspacer, at_offset; simpl.
    unfold array_pred, aggregate_pred.array_pred; simpl.
    unfold Zlength, Znth; simpl.
    apply precise_andp2.
    rewrite data_at_rec_eq; simpl.
    repeat (apply precise_sepcon; [apply mapsto_undef_precise; auto|]).
    apply precise_emp.*)
Admitted.

Lemma inv_positive : forall gsh2 buf ends len next ghosts,
  positive_mpred (Interp (lock_pred gsh2 buf ends len next ghosts)).
Proof.
Admitted.

(*Lemma data_at_inj : forall sh1 sh2 n1 n2 v, readable_share sh1 -> readable_share sh2 ->
  Int.min_signed <= n1 <= Int.max_signed -> Int.min_signed <= n2 <= Int.max_signed ->
  data_at sh1 (tarray tint 1) [Vint (Int.repr n1)] v *
  data_at sh2 (tarray tint 1) [Vint (Int.repr n2)] v |-- !!(n1 = n2).
Proof.
  intros.
  unfold data_at, field_at, at_offset; entailer; simpl.
  repeat rewrite data_at_rec_eq; simpl.
  unfold array_pred, aggregate_pred.array_pred; simpl; entailer.
  unfold at_offset, Znth; simpl.
  repeat rewrite data_at_rec_eq; simpl.
  unfold unfold_reptype; simpl.
  destruct H3, v; try contradiction; simpl.
  unfold mapsto; simpl.
  destruct (readable_share_dec sh1); [|contradiction].
  destruct (readable_share_dec sh2); [|contradiction].
  rewrite distrib_orp_sepcon; apply orp_left; [|entailer; discriminate].
  rewrite distrib_orp_sepcon2; apply orp_left; [|entailer; discriminate].
  eapply derives_trans; [|apply prop_derives].
  normalize.
  apply res_predicates.address_mapsto_value_cohere.
  intro X; rewrite <- (Int.signed_repr n1), <- (Int.signed_repr n2); congruence.
Qed.*)

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

Lemma length_complete : forall l m, (length l <= m)%nat -> length (complete m l) = m.
Proof.
  intros; unfold complete.
  rewrite app_length, repeat_length; omega.
Qed.

Lemma body_add : semax_body Vprog Gprog f_q_add add_spec.
Proof.
  start_function.
  forward_call (lock, sh, lock_pred gsh2 buf ends len next ghosts).
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
  time forward. (* 27s even with freeze *)
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
  time forward_call (lock, sh, lock_pred gsh2 buf ends len next ghosts). (* 36s *)
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
  time forward.
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
  time forward.
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
  forward_call (lock, sh, lock_pred gsh2 buf ends len next ghosts).
  { simpl.
    Exists reqs0 times0 (Nat.modulo (S head0) MAX) tail0 n0 (upd_Znth (Z.of_nat i) ns0 z).
    rewrite <- Zlength_correct.
    rewrite mod_Zmod, Nat2Z.inj_succ; simpl; [|omega].
    normalize.
    match goal with H : Forall _ (_ :: _) |- _ => inv H end.
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
    unfold fold_right at 2; cancel.
    exploit nth_ghost; eauto; intros (n2 & Hn2 & Heq); rewrite Heq.
    rewrite sepcon_comm.
    rewrite <- sepcon_assoc.
    rewrite (sepcon_comm _ (ghost _ _ _ _)).
    rewrite <- (sepcon_assoc _ (ghost _ _ _ _)), (sepcon_comm _ (ghost _ _ _ _)).
    repeat rewrite <- sepcon_assoc.
    do 4 rewrite sepcon_assoc.
    eapply derives_trans; [apply sepcon_derives; [apply prop_and_same_derives, ghost_inj | apply derives_refl]|].
    rewrite sepcon_andp_prop'; apply derives_extract_prop; intro.
    assert (Int.min_signed <= n2 < n0).
    { pose proof (nth_error_In _ _ Hn2) as Hin.
      match goal with X : Forall _ _ |- _ => rewrite Forall_forall in X; specialize (X _ Hin); auto end. }
    assert (n2 = t).
    { rewrite <- (Int.signed_repr n2), <- (Int.signed_repr t); try omega; congruence. }
    subst; erewrite ghost_join; eauto.
    eapply derives_trans; [apply sepcon_derives; [apply change_ghost with (v' := Vint (Int.repr z)) |
      apply derives_refl]|].
    erewrite <- ghost_join; eauto.
    repeat rewrite <- sepcon_assoc.
    rewrite (sepcon_assoc (ghost _ _ _ _)), (sepcon_comm (ghost gsh2 _ _ _)).
    repeat rewrite sepcon_assoc.
    rewrite <- (sepcon_assoc (ghost gsh2 _ _ _)), (sepcon_comm (ghost gsh2 _ _ _)).
    rewrite add_nth_ghost; auto.
    subst Frame; instantiate (1 := [!!(t < z <= Int.max_signed) && emp; ghost _ tint _ _; cond_var _ _;
      data_at _ trequest (_, _) _; cond_var _ _]).
    simpl; rewrite map_app, sepcon_app; cancel.
    normalize; apply andp_right; [apply prop_right | apply derives_refl].
    pose proof (nth_error_In _ _ Hn2) as Hin.
    match goal with X : _ /\ _ |- _ => destruct X as (? & X); rewrite Forall_forall in X;
      specialize (X _ Hin); omega end. }
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
  - admit.
  - apply precise_emp.
Admitted.

Lemma t_inv_positive : forall sh tsh cprod ccon lock lockt buf ends len next ghosts gsh1 gsh2 g,
  positive_mpred (Interp (t_lock_pred sh tsh cprod ccon lock lockt buf ends len next ghosts gsh1 gsh2 g)).
Proof.
Admitted.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  rewrite (lock_inv_isptr _ lockt); normalize.
  forward.
  destruct lockt as [| | | | |lockt o]; try contradiction; simpl.
  forward_for_simple_bound 3 (EX i : Z, PROP ()
      LOCAL (temp _l (Vptr lockt o); lvar _res (tarray tint 3) lvar0; 
             gvar _buf buf; gvar _ends ends; gvar _length len; gvar _next next; gvar _requests_lock lock;
             temp _arg (Vptr lockt o); gvar _requests_producer cprod; gvar _requests_consumer ccon)
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
    LOCAL (temp _l (Vptr lockt o); lvar _res (tarray tint 3) lvar0; 
           gvar _buf buf; gvar _ends ends; gvar _length len; gvar _next next; gvar _requests_lock lock;
           temp _arg (Vptr lockt o); gvar _requests_producer cprod; gvar _requests_consumer ccon)
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
Admitted.

Axiom ghost_alloc : forall D P Q R t v p, ENTAIL D, PROPx P (LOCALx Q (SEPx R)) |--
  PROPx P (LOCALx Q (SEPx (ghost Ews t v p :: R))).

Transparent lock_pred.

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
  { unfold tlock, semax_conc._lock_t, trequest, _request_t; entailer!. }
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
  eapply semax_pre; [apply ghost_alloc with (t := tint)(v := Vint (Int.repr (-1)))(p := Vint (Int.repr 1))|].
  eapply semax_pre; [apply ghost_alloc with (t := tint)(v := Vint (Int.repr (-1)))(p := Vint (Int.repr 2))|].
  eapply semax_pre; [apply ghost_alloc with (t := tint)(v := Vint (Int.repr (-1)))(p := Vint (Int.repr 3))|].
  set (ghosts := [Vint (Int.repr 1); Vint (Int.repr 2); Vint (Int.repr 3)]).
  forward_call (lock, Ews, lock_pred sh2 buf ends len next ghosts).
  rewrite (data_at_isptr _ (tarray _ _)), (field_at_isptr _ _ _ _ len), (field_at_isptr _ _ _ _ next);
    normalize.
  forward_call (lock, Ews, lock_pred sh2 buf ends len next ghosts).
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
    SEP (cond_var Ews ccon; cond_var Ews cprod;
         lock_inv Ews lock (Interp (lock_pred sh2 buf ends len next ghosts));
         ghost sh1 tint (Vint (Int.repr (-1))) (Vint (Int.repr 3));
         ghost sh1 tint (Vint (Int.repr (-1))) (Vint (Int.repr 2));
         ghost sh1 tint (Vint (Int.repr (-1))) (Vint (Int.repr 1));
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
   (SEPx ([cond_var s1 ccon; cond_var s1 cprod;
           lock_inv s1 lock (Interp (lock_pred sh2 buf ends len next ghosts))] ++
          firstn (Z.to_nat i) [lock_inv sh1 (Vptr b o) (Interp (t_lock_pred sh2 sh2 cprod ccon lock
              (Vptr b o) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 1))));
            lock_inv sh1 (Vptr b (Int.add o (Int.repr 16))) (Interp (t_lock_pred tsh2 sh2 cprod ccon lock
              (Vptr b (Int.add o (Int.repr 16))) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 2))));
            lock_inv sh1 (Vptr b (Int.add o (Int.repr 32))) (Interp (t_lock_pred tsh3 sh2 cprod ccon lock
              (Vptr b (Int.add o (Int.repr 32))) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 3))))] ++
          skipn (Z.to_nat i) (map (fun i => ghost sh1 tint (Vint (Int.repr (-1))) (Vint (Int.repr i))) [1; 2; 3]) ++
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
(*    clearbody lsh s0 s1.*)
    eapply semax_seq'.
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
    { subst Frame; instantiate (1 := [cond_var s0 ccon; cond_var s0 cprod;
        lock_inv s0 lock (Interp (lock_pred sh2 buf ends len next ghosts))] ++
        firstn (Z.to_nat i) [lock_inv sh1 (Vptr b o)
        (Interp (t_lock_pred sh2 sh2 cprod ccon lock (Vptr b o) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 1))));
        lock_inv sh1 (Vptr b (Int.add o (Int.repr 16)))
        (Interp (t_lock_pred tsh2 sh2 cprod ccon lock (Vptr b (Int.add o (Int.repr 16))) buf ends len next ghosts sh1
             sh2 (Vint (Int.repr 2))));
        lock_inv sh1 (Vptr b (Int.add o (Int.repr 32)))
        (Interp (t_lock_pred tsh3 sh2 cprod ccon lock (Vptr b (Int.add o (Int.repr 32))) buf ends len next ghosts sh1
             sh2 (Vint (Int.repr 3))))] ++
        skipn (Z.to_nat i) (map (fun i0 : Z => ghost sh1 tint (Vint (Int.repr (-1))) (Vint (Int.repr i0))) [1; 2; 3]) ++
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
      (share * share * Z * val * val * val * val * val * val * val * val * list val * nat * val * share * share)%type
      ((lsh, sh2, -1, lock, buf, ends, len, next, lockt, cprod, ccon, ghosts, Z.to_nat i, g, sh1, sh2),
     fun (x : (share * share * Z * val * val * val * val * val * val * val * val * list val * nat * val * share * share)) (_ : val) =>
     let '(sh, tsh, t, lock, buf, ends, len, next, lockt, cprod, ccon, ghosts, i, g, gsh1, gsh2) := x in
     Pred_list [Pred_prop (readable_share sh /\ Int.min_signed <= t <= Int.max_signed /\
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
      Exists (fun x : share * share * Z * _ * _ * _ * _ * val * val * _ * _ * list val * nat * val * share * share =>
        let '(sh, tsh, t, lock, buf, ends, len, next, lockt, cprod, ccon, ghosts, i, g, gsh1, gsh2) := x in
        [(_buf, buf); (_ends, ends); (_length, len); (_next, next); (_requests_lock, lock);
         (_requests_producer, cprod); (_requests_consumer, ccon)]).
      subst Frame; instantiate (1 := [cond_var s1 ccon; cond_var s1 cprod;
         lock_inv s1 lock (Interp (lock_pred sh2 buf ends len next ghosts))] ++
        firstn (Z.to_nat i) [lock_inv sh1 (Vptr b o) (Interp (t_lock_pred sh2 sh2 cprod ccon lock
            (Vptr b o) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 1))));
          lock_inv sh1 (Vptr b (Int.add o (Int.repr 16))) (Interp (t_lock_pred tsh2 sh2 cprod ccon lock
            (Vptr b (Int.add o (Int.repr 16))) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 2))));
          lock_inv sh1 (Vptr b (Int.add o (Int.repr 32))) (Interp (t_lock_pred tsh3 sh2 cprod ccon lock
            (Vptr b (Int.add o (Int.repr 32))) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 3))))] ++
        lock_inv sh1 lockt (Interp (t_lock_pred lsh sh2 cprod ccon lock lockt
            buf ends len next ghosts sh1 sh2 g)) ::
        skipn (S (Z.to_nat i)) (map (fun i => ghost sh1 tint (Vint (Int.repr (-1))) (Vint (Int.repr i))) [1; 2; 3]) ++
        skipn (S (Z.to_nat i)) [data_at_ Ews tlock (Vptr b o);
                            data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 16)));
                            data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 32)))]).
      repeat rewrite sepcon_app; simpl.
      repeat rewrite sepcon_app; simpl.
      repeat rewrite sepcon_assoc; apply sepcon_derives.
      { admit. }
      rewrite <- (sepcon_emp (_ * _)), sepcon_comm; apply sepcon_derives.
      { apply andp_right; auto; apply prop_right; split; [|split; [|split]]; auto; try computable.
        subst g; apply nth_error_nth.
        subst ghosts; simpl; Omega0. }
      rewrite interp_ghost; normalize.
      replace (fold_right sepcon emp (skipn _ (ghost _ _ _ _ :: _))) with
        (ghost sh1 tint (Vint (Int.repr (-1))) g * fold_right sepcon emp (skipn (Z.to_nat i)
         [ghost sh1 tint (Vint (Int.repr (-1))) (Vint (Int.repr 2));
          ghost sh1 tint (Vint (Int.repr (-1))) (Vint (Int.repr 3))])).
      apply sepalg.join_comm in Hshi.
      rewrite <- (lock_inv_join _ _ _ _ _ Hshi).
      repeat rewrite <- (cond_var_join _ _ _ _ Hshi).
      erewrite <- lock_inv_join; eauto; cancel.
      rewrite sepcon_comm; apply derives_refl.
      { destruct (eq_dec i 0); [|destruct (eq_dec i 1); [|assert (i = 2) by omega]]; subst; subst g; auto. }
    + admit.
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
   (SEPx (map (fun s1 => cond_var s1 ccon * cond_var s1 cprod *
                         lock_inv s1 lock (Interp (lock_pred sh2 buf ends len next ghosts)))
           (sh0 :: firstn (Z.to_nat i) [sh2; tsh2; tsh3]) ++
         skipn (Z.to_nat i) [lock_inv sh1 (Vptr b o) (Interp (t_lock_pred sh2 sh2 cprod ccon lock
           (Vptr b o) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 1))));
         lock_inv sh1 (Vptr b (Int.add o (Int.repr 16))) (Interp (t_lock_pred tsh2 sh2 cprod ccon lock
           (Vptr b (Int.add o (Int.repr 16))) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 2))));
         lock_inv sh1 (Vptr b (Int.add o (Int.repr 32))) (Interp (t_lock_pred tsh3 sh2 cprod ccon lock
           (Vptr b (Int.add o (Int.repr 32))) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 3))))] ++
         firstn (Z.to_nat i) (map (fun i => EX n : Z, ghost sh1 tint (Vint (Int.repr n)) (Vint (Int.repr i))) [1; 2; 3]) ++
         firstn (Z.to_nat i) [data_at_ Ews tlock (Vptr b o);
                              data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 16)));
                              data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 32)))]))).
  { go_lower; simpl.
    apply andp_right; [apply prop_right; auto|].
    apply andp_right; [apply prop_right; repeat split; auto |
      repeat rewrite sepcon_assoc; apply derives_refl]. }
  { set (lockt := Vptr b (Int.add o (Int.repr (16 * i)))).
    set (lsh := nth (Z.to_nat i) [sh2; tsh2; tsh3] sh0).
(*    set (s0 := nth (Z.to_nat i) [Ews; sh1; sh'] sh0). 
    set (s1 := nth (S (Z.to_nat i)) [Ews; sh1; sh'] sh0).*)
    set (g := nth (Z.to_nat i) ghosts (Vint (Int.repr 0))).
(*    assert (sepalg.join s1 lsh s0 /\ readable_share lsh) as (Hshi & ?).
    { destruct (eq_dec i 0); [|destruct (eq_dec i 1); [|assert (i = 2) by omega]]; subst;
        subst lsh s0 s1; auto. }*)
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
    { subst Frame; instantiate (1 := map (fun s1 => cond_var s1 ccon * cond_var s1 cprod *
         lock_inv s1 lock (Interp (lock_pred sh2 buf ends len next ghosts)))
        (sh0 :: firstn (Z.to_nat i) [sh2; tsh2; tsh3]) ++
        skipn (S (Z.to_nat i)) [lock_inv sh1 (Vptr b o) (Interp (t_lock_pred sh2 sh2 cprod ccon lock
          (Vptr b o) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 1))));
        lock_inv sh1 (Vptr b (Int.add o (Int.repr 16))) (Interp (t_lock_pred tsh2 sh2 cprod ccon lock
          (Vptr b (Int.add o (Int.repr 16))) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 2))));
        lock_inv sh1 (Vptr b (Int.add o (Int.repr 32))) (Interp (t_lock_pred tsh3 sh2 cprod ccon lock
          (Vptr b (Int.add o (Int.repr 32))) buf ends len next ghosts sh1 sh2 (Vint (Int.repr 3))))] ++
        firstn (Z.to_nat i) (map (fun i0 : Z => EX n : Z, ghost sh1 tint (Vint (Int.repr n)) (Vint (Int.repr i0))) [1; 2; 3]) ++
        firstn (Z.to_nat i) [data_at_ Ews tlock (Vptr b o); data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 16)));
                             data_at_ Ews tlock (Vptr b (Int.add o (Int.repr 32)))]).
      repeat rewrite sepcon_app; cancel.
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
  freeze [12; 13; 14; 15; 16; 17] FR.
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
  forward_call (lock, Ews, lock_pred sh2 buf ends len next ghosts).
  { split; auto; apply inv_positive. }
  forward_call (cprod, Ews).
  forward_call (ccon, Ews).
  eapply semax_pre; [|apply semax_return].
  thaw FR.
  (* timeout 80 entailer. XX times out, go_lower also times out *)
  go_lowerx; entailer'.
  subst POSTCONDITION; unfold abbreviate, frame_ret_assert, function_body_ret_assert.
  simpl; entailer.
Admitted.

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
semax_func_cons body_remove.
semax_func_cons body_f.
semax_func_cons body_main.
Admitted.
