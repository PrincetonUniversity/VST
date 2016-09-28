Require Import progs.verif_cond_queue.
Require Import progs.verif_incr.
Require Import msl.predicates_sl.
Require Import floyd.proofauto.
Require Import concurrency.semax_conc.
Require Import progs.ghost_queue.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn_thread spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makecond_spec := DECLARE _makecond (makecond_spec _).
Definition freecond_spec := DECLARE _freecond (freecond_spec _).
Definition wait_spec := DECLARE _wait (wait_spec _).
Definition signal_spec := DECLARE _signal (signal_spec _).

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

(* Note that a writable share must include all readable shares. *)
Definition lock_pred sh buf len next := Exp _ (fun reqs => Exp _ (fun n => Exp _ (fun n' =>
  Pred_list (Data_at _ Ews (tarray (tptr trequest) (Z.of_nat MAX)) (complete reqs) buf ::
             Data_at _ Ews (tarray tint 1) [Vint (Int.repr (Zlength reqs))] len ::
             Pred_prop (Int.min_signed <= n' <= n /\ n <= Int.max_signed /\ (length reqs <= MAX)%nat) ::
             Data_at _ Ews (tarray tint 1) [Vint (Int.repr n)] next ::
             Ghost sh tint (Vint (Int.repr n')) next ::
             map (fun r => Exp _ (fun data => Pred_list [Pred_prop (data < n);
               Data_at _ Tsh trequest (Vint (Int.repr data)) r])) reqs)))).

(* We would like the postcondition to tell us that the new request is  smaller than next. But because next is
   part of a lock invariant, we can only state this when the lock is held! *)
Definition get_request_spec :=
 DECLARE _get_request
  WITH sh : share, n : Z, lock : val, buf : val, len : val, next : val, gsh1 : share, gsh2 : share
  PRE [ ]
    PROP (readable_share sh; Int.min_signed <= n < Int.max_signed; sepalg.join gsh1 gsh2 Ews)
    LOCAL (gvar _requests_lock lock; gvar _next next)
    SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf len next)); ghost gsh1 tint (Vint (Int.repr n)) next)
  POST [ tptr trequest ]
    EX n' : Z, EX v : val, EX data : Z,
    PROP (data < n')
    LOCAL (temp ret_temp v)
    SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf len next));
         ghost gsh1 tint (Vint (Int.repr n')) next;
         data_at Tsh trequest (Vint (Int.repr data)) v).

Definition process_request_spec :=
 DECLARE _process_request
  WITH request : val, data : Z
  PRE [ _request OF (tptr trequest) ]
     PROP ()
     LOCAL (temp _request request)
     SEP (data_at Tsh trequest (Vint (Int.repr data)) request)
  POST [ tint ]
    PROP () LOCAL (temp ret_temp (Vint (Int.repr data))) SEP (emp).

Definition add_spec :=
 DECLARE _add
  WITH sh : share, n : Z, lock : val, request : val, data : Z, buf : val, len : val, next : val,
       cprod : val, ccon : val, gsh1 : share, gsh2 : share
  PRE [ _request OF (tptr trequest) ]
   PROP (readable_share sh; Int.min_signed <= n <= Int.max_signed; data < n)
   LOCAL (temp _request request; gvar _buf buf; gvar _length len; gvar _requests_lock lock;
          gvar _requests_producer cprod; gvar _requests_consumer ccon)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf len next)); cond_var sh cprod; cond_var sh ccon;
        data_at Tsh trequest (Vint (Int.repr data)) request; ghost gsh1 tint (Vint (Int.repr n)) next)
  POST [ tvoid ]
   EX n' : Z, PROP () LOCAL ()
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf len next)); cond_var sh cprod; cond_var sh ccon;
        ghost gsh1 tint (Vint (Int.repr n')) next).
(* Here's where we might need ghost variables to record the nature of the change? *)

Definition remove_spec :=
 DECLARE _remove
  WITH sh : share, n : Z, lock : val, buf : val, len : val, next : val, cprod : val, ccon : val,
       gsh1 : share, gsh2 : share
  PRE [ ]
   PROP (readable_share sh; Int.min_signed <= n < Int.max_signed; sepalg.join gsh1 gsh2 Ews)
   LOCAL (gvar _buf buf; gvar _length len; gvar _requests_lock lock; gvar _requests_producer cprod;
          gvar _requests_consumer ccon)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf len next)); cond_var sh cprod; cond_var sh ccon;
        ghost gsh1 tint (Vint (Int.repr n)) next)
  POST [ tptr trequest ]
   EX n' : Z, EX req : val, EX data : Z,
   PROP (data < n')
   LOCAL (temp ret_temp req)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf len next)); cond_var sh cprod; cond_var sh ccon;
        data_at Tsh trequest (Vint (Int.repr data)) req; ghost gsh1 tint (Vint (Int.repr n')) next).

Definition t_lock_pred := Pred_list [].

Definition f_spec :=
 DECLARE _f
  WITH sh : share, lock : val, wsh : share, buf : val, len : val, next : val, lockt : val
  PRE [ _arg OF (tptr tvoid) ]
   PROP ()
   LOCAL (gvar _buf buf; gvar _length len; gvar _requests_lock lock; temp _arg lockt)
   SEP (lock_inv sh lock (Interp (lock_pred wsh buf len next)); lock_inv sh lockt (Interp (t_lock_pred)))
  POST [ tvoid ]
   EX last : Z, EX res : val, EX v1 : Z, EX v2 : Z, EX v3 : Z,
   PROP (last < v1; v1 < v2; v2 < v3)
   LOCAL (temp _last (Vint (Int.repr last)); temp _res res)
   SEP (lock_inv sh lock (Interp (lock_pred wsh buf len next));
        lock_inv sh lockt (Interp (t_lock_pred));
        data_at Tsh (tarray tint 3) [Vint (Int.repr v1); Vint (Int.repr v2); Vint (Int.repr v3)] res).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Gprog : funspecs := augment_funspecs prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; makecond_spec; freecond_spec; wait_spec; signal_spec;
  malloc_spec; free_spec; get_request_spec; process_request_spec; add_spec; remove_spec; f_spec;
  main_spec].

Lemma lt_plus_one : forall n reqs, fold_right sepcon emp (map Interp (map (fun r => Exp _ (fun data =>
  Pred_list [Pred_prop (data < n); Data_at CompSpecs Tsh trequest (Vint (Int.repr data)) r])) reqs))
|-- fold_right sepcon emp (map Interp (map (fun r => Exp _ (fun data =>
  Pred_list [Pred_prop (data < n + 1); Data_at CompSpecs Tsh trequest (Vint (Int.repr data)) r])) reqs)).
Proof.
  induction reqs; simpl; entailer!.
  Exists x; entailer'; cancel.
Qed.

Lemma inv_precise : forall wsh buf len next (Hbuf : isptr buf) (Hlen : isptr len) (Hnext : isptr next),
  precise (Interp (lock_pred wsh buf len next)).
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

Lemma inv_positive : forall wsh buf len next,
  positive_mpred (Interp (lock_pred wsh buf len next)).
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
  forward_call (lock, sh, lock_pred gsh2 buf len next).
  simpl; Intros reqs n1 n2.
  forward.
  forward.
  forward.
  unfold upd_Znth, Znth; simpl.
  rewrite sublist.sublist_nil; simpl.
  rewrite add_repr.
  rewrite data_at_isptr, (data_at_isptr _ (tarray tint 1)), field_at_isptr; normalize.
  forward_call (lock, sh, lock_pred gsh2 buf len next).
  { simpl; Exists reqs (n1 + 1) (n1 + 1).
    unfold fold_right at 2; cancel.
    repeat rewrite interp_ghost.
    rewrite sepcon_comm.
    rewrite <- sepcon_assoc.
    rewrite (sepcon_comm _ (ghost _ _ _ _)).
    repeat rewrite <- sepcon_assoc.
    rewrite sepcon_assoc.
    eapply derives_trans; [apply sepcon_derives; [apply prop_and_same_derives, ghost_inj | apply derives_refl]|].
    normalize.
    assert (n2 = n).
    { rewrite <- (Int.signed_repr n2), <- (Int.signed_repr n); try omega; congruence. }
    subst; apply andp_right; [apply prop_right; repeat split; auto; try omega|].
    { admit. } (* Here's where we need better handling for max_signed. *)
    erewrite ghost_join; eauto.
    rewrite sepcon_assoc; eapply derives_trans; [eapply sepcon_derives; [|apply derives_refl]|].
    { apply change_ghost with (v' := Vint (Int.repr (n1 + 1))). }
    erewrite <- ghost_join; eauto; cancel.
    rewrite sepcon_assoc, sepcon_comm, sepcon_assoc.
    apply sepcon_derives; [apply lt_plus_one | cancel]. }
  { split; auto; split; [apply inv_precise | apply inv_positive]; auto. }
  eapply semax_pre; [|apply semax_return].
  subst POSTCONDITION; unfold abbreviate.
  go_lower; ent_iter.
  Exists (n1 + 1) (Vptr b i) n1; entailer'; cancel.
  { unfold field_compatible; simpl; repeat split; auto.
    unfold align_attr; simpl.
    simpl in *.
    eapply Zdivides_trans; eauto; unfold natural_alignment; exists 2; omega. }
Admitted.
(* We should actually do something smart when we hit max_signed, so we don't run out. *)

Lemma body_process_request : semax_body Vprog Gprog f_process_request process_request_spec.
Proof.
  start_function.
  forward.
  forward_call (request, sizeof trequest).
  { subst Frame; instantiate (1 := []); normalize.
    apply data_at_memory_block. }
  forward.
Qed.

Lemma derives_refl' : forall Delta P Q R, ENTAIL Delta, PROPx (P) (LOCALx (Q) (SEPx (R))) |--
  PROPx (P) (LOCALx (Q) (SEPx (R))).
Proof.
  go_lowerx; entailer'.
Qed.

Lemma body_add : semax_body Vprog Gprog f_add add_spec.
Proof.
  start_function.
  forward_call (lock, sh, lock_pred gsh2 buf len next).
  simpl; Intros reqs n1 n2.
  forward.
  unfold Znth; simpl.
  forward_while (EX reqs : list val, EX n' : Z,
   PROP (n <= n' <= Int.max_signed /\ (length reqs <= MAX)%nat)
   LOCAL (temp _len (Vint (Int.repr (Zlength reqs))); temp _request request; 
     gvar _buf buf; gvar _length len; gvar _requests_lock lock; gvar _requests_producer cprod;
     gvar _requests_consumer ccon)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf len next));
        data_at Ews (tarray (tptr trequest) (Z.of_nat MAX)) (complete reqs) buf;
        data_at Ews (tarray tint 1) [Vint (Int.repr (Zlength reqs))] len; emp;
        data_at Ews (tarray tint 1) [Vint (Int.repr n')] next;
        fold_right sepcon emp (map Interp (map (fun r => Exp _ (fun data0 =>
          Pred_list [Pred_prop (data0 < n'); Data_at CompSpecs Tsh trequest (Vint (Int.repr data0)) r])) reqs));
        cond_var sh cprod; cond_var sh ccon; @data_at CompSpecs Tsh trequest (Vint (Int.repr data)) request;
        ghost gsh1 tint (Vint (Int.repr n)) next * ghost gsh2 tint (Vint (Int.repr n)) next)).
  { Exists reqs n1; go_lower; entailer'.
    repeat rewrite interp_ghost.
    rewrite sepcon_comm.
    rewrite <- sepcon_assoc.
    rewrite (sepcon_comm _ (ghost _ _ _ _)).
    repeat rewrite <- sepcon_assoc.
    do 7 rewrite sepcon_assoc.
    eapply derives_trans; [apply sepcon_derives; [apply prop_and_same_derives, ghost_inj | apply derives_refl]|].
    normalize.
    assert (n2 = n).
    { rewrite <- (Int.signed_repr n2), <- (Int.signed_repr n); try omega; congruence. }
    subst; entailer'; cancel. }
  { go_lower; entailer'. }
  { match goal with H : _ /\ _ |- _ => destruct H end.
    forward_call (cprod, lock, sh, sh, lock_pred gsh2 buf len next).
    { simpl; cancel.
      Exists reqs0 n' n; unfold fold_right at 1; cancel.
      rewrite interp_ghost; cancel.
      rewrite <- (sepcon_emp (_ * _ * _)), sepcon_comm.
      apply sepcon_derives; [|cancel].
      apply andp_right; [apply prop_right; repeat split; auto; omega | apply derives_refl]. }
    simpl; Intros reqs2 n1' n2'.
    forward.
    Exists (reqs2, n1'); go_lower; unfold Znth; simpl; entailer'.
    repeat rewrite interp_ghost.
    rewrite sepcon_comm.
    rewrite <- sepcon_assoc.
    rewrite (sepcon_comm _ (ghost _ _ _ _)).
    repeat rewrite <- sepcon_assoc.
    do 7 rewrite sepcon_assoc.
    eapply derives_trans; [apply sepcon_derives; [apply prop_and_same_derives, ghost_inj | apply derives_refl]|].
    normalize.
    assert (n2' = n).
    { rewrite <- (Int.signed_repr n2'), <- (Int.signed_repr n); try omega; congruence. }
    subst; entailer'; cancel. }
  rewrite Int.signed_repr, Zlength_correct in HRE.
  forward.
  { unfold MAX in *; apply prop_right; rewrite Zlength_correct; omega. }
  forward.
  forward_call (ccon, sh).
  { simpl; cancel. }
  assert (length reqs0 < 10)%nat by (rewrite Nat2Z.inj_lt; auto).
  rewrite upd_complete; auto.
  unfold upd_Znth; repeat rewrite sublist.sublist_nil; simpl.
  rewrite add_repr.
  rewrite field_at_isptr, (field_at_isptr _ (tarray tint 1)), data_at_isptr; normalize.
  forward_call (lock, sh, lock_pred gsh2 buf len next).
  { simpl; unfold fold_right at 1; cancel.
    Exists (reqs0 ++ [request]) n' n.
    rewrite (data_at_isptr _ trequest); normalize.
    destruct request; try contradiction; simpl.
    repeat rewrite Zlength_correct; rewrite app_length; simpl.
    eapply derives_trans; [|apply prop_and_same_derives'; unfold MAX; omega].
    rewrite Nat2Z.inj_add; simpl; cancel.
    repeat rewrite map_app; rewrite sepcon_app; simpl.
    rewrite interp_ghost.
    Exists data; unfold fold_right at 1; cancel.
    entailer!; omega. }
  { split; auto; split; [apply inv_precise | apply inv_positive]; auto. }
  forward.
  Exists n; normalize; cancel.
  { match goal with H : _ /\ _ |- _ => destruct H end.
    pose proof Int.min_signed_neg.
    rewrite Zlength_correct; split; try omega.
    transitivity (Z.of_nat MAX); [Omega0 | simpl; computable]. }
Qed.

Lemma all_ptrs : forall n reqs, fold_right sepcon emp (map Interp (map (fun r => Exp _ (fun data =>
  Pred_list [Pred_prop (data < n); Data_at CompSpecs Tsh trequest (Vint (Int.repr data)) r])) reqs)) |--
  !!(Forall isptr reqs).
Proof.
  induction reqs; simpl; entailer.
  rewrite data_at_isptr.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IHreqs]|].
  eapply derives_trans; [apply saturate_aux20|].
  { apply andp_left1, derives_refl. }
  { apply derives_refl. }
  normalize.
Qed.

Lemma last_cons : forall {A} (d : A) l x, l <> [] -> last (x :: l) d = last l d.
Proof.
  intros.
  destruct l; auto.
  contradiction H; auto.
Qed.

Lemma nth_last : forall {A} (d : A) l, nth (length l - 1) l d = last l d.
Proof.
  induction l; auto.
  simpl nth.
  destruct (length l) eqn: Hlen.
  { destruct l; simpl in *; [auto | omega]. }
  rewrite last_cons; simpl in *; [|intro; subst; discriminate].
  rewrite NPeano.Nat.sub_0_r in IHl; auto.
Qed.

Lemma Znth_last : forall {A} l (d : A), Znth (Zlength l - 1) l d = last l d.
Proof.
  intros; unfold Znth.
  destruct (zlt (Zlength l - 1) 0).
  - destruct l; auto.
    rewrite Zlength_correct in *; simpl length in *.
    rewrite Nat2Z.inj_succ in *; omega.
  - rewrite Z2Nat.inj_sub; [|omega].
    rewrite Zlength_correct, Nat2Z.id; simpl.
    apply nth_last.
Qed.

Lemma body_remove : semax_body Vprog Gprog f_remove remove_spec.
Proof.
  start_function.
  forward_call (lock, sh, lock_pred gsh2 buf len next).
  simpl; Intros reqs n1 n2.
  forward.
  unfold Znth; simpl.
  forward_while (EX reqs : list val, EX n' : Z, PROP (n <= n' <= Int.max_signed /\ (length reqs <= MAX)%nat)
   LOCAL (temp _len (Vint (Int.repr (Zlength reqs))); gvar _buf buf; 
   gvar _length len; gvar _requests_lock lock; gvar _requests_producer cprod; gvar _requests_consumer ccon)
   SEP (lock_inv sh lock (Interp (lock_pred gsh2 buf len next));
        data_at Ews (tarray (tptr trequest) 10) (complete reqs) buf;
        data_at Ews (tarray tint 1) [Vint (Int.repr (Zlength reqs))] len; emp;
        data_at Ews (tarray tint 1) [Vint (Int.repr n')] next;
        fold_right sepcon emp (map Interp (map (fun r => Exp Z (fun data =>
          Pred_list [Pred_prop (data < n'); Data_at CompSpecs Tsh trequest (Vint (Int.repr data)) r])) reqs));
        cond_var sh cprod; cond_var sh ccon;
        ghost gsh1 tint (Vint (Int.repr n)) next; ghost gsh2 tint (Vint (Int.repr n)) next)).
  { Exists reqs n1; entailer.
    repeat rewrite interp_ghost.
    rewrite sepcon_comm.
    rewrite <- sepcon_assoc.
    rewrite (sepcon_comm _ (ghost _ _ _ _)).
    repeat rewrite <- sepcon_assoc.
    do 6 rewrite sepcon_assoc.
    eapply derives_trans; [apply sepcon_derives; [apply prop_and_same_derives, ghost_inj | apply derives_refl]|].
    normalize.
    assert (n2 = n).
    { rewrite <- (Int.signed_repr n2), <- (Int.signed_repr n); try omega; congruence. }
    subst; entailer'; cancel. }
  { entailer. }
  { forward_call (ccon, lock, sh, sh, lock_pred gsh2 buf len next).
    { simpl; cancel.
      Exists reqs0 n' n; unfold fold_right at 1; cancel.
      rewrite interp_ghost; cancel.
      rewrite <- (sepcon_emp (_ * _)), sepcon_comm.
      apply sepcon_derives; [|cancel].
      apply andp_right; [apply prop_right; repeat split; auto; try omega | apply derives_refl]. }
    simpl; Intros reqs2 n1' n2'.
    forward.
    Exists (reqs2, n1'); go_lower; unfold Znth; simpl; entailer'.
    repeat rewrite interp_ghost.
    rewrite sepcon_comm.
    rewrite <- sepcon_assoc.
    rewrite (sepcon_comm _ (ghost _ _ _ _)).
    repeat rewrite <- sepcon_assoc.
    do 6 rewrite sepcon_assoc.
    eapply derives_trans; [apply sepcon_derives; [apply prop_and_same_derives, ghost_inj | apply derives_refl]|].
    normalize.
    assert (n2' = n).
    { rewrite <- (Int.signed_repr n2'), <- (Int.signed_repr n); try omega; congruence. }
    subst; entailer'; cancel. }
  assert (length reqs0 > 0)%nat.
  { rewrite Zlength_correct in *.
    destruct (length reqs0); [|omega].
    contradiction HRE; auto. }
  assert (0 <= Zlength reqs0 - 1 < Z.of_nat MAX).
  { rewrite Zlength_correct.
    match goal with H : _ /\ _ |- _ => destruct H end; Omega0. }
  forward.
  { go_lower; normalize.
    rewrite Znth_complete; [|omega].
    do 4 rewrite sepcon_assoc; rewrite sepcon_comm.
    repeat rewrite sepcon_assoc.
    eapply derives_trans; [apply sepcon_derives; [apply prop_and_same_derives, all_ptrs | apply derives_refl]|].
    normalize; apply prop_right.
    apply Forall_Znth.
    { rewrite Zlength_correct; omega. }
    eapply Forall_impl; [|eauto].
    destruct a; auto. }
  forward.
  forward.
  forward_call (cprod, sh).
  { simpl; cancel. }
  rewrite field_at_isptr, (field_at_isptr _ (tarray tint 1)), data_at_isptr; normalize.
  forward_call (lock, sh, lock_pred gsh2 buf len next).
  { simpl.
    assert (reqs0 <> []) as Hreqs by (destruct reqs0; [simpl in *; omega | discriminate]).
    rewrite (app_removelast_last Vundef Hreqs) in *.
    replace (Zlength _ - 1) with (Zlength (removelast reqs0)).
    assert (length (removelast reqs0) < MAX)%nat.
    { rewrite app_length in *; simpl in *; omega. }
    rewrite remove_complete; auto.
    unfold upd_Znth; simpl.
    rewrite sublist.sublist_nil; simpl.
    Exists (removelast reqs0) n' n'; unfold fold_right at 1; cancel.
    repeat rewrite map_app; rewrite sepcon_app; simpl; cancel.
    erewrite sepcon_assoc, ghost_join; eauto.
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl |
      apply change_ghost with (v' := Vint (Int.repr n'))]|].
    erewrite <- ghost_join; eauto.
    rewrite interp_ghost; cancel.
    rewrite <- (sepcon_emp (_ * _ * _)), sepcon_comm.
    apply sepcon_derives; [|cancel].
    apply andp_right; [apply prop_right; repeat split; auto; omega | apply derives_refl].
    { repeat rewrite Zlength_correct; rewrite app_length; simpl; Omega0. } }
  { split; auto; split; [apply inv_precise | apply inv_positive]; auto. }
  forward.
  Exists n'; normalize.
  Exists (last reqs0 Vundef) x; normalize.
  apply andp_right.
  { apply prop_right; repeat split; auto.
    rewrite Znth_complete; [|omega].
    rewrite Znth_last; auto. }
  cancel.
Qed.

Lemma body_f : semax_body Vprog Gprog f_producer producer_spec.
Proof.
  start_function.

Qed.

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
  change (globvars2pred nil) with (@emp (environ->mpred) _ _).
  repeat rewrite sepcon_emp.
  rewrite <- seq_assoc.
  apply semax_seq' with (P' := PROP ( )
    LOCAL (gvar _buf gvar4; gvar _requests_producer gvar3; gvar _requests_consumer gvar2;
           gvar _length gvar1; gvar _requests_lock gvar0)
    SEP (data_at Ews (tarray (tptr trequest) (Z.of_nat MAX)) (repeat (Vint (Int.repr 0)) MAX) gvar4;
         data_at_ Ews tint gvar3; data_at_ Ews tint gvar2;
         data_at_ Ews (tarray tint 1) gvar1;
         data_at_ Ews (Tstruct 3%positive noattr) gvar0)).
  { eapply semax_for_const_bound_const_init with (P := fun _ => [])
      (Q := fun _ => [gvar _buf gvar4; gvar _requests_producer gvar3; gvar _requests_consumer gvar2; gvar _length gvar1; 
                      gvar _requests_lock gvar0])
      (R := fun i => [data_at Ews (tarray (tptr trequest) (Z.of_nat MAX))
             (repeat (Vint (Int.repr 0)) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (10 - i))) gvar4;
             data_at_ Ews tint gvar3; data_at_ Ews tint gvar2;
             data_at_ Ews (tarray tint 1) gvar1; data_at_ Ews tlock gvar0]);
    [reflexivity | try repable_signed | try repable_signed | reflexivity | try reflexivity; omega
    | intro; unfold map at 1; auto 50 with closed
    | cbv beta; simpl update_tycon
    | intro; cbv beta; simpl update_tycon; try solve [entailer!]
    | try apply semax_for_resolve_postcondition
    | intro; cbv beta; simpl update_tycon; abbreviate_semax;
      try (apply semax_extract_PROP; intro) ]; try computable.
    { unfold tlock, semax_conc._lock_t, trequest, _request_t; entailer!. }
    { unfold normal_ret_assert, tlock, semax_conc._lock_t; entailer!. }
    forward.
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
  forward_call (gvar0, Ews, lock_pred gvar4 gvar1).
  { unfold tlock, semax_conc._lock_t; cancel. }
  rewrite (data_at_isptr _ (tarray _ _)), field_at_isptr; normalize.
  forward_call (gvar0, Ews, lock_pred gvar4 gvar1).
  { simpl.
    Exists ([] : list val); simpl; entailer!. }
  { split; auto; split.
    - apply inv_precise; auto.
    - apply inv_positive. }
  forward_call (gvar3, Ews).
  { unfold tcond; cancel. }
  forward_call (gvar2, Ews).
  { unfold tcond; cancel. }
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  get_global_function'' _consumer.
  normalize.
  apply extract_exists_pre; intros c_.
  forward_call (c_, Vint (Int.repr 0), existT (fun ty => ty * (ty -> val -> Pred))%type
   (val * val * share * val * val * val)%type ((gvar4, gvar1, sh1, gvar0, gvar3, gvar2),
   fun (x : (val * val * share * val * val * val)) (_ : val) => let '(buf, len, sh, lock, cprod, ccon) := x in
     Pred_list [Pred_prop (readable_share sh); Lock_inv sh lock (lock_pred buf len);
                Cond_var _ sh cprod; Cond_var _ sh ccon])).
  { simpl; entailer.
    Exists _arg; entailer.
    Exists (fun x : val * val * share * val * val * val => let '(buf, len, sh, lock, cprod, ccon) := x in
      [(_buf, buf); (_length, len); (_requests_lock, lock); (_requests_producer, cprod);
       (_requests_consumer, ccon)]); entailer.
    subst Frame; instantiate (1 := [cond_var sh2 gvar2; cond_var sh2 gvar3;
      lock_inv sh2 gvar0 (Interp (lock_pred gvar4 gvar1))]).
    evar (body : funspec); replace (WITH _ : _ PRE [_] _ POST [_] _) with body.
    repeat rewrite sepcon_assoc; apply sepcon_derives; subst body; [apply derives_refl|].
    simpl.
    erewrite <- (sepcon_assoc (cond_var sh1 gvar2)), cond_var_join; eauto; cancel.
    repeat rewrite sepcon_assoc.
    erewrite <- (sepcon_assoc (cond_var sh1 gvar3)), cond_var_join; eauto; cancel.
    erewrite lock_inv_join; eauto; cancel.
    subst body; f_equal.
    extensionality.
    destruct x as (?, (((((?, ?), ?), ?), ?), ?)); simpl.
    f_equal; f_equal.
    unfold SEPx; simpl; normalize. }
  { simpl; intros ? Hpred.
    destruct Hpred as (? & ? & ? & (? & ?) & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hemp).
    eapply almost_empty_join; eauto; [|eapply almost_empty_join; eauto;
      [|eapply almost_empty_join; eauto; [|eapply almost_empty_join; eauto]]].
    - eapply prop_almost_empty; eauto.
    - eapply lock_inv_almost_empty; eauto.
    - eapply cond_var_almost_empty; eauto.
    - eapply cond_var_almost_empty; eauto.
    - eapply emp_almost_empty; eauto. }
  forward_call (gvar0, sh2, lock_pred gvar4 gvar1).
  simpl.
  Intro reqs; normalize.
  forward.
  unfold Znth; simpl.
  forward_while (EX reqs : list val, PROP (Forall isptr reqs; (length reqs <= MAX)%nat)
   LOCAL (temp _len (Vint (Int.repr (Zlength reqs))); gvar _consumer c_; gvar _buf gvar4; gvar _requests_producer gvar3;
   gvar _requests_consumer gvar2; gvar _length gvar1; gvar _requests_lock gvar0)
   SEP (data_at Ews (tarray (tptr trequest) (Z.of_nat MAX)) (complete reqs) gvar4;
   data_at Ews (tarray tint 1) [Vint (Int.repr (Zlength reqs))] gvar1;
   fold_right sepcon emp
     (map Interp (map (fun r : val => Exp Z (fun data : Z => Data_at CompSpecs Tsh trequest (Vint (Int.repr data)) r)) reqs));
   lock_inv sh2 gvar0 (Interp (lock_pred gvar4 gvar1));
   cond_var sh2 gvar2; cond_var sh2 gvar3)).
  { Exists reqs; entailer!. }
  { entailer. }
  { (* loop body *)
    forward_call (gvar3, gvar0, sh2, sh2, lock_pred gvar4 gvar1).
    { simpl; cancel.
      Exists reqs0; unfold fold_right at 1; cancel; entailer!. }
    simpl; Intro reqs'; normalize.
    forward.
    Exists reqs'; entailer!. }
  forward_call (gvar0, sh2, lock_pred gvar4 gvar1).
  { simpl; Exists reqs0; cancel.
    unfold fold_right at 1; entailer!. }
  { split; auto; split; [apply inv_precise | apply inv_positive]; auto. }
  destruct (split_readable_share _ H0) as (sh2' & sh3 & ? & ? & Hsh').
  get_global_function'' _producer.
  normalize.
  apply extract_exists_pre; intros p_.
  forward_call (p_, Vint (Int.repr 0), existT (fun ty => ty * (ty -> val -> Pred))%type
   (val * val * share * val * val * val)%type ((gvar4, gvar1, sh2', gvar0, gvar3, gvar2),
   fun (x : (val * val * share * val * val * val)) (_ : val) => let '(buf, len, sh, lock, cprod, ccon) := x in
     Pred_list [Pred_prop (readable_share sh); Lock_inv sh lock (lock_pred buf len);
                Cond_var _ sh cprod; Cond_var _ sh ccon])).
  { simpl; entailer.
    Exists _arg; entailer.
    Exists (fun x : val * val * share * val * val * val => let '(buf, len, sh, lock, cprod, ccon) := x in
      [(_buf, buf); (_length, len); (_requests_lock, lock); (_requests_producer, cprod);
       (_requests_consumer, ccon)]); entailer.
    subst Frame; instantiate (1 := [cond_var sh3 gvar2; cond_var sh3 gvar3;
      lock_inv sh3 gvar0 (Interp (lock_pred gvar4 gvar1))]).
    evar (body : funspec); replace (WITH _ : _ PRE [_] _ POST [_] _) with body.
    repeat rewrite sepcon_assoc; apply sepcon_derives; subst body; [apply derives_refl|].
    simpl.
    erewrite <- (sepcon_assoc (cond_var sh2' gvar2)), cond_var_join; eauto; cancel.
    repeat rewrite sepcon_assoc.
    erewrite <- (sepcon_assoc (cond_var sh2' gvar3)), cond_var_join; eauto; cancel.
    erewrite lock_inv_join; eauto; cancel.
    subst body; f_equal.
    extensionality.
    destruct x as (?, (((((?, ?), ?), ?), ?), ?)); simpl.
    f_equal; f_equal.
    unfold SEPx; simpl; normalize. }
  { simpl; intros ? Hpred.
    destruct Hpred as (? & ? & ? & (? & ?) & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hemp).
    eapply almost_empty_join; eauto; [|eapply almost_empty_join; eauto;
      [|eapply almost_empty_join; eauto; [|eapply almost_empty_join; eauto]]].
    - eapply prop_almost_empty; eauto.
    - eapply lock_inv_almost_empty; eauto.
    - eapply cond_var_almost_empty; eauto.
    - eapply cond_var_almost_empty; eauto.
    - eapply emp_almost_empty; eauto. }
  rewrite <- seq_assoc.
  apply semax_seq' with (P' := PROP () LOCAL () SEP (FF)).
  { match goal with |- semax _ ?P _ _ => eapply semax_loop with (Q' := P) end;
      forward; entailer!. }
  forward.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | ]).
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
eapply semax_func_cons_ext; try reflexivity.
{ admit. }
{ admit. }
eapply semax_func_cons_ext; try reflexivity.
{ admit. }
{ admit. }
semax_func_cons body_process.
semax_func_cons body_get_request.
semax_func_cons body_process_request.
semax_func_cons body_add.
semax_func_cons body_remove.
semax_func_cons body_producer.
semax_func_cons body_consumer.
semax_func_cons body_main.
Admitted.
