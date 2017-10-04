Require Import VST.progs.conc_queue_specs.
Require Import VST.progs.conclib.
Require Import VST.progs.queue_ex.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
(*Definition release_spec := DECLARE _release release_spec.*)
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
(*Definition freelock_spec := DECLARE _freelock (freelock_spec _).*)
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.
(*Definition makecond_spec := DECLARE _makecond (makecond_spec _).
Definition freecond_spec := DECLARE _freecond (freecond_spec _).
Definition wait_spec := DECLARE _waitcond (wait2_spec _).
Definition signal_spec := DECLARE _signalcond (signal_spec _).*)

Notation f_lock_inv lsh gsh gsh1 gsh2 p' p lock t locksp lockt resultsp :=
  (EX p1 : val, EX p2 : val, EX p3 : val, EX i1 : int, EX i2 : int, EX i3 : int,
     data_at gsh (tptr tqueue_t) p p' *
     lqueue lsh tint (tc_val tint) p lock gsh1 gsh2
       [QRem p1 (Vint i1); QRem p2 (Vint i2); QRem p3 (Vint i3)] *
     data_at gsh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp *
     field_at Ews (tarray (tarray tint 3) 3) [ArraySubsc t] [Vint i1; Vint i2; Vint i3] resultsp).

Definition f_lock_pred lsh gsh tsh gsh1 gsh2 p' p lock t locksp lockt resultsp :=
  selflock (f_lock_inv lsh gsh gsh1 gsh2 p' p lock t locksp lockt resultsp) tsh lockt.

Definition f_spec :=
 DECLARE _f
  WITH tid : val, x : share * share * share * share * share * val * val * val * Z * val * val * val
  PRE [ _arg OF (tptr tvoid) ]
   let '(lsh, gsh, tsh, gsh1, gsh2, p', p, lock, t, locksp, lockt, resultsp) := x in
   PROP ()
   LOCAL (temp _arg tid; gvar _q0 p'; gvar _thread_locks locksp; gvar _results resultsp)
   SEP (!!(0 <= t < 3 /\ isptr lockt /\ readable_share lsh /\ readable_share gsh /\ readable_share tsh /\
           sepalg.join gsh1 gsh2 Tsh) && emp;
        data_at gsh (tptr tqueue_t) p p'; lqueue lsh tint (tc_val tint) p lock gsh1 gsh2 [];
        data_at Tsh tint (vint t) tid; malloc_token Tsh (sizeof tint) tid;
        data_at gsh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp;
        field_at_ Ews (tarray (tarray tint 3) 3) [ArraySubsc t] resultsp;
        lock_inv tsh lockt (f_lock_pred lsh gsh tsh gsh1 gsh2 p' p lock t locksp lockt resultsp))
  POST [ tptr tvoid ] PROP () LOCAL () SEP (emp).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog [] u
  POST [ tint ] main_post prog [] u.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; (*release_spec;*) release2_spec;
  makelock_spec; (*freelock_spec;*) freelock2_spec; spawn_spec; (*makecond_spec; freecond_spec; wait_spec; signal_spec;*)
  surely_malloc_spec prog; q_new_spec prog; q_del_spec prog; q_add_spec prog; q_remove_spec prog;
  (*q_tryremove_spec prog;*) f_spec; main_spec]).

Lemma f_inv_precise : forall lsh gsh tsh gsh1 gsh2 p' p lock t locksp lockt resultsp,
  precise (f_lock_pred lsh gsh tsh gsh1 gsh2 p' p lock t locksp lockt resultsp).
Proof.
  intros; unfold f_lock_pred.
  apply selflock_precise.
  apply derives_precise' with (Q := data_at gsh (tptr tqueue_t) p p' *
    (EX h : hist (reptype tint), lqueue lsh tint (tc_val tint) p lock gsh1 gsh2 h) *
    data_at gsh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp *
    field_at_ Ews (tarray (tarray tint 3) 3) [ArraySubsc t] resultsp).
  - Intros p1 p2 p3 i1 i2 i3; cancel.
    Exists [QRem p1 (Vint i1); QRem p2 (Vint i2); QRem p3 (Vint i3)]; auto.
  - repeat apply precise_sepcon; auto.
Qed.

Lemma f_inv_positive : forall lsh gsh tsh gsh1 gsh2 p' p lock t locksp lockt resultsp,
  readable_share gsh ->
  positive_mpred (f_lock_pred lsh gsh tsh gsh1 gsh2 p' p lock t locksp lockt resultsp).
Proof.
  intros; apply selflock_positive; repeat (apply ex_positive; intro).
  do 3 apply positive_sepcon1.
  apply data_at_positive; auto.
Qed.
Hint Resolve f_inv_precise f_inv_positive.

Lemma lock_struct_array : forall sh z (v : list val) p,
  data_at sh (tarray (tptr (Tstruct _lock_t noattr)) z) v p =
  data_at sh (tarray (tptr tlock) z) v p.
Proof.
  intros.
  unfold data_at, field_at, at_offset; rewrite !data_at_rec_eq; simpl; f_equal.
Qed.

(* lookup_and_change_compspecs interacts poorly with polymorphic specs, and in particular the partially applied
   compspecs-taking functions like reptype and data_at. *)
Ltac forward_call_id1_wow' witness :=
let Frame := fresh "Frame" in
let A := fresh "A" in
let wit := fresh "wit" in
 evar (Frame: list (mpred));
 evar (A: rmaps.TypeTree);
 evar (wit: functors.MixVariantFunctor._functor
              (rmaps.dependent_type_functor_rec nil A) mpred);
 match goal with |- @semax ?CS _ _ _ _ _ =>
 eapply (@semax_call_id1_wow A wit Frame);
 [ check_function_name | subst A; reflexivity
 | find_spec_in_globals | check_result_type
 | apply Coq.Init.Logic.I | check_parameter_types
 | check_prove_local2ptree
 | check_typecheck
 | instantiate (1 := witness) in (Value of wit);
   check_funspec_precondition
 | check_prove_local2ptree
 | check_cast_params | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right_sepcon at 1 2; cancel
 | subst wit; cbv beta iota zeta; extensionality rho;
   repeat rewrite exp_uncurry;
   try rewrite no_post_exists; repeat rewrite exp_unfold;
   first [apply exp_congr; intros ?vret; reflexivity
           | give_EX_warning
           ]
 | prove_delete_temp
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto; subst A wit
 ] end.

Ltac forward_call_id00_wow' witness :=
let Frame := fresh "Frame" in
let A := fresh "A" in
let wit := fresh "wit" in
 evar (Frame: list (mpred));
 evar (A: rmaps.TypeTree);
 evar (wit: functors.MixVariantFunctor._functor
              (rmaps.dependent_type_functor_rec nil A) mpred);
 match goal with |- @semax ?CS _ _ _ _ _ =>
 eapply (@semax_call_id00_wow A wit Frame);
 [ check_function_name | subst A; reflexivity
 | find_spec_in_globals | check_result_type | check_parameter_types
 | check_prove_local2ptree
 | check_typecheck
 | instantiate (1 := witness) in (Value of wit);
   check_funspec_precondition
 | check_prove_local2ptree
 | check_cast_params | reflexivity
 | Forall_pTree_from_elements
 | Forall_pTree_from_elements
 | unfold fold_right_sepcon at 1 2; cancel
 | subst wit; cbv beta iota zeta;
    repeat rewrite exp_uncurry;
    try rewrite no_post_exists0;
    first [reflexivity | extensionality; simpl; reflexivity]
 | unify_postcondition_exps
 | unfold fold_right_and; repeat rewrite and_True; auto; subst A wit
 ]
 end.

Lemma body_f : semax_body Vprog Gprog f_f f_spec.
Proof.
  start_function.
  rewrite (data_at_isptr _ tint); Intros.
  replace_SEP 3 (data_at Tsh tint (vint t) (force_val (sem_cast_neutral tid))).
  { rewrite sem_cast_neutral_ptr; auto; go_lowerx; cancel. }
  forward.
  rewrite sem_cast_neutral_ptr; auto; simpl.
  replace_SEP 3 (memory_block Tsh (sizeof tint) tid).
  { go_lower.
    apply data_at_memory_block. }
  forward_call (tid, sizeof tint).
  { simpl; cancel. }
  rewrite lqueue_isptr; Intros.
  forward.
  forward_for_simple_bound 3 (EX i : Z, PROP ()
    LOCAL (temp _q1 p; temp _t (vint t); temp _arg tid; gvar _q0 p'; gvar _thread_locks locksp;
           gvar _results resultsp)
    SEP (data_at gsh (tptr tqueue_t) p p';
         data_at gsh (tarray (tptr tlock) 3) (upd_Znth t [Vundef; Vundef; Vundef] lockt) locksp;
         lock_inv tsh lockt (f_lock_pred lsh gsh tsh gsh1 gsh2 p' p lock t locksp lockt resultsp);
         EX vals : _, !!(Zlength vals = i) &&
           (lqueue lsh tint (tc_val tint) p lock gsh1 gsh2 (map (fun x => QRem (fst x) (Vint (snd x))) vals) *
            field_at Ews (tarray (tarray tint 3) 3) [ArraySubsc t]
              (map (fun x => Vint (snd x)) vals ++ repeat Vundef (Z.to_nat (3 - i))) resultsp))).
  { Exists ([] : list (val * int)); repeat entailer!. }
  { Intros vals.
(*    forward_call (lsh, q_rem_args tint (tc_val tint)
      (map (fun x => QRem (fst x) (Vint (snd x))) vals), p, lock, gsh1, gsh2).*)
    rewrite <- seq_assoc; eapply semax_seq'; [forward_call_id1_wow' (lsh, q_rem_args tint (tc_val tint)
      (map (fun x => QRem (fst x) (Vint (snd x))) vals), p, lock, gsh1, gsh2) | after_forward_call].
    Intros x; destruct x as (p1 & v1).
    simpl; forward.
    rewrite data_at_isptr; Intros.
    rewrite sem_cast_neutral_ptr; auto; simpl.
    forward.
    replace_SEP 1 (memory_block Tsh (sizeof tint) p1).
    { go_lowerx; cancel.
      apply data_at_memory_block. }
    forward_call (p1, sizeof tint).
    { simpl; cancel. }
    forward.
    destruct v1; try contradiction.
    Exists (vals ++ [(p1, i0)]); rewrite Zlength_app, Zlength_cons, Zlength_nil; entailer!.
    rewrite !map_app; simpl; cancel.
    replace (Z.to_nat (3 - Zlength vals)) with (S (Z.to_nat (3 - (Zlength vals + 1)))).
    simpl; rewrite upd_Znth_app2; [|rewrite !Zlength_map, !Zlength_correct; abstract omega].
    rewrite Zlength_map, Zminus_diag, upd_Znth0, sublist_1_cons, sublist_same, <- app_assoc; auto.
    - rewrite Zlength_cons; abstract omega.
    - rewrite <- Z2Nat.inj_succ; [f_equal|]; abstract omega. }
  Intros vals.
  rewrite <- lock_struct_array.
  forward.
  { rewrite upd_Znth_same; [entailer! | Omega0]. }
  rewrite upd_Znth_same; [|Omega0].
  forward_call (lockt, tsh, f_lock_inv lsh gsh gsh1 gsh2 p' p lock t locksp lockt resultsp,
                f_lock_pred lsh gsh tsh gsh1 gsh2 p' p lock t locksp lockt resultsp).
  { lock_props.
    { apply selflock_rec. }
    unfold f_lock_pred; rewrite selflock_eq at 2.
    do 3 (destruct vals; [rewrite Zlength_nil in *; omega | rewrite Zlength_cons in *]).
    destruct vals; [|rewrite Zlength_cons, Zlength_correct in *; omega].
    destruct p2 as (p3, i3), p1 as (p2, i2), p0 as (p1, i1).
    rewrite lock_struct_array.
    Exists p1 p2 p3 i1 i2 i3; subst Frame; instantiate (1 := []); simpl; cancel.
    apply lock_inv_later. }
  forward.
Qed.

Opaque upto.

Lemma main_loop1 : forall {Espec : OracleKind} (q0 locks results lvar0 : val) q lock
  lshs1 (Hlenl1 : Zlength lshs1 = 3)
  (Hlshs1 : forall i : Z, 0 <= i < 3 -> let '(a, b) := Znth i lshs1 (Tsh, Tsh) in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) lshs1 (Tsh, Tsh))))
  gshs1 (Hglen1 : Zlength gshs1 = 3)
  (Hgshs1 : forall i : Z, 0 <= i < 3 -> let '(a, b) := Znth i gshs1 (Ews, Ews) in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) gshs1 (Ews, Ews))))
  sh1 sh2 (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2) (Hsh : sepalg.join sh1 sh2 Tsh)
  (f_lock := fun x => f_lock_pred (snd (Znth (2 - fst x) lshs1 (Tsh, Tsh)))
    (snd (Znth (2 - fst x) gshs1 (Ews, Ews))) sh2 sh1 sh2 q0 q lock (fst x) locks (snd x) results)
  flocks (Hlen : Zlength flocks = 3) (Hflocks : Forall isptr flocks)
  (Hresults : field_compatible (tarray (tarray tint 3) 3) [] results) i (Hi : 0 <= i < 3),
semax (initialized_list [_i; _i__1; _t'1] (func_tycontext f_main Vprog Gprog))
  (PROP ( )
   LOCAL (temp _i__1 (vint i); temp _t'1 q; gvar _results results; gvar _thread_locks locks;
   gvar _q0 q0)
   SEP (lqueue (fst (Znth (3 - i) lshs1 (Tsh, Tsh))) tint (is_int I32 Signed) q lock sh1 sh2 [];
   data_at_ Ews (tarray (tarray tint 3) (3 - i))
     (offset_val (nested_field_offset (tarray (tarray tint 3) 3) [ArraySubsc i]) results);
   field_at (fst (Znth (3 - i) gshs1 (Ews, Ews))) (tptr tqueue_t) [] q q0;
   data_at (fst (Znth (3 - i) gshs1 (Ews, Ews))) (tarray (tptr (Tstruct _lock_t noattr)) 3) flocks locks;
   fold_right sepcon emp
     (map (fun x : Z * val => lock_inv sh1 (snd x) (f_lock x)) (sublist 0 i (combine (upto 3) flocks)));
   fold_right sepcon emp
     (map (fun x : Z * val => lock_inv Tsh (snd x) (f_lock x)) (sublist i 3 (combine (upto 3) flocks)));
   fold_right sepcon emp (map (fun x : val => malloc_token Tsh (sizeof tlock) x) flocks)))
  (Ssequence
     (Ssequence
        (Scall (Some _t'3) (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
           [Esizeof tint tuint]) (Sset _t (Ecast (Etempvar _t'3 (tptr tvoid)) (tptr tint))))
     (Ssequence (Sassign (Ederef (Etempvar _t (tptr tint)) tint) (Etempvar _i__1 tint))
        (Scall None
           (Evar _spawn
              (Tfunction
                 (Tcons (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))
                    (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
           [Ecast
              (Eaddrof (Evar _f (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))
                 (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default)))
              (tptr tvoid); Ecast (Etempvar _t (tptr tint)) (tptr tvoid)])))
  (normal_ret_assert
     (PROP (0 <= i + 1 <= 3)
      LOCAL (temp _i__1 (vint i); temp _t'1 q; gvar _results results; gvar _thread_locks locks;
      gvar _q0 q0)
      SEP (lqueue (fst (Znth (3 - (i + 1)) lshs1 (Tsh, Tsh))) tint (is_int I32 Signed) q lock sh1 sh2 [];
      data_at_ Ews (tarray (tarray tint 3) (3 - (i + 1)))
        (offset_val (nested_field_offset (tarray (tarray tint 3) 3) [ArraySubsc (i + 1)]) results);
      field_at (fst (Znth (3 - (i + 1)) gshs1 (Ews, Ews))) (tptr tqueue_t) [] q q0;
      data_at (fst (Znth (3 - (i + 1)) gshs1 (Ews, Ews))) (tarray (tptr (Tstruct _lock_t noattr)) 3) flocks locks;
      fold_right sepcon emp
        (map (fun x : Z * val => lock_inv sh1 (snd x) (f_lock x)) (sublist 0 (i + 1) (combine (upto 3) flocks)));
      fold_right sepcon emp
        (map (fun x : Z * val => lock_inv Tsh (snd x) (f_lock x)) (sublist (i + 1) 3 (combine (upto 3) flocks)));
      fold_right sepcon emp (map (fun x : val => malloc_token Tsh (sizeof tlock) x) flocks)))).
Proof.
  intros.
  simpl initialized_list; unfold func_tycontext, make_tycontext.
  forward_call (sizeof tint).
  { simpl; computable. }
  Intro t.
  rewrite malloc_compat; auto; Intros.
  rewrite memory_block_data_at_; auto.
  forward.
  get_global_function'' _f; Intros.
  apply extract_exists_pre; intros f_.
  specialize (Hgshs1 (2 - i)); exploit Hgshs1; [abstract omega|].
  destruct (Znth (2 - i) gshs1 (Ews, Ews)) eqn: Hg1.
  replace (2 - i + 1) with (3 - i) by abstract omega.
  intros (? & ? & Hglsh); rewrite <- (data_at_share_join _ _ _ _ _ _ Hglsh),
    <- (field_at_share_join _ _ _ _ _ _ _ Hglsh); auto.
  specialize (Hlshs1 (2 - i)); exploit Hlshs1; [omega|].
  destruct (Znth (2 - i) lshs1 (Tsh, Tsh)) eqn: Hl1.
  replace (2 - i + 1) with (3 - i) by abstract omega.
  intros (? & ? & Hllsh); replace_SEP 3 (lqueue s tint (tc_val tint) q lock sh1 sh2 [] *
    lqueue s0 tint (tc_val tint) q lock sh1 sh2 []).
  { go_lowerx.
    rewrite sepcon_emp; apply lqueue_share_join_nil; auto. }
  assert (length (upto 3) = length flocks).
  { rewrite upto_length; rewrite Zlength_correct in *; abstract Omega0. }
  forward_spawn (share * share * share * share * share * val * val * val * Z * val * val * val)%type
    (f_, t, (snd (Znth (2 - i) lshs1 (Tsh, Tsh)), snd (Znth (2 - i) gshs1 (Ews, Ews)), sh2, sh1, sh2, q0, q,
             lock, i, locks, Znth i flocks Vundef, results),
    fun (x : (share * share * share * share * share * val * val * val * Z * val * val * val)%type) (tid : val) =>
    let '(lsh, gsh, tsh, gsh1, gsh2, p', p, lock, t, locksp, lockt, resultsp) := x in
    fold_right sepcon emp
      [!!(0 <= t < 3 /\ isptr lockt /\ readable_share lsh /\ readable_share gsh /\ readable_share tsh /\
           sepalg.join gsh1 gsh2 Tsh) && emp;
        data_at gsh (tptr tqueue_t) p p'; lqueue lsh tint (tc_val tint) p lock gsh1 gsh2 [];
        data_at Tsh tint (vint t) tid; malloc_token Tsh (sizeof tint) tid;
        data_at gsh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp;
        field_at_ Ews (tarray (tarray tint 3) 3) [ArraySubsc t] resultsp;
        lock_inv tsh lockt (f_lock_pred lsh gsh tsh gsh1 gsh2 p' p lock t locksp lockt resultsp)]).
  { unfold spawn_pre; go_lower.
    entailer!.
    { rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto.
      rewrite Hg1, Hl1; repeat split; auto.
      apply Forall_Znth; auto; omega. }
    Exists _arg (fun x : (share * share * share * share * share * val * val * val * Z * val * val * val) =>
      let '(lsh, gsh, tsh, gsh1, gsh2, p', p, lock, t, locksp, lockt, resultsp) := x in
      [(_q0, p'); (_thread_locks, locksp); (_results, resultsp)]).
    rewrite !sepcon_assoc; apply sepcon_derives.
    { apply derives_refl'.
      f_equal; f_equal; extensionality; destruct x as (?, x); repeat destruct x as (x, ?); simpl.
      rewrite !sepcon_emp; reflexivity. }
    erewrite sublist_split with (lo := i), <- Znth_cons_sublist;
      try rewrite Zlength_combine, Zlength_upto, Z.min_l; simpl; try omega.
    instantiate (1 := (3, Vundef)).
    rewrite <- Znth_map', combine_snd; auto.
    rewrite <- (lock_inv_share_join sh1 sh2 Tsh); auto.
    unfold tarray at 1; erewrite data_at__eq, split2_data_at_Tarray with (n1 := 1); try apply eq_JMeq;
      try reflexivity; [| omega | rewrite sublist_same; auto].
    rewrite Hg1, Hl1; simpl.
    cancel.
    rewrite (sepcon_comm _ (data_at t1 _ _ _)); rewrite !sepcon_assoc; apply sepcon_derives.
    { rewrite lock_struct_array; apply stronger_array_ext.
      { unfold unfold_reptype; simpl.
        rewrite upd_Znth_Zlength; Omega0. }
      intros; unfold unfold_reptype, default_val; simpl.
      destruct (eq_dec i0 i).
      - subst; rewrite upd_Znth_same; [apply stronger_refl | Omega0].
      - rewrite upd_Znth_diff; auto.
        rewrite Znth_repeat with (x := Vundef)(n0 := 3%nat); apply stronger_default_val. }
    rewrite <- !sepcon_assoc, (sepcon_comm (lqueue _ _ _ _ _ _ _ _)), !sepcon_assoc; apply sepcon_derives.
    { eapply derives_trans; [|unfold field_at_; apply field_at_stronger, stronger_default_val].
      unfold data_at, field_at, at_offset; entailer!.
      { eapply field_compatible_cons_Tarray; try eassumption; reflexivity. }
      rewrite data_at_rec_eq; simpl.
      unfold array_pred, aggregate_pred.array_pred; simpl.
      unfold at_offset.
      rewrite offset_offset_val, Z.add_0_l, Z.add_0_r; entailer!. }
    rewrite <- !sepcon_assoc, (sepcon_comm _ (lock_inv sh2 _ _)), !sepcon_assoc; apply sepcon_derives.
    { apply derives_refl'; unfold f_lock; simpl; f_equal.
      rewrite <- Znth_map' with (f := fst), combine_fst; [|assumption].
      simpl; rewrite Znth_upto with (m := 3%nat); [|simpl; omega].
      rewrite Hl1, Hg1; simpl.
      rewrite <- Znth_map', combine_snd; [reflexivity | assumption]. }
    cancel.
    { unfold default_val; simpl.
      rewrite Zlength_list_repeat; auto; abstract omega. } }
  entailer!.
  replace (3 - (i + 1)) with (2 - i) by abstract omega; rewrite Hg1, Hl1; simpl; cancel.
  erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1, map_app, sepcon_app;
    try rewrite Zlength_combine, Zlength_upto, Z.min_l; simpl; try omega.
  instantiate (1 := (3, Vundef)).
  rewrite <- Znth_map' with (f := snd), combine_snd; simpl; [cancel | auto].
  replace (3 - i - 1) with (2 - i) by (clear; omega).
  unfold field_address0.
  destruct (field_compatible0_dec _ _ _).
  simpl; rewrite offset_offset_val.
  rewrite Z.mul_add_distr_l; simpl; cancel.
  { rewrite data_at_isptr; Intros; contradiction. }
  { exists 2; auto. }
Qed.

Lemma main_loop2 : forall {Espec : OracleKind} (q0 q lock locks results : val)
  sh1 sh2 (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2) (Hsh : sepalg.join sh1 sh2 Tsh)
  gshs1 (Hglen1 : Zlength gshs1 = 3)
  (Hgshs1 : forall i : Z,
         0 <= i < 3 ->
         let
         '(a, b) := Znth i gshs1 (Ews, Ews) in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) gshs1 (Ews, Ews))))
  lshs1 (Hlenl1 : Zlength lshs1 = 3)
  (Hlshs1 : forall i : Z,
         0 <= i < 3 ->
         let
         '(a, b) := Znth i lshs1 (Tsh, Tsh) in
          readable_share a /\ readable_share b /\ sepalg.join a b (fst (Znth (i + 1) lshs1 (Tsh, Tsh))))
  (f_lock := fun x : Z * val =>
          f_lock_pred (snd (Znth (2 - fst x) lshs1 (Tsh, Tsh))) (snd (Znth (2 - fst x) gshs1 (Ews, Ews))) sh2 sh1
            sh2 q0 q lock (fst x) locks (snd x) results)
  flocks (Hfl : Zlength flocks = 3) (Hflocks : Forall isptr flocks)
  (Hresults : field_compatible (tarray (tarray tint 3) 3) [] results)
  (lsh' := fst (Znth 0 lshs1 (Tsh, Tsh))) (gsh' := fst (Znth 0 gshs1 (Ews, Ews)))
  (Hgsh' : readable_share gsh') ptrs (Hptrs : Zlength ptrs = 9) i (Hi : 0 <= i < 3),
semax (initialized_list [_i; _i__1; _q1; _i__2; _i__3; _t'1] (func_tycontext f_main Vprog Gprog))
  (PROP ( )
   LOCAL (temp _i__3 (vint i); temp _q1 q; temp _t'1 q; gvar _results results; gvar _thread_locks locks;
   gvar _q0 q0)
   SEP (field_at gsh' (tptr tqueue_t) [] q q0;
   fold_right sepcon emp
     (sublist 0 i (map (fun sh : Share.t => data_at sh (tptr tqueue_t) q q0) (map snd (rev gshs1))));
   data_at gsh' (tarray (tptr (Tstruct _lock_t noattr)) 3) flocks locks;
   fold_right sepcon emp
     (sublist 0 i
        (map (fun sh : Share.t => data_at_ sh (tarray (tptr (Tstruct _lock_t noattr)) 3) locks)
           (map snd (rev gshs1))));
   fold_right sepcon emp
     (sublist i 3 (map (fun x : Z * val => lock_inv sh1 (snd x) (f_lock x)) (combine (upto 3) flocks)));
   fold_right sepcon emp (sublist i 3 (map (fun x : val => malloc_token Tsh (sizeof tlock) x) flocks));
   lqueue lsh' tint (is_int I32 Signed) q lock sh1 sh2
     (map (fun x : val * Z => QAdd (fst x) (vint (snd x))) (combine ptrs (upto (Z.to_nat 9))));
   EX vals : list (list (val * int)),
   !! (Zlength vals = i /\ Forall (fun l : list (val * int) => Zlength l = 3) vals) &&
   (fold_right sepcon emp
      (map
         (fun x : Share.t * list (val * int) =>
          let
          '(sh, vals0) := x in
           lqueue sh tint (is_int I32 Signed) q lock sh1 sh2
             (map (fun x0 : val * int => let '(p, i0) := x0 in QRem p (Vint i0)) vals0))
         (combine (sublist 0 i (map snd (rev lshs1))) vals)) *
    fold_right sepcon emp
      (map
         (fun x : Z =>
          field_at Ews (tarray (tarray tint 3) 3) [ArraySubsc x] (map Vint (map snd (Znth x vals []))) results)
         (upto (Z.to_nat i))))))
  (Ssequence
     (Sset _l__1
        (Ederef
           (Ebinop Oadd (Evar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 3))
              (Etempvar _i__3 tint) (tptr (tptr (Tstruct _lock_t noattr)))) (tptr (Tstruct _lock_t noattr))))
     (Ssequence
        (Scall None (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
           [Etempvar _l__1 (tptr (Tstruct _lock_t noattr))])
        (Ssequence
           (Scall None (Evar _freelock2 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
              [Etempvar _l__1 (tptr (Tstruct _lock_t noattr))])
           (Scall None (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
              [Etempvar _l__1 (tptr (Tstruct _lock_t noattr))]))))
  (normal_ret_assert
     (PROP (0 <= i + 1 <= 3)
      LOCAL (temp _i__3 (vint i); temp _q1 q; temp _t'1 q; gvar _results results; gvar _thread_locks locks;
      gvar _q0 q0)
      SEP (field_at gsh' (tptr tqueue_t) [] q q0;
      fold_right sepcon emp
        (sublist 0 (i + 1) (map (fun sh : Share.t => data_at sh (tptr tqueue_t) q q0) (map snd (rev gshs1))));
      data_at gsh' (tarray (tptr (Tstruct _lock_t noattr)) 3) flocks locks;
      fold_right sepcon emp
        (sublist 0 (i + 1)
           (map (fun sh : Share.t => data_at_ sh (tarray (tptr (Tstruct _lock_t noattr)) 3) locks)
              (map snd (rev gshs1))));
      fold_right sepcon emp
        (sublist (i + 1) 3 (map (fun x : Z * val => lock_inv sh1 (snd x) (f_lock x)) (combine (upto 3) flocks)));
      fold_right sepcon emp (sublist (i + 1) 3 (map (fun x : val => malloc_token Tsh (sizeof tlock) x) flocks));
      lqueue lsh' tint (is_int I32 Signed) q lock sh1 sh2
        (map (fun x : val * Z => QAdd (fst x) (vint (snd x))) (combine ptrs (upto (Z.to_nat 9))));
      EX vals : list (list (val * int)),
      !! (Zlength vals = i + 1 /\ Forall (fun l : list (val * int) => Zlength l = 3) vals) &&
      (fold_right sepcon emp
         (map
            (fun x : Share.t * list (val * int) =>
             let
             '(sh, vals0) := x in
              lqueue sh tint (is_int I32 Signed) q lock sh1 sh2
                (map (fun x0 : val * int => let '(p, i0) := x0 in QRem p (Vint i0)) vals0))
            (combine (sublist 0 (i + 1) (map snd (rev lshs1))) vals)) *
       fold_right sepcon emp
         (map
            (fun x : Z =>
             field_at Ews (tarray (tarray tint 3) 3) [ArraySubsc x] (map Vint (map snd (Znth x vals []))) results)
            (upto (Z.to_nat (i + 1)))))))).
Proof.
  intros.
  Intros vals.
  simpl initialized_list; unfold func_tycontext, make_tycontext.
  forward.
  { entailer!.
    apply Forall_Znth; [omega|].
    eapply Forall_impl; [|apply Hflocks]; auto. }
  forward_call (Znth i flocks Vundef, sh1, f_lock (i, Znth i flocks Vundef)).
  { assert (Zlength (map (fun x => lock_inv sh1 (snd x) (f_lock x)) (combine (upto 3) flocks)) = 3).
    { rewrite Zlength_map, Zlength_combine, Zlength_upto, Z.min_l; simpl; omega. }
    assert (length (upto 3) = length flocks) by (rewrite upto_length; rewrite Zlength_correct in *; Omega0).
    erewrite sublist_split with (lo := i), <- Znth_cons_sublist; try omega.
    rewrite Znth_map', <- Znth_map', combine_snd; auto.
    instantiate (1 := (3, Vundef)); simpl.
    rewrite Znth_combine, Znth_upto; simpl; auto; [cancel | omega]. }
  forward_call (Znth i flocks Vundef, Tsh, sh2, |>f_lock_inv (snd (Znth (2 - i) lshs1 (Tsh, Tsh)))
    (snd (Znth (2 - i) gshs1 (Ews, Ews))) sh1 sh2 q0 q lock i locks (Znth i flocks Vundef) results,
    |>f_lock (i, Znth i flocks Vundef)).
  { simpl; lock_props.
    - apply later_positive; unfold f_lock; apply f_inv_positive.
      exploit (Hgshs1 (2 - i)); [omega|].
      simpl; destruct (Znth (2 - i) gshs1 (Ews, Ews)); intros (? & ? & ?); auto.
    - unfold rec_inv, f_lock, f_lock_pred.
      rewrite selflock_eq at 1.
      rewrite later_sepcon; f_equal.
      apply lock_inv_later_eq.
    - unfold f_lock at 2; unfold f_lock_pred; rewrite selflock_eq.
      erewrite <- (lock_inv_share_join _ _ Tsh); try apply Hsh; auto.
      rewrite !sepcon_assoc; apply sepcon_derives; [apply lock_inv_later|].
      unfold f_lock at 2; unfold f_lock_pred; simpl snd; cancel. }
  forward_call (Znth i flocks Vundef, sizeof tlock).
  { rewrite data_at__memory_block.
    erewrite sublist_split with (lo := i), <- Znth_cons_sublist; try rewrite Zlength_map; try omega.
    rewrite Znth_map'.
    instantiate (1 := Vundef); simpl; Intros; cancel. }
  Intros p1 p2 p3 i1 i2 i3.
  Exists (vals ++ [[(p1, i1); (p2, i2); (p3, i3)]]); rewrite Zlength_app.
  entailer!.
  { rewrite Forall_app; split; auto. }
  erewrite sublist_split with (mid := Zlength vals)(hi := Zlength vals + 1), sublist_len_1;
    rewrite ?Zlength_map, ?Zlength_rev; try omega.
  rewrite 2Znth_map', Znth_rev; [|omega].
  rewrite Hglen1, sepcon_app; instantiate (1 := (Ews, Ews)).
  erewrite sublist_split with (mid := Zlength vals)(hi := Zlength vals + 1), sublist_len_1;
    rewrite ?Zlength_map, ?Zlength_rev; try omega.
  rewrite 2Znth_map', Znth_rev; [|omega].
  rewrite Hglen1, sepcon_app; instantiate (1 := (Ews, Ews)).
  erewrite sublist_split with (mid := Zlength vals)(hi := Zlength vals + 1), sublist_len_1;
    rewrite ?Zlength_map, ?Zlength_rev; try omega.
  rewrite Znth_map', Znth_rev; [|omega].
  rewrite Hlenl1, combine_app, map_app, sepcon_app.
  instantiate (1 := (Tsh, Tsh)).
  rewrite Z2Nat.inj_add, upto_app; try omega.
  change (upto (Z.to_nat 1)) with [0]; simpl.
  rewrite Z2Nat.id, map_app, sepcon_app, Z.add_0_r; [|omega].
  simpl; replace (3 - Zlength vals - 1) with (2 - Zlength vals) by (clear; abstract omega).
  rewrite app_Znth2, Zminus_diag; [simpl | clear; omega].
  rewrite <- lock_struct_array; cancel.
  apply sepcon_derives; [apply derives_refl|].
  apply derives_refl'; f_equal.
  rewrite Zlength_correct, Nat2Z.id; apply map_ext_in; intros.
  rewrite app_Znth1; auto.
  rewrite In_upto in H; rewrite Zlength_correct; clear - H; omega.
  { apply Nat2Z.inj; rewrite <- !Zlength_correct.
    rewrite Zlength_sublist; try rewrite Zlength_map, Zlength_rev; abstract omega. }
Qed.

Transparent upto.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  name q0 _q0; name locks _thread_locks; name results _results.
  start_function.
  exploit (split_readable_share Tsh); auto; intros (sh1 & sh2 & ? & ? & Hsh).
  rewrite <- !seq_assoc; eapply semax_seq'; [forward_call_id1_wow' (q_new_args tint (tc_val tint), sh1, sh2) |
    after_forward_call].
  Intro x; destruct x as (q, lock).
  simpl; forward.
  rewrite <- seq_assoc.
  exploit (split_shares 3 Ews); auto; intros (gshs1 & Hglen1 & Hgshs1).
  exploit (split_shares 3 Tsh); auto; intros (lshs1 & Hlenl1 & Hlshs1).
  set (f_lock := fun x => f_lock_pred (snd (Znth (2 - fst x) lshs1 (Tsh, Tsh)))
    (snd (Znth (2 - fst x) gshs1 (Ews, Ews))) sh2 sh1 sh2 q0 q lock (fst x) locks (snd x) results).
  rewrite lqueue_isptr; Intros.
  rewrite sem_cast_neutral_ptr; auto; simpl in *.
  forward_for_simple_bound 3 (EX i : Z,
    PROP ()
    LOCAL (temp _t'1 q; gvar _results results; gvar _thread_locks locks; gvar _q0 q0)
    SEP (lqueue Tsh tint (is_int I32 Signed) q lock sh1 sh2 [];
         data_at_ Ews (tarray (tarray tint 3) 3) results; field_at Ews (tptr tqueue_t) [] q q0;
         EX flocks : list val, (!!(Zlength flocks = i /\ Forall isptr flocks) &&
           (data_at Ews (tarray (tptr (Tstruct _lock_t noattr)) 3) (flocks ++ repeat Vundef (Z.to_nat (3 - i))) locks *
            fold_right sepcon emp (map (fun x => lock_inv Tsh (snd x) (f_lock x)) (combine (upto (Z.to_nat i)) flocks)) *
            fold_right sepcon emp (map (fun x => malloc_token Tsh (sizeof tlock) x) flocks))))).
  { Exists ([] : list val); entailer!.
    unfold data_at_, field_at_; simpl; cancel. }
  { forward_call (sizeof tlock).
    { admit. (* lock size broken *) }
    { simpl; computable. }
    Intros l flocks.
    rewrite malloc_compat; auto; Intros.
    forward.
    rewrite sem_cast_neutral_ptr; auto.
    forward_call (l, Tsh, f_lock (i, l)).
    { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
    { rewrite memory_block_data_at_; auto; simpl; cancel. }
    Exists (flocks ++ [l]); rewrite Zlength_app, Zlength_cons, Zlength_nil; entailer!.
    { rewrite Forall_app; split; auto. }
    replace (Z.to_nat (3 - Zlength flocks)) with (S (Z.to_nat (3 - (Zlength flocks + 1)))); simpl.
    rewrite upd_Znth_app2, Zminus_diag, upd_Znth0, sublist_1_cons, sublist_same; auto; try rewrite Zlength_cons;
      try solve [rewrite !Zlength_correct; omega].
    rewrite Z2Nat.inj_add, upto_app, combine_app, !map_app, !sepcon_app; simpl; try omega.
    rewrite Zlength_correct, !Z2Nat.id, Nat2Z.id, Z.add_0_r, <- app_assoc; [cancel | omega].
    { rewrite upto_length, Zlength_correct, Nat2Z.id; auto. }
    { rewrite <- Z2Nat.inj_succ; f_equal; omega. }
    { exists 2; auto. } }
  Intros flocks.
  rewrite Zminus_diag, app_nil_r, <- seq_assoc.
  erewrite add_andp with (P := data_at_ _ _ _); [|apply data_at__local_facts]; Intros.
  forward_for_simple_bound 3 (EX i : Z,
    PROP ()
    LOCAL (temp _t'1 q; gvar _results results; gvar _thread_locks locks; gvar _q0 q0)
    SEP (lqueue (fst (Znth (3 - i) lshs1 (Tsh, Tsh))) tint (is_int I32 Signed) q lock sh1 sh2 [];
         data_at_ Ews (tarray (tarray tint 3) (3 - i))
           (offset_val (nested_field_offset (tarray (tarray tint 3) 3) [ArraySubsc i]) results);
         field_at (fst (Znth (3 - i) gshs1 (Ews, Ews))) (tptr tqueue_t) [] q q0;
         data_at (fst (Znth (3 - i) gshs1 (Ews, Ews))) (tarray (tptr (Tstruct _lock_t noattr)) 3) flocks locks;
         fold_right sepcon emp (map (fun x => lock_inv sh1 (snd x) (f_lock x)) (sublist 0 i (combine (upto 3) flocks)));
         fold_right sepcon emp (map (fun x => lock_inv Tsh (snd x) (f_lock x)) (sublist i 3 (combine (upto 3) flocks)));
         fold_right sepcon emp (map (fun x => malloc_token Tsh (sizeof tlock) x) flocks))).
  { rewrite sublist_nil, sublist_same; auto; [|rewrite Zlength_combine, Zlength_upto, Z.min_l; simpl; omega].
    entailer!.
    rewrite !Znth_overflow; try omega; simpl; cancel. }
  { apply main_loop1; auto. }
  rewrite Zminus_diag.
  rewrite sublist_nil, sublist_same; auto; [|rewrite Zlength_combine, Zlength_upto, Z.min_l; simpl; omega].
  set (lsh' := fst (Znth 0 lshs1 (Tsh, Tsh))).
  set (gsh' := fst (Znth 0 gshs1 (Ews, Ews))).
  assert (readable_share gsh').
  { exploit (Hgshs1 0); [computable|].
    subst gsh'; destruct (Znth 0 gshs1 (Ews, Ews)) eqn: Hg1; setoid_rewrite Hg1; intros (? & ?); auto. }
  forward.
  rewrite <- seq_assoc.
  forward_for_simple_bound 9 (EX i : Z,
    PROP ()
    LOCAL (temp _q1 q; temp _t'1 q; gvar _results results; gvar _thread_locks locks; gvar _q0 q0)
    SEP (EX ptrs : list val, !!(Zlength ptrs = i) && lqueue lsh' tint (is_int I32 Signed) q lock sh1 sh2
          (map (fun x => QAdd (fst x) (vint (snd x))) (combine ptrs (upto (Z.to_nat i))));
         field_at gsh' (tptr tqueue_t) [] q q0;
         data_at gsh' (tarray (tptr (Tstruct _lock_t noattr)) 3) flocks locks;
         fold_right sepcon emp (map (fun x => lock_inv sh1 (snd x) (f_lock x)) (combine (upto 3) flocks));
         fold_right sepcon emp (map (fun x => malloc_token Tsh (sizeof tlock) x) flocks))).
  { Exists ([] : list val); entailer!.
    unfold data_at_, field_at_, field_at, at_offset.
    rewrite data_at_rec_eq; unfold unfold_reptype, default_val; simpl.
    rewrite array_pred_len_0; [entailer! | auto]. }
  { forward_call (sizeof tint).
    { simpl; computable. }
    Intros d ptrs.
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    forward.
    rewrite -> semax_seq_skip; eapply semax_seq'; [forward_call_id00_wow' (lsh', q_add_args tint (tc_val tint)
      (map (fun x => QAdd (fst x) (vint (snd x))) (combine ptrs (upto (Z.to_nat i)))) (vint i),
      q, lock, d, sh1, sh2) | after_forward_call].
(*    forward_call (lsh', existT (fun t => ((reptype t -> Prop) * hist (reptype t) * reptype t)%type) tint
      (is_int I32 Signed, map (fun x => QAdd (fst x) (vint (snd x))) (combine ptrs (upto (Z.to_nat i))), vint i),
      q, lock, d, sh1, sh2).*)
    { change_compspecs CompSpecs.
      simpl; cancel. }
    { exploit (Hlshs1 0); [computable|].
      subst lsh'; destruct (Znth 0 lshs1 (Tsh, Tsh)) eqn: Hg1; intros (? & ?); auto. }
    Exists (ptrs ++ [d]); rewrite Zlength_app, Zlength_cons, Zlength_nil; entailer!.
    rewrite Z2Nat.inj_add, upto_app, combine_app, map_app; try omega; simpl.
    rewrite Z2Nat.id, Z.add_0_r, Zlength_correct, Nat2Z.id; [cancel | omega].
    simple apply derives_refl.
    { rewrite upto_length, Zlength_correct, Nat2Z.id; auto. }
    { exists 2; auto. } }
  Intros ptrs.
  rewrite <- seq_assoc.
  forward_for_simple_bound 3 (EX i : Z,
    PROP ()
    LOCAL (temp _q1 q; temp _t'1 q; gvar _results results; gvar _thread_locks locks; gvar _q0 q0)
    SEP (field_at gsh' (tptr tqueue_t) [] q q0;
         fold_right sepcon emp (sublist 0 i (map (fun sh => data_at sh (tptr tqueue_t) q q0) (map snd (rev gshs1))));
         data_at gsh' (tarray (tptr (Tstruct _lock_t noattr)) 3) flocks locks;
         fold_right sepcon emp (sublist 0 i (map (fun sh => data_at_ sh (tarray (tptr (Tstruct _lock_t noattr)) 3) locks) (map snd (rev gshs1))));
         fold_right sepcon emp (sublist i 3 (map (fun x => lock_inv sh1 (snd x) (f_lock x)) (combine (upto 3) flocks)));
         fold_right sepcon emp (sublist i 3 (map (fun x => malloc_token Tsh (sizeof tlock) x) flocks));
         lqueue lsh' tint (is_int I32 Signed) q lock sh1 sh2
          (map (fun x => QAdd (fst x) (vint (snd x))) (combine ptrs (upto (Z.to_nat 9))));
         EX vals : list (list (val * int)), !!(Zlength vals = i /\ Forall (fun l => Zlength l = 3) vals) &&
         (fold_right sepcon emp (map (fun x => let '(sh, vals) := x in
            lqueue sh tint (is_int I32 Signed) q lock sh1 sh2
              (map (fun x => let '(p, i) := x in QRem p (Vint i)) vals))
            (combine (sublist 0 i (map snd (rev lshs1))) vals)) *
          fold_right sepcon emp (map (fun x => field_at Ews (tarray (tarray tint 3) 3) [ArraySubsc x]
            (map Vint (map snd (Znth x vals []))) results) (upto (Z.to_nat i)))))).
  { rewrite !sublist_nil; rewrite !sublist_same; auto;
      try rewrite Zlength_map; try rewrite Zlength_combine, Zlength_upto, Z.min_l; auto; [|simpl; omega].
    Exists ([] : list (list (val * int))); entailer!. }
  { simple apply main_loop2 with (q2 := q)(locks0 := locks)(q1 := q0)(gshs2 := gshs1)
      (lshs2 := lshs1)(sh3 := sh1)(sh4 := sh2)(lock0 := lock); auto. }
  Intros vals.
  rewrite !sublist_nil, !sublist_same; auto; rewrite ?Zlength_map, ?Zlength_rev; auto.
  rewrite !map_rev, !sepcon_rev.
  change (field_at gsh' (tptr tqueue_t) [] q q0) with (data_at gsh' (tptr tqueue_t) q q0).
  gather_SEP 0 1; subst gsh'; rewrite data_at_shares_join; [|rewrite Hglen1; auto].
  gather_SEP 1 2; replace_SEP 0 (data_at Ews (tarray (tptr (Tstruct _lock_t noattr)) 3) flocks locks).
  { go_lowerx.
    rewrite sepcon_emp; apply data_at__shares_join; rewrite Hglen1; auto. }
  gather_SEP 4 5; replace_SEP 0 (EX h' : hist (reptype tint),
    !!(interleave (map (fun x => QAdd (fst x) (vint (snd x))) (combine ptrs (upto (Z.to_nat 9))) ::
                   map (fun vals => map (fun x => let '(p, i) := x in QRem p (Vint i)) vals) (rev vals)) h') &&
    lqueue Tsh tint (is_int I32 Signed) q lock sh1 sh2 h').
  { assert (length lshs1 = length (map (fun vals => map (fun x => let '(p, i) := x in
      QRem p (Vint i)) vals) (rev vals))).
    { rewrite !map_length, rev_length; rewrite Zlength_correct in *; abstract omega. }
    go_lowerx; eapply derives_trans; [|apply lqueue_shares_join; [eauto | rewrite Hlenl1; eauto]].
    subst lsh'; cancel.
    rewrite combine_map_snd, map_map.
    rewrite <- sepcon_rev, <- map_rev, rev_combine, rev_involutive.
    erewrite map_ext; [apply derives_refl|].
    destruct a; auto.
    { rewrite rev_length, map_length, rev_length in *; auto. } }
  Intros h'.
  repeat (destruct ptrs; [rewrite Zlength_nil in *; discriminate | rewrite Zlength_cons in *]).
  destruct ptrs; [|rewrite Zlength_cons, Zlength_correct in *; omega].
  repeat (destruct vals; [rewrite Zlength_nil in *; discriminate | rewrite Zlength_cons in *]).
  destruct vals; [|rewrite Zlength_cons, Zlength_correct in *; omega].
  repeat match goal with H : Forall _ (_ :: _) |- _ => inv H end.
  repeat (destruct l as [|(?, ?)]; [rewrite Zlength_nil in *; discriminate | rewrite Zlength_cons in *]).
  destruct l; [|rewrite Zlength_cons, Zlength_correct in *; omega].
  repeat (destruct l0 as [|(?, ?)]; [rewrite Zlength_nil in *; discriminate | rewrite Zlength_cons in *]).
  destruct l0; [|rewrite Zlength_cons, Zlength_correct in *; omega].
  repeat (destruct l1 as [|(?, ?)]; [rewrite Zlength_nil in *; discriminate | rewrite Zlength_cons in *]).
  destruct l1; [|rewrite Zlength_cons, Zlength_correct in *; omega].
  simpl in *.
  rewrite lqueue_feasible; Intros.
  assert (consistent h' [] [] /\ interleave [[Vint i; Vint i0; Vint i1]; [Vint i2; Vint i3; Vint i4];
    [Vint i5; Vint i6; Vint i7]] [vint 0; vint 1; vint 2; vint 3; vint 4; vint 5; vint 6; vint 7; vint 8])
    as (? & ?).
  { match goal with H : feasible h' |- _ => destruct H as (b & Hcon) end.
    exploit (@add_first (reptype tint)); try eassumption.
    clear - Hcon.
    intros (h1 & h2 & Hadds & Hrems & Hcon'); simpl in *.
    rewrite interleave_remove_nil in Hrems.
    repeat setoid_rewrite interleave_remove_nil' with (ls1 := [_]) in Hadds.
    rewrite app_nil_r, interleave_single in Hadds.
    exploit (consistent_adds h1); subst; auto.
    intros (l & Hl & Hh1).
    repeat (destruct l as [|(?, ?)]; [discriminate|]); destruct l; [|discriminate].
    simpl in Hl; inv Hl.
    rewrite Hh1 in Hcon'.
    exploit (consistent_rems h2).
    { rewrite forallb_forall; intros ? Hin.
      rewrite interleave_In in Hin; [|eassumption].
      simpl in Hin; destruct Hin as (? & [? | [? | [? | ?]]] & Hin); try contradiction; subst;
        destruct Hin as [? | [? | [? | ?]]]; try contradiction; subst; auto. }
    { eassumption. }
    intros (? & ? & ?); subst.
    pose proof (Zlength_interleave _ _ Hrems) as Hlen.
    rewrite Zlength_map in Hlen; simpl in Hlen.
    assert (Zlength (x ++ b) = 9) by (rewrite <- H; Omega0).
    destruct b; [|rewrite Zlength_app, Zlength_cons in *; rewrite !Zlength_correct in *; omega].
    split; auto.
    rewrite app_nil_r in *; subst; simpl in *.
    eapply interleave_combine.
    { instantiate (1 := [[_; _; _]; [_; _; _]; [_; _; _]]).
      repeat (constructor; [simpl; reflexivity|]); auto. }
    { instantiate (1 := [_; _; _; _; _; _; _; _; _]); simpl; auto. }
    apply (interleave_map_inj (fun x => let '(p, v) := x in @QRem (reptype tint) p v)); simpl.
    { intros (?, ?) (?, ?) Heq; inv Heq; auto. }
    setoid_rewrite interleave_reorder with (ls1 := [_]) in Hrems.
    setoid_rewrite interleave_reorder with (ls1 := [_; _]) in Hrems.
    apply Hrems. }
  eapply semax_seq'; [forward_call_id00_wow' (q_rem_args tint (is_int I32 Signed) h', q, lock, sh1, sh2) |
    after_forward_call].
  forward.
Admitted.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_free.
repeat semax_func_cons_ext.
{ clear H. rewrite exp_unfold. Intros p.
  rewrite <- insert_local.
  rewrite lower_andp.
  apply derives_extract_prop; intro. hnf in H. rewrite retval_ext_rval in H.
  subst p.
  renormalize. entailer!. }
{ destruct x as (((?, ?), ?), ?).
  clear H.
  rewrite exp_unfold; Intros p.
  rewrite exp_unfold; Intros q.
  rewrite <- insert_local.
  rewrite lower_andp.
  apply derives_extract_prop; intro. hnf in H. rewrite retval_ext_rval in H.
  subst p.
  renormalize.
  rewrite lqueue_isptr; entailer!. }
{ destruct x as (((((?, (?, (?, ?))), ?), ?), ?), ?).
  clear H.
  rewrite exp_unfold; Intros p.
  rewrite exp_unfold; Intros q.
  rewrite <- insert_local.
  rewrite lower_andp.
  apply derives_extract_prop; intro. hnf in H. rewrite retval_ext_rval in H.
  subst p.
  renormalize. rewrite data_at_isptr; entailer!. }
semax_func_cons body_f.
semax_func_cons body_main.
Qed.

(* Linking? *)