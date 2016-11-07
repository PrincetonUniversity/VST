Require Import progs.conc_queue_specs.
Require Import progs.conclib.
Require Import progs.queue_ex.
Require Import floyd.library.
Require Import floyd.sublist.

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
Definition wait_spec := DECLARE _waitcond (wait2_spec _).
Definition signal_spec := DECLARE _signalcond (signal_spec _).

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH n:Z
   PRE [ _n OF tuint ]
       PROP (0 <= n <= Int.max_unsigned)
       LOCAL (temp _n (Vint (Int.repr n)))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (malloc_token Tsh n p * memory_block Tsh n p).

Definition q_new_spec := DECLARE _q_new q_new_spec'.
Definition q_del_spec := DECLARE _q_del q_del_spec'.
Definition q_add_spec := DECLARE _q_add q_add_spec'.
Definition q_remove_spec := DECLARE _q_remove q_remove_spec'.
Definition q_tryremove_spec := DECLARE _q_tryremove q_tryremove_spec'.

Notation f_lock_inv lsh gsh gsh1 gsh2 p' p lock t locksp lockt resultsp :=
  (EX p1 : val, EX p2 : val, EX p3 : val, EX i1 : int, EX i2 : int, EX i3 : int,
     data_at gsh (tptr tqueue_t) p p' *
     lqueue lsh tint (tc_val tint) p lock gsh1 gsh2
       [@QRem tint p1 (Vint i1); @QRem tint p2 (Vint i2); @QRem tint p3 (Vint i3)] *
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

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; release2_spec;
  makelock_spec; freelock_spec; freelock2_spec; spawn_spec; makecond_spec; freecond_spec; wait_spec; signal_spec;
  surely_malloc_spec; q_new_spec; q_del_spec; q_add_spec; q_remove_spec; q_tryremove_spec; f_spec; main_spec]).

Lemma f_inv_precise : forall lsh gsh tsh gsh1 gsh2 p' p lock t locksp lockt resultsp,
  precise (f_lock_pred lsh gsh tsh gsh1 gsh2 p' p lock t locksp lockt resultsp).
Proof.
  intros; unfold f_lock_pred.
  apply selflock_precise.
  apply derives_precise' with (Q := data_at gsh (tptr tqueue_t) p p' *
    (EX h : hist tint, lqueue lsh tint (tc_val tint) p lock gsh1 gsh2 h) *
    data_at gsh (tarray (tptr tlock) 3) (upd_Znth t (repeat Vundef 3) lockt) locksp *
    field_at_ Ews (tarray (tarray tint 3) 3) [ArraySubsc t] resultsp).
  - Intros p1 p2 p3 i1 i2 i3; cancel.
    Exists [@QRem tint p1 (Vint i1); @QRem tint p2 (Vint i2); @QRem tint p3 (Vint i3)]; auto.
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
           (lqueue lsh tint (tc_val tint) p lock gsh1 gsh2 (map (fun x => @QRem tint (fst x) (Vint (snd x))) vals) *
            field_at Ews (tarray (tarray tint 3) 3) [ArraySubsc t]
              (map (fun x => Vint (snd x)) vals ++ repeat Vundef (Z.to_nat (3 - i))) resultsp))).
  { Exists ([] : list (val * int)); repeat entailer!. }
  { Intros vals.
    forward_call (lsh, existT (fun t => ((reptype t -> Prop) * hist t)%type) tint (tc_val tint,
      map (fun x => @QRem tint (fst x) (Vint (snd x))) vals), p, lock, gsh1, gsh2).
    Intros x; destruct x as (p1 & v1).
    simpl; forward.
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

Opaque upto.

(* This should probably be proved higher up, and used regularly. *)
Lemma data_at__eq : forall sh t p, data_at_ sh t p = data_at sh t (default_val t) p.
Proof.
  intros; unfold data_at_, data_at, field_at_; auto.
Qed.

Lemma combine_snd : forall {A B} (l : list A) (l' : list B), length l = length l' ->
  map snd (combine l l') = l'.
Proof.
  induction l; destruct l'; try discriminate; auto; intros.
  inv H; simpl; rewrite IHl; auto.
Qed.

Set Default Timeout 60.

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
     (offset_val (nested_field_offset (tarray tint 3) [ArraySubsc i]) results);
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
        (offset_val (nested_field_offset (tarray tint 3) [ArraySubsc (i + 1)]) results);
      field_at (fst (Znth (3 - (i + 1)) gshs1 (Ews, Ews))) (tptr tqueue_t) [] q q0;
      data_at (fst (Znth (3 - (i + 1)) gshs1 (Ews, Ews))) (tarray (tptr (Tstruct _lock_t noattr)) 3) flocks locks;
      fold_right sepcon emp
        (map (fun x : Z * val => lock_inv sh1 (snd x) (f_lock x)) (sublist 0 (i + 1) (combine (upto 3) flocks)));
      fold_right sepcon emp
        (map (fun x : Z * val => lock_inv Tsh (snd x) (f_lock x)) (sublist (i + 1) 3 (combine (upto 3) flocks)));
      fold_right sepcon emp (map (fun x : val => malloc_token Tsh (sizeof tlock) x) flocks)))).
Proof.
  intros.
  forward_call (sizeof tint).
  { simpl; cancel. }
  { simpl; computable. }
  Intro t.
  rewrite malloc_compat; auto; Intros.
  rewrite memory_block_data_at_; auto.
  forward.
  get_global_function'' _f; Intros.
  match goal with |-context[mk_funspec ?a ?b (rmaps.ConstType ?c) (fun _ => ?d) (fun _ => ?e) _ _] =>
    change (mk_funspec _ _ _ _ _ _ _) with (NDmk_funspec a b c d e) end.
  apply extract_exists_pre; intros f_.
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
  { Timeout 100 entailer!.
    { rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto.
      split; auto; split; [apply Forall_Znth; auto; omega|].
      specialize (Hlshs1 (2 - i)); exploit Hlshs1; [omega|].
      destruct (Znth (2 - i) lshs1 (Tsh, Tsh)).
      specialize (Hgshs1 (2 - i)); exploit Hgshs1; [omega|].
      destruct (Znth (2 - i) gshs1 (Ews, Ews)); tauto. }
    Exists _arg (fun x : (share * share * share * share * share * val * val * val * Z * val * val * val) =>
      let '(lsh, gsh, tsh, gsh1, gsh2, p', p, lock, t, locksp, lockt, resultsp) := x in
      [(_q0, p'); (_thread_locks, locksp); (_results, resultsp)]).
    rewrite !sepcon_assoc; apply sepcon_derives.
    { apply derives_refl'.
      f_equal; f_equal; extensionality; destruct x as (?, x); repeat destruct x as (x, ?); simpl; try reflexivity.
      rewrite !sepcon_emp; reflexivity. }
      specialize (Hgshs1 (2 - i)); exploit Hgshs1; [omega|].
      destruct (Znth (2 - i) gshs1 (Ews, Ews)) eqn: Hg1.
      replace (2 - i + 1) with (3 - i) by omega.
      intros (? & ? & Hglsh); rewrite <- (data_at_share_join _ _ _ _ _ _ Hglsh),
        <- (field_at_share_join _ _ _ _ _ _ _ Hglsh); auto.
    specialize (Hlshs1 (2 - i)); exploit Hlshs1; [omega|].
    destruct (Znth (2 - i) lshs1 (Tsh, Tsh)) eqn: Hl1.
    replace (2 - i + 1) with (3 - i) by omega.
    intros (? & ? & Hllsh); rewrite <- (lqueue_share_join tint _ s s0 (fst (Znth (3 - i) lshs1 (Tsh, Tsh))))
      with (h1 := [])(h2 := []); auto.
    erewrite sublist_split with (lo := i), <- Znth_cons_sublist;
      try rewrite Zlength_combine, Zlength_upto, Z.min_l; simpl; try omega.
    instantiate (1 := (0, Vundef)).
    rewrite <- Znth_map', combine_snd; [|rewrite upto_length; rewrite Zlength_correct in *; Omega0].
    rewrite <- (lock_inv_share_join sh1 sh2 Tsh); auto.
    unfold tarray at 1; erewrite data_at__eq, split2_data_at_Tarray with (n1 := 1); try apply eq_JMeq;
      try reflexivity; [| omega | rewrite sublist_same; auto].
    Timeout 100 cancel.
    rewrite (sepcon_comm _ (data_at t1 _ _ _)); rewrite !sepcon_assoc; apply sepcon_derives.
    { rewrite lock_struct_array; apply stronger_array_ext.
      { unfold unfold_reptype; simpl.
        rewrite upd_Znth_Zlength; Omega0. }
      intros; unfold unfold_reptype, default_val; simpl.
      destruct (eq_dec i0 i).
      - subst; rewrite upd_Znth_same; [apply stronger_refl | Omega0].
      - rewrite upd_Znth_diff; auto; try Omega0.
        rewrite Znth_repeat with (x := Vundef)(n0 := 3%nat); apply stronger_default_val. }
    rewrite <- !sepcon_assoc, (sepcon_comm (lqueue _ _ _ _ _ _ _ _)), !sepcon_assoc; apply sepcon_derives.
    { unfold field_at_, data_at, field_at, at_offset; entailer!.
      { eapply field_compatible_cons_Tarray; try eassumption; reflexivity. }
      rewrite data_at_rec_eq; simpl.
    unfold f_lock.
    Search Znth map.
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
Qed.*)
Admitted.*)

(*Lemma main_loop2 : forall {Espec : OracleKind} (q0 lvar0 : val) gsh1 gsh2 (Hgsh1 : readable_share gsh1) (Hgsh2 : readable_share gsh2)
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
   fold_right sepcon emp (skipn (Z.to_nat i) (map (ghost gsh1 tint (vint (-1))) ghosts));
   fold_right sepcon emp (map Interp (map f_lock (combine (upto 3) flocks)));
   EX glocks : list val,
   !! (Zlength glocks = i) &&
   (data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6) (flocks ++ glocks ++ repeat Vundef (Z.to_nat (3 - i)))
      lvar0 * fold_right sepcon emp (map Interp (map g_lock (combine (upto (Z.to_nat i)) glocks))))))
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
      fold_right sepcon emp (skipn (Z.to_nat (i + 1)) (map (ghost gsh1 tint (vint (-1))) ghosts));
      fold_right sepcon emp (map Interp (map f_lock (combine (upto 3) flocks)));
      EX glocks : list val,
      !! (Zlength glocks = i + 1) &&
      (data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6)
         (flocks ++ glocks ++ repeat Vundef (Z.to_nat (3 - (i + 1)))) lvar0 *
       fold_right sepcon emp (map Interp (map g_lock (combine (upto (Z.to_nat (i + 1))) glocks))))))).
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
        fold_right sepcon emp (skipn (Z.to_nat (i + 1)) (map (ghost gsh1 tint (vint (-1))) ghosts));
        fold_right sepcon emp (map Interp (map f_lock (combine (upto 3) flocks)));
        data_at Tsh (tarray (tptr (Tstruct _lock_t noattr)) 6) (flocks ++ (glocks ++ [l]) ++ repeat Vundef (Z.to_nat (3 - (i + 1)))) lvar0;
        fold_right sepcon emp (map Interp (map g_lock (combine (upto (Z.to_nat (i + 1))) (glocks ++ [l]))))]).
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
   fold_right sepcon emp
     (firstn (Z.to_nat i)
        (map (fun sh : Share.t => data_at sh (tptr tqueue_t) p q0) (map snd (rev gshs1 ++ rev gshs2))));
   lqueue (fst (Znth 0 lshs2 (lsh', lsh'))) gsh2 p ghosts lock;
   fold_right sepcon emp
     (firstn (Z.to_nat i)
        (map (fun sh : Share.t => lqueue sh gsh2 p ghosts lock) (map snd (rev lshs1 ++ rev lshs2))));
   EX ns : list Z,
   !! (Zlength ns = Zlength ghosts) &&
   fold_right sepcon emp
     (firstn (Z.to_nat i - 3) (map (fun x : Z * val => ghost gsh1 tint (vint (fst x)) (snd x)) (combine ns ghosts)));
   fold_right sepcon emp (skipn (Z.to_nat i) (map Interp (map f_lock (combine (upto 3) flocks))));
   fold_right sepcon emp (skipn (Z.to_nat i - 3) (map Interp (map g_lock (combine (upto 3) glocks))));
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
      fold_right sepcon emp
        (firstn (Z.to_nat (i + 1))
           (map (fun sh : Share.t => data_at sh (tptr tqueue_t) p q0) (map snd (rev gshs1 ++ rev gshs2))));
      lqueue (fst (Znth 0 lshs2 (lsh', lsh'))) gsh2 p ghosts lock;
      fold_right sepcon emp
        (firstn (Z.to_nat (i + 1))
           (map (fun sh : Share.t => lqueue sh gsh2 p ghosts lock) (map snd (rev lshs1 ++ rev lshs2))));
      EX ns : list Z,
      !! (Zlength ns = Zlength ghosts) &&
      fold_right sepcon emp
        (firstn (Z.to_nat (i + 1) - 3)
           (map (fun x : Z * val => ghost gsh1 tint (vint (fst x)) (snd x)) (combine ns ghosts)));
      fold_right sepcon emp (skipn (Z.to_nat (i + 1)) (map Interp (map f_lock (combine (upto 3) flocks))));
      fold_right sepcon emp (skipn (Z.to_nat (i + 1) - 3) (map Interp (map g_lock (combine (upto 3) glocks))));
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
Qed.*)

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  name q0 _q0; name locks _thread_locks; name results _results.
  start_function.
  exploit (split_readable_share Tsh); auto; intros (sh1 & sh2 & ? & ? & Hsh).
  forward_call (existT (fun t => reptype t -> Prop) tint (tc_val tint), sh1, sh2).
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
    { simpl; cancel. }
    { simpl; computable. }
    Intros l flocks.
    rewrite malloc_compat; auto; Intros.
    forward.
    rewrite sem_cast_neutral_ptr; auto.
    forward_call (l, Tsh, f_lock (i, l)).
    { apply prop_right; rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
    { rewrite memory_block_data_at_; auto; simpl; cancel. }
    Exists (flocks ++ [l]); rewrite Zlength_app, Zlength_cons, Zlength_nil, Forall_app; entailer!.
    replace (Z.to_nat (3 - Zlength flocks)) with (S (Z.to_nat (3 - (Zlength flocks + 1)))); simpl.
    rewrite upd_Znth_app2, Zminus_diag, upd_Znth0, sublist_1_cons, sublist_same; auto; try rewrite Zlength_cons;
      try solve [rewrite !Zlength_correct; omega].
    rewrite Z2Nat.inj_add, upto_app, combine_app, !map_app, !sepcon_app; simpl; try omega.
    rewrite Zlength_correct, !Z2Nat.id, Nat2Z.id, Z.add_0_r, <- app_assoc; [unfold fold_right; cancel | omega].
    { rewrite upto_length, Zlength_correct, Nat2Z.id; auto. }
    { rewrite <- Z2Nat.inj_succ; f_equal; omega. }
    { exists 2; auto. } }
  Intros flocks.
  rewrite Zminus_diag, app_nil_r, <- seq_assoc.
  forward_for_simple_bound 3 (EX i : Z,
    PROP ()
    LOCAL (temp _t'1 q; gvar _results results; gvar _thread_locks locks; gvar _q0 q0)
    SEP (lqueue (fst (Znth (3 - i) lshs1 (Tsh, Tsh))) tint (is_int I32 Signed) q lock sh1 sh2 [];
         data_at_ Ews (tarray (tarray tint 3) (3 - i))
           (offset_val (nested_field_offset (tarray tint 3) [ArraySubsc i]) results);
         field_at (fst (Znth (3 - i) gshs1 (Ews, Ews))) (tptr tqueue_t) [] q q0;
         data_at (fst (Znth (3 - i) gshs1 (Ews, Ews))) (tarray (tptr (Tstruct _lock_t noattr)) 3) flocks locks;
         fold_right sepcon emp (map (fun x => lock_inv sh1 (snd x) (f_lock x)) (sublist 0 i (combine (upto 3) flocks)));
         fold_right sepcon emp (map (fun x => lock_inv Tsh (snd x) (f_lock x)) (sublist i 3 (combine (upto 3) flocks)));
         fold_right sepcon emp (map (fun x => malloc_token Tsh (sizeof tlock) x) flocks))).
  { rewrite sublist_nil, sublist_same; auto; [|rewrite Zlength_combine, Zlength_upto, Z.min_l; simpl; omega].
    entailer!.
    rewrite !Znth_overflow; try omega; simpl; cancel. }
  { semax_subcommand Vprog Gprog f_main.
apply main_loop1; auto. }
  simpl; Intros flocks.
  rewrite <- seq_assoc.
  set (lsh' := fst (Znth 0 lshs1 (Tsh, Tsh))).
  set (gsh' := fst (Znth 0 gshs1 (Ews, Ews))).
  forward_for_simple_bound 3 (EX i : Z,
    PROP ()
    LOCAL (temp _t'1 q; lvar _tid (tarray tint 3) lvar0; gvar _results results; gvar _thread_locks locks;
           gvar _q0 q0)
    SEP (EX ptrs : list val, !!(Zlength ptrs = i) && lqueue lsh' tint (is_int I32 Signed) q lock sh1 sh2
          (map (fun x => QAdd (fst x) (vint (snd x))) (combine ptrs (upto i)));
         field_at gsh' (tptr tqueue_t) [] q q0;
         data_at sh1' (tarray (tptr (Tstruct _lock_t noattr)) 3) flocks locks;
         fold_right sepcon emp (map (fun x => lock_inv sh1 (snd x) (f_lock x)) (combine (upto 3) flocks))))).
  { go_lower; simpl.
    Exists ([] : list val); entailer!.
    do 2 (rewrite Znth_overflow with (i := 3); [simpl; cancel | abstract omega]). }
  { semax_subcommand Vprog Gprog f_main.
apply main_loop2; auto. }

  simpl; Intro glocks; Intros.
  rewrite <- seq_assoc.
  forward_for_simple_bound 6 (EX i : Z,
    PROP (Forall isptr flocks; Forall isptr glocks)
    LOCAL (temp _t'1 p; lvar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 6) lvar0; gvar _q0 q0)
    SEP (ghost_factory; data_at (fst (Znth 0 gshs2 (gsh', gsh'))) (tptr tqueue_t) p q0;
         fold_right sepcon emp (firstn (Z.to_nat i) (map (fun sh => data_at sh (tptr tqueue_t) p q0) (map snd (rev gshs1 ++ rev gshs2))));
         lqueue (fst (Znth 0 lshs2 (lsh', lsh'))) gsh2 p ghosts lock;
         fold_right sepcon emp (firstn (Z.to_nat i) (map (fun sh => lqueue sh gsh2 p ghosts lock) (map snd (rev lshs1 ++ rev lshs2))));
         EX ns : list Z, (!!(Zlength ns = Zlength ghosts) &&
           fold_right sepcon emp (firstn (Z.to_nat i - 3) (map (fun x => ghost gsh1 tint (vint (fst x)) (snd x)) (combine ns ghosts))));
         fold_right sepcon emp (skipn (Z.to_nat i) (map Interp (map f_lock (combine (upto 3) flocks))));
         fold_right sepcon emp (skipn (Z.to_nat i - 3) (map Interp (map g_lock (combine (upto 3) glocks))));
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
  { semax_subcommand Vprog Gprog f_main.
apply main_loop3; auto. }
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

(*
(* linking *)
Require Import progs.verif_conc_queue.

Lemma Gprog_sub : incl verif_conc_queue.Gprog Gprog.
Proof.
  unfold verif_conc_queue.Gprog, Gprog.
  repeat apply incl_same_head.
  do 3 apply incl_tl; repeat apply incl_same_head; auto.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

(* Use semax_func_mono here. *)
Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
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
*)