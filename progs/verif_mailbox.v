Require Import progs.conclib.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import progs.mailbox.

Set Bullet Behavior "Strict Subproofs".

(* up *)
Lemma sepcon_derives_prop : forall P Q R, P |-- !!R -> P * Q |-- !!R.
Proof.
  intros; eapply derives_trans; [apply saturate_aux20 with (Q' := True); eauto|].
  - entailer!.
  - apply prop_left; intros (? & ?); apply prop_right; auto.
Qed.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
(*Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makecond_spec := DECLARE _makecond (makecond_spec _).
Definition freecond_spec := DECLARE _freecond (freecond_spec _).
Definition wait_spec := DECLARE _waitcond (wait2_spec _).
Definition signal_spec := DECLARE _signalcond (signal_spec _).*)

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

Definition memset_spec :=
 DECLARE _memset
  WITH sh : share, t : type, p : val, c : Z, n : Z
  PRE [ _s OF tptr tvoid, _c OF tint, _n OF tuint ]
   PROP (writable_share sh; sizeof t = n; n <= Int.max_unsigned; 0 <= c <= two_p 8 - 1)
   LOCAL (temp _s p; temp _c (vint c); temp _n (vint n))
   SEP (data_at_ sh t p)
  POST [ tptr tvoid ]
   PROP ()
   LOCAL (temp ret_temp p)
   SEP (data_at sh (tarray tuchar n) (repeat (vint c) (Z.to_nat n)) p).

Definition N := 3.
Definition B := N + 2.

Definition tbuffer := Tstruct _buffer noattr.

(* There are two invisible invariants: the last buffer written, and the buffer being read by each reader. *)
(* I think this can't be done with just ghost variables, though, since the readers want to track the value
   that the writer can update, and vice versa. Maybe it's more like the session type model, with views
   of a shared state machine. *)
(* For each reader, there's a pair of currently-reading and most-recently-published. *)
(* States:
   If currently-reading = most-recently-published, then comm[r] is Empty.
   Otherwise, comm[r] is most-recently-published.
   Writer can change most-recently-published to anything (...?)
   Reader can change currently-reading to most-recently-published.
 *)
(* From the reader's perspective, bw can be silently replaced with anything (except br).
   From the writer's perspective, br can be silently replaced with bw. *)
Inductive ghost_el := G (r : Z) (br : Z) (bw : Z) | R (r : Z) (br : Z) | W (brs : list Z) (bw : Z).
Definition consistent1 m n :=
  match m with
  | G r br bw => match n with
                | R r' br' => r = r' /\ br = br'
                | W brs' bw' => Zlength brs' = N /\ bw' = bw /\ (Znth r brs' (-2) = br \/ br = bw)
                | G r' br' bw' => (*bw' = bw /\ r <> r'*) False
                end
  | R r br => match n with
              | G r' br' bw => r = r' /\ br = br'
              | W brs bw => Zlength brs = N /\ (Znth r brs (-2) = br \/ br = bw)
              | _ => False
              end
  | W brs' bw' => Zlength brs' = N /\ match n with
                | G r br bw => bw' = bw /\ (Znth r brs' (-2) = br \/ br = bw)
                | R r br => Znth r brs' (-2) = br \/ br = bw'
                | _ => False
                end
  end.
Fixpoint consistent l :=
  match l with
  | [] => True
  | a :: rest => Forall (consistent1 a) rest /\ consistent rest
  end.
Definition view_shift m n := forall p, consistent (m ++ p) -> consistent (n ++ p).

Parameter ghost : list ghost_el -> mpred.
Axiom ghost_shift : forall Espec D P Q R C P' l l',
  view_shift l l' ->
  semax(Espec := Espec) D (PROPx P (LOCALx Q (SEPx (ghost l' :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost l :: R)))) C P'.
Axiom ghost_consistent : forall l, ghost l |-- !!consistent l.
Axiom ghost_join : forall l l', ghost l * ghost l' = ghost (l ++ l').

Definition comm_inv comm r :=
  EX br : Z, EX bw : Z, !!(0 <= bw) && (ghost [G r br bw] *
    field_at Ews (tarray tint N) [ArraySubsc r] (vint (if eq_dec br bw then -1 else bw)) comm).

(* How can we generalize this? *)
Definition atomic_exchange_spec :=
 DECLARE _simulate_atomic_exchange
  WITH sh1 : share, sh2 : share, r : Z, v : Z, locks : val, l : val, comm : val, writer : bool,
    g : ghost_el, brs : list Z, b : Z
  PRE [ _r OF tint, _v OF tint ]
   PROP (readable_share sh1; readable_share sh2; 0 <= r < N; repable_signed v;
         if writer then 0 <= v /\ g = W brs b /\ b <> v /\ Forall (fun x => x <> v) brs
         else v = -1 /\ g = R r b)
   LOCAL (temp _r (vint r); temp _v (vint v); gvar _lock locks; gvar _comm comm)
   SEP (field_at sh1 (tarray (tptr tlock) N) [ArraySubsc r] l locks;
        lock_inv sh2 l (comm_inv comm r); ghost [g])
  POST [ tint ]
   EX g' : ghost_el, EX v' : Z,
   PROP (if writer then g' = W (if eq_dec v' (-1) then upd_Znth r brs b else brs) v
         else g' = R r (if eq_dec v' (-1) then b else v'))
   LOCAL (temp ret_temp (vint v'))
   SEP (field_at sh1 (tarray (tptr tlock) N) [ArraySubsc r] l locks;
        lock_inv sh2 l (comm_inv comm r); ghost [g']).

Definition initialize_channels_spec :=
 DECLARE _initialize_channels
  WITH gsh1 : share, comm : val, lock : val, bufs : val, reading : val, last_given : val
  PRE [ ]
   PROP ()
   LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs bufs)
   SEP (data_at_ Ews (tarray tint N) comm; data_at_ Ews (tarray (tptr tlock) N) lock;
        data_at_ Ews (tarray tbuffer B) bufs)
  POST [ tvoid ]
   EX locks : list val,
   PROP ()
   LOCAL ()
   SEP (data_at Ews (tarray tint N) (repeat (vint 0) (Z.to_nat N)) comm;
        data_at Ews (tarray (tptr tlock) N) locks lock;
        fold_right sepcon emp (map (fun r =>
          lock_inv Tsh (Znth r locks Vundef) (comm_inv comm r(* gsh1 reading last_given*))) (upto (Z.to_nat N)));
        data_at Ews (tarray tbuffer B) (vint 0 :: repeat Vundef (Z.to_nat (B - 1))) bufs).

Definition initialize_reader_spec :=
 DECLARE _initialize_reader
  WITH r : Z, reading : val, last_read : val
  PRE [ _r OF tint ]
   PROP ()
   LOCAL (temp _r (vint r); gvar _reading reading; gvar _last_read last_read)
   SEP (field_at_ Ews (tarray tint N) [ArraySubsc r] reading;
        field_at_ Ews (tarray tint N) [ArraySubsc r] last_read)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (field_at Ews (tarray tint N) [ArraySubsc r] (vint (-1)) reading;
        field_at Ews (tarray tint N) [ArraySubsc r] (vint 0) last_read).

(* last_read retains the last buffer read, while reading is reset to Empty. *)
Definition start_read_spec :=
 DECLARE _start_read
  WITH gsh1 : share, r : Z, reading : val, last_read : val, last_given : val, b0 : Z, b : Z
  PRE [ _r OF tint ]
   PROP ()
   LOCAL (temp _r (vint r); gvar _reading reading; gvar _last_read last_read)
   SEP (field_at_ Ews (tarray tint N) [ArraySubsc r] reading;
        field_at Ews (tarray tint N) [ArraySubsc r] (vint b0) last_read; ghost [R r b0])
  POST [ tvoid ]
   EX b : Z,
   PROP (0 <= b)
   LOCAL ()
   SEP (field_at Ews (tarray tint N) [ArraySubsc r] (vint b) reading;
        field_at Ews (tarray tint N) [ArraySubsc r] (vint b) last_read; ghost [R r b]).
(* And bufs[b] is the most recent buffer completed by finish_write. *)
(* This will probably be a ghost-variable property. *)

Definition finish_read_spec :=
 DECLARE _finish_read
  WITH r : Z, reading : val
  PRE [ _r OF tint ]
   PROP ()
   LOCAL (temp _r (vint r); gvar _reading reading)
   SEP (field_at_ Ews (tarray tint N) [ArraySubsc r] reading)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (field_at Ews (tarray tint N) [ArraySubsc r] (vint (-1)) reading).

Definition initialize_writer_spec :=
 DECLARE _initialize_writer
  WITH writing : val, last_given : val, last_taken : val
  PRE [ ]
   PROP ()
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
   SEP (data_at_ Ews tint writing; data_at_ Ews tint last_given;
        data_at_ Ews (tarray tint N) last_taken)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (data_at Ews tint (vint (-1)) writing; data_at Ews tint (vint 0) last_given;
        data_at Ews (tarray tint N) (repeat (vint (-1)) (Z.to_nat N)) last_taken).

Definition start_write_spec :=
 DECLARE _start_write
  WITH gsh1 : share, writing : val, last_given : val, last_taken : val, reading : val, b0 : Z, lasts : list Z
  PRE [ ]
   PROP ()
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
   SEP (data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken)
  POST [ tint ]
   EX b : Z,
   PROP ()
   LOCAL (temp ret_temp (vint b))
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken).
(* And b is not in use by any reader. Can the current ghost state get us this? *)

Definition finish_write_spec :=
 DECLARE _finish_write
  WITH gsh1 : share, writing : val, last_given : val, last_taken : val, reading : val, b : Z, b0 : Z,
       lasts : list Z
  PRE [ ]
   PROP (0 <= b <= Int.max_signed)
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken; ghost [W lasts b0])
  POST [ tint ]
   EX lasts' : list Z,
   PROP ()
   LOCAL (temp ret_temp (vint b))
   SEP (data_at Ews tint (vint (-1)) writing; data_at Ews tint (vint b) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts') last_taken; ghost [W lasts' b]).

(* For now, we'll focus on proving these. *)

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  surely_malloc_spec; memset_spec; atomic_exchange_spec; initialize_channels_spec; initialize_reader_spec;
  start_read_spec; finish_read_spec; initialize_writer_spec; start_write_spec; finish_write_spec]).

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function. 
  forward_call (* p = malloc(n); *)
     n.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh n p * memory_block Tsh n p)).
*
  if_tac.
    subst p. entailer!.
    entailer!.
*
    forward_call tt.
    contradiction.
*
    if_tac.
    + forward. subst p. inv H0.
    + Intros. forward. entailer!.
*
  forward. Exists p; entailer!.
Qed.

Lemma body_memset : semax_body Vprog Gprog f_memset memset_spec.
Proof.
  start_function.
  forward.
  rewrite data_at__isptr; Intros.
  rewrite sem_cast_neutral_ptr; auto.
  pose proof (sizeof_pos t).
  forward_for_simple_bound n (EX i : Z, PROP () LOCAL (temp _p p; temp _s p; temp _c (vint c); temp _n (vint n))
    SEP (data_at sh (tarray tuchar n) (repeat (vint c) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (n - i))) p)).
  { entailer!.
    apply derives_trans with (Q := data_at_ sh (tarray tuchar (sizeof t)) p).
    - rewrite !data_at__memory_block; simpl.
      assert ((1 * Z.max 0 (sizeof t))%Z = sizeof t) as Hsize.
      { rewrite Z.mul_1_l, Z.max_r; auto; apply Z.ge_le; auto. }
      setoid_rewrite Hsize; Intros; apply andp_right; [|simpl; apply derives_refl].
      apply prop_right; match goal with H : field_compatible _ _ _ |- _ =>
        destruct H as (? & ? & ? & ? & ? & ? & ? & ?) end; repeat split; simpl; auto.
      + unfold legal_alignas_type, tarray, nested_pred, local_legal_alignas_type; simpl.
        rewrite andb_true_r, Z.leb_le; apply Z.ge_le; auto.
      + setoid_rewrite Hsize; auto.
      + unfold size_compatible in *; simpl.
        destruct p; try contradiction.
        setoid_rewrite Hsize; auto.
      + unfold align_compatible; simpl.
        unfold align_attr; simpl.
        destruct p; try contradiction.
        apply Z.divide_1_l.
    - rewrite data_at__eq.
      unfold default_val, reptype_gen; simpl.
      rewrite repeat_list_repeat, Z.sub_0_r; apply derives_refl. }
  - forward.
    entailer!.
    rewrite upd_Znth_app2; rewrite !Zlength_repeat, !Z2Nat.id; try omega.
    rewrite Zminus_diag, upd_Znth0.
    destruct (Z.to_nat (sizeof t - i)) eqn: Hi.
    { change O with (Z.to_nat 0) in Hi; apply Z2Nat.inj in Hi; omega. }
    simpl; rewrite sublist_1_cons, sublist_same; try rewrite Zlength_cons, !Zlength_repeat; try omega.
    repeat match goal with H : _ /\ _ |- _ => destruct H end; assert (c <= Int.max_unsigned).
    { etransitivity; eauto; unfold Int.max_unsigned; simpl; computable. }
    rewrite zero_ext_inrange; rewrite zero_ext_inrange; rewrite ?Int.unsigned_repr; try omega.
    replace (Z.to_nat (sizeof t - (i + 1))) with n.
    rewrite Z2Nat.inj_add, repeat_plus, <- app_assoc; auto; try omega.
    rewrite Z.sub_add_distr, Z2Nat.inj_sub; try omega.
    setoid_rewrite Hi; simpl; omega.
  - forward.
    rewrite Zminus_diag, app_nil_r; apply derives_refl.
Qed.

Lemma lock_struct_array_sub : forall sh z i (v : val) p,
  field_at sh (tarray (tptr (Tstruct _lock_t noattr)) z) [ArraySubsc i] v p =
  field_at sh (tarray (tptr tlock) z) [ArraySubsc i] v p.
Proof.
  intros.
  unfold field_at, at_offset; rewrite !data_at_rec_eq; simpl; f_equal.
Qed.

(*Axiom ghost_precise : forall l, precise (ghost l).*)
(* Is it too strong to say that any ghost is precise? Anyway, all we need is this. *)
Axiom G_precise : forall r, precise (EX br : Z, EX bw : Z, ghost [G r br bw]).

Lemma inv_precise : forall comm r, precise (comm_inv comm r).
Proof.
  unfold comm_inv; intros.
  eapply derives_precise' with (Q := _ * field_at_ Ews (tarray tint N) [ArraySubsc r] comm);
    [|apply precise_sepcon; [apply G_precise | auto]].
  Intros br bw; Exists br bw; apply sepcon_derives; eauto; cancel.
Qed.

Lemma inv_positive : forall comm r, positive_mpred (comm_inv comm r).
Proof.
  unfold comm_inv; intros.
  repeat (apply ex_positive; intro).
  apply positive_andp2, positive_sepcon2, positive_andp2.
  unfold at_offset; rewrite data_at_rec_eq; simpl; auto.
Qed.
Hint Resolve inv_precise inv_positive.

Lemma consistent_drop : forall l1 a l2, consistent (l1 ++ a :: l2) -> consistent (l1 ++ l2).
Proof.
  induction l1; simpl; intros.
  - destruct H; auto.
  - destruct H as (H & ?); split; [|eapply IHl1; eauto].
    rewrite Forall_app in H; destruct H as (? & H2); inv H2; rewrite Forall_app; auto.
Qed.

Lemma body_atomic_exchange : semax_body Vprog Gprog f_simulate_atomic_exchange atomic_exchange_spec.
Proof.
  start_function.
  rewrite <- lock_struct_array_sub, lock_inv_isptr; Intros.
  forward.
  forward_call (l, sh2, comm_inv comm r(* gsh2 reading last_given*)).
  unfold comm_inv at 2.
  Intros br bw.
  forward.
  forward.
  gather_SEP 1 4; rewrite ghost_join.
  assert_PROP (consistent [G r br bw; g]) as Hcon.
  { go_lowerx.
    apply sepcon_derives_prop, ghost_consistent. }
  simpl in Hcon; destruct Hcon as (Hcon & _); inversion Hcon as [|?? Hcon' _]; subst.
  destruct writer eqn: Hwriter; [destruct H1 as (? & ? & Hneq & Hv) | destruct H1 as (? & ?)];
    subst; simpl in Hcon'.
  - destruct Hcon' as (Hlen & ? & Hcon'); subst.
    apply ghost_shift with (l' := [G r br v] ++ [W (if eq_dec br bw then upd_Znth r brs bw else brs) v]).
    { clear - H Hlen Hcon'; intros p Hcon.
      rewrite <- Hlen in H.
      assert (consistent1 (G r br v) (W (if eq_dec br bw then upd_Znth r brs bw else brs) v)).
      { repeat split; auto; destruct (eq_dec br bw); auto.
        * rewrite upd_Znth_Zlength; auto.
        * subst; left; apply upd_Znth_same; auto.
        * destruct Hcon'; auto; contradiction n; auto. }
      induction p.
      * repeat split; simpl in *; auto.
      * simpl in Hcon.
        destruct Hcon as (Hcon1 & Hcon2 & ? & ?).
        inversion Hcon1 as [|??? HconG]; inv HconG; inv Hcon2.
        destruct a; simpl in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; try contradiction.
        subst.
        assert (Znth r0 (if eq_dec br0 bw then upd_Znth r0 brs bw else brs) (-2) = br0).
        { destruct (eq_dec br0 bw); [|destruct Hcon'; auto; contradiction n; auto].
          subst; apply upd_Znth_same; auto. }
        lapply IHp.
        intros (Hcon1' & Hcon2' & _).
        inversion Hcon1'.
        repeat constructor; auto.
        { repeat split; auto.
          constructor; auto; repeat split; auto. } }
    rewrite <- ghost_join.
    forward_call (l, sh2, comm_inv comm r).
    { lock_props.
      unfold comm_inv.
      Exists br v; entailer!.
      destruct (eq_dec br v); [|cancel].
      subst; destruct Hcon'; [|subst; contradiction Hneq; auto].
      rewrite Forall_forall in Hv; exploit Hv; try contradiction; eauto.
      apply Znth_In; rewrite <- Hlen in *; auto. }
    forward.
    Exists (W (if eq_dec br bw then upd_Znth r brs bw else brs) v) (if eq_dec br bw then -1 else bw); entailer!.
    + destruct (eq_dec br bw); destruct (initial_world.EqDec_Z _ _); auto.
      * contradiction n; auto.
      * omega.
    + simpl; rewrite lock_struct_array_sub; cancel.
  - destruct Hcon'; subst.
    apply ghost_shift with (l' := [G r bw bw] ++ [R r bw]).
    { clear; intros p Hcon.
      assert (consistent1 (G r bw bw) (R r bw)) by (simpl; auto).
      induction p.
      * repeat split; simpl in *; auto.
      * simpl in Hcon.
        destruct Hcon as (Hcon1 & Hcon2 & ? & ?).
        inversion Hcon1 as [|??? HconG]; inv HconG; inv Hcon2.
        destruct a; simpl in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; try contradiction.
        subst.
        lapply IHp.
        intros (Hcon1' & Hcon2' & _).
        inv Hcon1'.
        repeat split; repeat apply Forall_cons; repeat split; auto.
        { repeat constructor; auto. } }
    rewrite <- ghost_join.
    forward_call (l, sh2, comm_inv comm r).
    { lock_props.
      unfold comm_inv.
      Exists bw bw; entailer!.
      destruct (eq_dec bw bw); [cancel | contradiction n; auto]. }
    forward.
    Exists (R r (if eq_dec b bw then b else bw)) (if eq_dec b bw then -1 else bw); entailer!.
    + destruct (eq_dec b bw); destruct (initial_world.EqDec_Z _ _); auto.
      * contradiction n; auto.
      * omega.
    + rewrite lock_struct_array_sub; cancel.
      destruct (eq_dec b bw); subst; apply derives_refl.
Qed.
