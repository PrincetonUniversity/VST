Require Import veric.rmaps.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import progs.mailbox.

Set Bullet Behavior "Strict Subproofs".

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
(*Definition freelock_spec := DECLARE _freelock (freelock_spec _).*)
Definition spawn_spec := DECLARE _spawn spawn_spec.
(*Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
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

Definition hist := AE_hist.

Definition AE_inv x i sh R := EX h : list AE_hist_el, EX v : val,
  !!(apply_hist i h = Some v /\ v <> Vundef) &&
  (data_at sh tint v x * ghost ([] : hist, Some h) x * R h v * (weak_precise_mpred (R h v) && emp)).

Lemma AE_inv_positive : forall x i sh R, readable_share sh -> positive_mpred (AE_inv x i sh R).
Proof.
  unfold AE_inv; intros.
  do 2 (apply ex_positive; intro).
  apply positive_andp2, positive_sepcon1, positive_sepcon1, positive_sepcon1; auto.
Qed.
Hint Resolve AE_inv_positive.

Lemma AE_inv_precise : forall x i sh R (Hsh : readable_share sh),
  predicates_hered.derives TT (weak_precise_mpred (AE_inv x i sh R)).
Proof.
  intros ????? rho _ ???
    (? & h1 & v1 & (Hh1 & ?) & ? & ? & Hj1 & (? & ? & Hj'1 & (? & ? & ? & (? & Hv1) & Hg1) & HR1) & (HR & Hemp1))
    (? & h2 & v2 & (Hh2 & ?) & ? & ? & Hj2 & (? & ? & Hj'2 & (? & ? & ? & (? & Hv2) & Hg2) & HR2) & (_ & Hemp2))
    Hw1 Hw2.
  unfold at_offset in *; simpl in *; rewrite data_at_rec_eq in Hv1, Hv2; simpl in *.
  exploit (mapsto_inj _ _ _ _ _ _ _ w Hsh Hv1 Hv2); auto; try join_sub.
  unfold unfold_reptype; simpl; intros (? & Hv).
(*  assert (v1 = v2).
  { apply repr_inj_signed; auto; congruence. }*)
(*  exploit (ghost_inj' _ _ _ _ _ _ _ w Hg1 Hg2); try join_sub.
  intros (? & ?); subst.
  destruct (age_sepalg.join_level _ _ _ Hj1).
  exploit HR.
  { split; [|apply HR1].
    destruct (age_sepalg.join_level _ _ _ Hj'1); omega. }
  { split; [|apply HR2].
    pose proof (juicy_mem.rmap_join_sub_eq_level _ _ Hw1).
    pose proof (juicy_mem.rmap_join_sub_eq_level _ _ Hw2).
    destruct (age_sepalg.join_level _ _ _ Hj2), (age_sepalg.join_level _ _ _ Hj'2); omega. }
  { join_sub. }
  { join_sub. }
  intro; join_inj.
  apply sepalg.join_comm in Hj1; apply sepalg.join_comm in Hj2.
  match goal with H1 : predicates_hered.app_pred emp ?a,
    H2 : predicates_hered.app_pred emp ?b |- _ => assert (a = b);
      [eapply sepalg.same_identity; auto;
        [match goal with H : sepalg.join a ?x ?y |- _ =>
           specialize (Hemp1 _ _ H); instantiate (1 := x); subst; auto end |
         match goal with H : sepalg.join b ?x ?y |- _ =>
           specialize (Hemp2 _ _ H); subst; auto end] | subst] end.
  join_inj.
Qed.*)
Admitted.

(* Can we always provide a clunky function such that P and Q are a single function? *)
(* Compare and contrast with magic wand proof of bin tree *)
Definition AE_spec i P R Q := forall hc hx vc vx, apply_hist i hx = Some vx ->
  view_shift (R hx vx * P hc vc)
  (R (hx ++ [AE vx vc]) vc * (weak_precise_mpred (R (hx ++ [AE vx vc]) vc) && emp) *
   Q (hc ++ [(length hx, AE vx vc)]) vx).

Definition AE_type := ProdType (ProdType (ProdType
  (ConstType (share * share * val * val * val * val * hist))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType (list AE_hist_el)) (ArrowType (ConstType val) Mpred)))
  (ArrowType (ConstType hist) (ArrowType (ConstType val) Mpred)).

Notation "'TYPE' A 'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default A
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => P%assert end)
  (fun (ts: list Type) (x: t1*t2*t3*t4*t5*t6*t7*t8*t9*t10) =>
     match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10) => Q%assert end) _ _)
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0, x10 at level 0,
             P at level 100, Q at level 100).

Definition ghost_hist (h : hist) p := ghost (h, @None (list AE_hist_el)) p.

(* It would be nice to be able to store any kind of data in the location, but that won't typecheck. *)
Program Definition atomic_exchange_spec := DECLARE _simulate_atomic_exchange
  TYPE AE_type WITH ish : share, lsh : share, tgt : val, l : val,
    i : val, v : val, h : hist, P : hist -> val -> mpred, R : list AE_hist_el -> val -> mpred, Q : hist -> val -> mpred
  PRE [ _tgt OF tptr tint, _l OF tptr (Tstruct _lock_t noattr), _v OF tint ]
   PROP (tc_val tint v; readable_share lsh; writable_share ish; AE_spec i P R Q)
   LOCAL (temp _tgt tgt; temp _l l; temp _v v)
   SEP (lock_inv lsh l (AE_inv tgt i ish R); ghost_hist h tgt; P h v; weak_precise_mpred (P h v) && emp)
  POST [ tint ]
   EX t : nat, EX v' : val,
   PROP (Forall (fun x => fst x < t)%nat h)
   LOCAL (temp ret_temp v')
   SEP (lock_inv lsh l (AE_inv tgt i ish R); ghost_hist (h ++ [(t, AE v' v)]) tgt;
        Q (h ++ [(t, AE v' v)]) v').
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type)
    (x : share * share * val * val * val * val * hist *
         (hist -> val -> mpred) * (list AE_hist_el -> val -> mpred) * (hist -> val -> mpred)) rho =>
    PROP (let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in tc_val tint v /\ readable_share lsh /\
      writable_share ish /\ AE_spec i P R Q)
    LOCAL (let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in temp _tgt tgt;
           let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in temp _l l;
           let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in temp _v v)
    SEP (let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in
         lock_inv lsh l (AE_inv tgt i ish R) * ghost_hist h tgt * P h v *
         (weak_precise_mpred (P h v) && emp)) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive AE_type [fun _ => _] [fun _ => _; fun _ => _; fun _ => _]
    [fun _ => _]); repeat constructor; hnf; intros;
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto; simpl.
  - unfold AE_spec.
    (* This is probably provable for derives, but might need to be assumed for view shift. *)
    admit.
  - rewrite !approx_sepcon; f_equal; [f_equal|].
    + f_equal.
      rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
      setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
      f_equal; f_equal.
      unfold AE_inv; rewrite !approx_exp; f_equal; extensionality l'.
      rewrite !approx_exp; f_equal; extensionality z'.
      rewrite !approx_andp, !approx_sepcon; f_equal; f_equal.
      * replace (compcert_rmaps.RML.R.approx n (R l' z')) with
          (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) (R l' z')) at 1
          by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
      * rewrite !approx_andp; f_equal.
        apply (nonexpansive_super_non_expansive), precise_mpred_nonexpansive.
    + replace (compcert_rmaps.RML.R.approx n (P h v2)) with
        (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) (P h v2)) at 1
        by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
    + rewrite !approx_andp; f_equal.
      apply (nonexpansive_super_non_expansive), precise_mpred_nonexpansive.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto.
    unfold PROPx, SEPx; simpl; rewrite !sepcon_assoc; f_equal.
    f_equal; apply prop_ext; tauto.
Admitted.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type)
    (x : share * share * val * val * val * val * hist *
         (hist -> val -> mpred) * (list AE_hist_el -> val -> mpred) * (hist -> val -> mpred)) rho =>
    EX t : nat, EX v' : val,
      PROP (let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in Forall (fun x => (fst x < t)%nat) h)
      LOCAL (let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in temp ret_temp v')
      SEP (let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in
           lock_inv lsh l (AE_inv tgt i ish R) * ghost_hist (h ++ [(t, AE v' v)]) tgt *
           Q (h ++ [(t, AE v' v)]) v') rho).
  repeat intro.
  rewrite !approx_exp; f_equal; extensionality t.
  rewrite !approx_exp; f_equal; extensionality v'.
  pose proof (PROP_LOCAL_SEP_super_non_expansive AE_type
    [fun ts x => let '(_, _, _, _, _, _, h, _, _, _) := x in Forall (fun x => (fst x < t)%nat) h]
    [fun ts x => let '(_, _, _, _, _, _, _, _, _, _) := x in temp ret_temp v']
    [fun ts x => let '(ish, lsh, tgt, l, i, v, h, P, R, Q) := x in
       lock_inv lsh l (AE_inv tgt i ish R) * ghost_hist (h ++ [(t, AE v' v)]) tgt *
       Q (h ++ [(t, AE v' v)]) v'])
    as Heq; apply Heq; repeat constructor; hnf; intros;
      destruct x0 as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto; simpl.
  - rewrite !approx_sepcon; f_equal.
    + rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
      f_equal.
      setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
      f_equal; f_equal.
      unfold AE_inv; rewrite !approx_exp; f_equal; extensionality l'.
      rewrite !approx_exp; f_equal; extensionality z'.
      rewrite !approx_andp, !approx_sepcon; f_equal; f_equal.
      * replace (compcert_rmaps.RML.R.approx n0 (R l' z')) with
          (base.compose (compcert_rmaps.R.approx n0) (compcert_rmaps.R.approx n0) (R l' z')) at 1
          by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
      * rewrite !approx_andp; f_equal.
        apply (nonexpansive_super_non_expansive), precise_mpred_nonexpansive.
    + replace (compcert_rmaps.RML.R.approx n0 (Q _ v')) with
        (base.compose (compcert_rmaps.R.approx n0) (compcert_rmaps.R.approx n0) (Q (h ++ [(t, AE v' v2)]) v')) at 1
        by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), P), R), Q); auto.
    f_equal; extensionality.
    f_equal; extensionality.
    unfold SEPx; simpl; rewrite !sepcon_assoc; auto.
Qed.

Definition Empty := vint (-1).

Fixpoint find_read h d :=
  match h with
  | [] => (d, [])
  | AE r w :: rest => if eq_dec w Empty then if eq_dec r Empty then find_read rest d
                      else (r, rest) else find_read rest d
  end.

Definition last_two_reads h := let '(b1, rest) := find_read h (vint 1) in
  (b1, fst (find_read rest (vint (-1)))).

Fixpoint find_write h :=
  match h with
  | [] => None
  | AE r w :: rest => if eq_dec w Empty then find_write rest else Some (w, rest)
  end.

Definition prev_taken h := match find_write h with
  Some (_, rest) => fst (find_read rest (vint 1)) | None => vint 1 end.

Definition last_write h := match find_write h with Some (w, _) => w | None => vint 0 end.

(* The ghost variables are the last value read, the last value written, and the last value read before
   the last write (i.e., last_taken). The first is updated by the reader, the rest by the writer. *)

(* We can't use tokens because we need to consistently get the same share for each reader
   (so that the communication invariant is precise). *)
Definition comm_R bufs sh gsh p h v := EX b : Z, EX b1 : Z, EX b2 : Z,
  !!(v = vint b /\ -1 <= b < B /\ Forall (fun a => match a with AE v1 v2 => exists r w, v1 = vint r /\ v2 = vint w /\
     -1 <= r < B /\ -1 <= w < B end) h /\ last_two_reads (rev h) = (vint b1, vint b2)) &&
  ghost_var gsh tint (vint b1) p * ghost_var gsh tint (last_write (rev h)) (offset_val 1 p) *
  ghost_var gsh tint (prev_taken (rev h)) (offset_val 2 p) *
  if eq_dec b (-1) then EX v : Z, data_at sh tbuffer (vint v) (Znth b2 bufs Vundef)
  else EX v : Z, data_at sh tbuffer (vint v) (Znth b bufs Vundef).

Definition comm_inv comm bufs sh gsh := AE_inv comm Empty Tsh (comm_R bufs sh gsh comm).

Definition initialize_channels_spec :=
 DECLARE _initialize_channels
  WITH comm : val, lock : val, buf : val, reading : val, last_read : val,
       gsh1 : share, gsh2 : share, sh1 : share, shs : list share
  PRE [ ]
   PROP (sepalg.join gsh1 gsh2 Tsh; sepalg_list.list_join sh1 shs Tsh)
   LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs buf; gvar _reading reading; gvar _last_read last_read)
   SEP (data_at_ Ews (tarray (tptr tint) N) comm; data_at_ Ews (tarray (tptr tlock) N) lock;
        data_at_ Ews (tarray (tptr tbuffer) B) buf;
        data_at_ Ews (tarray (tptr tint) N) reading; data_at_ Ews (tarray (tptr tint) N) last_read)
  POST [ tvoid ]
   EX comms : list val, EX locks : list val, EX bufs : list val, EX reads : list val, EX lasts : list val,
   PROP (Forall isptr comms)
   LOCAL ()
   SEP (data_at Ews (tarray (tptr tint) N) comms comm;
        data_at Ews (tarray (tptr tlock) N) locks lock;
        data_at Ews (tarray (tptr tbuffer) B) bufs buf;
        data_at Ews (tarray (tptr tint) N) reads reading;
        data_at Ews (tarray (tptr tint) N) lasts last_read;
        fold_right sepcon emp (map (fun r =>
          lock_inv Tsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_hist []) comms);
        fold_right sepcon emp (map (ghost_var gsh1 tint (vint 0)) comms);
        fold_right sepcon emp (map (fun c => ghost_var gsh1 tint (vint 0) (offset_val 1 c) *
          ghost_var gsh1 tint Empty (offset_val 2 c)) comms);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) comms);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tlock)) locks);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) reads);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) lasts);
        fold_right sepcon emp (map (data_at Tsh tbuffer (vint 0)) bufs);
        fold_right sepcon emp (map (data_at_ Tsh tint) reads);
        fold_right sepcon emp (map (data_at_ Tsh tint) lasts)).
(* All the communication channels are now inside locks. *)

Definition initialize_reader_spec :=
 DECLARE _initialize_reader
  WITH r : Z, reading : val, last_read : val, reads : list val, lasts : list val, sh : share
  PRE [ _r OF tint ]
   PROP (readable_share sh)
   LOCAL (temp _r (vint r); gvar _reading reading; gvar _last_read last_read)
   SEP (data_at sh (tarray (tptr tint) N) reads reading; data_at sh (tarray (tptr tint) N) lasts last_read;
        data_at_ Tsh tint (Znth r reads Vundef); data_at_ Tsh tint (Znth r lasts Vundef))
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (data_at sh (tarray (tptr tint) N) reads reading; data_at sh (tarray (tptr tint) N) lasts last_read;
        data_at Tsh tint Empty (Znth r reads Vundef); data_at Tsh tint (vint 1) (Znth r lasts Vundef)).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0, x15 at level 0, x16 at level 0, x17 at level 0,
             P at level 100, Q at level 100).

Definition latest_read (h : hist) v := exists n, In (n, AE v Empty) h /\ Forall (fun x => fst x <= n)%nat h.

(* last_read retains the last buffer read, while reading is reset to Empty. *)
Definition start_read_spec :=
 DECLARE _start_read
  WITH r : Z, reading : val, last_read : val, lock : val, comm : val, reads : list val, lasts : list val,
    locks : list val, comms : list val, bufs : list val, sh : share, sh1 : share, sh2 : share, b0 : Z,
    gsh1 : share, gsh2 : share, h : hist
  PRE [ _r OF tint ]
   PROP (0 <= b0 < B; readable_share sh; readable_share sh1; readable_share sh2;
         sepalg.join gsh1 gsh2 Tsh; isptr (Znth r comms Vundef); latest_read h (vint b0))
   LOCAL (temp _r (vint r); gvar _reading reading; gvar _last_read last_read; gvar _lock lock; gvar _comm comm)
   SEP (data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
        data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at_ Tsh tint (Znth r reads Vundef); data_at Tsh tint (vint b0) (Znth r lasts Vundef);
        lock_inv sh2 (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs sh gsh2);
        EX v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs Vundef);
        ghost_hist h (Znth r comms Vundef); ghost_var gsh1 tint (vint b0) (Znth r comms Vundef))
  POST [ tint ]
   EX b : Z, EX t : nat, EX v0 : val, EX v : Z,
   PROP (0 <= b < B; if eq_dec v0 Empty then b = b0 else v0 = vint b)
   LOCAL (temp ret_temp (vint b))
   SEP (data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
        data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at Tsh tint (vint b) (Znth r reads Vundef); data_at Tsh tint (vint b) (Znth r lasts Vundef);
        lock_inv sh2 (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs sh gsh2);
        data_at sh tbuffer (vint v) (Znth b bufs Vundef);
        ghost_hist (h ++ [(t, AE v0 Empty)]) (Znth r comms Vundef);
        ghost_var gsh1 tint (vint b) (Znth r comms Vundef)).
(* And bufs[b] is the most recent buffer completed by finish_write. *)

Definition finish_read_spec :=
 DECLARE _finish_read
  WITH r : Z, reading : val, reads : list val, sh : share
  PRE [ _r OF tint ]
   PROP (readable_share sh)
   LOCAL (temp _r (vint r); gvar _reading reading)
   SEP (data_at sh (tarray (tptr tint) N) reads reading; data_at_ Tsh tint (Znth r reads Vundef))
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (data_at sh (tarray (tptr tint) N) reads reading; data_at Tsh tint Empty (Znth r reads Vundef)).

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
   SEP (data_at Ews tint Empty writing; data_at Ews tint (vint 0) last_given;
        data_at Ews (tarray tint N) (repeat (vint 1) (Z.to_nat N)) last_taken).

Definition start_write_spec :=
 DECLARE _start_write
  WITH gsh1 : share, writing : val, last_given : val, last_taken : val, b0 : Z, lasts : list Z
  PRE [ ]
   PROP (0 <= b0 < B; Forall (fun x => -1 <= x < B) lasts)
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
   SEP (data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken)
  POST [ tint ]
   EX b : Z,
   PROP (0 <= b < B; b <> b0; ~In b lasts)
   LOCAL (temp ret_temp (vint b))
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken).
(* And b is not in use by any reader. This follows from the property on lasts, but can we relate it to the
   relevant ghost state? *)

Fixpoint make_shares shs (lasts : list Z) i : list share :=
  match lasts with
  | [] => []
  | b :: rest => if eq_dec b i then make_shares (tl shs) rest i
                 else hd Share.bot shs :: make_shares (tl shs) rest i
  end.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0, x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0,
             P at level 100, Q at level 100).

(* A possible refinement, removing the requirement that the buffers be initialized, would be to
   turn the buffer invariant into upd_Znth b0 (map ... data_at_ sh tbuffer ... B) (EX v, data_at sh0 ...). *)
Definition finish_write_spec :=
 DECLARE _finish_write
  WITH writing : val, last_given : val, last_taken : val, comm : val, lock : val,
    comms : list val, locks : list val, bufs : list val, b : Z, b0 : Z, lasts : list Z,
    sh1 : share, lsh : share, shs : list share, gsh1 : share, gsh2 : share, h : list hist, sh0 : share
  PRE [ ]
   PROP (0 <= b < B; 0 <= b0 < B; Forall (fun x => -1 <= x < B) lasts; Zlength h = N; Zlength shs = N;
         readable_share sh1; readable_share lsh; readable_share sh0; Forall readable_share shs;
         sepalg_list.list_join sh0 shs Tsh; sepalg.join gsh1 gsh2 Tsh;
         Forall isptr comms; b <> b0; ~In b lasts; ~In b0 lasts)
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _comm comm;
          gvar _lock lock)
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        fold_right sepcon emp (map (fun r =>
          lock_inv lsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun x => let '(c, h) := x in ghost_hist h c) (combine comms h));
        fold_right sepcon emp (map (fun r => ghost_var gsh1 tint (vint b0) (offset_val 1 (Znth r comms Vundef)) *
          ghost_var gsh1 tint (vint (Znth r lasts (-1)))
            (offset_val 2 (Znth r comms Vundef))) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i b0 then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts i) sh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B))))
  POST [ tvoid ]
   EX lasts' : list Z, EX h' : list hist,
   PROP (Forall (fun x => -1 <= x < B) lasts';
         Forall2 (fun h1 h2 => exists t v, h2 = h1 ++ [(t, AE v (vint b))]) h h';
         ~In b lasts')
   LOCAL ()
   SEP (data_at Ews tint Empty writing; data_at Ews tint (vint b) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts') last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        fold_right sepcon emp (map (fun r =>
          lock_inv lsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun x => let '(c, h) := x in ghost_hist h c) (combine comms h'));
        fold_right sepcon emp (map (fun r => ghost_var gsh1 tint (vint b) (offset_val 1 (Znth r comms Vundef)) *
          ghost_var gsh1 tint (vint (Znth r lasts' (-1)))
            (offset_val 2 (Znth r comms Vundef))) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i b then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts' i) sh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B)))).

Definition reader_spec :=
 DECLARE _reader
  WITH arg : val, x : Z * val * val * val * val * val * list val * list val * list val * list val * list val *
                      share * share * share * share * share
  PRE [ _arg OF tptr tvoid ]
   let '(r, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs, sh1, sh2, sh, gsh1, gsh2) := x in
   PROP (readable_share sh; readable_share sh1; readable_share sh2; sepalg.join gsh1 gsh2 Tsh; isptr (Znth r comms Vundef))
   LOCAL (temp _arg arg; gvar _reading reading; gvar _last_read last_read;
          gvar _lock lock; gvar _comm comm; gvar _bufs buf)
   SEP (data_at Tsh tint (vint r) arg; malloc_token Tsh (sizeof tint) arg;
        data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
        data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at_ Tsh tint (Znth r reads Vundef); data_at_ Tsh tint (Znth r lasts Vundef);
        data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
        lock_inv sh2 (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs sh gsh2);
        EX v : Z, data_at sh tbuffer (vint v) (Znth 1 bufs Vundef);
        ghost_hist [] (Znth r comms Vundef); ghost_var gsh1 tint (vint 1) (Znth r comms Vundef))
  POST [ tptr tvoid ] PROP () LOCAL () SEP (emp).

Definition writer_spec :=
 DECLARE _writer
  WITH arg : val, x : val * val * val * val * val * val * list val * list val * list val *
                      share * share * share * list share * share * share
  PRE [ _arg OF tptr tvoid ]
   let '(writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs, gsh1, gsh2) := x in
   PROP (Zlength shs = N; readable_share sh1; readable_share lsh; readable_share sh0; Forall readable_share shs;
         sepalg_list.list_join sh0 shs Tsh; sepalg.join gsh1 gsh2 Tsh; Forall isptr comms)
   LOCAL (temp _arg arg; gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken;
          gvar _lock lock; gvar _comm comm; gvar _bufs buf)
   SEP (data_at_ Ews tint writing; data_at_ Ews tint last_given; data_at_ Ews (tarray tint N) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
        fold_right sepcon emp (map (fun r =>
          lock_inv lsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_hist []) comms);
        fold_right sepcon emp (map (fun c => ghost_var gsh1 tint (vint 0) (offset_val 1 c) *
          ghost_var gsh1 tint (vint 1) (offset_val 2 c)) comms);
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i 0 then sh = sh0 else if eq_dec i 1 then sh = sh0 else sh = Tsh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B))))
  POST [ tptr tvoid ] PROP () LOCAL () SEP (emp).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog [] u
  POST [ tint ] main_post prog [] u.

Definition Gprog : funspecs := ltac:(with_library prog [acquire_spec; release_spec; makelock_spec; spawn_spec;
  surely_malloc_spec; memset_spec; atomic_exchange_spec; initialize_channels_spec; initialize_reader_spec;
  start_read_spec; finish_read_spec; initialize_writer_spec; start_write_spec; finish_write_spec;
  reader_spec; writer_spec; main_spec]).

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
    repeat match goal with H : _ /\ _ |- _ => destruct H end; assert (c <= Int.max_unsigned).
    { etransitivity; eauto; unfold Int.max_unsigned; simpl; computable. }
    entailer!.
    rewrite zero_ext_inrange; rewrite zero_ext_inrange; rewrite ?Int.unsigned_repr; try omega.
    rewrite upd_init_const; [|omega].
    entailer!.
  - forward.
    rewrite Zminus_diag, app_nil_r; apply derives_refl.
Qed.

Lemma body_atomic_exchange : semax_body Vprog Gprog f_simulate_atomic_exchange atomic_exchange_spec.
Proof.
 match goal with |- semax_body ?V ?G ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s;
    match goal with
    | s :=  (DECLARE _ WITH u : unit
               PRE  [] main_pre _ nil u
               POST [ tint ] main_post _ nil u) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end.
 let DependedTypeList := fresh "DependedTypeList" in
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>
   match Pre with 
   | (fun x => match x with (a,b) => _ end) => intros Espec DependedTypeList [a b] 
   | (fun i => _) => intros Espec DependedTypeList i
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end.
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 simplify_func_tycontext;
 repeat match goal with 
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 process_stackframe_of.
 repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;
 repeat (apply semax_extract_PROP; 
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH 
                 | Share.t => intros ?SH 
                 | _ => intro
                 end
               | |- _ => intro
               end);
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
 abbreviate_semax.
  simpl; destruct ts as (((((((((ish, lsh), tgt), l), i), v), h), P), R), Q).
(* start_function doesn't work for dependent specs? *)
  rewrite lock_inv_isptr; Intros.
  forward_call (l, lsh, AE_inv tgt i ish R).
  unfold AE_inv at 2; Intros h' v'.
  gather_SEP 2 5; rewrite sepcon_comm.
  assert_PROP (join (h, None) ([], Some h') (h, Some h')) as Hjoin.
  { go_lowerx; apply sepcon_derives_prop.
    eapply derives_trans; [apply ghost_conflict|].
    apply prop_left; intros (? & (_ & Hh) & ([(? & ?) | (<- & _)] & Hincl)); try discriminate; simpl in *.
    apply prop_right; rewrite app_nil_r in *; repeat split; auto.
    repeat intro; apply Hincl.
    rewrite <- Hh; auto. }
  unfold ghost_hist; rewrite (ghost_join _ _ _ _ Hjoin).
  forward.
  { entailer!.
    unfold tc_val' in *; tauto. }
  forward.
  assert (apply_hist i (h' ++ [AE v' v]) = Some v) as Hh'.
  { erewrite apply_hist_app by eauto; simpl.
    apply eq_dec_refl. }
  apply hist_add with (e := AE v' v).
  destruct Hjoin as (? & ? & Hincl); simpl in Hincl.
  erewrite <- ghost_join; [|apply hist_sep_join].
  gather_SEP 3 5; simpl.
  match goal with H : AE_spec _ _ _ _ |- _ => apply H; auto end.
  forward_call (l, lsh, AE_inv tgt i ish R).
  { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
      [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
    { apply AE_inv_precise; auto. }
    unfold AE_inv.
    Exists (h' ++ [AE v' v]) v; entailer!.
    cancel.
    rewrite (sepcon_comm (_ * _) (ghost _ _)), !sepcon_assoc; apply sepcon_derives; auto; cancel. }
  forward.
  Exists (length h') (Vint v'); entailer!.
  - rewrite Forall_forall; intros (?, ?) Hin.
    specialize (Hincl _ _ Hin).
    simpl; rewrite <- nth_error_Some, Hincl; discriminate.
  - rewrite <- (sepcon_emp (ghost_hist _ _)), sepcon_assoc.
    apply sepcon_derives; auto.
    rewrite <- (sepcon_emp emp) at 3; apply sepcon_derives; apply andp_left2; auto.
  - intros ?? Hin.
    rewrite in_app in Hin; destruct Hin as [Hin | [X | ?]]; [| inv X | contradiction].
    + specialize (Hincl _ _ Hin); rewrite nth_error_app1; auto.
      rewrite <- nth_error_Some, Hincl; discriminate.
    + rewrite nth_error_app2, minus_diag; auto.
Qed.

Lemma lock_struct_array : forall sh z (v : list val) p,
  data_at sh (tarray (tptr (Tstruct _lock_t noattr)) z) v p =
  data_at sh (tarray (tptr tlock) z) v p.
Proof.
  intros.
  unfold data_at, field_at, at_offset; rewrite !data_at_rec_eq; simpl; f_equal.
Qed.

Lemma body_initialize_channels : semax_body Vprog Gprog f_initialize_channels initialize_channels_spec.
Proof.
  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound B (EX i : Z, PROP ()
    LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs buf; gvar _reading reading; gvar _last_read last_read)
    SEP (data_at_ Ews (tarray (tptr tint) N) comm; data_at_ Ews (tarray (tptr tlock) N) lock;
         data_at_ Ews (tarray (tptr tint) N) reading; data_at_ Ews (tarray (tptr tint) N) last_read;
         EX bufs : list val, !!(Zlength bufs = i /\ Forall isptr bufs) &&
           data_at Ews (tarray (tptr tbuffer) B) (bufs ++ repeat Vundef (Z.to_nat (B - i))) buf *
           fold_right sepcon emp (map (@data_at CompSpecs Tsh tbuffer (vint 0)) bufs) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs))).
  { unfold B, N; computable. }
  { unfold B, N; computable. }
  { entailer!.
    Exists ([] : list val); simpl; entailer!. }
  { forward_call (sizeof tbuffer).
    { simpl; computable. }
    Intros b bufs.
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    assert_PROP (field_compatible tbuffer [] b) by entailer!.
    forward_call (Tsh, tbuffer, b, 0, sizeof tbuffer).
    { repeat split; simpl; auto; computable. }
    forward.
    rewrite upd_init; auto; try omega.
    entailer!.
    Exists (bufs ++ [b]); rewrite Zlength_app, <- app_assoc, !map_app, !sepcon_app, Forall_app; simpl; entailer!.
    admit. (* How do we go from an array of bytes of the right length to a data_at predicate on a larger type? *)
    { exists 2; auto. } }
  Intros bufs; rewrite Zminus_diag, app_nil_r.
  forward_for_simple_bound N (EX i : Z, PROP ()
    LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs buf; gvar _reading reading; gvar _last_read last_read)
    SEP (EX locks : list val, EX comms : list val, !!(Zlength locks = i /\ Zlength comms = i /\
         Forall isptr comms) &&
          (data_at Ews (tarray (tptr tlock) N) (locks ++ repeat Vundef (Z.to_nat (N - i))) lock *
           data_at Ews (tarray (tptr tint) N) (comms ++ repeat Vundef (Z.to_nat (N - i))) comm *
           fold_right sepcon emp (map (fun r => lock_inv Tsh (Znth r locks Vundef)
             (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2)) (upto (Z.to_nat i))) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tlock)) locks)) *
           fold_right sepcon emp (map (ghost gsh1 (-1) (Tsh, [])) comms) *
(*           fold_right sepcon emp (map (fun c => ghost_var gsh1 tint (vint 0) (offset_val 1 c) *
             ghost_var gsh1 tint Empty (offset_val 2 c)) comms) * *)
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) comms);
         EX reads : list val, !!(Zlength reads = i) &&
           data_at Ews (tarray (tptr tint) N) (reads ++ repeat Vundef (Z.to_nat (N - i))) reading *
           fold_right sepcon emp (map (data_at_ Tsh tint) reads) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) reads);
         EX lasts : list val, !!(Zlength lasts = i) &&
           data_at Ews (tarray (tptr tint) N) (lasts ++ repeat Vundef (Z.to_nat (N - i))) last_read *
           fold_right sepcon emp (map (data_at_ Tsh tint) lasts) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) lasts);
         @data_at CompSpecs Ews (tarray (tptr tbuffer) B) bufs buf;
         fold_right sepcon emp (map (@data_at CompSpecs Tsh tbuffer (vint 0)) bufs);
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs))).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists ([] : list val) ([] : list val) ([] : list val) ([] : list val); rewrite !data_at__eq; entailer!. }
  { Intros locks comms reads lasts.
    forward_call (sizeof tint).
    { simpl; computable. }
    Intro c.
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    forward.
    forward.
    forward_call (sizeof tint).
    { simpl; computable. }
    Intro rr.
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    forward.
    forward_call (sizeof tint).
    { simpl; computable. }
    Intro ll. (* Fun fact: store_tac isn't robust against the existence of a variable named lr. *)
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    forward.
    forward_call (sizeof tlock).
    { admit. }
    { simpl; computable. }
    Intro l.
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    rewrite <- lock_struct_array.
    forward.
    forward_call (l, Tsh, comm_inv c bufs (Znth i shs Tsh) gsh2).
    (* make ghost vars here *)
    gather_SEP 7; eapply new_ghost with (i := -1).
    (* Actually, i should probably be forced to match the current value in general. *)
    erewrite <- ghost_share_join with (sh := Tsh); eauto.
    forward_call (l, Tsh, comm_inv c bufs (Znth i shs Tsh) gsh2).
    { unfold comm_inv; rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm;
        apply sepcon_derives;
        [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
      { apply AE_inv_precise; auto. }
      unfold AE_inv.
      Exists ([] : hist) (-1); unfold comm_R at 3.
      unfold last_two_reads, last_write, prev_taken; simpl; entailer!.
      { split; computable. }
      match goal with |- ?P |-- _ => subst Frame; instantiate (1 := [P]); simpl; cancel end.
      admit. }
    Exists (locks ++ [l]) (comms ++ [c]) (reads ++ [rr]) (lasts ++ [ll]); rewrite !upd_init; try omega.
    rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; rewrite <- !app_assoc.
    go_lower.
    apply andp_right; [apply prop_right; split; auto; omega|].
    apply andp_right; [apply prop_right; repeat split; auto|].
    rewrite !sepcon_andp_prop'; apply andp_right; [apply prop_right; rewrite Forall_app; repeat split; auto; omega|].
    rewrite !sepcon_andp_prop; repeat (apply andp_right; [apply prop_right; omega|]).
    rewrite Z2Nat.inj_add, upto_app, !map_app, !sepcon_app; try omega; simpl.
    rewrite Z2Nat.id, Z.add_0_r; [|omega].
    rewrite !Znth_app1; auto.
    replace (Z.to_nat (N - (Zlength locks + 1))) with (Z.to_nat (N - (i + 1))) by (subst; clear; Omega0).
    subst; rewrite Zlength_correct, Nat2Z.id.
    rewrite <- lock_struct_array; unfold comm_inv, AE_inv.
    erewrite map_ext_in; [cancel|].
    intros; rewrite In_upto, <- Zlength_correct in *.
    rewrite !app_Znth1; try omega; reflexivity.
    { exists 2; auto. }
    { exists 2; auto. }
    { exists 2; auto. }
    { exists 2; auto. } }
  Intros locks comms reads lasts.
  forward.
  rewrite !app_nil_r.
  Exists comms locks bufs reads lasts; entailer!.
  admit.
Admitted.

Lemma body_initialize_reader : semax_body Vprog Gprog f_initialize_reader initialize_reader_spec.
Proof.
  start_function.
  rewrite (data_at__isptr _ tint); Intros.
  assert_PROP (Zlength reads = N) by entailer!.
  assert (0 <= r < N) as Hr.
  { exploit (Znth_inbounds r reads Vundef); [|omega].
    intro Heq; rewrite Heq in *; contradiction. }
  forward.
  forward.
  forward.
  forward.
  forward.
Qed.

Lemma ghost_var_precise' : forall sh t v p, precise (ghost_var sh t v p).
Proof.
  intros; apply derives_precise' with (Q := EX v : reptype t, ghost_var sh t v p);
    [Exists v; auto | apply ghost_var_precise].
Qed.
Hint Resolve ghost_var_precise ghost_var_precise'.

Lemma last_two_reads_cons : forall r w h, last_two_reads (AE r w :: h) =
  if eq_dec w (-1) then if eq_dec r (-1) then last_two_reads h else (r, fst (last_two_reads h))
  else last_two_reads h.
Proof.
  intros; unfold last_two_reads; simpl.
  destruct (eq_dec w (-1)); auto.
  destruct (eq_dec r (-1)); auto.
  destruct (find_read (h ++ [AE 0 (-1)])) as [(?, ?)|]; auto.
  destruct (find_read l) as [(?, ?)|]; auto.
Qed.

Lemma prev_taken_cons : forall r w h, prev_taken (AE r w :: h) =
  if eq_dec w (-1) then prev_taken h else match find_read h with Some (b, _) => b | None => 0 end.
Proof.
  intros; unfold prev_taken; simpl.
  destruct (eq_dec w (-1)); auto.
Qed.

Lemma find_read_pos : forall h v rest, find_read h = Some (v, rest) -> v <> -1.
Proof.
  induction h; [discriminate|]; simpl; intros.
  destruct a.
  destruct (eq_dec w (-1)); eauto.
  destruct (eq_dec r (-1)); eauto.
  inv H; auto.
Qed.

Lemma last_two_reads_fst : forall h, fst (last_two_reads h) <> -1.
Proof.
  intro; unfold last_two_reads.
  rewrite find_read0.
  destruct (find_read h) as [(?, ?)|] eqn: Hfind; simpl; [|discriminate].
  pose proof (find_read_pos _ _ _ Hfind).
  destruct (find_read (l ++ [AE 0 (-1)])) as [(?, ?)|]; auto.
Qed.

Lemma find_read_In : forall h b rest, find_read h = Some (b, rest) -> In (AE b (-1)) h.
Proof.
  induction h; simpl; intros; try discriminate.
  destruct a.
  destruct (eq_dec w (-1)); [|right; eapply IHh; eauto].
  destruct (eq_dec r (-1)); [right; eapply IHh; eauto|].
  inv H; auto.
Qed.

Corollary last_two_reads_In : forall h, In (AE (fst (last_two_reads h)) (-1)) (h ++ [AE 0 (-1)]).
Proof.
  unfold last_two_reads; intros.
  rewrite find_read0.
  destruct (find_read h) as [(?, ?)|] eqn: Hfind; simpl.
  - apply find_read_In in Hfind.
    destruct (find_read (l ++ [AE 0 (-1)])) as [(?, ?)|]; rewrite in_app; auto.
  - rewrite in_app; simpl; auto.
Qed.

Lemma repable_buf : forall a, -1 <= a < B -> repable_signed a.
Proof.
  intros ? (? & ?).
  split; [transitivity (-1) | transitivity B]; unfold B, N in *; try computable; auto; omega.
Qed.

Lemma body_start_read : semax_body Vprog Gprog f_start_read start_read_spec.
Proof.
  start_function.
  rewrite (data_at__isptr _ tint); Intros.
  assert_PROP (Zlength reads = N) by entailer!.
  assert (0 <= r < N) as Hr.
  { exploit (Znth_inbounds r reads Vundef); [|omega].
    intro Heq; rewrite Heq in *; contradiction. }
  forward.
  rewrite lock_inv_isptr; Intros.
  rewrite <- lock_struct_array.
  forward.
  forward.
  forward.
  set (c := Znth r comms Vundef).
  set (l := Znth r locks Vundef).
(*   (* Do P and Q need all the arguments? *) *)
  forward_call (Tsh, sh2, gsh1, gsh2, sh2, c, l, -1, -1, h,
    fun h b => !!(b = -1 /\ fst (last_two_reads h) = b0) &&
      (EX v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs Vundef)) * ghost_var gsh1 tint (vint b0) c,
    comm_R bufs sh gsh2 c, fun h b => !!(-1 <= b < B) &&
      (EX v : Z, data_at sh tbuffer (vint v) (Znth (if eq_dec b (-1) then b0 else b) bufs Vundef)) *
      ghost_var gsh1 tint (vint (fst (last_two_reads h))) c).
  { unfold comm_inv; entailer!.
    rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives; [|cancel].
    apply andp_right; auto.
    eapply derives_trans; [|apply precise_weak_precise]; auto.
    apply derives_precise' with (Q := data_at_ sh tbuffer (Znth (fst (last_two_reads h)) bufs Vundef) *
      EX v : val, ghost_var gsh1 tint v c); [|apply precise_sepcon; [auto |
      apply ghost_var_precise with (t := tint)]].
    clear; Exists (vint (fst (last_two_reads h))); entailer!. }
  { repeat (split; auto); try computable.
    unfold AE_spec, comm_R; intros.
    intros ???????? Ha.
    rewrite !last_two_reads_cons, prev_taken_cons in Ha.
    unfold last_write in *; simpl in *.
    pose proof (last_two_reads_fst hx).
    destruct (last_two_reads hx) as (b1', b2') eqn: Hlast.
    rewrite !sepcon_andp_prop', !sepcon_andp_prop.
    erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
    erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
    Intros; subst.
    rewrite sepcon_comm, <- !sepcon_assoc, 3sepcon_assoc.
    assert_PROP (b1' = fst (last_two_reads h)).
    { go_lowerx.
      do 2 apply sepcon_derives_prop.
      eapply derives_trans; [apply ghost_var_inj|].
      apply prop_left; intro; apply prop_right.
      apply repr_inj_signed; try congruence.
      + pose proof (last_two_reads_In hx) as Hin.
        rewrite in_app in Hin; destruct Hin as [Hin | [Hin | ?]]; [| inv Hin | contradiction].
        * match goal with H : Forall _ _ |- _ => rewrite Forall_forall in H; specialize (H _ Hin) end.
          rewrite Hlast in *; simpl in *; apply repable_buf; omega.
        * rewrite Hlast in *; simpl in *; subst; split; computable.
      + apply repable_buf; omega. }
    subst; erewrite ghost_var_share_join; eauto.
    rewrite flatten_sepcon_in_SEP.
    apply change_ghost_var with (v' := vint (if eq_dec vx (-1) then fst (last_two_reads h) else vx)).
    eapply semax_pre, Ha.
    go_lowerx.
    rewrite !sepcon_andp_prop', !sepcon_andp_prop, !sepcon_andp_prop'.
    apply andp_right.
    { apply prop_right; repeat split; try constructor; auto; omega. }
    apply andp_right; [apply prop_right; auto|].
    erewrite <- ghost_var_share_join; eauto.
    rewrite !eq_dec_refl in Ha.
    destruct (eq_dec vx (-1)).
    - replace (fst (last_two_reads hc)) with (fst (last_two_reads h)) by auto; cancel.
      apply andp_right; auto.
      eapply derives_trans; [|apply precise_weak_precise]; auto.
      apply precise_andp2; repeat apply precise_sepcon; auto.
      destruct (eq_dec b2' (-1)); auto.
      apply derives_precise' with (Q := @data_at_ CompSpecs sh tbuffer (Znth b2' bufs Vundef)); auto.
      entailer!.
    - simpl in *; destruct (eq_dec (fst (last_two_reads h)) (-1)); [absurd (fst (last_two_reads h) = -1); auto|].
      subst; cancel.
      apply andp_right; auto.
      eapply derives_trans; [|apply precise_weak_precise]; auto.
      apply precise_andp2; repeat apply precise_sepcon; auto.
      eapply derives_precise' with (Q := @data_at_ CompSpecs sh tbuffer _); auto.
      entailer!. }
  Intros b.
  exploit repable_buf; eauto; intro.
  match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROP () (LOCALx (temp _t'2 (vint (if eq_dec b (-1) then 0 else 1)) :: Q) (SEPx R))) end.
  { forward.
    destruct (eq_dec b (-1)); [omega|].
    entailer!.
    simpl.
    rewrite add_repr.
    destruct (Int.lt (Int.repr b) (Int.repr (3 + 2))) eqn: Hlt; auto.
    apply lt_repr_false in Hlt; auto; unfold repable_signed; try computable.
    unfold B, N in *; omega. }
  { forward.
    destruct (eq_dec b (-1)); [|omega].
    entailer!. }
  forward_if (PROP () LOCAL (temp _b (vint (if eq_dec b (-1) then b0 else b)); temp _rr (Znth r reads Vundef);
      temp _r (vint r); gvar _reading reading; gvar _last_read last_read; gvar _lock lock; gvar _comm comm)
    SEP (lock_inv sh2 l (AE_inv c (-1) Tsh gsh2 (comm_R bufs sh gsh2 c));
         ghost gsh1 (-1) (sh2, AE b (-1) :: h) c;
         EX v : Z, data_at sh tbuffer (vint v) (Znth (if eq_dec b (-1) then b0 else b) bufs Vundef);
         ghost_var gsh1 tint (vint (fst (last_two_reads (AE b (-1) :: h)))) c;
         data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
         data_at_ Tsh tint (Znth r reads Vundef);
         data_at Tsh tint (vint (if eq_dec b (-1) then b0 else b)) (Znth r lasts Vundef);
         data_at sh1 (tarray (tptr tint) N) comms comm;
         data_at sh1 (tarray (tptr (Tstruct _lock_t noattr)) N) locks lock)).
  - forward.
    simpl eq_dec; destruct (eq_dec b (-1)); [match goal with H : _ <> _ |- _ => contradiction H; auto end|].
    entailer!.
  - forward.
    simpl eq_dec; destruct (eq_dec b (-1)); [|discriminate].
    entailer!.
  - forward.
    forward.
    Exists (if eq_dec b (-1) then fst (last_two_reads h) else b) b v.
    apply andp_right.
    { apply prop_right.
      split; [destruct (eq_dec b (-1)); auto; omega|].
      rewrite last_two_reads_cons, eq_dec_refl.
      destruct (eq_dec b (-1)); auto. }
    apply andp_right; [apply prop_right; auto|].
    unfold comm_inv; rewrite lock_struct_array; subst c l; cancel.
Qed.

Lemma body_finish_read : semax_body Vprog Gprog f_finish_read finish_read_spec.
Proof.
  start_function.
  rewrite (data_at__isptr _ tint); Intros.
  assert_PROP (Zlength reads = N) by entailer!.
  assert (0 <= r < N) as Hr.
  { exploit (Znth_inbounds r reads Vundef); [|omega].
    intro Heq; rewrite Heq in *; contradiction. }
  forward.
  forward.
  forward.
Qed.

Lemma body_initialize_writer : semax_body Vprog Gprog f_initialize_writer initialize_writer_spec.
Proof.
  start_function.
  forward.
  forward.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
   SEP (field_at Ews tint [] (eval_unop Oneg tint (vint 1)) writing; field_at Ews tint [] (vint 0) last_given;
        data_at Ews (tarray tint N) (repeat Empty (Z.to_nat i) ++ repeat Vundef (Z.to_nat (N - i))) last_taken)).
  { unfold N; computable. }
  { unfold N; computable. }
  { entailer!. }
  - forward.
    rewrite upd_init_const; auto.
    entailer!.
  - forward.
Qed.

Opaque upto.

Lemma body_start_write : semax_body Vprog Gprog f_start_write start_write_spec.
Proof.
  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound B (EX i : Z, PROP ( )
   LOCAL (lvar _available (tarray tint B) lvar0; gvar _writing writing; gvar _last_given last_given;
   gvar _last_taken last_taken)
   SEP (data_at Tsh (tarray tint B) (repeat (vint 1) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (B - i))) lvar0;
        data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
  { unfold B, N; computable. }
  { entailer!. }
  { forward.
    rewrite upd_init_const; auto; entailer!. }
  rewrite Zminus_diag, app_nil_r.
  forward.
  forward.
  rewrite <- seq_assoc.
  assert_PROP (Zlength lasts = N).
  { gather_SEP 3.
    go_lowerx.
    apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold N; omega|].
    apply prop_left; intros (? & ? & ?).
    unfold unfold_reptype in *; simpl in *.
    rewrite Zlength_map in *; apply prop_right; auto. }
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (temp _i (vint B); lvar _available (tarray tint B) lvar0; 
   gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
   SEP (field_at Tsh (tarray tint B) [] (map (fun x => vint (if eq_dec x b0 then 0
     else if in_dec eq_dec x (sublist 0 i lasts) then 0 else 1)) (upto (Z.to_nat B))) lvar0;
   data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
   data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
  { unfold N; computable. }
  { unfold N; computable. }
  { entailer!.
    rewrite upd_Znth_eq with (d := Vundef); simpl; [|Omega0].
    unfold Znth; simpl.
    apply derives_refl'; f_equal.
    apply map_ext_in; intros ? Hin.
    rewrite In_upto in Hin.
    destruct (eq_dec a b0); auto.
    destruct (zlt a 0); [omega|].
    destruct Hin as (? & Hin); apply Z2Nat.inj_lt in Hin; auto; try omega.
    simpl in *; destruct (Z.to_nat a); auto.
    repeat (destruct n0; [solve [auto]|]).
    omega. }
  { assert (0 <= i < Zlength lasts) by omega.
    forward.
    { entailer!.
      apply Forall_Znth.
      { rewrite Zlength_map in *; omega. }
      rewrite Forall_forall; intros ? Hin.
      rewrite in_map_iff in Hin; destruct Hin as (? & ? & ?); subst; simpl; auto. }
    rewrite Znth_map with (d' := -1); auto.
    forward_if (PROP ( )
      LOCAL (temp _last (vint (Znth i lasts (-1))); temp _r (vint i); temp _i (vint B); lvar _available (tarray tint 5) lvar0; 
             gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint B) [] (map (fun x => vint (if eq_dec x b0 then 0
             else if in_dec eq_dec x (sublist 0 (i + 1) lasts) then 0 else 1)) (upto (Z.to_nat B))) lvar0;
           data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
           data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    - assert (0 <= Znth i lasts (-1) < B).
      { exploit (Forall_Znth(A := Z)); eauto.
        instantiate (1 := -1); intro.
        destruct (eq_dec (Znth i lasts (-1)) (-1)); [|unfold B, N in *; simpl in *; omega].
        match goal with H : Int.repr _ <> Int.neg _ |- _ => contradiction H; rewrite e; auto end. }
      forward.
      entailer!.
      rewrite upd_Znth_eq with (d := Vundef); auto.
      apply derives_refl'; erewrite map_ext_in; [reflexivity|].
      intros; rewrite In_upto, map_length, upto_length in *; simpl in *.
      erewrite Znth_map, Znth_upto; simpl; auto; try omega.
      erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1 with (d := -1); auto; try omega.
      destruct (in_dec eq_dec a (sublist 0 i lasts ++ [Znth i lasts (-1)])); rewrite in_app in *.
      + destruct (eq_dec a (Znth i lasts (-1))); destruct (eq_dec a b0); auto.
        destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        destruct i0 as [? | [? | ?]]; subst; try contradiction.
        contradiction n; auto.
      + destruct (eq_dec a (Znth i lasts (-1))).
        { subst; contradiction n; simpl; auto. }
        destruct (eq_dec a b0); auto.
        destruct (in_dec eq_dec a (sublist 0 i lasts)); auto; contradiction n; auto.
    - forward.
      entailer!.
      apply derives_refl'; erewrite map_ext_in; [reflexivity|].
      intros; rewrite In_upto in *; simpl in *.
      destruct (eq_dec a b0); auto.
      erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1 with (d := -1); auto; try omega.
      match goal with H : Int.repr _ = Int.neg _ |- _ => apply repr_inj_signed in H end.
      destruct (in_dec eq_dec a (sublist 0 i lasts ++ [Znth i lasts (-1)])); rewrite in_app in *.
      + destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        destruct i0 as [? | [? | ?]]; subst; try contradiction.
        rewrite Int.unsigned_repr in *; try computable; omega.
      + destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        contradiction n0; auto.
      + apply Forall_Znth; auto.
        eapply Forall_impl; [|eauto]; unfold repable_signed; intros.
        split; [transitivity (-1) | transitivity B]; unfold B, N in *; try computable; try omega.
      + unfold repable_signed; computable.
    - intros.
      unfold exit_tycon, overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert; entailer!. }
  rewrite sublist_same; auto.
  set (available := map (fun x => vint (if eq_dec x b0 then 0 else if in_dec eq_dec x lasts then 0 else 1))
         (upto (Z.to_nat B))).
  rewrite <- seq_assoc.
  unfold Sfor.
  forward.
  eapply semax_seq, semax_ff.
  eapply semax_pre with (P' := EX i : Z, PROP (0 <= i <= B; forall j, j < i -> Znth j available (vint 0) = vint 0)
    LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) lvar0; gvar _writing writing;
           gvar _last_given last_given; gvar _last_taken last_taken)
    SEP (field_at Tsh (tarray tint 5) [] available lvar0; data_at_ Ews tint writing;
         data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken)).
  { Exists 0; entailer!.
    intros; apply Znth_underflow; auto. }
  eapply semax_loop.
  + Intros i.
    assert (repable_signed i).
    { split; [transitivity 0 | transitivity B]; unfold B, N in *; try computable; try omega. }
    forward_if (PROP (i < B)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) lvar0; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint 5) [] available lvar0; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given;
           data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    { forward.
      entailer!. }
    { forward.
      exploit (list_pigeonhole (b0 :: lasts) B).
      { rewrite Zlength_cons; unfold B; omega. }
      intros (j & ? & Hout); exploit (H3 j); [unfold B, N in *; omega|].
      subst available.
      rewrite Znth_map with (d' := B); [|rewrite Zlength_upto; auto].
      rewrite Znth_upto; [|rewrite Z2Nat.id; omega].
      destruct (eq_dec j b0); [contradiction Hout; simpl; auto|].
      destruct (in_dec eq_dec j lasts); [contradiction Hout; simpl; auto|].
      discriminate. }
    Intros.
    forward.
    { entailer!.
      apply Forall_Znth; [rewrite Zlength_map, Zlength_upto; unfold B, N in *; simpl; omega|].
      rewrite Forall_forall; intros ? Hin.
      rewrite in_map_iff in Hin; destruct Hin as (? & ? & ?); subst; simpl; auto. }
    { unfold B, N in *; apply prop_right; omega. }
    erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; try assumption; try omega.
    forward_if (PROP (Znth i available (vint 0) = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint B) lvar0; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint B) [] available lvar0; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    { forward.
      forward.
      Exists lvar0 i; entailer!.
      { destruct (eq_dec i b0); [|destruct (in_dec eq_dec i lasts)]; auto;
          match goal with H : Int.repr 0 <> Int.zero |- _ => contradiction H; auto end. }
      unfold data_at_, field_at_; entailer!. }
    { forward.
      entailer!.
      subst available.
      erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; try assumption; try omega.
      destruct (eq_dec _ _); auto.
      destruct (in_dec _ _ _); auto; discriminate. }
    intros.
    unfold exit_tycon, overridePost.
    destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
    Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert.
    instantiate (1 := EX i : Z, PROP (0 <= i < B; Znth i available (vint 0) = vint 0;
      forall j : Z, j < i -> Znth j available (vint 0) = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint B) lvar0; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint B) [] available lvar0; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    Exists i; entailer!.
  + Intros i.
    forward.
    Exists (i + 1); entailer!.
    intros; destruct (eq_dec j i); subst; auto.
    assert (j < i) by omega; auto.
Qed.

Lemma make_shares_out : forall b lasts shs
  (Hb : ~In b lasts) (Hlen : Zlength lasts = Zlength shs), make_shares shs lasts b = shs.
Proof.
  induction lasts; auto; simpl; intros.
  { rewrite Zlength_nil in *; destruct shs; auto; rewrite Zlength_cons, Zlength_correct in *; omega. }
  destruct (eq_dec a b); [contradiction Hb; auto|].
  destruct shs; rewrite !Zlength_cons in *; [rewrite Zlength_nil, Zlength_correct in *; omega|].
  simpl; rewrite IHlasts; auto; omega.
Qed.

Lemma find_write_rest : forall h b rest, find_write h = Some (b, rest) -> exists n, rest = skipn n h.
Proof.
  induction h; simpl; intros; try discriminate.
  destruct a.
  destruct (eq_dec w (-1)).
  - destruct (IHh _ _ H) as (n & ?); subst.
    exists (S n); auto.
  - inv H; exists 1%nat; auto.
Qed.

Corollary prev_taken_In : forall h, prev_taken h = -1 \/ prev_taken h = 0 \/ In (AE (prev_taken h) (-1)) h.
Proof.
  intros; unfold prev_taken.
  destruct (find_write h) as [(?, ?)|] eqn: Hfind; auto.
  apply find_write_rest in Hfind; destruct Hfind as (n & ?); subst.
  destruct (find_read (skipn n h)) as [(?, ?)|] eqn: Hfind; auto.
  pose proof (find_read_In _ _ _ Hfind).
  right; right; eapply skipn_In; eauto.
Qed.

Lemma write_val : forall w h rest v (Hw : find_write h = Some (w, rest))
  (Hh : apply_hist (-1) h = Some v), v = w \/ v = -1.
Proof.
  induction h; [discriminate|]; simpl; intros.
  destruct a.
  destruct (apply_hist (-1) h) eqn: Hh'; [|discriminate].
  destruct (eq_dec z r); inv Hh.
  destruct (eq_dec v (-1)); auto.
  inv Hw; auto.
Qed.

Lemma find_write_read : forall w h rest (Hw : find_write h = Some (w, rest))
  (Hread : apply_hist (-1) h = Some (-1)),
  exists rest', find_read h = Some (w, rest').
Proof.
  induction h; [discriminate|]; simpl; intros.
  destruct a.
  destruct (apply_hist (-1) h) eqn: Hh; [|discriminate].
  destruct (eq_dec z r); [subst | discriminate].
  inv Hread.
  rewrite eq_dec_refl; rewrite eq_dec_refl in Hw.
  destruct (eq_dec r (-1)); eauto.
  exploit write_val; eauto; intros [? | ?]; subst; eauto; contradiction n; auto.
Qed.

Lemma take_read : forall h v, apply_hist (-1) h = Some v ->
  prev_taken h = if eq_dec v (-1) then snd (last_two_reads h)
                 else fst (last_two_reads h).
Proof.
  induction h; simpl; intros.
  - inv H.
    rewrite eq_dec_refl; auto.
  - destruct a; rewrite prev_taken_cons, last_two_reads_cons.
    destruct (apply_hist (-1) h) eqn: Hh; [|discriminate].
    destruct (eq_dec z r); [subst | discriminate].
    inv H.
    erewrite IHh; eauto.
    destruct (eq_dec v (-1)).
    + destruct (eq_dec r (-1)); auto.
    + unfold last_two_reads; rewrite find_read0.
      destruct (find_read h) as [(?, ?)|]; auto.
      destruct (find_read (l ++ [AE 0 (-1)])) as [(?, ?)|]; auto.
Qed.

Lemma find_write_In : forall h b rest, find_write h = Some (b, rest) -> exists r, In (AE r b) h.
Proof.
  induction h; simpl; intros; try discriminate.
  destruct a.
  destruct (eq_dec w (-1)); [exploit IHh; eauto; intros (? & ?); eauto|].
  inv H; eauto.
Qed.

Lemma make_shares_app : forall i l1 l2 shs, Zlength l1 + Zlength l2 <= Zlength shs ->
  make_shares shs (l1 ++ l2) i =
  make_shares shs l1 i ++ make_shares (sublist (Zlength l1) (Zlength shs) shs) l2 i.
Proof.
  induction l1; simpl; intros.
  - rewrite sublist_same; auto.
  - rewrite Zlength_cons in *.
    destruct shs.
    { rewrite Zlength_nil, !Zlength_correct in *; omega. }
    rewrite Zlength_cons in *; simpl; rewrite IHl1; [|omega].
    rewrite sublist_S_cons with (i0 := Z.succ _); [|rewrite Zlength_correct; omega].
    unfold Z.succ; rewrite !Z.add_simpl_r.
    destruct (eq_dec a i); auto.
Qed.

Lemma make_shares_ext : forall i d l l' shs (Hlen : Zlength l = Zlength l')
  (Hi : forall j, 0 <= j < Zlength l -> Znth j l d = i <-> Znth j l' d = i),
  make_shares shs l i = make_shares shs l' i.
Proof.
  induction l; destruct l'; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; auto;
    try (rewrite Zlength_correct in *; omega).
  exploit (Hi 0); [rewrite Zlength_correct; omega|].
  rewrite !Znth_0_cons; intro Hiff.
  rewrite (IHl l'); try omega.
  - destruct (eq_dec a i), (eq_dec z i); tauto.
  - intros; exploit (Hi (j + 1)); [omega|].
    rewrite !Znth_pos_cons, !Z.add_simpl_r; auto; omega.
Qed.

Lemma find_read_write : forall h v, apply_hist (-1) h = Some v -> find_write h = None -> find_read h = None.
Proof.
  induction h; auto; simpl; intros.
  destruct a.
  destruct (apply_hist (-1) h) eqn: Hh; [|discriminate].
  destruct (eq_dec z r); [inv H | discriminate].
  destruct (eq_dec v (-1)); [|discriminate].
  destruct (eq_dec r (-1)); eauto.
  destruct h; [inv Hh; contradiction n; auto | simpl in *].
  destruct h.
  destruct (eq_dec w (-1)); [|discriminate].
  destruct (apply_hist (-1) h0); [|discriminate].
  destruct (eq_dec z r0); [|discriminate].
  inv Hh; omega.
Qed.

Fixpoint make_shares_inv shs (lasts : list Z) i {struct lasts} : list share :=
  match lasts with
  | [] => []
  | b :: rest => if eq_dec b i then hd Share.bot shs :: make_shares_inv (tl shs) rest i
                 else make_shares_inv (tl shs) rest i
  end.

Lemma make_shares_minus : forall i lasts sh0 shs sh' sh1 (Hsh' : sepalg_list.list_join sh0 shs sh')
  (Hsh1 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh1)
  (Hlen : Zlength shs = Zlength lasts),
  sepalg_list.list_join sh1 (make_shares_inv shs lasts i) sh'.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *;
    try (rewrite Zlength_correct in *; omega).
  - inv Hsh1; inv Hsh'; constructor.
  - inversion Hsh' as [|????? Hj1 Hj2]; subst.
    destruct (eq_dec a i).
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (x & ? & Hx).
      exploit IHlasts; eauto; [omega|].
      intro Hj'; destruct (sepalg_list.list_join_assoc2 Hj' Hx) as (? & ? & ?).
      econstructor; eauto.
    + inversion Hsh1 as [|????? Hja]; inversion Hsh' as [|????? Hjb]; subst.
      pose proof (sepalg.join_eq Hja Hjb); subst.
      eapply IHlasts; eauto; omega.
Qed.

Lemma make_shares_add : forall i i' d lasts j shs (Hj : 0 <= j < Zlength lasts)
  (Hi : Znth j lasts d = i) (Hi' : i' <> i) (Hlen : Zlength shs >= Zlength lasts),
  exists shs1 shs2, make_shares shs lasts i = shs1 ++ shs2 /\
    make_shares shs (upd_Znth j lasts i') i = shs1 ++ Znth j shs Tsh :: shs2.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; try omega.
  destruct (eq_dec j 0).
  - subst; rewrite Znth_0_cons in Hi', IHlasts; rewrite !Znth_0_cons.
    rewrite eq_dec_refl, upd_Znth0, Zlength_cons, sublist_1_cons, sublist_same; auto; try omega; simpl.
    destruct (eq_dec i' a); [contradiction Hi'; auto|].
    eexists [], _; simpl; split; eauto.
  - rewrite Znth_pos_cons in Hi; [|omega].
    rewrite Znth_pos_cons; [|omega].
    exploit (IHlasts (j - 1) shs); try omega.
    intros (shs1 & shs2 & Heq1 & Heq2).
    rewrite upd_Znth_cons; [simpl | omega].
    exists (if eq_dec a i then shs1 else t :: shs1), shs2; rewrite Heq1, Heq2; destruct (eq_dec a i); auto.
Qed.

Lemma make_shares_In : forall i lasts x shs (Hx : 0 <= x < Zlength lasts) (Hi : Znth x lasts 0 <> i)
  (Hlen : Zlength shs >= Zlength lasts),
  In (Znth x shs Tsh) (make_shares shs lasts i).
Proof.
  induction lasts; simpl; intros.
  - rewrite Zlength_nil in *; omega.
  - destruct shs; rewrite !Zlength_cons in *; [rewrite Zlength_nil, Zlength_correct in *; omega|].
    destruct (eq_dec x 0).
    + subst; rewrite Znth_0_cons in Hi; rewrite Znth_0_cons.
      destruct (eq_dec a i); [contradiction Hi | simpl]; auto.
    + rewrite Znth_pos_cons in Hi; [|omega].
      rewrite Znth_pos_cons; [|omega].
      exploit (IHlasts (x - 1) shs); eauto; try omega.
      destruct (eq_dec a i); simpl; auto.
Qed.

Lemma make_shares_inv_In : forall i lasts x shs (Hx : 0 <= x < Zlength lasts) (Hi : Znth x lasts 0 = i)
  (Hlen : Zlength shs >= Zlength lasts),
  In (Znth x shs Tsh) (make_shares_inv shs lasts i).
Proof.
  induction lasts; simpl; intros.
  - rewrite Zlength_nil in *; omega.
  - destruct shs; rewrite !Zlength_cons in *; [rewrite Zlength_nil, Zlength_correct in *; omega|].
    destruct (eq_dec x 0).
    + subst; rewrite Znth_0_cons in *; rewrite Znth_0_cons; subst.
      rewrite eq_dec_refl; simpl; auto.
    + rewrite Znth_pos_cons in Hi; [|omega].
      rewrite Znth_pos_cons; [|omega].
      exploit (IHlasts (x - 1) shs); eauto; try omega.
      destruct (eq_dec a i); simpl; auto.
Qed.

Lemma make_shares_sub : forall i lasts shs sh0 sh1 sh2 (Hlen : Zlength shs >= Zlength lasts)
  (Hsh1 : sepalg_list.list_join sh0 shs sh1) (Hsh2 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh2),
  sepalg.join_sub sh2 sh1.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite Zlength_correct in *; omega).
  - inv Hsh1; inv Hsh2; apply sepalg.join_sub_refl.
  - inversion Hsh1 as [|????? Hj1 Hj2]; inv Hsh2.
    destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?); eexists; eauto.
  - inversion Hsh1 as [|????? Hj1 Hj2]; subst.
    destruct (eq_dec a i).
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
      exploit IHlasts; eauto; [omega|].
      intro; eapply sepalg.join_sub_trans; eauto; eexists; eauto.
    + inversion Hsh2 as [|????? Hj1']; subst.
      pose proof (sepalg.join_eq Hj1 Hj1'); subst.
      eapply IHlasts; eauto; omega.
Qed.

Lemma make_shares_join : forall i d lasts shs sh0 j sh1 sh2 (Hlen : Zlength shs >= Zlength lasts)
  (Hsh1 : sepalg_list.list_join sh0 shs sh1) (Hsh2 : sepalg_list.list_join sh0 (make_shares shs lasts i) sh2)
  (Hin : 0 <= j < Zlength shs) (Hj : Znth j lasts d = i), exists sh', sepalg.join sh2 (Znth j shs Tsh) sh'.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite Zlength_correct in *; omega); try omega.
  { rewrite Znth_overflow in Hj; [|rewrite Zlength_nil; omega].
    inv Hsh2.
    exploit (Znth_In j (t :: shs) Tsh); [rewrite Zlength_cons; auto|].
    intro Hin'; apply in_split in Hin'.
    destruct Hin' as (? & ? & Heq); rewrite Heq in Hsh1.
    apply list_join_comm in Hsh1; inv Hsh1; eauto. }
  destruct (eq_dec j 0).
  - subst j; rewrite Znth_0_cons in Hj; rewrite Znth_0_cons; subst.
    rewrite eq_dec_refl in Hsh2.
    inversion Hsh1 as [|????? Hj1 Hj2]; subst.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
    exploit make_shares_sub; eauto; [omega|].
    intro; eapply sepalg.join_sub_joins_trans; eauto.
  - rewrite Znth_pos_cons in Hj; [|omega].
    rewrite Znth_pos_cons; [|omega].
    inversion Hsh1 as [|????? Hj1 Hj2].
    destruct (eq_dec a i); subst.
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
      eapply IHlasts; eauto; omega.
    + inversion Hsh2 as [|????? Hj1']; subst.
      pose proof (sepalg.join_eq Hj1 Hj1'); subst.
      eapply IHlasts; eauto; omega.
Qed.

Lemma upd_write_shares : forall bufs b b0 lasts shs sh0 (Hb : 0 <= b < B) (Hb0 : 0 <= b0 < B)
  (Hlasts : Forall (fun x : Z => -1 <= x < B) lasts) (Hshs : Zlength shs = N)
  (Hread0 : readable_share sh0) (Hread : Forall readable_share shs) (Hsh0 : sepalg_list.list_join sh0 shs Tsh)
  (Hdiff : b <> b0) (Hout : ~ In b lasts) (Hout0 : ~ In b0 lasts) (Hlasts : Zlength lasts = N)
  bsh' v' (Hv' : -1 <= v' < B) h' (Hh' : 0 <= Zlength h' < N)
  (Hbsh' : sepalg_list.list_join sh0 (sublist (Zlength h' + 1) N shs) bsh')
  bsh (Hbsh : sepalg.join bsh' (Znth (Zlength h') shs Tsh) bsh),
  (if eq_dec v' (-1) then if eq_dec (Znth (Zlength h') lasts 0) (-1) then emp else
   EX v0 : Z, data_at (Znth (Zlength h') shs Tsh) tbuffer (vint v0) (Znth (Znth (Zlength h') lasts 0) bufs Vundef)
   else !! (v' = b0) && (EX v'0 : Z, data_at (Znth (Zlength h') shs Tsh) tbuffer (vint v'0) (Znth v' bufs Vundef))) *
  ((EX v0 : Z, data_at bsh' tbuffer (vint v0) (Znth b bufs Vundef)) *
  fold_right sepcon emp (upd_Znth b (map (fun a => EX sh : share, !! (if eq_dec a b0 then
    sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
      (map (fun i : Z => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) a) sh
      else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h') N shs) sh
      else sepalg_list.list_join sh0 (make_shares shs
      (map (fun i : Z => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N))) a) sh) &&
      (EX v0 : Z, data_at sh tbuffer (vint v0) (Znth a bufs Vundef))) (upto (Z.to_nat B))) emp))
  |-- fold_right sepcon emp (map (fun a => EX sh : share, !! (if eq_dec a b0 then
        sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h' + 1)
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [v']) 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) a) sh
          else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h' + 1) N shs) sh
          else sepalg_list.list_join sh0 (make_shares shs
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [v']) 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N))) a) sh) &&
          (EX v0 : Z, data_at sh tbuffer (vint v0) (Znth a bufs Vundef))) (upto (Z.to_nat B))).
Proof.
  intros; set (shi := Znth (Zlength h') shs Tsh).
  assert (readable_share shi).
  { apply Forall_Znth; auto; omega. }
  set (lasti := Znth (Zlength h') lasts 0).
  exploit (Znth_In (Zlength h') lasts 0); [omega | intro Hini].
  assert (lasti <> b) as Hneq.
  { intro; match goal with H : ~In b lasts |- _ => contradiction H end; subst b lasti; auto. }
  assert (lasti <> b0) as Hneq0.
  { intro; match goal with H : ~In b0 lasts |- _ => contradiction H end; subst b0 lasti; auto. }
  set (l0 := upd_Znth b (map (fun a => EX sh : share, !!(if eq_dec a b0 then
             sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
               (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) a) sh
           else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h') N shs) sh
           else sepalg_list.list_join sh0 (make_shares shs (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0
                                           else Znth i lasts 0) (upto (Z.to_nat N))) a) sh) &&
          (EX v1 : Z, @data_at CompSpecs sh tbuffer (vint v1) (Znth a bufs Vundef))) (upto (Z.to_nat B)))
          (EX v1 : Z, @data_at CompSpecs bsh' tbuffer (vint v1) (Znth b bufs Vundef))).
  assert (Zlength l0 = B).
  { subst l0; rewrite upd_Znth_Zlength; rewrite Zlength_map, Zlength_upto; auto. }
  assert (lasti <> -1 -> 0 <= lasti < B).
  { intro; rewrite Forall_forall in Hlasts; specialize (Hlasts _ Hini); subst lasti; omega. }
  apply derives_trans with (fold_right sepcon emp (
    if eq_dec v' (-1) then if eq_dec lasti (-1) then l0 else upd_Znth lasti l0
            (EX sh : share, !!(exists sh', sepalg_list.list_join sh0 (make_shares shs
             (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N))) lasti) sh' /\
             sepalg.join sh' shi sh) &&
            (EX v1 : Z, @data_at CompSpecs sh tbuffer (vint v1) (Znth lasti bufs Vundef)))
          else upd_Znth b0 l0 (EX sh : share, !!(exists sh', sepalg_list.list_join sh0 (make_shares shs
            (sublist 0 (Zlength h') (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0)
            (upto (Z.to_nat N)))) b0) sh' /\ sepalg.join sh' shi sh) &&
            (EX v1 : Z, @data_at CompSpecs sh tbuffer (vint v1) (Znth b0 bufs Vundef))))).
  { rewrite replace_nth_sepcon.
    destruct (eq_dec v' (-1)).
    - destruct (eq_dec lasti (-1)); [rewrite emp_sepcon; auto|].
      rewrite extract_nth_sepcon with (i := lasti); [|subst l0; omega].
      erewrite upd_Znth_diff, Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; try omega.
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      Intros v1 ish v2.
      eapply derives_trans; [apply sepcon_derives; [apply data_at_value_cohere; auto | apply derives_refl]|].
      { eapply readable_share_list_join; eauto. }
      assert (exists sh', sepalg.join ish shi sh') as (sh' & ?).
      { eapply make_shares_join; eauto.
        + setoid_rewrite Hshs; rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega.
        + setoid_rewrite Hshs; auto.
        + rewrite Znth_map', Znth_upto; [|rewrite Z2Nat.id; omega].
          rewrite Znth_overflow; auto; omega. }
      erewrite data_at_share_join; [|eapply sepalg.join_comm; eauto].
      rewrite (extract_nth_sepcon (upd_Znth lasti l0 (EX sh : share, _)) lasti); [|rewrite upd_Znth_Zlength; omega].
      rewrite upd_Znth_twice; [|omega].
      apply sepcon_derives; [|apply derives_refl].
      rewrite upd_Znth_same; [|omega].
      Exists sh'; apply andp_right; [|Exists v1; auto].
      apply prop_right; eauto.
    - Intros; subst.
      rewrite extract_nth_sepcon with (i := b0); [|subst l0; omega].
      erewrite upd_Znth_diff, Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; try omega.
      destruct (eq_dec b0 b0); [|contradiction n0; auto].
      Intros v1 ish v2.
      eapply derives_trans; [apply sepcon_derives; [apply data_at_value_cohere; auto | apply derives_refl]|].
      { eapply readable_share_list_join; eauto. }
      assert (exists sh', sepalg.join ish shi sh') as (sh' & ?).
      { eapply make_shares_join; eauto.
        + setoid_rewrite Hshs; rewrite Zlength_sublist; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; omega.
        + setoid_rewrite Hshs; auto.
        + rewrite Znth_overflow; auto.
          rewrite Zlength_sublist; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; omega. }
      erewrite data_at_share_join; [|eapply sepalg.join_comm; eauto].
      rewrite (extract_nth_sepcon (upd_Znth b0 l0 (EX sh : share, _)) b0); [|rewrite upd_Znth_Zlength; omega].
      rewrite upd_Znth_twice; [|omega].
      apply sepcon_derives; [|apply derives_refl].
      rewrite upd_Znth_same; [|omega].
      Exists sh'; apply andp_right; [|Exists v1; auto].
      apply prop_right; eauto. }
  apply derives_refl'; f_equal.
  match goal with |- ?l = _ => assert (Zlength l = B) as Hlen end.
  { destruct (eq_dec v' (-1)); [destruct (eq_dec lasti (-1))|]; auto; rewrite upd_Znth_Zlength; auto; omega. }
  apply list_Znth_eq' with (d := FF).
  { rewrite Hlen, Zlength_map, Zlength_upto; auto. }
  rewrite Hlen; intros.
  assert (0 <= j <= B) by omega.
  erewrite Znth_map, Znth_upto; auto.
  destruct (eq_dec j lasti); [|destruct (eq_dec j b0)]; subst.
  - destruct (eq_dec v' (-1)).
    destruct (eq_dec lasti (-1)); [omega|].
    + rewrite upd_Znth_same; [|omega].
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      exploit (make_shares_add lasti b0 0 (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0
        else Znth i lasts 0) (upto (Z.to_nat N))) (Zlength h') shs); auto.
      { erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; try omega.
        rewrite Znth_overflow; [|omega].
        destruct (eq_dec 0 (-1)); [discriminate | auto]. }
      { setoid_rewrite Hshs; rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
      simpl; intros (shsa & shsb & Hshs1 & Hshs2).
      f_equal; extensionality; f_equal; f_equal.
      rewrite Hshs1.
      erewrite make_shares_ext, Hshs2.
      apply prop_ext; split.
      * intros (? & Hj1 & Hj2).
        apply list_join_comm.
        apply sepalg.join_comm in Hj2; destruct (sepalg_list.list_join_assoc2 Hj1 Hj2) as (? & ? & ?).
        econstructor; eauto.
        apply list_join_comm; auto.
      * intro Hj; apply list_join_comm in Hj.
        inversion Hj as [|????? Hj1 Hj2]; subst.
        apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
        do 2 eexists; eauto; apply list_join_comm; auto.
      * rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto.
      * rewrite Zlength_map, Zlength_upto; intros.
        rewrite Znth_map', Znth_upto; [|omega].
        destruct (zlt j (Zlength h')); [|destruct (eq_dec j (Zlength h'))].
        -- rewrite app_Znth1, upd_Znth_diff; auto; try omega.
           erewrite Znth_map, Znth_upto; auto; [reflexivity | omega].
        -- subst; rewrite Znth_app1, eq_dec_refl, upd_Znth_same; auto; reflexivity.
        -- rewrite Znth_overflow, upd_Znth_diff; auto; [|rewrite Zlength_app, Zlength_cons, Zlength_nil; omega].
           erewrite Znth_map, Znth_upto; auto; [|omega].
           rewrite Znth_overflow with (al := h'); [reflexivity | omega].
    + subst l0; rewrite 2upd_Znth_diff; auto; try omega.
      erewrite Znth_map, Znth_upto; try assumption.
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      simpl; erewrite make_shares_ext; eauto.
      rewrite Zlength_map, Zlength_upto; intros.
      erewrite Znth_map', Znth_map, !Znth_upto; auto; try omega.
      destruct (zlt j (Zlength h')); [|destruct (eq_dec j (Zlength h'))].
      * rewrite app_Znth1; auto; omega.
      * subst; rewrite Znth_overflow, Znth_app1; auto.
        destruct (eq_dec 0 (-1)); [discriminate|].
        destruct (eq_dec v' (-1)); [contradiction n; auto | reflexivity].
      * rewrite Znth_overflow, Znth_overflow with (al := h' ++ [v']); auto; [reflexivity|].
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
  - assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i h' 0) (-1) then b0
      else Znth i lasts 0) (upto (Z.to_nat N)))) = Zlength h') as Hlenh.
    { rewrite Zlength_sublist; try omega.
      rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
    assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i (h' ++ [v']) 0) (-1) then b0
      else Znth i lasts 0) (upto (Z.to_nat N)))) = Zlength h') as Hlenh'.
    { rewrite Zlength_sublist; try omega.
      rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
    simpl in *.
    destruct (eq_dec v' (-1)).
    + assert (EX sh : share, !! sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
          (map (fun i : Z => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) b0)
          sh && (EX v1 : Z, data_at sh tbuffer (vint v1) (Znth b0 bufs Vundef)) =
        EX sh : share, !! sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h' + 1)
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [v']) 0) (-1) then b0 else Znth i lasts 0)
          (upto (Z.to_nat N)))) b0) sh && (EX v0 : Z, data_at sh tbuffer (vint v0) (Znth b0 bufs Vundef))).
      { erewrite sublist_split with (mid := Zlength h')(hi := Zlength h' + 1), sublist_len_1, Znth_map', Znth_upto;
          auto; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; try omega.
        rewrite Znth_app1; auto.
        subst; rewrite eq_dec_refl, make_shares_app; simpl.
        rewrite eq_dec_refl, app_nil_r.
        erewrite make_shares_ext; eauto; [omega|].
        rewrite Hlenh; intros; erewrite !Znth_sublist, Znth_map', Znth_map, !Znth_upto; auto;
          rewrite ?Zlength_upto; simpl; try (unfold N in *; omega).
        rewrite app_Znth1; [reflexivity | omega].
        { setoid_rewrite Hshs; rewrite Hlenh', Zlength_cons, Zlength_nil; omega. } }
      destruct (eq_dec lasti (-1)); subst l0; [rewrite upd_Znth_diff | rewrite 2upd_Znth_diff]; auto; try omega;
        erewrite Znth_map, Znth_upto; auto; destruct (eq_dec b0 b0); auto; absurd (b0 = b0); auto.
    + rewrite upd_Znth_same; [|omega].
      erewrite sublist_split with (mid := Zlength h')(hi := Zlength h' + 1), sublist_len_1, Znth_map', Znth_upto;
        auto; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; simpl; try (unfold N in *; omega).
      rewrite Znth_app1; auto.
      destruct (eq_dec v' (-1)); [contradiction n0; auto|].
      rewrite make_shares_app; simpl.
      destruct (eq_dec _ b0); [contradiction n; auto|].
      rewrite hd_Znth, Znth_sublist; rewrite ?Hlenh'; try setoid_rewrite Hshs; try omega.
      f_equal; extensionality; f_equal; f_equal.
      erewrite make_shares_ext.
      apply prop_ext; split.
      * intros (? & Hj1 & Hj2).
        apply sepalg.join_comm in Hj2; destruct (sepalg_list.list_join_assoc2 Hj1 Hj2) as (? & ? & ?).
        apply list_join_comm; econstructor; eauto.
        erewrite Znth_indep; eauto.
        setoid_rewrite Hshs; auto.
      * intro Hj; apply list_join_comm in Hj; inversion Hj as [|????? Hj1 Hj2]; subst.
        apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
        do 2 eexists; eauto.
        subst shi; erewrite Znth_indep; eauto.
        setoid_rewrite Hshs; auto.
      * omega.
      * rewrite Hlenh; intros; erewrite !Znth_sublist, Znth_map', Znth_map, !Znth_upto;
          rewrite ?Zlength_upto; simpl; try (unfold N in *; omega).
        rewrite app_Znth1; [reflexivity | omega].
      * rewrite Hlenh', Zlength_cons, Zlength_nil; setoid_rewrite Hshs; omega.
  - transitivity (Znth j l0 FF).
    { destruct (eq_dec v' (-1)); [|rewrite upd_Znth_diff; auto; omega].
      destruct (eq_dec lasti (-1)); [|rewrite upd_Znth_diff]; auto; omega. }
    subst l0.
    destruct (eq_dec j b).
    + subst; rewrite upd_Znth_same; auto.
      apply mpred_ext'; intros ? HP.
      * exists bsh'; split; auto.
      * destruct HP as (x & HshP & ?).
        assert (x = bsh') by (eapply list_join_eq; eauto; apply HshP).
        subst; auto.
    + rewrite upd_Znth_diff; auto.
      erewrite Znth_map, Znth_upto; auto.
      destruct (eq_dec j b0); [contradiction n0; auto|].
      destruct (eq_dec j b); [contradiction n1; auto|].
      simpl; erewrite make_shares_ext; eauto.
      rewrite Zlength_map, Zlength_upto; intros.
      erewrite Znth_map', Znth_map, !Znth_upto; auto; try omega.
      destruct (zlt j0 (Zlength h')); [|destruct (eq_dec j0 (Zlength h'))].
      * rewrite app_Znth1; auto; omega.
      * subst; rewrite Znth_overflow, Znth_app1; auto.
        destruct (eq_dec 0 (-1)); [discriminate|].
        destruct (eq_dec v' (-1)); [|reflexivity].
        split; intro; subst; tauto.
      * rewrite Znth_overflow, Znth_overflow with (al := h' ++ [v']); auto; [reflexivity|].
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
Qed.

Lemma body_finish_write : semax_body Vprog Gprog f_finish_write finish_write_spec.
Proof.
  start_function.
  forward.
  forward.
  assert_PROP (Zlength (map (fun i => vint i) lasts) = N) by entailer!.
  rewrite Zlength_map in *.
  rewrite <- seq_assoc.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (temp _w (vint b); temp _last (vint b0); gvar _writing writing; gvar _last_given last_given;
          gvar _last_taken last_taken; gvar _comm comm; gvar _lock lock)
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
        fold_right sepcon emp (map (fun r => lock_inv lsh (Znth r locks Vundef)
          (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2)) (upto (Z.to_nat N)));
        EX h' : list Z, !!(Zlength h' = i) && fold_right sepcon emp (map
          (fun x : val * hist => let '(c, h0) := x in ghost gsh1 (-1) (lsh, h0) c)
          (combine comms (extend (map (fun v => AE v b) h') h))) *
          let lasts' := map (fun i => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0)
                            (upto (Z.to_nat N)) in
            data_at Ews (tarray tint N) (map (fun i => vint i) lasts') last_taken *
            fold_right sepcon emp (map (fun r =>
              ghost_var gsh1 tint (vint (if zlt r i then b else b0)) (offset_val 1 (Znth r comms Vundef)) *
              ghost_var gsh1 tint (vint (Znth r lasts' (-1))) (offset_val 2 (Znth r comms Vundef))) (upto (Z.to_nat N))) *
            fold_right sepcon emp (map (fun a => EX sh : share,
              !!(if eq_dec a b0 then sepalg_list.list_join sh0 (make_shares shs (sublist 0 i lasts') a) sh
                 else if eq_dec a b then sepalg_list.list_join sh0 (sublist i N shs) sh
                 else sepalg_list.list_join sh0 (make_shares shs lasts' a) sh) &&
              EX v : Z, @data_at CompSpecs sh tbuffer (vint v) (Znth a bufs Vundef)) (upto (Z.to_nat B))))).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists (@nil Z).
    replace (map (fun i => if eq_dec (Znth i [] 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))
      with lasts.
    entailer!.
    apply derives_refl'; f_equal; f_equal.
    apply map_ext; intro.
    f_equal; extensionality; f_equal; f_equal.
    apply prop_ext.
    destruct (eq_dec a b0); [|destruct (eq_dec a b); [|reflexivity]].
    - split; intro Hx; [subst; constructor | inv Hx; auto].
    - subst; rewrite sublist_same, make_shares_out; auto; try reflexivity.
      replace (Zlength lasts) with N; auto.
    - rewrite (list_Znth_eq 0 lasts) at 1.
      replace (length lasts) with (Z.to_nat N).
      apply map_ext.
      intro; rewrite Znth_nil; destruct (eq_dec 0 (-1)); auto; discriminate.
      { rewrite Zlength_correct in *; Omega0. } }
  - assert_PROP (Zlength comms = N) as Hcomms by entailer!.
    forward.
    { entailer!.
      apply Forall_Znth.
      { rewrite Hcomms; auto. }
      apply Forall_impl with (P := isptr); auto. }
    rewrite <- lock_struct_array.
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
      [|rewrite Zlength_map; auto].
    rewrite Znth_map with (d' := N); [|rewrite Zlength_upto; auto].
    rewrite Znth_upto; [|rewrite Z2Nat.id; auto; omega].
    rewrite lock_inv_isptr; Intros.
    forward.
    Intros h'.
    assert (Zlength comms = Zlength (extend (map (fun v0 : Z => AE v0 b) h') h)).
    { rewrite Zlength_extend; omega. }
    assert (Zlength (combine comms (extend (map (fun v => AE v b) h') h)) = N) as Hlens.
    { rewrite Zlength_combine, Z.min_l; auto; omega. }
    rewrite <- Hlens in *.
    rewrite (extract_nth_sepcon (map _ (combine comms _)) i); [|rewrite Zlength_map; auto].
    rewrite Znth_map with (d' := (Vundef, [])), Znth_combine; auto.
    rewrite Znth_extend_ge; [|rewrite Zlength_map; omega].
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat B))) b); [|rewrite Zlength_map, Zlength_upto; auto].
    rewrite Znth_map with (d' := B), Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; auto; try omega.
    Intros bsh.
    destruct (eq_dec b b0); [absurd (b = b0); auto|].
    match goal with H : if eq_dec b b then _ else _ |- _ => rewrite eq_dec_refl in H end.
    rewrite Hlens in *.
    match goal with H : sepalg_list.list_join _ (sublist i N shs) _ |- _ =>
      rewrite sublist_split with (mid := i + 1) in H; try omega;
      apply list_join_comm, sepalg_list.list_join_unapp in H; destruct H as (bsh' & ? & Hsh) end.
    rewrite sublist_len_1 with (d := Tsh), <- sepalg_list.list_join_1 in Hsh; [|omega].
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i); [|rewrite Zlength_map; auto].
    erewrite !Znth_map; rewrite ?Znth_upto; rewrite ?Znth_upto, ?Zlength_upto; rewrite ?Z2Nat.id; auto; try omega.
    rewrite Znth_overflow with (al := h'); [|omega].
    destruct (eq_dec 0 (-1)); [discriminate|].
    destruct (zlt i i); [clear - l; omega|].
    forward_call (Tsh, lsh, gsh1, gsh2, lsh, Znth i comms Vundef, Znth i locks Vundef, -1, b, Znth i h [],
      fun (h : hist) (v : Z) => !!(v = b) &&
        ghost_var gsh1 tint (vint b0) (offset_val 1 (Znth i comms Vundef)) *
        ghost_var gsh1 tint (vint (Znth i lasts 0)) (offset_val 2 (Znth i comms Vundef)) *
        EX v : Z, data_at (Znth i shs Tsh) tbuffer (vint v) (Znth b bufs Vundef),
      comm_R bufs (Znth i shs Tsh) gsh2 (Znth i comms Vundef), fun (h : hist) (v : Z) => !!(-1 <= v < B) &&
        ghost_var gsh1 tint (vint b) (offset_val 1 (Znth i comms Vundef)) *
        ghost_var gsh1 tint (vint (if eq_dec v (-1) then b0 else Znth i lasts 0))
          (offset_val 2 (Znth i comms Vundef)) *
        if eq_dec v (-1) then if eq_dec (Znth i lasts 0) (-1) then emp
          else EX v : Z, data_at (Znth i shs Tsh) tbuffer (vint v) (Znth (Znth i lasts 0) bufs Vundef)
        else !!(v = b0) && EX v' : Z, data_at (Znth i shs Tsh) tbuffer (vint v') (Znth v bufs Vundef)).
    { unfold comm_inv.
      Intro v0; Exists v0.
      rewrite <- (data_at_share_join _ _ _ _ _ _ Hsh).
      (* entailer! is slow *)
      rewrite true_eq, TT_andp; auto; cancel.
      subst Frame; instantiate (1 := [_ * _ * _ * _ * _ * _ * _ * _ *
        (EX v0 : Z, data_at bsh' tbuffer (vint v0) (Znth b bufs Vundef)) * _]).
      rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives; [|simpl; rewrite sepcon_emp;
        repeat (apply sepcon_derives; try apply derives_refl); Exists v0; auto].
      apply andp_right; auto.
      eapply derives_trans; [|apply precise_weak_precise]; auto.
      eapply derives_precise' with (Q := _ * data_at_ (Znth i shs Tsh) tbuffer (Znth b bufs Vundef));
        [apply sepcon_derives; [apply derives_refl|] | repeat apply precise_sepcon; auto].
      clear; entailer!. }
    { repeat (split; auto).
      { transitivity 0; try computable; omega. }
      { transitivity B; unfold B, N in *; try computable; omega. }
      unfold AE_spec, comm_R; intros.
      intros ???????? Ha.
      rewrite last_two_reads_cons, prev_taken_cons in Ha.
      rewrite !sepcon_andp_prop', !sepcon_andp_prop.
      erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
      erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
      Intros.
      destruct (eq_dec vc (-1)); [omega|].
      destruct (last_two_reads hx) as (b1, b2) eqn: Hlast.
      apply semax_pre with (P' := PROPx P (LOCALx Q (SEPx (
        (ghost_var gsh1 tint (vint b0) (offset_val 1 (Znth i comms Vundef)) *
         ghost_var gsh2 tint (vint (last_write hx)) (offset_val 1 (Znth i comms Vundef))) ::
        (ghost_var gsh1 tint (vint (Znth i lasts 0)) (offset_val 2 (Znth i comms Vundef)) *
         ghost_var gsh2 tint (vint (prev_taken hx)) (offset_val 2 (Znth i comms Vundef))) ::
        (ghost_var gsh2 tint (vint b1) (Znth i comms Vundef) *
         (if eq_dec vx (-1) then if eq_dec b2 (-1) then emp
          else EX v1 : Z, @data_at CompSpecs (Znth i shs Tsh) tbuffer (vint v1) (Znth b2 bufs Vundef)
          else EX v1 : Z, @data_at CompSpecs (Znth i shs Tsh) tbuffer (vint v1) (Znth vx bufs Vundef)) *
         (EX v1 : Z, @data_at CompSpecs (Znth i shs Tsh) tbuffer (vint v1) (Znth b bufs Vundef))) :: R)))).
      { go_lowerx; cancel. }
      assert_PROP (b0 = last_write hx).
      { go_lowerx; apply sepcon_derives_prop.
        eapply derives_trans; [apply ghost_var_inj|].
        apply prop_left; intro; apply prop_right.
        apply repr_inj_signed; try congruence.
        + apply repable_buf; omega.
        + unfold last_write.
          destruct (find_write hx) as [(?, ?)|] eqn: Hfind; [|split; computable].
          apply find_write_In in Hfind; destruct Hfind as (? & Hin).
          match goal with H : Forall _ _ |- _ => rewrite Forall_forall in H; specialize (H _ Hin) end.
          simpl in *; apply repable_buf; tauto. }
      assert_PROP (prev_taken hx = Znth i lasts 0) as Hprev.
      { go_lowerx.
        rewrite <- sepcon_assoc, (sepcon_comm (_ * _) (_ * ghost_var _ _ _ _)).
        do 2 apply sepcon_derives_prop.
        eapply derives_trans; [apply ghost_var_inj|].
        apply prop_left; intro; apply prop_right.
        apply repr_inj_signed; try congruence.
        + destruct (prev_taken_In hx) as [Hin | [Hin | Hin]]; try (rewrite Hin; split; computable).
          match goal with H : Forall _ _ |- _ => rewrite Forall_forall in H; specialize (H _ Hin) end.
          simpl in *; apply repable_buf; omega.
        + apply Forall_Znth; [omega|].
          eapply Forall_impl; [|eauto]; intros.
          apply repable_buf; auto. }
      subst; rewrite <- Hprev in *.
      erewrite !ghost_var_share_join; eauto.
      apply change_ghost_var with (v' := vint b).
      rewrite <- flatten_sepcon_in_SEP, sepcon_comm, flatten_sepcon_in_SEP.
      apply change_ghost_var with (v' := vint (if eq_dec vx (-1) then last_write hx else prev_taken hx)).
      rewrite <- !(ghost_var_share_join _ _ _ _ _ _ SH3).
      eapply semax_pre, Ha.
      go_lowerx.
      rewrite !sepcon_andp_prop', !sepcon_andp_prop, !sepcon_andp_prop'.
      apply andp_right; [apply prop_right; repeat split; try constructor; auto; omega|].
      apply andp_right; [apply prop_right; auto|].
      erewrite take_read, Hlast; eauto; simpl.
      unfold last_write in *; simpl in *.
      destruct (eq_dec vx (-1)); subst; cancel.
      + destruct (eq_dec b (-1)); [contradiction n1; auto | cancel].
        rewrite <- sepcon_emp at 1; apply sepcon_derives.
        destruct (find_write hx) as [(?, ?)|] eqn: Hwrite.
        * exploit find_write_read; eauto; intros (? & Hread); rewrite Hread; auto.
        * eapply find_read_write in Hwrite; eauto.
          rewrite Hwrite; auto.
        * apply andp_right; auto.
          eapply derives_trans; [|apply precise_weak_precise]; auto.
          apply precise_andp2; repeat apply precise_sepcon; auto.
          apply derives_precise' with
            (Q := @data_at_ CompSpecs (Znth (Zlength h') shs Tsh) tbuffer (Znth b bufs Vundef)); auto.
          clear; entailer!.
      + assert (exists rest, find_write hx = Some (vx, rest)) as (? & Hwrite).
        { destruct hx; simpl in *.
          { match goal with H : Some (-1) = Some vx |- _ => inv H; contradiction n2; auto end. }
          destruct h0.
          destruct (apply_hist (-1) hx) eqn: Hh'; [|discriminate].
          destruct (eq_dec z r); [match goal with H : Some _ = Some vx |- _ => inv H end | discriminate].
          destruct(eq_dec vx (-1)); [contradiction n2; auto | eauto]. }
        rewrite Hwrite in *.
        destruct (eq_dec b (-1)); [contradiction n1; auto|].
        rewrite !sepcon_andp_prop; apply andp_right; [apply prop_right; auto | cancel].
        rewrite <- sepcon_emp at 1; apply sepcon_derives.
        * unfold last_two_reads in Hlast; rewrite find_read0 in Hlast.
          destruct (find_read hx) as [(?, ?)|]; [|inv Hlast; auto].
          destruct (find_read (l ++ [AE 0 (-1)])) as [(?, ?)|]; inv Hlast; auto.
        * apply andp_right; auto.
          eapply derives_trans; [|apply precise_weak_precise]; auto.
          apply precise_andp2; repeat apply precise_sepcon; auto.
          apply derives_precise' with
            (Q := @data_at_ CompSpecs (Znth (Zlength h') shs Tsh) tbuffer (Znth b bufs Vundef)); auto.
          clear; entailer!. }
    Intros v'.
    gather_SEP 0 9; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      lock_inv lsh (Znth r locks Vundef) (AE_inv (Znth r comms Vundef) (-1) Tsh gsh2
        (comm_R bufs (Znth r shs Tsh) gsh2 (Znth r comms Vundef)))) (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto _)) i);
        [cancel | rewrite Zlength_map, Zlength_upto; unfold N in *; auto].
      rewrite Znth_map with (d' := N), Znth_upto; rewrite ?Zlength_upto; unfold N in *; simpl; auto; omega. }
    gather_SEP 1 9; replace_SEP 0 (fold_right sepcon emp (map (fun x => let '(c, h0) := x in
      ghost gsh1 (-1) (lsh, h0) c) (combine comms (extend (map (fun v1 : Z => AE v1 b) (h' ++ [v'])) h)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (combine _ _)) i);
        [|rewrite Zlength_map, Zlength_combine, Zlength_extend, Z.min_l; omega].
      assert (Zlength comms = Zlength (extend (map (fun v0 => AE v0 b) (h' ++ [v'])) h)).
      { rewrite Zlength_extend; omega. }
      assert (Zlength (combine comms (extend (map (fun v => AE v b) (h' ++ [v'])) h)) = N) as Hlens'.
      { rewrite Zlength_combine, Z.min_l; auto; omega. }
      rewrite <- Hlens' in *.
      rewrite Znth_map with (d' := (Vundef, [])), Znth_combine; auto.
      erewrite Znth_extend_in; rewrite ?Zlength_map, ?Zlength_app, ?Zlength_cons, ?Zlength_nil; try omega.
      rewrite Znth_map'.
      instantiate (1 := 0).
      subst; rewrite app_Znth2, Zminus_diag, Znth_0_cons; [cancel | omega].
      apply derives_refl'; f_equal.
      unfold upd_Znth; f_equal; rewrite !sublist_map, !sublist_combine, !sublist_extend.
      + rewrite map_app, sublist_app1; rewrite ?Zlength_map; auto; omega.
      + rewrite !Zlength_map, !Hlens, !Hlens'.
        rewrite !sublist_over with (l := map _ _); auto;
          rewrite Zlength_map, ?Zlength_app, ?Zlength_cons, ?Zlength_nil; omega. }
    gather_SEP 2 3 10; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      ghost_var gsh1 tint (vint (if zlt r (i + 1) then b else b0)) (offset_val 1 (Znth r comms Vundef)) *
      ghost_var gsh1 tint (vint (Znth r (map (fun i0 => if eq_dec (Znth i0 (h' ++ [v']) 0) (-1) then b0
        else Znth i0 lasts 0) (upto (Z.to_nat N))) (-1))) (offset_val 2 (Znth r comms Vundef))) 
      (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
        [|rewrite Zlength_map, Zlength_upto; auto].
      erewrite Znth_map, Znth_upto, Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; simpl; auto;
        try (unfold N in *; auto; omega).
      destruct (zlt i (i + 1)); [|clear - g0; omega].
      subst; rewrite app_Znth2, Zminus_diag, Znth_0_cons; [cancel | omega].
      apply derives_refl'; f_equal.
      unfold upd_Znth; f_equal; rewrite !sublist_map.
      + apply map_ext_in; intros ? Hin.
        apply In_sublist_upto in Hin; try omega.
        clear - Hin; destruct Hin as ((? & ?) & ?).
        erewrite !Znth_map, !Znth_upto; rewrite ?Zlength_upto; try (split; auto; omega).
        destruct (zlt a (Zlength h')); [|omega].
        destruct (zlt a (Zlength h' + 1)); [|omega].
        rewrite app_Znth1; auto.
      + f_equal; apply map_ext_in; intros ? Hin.
        apply In_sublist_upto in Hin; try omega.
        rewrite Zlength_map, Zlength_upto in Hin.
        destruct Hin as ((? & ?) & _).
        erewrite !Znth_map, !Znth_upto; rewrite ?Zlength_upto; try (split; auto; omega).
        destruct (zlt a (Zlength h')); [omega|].
        destruct (zlt a (Zlength h' + 1)); [omega|].
        rewrite Znth_overflow with (al := h'), Znth_overflow with (al := h' ++ [v']);
          rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; auto. }
    assert (repable_signed v').
    { split; [transitivity (-1) | transitivity B]; unfold B, N in *; try computable; omega. }
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx (?p0 :: ?p1 :: ?p2 :: ?p3 :: ?p4 :: ?p5 :: ?p6 :: ?p7 ::
      data_at _ _ ?l last_taken :: ?R2)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx (p0 :: p1 :: p2 :: p3 :: p4 :: p5 :: p6 :: p7 ::
        data_at Ews (tarray tint N) (upd_Znth i l (vint (if eq_dec v' (-1) then b0 else Znth i lasts 0))) last_taken :: R2)))) end.
    + forward.
      match goal with H : Int.repr v' = _ |- _ => rewrite Int.neg_repr in H; apply repr_inj_signed in H end; subst;
        auto; [|split; try computable].
      destruct (eq_dec (- (1)) (-1)); [|contradiction n1; auto].
      apply drop_tc_environ.
    + forward.
      destruct (eq_dec v' (-1)); [subst; absurd (Int.repr (-1) = Int.neg (Int.repr 1)); auto|].
      erewrite upd_Znth_triv with (i0 := i).
      apply drop_tc_environ.
      * rewrite !Zlength_map, Zlength_upto; auto.
      * rewrite !Znth_map', Znth_upto; [|simpl; unfold N in *; omega].
        rewrite Znth_overflow; [|omega].
        destruct (eq_dec 0 (-1)); [discriminate | auto].
    + intros.
      unfold exit_tycon, overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert.
      do 2 (apply andp_right; [apply prop_right; auto|]).
      Exists (h' ++ [v']).
      go_lower.
      repeat (apply andp_right; [apply prop_right; repeat split; auto; omega|]).
      rewrite lock_struct_array; unfold comm_inv; cancel.
      rewrite !sepcon_andp_prop'.
      rewrite Zlength_app, Zlength_cons, Zlength_nil; apply andp_right;
        [apply prop_right; auto|].
      cancel.
      rewrite (sepcon_comm _ (data_at _ _ _ last_taken)), !sepcon_assoc; apply sepcon_derives.
      * apply derives_refl'; f_equal.
        erewrite upd_Znth_eq, !map_length, upto_length, !map_map;
          [|rewrite !Zlength_map, Zlength_upto; unfold N in *; auto].
        apply map_ext_in; intros; rewrite In_upto in *.
        destruct (eq_dec a (Zlength h')).
        -- subst; rewrite app_Znth2, Zminus_diag, Znth_0_cons; auto; clear; omega.
        -- rewrite Znth_map', Znth_upto; [|omega].
           destruct (zlt a (Zlength h')); [rewrite app_Znth1 | rewrite Znth_overflow]; auto.
           rewrite Znth_overflow with (al := _ ++ _); auto.
           rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
      * eapply upd_write_shares; eauto.
  - Intros h'.
    forward.
    forward.
    forward.
    rewrite sublist_nil, sublist_same; rewrite ?Zlength_map; auto.
    Exists (map (fun i => if eq_dec (Znth i h' 0) (-1) then b0 else Znth i lasts 0) (upto (Z.to_nat N)))
      (extend (map (fun v => AE v b) h') h); entailer!.
    + repeat split.
      * rewrite Forall_map, Forall_forall; intros; simpl.
        destruct (eq_dec (Znth x h' 0) (-1)); [omega|].
        rewrite In_upto, Z2Nat.id in *; unfold N; try omega.
        apply Forall_Znth; [omega | auto].
      * assert (Zlength h' = Zlength h) as Hlen by omega; clear - Hlen; revert dependent h; induction h';
          destruct h; rewrite ?Zlength_nil, ?Zlength_cons in *; simpl; intros; auto; try omega.
        { rewrite Zlength_correct in *; omega. }
        constructor; eauto.
        apply IHh'; omega.
      * rewrite in_map_iff; intros (i & ? & ?); subst.
        rewrite In_upto, Z2Nat.id in *; try (unfold N; omega).
        destruct (eq_dec (Znth i h' 0) (-1)); [absurd (b0 = b0); auto|].
        match goal with H : ~In _ lasts |- _ => contradiction H; apply Znth_In; omega end.
    + apply derives_refl'; f_equal; f_equal.
      apply map_ext; intro.
      f_equal; extensionality; f_equal; f_equal; apply prop_ext.
      destruct (eq_dec a b).
      * destruct (eq_dec a b0); [absurd (b = b0); subst; auto|].
        split; intro Hx; [inv Hx; auto | subst; constructor].
      * destruct (eq_dec a b0); reflexivity.
Qed.

Ltac load_tac' :=
 ensure_normal_ret_assert;
 hoist_later_in_pre;
 match goal with   
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
 (* Super canonical load *)
    let e1 := fresh "e" in
    let efs := fresh "efs" in
    let tts := fresh "tts" in
      construct_nested_efield e e1 efs tts;

    let lr := fresh "lr" in
      pose (compute_lr e1 efs) as lr;
      vm_compute in lr;

    let HLE := fresh "HLE" in
    let p := fresh "p" in evar (p: val);
      match goal with
      | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
      | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
      end;

    let H_Denote := fresh "H_Denote" in
    let gfsB := fresh "gfsB" in
      solve_efield_denote Delta P Q R efs gfsB H_Denote;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs0" in evar (gfs0: list gfield);
    let gfsA := fresh "gfsA" in evar (gfsA: list gfield);
    let a := fresh "a" in evar (a: val);
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let n := fresh "n" in
    let Hf := fresh "Hf" in
    let eqL := constr:(p = field_address t_root gfsA a) in
    let eqR := constr:(p = a /\ gfsA = nil) in
    let g := constr:((ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !! eqL) \/ eqR) in
    let HNice := fresh "HNice" in

    tryif (
      tryif (
        assert g as HNice by (
          subst p gfsA gfsB a t_root;
          left;
          (eassumption || (apply prop_right; (eassumption || reflexivity)))
        )
      ) then (
        (sc_new_instantiate P Q R R Delta e1 gfsA gfsB tts lr a sh t_root gfs0 v n (0%nat) Hf
         || fail 15 "sc_new_instantiate should really not have failed" )
      ) else (
        instantiate (gfsA := nil); instantiate (a := p);
        (* will fail if these instantiations were a bad idea: *)
        sc_new_instantiate P Q R R Delta e1 gfsA gfsB tts lr a sh t_root gfs0 v n (0%nat) Hf;
        (assert g as HNice by (
          subst p gfsA gfsB a t_root;
          right;
          split; reflexivity
        ) || fail 15 "assert should really not have failed" )
      )
    ) then (
      let len := fresh "len" in
      pose ((length (gfsB ++ gfsA) - length gfs0)%nat) as len;
      simpl in len;
      let gfs1 := fresh "gfs1" in
      match goal with
      | len := ?len' |- _ => pose (gfs1 := (firstn len' (gfsB ++ gfsA)));
                             cbv [app gfsB gfsA firstn] in gfs1
      end;

      let gfsEq := fresh "gfsEq" in
      assert (gfsB ++ gfsA = gfs1 ++ gfs0) as gfsEq by reflexivity;

      let Heq := fresh "Heq" in
      match type of Hf with
      | (?R0 = _) => assert (nth_error R n = Some R0) as Heq by reflexivity
      end;

      refine (semax_SC_field_load_general' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
         _  _ _ lr _ _ _ HLE H_Denote HNice Heq _ gfsEq _ _ _ _ _); try reflexivity;
      [ auto (* readable_share *)
      | simpl_reptype.solve_load_rule_evaluation
      | clear HLE H_Denote;
        subst lr e1 gfs0 gfs1 gfsA gfsB efs tts t_root a v n(*;
        entailer_for_load_tac;
        subst p sh; clear Hf HNice gfsEq Heq*)
      | subst lr e1 gfs0 gfs1 gfsA gfsB efs tts t_root a v n;
        solve_legal_nested_field_in_entailment; try clear HLE H_Denote;
        subst p sh; clear Hf HNice gfsEq Heq ]
    ) else (
      assert (undo_and_first__assert_PROP eqL); subst t_root gfsA gfsB a p
    )
end.

Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  start_function.
  rewrite (data_at_isptr _ tint); Intros.
  replace_SEP 0 (data_at Tsh tint (vint r) (force_val (sem_cast_neutral arg))).
  { rewrite sem_cast_neutral_ptr; auto; go_lowerx; cancel. }
  forward.
  forward_call (r, reading, last_read, reads, lasts, sh1).
  eapply semax_seq'; [|apply semax_ff].
  set (c := Znth r comms Vundef).
  set (l := Znth r locks Vundef).
  eapply semax_pre with (P' := EX b0 : Z, EX h : hist, PROP (0 <= b0 < B; fst (last_two_reads h) = b0)
    LOCAL (temp _r (vint r); temp _arg arg; gvar _reading reading; gvar _last_read last_read; 
           gvar _lock lock; gvar _comm comm; gvar _bufs buf)
    SEP (data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
         data_at Tsh tint Empty (Znth r reads Vundef); data_at Tsh tint (vint b0) (Znth r lasts Vundef);
         data_at Tsh tint (vint r) (force_val (sem_cast_neutral arg)); malloc_token Tsh (sizeof tint) arg;
         data_at sh1 (tarray (tptr tint) N) comms comm;
         data_at sh1 (tarray (tptr tlock) N) locks lock;
         data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
         lock_inv sh2 l (comm_inv c bufs sh gsh2);
         EX v : Z, @data_at CompSpecs sh tbuffer (vint v) (Znth b0 bufs Vundef);
         ghost gsh1 (-1) (sh2, h) c; ghost_var gsh1 tint (vint b0) c)).
  { Exists 0 ([] : hist); entailer!. }
  eapply semax_loop; [|forward; apply drop_tc_environ].
  forward.
  Intros b0 h.
  subst c l; subst; forward_call (r, reading, last_read, lock, comm, reads, lasts, locks, comms, bufs,
    sh, sh1, sh2, fst (last_two_reads h), gsh1, gsh2, h).
  { repeat (split; auto). }
  Intros x; destruct x as ((b, e), v); simpl in *.
  rewrite (data_at_isptr _ tbuffer); Intros.
  (* !!forward runs forever here because entailer! runs forever on typechecking. *)
  eapply semax_seq'; [load_tac'; go_lower; entailer' | fwd_result; abbreviate_semax].
  forward.
  forward_call (r, reading, reads, sh1).
  go_lower.
  Exists b (AE e (-1) :: h) v; entailer'; cancel.
Qed.

Ltac store_tac' := 
ensure_open_normal_ret_assert;
hoist_later_in_pre;
match goal with
| |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e ?e2) _ =>
  (* Super canonical field store *)
    let e1 := fresh "e" in
    let efs := fresh "efs" in
    let tts := fresh "tts" in
      construct_nested_efield e e1 efs tts;

    let lr := fresh "lr" in
      pose (compute_lr e1 efs) as lr;
      vm_compute in lr;

    let HLE := fresh "H" in
    let p := fresh "p" in evar (p: val);
      match goal with
      | lr := LLLL |- _ => do_compute_lvalue Delta P Q R e1 p HLE
      | lr := RRRR |- _ => do_compute_expr Delta P Q R e1 p HLE
      end;

    let HRE := fresh "H" in
    let v0 := fresh "v" in evar (v0: val);
      do_compute_expr Delta P Q R (Ecast e2 (typeof (nested_efield e1 efs tts))) v0 HRE;

    let H_Denote := fresh "H" in
    let gfs := fresh "gfs" in
      solve_efield_denote Delta P Q R efs gfs H_Denote;

    let sh := fresh "sh" in evar (sh: share);
    let t_root := fresh "t_root" in evar (t_root: type);
    let gfs0 := fresh "gfs" in evar (gfs0: list gfield);
    let gfsA := fresh "gfsA" in pose (gfsA := @nil gfield);
    let v := fresh "v" in evar (v: reptype (nested_field_type t_root gfs0));
    let n := fresh "n" in
    let H := fresh "H" in
    (* new way of invoking sc_new_instantiate even though we're still in old code here!! *)
    sc_new_instantiate P Q R R Delta e1 gfsA gfs tts lr p sh t_root gfs0 v n (0%nat) H;

    try (unify v (default_val (nested_field_type t_root gfs0));
          lazy beta iota zeta delta - [list_repeat Z.to_nat] in v);

    let gfs1 := fresh "gfs" in
    let len := fresh "len" in
    pose ((length gfs - length gfs0)%nat) as len;
    simpl in len;
    match goal with
    | len := ?len' |- _ =>
      pose (firstn len' gfs) as gfs1
    end;

    clear len;
    unfold gfs in gfs0, gfs1;
    simpl firstn in gfs1;
    simpl skipn in gfs0;

    change gfs with (gfs1 ++ gfs0) in *;
    subst gfs;

    eapply (semax_SC_field_store Delta sh n p)
      with (lr0 := lr) (t_root0 := t_root) (gfs2 := gfs0) (gfs3 := gfs1);
    subst p;
      [ reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | reflexivity
      | try unfold data_at; try unfold data_at_; try unfold field_at_;
        subst n; cbv beta iota zeta delta [nth_error]; reflexivity
      | exact HLE
      | exact HRE
      | exact H_Denote
      | solve [subst sh; auto] (* writable share *)
      | solve_store_rule_evaluation
      | subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n;
        pre_entailer;
        try quick_typecheck3; 
        clear HLE HRE H_Denote H;
        unfold tc_efield(*; entailer_for_store_tac;
        simpl app; simpl typeof*)
      | solve_legal_nested_field_in_entailment;
        subst e1 gfs0 gfs1 efs tts t_root sh v0 lr n;
        clear HLE HRE H_Denote H
     ]
end.

Lemma body_writer : semax_body Vprog Gprog f_writer writer_spec.
Proof.
  start_function.
  forward_call (writing, last_given, last_taken).
  forward.
  eapply semax_seq'; [|apply semax_ff].
  eapply semax_pre with (P' := EX v : Z, EX b0 : Z, EX lasts : list Z, EX h : list hist,
   PROP (0 <= b0 < B; Forall (fun x => -1 <= x < B) lasts; Zlength h = N; ~In b0 lasts)
   LOCAL (temp _v (vint v); temp _arg arg; gvar _writing writing; gvar _last_given last_given;
   gvar _last_taken last_taken; gvar _lock lock; gvar _comm comm; gvar _bufs buf)
   SEP (data_at Ews tint Empty writing; data_at Ews tint (vint b0) last_given;
   data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken;
   data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
   data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
   fold_right sepcon emp (map (fun r0 => lock_inv lsh (Znth r0 locks Vundef)
     (comm_inv (Znth r0 comms Vundef) bufs (Znth r0 shs Tsh) gsh2)) (upto (Z.to_nat N)));
   fold_right sepcon emp (map (fun x => let '(c, h) := x in ghost gsh1 (-1) (lsh, h) c) (combine comms h));
   fold_right sepcon emp (map (fun r0 => ghost_var gsh1 tint (vint b0) (offset_val 1 (Znth r0 comms Vundef)) *
     ghost_var gsh1 tint (vint (Znth r0 lasts (-1))) (offset_val 2 (Znth r0 comms Vundef))) (upto (Z.to_nat N)));
   fold_right sepcon emp (map (fun i => EX sh : share, !! (if eq_dec i b0 then sh = sh0
     else sepalg_list.list_join sh0 (make_shares shs lasts i) sh) &&
     (EX v : Z, @data_at CompSpecs sh tbuffer (vint v) (Znth i bufs Vundef))) (upto (Z.to_nat B))))).
  { Exists 0 0 (repeat (-1) (Z.to_nat N)) (repeat ([] : hist) (Z.to_nat N)); entailer!.
    - split; [repeat constructor; computable | omega].
    - apply derives_refl'.
      f_equal; [f_equal|].
      + setoid_rewrite combine_const1 with (n := Z.to_nat N).
        rewrite map_map; auto.
        { match goal with H : Zlength comms = _ |- _ => setoid_rewrite H end.
          rewrite Z2Nat.id, Z.max_r; unfold N; omega. }
      + rewrite list_Znth_eq with (l := comms) at 1.
        replace (length comms) with (Z.to_nat N) by (apply Nat2Z.inj; rewrite <- Zlength_correct; auto).
        erewrite map_map, map_ext_in; eauto.
        intros; rewrite In_upto in *.
        match goal with |- context[Znth a ?l (-1)] => replace (Znth a l (-1)) with (-1); auto end.
        apply Forall_Znth; [Omega0|].
        repeat constructor; auto.
      + erewrite map_ext_in; eauto.
        intros; rewrite In_upto in *.
        destruct (eq_dec a 0); auto.
        generalize (make_shares_out a (repeat (-1) (Z.to_nat N)) shs); simpl; intro Heq; rewrite Heq; auto;
          [|omega].
        f_equal; extensionality; f_equal; f_equal.
        apply prop_ext; split; intro X; subst; auto.
        eapply list_join_eq; eauto. }
  eapply semax_loop; [|forward; apply drop_tc_environ].
  Intros v b0 lasts h.
  forward.
  forward_call (gsh1, writing, last_given, last_taken, b0, lasts).
  Intros b.
  rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat B))) b); [|rewrite Zlength_map; auto].
  erewrite Znth_map, Znth_upto; auto; rewrite ?Z2Nat.id; try omega.
  Intros sh v0.
  rewrite (data_at_isptr _ tbuffer); Intros.
  (* !! forward runs forever here because entailer! runs forever on typechecking. *)
  eapply semax_seq'; [load_tac'; go_lower; entailer' | fwd_result; abbreviate_semax].
  destruct (eq_dec b b0); [absurd (b = b0); auto|].
  assert_PROP (Zlength lasts = N).
  { gather_SEP 2; go_lowerx; apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts|].
    apply prop_left; intros (_ & ? & _); apply prop_right.
    unfold unfold_reptype in *; simpl in *.
    rewrite Zlength_map in *; auto. }
  rewrite make_shares_out in *; auto; [|setoid_rewrite H; auto].
  assert (sh = Tsh) by (eapply list_join_eq; eauto); subst.
  eapply semax_seq'; [store_tac'; go_lower; entailer' | fwd_result; abbreviate_semax].
  gather_SEP 9 10; replace_SEP 0 (fold_right sepcon emp (map (fun i => EX sh2 : share,
    !! (if eq_dec i b0 then sh2 = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts i) sh2) &&
    (EX v1 : Z, data_at sh2 tbuffer (vint v1) (Znth i bufs Vundef))) (upto (Z.to_nat B)))).
  { go_lowerx; eapply derives_trans with (Q := _ * _);
      [|erewrite replace_nth_sepcon, upd_Znth_triv; eauto].
    rewrite Znth_map', Znth_upto; [|simpl; unfold B, N in *; omega].
    destruct (eq_dec b b0); [absurd (b = b0); auto|].
    rewrite make_shares_out; auto; [|setoid_rewrite H; auto].
    Exists Tsh v; entailer'. }
  forward_call (writing, last_given, last_taken, comm, lock, comms, locks, bufs, b, b0, lasts,
    sh1, lsh, shs, gsh1, gsh2, h, sh0).
  { repeat (split; auto). }
  Intros x; destruct x as (lasts', h').
  forward.
  Exists (v + 1) b lasts' h'; entailer!.
  replace N with (Zlength h) by auto; symmetry; eapply mem_lemmas.Forall2_Zlength; eauto.
Qed.

Lemma interleave_remove_nil : forall {A} ls (l' : list A),
  interleave ([] :: ls) l' <-> interleave ls l'.
Proof.
  split; intro.
  - remember ([] :: ls) as l0; revert dependent ls; induction H; intros; subst.
    + inv Hnil; constructor; auto.
    + destruct (Z_le_dec i 0).
      { destruct (eq_dec i 0); [subst; rewrite Znth_0_cons in Hcons | rewrite Znth_underflow in Hcons];
          try discriminate; try omega. }
      rewrite Znth_pos_cons in Hcons; [econstructor; eauto | omega].
      apply IHinterleave.
      setoid_rewrite upd_Znth_app2 with (l1 := [[]]); auto.
      rewrite Zlength_cons, Zlength_nil.
      destruct (Z_le_dec (i - 1) (Zlength ls0)); [omega | rewrite Znth_overflow in Hcons; [discriminate | omega]].
  - induction H.
    + constructor; auto.
    + destruct (zlt i 0); [rewrite Znth_underflow in Hcons; [discriminate | auto]|].
      econstructor.
      * rewrite Znth_pos_cons, Z.add_simpl_r; eauto; omega.
      * setoid_rewrite upd_Znth_app2 with (l1 := [[]]); rewrite Zlength_cons, Zlength_nil.
        rewrite Z.add_simpl_r; auto.
        { destruct (Z_le_dec i (Zlength ls)); [omega | rewrite Znth_overflow in Hcons; [discriminate | omega]]. }
Qed.

Lemma interleave_single : forall {A} (l l' : list A), interleave [l] l' = (l' = l).
Proof.
  intros; apply prop_ext; split; intro; subst.
  - remember [l] as l0; revert dependent l; induction H; intros; subst.
    + inv Hnil; auto.
    + exploit (Znth_inbounds i [l0] []).
      { rewrite Hcons; discriminate. }
      intro; assert (i = 0) by (rewrite Zlength_cons, Zlength_nil in *; omega).
      subst; rewrite Znth_0_cons in Hcons; subst.
      rewrite upd_Znth0, sublist_nil in IHinterleave; specialize (IHinterleave _ eq_refl); subst; auto.
  - induction l; econstructor; auto.
    + instantiate (2 := 0); rewrite Znth_0_cons; eauto.
    + rewrite upd_Znth0, sublist_nil; auto.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  name buf _bufs.
  name lock _lock.
  name comm _comm.
  name reading _reading.
  name last_read _last_read.
  name last_taken _last_taken.
  name writing _writing.
  name last_given _last_given.
  start_function.
  exploit (split_readable_share Tsh); auto; intros (gsh1 & gsh2 & ? & ? & ?).
  exploit (split_shares (Z.to_nat N) Tsh); auto; intros (sh0 & shs & ? & ? & ? & ?).
  rewrite (data_at__eq _ (tarray (tptr (Tstruct _lock_t noattr)) N)), lock_struct_array.
  forward_call (comm, lock, buf, reading, last_read, gsh1, gsh2, sh0, shs).
  { unfold B, N, tbuffer, _buffer; simpl; cancel. }
  Intros x; destruct x as ((((comms, locks), bufs), reads), lasts).
  assert_PROP (Zlength comms = N) by entailer!.
  get_global_function'' _writer; Intros.
  apply extract_exists_pre; intros writer_.
  exploit (split_shares (Z.to_nat N) Ews); auto; intros (sh1 & shs1 & ? & ? & ? & ?).
  forward_spawn (val * val * val * val * val * val * list val * list val * list val *
                 share * share * share * list share * share * share)%type
    (writer_, vint 0, (writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, gsh1, sh0, shs, gsh1, gsh2),
    fun (x : (val * val * val * val * val * val * list val * list val * list val *
              share * share * share * list share * share * share)%type) (arg : val) =>
    let '(writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs, gsh1, gsh2) := x in
      fold_right sepcon emp [!!(fold_right and True [Zlength shs = N; readable_share sh1; readable_share lsh;
        readable_share sh0; Forall readable_share shs; sepalg_list.list_join sh0 shs Tsh;
        sepalg.join gsh1 gsh2 Tsh; Forall isptr comms]) && emp;
        data_at_ Ews tint writing; data_at_ Ews tint last_given; data_at_ Ews (tarray tint N) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
        fold_right sepcon emp (map (fun r =>
          lock_inv lsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost gsh1 (-1) (lsh, [])) comms);
        fold_right sepcon emp (map (fun c => ghost_var gsh1 tint (vint 0) (offset_val 1 c) *
          ghost_var gsh1 tint Empty (offset_val 2 c)) comms);
        fold_right sepcon emp (map (fun i => EX sh : share, !!(if eq_dec i 0 then sh = sh0 else sh = Tsh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B)))]).
  { apply andp_right.
    { entailer!. }
    unfold spawn_pre, PROPx, LOCALx, SEPx.
    go_lowerx.
    rewrite !sepcon_andp_prop, !sepcon_andp_prop'.
    apply andp_right; [apply prop_right; auto|].
    apply andp_right; [apply prop_right; repeat split; auto|].
    apply andp_right; [apply prop_right|].
    { unfold liftx; simpl; unfold lift, make_args'; simpl.
      rewrite eval_id_other, eval_id_same; auto; discriminate. }
    Exists _arg (fun x : (val * val * val * val * val * val * list val * list val * list val *
                 share * share * share * list share * share * share) =>
      let '(writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs, gsh1, gsh2) := x in
      [(_writing, writing); (_last_given, last_given); (_last_taken, last_taken);
       (_lock, lock); (_comm, comm); (_bufs, buf)]).
    rewrite !sepcon_assoc; apply sepcon_derives.
    { apply derives_refl'.
      f_equal; f_equal; extensionality; destruct x as (?, x); repeat destruct x as (x, ?); simpl.
      rewrite !sepcon_andp_prop'; extensionality.
      rewrite <- andp_assoc, prop_true_andp with (P := True); auto.
      rewrite (andp_comm (!! _) (!! _)), andp_assoc; f_equal; f_equal.
      rewrite emp_sepcon, !sepcon_emp; auto.
      * extensionality.
        clear; normalize. }
    rewrite sepcon_andp_prop'.
    apply andp_right; [apply prop_right; repeat (split; auto)|].
    erewrite map_ext; [|intro; erewrite <- lock_inv_share_join; try apply H1; auto; reflexivity].
    erewrite (map_ext (ghost gsh1 (-1) (Tsh, []))
      (fun x => ghost gsh1 (-1) (gsh1, []) x * ghost gsh1 (-1) (gsh2, []) x)).
    rewrite !sepcon_map.
    assert_PROP (Zlength bufs = B) by entailer!.
    do 3 (erewrite <- (data_at_shares_join Ews); eauto).
    rewrite (extract_nth_sepcon (map (data_at _ _ _) bufs) 0), Znth_map with (d' := Vundef);
      rewrite ?Zlength_map; try (unfold B, N in *; omega).
    erewrite <- (data_at_shares_join Tsh); eauto.
    rewrite (sepcon_comm (data_at sh0 _ _ _)), (sepcon_assoc _ (data_at sh0 _ _ _)), replace_nth_sepcon.
    unfold N; cancel.
    rewrite 2sepcon_assoc, sepcon_comm.
    rewrite !sepcon_assoc; apply sepcon_derives; [|cancel].
    assert (Zlength (upd_Znth 0 (map (data_at Tsh tbuffer (vint 0)) bufs)
      (data_at sh0 tbuffer (vint 0) (Znth 0 bufs Vundef))) = B) as Hlen.
    { rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto.
      unfold B, N in *; omega. }
    apply sepcon_list_derives.
    { rewrite Hlen, Zlength_map; auto. }
    intros; rewrite Hlen in *.
    erewrite Znth_map, Znth_upto; auto; [|unfold B, N in *; simpl; omega].
    destruct (eq_dec i 0).
    - subst; rewrite upd_Znth_same; [|rewrite Zlength_map; omega].
      Exists sh0 0; entailer'.
    - rewrite upd_Znth_diff; auto; rewrite ?Zlength_map; try omega.
      erewrite Znth_map; [|omega].
      Exists Tsh 0; entailer'.
    - intro; erewrite hist_share_join; eauto.
      apply mpred_ext'.
      + intros ??; exists []; split; auto.
        apply interleave_nil; auto.
      + intros ? (? & Hnil & ?).
        rewrite interleave_remove_nil, interleave_single in Hnil; replace [] with x; auto. }
  rewrite <- seq_assoc.
  assert_PROP (Zlength reads = N) by entailer!.
  assert_PROP (Zlength lasts = N) by entailer!.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (gvar _last_given last_given; gvar _writing writing; gvar _last_taken last_taken;
          gvar _last_read last_read; gvar _reading reading; gvar _comm comm; gvar _lock lock; gvar _bufs buf)
   SEP (EX sh' : share, !!(sepalg_list.list_join sh1 (sublist i N shs1) sh') &&
          data_at sh' (tarray (tptr tint) N) lasts last_read * data_at sh' (tarray (tptr tint) N) reads reading;
        fold_right sepcon emp (map (fun sh => data_at sh (tarray (tptr tint) N) comms comm) (sublist i N shs1));
        fold_right sepcon emp (map (fun sh => data_at sh (tarray (tptr tlock) N) locks lock) (sublist i N shs1));
        fold_right sepcon emp (map (fun sh => data_at sh (tarray (tptr tbuffer) B) bufs buf) (sublist i N shs1));
        fold_right sepcon emp (map (fun x => lock_inv gsh2 (Znth x locks Vundef)
          (comm_inv (Znth x comms Vundef) bufs (Znth x shs Tsh) gsh2)) (sublist i N (upto (Z.to_nat N))));
        fold_right sepcon emp (map (ghost gsh1 (-1) (gsh2, [])) (sublist i N comms));
        fold_right sepcon emp (map (ghost_var gsh1 tint (vint 0)) (sublist i N comms));
        fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i N reads));
        fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i N lasts));
        fold_right sepcon emp (map (malloc_token Tsh 4) comms);
        fold_right sepcon emp (map (malloc_token Tsh 4) locks);
        fold_right sepcon emp (map (malloc_token Tsh 4) bufs);
        fold_right sepcon emp (map (malloc_token Tsh 4) reads);
        fold_right sepcon emp (map (malloc_token Tsh 4) lasts);
        fold_right sepcon emp (map (fun sh => @data_at CompSpecs sh tbuffer (vint 0) (Znth 0 bufs Vundef)) (sublist i N shs)))).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists Ews; rewrite !sublist_same; auto; unfold N; entailer!. }
  { forward_call (sizeof tint).
    { simpl; computable. }
    Intro d.
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    forward.
    Intros sh'.
    get_global_function'' _reader; Intros.
    apply extract_exists_pre; intros reader_.
    match goal with H : sepalg_list.list_join sh1 _ sh' |- _ => rewrite sublist_next with (d0 := Tsh) in H;
      auto; [inversion H as [|????? Hj1 Hj2]; subst |
      match goal with H : Zlength shs1 = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; omega end] end.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh1' & ? & Hj').
    forward_spawn (Z * val * val * val * val * val * list val * list val * list val * list val * list val *
                   share * share * share * share * share)%type
      (reader_, d, (i, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs,
                    Znth i shs1 Tsh, gsh2, Znth i shs Tsh, gsh1, gsh2),
      fun (x : (Z * val * val * val * val * val * list val * list val * list val * list val * list val *
                share * share * share * share * share)%type) (arg : val) =>
        let '(r, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs, sh1, sh2, sh, gsh1, gsh2) := x in
        fold_right sepcon emp [!!(fold_right and True [readable_share sh; readable_share sh1; 
          readable_share sh2; sepalg.join gsh1 gsh2 Tsh; isptr (Znth r comms Vundef)]) && emp;
          data_at Tsh tint (vint r) arg; malloc_token Tsh (sizeof tint) arg;
          data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
          data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
          data_at_ Tsh tint (Znth r reads Vundef); data_at_ Tsh tint (Znth r lasts Vundef);
          data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
        lock_inv sh2 (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs sh gsh2);
        EX v : Z, data_at sh tbuffer (vint v) (Znth 0 bufs Vundef);
        ghost gsh1 (-1) (sh2, []) (Znth r comms Vundef); ghost_var gsh1 tint (vint 0) (Znth r comms Vundef)]).
    - apply andp_right.
      { entailer!. }
      unfold spawn_pre, PROPx, LOCALx, SEPx.
      go_lowerx.
      rewrite !sepcon_andp_prop, !sepcon_andp_prop'.
      apply andp_right; [apply prop_right; auto|].
      apply andp_right; [apply prop_right; repeat split; auto|].
      apply andp_right; [apply prop_right|].
      { unfold liftx; simpl; unfold lift, make_args'; simpl.
        rewrite eval_id_other, eval_id_same; [|discriminate].
        assert (isptr d) by (match goal with H : field_compatible _ _ d |- _ => destruct H;
          destruct d; auto; contradiction end).
        replace (eval_id _d rho) with d by auto.
        rewrite sem_cast_neutral_ptr; rewrite sem_cast_neutral_ptr; auto. }
      Exists _arg (fun x : (Z * val * val * val * val * val * list val * list val * list val * list val * list val *
                share * share * share * share * share) =>
        let '(r, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs, sh1, sh2, sh, gsh1, gsh2) := x in
        [(_reading, reading); (_last_read, last_read); (_lock, lock); (_comm, comm); (_bufs, buf)]).
      rewrite !sepcon_assoc; apply sepcon_derives.
      { apply derives_refl'.
        rewrite !prop_true_andp with (P := True), !sepcon_emp; auto.
        f_equal; f_equal; extensionality; destruct x as (?, x); repeat destruct x as (x, ?); simpl.
        rewrite !sepcon_andp_prop'; extensionality.
        rewrite <- andp_assoc, prop_true_andp with (P := True); auto.
        rewrite (andp_comm (!! _) (!! _)), andp_assoc; f_equal; f_equal.
        rewrite emp_sepcon, !sepcon_emp; auto. }
      rewrite sepcon_andp_prop'.
      apply andp_right; [apply prop_right; repeat (split; auto)|].
      { apply Forall_Znth; auto; match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; auto end. }
      { apply Forall_Znth; auto; match goal with H : Zlength shs1 = _ |- _ => setoid_rewrite H; auto end. }
      { apply Forall_Znth; auto; match goal with H : Zlength comms = _ |- _ => setoid_rewrite H; auto end. }
      rewrite <- !(data_at_share_join _ _ _ _ _ _ Hj').
      rewrite sublist_next with (d0 := Tsh); auto;
        [simpl | match goal with H : Zlength shs1 = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; omega end].
      rewrite !sublist_next with (i0 := i)(d0 := Vundef); auto; try omega; simpl.
      rewrite sublist_next with (d0 := N); rewrite ?Znth_upto; auto; rewrite? Zlength_upto; simpl;
        try (unfold N in *; omega).
      rewrite sublist_next with (i0 := i)(d0 := Tsh); auto;
        [simpl | match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; omega end].
      Exists 0; cancel.
    - Exists sh1'; entailer!.
    - exists 2; auto. }
  eapply semax_seq'; [|apply semax_ff].
  eapply semax_loop; [|forward; apply drop_tc_environ].
  forward.
  entailer!.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
repeat semax_func_cons_ext.
semax_func_cons body_malloc. apply semax_func_cons_malloc_aux.
repeat semax_func_cons_ext.
semax_func_cons body_surely_malloc.
semax_func_cons body_memset.
semax_func_cons body_atomic_exchange.
{ simpl in *.
  destruct x0 as ((((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?).
  (* This could probably be done automatically with a slight modification to precondition_closed. *)
  simpl not_a_param; auto 50 with closed. }
{ simpl in *.
  destruct x0 as ((((((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?), ?).
  simpl is_a_local; auto 50 with closed. }
semax_func_cons body_initialize_channels.
semax_func_cons body_initialize_reader.
semax_func_cons body_start_read.
semax_func_cons body_finish_read.
semax_func_cons body_initialize_writer.
eapply semax_func_cons; [ reflexivity
           | repeat apply Forall_cons; try apply Forall_nil; simpl; auto; computable
           | unfold var_sizes_ok; repeat constructor; simpl; computable | reflexivity | precondition_closed
           | apply body_start_write |].
{ apply closed_wrtl_PROPx, closed_wrtl_LOCALx, closed_wrtl_SEPx.
  repeat constructor; apply closed_wrtl_gvar; unfold is_a_local; simpl; intros [? | ?];
    try contradiction; discriminate. }
semax_func_cons body_finish_write.
semax_func_cons body_reader.
semax_func_cons body_writer.
semax_func_cons body_main.
Qed.