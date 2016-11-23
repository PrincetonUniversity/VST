Require Import veric.rmaps.
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

(*(* There are two invisible invariants: the last buffer written, and the buffer being read by each reader. *)
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
Inductive ghost_el := G (r : Z) (bro : Z) (br : Z) (bw : Z) | R (r : Z) (br : Z) | W (brs : list Z) (bw : Z).
Definition consistent1 m n :=
  match m with
  | G r bro br bw => match n with
                | R r' br' => r = r' /\ br = br'
                | W brs' bw' => Zlength brs' = N /\ bw' = bw /\ (Znth r brs' (-2) = br \/ (br = bw /\ Znth r brs' (-2) = bro))
                | G r' bro' br' bw' => (*bw' = bw /\ r <> r'*) False
                end
  | R r br => match n with
              | G r' bro br' bw => r = r' /\ br = br'
              | W brs bw => Zlength brs = N /\ (Znth r brs (-2) = br \/ br = bw)
              | _ => False
              end
  | W brs' bw' => Zlength brs' = N /\ match n with
                | G r bro br bw => bw' = bw /\ (Znth r brs' (-2) = br \/ (br = bw /\ Znth r brs' (-2) = bro))
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
Axiom ghost_join : forall l l', ghost l * ghost l' = ghost (l ++ l').*)

(* Ghost histories in the style of
   History-based Verification of Functional Behaviour of Concurrent Programs,
   Blom, Huisman, and Zharieva-Stojanovski (VerCors)
   Twente tech report, 2015 *)

(* These histories should be usable for any atomically accessed int-valued location. *)
Inductive hist_el := AE (r : Z) (w : Z).
Notation hist := (list hist_el).
Fixpoint apply_hist a h :=
  match h with
  | [] => Some a
  | AE r w :: h' => match apply_hist a h' with Some a' => if eq_dec a' r then Some w else None | _ => None end
  end.

Parameter ghost : forall (sh : share) (f : share * hist) (p : val), mpred.

Axiom new_ghost : forall {CS : compspecs} {Espec : OracleKind} D P Q R C P' t v p,
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh (Tsh, []) p :: data_at Tsh t v p :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (data_at Tsh t v p :: R)))) C P'.

Inductive list_incl {A} : list A -> list A -> Prop :=
| incl_nil l : list_incl [] l
| incl_skip l1 a l2 (Hincl : list_incl l1 l2) : list_incl l1 (a :: l2)
| incl_cons a l1 l2 (Hincl : list_incl l1 l2) : list_incl (a :: l1) (a :: l2).
Hint Constructors list_incl.

Inductive interleave {A} : list (list A) -> list A -> Prop :=
| interleave_nil ls (Hnil : Forall (fun l => l = []) ls) : interleave ls []
| interleave_cons ls i a l l' (Hcons : Znth i ls [] = a :: l) (Hrest : interleave (upd_Znth i ls l) l') :
    interleave ls (a :: l').

Axiom ghost_share_join : forall sh1 sh2 sh h1 h2 p, sepalg.join sh1 sh2 Tsh -> list_incl h1 h2 ->
  ghost sh1 (sh, h1) p * ghost sh2 (Tsh, h2) p = ghost Tsh (Tsh, h2) p.
Axiom hist_share_join : forall sh sh1 sh2 sh' h1 h2 p, sepalg.join sh1 sh2 sh' ->
  ghost sh (sh1, h1) p * ghost sh (sh2, h2) p = EX h' : hist, !!(interleave [h1; h2] h') && ghost sh (sh', h') p.
Axiom hist_add : forall {CS : compspecs} {Espec : OracleKind} D P Q R C P' h e p,
  apply_hist 0 (e :: h) <> None ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh (Tsh, e :: h) p :: R)))) C P' ->
  semax D (PROPx P (LOCALx Q (SEPx (ghost Tsh (Tsh, h) p :: R)))) C P'.
Axiom ghost_inj : forall sh1 sh2 sh h1 h2 p, ghost sh1 (sh, h1) p * ghost sh2 (Tsh, h2) p
  |-- !!(list_incl h1 h2).
Axiom ghost_inj_Tsh : forall sh1 sh2 h1 h2 p, ghost sh1 (Tsh, h1) p * ghost sh2 (Tsh, h2) p
  |-- !!(h1 = h2).
(* Should this be an axiom? *)
Axiom ghost_feasible : forall sh h p, ghost sh (Tsh, h) p |-- !!(apply_hist 0 h <> None).
Axiom ghost_conflict : forall sh1 sh2 v1 v2 p,
  ghost sh1 v1 p * ghost sh2 v2 p |-- !!sepalg.joins sh1 sh2.

Fixpoint prev_read h :=
  match h with
  | [] => None
  | AE r w :: rest => if eq_dec w (-1) then Some r else prev_read rest
  end.

Definition comm_inv comm bufs sh gsh :=
  EX h : hist, EX b : Z, !!(apply_hist 0 h = Some b /\ -1 <= b < B) && (ghost gsh (Tsh, h) comm *
    data_at Tsh tint (vint b) comm *
    EX v : Z, if eq_dec b (-1) then
      match prev_read (tl h) with Some b' => data_at sh tbuffer (vint v) (Znth b' bufs Vundef)
      | None => emp end
      else data_at sh tbuffer (vint v) (Znth b bufs Vundef)).

(* up *)
Lemma field_at_array_inbounds : forall sh t z a i v p,
  field_at sh (Tarray t z a) [ArraySubsc i] v p |-- !!(0 <= i < z).
Proof.
  intros; entailer!.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & ?); auto.
Qed.

(* How can we generalize this? *)
(*Definition atomic_exchange_spec :=
 DECLARE _simulate_atomic_exchange
  WITH r : Z, v : Z, lock : val, locks : list val, comm : val, comms : list val, bufs : list val,
    sh1 : share, sh2 : share, g : ghost_el, brs : list Z, b : Z, v1 : Z, bsh2 : share
  PRE [ _r OF tint, _v OF tint ]
   PROP (readable_share sh1; readable_share sh2; repable_signed v; -1 <= v < B;
         if eq_dec v (-1) then g = R r b else g = W brs b /\ b <> v /\ Forall (fun x => x <> v) brs)
   LOCAL (temp _r (vint r); temp _v (vint v); gvar _lock lock; gvar _comm comm)
   SEP (data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        lock_inv sh2 (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs r bsh2); ghost gsh1 (sh, h) (Znth r comms Vundef);
        data_at bsh2 tbuffer (vint v1) (Znth (if eq_dec v (-1) then b else v) bufs Vundef))
  POST [ tint ]
   EX g' : ghost_el, EX v' : Z, EX v1 : Z,
   PROP (if eq_dec v (-1) then g' = R r (if eq_dec v' (-1) then b else v')
         else g' = W (if eq_dec v' (-1) then upd_Znth r brs b else brs) v; -1 <= v' < B)
   LOCAL (temp ret_temp (vint v'))
   SEP (data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        lock_inv sh2 (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs r bsh2);
        ghost gsh1 (sh, AE v' v :: h) (Znth r comms Vundef);
        data_at bsh2 tbuffer (vint v1)
          (Znth (if eq_dec v' (-1) then (if eq_dec v (-1) then b else Znth r brs (-1)) else v') bufs Vundef)).*)
Program Definition atomic_exchange_spec := DECLARE _simulate_atomic_exchange
  mk_funspec ([(_tgt, tptr tint); (_l, tptr tlock); (_v, tint)], tint) cc_default
  (ProdType (ConstType (share * share * share * share * share * val * val * Z * hist))
     (ArrowType (ConstType hist) (ArrowType (ConstType Z) Mpred)))
  (fun (ts: list Type) (x: share * share * share * share * share * val * val * Z * hist * (hist -> Z -> mpred)) =>
     let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, v, h, R) := x in
     PROP (sepalg.join gsh1 gsh2 Tsh)
     LOCAL (temp _tgt tgt; temp _l l; temp _v (vint v))
     SEP (lock_inv lsh l (EX h : hist, EX v : Z, !!(apply_hist 0 h = Some v) &&
            (data_at ish tint (vint v) tgt * ghost gsh2 (Tsh, h) tgt * R h v));
          ghost gsh1 (hsh, h) tgt; R h v))
  (fun (ts: list Type) (x: share * share * share * share * share * val * val * Z * hist * (hist -> Z -> mpred)) =>
     let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, v, h, R) := x in
     EX v' : Z,
     PROP ()
     LOCAL (temp ret_temp (vint v'))
     SEP (lock_inv lsh l (EX h : hist, EX v : Z, !!(apply_hist 0 h = Some v) &&
            (data_at ish tint (vint v) tgt * ghost gsh2 (Tsh, h) tgt * R h v));
          ghost gsh1 (hsh, AE v' v :: h) tgt; R (AE v' v :: h) v')) _ _.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type)
    (x : share * share * share * share * share * val * val * Z * hist * (hist -> Z -> mpred)) rho =>
    PROP (let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, v, h, R) := x in sepalg.join gsh1 gsh2 Tsh)
    LOCAL (let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, v, h, R) := x in temp _tgt tgt;
           let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, v, h, R) := x in temp _l l;
           let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, v, h, R) := x in temp _v (vint v))
    SEP (let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, v, h, R) := x in
         lock_inv lsh l (EX h : hist, EX v : Z, !!(apply_hist 0 h = Some v) &&
           (data_at ish tint (vint v) tgt * ghost gsh2 (Tsh, h) tgt * R h v)) *
         ghost gsh1 (hsh, h) tgt * R h v) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive (ProdType (ConstType (share * share * share * share * share * val * val * Z * hist))
    (ArrowType (ConstType hist) (ArrowType (ConstType Z) Mpred)))
    [fun _ => _] [fun _ => _; fun _ => _; fun _ => _] [fun _ => _]); repeat constructor; hnf; intros;
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), R); auto; simpl.
  - rewrite !approx_sepcon; f_equal.
    + f_equal.
      rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
      setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
      f_equal; f_equal.
      rewrite !approx_exp; f_equal; extensionality l'.
      rewrite !approx_exp; f_equal; extensionality z'.
      rewrite !approx_andp, !approx_sepcon; f_equal; f_equal.
      replace (compcert_rmaps.RML.R.approx n (R l' z')) with
        (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) (R l' z')) at 1
        by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
    + replace (compcert_rmaps.RML.R.approx n (R l z)) with
        (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) (R l z)) at 1
        by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), R); auto.
    unfold SEPx; simpl; rewrite !sepcon_assoc; auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (_ : list Type)
    (x : share * share * share * share * share * val * val * Z * hist * (hist -> Z -> mpred)) rho =>
    EX v' : Z, PROP () LOCAL (let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, v, h, R) := x in temp ret_temp (vint v'))
    SEP (let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, v, h, R) := x in
         lock_inv lsh l (EX h : hist, EX v : Z, !!(apply_hist 0 h = Some v) &&
           (data_at ish tint (vint v) tgt * ghost gsh2 (Tsh, h) tgt * R h v)) *
         ghost gsh1 (hsh, AE v' v :: h) tgt * R (AE v' v :: h) v') rho).
  repeat intro.
  rewrite !approx_exp; f_equal; extensionality v'.
  apply (PROP_LOCAL_SEP_super_non_expansive (ProdType (ConstType (share * share * share * share * share * val * val * Z * hist))
    (ArrowType (ConstType hist) (ArrowType (ConstType Z) Mpred)))
    [] [fun ts x => let '(_, _, _, _, _, _, _, _, _, _) := x in temp ret_temp (vint v')]
    [fun ts x => let '(ish, lsh, gsh1, gsh2, hsh, tgt, l, v, h, R) := x in lock_inv lsh l
       (EX h0 : hist, (EX v0 : Z, !! (apply_hist 0 h0 = Some v0) &&
              (data_at ish tint (vint v0) tgt * ghost gsh2 (Tsh, h0) tgt * R h0 v0))) *
          ghost gsh1 (hsh, AE v' v :: h) tgt * R (AE v' v :: h) v']); repeat constructor; hnf; intros;
    destruct x0 as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), R); auto; simpl.
  - rewrite !approx_sepcon; f_equal.
    + rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)); [|apply nonexpansive_lock_inv].
      f_equal.
      setoid_rewrite (nonexpansive_super_non_expansive (fun R => lock_inv s0 v0 R)) at 2; [|apply nonexpansive_lock_inv].
      f_equal; f_equal.
      rewrite !approx_exp; f_equal; extensionality l'.
      rewrite !approx_exp; f_equal; extensionality z'.
      rewrite !approx_andp, !approx_sepcon; f_equal; f_equal.
      replace (compcert_rmaps.RML.R.approx n0 (R l' z')) with
        (base.compose (compcert_rmaps.R.approx n0) (compcert_rmaps.R.approx n0) (R l' z')) at 1
        by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
    + replace (compcert_rmaps.RML.R.approx n0 (R _ v')) with
        (base.compose (compcert_rmaps.R.approx n0) (compcert_rmaps.R.approx n0) (R (AE v' z :: l) v')) at 1
        by (rewrite compcert_rmaps.RML.approx_oo_approx; auto); auto.
  - extensionality ts x rho.
    destruct x as (((((((((?, ?), ?), ?), ?), ?), ?), ?), ?), R); auto.
    f_equal; extensionality.
    unfold SEPx; simpl; rewrite !sepcon_assoc; auto.
Qed.

Definition initialize_channels_spec :=
 DECLARE _initialize_channels
  WITH comm : val, lock : val, buf : val, reading : val, last_given : val, gsh1 : share, gsh2 : share,
    sh1 : share, shs : list share
  PRE [ ]
   PROP (sepalg.join gsh1 gsh2 Tsh; sepalg_list.list_join sh1 shs Tsh)
   LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs buf)
   SEP (data_at_ Ews (tarray (tptr tint) N) comm; data_at_ Ews (tarray (tptr tlock) N) lock;
        data_at_ Ews (tarray (tptr tbuffer) B) buf)
  POST [ tvoid ]
   EX comms : list val, EX locks : list val, EX bufs : list val,
   PROP ()
   LOCAL ()
   SEP (data_at Ews (tarray (tptr tint) N) comms comm;
        data_at Ews (tarray (tptr tlock) N) locks lock;
        data_at Ews (tarray (tptr tbuffer) B) bufs buf;
        fold_right sepcon emp (map (fun r =>
          lock_inv Tsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost gsh1 (Tsh, [])) comms);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) comms);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tlock)) locks);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs);
        fold_right sepcon emp (map (data_at_ Tsh tbuffer) bufs)).
(* All the communication channels are now inside locks. *)

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

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0, x15 at level 0,
             P at level 100, Q at level 100).

(* last_read retains the last buffer read, while reading is reset to Empty. *)
Definition start_read_spec :=
 DECLARE _start_read
  WITH r : Z, reading : val, last_read : val, lock : val, comm : val, c : val, bufs : list val,
    sh : share, sh1 : share, sh2 : share, l : val, b0 : Z, gsh1 : share, gsh2 : share, h : hist
  PRE [ _r OF tint ]
   PROP (readable_share sh; readable_share sh1; readable_share sh2; sepalg.join gsh1 gsh2 Tsh)
   LOCAL (temp _r (vint r); gvar _reading reading; gvar _last_read last_read; gvar _lock lock; gvar _comm comm)
   SEP (field_at_ Ews (tarray tint N) [ArraySubsc r] reading;
        field_at Ews (tarray tint N) [ArraySubsc r] (vint b0) last_read;
        field_at sh1 (tarray (tptr tint) N) [ArraySubsc r] c comm;
        field_at sh1 (tarray (tptr tlock) N) [ArraySubsc r] l lock;
        lock_inv sh2 l (comm_inv c bufs sh gsh2);
        data_at_ sh tbuffer (Znth b0 bufs Vundef);
        ghost gsh1 (sh2, h) c)
  POST [ tvoid ]
   EX b : Z, EX v0 : Z, EX v : Z,
   PROP ()
   LOCAL ()
   SEP (field_at Ews (tarray tint N) [ArraySubsc r] (vint b) reading;
        field_at Ews (tarray tint N) [ArraySubsc r] (vint b) last_read;
        field_at sh1 (tarray (tptr tint) N) [ArraySubsc r] c comm;
        field_at sh1 (tarray (tptr tlock) N) [ArraySubsc r] l lock;
        lock_inv sh2 l (comm_inv c bufs sh gsh2);
        data_at sh tbuffer (vint v) (Znth b bufs Vundef);
        ghost gsh1 (sh2, AE v0 (-1) :: h) c).
(* And bufs[b] is the most recent buffer completed by finish_write. *)

Definition finish_read_spec :=
 DECLARE _finish_read
  WITH r : Z, reading : val, bufs : val, sh : share, b : Z
  PRE [ _r OF tint ]
   PROP (readable_share sh)
   LOCAL (temp _r (vint r); gvar _reading reading)
   SEP (field_at Ews (tarray tint N) [ArraySubsc r] (vint b) reading)
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
   PROP (0 <= b0 < B; Forall (fun x => -1 <= x < B) lasts)
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
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
  | [] => shs
  | b :: rest => if eq_dec b i then make_shares (tl shs) rest i
                 else hd Share.bot shs :: make_shares (tl shs) rest i
  end.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0, x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0, x20 at level 0,
             P at level 100, Q at level 100).

Definition finish_write_spec :=
 DECLARE _finish_write
  WITH writing : val, last_given : val, last_taken : val, comm : val, lock : val,
    comms : list val, locks : list val, bufs : list val, b : Z, b0 : Z, lasts : list Z,
    sh1 : share, sh2 : share, lsh : share, shs : list share, gsh1 : share, gsh2 : share, h : list hist, sh0 : share, v : Z
  PRE [ ]
   PROP (0 <= b < B; Forall (fun x => -1 <= x < B) lasts; Zlength h = N; readable_share sh1;
         sepalg_list.list_join sh0 shs Tsh)
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _comm comm;
          gvar _lock lock)
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        fold_right sepcon emp (map (fun r =>
          lock_inv lsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun x => let '(c, h) := x in ghost gsh1 (lsh, h) c) (combine comms h));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(sepalg_list.list_join sh0 (make_shares shs lasts i) sh) &&
          data_at_ sh tbuffer (Znth i bufs Vundef)) (upto (Z.to_nat B))))
  POST [ tvoid ]
   EX lasts' : list Z, EX h' : list hist,
   PROP (Forall (fun x => -1 <= x < B) lasts'; Forall2 (fun h1 h2 => exists v, h2 = AE b v :: h1) h h')
   LOCAL ()
   SEP (data_at Ews tint (vint (-1)) writing; data_at Ews tint (vint b) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts') last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        fold_right sepcon emp (map (fun r =>
          lock_inv lsh (Znth r locks Vundef) (comm_inv (Znth r comms Vundef) bufs (Znth r shs Tsh) gsh2))
          (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun x => let '(c, h) := x in ghost gsh1 (lsh, h) c) (combine comms h'));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(sepalg_list.list_join sh0 (make_shares shs lasts' i) sh) &&
          data_at_ sh tbuffer (Znth i bufs Vundef)) (upto (Z.to_nat B)))).

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

(* up *)
Lemma upd_init : forall {A} (l : list A) i b v v', i < b -> Zlength l = i ->
  upd_Znth i (l ++ repeat v (Z.to_nat (b - i))) v' = l ++ v' :: repeat v (Z.to_nat (b - (i + 1))).
Proof.
  intros.
  rewrite upd_Znth_app2; rewrite ?Zlength_repeat, ?Z2Nat.id; try omega.
  subst; rewrite Zminus_diag, upd_Znth0.
  destruct (Z.to_nat (b - Zlength l)) eqn: Hi.
  { change O with (Z.to_nat 0) in Hi; apply Z2Nat.inj in Hi; omega. }
  simpl; rewrite sublist_1_cons, sublist_same; try rewrite Zlength_cons, !Zlength_repeat; try omega.
  replace (Z.to_nat (b - (Zlength l + 1))) with n; auto.
  rewrite Z.sub_add_distr, Z2Nat.inj_sub; try omega.
  setoid_rewrite Hi; simpl; omega.
Qed.

Corollary upd_init_const : forall {A} i b (v v' : A), 0 <= i < b ->
  upd_Znth i (repeat v' (Z.to_nat i) ++ repeat v (Z.to_nat (b - i))) v' =
  repeat v' (Z.to_nat (i + 1)) ++ repeat v (Z.to_nat (b - (i + 1))).
Proof.
  intros.
  rewrite upd_init; try rewrite Zlength_repeat, Z2Nat.id; auto; try omega.
  rewrite Z2Nat.inj_add, repeat_plus, <- app_assoc; auto; omega.
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
    rewrite zero_ext_inrange; rewrite zero_ext_inrange; rewrite ?Int.unsigned_repr; try omega.
    rewrite upd_init_const; [|omega].
    entailer!.
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

Axiom ghost_inj' : forall sh p h1 h2 r1 r2 r
  (Hp1 : predicates_hered.app_pred (ghost sh (Tsh, h1) p) r1)
  (Hp1 : predicates_hered.app_pred (ghost sh (Tsh, h2) p) r2)
  (Hr1 : sepalg.join_sub r1 r) (Hr2 : sepalg.join_sub r2 r),
  r1 = r2 /\ h1 = h2.

Arguments eq_dec _ _ _ _ : simpl never.

Lemma inv_precise : forall comm bufs sh gsh, readable_share sh -> precise (comm_inv comm bufs sh gsh).
Proof.
  unfold comm_inv; intros.
  intros ??? (h1 & b1 & (? & ?) & ? & ? & ? & (? & ? & ? & Hghost1 & ? & Hb1) & v1 & Hrest1)
    (h2 & b2 & (? & ?) & ? & ? & ? & (? & ? & ? & Hghost2 & ? & Hb2) & v2 & Hrest2) ??.
  unfold at_offset in *; simpl in *; rewrite data_at_rec_eq in Hb1, Hb2; simpl in *.
  assert (readable_share Tsh) as Hread by auto.
  exploit (mapsto_inj _ _ _ _ _ _ _ w Hread Hb1 Hb2); auto; try join_sub.
  { unfold unfold_reptype; simpl; discriminate. }
  { unfold unfold_reptype; simpl; discriminate. }
  unfold unfold_reptype; simpl; intros (? & Hb).
  assert (b1 = b2).
  { apply repr_inj_signed; try (split; [transitivity (-1) | transitivity B]; unfold B, N in *;
      try computable; try omega); congruence. }
  exploit (ghost_inj' _ _ _ _ _ _ w Hghost1 Hghost2); try join_sub.
  intros (? & ?); subst.
  destruct (eq_dec b2 (-1)).
  - destruct (prev_read (tl h2)).
    + destruct Hrest1 as (? & Hrest1), Hrest2 as (? & Hrest2).
      unfold at_offset in *; exploit (mapsto_inj sh); auto.
      { apply Hrest1. }
      { apply Hrest2. }
      { join_sub. }
      { join_sub. }
      { unfold unfold_reptype; simpl; discriminate. }
      { unfold unfold_reptype; simpl; discriminate. }
      intros (? & ?); subst; join_inj.
    + exploit Hrest1; [eapply sepalg.join_comm; eauto|].
      exploit Hrest2; [eapply sepalg.join_comm; eauto|].
      intros; join_inj.
  - destruct Hrest1 as (? & Hrest1), Hrest2 as (? & Hrest2).
    unfold at_offset in *; exploit (mapsto_inj sh); auto.
    { apply Hrest1. }
    { apply Hrest2. }
    { join_sub. }
    { join_sub. }
    { unfold unfold_reptype; simpl; discriminate. }
    { unfold unfold_reptype; simpl; discriminate. }
    intros (? & ?); subst; join_inj.
Qed.

Lemma inv_positive : forall comm bufs sh gsh, positive_mpred (comm_inv comm bufs sh gsh).
Proof.
  unfold comm_inv; intros.
  repeat (apply ex_positive; intro).
  apply positive_andp2, positive_sepcon1, positive_sepcon2; auto.
Qed.
Hint Resolve inv_precise inv_positive.

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
  simpl; destruct ts as (((((((((ish, lsh), gsh1), gsh2), hsh), tgt), l), v), h), R).
(* start_function doesn't work for dependent specs? *)
  rewrite <- lock_struct_array_sub, lock_inv_isptr; Intros.
  assert_PROP (0 <= r < N) as Hr.
  { go_lowerx; apply sepcon_derives_prop, field_at_array_inbounds. }
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
  destruct writer eqn: Hwriter; [destruct H0 as (? & ? & Hneq & Hv) | destruct H0 as (? & ?)];
    subst; simpl in Hcon'.
  - destruct Hcon' as (Hlen & ? & Hcon'); subst.
    apply ghost_shift with (l' := [G r br v] ++ [W (if eq_dec br bw then upd_Znth r brs bw else brs) v]).
    { clear - Hr Hlen Hcon'; intros p Hcon.
      rewrite <- Hlen in Hr.
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
    + destruct (eq_dec br bw); split; try omega; destruct (eq_dec _ _); auto.
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
    + destruct (eq_dec b bw); split; try omega; destruct (eq_dec _ _); auto.
      * contradiction n; auto.
      * omega.
    + rewrite lock_struct_array_sub; cancel.
      destruct (eq_dec b bw); subst; apply derives_refl.
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
  forward_for_simple_bound N (EX i : Z, PROP () LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs bufs)
    SEP (data_at_ Ews (tarray tint N) (offset_val (sizeof tint * i) comm);
         EX locks : list val, !!(Zlength locks = i) &&
          (data_at Ews (tarray (tptr tlock) N) (locks ++ repeat Vundef (Z.to_nat (N - i))) lock *
           fold_right sepcon emp (map (fun r => lock_inv Tsh (Znth r locks Vundef) (comm_inv comm r)) (upto (Z.to_nat i))) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tlock)) locks));
         data_at_ Ews (tarray tbuffer B) bufs)).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists ([] : list val); repeat entailer!. }
  - Intros locks.
(*    forward.
    forward_call (sizeof tlock).
    { admit. }
    { simpl; computable. }
    Intro l.
    rewrite malloc_compat; auto; Intros.
    rewrite memory_block_data_at_; auto.
    rewrite <- lock_struct_array.
    forward.
    forward_call (l, Tsh, comm_inv comm i).
    forward_call (l, Tsh, comm_inv comm i).
    { lock_props.
      unfold comm_inv.*)
Admitted.

Lemma body_initialize_reader : semax_body Vprog Gprog f_initialize_reader initialize_reader_spec.
Proof.
  start_function.
  assert_PROP (0 <= r < N) as Hr.
  { go_lowerx; apply sepcon_derives_prop, field_at_array_inbounds. }
  forward.
  forward.
  forward.
Qed.

Lemma body_start_read : semax_body Vprog Gprog f_start_read start_read_spec.
Proof.
  start_function.
  forward_call (sh1, sh2, r, -1, lock, l, comm, false, R r b0, [] : list Z, b0).
  { repeat split; auto; computable. }
  Intros x; destruct x as (? & b); simpl fst in *; simpl snd in *; subst.
  assert (repable_signed b).
  { split; [transitivity (-1); [computable | omega]|].
    transitivity B; [omega | unfold B, N; computable]. }
  forward_if (PROP ()
   LOCAL (temp _t'2 (vint (if eq_dec b (-1) then 0 else 1)); temp _b (vint b); temp _r (vint r); gvar _reading reading; gvar _last_read last_read; 
   gvar _lock lock; gvar _comm comm)
   SEP (field_at sh1 (tarray (tptr tlock) N) [ArraySubsc r] l lock; lock_inv sh2 l (comm_inv comm r);
   ghost [R r (if eq_dec b (-1) then b0 else b)]; field_at_ Ews (tarray tint N) [ArraySubsc r] reading;
   field_at Ews (tarray tint N) [ArraySubsc r] (vint b0) last_read)).
  { forward.
    destruct (eq_dec b (-1)); [omega|].
    entailer!.
    destruct (Int.lt (Int.repr b) (Int.repr (3 + 2))) eqn: Hlt; auto.
    apply lt_repr_false in Hlt; auto; unfold repable_signed; try computable.
    unfold B, N in *; omega. }
  { forward.
    destruct (eq_dec b (-1)); [|omega].
    entailer!. }
  assert_PROP (0 <= r < N) as Hr.
  { go_lowerx; apply sepcon_derives_prop, field_at_array_inbounds. }
  forward_if (PROP () LOCAL (temp _b (vint (if eq_dec b (-1) then b0 else b)); temp _r (vint r);
      gvar _reading reading; gvar _last_read last_read; gvar _lock lock; gvar _comm comm)
    SEP (field_at sh1 (tarray (tptr tlock) N) [ArraySubsc r] l lock; lock_inv sh2 l (comm_inv comm r);
         ghost [R r (if eq_dec b (-1) then b0 else b)]; field_at_ Ews (tarray tint N) [ArraySubsc r] reading;
         field_at Ews (tarray tint N) [ArraySubsc r] (vint (if eq_dec b (-1) then b0 else b)) last_read)).
  - forward.
    simpl eq_dec; destruct (eq_dec b (-1)); [contradiction H2; auto|].
    entailer!.
  - forward.
    simpl eq_dec; destruct (eq_dec b (-1)); [|discriminate].
    entailer!.
  - forward.
    forward.
    Exists (if eq_dec b (-1) then b0 else b); simpl; entailer!.
    destruct (eq_dec b (-1)); omega.
Qed.

Lemma body_finish_read : semax_body Vprog Gprog f_finish_read finish_read_spec.
Proof.
  start_function.
  assert_PROP (0 <= r < N) as Hr.
  { go_lowerx; apply sepcon_derives_prop, field_at_array_inbounds. }
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
        data_at Ews (tarray tint N) (repeat (vint (-1)) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (N - i))) last_taken)).
  { unfold N; computable. }
  { unfold N; computable. }
  { entailer!. }
  - forward.
    rewrite upd_init_const; auto.
    entailer!.
  - forward.
Qed.

Lemma list_Znth_eq : forall {A} d (l : list A), l = map (fun j => Znth j l d) (upto (length l)).
Proof.
  induction l; simpl; intros; auto.
  rewrite Znth_0_cons, IHl, map_map, map_length, upto_length.
  f_equal; apply map_ext_in; intros.
  rewrite Znth_pos_cons, <- IHl.
  unfold Z.succ; rewrite Z.add_simpl_r; auto.
  { rewrite In_upto in *; omega. }
Qed.

Lemma upd_Znth_eq : forall {A} {EqDec : EqDec A} (x d : A) (l : list A) i, 0 <= i < Zlength l ->
  upd_Znth i l x = map (fun j => if eq_dec j i then x else Znth j l d) (upto (length l)).
Proof.
  induction l; simpl; intros.
  { rewrite Zlength_nil in *; omega. }
  destruct (eq_dec 0 i).
  - subst; rewrite upd_Znth0, Zlength_cons, sublist_1_cons, sublist_same; auto; try omega.
    rewrite list_Znth_eq with (l0 := l)(d0 := d) at 1.
    rewrite map_map.
    f_equal; apply map_ext_in; intros.
    rewrite In_upto in *.
    destruct (eq_dec (Z.succ a0) 0); [omega|].
    rewrite Znth_pos_cons; [|omega].
    f_equal; omega.
  - rewrite Znth_0_cons, upd_Znth_cons; [|omega].
    rewrite Zlength_cons in *.
    rewrite IHl, map_map; [|omega].
    f_equal; apply map_ext_in; intros.
    rewrite In_upto in *.
    destruct (eq_dec a0 (i - 1)), (eq_dec (Z.succ a0) i); try omega; auto.
    rewrite Znth_pos_cons; [|omega].
    f_equal; omega.
Qed.

Lemma NoDup_filter : forall {A} (f : A -> bool) l, NoDup l -> NoDup (filter f l).
Proof.
  induction l; simpl; intros; auto.
  inv H.
  destruct (f a); auto.
  constructor; auto.
  rewrite filter_In; intros (? & ?); contradiction.
Qed.

Lemma list_in_count : forall {A} {A_eq : EqDec A} (l l' : list A), NoDup l' ->
  (length (filter (fun x => if in_dec eq_dec x l then true else false) l') <= length l)%nat.
Proof.
  intros.
  apply NoDup_incl_length; [apply NoDup_filter; auto|].
  intros ? Hin.
  rewrite filter_In in Hin; destruct Hin.
  destruct (in_dec eq_dec a l); [auto | discriminate].
Qed.

Lemma filter_length : forall {A} (f : A -> bool) l,
  length l = (length (filter f l) + length (filter (fun x => negb (f x)) l))%nat.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl.
  destruct (f a); simpl; omega.
Qed.

Lemma NoDup_upto : forall n, NoDup (upto n).
Proof.
  induction n; simpl; constructor.
  - rewrite in_map_iff.
    intros (? & ? & ?); rewrite In_upto in *; omega.
  - apply FinFun.Injective_map_NoDup; auto.
    intros ???; omega.
Qed.

Lemma list_pigeonhole : forall l n, Zlength l < n -> exists a, 0 <= a < n /\ ~In a l.
Proof.
  intros.
  pose proof (filter_length (fun x => if in_dec eq_dec x l then true else false) (upto (Z.to_nat n))) as Hlen.
  rewrite upto_length in Hlen.
  assert (length (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n))) > 0)%nat.
  { exploit (list_in_count l (upto (Z.to_nat n))).
    { apply NoDup_upto. }
    rewrite Zlength_correct in H.
    apply Z2Nat.inj_lt in H; try omega.
    rewrite Nat2Z.id in H; omega. }
  destruct (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n))) eqn: Hfilter;
    [simpl in *; omega|].
  assert (In z (filter (fun x => negb (if in_dec eq_dec x l then true else false)) (upto (Z.to_nat n)))) as Hin
    by (rewrite Hfilter; simpl; auto).
  rewrite filter_In, In_upto, Z2Nat.id in Hin; [|rewrite Zlength_correct in *; omega].
  destruct Hin; destruct (in_dec eq_dec z l); try discriminate; eauto.
Qed.

Opaque upto.

Lemma body_start_write : semax_body Vprog Gprog f_start_write start_write_spec.
Proof.
  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound B (EX i : Z, PROP ( )
   LOCAL (lvar _available (tarray tint 5) lvar0; gvar _writing writing; gvar _last_given last_given;
   gvar _last_taken last_taken; gvar _reading reading)
   SEP (data_at Tsh (tarray tint 5) (repeat (vint 1) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (B - i))) lvar0;
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
   LOCAL (temp _i (vint B); lvar _available (tarray tint 5) lvar0; 
   gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
   SEP (field_at Tsh (tarray tint 5) [] (map (fun x => vint (if eq_dec x b0 then 0
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
             gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
      SEP (field_at Tsh (tarray tint 5) [] (map (fun x => vint (if eq_dec x b0 then 0
             else if in_dec eq_dec x (sublist 0 (i + 1) lasts) then 0 else 1)) (upto (Z.to_nat B))) lvar0;
           data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
           data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    - assert (0 <= Znth i lasts (-1) < 5).
      { exploit (Forall_Znth(A := Z)); eauto.
        instantiate (1 := -1); intro.
        destruct (eq_dec (Znth i lasts (-1)) (-1)); [|unfold B, N in *; simpl in *; omega].
        match goal with H : Int.repr _ <> Int.neg _ |- _ => contradiction H; rewrite e; auto end. }
      forward.
      entailer!.
      rewrite upd_Znth_eq with (d := Vundef); auto.
      apply derives_refl'; erewrite map_ext_in; [reflexivity|].
      intros; rewrite In_upto, map_length, upto_length in *; simpl in *.
      rewrite Znth_map with (d' := 5), Znth_upto; simpl; auto; try omega.
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
           gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
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
             gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
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
    forward_if (PROP (Znth i available (vint 0) = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) lvar0; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
      SEP (field_at Tsh (tarray tint 5) [] available lvar0; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    { forward.
      forward.
      Exists lvar0 i; entailer!.
      unfold data_at_, field_at_; entailer!. }
    { forward.
      entailer!.
      subst available.
      rewrite Znth_map with (d' := 0) in *; try (rewrite Zlength_upto; unfold B, N in *; simpl in *; omega).
      unfold B, N; simpl; destruct (eq_dec _ _); auto.
      destruct (in_dec _ _ _); auto.
      unfold typed_false in *; simpl in *; discriminate. }
    intros.
    unfold exit_tycon, overridePost.
    destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
    Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert, loop1_ret_assert.
    instantiate (1 := EX i : Z, PROP (0 <= i < B; Znth i available (vint 0) = vint 0;
      forall j : Z, j < i -> Znth j available (vint 0) = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint 5) lvar0; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken; gvar _reading reading)
      SEP (field_at Tsh (tarray tint 5) [] available lvar0; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    Exists i; entailer!.
  - Intros i.
    forward.
    Exists (i + 1); entailer!.
    intros; destruct (eq_dec j i); subst; auto.
    assert (j < i) by omega; auto.
Qed.

Lemma body_finish_write : semax_body Vprog Gprog f_finish_write finish_write_spec.
Proof.
  start_function.
  forward.
  forward_for_simple_bound N (EX i : Z, ).
  { unfold N; computable. }
  { unfold N; computable. }
  
Admitted.