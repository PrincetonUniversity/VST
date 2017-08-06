Require Import mailbox.verif_atomic_exchange.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.
Require Import mailbox.mailbox.

Set Bullet Behavior "Strict Subproofs".

(* standard VST prelude *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* import funspecs from concurrency library *)
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.

(* utility function specs *)
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
   PROP (writable_share sh; sizeof t = (4 * n)%Z; 4 * n <= Int.max_unsigned; (4 | alignof t))
   LOCAL (temp _s p; temp _c (vint c); temp _n (vint (4 * n)%Z))
   SEP (data_at_ sh t p)
  POST [ tptr tvoid ]
   PROP ()
   LOCAL (temp ret_temp p)
   SEP (data_at sh (tarray tint n) (repeat (vint c) (Z.to_nat n)) p).

Definition N := 3.
Definition B := N + 2.

Definition tbuffer := Tstruct _buffer noattr.

Definition Empty := vint (-1).

(* operations on histories *)
Fixpoint find_read h d :=
  match h with
  | [] => (d, [])
  | AE r w :: rest => if eq_dec w Empty then if eq_dec r Empty then find_read rest d
                      else (r, rest) else find_read rest d
  end.

Definition last_two_reads h := let '(b1, rest) := find_read h (vint 1) in (b1, fst (find_read rest (vint 1))).

Fixpoint find_write h d :=
  match h with
  | [] => (d, [])
  | AE r w :: rest => if eq_dec w Empty then find_write rest d else (w, rest)
  end.

Definition prev_taken h := fst (find_read (snd (find_write h (vint 0))) (vint 1)).

Definition last_write h := fst (find_write h (vint 0)).

(* This is the invariant for the location buffers comm[N]. *)
(* The ghost variables are the last value read, the last value written, and the last value read before
   the last write (i.e., last_taken). The first is updated by the reader, the rest by the writer. *)
Definition comm_R bufs sh gsh g0 g1 g2 h v := EX b : Z, EX b1 : Z, EX b2 : Z,
  !!(v = vint b /\ -1 <= b < B /\
     Forall (fun a => match a with AE v1 v2 =>
       exists r w, v1 = vint r /\ v2 = vint w /\ -1 <= r < B /\ -1 <= w < B end) h /\
     last_two_reads (rev h) = (vint b1, vint b2) /\ repable_signed b1 /\ repable_signed b2) &&
  ghost_var gsh (vint b1) g0 * ghost_var gsh (last_write (rev h)) g1 *
  ghost_var gsh (prev_taken (rev h)) g2 *
  if eq_dec b (-1) then EX v : Z, data_at sh tbuffer (vint v) (Znth b2 bufs Vundef)
  else EX v : Z, data_at sh tbuffer (vint v) (Znth b bufs Vundef).

Definition comm_loc lsh lock comm g g0 g1 g2 bufs sh gsh :=
  AE_loc lsh lock comm g (vint 0) (comm_R bufs sh gsh g0 g1 g2).

(* messaging system function specs *)
Definition initialize_channels_spec :=
 DECLARE _initialize_channels
  WITH comm : val, lock : val, buf : val, reading : val, last_read : val, sh1 : share, shs : list share
  PRE [ ]
   PROP (Zlength shs = N; sepalg_list.list_join sh1 shs Tsh)
   LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs buf; gvar _reading reading; gvar _last_read last_read)
   SEP (data_at_ Ews (tarray (tptr tint) N) comm; data_at_ Ews (tarray (tptr tlock) N) lock;
        data_at_ Ews (tarray (tptr tbuffer) B) buf;
        data_at_ Ews (tarray (tptr tint) N) reading; data_at_ Ews (tarray (tptr tint) N) last_read)
  POST [ tvoid ]
   EX comms : list val, EX locks : list val, EX bufs : list val, EX reads : list val, EX lasts : list val,
     EX g : list val, EX g0 : list val, EX g1 : list val, EX g2 : list val,
   PROP (Forall isptr comms; Zlength g = N; Zlength g0 = N; Zlength g1 = N; Zlength g2 = N)
   LOCAL ()
   SEP (data_at Ews (tarray (tptr tint) N) comms comm;
        data_at Ews (tarray (tptr tlock) N) locks lock;
        data_at Ews (tarray (tptr tbuffer) B) bufs buf;
        data_at Ews (tarray (tptr tint) N) reads reading;
        data_at Ews (tarray (tptr tint) N) lasts last_read;
        fold_right sepcon emp (map (fun r =>
          comm_loc Tsh (Znth r locks Vundef) (Znth r comms Vundef) (Znth r g Vundef) (Znth r g0 Vundef)
            (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh) gsh2 ([] : hist)) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g0);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) comms);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tlock)) locks);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) reads);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) lasts);
        data_at sh1 tbuffer (vint 0) (Znth 0 bufs Vundef);
        fold_right sepcon emp (map (data_at Tsh tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs));
        fold_right sepcon emp (map (data_at_ Tsh tint) reads);
        fold_right sepcon emp (map (data_at_ Tsh tint) lasts)).
(* All the communication channels are now inside locks. Buffer 0 also starts distributed among the channels. *)

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

Definition latest_read (h : hist) v :=
  (* initial condition *)
  (Forall (fun x => let '(_, AE r w) := x in w = Empty -> r = Empty) h /\ v = vint 1) \/
  v <> Empty /\ exists n, In (n, AE v Empty) h /\
  Forall (fun x => let '(m, AE r w) := x in w = Empty -> r <> Empty -> m <= n)%nat h.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0,
               x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
             P at level 100, Q at level 100).

(* last_read retains the last buffer read, while reading is reset to Empty. *)
Definition start_read_spec :=
 DECLARE _start_read
  WITH r : Z, reading : val, last_read : val, lock : val, comm : val, reads : list val, lasts : list val,
    locks : list val, comms : list val, bufs : list val, sh : share, sh1 : share, sh2 : share, b0 : Z,
    g : val, g0 : val, g1 : val, g2 : val, h : hist
  PRE [ _r OF tint ]
   PROP (0 <= b0 < B; readable_share sh; readable_share sh1; readable_share sh2; isptr (Znth r comms Vundef); latest_read h (vint b0))
   LOCAL (temp _r (vint r); gvar _reading reading; gvar _last_read last_read; gvar _lock lock; gvar _comm comm)
   SEP (data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
        data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at_ Tsh tint (Znth r reads Vundef); data_at Tsh tint (vint b0) (Znth r lasts Vundef);
        comm_loc sh2 (Znth r locks Vundef) (Znth r comms Vundef) g g0 g1 g2 bufs sh gsh2 h;
        EX v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs Vundef);
        ghost_var gsh1 (vint b0) g0)
  POST [ tint ]
   EX b : Z, EX t : nat, EX v0 : val, EX v : Z,
   PROP (0 <= b < B; if eq_dec v0 Empty then b = b0 else v0 = vint b;
         latest_read (h ++ [(t, AE v0 Empty)]) (vint b))
   LOCAL (temp ret_temp (vint b))
   SEP (data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
        data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at Tsh tint (vint b) (Znth r reads Vundef); data_at Tsh tint (vint b) (Znth r lasts Vundef);
        comm_loc sh2 (Znth r locks Vundef) (Znth r comms Vundef) g g0 g1 g2 bufs sh gsh2 (h ++ [(t, AE v0 Empty)]);
        data_at sh tbuffer (vint v) (Znth b bufs Vundef);
        ghost_var gsh1 (vint b) g0).
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
  WITH writing : val, last_given : val, last_taken : val, b0 : Z, lasts : list Z
  PRE [ ]
   PROP (0 <= b0 < B; Forall (fun x => 0 <= x < B) lasts)
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
   SEP (data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken)
  POST [ tint ]
   EX b : Z,
   PROP (0 <= b < B; b <> b0; ~In b lasts)
   LOCAL (temp ret_temp (vint b))
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken).
(* And b is not in use by any reader. This follows from the property on lasts. *)

(* make_shares returns the elements of shs for which the corresponding element of lasts is not i. *)
Fixpoint make_shares shs (lasts : list Z) i : list share :=
  match lasts with
  | [] => []
  | b :: rest => if eq_dec b i then make_shares (tl shs) rest i
                 else hd Share.bot shs :: make_shares (tl shs) rest i
  end.

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 , x10 : t10 , x11 : t11 , x12 : t12 , x13 : t13 , x14 : t14 , x15 : t15 , x16 : t16 , x17 : t17 , x18 : t18 , x19 : t19 , x20 : t20 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (NDmk_funspec (nil, tz) cc_default (t1*t2*t3*t4*t5*t6*t7*t8*t9*t10*t11*t12*t13*t14*t15*t16*t17*t18*t19*t20)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => P%assert end)
           (fun x => match x with (x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20) => Q%assert end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0,
             x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
              x10 at level 0, x11 at level 0, x12 at level 0,  x13 at level 0, x14 at level 0,
               x15 at level 0, x16 at level 0, x17 at level 0, x18 at level 0, x19 at level 0,
                x20 at level 0,
             P at level 100, Q at level 100).

Definition finish_write_spec :=
 DECLARE _finish_write
  WITH writing : val, last_given : val, last_taken : val, comm : val, lock : val,
    comms : list val, locks : list val, bufs : list val, b : Z, b0 : Z, lasts : list Z,
    sh1 : share, lsh : share, shs : list share, g : list val, g0 : list val, g1 : list val, g2 : list val,
    h : list hist, sh0 : share
  PRE [ ]
   PROP (0 <= b < B; 0 <= b0 < B; Forall (fun x => 0 <= x < B) lasts; Zlength h = N; Zlength shs = N;
         readable_share sh1; readable_share lsh; Forall readable_share shs;
         sepalg_list.list_join sh0 shs Tsh; Forall isptr comms; b <> b0; ~In b lasts; ~In b0 lasts)
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _comm comm;
          gvar _lock lock)
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        fold_right sepcon emp (map (fun r =>
          comm_loc lsh (Znth r locks Vundef) (Znth r comms Vundef) (Znth r g Vundef) (Znth r g0 Vundef)
            (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh) gsh2 (Znth r h [])) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun r => ghost_var gsh1 (vint b0) (Znth r g1 Vundef) *
          ghost_var gsh1 (vint (Znth r lasts (-1))) (Znth r g2 Vundef)) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i b0 then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts i) sh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B))))
  POST [ tvoid ]
   EX lasts' : list Z, EX h' : list hist,
   PROP (Forall (fun x => 0 <= x < B) lasts';
         Forall2 (fun h1 h2 => exists t v, h2 = h1 ++ [(t, AE v (vint b))]) h h';
         ~In b lasts')
   LOCAL ()
   SEP (data_at Ews tint Empty writing; data_at Ews tint (vint b) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts') last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        fold_right sepcon emp (map (fun r =>
          comm_loc lsh (Znth r locks Vundef) (Znth r comms Vundef) (Znth r g Vundef) (Znth r g0 Vundef)
            (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh) gsh2 (Znth r h' [])) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun r => ghost_var gsh1 (vint b) (Znth r g1 Vundef) *
          ghost_var gsh1 (vint (Znth r lasts' (-1))) (Znth r g2 Vundef)) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i b then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts' i) sh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B)))).

(* client function specs *)
Definition reader_spec :=
 DECLARE _reader
  WITH arg : val, x : Z * val * val * val * val * val * list val * list val * list val * list val * list val *
                      share * share * share * val * val * val * val
  PRE [ _arg OF tptr tvoid ]
   let '(r, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs, sh1, sh2, sh, g, g0, g1, g2) := x in
   PROP (readable_share sh; readable_share sh1; readable_share sh2; isptr (Znth r comms Vundef))
   LOCAL (temp _arg arg; gvar _reading reading; gvar _last_read last_read;
          gvar _lock lock; gvar _comm comm; gvar _bufs buf)
   SEP (data_at Tsh tint (vint r) arg; malloc_token Tsh (sizeof tint) arg;
        data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
        data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at_ Tsh tint (Znth r reads Vundef); data_at_ Tsh tint (Znth r lasts Vundef);
        data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
        comm_loc sh2 (Znth r locks Vundef) (Znth r comms Vundef) g g0 g1 g2 bufs sh gsh2 [];
        EX v : Z, data_at sh tbuffer (vint v) (Znth 1 bufs Vundef);
        ghost_var gsh1 (vint 1) g0)
  POST [ tptr tvoid ] PROP () LOCAL () SEP ().

Definition writer_spec :=
 DECLARE _writer
  WITH arg : val, x : val * val * val * val * val * val * list val * list val * list val * share * share *
                      share * list share * list val * list val * list val * list val
  PRE [ _arg OF tptr tvoid ]
   let '(writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs, g, g0, g1, g2) := x in
   PROP (Zlength shs = N; readable_share sh1; readable_share lsh; Forall readable_share shs;
         sepalg_list.list_join sh0 shs Tsh; Zlength g1 = N; Zlength g2 = N; Forall isptr comms)
   LOCAL (temp _arg arg; gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken;
          gvar _lock lock; gvar _comm comm; gvar _bufs buf)
   SEP (data_at_ Ews tint writing; data_at_ Ews tint last_given; data_at_ Ews (tarray tint N) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
        fold_right sepcon emp (map (fun r =>
          comm_loc lsh (Znth r locks Vundef) (Znth r comms Vundef) (Znth r g Vundef) (Znth r g0 Vundef)
            (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh) gsh2 []) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2);
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i 0 then sh = sh0 else if eq_dec i 1 then sh = sh0 else sh = Tsh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B))))
  POST [ tptr tvoid ] PROP () LOCAL () SEP ().

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog [] u
  POST [ tint ] main_post prog [] u.

(* Create the environment containing all function specs. *)
Definition Gprog : funspecs := ltac:(with_library prog [release_spec; makelock_spec; spawn_spec;
  surely_malloc_spec; memset_spec; atomic_exchange_spec; initialize_channels_spec; initialize_reader_spec;
  start_read_spec; finish_read_spec; initialize_writer_spec; start_write_spec; finish_write_spec;
  reader_spec; writer_spec; main_spec]).

Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.

(* Now we prove that each function satisfies its specification. *)

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec.
Proof.
  start_function.
  forward_call n.
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (malloc_token Tsh n p * memory_block Tsh n p)).
  - if_tac; entailer!.
  - forward_call tt.
    contradiction.
  - if_tac.
    + forward. subst p. discriminate.
    + Intros. forward. entailer!.
  - forward. Exists p; entailer!.
Qed.

Lemma body_memset : semax_body Vprog Gprog f_memset memset_spec.
Proof.
  start_function.
  forward.
  rewrite data_at__isptr; Intros.
  rewrite sem_cast_neutral_ptr; auto.
  pose proof (sizeof_pos t).
  assert (vint n = force_val (sem_div tuint tint (vint (4 * n)) (vint 4))) as H4.
  { unfold sem_div; simpl.
    unfold Int.divu.
    rewrite !Int.unsigned_repr; auto; try (split; auto; try computable; omega).
    rewrite Z.mul_comm, Z_div_mult; auto; computable. }
  forward_for_simple_bound n (EX i : Z, PROP ()
    LOCAL (temp _p p; temp _s p; temp _c (vint c); temp _n (vint (4 * n)))
    SEP (data_at sh (tarray tint n) (repeat (vint c) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (n - i))) p)).
  { entailer!.
    { rewrite H4; auto. }
    apply derives_trans with (Q := data_at_ sh (tarray tint n) p).
    - rewrite !data_at__memory_block; simpl.
      assert ((4 * Z.max 0 n)%Z = sizeof t) as Hsize.
      { rewrite Z.max_r; auto; omega. }
      setoid_rewrite Hsize; Intros; apply andp_right; [|simpl; apply derives_refl].
      apply prop_right; match goal with H : field_compatible _ _ _ |- _ =>
        destruct H as (? & ? & ? & ? & ? & ? & ? & ?) end; repeat split; simpl; auto.
      + unfold legal_alignas_type, tarray, nested_pred, local_legal_alignas_type; simpl.
        rewrite andb_true_r, Z.leb_le; omega.
      + setoid_rewrite Hsize; auto.
      + unfold size_compatible in *; simpl.
        destruct p; try contradiction.
        setoid_rewrite Hsize; auto.
      + unfold align_compatible in *; simpl.
        unfold align_attr in *; simpl.
        destruct p; try contradiction.
        etransitivity; eauto.
    - rewrite data_at__eq.
      unfold default_val, reptype_gen; simpl.
      rewrite repeat_list_repeat, Z.sub_0_r; apply derives_refl. }
  - forward.
    rewrite upd_init_const; [|omega].
    entailer!.
    rewrite H4; auto.
  - forward.
    rewrite Zminus_diag, app_nil_r; apply derives_refl.
Qed.

Lemma lock_struct_array : forall sh z (v : list val) p,
  data_at sh (tarray (tptr (Tstruct _lock_t noattr)) z) v p =
  data_at sh (tarray (tptr tlock) z) v p.
Proof.
  intros.
  unfold data_at, field_at, at_offset; rewrite !data_at_rec_eq; simpl; f_equal.
Qed.

Lemma Empty_inj : forall i, vint i = Empty -> repable_signed i -> i = -1.
Proof.
  intros; apply repr_inj_signed; auto.
  unfold Empty in *; congruence.
Qed.

Lemma repable_buf : forall a, -1 <= a < B -> repable_signed a.
Proof.
  intros ? (? & ?).
  split; [transitivity (-1) | transitivity B]; unfold B, N in *; try computable; auto; omega.
Qed.

Lemma comm_R_precise : forall bufs sh gsh g0 g1 g2 h v,
  TT |-- weak_precise_mpred (comm_R bufs sh gsh g0 g1 g2 h v).
Proof.
  unfold comm_R; intros; apply precise_weak_precise.
  apply derives_precise' with (Q := EX b : Z, EX b2 : Z, !!(repable_signed b /\ repable_signed b2 /\
    v = vint b /\ snd (last_two_reads (rev h)) = vint b2) &&
    ((EX v : val, ghost_var gsh v g0) * (EX v : val, ghost_var gsh v g1) * (EX v : val, ghost_var gsh v g2) *
     data_at_ sh tbuffer (Znth (if eq_dec v Empty then b2 else b) bufs Vundef))).
  { Intros b b1 b2.
    assert (repable_signed b) by (apply repable_buf; auto).
    Exists b b2 (vint b1) (prev_taken (rev h)) (last_write (rev h)); entailer!.
    { replace (last_two_reads (rev h)) with (vint b1, vint b2); auto. }
    destruct (eq_dec (vint b) Empty).
    - apply Empty_inj in e; auto.
      subst; rewrite eq_dec_refl; entailer!.
    - destruct (eq_dec b (-1)); [subst; contradiction n; auto | entailer!]. }
  intros ??? (b & b2 & (? & ? & ? & ?) & ?) (b' & b2' & (? & ? & ? & ?) & ?); subst.
  assert (b = b' /\ b2 = b2') as (? & ?) by (split; apply repr_inj_signed; auto; congruence).
  subst.
  assert (precise ((EX v : val, ghost_var gsh v g0) * (EX v : val, ghost_var gsh v g1) *
        (EX v : val, ghost_var gsh v g2) *
        data_at_ sh tbuffer (Znth (if eq_dec (vint b') Empty then b2' else b') bufs Vundef))) as Hp;
    [|apply Hp; auto].
  repeat apply precise_sepcon; auto.
Qed.

Opaque upto.

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
    forward_call (Tsh, tbuffer, b, 0, 1).
    { repeat split; simpl; auto; try computable.
      apply Z.divide_refl. }
    forward.
    rewrite upd_init; auto; try omega.
    entailer!.
    Exists (bufs ++ [b]); rewrite Zlength_app, <- app_assoc, !map_app, !sepcon_app, Forall_app; simpl; entailer!.
    clear; unfold data_at, field_at, at_offset; Intros.
    rewrite !data_at_rec_eq; unfold withspacer; simpl.
    unfold array_pred, aggregate_pred.array_pred, unfold_reptype; simpl.
    entailer!.
    { exists 2; auto. } }
  Intros bufs; rewrite Zminus_diag, app_nil_r.
  forward_for_simple_bound N (EX i : Z, PROP ()
    LOCAL (gvar _comm comm; gvar _lock lock; gvar _bufs buf; gvar _reading reading; gvar _last_read last_read)
    SEP (EX locks : list val, EX comms : list val, EX g : list val, EX g0 : list val, EX g1 : list val,
         EX g2 : list val, !!(Zlength locks = i /\ Zlength comms = i /\ Forall isptr comms /\ Zlength g = i /\
           Zlength g0 = i /\ Zlength g1 = i /\ Zlength g2 = i) &&
          (data_at Ews (tarray (tptr tlock) N) (locks ++ repeat Vundef (Z.to_nat (N - i))) lock *
           data_at Ews (tarray (tptr tint) N) (comms ++ repeat Vundef (Z.to_nat (N - i))) comm *
           fold_right sepcon emp (map (fun r => comm_loc Tsh (Znth r locks Vundef) (Znth r comms Vundef)
             (Znth r g Vundef) (Znth r g0 Vundef) (Znth r g1 Vundef) (Znth r g2 Vundef) bufs
             (Znth r shs Tsh) gsh2 []) (upto (Z.to_nat i))) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tlock)) locks)) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g0) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2) *
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
         EX sh : share, !!(sepalg_list.list_join sh1 (sublist i N shs) sh) &&
           @data_at CompSpecs sh tbuffer (vint 0) (Znth 0 bufs Vundef);
         fold_right sepcon emp (map (@data_at CompSpecs Tsh tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs));
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs))).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists ([] : list val) ([] : list val) ([] : list val) ([] : list val) ([] : list val) ([] : list val)
      ([] : list val) ([] : list val) Tsh; rewrite !data_at__eq; entailer!.
    - rewrite sublist_same; auto; omega.
    - erewrite <- sublist_same with (al := bufs), sublist_next at 1; eauto; try (unfold B, N in *; omega).
      simpl; cancel. }
  { Intros locks comms g g0 g1 g2 reads lasts sh.
    forward_malloc tint c.
    forward.
    forward.
    forward_malloc tint rr.
    forward.
    forward_malloc tint ll.
    forward.
    forward_malloc tlock l.
    rewrite <- lock_struct_array.
    forward.
    eapply (ghost_alloc (Tsh, vint 1)); auto with init.
    eapply (ghost_alloc (Tsh, vint 0)); auto with init.
    eapply (ghost_alloc (Tsh, vint 1)); auto with init.
    eapply (ghost_alloc (Some (Tsh, [] : hist), Some ([] : hist))); auto with init.
    Intros g' g0' g1' g2'.
    forward_call (l, Tsh, AE_inv c g' (vint 0) (comm_R bufs (Znth i shs Tsh) gsh2 g0' g1' g2')).
    rewrite <- hist_ref_join_nil by (apply Share.nontrivial).
    fold (ghost_var Tsh (vint 1) g0') (ghost_var Tsh (vint 0) g1') (ghost_var Tsh (vint 1) g2').
    erewrite <- !ghost_var_share_join with (sh0 := Tsh) by eauto.
    match goal with H : sepalg_list.list_join sh1 (sublist i N shs) sh |- _ =>
      erewrite sublist_next in H; try omega; inversion H as [|????? Hj1 Hj2] end.
    apply sepalg.join_comm in Hj1; eapply sepalg_list.list_join_assoc1 in Hj2; eauto.
    destruct Hj2 as (sh' & ? & Hsh').
    erewrite <- data_at_share_join with (sh0 := sh) by (apply Hsh').
    forward_call (l, Tsh, AE_inv c g' (vint 0) (comm_R bufs (Znth i shs Tsh) gsh2 g0' g1' g2')).
    { entailer!. }
    { entailer!. }
    { rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
        [repeat apply andp_right; auto; eapply derives_trans; try apply positive_weak_positive; auto|].
      { apply AE_inv_precise; auto. }
      fast_cancel.
      unfold AE_inv.
      Exists (@nil AE_hist_el) (vint 0).
      unfold comm_R at 1.
      Exists 0 1 1; unfold last_two_reads, last_write, prev_taken; simpl.
      rewrite !sepcon_andp_prop', !sepcon_andp_prop, !sepcon_andp_prop'; apply andp_right;
        [apply prop_right; auto|].
      apply andp_right; [apply prop_right; repeat (split; auto); computable|].
      Exists 0; fast_cancel.
      rewrite <- emp_sepcon at 1; apply sepcon_derives.
      { apply andp_right; auto; eapply derives_trans; [|apply comm_R_precise]; auto. }
      cancel_frame. }
    Exists (locks ++ [l]) (comms ++ [c]) (g ++ [g']) (g0 ++ [g0']) (g1 ++ [g1']) (g2 ++ [g2'])
      (reads ++ [rr]) (lasts ++ [ll]) sh'; rewrite !upd_init; try omega.
    rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; rewrite <- !app_assoc.
    go_lower.
    apply andp_right; [apply prop_right; split; auto; omega|].
    apply andp_right; [apply prop_right; repeat split; auto|].
    rewrite !sepcon_andp_prop'; apply andp_right; [apply prop_right; rewrite Forall_app; repeat split; auto;
      omega|].
    rewrite !sepcon_andp_prop; repeat (apply andp_right; [apply prop_right; auto; try omega|]).
    rewrite Z2Nat.inj_add, upto_app, !map_app, !sepcon_app; try omega; simpl.
    change (upto 1) with [0]; simpl.
    rewrite Z2Nat.id, Z.add_0_r by omega.
    rewrite !Znth_app1 by auto.
    replace (Z.to_nat (N - (Zlength locks + 1))) with (Z.to_nat (N - (i + 1))) by (subst; clear; Omega0).
    subst; rewrite Zlength_correct, Nat2Z.id.
    rewrite <- lock_struct_array; unfold AE_inv.
    rewrite !sem_cast_neutral_ptr by auto.
    erewrite map_ext_in; [cancel|].
    { rewrite sepcon_comm; apply sepcon_derives; auto. }
    intros; rewrite In_upto, <- Zlength_correct in *.
    rewrite !app_Znth1; try omega; reflexivity. }
  Intros locks comms g g0 g1 g2 reads lasts sh.
  match goal with H : sepalg_list.list_join sh1 (sublist N N shs) sh |- _ =>
    rewrite sublist_nil in H; inv H end.
  forward.
  rewrite !app_nil_r.
  Exists comms locks bufs reads lasts g g0 g1 g2.
  (* entailer! is slow *)
  apply andp_right; auto.
  apply andp_right; [apply prop_right; repeat (split; auto)|].
  apply andp_right; auto; cancel.
Qed.

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

Lemma last_two_reads_cons : forall r w h, last_two_reads (AE r w :: h) =
  if eq_dec w Empty then if eq_dec r Empty then last_two_reads h else (r, fst (last_two_reads h))
  else last_two_reads h.
Proof.
  intros; unfold last_two_reads; simpl.
  destruct (eq_dec w Empty); auto.
  destruct (eq_dec r Empty); auto.
  destruct (find_read h (vint 1)); auto.
Qed.

Lemma prev_taken_cons : forall r w h, prev_taken (AE r w :: h) =
  if eq_dec w Empty then prev_taken h else fst (find_read h (vint 1)).
Proof.
  intros; unfold prev_taken; simpl.
  destruct (eq_dec w Empty); auto.
Qed.

Lemma find_read_pos : forall d h, d <> Empty -> fst (find_read h d) <> Empty.
Proof.
  induction h; auto; simpl; intro.
  destruct a.
  destruct (eq_dec w Empty); eauto.
  destruct (eq_dec r Empty); eauto.
Qed.

Corollary last_two_reads_fst : forall h, fst (last_two_reads h) <> Empty.
Proof.
  intro; unfold last_two_reads.
  pose proof (find_read_pos (vint 1) h); destruct (find_read h (vint 1)).
  simpl in *; apply H; discriminate.
Qed.

Lemma find_read_In : forall d h, In (AE (fst (find_read h d)) Empty) (AE d Empty :: h).
Proof.
  induction h; simpl; intros; auto.
  destruct a.
  destruct (eq_dec w Empty); [|destruct IHh; auto].
  destruct (eq_dec r Empty); [destruct IHh; auto|].
  subst; auto.
Qed.

Corollary last_two_reads_In1 : forall h, In (AE (fst (last_two_reads h)) Empty) (AE (vint 1) Empty :: h).
Proof.
  unfold last_two_reads; intros.
  pose proof (find_read_In (vint 1) h).
  destruct (find_read h (vint 1)) eqn: Hfind; auto.
Qed.

Lemma find_read_incl : forall a d h, In a (snd (find_read h d)) -> In a h.
Proof.
  induction h; auto; simpl.
  destruct a0.
  destruct (eq_dec w Empty); auto.
  destruct (eq_dec r Empty); auto.
Qed.

Corollary last_two_reads_In2 : forall h, In (AE (snd (last_two_reads h)) Empty) (AE (vint 1) Empty :: h).
Proof.
  unfold last_two_reads; intros.
  destruct (find_read h (vint 1)) eqn: Hfind.
  destruct (find_read_In (vint 1) l); simpl in *; auto.
  right; eapply find_read_incl; rewrite Hfind; auto.
Qed.

Lemma latest_read_Empty : forall h n v, latest_read (h ++ [(n, AE Empty Empty)]) v <-> latest_read h v.
Proof.
  unfold latest_read; split; intros [(Hnone & ?) | (? & m & Hin & Hlatest)]; subst.
  - rewrite Forall_app in Hnone; destruct Hnone; auto.
  - right; split; auto; exists m.
    rewrite in_app in Hin; destruct Hin as [? | [X | ?]]; [| inv X; contradiction H; auto | contradiction].
    split; auto.
    rewrite Forall_app in Hlatest; destruct Hlatest; auto.
  - rewrite Forall_app; auto.
  - right; split; auto; exists m.
    rewrite in_app; split; auto.
    rewrite Forall_app; split; auto.
    constructor; auto; contradiction.
Qed.

Lemma latest_read_new : forall h n v, Forall (fun x => fst x < n)%nat h -> v <> Empty ->
  latest_read (h ++ [(n, AE v Empty)]) v.
Proof.
  unfold latest_read; intros.
  right; split; auto; exists n.
  rewrite in_app; simpl; split; auto.
  rewrite Forall_app; split; auto.
  eapply Forall_impl; [|eauto]; intros.
  destruct a, a; simpl in *; omega.
Qed.

Lemma comm_loc_isptr : forall lsh l c g g0 g1 g2 b sh gsh h,
  comm_loc lsh l c g g0 g1 g2 b sh gsh h = !!(isptr l) && comm_loc lsh l c g g0 g1 g2 b sh gsh h.
Proof.
  intros; eapply local_facts_isptr with (P := fun l => _); [|eauto].
  unfold comm_loc, AE_loc.
  rewrite lock_inv_isptr; entailer!.
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
  rewrite comm_loc_isptr; Intros.
  rewrite <- lock_struct_array.
  forward.
  forward.
  forward.
  set (c := Znth r comms Vundef).
  set (l := Znth r locks Vundef).
  forward_call (sh2, c, g, l, vint 0, Empty, h,
    fun h b => !!(b = Empty /\ latest_read h (vint b0)) &&
      (EX v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs Vundef)) * ghost_var gsh1 (vint b0) g0,
    comm_R bufs sh gsh2 g0 g1 g2, fun h b => EX b' : Z, !!((if eq_dec b Empty then b' = b0 else b = vint b') /\
      -1 <= b' < B /\ latest_read h (vint b')) &&
      (EX v : Z, data_at sh tbuffer (vint v) (Znth b' bufs Vundef)) * ghost_var gsh1 (vint b') g0).
  { repeat (split; auto); try computable.
    unfold AE_spec; intros.
    intros ??????? Ha.
    unfold comm_R; unfold comm_R at 1 in Ha.
    rewrite !rev_app_distr in Ha; simpl in Ha.
    rewrite !last_two_reads_cons, prev_taken_cons in Ha.
    unfold last_write in *; simpl in *.
    pose proof (last_two_reads_fst (rev hx)).
    rewrite flatten_sepcon_in_SEP.
    rewrite extract_exists_in_SEP; Intro b.
    rewrite extract_exists_in_SEP; Intro b1.
    rewrite extract_exists_in_SEP; Intro b2.
    rewrite <- flatten_sepcon_in_SEP.
    rewrite !sepcon_andp_prop', !sepcon_andp_prop.
    erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
    erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
    Intros; subst.
    assert (last_two_reads (rev hx) = (vint b1, vint b2)) as Hlast by assumption.
    rewrite <- sepcon_assoc, sepcon_comm, <- !sepcon_assoc, 3sepcon_assoc.
    assert_PROP (vint b1 = vint b0) as Hb1.
    { go_lowerx.
      do 2 apply sepcon_derives_prop.
      rewrite sepcon_comm; apply ghost_var_inj; auto. }
    rewrite Hb1 in *; erewrite ghost_var_share_join; eauto.
    rewrite flatten_sepcon_in_SEP.
    apply ghost_var_update with (v' := vint (if eq_dec (vint b) Empty then b0 else b)).
    eapply semax_pre, Ha.
    go_lowerx.
    assert (repable_signed b0) by (apply repable_buf; omega).
    rewrite (sepcon_comm _ (weak_precise_mpred _ && _)).
    rewrite <- emp_sepcon at 1; rewrite !sepcon_assoc; apply sepcon_derives.
    { apply andp_right; auto; eapply derives_trans; [|apply comm_R_precise]; auto. }
    Exists (-1) (if eq_dec (vint b) Empty then b0 else b) (if eq_dec (vint b) Empty then b2 else b0).
    rewrite !sepcon_andp_prop'.
    apply andp_right.
    { apply prop_right; repeat (split; [solve [auto; omega]|]).
      rewrite Forall_app; split; [split; [|constructor]; auto|].
      { repeat eexists; auto; omega. }
      destruct (eq_dec (vint b) Empty); rewrite Hlast; auto.
      split; [|split]; auto; apply repable_buf; auto. }
    erewrite <- ghost_var_share_join; eauto.
    rewrite eq_dec_refl; cancel.
    setoid_rewrite sepcon_comm at 3.
    Exists (if eq_dec (vint b) Empty then b0 else b).
    destruct (eq_dec (vint b) Empty).
    - assert (b = -1) by (apply Empty_inj; auto; apply repable_buf; auto).
      subst; rewrite eq_dec_refl; entailer!.
      rewrite latest_read_Empty; auto.
    - destruct (eq_dec b (-1)); [subst; contradiction n; auto|].
      entailer!.
      apply latest_read_new; auto.
      apply hist_incl_lt; auto. }
  Intros x b'; destruct x as (t, v); simpl in *.
  assert (exists b, v = vint b /\ -1 <= b < B /\ if eq_dec b (-1) then b' = b0 else b' = b) as (b & ? & ? & ?).
  { destruct (eq_dec v Empty); subst.
    - exists (-1); rewrite eq_dec_refl; split; auto; omega.
    - do 2 eexists; eauto; split; [omega|].
      destruct (eq_dec b' (-1)); [subst; contradiction n; auto | auto]. }
  exploit repable_buf; eauto; intro; subst.
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
    SEP (comm_loc sh2 l c g g0 g1 g2 bufs sh gsh2 (h ++ [(t, AE (vint b) Empty)]);
         EX v : Z, data_at sh tbuffer (vint v) (Znth (if eq_dec b (-1) then b0 else b) bufs Vundef);
         ghost_var gsh1 (vint b') g0;
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
    Exists (if eq_dec b (-1) then b0 else b) t (vint b) v.
    apply andp_right.
    { apply prop_right.
      split; [destruct (eq_dec b (-1)); auto; omega|].
      destruct (eq_dec (vint b) Empty).
      + assert (b = -1) by (apply Empty_inj; auto).
        subst; rewrite eq_dec_refl; auto.
      + destruct (eq_dec b (-1)); [subst; contradiction n; auto|].
        split; auto; split; auto; apply latest_read_new; auto. }
    apply andp_right; [apply prop_right; auto|].
    rewrite lock_struct_array; subst c l; cancel.
    destruct (eq_dec b (-1)); subst; auto.
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
        data_at Ews (tarray tint N) (repeat (vint 1) (Z.to_nat i) ++ repeat Vundef (Z.to_nat (N - i))) last_taken)).
  { unfold N; computable. }
  { unfold N; computable. }
  { entailer!. }
  - forward.
    rewrite upd_init_const; auto.
    entailer!.
  - forward.
Qed.

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
    rewrite upd_Znth_eq with (d := Vundef); simpl; [|rewrite !Zlength_cons, Zlength_nil; unfold B, N in *; omega].
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
    forward_if (PROP ( )
      LOCAL (temp _last (vint (Znth i lasts 0)); temp _r (vint i); temp _i (vint B); lvar _available (tarray tint 5) lvar0; 
             gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint B) [] (map (fun x => vint (if eq_dec x b0 then 0
             else if in_dec eq_dec x (sublist 0 (i + 1) lasts) then 0 else 1)) (upto (Z.to_nat B))) lvar0;
           data_at_ Ews tint writing; data_at Ews tint (vint b0) last_given;
           data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    - assert (0 <= Znth i lasts 0 < B) by (apply Forall_Znth; auto).
      forward.
      entailer!.
      rewrite upd_Znth_eq with (d := Vundef); [|auto].
      apply derives_refl'; erewrite map_ext_in; [reflexivity|].
      intros; rewrite In_upto, map_length, upto_length in *; simpl in *.
      erewrite Znth_map, Znth_upto; simpl; auto; try omega.
      erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1 with (d := 0); auto; try omega.
      destruct (in_dec eq_dec a (sublist 0 i lasts ++ [Znth i lasts 0])); rewrite in_app in *.
      + destruct (eq_dec a (Znth i lasts 0)); destruct (eq_dec a b0); auto.
        destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        destruct i0 as [? | [? | ?]]; subst; try contradiction.
      + destruct (eq_dec a (Znth i lasts 0)).
        { subst; contradiction n; simpl; auto. }
        destruct (eq_dec a b0); auto.
        destruct (in_dec eq_dec a (sublist 0 i lasts)); auto; contradiction n; auto.
    - forward.
      entailer!.
      apply derives_refl'; erewrite map_ext_in; [reflexivity|].
      intros; rewrite In_upto in *; simpl in *.
      destruct (eq_dec a b0); auto.
      erewrite sublist_split with (mid := i)(hi := i + 1), sublist_len_1 with (d := 0); auto; try omega.
      match goal with H : Int.repr _ = Int.neg _ |- _ => apply repr_inj_signed in H end.
      destruct (in_dec eq_dec a (sublist 0 i lasts ++ [Znth i lasts 0])); rewrite in_app in *.
      + destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        destruct i0 as [? | [? | ?]]; subst; try contradiction.
        rewrite Int.unsigned_repr in *; try computable; omega.
      + destruct (in_dec eq_dec a (sublist 0 i lasts)); auto.
        contradiction n0; auto.
      + apply Forall_Znth; auto.
        eapply Forall_impl; [|eauto]; unfold repable_signed; intros.
        split; [transitivity 0 | transitivity B]; unfold B, N in *; try computable; try omega.
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
    { unfold B, N in *; apply prop_right; omega. }
    { entailer!.
      subst available; apply Forall_Znth; [rewrite Zlength_map, Zlength_upto; unfold B, N in *; simpl; omega|].
      rewrite Forall_forall; intros ? Hin.
      rewrite in_map_iff in Hin; destruct Hin as (? & ? & ?); subst; simpl; auto. }
    forward_if (PROP (Znth i available (vint 0) = vint 0)
      LOCAL (temp _i__1 (vint i); lvar _available (tarray tint B) lvar0; gvar _writing writing;
             gvar _last_given last_given; gvar _last_taken last_taken)
      SEP (field_at Tsh (tarray tint B) [] available lvar0; data_at_ Ews tint writing;
           data_at Ews tint (vint b0) last_given; data_at Ews (tarray tint N) (map (fun x : Z => vint x) lasts) last_taken)).
    { forward.
      forward.
      Exists lvar0 i; entailer!.
      { subst available.
        match goal with H : typed_true _ _ |- _ => setoid_rewrite Znth_map in H; [rewrite Znth_upto in H|];
          try assumption; rewrite ?Zlength_upto, ?Z2Nat.id; try omega; unfold typed_true in H; simpl in H; inv H end.
        destruct (eq_dec i b0); [|destruct (in_dec eq_dec i lasts)]; auto; discriminate. }
      unfold data_at_, field_at_; entailer!. }
    { forward.
      entailer!.
      subst available.
      erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; try assumption; try omega.
      match goal with H : typed_false _ _ |- _ => setoid_rewrite Znth_map in H; [rewrite Znth_upto in H|];
        try assumption; rewrite ?Zlength_upto, ?Z2Nat.id; try omega; unfold typed_true in H; simpl in H; inv H end.
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
    unfold loop2_ret_assert.
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

Lemma find_write_rest : forall d h, exists n, snd (find_write h d) = skipn n h.
Proof.
  induction h; simpl; intros; try discriminate.
  { exists O; auto. }
  destruct a.
  destruct (eq_dec w Empty).
  - destruct IHh as (n & ?); subst.
    exists (S n); auto.
  - exists 1%nat; auto.
Qed.

Corollary prev_taken_In : forall h, prev_taken h = vint 1 \/ In (AE (prev_taken h) Empty) h.
Proof.
  intros; unfold prev_taken.
  destruct (find_read_In (vint 1) (snd (find_write h (vint 0)))).
  - inv H; auto.
  - destruct (find_write_rest (vint 0) h) as (? & Hrest); rewrite Hrest in *.
    right; eapply skipn_In; eauto.
Qed.

Lemma write_val : forall h i v (Hh : apply_hist i (rev h) = Some v), v = Empty \/ v = fst (find_write h i).
Proof.
  induction h; simpl; intros.
  { inv Hh; auto. }
  destruct a.
  rewrite apply_hist_app in Hh; simpl in Hh.
  destruct (apply_hist i (rev h)) eqn: Hh'; [|discriminate].
  destruct (eq_dec r v0); inv Hh.
  destruct (eq_dec v Empty); auto.
Qed.

Lemma find_write_read : forall i d h (Hread : apply_hist i (rev h) = Some Empty) (Hi : i <> Empty),
  fst (find_read h d) = fst (find_write h i).
Proof.
  induction h; auto; simpl; intros.
  { inv Hread; contradiction Hi; auto. }
  destruct a.
  rewrite apply_hist_app in Hread; simpl in Hread.
  destruct (apply_hist i (rev h)) eqn: Hh; [|discriminate].
  destruct (eq_dec r v); [subst | discriminate].
  inv Hread.
  rewrite !eq_dec_refl.
  destruct (eq_dec v Empty); eauto.
  exploit write_val; eauto; intros [? | ?]; subst; eauto; contradiction n; auto.
Qed.

Lemma take_read : forall h v, apply_hist (vint 0) (rev h) = Some v ->
  prev_taken h = if eq_dec v Empty then snd (last_two_reads h)
                 else fst (last_two_reads h).
Proof.
  induction h; simpl; intros.
  - inv H.
    destruct (eq_dec (vint 0) Empty); auto.
  - destruct a; rewrite prev_taken_cons, last_two_reads_cons.
    rewrite apply_hist_app in H; simpl in H.
    destruct (apply_hist (vint 0) (rev h)) eqn: Hh; [|discriminate].
    destruct (eq_dec r v0); [subst | discriminate].
    inv H.
    erewrite IHh; eauto.
    destruct (eq_dec v Empty).
    + destruct (eq_dec v0 Empty); auto.
    + unfold last_two_reads.
      destruct (find_read h (vint 1)); auto.
Qed.

Lemma find_write_In : forall d h, fst (find_write h d) = d \/ exists r, In (AE r (fst (find_write h d))) h.
Proof.
  induction h; auto; simpl; intros.
  destruct a.
  destruct (eq_dec w Empty); [destruct IHh as [|(? & ?)]|]; eauto.
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

(* The complement of make_shares. *)
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

Lemma data_at_buffer_cohere : forall sh1 sh2 v1 v2 p, readable_share sh1 ->
  data_at sh1 tbuffer v1 p * data_at sh2 tbuffer v2 p |--
  data_at sh1 tbuffer v1 p * data_at sh2 tbuffer v1 p.
Proof.
  intros; unfold data_at, field_at, at_offset; Intros.
  apply andp_right; [apply prop_right; auto|].
  rewrite !data_at_rec_eq; unfold withspacer, at_offset; simpl.
  rewrite !data_at_rec_eq; simpl.
  apply mapsto_value_cohere; auto.
Qed.

(* The relationship between the last_taken array and the shares held by the writer is
   preserved by the action of the loop body. *)
Lemma upd_write_shares : forall bufs b b0 lasts shs sh0 (Hb : 0 <= b < B) (Hb0 : 0 <= b0 < B)
  (Hlasts : Forall (fun x : Z => 0 <= x < B) lasts) (Hshs : Zlength shs = N)
  (Hread : Forall readable_share shs) (Hsh0 : sepalg_list.list_join sh0 shs Tsh)
  (Hdiff : b <> b0) (Hout : ~ In b lasts) (Hout0 : ~ In b0 lasts) (Hlasts : Zlength lasts = N)
  bsh' v' (Hv' : -1 <= v' < B) h' (Hh' : 0 <= Zlength h' < N)
  (Hbsh' : sepalg_list.list_join sh0 (sublist (Zlength h' + 1) N shs) bsh')
  bsh (Hbsh : sepalg.join bsh' (Znth (Zlength h') shs Tsh) bsh),
  (if eq_dec v' (-1) then
   EX v0 : Z, data_at (Znth (Zlength h') shs Tsh) tbuffer (vint v0) (Znth (Znth (Zlength h') lasts 0) bufs Vundef)
   else !! (v' = b0) && (EX v'0 : Z, data_at (Znth (Zlength h') shs Tsh) tbuffer (vint v'0) (Znth b0 bufs Vundef))) *
  ((EX v0 : Z, data_at bsh' tbuffer (vint v0) (Znth b bufs Vundef)) *
  fold_right sepcon emp (upd_Znth b (map (fun a => EX sh : share, !! (if eq_dec a b0 then
    sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
      (map (fun i : Z => if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) a) sh
      else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h') N shs) sh
      else sepalg_list.list_join sh0 (make_shares shs
      (map (fun i : Z => if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N))) a) sh) &&
      (EX v0 : Z, data_at sh tbuffer (vint v0) (Znth a bufs Vundef))) (upto (Z.to_nat B))) emp))
  |-- fold_right sepcon emp (map (fun a => EX sh : share, !! (if eq_dec a b0 then
        sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h' + 1)
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint v']) Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) a) sh
          else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h' + 1) N shs) sh
          else sepalg_list.list_join sh0 (make_shares shs
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint v']) Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N))) a) sh) &&
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
               (map (fun i => if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) a) sh
           else if eq_dec a b then sepalg_list.list_join sh0 (sublist (Zlength h') N shs) sh
           else sepalg_list.list_join sh0 (make_shares shs (map (fun i => if eq_dec (Znth i h' Vundef) Empty then b0
                                           else Znth i lasts 0) (upto (Z.to_nat N))) a) sh) &&
          (EX v1 : Z, @data_at CompSpecs sh tbuffer (vint v1) (Znth a bufs Vundef))) (upto (Z.to_nat B)))
          (EX v1 : Z, @data_at CompSpecs bsh' tbuffer (vint v1) (Znth b bufs Vundef))).
  assert (Zlength l0 = B).
  { subst l0; rewrite upd_Znth_Zlength; rewrite Zlength_map, Zlength_upto; auto. }
  assert (0 <= lasti < B).
  { apply Forall_Znth; auto; omega. }
  apply derives_trans with (fold_right sepcon emp (
    if eq_dec v' (-1) then upd_Znth lasti l0
            (EX sh : share, !!(exists sh', sepalg_list.list_join sh0 (make_shares shs
             (map (fun i => if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N))) lasti) sh' /\
             sepalg.join sh' shi sh) &&
            (EX v1 : Z, @data_at CompSpecs sh tbuffer (vint v1) (Znth lasti bufs Vundef)))
          else upd_Znth b0 l0 (EX sh : share, !!(exists sh', sepalg_list.list_join sh0 (make_shares shs
            (sublist 0 (Zlength h') (map (fun i => if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0)
            (upto (Z.to_nat N)))) b0) sh' /\ sepalg.join sh' shi sh) &&
            (EX v1 : Z, @data_at CompSpecs sh tbuffer (vint v1) (Znth b0 bufs Vundef))))).
  { rewrite replace_nth_sepcon.
    destruct (eq_dec v' (-1)).
    - rewrite extract_nth_sepcon with (i := lasti); [|subst l0; omega].
      erewrite upd_Znth_diff, Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; try omega.
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      Intros v1 ish v2.
      rewrite <- sepcon_assoc.
      eapply derives_trans; [apply sepcon_derives; [apply data_at_buffer_cohere; auto | apply derives_refl]|].
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
      rewrite <- sepcon_assoc.
      eapply derives_trans; [apply sepcon_derives; [apply data_at_buffer_cohere; auto | apply derives_refl]|].
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
  { destruct (eq_dec v' (-1)); auto; rewrite upd_Znth_Zlength; auto; omega. }
  apply list_Znth_eq' with (d := FF).
  { rewrite Hlen, Zlength_map, Zlength_upto; auto. }
  rewrite Hlen; intros.
  assert (0 <= j <= B) by omega.
  erewrite Znth_map, Znth_upto; auto.
  destruct (eq_dec j lasti); [|destruct (eq_dec j b0)]; subst.
  - destruct (eq_dec v' (-1)).
    + rewrite upd_Znth_same; [|omega].
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      exploit (make_shares_add lasti b0 0 (map (fun i => if eq_dec (Znth i h' Vundef) Empty then b0
        else Znth i lasts 0) (upto (Z.to_nat N))) (Zlength h') shs); auto.
      { erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; try omega.
        rewrite Znth_overflow; [|omega].
        destruct (eq_dec Vundef Empty); [discriminate | auto]. }
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
        destruct (eq_dec Vundef Empty); [discriminate|].
        destruct (eq_dec (vint v') Empty); [contradiction n | reflexivity].
        apply Empty_inj; auto; apply repable_buf; auto.
      * rewrite Znth_overflow, Znth_overflow with (al := h' ++ [vint v']); auto; [reflexivity|].
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
  - assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i h' Vundef) Empty then b0
      else Znth i lasts 0) (upto (Z.to_nat N)))) = Zlength h') as Hlenh.
    { rewrite Zlength_sublist; try omega.
      rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
    assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint v']) Vundef) Empty
      then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) = Zlength h') as Hlenh'.
    { rewrite Zlength_sublist; try omega.
      rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
    simpl in *.
    destruct (eq_dec v' (-1)).
    + assert (EX sh : share, !! sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h')
          (map (fun i : Z => if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) b0)
          sh && (EX v1 : Z, data_at sh tbuffer (vint v1) (Znth b0 bufs Vundef)) =
        EX sh : share, !! sepalg_list.list_join sh0 (make_shares shs (sublist 0 (Zlength h' + 1)
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint v']) Vundef) Empty then b0 else Znth i lasts 0)
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
      destruct (eq_dec (vint v') Empty).
      { contradiction n0; apply Empty_inj; auto; apply repable_buf; auto. }
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
    { destruct (eq_dec v' (-1)); rewrite upd_Znth_diff; auto; omega. }
    subst l0.
    destruct (eq_dec j b).
    + subst; rewrite upd_Znth_same; auto.
      apply mpred_ext.
      * Exists bsh'; entailer!.
      * Intros sh.
        assert (sh = bsh') by (eapply list_join_eq; eauto; apply HshP).
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
        destruct (eq_dec Vundef Empty); [discriminate|].
        destruct (eq_dec (vint v') Empty); [|reflexivity].
        split; intro; subst; tauto.
      * rewrite Znth_overflow, Znth_overflow with (al := h' ++ [vint v']); auto; [reflexivity|].
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
Qed.

Lemma body_finish_write : semax_body Vprog Gprog f_finish_write finish_write_spec.
Proof.
  start_function.
  rewrite sepcon_map; Intros.
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
        EX t' : list nat, EX h' : list val, !!(Zlength t' = i /\ Zlength h' = i) &&
          fold_right sepcon emp (map (fun r => comm_loc lsh (Znth r locks Vundef) (Znth r comms Vundef)
            (Znth r g Vundef) (Znth r g0 Vundef) (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh)
            gsh2 (Znth r h [] ++ if zlt r i then [(Znth r t' O, AE (Znth r h' Vundef) (vint b))] else []))
            (upto (Z.to_nat N))) *
          let lasts' := map (fun i => if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0)
                            (upto (Z.to_nat N)) in
            data_at Ews (tarray tint N) (map (fun i => vint i) lasts') last_taken *
            fold_right sepcon emp (map (fun r =>
              ghost_var gsh1 (vint (if zlt r i then b else b0)) (Znth r g1 Vundef)) (upto (Z.to_nat N))) *
            fold_right sepcon emp (map (fun r =>
              ghost_var gsh1 (vint (Znth r lasts' (-1))) (Znth r g2 Vundef)) (upto (Z.to_nat N))) *
            fold_right sepcon emp (map (fun a => EX sh : share,
              !!(if eq_dec a b0 then sepalg_list.list_join sh0 (make_shares shs (sublist 0 i lasts') a) sh
                 else if eq_dec a b then sepalg_list.list_join sh0 (sublist i N shs) sh
                 else sepalg_list.list_join sh0 (make_shares shs lasts' a) sh) &&
              EX v : Z, @data_at CompSpecs sh tbuffer (vint v) (Znth a bufs Vundef)) (upto (Z.to_nat B))))).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists (@nil nat) (@nil val).
    replace (map (fun i => if eq_dec (Znth i [] Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N)))
      with lasts.
    entailer!.
    apply derives_refl'; f_equal; f_equal.
    { f_equal.
      apply map_ext_in.
      intros; rewrite In_upto in *.
      destruct (zlt a 0); [omega | rewrite app_nil_r; auto]. }
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
      intro; rewrite Znth_nil; destruct (eq_dec Vundef Empty); auto; discriminate.
      { rewrite Zlength_correct in *; Omega0. } }
  - assert_PROP (Zlength comms = N) as Hcomms by entailer!.
    Intros t' h'.
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
    destruct (zlt i i); [omega | rewrite app_nil_r].
    rewrite comm_loc_isptr; Intros.
    forward.
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat B))) b); [|rewrite Zlength_map, Zlength_upto; auto].
    rewrite Znth_map with (d' := B), Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; auto; try omega.
    Intros bsh.
    destruct (eq_dec b b0); [absurd (b = b0); auto|].
    match goal with H : if eq_dec b b then _ else _ |- _ => rewrite eq_dec_refl in H end.
    match goal with H : sepalg_list.list_join _ (sublist i N shs) _ |- _ =>
      rewrite sublist_split with (mid := i + 1) in H; try omega;
      apply list_join_comm, sepalg_list.list_join_unapp in H; destruct H as (bsh' & ? & Hsh) end.
    rewrite sublist_len_1 with (d := Tsh), <- sepalg_list.list_join_1 in Hsh; [|omega].
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i); [|rewrite Zlength_map; auto].
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i); [|rewrite Zlength_map; auto].
    erewrite !Znth_map; rewrite ?Znth_upto; rewrite ?Znth_upto, ?Zlength_upto; rewrite ?Z2Nat.id; auto; try omega.
    rewrite Znth_overflow with (al := h'); [|omega].
    destruct (zlt i i); [clear - l; omega|].
    forward_call (lsh, Znth i comms Vundef, Znth i g Vundef, Znth i locks Vundef, vint 0, vint b, Znth i h [],
      fun (h : hist) (v : val) => !!(v = vint b) &&
        ghost_var gsh1 (vint b0) (Znth i g1 Vundef) *
        ghost_var gsh1 (vint (Znth i lasts 0)) (Znth i g2 Vundef) *
        EX v : Z, data_at (Znth i shs Tsh) tbuffer (vint v) (Znth b bufs Vundef),
      comm_R bufs (Znth i shs Tsh) gsh2 (Znth i g0 Vundef) (Znth i g1 Vundef) (Znth i g2 Vundef),
        fun (h : hist) (v : val) => EX b' : Z, !!(v = vint b' /\ -1 <= b' < B) &&
          ghost_var gsh1 (vint b) (Znth i g1 Vundef) *
          ghost_var gsh1 (vint (if eq_dec b' (-1) then b0 else Znth i lasts 0)) (Znth i g2 Vundef) *
          if eq_dec b' (-1) then EX v : Z, data_at (Znth i shs Tsh) tbuffer (vint v) (Znth (Znth i lasts 0) bufs Vundef)
          else !!(b' = b0) && EX v' : Z, data_at (Znth i shs Tsh) tbuffer (vint v') (Znth b0 bufs Vundef)).
    { rewrite <- !sepcon_assoc; rewrite (sepcon_comm _ (EX v : Z, @data_at CompSpecs bsh tbuffer (vint v) _)).
      rewrite !sepcon_assoc; eapply derives_trans; [apply sepcon_derives; [|apply derives_refl]|].
      { instantiate (1 := (EX v : Z, data_at bsh' tbuffer (vint v) (Znth b bufs Vundef)) *
          (EX v : Z, data_at (Znth i shs Tsh) tbuffer (vint v) (Znth b bufs Vundef))).
        Intro v0; Exists v0 v0; rewrite (data_at_share_join _ _ _ _ _ _ Hsh); auto. }
      fast_cancel. }
    { repeat (split; auto).
      unfold AE_spec; intros.
      intros ??????? Ha.
      unfold comm_R; unfold comm_R at 1 in Ha.
      rewrite rev_app_distr in Ha; simpl in Ha.
      rewrite last_two_reads_cons, prev_taken_cons in Ha.
      rewrite flatten_sepcon_in_SEP.
      rewrite extract_exists_in_SEP; Intro b'.
      rewrite extract_exists_in_SEP; Intro b1.
      rewrite extract_exists_in_SEP; Intro b2.
      rewrite <- flatten_sepcon_in_SEP.
      rewrite !sepcon_andp_prop', !sepcon_andp_prop.
      erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
      erewrite extract_prop_in_SEP with (n := O); simpl; eauto.
      Intros.
      assert (repable_signed b) by (apply repable_buf; omega).
      destruct (eq_dec vc Empty).
      { subst; assert (b = -1) by (apply Empty_inj; auto); omega. }
      apply semax_pre with (P' := PROPx P (LOCALx Q (SEPx (
        (ghost_var gsh1 (vint b0) (Znth i g1 Vundef) *
         ghost_var gsh2 (last_write (rev hx)) (Znth i g1 Vundef)) ::
        (ghost_var gsh1 (vint (Znth i lasts 0)) (Znth i g2 Vundef) *
         ghost_var gsh2 (prev_taken (rev hx)) (Znth i g2 Vundef)) ::
        (ghost_var gsh2 (vint b1) (Znth i g0 Vundef) *
         (if eq_dec b' (-1) then EX v1 : Z, @data_at CompSpecs (Znth i shs Tsh) tbuffer (vint v1) (Znth b2 bufs Vundef)
          else EX v1 : Z, @data_at CompSpecs (Znth i shs Tsh) tbuffer (vint v1) (Znth b' bufs Vundef)) *
         (EX v1 : Z, @data_at CompSpecs (Znth i shs Tsh) tbuffer (vint v1) (Znth b bufs Vundef))) :: R)))).
      { go_lowerx; cancel. }
      assert_PROP (last_write (rev hx) = vint b0) as Hwrite.
      { go_lowerx; apply sepcon_derives_prop.
        rewrite sepcon_comm; apply ghost_var_inj; auto. }
      assert_PROP (prev_taken (rev hx) = vint (Znth i lasts 0)) as Hprev.
      { go_lowerx.
        rewrite <- sepcon_assoc, (sepcon_comm (_ * _) (_ * ghost_var _ _ _)).
        do 2 apply sepcon_derives_prop.
        rewrite sepcon_comm; apply ghost_var_inj; auto. }
      rewrite <- Hprev, <- Hwrite in *.
      erewrite !ghost_var_share_join; eauto.
      apply ghost_var_update with (v' := vint b).
      rewrite <- flatten_sepcon_in_SEP, sepcon_comm, flatten_sepcon_in_SEP.
      apply ghost_var_update with (v' := if eq_dec b' (-1) then last_write (rev hx) else prev_taken (rev hx)).
      rewrite <- !(ghost_var_share_join _ _ _ _ _ gsh1_gsh2_join).
      eapply semax_pre, Ha.
      go_lowerx.
      rewrite (sepcon_comm _ (weak_precise_mpred _ && _)).
      rewrite <- emp_sepcon at 1; rewrite !sepcon_assoc; apply sepcon_derives.
      { apply andp_right; auto; eapply derives_trans; [|apply comm_R_precise]; auto. }
      Exists b b1 b2.
      rewrite !sepcon_andp_prop'.
      apply andp_right.
      { apply prop_right; repeat (split; [solve [auto; omega]|]).
      rewrite Forall_app; split; [split; [|constructor]; auto | auto].
      subst; repeat eexists; auto; omega. }
      destruct (eq_dec b (-1)); [omega|].
      rewrite (sepcon_comm (_ * _)); Exists b'.
      rewrite !sepcon_andp_prop'; apply andp_right; [apply prop_right; auto|].
      assert (last_two_reads (rev hx) = (vint b1, vint b2)) as Hlast by assumption.
      erewrite take_read, Hlast in *; try (rewrite rev_involutive; eauto).
      unfold last_write in *; simpl in *.
      destruct (eq_dec vc Empty); [absurd (vc = Empty); auto|].
      assert (Znth i lasts 0 = if eq_dec vx Empty then b2 else b1).
      { assert (repable_signed (Znth i lasts 0)).
        { apply Forall_Znth; [omega|].
          eapply Forall_impl; [|eauto]; intros.
          apply repable_buf; simpl in *; omega. }
        destruct (eq_dec vx Empty); apply repr_inj_signed; auto; congruence. }
      destruct (eq_dec vx Empty); subst; fast_cancel.
      + assert (b' = -1) by (apply Empty_inj; auto; apply repable_buf; auto).
        subst; rewrite !eq_dec_refl.
        rewrite Hwrite; simpl; cancel.
        exploit find_write_read.
        { rewrite rev_involutive; eauto. }
        { discriminate. }
        intros ->; rewrite Hwrite; auto.
      + assert (exists rest, find_write (rev hx) (vint 0) = (vint b', rest)) as (? & Hwrite').
        { replace hx with (rev (rev hx)) in Hvx by (apply rev_involutive).
          destruct (rev hx); simpl in *.
          { assert (b' = 0); [|subst; eauto].
            apply repr_inj_signed.
            * apply repable_buf; auto.
            * split; computable.
            * congruence. }
          destruct a.
          rewrite apply_hist_app in Hvx.
          destruct (apply_hist (vint 0) (rev l)); [simpl in * | discriminate].
          destruct (eq_dec r v); [|discriminate].
          inv Hvx.
          destruct (eq_dec (vint b') Empty); [absurd (vint b' = Empty); auto | eauto]. }
        rewrite Hwrite' in Hwrite.
        assert (b' = b0).
        { apply repr_inj_signed; [apply repable_buf | apply repable_buf | simpl in *; congruence]; auto; omega. }
        subst.
        destruct (eq_dec b0 (-1)); [subst; contradiction n3; auto|].
        rewrite !sepcon_andp_prop', !sepcon_andp_prop; apply andp_right; [apply prop_right; auto|].
        unfold last_two_reads in Hlast; destruct (find_read (rev hx) (vint 1)); inv Hlast.
        simpl; cancel. }
    Intros x b'; destruct x as (t, v); simpl in *.
    gather_SEP 0 9; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      comm_loc lsh (Znth r locks Vundef) (Znth r comms Vundef) (Znth r g Vundef) (Znth r g0 Vundef)
        (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh) gsh2 (Znth r h [] ++
        (if zlt r (i + 1) then [(Znth r (t' ++ [t]) 0%nat, AE (Znth r (h' ++ [v]) Vundef) (vint b))] else [])))
      (upto (Z.to_nat N)))).
    { go_lower.
      rewrite replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength;
        rewrite !Zlength_map, Zlength_upto; auto.
      intros j ?; destruct (eq_dec j i).
      + subst; rewrite upd_Znth_same by (rewrite Zlength_map, Zlength_upto; auto).
        rewrite Znth_map with (d' := N), Znth_upto by (auto; omega).
        destruct (zlt (Zlength t') (Zlength t' + 1)); [|omega].
        rewrite !app_Znth2 by omega.
        rewrite Zminus_diag; replace (Zlength t') with (Zlength h'); rewrite Zminus_diag, !Znth_0_cons; auto.
      + rewrite upd_Znth_diff' by (rewrite ?Zlength_map, ?Zlength_upto; auto).
        rewrite !Znth_map with (d' := N), !Znth_upto by (auto; omega).
        if_tac; if_tac; auto; try omega.
        rewrite !app_Znth1; auto; omega. }
    gather_SEP 1 10; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      ghost_var gsh1 (vint (if zlt r (i + 1) then b else b0)) (Znth r g1 Vundef)) (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
        [|rewrite Zlength_map, Zlength_upto; auto].
      erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; simpl; auto;
        try (unfold N in *; auto; omega).
      destruct (zlt i (i + 1)); [fast_cancel | omega].
      apply sepcon_list_derives; rewrite !upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
      destruct (eq_dec i0 i); [subst; rewrite !upd_Znth_same by (rewrite ?Zlength_map; auto); auto|].
      rewrite !upd_Znth_diff' by (rewrite ?Zlength_map; auto).
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      destruct (zlt i0 i), (zlt i0 (i + 1)); auto; omega. }
    gather_SEP 2 10; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      ghost_var gsh1 (vint (Znth r (map (fun i0 => if eq_dec (Znth i0 (h' ++ [v]) Vundef) Empty then b0
        else Znth i0 lasts 0) (upto (Z.to_nat N))) (-1))) (Znth r g2 Vundef)) (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
        [|rewrite Zlength_map, Zlength_upto; auto].
      erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; simpl; auto;
        try (unfold N in *; auto; omega).
      erewrite Znth_map, Znth_upto by (auto; unfold N in *; simpl; omega).
      replace i with (Zlength h'); rewrite app_Znth2, Zminus_diag, Znth_0_cons; [fast_cancel | omega].
      apply sepcon_derives.
      { destruct (eq_dec v Empty), (eq_dec b' (-1)); auto; subst.
        + contradiction n0; apply Empty_inj; auto; apply repable_buf; auto.
        + contradiction n0; auto. }
      apply sepcon_list_derives; rewrite !upd_Znth_Zlength; rewrite !Zlength_map;
        try (rewrite !Zlength_upto; simpl; unfold N in *; omega); intros.
      destruct (eq_dec i0 (Zlength h')); [subst; rewrite !upd_Znth_same by (rewrite ?Zlength_map; auto); auto|].
      rewrite !upd_Znth_diff' by (rewrite ?Zlength_map, ?Zlength_upto; unfold N in *; simpl; auto; omega).
      erewrite !Znth_map; rewrite ?Znth_upto; rewrite ?Znth_upto; auto; rewrite Zlength_upto in *; try omega.
      destruct (zlt i0 (Zlength h')).
      + rewrite app_Znth1; auto.
      + rewrite Znth_overflow with (al := h'), Znth_overflow with (al := (h' ++ [v])); auto.
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega. }
    assert (repable_signed b') by (apply repable_buf; auto); subst v.
    focus_SEP 9.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx (data_at _ _ ?l last_taken :: ?R)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx (data_at Ews (tarray tint N)
        (upd_Znth i l (vint (if eq_dec (vint b') Empty then b0 else Znth i lasts 0))) last_taken :: R)))) end.
    + forward.
      match goal with H : Int.repr b' = _ |- _ => rewrite Int.neg_repr in H; apply repr_inj_signed in H end; subst;
        auto.
      destruct (eq_dec (- (1)) (-1)); [|absurd (-1 = -1); auto].
      apply drop_tc_environ.
    + forward.
      destruct (eq_dec b' (-1)); [subst; absurd (Int.repr (-1) = Int.neg (Int.repr 1)); auto|].
      erewrite upd_Znth_triv with (i0 := i).
      apply drop_tc_environ.
      * rewrite !Zlength_map, Zlength_upto; auto.
      * rewrite !Znth_map', Znth_upto; [|simpl; unfold N in *; omega].
        rewrite Znth_overflow; [|omega].
        destruct (eq_dec Vundef Empty); [discriminate|].
        destruct (eq_dec (vint b') Empty); auto.
        contradiction n0; apply Empty_inj; auto.
    + intros.
      unfold exit_tycon, overridePost.
      destruct (eq_dec ek EK_normal); [subst | apply drop_tc_environ].
      Intros; unfold POSTCONDITION, abbreviate, normal_ret_assert.
      do 2 (apply andp_right; [apply prop_right; auto|]).
      Exists (t' ++ [t]) (h' ++ [vint b']).
      go_lower.
      repeat (apply andp_right; [apply prop_right; repeat split; auto; omega|]).
      rewrite lock_struct_array; fast_cancel.
      rewrite !sepcon_andp_prop'.
      rewrite Zlength_app, Zlength_cons, Zlength_nil; apply andp_right.
      { replace (Zlength t') with (Zlength h'); apply prop_right; rewrite Zlength_app; auto. }
      fast_cancel.
      apply sepcon_derives.
      * apply derives_refl'; f_equal.
        erewrite upd_Znth_eq, !map_length, upto_length, !map_map;
          [|rewrite !Zlength_map, Zlength_upto; unfold N in *; auto].
        apply map_ext_in; intros; rewrite In_upto in *.
        replace (Zlength t') with (Zlength h').
        destruct (eq_dec a (Zlength h')).
        -- subst; rewrite app_Znth2, Zminus_diag, Znth_0_cons; auto; clear; omega.
        -- rewrite Znth_map', Znth_upto; [|omega].
           destruct (zlt a (Zlength t')); [rewrite app_Znth1 | rewrite Znth_overflow]; auto; try omega.
           rewrite Znth_overflow with (al := _ ++ _); auto.
           rewrite Zlength_app, Zlength_cons, Zlength_nil; omega.
      * fast_cancel.
        replace (Zlength t') with (Zlength h') in *; eapply upd_write_shares; eauto.
  - Intros t' h'.
    forward.
    forward.
    forward.
    rewrite sublist_nil, sublist_same; rewrite ?Zlength_map; auto.
    Exists (map (fun i => if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N)))
      (extendr (map (fun x : nat * val => let '(t, v) := x in (t, AE v (vint b))) (combine t' h')) h); entailer!.
    + repeat split.
      * rewrite Forall_map, Forall_forall; intros; simpl.
        destruct (eq_dec (Znth x h' Vundef) Empty); [omega|].
        rewrite In_upto, Z2Nat.id in *; unfold N; try omega.
        apply Forall_Znth; [omega | auto].
      * assert (Zlength h' = Zlength h) as Hlen by omega; assert (Zlength t' = Zlength h') as Hlen' by omega;
        clear - Hlen Hlen'; revert dependent h; revert dependent t'; induction h';
          destruct h, t'; rewrite ?Zlength_nil, ?Zlength_cons in *; simpl; intros; auto;
          try (rewrite Zlength_correct in *; omega).
        constructor; eauto.
        apply IHh'; omega.
      * rewrite in_map_iff; intros (i & ? & ?); subst.
        rewrite In_upto, Z2Nat.id in *; try (unfold N; omega).
        destruct (eq_dec (Znth i h' Vundef) Empty); [absurd (b0 = b0); auto|].
        match goal with H : ~In _ lasts |- _ => contradiction H; apply Znth_In; omega end.
    + rewrite sepcon_map, <- !sepcon_assoc.
      apply derives_refl'; f_equal; f_equal; [f_equal|].
      { erewrite map_ext_in; eauto; intros; simpl.
        rewrite In_upto in *.
        destruct (zlt a N); [|unfold N in *; simpl in *; omega].
        erewrite Znth_extendr_in, Znth_map', Znth_combine; eauto;
          rewrite ?Zlength_map, ?Zlength_combine, ?Z.min_l; omega. }
      apply map_ext; intro.
      f_equal; extensionality; f_equal; f_equal; apply prop_ext.
      destruct (eq_dec a b).
      * destruct (eq_dec a b0); [absurd (b = b0); subst; auto|].
        split; intro Hx; [inv Hx; auto | subst; constructor].
      * destruct (eq_dec a b0); reflexivity.
Qed.

Ltac entailer_for_load_tac ::= unfold tc_efield; go_lower; entailer'.
Ltac entailer_for_store_tac ::= unfold tc_efield; go_lower; entailer'.

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
  eapply semax_pre with (P' := EX b0 : Z, EX h : hist, PROP (0 <= b0 < B; latest_read h (vint b0))
    LOCAL (temp _r (vint r); temp _arg arg; gvar _reading reading; gvar _last_read last_read; 
           gvar _lock lock; gvar _comm comm; gvar _bufs buf)
    SEP (data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
         data_at Tsh tint Empty (Znth r reads Vundef); data_at Tsh tint (vint b0) (Znth r lasts Vundef);
         data_at Tsh tint (vint r) (force_val (sem_cast_neutral arg)); malloc_token Tsh (sizeof tint) arg;
         data_at sh1 (tarray (tptr tint) N) comms comm;
         data_at sh1 (tarray (tptr tlock) N) locks lock;
         data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
         comm_loc sh2 l c g g0 g1 g2 bufs sh gsh2 h;
         EX v : Z, @data_at CompSpecs sh tbuffer (vint v) (Znth b0 bufs Vundef);
         ghost_var gsh1 (vint b0) g0)).
  { Exists 1 ([] : hist); entailer!.
    unfold latest_read; auto. }
  eapply semax_loop; [|forward; apply drop_tc_environ].
  Intros b0 h.
  forward.
  subst c l; subst; forward_call (r, reading, last_read, lock, comm, reads, lasts, locks, comms, bufs,
    sh, sh1, sh2, b0, g, g0, g1, g2, h).
  { cancel. }
  { repeat (split; auto). }
  Intros x; destruct x as (((b, t), e), v); simpl in *.
  rewrite (data_at_isptr _ tbuffer); Intros.
  forward.
  forward.
  forward_call (r, reading, reads, sh1).
  { cancel. }
  go_lower.
  Exists b (h ++ [(t, AE e Empty)]) v; entailer'; cancel.
Qed.

Lemma body_writer : semax_body Vprog Gprog f_writer writer_spec.
Proof.
  start_function.
  forward_call (writing, last_given, last_taken).
  forward.
  eapply semax_seq'; [|apply semax_ff].
  eapply semax_pre with (P' := EX v : Z, EX b0 : Z, EX lasts : list Z, EX h : list hist,
   PROP (0 <= b0 < B; Forall (fun x => 0 <= x < B) lasts; Zlength h = N; ~In b0 lasts)
   LOCAL (temp _v (vint v); temp _arg arg; gvar _writing writing; gvar _last_given last_given;
   gvar _last_taken last_taken; gvar _lock lock; gvar _comm comm; gvar _bufs buf)
   SEP (data_at Ews tint Empty writing; data_at Ews tint (vint b0) last_given;
   data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken;
   data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
   data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
   fold_right sepcon emp (map (fun r0 => comm_loc lsh (Znth r0 locks Vundef) (Znth r0 comms Vundef)
     (Znth r0 g Vundef) (Znth r0 g0 Vundef) (Znth r0 g1 Vundef) (Znth r0 g2 Vundef) bufs
     (Znth r0 shs Tsh) gsh2 (Znth r0 h [])) (upto (Z.to_nat N)));
   fold_right sepcon emp (map (fun r0 => ghost_var gsh1 (vint b0) (Znth r0 g1 Vundef) *
     ghost_var gsh1 (vint (Znth r0 lasts (-1))) (Znth r0 g2 Vundef)) (upto (Z.to_nat N)));
   fold_right sepcon emp (map (fun i => EX sh : share, !! (if eq_dec i b0 then sh = sh0
     else sepalg_list.list_join sh0 (make_shares shs lasts i) sh) &&
     (EX v : Z, @data_at CompSpecs sh tbuffer (vint v) (Znth i bufs Vundef))) (upto (Z.to_nat B))))).
  { Exists 0 0 (repeat 1 (Z.to_nat N)) (repeat ([] : hist) (Z.to_nat N)); entailer!.
    { split; [repeat constructor; computable | omega]. }
    rewrite sepcon_map.
    apply derives_refl'.
    rewrite !sepcon_assoc; f_equal; f_equal; [|f_equal].
    - rewrite list_Znth_eq with (l := g1) at 1.
      replace (length g1) with (Z.to_nat N) by (symmetry; rewrite <- Zlength_length; auto; unfold N; computable).
      rewrite map_map; auto.
    - rewrite list_Znth_eq with (l := g2) at 1.
      replace (length g2) with (Z.to_nat N) by (symmetry; rewrite <- Zlength_length; auto; unfold N; computable).
      erewrite map_map, map_ext_in; eauto.
      intros; rewrite In_upto in *.
      match goal with |- context[Znth a ?l (-1)] => replace (Znth a l (-1)) with 1; auto end.
      apply Forall_Znth; auto.
    - erewrite map_ext_in; eauto.
      intros; rewrite In_upto in *.
      destruct (eq_dec a 0); auto.
      destruct (eq_dec a 1), (eq_dec 1 a); auto; try omega.
      { apply mpred_ext; Intros sh; Exists sh; entailer!.
        * constructor.
        * match goal with H : sepalg_list.list_join sh0 [] sh |- _ => inv H; auto end. }
      generalize (make_shares_out a (repeat 1 (Z.to_nat N)) shs); simpl; intro Heq.
      destruct (eq_dec 1 a); [contradiction n0; auto|].
       rewrite Heq; auto; [|omega].
      apply mpred_ext; Intros sh; Exists sh; entailer!.
      eapply list_join_eq; eauto. }
  eapply semax_loop; [|forward; apply drop_tc_environ].
  Intros v b0 lasts h.
  rewrite sepcon_map; Intros.
  forward.
  forward_call (writing, last_given, last_taken, b0, lasts).
  { cancel. }
  Intros b.
  rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat B))) b); [|rewrite Zlength_map; auto].
  erewrite Znth_map, Znth_upto; auto; rewrite ?Z2Nat.id; try omega.
  Intros sh v0.
  rewrite (data_at_isptr _ tbuffer); Intros.
  forward.
  destruct (eq_dec b b0); [absurd (b = b0); auto|].
  assert_PROP (Zlength lasts = N).
  { gather_SEP 2; go_lowerx; apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts|].
    apply prop_left; intros (_ & ? & _); apply prop_right.
    unfold unfold_reptype in *; simpl in *.
    rewrite Zlength_map in *; auto. }
  rewrite make_shares_out in *; auto; [|setoid_rewrite H; auto].
  assert (sh = Tsh) by (eapply list_join_eq; eauto); subst.
  forward.
  gather_SEP 7 8; rewrite <- sepcon_map.
  gather_SEP 8 9; replace_SEP 0 (fold_right sepcon emp (map (fun i => EX sh2 : share,
    !! (if eq_dec i b0 then sh2 = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts i) sh2) &&
    (EX v1 : Z, data_at sh2 tbuffer (vint v1) (Znth i bufs Vundef))) (upto (Z.to_nat B)))).
  { go_lowerx; eapply derives_trans with (Q := _ * _);
      [|erewrite replace_nth_sepcon, upd_Znth_triv; eauto].
    rewrite Znth_map', Znth_upto; [|simpl; unfold B, N in *; omega].
    destruct (eq_dec b b0); [absurd (b = b0); auto|].
    rewrite make_shares_out; auto; [|setoid_rewrite H; auto].
    Exists Tsh v; entailer!. }
  forward_call (writing, last_given, last_taken, comm, lock, comms, locks, bufs, b, b0, lasts,
    sh1, lsh, shs, g, g0, g1, g2, h, sh0).
  { repeat (split; auto). }
  Intros x; destruct x as (lasts', h').
  rewrite sepcon_map; Intros.
  forward.
  unfold loop2_ret_assert; Exists (v + 1) b lasts' h'; rewrite sepcon_map; entailer!.
  replace N with (Zlength h) by auto; symmetry; eapply mem_lemmas.Forall2_Zlength; eauto.
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
  exploit (split_shares (Z.to_nat N) Tsh); auto; intros (sh0 & shs & ? & ? & ? & ?).
  rewrite (data_at__eq _ (tarray (tptr (Tstruct _lock_t noattr)) N)), lock_struct_array.
  forward_call (comm, lock, buf, reading, last_read, sh0, shs).
  Intros x; destruct x as ((((((((comms, locks), bufs), reads), lasts), g), g0), g1), g2).
  assert_PROP (Zlength comms = N).
  { go_lowerx; apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold N; omega|].
    unfold unfold_reptype; simpl.
    apply prop_left; intros (? & ? & ?); apply prop_right; auto. }
  get_global_function'' _writer; Intros.
  apply extract_exists_pre; intros writer_.
  exploit (split_shares (Z.to_nat N) Ews); auto; intros (sh1 & shs1 & ? & ? & ? & ?).
  assert_PROP (Zlength bufs = B).
  { go_lowerx; rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at _ _ _ buf)), !sepcon_assoc.
    apply sepcon_derives_prop.
    eapply derives_trans; [apply data_array_at_local_facts'; unfold B, N; omega|].
    unfold unfold_reptype; simpl.
    apply prop_left; intros (? & ? & ?); apply prop_right; auto. }
  forward_spawn (val * val * val * val * val * val * list val * list val * list val *
                 share * share * share * list share * list val * list val * list val * list val)%type
    (writer_, vint 0, fun x : (val * val * val * val * val * val * list val * list val * list val * share * share *
      share * list share * list val * list val * list val * list val) =>
      let '(writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs,
            g, g0, g1, g2) := x in
      [(_writing, writing); (_last_given, last_given); (_last_taken, last_taken);
       (_lock, lock); (_comm, comm); (_bufs, buf)],
    (writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, gsh1, sh0, shs,
                       g, g0, g1, g2),
    fun (x : (val * val * val * val * val * val * list val * list val * list val *
              share * share * share * list share * list val * list val * list val * list val)%type)
        (arg : val) =>
    let '(writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs,
          g, g0, g1, g2) := x in
      fold_right sepcon emp [!!(fold_right and True [Zlength shs = N; readable_share sh1; readable_share lsh;
        Forall readable_share shs; sepalg_list.list_join sh0 shs Tsh;
        Zlength g1 = N; Zlength g2 = N; Forall isptr comms]) && emp;
        data_at_ Ews tint writing; data_at_ Ews tint last_given; data_at_ Ews (tarray tint N) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
        data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
        fold_right sepcon emp (map (fun r => comm_loc lsh (Znth r locks Vundef) (Znth r comms Vundef)
          (Znth r g Vundef) (Znth r g0 Vundef) (Znth r g1 Vundef) (Znth r g2 Vundef) bufs
          (Znth r shs Tsh) gsh2 []) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2);
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i 0 then sh = sh0 else if eq_dec i 1 then sh = sh0 else sh = Tsh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B)))]).
  { apply andp_right.
    { entailer!. }
    unfold spawn_pre, PROPx, LOCALx, SEPx.
    go_lowerx.
    rewrite !sepcon_andp_prop, !sepcon_andp_prop'.
    apply andp_right; [apply prop_right; auto|].
    apply andp_right; [apply prop_right; repeat split; auto|].
    apply andp_right; [apply prop_right; repeat split; auto|].
    apply andp_right; [apply prop_right|].
    { unfold liftx; simpl; unfold lift, make_args'; simpl.
      erewrite gvar_eval_var, !(force_val_sem_cast_neutral_gvar' _ writer_) by eauto.
      rewrite eval_id_same, eval_id_other, eval_id_same; [|discriminate].
      repeat split; auto; apply gvar_denote_global; auto. }
    Exists _arg.
    rewrite !sepcon_assoc; apply sepcon_derives.
    { apply derives_refl'.
      f_equal; f_equal; extensionality; destruct x as (?, x); repeat destruct x as (x, ?); simpl.
      rewrite !sepcon_andp_prop'; extensionality.
      rewrite <- andp_assoc, prop_true_andp with (P := True); auto.
      rewrite (andp_comm (!! _) (!! _)), andp_assoc; f_equal; f_equal.
      rewrite emp_sepcon, !sepcon_emp; auto. }
    rewrite sepcon_andp_prop'.
    apply andp_right; [apply prop_right; repeat (split; auto)|].
    unfold comm_loc; erewrite map_ext;
      [|intro; erewrite <- AE_loc_join with (h1 := [])(h2 := []); eauto; reflexivity].
    rewrite !sepcon_map.
    do 3 (erewrite <- (data_at_shares_join Ews); eauto).
    rewrite (extract_nth_sepcon (map (data_at _ _ _) (sublist 1 _ bufs)) 0), Znth_map with (d' := Vundef);
      rewrite ?Zlength_map, ?Zlength_sublist; try (unfold B, N in *; omega).
    erewrite <- (data_at_shares_join Tsh); eauto.
    rewrite (sepcon_comm (data_at sh0 _ _ (Znth 0  (sublist _ _ bufs) Vundef))),
      (sepcon_assoc _ (data_at sh0 _ _ _)).
    rewrite replace_nth_sepcon.
    fast_cancel.
    rewrite <- !sepcon_assoc, (sepcon_comm _ (data_at sh0 _ _ _)).
    rewrite <- !sepcon_assoc, (sepcon_comm _ (fold_right sepcon emp (upd_Znth 0 _ _))), !sepcon_assoc.
    rewrite <- sepcon_assoc; apply sepcon_derives; [|cancel_frame].
    assert (Zlength (data_at sh0 tbuffer (vint 0) (Znth 0 bufs Vundef)
         :: upd_Znth 0 (map (data_at Tsh tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs))
              (data_at sh0 tbuffer (vint 0) (Znth 0 (sublist 1 (Zlength bufs) bufs) Vundef))) = B) as Hlen.
    { rewrite Zlength_cons, upd_Znth_Zlength; rewrite Zlength_map, Zlength_sublist, ?Zlength_upto;
        simpl; unfold B, N in *; omega. }
    rewrite sepcon_comm; apply sepcon_list_derives with (l1 := _ :: _).
    { rewrite Zlength_map; auto. }
    intros; rewrite Hlen in *.
    erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto; auto; simpl; try (unfold B, N in *; omega).
    destruct (eq_dec i 0); [|destruct (eq_dec i 1)].
    - subst; rewrite Znth_0_cons.
      Exists sh0 0; entailer'.
    - subst; rewrite Znth_pos_cons, Zminus_diag, upd_Znth_same; rewrite ?Zlength_map, ?Zlength_sublist; try omega.
      rewrite Znth_sublist; try omega.
      Exists sh0 0; entailer'.
    - rewrite Znth_pos_cons, upd_Znth_diff; rewrite ?Zlength_map, ?Zlength_sublist; try omega.
      erewrite Znth_map; [|rewrite Zlength_sublist; omega].
      rewrite Znth_sublist; try omega.
      rewrite Z.sub_simpl_r.
      Exists Tsh 0; entailer'. }
  rewrite Znth_sublist; try (unfold B, N in *; omega).
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
        fold_right sepcon emp (map (fun x => comm_loc gsh2 (Znth x locks Vundef) (Znth x comms Vundef)
          (Znth x g Vundef) (Znth x g0 Vundef) (Znth x g1 Vundef) (Znth x g2 Vundef) bufs (Znth x shs Tsh) gsh2
          []) (sublist i N (upto (Z.to_nat N))));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) (sublist i N g0));
        fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i N reads));
        fold_right sepcon emp (map (data_at_ Tsh tint) (sublist i N lasts));
        fold_right sepcon emp (map (malloc_token Tsh 4) comms);
        fold_right sepcon emp (map (malloc_token Tsh 8) locks);
        fold_right sepcon emp (map (malloc_token Tsh 4) bufs);
        fold_right sepcon emp (map (malloc_token Tsh 4) reads);
        fold_right sepcon emp (map (malloc_token Tsh 4) lasts);
        fold_right sepcon emp (map (fun sh => @data_at CompSpecs sh tbuffer (vint 0) (Znth 1 bufs Vundef)) (sublist i N shs)))).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists Ews; rewrite !sublist_same; auto; unfold N; entailer!. }
  { Intros sh'.
    forward_malloc tint d.
    forward.
    get_global_function'' _reader; Intros.
    apply extract_exists_pre; intros reader_.
    match goal with H : sepalg_list.list_join sh1 _ sh' |- _ => rewrite sublist_next with (d0 := Tsh) in H;
      auto; [inversion H as [|????? Hj1 Hj2]; subst |
      match goal with H : Zlength shs1 = _ |- _ => setoid_rewrite H; rewrite Z2Nat.id; omega end] end.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (sh1' & ? & Hj').
    forward_spawn (Z * val * val * val * val * val * list val * list val * list val * list val * list val *
                   share * share * share * val * val * val * val)%type
      (reader_, d, fun x : (Z * val * val * val * val * val * list val * list val * list val * list val *
        list val * share * share * share * val * val * val * val) =>
        let '(r, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs, sh1, sh2, sh,
              g, g0, g1, g2) := x in
        [(_reading, reading); (_last_read, last_read); (_lock, lock); (_comm, comm); (_bufs, buf)],
      (i, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs,
                    Znth i shs1 Tsh, gsh2, Znth i shs Tsh, Znth i g Vundef, Znth i g0 Vundef, Znth i g1 Vundef,
                    Znth i g2 Vundef),
      fun (x : (Z * val * val * val * val * val * list val * list val * list val * list val * list val *
                share * share * share * val * val * val * val)%type) (arg : val) =>
        let '(r, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs, sh1, sh2, sh,
              g, g0, g1, g2) := x in
        fold_right sepcon emp [!!(fold_right and True [readable_share sh; readable_share sh1; 
          readable_share sh2; isptr (Znth r comms Vundef)]) && emp;
          data_at Tsh tint (vint r) arg; malloc_token Tsh (sizeof tint) arg;
          data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
          data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tlock) N) locks lock;
          data_at_ Tsh tint (Znth r reads Vundef); data_at_ Tsh tint (Znth r lasts Vundef);
          data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
          comm_loc sh2 (Znth r locks Vundef) (Znth r comms Vundef) g g0 g1 g2 bufs sh gsh2 [];
          EX v : Z, data_at sh tbuffer (vint v) (Znth 1 bufs Vundef);
          ghost_var gsh1 (vint 1) g0]).
    - apply andp_right.
      { entailer!. }
      unfold spawn_pre, PROPx, LOCALx, SEPx.
      go_lowerx.
      rewrite !sepcon_andp_prop, !sepcon_andp_prop'.
      apply andp_right; [apply prop_right; auto|].
      apply andp_right; [apply prop_right; repeat split; auto|].
      apply andp_right; [apply prop_right; repeat split; auto|].
      apply andp_right; [apply prop_right|].
      { unfold liftx; simpl; unfold lift, make_args'; simpl.
        erewrite gvar_eval_var, !(force_val_sem_cast_neutral_gvar' _ reader_) by eauto.
        rewrite eval_id_same, eval_id_other, eval_id_same; [|discriminate].
        replace (eval_id _d rho) with d.
        rewrite force_val_sem_cast_neutral_isptr'; rewrite force_val_sem_cast_neutral_isptr'; auto.
        repeat split; auto; apply gvar_denote_global; auto. }
      Exists _arg.
      rewrite !sepcon_assoc; apply sepcon_derives.
      { apply derives_refl'.
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
      simpl in *; rewrite !sublist_next with (i0 := i)(d0 := Vundef); auto; try omega; simpl.
      rewrite sublist_next with (d0 := N); rewrite ?Znth_upto; auto; rewrite? Zlength_upto; simpl;
        try (unfold N in *; omega).
      rewrite sublist_next with (i0 := i)(d0 := Tsh); auto; simpl.
      Exists 0; fast_cancel.
      { match goal with H : Zlength shs = _ |- _ => setoid_rewrite H; unfold N; omega end. }
    - Exists sh1'; entailer!. }
  eapply semax_seq'; [|apply semax_ff].
  eapply semax_loop; [|forward; apply drop_tc_environ].
  forward.
  entailer!.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

(* This lemma ties all the function proofs into a single proof for the entire program. *)
Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct, main_pre, main_post, prog_vars; simpl.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
repeat semax_func_cons_ext.
semax_func_cons body_malloc. apply semax_func_cons_malloc_aux.
repeat semax_func_cons_ext.
{ unfold PROPx, LOCALx, local, lift1, liftx, lift; simpl.
  unfold liftx, lift; simpl.
  Intros; subst.
  apply prop_right; unfold make_ext_rval, eval_id in *; simpl in *.
  destruct ret; auto. }
semax_func_cons body_surely_malloc.
semax_func_cons body_memset.
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
