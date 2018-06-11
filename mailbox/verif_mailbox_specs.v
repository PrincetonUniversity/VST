Require Import mailbox.verif_atomic_exchange.
Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox.

Set Bullet Behavior "Strict Subproofs".

(* standard VST prelude *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Instance CompSpecs_Preserve: change_composite_env verif_atomic_exchange.CompSpecs CompSpecs.
  make_cs_preserve verif_atomic_exchange.CompSpecs CompSpecs.
Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* import funspecs from concurrency library *)
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.

(* utility function specs *)
Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type
   PRE [ _n OF tuint ]
       PROP (0 <= sizeof t <= Int.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       LOCAL (temp _n (Vint (Int.repr (sizeof t))))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (malloc_token Tsh t p * data_at_ Tsh t p).

Definition memset_spec :=
 DECLARE _memset
  WITH sh : share, t : type, p : val, c : Z, n : Z
  PRE [ _s OF tptr tvoid, _c OF tint, _n OF tuint ]
   PROP (writable_share sh; sizeof t = (4 * n)%Z; align_compatible tint p)
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
  if eq_dec b (-1) then EX v : Z, data_at sh tbuffer (vint v) (Znth b2 bufs)
  else EX v : Z, data_at sh tbuffer (vint v) (Znth b bufs).

Definition comm_loc lsh lock comm g g0 g1 g2 bufs sh gsh :=
  AE_loc lsh lock comm g (vint 0) (comm_R bufs sh gsh g0 g1 g2).

(* messaging system function specs *)
Definition initialize_channels_spec :=
 DECLARE _initialize_channels
  WITH sh1 : share, shs : list share, gv: globals
  PRE [ ]
   PROP (Zlength shs = N; sepalg_list.list_join sh1 shs Tsh)
   LOCAL (gvars gv)
   SEP (data_at_ Ews (tarray (tptr tint) N) (gv _comm); data_at_ Ews (tarray (tptr tlock) N) (gv _lock);
        data_at_ Ews (tarray (tptr tbuffer) B) (gv _buf);
        data_at_ Ews (tarray (tptr tint) N) (gv _reading); data_at_ Ews (tarray (tptr tint) N) (gv _last_read))
  POST [ tvoid ]
   EX comms : list val, EX locks : list val, EX bufs : list val, EX reads : list val, EX lasts : list val,
     EX g : list gname, EX g0 : list gname, EX g1 : list gname, EX g2 : list gname,
   PROP (Forall isptr comms; Zlength g = N; Zlength g0 = N; Zlength g1 = N; Zlength g2 = N)
   LOCAL ()
   SEP (data_at Ews (tarray (tptr tint) N) comms (gv _comm);
        data_at Ews (tarray (tptr tlock) N) locks (gv _lock);
        data_at Ews (tarray (tptr tbuffer) B) bufs (gv _buf);
        data_at Ews (tarray (tptr tint) N) reads (gv _reading);
        data_at Ews (tarray (tptr tint) N) lasts (gv _last_read);
        fold_right sepcon emp (map (fun r =>
          comm_loc Tsh (Znth r locks) (Znth r comms) (Znth r g) (Znth r g0)
            (Znth r g1) (Znth r g2) bufs (Znth r shs) gsh2 empty_map) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g0);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2);
        fold_right sepcon emp (map (malloc_token Tsh tint) comms);
        fold_right sepcon emp (map (malloc_token Tsh tlock) locks);
        fold_right sepcon emp (map (malloc_token Tsh tbuffer) bufs);
        fold_right sepcon emp (map (malloc_token Tsh tint) reads);
        fold_right sepcon emp (map (malloc_token Tsh tint) lasts);
        data_at sh1 tbuffer (vint 0) (Znth 0 bufs);
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
   SEP (data_at sh (tarray (tptr tint) N) reads (gv _reading); data_at sh (tarray (tptr tint) N) lasts (gv _last_read);
        data_at_ Tsh tint (Znth r reads); data_at_ Tsh tint (Znth r lasts))
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (data_at sh (tarray (tptr tint) N) reads (gv _reading); data_at sh (tarray (tptr tint) N) lasts (gv _last_read);
        data_at Tsh tint Empty (Znth r reads); data_at Tsh tint (vint 1) (Znth r lasts)).

Definition latest_read (h : hist) v :=
  (* initial condition *)
  ((forall t r w, h t = Some (AE r w) -> w = Empty -> r = Empty) /\ v = vint 1) \/
  v <> Empty /\ exists n, h n = Some (AE v Empty) /\
  forall t r w, h t = Some (AE r w) -> w = Empty -> r <> Empty -> (t <= n)%nat.

(* last_read retains the last buffer read, while reading is reset to Empty. *)
Definition start_read_spec :=
 DECLARE _start_read
  WITH r : Z, reading : val, last_read : val, lock : val, comm : val, reads : list val, lasts : list val,
    locks : list val, comms : list val, bufs : list val, sh : share, sh1 : share, sh2 : share, b0 : Z,
    g : gname, g0 : gname, g1 : gname, g2 : gname, h : hist
  PRE [ _r OF tint ]
   PROP (0 <= b0 < B; readable_share sh; readable_share sh1; readable_share sh2; isptr (Znth r comms); latest_read h (vint b0))
   LOCAL (temp _r (vint r); gvar _reading reading; gvar _last_read last_read; gvar _lock lock; gvar _comm comm)
   SEP (data_at sh1 (tarray (tptr tint) N) reads (gv _reading); data_at sh1 (tarray (tptr tint) N) lasts (gv _last_read);
        data_at sh1 (tarray (tptr tint) N) comms (gv _comm); data_at sh1 (tarray (tptr tlock) N) locks (gv _lock);
        data_at_ Tsh tint (Znth r reads); data_at Tsh tint (vint b0) (Znth r lasts);
        comm_loc sh2 (Znth r locks) (Znth r comms) g g0 g1 g2 bufs sh gsh2 h;
        EX v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs);
        ghost_var gsh1 (vint b0) g0)
  POST [ tint ]
   EX b : Z, EX t : nat, EX v0 : val, EX v : Z,
   PROP (0 <= b < B; if eq_dec v0 Empty then b = b0 else v0 = vint b;
         latest_read (map_upd h t (AE v0 Empty)) (vint b))
   LOCAL (temp ret_temp (vint b))
   SEP (data_at sh1 (tarray (tptr tint) N) reads (gv _reading); data_at sh1 (tarray (tptr tint) N) lasts (gv _last_read);
        data_at sh1 (tarray (tptr tint) N) comms (gv _comm); data_at sh1 (tarray (tptr tlock) N) locks (gv _lock);
        data_at Tsh tint (vint b) (Znth r reads); data_at Tsh tint (vint b) (Znth r lasts);
        comm_loc sh2 (Znth r locks) (Znth r comms) g g0 g1 g2 bufs sh gsh2 (map_upd h t (AE v0 Empty));
        data_at sh tbuffer (vint v) (Znth b bufs);
        ghost_var gsh1 (vint b) g0).
(* And bufs[b] is the most recent buffer completed by finish_write. *)

Definition finish_read_spec :=
 DECLARE _finish_read
  WITH r : Z, reading : val, reads : list val, sh : share
  PRE [ _r OF tint ]
   PROP (readable_share sh)
   LOCAL (temp _r (vint r); gvar _reading reading)
   SEP (data_at sh (tarray (tptr tint) N) reads (gv _reading); data_at_ Tsh tint (Znth r reads))
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (data_at sh (tarray (tptr tint) N) reads (gv _reading); data_at Tsh tint Empty (Znth r reads)).

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
    sh1 : share, lsh : share, shs : list share, g : list gname, g0 : list gname, g1 : list gname, g2 : list gname,
    h : list hist, sh0 : share
  PRE [ ]
   PROP (0 <= b < B; 0 <= b0 < B; Forall (fun x => 0 <= x < B) lasts; Zlength h = N; Zlength shs = N;
         readable_share sh1; readable_share lsh; Forall readable_share shs;
         sepalg_list.list_join sh0 shs Tsh; Forall isptr comms; b <> b0; ~In b lasts; ~In b0 lasts)
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _comm comm;
          gvar _lock lock)
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms (gv _comm);
        data_at sh1 (tarray (tptr tlock) N) locks (gv _lock);
        fold_right sepcon emp (map (fun r =>
          comm_loc lsh (Znth r locks) (Znth r comms) (Znth r g) (Znth r g0)
            (Znth r g1) (Znth r g2) bufs (Znth r shs) gsh2 (Znth r h)) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun r => ghost_var gsh1 (vint b0) (Znth r g1) *
          ghost_var gsh1 (vint (@Znth Z (-1) r lasts)) (Znth r g2)) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i b0 then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts i) sh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs)) (upto (Z.to_nat B))))
  POST [ tvoid ]
   EX lasts' : list Z, EX h' : list hist,
   PROP (Forall (fun x => 0 <= x < B) lasts';
         Forall2 (fun h1 h2 => exists t v, h2 = map_upd h1 t (AE v (vint b))) h h';
         ~In b lasts')
   LOCAL ()
   SEP (data_at Ews tint Empty writing; data_at Ews tint (vint b) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts') last_taken;
        data_at sh1 (tarray (tptr tint) N) comms (gv _comm);
        data_at sh1 (tarray (tptr tlock) N) locks (gv _lock);
        fold_right sepcon emp (map (fun r =>
          comm_loc lsh (Znth r locks) (Znth r comms) (Znth r g) (Znth r g0)
            (Znth r g1) (Znth r g2) bufs (Znth r shs) gsh2 (Znth r h')) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun r => ghost_var gsh1 (vint b) (Znth r g1) *
          ghost_var gsh1 (vint (@Znth Z (-1) r lasts')) (Znth r g2)) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i b then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts' i) sh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs)) (upto (Z.to_nat B)))).

(* client function specs *)
Definition reader_spec :=
 DECLARE _reader
  WITH arg : val, x : Z * val * val * val * val * val * list val * list val * list val * list val * list val *
                      share * share * share * gname * gname * gname * gname
  PRE [ _arg OF tptr tvoid ]
   let '(r, reading, last_read, lock, comm, buf, reads, lasts, locks, comms, bufs, sh1, sh2, sh, g, g0, g1, g2) := x in
   PROP (readable_share sh; readable_share sh1; readable_share sh2; isptr (Znth r comms))
   LOCAL (temp _arg arg; gvar _reading reading; gvar _last_read last_read;
          gvar _lock lock; gvar _comm comm; gvar _bufs buf)
   SEP (data_at Tsh tint (vint r) arg; malloc_token Tsh tint arg;
        data_at sh1 (tarray (tptr tint) N) reads (gv _reading); data_at sh1 (tarray (tptr tint) N) lasts (gv _last_read);
        data_at sh1 (tarray (tptr tint) N) comms (gv _comm); data_at sh1 (tarray (tptr tlock) N) locks (gv _lock);
        data_at_ Tsh tint (Znth r reads); data_at_ Tsh tint (Znth r lasts);
        data_at sh1 (tarray (tptr tbuffer) B) bufs (gv _buf);
        comm_loc sh2 (Znth r locks) (Znth r comms) g g0 g1 g2 bufs sh gsh2 empty_map;
        EX v : Z, data_at sh tbuffer (vint v) (Znth 1 bufs);
        ghost_var gsh1 (vint 1) g0)
  POST [ tptr tvoid ] PROP () LOCAL () SEP ().

Definition writer_spec :=
 DECLARE _writer
  WITH arg : val, x : val * val * val * val * val * val * list val * list val * list val * share * share *
                      share * list share * list gname * list gname * list gname * list gname
  PRE [ _arg OF tptr tvoid ]
   let '(writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs, g, g0, g1, g2) := x in
   PROP (Zlength shs = N; readable_share sh1; readable_share lsh; Forall readable_share shs;
         sepalg_list.list_join sh0 shs Tsh; Zlength g1 = N; Zlength g2 = N; Forall isptr comms)
   LOCAL (temp _arg arg; gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken;
          gvar _lock lock; gvar _comm comm; gvar _bufs buf)
   SEP (data_at_ Ews tint writing; data_at_ Ews tint last_given; data_at_ Ews (tarray tint N) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms (gv _comm);
        data_at sh1 (tarray (tptr tlock) N) locks (gv _lock);
        data_at sh1 (tarray (tptr tbuffer) B) bufs (gv _buf);
        fold_right sepcon emp (map (fun r =>
          comm_loc lsh (Znth r locks) (Znth r comms) (Znth r g) (Znth r g0)
            (Znth r g1) (Znth r g2) bufs (Znth r shs) gsh2 empty_map) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2);
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i 0 then sh = sh0 else if eq_dec i 1 then sh = sh0 else sh = Tsh) &&
          EX v : Z, data_at sh tbuffer (vint v) (Znth i bufs)) (upto (Z.to_nat B))))
  POST [ tptr tvoid ] PROP () LOCAL () SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog [] gv
  POST [ tint ] main_post prog [] gv.

(* Create the environment containing all function specs. *)
Definition Gprog : funspecs := ltac:(with_library prog [release_spec; makelock_spec; spawn_spec;
  surely_malloc_spec; memset_spec; atomic_exchange_spec; initialize_channels_spec; initialize_reader_spec;
  start_read_spec; finish_read_spec; initialize_writer_spec; start_write_spec; finish_write_spec;
  reader_spec; writer_spec; main_spec]).

(*Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.*)

Lemma lock_struct_array : forall sh z (v : list val) p,
  data_at sh (tarray (tptr (Tstruct _lock_t noattr)) z) v p =
  data_at sh (tarray (tptr tlock) z) v p.
Proof.
  intros.
  unfold data_at, field_at, at_offset; rewrite !data_at_rec_eq; simpl; f_equal.
  apply ND_prop_ext.
  split; intros [? [? [? [? ?]]]]; (split; [| split; [| split; [| split]]]); auto.
  + destruct p; auto.
    inv H2.
    1: inv H4.
    constructor.
    intros.
    apply H8 in H2; clear H8.
    inv H2. inv H4.
    econstructor; [reflexivity |].
    exact H5.
  + destruct p; auto.
    inv H2.
    1: inv H4.
    constructor.
    intros.
    apply H8 in H2; clear H8.
    inv H2. inv H4.
    econstructor; [reflexivity |].
    exact H5.
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

Lemma latest_read_Empty : forall h n v, newer h n ->
  latest_read (map_upd h n (AE Empty Empty)) v <-> latest_read h v.
Proof.
  unfold latest_read; split; intros [(Hnone & ?) | (? & m & Hin & Hlatest)]; subst.
  - left; split; auto; intros.
    eapply (Hnone t); eauto.
    unfold map_upd; if_tac; auto.
    subst; erewrite newer_out in H0 by eauto; discriminate.
  - right; split; auto; exists m.
    unfold map_upd in Hin; destruct (eq_dec m n); [congruence|].
    split; auto; intros; eapply Hlatest; eauto.
    unfold map_upd; if_tac; auto.
    subst; erewrite newer_out in H1 by eauto; discriminate.
  - left; split; auto.
    unfold map_upd; intros ???.
    if_tac; eauto.
    inversion 1; auto.
  - right; split; auto; exists m.
    unfold map_upd.
    apply newer_out in H.
    split; [if_tac; auto; congruence|].
    intros ??; if_tac; eauto.
    intro; inversion 1; contradiction.
Qed.

Lemma latest_read_new : forall h n v, newer h n -> v <> Empty ->
  latest_read (map_upd h n (AE v Empty)) v.
Proof.
  unfold latest_read; intros.
  right; split; auto; exists n.
  unfold map_upd; rewrite eq_dec_refl; split; auto.
  intros ???; if_tac; [subst; auto|].
  intro Ht; specialize (H t); rewrite Ht in H; lapply H; [omega | discriminate].
Qed.

Lemma comm_loc_isptr : forall lsh l c g g0 g1 g2 b sh gsh h,
  comm_loc lsh l c g g0 g1 g2 b sh gsh h = !!(isptr l) && comm_loc lsh l c g g0 g1 g2 b sh gsh h.
Proof.
  intros; eapply local_facts_isptr with (P := fun l => _); [|eauto].
  unfold comm_loc, AE_loc.
  rewrite lock_inv_isptr; entailer!.
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
