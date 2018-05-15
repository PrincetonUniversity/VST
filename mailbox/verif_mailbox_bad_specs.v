Require Import mailbox.general_atomics.
Require Import VST.progs.conclib.
Require Import VST.progs.ghost.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox_bad.

Set Bullet Behavior "Strict Subproofs".

(* standard VST prelude *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* import funspecs from concurrency library *)
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition load_SC_spec := DECLARE _load_SC load_SC_spec.
Definition store_SC_spec := DECLARE _store_SC store_SC_spec.
Definition AEX_SC_spec := DECLARE _atomic_exchange_SC AEX_SC_spec.

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
Definition comm_R bufs sh gsh g g0 g1 g2 h b := EX b1 : Z, EX b2 : Z,
  !!(-1 <= b < B /\ Forall (fun a => match a with AE v1 v2 =>
       exists r w, v1 = vint r /\ v2 = vint w /\ -1 <= r < B /\ -1 <= w < B end) h /\
     apply_hist (vint 0) h = Some (vint b) /\
     last_two_reads (rev h) = (vint b1, vint b2) /\ repable_signed b1 /\ repable_signed b2) &&
  ghost_ref h g * ghost_var gsh (vint b1) g0 * ghost_var gsh (last_write (rev h)) g1 *
  ghost_var gsh (prev_taken (rev h)) g2 *
  if eq_dec b (-1) then EX v : _, data_at sh tbuffer (Vint v) (Znth b2 bufs Vundef)
  else EX v : _, data_at sh tbuffer (Vint v) (Znth b bufs Vundef).

Definition comm_inv (good : bool) comm bufs sh g g0 g1 g2 gsh :=
  EX v : Z, data_at Tsh tint (vint v) comm *
    if good then EX h : _, comm_R bufs sh gsh g g0 g1 g2 h v
    (* A bad reader's location buffer is modeled as holding all the buffer indices, since it may
       choose to read from any of the data buffers at any time. *)
    else (EX h : list AE_hist_el, ghost_ref h g) * (EX v : val, ghost_var gsh v g0) *
      (EX v : val, ghost_var gsh v g1) * (EX v : val, ghost_var gsh v g2) *
      fold_right sepcon emp (map (fun p => EX v : _, data_at sh tbuffer (Vint v) p) bufs).
(* The ghost_hist assertion is held by the thread, while the resource invariant is part of the
   global invariant. *)
(* The share ownership here is purely "defensive", modeling the fact that no one will write to a
   data buffer that is held by a good reader. *)

Notation hist := (list (nat * AE_hist_el)).

Definition comm_loc good lsh comm g g0 g1 g2 bufs sh gsh h :=
  invariant (comm_inv good comm bufs sh g g0 g1 g2 gsh) * ghost_hist lsh (h : hist) g.

(*(* To model the fact that only the writer can write to data buffers, we maintain an invariant that
   the values in the buffers are determined by the history held by the writer. *)
Notation bufs_hist := (list (nat * (Z * Z))).

Definition get_val i h := match find (fun '(b, v) => Z.eqb b i) (rev h) with Some (_, v) => v | _ => 0 end.

Definition bufs_inv bufs g := EX h : list (Z * Z), ghost_ref h g *
  fold_right sepcon emp (map (fun i => data_at Tsh tbuffer (vint (get_val i h)) (Znth i bufs Vundef))
    (upto (length bufs))).*)

(* messaging system function specs *)
(* At initialization, we have an oracle telling us which components can be trusted. The code is the
   same either way, but we only need to reason about the correctness of trusted components.
   A bad writer is modeled by setting all the readers to "bad": either way, no meaningful
   communication occurs and the most we can prove is that good components don't overflow buffers,
   dereference null pointers, etc. *)
Definition initialize_channels_spec :=
 DECLARE _initialize_channels
  WITH lgood : list bool, comm : val, buf : val, reading : val, last_read : val,
       sh1 : share, shs : list share, shg : share
  PRE [ ]
   PROP (Zlength lgood = N; Zlength shs = N; sepalg_list.list_join sh1 shs Tsh;
         (* shg is the maximum share that can be held by the writer *)
         sepalg_list.list_join sh1 (map snd (filter fst (combine lgood shs))) shg)
   LOCAL (gvar _comm comm; gvar _bufs buf; gvar _reading reading; gvar _last_read last_read)
   SEP (data_at_ Ews (tarray (tptr tint) N) comm; data_at_ Ews (tarray (tptr tbuffer) B) buf;
        data_at_ Ews (tarray (tptr tint) N) reading; data_at_ Ews (tarray (tptr tint) N) last_read)
  POST [ tvoid ]
   EX comms : list val, EX bufs : list val, EX reads : list val, EX lasts : list val,
     EX g : list val, EX g0 : list val, EX g1 : list val, EX g2 : list val,
   PROP (Forall isptr comms; Forall isptr bufs;
         Zlength g = N; Zlength g0 = N; Zlength g1 = N; Zlength g2 = N)
   LOCAL ()
   SEP (data_at Ews (tarray (tptr tint) N) comms comm;
        data_at Ews (tarray (tptr tbuffer) B) bufs buf;
        data_at Ews (tarray (tptr tint) N) reads reading;
        data_at Ews (tarray (tptr tint) N) lasts last_read;
        fold_right sepcon emp (map (fun r =>
          comm_loc (Znth r lgood false) Tsh (Znth r comms Vundef) (Znth r g Vundef) (Znth r g0 Vundef)
            (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh) gsh2 ([] : hist)) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g0);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) comms);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) reads);
        fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) lasts);
        (* The shares retained here are those that will be passed to the writer. *)
        data_at sh1 tbuffer (vint 0) (Znth 0 bufs Vundef);
        fold_right sepcon emp (map (data_at shg tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs));
        fold_right sepcon emp (map (data_at_ Tsh tint) reads);
        fold_right sepcon emp (map (data_at_ Tsh tint) lasts)).

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
  (Forall (fun x => let '(_, AE r w) := x in w = Empty ->
    match r with Vint i => Int.signed i < 0 \/ Int.signed i >= B | _ => True end) h /\ v = 1) \/
  0 <= v < B /\ exists n, In (n, AE (vint v) Empty) h /\
  Forall (fun x => let '(m, AE r w) := x in w = Empty -> forall v', r = vint v' -> 0 <= v' < B ->
    (m <= n)%nat) h.

(* last_read retains the last buffer read, while reading is reset to Empty. *)
Definition start_read_spec :=
 DECLARE _start_read
  WITH r : Z, reading : val, last_read : val, comm : val, reads : list val, lasts : list val,
    good : bool, comms : list val, bufs : list val, sh : share, sh1 : share, sh2 : share, b0 : Z,
    g : val, g0 : val, g1 : val, g2 : val, h : hist
  PRE [ _r OF tint ]
   PROP (0 <= b0 < B; readable_share sh; readable_share sh1; readable_share sh2; isptr (Znth r comms Vundef);
        latest_read h b0)
   LOCAL (temp _r (vint r); gvar _reading reading; gvar _last_read last_read; gvar _comm comm)
   SEP (data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at_ Tsh tint (Znth r reads Vundef); data_at Tsh tint (vint b0) (Znth r lasts Vundef);
        comm_loc good sh2 (Znth r comms Vundef) g g0 g1 g2 bufs sh gsh2 h;
        if good then EX v : _, data_at sh tbuffer (Vint v) (Znth b0 bufs Vundef) else emp;
        ghost_var gsh1 (vint b0) g0)
  POST [ tint ]
   EX b : Z, EX t : nat, EX v0 : Z,
   PROP (0 <= b < B; b = if (Z.leb 0 v0 && Z.ltb v0 B)%bool then v0 else b0;
         latest_read (h ++ [(t, AE (vint v0) Empty)]) b)
   LOCAL (temp ret_temp (vint b))
   SEP (data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at Tsh tint (vint b) (Znth r reads Vundef); data_at Tsh tint (vint b) (Znth r lasts Vundef);
        comm_loc good sh2 (Znth r comms Vundef) g g0 g1 g2 bufs sh gsh2 (h ++ [(t, AE (vint v0) Empty)]);
        if good then EX v : _, data_at sh tbuffer (Vint v) (Znth b bufs Vundef) else emp;
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
Fixpoint make_shares shs lasts i : list share :=
  match lasts with
  | [] => []
  | (g, b) :: rest => if (negb g || Z.eqb b i)%bool then make_shares (tl shs) rest i
                 else hd Share.bot shs :: make_shares (tl shs) rest i
  end.

Definition finish_write_spec :=
 DECLARE _finish_write
  WITH writing : val, last_given : val, last_taken : val, comm : val, comms : list val, bufs : list val,
    lgood : list bool, b : Z, b0 : Z, lasts : list Z,
    sh1 : share, lsh : share, shs : list share, g : list val, g0 : list val, g1 : list val, g2 : list val,
    h : list hist, sh0 : share
  PRE [ ]
   PROP (0 <= b < B; 0 <= b0 < B; Forall (fun x => 0 <= x < B) lasts; Zlength h = N;
         Zlength lgood = N; Zlength shs = N;
         readable_share sh1; readable_share lsh; Forall readable_share shs;
         sepalg_list.list_join sh0 shs Tsh; Forall isptr comms; b <> b0; ~In b lasts; ~In b0 lasts)
   LOCAL (gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken; gvar _comm comm)
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        fold_right sepcon emp (map (fun r =>
          comm_loc (Znth r lgood false) lsh (Znth r comms Vundef) (Znth r g Vundef) (Znth r g0 Vundef)
            (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh) gsh2 (Znth r h [])) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun r => ghost_var gsh1 (vint b0) (Znth r g1 Vundef) *
          ghost_var gsh1 (vint (Znth r lasts (-1))) (Znth r g2 Vundef)) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i b0 then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs (combine lgood lasts) i) sh) &&
          EX v : _, data_at sh tbuffer (Vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B))))
  POST [ tvoid ]
   EX lasts' : list Z, EX h' : list hist,
   PROP (Forall (fun x => 0 <= x < B) lasts';
         Forall2 (fun h1 h2 => exists t v, h2 = h1 ++ [(t, AE v (vint b))]) h h';
         ~In b lasts')
   LOCAL ()
   SEP (data_at Ews tint Empty writing; data_at Ews tint (vint b) last_given;
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts') last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        fold_right sepcon emp (map (fun r =>
          comm_loc (Znth r lgood false) lsh (Znth r comms Vundef) (Znth r g Vundef) (Znth r g0 Vundef)
            (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh) gsh2 (Znth r h' [])) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun r => ghost_var gsh1 (vint b) (Znth r g1 Vundef) *
          ghost_var gsh1 (vint (Znth r lasts' (-1))) (Znth r g2 Vundef)) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i b then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs (combine lgood lasts') i) sh) &&
          EX v : _, data_at sh tbuffer (Vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B)))).

(* client function specs *)
Definition reader_spec :=
 DECLARE _reader
  WITH arg : val, x : Z * bool * val * val * val * val * list val * list val * list val * list val *
                      share * share * share * val * val * val * val
  PRE [ _arg OF tptr tvoid ]
   let '(r, good, reading, last_read, comm, buf, reads, lasts, comms, bufs, sh1, sh2, sh, g, g0, g1, g2) := x in
   PROP (readable_share sh; readable_share sh1; readable_share sh2; isptr (Znth r comms Vundef);
         Forall isptr bufs)
   LOCAL (temp _arg arg; gvar _reading reading; gvar _last_read last_read;
          gvar _comm comm; gvar _bufs buf)
   SEP (data_at Tsh tint (vint r) arg; malloc_token Tsh (sizeof tint) arg;
        data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at_ Tsh tint (Znth r reads Vundef); data_at_ Tsh tint (Znth r lasts Vundef);
        data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
        comm_loc good sh2 (Znth r comms Vundef) g g0 g1 g2 bufs sh gsh2 [];
        if good then EX v : _, data_at sh tbuffer (Vint v) (Znth 1 bufs Vundef) else emp;
        ghost_var gsh1 (vint 1) g0)
  POST [ tptr tvoid ] PROP () LOCAL () SEP ().

Definition writer_spec :=
 DECLARE _writer
  WITH arg : val, x : list bool * val * val * val * val * val * list val * list val * share * share *
                      share * list share * share * list val * list val * list val * list val
  PRE [ _arg OF tptr tvoid ]
   let '(lgood, writing, last_given, last_taken, comm, buf, comms, bufs, sh1, lsh, sh0, shs, shg, g, g0, g1, g2) := x in
   PROP (Zlength lgood = N; Zlength shs = N; readable_share sh1; readable_share lsh;
         readable_share sh0; Forall readable_share shs;
         sepalg_list.list_join sh0 shs Tsh;
         sepalg_list.list_join sh0 (map snd (filter fst (combine lgood shs))) shg;
         Zlength g1 = N; Zlength g2 = N; Forall isptr comms)
   LOCAL (temp _arg arg; gvar _writing writing; gvar _last_given last_given; gvar _last_taken last_taken;
          gvar _comm comm; gvar _bufs buf)
   SEP (data_at_ Ews tint writing; data_at_ Ews tint last_given; data_at_ Ews (tarray tint N) last_taken;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
        fold_right sepcon emp (map (fun r =>
          comm_loc (Znth r lgood false) lsh (Znth r comms Vundef) (Znth r g Vundef) (Znth r g0 Vundef)
            (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh) gsh2 []) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1);
        fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2);
        fold_right sepcon emp (map (fun i => EX sh : share,
          !!(if eq_dec i 0 then sh = sh0 else if eq_dec i 1 then sh = sh0 else sh = shg) &&
          EX v : _, data_at sh tbuffer (Vint v) (Znth i bufs Vundef)) (upto (Z.to_nat B))))
  POST [ tptr tvoid ] PROP () LOCAL () SEP ().

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog [] u
  POST [ tint ] main_post prog [] u.

(* Create the environment containing all function specs. *)
Definition Gprog : funspecs := ltac:(with_library prog [spawn_spec;
  surely_malloc_spec; memset_spec; AEX_SC_spec; load_SC_spec; store_SC_spec;
  initialize_channels_spec; initialize_reader_spec;
  start_read_spec; finish_read_spec; initialize_writer_spec; start_write_spec; finish_write_spec;
  reader_spec; writer_spec; main_spec]).

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

Opaque upto.

Lemma list_join_minus : forall l (sh : share) shs sh1 sh2 (Hl : Zlength l = Zlength shs)
  (Hall : sepalg_list.list_join sh shs sh1)
  (Hsome : sepalg_list.list_join sh (map snd (filter fst (combine l shs))) sh2),
  sepalg_list.list_join sh2 (map snd (filter (fun '(b, _) => negb b) (combine l shs))) sh1.
Proof.
  induction l.
  { simpl; intros.
    symmetry in Hl; apply Zlength_nil_inv in Hl; subst.
    inv Hall; inv Hsome; constructor. }
  intros.
  destruct shs; [apply Zlength_nil_inv in Hl; discriminate|].
  inv Hall.
  rewrite !Zlength_cons in Hl.
  destruct a; simpl in *.
  - inv Hsome.
    assert (w0 = w1) by (eapply sepalg.join_eq; eauto); subst.
    eapply IHl; eauto; omega.
  - destruct (sepalg_list.list_join_assoc1 (sepalg.join_comm H2) H4) as (x & ? & Ho).
    exploit IHl; eauto; [omega|].
    intro Hx; destruct (sepalg_list.list_join_assoc2 Hx Ho) as (? & ? & ?).
    econstructor; eauto.
Qed.

Lemma fold_right_emp : forall l (Hemp : Forall (eq emp) l), fold_right sepcon emp l = emp.
Proof.
  induction 1; auto; simpl; subst.
  rewrite emp_sepcon; auto.
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

Lemma latest_read_bad : forall h n r v, repable_signed r -> r < 0 \/ r >= B ->
  latest_read (h ++ [(n, AE (vint r) Empty)]) v <-> latest_read h v.
Proof.
  unfold latest_read; split; intros [(Hnone & ?) | (? & m & Hin & Hlatest)]; subst.
  - rewrite Forall_app in Hnone; destruct Hnone; auto.
  - right; split; auto; exists m.
    rewrite in_app in Hin; destruct Hin as [? | [X | ?]]; [| | contradiction].
    + split; auto.
      rewrite Forall_app in Hlatest; destruct Hlatest; auto.
    + exploit (repr_inj_signed r v); auto; try omega; try congruence.
      apply repable_buf; omega.
  - rewrite Forall_app; left; repeat split; auto.
    constructor; auto.
    rewrite Int.signed_repr; auto.
  - right; split; auto; exists m.
    rewrite in_app; split; auto.
    rewrite Forall_app; split; auto.
    constructor; auto; intros.
    exploit (repr_inj_signed r v'); auto; try omega; try congruence.
    apply repable_buf; omega.
Qed.

Corollary latest_read_Empty : forall h n v,
  latest_read (h ++ [(n, AE Empty Empty)]) v <-> latest_read h v.
Proof.
  intros; apply latest_read_bad; auto; omega.
Qed.

Lemma latest_read_new : forall h n v, newer h n -> 0 <= v < B ->
  latest_read (h ++ [(n, AE (vint v) Empty)]) v.
Proof.
  unfold latest_read; intros.
  right; split; auto; exists n.
  rewrite in_app; simpl; split; auto.
  rewrite Forall_app; split; auto.
  eapply Forall_impl; [|eauto]; intros.
  destruct a, a; simpl in *; intros; omega.
Qed.
