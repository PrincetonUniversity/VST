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
   PROP (Forall isptr comms; Zlength g = N; Zlength g0 = N; Zlength g1 = N; Zlength g2 = N)
   LOCAL ()
   SEP (data_at Ews (tarray (tptr tint) N) comms comm;
        data_at Ews (tarray (tptr tbuffer) B) bufs buf;
        data_at Ews (tarray (tptr tint) N) reads reading;
        data_at Ews (tarray (tptr tint) N) lasts last_read;
        fold_right sepcon emp (map (fun r =>
          comm_loc (Znth r lgood false) Tsh (Znth r comms Vundef) (Znth r g Vundef) (Znth r g0 Vundef)
            (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh) gsh2 ([] : hist)) (upto (Z.to_nat N)));
        fold_right sepcon emp (map (ghost_hist Tsh ([] : hist)) g);
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

(*Ltac cancel_for_forward_call ::= repeat (rewrite ?sepcon_andp_prop', ?sepcon_andp_prop);
  repeat (apply andp_right; [auto; apply prop_right; auto|]); fast_cancel.*)

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

(*Lemma comm_R_precise : forall bufs sh gsh g0 g1 g2 h v,
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
Qed.*)

Opaque upto.

Lemma body_initialize_channels : semax_body Vprog Gprog f_initialize_channels initialize_channels_spec.
Proof.
  start_function.
  rewrite <- seq_assoc.
  forward_for_simple_bound B (EX i : Z, PROP ()
    LOCAL (gvar _comm comm; gvar _bufs buf; gvar _reading reading; gvar _last_read last_read)
    SEP (data_at_ Ews (tarray (tptr tint) N) comm;
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
    LOCAL (gvar _comm comm; gvar _bufs buf; gvar _reading reading; gvar _last_read last_read)
    SEP (EX comms : list val, EX g : list val, EX g0 : list val, EX g1 : list val,
         EX g2 : list val, !!(Zlength comms = i /\ Forall isptr comms /\ Zlength g = i /\
           Zlength g0 = i /\ Zlength g1 = i /\ Zlength g2 = i) &&
          (data_at Ews (tarray (tptr tint) N) (comms ++ repeat Vundef (Z.to_nat (N - i))) comm *
           fold_right sepcon emp (map (fun r => comm_loc (Znth r lgood false) Tsh (Znth r comms Vundef)
             (Znth r g Vundef) (Znth r g0 Vundef) (Znth r g1 Vundef) (Znth r g2 Vundef) bufs
             (Znth r shs Tsh) gsh2 []) (upto (Z.to_nat i))) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g0) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 0)) g1) *
           fold_right sepcon emp (map (ghost_var gsh1 (vint 1)) g2) *
           fold_right sepcon emp (map (malloc_token Tsh (sizeof tint)) comms));
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
         (* Actually, we need to give away shares of these for each bad reader. *)
         fold_right sepcon emp (map (@data_at CompSpecs Tsh tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs));
         fold_right sepcon emp (map (malloc_token Tsh (sizeof tbuffer)) bufs))).
  { unfold N; computable. }
  { unfold N; computable. }
  { Exists ([] : list val) ([] : list val) ([] : list val) ([] : list val) ([] : list val)
      ([] : list val) ([] : list val) Tsh; rewrite !data_at__eq; entailer!.
    - rewrite sublist_same; auto; omega.
    - erewrite <- sublist_same with (al := bufs), sublist_next at 1; eauto; try (unfold B, N in *; omega).
      simpl; cancel. }
  { Intros comms g g0 g1 g2 reads lasts sh.
    forward_malloc tint c.
    forward.
    forward.
    forward_malloc tint rr.
    forward.
    forward_malloc tint ll.
    eapply (ghost_alloc (Tsh, vint 1)); auto with init.
    eapply (ghost_alloc (Tsh, vint 0)); auto with init.
    eapply (ghost_alloc (Tsh, vint 1)); auto with init.
    eapply (ghost_alloc (Some (Tsh, [] : hist), Some ([] : hist))); auto with init.
    Intros g' g0' g1' g2'.
    rewrite <- hist_ref_join_nil by apply Share.nontrivial.
    repeat match goal with |-context[ghost (Tsh, ?v) ?g] => fold (ghost_var Tsh v g) end.
    erewrite <- !ghost_var_share_join with (sh0 := Tsh) by eauto.
    match goal with H : sepalg_list.list_join sh1 (sublist i N shs) sh |- _ =>
      erewrite sublist_next in H; try omega; inversion H as [|????? Hj1 Hj2] end.
    apply sepalg.join_comm in Hj1; eapply sepalg_list.list_join_assoc1 in Hj2; eauto.
    destruct Hj2 as (sh' & ? & Hsh').
    erewrite <- data_at_share_join with (sh0 := sh) by (apply Hsh').
    Intros.
    gather_SEP 1 3 5 7 13 27; eapply make_inv with (Q := comm_inv (Znth i lgood false)
      c bufs (Znth i shs Tsh) g' g0' g1' g2' gsh2).
    { unfold comm_inv.
      Exists 0; cancel.
      destruct (Znth _ lgood false) eqn: Hgood.
      - Exists (@nil AE_hist_el); unfold comm_R.
        Exists 1 1; unfold last_two_reads, last_write, prev_taken; simpl; entailer!.
        Exists Int.zero; entailer!.
      - Exists (@nil AE_hist_el) (vint 1) (vint 0) (vint 1); entailer!.
        admit. (* need to peel off shares of all buffers for bad reader *) }
    { unfold comm_inv, comm_R; prove_objective. }
    forward.
    Exists (comms ++ [c]) (g ++ [g']) (g0 ++ [g0']) (g1 ++ [g1']) (g2 ++ [g2'])
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
    subst; rewrite Zlength_correct, Nat2Z.id.
    rewrite !sem_cast_neutral_ptr by auto.
    erewrite map_ext_in; [unfold comm_loc; cancel|].
    intros; rewrite In_upto, <- Zlength_correct in *.
    rewrite !app_Znth1; try omega; reflexivity. }
  Intros comms g g0 g1 g2 reads lasts sh.
  match goal with H : sepalg_list.list_join sh1 (sublist N N shs) sh |- _ =>
    rewrite sublist_nil in H; inv H end.
  forward.
  rewrite !app_nil_r.
  Exists comms bufs reads lasts g g0 g1 g2.
  (* entailer! is slow *)
  apply andp_right; [apply prop_right; repeat (split; auto)|].
  apply andp_right; auto; cancel.
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

Lemma body_start_read : semax_body Vprog Gprog f_start_read start_read_spec.
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
  set (c := Znth r comms Vundef).
  forward_call (AEX_SC_witness c (-1)
    ((if good then EX v : _, data_at sh tbuffer (Vint v) (Znth b0 bufs Vundef) else emp) *
     ghost_var gsh1 (vint b0) g0 * ghost_hist sh2 h g)
    (fun _ : Z => comm_inv good c bufs sh g g0 g1 g2 gsh2) [0]
    (fun b => let b' := if (Z.leb 0 b && Z.ltb b B)%bool then b else b0 in
      !!(-1 <= b' < B /\ (good = true -> -1 <= b < B)) &&
      (if good then EX v : _, data_at sh tbuffer (Vint v) (Znth b' bufs Vundef) else emp) *
      ghost_var gsh1 (vint b') g0 *
      EX t : _, !!(newer h t) && ghost_hist sh2 (h ++ [(t, AE (vint b) Empty)]) g)).
  { simpl; unfold comm_loc; cancel. }
  { split; [split; computable|].
    apply wand_view_shifts2; simpl.
    assert (sh2 <> Share.bot) by (intro; subst; contradiction unreadable_bot).
    unfold comm_inv.
    view_shift_intro v0; view_shift_intros.
    if_tac.
    - view_shift_intro v'; view_shift_intro l.
      unfold comm_R at 1.
      view_shift_intro b1; view_shift_intro b2; view_shift_intros.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_ref _ _)).
      rewrite (sepcon_comm _ (ghost_hist _ _ _)).
      rewrite <- !sepcon_assoc, 7sepcon_assoc.
      apply view_shift_assert with (PP := hist_incl h l).
      { apply sepcon_derives_prop, hist_ref_incl; auto. }
      intros ?%hist_incl_lt.
      etransitivity; [apply view_shift_sepcon1, hist_add'; auto|].
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g0)).
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh1 _ g0)).
      erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto.
      view_shift_intros.
      exploit (repr_inj_signed b1 b0); auto.
      { apply repable_buf; omega. }
      intro; subst.
      rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1,
        ghost_var_update with (v'0 := vint (if eq_dec v0 (-1) then b0 else v0))|].
      erewrite <- ghost_var_share_join by eauto.
      apply derives_view_shift; Exists Tsh v0; entailer!.
      { apply repable_buf; auto. }
      rewrite <- wand_sepcon_adjoint.
      rewrite <- !exp_sepcon1, <- !exp_sepcon2.
      Exists (length l) (-1); entailer!.
      { if_tac; auto; omega. }
      rewrite <- !exp_sepcon1, <- !exp_sepcon2.
      Exists (l ++ [AE (vint v0) Empty]); unfold comm_R.
      rewrite rev_app_distr; simpl; rewrite last_two_reads_cons; simpl; cancel.
      rewrite prev_taken_cons; unfold last_write; simpl.
      assert (apply_hist (vint 0) (l ++ [AE (vint v0) Empty]) = Some Empty).
      { rewrite apply_hist_app; replace (apply_hist _ _) with (Some (vint v0)); simpl.
        apply eq_dec_refl. }
      if_tac.
      + subst; simpl.
        Exists b0 b2 v'; entailer!.
        { rewrite Forall_app; repeat (constructor; auto).
          exists (-1), (-1); repeat split; auto; omega. }
        rewrite sepcon_comm; auto.
      + destruct (eq_dec (vint v0) Empty).
        { apply Empty_inj in e; auto; contradiction. }
        Intros v''; Exists v'' v0 b0 v'.
        rewrite Zle_imp_le_bool, Fcore_Zaux.Zlt_bool_true by omega; simpl; entailer!.
        replace (last_two_reads _) with (vint b0, vint b2).
        rewrite Forall_app; repeat constructor; auto.
        exists v0, (-1); repeat split; auto; omega.
    - view_shift_intro l.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_ref _ _)).
      rewrite (sepcon_comm _ (ghost_hist _ _ _)).
      rewrite !sepcon_emp, <- !sepcon_assoc, 5sepcon_assoc.
      apply view_shift_assert with (PP := hist_incl h l).
      { apply sepcon_derives_prop, hist_ref_incl; auto. }
      intros ?%hist_incl_lt.
      etransitivity; [apply view_shift_sepcon1, hist_add'; auto|].
      view_shift_intro b0'.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g0)).
      rewrite <- !exp_sepcon1.
      rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh1 _ g0)).
      erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto.
      rewrite !sepcon_andp_prop'; apply view_shift_prop; intro; subst.
      rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1, ghost_var_update|].
      erewrite <- ghost_var_share_join by eauto.
      apply derives_view_shift; Exists Tsh (Int.signed (Int.repr v0)).
      rewrite sepcon_andp_prop'; apply andp_right.
      { entailer!.
        apply Int.signed_range. }
      rewrite Int.repr_signed; cancel.
      rewrite <- wand_sepcon_adjoint; cancel.
      set (v0' := Int.signed (Int.repr v0)).
      Exists (-1) (length l) (vint (if ((0 <=? v0') && (v0' <? B))%bool then v0' else b0))
        (l ++ [AE (vint v0) Empty]); entailer!.
      { rewrite <- and_assoc; split; [|discriminate].
        pose proof (Zle_cases 0 v0'); destruct (0 <=? v0'); simpl; try omega.
        pose proof (Zlt_cases v0' B); destruct (v0' <? B); omega. }
      rewrite (sepcon_comm _ (ghost_ref _ _)), !sepcon_assoc; apply sepcon_derives; auto; entailer!.
      rewrite sepcon_comm; auto. }
  Intros b.
  match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROP () (LOCALx (temp _t'2 (Val.of_bool (Z.leb 0 b && Z.ltb b B)) :: Q) (SEPx R))) end.
  { forward.
    entailer!.
    rewrite Zle_imp_le_bool by omega; simpl.
    unfold Int.lt, Int.add; simpl.
    rewrite !Int.signed_repr by (auto; computable).
    pose proof (Zlt_cases b B); if_tac; destruct (b <?B); auto; unfold B, N in *; omega. }
  { forward.
    entailer!.
    rewrite Fcore_Zaux.Zle_bool_false; auto. }
  set (b' := if ((0 <=? b) && (b <? B))%bool then b else b0) in * |- *.
  Intros t.
  forward_if (PROP () LOCAL (temp _b (vint b'); temp _rr (Znth r reads Vundef); temp _r (vint r);
      gvar _reading reading; gvar _last_read last_read; gvar _comm comm)
    SEP (comm_loc good sh2 c g g0 g1 g2 bufs sh gsh2 (h ++ [(t, AE (vint b) Empty)]);
         if good then EX v : _, data_at sh tbuffer (Vint v) (Znth b' bufs Vundef) else emp;
         ghost_var gsh1 (vint b') g0;
         data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
         data_at_ Tsh tint (Znth r reads Vundef); data_at Tsh tint (vint b') (Znth r lasts Vundef);
         data_at sh1 (tarray (tptr tint) N) comms comm)).
  - forward.
    replace b' with b by (subst b'; if_tac; auto; discriminate).
    entailer!.
  - forward.
    replace b' with b0 by (subst b'; if_tac; auto; discriminate).
    entailer!.
  - forward.
    forward.
    Exists b' t b; entailer!.
    split.
    + pose proof (Zle_cases 0 b); destruct (0 <=? b); subst b'; simpl; try if_tac; omega.
    + destruct (eq_dec b (-1)); subst.
      { rewrite latest_read_Empty; auto. }
      destruct ((0 <=? b) && (b <? B))%bool eqn: Hb; subst b'.
      * apply latest_read_new; auto; omega.
      * apply latest_read_bad; auto.
        rewrite andb_false_iff, Z.leb_nle, Z.ltb_nlt in Hb; omega.
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
      Exists i; entailer!.
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
    destruct a, shs.
    { rewrite Zlength_nil, !Zlength_correct in *; omega. }
    rewrite Zlength_cons in *; simpl; rewrite IHl1; [|omega].
    rewrite sublist_S_cons with (i0 := Z.succ _); [|rewrite Zlength_correct; omega].
    unfold Z.succ; rewrite !Z.add_simpl_r.
    if_tac; auto.
Qed.

Lemma make_shares_out : forall b lgood lasts shs (Hb : ~In b lasts)
  (Hlen1 : Zlength lgood = Zlength shs) (Hlen2 : Zlength lasts = Zlength shs),
  make_shares shs (combine lgood lasts) b = map snd (filter fst (combine lgood shs)).
Proof.
  induction lgood; auto; intros.
  destruct lasts; simpl.
  { symmetry in Hlen2; apply Zlength_nil_inv in Hlen2; subst.
    apply Zlength_nil_inv in Hlen1; discriminate. }
  destruct shs; simpl.
  { apply Zlength_nil_inv in Hlen1; discriminate. }
  destruct (z =? b) eqn: Heq; [rewrite Z.eqb_eq in Heq; subst; contradiction Hb; simpl; auto|].
  rewrite !Zlength_cons in *; rewrite IHlgood; try omega; simpl in *; [|tauto].
  destruct a; auto.
Qed.

Lemma make_shares_ext : forall i d l l' lgood shs (Hlen : Zlength l = Zlength l')
  (Hi : forall j, 0 <= j < Zlength l -> Znth j l d = i <-> Znth j l' d = i),
  make_shares shs (combine lgood l) i = make_shares shs (combine lgood l') i.
Proof.
  induction l; destruct l'; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; auto;
    try (rewrite Zlength_correct in *; omega).
  exploit (Hi 0); [rewrite Zlength_correct; omega|].
  rewrite !Znth_0_cons; intro Hiff.
  destruct lgood; auto; simpl.
  rewrite (IHl l'); try omega.
  destruct (negb b); auto.
  destruct (a =? i) eqn: Ha, (z =? i) eqn: Hz; auto; rewrite ?Z.eqb_eq, Z.eqb_neq in *; tauto.
  { intros; exploit (Hi (j + 1)); [omega|].
    rewrite !Znth_pos_cons, !Z.add_simpl_r; auto; omega. }
Qed.

Lemma make_shares_add : forall i i' d lasts lgood j shs (Hj : 0 <= j < Zlength lasts)
  (Hi : Znth j lasts d = i) (Hgood : Znth j lgood false = true) (Hi' : i' <> i)
  (Hlen : Zlength shs >= Zlength lasts),
  exists shs1 shs2, make_shares shs (combine lgood lasts) i = shs1 ++ shs2 /\
    make_shares shs (combine lgood (upd_Znth j lasts i')) i = shs1 ++ Znth j shs Tsh :: shs2.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; try omega.
  destruct lgood; [rewrite Znth_nil in Hgood; discriminate|].
  destruct (eq_dec j 0).
  - subst; rewrite Znth_0_cons in Hi', IHlasts; rewrite !Znth_0_cons; simpl.
    rewrite Znth_0_cons in Hgood; subst; simpl.
    rewrite Z.eqb_refl, Zlength_cons, sublist_1_cons, sublist_same; auto; try omega; simpl.
    rewrite <- Z.eqb_neq in Hi'; rewrite Hi'.
    eexists [], _; simpl; split; eauto.
  - rewrite Znth_pos_cons in Hi; [|omega].
    rewrite Znth_pos_cons in Hgood; [|omega].
    rewrite Znth_pos_cons; [|omega].
    exploit (IHlasts lgood (j - 1) shs); auto; try omega.
    intros (shs1 & shs2 & Heq1 & Heq2).
    rewrite upd_Znth_cons; [simpl | omega].
    exists (if (negb b || (a =? i))%bool then shs1 else t :: shs1), shs2; rewrite Heq1, Heq2;
      if_tac; auto.
Qed.

Lemma make_shares_In : forall i lasts lgood x shs (Hx : 0 <= x < Zlength lasts)
  (Hi : Znth x lasts 0 <> i) (Hgood : Znth x lgood false = true)
  (Hlen : Zlength shs >= Zlength lasts),
  In (Znth x shs Tsh) (make_shares shs (combine lgood lasts) i).
Proof.
  induction lasts; simpl; intros.
  - rewrite Zlength_nil in *; omega.
  - destruct shs; rewrite !Zlength_cons in *; [rewrite Zlength_nil, Zlength_correct in *; omega|].
    destruct lgood; [rewrite Znth_nil in Hgood; discriminate|].
    destruct (eq_dec x 0); simpl.
    + subst; rewrite Znth_0_cons in Hi; rewrite Znth_0_cons in Hgood; rewrite Znth_0_cons.
      rewrite <- Z.eqb_neq in Hi; rewrite Hi; subst; simpl; auto.
    + rewrite Znth_pos_cons in Hi; [|omega].
      rewrite Znth_pos_cons in Hgood; [|omega].
      rewrite Znth_pos_cons; [|omega].
      exploit (IHlasts lgood (x - 1) shs); eauto; try omega.
      if_tac; simpl; auto.
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
    destruct a.
    destruct (_ || _)%bool.
    + apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
      exploit IHlasts; eauto; [omega|].
      intro; eapply sepalg.join_sub_trans; eauto; eexists; eauto.
    + inversion Hsh2 as [|????? Hj1']; subst.
      pose proof (sepalg.join_eq Hj1 Hj1'); subst.
      eapply IHlasts; eauto; omega.
Qed.

(* up *)
Lemma combine_nil : forall {A B} (l : list A), combine l (@nil B) = [].
Proof.
  destruct l; auto.
Qed.

Lemma make_shares_join : forall i d lasts lgood shs sh0 j sh1 sh2
  (Hlen : Zlength shs >= Zlength lasts)
  (Hsh1 : sepalg_list.list_join sh0 shs sh1)
  (Hsh2 : sepalg_list.list_join sh0 (make_shares shs (combine lgood lasts) i) sh2)
  (Hin : 0 <= j < Zlength shs) (Hj : Znth j lasts d = i),
  exists sh', sepalg.join sh2 (Znth j shs Tsh) sh'.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (rewrite Zlength_correct in *; omega); try omega.
  { rewrite Znth_nil in Hj.
    rewrite combine_nil in Hsh2; inv Hsh2.
    exploit (Znth_In j (t :: shs) Tsh); [rewrite Zlength_cons; auto|].
    intro Hin'; apply in_split in Hin'.
    destruct Hin' as (? & ? & Heq); rewrite Heq in Hsh1.
    apply list_join_comm in Hsh1; inv Hsh1; eauto. }
  destruct (eq_dec j 0).
  - subst j; rewrite Znth_0_cons in Hj; rewrite Znth_0_cons; subst.
    destruct lgood; simpl in Hsh2; [inv Hsh2; inv Hsh1; eauto|].
    rewrite Z.eqb_refl in Hsh2.
    inversion Hsh1 as [|????? Hj1 Hj2]; subst.
    apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
    exploit (make_shares_sub i (combine lgood lasts)); eauto.
    { rewrite Zlength_combine, Z.ge_le_iff, Z.min_le_iff; omega. }
    { destruct b; eauto. }
    intro; eapply sepalg.join_sub_joins_trans; eauto.
  - rewrite Znth_pos_cons in Hj; [|omega].
    rewrite Znth_pos_cons; [|omega].
    inversion Hsh1 as [|????? Hj1 Hj2]; subst.
    destruct lgood; simpl in Hsh2.
    { inv Hsh2.
      apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
      eapply (IHlasts []); eauto; try constructor; omega. }
    destruct (_ || _)%bool.
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
  intros.
  repeat unfold_data_at 1%nat.
  rewrite !field_at_data_at'; simpl; entailer.
  apply data_at_value_cohere; auto.
Qed.

Lemma make_shares_add' : forall i i' d lasts lgood j shs (Hj : 0 <= j < Zlength lasts)
  (Hi : Znth j lasts d = i) (Hgood : Znth j lgood false = false)
  (Hlen : Zlength shs >= Zlength lasts),
  make_shares shs (combine lgood (upd_Znth j lasts i')) i = make_shares shs (combine lgood lasts) i.
Proof.
  induction lasts; destruct shs; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; try omega.
  destruct lgood; auto; simpl.
  destruct (eq_dec j 0).
  - subst; rewrite Znth_0_cons in IHlasts; rewrite Znth_0_cons in Hgood; rewrite !Znth_0_cons; subst; simpl.
    rewrite Zlength_cons, sublist_1_cons, sublist_same; auto; omega.
  - rewrite Znth_pos_cons in Hi by omega.
    rewrite Znth_pos_cons in Hgood by omega.
    rewrite upd_Znth_cons by omega; simpl.
    rewrite IHlasts by (auto; omega); auto.
Qed.

Lemma make_shares_ext' : forall i d l l' lgood shs (Hlen : Zlength l = Zlength l')
  (Hi : forall j, 0 <= j < Zlength l -> Znth j lgood false = true -> Znth j l d = i <-> Znth j l' d = i),
  make_shares shs (combine lgood l) i = make_shares shs (combine lgood l') i.
Proof.
  induction l; destruct l'; simpl; intros; rewrite ?Zlength_cons, ?Zlength_nil in *; auto;
    try (rewrite Zlength_correct in *; omega).
  destruct lgood; auto; simpl.
  rewrite (IHl l'); try omega.
  destruct b; auto; simpl.
  exploit (Hi 0); [rewrite Zlength_correct; omega | apply Znth_0_cons|].
  rewrite !Znth_0_cons; intro Hiff.
  destruct (a =? i) eqn: Ha, (z =? i) eqn: Hz; auto; rewrite ?Z.eqb_eq, Z.eqb_neq in *; tauto.
  { intros; exploit (Hi (j + 1)); rewrite ?Znth_pos_cons, ?Z.add_simpl_r; auto; omega. }
Qed.

(* The relationship between the last_taken array and the shares held by the writer is
   preserved by the action of the loop body. *)
Lemma upd_write_shares : forall bufs b b0 lgood lasts shs sh0 (Hb : 0 <= b < B) (Hb0 : 0 <= b0 < B)
  (Hlasts : Forall (fun x : Z => 0 <= x < B) lasts) (Hshs : Zlength shs = N)
  (Hread : Forall readable_share shs) (Hsh0 : sepalg_list.list_join sh0 shs Tsh)
  (Hdiff : b <> b0) (Hout : ~ In b lasts) (Hout0 : ~ In b0 lasts) (Hlasts : Zlength lasts = N)
  (Hlgood : Zlength lgood = N) i (Hh' : 0 <= i < N) good (Hgood : good = Znth i lgood false)
  b' (Hb' : good = true -> -1 <= b' < B) sh (Hsh : sh = Znth i shs Tsh)
  shi (Hshi : sepalg_list.list_join sh0
         (map snd (filter fst (sublist (i + 1) N (combine lgood shs)))) shi)
  bsh (Hbsh : sepalg_list.list_join shi
    (map snd (if good then [(good, sh)] else [])) bsh)
  h' (Hh' : Zlength h' = i) lasts' (Hlasts' : lasts' = map (fun i =>
    if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0) (upto 3))
  lasts'' (Hlasts'' : lasts'' = map (fun i =>
    if eq_dec (Znth i (h' ++ [vint b']) Vundef) Empty then b0 else Znth i lasts 0) (upto 3)) vb,
(if good then EX v : _, data_at sh tbuffer (Vint v)
     (Znth (if eq_dec b' (-1) then Znth i lasts 0 else b0) bufs Vundef)
 else emp) *
(data_at shi tbuffer (Vint vb) (Znth b bufs Vundef) *
 fold_right sepcon emp (upd_Znth b (map (fun a => EX sh2 : share,
   !! (if eq_dec a b0 then sepalg_list.list_join sh0
         (make_shares shs (combine lgood (sublist 0 i lasts')) a) sh2
       else if eq_dec a b then sepalg_list.list_join sh0
         (map snd (filter fst (sublist i N (combine lgood shs)))) sh2
       else sepalg_list.list_join sh0
         (make_shares shs (combine lgood lasts') a) sh2) &&
      (EX v : _, data_at sh2 tbuffer (Vint v) (Znth a bufs Vundef))) (upto 5)) emp))
|-- fold_right sepcon emp (map (fun a => EX sh2 : share,
   !! (if eq_dec a b0 then sepalg_list.list_join sh0
        (make_shares shs (combine lgood (sublist 0 (i + 1) lasts'')) a) sh2
      else if eq_dec a b then sepalg_list.list_join sh0
        (map snd (filter fst (sublist (i + 1) N (combine lgood shs)))) sh2
      else sepalg_list.list_join sh0
        (make_shares shs (combine lgood lasts'') a) sh2) &&
    (EX v : _, data_at sh2 tbuffer (Vint v) (Znth a bufs Vundef))) (upto 5)).
Proof.
  intros.
  assert (readable_share sh).
  { subst sh; apply Forall_Znth; auto; omega. }
  set (lasti := Znth i lasts 0).
  exploit (Znth_In i lasts 0); [omega | intro Hini].
  assert (lasti <> b) as Hneq.
  { intro; match goal with H : ~In b lasts |- _ => contradiction H end; subst b lasti; auto. }
  assert (lasti <> b0) as Hneq0.
  { intro; match goal with H : ~In b0 lasts |- _ => contradiction H end; subst b0 lasti; auto. }
  match goal with |- _ * (_ * fold_right sepcon emp (upd_Znth b ?l _)) |-- _ =>
    set (l0 := upd_Znth b l (EX v : _, @data_at CompSpecs shi tbuffer (Vint v) (Znth b bufs Vundef))) end.
  assert (Zlength l0 = B).
  { subst l0; rewrite upd_Znth_Zlength; rewrite Zlength_map, Zlength_upto; auto. }
  assert (0 <= lasti < B).
  { apply Forall_Znth; auto; omega. }
  apply derives_trans with (fold_right sepcon emp (
    if eq_dec b' (-1) then upd_Znth lasti l0
            (EX sh1 : share, !!(exists sh', sepalg_list.list_join sh0 (make_shares shs
             (combine lgood lasts') lasti) sh' /\ if good then sepalg.join sh' sh sh1 else sh1 = sh') &&
            (EX v1 : _, @data_at CompSpecs sh1 tbuffer (Vint v1) (Znth lasti bufs Vundef)))
          else upd_Znth b0 l0 (EX sh1 : share, !!(exists sh', sepalg_list.list_join sh0 (make_shares shs
            (combine lgood (sublist 0 i lasts')) b0) sh' /\ if good then sepalg.join sh' sh sh1 else sh1 = sh') &&
            (EX v1 : _, @data_at CompSpecs sh1 tbuffer (Vint v1) (Znth b0 bufs Vundef))))).
  { eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply sepcon_derives, derives_refl]|].
    { instantiate (1 := EX v : _, data_at shi tbuffer (Vint v) (Znth b bufs Vundef)).
      Exists vb; auto. }
    rewrite replace_nth_sepcon.
    destruct (eq_dec b' (-1)).
    - rewrite extract_nth_sepcon with (i := lasti) by (subst l0; omega).
      erewrite upd_Znth_diff', Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; simpl; try (unfold B, N in *; omega).
      destruct (eq_dec lasti b0); [contradiction Hneq0; auto|].
      destruct (eq_dec lasti b); [contradiction Hneq; auto|].
      Intros ish v2.
      assert (exists sh', sepalg.join ish sh sh') as (sh' & ?).
      { subst sh; eapply make_shares_join; eauto.
        + subst lasts'; setoid_rewrite Hshs; rewrite Zlength_map, Zlength_upto, ?Z2Nat.id; unfold N; simpl; omega.
        + setoid_rewrite Hshs; auto.
        + subst lasts'; rewrite Znth_map', Znth_upto by (unfold N in *; simpl; omega).
          rewrite Znth_overflow; auto; omega. }
      rewrite (extract_nth_sepcon (upd_Znth lasti l0 (EX sh : share, _)) lasti) by (rewrite upd_Znth_Zlength; omega).
      rewrite upd_Znth_twice, upd_Znth_same by omega.
      rewrite <- sepcon_assoc; apply sepcon_derives; auto.
      if_tac.
      + Intros v1.
        eapply derives_trans; [apply data_at_buffer_cohere; auto|].
        erewrite data_at_share_join by eauto.
        Exists sh' v1; entailer!; eauto.
      + Exists ish v2; entailer!; eauto.
    - Intros.
      rewrite extract_nth_sepcon with (i := b0) by (subst l0; omega).
      erewrite upd_Znth_diff, Znth_map, Znth_upto; rewrite ?Z2Nat.id; auto; try (unfold B, N in *; simpl; omega).
      destruct (eq_dec b0 b0); [|contradiction].
      Intros ish v2.
      assert (exists sh', sepalg.join ish sh sh') as (sh' & ?).
      { subst sh; eapply make_shares_join; eauto.
        + subst lasts'; setoid_rewrite Hshs; rewrite Zlength_sublist; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; unfold N in *; simpl; omega.
        + setoid_rewrite Hshs; auto.
        + rewrite Znth_overflow; auto.
          subst lasts'; rewrite Zlength_sublist; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; unfold N in *; simpl; omega. }
      rewrite (extract_nth_sepcon (upd_Znth b0 l0 (EX sh : share, _)) b0) by (rewrite upd_Znth_Zlength; omega).
      rewrite upd_Znth_twice, upd_Znth_same by omega.
      rewrite <- sepcon_assoc; apply sepcon_derives; auto.
      if_tac.
      + Intros v1.
        eapply derives_trans; [apply data_at_buffer_cohere; auto|].
        erewrite data_at_share_join by eauto.
        Exists sh' v1; entailer!; eauto.
      + Exists ish v2; entailer!; eauto. }
  apply derives_refl'; f_equal.
  match goal with |- ?l = _ => assert (Zlength l = B) as Hlen end.
  { destruct (eq_dec b' (-1)); auto; rewrite upd_Znth_Zlength; auto; omega. }
  apply list_Znth_eq' with (d := FF).
  { rewrite Hlen, Zlength_map, Zlength_upto; auto. }
  rewrite Hlen; intros.
  assert (0 <= j <= B) by omega.
  erewrite Znth_map, Znth_upto by auto.
  assert (forall j, j <> Zlength h' \/ vint b' <> Empty -> (if eq_dec (Znth j h' Vundef) Empty then b0 else Znth j lasts 0) =
    if eq_dec (Znth j (h' ++ [vint b']) Vundef) Empty then b0 else Znth j lasts 0) as Heq.
  { intros ? Hcase.
    destruct (zlt j0 (Zlength h')); [rewrite app_Znth1; auto|].
    rewrite Znth_overflow, app_Znth2 by auto.
    destruct (eq_dec j0 (Zlength h')).
    - if_tac; [discriminate|].
      destruct (eq_dec (Znth _ _ _) _); auto.
      subst; rewrite Zminus_diag, Znth_0_cons in e0; destruct Hcase; try contradiction.
    - rewrite (Znth_overflow _ [_]); auto.
      rewrite Zlength_cons, Zlength_nil; omega. }
  destruct (eq_dec j lasti); [|destruct (eq_dec j b0)]; subst.
  - destruct (eq_dec b' (-1)).
    + rewrite upd_Znth_same by omega.
      destruct (eq_dec lasti b0); [contradiction|].
      destruct (eq_dec lasti b); [contradiction|].
      f_equal; extensionality; f_equal; f_equal.
      destruct (Znth _ lgood _) eqn: Hgood.
      * exploit (make_shares_add lasti b0 0 (map (fun i => if eq_dec (Znth i h' Vundef) Empty then b0
          else Znth i lasts 0) (upto (Z.to_nat N))) lgood (Zlength h') shs); auto.
        { erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; try omega.
          rewrite Znth_overflow by omega.
          destruct (eq_dec Vundef Empty); [discriminate | auto]. }
        { setoid_rewrite Hshs; rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
        simpl; intros (shsa & shsb & Hshs1 & Hshs2).
        rewrite Hshs1.
        erewrite make_shares_ext, Hshs2.
        apply prop_ext; split.
        -- intros (? & Hj1 & Hj2).
           apply list_join_comm.
           apply sepalg.join_comm in Hj2; destruct (sepalg_list.list_join_assoc2 Hj1 Hj2) as (? & ? & ?).
           econstructor; eauto.
           apply list_join_comm; auto.
        -- intro Hj; apply list_join_comm in Hj.
           inversion Hj as [|????? Hj1 Hj2]; subst.
           apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
           do 2 eexists; eauto; apply list_join_comm; auto.
        -- rewrite upd_Znth_Zlength; rewrite !Zlength_map; auto.
        -- rewrite Zlength_map, Zlength_upto; intros.
           rewrite Znth_map', Znth_upto by omega.
           destruct (zlt j (Zlength h')); [|destruct (eq_dec j (Zlength h'))].
           ++ rewrite app_Znth1, upd_Znth_diff; auto; try omega.
              erewrite Znth_map, Znth_upto; auto; [reflexivity | omega].
           ++ subst; rewrite Znth_app1, eq_dec_refl, upd_Znth_same; auto; reflexivity.
           ++ rewrite Znth_overflow, upd_Znth_diff; auto; [|rewrite Zlength_app, Zlength_cons, Zlength_nil; omega].
              erewrite Znth_map, Znth_upto; auto; [|omega].
              rewrite Znth_overflow with (al := h'); [reflexivity | omega].
      * erewrite make_shares_ext'.
        apply prop_ext; split; [intros [? []]; subst|]; eauto.
        { rewrite !Zlength_map; auto. }
        { rewrite Zlength_map; intros.
          erewrite !Znth_map with (b1 := 0), !Znth_upto by (auto; rewrite ?Zlength_upto in *; omega).
          rewrite Heq; [reflexivity|].
          left; intro; subst; destruct (Znth (Zlength h') lgood false); discriminate. }
    + subst l0; rewrite 2upd_Znth_diff; auto; try omega.
      erewrite Znth_map, Znth_upto; try assumption.
      destruct (eq_dec lasti b0); [contradiction|].
      destruct (eq_dec lasti b); [contradiction|].
      erewrite make_shares_ext'; eauto.
      rewrite Zlength_map, Zlength_upto; intros.
      erewrite Znth_map', Znth_map, !Znth_upto; auto; try omega.
      rewrite Heq; [reflexivity|].
      destruct (eq_dec j (Zlength h')); auto.
      subst; right; intros ?%Empty_inj; auto; apply repable_buf; auto.
  - assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i h' Vundef) Empty then b0
      else Znth i lasts 0) (upto (Z.to_nat N)))) = Zlength h') as Hlenh.
    { rewrite Zlength_sublist; try omega.
      rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
    assert (Zlength (sublist 0 (Zlength h') (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint b']) Vundef) Empty
      then b0 else Znth i lasts 0) (upto (Z.to_nat N)))) = Zlength h') as Hlenh'.
    { rewrite Zlength_sublist; try omega.
      rewrite Zlength_map, Zlength_upto, Z2Nat.id; omega. }
    simpl in *.
    destruct (eq_dec b' (-1)).
    + assert (EX sh : share, !! sepalg_list.list_join sh0 (make_shares shs (combine lgood (sublist 0 (Zlength h')
          (map (fun i : Z => if eq_dec (Znth i h' Vundef) Empty then b0 else Znth i lasts 0) (upto (Z.to_nat N))))) b0)
          sh && (EX v1 : _, data_at sh tbuffer (Vint v1) (Znth b0 bufs Vundef)) =
        EX sh : share, !! sepalg_list.list_join sh0 (make_shares shs (combine lgood (sublist 0 (Zlength h' + 1)
          (map (fun i : Z => if eq_dec (Znth i (h' ++ [vint b']) Vundef) Empty then b0 else Znth i lasts 0)
          (upto (Z.to_nat N))))) b0) sh && (EX v0 : _, data_at sh tbuffer (Vint v0) (Znth b0 bufs Vundef))).
      { erewrite sublist_split with (mid := Zlength h')(hi := Zlength h' + 1), sublist_len_1, Znth_map', Znth_upto;
          auto; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; try omega.
        rewrite Znth_app1; auto.
        rewrite <- (app_nil_r (sublist 0 (Zlength h') _)).
        replace lgood with (sublist 0 (Zlength h') lgood ++ sublist (Zlength h') (Zlength lgood) lgood).
        assert (Zlength (sublist 0 (Zlength h') lgood) = Zlength h').
        { rewrite Zlength_sublist; omega. }
        rewrite !combine_app', combine_nil; try omega.
        subst; rewrite eq_dec_refl, app_nil_r, make_shares_app; simpl.
        replace (make_shares (sublist _ _ _) _ _) with (@nil share).
        erewrite app_nil_r, make_shares_ext; eauto; try omega.
        rewrite Hlenh; intros; erewrite !Znth_sublist, Znth_map', Znth_map, !Znth_upto; auto;
          rewrite ?Zlength_upto; simpl; try (unfold N in *; omega).
        rewrite app_Znth1; [reflexivity | omega].
        { destruct (sublist (Zlength h') (Zlength lgood) lgood); auto; simpl.
          rewrite Z.eqb_refl, orb_true_r, combine_nil; auto. }
        { rewrite !Zlength_combine, !Z.min_r; rewrite ?Zlength_cons, ?Zlength_nil; try omega.
          - setoid_rewrite Hshs; omega.
          - rewrite Zlength_sublist; omega. }
        { unfold N; simpl; omega. }
        { unfold N; simpl; omega. }
        { rewrite sublist_rejoin, sublist_same; auto; omega. } }
      destruct (eq_dec lasti (-1)); subst l0; [rewrite upd_Znth_diff | rewrite 2upd_Znth_diff]; auto; try omega.
      erewrite Znth_map, Znth_upto; auto; destruct (eq_dec b0 b0); [eauto | contradiction].
    + rewrite upd_Znth_same by omega.
      erewrite sublist_split with (mid := Zlength h')(hi := Zlength h' + 1), sublist_len_1, Znth_map', Znth_upto;
        auto; rewrite ?Zlength_map, ?Zlength_upto, ?Z2Nat.id; simpl; try (unfold N in *; omega).
      rewrite Znth_app1; auto.
      rewrite <- (app_nil_r (sublist 0 (Zlength h') _)).
      set (good := Znth (Zlength h') lgood false).
      replace lgood with (sublist 0 (Zlength h') lgood ++ sublist (Zlength h') (Zlength lgood) lgood).
      assert (Zlength (sublist 0 (Zlength h') lgood) = Zlength h').
      { rewrite Zlength_sublist; omega. }
      rewrite !combine_app', combine_nil; try omega.
      replace (combine (sublist (Zlength h') _ _) _) with [(good,
        if eq_dec (vint b') Empty then b0 else Znth (Zlength h') lasts 0)]; simpl.
      rewrite app_nil_r, make_shares_app; simpl.
      destruct good eqn: Hgood; simpl.
      * destruct (eq_dec (vint b') Empty).
        { apply Empty_inj in e; [contradiction|].
          apply repable_buf; auto. }
        fold lasti; destruct (lasti =? b0) eqn: Heq'; [rewrite Z.eqb_eq in Heq'; contradiction|].
        rewrite hd_Znth, Znth_sublist; rewrite ?Hlenh'; try setoid_rewrite Hshs; rewrite ?Zlength_combine, ?Z.min_l; try omega.
        f_equal; extensionality; f_equal; f_equal.
        replace (Zlength (sublist _ _ lgood)) with (Zlength h').
        erewrite make_shares_ext.
        apply prop_ext; split.
        -- intros (? & Hj1 & Hj2).
           apply sepalg.join_comm in Hj2; destruct (sepalg_list.list_join_assoc2 Hj1 Hj2) as (? & ? & ?).
           apply list_join_comm; econstructor; eauto.
           erewrite Znth_indep; eauto.
           setoid_rewrite Hshs; auto.
        -- intro Hj; apply list_join_comm in Hj; inversion Hj as [|????? Hj1 Hj2]; subst.
           apply sepalg.join_comm in Hj1; destruct (sepalg_list.list_join_assoc1 Hj1 Hj2) as (? & ? & ?).
           do 2 eexists; eauto.
           erewrite Znth_indep; eauto.
           setoid_rewrite Hshs; auto.
        -- omega.
        -- rewrite Hlenh; intros; erewrite !Znth_sublist, Znth_map', Znth_map, !Znth_upto;
             rewrite ?Zlength_upto; simpl; try (unfold N in *; omega).
           rewrite app_Znth1; [reflexivity | omega].
      * f_equal; extensionality; f_equal; f_equal.
        erewrite app_nil_r, make_shares_ext'.
        apply prop_ext; split; [intros (? & ? & ?); subst|]; eauto.
        { omega. }
        { rewrite Hlenh; intros ??; erewrite !Znth_sublist, !Znth_map with (b1 := 0), !Znth_upto; rewrite ?Zlength_upto; try (unfold N in *; simpl; omega).
          rewrite Z.add_0_r; intro; rewrite Heq; [reflexivity|].
          left; intro; subst; destruct (Znth (Zlength h') lgood false); discriminate. }
      * rewrite Zlength_combine, Z.min_l, Zlength_cons, Zlength_nil by omega.
        setoid_rewrite Hshs; omega.
      * erewrite sublist_next by omega; simpl.
        rewrite combine_nil; subst good; auto.
      * rewrite sublist_rejoin, sublist_same by omega; auto.
  - transitivity (Znth j l0 FF).
    { destruct (eq_dec b' (-1)); rewrite upd_Znth_diff; auto; omega. }
    subst l0.
    destruct (eq_dec j b).
    + subst; rewrite upd_Znth_same; auto.
      apply mpred_ext.
      * Exists shi; entailer!.
      * Intros sh1.
        assert (sh1 = shi) by (eapply list_join_eq; eauto; apply HshP).
        subst; auto.
    + rewrite upd_Znth_diff' by auto.
      erewrite Znth_map, Znth_upto by auto.
      destruct (eq_dec j b0); [contradiction|].
      destruct (eq_dec j b); [contradiction|].
      simpl; erewrite make_shares_ext'; eauto.
      rewrite Zlength_map, Zlength_upto; intros.
      erewrite Znth_map', Znth_map, !Znth_upto; auto; try omega.
      destruct (zlt j0 (Zlength h')); [rewrite app_Znth1 by auto; reflexivity|].
      rewrite Znth_overflow, app_Znth2 by auto.
      destruct (eq_dec Vundef Empty); [discriminate|].
      destruct (eq_dec _ Empty); [|reflexivity].
      destruct (eq_dec j0 (Zlength h')); [|rewrite Znth_overflow in e; try discriminate].
      split; intro; subst; tauto.
      { rewrite Zlength_cons, Zlength_nil; omega. }
Qed.

Lemma body_finish_write : semax_body Vprog Gprog f_finish_write finish_write_spec.
Proof.
  start_function.
  rewrite sepcon_map; Intros.
  forward.
  forward.
  assert_PROP (Zlength (map (fun i => vint i) lasts) = N) by entailer!.
  rewrite Zlength_map in *.
  assert (Zlength (combine lgood lasts) = N).
  { rewrite Zlength_combine, Z.min_l; omega. }
  assert (Zlength (combine lgood shs) = N).
  { rewrite Zlength_combine, Z.min_l; omega. }
  rewrite <- seq_assoc.
  forward_for_simple_bound N (EX i : Z, PROP ( )
   LOCAL (temp _w (vint b); temp _last (vint b0); gvar _writing writing; gvar _last_given last_given;
          gvar _last_taken last_taken; gvar _comm comm)
   SEP (data_at Ews tint (vint b) writing; data_at Ews tint (vint b0) last_given;
        data_at sh1 (tarray (tptr tint) N) comms comm;
        EX t' : list nat, EX h' : list val, !!(Zlength t' = i /\ Zlength h' = i) &&
          fold_right sepcon emp (map (fun r => comm_loc (Znth r lgood false) lsh (Znth r comms Vundef)
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
              !!(if eq_dec a b0 then sepalg_list.list_join sh0 (make_shares shs (combine lgood (sublist 0 i lasts')) a) sh
                 else if eq_dec a b then sepalg_list.list_join sh0 (map snd (filter fst (sublist i N (combine lgood shs)))) sh
                 else sepalg_list.list_join sh0 (make_shares shs (combine lgood lasts') a) sh) &&
              EX v : _, @data_at CompSpecs sh tbuffer (Vint v) (Znth a bufs Vundef)) (upto (Z.to_nat B))))).
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
    rewrite sublist_nil, combine_nil; simpl.
    apply prop_ext.
    destruct (eq_dec a b0); [|destruct (eq_dec a b); [|reflexivity]].
    - split; intro Hx; [subst; constructor | inv Hx; auto].
    - subst; rewrite sublist_same, make_shares_out; unfold share in *; auto; try reflexivity; omega.
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
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
      [|rewrite Zlength_map; auto].
    erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, Z2Nat.id; auto; omega).
    destruct (zlt i i); [omega | rewrite app_nil_r].
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat B))) b) by (rewrite Zlength_map, Zlength_upto; auto).
    erewrite Znth_map, Znth_upto by (rewrite ?Zlength_upto, ?Z2Nat.id; auto; omega).
    Intros bsh.
    destruct (eq_dec b b0); [contradiction|].
    match goal with H : if eq_dec b b then _ else _ |- _ => rewrite eq_dec_refl in H end.
    match goal with H : sepalg_list.list_join _ (map _ _) _ |- _ =>
      rewrite sublist_split with (mid := i + 1), sublist_len_1 with (d := (false, Tsh)), filter_app,
        map_app, Znth_combine in H by omega; simpl in H;
        apply list_join_comm, sepalg_list.list_join_unapp in H;
        destruct H as (shi & Hshi & Hbsh) end.
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i); [|rewrite Zlength_map; auto].
    rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i); [|rewrite Zlength_map; auto].
    erewrite !Znth_map; rewrite ?Znth_upto; rewrite ?Znth_upto, ?Zlength_upto; rewrite ?Z2Nat.id; auto; try omega.
    rewrite Znth_overflow with (al := h'); [simpl | omega].
    destruct (zlt i i); [clear - l; omega|].
    set (gi := Znth i g Vundef).
    set (g0i := Znth i g0 Vundef).
    set (g1i := Znth i g1 Vundef).
    set (g2i := Znth i g2 Vundef).
    set (c := Znth i comms Vundef).
    set (sh := Znth i shs Tsh) in *.
    set (hi := Znth i h []).
    set (good := Znth i lgood false) in *.
    Intro vb.
    forward_call (AEX_SC_witness c b
      ((if good then data_at sh tbuffer (Vint vb) (Znth b bufs Vundef) else emp) *
      ghost_var gsh1 (vint b0) g1i * ghost_var gsh1 (vint (Znth i lasts 0)) g2i * ghost_hist lsh hi gi)
      (fun _ : Z => comm_inv good c bufs sh gi g0i g1i g2i gsh2) [0]
      (fun b' => !!(good = true -> b' = -1 \/ b' = b0) &&
        (if good then EX v : _, data_at sh tbuffer (Vint v)
          (Znth (if eq_dec b' (-1) then Znth i lasts 0 else b0) bufs Vundef) else emp) *
        ghost_var gsh1 (vint b) g1i *
        ghost_var gsh1 (vint (if eq_dec b' (-1) then b0 else Znth i lasts 0)) g2i *
        EX t : _, !!(newer hi t) && ghost_hist lsh (hi ++ [(t, AE (vint b') (vint b))]) gi)).
    { unfold comm_loc at 1; simpl; cancel.
      destruct good; simpl in *.
      + rewrite <- sepalg_list.list_join_1 in Hbsh.
        rewrite <- (data_at_share_join _ _ _ _ _ _ Hbsh); cancel.
      + inv Hbsh; subst Frame; simpl; cancel. }
    { lapply (repable_buf b); [|omega].
      split; auto.
      apply wand_view_shifts2.
      assert (lsh <> Share.bot) by (intro; subst; contradiction unreadable_bot).
      if_tac; unfold comm_inv; simpl.
      + view_shift_intro v0; view_shift_intro l.
        unfold comm_R at 1.
        view_shift_intro b1; view_shift_intro b2; view_shift_intro v'; view_shift_intros.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_ref _ _)).
        rewrite (sepcon_comm _ (ghost_hist _ _ _)).
        rewrite !sepcon_emp, <- !sepcon_assoc, 7sepcon_assoc.
        apply view_shift_assert with (PP := hist_incl hi l).
        { apply sepcon_derives_prop, hist_ref_incl; auto. }
        intros ?%hist_incl_lt.
        etransitivity; [apply view_shift_sepcon1, hist_add'; auto|].
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g1i)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh1 _ g1i)).
        erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto.
        view_shift_intros.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1,
          ghost_var_update with (v' := vint b)|].
        erewrite <- ghost_var_share_join by eauto.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g2i)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh1 _ g2i)).
        erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto.
        view_shift_intros.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1,
          ghost_var_update with (v' := vint (if eq_dec v0 (-1) then b0 else Znth i lasts 0))|].
        erewrite <- ghost_var_share_join by eauto.
        apply derives_view_shift; Exists Tsh v0.
        rewrite sepcon_andp_prop'; apply andp_right.
        { entailer!.
          apply repable_buf; auto. }
        cancel.
        rewrite <- wand_sepcon_adjoint.
        Exists (length l); cancel.
        Exists b; entailer!.
        rewrite <- exp_sepcon1, <- exp_sepcon2.
        Exists (l ++ [AE (vint v0) (vint b)]); unfold comm_R.
        rewrite !rev_app_distr; unfold last_write in *; simpl;
          rewrite last_two_reads_cons, prev_taken_cons.
        destruct (eq_dec (vint b) Empty).
        { apply Empty_inj in e; auto; subst; omega. }
        destruct (eq_dec b (-1)); [omega|].
        assert (Forall (fun a => match a with AE v1 v2 => exists r w,
          v1 = vint r /\ v2 = vint w /\ -1 <= r < B /\ -1 <= w < B end)
          (l ++ [AE (vint v0) (vint b)])).
        { rewrite Forall_app; repeat constructor; auto.
          exists v0, b; repeat (split; auto; try omega). }
        assert (apply_hist (vint 0) (l ++ [AE (vint v0) (vint b)]) = Some (vint b)).
        { rewrite apply_hist_app; replace (apply_hist _ _) with (Some (vint v0)); simpl.
          apply eq_dec_refl. }
        match goal with H : _ = prev_taken _ |- _ =>
          erewrite take_read in H by (rewrite rev_involutive; eauto) end.
        match goal with H : last_two_reads _ = _ |- _ => rewrite H in * end.
        if_tac; Intro v; Exists b1 b2 v vb.
        * subst; match goal with H : vint _ = _ |- _ => rewrite eq_dec_refl in H end.
          exploit (repr_inj_signed b2 (Znth (Zlength t') lasts 0)); auto.
          { apply Forall_Znth; [omega|].
            eapply Forall_impl; [|eauto]; simpl; intros; apply repable_buf; omega. }
          { simpl in *; congruence. }
          intro; rewrite !sepcon_andp_prop'; apply andp_right.
          { entailer!. }
          erewrite find_write_read by (rewrite ?rev_involutive; eauto; discriminate); simpl.
          replace (fst _) with (vint b0).
          rewrite (sepcon_comm _ (ghost_ref _ _)), !sepcon_assoc; apply sepcon_derives; auto; cancel.
          apply andp_right; [apply prop_right; auto | subst; cancel].
        * destruct (eq_dec (vint v0) Empty); [apply Empty_inj in e; auto; contradiction|].
          exploit (write_val (rev l)); [rewrite rev_involutive; eauto|].
          intros [|]; [contradiction|].
          exploit (repr_inj_signed v0 b0); auto.
          { apply repable_buf; omega. }
          { congruence. }
          exploit (repr_inj_signed (Znth (Zlength t') lasts 0) b1); auto.
          { apply Forall_Znth; [omega|].
            eapply Forall_impl; [|eauto]; simpl; intros; apply repable_buf; omega. }
          { simpl in *; congruence. }
          entailer!.
          rewrite sepcon_comm; apply derives_refl'; f_equal; f_equal.
          unfold last_two_reads in *.
          destruct (find_read _ _); match goal with H : (_, _) = (_, _) |- _ => inv H; auto end.
      + view_shift_intro v0; view_shift_intro l.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_ref _ _)).
        rewrite (sepcon_comm _ (ghost_hist _ _ _)).
        rewrite !sepcon_emp, <- !sepcon_assoc, 6sepcon_assoc.
        apply view_shift_assert with (PP := hist_incl hi l).
        { apply sepcon_derives_prop, hist_ref_incl; auto. }
        intros ?%hist_incl_lt.
        etransitivity; [apply view_shift_sepcon1, hist_add'; auto|].
        view_shift_intro b0'; view_shift_intro b1'; view_shift_intro b2'.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g1i)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh1 _ g1i)).
        erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto.
        view_shift_intros.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1,
          ghost_var_update with (v' := vint b)|].
        erewrite <- ghost_var_share_join by eauto.
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh2 _ g2i)).
        rewrite <- !sepcon_assoc, (sepcon_comm _ (ghost_var gsh1 _ g2i)).
        erewrite <- !sepcon_assoc, ghost_var_share_join' by eauto.
        view_shift_intros.
        rewrite !sepcon_assoc; etransitivity; [apply view_shift_sepcon1,
          ghost_var_update with (v' := vint (if eq_dec (Int.signed (Int.repr v0)) (-1) then b0
          else Znth i lasts 0))|].
        erewrite <- ghost_var_share_join by eauto.
        apply derives_view_shift.
        Exists Tsh (Int.signed (Int.repr v0)); rewrite Int.repr_signed; entailer!.
        { apply Int.signed_range. }
        rewrite <- wand_sepcon_adjoint.
        Exists (length l) b (l ++ [AE (vint v0) (vint b)])
          (vint (if eq_dec (Int.signed (Int.repr v0)) (-1) then b0 else Znth (Zlength t') lasts 0))
          (vint b) b0'; entailer!.
        { discriminate. }
        rewrite sepcon_comm; auto. }
    Intros b' t.
    gather_SEP 0 4 8; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      comm_loc (Znth r lgood false) lsh (Znth r comms Vundef) (Znth r g Vundef) (Znth r g0 Vundef)
        (Znth r g1 Vundef) (Znth r g2 Vundef) bufs (Znth r shs Tsh) gsh2 (Znth r h [] ++
        (if zlt r (i + 1) then [(Znth r (t' ++ [t]) 0%nat, AE (Znth r (h' ++ [vint b']) Vundef) (vint b))] else [])))
      (upto (Z.to_nat N)))).
    { go_lower.
      rewrite <- sepcon_assoc, replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength;
        rewrite !Zlength_map, Zlength_upto; auto.
      intros j ?; destruct (eq_dec j i).
      + subst; rewrite upd_Znth_same by (rewrite Zlength_map, Zlength_upto; auto).
        rewrite Znth_map with (d' := N), Znth_upto by (auto; omega).
        destruct (zlt (Zlength t') (Zlength t' + 1)); [|omega].
        rewrite !app_Znth2 by omega.
        subst hi c gi g0i g1i g2i good sh.
        rewrite Zminus_diag; replace (Zlength t') with (Zlength h'); rewrite Zminus_diag, !Znth_0_cons; auto.
      + rewrite upd_Znth_diff' by (rewrite ?Zlength_map, ?Zlength_upto; auto).
        rewrite !Znth_map with (d' := N), !Znth_upto by (auto; omega).
        if_tac; if_tac; auto; try omega.
        rewrite !app_Znth1; auto; omega. }
    gather_SEP 2 8; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      ghost_var gsh1 (vint (if zlt r (i + 1) then b else b0)) (Znth r g1 Vundef)) (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
        [|rewrite Zlength_map, Zlength_upto; auto].
      erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; simpl; auto;
        try (unfold N in *; auto; omega).
      destruct (zlt i (i + 1)); [subst g1i; fast_cancel | omega].
      apply sepcon_list_derives; rewrite !upd_Znth_Zlength; rewrite !Zlength_map; auto; intros.
      destruct (eq_dec i0 i); [subst; rewrite !upd_Znth_same by (rewrite ?Zlength_map; auto); auto|].
      rewrite !upd_Znth_diff' by (rewrite ?Zlength_map; auto).
      erewrite !Znth_map, !Znth_upto by (auto; rewrite Zlength_upto in *; omega).
      destruct (zlt i0 i), (zlt i0 (i + 1)); auto; omega. }
    gather_SEP 3 8; replace_SEP 0 (fold_right sepcon emp (map (fun r =>
      ghost_var gsh1 (vint (Znth r (map (fun i0 => if eq_dec (Znth i0 (h' ++ [vint b']) Vundef) Empty then b0
        else Znth i0 lasts 0) (upto (Z.to_nat N))) (-1))) (Znth r g2 Vundef)) (upto (Z.to_nat N)))).
    { go_lowerx.
      rewrite (extract_nth_sepcon (map _ (upto (Z.to_nat N))) i);
        [|rewrite Zlength_map, Zlength_upto; auto].
      erewrite Znth_map, Znth_upto; rewrite ?Zlength_upto, ?Z2Nat.id; simpl; auto;
        try (unfold N in *; auto; omega).
      erewrite Znth_map, Znth_upto by (auto; unfold N in *; simpl; omega).
      replace i with (Zlength h'); rewrite app_Znth2, Zminus_diag, Znth_0_cons; [fast_cancel | omega].
      apply sepcon_derives.
      { replace (Zlength h') with i; subst g2i; destruct (eq_dec b' (-1)), (eq_dec (vint b') Empty);
          auto; subst; [contradiction|].
        contradiction n0; apply Empty_inj; auto; apply repable_buf; auto. }
      apply sepcon_list_derives; rewrite !upd_Znth_Zlength; rewrite !Zlength_map;
        try (rewrite !Zlength_upto; simpl; unfold N in *; omega); intros.
      destruct (eq_dec i0 (Zlength h')); [subst; rewrite !upd_Znth_same by (rewrite ?Zlength_map; auto); auto|].
      rewrite !upd_Znth_diff' by (rewrite ?Zlength_map, ?Zlength_upto; unfold N in *; simpl; auto; omega).
      erewrite !Znth_map; rewrite ?Znth_upto; rewrite ?Znth_upto; auto; rewrite Zlength_upto in *; try omega.
      destruct (zlt i0 (Zlength h')).
      + rewrite app_Znth1; auto.
      + rewrite Znth_overflow with (al := h'), Znth_overflow with (al := (h' ++ [vint b'])); auto.
        rewrite Zlength_app, Zlength_cons, Zlength_nil; omega. }
    focus_SEP 7.
    match goal with |- semax _ (PROP () (LOCALx ?Q (SEPx (data_at _ _ ?l last_taken :: ?R)))) _ _ =>
      forward_if (PROP () (LOCALx Q (SEPx (data_at Ews (tarray tint N)
        (upd_Znth i l (vint (if eq_dec (vint b') Empty then b0 else Znth i lasts 0))) last_taken :: R)))) end.
    + forward.
      match goal with H : Int.repr b' = _ |- _ => rewrite Int.neg_repr in H; apply repr_inj_signed in H end; subst;
        auto.
      destruct (eq_dec (- (1)) (-1)); [|absurd (-1 = -1); auto].
      apply drop_tc_environ.
    + forward.
      destruct (eq_dec b' (-1)); [subst; contradiction|].
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
      rewrite !Zlength_app, !Zlength_cons, !Zlength_nil; entailer!.
      rewrite !sepcon_assoc; apply sepcon_derives.
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
        subst good sh; replace (Zlength t') with (Zlength h') in *; eapply upd_write_shares; eauto.
        intro; match goal with H : _ -> _ \/ _ |- _ => destruct H; subst; auto; omega end.
  - Intros t' h'.
    forward.
    forward.
    forward.
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
  eapply semax_pre with (P' := EX b0 : Z, EX h : hist, PROP (0 <= b0 < B; latest_read h b0)
    LOCAL (temp _r (vint r); temp _arg arg; gvar _reading reading; gvar _last_read last_read; 
           gvar _comm comm; gvar _bufs buf)
    SEP (data_at sh1 (tarray (tptr tint) N) reads reading; data_at sh1 (tarray (tptr tint) N) lasts last_read;
         data_at Tsh tint Empty (Znth r reads Vundef); data_at Tsh tint (vint b0) (Znth r lasts Vundef);
         data_at Tsh tint (vint r) (force_val (sem_cast_neutral arg)); malloc_token Tsh (sizeof tint) arg;
         data_at sh1 (tarray (tptr tint) N) comms comm;
         data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
         comm_loc good sh2 c g g0 g1 g2 bufs sh gsh2 h;
         if good then EX v : _, @data_at CompSpecs sh tbuffer (Vint v) (Znth b0 bufs Vundef) else emp;
         ghost_var gsh1 (vint b0) g0)).
  { Exists 1 ([] : hist); entailer!.
    unfold latest_read; auto. }
  eapply semax_loop; [|forward; apply drop_tc_environ].
  Intros b0 h.
  forward.
  subst c; subst; forward_call (r, reading, last_read, comm, reads, lasts, good, comms, bufs,
    sh, sh1, sh2, b0, g, g0, g1, g2, h).
  { repeat (split; auto). }
  Intros x; destruct x as ((b, t), e); simpl in *.
  assert_PROP (Zlength bufs = B) as Hlen by entailer!.
  assert (isptr (Znth (if ((0 <=? e) && (e <? B))%bool then e else b0) bufs Vundef)).
  { apply Forall_Znth; auto; omega. }
  forward.
  forward_call (load_SC_witness (Znth b bufs Vundef)
    (if good then EX v : _, data_at sh tbuffer (Vint v) (Znth b bufs Vundef) else emp)
    (fun _ : Z => comm_inv good (Znth r comms Vundef) bufs sh g g0 g1 g2 gsh2) [0]
    (fun v' => if good then data_at sh tbuffer (vint v') (Znth b bufs Vundef) else emp)).
  { entailer!. }
  { simpl; unfold comm_loc; cancel. }
  { apply wand_view_shifts2.
    apply derives_view_shift.
    simpl; unfold comm_inv.
    Exists sh; Intros b'; destruct good.
    - Intros v; Exists (Int.signed v).
      unfold_data_at 2%nat.
      rewrite field_at_data_at'; simpl; rewrite Int.repr_signed, sepcon_andp_prop'; apply andp_right.
      { entailer!.
        apply Int.signed_range; auto. }
      entailer!.
      rewrite <- wand_sepcon_adjoint.
      Exists b' x; entailer!.
      unfold_data_at 2%nat.
      rewrite field_at_data_at'; simpl; entailer!; auto.
    - rewrite !sepcon_emp, <- !sepcon_assoc, sepcon_comm.
      rewrite extract_nth_sepcon with (i := b) by (rewrite Zlength_map; omega).
      erewrite Znth_map by omega; Intro v.
      Exists (Int.signed v); rewrite Int.repr_signed.
      rewrite !sepcon_assoc; apply sepcon_derives.
      { unfold_data_at 1%nat.
        rewrite field_at_data_at'; entailer!; eauto.
        apply Int.signed_range; auto. }
      rewrite <- wand_sepcon_adjoint.
      rewrite <- !exp_sepcon1; cancel.
      Exists b' v; entailer!.
      unfold_data_at 2%nat.
      rewrite field_at_data_at'; simpl; entailer!; auto. }
  Intros d.
  forward_call (r, reading, reads, sh1).
  go_lower.
  Exists b (h ++ [(t, AE (vint e) Empty)]); unfold comm_loc; entailer!.
  if_tac; auto; Exists (Int.repr d); auto.
Qed.

Lemma sepcon_filter_combine : forall {A} P (l : list A) l', Zlength l' = Zlength l ->
  fold_right sepcon emp (map P l) =
  fold_right sepcon emp (map P (map snd (filter fst (combine l' l)))) *
  fold_right sepcon emp (map P (map snd (filter (fun '(b, _) => negb b) (combine l' l)))).
Proof.
  induction l; intros.
  { rewrite combine_nil; simpl; rewrite sepcon_emp; auto. }
  destruct l'; [symmetry in H; apply Zlength_nil_inv in H; discriminate|].
  simpl.
  rewrite !Zlength_cons in *; rewrite (IHl l') by omega.
  destruct b; simpl; apply mpred_ext; cancel.
Qed.

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

Lemma data_at_shares_join' : forall {cs} sh v p shs sh1
  (Hsplit : sepalg_list.list_join sh1 shs sh), readable_share sh1 ->
  @data_at cs sh1 tint (Vint v) p *
    fold_right_sepcon (map (fun sh => EX v : _, data_at sh tint (Vint v) p) shs) =
  data_at sh tint (Vint v) p.
Proof.
  induction shs; intros; simpl.
  - inv Hsplit.
    rewrite sepcon_emp; auto.
  - inv Hsplit.
    erewrite <- IHshs; eauto.
    apply mpred_ext; cancel; rewrite <- (data_at_share_join sh1 a w1) by auto.
    + Intro v'; apply data_at_value_cohere; auto.
    + Exists v; auto.
    + eapply readable_share_join; eauto.
Qed.

Lemma map_snd_filter_fst : forall {A B C} f (g : B -> C) (l : list (A * B)),
  filter (fun '(a, _) => f a) (map (fun '(a, b) => (a, g b)) l) =
  map (fun '(a, b) => (a, g b)) (filter (fun '(a, _) => f a) l).
Proof.
  induction l; auto; simpl.
  destruct a.
  rewrite IHl; if_tac; auto.
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
   gvar _last_taken last_taken; gvar _comm comm; gvar _bufs buf)
   SEP (data_at Ews tint Empty writing; data_at Ews tint (vint b0) last_given;
   data_at Ews (tarray tint N) (map (fun x => vint x) lasts) last_taken;
   data_at sh1 (tarray (tptr tint) N) comms comm; data_at sh1 (tarray (tptr tbuffer) B) bufs buf;
   fold_right sepcon emp (map (fun r0 => comm_loc (Znth r0 lgood false) lsh (Znth r0 comms Vundef)
     (Znth r0 g Vundef) (Znth r0 g0 Vundef) (Znth r0 g1 Vundef) (Znth r0 g2 Vundef) bufs
     (Znth r0 shs Tsh) gsh2 (Znth r0 h [])) (upto (Z.to_nat N)));
   fold_right sepcon emp (map (fun r0 => ghost_var gsh1 (vint b0) (Znth r0 g1 Vundef) *
     ghost_var gsh1 (vint (Znth r0 lasts (-1))) (Znth r0 g2 Vundef)) (upto (Z.to_nat N)));
   fold_right sepcon emp (map (fun i => EX sh : share, !! (if eq_dec i b0 then sh = sh0
     else sepalg_list.list_join sh0 (make_shares shs (combine lgood lasts) i) sh) &&
     (EX v : _, @data_at CompSpecs sh tbuffer (Vint v) (Znth i bufs Vundef))) (upto (Z.to_nat B))))).
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
      replace (make_shares _ _ _) with
        (if eq_dec a 1 then [] else map snd (filter fst (combine lgood shs))).
      destruct (eq_dec a 1), (eq_dec 1 a); auto; try omega; apply mpred_ext; Intros sh; Exists sh;
        entailer!.
      + constructor.
      + match goal with H : sepalg_list.list_join sh0 [] sh |- _ => inv H; auto end.
      + eapply list_join_eq; eauto.
      + if_tac.
        * subst; destruct lgood; auto; simpl.
          rewrite orb_true_r; destruct lgood; auto; simpl.
          rewrite orb_true_r; destruct lgood; auto; simpl.
          rewrite orb_true_r, combine_nil; auto.
        * symmetry; apply make_shares_out; auto; [|unfold share in *; omega].
          intros [|[|[|]]]; auto. }
  eapply semax_loop; [|forward; apply drop_tc_environ].
  Intros v b0 lasts h.
  rewrite sepcon_map; Intros.
  forward.
  forward_call (writing, last_given, last_taken, b0, lasts).
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
  rewrite make_shares_out in *; auto; unfold share in *; try omega.
  assert (sh = shg) by (eapply list_join_eq; eauto); subst.
  assert_PROP (Zlength bufs = B) by entailer!.
  forward_call (store_SC_witness (Znth b bufs Vundef) (Int.signed (Int.repr v))
    (data_at shg tbuffer (Vint v0) (Znth b bufs Vundef))
    (fun r => comm_inv (Znth r lgood false) (Znth r comms Vundef) bufs (Znth r shs Tsh)
      (Znth r g Vundef) (Znth r g0 Vundef) (Znth r g1 Vundef) (Znth r g2 Vundef) gsh2)
    (map snd (filter (fun '(b, _) => negb b) (combine lgood (upto (Z.to_nat N)))))
    (data_at shg tbuffer (vint v) (Znth b bufs Vundef))).
  { entailer!.
    rewrite Int.repr_signed; auto. }
  { unfold comm_loc; rewrite sepcon_map.
    rewrite sepcon_filter_combine with (l' := lgood) by auto; cancel. }
  { split; [apply Int.signed_range; auto|].
    apply wand_view_shifts.
    apply derives_view_shift.
    Exists Tsh; rewrite Int.repr_signed, !prop_true_andp by auto.
    unfold_data_at 1%nat.
    rewrite field_at_data_at'; simpl; Intros.
    erewrite wand_sepcon_map with
      (P := fun r => EX v : _, data_at (Znth r shs Tsh) tint (Vint v) (Znth b bufs Vundef)) at 1.
    rewrite data_at__eq.
    assert (Zlength lgood = Zlength shs) by omega.
    assert (readable_share shg) by (eapply readable_share_list_join; eauto).
    assert (map (fun sh => EX v1 : _, data_at sh tint (Vint v1) (Znth b bufs Vundef))
     (map snd (filter (fun '(b1, _) => negb b1) (combine lgood shs))) =
     map (fun r => EX v1 : _, data_at (Znth r shs Tsh) tint (Vint v1) (Znth b bufs Vundef))
     (map snd (filter (fun '(b1, _) => negb b1) (combine lgood (upto 3))))) as Heq.
    { setoid_rewrite (list_Znth_eq Tsh shs) at 1.
      rewrite <- ZtoNat_Zlength; unfold share in *; replace (Zlength shs) with N; unfold N; simpl.
      rewrite combine_map_snd, map_snd_filter_fst, !map_map.
      apply map_ext; intros (?, ?); auto. }
    rewrite sepcon_comm, <- sepcon_assoc; apply sepcon_derives.
    - apply derives_trans with (Q := data_at Tsh tint (Vint v0) (Znth b bufs Vundef)); [|cancel].
      erewrite <- data_at_shares_join' with (sh := Tsh) by (try eapply list_join_minus; eauto).
      unfold share; rewrite <- data_at_offset_zero, Heq; auto.
    - erewrite <- data_at_shares_join' with (sh := Tsh) by (try eapply list_join_minus; eauto).
      unfold_data_at 4%nat.
      rewrite field_at_data_at'; simpl.
      rewrite <- data_at_offset_zero, prop_true_andp by auto.
      unfold share; rewrite Heq, sepcon_comm; apply wand_frame.
    - intro; rewrite in_map_iff.
      intros ((good, ?) & ? & Hi); rewrite filter_In in Hi.
      destruct Hi as (Hi & ?); simpl in *; subst; destruct good; try discriminate.
      eapply In_Znth in Hi.
      destruct Hi as (? & Hrange & Hi).
      assert (Zlength lgood = Zlength (upto 3)) by auto.
      rewrite Zlength_combine, Z.min_r, Zlength_upto in Hrange by omega.
      rewrite Znth_combine with (a := false)(b1 := 3) in Hi by auto; inversion Hi as [Hbad].
      rewrite Znth_upto in * by omega; subst.
      rewrite !Hbad.
      unfold comm_inv.
      rewrite <- exp_sepcon1.
      rewrite sepcon_comm, (sepcon_comm _ (fold_right _ _ _)).
      rewrite extract_nth_sepcon with (i := b) by (rewrite Zlength_map; omega).
      erewrite Znth_map by omega.
      rewrite 2sepcon_assoc; f_equal; [|reflexivity].
      f_equal; extensionality.
      unfold_data_at 1%nat.
      rewrite field_at_data_at'; simpl.
      rewrite <- data_at_offset_zero, prop_true_andp by eauto; auto. }
  forward_call (writing, last_given, last_taken, comm, comms, bufs, lgood, b, b0, lasts,
    sh1, lsh, shs, g, g0, g1, g2, h, sh0).
  { unfold comm_loc; rewrite !sepcon_map; cancel.
    rewrite sepcon_filter_combine with (l := upto (Z.to_nat N))(l' := lgood) by auto; cancel.
    rewrite sepcon_assoc, (sepcon_comm (data_at sh1 _ _ _)), <- sepcon_assoc.
    apply sepcon_derives; [|cancel_frame].
    rewrite replace_nth_sepcon; apply sepcon_list_derives; rewrite upd_Znth_Zlength; auto.
    rewrite Zlength_map; intros.
    destruct (eq_dec i b); [|rewrite upd_Znth_diff'; auto].
    subst; rewrite upd_Znth_same by auto.
    erewrite Znth_map, Znth_upto by (auto; simpl; unfold B, N in *; omega).
    if_tac; [contradiction|].
    rewrite make_shares_out by (auto; omega).
    Exists shg (Int.repr v); entailer!. }
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
  name comm _comm.
  name reading _reading.
  name last_read _last_read.
  name last_taken _last_taken.
  name writing _writing.
  name last_given _last_given.
  start_function.
  exploit (split_shares (Z.to_nat N) Tsh); auto; intros (sh0 & shs & ? & ? & ? & Hshs).
  rewrite Z2Nat.id in H by (unfold N; omega).
  (* decide here which are good *)
  destruct (eq_dec shs nil).
  { subst; unfold N in *; rewrite Zlength_nil in *; omega. }
  destruct (exists_last n) as (shs' & sh2 & ?); subst.
  destruct (sepalg_list.list_join_unapp Hshs) as (shg & ? & ?).
  set (shs := shs' ++ [sh2]) in *.
  assert (shs' = map snd (filter fst (combine [true; true; false] shs))) as Hshg.
  { simpl.
    destruct shs eqn: Hshs'; [contradiction | simpl].
    unfold N in *; rewrite Zlength_cons in *; destruct l; [rewrite Zlength_nil in *; omega | simpl].
    rewrite Zlength_cons in *; destruct l; [rewrite Zlength_nil in *; omega | simpl].
    rewrite Zlength_cons in *; destruct l; [|rewrite Zlength_cons in *; pose proof (Zlength_nonneg l); omega].
    subst shs.
    destruct shs'; [discriminate | inv Hshs'].
    destruct shs'; [discriminate | match goal with H : _ = _ |- _ => inv H end].
    destruct shs'; match goal with H : _ ++ _ = _ |- _ => inv H; auto end.
    destruct shs'; discriminate. }
  rewrite Hshg in *.
  forward_call ([true; true; false], comm, buf, reading, last_read, sh0, shs, shg).
  { unfold B, N, tbuffer, _buffer; simpl; cancel. }
  Intros x; destruct x as (((((((comms, bufs), reads), lasts), g), g0), g1), g2); simpl fst in *; simpl snd in *.
  assert_PROP (Zlength comms = N) by entailer!.
  get_global_function'' _writer; Intros.
  apply extract_exists_pre; intros writer_.
  exploit (split_shares (Z.to_nat N) Ews); auto; intros (sh1 & shs1 & ? & ? & ? & ?).
  assert_PROP (Zlength bufs = B) by entailer!.
  forward_spawn (val * val * val * val * val * val * list val * list val * list val *
                 share * share * share * list share * list val * list val * list val * list val)%type
    (writer_, vint 0, fun x : (val * val * val * val * val * val * list val * list val * list val * share * share *
      share * list share * list val * list val * list val * list val) =>
      let '(writing, last_given, last_taken, lock, comm, buf, locks, comms, bufs, sh1, lsh, sh0, shs,
            g, g0, g1, g2) := x in
      [(_writing, writing); (_last_given, last_given); (_last_taken, last_taken); (_comm, comm); (_bufs, buf)],
    (writing, last_given, last_taken, comm, buf, comms, bufs, sh1, gsh1, sh0, shs,
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
