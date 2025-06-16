Require Import VST.concurrency.conclib.
Require Import VST.atomics.SC_atomics.
Require Import VST.floyd.library.
Require Import mailbox.verif_atomic_exchange.
Require Import iris_ora.algebra.excl_auth.
Require Import VST.zlist.sublist.
Require Import mailbox.mailbox.

(* standard VST prelude *)
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_atom_int := Tstruct _atom_int noattr.

Open Scope Z.

Definition Ish := Share.comp Ews.

Lemma Ews_Ish_join : sepalg.join Ews Ish Tsh.
Proof.
  apply comp_join_top.
Qed.

Lemma Ish_not_bot : Ish <> Share.bot.
Proof.
  intro.
  generalize Ews_Ish_join; rewrite H.
  intro X; eapply sepalg.join_eq in X; [|apply join_bot_eq].
  generalize juicy_mem.perm_of_Ews; rewrite X.
  unfold juicy_mem.perm_of_sh.
  rewrite -> if_true by auto.
  rewrite -> if_true by auto; discriminate.
Qed.
#[export] Hint Resolve Ish_not_bot : core.

Section mpred.

Context `{!VSTGS unit Σ, AEGS0 : !AEGS t_atom_int, !inG Σ (excl_authR (leibnizO val))}.

Definition make_atomic_spec := DECLARE _make_atomic make_atomic_spec.
Definition atomic_exchange_spec := DECLARE _atom_exchange SC_atomics.atomic_exchange_spec.
Definition spawn_spec := DECLARE _spawn spawn_spec.

(* up *)
Lemma list_insert_upd : forall {A} i (a : A) l, 0 <= i < Zlength l ->
  <[Z.to_nat i := a]>l = upd_Znth i l a.
Proof.
  intros; generalize dependent i; induction l; simpl; intros.
  - rewrite Zlength_nil in H; lia.
  - rewrite Zlength_cons in H.
    destruct (Z.to_nat i) eqn: Hi; simpl.
    + assert (i = 0) as -> by lia.
      rewrite upd_Znth0 //.
    + rewrite upd_Znth_cons; last lia.
      rewrite -IHl; last lia.
      replace n with (Z.to_nat (i - 1)) by lia; done.
Qed.

(* utility function specs *)
Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:type, gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Int.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] ∃ p:_,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; malloc_token Ews t p ∗ data_at_ Ews t p).

Definition memset_spec :=
 DECLARE _memset
  WITH sh : share, t : type, p : val, c : Z, n : Z
  PRE [ tptr tvoid, tint, size_t ]
   PROP (writable_share sh; sizeof t = (4 * n)%Z; align_compatible tint p)
   PARAMS (p; vint c; Vptrofs (Ptrofs.repr (4 * n)%Z)) GLOBALS ()
   SEP (data_at_ sh t p)
  POST [ tptr tvoid ]
   PROP ()
   RETURN (p)
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

Definition ghost_auth (v : val) (g : gname) : mpred := own g (●E v : excl_authR (leibnizO val)).
Definition ghost_frag (v : val) (g : gname) : mpred := own g (◯E v : excl_authR (leibnizO val)).

Lemma ghost_var_update : forall g v1 v2 v', ghost_auth v1 g -∗ ghost_frag v2 g ==∗
  ⌜v1 = v2⌝ ∧ (ghost_auth v' g ∗ ghost_frag v' g).
Proof.
  intros; iIntros "auth frag".
  iDestruct (own_valid_2 with "auth frag") as %->%excl_auth_agree_L; rewrite bi.pure_True // bi.True_and.
  rewrite /ghost_auth /ghost_frag; iCombine "auth frag" as "H"; rewrite -!own_op.
  iApply (own_update with "H").
  apply @excl_auth_update.
Qed.

(* This is the invariant for the location buffers comm[N]. *)
(* The ghost variables are the last value read, the last value written, and the last value read before
   the last write (i.e., last_taken). The first is updated by the reader, the rest by the writer. *)
Definition comm_R bufs sh g0 g1 g2 h v := ∃ b : Z, ∃ b1 : Z, ∃ b2 : Z,
  ⌜v = vint b /\ -1 <= b < B /\
     Forall (fun a => match a with AE v1 v2 =>
       exists r w, v1 = vint r /\ v2 = vint w /\ -1 <= r < B /\ -1 <= w < B end) h /\
     last_two_reads (rev h) = (vint b1, vint b2) /\ repable_signed b1 /\ repable_signed b2⌝ ∧
  ghost_auth (vint b1) g0 ∗ ghost_auth (last_write (rev h)) g1 ∗ ghost_auth (prev_taken (rev h)) g2 ∗
  if eq_dec b (-1) then ∃ v : Z, data_at sh tbuffer (vint v) (Znth b2 bufs)
  else ∃ v : Z, data_at sh tbuffer (vint v) (Znth b bufs).

#[export] Instance data_at_buffer_timeless sh v p : Timeless (data_at sh tbuffer v p).
Proof.
  apply bi.and_timeless; first apply _.
  rewrite /at_offset data_at_rec_eq /withspacer /=.
  apply _.
Qed.

#[export] Instance comm_R_timeless bufs sh g0 g1 g2 h v : Timeless (comm_R bufs sh g0 g1 g2 h v).
Proof.
  rewrite /comm_R.
  repeat (apply bi.exist_timeless; intros).
  apply bi.and_timeless; first apply _.
  repeat (apply bi.sep_timeless; first apply _).
  if_tac; apply _.
Qed.

Definition comm_loc lsh comm g g0 g1 g2 bufs sh :=
  AE_loc lsh comm g (vint 0) (comm_R bufs sh g0 g1 g2).

Lemma comm_loc_isptr : forall lsh comm g g0 g1 g2 bufs sh h,
  comm_loc lsh comm g g0 g1 g2 bufs sh h ⊢ ⌜isptr comm⌝.
Proof.
  intros; apply AE_loc_isptr.
Qed.

(* messaging system function specs *)
Definition initialize_channels_spec :=
 DECLARE _initialize_channels
  WITH sh1 : share, shs : list share, gv: globals
  PRE [ ]
   PROP (Zlength shs = N; sepalg_list.list_join sh1 shs Ews)
   PARAMS () GLOBALS (gv)
   SEP (data_at_ Ews (tarray (tptr t_atom_int) N) (gv _comm);
        data_at_ Ews (tarray (tptr tbuffer) B) (gv _bufs);
        data_at_ Ews (tarray (tptr tint) N) (gv _reading); data_at_ Ews (tarray (tptr tint) N) (gv _last_read);
        mem_mgr gv)
  POST [ tvoid ]
   ∃ comms : list val, ∃ bufs : list val, ∃ reads : list val, ∃ lasts : list val,
     ∃ g : list gname, ∃ g0 : list gname, ∃ g1 : list gname, ∃ g2 : list gname,
   PROP ((*Forall isptr comms;*) Zlength g = N; Zlength g0 = N; Zlength g1 = N; Zlength g2 = N)
   RETURN ()
   SEP (data_at Ews (tarray (tptr t_atom_int) N) comms (gv _comm);
        data_at Ews (tarray (tptr tbuffer) B) bufs (gv _bufs);
        data_at Ews (tarray (tptr tint) N) reads (gv _reading);
        data_at Ews (tarray (tptr tint) N) lasts (gv _last_read);
        [∗] (map (fun r =>
          comm_loc 1 (Znth r comms) (Znth r g) (Znth r g0)
            (Znth r g1) (Znth r g2) bufs (Znth r shs) ∅) (upto (Z.to_nat N)));
        [∗] (map (ghost_frag (vint 1)) g0);
        [∗] (map (ghost_frag (vint 0)) g1);
        [∗] (map (ghost_frag (vint 1)) g2);
        [∗] (map (malloc_token Ews tbuffer) bufs);
        [∗] (map (malloc_token Ews tint) reads);
        [∗] (map (malloc_token Ews tint) lasts);
        data_at sh1 tbuffer (vint 0) (Znth 0 bufs);
        [∗] (map (data_at Ews tbuffer (vint 0)) (sublist 1 (Zlength bufs) bufs));
        [∗] (map (data_at_ Ews tint) reads);
        [∗] (map (data_at_ Ews tint) lasts);
        mem_mgr gv).
(* All the communication channels are now inside atomic invariants. Buffer 0 also starts distributed among the channels. *)

Definition initialize_reader_spec :=
 DECLARE _initialize_reader
  WITH r : Z, reads : list val, lasts : list val, sh : share, gv: globals
  PRE [ tint ]
   PROP (readable_share sh)
   PARAMS (vint r) GLOBALS (gv)
   SEP (data_at sh (tarray (tptr tint) N) reads (gv _reading); data_at sh (tarray (tptr tint) N) lasts (gv _last_read);
        data_at_ Ews tint (Znth r reads); data_at_ Ews tint (Znth r lasts))
  POST [ tvoid ]
   PROP ()
   RETURN ()
   SEP (data_at sh (tarray (tptr tint) N) reads (gv _reading); data_at sh (tarray (tptr tint) N) lasts (gv _last_read);
        data_at Ews tint Empty (Znth r reads); data_at Ews tint (vint 1) (Znth r lasts)).

Definition latest_read (h : hist) v :=
  (* initial condition *)
  ((forall t r w, h !! t = Excl' (AE r w) -> w = Empty -> r = Empty) /\ v = vint 1) \/
  v <> Empty /\ exists n, h !! n = Excl' (AE v Empty) /\
  forall t r w, h !! t = Excl' (AE r w) -> w = Empty -> r <> Empty -> (t <= n)%nat.

(* last_read retains the last buffer read, while reading is reset to Empty. *)
Definition start_read_spec :=
 DECLARE _start_read
  WITH r : Z, reads : list val, lasts : list val,
    comms : list val, bufs : list val, sh : share, sh1 : share, sh2 : Qp, b0 : Z,
    g : gname, g0 : gname, g1 : gname, g2 : gname, h : hist, gv: globals
  PRE [ tint ]
   PROP (0 <= b0 < B; readable_share sh; readable_share sh1; latest_read h (vint b0))
   PARAMS (vint r) GLOBALS (gv)
   SEP (data_at sh1 (tarray (tptr tint) N) reads (gv _reading); data_at sh1 (tarray (tptr tint) N) lasts (gv _last_read);
        data_at sh1 (tarray (tptr t_atom_int) N) comms (gv _comm);
        data_at_ Ews tint (Znth r reads); data_at Ews tint (vint b0) (Znth r lasts);
        comm_loc sh2 (Znth r comms) g g0 g1 g2 bufs sh h;
        ∃ v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs);
        ghost_frag (vint b0) g0)
  POST [ tint ]
   ∃ b : Z, ∃ t : nat, ∃ v0 : val, ∃ v : Z,
   PROP (0 <= b < B; if eq_dec v0 Empty then b = b0 else v0 = vint b;
         latest_read (<[t := Excl (AE v0 Empty)]>h) (vint b))
   RETURN (vint b)
   SEP (data_at sh1 (tarray (tptr tint) N) reads (gv _reading); data_at sh1 (tarray (tptr tint) N) lasts (gv _last_read);
        data_at sh1 (tarray (tptr t_atom_int) N) comms (gv _comm);
        data_at Ews tint (vint b) (Znth r reads); data_at Ews tint (vint b) (Znth r lasts);
        comm_loc sh2 (Znth r comms) g g0 g1 g2 bufs sh (<[t := Excl (AE v0 Empty)]>h);
        data_at sh tbuffer (vint v) (Znth b bufs);
        ghost_frag (vint b) g0).
(* And bufs[b] is the most recent buffer completed by finish_write. *)


Definition finish_read_spec :=
 DECLARE _finish_read
  WITH r : Z, reads : list val, sh : share, gv: globals
  PRE [ tint ]
   PROP (readable_share sh)
   PARAMS (vint r) GLOBALS (gv)
   SEP (data_at sh (tarray (tptr tint) N) reads (gv _reading); data_at_ Ews tint (Znth r reads))
  POST [ tvoid ]
   PROP ()
   RETURN ()
   SEP (data_at sh (tarray (tptr tint) N) reads (gv _reading); data_at Ews tint Empty (Znth r reads)).

Definition initialize_writer_spec :=
 DECLARE _initialize_writer
  WITH gv: globals
  PRE [ ]
   PROP ()
   PARAMS () GLOBALS (gv)
   SEP (data_at_ Ews tint (gv _writing); data_at_ Ews tint (gv _last_given);
        data_at_ Ews (tarray tint N) (gv _last_taken))
  POST [ tvoid ]
   PROP ()
   RETURN ()
   SEP (data_at Ews tint Empty (gv _writing); data_at Ews tint (vint 0) (gv _last_given);
        data_at Ews (tarray tint N) (repeat (vint 1) (Z.to_nat N)) (gv _last_taken)).

Definition start_write_spec :=
 DECLARE _start_write
  WITH b0 : Z, lasts : list Z, gv: globals
  PRE [ ]
   PROP (0 <= b0 < B; Forall (fun x => 0 <= x < B) lasts)
   PARAMS () GLOBALS (gv)
   SEP (data_at_ Ews tint (gv _writing); data_at Ews tint (vint b0) (gv _last_given);
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) (gv _last_taken))
  POST [ tint ]
   ∃ b : Z,
   PROP (0 <= b < B; b <> b0; ~In b lasts)
   RETURN (vint b)
   SEP (data_at Ews tint (vint b) (gv _writing); data_at Ews tint (vint b0) (gv _last_given);
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) (gv _last_taken)).
(* And b is not in use by any reader. This follows from the property on lasts. *)

(* make_shares returns the elements of shs for which the corresponding element of lasts is not i. *)
Fixpoint make_shares shs (lasts : list Z) i : list share :=
  match lasts with
  | [] => []
  | b :: rest => if eq_dec b i then make_shares (tl shs) rest i
                 else hd Share.bot shs :: make_shares (tl shs) rest i
  end.

Definition finish_write_spec :=
 DECLARE _finish_write
  WITH comms : list val, bufs : list val, b : Z, b0 : Z, lasts : list Z,
    sh1 : share, lsh : Qp, shs : list share, g : list gname, g0 : list gname, g1 : list gname, g2 : list gname,
    h : list hist, sh0 : share, gv: globals
  PRE [ ]
   PROP (0 <= b < B; 0 <= b0 < B; Forall (fun x => 0 <= x < B) lasts; Zlength h = N; Zlength shs = N;
         readable_share sh1; Forall readable_share shs;
         sepalg_list.list_join sh0 shs Ews; (*Forall isptr comms;*) b <> b0; ~In b lasts; ~In b0 lasts)
   PARAMS () GLOBALS (gv)
   SEP (data_at Ews tint (vint b) (gv _writing); data_at Ews tint (vint b0) (gv _last_given);
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts) (gv _last_taken);
        data_at sh1 (tarray (tptr t_atom_int) N) comms (gv _comm);
        [∗] (map (fun r =>
          comm_loc lsh (Znth r comms) (Znth r g) (Znth r g0)
            (Znth r g1) (Znth r g2) bufs (Znth r shs) (Znth r h)) (upto (Z.to_nat N)));
        [∗] (map (fun r => ghost_frag (vint b0) (Znth r g1) ∗
          ghost_frag (vint (@Znth Z (-1) r lasts)) (Znth r g2)) (upto (Z.to_nat N)));
        [∗] (map (fun i => ∃ sh : share,
          ⌜if eq_dec i b0 then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts i) sh⌝ ∧
          ∃ v : Z, data_at sh tbuffer (vint v) (Znth i bufs)) (upto (Z.to_nat B))))
  POST [ tvoid ]
   ∃ lasts' : list Z, ∃ h' : list hist,
   PROP (Forall (fun x => 0 <= x < B) lasts';
         Forall2 (fun h1 h2 => exists t v, h2 = <[t := Excl (AE v (vint b))]>h1) h h';
         ~In b lasts')
   RETURN ()
   SEP (data_at Ews tint Empty (gv _writing); data_at Ews tint (vint b) (gv _last_given);
        data_at Ews (tarray tint N) (map (fun x => vint x) lasts') (gv _last_taken);
        data_at sh1 (tarray (tptr t_atom_int) N) comms (gv _comm);
        [∗] (map (fun r =>
          comm_loc lsh (Znth r comms) (Znth r g) (Znth r g0)
            (Znth r g1) (Znth r g2) bufs (Znth r shs) (Znth r h')) (upto (Z.to_nat N)));
        [∗] (map (fun r => ghost_frag (vint b) (Znth r g1) ∗
          ghost_frag (vint (@Znth Z (-1) r lasts')) (Znth r g2)) (upto (Z.to_nat N)));
        [∗] (map (fun i => ∃ sh : share,
          ⌜if eq_dec i b then sh = sh0 else sepalg_list.list_join sh0 (make_shares shs lasts' i) sh⌝ ∧
          ∃ v : Z, data_at sh tbuffer (vint v) (Znth i bufs)) (upto (Z.to_nat B)))).

(* client function specs *)
Definition reader_spec :=
 DECLARE _reader
  WITH arg : val, x : Z * list val * list val * list val * list val *
                      share * Qp * share * gname * gname * gname * gname * globals
  PRE [ tptr tvoid ]
   let '(r, reads, lasts, comms, bufs, sh1, sh2, sh, g, g0, g1, g2, gv) := x in
   PROP (readable_share sh; readable_share sh1)
   PARAMS (arg) GLOBALS (gv)
   SEP (data_at Ews tint (vint r) arg; malloc_token Ews tint arg;
        data_at sh1 (tarray (tptr tint) N) reads (gv _reading); data_at sh1 (tarray (tptr tint) N) lasts (gv _last_read);
        data_at sh1 (tarray (tptr t_atom_int) N) comms (gv _comm);
        data_at_ Ews tint (Znth r reads); data_at_ Ews tint (Znth r lasts);
        data_at sh1 (tarray (tptr tbuffer) B) bufs (gv _bufs);
        comm_loc sh2 (Znth r comms) g g0 g1 g2 bufs sh ∅;
        ∃ v : Z, data_at sh tbuffer (vint v) (Znth 1 bufs);
        ghost_frag (vint 1) g0)
  POST [ tint ] PROP () RETURN (Vint Int.zero) SEP ().

Definition writer_spec :=
 DECLARE _writer
  WITH arg : val, x : list val * list val * share * Qp *
                      share * list share * list gname * list gname * list gname * list gname * globals
  PRE [ tptr tvoid ]
   let '(comms, bufs, sh1, lsh, sh0, shs, g, g0, g1, g2, gv) := x in
   PROP (Zlength shs = N; readable_share sh1; Forall readable_share shs;
         sepalg_list.list_join sh0 shs Ews; Zlength g1 = N; Zlength g2 = N(*; Forall isptr comms*))
   PARAMS (arg) GLOBALS (gv)
   SEP (data_at_ Ews tint (gv _writing); data_at_ Ews tint (gv _last_given); data_at_ Ews (tarray tint N) (gv _last_taken);
        data_at sh1 (tarray (tptr t_atom_int) N) comms (gv _comm);
        data_at sh1 (tarray (tptr tbuffer) B) bufs (gv _bufs);
        [∗] (map (fun r =>
          comm_loc lsh (Znth r comms) (Znth r g) (Znth r g0)
            (Znth r g1) (Znth r g2) bufs (Znth r shs) ∅) (upto (Z.to_nat N)));
        [∗] (map (ghost_frag (vint 0)) g1);
        [∗] (map (ghost_frag (vint 1)) g2);
        [∗] (map (fun i => ∃ sh : share,
          ⌜if eq_dec i 0 then sh = sh0 else if eq_dec i 1 then sh = sh0 else sh = Ews⌝ ∧
          ∃ v : Z, data_at sh tbuffer (vint v) (Znth i bufs)) (upto (Z.to_nat B))))
  POST [ tint ] PROP () RETURN (Vint Int.zero) SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

(* Create the environment containing all function specs. *)
Definition Gprog : funspecs := ltac:(with_library prog [spawn_spec;
  surely_malloc_spec; memset_spec; make_atomic_spec; atomic_exchange_spec; initialize_channels_spec; initialize_reader_spec;
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
  split; [transitivity (-1) | transitivity B]; unfold B, N in *; try computable; auto; lia.
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
  right; eapply find_read_incl; rewrite -> Hfind; auto.
Qed.

Lemma latest_read_Empty : forall h n v, newer h n ->
  latest_read (<[n := Excl (AE Empty Empty)]>h) v <-> latest_read h v.
Proof.
  unfold latest_read; split; intros [(Hnone & ?) | (? & m & Hin & Hlatest)]; subst.
  - left; split; auto; intros.
    eapply (Hnone t); eauto.
    rewrite lookup_insert_ne //.
    intros ->; erewrite newer_out in H0 by eauto; discriminate.
  - right; split; auto; exists m.
    destruct (eq_dec m n); [subst; rewrite lookup_insert in Hin; congruence | rewrite lookup_insert_ne // in Hin].
    split; auto; intros; eapply Hlatest; eauto.
    rewrite lookup_insert_ne //.
    intros ->; erewrite newer_out in H1 by eauto; discriminate.
  - left; split; auto.
    intros ???.
    destruct (eq_dec n t); [subst; rewrite lookup_insert | rewrite lookup_insert_ne //]; eauto.
    inversion 1; auto.
  - right; split; auto; exists m.
    apply newer_out in H.
    split; [destruct (eq_dec m n); [subst; rewrite lookup_insert; congruence | rewrite lookup_insert_ne //]|].
    intros ??.
    destruct (eq_dec n t); [subst; rewrite lookup_insert | rewrite lookup_insert_ne //]; eauto.
    intro; inversion 1; contradiction.
Qed.

Lemma latest_read_new : forall h n v, newer h n -> v <> Empty ->
  latest_read (<[n := Excl (AE v Empty)]>h) v.
Proof.
  unfold latest_read; intros.
  right; split; auto; exists n.
  rewrite lookup_insert; split; auto.
  intros ???; destruct (eq_dec n t); [subst; auto | rewrite lookup_insert_ne //].
  intro Ht; specialize (H t); rewrite Ht in H; lapply H; [lia | discriminate].
Qed.

Lemma make_shares_out : forall b lasts shs
  (Hb : ~In b lasts) (Hlen : Zlength lasts = Zlength shs), make_shares shs lasts b = shs.
Proof.
  induction lasts; auto; simpl; intros.
  { rewrite -> Zlength_nil in *; destruct shs; auto; rewrite -> Zlength_cons, Zlength_correct in *; lia. }
  destruct (eq_dec a b); [contradiction Hb; auto|].
  destruct shs; rewrite -> !Zlength_cons in *; [rewrite -> Zlength_nil, Zlength_correct in *; lia|].
  simpl; rewrite IHlasts; auto; lia.
Qed.

End mpred.

#[export] Hint Resolve comm_loc_isptr : saturate_locals.
