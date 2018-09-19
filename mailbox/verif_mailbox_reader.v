Require Import mailbox.verif_atomic_exchange.
Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.

Set Bullet Behavior "Strict Subproofs".

Ltac entailer_for_load_tac ::= unfold tc_efield; go_lower; entailer'.
Ltac entailer_for_store_tac ::= unfold tc_efield; go_lower; entailer'.

Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  start_function.
  rewrite (data_at_isptr _ tint); Intros.
  replace_SEP 0 (data_at Ews tint (vint r) (force_val (sem_cast_pointer arg))).
  { rewrite sem_cast_neutral_ptr; auto; go_lowerx; cancel. }
  forward.
  forward_call (r, reads, lasts, sh1, gv).
(*  eapply semax_seq'; [|apply semax_ff]. *)
  set (c := Znth r comms).
  set (l := Znth r locks).
  forward_loop (EX b0 : Z, EX h : hist, PROP (0 <= b0 < B; latest_read h (vint b0))
    LOCAL (temp _r (vint r); temp _arg arg; gvars gv)
    SEP (data_at sh1 (tarray (tptr tint) N) reads (gv _reading); data_at sh1 (tarray (tptr tint) N) lasts (gv _last_read);
         data_at Ews tint Empty (Znth r reads); data_at Ews tint (vint b0) (Znth r lasts);
         data_at Ews tint (vint r) (force_val (sem_cast_pointer arg)); malloc_token Tsh tint arg;
         data_at sh1 (tarray (tptr tint) N) comms (gv _comm);
         data_at sh1 (tarray (tptr tlock) N) locks (gv _lock);
         data_at sh1 (tarray (tptr tbuffer) B) bufs (gv _bufs);
         comm_loc sh2 l c g g0 g1 g2 bufs sh gsh2 h;
         EX v : Z, @data_at CompSpecs sh tbuffer (vint v) (Znth b0 bufs);
         ghost_var gsh1 (vint b0) g0))
  break: (@FF (environ->mpred) _).
  { Exists 1 (empty_map : hist); entailer!. split. unfold B,N. computable.
    unfold latest_read.
    left; split; auto; discriminate. }
  Intros b0 h.
  subst c l; subst; forward_call (r, reads, lasts, locks, comms, bufs,
    sh, sh1, sh2, b0, g, g0, g1, g2, h, gv).
  { repeat (split; auto). }
  Intros x; destruct x as (((b, t), e), v); cbv [fst snd] in *.
  rewrite (data_at_isptr _ tbuffer); Intros.
  forward.
  forward.
  forward_call (r, reads, sh1, gv).
  entailer!.
  Exists b (map_upd h t (AE e Empty)) v; entailer!.
Qed.
