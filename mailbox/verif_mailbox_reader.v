Require Import mailbox.verif_atomic_exchange.
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.
Require Import VST.zlist.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.

Ltac entailer_for_load_tac ::= unfold tc_efield; go_lower; entailer'.
Ltac entailer_for_store_tac ::= unfold tc_efield; go_lower; entailer'.

Section mpred.

Context `{!VSTGS unit Σ, AEGS0 : !AEGS t_atom_int, !inG Σ (excl_authR (leibnizO val))}.

Lemma body_reader : semax_body Vprog Gprog f_reader reader_spec.
Proof.
  start_function.
  assert (B < Int.max_signed) by computable.
  rewrite (data_at_isptr _ tint); Intros.
  replace_SEP 0 (data_at Ews tint (vint r) (force_val (sem_cast_pointer arg))).
  { rewrite sem_cast_neutral_ptr; auto; go_lowerx; cancel. }
  forward.
  forward_call (r, reads, lasts, sh1, gv).
(*  eapply semax_seq'; [|apply semax_ff]. *)
  set (c := Znth r comms).
  forward_loop (∃ b0 : Z, ∃ h : hist, PROP (0 <= b0 < B; latest_read h (vint b0))
    LOCAL (temp _r (vint r); temp _arg arg; gvars gv)
    SEP (data_at sh1 (tarray (tptr tint) N) reads (gv _reading); data_at sh1 (tarray (tptr tint) N) lasts (gv _last_read);
         data_at Ews tint Empty (Znth r reads); data_at Ews tint (vint b0) (Znth r lasts);
         data_at Ews tint (vint r) (force_val (sem_cast_pointer arg)); malloc_token Ews tint arg;
         data_at sh1 (tarray (tptr t_atom_int) N) comms (gv _comm);
         data_at sh1 (tarray (tptr tbuffer) B) bufs (gv _bufs);
         comm_loc sh2 c g g0 g1 g2 bufs sh h;
         ∃ v : Z, data_at sh tbuffer (vint v) (Znth b0 bufs);
         ghost_frag (vint b0) g0))
  break: (False : assert).
  { Exists 1 (∅ : hist); entailer!.
    unfold latest_read.
    left; split; auto; discriminate. }
  Intros b0 h.
  subst c; subst; forward_call (r, reads, lasts, comms, bufs,
    sh, sh1, sh2, b0, g, g0, g1, g2, h, gv).
  Intros x; destruct x as (((b, t), e), v); cbv [fst snd] in *.
  rewrite (data_at_isptr _ tbuffer); Intros.
  forward.
  forward.
  forward_call (r, reads, sh1, gv).
  entailer!.
  Exists b (<[t := Excl (AE e Empty)]>h) v; entailer!.
Qed.

End mpred.
