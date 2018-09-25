Require Import VST.progs.conclib.
Require Import VST.progs.incr.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.

Definition cptr_lock_inv ctr := EX z : Z, data_at Ews tuint (Vint (Int.repr z)) ctr.

Definition incr_spec :=
 DECLARE _incr
  WITH gv : globals, sh : share
  PRE [ ]
         PROP  (readable_share sh)
         LOCAL (gvars gv)
         SEP   (lock_inv sh (gv _ctr_lock) (cptr_lock_inv (gv _ctr)))
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (lock_inv sh (gv _ctr_lock) (cptr_lock_inv (gv _ctr))).

Definition read_spec :=
 DECLARE _read
  WITH gv : globals, sh : share
  PRE [ ]
         PROP  (readable_share sh)
         LOCAL (gvars gv)
         SEP   (lock_inv sh (gv _ctr_lock) (cptr_lock_inv (gv _ctr)))
  POST [ tuint ]
    EX z : Z,
         PROP ()
         LOCAL (temp ret_temp (Vint (Int.repr z)))
         SEP (lock_inv sh (gv _ctr_lock) (cptr_lock_inv (gv _ctr))).

Definition thread_lock_R sh ctr lockc :=
  lock_inv sh lockc (cptr_lock_inv ctr).

Definition thread_lock_inv sh ctr lockc lockt :=
  selflock (thread_lock_R sh ctr lockc) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * globals
  PRE [ _args OF (tptr tvoid) ]
         let '(sh, gv) := x in
         PROP  (readable_share sh)
         LOCAL (temp _args y; gvars gv)
         SEP   (lock_inv sh (gv _ctr_lock) (cptr_lock_inv (gv _ctr));
                lock_inv sh (gv _thread_lock) (thread_lock_inv sh (gv _ctr) (gv _ctr_lock) (gv _thread_lock)))
  POST [ tptr tvoid ]
         PROP ()
         LOCAL ()
         SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ] main_post prog nil gv.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; incr_spec; read_spec; thread_func_spec; main_spec]).

Lemma ctr_inv_exclusive : forall p,
  exclusive_mpred (cptr_lock_inv p).
Proof.
  intros; unfold cptr_lock_inv.
  eapply derives_exclusive, data_at__exclusive with (sh := Ews)(t := tuint); auto; simpl; try omega.
  Intro z; cancel.
Qed.
Hint Resolve ctr_inv_exclusive.

Lemma thread_inv_exclusive : forall sh ctr lock lockt,
  exclusive_mpred (thread_lock_inv sh ctr lock lockt).
Proof.
  intros; apply selflock_exclusive.
  unfold thread_lock_R; auto.
Qed.
Hint Resolve thread_inv_exclusive.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (gv _ctr_lock, sh, cptr_lock_inv (gv _ctr)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z.
  forward.
  forward.
  forward_call (gv _ctr_lock, sh, cptr_lock_inv (gv _ctr)).
  { lock_props.
    unfold cptr_lock_inv; Exists (z + 1).
    entailer!. }
  forward.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward_call (gv _ctr_lock, sh, cptr_lock_inv (gv _ctr)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z.
  forward.
  forward_call (gv _ctr_lock, sh, cptr_lock_inv (gv _ctr)).
  { lock_props.
    unfold cptr_lock_inv; Exists z; entailer!. }
  forward.
  Exists z; entailer!.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (gv, sh).
  set (lockt := gv _thread_lock).
  set (lock := gv _ctr_lock).
  set (ctr := gv _ctr).
  forward_call (lockt, sh, thread_lock_R sh ctr lock, thread_lock_inv sh ctr lock lockt).
  { lock_props.
    unfold thread_lock_inv, thread_lock_R.
    rewrite selflock_eq at 2; cancel. }
  forward.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  set (ctr := gv _ctr); set (lockt := gv _thread_lock); set (lock := gv _ctr_lock).
  forward.
  forward.
  forward.
  forward_call (lock, Ews, cptr_lock_inv ctr).
  { rewrite sepcon_comm; apply sepcon_derives; [apply derives_refl | cancel]. }
  forward_call (lock, Ews, cptr_lock_inv ctr).
  { lock_props.
    unfold cptr_lock_inv; Exists 0; entailer!. }
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (lockt, Ews, thread_lock_inv sh1 ctr lock lockt).
  { rewrite sepcon_comm; apply sepcon_derives; [apply derives_refl | cancel]. }
  subst lockt; subst lock; subst ctr.
  forward_spawn _thread_func nullval (sh1, gv).
  { erewrite <- lock_inv_share_join; try apply Hsh; auto.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto.
    entailer!. }
  forward_call (gv, sh2).
  forward_call (gv _thread_lock, sh2, thread_lock_inv sh1 (gv _ctr) (gv _ctr_lock) (gv _thread_lock)).
  unfold thread_lock_inv at 2; unfold thread_lock_R.
  rewrite selflock_eq; Intros.
  forward_call (gv, sh2).
  Intros z.
  set (lockt := gv _thread_lock).
  set (lock := gv _ctr_lock).
  set (ctr := gv _ctr).
  forward_call (lock, sh2, cptr_lock_inv ctr).
  forward_call (lockt, Ews, sh1, thread_lock_R sh1 ctr lock, thread_lock_inv sh1 ctr lock lockt).
  { lock_props.
    unfold thread_lock_inv, thread_lock_R.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel. }
  forward_call (lock, Ews, cptr_lock_inv ctr).
  { lock_props.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel. }
  forward.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons body_incr.
semax_func_cons body_read.
semax_func_cons body_thread_func.
semax_func_cons body_main.
Qed.
