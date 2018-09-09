Require Import VST.progs.conclib.
Require Import VST.progs.cond.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makecond_spec := DECLARE _makecond (makecond_spec _).
Definition freecond_spec := DECLARE _freecond (freecond_spec _).
Definition wait_spec := DECLARE _waitcond (wait_spec _).
Definition signal_spec := DECLARE _signalcond (signal_spec _).

Definition dlock_inv data := EX i : Z, data_at Ews tint (vint i) data.

Definition tlock_inv sh lockt lock cond data :=
  selflock (cond_var sh cond * lock_inv sh lock (dlock_inv data)) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * globals
  PRE [ _args OF (tptr tvoid) ]
         let '(sh, gv) := x in
         PROP  (readable_share sh)
         LOCAL (temp _args y; gvars gv)
         SEP   (cond_var sh (gv _cond);
                lock_inv sh (gv _mutex) (dlock_inv (gv _data));
                lock_inv sh (gv _tlock) (tlock_inv sh (gv _tlock) (gv _mutex) (gv _cond) (gv _data)))
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
  freelock_spec; freelock2_spec; spawn_spec; makecond_spec; freecond_spec; wait_spec; signal_spec;
  thread_func_spec; main_spec]).

Lemma inv_exclusive : forall p, exclusive_mpred (dlock_inv p).
Proof.
  intro; eapply derives_exclusive, data_at__exclusive with (sh := Ews)(t := tint); simpl; auto; try omega.
  unfold dlock_inv.
  Intros i; cancel.
Qed.
Hint Resolve inv_exclusive.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward.
  forward.
  forward_call (gv _mutex, sh, dlock_inv (gv _data)).
  unfold dlock_inv; simpl.
  Intro i.
  forward.
  forward_call (gv _cond, sh).
  forward_call (gv _mutex, sh, dlock_inv (gv _data)).
  { lock_props.
    unfold dlock_inv; Exists 1; cancel. }
  rewrite cond_var_isptr; Intros.
  forward_call (gv _tlock, sh, cond_var sh (gv _cond) * lock_inv sh (gv _mutex) (dlock_inv (gv _data)),
                tlock_inv sh (gv _tlock) (gv _mutex) (gv _cond) (gv _data)).
  { unfold tlock_inv; lock_props.
    { apply selflock_exclusive, exclusive_sepcon2, lock_inv_exclusive. }
    rewrite selflock_eq at 2; cancel. }
  forward.
Qed.

Ltac cancel_for_forward_call ::=
  match goal with
  | gv: globals |- _ =>
    repeat
    match goal with
    | x := gv ?i |- context [gv ?i] =>
        change (gv i) with x
    end
  | _ => idtac
  end;
  cancel_for_evar_frame.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
(*  name lock _mutex; name lockt _tlock; name cond _cond; name data _data. *)
  start_function.  
  simpl readonly2share. (* TODO: delete this line when possible. *)
  set (lock := gv _mutex). set (lockt := gv _tlock). set (cond := gv _cond). set (data := gv _data).
  forward.
  forward.
  forward.
  forward.
  forward_call (cond, Ews).
  { unfold tcond; entailer!. }
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (lock, Ews, dlock_inv data).
   change tlock with (tarray (tptr tvoid) 2). cancel.
  forward_call (lockt, Ews, tlock_inv sh1 lockt lock cond data).
   change tlock with (tarray (tptr tvoid) 2). cancel.
  forward_spawn _thread_func nullval (sh1, gv).
  { erewrite <- lock_inv_share_join; try apply Hsh; auto.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto.
    erewrite <- cond_var_share_join; try apply Hsh; auto.
    entailer!. }
  forward.
  forward_while (EX i : Z, PROP ( )
   LOCAL (temp _v (Vint (Int.repr i)); temp _c cond; temp _t lockt; temp _l lock; gvars gv)
   SEP (lock_inv sh2 lockt (tlock_inv sh1 lockt lock cond data);
        lock_inv sh2 lock (dlock_inv data); cond_var sh2 cond; dlock_inv data)).
  { Exists 0; entailer!.
    Exists 0; entailer. }
  { entailer. }
  - (* loop body *)
    forward_call (cond, lock, sh2, sh2, dlock_inv data).
    unfold dlock_inv; Intro i'.
    forward.
    unfold dlock_inv; Exists i'; entailer!.
    Exists i'; entailer!.
  - forward_call (lockt, sh2, tlock_inv sh1 lockt lock cond data).
    unfold tlock_inv at 2.
    rewrite selflock_eq.
    Intros.
    forward_call (lockt, Ews, sh1, cond_var sh1 cond * lock_inv sh1 lock (dlock_inv data),
                  tlock_inv sh1 lockt lock cond data).
    { unfold tlock_inv; lock_props.
      { apply selflock_exclusive, exclusive_sepcon2, lock_inv_exclusive. }
      erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel. }
    forward_call (lock, Ews, dlock_inv data).
    { lock_props.
      erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel. }
    forward_call (cond, Ews).
    { erewrite !sepcon_assoc, cond_var_share_join; eauto; cancel. }
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
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons body_thread_func.
semax_func_cons body_main.
Qed.
