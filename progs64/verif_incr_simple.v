Require Import VST.concurrency.conclib.
Require Import VST.concurrency.lock_specs.
Require Import VST.atomics.verif_lock.
Require Import VST.progs64.incr.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition t_counter := Tstruct _counter noattr.

Definition cptr_lock_inv ctr := EX z : Z, field_at Ews t_counter [StructField _ctr] (Vint (Int.repr z)) ctr.

Definition incr_spec :=
 DECLARE _incr
  WITH gv : globals, sh1 : share, sh : share, h : lock_handle
  PRE [ ]
         PROP  (readable_share sh1; sh <> Share.bot)
         PARAMS() GLOBALS(gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv (gv _c)))
  POST [ tvoid ]
         PROP ()
         RETURN ()
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv (gv _c))).

Definition read_spec :=
 DECLARE _read
  WITH gv : globals, sh1 : share, sh : share, h : lock_handle
  PRE [ ]
         PROP  (readable_share sh1; sh <> Share.bot)
         PARAMS() GLOBALS(gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv (gv _c)))
  POST [ tuint ]
    EX z : Z,
         PROP ()
         RETURN (Vint (Int.repr z))
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv (gv _c))).

Definition thread_lock_R sh1 sh ctr lockc :=
  field_at sh1 t_counter [StructField _lock] (ptr_of lockc) ctr * lock_inv sh lockc (cptr_lock_inv ctr).

Definition thread_lock_inv sh1 sh ctr lockc lockt :=
  selflock (thread_lock_R sh1 sh ctr lockc) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * share * lock_handle * lock_handle * globals
  PRE [ tptr tvoid ]
         let '(sh1, sh, h, ht, gv) := x in
         PROP  (readable_share sh1; sh <> Share.bot; ptr_of ht = y)
         PARAMS (y) GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv (gv _c));
                lock_inv sh ht (thread_lock_inv sh1 sh (gv _c) h ht))
  POST [ tint ]
         PROP ()
         RETURN (Vint Int.zero)
         SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  freelock_spec; spawn_spec; incr_spec; read_spec; thread_func_spec; main_spec]).

Lemma ctr_inv_exclusive : forall p,
  exclusive_mpred (cptr_lock_inv p).
Proof.
  intros; unfold cptr_lock_inv.
  eapply derives_exclusive, field_at__exclusive with (sh := Ews)(t := t_counter); auto; simpl; try lia.
  Intro z; cancel.
  { simpl; lia. }
Qed.
#[export] Hint Resolve ctr_inv_exclusive : core.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (sh, h, cptr_lock_inv (gv _c)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z.
  forward.
  forward.
  forward.
  forward_call release_simple (sh, h, cptr_lock_inv (gv _c)).
  { lock_props.
    unfold cptr_lock_inv; Exists (z + 1).
    entailer!. }
  forward.
  cancel.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward.
  forward_call (sh, h, cptr_lock_inv (gv _c)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z.
  forward.
  forward.
  forward_call release_simple (sh, h, cptr_lock_inv (gv _c)).
  { lock_props.
    unfold cptr_lock_inv; Exists z; entailer!. }
  forward.
  Exists z; entailer!.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  forward_call (gv, sh1, sh, h).
  forward_call release_self (sh, ht, thread_lock_R sh1 sh (gv _c) h).
  { unfold thread_lock_inv, selflock, thread_lock_R; cancel. }
  forward.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (library.create_mem_mgr gv).
  set (ctr := gv _c).
  forward.
  forward_call (gv, fun _ : lock_handle => cptr_lock_inv ctr).
  Intros lock.
  forward.
  forward.
  forward_call release_simple (Tsh, lock, cptr_lock_inv ctr).
  { lock_props.
    unfold_data_at (data_at _ _ _ _).
    unfold cptr_lock_inv; Exists 0; entailer!. }
  { contradiction Share.nontrivial. }
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (gv, thread_lock_inv sh2 gsh2 ctr lock).
  Intros lockt.
  subst ctr.
  sep_apply lock_inv_isptr; Intros.
  forward_spawn _thread_func (ptr_of lockt) (sh2, gsh2, lock, lockt, gv).
  { erewrite <- lock_inv_share_join; try apply gsh1_gsh2_join; auto.
    erewrite <- (lock_inv_share_join _ _ Tsh); try apply gsh1_gsh2_join; auto.
    erewrite <- field_at_share_join; try apply Hsh; auto.
    entailer!. }
  { simpl; auto. }
  forward_call (gv, sh1, gsh1, lock).
  forward_call (gsh1, lockt, thread_lock_inv sh2 gsh2 (gv _c) lock lockt).
  unfold thread_lock_inv at 2; unfold thread_lock_R, selflock; Intros.
  forward_call (gv, sh1, gsh1, lock).
  Intros z.
  forward.
  forward_call (gsh1, lock, cptr_lock_inv (gv _c)).
  forward_call freelock_self (gsh1, gsh2, lockt, thread_lock_R sh2 gsh2 (gv _c) lock).
  { unfold thread_lock_inv, selflock; cancel. }
  forward.
  forward_call freelock_simple (lock, cptr_lock_inv (gv _c)).
  { lock_props.
    erewrite <- (lock_inv_share_join _ _ Tsh); try apply gsh1_gsh2_join; auto; cancel. }
  forward.
Qed.

Definition extlink := ext_link_prog prog.
Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
#[export] Existing Instance Espec.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons_ext.
{ simpl.
  Intros h.
  unfold PROPx, LOCALx, SEPx, local, lift1; simpl; unfold liftx; simpl; unfold lift; Intros.
  destruct ret; unfold eval_id in H0; simpl in H0; subst; simpl; [|contradiction].
  saturate_local; apply prop_right; auto. }
do 4 semax_func_cons_ext.
semax_func_cons body_incr.
semax_func_cons body_read.
semax_func_cons body_thread_func.
semax_func_cons body_main.
Qed. 
