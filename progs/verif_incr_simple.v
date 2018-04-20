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
  WITH ctr : val, sh : share, lock : val
  PRE [ ]
         PROP  (readable_share sh)
         LOCAL (gvar _ctr ctr; gvar _ctr_lock lock)
         SEP   (lock_inv sh lock (cptr_lock_inv ctr))
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (lock_inv sh lock (cptr_lock_inv ctr)).

Definition read_spec :=
 DECLARE _read
  WITH ctr : val, sh : share, lock : val
  PRE [ ]
         PROP  (readable_share sh)
         LOCAL (gvar _ctr ctr; gvar _ctr_lock lock)
         SEP   (lock_inv sh lock (cptr_lock_inv ctr))
  POST [ tuint ]
    EX z : Z,
         PROP ()
         LOCAL (temp ret_temp (Vint (Int.repr z)))
         SEP (lock_inv sh lock (cptr_lock_inv ctr)).

Definition thread_lock_R sh ctr lockc :=
  lock_inv sh lockc (cptr_lock_inv ctr).

Definition thread_lock_inv sh ctr lockc lockt :=
  selflock (thread_lock_R sh ctr lockc) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : val * share * val * val
  PRE [ _args OF (tptr tvoid) ]
         let '(ctr, sh, lock, lockt) := x in
         PROP  ()
         LOCAL (temp _args y; gvar _ctr ctr; gvar _ctr_lock lock; gvar _thread_lock lockt)
         SEP   ((!!readable_share sh && emp); lock_inv sh lock (cptr_lock_inv ctr);
                lock_inv sh lockt (thread_lock_inv sh ctr lock lockt))
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

Lemma ctr_inv_precise : forall p,
  precise (cptr_lock_inv p).
Proof.
  intros; eapply derives_precise;
  [| apply data_at__precise with (sh := Ews)(t := tuint)].
  unfold cptr_lock_inv; Intros z.
  entailer!.
Qed.
Hint Resolve ctr_inv_precise.

Lemma ctr_inv_positive : forall ctr,
  positive_mpred (cptr_lock_inv ctr).
Proof.
  intros; unfold cptr_lock_inv.
  apply ex_positive; intro; auto.
Qed.
Hint Resolve ctr_inv_positive.

Lemma thread_inv_precise : forall sh ctr lock lockt,
  precise (thread_lock_inv sh ctr lock lockt).
Proof.
  intros; apply selflock_precise, lock_inv_precise.
Qed.
Hint Resolve thread_inv_precise.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (lock, sh, cptr_lock_inv ctr).
  unfold cptr_lock_inv at 2; simpl.
  Intros z.
  forward.
  forward.
  forward_call (lock, sh, cptr_lock_inv ctr).
  { lock_props.
    unfold cptr_lock_inv; Exists (z + 1).
    rewrite add_repr; cancel. }
  forward.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward_call (lock, sh, cptr_lock_inv ctr).
  unfold cptr_lock_inv at 2; simpl.
  Intros z.
  forward.
  forward_call (lock, sh, cptr_lock_inv ctr).
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
  forward_call (ctr, sh, lock).
  forward_call (lockt, sh, thread_lock_R sh ctr lock, thread_lock_inv sh ctr lock lockt).
  { unfold thread_lock_inv; lock_props.
    { apply thread_inv_precise. }
    rewrite selflock_eq at 2; unfold thread_lock_R; cancel.
    eapply derives_trans; [apply lock_inv_later | cancel]. }
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
  make_func_ptr _thread_func.
  set (f_ := gv _thread_func).
  forward_spawn (val * share * val * val)%type (f_, Vint (Int.repr 0),
    fun x : val * share * val * val => let '(ctr, sh, lock, lockt) := x in
      [(_ctr, ctr); (_ctr_lock, lock); (_thread_lock, lockt)], (ctr, sh1, lock, lockt),
    fun (x : (val * share * val * val)) (_ : val) => let '(ctr, sh, lock, lockt) := x in
         !!readable_share sh && emp * lock_inv sh lock (cptr_lock_inv ctr) *
         lock_inv sh lockt (thread_lock_inv sh ctr lock lockt)).
  { simpl spawn_pre; entailer!.
    { erewrite gvar_eval_var, !(force_val_sem_cast_neutral_gvar' _ f_) by eauto.
      split; auto; repeat split; apply gvar_denote_global; auto. }
    Exists _args; entailer!.
    rewrite !sepcon_assoc; apply sepcon_derives.
    { apply derives_refl'. f_equal.
      f_equal; extensionality.
      destruct x as (?, x); repeat destruct x as (x, ?); simpl.
      extensionality; apply mpred_ext; entailer!. }
    erewrite <- lock_inv_share_join; try apply Hsh; auto.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto.
    entailer!. }
  forward_call (ctr, sh2, lock).
  forward_call (lockt, sh2, thread_lock_inv sh1 ctr lock lockt).
  forward_call (ctr, sh2, lock).
  Intros z.
  forward_call (lock, sh2, cptr_lock_inv ctr).
  forward_call (lockt, Ews, sh1, |>thread_lock_R sh1 ctr lock, |>thread_lock_inv sh1 ctr lock lockt).
  { unfold thread_lock_inv; lock_props.
    - apply later_positive; auto.
    - unfold rec_inv.
      rewrite selflock_eq at 1.
      rewrite later_sepcon; f_equal.
      apply lock_inv_later_eq.
    - rewrite selflock_eq at 2.
      erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel.
      rewrite (sepcon_comm _ (lock_inv sh2 lockt _)), !sepcon_assoc.
      apply sepcon_derives; [apply lock_inv_later | cancel]. }
  forward_call (lock, Ews, cptr_lock_inv ctr).
  { lock_props.
    unfold thread_lock_R.
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
