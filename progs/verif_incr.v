Require Import progs.conclib.
Require Import concurrency.xsemax_conc.
Require Import progs.incr.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.

Definition cptr_lock_inv lock sh ctr := lock_inv sh lock
  (EX z : Z, data_at Ews tint (Vint (Int.repr z)) ctr).
Definition lock_pred ctr :=
  Exp _ (fun z => Data_at _ Ews tint (Vint (Int.repr z)) ctr).

Definition incr_spec :=
 DECLARE _incr
  WITH ctr : val, sh : share, lock : val
  PRE [ ]
         PROP  (readable_share sh)
         LOCAL (gvar _ctr ctr; gvar _ctr_lock lock)
         SEP   (cptr_lock_inv lock sh ctr)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (cptr_lock_inv lock sh ctr).

Definition read_spec :=
 DECLARE _read
  WITH ctr : val, sh : share, lock : val
  PRE [ ]
         PROP  (readable_share sh)
         LOCAL (gvar _ctr ctr; gvar _ctr_lock lock)
         SEP   (cptr_lock_inv lock sh ctr)
  POST [ tint ] EX z : Z,
         PROP ()
         LOCAL (temp ret_temp (Vint (Int.repr z)))
         SEP (cptr_lock_inv lock sh ctr).

Definition thread_lock_inv sh ctr lockc lockt := lock_inv sh lockt (selflock (cptr_lock_inv lockc sh ctr) sh lockt).
Definition thread_lock_pred sh ctr lockc lockt := Self_lock (Lock_inv sh lockc (lock_pred ctr)) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : val * share * val * val
  PRE [ _args OF (tptr tvoid) ]
         let '(ctr, sh, lock, lockt) := x in
         PROP  ()
         LOCAL (temp _args y; gvar _ctr ctr; gvar _ctr_lock lock; gvar _thread_lock lockt)
         SEP   ((!!readable_share sh && emp); cptr_lock_inv lock sh ctr; thread_lock_inv sh ctr lock lockt)
  POST [ tptr tvoid ]
         PROP ()
         LOCAL ()
         SEP (emp).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

Definition Gprog : funspecs := augment_funspecs prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; incr_spec; read_spec; thread_func_spec; main_spec].

Lemma ctr_inv_precise : forall p,
  precise (EX x : Z, data_at Ews tint (Vint (Int.repr x)) p).
Proof.
  intro; eapply derives_precise, data_at__precise with (sh := Ews)(t := tint); auto.
  intros ? (? & H); apply data_at_data_at_ in H; eauto.
Qed.

Lemma ctr_inv_positive : forall ctr,
  positive_mpred (EX x : Z, data_at Ews tint (Vint (Int.repr x)) ctr).
Proof.
  intro; apply ex_positive; auto.
Qed.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (lock, sh, lock_pred ctr).
  { destruct lock; try contradiction; simpl; entailer. }
  { unfold Frame; instantiate (1 := []); entailer. }
  simpl.
  Intro z.
  forward.
  forward.
  rewrite field_at_isptr; normalize.
  forward_call (lock, sh, lock_pred ctr).
  { destruct lock; try contradiction; simpl; entailer. }
  { simpl; unfold Frame; instantiate (1 := []); entailer.
    Exists (z + 1); entailer. }
  { destruct ctr; try contradiction.
    split; auto; simpl; split; [apply ctr_inv_precise | apply ctr_inv_positive]. }
  forward.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward_call (lock, sh, lock_pred ctr).
  { destruct lock; try contradiction; simpl; entailer. }
  { unfold Frame; instantiate (1 := []); entailer. }
  simpl.
  Intro z.
  forward.
  rewrite data_at_isptr; normalize.
  forward_call (lock, sh, lock_pred ctr).
  { destruct lock; try contradiction; simpl; entailer. }
  { simpl; unfold Frame; instantiate (1 := []); entailer.
    Exists z; entailer. }
  { destruct ctr; try contradiction.
    split; auto; simpl; split; [apply ctr_inv_precise | apply ctr_inv_positive]. }
  forward.
  Exists z; entailer.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  normalize.
  forward.
  forward_call (ctr, sh, lock).
  forward_call (lockt, sh, Self_lock (Lock_inv sh lock (lock_pred ctr)) sh lockt).
  { destruct lockt; try contradiction; simpl; entailer. }
  { subst Frame; instantiate (1 := []).
    unfold thread_lock_inv, cptr_lock_inv; simpl.
    rewrite selflock_eq at 2; entailer!.
    apply lock_inv_later. }
  { split; auto; simpl; split; [|split].
    - apply selflock_precise, lock_inv_precise.
    - apply selflock_positive, lock_inv_positive.
    - apply selflock_rec. }
  forward.
Qed.

Definition thread_lock_pred' sh ctr lockc lockt := Later (Self_lock (Lock_inv sh lockc (lock_pred ctr)) sh lockt).

Lemma lock_struct : forall p, data_at_ Ews (Tstruct _lock_t noattr) p |-- data_at_ Ews tlock p.
Proof.
  intros.
  unfold data_at_, field_at_; unfold_field_at 1%nat.
  unfold field_at; simpl.
  rewrite field_compatible_cons; simpl; entailer.
  (* temporarily broken *)
Admitted.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  name ctr _ctr; name lockt _thread_lock; name lock _ctr_lock.
  start_function.
  forward.
  forward.
  forward.
  forward_call (lock, Ews, lock_pred ctr).
  { destruct lock; try contradiction; simpl; entailer. }
  { rewrite (sepcon_comm _ (fold_right _ _ _)); apply sepcon_derives; [cancel | apply lock_struct]. }
  rewrite field_at_isptr; normalize.
  forward_call (lock, Ews, lock_pred ctr).
  { destruct lock; try contradiction; simpl; entailer. }
  { simpl.
    Exists 0; cancel. }
  { destruct ctr; try contradiction.
    split; auto; split; [apply ctr_inv_precise | apply ctr_inv_positive]. }
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (lockt, Ews, thread_lock_pred sh1 ctr lock lockt).
  { destruct lockt; try contradiction; simpl; entailer. }
  { rewrite (sepcon_comm _ (fold_right _ _ _)); apply sepcon_derives; [cancel | apply lock_struct]. }
  get_global_function'' _thread_func.
  normalize.
  apply extract_exists_pre; intros f_.
  forward_call (f_, Vint (Int.repr 0), existT (fun ty => ty * (ty -> val -> Pred))%type
   (val * share * val * val)%type ((ctr, sh1, lock, lockt),
   fun (x : (val * share * val * val)) (_ : val) => let '(ctr, sh, lock, tlock) := x in
     Pred_list [Pred_prop (readable_share sh); Lock_inv sh lock (lock_pred ctr);
    Lock_inv sh tlock (thread_lock_pred sh ctr lock tlock)])).
  { entailer.
    Exists _args; entailer.
    Exists (fun x : val * share * val * val => let '(ctr, sh, lock, lockt) := x in
      [(_ctr, ctr); (_ctr_lock, lock); (_thread_lock, lockt)]); simpl; entailer.
    evar (body : funspec); replace (WITH _ : _ PRE [_] _ POST [_] _) with body.
    repeat rewrite sepcon_assoc; apply sepcon_derives; subst body; [apply derives_refl|].
    subst Frame; instantiate (1 := [lock_inv sh2 lockt (Interp (thread_lock_pred sh1 ctr lock lockt));
      lock_inv sh2 lock (Interp (lock_pred ctr))]).
    simpl; entailer.
    repeat rewrite sepcon_assoc; erewrite <- (sepcon_assoc (lock_inv sh1 lockt _)), lock_inv_share_join; eauto.
    cancel.
    repeat rewrite sepcon_assoc; erewrite lock_inv_share_join; eauto; cancel.
    subst body; f_equal.
    extensionality.
    destruct x as (?, (((?, ?), ?), ?)); simpl.
    f_equal; f_equal.
    unfold SEPx; simpl.
    unfold thread_lock_inv, cptr_lock_inv; normalize. }
  forward_call (ctr, sh2, lock).
  { subst Frame; instantiate (1 := [lock_inv sh2 lockt (Interp (thread_lock_pred sh1 ctr lock lockt))]); simpl.
    unfold cptr_lock_inv; entailer!. }
  forward_call (lockt, sh2, thread_lock_pred sh1 ctr lock lockt).
  { destruct lockt; try contradiction; simpl; entailer. }
  forward_call (ctr, sh2, lock).
  Intro z.
  forward_call (lock, sh2, lock_pred ctr).
  { destruct lock; try contradiction; simpl; entailer. }
  { unfold cptr_lock_inv; simpl; entailer!. }
  forward_call (lockt, Ews, thread_lock_pred' sh1 ctr lock lockt).
  { destruct lockt; try contradiction; simpl; entailer. }
  { subst Frame; instantiate (1 := [cptr_lock_inv lock Ews ctr; Interp (lock_pred ctr)]); simpl; cancel.
    rewrite selflock_eq at 2.
    rewrite sepcon_assoc, <- (sepcon_assoc (lock_inv _ lockt _)), (sepcon_comm (lock_inv _ lockt _)).
    apply sepalg.join_comm in Hsh.
    unfold cptr_lock_inv.
    repeat rewrite <- sepcon_assoc; erewrite lock_inv_share_join; eauto; cancel.
    eapply derives_trans.
    { apply sepcon_derives; [apply lock_inv_later | apply derives_refl]. }
    erewrite lock_inv_share_join; eauto; unfold rec_inv; entailer. }
  { split; auto; split.
    - apply later_positive, selflock_positive, lock_inv_positive.
    - apply later_rec, selflock_rec. }
  forward_call (lock, Ews, lock_pred ctr).
  { destruct lock; try contradiction; simpl; entailer. }
  { unfold cptr_lock_inv; simpl; entailer!. }
  { split; [auto | apply ctr_inv_positive]. }
  forward.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
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
