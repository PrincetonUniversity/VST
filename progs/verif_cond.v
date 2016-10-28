Require Import progs.conclib.
Require Import progs.cond.

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

Definition lock_pred data :=
  Exp _ (fun i => Data_at _ Ews tint (Vint (Int.repr i)) data).

Definition tlock_pred sh lockt lock cond data :=
  Self_lock (Pred_list [Cond_var _ sh cond; Lock_inv sh lock (lock_pred data)]) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : val * share * val * val * val
  PRE [ _args OF (tptr tvoid) ]
         let '(data, sh, lock, lockt, cond) := x in
         PROP  ()
         LOCAL (temp _args y; gvar _data data; gvar _mutex lock; gvar _tlock lockt;
                gvar _cond cond)
         SEP   ((!!readable_share sh && emp); cond_var sh cond;
                lock_inv sh lock (Interp (lock_pred data));
                lock_inv sh lockt (Interp (tlock_pred sh lockt lock cond data)))
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
  freelock_spec; freelock2_spec; spawn_spec; makecond_spec; freecond_spec; wait_spec; signal_spec;
  thread_func_spec; main_spec].

Lemma inv_precise : forall p,
  precise (EX x : Z, data_at Ews tint (Vint (Int.repr x)) p).
Proof.
  intro; eapply derives_precise, data_at__precise with (sh := Ews)(t := tint); auto.
  intros ? (? & H); apply data_at_data_at_ in H; eauto.
Qed.

Lemma inv_positive : forall ctr,
  positive_mpred (EX x : Z, data_at Ews tint (Vint (Int.repr x)) ctr).
Proof.
  intro; apply ex_positive; auto.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  normalize.
  forward.
  forward.
  forward.
  forward_call (lock, sh, lock_pred data).
  { destruct lock; try contradiction; simpl; entailer. }
  simpl.
  Intro i.
  forward.
  forward_call (cond, sh).
  rewrite field_at_isptr; normalize.
  forward_call (lock, sh, lock_pred data).
  { destruct lock; try contradiction; simpl; entailer. }
  { simpl; entailer!.
    Exists 1.
    unfold data_at_, field_at_; entailer!. }
  { split; auto; destruct data; try contradiction; split.
    - apply inv_precise.
    - apply inv_positive. }
  rewrite cond_var_isptr; normalize.
  forward_call (lockt, sh, tlock_pred sh lockt lock cond data).
  { destruct lockt; try contradiction; simpl; entailer. }
  { subst Frame; instantiate (1 := []); simpl.
    setoid_rewrite selflock_eq at 2; entailer!.
    apply lock_inv_later. }
  { split; auto; simpl; split; [|split]; normalize.
    - apply selflock_precise, precise_sepcon; [|apply lock_inv_precise].
      destruct cond; try contradiction; apply cond_var_precise; auto.
    - apply selflock_positive, positive_sepcon2, lock_inv_positive.
    - apply selflock_rec. }
  forward.
Qed.

Lemma lock_struct : forall p, data_at_ Ews (Tstruct _lock_t noattr) p |-- data_at_ Ews tlock p.
Proof.
  intros.
  unfold data_at_, field_at_, field_at; simpl; entailer.
  unfold default_val; simpl.
  rewrite data_at_rec_eq; simpl.
  unfold struct_pred, aggregate_pred.struct_pred, at_offset, withspacer; simpl; entailer.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  name lock _mutex; name lockt _tlock; name cond _cond; name data _data.
  start_function.
  forward.
  forward.
  forward.
  forward.
  forward_call (cond, Ews).
  { unfold tcond; entailer!. }
  rewrite field_at_isptr; normalize.
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (lock, Ews, lock_pred data).
  { destruct lock; try contradiction; simpl; entailer. }
  { rewrite (sepcon_comm _ (fold_right _ _ _)); apply sepcon_derives; [cancel | apply lock_struct]. }
  forward_call (lockt, Ews, tlock_pred sh1 lockt lock cond data).
  { destruct lockt; try contradiction; simpl; entailer. }
  { rewrite (sepcon_comm _ (fold_right _ _ _)); apply sepcon_derives; [cancel | apply lock_struct]. }
  get_global_function'' _thread_func.
  normalize.
  apply extract_exists_pre; intros f_.
  forward_call (f_, Vint (Int.repr 0), existT (fun ty => ty * (ty -> val -> Pred))%type
   (val * share * val * val * val)%type ((data, sh1, lock, lockt, cond),
   fun (x : (val * share * val * val * val)) (_ : val) => let '(data, sh, lock, lockt, cond) := x in
     Pred_list [Pred_prop (readable_share sh); Cond_var _ sh cond; Lock_inv sh lock (lock_pred data);
                Lock_inv sh lockt (tlock_pred sh lockt lock cond data)])).
  { entailer.
    Exists _args; entailer.
    Exists (fun x :val * share * val * val * val => let '(data, sh, lock, lockt, cond) := x in
      [(_data, data); (_mutex, lock); (_tlock, lockt); (_cond, cond)]); entailer.
    subst Frame; instantiate (1 := [lock_inv sh2 lockt (Interp (tlock_pred sh1 lockt lock cond data));
      lock_inv sh2 lock (Interp (lock_pred data)); cond_var sh2 cond;
      field_at Ews tint [] (Vint (Int.repr 0)) data]).
    evar (body : funspec); replace (WITH _ : _ PRE [_] _ POST [_] _) with body.
    repeat rewrite sepcon_assoc; apply sepcon_derives; subst body; [apply derives_refl|].
    simpl; entailer; cancel.
    repeat rewrite sepcon_assoc.
    rewrite <- (sepcon_assoc (lock_inv sh1 lockt _)).
    erewrite lock_inv_share_join; eauto; cancel.
    repeat rewrite sepcon_assoc.
    rewrite <- (sepcon_assoc (lock_inv sh1 lock _)).
    erewrite lock_inv_share_join; eauto; cancel.
    erewrite cond_var_share_join; eauto.
    subst body; f_equal.
    extensionality.
    destruct x as (?, ((((?, ?), ?), ?), ?)); simpl.
    f_equal; f_equal.
    unfold SEPx; simpl; normalize. }
  forward.
  forward_while (EX i : Z, PROP ( )
   LOCAL (temp _v (Vint (Int.repr i)); temp _c cond; temp _t lockt; temp _l lock; gvar _data data;
     gvar _cond cond; gvar _tlock lockt; gvar _mutex lock)
   SEP (lock_inv sh2 lockt (Interp (tlock_pred sh1 lockt lock cond data));
        lock_inv sh2 lock (Interp (lock_pred data)); cond_var sh2 cond;
        Interp (lock_pred data))).
  { Exists 0; entailer!.
    Exists 0; entailer. }
  { entailer. }
  - (* loop body *)
    forward_call (cond, lock, sh2, sh2, lock_pred data).
    { destruct lock; try contradiction; simpl; entailer. }
    simpl; Intro i'.
    forward.
    Exists i'; entailer.
    Exists i'; entailer!.
  - forward_call (lockt, sh2, tlock_pred sh1 lockt lock cond data).
    { destruct lockt; try contradiction; simpl; entailer. }
    forward_call (lockt, Ews, Later (tlock_pred sh1 lockt lock cond data)).
    { destruct lockt; try contradiction; simpl; entailer. }
    { subst Frame; instantiate (1 := [lock_inv Ews lock (Interp (lock_pred data));
        cond_var Ews cond; Interp (lock_pred data)]); simpl; cancel.
      rewrite selflock_eq at 2.
      rewrite sepcon_assoc, <- (sepcon_assoc (lock_inv _ lockt _)), (sepcon_comm (lock_inv _ lockt _)).
      repeat rewrite sepcon_assoc; rewrite <- (sepcon_assoc (lock_inv sh2 lockt _)).
      apply sepalg.join_comm in Hsh.
      eapply derives_trans.
      { apply sepcon_derives; [apply derives_refl|].
        apply sepcon_derives; [apply derives_refl|].
        apply sepcon_derives; [|apply derives_refl].
        apply sepcon_derives; [apply lock_inv_later | apply derives_refl]. }
      erewrite lock_inv_share_join; eauto; cancel.
      repeat rewrite sepcon_assoc; rewrite <- (sepcon_assoc (lock_inv _ lock _)).
      apply sepalg.join_comm in Hsh.
      erewrite lock_inv_share_join; eauto; cancel.
      erewrite cond_var_share_join; eauto. }
    { split; auto; split.
      + apply later_positive, selflock_positive; simpl.
        apply positive_sepcon2, positive_sepcon1, lock_inv_positive.
      + apply later_rec, selflock_rec. }
    forward_call (lock, Ews, lock_pred data).
    { destruct lock; try contradiction; simpl; entailer. }
    { split; [auto | apply inv_positive]. }
    forward_call (cond, Ews).
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
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons body_thread_func.
semax_func_cons body_main.
Qed.
