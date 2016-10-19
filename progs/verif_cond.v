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
  Exp _ (fun i => Data_at _ Ews (tarray tint 1) [Vint (Int.repr i)] data).

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
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Gprog : funspecs := augment_funspecs prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; makecond_spec; freecond_spec; wait_spec; signal_spec;
  thread_func_spec; main_spec].

Lemma inv_precise : forall p,
  precise (EX x : Z, data_at Ews (tarray tint 1) [Vint (Int.repr x)] p).
Proof.
  intros ???? (? & ? & ?) (? & ? & ?) ??.
  unfold at_offset in *; simpl in *.
  eapply data_at_int_array_inj; try eassumption; auto.
  { repeat constructor; auto; discriminate. }
  { repeat constructor; auto; discriminate. }
Qed.

Lemma inv_positive : forall ctr,
  positive_mpred (EX x : Z, data_at Ews (tarray tint 1) [Vint (Int.repr x)] ctr).
Proof.
  intros ?? (? & ? & Hp).
  eapply mapsto_positive with (sh := Ews); auto.
  unfold at_offset in Hp; rewrite data_at_rec_eq in Hp; destruct Hp as (? & ? & ? & Hjoin & Hp & Hemp);
    simpl in *.
  unfold at_offset in Hp; rewrite by_value_data_at_rec_nonvolatile in Hp; auto.
  specialize (Hemp _ _ (sepalg.join_comm Hjoin)); subst; eauto.
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
  start_function.
  rewrite <- (sepcon_emp (main_pre _ _)).
  rewrite main_pre_start; unfold prog_vars, prog_vars'; simpl globvars2pred.
  process_idstar.
  simpl init_data2pred'.
  rewrite <- (sepcon_emp (_ * _)).
  simple apply move_globfield_into_SEP.
  rewrite sepcon_emp.
  process_idstar.
  simpl init_data2pred'.
  rewrite <- (sepcon_emp (_ * _)).
  simple apply move_globfield_into_SEP.
  rewrite sepcon_emp.
  process_idstar.
  simpl init_data2pred'.
  rewrite <- (sepcon_emp (_ * _)).
  simple apply move_globfield_into_SEP.
  rewrite sepcon_emp.
  process_idstar.
  simpl init_data2pred'.
  rewrite <- (sepcon_emp (_ * _)).
  simple apply move_globfield_into_SEP.
  change (globvars2pred nil) with (@emp (environ->mpred) _ _).
  repeat rewrite sepcon_emp.
  forward.
  unfold default_val, upd_Znth, Zlength; simpl.
  rewrite sublist.sublist_nil.
  forward.
  forward.
  forward.
  forward_call (gvar2, Ews).
  { unfold tcond; entailer!. }
  rewrite field_at_isptr; normalize.
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (gvar0, Ews, lock_pred gvar3).
  { destruct gvar0; try contradiction; simpl; entailer. }
  { rewrite (sepcon_comm _ (fold_right _ _ _)); apply sepcon_derives; [cancel | apply lock_struct]. }
  forward_call (gvar1, Ews, tlock_pred sh1 gvar1 gvar0 gvar2 gvar3).
  { destruct gvar1; try contradiction; simpl; entailer. }
  { rewrite (sepcon_comm _ (fold_right _ _ _)); apply sepcon_derives; [cancel | apply lock_struct]. }
  get_global_function'' _thread_func.
  normalize.
  apply extract_exists_pre; intros f_.
  forward_call (f_, Vint (Int.repr 0), existT (fun ty => ty * (ty -> val -> Pred))%type
   (val * share * val * val * val)%type ((gvar3, sh1, gvar0, gvar1, gvar2),
   fun (x : (val * share * val * val * val)) (_ : val) => let '(data, sh, lock, lockt, cond) := x in
     Pred_list [Pred_prop (readable_share sh); Cond_var _ sh cond; Lock_inv sh lock (lock_pred data);
                Lock_inv sh lockt (tlock_pred sh lockt lock cond data)])).
  { entailer.
    Exists _args; entailer.
    Exists (fun x :val * share * val * val * val => let '(data, sh, lock, lockt, cond) := x in
      [(_data, data); (_mutex, lock); (_tlock, lockt); (_cond, cond)]); entailer.
    subst Frame; instantiate (1 := [lock_inv sh2 gvar1 (Interp (tlock_pred sh1 gvar1 gvar0 gvar2 gvar3));
      lock_inv sh2 gvar0 (Interp (lock_pred gvar3)); cond_var sh2 gvar2;
      field_at Ews (tarray tint 1) [] [Vint (Int.repr 0)] gvar3]).
    evar (body : funspec); replace (WITH _ : _ PRE [_] _ POST [_] _) with body.
    repeat rewrite sepcon_assoc; apply sepcon_derives; subst body; [apply derives_refl|].
    simpl; entailer; cancel.
    repeat rewrite sepcon_assoc.
    rewrite <- (sepcon_assoc (lock_inv sh1 gvar1 _)).
    erewrite lock_inv_share_join; eauto; cancel.
    repeat rewrite sepcon_assoc.
    rewrite <- (sepcon_assoc (lock_inv sh1 gvar0 _)).
    erewrite lock_inv_share_join; eauto; cancel.
    erewrite cond_var_share_join; eauto.
    subst body; f_equal.
    extensionality.
    destruct x as (?, ((((?, ?), ?), ?), ?)); simpl.
    f_equal; f_equal.
    unfold SEPx; simpl; normalize. }
  forward.
  forward_while (EX i : Z, PROP ( )
   LOCAL (temp _v (Vint (Int.repr i)); temp _c gvar2; temp _t gvar1; temp _l gvar0; gvar _data gvar3;
     gvar _cond gvar2; gvar _tlock gvar1; gvar _mutex gvar0)
   SEP (lock_inv sh2 gvar1 (Interp (tlock_pred sh1 gvar1 gvar0 gvar2 gvar3));
        lock_inv sh2 gvar0 (Interp (lock_pred gvar3)); cond_var sh2 gvar2;
        Interp (lock_pred gvar3))).
  { Exists 0; entailer!.
    Exists 0; entailer. }
  { entailer. }
  - (* loop body *)
    forward_call (gvar2, gvar0, sh2, sh2, lock_pred gvar3).
    { destruct gvar0; try contradiction; simpl; entailer. }
    simpl; Intro i'.
    forward.
    Exists i'; entailer.
    Exists i'; entailer!.
  - forward_call (gvar1, sh2, tlock_pred sh1 gvar1 gvar0 gvar2 gvar3).
    { destruct gvar1; try contradiction; simpl; entailer. }
    forward_call (gvar1, Ews, Later (tlock_pred sh1 gvar1 gvar0 gvar2 gvar3)).
    { destruct gvar1; try contradiction; simpl; entailer. }
    { subst Frame; instantiate (1 := [lock_inv Ews gvar0 (Interp (lock_pred gvar3));
        cond_var Ews gvar2; Interp (lock_pred gvar3)]); simpl; cancel.
      rewrite selflock_eq at 2.
      rewrite sepcon_assoc, <- (sepcon_assoc (lock_inv _ gvar1 _)), (sepcon_comm (lock_inv _ gvar1 _)).
      repeat rewrite sepcon_assoc; rewrite <- (sepcon_assoc (lock_inv sh2 gvar1 _)).
      apply sepalg.join_comm in Hsh.
      eapply derives_trans.
      { apply sepcon_derives; [apply derives_refl|].
        apply sepcon_derives; [apply derives_refl|].
        apply sepcon_derives; [|apply derives_refl].
        apply sepcon_derives; [apply lock_inv_later | apply derives_refl]. }
      erewrite lock_inv_share_join; eauto; cancel.
      repeat rewrite sepcon_assoc; rewrite <- (sepcon_assoc (lock_inv _ gvar0 _)).
      apply sepalg.join_comm in Hsh.
      erewrite lock_inv_share_join; eauto; cancel.
      erewrite cond_var_share_join; eauto. }
    { split; auto; split.
      + apply later_positive, selflock_positive; simpl.
        apply positive_sepcon2, positive_sepcon1, lock_inv_positive.
      + apply later_rec, selflock_rec. }
    forward_call (gvar0, Ews, lock_pred gvar3).
    { destruct gvar0; try contradiction; simpl; entailer. }
    { split; [auto | apply inv_positive]. }
    forward_call (gvar2, Ews).
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
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons_ext.
{ admit. }
semax_func_cons body_thread_func.
semax_func_cons body_main.
Admitted.
