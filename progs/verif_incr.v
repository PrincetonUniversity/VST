Require Import floyd.proofauto.
Require Import concurrency.semax_conc.
Require Import progs.incr.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn_thread spawn_spec.

Definition rec_inv v R := exists Q sh, Interp R = (Q * lock_inv sh v (Interp (Later R))).

Lemma selflock_rec : forall sh v R, rec_inv v (Self_lock R sh v).
Proof.
  intros; unfold rec_inv.
  exists (Interp R), sh; simpl.
  apply selflock_eq.
Qed.

Lemma lock_inv_later_eq : forall sh v R, |> lock_inv sh v R = lock_inv sh v (|> R).
Proof.
Admitted.

Lemma later_rec : forall v R, rec_inv v R -> rec_inv v (Later R).
Proof.
  unfold rec_inv; intros.
  destruct H as (Q & sh & H); exists (|> Q), sh; simpl.
  rewrite H at 1; rewrite later_sepcon, lock_inv_later_eq; auto.
Qed.

Definition freelock2_spec :=
  DECLARE _freelock2
   WITH v : val, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (positive_mpred (Interp R); rec_inv v R)
     LOCAL (temp _lock v)  
     SEP (lock_inv Ews v (Interp R))
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (data_at_ Ews tlock v).

Definition release2_spec :=
  DECLARE _release2
   WITH v : val, sh : share, R : Pred
   PRE [ _lock OF tptr tlock ]
     PROP (readable_share sh; predicates_sl.precise (Interp R); positive_mpred (Interp R); rec_inv v R)
     LOCAL (temp _lock v)
     SEP (Interp R)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (emp).

Definition cptr_lock_inv lock sh ctr := lock_inv sh lock
  (EX z : Z, data_at Ews (tarray tint 1) [Vint (Int.repr z)] ctr).
Definition lock_pred ctr :=
  Exp _ (fun z => Data_at _ Ews (tarray tint 1) [Vint (Int.repr z)] ctr).

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
  WITH ctr : val, sh : share, lock : val, lockt : val
  PRE [ _args OF (tptr tvoid) ]
         PROP  (readable_share sh)
         LOCAL (gvar _ctr ctr; gvar _ctr_lock lock; gvar _thread_lock lockt)
         SEP   (cptr_lock_inv lock sh ctr; thread_lock_inv sh ctr lock lockt)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (emp).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Gprog : funspecs := augment_funspecs prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; incr_spec; read_spec; thread_func_spec; main_spec].

Lemma data_at_precise : forall sh t v, predicates_sl.precise (data_at_ sh t v).
Proof.
  intros; apply predicates_sl.derives_precise with
    (Q := at_offset (data_at_rec sh t (default_val t)) 0 v).
  - repeat intro.
    destruct H; auto.
  - unfold at_offset.
    intros ??? HP1 HP2 (b1 & Hw1) (b2 & Hw2).
    admit.
Admitted.

Lemma lock_inv_precise : forall ctr,
  predicates_sl.precise (EX x : Z, data_at Ews (tarray tint 1) [Vint (Int.repr x)] ctr).
Proof.
  intros; eapply predicates_sl.derives_precise; [|apply data_at_precise].
  repeat intro.
  destruct H.
  destruct H.
  unfold data_at_, field_at_, field_at; simpl in *.
  split; [eassumption|].
  unfold default_val; simpl.
  instantiate (1 := Ews).
  admit.
Admitted.

Lemma lock_inv_positive : forall ctr,
  positive_mpred (EX x : Z, data_at Ews (tarray tint 1) [Vint (Int.repr x)] ctr).
Proof.
  repeat intro.
  unfold compcert_rmaps.RML.R.resource_at.
  unfold compcert_rmaps.RML.R.unsquash.
  destruct H.
Admitted.

Lemma lock_inv_precise' : forall v sh R,
  predicates_sl.precise (lock_inv v sh R).
Proof.
  admit.
Admitted.

Lemma lock_inv_positive' : forall v sh R,
  positive_mpred (lock_inv v sh R).
Proof.
  admit.
Admitted.

Lemma selflock_precise : forall R sh v, predicates_sl.precise R ->
  predicates_sl.precise (selflock R v sh).
Proof.
Admitted.

Lemma selflock_positive : forall R sh v, positive_mpred R ->
  positive_mpred (selflock R v sh).
Proof.
Admitted.

Lemma later_positive : forall P, positive_mpred P -> positive_mpred (|> P).
Proof.
Admitted.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (lock, sh, lock_pred ctr).
  { unfold Frame; instantiate (1 := []); entailer. }
  simpl.
  Intro z.
  forward.
  forward.
  forward_call (lock, sh, lock_pred ctr).
  { simpl; unfold Frame; instantiate (1 := []); entailer.
    Exists (z + 1); entailer. }
  { split; auto; simpl; split; [apply lock_inv_precise | apply lock_inv_positive]. }
  forward.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward_call (lock, sh, lock_pred ctr).
  { unfold Frame; instantiate (1 := []); entailer. }
  simpl.
  Intro z.
  forward.
  forward_call (lock, sh, lock_pred ctr).
  { simpl; unfold Frame; instantiate (1 := []); entailer.
    Exists z; entailer. }
  { split; auto; simpl; split; [apply lock_inv_precise | apply lock_inv_positive]. }
  forward.
  Exists z; entailer.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  forward.
  forward_call (ctr, sh, lock).
  forward_call (lockt, sh, Self_lock (Lock_inv sh lock (lock_pred ctr)) sh lockt).
  { subst Frame; instantiate (1 := []).
    unfold thread_lock_inv, cptr_lock_inv; simpl.
    rewrite selflock_eq at 2; entailer!.
    apply lock_inv_later. }
  { split; auto; simpl; split; [|split].
    - apply selflock_precise, lock_inv_precise'.
    - apply selflock_positive, lock_inv_positive'.
    - apply selflock_rec. }
  forward.
Qed.

Lemma semax_fun_id'' id f Espec {cs} Delta P Q R Post c :
  (var_types Delta) ! id = None ->
  (glob_specs Delta) ! id = Some f ->
  (glob_types Delta) ! id = Some (type_of_funspec f) ->
  @semax cs Espec Delta
    (EX v : val, PROPx P
      (LOCALx (gvar id v :: Q)
      (SEPx ((func_ptr' f v) :: R)))) c Post ->
  @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c Post.
Proof.
intros V G GS SA.
apply (semax_fun_id id f Delta); auto.
eapply semax_pre_post; try apply SA; [ clear SA |
  intros; simpl; unfold local, lift1; entailer! ].
go_lowerx.
apply exp_right with (eval_var id (type_of_funspec f) rho).
entailer.
apply andp_right.
- (* about gvar *)
  apply prop_right.
  unfold gvar_denote, eval_var, Map.get.
  destruct H as (_ & _ & DG & DS).
  destruct (DS id _ GS) as [-> | (t & E)]; [ | congruence].
  destruct (DG id _ GS) as (? & -> & ?); auto.
- (* about func_ptr/func_ptr' *)
  unfold func_ptr'.
  rewrite <- andp_left_corable, andp_comm; auto.
  apply corable_func_ptr.
Qed.

Ltac get_global_function'' _f :=
eapply (semax_fun_id'' _f); try reflexivity.

Lemma lock_inv_join : forall sh1 sh2 sh v R (Hjoin : sepalg.join sh1 sh2 sh),
  lock_inv sh1 v R * lock_inv sh2 v R = lock_inv sh v R.
Proof.
  intros; unfold lock_inv.
  unfold res_predicates.LKspec.
Admitted.

Lemma split_readable_share sh :
  readable_share sh ->
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 sh.
Admitted.

Lemma split_Ews :
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 Ews.
Proof.
  apply split_readable_share; auto.
Qed.

Lemma lock_inv_almost_empty : forall sh v R phi, predicates_hered.app_pred (lock_inv sh v R) phi ->
  juicy_machine.almost_empty phi.
Proof.
Admitted.

Lemma emp_almost_empty : forall phi, predicates_hered.app_pred emp phi -> juicy_machine.almost_empty phi.
Proof.
Admitted.

Lemma prop_almost_empty : forall P phi, predicates_hered.app_pred (prop P) phi -> juicy_machine.almost_empty phi.
Proof.
Admitted.

Lemma almost_empty_join : forall phi1 phi2 phi, juicy_machine.almost_empty phi1 ->
  juicy_machine.almost_empty phi2 ->
  sepalg.join phi1 phi2 phi -> juicy_machine.almost_empty phi.
Proof.
Admitted.

Definition thread_lock_pred' sh ctr lockc lockt := Later (Self_lock (Lock_inv sh lockc (lock_pred ctr)) sh lockt).

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
  change (globvars2pred nil) with (@emp (environ->mpred) _ _).
  repeat rewrite sepcon_emp.
  forward.
  unfold default_val, upd_Znth, Zlength; simpl.
  rewrite sublist_nil.
  forward.
  forward.
  forward_call (gvar0, Ews, lock_pred gvar2).
  { unfold tlock, semax_conc._lock_t; entailer!. }
  forward_call (gvar0, Ews, lock_pred gvar2).
  { subst Frame; instantiate (1 := [data_at_ Ews tlock gvar1]); simpl.
    unfold tlock, semax_conc._lock_t; entailer!.
    Exists 0; entailer!. }
  { split; auto; split; [apply lock_inv_precise | apply lock_inv_positive]. }
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (gvar1, Ews, thread_lock_pred sh1 gvar2 gvar0 gvar1).
  get_global_function'' _thread_func.
  normalize.
  apply extract_exists_pre; intros f_.
  forward_call (f_, Vint (Int.repr 0), existT (fun ty => ty * (ty -> val -> Pred))%type
   (val * share * val * val)%type ((gvar2, sh1, gvar0, gvar1),
   fun (x : (val * share * val * val)) (_ : val) => let '(ctr, sh, lock, tlock) := x in
     Pred_list [Pred_prop (readable_share sh); Lock_inv sh lock (lock_pred ctr);
    Lock_inv sh tlock (thread_lock_pred sh gvar2 gvar0 gvar1)])).
  { entailer.
    Exists _args; entailer.
    Exists ([(_ctr, gvar2); (_ctr_lock, gvar0); (_thread_lock, gvar1)]); entailer.
    subst Frame; instantiate (1 := [lock_inv sh2 gvar1 (Interp (thread_lock_pred sh1 gvar2 gvar0 gvar1));
      lock_inv sh2 gvar0 (Interp (lock_pred gvar2))]).
    simpl; entailer.
    repeat rewrite sepcon_assoc; erewrite <- (sepcon_assoc (lock_inv sh1 gvar1 _)), lock_inv_join; eauto.
    cancel.
    repeat rewrite sepcon_assoc; erewrite lock_inv_join; eauto; cancel.
    admit. (* Can we move derives inside func_ptr? *) }
  { simpl; intros ? Hpred.
    destruct Hpred as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & Hemp).
    eapply almost_empty_join; eauto; [|eapply almost_empty_join; eauto; [|eapply almost_empty_join; eauto]].
    - eapply prop_almost_empty; eauto.
    - eapply lock_inv_almost_empty; eauto.
    - eapply lock_inv_almost_empty; eauto.
    - eapply emp_almost_empty; eauto. }
  forward_call (gvar2, sh2, gvar0).
  { subst Frame; instantiate (1 := [lock_inv sh2 gvar1 (Interp (thread_lock_pred sh1 gvar2 gvar0 gvar1))]); simpl.
    unfold cptr_lock_inv; entailer!. }
  forward_call (gvar1, sh2, thread_lock_pred sh1 gvar2 gvar0 gvar1).
  forward_call (gvar2, sh2, gvar0).
  Intro z.
  forward_call (gvar0, sh2, lock_pred gvar2).
  { unfold cptr_lock_inv; simpl; entailer!. }
  forward_call (gvar1, thread_lock_pred' sh1 gvar2 gvar0 gvar1).
  { subst Frame; instantiate (1 := [cptr_lock_inv gvar0 Ews gvar2; Interp (lock_pred gvar2)]); simpl; cancel.
    rewrite selflock_eq at 2.
    rewrite sepcon_assoc, <- (sepcon_assoc (lock_inv _ gvar1 _)), (sepcon_comm (lock_inv _ gvar1 _)).
    apply sepalg.join_comm in Hsh.
    unfold cptr_lock_inv.
    repeat rewrite <- sepcon_assoc; erewrite lock_inv_join; eauto; cancel.
    eapply derives_trans.
    { apply sepcon_derives; [apply lock_inv_later | apply derives_refl]. }
    erewrite lock_inv_join; eauto; unfold rec_inv; entailer. }
  { split.
    - apply later_positive, selflock_positive, lock_inv_positive'.
    - apply later_rec, selflock_rec. }
  forward_call (gvar0, Ews, lock_pred gvar2).
  { unfold cptr_lock_inv; simpl; entailer!. }
  { split; [auto | apply lock_inv_positive]. }
  forward.
Admitted.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | ]).
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
semax_func_cons body_incr.
semax_func_cons body_read.
semax_func_cons body_thread_func.
semax_func_cons body_main.
Admitted.
