Require Import msl.predicates_sl.
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
  rewrite H at 1.
  rewrite later_sepcon, lock_inv_later_eq; auto.
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
     PROP (readable_share sh; precise (Interp R); positive_mpred (Interp R); rec_inv v R)
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
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Gprog : funspecs := augment_funspecs prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; incr_spec; read_spec; thread_func_spec; main_spec].

Lemma precise_sepcon : forall P Q (HP : precise P) (HQ : precise Q), precise (P * Q).
Proof.
  unfold precise; intros ??????? (l1 & r1 & Hjoin1 & HP1 & HQ1) (l2 & r2 & Hjoin2 & HP2 & HQ2)
    Hsub1 Hsub2.
  specialize (HP w _ _ HP1 HP2); specialize (HQ w _ _ HQ1 HQ2).
  rewrite HP, HQ in Hjoin1.
  eapply sepalg.join_eq; eauto.
  - apply sepalg.join_sub_trans with (b := w1); auto.
    eapply sepalg.join_join_sub'; eauto.
  - apply sepalg.join_sub_trans with (b := w2); auto.
    eapply sepalg.join_join_sub'; eauto.
  - apply sepalg.join_sub_trans with (b := w1); auto.
    eapply sepalg.join_join_sub; eauto.
  - apply sepalg.join_sub_trans with (b := w2); auto.
    eapply sepalg.join_join_sub; eauto.
Qed.

Lemma precise_andp1 : forall P Q (HP : precise P), precise (P && Q).
Proof.
  intros ?????? (? & ?) (? & ?) ??; eauto.
Qed.

Lemma precise_andp2 : forall P Q (HQ : precise Q), precise (P && Q).
Proof.
  intros ?????? (? & ?) (? & ?) ??; eauto.
Qed.

Lemma ex_address_mapsto_precise: forall ch rsh sh l,
  precise (EX v : val, res_predicates.address_mapsto ch v rsh sh l).
Proof.
  intros.
  eapply derives_precise, res_predicates.VALspec_range_precise.
  repeat intro.
  destruct H.
  eapply res_predicates.address_mapsto_VALspec_range; eauto.
Qed.

Lemma mapsto_undef_precise : forall sh t b o (Hsh : readable_share sh)
  (Hval : type_is_by_value t = true) (Hvol : type_is_volatile t = false),
  precise (mapsto sh t (Vptr b o) Vundef).
Proof.
  intros; unfold mapsto.
  destruct (access_mode_by_value _ Hval) as (? & Heq); rewrite Heq, Hvol.
  destruct (readable_share_dec _); [|contradiction].
  pose proof (tc_val_Vundef t).
  intros ??? [(? & _) | (_ & HP1)] [(? & _) | (_ & HP2)]; normalize.
  eapply ex_address_mapsto_precise; eauto.
Qed.

Lemma lock_precise : forall sh b o, readable_share sh -> precise (data_at_ sh tlock (Vptr b o)).
Proof.
  intros.
  unfold data_at_, field_at_, field_at, at_offset; simpl.
  apply precise_andp2.
  rewrite data_at_rec_eq; unfold withspacer, at_offset; simpl.
  rewrite data_at_rec_eq; unfold withspacer, at_offset; simpl.
  rewrite data_at_rec_eq; unfold withspacer, at_offset; simpl.
  unfold array_pred, aggregate_pred.array_pred; simpl.
  unfold Zlength, Znth; simpl.
  rewrite data_at_rec_eq; simpl.
  rewrite data_at_rec_eq; simpl.
  apply precise_sepcon; apply precise_andp2; repeat apply precise_sepcon; try apply precise_emp;
    apply mapsto_undef_precise; auto.
Qed.

Lemma ctr_inv_precise : forall b o,
  predicates_sl.precise (EX x : Z, data_at Ews (tarray tint 1) [Vint (Int.repr x)] (Vptr b o)).
Proof.
  intros; apply predicates_sl.derives_precise with (Q := data_at_ Ews (tarray tint 1) (Vptr b o)).
  { intros ? (? & ?).
    apply (data_at_data_at_ _ _ _ _ _ H). }
  unfold data_at_, field_at_, field_at, at_offset; simpl.
  apply precise_andp2.
  rewrite data_at_rec_eq; unfold withspacer, at_offset; simpl.
  unfold array_pred, aggregate_pred.array_pred; simpl.
  unfold Zlength, Znth; simpl.
  apply precise_andp2.
  rewrite data_at_rec_eq; simpl.
  apply precise_sepcon; [apply mapsto_undef_precise | apply precise_emp]; auto.
Qed.

Lemma ctr_inv_positive : forall ctr,
  positive_mpred (EX x : Z, data_at Ews (tarray tint 1) [Vint (Int.repr x)] ctr).
Proof.
Admitted.

Lemma lock_inv_precise : forall v sh R, predicates_sl.precise (lock_inv sh v R).
Proof.
  repeat intro.
  destruct H as (b & o & ? & Hlock).
  admit.
Admitted.

Lemma lock_inv_positive : forall v sh R,
  positive_mpred (lock_inv v sh R).
Proof.
  admit.
Admitted.

Lemma selflock_precise : forall R sh v, predicates_sl.precise R ->
  predicates_sl.precise (selflock R v sh).
Proof.
  intros.
  rewrite selflock_eq.
  apply precise_sepcon; auto.
  apply lock_inv_precise.
Qed.

Lemma positive_sepcon1 : forall P Q (HP : positive_mpred P),
  positive_mpred (P * Q).
Proof.
  repeat intro.
  destruct H as (? & ? & ? & HP1 & ?).
  specialize (HP _ HP1).
  destruct HP as (l & sh & rsh & k & p & HP); exists l, sh, rsh, k, p.
  admit.
Admitted.

Lemma selflock_positive : forall R sh v, positive_mpred R ->
  positive_mpred (selflock R v sh).
Proof.
  intros.
  rewrite selflock_eq.
  apply positive_sepcon1; auto.
Qed.

Lemma later_positive : forall P, positive_mpred P -> positive_mpred (|> P).
Proof.
  admit.
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
  rewrite field_at_isptr; normalize.
  forward_call (lock, sh, lock_pred ctr).
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
  { unfold Frame; instantiate (1 := []); entailer. }
  simpl.
  Intro z.
  forward.
  rewrite data_at_isptr; normalize.
  forward_call (lock, sh, lock_pred ctr).
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
  admit.
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

Lemma emp_almost_empty : forall phi, predicates_hered.app_pred emp phi -> juicy_machine.almost_empty phi.
Proof.
  repeat intro; subst.
(*  Check compcert_rmaps.RML.resource_at_join.*)
  admit.
Admitted.

Lemma prop_almost_empty : forall P phi, predicates_hered.app_pred (prop P) phi -> juicy_machine.almost_empty phi.
Proof.
  admit.
Admitted.

Lemma lock_inv_almost_empty : forall sh v R phi, predicates_hered.app_pred (lock_inv sh v R) phi ->
  juicy_machine.almost_empty phi.
Proof.
  admit.
Admitted.

Lemma almost_empty_join : forall phi1 phi2 phi
  (Hphi1 : juicy_machine.almost_empty phi1)
  (Hphi2 : juicy_machine.almost_empty phi2)
  (Hjoin : sepalg.join phi1 phi2 phi),
  juicy_machine.almost_empty phi.
Proof.
  repeat intro.
  specialize (Hphi1 loc sh psh k P); specialize (Hphi2 loc sh psh k P).
  pose proof (compcert_rmaps.RML.resource_at_join _ _ _ loc Hjoin) as Hsum.
  rewrite H in Hsum.
(*  SearchAbout sepalg.join compcert_rmaps.RML.R.YES.*)
  admit.
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
  rewrite field_at_isptr; normalize.
  forward_call (gvar0, Ews, lock_pred gvar2).
  { subst Frame; instantiate (1 := [data_at_ Ews tlock gvar1]); simpl.
    unfold tlock, semax_conc._lock_t; entailer!.
    Exists 0; entailer!. }
  { destruct gvar2; try contradiction.
    split; auto; split; [apply ctr_inv_precise | apply ctr_inv_positive]. }
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
    Lock_inv sh tlock (thread_lock_pred sh ctr lock tlock)])).
  { entailer.
    Exists _args; entailer.
    Exists (fun x : val * share * val * val => let '(ctr, sh, lock, lockt) := x in
      [(_ctr, ctr); (_ctr_lock, lock); (_thread_lock, lockt)]); simpl; entailer.
    evar (body : funspec); replace (WITH _ : _ PRE [_] _ POST [_] _) with body.
    repeat rewrite sepcon_assoc; apply sepcon_derives; subst body; [apply derives_refl|].
    subst Frame; instantiate (1 := [lock_inv sh2 gvar1 (Interp (thread_lock_pred sh1 gvar2 gvar0 gvar1));
      lock_inv sh2 gvar0 (Interp (lock_pred gvar2))]).
    simpl; entailer.
    repeat rewrite sepcon_assoc; erewrite <- (sepcon_assoc (lock_inv sh1 gvar1 _)), lock_inv_join; eauto.
    cancel.
    repeat rewrite sepcon_assoc; erewrite lock_inv_join; eauto; cancel.
    subst body; f_equal.
    extensionality.
    destruct x as (?, (((?, ?), ?), ?)); simpl.
    f_equal; f_equal.
    unfold SEPx; simpl.
    unfold thread_lock_inv, cptr_lock_inv; normalize. }
  { simpl; intros ? Hpred.
    destruct Hpred as (? & ? & ? & (? & ?) & ? & ? & ? & ? & ? & ? & ? & ? & Hemp).
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
    - apply later_positive, selflock_positive, lock_inv_positive.
    - apply later_rec, selflock_rec. }
  forward_call (gvar0, Ews, lock_pred gvar2).
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
