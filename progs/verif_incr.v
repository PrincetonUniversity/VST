Require Import VST.progs.conclib.
Require Import VST.progs.ghost.
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

Definition cptr_lock_inv g1 g2 ctr := EX z : Z, data_at Ews tuint (Vint (Int.repr z)) ctr *
  EX x : Z, EX y : Z, !!(z = x + y) && ghost_var gsh1 x g1 * ghost_var gsh1 y g2.

Definition incr_spec :=
 DECLARE _incr
  WITH ctr : val, sh : share, lock : val, g1 : gname, g2 : gname, left : bool
  PRE [ ]
         PROP  (readable_share sh)
         LOCAL (gvar _ctr ctr; gvar _ctr_lock lock)
         SEP   (lock_inv sh lock (cptr_lock_inv g1 g2 ctr); ghost_var gsh2 0 (if left then g1 else g2))
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (lock_inv sh lock (cptr_lock_inv g1 g2 ctr); ghost_var gsh2 1 (if left then g1 else g2)).

Definition read_spec :=
 DECLARE _read
  WITH ctr : val, sh : share, lock : val, g1 : gname, g2 : gname, n1 : Z, n2 : Z
  PRE [ ]
         PROP  (readable_share sh)
         LOCAL (gvar _ctr ctr; gvar _ctr_lock lock)
         SEP   (lock_inv sh lock (cptr_lock_inv g1 g2 ctr); ghost_var gsh2 n1 g1; ghost_var gsh2 n2 g2)
  POST [ tuint ]
         PROP ()
         LOCAL (temp ret_temp (Vint (Int.repr (n1 + n2))))
         SEP (lock_inv sh lock (cptr_lock_inv g1 g2 ctr); ghost_var gsh2 n1 g1; ghost_var gsh2 n2 g2).

Definition thread_lock_R sh g1 g2 ctr lockc :=
  lock_inv sh lockc (cptr_lock_inv g1 g2 ctr) * ghost_var gsh2 1 g1.

Definition thread_lock_inv sh g1 g2 ctr lockc lockt :=
  selflock (thread_lock_R sh g1 g2 ctr lockc) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : val * share * val * val * gname * gname
  PRE [ _args OF (tptr tvoid) ]
         let '(ctr, sh, lock, lockt, g1, g2) := x in
         PROP  ()
         LOCAL (temp _args y; gvar _ctr ctr; gvar _ctr_lock lock; gvar _thread_lock lockt)
         SEP   ((!!readable_share sh && emp); lock_inv sh lock (cptr_lock_inv g1 g2 ctr);
                ghost_var gsh2 0 g1;
                lock_inv sh lockt (thread_lock_inv sh g1 g2 ctr lock lockt))
  POST [ tptr tvoid ]
         PROP ()
         LOCAL ()
         SEP ().

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; incr_spec; read_spec; thread_func_spec; main_spec]).

Lemma ctr_inv_precise : forall g1 g2 p,
  precise (cptr_lock_inv g1 g2 p).
Proof.
Admitted.
Hint Resolve ctr_inv_precise.

Lemma ctr_inv_positive : forall g1 g2 ctr,
  positive_mpred (cptr_lock_inv g1 g2 ctr).
Proof.
  intros; unfold cptr_lock_inv.
  apply ex_positive; intro.
  apply positive_sepcon1; auto.
Qed.
Hint Resolve ctr_inv_positive.

Lemma thread_inv_precise : forall sh g1 g2 ctr lock lockt,
  precise (thread_lock_inv sh g1 g2 ctr lock lockt).
Proof.
  intros; apply selflock_precise, precise_sepcon; auto.
Admitted.
Hint Resolve thread_inv_precise.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (lock, sh, cptr_lock_inv g1 g2 ctr).
  unfold cptr_lock_inv at 2; simpl.
  Intros z x y.
  forward.
  forward.
  (* It would be nice to have a version of replace_SEP for view shift. *)
  gather_SEP 2 3 4.
  match goal with |-semax _ (PROPx _ (LOCALx ?Q (SEPx (_ :: ?R)))) _ _ =>
    apply (semax_pre_bupd (PROP () (LOCALx Q
      (SEPx (!!((if left then x else y) = 0) && ghost_var Tsh 1 (if left then g1 else g2) ::
             ghost_var gsh1 (if left then y else x) (if left then g2 else g1) :: R))))) end.
  { go_lower.
    rewrite !prop_true_andp by auto.
    rewrite <- 3sepcon_assoc.
    eapply derives_trans; [|apply bupd_frame_r]; cancel.
    destruct left.
    - erewrite sepcon_assoc, sepcon_comm, sepcon_assoc, ghost_var_share_join' by (try apply sepalg.join_comm; eauto).
      Intros; rewrite prop_true_andp by auto; eapply derives_trans, bupd_frame_r; cancel.
      apply ghost_var_update.
    - erewrite sepcon_assoc, ghost_var_share_join'; eauto.
      Intros; rewrite prop_true_andp by auto; eapply derives_trans, bupd_frame_r; cancel.
      apply ghost_var_update. }
  Intros; forward_call (lock, sh, cptr_lock_inv g1 g2 ctr).
  { lock_props.
    unfold cptr_lock_inv; Exists (z + 1).
    erewrite <- ghost_var_share_join by eauto.
    unfold Frame; instantiate (1 := [ghost_var gsh2 1 (if left then g1 else g2)]); simpl.
    destruct left.
    - Exists 1 y; entailer!.
    - Exists x 1; entailer!. }
  forward.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward_call (lock, sh, cptr_lock_inv g1 g2 ctr).
  unfold cptr_lock_inv at 2; simpl.
  Intros z x y.
  forward.
  assert_PROP (x = n1 /\ y = n2) as Heq.
  { go_lower.
    rewrite <- sepcon_assoc, sepcon_comm; apply sepcon_derives_prop.
    rewrite <- sepcon_prop_prop; eapply derives_trans; [|apply sepcon_derives; apply ghost_var_inj].
    rewrite !sepcon_assoc; apply sepcon_derives; [apply derives_refl|].
    rewrite <- sepcon_assoc, (sepcon_comm (ghost_var gsh1 y g2)), sepcon_assoc; apply derives_refl.
    all: auto. }
  forward_call (lock, sh, cptr_lock_inv g1 g2 ctr).
  { lock_props.
    unfold cptr_lock_inv; Exists z x y; entailer!. }
  destruct Heq; forward.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (ctr, sh, lock, g1, g2, true).
  forward_call (lockt, sh, thread_lock_R sh g1 g2 ctr lock, thread_lock_inv sh g1 g2 ctr lock lockt).
  { unfold thread_lock_inv; lock_props.
    { apply thread_inv_precise. }
    rewrite selflock_eq at 2; unfold thread_lock_R; cancel.
    eapply derives_trans; [apply lock_inv_later | cancel]. }
  forward.
Qed.

Lemma lock_struct : forall p, data_at_ Ews (Tstruct _lock_t noattr) p |-- data_at_ Ews tlock p.
Proof.
  intros.
  unfold data_at_, field_at_; unfold_field_at 1%nat.
  unfold field_at; simpl.
  rewrite field_compatible_cons; simpl; entailer.
  (* temporarily broken *)
Admitted.

Lemma thread_ghost : forall sh g1 g2 ctr lock lockt,
  thread_lock_inv sh g1 g2 ctr lock lockt =
  ghost_var gsh2 1 g1 * (ghost_var gsh2 1 g1 -* thread_lock_inv sh g1 g2 ctr lock lockt).
Proof.
  intros; eapply wand_eq.
  unfold thread_lock_inv, thread_lock_R.
  rewrite selflock_eq.
  rewrite (sepcon_comm _ (ghost_var _ _ _)), sepcon_assoc; eauto.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  name ctr _ctr; name lockt _thread_lock; name lock _ctr_lock.
  start_function.
  (* How should we get the initial inG's? *)
  match goal with |-semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    apply (semax_pre (PROPx P (LOCALx Q (SEPx (inG (@pos_PCM (discrete_PCM Z)) :: R))))); [admit|] end.
  forward.
  forward.
  forward.
  ghost_alloc (ghost_var Tsh 0).
  Intro g1.
  ghost_alloc (ghost_var Tsh 0).
  Intro g2.
  forward_call (lock, Ews, cptr_lock_inv g1 g2 ctr).
  { rewrite (sepcon_comm _ (fold_right_sepcon _)); apply sepcon_derives; [cancel | apply lock_struct]. }
  forward_call (lock, Ews, cptr_lock_inv g1 g2 ctr).
  { lock_props.
    rewrite <- !(ghost_var_share_join gsh1 gsh2 Tsh) by auto.
    unfold cptr_lock_inv; Exists 0 0 0; entailer!. }
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (lockt, Ews, thread_lock_inv sh1 g1 g2 ctr lock lockt).
  { rewrite (sepcon_comm _ (fold_right_sepcon _)); apply sepcon_derives; [cancel | apply lock_struct]. }
  get_global_function'' _thread_func.
  apply extract_exists_pre; intros f_.
  forward_spawn (val * share * val * val * gname * gname)%type (f_, Vint (Int.repr 0),
    fun x : val * share * val * val * gname * gname => let '(ctr, sh, lock, lockt, g1, g2) := x in
      [(_ctr, ctr); (_ctr_lock, lock); (_thread_lock, lockt)], (ctr, sh1, lock, lockt, g1, g2),
    fun (x : (val * share * val * val * gname * gname)) (_ : val) => let '(ctr, sh, lock, lockt, g1, g2) := x in
         !!readable_share sh && emp * lock_inv sh lock (cptr_lock_inv g1 g2 ctr) *
         ghost_var gsh2 0 g1 *
         lock_inv sh lockt (thread_lock_inv sh g1 g2 ctr lock lockt)).
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
  forward_call (ctr, sh2, lock, g1, g2, false).
  forward_call (lockt, sh2, thread_lock_inv sh1 g1 g2 ctr lock lockt).
  rewrite thread_ghost at 2.
  forward_call (ctr, sh2, lock, g1, g2, 1, 1).
  gather_SEP 1 4; rewrite <- thread_ghost.
  (* We've proved that t is 2! *)
  forward_call (lock, sh2, cptr_lock_inv g1 g2 ctr).
  forward_call (lockt, Ews, sh1, |>thread_lock_R sh1 g1 g2 ctr lock, |>thread_lock_inv sh1 g1 g2 ctr lock lockt).
  { unfold thread_lock_inv; lock_props.
    - apply later_positive; auto.
    - unfold rec_inv.
      rewrite selflock_eq at 1.
      rewrite later_sepcon; f_equal.
      apply lock_inv_later_eq.
    - rewrite selflock_eq at 1.
      erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel.
      rewrite sepcon_comm, <- !sepcon_assoc, sepcon_comm.
      apply sepcon_derives; [apply lock_inv_later | cancel]. }
  forward_call (lock, Ews, cptr_lock_inv g1 g2 ctr).
  { lock_props.
    unfold thread_lock_R.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel. }
  forward.
Admitted.

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
