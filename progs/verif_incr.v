Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
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
  WITH sh : share, g1 : gname, g2 : gname, left : bool, n : Z, gv: globals
  PRE [ ]
         PROP  (readable_share sh)
         LOCAL (gvars gv)
         SEP   (lock_inv sh (gv _ctr_lock) (cptr_lock_inv g1 g2 (gv _ctr)); ghost_var gsh2 n (if left then g1 else g2))
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (lock_inv sh (gv _ctr_lock) (cptr_lock_inv g1 g2 (gv _ctr)); ghost_var gsh2 (n+1) (if left then g1 else g2)).

Definition read_spec :=
 DECLARE _read
  WITH sh : share, g1 : gname, g2 : gname, n1 : Z, n2 : Z, gv: globals
  PRE [ ]
         PROP  (readable_share sh)
         LOCAL (gvars gv)
         SEP   (lock_inv sh (gv _ctr_lock) (cptr_lock_inv g1 g2 (gv _ctr)); ghost_var gsh2 n1 g1; ghost_var gsh2 n2 g2)
  POST [ tuint ]
         PROP ()
         LOCAL (temp ret_temp (Vint (Int.repr (n1 + n2))))
         SEP (lock_inv sh (gv _ctr_lock) (cptr_lock_inv g1 g2 (gv _ctr)); ghost_var gsh2 n1 g1; ghost_var gsh2 n2 g2).

Definition thread_lock_R sh g1 g2 ctr lockc :=
  lock_inv sh lockc (cptr_lock_inv g1 g2 ctr) * ghost_var gsh2 1 g1.

Definition thread_lock_inv sh g1 g2 ctr lockc lockt :=
  selflock (thread_lock_R sh g1 g2 ctr lockc) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * gname * gname * globals
  PRE [ _args OF (tptr tvoid) ]
         let '(sh, g1, g2, gv) := x in
         PROP  (readable_share sh)
         LOCAL (temp _args y; gvars gv)
         SEP   (lock_inv sh (gv _ctr_lock) (cptr_lock_inv g1 g2 (gv _ctr));
                ghost_var gsh2 0 g1;
                lock_inv sh (gv _thread_lock) (thread_lock_inv sh g1 g2 (gv _ctr) (gv _ctr_lock) (gv _thread_lock)))
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

Lemma ctr_inv_exclusive : forall g1 g2 p,
  exclusive_mpred (cptr_lock_inv g1 g2 p).
Proof.
  intros; unfold cptr_lock_inv.
  eapply derives_exclusive, exclusive_sepcon1 with (Q := EX x : Z, EX y : Z, _),
    data_at__exclusive with (sh := Ews)(t := tuint); auto; simpl; try omega.
  Intro z; apply sepcon_derives; [cancel|].
  Intros x y; Exists x y; apply derives_refl.
Qed.
Hint Resolve ctr_inv_exclusive.

Lemma thread_inv_exclusive : forall sh g1 g2 ctr lock lockt,
  exclusive_mpred (thread_lock_inv sh g1 g2 ctr lock lockt).
Proof.
  intros; apply selflock_exclusive.
  unfold thread_lock_R.
  apply exclusive_sepcon1; auto.
Qed.
Hint Resolve thread_inv_exclusive.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (gv _ctr_lock, sh, cptr_lock_inv g1 g2 (gv _ctr)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z x y.
  forward.
  forward.
  gather_SEP 2 3 4.
  viewshift_SEP 0 (!!((if left then x else y) = n) && ghost_var Tsh (n+1) (if left then g1 else g2) *
    ghost_var gsh1 (if left then y else x) (if left then g2 else g1)).
  { go_lower.
    destruct left.
    - rewrite (sepcon_comm _ (ghost_var _ _ _)), <- sepcon_assoc.
      erewrite ghost_var_share_join' by eauto.
      Intros; rewrite prop_true_andp by auto; eapply derives_trans, bupd_frame_r; cancel.
      apply ghost_var_update.
    - erewrite ghost_var_share_join' by eauto.
      Intros; rewrite prop_true_andp by auto; eapply derives_trans, bupd_frame_r; cancel.
      apply ghost_var_update. }
  Intros; forward_call (gv _ctr_lock, sh, cptr_lock_inv g1 g2 (gv _ctr)).
  { lock_props.
    unfold cptr_lock_inv; Exists (z + 1).
    erewrite <- ghost_var_share_join by eauto.
    unfold Frame; instantiate (1 := [ghost_var gsh2 (n+1) (if left then g1 else g2)]); simpl.
    destruct left.
    - Exists (n+1) y; entailer!.
    - Exists x (n+1); entailer!. }
  forward.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward_call (gv _ctr_lock, sh, cptr_lock_inv g1 g2 (gv _ctr)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z x y.
  forward.
  assert_PROP (x = n1 /\ y = n2) as Heq.
  { gather_SEP 2 4.
    erewrite ghost_var_share_join' by eauto.
    gather_SEP 3 4.
    erewrite ghost_var_share_join' by eauto.
    entailer!. }
  forward_call (gv _ctr_lock, sh, cptr_lock_inv g1 g2 (gv _ctr)).
  { lock_props.
    unfold cptr_lock_inv; Exists z x y; entailer!. }
  destruct Heq; forward.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (sh, g1, g2, true, 0, gv).
  simpl.
  forward_call ((gv _thread_lock), sh, thread_lock_R sh g1 g2 (gv _ctr) (gv _ctr_lock), thread_lock_inv sh g1 g2 (gv _ctr) (gv _ctr_lock) (gv _thread_lock)).
  { lock_props.
    unfold thread_lock_inv, thread_lock_R.
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
  start_function.
  set (ctr := gv _ctr); set (lockt := gv _thread_lock); set (lock := gv _ctr_lock).
  forward.
  forward.
  forward.
  ghost_alloc (ghost_var Tsh 0).
  Intro g1.
  ghost_alloc (ghost_var Tsh 0).
  Intro g2.
  forward_call (lock, Ews, cptr_lock_inv g1 g2 ctr).
  { rewrite sepcon_comm; apply sepcon_derives; [apply derives_refl | cancel]. }
  forward_call (lock, Ews, cptr_lock_inv g1 g2 ctr).
  { lock_props.
    rewrite <- !(ghost_var_share_join gsh1 gsh2 Tsh) by auto.
    unfold cptr_lock_inv; Exists 0 0 0; entailer!. }
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (lockt, Ews, thread_lock_inv sh1 g1 g2 ctr lock lockt).
  { rewrite sepcon_comm; apply sepcon_derives; [apply derives_refl | cancel]. }
  forward_spawn _thread_func nullval (sh1, g1, g2, gv).
  { erewrite <- lock_inv_share_join; try apply Hsh; auto.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto.
    entailer!. }
  forward_call (sh2, g1, g2, false, 0, gv).
  simpl.
  forward_call (lockt, sh2, thread_lock_inv sh1 g1 g2 ctr lock lockt).
  unfold thread_lock_inv at 2; unfold thread_lock_R.
  rewrite selflock_eq.
  Intros.
  forward_call (sh2, g1, g2, 1, 1, gv).
  (* We've proved that t is 2! *)
  forward_call (lock, sh2, cptr_lock_inv g1 g2 ctr).
  forward_call (lockt, Ews, sh1, thread_lock_R sh1 g1 g2 ctr lock, thread_lock_inv sh1 g1 g2 ctr lock lockt).
  { lock_props.
    unfold thread_lock_inv, thread_lock_R.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel. }
  forward_call (lock, Ews, cptr_lock_inv g1 g2 ctr).
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
