Require Import VST.floyd.proofauto.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.ghosts.
From VSTlib Require Import spec_locks spec_threads spec_malloc.
Require VSTlib.verif_locks.
Require Import VSTlibtest.incr.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

#[export] Existing Instance verif_locks.M.
#[export] Existing Instance verif_malloc.M.

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition t_counter := Tstruct _counter noattr.

Definition cptr_lock_inv g1 g2 ctr := EX z : Z, field_at Ews t_counter [StructField _ctr] (Vint (Int.repr z)) ctr *
  EX x : Z, EX y : Z, !!(z = x + y) && ghost_var gsh1 x g1 * ghost_var gsh1 y g2.

Definition incr_spec :=
 DECLARE _incr
  WITH sh1 : share, sh : share, h : lock_handle, g1 : gname, g2 : gname, left : bool, n : Z, gv: globals
  PRE [ ]
         PROP  (readable_share sh1)
         PARAMS () GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv g1 g2 (gv _c)); ghost_var gsh2 n (if left then g1 else g2))
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv g1 g2 (gv _c)); ghost_var gsh2 (n+1) (if left then g1 else g2)).

Definition read_spec :=
 DECLARE _read
  WITH sh1 : share, sh : share, h : lock_handle, g1 : gname, g2 : gname, n1 : Z, n2 : Z, gv: globals
  PRE [ ]
         PROP  (readable_share sh1)
         PARAMS () GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv g1 g2 (gv _c)); ghost_var gsh2 n1 g1; ghost_var gsh2 n2 g2)
  POST [ tuint ]
         PROP ()
         RETURN (Vint (Int.repr (n1 + n2)))
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv g1 g2 (gv _c)); ghost_var gsh2 n1 g1; ghost_var gsh2 n2 g2).

Definition thread_lock_R sh1 sh h g1 g2 ctr :=
  field_at sh1 t_counter [StructField _lock] (ptr_of h) ctr * lock_inv sh h (cptr_lock_inv g1 g2 ctr) * ghost_var gsh2 1 g1.

Definition thread_lock_inv sh1 sh h g1 g2 ctr ht :=
  self_part sh ht * thread_lock_R sh1 sh h g1 g2 ctr.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * share * lock_handle * lock_handle * gname * gname * globals
  PRE [ tptr tvoid ]
         let '(sh1, sh, h, ht, g1, g2, gv) := x in
         PROP  (readable_share sh1; ptr_of ht = y)
         PARAMS (y) GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c);
                lock_inv sh h (cptr_lock_inv g1 g2 (gv _c));
                ghost_var gsh2 0 g1;
                lock_inv sh ht (thread_lock_inv sh1 sh h g1 g2 (gv _c) ht))
  POST [ tint ]
         PROP ()
         RETURN (Vint Int.zero)
         SEP ().

Definition compute2_spec :=
 DECLARE _compute2
 WITH gv: globals
 PRE [] PROP() PARAMS() GLOBALS(gv)
          SEP(mem_mgr gv; 
                data_at Ews t_counter (Vint (Int.repr 0), Vundef) (gv _c); 
                has_ext tt)
 POST [ tint ] PROP() RETURN (Vint (Int.repr 2)) 
                    SEP(mem_mgr gv; data_at_ Ews t_counter (gv _c); has_ext tt).

Definition SpawnASI_without_exit := 
    (* it's really a bug in the VSU system that we have to do this *)
    [(threads._spawn, spec_threads.spawn_spec)].

Definition incrImports := LockASI ++ SpawnASI_without_exit.
Definition incrInternals := [incr_spec; read_spec; thread_func_spec; compute2_spec].
Definition Gprog : funspecs :=   incrInternals ++ incrImports.

Lemma ctr_inv_exclusive : forall g1 g2 p,
  exclusive_mpred (cptr_lock_inv g1 g2 p).
Proof.
  intros; unfold cptr_lock_inv.
  eapply derives_exclusive, exclusive_sepcon1 with (Q := EX x : Z, EX y : Z, _),
    field_at__exclusive with (sh := Ews)(t := t_counter); auto; simpl.
  Intro z; apply sepcon_derives; [cancel|].
  Intros x y; Exists x y; apply derives_refl.
  { simpl; lia. }
Qed.
#[export] Hint Resolve ctr_inv_exclusive : core.

Lemma ghost_var_incr : forall g1 g2 x y n (left : bool), ghost_var gsh1 x g1 * ghost_var gsh1 y g2 * ghost_var gsh2 n (if left then g1 else g2) |--
  |==> !!((if left then x else y) = n) && ghost_var gsh1 (n+1) (if left then g1 else g2) * ghost_var gsh2 (n+1) (if left then g1 else g2) * ghost_var gsh1 (if left then y else x) (if left then g2 else g1).
Proof.
  destruct left.
  - eapply derives_trans, bupd_frame_r; cancel.
    rewrite sepcon_andp_prop'; apply ghost_var_update'.
  - eapply derives_trans, bupd_frame_r; cancel.
    rewrite sepcon_andp_prop'; apply ghost_var_update'.
Qed.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  assert_PROP (sh <> Share.bot) by entailer!.
  forward_call (sh, h, cptr_lock_inv g1 g2 (gv _c)).
  unfold cptr_lock_inv at 2. 
Intros z x y.
  forward.
  forward.

  gather_SEP (ghost_var _ x g1) (ghost_var _ y g2) (ghost_var _ n _).
  rewrite sepcon_assoc.
  viewshift_SEP 0 (!!((if left then x else y) = n) &&
    ghost_var gsh1 (n+1) (if left then g1 else g2) *
    ghost_var gsh2 (n+1) (if left then g1 else g2) *
    ghost_var gsh1 (if left then y else x) (if left then g2 else g1)).
  { go_lower.
    eapply derives_trans, bupd_fupd.
    rewrite <- sepcon_assoc; apply ghost_var_incr. }
  Intros.
  forward.
  forward_call release_simple (sh, h, cptr_lock_inv g1 g2 (gv _c)).
  { lock_props.
    unfold cptr_lock_inv; Exists (z + 1).
    unfold Frame; instantiate (1 := [ghost_var gsh2 (n+1) (if left then g1 else g2);
      field_at sh1 t_counter (DOT _lock) (ptr_of h) (gv _c)]); simpl.
    destruct left.
    - Exists (n+1) y; entailer!.
    - Exists x (n+1); entailer!. }
  forward.
  cancel.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward.
  assert_PROP (sh <> Share.bot) by entailer!.
  forward_call (sh, h, cptr_lock_inv g1 g2 (gv _c)).
  unfold cptr_lock_inv at 2.
  Intros z x y.
  forward.
  assert_PROP (x = n1 /\ y = n2) as Heq.
  { sep_apply (ghost_var_inj gsh1 gsh2 x); auto.
    sep_apply (ghost_var_inj gsh1 gsh2 y); auto.
    entailer!. }
  forward.
  forward_call release_simple (sh, h, cptr_lock_inv g1 g2 (gv _c)).
  { lock_props.    
    unfold cptr_lock_inv. Exists z x y. entailer!. }
  destruct Heq; forward; cancel.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  forward_call (sh1, sh, h, g1, g2, true, 0, gv).
  simpl.
  forward_call release_self (sh, ht, thread_lock_R sh1 sh h g1 g2 (gv _c)).
  { unfold thread_lock_inv, thread_lock_R; cancel. }
  forward.
Qed.

Lemma ghost_dealloc:
  forall {A} sh a pp, @ghost_var A sh a pp |-- emp.
Proof.
intros.
unfold ghost_var.
apply own_dealloc.
Qed.

Lemma body_compute2:  semax_body Vprog Gprog f_compute2 compute2_spec.
Proof.
  start_function.
  set (ctr := gv _c).
  forward.
  ghost_alloc (ghost_var Tsh 0).
  Intro g1.
  ghost_alloc (ghost_var Tsh 0).
  Intro g2.
  forward_call (gv, fun _ : lock_handle => cptr_lock_inv g1 g2 ctr).
  Intros lock.
  forward.
  forward.
  forward_call release_simple (Tsh, lock, cptr_lock_inv g1 g2 ctr).
  { lock_props.
    rewrite <- !(ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
    unfold_data_at (data_at _ _ _ _).
    unfold cptr_lock_inv; Exists 0 0 0; entailer!. }
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (gv, fun lockt => thread_lock_inv sh2 gsh2 lock g1 g2 ctr lockt).
  Intros lockt.
  sep_apply lock_inv_isptr; Intros.
  forward_spawn _thread_func (ptr_of lockt) (sh2, gsh2, lock, lockt, g1, g2, gv).
  { erewrite <- lock_inv_share_join; try apply gsh1_gsh2_join; auto.
    erewrite <- (lock_inv_share_join _ _ Tsh); try apply gsh1_gsh2_join; auto.
    erewrite <- field_at_share_join; try apply Hsh; auto.
    subst ctr; entailer!. }
  { simpl; auto. }
  forward_call (sh1, gsh1, lock, g1, g2, false, 0, gv).
  forward_call (gsh1, lockt, thread_lock_inv sh2 gsh2 lock g1 g2 (gv _c) lockt).
  unfold thread_lock_inv at 2; unfold thread_lock_R; Intros.
  simpl.
  forward_call (sh1, gsh1, lock, g1, g2, 1, 1, gv).
  (* We've proved that t is 2! *)
  forward.
  forward_call (gsh1, lock, cptr_lock_inv g1 g2 (gv _c)).
  forward_call freelock_self (gsh1, gsh2, lockt, thread_lock_R sh2 gsh2 lock g1 g2 (gv _c)).
  { unfold thread_lock_inv, selflock; cancel. }
  forward.
  forward_call freelock_simple (lock, cptr_lock_inv g1 g2 (gv _c)).
  { lock_props.
    erewrite <- (lock_inv_share_join _ _ Tsh); try apply gsh1_gsh2_join; auto; subst ctr; cancel. }
  forward.
  unfold_data_at (data_at_ _ _ _).
  simpl.
  unfold cptr_lock_inv. Intros z x y.
  sep_apply (field_at_share_join sh1 sh2 Ews).
  cancel.
  repeat sep_apply (@ghost_dealloc Z).
  cancel.
Qed.

(*

Definition extlink := ext_link_prog prog. (* this is wrong, because
       it doesn't include the programs of all the imported VSUs *)
Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
*)

#[local] Existing Instance NullExtension.Espec.  (* FIXME *)

Require Import VST.floyd.VSU.

Definition IncrVSU: VSU nil incrImports ltac:(QPprog prog) [compute2_spec] (InitGPred (Vardefs (QPprog prog))).
  Proof. 
    mkVSU prog incrInternals.
    - solve_SF_internal body_incr.
    - solve_SF_internal body_read.
    - solve_SF_internal body_thread_func.
    - solve_SF_internal body_compute2.
  Qed.
