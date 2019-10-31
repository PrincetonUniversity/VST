Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.progs.incr.
Require Import VST.progs.invariants.
Require Import VST.progs.fupd.
Require Import VST.atomics.general_locks.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock makelock_spec.
Definition freelock_spec := DECLARE _freelock freelock_spec.
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.

Definition ctr_state ctr n := data_at Ews tuint (Vint (Int.repr (Z.of_nat n))) ctr.

Definition ctr_inv lock ctr g (n : nat) := lock_inv' lock g n (ctr_state ctr).

Program Definition incr_spec :=
 DECLARE _incr
  ATOMIC TYPE (rmaps.ConstType (_ * _)) OBJ n INVS empty top
  WITH g : gname, gv : globals
  PRE [ ]
         PROP  ()
         LOCAL (gvars gv)
         SEPS   (seplog.emp) | (ctr_inv (gv _ctr_lock) (gv _ctr) g n)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (ctr_inv (gv _ctr_lock) (gv _ctr) g (n + 1)).

Program Definition read_spec :=
 DECLARE _read
  ATOMIC TYPE (rmaps.ConstType (_ * _)) OBJ n INVS empty top
  WITH g : gname, gv : globals
  PRE [ ]
         PROP  ()
         LOCAL (gvars gv)
         SEPS   (seplog.emp) | (ctr_inv (gv _ctr_lock) (gv _ctr) g n)
  POST [ tuint ]
    EX n' : nat,
         PROP ()
         LOCAL (temp ret_temp (Vint (Int.repr (Z.of_nat n'))))
         SEP (!!(n' = n) && ctr_inv (gv _ctr_lock) (gv _ctr) g n).

Definition cptr_lock_inv g g1 g2 ctr lockc :=
  EX x y : nat, ghost_var gsh1 x g1 * ghost_var gsh1 y g2 * ctr_inv lockc ctr g (x + y)%nat.

Definition thread_lock_R {inv_names : invG} i g g1 g2 ctr lockc :=
  invariant i (cptr_lock_inv g g1 g2 ctr lockc) * ghost_var gsh2 1 g1.

Definition thread_lock_inv {inv_names : invG} sh i g g1 g2 ctr lockc lockt :=
  selflock (thread_lock_R i g g1 g2 ctr lockc) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : iname * share * gname * gname * gname * globals * invG
  PRE [ _args OF (tptr tvoid) ]
         let '(i, sh, g, g1, g2, gv, inv_names) := x in
         PROP  (readable_share sh)
         LOCAL (temp _args y; gvars gv)
         SEP   (invariant i (cptr_lock_inv g g1 g2 (gv _ctr) (gv _ctr_lock));
                ghost_var gsh2 0 g1;
                lock_inv sh (gv _thread_lock) (thread_lock_inv sh i g g1 g2 (gv _ctr) (gv _ctr_lock) (gv _thread_lock)))
  POST [ tptr tvoid ]
         PROP ()
         LOCAL ()
         SEP (). (* really the thread lock invariant is the postcondition of the spawned thread *)

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [ ] main_pre prog nil gv
  POST [ tint ] main_post prog nil gv.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; incr_spec; read_spec; thread_func_spec; main_spec]).

Lemma thread_inv_exclusive : forall {inv_names : invG} i sh g g1 g2 ctr lock lockt, sh <> Share.bot ->
  exclusive_mpred (thread_lock_inv sh i g g1 g2 ctr lock lockt).
Proof.
  intros; apply selflock_exclusive.
  unfold thread_lock_R.
  apply exclusive_sepcon2, ghost_var_exclusive; auto.
Qed.
Hint Resolve thread_inv_exclusive.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  unfold atomic_shift; Intros P.
  set (AS := _ -* _).
  forward.
  sep_apply cored_dup.
  forward_call (@acquire_sub nat) (gv _ctr_lock, g, ctr_state (gv _ctr), |> P * EX n : nat, data_at Ews tuint (vint (Z.of_nat n)) (gv _ctr) * ghost_reference(P := discrete_PCM nat) g n, inv_names).
  { rewrite -> sepcon_comm, <- sepcon_assoc; apply sepcon_derives; [|cancel].
    unfold atomic_shift; Exists P; cancel.
    apply andp_derives; auto.
    iIntros "AS P"; iMod ("AS" with "P") as (z) "[ctr Hclose]"; unfold ctr_inv.
    iIntros "!>"; iExists z; iFrame.
    iSplit; first by iApply (bi.and_elim_l with "Hclose").
    iIntros (_) "[l (? & ctr & _)]"; simpl.
    iMod ("Hclose" with "l"); iFrame.
    iExists z; unfold ctr_state; iFrame.
    iMod (timeless with "ctr"); last by iFrame.
    { apply data_at_timeless. } }
  Intros n.
  forward.
  forward.
  rewrite add_repr.
  forward_call (@release_sub nat) (gv _ctr_lock, g, n, (n + 1)%nat, ctr_state (gv _ctr), Q, inv_names).
  { subst Frame; instantiate (1 := nil); simpl.
    unfold ctr_state; rewrite Nat2Z.inj_add; simpl; cancel.
    unfold atomic_shift. Exists P; cancel.
    apply andp_derives; auto.
    iIntros "AS P"; iMod ("AS" with "P") as (z') "[ctr' Hclose]"; unfold ctr_inv.
    iIntros "!>"; iExists z'; iFrame.
    iSplit; first by iApply (bi.and_elim_l with "Hclose").
    iIntros (_) "[[% l] _]"; subst; simpl.
    iDestruct "Hclose" as "[_ Hclose]"; iApply ("Hclose" $! tt with "[$l]"). }
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
  forward_call (lock, Ews, cptr_lock_inv g1 g2 ctr).
  { lock_props.
    rewrite <- !(ghost_var_share_join gsh1 gsh2 Tsh) by auto.
    unfold cptr_lock_inv; Exists 0 0 0; entailer!. }
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (lockt, Ews, thread_lock_inv sh1 g1 g2 ctr lock lockt).
  forward_spawn _thread_func nullval (sh1, g1, g2, gv).
  { erewrite <- lock_inv_share_join; try apply Hsh; auto.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto.
    subst ctr lock lockt; entailer!. }
  forward_call (sh2, g1, g2, false, 0, gv).
  forward_call (lockt, sh2, thread_lock_inv sh1 g1 g2 ctr lock lockt).
  { subst ctr lock lockt; cancel. }
  unfold thread_lock_inv at 2; unfold thread_lock_R.
  rewrite selflock_eq.
  Intros.
  simpl.
  forward_call (sh2, g1, g2, 1, 1, gv).
  (* We've proved that t is 2! *)
  forward_call (lock, sh2, cptr_lock_inv g1 g2 ctr).
  { subst ctr lock; cancel. }
  forward_call (lockt, Ews, sh1, thread_lock_R sh1 g1 g2 ctr lock, thread_lock_inv sh1 g1 g2 ctr lock lockt).
  { lock_props.
    unfold thread_lock_inv, thread_lock_R.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; subst ctr lock; cancel. }
  forward_call (lock, Ews, cptr_lock_inv g1 g2 ctr).
  { lock_props.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; subst lock ctr; cancel. }
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
