Require Import VST.concurrency.conclib.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.concurrency.ghosts.
Require Import VST.progs64.incr.
Require Import VST.atomics.general_locks.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition t_counter := Tstruct _counter noattr.

Definition ctr_state gv (g : gname) n := field_at Ews t_counter [StructField _ctr] (Vint (Int.repr (Z.of_nat n))) (gv _c).

Program Definition incr_spec :=
 DECLARE _incr
  ATOMIC TYPE (rmaps.ConstType _) OBJ n INVS ∅
  WITH sh1, sh, h, g, gv
  PRE [ ]
         PROP  (readable_share sh1; sh <> Share.bot)
         PARAMS () GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (sync_inv g Tsh (ctr_state gv))) | (public_half g n)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (sync_inv g Tsh (ctr_state gv))) | (public_half g (n + 1)%nat).

(*Program Definition read_spec :=
 DECLARE _read
  ATOMIC TYPE (rmaps.ConstType (_ * _ * _)) OBJ n INVS ∅
  WITH sh, h, g, gv
  PRE [ ]
         PROP  (sh <> Share.bot; ptr_of h = gv _ctr_lock)
         PARAMS () GLOBALS (gv)
         SEP   (lock_inv sh h (sync_inv g Tsh (ctr_state (gv _ctr)))) | (public_half g n)
  POST [ tuint ]
    EX n' : nat,
         PROP ()
         LOCAL (temp ret_temp (Vint (Int.repr (Z.of_nat n'))))
         SEP (lock_inv sh h (sync_inv g Tsh (ctr_state (gv _ctr)))) | (!!(n' = n) && public_half g n).*)

Definition cptr_inv g g1 g2 :=
  EX x y : nat, ghost_var gsh1 x g1 * ghost_var gsh1 y g2 * public_half g (x + y)%nat.

Definition thread_lock_R sh h g g1 gv := ghost_var gsh2 1%nat g1 * lock_inv sh h (sync_inv g Tsh (ctr_state (gv _ctr))).

Definition thread_lock_inv sh h g g1 gv lockt := selflock (thread_lock_R sh h g g1 gv) sh lockt.

(*Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : namespace * share * lock_handle * lock_handle * gname * gname * gname * globals
  PRE [ tptr tvoid ]
         let '(i, sh, hc, ht, g, g1, g2, gv) := x in
         PROP  (sh <> Share.bot; ptr_of hc = gv _ctr_lock; ptr_of ht = gv _thread_lock)
         PARAMS (y) GLOBALS (gv)
         SEP   (inv i (cptr_inv g g1 g2); ghost_var gsh2 O g1;
                    lock_inv sh hc (sync_inv g Tsh (ctr_state (gv _ctr)));
                lock_inv sh ht (thread_lock_inv sh hc g g1 gv ht))
  POST [ tint ]
         PROP ()
         RETURN (Vint Int.zero)
         SEP ().*)

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [ ] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; (*freelock2_spec;*) spawn_spec; incr_spec(*; read_spec; thread_func_spec*); main_spec]).

Lemma thread_inv_exclusive : forall sh hc g g1 gv lockt,
  exclusive_mpred (thread_lock_inv sh hc g g1 gv lockt).
Proof.
  intros; apply selflock_exclusive.
  unfold thread_lock_R.
  apply exclusive_sepcon1.
  apply ghost_var_exclusive; auto with share.
Qed.
#[local] Hint Resolve thread_inv_exclusive : exclusive.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
match goal with |- context[lock_inv ?a ?h ?c] =>
  gather_SEP (lock_inv a h c); viewshift_SEP 0 (!!(isptr (ptr_of h)) && lock_inv a h c);
    [go_lower; apply lock_inv_isptr | Intros] end.
  lock_isptr.
  viewshift_SEP 2 (!!isptr (ptr_of h) && lock_inv sh h (sync_inv g Tsh (ctr_state gv))).
  { entailer!. apply lock_inv_isptr.
  assert_PROP (isptr (ptr_of h)).
  { 
  forward.
  { entailer!.
  unfold t_lock.
  change threads._atom_int with _atom_int.

  forward.
410619246905162
  assert_PROP (gv _ctr_lock = field_address (tptr t_lock) [] (gv _ctr_lock)).
  entailer!. rewrite field_compatible_field_address; auto. simpl. rewrite isptr_offset_val_zero; auto.
  forward.
  forward_call (gv _ctr_lock, sh, sync_inv g Tsh (ctr_state (gv _ctr))).
  unfold sync_inv at 2; Intros n.
  unfold ctr_state.
  forward.
  forward.
  rewrite add_repr.
  gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
  viewshift_SEP 0 (Q * my_half g Tsh (n + 1)%nat).
  { go_lower.
    apply sync_commit1; intros.
    iIntros; iFrame; auto. }
  forward_call (gv _ctr_lock, sh, sync_inv g Tsh (ctr_state (gv _ctr))).
  { lock_props.
    unfold sync_inv, ctr_state.
    Exists (n + 1)%nat; rewrite Nat2Z.inj_add; cancel. }
  forward.
  cancel.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward_call (gv _ctr_lock, sh, sync_inv g Tsh (ctr_state (gv _ctr))).
  unfold sync_inv at 2; Intros n.
  unfold ctr_state.
  forward.
  gather_SEP (atomic_shift _ _ _ _ _) (my_half _ _ _).
  viewshift_SEP 0 (Q n * my_half g Tsh n).
  { go_lower.
    apply sync_commit2; intros.
    iIntros; iFrame; auto. }
  forward_call (gv _ctr_lock, sh, sync_inv g Tsh (ctr_state (gv _ctr))).
  { lock_props.
    unfold sync_inv, ctr_state.
    Exists n; cancel. }
  forward.
  Exists n; entailer!.
Qed.

(* prove a lemma about our specific use pattern of incr *)
Lemma incr_inv_shift : forall i g g1 g2 gv, (gv = g1 \/ gv = g2) ->
  inv i (cptr_inv g g1 g2) * ghost_var gsh2 0%nat gv |--
  atomic_shift (λ n : nat, public_half g n) (to_coPset i) ∅
      (λ (n : nat) (_ : ()), fold_right_sepcon [public_half g (n + 1)%nat]) (λ _ : (), ghost_var gsh2 1%nat gv).
Proof.
  intros; unfold cptr_inv.
  iIntros "[#inv g]".
  iAuIntro.
  rewrite /atomic_acc /=.
  iInv "inv" as "c" "Hclose"; auto.
  iDestruct "c" as (x y) "[[>g1 >g2] >c]".
  rewrite difference_diag_L; iModIntro.
  iExists (x + y)%nat; iFrame "c"; iSplit.
  - iIntros "c". iFrame.
    iApply "Hclose".
    iExists x, y; iFrame; auto.
  - iIntros (_) "(c & _)".
    destruct H; subst.
    + iPoseProof (ghost_var_inj(A := nat) with "[$g1 $g]") as "%"; auto with share; subst.
      iMod (ghost_var_update with "[g1 g]") as "g1".
      { rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; iFrame. }
      rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
      iDestruct "g1" as "[g1 $]".
      iApply "Hclose".
      iExists 1%nat, y; iFrame; auto.
      rewrite Nat.add_0_l Nat.add_comm; auto.
    + iPoseProof (ghost_var_inj(A := nat) with "[$g2 $g]") as "%"; auto with share; subst.
      iMod (ghost_var_update with "[g2 g]") as "g2".
      { rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; iFrame. }
      rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
      iDestruct "g2" as "[g2 $]".
      iApply "Hclose".
      iExists x, 1%nat; iFrame; auto.
      rewrite Nat.add_0_r; auto.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (sh, g, gv, ghost_var gsh2 1%nat g1).
  { sep_apply incr_inv_shift; auto.
    apply sepcon_derives; [apply atomic_update_mask_weaken; set_solver | cancel]. }
  forward_call ((gv _thread_lock), sh, thread_lock_R sh g g1 gv, thread_lock_inv sh g g1 gv (gv _thread_lock)).
  { lock_props.
    unfold thread_lock_inv, thread_lock_R.
    rewrite -> selflock_eq at 2; cancel. }
  forward.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  set (ctr := gv _ctr); set (lockt := gv _thread_lock); set (lock := gv _ctr_lock).
  forward.
  forward.
  forward.
  ghost_alloc (ghost_var Tsh O).
  Intro g1.
  ghost_alloc (ghost_var Tsh O).
  Intro g2.
  ghost_alloc (both_halves O).
  { apply @part_ref_valid. }
  Intro g; rewrite <- both_halves_join.
  forward_call (lock, Ews, sync_inv g Tsh (ctr_state ctr)).
  forward_call (lock, Ews, sync_inv g Tsh (ctr_state ctr)).
  { lock_props.
    unfold sync_inv, ctr_state.
    Exists O; cancel. }
  rewrite <- 2(ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; Intros.
  gather_SEP (public_half _ _) (ghost_var gsh1 _ _) (ghost_var gsh1 _ _); viewshift_SEP 0 (EX i, inv i (cptr_inv g g1 g2)).
  { go_lower; apply make_inv.
    unfold cptr_inv.
    Exists O O; simpl; cancel. }
  Intros i.
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (lockt, Ews, thread_lock_inv sh1 g g1 gv lockt).
  rewrite invariant_dup; Intros.
  forward_spawn _thread_func nullval (i, sh1, g, g1, g2, gv).
  { erewrite <- 2(lock_inv_share_join sh1 sh2 Ews) by (try apply Hsh; auto).
    subst ctr lock lockt; entailer!. }
  rewrite invariant_dup; Intros.
  gather_SEP (inv _ _) (ghost_var _ _ _).
  forward_call (sh2, g, gv, ghost_var gsh2 1%nat g2).
  { sep_apply incr_inv_shift; auto.
    apply sepcon_derives; [apply atomic_update_mask_weaken; set_solver | cancel]. }
  forward_call (lockt, sh2, thread_lock_inv sh1 g g1 gv lockt).
  { subst ctr lock lockt; cancel. }
  unfold thread_lock_inv at 2; unfold thread_lock_R.
  rewrite selflock_eq.
  Intros.
  gather_SEP (inv _ _) (ghost_var _ _ g1) (ghost_var _ _ g2).
  forward_call (sh2, g, gv, fun n => !!(n = 2)%nat && ghost_var gsh2 1%nat g1 * ghost_var gsh2 1%nat g2).
  { rewrite -> 3sepcon_assoc; apply sepcon_derives; cancel.
    unfold atomic_shift.
    iIntros "[[#I g1] g2]"; iAuIntro.
    rewrite /atomic_acc /=.
    iInv "I" as ">c" "H".
    iDestruct "c" as (x y) "[gs c]"; iExists (x + y)%nat; iFrame "c".
    iApply fupd_mask_intro; first set_solver.
    iIntros "mask"; iSplit.
    - iIntros "lock"; iMod "mask" as "_".
      iMod ("H" with "[-g1 g2]"); last by iFrame.
      unfold cptr_inv.
      iExists x, y; iFrame; auto.
    - iIntros (z) "[[% c] _]".
      iMod "mask" as "_".
      iDestruct "gs" as "[g1' g2']".
      iPoseProof (ghost_var_inj(A := nat) with "[$g1' $g1]") as "%"; auto with share; subst.
      iPoseProof (ghost_var_inj(A := nat) with "[$g2' $g2]") as "%"; auto with share; subst.
      iMod (ghost_var_update with "[g1' g1]") as "g1".
      { rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; iFrame. }
      iMod (ghost_var_update with "[g2' g2]") as "g2".
      { rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; iFrame. }
      rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
      iDestruct "g1" as "[? $]".
      rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
      iDestruct "g2" as "[? $]".
      iMod ("H" with "[-]"); [|auto].
      unfold cptr_inv.
      iExists 1%nat, 1%nat; iFrame; auto. }
  (* We've proved that t is 2! *)
  Intros v; subst.
  forward_call (lock, sh2, sync_inv g Tsh (ctr_state ctr)).
  { subst ctr lock; cancel. }
  forward_call (lockt, Ews, sh1, thread_lock_R sh1 g g1 gv, thread_lock_inv sh1 g g1 gv lockt).
  { lock_props.
    unfold thread_lock_inv, thread_lock_R.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; subst ctr lock; cancel. }
  forward_call (lock, Ews, sync_inv g Tsh (ctr_state ctr)).
  { lock_props.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; subst lock ctr; cancel. }
  forward.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
#[export] Existing Instance Espec.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
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

End proofs.
