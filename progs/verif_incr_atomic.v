Require Import VST.concurrency.conclib.
Require Import VST.concurrency.ghosts.
Require Import VST.progs.incr.
Require Import VST.atomics.general_locks.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition release2_spec := DECLARE _release2 release2_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).

Definition ctr_state ctr (g : gname) n := data_at Ews tuint (Vint (Int.repr (Z.of_nat n))) ctr.

Program Definition incr_spec :=
 DECLARE _incr
  ATOMIC TYPE (rmaps.ConstType _) OBJ n INVS empty top
  WITH sh, g, gv
  PRE [ ]
         PROP  (readable_share sh)
         PARAMS () GLOBALS (gv)
         SEP   (lock_inv sh (gv _ctr_lock) (sync_inv g Tsh (ctr_state (gv _ctr)))) | (public_half g n)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (lock_inv sh (gv _ctr_lock) (sync_inv g Tsh (ctr_state (gv _ctr)))) | (public_half g (n + 1)%nat).

Program Definition read_spec :=
 DECLARE _read
  ATOMIC TYPE (rmaps.ConstType (_ * _ * _)) OBJ n INVS empty top
  WITH sh, g, gv
  PRE [ ]
         PROP  (readable_share sh)
         PARAMS () GLOBALS (gv)
         SEP   (lock_inv sh (gv _ctr_lock) (sync_inv g Tsh (ctr_state (gv _ctr)))) | (public_half g n)
  POST [ tuint ]
    EX n' : nat,
         PROP ()
         LOCAL (temp ret_temp (Vint (Int.repr (Z.of_nat n'))))
         SEP (lock_inv sh (gv _ctr_lock) (sync_inv g Tsh (ctr_state (gv _ctr)))) | (!!(n' = n) && public_half g n).

Definition cptr_inv g g1 g2 :=
  EX x y : nat, ghost_var gsh1 x g1 * ghost_var gsh1 y g2 * public_half g (x + y)%nat.

Definition thread_lock_R sh g g1 gv := ghost_var gsh2 1%nat g1 * lock_inv sh (gv _ctr_lock) (sync_inv g Tsh (ctr_state (gv _ctr))).

Definition thread_lock_inv sh g g1 gv lockt := selflock (thread_lock_R sh g g1 gv) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : iname * share * gname * gname * gname * globals * invG
  PRE [ tptr tvoid ]
         let '(i, sh, g, g1, g2, gv, inv_names) := x in
         PROP  (readable_share sh)
         PARAMS (y) GLOBALS (gv)
         SEP   (invariant i (cptr_inv g g1 g2); ghost_var gsh2 O g1;
                    lock_inv sh (gv _ctr_lock) (sync_inv g Tsh (ctr_state (gv _ctr)));
                lock_inv sh (gv _thread_lock) (thread_lock_inv sh g g1 gv (gv _thread_lock)))
  POST [ tptr tvoid ]
         PROP ()
         LOCAL ()
         SEP (). (* really the thread lock invariant is the postcondition of the spawned thread *)

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [ ] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; incr_spec; read_spec; thread_func_spec; main_spec]).

Lemma thread_inv_exclusive : forall sh g g1 gv lockt, sh <> Share.bot ->
  exclusive_mpred (thread_lock_inv sh g g1 gv lockt).
Proof.
  intros; apply selflock_exclusive.
  unfold thread_lock_R.
  apply exclusive_sepcon1.
  apply ghost_var_exclusive; auto with share.
Qed.
Hint Resolve thread_inv_exclusive : exclusive.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
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
Lemma incr_inv_shift : forall {inv_names : invG} i g g1 g2 gv, (gv = g1 \/ gv = g2) ->
  invariant i (cptr_inv g g1 g2) * ghost_var gsh2 0%nat gv |--
  atomic_shift (λ n : nat, public_half g n) ∅ ⊤
      (λ (n : nat) (_ : ()), fold_right_sepcon [public_half g (n + 1)%nat]) (λ _ : (), ghost_var gsh2 1%nat gv).
Proof.
  intros; apply inv_atomic_shift; auto.
  { apply empty_subseteq. }
  unfold cptr_inv; iIntros "c".
  iDestruct "c" as (x y0) "[[>g1 >g2] >c]"; iModIntro.
  iExists (x + y0)%nat; iFrame; iSplit.
  - iIntros "c !>".
    iExists x, y0; iFrame; auto.
  - iIntros (_) "(>g & c & _)".
    destruct H; subst.
    + iPoseProof (ghost_var_inj(A := nat) with "[$g1 $g]") as "%"; auto with share; subst.
      iMod (ghost_var_update with "[g1 g]") as "g1".
      { rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; iFrame. }
      rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
      iDestruct "g1" as "[g1 $]".
      iExists 1%nat, y0; iFrame; auto.
      rewrite Nat.add_0_l Nat.add_comm; auto.
    + iPoseProof (ghost_var_inj(A := nat) with "[$g2 $g]") as "%"; auto with share; subst.
      iMod (ghost_var_update with "[g2 g]") as "g2".
      { rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; iFrame. }
      rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
      iDestruct "g2" as "[g2 $]".
      iExists x, 1%nat; iFrame; auto.
      rewrite Nat.add_0_r; auto.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (sh, g, gv, ghost_var gsh2 1%nat g1, inv_names).
  { sep_apply incr_inv_shift; auto.
    apply sepcon_derives; [apply derives_refl | cancel]. }
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
  rewrite <- (emp_sepcon (lock_inv _ _ _)); Intros.
  viewshift_SEP 0 (EX inv_names : invG, wsat).
  { go_lower; apply make_wsat. }
  Intros inv_names.
  rewrite <- 2(ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; Intros.
  gather_SEP 0 2 3 5; viewshift_SEP 0 (EX i, |> (wsat * invariant i (cptr_inv g g1 g2))).
  { go_lower.
    apply make_inv'.
    unfold cptr_inv.
    Exists O O; simpl; cancel. }
  Intros i.
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (lockt, Ews, thread_lock_inv sh1 g g1 gv lockt).
  rewrite invariant_dup; Intros.
  forward_spawn _thread_func nullval (i, sh1, g, g1, g2, gv, inv_names).
  { erewrite <- 2(lock_inv_share_join sh1 sh2 Ews) by (try apply Hsh; auto).
    subst ctr lock lockt; entailer!. }
  rewrite invariant_dup; Intros.
  gather_SEP (invariant _ _) (ghost_var _ _ _).
  forward_call (sh2, g, gv, ghost_var gsh2 1%nat g2, inv_names).
  { sep_apply incr_inv_shift; auto.
    apply sepcon_derives; [apply derives_refl | cancel]. }
  forward_call (lockt, sh2, thread_lock_inv sh1 g g1 gv lockt).
  { subst ctr lock lockt; cancel. }
  unfold thread_lock_inv at 2; unfold thread_lock_R.
  rewrite selflock_eq.
  Intros.
  gather_SEP (invariant _ _) (ghost_var _ _ g1) (ghost_var _ _ g2).
  forward_call (sh2, g, gv, fun n => !!(n = 2)%nat && ghost_var gsh2 1%nat g1 * ghost_var gsh2 1%nat g2, inv_names).
  { rewrite -> 4sepcon_assoc; apply sepcon_derives; cancel.
    unfold atomic_shift; Exists (ghost_var gsh2 1%nat g1 * ghost_var gsh2 1%nat g2);
      rewrite later_sepcon; cancel.
    erewrite (add_andp (invariant _ _)) by apply invariant_cored; apply andp_derives; auto.
    iIntros "I >[g1 g2]".
    iMod (inv_open with "I") as "[>c H]"; auto.
    iDestruct "c" as (x y) "[gs c]"; iExists (x + y)%nat; iFrame "c".
    iMod (fupd_mask_subseteq) as "mask".
    { apply empty_subseteq. }
    iIntros "!>"; iSplit.
    - iIntros "lock"; iMod "mask" as "_".
      iMod ("H" with "[-g1 g2]"); last by rewrite later_sepcon; iFrame; auto.
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
