Require Import VST.concurrency.conclib.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.concurrency.ghostsI.
Require Import VST.progs64.incr.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition t_counter := Tstruct _counter noattr.

Definition ctr_inv gv g := EX n : nat, field_at Ews t_counter [StructField _ctr] (vint (Z.of_nat n)) (gv _c) * ghost_var gsh2 n g.
Definition ctr_state gv l g (n : nat) := ghost_var gsh1 n g * inv_for_lock l (ctr_inv gv g).

Program Definition incr_spec :=
 DECLARE _incr
  ATOMIC TYPE (rmaps.ConstType (share * val * gname * globals)) OBJ n INVS ∅
  WITH sh, l, g, gv
  PRE [ ]
         PROP  (readable_share sh; isptr l)
         PARAMS () GLOBALS (gv)
         SEP   (field_at sh t_counter [StructField _lock] l (gv _c)) | (ctr_state gv l g n)
  POST [ tvoid ]
         PROP ()
         LOCAL ()
         SEP (field_at sh t_counter [StructField _lock] l (gv _c)) | (ctr_state gv l g (n + 1)%nat).

Program Definition read_spec :=
 DECLARE _read
  ATOMIC TYPE (rmaps.ConstType (share * val * gname * globals)) OBJ n INVS ∅
  WITH sh, l, g, gv
  PRE [ ]
         PROP  (readable_share sh; isptr l)
         PARAMS () GLOBALS (gv)
         SEP   (field_at sh t_counter [StructField _lock] l (gv _c)) | (ctr_state gv l g n)
  POST [ tuint ]
    EX n' : nat,
         PROP ()
         LOCAL (temp ret_temp (vint (Z.of_nat n')))
         SEP (field_at sh t_counter [StructField _lock] l (gv _c)) | (!!(n' = n) && ctr_state gv l g n).

Definition cptr_inv gv l g g1 g2 :=
  EX x y : nat, ghost_var gsh1 x g1 * ghost_var gsh1 y g2 * ctr_state gv l g (x + y)%nat.

Definition thread_lock_R sh1 gv l g1 := field_at sh1 t_counter [StructField _lock] l (gv _c) * ghost_var gsh2 1%nat g1.

Definition thread_lock_inv sh1 sh gv l g1 lockt := selflock (thread_lock_R sh1 gv l g1) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : namespace * share * share * val * lock_handle * gname * gname * gname * globals
  PRE [ tptr tvoid ]
         let '(i, sh1, sh, l, ht, g, g1, g2, gv) := x in
         PROP  (readable_share sh1; sh <> Share.bot; isptr l; ptr_of ht = y)
         PARAMS (y) GLOBALS (gv)
         SEP   (inv i (cptr_inv gv l g g1 g2); field_at sh1 t_counter [StructField _lock] l (gv _c);
                ghost_var gsh2 O g1; lock_inv sh ht (thread_lock_inv sh1 sh gv l g1 ht))
  POST [ tint ]
         PROP ()
         RETURN (Vint Int.zero)
         SEP ().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [ ] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  freelock_spec; spawn_spec; incr_spec; read_spec; thread_func_spec; main_spec]).

Lemma ctr_inv_exclusive : forall gv g, exclusive_mpred (ctr_inv gv g).
Proof.
  intros; unfold ctr_inv.
  eapply derives_exclusive, exclusive_sepcon1 with (Q := EX n : nat, _),
    field_at__exclusive with (sh := Ews)(t := t_counter); auto; simpl; try lia.
  Intro n; apply sepcon_derives; [cancel|].
  Exists n; apply derives_refl.
  { simpl; lia. }
Qed.
#[local] Hint Resolve ctr_inv_exclusive : core.

Lemma thread_inv_exclusive : forall sh1 gv l g1,
  exclusive_mpred (thread_lock_R sh1 gv l g1).
Proof.
  intros; unfold thread_lock_R.
  apply exclusive_sepcon2, ghost_var_exclusive; auto with share.
Qed.
#[local] Hint Resolve thread_inv_exclusive : core.

(* up *)
Lemma exclusive_weak_exclusive : forall P, exclusive_mpred P -> emp |-- weak_exclusive_mpred P && emp.
Proof.
  intros; apply andp_right; auto.
  eapply derives_trans, exclusive_weak_exclusive; auto.
Qed.

(* up *)
Lemma ghost_var_update' : forall {A} g (v1 v2 v : A), ghost_var gsh1 v1 g * ghost_var gsh2 v2 g |--
  |==> !!(v1 = v2) && (ghost_var gsh1 v g * ghost_var gsh2 v g).
Proof.
  intros; erewrite ghost_var_share_join' by eauto.
  Intros; subst; erewrite ghost_var_share_join by eauto.
  rewrite -> prop_true_andp by auto; apply ghost_var_update.
Qed.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  set (AS := atomic_shift _ _ _ _ _).
  forward_call acquire_inv (l, ctr_inv gv g, AS).
  { apply sepcon_derives; [|cancel].
    unfold atomic_shift; iIntros "AU"; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (n) "[ctr_state Hclose]"; unfold ctr_state at 1.
    iExists tt; iDestruct "ctr_state" as "[g $]".
    iModIntro; iSplit.
    { (* tactic? *)
      iIntros "l"; iApply "Hclose"; iFrame. }
    iIntros (_) "[inv _]".
    iApply "Hclose"; iFrame. }
  unfold ctr_inv; Intros n.
  forward.
  forward.
  forward.
  forward_call release_inv (l, ctr_inv gv g, Q).
  { apply sepcon_derives; [|cancel].
    rewrite -> !sepcon_assoc, <- sepcon_emp at 1; apply sepcon_derives, exclusive_weak_exclusive; auto. (* fix *)
    unfold atomic_shift; iIntros "(AU & ctr & g)"; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (n') "[ctr_state Hclose]"; unfold ctr_state at 1.
    iExists tt; iDestruct "ctr_state" as "[g' $]".
    rewrite add_repr.
    iMod (ghost_var_update' with "[$g' $g]") as "(-> & g1 & g2)".
    unfold ctr_inv at 1; iSplitL "ctr g2"; [iExists (n + 1)%nat; iFrame|].
    { rewrite Nat2Z.inj_add; auto. }
    iModIntro; iSplit.
    { (* tactic? *)
      iIntros "[inv l]". unfold ctr_inv at 1.
      iDestruct "inv" as (?) "[f g2]".
      iMod (ghost_var_update' with "[$g1 $g2]") as "(% & g1 & $)"; subst.
      rewrite Nat2Z.inj_add; iFrame "f".
      iApply "Hclose"; iFrame. }
    iIntros (_) "[l _]".
    iDestruct "Hclose" as "[_ Hclose]"; iApply ("Hclose" $! tt); simpl.
    rewrite sepcon_emp; unfold ctr_state; iFrame. }
  entailer!.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward.
  set (AS := atomic_shift _ _ _ _ _).
  forward_call acquire_inv (l, ctr_inv gv g, AS).
  { apply sepcon_derives; [|cancel].
    unfold atomic_shift; iIntros "AU"; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (n) "[ctr_state Hclose]"; unfold ctr_state at 1.
    iExists tt; iDestruct "ctr_state" as "[g $]".
    iModIntro; iSplit.
    { (* tactic? *)
      iIntros "l"; iApply "Hclose"; iFrame. }
    iIntros (_) "[inv _]".
    iApply "Hclose"; iFrame. }
  unfold ctr_inv; Intros n.
  forward.
  forward.
  forward_call release_inv (l, ctr_inv gv g, Q n).
  { apply sepcon_derives; [|cancel].
    rewrite -> !sepcon_assoc, <- sepcon_emp at 1; apply sepcon_derives, exclusive_weak_exclusive; auto. (* fix *)
    unfold atomic_shift; iIntros "(AU & ctr & g)"; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (n') "[ctr_state Hclose]"; unfold ctr_state at 1.
    iExists tt; iDestruct "ctr_state" as "[g' $]".
    simpl; iDestruct (ghost_var_inj with "[$g' $g]") as %?; auto; subst n'.
    unfold ctr_inv at 1; iSplitL "ctr g"; [iExists n; iFrame; auto|].
    iModIntro; iSplit.
    { (* tactic? *)
      iIntros "[inv l]". unfold ctr_inv at 1.
      iDestruct "inv" as (?) "[f g2]".
      iDestruct (ghost_var_inj with "[$g' $g2]") as %?; auto; subst.
      iFrame "f g2"; iApply "Hclose"; iFrame. }
    iIntros (_) "[l _]".
    iDestruct "Hclose" as "[_ Hclose]"; iApply "Hclose"; simpl.
    rewrite sepcon_emp; iSplit; auto.
    unfold ctr_state; iFrame. }
  forward.
  Exists n; entailer!.
Qed.

#[local] Instance ctr_state_timeless : forall gv l g n, Timeless (ctr_state gv l g n).
Proof.
  intros; unfold ctr_state.
  apply bi.sep_timeless; [apply _|].
  unfold inv_for_lock.
  apply bi.exist_timeless; intros []; apply _.
Qed.

(* prove a lemma about our specific use pattern of incr *)
Lemma incr_inv_shift : forall gv i g l g1 g2 gvar, (gvar = g1 \/ gvar = g2) ->
  inv i (cptr_inv gv l g g1 g2) * ghost_var gsh2 0%nat gvar |--
  atomic_shift (λ n : nat, ctr_state gv l g n) (to_coPset i) ∅
      (λ (n : nat) (_ : ()), fold_right_sepcon [ctr_state gv l g (n + 1)%nat]) (λ _ : (), ghost_var gsh2 1%nat gvar).
Proof.
  intros; unfold cptr_inv.
  iIntros "[#inv g]".
  iAuIntro; rewrite /atomic_acc /=.
  iInv "inv" as (x y) ">[[g1 g2] c]" "Hclose"; auto.
  rewrite difference_diag_L; iModIntro.
  iExists (x + y)%nat; iFrame "c"; iSplit.
  - iIntros "c". iFrame.
    iApply "Hclose".
    iExists x, y; iFrame; auto.
  - iIntros (_) "(c & _)".
    destruct H; subst.
    + iMod (ghost_var_update' with "[$g1 $g]") as "(% & g1 & $)"; subst.
      iApply "Hclose".
      iExists 1%nat, y; iFrame; auto.
      rewrite Nat.add_0_l Nat.add_comm; auto.
    + iMod (ghost_var_update' with "[$g2 $g]") as "(% & g2 & $)"; subst.
      iApply "Hclose".
      iExists x, 1%nat; iFrame; auto.
      rewrite Nat.add_0_r; auto.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  forward_call (sh1, l, g, gv, ghost_var gsh2 1%nat g1).
  { sep_apply incr_inv_shift; auto.
    apply sepcon_derives; [apply atomic_update_mask_weaken; set_solver | cancel]. }
  forward_call release_self (sh, ht, thread_lock_R sh1 gv l g1).
  { unfold thread_lock_inv, thread_lock_R, selflock; cancel. }
  forward.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  forward.
  ghost_alloc (ghost_var Tsh O).
  Intro g1.
  ghost_alloc (ghost_var Tsh O).
  Intro g2.
  sep_apply (library.create_mem_mgr gv).
  forward_call (gv).
  (* how do we want to make atomic locks? *)
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
