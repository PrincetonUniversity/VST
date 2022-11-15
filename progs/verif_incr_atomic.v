Require Import VST.concurrency.conclib.
Require Import VST.atomics.verif_lock_atomic.
Require Import VST.concurrency.ghostsI.
Require Import VST.progs.incr.

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

Definition cptr_inv g g1 g2 :=
  EX x y : nat, ghost_var gsh1 x g1 * ghost_var gsh1 y g2 * ghost_var gsh1 (x + y)%nat g.

Definition thread_lock_R sh1 sh gv l g g1 := lock_inv sh l (ctr_inv gv g) * field_at sh1 t_counter [StructField _lock] (ptr_of l) (gv _c) * ghost_var gsh2 1%nat g1.

Definition thread_lock_inv sh1 sh gv l g g1 lockt := selflock (thread_lock_R sh1 sh gv l g g1) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : namespace * share * share * lock_handle * lock_handle * gname * gname * gname * globals
  PRE [ tptr tvoid ]
         let '(i, sh1, sh, l, ht, g, g1, g2, gv) := x in
         PROP  (readable_share sh1; ptr_of ht = y; i ## name_of l)
         PARAMS (y) GLOBALS (gv)
         SEP   (inv i (cptr_inv g g1 g2); lock_inv sh l (ctr_inv gv g); field_at sh1 t_counter [StructField _lock] (ptr_of l) (gv _c);
                ghost_var gsh2 O g1; lock_inv sh ht (thread_lock_inv sh1 sh gv l g g1 ht))
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
    lock_props.
    unfold atomic_shift; iIntros "((AU & ctr) & g)"; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (n') "[ctr_state Hclose]"; unfold ctr_state at 1.
    iExists tt; iDestruct "ctr_state" as "[g' $]".
    rewrite add_repr.
    iMod (ghost_var_update' with "[$g' $g]") as "(-> & g1 & g2)".
    iSplitL "ctr g2".
    { iExists (n + 1)%nat; rewrite Nat2Z.inj_add; iFrame; auto. }
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
    lock_props.
    unfold atomic_shift; iIntros "((AU & ctr) & g)"; iAuIntro; unfold atomic_acc; simpl.
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

#[local] Instance ctr_inv_timeless : forall gv g, Timeless (ctr_inv gv g).
Proof.
  intros; unfold ctr_inv.
  apply bi.exist_timeless; intros []; apply _.
Qed.

(* In this client, the ctr_state is assembled from the combination of the counter's lock assertion
   and a global invariant for the ghost state. In theory we could put it all in a global invariant,
   but this wouldn't allow us to deallocate the lock at the end. *)

(* prove a lemma about our specific use pattern of incr *)
Lemma incr_inv_shift : forall i gv sh g l g1 g2 gvar, (gvar = g1 \/ gvar = g2) -> i ## name_of l ->
  lock_inv sh l (ctr_inv gv g) * inv i (cptr_inv g g1 g2) * ghost_var gsh2 0%nat gvar |--
  atomic_shift (λ n : nat, ctr_state gv (ptr_of l) g n) (⊤ ∖ ∅) ∅
      (λ (n : nat) (_ : ()), fold_right_sepcon [ctr_state gv (ptr_of l) g (n + 1)%nat]) (λ _ : (), lock_inv sh l (ctr_inv gv g) * ghost_var gsh2 1%nat gvar).
Proof.
  intros.
  unfold_lock_inv; Intros.
  rewrite -> prop_true_andp by auto.
  iIntros "[[[#inv0 sh] #inv] g]".
  unfold atomic_shift; iAuIntro; rewrite /atomic_acc /=.
  iMod (into_acc_cinv with "inv0 sh") as (_) "[[>i sh] Hclose0]". done.
  iInv "inv" as (x y) ">[[g1 g2] c]" "Hclose"; auto.
  unfold ctr_state at 1.
  iExists (x + y)%nat; iFrame "c i sh inv0".
  iApply fupd_mask_intro; first by set_solver. iIntros "mask"; iSplit.
  - iIntros "[g' c]". iFrame "g".
    iMod "mask"; iMod ("Hclose" with "[g1 g2 g']").
    { unfold cptr_inv; iExists x, y; iFrame; auto. }
    iApply "Hclose0"; auto.
  - iIntros (_) "([g' c] & _)".
    destruct H; subst.
    + iMod (ghost_var_update' with "[$g1 $g]") as "(% & g1 & $)"; subst.
      iMod "mask"; iMod ("Hclose" with "[g1 g2 g']").
      { iExists 1%nat, y; iFrame; auto.
        rewrite Nat.add_0_l Nat.add_comm; auto. }
      iApply "Hclose0"; auto.
    + iMod (ghost_var_update' with "[$g2 $g]") as "(% & g2 & $)"; subst.
      iMod "mask"; iMod ("Hclose" with "[g1 g2 g']").
      { iExists x, 1%nat; iFrame; auto.
        rewrite Nat.add_0_r; auto. }
      iApply "Hclose0"; auto.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  sep_apply lock_inv_isptr; Intros.
  forward_call (sh1, ptr_of l, g, gv, lock_inv sh l (ctr_inv gv g) * ghost_var gsh2 1%nat g1).
  { sep_apply incr_inv_shift; auto; cancel. }
  forward_call release_self (sh, ht, thread_lock_R sh1 sh gv l g g1).
  { unfold thread_lock_inv, thread_lock_R; cancel. }
  forward.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  forward.
  ghost_alloc (ghost_var Tsh O).
  Intro g1.
  ghost_alloc (ghost_var Tsh O).
  Intro g2.
  ghost_alloc (ghost_var Tsh O).
  Intro g.
  sep_apply (library.create_mem_mgr gv).
  (* We allocate the lock here, but give it an invariant later. *)
  forward_call (gv).
  Intros lockp.
  sep_apply atomic_int_isptr; Intros.
  forward.
  forward.
  forward_call release_nonatomic (lockp).
  (* make lock invariant *)
  unfold_data_at (data_at _ _ _ (gv _c)).
  rewrite <- 3(ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; Intros.
  gather_SEP (atomic_int_at _ _ lockp) (field_at _ _ [StructField _ctr] _ _) (ghost_var gsh2 _ g);
    viewshift_SEP 0 (EX lock, !!(ptr_of lock = lockp /\ name_of lock = nroot .@ "ctr") && lock_inv Tsh lock (ctr_inv gv g)).
  { go_lower; eapply derives_trans, make_lock_inv_0.
    unfold ctr_inv; Exists O; cancel. }
  Intros lock.
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call makelock_inv (gv, nroot .@ "tlock", fun lockt => thread_lock_inv sh2 gsh2 gv lock g g1 lockt).
  Intros lockt.
  match goal with |-context[|={⊤}=> ?P] => viewshift_SEP 1 P by entailer! end.
  Intros ht.
  sep_apply lock_inv_isptr; Intros.
  gather_SEP (ghost_var gsh1 _ g) (ghost_var gsh1 _ g1) (ghost_var gsh1 _ g2).
  viewshift_SEP 0 (inv (nroot .@ "ctr_inv") (cptr_inv g g1 g2)).
  { go_lower.
    eapply derives_trans, inv_alloc.
    eapply derives_trans, now_later.
    unfold cptr_inv.
    Exists O O; simpl; cancel. }
  rewrite invariant_dup; Intros.
  assert (nroot.@"ctr_inv" ## name_of lock) by (rewrite H0; solve_ndisj).
  forward_spawn _thread_func (ptr_of ht) (nroot .@ "ctr_inv", sh2, gsh2, lock, ht, g, g1, g2, gv).
  { entailer!.
    erewrite <- lock_inv_share_join; try apply gsh1_gsh2_join; auto.
    erewrite <- (lock_inv_share_join _ _ Tsh); try apply gsh1_gsh2_join; auto.
    erewrite <- field_at_share_join; try apply Hsh; auto.
    cancel. }
  { simpl; auto. }
  rewrite invariant_dup; Intros.
  forward_call (sh1, ptr_of lock, g, gv, lock_inv gsh1 lock (ctr_inv gv g) * ghost_var gsh2 1%nat g2).
  { sep_apply incr_inv_shift; auto; cancel. }
  forward_call acquire_inv_simple (gsh1, ht, thread_lock_inv sh2 gsh2 gv lock g g1 ht).
  unfold thread_lock_inv at 2; unfold thread_lock_R; rewrite -> 3later_sepcon; Intros.
  forward_call (sh1, ptr_of lock, g, gv, fun n => !!(n = 2)%nat && lock_inv gsh1 lock (ctr_inv gv g) * ghost_var gsh2 1%nat g1).
  { iIntros "((((((? & g1) & lock) & g2) & inv) & ?) & ?)"; iSplitL "g1 g2 inv lock"; [|iVST; cancel_frame].
    unfold_lock_inv; iDestruct "lock" as "[[[% %] #inv0] sh]".
    iDestruct "inv" as "#inv".
    unfold atomic_shift; iAuIntro; rewrite /atomic_acc /=.
    iMod (into_acc_cinv with "inv0 sh") as (_) "[[>i sh] Hclose0]". done.
    iInv "inv" as (x y) ">[gs c]" "Hclose"; auto.
    iExists (x + y)%nat; iFrame "c i".
    iApply fupd_mask_intro; first set_solver.
    iFrame "sh".
    iIntros "mask"; iSplit.
    - unfold ctr_state. iIntros "[g i]".
      iFrame "g1 g2"; iMod "mask"; iMod ("Hclose" with "[gs g]").
      { iExists x, y; iFrame; auto. }
      iApply "Hclose0"; auto.
    - iIntros (z) "[[% [g i]] _]".
      iMod "mask" as "_".
      iDestruct "gs" as "[g1' g2']".
      iPoseProof (ghost_var_inj(A := nat) with "[$g1' $g1]") as "%"; auto with share; subst.
      iPoseProof (ghost_var_inj(A := nat) with "[$g2' $g2]") as "%"; auto with share; subst.
      iMod (ghost_var_update with "[g1' g1]") as "g1".
      { rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; iFrame. }
      iMod (ghost_var_update with "[g2' g2]") as "g2".
      { rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; iFrame. }
      rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
      iFrame "inv0".
      iDestruct "g1" as "[g1 $]".
      rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
      iDestruct "g2" as "[g2 _]".
      iMod ("Hclose" with "[g1 g2 g]").
      { iExists 1%nat, 1%nat; iFrame "g1 g2 g"; auto. }
      iMod ("Hclose0" with "i"); auto. }
  (* We've proved that t is 2! *)
  Intros v; subst.
  forward.
  forward_call acquire_inv_simple (gsh1, lock, ctr_inv gv g).
  unfold thread_lock_inv.
  forward_call freelock_self (gsh1, gsh2, ht, thread_lock_R sh2 gsh2 gv lock g g1).
  forward.
  forward_call freelock_simple (lock, ctr_inv gv g).
  { lock_props.
    erewrite <- (lock_inv_share_join gsh1 gsh2 Tsh); auto; cancel. }
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
{ simpl; Intros p; unfold PROPx, LOCALx, SEPx, local; simpl; unfold liftx, lift1, lift; simpl; Intros; subst.
  sep_apply atomic_int_isptr; Intros.
  destruct ret; try contradiction.
  unfold eval_id in *; simpl in *; apply prop_right; auto. }
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons body_incr.
semax_func_cons body_read.
semax_func_cons body_thread_func.
semax_func_cons body_main.
Qed.
