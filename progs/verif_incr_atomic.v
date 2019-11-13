Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.progs.incr2.
Require Import VST.progs.invariants.
Require Import VST.progs.fupd.
Require Import VST.atomics.general_locks.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock makelock_spec.
Definition makelock2_spec := DECLARE _makelock2 (semax_conc.makelock_spec _).
Definition freelock_spec := DECLARE _freelock freelock_spec.
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition acquire2_spec := DECLARE _acquire2 semax_conc.acquire_spec.
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
         SEPS   (emp) | (ctr_inv (gv _ctr_lock) (gv _ctr) g n)
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
         SEPS   (emp) | (ctr_inv (gv _ctr_lock) (gv _ctr) g n)
  POST [ tuint ]
    EX n' : nat,
         PROP ()
         LOCAL (temp ret_temp (Vint (Int.repr (Z.of_nat n'))))
         SEP (!!(n' = n) && ctr_inv (gv _ctr_lock) (gv _ctr) g n).

Definition cptr_lock_inv g g1 g2 ctr lockc :=
  EX x y : nat, ghost_var gsh1 x g1 * ghost_var gsh1 y g2 * ctr_inv lockc ctr g (x + y)%nat.

Definition thread_lock_R g1 := ghost_var gsh2 1%nat g1.

Definition thread_lock_inv sh g1 lockt := selflock (thread_lock_R g1) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : iname * share * gname * gname * gname * globals * invG
  PRE [ _args OF (tptr tvoid) ]
         let '(i, sh, g, g1, g2, gv, inv_names) := x in
         PROP  (readable_share sh)
         LOCAL (temp _args y; gvars gv)
         SEP   (invariant i (cptr_lock_inv g g1 g2 (gv _ctr) (gv _ctr_lock));
                ghost_var gsh2 O g1;
                lock_inv sh (gv _thread_lock) (thread_lock_inv sh g1 (gv _thread_lock)))
  POST [ tptr tvoid ]
         PROP ()
         LOCAL ()
         SEP (). (* really the thread lock invariant is the postcondition of the spawned thread *)

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [ ] main_pre prog tt nil gv
  POST [ tint ] main_post prog nil gv.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; acquire2_spec; release_spec; release2_spec; makelock_spec;
  makelock2_spec; freelock_spec; freelock2_spec; spawn_spec; incr_spec; read_spec; thread_func_spec; main_spec]).

Lemma thread_inv_exclusive : forall sh g1 lockt, sh <> Share.bot ->
  exclusive_mpred (thread_lock_inv sh g1 lockt).
Proof.
  intros; apply selflock_exclusive.
  unfold thread_lock_R.
  apply ghost_var_exclusive; auto with share.
Qed.
Hint Resolve thread_inv_exclusive : exclusive.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  simpl.
  forward_call [nat : Type; unit : Type] acquire_inv (gv _ctr_lock, g, ctr_state (gv _ctr),
    (λ (n : nat) (_ : ()), ctr_inv (gv _ctr_lock) (gv _ctr) g (n + 1) * emp), (λ _ : (), Q), inv_names).
  { unfold ctr_inv; cancel. }
  Intros n.
  unfold ctr_state.
  forward.
  forward.
  rewrite add_repr.
  forward_call [nat : Type] release_sub (gv _ctr_lock, g, n, (n + 1)%nat, ctr_state (gv _ctr), Q, inv_names).
  { sep_apply (timeless_inv_timeless (ctr_state (gv _ctr))).
    subst Frame; instantiate (1 := nil); simpl.
    unfold ctr_state; rewrite Nat2Z.inj_add; simpl; cancel.
    apply atomic_shift_derives_simple; try solve [iIntros; auto].
    iIntros (x _) "[[% H] _]"; subst; iFrame; auto. }
  forward.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward_call [nat : Type; nat : Type] acquire_inv (gv _ctr_lock, g, ctr_state (gv _ctr),
    (λ (n : nat) n', !!(n' = n) && ctr_inv (gv _ctr_lock) (gv _ctr) g n * emp), Q, inv_names).
  { simpl; unfold ctr_inv; cancel. }
  Intros n.
  unfold ctr_state.
  forward.
  forward_call [nat : Type] release_sub (gv _ctr_lock, g, n, n, ctr_state (gv _ctr), Q n, inv_names).
  { sep_apply (timeless_inv_timeless (ctr_state (gv _ctr))).
    subst Frame; instantiate (1 := nil).
    unfold ctr_state; simpl; cancel.
    apply atomic_shift_derives; try solve [iIntros; auto].
    iIntros (x) "lock !>".
    iExists x; iFrame.
    iSplit; first by (iIntros "H !>").
    iIntros (_) "[[% H] $]"; subst.
    iExists n; iFrame.
    iIntros "!>"; iSplit; auto.
    iIntros "H"; auto. }
  forward.
  Exists n; entailer!.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward_call (g, gv, ghost_var gsh2 1%nat g1, inv_names).
  { unfold atomic_shift.
    Exists (ghost_var gsh2 O g1).
    subst Frame; instantiate (1 := [lock_inv _ _ _]); simpl; cancel; apply sepcon_derives, derives_refl.
    erewrite (add_andp (invariant _ _)) by apply invariant_cored.
    apply andp_derives; auto.
    unfold ashift.
    iIntros "I >g".
    iMod (inv_open with "I") as "[c Hclose]"; auto.
    unfold cptr_lock_inv at 1.
    iDestruct "c" as (x y0) "[[>g1 >g2] >c]".
    iExists (x + y0)%nat; iFrame.
    iMod (updates.fupd_intro_mask (⊤ ∖ inv i) ∅ emp with "[]") as "mask"; auto.
    { apply empty_subseteq. }
    iIntros "!>"; iSplit.
    - iIntros "c"; iFrame.
      iMod "mask" as "_".
      iMod ("Hclose" with "[c g1 g2]"); auto.
      unfold cptr_lock_inv.
      iExists x, y0; iFrame; auto.
    - iIntros (_) "[c _]".
      iPoseProof (ghost_var_inj(A := nat) with "[$g1 $g]") as "%"; auto with share; subst.
      iMod (ghost_var_update with "[g1 g]") as "g1".
      { rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; iFrame. }
      rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
      iDestruct "g1" as "[g1 $]".
      iMod "mask" as "_".
      iMod ("Hclose" with "[c g1 g2]"); auto.
      unfold cptr_lock_inv.
      iExists 1%nat, y0; iFrame; auto.
      rewrite Nat.add_0_l Nat.add_comm; auto. }
  forward_call ((gv _thread_lock), sh, thread_lock_R g1, thread_lock_inv sh g1 (gv _thread_lock)).
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
  forward_call [nat : Type] makelock_inv (lock, O, ctr_state ctr).
  Intros g.
  rewrite <- (emp_sepcon (lock_inv' _ _ _ _)); Intros.
  viewshift_SEP 0 (EX inv_names : invG, wsat).
  { go_lower; apply make_wsat. }
  Intros inv_names.
  rewrite <- 2(ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; Intros.
  gather_SEP (lock_inv' _ _ _ _) (ghost_var gsh1 _ g1) (ghost_var gsh1 _ g2).
  forward_call [nat : Type; nat : Type] release_inv (lock, g, O, ctr_state ctr, fun (n n' : nat) => emp,
    (fun (_ : nat) => emp), inv_names).
  { unfold ctr_state; cancel.
    rewrite -> 4sepcon_assoc; apply sepcon_derives; [|cancel].
    match goal with |- ?A |-- _ => set (P := A) end.
    iIntros "H"; iSplitL "".
    { iApply (timeless_inv_timeless (ctr_state ctr)); auto. }
    unfold atomic_shift.
    iExists P; iSplitR ""; auto; subst P.
    iSplit; last by iApply emp_cored.
    unfold ashift.
    iIntros ">[[lock g1] g2]".
    iExists O; iFrame "lock".
    iMod (updates.fupd_intro_mask ⊤ ∅ emp with "[]") as "mask"; auto.
    iIntros "!>"; iSplit.
    - iIntros "lock"; iMod "mask" as "_".
      iFrame; auto.
    - iIntros (_) "_".
      iMod "mask" as "_".
      iMod (own_dealloc(RA := pos_PCM (discrete_PCM _)) with "g1").
      iMod (own_dealloc(RA := pos_PCM (discrete_PCM _)) with "g2"); auto. }
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (lockt, Ews, thread_lock_inv sh1 g1 lockt).
  gather_SEP wsat (lock_ 3 5; viewshift_SEP 0 (EX i, |> (wsat * invariant i (cptr_lock_inv g g1 g2 ctr lock))).
  { go_lower.
    apply make_inv'.
    unfold cptr_lock_inv.
    Exists O O; unfold ctr_inv; simpl; cancel. }
  Intros i.*)
  forward_spawn _thread_func nullval (i, sh1, g, g1, g2, gv, inv_names).
  { erewrite <- lock_inv_share_join; try apply Hsh; auto.
    subst ctr lock lockt; entailer!. }
  sep_apply invariant_dup; Intros.
  gather_SEP (invariant _ _) (ghost_var _ _ _).
  forward_call (g, gv, ghost_var gsh2 1%nat g2, inv_names).
  { rewrite -> 4sepcon_assoc; apply sepcon_derives; cancel.
    unfold atomic_shift.
    Exists (ghost_var gsh2 O g2); cancel.
    unfold ashift.
    erewrite (add_andp (invariant _ _)) by apply invariant_cored; apply andp_derives; auto.
    iIntros "I >g".
    iMod (inv_open with "I") as "[>c H]"; auto.
    iDestruct "c" as (x y) "[gs c]"; iExists (x + y)%nat; iFrame "c".
    iMod (updates.fupd_intro_mask (⊤ ∖ inv i) ∅ emp with "[]") as "mask"; auto.
    { apply empty_subseteq. }
    iIntros "!>"; iSplit.
    - iIntros "lock"; iMod "mask" as "_".
      iMod ("H" with "[-g]"); auto.
      unfold cptr_lock_inv.
      iExists x, y; iFrame; auto.
    - iIntros (_) "[c _]".
      iMod "mask" as "_".
      iDestruct "gs" as "[g1 g2]".
      iPoseProof (ghost_var_inj(A := nat) with "[$g2 $g]") as "%"; auto with share; subst.
      iMod (ghost_var_update with "[g2 g]") as "g2".
      { rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share; iFrame. }
      rewrite <- (ghost_var_share_join gsh1 gsh2 Tsh) by auto with share.
      iDestruct "g2" as "[g2 $]".
      iApply "H".
      unfold cptr_lock_inv.
      iExists x, 1%nat; iFrame; auto.
      rewrite Nat.add_0_r; auto. }
  forward_call (lockt, sh2, thread_lock_inv sh1 g1 lockt).
  { subst ctr lock lockt; cancel. }
  unfold thread_lock_inv at 2; unfold thread_lock_R.
  rewrite selflock_eq.
  Intros.
  gather_SEP (invariant _ _) (ghost_var _ _ g1) (ghost_var _ _ g2).
  forward_call (g, gv, fun n => !!(n = 2)%nat && ghost_var gsh2 1%nat g1 * ghost_var gsh2 1%nat g2, inv_names).
  { rewrite -> 4sepcon_assoc; apply sepcon_derives; cancel.
    unfold atomic_shift; Exists (ghost_var gsh2 1%nat g1 * ghost_var gsh2 1%nat g2);
      rewrite later_sepcon; cancel.
    erewrite (add_andp (invariant _ _)) by apply invariant_cored; apply andp_derives; auto.
    iIntros "I >[g1 g2]".
    iMod (inv_open with "I") as "[>c H]"; auto.
    iDestruct "c" as (x y) "[gs c]"; iExists (x + y)%nat; iFrame "c".
    iMod (updates.fupd_intro_mask (⊤ ∖ inv i) ∅ emp with "[]") as "mask"; auto.
    { apply empty_subseteq. }
    iIntros "!>"; iSplit.
    - iIntros "lock"; iMod "mask" as "_".
      iMod ("H" with "[-g1 g2]"); last by rewrite later_sepcon; iFrame; auto.
      unfold cptr_lock_inv.
      iExists x, y; iFrame; auto.
    - iIntros (z) "[c _]".
      iMod "mask" as "_".
      iDestruct "gs" as "[g1' g2']".
      iPoseProof (ghost_var_inj(A := nat) with "[$g1' $g1]") as "%"; auto with share; subst.
      iPoseProof (ghost_var_inj(A := nat) with "[$g2' $g2]") as "%"; auto with share; subst.
      iDestruct "c" as "[% c]".
      iMod ("H" with "[c g1' g2']") as "_"; last by iFrame.
      unfold cptr_lock_inv.
      iExists 1%nat, 1%nat; iFrame; auto. }
  (* We've proved that t is 2! *)
  Intros n; subst.
  forward_call [nat : Type; nat : Type] acquire_inv (gv _ctr_lock, g, ctr_state (gv _ctr),
    (λ n n' : nat, !! (n = 2%nat ∧ n' = 2%nat) && lock_inv' (gv _ctr_lock) g n (ctr_state (gv _ctr))),
    λ _ : nat, emp, inv_names).
  Intros n.
  forward_call (lockt, Ews, sh1, thread_lock_R g1, thread_lock_inv sh1 g1 lockt).
  { lock_props.
    unfold thread_lock_inv, thread_lock_R.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; subst ctr lock; cancel. }
  forward_call (lock).
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
