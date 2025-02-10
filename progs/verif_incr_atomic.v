Require Import VST.concurrency.conclib.
Require Import VST.atomics.verif_lock_atomic.
Require Import iris_ora.algebra.ext_order.
Require Import iris.algebra.lib.excl_auth.
Require Import VST.progs.incr.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Canonical Structure excl_authR A := inclR (excl_authR A).

Section mpred.

(* box up concurrentGS? *)
Context `{!VSTGS unit Σ, !cinvG Σ, !inG Σ (excl_authR natO), !atomic_int_impl (Tstruct _atom_int noattr)}.
#[local] Instance concurrent_ext_spec : ext_spec unit := concurrent_ext_spec _ (ext_link_prog prog).

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition t_counter := Tstruct _counter noattr.

Definition ghost_auth (g : gname) (n : nat) : mpred := own g (●E n : excl_authR natO).
Definition ghost_frag (g : gname) (n : nat) : mpred := own g (◯E n : excl_authR natO).

Definition ctr_inv gv g := ∃ n : nat, field_at Ews t_counter [StructField _ctr] (vint (Z.of_nat n)) (gv _c) ∗ ghost_auth g n.
Definition ctr_state gv l g (n : nat) := ghost_frag g n ∗ inv_for_lock l (ctr_inv gv g).

Program Definition incr_spec :=
 DECLARE _incr
  ATOMIC TYPE (ConstType (share * val * gname * globals)) OBJ n INVS ∅
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
  ATOMIC TYPE (ConstType (share * val * gname * globals)) OBJ n INVS ∅
  WITH sh, l, g, gv
  PRE [ ]
         PROP  (readable_share sh; isptr l)
         PARAMS () GLOBALS (gv)
         SEP   (field_at sh t_counter [StructField _lock] l (gv _c)) | (ctr_state gv l g n)
  POST [ tuint ]
    ∃ n' : nat,
         PROP ()
         LOCAL (temp ret_temp (vint (Z.of_nat n')))
         SEP (field_at sh t_counter [StructField _lock] l (gv _c)) | (⌜n' = n⌝ ∧ ctr_state gv l g n).

Definition cptr_inv g g1 g2 :=
  ∃ x y : nat, ghost_auth g1 x ∗ ghost_auth g2 y ∗ ghost_frag g (x + y)%nat.

Definition thread_lock_R sh1 sh gv l g g1 := lock_inv sh l (ctr_inv gv g) ∗ field_at sh1 t_counter [StructField _lock] (ptr_of l) (gv _c) ∗ ghost_frag g1 1%nat.

Definition thread_lock_inv sh1 sh gv l g g1 lockt := selflock (thread_lock_R sh1 sh gv l g g1) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : namespace * share * Qp * lock_handle * lock_handle * gname * gname * gname * globals
  PRE [ tptr tvoid ]
         let '(i, sh1, sh, l, ht, g, g1, g2, gv) := x in
         PROP  (readable_share sh1; ptr_of ht = y; i ## name_of l)
         PARAMS (y) GLOBALS (gv)
         SEP   (inv i (cptr_inv g g1 g2); lock_inv sh l (ctr_inv gv g); field_at sh1 t_counter [StructField _lock] (ptr_of l) (gv _c);
                ghost_frag g1 O; lock_inv sh ht (thread_lock_inv sh1 sh gv l g g1 ht))
  POST [ tint ]
         PROP ()
         RETURN (Vint Int.zero)
         SEP ().

Definition compute2_spec :=
 DECLARE _compute2
 WITH gv: globals
 PRE [] PROP() PARAMS() GLOBALS(gv)
          SEP(library.mem_mgr gv;
                data_at Ews t_counter (Vint (Int.repr 0), Vundef) (gv _c);
                has_ext tt)
 POST [ tint ] PROP() RETURN (Vint (Int.repr 2)) 
                    SEP(library.mem_mgr gv; data_at_ Ews t_counter (gv _c); has_ext tt).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [ ] main_pre prog tt gv
  POST [ tint ] main_post prog gv.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; release_spec; makelock_spec;
  freelock_spec; spawn_spec; incr_spec; read_spec; thread_func_spec; compute2_spec; main_spec]).

Lemma ctr_inv_exclusive : forall gv g, exclusive_mpred (ctr_inv gv g).
Proof.
  intros; unfold ctr_inv.
  eapply derives_exclusive, exclusive_sepcon1 with (Q := ∃ n : nat, _),
    field_at__exclusive with (sh := Ews)(t := t_counter); auto; simpl; try lia.
  Intro n; apply bi.sep_mono; [cancel|].
  Exists n; apply derives_refl.
  { simpl; lia. }
Qed.
#[local] Hint Resolve ctr_inv_exclusive : core.

(* up *)
Lemma ghost_var_inj : forall g x y, ghost_auth g x ∗ ghost_frag g y ⊢ ⌜x = y⌝.
Proof.
  intros; iIntros "(a & f)".
  iDestruct (own_valid_2 with "a f") as %H%@excl_auth_agree; done.
Qed.

Lemma ghost_var_update' : forall g a b c,
  ghost_frag g a ∗ ghost_auth g b ==∗ ⌜a = b⌝ ∧ ghost_frag g c ∗ ghost_auth g c.
Proof.
  intros.
  iIntros "(f & a)".
  iDestruct (ghost_var_inj with "[$a $f]") as %->.
  iMod (own_update_2 with "a f") as "($ & $)"; last done.
  apply @excl_auth_update.
Qed.

Lemma ghost_frag_excl : forall g, exclusive_mpred (ghost_frag g 1).
Proof.
  intros; iIntros "(g1 & g2)".
  iDestruct (own_valid_2 with "g1 g2") as "%".
  rewrite excl_auth_frag_op_valid // in H.
Qed.

Lemma thread_lock_exclusive : forall sh1 sh gv l g g1, exclusive_mpred (thread_lock_R sh1 sh gv l g g1).
Proof.
  intros; unfold thread_lock_R.
  apply exclusive_sepcon2, exclusive_sepcon2, ghost_frag_excl.
Qed.
#[local] Hint Resolve thread_lock_exclusive : core.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  set (AS := atomic_shift _ _ _ _ _).
  forward_call acquire_inv (l, ctr_inv gv g, AS). (* need to patch to simplify rev_curry/tcurry? *)
  { apply bi.sep_mono; [|cancel].
    unfold atomic_shift; iIntros "AU"; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (n) "[ctr_state Hclose]"; unfold ctr_state at 1.
    iExists tt; iDestruct "ctr_state" as "[g $]".
    iModIntro; iSplit.
    { (* tactic? *)
      iIntros "l"; iApply "Hclose"; iFrame. }
    iIntros (?) "[inv _]".
    iApply "Hclose"; iFrame. }
  simpl; unfold ctr_inv; Intros n.
  forward.
  forward.
  forward.
  forward_call release_inv (l, ctr_inv gv g, Q).
  { rewrite assoc assoc; apply bi.sep_mono; [|cancel].
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
    iIntros (?) "[l _]".
    iDestruct "Hclose" as "[_ Hclose]"; iApply ("Hclose" $! tt); simpl.
    unfold ctr_state; iFrame. }
  simpl; entailer!.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward.
  set (AS := atomic_shift _ _ _ _ _).
  forward_call acquire_inv (l, ctr_inv gv g, AS).
  { apply bi.sep_mono; [|cancel].
    unfold atomic_shift; iIntros "AU"; iAuIntro; unfold atomic_acc; simpl.
    iMod "AU" as (n) "[ctr_state Hclose]"; unfold ctr_state at 1.
    iExists tt; iDestruct "ctr_state" as "[g $]".
    iModIntro; iSplit.
    { (* tactic? *)
      iIntros "l"; iApply "Hclose"; iFrame. }
    iIntros (?) "[inv _]".
    iApply "Hclose"; iFrame. }
  simpl; unfold ctr_inv; Intros n.
  forward.
  forward.
  forward_call release_inv (l, ctr_inv gv g, Q n).
  { rewrite assoc assoc; apply bi.sep_mono; [|cancel].
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
    iIntros (?) "[l _]".
    iDestruct "Hclose" as "[_ Hclose]"; iApply "Hclose"; simpl.
    iSplit; auto; iSplit; auto.
    unfold ctr_state; iFrame. }
  simpl. forward.
  Exists n; entailer!!.
Qed.

#[local] Instance ctr_inv_timeless : forall gv g, Timeless (ctr_inv gv g).
Proof.
  intros; unfold ctr_inv.
  apply bi.exist_timeless; intros.
  apply bi.sep_timeless; try apply _.
  apply bi.and_timeless; apply _.
Qed.

(* In this client, the ctr_state is assembled from the combination of the counter's lock assertion
   and a global invariant for the ghost state. In theory we could put it all in a global invariant,
   but this wouldn't allow us to deallocate the lock at the end. *)

(* prove a lemma about our specific use pattern of incr *)
Lemma incr_inv_shift : forall i gv sh g l g1 g2 gvar, (gvar = g1 \/ gvar = g2) -> i ## name_of l ->
  lock_inv sh l (ctr_inv gv g) ∗ inv i (cptr_inv g g1 g2) ∗ ghost_frag gvar 0%nat ⊢
  atomic_shift (λ n : nat, ctr_state gv (ptr_of l) g n) (⊤ ∖ ∅) ∅
      (λ (n : nat) (_ : ()), fold_right_sepcon [ctr_state gv (ptr_of l) g (n + 1)%nat]) (λ _ : (), lock_inv sh l (ctr_inv gv g) ∗ ghost_frag gvar 1%nat).
Proof.
  intros.
  unfold_lock_inv. unfold atomic_lock_inv. Intros.
  iIntros "([#inv0 sh] & #inv & g)".
  unfold atomic_shift; iAuIntro; rewrite /atomic_acc /=.
  iMod (into_acc_cinv with "inv0 sh") as (_) "[[>i sh] Hclose0]"; first done.
  iInv "inv" as (x y) ">(g1 & g2 & c)" "Hclose"; auto.
  unfold ctr_state at 1.
  iExists (x + y)%nat; iFrame "c i sh inv0".
  iFrame "%".
  iApply fupd_mask_intro; first by set_solver. iIntros "mask"; iSplit.
  - iIntros "[g' c]". iFrame "g".
    iMod "mask"; iMod ("Hclose" with "[g1 g2 g']").
    { unfold cptr_inv; iExists x, y; iFrame; auto. }
    iApply "Hclose0"; auto.
  - iIntros (_) "([g' c] & _)".
    destruct H; subst.
    + iMod (ghost_var_update' with "[$g1 $g]") as "(% & $ & g1)"; subst.
      iMod "mask"; iMod ("Hclose" with "[g1 g2 g']").
      { iExists 1%nat, y; iFrame; auto.
        rewrite Nat.add_0_l Nat.add_comm; auto. }
      iApply "Hclose0"; auto.
    + iMod (ghost_var_update' with "[$g2 $g]") as "(% & $ & g2)"; subst.
      iMod "mask"; iMod ("Hclose" with "[g1 g2 g']").
      { iExists x, 1%nat; iFrame; auto.
        rewrite Nat.add_0_r; auto. }
      iApply "Hclose0"; auto.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  sep_apply lock_inv_isptr; Intros.
  forward_call (sh1, ptr_of l, g, gv, lock_inv sh l (ctr_inv gv g) ∗ ghost_frag g1 1%nat); simpl.
  { rewrite /rev_curry /=. sep_apply incr_inv_shift; auto; simpl; cancel. }
  { auto. }
  forward_call release_self (sh, ht, thread_lock_R sh1 sh gv l g g1).
  { lock_props.
    unfold thread_lock_inv, selflock; cancel.
    unfold thread_lock_R; cancel. }
  forward.
Qed.

(* up *)
Lemma ghost_auth_frag : forall g a b, own g (●E a ⋅ ◯E b : excl_authR natO) ⊣⊢ ghost_auth g a ∗ ghost_frag g b.
Proof.
  intros; rewrite own_op //.
Qed.

Opaque Qp.div.

Lemma body_compute2 : semax_body Vprog Gprog f_compute2 compute2_spec.
Proof.
  start_function.
  forward.
  ghost_alloc (fun g => own g (●E O ⋅ ◯E O : excl_authR natO)).
  { apply excl_auth_valid. }
  Intro g1.
  ghost_alloc (fun g => own g (●E O ⋅ ◯E O : excl_authR natO)).
  { apply excl_auth_valid. }
  Intro g2.
  ghost_alloc (fun g => own g (●E O ⋅ ◯E O : excl_authR natO)).
  { apply excl_auth_valid. }
  Intro g.
  (* We allocate the lock here, but give it an invariant later. *)
  forward_call (gv).
  Intros lockp.
  sep_apply atomic_int_isptr; Intros.
  forward.
  forward.
  forward_call release_nonatomic (lockp).
  (* make lock invariant *)
  unfold_data_at (data_at _ _ _ (gv _c)).
  rewrite !ghost_auth_frag; Intros.
  gather_SEP (atomic_int_at _ _ lockp) (field_at _ _ [StructField _ctr] _ _) (ghost_auth g _);
    viewshift_SEP 0 (∃ lock, ⌜ptr_of lock = lockp /\ name_of lock = nroot .@ "ctr"⌝ ∧ lock_inv 1 lock (ctr_inv gv g)).
  { go_lowerx; eapply derives_trans, make_lock_inv_0.
    unfold ctr_inv; Exists O; cancel. }
  Intros lock.
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call makelock_inv (gv, nroot .@ "tlock", fun lockt => thread_lock_inv sh2 (1/2) gv lock g g1 lockt).
  Intros lockt.
  match goal with |-context[|={⊤}=> ?P] => viewshift_SEP 1 P by (go_lowerx; entailer!) end.
  Intros ht.
  sep_apply lock_inv_isptr; Intros.
  gather_SEP (ghost_frag g _) (ghost_auth g1 _) (ghost_auth g2 _).
  viewshift_SEP 0 (inv (nroot .@ "ctr_inv") (cptr_inv g g1 g2)).
  { go_lowerx.
    iIntros "((? & ? & ?) & _)"; iApply inv_alloc.
    unfold cptr_inv.
    by iExists O, O; iFrame. }
  rewrite (bi.persistent_sep_dup (inv _ _)); Intros.
  assert (nroot.@"ctr_inv" ## name_of lock) by (rewrite H0; solve_ndisj).
  forward_spawn _thread_func (ptr_of ht) (nroot .@ "ctr_inv", sh2, (1/2)%Qp, lock, ht, g, g1, g2, gv).
  { entailer!.
    rewrite -{1}Qp.half_half -frac_op -lock_inv_share_join.
    rewrite -{5}Qp.half_half -frac_op -lock_inv_share_join.
    erewrite <- field_at_share_join; try apply Hsh; auto.
    cancel. }
  { simpl; auto. }
  rewrite (bi.persistent_sep_dup (inv _ _)); Intros.
  forward_call (sh1, ptr_of lock, g, gv, lock_inv (1/2) lock (ctr_inv gv g) ∗ ghost_frag g2 1%nat); simpl.
  { rewrite /rev_curry /=. sep_apply incr_inv_shift; auto; simpl; cancel. }
  { rewrite H //. }
  forward_call acquire_inv_simple ((1/2)%Qp, ht, thread_lock_inv sh2 (1/2) gv lock g g1 ht).
  unfold thread_lock_inv at 2; unfold thread_lock_R; rewrite !bi.later_sep; Intros.
  forward_call (sh1, ptr_of lock, g, gv, fun n => ⌜n = 2⌝%nat ∧ lock_inv (1/2) lock (ctr_inv gv g) ∗ ghost_frag g1 1%nat ∗ ghost_frag g2 1%nat); simpl.
  { iIntros "(? & ? & ? & ? & g1 & lock & g2 & inv & ?)"; iSplitL "g1 g2 inv lock"; [|iStopProof; cancel_frame].
    unfold_lock_inv; iDestruct "lock" as "(% & #inv0 & sh)".
    iDestruct "inv" as "#inv".
    unfold rev_curry; simpl.
    unfold atomic_shift; iAuIntro; rewrite /atomic_acc /=.
    iMod (into_acc_cinv with "inv0 sh") as (_) "[[>i sh] Hclose0]"; first done.
    iInv "inv" as (x y) ">(g1' & g2' & c)" "Hclose"; auto.
    iExists (x + y)%nat; iFrame "c i".
    iApply fupd_mask_intro; first set_solver.
    iFrame "sh".
    iIntros "mask"; iSplit.
    - unfold ctr_state. iIntros "[g i]".
      iFrame "g1 g2"; iMod "mask"; iMod ("Hclose" with "[g1' g2' g]").
      { iExists x, y; iFrame; auto. }
      iApply "Hclose0"; auto.
    - iIntros (z) "[[% [g i]] _]".
      iMod "mask" as "_".
      iMod (ghost_var_update' with "[$g1' $g1]") as "(<- & $ & g1)".
      iMod (ghost_var_update' with "[$g2' $g2]") as "(<- & $ & g2)".
      iFrame "inv0".
      iMod ("Hclose" with "[g1 g2 g]").
      { iExists 1%nat, 1%nat; iFrame; auto. }
      iMod ("Hclose0" with "i"); auto. }
  (* We've proved that t is 2! *)
  { rewrite H //. }
  Intros v; subst.
  forward.
  forward_call acquire_inv_simple ((1/2)%Qp, lock, ctr_inv gv g).
  unfold thread_lock_inv.
  forward_call freelock_self ((1/2)%Qp, (1/2)%Qp, ht, thread_lock_R sh2 (1/2) gv lock g g1).
  { unfold selflock; cancel. }
  { apply Qp.half_half. }
  forward.
  forward_call freelock_simple (lock, ctr_inv gv g).
  { lock_props.
    rewrite -{3}Qp.half_half -frac_op -lock_inv_share_join; cancel. }
  forward.
  unfold_data_at (data_at_ _ _ _). simpl.
  cancel.
  unfold ctr_inv; Intros n; cancel.
  rewrite -(field_at_share_join _ _ Ews); [|eauto]; cancel.
  by iIntros "(_ & _ & _)".
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  sep_apply (library.create_mem_mgr gv).
  forward_call.
  { rewrite zero_val_eq.
    repeat change (fold_reptype ?a) with a.
    repeat unfold_data_at (data_at _ _ _ _); simpl.
    rewrite zero_val_eq; cancel. }
  forward.
Qed.

Lemma prog_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons_ext.
{ monPred.unseal; Intros p.
  unfold PROPx, LOCALx, SEPx, local, lift1; simpl; unfold liftx; simpl; unfold lift.
  monPred.unseal; Intros.
  destruct ret; unfold eval_id in H0; simpl in H0; subst; simpl; [|contradiction].
  saturate_local; auto. }
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons body_incr.
semax_func_cons body_read.
semax_func_cons body_thread_func.
semax_func_cons body_compute2.
semax_func_cons body_main.
Qed.

End mpred.
