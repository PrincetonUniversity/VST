Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.concurrency.conclib.
From VSTlib Require Import spec_locks spec_threads spec_malloc.
Require VSTlib.verif_locks.
Require Import iris_ora.algebra.ext_order.
Require Import iris_ora.logic.cancelable_invariants.
Require Import iris.algebra.lib.excl_auth.
Require Import VSTlibtest.incr.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

#[export] Existing Instance verif_locks.M.
#[export] Existing Instance verif_malloc.M.

Canonical Structure excl_authR A := inclR (excl_authR A).

Section mpred.
Context `{VSTGS1: !VSTGS unit Σ,
          cinvG1: !cinvG Σ,
          inG1: !inG Σ (excl_authR natO),
          aii1: !atomic_int_impl (Tstruct _atom_int noattr)}.

Definition spawn_spec := DECLARE _spawn spawn_spec.

Definition t_counter := Tstruct _counter noattr.

Definition ghost_auth (g : gname) (n : nat) : mpred := own g (●E n : excl_authR natO).
Definition ghost_frag (g : gname) (n : nat) : mpred := own g (◯E n : excl_authR natO).

Definition cptr_lock_inv (g1 g2 : gname) (ctr : val) := ∃ z : nat, field_at Ews t_counter [StructField _ctr] (Vint (Int.repr z)) ctr ∗
  ∃ x : nat, ∃ y : nat, ⌜(z = x + y)%nat⌝ ∧ ghost_auth g1 x ∗ ghost_auth g2 y.

Definition incr_spec :=
 DECLARE _incr
  WITH sh1 : share, sh : Qp, h : lock_handle, g1 : gname, g2 : gname, left : bool, n : nat, gv: globals
  PRE [ ]
      PROP  (readable_share sh1)
      PARAMS () GLOBALS (gv)
      SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c);
           lock_inv sh h (cptr_lock_inv g1 g2 (gv _c));
           ghost_frag (if left then g1 else g2) n)
  POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c);
           lock_inv sh h (cptr_lock_inv g1 g2 (gv _c));
           ghost_frag (if left then g1 else g2) (n+1)%nat).


Definition read_spec :=
 DECLARE _read
  WITH sh1 : share, sh : Qp, h : lock_handle, g1 : gname, g2 : gname, n1 : nat, n2 : nat, gv: globals
  PRE [ ]
         PROP  (readable_share sh1)
         PARAMS () GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv g1 g2 (gv _c)); ghost_frag g1 n1; ghost_frag g2 n2)
  POST [ tuint ]
         PROP ()
         RETURN (Vint (Int.repr (n1 + n2)%nat))
         SEP (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c); lock_inv sh h (cptr_lock_inv g1 g2 (gv _c)); ghost_frag g1 n1; ghost_frag g2 n2).

Definition thread_lock_R sh1 (sh : Qp) h (g1 g2 : gname) (ctr : val) :=
  field_at sh1 t_counter [StructField _lock] (ptr_of h) ctr ∗ lock_inv sh h (cptr_lock_inv g1 g2 ctr) ∗ ghost_frag g1 1.

Definition thread_lock_inv sh1 sh h g1 g2 ctr ht :=
  self_part sh ht ∗ thread_lock_R sh1 sh h g1 g2 ctr.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : share * Qp * lock_handle * lock_handle * gname * gname * globals
  PRE [ tptr tvoid ]
         let '(sh1, sh, h, ht, g1, g2, gv) := x in
         PROP  (readable_share sh1; ptr_of ht = y)
         PARAMS (y) GLOBALS (gv)
         SEP   (field_at sh1 t_counter [StructField _lock] (ptr_of h) (gv _c);
                lock_inv sh h (cptr_lock_inv g1 g2 (gv _c));
                ghost_frag g1 0;
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
Definition Gprog : funspecs :=   incrImports ++ incrInternals.

Lemma ctr_inv_exclusive : forall g1 g2 p,
  exclusive_mpred (cptr_lock_inv g1 g2 p).
Proof.
  intros; unfold cptr_lock_inv.
  iIntros "((% & ? & ?) & (% & ? & ?))".
  rewrite !field_at_field_at_; iApply (field_at__conflict with "[$]"); auto.
  { simpl; lia. }
Qed.
#[local] Hint Resolve ctr_inv_exclusive : core.

Lemma thread_inv_exclusive : forall sh1 sh h g1 g2 p,
  exclusive_mpred (thread_lock_R sh1 sh h g1 g2 p).
Proof.
  intros; unfold thread_lock_R.
  iIntros "((? & ? & g1) & (? & ? & g2))".
  iDestruct (own_valid_2 with "g1 g2") as %[]%@excl_auth_frag_op_valid.
Qed.
#[local] Hint Resolve thread_inv_exclusive : core.

Lemma ghost_var_inj : forall g x y, ghost_auth g x ∗ ghost_frag g y ⊢ ⌜x = y⌝.
Proof.
  intros; iIntros "(a & f)".
  iDestruct (own_valid_2 with "a f") as %H%@excl_auth_agree; done.
Qed.

Lemma ghost_var_incr : forall g1 g2 x y n (left : bool), ghost_auth g1 x ∗ ghost_auth g2 y ∗ ghost_frag (if left then g1 else g2) n ⊢
  |==> ⌜(if left then x else y) = n⌝ ∧ ghost_auth (if left then g1 else g2) (n+1)%nat ∗ ghost_frag (if left then g1 else g2) (n+1)%nat ∗
       ghost_auth (if left then g2 else g1) (if left then y else x).
Proof.
  destruct left.
  - iIntros "(a & $ & f)".
    iDestruct (ghost_var_inj with "[$a $f]") as %->.
    iMod (own_update_2 with "a f") as "($ & $)"; last done.
    apply @excl_auth_update.
  - iIntros "($ & a & f)".
    iDestruct (ghost_var_inj with "[$a $f]") as %->.
    iMod (own_update_2 with "a f") as "($ & $)"; last done.
    apply @excl_auth_update.
Qed.

Lemma body_incr: semax_body Vprog Gprog f_incr incr_spec.
Proof.
  start_function.
  forward.
  forward_call (sh, h, cptr_lock_inv g1 g2 (gv _c)).
  unfold cptr_lock_inv at 2.
  Intros z x y.
  forward.
  forward.

  gather_SEP (ghost_auth g1 x) (ghost_auth g2 y) (ghost_frag _ n).
  viewshift_SEP 0 (⌜(if left then x else y) = n⌝ ∧
    ghost_auth (if left then g1 else g2) (n+1)%nat ∗
    ghost_frag (if left then g1 else g2) (n+1)%nat ∗
    ghost_auth (if left then g2 else g1) (if left then y else x)).
  { go_lowerx.
    iIntros "(? & _)".
    by iMod (ghost_var_incr with "[$]"). }
  Intros.
  forward.
  forward_call release_simple (sh, h, cptr_lock_inv g1 g2 (gv _c)).
  { lock_props.
    unfold cptr_lock_inv; Exists (z + 1)%nat.
    unfold Frame; instantiate (1 := [ghost_frag (if left then g1 else g2) (n+1)%nat;
      field_at sh1 t_counter (DOT _lock) (ptr_of h) (gv _c)]); simpl.
    destruct left.
    - Exists (n+1)%nat y; subst; entailer!.
      rewrite !Nat2Z.inj_add //.
    - Exists x (n+1)%nat; entailer!.
      rewrite !Nat2Z.inj_add //. }
  forward.
  cancel.
Qed.

Lemma body_read : semax_body Vprog Gprog f_read read_spec.
Proof.
  start_function.
  forward.
  forward_call (sh, h, cptr_lock_inv g1 g2 (gv _c)).
  unfold cptr_lock_inv at 2; simpl.
  Intros z x y.
  forward.
  assert_PROP (x = n1 /\ y = n2) as Heq.
  { sep_apply ghost_var_inj.
    sep_apply (ghost_var_inj g2).
    entailer!. }
  forward.
  forward_call release_simple (sh, h, cptr_lock_inv g1 g2 (gv _c)).
  { lock_props.
    unfold cptr_lock_inv; Exists z x y; entailer!. }
  destruct Heq as [-> ->]; forward.
  entailer!.
Qed.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  forward_call (sh1, sh, h, g1, g2, true, 0, gv).
  simpl.
  forward_call release_self (sh, ht, thread_lock_R sh1 sh h g1 g2 (gv _c)).
  { lock_props.
    unfold thread_lock_R at 2; unfold thread_lock_inv; cancel. }
  forward.
Qed.

Lemma body_compute2:  semax_body Vprog Gprog f_compute2 compute2_spec.
Proof.
  start_function.
  set (ctr := gv _c).
  forward.
  ghost_alloc (fun g => own g (●E O ⋅ ◯E O : excl_authR natO)).
  { apply excl_auth_valid. }
  Intro g1.
  ghost_alloc (fun g => own g (●E O ⋅ ◯E O : excl_authR natO)).
  { apply excl_auth_valid. }
  Intro g2.
  forward_call (gv, fun _ : lock_handle => cptr_lock_inv g1 g2 ctr).
  Intros lock.
  forward.
  forward.
  forward_call release_simple (1%Qp, lock, cptr_lock_inv g1 g2 ctr).
  { lock_props.
    rewrite !own_op /cptr_lock_inv /ghost_auth.
    Exists O O O.
    unfold_data_at (data_at _ _ _ _); entailer!. }
  (* need to split off shares for the locks here *)
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (gv, fun lockt => thread_lock_inv sh2 (1/2)%Qp lock g1 g2 ctr lockt).
  Intros lockt.
  sep_apply lock_inv_isptr; Intros.
  forward_spawn _thread_func (ptr_of lockt) (sh2, (1/2)%Qp, lock, lockt, g1, g2, gv).
  { rewrite -{3}Qp.half_half -frac_op -lock_inv_share_join.
    rewrite -{1}Qp.half_half -frac_op -lock_inv_share_join.
    erewrite <- field_at_share_join; try apply Hsh; auto.
    subst ctr; entailer!. }
  { simpl; auto. }
  forward_call (sh1, (1/2)%Qp, lock, g1, g2, false, 0, gv).
  forward_call ((1/2)%Qp, lockt, thread_lock_inv sh2 (1/2)%Qp lock g1 g2 (gv _c) lockt).
  unfold thread_lock_inv at 2; unfold thread_lock_R; Intros.
  simpl.
  forward_call (sh1, (1/2)%Qp, lock, g1, g2, 1, 1, gv).
  (* We've proved that t is 2! *)
  forward.
  forward_call ((1/2)%Qp, lock, cptr_lock_inv g1 g2 (gv _c)).
  forward_call freelock_self ((1/2)%Qp, (1/2)%Qp, lockt, thread_lock_R sh2 (1/2) lock g1 g2 (gv _c)).
  { unfold thread_lock_inv, selflock; cancel. }
  { rewrite frac_op Qp.half_half //. }
  forward.
  forward_call freelock_simple (lock, cptr_lock_inv g1 g2 (gv _c)).
  { lock_props.
    rewrite -{2}Qp.half_half -frac_op -lock_inv_share_join.
    subst ctr; cancel. }
  forward.
  unfold_data_at (data_at_ _ _ _). simpl.
  cancel.
  unfold cptr_lock_inv; Intros z x y; cancel.
  rewrite -(field_at_share_join _ _ Ews); [|eauto]; cancel.
  by iIntros "(_ & _ & _ & _)".
 Qed.

(*

Definition extlink := ext_link_prog prog. (* this is wrong, because
       it doesn't include the programs of all the imported VSUs *)
Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
*)

Definition IncrVSU: VSU nil incrImports ltac:(QPprog prog) [compute2_spec] (InitGPred (Vardefs (QPprog prog))).
  Proof. 
    mkVSU prog incrInternals.
    - solve_SF_internal body_incr.
    - solve_SF_internal body_read.
    - solve_SF_internal body_thread_func.
    - solve_SF_internal body_compute2.
  Qed.

End mpred.

