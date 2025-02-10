Require Import VST.veric.juicy_extspec.
Require Import VST.veric.SeparationLogic.
Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.expr.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.field_at.
(*Require Import VST.concurrency.conclib.*)
Import Clightdefs.
Import String.

Definition voidstar_funtype := Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default.
(* Definition tlock := Tstruct _lock_t noattr. *)
Definition tlock := (Tarray (Tpointer Ctypes.Tvoid noattr) 2 noattr).

Goal forall (cenv: compspecs), @sizeof cenv tlock = LKSIZE.
Proof. reflexivity. Qed.

Section mpred.

Context `{!VSTGS OK_ty Σ}.

Definition selflock_fun Q sh p : mpred -> mpred :=
  fun R => (Q ∗ ▷lock_inv sh p R).

#[export] Instance selflock_contractive Q sh p : Contractive (selflock_fun Q sh p).
Proof.
  intros ????.
  rewrite /selflock_fun.
  f_equiv. (* f_contractive. *) apply later_contractive.
  destruct n; first apply dist_later_0.
  rewrite -!dist_later_S in H |- *.
  f_equiv. done.
Qed.

Definition selflock Q sh p : mpred := fixpoint (selflock_fun Q sh p).

Lemma selflock_eq Q sh p : selflock Q sh p ⊣⊢ (Q ∗ ▷lock_inv sh p (selflock Q sh p)).
Proof.
  rewrite {1}/selflock fixpoint_unfold //.
Qed.

(*(* In fact we need locks to two resources:
   1) the resource invariant, for passing the resources
   2) the join resource invariant, for returning all resources, including itself
   for this we need to define them in a mutually recursive fashion: *)

Definition res_invariants_fun Q sh1 p1 sh2 p2 : (bool -> mpred) -> (bool -> mpred) :=
  fun R b =>
    if b then
      (Q * lock_inv sh2 p2 (▷ R false))
    else
      (Q * lock_inv sh1 p1 (▷ R true) * lock_inv sh2 p2 (▷ R false)).

Definition res_invariants Q sh1 p1 sh2 p2 : bool -> mpred := HORec (res_invariants_fun Q sh1 p1 sh2 p2).
Definition res_invariant Q sh1 p1 sh2 p2 : mpred := res_invariants Q sh1 p1 sh2 p2 true.
Definition join_res_invariant Q sh1 p1 sh2 p2 : mpred := res_invariants Q sh1 p1 sh2 p2 false.

Lemma res_invariants_eq Q sh1 p1 sh2 p2 : res_invariants Q sh1 p1 sh2 p2 =
  res_invariants_fun Q sh1 p1 sh2 p2 (res_invariants Q sh1 p1 sh2 p2).
Proof.
  apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 b.
  destruct b.
    (* resource invariant *)
    apply subp_sepcon; try apply subp_refl.
    apply allp_left with false.
    eapply derives_trans.
      apply semax_conc.nonexpansive_entail, nonexpansive_lock_inv.
      apply fash_derives, andp_left1, derives_refl.

    (* join resource invariant *)
    repeat apply subp_sepcon; try apply subp_refl.
      apply allp_left with true.
      eapply derives_trans.
        apply semax_conc.nonexpansive_entail, nonexpansive_lock_inv.
        apply fash_derives, andp_left1, derives_refl.

      apply allp_left with false.
      eapply derives_trans.
        apply semax_conc.nonexpansive_entail, nonexpansive_lock_inv.
        apply fash_derives, andp_left1, derives_refl.
Qed.

Lemma res_invariant_eq Q sh1 p1 sh2 p2 :
  res_invariant Q sh1 p1 sh2 p2 =
  (Q *
  lock_inv sh2 p2 (▷ join_res_invariant Q sh1 p1 sh2 p2)).
Proof.
  unfold res_invariant at 1.
  rewrite res_invariants_eq.
  reflexivity.
Qed.

Lemma join_res_invariant_eq Q sh1 p1 sh2 p2 :
  join_res_invariant Q sh1 p1 sh2 p2 =
  (Q *
  lock_inv sh1 p1 (▷ res_invariant Q sh1 p1 sh2 p2) *
  lock_inv sh2 p2 (▷ join_res_invariant Q sh1 p1 sh2 p2)).
Proof.
  unfold join_res_invariant at 1.
  rewrite res_invariants_eq.
  reflexivity.
Qed.*)

(*+ Specification of each concurrent primitive *)

Definition acquire_arg_type: TypeTree := ProdType (ConstType (val * share)) Mpred.

(* up *)
#[export] Instance monPred_at_ne : NonExpansive (@monPred_at environ_index mpred : _ -> _ -d> _).
Proof. solve_proper. Qed.

#[export] Instance monPred_at_args_ne : NonExpansive (@monPred_at argsEnviron_index mpred : _ -> _ -d> _).
Proof. solve_proper. Qed.

Program Definition acquire_spec :=
  TYPE acquire_arg_type WITH v : _, sh : _, R : _
  PRE [ tptr tvoid ]
     PROP (readable_share sh)
     PARAMS (v)
     SEP (lock_inv sh v R)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v R; R).
Next Obligation.
Proof.
  intros ? ((v, sh), R) ((?, ?), ?) ([=] & HR); simpl in *; subst.
  rewrite HR //.
Qed.
Next Obligation.
Proof.
  intros ? ((v, sh), R) ((?, ?), ?) ([=] & HR); simpl in *; subst.
  rewrite HR //.
Qed.

Definition release_arg_type: TypeTree := ProdType (ConstType (val * share)) Mpred.

Program Definition release_spec :=
  TYPE release_arg_type WITH v : _, sh : _, R : _
  PRE [ tptr tvoid ]
     PROP (readable_share sh)
     PARAMS (v)
     SEP (<affine> exclusive_mpred R; lock_inv sh v R; R)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v R).
Next Obligation.
Proof.
  intros ? ((v, sh), R) ((?, ?), ?) ([=] & HR); simpl in *; subst.
  rewrite /exclusive_mpred HR //.
Qed.
Next Obligation.
Proof.
  intros ? ((v, sh), R) ((?, ?), ?) ([=] & HR); simpl in *; subst.
  rewrite /exclusive_mpred HR //.
Qed.

Program Definition makelock_spec (cs : compspecs) : funspec :=
  TYPE ProdType (ConstType (val * share)) Mpred WITH v : _, sh : _, R : _
  PRE [ tptr tvoid ]
    PROP (writable_share sh)
    PARAMS (v)
    SEP (data_at_ sh tlock v)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (lock_inv sh v R).
Next Obligation.
Proof.
  intros ?? ((v, sh), R) ((?, ?), ?) ([=] & HR); simpl in *; subst.
  reflexivity.
Qed.
Next Obligation.
  intros ?? ((v, sh), R) ((?, ?), ?) ([=] & HR); simpl in *; subst.
  rewrite HR //.
Qed.

Program Definition freelock_spec (cs : compspecs) : funspec :=
  TYPE ProdType (ConstType (val * share)) Mpred WITH v : _, sh : _, R : _
  PRE [ tptr tvoid ]
    PROP (writable_share sh)
    PARAMS (v)
    SEP (exclusive_mpred R; lock_inv sh v R; R)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (data_at_ sh tlock v; R).
Next Obligation.
Proof.
  intros ?? ((v, sh), R) ((?, ?), ?) ([=] & HR); simpl in *; subst.
  rewrite /exclusive_mpred HR //.
Qed.
Next Obligation.
Proof.
  intros ?? ((v, sh), R) ((?, ?), ?) ([=] & HR); simpl in *; subst.
  rewrite HR //.
Qed.

(* versions that give away all their resources *)

Lemma selflock_rec : forall sh v R, ⊢rec_inv sh v R (selflock R sh v).
Proof.
  intros; unfold rec_inv.
  rewrite {1} selflock_eq.
  apply bi.wand_iff_refl.
Qed.

Program Definition freelock2_spec (cs : compspecs) : funspec :=
  TYPE ProdType (ProdType (ConstType (val * share * share)) Mpred) Mpred
  WITH v : _, sh : _, sh' : _, Q : _, R : _
  PRE [ tptr tvoid ]
    PROP (writable_share sh)
    PARAMS (v)
    SEP (exclusive_mpred R; rec_inv sh' v Q R; lock_inv sh v R)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (data_at_ sh tlock v).
Next Obligation.
Proof.
  intros ?? ((((v, sh), sh'), Q), R) ((((?, ?), ?), ?), ?) (([=] & HQ) & HR); simpl in *; subst.
  rewrite /exclusive_mpred /rec_inv HQ HR //.
Qed.
Next Obligation.
Proof.
  intros ?? ((((v, sh), sh'), Q), R) ((((?, ?), ?), ?), ?) (([=] & HQ) & HR); simpl in *; subst.
  reflexivity.
Qed.

Program Definition release2_spec: funspec :=
  TYPE ProdType (ProdType (ConstType (val * share)) Mpred) Mpred
  WITH v : _, sh : _, Q : _, R : _
  PRE [ tptr tvoid ]
    PROP (readable_share sh)
    PARAMS (v)
    SEP (exclusive_mpred R; rec_inv sh v Q R; R)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP ().
Next Obligation.
Proof.
  intros ? (((v, sh), Q), R) (((?, ?), ?), ?) (([=] & HQ) & HR); simpl in *; subst.
  rewrite /exclusive_mpred /rec_inv HQ HR //.
Qed.
Next Obligation.
Proof.
  intros ? (((v, sh), Q), R) (((?, ?), ?), ?) (([=] & HQ) & HR); simpl in *; subst.
  reflexivity.
Qed.

(*
(* condition variables *)
Definition makecond_spec cs :=
   WITH v : val, sh : share
   PRE [ _cond OF tptr tcond ]
     PROP (writable_share sh)
     LOCAL (temp _cond v)
     SEP (@data_at_ cs sh tcond v)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (cond_var sh v).

Definition freecond_spec cs :=
   WITH v : val, sh : share
   PRE [ _cond OF tptr tcond ]
     PROP (writable_share sh)
     LOCAL (temp _cond v)
     SEP (@cond_var cs sh v)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (@data_at_ cs sh tcond v).

Program Definition wait_spec cs: funspec := mk_funspec
  ((_cond OF tptr tcond)%formals :: (_lock OF tptr Tvoid)%formals :: nil, tvoid)
  cc_default
  (ProdType (ConstType (val * val * share * share)) Mpred)
  (fun _ x =>
   match x with
   | (c, l, shc, shl, R) =>
     PROP (readable_share shc)
     LOCAL (temp _cond c; temp _lock l)
     SEP (@cond_var cs shc c; lock_inv shl l R; R)
   end)
  (fun _ x =>
   match x with
   | (c, l, shc, shl, R) =>
     PROP ()
     LOCAL ()
     SEP (cond_var shc c; lock_inv shl l R; R)
   end)
  _
  _
.
Next Obligation.
  intros cs; hnf.
  intros.
  destruct x as [[[[c l] shc] shl] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP (readable_share shc)
    LOCAL (temp _cond c; temp _lock l)
    SEP (cond_var shc c; lock_inv shl l R; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          ((fun _ => readable_share shc) :: nil)
          (temp _cond c :: temp _lock l :: nil)
          ((fun R => cond_var shc c) :: (fun R => lock_inv shl l R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.
Next Obligation.
  intros cs; hnf.
  intros.
  destruct x as [[[[c l] shc] shl] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP ()
    LOCAL ()
    SEP (cond_var shc c; lock_inv shl l R; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun R => cond_var shc c) :: (fun R => lock_inv shl l R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.

Program Definition wait2_spec cs: funspec := mk_funspec
  ((_cond OF tptr tcond)%formals :: (_lock OF tptr Tvoid)%formals :: nil, tvoid)
  cc_default
  (ProdType (ConstType (val * val * share * share)) Mpred)
  (fun _ x =>
   match x with
   | (c, l, shc, shl, R) =>
     PROP (readable_share shc)
     LOCAL (temp _cond c; temp _lock l)
     SEP (lock_inv shl l R; R && (@cond_var cs shc c * TT))
   end)
  (fun _ x =>
   match x with
   | (c, l, shc, shl, R) =>
     PROP ()
     LOCAL ()
     SEP (lock_inv shl l R; R)
   end)
  _
  _
.
Next Obligation.
  intros cs; hnf.
  intros.
  destruct x as [[[[c l] shc] shl] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP (readable_share shc)
    LOCAL (temp _cond c; temp _lock l)
    SEP (lock_inv shl l R; R && (@cond_var cs shc c * TT))) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          ((fun _ => readable_share shc) :: nil)
          (temp _cond c :: temp _lock l :: nil)
          ((fun R => lock_inv shl l R) :: (fun R => R && (@cond_var cs shc c * TT)) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply (conj_nonexpansive (fun R => R) (fun _ => (cond_var shc c * TT))).
    - apply identity_nonexpansive.
    - apply const_nonexpansive.
Qed.
Next Obligation.
  intros cs; hnf.
  intros.
  destruct x as [[[[c l] shc] shl] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP ()
    LOCAL ()
    SEP (lock_inv shl l R; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun R => lock_inv shl l R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.

Definition signal_spec cs :=
   WITH c : val, shc : share
   PRE [ _cond OF tptr tcond ]
     PROP (readable_share shc)
     LOCAL (temp _cond c)
     SEP (@cond_var cs shc c)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (@cond_var cs shc c).
*)


(* Notes about spawn_thread:

The spawned function has for argument name [_y], which is
existentially quantified.  The function also can use a list of global
variables [globals].

For now, the specification of the spawned function has to be exactly
of the form that you can see below (inside the "match ...").
Cao Qinxiang is working on a notion of sub-specification that might
enable us to have smoother specifications.

The postcondition might not be emp, so we have potential memory leaks
when a thread exists (those maps are still handled by the concurrent
machine).

To enable joinable threads, the postcondition would be [tptr tthread]
with a type [tthread] related to the postcondition through a [thread]
predicate in the logic.  The [join] would then also be implemented
using the oracle, as [acquire] is.  The postcondition would be [match
PrePost with existT ty (w, pre, post) => thread th (post w b)
end] *)

(* @Qinxiang: it would be great to complete the annotation *)

Definition spawn_arg_type := ProdType (ConstType (val * val)) (SigType Type (fun A => ProdType (ProdType
  (ArrowType (ConstType A) (ConstType globals)) (ConstType A))
  (ArrowType (ConstType A) (ArrowType (ConstType val) Mpred)))).

Program Definition spawn_spec :=
  TYPE spawn_arg_type WITH f : _, b : _, fs : _
  PRE [ tptr voidstar_funtype, tptr tvoid ]
    PROP (tc_val (tptr Tvoid) b)
    PARAMS (f; b)
    GLOBALS (let 'existT _ ((gv, w), _) := fs in gv w)
    SEP (let 'existT _ ((gv, w), pre) := fs in
         (func_ptr
           (WITH y : val, x : _
             PRE [ tptr tvoid ]
               PROP ()
               PARAMS (y)
               GLOBALS (gv w)
               SEP (pre x y)
             POST [ tptr tvoid ]
               PROP  ()
               LOCAL ()
               SEP   ())
           f);
         let 'existT _ ((gv, w), pre) := fs in valid_pointer b ∧ pre w b) (* Do we need the valid_pointer here? *)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP ().
Next Obligation.
Proof.
  intros ? ((f, b), (?, ((gv, w), pre))) ((?, ?), (?, ((?, ?), ?))) ([=] & ? & Hfs); simpl in *; subst; simpl in *.
  destruct Hfs as ((Hgv & [=]) & Hpre); simpl in *; subst.
  rewrite Hgv.
  do 5 f_equiv.
  constructor; last constructor; last done.
  - apply func_ptr_si_nonexpansive; last done.
    split3; [done..|].
    exists eq_refl; simpl.
    split; first done.
    split; intros (?, ?); simpl; last done.
    rewrite (Hpre _ _) //.
  - rewrite (Hpre _ _) //.
Qed.
Next Obligation.
Proof.
  intros ? ((f, b), ?) ((?, ?), ?) ?.
  reflexivity.
Qed.


(*+ Adding the specifications to a void ext_spec *)

Context (Z : Type) `{!externalGS Z Σ}.

Definition concurrent_simple_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  nil.

#[local] Instance concurrent_simple_ext_spec (cs : compspecs) (ext_link : string -> ident) : ext_spec OK_ty :=
  add_funspecs_rec OK_ty
    ext_link
    (void_spec OK_ty)
    (concurrent_simple_specs cs ext_link).

Lemma strong_nat_ind (P : nat -> Prop) (IH : forall n, (forall i, lt i n -> P i) -> P n) n : P n.
Proof.
  apply IH; induction n; intros i li; inversion li; eauto.
Qed.

Definition concurrent_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  (ext_link "makelock"%string, makelock_spec cs) ::
  (ext_link "freelock"%string, freelock_spec cs) ::
  (ext_link "spawn"%string, spawn_spec) ::
  nil.

#[export] Instance concurrent_ext_spec (cs : compspecs) (ext_link : string -> ident) : ext_spec OK_ty :=
  add_funspecs_rec OK_ty
    ext_link
    (void_spec OK_ty)
    (concurrent_specs cs ext_link).

End mpred.
