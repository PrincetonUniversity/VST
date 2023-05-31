Require Import VST.veric.SeparationLogic.
Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.expr.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.juicy.semax_conc_pred.
(*Require Import VST.concurrency.conclib.*)
Import Clightdefs.
Import String.

Definition voidstar_funtype := Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default.
(* Definition tlock := Tstruct _lock_t noattr. *)
Definition tlock := (Tarray (Tpointer Ctypes.Tvoid noattr) 2 noattr).

Goal forall (cenv: compspecs), @sizeof cenv tlock = LKSIZE.
Proof. reflexivity. Qed.

Section mpred.

Context `{!heapGS Σ}.

Definition selflock_fun Q sh p : mpred -> mpred :=
  fun R => (Q ∗ ▷lock_inv sh p R).

#[export] Instance lock_inv_nonexpansive sh p : NonExpansive (lock_inv sh p).
Proof.
  intros ????.
  rewrite /lock_inv /LKspec.
  do 9 f_equiv.
  by apply inv_ne.
Qed.

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

Program Definition acquire_spec :=
  WITH v : _, sh : _, R : _
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
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (semax_conc.nonexpansive_super_non_expansive
   (fun R => (PROP (readable_share sh)  PARAMS (v)  SEP (lock_inv sh v R)) gargs)).
  apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
          ((fun _ => readable_share sh) :: nil)
          (v :: nil)
          nil
          ((fun R => lock_inv sh v R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
Qed.
Next Obligation.
Proof.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (semax_conc.nonexpansive_super_non_expansive
   (fun R => (PROP ()  LOCAL ()  SEP (lock_inv sh v R; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun R => lock_inv sh v R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.

Definition release_arg_type: rmaps.TypeTree := rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred.

Program Definition release_spec :=
  TYPE release_arg_type WITH v : _, sh : _, R : _
  PRE [ tptr tvoid ]
     PROP (readable_share sh)
     PARAMS (v)
     SEP (weak_exclusive_mpred R && emp; lock_inv sh v R; R)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v R).
Next Obligation.
Proof.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP (readable_share sh)  PARAMS (v)  SEP (weak_exclusive_mpred R && emp; lock_inv sh v R; R)) gargs)).
  apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
          ((fun _ => readable_share sh) :: nil)
          (v :: nil)
          nil
          ((fun R => weak_exclusive_mpred R && emp) :: (fun R => lock_inv sh v R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun R => weak_exclusive_mpred R)).
    - apply exclusive_mpred_nonexpansive.
    - apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.
Next Obligation.
Proof.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP ()  LOCAL ()  SEP (lock_inv sh v R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun R => lock_inv sh v R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  apply nonexpansive_lock_inv.
Qed.

Program Definition makelock_spec cs: funspec := mk_funspec
  (tptr tvoid :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (v, sh, R) =>
     PROP (writable_share sh)
     PARAMS (v)
     SEP (@data_at_ cs sh tlock v)
   end)
  (fun _ x =>
   match x with
   | (v, sh, R) =>
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v R)
   end)
  _
  _
.
Next Obligation.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  auto.
Qed.
Next Obligation.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP ()  LOCAL ()  SEP (lock_inv sh v R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun R => lock_inv sh v R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  apply nonexpansive_lock_inv.
Qed.

Program Definition freelock_spec cs: funspec := mk_funspec
  (tptr tvoid :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (v, sh, R) =>
     PROP (writable_share sh)
     PARAMS (v)
     SEP (weak_exclusive_mpred R && emp; lock_inv sh v R; R)
   end)
  (fun _ x =>
   match x with
   | (v, sh, R) =>
     PROP ()
     LOCAL ()
     SEP (@data_at_ cs sh tlock v; R)
   end)
  _
  _
.
Next Obligation.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP (writable_share sh)
    PARAMS (v)
    SEP (weak_exclusive_mpred R && emp; lock_inv sh v R; R)) gargs)).
  apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
          ((fun _ => writable_share sh) :: nil)
          (v :: nil) nil
          ((fun R => weak_exclusive_mpred R && emp) :: (fun R => lock_inv sh v R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive weak_exclusive_mpred).
    - apply exclusive_mpred_nonexpansive.
    - apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.
Next Obligation.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP ()  LOCAL ()  SEP (data_at_ sh tlock v; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun _ => data_at_ sh tlock v) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply identity_nonexpansive.
Qed.

(* versions that give away all their resources *)

Lemma selflock_rec : forall sh v R, rec_inv sh v R (selflock R sh v).
Proof.
  intros; unfold rec_inv.
  apply selflock_eq.
Qed.

Program Definition freelock2_spec cs: funspec := mk_funspec
  (tptr tvoid :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ProdType (rmaps.ConstType (val * share * share)) rmaps.Mpred) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (v, sh, sh', Q, R) =>
     PROP (writable_share sh)
     PARAMS (v)
     SEP (weak_exclusive_mpred R && weak_rec_inv sh' v Q R && emp; lock_inv sh v R)
   end)
  (fun _ x =>
   match x with
   | (v, sh, sh', Q, R) =>
     PROP ()
     LOCAL ()
     SEP (@data_at_ cs sh tlock v)
   end)
  _
  _
.
Next Obligation.
  hnf.
  intros.
  destruct x as [[[[v sh] sh'] Q] R]; simpl in *.
  apply (nonexpansive2_super_non_expansive
   (fun Q R => (PROP (writable_share sh)
     PARAMS (v)
     SEP (weak_exclusive_mpred R && weak_rec_inv sh' v Q R && emp; lock_inv sh v R)) gargs));
  [ clear Q R; intros Q;
    apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
            ((fun _ => writable_share sh) :: nil)
            (v :: nil) nil
            ((fun R => weak_exclusive_mpred R && weak_rec_inv sh' v Q R && emp) :: (fun R => lock_inv sh v R) :: nil))
  | clear Q R; intros R;
    apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
            ((fun _ => writable_share sh) :: nil)
            (v :: nil) nil
            ((fun Q => weak_exclusive_mpred R && weak_rec_inv sh' v Q R && emp) :: (fun _ => lock_inv sh v R) :: nil))];
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun R => weak_exclusive_mpred R && weak_rec_inv sh' v Q R)); [apply (conj_nonexpansive weak_exclusive_mpred) |].
    - apply exclusive_mpred_nonexpansive.
    - apply rec_inv1_nonexpansive.
    - apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun Q => weak_exclusive_mpred R && weak_rec_inv sh' v Q R)); [apply (conj_nonexpansive (fun _ => weak_exclusive_mpred R)) |].
    - apply const_nonexpansive.
    - apply rec_inv2_nonexpansive.
    - apply const_nonexpansive.
  + apply const_nonexpansive.
Qed.
Next Obligation.
  hnf.
  intros.
  destruct x as [[[[v sh] sh'] Q] R]; simpl in *.
  auto.
Qed.

Program Definition release2_spec: funspec := mk_funspec
  (tptr tvoid :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (v, sh, Q, R) =>
     PROP (readable_share sh)
     PARAMS (v)
     SEP (weak_exclusive_mpred R && weak_rec_inv sh v Q R && emp; R)
   end)
  (fun _ x =>
   match x with
   | (v, sh, Q, R) =>
     PROP ()
     LOCAL ()
     SEP (emp)
   end)
  _
  _
.
Next Obligation.
  hnf.
  intros.
  destruct x as [[[v sh] Q] R]; simpl in *.
  apply (nonexpansive2_super_non_expansive
   (fun Q R => (PROP (readable_share sh)
     PARAMS (v)
     SEP (weak_exclusive_mpred R && weak_rec_inv sh v Q R && emp; R)) gargs));
  [ clear Q R; intros Q;
    apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
            ((fun _ => readable_share sh) :: nil)
            (v :: nil) nil
            ((fun R => weak_exclusive_mpred R && weak_rec_inv sh v Q R && emp) :: (fun R => R) :: nil))
  | clear Q R; intros R;
    apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
            ((fun _ => readable_share sh) :: nil)
            (v :: nil) nil
            ((fun Q => weak_exclusive_mpred R && weak_rec_inv sh v Q R && emp) :: (fun _ => R) :: nil))];
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun R => weak_exclusive_mpred R && weak_rec_inv sh v Q R)); [apply (conj_nonexpansive (fun R => weak_exclusive_mpred R)) |].
    - apply exclusive_mpred_nonexpansive.
    - apply rec_inv1_nonexpansive.
    - apply const_nonexpansive.
  + apply identity_nonexpansive.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun Q => weak_exclusive_mpred R && weak_rec_inv sh v Q R)); [apply (conj_nonexpansive (fun Q => weak_exclusive_mpred R)) |].
    - apply const_nonexpansive.
    - apply rec_inv2_nonexpansive.
    - apply const_nonexpansive.
  + apply const_nonexpansive.
Qed.
Next Obligation.
  hnf.
  intros.
  destruct x as [[[v sh] Q] R]; simpl in *.
  auto.
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
  (rmaps.ProdType (rmaps.ConstType (val * val * share * share)) rmaps.Mpred)
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
  (rmaps.ProdType (rmaps.ConstType (val * val * share * share)) rmaps.Mpred)
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

Local Open Scope logic.

(* @Qinxiang: it would be great to complete the annotation *)

(*Definition spawn_arg_type := rmaps.ProdType (rmaps.ProdType (rmaps.ProdType (rmaps.ConstType (val * val))
  (rmaps.ArrowType (rmaps.DependentType 0) (rmaps.ConstType globals))) (rmaps.DependentType 0))
  (rmaps.ArrowType (rmaps.DependentType 0) (rmaps.ArrowType (rmaps.ConstType val) rmaps.Mpred)).

Definition spawn_pre :=
  (fun (ts: list Type) (x: val * val * (nth 0 ts unit -> globals) * nth 0 ts unit *
                           (nth 0 ts unit -> val -> mpred)) =>
   match x with
   | (f, b, gv, w, pre) =>
     PROP (tc_val (tptr Tvoid) b)
     PARAMS (f, b)
     GLOBALS  :: temp _args b :: gvars (gv w) :: nil
     (SEP (
       EX _y : ident,
         (func_ptr'
           (WITH y : val, x : nth 0 ts unit
             PRE [ _y OF tptr tvoid ]
               PROP ()
               (LOCALx (temp _y y :: gvars (gv x) :: nil)
               (SEP   (pre x y)))
             POST [tptr tvoid]
               PROP  ()
               LOCAL ()
               SEP   ())
           f);
         valid_pointer b && pre w b))) (* Do we need the valid_pointer here? *)
   end).

Definition spawn_post :=
  (fun (ts: list Type) (x: val * val * (nth 0 ts unit -> globals) * nth 0 ts unit *
                           (nth 0 ts unit -> val -> mpred)) =>
   match x with
   | (f, b, w, pre) =>
     PROP ()
     LOCAL ()
     SEP ()
   end).

Lemma approx_idem : forall n P, compcert_rmaps.R.approx n (compcert_rmaps.R.approx n P) =
  compcert_rmaps.R.approx n P.
Proof.
  intros.
  transitivity (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) P); auto.
  rewrite compcert_rmaps.RML.approx_oo_approx; auto.
Qed.

Lemma spawn_pre_nonexpansive: @super_non_expansive spawn_arg_type spawn_pre.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  unfold LOCALx; simpl; rewrite !approx_andp; f_equal.
  unfold SEPx; simpl; rewrite !sepcon_emp, !approx_sepcon, !approx_andp, ?approx_idem; f_equal.
  rewrite !approx_exp; apply f_equal; extensionality y.
  rewrite approx_func_ptr'.
  setoid_rewrite approx_func_ptr' at 2.
  do 3 f_equal.
  extensionality a rho'; destruct a.
  rewrite !approx_andp, !approx_sepcon, approx_idem; auto.
Qed.

Lemma spawn_post_nonexpansive: @super_non_expansive spawn_arg_type spawn_post.
Proof.
  hnf; intros.
  destruct x as [[[]] pre]; auto.
Qed.

Definition spawn_spec := mk_funspec
  ((_f OF tptr voidstar_funtype)%formals :: (_args OF tptr tvoid)%formals :: nil, tvoid)
  cc_default
  spawn_arg_type
  spawn_pre
  spawn_post
  spawn_pre_nonexpansive
  spawn_post_nonexpansive.*)

(*+ Adding the specifications to a void ext_spec *)

Definition concurrent_simple_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  nil.

Definition concurrent_simple_ext_spec Z (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecs_rec
    ext_link
    (ok_void_spec Z).(@OK_ty)
    (ok_void_spec Z).(@OK_spec)
    (concurrent_simple_specs cs ext_link).

Definition Concurrent_Simple_Espec Z cs ext_link :=
  Build_OracleKind
    Z
    (concurrent_simple_ext_spec Z cs ext_link).

Lemma strong_nat_ind (P : nat -> Prop) (IH : forall n, (forall i, lt i n -> P i) -> P n) n : P n.
Proof.
  apply IH; induction n; intros i li; inversion li; eauto.
Qed.

Set Printing Implicit.

Definition concurrent_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  (ext_link "makelock"%string, makelock_spec cs) ::
  (ext_link "freelock"%string, freelock_spec cs) ::
  (ext_link "spawn"%string, spawn_spec) ::
  nil.

Definition concurrent_ext_spec Z (cs : compspecs) (ext_link : string -> ident) :=
  add_funspecs_rec
    ext_link
    (ok_void_spec Z).(@OK_ty)
    (ok_void_spec Z).(@OK_spec)
    (concurrent_specs cs ext_link).

Definition Concurrent_Espec Z cs ext_link :=
  Build_OracleKind
    Z
    (concurrent_ext_spec Z cs ext_link).

End mpred.