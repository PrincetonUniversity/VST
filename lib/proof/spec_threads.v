Require Import VST.floyd.proofauto.
Require Import VSTlib.threads.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Import VST.veric.rmaps.
Require Import Ensembles.
Notation vint z := (Vint (Int.repr z)).

Local Open Scope logic.

Definition spawn_arg_type := rmaps.ProdType (rmaps.ProdType (rmaps.ProdType (rmaps.ConstType (val * val))
  (rmaps.ArrowType (rmaps.DependentType 0) (rmaps.ConstType globals))) (rmaps.DependentType 0))
  (rmaps.ArrowType (rmaps.DependentType 0) (rmaps.ArrowType (rmaps.ConstType val) rmaps.Mpred)).

Definition spawn_pre :=
  (fun (ts: list Type) (x: val * val * (nth 0 ts unit -> globals) * nth 0 ts unit *
                           (nth 0 ts unit -> val -> mpred)) =>
   match x with
   | (f, b, gv, w, pre) =>
     PROP (tc_val (tptr Ctypes.Tvoid) b)
     PARAMS (f;b) GLOBALS (gv w)
     (SEP (
         (func_ptr'
           (WITH y : val, x : nth 0 ts unit
             PRE [ tptr tvoid ]
               PROP ()
               PARAMS (y) GLOBALS (gv x)
               (SEP   (pre x y))
             POST [ tint ]
               PROP  ()
               RETURN (Vint Int.zero) (* spawned functions must return 0 for now *)
               SEP   ())
           f);
         pre w b))
   end)%argsassert.

Definition spawn_post :=
  (fun (ts: list Type) (x: val * val * (nth 0 ts unit -> globals) * nth 0 ts unit *
                           (nth 0 ts unit -> val -> mpred)) =>
   match x with
   | (f, b, w, pre) =>
     PROP ()
     LOCAL ()
     SEP () (* here's where we'd put a join condition *)
   end).

Lemma approx_idem : forall n P, compcert_rmaps.R.approx n (compcert_rmaps.R.approx n P) =
  compcert_rmaps.R.approx n P.
Proof.
  intros.
  transitivity (base.compose (compcert_rmaps.R.approx n) (compcert_rmaps.R.approx n) P); auto.
  rewrite compcert_rmaps.RML.approx_oo_approx; auto.
Qed.

Lemma funcptr_f_equal' fs fs' v v': fs=fs' -> v=v' -> func_ptr' fs v = func_ptr' fs' v'.
Proof. intros; subst; trivial. Qed.

Import compcert_rmaps.R.

Lemma approx_Sn_eq_weaken:
  forall n a b, approx (S n) a = approx (S n) b -> approx n a = approx n b.
Proof.
intros.
apply predicates_hered.pred_ext.
-
intros ? ?.
destruct H0.
split; auto.
assert (predicates_hered.app_pred (approx (S n) b) a0).
rewrite <- H.
split; auto.
apply H2.
-
intros ? ?.
destruct H0.
split; auto.
assert (predicates_hered.app_pred (approx (S n) a) a0).
rewrite H.
split; auto.
apply H2.
Qed.

Lemma spawn_pre_nonexpansive: @args_super_non_expansive spawn_arg_type spawn_pre.
Proof. repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  unfold LAMBDAx. rewrite !approx_andp; f_equal.
  unfold GLOBALSx, LOCALx; simpl. rewrite !approx_andp. f_equal.
  unfold argsassert2assert. simpl.
  unfold SEPx; simpl. rewrite !sepcon_emp.
  rewrite !approx_sepcon. rewrite approx_idem.
  apply pred_ext; apply sepcon_derives; trivial; apply derives_refl'.
  (* f_equal.*)
  + apply approx_Sn_eq_weaken.
    rewrite approx_func_ptr'.
    setoid_rewrite approx_func_ptr' at 2. apply f_equal.
    apply funcptr_f_equal'; trivial. simpl.
    apply semax_prog.funspec_eq; trivial.
    extensionality tss a rho'; destruct a.
    rewrite !approx_andp, !approx_sepcon, approx_idem; auto.
  + apply approx_Sn_eq_weaken.
    rewrite approx_func_ptr'.
    setoid_rewrite approx_func_ptr' at 2. apply f_equal.
    apply funcptr_f_equal'; trivial. simpl.
    apply semax_prog.funspec_eq; trivial.
    extensionality tss a rho'; destruct a.
    rewrite !approx_andp, !approx_sepcon, approx_idem; auto.
Qed.

Lemma spawn_post_nonexpansive: @super_non_expansive spawn_arg_type spawn_post.
Proof.
  hnf; intros.
  destruct x as [[[]] pre]; auto.
Qed.

Definition spawned_funtype := Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default.

Definition spawn_spec := mk_funspec
  ((tptr spawned_funtype) :: (tptr tvoid) :: nil, tvoid)
  cc_default
  spawn_arg_type
  spawn_pre
  spawn_post
  spawn_pre_nonexpansive
  spawn_post_nonexpansive.

Definition exit_thread_spec :=
  DECLARE _exit_thread
  WITH v : val
  PRE [ tint ]
    PROP ()
    PARAMS (v)
    SEP ()
  POST [ tvoid ]
    PROP (False)
    RETURN ()
    SEP ().

Definition ThreadsASI:funspecs := [
    (_spawn, spawn_spec); exit_thread_spec
 ].


