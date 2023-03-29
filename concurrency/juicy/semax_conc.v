Require Import VST.msl.msl_standard.
Require Import VST.msl.seplog.
Require Import VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.juicy_mem_ops.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.semax.
Require Import VST.veric.semax_call.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.Clight_core.
Require Import VST.veric.res_predicates.
Require Import VST.veric.SeparationLogic.
Require Import VST.sepcomp.extspec.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.jmeq_lemmas.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.conclib.
Import Clightdefs.
Import String.

(*(* Variables to be instantiated once the program is known. *)
Definition _f := 1%positive.      (* alpha-convertible *)
Definition _args := 2%positive.   (* alpha-convertible *)
Definition _lock := 1%positive.   (* alpha-convertible *)
Definition _cond := 2%positive.   (* alpha-convertible *)
(*Definition _lock_t := 2%positive. (* 2 (* or sometimes 3 -WM *) is the number given by
clightgen when threads.h is included first *)*)
*)

Definition voidstar_funtype := Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default.
(* Definition tlock := Tstruct _lock_t noattr. *)
Definition tlock := (Tarray (Tpointer Ctypes.Tvoid noattr) 2 noattr).
(* Notation tlock := tuint (only parsing). *)

Goal forall (cenv: compspecs), @sizeof cenv tlock = LKSIZE.
Proof. reflexivity. Qed.

Definition selflock_fun Q sh p : (unit -> mpred) -> (unit -> mpred) :=
  fun R _ => (Q * |>lock_inv sh p (R tt))%logic.

Definition selflock' Q sh p : unit -> mpred := HORec (selflock_fun Q sh p).
Definition selflock Q sh p : mpred := selflock' Q sh p tt.

Lemma HOnonexpansive_nonexpansive: forall F: mpred -> mpred, nonexpansive F <-> HOnonexpansive (fun P (_ : unit) => F (P tt)).
Proof.
  intros.
  split; intros; hnf in H |- *.
  + intros P Q.
    specialize (H (P tt) (Q tt)).
    rewrite !allp_unit.
    constructor; auto.
  + intros P Q.
    specialize (H (fun x => P) (fun x => Q)).
    rewrite !allp_unit in H.
    destruct H; auto.
Qed.

Lemma selflock'_eq Q sh p : selflock' Q sh p =
  selflock_fun Q sh p (selflock' Q sh p).
Proof.
  apply HORec_fold_unfold, prove_HOcontractive'.
  intros P1 P2 u.
  apply subp_sepcon; [ apply subp_refl | ].
  apply allp_left with tt.
  eapply derives_trans, subp_later1.
  apply later_derives.
  constructor.
  eapply predicates_hered.derives_trans, eqp_subp.
  apply nonexpansive_lock_inv.
Qed.

Lemma selflock_eq Q sh p : selflock Q sh p = (Q * |>lock_inv sh p (selflock Q sh p))%logic.
Proof.
  unfold selflock at 1.
  rewrite selflock'_eq.
  reflexivity.
Qed.

(* In fact we need locks to two resources:
   1) the resource invariant, for passing the resources
   2) the join resource invariant, for returning all resources, including itself
   for this we need to define them in a mutually recursive fashion: *)

Definition res_invariants_fun Q sh1 p1 sh2 p2 : (bool -> mpred) -> (bool -> mpred) :=
  fun R b =>
    if b then
      (Q * lock_inv sh2 p2 (|> R false))%logic
    else
      (Q * lock_inv sh1 p1 (|> R true) * lock_inv sh2 p2 (|> R false))%logic.

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
  lock_inv sh2 p2 (|> join_res_invariant Q sh1 p1 sh2 p2))%logic.
Proof.
  unfold res_invariant at 1.
  rewrite res_invariants_eq.
  reflexivity.
Qed.

Lemma join_res_invariant_eq Q sh1 p1 sh2 p2 :
  join_res_invariant Q sh1 p1 sh2 p2 =
  (Q *
  lock_inv sh1 p1 (|> res_invariant Q sh1 p1 sh2 p2) *
  lock_inv sh2 p2 (|> join_res_invariant Q sh1 p1 sh2 p2))%logic.
Proof.
  unfold join_res_invariant at 1.
  rewrite res_invariants_eq.
  reflexivity.
Qed.

(*+ Specification of each concurrent primitive *)

Lemma nonexpansive2_super_non_expansive: forall (F: mpred -> mpred -> mpred),
  (forall P, nonexpansive (fun Q => F P Q)) ->
  (forall Q, nonexpansive (fun P => F P Q)) ->
  forall P Q n,
  approx n (F P Q) = approx n (F (approx n P) (approx n Q)).
Proof.
  intros.
  apply semax_conc.approx_eq_i'.
  intros m ?.
  pose proof semax_conc.nonexpansive_entail _ (H P) Q (approx n Q) as H2; cbv beta in H2.
  destruct H2 as [H2]; specialize (H2 m). spec H2; [apply (semax_conc.fash_equiv_approx n Q m); auto |].
  pose proof semax_conc.nonexpansive_entail _ (H0 (approx n Q)) P (approx n P) as H3; cbv beta in H3.
  destruct H3 as [H3]; specialize (H3 m). spec H3; [apply (semax_conc.fash_equiv_approx n P m); auto |].
  remember (F P Q) as X1.
  remember (F P (approx n Q)) as X2.
  remember (F (approx n P) (approx n Q)) as X3.
  clear - H2 H3.
  change ((X1 <=> X2)%pred m) in H2.
  change ((X2 <=> X3)%pred m) in H3.
  intros y H; specialize (H2 y H); specialize (H3 y H).
  destruct H2 as [H2A H2B], H3 as [H3A H3B].
  split; intros z H0.
  + specialize (H2A z H0); specialize (H3A z H0); auto.
  + specialize (H2B z H0); specialize (H3B z H0); auto.
Qed.

(*
Lemma nonexpansive_2super_non_expansive: forall {A B: Type} (F: (A -> B -> mpred) -> mpred),
  (forall a b, nonexpansive (fun Q => F P Q)) ->
  (forall Q, nonexpansive (fun P => F P Q)) ->
  forall P Q n,
  approx n (F P Q) = approx n (F (approx n P) (approx n Q)).
*)
Definition acquire_arg_type: rmaps.TypeTree := rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred.

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
          ((fun R => weak_exclusive_mpred R && emp)%logic :: (fun R => lock_inv sh v R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun R => weak_exclusive_mpred R)%logic).
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
          ((fun R => weak_exclusive_mpred R && emp)%logic :: (fun R => lock_inv sh v R) :: (fun R => R) :: nil));
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
            ((fun R => weak_exclusive_mpred R && weak_rec_inv sh' v Q R && emp)%logic :: (fun R => lock_inv sh v R) :: nil))
  | clear Q R; intros R;
    apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
            ((fun _ => writable_share sh) :: nil)
            (v :: nil) nil
            ((fun Q => weak_exclusive_mpred R && weak_rec_inv sh' v Q R && emp)%logic :: (fun _ => lock_inv sh v R) :: nil))];
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun R => weak_exclusive_mpred R && weak_rec_inv sh' v Q R)%logic); [apply (conj_nonexpansive weak_exclusive_mpred) |].
    - apply exclusive_mpred_nonexpansive.
    - apply rec_inv1_nonexpansive.
    - apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun Q => weak_exclusive_mpred R && weak_rec_inv sh' v Q R)%logic); [apply (conj_nonexpansive (fun _ => weak_exclusive_mpred R)) |].
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
            ((fun R => weak_exclusive_mpred R && weak_rec_inv sh v Q R && emp)%logic :: (fun R => R) :: nil))
  | clear Q R; intros R;
    apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
            ((fun _ => readable_share sh) :: nil)
            (v :: nil) nil
            ((fun Q => weak_exclusive_mpred R && weak_rec_inv sh v Q R && emp)%logic :: (fun _ => R) :: nil))];
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun R => weak_exclusive_mpred R && weak_rec_inv sh v Q R)%logic); [apply (conj_nonexpansive (fun R => weak_exclusive_mpred R)%logic) |].
    - apply exclusive_mpred_nonexpansive.
    - apply rec_inv1_nonexpansive.
    - apply const_nonexpansive.
  + apply identity_nonexpansive.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun Q => weak_exclusive_mpred R && weak_rec_inv sh v Q R)%logic); [apply (conj_nonexpansive (fun Q => weak_exclusive_mpred R)%logic) |].
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
          ((fun R => lock_inv shl l R) :: (fun R => R && (@cond_var cs shc c * TT))%logic :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply (conj_nonexpansive (fun R => R) (fun _ => (cond_var shc c * TT)%logic)).
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

Require Import VST.atomics.SC_atomics_base.

Parameter (AI : atomic_int_impl).
(* We might need to make this concrete. *)

(*+ Adding the specifications to a void ext_spec *)

Definition concurrent_simple_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  (ext_link "make_atomic"%string, @make_atomic_spec AI) ::
  (ext_link "free_atomic"%string, @free_atomic_spec AI) ::
  (ext_link "atomic_load"%string, @atomic_load_spec AI) ::
  (ext_link "atomic_store"%string, @atomic_store_spec AI) ::
  (ext_link "atomic_CAS"%string, atomic_CAS_spec(AI := AI)) ::
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

Definition concurrent_specs (cs : compspecs) (ext_link : string -> ident) :=
  (ext_link "acquire"%string, acquire_spec) ::
  (ext_link "release"%string, release_spec) ::
  (ext_link "makelock"%string, makelock_spec cs) ::
  (ext_link "freelock"%string, freelock_spec cs) ::
  (ext_link "make_atomic"%string, @make_atomic_spec AI) ::
  (ext_link "free_atomic"%string, @free_atomic_spec AI) ::
  (ext_link "atomic_load"%string, @atomic_load_spec AI) ::
  (ext_link "atomic_store"%string, @atomic_store_spec AI) ::
  (ext_link "atomic_CAS"%string, atomic_CAS_spec(AI := AI)) ::
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
