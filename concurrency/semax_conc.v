Require Import VST.msl.msl_standard.
Require Import VST.msl.seplog.
Require Import VST.veric.Clight_base.
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
(*Require Import VST.veric.Clight_new.*)
Require Import VST.veric.res_predicates.
Require Import VST.veric.SeparationLogic.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.jmeq_lemmas.
Require Import VST.floyd.funspec_old.
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.semax_conc_pred.
Import FashNotation.
Import String.
Open Scope funspec_scope.

Set Bullet Behavior "Strict Subproofs".

(* Variables to be instantiated once the program is known. *)
Definition _f := 1%positive.      (* alpha-convertible *)
Definition _args := 2%positive.   (* alpha-convertible *)
Definition _lock := 1%positive.   (* alpha-convertible *)
Definition _cond := 2%positive.   (* alpha-convertible *)
(*Definition _lock_t := 2%positive. (* 2 (* or sometimes 3 -WM *) is the number given by
clightgen when threads.h is included first *)*)

Definition voidstar_funtype := Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default.
(* Definition tlock := Tstruct _lock_t noattr. *)
Definition tlock := (Tarray (Tpointer Ctypes.Tvoid noattr) 2 noattr).
(* Notation tlock := tuint (only parsing). *)

Goal forall (cs: compspecs), @sizeof cs tlock = LKSIZE.
Proof. reflexivity. Qed.

Definition selflock_fun Q sh p : (unit -> mpred) -> (unit -> mpred) :=
  fun R _ => (Q * |>lock_inv sh p (R tt))%logic.

Definition selflock' Q sh p : unit -> mpred := HORec (selflock_fun Q sh p).
Definition selflock Q sh p : mpred := selflock' Q sh p tt.

Lemma nonexpansive_entail (F: pred rmap -> pred rmap) : nonexpansive F -> forall P Q, (P <=> Q |-- F P <=> F Q)%logic.
Proof.
  intros N P Q.
  specialize (N P Q).
  eapply derives_trans; [ eapply derives_trans | ]; [ | apply N | ];
  apply derives_refl.
Qed.

Lemma HOnonexpansive_nonexpansive: forall F: mpred -> mpred, nonexpansive F <-> HOnonexpansive (fun P (_ : unit) => F (P tt)).
Proof.
  intros.
  split; intros; hnf in H |- *.
  + intros P Q.
    specialize (H (P tt) (Q tt)).
    rewrite !allp_unit.
    auto.
  + intros P Q.
    specialize (H (fun x => P) (fun x => Q)).
    rewrite !allp_unit in H.
    auto.
Qed.

Lemma selflock'_eq Q sh p : selflock' Q sh p =
  selflock_fun Q sh p (selflock' Q sh p).
Proof.
  apply HORec_fold_unfold, prove_HOcontractive.
  intros P1 P2 u.
  apply subp_sepcon; [ apply subp_refl | ].
  rewrite <- subp_later.
  repeat intro.
  match goal with |- app_pred (?P >=> ?Q)%logic ?a => change (subtypes.fash (P --> Q) a) end.
  unfold lock_inv; repeat intro.
  destruct H3 as (b & ofs & ? & Hl & ?); exists b, ofs; split; auto; split; auto.
  intro l; specialize (Hl l); simpl in *.
  if_tac; auto.
  destruct Hl as [rsh Hl]; exists rsh; rewrite Hl; repeat f_equal.
  extensionality.
  specialize (H tt); rewrite <- eqp_later in H.
  specialize (H _ H0).
  apply necR_level in H2.
  apply predicates_hered.pred_ext; intros ? []; split; auto.
  - destruct (H a0) as [X _]; [lia|].
    specialize (X _ (necR_refl _)); auto.
  - destruct (H a0) as [_ X]; [lia|].
    specialize (X _ (necR_refl _)); auto.
Qed.

Lemma selflock_eq Q sh p : selflock Q sh p = (Q * |>lock_inv sh p (selflock Q sh p))%logic.
Proof.
  unfold selflock at 1.
  rewrite selflock'_eq.
  reflexivity.
Qed.

Lemma eqp_refl : forall (G : Triv) P, G |-- (P <=> P)%logic.
Proof.
  intros; rewrite andp_dup; apply subp_refl.
Qed.

Lemma eqp_sepcon : forall (G : Triv) (P P' Q Q' : mpred)
  (HP : (G |-- P <=> P')%logic) (HQ : (G |-- Q <=> Q')%logic), (G |-- P * Q <=> P' * Q')%logic.
Proof.
  intros.
  rewrite fash_andp in HP, HQ |- *.
  apply andp_right; apply subp_sepcon; auto; intros ? Ha; destruct (HP _ Ha), (HQ _ Ha); auto.
Qed.

Lemma eqp_andp : forall (G : Triv) (P P' Q Q' : mpred)
  (HP : (G |-- P <=> P')%logic) (HQ : (G |-- Q <=> Q')%logic), G |-- (P && Q <=> P' && Q')%logic.
Proof.
  intros.
  rewrite fash_andp in HP, HQ |- *.
  apply andp_right; apply subp_andp; auto; intros ? Ha; destruct (HP _ Ha), (HQ _ Ha); auto.
Qed.

Lemma eqp_exp : forall (A : Type) (NA : NatDed A) (IA : Indir A) (RecIndir : RecIndir A)
    (G : Triv) (B : Type) (X Y : B -> A),
  (forall x : B, (G |-- X x <=> Y x)%logic) ->
  G |-- ((EX x : _, X x) <=> (EX x : _, Y x))%logic.
Proof.
  intros.
  rewrite fash_andp; apply andp_right; apply subp_exp; intro x; specialize (H x); rewrite fash_andp in H;
    intros ? Ha; destruct (H _ Ha); auto.
Qed.

Lemma lock_inv_nonexpansive2 : forall {A} (P Q : A -> mpred) sh p x, (ALL x : _, |> (P x <=> Q x) |--
  |> lock_inv sh p (P x) <=> |> lock_inv sh p (Q x))%logic.
Proof.
  intros.
  apply allp_left with x.
  rewrite <- eqp_later; apply later_derives.
  apply nonexpansive_entail; apply nonexpansive_lock_inv.
Qed.

Lemma selflock_nonexpansive : forall sh p, nonexpansive (fun P => selflock P sh p).
Proof.
  intros ????.
  unfold selflock, selflock'.
  apply (HORec_nonexpansive _ (fun P => selflock_fun P sh p)).
  - intros ???.
    unfold selflock_fun.
    apply predicates_hered.allp_right; intro.
    apply eqp_sepcon; [apply eqp_refl|].
    match goal with |- _ |-- ?Q => change ((ALL x : _, |> (P0 x <=> Q0 x))%logic |-- Q) end.
    apply lock_inv_nonexpansive2.
  - intros ????.
    unfold selflock_fun.
    apply eqp_sepcon, eqp_refl.
    apply derives_refl.
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
      apply nonexpansive_entail, nonexpansive_lock_inv.
      apply fash_derives, andp_left1, derives_refl.

    (* join resource invariant *)
    repeat apply subp_sepcon; try apply subp_refl.
      apply allp_left with true.
      eapply derives_trans.
        apply nonexpansive_entail, nonexpansive_lock_inv.
        apply fash_derives, andp_left1, derives_refl.

      apply allp_left with false.
      eapply derives_trans.
        apply nonexpansive_entail, nonexpansive_lock_inv.
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

(* Condition variables *)
(*Definition _cond_t := 4%positive.*)
Definition tcond := tint.

(* Does this need to be anything special? *)
Definition cond_var {cs} sh v := @data_at_ cs sh tcond v.

(*+ Specification of each concurrent primitive *)

Lemma approx_eq_i':
  forall (P Q : pred rmap) n,
  (|> (P <=> Q))%pred n -> approx n P = approx n Q.
Proof.
  intros.
apply pred_ext'; extensionality m'.
unfold approx.
apply and_ext'; auto; intros.
specialize (H (level m')); spec H; [simpl; apply later_nat; auto |].
specialize (H m').
spec H; [lia |].
destruct H.
specialize (H m').
specialize (H1 m').
apply prop_ext; split; auto.
Qed.

Lemma fash_equiv_approx: forall n (R: pred rmap),
  (|> (R <=> approx n R))%pred n.
Proof.
  intros.
  intros m ? x ?; split; intros y ? ?.
  + apply approx_lt; auto.
    apply necR_level in H1.
    apply later_nat in H; lia.
  + eapply approx_p; eauto.
Qed.

Lemma nonexpansive_super_non_expansive: forall (F: mpred -> mpred),
  nonexpansive F ->
  forall R n,
  approx n (F R) = approx n (F (approx n R)).
Proof.
  intros.
  apply approx_eq_i'.
  intros m ?.
  pose proof nonexpansive_entail _ H R (approx n R) m.
  apply H1.
  clear - H0.
  apply (fash_equiv_approx n R m); auto.
Qed.

Lemma nonexpansive2_super_non_expansive: forall (F: mpred -> mpred -> mpred),
  (forall P, nonexpansive (fun Q => F P Q)) ->
  (forall Q, nonexpansive (fun P => F P Q)) ->
  forall P Q n,
  approx n (F P Q) = approx n (F (approx n P) (approx n Q)).
Proof.
  intros.
  apply approx_eq_i'.
  intros m ?.
  pose proof nonexpansive_entail _ (H P) Q (approx n Q) m; cbv beta in H2.
  spec H2; [apply (fash_equiv_approx n Q m); auto |].
  pose proof nonexpansive_entail _ (H0 (approx n Q)) P (approx n P) m; cbv beta in H3.
  spec H3; [apply (fash_equiv_approx n P m); auto |].
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

Definition acquire_pre: val * share * mpred -> argsEnviron -> mpred :=
  fun args =>
  match args with
  | (v, sh, R) =>
     PROP (readable_share sh)
     PARAMS (v) GLOBALS ()
     SEP (lock_inv sh v R)
  end%argsassert.

Notation acquire_post :=
  (fun args =>
  match args with
  | (v, sh, R) =>
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v R; R)
  end).
(*
Lemma NP_acquire_pre: @super_non_expansive acquire_arg_type (fun _ => acquire_pre).
Proof.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP (readable_share sh)  LOCAL (temp _lock v)  SEP (lock_inv sh v R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          ((fun _ => readable_share sh) :: nil)
          ((temp _lock v) :: nil)
          ((fun R => lock_inv sh v R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + unfold compose. apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
Qed.*)

Lemma NP_acquire_pre: @args_super_non_expansive acquire_arg_type (fun _ => acquire_pre).
Proof.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  unfold PROPx. simpl. rewrite 2 approx_andp. f_equal.
  unfold LAMBDAx. simpl. rewrite 2 approx_andp. f_equal.
  unfold GLOBALSx, LOCALx. simpl. rewrite 2 approx_andp. f_equal. 
  unfold argsassert2assert, SEPx. simpl. rewrite 2 sepcon_emp.
  apply nonexpansive_super_non_expansive. apply nonexpansive_lock_inv.
Qed.

Lemma NP_acquire_post: @super_non_expansive acquire_arg_type (fun _ => acquire_post).
Proof.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP ()  LOCAL ()  SEP (lock_inv sh v R; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          nil
          nil
          ((fun R => lock_inv sh v R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.

Definition acquire_spec: funspec := mk_funspec
  (tptr Ctypes.Tvoid :: nil, tvoid)
  cc_default
  acquire_arg_type
  (fun _ => acquire_pre)
  (fun _ => acquire_post)
  NP_acquire_pre
  NP_acquire_post
.

Definition release_arg_type: rmaps.TypeTree := rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred.

Definition release_pre: val * share * mpred -> argsEnviron -> mpred :=
  fun args =>
  match args with
  | (v, sh, R) =>
     PROP (readable_share sh)
     PARAMS (v) GLOBALS ()
     SEP (weak_exclusive_mpred R && emp; lock_inv sh v R; R)
  end%argsassert.

Notation release_post :=
  (fun args =>
  match args with
  | (v, sh, R) =>
     PROP ()
     LOCAL ()
     SEP (lock_inv sh v R)
  end).

(*
Lemma NP_release_pre: @super_non_expansive release_arg_type (fun _ => release_pre).
Proof.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive
   (fun R => (PROP (readable_share sh)  LOCAL (temp _lock v)  SEP (weak_exclusive_mpred R && emp; lock_inv sh v R; R)) rho)).
  apply (PROP_LOCAL_SEP_nonexpansive
          ((fun _ => readable_share sh) :: nil)
          ((temp _lock v) :: nil)
          ((fun R => weak_exclusive_mpred R && emp)%logic :: (fun R => lock_inv sh v R) :: (fun R => R) :: nil));
  repeat apply Forall_cons; try apply Forall_nil.
  + apply const_nonexpansive.
  + apply (conj_nonexpansive (fun R => weak_exclusive_mpred R)%logic).
    - apply exclusive_mpred_nonexpansive.
    - apply const_nonexpansive.
  + apply nonexpansive_lock_inv.
  + apply identity_nonexpansive.
Qed.*)

Lemma NP_release_pre: @args_super_non_expansive release_arg_type (fun _ => release_pre).
Proof.
  hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  unfold PROPx. simpl. rewrite 2 approx_andp. f_equal.
  unfold LAMBDAx. simpl. rewrite 2 approx_andp. f_equal.
  unfold GLOBALSx, LOCALx. simpl. rewrite 2 approx_andp. f_equal. 
  unfold argsassert2assert. simpl. unfold SEPx; simpl. rewrite 2 sepcon_emp.
  rewrite -> ! approx_sepcon. f_equal. 
  + apply (nonexpansive_super_non_expansive (fun R => weak_exclusive_mpred R && emp))%logic.
    apply (conj_nonexpansive (fun R => weak_exclusive_mpred R)%logic).
    - apply exclusive_mpred_nonexpansive.
    - apply const_nonexpansive.
  + f_equal.
    - apply (nonexpansive_super_non_expansive). apply nonexpansive_lock_inv.
    - remember (approx n (approx n R)). rewrite <- (approx_oo_approx n). subst.
      reflexivity.
Qed. 

Lemma NP_release_post: @super_non_expansive release_arg_type (fun _ => release_post).
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

Definition release_spec: funspec := mk_funspec
  (*((_lock OF tptr Tvoid)%formals :: nil, tvoid)*)
  ((tptr Ctypes.Tvoid) :: nil, tvoid)
  cc_default
  release_arg_type
  (fun _ => release_pre)
  (fun _ => release_post)
  NP_release_pre
  NP_release_post
.

Program Definition makelock_spec cs: funspec := mk_funspec
  (*((_lock OF tptr Tvoid)%formals :: nil, tvoid)*)
  ((tptr Ctypes.Tvoid) :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (v, sh, R) =>
     PROP (writable_share sh)
     PARAMS (v) GLOBALS ()
     SEP (@data_at_ cs sh tlock v)
   end)%argsassert
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
  intros cs; hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  auto.
Qed.
Next Obligation.
  intro cs; hnf.
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
  (*((_lock OF tptr Tvoid)%formals :: nil, tvoid)*)
  ((tptr Ctypes.Tvoid) :: nil, tvoid)
 cc_default
  (rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (v, sh, R) =>
     PROP (writable_share sh)
     PARAMS (v) GLOBALS()
     SEP (weak_exclusive_mpred R && emp; lock_inv sh v R; R)
   end)%argsassert
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
  intro cs; hnf.
  intros.
  destruct x as [[v sh] R]; simpl in *.
  apply (nonexpansive_super_non_expansive (fun R => (PROP (writable_share sh)
    PARAMS(v) GLOBALS()
    SEP (weak_exclusive_mpred R && emp; lock_inv sh v R; R))%argsassert gargs)).
  unfold PARAMSx, GLOBALSx, SEPx, PROPx, LOCALx, argsassert2assert. simpl. 
  apply (conj_nonexpansive (fun R0 : mpred => (!! (writable_share sh /\ True)))
    (fun R0 => (!! (snd gargs = v :: nil) &&
     (local (liftx True) (Clight_seplog.mkEnv (fst gargs) nil nil) &&
      (weak_exclusive_mpred R0 && emp * (lock_inv sh v R0 * (R0 * emp)))))))%logic.
  apply const_nonexpansive.
  apply (conj_nonexpansive (fun R0 : pred rmap => (!! (snd gargs = v :: nil)))
          (fun R0 => (local (liftx True) (Clight_seplog.mkEnv (fst gargs) nil nil) &&
     (weak_exclusive_mpred R0 && emp * (lock_inv sh v R0 * (R0 * emp))))))%logic.
  apply const_nonexpansive.
  apply (conj_nonexpansive
         (fun R0 : pred rmap => (local (liftx True) (Clight_seplog.mkEnv (fst gargs) nil nil)))
         (fun R0 : pred rmap => (weak_exclusive_mpred R0 && emp * (lock_inv sh v R0 * (R0 * emp)))))%logic.
  apply const_nonexpansive.
  apply sepcon_nonexpansive.
  apply (conj_nonexpansive (fun x =>weak_exclusive_mpred x) (fun x => emp)). apply exclusive_mpred_nonexpansive.
  apply const_nonexpansive.
  apply sepcon_nonexpansive.
  apply nonexpansive_lock_inv.
  apply sepcon_nonexpansive. 
  apply identity_nonexpansive.
  apply const_nonexpansive.
Qed.
Next Obligation.
  intro cs; hnf.
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
  (*((_lock OF tptr Tvoid)%formals :: nil, tvoid)*)
  ((tptr Ctypes.Tvoid)%formals :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ProdType (rmaps.ConstType (val * share * share)) rmaps.Mpred) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (v, sh, sh', Q, R) =>
     PROP (writable_share sh)
     PARAMS (v) GLOBALS ()
     SEP (weak_exclusive_mpred R && weak_rec_inv sh' v Q R && emp; lock_inv sh v R)
   end)%argsassert
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
  intro cs; hnf.
  intros.
  destruct x as [[[[v sh] sh'] Q] R]; simpl in *.
  apply (nonexpansive2_super_non_expansive
   (fun Q R => (PROP (writable_share sh)
     PARAMS (v) GLOBALS()
     SEP (weak_exclusive_mpred R && weak_rec_inv sh' v Q R && emp; lock_inv sh v R))%argsassert gargs));
  [ clear Q R; intros Q;
    apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
            ((fun _ => writable_share sh) :: nil)
            (v :: nil) nil
            ((fun R => weak_exclusive_mpred R && weak_rec_inv sh' v Q R && emp)%logic :: (fun R => lock_inv sh v R) :: nil) gargs)
  | clear Q R; intros R;
    apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
            ((fun _ => writable_share sh) :: nil)
            (v :: nil) nil
            ((fun Q => weak_exclusive_mpred R && weak_rec_inv sh' v Q R && emp)%logic :: (fun _ => lock_inv sh v R) :: nil) gargs)];
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
  intro cs; hnf.
  intros.
  destruct x as [[[[v sh] sh'] Q] R]; simpl in *.
  auto.
Qed.

Program Definition release2_spec: funspec := mk_funspec
  (*((_lock OF tptr Tvoid)%formals :: nil, tvoid)*)
  ((tptr Ctypes.Tvoid) :: nil, tvoid)
 cc_default
  (rmaps.ProdType (rmaps.ProdType (rmaps.ConstType (val * share)) rmaps.Mpred) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (v, sh, Q, R) =>
     PROP (readable_share sh)
     PARAMS (v) GLOBALS ()
     SEP (weak_exclusive_mpred R && weak_rec_inv sh v Q R && emp; R)
   end)%argsassert
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
  intro cs; hnf.
  intros.
  destruct x as [[[v sh] Q] R]; simpl in *.
  apply (nonexpansive2_super_non_expansive
   (fun Q R => (PROP (readable_share sh)
            PARAMS (v) GLOBALS()
     SEP (weak_exclusive_mpred R && weak_rec_inv sh v Q R && emp; R))%argsassert gargs));
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
  intro cs; hnf.
  intros.
  destruct x as [[[v sh] Q] R]; simpl in *.
  auto.
Qed.

(* condition variables *)
Definition makecond_spec cs :=
   WITH v : val, sh : share
   PRE [ (*_cond OF*) tptr tcond ]
     PROP (writable_share sh)
     (*LOCAL (temp _cond v)*) PARAMS (v) GLOBALS ()
     SEP (@data_at_ cs sh tcond v)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (cond_var sh v).

Definition freecond_spec cs :=
   WITH v : val, sh : share
   PRE [ (*_cond OF*) tptr tcond ]
     PROP (writable_share sh)
     (*LOCAL (temp _cond v)*) PARAMS (v) GLOBALS ()
     SEP (@cond_var cs sh v)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (@data_at_ cs sh tcond v).

Program Definition wait_spec cs: funspec := mk_funspec
 (* ((_cond OF tptr tcond)%formals :: (_lock OF tptr Tvoid)%formals :: nil, tvoid)*)
  ((tptr tcond) :: (tptr Ctypes.Tvoid) :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ConstType (val * val * share * share)) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (c, l, shc, shl, R) =>
     PROP (readable_share shc)
     PARAMS (c;l) GLOBALS ()
     SEP (@cond_var cs shc c; lock_inv shl l R; R)
   end)%argsassert
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
    PARAMS (c;l) GLOBALS ()
    SEP (cond_var shc c; lock_inv shl l R; R))%argsassert gargs)).
  apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
          ((fun _ => readable_share shc) :: nil)
          (*(temp _cond c :: temp _lock l :: nil)*)(c::l :: nil) nil
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
  (*((_cond OF tptr tcond)%formals :: (_lock OF tptr Tvoid)%formals :: nil, tvoid)*)
  ((tptr tcond)%formals :: (tptr Ctypes.Tvoid)%formals :: nil, tvoid)
  cc_default
  (rmaps.ProdType (rmaps.ConstType (val * val * share * share)) rmaps.Mpred)
  (fun _ x =>
   match x with
   | (c, l, shc, shl, R) =>
     PROP (readable_share shc)
     PARAMS (c;l) GLOBALS ()
     SEP (lock_inv shl l R; R && (@cond_var cs shc c * TT))
   end)%argsassert
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
    PARAMS (c;l) GLOBALS ()
    SEP (lock_inv shl l R; R && (@cond_var cs shc c * TT)))%argsassert gargs)).
  apply (PROP_PARAMS_GLOBALS_SEP_nonexpansive
          ((fun _ => readable_share shc) :: nil)
          (c::l::nil) nil
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
   PRE [ (*_cond OF*) tptr tcond ]
     PROP (readable_share shc)
     (*LOCAL (temp _cond c)*)PARAMS (c) GLOBALS ()
     SEP (@cond_var cs shc c)
   POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (@cond_var cs shc c).



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

Definition spawn_arg_type := rmaps.ProdType (rmaps.ProdType (rmaps.ProdType (rmaps.ConstType (val * val))
  (rmaps.ArrowType (rmaps.DependentType 0) (rmaps.ConstType globals))) (rmaps.DependentType 0))
  (rmaps.ArrowType (rmaps.DependentType 0) (rmaps.ArrowType (rmaps.ConstType val) rmaps.Mpred)).

Definition spawn_pre :=
  (fun (ts: list Type) (x: val * val * (nth 0 ts unit -> globals) * nth 0 ts unit *
                           (nth 0 ts unit -> val -> mpred)) =>
   match x with
   | (f, b, gv, w, pre) =>
     PROP (tc_val (tptr Ctypes.Tvoid) b)
     (*(LOCALx (temp _f f :: temp _args b :: gvars (gv w) :: nil)*)
     PARAMS (f;b) GLOBALS (gv w)
     (SEP (
       EX _y : ident,
         (func_ptr'
           (WITH y : val, x : nth 0 ts unit
             PRE [ (*_y OF *)tptr tvoid ]
               PROP ()
               (*(LOCALx (temp _y y :: gvars (gv x) :: nil)*) PARAMS (y) GLOBALS (gv x)
               (SEP   (pre x y)) (*)*)
             POST [tptr tvoid]
               PROP  ()
               LOCAL ()
               SEP   ())
           f);
         pre w b)) (*)*)
   end)%argsassert.

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

Lemma approx_idem' : forall n P, approx n (approx n P) =
  approx n P.
Proof. intros. apply approx_idem. Qed.
(*
Lemma spawn_pre_nonexpansive: @super_non_expansive spawn_arg_type spawn_pre.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx; simpl; rewrite !approx_andp; f_equal.
  unfold LOCALx; simpl; rewrite !approx_andp; f_equal.
  unfold SEPx; simpl; rewrite !sepcon_emp, !approx_sepcon, ?approx_idem; f_equal.
  rewrite !approx_exp; apply f_equal; extensionality y.
  rewrite approx_func_ptr'.
  setoid_rewrite approx_func_ptr' at 2.
  do 3 f_equal.
  extensionality a rho'; destruct a.
  rewrite !approx_andp, !approx_sepcon, approx_idem; auto.
Qed.*)

Lemma approx_derives_e {n P Q}: @derives mpred Nveric  P Q -> @derives mpred Nveric (approx n P) (approx n Q).
Proof. intros. apply approx_hered_derives_e. apply H. Qed.

Lemma funcptr_f_equal' fs fs' v v': fs=fs' -> v=v' -> func_ptr' fs v = func_ptr' fs' v'.
Proof. intros; subst; trivial. Qed.

Lemma approx_Sn_eq_weaken:
  forall n a b, approx (S n) a = approx (S n) b -> approx n a = approx n b.
Proof.
intros.
apply predicates_hered.pred_ext.
-
intros ? ?.
destruct H0.
split; auto.
assert (approx (S n) b a0).
rewrite <- H.
split; auto.
apply H2.
-
intros ? ?.
destruct H0.
split; auto.
assert (approx (S n) a a0).
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
  + rewrite !approx_exp; apply f_equal; extensionality y.
    apply approx_Sn_eq_weaken.
    rewrite approx_func_ptr'.
    setoid_rewrite approx_func_ptr' at 2. apply f_equal.
    apply funcptr_f_equal'; trivial. simpl.
    apply semax_prog.funspec_eq; trivial.
    extensionality tss a rho'; destruct a.
    rewrite !approx_andp, !approx_sepcon, approx_idem; auto.
  + rewrite !approx_exp; apply f_equal; extensionality y.
    apply approx_Sn_eq_weaken.
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

Definition spawn_spec := mk_funspec
  (*((_f OF tptr voidstar_funtype)%formals :: (_args OF tptr tvoid)%formals :: nil, tvoid)*)
  ((tptr voidstar_funtype)%formals :: (tptr tvoid)%formals :: nil, tvoid)
  cc_default
  spawn_arg_type
  spawn_pre
  spawn_post
  spawn_pre_nonexpansive
  spawn_post_nonexpansive.

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
