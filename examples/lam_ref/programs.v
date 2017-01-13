(*
 * Copyright (c) 2009 Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.msl_standard.

Require Import lam_ref_tcb.
Require Import lam_ref_eval.
Require Import lam_ref_mach_defs.
Require Import lam_ref_mach_lemmas.
Require Import lam_ref_type_defs.
Require Import lam_ref_type_safety.
Require Import lam_ref_type_rules.

Definition unary_primop (f:nat -> nat) : expr :=
  Lam (prim (v_Nat oo f) (Var 0)).

Program Definition bin_primop (f:nat -> nat -> nat) : expr :=
  Lam (prim (fun n1 => Lam (prim (fun n2 => v_Nat (f n1 n2)) (Var 0))) (Var 0)).
Next Obligation.
  compute; split; auto.
Qed.

Lemma unary_primop_typ : forall f,
  Typ nil (unary_primop f) (ty_lam ty_nat ty_nat).
Proof.
  intros; unfold unary_primop.
  apply T_Abs.
  apply T_Prim.
  intros.
  unfold val_to_exp, v_Nat; simpl.
  eapply T_Nat.
  apply T_Var; auto.
Qed.

Lemma binary_primop_typ : forall (f:nat -> nat -> nat),
  Typ nil (bin_primop f) (ty_lam ty_nat (ty_lam ty_nat ty_nat)).
Proof.
  intros.
  unfold bin_primop.
  apply T_Abs.
  apply T_Prim; intros.
  unfold val_to_exp; simpl.
  apply T_Abs.
  apply T_Prim; intros.
  unfold val_to_exp, v_Nat; simpl.
  apply T_Nat.
  apply T_Var; auto.
  apply T_Var; auto.
Qed.

Definition ty_bool := ALL a:pred world, ty_lam a (ty_lam a a).
Definition e_true := Lam (Lam (Var 1)).
Definition e_false := Lam (Lam (Var 0)).

Definition e_if b t f :=
  (App (App (App b (Lam t)) (Lam f)) (Nat 0)).

Lemma e_true_typ :
  Typ nil e_true ty_bool.
Proof.
  unfold e_true, ty_bool.
  apply T_UnivI; simpl; intros; auto.
  apply T_Abs.
  apply T_Abs.
  apply T_Var; simpl; auto.
Qed.

Lemma e_false_typ :
  Typ nil e_false ty_bool.
Proof.
  unfold e_false, ty_bool.
  apply T_UnivI; simpl; intros; auto.
  apply T_Abs.
  apply T_Abs.
  apply T_Var; simpl; auto.
Qed.

Lemma T_if : forall G b t f tau,
  Typ G b ty_bool ->
  Typ (TT :: G) t tau ->
  Typ (TT :: G) f tau ->
  Typ G (e_if b t f) tau.
Proof.
  intros.
  unfold e_if.
  apply T_App with TT.
  apply T_App with (ty_lam TT tau).
  apply T_App with (ty_lam TT tau).
  change (ty_lam (ty_lam TT tau) (ty_lam (ty_lam TT tau) (ty_lam TT tau)))
    with ((fun t => ty_lam t (ty_lam t t)) (ty_lam TT tau)).
  apply T_UnivE.
  apply H.
  apply T_Abs; auto.
  apply T_Abs; auto.
  apply T_weaken_nil.
  apply T_sub with ty_nat.
  apply subp_top.
  apply T_Nat.
Qed.

Program Definition isZ : expr -> expr :=
  prim (fun n => if beq_nat n 0 then e_true else e_false).
Solve Obligations using (compute; split; auto).

Lemma T_isZ : forall G e,
  Typ G e ty_nat ->
  Typ G (isZ e) ty_bool.
Proof.
  intros.
  unfold isZ.
  apply T_Prim; intros; auto.
  unfold val_to_exp; simpl.
  destruct (beq_nat n 0); simpl.
  apply e_true_typ.
  apply e_false_typ.
Qed.

Definition e_let (def body:expr) :=
  (App (Lam body) def).

Definition option (a:pred world) :=
  ALL b:pred world, ty_lam b (ty_lam (ty_lam a b) b).

Definition none : expr := Lam (Lam (Var 1)).
Definition some : expr := Lam (Lam (Lam (App (Var 0) (Var 2)))).
Definition out  : expr := Lam (Lam (App (App (Var 0) (Var 1)) (Lam (Var 0)))).

Lemma out_typ :
  Typ nil out (ALL tau:pred world, ty_lam tau (ty_lam (option tau) tau)).
Proof.
  intros.
  unfold out.
  apply T_UnivI; simpl; intros; auto.
  apply T_Abs.
  apply T_Abs.
  eapply T_App with (ty_lam tau tau).
  2: apply T_Abs.
  2: apply T_Var; simpl; auto.
  apply T_App with tau.
  2: apply T_Var; simpl; auto.
  unfold option.
  change (ty_lam tau (ty_lam (ty_lam tau tau) tau))
    with ((fun b => ty_lam b (ty_lam (ty_lam tau b) b)) tau).
  apply T_UnivE.
  apply T_Var; simpl; auto.
Qed.

Lemma none_typ :
  Typ nil none (ALL tau:pred world, option tau).
Proof.
  intros.
  unfold none.
  unfold option.
  apply T_UnivI.
  simpl; auto.
  intros.
  apply T_UnivI.
  simpl; auto.
  intros b.
  apply T_Abs.
  apply T_Abs.
  apply T_Var.
  simpl; auto.
Qed.

Lemma some_typ :
  Typ nil some (ALL tau:pred world, ty_lam tau (option tau)).
Proof.
  unfold some.
  apply T_UnivI; simpl; intros; auto.
  apply T_Abs.
  unfold option.
  apply T_UnivI; simpl; intros; auto.
  apply T_Abs.
  apply T_Abs.
  apply T_App with tau.
  apply T_Var; simpl; auto.
  apply T_Var; simpl; auto.
Qed.

Definition W := (Lam (App (Var 0) (Var 0))).
Definition diverge := App W W.

Definition W_ty Z := fun X => ty_lam X Z.
Lemma W_ty_cont : forall Z, contractive (W_ty Z).
Proof.
  intros.
  unfold W_ty.
  apply ty_lam_contractive.
  hnf; simpl; intros.
  hnf; auto.
  hnf; simpl; repeat intro.
  split; hnf; eauto.
Qed.

Lemma W_typ : forall Z, Typ nil W (Rec (W_ty Z)).
Proof.
  intros.
  rewrite Rec_fold_unfold.
  2: apply W_ty_cont.
  unfold W.
  unfold W_ty.
  apply T_Abs.
  apply T_App with (Rec (W_ty Z)).
  rewrite Rec_fold_unfold.
  2: apply W_ty_cont.
  apply T_Var; auto.
  apply T_Var; auto.
Qed.

Lemma diverge_typ : forall t,
  Typ nil diverge t.
Proof.
  intros.
  unfold diverge.
  apply T_App with (Rec (W_ty t)).
  generalize (W_typ t).
  rewrite Rec_fold_unfold at 1; auto.
  apply W_ty_cont.
  apply W_typ.
Qed.

(* The standard CBV fixpoint combinator *)
Definition Wf := (Lam (App (Var 1) (Lam (App (App (Var 1) (Var 1)) (Var 0))))).
Definition Y := Lam (App Wf Wf).

Definition Wf_ty A B := fun X => ty_lam X (ty_lam A B).
Lemma Wf_ty_cont : forall A B, contractive (Wf_ty A B).
Proof.
  intros.
  unfold Wf_ty.
  apply ty_lam_contractive.
  repeat intro; auto.
  repeat intro; split; repeat intro; auto.
Qed.

Lemma Wf_typ : forall A B,
  Typ (ty_lam (ty_lam A B) (ty_lam A B) :: nil) Wf (Rec (Wf_ty A B)).
Proof.
  intros.
  unfold Wf.
  rewrite Rec_fold_unfold.
  2: apply Wf_ty_cont.
  unfold Wf_ty.
  apply T_Abs.
  apply T_App with (ty_lam A B).
  apply T_Var; simpl; auto.
  apply T_Abs.
  apply T_App with A.
  apply T_App with (Rec (Wf_ty A B)).
  rewrite Rec_fold_unfold at 1.
  2: apply (Wf_ty_cont A B).
  apply T_Var; auto.
  apply T_Var; auto.
  apply T_Var; auto.
Qed.

Lemma Y_typ : forall A B,
  Typ nil Y (ty_lam (ty_lam (ty_lam A B) (ty_lam A B)) (ty_lam A B)).
Proof.
  intros.
  unfold Y.
  apply T_Abs.
  apply T_App with (Rec (Wf_ty A B)).
  generalize (Wf_typ A B).
  rewrite Rec_fold_unfold at 1; auto.
  apply Wf_ty_cont.
  apply Wf_typ.
Qed.

Definition e_fix f := App Y (Lam f).

Lemma fix_ty : forall A B G f,
  Typ (ty_lam A B :: G) f (ty_lam A B) ->
  Typ G (e_fix f) (ty_lam A B).
Proof.
  intros.
  unfold e_fix.
  apply T_App with (ty_lam (ty_lam A B) (ty_lam A B)).
  apply T_weaken_nil.
  apply Y_typ.
  apply T_Abs.
  auto.
Qed.

(* The "backpatching" fixpoint combinator, AKA Landin's knot. *)
Definition refY :=
  Lam (e_let (New (Lam diverge))
             (Update (Var 0) (Lam (App (App (Var 2) (Deref (Var 1))) (Var 0))) (Deref (Var 0)) )).

Lemma refY_typ : forall A B,
  Typ nil refY (ty_lam (ty_lam (ty_lam A B) (ty_lam A B)) (ty_lam A B)).
Proof.
  intros.
  unfold refY.
  apply T_Abs.
  unfold e_let.
  apply T_App with (ty_ref (ty_lam A B)).
  2: apply T_New.
  2: apply T_Abs.
  2: apply T_weaken_nil.
  2: apply diverge_typ.
  apply T_Abs.
  eapply T_Update.
  apply T_Var; simpl; auto.
  apply T_Abs.
  apply T_App with A.
  apply T_App with (ty_lam A B).
  apply T_Var; simpl; auto.
  apply T_Deref.
  apply T_Var; simpl; auto.
  apply T_Var; simpl; auto.
  apply T_Deref.
  apply T_Var; simpl; auto.
Qed.

Definition r_fix f := App refY (Lam f).

Lemma rfix_ty : forall A B G f,
  Typ (ty_lam A B :: G) f (ty_lam A B) ->
  Typ G (r_fix f) (ty_lam A B).
Proof.
  intros.
  unfold r_fix.
  apply T_App with (ty_lam (ty_lam A B) (ty_lam A B)).
  apply T_weaken_nil.
  apply refY_typ.
  apply T_Abs.
  assumption.
Qed.


(* Factorial function
 *)
Definition e_fac : expr :=
  r_fix (Lam
          (e_if (isZ (Var 0))

            (* base case *)
            (Nat 1)

            (* recursive case *)
            (App (App (bin_primop mult) (Var 1))
                 (App (Var 2) (App (unary_primop Peano.pred) (Var 1)))))).

Lemma e_fac_typ :
  Typ nil e_fac (ty_lam ty_nat ty_nat).
Proof.
  unfold e_fac.
  apply rfix_ty.
  apply T_Abs.
  apply T_if.
  apply T_isZ.
  apply T_Var; auto.
  apply T_Nat.
  apply T_App with ty_nat.
  apply T_App with ty_nat.
  apply T_weaken_nil.
  apply binary_primop_typ.
  apply T_Var; auto.
  apply T_App with ty_nat.
  apply T_Var; auto.
  apply T_App with ty_nat.
  apply T_weaken_nil.
  apply unary_primop_typ.
  apply T_Var; auto.
Qed.

(* Demonstrate an example of the factorial program
   working correctly.
 *)
Eval vm_compute in (snd (eval 100 empty_mem (App e_fac (Nat 6)))).


(* Our typed calculus is turing-complete.
   We demonstrate this by embedding the
   "untyped" CBV lambda terms.
   First we define a type U with the characteristic
   equation U = U -> U, and then we show that all closed
   terms formed from abstraction, application and
   variables can be given this type.

   Turing-completeness follows from the fact that
   untyped CBV l-calc is turing-complete.
 *)

Fixpoint isULTerm (e:expr) : Prop :=
  match e with
  | Lam e' => isULTerm e'
  | App e1 e2 => isULTerm e1 /\ isULTerm e2
  | Var _ => True
  | _ => False
  end.

Lemma U_contractive : contractive (fun X => ty_lam X X).
Proof.
  apply ty_lam_contractive; hnf; repeat intro; auto.
Qed.

Definition U := Rec (fun X => ty_lam X X).
Lemma U_eqn : U = ty_lam U U.
Proof.
  unfold U at 1.
  rewrite Rec_fold_unfold; fold U; auto.
  apply U_contractive.
Qed.

Fixpoint Ulist (n:nat) :=
  match n with
  | 0 => nil
  | S n' => U :: Ulist n'
  end.

Lemma ULTyped' : forall e n,
  isULTerm e ->
  closed' n e ->
  Typ (Ulist n) e U.
Proof.
  induction e; simpl; intuition.

  apply T_Var.
  revert n0 H0; induction n; simpl; intros.
  inv H0; simpl; auto.
  destruct n0.
  omegac.
  simpl; apply IHn; omega.

  rewrite U_eqn.
  apply T_Abs.
  apply (IHe (S n)); auto.
  replace (S n) with (n+1) by omega; auto.

  apply T_App with U.
  rewrite <- U_eqn.
  apply IHe1; auto.
  apply IHe2; auto.
Qed.

Theorem ULTyped : forall e,
  closed e /\ isULTerm e ->
  Typ nil e U.
Proof.
  intuition; apply (ULTyped' e 0); auto.
Qed.
