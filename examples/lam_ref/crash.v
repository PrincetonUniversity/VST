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

Require Import programs.

(** Here we prove that the "obvious" typing rule
    for allp introduction is incorrect.
    The correct rule has the "value restriction."

    We want to show that this typing rule would
    allow us to type an unsafe program.

    Here is the form of the incorrect rule.
 *)

Definition bad_UnivI_rule :=
  forall G e (X:pred world -> pred world),
    (forall tau, Typ G e (X tau)) ->
    Typ G e (allp X).


(* Here is the program.  The problem is that the
   reference 'r' is used at two incompatible types.
   This program eventually attepmts to apply
   the nat 5 to the nat 42 which gets stuck.

   The program, in pseudo-ML, is:

     let f :=
         (let r := new none in
            fun x => r := some x; r) in
     let a := f (fun z => z) in
     let b := f 5 in
     out (fun z => z) (!a) 42

 *)
Definition crash :=
  e_let
    (* f := *)
    ( e_let (* r := *) (New none) (* in *)
       (Lam (* x *)
          (Update (Var 1 (*r*))
             (*:=*) (App some (Var 0 (*x*)))
             (* ; *) (Var 1 (*r*)))))
    (* in *)
    ( e_let (* a := *) (App (Var 0 (*f*)) (Lam (Var 0))) (* in *)
     (e_let (* b := *) (App (Var 1 (*f*)) (Nat 5))       (* in *)
       (App (App (App out (Lam (Var 0))) (Deref (Var 1 (*a*)))) (Nat 42))
     )).

Lemma crash_steps : exists m,
  stepstar (empty_mem, crash) (m, App (Nat 5) (Nat 42)).
Proof.
  intros.
  case_eq (eval 100 empty_mem crash); intros.
  exists m.
  apply eval_correct with 100%Z.
  compute in *; congruence.
Qed.

Lemma crash_unsafe : ~safe_prog crash.
Proof.
  intros H.
  destruct crash_steps as [m Hst].
  spec H empty_mem (m,App (Nat 5) (Nat 42)) Hst.
  destruct H; inv H.
  inv H0.
  inv H4.
  simpl in H1; auto.
Qed.

(* Typing derivation for "crash" which uses the
   incorrect rule.
 *)
Lemma bad_rule_crash :
  bad_UnivI_rule -> Typ nil crash ty_nat.
Proof.
  intros.
  unfold crash.
  unfold e_let at 1.
  apply T_App with (ALL tau:pred world, ty_lam tau (ty_ref (option tau))).
  apply T_Abs.
  unfold e_let at 1.
  apply T_App with (ty_ref (option (ty_lam ty_nat ty_nat))).
  apply T_Abs.
  unfold e_let at 1.
  apply T_App with (ty_ref (option ty_nat)).
  apply T_Abs.
  apply T_App with ty_nat.
  apply T_App with (option (ty_lam ty_nat ty_nat)).
  apply T_App with (ty_lam ty_nat ty_nat).
  apply T_weaken_nil.
  change (ty_lam (ty_lam ty_nat ty_nat)
    (ty_lam (option (ty_lam ty_nat ty_nat)) (ty_lam ty_nat ty_nat)))
  with ((fun t => ty_lam t (ty_lam (option t) t)) (ty_lam ty_nat ty_nat)).
  apply T_UnivE.
  apply out_typ.
  apply T_Abs.
  apply T_Var; simpl; auto.
  apply T_Deref.
  apply T_Var; simpl; auto.
  apply T_Nat.
  apply T_App with ty_nat.
  change (ty_lam ty_nat (ty_ref (option ty_nat)))
    with ((fun t => ty_lam t (ty_ref (option t))) ty_nat).
  apply T_UnivE.
  apply T_Var; simpl; auto.
  apply T_Nat.

  apply T_App with (ty_lam ty_nat ty_nat).
  change (ty_lam (ty_lam ty_nat ty_nat) (ty_ref (option (ty_lam ty_nat ty_nat))))
    with ((fun t => ty_lam t (ty_ref (option t))) (ty_lam ty_nat ty_nat)).
  apply T_UnivE.
  apply T_Var; simpl; auto.
  apply T_Abs.
  apply T_Var; simpl; auto.

  unfold bad_UnivI_rule in H.
  apply H; intros.
  apply T_App with (ty_ref (option tau)).
  apply T_Abs.
  apply T_Abs.
  apply T_Update with (option tau).
  apply T_Var; simpl; auto.
  apply T_App with tau.
  change (ty_lam tau (option tau))
    with ((fun t => ty_lam t (option t)) tau).
  apply T_UnivE.
  apply T_weaken_nil.
  apply some_typ.
  apply T_Var; simpl; auto.
  apply T_Var; simpl; auto.
  apply T_New.
  apply T_UnivE.
  apply none_typ.
Qed.

(* Apply the counterexample to show that the rule is unsound.
 *)
Theorem unrestricted_universals_inconsistent : ~bad_UnivI_rule.
Proof.
  intro H.
  apply crash_unsafe.
  apply typing_implies_safety with ty_nat.
  apply bad_rule_crash.
  assumption.
Qed.

(* In contrast, the following slight modification is
   safe.  We've inserted a lambda to make sure that
   the reference cell "inside" f isn't allocated until
   after polymorphic type instantiation.  This makes
   the expression a value, and allows us to apply
   the allp introduction rule with the
   value restriction.
 *)
Definition ok_program :=
  e_let
    (* f := *)
    (Lam
    ( e_let (* r := *) (New none) (* in *)
       (Lam (* x *)
          (Update (Var 1 (*r*))
             (*:=*) (App some (Var 0 (*x*)))
             (* ; *) (Var 1 (*r*))))))
    (* in *)
    ( e_let (* a := *) (App (App (Var 0 (*f*)) (Nat 0)) (Lam (Var 0))) (* in *)
     (e_let (* b := *) (App (App (Var 1 (*f*)) (Nat 0)) (Nat 5))       (* in *)
       (App (App (App out (Lam (Var 0))) (Deref (Var 1 (*a*)))) (Nat 42))
     )).

Lemma ok_program_types :
  Typ nil ok_program ty_nat.
Proof.
  intros.
  unfold ok_program.
  unfold e_let at 1.
  apply T_App with (ALL tau:pred world, ty_lam ty_nat (ty_lam tau (ty_ref (option tau)))).
  apply T_Abs.
  unfold e_let at 1.
  apply T_App with (ty_ref (option (ty_lam ty_nat ty_nat))).
  apply T_Abs.
  unfold e_let at 1.
  apply T_App with (ty_ref (option ty_nat)).
  apply T_Abs.
  apply T_App with ty_nat.
  apply T_App with (option (ty_lam ty_nat ty_nat)).
  apply T_App with (ty_lam ty_nat ty_nat).
  apply T_weaken_nil.
  change (ty_lam (ty_lam ty_nat ty_nat)
    (ty_lam (option (ty_lam ty_nat ty_nat)) (ty_lam ty_nat ty_nat)))
  with ((fun t => ty_lam t (ty_lam (option t) t)) (ty_lam ty_nat ty_nat)).
  apply T_UnivE.
  apply out_typ.
  apply T_Abs.
  apply T_Var; simpl; auto.
  apply T_Deref.
  apply T_Var; simpl; auto.
  apply T_Nat.
  apply T_App with ty_nat.
  apply T_App with ty_nat.
  change (ty_lam ty_nat (ty_lam ty_nat (ty_ref (option ty_nat))))
    with ((fun t => ty_lam ty_nat (ty_lam t (ty_ref (option t)))) ty_nat).
  apply T_UnivE.
  apply T_Var; simpl; auto.
  apply T_Nat.
  apply T_Nat.

  apply T_App with (ty_lam ty_nat ty_nat).
  apply T_App with ty_nat.
  change (ty_lam ty_nat (ty_lam (ty_lam ty_nat ty_nat) (ty_ref (option (ty_lam ty_nat ty_nat)))))
    with ((fun t => ty_lam ty_nat (ty_lam t (ty_ref (option t)))) (ty_lam ty_nat ty_nat)).
  apply T_UnivE.
  apply T_Var; simpl; auto.
  apply T_Nat.
  apply T_Abs.
  apply T_Var; simpl; auto.

  apply T_UnivI; simpl; intros; auto.
  apply T_Abs.
  apply T_App with (ty_ref (option tau)).
  apply T_Abs.
  apply T_Abs.
  apply T_Update with (option tau).
  apply T_Var; simpl; auto.
  apply T_App with tau.
  change (ty_lam tau (option tau))
    with ((fun t => ty_lam t (option t)) tau).
  apply T_UnivE.
  apply T_weaken_nil.
  apply some_typ.
  apply T_Var; simpl; auto.
  apply T_Var; simpl; auto.
  apply T_New.
  apply T_UnivE.
  apply T_weaken_nil.
  apply none_typ.
Qed.

Theorem ok_program_safe :
  safe_prog ok_program.
Proof.
  eapply typing_implies_safety; apply ok_program_types.
Qed.

Eval vm_compute in (snd (eval 100 empty_mem crash)).
Eval vm_compute in (snd (eval 100 empty_mem ok_program)).

