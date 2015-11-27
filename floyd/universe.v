Require Import Coq.Logic.JMeq.

Set Printing Universes.
Print Universes.
Print Coq.Logic.JMeq.


Lemma JMeq_eq_dep_id_equiv :
       forall (A : Type (* Coq.Logic.JMeq.119 *))
         (B : Type (* Coq.Logic.JMeq.120 *)) (x : A) 
         (y : B),
       JMeq x y <->
       EqdepFacts.eq_dep Type (* Coq.Logic.JMeq.123 *)
         (fun X : Type (* Coq.Logic.JMeq.123 *) => X) A x B y.
Proof.
  intros; split.
  + apply JMeq_eq_dep_id.
  + apply eq_dep_id_JMeq.
Qed.

Print Universes.
Print JMeq_eq_dep_id_equiv.
Module JMEQ.

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** John Major's Equality as proposed by Conor McBride

  Reference:

  [McBride] Elimination with a Motive, Proceedings of TYPES 2000,
  LNCS 2277, pp 197-216, 2002.

*)

Set Implicit Arguments.

Unset Elimination Schemes.

Inductive JMeq (A:Type) (x:A) : forall B:Type, B -> Prop :=
    JMeq_refl : JMeq x x.

Set Elimination Schemes.

Arguments JMeq_refl {A x} , [A] x.

Hint Resolve JMeq_refl.

Lemma JMeq_sym : forall (A B:Type) (x:A) (y:B), JMeq x y -> JMeq y x.
Proof.
destruct 1; trivial.
Qed.

Hint Immediate JMeq_sym.

Lemma JMeq_trans :
 forall (A B C:Type) (x:A) (y:B) (z:C), JMeq x y -> JMeq y z -> JMeq x z.
Proof.
destruct 2; trivial.
Qed.

Axiom JMeq_eq : forall (A:Type) (x y:A), JMeq x y -> x = y.

Lemma JMeq_ind : forall (A:Type) (x:A) (P:A -> Prop),
  P x -> forall y, JMeq x y -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_rec : forall (A:Type) (x:A) (P:A -> Set),
  P x -> forall y, JMeq x y -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_rect : forall (A:Type) (x:A) (P:A->Type),
  P x -> forall y, JMeq x y -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_ind_r : forall (A:Type) (x:A) (P:A -> Prop),
   P x -> forall y, JMeq y x -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := JMeq_sym H'); trivial.
Qed.

Lemma JMeq_rec_r : forall (A:Type) (x:A) (P:A -> Set),
   P x -> forall y, JMeq y x -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := JMeq_sym H'); trivial.
Qed.

Lemma JMeq_rect_r : forall (A:Type) (x:A) (P:A -> Type),
   P x -> forall y, JMeq y x -> P y.
Proof.
intros A x P H y H'; case JMeq_eq with (1 := JMeq_sym H'); trivial.
Qed.

Lemma JMeq_congr :
 forall (A:Type) (x:A) (B:Type) (f:A->B) (y:A), JMeq x y -> f x = f y.
Proof.
intros A x B f y H; case JMeq_eq with (1 := H); trivial.
Qed.

(** [JMeq] is equivalent to [eq_dep Type (fun X => X)] *)

Require Import Coq.Logic.Eqdep.

Lemma JMeq_eq_dep_id :
 forall (A B:Type) (x:A) (y:B), JMeq x y -> eq_dep Type (fun X => X) A x B y.
Proof.
destruct 1.
apply eq_dep_intro.
Qed.

End JMEQ.

(*
JMEQ.JMeq_eq_dep_id = 
fun (A : Type (* Top.1590 *)) (B : Type (* Top.1591 *)) 
  (x : A) (y : B) (H : @JMEQ.JMeq A x B y) =>
match
  H in (@JMEQ.JMeq _ _ B0 b)
  return
    (EqdepFacts.eq_dep Type (* Top.1594 *) (fun X : Type (* Top.1594 *) => X)
       A x B0 b)
with
| JMEQ.JMeq_refl =>
    EqdepFacts.eq_dep_intro Type (* Top.1594 *)
      (fun X : Type (* Top.1594 *) => X) A x
end
     : forall (A : Type (* Top.1590 *)) (B : Type (* Top.1591 *)) 
         (x : A) (y : B),
       @JMEQ.JMeq A x B y ->
       EqdepFacts.eq_dep Type (* Top.1594 *)
         (fun X : Type (* Top.1594 *) => X) A x B y


This Match-In clause is why Top.1473 <= Top.1594.

Because we are pattern match a Type known as Top.1473, to fullfil a place which should be Type Top.1594.

This causes the fact that Top.1594 < Coq.Logic.EqdepFacts.1,
i.e. JMeq.2 < Coq.Logic.EqdepFacts.1.
*)


Set Printing Universes.
Print Universes.
Print Coq.Logic.EqdepFacts.
Set Printing All.

Print JMEQ.

Print Universes.
Print JMEQ.JMeq_eq_dep_id.

Require Import Coq.Logic.JMeq.
Require Import Coq.Init.Logic.

Set Printing Universes.
Print Universes.
Set Printing All.
Print Coq.Logic.JMeq.
Print EqdepFacts.eq_dep.
