Require Import VST.msl.Extensionality.
Require Import VST.msl.sepalg.
Require Import VST.msl.ageable.
Require Import VST.msl.age_sepalg.
Require Import VST.msl.base.
Require Import VST.msl.predicates_hered.
Require Import VST.msl.predicates_sl.
Require Import VST.msl.subtypes.
Require Import VST.msl.subtypes_sl.
Require Import VST.msl.predicates_rec.

(* Given a separation algebra on type [A], we can make a separation logic
   with predicates of type  [pred A].  But the type   [B -> pred A] is also
   a natural separation logic.  These typeclasses automagically extend
   the separation-logic operators to the pointwise-function case.
   At present, this is just the beginnings of an experiment with this idea;
   don't expect it to work well enough to be useful.
   Andrew Appel, August 2012, following an approach suggested by Rob Dockins
*)

Class StarOp A := {  starOp : A -> A -> A }.

Instance baseStarOp {A}{agA: ageable A}{JA: Join A}{PA: Perm_alg A}{AgeA: Age_alg A}
 : StarOp (pred A) := {| starOp := sepcon |}.

Instance funStarOp (B: Type)(A: Type)(StarA: StarOp A) : StarOp (B -> A) :=
   {| starOp := fun (P Q : B -> A) (b : B) =>  starOp (P b) (Q b) |}.

Notation "P '*' Q" := (starOp P Q) : pred.
(* Opaque baseStarOp *)

Class DerivesOp A := {  derivesOp : A -> A -> Prop }.

Instance baseDerivesOp {A}{agA: ageable A}
 : DerivesOp (pred A) := {| derivesOp := @derives A agA|}.

Instance funDerivesOp (B: Type)(A: Type)(DerivesA: DerivesOp A) : DerivesOp (B -> A)
 := {| derivesOp := fun (P Q : B -> A)  => forall b, derivesOp (P b) (Q b) |}.
Notation "P '|--' Q" := (derivesOp P%pred Q%pred).
(* Opaque baseDerivesOp. *)

Class WandOp A := {  wandOp : A -> A -> A }.

Instance baseWandOp {A}{agA: ageable A}{JA: Join A}{PA: Perm_alg A}{AgeA: Age_alg A}
 : WandOp (pred A) := {| wandOp := wand |}.

Instance funWandOp (B: Type)(A: Type)(WandA: WandOp A) : WandOp (B -> A) :=
   {| wandOp := fun (P Q : B -> A) (b : B) =>  wandOp (P b) (Q b) |}.

Notation "P '-*' Q" := (wandOp P Q) : pred.
(* Opaque baseWandOp *)

Class EmpOp A := { Emp: A}.

Instance baseEmpOp {A}{agA: ageable A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AgeA: Age_alg A}
  : EmpOp (pred A) := {| Emp := @emp A JA PA SA agA AgeA |}.

Instance funEmpOp  (B: Type)(A: Type)(EmpA: EmpOp A) : EmpOp (B -> A) :=
   {| Emp := fun (b : B) =>  Emp  |}.

Section Test.
Variable environ: Type.
Variables (rmap : Type)
      (Join_rmap: Join rmap) (Perm_rmap: @Perm_alg rmap Join_rmap)
      (Sep_rmap: @Sep_alg rmap Join_rmap)
      (Canc_rmap: @Canc_alg rmap Join_rmap)
      (Disj_rmap: @Disj_alg rmap Join_rmap)
      (ag_rmap: ageable rmap)
      (Age_rmap: @Age_alg rmap Join_rmap ag_rmap).
Existing Instance  Join_rmap.
Existing Instance  Perm_rmap.
Existing Instance  Sep_rmap.
Existing Instance  Canc_rmap.
Existing Instance  Disj_rmap.
Existing Instance  ag_rmap.
Existing Instance  Age_rmap.

Lemma test1: forall (P : environ -> pred rmap) (Q: pred rmap),
   P * Emp |-- P.
Proof.
 intros.
  intro. simpl; rewrite sepcon_emp.
auto.
Qed.

End Test.
