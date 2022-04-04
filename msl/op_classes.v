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

#[global] Instance baseStarOp {A}{agA: ageable A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AgeA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A}
 : StarOp (pred A) := {| starOp := sepcon |}.

#[global] Instance funStarOp (B: Type)(A: Type)(StarA: StarOp A) : StarOp (B -> A) :=
   {| starOp := fun (P Q : B -> A) (b : B) =>  starOp (P b) (Q b) |}.

Set Warnings "-notation-overridden".
Notation "P '*' Q" := (starOp P Q) : pred.
Set Warnings "notation-overridden".
(* Opaque baseStarOp *)

Class DerivesOp A := {  derivesOp : A -> A -> Prop }.

#[global] Instance baseDerivesOp {A}{agA: ageable A}{EO: Ext_ord A}
 : DerivesOp (pred A) := {| derivesOp := @derives A agA EO|}.

#[global] Instance funDerivesOp (B: Type)(A: Type)(DerivesA: DerivesOp A) : DerivesOp (B -> A)
 := {| derivesOp := fun (P Q : B -> A)  => forall b, derivesOp (P b) (Q b) |}.
Set Warnings "-notation-overridden".
Declare Scope logic_derives.
Notation "P '|--' Q" := (derivesOp P%pred Q%pred) : logic_derives.
Set Warnings "notation-overridden".
Open Scope logic_derives.
(* Opaque baseDerivesOp. *)

Class WandOp A := {  wandOp : A -> A -> A }.

#[global] Instance baseWandOp {A}{agA: ageable A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AgeA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A}
 : WandOp (pred A) := {| wandOp := wand |}.

#[global] Instance funWandOp (B: Type)(A: Type)(WandA: WandOp A) : WandOp (B -> A) :=
   {| wandOp := fun (P Q : B -> A) (b : B) =>  wandOp (P b) (Q b) |}.

Set Warnings "-notation-overridden".
Notation "P '-*' Q" := (wandOp P Q) : pred.
Set Warnings "notation-overridden".
(* Opaque baseWandOp *)

Class EmpOp A := { Emp: A}.

#[global] Instance baseEmpOp {A}{agA: ageable A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{AgeA: Age_alg A}{EO: Ext_ord A}
  : EmpOp (pred A) := {| Emp := @emp A JA SA agA AgeA EO |}.

#[global] Instance funEmpOp  (B: Type)(A: Type)(EmpA: EmpOp A) : EmpOp (B -> A) :=
   {| Emp := fun (b : B) =>  Emp  |}.

Section Test.
Variable environ: Type.
Variables (rmap : Type)
      (Join_rmap: Join rmap) (Perm_rmap: @Perm_alg rmap Join_rmap)
      (Sep_rmap: @Sep_alg rmap Join_rmap)
      (Canc_rmap: @Canc_alg rmap Join_rmap)
      (Disj_rmap: @Disj_alg rmap Join_rmap)
      (ag_rmap: ageable rmap)
      (Age_rmap: @Age_alg rmap Join_rmap ag_rmap Sep_rmap)
      (Ext_rmap: @Ext_ord rmap ag_rmap)
      (ExtA_rmap: @Ext_alg rmap ag_rmap Ext_rmap Join_rmap Sep_rmap).
#[local] Existing Instance  Join_rmap.
#[local] Existing Instance  Perm_rmap.
#[local] Existing Instance  Sep_rmap.
#[local] Existing Instance  Canc_rmap.
#[local] Existing Instance  Disj_rmap.
#[local] Existing Instance  ag_rmap.
#[local] Existing Instance  Age_rmap.
#[local] Existing Instance  Ext_rmap.
#[local] Existing Instance  ExtA_rmap.

Lemma test1: forall (P : environ -> pred rmap) (Q: pred rmap),
   P * Emp |-- P.
Proof.
 intros.
  intro. simpl; rewrite sepcon_emp.
auto.
Qed.

End Test.
