(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* Some basic definitions used in cost models, admissibility predicates, etc. *)
Set Implicit Arguments.

Require Import FCF.Comp.

Definition DataTypeFamily := nat -> Set.

Definition FunctionCostModel := forall (A B : Type), (A -> B) -> nat -> Prop.
Definition CompCostModel := forall (A : Set), Comp A -> nat -> Prop.
Definition OC_CostModel := forall (A B C : Set), OracleComp A B C -> (nat -> nat) -> Prop.

Definition pred_comp_fam := forall (A : nat -> Set), (forall n, Comp (A n)) -> Prop.
Definition pred_comp_func_2_fam := forall (A B C : nat -> Set), (forall n, A n -> B n -> Comp (C n)) -> Prop.

Definition pred_oc_fam := forall (A B C : nat -> Set), (forall n, OracleComp (A n) (B n) (C n)) -> Prop.
Definition pred_oc_func_2_fam := forall (A B C D E : nat -> Set), (forall n, A n -> B n -> OracleComp (C n) (D n) (E n)) -> Prop.
