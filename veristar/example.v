(********** THE EXAMPLE FROM THE NAVARRO/RYBALCHENKO PAPER ***********)

Require Import ZArith.
Require Import Znumtheory.
Require Import Coq.Lists.List.
Require Import veristar.variables veristar.datatypes veristar.clauses.
Require Import veristar.superpose veristar.veristar.
Import Superposition VeriStar.

Definition a := Var 1%positive.
Definition b := Var 2%positive.
Definition c := Var 3%positive.
Definition d := Var 4%positive.
Definition e := Var 5%positive.

Definition example_ent := Entailment
  (Assertion [Nequ c e] [Lseg a b , Lseg a c , Next c d , Lseg d e])
  (Assertion nil [Lseg b c , Lseg c e]).

Compute cnf example_ent.
Compute check_entailment example_ent.