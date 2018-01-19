Require Import VST.floyd.proofauto.
Require Import VST.progs.sumarray.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
Definition Gprog: funspecs := nil.
Definition Delta1 : tycontext :=
  ltac:(let x := constr:(initialized _i (func_tycontext f_sumarray Vprog Gprog))
         in let y := eval hnf in x
         in exact y).

(* This example is from the "EX, Intros, Exists" chapter of the Verifiable C Reference Manual *)
Lemma exercise1:
 let Delta := @abbreviate _ Delta1 in 
 forall sh p,
 ENTAIL Delta,
   EX x:Z,
    PROP(0<=x) LOCAL(temp _i (Vint (Int.repr x)))
    SEP (EX y:Z, !!(x<y) && data_at sh tint (Vint (Int.repr y)) p)
|-- EX u: Z,
     PROP(0<u) LOCAL()
     SEP (data_at sh tint (Vint (Int.repr u)) p).
Proof.
intros.
Intros a b.
Exists b.
entailer!.
Qed.

(* These examples of [rep_omega] are from is from the "Integers: nat, Z, int" chapter of the Verifiable C Reference Manual *)
Lemma exercise2:
  forall x,
  Int.min_signed <= x <= Int.max_signed ->
  Int.signed (Int.repr x) = x.
Proof.
intros x H.
(* Notice that the premise H is needed for the next line *)
rewrite Int.signed_repr by rep_omega.
auto.
Qed.

Lemma exercise3: 
  forall n, 0 <= n <= Int.max_signed ->
  Int.min_signed <= 0 <= n.
Proof.
intros.
rep_omega.
Qed.

Print Ltac rep_omega.









