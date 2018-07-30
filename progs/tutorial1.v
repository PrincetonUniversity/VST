Require Import VST.floyd.proofauto.
Require Import VST.progs.sumarray.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.
Definition Gprog: funspecs := nil.
Definition Delta1 : tycontext :=
  ltac:(let x := constr:(func_tycontext f_sumarray Vprog Gprog nil)
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

Lemma exercise3b: 
  forall al: list Z ,  Zlength al < 50 ->
         0 <= Zlength al < Int.max_signed.
Proof.
intros.
rep_omega.
Qed.

Lemma exercise3c: 
  forall i,
         0 <= Int.unsigned (Int.repr i) <= Int.max_unsigned.
Proof.
intros.
rep_omega.
Qed.


(**  How to manage semi-opaque constants, using Hint Rewrite : rep_omega. *)
(* Suppose you have an uninitialized array of size N: *)

Definition N : Z := 20.

Lemma exercise4:
 let Delta := @abbreviate _ Delta1 in 
 forall sh p,
    data_at sh (tarray tint N) (Vint (Int.repr 1) :: Vint (Int.repr 2) :: list_repeat (Z.to_nat (N-2)) Vundef) p
 |--  !! (0 <= Zlength (list_repeat (Z.to_nat (N-2)) Vundef) < Int.max_signed).
Proof.
intros.
simpl.
(* It's not nice that [simpl] unfolded the list_repeat. *)
entailer!.
repeat rewrite Zlength_cons. rewrite Zlength_nil. 
rep_omega.
Abort.

(* To avoid unfolding of the list_repeat, let us make N opaque. *)

Global Opaque N.

Lemma exercise4b:
 let Delta := @abbreviate _ Delta1 in 
 forall sh p,
    data_at sh (tarray tint N) (Vint (Int.repr 1) :: Vint (Int.repr 2) :: list_repeat (Z.to_nat (N-2)) Vundef) p
 |--  !! (0 <= Zlength (list_repeat (Z.to_nat (N-2)) Vundef) < Int.max_signed).
Proof.
intros.
simpl.
(* That's better; the data_at is more concise.  But now, unfortunately: *)
entailer!.
rewrite Zlength_list_repeat.
Fail rep_omega.
(* now rep_omega does not know that N=20. *)
Abort.

(* To tell rep_omega that N=20, just add a hint to the rep_omega database: *)

Lemma N_eq: N=20.
Proof. reflexivity. Qed.
Hint Rewrite N_eq : rep_omega.

Lemma exercise4c:
 let Delta := @abbreviate _ Delta1 in 
 forall sh p,
    data_at sh (tarray tint N) (Vint (Int.repr 1) :: Vint (Int.repr 2) :: list_repeat (Z.to_nat (N-2)) Vundef) p
 |--  !! (0 <= Zlength (list_repeat (Z.to_nat (N-2)) Vundef) < Int.max_signed).
Proof.
intros.
simpl.
(* That's still good; the data_at is more concise.  *)
entailer!.
rewrite Zlength_list_repeat.
rep_omega.
rep_omega.
Qed.

(* Summary: Make your constant Global Opaque, but add a Hint Rewrite rule to the rep_omega database. *)








