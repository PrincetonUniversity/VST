(* THESE PROOFS are discussed in the book chapter entitled "Normalization
    of separation logic formulas" *)

Goal forall (P Q R: nat -> Prop),
    (forall z, P z -> Q (S z)) ->
         (exists z, P z) /\ R 0 -> (exists y, Q y).
Proof.
intros P Q R H.
Abort.

Require Import msl.msl_standard.
Require Import msl.normalize.

Section Example.
Context {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}{agA: ageable A}{AgeA: Age_alg A}.

Goal forall P Q R: nat -> pred A,
       (forall z, P z |-- Q (S z)) ->
      (EX z:nat, P z) * R 0 |-- (EX y:nat, Q y) * TT.
Proof.
intros.
(* don't do this:    intros ? [a1 [a2 [? [[z ?] ?]]]]. *)
normalize.
intro x.
apply (exp_right (S x)).
apply sepcon_derives; auto.
Qed.


Goal forall (Q: nat -> Prop) (P R: nat -> pred A),
   (forall z, Q z -> Q (S z)) ->
   (forall z, !! Q (S z) && P z |-- R z)  ->
   forall z,  P z && !! Q z |-- !!Q (S z) && R z.
Proof.
intros.
normalize.
eapply derives_trans; [ | apply H0].
normalize.
Qed.

End EXample.



