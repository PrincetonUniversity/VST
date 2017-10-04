(* This is not a complete definition of CCC. But it is enough to prove useful *)
(* properties.                                                                *)
(* It is possible to define a Type version instead of Prop version, which is  *)
(* more faithful to its mathmatical definitions. Again, a Prop version is     *)
(* good to use in VST already.                                                *)
(*                                                               -- Qinxiang  *)

Module CartesianClosedCat.

Section CartesianClosedCat.

Variable A: Type.
Variable arrow: A -> A -> Prop.
Variable iso: A -> A -> Prop.

Class CCC (prod expo: A -> A -> A): Prop := mkCCC {
  comm: forall x y, iso (prod x y) (prod y x);
  assoc: forall x y z, iso (prod (prod x y) z) (prod x (prod y z));
  adjoint: forall x y z, arrow (prod x y) z <-> arrow x (expo y z);
  prod_UMP: forall x x' y y', arrow x x' -> arrow y y' -> arrow (prod x y) (prod x' y')
}.

(* This is an example of useful property. *)

Hypothesis transitivity: forall x y z, arrow x y -> arrow y z -> arrow x z.
Hypothesis identity: forall x, arrow x x.

Lemma expo_UMP: forall prod expo `{CCC prod expo},
  forall x x' y y', arrow x' x -> arrow y y' -> arrow (expo x y) (expo x' y').
Proof.
  intros.
  apply adjoint.
  eapply transitivity; [| exact H1].
  eapply transitivity; [apply prod_UMP; [apply identity | eassumption] |].
  apply adjoint.
  apply identity.
Qed.

End CartesianClosedCat.

End CartesianClosedCat.
