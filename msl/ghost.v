Require Import VST.msl.sepalg.

Class Ghost := { G : Type;
  Join_G :> Join G; Sep_G :> Sep_alg G; Perm_G :> Perm_alg G }.

Definition fp_update_ND {RA: Ghost} (a: G) B := forall c, joins a c -> exists b, B b /\ joins b c.

Definition fp_update {RA: Ghost} (a b : G) := forall c, joins a c -> joins b c.
