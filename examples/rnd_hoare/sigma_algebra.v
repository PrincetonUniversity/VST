Require Export Coq.Sets.Ensembles.
Require Export Coq.Classes.Equivalence.

Definition Countable_Union (A: Type) (P: nat -> Ensemble A) : Ensemble A :=
  fun x => exists i, P i x.

Definition Non_Empty {U: Type} (A: Ensemble U): Prop := exists x, A x.

Definition unsig_Set {U: Type} {P: U -> Prop} (A: Ensemble {x: U | P x}): Ensemble U := fun x => exists H: P x, A (exist _ x H).

Definition sig_Set {U: Type} (Q P: Ensemble U): Ensemble {x: U | P x} := fun x => Q (proj1_sig x).

Class SigmaAlgebra (Omega: Type): Type := {
  is_measurable_set: Ensemble Omega -> Prop;
  universal_set_measurable: is_measurable_set (Full_set _);
  complement_measurable: forall P, is_measurable_set P -> is_measurable_set (Complement _ P);
  countable_union_measurable: forall P: nat -> Ensemble Omega, (forall i, is_measurable_set (P i)) -> is_measurable_set (Countable_Union _ P)
}.

Definition measurable_set (Omega: Type) {sa: SigmaAlgebra Omega}: Type := {x: Ensemble Omega | is_measurable_set x}.

Definition MSet_Ensemble {Omega: Type} {sa: SigmaAlgebra Omega} (P: measurable_set Omega): Ensemble Omega := proj1_sig P.
Global Coercion MSet_Ensemble: measurable_set >-> Ensemble.

Definition In_MSet {Omega: Type} {sa: SigmaAlgebra Omega} (P: measurable_set Omega) (x: Omega) : Prop := proj1_sig P x.
Global Coercion In_MSet: measurable_set >-> Funclass.

Definition Countable_Union_MSet {Omega: Type} {sa: SigmaAlgebra Omega} (x: nat -> measurable_set Omega): measurable_set Omega :=
  exist _
   (Countable_Union _ (fun i => x i))
   (countable_union_measurable _ (fun i => proj2_sig _)).

Definition Full_MSet (Omega: Type) {sa: SigmaAlgebra Omega}: measurable_set Omega :=
  exist _ (Full_set _) universal_set_measurable.

Definition max_sigma_alg (Omega: Type): SigmaAlgebra Omega :=
  Build_SigmaAlgebra _ (fun _ => True) I (fun _ _ => I) (fun _ _ => I).

Definition Same_MSet {Omega: Type} {sa: SigmaAlgebra Omega}: measurable_set Omega -> measurable_set Omega -> Prop := fun P Q => forall x, P x <-> Q x.

Instance Same_MSet_Equiv {Omega: Type} {sa: SigmaAlgebra Omega}: Equivalence (@Same_MSet Omega sa).
Admitted.