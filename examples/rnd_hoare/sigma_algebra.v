Require Export Coq.Sets.Ensembles.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.

Definition Countable_Union (A: Type) (P: nat -> Ensemble A) : Ensemble A :=
  fun x => exists i, P i x.

Definition Non_Empty {U: Type} (A: Ensemble U): Prop := exists x, A x.

Definition unsig_Set {U: Type} {P: U -> Prop} (A: Ensemble {x: U | P x}): Ensemble U := fun x => exists H: P x, A (exist _ x H).

Definition sig_Set {U: Type} (Q P: Ensemble U): Ensemble {x: U | P x} := fun x => Q (proj1_sig x).

Class SigmaAlgebra (Omega: Type): Type := {
  is_measurable_set: Ensemble Omega -> Prop;
  is_measurable_set_proper: Proper (Same_set _ ==> iff) is_measurable_set;
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

Definition Union_MSet (Omega: Type) {sa: SigmaAlgebra Omega} (A B: measurable_set Omega): measurable_set Omega.
  exists (Union _ A B).
  admit.
Defined.

Definition Intersection_MSet (Omega: Type) {sa: SigmaAlgebra Omega} (A B: measurable_set Omega): measurable_set Omega.
  exists (Intersection _ A B).
  admit.
Defined.

Definition Complement_MSet (Omega: Type) {sa: SigmaAlgebra Omega} (A: measurable_set Omega): measurable_set Omega.
  exists (Complement _ A).
  apply complement_measurable.
  apply (proj2_sig A).
Defined.

Definition Same_MSet {Omega: Type} {sa: SigmaAlgebra Omega}: measurable_set Omega -> measurable_set Omega -> Prop := fun P Q => Same_set _ P Q.

Instance Same_MSet_Equiv {Omega: Type} {sa: SigmaAlgebra Omega}: Equivalence (@Same_MSet Omega sa).
Admitted.

Definition max_sigma_alg (Omega: Type): SigmaAlgebra Omega :=
  Build_SigmaAlgebra _ (fun _ => True) (fun _ _ _ => conj (fun _ => I) (fun _ => I)) I (fun _ _ => I) (fun _ _ => I).

Definition left_discreste_prod_sigma_alg (O1 O2: Type) {sa2: SigmaAlgebra O2}: SigmaAlgebra (O1 * O2).
  apply (Build_SigmaAlgebra _ (fun P => forall x1, is_measurable_set (fun x2 => P (x1, x2)))).
  + intros P1 P2 ?; simpl.
    split; intros; specialize (H0 x1).
    - eapply is_measurable_set_proper; [| eassumption].
      split; hnf; unfold In; intros; apply H; auto.
    - eapply is_measurable_set_proper; [| eassumption].
      split; hnf; unfold In; intros; apply H; auto.
  + intros; eapply is_measurable_set_proper; [| apply universal_set_measurable].
    split; hnf; unfold In; intros; constructor.
  + intros.
    intros; eapply is_measurable_set_proper; [| apply complement_measurable, (H x1)].
    split; hnf; unfold Complement, In; intros; auto.
  + admit.
Defined.

    
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rfunctions.

Local Open Scope R.

Parameter Lebegue_sigma_algebra: SigmaAlgebra R.

Axiom open_set_measurable: forall a: R, is_measurable_set (fun x: R => x < a).