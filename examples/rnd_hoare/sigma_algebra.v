Require Export Coq.Sets.Ensembles.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Logic.Classical.
Require Export RamifyCoq.lib.Ensembles_ext.

Definition unsig_Set {U: Type} {P: U -> Prop} (A: Ensemble {x: U | P x}): Ensemble U := fun x => exists H: P x, A (exist _ x H).

Definition sig_Set {U: Type} (Q P: Ensemble U): Ensemble {x: U | P x} := fun x => Q (proj1_sig x).

Class SigmaAlgebra (Omega: Type): Type := {
  is_measurable_set: Ensemble Omega -> Prop;
  is_measurable_set_proper: Proper (Same_set ==> iff) is_measurable_set;
  full_measurable: is_measurable_set (Full_set _);
  complement_measurable: forall P, is_measurable_set P -> is_measurable_set (Complement _ P);
  countable_union_measurable: forall P: nat -> Ensemble Omega, (forall i, is_measurable_set (P i)) -> is_measurable_set (Countable_Union _ P)
}.

Lemma empty_measurable {Omega: Type} {sa: SigmaAlgebra Omega}: is_measurable_set (Empty_set _).
Proof.
  intros.
  eapply is_measurable_set_proper; [| apply complement_measurable, full_measurable].
  rewrite Same_set_spec; intros x; unfold Complement, Ensembles.In.
  rewrite Empty_set_spec, Full_set_spec.
  tauto.
Qed.

Lemma union_measurable {Omega: Type} {sa: SigmaAlgebra Omega}: forall P Q, is_measurable_set P -> is_measurable_set Q -> is_measurable_set (Union _ P Q).
Proof.
  intros.
  eapply is_measurable_set_proper; [apply Union_is_Countable_Union |].
  apply countable_union_measurable; intros.
  destruct i as [| [|]]; auto.
  simpl.
  apply empty_measurable.
Qed.

Lemma intersection_measurable {Omega: Type} {sa: SigmaAlgebra Omega}: forall P Q, is_measurable_set P -> is_measurable_set Q -> is_measurable_set (Intersection _ P Q).
Proof.
  intros.
  eapply is_measurable_set_proper; [apply Intersection_is_Complement_Union, classic |].
  apply complement_measurable, union_measurable; apply complement_measurable; auto.
Qed.

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
  exist _ (Full_set _) full_measurable.

Definition Empty_MSet (Omega: Type) {sa: SigmaAlgebra Omega}: measurable_set Omega :=
  exist _ (Empty_set _) empty_measurable.

Definition Union_MSet (Omega: Type) {sa: SigmaAlgebra Omega} (A B: measurable_set Omega): measurable_set Omega :=
  exist _ (Union _ A B) (union_measurable _ _ (proj2_sig A) (proj2_sig B)).

Definition Intersection_MSet (Omega: Type) {sa: SigmaAlgebra Omega} (A B: measurable_set Omega): measurable_set Omega :=
  exist _ (Intersection _ A B) (intersection_measurable _ _ (proj2_sig A) (proj2_sig B)).

Definition Complement_MSet (Omega: Type) {sa: SigmaAlgebra Omega} (A: measurable_set Omega): measurable_set Omega :=
  exist _ (Complement _ A) (complement_measurable _ (proj2_sig A)).

Definition Same_MSet {Omega: Type} {sa: SigmaAlgebra Omega}: measurable_set Omega -> measurable_set Omega -> Prop := fun P Q => Same_set P Q.

Instance Same_MSet_Equiv {Omega: Type} {sa: SigmaAlgebra Omega}: Equivalence (@Same_MSet Omega sa).
  unfold Same_MSet.
  constructor.
  + intros x; simpl; reflexivity.
  + intros x y ?; simpl; symmetry; auto.
  + intros x y z ? ?; simpl; transitivity y; auto.
Qed.

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
  + intros; eapply is_measurable_set_proper; [| apply full_measurable].
    split; hnf; unfold In; intros; constructor.
  + intros.
    intros; eapply is_measurable_set_proper; [| apply complement_measurable, (H x1)].
    split; hnf; unfold Complement, In; intros; auto.
  + intros.
    change (fun x2 : O2 => Countable_Union (O1 * O2) P (x1, x2))
      with (Countable_Union _ (fun i x2 => P i (x1, x2))).
    apply countable_union_measurable.
    intros.
    auto.
Defined.

Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Rfunctions.

Local Open Scope R.

Parameter Lebegue_sigma_algebra: SigmaAlgebra R.

Axiom open_set_measurable: forall a: R, is_measurable_set (fun x: R => x < a).