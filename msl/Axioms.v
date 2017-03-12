
(** This file collects some axioms used throughout the Mechanized Semantic Library development.
  This file was developed in 2010 by Andrew W. Appel and Xavier Leroy, and harmonizes
  the axioms used by MSL and by the CompCert project.
 *)

Require Coq.Logic.ClassicalFacts.

(** * Extensionality axioms *)

(** The following [Require Export] gives us functional extensionality for dependent function types:
<<
Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.
>>
and, as a corollary, functional extensionality for non-dependent functions:
<<
Lemma functional_extensionality {A B} (f g : A -> B) :
  (forall x, f x = g x) -> f = g.
>>
*)
Require Export Coq.Logic.FunctionalExtensionality.

(** For compatibility with earlier developments, [extensionality]
  is an alias for [functional_extensionality]. *)

Lemma extensionality:
  forall (A B: Type) (f g : A -> B),  (forall x, f x = g x) -> f = g.
Proof. intros; apply functional_extensionality. auto. Qed.

Arguments extensionality [A B] _ _ _.

(** We also assert propositional extensionality. *)

Axiom prop_ext: ClassicalFacts.prop_extensionality.
Arguments prop_ext [A B] _.

(** * Proof irrelevance *)

(** We also use proof irrelevance, which is a consequence of propositional
    extensionality. *)

Lemma proof_irr: ClassicalFacts.proof_irrelevance.
Proof.
  exact (ClassicalFacts.ext_prop_dep_proof_irrel_cic prop_ext).
Qed.
Arguments proof_irr [A] _ _.


