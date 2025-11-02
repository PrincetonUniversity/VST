From iris.algebra Require Export excl auth.
Set Warnings "-notation-overridden,-hiding-delimiting-key".
From iris_ora.algebra Require Export excl_auth.
From iris_ora.logic Require Export own.
Set Warnings "notation-overridden,hiding-delimiting-key".
From iris.proofmode Require Import proofmode.

Class externalGS (Z : Type) (Σ : gFunctors) := ExternalGS {
  external_inG : inG Σ (excl_authR (leibnizO Z));
  external_name : gname
}.

Definition has_ext {Z : Type} `{!externalGS Z Σ} (z : Z) : iProp Σ :=
  own(inG0 := external_inG) external_name (auth_frag(A := optionUR (@exclR (leibnizO Z))) (Excl' z)).

Definition ext_auth {Z : Type} `{!externalGS Z Σ} (z : Z) : iProp Σ :=
  own(inG0 := external_inG) external_name (auth_auth(A := optionUR (@exclR (leibnizO Z))) (DfracOwn 1) (Excl' z)).

Lemma ext_alloc {Z : Type} `{!inG Σ (excl_authR (leibnizO Z))} (z : Z) : ⊢ |==> ∃ _ : externalGS Z Σ, ext_auth z ∗ has_ext z.
Proof.
  rewrite /ext_auth /has_ext.
  iMod (own_alloc (●E (z : leibnizO Z) ⋅ ◯E (z : leibnizO Z) : excl_authR (leibnizO Z))) as (γ) "?".
  { apply excl_auth_valid. }
  iExists (ExternalGS _ _ _ γ).
  rewrite own_op //.
Qed.
