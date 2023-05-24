From iris.algebra Require Export excl auth.
From iris_ora.algebra Require Export excl.
From iris_ora.logic Require Export own.
From VST.veric Require Export base auth.
From iris.proofmode Require Import proofmode.

(* external ghost state *)
Lemma excl_orderN_includedN : forall {A : ofe} n (x y : excl' A), x ≼ₒ{n} y → x ≼{n} y.
Proof.
  intros.
  destruct x, y; simpl in *; try done.
  - exists None; rewrite right_id; constructor; done.
  - eexists; rewrite left_id //.
Qed.

Canonical Structure excl_authR (A : ofe) := authR (optionUR (@exclR A)) excl_orderN_includedN.

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
  iMod (own_alloc (auth_auth(A := optionUR (@exclR (leibnizO Z))) (DfracOwn 1) (Excl' z) ⋅ auth_frag(A := optionUR (@exclR (leibnizO Z))) (Excl' z))) as (γ) "?".
  { by apply (auth_both_valid_2(A := uora_ucmraR (optionUR (@exclR (leibnizO Z))))). }
  iExists (ExternalGS _ _ _ γ).
  rewrite own_op //.
Qed.
