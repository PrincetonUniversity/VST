From iris.algebra Require Export excl.
From iris_ora.algebra Require Export excl.
From iris_ora.logic Require Export own.
From VST.veric Require Export base dfrac auth res_predicates.

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

Definition has_ext `{heapGS Σ} {Z : Type} `{!externalGS Z Σ} (z : Z) : mpred :=
  own(inG0 := external_inG) external_name (auth_frag(A := optionUR (@exclR (leibnizO Z))) (Excl' z)).

Definition ext_auth `{heapGS Σ} {Z : Type} `{!externalGS Z Σ} (z : Z) : mpred :=
  own(inG0 := external_inG) external_name (auth_auth(A := optionUR (@exclR (leibnizO Z))) (DfracOwn Tsh) (Excl' z)).
