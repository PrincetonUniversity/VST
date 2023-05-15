(* General extra lemmas about algebras of interest, extracted from iris.base_logic.algebra *)
From iris.algebra Require Import auth.
From iris_ora.logic Require Import logic.
From VST.veric Require Import dshare view gmap_view auth.

Section oupred.
  Context {M : uora}.

  (* Force implicit argument M *)
  Notation "P ⊢ Q" := (bi_entails (PROP:=ouPredI M) P Q).
  Notation "P ⊣⊢ Q" := (equiv (A:=ouPredI M) P%I Q%I).
  Notation "⊢ Q" := (bi_entails (PROP:=ouPredI M) True Q).

Section view.
  Context {A} {B : uora} (rel : view_rel A B).
  Implicit Types a : A.
  Implicit Types ag : option (share * agree A).
  Implicit Types b : B.
  Implicit Types x y : view rel.

  Context (view_rel_order : ∀n a b1 b2, b1 ≼ₒ{n} b2 → rel n a b2 → rel n a b1).

  Local Canonical Structure viewR := (view.viewR rel view_rel_order).

  Lemma view_both_dfrac_validI_1 (relI : ouPred M) dq a b :
    (∀ n (x : M), rel n a b → relI n x) →
    ✓ (●V{dq} a ⋅ ◯V b : viewR) ⊢ ⌜✓dq⌝ ∧ relI.
  Proof.
    intros Hrel. ouPred.unseal. split=> n x _ /=.
    rewrite /ouPred_holds /= view_both_dfrac_validN. by move=> [? /Hrel].
  Qed.
  Lemma view_both_dfrac_validI_2 (relI : ouPred M) dq a b :
    (∀ n (x : M), relI n x → rel n a b) →
    ⌜✓dq⌝ ∧ relI ⊢ ✓ (●V{dq} a ⋅ ◯V b : viewR).
  Proof.
    intros Hrel. ouPred.unseal. split=> n x _ /=.
    rewrite /ouPred_holds /= view_both_dfrac_validN. by move=> [? /Hrel].
  Qed.
  Lemma view_both_dfrac_validI (relI : ouPred M) dq a b :
    (∀ n (x : M), rel n a b ↔ relI n x) →
    ✓ (●V{dq} a ⋅ ◯V b : viewR) ⊣⊢ ⌜✓dq⌝ ∧ relI.
  Proof.
    intros. apply (anti_symm _);
      [apply view_both_dfrac_validI_1|apply view_both_dfrac_validI_2]; naive_solver.
  Qed.

  Lemma view_both_validI_1 (relI : ouPred M) a b :
    (∀ n (x : M), rel n a b → relI n x) →
    ✓ (●V a ⋅ ◯V b : viewR) ⊢ relI.
  Proof. intros. by rewrite view_both_dfrac_validI_1 // bi.and_elim_r. Qed.
  Lemma view_both_validI_2 (relI : ouPred M) a b :
    (∀ n (x : M), relI n x → rel n a b) →
    relI ⊢ ✓ (●V a ⋅ ◯V b : viewR).
  Proof.
    intros. rewrite -view_both_dfrac_validI_2 //.
    apply bi.and_intro; [|done]. by apply bi.pure_intro.
  Qed.
  Lemma view_both_validI (relI : ouPred M) a b :
    (∀ n (x : M), rel n a b ↔ relI n x) →
    ✓ (●V a ⋅ ◯V b : viewR) ⊣⊢ relI.
  Proof.
    intros. apply (anti_symm _);
      [apply view_both_validI_1|apply view_both_validI_2]; naive_solver.
  Qed.

  Lemma view_auth_dfrac_validI (relI : ouPred M) dq a :
    (∀ n (x : M), relI n x ↔ rel n a ε) →
    ✓ (●V{dq} a : viewR) ⊣⊢ ⌜✓dq⌝ ∧ relI.
  Proof.
    intros. rewrite -(right_id ε op (●V{dq} a)). by apply view_both_dfrac_validI.
  Qed.
  Lemma view_auth_validI (relI : ouPred M) a :
    (∀ n (x : M), relI n x ↔ rel n a ε) →
    ✓ (●V a : viewR) ⊣⊢ relI.
  Proof. intros. rewrite -(right_id ε op (●V a)). by apply view_both_validI. Qed.

  Lemma view_frag_validI (relI : ouPred M) b :
    (∀ n (x : M), relI n x ↔ ∃ a, rel n a b) →
    ✓ (◯V b : viewR) ⊣⊢ relI.
  Proof. ouPred.unseal=> Hrel. split=> n x _. by rewrite Hrel. Qed.
End view.

Section auth.
  Context {A : uora}.
  Implicit Types a b : A.
  Implicit Types x y : auth A.

  Context (auth_order : ∀n (x y : A), x ≼ₒ{n} y → x ≼{n} y).

  Local Canonical Structure authR := (auth.authR _ auth_order).
  Local Canonical Structure authUR := (auth.authUR _ auth_order).

  Lemma auth_auth_dfrac_validI dq a : ✓ (●{dq} a : authR) ⊣⊢ ⌜✓dq⌝ ∧ ✓ a.
  Proof.
    apply view_auth_dfrac_validI=> n. ouPred.unseal; split; [|by intros [??]].
    split; [|done]. apply ucmra_unit_leastN.
  Qed.
  Lemma auth_auth_validI a : ✓ (● a : authR) ⊣⊢ ✓ a.
  Proof.
    by rewrite auth_auth_dfrac_validI bi.pure_True // left_id.
  Qed.

  Lemma auth_frag_validI a : ✓ (◯ a : authR) ⊣⊢ ✓ a.
  Proof.
    apply view_frag_validI=> n x.
    rewrite auth_view_rel_exists. by ouPred.unseal.
  Qed.

  Lemma auth_both_dfrac_validI dq a b :
    ✓ (●{dq} a ⋅ ◯ b : authR) ⊣⊢ ⌜✓dq⌝ ∧ (∃ c, a ≡ b ⋅ c) ∧ ✓ a.
  Proof. apply view_both_dfrac_validI=> n. by ouPred.unseal. Qed.
  Lemma auth_both_validI a b :
    ✓ (● a ⋅ ◯ b : authR) ⊣⊢ (∃ c, a ≡ b ⋅ c) ∧ ✓ a.
  Proof.
    by rewrite auth_both_dfrac_validI bi.pure_True // left_id.
  Qed.

End auth.

(*Section excl_auth.
  Context {A : ofe}.
  Implicit Types a b : A.

  Lemma excl_auth_agreeI a b : ✓ (●E a ⋅ ◯E b) ⊢ (a ≡ b).
  Proof.
    rewrite auth_both_validI bi.and_elim_l.
    apply bi.exist_elim=> -[[c|]|];
      by rewrite option_equivI /= excl_equivI //= bi.False_elim.
  Qed.
End excl_auth.

Section dfrac_agree.
  Context {A : ofe}.
  Implicit Types a b : A.

  Lemma dfrac_agree_validI dq a : ✓ (to_dfrac_agree dq a) ⊣⊢ ⌜✓ dq⌝.
  Proof.
    rewrite prod_validI /= ouPred.discrete_valid. apply bi.entails_anti_sym.
    - by rewrite bi.and_elim_l.
    - apply bi.and_intro; first done. etrans; last apply to_agree_validI.
      apply bi.True_intro.
  Qed.

  Lemma dfrac_agree_validI_2 dq1 dq2 a b :
    ✓ (to_dfrac_agree dq1 a ⋅ to_dfrac_agree dq2 b) ⊣⊢ ⌜✓ (dq1 ⋅ dq2)⌝ ∧ (a ≡ b).
  Proof.
    rewrite prod_validI /= ouPred.discrete_valid to_agree_op_validI //.
  Qed.

  Lemma frac_agree_validI q a : ✓ (to_frac_agree q a) ⊣⊢ ⌜(q ≤ 1)%Qp⌝.
  Proof.
    rewrite dfrac_agree_validI dfrac_valid_own //.
  Qed.

  Lemma frac_agree_validI_2 q1 q2 a b :
    ✓ (to_frac_agree q1 a ⋅ to_frac_agree q2 b) ⊣⊢ ⌜(q1 + q2 ≤ 1)%Qp⌝ ∧ (a ≡ b).
  Proof.
    rewrite dfrac_agree_validI_2 dfrac_valid_own //.
  Qed.
End dfrac_agree.*)

Section gmap_view.
  Context {K : Type} `{Countable K} {V : ofe}.
  Implicit Types (m : gmap K V) (k : K) (dq : dfrac) (v : V).

  Lemma gmap_view_both_validI m k dq v :
    ✓ (gmap_view_auth (DfracOwn 1) m ⋅ gmap_view_frag k dq v) ⊢
    ✓ dq ∧ m !! k ≡ Some v.
  Proof.
    rewrite /gmap_view_auth /gmap_view_frag. apply view_both_validI_1.
    intros n a. ouPred.unseal. apply gmap_view.gmap_view_rel_lookup.
  Qed.

  Lemma gmap_view_frag_op_validI k dq1 dq2 v1 v2 :
    ✓ (gmap_view_frag k dq1 v1 ⋅ gmap_view_frag k dq2 v2) ⊣⊢
    ✓ (dq1 ⋅ dq2) ∧ v1 ≡ v2.
  Proof.
    rewrite /gmap_view_frag -view_frag_op. apply view_frag_validI=> n x.
    rewrite gmap_view.gmap_view_rel_exists singleton_op singleton_validN.
    rewrite pair_validN to_agree_op_validN. by ouPred.unseal.
  Qed.

End gmap_view.

End oupred.
