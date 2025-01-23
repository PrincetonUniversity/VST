From VST.lithium Require Import definitions simpl_classes proof_state.

Inductive LVAR_HINT {A} (name : string) (x : A) : Prop := { lvar_locked : locked True }.
Definition lvar (name : string) (A : Type) : Type := A.

Definition set_lvar {prop:bi} {A} (name : string) (x : A) : prop := True.
Global Typeclasses Opaque set_lvar.

Notation "'lvar' id : v" := (LVAR_HINT id v) (at level 200, only printing).

Lemma simplify_goal_set_lvar (prop:bi) A (x : A) name (T : prop) :
  (<affine>⌜LVAR_HINT name x⌝ -∗ T) ⊢ simplify_goal (set_lvar name x) T.
Proof.
  iIntros "HT". rewrite /set_lvar. iSplit => //. iApply "HT".
  iPureIntro. constructor. by unlock.
Qed.
Definition simplify_goal_set_lvar_inst := [instance simplify_goal_set_lvar with 0%N].
Global Existing Instance simplify_goal_set_lvar_inst.

Lemma simpl_exist_lvar (prop:bi) A (x : A) name :
  LVAR_HINT name x →
  @SimplExist prop (lvar name A) (λ P, P x)%I.
Proof. move => ?. rewrite /SimplExist. iIntros (?) "?". iExists _. iFrame. Qed.
Global Hint Extern 2 (SimplExist (lvar ?i _) _) =>
         (notypeclasses refine (simpl_exist_lvar _ _ _ _ _); eassumption) : typeclass_instances.
