Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import sepcomp.StructuredInjections.
Require Import sepcomp.effect_simulations.

Module SMInj.

Record t : Type := { mu : SM_Injection; _ : SM_wd mu }.

Definition empty' := 
  Build_SM_Injection 
  pred0 pred0 pred0 pred0 (fun _ => None)
  pred0 pred0 pred0 pred0 (fun _ => None).

Lemma wd_empty' : SM_wd empty'.
Proof. by rewrite/empty'; apply: Build_SM_wd=> //=; left. Qed.

Definition empty := Build_t wd_empty'.

End SMInj.

Coercion SMInj.mu : SMInj.t >-> SM_Injection.

Section SMInj_lems.

Variable mu : SMInj.t.

Lemma SMInj_wd : SM_wd mu.
Proof. by case: mu. Qed.

End SMInj_lems.

Lemma restrict_some mu b1 b2 d X : 
  (restrict mu X) b1 = Some (b2, d) -> mu b1 = Some (b2, d).
Proof. by rewrite/restrict; case: (X b1). Qed.

Lemma restrict_sm_domsrc mu b1 X : 
  DomSrc (restrict_sm mu X) b1 -> DomSrc mu b1.
Proof. by rewrite/restrict_sm; case: mu. Qed.

Lemma restrict_sm_domtgt mu b2 X : 
  DomTgt (restrict_sm mu X) b2 -> DomTgt mu b2.
Proof. by rewrite/restrict_sm; case: mu. Qed.

Lemma sm_inject_separated_restrict mu mu' m1 m2 X : 
  sm_inject_separated mu mu' m1 m2 -> 
  sm_inject_separated mu (restrict_sm mu' X) m1 m2.
Proof.
move=>[]H []H2 H3; split.
move=> b1 b2 d A; rewrite restrict_sm_all; move/restrict_some=> B.
by apply: (H _ _ _ A B).
split; first by move=> b1 A; move/restrict_sm_domsrc=> B; apply: (H2 _ A B).
by move=> b2 A; move/restrict_sm_domtgt=> B; apply: (H3 _ A B).
Qed.



