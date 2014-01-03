Add LoadPath "..".
Require Import msl.Axioms.

Require Import sepcomp.effect_semantics.

Require Import sepcomp.pos.
Require Import sepcomp.linking.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Require Import compcert.common.AST. (*for ident*)
Require Import compcert.common.Values. 
Require Import compcert.common.Globalenvs. 

Section linkingLemmas.

Import Linker.
Import Static.

Variable N : pos.
Variable (cores : 'I_N -> Static.t). 
Variable fun_tbl : ident -> option 'I_N.
Variable entry_points : seq (val*val*signature).
Variable my_ge : ge_ty.

Let linker := effsem N cores fun_tbl.

Lemma peek_upd (st : Linker.linker N cores) c : 
  peekCore st = Some c -> 
  updCore st (Core.upd c (Core.c c)) = st.
Proof.
rewrite/updCore/updStack; case: st=> //= fn_tbl; rewrite/peekCore; case.
case=> // a l ? /=; case=> ->; do 2 f_equal.
move=> _ _; case=> -> -> //. 
by case: c.
by apply: proof_irr.
Qed.

Lemma upd_peek (st : Linker.linker N cores) c : 
  peekCore (updCore st c) = Some c.
Proof. by []. Qed.

Lemma upd_upd (st : Linker.linker N cores) c c' :
  updCore (updCore st c) c' = updCore st c'.
Proof. 
case: st=> ? ?; rewrite/updCore/updStack /=; do 2 f_equal.
by apply: proof_irr.
Qed.

Lemma step_STEP {U c1 st1 m1 c1' m1'} (A : peekCore st1 = Some c1) :
  effect_semantics.effstep 
    (coreSem (cores (Core.i c1))) (ge (cores (Core.i c1))) 
    U (Core.c c1) m1 c1' m1' -> 
  effect_semantics.effstep linker my_ge 
  U st1 m1 (updCore st1 (Core.upd c1 c1')) m1'.
Proof.
move=> STEP; move: (@effstep_corestep _ _ _ _ _ _ _ _ _ STEP)=> STEP'; split.
by left; rewrite/Sem.corestep0/effstep0 A; exists c1'; split.
by move=> ?; rewrite/effstep0 A; exists c1'; split.
Qed.

Lemma stepN_STEPN {U c1 st1 m1 c1' m1'} (A : peekCore st1 = Some c1) n :
  effect_semantics.effstepN 
    (coreSem (cores (Core.i c1))) (ge (cores (Core.i c1))) 
    n U (Core.c c1) m1 c1' m1' -> 
  effect_semantics.effstepN linker my_ge 
  n U st1 m1 (updCore st1 (Core.upd c1 c1')) m1'.
Proof.
move: A; move: st1 c1 c1' m1 U; elim: n.
by move=> //= U m1 c1' c1 st1 A; case=> <- <-; rewrite peek_upd.
move=> n IH st1 c1 c1' m1 U A /= => [][]c1'' []m1'' []B C.
exists (updCore st1 (Core.upd c1 c1'')), m1''; split.
by apply: (step_STEP A B).
have A': peekCore (updCore st1 (Core.upd c1 c1'')) = Some (Core.upd c1 c1'').
 by rewrite upd_peek.
set U' := fun b ofs => U b ofs || StructuredInjections.freshloc m1 m1'' b.
by move: (IH _ (Core.upd c1 c1'') c1' m1'' U' A'); rewrite upd_upd; apply.
Qed.

Lemma stepPLUS_STEPPLUS 
  {U c1 st1 m1 c1' m1'} (A : peekCore st1 = Some c1) :
  effect_semantics.effstep_plus 
    (coreSem (cores (Core.i c1))) (ge (cores (Core.i c1))) 
    U (Core.c c1) m1 c1' m1' -> 
  effect_semantics.effstep_plus linker my_ge 
  U st1 m1 (updCore st1 (Core.upd c1 c1')) m1'.
Proof. 
by rewrite/effstep_plus=> [][]n; move/(stepN_STEPN A)=> B; exists n.
Qed.

Lemma stepSTAR_STEPSTAR 
  {U c1 st1 m1 c1' m1'} (A : peekCore st1 = Some c1) :
  effect_semantics.effstep_star
    (coreSem (cores (Core.i c1))) (ge (cores (Core.i c1))) 
    U (Core.c c1) m1 c1' m1' -> 
  effect_semantics.effstep_star linker my_ge 
  U st1 m1 (updCore st1 (Core.upd c1 c1')) m1'.
Proof. 
by rewrite/effstep_star=> [][]n; move/(stepN_STEPN A)=> B; exists n.
Qed.

End linkingLemmas.
