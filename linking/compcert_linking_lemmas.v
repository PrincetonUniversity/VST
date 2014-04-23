Require Import msl.Axioms.

Require Import sepcomp.effect_semantics.

Require Import linking.pos.
Require Import linking.compcert_linking.
Require Import linking.core_semantics_lemmas.

Require Import ssreflect ssrbool ssrnat ssrfun seq fintype.
Set Implicit Arguments.

Require Import compcert.common.AST. (*for ident*)
Require Import compcert.common.Values. 
Require Import compcert.common.Globalenvs. 

Section linkingLemmas.

Import Linker.
Import Modsem.

Variable N : pos.
Variable cores : 'I_N -> Modsem.t. 
Variable fun_tbl : ident -> option 'I_N.
Variable my_ge : ge_ty.

Let linker := effsem N cores fun_tbl.

Lemma peek_upd (st : Linker.t N cores) : 
  updCore st (peekCore st) = st.
Proof.
case: st=> fn_tbl; case; case=> //= a l pf.
by case: a pf=> ? c pf /=; do 2 f_equal=> //=; apply: proof_irr.
Qed.

Lemma upd_peek (st : Linker.t N cores) c : peekCore (updCore st c) = c.
Proof. by []. Qed.

Lemma upd_upd (st : Linker.t N cores) c c' :
  updCore (updCore st c) c' = updCore st c'.
Proof. by case: st=> ? ? /=; do 2 f_equal; apply: proof_irr. Qed.

Lemma step_STEP {U st1 m1 c1' m1'} : 
  let: c1 := peekCore st1 in
  effect_semantics.effstep 
    (sem (cores (Core.i c1))) 
    (ge (cores (Core.i c1))) U (Core.c c1) m1 c1' m1' -> 
  effect_semantics.effstep linker my_ge 
  U st1 m1 (updCore st1 (Core.upd c1 c1')) m1'.
Proof.
move=> STEP; move: (@effstep_corestep _ _ _ _ _ _ _ _ _ STEP)=> STEP'; split.
by left; exists c1'; split.
by move=> ?; exists c1'; split.
by move=> H b ofs; case: H; rewrite/LinkerSem.corestep0; exists c1'; split.
Qed.

Lemma stepN_STEPN {U st1 m1 c1' m1' n} :
  let: c1 := peekCore st1 in
  effect_semantics.effstepN 
    (sem (cores (Core.i c1))) 
    (ge (cores (Core.i c1))) n U (Core.c c1) m1 c1' m1' -> 
  effect_semantics.effstepN linker my_ge 
  n U st1 m1 (updCore st1 (Core.upd c1 c1')) m1'.
Proof.
move: st1 c1' m1 U; elim: n.
case=> ?; case; case=> // a l pf x ? ?; case; case=> /= <- <- <-; split=> //.
do 3 f_equal. move=> // _ _; case=> <- <-; f_equal=> //.
by move: pf x; case: a=> //. 
by apply: proof_irr.
move=> n IH st1 c1' m1 U /= => [][]c1'' []m1'' []U1 []U2 []B []C D.
exists (updCore st1 (Core.upd (peekCore st1) c1'')), m1'',U1,U2; split.
by apply: (step_STEP B).
move: (IH (updCore st1 (Core.upd (peekCore st1) c1'')) c1' m1'' U2).
by rewrite upd_upd=> H; split=> //; move: H; apply; apply: C.
Qed.

Lemma stepPLUS_STEPPLUS {U st1 m1 c1' m1'} :
  let: c1 := peekCore st1 in
  effect_semantics.effstep_plus 
    (sem (cores (Core.i c1))) 
    (ge (cores (Core.i c1))) U (Core.c c1) m1 c1' m1' -> 
  effect_semantics.effstep_plus linker my_ge 
  U st1 m1 (updCore st1 (Core.upd c1 c1')) m1'.
Proof. by rewrite/effstep_plus=> [][]n; move/stepN_STEPN=> B; exists n. Qed.

Lemma stepSTAR_STEPSTAR {U st1 m1 c1' m1'} :
  let: c1 := peekCore st1 in
  effect_semantics.effstep_star
    (sem (cores (Core.i c1))) 
    (ge (cores (Core.i c1))) U (Core.c c1) m1 c1' m1' -> 
  effect_semantics.effstep_star linker my_ge 
  U st1 m1 (updCore st1 (Core.upd c1 c1')) m1'.
Proof. by rewrite/effstep_star=> [][]n; move/stepN_STEPN=> B; exists n. Qed.

End linkingLemmas.
