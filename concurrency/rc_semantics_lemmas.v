Require Import Bool.
Require Import ZArith.
Require Import BinPos.

Require Import Axioms.

Require Import compcert_imports. Import CompcertCommon.

Require Import sepcomp. Import SepComp.
Require Import arguments.

Require Import rc_semantics.

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import SM_simulation.

Section rc_2lems.

Variables F_S V_S F_T V_T : Type.

Variables C D : Type.

Variable eff_S : @EffectSem (Genv.t F_S V_S) C.

Variable eff_T : @EffectSem (Genv.t F_T V_T) D.

Variable ge_S : Genv.t F_S V_S.

Variable ge_T : Genv.t F_T V_T.

Variable sim : SM_simulation_inject eff_S eff_T ge_S ge_T.

Lemma rc_sim : 
  SM_simulation_inject (RC.effsem eff_S) eff_T ge_S ge_T.
Proof.
case: sim=> cd mtch ord e f g genv_infos h i j init step halt atext aftext. 
eapply Build_SM_simulation_inject with
       (core_data   := cd)
       (core_ord    := ord)
       (match_state := 
         fun cd mu c m d tm => 
           mtch cd mu (RC.core c) m d tm); eauto.
{ move=> v vals1 c1 m1 j0 vals2 m2 dS dT.
move=> init1 inj vinj pres pres2 H I resp1 resp2 J K.
have [c1' init1']:
  exists c1', initial_core eff_S ge_S v vals1 = Some c1'.
{ move: init1; rewrite /= /RC.initial_core.
  case x: (initial_core _ _ _ _)=> //.
  by case; case: c1=> c ?; case=> -> _; exists c. }
move: (init v vals1 c1' m1 j0 vals2 m2 dS dT init1').
case/(_ inj vinj pres pres2 H I resp1 resp2 J K)=> x []c2' []init2' mtch12.
exists x,c2'; split=> //.
move: init1; rewrite /= /RC.initial_core; rewrite init1'; case.
by case: c1=> ? ?; case=> <- <- /=. }
{ move=> st1 m1 st1' m1' U1 estep cd0 st2 mu m2 mtch12.
move: estep; rewrite /= /RC.effstep=> [][]estep []ctnd' locs.
move: (step (RC.core st1) m1 (RC.core st1') m1' U1 estep cd0).
case/(_ st2 mu m2 mtch12)=> st2' []m2' []cd' []mu'.
case=> incr (*[]sep*) []localloc []mtch12' []U2 []estep' trackback.
exists st2',m2',cd',mu'=> /=.
split=> //.
split=> //.
split=> //.
split=> //.
by exists estep'.                    
(*by exists U2.*) }
{ move=> cd0 mu c1 m1 c2 m2 v1 M; rewrite /= /RC.halted.
  case hlt1: (halted _ _)=> //.
  case def1: (vals_def _)=> //; case=> <-.
  case: (halt _ _ _ _ _ _ _ M hlt1)=> v2 []? []? ?.
  exists v2; split=> //. }                                         
{ move=> cd0 mu c1 m1 c2 m2 e0 vals1 ef_sig mtch' at1.
have at1': at_external eff_S (RC.core c1) = Some (e0, ef_sig, vals1).
{ move: at1; rewrite /= /RC.at_external.
  by case q: (at_external _ _)=> [[[? ?] ?]|//]; case r: (vals_def _). }
case: (atext cd0 mu (RC.core c1) m1 c2 m2 e0 vals1 ef_sig mtch' at1').
by move=> H H2; split. }
{ move=> cd0 mu st1 st2 m1 e0 vals1 m2 sig vals2 e' ef_sig'.
move=> inj mtch' at1 at2 vinj pSrc' H pTgt' I nu J nu' ret1 m1' ret2 m2'.
move=> ty1 ty2 eincr sep wd val inj' vinj' fwd fwd' rdo rdo' fS' K fT' L mu' M unch1 unch2.
have at1': at_external eff_S (RC.core st1) = Some (e0, sig, vals1).
{ move: at1; rewrite /= /RC.at_external.
  by case q: (at_external _ _)=> [[[? ?] ?]|//]; case r: (vals_def _). }
case: (aftext cd0 mu (RC.core st1) st2 m1 e0 vals1 m2 sig vals2 e' ef_sig'
  inj mtch' at1' at2 vinj pSrc' H pTgt' I nu J nu' ret1 m1' ret2 m2'
  ty1 ty2 eincr sep wd val inj' vinj' fwd fwd' rdo rdo' fS' K fT' L mu' M unch1 unch2).
move=> cd' []st1' []st2' []aft1' []aft2' mtch12'.
exists cd'.
exists (RC.mk st1' [predU getBlocks [::ret1] & RC.locs st1]).
exists st2'.
split=> //.
by rewrite /= /RC.after_external aft1'. }
Qed.

End rc_2lems.
