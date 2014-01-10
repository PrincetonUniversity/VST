Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import sepcomp.StructuredInjections.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.pred_lemmas.

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

Lemma pubBlocksLocalSrc (mu : SMInj.t) :
  {subset (pubBlocksSrc mu) <= locBlocksSrc mu}.  
Proof. by move=> b; apply: pubBlocksLocalSrc; apply: SMInj_wd. Qed.

Lemma pubBlocksLocalTgt (mu : SMInj.t) : 
  {subset (pubBlocksTgt mu) <= locBlocksTgt mu}.  
Proof. by move=> b; apply: pubBlocksLocalTgt; apply: SMInj_wd. Qed.

Lemma pubBlocksExportedSrc m1 (mu : SMInj.t) vals :
  {subset (pubBlocksSrc mu) <= REACH m1 (exportedSrc mu vals)}.
Proof. 
move=> b A; apply: REACH_nil; apply/orP; right; apply: pubSrc_shared=> //.
by apply: SMInj_wd.
Qed.

Lemma pubBlocksExportedTgt m1 (mu : SMInj.t) vals : 
  {subset (pubBlocksTgt mu) <= REACH m1 (exportedTgt mu vals)}.
Proof. 
move=> b A; apply: REACH_nil; apply/orP; right. 
by rewrite/sharedTgt; apply/orP; right.
Qed.

Lemma pubBlocksLocReachSrc m1 (mu : SMInj.t) vals :
  {subset (pubBlocksSrc mu) 
   <= [predI locBlocksSrc mu & REACH m1 (exportedSrc mu vals)]}.
Proof.
apply: subsetI; first by apply: pubBlocksLocalSrc.
by apply: pubBlocksExportedSrc.
Qed.

Lemma pubBlocksLocReachTgt m1 (mu : SMInj.t) vals :
  {subset (pubBlocksTgt mu) 
   <= [predI locBlocksTgt mu & REACH m1 (exportedTgt mu vals)]}.
Proof.
apply: subsetI; first by apply: pubBlocksLocalTgt.
by apply: pubBlocksExportedTgt.
Qed.

Lemma replace_reach_wd m1 m2 (mu : SMInj.t) vals1 vals2 :
  Memory.Mem.inject (as_inj mu) m1 m2 ->
  List.Forall2 (Values.val_inject (as_inj mu)) vals1 vals2 ->
  SM_wd (replace_locals mu
          [predI locBlocksSrc mu & REACH m1 (exportedSrc mu vals1)]
          [predI locBlocksTgt mu & REACH m2 (exportedTgt mu vals2)]).
Proof.
move=> A B; apply: replace_locals_wd; first by case: mu A B.
move=> b1; rewrite/predI/=/in_mem/=; move/andP=> []C D.
case: (REACH_local_REACH mu (SMInj_wd mu) _ _ _ _ A B _ D C)=> b2 []d2 []E F.
exists b2, d2; split=> //; apply/andP; split=> //.
by case: (local_locBlocks mu (SMInj_wd mu) _ _ _ E)=> _; case.
by move=> b /andP /= => [] []; rewrite/in_mem /= => C D.
Qed.

Lemma sm_sep_step (mu0 mu mu' : SMInj.t) m10 m20 m1 m2
  (val : sm_valid mu0 m10 m20)
  (sep1 : sm_inject_separated mu0 mu m10 m20)
  (sep2 : sm_inject_separated mu mu' m1 m2)
  (fwd1 : mem_forward m10 m1)
  (fwd2 : mem_forward m20 m2)
  (incr : Values.inject_incr (as_inj mu) (as_inj mu')) :
  sm_inject_separated mu0 mu' m10 m20.
Proof.
case: sep1=> A []B C; split.
move=> b1 b2 d H1 H2; case S: (as_inj mu b1)=> [[b2' d']|].
move: (incr _ _ _ S); rewrite H2; case=> b2b2' dd'; subst b2' d'.
by apply: (A _ _ _ H1 S).
case: sep2=> A' []B' C'; case: (A' _ _ _ S H2)=> D E; split.
+ have D': DomSrc mu' b1. 
    by case: (as_inj_DomRng _ _ _ _ H2)=> //; apply: (SMInj_wd mu').
  move: (B' _ D D')=> V1.
  have V0: ~Memory.Mem.valid_block m10 b1 
    by move=> ?; apply: V1; case: (fwd1 b1).
  by case F: (DomSrc mu0 b1)=> //; case: val; move/(_ b1 F).
+ have E': DomTgt mu' b2. 
    by case: (as_inj_DomRng _ _ _ _ H2)=> //; apply: (SMInj_wd mu').
  move: (C' _ E E')=> V2.
  have V0: ~Memory.Mem.valid_block m20 b2 
    by move=> ?; apply: V2; case: (fwd2 b2).
  by case F: (DomTgt mu0 b2)=> //; case: val=> _; move/(_ b2 F).
case: sep2=> A' []B' C'; split.
+ move=> b1 D E.
  case F: (DomSrc mu b1); first by apply: (B _ D F).
  by move: (B' _ F E)=> V1 V0; apply: V1; case: (fwd1 b1).
+ move=> b2 D E.
  case F: (DomTgt mu b2); first by apply: (C _ D F).
  by move: (C' _ F E)=> V1 V0; apply: V1; case: (fwd2 b2).
Qed.

Definition smvalid_src (mu : SMInj.t) m1 := 
  forall b1, DOM mu b1 -> Memory.Mem.valid_block m1 b1.
