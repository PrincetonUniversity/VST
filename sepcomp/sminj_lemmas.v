Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Bool.

Require Import compcert.common.Globalenvs.

Require Import msl.Axioms.

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

Lemma sm_sep_step (mu0 mu : SM_Injection) (mu' : SMInj.t) m10 m20 m1 m2
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

Lemma DOM_replace_locals mu S T b :
  DOM (replace_locals mu S T) b -> 
  DOM mu b.
Proof. by case: mu. Qed.

Lemma smvalid_src_replace_locals mu m S T : 
  smvalid_src mu m -> 
  smvalid_src (replace_locals mu S T) m.
Proof. by move=> H b H2; apply: (H b); apply (DOM_replace_locals H2). Qed.

Lemma smvalid_src_DOM_valid mu m b :
  smvalid_src mu m -> 
  DOM mu b -> 
  Memory.Mem.valid_block m b.
Proof. by apply. Qed.

Lemma smvalid_src_mem_forward mu m m' : 
  smvalid_src mu m -> 
  mem_forward m m' -> 
  smvalid_src mu m'.
Proof.
move=> H H2 b; move: (H2 b)=> H3 H4; case: H3=> //.
by apply: (smvalid_src_DOM_valid H H4).
Qed.

Definition validblock (m : Memory.Mem.mem) (b : Values.block) :=
  BinPos.Pos.ltb b (Memory.Mem.nextblock m).

Lemma validblock_valid_block m b : 
  validblock m b <-> Memory.Mem.valid_block m b.
Proof.
by rewrite/validblock/Memory.Mem.valid_block /Coqlib.Plt -BinPos.Pos.ltb_lt.
Qed.

Lemma smvalid_locsrc_bound mu m :
  smvalid_src mu m -> 
  [pred b | locBlocksSrc mu b]
  = [predI (locBlocksSrc mu) & [pred b | validblock m b]].
Proof.
rewrite/smvalid_src/DOM/DomSrc=> A.
rewrite/predI/in_mem/=; f_equal; extensionality a.
case H: (a \in [pred b | validblock m b]); first by rewrite/in_mem/=andb_true_r.
rewrite/in_mem/= in H; move: (@validblock_valid_block m a); rewrite H.
case=> // _ B; move: (A a); case: (locBlocksSrc mu a)=> //= C. 
by move: (B (C erefl)).
by case: (a \in locBlocksSrc mu).
Qed.

Lemma smvalid_loctgt_bound mu m :
  smvalid_tgt mu m -> 
  [pred b | locBlocksTgt mu b]
  = [predI (locBlocksTgt mu) & [pred b | validblock m b]].
Proof.
rewrite/smvalid_tgt/RNG/DomTgt=> A.
rewrite/predI/in_mem/=; f_equal; extensionality a.
case H: (a \in [pred b | validblock m b]); first by rewrite/in_mem/=andb_true_r.
rewrite/in_mem/= in H; move: (@validblock_valid_block m a); rewrite H.
case=> // _ B; move: (A a); case: (locBlocksTgt mu a)=> //= C. 
by move: (B (C erefl)).
by case: (a \in locBlocksTgt mu).
Qed.

Lemma smvalid_extsrc_bound mu m :
  smvalid_src mu m -> 
  [pred b | extBlocksSrc mu b]
  = [predI (extBlocksSrc mu) & [pred b | validblock m b]].
Proof.
rewrite/smvalid_src/DOM/DomSrc=> A.
rewrite/predI/in_mem/=; f_equal; extensionality a.
case H: (a \in [pred b | validblock m b]); first by rewrite/in_mem/=andb_true_r.
rewrite/in_mem/= in H; move: (@validblock_valid_block m a); rewrite H.
case=> // _ B; move: (A a); case: (extBlocksSrc mu a)=> //= C. 
by rewrite orb_true_r in C; move: (B (C erefl)).
by case: (a \in extBlocksSrc mu).
Qed.

Lemma smvalid_exttgt_bound mu m :
  smvalid_tgt mu m -> 
  [pred b | extBlocksTgt mu b]
  = [predI (extBlocksTgt mu) & [pred b | validblock m b]].
Proof.
rewrite/smvalid_tgt/RNG/DomTgt=> A.
rewrite/predI/in_mem/=; f_equal; extensionality a.
case H: (a \in [pred b | validblock m b]); first by rewrite/in_mem/=andb_true_r.
rewrite/in_mem/= in H; move: (@validblock_valid_block m a); rewrite H.
case=> // _ B; move: (A a); case: (extBlocksTgt mu a)=> //= C. 
by rewrite orb_true_r in C; move: (B (C erefl)).
by case: (a \in extBlocksTgt mu).
Qed.

Lemma pubsrc_sub_locsrc (mu : SMInj.t) : 
  {subset (pubBlocksSrc mu) <= locBlocksSrc mu}.
Proof. 
move=> b; apply: StructuredInjections.pubBlocksLocalSrc.
by apply: SMInj_wd.
Qed.

Lemma pubtgt_sub_loctgt (mu : SMInj.t) : 
  {subset (pubBlocksTgt mu) <= locBlocksTgt mu}.
Proof. 
move=> b; apply: StructuredInjections.pubBlocksLocalTgt.
by apply: SMInj_wd.
Qed.

Lemma frgnsrc_sub_extsrc (mu : SMInj.t) : 
  {subset (frgnBlocksSrc mu) <= extBlocksSrc mu}.
Proof. 
move=> b; apply: frgnBlocksSrc_extBlocksSrc.
by apply: SMInj_wd.
Qed.

Lemma frgntgt_sub_exttgt (mu : SMInj.t) : 
  {subset (frgnBlocksTgt mu) <= extBlocksTgt mu}.
Proof. 
move=> b A; case: (SMInj_wd mu)=> ? ? ? ? ? ? ?.
by move/(_ b A).
Qed.

Lemma smvalid_pubsrc_bound (mu : SMInj.t) m :
  smvalid_src mu m -> 
  [pred b | pubBlocksSrc mu b]
  = [predI (pubBlocksSrc mu) & [pred b | validblock m b]].
Proof.
move=> A.
by rewrite -(predI_sub3 (sym_eq (smvalid_locsrc_bound A)) 
            (@pubsrc_sub_locsrc mu)).
Qed.

Lemma smvalid_pubtgt_bound (mu : SMInj.t) m :
  smvalid_tgt mu m -> 
  [pred b | pubBlocksTgt mu b]
  = [predI (pubBlocksTgt mu) & [pred b | validblock m b]].
Proof.
move=> A.
by rewrite -(predI_sub3 (sym_eq (smvalid_loctgt_bound A)) 
            (@pubtgt_sub_loctgt mu)).
Qed.

Lemma smvalid_frgnsrc_bound (mu : SMInj.t) m :
  smvalid_src mu m -> 
  [pred b | frgnBlocksSrc mu b]
  = [predI (frgnBlocksSrc mu) & [pred b | validblock m b]].
Proof.
move=> A.
by rewrite -(predI_sub3 (sym_eq (smvalid_extsrc_bound A)) 
            (@frgnsrc_sub_extsrc mu)).
Qed.

Lemma smvalid_frgntgt_bound (mu : SMInj.t) m :
  smvalid_tgt mu m -> 
  [pred b | frgnBlocksTgt mu b]
  = [predI (frgnBlocksTgt mu) & [pred b | validblock m b]].
Proof.
move=> A.
by rewrite -(predI_sub3 (sym_eq (smvalid_exttgt_bound A)) 
            (@frgntgt_sub_exttgt mu)).
Qed.

Lemma smvalid_locsrc_disjoint mu m :
  smvalid_src mu m -> 
  Disjoint (locBlocksSrc mu) [pred b | ~~ validblock m b].
Proof.
move/smvalid_locsrc_bound=> A.
change (Disjoint [pred b | locBlocksSrc mu b] [pred b | ~~ validblock m b]).
by rewrite A; apply: DisjointInI.
Qed.

Lemma smvalid_loctgt_disjoint mu m :
  smvalid_tgt mu m -> 
  Disjoint (locBlocksTgt mu) [pred b | ~~ validblock m b].
Proof.
move/smvalid_loctgt_bound=> A.
change (Disjoint [pred b | locBlocksTgt mu b] [pred b | ~~ validblock m b]).
by rewrite A; apply: DisjointInI.
Qed.

Lemma sminjsep_locsrc mu (mu' : SMInj.t) m1 m2 :
  intern_incr mu mu' -> 
  sm_valid mu m1 m2 -> 
  sm_inject_separated mu mu' m1 m2 -> 
  {subset [predD (locBlocksSrc mu') & locBlocksSrc mu]
  <= [pred b | ~~ validblock m1 b]}.
Proof.
move=> INCR V []A []B C b; rewrite in_predD; move/andP. 
rewrite/in_mem/= => [][]D; rewrite/is_true negb_true_iff=> E. 
apply/negP; rewrite validblock_valid_block=> F; move: (B b). 
rewrite /DomSrc D E; apply=> //=; case H: (extBlocksSrc _ _)=> //.
move: H; case: INCR=> []_ []_ []_ []_ []_ []_ []_ []_ []-> _ G.
by case: (SMInj_wd mu'); move/(_ b); rewrite D G; case.
Qed.

Lemma sminjsep_loctgt mu (mu' : SMInj.t) m1 m2 :
  intern_incr mu mu' -> 
  sm_valid mu m1 m2 -> 
  sm_inject_separated mu mu' m1 m2 -> 
  {subset [predD (locBlocksTgt mu') & locBlocksTgt mu]
  <= [pred b | ~~ validblock m2 b]}.
Proof.
move=> INCR V []A []B C b; rewrite in_predD; move/andP. 
rewrite/in_mem/= => [][]D; rewrite/is_true negb_true_iff=> E. 
apply/negP; rewrite validblock_valid_block=> F; move: (C b).
rewrite /DomTgt D E; apply=> //=; case H: (extBlocksTgt mu b)=> //.
move: H; case: INCR=> []_ []_ []_ []_ []_ []_ []_ []_ []_ -> G.
by case: (SMInj_wd mu')=> _; move/(_ b); rewrite D G; case.
Qed.

Lemma sm_inject_separated_refl mu m m' : sm_inject_separated mu mu m m'.
Proof.
split; first by move=> ? ? ? ->; discriminate.
split; first by move=> ? ->; discriminate.
by move=> ? ->; discriminate.
Qed.

Definition join_sm' mu1 mu2 : SM_Injection :=
  Build_SM_Injection 
    [predU (locBlocksSrc mu1) & locBlocksSrc mu2]
    [predU (locBlocksTgt mu1) & locBlocksTgt mu2]
    [predU (pubBlocksSrc mu1) & pubBlocksSrc mu2]
    [predU (pubBlocksTgt mu1) & pubBlocksTgt mu2]
    (join (local_of mu1) (local_of mu2))
    [predU (extBlocksSrc mu1) & extBlocksSrc mu2]
    [predU (extBlocksTgt mu1) & extBlocksTgt mu2]
    [predU (frgnBlocksSrc mu1) & frgnBlocksSrc mu2]
    [predU (frgnBlocksTgt mu1) & frgnBlocksTgt mu2]
    (join (extern_of mu1) (extern_of mu2)).

Definition join_sm mu1 mu2 := 
  let mu := join_sm' mu1 mu2 in
  let extSrc := [predD (extBlocksSrc mu) & locBlocksSrc mu] in
  Build_SM_Injection
    (locBlocksSrc mu) (locBlocksTgt mu)
    (pubBlocksSrc mu) (pubBlocksTgt mu)
    (local_of mu)
    [predD (extBlocksSrc mu) & locBlocksSrc mu] 
    [predD (extBlocksTgt mu) & locBlocksTgt mu] 
    [predD (frgnBlocksSrc mu) & locBlocksSrc mu] 
    [predD (frgnBlocksTgt mu) & locBlocksTgt mu] 
    (restrict (extern_of mu) extSrc).

Lemma join_sm_wd (mu1 mu2 : SMInj.t) : SM_wd (join_sm mu1 mu2).
Proof.
apply: Build_SM_wd=> /=.
by move=> b; case H: (b \in [predU _ & _]); [right|left].
by move=> b; case H: (b \in [predU _ & _]); [right|left].
move=> b1 b2 z; rewrite/join; case H: (local_of mu1 b1)=> [[b' d']|] A.
case: (local_DomRng _ (SMInj_wd mu1) _ _ _ H).
by case: A=> -> _; rewrite/mem/in_mem/= => -> ->.
case: (local_DomRng _ (SMInj_wd mu2) _ _ _ A).
by rewrite/mem/in_mem/= => -> ->; split; apply/orP; right.
move=> b1 b2 z A; split.
apply/andP.
Admitted. (*tedious*)

Fixpoint join_all (mus : seq SMInj.t) : SM_Injection :=
  if mus is [:: mu & mus] then join_sm mu (join_all mus)
  else SMInj.empty'.

Lemma join_all_wd (mus : seq SMInj.t) : SM_wd (join_all mus).
Proof.
elim: mus=> //; first by apply: SMInj.wd_empty'.
move=> mu mus' IH /=.
have A: SM_wd (join_sm mu (SMInj.Build_t IH)) by apply: join_sm_wd.
by apply: A.
Qed.

Definition assimilated mu0 mu := join_sm mu0 mu = mu.

Lemma assimilated_sub_locSrc mu0 mu :
  assimilated mu0 mu -> {subset (locBlocksSrc mu0) <= locBlocksSrc mu}. 
Proof. by rewrite/assimilated/join_sm=> <- b /= => A; apply/orP; left. Qed.

Lemma assimilated_sub_locTgt mu0 mu :
  assimilated mu0 mu -> {subset (locBlocksTgt mu0) <= locBlocksTgt mu}. 
Proof. by rewrite/assimilated/join_sm=> <- b /= => A; apply/orP; left. Qed.

Lemma assimilated_sub_pubSrc mu0 mu :
  assimilated mu0 mu -> {subset (pubBlocksSrc mu0) <= pubBlocksSrc mu}. 
Proof. by rewrite/assimilated/join_sm=> <- b /= => A; apply/orP; left. Qed.

Lemma assimilated_sub_pubTgt mu0 mu :
  assimilated mu0 mu -> {subset (pubBlocksTgt mu0) <= pubBlocksTgt mu}. 
Proof. by rewrite/assimilated/join_sm=> <- b /= => A; apply/orP; left. Qed.

Lemma assimilated_sub_extSrc mu0 mu :
  assimilated mu0 mu -> {subset (locBlocksSrc mu0) <= locBlocksSrc mu}. 
Proof. by rewrite/assimilated/join_sm=> <- b /= => A; apply/orP; left. Qed.

Lemma join_sm_extSrc mu1 mu2 : 
  {subset (extBlocksSrc (join_sm mu1 mu2)) 
  <= [predU (extBlocksSrc mu1) & extBlocksSrc mu2]}.
Proof. by rewrite/join_sm/= => b; rewrite/in_mem/=; move/andP=> []A B. Qed.

Lemma join_sm_extTgt mu1 mu2 : 
  {subset (extBlocksTgt (join_sm mu1 mu2)) 
  <= [predU (extBlocksTgt mu1) & extBlocksTgt mu2]}.
Proof. by rewrite/join_sm/= => b; rewrite/in_mem/=; move/andP=> []A B. Qed.

Lemma join_sm_frgnSrc mu1 mu2 : 
  {subset (frgnBlocksSrc (join_sm mu1 mu2)) 
  <= [predU (frgnBlocksSrc mu1) & frgnBlocksSrc mu2]}.
Proof. by rewrite/join_sm/= => b; rewrite/in_mem/=; move/andP=> []A B. Qed.

Lemma join_sm_frgnTgt mu1 mu2 : 
  {subset (frgnBlocksTgt (join_sm mu1 mu2)) 
  <= [predU (frgnBlocksTgt mu1) & frgnBlocksTgt mu2]}.
Proof. by rewrite/join_sm/= => b; rewrite/in_mem/=; move/andP=> []A B. Qed.

Lemma join_sm_preserves_globals F V (ge : Genv.t F V) (mu1 mu2 : SMInj.t) : 
  Events.meminj_preserves_globals ge (extern_of mu1) -> 
  Events.meminj_preserves_globals ge (extern_of mu2) -> 
  Events.meminj_preserves_globals ge (extern_of (join_sm mu1 mu2)).
Proof.
move=> []A []B C []D []E G; rewrite/join_sm/=; split.
move=> id b H; move: (A _ _ H); move: (D _ _ H).
rewrite/restrict/=/in_mem/=/in_mem/=/join=> H2 H3.
have H4: extBlocksSrc mu1 b = true.
  by case: (extern_DomRng _ (SMInj_wd mu1) _ _ _ H3).
have H5: extBlocksSrc mu2 b = true.
  by case: (extern_DomRng _ (SMInj_wd mu2) _ _ _ H2).
have ->: locBlocksSrc mu1 b = false.
  by move: H4; case: (disjoint_extern_local_Src _ (SMInj_wd mu1) b)=> // ->.
have ->: locBlocksSrc mu2 b = false.
  case: (extern_DomRng _ (SMInj_wd mu2) _ _ _ H2).
  by move: H5; case: (disjoint_extern_local_Src _ (SMInj_wd mu2) b)=> // ->.
by rewrite H4 H5 H3.
split.
move=> b gv H. move: (B _ _ H); move: (E _ _ H). 
rewrite/restrict/=/in_mem/=/in_mem/=/join=> H2 H3.
have H4: extBlocksSrc mu1 b = true.
  by case: (extern_DomRng _ (SMInj_wd mu1) _ _ _ H3).
have H5: extBlocksSrc mu2 b = true.
  by case: (extern_DomRng _ (SMInj_wd mu2) _ _ _ H2).
have ->: locBlocksSrc mu1 b = false.
  by move: H4; case: (disjoint_extern_local_Src _ (SMInj_wd mu1) b)=> // ->.
have ->: locBlocksSrc mu2 b = false.
  case: (extern_DomRng _ (SMInj_wd mu2) _ _ _ H2).
  by move: H5; case: (disjoint_extern_local_Src _ (SMInj_wd mu2) b)=> // ->.
by rewrite H4 H5 H3.
move=> b1 b2 z gv H; move/restrictD_Some=> []; rewrite/join=> H2 H3.
move: H2; case H4: (extern_of mu1 b1)=> // [[b' z']|].
by move=> EQ; move: EQ H H4; case=> <- _ H H4; move: (C _ _ _ _ H H4).
by apply/(G _ _ _ _ H).
Qed.

Lemma join_sm_id mu : join_sm mu mu = mu.
Proof.
case: mu=> ? ? ? ? ? ? ? ? ? ?; rewrite/join_sm /=.
f_equal=> //.
Admitted.

Lemma join_sm_empty mu : join_sm mu SMInj.empty' = mu.
Proof.
case: mu=> ? ? ? ? ? ? ? ? ? ?; rewrite/join_sm /=.
f_equal=> //.
Admitted.

Lemma join_all_id mu : join_all [:: mu] = mu.
Proof. by rewrite/join_all; rewrite join_sm_empty. Qed.

Lemma join_all_frgnSrc mu1 mu2 : 
  {subset (frgnBlocksSrc (join_sm mu1 mu2)) 
  <= [predU (frgnBlocksSrc mu1) & frgnBlocksSrc mu2]}.
Proof. by rewrite/join_sm/= => b; rewrite/in_mem/=; move/andP=> []A B. Qed.

Fixpoint All T P (l : seq T) :=
  match l with
    | nil => True
    | a :: l' => [/\ P a & All P l']
  end.

Lemma join_all_preserves_globals F V (ge : Genv.t F V) (mus : seq.seq SMInj.t) : 
  length mus > 0 ->
  All (Events.meminj_preserves_globals ge \o extern_of \o SMInj.mu) mus -> 
  Events.meminj_preserves_globals ge (extern_of (join_all mus)).
Proof.
elim: mus=> // mu0 mus' IH; case: mus' IH.
by move=> _ _; rewrite join_all_id; case.
move=> mu1 mus' IH A B.
change (Events.meminj_preserves_globals 
  ge (extern_of (join_sm mu0 (join_all [:: mu1 & mus'])))).
have wd: SM_wd (join_all [:: mu1 & mus']) by apply: join_all_wd.
change (Events.meminj_preserves_globals 
  ge (extern_of (join_sm mu0 (SMInj.Build_t wd)))).
apply: join_sm_preserves_globals; first by case: B.
by move: B=> []C []D E; apply: IH.
Qed.



