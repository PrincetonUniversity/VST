Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Bool.
Require Import Zbool.
Require Import BinPos. 

Require Import compcert_imports. Import CompcertCommon.

Require Import Axioms.

Require Import sepcomp. Import SepComp.

Require Import pred_lemmas.
Require Import seq_lemmas.

(* This file collects lemmas on structured injections.                    *)
(* [Inj.t] is the type of well-defined structured injections. It is       *)
(* coercible to [SM_Injection] via the coercion [Inj.mu].                 *)

Module Inj.

Record t : Type := mk { mu : SM_Injection; _ : SM_wd mu }.

Definition empty' := 
  Build_SM_Injection 
  pred0 pred0 pred0 pred0 (fun _ => None)
  pred0 pred0 pred0 pred0 (fun _ => None).

Lemma wd_empty' : SM_wd empty'.
Proof. by rewrite/empty'; apply: Build_SM_wd=> //=; left. Qed.

Definition empty := mk wd_empty'.

End Inj.

Coercion Inj.mu : Inj.t >-> SM_Injection.

Section Inj_lems.

Variable mu : Inj.t.

Lemma Inj_wd : SM_wd mu.
Proof. by case: mu. Qed.

(* Local-Frgn/Extern disjointness *)

Lemma Inj_DisjointLFS : Disjoint (locBlocksSrc mu) (frgnBlocksSrc mu).
Proof.
apply/DisjointP=> b; move: (frgnBlocksSrc_locBlocksSrc _ Inj_wd b).
case: (locBlocksSrc _ _); case: (frgnBlocksSrc _ _).
by move/(_ erefl). by right. by left. by left.
Qed.

Lemma Inj_DisjointLFT : Disjoint (locBlocksTgt mu) (frgnBlocksTgt mu).
Proof.
apply/DisjointP=> b; move: (frgnBlocksTgt_locBlocksTgt _ Inj_wd b).
case: (locBlocksTgt _ _); case: (frgnBlocksTgt _ _).
by move/(_ erefl). by right. by left. by left.
Qed.

Lemma Inj_DisjointLES : Disjoint (locBlocksSrc mu) (extBlocksSrc mu).
Proof.
apply/DisjointP=> b; move: (extBlocksSrc_locBlocksSrc _ Inj_wd b).
case: (locBlocksSrc _ _); case: (extBlocksSrc _ _).
by move/(_ erefl). by right. by left. by left.
Qed.

Lemma Inj_DisjointLET : Disjoint (locBlocksTgt mu) (extBlocksTgt mu).
Proof.
apply/DisjointP=> b; move: (extBlocksTgt_locBlocksTgt _ Inj_wd b).
case: (locBlocksTgt _ _); case: (extBlocksTgt _ _).
by move/(_ erefl). by right. by left. by left.
Qed.

End Inj_lems.

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
move=> b1 b2 d A; rewrite restrict_sm_all; move/restrictD_Some=> []B _.
by apply: (H _ _ _ A B).
split; first by move=> b1 A; move/restrict_sm_domsrc=> B; apply: (H2 _ A B).
by move=> b2 A; move/restrict_sm_domtgt=> B; apply: (H3 _ A B).
Qed.

Lemma as_inj_restrict_smE' mu X b1 : 
  as_inj (restrict_sm mu X) b1 = None -> 
  [\/ as_inj mu b1 = None | X b1=false].
Proof.
rewrite restrict_sm_all /restrict.
case: (X b1)=> //.
by left.
by right.
Qed.

Lemma sm_sep_restrict2 (mu : Inj.t) mu' m1 m2 X Y : 
  sm_valid mu m1 m2 -> 
  sm_inject_separated mu mu' m1 m2 -> 
  (forall b, X b=false -> Y b=true -> ~Memory.Mem.valid_block m1 b) -> 
  sm_inject_separated (restrict_sm mu X) (restrict_sm mu' Y) m1 m2.
Proof.
move=> W; move=> []H []H2 H3 Z; split.
move=> b1 b2 d A; rewrite restrict_sm_all. 
move/restrictD_Some=> []B C.
move: {A}(as_inj_restrict_smE' A); case.
rewrite restrict_sm_DomSrc restrict_sm_DomTgt.
by move=> A; apply: (H _ _ _ A B).
move=> D; move: {Z}(Z _ D C)=> E.
case: (W); move/(_ b1)=> U; move/(_ b2); move: U.
rewrite/DOM/RNG=> U V; split; move: U V. 
rewrite restrict_sm_DomSrc; case: (DomSrc mu b1)=> //. 
by move=> U; elimtype False; apply: E; apply U.
rewrite restrict_sm_DomTgt; case K: (DomTgt mu b2)=> //.
case G: (as_inj mu b1)=> [[? ?]|].
elimtype False.
case: (as_inj_DomRng _ _ _ _ G (Inj_wd _))=> I J.
case: W; rewrite/DOM; move/(_ b1); rewrite I=> Contra _.
by apply: E; apply: Contra.
by case: (H _ _ _ G B); rewrite K.
split.
rewrite !restrict_sm_DomSrc; move=> b1 A B.
by apply: (H2 _ A B).
rewrite !restrict_sm_DomTgt; move=> b1 A B.
by apply: (H3 _ A B).
Qed.

Lemma sm_sep_restrict (mu : Inj.t) mu' m1 m2 X : 
  sm_valid mu m1 m2 -> 
  sm_inject_separated mu mu' m1 m2 -> 
  sm_inject_separated (restrict_sm mu X) (restrict_sm mu' X) m1 m2.
Proof.
by move=> Z W; apply (sm_sep_restrict2 Z W); move=> b ->.
Qed.

Lemma sm_locally_allocated_restrict mu mu' m1 m2 m1' m2' X Y :
  sm_locally_allocated mu mu' m1 m2 m1' m2' -> 
  sm_locally_allocated (restrict_sm mu X) (restrict_sm mu' Y) m1 m2 m1' m2'.
Proof.
rewrite 2!sm_locally_allocatedChar.
move=> []A []B []C []D []E []F.
split; first by rewrite !restrict_sm_DomSrc.
split; first by rewrite !restrict_sm_DomTgt.
split; first by rewrite !restrict_sm_locBlocksSrc.
split; first by rewrite !restrict_sm_locBlocksTgt.
split; first by rewrite !restrict_sm_extBlocksSrc.
by rewrite !restrict_sm_extBlocksTgt.
Qed.

Lemma pubBlocksLocalSrc (mu : Inj.t) :
  {subset (pubBlocksSrc mu) <= locBlocksSrc mu}.  
Proof. by move=> b; apply: pubBlocksLocalSrc; apply: Inj_wd. Qed.

Lemma pubBlocksLocalTgt (mu : Inj.t) : 
  {subset (pubBlocksTgt mu) <= locBlocksTgt mu}.  
Proof. by move=> b; apply: pubBlocksLocalTgt; apply: Inj_wd. Qed.

Lemma pubBlocksExportedSrc m1 (mu : Inj.t) vals :
  {subset (pubBlocksSrc mu) <= REACH m1 (exportedSrc mu vals)}.
Proof. 
move=> b A; apply: REACH_nil; apply/orP; right; apply: pubSrc_shared=> //.
by apply: Inj_wd.
Qed.

Lemma pubBlocksExportedTgt m1 (mu : Inj.t) vals : 
  {subset (pubBlocksTgt mu) <= REACH m1 (exportedTgt mu vals)}.
Proof. 
move=> b A; apply: REACH_nil; apply/orP; right. 
by rewrite/sharedTgt; apply/orP; right.
Qed.

Lemma pubBlocksLocReachSrc m1 (mu : Inj.t) vals :
  {subset (pubBlocksSrc mu) 
   <= [predI locBlocksSrc mu & REACH m1 (exportedSrc mu vals)]}.
Proof.
apply: subsetI; first by apply: pubBlocksLocalSrc.
by apply: pubBlocksExportedSrc.
Qed.

Lemma pubBlocksLocReachTgt m1 (mu : Inj.t) vals :
  {subset (pubBlocksTgt mu) 
   <= [predI locBlocksTgt mu & REACH m1 (exportedTgt mu vals)]}.
Proof.
apply: subsetI; first by apply: pubBlocksLocalTgt.
by apply: pubBlocksExportedTgt.
Qed.

Lemma replace_reach_wd m1 m2 (mu : Inj.t) vals1 vals2 :
  Memory.Mem.inject (as_inj mu) m1 m2 ->
  List.Forall2 (Values.val_inject (as_inj mu)) vals1 vals2 ->
  SM_wd (replace_locals mu
          [predI locBlocksSrc mu & REACH m1 (exportedSrc mu vals1)]
          [predI locBlocksTgt mu & REACH m2 (exportedTgt mu vals2)]).
Proof.
move=> A B; apply: replace_locals_wd; first by case: mu A B.
move=> b1; rewrite/predI/=/in_mem/=; move/andP=> []C D.
case: (REACH_local_REACH mu (Inj_wd mu) _ _ _ _ A B _ D C)=> b2 []d2 []E F.
exists b2, d2; split=> //; apply/andP; split=> //.
by case: (local_locBlocks mu (Inj_wd mu) _ _ _ E)=> _; case.
by move=> b /andP /= => [] []; rewrite/in_mem /= => C D.
Qed.

Lemma sm_sep_step (mu0 mu : SM_Injection) (mu' : Inj.t) m10 m20 m1 m2
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
    by case: (as_inj_DomRng _ _ _ _ H2)=> //; apply: (Inj_wd mu').
  move: (B' _ D D')=> V1.
  have V0: ~Memory.Mem.valid_block m10 b1 
    by move=> ?; apply: V1; case: (fwd1 b1).
  by case F: (DomSrc mu0 b1)=> //; case: val; move/(_ b1 F).
+ have E': DomTgt mu' b2. 
    by case: (as_inj_DomRng _ _ _ _ H2)=> //; apply: (Inj_wd mu').
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
  DOM (replace_locals mu S T) b -> DOM mu b.
Proof. by case: mu. Qed.

Lemma smvalid_src_replace_locals mu m S T : 
  smvalid_src mu m -> 
  smvalid_src (replace_locals mu S T) m.
Proof. by move=> H b H2; apply: (H b); apply (DOM_replace_locals H2). Qed.

Lemma smvalid_src_DOM_valid mu m b :
  smvalid_src mu m -> DOM mu b -> Memory.Mem.valid_block m b.
Proof. by apply. Qed.

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

Lemma pubsrc_sub_locsrc (mu : Inj.t) : 
  {subset (pubBlocksSrc mu) <= locBlocksSrc mu}.
Proof. 
move=> b; apply: structured_injections.pubBlocksLocalSrc.
by apply: Inj_wd.
Qed.

Lemma pubtgt_sub_loctgt (mu : Inj.t) : 
  {subset (pubBlocksTgt mu) <= locBlocksTgt mu}.
Proof. 
move=> b; apply: structured_injections.pubBlocksLocalTgt.
by apply: Inj_wd.
Qed.

Lemma frgnsrc_sub_extsrc (mu : Inj.t) : 
  {subset (frgnBlocksSrc mu) <= extBlocksSrc mu}.
Proof. 
move=> b; apply: frgnBlocksSrc_extBlocksSrc.
by apply: Inj_wd.
Qed.

Lemma frgntgt_sub_exttgt (mu : Inj.t) : 
  {subset (frgnBlocksTgt mu) <= extBlocksTgt mu}.
Proof. 
move=> b A; case: (Inj_wd mu)=> ? ? ? ? ? ? ?.
by move/(_ b A).
Qed.

Lemma extsrc_sub_domsrc (mu : Inj.t) : 
  {subset (extBlocksSrc mu) <= DomSrc mu}.
Proof. 
by move=> b; rewrite /DomSrc /in_mem /= => ->; apply/orP; right.
Qed.

Lemma exttgt_sub_domtgt (mu : Inj.t) : 
  {subset (extBlocksTgt mu) <= DomTgt mu}.
Proof. 
by move=> b; rewrite /DomTgt /in_mem /= => ->; apply/orP; right.
Qed.

Lemma frgnsrc_sub_domsrc (mu : Inj.t) : 
  {subset (frgnBlocksSrc mu) <= DomSrc mu}.
Proof. 
by move=> A; move/frgnsrc_sub_extsrc; apply: extsrc_sub_domsrc.
Qed.

Lemma frgntgt_sub_domtgt (mu : Inj.t) : 
  {subset (frgnBlocksTgt mu) <= DomTgt mu}.
Proof. 
by move=> A; move/frgntgt_sub_exttgt; apply: exttgt_sub_domtgt.
Qed.

Lemma frgnsrc_sub_sharedsrc (mu : Inj.t) : 
  {subset (frgnBlocksSrc mu) <= sharedSrc mu}.
Proof.
move=> a; rewrite /sharedSrc /shared_of /join /in_mem /=.
by move/(frgnSrc _ (Inj_wd _) _)=> []x []y []-> B.
Qed.

Lemma frgntgt_sub_sharedtgt (mu : Inj.t) : 
  {subset (frgnBlocksTgt mu) <= sharedTgt mu}.
Proof.
by move=> a; rewrite /sharedTgt /shared_of /join /in_mem /= => ->.
Qed.

Lemma frgnsrc_sub_exportedsrc (mu : Inj.t) vals : 
  {subset (frgnBlocksSrc mu) <= exportedSrc mu vals}.
Proof.
move=> a; rewrite /exportedSrc; move/frgnsrc_sub_sharedsrc.
by rewrite /in_mem /= => ->; apply/orP; right.
Qed.

Lemma frgntgt_sub_exportedtgt (mu : Inj.t) vals : 
  {subset (frgnBlocksTgt mu) <= exportedTgt mu vals}.
Proof.
move=> a; rewrite /exportedTgt; move/frgntgt_sub_sharedtgt.
by rewrite /in_mem /= => ->; apply/orP; right.
Qed.

Lemma sharedsrc_sub_domsrc (mu : Inj.t) :
  {subset (sharedSrc mu) <= DomSrc mu}.
Proof.
move=> a; rewrite /sharedSrc /in_mem /=.
case e: (_ a)=> //[[? ?]].
move: (shared_in_all _ (Inj_wd _) _ _ _ e)=> asinj.
by case: (as_inj_DomRng _ _ _ _ asinj (Inj_wd _)).
Qed.

Lemma sharedtgt_sub_domtgt (mu : Inj.t) :
  {subset (sharedTgt mu) <= DomTgt mu}.
Proof.
move=> a; rewrite /sharedTgt /in_mem /=.
rewrite /DomTgt; case/orP.
by move/frgntgt_sub_exttgt; rewrite /in_mem /= => ->; apply/orP; right.
by move/pubtgt_sub_loctgt; rewrite /in_mem /= => ->.
Qed.

Lemma smvalid_pubsrc_bound (mu : Inj.t) m :
  smvalid_src mu m -> 
  [pred b | pubBlocksSrc mu b]
  = [predI (pubBlocksSrc mu) & [pred b | validblock m b]].
Proof.
move=> A.
by rewrite -(predI_sub3 (sym_eq (smvalid_locsrc_bound A)) 
            (@pubsrc_sub_locsrc mu)).
Qed.

Lemma smvalid_pubtgt_bound (mu : Inj.t) m :
  smvalid_tgt mu m -> 
  [pred b | pubBlocksTgt mu b]
  = [predI (pubBlocksTgt mu) & [pred b | validblock m b]].
Proof.
move=> A.
by rewrite -(predI_sub3 (sym_eq (smvalid_loctgt_bound A)) 
            (@pubtgt_sub_loctgt mu)).
Qed.

Lemma smvalid_frgnsrc_bound (mu : Inj.t) m :
  smvalid_src mu m -> 
  [pred b | frgnBlocksSrc mu b]
  = [predI (frgnBlocksSrc mu) & [pred b | validblock m b]].
Proof.
move=> A.
by rewrite -(predI_sub3 (sym_eq (smvalid_extsrc_bound A)) 
            (@frgnsrc_sub_extsrc mu)).
Qed.

Lemma smvalid_frgntgt_bound (mu : Inj.t) m :
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

Lemma smvalid_src_fwd mu m m' : 
  mem_forward m m' -> 
  smvalid_src mu m -> smvalid_src mu m'.
Proof.
by move=> A B b C; move: {A B}(A b) (B b)=> A B; case: (A (B C)).
Qed.

Lemma smvalid_tgt_fwd mu m m' : 
  mem_forward m m' -> 
  smvalid_tgt mu m -> smvalid_tgt mu m'.
Proof.
by move=> A B b C; move: {A B}(A b) (B b)=> A B; case: (A (B C)).
Qed.

Lemma valid_block_fwd b m m' :
  Memory.Mem.valid_block m b -> 
  mem_forward m m' -> 
  Memory.Mem.valid_block m' b.
Proof. by move=> A; move/(_ b A); case. Qed.

Lemma sm_valid_fwd mu m1 m1' m2 m2' :
  sm_valid mu m1 m2 ->   
  mem_forward m1 m1' -> 
  mem_forward m2 m2' -> 
  sm_valid mu m1' m2'.
Proof.
move=> []A B C D; split=> b.
by move/(A _)=> E; apply: (valid_block_fwd E C).
by move/(B _)=> E; apply: (valid_block_fwd E D).
Qed.

Lemma intern_incr_frgnsrc mu mu' : 
  intern_incr mu mu' -> frgnBlocksSrc mu=frgnBlocksSrc mu'.
Proof. by case=> _ []_ []_ []_ []_ []_ []->. Qed.

Lemma intern_incr_frgntgt mu mu' : 
  intern_incr mu mu' -> frgnBlocksTgt mu=frgnBlocksTgt mu'.
Proof. by case=> _ []_ []_ []_ []_ []_ []_ []->. Qed.

Lemma intern_incr_extsrc mu mu' : 
  intern_incr mu mu' -> extBlocksSrc mu=extBlocksSrc mu'.
Proof. by case=> _ []_ []_ []_ []_ []_ []_ []_ []->. Qed.

Lemma intern_incr_exttgt mu mu' : 
  intern_incr mu mu' -> extBlocksTgt mu=extBlocksTgt mu'.
Proof. by case=> _ []_ []_ []_ []_ []_ []_ []_ []_ ->. Qed.

Lemma intern_incr_extern mu mu' : 
  intern_incr mu mu' -> extern_of mu=extern_of mu'.
Proof. by case=> _ []->. Qed.

(*Obsolete: see bellow sminj_alloc_locsrc*)
Lemma sminjsep_locsrc mu (mu' : Inj.t) m1 m2 :
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
by case: (Inj_wd mu'); move/(_ b); rewrite D G; case.
Qed.

(*Obsolete: see bellow sminj_alloc_loctgt*)
Lemma sminjsep_loctgt mu (mu' : Inj.t) m1 m2 :
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
by case: (Inj_wd mu')=> _; move/(_ b); rewrite D G; case.
Qed.

Lemma localloc_locS:
  forall mu mu' m10 m20 m1 m2,
    sm_locally_allocated mu mu' m10 m20 m1 m2 ->
    {subset [predD locBlocksSrc mu' & locBlocksSrc mu] <= [pred b | freshloc m10 m1 b]}.
  rewrite /sm_locally_allocated.
  case => locS locT ? ? ? ? ? ? ? ?;
  case => locS' locT' ? ? ? ? ? ? ? ? /=.
  move => m10 m20 m1 m2.                    
  case => locSH [locTH ext]. 
  rewrite locSH /sub_mem /predD /in_mem /mem /in_mem /=.
  rewrite /in_mem => x /=.
  case (locS x) => //=.
Qed.

Lemma localloc_locT:
  forall mu mu' m10 m20 m1 m2,
    sm_locally_allocated mu mu' m10 m20 m1 m2 ->
    {subset [predD locBlocksTgt mu' & locBlocksTgt mu] <= [pred b | freshloc m20 m2 b]}.
  rewrite /sm_locally_allocated.
  case => locS locT ? ? ? ? ? ? ? ?;
  case => locS' locT' ? ? ? ? ? ? ? ? /=.
  move => m10 m20 m1 m2.                    
  case => locSH [locTH ext]. 
  rewrite locTH /sub_mem /predD /in_mem /mem /in_mem /=.
  rewrite /in_mem => x /=.
  case (locT x) => //=.
Qed. 

Lemma sminj_alloc_locsrc:
  forall (mu : SM_Injection) (mu' : Inj.t) (m10 m20 m1 m2 : Memory.mem),
    intern_incr mu mu' ->
    (*sm_valid mu m10 m20 ->*)
    sm_locally_allocated mu mu' m10 m20 m1 m2 ->
       {subset [predD locBlocksSrc mu' & locBlocksSrc mu]
            <= [pred b | ~~ validblock m10 b]}.
  intros ? ? ? ? ? ? incr (*VAL*) loca.
  eapply (subset_trans' (localloc_locS loca)).
  unfold freshloc.
  move=> b.
  case/andP=> //= =>H.
  case (valid_block_dec m10 b)=>//=.
  rewrite /in_mem => /=.
  rewrite /validblock /Mem.valid_block /Plt;
    move=> HH ?.
    by apply/negP/Pos.ltb_lt=>//.
Qed.  

Lemma sminj_alloc_loctgt:
  forall (mu : SM_Injection) (mu' : Inj.t) (m10 m20 m1 m2 : Memory.mem),
    intern_incr mu mu' ->
    (*sm_valid mu m10 m20 ->*)
    sm_locally_allocated mu mu' m10 m20 m1 m2 ->
       {subset [predD locBlocksTgt mu' & locBlocksTgt mu]
            <= [pred b | ~~ validblock m20 b]}.
  intros ? ? ? ? ? ? incr (*VAL*) loca. 
  eapply (subset_trans' (localloc_locT loca)).
  unfold freshloc.
  move=> b.
  case/andP=> //= =>H.
  case (valid_block_dec m20 b)=>//=.
  rewrite /in_mem => /=.
  rewrite /validblock /Mem.valid_block /Plt;
    move=> HH ?.
    by apply/negP/Pos.ltb_lt=>//.
Qed.  

Lemma sm_inject_separated_refl mu m m' : sm_inject_separated mu mu m m'.
Proof.
split; first by move=> ? ? ? ->; discriminate.
split; first by move=> ? ->; discriminate.
by move=> ? ->; discriminate.
Qed.

Lemma sm_inject_separated_replace_locals mu X Y mu' m1 m2 : 
  sm_inject_separated mu mu' m1 m2 -> 
  sm_inject_separated (replace_locals mu X Y) mu' m1 m2.
Proof.
case.
rewrite /sm_inject_separated.
rewrite replace_locals_DomSrc.
rewrite replace_locals_DomTgt.
rewrite replace_locals_as_inj.
by [].
Qed.

Lemma vis_sub_DomSrc (mu0 : Inj.t) : {subset vis mu0 <= DomSrc mu0}.
Proof.
move=> b; case/orP; rewrite /DomSrc.
by rewrite /in_mem /= => ->.
by move/frgnsrc_sub_extsrc=> H; apply/orP; right.
Qed.
