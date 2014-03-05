Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Bool.
Require Import Zbool.
Require Import BinPos. 

Require Import compcert.common.Globalenvs.

Require Import msl.Axioms.

Require Import sepcomp.StructuredInjections.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.reach.
Require Import sepcomp.effect_simulations.

Require Import linking.pred_lemmas.
Require Import linking.seq_lemmas.

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
move=> b; apply: StructuredInjections.pubBlocksLocalSrc.
by apply: Inj_wd.
Qed.

Lemma pubtgt_sub_loctgt (mu : Inj.t) : 
  {subset (pubBlocksTgt mu) <= locBlocksTgt mu}.
Proof. 
move=> b; apply: StructuredInjections.pubBlocksLocalTgt.
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

Lemma sm_inject_separated_refl mu m m' : sm_inject_separated mu mu m m'.
Proof.
split; first by move=> ? ? ? ->; discriminate.
split; first by move=> ? ->; discriminate.
by move=> ? ->; discriminate.
Qed.

(* The following variation of [join] is appropriate for shared resources  *)
(* like extern injections: each core must have a consistent mapping on    *)
(* extern blocks but the domains of the mappings are not necessarily      *)
(* disjoint.                                                              *)

Definition join2 (j  k : Values.meminj) b :=
  match j b with
    | Some (b1,d1) => 
      match k b with
        | Some (b2,d2) => 
            if [&& Pos.eqb b1 b2 & Zeq_bool d1 d2]
            then Some (b1,d1) else None
        | None => None
      end
    | None => None
  end.

Lemma join2P j k b1 b2 d2 :
  join2 j k b1 = Some (b2,d2) <->
  [/\ j b1 = Some (b2,d2) & k b1 = Some (b2,d2)].
Proof.
rewrite/join2; split.
case A: (j b1)=> // [[x y]]; case B: (k b1)=> // [[x' y']].
case H: (_ && _)=> //; move: H; move/andP=> []. 
by move/Peqb_true_eq=> <-; move/Zeq_bool_eq=> <-; case=> -> ->.
move=> []-> ->; case H: (_ && _)=> //; move: H; move/andP=> []; split.
by rewrite/is_true Pos.eqb_eq.
by rewrite/is_true -Zeq_is_eq_bool.
Qed.

(* [join_sm mu1 mu2] is a union operator on structured injections. If     *)
(* we have struct. injections                                             *)
(*                                                                        *)
(*   mu1 = LOC1, locof1, EXT1, extof1                                     *)
(*   mu2 = LOC2, locof2, EXT2, extof2                                     *)
(*                                                                        *)
(* then [join_sm mu1 mu2 = mu12] is equal to                              *)
(*                                                                        *)
(*   LOC1 \cup LOC2, join locof1 locof2,                                  *)
(*   EXT1 \cap EXT2, join2 extof1 extof2                                  *)
(*                                                                        *)
(* w/ PUB12 = \emptyset, FRGN12 = FRGN1 \cap FRGN2.                       *)
(*                                                                        *)
(* While conceptually, LOC1 \cup LOC2 is disjoint union, in practice we   *)
(* make [join_sm] a total operation.  However, [mu12] is only             *)
(* well-defined if                                                        *)
(*                                                                        *)
(*   1) LOC1 \cap \LOC2 = \emptyset; and                                  *)
(*   2) extof1 and extof2 are "consistent"                                *)
(*                                                                        *)
(* We say that two injections [j],[k] are consistent when the following   *)
(* condition holds:                                                       *)

Definition consistent (j k : Values.meminj) := 
  forall b1 b2 b2' d2 d2', 
  j b1 = Some (b2,d2) -> k b1 = Some (b2',d2') -> [/\ b2=b2' & d2=d2'].

Definition DisjointLS := 
  [fun mu mu' => Disjoint (locBlocksSrc mu) (locBlocksSrc mu')].

Definition DisjointLT := 
  [fun mu mu' => Disjoint (locBlocksTgt mu) (locBlocksTgt mu')].

Definition Consistent := 
  [fun mu mu' => consistent (extern_of mu) (extern_of mu')].

Definition join_sm mu1 mu2 : SM_Injection :=
  Build_SM_Injection 
    [predU (locBlocksSrc mu1) & locBlocksSrc mu2]
    [predU (locBlocksTgt mu1) & locBlocksTgt mu2]
    pred0
    pred0
    (join (local_of mu1) (local_of mu2))
    [predI (extBlocksSrc mu1) & extBlocksSrc mu2]
    [predI (extBlocksTgt mu1) & extBlocksTgt mu2]
    [predI (frgnBlocksSrc mu1) & frgnBlocksSrc mu2]
    [predI (frgnBlocksTgt mu1) & frgnBlocksTgt mu2]
    (join2 (extern_of mu1) (extern_of mu2)).

Lemma join_sm_wd (mu1 : Inj.t) (mu2 : Inj.t) :
  DisjointLS mu1 mu2 -> 
  DisjointLT mu1 mu2 -> 
  Consistent mu1 mu2 -> 
  SM_wd (join_sm mu1 mu2).
Proof.
move=> D1 D2 C12; apply: Build_SM_wd; rewrite/join_sm/=/in_mem/=/in_mem/=.
move=> b; move: (Inj_DisjointLES mu1); move/DisjointP/(_ b).
move: (Inj_DisjointLES mu2); move/DisjointP/(_ b). 
by case: (locBlocksSrc mu1 b); case: (locBlocksSrc mu2 b);
   case: (extBlocksSrc mu1 b); case: (extBlocksSrc mu2 b)=>//=;
   solve[by left|by right|by case|by move=> _; case].
move=> b; move: (Inj_DisjointLET mu1); move/DisjointP/(_ b).
move: (Inj_DisjointLET mu2); move/DisjointP/(_ b). 
rewrite/join_sm/=/in_mem/=/in_mem/=.
by case: (locBlocksTgt mu1 b); case: (locBlocksTgt mu2 b);
   case: (extBlocksTgt mu1 b); case: (extBlocksTgt mu2 b)=>//=;
   solve[by left|by right|by case|by move=> _; case].
rewrite/join=> b1 b2 z.
case H: (local_of _ _)=> [[? ?]|]=> A; move: A H. case=> -> ->.
by move/local_DomRng; move/(_ (Inj_wd mu1))=> []-> ->.
move/local_DomRng; move/(_ (Inj_wd mu2))=> []-> -> _.
by split; apply/orP; right.
move=> b1 b2 z; move/join2P=> [].
move/(extern_DomRng _ (Inj_wd mu1))=> []-> -> /=.
by move/(extern_DomRng _ (Inj_wd mu2))=> []-> -> /=.
by [].
move=> b1; move/andP=> []; rewrite/join2.
move=> A B.
move: (frgnSrcAx _ (Inj_wd _) _ A)=> []b2 []d2 []A0 A'.
move: (frgnSrcAx _ (Inj_wd _) _ B)=> []b2' []d2' []B0 B'.
exists b2,d2; move: A' B'; rewrite A0 B0; case H: (_ && _).
by move: H; move/andP=> []; move/Peqb_true_eq=> <- _ -> ->.
move: (C12 _ _ _ _ _ A0 B0) H; case=> <- <-; move/andP=> []; split.
by rewrite/is_true Pos.eqb_eq.
by rewrite/is_true -Zeq_is_eq_bool.
by [].
move=> b; move/andP=> []. 
move/frgntgt_sub_exttgt; rewrite/in_mem/= => ->.
by move/frgntgt_sub_exttgt; rewrite/in_mem/= => ->.
Qed.

(* The following definitions/lemmas extend [join2] to nonempty sequences  *)
(* of struct. injections.                                                 *)

Definition AllDisjoint (proj : SM_Injection -> Values.block -> bool) := 
  All2 (fun mu mu' => Disjoint (proj mu) (proj mu')).

Definition AllConsistent := 
  All2 (fun mu mu' => consistent (extern_of mu) (extern_of mu')).

Fixpoint join_all (mu0 : Inj.t) (mus : seq Inj.t) : SM_Injection :=
  if mus is [:: mu & mus] then join_sm mu (join_all mu0 mus)
  else mu0.

Lemma join_all_cons mu0 mu mus : 
  join_all mu0 (mu :: mus) = join_sm mu (join_all mu0 mus).
Proof. by []. Qed.

Lemma join_all_disjoint_src mu0 (mu : Inj.t) mus :
  All (fun mu' => Disjoint (locBlocksSrc mu0) (locBlocksSrc mu')) 
    (map Inj.mu (mu :: mus)) -> 
  Disjoint (locBlocksSrc mu0) (locBlocksSrc (join_all mu mus)).
Proof.
elim: mus=> //=; first by move=> [].
by move=> mu' mus' IH []A []B C; move: (IH (conj A C))=> D; apply: DisjointInU.
Qed.

Lemma join_all_disjoint_tgt mu0 (mu : Inj.t) mus :
  All (fun mu' => Disjoint (locBlocksTgt mu0) (locBlocksTgt mu'))  
    (map Inj.mu (mu :: mus)) -> 
  Disjoint (locBlocksTgt mu0) (locBlocksTgt (join_all mu mus)).
Proof.
elim: mus=> //=; first by move=> [].
by move=> mu' mus' IH []A []B C; move: (IH (conj A C))=> D; apply: DisjointInU.
Qed.

Lemma join2_consistent j k k' :
  consistent j k -> 
  consistent j k' ->
  consistent j (join2 k k').
Proof.
rewrite/consistent=> A B b1 b2 b2' d2 d2' C.
by move/join2P=> []D E; case: (A _ _ _ _ _ C D).
Qed.

Lemma join_all_consistent mu0 (mu : Inj.t) mus :
  All (fun mu' => consistent (extern_of mu0) (extern_of mu'))  
    (map Inj.mu (mu :: mus)) -> 
  consistent (extern_of mu0) (extern_of (join_all mu mus)).
Proof.
elim: mus=> //=; first by move=> [].
by move=> mu' mus' IH []A []B C; move: (IH (conj A C))=> D; 
   apply: join2_consistent.
Qed.

(* Why is this lemma not in ZArith?!? *)

Lemma Zeq_bool_refl x : Zeq_bool x x.
Proof. by case: (Zeq_is_eq_bool x x)=> A _; apply: A. Qed.

Lemma join2P' (j k : SM_Injection) b1 :                                
  Consistent j k ->                                                    
  (join2 (extern_of j) (extern_of k) b1 = None <->                     
   [\/ extern_of j b1 = None | extern_of k b1 = None]).                
Proof.                                                                 
rewrite /=/consistent=> C.                                             
rewrite/join2; split.                                                  
case A: (extern_of j b1)=> // [[? ?]|].                                
case B: (extern_of k b1)=> // [[? ?]|].                                
case: (C _ _ _ _ _ A B)=> -> ->.                                       
by rewrite Pos.eqb_refl Zeq_bool_refl /=.
by right.                                                              
by left.                                                               
case=> ->; first by [].                             
by case: (extern_of j b1)=> // [[? ?]].                                
Qed.                                                                   

Lemma Disjoint_locSrcC mu mu' : DisjointLS mu mu' -> DisjointLS mu' mu.
Proof. by rewrite /= DisjointC. Qed.

Lemma Disjoint_locTgtC mu mu' : DisjointLT mu mu' -> DisjointLT mu' mu.
Proof. by rewrite /= DisjointC. Qed.

Lemma consistentC mu mu' : Consistent mu mu' -> Consistent mu' mu.
Proof. 
rewrite /= /consistent=> A b1 b2 b2' d2 d2' B C.
by case: (A _ _ _ _ _ C B)=> -> ->.
Qed.

Lemma join_all_wd mu (mus : seq Inj.t) :
  AllDisjoint locBlocksSrc $ map Inj.mu (mu :: mus) -> 
  AllDisjoint locBlocksTgt $ map Inj.mu (mu :: mus) -> 
  AllConsistent $ map Inj.mu (mu :: mus) -> 
  SM_wd (join_all mu mus).
Proof.
elim: mus=> /=; first by move=> _ _ _; apply: (Inj_wd mu).
move=> mu0 mus IH A B C.
move: {A B C} 
  (All2C A Disjoint_locSrcC) (All2C B Disjoint_locTgtC)
  (All2C C consistentC).
move/All2_cons=> []A B. 
move/All2_cons=> []C D.
move/All2_cons=> []E F.
have wd: SM_wd (join_all mu mus) by apply IH.
change (SM_wd (join_sm mu0 (Inj.mk wd))).
apply: join_sm_wd=> /=.
by apply: join_all_disjoint_src.
by apply: join_all_disjoint_tgt.
by apply: join_all_consistent.
Qed.

Lemma join_sm_frgn (mu1 mu2 : Inj.t) b : 
  frgnBlocksSrc mu1 b -> 
  frgnBlocksSrc mu2 b -> 
  frgnBlocksSrc (join_sm mu1 mu2) b.
Proof. by rewrite/join_sm/= => A B; apply/andP; split. Qed.

Definition assimilated mu0 mu := join_sm mu0 mu = mu.

Lemma assimilated_sub_locSrc mu0 mu :
  assimilated mu0 mu -> {subset (locBlocksSrc mu0) <= locBlocksSrc mu}. 
Proof. by rewrite/assimilated/join_sm=> <- b /= => A; apply/orP; left. Qed.

Lemma assimilated_sub_locTgt mu0 mu :
  assimilated mu0 mu -> {subset (locBlocksTgt mu0) <= locBlocksTgt mu}. 
Proof. by rewrite/assimilated/join_sm=> <- b /= => A; apply/orP; left. Qed.

Lemma assimilated_sub_extSrc mu0 mu :
  assimilated mu0 mu -> {subset (locBlocksSrc mu0) <= locBlocksSrc mu}. 
Proof. by rewrite/assimilated/join_sm=> <- b /= => A; apply/orP; left. Qed.

Lemma join_sm_extSrc mu1 mu2 : 
  extBlocksSrc (join_sm mu1 mu2) 
  = [predI (extBlocksSrc mu1) & extBlocksSrc mu2].
Proof. by []. Qed.

Lemma join_sm_extTgt mu1 mu2 : 
  extBlocksTgt (join_sm mu1 mu2) 
  = [predI (extBlocksTgt mu1) & extBlocksTgt mu2].
Proof. by []. Qed.

Lemma join_sm_frgnSrc mu1 mu2 : 
  frgnBlocksSrc (join_sm mu1 mu2) 
  = [predI (frgnBlocksSrc mu1) & frgnBlocksSrc mu2].
Proof. by []. Qed.

Lemma join_sm_frgnTgt mu1 mu2 : 
  frgnBlocksTgt (join_sm mu1 mu2) 
  = [predI (frgnBlocksTgt mu1) & frgnBlocksTgt mu2].
Proof. by []. Qed.

Lemma join_sm_preserves_globals F V (ge : Genv.t F V) (mu1 mu2 : Inj.t) : 
  Events.meminj_preserves_globals ge (extern_of mu1) -> 
  Events.meminj_preserves_globals ge (extern_of mu2) -> 
  Events.meminj_preserves_globals ge (extern_of (join_sm mu1 mu2)).
Proof.
move=> []A []B C []D []E G; rewrite /join_sm /= /join2; split.
+ move=> id b H. 
  rewrite (A _ _ H) (D _ _ H).
  by case: (@andP _ _)=> // [][]; rewrite /is_true Pos.eqb_eq -Zeq_is_eq_bool.
split. 
+ move=> b gv H; rewrite (B _ _ H) (E _ _ H).
  by case: (@andP _ _)=> // [][]; rewrite /is_true Pos.eqb_eq -Zeq_is_eq_bool.
+ move=> b1 b2 d gv H.
  case H1: (extern_of _ _)=> // [[? ?]]; case H2: (extern_of _ _)=> // [[? ?]].  
  case: (@andP _ _)=> //; case. 
  rewrite /is_true Pos.eqb_eq -Zeq_is_eq_bool=> X Y; case=> Z W.
  by move: X Y Z W H1 H2=> -> -> -> -> //; move/(C _ _ _ _ H)=> <-.
Qed.

Lemma join_sm_isGlob F V (ge : Genv.t F V) (mu1 mu2 : Inj.t) :
 (forall b, isGlobalBlock ge b -> frgnBlocksSrc mu1 b) -> 
 (forall b, isGlobalBlock ge b -> frgnBlocksSrc mu2 b) -> 
 forall b, isGlobalBlock ge b -> frgnBlocksSrc (join_sm mu1 mu2) b.
Proof.
rewrite/join_sm /= => A B b C; move: (A _ C) (B _ C)=> ? ?.
by apply/andP; split.
Qed.

Lemma join_all_id mu : join_all mu [::] = mu.
Proof. by []. Qed.

Lemma join_all_preserves_globals 
      F V (ge : Genv.t F V) (mu : Inj.t) (mus : seq Inj.t) : 
  Events.meminj_preserves_globals ge (extern_of mu) ->
  (AllDisjoint locBlocksSrc \o map Inj.mu) (mu :: mus) -> 
  (AllDisjoint locBlocksTgt \o map Inj.mu) (mu :: mus) -> 
  (AllConsistent \o map Inj.mu) (mu :: mus) -> 
  All (Events.meminj_preserves_globals ge \o extern_of \o Inj.mu) mus -> 
  Events.meminj_preserves_globals ge (extern_of (join_all mu mus)).
Proof.
elim: mus=> //= mu' mus' IH PRES A B C. 
move: {A B C} 
  (All2C A Disjoint_locSrcC) (All2C B Disjoint_locTgtC)
  (All2C C consistentC).
move/All2_cons=> []B C.
move/All2_cons=> []D E.
move/All2_cons=> []G H.
have wd: SM_wd (join_all mu mus') by apply: join_all_wd.
move=> []I J.
change (Events.meminj_preserves_globals ge 
  (extern_of (join_sm mu' (Inj.mk wd)))).
apply: join_sm_preserves_globals=> //.
by apply: IH.
Qed.

Lemma join_all_isGlob F V (ge : Genv.t F V) (mu : Inj.t) (mus : seq Inj.t) :
 (forall b, isGlobalBlock ge b -> frgnBlocksSrc mu b) -> 
 All (fun mu => forall b, isGlobalBlock ge b -> frgnBlocksSrc mu b) 
     (map Inj.mu mus) -> 
 forall b, isGlobalBlock ge b -> frgnBlocksSrc (join_all mu mus) b.
Proof.
elim: mus mu=> // mu' mus' IH mu A /= []B C b D; apply/andP; split=> //.
by apply: (B _ D).
by apply: IH.
Qed.

Lemma join_sm_valid mu1 mu2 m1 m2 :
  sm_valid mu1 m1 m2 -> 
  sm_valid mu2 m1 m2 -> 
  sm_valid (join_sm mu1 mu2) m1 m2.
Proof.
rewrite/join_sm/sm_valid/DOM/RNG/DomSrc/DomTgt /= => [][]A B []C D; split.
move=> b1; move/orP; case.
move/orP; case=> E.
by apply: A; apply/orP; left.
by apply: C; apply/orP; left.
move/andP=> []E F.
by apply: A; apply/orP; right.
move=> b2; move/orP; case.
move/orP; case=> E.
by apply: B; apply/orP; left.
by apply: D; apply/orP; left.
move/andP=> []E F.
by apply: D; apply/orP; right.
Qed.

Lemma join_smvalid_src mu1 mu2 m1 :
  smvalid_src mu1 m1 ->
  smvalid_src mu2 m1 ->
  smvalid_src (join_sm mu1 mu2) m1.
Proof.
rewrite/join_sm/smvalid_src/DOM/RNG/DomSrc/DomTgt /= => []A B.
move=> b1; move/orP; case.
move/orP; case=> E.
by apply: A; apply/orP; left.
by apply: B; apply/orP; left.
move/andP=> []E F.
by apply: A; apply/orP; right.
Qed.

Lemma join_all_valid (mu : Inj.t) mus m1 m2 :
  sm_valid mu m1 m2 -> 
  All (fun mu0 => sm_valid (Inj.mu mu0) m1 m2) mus -> 
  sm_valid (join_all mu mus) m1 m2.
Proof.
move: mu m1 m2; elim: mus=> // mu' mus' IH mu m1 m2 A /= []B C.
by apply: join_sm_valid=> //; apply: IH.
Qed.

Lemma join_all_valid_src (mu : Inj.t) mus m1 :
  smvalid_src mu m1 ->
  All (fun mu0 => smvalid_src (Inj.mu mu0) m1) mus -> 
  smvalid_src (join_all mu mus) m1.
Proof.
move: mu m1; elim: mus=> // mu' mus' IH mu m1 A /= []B C.
by apply: join_smvalid_src=> //; apply: IH.
Qed.

Lemma DisjointLS_restrict mu1 mu2 X Y : 
  DisjointLS mu1 mu2 -> 
  DisjointLS (restrict_sm mu1 X) (restrict_sm mu2 Y).
Proof. by case: mu1; case: mu2. Qed.

Lemma DisjointLT_restrict mu1 mu2 X Y : 
  DisjointLT mu1 mu2 -> 
  DisjointLT (restrict_sm mu1 X) (restrict_sm mu2 Y).
Proof. by case: mu1; case: mu2. Qed.

Lemma DisjointLS_E1 mu1 mu2 b : 
  DisjointLS mu1 mu2 -> 
  locBlocksSrc mu1 b -> 
  locBlocksSrc mu2 b=false.
Proof.
move/DisjointP; move/(_ b); case; first by contradiction.
by case: (locBlocksSrc mu2 b).
Qed.

Lemma DisjointLS_E2 mu1 mu2 b : 
  DisjointLS mu1 mu2 -> 
  locBlocksSrc mu2 b -> 
  locBlocksSrc mu1 b=false.
Proof.
move/DisjointP; move/(_ b); case; first by case: (locBlocksSrc mu1 b).
by contradiction.
Qed.

Lemma DisjointLT_E1 mu1 mu2 b : 
  DisjointLT mu1 mu2 -> 
  locBlocksTgt mu1 b -> 
  locBlocksTgt mu2 b=false.
Proof.
move/DisjointP; move/(_ b); case; first by contradiction.
by case: (locBlocksTgt mu2 b).
Qed.

Lemma DisjointLT_E2 mu1 mu2 b : 
  DisjointLT mu1 mu2 -> 
  locBlocksTgt mu2 b -> 
  locBlocksTgt mu1 b=false.
Proof.
move/DisjointP; move/(_ b); case; first by case: (locBlocksTgt mu1 b).
by contradiction.
Qed.

Lemma DisjointLS_incr mu1 mu1' mu2 m1 m2 m1' m2' : 
  DisjointLS mu1 mu2 -> 
  intern_incr mu1 mu1' -> 
  sm_inject_separated mu1 mu1' m1 m2 -> 
  sm_locally_allocated mu1 mu1' m1 m2 m1' m2' -> 
  sm_valid mu2 m1 m2 -> 
  DisjointLS mu1' mu2.
Proof.
move/DisjointP=> A B C D E /=; rewrite DisjointP=> b; move: (A b).
case=> // F. 
case G: (locBlocksSrc mu2 b); last by right. left=> H.
have F': locBlocksSrc mu1 b = false by move: F; case: (locBlocksSrc mu1 b).
case: (sm_inject_separated_intern_MYB _ _ _ _ _ _ C D); move/(_ b F' H)=> I _.
by case: E; move/(_ b); rewrite/DOM/DomSrc G=> J _; apply: I; apply: J.
by right.
Qed.

Lemma DisjointLT_incr mu1 mu1' mu2 m1 m2 m1' m2' : 
  DisjointLT mu1 mu2 -> 
  intern_incr mu1 mu1' -> 
  sm_inject_separated mu1 mu1' m1 m2 -> 
  sm_locally_allocated mu1 mu1' m1 m2 m1' m2' -> 
  sm_valid mu2 m1 m2 -> 
  DisjointLT mu1' mu2.
Proof.
move/DisjointP=> A B C D E /=; rewrite DisjointP=> b; move: (A b).
case=> // F. 
case G: (locBlocksTgt mu2 b); last by right. left=> H.
have F': locBlocksTgt mu1 b = false by move: F; case: (locBlocksTgt mu1 b).
case: (sm_inject_separated_intern_MYB _ _ _ _ _ _ C D)=> _; move/(_ b F' H)=> I.
by case: E=> _; move/(_ b); rewrite/RNG/DomTgt G => J; apply: I; apply: J.
by right.
Qed.

Lemma AllDisjointLS_incr mu1 mu1' mus m1 m2 m1' m2' : 
  All (fun mu0 => DisjointLS mu1 mu0) mus -> 
  intern_incr mu1 mu1' -> 
  sm_inject_separated mu1 mu1' m1 m2 -> 
  sm_locally_allocated mu1 mu1' m1 m2 m1' m2' -> 
  All (fun mu0 => sm_valid mu0 m1 m2) mus -> 
  All (fun mu0 => DisjointLS mu1' mu0) mus.
Proof.
elim: mus=> // mu0 mus' IH /= []A B C D E []F G.
split; first by apply: (DisjointLS_incr A C D E F).
by apply: IH.
Qed.

Lemma AllDisjointLT_incr mu1 mu1' mus m1 m2 m1' m2' : 
  All (fun mu0 => DisjointLT mu1 mu0) mus -> 
  intern_incr mu1 mu1' -> 
  sm_inject_separated mu1 mu1' m1 m2 -> 
  sm_locally_allocated mu1 mu1' m1 m2 m1' m2' -> 
  All (fun mu0 => sm_valid mu0 m1 m2) mus -> 
  All (fun mu0 => DisjointLT mu1' mu0) mus.
Proof.
elim: mus=> // mu0 mus' IH /= []A B C D E []F G.
split; first by apply: (DisjointLT_incr A C D E F).
by apply: IH.
Qed.

Lemma vis_join_sm mu1 mu2 :
  vis (join_sm mu1 mu2) 
  = [predU [predU (locBlocksSrc mu1) & locBlocksSrc mu2]
         & [predI (frgnBlocksSrc mu1) & frgnBlocksSrc mu2]].
Proof. 
by rewrite/vis/join_sm/=; extensionality b=> /=; rewrite/predU. 
Qed.

Lemma locBlocksSrc_vis mu : {subset (locBlocksSrc mu) <= vis mu}.
Proof. by rewrite/vis=> b; rewrite/in_mem/= => A; apply/orP; left. Qed.

Lemma frgnBlocksSrc_vis mu : {subset (frgnBlocksSrc mu) <= vis mu}.
Proof. by rewrite/vis=> b; rewrite/in_mem/= => A; apply/orP; right. Qed.

Lemma join_sm_incr mu1 mu1' mu2 mu2' : 
  disjoint (local_of mu1') (local_of mu2') -> 
  intern_incr mu1 mu1' -> 
  intern_incr mu2 mu2' -> 
  intern_incr (join_sm mu1 mu2) (join_sm mu1' mu2').
Proof.
rewrite/intern_incr/join_sm/= => disj. 
move=> []incr1 []<- []A []B []? []? []<- []<- []<- <-.
move=> []incr2 []<- []C []D []? []? []<- []<- []<- <-. 
split=> //. 
apply: inject_incr_join=> //.
split=> //.
split=> //. 
move=> b; move/orP; case=> H.
by rewrite/in_mem/= (A _ H).
by rewrite/in_mem/= (C _ H); apply/orP; right.
split=> //. 
move=> b; move/orP; case=> H.
by rewrite/in_mem/= (B _ H).
by rewrite/in_mem/= (D _ H); apply/orP; right.
Qed.

Lemma join_all_incr (mu_trash mu mu' : Inj.t) (mus : seq Inj.t) : 
  disjoint (local_of mu') (local_of (join_all mu_trash mus)) ->
  intern_incr mu mu' -> 
  intern_incr (join_all mu_trash (mu :: mus)) 
              (join_all mu_trash (mu':: mus)).
Proof. by move=> /= A B; apply: join_sm_incr. Qed.

Lemma joinP j k b1 b2 d :
  join j k b1 = Some (b2,d) <->
  j b1 = Some (b2,d) \/ (j b1 = None /\ k b1 = Some (b2,d)).
Proof.
rewrite/join; split.
case: (j b1)=> // [[? ?]|->]; first by case=> -> ->; left.
by right. case=> A; first by rewrite A.
by case: A=> ->.
Qed.

Lemma joinP' j k b1 :
  join j k b1 = None <-> j b1 = None /\ k b1 = None.
Proof.
rewrite/join; split; first by case: (j b1)=> //; first by case.
by move=> []-> ->.
Qed.
                                                                      
Lemma as_injE mu b1 b2 d :
  as_inj mu b1 = Some (b2,d) -> 
  [\/ local_of mu b1 = Some (b2,d) | extern_of mu b1 = Some (b2,d)].
Proof.
rewrite/as_inj/join; case: (extern_of mu b1)=> // [[? ?]|].
by case=> -> ->; right.
by left.
Qed.

Lemma as_injE' mu b1 :
  as_inj mu b1 = None -> 
  [/\ local_of mu b1 = None & extern_of mu b1 = None].
Proof.
rewrite/as_inj/join; case: (extern_of mu b1)=> // [[? ?]].
by discriminate.
Qed.

Lemma local_of_join_smE mu1 mu2 b1 b2 d : 
  local_of (join_sm mu1 mu2) b1 = Some (b2,d) -> 
  [\/ local_of mu1 b1 = Some (b2,d) 
    | [/\ local_of mu1 b1 = None & local_of mu2 b1 = Some (b2,d)]].
Proof. by rewrite/join_sm/=; move/joinP. Qed.

Lemma local_of_join_smE' mu1 mu2 b1 :
  local_of (join_sm mu1 mu2) b1 = None -> 
  [/\ local_of mu1 b1 = None & local_of mu2 b1 = None].
Proof. by rewrite/join_sm/=; move/joinP'. Qed.

Lemma extern_of_join_smE mu1 mu2 b1 b2 d : 
  extern_of (join_sm mu1 mu2) b1 = Some (b2,d) -> 
  [/\ extern_of mu1 b1 = Some (b2,d) 
    & extern_of mu2 b1 = Some (b2,d)].
Proof. by rewrite/join_sm/=; move/join2P. Qed.

Lemma extern_of_join_smE' mu1 mu2 b1 :                                 
  Consistent mu1 mu2 ->                                                
  extern_of (join_sm mu1 mu2) b1 = None ->                             
  [\/ extern_of mu1 b1 = None                                          
    | extern_of mu2 b1 = None].                                        
Proof. by rewrite/join_sm/=; move/(join2P' b1)=> ->. Qed.              

Lemma join2_restrict j k X :
  join2 (restrict j X) (restrict k X) = restrict (join2 j k) X.
Proof.
extensionality b.
case A: (join2 _ _ b)=> [[b' ofs]|].
move: A; move/join2P=> []. 
move/restrictD_Some=> []A B; move/restrictD_Some=> []C _.
by rewrite/join2/restrict B A C Pos.eqb_refl Zeq_bool_refl.
move: A; rewrite/join2.
case A: (restrict j X b)=> [[b' ofs]|].
case B: (restrict k X b)=> [[b'' ofs']|].
case C: (Pos.eqb b' b'') A B.
case D: (Zeq_bool ofs ofs')=> //=.
by rewrite/restrict; case E: (X b)=> //; move=> -> ->; rewrite C D.
by rewrite/restrict; case E: (X b)=> //; move=> -> ->; rewrite C.
move: A; move/restrictD_Some=> []C D; rewrite/restrict D C.
move: B; move/restrictD_None; case: (k b)=> // [[b'' ofs']]. 
by move/(_ b'' ofs' erefl); move: D=> ->.
rewrite/restrict; case B: (j b)=> // [[b' ofs]|].
by move: A; move/restrictD_None; move/(_ b' ofs B)=> ->.
by case: (X b).
Qed.

Lemma join_sm_restrict mu1 mu2 X :
  restrict_sm (join_sm mu1 mu2) X 
  = join_sm (restrict_sm mu1 X) (restrict_sm mu2 X).
Proof.
rewrite/join_sm/=; f_equal.
by rewrite !restrict_sm_locBlocksSrc.
by rewrite !restrict_sm_locBlocksTgt.
by rewrite -!join_restrict !restrict_sm_local.
by rewrite !restrict_sm_extBlocksSrc.
by rewrite !restrict_sm_extBlocksTgt.
by rewrite !restrict_sm_frgnBlocksSrc.
by rewrite !restrict_sm_frgnBlocksTgt.
by rewrite -!join2_restrict !restrict_sm_extern.
Qed.

Lemma disjoint_restrict j k X : 
  disjoint j k -> 
  disjoint (restrict j X) (restrict k X).
Proof. by rewrite/disjoint/restrict=> A b; case: (X b)=> //; left. Qed.

Lemma restrict_incr' j j' X X' :
  {subset X <= X'} -> 
  Values.inject_incr j j' -> 
  Values.inject_incr (restrict j X) (restrict j' X').
Proof.
move=> A; rewrite/Values.inject_incr=> B b b' ofs.
move/restrictD_Some=> []C; move/A; rewrite/in_mem/= => D.
by rewrite/restrict D; apply: (B _ _ _ C).
Qed.

Lemma restrict_disj j X X' :
  {subset X <= X'} -> 
  (forall b b' ofs, j b = Some (b',ofs) -> ~~ [predD X' & X] b) -> 
  restrict j X = restrict j X'.
Proof.
move=> A B; rewrite/restrict; extensionality b.
case C: (X b); first by move: (A b C); rewrite/in_mem/= => ->.
case D: (X' b)=> //.
case E: (j b)=> // [[b' ofs]].
move: (B _ _ _ E).
rewrite notin_predD; move/orP; case.
by rewrite/in_mem/= D.
by rewrite/in_mem/= C.
Qed.

Lemma intern_incr_restrict mu mu' X X' :
  intern_incr mu mu' -> 
  {subset X <= X'} -> 
  (forall b b' ofs, extern_of mu' b = Some (b',ofs) -> ~~ [predD X' & X] b) -> 
  intern_incr (restrict_sm mu X) (restrict_sm mu' X').
Proof.
case=> A []B []C []D []E []F []G []H []I J K; split=> //.
by rewrite 2!restrict_sm_local; apply: restrict_incr'.
split; first by rewrite 2!restrict_sm_extern; rewrite B; apply: restrict_disj.
split; first by rewrite 2!restrict_sm_locBlocksSrc; apply: C.
split; first by rewrite 2!restrict_sm_locBlocksTgt; apply: D.
split; first by rewrite 2!restrict_sm_pubBlocksSrc E.
split; first by rewrite 2!restrict_sm_pubBlocksTgt F.
split; first by rewrite 2!restrict_sm_frgnBlocksSrc G.
split; first by rewrite 2!restrict_sm_frgnBlocksTgt H.
split; first by rewrite 2!restrict_sm_extBlocksSrc I.
by rewrite 2!restrict_sm_extBlocksTgt J.
Qed.

Lemma join_sm_vis_loc mu1 (mu1' : Inj.t) mu2 b : 
  intern_incr mu1 mu1' -> 
  vis (join_sm mu1 mu2) b=false -> 
  vis (join_sm mu1' mu2) b -> 
  locBlocksSrc mu1 b=false /\ locBlocksSrc mu1' b.
Proof.
rewrite 2!vis_join_sm /=/in_mem/=/in_mem/=.
move=> incr D E.
have F: locBlocksSrc mu1 b=false by move: D; case: (locBlocksSrc mu1 b).
rewrite F in D; move: D=> /= => D.
have G: locBlocksSrc mu2 b=false by move: D; case: (locBlocksSrc mu2 b).
rewrite G in D; move: D=> /= => D.
have H: (frgnBlocksSrc mu1 b=false \/ frgnBlocksSrc mu2 b=false).
  move: D; case: (frgnBlocksSrc mu1 b); case: (frgnBlocksSrc mu2 b)=> //=.
  by right. by left. by right.
have I: (frgnBlocksSrc mu1' b && frgnBlocksSrc mu2 b = false).
  move: H; case: incr=> _ []_ []_ []_ []_ []_ []<- []_ _.
  case: (frgnBlocksSrc mu1 b)=> //.
  case: (frgnBlocksSrc mu2 b)=> //.  
  by case.
have J: locBlocksSrc mu1' b.
  by move: E; rewrite G I=> /=; move/orP; case=> //; move/orP; case.
by split.
Qed.

Lemma join_sm_vis_dom mu1 (mu1' : Inj.t) mu2 b : 
  intern_incr mu1 mu1' -> 
  vis (join_sm mu1 mu2) b=false -> 
  vis (join_sm mu1' mu2) b -> 
  DOM mu1 b=false /\ DOM mu1' b.
Proof.
rewrite 2!vis_join_sm /=/in_mem/=/in_mem/=.
move=> incr D E.
have F: locBlocksSrc mu1 b=false by move: D; case: (locBlocksSrc mu1 b).
rewrite F in D; move: D=> /= => D.
have G: locBlocksSrc mu2 b=false by move: D; case: (locBlocksSrc mu2 b).
rewrite G in D; move: D=> /= => D.
have H: (frgnBlocksSrc mu1 b=false \/ frgnBlocksSrc mu2 b=false).
  move: D; case: (frgnBlocksSrc mu1 b); case: (frgnBlocksSrc mu2 b)=> //=.
  by right. by left. by right.
have I: (frgnBlocksSrc mu1' b && frgnBlocksSrc mu2 b = false).
  move: H; case: incr=> _ []_ []_ []_ []_ []_ []<- []_ _.
  case: (frgnBlocksSrc mu1 b)=> //.
  case: (frgnBlocksSrc mu2 b)=> //.  
  by case.
have J: locBlocksSrc mu1' b.
  by move: E; rewrite G I=> /=; move/orP; case=> //; move/orP; case.
have K: extBlocksSrc mu1' b=false.
  by apply: (locBlocksSrc_extBlocksSrc _ (Inj_wd mu1') _ J).
have L: extBlocksSrc mu1 b=false.
  by move: H; case: incr=> _ []_ []_ []_ []_ []_ []_ []_ []->.
by rewrite/DOM/DomSrc F J K L.
Qed.

Lemma join_sm_vis_extBlocksSrc mu1 mu1' mu2 : 
  intern_incr mu1 mu1' -> 
  extBlocksSrc (join_sm mu1 mu2) = extBlocksSrc (join_sm mu1' mu2).
Proof.
rewrite 2!join_sm_extSrc.
by case=> _ []_ []_ []_ []_ []_ []_ []_ []->.
Qed.

Lemma join_sm_restrict_incr mu1 (mu1' mu2 : Inj.t) m1 m2 :
  disjoint (local_of mu1') (local_of mu2) -> 
  intern_incr mu1 mu1' -> 
  sm_inject_separated mu1 mu1' m1 m2 -> 
  sm_valid mu2 m1 m2 -> 
  let mu12  := join_sm mu1 mu2 in
  let mu12' := join_sm mu1' mu2 in
  intern_incr (restrict_sm mu12 (vis mu12)) (restrict_sm mu12' (vis mu12')).
Proof.
move=> A B sep val mu12 mu12'; rewrite 2!join_sm_restrict.
have S: {subset vis mu12 <= vis mu12'}.
  { move=> b; rewrite 2!vis_join_sm /in_mem/=/in_mem/=/in_mem/=. 
    move/orP; case=> D; apply/orP.
    left; case: (orP D)=> E; apply/orP; last by right.
    by case: B=> _ []_ []F _; left; apply: (F _ E).
    move: (andP D)=> []E F; right; apply/andP; split=> //.
    by case: B=> _ []_ []_ []_ []_ []_ []<-. }
apply: join_sm_incr=> //. 
by rewrite 2!restrict_sm_local; apply: (disjoint_restrict _ A).
have C: forall b b' ofs, 
  extern_of mu1' b = Some (b',ofs) -> ~~[predD (vis mu12') & (vis mu12)] b.
  { move=> b b' ofs; rewrite/mu12'/= => C; apply/negP; move/andP=> []E F. 
    cut (locBlocksSrc mu1' b). 
    by move/(locBlocksSrc_externNone _ (Inj_wd _)); rewrite C.
    move: E F; rewrite/mu12/vis/in_mem/=; move/negP; rewrite/in_mem/=.
    case: B=> _ []_ []_ []_ []_ []_ []<- []_ []_ _.
    case: (locBlocksSrc mu1 b)=> //; case: (locBlocksSrc mu2 b)=> //.
    by case: (locBlocksSrc mu1' b). }
by apply: (intern_incr_restrict B).
have C: forall b b' ofs, 
  extern_of mu2 b = Some (b',ofs) -> ~~[predD (vis mu12') & (vis mu12)] b.
  { move=> b b' ofs; rewrite/mu12'/= => C; apply/negP; move/andP=> []E F. 
    have G: DOM mu1 b=false /\ DOM mu1' b.
      have E': vis mu12 b = false. 
        by move: E; rewrite/in_mem/=; case: (vis mu12 b).
      have F': vis mu12' b by apply: F.
      by apply (join_sm_vis_dom B E' F').
    rewrite/DOM in G; case: G=> G H; case: sep=> []_ []. 
    have G': DomSrc mu1 b=false. 
      move: G; case: (DomSrc mu1 b)=> //. 
    have H': (is_true false) <-> False by split.
    by move=> I; elimtype False; rewrite -H' -I.
    move/(_ b G' H).
    case: val; rewrite/DOM/DomSrc; move/(_ b).
    case: (extern_DomRng _ (Inj_wd mu2) _ _ _ C)=> -> _ I _ J _.
    by apply: J; apply: I; apply/orP; right. }
by apply: intern_incr_restrict.
Qed.

Lemma join_sm_inject_separated (mu1 mu1' mu2 : Inj.t) m1 m2 m1' m2' : 
  Consistent mu1 mu2 -> 
  intern_incr mu1 mu1' -> 
  sm_inject_separated mu1 mu1' m1 m2 -> 
  sm_locally_allocated mu1 mu1' m1 m2 m1' m2' -> 
  sm_valid mu1 m1 m2 -> 
  sm_valid mu2 m1 m2 -> 
  sm_inject_separated (join_sm mu1 mu2) (join_sm mu1' mu2) m1 m2.
Proof.
move=> consistent A []B []C D E val F.
rewrite ->sm_locally_allocatedChar in E.
case: E=> E1 []E2 []E3 []E4 []E5 E6.
split.
move=> b1 b2 d.
rewrite/join_sm/DomSrc/DomTgt/as_inj/in_mem/=/in_mem/=.
move/joinP'=> []G. move/joinP'=> []H I.
move/joinP=> J.
rewrite ->join2P' in G=> //.
case: J.
move/join2P=> []J K.
case: G=> L.
case: (B b1 b2 d).
by rewrite/as_inj/join L H.
by rewrite/as_inj/join J.
move=> M N.
split.
move: M N; rewrite/DomSrc/DomTgt.
case: (locBlocksSrc mu1 b1)=> //.
case: (extBlocksSrc mu1 b1)=> //.
case: (locBlocksTgt mu1 b2)=> //=.
case: (extern_DomRng _ (Inj_wd _) _ _ _ K)=> _ M.
have ->: locBlocksSrc mu2 b1 = false. 
  case: (extern_DomRng _ (Inj_wd _) _ _ _ K).
  by move/(extBlocksSrc_locBlocksSrc _ (Inj_wd _))=> ->.
by [].
move: M N; rewrite/DomSrc/DomTgt.
case: (locBlocksSrc mu1 b1)=> //.
case: (extBlocksSrc mu1 b1)=> //.
case: (locBlocksTgt mu1 b2)=> //=.
case: (extBlocksTgt mu1 b2)=> //=.
case: (extern_DomRng _ (Inj_wd _) _ _ _ K)=> M N.
have ->: locBlocksTgt mu2 b2 = false. 
  case: (extern_DomRng _ (Inj_wd _) _ _ _ K)=> _.
  by move/(extBlocksTgt_locBlocksTgt _ (Inj_wd _))=> ->.
by [].
rewrite K in L; congruence.
move=> []. move/join2P'=> J.
move/joinP=> K.
case: K. move=> K.
case: G=> G.
case: (B b1 b2 d).
by rewrite/as_inj/join G H.
rewrite/as_inj/join.
have ->: extern_of mu1' b1=None. 
  case X: (extern_of mu1' b1)=> // [[? ?]].
  case: (extern_DomRng _ (Inj_wd _) _ _ _ X)=> Y _.
  case: (local_DomRng _ (Inj_wd _) _ _ _ K)=> Z _.
  by move: Y Z; move/(extBlocksSrc_locBlocksSrc _ (Inj_wd _))=> ->.
by [].
move=> M N.
split.
move: M N; rewrite/DomSrc/DomTgt.
case X: (locBlocksSrc mu1 b1)=> //.
case Y: (extBlocksSrc mu1 b1)=> //.
case: (locBlocksTgt mu1 b2)=> //.
case: (extBlocksTgt mu1 b2)=> //.
simpl.
have L: ~Memory.Mem.valid_block m1 b1.
  apply: C.
  by rewrite/DomSrc X Y.
  case: (local_DomRng _ (Inj_wd _) _ _ _ K).
  rewrite/DomSrc.
  by move=> ->.
case M: (locBlocksSrc mu2 b1)=> //.
case: F; move/(_ b1)=> N.
elimtype False.
apply: L; apply: N.
by rewrite/DOM/DomSrc M.
move: M N; rewrite/DomSrc/DomTgt.
case: (locBlocksSrc mu1 b1)=> //.
case: (extBlocksSrc mu1 b1)=> //.
case X: (locBlocksTgt mu1 b2)=> //.
case Y: (extBlocksTgt mu1 b2)=> //.
simpl.
have L: ~Memory.Mem.valid_block m2 b2.
  apply: D.
  by rewrite/DomTgt X Y.
  case: (local_DomRng _ (Inj_wd _) _ _ _ K).
  rewrite/DomTgt.
  by move=> _ ->.
case M: (locBlocksTgt mu2 b2)=> //.
case: F=> _; move/(_ b2)=> N.
elimtype False.
apply: L; apply: N.
by rewrite/RNG/DomTgt M.
case: (local_DomRng _ (Inj_wd _) _ _ _ K)=> M N.
rewrite E3 in M.
rewrite E4 in N.
have O: extern_of mu1 b1=None. 
  case X: (extern_of mu1 b1)=> // [[? ?]].
  case: (extern_DomRng _ (Inj_wd _) _ _ _ X)=> O P.
  case: val; move/(_ b1)=> Q.
  move: M; case Y: (locBlocksSrc mu1 b1)=> //=.
  rewrite extBlocksSrc_locBlocksSrc in Y=> //.
  by apply: Inj_wd.
  rewrite freshloc_charT=> [][]Z W _.
  elimtype False.
  apply: W.
  apply: Q.
  by rewrite/DOM/DomSrc O; apply/orP; right.
case: (B b1 b2 d).
by rewrite/as_inj/join O H.
rewrite/as_inj/join. 
have ->: extern_of mu1' b1=None. 
  case P: (extern_of mu1' b1)=> // [[? ?]].
  case: (extern_DomRng _ (Inj_wd _) _ _ _ P)=> Q R.
  case: (local_DomRng _ (Inj_wd _) _ _ _ K)=> S T.
  rewrite extBlocksSrc_locBlocksSrc in S=> //.
  by apply: Inj_wd.
by [].
move=> P Q.
split.
move: P; rewrite/DomSrc.
case X: (locBlocksSrc mu1 b1)=> //.
case Y: (extBlocksSrc mu1 b1)=> //.
simpl.
case Z: (locBlocksSrc mu2 b1)=> //.
have L: ~Memory.Mem.valid_block m1 b1.
  apply: C.
  by rewrite/DomSrc X Y.
  case: (local_DomRng _ (Inj_wd _) _ _ _ K).
  rewrite/DomSrc.
  by move=> ->.
case R: (locBlocksSrc mu2 b1)=> //.
case: F; move/(_ b1)=> S.
elimtype False.
apply: L; apply: S.
by rewrite/DOM/DomSrc Z.
rewrite Z in R.
congruence.
move: Q; rewrite/DomTgt.
case X: (locBlocksTgt mu1 b2)=> //.
case Y: (extBlocksTgt mu1 b2)=> //.
simpl.
case Z: (locBlocksTgt mu2 b2)=> //.
have L: ~Memory.Mem.valid_block m2 b2.
  apply: D.
  by rewrite/DomTgt X Y.
  case: (local_DomRng _ (Inj_wd _) _ _ _ K).
  rewrite/DomTgt.
  by move=> _ ->.
case R: (locBlocksTgt mu2 b2)=> //.
case: F=> _; move/(_ b2)=> S.
elimtype False.
apply: L; apply: S.
by rewrite/RNG/DomTgt Z.
rewrite Z in R.
congruence.
by rewrite I=> [][].
split.
{ move=> b1.
rewrite/DomSrc/join_sm/=/in_mem/=.
move=> G H.
have G1: locBlocksSrc mu1 b1=false.
  move: G.
  by case: (locBlocksSrc mu1 b1).
have G2: locBlocksSrc mu2 b1=false.
  move: G.
  rewrite G1.
  by case: (locBlocksSrc mu2 b1).
have G3: (extBlocksSrc mu1 b1 && extBlocksSrc mu2 b1)=false.
  move: G.
  case: (extBlocksSrc mu1 b1 && extBlocksSrc mu2 b1)=> //.
  case/orP.
  by right.
have H1: locBlocksSrc mu1' b1=true.
  move: H.
  rewrite G2.
  rewrite E5.
  rewrite G3=> /=.
  by case: (locBlocksSrc mu1' b1).
have G4: extBlocksSrc mu1 b1=false.
  rewrite -E5.
  apply locBlocksSrc_extBlocksSrc in H1=> //.
  by apply: Inj_wd.
apply: C.
by rewrite/DomSrc G1 G4.
by rewrite/DomSrc H1. }
{ move=> b1.
rewrite/DomTgt/join_sm/=/in_mem/=.
move=> G H.
have G1: locBlocksTgt mu1 b1=false.
  move: G.
  by case: (locBlocksTgt mu1 b1).
have G2: locBlocksTgt mu2 b1=false.
  move: G.
  rewrite G1.
  by case: (locBlocksTgt mu2 b1).
have G3: (extBlocksTgt mu1 b1 && extBlocksTgt mu2 b1)=false.
  move: G.
  case: (extBlocksTgt mu1 b1 && extBlocksTgt mu2 b1)=> //.
  case/orP.
  by right.
have H1: locBlocksTgt mu1' b1=true.
  move: H.
  rewrite G2.
  rewrite E6.
  rewrite G3=> /=.
  by case: (locBlocksTgt mu1' b1).
have G4: extBlocksTgt mu1 b1=false.
  rewrite -E6.
  apply locBlocksTgt_extBlocksTgt in H1=> //.
  by apply: Inj_wd.
apply: D.
by rewrite/DomTgt G1 G4.
by rewrite/DomTgt H1. }
Qed.

Lemma join_all_sm_inject_separated 
    (mu_trash : Inj.t) (mu1 mu1' : Inj.t) (mus : seq Inj.t) m1 m2 m1' m2' :
  All (fun mu0 => Consistent mu1 mu0) [seq Inj.mu x | x <- mus] -> 
  All (fun mu0 => sm_valid mu0 m1 m2) [seq Inj.mu x | x <- mus] -> 
  SM_wd (join_all mu_trash $ mus) -> 
  Consistent mu1 mu_trash ->
  intern_incr mu1 mu1' -> 
  sm_inject_separated mu1 mu1' m1 m2 -> 
  sm_locally_allocated mu1 mu1' m1 m2 m1' m2' -> 
  sm_valid mu1 m1 m2 -> 
  sm_valid mu_trash m1 m2 -> 
  sm_inject_separated 
    (join_all mu_trash $ mu1 :: mus) (join_all mu_trash $ mu1' :: mus) m1 m2.
Proof.
elim: mus; first by move=> _ _ _; apply: join_sm_inject_separated.
move=> mu0 mus' IH cons1 /=. 
move=> []val1 allval wd cons2 incr sep localloc val2 valtr.
have B': All [eta Consistent mu1] [seq Inj.mu x | x <- mu_trash :: mus'].
  by move=> /=; split=> //; move: cons1=> /= [].
move: (join_all_consistent B')=> G. 
change (sm_inject_separated (join_sm mu1 (Inj.mk wd)) 
                            (join_sm mu1' (Inj.mk wd)) m1 m2).
apply join_sm_inject_separated with (m1':=m1') (m2':=m2')=> //.
by rewrite/join_sm/=; apply: join2_consistent=> //; move: cons1=> //= [].
apply: join_sm_valid=> //; apply: join_all_valid=> //; move: allval.
by rewrite -All_comp.
Qed.

Lemma join_sm_DomSrc mu1 mu2 : 
  DomSrc (join_sm mu1 mu2) 
  = (fun b => locBlocksSrc mu1 b || locBlocksSrc mu2 b
           || extBlocksSrc mu1 b && extBlocksSrc mu2 b).
Proof. by []. Qed.

Lemma join_sm_DomTgt mu1 mu2 : 
  DomTgt (join_sm mu1 mu2) 
  = (fun b => locBlocksTgt mu1 b || locBlocksTgt mu2 b
           || extBlocksTgt mu1 b && extBlocksTgt mu2 b).
Proof. by []. Qed.

Lemma join_sm_locBlocksSrc mu1 mu2 : 
  locBlocksSrc (join_sm mu1 mu2) 
  = (fun b => locBlocksSrc mu1 b || locBlocksSrc mu2 b).
Proof. by []. Qed.

Lemma join_sm_locBlocksTgt mu1 mu2 : 
  locBlocksTgt (join_sm mu1 mu2) 
  = (fun b => locBlocksTgt mu1 b || locBlocksTgt mu2 b).
Proof. by []. Qed.

Lemma join_sm_extBlocksSrc mu1 mu2 : 
  extBlocksSrc (join_sm mu1 mu2) 
  = (fun b => extBlocksSrc mu1 b && extBlocksSrc mu2 b).
Proof. by []. Qed.

Lemma join_sm_extBlocksTgt mu1 mu2 : 
  extBlocksTgt (join_sm mu1 mu2) 
  = (fun b => extBlocksTgt mu1 b && extBlocksTgt mu2 b).
Proof. by []. Qed.

Lemma join_sm_locally_allocated mu1 mu1' mu2 m1 m2 m1' m2' :
  sm_locally_allocated mu1 mu1' m1 m2 m1' m2' -> 
  sm_locally_allocated (join_sm mu1 mu2) (join_sm mu1' mu2) m1 m2 m1' m2'.
Proof.
rewrite 2!sm_locally_allocatedChar.
move=> []A []B []C []D []E F.
rewrite !join_sm_DomSrc !join_sm_DomTgt. 
rewrite !join_sm_locBlocksSrc !join_sm_locBlocksTgt.
rewrite !join_sm_extBlocksSrc !join_sm_extBlocksTgt.
split.
extensionality b; rewrite C E -(orb_comm (freshloc _ _ _)) -!orb_assoc.
by rewrite (orb_comm (freshloc _ _ _)) !orb_assoc.
split.
extensionality b; rewrite D F -(orb_comm (freshloc _ _ _)) -!orb_assoc.
by rewrite (orb_comm (freshloc _ _ _)) !orb_assoc.
split.
by extensionality b; rewrite C -orb_assoc (orb_comm (freshloc _ _ _)) orb_assoc.
split.
extensionality b; rewrite D. 
by rewrite -orb_assoc (orb_comm (freshloc _ _ _)) orb_assoc.
split; extensionality b; first by rewrite E.
by rewrite F.
Qed.

Lemma join_all_locally_allocated mu_trash (mu mu' : Inj.t) mus m1 m2 m1' m2' :
  sm_locally_allocated mu mu' m1 m2 m1' m2' -> 
  sm_locally_allocated 
    (join_all mu_trash (mu :: mus)) 
    (join_all mu_trash (mu' :: mus)) m1 m2 m1' m2'.
Proof.
elim: mus; first by rewrite !join_all_cons; apply: join_sm_locally_allocated.
move=> mu0 mus' IH A; rewrite 2!join_all_cons. 
by apply: join_sm_locally_allocated.
Qed.

Lemma All_disjoint (mu_trash : Inj.t) (mu : Inj.t) mus : 
  disjoint (local_of mu) (local_of mu_trash) -> 
  All (fun mu2 : Inj.t => disjoint (local_of mu) (local_of mu2)) mus -> 
  disjoint (local_of mu) (local_of (join_all mu_trash mus)).
Proof.
elim: mus=> // mu0 mus' IH A /= []B C.
rewrite disjoint_com; apply: join_disjoint; first by rewrite disjoint_com.
by rewrite disjoint_com; apply: IH.
Qed.

Lemma DisjointLS_disjoint (mu mu' : Inj.t) : 
  DisjointLS mu mu' -> disjoint (local_of mu) (local_of mu').
Proof.
move=> A b.
case B: (local_of mu b)=> [[? ?]|].
case: (local_DomRng _ (Inj_wd _) _ _ _ B)=> C _.
case E: (local_of mu' b)=> [[? ?]|].
case: (local_DomRng _ (Inj_wd _) _ _ _ E)=> D _.
by move: D; move: (DisjointLS_E1 A C)=> ->.
by right.
by left.
Qed.

Lemma join_all_restrict_incr (mu_trash mu mu' : Inj.t) (mus : seq Inj.t) m1 m2 : 
  All (fun mu2 : Inj.t => disjoint (local_of mu') (local_of mu2)) mus -> 
  All (DisjointLS mu_trash) $ map Inj.mu mus -> 
  All (DisjointLT mu_trash) $ map Inj.mu mus -> 
  All (fun mu2 => consistent (extern_of mu_trash) (extern_of mu2)) 
      $ map Inj.mu mus -> 
  disjoint (local_of mu') (local_of mu_trash) -> 
  AllDisjoint locBlocksSrc \o map Inj.mu $ mus -> 
  AllDisjoint locBlocksTgt \o map Inj.mu $ mus -> 
  AllConsistent \o map Inj.mu $ mus -> 
  All (fun mu2 => sm_valid (Inj.mu mu2) m1 m2) mus -> 
  intern_incr mu mu' -> 
  sm_inject_separated mu mu' m1 m2 -> 
  sm_valid (Inj.mu mu_trash) m1 m2 -> 
  let mu_tot  := join_all mu_trash (mu :: mus) in
  let mu_tot' := join_all mu_trash (mu' :: mus) in
  intern_incr (restrict_sm mu_tot (vis mu_tot)) (restrict_sm mu_tot' (vis mu_tot')).
Proof.
move=> A disj_S disj_T consist disj_trash allS allT allC B C D E top top'. 
rewrite/top/top' 2!join_all_cons.
have G: SM_wd (join_all mu_trash mus) by apply: join_all_wd.
have H: sm_valid (Inj.mk G) m1 m2 by apply: join_all_valid.
have I: disjoint (local_of mu') (local_of (Inj.mk G)).
  by apply: All_disjoint.
by apply: (join_sm_restrict_incr I C D H).
Qed.

Lemma join_all_restrict_sep
    (mu_trash : Inj.t) (mu1 mu1' : Inj.t) (mus : seq Inj.t) m1 m2 m1' m2' :
  All (fun mu0 => Consistent mu1 mu0) [seq Inj.mu x | x <- mus] -> 
  All (fun mu0 => sm_valid mu0 m1 m2) [seq Inj.mu x | x <- mus] -> 
  Consistent mu1 mu_trash ->
  sm_valid mu_trash m1 m2 -> 
  sm_valid mu1 m1 m2 -> 
  intern_incr mu1 mu1' -> 
  sm_inject_separated mu1 mu1' m1 m2 -> 
  sm_locally_allocated mu1 mu1' m1 m2 m1' m2' -> 
  let mu_tot  := join_all mu_trash (mu1 :: mus) in
  let mu_tot' := join_all mu_trash (mu1' :: mus) in
  sm_valid mu_tot m1 m2 ->
  SM_wd (join_all mu_trash mus) -> 
  SM_wd mu_tot -> 
  sm_inject_separated  
    (restrict_sm mu_tot (vis mu_tot)) 
    (restrict_sm mu_tot' (vis mu_tot')) m1 m2.
Proof.
move=> A B C D val incr E loc_alloc mu_tot mu_tot' F tot'_wd tot_wd.
have Cut: sm_inject_separated mu_tot mu_tot' m1 m2.
  apply: join_all_sm_inject_separated=> //.
  by eapply loc_alloc.
set mu_tot2 := Inj.mk tot_wd. 
change (sm_inject_separated 
         (restrict_sm mu_tot2 (vis mu_tot2))
         (restrict_sm mu_tot' (vis mu_tot')) m1 m2).
  apply: sm_sep_restrict2=> //.
move=> b Y Z.
have [G H]: [/\ locBlocksSrc mu1 b=false & locBlocksSrc mu1' b=true].
  by apply (join_sm_vis_loc incr Y Z).
apply sm_locally_allocatedChar in loc_alloc.
case loc_alloc=> A1 []A2 []A3 []A4 []A5 A6.
rewrite A3 G /= in H.
rewrite ->freshloc_charT in H.
by case: H.
Qed.

Lemma vis_restrict_sm mu X : vis (restrict_sm mu X) = vis mu.
Proof.
by extensionality b; case: mu.
Qed.

Lemma sm_locally_allocated_refl mu m1 m2 :
  sm_locally_allocated mu mu m1 m2 m1 m2.
Proof.
case: mu=> // ? ? ? ? ? ? ? ? ? ? /=; split=> //.
by extensionality b; rewrite freshloc_irrefl orb_false_r. 
split; first by extensionality b; rewrite freshloc_irrefl orb_false_r. 
by split.
Qed.