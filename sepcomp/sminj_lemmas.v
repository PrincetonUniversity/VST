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
Require Import sepcomp.effect_simulations.
Require Import sepcomp.pred_lemmas.

(* This file collects lemmas on structured injections. *)

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

Lemma smvalid_src_mem_forward mu m m' : 
  smvalid_src mu m -> mem_forward m m' -> smvalid_src mu m'.
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

(* The following variation of [join] is appropriate for shared resources       *)
(* like extern injections: each core must have a consistent mapping on         *)
(* extern blocks but the domains of the mappings are not necessarily disjoint. *)

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

Definition consistent (j k : Values.meminj) := 
  forall b1 b2 b2' d2 d2', 
  j b1 = Some (b2,d2) -> k b1 = Some (b2',d2') -> [/\ b2=b2' & d2=d2'].

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
  Disjoint (locBlocksSrc mu1) (locBlocksSrc mu2) -> 
  Disjoint (locBlocksTgt mu1) (locBlocksTgt mu2) -> 
  consistent (extern_of mu1) (extern_of mu2) -> 
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

Fixpoint All T P (l : seq T) :=
  match l with
    | nil => True
    | a :: l' => [/\ P a & All P l']
  end.

Fixpoint All2_aux T P (a : T) (l : seq T) :=
  if l is [:: a' & l'] then
    [/\ P a a' & All2_aux P a l']
  else True. 

Fixpoint All2 T (P : T -> T -> Prop) (l : seq T) :=
  if l is [:: a & l'] then [/\ All2_aux P a l' & All2 P l']
  else True.

Lemma All2_cons T P (a : T) (l : seq T) :
  All2 P [:: a & l] <-> [/\ All2_aux P a l & All2 P l].
Proof. by split=> /= => [][]A B; split. Qed.

Definition AllDisjoint (proj : SM_Injection -> Values.block -> bool) := 
  All2 (fun mu mu' => Disjoint (proj mu) (proj mu')).

Definition AllConsistent := 
  All2 (fun mu mu' => consistent (extern_of mu) (extern_of mu')).

Fixpoint join_all (mu0 : Inj.t) (mus : seq Inj.t) : SM_Injection :=
  if mus is [:: mu & mus] then join_sm mu (join_all mu0 mus)
  else mu0.

Lemma join_all_disjoint_src mu0 (mu : Inj.t) mus :
  All2_aux 
    (fun mu mu' => Disjoint (locBlocksSrc mu) (locBlocksSrc mu'))  
    mu0 (map Inj.mu (mus ++ [:: mu])) -> 
  Disjoint (locBlocksSrc mu0) (locBlocksSrc (join_all mu mus)).
Proof.
elim: mus=> //=; first by move=> [].
by move=> mu' mus' IH []A B; move: (IH B)=> C; apply: DisjointInU.
Qed.

Lemma join_all_disjoint_tgt mu0 (mu : Inj.t) mus :
  All2_aux 
    (fun mu mu' => Disjoint (locBlocksTgt mu) (locBlocksTgt mu'))  
    mu0 (map Inj.mu (mus ++ [:: mu])) -> 
  Disjoint (locBlocksTgt mu0) (locBlocksTgt (join_all mu mus)).
Proof.
elim: mus=> //=; first by move=> [].
by move=> mu' mus' IH []A B; move: (IH B)=> C; apply: DisjointInU.
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
  All2_aux 
    (fun mu mu' => consistent (extern_of mu) (extern_of mu'))  
    mu0 (map Inj.mu (mus ++ [:: mu])) -> 
  consistent (extern_of mu0) (extern_of (join_all mu mus)).
Proof.
elim: mus=> //=; first by move=> [].
by move=> mu' mus' IH []A B; move: (IH B)=> C; apply: join2_consistent.
Qed.

Lemma join_all_wd mu (mus : seq Inj.t) :
  (AllDisjoint locBlocksSrc \o map Inj.mu) (mus ++ [:: mu]) -> 
  (AllDisjoint locBlocksTgt \o map Inj.mu) (mus ++ [:: mu]) -> 
  (AllConsistent \o map Inj.mu) (mus ++ [:: mu]) -> 
  SM_wd (join_all mu mus).
Proof.
elim: mus=> /=; first by move=> _ _ _; apply: (Inj_wd mu).
move=> mu0 mus IH.
move/All2_cons=> []A B. 
move/All2_cons=> []C D.
move/All2_cons=> []E F.
have wd: SM_wd (join_all mu mus) by apply: (IH B D).
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
  {subset (extBlocksSrc (join_sm mu1 mu2)) 
  <= [predI (extBlocksSrc mu1) & extBlocksSrc mu2]}.
Proof. by rewrite/join_sm /= => b; rewrite in_predI. Qed.

Lemma join_sm_extTgt mu1 mu2 : 
  {subset (extBlocksTgt (join_sm mu1 mu2)) 
  <= [predI (extBlocksTgt mu1) & extBlocksTgt mu2]}.
Proof. by rewrite/join_sm /= => b; rewrite in_predI. Qed.

Lemma join_sm_frgnSrc mu1 mu2 : 
  {subset (frgnBlocksSrc (join_sm mu1 mu2)) 
  <= [predI (frgnBlocksSrc mu1) & frgnBlocksSrc mu2]}.
Proof. by rewrite/join_sm /= => b; rewrite in_predI. Qed.

Lemma join_sm_frgnTgt mu1 mu2 : 
  {subset (frgnBlocksTgt (join_sm mu1 mu2)) 
  <= [predI (frgnBlocksTgt mu1) & frgnBlocksTgt mu2]}.
Proof. by rewrite/join_sm /= => b; rewrite in_predI. Qed.

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

Lemma join_all_id mu : join_all mu [::] = mu.
Proof. by []. Qed.

Lemma join_all_preserves_globals 
      F V (ge : Genv.t F V) (mu : Inj.t) (mus : seq Inj.t) : 
  Events.meminj_preserves_globals ge (extern_of mu) ->
  (AllDisjoint locBlocksSrc \o map Inj.mu) (mus ++ [:: mu]) -> 
  (AllDisjoint locBlocksTgt \o map Inj.mu) (mus ++ [:: mu]) -> 
  (AllConsistent \o map Inj.mu) (mus ++ [:: mu]) -> 
  All (Events.meminj_preserves_globals ge \o extern_of \o Inj.mu) mus -> 
  Events.meminj_preserves_globals ge (extern_of (join_all mu mus)).
Proof.
elim: mus=> //= mu' mus' IH A. 
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



