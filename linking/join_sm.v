Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Bool.
Require Import Zbool.
Require Import BinPos. 

Require Import compcert. Import CompcertCommon.

Require Import msl.Axioms.

Require Import linking.sepcomp. Import SepComp.

Require Import linking.pred_lemmas.
Require Import linking.seq_lemmas.
Require Import linking.inj_lemmas.

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

(* Why is this lemma not in ZArith?!? *)

Lemma Zeq_bool_refl x : Zeq_bool x x.
Proof. by case: (Zeq_is_eq_bool x x)=> A _; apply: A. Qed.

Lemma Zeq_bool_sym x y : Zeq_bool x y = Zeq_bool y x.
Proof. 
case e: (Zeq_bool x y).
rewrite (Zeq_bool_eq _ _ e).
by rewrite Zeq_bool_refl.
move: (Zeq_bool_neq _ _ e)=> neq.
case f: (Zeq_bool y x)=> //.
move: (Zeq_bool_eq _ _ f)=> eq. 
by subst x; elimtype False; apply: neq.
Qed.

Lemma join2_inject_incr j k : 
  inject_incr j k -> 
  join2 j k = j.
Proof.
move=> incr; rewrite /join2; extensionality b.
case jj: (j b)=> //[[x y]].
move: (incr _ _ _ jj).
case kk: (k b)=> [[x' y']|//].
case=> -> ->.
by rewrite Pos.eqb_refl Zeq_bool_refl.
Qed.

Lemma join2C j k : join2 j k = join2 k j.
Proof.
rewrite /join2; extensionality b.
case: (j b)=> [[x y]|].
case: (k b)=> [[x' y']|].
rewrite Pos.eqb_sym.
rewrite Zeq_bool_sym.
case e: (_ && _)=> //.
case: (andP e).
move/Peqb_true_eq=> ->.
by move/Zeq_bool_eq=> ->.
by [].
by case: (k b)=> [[? ?]|].
Qed.

Lemma join2A j k l : join2 j (join2 k l) = join2 (join2 j k) l.
Proof.
rewrite /join2; extensionality b.
case: (j b)=> [[x y]|] //.
case: (k b)=> [[x' y']|] //.
case: (l b)=> [[x'' y'']|] //.
rewrite Pos.eqb_sym.
rewrite Zeq_bool_sym.
case e: (_ && _)=> //.
case: (andP e).
move/Peqb_true_eq=> ->.
move/Zeq_bool_eq=> ->.
rewrite Pos.eqb_sym.
rewrite Zeq_bool_sym.
case f: (_ && _)=> //.
case: (andP f).
move/Peqb_true_eq=> ->.
move/Zeq_bool_eq=> ->.
by rewrite Pos.eqb_refl Zeq_bool_refl.
case f: (_ && _)=> //.
case: (andP f).
move/Peqb_true_eq=> ->.
move/Zeq_bool_eq=> ->.
case g: (_ && _)=> //.
case: (andP g).
move/Peqb_true_eq=> A.
move/Zeq_bool_eq=> B.
move: e; rewrite andb_false_iff; case.
by rewrite A Pos.eqb_refl.
by rewrite B Zeq_bool_refl.
by case e: (_ && _).
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
  [fun mu mu' => consistent (as_inj mu) (as_inj mu')].

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
have A0': as_inj mu1 b1 = Some (b2,d2).
  by rewrite /as_inj /join A0.
have B0': as_inj mu2 b1 = Some (b2',d2').
  by rewrite /as_inj /join B0.
move: (C12 _ _ _ _ _ A0' B0') H; case=> <- <-; move/andP=> []; split.
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
  All2 (fun mu mu' => consistent (as_inj mu) (as_inj mu')).

Fixpoint join_all (mu0 : Inj.t) (mus : seq Inj.t) : SM_Injection :=
  if mus is [:: mu & mus] then join_sm mu (join_all mu0 mus)
  else mu0.

Lemma join_all_cons mu0 mu mus : 
  join_all mu0 (mu :: mus) = join_sm mu (join_all mu0 mus).
Proof. by []. Qed.

Lemma join_all_frgnS_cons mu0 mu mus : 
  frgnBlocksSrc (join_all mu0 (mu :: mus))
  = [predI (frgnBlocksSrc mu) & frgnBlocksSrc (join_all mu0 mus)].
Proof. by rewrite join_all_cons. Qed.

Lemma join_all_frgnT_cons mu0 mu mus : 
  frgnBlocksTgt (join_all mu0 (mu :: mus))
  = [predI (frgnBlocksTgt mu) & frgnBlocksTgt (join_all mu0 mus)].
Proof. by rewrite join_all_cons. Qed.

Lemma join_all_extS_cons mu0 mu mus : 
  extBlocksSrc (join_all mu0 (mu :: mus))
  = [predI (extBlocksSrc mu) & extBlocksSrc (join_all mu0 mus)].
Proof. by rewrite join_all_cons. Qed.

Lemma join_all_extT_cons mu0 mu mus : 
  extBlocksTgt (join_all mu0 (mu :: mus))
  = [predI (extBlocksTgt mu) & extBlocksTgt (join_all mu0 mus)].
Proof. by rewrite join_all_cons. Qed.

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

Lemma local_some_extern_none (mu : Inj.t) b1 b2 d2 : 
  local_of mu b1 = Some (b2,d2) -> 
  extern_of mu b1 = None.
Proof.
case/local_DomRng; first by apply Inj_wd.
move/locBlocksSrc_externNone=> -> //.
by apply: Inj_wd.
Qed.

Lemma locof_extof_False (mu : Inj.t) (mus : seq Inj.t) b1 b2 d2 b2' d2' :
  local_of (join_all mu mus) b1 = Some (b2, d2) -> 
  extern_of (join_all mu mus) b1 = Some (b2', d2') -> 
  False.
Proof.
elim: mus=> //; first by move/local_some_extern_none=> ->.
move=> mu0 mus' IH /=; rewrite /join.
case e: (local_of mu0 b1)=> [[b' ofs']|].
case=> e1 e2; rewrite e1 e2 in e.
by move/join2P=> []; move: (local_some_extern_none e)=> ->.
move=> A; move/join2P=> []B C.
apply: (IH A C).
Qed.

Lemma join_sm_consistent mu0 (mu1 mu2 : Inj.t) :
  Consistent mu0 mu1 -> 
  Consistent mu0 mu2 -> 
  Consistent mu0 (join_sm mu1 mu2).
Proof.
move=> A B b1 b2 b2' d2 d2' E /=; rewrite /join_sm /as_inj /join /=.
case e: (join2 _ _ _)=> // [[b' ofs']|].
case=> e1 e2; rewrite e1 e2 in e.
move: e; move/join2P=> []E1 E2.
have E1': as_inj mu1 b1 = Some (b2',d2').
  by rewrite /as_inj /join E1.
by apply: (A _ _ _ _ _ E E1').
case f: (local_of _ _)=> // [[b' ofs']|].
case=> e1 e2.
rewrite e1 e2 in f.
have F: extern_of mu1 b1 = None.
  by apply: (local_some_extern_none f).
have G: as_inj mu1 b1 = Some (b2',d2').
  by rewrite /as_inj /join F f.
by apply: (A _ _ _ _ _ E G).
move=> F. 
have G: as_inj mu2 b1 = Some (b2',d2').
  rewrite /as_inj /join F.
  case G: (extern_of _ _)=> //[[b' ofs']].
  by rewrite (local_some_extern_none F) in G.
by apply: (B _ _ _ _ _ E G).
Qed.

Lemma join_sm_consistent' mu0 (mu1 mu2 : Inj.t) (mus : seq Inj.t) :
  Consistent mu0 mu1 -> 
  Consistent mu0 (join_all mu2 mus) -> 
  Consistent mu0 (join_sm mu1 (join_all mu2 mus)).
Proof.
move=> A B b1 b2 b2' d2 d2' E /=; rewrite /join_sm /as_inj /join /=.
case e: (join2 _ _ _)=> // [[b' ofs']|].
case=> e1 e2; rewrite e1 e2 in e.
move: e; move/join2P=> []E1 E2.
have E1': as_inj mu1 b1 = Some (b2',d2').
  by rewrite /as_inj /join E1.
by apply: (A _ _ _ _ _ E E1').
case f: (local_of _ _)=> // [[b' ofs']|].
case=> e1 e2.
rewrite e1 e2 in f.
have F: extern_of mu1 b1 = None.
  by apply: (local_some_extern_none f).
have G: as_inj mu1 b1 = Some (b2',d2').
  by rewrite /as_inj /join F f.
by apply: (A _ _ _ _ _ E G).
move=> F. 
have G: as_inj (join_all mu2 mus) b1 = Some (b2',d2').
  rewrite /as_inj /join F.
  case G: (extern_of _ _)=> //[[b' ofs']].
  by elimtype False; apply: (locof_extof_False F G).
by apply: (B _ _ _ _ _ E G).
Qed.

Lemma join_all_consistent mu0 (mu : Inj.t) mus :
  All (fun mu' => consistent (as_inj mu0) (as_inj mu'))  
    (map Inj.mu (mu :: mus)) -> 
  consistent (as_inj mu0) (as_inj (join_all mu mus)).
Proof.
elim: mus=> //=; first by move=> [].
move=> mu' mus' IH []A []B C; move: (IH (conj A C))=> D.
by apply: join_sm_consistent'.
Qed.

Lemma join2P' (j k : SM_Injection) b1 :                                
  Consistent j k ->                                                    
  (join2 (extern_of j) (extern_of k) b1 = None <->                     
   [\/ extern_of j b1 = None | extern_of k b1 = None]).                
Proof.                                                                 
rewrite /=/consistent=> C.                                             
rewrite/join2; split.                                                  
case A: (extern_of j b1)=> // [[x y]|].                                
case B: (extern_of k b1)=> // [[x' y']|].                                
have A': as_inj j b1 = Some (x,y) by rewrite /as_inj /join A.
have B': as_inj k b1 = Some (x',y') by rewrite /as_inj /join B.
case: (C _ _ _ _ _ A' B')=> -> ->.                                       
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
by apply join_all_consistent.
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
move: cons1=> /= []H I. 
have J: Consistent mu1 (join_all mu_trash mus').
  by apply: join_all_consistent.
by apply: (join_sm_consistent' H J).
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
  All (fun mu2 => Consistent mu_trash mu2) $ map Inj.mu mus -> 
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

Lemma join_absorb f g : join f (join f g) = join f g.
Proof.
by rewrite /join; extensionality a; case: (f a).
Qed.

Lemma join_absorb' f' f g : 
  inject_incr f' f -> 
  join f' (join f g) = join f g.
Proof.
move=> A; rewrite /join; extensionality a.
by case e: (f' a)=> // [[b ofs]]; rewrite (A _ _ _ e).
Qed.

Lemma join_sm_absorb mu1 mu2 : 
  join_sm mu1 (join_sm mu1 mu2) = join_sm mu1 mu2.
Proof.
case: mu1=> ? ? ? ? ? ? ? ? ? ?; rewrite /join_sm /join2 /=; f_equal.
by rewrite predU_absorb.
by rewrite predU_absorb.
by rewrite join_absorb.
by rewrite predI_absorb.
by rewrite predI_absorb.
by rewrite predI_absorb.
by rewrite predI_absorb.
extensionality a.
case: (_ a)=> //.
move=> [b ofs].
case: (extern_of _ _)=> //.
move=> [b' ofs'].
case: (_ && _)=> //.
by rewrite Pos.eqb_refl Zeq_bool_refl.
Qed.

Lemma join_sm_absorb' mu0 mu1 mu2 : 
  inject_incr (local_of mu0) (local_of mu1) -> 
  inject_incr (extern_of mu1) (extern_of mu0) -> 
  {subset (locBlocksSrc mu0) <= locBlocksSrc mu1} -> 
  {subset (locBlocksTgt mu0) <= locBlocksTgt mu1} -> 
  {subset (extBlocksSrc mu1) <= extBlocksSrc mu0} -> 
  {subset (extBlocksTgt mu1) <= extBlocksTgt mu0} -> 
  {subset (frgnBlocksSrc mu1) <= frgnBlocksSrc mu0} -> 
  {subset (frgnBlocksTgt mu1) <= frgnBlocksTgt mu0} -> 
  join_sm mu0 (join_sm mu1 mu2) = join_sm mu1 mu2.
Proof.
case: mu0=> ? ? ? ? ? ex0s ex0t fr0s fr0t ef0. 
case: mu1=> ? ? ? ? ? ex1s ex1t fr1s fr1t ef1; rewrite /join_sm /join2 /=.
move=> A B C D E F G H; f_equal.
by rewrite predU_absorb'.
by rewrite predU_absorb'.
by rewrite join_absorb'.
by rewrite -predI_absorb_sub.
by rewrite -predI_absorb_sub.
by rewrite -predI_absorb_sub.
by rewrite -predI_absorb_sub.
extensionality a.
case e0: (ef0 a)=> // [[b ofs]|].
case e1: (ef1 a)=> // [[b' ofs']].
case e2: (extern_of _ _)=> // [[b'' ofs'']].
case f: (_ && _)=> //.
case: (andP f).
move/Peqb_true_eq=> ->.
move/Zeq_bool_eq=> ->.
case g: (_ && _)=> //.
case: (andP g).
move/Peqb_true_eq=> ->.
by move/Zeq_bool_eq=> ->.
move: (B _ _ _ e1); rewrite e0; case.
case: (andP f).
move/Peqb_true_eq=> ->.
move/Zeq_bool_eq=> ->.
move=> eq1 eq2.
rewrite eq1 eq2 Pos.eqb_refl Zeq_bool_refl /= in g.
congruence.
case e1: (ef1 a)=> // [[b ofs]].
move: (B _ _ _ e1); rewrite e0; congruence.
Qed.

Lemma join_all_absorb' mu_trash (mu0 mu1 : Inj.t) (mus : seq Inj.t) : 
  inject_incr (local_of mu0) (local_of mu1) -> 
  inject_incr (extern_of mu1) (extern_of mu0) -> 
  {subset (locBlocksSrc mu0) <= locBlocksSrc mu1} -> 
  {subset (locBlocksTgt mu0) <= locBlocksTgt mu1} -> 
  {subset (extBlocksSrc mu1) <= extBlocksSrc mu0} -> 
  {subset (extBlocksTgt mu1) <= extBlocksTgt mu0} -> 
  {subset (frgnBlocksSrc mu1) <= frgnBlocksSrc mu0} -> 
  {subset (frgnBlocksTgt mu1) <= frgnBlocksTgt mu0} -> 
  join_all mu_trash [:: mu0, mu1 & mus] = join_all mu_trash [:: mu1 & mus].
Proof.
by move=> A B C D E F G H /=; rewrite join_sm_absorb'.
Qed.

Lemma join_all_locBlocksSrc mu mus b :
  locBlocksSrc (join_all mu mus) b
  <-> locBlocksSrc mu b
      \/ (exists mu0, List.In mu0 mus /\ locBlocksSrc mu0 b).
Proof.
elim: mus mu=> //=; split=> H1; first by left.
by case: H1=> //; move=> []? [].
case: (orP H1); rewrite /in_mem /= => H2.
by right; exists a; split; first by left.
move: H2; rewrite H; case; first by left.
by case=> x []H2 H3; right; exists x; split=> //; right.
case: H1=> [H1|[x [H2 H3]]]; apply/orP; rewrite /in_mem /=.
by rewrite H; right; left.
case: H2; first by move=> ->; left.
by move=> H4; right; rewrite H; right; exists x; split.
Qed.

Lemma join_all_locBlocksTgt mu mus b :
  locBlocksTgt (join_all mu mus) b
  <-> locBlocksTgt mu b
      \/ (exists mu0, List.In mu0 mus /\ locBlocksTgt mu0 b).
Proof.
elim: mus mu=> //=; split=> H1; first by left.
by case: H1=> //; move=> []? [].
case: (orP H1); rewrite /in_mem /= => H2.
by right; exists a; split; first by left.
move: H2; rewrite H; case; first by left.
by case=> x []H2 H3; right; exists x; split=> //; right.
case: H1=> [H1|[x [H2 H3]]]; apply/orP; rewrite /in_mem /=.
by rewrite H; right; left.
case: H2; first by move=> ->; left.
by move=> H4; right; rewrite H; right; exists x; split.
Qed.

Lemma join_all_extBlocksSrc mu mus b :
  extBlocksSrc (join_all mu mus) b
  <-> extBlocksSrc mu b
      /\ (forall mu0, List.In mu0 mus -> extBlocksSrc mu0 b).
Proof.
elim: mus mu=> //=; split=> H1; first by split.
by case: H1=> //; move=> []? [].
case: (andP H1); rewrite /in_mem /= => H2; rewrite H; case=> H3 H4.
split=> //; move=> mu0; case; first by move=> <-.
by move=> H5; apply: (H4 _ H5).
case: H1=> H1 H2.
apply/andP; rewrite /in_mem /=; split.
by apply: H2; left.
by rewrite H; split=> //; move=> mu0 H3; apply: H2; right.
Qed.

Lemma join_all_frgnBlocksSrc mu mus b :
  frgnBlocksSrc (join_all mu mus) b
  <-> frgnBlocksSrc mu b
      /\ (forall mu0, List.In mu0 mus -> frgnBlocksSrc mu0 b).
Proof.
elim: mus mu=> //=; split=> H1; first by split.
by case: H1=> //; move=> []? [].
case: (andP H1); rewrite /in_mem /= => H2; rewrite H; case=> H3 H4.
split=> //; move=> mu0; case; first by move=> <-.
by move=> H5; apply: (H4 _ H5).
case: H1=> H1 H2.
apply/andP; rewrite /in_mem /=; split.
by apply: H2; left.
by rewrite H; split=> //; move=> mu0 H3; apply: H2; right.
Qed.

Lemma join_all_extBlocksTgt mu mus b :
  extBlocksTgt (join_all mu mus) b
  <-> extBlocksTgt mu b
      /\ (forall mu0, List.In mu0 mus -> extBlocksTgt mu0 b).
Proof.
elim: mus mu=> //=; split=> H1; first by split.
by case: H1=> //; move=> []? [].
case: (andP H1); rewrite /in_mem /= => H2; rewrite H; case=> H3 H4.
split=> //; move=> mu0; case; first by move=> <-.
by move=> H5; apply: (H4 _ H5).
case: H1=> H1 H2.
apply/andP; rewrite /in_mem /=; split.
by apply: H2; left.
by rewrite H; split=> //; move=> mu0 H3; apply: H2; right.
Qed.

Lemma join_all_frgnBlocksTgt mu mus b :
  frgnBlocksTgt (join_all mu mus) b
  <-> frgnBlocksTgt mu b
      /\ (forall mu0, List.In mu0 mus -> frgnBlocksTgt mu0 b).
Proof.
elim: mus mu=> //=; split=> H1; first by split.
by case: H1=> //; move=> []? [].
case: (andP H1); rewrite /in_mem /= => H2; rewrite H; case=> H3 H4.
split=> //; move=> mu0; case; first by move=> <-.
by move=> H5; apply: (H4 _ H5).
case: H1=> H1 H2.
apply/andP; rewrite /in_mem /=; split.
by apply: H2; left.
by rewrite H; split=> //; move=> mu0 H3; apply: H2; right.
Qed.

Lemma join_all_local_of (mu mu0 : Inj.t) mus :
  AllDisjoint locBlocksSrc [seq Inj.mu x | x <- [:: mu, mu0 & mus]] -> 
  local_of (join_all mu [:: mu0 & mus]) 
  = join (local_of mu) (local_of (join_all mu0 mus)).
Proof.
elim: mus mu0 mu=> //=.
move=> mu0 mu /= D; rewrite join_com=> //.
move: D=> /=; case=> /=; case. 
by move/DisjointLS_disjoint; rewrite disjoint_com.
move=> a mus' IH mu0 mu /= D.
symmetry.
rewrite join_assoc.
rewrite (join_com (local_of mu)).
rewrite -join_assoc.
rewrite -(IH mu0 mu).
rewrite join_assoc.
rewrite (join_com (local_of a)).
by rewrite -join_assoc.
case: D=> /= [][]_ []_ H [][]; move/DisjointLS_disjoint. 
by rewrite disjoint_com.
case: D=> /= [][]H1 []H2 H3 [][]H4 H5 []H6 H7.
by split=> //.
case: D=> /= [][]H1 []H2 H3 [][]H4 H5 []H6 H7.
by apply: (DisjointLS_disjoint H2).
Qed.

Lemma DisjointLS_local_of_contra (mu mu' : Inj.t) b b' d' b'' d'' : 
  local_of mu b = Some (b',d') -> 
  local_of mu' b = Some (b'',d'') ->   
  DisjointLS mu mu' -> 
  False.
Proof.
by move=> L1 L2; move/DisjointLS_disjoint; move/(_ b); rewrite L1 L2; case.
Qed.

Section join_all_shift.

Variables mu0 mu1 mu_trash : Inj.t.

Variable mus : seq Inj.t.

Let mu_trash'' := join_sm mu0 mu_trash.

Variable mu_trash''_wd : SM_wd mu_trash''.

Let mu_trash' := Inj.mk mu_trash''_wd.

Lemma join_all_shift_locBlocksSrcE :
  locBlocksSrc (join_all mu_trash' mus)
  = [predU (locBlocksSrc mu0)
    & locBlocksSrc (join_all mu_trash mus)].
Proof.
rewrite /= /predU; f_equal; extensionality b; rewrite /in_mem /= /in_mem /=.
case lOf0: (locBlocksSrc mu0)=> /=.
have H: locBlocksSrc (join_all mu_trash' mus) b.
{ rewrite join_all_locBlocksSrc; left; rewrite /mu_trash' /=.
  by apply/orP; rewrite /in_mem /=; left. }
by [].
have H: 
      is_true (locBlocksSrc (join_all mu_trash mus) b) 
  <-> is_true (locBlocksSrc (join_all mu_trash' mus) b).
{ by rewrite 2!join_all_locBlocksSrc /mu_trash' /= /in_mem /= lOf0. }
have H2: 
    locBlocksSrc (join_all mu_trash mus) b
  = locBlocksSrc (join_all mu_trash' mus) b.
{ move: H; case: (locBlocksSrc (join_all mu_trash mus) b).
  by case=> H1 H2; rewrite H1.
  case: (locBlocksSrc (join_all mu_trash' mus) b)=> //.
  by case=> //_; move/(_ erefl). }
by rewrite H2. 
Qed.

Lemma join_all_shift_locBlocksSrc :
    [predU (locBlocksSrc mu0) 
    & locBlocksSrc (join_all mu_trash [:: mu1 & mus])]
  = [predU (locBlocksSrc mu1)
    & locBlocksSrc (join_all mu_trash' mus)].
Proof.
rewrite join_all_shift_locBlocksSrcE /=.
by rewrite predUA predUC -predUA.
Qed.

Lemma join_all_shift_locBlocksTgtE :
  locBlocksTgt (join_all mu_trash' mus)
  = [predU (locBlocksTgt mu0)
    & locBlocksTgt (join_all mu_trash mus)].
Proof.
rewrite /= /predU; f_equal; extensionality b; rewrite /in_mem /= /in_mem /=.
case lOf0: (locBlocksTgt mu0)=> /=.
have H: locBlocksTgt (join_all mu_trash' mus) b.
{ rewrite join_all_locBlocksTgt; left; rewrite /mu_trash' /=.
  by apply/orP; rewrite /in_mem /=; left. }
by [].
have H: 
      is_true (locBlocksTgt (join_all mu_trash mus) b) 
  <-> is_true (locBlocksTgt (join_all mu_trash' mus) b).
{ by rewrite 2!join_all_locBlocksTgt /mu_trash' /= /in_mem /= lOf0. }
have H2: 
    locBlocksTgt (join_all mu_trash mus) b
  = locBlocksTgt (join_all mu_trash' mus) b.
{ move: H; case: (locBlocksTgt (join_all mu_trash mus) b).
  by case=> H1 H2; rewrite H1.
  case: (locBlocksTgt (join_all mu_trash' mus) b)=> //.
  by case=> //_; move/(_ erefl). }
by rewrite H2. 
Qed.

Lemma join_all_shift_locBlocksTgt :
    [predU (locBlocksTgt mu0) 
    & locBlocksTgt (join_all mu_trash [:: mu1 & mus])]
  = [predU (locBlocksTgt mu1)
    & locBlocksTgt (join_all mu_trash' mus)].
Proof.
rewrite join_all_shift_locBlocksTgtE /=.
by rewrite predUA predUC -predUA.
Qed.

Lemma join_all_shift_extBlocksSrcE :
  extBlocksSrc (join_all mu_trash' mus)
  = [predI (extBlocksSrc mu0)
    & extBlocksSrc (join_all mu_trash mus)].
Proof.
rewrite /= /predI; f_equal; extensionality b; rewrite /in_mem /= /in_mem /=.
case eOf0: (extBlocksSrc mu0)=> /=.
cut (extBlocksSrc (join_all mu_trash mus) b
 <-> extBlocksSrc (join_all mu_trash' mus) b).
case: (extBlocksSrc mu1 b)=> //.
case: (extBlocksSrc _ _)=> //.
case: (extBlocksSrc _ _)=> //.
case. by move/(_ erefl). case.
case: (extBlocksSrc _ _)=> //.
case: (extBlocksSrc _ _)=> //.
by move=> _; move/(_ erefl). 
by move=> _; move/(_ erefl).
case. 
case: (extBlocksSrc _ _)=> //.
case: (extBlocksSrc _ _)=> //.
by move/(_ erefl). 
case: (extBlocksSrc _ _)=> //.
case: (extBlocksSrc _ _)=> //.
by move=> _; move/(_ erefl). 
by move=> _; move/(_ erefl).
rewrite 2!join_all_extBlocksSrc.
have H: (extBlocksSrc mu_trash b = extBlocksSrc mu_trash' b).
{ by rewrite /mu_trash' /= /in_mem /= eOf0. }
by rewrite -H.
cut (false 
 <-> extBlocksSrc (join_all mu_trash' mus) b).
case: (extBlocksSrc _ _)=> //.
by case=> _; move/(_ erefl).
rewrite join_all_extBlocksSrc /mu_trash' /= /in_mem /= eOf0 /=.
by split=> //; last by case.
Qed.

Lemma join_all_shift_extBlocksSrc :
    [predI (extBlocksSrc mu0) 
    & extBlocksSrc (join_all mu_trash [:: mu1 & mus])]
  = [predI (extBlocksSrc mu1)
    & extBlocksSrc (join_all mu_trash' mus)].
Proof.
rewrite join_all_shift_extBlocksSrcE /=.
by rewrite predIA predIC -predIA.
Qed.

Lemma join_all_shift_frgnBlocksSrcE :
  frgnBlocksSrc (join_all mu_trash' mus)
  = [predI (frgnBlocksSrc mu0)
    & frgnBlocksSrc (join_all mu_trash mus)].
Proof.
rewrite /= /predI; f_equal; extensionality b; rewrite /in_mem /= /in_mem /=.
case eOf0: (frgnBlocksSrc mu0)=> /=.
cut (frgnBlocksSrc (join_all mu_trash mus) b
 <-> frgnBlocksSrc (join_all mu_trash' mus) b).
case: (frgnBlocksSrc mu1 b)=> //.
case: (frgnBlocksSrc _ _)=> //.
case: (frgnBlocksSrc _ _)=> //.
case. by move/(_ erefl). case.
case: (frgnBlocksSrc _ _)=> //.
case: (frgnBlocksSrc _ _)=> //.
by move=> _; move/(_ erefl). 
by move=> _; move/(_ erefl).
case. 
case: (frgnBlocksSrc _ _)=> //.
case: (frgnBlocksSrc _ _)=> //.
by move/(_ erefl). 
case: (frgnBlocksSrc _ _)=> //.
case: (frgnBlocksSrc _ _)=> //.
by move=> _; move/(_ erefl). 
by move=> _; move/(_ erefl).
rewrite 2!join_all_frgnBlocksSrc.
have H: (frgnBlocksSrc mu_trash b = frgnBlocksSrc mu_trash' b).
{ by rewrite /mu_trash' /= /in_mem /= eOf0. }
by rewrite -H.
cut (false 
 <-> frgnBlocksSrc (join_all mu_trash' mus) b).
case: (frgnBlocksSrc _ _)=> //.
by case=> _; move/(_ erefl).
rewrite join_all_frgnBlocksSrc /mu_trash' /= /in_mem /= eOf0 /=.
by split=> //; last by case.
Qed.

Lemma join_all_shift_extBlocksTgtE :
  extBlocksTgt (join_all mu_trash' mus)
  = [predI (extBlocksTgt mu0)
    & extBlocksTgt (join_all mu_trash mus)].
Proof.
rewrite /= /predI; f_equal; extensionality b; rewrite /in_mem /= /in_mem /=.
case eOf0: (extBlocksTgt mu0)=> /=.
cut (extBlocksTgt (join_all mu_trash mus) b
 <-> extBlocksTgt (join_all mu_trash' mus) b).
case: (extBlocksTgt mu1 b)=> //.
case: (extBlocksTgt _ _)=> //.
case: (extBlocksTgt _ _)=> //.
case. by move/(_ erefl). case.
case: (extBlocksTgt _ _)=> //.
case: (extBlocksTgt _ _)=> //.
by move=> _; move/(_ erefl). 
by move=> _; move/(_ erefl).
case. 
case: (extBlocksTgt _ _)=> //.
case: (extBlocksTgt _ _)=> //.
by move/(_ erefl). 
case: (extBlocksTgt _ _)=> //.
case: (extBlocksTgt _ _)=> //.
by move=> _; move/(_ erefl). 
by move=> _; move/(_ erefl).
rewrite 2!join_all_extBlocksTgt.
have H: (extBlocksTgt mu_trash b = extBlocksTgt mu_trash' b).
{ by rewrite /mu_trash' /= /in_mem /= eOf0. }
by rewrite -H.
cut (false 
 <-> extBlocksTgt (join_all mu_trash' mus) b).
case: (extBlocksTgt _ _)=> //.
by case=> _; move/(_ erefl).
rewrite join_all_extBlocksTgt /mu_trash' /= /in_mem /= eOf0 /=.
by split=> //; last by case.
Qed.

Lemma join_all_shift_extBlocksTgt :
    [predI (extBlocksTgt mu0) 
    & extBlocksTgt (join_all mu_trash [:: mu1 & mus])]
  = [predI (extBlocksTgt mu1)
    & extBlocksTgt (join_all mu_trash' mus)].
Proof.
rewrite join_all_shift_extBlocksTgtE /=.
by rewrite predIA predIC -predIA.
Qed.

Lemma join_all_shift_frgnBlocksTgtE :
  frgnBlocksTgt (join_all mu_trash' mus)
  = [predI (frgnBlocksTgt mu0)
    & frgnBlocksTgt (join_all mu_trash mus)].
Proof.
rewrite /= /predI; f_equal; extensionality b; rewrite /in_mem /= /in_mem /=.
case eOf0: (frgnBlocksTgt mu0)=> /=.
cut (frgnBlocksTgt (join_all mu_trash mus) b
 <-> frgnBlocksTgt (join_all mu_trash' mus) b).
case: (frgnBlocksTgt mu1 b)=> //.
case: (frgnBlocksTgt _ _)=> //.
case: (frgnBlocksTgt _ _)=> //.
case. by move/(_ erefl). case.
case: (frgnBlocksTgt _ _)=> //.
case: (frgnBlocksTgt _ _)=> //.
by move=> _; move/(_ erefl). 
by move=> _; move/(_ erefl).
case. 
case: (frgnBlocksTgt _ _)=> //.
case: (frgnBlocksTgt _ _)=> //.
by move/(_ erefl). 
case: (frgnBlocksTgt _ _)=> //.
case: (frgnBlocksTgt _ _)=> //.
by move=> _; move/(_ erefl). 
by move=> _; move/(_ erefl).
rewrite 2!join_all_frgnBlocksTgt.
have H: (frgnBlocksTgt mu_trash b = frgnBlocksTgt mu_trash' b).
{ by rewrite /mu_trash' /= /in_mem /= eOf0. }
by rewrite -H.
cut (false 
 <-> frgnBlocksTgt (join_all mu_trash' mus) b).
case: (frgnBlocksTgt _ _)=> //.
by case=> _; move/(_ erefl).
rewrite join_all_frgnBlocksTgt /mu_trash' /= /in_mem /= eOf0 /=.
by split=> //; last by case.
Qed.

Lemma join_all_shift_local_ofE :
  All (fun mu1 => DisjointLS mu0 mu1) [seq Inj.mu x | x <- mus] -> 
  local_of (join_all mu_trash' mus)
  = join (local_of mu0) (local_of (join_all mu_trash mus)).
Proof.
move=> D; elim: mus D=> // a mus' IH /= []D E.
rewrite IH // join_assoc (join_com (local_of a)).
by rewrite -join_assoc.
by rewrite disjoint_com; apply: DisjointLS_disjoint D.
Qed.

Lemma join_all_shift_local_of :
  AllDisjoint locBlocksSrc [seq Inj.mu x | x <- [:: mu_trash, mu0, mu1 & mus]] -> 
    join (local_of mu0) (local_of (join_all mu_trash [:: mu1 & mus]))
  = join (local_of mu1) (local_of (join_all mu_trash' mus)).
Proof.
move=> D; rewrite /join join_all_local_of=> //.
extensionality b.
case lOf0: (local_of mu0 b)=> [[x y]|].
case lOf1: (local_of mu1 b)=> [[x' y']|].
elimtype False; apply: (DisjointLS_local_of_contra lOf0 lOf1).
by case: D=> /= [][]H1 []H2 H3 [][]H4 H5 []H6 H7.
elim: mus D=> //=.
by rewrite /join lOf0.
move=> a mus' IH D; rewrite /join.
case lOfa: (local_of a b)=> [[x' y']|].
elimtype False; apply: (DisjointLS_local_of_contra lOf0 lOfa).
by case: D=> /= [][]H1 []H2 H3 [][]H4 []H5.
apply: IH.
case: D=> /= [][]H1 []H2 []H3 H4 [][]H5 []H6 H7 [][]H8 H9 []H10 H11.
by split.
rewrite /join.
case lOf1: (local_of mu1 b)=> [[x y]|].
case lOftr: (local_of mu_trash b)=> [[x' y']|].
elimtype False; apply: (DisjointLS_local_of_contra lOf1 lOftr).
by case: D=> /= [][]H1 []H2 H3 [][]H4 H5 []H6 H7; rewrite DisjointC.
elim: mus D=> //a mus' IH D /=; rewrite /join.
case lOfa: (local_of a b)=> [[x' y']|].
elimtype False; apply: (DisjointLS_local_of_contra lOf1 lOfa).
by case: D=> /= [][]H1 []H2 []H3 H4 [][]H5 []H6 H7 [][]H8 H9 []H10 H11.
apply: IH.
by case: D=> /= [][]H1 []H2 []H3 H4 [][]H5 []H6 H7 [][]H8 H9 []H10 H11.
case lOftr: (local_of mu_trash b)=> [[x y]|]. 
elim: mus D; first by move=> D /=; rewrite /join lOf0 lOftr.
move=> a mus' IH D /=; rewrite /join.
case lOfa: (local_of a b)=> [[x' y']|].
elimtype False; apply: (DisjointLS_local_of_contra lOftr lOfa).
by case: D=> /= [][]H1 []H2 []H3 H4 [][]H5 []H6 H7 [][]H8 H9 []H10 H11.
apply: IH.
by case: D=> /= [][]H1 []H2 []H3 H4 [][]H5 []H6 H7 [][]H8 H9 []H10 H11; split.
elim: mus D; first by rewrite /= /join lOf0 lOf1 lOftr.
move=> a mus' IH D /=; rewrite /join.
case: (local_of a b)=> //.
apply: IH.
by case: D=> /= [][]H1 []H2 []H3 H4 [][]H5 []H6 H7 [][]H8 H9 []H10 H11; split.
by case: D=> /= [][]H1 []H2 H3 [][]H4 H5 []H6 H7; split.
Qed.

Lemma join_all_shift_extern_ofE : 
  extern_of (join_all mu_trash' mus)
  = join2 (extern_of mu0) (extern_of (join_all mu_trash mus)).
Proof.
elim: mus=> // a mus' IH /=.
rewrite IH //.
by rewrite join2A (join2C (extern_of a)) -join2A.
Qed.

End join_all_shift.

Definition replace_externs' (mu : SM_Injection) (eSrc' eTgt' : block -> bool) :=
  match mu with
    | {| locBlocksSrc := locBSrc; locBlocksTgt := locBTgt; pubBlocksSrc := pSrc;
      pubBlocksTgt := pTgt; local_of := local; frgnBlocksSrc := frgnBSrc;
      frgnBlocksTgt := frgnBTgt; extern_of := extern |} =>
      {| locBlocksSrc := locBSrc;
         locBlocksTgt := locBTgt;
         pubBlocksSrc := pSrc;
         pubBlocksTgt := pTgt;
         local_of := local;
         extBlocksSrc := eSrc';
         extBlocksTgt := eTgt';
         frgnBlocksSrc := frgnBSrc;
         frgnBlocksTgt := frgnBTgt;
         extern_of := restrict extern eSrc' |}
  end.

Lemma replace_externs'_locBlocksSrc mu eSrc' eTgt' :
  locBlocksSrc (replace_externs' mu eSrc' eTgt')
  = locBlocksSrc mu.
Proof. by case: mu. Qed.

Lemma replace_externs'_locBlocksTgt mu eSrc' eTgt' :
  locBlocksTgt (replace_externs' mu eSrc' eTgt')
  = locBlocksTgt mu.
Proof. by case: mu. Qed.

Lemma replace_externs'_extBlocksSrc mu eSrc' eTgt' :
  extBlocksSrc (replace_externs' mu eSrc' eTgt')
  = eSrc'.
Proof. by case: mu. Qed.

Lemma replace_externs'_extBlocksTgt mu eSrc' eTgt' :
  extBlocksTgt (replace_externs' mu eSrc' eTgt')
  = eTgt'.
Proof. by case: mu. Qed.

Lemma replace_externs'_local_of mu eSrc' eTgt' :
  local_of (replace_externs' mu eSrc' eTgt')
  = local_of mu.
Proof. by case: mu. Qed.

Lemma replace_externs'_extern_of mu eSrc' eTgt' :
  extern_of (replace_externs' mu eSrc' eTgt')
  = restrict (extern_of mu) eSrc'.
Proof. by case: mu. Qed.

Lemma replace_externs'_wd (mu : Inj.t) eSrc' eTgt' : 
  (forall b, locBlocksSrc mu b = false \/ eSrc' b = false) -> 
  (forall b, locBlocksTgt mu b = false \/ eTgt' b = false) -> 
  (forall b, frgnBlocksSrc mu b -> eSrc' b) -> 
  (forall b, frgnBlocksTgt mu b -> eTgt' b) -> 
  SM_wd (replace_externs' mu eSrc' eTgt').
Proof.
move=> H1 H2 S1 S2; apply: Build_SM_wd.
rewrite replace_externs'_locBlocksSrc.
by rewrite replace_externs'_extBlocksSrc.
rewrite replace_externs'_locBlocksTgt.
by rewrite replace_externs'_extBlocksTgt.
rewrite replace_externs'_local_of.
move=> b1 b2 z lOf.
case: (Inj_wd mu)=> _ _ H3 _ _ _ _ _.
case: (H3 _ _ _ lOf).
rewrite replace_externs'_locBlocksSrc.
rewrite replace_externs'_locBlocksTgt.
by move=> ? ?; split.
rewrite replace_externs'_extern_of.
rewrite replace_externs'_extBlocksSrc.
rewrite replace_externs'_extBlocksTgt.
Abort. (*FIXME*)

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

Lemma inject_incr_empty j : inject_incr (fun _ => None) j.
Proof.
by move=> b b' ofs; discriminate.
Qed.

Import StructuredInjections.

Lemma sharedTgt_DomTgt (mu : Inj.t) :
  forall b, sharedTgt mu b -> DomTgt mu b.
Proof.
rewrite /sharedTgt /DomTgt=> b; move/orP; case.
by move/(frgnBlocksExternTgt _ (Inj_wd _) _)=> ->; apply/orP; right.
by move/(pubBlocksLocalTgt _ (Inj_wd _) _)=> ->; apply/orP; left.
Qed.

Section getBlocks_lems.

Context args1 args2 j (vinj : val_list_inject j args1 args2).

Lemma getBlocks_tail v vs b : 
  getBlocks vs b -> 
  getBlocks (v :: vs) b.
Proof.
by case: v=> //? ? ?; rewrite getBlocksD; apply/orP; right.  
Qed.

Lemma vals_def_getBlocksTS b' : 
  vals_def args1 -> 
  getBlocks args2 b' -> 
  exists b d', [/\ getBlocks args1 b & j b = Some (b',d')].
Proof.
move=> H1 H2.
elim: args2 args1 vinj H1 H2=> //.
move=> a2 args2' IH args1' vinj' H1 H2.
move: H2 vinj' H1; rewrite getBlocksD. 
case: args1'; first by move=> ?; inversion 1.
move=> a1 args1' /=; case: a2=> //.
move=> A; inversion 1; subst; move/andP=> []C D.
case: (IH _ H4 D A)=> x []y []? ?; exists x,y; split=> //.
by apply: getBlocks_tail.
move=> i A; inversion 1; subst; move/andP=> []C D.
case: (IH _ H4 D A)=> x []y []? ?; exists x,y; split=> //.
by apply: getBlocks_tail.
move=> i A; inversion 1; subst; move/andP=> []C D.
case: (IH _ H4 D A)=> x []y []? ?; exists x,y; split=> //.
by apply: getBlocks_tail.
move=> i A; inversion 1; subst; move/andP=> []C D.
case: (IH _ H4 D A)=> x []y []? ?; exists x,y; split=> //.
by apply: getBlocks_tail.
move=> b i; case/orP. 
move/Coqlib.proj_sumbool_true=> eq; subst b'.
inversion 1; subst; move/andP=> []H5 H6.
inversion H2; subst=> //.
exists b1,delta; split=> //.
rewrite getBlocksD; apply/orP; left.
by apply: Coqlib.proj_sumbool_is_true.
move=> A; inversion 1; subst; case/andP=> B C.
case: (IH _ H4 C A)=> x []y []? ?; exists x,y; split=> //.
by apply: getBlocks_tail.
Qed.

End getBlocks_lems.
