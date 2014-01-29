Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import msl.Axioms.

Require Import compcert.common.Memory.
Require Import ZArith.

Require Import sepcomp.StructuredInjections.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.rg_lemmas.
Require Import sepcomp.mem_lemmas.

Require Import sepcomp.sminj_lemmas.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.pred_lemmas.

(** Domain Invariant: 
    ~~~~~~~~~~~~~~~~~

    The [dominv] invariant enforces disjointness conditions between
    the local, public and foreign block sets declared by [mu0], an
    [SM_injection] appearing at existentially quantified positions in
    the callstack invariant, and those declared by [mu], the
    [SM_injection] of the currently running core.  
*)

Record disjinv mu0 mu : Type := 
  { disj_locsrc : Disjoint (locBlocksSrc mu0) (locBlocksSrc mu)
  ; disj_pubfrgnsrc : {subset [predI (frgnBlocksSrc mu) & locBlocksSrc mu0] 
                      <= pubBlocksSrc mu0}
  ; disj_loctgt : Disjoint (locBlocksTgt mu0) (locBlocksTgt mu)
  ; disj_pubfrgntgt : forall b1 b2 d, 
                      foreign_of mu b1 = Some (b2, d) -> 
                      (b1 \in locBlocksSrc mu0) || (b2 \in locBlocksTgt mu0) -> 
                      pub_of mu0 b1 = Some (b2, d) }.

Record relinv mu0 mu : Type := 
  { rel_src      : {subset (DomSrc mu0) <= DomSrc mu}
  ; rel_tgt      : {subset (DomTgt mu0) <= DomTgt mu}
  ; rel_restrict : restrict (as_inj mu) (DomSrc mu0) = as_inj mu0 
  ; rel_sep      : forall b1 b2 d, 
                   (as_inj mu0) b1 = None -> (as_inj mu) b1 = Some (b2, d) -> 
                   [/\ DomSrc mu0 b1 = false & DomTgt mu0 b2 = false] }.

Definition dominv mu0 mu := [/\ disjinv mu0 mu & relinv mu0 mu].

Lemma disjinv_restrict mu0 mu X : 
  disjinv mu0 mu -> disjinv (restrict_sm mu0 X) (restrict_sm mu X).
Proof.
case=> H H2 H3 H4; apply: Build_disjinv. 
by rewrite !restrict_sm_locBlocksSrc.
by rewrite restrict_sm_frgnBlocksSrc restrict_sm_pubBlocksSrc 
           restrict_sm_locBlocksSrc.
by rewrite !restrict_sm_locBlocksTgt.
rewrite !restrict_sm_foreign=> b1 b2 d. 
rewrite !restrict_sm_pub; rewrite/restrict; case: (X b1)=> //.
by rewrite restrict_sm_locBlocksSrc restrict_sm_locBlocksTgt; apply: H4.
Qed.

Lemma disjinv_restrict' mu0 mu X : 
  disjinv mu0 mu -> disjinv mu0 (restrict_sm mu X).
Proof.
case=> H H2 H3 H4; apply: Build_disjinv. 
by rewrite !restrict_sm_locBlocksSrc.
by rewrite restrict_sm_frgnBlocksSrc.
by rewrite !restrict_sm_locBlocksTgt.
rewrite !restrict_sm_foreign=> b1 b2 d. 
rewrite/restrict; case: (X b1)=> //.
by apply: H4.
Qed.

Lemma relinv_restrict mu0 mu X : 
  relinv mu0 mu -> relinv (restrict_sm mu0 X) (restrict_sm mu X).
Proof.
case=> H H2 H3 H4; apply: Build_relinv. 
by rewrite !restrict_sm_DomSrc.
by rewrite !restrict_sm_DomTgt.
by rewrite !restrict_sm_all restrict_sm_DomSrc; rewrite -H3 restrict_com.
move=> b1 b2 d; rewrite !restrict_sm_all restrict_sm_DomSrc restrict_sm_DomTgt.
by rewrite/restrict; case: (X b1)=> //; apply: H4.
Qed.

Lemma dominv_restrict mu0 mu X : 
  dominv mu0 mu -> dominv (restrict_sm mu0 X) (restrict_sm mu X).
Proof.
case=> A B; split; first by apply: disjinv_restrict. 
by apply: relinv_restrict.
Qed.

Lemma disjinv_relat_empty mu : disjinv mu (reestablish SMInj.empty mu).
Proof.
apply: Build_disjinv; case: mu=> //=.
by move=> s _ _ _ _ _ _ _ _ _; apply: predI01.
by move=> _ t _ _ _ _ _ _ _ _; apply: predI01. 
Qed.

Lemma disjinv_call_aux mu0 mu S T :
  {subset (pubBlocksSrc mu0) <= S} -> 
  {subset (pubBlocksTgt mu0) <= T} -> 
  disjinv mu0 mu -> disjinv (replace_locals mu0 S T) mu.
Proof.
move=> H1 H2; case: mu0 H1 H2=> a b c d e a' b' c' d' e' /= H1 H2.
case=> /= A B C D; apply: Build_disjinv=> //=.
by apply: (subset_trans' _ H1).
move=> b1 b2 d2 H3 H4; move: (D _ _ _ H3 H4); case E: (c b1)=> // H5.
by have ->: (S b1) by apply: H1.
Qed.

Lemma disjinv_call (mu0 : SMInj.t) mu m10 m20 vals1 vals2 :
  let: pubSrc := [predI (locBlocksSrc mu0) & REACH m10 (exportedSrc mu0 vals1)] in
  let: pubTgt := [predI (locBlocksTgt mu0) & REACH m20 (exportedTgt mu0 vals2)] in
  let: nu0    := replace_locals mu0 pubSrc pubTgt in
  disjinv mu0 mu -> disjinv nu0 mu.
Proof.
apply: disjinv_call_aux; first by apply: pubBlocksLocReachSrc.
by apply: pubBlocksLocReachTgt.
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

Lemma disjinv_intern_step mu0 (mu mu' : SMInj.t) m10 m20 m1 m2 :
  disjinv mu0 mu -> 
  intern_incr mu mu' -> 
  mem_forward m10 m1 -> 
  mem_forward m20 m2 ->   
  sm_inject_separated mu0 mu m10 m20 -> 
  sm_inject_separated mu mu' m1 m2  -> 
  sm_valid mu0 m10 m20 -> 
  sm_valid mu m1 m2 -> 
  disjinv mu0 mu'.
Proof.
move=> inv INCR H3 H4 H5 H6 VAL VAL'.
apply: Build_disjinv. 
+ have A: Disjoint (locBlocksSrc mu0) (locBlocksSrc mu) by case: inv.
  have B: Disjoint (locBlocksSrc mu0) [pred b | ~~ validblock m1 b].
    apply: smvalid_locsrc_disjoint. 
    by apply: (smvalid_src_fwd H3 (sm_valid_smvalid_src _ _ _ VAL)). 
  have C: {subset [predD (locBlocksSrc mu') & locBlocksSrc mu]
          <= [pred b | ~~ validblock m1 b]}.
    by apply: (sminjsep_locsrc INCR VAL').
  have D: Disjoint (locBlocksSrc mu0) 
                   [predD (locBlocksSrc mu') & locBlocksSrc mu].
    by apply: (Disjoint_sub1 B C).
  by apply: (Disjoint_incr A D).
+ have A: [predI (frgnBlocksSrc mu') & locBlocksSrc mu0]
          = [predI (frgnBlocksSrc mu) & locBlocksSrc mu0].
    by rewrite (intern_incr_frgnsrc INCR).  
  by rewrite A; case: inv.
+ have A: Disjoint (locBlocksTgt mu0) (locBlocksTgt mu) by case: inv.
  have B: Disjoint (locBlocksTgt mu0) [pred b | ~~ validblock m2 b].
    apply: smvalid_loctgt_disjoint. 
    by apply: (smvalid_tgt_fwd H4 (sm_valid_smvalid_tgt _ _ _ VAL)). 
  have C: {subset [predD (locBlocksTgt mu') & locBlocksTgt mu]
          <= [pred b | ~~ validblock m2 b]}.
    by apply: (sminjsep_loctgt INCR VAL').
  have D: Disjoint (locBlocksTgt mu0) 
                   [predD (locBlocksTgt mu') & locBlocksTgt mu].
    by apply: (Disjoint_sub1 B C).
  by apply: (Disjoint_incr A D).
+ case: inv; rewrite/foreign_of. 
  generalize dependent mu; generalize dependent mu'.
  case; case=> /= ? ? ? ? ? ? ? ? ? ? ?. 
  case; case=> /= ? ? ? ? ? ? ? ? ? ? ? incr.
  move: (intern_incr_frgnsrc incr) (intern_incr_frgntgt incr)=> /= -> ->.
  by move: (intern_incr_extern incr)=> /= ->.
Qed.

Lemma disjinv_unchanged_on_src 
  mu0 mu (E : Values.block -> BinNums.Z -> bool) m m' (val : smvalid_src mu0 m) :
  (forall b ofs, E b ofs -> Mem.valid_block m b -> vis mu b) -> 
  Memory.Mem.unchanged_on (fun b ofs => E b ofs = false) m m' -> 
  disjinv mu0 mu -> 
  Memory.Mem.unchanged_on (fun b => 
    [fun _ => locBlocksSrc mu0 b=true /\ pubBlocksSrc mu0 b=false]) m m'.
Proof.
move=> A B; case=> C D _ _; apply: (RGSrc_multicore mu E m m' A B mu0)=> //.
move: C; rewrite DisjointInE=> C.
move=> b F; move: (C b); rewrite/in_mem /=; move/andP=> G.
case H: (locBlocksSrc mu b)=> //; rewrite/in_mem /= H in G; elimtype False.
by apply: G; split.
Qed.

Lemma disjinv_unchanged_on_tgt
  (mu0 mu : SMInj.t) (Esrc Etgt : Values.block -> BinNums.Z -> bool)
  m1 m1' m2 m2' (fwd : mem_forward m1 m1') (valid : smvalid_src mu0 m1) :
  (forall (b : Values.block) (ofs : Z),
    Etgt b ofs = true ->
    Mem.valid_block m2 b /\
    (locBlocksTgt mu b = false ->
      exists (b1 : Values.block) (delta1 : Z),
        foreign_of mu b1 = Some (b, delta1) /\
        Esrc b1 (ofs - delta1)%Z = true /\
        Mem.perm m1' b1 (ofs - delta1) Max Nonempty)) -> 
  Mem.unchanged_on (fun b ofs => Etgt b ofs = false) m2 m2' -> 
  disjinv mu0 mu -> 
  Memory.Mem.unchanged_on (local_out_of_reach mu0 m1) m2 m2'.
Proof.
move=> A B; case=> _ _ D E.
apply: (mem_lemmas.unchanged_on_validblock _ _ _ 
         (local_out_of_reach mu0 m1'))=> //.
move=> b ofs val []F G; split=> // b' d' H; case: (G _ _ H)=> I.
left=> J; apply: I; case: (fwd b')=> //. 
apply: (valid b'); apply/orP; left. 
by case: (local_DomRng mu0 (SMInj_wd mu0) _ _ _ H).
by move=> _; apply.
by right.
apply: (RGTgt_multicorePerm mu Etgt Esrc m2 m2' (SMInj_wd mu) m1' A B). 
move: D; rewrite DisjointInE=> D.
move=> b F; move: (D b); rewrite/in_mem /=; move/andP=> G.
case H: (locBlocksTgt mu b)=> //; rewrite/in_mem /= H in G; elimtype False.
by apply: G; split.
by apply: E.
Qed.

Lemma relinv_intern_step mu0 (mu mu' : SMInj.t) m10 m20 m1 m2 :
  relinv mu0 mu -> 
  intern_incr mu mu' -> 
  mem_forward m10 m1 -> 
  mem_forward m20 m2 ->   
  sm_inject_separated mu0 mu m10 m20 -> 
  sm_inject_separated mu mu' m1 m2  -> 
  sm_valid mu0 m10 m20 -> 
  relinv mu0 mu'.
Proof.
move=> inv H2 H3 H4 H5 H6 Hvalid; case: H2.
move=> H7 []H8 []H9 []H10 []H11 []H12 []H13 []H14 []H15 H16.
apply: Build_relinv.
move=> b A; move: {A}(rel_src inv A).
rewrite/DomSrc /in_mem /=; move/orP; case=> A; apply/orP. 
by left; apply: H9. 
by right; rewrite -H15.
move=> b A; move: {A}(rel_tgt inv A).
rewrite/DomTgt /in_mem /=; move/orP; case=> A; apply/orP.
by left; apply: H10. by right; rewrite -H16.
rewrite -(rel_restrict inv) /restrict.
extensionality b; case DOM: (DomSrc _ _)=> //; rewrite/as_inj /join -H8.
case E: (extern_of mu b)=> //.
case A: (local_of mu b)=> [[b' d']|].
by move: (H7 _ _ _ A).
case B: (local_of mu' b)=> // [[b' d']]; case: H6; move/(_ b b' d').
rewrite/as_inj/join E; move/(_ A); rewrite -H8 E; move/(_ B)=> [C D] [].
move/(_ b C).
have F: DomSrc mu' b. 
  by rewrite/DomSrc; move: (local_locBlocks _ (SMInj_wd mu') _ _ _ B)=> []->.
move/(_ F)=> G _.
have H: Memory.Mem.valid_block m10 b.
  by case: Hvalid; move/(_ b)=> H _; apply: H.
by elimtype False; apply: G; case: (H3 b).
move=> b1 b2 d A B.
move: (@rel_sep _ _ inv b1 b2 d A).
case C: (as_inj mu b1)=> [[b1' d']|].
move: C B; rewrite/as_inj/join -H8.
case B: (extern_of mu b1)=> [[b1'' d'']|].
by case=> <- <-; case=> <- <-; case.
move=> C D.
move: (H7 _ _ _ C).
by rewrite D; case=> <- <-; case.
move=> _.
have M: ~Memory.Mem.valid_block m10 b1.
  have N: ~Memory.Mem.valid_block m1 b1.
    case: H6; move/(_ b1 b2 d C B); case=> D E.
    case: (as_inj_DomRng _ _ _ _ B (SMInj_wd mu'))=> O ?.
    by case; move/(_ b1 D O).
  by move=> M; apply: N; case: (H3 b1 M). 
have N: ~Memory.Mem.valid_block m20 b2.
  have P: ~Memory.Mem.valid_block m2 b2.
    case: H6; move/(_ b1 b2 d C B); case=> D E.
    case: (as_inj_DomRng _ _ _ _ B (SMInj_wd mu'))=> ? O.
    by case=> _; move/(_ b2 E O).
  by move=> Q; apply: P; case: (H4 b2 Q). 
case: Hvalid. move/(_ b1)=> E. move/(_ b2)=> F; split.
case G: (DomSrc mu0 b1)=> //.
by elimtype False; apply: M; apply: (E G).
case G: (DomTgt mu0 b2)=> //.
by elimtype False; apply: N; apply: (F G).
Qed.

Lemma dominv_intern_step mu0 (mu mu' : SMInj.t) m10 m20 m1 m2 :
  dominv mu0 mu -> 
  intern_incr mu mu' -> 
  mem_forward m10 m1 -> 
  mem_forward m20 m2 ->   
  sm_inject_separated mu0 mu m10 m20 -> 
  sm_inject_separated mu mu' m1 m2  -> 
  sm_valid mu0 m10 m20 -> 
  sm_valid mu m1 m2 -> 
  dominv mu0 mu'.
Proof.
case=> A B C D E F G H I.
split; first by apply: (disjinv_intern_step A C D E F G H I).
by apply: (relinv_intern_step B C D E F G H).
Qed.

(* The analogous lemma for extern_incr doesn't appear to hold: *)

(* Lemma disjinv_extern_step (mu0 mu mu' : SMInj.t) m10 m20 m1 m2 : *)
(*   disjinv mu0 mu ->  *)
(*   extern_incr mu mu' ->  *)
(*   mem_forward m10 m1 ->  *)
(*   mem_forward m20 m2 ->    *)
(*   sm_inject_separated mu0 mu m10 m20 ->  *)
(*   sm_inject_separated mu mu' m1 m2  ->  *)
(*   sm_valid mu0 m10 m20 ->  *)
(*   disjinv mu0 mu'. *)
(* Proof. *)
(* move=> inv H2 H3 H4 H5 H6 Hvalid; case: H2. *)
(* move=> H7 []H8 []H9 []H10 []H11 []H12 []H13 []H14 []H15 H16. *)
(* apply: Build_disjinv. *)
(* by rewrite -H11; apply: (disj_locsrc inv). *)
(* move=> b A; apply: (disj_pubfrgnsrc inv).  *)
(* move: A; rewrite !in_predI; move/andP=> [].  *)
(* rewrite/in_mem /= => A B; apply/andP; split=> //. *)
(* admit. (*not true?*) *)
(* by rewrite -H12; apply: (disj_loctgt inv). *)
(* move=> b1 b2 d A B.  *)
(* case C: (foreign_of mu b1)=> [[b2' d']|]. *)
(* have D: extern_of mu b1 = Some (b2', d') by apply: foreign_in_extern. *)
(* have E: extern_of mu' b1 = Some (b2, d)  by apply: foreign_in_extern. *)
(* move: (H7 _ _ _ D) B; rewrite E; case=> -> ->. *)
(* by apply: (disj_pubfrgntgt inv). *)
(* case D: (pub_of mu0 b1)=> [[b2' d']|]. admit. (*easy case*) *)
(* admit. (*not true?*) *)
(* Abort. *)
