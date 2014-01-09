Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import sepcomp.StructuredInjections.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.sminj_lemmas.
Require Import sepcomp.mem_lemmas.

(** Domain Invariant: 
    ~~~~~~~~~~~~~~~~~

    The [dom_inv] invariant enforces disjointness conditions between
    the local, public and foreign block sets declared by [mu0], an
    [SM_injection] appearing at existentially quantified positions in
    the callstack invariant, and those declared by [mu], the
    [SM_injection] of the currently running core.  
*)

Record dominv mu0 mu : Type := 
  { dom_locdisj_src : [predI (locBlocksSrc mu0) & locBlocksSrc mu] =i pred0
  ; dom_pubfrgn_src : {subset [predI (frgnBlocksSrc mu) & locBlocksSrc mu0] 
                      <= pubBlocksSrc mu0}
  ; dom_locdisj_tgt : [predI (locBlocksTgt mu0) & locBlocksTgt mu] =i pred0
  ; dom_pubfrgn_tgt : forall b1 b2 d, 
                      foreign_of mu b1 = Some (b2, d) -> 
                      (b1 \in locBlocksSrc mu0) || (b2 \in locBlocksTgt mu0) -> 
                      pub_of mu0 b1 = Some (b2, d) }.                  

Definition dominv_opt mu0 (omu : option SM_Injection) :=
  if omu is Some mu then dominv mu0 mu else True.

Lemma dominv_restrict nu mu X : dominv nu mu -> dominv nu (restrict_sm mu X).
Proof.
case=> H H2 H3 H4; apply: Build_dominv. 
by rewrite restrict_sm_locBlocksSrc.
by rewrite restrict_sm_frgnBlocksSrc.
by rewrite restrict_sm_locBlocksTgt.
by rewrite restrict_sm_foreign; move=> b1 b2 d; move/restrict_some; apply: H4.
Qed.

(* I'm probably missing these in the ssreflect libraries ... *)

Section pred_lems.

Context {T} {pTy : predType T} (p q r : pTy).

Lemma predI0 : [predI p & pred0] =i pred0.
Proof. by rewrite/eq_mem/=/in_mem/=/andb=> x; case: (x \in p). Qed.

Lemma predIT : [predI predT & p] =i p.
Proof. by rewrite/eq_mem/=/in_mem/=/andb/in_mem => x. Qed.

Lemma predIC : [predI p & q] =i [predI q & p].
Proof. 
by rewrite/eq_mem/in_mem/=/andb=> x; case: (x \in p); case: (x \in q).
Qed.

Lemma in_predI b : b \in [predI p & q] = [&& b \in p & b \in q].
Proof. by rewrite/in_mem. Qed.

Lemma in_pred0 (b : T) : b \in pred0 = false.
Proof. by rewrite/pred0/in_mem. Qed.

Lemma eq_mem_trans : p =i q -> q =i r -> p =i r.
Proof. 
by rewrite/eq_mem/in_mem/= => H H2 x; rewrite -(H2 x) (H x). 
Qed.

End pred_lems.

Lemma dominv_relat_empty mu : dominv mu (reestablish SMInj.empty mu).
Proof.
apply: Build_dominv; case: mu=> //=.
by move=> s _ _ _ _ _ _ _ _ _; apply: predI0.
by move=> _ t _ _ _ _ _ _ _ _; apply: predI0. 
Qed.

Lemma dominv_intern_step (mu0 mu mu' : SMInj.t) m10 m20 m1 m2 :
  dominv mu0 mu -> 
  intern_incr mu mu' -> 
  mem_forward m10 m1 -> 
  mem_forward m20 m2 ->   
  sm_inject_separated mu0 mu m10 m20 -> 
  sm_inject_separated mu mu' m1 m2  -> 
  sm_valid mu0 m10 m20 -> 
  dominv mu0 mu'.
Proof.
move=> inv H2 H3 H4 H5 H6 Hvalid; case: H2.
move=> H7 []H8 []H9 []H10 []H11 []H12 []H13 []H14 []H15 H16.
apply: Build_dominv.
move=> b; case: H6=> []_ []; move/(_ b)=> H17 _; rewrite in_predI.
case A: (b \in locBlocksSrc mu).
by case: inv; move/(_ b); rewrite in_predI A; case (b \in locBlocksSrc mu0).
case B: (b \in locBlocksSrc mu'). 
rewrite/in_mem /= in A B; rewrite/DomSrc A B /= in H17.
have Q: extBlocksSrc mu b = false.
  move: (SMInj_wd mu')=> []; move/(_ b); rewrite B; case=> // D _ _ _ _ _ _ _.
  by rewrite -H15 in D.
have C: ~Memory.Mem.valid_block m1 b by apply: H17.
have D: ~Memory.Mem.valid_block m10 b by move=> C'; apply: C; case: (H3 b).
case E: (locBlocksSrc mu0 b). 
case: Hvalid=> []; move/(_ b); rewrite/DOM/DomSrc E /= => F _.
by elimtype False; apply: D; apply: F.
by rewrite/in_mem/= E.
by case: (b \in _).
by case: inv; rewrite -H13.
move=> b; case: H6=> []_ []; move=> _; move/(_ b)=> H17.
case A: (b \in locBlocksTgt mu). 
  + case: inv=> _ _; move/(_ b). 
    by rewrite !in_predI A; case (b \in locBlocksTgt mu0).
case B: (b \in locBlocksTgt mu'). 
rewrite/in_mem /= in A B; rewrite/DomTgt A B /= in H17.
have Q: extBlocksTgt mu b = false.
  move: (SMInj_wd mu')=> []; move=> _; move/(_ b). 
  by rewrite B; case=> // D _ _ _ _ _ _; rewrite -H16 in D.
have C: ~Memory.Mem.valid_block m2 b by apply: H17.
have D: ~Memory.Mem.valid_block m20 b by move=> C'; apply: C; case: (H4 b).
case E: (locBlocksTgt mu0 b). 
case: Hvalid=> [] _; move/(_ b); rewrite/RNG/DomTgt E /= => F.
by elimtype False; apply: D; apply: F.
by rewrite in_predI /in_mem /= E.
by rewrite in_predI B in_pred0; case: (b \in _).
case: inv; rewrite/foreign_of. 
generalize dependent mu; generalize dependent mu'.
case; case=> /= ? ? ? ? ? ? ? ? ? ? ?. 
case; case=> /= ? ? ? ? ? ? ? ? ? ? ?. 
by move=> ? ? ? -> ? ? ? ? ->. 
Qed.

(* The analogous lemma for extern_incr doesn't appear to hold: *)

Lemma dominv_extern_step (mu0 mu mu' : SMInj.t) m10 m20 m1 m2 :
  dominv mu0 mu -> 
  extern_incr mu mu' -> 
  mem_forward m10 m1 -> 
  mem_forward m20 m2 ->   
  sm_inject_separated mu0 mu m10 m20 -> 
  sm_inject_separated mu mu' m1 m2  -> 
  sm_valid mu0 m10 m20 -> 
  dominv mu0 mu'.
Proof.
move=> inv H2 H3 H4 H5 H6 Hvalid; case: H2.
move=> H7 []H8 []H9 []H10 []H11 []H12 []H13 []H14 []H15 H16.
apply: Build_dominv.
by rewrite -H11; apply: (dom_locdisj_src inv).
move=> b A; apply: (dom_pubfrgn_src inv). 
move: A; rewrite !in_predI; move/andP=> []. 
rewrite/in_mem /= => A B; apply/andP; split=> //.
admit. (*not true?*)
by rewrite -H12; apply: (dom_locdisj_tgt inv).
move=> b1 b2 d A B. 
case C: (foreign_of mu b1)=> [[b2' d']|].
have D: extern_of mu b1 = Some (b2', d') by apply: foreign_in_extern.
have E: extern_of mu' b1 = Some (b2, d)  by apply: foreign_in_extern.
move: (H7 _ _ _ D) B; rewrite E; case=> -> ->.
by apply: (dom_pubfrgn_tgt inv).
case D: (pub_of mu0 b1)=> [[b2' d']|]. admit. (*easy case*)
admit. (*not true?*)
Abort.
