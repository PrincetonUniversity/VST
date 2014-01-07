(* standard Coq libraries *)

Require Import JMeq.

(* msl imports *)

Require Import msl.Axioms. (*for proof_irr*)

(* sepcomp imports *)

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.StructuredInjections.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.effect_properties.
Require Import sepcomp.pos.
Require Import sepcomp.stack.
Require Import sepcomp.cast.
Require Import sepcomp.wf_lemmas.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.linking.
Require Import sepcomp.linking_lemmas.

(* ssreflect *)

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.

(* compcert imports *)

Require Import compcert.common.AST.    (*for ident*)
Require Import compcert.common.Values.   
Require Import compcert.common.Globalenvs.   
Require Import compcert.common.Memory.   

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Linking simulation proof 

This file states and proves the main linking simulation result.

*)

Section linkingSimulation.

Import SM_simulation.
Import Linker.
Import Static.

Arguments core_data {F1 V1 C1 F2 V2 C2 Sem1 Sem2 ge1 ge2} _ _.
Arguments core_ord  {F1 V1 C1 F2 V2 C2 Sem1 Sem2 ge1 ge2 entry_points} _ _ _.
Arguments match_state {F1 V1 C1 F2 V2 C2 Sem1 Sem2 ge1 ge2 entry_points} 
  _ _ _ _ _ _ _.

Variable N : pos.
Variable (cores_S cores_T : 'I_N -> Static.t). 
Variable fun_tbl : ident -> option 'I_N.
Variable entry_points : seq (val*val*signature).
Variable (sims : forall i : 'I_N, 
  let s := cores_S i in
  let t := cores_T i in
  SM_simulation_inject s.(coreSem) t.(coreSem) s.(ge) t.(ge) entry_points).
Variable my_ge : ge_ty.
Variable my_ge_S : forall (i : 'I_N), genvs_domain_eq my_ge (cores_S i).(ge).
Variable my_ge_T : forall (i : 'I_N), genvs_domain_eq my_ge (cores_T i).(ge).

Let types := fun i : 'I_N => (sims i).(core_data entry_points).
Let ords : forall i : 'I_N, types i -> types i -> Prop 
  := fun i : 'I_N => (sims i).(core_ord).

Variable wf_ords : forall i : 'I_N, well_founded (@ords i).

Let linker_S := effsem N cores_S fun_tbl.
Let linker_T := effsem N cores_T fun_tbl.

Let ord := @Lex.ord N types ords.

Notation cast' pf x := (cast (C \o cores_T) pf x).

Notation cast pf x := (cast (C \o cores_T) (sym_eq pf) x).

(** These lemmas on [restrict_sm] should go elsewhere. *)

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

(** Domain Invariant: 
    ~~~~~~~~~~~~~~~~~

    The [dom_inv] invariant enforces disjointness conditions between
    the local, public and foreign block sets declared by [mu0], an
    [SM_injection] appearing at existentially quantified positions in
    the callstack invariant, and those declared by [mu], the
    [SM_injection] of the currently running core.  
*)

Record dom_inv mu0 mu : Type := 
  { dom_locdisj_src : [predI (locBlocksSrc mu0) & locBlocksSrc mu] =i pred0
  ; dom_pubfrgn_src : pubBlocksSrc mu0 
                      =i [predI (frgnBlocksSrc mu) & locBlocksSrc mu0] 
  ; dom_locdisj_tgt : pred0 [predI (locBlocksTgt mu0) & locBlocksTgt mu] 
  ; dom_pubfrgn_tgt : forall b1 b2 d, 
                      foreign_of mu b1 = Some (b2, d) -> 
                      (b1 \in locBlocksSrc mu0) || (b2 \in locBlocksTgt mu0) -> 
                      pub_of mu0 b1 = Some (b2, d) }.                  

Definition dom_inv_opt mu0 (omu : option SM_Injection) :=
  if omu is Some mu then dom_inv mu0 mu else True.

Lemma dom_inv_restrict nu mu X : dom_inv nu mu -> dom_inv nu (restrict_sm mu X).
Proof.
case=> H H2 H3 H4; apply: Build_dom_inv. 
by rewrite restrict_sm_locBlocksSrc.
by rewrite restrict_sm_frgnBlocksSrc.
by rewrite restrict_sm_locBlocksTgt.
by rewrite restrict_sm_foreign; move=> b1 b2 d; move/restrict_some; apply: H4.
Qed.

Section frame_inv.

Import Core.

Variables (c : t cores_S) (d : t cores_T). 
Variable  pf : c.(i)=d.(i).

Require Import compcert.lib.Coqlib. (*for Forall2*)

(** Frame Invariant: 
    ~~~~~~~~~~~~~~~~

   The frame invariant applies to cores in caller positions in the
   call stack.  I.e, to cores that are waiting [at_external] for the
   environment to return. Main arguments are:

   * Existentially quantified when [frame_inv] is applied:
   -[mu0]: [SM_injection] at point of external call

   -[nu0]: [SM_injection] derived from [mu0] by restricting [pubSrc]
   and [pubTgt] to reachable local blocks.  [nu0] is used primarily to
   state the [unchOn] invariants assumable by THIS core.

   -[m10], [m20]: Source and target memories active at call point. 

   * True parameters: 
   -[mu]: The [SM_injection] of the currently running core (/not/ this
    one).  Things to note:

     + Resuming a core:
     ~~~~~~~~~~~~~~~~~~

     When we resume a core, we do not use [mu] directly.  Instead, we
     employ the derived [SM_injection]:
       mu' := { local_of  := local_of mu0
              ; extern_of := extern_of mu0 
                             + {extern_of mu | REACH m1' m2' ret1 ret2}
              ; ... }
     This [SM_injection] satisfies [extern_incr mu0 mu'], among other
     properties required by the [after_external] clause of structured
     simulations.


     + The [frame_dom] invariant [dom_inv mu0 mu]: 
     ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

     [mu0] is always disjoint, in the way specified by [dom_inv], 
     from the active injection [mu].  This is to ensure that we can 
     re-establish over steps of the active core the [frame_unch1] 
     and [frame_unch2] invariants given below (which in turn are 
     required by [after_external]).
     
     In order to re-establish [dom_inv] when a core returns to its
     context, we track as an additional invariant that [dom_inv mu0
     mu_head], where [mu_head] is the existentially quantified
     injection of the callee.

   -[m1], [m2]: Active memories. 
*)

Record frame_inv cd0 mu0 mu_head mu 
                 m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2 : Prop :=
  { (* local definitions *)
    pubSrc := [predI (locBlocksSrc mu0) & REACH m10 (exportedSrc mu0 vals1)] 
  ; pubTgt := [predI (locBlocksTgt mu0) & REACH m20 (exportedTgt mu0 vals2)] 
  ; nu0    := replace_locals mu0 pubSrc pubTgt

    (* invariants required to instantiate at_external *)
  ; frame_inj0  : Mem.inject (as_inj mu0) m10 m20
  ; frame_inj   : Mem.inject (as_inj mu0) m1 m2
  ; frame_match : (sims c.(i)).(match_state) cd0 mu0 
                    c.(Core.c) m10 (cast pf d.(Core.c)) m20 
  ; frame_at1   : at_external (cores_S c.(i)).(coreSem) c.(Core.c) 
                    = Some (e1, ef_sig1, vals1) 
  ; frame_at2   : at_external (cores_T c.(i)).(coreSem) (cast pf d.(Core.c)) 
                    = Some (e2, ef_sig2, vals2) 
  ; frame_vinj  : Forall2 (val_inject (as_inj mu0)) vals1 vals2  
  ; frame_fwd1  : mem_forward m10 m1
  ; frame_fwd2  : mem_forward m20 m2
  ; frame_dom1  : dom_inv mu0 mu
  ; frame_dom2  : dom_inv_opt mu0 mu_head
  ; frame_unch1 : Mem.unchanged_on [fun b ofs => 
                    [/\ locBlocksSrc nu0 b & pubBlocksSrc nu0 b=false]] m10 m1
  ; frame_unch2 : Mem.unchanged_on (local_out_of_reach nu0 m10) m20 m2 
  ; frame_sep   : StructuredInjections.sm_inject_separated nu0 mu m10 m20 }.

End frame_inv.

Section head_inv.

Import Core.

Variables (c : t cores_S) (d : t cores_T). 
Variable  (pf : c.(i)=d.(i)).

Record head_inv cd mu m1 m2 : Type :=
  { head_match : (sims c.(i)).(match_state) cd mu 
                 c.(Core.c) m1 (cast pf d.(Core.c)) m2 }.

End head_inv.

Section head_inv_lems.

Context c d pf cd mu m1 m2 (inv : @head_inv c d pf cd mu m1 m2).

Lemma head_inv_restrict (X : block -> bool) : 
  (forall b : block, vis mu b -> X b) -> 
  REACH_closed m1 X -> 
  @head_inv c d pf cd (restrict_sm mu X) m1 m2.
Proof.
case: inv=> H H2 H3; apply: Build_head_inv.
by apply: (match_restrict _ _ _ _ _ (sims (Core.i c))).
Qed.

End head_inv_lems.

Fixpoint tail_inv_aux mu_head mu
  (s1 : Stack.t (Core.t cores_S)) (s2 : Stack.t (Core.t cores_T)) m1 m2 :=
  match s1, s2 with
    | c :: s1', d :: s2' => 
      exists mu0,
      [/\ exists (pf : c.(Core.i)=d.(Core.i)) cd0,
          exists m10 e1 ef_sig1 vals1,
          exists m20 e2 ef_sig2 vals2, 
          @frame_inv c d pf cd0 mu0 mu_head mu 
                     m10 m1 e1 ef_sig1 vals1 m20 m2 e2 ef_sig2 vals2
       & tail_inv_aux (Some mu0) mu s1' s2' m1 m2]
    | _, _ => False
  end.

Notation tail_inv := (tail_inv_aux None).

Section tail_inv_lems.

Context mu_head mu s1 s2 m1 m2 (inv : tail_inv_aux mu_head mu s1 s2 m1 m2).

Lemma tail_len_eq : length s1 = length s2.
Proof.
move: s2 mu_head mu inv; elim: s1=> // a s1' IH /= s0 mu_head' mu'. 
case: s0=> // b s2' [] /= mu0 []? H2.
by rewrite (IH _ _ _ H2).
Qed.

Lemma tail_inv_restrict (X : block -> bool) : 
  (forall b : block, vis mu b -> X b) -> 
  REACH_closed m1 X -> 
  tail_inv_aux mu_head (restrict_sm mu X) s1 s2 m1 m2.
Proof.
move=> H H2; move: s2 tail_len_eq mu_head mu inv; elim: s1=> // a s1' IH s0. 
case: s0=> // b s2' H3.
have H4: length s1' = length s2' by move: H3=> /=; case.
move=> mu_head' mu' /= [] mu0 []H5 H6; exists mu0; split; last by apply: IH.
move: H5=> [pf][cd][m10][e1][sig1][vals1][m20][e2][sig2][vals2][].
exists pf, cd, m10, e1, sig1, vals1, m20, e2, sig2, vals2. 
apply: Build_frame_inv=> //; last by apply: sm_inject_separated_restrict.
by apply: dom_inv_restrict.
Qed.

(*
Lemma tail_inv_step mu0 mu' m1' m2' : tail_inv_aux (Some mu0) mu' s1 s2 m1' m2'.
Proof.
move: mu0 mu_head inv.
elim: s1 s2=> // a s1' IH s2' mu0 mu_head0.
case: s2'=> //= b s2'.
move=> []mu00 [][]eq_ab []data0 []m10 []e1 []sig1 []vals1. 
move=> []m20 []e2 []sig2 []vals2 FRM_INV TL_INV.
exists mu00. 
split; last by apply: (IH _ mu00 (Some mu00)).
exists eq_ab, data0, m10, e1, sig1, vals1.
exists m20, e2, sig2, vals2.
case: FRM_INV=> ?? ?? ?? ?? ?? ?? ?? ??.
apply: Build_frame_inv=> //.
*)

End tail_inv_lems.

Section R.

Import CallStack.
Import Linker.

Record R (data : Lex.t types) mu 
         (x1 : linker N cores_S) m1 (x2 : linker N cores_T) m2 := 
  { (* local defns. *)
    s1  := x1.(stack) 
  ; s2  := x2.(stack) 
  ; pf1 := CallStack.callStack_nonempty s1 
  ; pf2 := CallStack.callStack_nonempty s2 
  ; c   := stack.head _ pf1 
  ; d   := stack.head _ pf2 
    (* invariants *)
  ; R_head : exists (pf : c.(Core.i)=d.(Core.i)) cd, @head_inv c d pf cd mu m1 m2 
  ; R_tail : tail_inv mu (pop s1.(callStack)) (pop s2.(callStack)) m1 m2 }.

End R.

Section R_lems.

Context data mu x1 m1 x2 m2 (pf : R data mu x1 m1 x2 m2).

Import CallStack.
Import Linker.

Lemma peek_ieq : Core.i (peekCore x1) = Core.i (peekCore x2).
Proof. by move: (R_head pf)=> []A []cd=> _; apply: A. Qed.

Lemma peek_match :
  exists cd, 
  match_state (sims (Core.i (peekCore x1))) cd mu 
  (Core.c (peekCore x1)) m1 
  (cast peek_ieq (Core.c (peekCore x2))) m2.
Proof.
move: (R_head pf)=> []A []cd; move/head_match=> MATCH.
have ->: (cast peek_ieq (Core.c (peekCore x2)) = cast A (Core.c (peekCore x2)))
  by f_equal; f_equal; apply proof_irr.
by exists cd.
Qed.

Lemma R_wd : SM_wd mu.
Proof. 
move: (R_head pf)=> [A][B]; move/head_match.
by apply: (match_sm_wd _ _ _ _ _ (sims (Core.i (c pf)))).
Qed.

Lemma R_pres_globs : Events.meminj_preserves_globals my_ge (extern_of mu).
Proof. 
move: (R_head pf)=> [A][B]; move/head_match=> H. 
move: (match_genv _ _ _ _ _ (sims (Core.i (c pf))) _ _ _ _ _ _ H)=> []H2 H3.
rewrite -meminj_preserves_genv2blocks.
rewrite (genvs_domain_eq_preserves _ _ 
        (extern_of mu) (my_ge_S (Core.i (c pf)))).
rewrite meminj_preserves_genv2blocks.
by apply: H2.
Qed.

Lemma R_match_genv :
  Events.meminj_preserves_globals my_ge (extern_of mu) /\
  forall b : block, isGlobalBlock my_ge b -> frgnBlocksSrc mu b.
Proof.
move: (R_head pf)=> [A][B]; move/head_match=> H.
split; first by apply: R_pres_globs.
rewrite (genvs_domain_eq_isGlobal _ _ (my_ge_S (Core.i (c pf)))).
by move: (match_genv _ _ _ _ _ (sims (Core.i (c pf))) _ _ _ _ _ _ H)=> [] _.
Qed.

Lemma R_match_visible : REACH_closed m1 (vis mu).
move: (R_head pf)=> [A][B]; move/head_match=> H. 
by apply: (@match_visible _ _ _ _ _ _ _ _ _ _ _ 
          (sims (Core.i (c pf))) _ _ _ _ _ _ H).
Qed.

Lemma R_match_restrict (X : block -> bool) : 
  (forall b : block, vis mu b -> X b) -> REACH_closed m1 X -> 
  R data (restrict_sm mu X) x1 m1 x2 m2.
Proof.
move: (R_head pf)=> [A][B]; move/head_inv_restrict=> H H2 H3. 
move: (H _ H2 H3)=> H'; apply: Build_R; first by exists A, B; apply: H'. 
by apply: tail_inv_restrict=> //; apply: (R_tail pf). 
Qed.

Lemma R_match_validblocks : sm_valid mu m1 m2.
Proof. 
move: (R_head pf)=> [A][B]; move/head_match. 
by apply: match_validblocks. 
Qed.

End R_lems.

Lemma link : SM_simulation_inject linker_S linker_T my_ge my_ge entry_points.
Proof.

eapply Build_SM_simulation_inject
  with (core_data   := Lex.t types)
       (core_ord    := ord)
       (match_state := R).

(* well_founded ord *)
- by apply: Lex.wf_ord.

(* match -> SM_wd mu *)
- by apply: R_wd. 

(* genvs_domain_eq *)
- by apply: genvs_domain_eq_refl.

(* match_genv *)
- by move=> data mu c1 m1 c2 m2; apply: R_match_genv.

(* match_visible *)
- by apply: R_match_visible.

(* match_restrict *)
- by move=> data mu c1 m1 c2 m2 X H; apply: (R_match_restrict H).

(* match_validblocks *)
- by move=> ??; apply: R_match_validblocks.

(* core_initial *)
- by admit. (* TODO *)

(* NOT NEEDED diagram1 *)
- by admit.
(* NOT NEEDED diagram2 *)
- by admit.
(* NOT NEEDED diagram3 *)
- by admit.

(* real diagram *)
- move=> st1 m1 st1' m1' U1 STEP data st2 mu m2 U1_DEF INV.
case: STEP=> STEP STEP_EFFSTEP.
case: STEP.
 (* Case: corestep0 *)
 + move=> STEP. 
(*
 have [c A]: exists c, peekCore st1 = Some c. 
  { move: STEP; rewrite/Sem.corestep0; case: (peekCore st1)=> // a. 
    by exists a. }
*)
 set c1 := peekCore st1.
 have [c1' [STEP0 ST1']]: 
         exists c' : C (cores_S (Core.i c1)), 
         Coresem.corestep 
            (t := Effectsem.instance (coreSem (cores_S (Core.i c1)))) 
            (ge (cores_S (Core.i c1))) (Core.c c1) m1 c' m1' 
         /\ st1' = updCore st1 (Core.upd c1 c').
  { by move: STEP; rewrite/Sem.corestep0=> [][]c' []B C; exists c'; split. }

 have EFFSTEP: 
        effect_semantics.effstep (coreSem (cores_S (Core.i c1))) 
        (ge (cores_S (Core.i c1))) U1 (Core.c c1) m1 c1' m1'.
  { move: (STEP_EFFSTEP STEP); rewrite/effstep0=> [][] c1'' [] STEP0' ST1''.
    by rewrite ST1'' in ST1'; rewrite -(updCore_inj_upd ST1'). }

 (* specialize core diagram at module (Core.i c1) *)
 move: (effcore_diagram_strong_perm _ _ _ _ _ (sims (Core.i c1))).  
 move/(_ _ _ _ _ _ EFFSTEP).
 move/(_ _ _ _ _ U1_DEF).
 move: (peek_match INV)=> []cd MATCH.
 move/(_ _ _ _ MATCH).
 move=> []c2' []m2' []cd' []mu'.
 move=> []INCR []SEP []LOCALLOC []MATCH' []U2 []STEP' PERM.

 (* instantiate existentials *)
 set c2''  := cast' (peek_ieq INV) c2'.
 set st2'  := updCore st2 (Core.upd (peekCore st2) c2'').
 set data' := Lex.set (Core.i c1) cd' data.
 exists st2', m2', data', mu'; do 4 split=> //.

 (* re-establish invariant *)
 apply: Build_R; rewrite ST1'; rewrite /st2' /=.

 (* head_inv *)
 + exists (peek_ieq INV), cd'; apply: Build_head_inv. 
   have ->: cast (peek_ieq INV) (cast' (peek_ieq INV) c2') = c2' 
     by apply: cast_cast_eq.
   by apply: MATCH'. 

 (* tail_inv *)
 + move: (R_tail INV); rewrite/s1/s2/st2'; generalize dependent st1.
   case=> ?; case; case=> //; case=> ai a l1 pf1. 
   case: st2=> ?; case; case=> //; case=> bi b l2 pf2 /= INV A B c1' D EQ.
   move: EQ A B D=> -> /= STEP_EFFSTEP STEP0.
   move=> STEP EFFSTEP cd MATCH c2' cd' MATCH' STEP_ORD. 
   admit. (*hole: tail_inv lemma*)

 (* matching execution *)
 + exists U2; split=> //; case: STEP'=> STEP'. 
   left; apply: stepPLUS_STEPPLUS=> //.
   set T := C \o cores_T.
   set P := fun ix (x : T ix) (y : T ix) => 
               effect_semantics.effstep_plus 
               (coreSem (cores_T ix)) (ge (cores_T ix)) U2 x m2 y m2'.
   set c2 := peekCore st2.
   change (P (Core.i c2) (Core.c c2) (cast.cast T (peek_ieq INV) c2')).
   by apply: cast_indnatdep2.
   admit. (* TODO: ord case *) 

Admitted. (*WORK-IN-PROGRESS*)

End linkingSimulation.


