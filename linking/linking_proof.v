(* standard Coq libraries *)

Require Import JMeq.

(* msl imports *)

Require Import msl.Axioms. (*for proof_irr*)

(* sepcomp imports *)

Require Import linking.sepcomp. Import SepComp. 
Require Import sepcomp.arguments.

Require Import linking.pos.
Require Import linking.stack.
Require Import linking.cast.
Require Import linking.pred_lemmas.
Require Import linking.seq_lemmas.
Require Import linking.wf_lemmas.
Require Import linking.reestablish.
Require Import linking.core_semantics_lemmas.
Require Import linking.inj_lemmas.
Require Import linking.join_sm.
Require Import linking.reach_lemmas.
Require Import linking.compcert_linking.
Require Import linking.compcert_linking_lemmas.
Require Import linking.disjointness.
Require Import linking.rc_semantics.
Require Import linking.rc_semantics_lemmas.
Require Import linking.linking_inv.
Require Import linking.call_lemmas.
Require Import linking.ret_lemmas.

(* compcert imports *)

Require Import compcert.common.AST.    (*for ident*)
Require Import compcert.common.Globalenvs.   
Require Import compcert.common.Memory.   

(* ssreflect *)

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import compcert.common.Values.   
Require Import sepcomp.nucular_semantics.

(* This file proves the main linking simulation result (see               *)
(* linking/linking_spec.v for the specification of the theorem that's     *)
(* proved).                                                               *)

Import Wholeprog_simulation.
Import SM_simulation.
Import Linker. 
Import Modsem.

Section linkingSimulation.

Variable N : pos.

Variable cores_S' cores_T : 'I_N -> Modsem.t. 

Variable nucular_T : forall i : 'I_N, Nuke_sem.t (cores_T i).(sem).

Variable fun_tbl : ident -> option 'I_N.

Variable sims' : forall i : 'I_N, 
  let s := cores_S' i in
  let t := cores_T i in
  SM_simulation_inject s.(sem) t.(sem) s.(ge) t.(ge).

Variable my_ge : ge_ty.
Variable my_ge_S : forall (i : 'I_N), genvs_domain_eq my_ge (cores_S' i).(ge).
Variable my_ge_T : forall (i : 'I_N), genvs_domain_eq my_ge (cores_T i).(ge).

Let types := fun i : 'I_N => (sims' i).(core_data).
Let ords : forall i : 'I_N, types i -> types i -> Prop 
  := fun i : 'I_N => (sims' i).(core_ord).

Let cores_S (ix : 'I_N) := 
  Modsem.mk (cores_S' ix).(ge) (RC.effsem (cores_S' ix).(sem)).

Let linker_S := effsem N cores_S fun_tbl.
Let linker_T := effsem N cores_T fun_tbl.

Let ord := @Lex.ord N types ords.

Notation cast'  pf x := (cast (C \o cores_T) pf x).
Notation cast'' pf x := (cast (C \o cores_T) (sym_eq pf) x).
Notation rc_cast'  pf x := (cast (RC.state \o C \o cores_T) pf x).
Notation rc_cast'' pf x := (cast (RC.state \o C \o cores_T) (sym_eq pf) x).

Notation R := (@R N cores_S' cores_T nucular_T sims' my_ge). 

Section halted_lems.

Context
(mu : Inj.t) m1 m2 rv1 
(st1 : linker N cores_S) cd st2  
(hlt1 : LinkerSem.halted st1 = Some rv1)
(inv : R cd mu st1 m1 st2 m2).

Lemma toplevel_hlt2 : exists rv2, LinkerSem.halted st2 = Some rv2.
Proof.
case: (R_inv inv)=> pf []mu_top []mus []mu_eq.
move=> []pf2 hdinv tlinv.
move: hlt1; rewrite /LinkerSem.halted. 
case inCtx1: (inContext st1)=> //=.
have inCtx2: ~~inContext st2.
{ case inCtx2: (inContext st2)=> //=.
  by move: (R_inContext' inv inCtx2); rewrite inCtx1. }
rewrite inCtx2.
case hlt0: (LinkerSem.halted0 st1)=> [rv1'|//]; case=> eq1.
by case: (hlt2 hlt0 inv)=> rv2 hlt2; exists rv2; rewrite hlt2.
Qed.

End halted_lems.

Require Import sepcomp.mem_wd.

(*TODO: move elsewhere*)
Lemma valid_genvs_domain_eq F1 F2 V1 V2 
    (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2) m :  
  genvs_domain_eq ge1 ge2 -> 
  valid_genv ge1 m -> 
  valid_genv ge2 m.
Proof.
move=> H1 []H2 H3; split.
move=> id b fnd. 
have isGlob: isGlobalBlock ge2 b.
{ rewrite /isGlobalBlock /=; apply/orP; left.
  by move: fnd; move/Genv.find_invert_symbol=> ->. }
move: (genvs_domain_eq_isGlobal _ _ H1)=> A; rewrite -A in isGlob.
have [[id' fnd']|[id' fnd']]: 
   (exists id, Genv.find_symbol ge1 id = Some b)
\/ (exists gv, Genv.find_var_info ge1 b = Some gv).
{ case: (orP isGlob)=> /=.
  case e: (Genv.invert_symbol _ _)=> [id'|//]=> _.
  by left; exists id'; apply: Genv.invert_find_symbol.
  by case e: (Genv.find_var_info _ _)=> [gv|//]=> _; right; exists gv. }
by apply: (H2 _ _ fnd').
by apply: (H3 _ _ fnd').
move=> gv b; case: H1=> _; move/(_ b)=> /= []A B C; case: B; first by exists gv.
by move=> x fnd; apply: (H3 _ _ fnd).
Qed.

Lemma link (main : val) : Wholeprog_simulation linker_S linker_T my_ge my_ge main.
Proof.
eapply Build_Wholeprog_simulation
  with (core_data   := sig_data N (fun ix : 'I_N => (sims sims' ix).(core_data)))
       (core_ord    := sig_ord (fun ix : 'I_N => (sims sims' ix).(core_ord)))
       (match_state := R).

(* well_founded ord *)
{ by apply: wf_sig_ord=> ix; case: (sims sims' ix). }

(* genvs_domain_eq *)
{ by apply: genvs_domain_eq_refl. }

{(* Case: [core_initial] *)
  move=> j c1 vals1 m1 vals2 m2 init1 inj vinj pres reach wd vgenv vval.
  move: init1. 
  rewrite /= /LinkerSem.initial_core.
  case e: main=> [//|//|//|//|b ofs].
  case f: (fun_tbl b)=> [ix|//].
  case g: (initCore _ _ _ _)=> [x|//].
  case h: (Integers.Int.eq _ _)=> //.
  case.
  move=> <-.
  case: x g=> ix1 c0 init1.

  set fS := (REACH m1 (fun b0 : block => 
    isGlobalBlock (ge (cores_S ix)) b0 || getBlocks vals1 b0)).
  set fT := (REACH m2 (fun b0 : block => 
    isGlobalBlock (ge (cores_T ix)) b0 || getBlocks vals2 b0)).

  set dS := (fun b : block => valid_block_dec m1 b).
  set dT := (fun b : block => valid_block_dec m2 b).

  exists (initial_SM dS dT fS fT j).

  Arguments core_initial : default implicits.

  move: init1; rewrite /initCore.
  case g: (core_semantics.initial_core _ _ _ _)=> [c|//].
  case=> eq1 H2. subst ix1.
  apply Eqdep_dec.inj_pair2_eq_dec in H2. subst c0.

  have valid_dec: forall m b, Mem.valid_block m b -> valid_block_dec m b.
  { by move=> m b0; rewrite /is_left; case l: (valid_block_dec m b0). }

  have valid_dec': forall m b, valid_block_dec m b -> Mem.valid_block m b.
  { by move=> m b0; rewrite /is_left; case l: (valid_block_dec m b0). }

  have main_eq: main = Vptr b Integers.Int.zero.
  { move: (Integers.Int.eq_spec ofs Integers.Int.zero).
    by rewrite e; move: h g=> /= -> h ->. }
    
  move: (core_initial (sims sims' ix))=> H1.
  move: (H1 main vals1 c m1 j vals2  m2 dS dT).
  case=> //.

  by rewrite main_eq.

  rewrite -meminj_preserves_genv2blocks.
  rewrite -(genvs_domain_eq_match_genvs (my_ge_S ix)).
  rewrite meminj_preserves_genv2blocks.
  by [].

  { rewrite /dS /dT /mapped=> ? ? ? eq; split.
    apply Mem.valid_block_inject_1 with (m1:=m1) (m2:=m2) in eq=> //.
    by apply: valid_dec.
    apply Mem.valid_block_inject_2 with (m1:=m1) (m2:=m2) in eq=> //. 
    by apply: valid_dec. }

  { move=> b0 R; suff: Mem.valid_block m2 b0.
    by apply: valid_dec.
    apply: reach; apply: (REACH_mono (fun b' : block =>
      isGlobalBlock (ge (cores_T ix)) b' || getBlocks vals2 b'))=> //.
    move=> b1; case/orP; first by rewrite -(isGlob_iffT my_ge_T)=> ->.
    by move=> ->; apply/orP; right. }

  { by apply: valid_dec'. }

  { by apply: valid_dec'. }

  move=> cd []c2 []init2 mtch12.

  exists (existT _ ix cd).
  exists (mkLinker fun_tbl (CallStack.singl (Core.mk _ _ ix c2))).
  
  split.

  rewrite /as_inj /join /=; extensionality b0.
  by case: (j b0)=> [[? ?]//|//].

  simpl in init2.

  rewrite -main_eq init2; split=> //.

  set mu_top0 := initial_SM dS dT fS fT j.

  have mu_top_wd : SM_wd mu_top0.
  { apply: initial_SM_wd=> //. 
    move=> b1 b2 d0 l; split.
    apply Mem.valid_block_inject_1 with (m1:=m1) (m2:=m2) in l=> //.
    by apply: valid_dec.
    apply Mem.valid_block_inject_2 with (m1:=m1) (m2:=m2) in l=> //.
    by apply: valid_dec.
    move=> b1; rewrite /fS; case l: (j b1)=> [[x y]|//].
    exists x,y; split=> //.
    rewrite /fT; set fT0 := (fun b0 : block =>
      isGlobalBlock (ge (cores_T ix)) b0 || getBlocks vals2 b0).
    move: H; move/REACH_inject; case/(_ _ _ inj fT0)=> b0.
    case/orP=> H2.
    move: pres; move/meminj_preserves_globals_isGlobalBlock.
    have H3: isGlobalBlock my_ge b0 
      by move: H2; rewrite -(isGlob_iffS my_ge_S).
    move/(_ b0 H3)=> J; exists b0,0; split=> //.
    by apply/orP; left; rewrite -(isGlob_iffT my_ge_T).
    case: (getBlocks_inject _ _ _ vinj _ H2)=> x' []y' []J X.
    by exists x',y'; split=> //; apply/orP; right.
    by case=> d []J H; rewrite l in J; case: J=> -> _.
    set fT0 := (fun b0 : block =>
      isGlobalBlock (ge (cores_T ix)) b0 || getBlocks vals2 b0).
    move/REACH_inject; case/(_ _ _ inj fT0)=> b0.
    case/orP=> H2.
    move: pres; move/meminj_preserves_globals_isGlobalBlock.
    have H3: isGlobalBlock my_ge b0 
      by move: H2; rewrite -(isGlob_iffS my_ge_S).
    move/(_ b0 H3)=> J; exists b0,0; split=> //.
    by apply/orP; left; rewrite -(isGlob_iffT my_ge_T).
    case: (getBlocks_inject _ _ _ vinj _ H2)=> x' []y' []J X.
    by exists x',y'; split=> //; apply/orP; right.
    by case=> d []J; rewrite J in l; discriminate.
    move=> b0 H.
    case: (REACH_inject _ _ _ inj 
      (fun b0 : block =>
        isGlobalBlock (ge (cores_S ix)) b0 || getBlocks vals1 b0)
      (fun b0 : block =>
        isGlobalBlock (ge (cores_T ix)) b0 || getBlocks vals2 b0) _ b0).
    move=> b1; case/orP=> H2.
    move: pres; move/meminj_preserves_globals_isGlobalBlock.
    have H3: isGlobalBlock my_ge b1 
      by move: H2; rewrite -(isGlob_iffS my_ge_S).
    move/(_ b1 H3)=> J; exists b1,0; split=> //.
    by apply/orP; left; rewrite -(isGlob_iffT my_ge_T).
    case: (getBlocks_inject _ _ _ vinj _ H2)=> x' []y' []J X.
    by exists x',y'; split=> //; apply/orP; right.
    by apply: (REACH_mono (fun b1 : block =>
      isGlobalBlock (ge (cores_S ix)) b1 || getBlocks vals1 b1)).
    move=> x []y []J _; apply: valid_dec.
    by apply Mem.valid_block_inject_1 with (m1:=m1) (m2:=m2) in J.
    move=> b0 F; apply: valid_dec; apply: reach.
    apply: (REACH_mono (fun b1 : block => 
      isGlobalBlock (ge (cores_T ix)) b1 || getBlocks vals2 b1))=> //.
    move=> b1; case/orP=> G. 
    by apply/orP; left; move: G; rewrite -(isGlob_iffT my_ge_T).
    by apply/orP; right. }

  set mu_top := Inj.mk mu_top_wd.
  
  have mu_top_val: sm_valid mu_top m1 m2.
  { split.
    by move=> b1; rewrite /DOM /DomSrc; case/orP=> //=; apply: valid_dec'.
    by move=> b2; rewrite /RNG /DomTgt; case/orP=> //=; apply: valid_dec'. }

  apply: Build_R=> /=.
  exists erefl,mu_top,[::]=> /=; split=> //.

  exists erefl; apply: Build_head_inv=> //.
  apply: Build_vis_inv; rewrite /= /RC.roots /vis /mu_top0 /= /fS.

  have ->: RC.args c = vals1.
  { by apply: (RC.initial_core_args g). }

  have ->: RC.rets c = [::].
  { by apply: (RC.initial_core_rets g). }

  have ->: RC.locs c = (fun _ => false).
  { by apply: (RC.initial_core_locs g). }

  move=> /=; rewrite /in_mem {2}/getBlocks /= => b1 H.
  suff [H2|H2]: isGlobalBlock my_ge b1 \/ getBlocks vals1 b1.
  by apply: REACH_nil; apply/orP; left; rewrite -(isGlob_iffS my_ge_S).
  by apply: REACH_nil; apply/orP; right.
  case: (orP H)=> //; case/orP=> //; case/orP; first by move=> ->; left.
  by move=> ->; right.

  have vgenv_ix: valid_genv (ge (cores_T ix)) m2.
  { by apply: (valid_genvs_domain_eq (my_ge_T ix) vgenv). }

  by apply: (Nuke_sem.wmd_initial _ vval vgenv_ix wd init2).
  by [].

  by move=> ix'; move: vgenv; apply: valid_genvs_domain_eq.

  by apply: ord_dec. 

  by case: (Integers.Int.eq _ _).
  by case: (Integers.Int.eq _ _). }(*END [Case: core_initial]*)
    
{(*[Case: diagram]*)
move=> st1 m1 st1' m1' U1 STEP data st2 mu m2 INV. 
case: STEP=> STEP STEP_EFFSTEP; case: STEP.

{(*[Subcase: corestep0]*)
move=> STEP. 
set c1 := peekCore st1.
set c2 := peekCore st2.

have [c1' [STEP0 [U1'_EQ [c1_args [c1_rets [c1_locs ST1']]]]]]:
   exists c1',
       Coresem.corestep 
         (t := effect_instance (sem (cores_S (Core.i c1)))) 
         (ge (cores_S (Core.i c1))) (Core.c c1) m1 c1' m1' 
   /\ (forall b ofs, U1 b ofs -> 
       RC.reach_set (ge (cores_S (Core.i c1))) (Core.c c1) m1 b)
   /\ RC.args (Core.c (c INV)) = RC.args c1'
   /\ RC.rets (Core.c (c INV)) = RC.rets c1'
   /\ RC.locs c1' 
      = (fun b => RC.locs (Core.c (c INV)) b || freshloc m1 m1' b 
               || RC.reach_set (ge (cores_S (Core.i c1))) (Core.c (c INV)) m1 b)
   /\ st1' = updCore st1 (Core.upd c1 c1').
  { move: (STEP_EFFSTEP STEP)=> EFFSTEP.
    move: STEP; rewrite/LinkerSem.corestep0=> [][]c1' []B C. 
    move: EFFSTEP; rewrite/effstep0.
    move=> []? []/=; rewrite/RC.effstep=> [][]EFFSTEP []u1 []args []rets locs D.
    exists c1'. split=> //. split=> //.
    by move: C D=> ->; move/updCore_inj_upd=> ->; split. }

have EFFSTEP: 
    effect_semantics.effstep 
    (sem (cores_S (Core.i c1)))
    (ge (cores_S (Core.i c1))) U1 (Core.c c1) m1 c1' m1'.
  { move: (STEP_EFFSTEP STEP); rewrite/effstep0=> [][] c1'' [] STEP0' ST1''. 
    by rewrite ST1'' in ST1'; rewrite -(updCore_inj_upd ST1'). }

(* specialize core diagram at module (Core.i c1) *)
move: (effcore_diagram _ _ _ _ (sims sims' (Core.i c1))).  
move/(_ _ _ _ _ _ EFFSTEP).
case: (R_inv INV)=> pf []mupkg []mus []mu_eq.
move=> []pf2 hdinv tlinv.

move: (head_match hdinv)=> MATCH.

have U1_DEF': forall b ofs, U1 b ofs -> vis mupkg b. 
{ move=> b ofs U; move: (U1'_EQ b ofs U)=> H.
  apply match_visible in MATCH; apply: MATCH.
  apply (REACH_mono (fun b => 
    b \in RC.roots (ge (cores_S (Core.i c1))) (Core.c c1)))=> //.
  move=> b0 roots; case: (head_vis hdinv); apply.
  have ->: Core.c (c INV) = Core.c c1.
  { by rewrite /c /c1 /peekCore /s1. }
  apply: (RC.roots_domains_eq 
    (ge1 := ge (cores_S (Core.i c1))) (ge2 := my_ge))=> //.
  by apply: genvs_domain_eq_sym; apply: my_ge_S. }

move/(_ _ _ _ _ U1_DEF' MATCH).
move=> []c2' []m2' []cd' []mu_top0.
move=> []INCR []SEP []LOCALLOC []MATCH' []U2 []STEP' PERM.

have fwd2: mem_forward m2 m2'.
{ case: STEP'=> step; first by apply effstep_plus_fwd in step.
  by case: step=> step0 step1; apply effstep_star_fwd in step0. }

have mu_top'_wd: SM_wd mu_top0 by move: MATCH'; apply: match_sm_wd.
set mu_top' := Inj.mk mu_top'_wd.
have mu_top'_valid: sm_valid mu_top' m1' m2'
  by apply: (match_validblocks _ MATCH').
set mupkg' := Build_frame_pkg mu_top'_valid.

(* instantiate existentials *)
set c2''   := cast' (peek_ieq INV) c2'.
set st2'   := updCore st2 (Core.upd c2 c2'').
set data'  := (existT (fun ix => core_data (sims sims' ix)) (Core.i c1) cd'). 
set mu'    := mu_top'.
exists st2', m2', data', mu'. 

have [n STEPN]: 
 exists n, effstepN (sem (cores_T (Core.i c2)))
   (ge (cores_T (Core.i c2))) n U2 (Core.c (d INV)) m2 c2'' m2'. 
 { set T := C \o cores_T.
   case: STEP'. case=> n step; exists (S n).
   set P := fun ix (x : T ix) (y : T ix) => 
             effstepN (sem (cores_T ix))
             (ge (cores_T ix)) (S n) U2 x m2 y m2'.
   change (P (Core.i c2) (Core.c c2) c2''); apply: cast_indnatdep2.
   by move: step; have ->: pf = peek_ieq INV by apply: proof_irr.
   case; case=> n step _; exists n.
   set P := fun ix (x : T ix) (y : T ix) => 
             effstepN (sem (cores_T ix))
             (ge (cores_T ix)) n U2 x m2 y m2'.
   change (P (Core.i c2) (Core.c c2) c2''); apply: cast_indnatdep2.
   by move: step; have ->: pf = peek_ieq INV by apply: proof_irr. }

split. 

{(* Label: [re-establish invariant] *) 
 apply: Build_R. rewrite ST1'; rewrite /st2'.

 exists pf,mupkg',mus; split=> //.

 (* head_inv *)
 { case: tlinv=> allrel frameall.
   exists erefl=> /=.
   have rcvis: REACH_closed m1' (vis mu').
   { by apply match_visible in MATCH'; apply: MATCH'. }
   apply (@head_inv_step _ _ _ _ sims' my_ge my_ge_S 
     mupkg m1 m2 mu_top' m1' m2' fwd2 (head_valid hdinv) INCR SEP LOCALLOC rcvis
     (c INV) (d INV) pf c1' c2'' _ _ mus
     (STACK.pop (CallStack.callStack (s1 INV))) 
     (STACK.pop (CallStack.callStack (s2 INV))) U1 n U2 hdinv frameall)=> //=.
   by apply: (R_ge INV).
   by have ->: cast'' pf c2'' = c2' by apply: cast_cast_eq'. }

 (* tail_inv *)
 { eapply tail_inv_step with (Esrc := U1) (Etgt := U2) (mu' := mu_top'); eauto.
   by apply: (effstep_unchanged _ _ _ _ _ _ _ EFFSTEP).
   by move: STEPN; apply: effect_semantics.effstepN_unchanged.
   by move: (effax1 EFFSTEP)=> []; move/corestep_fwd.
   move=> ? ? X; move: (PERM _ _ X)=> []Y Z; split=> //.
   by eapply effstepN_valid in STEPN; eauto.
   by apply: (head_valid hdinv).
   by apply match_visible in MATCH'; apply: MATCH'.
   by apply: (head_rel hdinv). } 

 (* fn_tbl *)
 { by rewrite ST1' (R_fntbl INV). } 

 (* valid_genv *)
 { move=> ix; move: (R_ge INV); move/(_ ix)=> vgenv. 
   by apply: (Nuke_sem.valid_genv_fwd vgenv). }
 } (*end [re-establish invariant]*)
 
 {(* Label: [matching execution] *) 
 have EFFECTS_REFINEMENT: 
     forall b ofs, U2 b ofs = true ->
     visTgt mu b = true /\
     (locBlocksTgt mu b = false ->
       exists b1 d1, 
         foreign_of mu b1 = Some (b, d1) /\
         U1 b1 (ofs - d1) = true /\
         Mem.perm m1 b1 (ofs - d1) Max Nonempty).
 { move=> b ofs X; move: (PERM _ _ X)=> []H Y; split.
   by move: H; rewrite mu_eq. 
   by rewrite mu_eq. }

exists U2; split=> //; case: STEP'=> STEP'.

have STEP'': 
  effstep_plus (sem (cores_T (Core.i c2)))
  (ge (cores_T (Core.i c2))) U2 (Core.c (d INV)) m2 c2'' m2'. 
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) (y : T ix) => 
             effstep_plus (sem (cores_T ix))
             (ge (cores_T ix)) U2 x m2 y m2'.
   change (P (Core.i c2) (Core.c c2) c2''); apply: cast_indnatdep2.
   by move: STEP'; have ->: pf = peek_ieq INV by apply: proof_irr. }
by left; move: STEP''; apply: stepPLUS_STEPPLUS.

have STEP'': 
  effstep_star (sem (cores_T (Core.i c2)))
  (ge (cores_T (Core.i c2))) U2 (Core.c c2) m2 c2'' m2'. 
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) (y : T ix) => 
             effstep_star (sem (cores_T ix))
             (ge (cores_T ix)) U2 x m2 y m2'.
   change (P (Core.i c2) (Core.c c2) c2''); apply: cast_indnatdep2.
   by case: STEP'; have ->: pf = peek_ieq INV by apply: proof_irr; by []. }
right; split; first by move: STEP''; apply: stepSTAR_STEPSTAR.
rewrite /sig_ord /data' /=.

have eq: Core.i c1 = projT1 data.
{ by clear - pf2; move: pf2; rewrite /c /s1 /c1 /peekCore /= => ->. }

exists eq; case: STEP'=> STEP' ORD.
have <-: pf2 = sym_eq eq by apply: proof_irr.
by apply: ORD. } (*end [Label: matching execution]*)
} (*end [Subcase: corestep0]*)

move=> []<- []NSTEP.
case AT1: (LinkerSem.at_external0 st1)=> [[[ef1 sig1] args1]|].

{(*[Subcase: at_external0]*)
case FID: (LinkerSem.fun_id ef1)=> [id|//].
case HDL: (LinkerSem.handle _)=> [st1''|//] eq1 A.
have wd: SM_wd mu by apply: (R_wd INV).
have INV': R data (Inj.mk wd) st1 m1 st2 m2 by [].
case: (atext2 AT1 INV')=> args2 AT2.
case: (hdl2 my_ge_S my_ge_T AT1 HDL INV' AT2)=> cd' []st2' []mu' []HDL2 INV2.
exists st2',m2,cd',mu'; split=> //; first by rewrite eq1.
set (empty_U := fun (_ : block) (_ : Z) => false); exists empty_U; split=> //.
left; exists O=> /=; exists st2',m2,empty_U,empty_U; split=> //.
constructor=> //. 
right; split=> //; split=> //.
by move/LinkerSem.corestep_not_at_external0; rewrite AT2.
by rewrite AT2 FID HDL2.
by move/LinkerSem.corestep_not_at_external0; rewrite AT2.
}(*end [Subcase: at_external0]*)

case CTXT: (inContext st1)=> //.
case HLT1: (LinkerSem.halted0 st1)=> [rv|].

{(*[Subcase: halted0]*)
case POP1: (popCore st1)=> [st1''|//].
case AFT1: (LinkerSem.after_external (Some rv) st1'')=> [st1'''|//] eq1 A.

have mu_wd: SM_wd mu. 
{ by apply: (R_wd INV). }

have INV': R data (Inj.mk mu_wd) st1 m1 st2 m2.
{ by apply: INV. }

case: (aft2 my_ge_S HLT1 POP1 AFT1 INV')=> 
  rv2 []st2'' []st2' []cd' []mu' []HLT2 CTX2 POP2 AFT2 INV''.
exists st2',m2,cd',mu'.
split=> //; first by rewrite eq1.
exists (fun _ _ => false); split=> //.
left; exists O=> /=; exists st2',m2,(fun _ _ => false),(fun _ _ => false).
split=> //.
rewrite /effstep; split=> //.
rewrite /LinkerSem.corestep; right; split=> //.
have nStep: ~LinkerSem.corestep0 st2 m2 st2' m2.
{ case=> x []step st2'_eq; apply corestep_not_halted in step.
  by move: step HLT2; rewrite /LinkerSem.halted0 /= /RC.halted=> ->. }
split=> //. 
rewrite CTX2.
have atExt2: (LinkerSem.at_external0 st2 = None).
{ case: (LinkerSem.at_external_halted_excl0 st2)=> //.
  by rewrite HLT2. }
by rewrite atExt2 HLT2 POP2 AFT2.
move: HLT2; rewrite /LinkerSem.halted0 /LinkerSem.corestep0.
move=> HLT2' []c' []; move=> STEP _.
apply corestep_not_halted in STEP.
by move: STEP HLT2'=> /=; rewrite/RC.halted=> ->.
}(*end [Subcase: halted0]*)

by [].

} (*end [Case: diagram]*)

{(*Case: halted*)
move=> cd mu c1 m1 c2 m2 v1 inv hlt1.
have mu_wd: SM_wd mu by apply: R_wd inv.
have inv': R cd (Inj.mk mu_wd) c1 m1 c2 m2 by [].
case: (toplevel_hlt2 hlt1 inv')=> v2 hlt2.
case: (R_inv inv')=> pf []mupkg []mus []mu_eq.
move=> []pf2 hdinv tlinv; move: (head_match hdinv)=> mtch0.

have hlt10: 
  halted (sem (cores_S (Core.i (c inv')))) (Core.c (c inv)) 
= Some v1.
{ move: hlt1; rewrite /= /LinkerSem.halted.
  case inCtx1: (inContext c1)=> //=.
  case hlt10: (LinkerSem.halted0 c1)=> [v1'|//]; case=> <-.
  by move: hlt10; rewrite /LinkerSem.halted0 /c /= /RC.halted=> ->. }

case: (core_halted (sims sims' (Core.i (c inv'))) _ _ _ _ _ _ mtch0 hlt10).
move=> v2' []inj []vinj hlt2'.

exists (as_inj mupkg),v2'; split.

rewrite -meminj_preserves_genv2blocks.
rewrite (genvs_domain_eq_match_genvs (my_ge_S (Core.i (c inv')))).
rewrite meminj_preserves_genv2blocks.
case: (match_genv mtch0)=> ext isGlob_frgn.
rewrite match_genv_meminj_preserves_extern_iff_all=> //.
by apply: Inj_wd.
split; first by apply: (val_inject_restrictD _ _ _ _ vinj).
split; first by [].
rewrite /= hlt2.
move: hlt2; rewrite /LinkerSem.halted.
case e: (~~ inContext c2)=> //.
case f: (LinkerSem.halted0 c2)=> [rv|//]; case=> <-.
rewrite /LinkerSem.halted0 /= /RC.halted in f hlt2'.
have g: halted (sem (cores_T (Core.i (c inv'))))
               (cast'' pf (Core.c (d inv')))  
      = Some rv.
{ set T := C \o cores_T.
  set P := fun ix (x : T ix) => 
             halted (sem (cores_T ix)) x  
           = Some rv.
  change (P (Core.i (c inv')) (cast T (sym_eq pf) (Core.c (d inv')))).
  by apply: cast_indnatdep; rewrite /P; rewrite -f. }
by rewrite -g. }(*END Case: halted*)

Qed.

End linkingSimulation.

Print Assumptions link.

Require Import linking.linking_spec.

Module LinkingSimulation : LINKING_SIMULATION.

Lemma link : 
  forall (N : pos) (sems_S sems_T : 'I_N -> t),
  (forall ix : 'I_N, Nuke_sem.t (sem (sems_T ix))) ->
  forall (plt : ident -> option 'I_N)
    (sims : forall ix : 'I_N,
            let s := sems_S ix in
            let t := sems_T ix in
            SM_simulation_inject (sem s) (sem t) (ge s) (ge t))
    (ge_top : ge_ty),
  (forall ix : 'I_N, genvs_domain_eq ge_top (ge (sems_S ix))) ->
  (forall ix : 'I_N, genvs_domain_eq ge_top (ge (sems_T ix))) ->
  let sems_S0 :=
    fun ix : 'I_N =>
    {|
    F := F (sems_S ix);
    V := V (sems_S ix);
    ge := ge (sems_S ix);
    C := RC.state (C (sems_S ix));
    sem := RC.effsem (sem (sems_S ix)) |} in
  let linker_S := effsem N sems_S0 plt in
  let linker_T := effsem N sems_T plt in
  forall main : val, Wholeprog_simulation linker_S linker_T ge_top ge_top main.
Proof. by move=> *; apply: link. Qed.

End LinkingSimulation.
