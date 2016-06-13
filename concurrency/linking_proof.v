(* standard Coq libraries *)

Require Import JMeq.

(* msl imports *)

Require Import Axioms. (*for proof_irr*)

(* sepcomp imports *)

Require Import sepcomp. Import SepComp. 
Require Import arguments.

Require Import pos.
Require Import stack.
Require Import cast.
Require Import pred_lemmas.
Require Import seq_lemmas.
Require Import wf_lemmas.
Require Import reestablish.
Require Import inj_lemmas.
Require Import join_sm.
Require Import reach_lemmas.
Require Import compcert_linking.
Require Import compcert_linking_lemmas.
Require Import disjointness.
Require Import rc_semantics.
Require Import rc_semantics_lemmas.
Require Import linking_inv.
Require Import call_lemmas.
Require Import ret_lemmas.

(* compcert imports *)

Require Import AST.    (*for ident*)
Require Import Globalenvs.   
Require Import Memory.   

(* ssreflect *)

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Values.   
Require Import nucular_semantics.

(** * Linking Proof (Theorem 2) *)

(** This file proves the main linking simulation result (see
  linking/linking_spec.v for the specification of the theorem). *)

Import Wholeprog_sim.
Import SM_simulation.
Import Linker. 
Import Modsem.

Section linkingSimulation.

Variable N : pos.

Variable cores_S cores_T : 'I_N -> Modsem.t. 

Variable find_symbol_ST : 
  forall (i : 'I_N) id bf, 
  Genv.find_symbol (ge (cores_S i)) id = Some bf -> 
  Genv.find_symbol (ge (cores_T i)) id = Some bf.

Variable rclosed_S : forall i : 'I_N, RCSem.t (cores_S i).(sem) (cores_S i).(ge).
Variable nucular_T : forall i : 'I_N, Nuke_sem.t (cores_T i).(sem).

Variable fun_tbl : ident -> option 'I_N.

Variable sims : forall i : 'I_N, 
  let s := cores_S i in
  let t := cores_T i in
  SM_simulation_inject s.(sem) t.(sem) s.(ge) t.(ge).

Variable my_ge : ge_ty.
Variable my_ge_S : forall (i : 'I_N), genvs_domain_eq my_ge (cores_S i).(ge).
Variable my_ge_T : forall (i : 'I_N), genvs_domain_eq my_ge (cores_T i).(ge).

(*Four new assumptions*)
Variable find_symbol_up_S: forall i id b,
    Genv.find_symbol (cores_S i).(ge) id = Some b ->
    Genv.find_symbol my_ge id = Some b.

Variable find_symbol_up_T: forall i id b,
    Genv.find_symbol (cores_T i).(ge) id = Some b ->
    Genv.find_symbol my_ge id = Some b.

Variable all_gvars_includedS: forall i b,
     gvars_included (Genv.find_var_info (cores_S i).(ge) b) (Genv.find_var_info my_ge b).

Variable all_gvars_includedT: forall i b,
     gvars_included (Genv.find_var_info (cores_T i).(ge) b) (Genv.find_var_info my_ge b).  

Let types := fun i : 'I_N => (sims i).(core_data).
Let ords : forall i : 'I_N, types i -> types i -> Prop 
  := fun i : 'I_N => (sims i).(core_ord).

Let linker_S := effsem N cores_S fun_tbl.
Let linker_T := effsem N cores_T fun_tbl.

Let ord := @Lex.ord N types ords.

Notation cast'  pf x := (cast (C \o cores_T) pf x).
Notation cast'' pf x := (cast (C \o cores_T) (sym_eq pf) x).
Notation rc_cast'  pf x := (cast (RC.state \o C \o cores_T) pf x).
Notation rc_cast'' pf x := (cast (RC.state \o C \o cores_T) (sym_eq pf) x).

Notation R := (@R N cores_S cores_T rclosed_S nucular_T sims my_ge). 

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

Require Import mem_welldefined.

(*TODO: move elsewhere*)
Lemma valid_genvs_domain_eq F1 F2 V1 V2 
    (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2) m :  
  genvs_domain_eq ge1 ge2 -> 
  valid_genv ge1 m -> 
  valid_genv ge2 m.
Proof.
move=> H1 []H2 H3; constructor=> b isGlob. 
move: (genvs_domain_eq_isGlobal _ _ H1)=> A; rewrite -A in isGlob.
by apply (H2 _ isGlob).
case: H1=> _ []_; case/(_ b)=> X Y Z; case: Y; first by exists isGlob.
by move=> x FND; apply: (H3 _ _ FND).
Qed.

(** ** Proof of Theorem 2 *)

Lemma link (main : val) : CompCert_wholeprog_sim linker_S linker_T my_ge my_ge main.
Proof.
eapply Build_Wholeprog_sim
  with (core_data   := sig_data N (fun ix : 'I_N => (sims ix).(core_data)))
       (core_ord    := sig_ord (fun ix : 'I_N => (sims ix).(core_ord)))
       (match_state := R).

(** well_founded ord *)
{ by apply: wf_sig_ord=> ix; case: (sims ix). }

(** genvs_domain_eq *)
{ by apply: genvs_domain_eq_refl. }

{(** Case: [core_initial] *)
  move=> j c1 vals1 m1 vals2 m2 init1.
  case=>inj []vinj []pres []gfi []wd []vgenv []vval []ro1 ro2.
  move: init1. 
  rewrite /= /LinkerSem.initial_core.
  case e: main=> [//|//|//|//|b ofs].
  case h: (Integers.Int.eq _ _)=> //.
  case i: (Genv.invert_symbol _ _)=> // [id].
  case f: (fun_tbl id)=> [ix|//].
  case g: (initCore _ _ _ _)=> [x|//].
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

  move: init1 g; rewrite /initCore.
  case g: (semantics.initial_core _ _ _ _)=> [c|//].
  move=> sig1; case=> eq1 H2. subst ix1.
  apply Eqdep_dec.inj_pair2_eq_dec in H2. subst c0.

  have valid_dec: forall m b, Mem.valid_block m b -> valid_block_dec m b.
  { by move=> m b0; rewrite /is_left; case l: (valid_block_dec m b0). }

  have valid_dec': forall m b, valid_block_dec m b -> Mem.valid_block m b.
  { by move=> m b0; rewrite /is_left; case l: (valid_block_dec m b0). }

  have main_eq: main = Vptr b Integers.Int.zero.
  { move: (Integers.Int.eq_spec ofs Integers.Int.zero).
    by rewrite e; move: h g=> /= -> h ->. }

  have reach: forall b,
    REACH m2 (fun b0 => isGlobalBlock (ge (cores_T ix)) b0 
                       || getBlocks vals2 b0) b=true ->
    Mem.valid_block m2 b.
  { move=> ? ?; eapply mem_wd_reach_globargs; eauto.
    suff ->: isGlobalBlock my_ge = isGlobalBlock (ge (cores_T ix)). by [].
    extensionality b'.
    suff: is_true (isGlobalBlock my_ge b') <->
          is_true (isGlobalBlock (ge (cores_T ix)) b').
    case; rewrite /is_true /=.
    case: (isGlobalBlock _ _)=> //; case: (isGlobalBlock _ _)=> //.
    by intuition.
    by intuition.
    by apply: isGlob_iffT. }
    
  move: (core_initial (sims ix))=> H1.
  move: (H1 main vals1 c m1 j vals2  m2 dS dT).
  case=> //.

  by rewrite main_eq.

  { rewrite -meminj_preserves_genv2blocks.
    rewrite -(genvs_domain_eq_match_genvs (my_ge_S ix)).
    rewrite meminj_preserves_genv2blocks.
    by []. }

  { by apply: (genvs_domain_eq_globalptr_inject (my_ge_S ix) gfi). }

  { rewrite /dS /dT /mapped=> ? ? ? eq; split.
    apply Mem.valid_block_inject_1 with (m1:=m1) (m2:=m2) in eq=> //.
    by apply: valid_dec.
    apply Mem.valid_block_inject_2 with (m1:=m1) (m2:=m2) in eq=> //. 
    by apply: valid_dec. }

  { move=> b0 R; suff: Mem.valid_block m2 b0.
    by apply: valid_dec.
    apply reach; apply: (REACH_mono (fun b' : block =>
      isGlobalBlock (ge (cores_T ix)) b' || getBlocks vals2 b'))=> //. }

  { by eapply mrr_down_S; eassumption. }
  { by eapply mrr_down_T; eassumption. }

  { by apply: valid_dec'. }

  { by apply: valid_dec'. }

  move=> cd []c2 []init2 mtch12 mainsig_sig1.

  exists (existT _ ix cd).
  exists (mkLinker fun_tbl (CallStack.singl (Core.mk _ _ ix c2 sig1))).
  
  split.

  rewrite /as_inj /join /=; extensionality b0.
  by case: (j b0)=> [[? ?]//|//].

  simpl in init2.

  rewrite -main_eq init2 mainsig_sig1; split=> //.

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
      isGlobalBlock (ge (cores_T ix)) b1 || getBlocks vals2 b1))=> //. }

  set mu_top := Inj.mk mu_top_wd.
  
  have mu_top_val: sm_valid mu_top m1 m2.
  { split.
    by move=> b1; rewrite /DOM /DomSrc; case/orP=> //=; apply: valid_dec'.
    by move=> b2; rewrite /RNG /DomTgt; case/orP=> //=; apply: valid_dec'. }

  apply: Build_R=> //=.
  exists erefl,erefl,mu_top,[::]=> /=; split=> //.

  exists erefl; apply: Build_head_inv=> //.
  exists (getBlocks vals1); split.
  apply: Build_vis_inv; rewrite /= /RC.roots /vis /mu_top0 /= /fS.

  move=> /=; rewrite /in_mem {2}/getBlocks /= => b1 H.
  suff [H2|H2]: isGlobalBlock my_ge b1 \/ getBlocks vals1 b1.
  by apply: REACH_nil; apply/orP; left; rewrite -(isGlob_iffS my_ge_S).
  by apply: REACH_nil; apply/orP; right.
  apply/orP; case: (orP H); [|by move=> ->; rewrite orbC].
  by move/isGlob_iffS;  move/(_ _ my_ge_S)=> ->.

  by apply RCSem.init_ax with (v := Vptr b Int.zero).

  have vgenv_ix: valid_genv (ge (cores_T ix)) m2.
  { by apply: (valid_genvs_domain_eq (my_ge_T ix) vgenv). }

  by apply: (Nuke_sem.wmd_initial _ vval vgenv_ix wd init2).
  by move: gfi; rewrite /mu_top /= /mu_top0 initial_SM_as_inj.
  by move=> ix'; move: vgenv; apply: valid_genvs_domain_eq.

  by move=>ixx; eapply mrr_down_S; eassumption.
  by move=>ixx; eapply mrr_down_T; eassumption. 

  by apply: ord_dec. }(*END [Case: core_initial]*)
    
{(** Case: diagram*)
move=> st1 m1 st1' m1' STEP data st2 mu m2 INV. 
case: STEP=> STEP STEP_EFFSTEP; case: STEP.

{(** Subcase: corestep0*)
move=> STEP. 
set c1 := peekCore st1.
set c2 := peekCore st2.

have [c1_B [c1_vis c1_I]]: 
  exists B, [/\ vis_inv c1 B mu 
              & RCSem.I (rclosed_S c1.(Core.i)) c1.(Core.c) m1 B].
{ case: INV; rewrite /c1 /c2 /=; case=> ? []? []? []? []Hmueq []?.
  by case=> _ _ []B []c1_vis c1_I; exists B; split=> //; subst. }

have [U1 [c1' [STEP0 [ESTEP0 [U1'_EQ ST1']]]]]:
   exists (U1:block -> Z -> bool) c1',
       @corestep _ _ _
         (sem (cores_S (Core.i c1))) 
         (ge (cores_S (Core.i c1))) (Core.c c1) m1 c1' m1' 
   /\  effect_semantics.effstep 
         (sem (cores_S (Core.i c1)))
         (ge (cores_S (Core.i c1))) U1 (Core.c c1) m1 c1' m1'
   /\ (forall b ofs, U1 b ofs -> 
       RC.reach_set (ge (cores_S (Core.i c1))) (RC.mk (Core.c c1) c1_B) m1 b)
   /\ st1' = updCore st1 (Core.upd c1 c1').
  { move: (STEP_EFFSTEP STEP)=> EFFSTEP.
    move: STEP; rewrite/LinkerSem.corestep0=> [][]c1' []B C. 
    move: EFFSTEP; rewrite/effstep0.
    move=> []U1 []/= => x []EFFSTEP u1.
    eapply RCSem.step_ax in B; eauto; case: B=> /= D E.
    case: D=> B; rewrite /RC.effstep => /= [][]Hstep []Hin _.
    exists B, c1'; split=> //.
    by apply effect_semantics.effax1 in Hstep; case: Hstep. }

(** Specialize core diagram at module (Core.i c1). *)
move: (effcore_diagram _ _ _ _ (sims (Core.i c1))).  
move/(_ _ _ _ _ _ ESTEP0).
case: (R_inv INV)=> pf []pf_sig []mupkg []mus []mu_eq.
move=> []pf2 hdinv tlinv.

move: (head_match hdinv)=> MATCH.

have U1_DEF': forall b ofs, U1 b ofs -> vis mupkg b. 
{ move=> b ofs U; move: (U1'_EQ b ofs U)=> H.
  apply match_visible in MATCH; apply: MATCH.
  apply (REACH_mono (fun b => 
    b \in RC.roots (ge (cores_S (Core.i c1))) (RC.mk (Core.c c1) c1_B)))=> //.
  by move=> b0 roots; case: c1_vis; subst; apply. }

move/(_ _ _ _ _ MATCH).
move=> []c2' []m2' []cd' []mu_top0.
move=> []INCR []GSEP []LOCALLOC []MATCH' []U2 []STEP' PERM.

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
set data'  := (existT (fun ix => core_data (sims ix)) (Core.i c1) cd'). 
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

{(** Re-establish invariant. *) 
 have fwd1: mem_forward m1 m1'.
 { by apply: (corestep_fwd STEP0). }

 apply: Build_R. rewrite ST1'; rewrite /st2'.

 have sgeq: Core.sg c1=Core.sg c2.
 { by move: pf_sig; rewrite /c /d /c1 /c2 /= => <-. }

 exists pf,sgeq,mupkg',mus; split=> //.

 (* head_inv *)
 { case: tlinv=> allrel frameall.
   exists erefl=> /=.
   have rcvis: REACH_closed m1' (vis mu').
   { by apply match_visible in MATCH'; apply: MATCH'. }
   have GSEP': (globals_separate my_ge mupkg mu_top').
   {
     eapply gsep_domain_eq; eauto.
     apply genvs_domain_eq_sym; eauto.
   }
   apply (@head_inv_step _ _ _ _ _ sims my_ge 
     mupkg m1 m2 mu_top' m1' m2' fwd2 (head_valid hdinv) INCR GSEP' LOCALLOC rcvis
     (c INV) (d INV) pf c1' c2'' _ _ mus
     (STACK.pop (CallStack.callStack (s1 INV))) 
     (STACK.pop (CallStack.callStack (s2 INV))) U1 n U2 hdinv frameall)=> //=.
   by apply: (R_ge INV).
   by have ->: cast'' pf c2'' = c2' by apply: cast_cast_eq'. }

 (* tail_inv *)
 { eapply tail_inv_step with (Esrc := U1) (Etgt := U2) (mu' := mu_top'); eauto.
   by apply: (effstep_unchanged _ _ _ _ _ _ _ ESTEP0).
   by move: STEPN; apply: effect_semantics.effstepN_unchanged.
   by move: STEP0; apply corestep_rdonly.
   by apply effstepN_corestepN in STEPN; move: STEPN; 
      apply semantics_lemmas.corestepN_rdonly.
   move=> ? ? X; move: (PERM U1_DEF' _ _ X)=> []Y Z; split=> //.
   by eapply effstepN_valid in STEPN; eauto.
     by apply: (head_valid hdinv).
     {
     eapply gsep_domain_eq; eauto.
     apply genvs_domain_eq_sym; eauto.
     }
   by apply match_visible in MATCH'; apply: MATCH'.
   by apply: (head_rel hdinv). } 

 (* fn_tbl *)
 { by rewrite ST1' (R_fntbl INV). } 

 (* valid_genv *)
 { move=> ix; move: (R_ge INV); move/(_ ix)=> vgenv. 
   by apply: (Nuke_sem.valid_genv_fwd vgenv). }

 (* mem_respects_readonly ... m1' *)
 { move=> ix; move: (R_ro1 INV); move/(_ ix)=> RO1.
   apply (mem_respects_readonly_fwd _ _ _ RO1 fwd1).
   move: STEP0; apply corestep_rdonly.
 }

 (* mem_respects_readonly ... m2' *)
 { move=> ix; move: (R_ro2 INV); move/(_ ix)=> RO2.
   apply (mem_respects_readonly_fwd _ _ _ RO2 fwd2).
   apply effstepN_corestepN in STEPN; move: STEPN.
   apply semantics_lemmas.corestepN_rdonly.
 }

 (* mem_respects_readonly ... m1' *)
 { move: (frame_mmr1 INV); move=> RO1.
   apply (mem_respects_readonly_fwd _ _ _ RO1 fwd1).
   move: STEP0; apply corestep_rdonly.
 }

 (* mem_respects_readonly ... m2' *)
 { move: (frame_mmr2 INV); move=> RO2.
   apply (mem_respects_readonly_fwd _ _ _ RO2 fwd2).
   apply effstepN_corestepN in STEPN; move: STEPN.
   apply semantics_lemmas.corestepN_rdonly.
 }
    
 unfold c1 in *; rewrite ST1'; move: (R_tys1 INV). 
 rewrite /s1 => tys; clear -tys; case st1_eq: st1 tys c1'=> // [fntbl stack]. 
 case stack_eq: stack=> [stack0 WF]; rewrite /= => tys _.
 by case stack0_eq: stack0 WF stack_eq tys.

 unfold c2 in *; rewrite /st2'; move: (R_tys2 INV); rewrite /s2=> tys.
 clear -tys; case st2_eq: st2 tys c2' c2''=> // [fntbl stack]. 
 case stack_eq: stack=> [stack0 WF]; rewrite /= => tys _.
 by case stack0_eq: stack0 WF stack_eq tys.

 } (*end [re-establish invariant]*)
 
 {(** Matching execution *) 
 have EFFECTS_REFINEMENT: 
     forall b ofs, U2 b ofs = true ->
     visTgt mu b = true /\
     (locBlocksTgt mu b = false ->
       exists b1 d1, 
         foreign_of mu b1 = Some (b, d1) /\
         U1 b1 (ofs - d1) = true /\
         Mem.perm m1 b1 (ofs - d1) Max Nonempty).
 { move=> b ofs X; move: (PERM U1_DEF' _ _ X)=> []H Y; split.
   by move: H; rewrite mu_eq. 
   by rewrite mu_eq. }

case: STEP'=> STEP'.

have STEP'': 
  effstep_plus (sem (cores_T (Core.i c2)))
  (ge (cores_T (Core.i c2))) U2 (Core.c (d INV)) m2 c2'' m2'. 
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) (y : T ix) => 
             effstep_plus (sem (cores_T ix))
             (ge (cores_T ix)) U2 x m2 y m2'.
   change (P (Core.i c2) (Core.c c2) c2''); apply: cast_indnatdep2.
   by move: STEP'; have ->: pf = peek_ieq INV by apply: proof_irr. }
left; move: STEP''; move/(@stepPLUS_STEPPLUS _ _ fun_tbl my_ge).
by case=> m H; apply effstepN_corestepN in H; exists m; apply: H.

have STEP'': 
  effstep_star (sem (cores_T (Core.i c2)))
  (ge (cores_T (Core.i c2))) U2 (Core.c c2) m2 c2'' m2'. 
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) (y : T ix) => 
             effstep_star (sem (cores_T ix))
             (ge (cores_T ix)) U2 x m2 y m2'.
   change (P (Core.i c2) (Core.c c2) c2''); apply: cast_indnatdep2.
   by case: STEP'; have ->: pf = peek_ieq INV by apply: proof_irr; by []. }
right; move: STEP''; move/(@stepSTAR_STEPSTAR _ _ fun_tbl my_ge).
case=> m H; apply effstepN_corestepN in H; split; first by exists m; apply: H.
rewrite /sig_ord /data' /=.

have eq: Core.i c1 = projT1 data.
{ by clear - pf2; move: pf2; rewrite /c /s1 /c1 /peekCore /= => ->. }

exists eq; case: STEP'=> STEP' ORD.
have <-: pf2 = sym_eq eq by apply: proof_irr.
by apply: ORD. } (*end [Label: matching execution]*)
} (*end [Subcase: corestep0]*)

move=> []<- []NSTEP.
case AT1: (LinkerSem.at_external0 st1)=> [[[ef1 sig1] args1]|].

{(** Subcase: at_external0 *)
case FID: (LinkerSem.fun_id ef1)=> [id|//].
case HDL: (LinkerSem.handle _ _ _ _)=> [st1''|//] eq1.
have wd: SM_wd mu by apply: (R_wd INV).
have INV': R data (Inj.mk wd) st1 m1 st2 m2 by [].
case: (atext2 AT1 INV')=> args2 AT2.
case: (hdl2 find_symbol_ST my_ge_S my_ge_T AT1 HDL INV' AT2)=> 
  cd' []st2' []mu' []HDL2 INV2.
exists st2',m2,cd',mu'; split=> //; first by rewrite eq1.
left; exists O=> /=; exists st2',m2; split=> //.
constructor=> //. 
right; split=> //; split=> //.
by move/LinkerSem.corestep_not_at_external0; rewrite AT2.
by rewrite AT2 FID HDL2.
by move/LinkerSem.corestep_not_at_external0; rewrite AT2.
}(*end [Subcase: at_external0]*)

case CTXT: (inContext st1)=> //.
case HLT1: (LinkerSem.halted0 st1)=> [rv|].

{(** Subcase: halted0 *)
case POP1: (popCore st1)=> [st1''|//].
case AFT1: (LinkerSem.after_external (Some rv) st1'')=> [st1'''|//] eq1.

have mu_wd: SM_wd mu. 
{ by apply: (R_wd INV). }

have INV': R data (Inj.mk mu_wd) st1 m1 st2 m2.
{ by apply: INV. }

case: (aft2 my_ge_T all_gvars_includedS all_gvars_includedT HLT1 POP1 INV' AFT1)=> 
  rv2 []st2'' []st2' []cd' []mu' []HLT2 CTX2 POP2 AFT2 INV''.
exists st2',m2,cd',mu'.
split=> //; first by rewrite eq1.
left; exists O=> /=; exists st2',m2.
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

{(** Case: halted *)
move=> cd mu c1 m1 c2 m2 v1 inv hlt1.
have mu_wd: SM_wd mu by apply: R_wd inv.
have inv': R cd (Inj.mk mu_wd) c1 m1 c2 m2 by [].
case: (toplevel_hlt2 hlt1 inv')=> v2 hlt2.
case: (R_inv inv')=> pf []pf_sig []mupkg []mus []mu_eq.
move=> []pf2 hdinv tlinv; move: (head_match hdinv)=> mtch0.

have hlt10: 
  halted (sem (cores_S (Core.i (c inv')))) (Core.c (c inv)) 
= Some v1.
{ move: hlt1; rewrite /= /LinkerSem.halted.
  case inCtx1: (inContext c1)=> //=.
  case hlt10: (LinkerSem.halted0 c1)=> [v1'|//]; case=> <-.
  move: hlt10; rewrite /LinkerSem.halted0 /c /= /RC.halted.
  case hlt100: (halted _ _)=> //.
  case hasty: (val_casted.val_has_type_func _ _)=> //. }

case: (core_halted (sims (Core.i (c inv'))) _ _ _ _ _ _ mtch0 hlt10).
move=> v2' []inj []mrr1 []mrr2 []vinj hlt2'.

exists mupkg,v2'; split.

rewrite /cc_halt_inv.
rewrite -meminj_preserves_genv2blocks.
rewrite (genvs_domain_eq_match_genvs (my_ge_S (Core.i (c inv')))).
rewrite meminj_preserves_genv2blocks.
case: (match_genv mtch0)=> ext isGlob_frgn.
rewrite match_genv_meminj_preserves_extern_iff_all=> //.
split=> //. 
split; first by apply: (val_inject_restrictD _ _ _ _ vinj).
by [].
by apply: Inj_wd.
rewrite /= hlt2.
move: hlt2; rewrite /LinkerSem.halted.
case e: (~~ inContext c2)=> //.
case f: (LinkerSem.halted0 c2)=> [rv|//]; case=> <-.
rewrite /LinkerSem.halted0 /= /RC.halted in f hlt2'.
have f': halted (sem (cores_T (Core.i (peekCore c2)))) (Core.c (peekCore c2))
       = Some rv.
{ move: f.
  case: (halted _ _)=> //v.
  case: (val_casted.val_has_type_func _ _)=> //. }
have g: halted (sem (cores_T (Core.i (c inv'))))
               (cast'' pf (Core.c (d inv')))  
      = Some rv.
{ set T := C \o cores_T.
  set P := fun ix (x : T ix) => 
             halted (sem (cores_T ix)) x  
           = Some rv.
  change (P (Core.i (c inv')) (cast T (sym_eq pf) (Core.c (d inv')))).
  by apply: cast_indnatdep; rewrite /P; rewrite -f'. }
by rewrite -g. }(*END Case: halted*)

Qed.

End linkingSimulation.

Require Import linking_spec.

Module LinkingSimulation : LINKING_SIMULATION.

Lemma link : 
  forall (N : pos) (sems_S sems_T : 'I_N -> t),
  (forall (i : 'I_N) (id : ident) (bf : block),
  Genv.find_symbol (ge (sems_S i)) id = Some bf ->
  Genv.find_symbol (ge (sems_T i)) id = Some bf) ->
 (forall ix : 'I_N, RCSem.t (sem (sems_S ix)) (ge (sems_S ix))) ->
 (forall ix : 'I_N, Nuke_sem.t (sem (sems_T ix))) ->
 forall plt : ident -> option 'I_N,
 (forall ix : 'I_N,
  let s := sems_S ix in
  let t := sems_T ix in
  SM_simulation_inject (sem s) (sem t) (ge s) (ge t)) ->
 forall ge_top : ge_ty,
 (forall ix : 'I_N, genvs_domain_eq ge_top (ge (sems_S ix))) ->
 (forall ix : 'I_N, genvs_domain_eq ge_top (ge (sems_T ix))) ->

 (*Four new assumptions*)
 (forall ix id b,
    Genv.find_symbol (ge (sems_S ix)) id = Some b ->
    Genv.find_symbol ge_top id = Some b) ->
 (forall ix id b,
    Genv.find_symbol  (ge (sems_T ix)) id = Some b ->
    Genv.find_symbol ge_top id = Some b) ->
 (forall ix b, gvars_included (Genv.find_var_info (ge (sems_S ix)) b)
                             (Genv.find_var_info ge_top b)) ->
 (forall ix b, gvars_included (Genv.find_var_info (ge (sems_T ix)) b)
                             (Genv.find_var_info ge_top b)) ->

 let linker_S := effsem N sems_S plt in
 let linker_T := effsem N sems_T plt in
 forall main : val,
 CompCert_wholeprog_sim linker_S linker_T ge_top ge_top main.
Proof. by move=> *; apply: link. Qed.

End LinkingSimulation.
