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

Import Wholeprog_sim.
Import SM_simulation.
Import Linker. 
Import Modsem.
Import CallStack.

Require Import compcert_imports. Import CompcertLibraries.
Require Import mem_welldefined.

Section call_lems.

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

Notation my_cast  pf x := (cast (C \o cores_T) pf x).
Notation my_cast_sym pf x := (cast (C \o cores_T) (sym_eq pf) x).
Notation R := (@R N cores_S cores_T rclosed_S nucular_T sims my_ge). 

Context
(mu : Inj.t) m1 m2 ef sig args1 
(st1 st1' : linker N cores_S) cd st2 id 
(valid : sm_valid mu m1 m2)
(fid : LinkerSem.fun_id ef = Some id)
(atext1 : LinkerSem.at_external0 st1 = Some (ef,sig,args1))
(hdl1 : LinkerSem.handle (ef_sig ef) id st1 args1 = Some st1')
(inv : R cd mu st1 m1 st2 m2).

Lemma atext2 : 
  exists args2, 
  LinkerSem.at_external0 st2 = Some (ef,sig,args2).
Proof.
case: (R_inv inv)=> pf []pf_sig []mu_top []mus []eq []pf2; move/head_match.
unfold LinkerSem.at_external0 in atext1.
have atext1':
  at_external 
    (sem (cores_S (Core.i (peekCore st1)))) 
    (Core.c (peekCore st1)) =
  Some (ef,sig,args1) by rewrite /RC.at_external.
move=> hd_match _.
case: (core_at_external (sims (Core.i (c inv))) 
      _ _ _ _ _ _ hd_match atext1').
move=> inj []mmr1 []mrr2 []args2 []valinj []atext2 extends; exists args2.
set T := C \o cores_T.
rewrite /LinkerSem.at_external0.
set P := fun ix (x : T ix) => 
            at_external (sem (cores_T ix)) x
            = Some (ef, sig, args2).
change (P (Core.i (peekCore st2)) (Core.c (peekCore st2))).
have X: (P (Core.i (c inv)) (my_cast_sym pf (Core.c (d inv)))).
{ move: atext2=> /=; rewrite /RC.at_external /P /=.
  have eq': at_external (sem (cores_T (Core.i (c inv))))
            (my_cast_sym pf (Core.c (d inv))) =
           at_external (sem (cores_T (Core.i (d inv))))
            (Core.c (d inv)). 
  { set T' := C \o cores_T.
    set P' := fun ix (x : T' ix) => 
                 at_external (sem (cores_T ix)) x
                 = at_external (sem (cores_T (Core.i (d inv))))
                     (Core.c (d inv)).
    change (P' (Core.i (c inv)) 
               (cast T' (sym_eq pf) (Core.c (d inv)))).
    by apply: cast_indnatdep. }
  by []. }
by apply: (cast_indnatdep' X).
Qed.

Lemma genvs_domain_eq_globalptr_inject F1 V1 F2 V2 (ge : Genv.t F1 V1) (ge' : Genv.t F2 V2) j :
  genvs_domain_eq ge ge' -> 
  globalfunction_ptr_inject ge j -> 
  globalfunction_ptr_inject ge' j.
Proof.
move=> Hgenv; case: (Hgenv)=> _ []_ H H2 b f Hfind. 
case: (H b)=> H3 H4; case: H4; first by exists f.
move=> f1 Hfind1; case: (H2 _ _ Hfind1); split=> //.
by rewrite -(genvs_domain_eq_isGlobal _ _ Hgenv).
Qed.

Lemma hdl2 args2 : 
  LinkerSem.at_external0 st2 = Some (ef,sig,args2) -> 
  exists cd' st2' mu',
    LinkerSem.handle (ef_sig ef) id st2 args2 = Some st2'
    /\ R cd' mu' st1' m1 st2' m2.
Proof.
move=> A.
case: (R_inv inv)=> pf []pf_sig []mu_top []mus []mu_eq.
move=> []pf2 hdinv tlinv; move: hdl1; rewrite LinkerSem.handleP.
move=> []all_at1 []ix []bf []c1 []fntbl1 genv init1 st1'_eq.

have atext1': 
  at_external (sem (cores_S (Core.i (c inv)))) (Core.c (c inv)) 
  = Some (ef,sig,args1) by [].

have atext2': 
  at_external (sem (cores_T (Core.i (c inv)))) 
              (my_cast_sym pf (Core.c (d inv)))
  = Some (ef,sig,args2).
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) => 
              at_external (sem (cores_T ix)) x
              = Some (ef, sig, args2).
   have: (P (Core.i (d inv)) (Core.c (d inv)))
     by rewrite /LinkerSem.at_external0.
   by apply: cast_indnatdep. }

have atext2'': 
  at_external (sem (cores_T (Core.i (c inv))))
              (my_cast_sym pf (Core.c (d inv)))
  = Some (ef,sig,args2).
 { set T := C \o cores_T.
   set P := fun ix (x : T ix) => 
              at_external (sem (cores_T ix)) x
              = Some (ef, sig, args2).
   have: (P (Core.i (d inv)) (Core.c (d inv)))
     by rewrite /LinkerSem.at_external0.
   by apply: cast_indnatdep. }

case: (core_at_external (sims (Core.i (c inv))) 
      _ _ _ _ _ _ (head_match hdinv) atext1').
move=> inj []mrr1 []mrr2 []args2' []vinj []atext2''' extends.

have eq: args2 = args2' by move: atext2'''; rewrite atext2''; case.
subst args2'.

set (j := as_inj mu_top).
set (domS := DomSrc mu_top).
set (domT := DomTgt mu_top).
set (frgnS := REACH m1 (fun b => 
  isGlobalBlock (ge (cores_S (Core.i c1))) b || getBlocks args1 b)).
set (frgnT := REACH m2 (fun b => 
  isGlobalBlock (ge (cores_T (Core.i c1))) b || getBlocks args2 b)).

have j_domS_domT:
  forall b1 b2 d0,
  j b1 = Some (b2, d0) -> domS b1 = true /\ domT b2 = true.
{ move=> b1 b2 d0; rewrite /j /domS /domT; move/as_inj_DomRng.
  by move/(_ (Inj_wd _)). }

have my_atext2: 
    at_external (sem (cores_T (Core.i (d inv)))) (Core.c (d inv)) 
  = Some (ef,sig,args2).
{ move: atext2'. 
  set T := C \o cores_T.
  set P := fun (ix : 'I_N) (c : T ix) => 
    at_external (sem (cores_T ix)) c = Some (ef,sig,args2).
  change (P (Core.i (c inv)) (cast T (sym_eq pf) (Core.c (d inv)))
       -> P (Core.i (d inv)) (Core.c (d inv))).
  by apply: cast_indnatdep'. }

have wmd: mem_wd m2.
{ by case: (Nuke_sem.wmd_at_external (ge (cores_T (Core.i (d inv)))) 
             (head_nukeI hdinv) my_atext2). }

have DomTgt_rc: REACH_closed m2 (DomTgt mu_top).
{ move=> b rch; rewrite (head_domt hdinv) in rch|-*. 
  by apply: valid_dec; apply: mem_wd_reach. }

have defs1: vals_def args1.
{ clear - hdinv atext1'; move: atext1'; rewrite /= /RC.at_external.
  case e: (at_external _ _)=> [[[ef0 dep_sig0] args0]|//].
  case: hdinv=> _ _; case=> B []_ I _ _ _.
  by case=> _ _ <-; apply: (RCSem.atext_ax I e). }

have frgnT_sub_domT: {subset frgnT <= domT}.
{ move=> b H; apply: DomTgt_rc. 
  apply: (REACH_mono (fun b : block =>
    isGlobalBlock (ge (cores_T (Core.i c1))) b || getBlocks args2 b))=> //.
  move=> b0; case/orP=> H3.
  move: (H3); rewrite -(isGlob_iffT my_ge_T)=> H3'.
  move: (head_globs my_ge_S hdinv); move/(_ b0 H3')=> H4.
  have J: extern_of mu_top b0 = Some (b0,0).
  { move: (head_match hdinv)=> mtch; apply match_genv in mtch.
    case: mtch=> pres _; move: (meminj_preserves_globals_isGlobalBlock _ _ pres b0)=> H5. 
    apply: H5; set (b' := isGlobalBlock _ _); suff: (is_true b')=> //.
    by rewrite -(isGlob_iffS (my_ge:=my_ge)). }
  case: (Inj_wd mu_top)=> _ _ _ _ _; case/(_ b0 H4)=> x []y []H5 H6 _ _.
  by apply/orP; right; apply: frgntgt_sub_exttgt; move: H6; 
     rewrite H5 in J; case: J=> ->.
  have [b1 [ofs [getbs1 asinj1]]]: 
    exists b1 ofs, 
    [/\ getBlocks args1 b1
      & as_inj mu_top b1 = Some (b0,ofs)]. 
  { move: (forall_inject_val_list_inject _ _ _ vinj)=> vinj'.
    case: (vals_def_getBlocksTS vinj' defs1 H3)=> x' []y' []? res.
    by exists x',y'; split=> //; case: (restrictD_Some _ _ _ _ _ res). }
  by case: (as_inj_DomRng _ _ _ _ asinj1 (Inj_wd _))=> _ ->. }

have st1_eq: callStack (stack st1) = [:: c inv & STACK.pop st1].
{ by rewrite /c /s1; case: st1 inv=> //= ?; case=> //=; case. }

have st2_eq: callStack (stack st2) = [:: d inv & STACK.pop st2].
{ by rewrite /d /s2; case: st2 inv=> //= ?; case=> //=; case. }

have all_at2: all (atExternal cores_T) (CallStack.callStack st2).
{ move: (callStack_wf st2); move/andP=> []atext_tail _; rewrite st2_eq.
  move=> /=; apply/andP; split=> //; move: A. 
  rewrite /LinkerSem.at_external0 /atExternal /d /s2 /pf2 /peekCore.
  by case: (STACK.head _ _)=> ? ? /= d atext2_; rewrite /RC.at_external atext2_. }

have globs_frgnS:
  forall b,
  isGlobalBlock (ge (cores_S (Core.i c1))) b ->
  frgnBlocksSrc mu_top b.
{ move=> b H; case: (match_genv (head_match hdinv))=> _; move/(_ b); apply.  
  move: H; rewrite -(initCore_ix init1).
  have eq: genvs_domain_eq (ge (cores_S ix)) (ge (cores_S (Core.i (c inv)))).
    apply genvs_domain_eq_trans with (ge2 := my_ge)=> //.
    by apply: (genvs_domain_eq_sym _ _ (my_ge_S ix)).
  by rewrite /= (genvs_domain_eq_isGlobal _ _ eq). }

have presglobs: meminj_preserves_globals (ge (cores_S (Core.i c1))) j.
{ move: (head_presglobs my_ge_S hdinv).
  rewrite -meminj_preserves_genv2blocks.
  rewrite (genvs_domain_eq_match_genvs (my_ge_S (Core.i c1))).
  rewrite meminj_preserves_genv2blocks.
  rewrite match_genv_meminj_preserves_extern_iff_all=> //.
  by apply: Inj_wd. }

have globs_frgnT:
  forall b,
  isGlobalBlock (ge (cores_T (Core.i c1))) b ->
  frgnBlocksTgt mu_top b.
{ move=> b H; case: (match_genv (head_match hdinv))=> _; move=> I. 
  have fS: frgnBlocksSrc mu_top b.
  { apply: I; move: H; rewrite -(initCore_ix init1).
    have eq: genvs_domain_eq (ge (cores_T ix)) (ge (cores_S (Core.i (c inv)))).
      apply genvs_domain_eq_trans with (ge2 := my_ge)=> //.
      by apply: (genvs_domain_eq_sym _ _ (my_ge_T ix)).
    by rewrite (genvs_domain_eq_isGlobal _ _ eq). }
  case: (frgnSrc _ (Inj_wd _) _ fS)=> b' []d []fOf fT.
  have eq: b=b'. 
  { case: (match_genv (head_match hdinv))=> [][]J []K L _.
    have H': isGlobalBlock (ge (cores_S (Core.i (c inv)))) b.
    { by rewrite (isGlob_iffST' my_ge_S); eauto. }
    move: H'; rewrite /isGlobalBlock /=.
    case e1: (Genv.invert_symbol _ _)=> //=.
    move: (Genv.invert_find_symbol _ _ e1)=> M O.
    move: (J _ _ M)=> E.
    by move: (foreign_in_extern _ _ _ _ fOf); rewrite E; case.
    case e2: (Genv.find_var_info _ _)=> //[gv].
    move: (K _ _ e2).
    by move: (foreign_in_extern _ _ _ _ fOf)=> ->; case. }
  by rewrite eq. }

have vinj': Forall2 (val_inject (as_inj mu_top)) args1 args2. 
{ by apply: (forall_vals_inject_restrictD _ _ _ _ vinj). }

have domS_valid:
  forall b, domS b -> Mem.valid_block m1 b.
{ by move: (match_validblocks _ (head_match hdinv)); case=> H I; apply: H. }

have domT_valid:
  forall b, domT b -> Mem.valid_block m2 b.
{ by move: (match_validblocks _ (head_match hdinv)); case=> H I; apply: I. }

have [cd_new [c2 [pf_new [init2 mtch12]]]]:
  exists (cd_new : core_data (sims (Core.i c1))) 
         (c2 : Core.t cores_T)
         (pf : Core.i c1 = Core.i c2),
    [/\ initCore cores_T (ef_sig ef) ix (Vptr bf Integers.Int.zero) args2 = Some c2
      & match_state (sims (Core.i c1)) cd_new
        (initial_SM domS domT frgnS frgnT j) 
        (Core.c c1) m1 (my_cast_sym pf (Core.c c2)) m2].
{ move: init1; rewrite /initCore.
  case init1: (semantics.initial_core _ _ _ _)=> //[c1']; case=> X.
  generalize dependent c1; case=> c1_i c1; intros.
  move: (X) init1; case=> eq _ _ init1; subst ix=> /=.
  case: (core_initial _ _ _ _ (sims c1_i) _ 
         args1 _ m1 j args2 m2 domS domT init1 inj vinj')=> //.
  case: hdinv=> ? ? ? ? ? genvs /=; rewrite /j.
  by apply: (genvs_domain_eq_globalptr_inject (my_ge_S c1_i) genvs). 
  by apply: (R_ro1 inv). 
  by apply: (R_ro2 inv).
(*  by case: inv=> ????????? Ro1 Ro2 _ _ _ _; apply: Ro1.
  by case: inv=> ????????? Ro1 Ro2 _ _; apply: Ro2.*)
  move=> cd' []c2' []init2 mtch_init12.
  exists cd',(Core.mk N cores_T c1_i c2' (ef_sig ef)),erefl.
  move: init2=> /= ->; split=> //=.
  rewrite cast_ty_erefl; move: X; case=> X.
  move: (EqdepFacts.eq_sigT_snd X)=> /= <-. intros. 
  rewrite -Eqdep_dec.eq_rect_eq_dec; first by apply: mtch_init12.
  move=> m n; case e: (m == n); first by left; move: (eqP e).
  right=> Contra; rewrite Contra in e. 
  by rewrite eq_refl in e. }

set (st2' := pushCore st2 c2 all_at2).

have eq1: 
    Core.i (STACK.head st1' (callStack_nonempty st1'))
  = Core.i c1.
{ by rewrite st1'_eq. }

have eq2: 
    Core.i (STACK.head st2' (callStack_nonempty st2'))
  = Core.i c2.
{ by []. }

set mu_new := initial_SM domS domT frgnS frgnT j.

have mu_new_wd: SM_wd mu_new.
{ apply: initial_SM_wd=> //.
  move=> b1; apply: REACH_inject=> // b; case/orP=> H.  
  move: (meminj_preserves_globals_isGlobalBlock _ _ presglobs _ H)=> H2.
  exists b,0; split=> //; apply/orP; left.
  by move: H; rewrite -(@isGlob_iffS _ _ _ my_ge_S (Core.i c1))
    (@isGlob_iffT _ _ _ my_ge_T (Core.i c1)).
  case: (getBlocks_inject _ _ _ vinj' _ H)=> x []y []H2 H3.
  by exists x,y; split=> //; apply/orP; right.
  move=> b H; move: (head_match hdinv)=> mtch; apply match_visible in mtch.
  suff: vis mu_top b by apply: vis_sub_DomSrc.
  apply: mtch; apply: (REACH_mono 
    (fun b : block =>
      isGlobalBlock (ge (cores_S (Core.i c1))) b || getBlocks args1 b))=> //.
  by move=> b0; eapply globs_blocks_in_vis; eauto. }

set mu_new' := Inj.mk mu_new_wd.

case: (extends _ _ erefl erefl _ erefl). 

(* mu_pkg is leak-out(mu_top) *)

set mu_pkg' := 
  (replace_locals mu_top
  (fun b : block =>
    locBlocksSrc mu_top b && REACH m1 (exportedSrc mu_top args1) b)
  (fun b : block =>
    locBlocksTgt mu_top b && REACH m2 (exportedTgt mu_top args2) b)).

move=> mtch_pkg inj_pkg.

have mu_pkg_wd: SM_wd mu_pkg'.
{ by exploit lo_wd; eauto. }

set mu_pkg := Inj.mk mu_pkg_wd.

have valid': sm_valid mu_pkg m1 m2. 
{ by apply match_validblocks in mtch_pkg. }

set pkg := Build_frame_pkg valid'.

have mu_pkg_as_inj: as_inj mu_pkg = as_inj mu_top.
{ by rewrite /mu_pkg /= replace_locals_as_inj. }

have pkg_hdinv: 
  head_inv rclosed_S nucular_T my_ge pf
  (cast (fun ix : 'I_N => core_data (sims ix)) pf2 (projT2 cd))
  pkg mus m1 m2.
{ move: (@lo_head_inv _ _ _ _ _ _ _ (c inv) (d inv) pf 
    (cast (fun ix0 : 'I_N => core_data (sims ix0)) pf2 (projT2 cd))
    mu_top mus m1 m2 hdinv _ _ args1 args2 inj vinj erefl erefl mtch_pkg).
  rewrite /pkg /= /mu_pkg.
  have ->: lo_wd _ _ _ _ _ = mu_pkg_wd by move=> *; apply: proof_irr.
    by apply. }

have mu_new_rel_inv_pkg: rel_inv_pred my_ge m1 mu_new pkg.
{ by apply init_rel_inv_mu
    with (c := c inv) (d := d inv) (pf := pf) 
         (cd := (cast (fun ix : 'I_N => 
           core_data (sims ix)) pf2 (projT2 cd))) 
         (mus := mus)
         (inv := hdinv) (inj := inj) (vinj := vinj)
         (eq1 := erefl) (eq2 := erefl). }

have mu_new_rel_inv_all: 
  All (rel_inv_pred my_ge m1 (initial_SM domS domT frgnS frgnT j)) mus.
{ apply init_rel_inv_rest 
    with (c := c inv) (d := d inv) (pf := pf) 
         (cd := (cast (fun ix : 'I_N => 
           core_data (sims ix)) pf2 (projT2 cd))) 
         (mus := mus) 
         (my_ge := my_ge)
         (rclosed_S := rclosed_S)
         (nucular_T := nucular_T)=> //.
  by move: (head_match hdinv)=> mtch; apply match_visible in mtch. }

have mu_new_vis_inv: vis_inv c1 (getBlocks args1) mu_new'.
{ apply: Build_vis_inv=> // b; rewrite /in_mem /= => Y.
  rewrite /vis /mu_new /frgnS /exportedSrc /=.
  move: Y; rewrite /RC.roots; case/orP.
  move=> H1.
  by apply: REACH_nil; apply/orP; left.
  by move=> getB; apply: REACH_nil; apply/orP; right. }

have hdinv_new:
  head_inv rclosed_S nucular_T my_ge pf_new cd_new mu_new' (pkg :: mus) m1 m2.
{ apply: Build_head_inv=> //. 
  exists (getBlocks args1); split=> //.
  move: init1; rewrite /initCore; case Hinit: (initial_core _ _ _ _)=> //. 
  by case=> <-; apply RCSem.init_ax with (v := Vptr bf Int.zero).
  by rewrite /= /mu_new initial_SM_DomTgt /domT; apply: (head_domt hdinv). 
  have vgenv1: valid_genv (ge (cores_T (Core.i (c inv)))) m2.
  { by move: (R_ge inv)=> val_ges; apply: (val_ges (Core.i (c inv))). }
  have vgenv2: valid_genv (ge (cores_T (Core.i c2))) m2.
  { by move: (R_ge inv)=> val_ges; apply: (val_ges (Core.i c2)). }
  have vval: Forall (val_valid^~ m2) args2.
  { by case: (Nuke_sem.wmd_at_external (ge (cores_T (Core.i (d inv)))) 
               (head_nukeI hdinv) my_atext2). }
  have init: initial_core (cores_T (Core.i c2)).(sem) 
               (ge (cores_T (Core.i c2))) (Vptr bf Int.zero) args2 
           = Some c2.(Core.c).
  { clear - init2; move: init2; rewrite /initCore.
    by case e: (initial_core _ _ _ _)=> [c|//]; case=> <- /=. }
  by apply: (Nuke_sem.wmd_initial (nucular_T (Core.i c2)) vval vgenv2 wmd init). 
  rewrite /mu_new' /= /mu_new /= initial_SM_as_inj.
  by case: hdinv=> ? ? ? ? ? genvs /=; rewrite /j.
}

exists (existT _ (Core.i c1) cd_new),st2',mu_new'; split.
rewrite LinkerSem.handleP; exists all_at2,ix,bf,c2; split=> //.
by move: fntbl1; rewrite (R_fntbl inv).
by apply: find_symbol_ST.

have valid_new: sm_valid mu_new' m1 m2. 
{ move: (head_match hdinv)=> mtch; apply match_validblocks in mtch.
  by apply: mtch. }

set (pkg_new := Build_frame_pkg valid_new).

have pf_new':
    Core.i (STACK.head st1' (callStack_nonempty st1'))
  = Core.i (STACK.head st2' (callStack_nonempty st2')).
{ by rewrite eq1 eq2; apply: pf_new. }

(*TODO: MOVE*)
have initCore_sg: 
  forall cores sg ix v args c,
  initCore cores sg ix v args = Some c -> 
  Core.sg c=sg.
{ move=> p cores sg0 ? v args c; rewrite /initCore /=.
  by case: (initial_core _ _ _ _)=> // ?; case=> <-. }

have pf_sig':
    Core.sg (STACK.head st1' (callStack_nonempty st1')) 
  = Core.sg (STACK.head st2' (callStack_nonempty st2')).
{ rewrite st1'_eq /st2' /=. 
  rewrite (initCore_sg _ _ _ _ _ _ _ init1) 
          (initCore_sg _ _ _ _ _ _ _ init2)=> //. }

apply: Build_R.
exists pf_new',pf_sig',mu_new',[:: pkg & mus]; split=> //.
rewrite ->st1'_eq in *; rewrite /=.

have eq: Core.i c1 
       = Core.i (SeqStack.head (callStack (stack st1')) 
                (callStack_nonempty (stack st1'))).
{ by clear - st1'_eq; rewrite st1'_eq. }

exists eq; move: hdinv_new.
have hd_eq: 
  SeqStack.head (CallStack.callStack (stack st1')) (callStack_nonempty st1')
= c1.
{ by clear - st1'_eq; rewrite st1'_eq. }

clear - hd_eq; move: hd_eq eq pf_new'=> /=. 
set pf := (callStack_nonempty st1').
set q  := (SeqStack.head (CallStack.callStack (stack st1')) pf).
subst q=> -> eq; have ->: eq = erefl (Core.i c1) by apply: proof_irr.
rewrite cast_ty_erefl=> pf_new'.
by have ->: pf_new' = pf_new by apply: proof_irr.

have valid'': sm_valid pkg m1 m2 by apply: valid'.
have vinj'': 
  Forall2 (val_inject (restrict (as_inj pkg) (vis pkg))) args1 args2.
{ rewrite mu_pkg_as_inj; apply: restrict_forall_vals_inject=> //.
  move=> b H; move: (blocks_in_vis vinj); move/(_ b H).
  case/orP=> H2; apply/orP.
  by rewrite replace_locals_locBlocksSrc; left.
  by rewrite replace_locals_frgnBlocksSrc; right. }
have inj': Mem.inject (as_inj pkg) m1 m2.
{ by rewrite mu_pkg_as_inj. }
move: (head_tail_inv tlinv pf_sig valid'' atext1' atext2' inj' vinj'' pkg_hdinv).
rewrite /s1 /s2 st1'_eq /st2' /pkg /= => tlinv'. 
by rewrite st1_eq st2_eq; apply: tlinv'.
by rewrite st1'_eq /st2'; apply: (R_fntbl inv).
by apply: (R_ge inv).

{
apply: (R_ro1 inv).
}

{
apply: (R_ro2 inv).
}

{ apply: (frame_mmr1 inv). } 
{ apply: (frame_mmr2 inv). }

{
have sigOf1: sig_of (c inv) = Some (Core.sg c1).
{ move: (initCore_sg _ _ _ _ _ _ _ init1)=> X; clear -X atext1' defs1.
  case: c1 X=> /= => ? ? ? ->; rewrite /sig_of /=. 
  by move: atext1'; rewrite /= => ->. 
}

move: (R_tys1 inv); rewrite st1'_eq /=.
by rewrite /s1 st1_eq /= sigOf1=> ?; split.
}

have sigOf2: sig_of (d inv) = Some (Core.sg c2).
{ move: (initCore_sg _ _ _ _ _ _ _ init2)=> X; clear -X my_atext2.
  case: c2 X=> /= => ? ? ? ->; rewrite /sig_of /=. 
  by move: my_atext2; rewrite /= => ->. }

move: (R_tys2 inv); rewrite /st2' /=.
by rewrite /s2 st2_eq /= sigOf2=> ?; split.
Qed.

End call_lems.

