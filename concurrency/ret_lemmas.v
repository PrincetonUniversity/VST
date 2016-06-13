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

(* This file proves the main linking simulation result (see               *)
(* linking/linking_spec.v for the specification of the theorem that's     *)
(* proved).                                                               *)

Import Wholeprog_sim.
Import SM_simulation.
Import Linker. 
Import Modsem.

Section return_lems.

Variable N : pos.

Variable cores_S cores_T : 'I_N -> Modsem.t. 
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

Variable all_gvars_includedS: forall i b,
     gvars_included (Genv.find_var_info (cores_S i).(ge) b) (Genv.find_var_info my_ge b).

Variable all_gvars_includedT: forall i b,
     gvars_included (Genv.find_var_info (cores_T i).(ge) b) (Genv.find_var_info my_ge b).
(*
 Variable genvs_cohereS: forall m, mem_respects_readonly my_ge m ->
                        forall i, mem_respects_readonly (cores_S i).(ge) m.

  Variable genvs_cohereT: forall m, mem_respects_readonly my_ge m ->
                        forall i, mem_respects_readonly (cores_T i).(ge) m.
*)
Notation cast'  pf x := (cast (C \o cores_T) pf x).
Notation cast'' pf x := (cast (C \o cores_T) (sym_eq pf) x).
Notation rc_cast'  pf x := (cast (RC.state \o C \o cores_T) pf x).
Notation rc_cast'' pf x := (cast (RC.state \o C \o cores_T) (sym_eq pf) x).

Notation R := (@R N cores_S cores_T rclosed_S nucular_T sims my_ge). 

Context
(mu : Inj.t) m1 m2 rv1 st1''
(st1 st1' : linker N cores_S) cd st2  
(valid : sm_valid mu m1 m2)
(hlt1 : LinkerSem.halted0 st1 = Some rv1)
(pop1 : popCore st1 = Some st1'')
(inv : R cd mu st1 m1 st2 m2).

Lemma hlt2 : exists rv2, LinkerSem.halted0 st2 = Some rv2.
Proof.
case: (R_inv inv)=> pf []pf_sig []mu_top []mus []mu_eq.
move=> []pf2 hdinv tlinv.
move: hlt1; rewrite /LinkerSem.halted0.
case hlt10: (halted _ _)=> //[rv].
case hasty: (val_casted.val_has_type_func _ _)=> //. 
case=> Heq; subst rv1.
case: (core_halted (sims (Core.i (peekCore st1)))
       _ _ _ _ _ _ (head_match hdinv) hlt10)
       => rv2 []inj12 []mmr1 []mmr2 []vinj hlt2.
exists rv2.
set T := C \o cores_T.
set P := fun sg ix (x : T ix) => 
  match
     halted (sem (cores_T ix)) x
  with
   | Some mv =>
       if val_casted.val_has_type_func mv (proj_sig_res sg)
       then Some mv
       else None
   | None => None
   end = Some rv2.
change (P (Core.sg (peekCore st2)) 
          (Core.i (peekCore st2)) (Core.c (peekCore st2))).
apply: (cast_indnatdep'' (j := Core.i (peekCore st1))).
rewrite /P; move: hlt2; rewrite /= /RC.halted /= => ->. 
have H: val_casted.val_has_type_func rv2 (proj_sig_res (Core.sg (peekCore st2))).
{ move: hlt1; rewrite /LinkerSem.halted0.
  case: (halted _ _)=> //[rv'].
  case hasty': (val_casted.val_has_type_func _ _)=> //; case=> veq; subst rv'.
  have ->: Core.sg (peekCore st2)=Core.sg (peekCore st1). 
  { by clear -pf_sig; move: pf_sig; rewrite /c /d /s1 /s2 /peekCore /= => ->. }
  move: hasty'; move/val_casted.val_has_type_funcP=> hasty'.
  apply/val_casted.val_has_type_funcP.
  apply: (val_casted.valinject_hastype' _ _ _ vinj)=> //.
  case: hdinv=> _ _; case=> B []_ I _ _ _.
  by move=> C; move: (RCSem.halted_ax I hlt10); rewrite C. }
by rewrite H.
Qed.

Lemma pop2 : exists st2'', popCore st2 = Some st2''.
Proof.
move: pop1; case/popCoreE=> pf []inCtx1 st1''_eq.
have inCtx2: inContext st2.
  by apply: (R_inContext inv inCtx1).
have pf': wf_callStack (STACK.pop (CallStack.callStack st2)).
  apply: inContext_wf=> //.
  by apply: CallStack.callStack_wf.
exists (updStack st2 
  (CallStack.mk (STACK.pop (CallStack.callStack st2)) pf')).
by apply: popCoreI.
Qed.

Require Import mem_welldefined.

Context (aft1 : LinkerSem.after_external (Some rv1) st1'' = Some st1').

Lemma aft2 : 
  exists rv2 st2'' (st2' : linker N cores_T) cd' mu', 
  [/\ LinkerSem.halted0 st2 = Some rv2
    , inContext st2
    , popCore st2 = Some st2''
    , LinkerSem.after_external (Some rv2) st2'' = Some st2'
    & R cd' mu' st1' m1 st2' m2].
Proof.
case: (R_inv inv)=> pf []pf_sig []mu_top []mus []mu_eq.
move=> []pf_hd hdinv tlinv.
move: hlt1; rewrite /LinkerSem.halted0=> hlt100.
move: hlt100; case hlt10: (halted _ _)=> //[rv1'].
case hasty1: (val_casted.val_has_type_func _ _)=> //; case=> X; subst rv1'.

move: (R_tys1 inv); rewrite /s1=> tys1.
move: (R_tys2 inv); rewrite /s2=> tys2.

case: (core_halted (sims (Core.i (peekCore st1)))
       _ _ _ _ _ _ (head_match hdinv) hlt10)
       => rv2 []inj12 []mmr1 []mmr2 []vinj hlt2.

have hasty2: (val_casted.val_has_type_func rv2 (proj_sig_res (Core.sg (peekCore st2)))).
{ move: pf_sig hasty1; rewrite /c /d /s1 /s2 /peekCore /= => ->.
  move/val_casted.val_has_type_funcP=> hasty1.
  apply/val_casted.val_has_type_funcP.
  apply: (val_casted.valinject_hastype' _ _ _ vinj)=> //.
  case: hdinv=> _ _; case=> B []_ I _ _ _.
  by move=> C; move: (RCSem.halted_ax I hlt10); rewrite C. }

exists rv2.
case: pop2=> st2'' pop2.

case: (LinkerSem.after_externalE _ _ aft1)=> fntbl []hd1 []hd1' []tl1.
move=> []pf1 []pf2 []e1 []esig []st1''_eq st1'_eq aft1'; exists st2''.
rewrite /s1 /s2 in tlinv.

have [hd2 [tl2 [pf20 st2''_eq]]]:
  exists hd2 tl2 pf2,
  st2'' = {| fn_tbl := fntbl; stack := CallStack.mk (hd2::tl2) pf2 |}.
{ case: (popCoreE _ pop2)=> wf_pf []inCtx2 st2''_eq.
  move: wf_pf st2''_eq; rewrite /updStack.
  case: (STACK.pop (CallStack.callStack st2))=> // x0 xs wf_pf ->.
  exists x0,xs,wf_pf; f_equal=> //; rewrite -(R_fntbl inv).
  by case: (popCoreE _ pop1)=> ? []_; rewrite st1''_eq; case. }

rewrite st2''_eq.

have [mu0 [mus' mus_eq]]:
  exists mu0 mus',
  mus = [:: mu0 & mus'].
{ clear - pop1 pop2 tlinv; case: mus pop1 pop2 tlinv.
  case/popCoreE=> []wf_pf1 []_ eq1; case/popCoreE=> []wf_pf2 []_ eq2.
  move: wf_pf1 eq1; case: (STACK.pop (CallStack.callStack st1))=> // x0 xs ? ?.
  move: wf_pf2 eq2; case: (STACK.pop (CallStack.callStack st2))=> // y0 ys ? ?.
  by case.
  by move=> mu0 mus' ? ? ?; exists mu0,mus'. }

case: (tlinv)=> allrelinv frameall.
rewrite mus_eq /tail_inv in tlinv.
case: tlinv=> allinv tlinv; move: tlinv=> /=.
case: mu0 mus_eq allinv=> /= mu0 m10 m20 mu0_val mus_eq []all0 allinv.

simpl in frameall.
case: (popCoreE _ pop1)=> pf_wf1 []ctx1.
rewrite /updStack st1''_eq; case=> fntbleq1 eq1; rewrite -eq1 in frameall|-*.
case: (popCoreE _ pop2)=> pf_wf2 []ctx2.
rewrite /updStack st2''_eq; case=> fntbleq2 eq2; rewrite -eq2 in frameall|-*.
move {eq1 eq2}.
case; case=> pf0 []pf_sig0 []cd0 []x0 []sig01 []vals01 []e0 []sig02 []vals02.
move=> fr0 frametail.

move: (frame_inj0 fr0)=> inj0.
move: (frame_match fr0)=> mtch0.
move: (frame_at1 fr0)=> at01.
move: (frame_at2 fr0)=> at02.
move: (frame_vinj fr0)=> vinj0.
move: (frame_fwd1 fr0)=> fwd1.
move: (frame_fwd2 fr0)=> fwd2.
move: (frame_unch1 fr0)=> unch1.
move: (frame_unch2 fr0)=> unch2.

have at02':
  at_external (sem (cores_T (Core.i hd1)))
    (cast'' pf0 (Core.c hd2)) = Some (e0,sig02,vals02).
{ by rewrite /= -at02; f_equal. }

(* nu = leak-out(mu0) -- mu0 is callee *)

set pubSrc' := fun b => 
  locBlocksSrc mu0 b && REACH m10 (exportedSrc mu0 vals01) b.
set pubTgt' := fun b => 
  locBlocksTgt mu0 b && REACH m20 (exportedTgt mu0 vals02) b.
set nu := replace_locals mu0 pubSrc' pubTgt'.

have mu0_wd: SM_wd mu0.
{ by apply: Inj_wd. }

have vinj0': Forall2 (val_inject (as_inj mu0)) vals01 vals02.
{ by apply: (forall_vals_inject_restrictD _ _ _ _ vinj0). }

have [nu_wd [nu_valid0 [nu_inj0 nu_vinj]]]:
  SM_wd nu
  /\ sm_valid nu m10 m20 
  /\ Mem.inject (as_inj nu) m10 m20 
  /\ Forall2 (val_inject (as_inj nu)) vals01 vals02.
{ by apply: (eff_after_check1 
  _ mu0_wd 
  _ _ mu0_val
  inj0 
  _ _ vinj0' 
  pubSrc' erefl
  pubTgt' erefl 
  nu erefl). }

(* nu' = reestablish nu w/r/t mu_top *)

set nu' := reestablish nu mu_top.  

have restrict_mu_top_nu:
  restrict (as_inj mu_top) (DomSrc nu) = as_inj nu.
{ (*edit: Santiago*)
  rewrite /nu lo_DomSrc replace_locals_as_inj; extensionality b.
  move: (head_rel hdinv). rewrite mus_eq /= =>[] []. 
  case=> /= incr_mu0_top sep_mu0_top gsep_mu0_top disj_mu0_top _ _.
  case incr_mu0_top => incr [incrS incrT].
  destruct (as_inj mu0 b) eqn:map1.
  - move: p map1. case => b0 d map1.
    have DS: DomSrc mu0 b = true.
    { move: map1; move /(as_inj_DomRng). move => HH. move/HH: mu0_wd => [] //. }
    rewrite /restrict DS.
    by apply: incr =>  //=.
  - rewrite /restrict. destruct (DomSrc mu0 b) eqn:DS=> //=.
    (*have DS': DomSrc mu_top b = true by apply: incrS.*)
    case map: (as_inj mu_top b) => [p|] .
    + exfalso; move: map; case p => b2 d.
      case (sep_mu0_top) => sep0 []sep1 sep2 map2.
      case (sep0 b b2 d map1 map2).
      by rewrite DS; discriminate.
    + reflexivity. }

  (*Old proof 
  rewrite /restrict /as_inj /join; extensionality b.
  move: (head_rel hdinv); rewrite mus_eq /= => [][]. 
  case=> /= incr_mu0_top sep_mu0_top disj_mu0_top _ _.
  case e: (DomSrc nu b)=> //. 
  { 
  case eOf_nu: (extern_of nu b)=> [[x' y']|].  
  rewrite /nu replace_locals_extern in eOf_nu.
  case eOf_top: (extern_of mu_top b)=> [[x'' y'']|].
  case: incr_mu0_top; rewrite /as_inj /join.
  by move/(_ b x' y'); rewrite eOf_nu eOf_top=> H1 H2; apply: H1.
  case: incr_mu0_top; rewrite /as_inj /join; move/(_ b x' y').
  by rewrite eOf_nu eOf_top=> H1 H2; apply: H1.
  rewrite /nu replace_locals_extern in eOf_nu.
  rewrite /nu replace_locals_DomSrc in e.
  case eOf_top: (extern_of mu_top b)=> [[x' y']|].
  case lOf_nu: (local_of nu b)=> [[x'' y'']|].
  case: incr_mu0_top=> inj_incr []H1 H2.  
  move: (inj_incr b x'' y''); rewrite /as_inj /join.
  rewrite /nu replace_locals_local in lOf_nu.
  by rewrite eOf_nu eOf_top lOf_nu; apply.
  have Contra: False.
  { case: sep_mu0_top; move/(_ b x' y').
    rewrite /nu replace_locals_local in lOf_nu.
    rewrite /as_inj /join eOf_nu lOf_nu eOf_top; case=> //.
    by rewrite e.
  } by elimtype False; apply: Contra.
  have local_of_mu_top_nu: local_of mu_top b = local_of nu b.
  { case: incr_mu0_top=> inj_incr []H1 H2.
    case lOf_nu: (local_of nu b)=> [[x' y']|].
    rewrite /nu replace_locals_local in lOf_nu.
    case lOf_top: (local_of mu_top b)=> [[x'' y'']|].
    move: (inj_incr b x' y'); rewrite /as_inj /join.
    by rewrite lOf_nu lOf_top eOf_nu eOf_top; apply.
    move: (inj_incr b x' y'); rewrite /as_inj /join.
    by rewrite lOf_nu lOf_top eOf_nu eOf_top; move/(_ erefl).
    rewrite /nu replace_locals_local in lOf_nu.
    case lOf_top: (local_of mu_top b)=> //[[x' y']].
    case: (local_locBlocks _ (Inj_wd _) _ _ _ lOf_top).
    case: sep_mu0_top; move/(_ b x' y').
    rewrite /as_inj /join eOf_nu lOf_nu eOf_top lOf_top; case=> //.
    by rewrite e. 
  } by apply: local_of_mu_top_nu.
  }
  case eOf_nu: (extern_of nu b)=> [[x' y']|].
  rewrite /nu replace_locals_extern in eOf_nu.
  case: (extern_DomRng' _ (Inj_wd _) _ _ _ eOf_nu).
  move=> _ []_ []_ []_ []_ []_ []dSrc _.
  by rewrite /nu replace_locals_DomSrc dSrc in e.
  case lOf_nu: (local_of nu b)=> //[[x' y']].
  rewrite /nu replace_locals_local in lOf_nu.
  case: (local_DomRng _ (Inj_wd _) _ _ _ lOf_nu)=> H1 _.  
  by rewrite /DomSrc /nu replace_locals_locBlocksSrc H1 /= in e. }*)

have asInj_nu'_mu_top: as_inj nu' = as_inj mu_top.
{ by apply: reestablish_as_inj. }

(* Old proof
  rewrite /nu' /as_inj reestablish_local_of reestablish_extern_of /nu
          replace_locals_locBlocksSrc replace_locals_local.
   move: (head_rel hdinv). rewrite mus_eq /= =>[] []. 
  case=> /= incr_mu0_top locinv sep_mu0_top disj_mu0_top _ _.    
  rewrite locinv /as_inj /join /restrict.
  extensionality b.
  destruct (locBlocksSrc mu0 b) eqn:locS0.
  - reflexivity. 
  - destruct (extern_of mu_top b) eqn:extmap.
    + destruct p; reflexivity.
    + destruct (local_of mu_top b); try destruct p; reflexivity. }*)

have nu'_vinj: val_inject (as_inj nu') rv1 rv2.
{ rewrite asInj_nu'_mu_top.
  by apply: (val_inject_restrictD _ _ _ _ vinj). }

move: (head_rel hdinv); rewrite mus_eq /= => [][].  
case=> /= incr0_top sep0_top gsep0_top disj0_top _ _.

have extsrc_nu_top b: extBlocksSrc nu b -> DomSrc mu_top b.
{ rewrite /nu replace_locals_extBlocksSrc=> H1.
  case: incr0_top=> _ []; move/(_ b); rewrite /DomSrc H1.
  by move=> H2 _; apply: H2; apply/orP; right. }

have exttgt_nu_top b: extBlocksTgt nu b -> DomTgt mu_top b.
{ rewrite /nu replace_locals_extBlocksTgt=> H1.
  case: incr0_top=> _ [] _; move/(_ b); rewrite /DomTgt H1.
  by apply; apply/orP; right. }

have nu_nu'_eincr: extern_incr nu nu'.
{ apply: reestablish_extern_incr=> //; by apply: Inj_wd. }

have locsrc_nu_top b: locBlocksSrc nu b -> DomSrc mu_top b.
{ rewrite /nu replace_locals_locBlocksSrc=> H1.
  case: incr0_top=> _ []; move/(_ b); rewrite /DomSrc H1.
  by move=> H2 _; apply: H2. }

have loctgt_nu_top b: locBlocksTgt nu b -> DomTgt mu_top b.
{ rewrite /nu replace_locals_locBlocksTgt=> H1.
  by case: incr0_top=> _ [] _; move/(_ b); rewrite /DomTgt H1; apply. }

(*Obsolete *)
(*have nu_nu'_sep: sm_inject_separated nu nu' m10 m20.
{ apply: reestablish_sm_injsep=> //; first by apply: Inj_wd.
  by apply: sm_inject_separated_replace_locals. }*)

(* This version is just FALSE in general:
have nu_nu'_sep: sm_inject_separated' nu nu' m10 m20.
{ ad_it. } *)

(*New *)
Lemma gsep_change_env {V V'} {F F'} (ge: Genv.t V F) (ge': Genv.t V' F') mu1 mu2:
  genvs_domain_eq ge ge' ->
  globals_separate ge mu1 mu2 ->
  globals_separate ge' mu1 mu2.
  case => A []B C.
  rewrite /globals_separate /isGlobalBlock /genv2blocksBool /=.
  move => H1 b1 b2 d H2 H3. move: (H1 _ _ _ H2 H3).
  move: A B; rewrite /genv2blocks /=; move => A B.
  
  case one':(Genv.invert_symbol ge b2) =>  //.
  have one:(Genv.invert_symbol ge' b2 = None).
  { case one:(Genv.invert_symbol ge' b2)=>  [ a|]; last by reflexivity.
    apply Genv.invert_find_symbol in one.
    have ONE:(exists a, Genv.find_symbol ge' a = Some b2) by exists a; auto.
    apply A in ONE; case ONE => a' ONE'.   
    apply Genv.find_invert_symbol in ONE'.
    rewrite one' in ONE'; discriminate. }
  
  case two':(Genv.find_var_info ge b2) =>  //.
  have two:(Genv.find_var_info ge' b2 = None).
  { case two:(Genv.find_var_info ge' b2)=>  [ a|]; last by reflexivity.
    have TWO:(exists a, Genv.find_var_info ge' b2 = Some a) by exists a; auto.
    apply B in TWO; case TWO => a' TWO'.  
    rewrite two' in TWO'; discriminate. }
    by rewrite one two.
Qed.

have nu_nu'_gsep: globals_separate (ge (cores_T (Core.i hd1))) nu nu'.
{ apply (@gsep_change_env _ _ _ _ _ _ _ _ (my_ge_T (Core.i hd1))).
  have : (SM_wd nu) by auto.
  rewrite /globals_separate /nu' /nu. move => _ b1 b2 d.
  rewrite replace_locals_as_inj reestablish_as_inj //.
          
  rewrite /globals_separate in gsep0_top.
  intros.
  by eapply (gsep0_top b1 b2 d); auto.
}
  
(*  May want to make it into a lemma. This one is wrong:
  Lemma reestablish_globals_separate:
    forall F V ge (mu0 mu : SM_Injection),
       SM_wd mu0 ->
       SM_wd mu ->
       restrict (as_inj mu) (DomSrc mu0) = as_inj mu0 ->
       (forall b : block, locBlocksSrc mu0 b = true -> DomSrc mu b = true) ->
       (forall b : block, locBlocksTgt mu0 b = true -> DomTgt mu b = true) ->
       forall m1 m2 : Memory.mem,
       globals_separate(F:=F)(V:=V) ge mu0 mu ->
       globals_separate ge mu0 (reestablish mu0 mu).
    clear.
    move => ? ? ge mu mu' wd wd' rest HHS HHT m1 m2.
    rewrite /globals_separate.
    intros. eapply H; eauto.
    move: H1. rewrite reestablish_as_inj; eauto. 
  Qed.
  eapply reestablish_globals_separate; eauto.
  case mu_top; auto.
}*)


have nu'_wd: SM_wd nu'.
{ apply: reestablish_wd=> //; first by apply: Inj_wd.
  case: sep0_top=> H1 _; rewrite /nu. 
  rewrite replace_locals_DomSrc replace_locals_DomTgt. 
  by rewrite replace_locals_as_inj. }

have nu'_valid: sm_valid nu' m1 m2.
{ apply: reestablish_sm_valid=> //.
  by apply: Inj_wd.
  by apply: (head_valid hdinv). }

have nu'_inj: Mem.inject (as_inj nu') m1 m2.
{ by rewrite /nu' reestablish_as_inj. }

set frgnSrc' := fun b => 
  [&& DomSrc nu' b, ~~locBlocksSrc nu' b
    & REACH m1 (exportedSrc nu' [:: rv1]) b].
set frgnTgt' := fun b => 
  [&& DomTgt nu' b, ~~locBlocksTgt nu' b
    & REACH m2 (exportedTgt nu' [:: rv2]) b].

(* mu' = leak-in(nu') *)

set mu' := replace_externs nu' frgnSrc' frgnTgt'.

have sgeq1: Core.sg (peekCore st1)=ef_sig x0. 
{ clear -tys1 at01 st1''_eq pop1; move: tys1; rewrite /peekCore.
  case: (popCoreE _ pop1)=> wf []_ st1''_eq2. 
  rewrite st1''_eq2 in st1''_eq; move: st1''_eq; case=> _ /=. 
  clear -at01; case: st1=> /= _; case; case=> // a l _ /= => -> /=.
  by rewrite /sig_of; rewrite at01; case. }

have hasty_rv1: Val.has_type rv1 (proj_sig_res (ef_sig x0)).
{ by move: hasty1; move/val_casted.val_has_type_funcP; rewrite -sgeq1. }

have sgeq2: Core.sg (peekCore st2)=ef_sig e0. 
{ clear -tys2 at02 st2''_eq pop2; move: tys2; rewrite /peekCore.
  case: (popCoreE _ pop2)=> wf []_ st2''_eq2. 
  rewrite st2''_eq2 in st2''_eq; move: st2''_eq; case=> _ /=. 
  clear -at02; case: st2=> /= _; case; case=> // a l _ /= => -> /=.
  rewrite /sig_of. 
  have at02': at_external (sem (cores_T (Core.i hd2))) (Core.c hd2) =
              Some (e0, sig02, vals02). 
  { set T := C \o cores_T.  
    set P := fun ix (x : T ix) =>
      at_external (sem (cores_T ix)) x = Some (e0,sig02,vals02).
    move: at02.
    change (P (Core.i hd1) (cast T (sym_eq pf0) (Core.c hd2)) 
         -> P (Core.i hd2) (Core.c hd2)).
    by apply: cast_indnatdep'. }
  by rewrite at02'; case. }

have hasty_rv2: Val.has_type rv2 (proj_sig_res (ef_sig e0)).
{ by move: hasty2; move/val_casted.val_has_type_funcP; rewrite -sgeq2. }

have [hd2' [pf_eq22' [pf_sig22' [pf_eq12' [pf_sig12' [cd' [aft2' mtch12']]]]]]]:
  exists hd2' (pf_eq22' : Core.i hd2 = Core.i hd2') 
              (pf_sig22' : Core.sg hd2 = Core.sg hd2')
              (pf_eq12' : Core.i hd1' = Core.i hd2')
              (pf_sig12' : Core.sg hd1' = Core.sg hd2')
         cd',
  [/\ after_external (sem (cores_T (Core.i hd2)))
        (Some rv2) (Core.c hd2) 
      = Some (cast'' pf_eq22' (Core.c hd2'))
    & match_state (sims (Core.i hd1')) cd' mu' 
      (Core.c hd1') m1 (cast'' pf_eq12' (Core.c hd2')) m2].
{ case: (popCoreE _ pop2)=> wf_pf []inCtx2 st2''_eq'.
  rewrite st2''_eq' in st2''_eq.
  rewrite /updStack in st2''_eq; case: st2''_eq=> fntbl_eq pop2_eq'.
  (*assert (nu_nu'_gsep: globals_separate (ge (cores_T (Core.i hd1))) nu nu').
  { move: nu_nu'_sep; unfold globals_separate; unfold sm_inject_separated.
    intros. destruct (nu_nu'_sep) as [a  [b c]]. 
    destruct (a _ _ _ H H0) as [DSfalse DTfalse]. }*)
  assert (RDS: RDOnly_fwd m10 m1 (ReadOnlyBlocks (ge (cores_S (Core.i hd1))))).
        specialize (frame_rdoS fr0); intros RD_S. red; intros. eapply RD_S.
        unfold ReadOnlyBlocks in Hb. remember (Genv.find_var_info (ge (cores_S (Core.i hd1))) b) as d.
       destruct d; inv Hb. assert (GV:=all_gvars_includedS  (Core.i hd1) b). rewrite <- Heqd in GV. 
        red in GV. unfold ReadOnlyBlocks. destruct (Genv.find_var_info my_ge b ); try contradiction.
       destruct GV as [? [? ?]]. rewrite H1 H2. trivial.
  assert (RDT: RDOnly_fwd m20 m2 (ReadOnlyBlocks (ge (cores_T (Core.i hd1))))).
        specialize (frame_rdoT fr0); intros RD_T. red; intros. eapply RD_T.
        unfold ReadOnlyBlocks in Hb. remember (Genv.find_var_info (ge (cores_T (Core.i hd1))) b) as d.
       destruct d; inv Hb. assert (GV:=all_gvars_includedT  (Core.i hd1) b). rewrite <- Heqd in GV. 
        red in GV. unfold ReadOnlyBlocks. destruct (Genv.find_var_info my_ge b ); try contradiction.
       destruct GV as [? [? ?]]. rewrite H1 H2. trivial.

  move: (@eff_after_external
  _ _ _ _ _ _ _ _ 
  _ _  
  (sims (Core.i hd1))
  _ _ _ _ _ _ _ _ _ _ _ _
  inj0 mtch0 at01 at02' vinj0

  pubSrc' erefl pubTgt' erefl nu erefl

  nu' rv1 m1 rv2 m2

  hasty_rv1 hasty_rv2 nu_nu'_eincr nu_nu'_gsep
  nu'_wd nu'_valid nu'_inj nu'_vinj
  fwd1 fwd2 RDS RDT

  frgnSrc' erefl frgnTgt' erefl mu' erefl

  unch1 unch2).
  case=> cd' []c0' []d0' []aft1'' []aft2'' mtch12'.
  exists (Core.mk _ cores_T (Core.i hd1) d0' (Core.sg hd1)). 
  exists (sym_eq pf0). 
  exists (sym_eq pf_sig0).
  exists (sym_eq e1)=> /=.
  exists (sym_eq esig).
  exists (cast (fun ix => core_data (sims ix)) e1 cd'); split=> //.
  
  move: aft2''.
  set T := C \o cores_T.  
  set P := fun ix (x : T ix) (y : T ix) => 
    after_external (sem (cores_T ix)) (Some rv2) x = Some y.
  change (P (Core.i hd1) (cast T (sym_eq pf0) (Core.c hd2)) d0'
       -> P (Core.i hd2) (Core.c hd2) (cast T (sym_eq (sym_eq pf0)) d0')).
  have ->: sym_eq (sym_eq pf0) = pf0 by apply: proof_irr.
  by apply: cast_indnatdep2.

  move: mtch12'.
  have ->: sym_eq (sym_eq e1) = e1 by apply: proof_irr.
  rewrite aft1' in aft1''; case: aft1''=> <-.
  set T := (fun ix => core_data (sims ix)).
  set U := C \o cores_S.
  set V := C \o cores_T.
  set P := fun ix (x : T ix) (y : U ix) (z : V ix) => 
    match_state (sims ix) x mu' y m1 z m2.
  change (P (Core.i hd1) cd' (cast U (sym_eq e1) (Core.c hd1')) d0'
       -> P (Core.i hd1') (cast T e1 cd') (Core.c hd1') (cast V e1 d0')).
  by apply: cast_indnatdep33. }

set st2' := {| fn_tbl := fntbl; stack := CallStack.mk (hd2'::tl2) pf20 |}.

exists st2'. 
exists (existT _ (Core.i hd1') cd'). 
exists mu'.

split=> //.

have hlt02': 
  (halted (sem (cores_T (Core.i (peekCore st2)))) (Core.c (peekCore st2))
   = Some rv2).
{ set T := C \o cores_T.
  set P := fun ix (x : T ix) => 
   halted (sem (cores_T ix)) x = Some rv2.
  move: hlt2.
  change (P (Core.i (peekCore st1)) (cast T (sym_eq pf) (Core.c (d inv)))
       -> P (Core.i (peekCore st2)) (Core.c (peekCore st2))).
  by apply: cast_indnatdep'. }

rewrite hlt02' sgeq2.
have ->: val_casted.val_has_type_func rv2 (proj_sig_res (ef_sig e0)).
{ by apply/val_casted.val_has_type_funcP. }
by [].         

by rewrite pop2 st2''_eq.

{ rewrite /st2'; move: aft2'.
rewrite /LinkerSem.after_external /= => -> /=. 
rewrite /SeqStack.updStack /Core.upd.
do 3 f_equal; first by move=> ? ?; case=> -> ->.
f_equal; clear - hd2' pf_eq22' pf_sig22'; destruct hd2'=> /=.
by rewrite pf_sig22'; rewrite ->pf_eq22'=> /=; f_equal=> //. 
by apply: proof_irr. }

apply: Build_R=> /=.
rewrite st1'_eq; exists pf_eq12', pf_sig12'.

have mu'_wd : SM_wd mu'.
{ case: (eff_after_check2 nu' rv1 m1 m2 rv2 nu'_inj nu'_vinj
        frgnSrc' erefl frgnTgt' erefl mu' erefl nu'_wd nu'_valid)=> H1 H2.
  by apply: H1. }

have mu'_valid : sm_valid mu' m1 m2.
{ case: (eff_after_check2 nu' rv1 m1 m2 rv2 nu'_inj nu'_vinj
        frgnSrc' erefl frgnTgt' erefl mu' erefl nu'_wd nu'_valid)=> H1 H2.
  by apply: H2. }

have mu0_mu'_inject_incr : inject_incr (as_inj mu0) (as_inj mu').
{ by apply: (eff_after_check4 mu0 pubSrc' pubTgt' nu erefl nu' nu_nu'_eincr
            mu' frgnSrc' frgnTgt' erefl nu'_wd). }

have mu0_in: In (Inj.mu mu0) 
                [seq (Inj.mu \o frame_mu0) x | x <- mus].
{ by rewrite mus_eq /=; left. }

have mu0_mu'_incr : incr mu0 mu'.
{ split=> //; split=> b0.
  rewrite /DomSrc; case/orP; rewrite /mu' replace_externs_locBlocksSrc /nu'.
  by rewrite reestablish_locBlocksSrc /nu replace_locals_locBlocksSrc=> ->.
  rewrite /mu' replace_externs_extBlocksSrc /nu'.
  rewrite reestablish_extBlocksSrc /nu replace_locals_locBlocksSrc=> E.
  have lN: locBlocksSrc mu0 b0 = false.
  { by move: (extBlocksSrc_locBlocksSrc _ (Inj_wd _) _ E). }
  rewrite lN; apply/orP; right.
  move: (head_rel hdinv); rewrite mus_eq /=; case; case=> /=; case.
  move=> _; case; move/(_ b0)=> H _ _ _ _ _ _; apply: H.
  by rewrite /DomSrc E; apply/orP; right.

  rewrite /DomTgt; case/orP; rewrite /mu' replace_externs_locBlocksTgt /nu'.
  by rewrite reestablish_locBlocksTgt /nu replace_locals_locBlocksTgt=> ->.
  rewrite /mu' replace_externs_extBlocksTgt /nu'.
  rewrite reestablish_extBlocksTgt /nu replace_locals_locBlocksTgt=> E.
  have lN: locBlocksTgt mu0 b0 = false.
  { by move: (extBlocksTgt_locBlocksTgt _ (Inj_wd _) _ E). }
  rewrite lN; apply/orP; right.
  move: (head_rel hdinv); rewrite mus_eq /=; case; case=> /=; case.
  move=> _; case=> _; move/(_ b0)=> H _ _ _ _ _; apply: H.
  by rewrite /DomTgt E; apply/orP; right. }

have as_inj_mu'_mu_top : as_inj mu' = as_inj mu_top.
{ by rewrite replace_externs_as_inj asInj_nu'_mu_top. }

have locS_mu'_mu_top : locBlocksSrc mu' = locBlocksSrc nu.
{ by rewrite /mu' /nu' replace_externs_locBlocksSrc reestablish_locBlocksSrc. }

have locT_mu'_mu_top : locBlocksTgt mu' = locBlocksTgt nu.
{ by rewrite /mu' /nu' replace_externs_locBlocksTgt reestablish_locBlocksTgt. }

have DomSrc_mu'_mu_top : DomSrc mu' = DomSrc mu_top .
{ by rewrite /mu' replace_externs_DomSrc reestablish_DomSrc. }

have DomTgt_mu'_mu_top : DomTgt mu' = DomTgt mu_top.
{ by rewrite /mu' replace_externs_DomTgt reestablish_DomTgt. }

have mu_top_mu'_incr : incr mu_top mu'.
{ split; first by rewrite as_inj_mu'_mu_top; apply: inject_incr_refl.
  split; first by rewrite DomSrc_mu'_mu_top.
  by rewrite DomTgt_mu'_mu_top. }

have locBlocksSrc_mu'_eq : locBlocksSrc mu' = locBlocksSrc mu0.
{ rewrite /mu' replace_externs_locBlocksSrc /nu'.
  by rewrite reestablish_locBlocksSrc /nu replace_locals_locBlocksSrc. }

have locBlocksTgt_mu'_eq : locBlocksTgt mu' = locBlocksTgt mu0.
{ rewrite /mu' replace_externs_locBlocksTgt /nu'.
  by rewrite reestablish_locBlocksTgt /nu replace_locals_locBlocksTgt. }

have extBlocksSrc_mu'_eq : 
  extBlocksSrc mu' 
= (fun b => if locBlocksSrc mu0 b then false else DomSrc mu_top b).
{ rewrite /mu' replace_externs_extBlocksSrc /nu'.
  by rewrite reestablish_extBlocksSrc /nu replace_locals_locBlocksSrc. }

have extBlocksTgt_mu'_eq : 
  extBlocksTgt mu' 
= (fun b => if locBlocksTgt mu0 b then false else DomTgt mu_top b).
{ rewrite /mu' replace_externs_extBlocksTgt /nu'.
  by rewrite reestablish_extBlocksTgt /nu replace_locals_locBlocksTgt. }

have frgnBlocksSrc_mu'_eq : frgnBlocksSrc mu' = frgnSrc'.
{ by rewrite /mu' replace_externs_frgnBlocksSrc. }

have frgnBlocksTgt_mu'_eq : frgnBlocksTgt mu' = frgnTgt'.
{ by rewrite /mu' replace_externs_frgnBlocksTgt. }

have subFS: {subset frgnBlocksSrc mu0 <= frgnSrc'}.
{ rewrite /frgnSrc' /nu'=> b0; rewrite /in_mem /= => H.
  rewrite /DomSrc reestablish_locBlocksSrc /nu.
  rewrite replace_locals_locBlocksSrc.
  rewrite reestablish_extBlocksSrc.
  rewrite replace_locals_locBlocksSrc.
  have lN: locBlocksSrc mu0 b0 = false.
  { by move: (extBlocksSrc_locBlocksSrc _ (Inj_wd _) _ (frgnsrc_sub_extsrc H)). }
  rewrite lN /=.
  rewrite /exportedSrc sharedSrc_iff_frgnpub.
  rewrite reestablish_frgnBlocksSrc.
  rewrite replace_locals_frgnBlocksSrc.
  have pub_eq: 
    pubBlocksSrc (reestablish (replace_locals mu0 pubSrc' pubTgt') mu_top)
    = pubBlocksSrc (replace_locals mu0 pubSrc' pubTgt').
  { by rewrite reestablish_pubBlocksSrc. }
  rewrite pub_eq replace_locals_pubBlocksSrc; apply/andP; split.
  case: incr0_top=> _; case; move/(_ b0)=> H2 _.
  apply: H2; rewrite /DomSrc.
  move: (frgnsrc_sub_extsrc H). 
  by rewrite /in_mem /= => ->; apply/orP; right.
  by apply: REACH_nil; apply/orP; right; apply/orP; left.
  by apply: nu'_wd. }

have subFT: {subset frgnBlocksTgt mu0 <= frgnTgt'}.
{ rewrite /frgnTgt' /nu'=> b0; rewrite /in_mem /= => H.
  rewrite /DomTgt reestablish_locBlocksTgt /nu.
  rewrite replace_locals_locBlocksTgt.
  rewrite reestablish_extBlocksTgt.
  rewrite replace_locals_locBlocksTgt.
  have lN: locBlocksTgt mu0 b0 = false.
  { by move: (extBlocksTgt_locBlocksTgt _ (Inj_wd _) _ (frgntgt_sub_exttgt H)). }
  rewrite lN /=.
  rewrite /exportedTgt /sharedTgt. 
  rewrite reestablish_frgnBlocksTgt replace_locals_frgnBlocksTgt.
  have pub_eq: 
    pubBlocksTgt (reestablish (replace_locals mu0 pubSrc' pubTgt') mu_top)
    = pubBlocksTgt (replace_locals mu0 pubSrc' pubTgt').
  { by rewrite reestablish_pubBlocksTgt. }
  rewrite pub_eq replace_locals_pubBlocksTgt; apply/andP; split.
  case: incr0_top=> _; case; move/(_ b0)=> _ H2.
  apply: H2; rewrite /DomTgt.
  move: (frgntgt_sub_exttgt H). 
  by rewrite /in_mem /= => ->; apply/orP; right.
  by apply: REACH_nil; apply/orP; right; apply/orP; left. }

have shrdS_mu0_mu': {subset sharedSrc mu0 <= sharedSrc mu'}.
{ move=> b0; rewrite !sharedSrc_iff_frgnpub=> //; case/orP=> F.
  apply/orP; left; rewrite frgnBlocksSrc_mu'_eq.
  by apply: subFS.
  rewrite /mu' replace_externs_pubBlocksSrc /nu'.
  rewrite reestablish_pubBlocksSrc /nu replace_locals_pubBlocksSrc.
  apply/orP; right; rewrite /pubSrc'; apply/andP; split.
  by apply: pubsrc_sub_locsrc.
  apply: REACH_nil; apply/orP; right; rewrite sharedSrc_iff_frgnpub.
  by apply/orP; right.
  by apply: Inj_wd. }

have shrdT_mu0_mu': {subset sharedTgt mu0 <= sharedTgt mu'}.
{ move=> b0; rewrite /sharedTgt; case/orP=> F.
  apply/orP; left; rewrite frgnBlocksTgt_mu'_eq.
  by apply: subFT.
  rewrite /mu' replace_externs_pubBlocksTgt /nu'.
  rewrite reestablish_pubBlocksTgt /nu replace_locals_pubBlocksTgt.
  apply/orP; right; rewrite /pubTgt'; apply/andP; split.
  by apply: pubtgt_sub_loctgt.
  apply: REACH_nil; apply/orP; right; rewrite /sharedTgt.
  by apply/orP; right. }

(*Obsolete:
have mu0_mu'_sep : sm_inject_separated mu0 mu' m10 m20.
{ by apply: (eff_after_check5 mu0 pubSrc' pubTgt' nu erefl nu'
            mu' frgnSrc' frgnTgt' erefl m10 m20 nu_nu'_sep). } *)

(* Again, this has no reason to hold within a core.
have mu0_mu'_sep : sm_inject_separated' mu0 mu' m10 m20.
{ ad_it. }*)

exists (Inj.mk mu'_wd),(tl mus).

move=> /=; split=> //.

set mu0_pkg := {| frame_mu0 := mu0; frame_m10 := m10; frame_m20 := m20;
                  frame_val := mu0_val |}.

{(* head_inv *)
exists erefl.

move: (head_rel hdinv); rewrite mus_eq /= => rel.
case: rel; case=> /= incr1 sep1 gsep1 disj1 rc rel. 

have vinj'': 
 Forall2 (val_inject (restrict (as_inj mu_top) (vis mu_top))) 
 [:: rv1] [:: rv2].
{ by apply: Forall2_cons. }

have vinj''': 
 val_list_inject (restrict (as_inj mu_top) (vis mu_top)) 
 [:: rv1] [:: rv2].
{ by apply: val_cons_inject. }

have eq: sharedSrc (reestablish nu mu_top) = sharedSrc nu.
{ rewrite !sharedSrc_iff_frgnpub=> //; extensionality b0.
  by rewrite reestablish_frgnBlocksSrc reestablish_pubBlocksSrc. }

apply: Build_head_inv=> //.
{(*All (rel_inv_pred ...) mus'*)
  move {mus_eq allinv frametail rc}.
  elim: mus' all0 rel=> // a mus' IH.
  move=> /= []H1 H2 []H3 H4; split; last by apply: IH.
  case: H3=> incr3 sep3 gsep3 disj3 rel3.

  have frgnSrc'_loc_pub: 
    {subset [predI frgnSrc' & locBlocksSrc a] <= pubBlocksSrc a}.
  { rewrite /frgnSrc' /nu' /exportedSrc eq.
    move=> b; rewrite /in_mem /= /in_mem /=; case/andP=> XX YY.
    case: disj3=> A B C D E.
    case: {XX}(andP XX)=> H5; case/andP=> H6 H7.
    rewrite reestablish_locBlocksSrc replace_locals_locBlocksSrc in H6.
    rewrite reestablish_DomSrc in H5=> //; case: (orP H5)=> H8.
    by move: A; move/DisjointP; move/(_ b); rewrite YY H8; case.
    have V: {subset [predI REACH m1 (vis mu0) & locBlocksSrc a]
            <= pubBlocksSrc a}.
    { by case: H1. }
    have [U|U]: b \in frgnBlocksSrc mu_top 
             \/ b \in REACH m1 (vis mu0).
    { case fS: (_ \in frgnBlocksSrc _); first by left.
      move: H7; case/REACH_split=> H9.
      suff: vis mu_top b. 
      case/orP; first by rewrite extBlocksSrc_locBlocksSrc=> //; apply: Inj_wd.
      by move=> fS'; move: fS' fS; rewrite /= /in_mem /= => ->.
      move: (head_match hdinv)=> mtch; apply match_visible in mtch.
      apply: mtch; apply: (REACH_mono (getBlocks [:: rv1]))=> //.
      move=> b0 get; case: (getBlocks_inject _ _ _ vinj'' _ get)=> x []y [].    
      case/restrictD_Some=> H; case/orP; first by rewrite /vis=> ->.
      by rewrite /vis=> -> _; apply/orP; right.
      right; apply: (REACH_mono (sharedSrc nu))=> // b0.
      rewrite sharedSrc_iff_frgnpub=> //; rewrite replace_locals_frgnBlocksSrc.
      case/orP=> H10; apply/orP; first by right; rewrite H10.
      move: H10; rewrite replace_locals_pubBlocksSrc /pubSrc'. 
      by case/andP=> -> _; left. }
    by apply: C; apply/andP; split.
    by apply: V; apply/andP; split. }

  apply: Build_rel_inv=> //; first by apply: (incr_trans incr3).
  { case: mu_top_mu'_incr=> AA []BB CC.
    (*HERE*)
    case: H1 => _ []sep00 sep01 __ _.
    case: sep3 => sep30 []sep31 sep32.
    split.
    - by rewrite as_inj_mu'_mu_top.
    - by rewrite /mu' replace_externs_locBlocksSrc replace_externs_locBlocksTgt
       /nu' reestablish_locBlocksSrc reestablish_locBlocksTgt
       /nu  replace_locals_locBlocksSrc replace_locals_locBlocksTgt.
  }

  {(*globals_separate my_ge a mu'*)
    case: mu_top_mu'_incr=> AA []BB CC.
    move=> b1 b2 d1 asInj asInj'.  
    case e: (as_inj mu_top b1)=> [[x y]|].
    move: (AA _ _ _ e); rewrite asInj'; case=> -> _.
      by apply: (gsep3 _ _ _ asInj e).
        by rewrite as_inj_mu'_mu_top in asInj'; rewrite asInj' in e.
 }
   
  {(*disjinv a mu'*) 
  case: H1=> _ _ _ disj4 rc4.
  case: disj4=> X Y Z W U; apply: Build_disjinv.
  by rewrite locBlocksSrc_mu'_eq.
  by rewrite locBlocksTgt_mu'_eq.
  by rewrite frgnBlocksSrc_mu'_eq; apply: frgnSrc'_loc_pub. 

  move=> b1 b2 d1 fOf.
  case: (foreign_DomRng _ mu'_wd _ _ _ fOf)=> _[]_ []_ []_.
  rewrite frgnBlocksSrc_mu'_eq frgnBlocksTgt_mu'_eq; case=> AA []BB _.

  have aOf: as_inj mu_top b1 = Some (b2,d1).
  { move: fOf; rewrite /mu' replace_externs_foreign.
    case xx: (frgnSrc' _)=> //.
    rewrite /nu' reestablish_extern_of.
    case yy: (locBlocksSrc _ _)=> // H. }

  rewrite /in_mem /=; case/orP=> L.

  { have pA: pubBlocksSrc a b1.
    { apply: frgnSrc'_loc_pub; rewrite /in_mem /= /in_mem /=; apply/andP.
      by split. }
    case: (pubSrcAx _ _ _ pA); first by apply: Inj_wd.
    move=> x []z []lOf pT.
    case: disj3=> _ _ _ _ Catop.
    case e: (pub_of a b1)=> [[? ?]|].
    move: (pub_in_local _ _ _ _ e); rewrite lOf; case=> <- <-.
    rewrite /Consistent /consistent /= in Catop.
    move: (Catop b1 x b2 z d1).
    rewrite (local_in_all _ _ _ _ _ lOf).
    by case/(_ erefl aOf)=> -> ->.
    by apply: Inj_wd.
    move: e; rewrite /pub_of.
    by case: (Inj.mu a) pA lOf=> /= ? ? pubSrc ? lOf ? ? ? ? ? -> ->. }

  { suff e: pubBlocksSrc a b1. 
    move: (e); move/pubSrcAx; case/(_ (Inj_wd _))=> x []y []lOf pT. 
    { have asInj: as_inj a b1 = Some (x,y) 
        by apply: local_in_all=> //; apply: Inj_wd.
      case: incr3; move/(_ _ _ _ asInj)=> asInj' _.
      rewrite asInj' in aOf; case: aOf=> <- <-.
      clear - lOf e; case: a lOf e=> ???? /=.
      by rewrite /pub_of; case f: (Inj.mu _)=> //= g ->. }
    apply: frgnSrc'_loc_pub; apply/andP; split=> //.
    have aOf0: as_inj a b1 = Some (b2,d1).
    { case e: (as_inj a b1)=> [[x y]|].
      by case: incr3; move/(_ _ _ _ e); rewrite aOf; case=> <- <-.
      case sep3 => sep30 []sep31 sep32.
      move: sep30. case/(_ b1 b2 d1 e aOf).
      rewrite /DomTgt L; discriminate. }
    by rewrite /= /in_mem /= (@as_inj_locBlocks a _ _ _ (Inj_wd _) aOf0). }

  move=> b1 b2 b2' d1 d1' AA BB.
  rewrite as_inj_mu'_mu_top in BB.
  case: disj3=> _ _ _ _ Catop.
  by apply: (Catop b1 b2 b2' d1 d1' AA BB). }(*END disjinv a mu'*)

  {(*sub REACH ...*)
    move=> b; case/andP=> /= A B.
    case: H1=> incr0 sep0 gsep0 disj0 sub0.
    have C: b \in vis mu' by apply match_visible in mtch12'; apply: mtch12'.
    case: (orP C)=> D.
    case: disj0; move/DisjointP; move/(_ b)=> E _ _ _.
    move: B E; rewrite /in_mem /= => ->.
    by move: D; rewrite locBlocksSrc_mu'_eq=> ->; case.
    rewrite replace_externs_frgnBlocksSrc in D.
    by apply: frgnSrc'_loc_pub; apply/andP; split. }
  }(*END All (rel_inv_pred ...) mus'*)

{(*vis_inv*) 

have [hd1_B [hd1_vis hd1_I]]: 
  exists B, [/\ vis_inv hd1 B mu0 
              & RCSem.I (rclosed_S hd1.(Core.i)) hd1.(Core.c) m10 B].
{ move: frameall; rewrite mus_eq /=; case; case=> pft []sgt []cd1 []e1t []efs1.
  case=> vals1 []e2t []efs2 []vals2; case=> ?????????; case=> B []vis I _ _ _ _ _ _ _.
  by exists B; split. }

exists [predU getBlocks [:: rv1] & hd1_B]; split.
apply: Build_vis_inv.
rewrite /vis /=.
rewrite /mu'.
rewrite replace_externs_locBlocksSrc replace_externs_frgnBlocksSrc.
have eqL: locBlocksSrc nu' = locBlocksSrc mu0.
{ by rewrite /nu' reestablish_locBlocksSrc /nu replace_locals_locBlocksSrc. }
rewrite eqL.
have subF: {subset frgnBlocksSrc mu0 <= frgnSrc'}.
{ rewrite /frgnSrc' /nu'=> b; rewrite /in_mem /= => H.
  rewrite /DomSrc reestablish_locBlocksSrc /nu.
  rewrite replace_locals_locBlocksSrc.
  rewrite reestablish_extBlocksSrc.
  rewrite replace_locals_locBlocksSrc.
  have lN: locBlocksSrc mu0 b = false.
  { by move: (extBlocksSrc_locBlocksSrc _ (Inj_wd _) _ (frgnsrc_sub_extsrc H)). }
  rewrite lN /=.
  rewrite /exportedSrc sharedSrc_iff_frgnpub.
  rewrite reestablish_frgnBlocksSrc.
  rewrite replace_locals_frgnBlocksSrc.
  have pub_eq: 
    pubBlocksSrc (reestablish (replace_locals mu0 pubSrc' pubTgt') mu_top)
    = pubBlocksSrc (replace_locals mu0 pubSrc' pubTgt').
  { by rewrite reestablish_pubBlocksSrc. }
  rewrite pub_eq replace_locals_pubBlocksSrc; apply/andP; split.
  case: incr0_top=> _; case; move/(_ b)=> H2 _.
  apply: H2; rewrite /DomSrc.
  move: (frgnsrc_sub_extsrc H). 
  by rewrite /in_mem /= => ->; apply/orP; right.
  by apply: REACH_nil; apply/orP; right; apply/orP; left.
  by apply: nu'_wd. }
{(*{subset RC.roots ...}*)
  move: aft1'=> /= aft1'.
  have rc_aft1': 
    RC.after_external (sem (cores_S (Core.i hd1))) (Some rv1) (RC.mk (Core.c hd1) hd1_B)
    = Some (RC.mk (cast (C \o cores_S) (Logic.eq_sym e1) (Core.c hd1'))
                  [predU getBlocks [:: rv1] & hd1_B]).
  { by rewrite /RC.after_external aft1'. }
  move: (RC.after_external_rc_basis (ge (cores_S (Core.i hd1))) rc_aft1').
  move=> eq_hd1' b; rewrite /in_mem /= => H.
  have eq_hd1'': 
    RC.roots (ge (cores_S (Core.i hd1'))) 
             (RC.mk (Core.c hd1') [predU getBlocks [:: rv1] & hd1_B])
    = (fun b => 
         getBlocks [:: rv1] b
      || RC.roots (ge (cores_S (Core.i hd1))) 
                  (RC.mk (Core.c hd1) hd1_B) b).
  { move: eq_hd1'. 
    set T := C \o cores_S.
    set P := fun ix (x : T ix) => 
               RC.roots (ge (cores_S ix)) (RC.mk x [predU getBlocks [:: rv1] & hd1_B]) 
           = (fun b0 => 
              getBlocks [:: rv1] b0
              || RC.roots (ge (cores_S (Core.i hd1))) 
                          (RC.mk (Core.c hd1) hd1_B) b0).
    change (P (Core.i hd1) (cast T (sym_eq e1) (Core.c hd1'))
         -> P (Core.i hd1') (Core.c hd1')).
    by apply: cast_indnatdep'. }
  have eq_hd1''': 
    RC.roots (ge (cores_S (Core.i hd1'))) (RC.mk (Core.c hd1') [predU getBlocks [:: rv1] & hd1_B])
    = (fun b =>
         getBlocks [:: rv1] b
         || RC.roots (ge (cores_S (Core.i hd1))) 
                     (RC.mk (Core.c hd1) hd1_B) b).
  { by rewrite -eq_hd1'' /RC.roots; extensionality b0. }
  rewrite eq_hd1''' in H.
  case: (orP H).
  { move=> get1; case: (getBlocks_inject _ _ _ vinj'' _ get1)=> x []y [].
    case/restrictD_Some=> I J K.
    case l: (locBlocksSrc mu0 b); first by apply/orP; left.
    rewrite /frgnSrc' /exportedSrc; apply/orP; right; apply/andP; split.
    rewrite /nu' reestablish_DomSrc /DomSrc.
    by apply: (vis_sub_DomSrc J).
    rewrite /nu replace_locals_locBlocksSrc=> b0 M.
    case: incr1=> _ []; move/(_ b0)=> O _; apply: O.
    by apply/orP; left.
    apply/andP; split; first by rewrite eqL l.
    by apply: REACH_nil; apply/orP; left. }
  { move=> RB; case: hd1_vis=> vis_sub.
    have vis0_b: vis mu0 b.
    { apply: vis_sub.
      rewrite /in_mem /=; move: RB; rewrite /RC.roots.
      by case/orP=> -> //; rewrite orbC. }
    { case: (orP vis0_b); first by move=> ->.
      by move=> L; apply/orP; right; apply: subF. } } 
}(*END {subset RC.roots ...}*)

  { (* RCSem.I *)
    clear -at01 aft1' hd1_I; eapply RCSem.aftext_ax with (m' := m1) in at01; eauto.
    move: at01. 
    set T := C \o cores_S.
    set P := fun ix (x : T ix) => 
      RCSem.I (rclosed_S ix) x m1 (fun b : block => getBlocks [:: rv1] b || hd1_B b).
    change (P (Core.i hd1) (cast T (Logic.eq_sym e1) (Core.c hd1')) ->
            P (Core.i hd1') (Core.c hd1')).
    by apply: cast_indnatdep'. }
}(*END vis_inv*)

{(*Label: domt*)
  rewrite /= /mu' replace_externs_DomTgt /nu' reestablish_DomTgt.
  apply: (head_domt hdinv)=> //. 
  by apply: loctgt_nu_top.
}(*END domt*)

{(*Label: nucular*)
  have [rv2_val wd2]: [/\ oval_valid (Some rv2) m2 & mem_wd m2]. 
  { have nuke: Nuke_sem.I (nucular_T (Core.i (peekCore st1))) 
               (cast'' pf (Core.c (d inv))) m2. 
    { move: (head_nukeI hdinv).
      set T := C \o cores_T.
      set P := fun (ix : 'I_N) (c : T ix) => Nuke_sem.I (nucular_T ix) c m2.
      change (P (Core.i (d inv)) (Core.c (d inv))
           -> P (Core.i (peekCore st1)) (cast T (sym_eq pf) (Core.c (d inv)))).
      by apply: cast_indnatdep. }
    by case: (Nuke_sem.wmd_halted nuke hlt2). }
  move: (frame_nukeI fr0)=> nukeI.
  move: (Nuke_sem.wmd_after_external nukeI aft2' rv2_val fwd2 wd2).
  set T := C \o cores_T.
  set P := fun (ix : 'I_N) (c : T ix) => Nuke_sem.I (nucular_T ix) c m2.
  change (P (Core.i hd2) (cast T (sym_eq pf_eq22') (Core.c hd2')) 
       -> P (Core.i hd2') (Core.c hd2')).
  by apply: cast_indnatdep'. }(*END nucular*)
  by rewrite /= /mu' replace_externs_as_inj asInj_nu'_mu_top; case: hdinv=> *.
}(*END head_inv*)

split; first by move: allinv; rewrite mus_eq.
by rewrite mus_eq.
by rewrite st1'_eq.
by apply: (R_ge inv).

by apply: (R_ro1 inv).

by apply: (R_ro2 inv).

by apply: (frame_mmr1 inv).
by apply: (frame_mmr2 inv).

{ rewrite st1'_eq; move: tys1; case: (popCoreE _ pop1); rewrite st1''_eq=> x []_. 
  case=> _; case: st1 x=> y; case=> /=; case=> // a l _ _ /= => <- /=.
  by case sgof: (sig_of hd1)=> //; case=> ?; rewrite esig. }

{ move: tys2; case: (popCoreE _ pop2); rewrite st2''_eq=> x []_. 
  case=> _; case: st2 x=> y; case=> /=; case=> // a l _ _ /= => <- /=.
  by case sgof: (sig_of hd2)=> //; case=> ?; rewrite pf_sig22'. }

Qed.

End return_lems.
