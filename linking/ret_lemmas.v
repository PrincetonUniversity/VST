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

Section return_lems.

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

Let cores_S (ix : 'I_N) := 
  Modsem.mk (cores_S' ix).(ge) (RC.effsem (cores_S' ix).(sem)).

Notation cast'  pf x := (cast (C \o cores_T) pf x).
Notation cast'' pf x := (cast (C \o cores_T) (sym_eq pf) x).
Notation rc_cast'  pf x := (cast (RC.state \o C \o cores_T) pf x).
Notation rc_cast'' pf x := (cast (RC.state \o C \o cores_T) (sym_eq pf) x).

Notation R := (@R N cores_S' cores_T nucular_T sims' my_ge). 

Context
(mu : Inj.t) m1 m2 rv1 st1''
(st1 st1' : linker N cores_S) cd st2  
(valid : sm_valid mu m1 m2)
(hlt1 : LinkerSem.halted0 st1 = Some rv1)
(pop1 : popCore st1 = Some st1'')
(aft1 : LinkerSem.after_external (Some rv1) st1'' = Some st1')
(inv : R cd mu st1 m1 st2 m2).

Lemma hlt2 : exists rv2, LinkerSem.halted0 st2 = Some rv2.
Proof.
case: (R_inv inv)=> pf []mu_top []mus []mu_eq.
move=> []pf2 hdinv tlinv.
move: hlt1; rewrite /LinkerSem.halted0=> hlt10.
case: (core_halted (sims sims' (Core.i (peekCore st1)))
       _ _ _ _ _ _ (head_match hdinv) hlt10)
       => rv2 []inj12 []vinj hlt2.
exists rv2.
set T := C \o cores_T.
set P := fun ix (x : T ix) => 
  halted (sem (cores_T ix)) x = Some rv2.
change (P (Core.i (peekCore st2)) (Core.c (peekCore st2))).
apply: (cast_indnatdep' (j := Core.i (peekCore st1)))=> // H.
rewrite /P; move: hlt2; rewrite /= /RC.halted /= => <-. 
f_equal.
f_equal.
f_equal.
f_equal.
by apply: proof_irr.
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

Require Import sepcomp.mem_wd.

Lemma aft2 : 
  exists rv2 st2'' (st2' : linker N cores_T) cd' mu', 
  [/\ LinkerSem.halted0 st2 = Some rv2
    , inContext st2
    , popCore st2 = Some st2''
    , LinkerSem.after_external (Some rv2) st2'' = Some st2'
    & R cd' mu' st1' m1 st2' m2].
Proof.
case: (R_inv inv)=> pf []mu_top []mus []mu_eq.
move=> []pf_hd hdinv tlinv.
move: hlt1; rewrite /LinkerSem.halted0=> hlt10.
case: (core_halted (sims sims' (Core.i (peekCore st1)))
       _ _ _ _ _ _ (head_match hdinv) hlt10)
       => rv2 []inj12 []vinj hlt2.
exists rv2.
case: pop2=> st2'' pop2.

case: (LinkerSem.after_externalE _ _ aft1)=> fntbl []hd1 []hd1' []tl1.
move=> []pf1 []pf2 []e1 []st1''_eq st1'_eq aft1'; exists st2''.
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
case; case=> pf0 []cd0 []x0 []sig01 []vals01 []e0 []sig02 []vals02.
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
{ rewrite /restrict /as_inj /join; extensionality b.
  move: (head_rel hdinv); rewrite mus_eq /= => [][]. 
  case=> /= incr_mu0_top sep_mu0_top disj_mu0_top _ _.
  case e: (DomSrc nu b)=> //.
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
  case: sep_mu0_top; move/(_ b x' y').
  rewrite /nu replace_locals_local in lOf_nu.
  rewrite /as_inj /join eOf_nu lOf_nu eOf_top; case=> //.
  by rewrite e.
  case: incr_mu0_top=> inj_incr []H1 H2.
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
  case eOf_nu: (extern_of nu b)=> [[x' y']|].
  rewrite /nu replace_locals_extern in eOf_nu.
  case: (extern_DomRng' _ (Inj_wd _) _ _ _ eOf_nu).
  move=> _ []_ []_ []_ []_ []_ []dSrc _.
  by rewrite /nu replace_locals_DomSrc dSrc in e.
  case lOf_nu: (local_of nu b)=> //[[x' y']].
  rewrite /nu replace_locals_local in lOf_nu.
  case: (local_DomRng _ (Inj_wd _) _ _ _ lOf_nu)=> H1 _.  
  by rewrite /DomSrc /nu replace_locals_locBlocksSrc H1 /= in e. }

have asInj_nu'_mu_top: as_inj nu' = as_inj mu_top.
{ by apply: reestablish_as_inj. }

have nu'_vinj: val_inject (as_inj nu') rv1 rv2.
{ rewrite asInj_nu'_mu_top.
  by apply: (val_inject_restrictD _ _ _ _ vinj). }

move: (head_rel hdinv); rewrite mus_eq /= => [][].  
case=> /= incr0_top sep0_top disj0_top _ _.

have extsrc_nu_top b: extBlocksSrc nu b -> DomSrc mu_top b.
{ rewrite /nu replace_locals_extBlocksSrc=> H1.
  case: incr0_top=> _ []; move/(_ b); rewrite /DomSrc H1.
  by move=> H2 _; apply: H2; apply/orP; right. }

have exttgt_nu_top b: extBlocksTgt nu b -> DomTgt mu_top b.
{ rewrite /nu replace_locals_extBlocksTgt=> H1.
  case: incr0_top=> _ [] _; move/(_ b); rewrite /DomTgt H1.
  by apply; apply/orP; right. }

have nu_nu'_eincr: extern_incr nu nu'.
{ apply: reestablish_extern_incr=> //; first by apply: Inj_wd. }

have locsrc_nu_top b: locBlocksSrc nu b -> DomSrc mu_top b.
{ rewrite /nu replace_locals_locBlocksSrc=> H1.
  case: incr0_top=> _ []; move/(_ b); rewrite /DomSrc H1.
  by move=> H2 _; apply: H2. }

have loctgt_nu_top b: locBlocksTgt nu b -> DomTgt mu_top b.
{ rewrite /nu replace_locals_locBlocksTgt=> H1.
  by case: incr0_top=> _ [] _; move/(_ b); rewrite /DomTgt H1; apply. }

have nu_nu'_sep: sm_inject_separated nu nu' m10 m20.
{ apply: reestablish_sm_injsep=> //; first by apply: Inj_wd.
  by apply: sm_inject_separated_replace_locals. }

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

have [hd2' [pf_eq22' [pf_eq12' [cd' [aft2' mtch12']]]]]:
  exists hd2' (pf_eq22' : Core.i hd2 = Core.i hd2') 
              (pf_eq12' : Core.i hd1' = Core.i hd2')
         cd',
  [/\ after_external (sem (cores_T (Core.i hd2)))
        (Some rv2) (Core.c hd2) 
      = Some (cast'' pf_eq22' (Core.c hd2'))
    & match_state (sims sims' (Core.i hd1')) cd' mu' 
      (Core.c hd1') m1 (cast'' pf_eq12' (Core.c hd2')) m2].
{ case: (popCoreE _ pop2)=> wf_pf []inCtx2 st2''_eq'.
  rewrite st2''_eq' in st2''_eq.
  rewrite /updStack in st2''_eq; case: st2''_eq=> fntbl_eq pop2_eq'.
  move: (@eff_after_external 
  _ _ _ _ _ _ _ _ 
  _ _  
  (sims sims' (Core.i hd1))
  _ _ _ _ _ _ _ _ _ _ _ _
  inj0 mtch0 at01 at02' vinj0

  pubSrc' erefl pubTgt' erefl nu erefl

  nu' rv1 m1 rv2 m2

  nu_nu'_eincr nu_nu'_sep
  nu'_wd nu'_valid nu'_inj nu'_vinj
  fwd1 fwd2

  frgnSrc' erefl frgnTgt' erefl mu' erefl

  unch1 unch2).
  case=> cd' []c0' []d0' []aft1'' []aft2'' mtch12'.
  exists (Core.mk _ cores_T (Core.i hd1) d0'),(sym_eq pf0),(sym_eq e1)=> /=.
  exists (cast (fun ix => core_data (sims sims' ix)) e1 cd'); split=> //.
  
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
  set T := (fun ix => core_data (sims sims' ix)).
  set U := C \o cores_S.
  set V := C \o cores_T.
  set P := fun ix (x : T ix) (y : U ix) (z : V ix) => 
    match_state (sims sims' ix) x mu' y m1 z m2.
  change (P (Core.i hd1) cd' (cast U (sym_eq e1) (Core.c hd1')) d0'
       -> P (Core.i hd1') (cast T e1 cd') (Core.c hd1') (cast V e1 d0')).
  by apply: cast_indnatdep33. }

set st2' := {| fn_tbl := fntbl; stack := CallStack.mk (hd2'::tl2) pf20 |}.

exists st2'. 
exists (existT _ (Core.i hd1') cd'). 
exists mu'.

split=> //.

move: hlt2.

set T := C \o cores_T.
set P := fun ix (x : T ix) => 
 halted (sem (cores_T ix)) x = Some rv2.
change (P (Core.i (peekCore st1)) (cast T (sym_eq pf) (Core.c (d inv)))
     -> P (Core.i (peekCore st2)) (Core.c (peekCore st2))).
by apply: cast_indnatdep'.

by rewrite pop2 st2''_eq.

{ rewrite /st2'; move: aft2'.
rewrite /LinkerSem.after_external /= => -> /=. 
rewrite /SeqStack.updStack /Core.upd.
do 3 f_equal; first by move=> ? ?; case=> -> ->.
f_equal; clear - hd2' pf_eq22'; destruct hd2'=> /=.
by move: pf_eq22'=> /= pf; subst; f_equal.
by apply: proof_irr. }

apply: Build_R=> /=.
rewrite st1'_eq; exists pf_eq12'.

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
  move=> _; case; move/(_ b0)=> H _ _ _ _ _; apply: H.
  by rewrite /DomSrc E; apply/orP; right.

  rewrite /DomTgt; case/orP; rewrite /mu' replace_externs_locBlocksTgt /nu'.
  by rewrite reestablish_locBlocksTgt /nu replace_locals_locBlocksTgt=> ->.
  rewrite /mu' replace_externs_extBlocksTgt /nu'.
  rewrite reestablish_extBlocksTgt /nu replace_locals_locBlocksTgt=> E.
  have lN: locBlocksTgt mu0 b0 = false.
  { by move: (extBlocksTgt_locBlocksTgt _ (Inj_wd _) _ E). }
  rewrite lN; apply/orP; right.
  move: (head_rel hdinv); rewrite mus_eq /=; case; case=> /=; case.
  move=> _; case=> _; move/(_ b0)=> H _ _ _ _; apply: H.
  by rewrite /DomTgt E; apply/orP; right. }

have as_inj_mu'_mu_top : as_inj mu' = as_inj mu_top.
{ by rewrite replace_externs_as_inj asInj_nu'_mu_top. }

have DomSrc_mu'_mu_top : DomSrc mu' = DomSrc mu_top.
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

have mu0_mu'_sep : sm_inject_separated mu0 mu' m10 m20.
{ by apply: (eff_after_check5 mu0 pubSrc' pubTgt' nu erefl nu'
            mu' frgnSrc' frgnTgt' erefl m10 m20 nu_nu'_sep). }

exists (Inj.mk mu'_wd),(tl mus).

move=> /=; split=> //.

set mu0_pkg := {| frame_mu0 := mu0; frame_m10 := m10; frame_m20 := m20;
                  frame_val := mu0_val |}.

{(* head_inv *)
exists erefl.

move: (head_rel hdinv); rewrite mus_eq /= => rel.
case: rel; case=> /= incr1 sep1 disj1 rc rel. 

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
  case: H3=> incr3 sep3 disj3 rel3.

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
  { case: mu_top_mu'_incr=> AA []BB CC; case: sep3=> XX []YY ZZ; split.
  move=> b1 b2 d1 asInj asInj'.  
  case e: (as_inj mu_top b1)=> [[x y]|].
  move: (AA _ _ _ e); rewrite asInj'; case=> -> _.
  by apply: (XX _ _ _ asInj e).
  by rewrite as_inj_mu'_mu_top in asInj'; rewrite asInj' in e.
  by rewrite DomSrc_mu'_mu_top DomTgt_mu'_mu_top; split. }

  {(*disjinv a mu'*) 
  case: H1=> _ _ disj4 rc4.
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
      case: sep3; case/(_ b1 b2 d1 e aOf)=> _ D _.
      move: D; rewrite /DomTgt L; discriminate. }
    by rewrite /= /in_mem /= (@as_inj_locBlocks a _ _ _ (Inj_wd _) aOf0). }

  move=> b1 b2 b2' d1 d1' AA BB.
  rewrite as_inj_mu'_mu_top in BB.
  case: disj3=> _ _ _ _ Catop.
  by apply: (Catop b1 b2 b2' d1 d1' AA BB). }(*END disjinv a mu'*)

  {(*sub REACH ...*)
    move=> b; case/andP=> /= A B.
    case: H1=> incr0 sep0 disj0 sub0.
    have C: b \in vis mu' by apply match_visible in mtch12'; apply: mtch12'.
    case: (orP C)=> D.
    case: disj0; move/DisjointP; move/(_ b)=> E _ _ _.
    move: B E; rewrite /in_mem /= => ->.
    by move: D; rewrite locBlocksSrc_mu'_eq=> ->; case.
    rewrite replace_externs_frgnBlocksSrc in D.
    by apply: frgnSrc'_loc_pub; apply/andP; split. }
  }(*END All (rel_inv_pred ...) mus'*)

{(*vis_inv*) 
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
  move: (RC.after_external_rc_basis (ge (cores_S (Core.i hd1))) aft1').
  move=> eq_hd1' b; rewrite /in_mem /= => H.
  have eq_hd1'': 
    RC.roots (ge (cores_S (Core.i hd1'))) (Core.c hd1')
    = (fun b => 
         getBlocks [:: rv1] b
      || RC.roots (ge (cores_S (Core.i hd1))) (Core.c hd1) b).
  { move: eq_hd1'. 
    set T := C \o cores_S.
    set P := fun ix (x : T ix) => 
               RC.roots (ge (cores_S ix)) x 
           = (fun b0 => 
              getBlocks [:: rv1] b0
              || RC.roots (ge (cores_S (Core.i hd1))) (Core.c hd1) b0).
    change (P (Core.i hd1) (cast T (sym_eq e1) (Core.c hd1'))
         -> P (Core.i hd1') (Core.c hd1')).
    by apply: cast_indnatdep'. }
  have eq_hd1''': 
    RC.roots my_ge (Core.c hd1') 
    = (fun b =>
         getBlocks [:: rv1] b
         || RC.roots (ge (cores_S (Core.i hd1))) (Core.c hd1) b).
  { rewrite -eq_hd1'' /RC.roots; extensionality b0.
    have glob_eq: isGlobalBlock my_ge b0
                = isGlobalBlock (ge (cores_S (Core.i hd1'))) b0. 
    { suff: isGlobalBlock my_ge b0 
        <-> isGlobalBlock (ge (cores_S (Core.i hd1'))) b0.
      case: (isGlobalBlock _ _)=> //.
      case: (isGlobalBlock _ _)=> //.
      case=> //.
      by move/(_ erefl).         
      case: (isGlobalBlock _ _)=> //.
      case=> //.
      by move=> _; move/(_ erefl).               
      by rewrite -(isGlob_iffS my_ge_S). }
    by rewrite -glob_eq. }
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
  { move=> RB; case: (frame_vis fr0)=> vis_sub. 
    have vis0_b: vis mu0 b.
    { apply: vis_sub.
      rewrite /in_mem /=; move: RB; rewrite /RC.roots.
      have glob_eq: isGlobalBlock my_ge b
                  = isGlobalBlock (ge (cores_S (Core.i hd1))) b. 
      { suff: isGlobalBlock my_ge b 
          <-> isGlobalBlock (ge (cores_S (Core.i hd1))) b.
        case: (isGlobalBlock _ _)=> //.
        case: (isGlobalBlock _ _)=> //.
        case=> //.
        by move/(_ erefl).         
        case: (isGlobalBlock _ _)=> //.
        case=> //.
        by move=> _; move/(_ erefl).               
        by rewrite -(isGlob_iffS my_ge_S). }
      by rewrite -glob_eq. }
    { case: (orP vis0_b); first by move=> ->.
      by move=> L; apply/orP; right; apply: subF. } } 
}(*END {subset RC.roots ...}*)
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
}(*END head_inv*)

split; first by move: allinv; rewrite mus_eq.
by rewrite mus_eq.
by rewrite st1'_eq.
by apply: (R_ge inv).
Qed.

End return_lems.

