(* sepcomp imports *)

Require Import sepcomp. Import SepComp. 
Require Import arguments.

Require Import pos.
Require Import compcert_linking.
Require Import rc_semantics.
Require Import rc_semantics_lemmas.
Require Import context.
Require Import linking_spec.

(* ssreflect *)

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import nucular_semantics.
Require Import Values.   
Require Import closed_simulations_lemmas.
Require Import closed_safety.
Require Import semantics_lemmas.

Import SM_simulation.
Import Wholeprog_sim.
Import Linker. 
Import Modsem.

Lemma pos_incr' (p : pos) : (0 < (p+1))%nat.                           
Proof. omega. Qed.                                                     
                                                                       
Definition pos_incr (p : pos) := mkPos (pos_incr' p).                  

Module Prog.
Record t (N : pos) : Type := 
  mk { sems :> 'I_N -> Modsem.t;
       main : val
     }.
End Prog.

Section ExtendSems.

Variable ge : ge_ty.
Variable C : Ctx.t ge.
Variable N0 : pos.

Let N := pos_incr N0.

Lemma lt_ssrnatlt n m : lt n m -> ssrnat.leq (S n) m.
Proof. by move=> H; apply/ssrnat.ltP. Qed.

Definition extend_sems (f : 'I_N0 -> Modsem.t) (ix : 'I_N) : Modsem.t :=
  match lt_dec ix N0 with
    | left pf => let ix' : 'I_N0 := Ordinal (lt_ssrnatlt pf) in f ix'
    | right _ => C.(Ctx.C)
  end.

End ExtendSems.

(** * Reach-Closed Contextual Equivalence *)

Definition apply_ctx (ge : ge_ty) (C : Ctx.t ge) 
                     (N : pos) (p : Prog.t N) : Prog.t (pos_incr N) :=
  Prog.mk (extend_sems C p.(Prog.sems)) (Prog.main p).

Lemma leq_N_Nincr (N : pos) : ssrnat.leq N (pos_incr N).
Proof. by rewrite /= plus_comm. Qed.

Lemma leq_SN_Nincr (N : pos) : ssrnat.leq (S N) (pos_incr N).
Proof. by rewrite /= plus_comm. Qed.

Definition link_ctx (ge : ge_ty) (C : Ctx.t ge) (N : pos) (p : Prog.t N) plt : EffectSem :=
  let extended_plt (id : ident) := 
    match plt id with
      | None => Some (Ordinal (leq_SN_Nincr N))
      | Some ix => Some (widen_ord (leq_N_Nincr N) ix)
    end
  in effsem (pos_incr N) (Prog.sems (apply_ctx C p)) extended_plt.

Section program_behaviors.
Variables (ge : ge_ty) (N : pos).

Definition initializable plt (C : Ctx.t ge) (p : Prog.t N) args :=
  exists c, initial_core (link_ctx C p plt) ge (Prog.main p) args = Some c.

Definition prog_has_behavior plt (C : Ctx.t ge) (p : Prog.t N) args m beh :=
  [\/ exists c, 
      [/\ initial_core (link_ctx C p plt) ge (Prog.main p) args = Some c
        & has_behavior (link_ctx C p plt) ge c m beh]
    | [/\ ~initializable plt C p args & beh = Going_wrong]].

Definition prog_terminates plt (C : Ctx.t ge) (p : Prog.t N) args m :=
  prog_has_behavior plt C p args m Termination.

Lemma prog_terminates_initializable plt C p args m :
  prog_terminates plt C p args m ->
  initializable plt C p args.
Proof.
case; first by case=> c []Hinit ?; exists c=> //.
by case=> ?; discriminate.
Qed.

Definition prog_refines plt (C : Ctx.t ge) (p tp : Prog.t N) args targs m tm :=
  forall tbeh, prog_has_behavior plt C tp targs tm tbeh ->
  exists beh, [/\ prog_has_behavior plt C p args m beh & behavior_refines tbeh beh].

Definition prog_equiv plt (C : Ctx.t ge) (p tp : Prog.t N) args targs m tm :=
  [/\ prog_refines plt C p tp args targs m tm
    & prog_refines plt C tp p targs args tm m].

Definition safe plt (C : Ctx.t ge) (p : Prog.t N) args m :=
  exists c, 
  [/\ initial_core (link_ctx C p plt) ge (Prog.main p) args = Some c
    & forall n, safeN (link_ctx C p plt) ge n c m].

Lemma behavior_exists (EM : ClassicalFacts.excluded_middle)
          plt C p args m :
  exists beh, prog_has_behavior plt C p args m beh.
Proof.
case Init: (initial_core (link_ctx C p plt) ge (Prog.main p) args)=> [c|].
case: (EM (prog_terminates plt C p args m)).
{ move=> Hterm; exists Termination; left; exists c; split=> //.
  by case: Hterm; case=> c' //; rewrite Init; case; case=> <-. }
{ move=> Hnterm; case: (EM (safe plt C p args m)).
  { move=> Hsafe; exists Divergence; left; exists c; split=> //.
    case: Hsafe=> c'; rewrite Init; case; case=> <- Hsafe.
    constructor=> // Hnterm'; first by apply safeN_safeN_det.
    by apply: Hnterm; left; exists c; split=> //; constructor. }
  { move=> Hnsafe; exists Going_wrong; left; exists c; split=> //.
    by constructor=> // Hnsafe'; apply: Hnsafe; exists c; split. }
}
exists Going_wrong; right; split=> //.
by rewrite /initializable Init; case.
Qed.
    
End program_behaviors.

Definition ok_init j (ge : ge_ty) args1 args2 m1 m2 :=
  cc_init_inv j ge args1 m1 ge args2 m2.

Definition Equiv_ctx (ge : ge_ty) (N : pos) plt (p1 p2 : Prog.t N) :=
  forall (C : Ctx.t ge) args1 args2 m1 m2 j, 
  ok_init j ge args1 args2 m1 m2 -> safe plt C p1 args1 m1 -> 
  (prog_terminates plt C p1 args1 m1 <-> prog_terminates plt C p2 args2 m2).

Definition Prog_refines (ge : ge_ty) (N : pos) plt (p1 p2 : Prog.t N) :=
  forall (C : Ctx.t ge) args1 args2 m1 m2 j, ok_init j ge args1 args2 m1 m2 ->     
  prog_refines plt C p1 p2 args1 args2 m1 m2.

(** An alternate contextual refinement, in which the initial memory [m]
 is equal in source and target (this is possible, e.g., if [m] contains just
 globals). [m] must self-inject. 

 The advantage of this alternate notion is that it is easily shown reflexive and
 transitive. *)

Definition Prog_refines2 (ge : ge_ty) (N : pos) plt (p1 p2 : Prog.t N) :=
  forall (C : Ctx.t ge) args m, 
  ok_init (Mem.flat_inj (Mem.nextblock m)) ge args args m m ->     
  prog_refines plt C p1 p2 args args m m.

Lemma Prog_refines_implies2 ge N plt (p1 p2 : Prog.t N) :
  Prog_refines ge plt p1 p2 -> Prog_refines2 ge plt p1 p2.
Proof.
  move=> H1 C args m Hok; apply: H1=> //.
  eassumption.
(*refine (Mem.flat_inj (Mem.nextblock m)); auto.
by []. *)
Qed. 

Lemma behavior_refines_refl beh : behavior_refines beh beh.
Proof. by case: beh; constructor. Qed.

Lemma behavior_refines_trans beh1 beh2 beh3 : 
  behavior_refines beh1 beh2 -> 
  behavior_refines beh2 beh3 -> 
  behavior_refines beh1 beh3.
Proof.
inversion 1; subst; auto. 
inversion 1; subst; auto.
Qed.

Lemma Prog_refines2_refl ge N plt (p : Prog.t N) : Prog_refines2 ge plt p p.
Proof. 
move=> C args m Inv beh Has; exists beh; split=> //.
by apply: behavior_refines_refl.
Qed.

Lemma Prog_refines2_trans ge N plt (p1 p2 p3 : Prog.t N) : 
  Prog_refines2 ge plt p1 p2 -> 
  Prog_refines2 ge plt p2 p3 -> 
  Prog_refines2 ge plt p1 p3.
Proof. 
move=> H1 H2 C main args Inv beh3 Has3.
case: (H2 C main args Inv beh3 Has3)=> beh2 []Has2 Href23.
case: (H1 C main args Inv beh2 Has2)=> beh1 []Has1 Href12.
exists beh1; split=> //.
by eapply behavior_refines_trans; eauto.
Qed.

(** Simulation implies Equiv_ctx *)

Module ContextEquiv (LS : LINKING_SIMULATION). 
                                                                       
Import LS.                                                             
                                                                       
Section ContextEquiv.

Variable N : pos.
Variable pS pT : Prog.t N.
Variable rclosed_S : forall ix : 'I_N, RCSem.t (Prog.sems pS ix).(sem) (Prog.sems pS ix).(ge).
Variable valid_T : forall ix : 'I_N, Nuke_sem.t (Prog.sems pT ix).(sem).
Variable targets_det : forall ix : 'I_N, corestep_fun (Prog.sems pT ix).(sem).
Variable plt : ident -> option 'I_N.
Variable sims : 
  forall ix : 'I_N,                                          
  let s := Prog.sems pS ix in                                              
  let t := Prog.sems pT ix in                                              
  SM_simulation_inject s.(sem) t.(sem) s.(ge) t.(ge).
Variable ge_top : ge_ty.                                                     
Variable domeq_S : forall ix : 'I_N, genvs_domain_eq ge_top (Prog.sems pS ix).(ge).

(*Four new assumptions*)
Variable symbols_up_S: forall ix id b,
     Genv.find_symbol ((Prog.sems pS ix).(ge)) id = Some b ->
     Genv.find_symbol ge_top id = Some b.
Variable symbols_up_T: forall ix id b,
     Genv.find_symbol ((Prog.sems pT ix).(ge)) id = Some b ->
     Genv.find_symbol ge_top id = Some b.
Variable all_gvars_includedS: forall ix b,
     gvars_included (Genv.find_var_info ((Prog.sems pS ix).(ge)) b) (Genv.find_var_info ge_top b).
Variable all_gvar_infos_eq: forall ix, gvar_infos_eq (ge (Prog.sems pS ix)) (ge (Prog.sems pT ix)).

Variable find_symbol_ST : 
  forall (ix : 'I_N) id bf, 
  Genv.find_symbol (ge (Prog.sems pS ix)) id = Some bf -> 
  Genv.find_symbol (ge (Prog.sems pT ix)) id = Some bf.

Lemma equiv (Hmain : Prog.main pS = Prog.main pT) : Equiv_ctx ge_top plt pS pT.
Proof.
rewrite /Equiv_ctx=> C args1 args2 m1 m2 j Inv Hsafe. 
have domeq_T : forall ix : 'I_N, genvs_domain_eq ge_top (Prog.sems pT ix).(ge). 
{ move=> ix; apply genvs_domain_eq_trans with (ge2 := ge (Prog.sems pS ix))=> //.
  by case: (sims ix). }
have sim: CompCert_wholeprog_sim 
          (link_ctx C pS plt) (link_ctx C pT plt) ge_top ge_top (Prog.main pS).
{ apply: link=> ix; rewrite /Prog.sems/apply_ctx/extend_sems. 
  by move=> ??; case e: (lt_dec ix N)=> [pf|pf] //; apply find_symbol_ST.
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.rclosed_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.valid_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.sim_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.domeq_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.domeq_C C).
  { move=> ??; case e: (lt_dec ix N)=> [pf|pf]. move=> ?. eapply symbols_up_S. eassumption. apply (Ctx.symbols_up_C). }
  { move=> ??; case e: (lt_dec ix N)=> [pf|pf]. move=> ?. eapply symbols_up_T. eassumption. apply (Ctx.symbols_up_C). }
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.gvars_included_C C). 
  case e: (lt_dec ix N)=> [pf|pf] //; try apply: (Ctx.gvars_included_C C).
    move=> b; specialize (gvar_infos_eqD2 _ _ (all_gvar_infos_eq (Ordinal (lt_ssrnatlt pf))) b).
    intros.
    destruct (Genv.find_var_info (ge (Prog.sems pT (Ordinal (lt_ssrnatlt pf)))) b).
      destruct (H g) as [g1 [? [? [? ?]]]]; trivial; clear H.
      assert (GV1:= all_gvars_includedS  (Ordinal (lt_ssrnatlt pf)) b). 
      rewrite H0 in GV1; simpl in GV1.  rewrite H1 H2 H3 in GV1; apply GV1. 
    simpl; destruct ( Genv.find_var_info ge_top b); trivial. 
  }
have target_det: corestep_fun (link_ctx C pT plt). 
{ apply: linking_det=> ix; rewrite /Prog.sems/apply_ctx/extend_sems.
  by case e: (lt_dec ix N)=> [pf|pf] //; apply Ctx.det_C. }
case: Hsafe=> c1 []Init1 Hsafe; move: (Init1)=> Init1'.
eapply @core_initial 
  with (Sem1 := link_ctx C pS plt) (Sem2 := link_ctx C pT plt) 
       (ge1 := ge_top) (ge2 := ge_top) (halt_inv := cc_halt_inv)
       (j := j) (main := Prog.main pS) (m1 := m1) (m2 := m2) (w := sim)
  in Init1; eauto.
case: Init1=> mu []cd []c2 []_ []Init2 Hmatch.
apply equitermination in Hmatch=> //; split=> H1.
left; exists c2; split=> //; first by rewrite Hmain in Init2.
constructor; rewrite -Hmatch. 
by case: H1=> [][]c1' //; rewrite Init1'; case; case=> <-; inversion 1.
left; exists c1; split=> //; constructor; rewrite Hmatch.
by case: H1=> [][]c2' //; rewrite -Hmain Init2; case; case=> <-; inversion 1.
Qed.

End ContextEquiv.

End ContextEquiv.

(** Simulation implies behavior refinement *)

Module ProgRefines (LS : LINKING_SIMULATION). 
                                                                       
Import LS.                                                             
                                                                       
Section ProgRefines.

Variable N : pos.
Variable pS pT : Prog.t N.
Variable rclosed_S : forall ix : 'I_N, RCSem.t (Prog.sems pS ix).(sem) (Prog.sems pS ix).(ge).
Variable valid_T : forall ix : 'I_N, Nuke_sem.t (Prog.sems pT ix).(sem).
Variable targets_det : forall ix : 'I_N, corestep_fun (Prog.sems pT ix).(sem).
Variable plt : ident -> option 'I_N.
Variable sims : 
  forall ix : 'I_N,                                          
  let s := Prog.sems pS ix in                                              
  let t := Prog.sems pT ix in                                              
  SM_simulation_inject s.(sem) t.(sem) s.(ge) t.(ge).
Variable ge_top : ge_ty.                                                     
Variable domeq_S : forall ix : 'I_N, genvs_domain_eq ge_top (Prog.sems pS ix).(ge).

(*Four new assumptions*)
Variable symbols_up_S: forall ix id b,
     Genv.find_symbol ((Prog.sems pS ix).(ge)) id = Some b ->
     Genv.find_symbol ge_top id = Some b.
Variable symbols_up_T: forall ix id b,
     Genv.find_symbol ((Prog.sems pT ix).(ge)) id = Some b ->
     Genv.find_symbol ge_top id = Some b.
Variable all_gvars_includedS: forall ix b,
     gvars_included (Genv.find_var_info ((Prog.sems pS ix).(ge)) b) (Genv.find_var_info ge_top b).

Variable all_gvar_infos_eq: forall ix, gvar_infos_eq (ge (Prog.sems pS ix)) (ge (Prog.sems pT ix)).
Variable find_symbol_ST : 
  forall (ix : 'I_N) id bf, 
  Genv.find_symbol (ge (Prog.sems pS ix)) id = Some bf -> 
  Genv.find_symbol (ge (Prog.sems pT ix)) id = Some bf.

Lemma domeq_T : forall ix : 'I_N, genvs_domain_eq ge_top (Prog.sems pT ix).(ge). 
Proof. 
move=> ix; apply genvs_domain_eq_trans with (ge2 := ge (Prog.sems pS ix))=> //.
by case: (sims ix). 
Qed.

Lemma refines (Hmain : Prog.main pS = Prog.main pT) 
      (EM : ClassicalFacts.excluded_middle) : Prog_refines ge_top plt pS pT.
Proof.
move=> C args1 args2 m1 m2 j Inv tbeh Hhas2.
have sim: CompCert_wholeprog_sim 
          (link_ctx C pS plt) (link_ctx C pT plt) ge_top ge_top (Prog.main pS).
{ apply: link=> ix; rewrite /Prog.sems/apply_ctx/extend_sems. 
  by move=> ??; case e: (lt_dec ix N)=> [pf|pf] //; apply find_symbol_ST.
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.rclosed_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.valid_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.sim_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.domeq_C C).
  case e: (lt_dec ix N)=> [pf|pf] //; last by apply: (Ctx.domeq_C C). by apply: domeq_T. 
  { move=> ??; case e: (lt_dec ix N)=> [pf|pf]. move=> ?. eapply symbols_up_S. eassumption. apply (Ctx.symbols_up_C). }
  { move=> ??; case e: (lt_dec ix N)=> [pf|pf]. move=> ?. eapply symbols_up_T. eassumption. apply (Ctx.symbols_up_C). }
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.gvars_included_C C). 
  case e: (lt_dec ix N)=> [pf|pf] //; try apply: (Ctx.gvars_included_C C).
    move=> b; specialize (gvar_infos_eqD2 _ _ (all_gvar_infos_eq (Ordinal (lt_ssrnatlt pf))) b).
    intros.
    destruct (Genv.find_var_info (ge (Prog.sems pT (Ordinal (lt_ssrnatlt pf)))) b).
      destruct (H g) as [g1 [? [? [? ?]]]]; trivial; clear H.
      assert (GV1:= all_gvars_includedS  (Ordinal (lt_ssrnatlt pf)) b). 
      rewrite H0 in GV1; simpl in GV1.  rewrite H1 H2 H3 in GV1; apply GV1. 
    simpl; destruct ( Genv.find_var_info ge_top b); trivial. 
}
have target_det: corestep_fun (link_ctx C pT plt). 
{ apply: linking_det=> ix; rewrite /Prog.sems/apply_ctx/extend_sems.
  by case e: (lt_dec ix N)=> [pf|pf] //; apply Ctx.det_C. }

have [beh Hhas1]: (exists beh, prog_has_behavior plt C pS args1 m1 beh).
{ by apply: behavior_exists. }

case: Hhas1.
{ 
case=> c1 []Init1 Hhas1; move: (Init1)=> Init1'.
eapply @core_initial 
  with (Sem1 := link_ctx C pS plt) (Sem2 := link_ctx C pT plt) 
       (ge1 := ge_top) (ge2 := ge_top) (halt_inv := cc_halt_inv)
       (j := j) (main := Prog.main pS) (m1 := m1) (m2 := m2) (w := sim)
  in Init1; eauto.
case: Init1=> mu []cd []c2 []_ []Init2 Hmatch.
case: (behavior_refinement (Prog.main pS) sim target_det EM c1 c2 m1 m2 tbeh).
by exists cd, mu.
case: Hhas2; case=> c2' //; first by rewrite -Hmain Init2; case; case=> <-.
by elimtype False; apply: c2'; exists c2; rewrite -Hmain Init2.
move=> beh' []Hhas1' Href; exists beh'; split=> //.
by left; exists c1; split.
}
{
case=> Init1 Hwrong; exists Going_wrong; split; last by constructor.
by right; split.
}
Qed.

(* An alternative proof of equiv, relying on behavior_equiv. *)
Lemma equiv' (Hmain : Prog.main pS = Prog.main pT) 
      (EM : ClassicalFacts.excluded_middle) : Equiv_ctx ge_top plt pS pT.
Proof.
move=> C args1 args2 m1 m2 j Inv Hsafe.
have sim: CompCert_wholeprog_sim 
          (link_ctx C pS plt) (link_ctx C pT plt) ge_top ge_top (Prog.main pS).
{ apply: link=> ix; rewrite /Prog.sems/apply_ctx/extend_sems. 
  by move=> ??; case e: (lt_dec ix N)=> [pf|pf] //; apply find_symbol_ST.
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.rclosed_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.valid_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.sim_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.domeq_C C).
  case e: (lt_dec ix N)=> [pf|pf] //; last by apply: (Ctx.domeq_C C). by apply: domeq_T.
  { move=> ??; case e: (lt_dec ix N)=> [pf|pf]. move=> ?. eapply symbols_up_S. eassumption. apply (Ctx.symbols_up_C). }
  { move=> ??; case e: (lt_dec ix N)=> [pf|pf]. move=> ?. eapply symbols_up_T. eassumption. apply (Ctx.symbols_up_C). }
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.gvars_included_C C). 
  case e: (lt_dec ix N)=> [pf|pf] //; try apply: (Ctx.gvars_included_C C).
    move=> b; specialize (gvar_infos_eqD2 _ _ (all_gvar_infos_eq (Ordinal (lt_ssrnatlt pf))) b).
    intros.
    destruct (Genv.find_var_info (ge (Prog.sems pT (Ordinal (lt_ssrnatlt pf)))) b).
      destruct (H g) as [g1 [? [? [? ?]]]]; trivial; clear H.
      assert (GV1:= all_gvars_includedS  (Ordinal (lt_ssrnatlt pf)) b). 
      rewrite H0 in GV1; simpl in GV1.  rewrite H1 H2 H3 in GV1; apply GV1. 
    simpl; destruct ( Genv.find_var_info ge_top b); trivial. 
}
have target_det: corestep_fun (link_ctx C pT plt). 
{ apply: linking_det=> ix; rewrite /Prog.sems/apply_ctx/extend_sems.
  by case e: (lt_dec ix N)=> [pf|pf] //; apply Ctx.det_C. }

have [beh Hhas1]: (exists beh, prog_has_behavior plt C pS args1 m1 beh).
{ by apply: behavior_exists. }

case: Hhas1.
{ 
case=> c1 []Init1 Hhas1; move: (Init1)=> Init1'.
eapply @core_initial 
  with (Sem1 := link_ctx C pS plt) (Sem2 := link_ctx C pT plt) 
       (ge1 := ge_top) (ge2 := ge_top) (halt_inv := cc_halt_inv)
       (j := j) (main := Prog.main pS) (m1 := m1) (m2 := m2) (w := sim)
  in Init1; eauto.
case: Init1=> mu []cd []c2 []_ []Init2 Hmatch.
case: (behavior_equiv (Prog.main pS) sim target_det EM c1 c2 m1 m2 Termination).
by exists cd, mu.
by case: Hsafe=> x []; rewrite Init1'; case=> <-.
move=> H1 H2; rewrite /prog_terminates /prog_has_behavior; split; case;
 try solve[case=> _ ? //].
* case=> c; rewrite Init1'; case; case=> ?; subst c1=> H.
  left; exists c2; split=> //; first by rewrite -Hmain. by apply: (H2 H).
* case=> c; rewrite -Hmain Init2; case; case=> ?; subst c2=> H.
  by left; exists c1; split=> //; apply: (H1 H).
}
{
case=> Init1 Hwrong; case: Hsafe=> x []Hinit Hsafe. 
by elimtype False; apply: Init1; exists x.
}
Qed.

End ProgRefines.

End ProgRefines.



