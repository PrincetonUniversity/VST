(* In this file, we prove that our simulation structures "are conservative" over
  CompCert2.0's (and CompCert1.x's) memory-ignorant simulation structures:

Theorem CoreCorrectness_implies_CompcertForwardSimulation:
  forall F1 C1 V1 F2 C2 V2
    (Sem1: CoreSemantics (Genv.t F1 V1) C1 mem)
    (Sem2: CoreSemantics (Genv.t F2 V2) C2 mem)
    P1 P2 ExternIdents epts,
    In (P1.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents  ->
    P1.(prog_main) = P2.(prog_main) ->
    CompilerCorrectness.core_correctness (fun F C V Sem P => True)
         ExternIdents epts F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
    forward_simulation (mk_semantics F1 C1 V1 Sem1 P1) (mk_semantics F2 C2 V2 Sem2 P2).

We also prove the corresponding result for CoreCorrectnessT

Theorem CoreCorrectnessT_implies_CompcertForwardSimulation:
  forall F1 C1 V1 F2 C2
    (Sem1: CoreSemantics (Genv.t F1 V1) C1 mem)
    (Sem2: CoreSemantics (Genv.t F2 V1) C2 mem)
    P1 P2 ExternIdents epts
    (EXT: In (P1.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents),
    CompilerCorrectness.core_correctnessT (fun F C V Sem P => True)
            ExternIdents epts F1 C1 V1 F2 C2 Sem1 Sem2 P1 P2 ->
    forward_simulation (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V1 Sem2 P2).

The second proof shows that for full-program translations, the assumptions
  GenvHyp are not required.

*)

Require Import Coqlib.
Require Import Events.
Require Import Smallstep.
Require Import Globalenvs.
Require Import AST.
Require Import Memory.
Require Import compcert.common.Values.
Require Import Integers.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.compiler_correctness.

Require Import sepcomp.Coqlib2.

Section CoreSem_to_semantics.
  Variables (F C V:Type).
  Let genv  := Genv.t F V.
  (*HERE we used to specialize type D to program variables
  Variable (Sem: CoreSemantics genv C mem (list (ident * globdef F V))). *)
  Variable (Sem: CoreSemantics genv C mem).

  Let state := (C * mem)%type.

  Inductive step (ge:genv) : state -> trace -> state -> Prop :=
  | step_corestep : forall c m c' m',
    corestep Sem ge c m c' m' ->
    step ge (c,m) E0 (c',m')

  | step_ext_step : forall c m c' m' ef args tr ret,
    at_external Sem c = Some (ef,ef_sig ef,args) ->
    external_call ef ge args m tr ret m' ->
    after_external Sem (Some ret) c = Some c' ->
    step ge (c,m) tr (c',m').

  Variable (prog:AST.program F V).

  Definition main_sig : signature := mksignature (nil) (Some AST.Tint).

  Definition initial_state (st:state) : Prop :=
    exists b, exists vals,
      Forall2 (val_inject (Mem.flat_inj (Mem.nextblock (snd st)))) vals vals /\
      Forall2 Val.has_type vals (sig_args main_sig) /\
      Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
      initial_core Sem (Genv.globalenv prog) (Vptr b Int.zero) vals = Some (fst st) /\
      Genv.init_mem prog = Some (snd st).

  (*Require that return values are int here - that's what we need below for mk_semantics*)
  Definition final_state (st:state) (i:int) : Prop :=
    halted Sem (fst st) = Some (Vint i).

  Definition mk_semantics: semantics :=
    Semantics step initial_state final_state (Genv.globalenv prog).

  Lemma corestep_plus_step: forall  ge c m c' m',
    corestep Sem ge c m c' m' ->
    plus step ge (c, m) E0 (c', m').
  Proof.
    intros.
    eapply plus_left. eapply step_corestep. apply H.  apply star_refl.
    rewrite E0_left. trivial.
  Qed.

  Lemma corestep_plus_plus_step: forall ge c m c' m',
    corestep_plus Sem ge c m c' m' -> plus step ge (c, m) E0 (c', m').
  Proof.
    intros. unfold corestep_plus in H. destruct H as [n Hn].
    generalize dependent m.  generalize dependent c.
    induction n.
    simpl; intros. destruct Hn as [c2 [m2 [Hstep X]]]. inv X.
    eapply corestep_plus_step; auto.
    intros. simpl in Hn. destruct Hn as [c1 [m1 [Hstep X]]].
    eapply plus_left. eapply step_corestep. apply Hstep.
    eapply plus_star. eapply IHn. apply X.  rewrite E0_left. trivial.
  Qed.

  Lemma corestep_star_star_step: forall ge c m c' m',
    corestep_star Sem ge c m c' m' -> star step ge (c, m) E0 (c', m').
  Proof. intros. unfold corestep_star in H. destruct H as [n Hn].
    destruct n; simpl in Hn. inv Hn. apply star_refl.
    eapply plus_star. eapply corestep_plus_plus_step. exists n. apply Hn.
  Qed.

End CoreSem_to_semantics.

Module CompilerCorrectness_implies_forward_simulation.

Theorem CoreCorrectness_implies_CompcertForwardSimulation:
  forall F1 C1 V1 F2 C2 V2
    (Sem1: CoreSemantics (Genv.t F1 V1) C1 mem)
    (Sem2: CoreSemantics (Genv.t F2 V2) C2 mem)
    P1 P2 ExternIdents epts,
    In (P1.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents  ->
    P1.(prog_main) = P2.(prog_main) ->
    CompilerCorrectness.core_correctness

    (fun F C V Sem P => True)
(*was:    (fun F C V Sem P => (forall x, Genv.init_mem P = Some x <->
      initial_mem Sem (Genv.globalenv P) x P.(prog_defs)))*)

    ExternIdents epts F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
    forward_simulation (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2).
Proof.
  intros.
  induction X; intros.

(*CASE 1: equality phase*)
  rename i into GenvInit1; rename i0 into GenvInit2.
  destruct g as [HypGenv HypVolatile].
  set (fsim_index := Forward_simulation_eq.core_data R).
  set (fsim_order := Forward_simulation_eq.core_ord R).
  set (fsim_order_wf := Forward_simulation_eq.core_ord_wf R).
  set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
    Forward_simulation_eq.match_core R s (fst x) (fst y) /\ snd x = snd y).
  apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2)
    fsim_index fsim_order fsim_order_wf  fsim_match_states).
  (*initial_state*) simpl. unfold initial_state. intros.
    destruct s1 as [c1 m1].
    destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
    destruct (ePts_ok _ _ H) as [bb [KK1 [KK2 [KK3 KK4]]]].
    assert (X := @Forward_simulation_eq.core_initial _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv P2) epts R _ _ _ KK3 nil).
    simpl in X.  destruct X. constructor.
    destruct H1 as [cc1 [cc2 [ini1 [ini2 mtch]]]].
    exists x. exists (cc2, m1).
    split. simpl. exists bb. exists nil. simpl.
    repeat  split; try constructor. rewrite <- H0. apply KK2.
    assumption.
    apply (Eq_init m1). assumption.
    (*was: destruct (Eq_init m1). apply GenvInit1. apply K5. destruct H1; subst. simpl in *.
           apply GenvInit2. apply H1. *)
    simpl. hnf. simpl in *. split; trivial. rewrite K3 in KK1. inv KK1.  inv K2.
    rewrite K4 in ini1. inv ini1. assumption.
  (*final_state*)
    clear GenvInit1 GenvInit2.
    simpl. unfold final_state. intros. destruct s1 as [c1 m1].
    destruct s2 as [c2 m2]. simpl in *.
    destruct H1. simpl in H3. subst.  simpl in *.
    apply (Forward_simulation_eq.core_halted R _ _ _ _ H1 H2).
  (*diagram*)
    clear GenvInit1 GenvInit2.
    simpl. subst fsim_match_states. simpl. intros.
    destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
    destruct H2. subst.
    inv H1.
  (*corestep*)
    assert (DD := @Forward_simulation_eq.core_diagram _ _ _ _ _ Sem1 Sem2
       (Genv.globalenv P1) (Genv.globalenv P2) epts R _ _ _ _ H6 _ _ H2).
    destruct DD as [c2' [d' [MC myStep]]].
    exists d'. exists (c2', m1'); simpl. split; auto.
    destruct myStep.
    (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
    (*case core_step_star*) right. destruct H1. split; auto. apply corestep_star_star_step; eauto.
  (*external_step*)
    destruct (@Forward_simulation_eq.core_at_external _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv P2) epts R _ _ _ _ _ (ef_sig ef) H2 H8)
      as [AtExt2 TP].
    assert (DD := @Forward_simulation_eq.core_after_external _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv P2) epts R).
    assert (RetTp:= external_call_well_typed _ _ _ _ _ _ _ H9).
    destruct (DD _ _ _ ret _ _ _ H2 H8 AtExt2 TP RetTp)
      as [c1'' [c2' [d' [AftExt1 [AftExt2 CM]]]]]; clear DD.
    rewrite AftExt1 in H10. inv H10.
    exists d'. exists (c2', m1'). simpl.
    split; auto. left.
    eapply plus_one. eapply step_ext_step. apply AtExt2.
      apply external_call_symbols_preserved_gen with (ge1:=(Genv.globalenv P1)).
        apply HypGenv. (*HERE*)
        apply HypVolatile. (*HERE*)
        apply H9.
    apply AftExt2.
 (* fsim_symbols_preserved*) simpl. apply HypGenv. (*SAME HERE*)

(*CASE 2: extension phase*)
  rename i into GenvInit1; rename i0 into GenvInit2.
  destruct g as [HypGenv HypVolatile].
  set (fsim_index := Forward_simulation_ext.core_data R).
  set (fsim_order := Forward_simulation_ext.core_ord R).
  set (fsim_order_wf := Forward_simulation_ext.core_ord_wf R).
  set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
    Forward_simulation_ext.match_state R s (fst x)  (snd x) (fst y) (snd y)).
  apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)
                  (mk_semantics F2 C2 V2 Sem2 P2)
    fsim_index fsim_order fsim_order_wf  fsim_match_states).
  (*initial_state*) simpl.
    unfold initial_state. intros.
    destruct s1 as [c1 m1]. simpl in *.
    destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
    destruct (ePts_ok _ _ H) as [b1 [KK1 [KK2 [Hfound [f1 [f2 [Hf1 Hf2]]]]]]].
    rewrite KK1 in K3. inv K3. inv K2. clear K1 ePts_ok H.
    destruct (Extends_init _ K5) as [m2 [iniMem2 Mextends]].
    (*WAS: apply GenvInit1 in K5. apply Extends_init in K5.
           destruct K5 as [m2 [iniMem2 Mextends]].*)
    assert (X := @Forward_simulation_ext.core_initial _ _ _ _ Sem1 Sem2
     (Genv.globalenv P1) (Genv.globalenv P2)  epts R _ _ _ Hfound nil nil m1 m2).
    destruct X as [d' [c1' [c2' [IniCore1 [IniCore2 ExtMatch]]]]].
    constructor.
    constructor.
    assumption.
    rewrite IniCore1 in K4. inv K4.
    exists d'. exists (c2', m2); simpl.
    split; auto.
    exists b. exists nil. simpl.
    repeat  split; try constructor.
    rewrite <- H0. apply KK2.
    assumption.
   (*apply GenvInit2.*) apply iniMem2.
  (*finalstate*)
    clear GenvInit1 GenvInit2.
    simpl. unfold final_state. intros.
    destruct s1 as [c1 m1].
    destruct s2 as [c2 m2]. simpl in *.
    destruct (Forward_simulation_ext.core_halted R _ _ _ _ _ _ H1 H2)
      as [r2 [LessDefR [SH2 [Ext RVal]]]]; simpl in *; trivial.
    inv LessDefR. simpl in *. assumption.
  (*diagram*)
    clear GenvInit1 GenvInit2.
    simpl. subst fsim_match_states. simpl. intros.
    destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
    inv H1.
  (*corestep*)
    assert (DD := @Forward_simulation_ext.core_diagram _ _ _ _ Sem1 Sem2
       (Genv.globalenv P1) (Genv.globalenv P2) epts R _ _ _ _ H6 _ _ _ H2).
    destruct DD as [c2' [m2' [d'  [MC' myStep]]]].
    exists d'. exists (c2', m2'); simpl. split; auto.
    destruct myStep.
    (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
    (*case core_step_star*) right. destruct H1. split; auto.
        apply corestep_star_star_step; eauto.
  (*external_step*)
    destruct (@Forward_simulation_ext.core_at_external _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv P2) epts R _ _ _ _ _ _ _ _ H2 H8)
      as [args2 [Mextends [lessArgs [TpArgs2 AtExt2]]]].
    assert (EXT:= @external_call_mem_extends _ _ _ _ _ _ _ _ _  _ _ H9 Mextends
               (forall_lessdef_val_listless _ _ lessArgs)).
    destruct EXT as [ret2 [m2' [extCall2 [lessRet [Mextends' MunchOn]]]]].
    assert (extCall2Genv2 : external_call ef (Genv.globalenv P2) args2 m2 t ret2 m2').
    eapply external_call_symbols_preserved_gen.
    apply HypGenv. (*HERE*)
    apply HypVolatile. (*HERE*)
    apply extCall2.
    clear extCall2.
    assert (DD := @Forward_simulation_ext.core_after_external _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv P2) epts R _ _ _ _ _ _ _ _
      ret ret2 m1' m2' _ H2 H8 AtExt2 lessArgs TpArgs2).
    destruct DD as [c1'' [c2' [d' [AftExt1 [AftExt2 Match']]]]].
    eapply external_call_mem_forward; eauto.
    eapply external_call_mem_forward; eauto.
    eapply mem_unchanged_on_sub; eauto.
    assumption.
    assumption.
    apply (external_call_well_typed _ _ _ _ _ _ _ extCall2Genv2).
    rewrite AftExt1 in H10. inv H10.
    exists d'. exists (c2', m2'); simpl.
    split; auto. left.  eapply plus_one.
    apply step_ext_step with (ef:=ef)(args:=args2)(ret:=ret2).
    apply AtExt2.
    apply extCall2Genv2.
    assumption.
  (*fsim_symbols_preserved*) simpl. apply HypGenv. (*SAME HERE*)

  (*CASE 3: injection phase*)
    rename i into GenvInit1; rename i0 into GenvInit2.
    destruct g as [HypGenv HypVolatile].
    set (fsim_index := Forward_simulation_inj.core_data R).
    set (fsim_order := Forward_simulation_inj.core_ord R).
    set (fsim_order_wf := Forward_simulation_inj.core_ord_wf R).
    set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
      exists j,  inject_incr jInit j /\
      Forward_simulation_inj.match_state R s j (fst x)  (snd x) (fst y) (snd y)).
    apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)
                (mk_semantics F2 C2 V2 Sem2 P2)
    fsim_index fsim_order fsim_order_wf  fsim_match_states).
  (*initial_state*) simpl. unfold initial_state. intros.
    destruct s1 as [c1 m1]. simpl in *.
    destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
    destruct (ePts_ok _ _ H) as [b1 [b2 [KK1 [KK2 [Hjb [Hfound [f1 [f2 [Hf1 Hf2]]]]]]]]].
    rewrite KK1 in K3. inv K3. inv K2. clear K1.
    destruct (Inj_init m1) as [m2 [initMem2 Inj]]; clear Inj_init .
        (*apply GenvInit1.*) apply K5.
    assert (X := @Forward_simulation_inj.core_initial _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv P2)  epts R _ _ _ Hfound nil _ _ _ nil _ K4 Inj).
    destruct X as [d' [c2 [iniCore2 Match]]].
    constructor.
    constructor.
    exists d'. exists (c2,m2). simpl in *.
    split; auto. exists b2. exists nil.
    repeat  split; try constructor.
    rewrite <- H0. apply KK2.
    assumption.
    (*apply GenvInit2.*) apply initMem2.
    exists jInit. split; auto.
  (*finalstate*)
    clear GenvInit1 GenvInit2.
    simpl. unfold final_state. intros. destruct s1 as [c1 m1].
    destruct s2 as [c2 m2]. simpl in *.
    destruct H1 as [j [InjJ MCJ]]; simpl in *.
    destruct (Forward_simulation_inj.core_halted R _ _ _ _ _ _ _ MCJ H2)
      as [r2 [InjR [SH2 InjM]]].
    inv InjR. assumption.
  (*diagram*)
    clear GenvInit1 GenvInit2.
    simpl. subst fsim_match_states. simpl. intros.
    destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
    destruct H2 as [j [InjJ MCJ]].
    inv H1.
  (*corestep*)
    assert (DD := @Forward_simulation_inj.core_diagram _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv P2) epts R _ _ _ _ H5 _ _ _ _ MCJ).
    destruct DD as [c2' [m2' [d' [j' [InjJ' [Sep [MC' myStep]]]]]]].
    exists d'. exists (c2', m2'); simpl. split; auto.
    destruct myStep as [H2 | [H2 H3]].
    (*case corestep_plus*)
       left. apply corestep_plus_plus_step; eauto.
    (*case core_step_star*) right. split; auto.
      apply corestep_star_star_step; eauto.
      exists j'; split; auto. eapply inject_incr_trans. apply InjJ. apply InjJ'.
  (*external_step*)
    destruct (@Forward_simulation_inj.core_at_external _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv P2) epts R _ _ _ _ _ _ _ _ _ MCJ H7)
     as[INJ [jPG [args2 [LD [TP AtExt2]]]]].
    apply forall_inject_val_list_inject in LD.
    assert (ZZ:= @external_call_mem_inject ef  _ _
      (Genv.globalenv P1) _ _ _ _ _ j _ _ jPG H8 INJ LD).
    destruct ZZ as [j'  [ret2 [m2' [extCall2 [RetInj [MInj2 [Munch1 [Munch2 [InjJ' Sep']]]]]]]]].
    assert (extCall2Genv2 : external_call ef (Genv.globalenv P2) args2 m2 t ret2 m2').
    eapply external_call_symbols_preserved_gen.
    apply HypGenv. (*HERE*)
    apply HypVolatile. (*HERE*)
    solve[apply extCall2].
    clear extCall2.
    assert (DD := @Forward_simulation_inj.core_after_external _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv P2) epts R i j).
    assert (RetTp:= external_call_well_typed _ _ _ _ _ _ _ H8).
    assert (RetInjOpt: val_inject_opt j' (Some ret) (Some ret2)) by auto.
    destruct (DD j' _ _ _ _ _ _ _ _ _ _ (ef_sig ef) INJ MCJ H7 jPG InjJ' Sep' MInj2 RetInjOpt)
      as [d' [c1'' [c2' [AftExt1 [AftExt2 Match2]]]]]; clear DD.
    eapply external_call_mem_forward; eauto.
    apply mem_unchanged_on_sub with (Q := loc_unmapped j); auto.
    eapply external_call_mem_forward; eauto.
    apply mem_unchanged_on_sub with (Q := loc_out_of_reach j m1); auto.
    eapply external_call_well_typed; eauto.
    rewrite AftExt1 in H9. inv H9.
    exists d'. exists (c2', m2').
    split. left. apply plus_one.
                      eapply (step_ext_step _ _ _ _ _ _ _ _ _ _ _ _ _
                            AtExt2 extCall2Genv2 AftExt2).
    exists j'; simpl.  split;eauto. eapply inject_incr_trans. apply InjJ. apply InjJ'.
  (* fsim_symbols_preserved*) simpl. apply HypGenv. (*SAME HERE*)

 (*CASE 4: transitivity*)
   assert (MM: prog_main P1 = prog_main P2) by
      (eapply CompilerCorrectness.corec_main; eauto).
   spec IHX1. apply H.
   spec IHX1. apply MM.
   spec IHX2. rewrite MM in H. apply H.
   spec IHX2. eapply CompilerCorrectness.corec_main; eauto.
   clear X1 X2.
   eapply compose_forward_simulation; eauto.
Qed.

(* 1. The need for the axiom GenvHyp in all cases (or alternatively
the addition of axioms HypGenv and HypVolatile, at the beginning of
all cases): These are needed in order to apply
external_call_symbols_preserved_gen, in order to establish
external_call ef (GEnv P2) vargs m1 t vres m2, As mentioned in the
file, an alternative proof of this fact using
external_call_symbols_preserved_2 would require a slightly different
axiom on globvars, eliminating the need for HypVolatile.
Additionally, HypGenv is also explicitly required in order to
discharge Xavier's condition fsim_symbols_preserved.

2. The need to establish a "meminj_preserves_globals" property in case
inject-diamond-externalStep.  I temporarily added the condition
meminj_preserves_globals jInit in cc_inj, with the idea that we would
thread it through the execution. But meminj_preserves_globals is
formally not preserved by inj_incr. But maybe the 3rd clause in
meminj_preserves_globals is stronger than what's needed to prove the
CompCert phases?

An alternative (maybe this is needed in any case) would be to have
at_external (or maybe external_call ef ge vargs m1 t vres m2 in
general) imply that (f,d) in ExternIdent, so that we can apply
entries_ok or entries_inject_ok.  But: some externals_funstions
("builtins") dont have idents - so maybe ExternIdents should be of a
different type, not take idents? Or maybe should differentiate in
external_description between builtins and nonbuiltins?

It seems given the strong condition imposed by
meminj_preserves_global, our choice to differentiate between
entries_ok and entries_inject_ok is too fine for current CompCert.
Maybe we soulh use entries_ok even in inject-case (at least for the
sake of demonstrating that our approach works)?
*)

End CompilerCorrectness_implies_forward_simulation.

Lemma transl_program_block_volatile:
  forall {F FF V} (P: AST.program F V) (transf: F -> FF) b,
  block_is_volatile (Genv.globalenv (AST.transform_program transf P)) b =
  block_is_volatile (Genv.globalenv P) b.
Proof. intros. unfold block_is_volatile.
  rewrite Genv.find_var_info_transf. trivial.
Qed.

Module CompilerCorrectnessT_implies_forward_simulation.

(*Similar proof, but explicitly require that P2 be a translation of P1*)
Theorem CoreCorrectnessT_implies_CompcertForwardSimulation:
  forall F1 C1 V1 F2 C2
    (Sem1: CoreSemantics (Genv.t F1 V1) C1 mem)
    (Sem2: CoreSemantics (Genv.t F2 V1) C2 mem)
    P1 P2 ExternIdents epts
    (EXT: In (P1.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents),
    CompilerCorrectness.core_correctnessT

    (fun F C V Sem P => True)
(*was:    (fun F C V Sem P => (forall x, Genv.init_mem P = Some x <->
      initial_mem Sem (Genv.globalenv P) x P.(prog_defs)))*)

    ExternIdents epts F1 C1 V1 F2 C2 Sem1 Sem2 P1 P2 ->
    forward_simulation (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V1 Sem2 P2).
Proof.
  intros.
  induction X; intros.

(*CASE 1: equality phase*)
  rewrite HP in *. clear HP. clear P2.
  rename i into GenvInit1; rename i0 into GenvInit2.
  set (fsim_index := Forward_simulation_eq.core_data R).
  set (fsim_order := Forward_simulation_eq.core_ord R).
  set (fsim_order_wf := Forward_simulation_eq.core_ord_wf R).
  set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
    Forward_simulation_eq.match_core R s (fst x) (fst y) /\ snd x = snd y).
  apply ( @Forward_simulation  (mk_semantics F1 C1 V Sem1 P1)  (mk_semantics F2 C2 V Sem2 (transform_program transf P1))
    fsim_index fsim_order fsim_order_wf  fsim_match_states).
  (*initial_state*) simpl. unfold initial_state. intros.
    destruct s1 as [c1 m1].
    destruct H as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
    destruct (ePts_ok _ _ EXT) as [bb [KK1 [KK2 [KK3 KK4]]]].
    assert (X := @Forward_simulation_eq.core_initial _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv (transform_program transf P1)) epts R _ _ _ KK3 nil).
    simpl in X.  destruct X. constructor.
    destruct H as [cc1 [cc2 [ini1 [ini2 mtch]]]].
    exists x. exists (cc2, m1).
    split. simpl. exists bb. exists nil. simpl.
    repeat  split; try constructor; trivial.
    subst. rewrite Genv.init_mem_transf with (m:=m1). trivial.
    apply K5.
    simpl. hnf. simpl in *. split; trivial. rewrite K3 in KK1. inv KK1.  inv K2.
    rewrite K4 in ini1. inv ini1. assumption.
  (*final_state*)
    clear GenvInit1 GenvInit2.
    simpl. unfold final_state. intros. destruct s1 as [c1 m1].
    destruct s2 as [c2 m2]. simpl in *.
    destruct H. simpl in H1. subst m1. simpl in *.
    apply (Forward_simulation_eq.core_halted R _ _ _ _ H H0).
  (*diagram*)
    clear GenvInit1 GenvInit2.
    simpl. subst fsim_match_states. simpl. intros.
    destruct s1 as [c1 m1]. destruct s2 as [c2 m2].
    destruct s1' as [c1' m1'].  simpl in *.
    destruct H0. subst m1.
    inv H.
  (*corestep*)
    assert (DD := @Forward_simulation_eq.core_diagram _ _ _ _ _ Sem1 Sem2
       (Genv.globalenv P1) (Genv.globalenv (transform_program transf P1))
       epts R _ _ _ _ H4 _ _ H0).
    destruct DD as [c2' [d' [MC myStep]]].
    exists d'. exists (c2', m1'); simpl. split; auto.
    destruct myStep.
    (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
    (*case core_step_star*) right. destruct H. split; auto. apply corestep_star_star_step; eauto.
  (*external_step*)
    destruct (@Forward_simulation_eq.core_at_external _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv (transform_program transf P1))
       epts R _ _ _ _ _ (ef_sig ef) H0 H6)
      as [AtExt2 TP].
    assert (DD := @Forward_simulation_eq.core_after_external _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv (transform_program transf P1)) epts R).
    assert (RetTp:= external_call_well_typed _ _ _ _ _ _ _ H7).
    destruct (DD _ _ _ ret _ _ _ H0 H6 AtExt2 TP RetTp)
      as [c1'' [c2' [d' [AftExt1 [AftExt2 CM]]]]]; clear DD.
    rewrite AftExt1 in H8. inv H8.
    exists d'. exists (c2', m1'). simpl.
    split; auto. left.
    eapply plus_one. eapply step_ext_step. apply AtExt2.
      apply external_call_symbols_preserved_gen with (ge1:=(Genv.globalenv P1)).
        apply Genv.find_symbol_transf.
        apply transl_program_block_volatile.
        eassumption.
    apply AftExt2.
 (* fsim_symbols_preserved*) simpl. apply Genv.find_symbol_transf.
(*CASE 2: extension phase*)
  rewrite HP in *. clear HP P2.
  rename i into GenvInit1; rename i0 into GenvInit2.
  set (fsim_index := Forward_simulation_ext.core_data R).
  set (fsim_order := Forward_simulation_ext.core_ord R).
  set (fsim_order_wf := Forward_simulation_ext.core_ord_wf R).
  set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
    Forward_simulation_ext.match_state R s (fst x)  (snd x) (fst y) (snd y)).
 apply ( @Forward_simulation  (mk_semantics F1 C1 V Sem1 P1)
                  (mk_semantics F2 C2 V Sem2 (transform_program transf P1))
    fsim_index fsim_order fsim_order_wf  fsim_match_states).
  (*initial_state*) simpl.
    unfold initial_state. intros.
    destruct s1 as [c1 m1]. simpl in *.
    destruct H as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
    destruct (ePts_ok _ _ EXT) as [b1 [KK1 [KK2 [Hfound [f1 [f2 [Hf1 Hf2]]]]]]].
    rewrite KK1 in K3. inv K3. inv K2. clear K1 ePts_ok EXT.
    (*destruct (Extends_init _ K5) as [m2 [iniMem2 Mextends]].    *)
    (*WAS: apply GenvInit1 in K5. apply Extends_init in K5.
           destruct K5 as [m2 [iniMem2 Mextends]].*)
    assert (X := @Forward_simulation_ext.core_initial _ _ _ _ Sem1 Sem2
     (Genv.globalenv P1) (Genv.globalenv (transform_program transf P1)) epts R _ _ _ Hfound nil nil m1 m1).
    destruct X as [d' [c1' [c2' [IniCore1 [IniCore2 ExtMatch]]]]].
    constructor.
    constructor.
    apply Mem.extends_refl.
    rewrite IniCore1 in K4. inv K4.
    exists d'. exists (c2', m1); simpl.
    split; auto.
    exists b. exists nil. simpl.
    repeat  split; try constructor.
    apply KK2.
    assumption.
   (*apply GenvInit2.*) apply Genv.init_mem_transf. assumption.
  (*finalstate*)
    clear GenvInit1 GenvInit2.
    simpl. unfold final_state. intros.
    destruct s1 as [c1 m1].
    destruct s2 as [c2 m2]. simpl in *.
    destruct (Forward_simulation_ext.core_halted R _ _ _ _ _ _ H H0)
      as [r2 [LessDefR [SH2 [Ext RVal]]]]; simpl in *; trivial.
    inv LessDefR. simpl in *. assumption.
  (*diagram*)
    clear GenvInit1 GenvInit2.
    simpl. subst fsim_match_states. simpl. intros.
    destruct s1 as [c1 m1]. destruct s2 as [c2 m2].
    destruct s1' as [c1' m1'].  simpl in *.
    inv H.
  (*corestep*)
    assert (DD := @Forward_simulation_ext.core_diagram _ _ _ _ Sem1 Sem2
       (Genv.globalenv P1) (Genv.globalenv (transform_program transf P1))
        epts R _ _ _ _ H4 _ _ _ H0).
    destruct DD as [c2' [m2' [d'  [MC' myStep]]]].
    exists d'. exists (c2', m2'); simpl. split; auto.
    destruct myStep.
    (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
    (*case core_step_star*) right. destruct H. split; auto.
        apply corestep_star_star_step; eauto.
  (*external_step*)
     destruct (@Forward_simulation_ext.core_at_external _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv (transform_program transf P1))
      epts R _ _ _ _ _ _ _ _ H0 H6)
      as [args2 [Mextends [lessArgs [TpArgs2 AtExt2]]]].
    assert (EXTCALL:= @external_call_mem_extends _ _ _ _ _ _ _ _ _  _ _ H7 Mextends
               (forall_lessdef_val_listless _ _ lessArgs)).
    destruct EXTCALL as [ret2 [m2' [extCall2 [lessRet [Mextends' MunchOn]]]]].
    assert (extCall2Genv2 :
      external_call ef (Genv.globalenv (transform_program transf P1)) args2 m2 t ret2 m2').
    eapply external_call_symbols_preserved_gen.
    apply Genv.find_symbol_transf.
    apply transl_program_block_volatile.
    apply extCall2.
    clear extCall2.
    assert (DD := @Forward_simulation_ext.core_after_external _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv (transform_program transf P1)) epts R
       _ _ _ _ _ _ _ args2
      ret ret2 m1' m2' _ H0 H6).
    destruct DD as [c1'' [c2' [d' [AftExt1 [AftExt2 Match']]]]]; trivial.
      eapply external_call_mem_forward; eauto.
      eapply external_call_mem_forward; eauto.
      apply (external_call_well_typed _ _ _ _ _ _ _ extCall2Genv2).
    rewrite AftExt1 in H8. inv H8.
    exists d'. exists (c2', m2'); simpl.
    split; auto. left.  eapply plus_one.
    apply step_ext_step with (ef:=ef)(args:=args2)(ret:=ret2).
    apply AtExt2.
    apply extCall2Genv2.
    assumption.
  (*fsim_symbols_preserved*) simpl.
    apply Genv.find_symbol_transf.

  (*CASE 3: injection phase*)
  rewrite HP in *. clear HP P2.
    rename i into GenvInit1; rename i0 into GenvInit2.
    set (fsim_index := Forward_simulation_inj.core_data R).
    set (fsim_order := Forward_simulation_inj.core_ord R).
    set (fsim_order_wf := Forward_simulation_inj.core_ord_wf R).
    set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
      exists j,  inject_incr (Mem.flat_inj (Mem.nextblock m)) j /\
      Forward_simulation_inj.match_state R s j (fst x)  (snd x) (fst y) (snd y)).
    apply ( @Forward_simulation  (mk_semantics F1 C1 V Sem1 P1)
                (mk_semantics F2 C2 V Sem2 (transform_program transf P1))
    fsim_index fsim_order fsim_order_wf  fsim_match_states).
  (*initial_state*) simpl. unfold initial_state. intros.
    destruct s1 as [c1 m1]. simpl in *.
    destruct H as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
    destruct (ePts_ok _ _ EXT) as [b1 [b2 [KK1 [KK2 [Hjb [Hfound [f1 [f2 [Hf1 Hf2]]]]]]]]].
    rewrite KK1 in K3. inv K3. inv K2. clear K1.
    rewrite K5 in InitMem. inv InitMem.
    assert (Inj:= Genv.initmem_inject _ K5).
    assert (X := @Forward_simulation_inj.core_initial _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv (transform_program transf P1)) epts
       R _ _ _ Hfound nil _ _ _ nil _ K4 Inj).
    destruct X as [d' [c2 [iniCore2 Match]]].
    constructor.
    constructor.
    exists d'. exists (c2,m). simpl in *.
    split; auto. exists b2. exists nil.
    repeat  split; try constructor.
    apply KK2.
    assumption.
    (*apply GenvInit2.*) apply Genv.init_mem_transf. assumption.
    econstructor. split; eauto.
  (*finalstate*)
    clear GenvInit1 GenvInit2.
    simpl. unfold final_state. intros. destruct s1 as [c1 m1]. destruct s2 as [c2 m2]. simpl in *.
    destruct H as [j [InjJ MCJ]]; simpl in *.
    destruct (Forward_simulation_inj.core_halted R _ _ _ _ _ _ _ MCJ H0)
      as [r2 [InjR [SH2 InjM]]].
    inv InjR. assumption.
  (*diagram*)
    clear GenvInit1 GenvInit2.
    simpl. subst fsim_match_states. simpl. intros.
    destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
    destruct H0 as [j [InjJ MCJ]].
    inv H.
  (*corestep*)
    assert (DD := @Forward_simulation_inj.core_diagram _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv (transform_program transf P1))
       epts R _ _ _ _ H3 _ _ _ _ MCJ).
    destruct DD as [c2' [m2' [d' [j' [InjJ' [Sep [MC' myStep]]]]]]].
    exists d'. exists (c2', m2'); simpl. split; auto.
    destruct myStep.
    (*case corestep_plus*)
       left. apply corestep_plus_plus_step; eauto.
    (*case core_step_star*) right. destruct H. split; auto.
      apply corestep_star_star_step; eauto.
      exists j'; split; auto. eapply inject_incr_trans. apply InjJ. apply InjJ'.
  (*external_step*)
    destruct (@Forward_simulation_inj.core_at_external _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv (transform_program transf P1))
       epts R _ _ _ _ _ _ _ _ _ MCJ H5)
     as[INJ [jPG [args2 [LD [TP AtExt2]]]]].
    apply forall_inject_val_list_inject in LD.
    assert (ZZ:= @external_call_mem_inject ef  _ _
      (Genv.globalenv P1) _ _ _ _ _ j _ _ jPG H6 INJ LD).
    destruct ZZ as [j'  [ret2 [m2' [extCall2 [RetInj [MInj2 [Munch1 [Munch2 [InjJ' Sep']]]]]]]]].
    assert (extCall2Genv2 :
      external_call ef (Genv.globalenv (transform_program transf P1)) args2 m2 t ret2 m2').
    eapply external_call_symbols_preserved_gen.
    apply Genv.find_symbol_transf.
    apply transl_program_block_volatile.
    solve[apply extCall2].
    clear extCall2.
    assert (DD := @Forward_simulation_inj.core_after_external _ _ _ _ _ Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv (transform_program transf P1)) epts R i j).
    assert (RetTp:= external_call_well_typed _ _ _ _ _ _ _ H6).
    assert (RetInjOpt: val_inject_opt j' (Some ret) (Some ret2)) by auto.
    destruct (DD j' _ _ _ _ _ _ _ _ _ _ (ef_sig ef) INJ MCJ H5 jPG InjJ' Sep' MInj2 RetInjOpt)
      as [d' [c1'' [c2' [AftExt1 [AftExt2 Match2]]]]]; clear DD.
    eapply external_call_mem_forward; eauto.
    apply mem_unchanged_on_sub with (Q := loc_unmapped j); auto.
    eapply external_call_mem_forward; eauto.
    apply mem_unchanged_on_sub with (Q := loc_out_of_reach j m1); auto.
    eapply external_call_well_typed; eauto.
    rewrite AftExt1 in H7. inv H7.
    exists d'. exists (c2', m2').
    split. left. apply plus_one.
                      eapply (step_ext_step _ _ _ _ _ _ _ _ _ _ _ _ _
                            AtExt2 extCall2Genv2 AftExt2).
    exists j'; simpl.  split;eauto. eapply inject_incr_trans. apply InjJ. apply InjJ'.
  (* fsim_symbols_preserved*) simpl.
    apply Genv.find_symbol_transf.

 (*CASE 4: transitivity*)
   rewrite HP in *; clear P2 HP.
   rewrite HPP in *; clear P3 HPP.
   spec IHX1. apply EXT.
   eapply compose_forward_simulation; eauto.
Qed.

End CompilerCorrectnessT_implies_forward_simulation.
