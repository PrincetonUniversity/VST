Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import sepcomp.Inlining.
Require Import sepcomp.Inliningspec.
Require Import RTL.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.

Require Export Axioms.
Require Import CminorSel_coop.
Require Import RTL_eff.
Require Import RTL_coop.

Load Santiago_tactics.

Variable SrcProg: RTL.program.
Variable TrgProg: RTL.program.
Hypothesis TRANSF: transf_program SrcProg = OK TrgProg.
Let SrcGe : RTL.genv := Genv.globalenv SrcProg.
Let TrgGe : RTL.genv := Genv.globalenv TrgProg.
Let fenv := funenv_program SrcProg.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol TrgGe s = Genv.find_symbol SrcGe s.
Proof.
  intros. apply Genv.find_symbol_transf_partial with (transf_fundef fenv). apply TRANSF.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info TrgGe b = Genv.find_var_info SrcGe b.
Proof.
  intros. apply Genv.find_var_info_transf_partial with (transf_fundef fenv). apply TRANSF.
Qed.

(*LENB: GFP as in selectionproofEFF*)
Definition globalfunction_ptr_inject (j:meminj):=
  forall b f, Genv.find_funct_ptr SrcGe b = Some f -> 
              j b = Some(b,0) /\ isGlobalBlock SrcGe b = true. 

(*The new match_states*)
Inductive match_states (j:meminj): RTL_core -> mem -> RTL_core -> mem -> Prop :=
| match_state:
    forall f s k sp e m tm cs tf ns rs (*map ncont nexits ngoto nret rret*) sp'
           (*(MWF: map_wf map)*)
           (*(TS: tr_stmt tf.(fn_code) map s ns ncont nexits ngoto nret rret)*)
           (*(TF: tr_fun tf map f ngoto nret rret)*)
           (*(TK: tr_cont j tf.(fn_code) map k ncont nexits ngoto nret rret cs)*)
           (*(ME: match_env j map e nil rs)*)
           (*(MEXT: Mem.extends m tm)*)
           (MINJ: Mem.inject j m tm)
    (*(*NEW:*) (SP: sp_preserved j sp sp')*),
      match_states j (RTL_State f s k sp e) m
                   (RTL_State cs tf sp' ns rs) tm
| match_callstate:
    forall f args targs k m tm cs tf
    (*(TF: transl_fundef f = OK tf)*)
    (*(MS: match_stacks j k cs)*)
    (*(LD: Val.lessdef_list args targs)*)
    (*(AINJ: val_list_inject j args targs)*)
    (*(MEXT: Mem.extends m tm)*)
    (*(MINJ: Mem.inject j m tm)*),
      match_states j (RTL_Callstate f args k) m
                   (RTL_Callstate cs tf targs) tm
| match_returnstate:
    forall v tv k m tm cs
    (*(MS: match_stacks j k cs)*)
    (*(LD: Val.lessdef v tv)*)
    (*(VINJ: val_inject j v tv)*)
    (*(MEXT: Mem.extends m tm)*)
    (*(MINJ: Mem.inject j m tm)*),
      match_states j (RTL_Returnstate v k) m
                   (RTL_Returnstate cs tv) tm.

Print restrict.
Definition MATCH (d:RTL_core) mu c1 m1 c2 m2:Prop :=
  match_states (restrict (as_inj mu) (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals SrcGe (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock SrcGe b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.


(** The simulation proof *)
Theorem transl_program_correct:
  forall (R: list_norepet (map fst (prog_defs SrcProg)))
         entrypoints
         (entry_points_ok : 
            forall v1 v2 sig,
              In (v1, v2, sig) entrypoints -> 
              exists b f1 f2, 
                v1 = Vptr b Int.zero 
                /\ v2 = Vptr b Int.zero
                /\ Genv.find_funct_ptr SrcGe b = Some f1
                /\ Genv.find_funct_ptr TrgGe b = Some f2)
         (init_mem: exists m0, Genv.init_mem SrcProg = Some m0),
    SM_simulation.SM_simulation_inject rtl_eff_sem
                                       rtl_eff_sem SrcGe TrgGe entrypoints.

  intros.
  eapply sepcomp.effect_simulations_lemmas.inj_simulation_star_wf.

  Lemma genvs_domain_eq_implication: (exists m0:mem, Genv.init_mem SrcProg = Some m0) -> 
                                     genvs_domain_eq SrcGe TrgGe.
    descend;
    destruct H0 as [b0]; exists b0;
    rewriter_back;
    [rewrite symbols_preserved| rewrite <- symbols_preserved| rewrite varinfo_preserved| rewrite <- varinfo_preserved]; reflexivity.
  Qed.
  Hint Resolve genvs_domain_eq_implication: trans_correct.
  auto with trans_correct.

Lemma MATCH_wd: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                                   (m1 : mem) (c2 : RTL_core) (m2 : mem) (MC:MATCH d mu c1 m1 c2 m2), SM_wd mu.
intros. eapply MC. Qed.
Hint Resolve MATCH_wd: trans_correct.
eauto with trans_correct.
Lemma MATCH_RC: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                             (m1 : mem) (c2 : RTL_core) (m2 : mem) (MC:
                        MATCH d mu c1 m1 c2 m2), REACH_closed m1 (vis mu).
intros. eapply MC. Qed.
Hint Resolve MATCH_RC: trans_correct.
eauto with trans_correct.

Lemma restrict_preserves_globalfun_ptr: forall j X
  (PG : globalfunction_ptr_inject j)
  (Glob : forall b, isGlobalBlock SrcGe b = true -> X b = true),
globalfunction_ptr_inject (restrict j X).
Proof. intros.
  red; intros. 
  destruct (PG _ _ H). split; trivial.
  apply restrictI_Some; try eassumption.
  apply (Glob _ H1).
Qed.
Lemma MATCH_restrict: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                                 (m1 : mem) (c2 : RTL_core) (m2 : mem) (X : block -> bool) (MC: MATCH d mu c1 m1 c2 m2)(HX: forall b : block, vis mu b = true -> X b = true)(RC0:REACH_closed m1 X), MATCH d (restrict_sm mu X) c1 m1 c2 m2.
intros.
Proof. intros.
  destruct MC as [MS [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  rewrite vis_restrict_sm.
  rewrite restrict_sm_all.
  rewrite restrict_nest; intuition.
split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RC.
split. clear -PG Glob HX.
  eapply restrict_sm_preserves_globals; try eassumption.
  unfold vis in HX. intuition.
split. rewrite restrict_sm_all.
  eapply restrict_preserves_globalfun_ptr; try eassumption.
  unfold vis in HX. intuition.
split. 
  rewrite restrict_sm_frgnBlocksSrc. apply Glob.
split. 
  destruct SMV.
  split; intros.
    rewrite restrict_sm_DOM in H1.
    apply (H _ H1).
  rewrite restrict_sm_RNG in H1.
    apply (H0 _ H1).
split. assumption.
  rewrite restrict_sm_all.
  eapply inject_restrict; eassumption.
Qed.
Hint Resolve MATCH_restrict: trans_correct.
auto with trans_correct.
Lemma MATCH_valid:  forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                              (m1 : mem) (c2 : RTL_core) (m2 : mem)
                         (MC: MATCH d mu c1 m1 c2 m2), sm_valid mu m1 m2.
intros.
eapply MC.
Qed.

Hint Resolve MATCH_valid: trans_correct.
eauto with trans_correct.

Lemma MATCH_PG:  forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                                           (m1 : mem) (c2 : RTL_core) (m2 : mem)(
                                      MC: MATCH d mu c1 m1 c2 m2),
                                      meminj_preserves_globals SrcGe (extern_of mu) /\
                                      (forall b : block,
                                         isGlobalBlock SrcGe b = true -> frgnBlocksSrc mu b = true).
Proof.
  intros.
  assert (GF: forall b, isGlobalBlock SrcGe b = true -> frgnBlocksSrc mu b = true).
    apply MC.
  split; trivial.
  rewrite <- match_genv_meminj_preserves_extern_iff_all; trivial.
    apply MC. apply MC.
Qed.
Hint Resolve MATCH_PG: trans_correct.
eauto with trans_correct.
Lemma MATCH_initial: forall v1 v2 sig entrypoints
      (EP: In (v1, v2, sig) entrypoints)
      (entry_points_ok : forall (v1 v2 : val) (sig : signature),
                  In (v1, v2, sig) entrypoints ->
                  exists b f1 f2,
                    v1 = Vptr b Int.zero /\
                    v2 = Vptr b Int.zero /\
                    Genv.find_funct_ptr SrcGe b = Some f1 /\
                    Genv.find_funct_ptr TrgGe b = Some f2)
      vals1 c1 m1 j vals2 m2 (DomS DomT : block -> bool)
      (Ini: initial_core rtl_eff_sem SrcGe v1 vals1 = Some c1)
      (Inj: Mem.inject j m1 m2)
      (VInj: Forall2 (val_inject j) vals1 vals2)
      (PG:meminj_preserves_globals SrcGe j)
      (R : list_norepet (map fst (prog_defs SrcProg)))
      (J: forall b1 b2 delta, j b1 = Some (b2, delta) -> 
            (DomS b1 = true /\ DomT b2 = true))
      (RCH: forall b, REACH m2 
          (fun b' : block => isGlobalBlock TrgGe b' || getBlocks vals2 b') b = true ->
          DomT b = true)
      (InitMem : exists m0 : mem, Genv.init_mem SrcProg = Some m0 
               /\ Ple (Mem.nextblock m0) (Mem.nextblock m1) 
               /\ Ple (Mem.nextblock m0) (Mem.nextblock m2))   
      (GDE: genvs_domain_eq SrcGe TrgGe)
      (HDomS: forall b : block, DomS b = true -> Mem.valid_block m1 b)
      (HDomT: forall b : block, DomT b = true -> Mem.valid_block m2 b),
exists c2,
  initial_core rtl_eff_sem TrgGe v2 vals2 = Some c2 /\
  MATCH c1
    (initial_SM DomS DomT
       (REACH m1 (fun b : block => isGlobalBlock SrcGe b || getBlocks vals1 b))
       (REACH m2 (fun b : block => isGlobalBlock TrgGe b || getBlocks vals2 b))
       j) c1 m1 c2 m2.
intros.
  inversion Ini.
  unfold CMinSel_initial_core in H0. unfold ge in *. unfold TrgGe in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv SrcProg) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
    Lemma function_ptr_translated:
  forall (b: block) (f: CminorSel.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr TrgGe b = Some tf /\ transl_fundef f = OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transl_fundef _ TRANSL).
  exploit function_ptr_translated; eauto. intros [tf [FP TF]].
  exists (RTL_Callstate nil tf vals2).
  split.
    destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
    subst. inv A. rewrite C in Heqzz. inv Heqzz.
    unfold tge in FP. rewrite D in FP. inv FP.
    unfold cminsel_eff_sem, cminsel_coop_sem. simpl.
    case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
    solve[rewrite D; auto].

    intros CONTRA.
    solve[elimtype False; auto].
(*  assert (exists targs tres, type_of_fundef f = Tfunction targs tres).
         destruct f; simpl. eexists; eexists. reflexivity.
         eexists; eexists. reflexivity.
  destruct H as [targs [tres Tfun]].*)
  destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
     VInj J RCH PG GDE HDomS HDomT _ (eq_refl _))
    as [AA [BB [CC [DD [EE [FF GG]]]]]].
  split.
    eapply match_callstate; try eassumption.
      constructor.
      rewrite initial_SM_as_inj.
        unfold vis, initial_SM; simpl.
        apply forall_inject_val_list_inject.
        eapply restrict_forall_vals_inject; try eassumption.
          intros. apply REACH_nil. rewrite H; intuition.
    rewrite initial_SM_as_inj.
      unfold vis, initial_SM; simpl.
      eapply inject_restrict; eassumption.
  intuition.
    rewrite match_genv_meminj_preserves_extern_iff_all.
      assumption.
      apply BB.
      apply EE.
    (*as in selectionprffEFF*)
    rewrite initial_SM_as_inj.
      red; intros. specialize (Genv.find_funct_ptr_not_fresh prog). intros.
         destruct InitMem as [m0 [INIT_MEM [? ?]]].
         specialize (H0 _ _ _ INIT_MEM H). 
         destruct (valid_init_is_global _ R _ INIT_MEM _ H0) as [id Hid]. 
           destruct PG as [PGa [PGb PGc]]. split. eapply PGa; eassumption.
         unfold isGlobalBlock. 
          apply orb_true_iff. left. apply genv2blocksBool_char1.
            simpl. exists id; eassumption.
    rewrite initial_SM_as_inj; assumption.
Qed.




apply MATCH_REACH_REACH.
Lemma inject_val_inject_halted: forall (cd : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                                       (m1 : mem) (c2 : RTL_core) (m2 : mem) (v1 : val),
                                  MATCH cd mu c1 m1 c2 m2 ->
                                  halted rtl_eff_sem c1 = Some v1 ->
                                  exists v2 : val,
                                    Mem.inject (as_inj mu) m1 m2 /\
                                    val_inject (restrict (as_inj mu) (vis mu)) v1 v2 /\
                                    halted rtl_eff_sem c2 = Some v2.
Admitted.
apply inject_val_inject_halted.
Lemma at_external_lemma: forall (mu : SM_Injection) (c1 : RTL_core) (m1 : mem) 
                                (c2 : RTL_core) (m2 : mem) (e : external_function) 
                                (vals1 : list val) (ef_sig : signature),
                           MATCH c1 mu c1 m1 c2 m2 ->
                           at_external rtl_eff_sem c1 = Some (e, ef_sig, vals1) ->
                           Mem.inject (as_inj mu) m1 m2 /\
                           (exists vals2 : list val,
                              Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\
                              at_external rtl_eff_sem c2 = Some (e, ef_sig, vals2)).
Admitted.
apply at_external_lemma.



Record map_wf (m: mapping) : Prop :=
  mk_map_wf {
      map_wf_inj:
        (forall id1 id2 r,
           m.(map_vars)!id1 = Some r -> m.(map_vars)!id2 = Some r -> id1 = id2);
      map_wf_disj:
        (forall id r,
           m.(map_vars)!id = Some r -> In r m.(map_letvars) -> False)
    }.

Inductive match_states (j:meminj): CMinSel_core -> mem -> RTL_core -> mem -> Prop :=
| match_state:
    forall f s k sp e m tm cs tf ns rs map ncont nexits ngoto nret rret sp'
           (MWF: map_wf map)
           (TS: tr_stmt tf.(fn_code) map s ns ncont nexits ngoto nret rret)
           (TF: tr_fun tf map f ngoto nret rret)
           (TK: tr_cont j tf.(fn_code) map k ncont nexits ngoto nret rret cs)
           (ME: match_env j map e nil rs)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject j m tm)
                 (*NEW:*) (SP: sp_preserved j sp sp'),
      match_states j (CMinSel_State f s k sp e) m
                   (RTL_State cs tf sp' ns rs) tm
| match_callstate:
    forall f args targs k m tm cs tf
           (TF: transl_fundef f = OK tf)
           (MS: match_stacks j k cs)
        (*(LD: Val.lessdef_list args targs)*)
        (AINJ: val_list_inject j args targs)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject j m tm),
      match_states j (CMinSel_Callstate f args k) m
                   (RTL_Callstate cs tf targs) tm
| match_returnstate:
    forall v tv k m tm cs
           (MS: match_stacks j k cs)
        (*(LD: Val.lessdef v tv)*)
        (VINJ: val_inject j v tv)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject j m tm),
      match_states j (CMinSel_Returnstate v k) m
                   (RTL_Returnstate cs tv) tm.



Definition MATCH (d:RTL_core) mu c1 m1 c2 m2:Prop :=
  match_states (restrict (as_inj mu) (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.

Print effstep.
Print rtl_eff_sem.
Print vis.
Print locBlocksSrc.

Variable tprog: RTL.program.
Let tge : RTL.genv := Genv.globalenv tprog.
Print genv.

Lemma MATCH_effcore_diagram: forall 
                               st1 m1 st1' m1' (U1 : block -> Z -> bool) ge'
                               (CS: effstep rtl_eff_sem ge' U1 st1 m1 st1' m1') (* unpacks the effect step. RTL_effstep. *)
                               st2 mu m2 
                               (UHyp: forall b z, U1 b z = true -> 
                                                  Mem.valid_block m1 b -> vis mu b = true) (* Proof that allocated valid blocks are visible in the source*)
                             (*(MTCH: MATCH st1 mu st1 m1 st2 m2)*),
                             exists st2' m2' mu', exists U2 : block -> Z -> bool,
                                                    (effstep_plus rtl_eff_sem tge U2 st2 m2 st2' m2' \/
                                                     effstep_star rtl_eff_sem tge U2 st2 m2 st2' m2' (*/\ lt_state st1' st1*))
                                                    /\ intern_incr mu mu' /\
                                                    sm_inject_separated mu mu' m1 m2 /\
                                                    sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                                                    (*MATCH st1' mu' st1' m1' st2' m2' /\ *)
                                                    (forall (b : block) (ofs : Z),
                                                       U2 b ofs = true ->
                                                       Mem.valid_block m2 b /\
                                                       (locBlocksTgt mu b = false ->
                                                        exists (b1 : block) (delta1 : Z),
                                                          foreign_of mu b1 = Some (b, delta1) /\
                                                          U1 b1 (ofs - delta1)%Z = true /\
                                                          Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
  (*New script*)
  intros st1 m1 st1' m1' U1 ge' CS. intros. 
  eexists. exists m2, mu, EmptyEffect.
  split.
  right.






  intros st1 m1 st1' m1' U1 ge'. CS.

  induction CS; intros; eexists. (*12 Cases*)

  (*Case: skip seq*)
  exists m2, mu. 
  exists EmptyEffect.
  split.
  right.
  unfold vis in UHyp.
  unfold effstep_star; exists O; simpl.
  reflexivity.

  split. 
  apply intern_incr_refl.

  split.
  apply sm_inject_separated_same_sminj.

  split.
  Lemma sm_locally_allocated_refl: forall mu m1 m2, sm_locally_allocated mu mu m1 m2 m1 m2.
  Admitted.
  apply sm_locally_allocated_refl.
  intros. unfold EmptyEffect in H0.
  contradict H0; auto.

  (*Case: skip block*)
  exists m2, mu.
  exists EmptyEffect. (*This should change*)
  split. 
  right.
  unfold effstep_star; exists O; simpl.
  reflexivity.

  split.
  apply intern_incr_refl.

  split.
  apply sm_inject_separated_same_sminj.

  split.
  apply sm_locally_allocated_refl.

  intros. unfold EmptyEffect in H1.
  contradict H1; auto.

  (*Case: skip return*)
  exists m2, mu.
  exists EmptyEffect. (*This should change*)
  split. 
  right.
  unfold effstep_star; exists O; simpl.
  reflexivity.

  split.
  apply intern_incr_refl.

  split.
  apply sm_inject_separated_same_sminj.

  split.
  apply sm_locally_allocated_refl.

  intros. unfold EmptyEffect in H2.
  contradict H2; auto.

  (*assign*)

  exists m2, mu.

  exists EmptyEffect. (*This should change*)
  split. 
  right.
  unfold effstep_star. exists O. simpl.
  reflexivity.

  split.
  apply intern_incr_refl.

  split.
  apply sm_inject_separated_same_sminj.


  split. admit.

  intros. unfold EmptyEffect in H2.
  contradict H2; auto.




  split_allsplit.

  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  split. (* effste*)
  unfold effstep_plus.
  unfold effstep_star.
  (*Lemma about effstepN.*)

  Focus 2. split.
  (*intern_incr
unfold intern_incr.*)

  Focus 2. split.
  unfold sm_inject_separated.

  Focus 2. split.
  unfold sm_locally_allocated.
