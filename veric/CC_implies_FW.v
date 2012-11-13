Add LoadPath "..".
Require Import veric.base.
Require Import compcert.Events.
Require Import veric.sim.
Require Import compcert.Smallstep.
(*
Section CompcertCoreSem_to_semantics.*)
Section CoreSem_to_semantics.
    Variables (F C V:Type).
    Let genv  := Genv.t F V.
(*    Variable (Sem:CompcertCoreSem genv C (list (ident * globvar V))). (*HERE we specialize type D to program variables*)
*)
    Variable (Sem:CoreSemantics genv C mem (list (ident * globvar V))). (*HERE we specialize type D to program variables*)

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

    (*Definition main_sig : signature := 
       mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint).*)
    Definition main_sig : signature := 
       mksignature (nil) (Some AST.Tint).

    Definition initial_state (st:state) : Prop :=
      exists b, exists vals,
        Forall2 (val_inject (Mem.flat_inj (Mem.nextblock (snd st)))) vals vals /\
        Forall2 Val.has_type vals (sig_args main_sig) /\
        Genv.find_symbol (Genv.globalenv prog) (prog_main prog) = Some b /\
        make_initial_core Sem (Genv.globalenv prog) (Vptr b Int.zero) vals = Some (fst st) /\
        Genv.init_mem prog = Some (snd st). 

   (*Require that return values are int here - that's what we need below for mk_semantics*)
    Definition final_state (st:state) (i:int) : Prop :=
      safely_halted Sem (Genv.globalenv prog) (fst st) = Some (Vint i).

   Definition mk_semantics: semantics :=
           Semantics  step initial_state final_state (Genv.globalenv prog).

  Lemma corestep_plus_step: forall  ge c m c' m',
         corestep Sem ge c m c' m' ->
         plus step ge (c, m) E0 (c', m').
    Proof. intros.  eapply plus_left. eapply step_corestep. apply H.  apply star_refl. rewrite E0_left. trivial. Qed.

  Lemma corestep_plus_plus_step: forall ge c m c' m',
              corestep_plus Sem ge c m c' m' -> plus step ge (c, m) E0 (c', m').
    Proof. intros. unfold corestep_plus in H. destruct H as [n Hn].
       generalize dependent m.  generalize dependent c. 
      induction n.
         simpl; intros. destruct Hn as [c2 [m2 [Hstep X]]]. inv X. eapply corestep_plus_step; auto.
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
(*
  Lemma corestep_plus_step: forall F C V (Sem:CompcertCoreSem (Genv.t F V) C  (list (ident * globvar V))) P c m c' m',
         corestep Sem (Genv.globalenv P) c m c' m' ->
         plus (step F C V Sem) (Genv.globalenv P) (c, m) E0 (c', m').
    Proof. intros.  eapply plus_left. eapply step_corestep. apply H.  apply star_refl. rewrite E0_left. trivial. Qed.

  Lemma corestep_plus_plus_step: forall F C V (Sem:CompcertCoreSem (Genv.t F V) C (list (ident * globvar V))) P c m c' m',
              corestep_plus Sem (Genv.globalenv P) c m c' m' -> plus (step F C V Sem) (Genv.globalenv P) (c, m) E0 (c', m').
    Proof. intros. unfold corestep_plus in H. destruct H as [n Hn].
       generalize dependent m.  generalize dependent c. 
      induction n.
         simpl; intros. destruct Hn as [c2 [m2 [Hstep X]]]. inv X. eapply corestep_plus_step; auto.
      intros. simpl in Hn. destruct Hn as [c1 [m1 [Hstep X]]].
          eapply plus_left. eapply step_corestep. apply Hstep.
             eapply plus_star. eapply IHn. apply X.  rewrite E0_left. trivial.
   Qed.

  Lemma corestep_star_star_step: forall F C V (Sem:CompcertCoreSem (Genv.t F V) C  (list (ident * globvar V))) P c m c' m',
              corestep_star Sem (Genv.globalenv P) c m c' m' -> star (step F C V Sem) (Genv.globalenv P) (c, m) E0 (c', m').
    Proof. intros. unfold corestep_star in H. destruct H as [n Hn].
      destruct n; simpl in Hn. inv Hn. apply star_refl. 
      eapply plus_star. eapply corestep_plus_plus_step. exists n. apply Hn.
    Qed.
*)

(*LENB: INSTEAD OF USING THIS (INCORRECT) LEMMA IN THE PROOF BELOW
I added the hypothesis meminj_preserves_globals ge1 j in Sim_inj.at_external and after_external.
*)
Goal (*Lemma meminj_preserves_globals_inject_incr:*) forall {F V} (ge: Genv.t F V) j j'
              (MPj: meminj_preserves_globals ge j) (InjJ : inject_incr j j'),
              meminj_preserves_globals ge j'.
  Proof. intros.
       destruct MPj as [MP1 [MP2 MP3]].
       split. clear MP2 MP3. intros. apply InjJ. eapply MP1. apply H.
       split. clear MP1 MP3. intros. apply InjJ. eapply MP2. apply H.
       intros. admit. (*does not hold*)
  Qed.

Theorem CoreCorrectness_implies_CompcertForwardSimulation:
     forall F1 C1 V1 F2 C2 V2
(*        (Sem1: CompcertCoreSem (Genv.t F1 V1) C1 (list (ident * globvar V1)))
        (Sem2: CompcertCoreSem (Genv.t F2 V2) C2  (list (ident * globvar V2)))*)
        (Sem1: CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globvar V1)))
        (Sem2: CoreSemantics (Genv.t F2 V2) C2 mem (list (ident * globvar V2)))
        P1 P2 ExternIdents,
        In (P1.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents  -> P1.(prog_main) = P2.(prog_main) ->
        CompilerCorrectness.core_correctness
             (fun F C V Sem P => (forall x, Genv.init_mem P = Some x <-> initial_mem Sem (Genv.globalenv P) x P.(prog_vars)))
              ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
        forward_simulation (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2).
Proof.
  intros.
  induction X; intros.
  Focus 4. (*trans_case*)
     assert (MM: prog_main P1 = prog_main P2). eapply CompilerCorrectness.corec_main; eauto.
      spec IHX1.  apply H.
      spec IHX1. apply MM.  
      spec IHX2. rewrite MM in H. apply H.
      spec IHX2. eapply CompilerCorrectness.corec_main; eauto.
      clear X1 X2.
      eapply compose_forward_simulation; eauto.
  (*equals_case*)
        rename i into GenvInit1; rename i0 into GenvInit2.
        destruct g as [HypGenv HypVolatile].
        set (fsim_index := Sim_eq.core_data R).
        set (fsim_order := Sim_eq.core_ord R).
        set (fsim_order_wf := Sim_eq.core_ord_wf R).
        set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
                          Sim_eq.match_core R s (fst x) (fst y) /\ snd x = snd y).
        apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2)
                        fsim_index fsim_order fsim_order_wf  fsim_match_states).
             (*initial_state*) simpl. unfold initial_state. intros.
                      destruct s1 as [c1 m1].
                      destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
                      destruct (ePts_ok _ _ H) as [bb [KK1 [KK2 [KK3 KK4]]]].
                      assert (X := @Sim_eq.core_initial _ _ _ _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ KK3 nil).
                      simpl in X.  destruct X. constructor. 
                            destruct H1 as [cc1 [cc2 [ini1 [ini2 mtch]]]].
                          exists x. exists (cc2,m1).
                         split. simpl. exists bb. exists nil. simpl.
                             repeat  split; try constructor. rewrite <- H0. apply KK2.
                                assumption.
                           destruct (Eq_init m1).  apply GenvInit1. apply K5. destruct H1; subst. simpl in *. apply GenvInit2. apply H1. 
                      simpl. hnf. simpl in *. split; trivial. rewrite K3 in KK1. inv KK1.  inv K2. rewrite K4 in ini1.  inv ini1. assumption.
           (*finalstate*)
                 clear GenvInit1 GenvInit2.
                 simpl. unfold final_state. intros. destruct s1 as [c1 m1]. destruct s2 as [c2 m2]. simpl in *.
                      destruct H1. simpl in H3. subst.  simpl in *.
                      apply (Sim_eq.core_halted R _ _ _ _ H1 H2).
                      (*apply (@Sim_eq.core_halted _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ _ H1 H2).*)
           (*diagram*)
                 clear GenvInit1 GenvInit2.
                 simpl. subst fsim_match_states. simpl. intros.
                destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
                      destruct H2. subst.
                 inv H1.
                 (*corestep*)  
                   assert (DD := @Sim_eq.core_diagram _ _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ H6 _ _ H2).
                   destruct DD as [c2' [d' [MC myStep]]].
                  exists d'. exists (c2', m1'); simpl. split; auto.
                    destruct myStep.
                      (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
                      (*case core_step_star*) right.  destruct H1. split; auto. apply corestep_star_star_step; eauto.
               (*external_step*) 
                    destruct (@Sim_eq.core_at_external _ _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ (ef_sig ef) H2 H8) as [AtExt2 TP].
                    assert (DD := @Sim_eq.core_after_external _ _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R).
                    assert (RetTp:= external_call_well_typed _ _ _ _ _ _ _ H9).
                    destruct (DD _ _ _ ret _ _ _ H2 H8 AtExt2 TP RetTp) as [c1'' [c2' [d' [AftExt1 [AftExt2 CM]]]]]; clear DD.
                    rewrite AftExt1 in H10. inv H10.
                    exists d'. exists (c2', m1'). simpl.
                    split; auto. left.  eapply plus_one. eapply step_ext_step. apply AtExt2. Focus 2. apply AftExt2.
                                 apply external_call_symbols_preserved_gen with (ge1:=(Genv.globalenv P1)).
                                        apply HypGenv. (*HERE*)
                                        apply HypVolatile. (*HERE*)
                                        apply H9. 
         (* fsim_symbols_preserved*) simpl. apply HypGenv. (*SAME HERE*) 
   (*extends*) 
        rename i into GenvInit1; rename i0 into GenvInit2.
        destruct g as [HypGenv HypVolatile].
        set (fsim_index := Sim_ext.core_data R).
        set (fsim_order := Sim_ext.core_ord R).
        set (fsim_order_wf := Sim_ext.core_ord_wf R).
        set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
                        Sim_ext.match_state R s (fst x)  (snd x) (fst y) (snd y)).
        apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2)
                        fsim_index fsim_order fsim_order_wf  fsim_match_states).
             (*initial_state*) simpl. unfold initial_state. intros.
                      destruct s1 as [c1 m1]. simpl in *.
                      destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
                       destruct (ePts_ok _ _ H) as [b1 [KK1 [KK2 [Hfound [f1 [f2 [Hf1 Hf2]]]]]]].
                       rewrite KK1 in K3. inv K3. inv K2. clear K1 ePts_ok H.
                       apply GenvInit1 in K5. apply Extends_init in K5. destruct K5 as [m2 [iniMem2 Mextends]].
                      assert (X := @Sim_ext.core_initial _ _ _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ Hfound nil nil m1 m2).
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
                         apply GenvInit2. apply iniMem2. 
           (*finalstate*)
                 clear GenvInit1 GenvInit2.
                 simpl. unfold final_state. intros. destruct s1 as [c1 m1]. destruct s2 as [c2 m2]. simpl in *.
                    destruct (Sim_ext.core_halted R _ _ _ _ _ _ H1 H2) as [r2 [LessDefR [SH2 Ext]]].
                    inv LessDefR. simpl in *. assumption.
                    (*apply (@Sim_ext.core_halted _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ _ _ _ H1 H2).*)
           (*diagram*)
                 clear GenvInit1 GenvInit2.
                 simpl. subst fsim_match_states. simpl. intros.
                destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
                 inv H1. 
                 (*corestep*)  
                   assert (DD := @Sim_ext.core_diagram _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ H6 _ _ _ H2).
                   destruct DD as [c2' [m2' [d'  [MC' myStep]]]].
                  exists d'. exists (c2', m2'); simpl. split; auto.
                    destruct myStep.
                      (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
                      (*case core_step_star*) right.  destruct H1. split; auto. apply corestep_star_star_step; eauto.
               (*external_step*) 
                    destruct (@Sim_ext.core_at_external _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ _ _ _ H2 H8) as [args2 [Mextends [lessArgs [TpArgs2 AtExt2]]]].
                   assert (EXT:= @external_call_mem_extends _ _ _ _ _ _ _ _ _  _ _ H9 Mextends (forall_lessdef_val_listless _ _ lessArgs)).
                   destruct EXT as [ret2 [m2' [extCall2 [lessRet [Mextends' MunchOn]]]]].
                   assert (extCall2Genv2 : external_call ef (Genv.globalenv P2) args2 m2 t ret2 m2').
                         eapply external_call_symbols_preserved_gen. 
                             apply HypGenv. (*HERE*) 
                             apply HypVolatile. (*HERE*)
                             apply extCall2.
                         (*An alternative would be to use this proof of extCall2Genv2:
                                    apply (@external_call_symbols_preserved_2 ef F1 V1 F2 V2 (fun v1 =>Errors.Error nil)) with (ge1:=(Genv.globalenv P1)).
                                          apply extCall2.
                                          apply HypGenv. (*HERE*) 
                                          simpl. intros.  assert (ECP:= external_call_spec ef). admit. (*first hyp on globvars*) 
                                          simpl. admit. (*second hyp on globvars*) 
                           *)
                    clear extCall2.
                    assert (DD := @Sim_ext.core_after_external _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ _ _ _ ret ret2 m1' m2' _ H2 H8 AtExt2 lessArgs TpArgs2).
                    destruct DD as [c1'' [c2' [d' [AftExt1 [AftExt2 Match']]]]].
                            eapply external_call_mem_forward; eauto.
                            eapply external_call_mem_forward; eauto.
                            assumption.
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
         (* fsim_symbols_preserved*) simpl. apply HypGenv. (*SAME HERE*)  
   (*inject*)
        rename i into GenvInit1; rename i0 into GenvInit2.
        destruct g as [HypGenv HypVolatile].
        set (fsim_index := Sim_inj.core_data R).
        set (fsim_order := Sim_inj.core_ord R).
        set (fsim_order_wf := Sim_inj.core_ord_wf R).
        set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
                        exists j,  inject_incr jInit j /\  Sim_inj.match_state R s j (fst x)  (snd x) (fst y) (snd y)).
        apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2)
                        fsim_index fsim_order fsim_order_wf  fsim_match_states).
             (*initial_state*) simpl. unfold initial_state. intros.
                      destruct s1 as [c1 m1]. simpl in *.
                      destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
                       destruct (ePts_ok _ _ H) as [b1 [b2 [KK1 [KK2 [Hjb [Hfound [f1 [f2 [Hf1 Hf2]]]]]]]]].
                      rewrite KK1 in K3. inv K3. inv K2. clear K1.
                       destruct (Inj_init m1) as [m2 [initMem2 Inj]]; clear Inj_init . apply GenvInit1. apply K5.
                        assert (X := @Sim_inj.core_initial _ _ _ _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ Hfound nil _ _ _ nil _ K4 Inj).
                        (*would need relationship between entrypoints and externidents assert (ZZ: (forall (w1 w2 : val) (sigg : signature),  In (w1,w2, sigg) entrypoints -> val_inject j w1 w2)).
                             intros.  unfold CompilerCorrectness.entries_inject_ok in ext_ok. apply ext_ok in H1.*)
                        destruct X as [d' [c2 [iniCore2 Match]]].
                          constructor.
                          constructor. 
                          exists d'. exists (c2,m2). simpl in *.
                          split; auto. exists b2. exists nil.
                             repeat  split; try constructor.
                             rewrite <- H0. apply KK2.
                             assumption.
                             apply GenvInit2. apply initMem2.
                         exists jInit. split; auto. 
           (*finalstate*)
                 clear GenvInit1 GenvInit2.
                 simpl. unfold final_state. intros. destruct s1 as [c1 m1]. destruct s2 as [c2 m2]. simpl in *.
                      destruct H1 as [j [InjJ MCJ]]; simpl in *.
                      destruct (Sim_inj.core_halted R _ _ _ _ _ _ _ MCJ H2) as [r2 [InjR [SH2 InjM]]].
                      inv InjR. assumption.
           (*diagram*) 
                 clear GenvInit1 GenvInit2.
                 simpl. subst fsim_match_states. simpl. intros.
                destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
                destruct H2 as [j [InjJ MCJ]].
                 inv H1. 
                 (*corestep*)  
                   assert (DD := @Sim_inj.core_diagram _ _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ H5 _ _ _ _ MCJ).
                   destruct DD as [c2' [m2' [d' [j' [InjJ' [Sep [MC' myStep]]]]]]].
                  exists d'. exists (c2', m2'); simpl. split; auto.
                    destruct myStep.
                      (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
                      (*case core_step_star*) right.  destruct H1. split; auto. apply corestep_star_star_step; eauto.
                   exists j'; split; auto. eapply inject_incr_trans. apply InjJ. apply InjJ'.                    
               (*external_step*) 
                    destruct (@Sim_inj.core_at_external _ _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ _ _ _ _ MCJ H7) 
                               as[INJ [jPG [args2 [LD [TP AtExt2]]]]].
                    (*LENB: HERE's where we need that j preserves globals.
                            assert (HH: meminj_preserves_globals (Genv.globalenv P1) j).
                       eapply meminj_preserves_globals_inject_incr. apply preserves_globals. apply InjJ.*)
                           (* it seems inject doesn't preserve globals!
                             split; intros. destruct HGenv1. apply (H3 _ (id, CompilerCorrectness.extern_func (ef_sig ef))) in H8.  apply ext_ok in H8.
                                    destruct H8 as [b1 [b2 [Hb1 [Hb2 [Hb1b2 _]]]]]. rewrite Hb1 in H1. inv H1.  apply InjJ. assumption.*)
                    apply forall_inject_val_list_inject in LD.
                    assert (ZZ:= @external_call_mem_inject ef  _ _ (Genv.globalenv P1) _ _ _ _ _ j _ _ jPG H8 INJ LD).
                    destruct ZZ as [j'  [ret2 [m2' [extCall2 [RetInj [MInj2 [Munch1 [Munch2 [InjJ' Sep']]]]]]]]].
                    assert (extCall2Genv2 : external_call ef (Genv.globalenv P2) args2 m2 t ret2 m2'). 
                         eapply external_call_symbols_preserved_gen. 
                             apply HypGenv. (*HERE*) 
                             apply HypVolatile. (*HERE*)
                             apply extCall2.
                          (*An alternative would be the following proof of extCall2Genv2:
                                    apply (@external_call_symbols_preserved_2 ef F1 V1 F2 V2 (fun v1 =>Errors.Error nil)) with (ge1:=(Genv.globalenv P1)).
                                          apply extCall2.
                                          admit. (*symmetric hypothesis on Genv.findSymbol*) 
                                          simpl. admit. (*first hyp on globvars*) 
                                          simpl. admit. (*second hyp on globvars*) *)
                    clear extCall2.
                    assert (DD := @Sim_inj.core_after_external _ _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) 
                                               entrypoints R i j).
                    assert (RetTp:= external_call_well_typed _ _ _ _ _ _ _ H8).
                    destruct (DD j' _ _ _ _ _ _ _ _ _ _ (ef_sig ef) INJ MCJ H7 jPG InjJ' Sep' MInj2 RetInj) as [d' [c1'' [c2' [AftExt1 [AftExt2 Match2]]]]]; clear DD.
                         eapply external_call_mem_forward; eauto.
                         apply Munch1.
                         eapply external_call_mem_forward; eauto.
                         apply Munch2.
                         eapply external_call_well_typed. apply extCall2Genv2. 
                      rewrite AftExt1 in H9. inv H9.
                         exists d'. exists (c2', m2').
                         split. left. apply plus_one. eapply  step_ext_step. apply AtExt2. apply extCall2Genv2. apply AftExt2. 
                         exists j'; simpl.  split;eauto. eapply inject_incr_trans. apply InjJ. apply InjJ'.
         (* fsim_symbols_preserved*) simpl. apply HypGenv. (*SAME HERE*)
Qed.

(*We may lift the result to CompcertCoreSem's*)
Theorem CompilerCorrectness_implies_CompcertForwardSimulation:
     forall F1 C1 V1 F2 C2 V2
        (Sem1: CompcertCoreSem (Genv.t F1 V1) C1 (list (ident * globvar V1)))
        (Sem2: CompcertCoreSem (Genv.t F2 V2) C2  (list (ident * globvar V2)))
        P1 P2 ExternIdents,
        In (P1.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents  -> P1.(prog_main) = P2.(prog_main) ->
        CompilerCorrectness.compiler_correctness
             (fun F C V Sem P => (forall x, Genv.init_mem P = Some x <-> initial_mem Sem (Genv.globalenv P) x P.(prog_vars)))
              ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
        forward_simulation (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2).
Proof.
  intros. eapply CoreCorrectness_implies_CompcertForwardSimulation.
       apply H. apply H0. 
   clear H H0. induction X.
         eapply CompilerCorrectness.corec_eq; eassumption.
         eapply CompilerCorrectness.corec_ext; eassumption.
         eapply CompilerCorrectness.corec_inj; eassumption.
         eapply CompilerCorrectness.corec_trans; eassumption. 
Qed.

(*The result of Theorem CompilerCorrectness_implies_CompcertForwardSimulation as a direct proof*)
Theorem CompilerCorrectness_implies_CompcertForwardSimulation_explicit_proof:
     forall F1 C1 V1 F2 C2 V2
        (Sem1: CompcertCoreSem (Genv.t F1 V1) C1 (list (ident * globvar V1)))
        (Sem2: CompcertCoreSem (Genv.t F2 V2) C2  (list (ident * globvar V2)))
        P1 P2 ExternIdents,
        In (P1.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents  -> P1.(prog_main) = P2.(prog_main) ->
        CompilerCorrectness.compiler_correctness
             (fun F C V Sem P => (forall x, Genv.init_mem P = Some x <-> initial_mem Sem (Genv.globalenv P) x P.(prog_vars)))
              ExternIdents F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
        forward_simulation (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2).
Proof.
  intros.
  induction X; intros.
  Focus 4. (*trans_case*)
     assert (MM: prog_main P1 = prog_main P2). eapply CompilerCorrectness.cc_main; eauto.
      spec IHX1.  apply H.
      spec IHX1. apply MM.  
      spec IHX2. rewrite MM in H. apply H.
      spec IHX2. eapply CompilerCorrectness.cc_main; eauto.
      clear X1 X2.
      eapply compose_forward_simulation; eauto.
  (*equals_case*)
        rename i into GenvInit1; rename i0 into GenvInit2.
        destruct g as [HypGenv HypVolatile].
        set (fsim_index := Sim_eq.core_data R).
        set (fsim_order := Sim_eq.core_ord R).
        set (fsim_order_wf := Sim_eq.core_ord_wf R).
        set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
                          Sim_eq.match_core R s (fst x) (fst y) /\ snd x = snd y).
        apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2)
                        fsim_index fsim_order fsim_order_wf  fsim_match_states).
             (*initial_state*) simpl. unfold initial_state. intros.
                      destruct s1 as [c1 m1].
                      destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
                      destruct (ePts_ok _ _ H) as [bb [KK1 [KK2 [KK3 KK4]]]].
                      assert (X := @Sim_eq.core_initial _ _ _ _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ KK3 nil).
                      simpl in X.  destruct X. constructor. 
                            destruct H1 as [cc1 [cc2 [ini1 [ini2 mtch]]]].
                          exists x. exists (cc2,m1).
                         split. simpl. exists bb. exists nil. simpl.
                             repeat  split; try constructor. rewrite <- H0. apply KK2.
                                assumption.
                           destruct (Eq_init m1).  apply GenvInit1. apply K5. destruct H1; subst. simpl in *. apply GenvInit2. apply H1. 
                      simpl. hnf. simpl in *. split; trivial. rewrite K3 in KK1. inv KK1.  inv K2. rewrite K4 in ini1.  inv ini1. assumption.
           (*finalstate*)
                 clear GenvInit1 GenvInit2.
                 simpl. unfold final_state. intros. destruct s1 as [c1 m1]. destruct s2 as [c2 m2]. simpl in *.
                      destruct H1. simpl in H3. subst.  simpl in *.
                      apply (Sim_eq.core_halted R _ _ _ _ H1 H2).
                      (*apply (@Sim_eq.core_halted _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ _ H1 H2).*)
           (*diagram*)
                 clear GenvInit1 GenvInit2.
                 simpl. subst fsim_match_states. simpl. intros.
                destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
                      destruct H2. subst.
                 inv H1.
                 (*corestep*)  
                   assert (DD := @Sim_eq.core_diagram _ _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ H6 _ _ H2).
                   destruct DD as [c2' [d' [MC myStep]]].
                  exists d'. exists (c2', m1'); simpl. split; auto.
                    destruct myStep.
                      (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
                      (*case core_step_star*) right.  destruct H1. split; auto. apply corestep_star_star_step; eauto.
               (*external_step*) 
                    destruct (@Sim_eq.core_at_external _ _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ (ef_sig ef) H2 H8) as [AtExt2 TP].
                    assert (DD := @Sim_eq.core_after_external _ _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R).
                    assert (RetTp:= external_call_well_typed _ _ _ _ _ _ _ H9).
                    destruct (DD _ _ _ ret _ _ _ H2 H8 AtExt2 TP RetTp) as [c1'' [c2' [d' [AftExt1 [AftExt2 CM]]]]]; clear DD.
                    rewrite AftExt1 in H10. inv H10.
                    exists d'. exists (c2', m1'). simpl.
                    split; auto. left.  eapply plus_one. eapply step_ext_step. apply AtExt2. Focus 2. apply AftExt2.
                                 apply external_call_symbols_preserved_gen with (ge1:=(Genv.globalenv P1)).
                                        apply HypGenv. (*HERE*)
                                        apply HypVolatile. (*HERE*)
                                        apply H9. 
         (* fsim_symbols_preserved*) simpl. apply HypGenv. (*SAME HERE*) 
   (*extends*) 
        rename i into GenvInit1; rename i0 into GenvInit2.
        destruct g as [HypGenv HypVolatile].
        set (fsim_index := Sim_ext.core_data R).
        set (fsim_order := Sim_ext.core_ord R).
        set (fsim_order_wf := Sim_ext.core_ord_wf R).
        set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
                        Sim_ext.match_state R s (fst x)  (snd x) (fst y) (snd y)).
        apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2)
                        fsim_index fsim_order fsim_order_wf  fsim_match_states).
             (*initial_state*) simpl. unfold initial_state. intros.
                      destruct s1 as [c1 m1]. simpl in *.
                      destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
                       destruct (ePts_ok _ _ H) as [b1 [KK1 [KK2 [Hfound [f1 [f2 [Hf1 Hf2]]]]]]].
                       rewrite KK1 in K3. inv K3. inv K2. clear K1 ePts_ok H.
                       apply GenvInit1 in K5. apply Extends_init in K5. destruct K5 as [m2 [iniMem2 Mextends]].
                      assert (X := @Sim_ext.core_initial _ _ _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ Hfound nil nil m1 m2).
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
                         apply GenvInit2. apply iniMem2. 
           (*finalstate*)
                 clear GenvInit1 GenvInit2.
                 simpl. unfold final_state. intros. destruct s1 as [c1 m1]. destruct s2 as [c2 m2]. simpl in *.
                    destruct (Sim_ext.core_halted R _ _ _ _ _ _ H1 H2) as [r2 [ExtR [SH2 ExtM]]].
                    inv ExtR. simpl in *. assumption.
                    (*apply (@Sim_ext.core_halted _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ _ _ _ H1 H2).*)
           (*diagram*)
                 clear GenvInit1 GenvInit2.
                 simpl. subst fsim_match_states. simpl. intros.
                destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
                 inv H1. 
                 (*corestep*)  
                   assert (DD := @Sim_ext.core_diagram _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ H6 _ _ _ H2).
                   destruct DD as [c2' [m2' [d'  [MC' myStep]]]].
                  exists d'. exists (c2', m2'); simpl. split; auto.
                    destruct myStep.
                      (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
                      (*case core_step_star*) right.  destruct H1. split; auto. apply corestep_star_star_step; eauto.
               (*external_step*) 
                    destruct (@Sim_ext.core_at_external _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ _ _ _ H2 H8) as [args2 [Mextends [lessArgs [TpArgs2 AtExt2]]]].
                   assert (EXT:= @external_call_mem_extends _ _ _ _ _ _ _ _ _  _ _ H9 Mextends (forall_lessdef_val_listless _ _ lessArgs)).
                   destruct EXT as [ret2 [m2' [extCall2 [lessRet [Mextends' MunchOn]]]]].
                   assert (extCall2Genv2 : external_call ef (Genv.globalenv P2) args2 m2 t ret2 m2').
                         eapply external_call_symbols_preserved_gen. 
                             apply HypGenv. (*HERE*) 
                             apply HypVolatile. (*HERE*)
                             apply extCall2.
                         (*An alternative would be to use this proof of extCall2Genv2:
                                    apply (@external_call_symbols_preserved_2 ef F1 V1 F2 V2 (fun v1 =>Errors.Error nil)) with (ge1:=(Genv.globalenv P1)).
                                          apply extCall2.
                                          apply HypGenv. (*HERE*) 
                                          simpl. intros.  assert (ECP:= external_call_spec ef). admit. (*first hyp on globvars*) 
                                          simpl. admit. (*second hyp on globvars*) 
                           *)
                    clear extCall2.
                    assert (DD := @Sim_ext.core_after_external _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ _ _ _ ret ret2 m1' m2' _ H2 H8 AtExt2 lessArgs TpArgs2).
                    destruct DD as [c1'' [c2' [d' [AftExt1 [AftExt2 Match']]]]].
                            eapply external_call_mem_forward; eauto.
                            eapply external_call_mem_forward; eauto.
                            assumption.
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
         (* fsim_symbols_preserved*) simpl. apply HypGenv. (*SAME HERE*)  
   (*inject*)
        rename i into GenvInit1; rename i0 into GenvInit2.
        destruct g as [HypGenv HypVolatile].
        set (fsim_index := Sim_inj.core_data R).
        set (fsim_order := Sim_inj.core_ord R).
        set (fsim_order_wf := Sim_inj.core_ord_wf R).
        set (fsim_match_states s (x:C1 * mem) (y:C2 * mem) :=
                        exists j,  inject_incr jInit j /\  Sim_inj.match_state R s j (fst x)  (snd x) (fst y) (snd y)).
        apply ( @Forward_simulation  (mk_semantics F1 C1 V1 Sem1 P1)  (mk_semantics F2 C2 V2 Sem2 P2)
                        fsim_index fsim_order fsim_order_wf  fsim_match_states).
             (*initial_state*) simpl. unfold initial_state. intros.
                      destruct s1 as [c1 m1]. simpl in *.
                      destruct H1 as [b [args [K1 [ K2 [K3 [K4 K5]]]]]].
                       destruct (ePts_ok _ _ H) as [b1 [b2 [KK1 [KK2 [Hjb [Hfound [f1 [f2 [Hf1 Hf2]]]]]]]]].
                      rewrite KK1 in K3. inv K3. inv K2. clear K1.
                       destruct (Inj_init m1) as [m2 [initMem2 Inj]]; clear Inj_init . apply GenvInit1. apply K5.
                        assert (X := @Sim_inj.core_initial _ _ _ _ _ _ _ Sem1 Sem2  (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints R _ _ _ Hfound nil _ _ _ nil _ K4 Inj).
                        (*would need relationship between entrypoints and externidents assert (ZZ: (forall (w1 w2 : val) (sigg : signature),  In (w1,w2, sigg) entrypoints -> val_inject j w1 w2)).
                             intros.  unfold CompilerCorrectness.entries_inject_ok in ext_ok. apply ext_ok in H1.*)
                        destruct X as [d' [c2 [iniCore2 Match]]].
                          constructor.
                          constructor. 
                          exists d'. exists (c2,m2). simpl in *.
                          split; auto. exists b2. exists nil.
                             repeat  split; try constructor.
                             rewrite <- H0. apply KK2.
                             assumption.
                             apply GenvInit2. apply initMem2.
                         exists jInit. split; auto. 
           (*finalstate*)
                 clear GenvInit1 GenvInit2.
                 simpl. unfold final_state. intros. destruct s1 as [c1 m1]. destruct s2 as [c2 m2]. simpl in *.
                      destruct H1 as [j [InjJ MCJ]]; simpl in *.
                      destruct (Sim_inj.core_halted R _ _ _ _ _ _ _ MCJ H2) as [v2 [InjV [SH2 InjM]]].
                      inv InjV. assumption.
           (*diagram*) 
                 clear GenvInit1 GenvInit2.
                 simpl. subst fsim_match_states. simpl. intros.
                destruct s1 as [c1 m1]. destruct s2 as [c2 m2].  destruct s1' as [c1' m1'].  simpl in *.
                destruct H2 as [j [InjJ MCJ]].
                 inv H1. 
                 (*corestep*)  
                   assert (DD := @Sim_inj.core_diagram _ _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ H5 _ _ _ _ MCJ).
                   destruct DD as [c2' [m2' [d' [j' [InjJ' [Sep [MC' myStep]]]]]]].
                  exists d'. exists (c2', m2'); simpl. split; auto.
                    destruct myStep.
                      (*case corestep_plus*) left. eapply corestep_plus_plus_step; eauto.
                      (*case core_step_star*) right.  destruct H1. split; auto. apply corestep_star_star_step; eauto.
                   exists j'; split; auto. eapply inject_incr_trans. apply InjJ. apply InjJ'.                    
               (*external_step*) 
                    destruct (@Sim_inj.core_at_external _ _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) entrypoints R _ _ _ _ _ _ _ _ _ MCJ H7) 
                               as[INJ [jPG [args2 [LD [TP AtExt2]]]]].
                    (*LENB: HERE's where we need that j preserves globals.
                            assert (HH: meminj_preserves_globals (Genv.globalenv P1) j).
                       eapply meminj_preserves_globals_inject_incr. apply preserves_globals. apply InjJ.*)
                           (* it seems inject doesn't preserve globals!
                             split; intros. destruct HGenv1. apply (H3 _ (id, CompilerCorrectness.extern_func (ef_sig ef))) in H8.  apply ext_ok in H8.
                                    destruct H8 as [b1 [b2 [Hb1 [Hb2 [Hb1b2 _]]]]]. rewrite Hb1 in H1. inv H1.  apply InjJ. assumption.*)
                    apply forall_inject_val_list_inject in LD.
                    assert (ZZ:= @external_call_mem_inject ef  _ _ (Genv.globalenv P1) _ _ _ _ _ j _ _ jPG H8 INJ LD).
                    destruct ZZ as [j'  [ret2 [m2' [extCall2 [RetInj [MInj2 [Munch1 [Munch2 [InjJ' Sep']]]]]]]]].
                    assert (extCall2Genv2 : external_call ef (Genv.globalenv P2) args2 m2 t ret2 m2'). 
                         eapply external_call_symbols_preserved_gen. 
                             apply HypGenv. (*HERE*) 
                             apply HypVolatile. (*HERE*)
                             apply extCall2.
                          (*An alternative would be the following proof of extCall2Genv2:
                                    apply (@external_call_symbols_preserved_2 ef F1 V1 F2 V2 (fun v1 =>Errors.Error nil)) with (ge1:=(Genv.globalenv P1)).
                                          apply extCall2.
                                          admit. (*symmetric hypothesis on Genv.findSymbol*) 
                                          simpl. admit. (*first hyp on globvars*) 
                                          simpl. admit. (*second hyp on globvars*) *)
                    clear extCall2.
                    assert (DD := @Sim_inj.core_after_external _ _ _ _ _ _ _ Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) 
                                               entrypoints R i j).
                    assert (RetTp:= external_call_well_typed _ _ _ _ _ _ _ H8).
                    destruct (DD j' _ _ _ _ _ _ _ _ _ _ (ef_sig ef) INJ MCJ H7 jPG InjJ' Sep' MInj2 RetInj) as [d' [c1'' [c2' [AftExt1 [AftExt2 Match2]]]]]; clear DD.
                         eapply external_call_mem_forward; eauto.
                         apply Munch1.
                         eapply external_call_mem_forward; eauto.
                         apply Munch2.
                         eapply external_call_well_typed. apply extCall2Genv2. 
                      rewrite AftExt1 in H9. inv H9.
                         exists d'. exists (c2', m2').
                         split. left. apply plus_one. eapply  step_ext_step. apply AtExt2. apply extCall2Genv2. apply AftExt2. 
                         exists j'; simpl.  split;eauto. eapply inject_incr_trans. apply InjJ. apply InjJ'.
         (* fsim_symbols_preserved*) simpl. apply HypGenv. (*SAME HERE*)
Qed.
(*
1. The need for the axiom GenvHyp in all cases (or alternatively the addition of axioms  HypGenv and HypVolatile, 
     at the beginning of all cases): 
These are needed in order to apply external_call_symbols_preserved_gen, in order to establish external_call 
ef (GEnv P2) vargs m1 t vres m2, 
As mentioned in the file, an alternative proof of this fact using external_call_symbols_preserved_2 would require 
a slightly different axiom on globvars, eliminating the need for HypVolatile.
Additionally, HypGenv is also explicitly required in order to discharge Xavier's condition  fsim_symbols_preserved.

2. The need to establish a "meminj_preserves_globals" property in case inject-diamond-externalStep.
I temporarily added the condition meminj_preserves_globals jInit in cc_inj, with the idea
  that we would thread it through the execution. But meminj_preserves_globals is formally 
  not preserved by inj_incr. But maybe the 3rd clause in meminj_preserves_globals is
  stronger than what's needed to prove the CompCert phases?

An alternative (maybe this is needed in any case) would be to have at_external
   (or maybe external_call ef ge vargs m1 t vres m2 in general)  
  imply that (f,d) in ExternIdent, so that we can apply entries_ok or entries_inject_ok.
  But: some externals_funstions ("builtins") dont have idents - so maybe ExternIdents should be
        of a different type, not take idents? Or maybe should differentiate in external_description
         between builtins and nonbuiltins?

It seems given the strong condition imposed by meminj_preserves_global, our choice to
differentiate between entries_ok and entries_inject_ok is too fine for current CompCert.
Maybe we soulh use entries_ok even in inject-case (at least for the sake of demonstrating 
that our approach works)?

3. Do we still need the allowed_modifications stuff??
 *)

End CompilerCorrectness_implies_forward_simulation.
(*
meminj_preserves_globals:
  - defined in Events (so quite at a high level)
  - established ONLY in cfrontend/Cminorgenproof (no other compiler phase establishes it!) via the
    following lemma:
      Remark inj_preserves_globals: forall f hi, match_globalenvs f hi -> meminj_preserves_globals ge f.
*)