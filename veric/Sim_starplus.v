Add LoadPath "..".
Require Import veric.base.
Require Import compcert.Events.
Require Import veric.sim. 

(*Proofs that the individual cases of sim (sim_eq, sim_ext and sim_inj are closed under
   star and plus. Then (presumably) lift this to compilercorrectness.*)

(*SEVERAL HOLES IN THIS FILE!!!*)

Section Sim_EQ_SIMU_DIAGRAMS.

  Context {G1 C1 D1 G2 C2 D2:Type}
          {Sem1 : CompcertCoreSem G1 C1 D1}
          {Sem2 : CompcertCoreSem G2 C2 D2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Variable core_data:Type.
  Variable order: core_data -> core_data -> Prop.
  Hypothesis order_wf: well_founded order.

  Variable match_cores: core_data -> C1 -> C2 -> Prop.
  Hypothesis match_initial_cores: 
        forall v1 v2 sig, In (v1,v2,sig) entry_points ->
        forall vals,  Forall2 (Val.has_type) vals (sig_args sig) ->
       exists cd : core_data, exists c1 : C1, exists c2 : C2,
                make_initial_core Sem1 ge1 v1 vals = Some c1 /\
                make_initial_core Sem2 ge2 v2 vals = Some c2 /\ match_cores cd c1 c2.
(*Smallstep/old version of this file had
  Hypothesis match_initial_cores: 
        forall v1 v2 sig, In (v1,v2,sig) entry_points ->
        forall vals,  Forall2 (Val.has_type) vals (sig_args sig) ->
        forall c1, make_initial_core Sem1 ge1 v1 vals = Some c1 ->
                   exists c2, exists d, make_initial_core Sem2 ge2 v2 vals = Some c2 /\
                                                   match_cores d c1 c2.
But the core_initial axiom in the record Sim_eq.Forward_simulation_equals currently has an /\
  in place of the implication -- maybe that should be changed?
*)

  Hypothesis eq_safely_halted:
      forall (cd : core_data) (c1 : C1) (c2 : C2) (v : int),
      match_cores cd c1 c2 ->
      safely_halted Sem1 ge1 c1 = Some v -> safely_halted Sem2 ge2 c2 = Some v.

  Hypothesis eq_at_external: 
         forall (d : core_data) (st1 : C1) (st2 : C2) (e : external_function) (args : list val) sig,
         match_cores d st1 st2 ->
         at_external Sem1 st1 = Some (e, sig, args) ->
         at_external Sem2 st2 = Some (e, sig, args) /\
         Forall2 Val.has_type args (sig_args sig).

  Hypothesis eq_after_external: forall (d : core_data) (st1 : C1) (st2 : C2) (ret : val)
                                                                 (e : external_function) (args : list val) sig,
                      match_cores d st1 st2 ->
                      at_external Sem1 st1 = Some (e, sig, args) ->
                      at_external Sem2 st2 = Some (e, sig, args) ->
                      Forall2 Val.has_type args (sig_args sig) ->
                      Val.has_type ret (proj_sig_res sig) ->
                      exists st1' : C1, exists st2' : C2, exists d' : core_data,
                              after_external Sem1 (Some ret) st1 = Some st1' /\
                              after_external Sem2 (Some ret) st2 = Some st2' /\ match_cores d' st1' st2'.
(*
Section SIMULATION_STAR_WF.
  Hypothesis eq_simulation:
     forall c1 m c1' m',  corestep Sem1 ge1 c1 m c1' m' ->
     forall d c2, match_cores d c1 c2 ->
      exists c2', exists d', match_cores d' c1' c2' /\
                  (corestep_plus Sem2 ge2  c2 m c2' m' \/ (corestep_star Sem2 ge2 c2 m c2' m' /\ order d' d)).

Lemma  eq_simulation_star_wf: Sim_eq.Forward_simulation_equals _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply Sim_eq.Build_Forward_simulation_equals with
        (core_ord := order)
        (match_core := match_cores). (*fun d c1 c2 => idx = s1 /\ match_cores c1 c2);*)
   apply order_wf.
   apply eq_simulation.
   apply match_initial_cores.
   apply eq_safely_halted.
   apply eq_at_external.
   apply eq_after_external.
Qed.
End SIMULATION_STAR_WF.

Section SIMULATION_STAR.
  Variable measure: C1 -> nat.
  
  Hypothesis eq_star_simulation:
    forall c1 m c1' m', corestep Sem1 ge1 c1 m c1' m'  -> 
    (measure c1' < measure c1 /\
    forall d c2, match_cores d c1 c2 ->
    (exists c2', exists d', corestep_plus Sem2 ge2 c2 m c2' m' /\ match_cores d' c1' c2' /\ order d' d)
   \/ (measure c1' < measure c1 /\ m'=m /\ match_cores d c1' c2))%nat.

  Definition star_data : Type := (core_data * C1)%type.
  Definition star_ord:= lex_ord order (ltof _ measure). 

  Definition match_cores_star (cd:star_data) (c1:  C1) (c2: C2): Prop :=
       match cd with (d,c) => match_cores d c1 c2 \/exists d',  order d' d /\ match_cores d' c c2 (* lt (measure c1) (measure c) /\*)
       end.
(*
  Definition match_cores_star (cd:star_data) (c1:  C1) (c2: C2): Prop :=
       match cd with (d,c) => match_cores d c1 c2 /\ lt (measure c1) (measure c) 
       end.
*)
Lemma  eq_simulation_star: Sim_eq.Forward_simulation_equals _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply Sim_eq.Build_Forward_simulation_equals with (core_ord:= star_ord)(match_core:=match_cores_star).
      eapply wf_lex_ord. apply order_wf. apply (well_founded_ltof _ measure).
      clear match_initial_cores eq_safely_halted eq_at_external eq_after_external.
         unfold match_cores_star. intros. destruct d as [d c].
         rename st1 into c1. rename st1' into c1'. rename st2 into c2.
        destruct  (eq_star_simulation _ _ _ _ H) as [MM LLL]; clear eq_star_simulation .
        destruct H0.
        (*1*) specialize (LLL _ _ H0).
                              destruct LLL as [X | X]. (*; clear LLL. eq_star_simulation.*)
                                  (*case 1*) destruct X as [c2' [d'' [CS [MC ORD]]]].
                                                    exists c2'. exists (d'', c). split. left. assumption.  left; assumption. (*transitivity*)  (*left; trivial. left; trivial.*)                                                   
                                 (*case 2*) destruct X as [Measure [M MTCH]]. subst.
                                                    exists c2.  unfold star_ord.  exists (d, c1). split. left; trivial. 
                                                                      (*exists d.  split; trivial. left; assumption.*) (*left; assumption. *)(* right; auto*)
                                                             right. split. exists O. reflexivity.
                                                                 apply lex_ord_right. apply H1.  (*unfold ltof. admit.*)  (*HERE's A HOLE!!*)
            (*destruct H0. admit.*)
    clear eq_star_simulation eq_after_external eq_at_external eq_safely_halted.
        intros. specialize (match_initial_cores _ _ _ H _ H0).
                   destruct match_initial_cores as [d [c1 [c2 [Ini1 [Ini2 MC]]]]].
                   exists (d,c1). exists c1. exists c2. split; trivial. split; trivial.
                   simpl. left; trivial.
    clear eq_star_simulation eq_after_external eq_at_external match_initial_cores.
        intros. destruct cd as [d c].
                   destruct H. eapply (eq_safely_halted _ _ _ _ H H0).
                   destruct H.  admit. (*HOLE*)
    clear eq_after_external match_initial_cores eq_star_simulation eq_safely_halted.
        intros. destruct d as [d c].
                   destruct H. 
                       eapply eq_at_external. apply H. apply H0.
                   destruct H.  
                       eapply eq_at_external. apply H1. admit. (*HOLE*)
       (*afterexternal*)
           admit.
Qed.
End SIMULATION_STAR.
*)

Section EQ_SIMULATION_STAR.
  Variable measure: C1 -> nat. 
  Definition star_data : Type := (core_data * C1)%type.
  Definition star_ord:= lex_ord order (ltof _ measure).
 
  Definition match_cores_star (cd:star_data) (c1:  C1) (c2: C2): Prop :=
       match cd with (d,c) => match_cores d c1 c2 \/ (lt (measure c) (measure c1) /\ match_cores d c c2)
       end.

  Hypothesis eq_star_halted_Zero:  forall c1 v, safely_halted Sem1 ge1 c1 = Some v -> measure c1 = O.
  Hypothesis eq_star_atExt_Zero:  forall c1 v, at_external Sem1 c1 = Some v -> measure c1 = O.

(*  Hypothesis eq_star_simulation:
     forall c1 m c1' m',  corestep Sem1 ge1 c1 m c1' m' ->
     forall d c2, match_cores d c1 c2 ->
      exists c2', exists d', (corestep_plus Sem2 ge2 c2 m c2' m' /\ match_cores_star (d',c1') c1' c2' /\ order d' d) \/
                                       (corestep_star Sem2 ge2 c2 m c2' m' /\ measure c1' < measure c1 /\ m'=m /\ match_cores d c1' c2)%nat.
*)(*
  Hypothesis  eq_star_simulation: forall c1 m c1' m' (CS: corestep Sem1 ge1 c1 m c1' m')
                       dc c2 (MCS:match_cores_star dc c1 c2),
                      exists c2', 
                            (exists dc', match_cores_star dc' c1' c2' /\ corestep_plus Sem2 ge2 c2 m c2' m') \/
                            (exists d, exists c, dc=(d,c) /\ measure c1 < measure c1' /\ 
                                     match_cores_star (d,c) c1' c2)%nat.*)
 Hypothesis eq_star_sim_diag:  forall c1 m c1' m' (CS: corestep Sem1 ge1 c1 m c1' m')
                       dc c2 (MCS:match_cores_star dc c1 c2),
                      exists c2', exists dc',
    match_cores_star dc' c1' c2' /\
    (corestep_plus Sem2 ge2 c2 m c2' m' \/
     corestep_star Sem2 ge2 c2 m c2' m' /\ star_ord dc' dc).

Lemma  eq_simulation_star: Sim_eq.Forward_simulation_equals _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply Sim_eq.Build_Forward_simulation_equals with (core_ord:= star_ord)(match_core:=match_cores_star).
      eapply wf_lex_ord. apply order_wf.  apply (well_founded_ltof _ measure).
   apply eq_star_sim_diag.
   intros. clear  eq_safely_halted eq_at_external eq_after_external eq_star_sim_diag.
          specialize (match_initial_cores _ _ _ H _ H0).
          destruct match_initial_cores as [d [c1 [c2 [Ini1 [Ini2 Mtch]]]]]; clear match_initial_cores.
          exists (d,c1). exists c1. exists c2. split; trivial.  split; trivial.  left.  trivial.
   intros. clear  eq_at_external eq_after_external eq_star_sim_diag match_initial_cores eq_star_sim_diag.
        assert (X:= eq_star_halted_Zero _ _ H0).
         destruct cd as [d c]. destruct H. eapply eq_safely_halted . apply H. apply H0.
         destruct H. rewrite X in H. inv H.
   intros. clear eq_star_sim_diag eq_safely_halted  eq_after_external match_initial_cores eq_star_halted_Zero.
           assert (X:= eq_star_atExt_Zero _ _ H0).
        destruct d as [d c]. destruct H.
          eapply eq_at_external ; eauto. 
        destruct H. rewrite X in H. inv H.
   intros. clear eq_star_sim_diag eq_safely_halted  match_initial_cores eq_star_halted_Zero.
           destruct d as [d c]. 
           destruct H. specialize (eq_after_external _ _ _ _ _ _ _ H H0 H1 H2 H3).
                destruct eq_after_external  as [c1' [c2' [d' [AftExt1 [AftExt2 MC]]]]].
                exists c1'. exists c2'. exists (d',c). split; trivial. split; trivial. left. assumption.
          destruct H. rewrite (eq_star_atExt_Zero _ _ H0) in H. inv H.
Qed.
End EQ_SIMULATION_STAR.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section EQ_SIMULATION_PLUS.
(*
Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Plus L2 s2 t s2' /\ match_states s1' s2'.
*)
 Hypothesis eq_plus_sim_diag:  forall c1 m c1' m' (CS: corestep Sem1 ge1 c1 m c1' m')
                       dc c2 (MCS:match_cores_star (fun _ => O) dc c1 c2),
                      exists c2', exists dc',
    match_cores_star (fun _ => O) dc' c1' c2' /\ corestep_plus Sem2 ge2 c2 m c2' m'.

Lemma  eq_simulation_plus: Sim_eq.Forward_simulation_equals _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  apply eq_simulation_star with (measure := fun _ => O).
      intros. trivial.
      intros. trivial.
      intros.
               clear eq_after_external eq_at_external eq_safely_halted match_initial_cores.
               destruct (eq_plus_sim_diag _ _ _ _ CS _ _ MCS) as [c2' [dc' [MCS' CSP]]].
               exists c2'. exists dc'. split. assumption. left. trivial.
Qed.

End EQ_SIMULATION_PLUS.

(*
 eq_safely_halted; eassumption.
        destruct H. 
   apply eq_safely_halted.
   apply eq_at_external.
   apply eq_after_external.
   intros. clear match_initial_cores  eq_safely_halted eq_at_external eq_after_external.
        destruct d as [d c]. inv H0. 
        specialize (eq_star_simulation _ _ _ _ H _ _ H1). 
         destruct eq_star_simulation  as [c2' [d' [ [StepPlus [MtchStar Ord]]| [StepStar [MM [X Mtch]]]]]]; clear eq_star_simulation.
              exists c2'. exists (d',st1'). split; trivial. left; assumption.
          subst. exists c2'. exists (d,

   intros. clear match_initial_cores  eq_safely_halted eq_at_external eq_after_external.
        specialize (eq_star_simulation _ _ _ _ H _ _ H0). 
        destruct d as [d c]. inv H0.
         destruct  eq_star_simulation as [c2' [X | X]]; clear eq_star_simulation.
             destruct X as [[d' c'] [ MtchStar SPlus]].
             exists c2'. exists (d',c'); split; trivial. left; trivial.
           destruct X as [d' [c' [X [StepStar [MM Mtch]]]]]. inv X.
              exists c2'.  exists (d',c'). split; trivial. left; assumption.
          subst. exists c2'. exists (d,
   apply eq_star_simulation.
   intros. clear eq_star_simulation  eq_safely_halted eq_at_external eq_after_external.
   intros. clear eq_star_simulation  eq_at_external eq_after_external match_initial_cores.
        destruct cd as [d c]. destruct H.
           eapply eq_safely_halted; eassumption.
        destruct H. 
   apply eq_safely_halted.
   apply eq_at_external.
   apply eq_after_external.
   intros. clear match_initial_cores  eq_safely_halted eq_at_external eq_after_external.
        destruct d as [d c]. inv H0. 
        specialize (eq_star_simulation _ _ _ _ H _ _ H1). 
         destruct eq_star_simulation  as [c2' [d' [ [StepPlus [MtchStar Ord]]| [StepStar [MM [X Mtch]]]]]]; clear eq_star_simulation.
              exists c2'. exists (d',st1'). split; trivial. left; assumption.
          subst. exists c2'. exists (d,
  
   apply eq_simulation.
   apply match_initial_cores.
   apply eq_safely_halted.
   apply eq_at_external.
   apply eq_after_external.
Qed.
 
  Hypothesis eq_simulation:
     forall c1 m c1' m',  corestep Sem1 ge1 c1 m c1' m' ->
     forall d c2, match_cores d c1 c2 ->
      exists c2', exists d', match_cores d' c1' c2' /\
                  (corestep_plus Sem2 ge2  c2 m c2' m' \/ (corestep_star Sem2 ge2 c2 m c2' m' /\ order d' d)).

Lemma  eq_simulation_star_wf: Sim_eq.Forward_simulation_equals _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply Sim_eq.Build_Forward_simulation_equals with
        (core_ord := order)
        (match_core := match_cores). (*fun d c1 c2 => idx = s1 /\ match_cores c1 c2);*)
   apply order_wf.
   apply eq_simulation.
   apply match_initial_cores.
   apply eq_safely_halted.
   apply eq_at_external.
   apply eq_after_external.
Qed.
End SIMULATION_STAR_WF.
(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)
Section SIMULATION_PLUS.

Hypothesis eq_plus_simulation:
  forall c1 m c1' m', corestep Sem1 ge1 c1 m c1' m'  ->
  forall d c2, match_cores d c1 c2 ->
  (exists c2', exists d', corestep_plus Sem2 ge2 c2 m c2' m' /\ match_cores d' c1' c2'  /\ order d' d).

Lemma eq_simulation_plus: Sim_eq.Forward_simulation_equals _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  apply eq_simulation_star with (measure := fun _ => O).
  intros. left. clear eq_after_external eq_at_external  eq_safely_halted match_initial_cores.
       apply (eq_plus_simulation _ _ _ _ H _ _ H0).
Qed.

End SIMULATION_PLUS.
*)

End Sim_EQ_SIMU_DIAGRAMS.

Section Sim_EXT_SIMU_DIAGRAMS.

  Context {G1 C1 D1 G2 C2 D2:Type}
          {Sem1 : CompcertCoreSem G1 C1 D1}
          {Sem2 : CompcertCoreSem G2 C2 D2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Variable core_data:Type.
  Variable order: core_data -> core_data -> Prop.
  Hypothesis order_wf: well_founded order.

  Variable match_state: core_data -> C1 -> mem -> C2 -> mem -> Prop.
  Hypothesis match_initial_cores: forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          Forall2 Val.lessdef vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.extends m1 m2 ->
          exists cd, exists c1, exists c2,
            make_initial_core Sem1 ge1 v1 vals = Some c1 /\
            make_initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_state cd c1 m1 c2 m2.

  Hypothesis ext_safely_halted:
      forall cd st1 m1 st2 m2 (v:int),
        match_state cd st1 m1 st2 m2 ->
        safely_halted Sem1 ge1 st1 = Some v ->
          safely_halted Sem2 ge2 st2 = Some v /\
          Mem.extends m1 m2.

  Hypothesis ext_at_external: 
      forall cd st1 m1 st2 m2 e vals1 sig,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        exists vals2,
          Mem.extends m1 m2 /\
          Forall2 Val.lessdef vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args sig) /\
          at_external Sem2 st2 = Some (e,vals2).

  Hypothesis ext_after_external:
      forall cd st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2' sig,
        match_state cd st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        at_external Sem2 st2 = Some (e,vals2) ->

        Forall2 Val.lessdef vals1 vals2 ->
        Forall2 (Val.has_type) vals2 (sig_args sig) ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        mem_unchanged_on (loc_out_of_bounds m1) m2 m2' -> (*ie spill-locations didn't change*)
        Val.lessdef ret1 ret2 ->
        Mem.extends m1' m2' ->

        Val.has_type ret2 (proj_sig_res sig) ->

        exists st1', exists st2', exists cd',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' st1' m1' st2' m2'. 

Section EXT_SIMULATION_STAR.
  Variable measure: C1 -> nat. 
  Definition ext_star_data : Type := (core_data * C1)%type.
  Definition ext_star_ord:= lex_ord order (ltof _ measure).
 
  Definition ext_match_states_star (cd:ext_star_data) (c1:  C1) m1 (c2: C2) m2 : Prop :=
       match cd with (d,c) => match_state d c1 m1 c2 m2 \/ (lt (measure c) (measure c1) /\ match_state d c m1 c2 m2)
       end.

  Hypothesis ext_star_halted_Zero:  forall c1 v, safely_halted Sem1 ge1 c1 = Some v -> measure c1 = O.
  Hypothesis ext_star_atExt_Zero:  forall c1 v, at_external Sem1 c1 = Some v -> measure c1 = O.

 Hypothesis ext_star_sim_diag:  forall c1 m1 c1' m1' (CS: corestep Sem1 ge1 c1 m1 c1' m1')
                       dc c2 m2 (MCS:ext_match_states_star dc c1 m1 c2 m2),
                      exists c2', exists m2', exists dc',
    ext_match_states_star dc' c1' m1' c2' m2' /\
    (corestep_plus Sem2 ge2 c2 m2 c2' m2' \/
     corestep_star Sem2 ge2 c2 m2 c2' m2' /\ ext_star_ord dc' dc).

Lemma  ext_simulation_star: Sim_ext.Forward_simulation_extends _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply Sim_ext.Build_Forward_simulation_extends with (core_ord:= ext_star_ord). (*(match_state:=ext_match_states_star).*)
      eapply wf_lex_ord. apply order_wf.  apply (well_founded_ltof _ measure).
   apply ext_star_sim_diag.
   intros. clear  ext_safely_halted ext_at_external ext_after_external ext_star_sim_diag.
          specialize (match_initial_cores _ _ _ H _ _ _ _ H0 H1 H2).
          destruct match_initial_cores as [d [c1 [c2 [Ini1 [Ini2 Mtch]]]]]; clear match_initial_cores.
          exists (d,c1). exists c1. exists c2. split; trivial.  split; trivial.  left.  trivial.
   intros. clear  ext_at_external ext_after_external ext_star_sim_diag match_initial_cores ext_star_sim_diag.
        assert (X:= ext_star_halted_Zero _ _ H0).
         destruct cd as [d c]. destruct H. eapply ext_safely_halted . apply H. apply H0.
         destruct H. rewrite X in H. inv H.
   intros. clear ext_star_sim_diag ext_safely_halted  ext_after_external match_initial_cores ext_star_halted_Zero.
           assert (X:= ext_star_atExt_Zero _ _ H0).
        destruct cd as [d c]. destruct H.
          eapply ext_at_external ; eauto. 
        destruct H. rewrite X in H. inv H.
   intros. clear ext_star_sim_diag ext_safely_halted  match_initial_cores ext_star_halted_Zero ext_at_external.
           destruct cd as [d c]. 
           destruct H. specialize (ext_after_external _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9).
                destruct ext_after_external  as [c1' [c2' [d' [AftExt1 [AftExt2 MC]]]]].
                exists c1'. exists c2'. exists (d',c). split; trivial. split; trivial. left. assumption.
          destruct H. rewrite (ext_star_atExt_Zero _ _ H0) in H. inv H.
Qed.
End EXT_SIMULATION_STAR.

Section EXT_SIMULATION_PLUS.
 Hypothesis ext_plus_sim_diag:  forall c1 m1 c1' m1' (CS: corestep Sem1 ge1 c1 m1 c1' m1')
                       dc c2 m2 (MCS:ext_match_states_star (fun _ => O) dc c1 m1 c2 m2),
                      exists c2', exists m2', exists dc',
    ext_match_states_star (fun _ => O) dc' c1' m1' c2' m2' /\ corestep_plus Sem2 ge2 c2 m2 c2' m2'.

Lemma  ext_simulation_plus: Sim_ext.Forward_simulation_extends _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  apply ext_simulation_star with (measure := fun _ => O).
      intros. trivial.
      intros. trivial.
      intros.
               clear ext_after_external ext_at_external ext_safely_halted match_initial_cores.
               destruct (ext_plus_sim_diag _ _ _ _ CS _ _ _ MCS) as [c2' [m2' [dc' [MCS' CSP]]]].
               exists c2'. exists m2'. exists dc'. split. assumption. left. trivial.
Qed.

End EXT_SIMULATION_PLUS.

End Sim_EXT_SIMU_DIAGRAMS.

Section Sim_INJ_SIMU_DIAGRAMS.

  Context {F1 V1 C1 D1 G2 C2 D2:Type}
          {Sem1 : CompcertCoreSem (Genv.t F1 V1)  C1 D1}
          {Sem2 : CompcertCoreSem G2 C2 D2}

          {ge1: Genv.t F1 V1} 
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Variable core_data:Type.
  Variable order: core_data -> core_data -> Prop.
  Hypothesis order_wf: well_founded order.

  Variable match_state: core_data -> meminj ->  C1 -> mem -> C2 -> mem -> Prop.
  Hypothesis match_initial_cores: forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 j vals2 m2,
          make_initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject j m1 m2 -> 
          (*Is this line needed?? (forall w1 w2 sigg,  In (w1,w2,sigg) entry_points -> val_inject j w1 w2) ->*)
           Forall2 (val_inject j) vals1 vals2 ->

          Forall2 (Val.has_type) vals2 (sig_args sig) ->
          exists cd, exists c2, (*exists vals2, exists m2, *)
            make_initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            match_state cd j c1 m1 c2 m2. 

  Hypothesis inj_safely_halted:forall cd j c1 m1 c2 m2 (v1:int),
      match_state cd j c1 m1 c2 m2 ->
      safely_halted Sem1 ge1 c1 = Some v1 ->
        (safely_halted Sem2 ge2 c2 = Some v1 /\
         Mem.inject j m1 m2).

  Hypothesis inj_at_external: 
      forall cd j st1 m1 st2 m2 e vals1 sig,
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
        ( Mem.inject j m1 m2 /\
          meminj_preserves_globals ge1 j /\ (*LENB: also added meminj_preserves_global HERE*)
          exists vals2, Forall2 (val_inject j) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args sig) /\
          at_external Sem2 st2 = Some (e,vals2)).

  Hypothesis inj_after_external:
      forall cd j j' st1 st2 m1 e vals1 (*vals2*) ret1 m1' m2 m2' ret2 sig,
        Mem.inject j m1 m2->
        match_state cd j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,vals1) ->
(*     at_external Sem2 st2 = Some (e,vals2) ->
        Forall2 (val_inject j) vals1 vals2 ->*)

(* LENB: we may want to add meminj_preserves_globals ge1 j as another asumption here,
      to get rid of meminj_preserved_globals_inject_incr below. But this would require spaeicaliing G1 to Genv.t....
     Maybe we can specialize G1 and G2 of CompCertCoreSem's to Genv F1 V1/Genv F2 V2, but
    not specialize CoreSem's?*)
        meminj_preserves_globals ge1 j -> 

        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject j' ret1 ret2 ->

         mem_forward m1 m1'  -> 
         mem_unchanged_on (loc_unmapped j) m1 m1' ->
         mem_forward m2 m2' -> 
         mem_unchanged_on (loc_out_of_reach j m1) m2 m2' ->
         Val.has_type ret2 (proj_sig_res sig) ->

        exists cd', exists st1', exists st2',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          match_state cd' j' st1' m1' st2' m2'. 

Section INJ_SIMULATION_STAR.
  Variable measure: C1 -> nat. 
  Definition inj_star_data : Type := (core_data * C1)%type.
  Definition inj_star_ord:= lex_ord order (ltof _ measure).
 
  Definition inj_match_states_star (cd:inj_star_data) j (c1:  C1) m1 (c2: C2) m2 : Prop :=
       match cd with (d,c) => match_state d j c1 m1 c2 m2 \/ (lt (measure c) (measure c1) /\ match_state d j c m1 c2 m2)
       end.

  Hypothesis inj_star_halted_Zero:  forall c1 v, safely_halted Sem1 ge1 c1 = Some v -> measure c1 = O.
  Hypothesis inj_star_atExt_Zero:  forall c1 v, at_external Sem1 c1 = Some v -> measure c1 = O.

 Hypothesis inj_star_sim_diag:  forall c1 m1 c1' m1' (CS: corestep Sem1 ge1 c1 m1 c1' m1')
                       dc c2 j m2 (MCS:inj_match_states_star dc j c1 m1 c2 m2),
                      exists c2', exists m2', exists dc', exists j',
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          inj_match_states_star dc' j' c1' m1' c2' m2' /\
          ((corestep_plus Sem2 ge2 c2 m2 c2' m2') \/
            corestep_star Sem2 ge2 c2 m2 c2' m2' /\
            inj_star_ord dc' dc).

Lemma  inj_simulation_star: Sim_inj.Forward_simulation_inject _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply Sim_inj.Build_Forward_simulation_inject with (core_ord:= inj_star_ord). (*(match_state:=inj_match_states_star).*)
      eapply wf_lex_ord. apply order_wf.  apply (well_founded_ltof _ measure).
   apply inj_star_sim_diag.
   intros. clear  inj_safely_halted inj_at_external inj_after_external inj_star_sim_diag.
          specialize (match_initial_cores _ _ _ H _ _ _ _ _ _ H0 H1 H2 H3).
          destruct match_initial_cores as [d [c2 [Ini2 Mtch]]]; clear match_initial_cores.
          exists (d,c1). exists c2. split; trivial.  left.  trivial.
   intros. clear  inj_at_external inj_after_external inj_star_sim_diag match_initial_cores inj_star_sim_diag.
        assert (X:= inj_star_halted_Zero _ _ H0).
         destruct cd as [d c]. destruct H. eapply inj_safely_halted . apply H. apply H0.
         destruct H. rewrite X in H. inv H.
   intros. clear inj_star_sim_diag inj_safely_halted  inj_after_external match_initial_cores inj_star_halted_Zero.
           assert (X:= inj_star_atExt_Zero _ _ H0).
        destruct cd as [d c]. destruct H.
          eapply inj_at_external ; eauto. 
        destruct H. rewrite X in H. inv H.
   intros. clear inj_star_sim_diag inj_safely_halted  match_initial_cores inj_star_halted_Zero inj_at_external.
           destruct cd as [d c]. 
           destruct H0. specialize (inj_after_external _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11).
                destruct inj_after_external  as [d' [c1' [c2' [AftExt1 [AftExt2 MC]]]]].
                exists (d',c).  exists c1'. exists c2'. split; trivial. split; trivial. left. assumption.
          destruct H0. rewrite (inj_star_atExt_Zero _ _ H1) in H0. inv H0.
Qed.
End INJ_SIMULATION_STAR.

Section INJ_SIMULATION_PLUS.
 Hypothesis inj_plus_sim_diag:   forall c1 m1 c1' m1' (CS: corestep Sem1 ge1 c1 m1 c1' m1')
                       dc c2 j m2 (MCS:inj_match_states_star (fun _ => O) dc j c1 m1 c2 m2),
        exists c2', exists m2', exists dc', exists j',
          inject_incr j j' /\
          inject_separated j j' m1 m2 /\
          inj_match_states_star (fun _ => O) dc' j' c1' m1' c2' m2' /\
          corestep_plus Sem2 ge2 c2 m2 c2' m2'.

Lemma  inj_simulation_plus: Sim_inj.Forward_simulation_inject _ _ Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  apply inj_simulation_star with (measure := fun _ => O).
      intros. trivial.
      intros. trivial.
      intros.
               clear inj_after_external inj_at_external inj_safely_halted match_initial_cores.
               destruct (inj_plus_sim_diag _ _ _ _ CS _ _ _ _ MCS) as [c2' [m2' [dc' [j' [InjInc [InjSep [MCS' CSP]]]]]]].
               exists c2'. exists m2'. exists dc'. exists j'.  split. assumption. split. assumption.  split. assumption. left. trivial.
Qed.

End INJ_SIMULATION_PLUS.
End Sim_INJ_SIMU_DIAGRAMS.


