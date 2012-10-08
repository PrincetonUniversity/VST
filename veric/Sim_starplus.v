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
         forall (d : core_data) (st1 : C1) (st2 : C2) (e : external_function) (args : list val),
         match_cores d st1 st2 ->
         at_external Sem1 st1 = Some (e, args) ->
         at_external Sem2 st2 = Some (e, args) /\
         Forall2 Val.has_type args (sig_args (ef_sig e)).

  Hypothesis eq_after_external: forall (d : core_data) (st1 : C1) (st2 : C2) (ret : val)
                                                                 (e : external_function) (args : list val),
                      match_cores d st1 st2 ->
                      at_external Sem1 st1 = Some (e, args) ->
                      at_external Sem2 st2 = Some (e, args) ->
                      Forall2 Val.has_type args (sig_args (ef_sig e)) ->
                      Val.has_type ret (proj_sig_res (ef_sig e)) ->
                      exists st1' : C1, exists st2' : C2, exists d' : core_data,
                              after_external Sem1 ret st1 = Some st1' /\
                              after_external Sem2 ret st2 = Some st2' /\ match_cores d' st1' st2'.
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

Section SIMULATION_STAR.
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
           destruct H. specialize (eq_after_external _ _ _ _ _ _ H H0 H1 H2 H3).
                destruct eq_after_external  as [c1' [c2' [d' [AftExt1 [AftExt2 MC]]]]].
                exists c1'. exists c2'. exists (d',c). split; trivial. split; trivial. left. assumption.
          destruct H. rewrite (eq_star_atExt_Zero _ _ H0) in H. inv H.
Qed.
End SIMULATION_STAR.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.
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

End SIMULATION_PLUS.

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