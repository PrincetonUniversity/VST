Add LoadPath "..".
Require Import veric.base.
Require Import compcert.Errors.

Require Import compcert.Csharpminor.
Require Import compcert.Cminor.
Require Import veric.Cminor_CompcertSemantics.
Require Import veric.CSharpminor_CompcertSemantics.

Require Import veric.sim.
Require Import veric.Sim_starplus.
Require Import compcert.Cminorgen.
Require Import compcert.CminorgenproofRestructured.

Require Import Coq.Program.Equality.

Section TRANSLATION.
Variable prog: Csharpminor.program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: transl_program prog = OK tprog.
Let ge : Csharpminor.genv := Genv.globalenv prog.
Let gce : compilenv := build_global_compilenv prog.
Let tge: genv := Genv.globalenv tprog.

Let core_data := unit.
(*
Definition match_state ( _ : core_data) (j:meminj) (c:CSharpMin_core)  (m: mem) (c': CMin_core)(m':mem) : Prop :=
  match c, c' with
      CSharpMin_State f s k e le, CMin_State f' s' k' sp' e' =>
               match_states prog (Csharpminor.State f s k e le m) (Cminor.State f' s' k' sp' e' m')
  | CSharpMin_Callstate f args k, CMin_Callstate f' args' k' =>
               match_states prog (Csharpminor.Callstate f args k m) (Cminor.Callstate f' args' k' m')
  | CSharpMin_Returnstate v k, CMin_Returnstate v' k' =>
               match_states prog (Csharpminor.Returnstate v k m) (Cminor.Returnstate v' k' m')
  | _ , _ => False
  end.
*)
Inductive match_cores: core_data -> meminj -> CSharpMin_core -> mem -> CMin_core -> mem -> Prop :=
  | MC_states:
      forall fn s k e le m tfn ts tk sp te tm cenv xenv j lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt fn.(fn_return) cenv xenv s = OK ts)
      (MINJ: Mem.inject j m tm)
      (MCS: match_callstack prog j m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk fn.(fn_return) cenv xenv cs),
      match_cores tt j (CSharpMin_State fn s k e le) m
                   (CMin_State tfn ts tk (Vptr sp Int.zero) te) tm
  | MC_state_seq:
      forall fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv j lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt fn.(fn_return) cenv xenv s1 = OK ts1)
      (MINJ: Mem.inject j m tm)
      (MCS: match_callstack prog j m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont (Csharpminor.Kseq s2 k) tk fn.(fn_return) cenv xenv cs),
      match_cores tt j (CSharpMin_State fn (Csharpminor.Sseq s1 s2) k e le) m
                   (CMin_State tfn ts1 tk (Vptr sp Int.zero) te) tm
  | MC_callstate:
      forall fd args k m tfd targs tk tm j cs cenv
      (TR: transl_fundef gce fd = OK tfd)
      (MINJ: Mem.inject j m tm)
      (MCS: match_callstack prog j m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk (Csharpminor.funsig fd).(sig_res) cenv nil cs)
      (ISCC: Csharpminor.is_call_cont k)
      (ARGSINJ: val_list_inject j args targs)

(*LENB: added the following 2 conditions , to enable a proof of sim.at_external.
  Really, the first one should suffice (since the second one should follow from the first one and  
   (ARGSINJ: val_list_inject j args targs). Maybe we should add a (boolean-valued version of)
     these conditions in CSharpminor_CompcertSemantics.CSharpMin_at_external, and
     similarly for Cminor?*)
     (ARGSTYP: Forall2 Val.has_type args (Csharpminor.funsig fd).(sig_args))
     (TARGSTYP: Forall2 Val.has_type targs (Csharpminor.funsig fd).(sig_args)),
 
      match_cores tt j (CSharpMin_Callstate fd args k) m
                   (CMin_Callstate tfd targs tk) tm
  | MC_returnstate:
      forall v k m tv tk tm j cs ty cenv
      (MINJ: Mem.inject j m tm)
      (MCS: match_callstack prog j m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk ty cenv nil cs)
      (RESINJ: val_inject j v tv),
      match_cores tt j (CSharpMin_Returnstate v k) m
                   (CMin_Returnstate tv tk) tm.

Lemma init_cores: forall v1 v2 vals1 (c1 : CSharpMin_core) m1 j vals2 m2 
      sig
      (CSM_Ini : make_initial_core CSharpMin_CompcertCoreSem ge v1 vals1 = Some c1)
      (Inj : Mem.inject j m1 m2)
      (VI: Forall2 (val_inject j) vals1 vals2)
      (HT: Forall2 Val.has_type vals2 (sig_args sig)),
exists cd : core_data,
  exists c2 : CMin_core,
    make_initial_core CMin_CompcertCoreSem tge v2 vals2 = Some c2 /\
    match_cores cd j c1 m1 c2 m2.
Proof.
  intros. inv CSM_Ini.
  unfold  CSharpMin_make_initial_core in H0.
                              remember (Genv.find_symbol ge CSharpMin_MainIdent) as z; destruct z; try inv H0.
                              remember (Genv.find_funct_ptr ge b) as zz; destruct zz; try inv H1.
                              remember (Csharpminor.funsig f) as fs; destruct fs.
                              destruct sig_args; try inv H0.
                              destruct sig_res; try inv H1.
                              destruct t; try inv H0.
  apply eq_sym in Heqzz.
  destruct (function_ptr_translated _ _ TRANSL _ _ Heqzz) as [tf [FIND TR]].  
  exists tt. eexists.
  split.
  (*make_initial_core*)
      simpl. unfold CMin_make_initial_core.
      unfold ge in *. assert (ID: CMin_MainIdent = CSharpMin_MainIdent). admit. rewrite ID in *. 
              assert (X: Genv.find_symbol tge CSharpMin_MainIdent =  Genv.find_symbol (Genv.globalenv prog) CSharpMin_MainIdent).
                 apply symbols_preserved; assumption.
             rewrite <- Heqz in X. rewrite X. unfold tge in *. rewrite FIND. 
        rewrite (sig_preserved _ _ _ TR). rewrite <- Heqfs. reflexivity.
  (*match_cores*)
  eapply MC_callstate with (j := j) (cs := @nil frame); try eassumption.
      Focus 2. econstructor.
      Focus 2. econstructor.
      Focus 2. econstructor.
(*   
     destruct Inj. clear HT VI vals1 vals2 Heqz Heqzz Heqfs FIND TR f tf. destruct mi_inj.
     apply mcs_nil with (Mem.nextblock m1). 
            
      apply match_globalenvs_init; auto. can't be right since memories are not necessarily initial
omega. omega.
  instantiate (1 := gce). constructor.
  red; auto. constructor.  econstructor.
          econstructor.*)
Admitted.

Lemma MC_safely_halted: forall (cd : core_data) (j : meminj) (c1 : CSharpMin_core) (m1 : mem)
  (c2 : CMin_core) (m2 : mem) (v1 : int),
match_cores cd j c1 m1 c2 m2 ->
safely_halted CSharpMin_CompcertCoreSem ge c1 = Some v1 ->
safely_halted CMin_CompcertCoreSem tge c2 = Some v1 /\ Mem.inject j m1 m2.
Proof.
  intros.
  inv H; simpl in *; try congruence.
     inv RESINJ; simpl in *; trivial; try congruence.
         inv MK; try congruence.
           split; assumption.
Qed.

Lemma MC_at_external: forall (cd : core_data) (j : meminj) (st1 : CSharpMin_core) (m1 : mem)
  (st2 : CMin_core) (m2 : mem) (e : external_function) (vals1 : list val) sig,
match_cores cd j st1 m1 st2 m2 ->
at_external CSharpMin_CompcertCoreSem st1 = Some (e, sig, vals1) ->
Mem.inject j m1 m2 /\
Events.meminj_preserves_globals ge j /\
(exists vals2 : list val,
   Forall2 (val_inject j) vals1 vals2 /\
   Forall2 Val.has_type vals2 (sig_args (ef_sig e)) /\
   at_external CMin_CompcertCoreSem st2 = Some (e, sig, vals2)).
Proof.
  intros.
  inv H; simpl in *; try congruence.
  split; trivial.
  split. destruct (match_callstack_match_globalenvs _ _ _ _ _ _ _ MCS) as [hi Hhi].
              eapply inj_preserves_globals; eassumption.
  destruct fd; try congruence. inv H0.
  exists targs.
  split. eapply val_list_inject_forall_inject; eassumption.
  inv TR.
  split; trivial.
Qed.

(* Require Import compcert.Events.*)
Lemma MC_after_external:forall (cd : core_data) (j j' : meminj) (st1 : CSharpMin_core)
  (st2 : CMin_core) (m1 : mem) (e : external_function) (vals1 : list val) sig
  (ret1 : val) (m1' m2 m2' : mem) (ret2 : val),
Mem.inject j m1 m2 ->
match_cores cd j st1 m1 st2 m2 ->
at_external CSharpMin_CompcertCoreSem st1 = Some (e, sig, vals1) ->
Events.meminj_preserves_globals ge j ->
inject_incr j j' ->
Events.inject_separated j j' m1 m2 ->
Mem.inject j' m1' m2' ->
val_inject j' ret1 ret2 ->
mem_forward m1 m1' ->
Events.mem_unchanged_on (Events.loc_unmapped j) m1 m1' ->
mem_forward m2 m2' ->
Events.mem_unchanged_on (Events.loc_out_of_reach j m1) m2 m2' ->
Val.has_type ret2 (proj_sig_res (ef_sig e)) ->
exists cd' : core_data,
  exists st1' : CSharpMin_core,
    exists st2' : CMin_core,
      after_external CSharpMin_CompcertCoreSem (Some ret1) st1 = Some st1' /\
      after_external CMin_CompcertCoreSem (Some ret2) st2 = Some st2' /\
      match_cores cd' j' st1' m1' st2' m2'.
Proof. intros.
  destruct (MC_at_external _ _ _ _ _ _ _ _ _ H0 H1) as [_ [_ [vals2 [ValsInj [vals2Typ AtExt2]]]]].
  inv H0; simpl in *; try congruence.
  destruct fd; try congruence. inv H1.
  destruct tfd; try congruence. inv AtExt2.
  exists tt. eexists. eexists.
    split. reflexivity.
    split. reflexivity.
  simpl in *.
  econstructor; try eassumption.
  (*clear TR.*)
admit.
(*  destruct k; simpl in *; try contradiction. (*cases k = Kseq and k=Kblock eliminated*)
  (*k=Kstop*) 
      inv MK; simpl in *.
  exploit match_callstack_match_globalenvs; eauto. intros [hi MG].
  exploit Events.external_call_mem_inject; eauto. 
  eapply Events.external_call_symbols_preserved_2; eauto.

(*  eapply inj_preserves_globals; eauto.*)
  Focus 2. 
  intros [f' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH [INCR SEPARATED]]]]]]]]].
  eapply Events.external_call_symbols_preserved_2; eauto.
   econstructor. exact symbols_preserved.
  left; econstructor; split.
  apply plus_one. econstructor.
  eapply external_call_symbols_preserved_2; eauto.
  exact symbols_preserved.
  eexact var_info_translated.
  eexact var_info_rev_translated.
  econstructor; eauto.
  apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm).
  eapply match_callstack_external_call; eauto.
  intros. eapply external_call_max_perm; eauto.
  omega. omega.
  eapply external_call_nextblock_incr; eauto.
  eapply external_call_nextblock_incr; eauto.

  exploit transl_expr_correct; eauto. intros [tvf [EVAL1 [VINJ1 APP1]]].
  assert (tvf = vf).
    exploit match_callstack_match_globalenvs; eauto. intros [bnd MG].
    eapply val_inject_function_pointer; eauto.
  subst tvf.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  left; econstructor; split.
  apply plus_one. eapply step_call; eauto.
  apply sig_preserved; eauto.
  econstructor; eauto.
  eapply match_Kcall with (cenv' := cenv); eauto.
  red; auto.
  monadInv TR. eapply match_callstack_external_call.
     apply H8. apply H10. assumption. apply H4.
  exploit transl_expr_correct; eauto.
     eapply match_callstack_external_call; try eassumption. (* intros [tv [EVAL [VINJ APP]]].*)
     exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  econstructor; split.
  apply plus_one. eapply step_return_1. eauto. eauto. 
  econstructor; eauto. eapply match_call_cont; eauto.
  eapply match_callstack_external_call; try eassumption.
  assert (MCF:= match_callstack_freelist).
  assert (ECall := match_callstack_external_call).
    eapply ECall. apply H8. apply H10. assumption. assumption. admit. clear ECall.
     assert (TC:= transl_expr_correct _ _ TRANSL).  _ _ _ _ _ _ _ _ _ _ _ _ MINJ).
  simpl in *.
  assert (MCF:= match_callstack_freelist).
  eapply match_callstack_external_call; try eassumption. eassumption. eassumption. eassumption.
  assert (MCF:= match_callstack_freelist).
  assert (Z: exists lo, exists hi, exists sp, exists te, exists tf, exists e, exists le ,
        match_callstack prog j m1 m2 (Frame cenv tf e le te sp lo hi :: nil)  (Mem.nextblock m1) (Mem.nextblock m2)).
          eexists. eexists. eexists. eexists. eexists.  eexists. eexists. 
           eapply mcs_cons. Focus 5. eassumption.
Focus 5. destruct Z as [lo [hi [sp [te [tf [ee [le MCSFrame]]]]]]].
  assert (TC:= transl_expr_correct _ _ TRANSL _ _ _ _ _ _ _ _ _ _ _ _ MINJ MCSFrame).

 
  assert (TC:= transl_expr_correct _ _ TRANSL _ _ _ _ _ _ _ _ _ _ _ _ MINJ MCS).
  simpl in *.
  assert (MCF:= match_callstack_freelist).
  eapply match_callstack_external_call; try eassumption. eassumption. eassumption. eassumption.
  assert (MCF:= match_callstack_freelist).
  assert (Z: exists lo, exists hi, exists sp, exists te, exists tf, exists e, exists le ,
        match_callstack prog j m1 m2 (Frame cenv tf e le te sp lo hi :: nil)  (Mem.nextblock m1) (Mem.nextblock m2)).
          eexists. eexists. eexists. eexists. eexists.  eexists. eexists. 
           eapply mcs_cons. Focus 5. eassumption.
Focus 5. destruct Z as [lo [hi [sp [te [tf [ee [le MCSFrame]]]]]]].
  assert (TC:= transl_expr_correct _ _ TRANSL _ _ _ _ _ _ _ _ _ _ _ _ MINJ MCSFrame).

  j m1 m2 
  assert (X:= match_callstack_external_call).
  assert (MCF:= match_callstack_freelist).
  assert (TC:= transl_expr_correct _ _ TRANSL _ _ _ _ _ _ _ _ _ _ _ _ MINJ). MCS).
  monadInv TR. eapply match_callstack_external_call.
     apply H8. apply H10. assumption. apply H4.
  exploit transl_expr_correct; eauto.
     eapply match_callstack_external_call; try eassumption. (* intros [tv [EVAL [VINJ APP]]].*)
     exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  econstructor; split.
  apply plus_one. eapply step_return_1. eauto. eauto. 
  econstructor; eauto. eapply match_call_cont; eauto.
  eapply match_callstack_external_call; try eassumption.
         
  inv TR.
*)
Qed.

Parameter MC_order :  core_data -> core_data -> Prop. 
Parameter MC_wellfounded: well_founded MC_order.
(*Definition MC_measure (q:CSharpMin_core): nat :=
  match q with
  | CSharpMin_State fn s k e le => seq_left_depth s
  | _ => O
  end.*)
Parameter MC_measure: CSharpMin_core-> nat.

Lemma MC_matchstates: forall j
       q m q' m',
      match_cores tt j q m q' m' -> 
      match_statesInj prog j  (ToState q m) (Cminor_CompcertSemantics.ToState q' m').
  Proof. intros.
    inv H; simpl in *.
     eapply matchInj_state; try eassumption. 
     eapply matchInj_state_seq; try eassumption. 
     eapply matchInj_callstate; try eassumption. 
     eapply matchInj_returnstate; try eassumption.
Qed.  

Lemma MC_matchcores: forall j q m q' m',
      match_statesInj prog j (ToState q m) (Cminor_CompcertSemantics.ToState q' m') ->
      match_cores tt j q m q' m'.
  Proof. intros.
    inv H; simpl in *.
     destruct q; simpl in *; inv H2.
        destruct q'; simpl in *; inv H3.
        eapply MC_states; try eassumption. 
     destruct q; simpl in *; inv H2.
        destruct q'; simpl in *; inv H3.
        eapply MC_state_seq; try eassumption. 
     destruct q; simpl in *; inv H2.
        destruct q'; simpl in *; inv H3.
        eapply MC_callstate; try eassumption. admit. admit. (*New conditions ARGSTYP and TARGSTYP*)
     destruct q; simpl in *; inv H2.
        destruct q'; simpl in *; inv H3.
        eapply MC_returnstate; try eassumption.
Qed.  

Lemma MC_atExt: forall j c1 m1 c2 m2
(H: match_statesInj prog j (ToState c1 m1) (Cminor_CompcertSemantics.ToState c2 m2) ),
(CSharpMin_at_external c1 = None) = (CMin_at_external c2 = None).
Proof.
  intros.
  destruct c1; destruct c2; inv H; simpl in *; trivial.
  destruct f; destruct f0; simpl in *; trivial.
     remember (transl_function (build_global_compilenv prog) f) as z.
     destruct z; simpl in *. inv TR. inv TR.
  inv TR.
  apply prop_ext. split; intros; inv H.
Qed.

Lemma inject_separated_same_meminj: forall j m m', Events.inject_separated j j m m'.
  Proof. intros j m m' b; intros. congruence. Qed.

Lemma MS_step_case_SkipSeq:
forall cenv sz f tfn j m tm  e le te sp lo hi cs s k tk xenv
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MK : match_cont (Csharpminor.Kseq s k) tk (fn_return f) cenv xenv cs)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn Sskip tk (Vptr sp Int.zero) te) tm c2' m2' /\
   exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f s k e le) m c2' m2'.
Proof. intros.
(*  destruct (trans_step_case_SkipSeq _ _ TRANSL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF MINJ MCS MK) as [T2 [Steps MSI]].
   apply matchInj_Elim in MSI. eauto.*)
  dependent induction MK.

  eexists. eexists. 
  split.
    apply corestep_plus_one. 
        eapply CompCertStep_CMin_corestep'.  simpl.  econstructor. reflexivity.
  simpl. exists (CSharpMin_State f s k e le).
     left. eapply MC_states; eauto.
 
  eexists. eexists.
  split.
    apply corestep_plus_one. 
        eapply CompCertStep_CMin_corestep'.  simpl.  econstructor. reflexivity.
   simpl. exists (CSharpMin_State f (Csharpminor.Sseq s1 s2) k e le).
      left.  eapply MC_state_seq; eauto.

  exploit IHMK; eauto. clear IHMK.  intros [T2 [m2 [A [c' C]]]].
  exists T2; exists m2.
  split.
     eapply corestep_star_plus_trans.
        apply corestep_star_one.  eapply CompCertStep_CMin_corestep'.  simpl.  constructor. reflexivity.
        simpl. apply A. 
  simpl in *. exists c'. apply C.
Qed.

Lemma MS_step_case_SkipBlock: 
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv 
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MK : match_cont (Csharpminor.Kblock k) tk (fn_return f) cenv xenv cs)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn Sskip tk (Vptr sp Int.zero) te) tm c2' m2' /\
exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f Csharpminor.Sskip k e le) m c2' m2'.
Proof. intros.
  dependent induction MK.

  eexists. eexists. 
  split.
    apply corestep_plus_one. 
        eapply CompCertStep_CMin_corestep'.  simpl. constructor. reflexivity.  
   simpl. exists (CSharpMin_State f Csharpminor.Sskip k e le).
      left.  eapply MC_states; eauto.

  exploit IHMK; eauto. clear IHMK.  intros [T2 [m2 [A [c' C]]]].
  exists T2; exists m2.
  split.
     eapply corestep_star_plus_trans.
        apply corestep_star_one.  eapply CompCertStep_CMin_corestep'.  simpl.  constructor. reflexivity.
        simpl. apply A. 
  simpl in *. exists c'. apply C.
Qed.

Lemma MS_match_is_call_cont:
  forall tfn te sp tm k tk ty cenv xenv cs,
  match_cont k tk ty cenv xenv cs ->
  Csharpminor.is_call_cont k ->
  exists tk',
    corestep_star CMin_core_sem tge (CMin_State tfn Sskip tk sp te) tm
                (CMin_State tfn Sskip tk' sp te) tm
    /\ is_call_cont tk'
    /\ match_cont k tk' ty cenv nil cs.
Proof.
  induction 1; simpl; intros; try contradiction.
  econstructor; split.
     apply corestep_star_zero. split. exact I. econstructor; eauto.
  exploit IHmatch_cont; eauto.
  intros [tk' [A B]]. exists tk'; split.
  eapply corestep_star_trans; eauto. apply corestep_star_one. simpl. eexists. constructor. auto.

  econstructor; split. apply corestep_star_zero. split. exact I. econstructor; eauto.
Qed.

Lemma MS_step_case_SkipCall:
 forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv m'
(CC: Csharpminor.is_call_cont k)
(RET: fn_return f = None)
(FL: Mem.free_list m (blocks_of_env e) = Some m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MK : match_cont k tk (fn_return f) cenv xenv cs)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State  tfn Sskip tk (Vptr sp Int.zero) te) tm c2' m2' /\
exists c' : CSharpMin_core,
       inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_Returnstate Vundef k) m' c2' m2'.
Proof. intros.
  exploit MS_match_is_call_cont; eauto. intros [tk' [A [B C]]]. 
  exploit match_callstack_freelist; eauto. intros [tm' [P [Q R]]].

  eexists. eexists.
  split.
    eapply corestep_star_plus_trans. eexact A. apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. apply step_skip_call. assumption. 
        rewrite (sig_preserved_body _ _ _ _ TRF). auto.
    eauto.
    econstructor; eauto.

  simpl in *. exists (CSharpMin_Returnstate Vundef k). left. econstructor; eauto.
Qed.

Lemma MS_step_case_Assign:
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv m' ts  x a x0 v id
(EE:Csharpminor.eval_expr ge e le m a v)
(ASS: exec_assign ge e m id v m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MK : match_cont k tk (fn_return f) cenv xenv cs)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(EQ : transl_expr cenv a = OK (x, x0))
(EQ0 : var_set cenv id x = OK ts),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State  tfn  ts tk (Vptr sp Int.zero) te) tm c2' m2' /\
  exists c' : CSharpMin_core,
       inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f Csharpminor.Sskip k e le) m' c2' m2'.
Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  exploit var_set_correct; eauto. 
  intros [te' [tm' [EXEC [MINJ' [MCS' OTHER]]]]].
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. eexact EXEC. reflexivity.
  simpl in *. exists (CSharpMin_State f Csharpminor.Sskip k e le). left. econstructor; eauto.
Qed.

Lemma MS_step_case_Set:
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv x x0 v a id
(H: Csharpminor.eval_expr ge e le m a v)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk (fn_return f) cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State  tfn (Sassign (for_temp id) x) tk (Vptr sp Int.zero) te) tm c2' m2' /\
  exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j 
          (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v le)) m c2' m2' .
Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. econstructor; eauto.  reflexivity.
  simpl in *.
  assert (X:= match_callstack_set_temp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ id _ _ VINJ MCS).
  exists (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v le)).
    left. econstructor; eauto.
Qed.

Lemma MS_step_case_Store:
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv x x0 x1 x2 
      chunk m' a addr vaddr v
(CH: Mem.storev chunk m vaddr v = Some m')
(EvAddr : Csharpminor.eval_expr ge e le m addr vaddr)
(EvA : Csharpminor.eval_expr ge e le m a v)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
                (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk (fn_return f) cenv xenv cs)
(EQ : transl_expr cenv addr = OK (x, x0))
(EQ1 : transl_expr cenv a = OK (x1, x2)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State  tfn (make_store chunk x x1) tk (Vptr sp Int.zero) te) tm c2' m2' /\
 exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j 
                      (CSharpMin_State f Csharpminor.Sskip k e le) m' c2' m2' .
Proof. intros.
  exploit transl_expr_correct. eauto. eauto. eauto. eexact EvAddr. eauto. 
  intros [tv1 [EVAL1 [VINJ1 APP1]]].
  exploit transl_expr_correct. eauto. eauto. eauto. eexact EvA. eauto. 
  intros [tv2 [EVAL2 [VINJ2 APP2]]].
  exploit make_store_correct. eexact EVAL1. eexact EVAL2. eauto. eauto. auto. auto.
  intros [tm' [tv' [EXEC [STORE' MINJ']]]].
  eexists; eexists; split.
      apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. eexact EXEC. reflexivity.
  simpl in *.
    assert (X:= match_callstack_storev_mapped _ _ _ _ _ _ _ _ _ _ _  VINJ1 CH STORE' _ _ _ MCS).
    exists (CSharpMin_State f Csharpminor.Sskip k e le).
    left. econstructor; eauto.
      rewrite (nextblock_storev _ _ _ _ _ CH).
      rewrite (nextblock_storev _ _ _ _ _ STORE').
      eauto.
Qed. 

Lemma MS_step_case_Call:
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv  x x0 x1 a vf fd optid vargs bl
(EvalA: Csharpminor.eval_expr ge e le m a vf)
(EvalBL: Csharpminor.eval_exprlist ge e le m bl vargs)
(FF: Genv.find_funct ge vf = Some fd)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k (fn_return f) cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0))
(EQ1 : transl_exprlist cenv bl = OK x1),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge 
           (CMin_State  tfn (Scall (option_map for_temp optid) (Csharpminor.funsig fd) x x1)  k (Vptr sp Int.zero) te) tm c2' m2' /\
 exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j
              (CSharpMin_Callstate fd vargs (Csharpminor.Kcall optid f e le tk)) m c2' m2'.
Proof. intros.
  simpl in FF. exploit functions_translated; eauto. intros [tfd [FIND TRANS]].
  exploit transl_expr_correct; eauto. intros [tvf [EVAL1 [VINJ1 APP1]]].
  assert (tvf = vf).
    exploit match_callstack_match_globalenvs; eauto. intros [bnd MG].
    eapply val_inject_function_pointer; eauto.
  subst tvf.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  eexists; eexists; split.
      apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
          eapply step_call. eassumption. eassumption. apply FIND.
                      eapply sig_preserved; eauto.
          econstructor; eauto.
  simpl in *.
     exists  (CSharpMin_Callstate fd vargs (Csharpminor.Kcall optid f e le tk)).
     left. econstructor; eauto. eapply match_Kcall with (cenv' := cenv); eauto.
            simpl; trivial.
      admit. admit. (*These are the new conditions in rule MC_Callstate*)
Qed.

Lemma MS_step_case_Builtin:
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv x t ef optid vres m' bl vargs
(EvalArgs: Csharpminor.eval_exprlist ge e le m bl vargs)
(ExtCall: Events.external_call ef ge vargs m t vres m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk (fn_return f) cenv xenv cs)
(EQ : transl_exprlist cenv bl = OK x),
exists c2' : CMin_core,
  exists m2' : mem, 
      corestep_plus CMin_core_sem tge
           (CMin_State tfn (Sbuiltin (option_map for_temp optid) ef x) tk (Vptr sp Int.zero) te) tm c2' m2' /\
  exists j' : meminj,
        inject_incr j j' /\
        Events.inject_separated j j' m tm /\
  exists c',
        inj_match_states_star unit match_cores MC_measure (tt,c') j'
          (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid vres le)) m' c2' m2'.
Proof. intros.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  exploit match_callstack_match_globalenvs; eauto. intros [hi' MG].
  exploit Events.external_call_mem_inject; eauto. 
       eapply inj_preserves_globals; eauto.
  intros [j' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH [INCR SEPARATED]]]]]]]]].
  eexists; eexists; split.
      apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
           econstructor; try eassumption.
             eapply Events.external_call_symbols_preserved_2; eauto.
                 eapply symbols_preserved; assumption.
                 eapply var_info_translated; assumption.
                 eapply var_info_rev_translated; assumption.
           reflexivity.
  assert (MCS': match_callstack prog j' m' tm'
                 (Frame cenv tfn e le te sp lo hi :: cs)
                 (Mem.nextblock m') (Mem.nextblock tm')).
    apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm).
    eapply match_callstack_external_call; eauto.
    intros. eapply Events.external_call_max_perm; eauto.
    omega. omega. 
    eapply external_call_nextblock_incr; eauto.
    eapply external_call_nextblock_incr; eauto.
exists j'. split. assumption.  split. assumption. 
  simpl in *. exists  (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid vres le)).
  left. econstructor; eauto.
Opaque PTree.set.
  unfold set_optvar. destruct optid; simpl. 
  eapply match_callstack_set_temp; eauto. 
  auto.
Qed.

Lemma MS_step_case_Ite: 
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv x x0 x1 x2 b v a s1 s2
(H : Csharpminor.eval_expr ge e le m a v)
(BoolOfVal : Val.bool_of_val v b)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk (fn_return f) cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0))
(EQ1 : transl_stmt (fn_return f) cenv xenv s1 = OK x1)
(EQ0 : transl_stmt (fn_return f) cenv xenv s2 = OK x2),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge
             (CMin_State tfn (Sifthenelse x x1 x2) tk (Vptr sp Int.zero) te) tm c2' m2' /\
  exists c',
        inj_match_states_star unit match_cores MC_measure (tt,c') j
             (CSharpMin_State f (if b then s1 else s2) k e le) m c2' m2'.
Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  exists (CMin_State tfn (if b then x1 else x2) tk (Vptr sp Int.zero) te). exists tm.
  split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep.
              eapply step_ifthenelse; eauto. eapply bool_of_val_inject; eauto.
        econstructor; eauto.
  simpl in *.
    exists (CSharpMin_State f (if b then s1 else s2) k e le).
    left. econstructor; eauto.
       destruct b; auto.
Qed.

Lemma MS_step_case_Loop:
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv x s
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k (fn_return f) cenv xenv cs)
(EQ : transl_stmt (fn_return f) cenv xenv s = OK x),
exists c2' : CMin_core,
  exists m2' : mem,
      corestep_plus CMin_core_sem tge (CMin_State tfn (Sloop x) k (Vptr sp Int.zero) te) tm c2' m2' /\
    exists c',   inj_match_states_star unit match_cores MC_measure (tt,c') j
          (CSharpMin_State f s (Csharpminor.Kseq (Csharpminor.Sloop s) tk) e le) m c2' m2'. 
Proof. intros.
  eexists; eexists.
  split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
        econstructor; eauto.
        reflexivity.
  simpl in *.
      exists  (CSharpMin_State f s (Csharpminor.Kseq (Csharpminor.Sloop s) tk) e le).
      left.
      econstructor; eauto. econstructor; eauto. simpl. rewrite EQ; auto. 
Qed.

Lemma MS_step_case_Block:
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv x s
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k (fn_return f) cenv xenv cs)
(EQ : transl_stmt (fn_return f) cenv (true :: xenv) s = OK x),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn (Sblock x) k (Vptr sp Int.zero) te) tm c2' m2' /\
    exists c' ,
       inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f s (Csharpminor.Kblock tk) e le) m c2' m2'.
Proof. intros.
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
        econstructor; eauto.
        reflexivity.
  simpl in *.
      exists  (CSharpMin_State f s (Csharpminor.Kblock tk) e le).
      left.
      econstructor; eauto. econstructor; eauto. 
Qed.

Lemma MS_step_case_ExitSeq:
forall  cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv n s
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kseq s tk) k (fn_return f) cenv xenv cs),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge
               (CMin_State tfn (Sexit (shift_exit xenv n)) k (Vptr sp Int.zero) te) tm c2' m2'  /\
    exists c',  inj_match_states_star unit match_cores MC_measure (tt,c') j
                                   (CSharpMin_State f (Csharpminor.Sexit n) tk e le) m c2' m2'.
Proof. intros.
  dependent induction MK.

  eexists; eexists; split. 
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
        econstructor; eauto.
        reflexivity.
  simpl in *.
      exists   (CSharpMin_State f (Csharpminor.Sexit n) tk e le).
      left. econstructor; eauto. reflexivity.

  exploit IHMK; eauto. intros [c2' [m2' [A B]]].
  exists c2'. exists m2'. 
  split; auto. 
     eapply corestep_plus_trans. 
         apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
         simpl. apply A.

  exploit IHMK; eauto.  intros [c2' [m2' [A B]]].
  exists c2'. exists m2'. 
  split; auto. 
     eapply corestep_plus_trans. 
         apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
         simpl. apply A.
Qed.

Lemma MS_step_case_ExitBlockZero:
forall  cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv 
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kblock tk) k (fn_return f) cenv xenv cs),
exists c2' : CMin_core,
  exists m2' : mem,
       corestep_plus CMin_core_sem tge (CMin_State tfn (Sexit (shift_exit xenv 0)) k (Vptr sp Int.zero) te) tm c2' m2' /\
    exists c', inj_match_states_star unit match_cores MC_measure (tt,c') j
                                    (CSharpMin_State f Csharpminor.Sskip tk e le) m c2' m2'.
Proof. intros.
  dependent induction MK.

  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity. 
  simpl in *.
    exists  (CSharpMin_State f Csharpminor.Sskip tk e le). 
    left. econstructor; eauto.

  exploit IHMK; eauto. intros [c2' [m2' [A B]]].
  exists c2'. exists m2'. 
  split; auto. 
     eapply corestep_plus_trans. 
         apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
         simpl. apply A.
Qed.

Lemma MS_step_case_ExitBlockNonzero:
forall  cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv n
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
                     (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kblock tk) k (fn_return f) cenv xenv cs),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge
                     (CMin_State tfn (Sexit (shift_exit xenv (S n))) k (Vptr sp Int.zero) te) tm c2' m2' /\ 
    exists c', inj_match_states_star unit match_cores MC_measure (tt,c') j
          (CSharpMin_State f (Csharpminor.Sexit n) tk e le) m c2' m2'.
Proof. intros.
  dependent induction MK.

  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity. 
  simpl in *.
    exists  (CSharpMin_State f (Csharpminor.Sexit n) tk e le).
    left. econstructor; eauto. auto.

  exploit IHMK; eauto. intros [c2' [m2' [A B]]].
  exists c2'. exists m2'. 
  split; auto. 
     eapply corestep_plus_trans. 
         apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
         simpl. apply A.
Qed.

Lemma MS_switch_descent:
  forall ty cenv xenv k ls body s,
  transl_lblstmt ty cenv (switch_env ls xenv) ls body = OK s ->
  exists k',
  transl_lblstmt_cont ty cenv xenv ls k k'
  /\ (forall f sp e m,
      corestep_plus CMin_core_sem tge (CMin_State f s k sp e) m (CMin_State f body k' sp e) m).
Proof.
  induction ls; intros.
(*1*) 
  monadInv H.
  eexists; split.
      econstructor; eauto.
  intros. eapply corestep_plus_trans. 
                   apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
                   simpl.  apply corestep_plus_one. eapply CompCertStep_CMin_corestep.  constructor. reflexivity.
(*2*)
  monadInv H. exploit IHls; eauto. intros [k' [A B]]. 
  eexists; split.
      econstructor; eauto.
  intros. eapply corestep_plus_star_trans. eauto. 
  eapply corestep_star_trans. 
      apply corestep_star_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
      simpl. apply corestep_star_one. eapply CompCertStep_CMin_corestep.  constructor. reflexivity. 
Qed.

Lemma MS_switch_ascent:
  forall f n sp e m ty cenv xenv k ls k1,
  let tbl := switch_table ls O in
  let ls' := select_switch n ls in
  transl_lblstmt_cont ty cenv xenv ls k k1 ->
  exists k2,
  corestep_star CMin_core_sem tge (CMin_State f (Sexit (compcert.Switch.switch_target n (length tbl) tbl)) k1 sp e) m  (CMin_State f (Sexit O) k2 sp e) m
  /\ transl_lblstmt_cont ty cenv xenv ls' k k2.
Proof.
  induction ls; intros; unfold tbl, ls'; simpl.
(*1*)
  inv H. 
  eexists; split.
     apply corestep_star_zero.
     econstructor; eauto.
(*2*)
  simpl in H. inv H. 
  rewrite Int.eq_sym. destruct (Int.eq i n).
  econstructor; split.  apply corestep_star_zero. econstructor; eauto. 
  exploit IHls; eauto. intros [k2 [A B]].
  rewrite (length_switch_table ls 1%nat 0%nat). 
  rewrite switch_table_shift.
  exists k2; split; try exact B.
  eapply corestep_star_trans.
        eapply corestep_star_one.  eapply CompCertStep_CMin_corestep'. constructor. reflexivity. 
        simpl. eapply corestep_star_trans.
                       eapply corestep_star_one.  eapply CompCertStep_CMin_corestep'. econstructor. reflexivity. 
                       apply A. 
Qed.
Lemma MS_switch_match_statesInj:
  forall fn k e le m tfn ts tk sp te tm cenv xenv j lo hi cs sz ls body tk'
    (TRF: transl_funbody cenv sz fn = OK tfn)
    (TR: transl_lblstmt (fn_return fn) cenv (switch_env ls xenv) ls body = OK ts)
    (MINJ: Mem.inject j m tm)
    (MCS: match_callstack prog j m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
    (MK: match_cont k tk (fn_return fn) cenv xenv cs)
    (TK: transl_lblstmt_cont (fn_return fn) cenv xenv ls tk tk'),
  exists S, exists mm,
  corestep_plus CMin_core_sem tge (CMin_State tfn (Sexit O) tk' (Vptr sp Int.zero) te) tm S mm
  /\ match_statesInj prog j (Csharpminor.State fn (seq_of_lbl_stmt ls) k e le m) (Cminor_CompcertSemantics.ToState S mm).
Proof.
  intros. destruct ls; simpl.
(*1*)
  inv TK. econstructor; eexists; split. 
     eapply corestep_plus_trans.
         eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity. 
         simpl. eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity. 
    simpl. eapply matchInj_state; eauto.
(*2*) 
  inv TK. econstructor; eexists; split.
     eapply corestep_plus_trans.
         eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity. 
         simpl. eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity. 
    simpl. 
       eapply matchInj_state_seq; eauto.
        simpl. eapply  switch_match_cont; eauto. 
Qed.

Lemma MS_step_case_Switch:
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv a x x0 ts cases n
(EvalA: Csharpminor.eval_expr ge e le m a (Vint n))
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk (fn_return f) cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0))
(EQ0 : transl_lblstmt (fn_return f) cenv (switch_env cases xenv) cases
        (Sswitch x (switch_table cases 0) (length (switch_table cases 0))) =
      OK ts),
exists c2' : CMin_core,
  exists m2' : mem,
          corestep_plus CMin_core_sem tge (CMin_State tfn ts tk (Vptr sp Int.zero) te) tm c2' m2' /\
    exists c', inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f (seq_of_lbl_stmt (select_switch n cases)) k e le) m c2' m2'.

Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  inv VINJ.
  exploit MS_switch_descent; eauto. intros [k1 [A B]].
  exploit MS_switch_ascent; eauto. intros [k2 [C D]].
  exploit transl_lblstmt_suffix; eauto. simpl. intros [body' [ts' E]].
  exploit MS_switch_match_statesInj; eauto. intros [T2 [m2' [F G]]].
  exists T2; exists m2'; split.
      eapply corestep_plus_star_trans.
          eapply B. 
      eapply corestep_star_trans.
         eapply corestep_star_one. eapply CompCertStep_CMin_corestep'. constructor. eassumption. reflexivity. 
      simpl.
        eapply corestep_star_trans.
         apply C.
         eapply corestep_plus_star. eapply F.
  exists (CSharpMin_State f (seq_of_lbl_stmt (select_switch n cases)) k e le).
   left. simpl. eapply MC_matchcores. apply G.
Qed.

Lemma MS_step_case_ReturnNone:
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv m'
(Freelist: Mem.free_list m (blocks_of_env e) = Some m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
                 (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k (fn_return f) cenv xenv cs),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn (Sreturn None) k (Vptr sp Int.zero) te) tm c2' m2'  /\
    exists c', inj_match_states_star unit match_cores MC_measure (tt,c') j
                             (CSharpMin_Returnstate Vundef (Csharpminor.call_cont tk)) m' c2' m2'.
Proof. intros.
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. eapply step_return_0. eauto. reflexivity. 
  simpl in *.
    exists (CSharpMin_Returnstate Vundef (Csharpminor.call_cont tk)).
    left. econstructor; eauto. eapply match_call_cont; eauto.
Qed.

Lemma MS_step_case_ReturnSome:
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv a x x0 m' v 
(EvalA: Csharpminor.eval_expr ge e le m a v)
(Freelist: Mem.free_list m (blocks_of_env e) = Some m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k (fn_return f) cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn (Sreturn (Some x)) k (Vptr sp Int.zero) te) tm c2' m2' /\
    exists c' ,
          inj_match_states_star unit match_cores MC_measure (tt,c') j
                 (CSharpMin_Returnstate v (Csharpminor.call_cont tk)) m' c2' m2'.
Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. eapply step_return_1. eauto. eauto. reflexivity. 
  simpl in *.
    exists  (CSharpMin_Returnstate v (Csharpminor.call_cont tk)).
    left. econstructor; eauto. eapply match_call_cont; eauto.
Qed.

Lemma MS_step_case_Label:
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv lbl x s
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk (fn_return f) cenv xenv cs)
(EQ : transl_stmt (fn_return f) cenv xenv s = OK x),
exists c2' : CMin_core,
  exists m2' : mem,
       corestep_plus CMin_core_sem tge (CMin_State tfn (Slabel lbl x) tk (Vptr sp Int.zero) te) tm c2' m2' /\ 
    exists c', inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f s k e le) m c2' m2'.
Proof. intros.
  eexists; eexists; split.
    eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
  simpl.
  exists (CSharpMin_State f s k e le). 
    left. econstructor; eauto.
Qed.

Lemma MS_step_case_Goto:
forall cenv sz f tfn j m tm e le te sp lo hi cs k tk xenv lbl s' k'
(FindLab: Csharpminor.find_label lbl (Csharpminor.fn_body f)
       (Csharpminor.call_cont k) = Some (s', k'))
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e le te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk (fn_return f) cenv xenv cs),
exists c2' : CMin_core,
  exists m2' : mem,
          corestep_plus CMin_core_sem tge (CMin_State tfn (Sgoto lbl) tk (Vptr sp Int.zero) te) tm c2' m2' /\
    exists c', inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f s' k' e le) m c2' m2'.
Proof. intros.
  exploit transl_find_label_body; eauto. 
  intros [ts' [tk' [xenv' [A [B C]]]]].
  eexists; eexists; split.
    eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. apply step_goto. eexact A. reflexivity.
  simpl.
  exists (CSharpMin_State f s' k' e le).
    left. econstructor; eauto.
Qed.

Lemma MS_var_set_self_correct_scalar:
  forall cenv id s a f tf e le te sp lo hi m cs tm tv v m' fn k,
  var_set_self cenv id s = OK a ->
  match_callstack prog f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  val_inject f v tv ->
  Mem.inject f m tm ->
  exec_assign ge e m id v m' ->
  te!(for_var id) = Some tv ->
  exists tm',
    corestep_star CMin_core_sem tge (CMin_State fn a k (Vptr sp Int.zero) te) tm
                                    (CMin_State fn s k (Vptr sp Int.zero) te) tm' /\
    Mem.inject f m' tm' /\
    match_callstack prog f m' tm' (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m') (Mem.nextblock tm').
Proof.
  intros until k. 
  intros VS MCS VINJ MINJ ASG VAL.
  unfold var_set_self in VS. inv ASG. 
  assert (NEXTBLOCK: Mem.nextblock m' = Mem.nextblock m).
    eapply Mem.nextblock_store; eauto.
  assert (MV: match_var prog f id e m te sp cenv!!id).
    inv MCS. inv MENV. auto.
  assert (EVAR: eval_expr tge (Vptr sp Int.zero) te tm (Evar (for_var id)) tv).
    constructor. auto.
  revert VS; inv MV; intro VS; inv VS; inv H; try congruence.
  (* var_local *)
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  exists tm.
  split. apply corestep_star_zero. 
  split. eapply Mem.store_unmapped_inject; eauto. 
  rewrite NEXTBLOCK. 
  apply match_callstack_extensional with (PTree.set (for_var id) tv te).
  intros. repeat rewrite PTree.gsspec.
  destruct (peq (for_var id0) (for_var id)). congruence. auto.
  intros. rewrite PTree.gso; auto. unfold for_temp, for_var; congruence.
  eapply match_callstack_store_local; eauto.
  (* var_stack_scalar *)
  assert (b0 = b) by congruence. subst b0.
  assert (chunk0 = chunk) by congruence. subst chunk0.
  assert (Mem.storev chunk m (Vptr b Int.zero) v = Some m'). assumption.
  exploit make_store_correct.
    eapply make_stackaddr_correct.
    eauto. eauto. eauto. eauto. eauto. 
  intros [tm' [tvrhs' [EVAL' [STORE' MEMINJ]]]].
  exists tm'.
  split. eapply corestep_star_trans.
           eapply corestep_star_one. eapply CompCertStep_CMin_corestep'. econstructor. reflexivity.
         simpl. 
         eapply corestep_star_trans.
           eapply corestep_star_one. eapply CompCertStep_CMin_corestep'. apply EVAL'. reflexivity. 
         simpl.
           eapply corestep_star_one. eapply CompCertStep_CMin_corestep. constructor. reflexivity.
  split. auto.
  rewrite NEXTBLOCK. rewrite (nextblock_storev _ _ _ _ _ STORE'). 
  eapply match_callstack_storev_mapped; eauto.
Qed.

Lemma MS_var_set_self_correct_array:
  forall cenv id s a f tf e le te sp lo hi m cs tm tv b v sz al m' fn k,
  var_set_self cenv id s = OK a ->
  match_callstack prog f m tm (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  val_inject f v tv ->
  Mem.inject f m tm ->
  PTree.get id e = Some(b, Varray sz al) ->
  Events.extcall_memcpy_sem sz (Zmin al 4) ge
                             (Vptr b Int.zero :: v :: nil) m Events.E0 Vundef m' ->
  te!(for_var id) = Some tv ->
  exists f', exists tm',
    corestep_star CMin_core_sem tge (CMin_State fn a k (Vptr sp Int.zero) te) tm
                                    (CMin_State fn s k (Vptr sp Int.zero) te) tm' /\
    Mem.inject f' m' tm' /\
    match_callstack prog f' m' tm' (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m') (Mem.nextblock tm') /\
    inject_incr f f'.
Proof.
  intros until k. 
  intros VS MCS VINJ MINJ KIND MEMCPY VAL.
  assert (MV: match_var prog f id e m te sp cenv!!id).
    inv MCS. inv MENV. auto.
  inv MV; try congruence. rewrite KIND in H0; inv H0.
  (* var_stack_array *)
  unfold var_set_self in VS. rewrite <- H in VS. inv VS.
  exploit match_callstack_match_globalenvs; eauto. intros [hi' MG].
  assert (Events.external_call (EF_memcpy sz0 (Zmin al0 4)) ge (Vptr b0 Int.zero :: v :: nil) m Events.E0 Vundef m').
    assumption.
  exploit Events.external_call_mem_inject; eauto. 
  eapply inj_preserves_globals; eauto.
  intros [f' [vres' [tm' [EC' [VINJ' [MINJ' [UNMAPPED [OUTOFREACH [INCR SEPARATED]]]]]]]]].
  exists f'; exists tm'.
  split. eapply corestep_star_trans.
           eapply corestep_star_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity. 
         simpl.
         eapply corestep_star_trans.
           eapply corestep_star_one. eapply CompCertStep_CMin_corestep'. econstructor; eauto. 
                constructor. apply make_stackaddr_correct. constructor. constructor. eauto. constructor.
                  eapply Events.external_call_symbols_preserved_2; eauto.
                  apply symbols_preserved. assumption.
                  apply var_info_translated. assumption.
                  apply var_info_rev_translated. assumption.
               reflexivity.
         simpl. eapply corestep_star_one. eapply CompCertStep_CMin_corestep. constructor. reflexivity.
  split. auto.
  split. apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm).
  eapply match_callstack_external_call; eauto.
  intros. eapply Events.external_call_max_perm; eauto.
  omega. omega.
  eapply external_call_nextblock_incr; eauto.
  eapply external_call_nextblock_incr; eauto.
  auto.
Qed.

(*Lenb: This seems to be a new lemma*)
Lemma bind_parameters_validblock_1:
forall gee e params vals m1 m2 (BP: bind_parameters gee e m1 params vals m2)
b (B1:Mem.valid_block m1 b), Mem.valid_block m2 b.
Proof. intros gee e params.
  induction params; intros.
   inv BP. trivial.
  destruct vals; inv BP.
    (*skalar*)
      eapply (IHparams _ _ _ H9). clear IHparams H9.
      eapply Mem.store_valid_block_1; eauto.
    (*array*)
      eapply (IHparams _ _ _ H8). clear IHparams H8.
      inv H7. 
      eapply Mem.storebytes_valid_block_1; eauto.
Qed.

(*Lenb: This seems to be a new lemma*)
Lemma bind_parameters_validblock_2:
forall gee e params vals m1 m2 (BP: bind_parameters gee e m1 params vals m2)
b (B1:Mem.valid_block m2 b), Mem.valid_block m1 b.
Proof. intros gee e params.
  induction params; intros.
   inv BP. trivial.
  destruct vals; inv BP.
    (*skalar*)
      eapply Mem.store_valid_block_2. apply H8.
      eapply (IHparams _ _ _ H9 _ B1). 
    (*array*)
      inv H7.
      eapply Mem.storebytes_valid_block_2. apply H13.
      eapply (IHparams _ _ _ H8 _ B1). 
Qed.

(*Lenb: This seems to be a new lemma*)
Lemma bind_parameters_inject_separated_skalar:
forall gee e params vals m1 m2 f' tm3 j tm1 m tm2 v b ch
(CH: Mem.store ch m b 0 v = Some m1)
(BP: bind_parameters gee e m1 params vals m2)
(MINJ : Mem.inject f' m2 tm3)
(SEP : Events.inject_separated j f' m1 tm2),
Events.inject_separated j f' m tm1.
Proof. intros.
  intros bb; intros.
     unfold Events.inject_separated in SEP.
     destruct (SEP _ _ _ H H0).
     split; intros XX.  
       apply H1. eapply Mem.store_valid_block_1; eauto.
     assert (~ Mem.valid_block m2 bb).
       intros ZZ. apply H1. apply (bind_parameters_validblock_2 _ _ _ _ _ _ BP _ ZZ). 
       unfold Mem.inject in MINJ. destruct MINJ.
         rewrite (mi_freeblocks _ H3) in H0. inv H0.    
Qed.

Lemma bind_parameters_inject_separated_array:
forall gee e params vals m1 m2  m cpvals t n sz
(MemCPY: Events.extcall_memcpy_sem sz n gee
         cpvals m t Vundef m1)
(BP: bind_parameters gee e m1 params vals m2) f' tm3 j tm1 tm2 
(MINJ : Mem.inject f' m2 tm3)
(SEP : Events.inject_separated j f' m1 tm2),
Events.inject_separated j f' m tm1.
Proof. intros. inv MemCPY.
  intros bb; intros.
     unfold Events.inject_separated in SEP.
     destruct (SEP _ _ _ H7 H8).
     split; intros XX.  
       apply H9. eapply Mem.storebytes_valid_block_1; eauto.
     assert (~ Mem.valid_block m2 bb).
       intros ZZ. apply H9. apply (bind_parameters_validblock_2 _ _ _ _ _ _ BP _ ZZ). 
       unfold Mem.inject in MINJ. destruct MINJ.
         rewrite (mi_freeblocks _ H11) in H8. inv H8.    
Qed.


Lemma MS_store_parameters_correct:
  forall e le te m1 params vl m2,
  bind_parameters ge e m1 params vl m2 ->
  forall s j cenv tf sp lo hi cs tm1 fn k,
  vars_vals_match j params vl te ->
  list_norepet (List.map variable_name params) ->
  Mem.inject j m1 tm1 ->
  match_callstack prog j m1 tm1 (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m1) (Mem.nextblock tm1) ->
  store_parameters cenv params = OK s ->
  exists j', exists tm2,
     corestep_star CMin_core_sem tge (CMin_State fn s k (Vptr sp Int.zero) te) tm1
                 (CMin_State fn Sskip k (Vptr sp Int.zero) te) tm2
  /\ Mem.inject j' m2 tm2
  /\ match_callstack prog j' m2 tm2 (Frame cenv tf e le te sp lo hi :: cs) (Mem.nextblock m2) (Mem.nextblock tm2)
  /\ inject_incr j j'
  /\ Events.inject_separated j j' m1 tm1.
Proof.
  induction 1.
  (* base case *)
  intros; simpl. monadInv H3.
  exists j; exists tm1. split. eapply corestep_star_zero.
       split; trivial.
       split; trivial.
       split; trivial. apply inject_separated_same_meminj.
  (* scalar case *)
  intros until k.  intros VVM NOREPET MINJ MATCH STOREP.
  monadInv STOREP. inv VVM. inv NOREPET.
  exploit MS_var_set_self_correct_scalar; eauto.
    econstructor; eauto. econstructor; eauto.
  intros [tm2 [EXEC1 [MINJ1 MATCH1]]].
  exploit IHbind_parameters; eauto.
  intros [f' [tm3 [EXEC2 [MINJ2 [MATCH2 [INCR2 SEP2]]]]]].
  exists f'; exists tm3.
  split. eapply corestep_star_trans; eauto.
  assert (X:= bind_parameters_inject_separated_skalar _ _ _ _ _ _ _ _ _ tm1 _ _ _ _ _ H1 H2 MINJ2 SEP2).
  auto.        
  (* array case *)
  intros until k.  intros VVM NOREPET MINJ MATCH STOREP.
  monadInv STOREP. inv VVM. inv NOREPET.
  exploit MS_var_set_self_correct_array; eauto.
  intros [f2 [tm2 [EXEC1 [MINJ1 [MATCH1 INCR1]]]]].
  exploit IHbind_parameters. eapply vars_vals_match_incr; eauto. auto. eauto. eauto. eauto. 
  intros [f3 [tm3 [EXEC2 [MINJ2 [MATCH2 [INCR2 SEP2]]]]]].
  exists f3; exists tm3.
  split. eapply corestep_star_trans; eauto.
  split. auto. split. auto. 
  split. eapply inject_incr_trans; eauto.
  assert (X:= bind_parameters_inject_separated_array _ _ _ _ _ _ _ _ _ _ _ H0 H1).
    clear MATCH H9 H10 EXEC1 EXEC2 MATCH1 MATCH2.
   assert (ZZ: Events.inject_separated f2 f3 m tm1).
        eapply X; eassumption.
        eapply X. eassumption.
(*   eapply X. apply  _ _ _ _ _ _ _ _ _ tm1 _ _ _ _ _ _ H0 H1). MINJ2 SEP2).
  intros bb; intros. 
  auto.        
  *)
Admitted. (* inject-separated*)

Lemma MS_function_entry_ok:
  forall fn m e m1 vargs m2 j cs tm cenv tf tm1 sp tvargs s fn' k,
  list_norepet (fn_params_names fn ++ fn_vars_names fn) ->
  alloc_variables empty_env m (fn_variables fn) e m1 ->
  bind_parameters ge e m1 fn.(Csharpminor.fn_params) vargs m2 ->
  match_callstack prog j m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  build_compilenv gce fn = (cenv, tf.(fn_stackspace)) ->
  tf.(fn_stackspace) <= Int.max_unsigned ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm1, sp) ->
  let tparams := List.map for_var (fn_params_names fn) in
  let tvars := List.map for_var (fn_vars_names fn) in
  let ttemps := List.map for_temp (Csharpminor.fn_temps fn) in
  let te := set_locals (tvars ++ ttemps) (set_params tvargs tparams) in
  val_list_inject j vargs tvargs ->
  Mem.inject j m tm ->
  store_parameters cenv fn.(Csharpminor.fn_params) = OK s ->
  exists j', exists tm2,
     corestep_star CMin_core_sem tge (CMin_State fn' s k (Vptr sp Int.zero) te) tm1
                                 (CMin_State fn' Sskip k (Vptr sp Int.zero) te) tm2
  /\ Mem.inject j' m2 tm2
  /\ inject_incr j j'
  /\ Events.inject_separated j j' m tm
  /\ match_callstack prog j' m2 tm2
       (Frame cenv tf e empty_temp_env te sp (Mem.nextblock m) (Mem.nextblock m1) :: cs)
       (Mem.nextblock m2) (Mem.nextblock tm2).
Proof.
  intros.
  exploit match_callstack_alloc_variables; eauto.
  intros [j1 [INCR1 [MINJ1 MATCH1]]].
  exploit vars_vals_match_holds.
    eexact H. 
    apply val_list_inject_incr with j. eauto. eauto.
    eapply bind_parameters_normalized; eauto.
  instantiate (1 := Csharpminor.fn_temps fn). 
  fold tvars. fold ttemps. fold (fn_params_names fn). fold tparams. fold te.   
  intro VVM.
  exploit MS_store_parameters_correct.
    eauto. eauto. eapply list_norepet_append_left; eauto.
    eexact MINJ1. eexact MATCH1. eauto.
  intros [j2 [tm2 [EXEC [MINJ2 [MATCH2 [INCR2 SEP2]]]]]].
  exists j2; exists tm2. 
  split; eauto. split; auto. split; auto. eapply inject_incr_trans; eauto.
  split; eauto. admit. (*inject -separated*)
Qed.


Lemma MS_step_case_InternalCall:
forall cenv  f j m tm e cs k tk vargs targs x m1 m2
(Param: list_norepet (fn_params_names f ++ fn_vars_names f))
(AllocVars : alloc_variables empty_env m (fn_variables f) e m1)
(BindParams : bind_parameters ge e m1 (Csharpminor.fn_params f) vargs m2)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm cs (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk (fn_return f) cenv nil cs)
(ISCC: Csharpminor.is_call_cont k)
(ARGSINJ : val_list_inject j vargs targs)
(EQ : transl_function gce f = OK x),
exists c2' : CMin_core,
  exists m2' : mem,
       corestep_plus CMin_core_sem tge (CMin_Callstate (AST.Internal x) targs tk) tm c2' m2' /\
  exists j' : meminj,
        inject_incr j j' /\
        Events.inject_separated j j' m tm /\
  exists c',
        inj_match_states_star unit match_cores MC_measure (tt,c') j'
           (CSharpMin_State f (Csharpminor.fn_body f) k e empty_temp_env) m2 c2' m2'.
Proof. intros.
  generalize EQ; clear EQ; unfold transl_function.
  caseEq (build_compilenv gce f). intros ce sz BC.
  destruct (zle sz Int.max_unsigned); try congruence.
  intro TRBODY.
  generalize TRBODY; intro TMP. monadInv TMP.
  set (tf := mkfunction (Csharpminor.fn_sig f) 
                        (List.map for_var (fn_params_names f))
                        (List.map for_var (fn_vars_names f)
                         ++ List.map for_temp (Csharpminor.fn_temps f))
                        sz
                        (Sseq x1 x0)) in *.
  caseEq (Mem.alloc tm 0 (fn_stackspace tf)). intros tm' sp ALLOC'.
  exploit MS_function_entry_ok; eauto; simpl; auto.  
  intros [j' [tm2 [EXEC [MINJ2 [IINCR [SEP MCS2]]]]]].
  eexists; eexists; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor; simpl; eauto. reflexivity.  
    simpl.
    eapply corestep_star_trans.
      eapply corestep_star_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
    simpl.
    eapply corestep_star_trans. apply EXEC.
      simpl. eapply corestep_star_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
  simpl in *.
  exists j'.
  split. assumption.
  split. assumption.
  exists (CSharpMin_State f(Csharpminor.fn_body f) k e empty_temp_env).
  left.
  econstructor. eexact TRBODY. eauto. eexact MINJ2. 
  eexact MCS2.
  inv MK; simpl in ISCC; contradiction || econstructor; eauto.
Qed.

Lemma MS_step: forall (c1 : CSharpMin_core) (m1 : mem) (c1' : CSharpMin_core) (m1' : mem),
corestep CSharpMin_CompcertCoreSem ge c1 m1 c1' m1' ->
forall (dc : inj_star_data core_data) (c2 : CMin_core) (j : meminj)
  (m2 : mem),
inj_match_states_star core_data match_cores MC_measure dc j c1 m1 c2 m2 ->
exists c2' : CMin_core,
  exists m2' : mem,
    exists dc' : inj_star_data core_data,
      exists j' : meminj,
        inject_incr j j' /\
        Events.inject_separated j j' m1 m2 /\
        inj_match_states_star core_data match_cores MC_measure dc' j' c1' m1'
          c2' m2' /\
        (corestep_plus CMin_CompcertCoreSem tge c2 m2 c2' m2' \/
         corestep_star CMin_CompcertCoreSem tge c2 m2 c2' m2' /\
         inj_star_ord core_data MC_order MC_measure dc' dc).
Proof.
  intros. destruct dc as [DATA CORE]. subst. unfold core_data in *. destruct DATA.
   destruct (CSharpMin_corestep_2_CompCertStep _ _ _ _ _ H) as [t Ht]. simpl in *.
  apply CSharpMin_corestep_not_at_external in H.
destruct H0.
   apply MC_matchstates in H0. rename H0 into MSTATE.
   inv Ht; simpl in *.
  (*skip seq*)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3. 
      inv MSTATE; simpl in *. 
      monadInv TR.
      destruct c2; simpl in *; try inv H8. 
      destruct (MS_step_case_SkipSeq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF MINJ MK MCS) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*skip Block*)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3. 
      inv MSTATE; simpl in *. 
      monadInv TR.
      destruct c2; simpl in *; try inv H8. 
      destruct (MS_step_case_SkipBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF MINJ MK MCS) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*skip Call*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE; simpl in *. 
      monadInv TR.
      destruct c2; simpl in *; try inv H11.
      destruct (MS_step_case_SkipCall  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H3 H5 TRF MINJ MK MCS) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
   (*assign*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H10.
      rename  m1' into m'. rename m1 into m. rename m2 into tm. rename k0 into tk. rename f0 into tfn. rename e0 into te.
      destruct (MS_step_case_Assign  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H4 TRF MINJ MK MCS EQ EQ0) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
   (*set*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H9.
      destruct (MS_step_case_Set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ id H3 TRF MINJ MCS MK EQ) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
   (*store*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H11. rename f0 into tfn. rename m1 into m. rename m2  into tm. rename e0 into te. rename k0 into tk. rename  m1' into m'.
      destruct (MS_step_case_Store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 H2 H3 TRF MINJ MCS MK EQ EQ1) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
   (*call*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H11. 
      rename f into fd. rename f0 into f. rename f1 into tfn.
      rename m1' into m. rename m2  into tm. rename e into te.
      rename e0 into e.  rename k0 into tk. rename  le0 into le.
      destruct (MS_step_case_Call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ optid _ _ H2 H3 H4 TRF MINJ MCS MK EQ EQ1) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
   (*builtin*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H10. 
      rename f0 into tfn. 
      rename m1 into m. rename m2  into tm. rename e into te.
      rename e0 into e.  rename k0 into tk. rename  le0 into le.  rename m1' into m'.
      destruct (MS_step_case_Builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ optid _ _ _ _ H2 H4 TRF MINJ MCS MK EQ) as [c2' [m2' [cstepPlus [j' [InjIncr [InjSep [c' MS]]]]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j'. auto.
  (* seq *)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3. 
     rename k0 into k.
      inv MSTATE. 
      (*Case 1*) 
         monadInv TR.
         destruct c2; simpl in *; try inv H8.
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
         exists  (CMin_State tfn x (Kseq x0 tk) (Vptr sp Int.zero) te). exists m2. 
         exists (tt,CSharpMin_State f s (Csharpminor.Kseq s2 k) e le).
         exists j. 
                split. apply inject_incr_refl.
                split. apply inject_separated_same_meminj.
                split; left; simpl. 
                     econstructor; eauto.
                          econstructor; eauto.
                     apply corestep_plus_one. eapply CompCertStep_CMin_corestep.  econstructor. reflexivity.
       (* seq 2 *)
          exists c2. exists m2. exists (tt,CSharpMin_State f s (Csharpminor.Kseq s2 k) e le). exists j.
                split. apply inject_incr_refl.
                split. apply inject_separated_same_meminj. 
                destruct  c2; simpl in *; inv H9.
                split.  left. econstructor; try eassumption.
                   right. split. apply corestep_star_zero.
simpl. eapply lex_ord_right. simpl. unfold ltof. (*unfold MC_measure. simpl. *) admit. (*CORE is unconstrained!?*)
(* ifthenelse *)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H10. 
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm. 
      destruct (MS_step_case_Ite _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H4 TRF MINJ MCS MK EQ EQ1 EQ0) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*loop*)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H8. 
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm. 
      destruct (MS_step_case_Loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF MINJ MCS MK EQ) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*block*)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H8. 
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm.  rename s0 into s.
      destruct (MS_step_case_Block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF MINJ MCS MK EQ) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*exit seq*)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H8. 
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm.
      destruct (MS_step_case_ExitSeq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ TRF MINJ MCS MK) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*exit block 0*)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H8. 
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm.
      destruct (MS_step_case_ExitBlockZero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF MINJ MCS MK) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*exit block n+1*)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H8. 
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm.
      destruct (MS_step_case_ExitBlockNonzero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n TRF MINJ MCS MK) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*switch*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H9. 
         rename f0 into tfn.  rename e0 into te.
         rename k0 into tk. rename m1' into m. rename m2  into tm.  rename s into ts.
      destruct (MS_step_case_Switch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 TRF MINJ MCS MK EQ EQ0) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*return none*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H9. 
       rename f into tfn.  rename f0 into f. rename e into te. rename e0 into e.
         rename k0 into tk. rename m1 into m. rename m2  into tm. rename m1'  into m'.  rename le0 into le.
      destruct (MS_step_case_ReturnNone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 TRF MINJ MCS MK) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*return some*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H10. 
       rename f into tfn.  rename f0 into f. rename e into te. rename e0 into e. rename k into tk.
         rename k0 into k. rename m1 into m. rename m2  into tm. rename m1'  into m'.  rename le0 into le. rename v0 into v.
      destruct (MS_step_case_ReturnSome _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H4 TRF MINJ MCS MK EQ) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*label*)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H8. 
       rename f0 into tfn. rename e0 into te. 
         rename k0 into tk. rename m1' into m. rename m2  into tm. rename s0 into s.  
      destruct (MS_step_case_Label _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lbl _ _ TRF MINJ MCS MK EQ) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*goto*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H9. 
       rename f0 into tfn. rename e0 into te. 
         rename k1 into tk. rename s into s'.  rename k into k'. rename k0 into k. rename m1' into m. rename m2  into tm.
      destruct (MS_step_case_Goto _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 TRF MINJ MCS MK) as [c2' [m2' [cstepPlus [c' MS]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.

(* internal call *)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H9. 
      rename m1 into m. rename m2 into tm. rename f0 into f. rename e0 into e.
      rename m0 into m1. rename args into vargs. rename m1' into m2.
      rename k0 into tk. rename args0 into targs. 
      destruct (MS_step_case_InternalCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H3 H5 MINJ MCS MK ISCC ARGSINJ EQ) as [c2' [m2' [cstepPlus [j' [InjIncr [InjSep [c' MS]]]]]]].
      exists c2'. exists m2'. exists (tt,c'). exists j'. auto.
(* external call *)
  inv MSTATE. monadInv TR. rename f into j.
  destruct (transl_step_case_ExternalCall _ _ _ _ _ _ _ _ _ _ _ _ _ H MINJ MCS MK ISCC ARGSINJ) as [T2 [Steps [j' [Inc MSI]]]].
   apply matchInj_Elim in MSI. eauto.

(* return *)
  inv MSTATE. rename f0 into j.
  destruct (transl_step_case_Return _ _ _ _ _ _ _ _ _ _ _ _ tv optid MINJ MCS MK RESINJ) as [T2 [Steps MSI]].
   apply matchInj_Elim in MSI. eauto.
Qed.
       unfold core_data in *. destruct DATA.
       eapply MC_matchstates in H0.
       rewrite (MC_atExt _ _ _ _ H0) in H.
       destruct (transl_step_correct _ _ TRANSL _ _ _ Ht _ H0) as [[T2 [SPlus X]] | X]. 
           destruct (CompCertStepPlus_2_CMin_corestepPlus _ _ _ _ _ SPlus H) as [c2' [m2' [? CMinPlus]]]; subst.
           apply MC_matchcores in X. destruct X as [j' Hj'].
           exists c2'. exists m2'. exists (tt,CORE). exists j'.
             split. admit. (*not satisfied - we actuall have to redo the proof of transl_step_correct for this reason! -- j/j' are hidden*)
             split . admit. (*same here*)
             split; left; assumption.
        destruct X as [MEAS [X  MSP]]. subst. 
           apply MC_matchcores in MSP. destruct MSP as [j' Hj'].
           exists c2. exists m2. exists (tt,c1'). exists j'.
             split. admit. (*not satisfied - we actuall have to redo the proof of transl_step_correct for this reason! -- j/j' are hidden*)
             split . admit. (*same here*)
             split. simpl. left; assumption.
             right. split. exists O.  reflexivity. 
             simpl. admit (*.. measure stuff . *).
  destruct H0. 
       unfold core_data in *. destruct DATA.
       eapply MC_matchstates in H1.
       rewrite (MC_atExt _ _ _ _ H1) in H.
       destruct (transl_step_correct _ _ TRANSL _ _ _ Ht _ H0) as [[T2 [SPlus X]] | X]. 
           destruct (CompCertStepPlus_2_CMin_corestepPlus _ _ _ _ _ SPlus H) as [c2' [m2' [? CMinPlus]]]; subst.
           apply MC_matchcores in X. destruct X as [j' Hj'].
           exists c2'. exists m2'. exists (tt,CORE). exists j'.
             split. admit. (*not satisfied - we actuall have to redo the proof of transl_step_correct for this reason! -- j/j' are hidden*)
             split . admit. (*same here*)
             split; left; assumption.
        destruct X as [MEAS [X  MSP]]. subst. 
           apply MC_matchcores in MSP. destruct MSP as [j' Hj'].
           exists c2. exists m2. exists (tt,c1'). exists j'.
             split. admit. (*not satisfied - we actuall have to redo the proof of transl_step_correct for this reason! -- j/j' are hidden*)
             split . admit. (*same here*)
             split. simpl. left; assumption.
             right. split. exists O.  reflexivity. 
             simpl. admit (*.. measure stuff . *).
      
    unfold core_data in *. destruct X as [MEAS [TRACE MS]]. subst.
      destruct (transl_step_correct _ _ TRANSL _ _ _ Ht _ H0) as [[T2 [SPlus X]] | X]. 
      rewrite (MC_atExt _ _ _ _ H0) in H.
      destruct (CompCertStepPlus_2_CMin_corestepPlus _ _ _ _ _ SPlus H) as [c2' [m2' [? CMinPlus]]]; subst.
      apply MC_matchcores in X. destruct X as [j' Hj'].
      exists c2'. exists m2'. exists (tt,CORE). exists j'.
        split. admit. (*not satisfied - we actuall have to redo the proof of transl_step_correct for this reason! -- j/j' are hidden*)
        split . admit. (*same here*)
        split; left; assumption.
         
  
        left. assumption.
 
        exis unfold inj_star_data. unit. exists tt. 
       
 xx CompCertStepStar_2_corestepstar in SPlus.
            admit.
          destruct (CompCertStep_2_corestep _ _ _ _ _ Ht H) as [q' [m' [? MinStep]]]. clear Ht.
          apply CSharpMin_core2state_injective in H1. destruct H1; subst.   (*We can't simply left Cminor_CompCertsemantics.CompCertStep_corestep
                         to plus, since we have no guarantee that all intermediate steps in assumption X
                         satisfy atExternal = None.
                         I believe they do
        simpl in X.
   inv H0; simpl in *.
     eapply MC_matchstates in MCS.
    assert (ZZ:= MC_matchstates _ _ _ _ _ _ _ MCS).
(*   destruct c1; destruct c1'. simpl in H.*)
   destruct (corestep_CompCertStep ge (CSharpMin_State f s k e le) m1 (CSharpMin_State f0 s0 k0 e0 le0) m1' H) as [t Ht]. simpl in *.
   assert (X:= transl_step_correct _ _ TRANSL _ _ _ Ht). simpl in X.
   inv H0; simpl in *. Focus 2.
   inv H. simpl in *.
       inv H1. simpl in *.
          destruct H0. simpl in H. exists c2. exists m2.   destruct H. inv H. 
   generalize dependent dc. generalize dependent j.  generalize dependent m2.  generalize dependent c2.
   (*State State*)  admit.
   (*State CallState*)  admit.
   (*State ReturnState*) admit.
   (*Callstate State*) admit.
   (*Returnstate*)
        simpl in *. induction H. inv H.
  unfold corestep  in H. simpl in *. unfold CSharpMin_corestep in H. inv H. induction H.  
Admitted.


Lemma Csharpminor_Cminor_sim_inj: forall entrypoints
(*              ExternIdents  (ext_ok : CompilerCorrectness.entryPts_ok p p ExternIdents entrypoints),*),
              Sim_inj.Forward_simulation_inject _ _ CSharpMin_CompcertCoreSem CMin_CompcertCoreSem
                  ge tge entrypoints.
Proof.
  intros. eapply inj_simulation_star with ( match_state := match_cores)(order:=MC_order)(measure:=MC_measure).
   apply MC_wellfounded.
   intros. eapply init_cores; eauto.
   apply MC_safely_halted.
   eapply MC_at_external; eauto.
    Focus 4.
