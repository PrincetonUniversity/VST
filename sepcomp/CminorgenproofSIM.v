Require Export Axioms.
Require Import Errors.
Require Import Events.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Import Globalenvs.
Require Export Maps.

Require Import Csharpminor.
Require Import Cminor.
(*Require Import veric.Cminor_CompcertSemantics.
Require Import veric.CSharpminor_CompcertSemantics.*)
Require Import sepcomp.Cminor_coop.
Require Import sepcomp.Csharpminor_coop.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import Cminorgen.
Require Import sepcomp.CminorgenproofRestructured.

Require Import Coq.Program.Equality.

Lemma allocvars_blocks_valid: forall vars E m e m1,
 alloc_variables E m vars e m1 -> 
 forall b, Mem.valid_block m b -> Mem.valid_block m1 b.
Proof.
  intros. induction H; simpl in *.  assumption.
  apply IHalloc_variables. eapply Mem.valid_block_alloc; eauto. 
Qed.

Lemma storev_valid_block_1:
forall ch m addr v m', 
Mem.storev ch m addr v = Some m' -> 
(forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof. intros. destruct addr; inv H. eapply Mem.store_valid_block_1; eauto. Qed.

Lemma storev_valid_block_2:
forall ch m addr v m', 
Mem.storev ch m addr v = Some m' -> 
(forall b, Mem.valid_block m' b -> Mem.valid_block m b).
Proof. intros. destruct addr; inv H. eapply Mem.store_valid_block_2; eauto. Qed.

Section TRANSLATION.
Variable prog: Csharpminor.program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: transl_program prog = OK tprog.
Let ge : Csharpminor.genv := Genv.globalenv prog.
(*Let gce : compilenv := build_global_compilenv prog.*)
Let tge: genv := Genv.globalenv tprog.

Let core_data := CSharpMin_core.

Inductive match_cores: core_data -> meminj -> CSharpMin_core -> mem -> CMin_core -> mem -> Prop :=
  | MC_states:
      forall d fn s k e le m tfn ts tk sp te tm cenv xenv j lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s = OK ts)
      (MINJ: Mem.inject j m tm)
      (MCS: match_callstack prog j m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk  cenv xenv cs),
      match_cores d j (CSharpMin_State fn s k e le) m
                   (CMin_State tfn ts tk (Vptr sp Int.zero) te) tm
  | MC_state_seq:
      forall d fn s1 s2 k e le m tfn ts1 tk sp te tm cenv xenv j lo hi cs sz
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s1 = OK ts1)
      (MINJ: Mem.inject j m tm)
      (MCS: match_callstack prog j m tm
               (Frame cenv tfn e le te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont (Csharpminor.Kseq s2 k) tk cenv xenv cs),
      match_cores d j (CSharpMin_State fn (Csharpminor.Sseq s1 s2) k e le) m
                   (CMin_State tfn ts1 tk (Vptr sp Int.zero) te) tm
  | MC_callstate:
      forall d fd args k m tfd targs tk tm j cs cenv
      (TR: transl_fundef fd = OK tfd)
      (MINJ: Mem.inject j m tm)
      (MCS: match_callstack prog j m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (ISCC: Csharpminor.is_call_cont k)
      (ARGSINJ: val_list_inject j args targs)

(*LENB: added the following 2 conditions , to enable a proof of sim.at_external.
  Really, the first one should suffice (since the second one should follow from the first one and  
   (ARGSINJ: val_list_inject j args targs). Maybe we should add a (boolean-valued version of)
     these conditions in CSharpminor_CompcertSemantics.CSharpMin_at_external, and
     similarly for Cminor?*)
     (ARGSTYP: Forall2 Val.has_type args (Csharpminor.funsig fd).(sig_args))
     (TARGSTYP: Forall2 Val.has_type targs (Csharpminor.funsig fd).(sig_args)),
 
      match_cores d j (CSharpMin_Callstate fd args k) m
                   (CMin_Callstate tfd targs tk) tm
  | MC_returnstate:
      forall d v k m tv tk tm j cs cenv
      (MINJ: Mem.inject j m tm)
      (MCS: match_callstack prog j m tm cs (Mem.nextblock m) (Mem.nextblock tm))
      (MK: match_cont k tk cenv nil cs)
      (RESINJ: val_inject j v tv),
      match_cores d j (CSharpMin_Returnstate v k) m
                   (CMin_Returnstate tv tk) tm.

(*Lenb -- lemma is new, and needed for the proof of
Theorem transl_program_correct at the end of this file*)
Lemma match_cores_valid: 
forall d j c1 m1 c2 m2,  match_cores d j c1 m1 c2 m2 -> 
          forall b1 b2 ofs, j b1 = Some(b2,ofs) -> 
               (Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2).
Proof.
intros.
inv H.
  split. eapply Mem.valid_block_inject_1; eassumption.
         eapply Mem.valid_block_inject_2; eassumption.
  split. eapply Mem.valid_block_inject_1; eassumption.
         eapply Mem.valid_block_inject_2; eassumption.
  split. eapply Mem.valid_block_inject_1; eassumption.
         eapply Mem.valid_block_inject_2; eassumption.
  split. eapply Mem.valid_block_inject_1; eassumption.
         eapply Mem.valid_block_inject_2; eassumption.
Qed.

Lemma init_cores: forall (v1 v2 : val) (sig : signature) entrypoints
(EP: In (v1, v2, sig) entrypoints)
  (vals1 : list val) (c1 : core_data) (m1 : mem) (j : meminj)
  (vals2 : list val) (m2 : mem)
  (CSM_Ini : initial_core CSharpMin_core_sem ge v1 vals1 = Some c1)
  (Inj : Mem.inject j m1 m2)
  (VI: Forall2 (val_inject j) vals1 vals2)
  (HT: Forall2 Val.has_type vals2 (sig_args sig)),
exists c2 : CMin_core,
  initial_core CMin_core_sem tge v2 vals2 = Some c2 /\
  match_cores c1 j c1 m1 c2 m2. 
Proof. intros.
  inversion CSM_Ini. unfold  CSharpMin_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0. apply eq_sym in Heqzz.
  (*
                   remember (Genv.find_symbol (Genv.globalenv prog) CSharpMin_MainIdent) as z; destruct z; try inv H0.
                   remember (Genv.find_funct_ptr  (Genv.globalenv prog) b) as zz; destruct zz; try inv H1. *)
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
 
  exists (CMin_Callstate tf nil Cminor.Kstop).
  specialize (sig_preserved _ _ TR). intros QQ.
  rewrite <- QQ in H1. simpl in *.
  remember (Int.eq_dec Int.zero Int.zero) as r.
  destruct r. Focus 2. exfalso. apply n. trivial.
  rewrite Heqzz in CSM_Ini.
  rewrite <- QQ in CSM_Ini. simpl in *.
  remember (funsig tf) as F.
  destruct F; try inv H1. 
  destruct sig_args; try inv H0.
  destruct sig_res; try inv H1.
  destruct t; inv H0.
   split. admit. (*Entrypoints not yet updated in Compcert*)
  eapply MC_callstate with (cenv:=PTree.empty _)(cs := @nil frame); try eassumption.
  apply mcs_nil with (Mem.nextblock m1). 
  (*apply match_globalenvs_init*)
  admit. (*CompCert's globalenvs not yet adapted to noninitial entry points*)
  xomega. 
  admit. (*CompCert's globalenvs not yet adapted to noninitial entry points
            so use of same hi in mcs_nil misleading*)
  econstructor. 
  simpl. trivial.
  simpl. constructor.
  rewrite <- QQ. simpl. constructor.
  rewrite <- QQ. simpl. constructor.
Qed.

(*
  rewrite <- TprogMain. unfold transl_program in TRANSL.
  econstructor; split.
      destruct CMin_core_sem. simpl. destruct csem. simpl. 
       econstructor.
       unfold make_initial_core.
  econstructor.
  apply (Genv.init_mem_transf_partial2 _ _ _ TRANSL). eauto. 
  simpl. fold tge. rewrite symbols_preserved.
  replace (prog_main tprog) with (prog_main prog). eexact H0.
  symmetry. unfold transl_program in TRANSL.
  eapply transform_partial_program2_main; eauto.
  eexact FIND. 
  rewrite <- H2. apply sig_preserved; auto.
  eapply match_callstate with (f := Mem.flat_inj (Mem.nextblock m0)) (cs := @nil frame).
  auto.
  eapply Genv.initmem_inject; eauto.
  apply mcs_nil with (Mem.nextblock m0). apply match_globalenvs_init; auto. omega. omega.
  instantiate (1 := gce). constructor.
  red; auto. constructor. 
(*
v1 v2 vals1 (c1 : CSharpMin_core) m1 j vals2 m2 
      sig
      (CSM_Ini : make_initial_core CSharpMin_core_sem ge v1 vals1 = Some c1)
      (Inj : Mem.inject j m1 m2)
      (VI: Forall2 (val_inject j) vals1 vals2)
      (HT: Forall2 Val.has_type vals2 (sig_args sig)),
exists cd : core_data,
  exists c2 : CMin_core,
    make_initial_core CMin_core_sem tge v2 vals2 = Some c2 /\
    match_cores cd j c1 m1 c2 m2.*)
Proof.
  intros. inv CSM_Ini. eexists. simpl. unfold CMin_make_initial_core. unfold tge.
        rewrite <- TprogMain. rewrite <- Heqz.
  unfold  CSharpMin_make_initial_core in H0.
                              remember (Genv.find_symbol ge CSharpMin_MainIdent) as z; destruct z; try inv H0.
                             rewrite <- ProgMain in Heqz. unfold ge in Heqz. unfold tge in Heqz.
                              rewrite <- (symbols_preserved _ _ TRANSL) in Heqz. 
                              remember (Genv.find_funct_ptr ge b) as zz; destruct zz; try inv H1. 
                              apply eq_sym in Heqzz.  unfold ge in Heqzz.
                              destruct (Genv.find_funct_ptr_transf_partial2 _ _  _ TRANSL b Heqzz) as [tf  [Htf TransF]].
                              remember (Csharpminor.funsig f) as fs; destruct fs.
                              destruct sig_args; try inv H0.
                              destruct sig_res; try inv H1.
                              destruct t; try inv H0.
(*  apply eq_sym in Heqzz.*)
  destruct (function_ptr_translated _ _ TRANSL _ _ Heqzz) as [tff [FIND TR]].
  rewrite FIND in Htf. inv Htf.  
    (*unfold core_data. exists (CSharpMin_Callstate f nil Csharpminor.Kstop).*)
   eexists.
  split.
  (*make_initial_core*)
      simpl. unfold CMin_make_initial_core. unfold tge.
        rewrite <- TprogMain. rewrite <- Heqz.
  rewrite (symbols_preserved _ _ TRANSL).
          rewrite 
          assert (Z:= sig_preserved _ _ _ TR). apply symbols_preserved; assumption.
      unfold ge in *. assert (ID: CMin_MainIdent = CSharpMin_MainIdent). admit. rewrite ID in *. 
              assert (X: Genv.find_symbol tge CSharpMin_MainIdent =  Genv.find_symbol (Genv.globalenv prog) CSharpMin_MainIdent).
                 apply symbols_preserved; assumption.
             rewrite <- Heqz in X. rewrite X. unfold tge in *. rewrite FIND. 
        rewrite (sig_preserved _ _ _ TR). rewrite <- Heqfs. reflexivity.
  (*match_cores*)
  eapply MC_callstate with (j := j) (cs := @nil frame); try eassumption.
     admit. (*some error here wrt initial mems*)
      econstructor.
      econstructor.
      econstructor.
      rewrite <- Heqfs. simpl. constructor.
      rewrite <- Heqfs. simpl. constructor.
(*   
     destruct Inj. clear HT VI vals1 vals2 Heqz Heqzz Heqfs FIND TR f tf. destruct mi_inj.
     apply mcs_nil with (Mem.nextblock m1). 
            
      apply match_globalenvs_init; auto. can't be right since memories are not necessarily initial
omega. omega.
  instantiate (1 := gce). constructor.
  red; auto. constructor.  econstructor.
          econstructor.*)*)

Lemma MC_safely_halted: forall (cd : core_data) (j : meminj) (c1 : CSharpMin_core) (m1 : mem)
  (c2 : CMin_core) (m2 : mem) (v1 : val),
match_cores cd j c1 m1 c2 m2 ->
halted CSharpMin_core_sem  c1 = Some v1 ->
exists v2,
halted CMin_core_sem c2 = Some v2 /\ Mem.inject j m1 m2 /\
val_inject j v1 v2.
Proof.
  intros.
  inv H; simpl in *; inv H0.
  destruct k; inv H1. exists tv.
  split.
         inv MK. trivial.
  split; trivial.
Qed.

Lemma MC_at_external: forall (cd : core_data) (j : meminj) (st1 : CSharpMin_core) (m1 : mem)
  (st2 : CMin_core) (m2 : mem) (e : external_function) (vals1 : list val) sig,
(cd = st1 /\ match_cores cd j st1 m1 st2 m2) ->
at_external CSharpMin_core_sem st1 = Some (e, sig, vals1) ->
Mem.inject j m1 m2 /\
Events.meminj_preserves_globals ge j /\
(exists vals2 : list val,
   Forall2 (val_inject j) vals1 vals2 /\
   Forall2 Val.has_type vals2 (sig_args sig) /\
   at_external CMin_core_sem st2 = Some (e, sig, vals2)).
Proof.
  intros. destruct H; subst.
  inv H1; simpl in *; inv H0.
  split; trivial.
  split. destruct (match_callstack_match_globalenvs _ _ _ _ _ _ _ MCS) as [hi Hhi].
              eapply inj_preserves_globals; eassumption.
  destruct fd; inv H1.
  exists targs.
  split. eapply val_list_inject_forall_inject; eassumption.
  inv TR.
  split; trivial.
Qed.

Lemma MC_after_external:forall (d : core_data) (j j' : meminj) (st1 : core_data) (st2 : CMin_core)
  (m1 : mem) (e : external_function) (vals1 : list val) (ret1 : val)
  (m1' m2 m2' : mem) (ret2 : val) (sig : signature),
d = st1 /\ match_cores d j st1 m1 st2 m2 ->
at_external CSharpMin_core_sem st1 = Some (e, sig, vals1) ->
Events.meminj_preserves_globals ge j ->
inject_incr j j' ->
Events.inject_separated j j' m1 m2 ->
Mem.inject j' m1' m2' ->
val_inject j' ret1 ret2 ->
mem_forward m1 m1' ->
Mem.unchanged_on (Events.loc_unmapped j) m1 m1' ->
mem_forward m2 m2' ->
Mem.unchanged_on (Events.loc_out_of_reach j m1) m2 m2' ->
Val.has_type ret2 (proj_sig_res sig) ->
exists st1' : core_data,
  exists st2' : CMin_core,
    exists d' : core_data,
      after_external CSharpMin_core_sem (Some ret1) st1 = Some st1' /\
      after_external CMin_core_sem (Some ret2) st2 = Some st2' /\
      d' = st1' /\ match_cores d' j' st1' m1' st2' m2'. 
Proof. intros.
  destruct (MC_at_external _ _ _ _ _ _ _ _ _ H H0) as [_ [_ [vals2 [ValsInj [vals2Typ AtExt2]]]]].
  destruct H as [X MC]; subst.
  inv MC; simpl in *; inv H0.
  destruct fd; inv H11.
  destruct tfd; inv AtExt2.
  exists (CSharpMin_Returnstate ret1 k). eexists. eexists.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
  simpl in *.
  econstructor; try eassumption.
  clear TR H11.
  destruct k; simpl in *; try contradiction. (*cases k = Kseq and k=Kblock eliminated*)
  (*k=Kstop*) 
      inv MK; simpl in *.   
      apply match_callstack_incr_bound with (Mem.nextblock m1) (Mem.nextblock m2).
      eapply match_callstack_external_call; eauto.
          intros. eapply H6; eauto.
          xomega.
          xomega.
         eapply forward_nextblock; assumption.
         eapply forward_nextblock; assumption.
  (*k=Kcall*) 
      inv MK; simpl in *.   
      apply match_callstack_incr_bound with (Mem.nextblock m1) (Mem.nextblock m2).
      eapply match_callstack_external_call; eauto.
          intros. eapply H6; eauto.
          xomega.
          xomega.
         eapply forward_nextblock; assumption.
         eapply forward_nextblock; assumption.
Qed.

Lemma MC_MSI: forall d j
       q m q' m',
      match_cores d j q m q' m' -> 
      match_statesInj prog j  (ToState q m) (Cminor_coop.ToState q' m').
  Proof. intros.
    inv H; simpl in *.
     eapply matchInj_state; try eassumption. 
     eapply matchInj_state_seq; try eassumption. 
     eapply matchInj_callstate; try eassumption. 
     eapply matchInj_returnstate; try eassumption.
Qed.  

Lemma MSI_MC: forall j q m q' m' d,
      match_statesInj prog j (ToState q m) (Cminor_coop.ToState q' m') ->
      match_cores d j q m q' m'.
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

Lemma MSI_atExt: forall j c1 m1 c2 m2
(H: match_statesInj prog j (ToState c1 m1) (Cminor_coop.ToState c2 m2) ),
(CSharpMin_at_external c1 = None) = (CMin_at_external c2 = None).
Proof.
  intros.
  destruct c1; destruct c2; inv H; simpl in *; trivial.
  destruct f; destruct f0; simpl in *; trivial.
   apply bind_inversion in TR. destruct TR as [z [ZZ1 ZZ2]]; subst.
  inv ZZ2.
  inv TR.
  inv TR.
  apply prop_ext. split; intros; inv H. 
Qed.

Parameter MC_order :  core_data -> core_data -> Prop. 
Parameter MC_wellfounded: well_founded MC_order.
Definition MC_measure (q:CSharpMin_core): nat :=
  match q with
  | CSharpMin_State fn s k e lenv => seq_left_depth s
  | _ => O
  end.
(*Parameter MC_measure: CSharpMin_core-> nat.*)

Lemma MS_step_case_SkipSeq:
forall cenv sz f tfn j m tm  e lenv te sp lo hi cs s k tk xenv
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MK : match_cont (Csharpminor.Kseq s k) tk cenv xenv cs)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn Sskip tk (Vptr sp Int.zero) te) tm c2' m2' /\
        match_cores (CSharpMin_State f s k e lenv) j (CSharpMin_State f s k e lenv) m c2' m2'.
(*   exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f s k e lenv) m c2' m2'.*)
Proof. intros.
  dependent induction MK.

  eexists. eexists. 
  split.
    apply corestep_plus_one. 
        eapply CompCertStep_CMin_corestep'.  simpl.  econstructor. reflexivity.
  simpl. (* exists (CSharpMin_State f s k e le).
     left. *) eapply MC_states; eauto.
 
  eexists. eexists.
  split.
    apply corestep_plus_one. 
        eapply CompCertStep_CMin_corestep'.  simpl.  econstructor. reflexivity.
   simpl. (*exists (CSharpMin_State f (Csharpminor.Sseq s1 s2) k e le).
      left.  *) eapply MC_state_seq; eauto.

  exploit IHMK; eauto. clear IHMK.  intros [T2 [m2 [A C]]].
  exists T2; exists m2.
  split.
     eapply corestep_star_plus_trans.
        apply corestep_star_one.  eapply CompCertStep_CMin_corestep'.  simpl.  constructor. reflexivity.
        simpl. apply A. 
  apply C.
Qed.

Lemma MS_step_case_SkipBlock: 
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv 
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MK : match_cont (Csharpminor.Kblock k) tk cenv xenv cs)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn Sskip tk (Vptr sp Int.zero) te) tm c2' m2' /\
         match_cores  (CSharpMin_State f Csharpminor.Sskip k e lenv)   j (CSharpMin_State f Csharpminor.Sskip k e lenv) m c2' m2'
(*exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f Csharpminor.Sskip k e le) m c2' m2'*).
Proof. intros.
  dependent induction MK.

  eexists. eexists. 
  split.
    apply corestep_plus_one. 
        eapply CompCertStep_CMin_corestep'.  simpl. constructor. reflexivity.  
   simpl. (*exists (CSharpMin_State f Csharpminor.Sskip k e le).
      left.  *) eapply MC_states; eauto.

  exploit IHMK; eauto. clear IHMK.  intros [T2 [m2 [A C]]].
  exists T2; exists m2.
  split.
     eapply corestep_star_plus_trans.
        apply corestep_star_one.  eapply CompCertStep_CMin_corestep'.  simpl.  constructor. reflexivity.
        simpl. apply A. 
  (* simpl in *. exists c'.*) apply C.
Qed.

Lemma MS_match_is_call_cont:
  forall tfn te sp tm k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  Csharpminor.is_call_cont k ->
  exists tk',
    corestep_star CMin_core_sem tge (CMin_State tfn Sskip tk sp te) tm
                (CMin_State tfn Sskip tk' sp te) tm
    /\ is_call_cont tk'
    /\ match_cont k tk' cenv nil cs.
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
 forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv m'
(CC: Csharpminor.is_call_cont k)
(FL: Mem.free_list m (blocks_of_env e) = Some m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MK : match_cont k tk cenv xenv cs)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State  tfn Sskip tk (Vptr sp Int.zero) te) tm c2' m2' /\
         match_cores  (CSharpMin_Returnstate Vundef k)  j (CSharpMin_Returnstate Vundef k) m' c2' m2'.
(*exists c' : CSharpMin_core,
       inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_Returnstate Vundef k) m' c2' m2'.*)
Proof. intros.
  exploit MS_match_is_call_cont; eauto. intros [tk' [A [B C]]]. 
  exploit match_callstack_freelist; eauto. intros [tm' [P [Q R]]].

  eexists. eexists.
  split.
    eapply corestep_star_plus_trans. eexact A. apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. apply step_skip_call. assumption. 
      eauto.
    eauto.
    econstructor; eauto.

Qed.

Lemma MS_step_case_Assign:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv  x a x0 v id
(EE:Csharpminor.eval_expr ge e lenv m a v)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MK : match_cont k tk cenv xenv cs)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(EQ : transl_expr cenv a = OK (x, x0)),
exists c2' : CMin_core,
  exists m2' : mem,
    corestep_plus CMin_core_sem tge
     (CMin_State tfn (Sassign id x) tk (Vptr sp Int.zero) te) tm c2' m2' /\
   match_cores
     (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)) j
     (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)) m c2'
     m2'.
(*  exists c' : CSharpMin_core,
       inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f Csharpminor.Sskip k e lenv) m' c2' m2'.*)
Proof. intros.
 intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
(*
  exploit var_set_correct; eauto. 
  intros [te' [tm' [EXEC [MINJ' [MCS' OTHER]]]]].
*)
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. 
         econstructor. eassumption. reflexivity.
inv MCS.
  econstructor; eauto.
econstructor; eauto.
eapply match_temps_assign; assumption.
Qed.


(*no case set in ocmpCert 2.0
Lemma MS_step_case_Set:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv x x0 v a id
(H: Csharpminor.eval_expr ge e lenv m a v)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk (fn_return f) cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State  tfn (Sassign (for_temp id) x) tk (Vptr sp Int.zero) te) tm c2' m2' /\
       match_cores (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)) j 
          (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)) m c2' m2' .
(*  exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j 
          (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)) m c2' m2' .*)
Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. econstructor; eauto.  reflexivity.
  simpl in *.
  econstructor; eauto.
  apply (match_callstack_set_temp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ id _ _ VINJ MCS).
(*  exists (CSharpMin_State f Csharpminor.Sskip k e (PTree.set id v lenv)).
    left. econstructor; eauto.*)
Qed.
*)
Lemma MS_step_case_Store:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv x x0 x1 x2 
      chunk m' a addr vaddr v
(CH: Mem.storev chunk m vaddr v = Some m')
(EvAddr : Csharpminor.eval_expr ge e lenv m addr vaddr)
(EvA : Csharpminor.eval_expr ge e lenv m a v)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
                (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_expr cenv addr = OK (x, x0))
(EQ1 : transl_expr cenv a = OK (x1, x2)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State  tfn (make_store chunk x x1) tk (Vptr sp Int.zero) te) tm c2' m2' /\
        match_cores (CSharpMin_State f Csharpminor.Sskip k e lenv) j 
                      (CSharpMin_State f Csharpminor.Sskip k e lenv) m' c2' m2' .
(* exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j 
                      (CSharpMin_State f Csharpminor.Sskip k e lenv) m' c2' m2' .*)
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
  inv VINJ1; simpl in CH; try discriminate.
  econstructor; eauto. 
  rewrite (Mem.nextblock_store _ _ _ _ _ _ CH).
  rewrite (Mem.nextblock_store _ _ _ _ _ _ STORE').
  eapply match_callstack_invariant (*with f0 m tm*); eauto.
  intros. eapply Mem.perm_store_2; eauto. 
  intros. eapply Mem.perm_store_1; eauto.
Qed. 


Lemma MS_step_case_Call:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv  x x0 x1 a vf fd optid vargs bl
(EvalA: Csharpminor.eval_expr ge e lenv m a vf)
(EvalBL: Csharpminor.eval_exprlist ge e lenv m bl vargs)
(FF: Genv.find_funct ge vf = Some fd)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0))
(EQ1 : transl_exprlist cenv bl = OK x1),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge 
             (CMin_State  tfn (Scall optid (Csharpminor.funsig fd) x x1)  k (Vptr sp Int.zero) te) tm c2' m2' /\
       match_cores (CSharpMin_Callstate fd vargs (Csharpminor.Kcall optid f e lenv tk))  j
              (CSharpMin_Callstate fd vargs (Csharpminor.Kcall optid f e lenv tk)) m c2' m2'.
(* exists c' : CSharpMin_core,
        inj_match_states_star unit match_cores MC_measure (tt,c') j
              (CSharpMin_Callstate fd vargs (Csharpminor.Kcall optid f e lenv tk)) m c2' m2'.*)
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
     (*exists  (CSharpMin_Callstate fd vargs (Csharpminor.Kcall optid f e lenv tk)).
     left.*) econstructor; eauto. eapply match_Kcall with (cenv' := cenv); eauto.
            simpl; trivial.
      admit. admit. (*These are the new conditions in rule MC_Callstate*)
Qed.

Lemma MS_step_case_Builtin:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv x t ef optid vres m' bl vargs
(EvalArgs: Csharpminor.eval_exprlist ge e lenv m bl vargs)
(ExtCall: Events.external_call ef ge vargs m t vres m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_exprlist cenv bl = OK x),
exists c2' : CMin_core,
  exists m2' : mem, 
      corestep_plus CMin_core_sem tge
           (CMin_State tfn (Sbuiltin optid ef x) tk (Vptr sp Int.zero) te) tm c2' m2' /\
  exists j' : meminj,
        inject_incr j j' /\
        Events.inject_separated j j' m tm /\
       match_cores (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid vres lenv))  j'
              (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid vres lenv)) m' c2' m2'.
(*  exists c',
        inj_match_states_star unit match_cores MC_measure (tt,c') j'
          (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid vres lenv)) m' c2' m2'.*)
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
             eapply Events.external_call_symbols_preserved; eauto.
                 eapply symbols_preserved; assumption.
                 eapply varinfo_preserved; assumption.
           reflexivity.
  assert (MCS': match_callstack prog j' m' tm'
                 (Frame cenv tfn e lenv te sp lo hi :: cs)
                 (Mem.nextblock m') (Mem.nextblock tm')).
    apply match_callstack_incr_bound with (Mem.nextblock m) (Mem.nextblock tm).
    eapply match_callstack_external_call; eauto.
    intros. eapply Events.external_call_max_perm; eauto.
    xomega. xomega. 
    eapply external_call_nextblock; eauto.
    eapply external_call_nextblock; eauto.
exists j'. split. assumption.  split. assumption. 
  simpl in *. (* exists  (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid vres lenv)).
  left. *) econstructor; eauto.
Opaque PTree.set.
  unfold set_optvar. destruct optid; simpl. 
  eapply match_callstack_set_temp; eauto. 
  auto.
Qed.

Lemma MS_step_case_Ite: 
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv x x0 x1 x2 b v a s1 s2
(H : Csharpminor.eval_expr ge e lenv m a v)
(BoolOfVal : Val.bool_of_val v b)
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0))
(EQ1 : transl_stmt cenv xenv s1 = OK x1)
(EQ0 : transl_stmt cenv xenv s2 = OK x2),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge
             (CMin_State tfn (Sifthenelse x x1 x2) tk (Vptr sp Int.zero) te) tm c2' m2' /\
        match_cores  (CSharpMin_State f (if b then s1 else s2) k e lenv)  j
             (CSharpMin_State f (if b then s1 else s2) k e lenv) m c2' m2'.
(*  exists c',
        inj_match_states_star unit match_cores MC_measure (tt,c') j
             (CSharpMin_State f (if b then s1 else s2) k e lenv) m c2' m2'.*)
Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  exists (CMin_State tfn (if b then x1 else x2) tk (Vptr sp Int.zero) te). exists tm.
  split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep.
              eapply step_ifthenelse; eauto. eapply bool_of_val_inject; eauto.
        econstructor; eauto.
  simpl in *.
 (*   exists (CSharpMin_State f (if b then s1 else s2) k e lenv).
    left. *) econstructor; eauto.
       destruct b; auto.
Qed.

Lemma MS_step_case_Loop:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv x s
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k cenv xenv cs)
(EQ : transl_stmt cenv xenv s = OK x),
exists c2' : CMin_core,
  exists m2' : mem,
      corestep_plus CMin_core_sem tge (CMin_State tfn (Sloop x) k (Vptr sp Int.zero) te) tm c2' m2' /\
      match_cores  (CSharpMin_State f s (Csharpminor.Kseq (Csharpminor.Sloop s) tk) e lenv)  j
          (CSharpMin_State f s (Csharpminor.Kseq (Csharpminor.Sloop s) tk) e lenv) m c2' m2'. 
(*    exists c',   inj_match_states_star unit match_cores MC_measure (tt,c') j
          (CSharpMin_State f s (Csharpminor.Kseq (Csharpminor.Sloop s) tk) e lenv) m c2' m2'. *)
Proof. intros.
  eexists; eexists.
  split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
        econstructor; eauto.
        reflexivity.
  simpl in *.
(*      exists  (CSharpMin_State f s (Csharpminor.Kseq (Csharpminor.Sloop s) tk) e lenv).
      left.*)
      econstructor; eauto. econstructor; eauto. simpl. rewrite EQ; auto. 
Qed.

Lemma MS_step_case_Block:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv x s
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k cenv xenv cs)
(EQ : transl_stmt cenv (true :: xenv) s = OK x),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn (Sblock x) k (Vptr sp Int.zero) te) tm c2' m2' /\
        match_cores (CSharpMin_State f s (Csharpminor.Kblock tk) e lenv)  j (CSharpMin_State f s (Csharpminor.Kblock tk) e lenv) m c2' m2'.
(*    exists c' ,
       inj_match_states_star unit match_cores MC_measure (tt,c') j (CSharpMin_State f s (Csharpminor.Kblock tk) e lenv) m c2' m2'.*)
Proof. intros.
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
        econstructor; eauto.
        reflexivity.
  simpl in *.
(*      exists  (CSharpMin_State f s (Csharpminor.Kblock tk) e lenv).
      left.*)
      econstructor; eauto. econstructor; eauto. 
Qed.

Lemma MS_step_case_ExitSeq:
forall  cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv n s
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kseq s tk) k cenv xenv cs),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge
               (CMin_State tfn (Sexit (shift_exit xenv n)) k (Vptr sp Int.zero) te) tm c2' m2'  /\
        match_cores (CSharpMin_State f (Csharpminor.Sexit n) tk e lenv) j
                               (CSharpMin_State f (Csharpminor.Sexit n) tk e lenv) m c2' m2'.
(*    exists c',  inj_match_states_star unit match_cores MC_measure (tt,c') j
                                   (CSharpMin_State f (Csharpminor.Sexit n) tk e lenv) m c2' m2'.*)
Proof. intros.
  dependent induction MK.

  eexists; eexists; split. 
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'.
        econstructor; eauto.
        reflexivity.
  simpl in *.
      (*exists   (CSharpMin_State f (Csharpminor.Sexit n) tk e lenv).
      left.*) econstructor; eauto. reflexivity.

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
forall  cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv 
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kblock tk) k cenv xenv cs),
exists c2' : CMin_core,
  exists m2' : mem,
       corestep_plus CMin_core_sem tge (CMin_State tfn (Sexit (shift_exit xenv 0)) k (Vptr sp Int.zero) te) tm c2' m2' /\
       match_cores  (CSharpMin_State f Csharpminor.Sskip tk e lenv) j
                              (CSharpMin_State f Csharpminor.Sskip tk e lenv) m c2' m2'.
(*    exists c', inj_match_states_star unit match_cores MC_measure (tt,c') j
                                    (CSharpMin_State f Csharpminor.Sskip tk e lenv) m c2' m2'.*)
Proof. intros.
  dependent induction MK.

  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity. 
  simpl in *.
    (*exists  (CSharpMin_State f Csharpminor.Sskip tk e lenv). 
    left.*) econstructor; eauto.

  exploit IHMK; eauto. intros [c2' [m2' [A B]]].
  exists c2'. exists m2'. 
  split; auto. 
     eapply corestep_plus_trans. 
         apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
         simpl. apply A.
Qed.

Lemma MS_step_case_ExitBlockNonzero:
forall  cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv n
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
                     (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kblock tk) k cenv xenv cs),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge
                     (CMin_State tfn (Sexit (shift_exit xenv (S n))) k (Vptr sp Int.zero) te) tm c2' m2' /\ 
       match_cores (CSharpMin_State f (Csharpminor.Sexit n) tk e lenv)  j
          (CSharpMin_State f (Csharpminor.Sexit n) tk e lenv) m c2' m2'.
Proof. intros.
  dependent induction MK.

  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity. 
  simpl in *.
    econstructor; eauto. auto.

  exploit IHMK; eauto. intros [c2' [m2' [A B]]].
  exists c2'. exists m2'. 
  split; auto. 
     eapply corestep_plus_trans. 
         apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
         simpl. apply A.
Qed.

Lemma MS_switch_descent:
  forall cenv xenv k ls body s,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK s ->
  exists k',
  transl_lblstmt_cont cenv xenv ls k k'
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
  forall f n sp e m cenv xenv k ls k1,
  let tbl := switch_table ls O in
  let ls' := select_switch n ls in
  transl_lblstmt_cont cenv xenv ls k k1 ->
  exists k2,
  corestep_star CMin_core_sem tge (CMin_State f (Sexit (Switch.switch_target n (length tbl) tbl)) k1 sp e) m  (CMin_State f (Sexit O) k2 sp e) m
  /\ transl_lblstmt_cont cenv xenv ls' k k2.
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

Lemma MS_switch_MSI:
  forall fn k e lenv m tfn ts tk sp te tm cenv xenv j lo hi cs sz ls body tk'
    (TRF: transl_funbody cenv sz fn = OK tfn)
    (TR: transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts)
    (MINJ: Mem.inject j m tm)
    (MCS: match_callstack prog j m tm
               (Frame cenv tfn e lenv te sp lo hi :: cs)
               (Mem.nextblock m) (Mem.nextblock tm))
    (MK: match_cont k tk cenv xenv cs)
    (TK: transl_lblstmt_cont cenv xenv ls tk tk'),
  exists S, exists mm,
  corestep_plus CMin_core_sem tge (CMin_State tfn (Sexit O) tk' (Vptr sp Int.zero) te) tm S mm
  /\ match_statesInj prog j (Csharpminor.State fn (seq_of_lbl_stmt ls) k e lenv m) (Cminor_coop.ToState S mm).
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
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv a x x0 ts cases n
(EvalA: Csharpminor.eval_expr ge e lenv m a (Vint n))
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0))
(EQ0 : transl_lblstmt cenv (switch_env cases xenv) cases
        (Sswitch x (switch_table cases 0) (length (switch_table cases 0))) =
      OK ts),
exists c2' : CMin_core,
  exists m2' : mem,
          corestep_plus CMin_core_sem tge (CMin_State tfn ts tk (Vptr sp Int.zero) te) tm c2' m2' /\
         match_cores (CSharpMin_State f (seq_of_lbl_stmt (select_switch n cases)) k e lenv)  j
                               (CSharpMin_State f (seq_of_lbl_stmt (select_switch n cases)) k e lenv) m c2' m2'.
Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  inv VINJ.
  exploit MS_switch_descent; eauto. intros [k1 [A B]].
  exploit MS_switch_ascent; eauto. intros [k2 [C D]].
  exploit transl_lblstmt_suffix; eauto. simpl. intros [body' [ts' E]].
  exploit MS_switch_MSI; eauto. intros [T2 [m2' [F G]]].
  exists T2; exists m2'; split.
      eapply corestep_plus_star_trans.
          eapply B. 
      eapply corestep_star_trans.
         eapply corestep_star_one. eapply CompCertStep_CMin_corestep'. constructor. eassumption. reflexivity. 
      simpl.
        eapply corestep_star_trans.
         apply C.
         eapply corestep_plus_star. eapply F.
  simpl. eapply MSI_MC. apply G.
Qed.

Lemma MS_step_case_ReturnNone:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv m'
(Freelist: Mem.free_list m (blocks_of_env e) = Some m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
                 (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k cenv xenv cs),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn (Sreturn None) k (Vptr sp Int.zero) te) tm c2' m2'  /\
       match_cores (CSharpMin_Returnstate Vundef (Csharpminor.call_cont tk))  j
                             (CSharpMin_Returnstate Vundef (Csharpminor.call_cont tk)) m' c2' m2'.
Proof. intros.
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. eapply step_return_0. eauto. reflexivity. 
  simpl in *.
    econstructor; eauto. eapply match_call_cont; eauto.
Qed.

Lemma MS_step_case_ReturnSome:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv a x x0 m' v 
(EvalA: Csharpminor.eval_expr ge e lenv m a v)
(Freelist: Mem.free_list m (blocks_of_env e) = Some m')
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont tk k cenv xenv cs)
(EQ : transl_expr cenv a = OK (x, x0)),
exists c2' : CMin_core,
  exists m2' : mem,
        corestep_plus CMin_core_sem tge (CMin_State tfn (Sreturn (Some x)) k (Vptr sp Int.zero) te) tm c2' m2' /\
        match_cores  (CSharpMin_Returnstate v (Csharpminor.call_cont tk)) j
                 (CSharpMin_Returnstate v (Csharpminor.call_cont tk)) m' c2' m2'.
Proof. intros.
  exploit transl_expr_correct; eauto. intros [tv [EVAL [VINJ APP]]].
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  eexists; eexists; split.
     apply corestep_plus_one. eapply CompCertStep_CMin_corestep'. eapply step_return_1. eauto. eauto. reflexivity. 
  simpl in *.
    econstructor; eauto. eapply match_call_cont; eauto.
Qed.

Lemma MS_step_case_Label:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv lbl x s
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv xenv cs)
(EQ : transl_stmt cenv xenv s = OK x),
exists c2' : CMin_core,
  exists m2' : mem,
       corestep_plus CMin_core_sem tge (CMin_State tfn (Slabel lbl x) tk (Vptr sp Int.zero) te) tm c2' m2' /\ 
      match_cores (CSharpMin_State f s k e lenv)  j (CSharpMin_State f s k e lenv) m c2' m2'.
Proof. intros.
  eexists; eexists; split.
    eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. constructor. reflexivity.
  simpl.
  econstructor; eauto.
Qed.

Lemma MS_step_case_Goto:
forall cenv sz f tfn j m tm e lenv te sp lo hi cs k tk xenv lbl s' k'
(FindLab: Csharpminor.find_label lbl (Csharpminor.fn_body f)
       (Csharpminor.call_cont k) = Some (s', k'))
(TRF : transl_funbody cenv sz f = OK tfn)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm (Frame cenv tfn e lenv te sp lo hi :: cs)
        (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv xenv cs),
exists c2' : CMin_core,
  exists m2' : mem,
       corestep_plus CMin_core_sem tge (CMin_State tfn (Sgoto lbl) tk (Vptr sp Int.zero) te) tm c2' m2' /\
       match_cores  (CSharpMin_State f s' k' e lenv) j (CSharpMin_State f s' k' e lenv) m c2' m2'.
Proof. intros.
  exploit transl_find_label_body; eauto. 
  intros [ts' [tk' [xenv' [A [B C]]]]].
  eexists; eexists; split.
    eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. apply step_goto. eexact A. reflexivity.
  simpl.
  econstructor; eauto.
Qed.


(******************************Functions required for internal call rule*****************************)
(****These extend the original lemmas by additional guarantees of the (now exposed) memory injections, in order
    for the overall lemma for internal calls to establish the inject_separated fact******************************)

Lemma MS_match_callstack_alloc_variables_rec:
  forall tm sp tf cenv le te lo cs,
  Mem.valid_block tm sp ->
  fn_stackspace tf <= Int.max_unsigned ->
  (forall ofs k p, Mem.perm tm sp ofs k p -> 0 <= ofs < fn_stackspace tf) ->
  (forall ofs k p, 0 <= ofs < fn_stackspace tf -> Mem.perm tm sp ofs k p) ->
  forall e1 m1 vars e2 m2,
  alloc_variables e1 m1 vars e2 m2 ->
  forall f1,
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace tf) ->
  cenv_separated cenv vars ->
  cenv_mem_separated cenv vars f1 sp m1 ->
  (forall id sz, In (id, sz) vars -> e1!id = None) ->
  match_callstack prog f1 m1 tm
    (Frame (cenv_remove cenv vars) tf e1 le te sp lo (Mem.nextblock m1) :: cs)
    (Mem.nextblock m1) (Mem.nextblock tm) ->
  Mem.inject f1 m1 tm ->
  exists f2,
    match_callstack prog f2 m2 tm
      (Frame cenv tf e2 le te sp lo (Mem.nextblock m2) :: cs)
      (Mem.nextblock m2) (Mem.nextblock tm)
  /\ Mem.inject f2 m2 tm
  /\ (*LENB: THIS IS NEW*) inject_incr f1 f2
(****************The following three conditions are new******************)
  /\ (forall b, Mem.valid_block m1 b -> f2 b = f1 b)
  /\ (forall b b' d', f1 b = None -> f2 b = Some (b',d') -> b' = sp)
  /\ forall j',  inject_incr f2 j' -> inject_separated f2 j' m2 tm -> 
                 inject_separated f2 j' m1 tm.
Proof.
Proof.
  intros until cs; intros VALID REPRES STKSIZE STKPERMS.
  induction 1; intros f1 NOREPET COMPAT SEP1 SEP2 UNBOUND MCS MINJ.
  (* base case *)
  simpl in MCS. exists f1.
   split. assumption. 
   split. assumption. 
   split. apply inject_incr_refl. 
   split. auto. 
   split. intros. rewrite H in H0; inv H0. 
   intros. assumption. 
  (* inductive case *)
  simpl in NOREPET. inv NOREPET.
(* exploit Mem.alloc_result; eauto. intros RES.
  exploit Mem.nextblock_alloc; eauto. intros NB.*)
  exploit (COMPAT id sz). auto with coqlib. intros [ofs [CENV [ALIGNED [LOB HIB]]]].
  exploit Mem.alloc_left_mapped_inject. 
    eexact MINJ.
    eexact H.
    eexact VALID.
    instantiate (1 := ofs). zify. omega. 
    intros. exploit STKSIZE; eauto. omega. 
    intros. apply STKPERMS. zify. omega.
    replace (sz - 0) with sz by omega. auto.
    intros. eapply SEP2. eauto with coqlib. eexact CENV. eauto. eauto. omega. 
  intros [f2 [A [B [C D]]]].
  exploit (IHalloc_variables f2); eauto.
    red; intros. eapply COMPAT. auto with coqlib.
    red; intros. eapply SEP1; eauto with coqlib.
    red; intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b b1); intros P.
    subst b. rewrite C in H5; inv H5. 
    exploit SEP1. eapply in_eq. eapply in_cons; eauto. eauto. eauto. 
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto. 
    omega.
    eapply SEP2. apply in_cons; eauto. eauto. 
    rewrite D in H5; eauto. eauto. auto. 
    intros. rewrite PTree.gso. eapply UNBOUND; eauto with coqlib. 
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    eapply match_callstack_alloc_left; eauto. 
    rewrite cenv_remove_gso; auto. 
    apply UNBOUND with sz; auto with coqlib.
  intros. destruct H1 as [f3 [HF1 [HF2 [Hf3 [HF4 [HF5 HF6]]]]]]. 
    exists f3. split; trivial.
    split; trivial. 
    split. eapply inject_incr_trans; eassumption.
    split. intros.
        rewrite HF4.
         apply D.
           intros N; subst.
               eapply (Mem.fresh_block_alloc _ _ _ _ _ H H1).
           apply (Mem.valid_block_alloc _ _ _ _ _ H _ H1).
    split; intros.
       destruct (eq_block b b1); subst.
       rewrite (Hf3 _ _ _ C) in H2. inv H2. trivial.
       specialize (D _ n).
         rewrite <- D in H1. apply (HF5 _ _ _ H1 H2).
    intros b; intros.
      destruct (H2 _ _ _ H5 H6).
      split; trivial.
      intros N. apply H7; clear H7.
      apply (Mem.valid_block_alloc _ _ _ _ _ H) in N.
      eapply alloc_variables_forward. eassumption. apply N.
Qed.

Lemma MS_match_callstack_alloc_variables_aux:
  forall tm1 sp tm2 m1 vars e m2 cenv f1 cs fn le te,
  Mem.alloc tm1 0 (fn_stackspace fn) = (tm2, sp) ->
  fn_stackspace fn <= Int.max_unsigned ->
  alloc_variables empty_env m1 vars e m2 ->
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace fn) ->
  cenv_separated cenv vars ->
  (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)) ->
  Mem.inject f1 m1 tm1 ->
  match_callstack prog f1 m1 tm1 cs (Mem.nextblock m1) (Mem.nextblock tm1) ->
  match_temps f1 le te ->
  exists f2,
    match_callstack prog f2 m2 tm2 (Frame cenv fn e le te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                    (Mem.nextblock m2) (Mem.nextblock tm2)
  /\ Mem.inject f2 m2 tm2
  /\ (*LENB: THIS IS NEW*) inject_incr f1 f2
(****************The following three conditions are new******************)
(* In the third clause, we now stepfrom  m' to m, and also from f' to f and from tm' to tm******************)
  /\ (forall b, Mem.valid_block m1 b -> f2 b = f1 b)
  /\ (forall b b' d', f1 b = None -> f2 b = Some (b',d') -> b' = sp)
  /\ forall j',  inject_incr f2 j' -> Events.inject_separated f2 j' m2 tm2 -> 
          Events.inject_separated f2 j' m1 tm1.
Proof. clear core_data.
  intros.
  unfold build_compilenv in H.
assert (AR: exists f',
   match_callstack prog f' m2 tm2
                     (Frame cenv fn e le te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                     (Mem.nextblock m2) (Mem.nextblock tm2) 
 
  /\ Mem.inject f' m2 tm2
  /\ inject_incr f1 f'
  /\ (forall b, Mem.valid_block m1 b -> f' b = f1 b)
  /\ (forall b b' d', f1 b = None -> f' b = Some (b',d') -> b' = sp)
  /\ forall j',  inject_incr f' j' -> Events.inject_separated f' j' m2 tm2 -> 
                  Events.inject_separated f' j' m1 tm2).

  eapply MS_match_callstack_alloc_variables_rec; eauto with mem.
  (*instantiate (1 := f1).*) red; intros. eelim Mem.fresh_block_alloc; eauto.
  eapply Mem.valid_block_inject_2; eauto. 
  intros. apply PTree.gempty.
  eapply match_callstack_alloc_right; eauto. 
  intros. destruct (In_dec peq id (map fst vars)).
  apply cenv_remove_gss; auto.
  rewrite cenv_remove_gso; auto.
  destruct (cenv!id) as [ofs|] eqn:?; auto. elim n; eauto. 
  eapply Mem.alloc_right_inject; eauto. 

destruct AR as  [f' [INC [INJ [MC [VB1 [SP SEP]]]]]].
exists f' ; intuition.
  intros b; intros.
  remember (f' b) as z; destruct z; apply eq_sym in Heqz.
  (*Some p*) destruct p.
            assert (j' b = Some (b0,z)). apply (H9 _ _ _ Heqz). inv H11. 
   (*None*) assert (HH:= SEP _ H9 H10).
                     destruct (HH _ _ _ Heqz H12).
                     split; trivial. 
                     intros N. apply H14. eapply Mem.valid_block_alloc; eauto. 
Qed.

(*Outdated in CompCert 2.0
Lemma MS_match_callstack_alloc_variable:
  forall atk id lv cenv sz cenv' sz' tm sp e tf m m' b te lenv lo cs f tv,
  assign_variable atk (id, lv) (cenv, sz) = (cenv', sz') ->
  Mem.valid_block tm sp ->
  (forall ofs k p,
    Mem.perm tm sp ofs k p -> 0 <= ofs < tf.(fn_stackspace)) ->
  Mem.range_perm tm sp 0 tf.(fn_stackspace) Cur Freeable ->
  tf.(fn_stackspace) <= Int.max_unsigned ->
  Mem.alloc m 0 (sizeof lv) = (m', b) ->
  match_callstack prog f m tm 
                  (Frame cenv tf e lenv te sp lo (Mem.nextblock m) :: cs)
                  (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  0 <= sz -> sz' <= tf.(fn_stackspace) ->
  (forall b delta ofs k p,
     f b = Some(sp, delta) -> Mem.perm m b ofs k p -> ofs + delta < sz) ->
  e!id = None ->
  te!(for_var id) = Some tv ->
  exists f',
     inject_incr f f'
  /\ Mem.inject f' m' tm
  /\ match_callstack prog f' m' tm
                     (Frame cenv' tf (PTree.set id (b, lv) e) lenv te sp lo (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm)
  /\ (forall b delta ofs k p,
      f' b = Some(sp, delta) -> Mem.perm m' b ofs k p -> ofs + delta < sz') 
(****************The following three conditions are new******************)
  /\ (forall b, Mem.valid_block m b -> f' b = f b)
  /\ (forall b b' d', f b = None -> f' b = Some (b',d') -> b' = sp)
  /\ forall j',  inject_incr f' j' -> Events.inject_separated f' j' m' tm -> Events.inject_separated f' j' m tm.
Proof.
  intros until tv. intros ASV VALID BOUNDS PERMS NOOV ALLOC MCS INJ LO HI RANGE E TE.
  generalize ASV. unfold assign_variable. 
  caseEq lv.
  (* 1. lv = LVscalar chunk *)
  intros chunk LV. case (Identset.mem id atk).
  (* 1.1 info = Var_stack_scalar chunk ofs *)
    set (ofs := align sz (size_chunk chunk)).
    intro EQ; injection EQ; intros; clear EQ. rewrite <- H0.
    generalize (size_chunk_pos chunk); intro SIZEPOS.
    generalize (align_le sz (size_chunk chunk) SIZEPOS). fold ofs. intro SZOFS.
    exploit Mem.alloc_left_mapped_inject.
      eauto. eauto. eauto. 
      instantiate (1 := ofs). omega.
      intros. exploit BOUNDS; eauto. omega. 
      intros. apply Mem.perm_implies with Freeable; auto with mem. apply Mem.perm_cur. 
      apply PERMS. rewrite LV in H1. simpl in H1. omega.
      rewrite LV; simpl. rewrite Zminus_0_r. unfold ofs. 
      apply inj_offset_aligned_var.
      intros. generalize (RANGE _ _ _ _ _ H1 H2). omega. 
    intros [f1 [MINJ1 [INCR1 [SAME OTHER]]]].
    exists f1; split. auto. split. auto. split. 
    eapply match_callstack_alloc_left; eauto.
    rewrite <- LV; auto. 
    rewrite SAME; constructor.
  split.
    intros. exploit Mem.perm_alloc_inv; eauto. destruct (zeq b0 b).
    subst b0. assert (delta = ofs) by congruence. subst delta.  
    rewrite LV. simpl. omega.
    intro. rewrite OTHER in H1; eauto. generalize (RANGE _ _ _ _ _ H1 H3). omega. 
  assert (XX: forall b0 : Values.block, Mem.valid_block m b0 -> f1 b0 = f b0).
     intros b0; intros. destruct (eq_block b0 b); subst. 
                     exfalso. apply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC H1).
                  apply (OTHER _ n).
   split; trivial.
   split; intros. destruct (eq_block b0 b); subst. rewrite SAME in H2. inv H2. trivial.
                         rewrite (OTHER _ n) in H2. congruence. 
     intros. intros bb; intros.
     destruct (H2 _ _ _ H3 H4). split; trivial. intros N. apply H5. eapply Mem.valid_block_alloc; eauto.
  (* 1.2 info = Var_local chunk *)
    intro EQ; injection EQ; intros; clear EQ. subst sz'. rewrite <- H0.
    exploit Mem.alloc_left_unmapped_inject; eauto.
    intros [f1 [MINJ1 [INCR1 [SAME OTHER]]]].
    exists f1; split. auto. split. auto. split.
      eapply match_callstack_alloc_left; eauto.  
      rewrite <- LV; auto.
      rewrite SAME; constructor.
   split.
      intros. exploit Mem.perm_alloc_inv; eauto. destruct (zeq b0 b).
      subst b0. congruence.
      rewrite OTHER in H; eauto.
  assert (XX: forall b0 : Values.block, Mem.valid_block m b0 -> f1 b0 = f b0).
     intros b0; intros. destruct (eq_block b0 b); subst. 
                     exfalso. apply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC H).
                  apply (OTHER _ n).
   split; trivial.
   split; intros. destruct (eq_block b0 b); subst. rewrite SAME in H1. inv H1.
                         rewrite (OTHER _ n) in H1. congruence. 
   intros bb; intros.
     destruct (H1 _ _ _ H2 H3). split; trivial. intros N. apply H4. eapply Mem.valid_block_alloc; eauto.
  (* 2 info = Var_stack_array ofs *)
  intros dim al LV EQ. injection EQ; clear EQ; intros. rewrite <- H.
  assert (0 <= Zmax 0 dim). apply Zmax1. 
  generalize (align_le sz (array_alignment dim) (array_alignment_pos dim)). intro.
  set (ofs := align sz (array_alignment dim)) in *.
  exploit Mem.alloc_left_mapped_inject. eauto. eauto. eauto. 
    instantiate (1 := ofs). 
    generalize Int.min_signed_neg. omega.
    intros. exploit BOUNDS; eauto. generalize Int.min_signed_neg. omega.
    intros. apply Mem.perm_implies with Freeable; auto with mem. apply Mem.perm_cur.
    apply PERMS. rewrite LV in H3. simpl in H3. omega.
    rewrite LV; simpl. rewrite Zminus_0_r. unfold ofs. 
    apply inj_offset_aligned_array'.
    intros. generalize (RANGE _ _ _ _ _ H3 H4). omega. 
  intros [f1 [MINJ1 [INCR1 [SAME OTHER]]]].
  exists f1; split. auto. split. auto. split. 
    subst cenv'. eapply match_callstack_alloc_left; eauto.
    rewrite <- LV; auto. 
    rewrite SAME; constructor.
  split.
    intros. exploit Mem.perm_alloc_inv; eauto. destruct (zeq b0 b).
    subst b0. assert (delta = ofs) by congruence. subst delta. 
    rewrite LV. simpl. omega.
    intro. rewrite OTHER in H3; eauto. generalize (RANGE _ _ _ _ _ H3 H5). omega. 
  assert (XX: forall b0 : Values.block, Mem.valid_block m b0 -> f1 b0 = f b0).
     intros b0; intros. destruct (eq_block b0 b); subst. 
                     exfalso. apply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC H3).
                  apply (OTHER _ n).
   split; trivial.
   split; intros. destruct (eq_block b0 b); subst. rewrite SAME in H4. inv H4. trivial.
                         rewrite (OTHER _ n) in H4. congruence. 
   intros bb; intros.
     destruct (H4 _ _ _ H5 H6). split; trivial. intros N. apply H7. eapply Mem.valid_block_alloc; eauto.
Qed.

Lemma MS_match_callstack_alloc_variables_rec:
  forall tm sp cenv' tf lenv te lo cs atk,
  Mem.valid_block tm sp ->
  (forall ofs k p,
    Mem.perm tm sp ofs k p -> 0 <= ofs < tf.(fn_stackspace)) ->
  Mem.range_perm tm sp 0 tf.(fn_stackspace) Cur Freeable ->
  tf.(fn_stackspace) <= Int.max_unsigned ->
  forall e m vars e' m',
  alloc_variables e m vars e' m' ->
  forall f cenv sz,
  assign_variables atk vars (cenv, sz) = (cenv', tf.(fn_stackspace)) ->
  match_callstack prog f m tm 
                  (Frame cenv tf e lenv te sp lo (Mem.nextblock m) :: cs)
                  (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  0 <= sz ->
  (forall b delta ofs k p,
     f b = Some(sp, delta) -> Mem.perm m b ofs k p -> ofs + delta < sz) ->
  (forall id lv, In (id, lv) vars -> te!(for_var id) <> None) ->
  list_norepet (List.map (@fst ident var_kind) vars) ->
  (forall id lv, In (id, lv) vars -> e!id = None) ->
  exists f',
     inject_incr f f'
  /\ Mem.inject f' m' tm
  /\ match_callstack prog f' m' tm
                     (Frame cenv' tf e' lenv te sp lo (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm)
(****************The following three conditions are new******************)
(*** Note that in the third clause, we only "step" from m' to m ***************)
  /\ (forall b, Mem.valid_block m b -> f' b = f b)
  /\ (forall b b' d', f b = None -> f' b = Some (b',d') -> b' = sp)
  /\ forall j',  inject_incr f' j' -> Events.inject_separated f' j' m' tm -> Events.inject_separated f' j' m tm .
Proof. clear core_data. 
  intros until atk. intros VALID BOUNDS PERM NOOV.
  induction 1.
  (* base case *)
  intros. simpl in H. inversion H; subst cenv sz.
  exists f. split. apply inject_incr_refl. split. auto. split. auto.
    split; trivial.
    split; trivial. intros. congruence.
  (* inductive case *)
  intros until sz.
  change (assign_variables atk ((id, lv) :: vars) (cenv, sz))
  with (assign_variables atk vars (assign_variable atk (id, lv) (cenv, sz))).
  caseEq (assign_variable atk (id, lv) (cenv, sz)).
  intros cenv1 sz1 ASV1 ASVS MATCH MINJ SZPOS BOUND DEFINED NOREPET UNDEFINED.
  assert (DEFINED1: forall id0 lv0, In (id0, lv0) vars -> te!(for_var id0) <> None).
    intros. eapply DEFINED. simpl. right. eauto.
  assert (exists tv, te!(for_var id) = Some tv).
    assert (te!(for_var id) <> None). eapply DEFINED. simpl; left; auto.
    destruct (te!(for_var id)). exists v; auto. congruence. 
  destruct H1 as [tv TEID].
  assert (sz1 <= fn_stackspace tf). eapply assign_variables_incr; eauto. 
  exploit MS_match_callstack_alloc_variable; eauto with coqlib.
  intros [f1 [INCR1 [INJ1 [MCS1 [BOUND1 [VB [SP SEP]]]]]]].
  exploit IHalloc_variables; eauto. 
  apply Zle_trans with sz; auto. eapply assign_variable_incr; eauto.
  inv NOREPET; auto.
  intros. rewrite PTree.gso. eapply UNDEFINED; eauto with coqlib.
  simpl in NOREPET. inversion NOREPET. red; intro; subst id0.
  elim H5. change id with (fst (id, lv0)). apply List.in_map. auto.
  intros [f2 [INCR2 [INJ2 [MCS2 [VBF2 [SP2 SEP2]]]]]].
  assert (X: forall b : Values.block, Mem.valid_block m b -> f2 b = f b).
           intros. rewrite <- (VB _ H2). apply VBF2. eapply Mem.valid_block_alloc; eauto.
  assert (Y:  (forall (b b' : Values.block) (d' : Z), f b = None -> f2 b = Some (b', d') -> b' = sp)).
       clear MCS2 BOUND1 MCS1 DEFINED1 SEP SEP2 IHalloc_variables UNDEFINED.
          intros. remember (f1 b) as z. destruct z; apply eq_sym in Heqz.
              destruct p.  assert (Z1 := SP _ _ _ H2 Heqz). subst.
                 apply INCR2 in Heqz. rewrite Heqz in H3. inv H3. trivial.
             apply (SP2 _ _ _ Heqz H3).
  exists f2 ; intuition.
    eapply inject_incr_trans; eauto.
    intros b; intros. destruct (H3 _ _ _ H4 H5). split; trivial.
     intros N. apply H6. apply (Mem.valid_block_alloc _ _ _ _ _ H) in N.
              eapply allocvars_blocks_valid; eauto.
Qed. 

Lemma MS_match_callstack_alloc_variables:
  forall fn cenv tf m e m' tm tm' sp f cs targs,
  build_compilenv gce fn = (cenv, tf.(fn_stackspace)) ->
  tf.(fn_stackspace) <= Int.max_unsigned ->
  list_norepet (fn_params_names fn ++ fn_vars_names fn) ->
  alloc_variables Csharpminor.empty_env m (fn_variables fn) e m' ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  match_callstack prog f m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  let tparams := List.map for_var (fn_params_names fn) in
  let tvars := List.map for_var (fn_vars_names fn) in
  let ttemps := List.map for_temp (Csharpminor.fn_temps fn) in
  let te := set_locals (tvars ++ ttemps) (set_params targs tparams) in
  exists f',
     inject_incr f f'
  /\ Mem.inject f' m' tm'
  /\ match_callstack prog f' m' tm'
                     (Frame cenv tf e empty_temp_env te sp (Mem.nextblock m) (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm') 
(****************The following three conditions are new******************)
(* In the third clause, we now stepfrom  m' to m, and also from f' to f and from tm' to tm******************)
  /\ (forall b, Mem.valid_block m b -> f' b = f b)
  /\ (forall b b' d', f b = None -> f' b = Some (b',d') -> b' = sp)
  /\ forall j',  inject_incr f' j' -> Events.inject_separated f' j' m' tm' -> Events.inject_separated f j' m tm.
Proof. clear core_data.
  intros.
  unfold build_compilenv in H.
assert (AR: exists f',
     inject_incr f f'
  /\ Mem.inject f' m' tm'
  /\ match_callstack prog f' m' tm'
                     (Frame cenv tf e empty_temp_env te sp (Mem.nextblock m) (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm') 
  /\ (forall b, Mem.valid_block m b -> f' b = f b)
  /\ (forall b b' d', f b = None -> f' b = Some (b',d') -> b' = sp)
  /\ forall j',  inject_incr f' j' -> Events.inject_separated f' j' m' tm' -> Events.inject_separated f' j' m tm').
  eapply MS_match_callstack_alloc_variables_rec; eauto with mem.
  red; intros. eapply Mem.perm_alloc_2; eauto. 
  eapply match_callstack_alloc_right; eauto.
  eapply Mem.alloc_right_inject; eauto. omega. 
  intros. elim (Mem.valid_not_valid_diff tm sp sp); eauto with mem.
  eapply Mem.valid_block_inject_2; eauto.
  intros. unfold te. apply set_locals_params_defined.
  elim (in_app_or _ _ _ H6); intros.
  apply in_or_app; left. unfold tparams. apply List.in_map.
  change id with (fst (id, lv)). apply List.in_map. auto.
  apply in_or_app; right. apply in_or_app; left. unfold tvars. apply List.in_map. 
  change id with (fst (id, lv)). apply List.in_map; auto.
  (* norepet *)
  unfold fn_variables. rewrite List.map_app. assumption.
  (* undef *)
  intros. unfold empty_env. apply PTree.gempty.

destruct AR as  [f' [INC [INJ [MC [VB1 [SP SEP]]]]]].
exists f' ; intuition.
  intros b; intros.
  remember (f' b) as z; destruct z; apply eq_sym in Heqz.
  (*Some p*) destruct p.
            assert (j' b = Some (b0,z)). apply (H6 _ _ _ Heqz). 
             rewrite H9 in H10; inv H10.
             assert (Z:= SP _ _ _ H8 Heqz); subst.
             split; intros N. rewrite (VB1 _ N) in Heqz. congruence.
             eapply (Mem.fresh_block_alloc _ _ _ _ _ H3 N).
  (*None*) assert (HH:= SEP _ H6 H7).
                     destruct (HH _ _ _ Heqz H9).
                     split; trivial. 
                     intros N. apply H11. eapply Mem.valid_block_alloc; eauto. 
Qed.

Lemma MS_var_set_self_correct_scalar:
  forall cenv id s a f tf e lenv te sp lo hi m cs tm tv v m' fn k,
  var_set_self cenv id s = OK a ->
  match_callstack prog f m tm (Frame cenv tf e lenv te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
  val_inject f v tv ->
  Mem.inject f m tm ->
  exec_assign ge e m id v m' ->
  te!(for_var id) = Some tv ->
  exists tm',
    corestep_star CMin_core_sem tge (CMin_State fn a k (Vptr sp Int.zero) te) tm
                                    (CMin_State fn s k (Vptr sp Int.zero) te) tm' /\
    Mem.inject f m' tm' /\
    match_callstack prog f m' tm' (Frame cenv tf e lenv te sp lo hi :: cs) (Mem.nextblock m') (Mem.nextblock tm') 
(********* The following 2 conditions are new*****)
   /\ (forall b, Mem.valid_block m b -> Mem.valid_block m' b) (* actually <-> holds*)
  /\ (forall b, Mem.valid_block tm b -> Mem.valid_block tm' b). (* actually <-> holds*)
Proof. clear core_data.
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
  split.
    apply match_callstack_extensional with (PTree.set (for_var id) tv te).
    intros. repeat rewrite PTree.gsspec.
    destruct (peq (for_var id0) (for_var id)). congruence. auto.
    intros. rewrite PTree.gso; auto. unfold for_temp, for_var. congruence. 
    eapply match_callstack_store_local; eauto.
  split; intros; trivial. 
    (*apply prop_ext.
    split; intros. *) eapply Mem.store_valid_block_1; eauto.
     (* eapply Mem.store_valid_block_2; eauto.*)
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
  split. trivial.
  split.
    rewrite NEXTBLOCK. rewrite (nextblock_storev _ _ _ _ _ STORE'). 
    eapply match_callstack_storev_mapped; eauto.
  split; intros. 
    (*apply prop_ext; split; intros. *) eapply Mem.store_valid_block_1; eauto.
           (* eapply Mem.store_valid_block_2; eauto.  *)
    inv EVAL'.  (*apply prop_ext; split; intros.  *) eapply storev_valid_block_1; eauto.
                             (*eapply storev_valid_block_2; eauto.   *)
Qed.

Lemma MS_var_set_self_correct_array:
  forall cenv id s a f tf e lenv te sp lo hi m cs tm tv b v sz al m' fn k,
  var_set_self cenv id s = OK a ->
  match_callstack prog f m tm (Frame cenv tf e lenv te sp lo hi :: cs) (Mem.nextblock m) (Mem.nextblock tm) ->
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
    match_callstack prog f' m' tm' (Frame cenv tf e lenv te sp lo hi :: cs) (Mem.nextblock m') (Mem.nextblock tm') /\
    inject_incr f f'  /\
(******* The following five conditions are new -- but actually, only conditions 3-5 or used below*****)
    Events.mem_unchanged_on (Events.loc_unmapped f) m m' /\
    Events.mem_unchanged_on (Events.loc_out_of_reach f m) tm tm' /\
    Events.inject_separated f f' m tm  /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b) (* actually <-> holds*)
  /\ (forall b, Mem.valid_block tm b -> Mem.valid_block tm' b). 
Proof. clear core_data.
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
split.  auto.
split; trivial.
split; trivial.
split; trivial.
split; intros. inv MEMCPY. eapply Mem.storebytes_valid_block_1; eauto.
   (*    apply prop_ext; split; intros. eapply Mem.storebytes_valid_block_1; eauto. eapply Mem.storebytes_valid_block_2; eauto.      *)
eapply Events.external_call_valid_block; eauto. 
Qed.

(*Lemma appears to be new*)
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

(*Lemma appears to be new, but was not needed after all in new proof*)
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

(*Lemma appears to be new, but was not needed after all in new proof*)
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

(*Lemma appears to be new, but was not needed after all in new proof*)
Lemma bind_parameters_inject_separated_array:
forall gee e params vals m1 m2  m cpvals t n sz
(MemCPY: Events.extcall_memcpy_sem sz n gee cpvals m t Vundef m1)
(BP: bind_parameters gee e m1 params vals m2) 
j' tm3 j tm1 tm2 
(MINJ : Mem.inject j' m2 tm3)
(SEP : Events.inject_separated j j' m1 tm2),
Events.inject_separated j j' m tm1.
Proof. intros. inv MemCPY.
  intros bb; intros.
     unfold Events.inject_separated in SEP.
     destruct (SEP _ _ _ H7 H8).
     split; intros XX.  
       apply H9. eapply Mem.storebytes_valid_block_1; eauto.
     assert (~ Mem.valid_block m2 bb).
       intros ZZ. apply H9.  apply (bind_parameters_validblock_2 _ _ _ _ _ _ BP _ ZZ). 
       unfold Mem.inject in MINJ. destruct MINJ.
         rewrite (mi_freeblocks _ H11) in H8. inv H8.    
Qed.

Lemma MS_store_parameters_correct:
  forall e lenv te m1 params vl m2,
  bind_parameters ge e m1 params vl m2 ->
  forall s j1 cenv tf sp lo hi cs tm1 fn' k,
  vars_vals_match j1 params vl te ->
  list_norepet (List.map variable_name params) ->
  Mem.inject j1 m1 tm1 ->
  match_callstack prog j1 m1 tm1 (Frame cenv tf e lenv te sp lo hi :: cs) (Mem.nextblock m1) (Mem.nextblock tm1) ->
  store_parameters cenv params = OK s ->
 exists j2, exists tm2,
     corestep_star CMin_core_sem tge (CMin_State fn' s k (Vptr sp Int.zero) te) tm1
                 (CMin_State fn' Sskip k (Vptr sp Int.zero) te) tm2
  /\ Mem.inject j2 m2 tm2
  /\ match_callstack prog j2 m2 tm2 (Frame cenv tf e lenv te sp lo hi :: cs) (Mem.nextblock m2) (Mem.nextblock tm2)
  /\ inject_incr j1 j2
(********* The following 3 conditions are new*****)
  /\ Events.inject_separated j1 j2 m1 tm1
  /\ (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b)
  /\ (forall b, Mem.valid_block tm1 b -> Mem.valid_block tm2 b).
Proof.
  induction 1.
  (* base case *)
  intros; simpl. monadInv H3. rename m into m1.
  exists j1. exists tm1. split. eapply corestep_star_zero.
       split; trivial.
       split; trivial.
       split; trivial.
       split. apply inject_separated_same_meminj.
       split; trivial.
  (* scalar case *)
  rename m1 into mm1. rename m into m1.
  intros until k.  intros VVM NOREPET MINJ MATCH STOREP.
  monadInv STOREP. inv VVM. inv NOREPET. 
  exploit MS_var_set_self_correct_scalar; eauto.
    econstructor; eauto. econstructor; eauto.
  intros [tmm1 [EXEC1 [MINJ1 [MATCH1 [VB TVB]]]]]. 
  exploit IHbind_parameters; eauto.
  intros [j2 [tm2 [EXEC2 [MINJ2 [MATCH2 [INJ2 [SEP2 [VB2 TVB2]]]]]]]]. 
  exists j2; exists tm2.
  split. eapply corestep_star_trans; eauto.
  split; trivial.
  split; trivial.
  split; trivial.
  split.
      intros bb; intros. destruct (SEP2 _ _ _ H3 H4).
      split; intros N. (*rewrite VB in N. apply (H7 N).*) apply H7. apply (VB _ N).
                                (*rewrite TVB in N. apply (H9 N). *) apply H9. apply (TVB _ N).
  split; intros.   (*rewrite VB. apply VB2. *) apply VB2. apply (VB _ H3).
           apply TVB2. (*rewrite <- TVB. assumption. *) apply (TVB _ H3).
  (* array case *)
  intros until k.  intros VVM NOREPET MINJ MATCH STOREP.
  monadInv STOREP. inv VVM. inv NOREPET.
  exploit MS_var_set_self_correct_array; eauto.
  intros [f2 [tm2 [EXEC1 [MINJ1 [MATCH1 [INCR1 [UcOn [TUcOn1 [SEP1 [VB1 TVB1]]]]]]]]]].
  clear UcOn TUcOn1. (*this shows that the first 2 new conditions of MS_var_set_self_correct_array are in fact superfluous*)
  exploit IHbind_parameters. eapply vars_vals_match_incr; eauto. auto. eauto. eauto. eauto. 
  intros [f3 [tm3 [EXEC2 [MINJ2 [MATCH2 [INCR2 [SEP2 [VB2 TVB2]]]]]]]]. 
  exists f3; exists tm3.
  split. eapply corestep_star_trans; eauto.
  split. auto. split. auto. 
  split. eapply inject_incr_trans; eauto.
  split. clear EXEC2 MATCH2 EXEC1 MATCH1 IHbind_parameters.
     intros bb; intros.
       remember (f2 bb) as z; destruct z; apply eq_sym in Heqz.
       (*Some p*) destruct p.
             assert (f3 bb = Some (b0, z)). apply INCR2 in Heqz. assumption.
             rewrite H6 in H3. inv H3.
             eapply SEP1. assumption. eassumption.
       (*None*) 
             destruct (SEP2 _ _ _ Heqz H3).
             split; intros N. (*rewrite VB1 in N. apply (H6 N).*) apply H6. apply (VB1 _ N).
                 apply TVB1 in N. apply (H7 N).
  split; intros. (*rewrite VB1. apply VB2.*) apply VB2. apply (VB1 _ H2).
           apply TVB2. apply (TVB1 _ H2).
Qed.
Lemma MS_function_entry_ok:
  forall tf fn m e m1 vargs m2 j cs tm cenv tm1 sp tvargs s fn' k,
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

  (*This condition is new*)
  /\ Events.inject_separated j j' m tm

  /\ match_callstack prog j' m2 tm2
       (Frame cenv tf e empty_temp_env te sp (Mem.nextblock m) (Mem.nextblock m1) :: cs)
       (Mem.nextblock m2) (Mem.nextblock tm2).
Proof.
  intros.
  exploit MS_match_callstack_alloc_variables; eauto.
  intros [j1 [INCR1 [MINJ1 [MATCH1 [VB1 [SP1 SEP1]]]]]].
  exploit vars_vals_match_holds.
    eexact H. 
    apply val_list_inject_incr with j. eauto. eauto.
    eapply bind_parameters_normalized; eauto.
  instantiate (1 := Csharpminor.fn_temps fn). 
  fold tvars. fold ttemps. fold (fn_params_names fn). fold tparams. fold te.   
  intro VVM.
  exploit MS_store_parameters_correct.
    eauto. eauto. eauto. eapply list_norepet_append_left; eauto.
    eexact MINJ1. eexact MATCH1. eauto.
  intros [j2 [tm2 [EXEC [MINJ2 [MATCH2 [INCR2 [SEP2 [VB2 TVB2]]]]]]]].
  exists j2; exists tm2. 
  split; eauto. split; auto. split; auto. eapply inject_incr_trans; eauto.
Qed. 
*)

Lemma MS_match_callstack_alloc_variables:
  forall tm1 sp tm2 m1 vars e m2 cenv f1 cs fn le te,
  Mem.alloc tm1 0 (fn_stackspace fn) = (tm2, sp) ->
  fn_stackspace fn <= Int.max_unsigned ->
  alloc_variables empty_env m1 vars e m2 ->
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace fn) ->
  cenv_separated cenv vars ->
  (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)) ->
  Mem.inject f1 m1 tm1 ->
  match_callstack prog f1 m1 tm1 cs (Mem.nextblock m1) (Mem.nextblock tm1) ->
  match_temps f1 le te ->
  exists f2,
    match_callstack prog f2 m2 tm2 (Frame cenv fn e le te sp (Mem.nextblock m1) (Mem.nextblock m2) :: cs)
                    (Mem.nextblock m2) (Mem.nextblock tm2)
  /\ Mem.inject f2 m2 tm2
  /\ (*LENB: THIS IS NEW*) inject_incr f1 f2
  /\ (*LENB this clause in new in coop-sim proof*) inject_separated f1 f2 m1 tm1.
Proof.
  intros.
  destruct (MS_match_callstack_alloc_variables_aux
     _ _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 H5 H6 H7 H8)
     as [f2 [MCS2 [INJ2 [INC [HH1 [HH2 HH3]]]]]].
  exists f2.
  split; trivial.
  split; trivial.
  split; trivial.
  intros b; intros.
  specialize (HH2 _ _ _ H9 H10); subst.
  split. intros N. rewrite (HH1 _ N) in H10.
         rewrite H10 in H9; discriminate.
  eapply (Mem.fresh_block_alloc _ _ _ _ _ H).
Qed.

(***** All the additional conditions in the above auxiliary lemmas were needed for proving
 the condition Events.inject_separated j j' m tm in his lemma; otherwise, the claim is as before, 
  just updated by replacing star step by corestep_star, as ususal*)

Theorem MS_match_callstack_function_entry:
  forall fn cenv tf m e m' tm tm' sp f cs args targs le,
  build_compilenv fn = (cenv, tf.(fn_stackspace)) ->
  tf.(fn_stackspace) <= Int.max_unsigned ->
  list_norepet (map fst (Csharpminor.fn_vars fn)) ->
  list_norepet (Csharpminor.fn_params fn) ->
  list_disjoint (Csharpminor.fn_params fn) (Csharpminor.fn_temps fn) ->
  alloc_variables Csharpminor.empty_env m (Csharpminor.fn_vars fn) e m' ->
  bind_parameters (Csharpminor.fn_params fn) args (create_undef_temps fn.(fn_temps)) = Some le ->
  val_list_inject f args targs ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  match_callstack prog f m tm cs (Mem.nextblock m) (Mem.nextblock tm) ->
  Mem.inject f m tm ->
  let te := set_locals (Csharpminor.fn_temps fn) (set_params targs (Csharpminor.fn_params fn)) in
  exists f',
     match_callstack prog f' m' tm'
                     (Frame cenv tf e le te sp (Mem.nextblock m) (Mem.nextblock m') :: cs)
                     (Mem.nextblock m') (Mem.nextblock tm')
  /\ Mem.inject f' m' tm' 
  /\ (*LENB: this clause is new in Restructured Proof*) inject_incr f f'
  /\ (*LENB this clause in new in coop-sim proof*) inject_separated f f' m tm.
Proof.
  intros.
  exploit build_compilenv_sound; eauto. intros [C1 C2].
  eapply MS_match_callstack_alloc_variables; eauto.
  intros. eapply build_compilenv_domain; eauto.
  eapply bind_parameters_agree; eauto. 
Qed.

Lemma MS_step_case_InternalCall:
forall cenv  f j m tm e cs k tk vargs targs x m1 lenv
(Param1: list_norepet (map fst (Csharpminor.fn_vars f)))
(Param2 : list_norepet (Csharpminor.fn_params f))
(Param3 : list_disjoint (Csharpminor.fn_params f) (fn_temps f))
(AlocVars : alloc_variables empty_env m (Csharpminor.fn_vars f) e m1)
(BindParams: bind_parameters (Csharpminor.fn_params f) vargs
       (create_undef_temps (fn_temps f)) = Some lenv)
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm cs (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont k tk cenv nil cs)
(ISCC : Csharpminor.is_call_cont k)
(ARGSINJ : val_list_inject j vargs targs)
(EQ : transl_function f = OK x),
exists (c2' : CMin_core) (m2' : mem),
  corestep_plus CMin_core_sem tge (CMin_Callstate (AST.Internal x) targs tk) tm c2' m2'
 /\ exists (j' : meminj),
  inject_incr j j' /\
  inject_separated j j' m tm /\
  match_cores (CSharpMin_State f (Csharpminor.fn_body f) k e lenv) j'
    (CSharpMin_State f (Csharpminor.fn_body f) k e lenv) m1 c2' m2'.
Proof. intros.
  generalize EQ; clear EQ; unfold transl_function.
  caseEq (build_compilenv f). intros ce sz BC.
  destruct (zle sz Int.max_unsigned).
  Focus 2. intros. exfalso. clear core_data.  congruence. (*core data versus congruence bug; Xavier's proof has 
             destruct (zle sz Int.max_unsigned); try congruence here....*)
  intro TRBODY.
  generalize TRBODY; intro TMP. monadInv TMP.
  set (tf := mkfunction (Csharpminor.fn_sig f) 
                        (Csharpminor.fn_params f)
                        (Csharpminor.fn_temps f)
                        sz
                        x0) in *.
  caseEq (Mem.alloc tm 0 (fn_stackspace tf)). intros tm' sp ALLOC'.
  exploit MS_match_callstack_function_entry; eauto. simpl; eauto. simpl; auto.
  intros [j' [MCS2 [MINJ2 [IINCR SEP]]]].
  exists (CMin_State tf x0 tk (Vptr sp Int.zero)
     (set_locals (fn_temps f) (set_params targs (Csharpminor.fn_params f)))).
  exists tm'.
  split.
    eapply corestep_plus_one. simpl. 
    econstructor.
    constructor. assumption. reflexivity.
  exists j'. split. assumption.
  split. assumption. 
  econstructor. eexact TRBODY. eauto. eexact MINJ2. 
  eexact MCS2.
  inv MK; simpl in ISCC; contradiction || econstructor; eauto.
Qed.

(******************End of updated section for internal call rule*****************************)
(************************************************************************************)

Lemma MS_step_case_Return:
forall j m tm cs f e lenv k tk cenv v tv optid
(MINJ : Mem.inject j m tm)
(MCS : match_callstack prog j m tm cs (Mem.nextblock m) (Mem.nextblock tm))
(MK : match_cont (Csharpminor.Kcall optid f e lenv k) tk cenv nil cs)
(RESINJ : val_inject j v tv),
exists c2' : CMin_core,
  exists m2' : mem,
       corestep_plus CMin_core_sem tge (CMin_Returnstate tv tk) tm c2' m2'  /\
       match_cores  (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid v lenv)) j
             (CSharpMin_State f Csharpminor.Sskip k e (set_optvar optid v lenv)) m c2' m2' .
Proof. intros.
  inv MK. simpl.
  eexists; eexists; split.
       eapply corestep_plus_one. eapply CompCertStep_CMin_corestep'. econstructor; eauto. reflexivity.
  simpl.
  unfold set_optvar. destruct optid; simpl option_map; econstructor; eauto.              
         eapply match_callstack_set_temp; eauto. 
Qed. 

Lemma MS_step: forall (c1 : core_data) (m1 : mem) (c1' : core_data) (m1' : mem),
corestep CSharpMin_core_sem ge c1 m1 c1' m1' ->
forall (c2 : CMin_core) (m2 : mem) (j : meminj),
match_cores c1 j c1 m1 c2 m2 ->
(exists c2' : CMin_core,
   exists m2' : mem,
     exists j' : meminj,
       inject_incr j j' /\
       Events.inject_separated j j' m1 m2 /\
       corestep_plus CMin_core_sem tge c2 m2 c2' m2' /\
       match_cores c1' j' c1' m1' c2' m2') \/
(MC_measure c1' < MC_measure c1)%nat /\ match_cores c1' j c1' m1' c2 m2.
Proof.
  intros. unfold core_data in *.
   destruct (CSharpMin_corestep_2_CompCertStep _ _ _ _ _ H) as [t Ht]. simpl in *.
  apply CSharpMin_corestep_not_at_external in H.
   apply MC_MSI in H0. rename H0 into MSTATE.
   inv Ht; simpl in *.
  (*skip seq*)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3.
      inv MSTATE; simpl in *. 
      monadInv TR.
      destruct c2; simpl in *; try inv H8. 
      destruct (MS_step_case_SkipSeq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF MINJ MK MCS) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*skip Block*)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3. 
      inv MSTATE; simpl in *. 
      monadInv TR.
      destruct c2; simpl in *; try inv H8. 
      destruct (MS_step_case_SkipBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF MINJ MK MCS) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
  (*skip Call*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE; simpl in *. 
      monadInv TR.
      destruct c2; simpl in *; try inv H10.
      destruct (MS_step_case_SkipCall  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H4 TRF MINJ MK MCS) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
   (*assign*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H9.
      rename  m1' into m'. rename m' into m. 
      rename m2 into tm. rename k0 into tk.
      rename f0 into tfn. rename e0 into te.
      rename le0 into lenv. 
      destruct (MS_step_case_Assign  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ id H3 TRF MINJ MK MCS EQ) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
   (*set case has disappeared
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H11.
      destruct (MS_step_case_Set _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ id H3 TRF MINJ MCS MK EQ) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.*)
   (*store*)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE; simpl in *.
      monadInv TR.
      destruct c2; simpl in *; try inv H11.
      rename f0 into tfn. rename m1 into m. rename m2  into tm.
      rename e0 into te. rename k0 into tk. rename  m1' into m'.
      destruct (MS_step_case_Store _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H5 H2 H3 TRF MINJ MCS MK EQ EQ1) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
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
      destruct (MS_step_case_Call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ optid _ _ H2 H3 H4 TRF MINJ MCS MK EQ EQ1) as [c2' [m2' [cstepPlusMS]]].
      left. exists c2'. exists m2'. exists j.
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
      destruct (MS_step_case_Builtin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ optid _ _ _ _ H2 H4 TRF MINJ MCS MK EQ) as [c2' [m2' [cstepPlus [j' [InjIncr [InjSep MS]]]]]].
      left. exists c2'. exists m2'.  exists j'. auto.
  (* seq *)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3. 
     rename k0 into k.
      inv MSTATE. 
      (*Case 1*) 
         monadInv TR. left.
         destruct c2; simpl in *; try inv H8.
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
         exists  (CMin_State tfn x (Kseq x0 tk) (Vptr sp Int.zero) te). exists m2. 
         exists j. 
                split. apply inject_incr_refl.
                split. apply inject_separated_same_meminj.
                split; simpl.
                    eapply corestep_plus_one.  eapply CompCertStep_CMin_corestep.  econstructor; eauto. reflexivity. 
                econstructor; eauto.
                          econstructor; eauto.
      (* seq 2 *) 
         destruct c2; simpl in *; try inv H9.
         right. split. omega.
                   econstructor; eauto.
(* ifthenelse *)
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H10. 
         rename f0 into tfn. rename e0 into te. rename k0 into tk.
      rename m1' into m. rename m2  into tm. 
      destruct (MS_step_case_Ite _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H4 TRF MINJ MCS MK EQ EQ1 EQ0) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
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
      destruct (MS_step_case_Loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF MINJ MCS MK EQ) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
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
      destruct (MS_step_case_Block _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF MINJ MCS MK EQ) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
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
      destruct (MS_step_case_ExitSeq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n _ TRF MINJ MCS MK) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
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
      destruct (MS_step_case_ExitBlockZero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TRF MINJ MCS MK) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
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
      destruct (MS_step_case_ExitBlockNonzero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n TRF MINJ MCS MK) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
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
      destruct (MS_step_case_Switch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 TRF MINJ MCS MK EQ EQ0) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
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
      destruct (MS_step_case_ReturnNone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 TRF MINJ MCS MK) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
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
      destruct (MS_step_case_ReturnSome _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H4 TRF MINJ MCS MK EQ) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
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
      destruct (MS_step_case_Label _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lbl _ _ TRF MINJ MCS MK EQ) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
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
      destruct (MS_step_case_Goto _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H3 TRF MINJ MCS MK) as [c2' [m2' [cstepPlus MS]]].
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto.
(* internal call *) 
      destruct c1; simpl in *; try inv H0. 
      destruct c1'; simpl in *; try inv H1. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H11. 
      rename m1 into m. rename m2 into tm.
      rename f0 into f. rename e0 into e.
      rename m1' into m1. rename args into vargs.
      rename k0 into tk. rename le0 into lenv.
      rename args0 into targs.
      destruct (MS_step_case_InternalCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H3 H4 H5 H7 MINJ MCS MK ISCC ARGSINJ EQ) as [c2' [m2' [cstepPlus [j' [InjIncr [InjSep MS]]]]]].
      left. exists c2'. exists m2'. exists j'. auto.
(* external call *)
      destruct c1; simpl in *; try inv H0. inv H. 
   (*nothing to show here - cf corestep not at external *) 
 (*     destruct c1'; simpl in *; try inv H1. 
      inv MSTATE. 
      monadInv TR.
      destruct c2; simpl in *; try inv H7.  
      rename m1 into m. rename m2 into tm. 
      rename k0 into tk. rename args0 into targs.  rename m1' into m'. 
  inv MSTATE. monadInv TR. rename f into j.
  destruct (transl_step_case_ExternalCall _ _ _ _ _ _ _ _ _ _ _ _ _ H MINJ MCS MK ISCC ARGSINJ) as [T2 [Steps [j' [Inc MSI]]]].
   apply matchInj_Elim in MSI. eauto.*)

(* return *)
      destruct c1; simpl in *; try inv H1. 
      destruct c1'; simpl in *; try inv H3. 
      inv MSTATE. 
      destruct c2; simpl in *; try inv H5.
      rename m1' into m. rename m2 into tm. rename f0 into f.
      rename e0 into e. rename k into tk. rename k0 into k.
      rename v into tv. rename v0 into v.
      destruct (MS_step_case_Return _ _ _ _ _ _ _ _ _ _ _ tv optid MINJ MCS MK RESINJ) as [c2' [m2' [cstepPlus MS]]]. 
      left. exists c2'. exists m2'. exists j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      auto. 
Qed.

Require Import sepcomp.forward_simulations.

Require Import sepcomp.forward_simulations_lemmas.

(*program structure not yet updated to module*)
Theorem transl_program_correct:
  forall entrypoints, 
Forward_simulation_inj.Forward_simulation_inject CSharpMin_core_sem 
   CMin_core_sem ge tge entrypoints.
Proof.
intros.
 eapply inj_simulation_star with 
  (match_states:=match_cores)(measure:=MC_measure).
 apply match_cores_valid.
 intros. eapply (init_cores _ _ _ entrypoints); eauto.
 intros. destruct (MC_at_external _ _ _ _ _ _ _ _ _ H H0)
           as [Inc [Presv [vals2 [ValsInj [avlsHT2 AtExt2]]]]].
    split; trivial.
    split; trivial.
    exists vals2. 
    split; trivial.
    split; trivial.
    split; trivial.
    admit. (*val_valid*)
 intros. 
    destruct (MC_after_external _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0
             H1 H2 H3 H4 H5 H6 H7 H8 H9 H11)
           as [dd [core [dd' [afterExtA [afterExtB [ MC X]]]]]].
     subst. eexists; eexists. eexists.
        split. eassumption.
        split. eassumption.
        split. reflexivity. eassumption.
  intros. destruct (MS_step _ _ _ _ H _ _ _ H0).
   destruct H1 as [c2' [m2' [j' [INC [Sep [CSP MC]]]]]].
      exists c2', m2', j'. 
       split; trivial.
       split; trivial.
       split; trivial.
       left; trivial. 
    destruct H1. 
      exists c2, m2, j.
      split. apply inject_incr_refl.
      split. apply inject_separated_same_meminj.
      split; trivial.
      right. split; trivial.
      apply corestep_star_zero. 
Qed.

(*Later, we could lift this the csharpmin_coop etc*)

End TRANSLATION.