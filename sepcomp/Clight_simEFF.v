Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Memory.
Require Export Axioms.
Require Import Errors.
Require Import Events.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Export Maps.
Require Import Cop. (*for sem_cast*)
Require Import Ctypes. (*for access_mode*)
Require Import Clight.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.
Require Import Clight_new.
Require Import Clightnew_coop.
Require Import sepcomp.Clightnew_eff.
Require Import Clight_coop.
Require Import sepcomp.Clight_eff.

Fixpoint strip_skip' (k: Clight.cont) : Clight.cont :=
 match k with 
 | Clight.Kseq Sskip k' => strip_skip' k' 
 | _ => k 
 end.

Inductive match_cont:  Clight_new.cont -> Clight.cont -> Prop :=
  | match_cont_nil: match_cont nil Clight.Kstop
  | match_cont_seq: forall s k k',
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kseq s :: k) (Clight.Kseq s k')
  | match_cont_loop1: forall e3 s k k',
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kseq Scontinue :: Kloop1 s e3 :: k) (Clight.Kloop1 s e3 k')
  | match_cont_loop2: forall e3 s k k',
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kloop2 s e3 :: k) (Clight.Kloop2 s e3 k')
  | match_cont_switch: forall k k',
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kswitch :: k) (Clight.Kswitch k')
  | match_cont_call: forall lid fd f ve te k k'
         (CUR: current_function k = Some f),
         match_cont (strip_skip k) (strip_skip' k') ->
          match_cont (Kseq (Sreturn None) :: Kcall lid fd ve te :: k) 
                     (Clight.Kcall lid f ve te k').

(*Lenb: always offset 0*)
Definition match_env (j: meminj) (ve ve':env) :=
  forall id, 
  match ve!id with
    None => ve'!id=None
  | Some(b,ty) => exists b', j b = Some(b',0) /\ ve'!id=Some(b',ty)
  end.

Definition match_tenv (j: meminj) (te te':temp_env) :=
  forall id v, te!id = Some v ->
  exists v', val_inject j v v' /\ te'!id=Some v'.
     

Inductive match_states: forall (d:corestate) (mu: SM_Injection)
                               (qm: corestate) (m:mem) (st: CL_core) (m':mem), Prop :=
 | match_states_seq: forall d mu f ve ve' te' te s k k' m m' 
      (ENV: match_env (restrict (as_inj mu) (vis mu)) ve ve')
      (TENV: match_tenv (restrict (as_inj mu) (vis mu)) te te')
      (CUR: current_function k = Some f),
      match_cont (strip_skip k) (strip_skip' (Clight.Kseq s k')) ->
      match_states d mu (State ve te k) m (CL_State f s k' ve' te') m'
 | match_states_ext: forall d mu k f ef tyargs tyres args args' lid ve ve' te te' k' m m'
      (ENV: match_env (restrict (as_inj mu) (vis mu)) ve ve')
      (TENV: match_tenv (restrict (as_inj mu) (vis mu)) te te')
      (ARGS: val_list_inject (restrict (as_inj mu) (vis mu)) args args')
      (CUR: current_function k = Some f),
      match_cont (strip_skip k) (strip_skip' k') ->
      match_states d mu (ExtCall ef (signature_of_type tyargs tyres) args lid ve te k) m 
           (CL_Callstate (External ef tyargs tyres) args' (Clight.Kcall lid f ve' te' k')) m'.


Definition MATCH (ge:Clight.genv) d mu (c1:corestate) m1 (c2:CL_core) m2:Prop :=
  match_states d mu c1 m1 c2 m2 (*(restrict_sm mu (vis mu)) doesn't work here, since 
                              some of the conditions of match_env are "global"*) /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\
  Mem.inject (as_inj mu) m1 m2.

Lemma MATCH_sm_wd: forall ge d mu c1 m1 c2 m2, 
          MATCH ge d mu c1 m1 c2 m2 -> 
          SM_wd mu.
Proof. intros. apply H. Qed.

Lemma MATCH_genv: forall ge d mu c1 m1 c2 m2
                  (MC:MATCH ge d mu c1 m1 c2 m2),
          meminj_preserves_globals ge (extern_of mu) /\
          (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
Proof.
  intros.
  assert (WD:= MATCH_sm_wd _ _ _ _ _ _ _ MC).
  assert (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
    apply MC.
  split; trivial.
  rewrite <- match_genv_meminj_preserves_extern_iff_all; trivial.
    apply MC.
Qed.

Lemma MATCH_visible: forall ge d mu c1 m1 c2 m2, 
          MATCH ge d mu c1 m1 c2 m2 -> 
          REACH_closed m1 (vis mu).
Proof. intros. apply H. Qed.

Lemma match_states_restrict: forall d mu c1 m1 c2 m2 
        (MC : match_states d mu c1 m1 c2 m2)
        (X : block -> bool)
        (HX : forall b : block, vis mu b = true -> X b = true),
      match_states d (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  inv MC. 
  econstructor; trivial.
    rewrite vis_restrict_sm.
      rewrite restrict_sm_all.
      rewrite restrict_nest; try assumption.
    rewrite vis_restrict_sm.
      rewrite restrict_sm_all.
      rewrite restrict_nest; assumption.
  econstructor; trivial.
    rewrite vis_restrict_sm.
      rewrite restrict_sm_all.
      rewrite restrict_nest; assumption.
    rewrite vis_restrict_sm.
      rewrite restrict_sm_all.
      rewrite restrict_nest; assumption.
    rewrite vis_restrict_sm.
      rewrite restrict_sm_all.
      rewrite restrict_nest; assumption.
Qed.

Lemma MATCH_restrict: forall ge d mu c1 m1 c2 m2 X
          (MC: MATCH ge d mu c1 m1 c2 m2)
          (HX: forall b, vis mu b = true -> X b = true)
          (RC: REACH_closed m1 X),
          MATCH ge d (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  destruct MC as [MC [RCLocs [PG [Glob [SMV [WD INJ]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split. eapply match_states_restrict; eassumption.
split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RCLocs.
split. clear -PG HX Glob.
  eapply restrict_sm_preserves_globals; try eassumption.
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
eapply inject_mapped. eassumption.
    rewrite restrict_sm_all.
      apply inject_REACH_closed in INJ.
      apply (restrict_mapped_closed _ _ _ INJ RC).
    rewrite restrict_sm_all.
      apply (restrict_incr (as_inj mu) X). 
Qed.

Lemma MATCH_validblocks: forall ge d mu c1 m1 c2 m2, 
      MATCH ge d mu c1 m1 c2 m2 -> sm_valid mu m1 m2.
Proof. intros. apply H. Qed.

Lemma MATCH_at_external: forall ge mu st1 m1 st2 m2 e vals1 sig
     (MC: match_states ge mu st1 m1 st2 m2) 
     (AtExt: at_external cln_eff_sem st1 = Some (e, sig, vals1)),
  exists vals2, Forall2 (val_inject (as_inj mu)) vals1 vals2 /\
                at_external CL_eff_sem2 st2 = Some (e, sig, vals2).
Proof.
  intros. 
  inv MC; simpl in *; inv AtExt.
  exists args'.
  split. eapply forall_vals_inject_restrictD. 
           apply val_list_inject_forall_inject; eassumption.
  simpl. admit. (*TODO inv TR. trivial.*)
Qed.

Lemma match_env_after_external: forall ve ve' mu  m1'
      (ENV : match_env
        (restrict (as_inj mu)
           (fun b : block => locBlocksSrc mu b || frgnBlocksSrc mu b)) ve ve')
      PubS PubT nu' L (INC : extern_incr (replace_locals mu PubS PubT) nu')
      (WDnu': SM_wd nu'),
     match_env (restrict (as_inj nu')
     (fun b : block =>
         locBlocksSrc nu' b
        || DomSrc nu' b &&
           (negb (locBlocksSrc nu' b) &&
            REACH m1' (exportedSrc nu' L) b))) ve ve'.
Proof. intros. red; intros.
 specialize (ENV id).
 remember (ve ! id) as d.
 destruct d; trivial. 
 destruct p. destruct ENV as [bb [RE VE']].
 rewrite VE'. exists bb; split; trivial.
 destruct (restrictD_Some _ _ _ _ _ RE).
         apply restrictI_Some.
           apply extern_incr_as_inj in INC; trivial.
           rewrite replace_locals_as_inj in INC.
           apply INC; assumption.
         assert (LB: locBlocksSrc (replace_locals mu PubS PubT)
                  = locBlocksSrc nu'). eapply INC. 
         rewrite <- LB; clear LB. rewrite replace_locals_locBlocksSrc. 
         remember (locBlocksSrc mu b) as d.
         destruct d; trivial; apply eq_sym in Heqd; simpl in *.
         apply andb_true_iff.
         assert (frgnBlocksSrc nu' b = true).
           eapply INC. rewrite replace_locals_frgnBlocksSrc. assumption.
         split. 
           unfold DomSrc. apply frgnBlocksSrc_extBlocksSrc in H1; trivial. intuition.
         apply REACH_nil. unfold exportedSrc.
           apply frgnSrc_shared in H1; trivial. intuition.
Qed.

Lemma match_temp_env_after_external: forall te te' mu  m1'
      (TENV : match_tenv
         (restrict (as_inj mu)
            (fun b : block => locBlocksSrc mu b || frgnBlocksSrc mu b)) te
         te')
      PubS PubT nu' (INC : extern_incr (replace_locals mu PubS PubT) nu')
     (WDnu': SM_wd nu') ret1 ret2 x
     (VI: val_inject (as_inj nu') ret1 ret2),
     match_tenv
       (restrict (as_inj nu')
            (fun b : block =>
              locBlocksSrc nu' b
               || DomSrc nu' b &&
                (negb (locBlocksSrc nu' b) &&
              REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
       (PTree.set x ret1 te)
       (set_opttemp (Some x) ret2 te').
Proof. intros. red; intros. rewrite PTree.gsspec in H.
      destruct (peq id x); subst; simpl. inv H.
        exists ret2. split.
          eapply restrict_val_inject; try eassumption.
          intros.
          destruct (getBlocks_inject (as_inj nu') (v::nil) (ret2::nil))
             with (b:=b) as [bb [dd [JJ' GBbb]]]; try eassumption.
            constructor. assumption. constructor.
          remember (locBlocksSrc nu' b) as d.
          destruct d; simpl; trivial. apply andb_true_iff.
          split. eapply as_inj_DomRng; eassumption.
          apply REACH_nil. unfold exportedSrc.
            rewrite H. trivial.
        rewrite PTree.gss. trivial.
      destruct (TENV _ _ H) as [v' [RE VE']].
         exists v'.
         split. eapply val_inject_incr; try eassumption.
            red; intros.
            destruct (restrictD_Some _ _  _ _ _ H0).
            apply restrictI_Some.
              apply extern_incr_as_inj in INC; trivial.
              rewrite replace_locals_as_inj in INC.
              apply INC; assumption.
            assert (LB: locBlocksSrc (replace_locals mu PubS PubT)
                       = locBlocksSrc nu'). eapply INC.  
           rewrite <- LB; clear LB. rewrite replace_locals_locBlocksSrc. 
           remember (locBlocksSrc mu b) as d.
           destruct d; trivial; apply eq_sym in Heqd; simpl in *.
           apply andb_true_iff.
           assert (frgnBlocksSrc nu' b = true).
             eapply INC. rewrite replace_locals_frgnBlocksSrc. assumption.
           split. 
             unfold DomSrc. apply frgnBlocksSrc_extBlocksSrc in H3; trivial. intuition.
           apply REACH_nil. unfold exportedSrc.
             apply frgnSrc_shared in H3; trivial. intuition.
         rewrite PTree.gso; assumption.
Qed.

Lemma MATCH_after_external: 
forall ge mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
      (MemInjMu : Mem.inject (as_inj mu) m1 m2)
      (MatchMu : MATCH ge st1 mu st1 m1 st2 m2)
      (AtExtSrc : at_external cln_eff_sem st1 = Some (e, ef_sig, vals1))
      (AtExtTgt : at_external CL_eff_sem2 st2 = Some (e', ef_sig', vals2))
      (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2)
      (pubSrc' : block -> bool)
      (pubSrcHyp : pubSrc' =
            (fun b : block =>
             locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
      (pubTgt' : block -> bool)
      (pubTgtHyp : pubTgt' =
            (fun b : block =>
             locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
      nu (NuHyp : nu = replace_locals mu pubSrc' pubTgt')
      nu' ret1 m1' ret2 m2'
      (INC : extern_incr nu nu')
      (SEP : sm_inject_separated nu nu' m1 m2)
      (WDnu' : SM_wd nu')
      (SMvalNu' : sm_valid nu' m1' m2')
      (MemInjNu' : Mem.inject (as_inj nu') m1' m2')
      (RValInjNu' : val_inject (as_inj nu') ret1 ret2)
      (FwdSrc : mem_forward m1 m1')
      (FwdTgt : mem_forward m2 m2')
      (frgnSrc' : block -> bool)
      (frgnSrcHyp : frgnSrc' =
             (fun b : block =>
              DomSrc nu' b &&
              (negb (locBlocksSrc nu' b) &&
               REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
      (frgnTgt' : block -> bool)
      (frgnTgtHyp : frgnTgt' =
             (fun b : block =>
              DomTgt nu' b &&
              (negb (locBlocksTgt nu' b) &&
               REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
      mu' (Mu'Hyp : mu' = replace_externs nu' frgnSrc' frgnTgt')
      (UnchPrivSrc : Mem.unchanged_on
                (fun (b : Values.block) (_ : Z) =>
                 locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1
                m1'),
exists (st1' : corestate) (st2' : CL_core),
  after_external cln_eff_sem (Some ret1) st1 = Some st1' /\
  after_external CL_eff_sem2 (Some ret2) st2 = Some st2' /\
  MATCH ge st1' mu' st1' m1' st2' m2'.
Proof. intros. 
 destruct MatchMu as [MC [RC [PG [GF [VAL [WDmu INJ]]]]]].
 (*assert (PGG: meminj_preserves_globals (Genv.globalenv prog)
                  (restrict (as_inj mu) (vis mu))).
      eapply restrict_preserves_globals; try eassumption.
        unfold vis; intuition.*)
 inv MC; simpl in *; inv AtExtSrc.
assert (exists x, lid = Some x). admit. (*TODO: the 2 languages use slightly different afterExternal conditions *) 
destruct H0; subst lid. 
 inv AtExtTgt.
  eexists. eexists.
    split. reflexivity.
    split. reflexivity.
(*rename PG0 into PGRestrictMu.*)
assert (INCvisNu': inject_incr
  (restrict (as_inj nu')
     (vis
        (replace_externs nu'
           (fun b : Values.block =>
            DomSrc nu' b &&
            (negb (locBlocksSrc nu' b) &&
             REACH m1' (exportedSrc nu' (ret1 :: nil)) b))
           (fun b : Values.block =>
            DomTgt nu' b &&
            (negb (locBlocksTgt nu' b) &&
             REACH m2' (exportedTgt nu' (ret2 :: nil)) b))))) (as_inj nu')).
      unfold vis. rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc.
      apply restrict_incr. 
assert (RC': REACH_closed m1' (mapped (as_inj nu'))).
        eapply inject_REACH_closed; eassumption.
assert (PHnu': meminj_preserves_globals ge (as_inj nu')).
    subst. clear - INC SEP PG GF WDmu WDnu'.
    apply meminj_preserves_genv2blocks in PG.
    destruct PG as [PGa [PGb PGc]].
    apply meminj_preserves_genv2blocks.
    split; intros.
      specialize (PGa _ H).
      apply joinI; left. apply INC.
      rewrite replace_locals_extern.
      assert (GG: isGlobalBlock ge b = true).
          unfold isGlobalBlock. apply genv2blocksBool_char1 in H.
          rewrite H. trivial.
      destruct (frgnSrc _ WDmu _ (GF _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGa. inv PGa.
      apply foreign_in_extern; eassumption.
    split; intros. specialize (PGb _ H).
      apply joinI; left. apply INC.
      rewrite replace_locals_extern.
      assert (GG: isGlobalBlock ge b = true).
          unfold isGlobalBlock. apply genv2blocksBool_char2 in H.
          rewrite H. intuition.
      destruct (frgnSrc _ WDmu _ (GF _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGb. inv PGb.
      apply foreign_in_extern; eassumption.
    eapply (PGc _ _ delta H). specialize (PGb _ H). clear PGa PGc.
      remember (as_inj mu b1) as d.
      destruct d; apply eq_sym in Heqd.
        destruct p. 
        apply extern_incr_as_inj in INC; trivial.
        rewrite replace_locals_as_inj in INC.
        rewrite (INC _ _ _ Heqd) in H0. trivial.
      destruct SEP as [SEPa _].
        rewrite replace_locals_as_inj, replace_locals_DomSrc, replace_locals_DomTgt in SEPa. 
        destruct (SEPa _ _ _ Heqd H0).
        destruct (as_inj_DomRng _ _ _ _ PGb WDmu).
        congruence.
assert (RR1: REACH_closed m1'
  (fun b : Values.block =>
   locBlocksSrc nu' b
   || DomSrc nu' b &&
      (negb (locBlocksSrc nu' b) &&
       REACH m1' (exportedSrc nu' (ret1 :: nil)) b))).
  intros b Hb. rewrite REACHAX in Hb. destruct Hb as [L HL].
  generalize dependent b.
  induction L; simpl; intros; inv HL.
     assumption.
  specialize (IHL _ H2); clear H2.
  apply orb_true_iff in IHL.
  remember (locBlocksSrc nu' b') as l.
  destruct l; apply eq_sym in Heql.
  (*case locBlocksSrc nu' b' = true*)
    clear IHL.
    remember (pubBlocksSrc nu' b') as p.
    destruct p; apply eq_sym in Heqp.
      assert (Rb': REACH m1' (mapped (as_inj nu')) b' = true).
        apply REACH_nil. 
        destruct (pubSrc _ WDnu' _ Heqp) as [bb2 [dd1 [PUB PT]]].
        eapply mappedI_true.
         apply (pub_in_all _ WDnu' _ _ _ PUB).
      assert (Rb:  REACH m1' (mapped (as_inj nu')) b = true).
        eapply REACH_cons; try eassumption.
      specialize (RC' _ Rb).
      destruct (mappedD_true _ _ RC') as [[b2 d1] AI'].
      remember (locBlocksSrc nu' b) as d.
      destruct d; simpl; trivial.
      apply andb_true_iff. 
      split. eapply as_inj_DomRng; try eassumption.
      eapply REACH_cons; try eassumption.
        apply REACH_nil. unfold exportedSrc.
        rewrite (pubSrc_shared _ WDnu' _ Heqp). intuition.
      destruct UnchPrivSrc as [UP UV].
        specialize (UP b' z Cur Readable). 
        specialize (UV b' z). 
        destruct INC as [_ [_ [_ [_ [LCnu' [_ [PBnu' [_ [FRGnu' _]]]]]]]]].
        rewrite <- LCnu'. rewrite replace_locals_locBlocksSrc.  
        rewrite <- LCnu' in Heql. rewrite replace_locals_locBlocksSrc in *.
        rewrite <- PBnu' in Heqp. rewrite replace_locals_pubBlocksSrc in *.
        clear INCvisNu'. 
        rewrite Heql in *. simpl in *. intuition.
        assert (VB: Mem.valid_block m1 b').
          eapply VAL. unfold DOM, DomSrc. rewrite Heql. intuition.
        apply (H0 VB) in H3.
        rewrite (H1 H3) in H5.
        remember (locBlocksSrc mu b) as q.
        destruct q; simpl; trivial; apply eq_sym in Heqq.
        assert (Rb : REACH m1 (vis mu) b = true).
           eapply REACH_cons; try eassumption.
           apply REACH_nil. unfold vis. rewrite Heql; trivial.
        specialize (RC _ Rb). unfold vis in RC.
           rewrite Heqq in RC; simpl in *.
        assert (frgnBlocksSrc nu' b = true).
          apply FRGnu'. rewrite replace_locals_frgnBlocksSrc. assumption.
        apply andb_true_iff.  
        split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H2). intuition.
        apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ H2). intuition.
  (*case DomSrc nu' b' &&
    (negb (locBlocksSrc nu' b') &&
     REACH m1' (exportedSrc nu' (ret1 :: nil)) b') = true*)
    destruct IHL. discriminate.
    apply andb_true_iff in H0. simpl in H0. 
    destruct H0 as[DomNu' Rb']. 
    clear INC SEP INCvisNu' UnchPrivSrc.
    remember (locBlocksSrc nu' b) as d.
    destruct d; simpl; trivial. apply eq_sym in Heqd.
    apply andb_true_iff.
    split. assert (RET: Forall2 (val_inject (as_inj nu')) (ret1::nil) (ret2::nil)).
              constructor. assumption. constructor.
           destruct (REACH_as_inj _ WDnu' _ _ _ _ MemInjNu' RET
               _ Rb' (fun b => true)) as [b2 [d1 [AI' _]]]; trivial.
           assert (REACH m1' (mapped (as_inj nu')) b = true).
             eapply REACH_cons; try eassumption.
             apply REACH_nil. eapply mappedI_true; eassumption.
           specialize (RC' _ H0). 
           destruct (mappedD_true _ _ RC') as [[? ?] ?].
           eapply as_inj_DomRng; eassumption.
    eapply REACH_cons; try eassumption.
(*assert (RRR: REACH_closed m1' (exportedSrc nu' (ret1 :: nil))).
    intros b Hb. apply REACHAX in Hb.
       destruct Hb as [L HL].
       generalize dependent b.
       induction L ; simpl; intros; inv HL; trivial.
       specialize (IHL _ H1); clear H1.
       unfold exportedSrc.
       eapply REACH_cons; eassumption.*)
    
assert (RRC: REACH_closed m1' (fun b : Values.block =>
                         mapped (as_inj nu') b &&
                           (locBlocksSrc nu' b
                            || DomSrc nu' b &&
                               (negb (locBlocksSrc nu' b) &&
                           REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))).
  eapply REACH_closed_intersection; eassumption.
assert (GFnu': forall b, isGlobalBlock ge b = true ->
               DomSrc nu' b &&
               (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b) = true).
     intros. specialize (GF _ H0).
       assert (FF: frgnBlocksSrc nu' b = true).
           eapply INC. rewrite replace_locals_frgnBlocksSrc. eassumption.
       rewrite (frgnBlocksSrc_locBlocksSrc _ WDnu' _ FF). 
       apply andb_true_iff; simpl.
        split.
          unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ FF). intuition.
          apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ FF). intuition.
split. 
  econstructor; try eassumption.
    unfold vis in *. rewrite replace_externs_as_inj.
      rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc in *.
      eapply match_env_after_external; try eassumption.
    unfold vis in *. rewrite replace_externs_as_inj.
      rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc in *.
      eapply match_temp_env_after_external; try eassumption.
unfold vis.
rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj.
destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu' 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
intuition.
Qed.

Lemma exec_skips_CL:
 forall {s0 k s k'} 
   (H1: match_cont (Kseq s0 :: k) (strip_skip' (Clight.Kseq s k')))
   ge f ve te m,
   match s0 with Sskip => False | Scontinue => False | Sloop _ _ => False 
            | Sifthenelse _ _ _ => False | Sreturn _ => False 
            | _ => True end ->
   exists k2, strip_skip' (Clight.Kseq s k') = Clight.Kseq s0 k2 /\
     corestep_star CL_core_sem2 ge  (CL_State f s k' ve te) m 
              (CL_State f s0 k2 ve te) m.
Proof.
 intros.
(*proof using  exec_skips is not expected to work since conversion CCstep to CC_step is only possible for nonAtexternal states
assert (ZZ:= exec_skips H1 ge f ve te m H). clear H.
  destruct ZZ as [k2 [K1 K2]].
 exists k2. split; trivial.*)

 remember (Clight.Kseq s k') as k0.
 revert k s k' H1 Heqk0; induction k0; intros; inv Heqk0.
 assert ({s1=Sskip}+{s1<>Sskip}) by (destruct s1; try (left; congruence); right; congruence). 
 destruct H0.
 (*s1 = Sskip*)  subst s1.
      destruct k'; try solve [inv H1].
      (*1/3*) specialize (IHk0 _ s k' H1 (eq_refl _)).
                   destruct IHk0 as [k2 [? ?]].
                   exists k2. split; simpl; auto.
                   (*old proof. i.e used in exec_skips: econstructor 2. constructor. eauto. auto.*)
                   clear - H2. destruct H2 as [n Hn]. exists (S n). simpl.
                     eexists. eexists. split. Focus 2. apply Hn.
                                                          constructor.
     (*2/3*) inv H1; contradiction.
     (*3/3*) simpl in H1. inv H1. contradiction.
(*s1 <> Sskip*)
   replace (strip_skip' (Clight.Kseq s1 k')) with (Clight.Kseq s1 k')  in *
       by (destruct s1; try congruence; auto).
  clear - H H1.
   inv H1. exists k'; split; auto.  exists O. reflexivity.
Qed.

Section EXPREVALINJECT.
Variable ge: genv.
Variable ve: env.
Variable ve': env.
Variable te: temp_env.
Variable te': temp_env.
Variable m: mem.
Variable m': mem.
Variable j: meminj.
Hypothesis ENV : match_env j ve ve'.
Hypothesis TENV : match_tenv j te te'.
Hypothesis MINJ: Mem.inject j m m'.
Hypothesis PG: meminj_preserves_globals ge j.

Lemma transl_unop_correct:
  forall op ty u v u',
  sem_unary_operation op u ty = Some v ->
  val_inject j u u' ->
  exists v', val_inject j v v' /\
  sem_unary_operation op u' ty = Some v'.
Proof.
  intros. destruct op; simpl in *.
  destruct u; inv H; simpl in *.
  eapply make_notbool_correct; eauto. 
  eapply make_notint_correct; eauto. 
  eapply make_neg_correct; eauto.
Qed.*)

Lemma transl_expr_lvalue_correct:
  (forall a v,
   eval_expr ge ve te m a v ->
   exists tv, val_inject j v tv /\
   eval_expr ge ve' te' m' a tv)
/\(forall a b ofs,
      eval_lvalue ge ve te m a b ofs ->
      exists b' ofs',
        eval_lvalue ge ve' te' m' a b' ofs' /\
        val_inject j (Vptr b ofs) (Vptr b' ofs')).
Proof.
apply eval_expr_lvalue_ind; intros. 
  eexists; split.  
    econstructor.
    econstructor.
  eexists; split.  
    econstructor.
    econstructor.
  eexists; split.  
    econstructor.
    econstructor.
  destruct (TENV _ _ H) as [v' [? ?]].
    exists v'; split; trivial.  
    econstructor. trivial.
  destruct H0 as [b' [ofs' [? ?]]].
    exists (Vptr b' ofs'); split; trivial.  
    econstructor. trivial.
  destruct H0 as [tv [? ?]].
    eexists; split.
     Focus 2. econstructor. eassumption.
          simpl.  
    econstructor. trivial.
    econstructor.

  specialize (ENV id). 
    rewrite H in ENV. destruct ENV as [loc' [? ?]].
    eexists; eexists.
    split. eapply eval_Evar_local; eassumption.
           econstructor. eassumption.
           rewrite Int.add_zero. trivial.
  specialize (ENV id). 
    rewrite H in ENV. 
    eexists; eexists.
    split. eapply eval_Evar_global; try eassumption.
      apply meminj_preserves_genv2blocks in PG.
      destruct PG. specialize (H2 loc). 
        econstructor. apply H2. 
        simpl.  exists id; trivial.
        rewrite Int.add_zero. trivial.
   
   eval_Ederef  meminj_preserves_globals_ind in PG.
    
  destruct (ENV _ _ _ H) as [loc' [? ?]].
    eexists; eexists.
    split. econstructor. eassumption.
           econstructor. eassumption.
           rewrite Int.add_zero. trivial.econstructor. eassumption.
           econstructor. eassumption.
           rewrite Int.add_zero. trivial.
  

Lemma MATCH_corestep: forall ge st1 m1 st1' m1'
        (CS: corestep cln_eff_sem ge st1 m1 st1' m1')
        st2 mu m2
        (MTCH :MATCH ge st1 mu st1 m1 st2 m2),
      exists st2' m2' mu',
  corestep_plus CL_eff_sem2 ge st2 m2 st2' m2' /\
  intern_incr mu mu' /\
  sm_inject_separated mu mu' m1 m2 /\
  sm_locally_allocated mu mu' m1 m2 m1' m2' /\
  MATCH ge st1' mu' st1' m1' st2' m2' /\
  SM_wd mu' /\
  sm_valid mu' m1' m2'.
Proof.
  intros. inv CS.
{ (* step_assign *)
  destruct MTCH as [MS INV].
  inv MS. simpl strip_skip in H12.   
  destruct (exec_skips_CL H12 ge f ve' te' m2) as [k2 [? ?]]; auto.
  exists (CL_State f Sskip k2 ve' te'). exists m2. exists mu.
  split.
       eapply corestep_star_plus_trans. eassumption.
              eapply corestep_plus_one. 
       econstructor.
constructor; auto.
rewrite H4 in H9. inv H9; auto.

  (*skip seq*)

Section TRANSLATION.
Variable prog: Clight.program.
(*Variable tprog: Clight.program.
Hypothesis TRANSL: transl_program prog = OK tprog.
*)
Let ge : Clight.genv := Genv.globalenv prog.
(*Let tge: genv := Genv.globalenv tprog.*)


Theorem transl_program_correct:
  forall  (R: list_norepet (map fst (prog_defs prog)))
         entrypoints
         (entry_points_ok : 
            forall v1 v2 sig,
              In (v1, v2, sig) entrypoints -> 
              exists b f1 f2, 
                v1 = Vptr b Int.zero 
                /\ v2 = Vptr b Int.zero
                /\ Genv.find_funct_ptr ge b = Some f1
                /\ Genv.find_funct_ptr ge b = Some f2)
         (init_mem: exists m0, Genv.init_mem prog = Some m0),
SM_simulation.SM_simulation_inject cln_eff_sem
   CL_eff_sem2 ge ge entrypoints.
Proof.
intros.
assert (GDE: genvs_domain_eq ge ge).
    unfold genvs_domain_eq, genv2blocks. intuition.
  pose (bogus_measure := (fun x: corestate => O)).
 eapply sepcomp.effect_simulations_lemmas.inj_simulation_plus with
  (match_states:=MATCH ge) (measure:=bogus_measure)(*(measure:=MC_measure)*).
(*genvs_dom_eq*)
  apply GDE.
(*match_wd*)
  apply MATCH_sm_wd.
(*match_visible*)
  apply MATCH_visible.
(*match_restrict*)
  apply MATCH_restrict.
(*match_valid*)
  apply MATCH_validblocks.
(*match_genv*)
  apply MATCH_genv.
(*initial_core*)
  { admit. (*TODO: match_init
  intros. eapply Match_init_core; try eassumption.
   destruct init_mem as [m0 INIT].
   exists m0; split; trivial.
   unfold meminj_preserves_globals in H3.    
   destruct H3 as [A [B C]].
   assert (P: forall p q, {Ple p q} + {Plt q p}).
        intros p q.
        case_eq (Pos.leb p q).
        intros TRUE.
        apply Pos.leb_le in TRUE.
        left; auto.
        intros FALSE.
        apply Pos.leb_gt in FALSE.
        right; auto.

      cut (forall b, Plt b (Mem.nextblock m0) -> 
             exists id, Genv.find_symbol ge id = Some b). intro D.
    
      split.
      destruct (P (Mem.nextblock m0) (Mem.nextblock m1)); auto.
      exfalso. 
      destruct (D _ p).
      apply A in H3.
      assert (VB: Mem.valid_block m1 (Mem.nextblock m1)).
        eapply Mem.valid_block_inject_1; eauto.
      clear - VB; unfold Mem.valid_block in VB.
      xomega.

      destruct (P (Mem.nextblock m0) (Mem.nextblock m2)); auto.
      exfalso. 
      destruct (D _ p).
      apply A in H3.
      assert (VB:Mem.valid_block m2 (Mem.nextblock m2)).
        eapply Mem.valid_block_inject_2; eauto.
      clear - VB; unfold Mem.valid_block in VB.
      xomega.

      intros b LT.    
      unfold ge.
      apply valid_init_is_global with (b := b) in INIT.
      eapply INIT; auto.
      apply R.
      apply LT.*) }
(*halted*) 
  { intros. destruct H as [MC [RC [PG [GF [VAL [WD INJ]]]]]]. 
    admit. (*This proof works by I thin the definition of
              match_states in incomplete 
           inv MC; simpl in *. simpl in H0. inv H0.*) }
(* at_external*)
  { intros. destruct H as [MC [RC [PG [GF [VAL [WD INJ]]]]]].
    split; trivial.
    eapply MATCH_at_external; eassumption. }
(* after_external*)
  { intros.
    eapply (MATCH_after_external ge mu st1 st2 m1 e vals1 m2 
             ef_sig vals2 e' ef_sig') with
            (pubSrc':=pubSrc') (pubTgt':=pubTgt') 
            (frgnSrc':=frgnSrc') (frgnTgt':=frgnTgt')
            (nu:=nu) (nu':=nu') (mu':=mu');
     try assumption; try reflexivity. }
(* Match_corestep*)
  { apply Match_corestep. }
(* Match_effect_diagram *)
  { admit. (* ok - we're not proving the Match_effect_diagram clause*)}
(* effcore_diagram_strong*)
  { admit. (* ok - we're not proving the _diagram_strong clause*) }
(* effcore_diagram_strong_perm*)
  { apply Match_eff_diagram_strong_perm. }
Qed.
End TRANSLATION.


