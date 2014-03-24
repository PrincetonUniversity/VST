Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Axioms.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import core_semantics.
Require Import effect_semantics.

Require Import sepcomp.mem_lemmas. (*for genvs_domain_eq*)
Require Import StructuredInjections. (*for freshloc*)
Require Import effect_simulations. (*for isGlobalBlock*)

Definition merge_LocExt (mu12 mu':SM_Injection): SM_Injection :=
  Build_SM_Injection (locBlocksSrc mu12) (locBlocksTgt mu12)
                     (pubBlocksSrc mu12) (pubBlocksTgt mu12)
                     (local_of mu12)
                     (extBlocksSrc mu') (extBlocksTgt mu')
                     (frgnBlocksSrc mu12) (frgnBlocksTgt mu12)
                     (extern_of mu').

Lemma merge_locExt_WD mu12 mu': forall
      (WD12: SM_wd mu12) (WD': SM_wd mu')
      (EI: extern_incr mu12 mu'),
      SM_wd (merge_LocExt mu12 mu').
Proof. intros.
   destruct EI as [EI1 [EI2 [EI3 [EI4 [EI5 [EI6 [EI7 [EI8 [EI9 EI10]]]]]]]]].
   split; simpl; try eapply WD12; try eapply WD'. 
   intros. rewrite EI5. eapply WD'.
   intros. rewrite EI6. eapply WD'.
   intros. destruct (frgnSrcAx _ WD12 _ H) as [b2 [d [F T]]].
     apply EI1 in F. exists b2, d. split; trivial. 
   intros. apply EI4. apply (frgnBlocksExternTgt _ WD12 _ H). 
Qed.

(*There's no need to distinguish between SRC and TGT language, 
  nor to maintain injections local/extern*)
Record SM_Equality:=
  { locBlocks : block -> bool;
       (* The blocks allocated by THIS module*)
    pubBlocks : block -> bool; (*subset of locBlocks that have been 
                        made public. *)
    extBlocks: block -> bool; (*blocks allocated by OTHER modules*)
    frgnBlocks: block -> bool (*subset of extBlocksSrc that have been 
                        made visible to THIS module.*)
}.

Record SE_wd (mu:SM_Equality):Prop := {
  disjoint_extern_local_Blocks: forall b, locBlocks mu b = false \/ extBlocks mu b = false;
  pubBlocksAx: forall b, pubBlocks mu b = true -> locBlocks mu b = true;
  frgnBlocksAx: forall b, frgnBlocks mu b = true -> extBlocks mu b = true
}.

Definition Blocks (mu: SM_Equality) (b: block): bool := 
     locBlocks mu b || extBlocks mu b.
  
Definition se_valid (mu : SM_Equality) (m: mem) :=
       forall b, Blocks mu b = true -> Mem.valid_block m b.

Definition visEq mu b:= locBlocks mu b || frgnBlocks mu b.

Definition restrict_se mu (X:block -> bool) :=
  Build_SM_Equality 
     (fun b => locBlocks mu b && X b)
     (fun b => pubBlocks mu b && X b)
     (fun b => extBlocks mu b && X b)
     (fun b => frgnBlocks mu b && X b).  

Definition eq_intern_incr (mu mu': SM_Equality) :=
   (forall b, locBlocks mu b = true -> locBlocks mu' b = true) /\
   (pubBlocks mu = pubBlocks mu') /\
   (frgnBlocks mu = frgnBlocks mu') /\
   (extBlocks mu = extBlocks mu').

Definition eq_extern_incr (mu mu': SM_Equality) :=
   (forall b, extBlocks mu b = true -> extBlocks mu' b = true) /\
   (locBlocks mu = locBlocks mu') /\
   (pubBlocks mu = pubBlocks mu') /\
   (frgnBlocks mu = frgnBlocks mu').

Definition eq_inject_separated (mu mu' : SM_Equality) (m:mem):Prop :=
  forall b, Blocks mu b = false -> Blocks mu' b = true -> ~Mem.valid_block m b.

Definition eq_locally_allocated (mu mu' : SM_Equality) (m m':mem):Prop :=
    locBlocks mu' = (fun b => (locBlocks mu b) || (freshloc m m' b))
     /\ extBlocks mu' = extBlocks mu. 

Lemma restrict_se_WD:
      forall mu (WD: SE_wd mu) X
          (HX: forall b, visEq mu b = true -> X b = true),
      SE_wd (restrict_se mu X).
Proof. intros.
split; intros; simpl in *.
   destruct (disjoint_extern_local_Blocks _ WD b); rewrite H; simpl.
    left; trivial.
    right; trivial.
  apply andb_true_iff in H; destruct H.
    rewrite (pubBlocksAx _ WD _ H), H0; trivial.
  apply andb_true_iff in H; destruct H.
    rewrite (frgnBlocksAx _ WD _ H), H0; trivial.
Qed.

Lemma restrict_se_Blocks mu X b:
      Blocks (restrict_se mu X) b = true ->
      Blocks mu b = true.
Proof. unfold Blocks; simpl; intros.
  apply orb_true_iff.
  apply orb_true_iff in H; destruct H; 
    apply andb_true_iff in H; intuition.
Qed.

Lemma core_initial_se_wd : forall {F1 V1 F2 V2} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) 
                               vals m Blks
          (R: forall b, REACH m (fun b' => isGlobalBlock ge1 b' || getBlocks vals b') b = true -> 
                        Blks b = true)
          (HBlks: forall b, Blks b = true -> Mem.valid_block m b)
          mu (Hmu: mu = Build_SM_Equality 
                              (fun b => false)
                              (fun b => false)
                              Blks
                              (REACH m (fun b' => isGlobalBlock ge1 b' || getBlocks vals b'))),
       SE_wd mu /\ se_valid mu m /\ 
(*       meminj_preserves_globals ge1 (extern_of mu) /\*)
       (forall b, isGlobalBlock ge1 b = true -> frgnBlocks mu b = true) /\
       REACH_closed m (visEq mu).
Proof. intros.
split.
  subst.
  split; simpl; intros. left; trivial. trivial.
    apply (R _ H). 
split.
  red; subst; unfold Blocks; simpl; intros. auto.
split; subst; simpl; intros.
  apply REACH_nil. rewrite H; trivial.
unfold visEq; subst; simpl.
   apply REACH_is_closed.    
Qed.

Module SE_simulation. Section SharedMemory_simulation_equality. 
  Context {F1 V1 C1 F2 V2 C2:Type}
          (Sem1 : @EffectSem (Genv.t F1 V1) C1)
          (Sem2 : @EffectSem (Genv.t F2 V2) C2)
          (ge1: Genv.t F1 V1)
          (ge2: Genv.t F2 V2)
          (entry_points : list (val * val * signature)).
 

  Record SE_simulation_equality := 
  { core_data : Type;
    match_state : core_data -> SM_Equality -> C1 -> mem -> C2 -> Prop;
    core_ord : core_data -> core_data -> Prop;
    core_ord_wf : well_founded core_ord;

    match_se_wd: forall d mu c1 m c2, 
          match_state d mu c1 m c2 ->
          SE_wd mu;

    genvs_dom_eq: genvs_domain_eq ge1 ge2;

    match_genv: forall d mu c1 m c2 (MC:match_state d mu c1 m c2),
          (*meminj_preserves_globals ge1 (extern_of mu) /\*)
          (forall b, isGlobalBlock ge1 b = true -> frgnBlocks mu b = true); 

    match_visible: forall d mu c1 m c2, 
          match_state d mu c1 m c2 -> 
          REACH_closed m (visEq mu);

    match_restrict: forall d mu c1 m c2 X, 
          match_state d mu c1 m c2 -> 
          (forall b, visEq mu b = true -> X b = true) ->
          REACH_closed m X ->
          match_state d (restrict_se mu X) c1 m c2;

    match_validblocks: forall d mu c1 m c2, 
          match_state d mu c1 m c2 ->
          se_valid mu m;

    core_initial : forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals c1 m Blks,
          initial_core Sem1 ge1 v1 vals = Some c1 ->
          (*meminj_preserves_globals ge1 j ->*)

        (*the next condition is required to guarantee initialSE_wd*)
         (forall b, REACH m (fun b' => isGlobalBlock ge1 b' || getBlocks vals b') b = true ->
                    Blks b = true) ->

        (*the next condition ensures the initialSM satisfies se_valid*)
         (forall b, Blks b = true -> Mem.valid_block m b) ->

       exists cd, exists c2, 
            initial_core Sem2 ge2 v2 vals = Some c2 /\
            match_state cd (Build_SM_Equality 
                              (fun b => false)
                              (fun b => false)
                              Blks
                              (REACH m (fun b' => isGlobalBlock ge1 b' || getBlocks vals b')))
                           c1 m c2;

    core_diagram : 
      forall st1 m st1' m', 
        corestep Sem1 ge1 st1 m st1' m' ->
      forall cd st2 mu,
        match_state cd mu st1 m st2 ->
        exists st2', exists cd', exists mu',
          eq_intern_incr mu mu' /\
          eq_inject_separated mu mu' m /\

          (*new condition: corestep evolution is soundly and completely 
                           tracked by the local knowledge*)
          eq_locally_allocated mu mu' m m' /\
 
          match_state cd' mu' st1' m' st2' /\
          ((corestep_plus Sem2 ge2 st2 m st2' m') \/
            corestep_star Sem2 ge2 st2 m st2' m' /\
            core_ord cd' cd);

      effcore_diagram : 
      forall st1 m st1' m' U1, 
        effstep Sem1 ge1 U1 st1 m st1' m' ->

      forall cd st2 mu
        (UHyp: forall b1 z, U1 b1 z = true -> visEq mu b1 = true),
        match_state cd mu st1 m st2 ->
        exists st2', exists cd', exists mu',
          eq_intern_incr mu mu' /\
          eq_inject_separated mu mu' m /\
          eq_locally_allocated mu mu' m m' /\ 
          match_state cd' mu' st1' m' st2' /\

          exists U2,              
            ((effstep_plus Sem2 ge2 U2 st2 m st2' m' \/
              (effstep_star Sem2 ge2 U2 st2 m st2' m' /\
               core_ord cd' cd)) /\

             forall b ofs, U2 b ofs = true -> 
                       (visEq mu b = true /\
                         (locBlocks mu b = false ->
                           (frgnBlocks mu b = true /\ 
                            U1 b ofs = true /\ 
                            Mem.perm m b ofs Max Nonempty))));

    core_halted : forall cd mu c1 m c2 v,
      match_state cd mu c1 m c2 ->
      halted Sem1 c1 = Some v ->
      halted Sem2 c2 = Some v;

    core_at_external : 
      forall cd mu c1 m c2 e vals ef_sig,
        match_state cd mu c1 m c2 ->
        at_external Sem1 c1 = Some (e,ef_sig,vals) ->
        (*the minimal assumption corresponding to Mem.inject (as_inj mu) m1 m2)*)
        (REACH_closed m (Blocks mu) /\ 
         at_external Sem2 c2 = Some (e,ef_sig,vals));
(*        ((forall b, getBlocks vals b = true -> visEq mu b = true)
         /\ at_external Sem2 c2 = Some (e,ef_sig,vals)); *)

    eff_after_external: 
      forall cd mu st1 st2 m e vals ef_sig e' ef_sig'
        (*standard assumptions:*)
        (MatchMu: match_state cd mu st1 m st2)
        (AtExtSrc: at_external Sem1 st1 = Some (e,ef_sig,vals))
        (AtExtTgt: at_external Sem2 st2 = Some (e',ef_sig',vals)) 

        (*if we don't guarantee this property in atExternal, but assume 
          it here in after_external,  we can't prove composition INJ_EQ
        (ValsVis: forall b, getBlocks vals b = true -> visEq mu b = true)*)

        pubBlks' (pubBlksHyp: pubBlks' = fun b => 
                       (locBlocks mu b) &&
                       (REACH m (fun b' => (getBlocks vals b') || (pubBlocks mu b') || (frgnBlocks mu b')) b))

        nu (NuHyp: nu = Build_SM_Equality (locBlocks mu) pubBlks'
                                          (extBlocks mu) (frgnBlocks mu)),

      forall nu' ret m'
        (INC: eq_extern_incr nu nu')  
        (SEP: eq_inject_separated nu nu' m)

        (WDnu': SE_wd nu') (SMvalNu': se_valid nu' m')

        (RValNu': forall b, getBlocks (ret::nil) b = true -> Blocks nu' b = true)

        (*the minimal assumption corresponding to Mem.inject (as_inj nu') m1' m2')*)
        (RC': REACH_closed m' (Blocks nu'))
        (RC': REACH_closed m' ((getBlocks (ret::nil)

        (Fwd: mem_forward m m')

        frgnBlks' (frgnBlksHyp: frgnBlks' = fun b => 
                     (extBlocks nu' b) &&
                     (REACH m' (fun b' => (getBlocks (ret::nil) b') || (pubBlocks nu' b') || (frgnBlocks nu' b')) b))

        mu' (Mu'Hyp: mu' = Build_SM_Equality (locBlocks nu') (pubBlocks nu')
                                             (extBlocks nu') frgnBlks')
 
         (UnchPriv: Mem.unchanged_on (fun b ofs => locBlocks nu b = true /\ 
                                                      pubBlocks nu b = false) m m'),
        exists cd', exists st1', exists st2',
          after_external Sem1 (Some ret) st1 = Some st1' /\
          after_external Sem2 (Some ret) st2 = Some st2' /\
          match_state cd' mu' st1' m' st2'
}.

End SharedMemory_simulation_equality.
End SE_simulation.
(*

Module SIMULATION.
Section EFFECT_SIM.
  Context {F1 V1 C1 F2 V2 C2:Type}
          (Sem1 : @EffectSem (Genv.t F1 V1) C1)
          (Sem2 : @EffectSem (Genv.t F2 V2) C2).

Inductive effect_sim g1 g2 entrypoints:Type :=
  eff_sim_eq: forall (R:@SE_simulation.SE_simulation_equality
                         _ _ _ _ _ _ Sem1 Sem2 g1 g2 entrypoints),
          effect_sim g1 g2 entrypoints
| eff_sim_inj: forall (R:@SM_simulation.SM_simulation_inject
                         _ _ _ _ _ _ Sem1 Sem2 g1 g2 entrypoints),
          effect_sim g1 g2 entrypoints.
End EFFECT_SIM. 
End SIMULATION. 
*)

Lemma eq_intern_incr_refl mu: eq_intern_incr mu mu.
Proof. red; intros. intuition. Qed.
Lemma eq_inject_separated_same_se mu m: eq_inject_separated mu mu m.
Proof. red; intros. congruence. Qed.

Lemma eq_intern_incr_trans mu mu' mu'':
      forall (H:eq_intern_incr mu mu') (H': eq_intern_incr mu' mu''), 
      eq_intern_incr mu mu''.
Proof. unfold eq_intern_incr; intros.
  destruct H as [L [P [F E]]].
  destruct H' as [L' [P' [F' E']]].
  rewrite P, F, E.
  intuition.
Qed.

Lemma eq_inject_separated_trans mu mu' mu'' m m': 
  forall (Sep': eq_inject_separated mu' mu'' m')
         (Sep : eq_inject_separated mu mu' m)
         (Fwd: mem_forward m m'),
  eq_inject_separated mu mu'' m.
Proof. intros.
  red; intros. specialize (Sep b); specialize (Sep' b).
  remember (Blocks mu' b) as d.
  destruct d; apply eq_sym in Heqd.
    eapply Sep; trivial.
  clear Sep. intros N. apply Sep'; trivial.
  eapply Fwd; trivial.
Qed.

Lemma eq_locally_allocated_trans mu mu' mu'' m m' m'':
      forall (LAL: eq_locally_allocated mu mu' m m'')
             (LAL': eq_locally_allocated mu' mu'' m'' m')
             (Fwd: mem_forward m m'')
             (Fwd': mem_forward m'' m'),
      eq_locally_allocated mu mu'' m m'.
Proof. intros. destruct LAL; destruct LAL'.
  red; intros. rewrite H0 in H2.
  rewrite H1, H2; clear H0 H1 H2.
  split; trivial. extensionality b.
  rewrite H; clear H.
  remember (locBlocks mu b) as d.
  destruct d; apply eq_sym in Heqd; simpl; trivial.
  unfold freshloc.
  remember (valid_block_dec m' b) as q.
  destruct q; clear Heqq; simpl.
    remember (valid_block_dec m'' b) as p.
    destruct p; simpl; trivial. apply orb_false_r.
    clear Heqp. 
    remember (valid_block_dec m b) as w.
    destruct w; simpl; trivial. clear Heqw. 
    elim n; clear n. eapply Fwd. eassumption.
  rewrite orb_false_r. 
    remember (valid_block_dec m b) as w.
    destruct w; simpl; trivial. apply andb_false_r.
    clear Heqw. rewrite andb_true_r.
    remember (valid_block_dec m'' b) as p.
    destruct p; simpl; trivial. 
    clear Heqp. 
    elim n; clear n. eapply Fwd'. eassumption.
Qed.
(*
Definition compose_se_sm (mu12:SM_Equality)(mu23:SM_Injection) : SM_Injection :=
  Build_SM_Injection (locBlocks mu12) (locBlocksTgt mu23)
                     (pubBlocks mu12) (pubBlocksTgt mu23)
                     (local_of mu23)
                     (extBlocks mu12) (extBlocksTgt mu23)
                     (frgnBlocks mu12) (frgnBlocksTgt mu23)
                     (extern_of mu23).

Lemma compose_se_sm_as_inj mu12 mu23: 
      as_inj (compose_se_sm mu12 mu23) = as_inj mu23.
Proof. destruct mu12; destruct mu23; unfold as_inj; trivial. Qed.

Lemma compose_se_sm_DomSrc mu12 mu23: 
      DomSrc (compose_se_sm mu12 mu23) = Blocks mu12.
Proof. unfold DomSrc, Blocks. destruct mu12; destruct mu23; trivial. Qed.

Lemma compose_se_sm_DomTgt mu12 mu23: 
      DomTgt (compose_se_sm mu12 mu23) = DomTgt mu23.
Proof. unfold DomTgt. destruct mu12; destruct mu23; trivial. Qed.

Lemma compose_se_sm_intern_incr mu12 mu12' mu23 mu23':
      forall (EqIncr12 : eq_intern_incr mu12 mu12')
             (IntIncr23 : intern_incr mu23 mu23'),
      intern_incr (compose_se_sm mu12 mu23) (compose_se_sm mu12' mu23'). 
Proof. intros.
  destruct EqIncr12 as [Loc12 [Pub12 [Frgn12 Ext12]]].
  destruct IntIncr23 as [Local23 [Extern23 [LocSrc23 [LocTgt23 [PubSrc23 
         [PubTgt23 [FrgnSrc23 [FrgnTgt23 [ExtSrc23 ExtTgt23]]]]]]]]].
  split; intuition.
Qed.

Definition SE_SM_INV mu12 mu23:=
           locBlocks mu12 = locBlocksSrc mu23 /\
           extBlocks mu12 = extBlocksSrc mu23 /\
           (forall b, pubBlocks mu12 b = true -> 
                      pubBlocksSrc mu23 b = true) /\
           (forall b, frgnBlocks mu12 b = true ->
                      frgnBlocksSrc mu23 b = true).

Lemma SE_SM_INV_BlocksDomSrc mu12 mu23:
      SE_SM_INV mu12 mu23 -> Blocks mu12 = DomSrc mu23.
Proof. intros.
  unfold DomSrc, Blocks. 
  destruct H as [InvLoc [InvExt [InvPub InvFrgn]]].
  rewrite InvLoc, InvExt. trivial.
Qed.

Lemma compose_se_sm_inject_separated mu12 mu12' mu23 mu23' m m3:
      forall (EqSep12 : eq_inject_separated mu12 mu12' m)
             (InjSep23 : sm_inject_separated mu23 mu23' m m3)
             (INV: SE_SM_INV mu12 mu23),
      sm_inject_separated (compose_se_sm mu12 mu23) (compose_se_sm mu12' mu23') m m3.
Proof. intros.
  red in EqSep12. destruct InjSep23 as [SepA [SepB SepC]].
  split; intros.
    rewrite compose_se_sm_as_inj in *;
    rewrite compose_se_sm_DomSrc, compose_se_sm_DomTgt.
    destruct (SepA _ _ _ H H0). clear SepA.
    rewrite (SE_SM_INV_BlocksDomSrc _ _ INV).
    split; trivial.
  intros. 
    rewrite compose_se_sm_DomSrc, compose_se_sm_DomTgt.
    rewrite compose_se_sm_DomSrc, compose_se_sm_DomTgt.
    split; assumption.
Qed.

Lemma compose_se_sm_locally_allocated mu12 mu12' mu23 mu23' m m3 m' m3':
      forall (LocAlloc12 : eq_locally_allocated mu12 mu12' m m')
             (LocAlloc23 : sm_locally_allocated mu23 mu23' m m3 m' m3')
             (INV: SE_SM_INV mu12 mu23)
             (INV': SE_SM_INV mu12' mu23'),
      sm_locally_allocated (compose_se_sm mu12 mu23) (compose_se_sm mu12' mu23') m m3 m' m3'.
Proof. intros.
  destruct LocAlloc12 as [Src12 Tgt12].
  rewrite sm_locally_allocatedChar.
  rewrite sm_locally_allocatedChar in LocAlloc23.
  destruct LocAlloc23 as [Dom23 [Rng23 [locSrc23 [locTgt23 [extSrc23 extTgt23]]]]].
  rewrite compose_se_sm_DomSrc, compose_se_sm_DomTgt.
  rewrite compose_se_sm_DomSrc, compose_se_sm_DomTgt.
  simpl. rewrite (SE_SM_INV_BlocksDomSrc _ _ INV).
  rewrite (SE_SM_INV_BlocksDomSrc _ _ INV'). intuition.
Qed. 
*)
Definition compose_sm_se (mu12:SM_Injection)(mu23:SM_Equality) : SM_Injection :=
  Build_SM_Injection (locBlocksSrc mu12) (locBlocks mu23)
                     (pubBlocksSrc mu12) (pubBlocks mu23)
                     (local_of mu12)
                     (extBlocksSrc mu12) (extBlocks mu23)
                     (frgnBlocksSrc mu12) (frgnBlocks mu23)
                     (extern_of mu12).

Lemma compose_sm_se_as_inj mu12 mu23: 
      as_inj (compose_sm_se mu12 mu23) = as_inj mu12.
Proof. destruct mu12; destruct mu23; unfold as_inj; trivial. Qed.

Lemma compose_sm_se_local mu12 mu23: 
      local_of (compose_sm_se mu12 mu23) = local_of mu12.
Proof. destruct mu12; destruct mu23; unfold as_inj; trivial. Qed.

Lemma compose_sm_se_extern mu12 mu23: 
      extern_of (compose_sm_se mu12 mu23) = extern_of mu12.
Proof. destruct mu12; destruct mu23; unfold as_inj; trivial. Qed.

Lemma compose_sm_se_pub mu12 mu23: 
      pub_of (compose_sm_se mu12 mu23) = pub_of mu12.
Proof. destruct mu12; destruct mu23; unfold as_inj; trivial. Qed.

Lemma compose_sm_se_foreign mu12 mu23: 
      foreign_of (compose_sm_se mu12 mu23) = foreign_of mu12.
Proof. destruct mu12; destruct mu23; unfold as_inj; trivial. Qed.

Lemma compose_sm_se_DomSrc mu12 mu23: 
      DomSrc (compose_sm_se mu12 mu23) = DomSrc mu12.
Proof. unfold DomSrc, Blocks. destruct mu12; destruct mu23; trivial. Qed.

Lemma compose_sm_se_DomTgt mu12 mu23: 
      DomTgt (compose_sm_se mu12 mu23) = Blocks mu23.
Proof. unfold DomTgt. destruct mu12; destruct mu23; trivial. Qed.

Lemma compose_sm_se_vis mu12 mu23: 
      vis (compose_sm_se mu12 mu23) = vis mu12.
Proof. unfold vis; trivial. Qed.
Lemma compose_sm_se_visTgt mu12 mu23: 
      visTgt (compose_sm_se mu12 mu23) = visEq mu23.
Proof. unfold visTgt, visEq; trivial. Qed.

Lemma compose_sm_se_intern_incr mu12 mu12' mu23 mu23':
      forall (IntIncr12 : intern_incr mu12 mu12')
             (EqIncr23: eq_intern_incr mu23 mu23'),
      intern_incr (compose_sm_se mu12 mu23) (compose_sm_se mu12' mu23'). 
Proof. intros.
  destruct EqIncr23 as [Loc23 [Pub23 [Frgn23 Ext23]]].
  destruct IntIncr12 as [Local12 [Extern12 [LocSrc12 [LocTgt12 [PubSrc12 
         [PubTgt12 [FrgnSrc12 [FrgnTgt12 [ExtSrc12 ExtTgt12]]]]]]]]].
  split; intuition.
Qed.

Definition SM_SE_INV mu12 mu23:=
           locBlocksTgt mu12 = locBlocks mu23 /\
           extBlocksTgt mu12 = extBlocks mu23 /\
           (forall b, pubBlocksTgt mu12 b = true -> 
                      pubBlocks mu23 b = true) /\
           (forall b, frgnBlocksTgt mu12 b = true ->
                      frgnBlocks mu23 b = true).

Lemma SM_SE_INV_DomTgtBlocks mu12 mu23:
      SM_SE_INV mu12 mu23 -> DomTgt mu12 = Blocks mu23.
Proof. intros.
  unfold DomTgt, Blocks. 
  destruct H as [InvLoc [InvExt [InvPub InvFrgn]]].
  rewrite InvLoc, InvExt. trivial.
Qed.

Lemma compose_sm_se_inject_separated mu12 mu12' mu23 mu23' m m3:
      forall (InjSep12 : sm_inject_separated mu12 mu12' m m3)
             (EqSep23 : eq_inject_separated mu23 mu23' m3)
             (INV: SM_SE_INV mu12 mu23),
      sm_inject_separated (compose_sm_se mu12 mu23) (compose_sm_se mu12' mu23') m m3.
Proof. intros.
  red in EqSep23. destruct InjSep12 as [SepA [SepB SepC]].
  split; intros.
    rewrite compose_sm_se_as_inj in *;
    rewrite compose_sm_se_DomSrc, compose_sm_se_DomTgt.
    destruct (SepA _ _ _ H H0). clear SepA.
    rewrite <- (SM_SE_INV_DomTgtBlocks _ _ INV).
    split; trivial.
  intros. 
    rewrite compose_sm_se_DomSrc, compose_sm_se_DomTgt.
    rewrite compose_sm_se_DomSrc, compose_sm_se_DomTgt.
    split; assumption.
Qed.

Lemma compose_sm_se_locally_allocated mu12 mu12' mu23 mu23' m m3 m' m3':
      forall (LocAlloc23 : eq_locally_allocated mu23 mu23' m3 m3')
             (LocAlloc12 : sm_locally_allocated mu12 mu12' m m3 m' m3')
             (INV: SM_SE_INV mu12 mu23)
             (INV': SM_SE_INV mu12' mu23'),
      sm_locally_allocated (compose_sm_se mu12 mu23) (compose_sm_se mu12' mu23') m m3 m' m3'.
Proof. intros.
  destruct LocAlloc23 as [Src12 Tgt12].
  rewrite sm_locally_allocatedChar.
  rewrite sm_locally_allocatedChar in LocAlloc12.
  destruct LocAlloc12 as [Dom12 [Rng12 [locSrc12 [locTgt12 [extSrc12 extTgt12]]]]].
  rewrite compose_sm_se_DomSrc, compose_sm_se_DomTgt.
  rewrite compose_sm_se_DomSrc, compose_sm_se_DomTgt.
  simpl. rewrite <- (SM_SE_INV_DomTgtBlocks _ _ INV).
  rewrite <- (SM_SE_INV_DomTgtBlocks _ _ INV'). intuition.
Qed. 

Lemma compose_sm_se_restrict_sm mu12 mu23 X:
      restrict_sm (compose_sm_se mu12 mu23) X =
      compose_sm_se (restrict_sm mu12 X) mu23.
Proof. unfold compose_sm_se. simpl.  f_equal; simpl.
       rewrite restrict_sm_locBlocksSrc. reflexivity.
       rewrite restrict_sm_pubBlocksSrc. reflexivity.
       rewrite restrict_sm_local. reflexivity.
       rewrite restrict_sm_extBlocksSrc. reflexivity.
       rewrite restrict_sm_frgnBlocksSrc. reflexivity.
       rewrite restrict_sm_extern. reflexivity.
Qed.
        
Require Import forward_simulations_trans. (*for definition of entrypoint_compose*)
Require Import effect_simulations_trans. (*for proof that injections_effect_simulations compose*)

Require Import Wellfounded.
Require Import Relations.
Import SE_simulation.

Module TRANS.
Section EFFECT_SIM_TRANS.
Context {F1 V1 C1 F2 V2 C2 F3 V3 C3:Type}
        (Sem1 : @EffectSem (Genv.t F1 V1) C1)
        (Sem2 : @EffectSem (Genv.t F2 V2) C2)
        (Sem3 : @EffectSem (Genv.t F3 V3) C3)
        (g1 : Genv.t F1 V1)
        (g2 : Genv.t F2 V2)
        (g3 : Genv.t F3 V3).

Lemma eqeq_corediagram_trans: forall
      (core_data12:Type)
      (match_core12: core_data12 -> SM_Equality -> C1 -> mem -> C2 -> Prop)
      (core_ord12 : core_data12 -> core_data12 -> Prop)
      (CD12: forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem),
                 corestep Sem1 g1 st1 m st1' m' ->
                 forall (cd : core_data12) (st2 : C2) (mu : SM_Equality),
                 match_core12 cd mu st1 m st2 ->
                 exists (st2' : C2) (cd' : core_data12) (mu' : SM_Equality),
                   eq_intern_incr mu mu' /\
                   eq_inject_separated mu mu' m /\
                   eq_locally_allocated mu mu' m m' /\
                   match_core12 cd' mu' st1' m' st2' /\
                   (corestep_plus Sem2 g2 st2 m st2' m' \/
                    corestep_star Sem2 g2 st2 m st2' m' /\ core_ord12 cd' cd))
      (core_data23:Type)
      (match_core23: core_data23 -> SM_Equality -> C2 -> mem -> C3 -> Prop)
      (core_ord23 : core_data23 -> core_data23 -> Prop)
      (CD23: forall (st1 : C2) (m : mem) (st1' : C2) (m' : mem),
                 corestep Sem2 g2 st1 m st1' m' ->
                 forall (cd : core_data23) (st2 : C3) (mu : SM_Equality),
                 match_core23 cd mu st1 m st2 ->
                 exists (st2' : C3) (cd' : core_data23) (mu' : SM_Equality),
                   eq_intern_incr mu mu' /\
                   eq_inject_separated mu mu' m /\
                   eq_locally_allocated mu mu' m m' /\
                   match_core23 cd' mu' st1' m' st2' /\
                   (corestep_plus Sem3 g3 st2 m st2' m' \/
                    corestep_star Sem3 g3 st2 m st2' m' /\ core_ord23 cd' cd)),
forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem),
       corestep Sem1 g1 st1 m st1' m' ->
forall (cd : core_data12 * option C2 * core_data23) (st2 : C3) (mu : SM_Equality),
       (let (y, d2) := cd in
         let (d1, X) := y in
        exists c2 : C2,
        X = Some c2 /\ match_core12 d1 mu st1 m c2 /\ match_core23 d2 mu c2 m st2) ->
exists (st2' : C3) (cd' : core_data12 * option C2 * core_data23) (mu' : SM_Equality),
  eq_intern_incr mu mu' /\
  eq_inject_separated mu mu' m /\
  eq_locally_allocated mu mu' m m' /\
  (let (y, d2) := cd' in
   let (d1, X) := y in
   exists c2 : C2,
     X = Some c2 /\
     match_core12 d1 mu' st1' m' c2 /\ match_core23 d2 mu' c2 m' st2') /\
  (corestep_plus Sem3 g3 st2 m st2' m' \/
   corestep_star Sem3 g3 st2 m st2' m' /\
   clos_trans (core_data12 * option C2 * core_data23)
     (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd' cd).
Proof. intros. rename st2 into st3. 
  destruct cd as [[d12 cc2] d23].
  destruct H0 as [c2 [X [MC12 MC23]]]; subst.
  destruct (CD12 _ _ _ _ H _ _ _ MC12)
    as [c2' [d12' [mu' [EqIncr12 [EqSep12 [LocAlloc12
       [MC12' Y]]]]]]]; clear CD12 H.
  assert (ZZ: corestep_plus Sem2 g2 c2 m c2' m' \/
    (c2,m) = (c2',m') /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
  right. split; auto.
  left. exists x; auto.
  clear Y. destruct ZZ as [CS2 | [CS2 ord12']].
 (*case1*) 
  destruct CS2.
  clear MC12.
  cut (exists st3', exists d23', exists mu'',
      eq_intern_incr mu mu'' /\
      eq_inject_separated mu mu'' m /\
      eq_locally_allocated mu mu'' m m' /\
    match_core23 d23' mu'' c2' m' st3' /\
    (corestep_plus Sem3 g3 st3 m st3' m' \/
      (corestep_star Sem3 g3 st3 m st3' m' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)
               (d12', Some c2', d23')
               (d12, Some c2, d23)))).
  intros XX; destruct XX as [st3' [d23' [mu'' [EqIncr23 [EqSep23 [LocAlloc23 [MC23' ZZ]]]]]]].
  assert (mu'' = mu').
    clear ZZ H MC23.
      destruct LocAlloc12; destruct LocAlloc23.
      rewrite <- H in H1. rewrite <- H0 in H2. clear H H0.
      destruct EqIncr12 as [_ [PUB' [FRGN' _]]].
      destruct EqIncr23 as [_ [PUB'' [FRGN'' _]]].
      rewrite PUB'' in PUB'. rewrite FRGN'' in FRGN'. 
      destruct mu'; destruct mu''; simpl in *.
      rewrite H1, H2, PUB', FRGN'. trivial. 
  subst.     
  exists st3', (d12', Some c2', d23'), mu'.
  split; trivial. 
  split; trivial.
  split; trivial. 
  split. exists c2'.
     split. reflexivity.
     split; trivial.
     trivial.

  (*proof of the cut*)
  clear MC12' EqIncr12 EqSep12 LocAlloc12 st1 st1'
        C1 Sem1 match_core12 g1 mu'.
  revert mu m d23 c2 st3 H MC23.
  induction x; intros. 
   (*base case*) simpl in H.
    destruct H as [st2 [m'' [? ?]]].
    inv H0.
    destruct (CD23 _ _ _ _ H _ _ _ MC23) 
      as [st3' [d23' [mu'' [EqInc23 [EqSep23
          [LocAlloc23 [? ?]]]]]]]; clear CD23.
    exists st3', d23', mu''. 
    split; trivial.
    split; trivial.
    split; trivial.
    split; trivial.
    destruct H1. left; assumption.
           destruct H1. right. split; trivial.
           apply t_step. constructor 2. apply H2.
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    destruct H as [st2'' [m'' [? ?]]]. subst x'.
    destruct (CD23 _ _ _ _  H _ _ _ MC23) 
      as [c3' [d23' [mu' [InjInc23 [InjSep23 
             [LocAlloc23 [? ?]]]]]]]; clear CD23.
    specialize (IHx mu' _ d23' _ c3' H0 H1).
    destruct IHx as [c3'' [d23'' [mu'' [EqIncr' 
             [EqSep' [LocAlloc23' [MC' XX]]]]]]].
    exists c3'', d23'', mu''.
    split. eapply eq_intern_incr_trans; eassumption. 
    split. eapply eq_inject_separated_trans; try eassumption. 
           eapply corestep_fwd; eassumption.
    split. apply corestep_fwd in H.
           assert (FWD': mem_forward m'' m').
             destruct XX as [XX | [XX _]].
             eapply corestep_plus_fwd; eassumption.
             eapply corestep_star_fwd; eassumption.
           eapply eq_locally_allocated_trans; eassumption.
    split. trivial.
    destruct H2; destruct XX.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H3.
               left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*4/4*)
               right. destruct H2. destruct H3.
               split. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
               eapply t_trans.
                 apply H5. clear H5.  
                 apply t_step.
                 constructor 2. apply H4.
  (*case 2*)
   inv CS2.
   assert (mu' = mu).
     destruct LocAlloc12. 
     assert (locBlocks mu' = locBlocks mu).
       rewrite H. extensionality b. rewrite freshloc_irrefl.
       apply orb_false_r.
     clear H.
      destruct EqIncr12 as [_ [PUB' [FRGN' _]]].
      destruct mu'; destruct mu; simpl in *.
      rewrite H0, H1, PUB', FRGN'. trivial. 
   subst.
   exists st3, (d12',Some c2',d23), mu.
   split; trivial.
   split; trivial.
   split; trivial.
   split. exists c2'. split; trivial. split; trivial.
   right. split. exists O. simpl; auto.
      apply t_step. constructor 1; auto.
Qed.

Lemma eqeq_effcorediagram_trans: forall 
      (core_data12:Type)
      (match_core12: core_data12 -> SM_Equality -> C1 -> mem -> C2 -> Prop) 
      (core_ord12 : core_data12 -> core_data12 -> Prop)
      (CD12: forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem)
                      (U1 : block -> Z -> bool),
                    effstep Sem1 g1 U1 st1 m st1' m' ->
                    forall (cd : core_data12) (st2 : C2) (mu : SM_Equality),
                    (forall (b1 : block) (z : Z),
                     U1 b1 z = true -> visEq mu b1 = true) ->
                    match_core12 cd mu st1 m st2 ->
                    exists
                      (st2' : C2) (cd' : core_data12) (mu' : SM_Equality),
                      eq_intern_incr mu mu' /\
                      eq_inject_separated mu mu' m /\
                      eq_locally_allocated mu mu' m m' /\
                      match_core12 cd' mu' st1' m' st2' /\
                      (exists U2 : block -> Z -> bool,
                         (effstep_plus Sem2 g2 U2 st2 m st2' m' \/
                          effstep_star Sem2 g2 U2 st2 m st2' m' /\
                          core_ord12 cd' cd) /\
                         (forall (b : block) (ofs : Z),
                          U2 b ofs = true ->
                          visEq mu b = true /\
                          (locBlocks mu b = false ->
                           frgnBlocks mu b = true /\
                           U1 b ofs = true /\ Mem.perm m b ofs Max Nonempty))))
      (core_data23:Type)
      (match_core23: core_data23 -> SM_Equality -> C2 -> mem -> C3 -> Prop)
      (core_ord23 : core_data23 -> core_data23 -> Prop)
      (CD23 : forall (st1 : C2) (m : mem) (st1' : C2) (m' : mem)
                      (U1 : block -> Z -> bool),
                    effstep Sem2 g2 U1 st1 m st1' m' ->
                    forall (cd : core_data23) (st2 : C3) (mu : SM_Equality),
                    (forall (b1 : block) (z : Z),
                     U1 b1 z = true -> visEq mu b1 = true) ->
                    match_core23 cd mu st1 m st2 ->
                    exists
                      (st2' : C3) (cd' : core_data23) (mu' : SM_Equality),
                      eq_intern_incr mu mu' /\
                      eq_inject_separated mu mu' m /\
                      eq_locally_allocated mu mu' m m' /\
                      match_core23 cd' mu' st1' m' st2' /\
                      (exists U2 : block -> Z -> bool,
                         (effstep_plus Sem3 g3 U2 st2 m st2' m' \/
                          effstep_star Sem3 g3 U2 st2 m st2' m' /\
                          core_ord23 cd' cd) /\
                         (forall (b : block) (ofs : Z),
                          U2 b ofs = true ->
                          visEq mu b = true /\
                          (locBlocks mu b = false ->
                           frgnBlocks mu b = true /\
                           U1 b ofs = true /\ Mem.perm m b ofs Max Nonempty)))),
forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem) (U1 : block -> Z -> bool)
    (CS: effstep Sem1 g1 U1 st1 m st1' m')
    (cd : core_data12 * option C2 * core_data23) (st2 : C3)
    (mu : SM_Equality)
    (UHyp: forall b1 z, U1 b1 z = true -> visEq mu b1 = true),
    (let (y, d2) := cd in
     let (d1, X) := y in
     exists c2 : C2,
       X = Some c2 /\ match_core12 d1 mu st1 m c2 /\ match_core23 d2 mu c2 m st2) ->
exists
  (st2' : C3) (cd' : core_data12 * option C2 * core_data23) (mu' : SM_Equality),
  eq_intern_incr mu mu' /\
  eq_inject_separated mu mu' m /\
  eq_locally_allocated mu mu' m m' /\
  (let (y, d2) := cd' in
   let (d1, X) := y in
   exists c2 : C2,
     X = Some c2 /\
     match_core12 d1 mu' st1' m' c2 /\ match_core23 d2 mu' c2 m' st2') /\
  (exists U2 : block -> Z -> bool,
     (effstep_plus Sem3 g3 U2 st2 m st2' m' \/
      effstep_star Sem3 g3 U2 st2 m st2' m' /\
      clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd' cd) /\
     (forall (b : block) (ofs : Z),
      U2 b ofs = true ->
      visEq mu b = true /\
      (locBlocks mu b = false ->
       frgnBlocks mu b = true /\
       U1 b ofs = true /\ Mem.perm m b ofs Max Nonempty))).
Proof. intros. rename st2 into st3. 
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [X [MC12 MC23]]]; subst.
  destruct (CD12 _ _ _ _ _ CS _ _ _ UHyp MC12)
    as [c2' [d12' [mu' [EqIncr12 [EqSep12 [LocAlloc12
       [MC12' [U2 [Y U2Spec]]]]]]]]]; clear CD12 CS.
  assert (ZZ: effstep_plus Sem2 g2 U2 c2 m c2' m' \/
    (c2,m) = (c2',m') /\ (U2 = fun b z => false) /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
  right. simpl in H. destruct H. split; trivial. split; auto.
  left. exists x; auto.
  clear Y. destruct ZZ as [CS2 | [CS2 [U2False ord12']]].
 (*case1*) 
  destruct CS2.
  clear MC12.
  cut (exists st3', exists d23', exists mu'',
      eq_intern_incr mu mu'' /\
      eq_inject_separated mu mu'' m /\
      eq_locally_allocated mu mu'' m m' /\
    match_core23 d23' mu'' c2' m' st3' /\
    exists U3: block -> Z -> bool,
    ((effstep_plus Sem3 g3 U3 st3 m st3' m' \/
      (effstep_star Sem3 g3 U3 st3 m st3' m' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)
               (d12', Some c2', d23')
               (d12, Some c2, d23)))
      /\ (forall b ofs,
      U3 b ofs = true ->
      visEq mu b = true /\
      (locBlocks mu b = false ->
       frgnBlocks mu b = true /\
       U2 b ofs = true /\ Mem.perm m b ofs Max Nonempty)))).
  intros XX; destruct XX as [st3' [d23' [mu'' [EqIncr23 [EqSep23 [LocAlloc23 [MC23' [U3 [ZZ U3Spec]]]]]]]]].
  assert (mu'' = mu').
    clear ZZ H MC23 U2Spec U3Spec.
      destruct LocAlloc12; destruct LocAlloc23.
      rewrite <- H in H1. rewrite <- H0 in H2. clear H H0.
      destruct EqIncr12 as [_ [PUB' [FRGN' _]]].
      destruct EqIncr23 as [_ [PUB'' [FRGN'' _]]].
      rewrite PUB'' in PUB'. rewrite FRGN'' in FRGN'. 
      destruct mu'; destruct mu''; simpl in *.
      rewrite H1, H2, PUB', FRGN'. trivial. 
  subst.     
  exists st3', (d12', Some c2', d23'), mu'.
  split; trivial. 
  split; trivial.
  split; trivial. 
  split. exists c2'.
     split. reflexivity.
     split; trivial.
  exists U3. split. apply ZZ.
     intros. destruct (U3Spec _ _ H0). split; trivial.
     intros. destruct (H2 H3) as [? [? ?]].
     split; trivial. split; trivial.
     eapply U2Spec; trivial. 

  (*proof of the cut*)
  clear MC12' EqIncr12 EqSep12 LocAlloc12 st1 st1'
        C1 Sem1 match_core12 g1 mu'.
  assert (U2Hyp : forall b2 z, U2 b2 z = true -> visEq mu b2 = true).
      intros. eapply U2Spec; eassumption. 
  clear U2Spec UHyp U1.
  revert U2 mu m d23 c2 st3 U2Hyp MC23 H .
  induction x; intros. 
   (*base case*) simpl in H.
    destruct H as [st2 [m'' [U2a [U2b [CS2 [[? ?] ?]]]]]].
    inv H.
    assert (U2aHyp: forall b1 z, U2a b1 z = true -> 
                    visEq mu b1 = true).
       intros. eapply (U2Hyp _ z). rewrite H. trivial.
    destruct (CD23 _ _ _ _ _ CS2 _ _ _ U2aHyp MC23) 
      as [st3' [d23' [mu'' [EqInc23 [EqSep23
          [LocAlloc23 [? [U3 [? U3Spec]]]]]]]]]; clear CD23.
    exists st3', d23', mu''. 
    split; trivial.
    split; trivial.
    split; trivial.
    split; trivial.
    exists U3.
    split. destruct H0. left; assumption.
           destruct H0. right. split; trivial.
           apply t_step. constructor 2. apply H1.
    intros. destruct (U3Spec _ _ H1). split; trivial.
       intros. destruct (H3 H4) as [? [? ?]].
       rewrite H6. intuition.
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    destruct H as [st2'' [m'' [U2a [U2b [? [? U2split]]]]]]. subst x'.
    assert (U2aHyp: forall b1 z, U2a b1 z = true -> 
                    visEq mu b1 = true).
       intros. clear IHx. eapply (U2Hyp _ z). subst.
       rewrite H1; trivial.
    destruct (CD23 _ _ _ _ _ H _ _ _ U2aHyp MC23) 
      as [st3' [d23' [mu' [EqInc23 [EqSep23
          [LocAlloc23 [? [U3a [? U3aSpec]]]]]]]]]; clear CD23.
    assert (U2bHyp: forall b1 z, U2b b1 z = true -> 
                    visEq mu' b1 = true).
       intros. clear IHx U3aSpec H2 IHx. 
       assert (VB'': Mem.valid_block m'' b1). eapply effstepN_valid; eassumption.
       unfold visEq. 
       destruct LocAlloc23 as [LOC' _]; rewrite LOC' in *.
       unfold freshloc.
       assert (frgnBlocks mu = frgnBlocks mu') by eapply EqInc23.
       rewrite <- H2.
       remember (valid_block_dec m'' b1) as q.
       destruct q; try contradiction. simpl.
       remember (valid_block_dec m b1) as d.
       destruct d; apply eq_sym in Heqd; simpl in *.
         assert (visEq mu b1 = true).
           eapply (U2Hyp _ z); subst U2. rewrite H3, Heqd; simpl. intuition.
         rewrite orb_false_r. unfold visEq; trivial. 
       intuition.          
    specialize (IHx _ _ _ d23' _ st3' U2bHyp H1 H0).
    destruct IHx as [c3'' [d23'' [mu'' [EqIncr' 
             [EqSep' [LocAlloc23' [MC' [U3b [XX U3bSpec]]]]]]]]].
    exists c3'', d23'', mu''.
    assert (FWD: mem_forward m m'').
      destruct H2 as [CS | [CS _]].
             eapply effstep_plus_fwd; eassumption.
             eapply effstep_star_fwd; eassumption.
    split. eapply eq_intern_incr_trans; eassumption. 
    split. eapply eq_inject_separated_trans; try eassumption.            
    split. eapply eq_locally_allocated_trans; try eassumption.
           eapply effstepN_fwd; eapply H0. 
    split. trivial.
    exists (fun b z => U3a b z || U3b b z && valid_block_dec m b).
    split. destruct H2; destruct XX.
           (*1/4*)
              left. eapply effstep_plus_trans; eassumption.
           (*2/4*)
              left. destruct H3 as [EFF3 CT].
              eapply effstep_plus_star_trans; eassumption. 
           (*3/4*)
               left. destruct H2 as [EFF3 CORD].
               eapply effstep_star_plus_trans; eassumption.
           (*4/4*)
               right. destruct H2 as [EFF3 CORD].
                      destruct H3 as [EFF3' CT].
               split. eapply effstep_star_trans; eassumption.
               eapply t_trans.
                 apply CT. clear CT.  
                 apply t_step.
                 constructor 2. apply CORD.
    intros. apply orb_true_iff in H3. subst U2. 
      destruct H3.
        destruct (U3aSpec _ _ H3). split; trivial.
        intros. destruct (H5 H6) as [? [? ?]].
          rewrite H8. intuition.
      apply andb_true_iff in H3; destruct H3.
        destruct (U3bSpec _ _ H3). 
        unfold visEq in H5.
        destruct LocAlloc23 as [LOC' _]; rewrite LOC' in *.
               unfold freshloc in *. rewrite H4 in *.
        simpl in *.
        rewrite andb_false_r, orb_false_r in *.
        assert (frgnBlocks mu = frgnBlocks mu') by eapply EqInc23.
        unfold visEq. rewrite H7, andb_true_r in *.
        split. apply H5.
        intros. destruct (H6 H8) as [? [? ?]]. 
          rewrite H10, orb_true_r. split; trivial. split; trivial. 
          eapply FWD; trivial.
          destruct (valid_block_dec m b); trivial; try discriminate.
  (*case 2*)
   inv CS2. clear U2Spec.
   assert (mu' = mu).
     destruct LocAlloc12. 
     assert (locBlocks mu' = locBlocks mu).
       rewrite H. extensionality b. rewrite freshloc_irrefl.
       apply orb_false_r.
     clear H.
      destruct EqIncr12 as [_ [PUB' [FRGN' _]]].
      destruct mu'; destruct mu; simpl in *.
      rewrite H0, H1, PUB', FRGN'. trivial. 
   subst.
   exists st3, (d12',Some c2',d23), mu.
   split; trivial.
   split; trivial.
   split; trivial.
   split. exists c2'. split; trivial. split; trivial.
   exists (fun b z=>false). 
   split. right. split. exists O. simpl; auto.
      apply t_step. constructor 1; auto.
   intros; discriminate.
Qed.
(*
Lemma eqinj_corediagram_trans: forall
      (core_data12:Type)
      (match_core12: core_data12 -> SM_Equality -> C1 -> mem -> C2 -> Prop)
      (core_ord12 : core_data12 -> core_data12 -> Prop)
      (CD12: forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem),
                 corestep Sem1 g1 st1 m st1' m' ->
                 forall (cd : core_data12) (st2 : C2) (mu : SM_Equality),
                 match_core12 cd mu st1 m st2 ->
                 exists (st2' : C2) (cd' : core_data12) (mu' : SM_Equality),
                   eq_intern_incr mu mu' /\
                   eq_inject_separated mu mu' m /\
                   eq_locally_allocated mu mu' m m' /\
                   match_core12 cd' mu' st1' m' st2' /\
                   (corestep_plus Sem2 g2 st2 m st2' m' \/
                    corestep_star Sem2 g2 st2 m st2' m' /\ core_ord12 cd' cd))
      (core_data23 : Type)
      (match_core23 : core_data23 -> SM_Injection -> C2 -> mem -> C3 -> mem -> Prop)
      (MatchWD23: forall cd mu st2 m2 st3 m3,
                 match_core23 cd mu st2 m2 st3 m3 -> SM_wd mu)
      (core_ord23 : core_data23 -> core_data23 -> Prop)
      (CD23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                 corestep Sem2 g2 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (mu : SM_Injection)
                   (m2 : mem),
                 match_core23 cd mu st1 m1 st2 m2 ->
                 exists
                   (st2' : C3) (m2' : mem) (cd' : core_data23) (mu' : SM_Injection),
                   intern_incr mu mu' /\ 
                   sm_inject_separated mu mu' m1 m2 /\
                   sm_locally_allocated mu mu' m1 m2 m1' m2' /\ 
                   match_core23 cd' mu' st1' m1' st2' m2' /\
                   (corestep_plus Sem3 g3 st2 m2 st2' m2' \/
                    corestep_star Sem3 g3 st2 m2 st2' m2' /\
                    core_ord23 cd' cd)),
forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem),
corestep Sem1 g1 st1 m st1' m' ->
forall (cd : core_data12 * option C2 * core_data23) (st3 : C3) mu12 mu23 m3,
(let (y, d2) := cd in
 let (d1, X) := y in
 exists c2 : C2, 
   X = Some c2 /\ match_core12 d1 mu12 st1 m c2 /\ 
   match_core23 d2 mu23 c2 m st3 m3 /\
   SE_SM_INV mu12 mu23) ->
exists
  (st3' : C3) m3' (cd' : core_data12 * option C2 * core_data23) mu12' mu23',
  intern_incr (compose_se_sm mu12 mu23) (compose_se_sm mu12' mu23') /\
  sm_inject_separated (compose_se_sm mu12 mu23) (compose_se_sm mu12' mu23') m m3 /\
  sm_locally_allocated (compose_se_sm mu12 mu23) (compose_se_sm mu12' mu23') m m3 m' m3' /\
  (let (y, d2) := cd' in
   let (d1, X) := y in
   exists c2 : C2,
     X = Some c2 /\
     match_core12 d1 mu12' st1' m' c2 /\ match_core23 d2 mu23' c2 m' st3' m3') /\
  (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
   corestep_star Sem3 g3 st3 m3 st3' m3' /\
   clos_trans (core_data12 * option C2 * core_data23)
     (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd' cd) /\
   SE_SM_INV mu12' mu23'.
Proof. intros. 
  destruct cd as [[d12 cc2] d23].
  destruct H0 as [c2 [X [MC12 [MC23 INV]]]]; subst.
  destruct (CD12 _ _ _ _ H _ _ _ MC12)
    as [c2' [d12' [mu12' [EqIncr12 [EqSep12 [LocAlloc12
       [MC12' Y]]]]]]]; clear CD12 H.
  assert (ZZ: corestep_plus Sem2 g2 c2 m c2' m' \/
    (c2,m) = (c2',m') /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
  right. split; auto.
  left. exists x; auto.
  clear Y. destruct ZZ as [CS2 | [CS2 ord12']].
 (*case1*) 
  destruct CS2.
  clear MC12.
  cut (exists st3', exists m3', exists d23', exists mu23',
      intern_incr mu23 mu23' /\
      sm_inject_separated mu23 mu23' m m3 /\
      sm_locally_allocated mu23 mu23' m m3 m' m3' /\
    match_core23 d23' mu23' c2' m' st3' m3' /\
    (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
      (corestep_star Sem3 g3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)
               (d12', Some c2', d23')
               (d12, Some c2, d23))) /\
    SE_SM_INV mu12' mu23').
  intros XX; destruct XX as [st3' [m3' [d23' [mu23' [IntIncr23 [InjSep23 
             [LocAlloc23 [MC23' [ZZ INV']]]]]]]]].
  exists st3', m3', (d12', Some c2', d23'), mu12', mu23'.
  split. eapply compose_se_sm_intern_incr; eassumption.
  split. eapply compose_se_sm_inject_separated; eassumption.
  split. eapply compose_se_sm_locally_allocated; eassumption.
  split. exists c2'.
     split. reflexivity.
     split; trivial.
  split; assumption.
  (*proof of the cut*)
  destruct LocAlloc12 as [locLocAlloc12' extLocAlloc12'].
  assert (pubAlloc12': pubBlocks mu12 = pubBlocks mu12').
         eapply EqIncr12. 
  assert (frgnAlloc12': frgnBlocks mu12 = frgnBlocks mu12').
         eapply EqIncr12. 
  clear EqIncr12 MC12' EqSep12. 
  destruct INV as [InvLoc [InvExt [InvPub InvFrgn]]].
  rewrite InvLoc, InvExt in *. clear InvLoc InvExt.
  clear st1 st1' C1 Sem1 match_core12 g1.
  rewrite pubAlloc12', frgnAlloc12' in *.
  clear pubAlloc12' frgnAlloc12'.
  unfold SE_SM_INV.
  rewrite locLocAlloc12', extLocAlloc12'.
  clear locLocAlloc12' extLocAlloc12'.
  remember (pubBlocks mu12') as pubBlocks12'.
  remember (frgnBlocks mu12') as frgnBlocks12'.
  clear HeqpubBlocks12' HeqfrgnBlocks12'.
  clear mu12'.
  revert mu23 m d23 c2 st3 m3 H MC23 InvPub InvFrgn.
  induction x; intros. 
   (*base case*) simpl in H.
    destruct H as [st2 [m'' [? ?]]].
    inv H0.
    destruct (CD23 _ _ _ _ H _ _ _ _ MC23) 
      as [st3' [m3' [d23' [mu' [EqInc23 [EqSep23
          [LocAlloc23 [? ?]]]]]]]]; clear CD23.
    exists st3', m3', d23', mu'. 
    split; trivial.
    split; trivial.
    split; trivial.
    split; trivial.
    split. destruct H1. left; assumption.
           destruct H1. right. split; trivial.
             apply t_step. constructor 2. apply H2.
    apply sm_locally_allocatedChar in LocAlloc23. 
      destruct LocAlloc23 as [Dom' [Tgt' [LocS' [LocT' [ExtS' ExtT']]]]].
      rewrite <- LocS', ExtS'. split; trivial. split; trivial.
      destruct EqInc23 as [_ [_ [_ [_ [PP [_ [FF _]]]]]]].
      rewrite <- PP, <- FF. split; assumption.   
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    destruct H as [st2'' [m'' [? ?]]]. subst x'.
    destruct (CD23 _ _ _ _  H _ _ _ _ MC23) 
      as [c3' [m3' [d23' [mu23' [InjInc23 [InjSep23 
             [LocAlloc23 [? ?]]]]]]]]; clear CD23.
    specialize (IHx _ _ _ _ _ _ H0 H1).
    destruct IHx as [c3'' [m3'' [d23'' [mu23'' [InjIncr23' 
             [InjSep23' [LocAlloc23' [MC' [XX INV'']]]]]]]]].
      assert (pubBlocksSrc mu23 = pubBlocksSrc mu23') by eapply InjInc23.
      rewrite <- H3; assumption.
      assert (frgnBlocksSrc mu23 = frgnBlocksSrc mu23') by eapply InjInc23.
      rewrite <- H3; assumption.
    exists c3'', m3'', d23'', mu23''.
    split. eapply intern_incr_trans; eassumption. 
    split. eapply intern_separated_incr_fwd2; try eassumption.
           eapply corestep_fwd; eassumption.
           destruct H2 as [YY | [YY _]].
             eapply corestep_plus_fwd; eassumption.
             eapply corestep_star_fwd; eassumption.
           eauto. 
    split. eapply sm_locally_allocated_trans; try eassumption.
           eapply corestep_fwd; eassumption.
           eapply corestepN_fwd; eassumption.
           destruct H2 as [YY | [YY _]].
             eapply corestep_plus_fwd; eassumption.
             eapply corestep_star_fwd; eassumption.
           destruct XX as [YY | [YY _]].
             eapply corestep_plus_fwd; eassumption.
             eapply corestep_star_fwd; eassumption.           
    split. trivial.
    split. destruct H2; destruct XX.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H3.
               left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*4/4*)
               right. destruct H2. destruct H3.
               split. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
               eapply t_trans.
                 apply H5. clear H5.  
                 apply t_step.
                 constructor 2. apply H4.
         destruct INV'' as [Loc'' [Ext'' [Pub'' Frgn'']]].
           rewrite <- Loc'', <- Ext''; clear Loc'' Ext''.
           rewrite sm_locally_allocatedChar in LocAlloc23.
           destruct LocAlloc23 as [Dom23' [Tgt23' [LocS23' [LocT23' [ExtS23' ExtT23']]]]].
           rewrite LocS23', ExtS23'; clear LocS23' ExtS23'.
           split. extensionality b.
                  rewrite <- orb_assoc, freshloc_trans; trivial.
                    eapply corestep_fwd; eassumption. 
                    eapply corestepN_fwd; eassumption.
           split; trivial.
           split; trivial.
  (*case 2*)
   inv CS2. clear CD23.
   exists st3, m3, (d12',Some c2',d23), mu12', mu23.
   split. eapply compose_se_sm_intern_incr; try eassumption.
              eapply intern_incr_refl.
   split. eapply compose_se_sm_inject_separated; try eassumption.
              eapply sm_inject_separated_same_sminj.
   split. rewrite sm_locally_allocatedChar. simpl.
          destruct EqIncr12 as [Loc12 [Pub12 [Frgn12 Ext12]]]. 
          destruct LocAlloc12 as [L12a L12b].
          split. extensionality b.
             repeat rewrite compose_se_sm_DomSrc.
             unfold Blocks. rewrite Ext12, L12a.
             repeat rewrite freshloc_irrefl, orb_false_r.
             rewrite orb_false_r. trivial.
          split. extensionality b.
             repeat rewrite compose_se_sm_DomTgt.
             repeat rewrite freshloc_irrefl, orb_false_r. trivial.
          split; trivial.
          split. extensionality b.
             rewrite freshloc_irrefl, orb_false_r. trivial.
          rewrite Ext12; split; trivial.
   split. exists c2'; eauto.
   split. right. split. exists O. simpl; auto.
      apply t_step. constructor 1; auto.
   red. destruct EqIncr12 as [Loc12 [Pub12 [Frgn12 Ext12]]].
          destruct INV as [InvL [InvE [InvP InvF]]]. 
          destruct LocAlloc12 as [L12a L12b].
          rewrite L12a, L12b; clear L12a L12b.
          split.
             extensionality b.
             rewrite freshloc_irrefl, orb_false_r. rewrite InvL; trivial.
          split. trivial.
          rewrite <- Pub12, <- Frgn12 in *. split; trivial.
Qed.

Lemma eqinj_effcorediagram_trans: forall 
      (core_data12:Type)
      (match_core12: core_data12 -> SM_Equality -> C1 -> mem -> C2 -> Prop)
      (core_ord12 : core_data12 -> core_data12 -> Prop)
      (CD12: forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem)
                      (U1 : block -> Z -> bool),
                    effstep Sem1 g1 U1 st1 m st1' m' ->
                    forall (cd : core_data12) (st2 : C2) (mu : SM_Equality),
                    (forall (b1 : block) (z : Z),
                     U1 b1 z = true -> visEq mu b1 = true) ->
                    match_core12 cd mu st1 m st2 ->
                    exists
                      (st2' : C2) (cd' : core_data12) (mu' : SM_Equality),
                      eq_intern_incr mu mu' /\
                      eq_inject_separated mu mu' m /\
                      eq_locally_allocated mu mu' m m' /\
                      match_core12 cd' mu' st1' m' st2' /\
                      (exists U2 : block -> Z -> bool,
                         (effstep_plus Sem2 g2 U2 st2 m st2' m' \/
                          effstep_star Sem2 g2 U2 st2 m st2' m' /\
                          core_ord12 cd' cd) /\
                         (forall (b : block) (ofs : Z),
                          U2 b ofs = true ->
                          visEq mu b = true /\
                          (locBlocks mu b = false ->
                           frgnBlocks mu b = true /\
                           U1 b ofs = true /\ Mem.perm m b ofs Max Nonempty))))
      (core_data23 : Type)
      (match_core23 : core_data23 -> SM_Injection -> C2 -> mem -> C3 -> mem -> Prop)
      (MatchWD23: forall cd mu st2 m2 st3 m3,
                 match_core23 cd mu st2 m2 st3 m3 -> SM_wd mu)
      (match_validblock23 : forall cd mu st2 m2 st3 m3,
                 match_core23 cd mu st2 m2 st3 m3 ->  sm_valid mu m2 m3)
      (core_ord23 : core_data23 -> core_data23 -> Prop)
      (CD23 : forall (st2 : C2) (m2 : mem) (st2' : C2) (m2' : mem)
                     (U2 : block -> Z -> bool),
                 effstep Sem2 g2 U2 st2 m2 st2' m2' ->
                 forall (cd : core_data23) (st3 : C3) (mu : SM_Injection)
                   (m3 : mem),
                 (forall b2 z, U2 b2 z = true -> vis mu b2 = true) ->
                 match_core23 cd mu st2 m2 st3 m3 ->
                 exists
                   (st3' : C3) (m3' : mem) (cd' : core_data23) (mu' : SM_Injection),
                   intern_incr mu mu' /\ 
                   sm_inject_separated mu mu' m2 m3 /\
                   sm_locally_allocated mu mu' m2 m3 m2' m3' /\ 
                   match_core23 cd' mu' st2' m2' st3' m3' /\
                   (exists U3 : block -> Z -> bool,
                      (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
                       (effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
                        core_ord23 cd' cd)) 
                    /\ (forall b3 ofs, U3 b3 ofs = true ->
                          (visTgt mu b3 = true /\
                           (locBlocksTgt mu b3 = false->
                           exists b2 delta2, foreign_of mu b2 = Some(b3,delta2) /\
                           U2 b2 (ofs-delta2) = true /\ 
                           Mem.perm m2 b2 (ofs-delta2) Max Nonempty))))),
forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem) (U1 : block -> Z -> bool)
    (CS: effstep Sem1 g1 U1 st1 m st1' m')
    (cd : core_data12 * option C2 * core_data23) (st3 : C3) mu12 mu23 m3,
(let (y, d2) := cd in
 let (d1, X) := y in
 exists c2 : C2, 
   X = Some c2 /\ match_core12 d1 mu12 st1 m c2 /\ 
   match_core23 d2 mu23 c2 m st3 m3 /\
   SE_SM_INV mu12 mu23) ->
forall (UHyp: forall b1 z, U1 b1 z = true -> vis (compose_se_sm mu12 mu23) b1 = true),
exists
  (st3' : C3) m3' (cd' : core_data12 * option C2 * core_data23) mu12' mu23',
  intern_incr (compose_se_sm mu12 mu23) (compose_se_sm mu12' mu23') /\
  sm_inject_separated (compose_se_sm mu12 mu23) (compose_se_sm mu12' mu23') m m3 /\
  sm_locally_allocated (compose_se_sm mu12 mu23) (compose_se_sm mu12' mu23') m m3 m' m3' /\
  (let (y, d2) := cd' in
   let (d1, X) := y in
   exists c2 : C2,
     X = Some c2 /\
     match_core12 d1 mu12' st1' m' c2 /\ match_core23 d2 mu23' c2 m' st3' m3') /\
  (exists U3 : block -> Z -> bool,
    (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
     effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
     clos_trans (core_data12 * option C2 * core_data23)
       (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd' cd) /\
    SE_SM_INV mu12' mu23' /\
    (forall (b3 : block) (ofs : Z),
      U3 b3 ofs = true ->
      visTgt (compose_se_sm mu12 mu23) b3 = true /\
      (locBlocksTgt (compose_se_sm mu12 mu23) b3 = false ->
        exists b1 delta,
          foreign_of (compose_se_sm mu12 mu23) b1 = Some(b3,delta) /\
          U1 b1 (ofs-delta) = true /\ Mem.perm m b1 (ofs-delta) Max Nonempty))).
Proof. intros.
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [X [MC12 [MC23 INV]]]]; subst.
  assert (VIS12: vis (compose_se_sm mu12 mu23) = visEq mu12).
    clear CD12 CD23 CS MC12 MC23 UHyp. unfold vis, visEq; trivial.
  rewrite VIS12 in *.
  destruct (CD12 _ _ _ _ _ CS _ _ _ UHyp MC12)
    as [c2' [d12' [mu12' [EqIncr12 [EqSep12 [LocAlloc12
       [MC12' [U2 [Y U2Spec]]]]]]]]]; clear CD12 CS.
  assert (ZZ: effstep_plus Sem2 g2 U2 c2 m c2' m' \/
    (c2,m) = (c2',m') /\ (U2 = fun b z => false) /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
    simpl in H. destruct H. right. split; trivial. split; auto.
  left. exists x; auto.
  clear Y. destruct ZZ as [CS2 | [CS2 [U2Empty ord12']]].
 (*case1*) 
  destruct CS2.
  clear MC12.
  cut (exists st3', exists m3', exists d23', exists mu23',
      intern_incr mu23 mu23' /\
      sm_inject_separated mu23 mu23' m m3 /\
      sm_locally_allocated mu23 mu23' m m3 m' m3' /\
    match_core23 d23' mu23' c2' m' st3' m3' /\
    (exists U3, 
     (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
      (effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)
               (d12', Some c2', d23')
               (d12, Some c2, d23))) /\
      SE_SM_INV mu12' mu23' /\
     (forall (b3 : block) (ofs : Z),
      U3 b3 ofs = true ->
      visTgt mu23 b3 = true /\
      (locBlocksTgt mu23 b3 = false ->
        exists b2 delta2,
          foreign_of mu23 b2 = Some(b3,delta2) /\
          U2 b2 (ofs-delta2) = true /\
          Mem.perm m b2 (ofs-delta2) Max Nonempty)))).
  intros XX; destruct XX as [st3' [m3' [d23' [mu23' [IntIncr23 [InjSep23 
             [LocAlloc23 [MC23' [U3 [ZZ [INV' U3Spec]]]]]]]]]]].
  exists st3', m3', (d12', Some c2', d23'), mu12', mu23'.
  split. eapply compose_se_sm_intern_incr; eassumption.
  split. eapply compose_se_sm_inject_separated; eassumption.
  split. eapply compose_se_sm_locally_allocated; eassumption.
  split. exists c2'.
     split. reflexivity.
     split; trivial.
  exists U3.
  split. assumption.
  split. assumption. 
  simpl. intros. destruct (U3Spec _ _ H0).
    split. unfold visTgt; simpl. apply H1.
    intros. destruct INV as [LOC [EXT [PUB FRGN]]].
            rewrite LOC in *. 
            destruct (H2 H3) as [b [d [Frg [U2b Pb]]]].
            exists b, d.
            destruct (U2Spec _ _ U2b) as [VIS1 X].
            destruct X as [? [? ?]].
            eapply foreign_DomRng; try eassumption. eauto. 
            rewrite H4. apply foreign_in_extern in Frg. auto. 
  (*proof of the cut*)
  destruct LocAlloc12 as [locLocAlloc12' extLocAlloc12'].
  assert (pubAlloc12': pubBlocks mu12 = pubBlocks mu12').
         eapply EqIncr12. 
  assert (frgnAlloc12': frgnBlocks mu12 = frgnBlocks mu12').
         eapply EqIncr12. 
  clear EqIncr12 MC12' EqSep12. 
  destruct INV as [InvLoc [InvExt [InvPub InvFrgn]]].
  rewrite InvLoc, InvExt in *. 
  clear st1 st1' C1 Sem1 match_core12 g1.
  rewrite pubAlloc12', frgnAlloc12' in *.
  assert (U2Hyp : forall b2 z, U2 b2 z = true -> vis mu23 b2 = true).
      intros. unfold vis.
      destruct (U2Spec _ _ H0) as [VS _]. unfold visEq in VS.
      rewrite InvLoc, frgnAlloc12' in VS.
      remember (locBlocksSrc mu23 b2) as d.
      destruct d; apply eq_sym in Heqd; simpl in *; intuition.
  clear InvLoc InvExt pubAlloc12' frgnAlloc12'.
  unfold SE_SM_INV.
  rewrite locLocAlloc12', extLocAlloc12'.
  clear locLocAlloc12' extLocAlloc12'.
  remember (pubBlocks mu12') as pubBlocks12'.
  remember (frgnBlocks mu12') as frgnBlocks12'.
  clear HeqpubBlocks12' HeqfrgnBlocks12'.
  clear UHyp U1 U2Spec VIS12 mu12'.
  revert U2 mu23 m d23 c2 st3 m3 H MC23 InvPub InvFrgn U2Hyp.
  induction x; intros. 
   (*base case*) simpl in H.
    destruct H as [st2 [m2' [U2a [U2b [CS2 [[? ?] HU2]]]]]].
    inv H. simpl in *. 
    assert (forall b2 z, U2a b2 z = true -> vis mu23 b2 = true).
       intros. eapply (U2Hyp _ z). rewrite orb_false_r; trivial.
    clear U2Hyp; rename H into U2Hyp.
    destruct (CD23 _ _ _ _ _ CS2 _ _ _ _ U2Hyp MC23) 
      as [st3' [m3' [d23' [mu' [EqInc23 [EqSep23
          [LocAlloc23 [? [U3 [? U3Spec]]]]]]]]]]; clear CD23.
    exists st3', m3', d23', mu'. 
    split; trivial.
    split; trivial.
    split; trivial.
    split; trivial.
    exists U3. 
    split. destruct H0. left; assumption.
           destruct H0. right. split; trivial.
             apply t_step. constructor 2. apply H1.
    split. apply sm_locally_allocatedChar in LocAlloc23. 
      destruct LocAlloc23 as [Dom' [Tgt' [LocS' [LocT' [ExtS' ExtT']]]]].
      rewrite <- LocS', ExtS'. split; trivial. split; trivial.
      destruct EqInc23 as [_ [_ [_ [_ [PP [_ [FF _]]]]]]].
      rewrite <- PP, <- FF. split; assumption.
    intros. destruct (U3Spec _ _ H1). 
        split; trivial. 
        intros. destruct (H3 H4) as [b2 [d3 [FRG [UU2 PP]]]].
         exists b2, d3. rewrite orb_false_r. auto.   
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    destruct H as [st2'' [m'' [U2a [U2b [? [? U2Spec]]]]]]. subst x'.
    assert (U2aHyp:forall b2 z, U2a b2 z = true -> vis mu23 b2 = true).
      intros. clear IHx. subst U2. eapply (U2Hyp _ z).
      rewrite H1; trivial. 
    destruct (CD23 _ _ _ _ _ H _ _ _ _ U2aHyp MC23) 
      as [c3' [m3' [d23' [mu23' [InjInc23 [InjSep23 
             [LocAlloc23 [? [U3a [? U3aSpec]]]]]]]]]]; clear CD23.
    assert (U2bHyp: forall b2 z, U2b b2 z = true -> vis mu23' b2 = true).
      clear IHx U3aSpec H2. intros.
      assert (VAL:= effstepN_valid _ _ _ _ _ _ _ _ H0 _ _ H2).
      rewrite sm_locally_allocatedChar in LocAlloc23.
      assert (L23': locBlocksSrc mu23' =
                   (fun b => locBlocksSrc mu23 b || freshloc m m'' b)) by eapply LocAlloc23; clear LocAlloc23.
      assert (F23: frgnBlocksSrc mu23 = frgnBlocksSrc mu23') by eapply InjInc23.
      unfold vis. rewrite <- F23, L23'. clear F23 L23'.
      remember (freshloc m m'' b2) as d.
      destruct d; apply eq_sym in Heqd. intuition.
      rewrite orb_false_r. eapply (U2Hyp _ z). subst U2.
      rewrite H2. unfold freshloc in Heqd. simpl.
      destruct (valid_block_dec m'' b2); simpl in *; try contradiction.
      destruct (valid_block_dec m b2); try discriminate. intuition.
    specialize (IHx _ _ _ _ _ _ _ H0 H1).
    destruct IHx as [c3'' [m3'' [d23'' [mu23'' [InjIncr23' 
             [InjSep23' [LocAlloc23' [MC' [U3b [XX [INV'' U3bSpec]]]]]]]]]]].
      assert (pubBlocksSrc mu23 = pubBlocksSrc mu23') by eapply InjInc23.
        rewrite <- H3; assumption.
      assert (frgnBlocksSrc mu23 = frgnBlocksSrc mu23') by eapply InjInc23.
        rewrite <- H3; assumption.
      assumption.
    exists c3'', m3'', d23'', mu23''.
    split. eapply intern_incr_trans; eassumption. 
    split. eapply intern_separated_incr_fwd2; try eassumption.
           eapply effstep_fwd; eassumption.
           destruct H2 as [YY | [YY _]].
             eapply effstep_plus_fwd; eassumption.
             eapply effstep_star_fwd; eassumption.
           eauto. 
    split. eapply sm_locally_allocated_trans; try eassumption.
           eapply effstep_fwd; eassumption.
           eapply effstepN_fwd; eassumption.
           destruct H2 as [YY | [YY _]].
             eapply effstep_plus_fwd; eassumption.
             eapply effstep_star_fwd; eassumption.
           destruct XX as [YY | [YY _]].
             eapply effstep_plus_fwd; eassumption.
             eapply effstep_star_fwd; eassumption.           
    split. trivial.
    exists (fun b z => U3a b z || U3b b z && valid_block_dec m3 b).
    split. destruct H2; destruct XX.
           (*1/4*)
              left.
              eapply effstep_plus_trans; eassumption.
           (*2/4*)
              left. destruct H3 as [EFF3 CT].
              eapply effstep_plus_star_trans; eassumption. 
           (*3/4*)
               left. destruct H2 as [EFF3 CORD].
               eapply effstep_star_plus_trans; eassumption.
           (*4/4*)
               right. destruct H2 as [EFF3 CORD].
                      destruct H3 as [EFF3' CT].
               split. eapply effstep_star_trans; eassumption.
               eapply t_trans.
                 apply CT. clear CT.  
                 apply t_step.
                 constructor 2. apply CORD.
         destruct INV'' as [Loc'' [Ext'' [Pub'' Frgn'']]].
           rewrite <- Loc'', <- Ext''; clear Loc'' Ext''.
           rewrite sm_locally_allocatedChar in LocAlloc23.
           destruct LocAlloc23 as [Dom23' [Tgt23' [LocS23' [LocT23' [ExtS23' ExtT23']]]]].
           rewrite LocS23', ExtS23'; clear LocS23' ExtS23'.
           split.
             split. extensionality b.
                    rewrite <- orb_assoc, freshloc_trans; trivial.
                    eapply effstep_fwd; eassumption. 
                    eapply effstepN_fwd; eassumption.
             split; trivial.
             split; trivial.
           intros. apply orb_true_iff in H3.
             destruct H3.
               destruct (U3aSpec _ _ H3).
               split; trivial.
               intros. subst U2. destruct (H5 H6) as [b2 [d3 [Frg [U2b2 P2]]]].
                 exists b2, d3. rewrite U2b2; simpl. auto.
             apply andb_true_iff in H3; destruct H3.
               destruct (U3bSpec _ _ H3). unfold visTgt in H5.
               assert (FT23': frgnBlocksTgt mu23 = frgnBlocksTgt mu23') by eapply InjInc23.
               rewrite LocT23', <- FT23' in *.
               assert (FR3: freshloc m3 m3' b3 = false). 
                  unfold freshloc. rewrite H4. simpl. apply andb_false_r.
               rewrite FR3, orb_false_r in *.
               split. apply H5.
               intros. destruct (H6 H7) as [b2 [d2 [Frg23 [U2b2 Pb2]]]].   
                 exists b2, d2. rewrite <- (intern_incr_foreign _ _ InjInc23) in Frg23.
                 assert (VB2: Mem.valid_block m b2). 
                    eapply (match_validblock23 _ _ _ _ _ _ MC23).
                    eapply foreign_DomRng; try eassumption.
                       eauto.
                 split. trivial.
                 split. subst U2. rewrite U2b2. 
                    destruct (valid_block_dec m b2). intuition. contradiction.
                 eapply effstep_fwd; eassumption.
  (*case 2*)
   inv CS2. clear CD23 U2Spec.
   exists st3, m3, (d12',Some c2',d23), mu12', mu23.
   split. eapply compose_se_sm_intern_incr; try eassumption.
              eapply intern_incr_refl.
   split. eapply compose_se_sm_inject_separated; try eassumption.
              eapply sm_inject_separated_same_sminj.
   split. rewrite sm_locally_allocatedChar. simpl.
          destruct EqIncr12 as [Loc12 [Pub12 [Frgn12 Ext12]]]. 
          destruct LocAlloc12 as [L12a L12b].
          split. extensionality b.
             repeat rewrite compose_se_sm_DomSrc.
             unfold Blocks. rewrite Ext12, L12a.
             repeat rewrite freshloc_irrefl, orb_false_r.
             rewrite orb_false_r. trivial.
          split. extensionality b.
             repeat rewrite compose_se_sm_DomTgt.
             repeat rewrite freshloc_irrefl, orb_false_r. trivial.
          split; trivial.
          split. extensionality b.
             rewrite freshloc_irrefl, orb_false_r. trivial.
          rewrite Ext12; split; trivial.
   split. exists c2'; eauto.
   exists (fun b z => false). 
   split. right. split. exists O. simpl; auto.
      apply t_step. constructor 1; auto.
   split. red. destruct EqIncr12 as [Loc12 [Pub12 [Frgn12 Ext12]]].
          destruct INV as [InvL [InvE [InvP InvF]]]. 
          destruct LocAlloc12 as [L12a L12b].
          rewrite L12a, L12b; clear L12a L12b.
          split.
             extensionality b.
             rewrite freshloc_irrefl, orb_false_r. rewrite InvL; trivial.
          split. trivial.
          rewrite <- Pub12, <- Frgn12 in *. split; trivial.
   intros; discriminate.
Qed.
*)

Lemma injeq_corediagram_trans: forall
      (core_data12 : Type)
      (match_core12 : core_data12 -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop)
      (core_ord12 : core_data12 -> core_data12 -> Prop)
      (core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 g1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (mu : SM_Injection)
                   (m2 : mem),
                 match_core12 cd mu st1 m1 st2 m2 ->
                 exists
                   (st2' : C2) (m2' : mem) (cd' : core_data12) (mu' : SM_Injection),
                   intern_incr mu mu' /\
                   sm_inject_separated mu mu' m1 m2 /\
                   sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                   match_core12 cd' mu' st1' m1' st2' m2' /\
                   (corestep_plus Sem2 g2 st2 m2 st2' m2' \/
                    corestep_star Sem2 g2 st2 m2 st2' m2' /\
                    core_ord12 cd' cd))
      (core_data23 : Type)
      (match_core23 : core_data23 -> SM_Equality -> C2 -> mem -> C3 -> Prop)
      (core_ord23 : core_data23 -> core_data23 -> Prop)
      (core_diagram23 : forall (st2 : C2) (m : mem) (st2' : C2) (m' : mem),
                 corestep Sem2 g2 st2 m st2' m' ->
                 forall (cd : core_data23) (st3 : C3) (mu : SM_Equality),
                 match_core23 cd mu st2 m st3 ->
                 exists (st3' : C3) (cd' : core_data23) (mu' : SM_Equality),
                   eq_intern_incr mu mu' /\
                   eq_inject_separated mu mu' m /\
                   eq_locally_allocated mu mu' m m' /\
                   match_core23 cd' mu' st2' m' st3' /\
                   (corestep_plus Sem3 g3 st3 m st3' m' \/
                    corestep_star Sem3 g3 st3 m st3' m' /\ core_ord23 cd' cd)),
forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
       corestep Sem1 g1 st1 m1 st1' m1' ->
forall (cd : core_data12 * option C2 * core_data23) (st3 : C3)
  (mu : SM_Injection) (m3 : mem),
(let (y, d2) := cd in
 let (d1, X) := y in
 exists (c2 : C2) (mu12 : SM_Injection) (mu23 : SM_Equality),
   X = Some c2 /\
   mu = compose_sm_se mu12 mu23 /\
   match_core12 d1 mu12 st1 m1 c2 m3 /\
   match_core23 d2 mu23 c2 m3 st3 /\ SM_SE_INV mu12 mu23) ->
exists (st3' : C3) (m3' : mem) (cd' : core_data12 * option C2 * core_data23) 
       (mu' : SM_Injection),
  intern_incr mu mu' /\
  sm_inject_separated mu mu' m1 m3 /\
  sm_locally_allocated mu mu' m1 m3 m1' m3' /\
  (let (y, d2) := cd' in
   let (d1, X) := y in
   exists (c2 : C2) (mu12 : SM_Injection) (mu23 : SM_Equality),
     X = Some c2 /\
     mu' = compose_sm_se mu12 mu23 /\
     match_core12 d1 mu12 st1' m1' c2 m3' /\
     match_core23 d2 mu23 c2 m3' st3' /\ SM_SE_INV mu12 mu23) /\
  (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
   corestep_star Sem3 g3 st3 m3 st3' m3' /\
   clos_trans (core_data12 * option C2 * core_data23)
     (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd' cd).
Proof. intros. 
  destruct cd as [[d12 cc2] d23].
  destruct H0 as [c2 [mu12 [mu23 [X [MU [MC12 [MC23 INV]]]]]]]; subst.
  destruct (core_diagram12 _ _ _ _ H _ _ _ _ MC12)
    as [c2' [m3' [d12' [mu12' [Incr12 [Sep12 [LocAlloc12
       [MC12' Y]]]]]]]]; clear core_diagram12 H.
  assert (ZZ: corestep_plus Sem2 g2 c2 m3 c2' m3' \/
    (c2,m3) = (c2',m3') /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
  right. split; auto.
  left. exists x; auto.
  clear Y. destruct ZZ as [CS2 | [CS2 ord12']].
 (*case1*) 
  destruct CS2.
  clear MC12.
  cut (exists st3', exists d23', exists mu23'',
      eq_intern_incr mu23 mu23'' /\
      eq_inject_separated mu23 mu23'' m3 /\
      eq_locally_allocated mu23 mu23'' m3 m3' /\
    match_core23 d23' mu23'' c2' m3' st3' /\
    (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
      (corestep_star Sem3 g3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)
               (d12', Some c2', d23')
               (d12, Some c2, d23)))).
  intros XX; destruct XX as [st3' [d23' [mu23' [EqIncr23 [EqSep23 [LocAlloc23 [MC23' ZZ]]]]]]].
  exists st3', m3', (d12', Some c2', d23'), (compose_sm_se mu12' mu23'). 
  split. clear - Incr12 EqIncr23.
         red; simpl. 
         split. apply Incr12.
         repeat split; try apply Incr12; try apply EqIncr23.
  split. clear - INV Sep12 EqSep23.
         red; simpl. 
         repeat rewrite compose_sm_se_as_inj, compose_sm_se_DomSrc, compose_sm_se_DomTgt.
         destruct Sep12 as [Sep12A [Sep12B Sep12C]].
         rewrite <- (SM_SE_INV_DomTgtBlocks _ _ INV).
         split. apply Sep12A.
         split. apply Sep12B.
         rewrite (SM_SE_INV_DomTgtBlocks _ _ INV). 
         apply EqSep23.
  split. clear - LocAlloc23 LocAlloc12.
         red; simpl.
         rewrite sm_locally_allocatedChar in LocAlloc12.
         destruct LocAlloc12 as [LA12A [LA12B [LA12C [LA12D [LA12E LA12F]]]]].
         destruct LocAlloc23 as [LA23A LA23B].
         split. assumption.
         split. assumption.
         split; assumption. 
  split. exists c2', mu12', mu23'.
     split. reflexivity.
     split; trivial.
     split; trivial.
     split; trivial.
     red; intros.
         rewrite sm_locally_allocatedChar in LocAlloc12.
         destruct LocAlloc12 as [LA12A [LA12B [LA12C [LA12D [LA12E LA12F]]]]].
         destruct LocAlloc23 as [LA23A LA23B].
         destruct INV as [InvA [InvB [InvC InvD]]].
         split. rewrite LA12D, LA23A, InvA. trivial.
         split. rewrite LA12F, LA23B, InvB. trivial.
         assert (PUB: pubBlocksTgt mu12 = pubBlocksTgt mu12') by eapply Incr12.
         assert (FRG: frgnBlocksTgt mu12 = frgnBlocksTgt mu12') by eapply Incr12.
         rewrite <- PUB, <- FRG.
         destruct EqIncr23 as [Inc23A [Inc23B [Inc23C Inc23D]]].
         rewrite <- Inc23B, <- Inc23C.
         split; assumption.
     assumption.
  (*proof of the cut*)
  clear MC12' Incr12 Sep12 LocAlloc12 st1 st1' C1 Sem1 
        match_core12 g1 mu12' m1 m1' mu12 INV.
  revert mu23 m3 d23 c2 st3 H MC23.
  induction x; intros. 
   (*base case*) simpl in H.
    destruct H as [st2 [m3'' [? ?]]].
    inv H0.
    destruct (core_diagram23 _ _ _ _ H _ _ _ MC23) 
      as [st3' [d23' [mu23' [EqInc23 [EqSep23
          [LocAlloc23 [? ?]]]]]]]; clear core_diagram23.
    exists st3', d23', mu23'. 
    split; trivial.
    split; trivial.
    split; trivial.
    split; trivial.
    destruct H1. left; assumption.
           destruct H1. right. split; trivial.
           apply t_step. constructor 2. apply H2.
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    destruct H as [st3'' [m3'' [? ?]]]. subst x'.
    destruct (core_diagram23 _ _ _ _  H _ _ _ MC23) 
      as [c3' [d23' [mu23' [InjInc23 [InjSep23 
             [LocAlloc23 [? ?]]]]]]]; clear core_diagram23.
    destruct (IHx _ _ _ _ _ H0 H1)
       as [c3'' [d23'' [mu23'' [EqIncr' 
          [EqSep' [LocAlloc23' [MC' XX]]]]]]]; clear IHx.
    exists c3'', d23'', mu23''.
    split. eapply eq_intern_incr_trans; eassumption. 
    split. eapply eq_inject_separated_trans; try eassumption. 
           eapply corestep_fwd; eassumption.
    split. apply corestep_fwd in H.
           assert (FWD': mem_forward m3'' m3').
             destruct XX as [XX | [XX _]].
             eapply corestep_plus_fwd; eassumption.
             eapply corestep_star_fwd; eassumption.
           eapply eq_locally_allocated_trans; eassumption.
    split. trivial.
    destruct H2; destruct XX.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H3.
               left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*4/4*)
               right. destruct H2. destruct H3.
               split. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
               eapply t_trans.
                 apply H5. clear H5.  
                 apply t_step.
                 constructor 2. apply H4.
  (*case 2*)
   inv CS2.
   exists st3, m3', (d12',Some c2',d23), (compose_sm_se mu12' mu23).
   assert (PUB: pubBlocksTgt mu12 = pubBlocksTgt mu12') by eapply Incr12.
   assert (FRG: frgnBlocksTgt mu12 = frgnBlocksTgt mu12') by eapply Incr12.
   specialize (SM_SE_INV_DomTgtBlocks _ _ INV); intros BL.
   destruct INV as [InvA [InvB [InvC InvD]]]. 
   rewrite sm_locally_allocatedChar in LocAlloc12.
   destruct LocAlloc12 as [LA12A [LA12B [LA12C [LA12D [LA12E LA12F]]]]].
   split. red; simpl. intuition; apply Incr12; trivial. 
   split. red; simpl. repeat rewrite compose_sm_se_as_inj,
                              compose_sm_se_DomSrc, 
                              compose_sm_se_DomTgt.
          rewrite <- BL.
          split. eapply Sep12; eassumption.
          split. eapply Sep12; eassumption.
          intros; congruence.
   split. red; simpl. intuition. 
          extensionality b. rewrite freshloc_irrefl, orb_false_r. trivial.
   split. exists c2', mu12', mu23. split; trivial. split; trivial.
          split. assumption. split. assumption.
          red; simpl.
          rewrite <- PUB, <- FRG, <- InvA, <- InvB, LA12D. intuition.
          extensionality b. rewrite freshloc_irrefl. apply orb_false_r.
   right. split. exists O. simpl; auto.
      apply t_step. constructor 1; auto.
Qed.

Lemma injeq_effcorediagram_trans: forall
      (core_data12 : Type)
      (match_core12 : core_data12 -> SM_Injection -> C1 -> mem -> C2 -> mem -> Prop)
      (core_ord12 : core_data12 -> core_data12 -> Prop)
      (effcore_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem)
                      (U1 : block -> Z -> bool),
                    effstep Sem1 g1 U1 st1 m1 st1' m1' ->
                    forall (cd : core_data12) (st2 : C2) (mu : SM_Injection)
                      (m2 : mem),
                    (forall b1 z, U1 b1 z = true -> vis mu b1 = true) ->
                    match_core12 cd mu st1 m1 st2 m2 ->
                    exists
                      (st2' : C2) (m2' : mem) (cd' : core_data12) (mu' : SM_Injection),
                      intern_incr mu mu' /\
                      sm_inject_separated mu mu' m1 m2 /\
                      sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                      match_core12 cd' mu' st1' m1' st2' m2' /\
                      (exists U2 : block -> Z -> bool,
                         (effstep_plus Sem2 g2 U2 st2 m2 st2' m2' \/
                          effstep_star Sem2 g2 U2 st2 m2 st2' m2' /\
                          core_ord12 cd' cd) /\
                         (forall (b : block) (ofs : Z),
                          U2 b ofs = true ->
                          visTgt mu b = true /\
                          (locBlocksTgt mu b = false ->
                           exists (b1 : block) (delta1 : Z),
                             foreign_of mu b1 = Some (b, delta1) /\
                             U1 b1 (ofs - delta1) = true /\
                             Mem.perm m1 b1 (ofs - delta1) Max Nonempty))))
      (core_data23 : Type)
      (match_core23 : core_data23 -> SM_Equality -> C2 -> mem -> C3 -> Prop)
      (core_ord23 : core_data23 -> core_data23 -> Prop)
      (effcore_diagram23 : forall (st2 : C2) (m : mem) (st2' : C2) (m' : mem)
                      (U2 : block -> Z -> bool),
                    effstep Sem2 g2 U2 st2 m st2' m' ->
                    forall (cd : core_data23) (st3 : C3) (mu : SM_Equality),
                    (forall b1 z, U2 b1 z = true -> visEq mu b1 = true) ->
                    match_core23 cd mu st2 m st3 ->
                    exists
                      (st3' : C3) (cd' : core_data23) (mu' : SM_Equality),
                      eq_intern_incr mu mu' /\
                      eq_inject_separated mu mu' m /\
                      eq_locally_allocated mu mu' m m' /\
                      match_core23 cd' mu' st2' m' st3' /\
                      (exists U3 : block -> Z -> bool,
                         (effstep_plus Sem3 g3 U3 st3 m st3' m' \/
                          effstep_star Sem3 g3 U3 st3 m st3' m' /\
                          core_ord23 cd' cd) /\
                         (forall (b : block) (ofs : Z),
                          U3 b ofs = true ->
                          visEq mu b = true /\
                          (locBlocks mu b = false ->
                           frgnBlocks mu b = true /\
                           U2 b ofs = true /\ Mem.perm m b ofs Max Nonempty)))),
forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem) (U1 : block -> Z -> bool)
       (CS: effstep Sem1 g1 U1 st1 m1 st1' m1'), 
forall (cd : core_data12 * option C2 * core_data23) (st3 : C3)
       (mu : SM_Injection) (m3 : mem)
       (U1Hyp: forall (b1 : block) (z : Z), U1 b1 z = true -> vis mu b1 = true),
(let (y, d2) := cd in
 let (d1, X) := y in
 exists (c2 : C2) (mu12 : SM_Injection) (mu23 : SM_Equality),
   X = Some c2 /\
   mu = compose_sm_se mu12 mu23 /\
   match_core12 d1 mu12 st1 m1 c2 m3 /\
   match_core23 d2 mu23 c2 m3 st3 /\ SM_SE_INV mu12 mu23) ->
exists
  (st3' : C3) (m3' : mem) (cd' : core_data12 * option C2 * core_data23) 
(mu' : SM_Injection),
  intern_incr mu mu' /\
  sm_inject_separated mu mu' m1 m3 /\
  sm_locally_allocated mu mu' m1 m3 m1' m3' /\
  (let (y, d2) := cd' in
   let (d1, X) := y in
   exists (c2 : C2) (mu12 : SM_Injection) (mu23 : SM_Equality),
     X = Some c2 /\
     mu' = compose_sm_se mu12 mu23 /\
     match_core12 d1 mu12 st1' m1' c2 m3' /\
     match_core23 d2 mu23 c2 m3' st3' /\ SM_SE_INV mu12 mu23) /\
  (exists U3 : block -> Z -> bool,
     (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
      effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
      clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd' cd) /\
     (forall (b : block) (ofs : Z),
      U3 b ofs = true ->
      visTgt mu b = true /\
      (locBlocksTgt mu b = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b, delta1) /\
         U1 b1 (ofs - delta1) = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty))).
Proof. intros. 
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [mu12 [mu23 [X [MU [MC12 [MC23 INV]]]]]]]; subst.
  rewrite compose_sm_se_vis in U1Hyp.
  destruct (effcore_diagram12 _ _ _ _ _ CS _ _ _ _ U1Hyp MC12)
    as [c2' [m3' [d12' [mu12' [Incr12 [Sep12 [LocAlloc12
       [MC12' [U2 [Y U2Spec]]]]]]]]]]; clear effcore_diagram12 CS.
  assert (ZZ: effstep_plus Sem2 g2 U2 c2 m3 c2' m3' \/
    (c2,m3) = (c2',m3') /\ (U2=fun b z => false) /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x; simpl in *.
  destruct H. right. split. assumption. auto.
  left. exists x; auto.
  clear Y. destruct ZZ as [CS2 | [CS2 [U2emp ord12']]].
 (*case1*) 
  destruct CS2.
  clear MC12.
  cut (exists st3', exists d23', exists mu23'',
      eq_intern_incr mu23 mu23'' /\
      eq_inject_separated mu23 mu23'' m3 /\
      eq_locally_allocated mu23 mu23'' m3 m3' /\
    match_core23 d23' mu23'' c2' m3' st3' /\
    (exists U3: block -> Z -> bool,
      (effstep_plus Sem3 g3 U3 st3 m3 st3' m3' \/
      (effstep_star Sem3 g3 U3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)
               (d12', Some c2', d23')
               (d12, Some c2, d23)))
      /\ (forall b3 ofs, U3 b3 ofs = true ->
                 visEq mu23 b3 = true /\
                 (locBlocks mu23 b3 = false ->
                   frgnBlocks mu23 b3 = true /\
                   U2 b3 ofs = true /\ Mem.perm m3 b3 ofs Max Nonempty)))).
  intros XX; destruct XX as [st3' [d23' [mu23' [EqIncr23 [EqSep23 [LocAlloc23 [MC23' [U3 [ZZ U3Spec]]]]]]]]].
  exists st3', m3', (d12', Some c2', d23'), (compose_sm_se mu12' mu23'). 
  split. clear - Incr12 EqIncr23.
         red; simpl. 
         split. apply Incr12.
         repeat split; try apply Incr12; try apply EqIncr23.
  split. clear - INV Sep12 EqSep23.
         red; simpl. 
         repeat rewrite compose_sm_se_as_inj, compose_sm_se_DomSrc, compose_sm_se_DomTgt.
         destruct Sep12 as [Sep12A [Sep12B Sep12C]].
         rewrite <- (SM_SE_INV_DomTgtBlocks _ _ INV).
         split. apply Sep12A.
         split. apply Sep12B.
         rewrite (SM_SE_INV_DomTgtBlocks _ _ INV). 
         apply EqSep23.
  split. clear - LocAlloc23 LocAlloc12.
         red; simpl.
         rewrite sm_locally_allocatedChar in LocAlloc12.
         destruct LocAlloc12 as [LA12A [LA12B [LA12C [LA12D [LA12E LA12F]]]]].
         destruct LocAlloc23 as [LA23A LA23B].
         split. assumption.
         split. assumption.
         split; assumption. 
  split. exists c2', mu12', mu23'.
     split. reflexivity.
     split; trivial.
     split; trivial.
     split; trivial.
     red; intros.
         rewrite sm_locally_allocatedChar in LocAlloc12.
         destruct LocAlloc12 as [LA12A [LA12B [LA12C [LA12D [LA12E LA12F]]]]].
         destruct LocAlloc23 as [LA23A LA23B].
         destruct INV as [InvA [InvB [InvC InvD]]].
         split. rewrite LA12D, LA23A, InvA. trivial.
         split. rewrite LA12F, LA23B, InvB. trivial.
         assert (PUB: pubBlocksTgt mu12 = pubBlocksTgt mu12') by eapply Incr12.
         assert (FRG: frgnBlocksTgt mu12 = frgnBlocksTgt mu12') by eapply Incr12.
         rewrite <- PUB, <- FRG.
         destruct EqIncr23 as [Inc23A [Inc23B [Inc23C Inc23D]]].
         rewrite <- Inc23B, <- Inc23C.
         split; assumption.
     exists U3. 
      split. assumption.
      rewrite compose_sm_se_visTgt, compose_sm_se_foreign.
      intros. simpl.
         destruct (U3Spec _ _ H0); clear U3Spec.
         split; trivial.
         intros. destruct (H2 H3) as [? [? ?]]; clear H2.
         destruct (U2Spec _ _ H5); clear U2Spec.
         apply H7. destruct INV as [INVL _]; rewrite INVL. trivial.
  (*proof of the cut*)
  assert (U2Hyp: forall b1 z, U2 b1 z = true -> visEq mu23 b1 = true).
    intros. unfold visEq. destruct (U2Spec _ _ H0) as [VIS _].
     unfold visTgt in VIS. 
     destruct INV as [InvA [InvB [InvC InvD]]].
     rewrite InvA in VIS.
     destruct (locBlocks mu23 b1); simpl in *; trivial.
     apply (InvD _ VIS).
  clear MC12' Incr12 Sep12 LocAlloc12 st1 st1' C1 Sem1 
        match_core12 g1 mu12' m1 m1' mu12 INV U1Hyp U2Spec.
  revert U2 mu23 m3 d23 c2 st3 H MC23 U2Hyp.
  induction x; intros. 
   (*base case*) simpl in H.
    destruct H as [st2 [m3'' [U2a [U2b [? [[? U2bSpec] U2Split]]]]]].
    inv H0. simpl in *. 
    assert (U2aHyp: forall b2 z, U2a b2 z = true -> visEq mu23 b2 = true).
      intros. eapply (U2Hyp _ z). rewrite H0; trivial.
    destruct (effcore_diagram23 _ _ _ _ _ H _ _ _ U2aHyp MC23) 
      as [st3' [d23' [mu23' [EqInc23 [EqSep23
          [LocAlloc23 [? [U3 [? U3Spec]]]]]]]]]; clear effcore_diagram23.
    exists st3', d23', mu23'. 
    split; trivial.
    split; trivial.
    split; trivial.
    split; trivial.
    exists U3.
    split. destruct H1. left; assumption.
           destruct H1. right. split; trivial.
           apply t_step. constructor 2. apply H2.
    intros. rewrite orb_false_r. apply (U3Spec _ _ H2).
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    destruct H as [st3'' [m3'' [U2a [U2b [? [? U2Split]]]]]]. subst x'.
    assert (U2aHyp : forall b2 z, U2a b2 z = true -> visEq mu23 b2 = true).
      intros. apply (U2Hyp _ z). subst U2. rewrite H1. trivial.      
    destruct (effcore_diagram23 _ _ _ _ _ H _ _ _ U2aHyp MC23) 
      as [c3' [d23' [mu23' [EqInc23 [EqSep23 
             [LocAlloc23 [? [U3a [? U3aSpec]]]]]]]]]; clear effcore_diagram23.
    assert (FF: frgnBlocks mu23 = frgnBlocks mu23') by eapply EqInc23.
    assert (U2bHyp: forall b2 z, U2b b2 z = true -> visEq mu23' b2 = true).
      intros. unfold visEq. clear IHx U3aSpec H2. 
      assert (Mem.valid_block m3'' b2) by (eapply effstepN_valid; eassumption).
      destruct LocAlloc23. rewrite H4, <- FF.
      unfold freshloc.
      destruct (valid_block_dec m3'' b2); try contradiction; simpl. clear v.
      remember (valid_block_dec m3 b2) as d. 
      destruct d; simpl. 
        rewrite orb_false_r. subst U2; apply (U2Hyp b2 z).
        rewrite H3, <- Heqd. simpl. apply orb_true_r.
      rewrite orb_true_r; trivial.
    destruct (IHx _ _ _ _ _ _ H0 H1 U2bHyp)
       as [c3'' [d23'' [mu23'' [EqIncr' 
          [EqSep' [LocAlloc23' [MC' [U3b [XX U3bSpec]]]]]]]]]; clear IHx.
    exists c3'', d23'', mu23''.
    split. eapply eq_intern_incr_trans; eassumption. 
    split. eapply eq_inject_separated_trans; try eassumption. 
           eapply effstep_fwd; eassumption.
    split. apply effstep_fwd in H.
           assert (FWD': mem_forward m3'' m3').
             destruct XX as [XX | [XX _]].
             eapply effstep_plus_fwd; eassumption.
             eapply effstep_star_fwd; eassumption.
           eapply eq_locally_allocated_trans; eassumption.
    split. trivial.
    exists (fun b3 z => U3a b3 z || (U3b b3 z && valid_block_dec m3 b3)).
    split. clear U3bSpec U3aSpec. destruct H2; destruct XX.
           (*1/4*)
              left. eapply effstep_plus_trans; eassumption.
           (*2/4*)
              left. destruct H3 as [EFF3 CT].
              eapply effstep_plus_star_trans; eassumption. 
           (*3/4*)
               left. destruct H2 as [EFF3 CORD].
               eapply effstep_star_plus_trans; eassumption.
           (*4/4*)
               right. destruct H2 as [EFF3 CORD].
                      destruct H3 as [EFF3' CT].
               split. eapply effstep_star_trans; eassumption.
               eapply t_trans.
                 apply CT. clear CT.  
                 apply t_step.
                 constructor 2. apply CORD.
    subst U2. intros b3 ofs HU3.
      apply orb_true_iff in HU3.
      destruct HU3.
        destruct (U3aSpec _ _ H3). split; trivial.
        intros. destruct (H5 H6) as [Frg [HU2 Perm3]].
        rewrite HU2; auto.
      apply andb_true_iff in H3. destruct H3.
        rewrite H4, andb_true_r.
        destruct (U3bSpec _ _ H3).
        unfold visEq in H5; unfold visEq.
        destruct LocAlloc23. rewrite H7, <- FF in *.
        assert (freshloc m3 m3'' b3 = false).
          unfold freshloc. rewrite H4; simpl. apply andb_false_r.
        rewrite H9, orb_false_r in *. 
        split. assumption.
        intros. destruct (H6 H10) as [? [? ?]].
        rewrite H12, orb_true_r. split; trivial. split; trivial. 
        assert (FWD3: mem_forward m3 m3'').
          destruct H2 as [XX3 | [XX3 _]]. 
            eapply effstep_plus_fwd. eapply XX3. 
            eapply effstep_star_fwd. eapply XX3. 
        eapply FWD3; try eassumption. 
          destruct (valid_block_dec m3 b3); trivial; try discriminate.
  (*case 2*)
   inv CS2.
   exists st3, m3', (d12',Some c2',d23), (compose_sm_se mu12' mu23).
   assert (PUB: pubBlocksTgt mu12 = pubBlocksTgt mu12') by eapply Incr12.
   assert (FRG: frgnBlocksTgt mu12 = frgnBlocksTgt mu12') by eapply Incr12.
   specialize (SM_SE_INV_DomTgtBlocks _ _ INV); intros BL.
   destruct INV as [InvA [InvB [InvC InvD]]]. 
   rewrite sm_locally_allocatedChar in LocAlloc12.
   destruct LocAlloc12 as [LA12A [LA12B [LA12C [LA12D [LA12E LA12F]]]]].
   split. red; simpl. intuition; apply Incr12; trivial. 
   split. red; simpl. repeat rewrite compose_sm_se_as_inj,
                              compose_sm_se_DomSrc, 
                              compose_sm_se_DomTgt.
          rewrite <- BL.
          split. eapply Sep12; eassumption.
          split. eapply Sep12; eassumption.
          intros; congruence.
   split. red; simpl. intuition. 
          extensionality b. rewrite freshloc_irrefl, orb_false_r. trivial.
   split. exists c2', mu12', mu23. split; trivial. split; trivial.
          split. assumption. split. assumption.
          red; simpl.
          rewrite <- PUB, <- FRG, <- InvA, <- InvB, LA12D. intuition.
          extensionality b. rewrite freshloc_irrefl. apply orb_false_r.
   exists (fun b3 z => false).
   split. right. split. exists O. simpl; auto.
      apply t_step. constructor 1; auto.
   intros; discriminate. 
Qed.

Context epts12 epts23 epts13
        (EPC : entrypoints_compose epts12 epts23 epts13).

Lemma EQ_EQ (EQ12 : SE_simulation_equality Sem1 Sem2 g1 g2 epts12)
            (EQ23 : SE_simulation_equality Sem2 Sem3 g2 g3 epts23):
      SE_simulation_equality Sem1 Sem3 g1 g3 epts13.
Proof.
  intros.
  destruct EQ12 
    as [core_data12 match_core12 core_ord12 core_ord_wf12 
      match_se_wd12 genvs_dom_eq12 match_genv12
      match_visible12 match_restrict12 
      match_se_valid12 (*match_protected12*) core_initial12 
      core_diagram12 effcore_diagram12
      core_halted12 core_at_external12 eff_after_external12].  
  destruct EQ23 
    as [core_data23 match_core23 core_ord23 core_ord_wf23 
      match_se_wd23 genvs_dom_eq23 match_genv23
      match_visible23 match_restrict23
      match_se_valid23 (*match_protected23*) core_initial23 
      core_diagram23 effcore_diagram23
      core_halted23 core_at_external23 eff_after_external23].
  eapply Build_SE_simulation_equality with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d mu c1 m c3 => 
      match d with (d1,X,d2) => 
        exists c2, X=Some c2 /\ match_core12 d1 mu c1 m c2 /\ match_core23 d2 mu c2 m c3 
(*        exists c2, exists mu1, exists mu2,
          X=Some c2 /\ 
          (locBlocks mu1 = locBlocks mu2 /\
           extBlocks mu1 = extBlocks mu2 /\
           (forall b, pubBlocks mu1 b = true -> pubBlocks mu2 b = true) /\
           (forall b, frgnBlocks mu1 b = true -> frgnBlocks mu2 b = true)) /\ 
          match_core12 d1 mu1 c1 m c2 /\ match_core23 d2 mu2 c2 m c3 *)
      end).
 (*well_founded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
{ (*wd*) clear - match_se_wd12 match_se_wd23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct H as [c2 [? [MC12 MC23]]]; subst.
  eapply match_se_wd12; eassumption. }
{ (*genvs_domain_eq*) clear - genvs_dom_eq12 genvs_dom_eq23. 
  eapply genvs_domain_eq_trans; eassumption. }
{ (*match_genv*) clear - match_genv12 match_genv23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct MC as [c2 [? [MC12 MC23]]]; subst.
  eapply match_genv12; eassumption. }
{ (*match_visible*) clear - match_visible12 match_visible23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct H as [c2 [? [MC12 MC23]]]; subst.
  eapply match_visible12; eassumption. }
{ (*match_restrict*) clear - match_restrict12 match_restrict23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct H as [c2 [? [MC12 MC23]]]; subst.
  exists c2. eauto. }
{ (*match_validblocks*) 
  clear - match_se_valid12 match_se_valid23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct H as [c2 [? [MC12 MC23]]]; subst.
  eauto. }
{ (*initialcore*)
  clear - EPC genvs_dom_eq12 genvs_dom_eq23 core_initial12 core_initial23.
  intros. rename v2 into v3.
  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  destruct (core_initial12 _ _ _ EP12 _ _ _ _ H0 H1 H2)
    as [cd12 [c2 [Ini2 MC12]]].
  rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq12) in H1.            
  destruct (core_initial23 _ _ _ EP23 _ _ _ _ Ini2 H1 H2)
    as [cd23 [c3 [Ini3 MC23]]].
  rewrite <- (genvs_domain_eq_isGlobal _ _ genvs_dom_eq12) in MC23.
  exists (cd12,Some c2, cd23), c3.
  split; trivial.
  exists c2; split; trivial.
  split; trivial. }
{ (*core_diagram*)
  eapply eqeq_corediagram_trans; eassumption. }
{ (*effcore_diagram*)
  clear - effcore_diagram12 effcore_diagram23.
  eapply eqeq_effcorediagram_trans; eassumption. }
{ (*halted*)
  clear - core_halted12 core_halted23.
  intros. rename c2 into c3.  
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [? [MC12 MC23]]]; subst.
  specialize (core_halted12 _ _ _ _ _ _ MC12 H0).
  apply (core_halted23 _ _ _ _ _ _ MC23 core_halted12). }
(*at_external rule with args in visEq Mu
{ clear - core_at_external12 core_at_external23.
  intros. rename c2 into c3.
  rename H0 into AtExtSrc. 
  destruct cd as [[d12 cc2] d23]. 
  destruct H as [st2 [? [MC12 MC23]]]; subst.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 AtExtSrc)
    as [ArgsVis12 AtExt2]; clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2)
    as [_ AtExtTgt]; clear core_at_external23.
  split; assumption. }*)
(*at_external*)
{ clear - core_at_external12 core_at_external23.
  intros. rename c2 into c3.
  rename H0 into AtExtSrc. 
  destruct cd as [[d12 cc2] d23]. 
  destruct H as [st2 [? [MC12 MC23]]]; subst.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 AtExtSrc)
    as [RC AtExtMid]; clear core_at_external12.
  eauto. }
(*after_external*)
{ clear - core_at_external12 core_at_external23
          eff_after_external12 eff_after_external23. 
  intros. rename st2 into st3. 
  destruct cd as [[d12 cc2] d23].
  destruct MatchMu as [st2 [X [MC12 MC23]]].

  (*destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 AtExtSrc)
    as [ArgsVis12 AtExt2]; clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2)
    as [_ AtExtTgt']; clear core_at_external23.*)
  destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 AtExtSrc) 
     as [RCSrc AtExt2].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2)
     as [_ AtExtTgt'].
  clear core_at_external12 core_at_external23.

  assert (e' = e /\ ef_sig'=ef_sig).
    rewrite AtExtTgt in AtExtTgt'. inv AtExtTgt'. split; trivial.
  destruct H as [He Hefsig]. subst e'; subst ef_sig'. clear AtExtTgt'.
  destruct (eff_after_external12 _ _ _ _ _ _ _ _ _ _ MC12 AtExtSrc AtExt2
       (*ValsVis*) _ pubBlksHyp _ NuHyp _ ret _ INC SEP WDnu' SMvalNu' RValNu'
       RC' Fwd _ frgnBlksHyp _ Mu'Hyp UnchPriv) 
   as [cd12 [st1' [c2' [AftExt1 [AftExt2 MC12']]]]]; clear eff_after_external12.
  destruct (eff_after_external23 _ _ _ _ _ _ _ _ _ _ MC23 AtExt2 AtExtTgt
       (*ValsVis*) _ pubBlksHyp _ NuHyp _ _ _ INC SEP WDnu' SMvalNu' RValNu'
       RC' Fwd _ frgnBlksHyp _ Mu'Hyp UnchPriv)
   as [cd23 [st2' [st3' [AftExt2' [AftExt3 MC23']]]]]; clear eff_after_external23.
  assert (c2' = st2').
    rewrite AftExt2 in AftExt2'. inv AftExt2'. trivial.
  subst c2'.
  exists (cd12, Some st2', cd23), st1', st3'.
  split; trivial.
  split; trivial.
  exists st2'. split; trivial. split; trivial. }
Qed.

Lemma INJ_EQ (INJ12 : SM_simulation.SM_simulation_inject Sem1 Sem2 g1 g2 epts12)
             (EQ23 : SE_simulation_equality Sem2 Sem3 g2 g3 epts23):
      SM_simulation.SM_simulation_inject Sem1 Sem3 g1 g3 epts13.
Proof.
  intros.
  destruct INJ12 
    as [core_data12 match_core12 core_ord12 core_ord_wf12 
      match_sm_wd12 genvs_dom_eq12 match_genv12
      match_visible12 match_restrict12 
      match_sm_valid12 (*match_protected12*) core_initial12 
      core_diagram12 effcore_diagram12
      core_halted12 core_at_external12 eff_after_external12].  
  destruct EQ23 
    as [core_data23 match_core23 core_ord23 core_ord_wf23 
      match_se_wd23 genvs_dom_eq23 match_genv23
      match_visible23 match_restrict23
      match_se_valid23 (*match_protected23*) core_initial23 
      core_diagram23 effcore_diagram23
      core_halted23 core_at_external23 eff_after_external23].
  eapply SM_simulation.Build_SM_simulation_inject with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d mu c1 m1 c3 m3 => 
      match d with (d1,X,d2) => exists c2 mu12 mu23, X = Some c2 /\ 
        mu = compose_sm_se mu12 mu23 /\
        match_core12 d1 mu12 c1 m1 c2 m3 /\ match_core23 d2 mu23 c2 m3 c3 /\
        SM_SE_INV mu12 mu23
      end).
 (*well_founded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
{ (*wd*) clear - match_sm_wd12 match_se_wd23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  apply match_sm_wd12 in MC12.
  apply match_se_wd23 in MC23.
  destruct INV as [LOC [EXT [PUB FRG]]].
  split; intros; simpl in *.
    eapply MC12.
    eapply MC23.
    rewrite <- LOC.
      apply (local_DomRng _ MC12 _ _ _ H). 
    rewrite <- EXT.
      apply (extern_DomRng _ MC12 _ _ _ H). 
    destruct (pubSrcAx _ MC12 _ H) as [b2 [d [p t]]].
      apply PUB in t.
      exists b2, d. split; eassumption.
    destruct (frgnSrcAx _ MC12 _ H) as [b2 [d [p t]]].
      apply FRG in t.
      exists b2, d. split; eassumption.
    apply MC23; assumption. 
    apply MC23; assumption. }
{ (*genvs_domain_eq*) clear - genvs_dom_eq12 genvs_dom_eq23. 
  eapply genvs_domain_eq_trans; eassumption. }
{ (*match_genv*) clear - match_genv12.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct MC as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  simpl. eapply match_genv12. apply MC12. }
{ (*match_visible*) clear - match_visible12 match_visible23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  rewrite compose_sm_se_vis.
  eapply match_visible12; eassumption. }
{ (*match_restrict*) clear - match_restrict12 match_restrict23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  exists c2, (restrict_sm mu12 X), mu23.
  split. trivial. 
  split. apply compose_sm_se_restrict_sm. 
           (*?? unfold restrict_sm?? compose_sm_se. simpl in *.*)
  split. rewrite compose_sm_se_vis in H0. 
         eapply (match_restrict12 _ _ _ _ _ _ _ MC12 H0 H1).
  split. assumption.
  destruct INV as [LOC [EXT [PUB FRG]]].
    red. 
      rewrite restrict_sm_locBlocksTgt, restrict_sm_extBlocksTgt, 
              restrict_sm_pubBlocksTgt, restrict_sm_frgnBlocksTgt.
      intuition. }
{ (*match_validblocks*) 
  clear - match_sm_valid12 match_se_valid23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  split; simpl; intros.
    destruct (match_sm_valid12 _ _ _ _ _ _ MC12).
      eapply H0. apply H.
    apply (match_se_valid23 _ _ _ _ _ MC23 b2).
      apply H. }
{ (*initialcore*)
  clear - EPC genvs_dom_eq12 genvs_dom_eq23 core_initial12 core_initial23.
  intros. rename v2 into v3.
  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  rewrite <- (genvs_domain_eq_isGlobal _ _ genvs_dom_eq23) in H5.
  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ _ _ 
              H0 H1 H2 H3 H4 H5 H6 H7)
    as [cd12 [c2 [Ini2 MC12]]]; clear core_initial12.
  destruct (core_initial23 _ _ _ EP23 _ _ _ _ Ini2 H5 H7)
    as [cd23 [c3 [Ini3 MC23]]]; clear core_initial23.
  exists (cd12, Some c2, cd23), c3.
  split; trivial.
  exists c2; eexists; eexists; split; trivial.
  split. Focus 2. split. eassumption. split. eassumption.
    rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq12).
    split; auto.
  rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq23).
    unfold initial_SM, compose_sm_se; simpl.
    f_equal.  }
{ (*core_diagram*)
  clear - core_diagram12 match_sm_wd12 match_se_wd23 core_diagram23.
  eapply injeq_corediagram_trans; eassumption. }
{ (*effcore_diagram*)
  clear - effcore_diagram12 effcore_diagram23.
  eapply injeq_effcorediagram_trans; eassumption. }
{ (*halted*)
  clear - core_halted12 core_halted23.
  intros. rename c2 into c3.  
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  destruct (core_halted12 _ _ _ _ _ _ _ MC12 H0)
    as [v2 [Inj [Vinj Halted2]]].
  apply (core_halted23 _ _ _ _ _ _ MC23) in Halted2.
  rewrite compose_sm_se_as_inj, compose_sm_se_vis.
  exists v2; auto. }
(*version where args must be in VisEq mu
{ (*at_external*)
  clear - core_at_external12 core_at_external23.
  intros. rename c2 into c3.  
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 H0)
    as [Inj [vals2 [Vinj AtExt2]]].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2).
  rewrite compose_sm_se_as_inj, compose_sm_se_vis.
  split; trivial. 
  exists vals2; auto. }*)
{ (*at_external*)
  clear - core_at_external12 core_at_external23.
  intros. rename c2 into c3.  
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 H0)
    as [Inj [vals2 [Vinj AtExt2]]].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2)
    as [RCMid AtExtTgt].
  rewrite compose_sm_se_as_inj, compose_sm_se_vis.
  split; trivial. 
  exists vals2; auto. }
{ (*after_external*)
  clear - match_sm_wd12 match_se_wd23 core_at_external12 
          core_at_external23 eff_after_external12 eff_after_external23.
  intros. rename st2 into st3. rename vals2 into vals3.  
  destruct cd as [[d12 cc2] d23].
  destruct MatchMu as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]].
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExtSrc)
    as [Inj [vals2 [Vinj AtExt2]]].

  (*destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2)
    as [VisEq AtExt3].*)
  destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2)
    as [RCMid AtExt3].
  clear core_at_external12 core_at_external23.

  assert (e'= e /\ ef_sig' = ef_sig /\ vals2=vals3).
    rewrite AtExt3 in AtExtTgt. inv AtExtTgt.
    clear. intuition.
  destruct H0 as [? [? ?]]; subst e' ef_sig' vals2.
  clear AtExtTgt.
  subst mu. rewrite compose_sm_se_as_inj, compose_sm_se_vis in *.
  simpl in *.
  assert (LOCAL12: local_of mu12 = local_of nu'). subst. eapply INC.
  assert (EXPSRC12: exportedSrc (compose_sm_se mu12 mu23) vals1 =
           exportedSrc mu12 vals1).
    unfold exportedSrc; simpl.
    unfold compose_sm_se, sharedSrc, shared_of; extensionality b; simpl. 
      unfold foreign_of, pub_of; simpl. destruct mu12; simpl. reflexivity.
  rewrite EXPSRC12 in *.
  unfold exportedTgt, sharedTgt in pubTgtHyp. simpl in *.
  specialize (eff_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ 
       MemInjMu MC12 AtExtSrc AtExt2 Vinj _ (eq_refl _) _ (eq_refl _) _ (eq_refl _)).
  specialize (eff_after_external23 _ _ _ _ _ _ _ _ _ _ MC23 
       AtExt2 AtExt3 (*VisEq*) _ (eq_refl _) _ (eq_refl _)).
  remember (replace_locals mu12
                            (fun b : block =>
                             locBlocksSrc mu12 b &&
                             REACH m1 (exportedSrc mu12 vals1) b)
                            (fun b : block =>
                             locBlocksTgt mu12 b &&
                             REACH m2 (exportedTgt mu12 vals3) b)) as nu12.
  assert (extIncNu12: extern_incr nu12 (merge_LocExt nu12 nu')).
    subst. clear - INV INC.
    unfold merge_LocExt, as_inj, extern_incr; simpl.
           rewrite replace_locals_local, replace_locals_extern, 
           replace_locals_locBlocksSrc, replace_locals_locBlocksTgt, 
           replace_locals_extBlocksSrc, replace_locals_extBlocksTgt,
           replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt, 
           replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt.
           destruct INV as [InvA [InvB [InvC InvD]]]; simpl in *.
             split. eapply INC. split. trivial.
             split. eapply INC.
             split. intros. eapply INC. simpl. 
                    rewrite <- InvB. assumption.
             split; trivial. split; trivial. split; trivial. 
             split; trivial. split; trivial.
  assert (asInjNu12: as_inj (merge_LocExt nu12 nu') = as_inj nu').
    subst. clear - LOCAL12.
    unfold merge_LocExt, as_inj. simpl in *.
    rewrite replace_locals_local, LOCAL12.
    trivial.
  assert (sepNu12: sm_inject_separated nu12 (merge_LocExt nu12 nu') m1 m2).
    subst. clear - LOCAL12 INV INC SEP.
    destruct SEP as [SEPA [SEPB SEPC]]; simpl in *.
    destruct INV as [InvA [InvB [InvC InvD]]]; simpl in *.
    rewrite <- InvA, <- InvB, LOCAL12 in *.
    red; simpl. unfold merge_LocExt, as_inj. simpl.
    unfold DomSrc, DomTgt in *; simpl in *.
    rewrite replace_locals_local, replace_locals_extern,
           replace_locals_locBlocksSrc, replace_locals_locBlocksTgt, 
           replace_locals_extBlocksSrc, replace_locals_extBlocksTgt.
    unfold as_inj in *; simpl in *.
    rewrite LOCAL12.
    split. eapply SEPA; eassumption.
    split; intros. apply SEPB. assumption.
         destruct (locBlocksSrc mu12 b1); simpl in *. discriminate.
         rewrite H0. apply orb_true_r.
    apply SEPC. assumption.
         destruct (locBlocksTgt mu12 b2); simpl in *. discriminate.
         rewrite H0. apply orb_true_r. 
      
  assert (WDmerge: SM_wd (merge_LocExt nu12 nu')).
     clear eff_after_external12 UnchLOOR UnchPrivSrc eff_after_external23. 
     subst. unfold merge_LocExt; simpl.
     specialize (match_sm_wd12 _ _ _ _ _ _ MC12).
     specialize (match_se_wd23 _ _ _ _ _ MC23).
     destruct INV as [InvA [InvB [InvC InvD]]]; simpl in *.
     destruct INC as [I1 [I2 [I3 [I4 [I5 [I6 [I7 [I8 [I9 I10]]]]]]]]]; simpl in *.
     destruct extIncNu12 as [IN1 [IN2 [IN3 [IN4 [IN5 [IN6 [IN7 [IN8 [IN9 IN10]]]]]]]]]; simpl in *.
     clear sepNu12 asInjNu12.
       rewrite replace_locals_locBlocksSrc, replace_locals_locBlocksTgt, 
           replace_locals_extBlocksSrc, replace_locals_extBlocksTgt,
           replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt, 
           replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
           replace_locals_local in *.
     split; simpl.
       rewrite I5. eapply WDnu'.
       rewrite InvA, I6. eapply WDnu'.
       eapply match_sm_wd12.
       eapply WDnu'.
       intros b' LOC'. apply andb_true_iff in LOC'; destruct LOC' as [LOC' RCH']. 
         apply forall_vals_inject_restrictD in Vinj.
         destruct (REACH_local_REACH _ match_sm_wd12 _ _ _ _ Inj Vinj _ RCH' LOC')
           as [b2 [delta [LOC12 RCH2]]].
         exists b2, delta. rewrite LOC12.
           destruct (local_DomRng _ match_sm_wd12 _ _ _ LOC12).
           intuition.
     intros. destruct (frgnSrcAx _ match_sm_wd12 _  H) as [b2 [delta [FRG FT]]].
       exists b2, delta. rewrite (I1 _ _ _ FRG). split; trivial.
     intros. apply andb_true_iff in H; destruct H. trivial.
     intros. apply InvD in H. rewrite I10 in H.
       apply (frgnBlocksExternTgt _ WDnu' _ H).
  assert (ValidMerge: sm_valid (merge_LocExt nu12 nu') m1' m2').
    split; intros b2 Hb2; eapply SMvalNu'.
       subst. unfold DOM, DomSrc; unfold DOM, merge_LocExt, DomSrc in Hb2. simpl in *.
       assert (LOC: locBlocksSrc mu12 = locBlocksSrc nu') by eapply INC. 
       rewrite replace_locals_locBlocksSrc, LOC in Hb2. apply Hb2.
    subst. unfold RNG, DomTgt; unfold RNG, merge_LocExt, DomTgt in Hb2. simpl in *.
       rewrite replace_locals_locBlocksTgt in Hb2.
       remember (locBlocksTgt mu12 b2) as d.
       destruct d; simpl in *.
          apply eq_sym in Heqd.
          assert (LOC: locBlocks mu23 = locBlocksTgt nu') by eapply INC.
          rewrite <- LOC. apply orb_true_iff. left.
          destruct INV. rewrite <- H. trivial.
       rewrite Hb2. apply orb_true_r.
  specialize (eff_after_external12 (merge_LocExt nu12 nu') ret1 m1' ret2 m2'
              extIncNu12 sepNu12 WDmerge ValidMerge). 
  rewrite asInjNu12 in *.
  assert (RVal2Nu12: forall b, getBlocks (ret2 :: nil) b = true ->
                        RNG (merge_LocExt nu12 nu') b).
    assert (LT: locBlocks mu23 = locBlocksTgt nu').
      subst nu. eapply INC.
    assert (LT2: locBlocksTgt mu12 = locBlocks mu23) by eapply INV.
    clear - RVal2 LT LT2 Heqnu12.
    intros. specialize (RVal2 _ H).
    unfold RNG, DomTgt in *; simpl in *.
    rewrite <- LT, <- LT2 in RVal2. subst; simpl.
    rewrite replace_locals_locBlocksTgt. assumption.
  assert (RCMid': REACH_closed m2' (DomTgt (merge_LocExt nu12 nu'))).
    subst nu12; unfold merge_LocExt, DomTgt; simpl. rewrite replace_locals_locBlocksTgt.
    assert (locBlocksTgt nu=locBlocksTgt nu') by eapply INC.
    subst nu; simpl in *.
    assert (locBlocksTgt mu12 = locBlocks mu23) by eapply INV.
    rewrite H1, H0. apply RC2'.
  destruct (eff_after_external12 MemInjNu' RValInjNu' RVal2Nu12 RCMid' FwdSrc
            FwdTgt _ (eq_refl _)  _ (eq_refl _)  _ (eq_refl _)) 
    as [cd12' [st1' [st2' [AftExt1 [AftExt2 MC12']]]]]; clear eff_after_external12.
  (*first UnchOn side condition*)
     clear eff_after_external23; subst.
     rewrite replace_locals_locBlocksSrc, replace_locals_pubBlocksSrc.
     simpl in *. apply UnchPrivSrc.
  (*second UnchOn side condition*)
     clear eff_after_external23; subst. 
     eapply unchanged_on_validblock; try eassumption.
     unfold local_out_of_reach; simpl.
     rewrite replace_locals_locBlocksTgt, replace_locals_pubBlocksSrc, replace_locals_local.
     intros b2 ofs2 VB2 Hyp2. destruct Hyp2. split; trivial.
     destruct INV as [LOC _]. rewrite LOC in *. trivial.
  
  remember {| locBlocks := locBlocks mu23;
                         pubBlocks := fun b : block =>
                                      locBlocks mu23 b &&
                                      REACH m2
                                        (fun b' : block =>
                                         getBlocks vals3 b'
                                         || pubBlocks mu23 b'
                                         || frgnBlocks mu23 b') b;
                         extBlocks := extBlocks mu23;
                         frgnBlocks := frgnBlocks mu23 |} as nu23.
  remember (Build_SM_Equality (locBlocks mu23)
                      (fun b => locBlocks mu23 b &&
                                  REACH m2
                                        (fun b' => getBlocks vals3 b'
                                         || pubBlocks mu23 b'
                                         || frgnBlocks mu23 b') b)
                      (extBlocksTgt nu')
                      (frgnBlocks mu23)) as nu23'.
  assert (RCH123: forall b, getBlocks vals3 b || (frgnBlocksTgt mu12 b || pubBlocksTgt mu12 b) = true ->
                            getBlocks vals3 b || pubBlocks mu23 b || frgnBlocks mu23 b = true).
    intros b3 Hb3.
          destruct (getBlocks vals3 b3); simpl in *; trivial.
          rewrite orb_comm. 
          remember (frgnBlocksTgt mu12 b3) as q; apply eq_sym in Heqq.
          destruct INV as [InvA [InvB [InvC InvD]]]; simpl in *.
          destruct q; simpl in *; trivial.
            rewrite (InvD _ Heqq). trivial.
            rewrite (InvC _ Hb3). apply orb_true_r.
  assert (Inc23: eq_extern_incr nu23 nu23').
    red. subst nu23'; subst nu23; simpl in *.
    split. intros. eapply INC. subst nu; simpl. assumption.
    split. trivial.
    split; trivial.
  assert (Sep23: eq_inject_separated nu23 nu23' m2).
    red. subst nu23'; subst nu23; simpl in *.
    destruct Inc23 as [IA [IB [IC ID]]]; simpl in *.
    unfold Blocks; simpl. intros b3 Hb3 Hb3'. 
    eapply SEP. subst nu. unfold DomTgt; simpl. assumption. 
           unfold DomTgt. destruct (locBlocks mu23 b3); simpl in *. discriminate.
             rewrite Hb3'. apply orb_true_r.
  assert (WD23': SE_wd nu23').
    subst nu23'; simpl.
    split; simpl. 
       intros b3.
         destruct (disjoint_extern_local_Tgt _ WDnu' b3) as [LOC | EXT].
         assert (LB: locBlocksTgt nu = locBlocksTgt nu') by eapply INC.
         rewrite <- LB in LOC. subst nu; simpl in *. left; trivial.
         right; trivial.
    intros b3 Hb3. apply andb_true_iff in Hb3. destruct Hb3; trivial.
    intros. eapply INC. subst nu; simpl in *.
      eapply (match_se_wd23 _ _ _ _ _ MC23). assumption.
  assert (Valid23': se_valid nu23' m2').
    red. unfold Blocks;  subst nu23'; simpl in *; intros.
         eapply SMvalNu'. unfold RNG; simpl. 
            unfold DomTgt.
         assert (LOC: locBlocksTgt nu = locBlocksTgt nu') by eapply INC.
         rewrite <- LOC; clear LOC. subst nu; simpl. assumption.
(*  assert (Ret23': forall b, getBlocks (ret2 :: nil) b = true ->
                            Blocks nu23' b = true).
         simpl.
         intros. subst nu23'. unfold Blocks; simpl.
         clear eff_after_external23 UnchLOOR UnchPrivSrc Valid23'.
         rewrite <- asInjNu12 in RValInjNu'. clear - H0 RValInjNu'.
         apply getBlocks_char in H0. destruct H0. simpl in H. destruct H; try contradiction. subst.
         ?? (*TODO: maybe add corresponding assumption in inj_afterexternal?*)*)
  specialize (eff_after_external23 nu23'
                  ret2 m2' Inc23 Sep23 WD23' Valid23'). 
  assert (Ret23': forall b, getBlocks (ret2 :: nil) b = true ->
                            Blocks nu23' b = true).
    subst nu23'; unfold Blocks; simpl. 
    clear - INC RVal2 NuHyp.
    intros. specialize (RVal2 _ H). unfold RNG, DomTgt in *.
     subst.
     assert (locBlocks mu23 = locBlocksTgt nu') by eapply INC.
     rewrite H0; trivial. 
  assert (RC23': REACH_closed m2' (Blocks nu23')).
    subst nu23'. clear eff_after_external23.
    unfold Blocks; simpl. subst; simpl in *.
    assert (locBlocks mu23 = locBlocksTgt nu') by eapply INC.
    rewrite H. apply RC2'.
  destruct (eff_after_external23 Ret23' RC23' FwdTgt _ (eq_refl _) _ (eq_refl _))
    as [cd23' [st2'' [st3' [AftExt2' [AftExt3 MC23']]]]]; clear eff_after_external23.
    (*unchOn side condition*)
     subst. simpl in *.
     eapply unchanged_on_validblock; try eassumption.
     unfold local_out_of_reach; simpl. intros b2 z VB [LB RCH2F].
     rewrite LB in RCH2F. simpl in *.
     split. assumption.
     specialize (match_sm_wd12 _ _ _ _ _ _ MC12).
     intros b1 delta LOCb1. destruct (local_DomRng _ match_sm_wd12 _ _ _ LOCb1) as [Srcb1 Tgtb1].
     rewrite Srcb1; simpl.
     remember (REACH m1 (exportedSrc mu12 vals1) b1) as d.
     destruct d; apply eq_sym in Heqd.
         apply forall_vals_inject_restrictD in Vinj.
         destruct (REACH_local_REACH _ match_sm_wd12 _ _ _ _ Inj Vinj _ Heqd Srcb1)
           as [bb2 [ddelta [LOC12 RCH2T]]].
         rewrite LOC12 in LOCb1. inv LOCb1.
         assert (REACH m2 (fun b' =>
                  getBlocks vals3 b' || pubBlocks mu23 b' || frgnBlocks mu23 b') b2 = true).
          eapply REACH_mono; try eassumption.
          unfold exportedTgt, sharedTgt; intros. apply RCH123. assumption.
          rewrite H in RCH2F; discriminate.
     right; trivial.
  exists (cd12', Some st2'', cd23'), st1', st3'.
  split; trivial.
  split; trivial.
  exists st2'', (replace_externs (merge_LocExt nu12 nu')
             (fun b : block =>
              DomSrc (merge_LocExt nu12 nu') b &&
              (negb (locBlocksSrc (merge_LocExt nu12 nu') b) &&
               REACH m1' (exportedSrc (merge_LocExt nu12 nu') (ret1 :: nil))
                 b))
             (fun b : block =>
              DomTgt (merge_LocExt nu12 nu') b &&
              (negb (locBlocksTgt (merge_LocExt nu12 nu') b) &&
               REACH m2' (exportedTgt (merge_LocExt nu12 nu') (ret2 :: nil))
                 b))),
       {|
          locBlocks := locBlocks nu23';
          pubBlocks := pubBlocks nu23';
          extBlocks := extBlocks nu23';
          frgnBlocks := fun b : block =>
                        extBlocks nu23' b &&
                        REACH m2'
                          (fun b' : block =>
                           getBlocks (ret2 :: nil) b' || pubBlocks nu23' b'
                           || frgnBlocks nu23' b') b |}.
  split; trivial.
  rewrite AftExt2 in AftExt2'. inv AftExt2'.
  destruct INV as [InvA [InvB [InvC InvD]]]; simpl in *.
  split. clear UnchLOOR UnchPrivSrc ValidMerge WDmerge MC12' MC23'.
         unfold merge_LocExt, compose_sm_se in *; simpl in *.
         unfold replace_externs, DomSrc, DomTgt, exportedTgt, sharedTgt. simpl; simpl in *. 
         rewrite replace_locals_locBlocksSrc, replace_locals_locBlocksTgt,  
                replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt,
                replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
                replace_locals_local. simpl; simpl in *.
         destruct nu'; simpl in *.
         destruct INC as [IncA [IncB [IncC [IncD [IncE [IncF [IncG [IncH [IncI IncJ]]]]]]]]]; simpl in *.
         f_equal. intuition. intuition.
           subst pubBlocksSrc. trivial. 
           subst pubBlocksTgt. trivial. 
           extensionality b. f_equal. f_equal.
              extensionality b'. rewrite (orb_comm (frgnBlocks mu23 b')).
              apply orb_assoc.
         intuition.
         extensionality b. rewrite IncE, <- IncF.
           f_equal. f_equal. f_equal. rewrite <- IncG, <- IncH.
             rewrite IncE. rewrite IncF.
           unfold exportedSrc, sharedSrc, shared_of. simpl.
           extensionality b'. f_equal. rewrite IncI, IncB.
           reflexivity.
         extensionality b. 
           remember (locBlocksTgt b) as d; destruct d; simpl; trivial.
             assert (extBlocksTgt b = false).  
               eapply (locBlocksTgt_extBlocksTgt _ WDnu' b). simpl. rewrite <- Heqd; trivial.
             rewrite H; trivial.
           rewrite <- IncH. f_equal. f_equal. extensionality b'.
             rewrite <- orb_assoc. f_equal. rewrite orb_comm. f_equal. f_equal.
             f_equal. extensionality bb.
             rewrite (orb_comm (frgnBlocks mu23 bb)). apply orb_assoc.
          rewrite IncJ. trivial. 
  split; trivial.
  split; trivial.
  unfold  merge_LocExt in *. clear UnchLOOR UnchPrivSrc ValidMerge WDmerge.
  simpl in *. unfold DomSrc, DomTgt, exportedTgt, sharedTgt in *.
  rewrite replace_locals_locBlocksSrc, replace_locals_locBlocksTgt,  
                replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt,
                replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
                replace_locals_local in *. simpl in *.
  clear MC12' MC23'. simpl. simpl in *.
  split; simpl. assumption. 
    split; trivial. 
    split. rewrite InvA. intros.
           destruct (locBlocks mu23 b); simpl in *; try discriminate. 
           eapply REACH_mono; try eapply H. clear H. apply RCH123.
    intros. destruct (locBlocksTgt mu12 b); simpl in *; try discriminate.
            destruct (extBlocksTgt nu' b); simpl in *; try discriminate.
            eapply REACH_mono; try eapply H. clear H.
            simpl; intros.
            destruct (getBlocks (ret2 :: nil) b0); simpl in *; trivial.
            remember (frgnBlocksTgt mu12 b0) as q; destruct q; simpl in *.
              apply eq_sym in Heqq. rewrite (InvD _ Heqq). apply orb_true_r.
            apply orb_true_iff; left. rewrite InvA in *.
            destruct (locBlocks mu23 b0); simpl in *; try discriminate.
            eapply REACH_mono; try eapply H. clear H. apply RCH123.
}
Qed.
(*
Lemma EQ_INJ (EQ12 : SE_simulation_equality Sem1 Sem2 g1 g2 epts12)
             (INJ23 : SM_simulation.SM_simulation_inject Sem2 Sem3 g2 g3 epts23):
      SM_simulation.SM_simulation_inject Sem1 Sem3 g1 g3 epts13.
Proof.
  intros.
  destruct EQ12 
    as [core_data12 match_core12 core_ord12 core_ord_wf12 
      match_se_wd12 genvs_dom_eq12 match_genv12
      match_visible12 match_restrict12 
      match_se_valid12 (*match_protected12*) core_initial12 
      core_diagram12 effcore_diagram12
      core_halted12 core_at_external12 eff_after_external12].  
  destruct INJ23 
    as [core_data23 match_core23 core_ord23 core_ord_wf23 
      match_sm_wd23 genvs_dom_eq23 match_genv23
      match_visible23 match_restrict23
      match_sm_valid23 (*match_protected23*) core_initial23 
      core_diagram23 effcore_diagram23
      core_halted23 core_at_external23 eff_after_external23].
  eapply SM_simulation.Build_SM_simulation_inject with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d mu c1 m c3 m3 => 
      match d with (d1,X,d2) => exists c2 mu12 mu23, X = Some c2 /\ 
        mu = compose_se_sm mu12 mu23 /\
        match_core12 d1 mu12 c1 m c2 /\ match_core23 d2 mu23 c2 m c3 m3 /\
        SE_SM_INV mu12 mu23
      end).
 (*well_founded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
{ (*wd*) clear - match_se_wd12 match_sm_wd23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  apply match_se_wd12 in MC12.
  apply match_sm_wd23 in MC23.
  destruct INV as [LOC [EXT [PUB FRG]]].
  split; intros; simpl. eapply MC12. eapply MC23.
    rewrite LOC. eapply MC23.  apply H. 
    rewrite EXT. eapply MC23.  apply H.
    assert (pubBlocksSrc mu23 b1 = true).
      apply PUB. apply H.
      destruct (pubSrcAx _ MC23 _ H0) as [b2 [d [p t]]].
      exists b2, d. split; eassumption.
    assert (frgnBlocksSrc mu23 b1 = true).
      apply FRG. apply H.
      destruct (frgnSrcAx _ MC23 _ H0) as [b2 [d [p t]]].
      exists b2, d. split; eassumption.
    eapply pubBlocksLocalTgt; eassumption.
    eapply frgnBlocksExternTgt; eassumption. }
{ (*genvs_domain_eq*) clear - genvs_dom_eq12 genvs_dom_eq23. 
  eapply genvs_domain_eq_trans; eassumption. }
{ (*match_genv*) clear -  genvs_dom_eq12 genvs_dom_eq23 match_genv12 match_genv23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct MC as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  destruct (match_genv23 _ _ _ _ _ _ MC23).
  split. apply meminj_preserves_genv2blocks. apply meminj_preserves_genv2blocks in H.
         apply (genvs_domain_eq_preserves _ _ _ genvs_dom_eq12).
         apply H.
  intros. apply (match_genv12 _ _ _ _ _ MC12 _ H1). }
{ (*match_visible*) clear - match_visible12 match_visible23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  eapply match_visible12; eassumption. }
{ (*match_restrict*) clear - match_restrict12 match_restrict23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  exists c2, (restrict_se mu12 X), mu23.
  split. trivial. 
  split. admit. ok is in comment
  split. eapply (match_restrict12 _ _ _ _ _ _ MC12).
           intros. eapply H0. apply H. apply H1.
  split. assumption.
  destruct INV as [LOC [EXT [PUB FRG]]].
    split; intros; simpl.
      extensionality b. rewrite <- LOC.
      remember (locBlocks mu12 b) as d.
      destruct d; trivial. apply eq_sym in Heqd.
        rewrite H0; trivial. unfold vis.
        apply orb_true_iff; left; apply Heqd.
    split. 
      extensionality b. rewrite <- EXT.
      remember (extBlocks mu12 b) as d.
      destruct d; trivial. apply eq_sym in Heqd. simpl.
        unfold compose_se_sm, vis in H0; simpl in H0.
      admit. ok - is in comment (*def of restrict_se wrong?*)
    split. intros. apply andb_true_iff in H; destruct H.
       apply (PUB _ H).
    intros. apply andb_true_iff in H; destruct H.
       apply (FRG _ H). }
{ (*match_validblocks*) 
  clear - match_se_valid12 match_sm_valid23.
  intros. destruct d as [[d1 st2] d2]. rename c2 into c3.
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  split; simpl; intros.
    eapply match_se_valid12; try eassumption.
    eapply match_sm_valid23; try eassumption.  }
{ (*initialcore*)
  clear - EPC genvs_dom_eq12 genvs_dom_eq23 core_initial12 core_initial23.
  intros. rename v2 into v3.
  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  assert (RCH: forall b,  
         REACH m1 (fun b' : block => isGlobalBlock g1 b' || getBlocks vals1 b') b =
         true -> DomS b = true).
    intros.
    assert (MP: forall b0 : block, isGlobalBlock g1 b0 || getBlocks vals1 b0 = true ->
                exists jb d, j b0 = Some (jb, d) /\ 
               isGlobalBlock g3 jb || getBlocks vals2 jb = true).
      intros. apply orb_true_iff in H8.
      destruct H8. exists b0, 0.
        split. eapply meminj_preserves_globals_isGlobalBlock; eassumption.
        rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq12) in H8.
        rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq23) in H8.
        rewrite H8; trivial.
      destruct (getBlocks_inject _ _ _ H2 _ H8) as [bb [d [J GB]]].
        exists bb, d; rewrite J, GB; intuition. 
    destruct (REACH_inject _ _ _ H1 _
        (fun b' : block => isGlobalBlock g3 b' || getBlocks vals2 b')
        MP _ H) as [b2 [d [J RCH2]]].
    eapply (H4 _ _ _ J).
  destruct (core_initial12 _ _ _ EP12 _ _ m1 DomS H0 RCH H6)
    as [cd12 [c2 [Ini2 MC12]]].
  apply meminj_preserves_genv2blocks in H3.
  apply (genvs_domain_eq_preserves _ _ _ genvs_dom_eq12) in H3.
  apply meminj_preserves_genv2blocks in H3.
  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _ _ _
            Ini2 H1 H2 H3 H4 H5 H6 H7)
    as [cd23 [c3 [Ini3 MC23]]].
(*  rewrite <- (genvs_domain_eq_isGlobal _ _ genvs_dom_eq12) in MC23.*)
  exists (cd12,Some c2, cd23), c3.
  split; trivial.
  exists c2; eexists; eexists; split; trivial.
  split. Focus 2. split. eassumption. split. eassumption.
    rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq12).
    split; auto.
  split; simpl. }
{ (*core_diagram*)
  clear - core_diagram12 match_sm_wd23 core_diagram23.
  assert (CD23: forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
  corestep Sem2 g2 st1 m1 st1' m1' ->
  forall (cd : core_data23) (st2 : C3) (mu : SM_Injection) (m2 : mem),
  match_core23 cd mu st1 m1 st2 m2 ->
  exists (st2' : C3) (m2' : mem) (cd' : core_data23) (mu' : SM_Injection),
    intern_incr mu mu' /\
    sm_inject_separated mu mu' m1 m2 /\
    sm_locally_allocated mu mu' m1 m2 m1' m2' /\
    match_core23 cd' mu' st1' m1' st2' m2' /\
    (corestep_plus Sem3 g3 st2 m2 st2' m2' \/
     corestep_star Sem3 g3 st2 m2 st2' m2' /\ core_ord23 cd' cd)).
    intros. destruct (core_diagram23 _ _ _ _ H _ _ _ _ H0)
              as [c2' [m2' [cd23' [mu23' [IntInc [InjSep [LocAlloc [MC ZZ]]]]]]]].
      exists c2', m2', cd23', mu23'.
      split; trivial. split; trivial. 
      split; trivial. split; trivial. 
  specialize (eqinj_corediagram_trans _ _ _ core_diagram12
    _ _  match_sm_wd23 _ CD23); 
  clear core_diagram12 core_diagram23 CD23. intros XX. 
  intros. rename st2 into c3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23].
  destruct H0 as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  specialize (XX _ _ _ _ H (d12, Some c2, d23) c3 mu12 mu23 m3). 
  destruct XX as [st3' [m3' [cd' [mu12' [mu23' [ZZa [ZZb [ZZc [ZZd [ZZe ZZf]]]]]]]]]].
    exists c2. auto.
  exists st3', m3', cd', (compose_se_sm mu12' mu23').
  split; trivial. 
  split; trivial. 
  split; trivial.
  split. destruct cd' as [[d12' cc2'] d23']. 
         destruct ZZd as [c2' [? [MCa MCb]]].
         exists c2', mu12', mu23'. clear ZZe. intuition.
  assumption. }
{ (*effcore_diagram*)
  (*
  eapply eqeq_effcorediagram_trans; eassumption.*)
  clear - effcore_diagram12 match_sm_wd23 match_sm_valid23 effcore_diagram23.
  intros. rename st2 into c3. rename m2 into m3.
  specialize (eqinj_effcorediagram_trans _ _ _  effcore_diagram12
       _ _ match_sm_wd23 match_sm_valid23 _ effcore_diagram23
       _ _ _ _ _ H cd c3).   
  destruct cd as [[d12 cc2] d23].
  destruct H0 as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  intros XX.
  destruct (XX mu12 mu23 m3) as
    [st3' [m3' [cd' [mu12' [mu23' [ZZa [ZZb [ZZc [ZZd [U3 [ZZe [ZZf ZZg]]]]]]]]]]]].
    clear XX. exists c2; auto.
    assumption.
  exists st3', m3', cd', (compose_se_sm mu12' mu23').
  split; trivial. 
  split; trivial. 
  split; trivial.
  split. destruct cd' as [[d12' cc2'] d23']. 
         destruct ZZd as [c2' [? [MCa MCb]]].
         exists c2', mu12', mu23'. clear ZZe. intuition.
  exists U3. split; assumption. }
{ (*halted*)
  clear - core_halted12 core_halted23.
  intros. rename c2 into c3.  
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  specialize (core_halted12 _ _ _ _ _ _ MC12 H0).
  destruct (core_halted23 _ _ _ _ _ _ _ MC23 core_halted12)
      as [v3 [INJ [ValInj Halted3]]].
  exists v3. rewrite compose_se_sm_as_inj. intuition.
     unfold vis. simpl. unfold vis in ValInj.
     destruct INV as [LOC [EXT [PUB FRG]]].
     rewrite LOC.
     eapply val_inject_incr; try eassumption.
     red; intros. destruct (restrictD_Some _ _ _ _ _ H).
       apply restrictI_Some; try eassumption.
       apply orb_true_iff in H2; destruct H2.
       rewrite H2; trivial.
   admit.ok is in comment (*mistake in compose_se_sm or restrict_se*) }
(*at_external*)
{ clear - core_at_external12 core_at_external23.
  intros. rename c2 into c3.
  rename H0 into AtExtSrc. 
  destruct cd as [[d12 cc2] d23]. 
  destruct H as [c2 [mu12 [mu23 [? [MU [MC12 [MC23 INV]]]]]]]; subst.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 AtExtSrc)
    as [ArgsVis12 AtExt2]; clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2)
    as [Minj [vals3 [AtExtTgt ZZ]]]; clear core_at_external23.
  rewrite compose_se_sm_as_inj.
  split; trivial.
  exists vals3. split; trivial. admit. admit is in comment (*same as in halted*) }
(*after_external*)
{ clear - core_at_external12 core_at_external23
          eff_after_external12 eff_after_external23. 
  intros. rename st2 into st3. 
  destruct cd as [[d12 cc2] d23].
  destruct MatchMu as [st2 [mu12 [mu23 [? [X [MC12 [MC23 INV]]]]]]]; subst cc2; subst mu.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 AtExtSrc)
    as [ArgsVis12 AtExt2]; clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2)
    as [Minj23 [vals3 [ArgsVis23 AtExtTgt']]]; clear core_at_external23.
  assert (e' = e /\ ef_sig'=ef_sig /\ vals2=vals3).
    rewrite AtExtTgt in AtExtTgt'. inv AtExtTgt'.
    split; trivial. split; trivial.
  destruct H as [He [Hefsig Hvals]]. subst e'; subst ef_sig'; subst vals2. clear AtExtTgt'.
  assert (PHS: pubSrc' = (fun b => locBlocks mu12 b &&
   REACH m1
     (fun b' : block =>
      getBlocks vals1 b' || pubBlocks mu12 b' || frgnBlocks mu12 b') b)).
    subst pubSrc'. extensionality b. simpl.
    assert (exportedSrc (compose_se_sm mu12 mu23) vals1 = 
            fun b' => getBlocks vals1 b' || pubBlocks mu12 b' || frgnBlocks mu12 b').
      unfold exportedSrc; simpl. extensionality bb. 
       rewrite sharedSrc_iff_frgnpub. simpl. rewrite (orb_comm (frgnBlocks mu12 bb)).
              rewrite orb_assoc. trivial.
        admit. (*admit is ok - in comment*)
    rewrite H. trivial.
  clear pubSrcHyp.
  specialize (eff_after_external12 _ _ _ _ _ _ _ _ _ _ MC12 AtExtSrc AtExt2
       ArgsVis12 _ PHS _ NuHyp _ _ _ INC SEP WDnu' SMvalNu'). RValNu'
       FwdSrc _ frgnSrcHyp _ Mu'Hyp UnchPrivSrc) 
   as [cd12 [st1' [c2' [AftExt1 [AftExt2 MC12']]]]]; clear eff_after_external12.
  destruct (eff_after_external23 _ _ _ _ _ _ _ _ _ _ MC23 AtExt2 AtExtTgt
       ValsVis _ pubBlksHyp _ NuHyp _ _ _ INC SEP WDnu' SMvalNu' RValNu'
       Fwd _ frgnBlksHyp _ Mu'Hyp UnchPriv)
   as [cd23 [st2' [st3' [AftExt2' [AftExt3 MC23']]]]]; clear eff_after_external23.
  assert (c2' = st2').
    rewrite AftExt2 in AftExt2'. inv AftExt2'. trivial.
  subst c2'.
  exists (cd12, Some st2', cd23), st1', st3'.
  split; trivial.
  split; trivial.
  exists st2'. split; trivial. split; trivial. }
Qed.
*)
(*dont need this
Theorem effect_simulations_tr: forall 
        (SIM12: @SIMULATION.effect_sim _ _ _ _ _ _ Sem1 Sem2 g1 g2 epts12)
        (SIM23: @SIMULATION.effect_sim _ _ _ _ _ _ Sem2 Sem3 g2 g3 epts23),
        @SIMULATION.effect_sim _ _ _ _ _ _ Sem1 Sem3 g1 g3 epts13.
Proof.
  intros.
  induction SIM12 as [EQ12 | INJ12].
  induction SIM23 as [EQ23 | INJ23].
*)
End EFFECT_SIM_TRANS.
End TRANS. 


Section Eff_EQ_SIMU_DIAGRAMS.
  Context {F1 V1 C1 F2 V2 C2:Type}
          {Sem1 : @EffectSem (Genv.t F1 V1) C1} 
          {Sem2 : @EffectSem (Genv.t F2 V2) C2}

          {ge1: Genv.t F1 V1} 
          {ge2: Genv.t F2 V2} 
          {entry_points : list (val * val * signature)}. 

  Let core_data := C1.

  Variable match_states : core_data -> SM_Equality -> C1 -> mem -> C2 -> Prop.
    
   Hypothesis match_se_wd: forall d mu c1 m c2, 
          match_states d mu c1 m c2 ->
          SE_wd mu.
    
   Hypothesis genvs_dom_eq: genvs_domain_eq ge1 ge2.
    
   Hypothesis match_genv: forall d mu c1 m c2
          (MC:match_states d mu c1 m c2),
          (*meminj_preserves_globals ge1 (extern_of mu) /\*)
          (forall b, isGlobalBlock ge1 b = true -> frgnBlocks mu b = true).

    Hypothesis match_visible: forall d mu c1 m c2, 
          match_states d mu c1 m c2 -> 
          REACH_closed m (visEq mu).

    Hypothesis match_restrict: forall d mu c1 m c2 X, 
          match_states d mu c1 m c2 -> 
          (forall b, visEq mu b = true -> X b = true) ->
          REACH_closed m X ->
          match_states d (restrict_se mu X) c1 m c2.

    Hypothesis match_validblocks: forall d mu c1 m c2, 
          match_states d mu c1 m c2 ->
          se_valid mu m.

    Hypothesis core_initial : forall v1 v2 sig,
       In (v1,v2,sig) entry_points -> 
       forall vals c1 m Blks,
          initial_core Sem1 ge1 v1 vals = Some c1 ->
          (*meminj_preserves_globals ge1 j ->*)

        (*the next condition is required to guarantee initialSE_wd*)
         (forall b, REACH m (fun b' => isGlobalBlock ge1 b' || getBlocks vals b') b = true ->
                    Blks b = true) ->

        (*the next condition ensures the initialSM satisfies se_valid*)
         (forall b, Blks b = true -> Mem.valid_block m b) ->

       exists c2, 
            initial_core Sem2 ge2 v2 vals = Some c2 /\
            match_states c1 (Build_SM_Equality 
                              (fun b => false)
                              (fun b => false)
                              Blks
                              (REACH m (fun b' => isGlobalBlock ge1 b' || getBlocks vals b')))
                           c1 m c2.

    Hypothesis core_halted : forall cd mu c1 m c2 v,
      match_states cd mu c1 m c2 ->
      halted Sem1 c1 = Some v ->
      halted Sem2 c2 = Some v.

    Hypothesis core_at_external : 
      forall cd mu c1 m c2 e vals ef_sig,
        match_states cd mu c1 m c2 ->
        at_external Sem1 c1 = Some (e,ef_sig,vals) ->
        (REACH_closed m (Blocks mu) /\ 
         at_external Sem2 c2 = Some (e,ef_sig,vals)). (*
        ((forall b, getBlocks vals b = true -> visEq mu b = true)
         /\ at_external Sem2 c2 = Some (e,ef_sig,vals)).*)

    Hypothesis eff_after_external: 
      forall cd mu st1 st2 m e vals ef_sig e' ef_sig'
        (*standard assumptions:*)
        (MatchMu: match_states cd mu st1 m st2)
        (AtExtSrc: at_external Sem1 st1 = Some (e,ef_sig,vals))
        (AtExtTgt: at_external Sem2 st2 = Some (e',ef_sig',vals)) 

   (*     (ValsVis: forall b, getBlocks vals b = true -> visEq mu b = true)*)

        pubBlks' (pubBlksHyp: pubBlks' = fun b => 
                       (locBlocks mu b) &&
                       (REACH m (fun b' => (getBlocks vals b') || (pubBlocks mu b') || (frgnBlocks mu b')) b))

        nu (NuHyp: nu = Build_SM_Equality (locBlocks mu) pubBlks'
                                          (extBlocks mu) (frgnBlocks mu)),

      forall nu' ret m'
        (INC: eq_extern_incr nu nu')  
        (SEP: eq_inject_separated nu nu' m)

        (WDnu': SE_wd nu') (SMvalNu': se_valid nu' m')

        (RValNu': forall b, getBlocks (ret::nil) b = true -> Blocks nu' b = true)

        (*the minimal assumption corresponding to Mem.inject (as_inj nu') m1' m2')*)
        (RC': REACH_closed m' (Blocks nu'))

        (Fwd: mem_forward m m')

        frgnBlks' (frgnBlksHyp: frgnBlks' = fun b => 
                     (extBlocks nu' b) &&
                     (REACH m' (fun b' => (getBlocks (ret::nil) b') || (pubBlocks nu' b') || (frgnBlocks nu' b')) b))

        mu' (Mu'Hyp: mu' = Build_SM_Equality (locBlocks nu') (pubBlocks nu')
                                             (extBlocks nu') frgnBlks')
 
         (UnchPriv: Mem.unchanged_on (fun b ofs => locBlocks nu b = true /\ 
                                                      pubBlocks nu b = false) m m'),
        exists st1', exists st2',
          after_external Sem1 (Some ret) st1 = Some st1' /\
          after_external Sem2 (Some ret) st2 = Some st2' /\
          match_states st1' mu' st1' m' st2'.
   
Section EFF_EQ_SIMULATION_STAR_WF.
Variable order: C1 -> C1 -> Prop.
Hypothesis order_wf: well_founded order.

    Hypothesis core_diagram : 
      forall st1 m st1' m', 
        corestep Sem1 ge1 st1 m st1' m' ->
      forall st2 mu,
        match_states st1 mu st1 m st2 ->
        exists st2', exists mu',
          eq_intern_incr mu mu' /\
          eq_inject_separated mu mu' m /\

          (*new condition: corestep evolution is soundly and completely 
                           tracked by the local knowledge*)
          eq_locally_allocated mu mu' m m' /\
 
          match_states st1' mu' st1' m' st2' /\
          ((corestep_plus Sem2 ge2 st2 m st2' m') \/
            corestep_star Sem2 ge2 st2 m st2' m' /\
            order st1' st1).

    Hypothesis effcore_diagram : 
      forall st1 m st1' m' U1, 
        effstep Sem1 ge1 U1 st1 m st1' m' ->

      forall st2 mu
        (UHyp: forall b1 z, U1 b1 z = true -> visEq mu b1 = true),
        match_states st1 mu st1 m st2 ->
        exists st2', exists mu',
          eq_intern_incr mu mu' /\
          eq_inject_separated mu mu' m /\
          eq_locally_allocated mu mu' m m' /\ 
          match_states st1' mu' st1' m' st2' /\

          exists U2,              
            ((effstep_plus Sem2 ge2 U2 st2 m st2' m' \/
              (effstep_star Sem2 ge2 U2 st2 m st2' m' /\
               order st1' st1)) /\

             forall b ofs, U2 b ofs = true -> 
                       (visEq mu b = true /\
                         (locBlocks mu b = false ->
                           (frgnBlocks mu b = true /\ 
                            U1 b ofs = true /\ 
                            Mem.perm m b ofs Max Nonempty)))).

Lemma eq_simulation_star_wf: 
  SE_simulation.SE_simulation_equality Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply SE_simulation.Build_SE_simulation_equality with
    (core_ord := order)
    (match_state := fun d j c1 m1 c2 => d = c1 /\ match_states d j c1 m1 c2).
  apply order_wf.
clear - match_se_wd. intros. destruct H; subst. eauto.
assumption.
clear - match_genv. intros. destruct MC; subst. eauto.
clear - match_visible. intros. destruct H; subst. eauto.
clear - match_restrict. intros. destruct H; subst. eauto.
clear - match_validblocks. intros.
    destruct H; subst. eauto.
clear - core_initial. intros.
  destruct (core_initial _ _ _ H _ _ _ _ H0 H1 H2)
    as [c2 [INI MS]]; clear core_initial.
  exists c1, c2. intuition. 
clear - core_diagram.
  intros. destruct H0; subst.
  destruct (core_diagram _ _ _ _ H _ _ H1) as 
    [c2' [mu' [INC [SEP [LAC [MC' Step]]]]]].
  exists c2'. exists st1'. exists mu'. intuition.
clear - effcore_diagram. 
  intros. destruct H0; subst.
  destruct (effcore_diagram _ _ _ _ _ H _ _ UHyp H1) as 
    [c2' [mu' [INC [SEP [LAC [MC' XX]]]]]]. 
  exists c2'. exists st1'. exists mu'. intuition.
clear - core_halted. intros. destruct H; subst.
  apply(core_halted _ _ _ _ _ _ H1 H0).
clear - core_at_external. intros. destruct H; subst.
  apply (core_at_external _ _ _ _ _ _ _ _ H1 H0).
clear - eff_after_external. intros. 
  destruct MatchMu as [ZZ matchMu]. subst cd.
  destruct (eff_after_external _ _ _ _ _ _ _ _ _ _ 
      matchMu AtExtSrc AtExtTgt (*ValsVis*) _ pubBlksHyp 
      _ NuHyp _ _ _ INC SEP WDnu' SMvalNu' RValNu' RC' Fwd 
      _ frgnBlksHyp _ Mu'Hyp UnchPriv)
    as [st1' [st2' [AftExt1 [AftExt2 MS']]]].
  exists st1', st1', st2'. intuition.
Qed.

End EFF_EQ_SIMULATION_STAR_WF.

Section EFF_EQ_SIMULATION_STAR.
  Variable measure: C1 -> nat.
  
    Hypothesis core_diagram : 
      forall st1 m st1' m', 
        corestep Sem1 ge1 st1 m st1' m' ->
      forall st2 mu,
        match_states st1 mu st1 m st2 ->
        exists st2', exists mu',
          eq_intern_incr mu mu' /\
          eq_inject_separated mu mu' m /\

          (*new condition: corestep evolution is soundly and completely 
                           tracked by the local knowledge*)
          eq_locally_allocated mu mu' m m' /\
 
          match_states st1' mu' st1' m' st2' /\
          ((corestep_plus Sem2 ge2 st2 m st2' m') \/
            ((measure st1' < measure st1)%nat /\ corestep_star Sem2 ge2 st2 m st2' m')).

    Hypothesis effcore_diagram : 
      forall st1 m st1' m' U1, 
        effstep Sem1 ge1 U1 st1 m st1' m' ->

      forall st2 mu
        (UHyp: forall b1 z, U1 b1 z = true -> visEq mu b1 = true),
        match_states st1 mu st1 m st2 ->
        exists st2', exists mu',
          eq_intern_incr mu mu' /\
          eq_inject_separated mu mu' m /\
          eq_locally_allocated mu mu' m m' /\ 
          match_states st1' mu' st1' m' st2' /\

          exists U2,      
            ((effstep_plus Sem2 ge2 U2 st2 m st2' m' \/
             ((measure st1' < measure st1)%nat /\ effstep_star Sem2 ge2 U2 st2 m st2' m')) /\
             forall b ofs, U2 b ofs = true -> 
                       (visEq mu b = true /\
                         (locBlocks mu b = false ->
                           (frgnBlocks mu b = true /\ 
                            U1 b ofs = true /\ 
                            Mem.perm m b ofs Max Nonempty)))).

Lemma eq_simulation_star: 
  SE_simulation.SE_simulation_equality Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply eq_simulation_star_wf.
  apply  (well_founded_ltof _ measure).
clear - core_diagram. intros.
  destruct (core_diagram _ _ _ _ H _ _ H0) 
    as [c2' [mu' [INC [SEP [LAC [MC' STEP]]]]]]. 
  exists c2', mu'. intuition.
clear - effcore_diagram. intros.
  destruct (effcore_diagram _ _ _ _ _ H _ _ UHyp H0) 
    as [c2' [mu' [INC [SEP [LAC [MC' [U2 XX]]]]]]].
  exists c2', mu'. intuition.
  exists U2. intuition.
  exists U2. intuition.
Qed.

End EFF_EQ_SIMULATION_STAR.

Section EFF_EQ_SIMULATION_PLUS.
  Variable measure: C1 -> nat.
 
    Hypothesis core_diagram : 
      forall st1 m st1' m', 
        corestep Sem1 ge1 st1 m st1' m' ->
      forall st2 mu,
        match_states st1 mu st1 m st2 ->
        exists st2', exists mu',
          eq_intern_incr mu mu' /\
          eq_inject_separated mu mu' m /\

          (*new condition: corestep evolution is soundly and completely 
                           tracked by the local knowledge*)
          eq_locally_allocated mu mu' m m' /\
 
          match_states st1' mu' st1' m' st2' /\
          ((corestep_plus Sem2 ge2 st2 m st2' m') \/
            ((measure st1' < measure st1)%nat /\ corestep_star Sem2 ge2 st2 m st2' m')).

    Hypothesis effcore_diagram : 
      forall st1 m st1' m' U1, 
        effstep Sem1 ge1 U1 st1 m st1' m' ->

      forall st2 mu
        (UHyp: forall b1 z, U1 b1 z = true -> visEq mu b1 = true),
        match_states st1 mu st1 m st2 ->
        exists st2', exists mu',
          eq_intern_incr mu mu' /\
          eq_inject_separated mu mu' m /\
          eq_locally_allocated mu mu' m m' /\ 
          match_states st1' mu' st1' m' st2' /\

          exists U2,      
            ((effstep_plus Sem2 ge2 U2 st2 m st2' m' \/
             ((measure st1' < measure st1)%nat /\ effstep_star Sem2 ge2 U2 st2 m st2' m')) /\
             forall b ofs, U2 b ofs = true -> 
                       (visEq mu b = true /\
                         (locBlocks mu b = false ->
                           (frgnBlocks mu b = true /\ 
                            U1 b ofs = true /\ 
                            Mem.perm m b ofs Max Nonempty)))).

Lemma eq_simulation_plus: 
  SE_simulation.SE_simulation_equality Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  apply eq_simulation_star with (measure:=measure).
clear - core_diagram. intros.
  destruct (core_diagram _ _ _ _ H _ _ H0) 
    as [c2' [mu' [INC [SEP [LAC [MC' STEP]]]]]]. 
  exists c2', mu'.
  intuition.
clear - effcore_diagram. intros.
  destruct (effcore_diagram _ _ _ _ _ H _ _ UHyp H0) 
    as [c2' [mu' [INC [SEP [LAC [MC' [U2 XX]]]]]]].
  exists c2', mu'. intuition.
  exists U2. intuition.
  exists U2. intuition.
Qed.

End EFF_EQ_SIMULATION_PLUS.

End Eff_EQ_SIMU_DIAGRAMS.