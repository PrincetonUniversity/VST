(*CompCert imports*)
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import msl.Axioms.
Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.trace_semantics.
Require Import sepcomp.StructuredInjections.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.effect_properties.
Require Import sepcomp.extspec.

Import SM_simulation.

(** * Safety and semantics preservation *)

Section safety.
Context { G C D : Type }
        (Hcore : CoopCoreSem G C)
        (ge : G).

Fixpoint safeN (n:nat) (c:C) (m:mem) : Prop :=
  match n with
    | O => True
    | S n' => 
      match halted Hcore c with
        | None => 
          exists c', exists m',
            corestep Hcore ge c m c' m' /\
            safeN n' c' m'
        | Some i => True
      end
  end.

Definition corestep_fun  :=
  forall ge m q m1 q1 m2 q2 ,
    corestep Hcore ge q m q1 m1 -> 
    corestep Hcore ge q m q2 m2 -> 
    (q1, m1) = (q2, m2).

Lemma safe_downward1 :
  forall n c m,
    safeN (S n) c m -> safeN n c m.
Proof.
  induction n; simpl; intros; auto.
  destruct (halted Hcore c); auto.
  destruct H as [c' [m' [? ?]]].
  exists c', m'; split; auto.
Qed.

Lemma safe_downward : 
  forall (n n' : nat) c m,
    le n' n ->
    safeN n c m -> safeN n' c m.
Proof.
  do 6 intro. revert c m H0. induction H; auto.
  intros. apply IHle. apply safe_downward1. auto.
Qed.

Lemma safe_corestep_forward:
  corestep_fun -> 
  forall c m c' m' n,
    corestep Hcore ge c m c' m' -> safeN (S n) c m -> safeN n c' m'.
Proof.
  simpl; intros.
  erewrite corestep_not_halted in H1; eauto.
  destruct H1 as [c'' [m'' [? ?]]].
  assert ((c',m') = (c'',m'')).
  eapply H; eauto.
  inv H3; auto.
Qed.

Lemma safe_corestepN_forward:
  corestep_fun -> 
  forall c m c' m' n n0,
    corestepN Hcore ge n0 c m c' m' -> safeN (n + S n0) c m -> safeN n c' m'.
Proof.
  intros.
  revert c m c' m' n H0 H1.
  induction n0; intros; auto.
  simpl in H0; inv H0.
  eapply safe_downward in H1; eauto. omega.
  simpl in H0. destruct H0 as [c2 [m2 [STEP STEPN]]].
  apply (IHn0 _ _ _ _ n STEPN). 
  assert (Heq: (n + S (S n0) = S (n + S n0))%nat) by omega.
  rewrite Heq in H1.
  eapply safe_corestep_forward in H1; eauto.
Qed.

Lemma safe_corestep_backward:
  forall c m c' m' n,
    corestep Hcore ge c m c' m' -> safeN (n - 1) c' m' -> safeN n c m.
Proof.
  simpl; intros.
  induction n; simpl; auto.
  erewrite corestep_not_halted; eauto.
  exists c', m'; split; auto.
  assert (Heq: (n = S n - 1)%nat) by omega.
  rewrite Heq; auto.
Qed.

Lemma safe_corestepN_backward:
  forall c m c' m' n n0,
    corestepN Hcore ge n0 c m c' m' -> safeN (n - n0) c' m' -> safeN n c m.
Proof.
  simpl; intros.
  revert c m c' m' n H H0.
  induction n0; intros; auto.
  simpl in H; inv H.
  solve[assert (Heq: (n = n - 0)%nat) by omega; rewrite Heq; auto].
  simpl in H. destruct H as [c2 [m2 [STEP STEPN]]].
  assert (H: safeN (n - 1 - n0) c' m'). 
  eapply safe_downward in H0; eauto. omega.
  specialize (IHn0 _ _ _ _ (n - 1)%nat STEPN H). 
  eapply safe_corestep_backward; eauto.
Qed.

End safety.

Definition target_accessible mu m tm args b ofs :=
  Mem.valid_block tm b /\ 
  (locBlocksTgt mu b=false -> 
    exists b0 d, 
      foreign_of mu b0 = Some (b, d) 
      /\ REACH m (getBlocks args) b0=true 
      /\ Mem.perm m b0 (ofs-d) Max Nonempty).

Section semantics_preservation.
Context  {F V TF TV C D Z : Type}
         {source : @EffectSem (Genv.t F V) C}
         {target : @EffectSem (Genv.t TF TV) D}
         {geS : Genv.t F V}
         {geT : Genv.t TF TV}
         {entry_points : list (val*val*signature)}

  (z_init : Z)

  (spec : ext_spec Z)
  (spec_closed : injection_closed spec)
  (spec_ok : 
    forall ef x tys args targs m rty rv m' tm z z' j,
    ext_spec_pre spec ef x tys args z m -> 
    ext_spec_post spec ef x rty rv z' m' -> 
    Mem.inject (as_inj j) m tm -> 
    val_list_inject (restrict (as_inj j) (vis j)) args targs -> 
    mem_forward m m' -> 
    Mem.unchanged_on (fun b ofs => REACH m (getBlocks args) b=false) m m'  -> 
    exists j' rv' tm',
      inject_incr (as_inj j) (as_inj j') 
      /\ oval_inject (as_inj j') rv rv'
      /\ Mem.inject (as_inj j') m' tm'
      /\ sm_inject_separated j j' m tm 
      /\ SM_wd j'
      /\ sm_valid j' m' tm'
      /\ mem_forward tm tm'
      /\ Mem.unchanged_on (fun b ofs => 
           ~target_accessible j m tm args b ofs) tm tm').

Section match_event.

Import Event.

Inductive match_event : Event.t -> Event.t -> Prop :=
| mk_match_event : 
  forall j j' ev1 ev2,
  Mem.inject (as_inj j) ev1.(pre_mem) ev2.(pre_mem) -> 
  Mem.inject (as_inj j') ev1.(post_mem) ev2.(post_mem) -> 
  Forall2 (val_inject (restrict (as_inj j) (vis j))) ev1.(args) ev2.(args) -> 
  oval_inject (as_inj j') ev1.(rv) ev2.(rv) ->
  match_event ev1 ev2.

End match_event.

Inductive match_trace : list Event.t -> list Event.t -> Prop :=
| match_trace_nil : match_trace nil nil
| match_trace_cons : 
  forall tr1 tr2 ev1 ev2,
  match_event ev1 ev2 -> 
  match_trace tr1 tr2 -> 
  match_trace (ev1 :: tr1) (ev2 :: tr2).

Variable sim : SM_simulation_inject source target geS geT entry_points.

Notation data := (sim.(SM_simulation.core_data _ _ _ _ _)).
Notation ord  := (sim.(SM_simulation.core_ord _ _ _ _ _)).
Notation match_state := (sim.(SM_simulation.match_state _ _ _ _ _)).

Inductive trace_match_state : 
  data -> SM_Injection -> Z*list Event.t*C -> mem -> Z*list Event.t*D -> mem -> Prop :=
| mk_trace_match_state :
  forall j tr z c m ttr d tm cd,
  match_trace tr ttr -> 
  match_state cd j c m d tm -> 
  trace_match_state cd j (z,tr,c) m (z,ttr,d) tm. 

Variables 
(SRC_DET : corestep_fun source)
(TGT_DET : corestep_fun target).

Notation tr_source := (TraceSemantics.coopsem z_init source spec).
Notation tr_target := (TraceSemantics.coopsem z_init target spec).

Lemma corestep_plus_match {c m d tm c' m' cd j} :
  corestep_plus source geS c m c' m' -> 
  match_state cd j c m d tm -> 
  exists d' tm' cd' j', 
    corestep_plus target geT d tm d' tm'
    /\ match_state cd' j' c' m' d' tm'.
Admitted.

Lemma REACH_mono':
  forall B1 B2 : block -> bool,
  (forall b : block, B1 b = true -> B2 b = true) ->
  forall (m : mem) (b : block), REACH m B2 b = false -> REACH m B1 b = false.
Proof.
intros ? ? SUB m b HR.
case_eq (REACH m B1 b); auto.
solve[intros H; generalize (REACH_mono _ _ SUB _ _ H); congruence].
Qed.

Lemma REACH_as_inj': forall mu (WD: SM_wd mu) m1 m2 vals1 vals2 
        (MemInjMu : Mem.inject (as_inj mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2) b1
        (R : REACH m1 (getBlocks vals1) b1 = true)
        B (HB: forall b b2 d, shared_of mu b = Some(b2,d) -> B b2 = true),
      exists b2 d, as_inj mu b1 = Some (b2, d) /\ 
                   REACH m2 (fun b => orb (getBlocks vals2 b) (B b)) b2 = true.
Proof. intros.
 eapply (REACH_inject _ _ _ MemInjMu); try eassumption.
 clear R. simpl; intros.
 destruct (getBlocks_inject _ _ _ ValInjMu _ H) as [b2 [d [J G]]].
 exists b2, d. rewrite J, G. intuition.
Qed.

Lemma REACH_as_inj_REACH': forall mu (WD: SM_wd mu) m1 m2 vals1 vals2 
        (MemInjMu : Mem.inject (as_inj mu) m1 m2)
        (ValInjMu : Forall2 (val_inject (as_inj mu)) vals1 vals2) b1
        (R : REACH m1 (getBlocks vals1) b1 = true),
      exists b2 d, as_inj mu b1 = Some (b2, d) /\ 
                   REACH m2 (getBlocks vals2) b2 = true.
Proof. intros.
  destruct (REACH_as_inj' _ WD _ _ _ _ MemInjMu ValInjMu _ R (fun b => true))
       as [b2 [d [ASI _]]]. trivial.
  exists b2, d. split; trivial.
  destruct (REACH_inject _ _ _ MemInjMu) 
    with (B1 := getBlocks vals1) (B2 := getBlocks vals2) (b1 := b1); auto.
  intros.
  solve[apply getBlocks_inject with (vals1 := vals1); auto]. 
  destruct H as [bb2 [ASI' RR]]; rewrite ASI' in ASI; inv ASI.
  assumption.
Qed.

Definition visSrc mu b := locBlocksSrc mu b || frgnBlocksSrc mu b.

Definition visTgt mu b := locBlocksTgt mu b || frgnBlocksTgt mu b.

Definition marshal j m args tm targs := 
  Build_SM_Injection
  (fun _ => false) (fun _ => false) 
  (fun _ => false) (fun _ => false) 
  (fun _ => None)
  (REACH m (getBlocks args))
  (REACH tm (getBlocks targs))
  (REACH m (getBlocks args))
  (REACH tm (getBlocks targs))
  j.

Lemma as_inj_marshal j m args tm targs :
  as_inj (marshal j m args tm targs) = j.
Proof. 
unfold marshal, as_inj, join; simpl.
extensionality b.
destruct (j b); auto.
destruct p; auto.
Qed.

Lemma foreign_of_marshal j m args tm targs :
  foreign_of (marshal j m args tm targs) 
  = restrict j (REACH m (getBlocks args)).
Proof. 
unfold marshal, as_inj, join, restrict; simpl.
extensionality b.
destruct (j b); auto.
Qed.

Lemma locBlocksTgt_marshal j m args tm targs :
  locBlocksTgt (marshal j m args tm targs) = (fun _ => false).
Proof. unfold marshal, as_inj, join, restrict; auto. Qed.

Lemma vis_marshal j m args tm targs :
  vis (marshal j m args tm targs) = REACH m (getBlocks args).
Proof. unfold marshal, vis; simpl; auto. Qed.

Lemma yielded_source_yielded_target {cd j c d m tm} :
  match_state cd j c m d tm -> 
  TraceSemantics.yielded source c -> 
  TraceSemantics.yielded target d.
Admitted.

Lemma semantics_preservation_aux {n c c' d m m' tm cd j} : 
  trace_match_state cd j c m d tm -> 
  corestepN tr_source geS n c m c' m' -> 
  exists cd' j' d' tm',
    corestepN tr_target geT n d tm d' tm' 
    /\ trace_match_state cd' j' c' m' d' tm'.
Proof.
intros TRMATCH STEPN; revert cd j c m d tm TRMATCH STEPN.
induction n; simpl; intros cd j c m d tm TRMATCH STEPN.
solve[inv STEPN; exists cd, j, d, tm; split; auto].
destruct STEPN as [[[z2 tr] c2] [m2 [STEP STEPN]]].
destruct c as [[z tr2] c].
destruct d as [[tz ttr] d].
assert (MATCH: match_state cd j c m d tm). 
  solve[inv TRMATCH; auto].
inv STEP; rename H8 into STEPP.
{ (*internal step case*)
generalize (corestep_plus_match STEPP MATCH).
intros [d2 [tm2 [cd2 [j2 [STEPP' MATCH2]]]]].
assert (TRMATCH2: trace_match_state cd2 j2 (z2,tr,c2) m2 (z2,ttr,d2) tm2).
  constructor; auto.
  solve[inv TRMATCH; auto].
generalize (IHn _ _ _ _ _ _ TRMATCH2 STEPN).
intros [cd' [j' [d' [tm' [TSTEPN' TRMATCH']]]]].
exists cd', j', d', tm'; split; auto.
exists (tz,ttr,d2), tm2; split; auto.
constructor; auto.
solve[eapply yielded_source_yielded_target in H9; eauto].
assert (tz = z2) as -> by (inv TRMATCH; auto). 
solve[auto].
}
Arguments core_at_external : default implicits.
{ (*external step case*)
assert (exists targs, 
  at_external target d = Some (ef, sig, targs)
  /\ val_list_inject (restrict (as_inj j) (vis j)) args targs) 
  as [targs [AT VALINJ]].
  inv TRMATCH; eapply core_at_external in H15; eauto.
  destruct H15 as [_ [targs [? ?]]]; exists targs; split; auto.
  solve[apply forall_inject_val_list_inject; auto].
assert (INJ: Mem.inject (as_inj j) m tm). 
  inv TRMATCH; eapply core_at_external in H15; eauto.
  solve[destruct H15 as [? _]; auto].
set (pubSrc' := fun b => andb (locBlocksSrc j b) (REACH m (exportedSrc j args) b)).
set (pubTgt' := fun b => andb (locBlocksTgt j b) (REACH tm (exportedTgt j targs) b)).
set (nu := replace_locals j pubSrc' pubTgt').

set (mu := marshal (as_inj j) m args tm targs).
assert (MU_INJ: Mem.inject (as_inj mu) m tm). 
  solve[unfold mu; rewrite as_inj_marshal; auto].
assert (MU_VALINJ: val_list_inject (restrict (as_inj mu) (vis mu)) args targs).
  inv TRMATCH; eapply core_at_external in H15; eauto.
  destruct H15 as [_ [? [VALINJ' ATEXT]]].
  rewrite ATEXT in AT; inv AT.
  unfold mu; rewrite as_inj_marshal, vis_marshal.
  apply forall_inject_val_list_inject.
  admit.

generalize (spec_ok ef x (sig_args sig) args targs m 
  (sig_res sig) (Some rv) m2 tm _ _ mu H11 H12 MU_INJ MU_VALINJ H10 STEPP).
intros [mu2 [trv [tm2 [INCR [RVALINJ [INJ2 [SEP2 [WD2 [VAL2 [TFWD2 TUNCH]]]]]]]]]].

set (nu2 := reestablish nu mu2).
set (frgnSrc' := fun b : block =>
     DomSrc nu2 b &&
     (negb (locBlocksSrc nu2 b) && REACH m2 (exportedSrc nu2 (rv :: nil)) b)).

assert (exists trv0, trv = Some trv0) as [trv0 ->]. 
  simpl in RVALINJ; destruct trv as [trv|]; try solve[elimtype False; auto].
  solve[exists trv; auto].

set (frgnTgt' := fun b : block =>
     DomTgt nu2 b &&
     (negb (locBlocksTgt nu2 b) &&
      REACH tm2 (exportedTgt nu2 (trv0 :: nil)) b)).

set (nu' := replace_externs nu2 frgnSrc' frgnTgt').

(* admits here mostly related to reestablish -- *)
assert (VALINJ': Forall2 (val_inject (as_inj j)) args targs). 
  admit.
assert (VALINJ'': Forall2 (val_inject (restrict (as_inj j) (vis j))) args targs).
  solve[apply val_list_inject_forall_inject; auto].

assert (EINCR: extern_incr nu nu2). 
  apply reestablish_extern_incr'; auto.
  admit. 
  unfold nu; rewrite replace_locals_as_inj.
  apply inject_incr_trans with (f2 := as_inj mu); auto.
  unfold mu; rewrite as_inj_marshal.
  apply inject_incr_refl.
  admit.
  admit.
assert (NU_SEP: sm_inject_separated nu nu2 m tm). 
  admit.
assert (NU_WD: SM_wd nu2).
  apply reestablish_wd'; auto.
  admit.
  unfold nu; rewrite replace_locals_as_inj.
  apply inject_incr_trans with (f2 := as_inj mu); auto.
  unfold mu; rewrite as_inj_marshal.
  apply inject_incr_refl.
  intros ? ? ? AS.
  unfold nu. 
  rewrite replace_locals_locBlocksSrc, replace_locals_locBlocksTgt.
  rewrite replace_locals_extBlocksSrc, replace_locals_extBlocksTgt.
  split; auto.
  admit. (*by j WD*)
  admit. (*by j WD*)
  admit.
assert (NU_VAL: sm_valid nu2 m2 tm2). admit.
assert (NU_INJ: Mem.inject (as_inj nu2) m2 tm2). admit.
assert (NU_VINJ: val_inject (as_inj nu2) rv trv0). admit.

generalize (@eff_after_external _ _ _ _ _ _ _ _ _ _ _ 
  sim cd j c d m ef args tm sig targs ef sig INJ MATCH H6 AT VALINJ''
  pubSrc' refl_equal
  pubTgt' refl_equal
  nu refl_equal nu2 rv m2 trv0 tm2 
  EINCR NU_SEP NU_WD NU_VAL NU_INJ NU_VINJ H10 TFWD2
  frgnSrc' refl_equal
  frgnTgt' refl_equal
  nu' refl_equal).

destruct 1 as [acd [ac [ad [AFT1 [AFT2 AMATCH]]]]]; auto. 
apply unch_on_validblock with (V := 
  fun b ofs => REACH m (getBlocks args) b=false); auto.
intros b ofs BVAL [X Y].
unfold nu in Y; unfold pubSrc', pubTgt' in Y. 
rewrite replace_locals_pubBlocksSrc in Y. 
unfold nu in X; rewrite replace_locals_locBlocksSrc in X.
rewrite X in Y; simpl in Y.
apply REACH_mono' with (B2 := exportedSrc j args); auto.
solve[intros b'; unfold exportedSrc; intros ->; auto].

apply unch_on_validblock with (V := 
  fun b ofs => ~target_accessible mu m tm args b ofs); auto.
intros b ofs BVAL [X Y].
unfold nu in Y; unfold pubSrc', pubTgt' in Y. 
rewrite replace_locals_pubBlocksSrc in Y.
rewrite replace_locals_local in Y.
unfold nu in X; rewrite replace_locals_locBlocksTgt in X.
unfold target_accessible; unfold mu; simpl; intros [VAL TA].
destruct TA as [b0 [d0 [INJ0 [HR' PERM]]]]; auto.
assert (HR'': REACH m (exportedSrc j args) b0=true).
  apply REACH_mono with (B1 := getBlocks args); auto.
  solve[unfold exportedSrc; intros ? ->; auto].
Arguments match_sm_wd : default implicits.
generalize (match_sm_wd sim _ _ _ _ _ _ MATCH); intros WD.
apply REACH_as_inj_REACH with (m2 := tm) (vals2 := targs) in HR''; auto.
destruct HR'' as [b' [d' [INJ'' HR'']]].
assert (b = b' /\ d0 = d') as [? ?]. 
  unfold mu in INJ0; rewrite HR' in INJ0.
  solve[rewrite INJ0 in INJ''; inv INJ''; auto].
subst b' d'.

assert (local_of j b0 = Some (b, d0) /\ locBlocksSrc j b0=true)
  as [LOCOF LSRC].
  generalize INJ''; clear INJ''.
  unfold as_inj, join.
  case_eq (extern_of j b0); auto.
  intros [? ?] EXT; inversion 1; subst.
  apply extern_DomRng' in EXT; auto.
  destruct EXT as [_ [_ [_ [TLOC _]]]].
  solve[rewrite TLOC in X; congruence].
  intros; split; auto.
  apply local_DomRng in INJ''; auto.
  destruct INJ''; auto.
destruct (Y _ _ LOCOF).
solve[apply H; apply PERM].
assert (HR''': REACH m (exportedSrc j args) b0=true).
  apply REACH_mono with (B1 := getBlocks args); auto.
  solve[unfold exportedSrc; intros ? ->; auto].
rewrite LSRC, HR''' in H; simpl in H; congruence.

Arguments match_validblocks : default implicits.
generalize (match_validblocks sim _ _ _ _ _ _ MATCH); intros ?.
edestruct eff_after_check1 
  with (mu := j) (m1 := m) (m2 := tm) (vals1 := args) (vals2 := targs)
       (pubSrc' := pubSrc') (pubTgt' := pubTgt'); auto.
solve[apply (match_sm_wd sim _ _ _ _ _ _ MATCH)].
set (tr2' := Event.mk m m2 args (Some rv) :: tr2).
set (ttr' := Event.mk tm tm2 targs (Some trv0) :: ttr).
destruct (IHn acd nu' (z2,tr2',ac) m2 (z2,ttr',ad) tm2)
  as [cd' [j' [d' [tm' [STEPN' MATCH']]]]].
constructor. constructor. econstructor; eauto.
solve[apply val_list_inject_forall_inject; auto].
solve[inv TRMATCH; auto].
solve[auto].
solve[rewrite H13 in AFT1; inv AFT1; apply STEPN].

exists cd', j', d', tm'; split; auto.
exists (z2,ttr',ad), tm2; split; auto.
econstructor; eauto. 

apply unch_on_validblock with (V := 
  fun b ofs => ~target_accessible mu m tm args b ofs); auto.
intros b ofs X Y. 
unfold target_accessible; intros [VAL TA]. 
destruct TA as [b0 [d0 [FR [RC PERM]]]]; auto.
apply REACH_as_inj_REACH' with (m2 := tm) (vals2 := targs) (mu := j) in RC; auto.
destruct RC as [b2 [d2 [INJ' RR]]].
assert (b = b2). 
  apply foreign_in_all in FR. 
  unfold mu in FR; rewrite as_inj_marshal in FR.
  solve[rewrite FR in INJ'; inv INJ'; auto].
solve[subst; congruence].
solve[apply (match_sm_wd sim _ _ _ _ _ _ MATCH)].

instantiate (1 := x).
assert (VALINJ''' : val_list_inject (as_inj j) args targs). 
  solve[apply forall_inject_val_list_inject; auto].
generalize (P_closed spec_closed ef x (sig_args sig) z H11 VALINJ''' INJ).
assert (z = tz) as -> by (inv TRMATCH; auto).
solve[auto].
generalize (Q_closed spec_closed ef x 
  (sig_res sig) (Some rv) z2 (Some trv0) H12 RVALINJ INJ2).
solve[auto]. }
Qed.

Lemma target_tracesem_det {x x' x'' m m' m'' n} :
  corestepN tr_target geT n x m x' m' -> 
  corestepN tr_target geT n x m x'' m'' -> 
  x'=x'' /\ m'=m''.
Admitted.

Lemma semantics_preservation z z' c c' d m m' tm tr cd j n :
  match_state cd j c m d tm -> 
  corestepN tr_source geS n (z,nil,c) m (z',tr,c') m' -> 
  (exists z'' d' tm' ttr, corestepN tr_target geT n (z,nil,d) tm (z'',ttr,d') tm')
  /\ forall z'' d' tm' ttr, 
     corestepN tr_target geT n (z,nil,d) tm (z'',ttr,d') tm' -> 
     match_trace tr ttr.
Proof.  
intros MATCH STEPN.
assert (TRMATCH: trace_match_state cd j (z,nil,c) m (z,nil,d) tm).
  constructor; auto.
  solve[constructor; auto].
generalize (semantics_preservation_aux TRMATCH STEPN).
intros [cd' [j' [[[tz' ttr] d'] [tm' [TSTEPN TTRMATCH]]]]].
split; [solve[exists tz', d', tm', ttr; auto]|].
intros tz'' d'' tm'' ttr' TSTEPN'.
generalize (target_tracesem_det TSTEPN TSTEPN'); intros [X Y].
inv X.
solve[inv TTRMATCH; auto].
Qed.

End semantics_preservation.