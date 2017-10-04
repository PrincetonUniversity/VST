Require Import sepcomp.compcert. Import CompcertAll.

Require Import msl.Axioms.

Require Import sepcomp.step_lemmas.
Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.trace_semantics.
Require Import sepcomp.StructuredInjections.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.effect_properties.
Require Import sepcomp.rg_lemmas.
Require Import sepcomp.extspec. Import ExtSpecProperties.
Require Import sepcomp.arguments.
Require Import sepcomp.closed_safety.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import SM_simulation.

Definition target_accessible mu m tm args b ofs :=
  Mem.valid_block tm b /\
  (locBlocksTgt mu b=false ->
    exists b0 d,
      foreign_of mu b0 = Some (b, d)
      /\ REACH m (getBlocks args) b0=true
      /\ Mem.perm m b0 (ofs-d) Max Nonempty).

Definition incr mu mu' :=
  inject_incr (as_inj mu) (as_inj mu')
  /\ (forall b, DomSrc mu b=true -> DomSrc mu' b=true)
  /\ (forall b, DomTgt mu b=true -> DomTgt mu' b=true).

Section open_semantics_preservation.

Variable (F V TF TV C D Z : Type) (z_init : Z).

Variable source : @EffectSem (Genv.t F V) C.
Variable target : @EffectSem (Genv.t TF TV) D.

Variable (geS : Genv.t F V) (geT : Genv.t TF TV).
Variable entry_points : list (val*val*signature).

Variable spec : ext_spec Z.

(* External function specifications P,Q,EXIT closed under injection of
   arguments, return values, and memories: *)

Variable spec_closed : ExtSpecProperties.closed spec.

(* External function specs commute w/ injection in the following sense: *)

Variable spec_ok :
  forall ef x tys args targs m rty rv m' tm z z' j,
  ext_spec_pre spec ef x tys args z m ->
  ext_spec_post spec ef x rty rv z' m' ->
  Mem.inject (as_inj j) m tm ->
  val_list_inject (restrict (as_inj j) (vis j)) args targs ->
  mem_forward m m' ->
  Mem.unchanged_on (fun b ofs => REACH m (getBlocks args) b=false) m m' ->
  exists j' rv' tm',
    incr j j'
    /\ oval_inject (as_inj j') rv rv'
    /\ Mem.inject (as_inj j') m' tm'
    /\ sm_inject_separated j j' m tm
    /\ SM_wd j'
    /\ sm_valid j' m' tm'
    /\ mem_forward tm tm'
    /\ Mem.unchanged_on (fun b ofs =>
         ~target_accessible j m tm args b ofs) tm tm'.

Variable sim : SM_simulation_inject source target geS geT entry_points.

Variable src_det : corestep_fun source.
Variable tgt_det : corestep_fun target.
Variable ext_spec_det : ExtSpecProperties.det spec.

Notation tr_source := (TraceSemantics.coopsem z_init source spec).
Notation tr_target := (TraceSemantics.coopsem z_init target spec).

(* Follow from determinism of ext calls + src/tgt_det above *)

Lemma tr_src_det : corestep_fun tr_source.
Proof. apply TraceSemantics.fun_FUN; auto. Qed.

Lemma tr_tgt_det : corestep_fun tr_target.
Proof. apply TraceSemantics.fun_FUN; auto. Qed.

Definition ogetBlock (ov : option val) : block -> bool :=
  match ov with
    | None => fun _:block => false
    | Some v => getBlocks (v::nil)
  end.

Section match_event.

Import Event.

Inductive match_event : Event.t -> Event.t -> Prop :=
| mk_match_event :
  forall j j' ev1 ev2,
  let args1 := ev1.(args) in
  let args2 := ev2.(args) in
  let rv1 := ev1.(rv) in
  let rv2 := ev2.(rv) in
  let m1 := ev1.(pre_mem) in
  let m1' := ev1.(post_mem) in
  let m2 := ev2.(pre_mem) in
  let m2' := ev2.(post_mem) in
  inject_incr (as_inj j) (as_inj j') ->
  Mem.inject (as_inj j) m1 m2 ->
  Mem.inject (as_inj j') m1' m2' ->
  Forall2 (val_inject (as_inj j)) args1 args2 ->
  oval_inject (as_inj j') rv1 rv2 ->
  match_event ev1 ev2.

End match_event.

Inductive match_trace : list Event.t -> list Event.t -> Prop :=
| match_trace_nil : match_trace nil nil
| match_trace_cons :
  forall tr1 tr2 ev1 ev2,
  match_event ev1 ev2 ->
  match_trace tr1 tr2 ->
  match_trace (ev1 :: tr1) (ev2 :: tr2).

Notation data := (sim.(SM_simulation.core_data _ _ _ _ _)).
Notation ord  := (sim.(SM_simulation.core_ord _ _ _ _ _)).
Notation match_state := (sim.(SM_simulation.match_state _ _ _ _ _)).

Inductive trace_match_state :
  data -> SM_Injection -> Z*list Event.t*C -> mem ->
                          Z*list Event.t*D -> mem -> Prop :=
| mk_trace_match_state :
  forall j tr z c m ttr d tm cd,
  match_trace tr ttr ->
  match_state cd j c m d tm ->
  trace_match_state cd j (z,tr,c) m (z,ttr,d) tm.

Lemma corestep_matchN {c m d tm c' m' cd j n} :
  corestepN source geS n c m c' m' ->
  match_state cd j c m d tm ->
  exists d' tm' cd' j' n',
    corestepN target geT n' d tm d' tm'
    /\ match_state cd' j' c' m' d' tm'.
Proof.
revert cd j c m d tm; induction n; simpl; intros cd j c m d tm.
inversion 1; subst.
intros MATCH; exists d, tm, cd, j, O; split; simpl; auto.
intros [c2 [m2 [STEP STEPN]]] MATCH.
generalize STEP as STEP'; intro.
eapply core_diagram in STEP; eauto.
destruct STEP as [d2 [tm2 [cd2 [j2 [? [? [? [MATCH2 [? [? TSTEPN]]]]]]]]]].
assert (exists n', corestepN target geT n' d tm d2 tm2) as [n' TSTEPN'].
{ destruct TSTEPN as [[n' X]|[[n' X] _]].
  exists (S n'); auto.
  exists n'; auto. }
assert (STEPN': corestepN source geS (S O) c m c2 m2).
{ simpl; exists c2, m2; split; auto. }
destruct (IHn _ _ _ _ _ _ STEPN MATCH2)
  as [d'' [tm'' [cd'' [j'' [n'' [TSTEPN'' MATCH']]]]]].
exists d'', tm'', cd'', j'', (plus n' n''); split; auto.
rewrite corestepN_add; exists d2, tm2; split; auto.
Qed.

Lemma yielded_src_tgt {cd j c d m tm} :
  match_state cd j c m d tm ->
  TraceSemantics.yielded source c ->
  TraceSemantics.yielded target d.
Proof.
intros MATCH [[ef [sig [args X]]]|[rv X]].
eapply core_at_external in MATCH; eauto.
destruct MATCH as [? [? [? ?]]]; left.
exists ef, sig, x; auto.
eapply core_halted in MATCH; eauto.
destruct MATCH as [? [? [? ?]]].
right; exists x; auto.
Qed.

Lemma nyielded_tgt_src {cd j c d m tm} :
  match_state cd j c m d tm ->
  ~TraceSemantics.yielded target d ->
  ~TraceSemantics.yielded source c.
Proof. intros H H2 H3; apply H2; eapply yielded_src_tgt; eauto. Qed.

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
  destruct (@REACH_as_inj' _ WD _ _ _ _ MemInjMu ValInjMu _ R (fun b => true))
       as [b2 [d [ASI _]]]. trivial.
  exists b2, d. split; trivial.
  destruct (REACH_inject _ _ _ MemInjMu)
    with (B1 := getBlocks vals1) (B2 := getBlocks vals2) (b1 := b1); auto.
  intros.
  solve[apply getBlocks_inject with (vals1 := vals1); auto].
  destruct H as [bb2 [ASI' RR]]; rewrite ASI' in ASI; inv ASI.
  assumption.
Qed.

Definition marshal j m args tm targs :=
  Build_SM_Injection
  (fun _ => false) (fun _ => false)
  (fun _ => false) (fun _ => false)
  (fun _ => None)
  (DomSrc j)
  (DomTgt j)
  (REACH m (getBlocks args))
  (REACH tm (getBlocks targs))
  (as_inj j).

Lemma as_inj_marshal j m args tm targs :
  as_inj (marshal j m args tm targs) = as_inj j.
Proof.
unfold marshal, as_inj, join; simpl; extensionality b.
destruct (extern_of j b).
destruct p; auto.
destruct (local_of j b); auto.
destruct p; auto.
Qed.

Lemma foreign_of_marshal j m args tm targs :
  foreign_of (marshal j m args tm targs)
  = restrict (as_inj j) (REACH m (getBlocks args)).
Proof.
unfold marshal, as_inj, join, restrict; simpl.
extensionality b.
destruct (REACH m (getBlocks args) b); simpl; auto.
Qed.

Lemma DomSrc_marshal j m args tm targs :
  DomSrc (marshal j m args tm targs) = DomSrc j.
Proof. unfold DomSrc; extensionality b; auto. Qed.

Lemma DomTgt_marshal j m args tm targs :
  DomTgt (marshal j m args tm targs) = DomTgt j.
Proof. unfold DomSrc; extensionality b; auto. Qed.

Lemma locBlocksTgt_marshal j m args tm targs :
  locBlocksTgt (marshal j m args tm targs) = (fun _ => false).
Proof. unfold marshal, as_inj, join, restrict; auto. Qed.

Lemma vis_marshal j m args tm targs :
  vis (marshal j m args tm targs) = REACH m (getBlocks args).
Proof. unfold marshal, vis; simpl; auto. Qed.

Lemma injsep_marshal j j' m args tm targs m1 m2 :
  sm_inject_separated j (marshal j' m args tm targs) m1 m2 ->
  sm_inject_separated j j' m1 m2.
Proof.
intros [H [H2 H3]].
rewrite as_inj_marshal in H.
rewrite DomSrc_marshal in H2.
rewrite DomTgt_marshal in H3.
split; intros.
solve[destruct (H _ _ _ H0 H1); split; auto].
split; intros.
apply H2; auto.
apply H3; auto.
Qed.

Lemma injsep_marshal' j j' m args tm targs m1 m2 :
  sm_inject_separated (marshal j m args tm targs) j' m1 m2 ->
  sm_inject_separated j j' m1 m2.
Proof.
intros [H [H2 H3]].
rewrite as_inj_marshal in H.
rewrite DomSrc_marshal in H2.
rewrite DomTgt_marshal in H3.
split; intros.
destruct (H _ _ _ H0 H1); split.
rewrite DomSrc_marshal in H4; auto.
rewrite DomTgt_marshal in H5; auto.
split; intros.
apply H2; auto.
apply H3; auto.
Qed.

Lemma restrict_as_inj_eq j j' m1 m2 :
  SM_wd j ->
  SM_wd j' ->
  inject_incr (as_inj j) (as_inj j') ->
  sm_inject_separated j j' m1 m2 ->
  sm_valid j m1 m2 ->
  restrict (as_inj j') (DomSrc j) = as_inj j.
Proof.
intros.
extensionality b.
case_eq (as_inj j b).
intros [ofs d] INJ.
assert (H4: DomSrc j b=true).
{ apply as_inj_DomRng in INJ; auto.
  destruct INJ; auto. }
apply H1 in INJ.
unfold restrict.
rewrite H4; auto.
intros INJ.
case_eq (as_inj j' b).
intros [ofs d] INJ'.
assert (H5: DomSrc j b=false).
{ destruct H3 as [H3 H4].
  destruct H2 as [H5 [H6 H7]].
  destruct (H5 _ _ _ INJ INJ'); auto. }
assert (H6: ~Mem.valid_block m1 b).
{ destruct H3 as [H3 H4].
  destruct H2 as [H6 [H7 H8]].
  apply as_inj_DomRng in INJ'; auto.
  destruct INJ' as [X Y]; auto. }
unfold restrict; rewrite H5; auto.
intros INJ'.
unfold restrict.
rewrite INJ'; destruct (DomSrc j b); auto.
Qed.

Lemma reach_in_exported_src b m args j :
  REACH m (getBlocks args) b=true -> REACH m (exportedSrc j args) b=true.
Proof.
intros H; apply REACH_mono with (B1 := getBlocks args); auto.
intros b0 H2; unfold exportedSrc; rewrite H2; auto.
Qed.

Arguments reach_in_exported_src {b m args} j _.

Lemma reach_in_exported_tgt {b m args} j :
  REACH m (getBlocks args) b=true -> REACH m (exportedTgt j args) b=true.
Proof.
intros H; apply REACH_mono with (B1 := getBlocks args); auto.
intros b0 H2; unfold exportedTgt; rewrite H2; auto.
Qed.

Arguments reach_in_exported_tgt {b m args} j _.

Lemma extern_semantics_preservation c c' d m m' tm cd j ef sig args :
  trace_match_state cd j c m d tm ->
  corestep tr_source geS c m c' m' ->
  at_external source (snd c) = Some (ef, sig, args) ->
  exists cd' j' d' tm',
    corestep tr_target geT d tm d' tm'
    /\ trace_match_state cd' j' c' m' d' tm'.
Proof.
intros TRMATCH STEP ATEXTSRC.
destruct c as [[z tr2] c].
destruct d as [[tz ttr] d].
assert (MATCH: match_state cd j c m d tm) by (inv TRMATCH; auto).
inv STEP. rename H6 into STEP.

{ (*internal step case*)
elimtype False.
apply corestep_not_at_external in STEP.
simpl in ATEXTSRC; rewrite STEP in ATEXTSRC; inv ATEXTSRC. }

{ (*external step case*)
assert (exists targs,
  at_external target d = Some (ef, sig, targs)
  /\ val_list_inject (restrict (as_inj j) (vis j)) args targs)
  as [targs [AT VALINJ]].
  { inv TRMATCH; eapply core_at_external in ATEXTSRC; eauto.
    destruct ATEXTSRC as [_ [targs [? ?]]]; exists targs; split; auto.
    solve[apply forall_inject_val_list_inject; auto]. }

assert (INJ: Mem.inject (as_inj j) m tm).
  { inv TRMATCH; eapply core_at_external in ATEXTSRC; eauto.
    solve[destruct ATEXTSRC as [? _]; auto]. }

set (pubSrc' := fun b =>
  andb (locBlocksSrc j b) (REACH m (exportedSrc j args) b)).
set (pubTgt' := fun b =>
  andb (locBlocksTgt j b) (REACH tm (exportedTgt j targs) b)).
set (nu := replace_locals j pubSrc' pubTgt').
set (mu := marshal nu m args tm targs).

assert (MU_INJ: Mem.inject (as_inj mu) m tm)
  by (unfold mu, nu; rewrite as_inj_marshal, replace_locals_as_inj; auto).

assert (MU_VALINJ:
  val_list_inject (restrict (as_inj mu) (vis mu)) args targs).
  { inv TRMATCH; eapply core_at_external in ATEXTSRC; eauto.
    destruct ATEXTSRC as [_ [? [VALINJ' ATEXT]]].
    rewrite ATEXT in AT; inv AT.
    unfold mu; rewrite as_inj_marshal, vis_marshal.
    apply forall_inject_val_list_inject.
    unfold nu; rewrite replace_locals_as_inj.
    apply forall_vals_inject_restrictD in VALINJ'.
    apply restrict_forall_vals_inject; auto.
    intros b GET; apply REACH_nil; auto. }

simpl in ATEXTSRC; rewrite H2 in ATEXTSRC; inv ATEXTSRC.
rename H3 into UNCH; rename H4 into FORWARD.
rename H6 into PRE; rename H10 into POST.
generalize (@spec_ok ef x (sig_args sig) args targs m
  (sig_res sig) (Some rv) m' tm _ _ mu PRE POST MU_INJ MU_VALINJ FORWARD UNCH).
intros [mu2 [trv [tm2 [INCR [RVALINJ [INJ2 [SEP2 [WD2
  [VAL2 [TFWD2 TUNCH]]]]]]]]]].
set (nu2 := reestablish nu mu2).
set (frgnSrc' := fun b : block =>
     DomSrc nu2 b && (negb (locBlocksSrc nu2 b)
       && REACH m' (exportedSrc nu2 (rv :: nil)) b)).

assert (exists trv0, trv = Some trv0) as [trv0 ->].
  { simpl in RVALINJ; destruct trv as [trv|]; try solve[elimtype False; auto].
    solve[exists trv; auto]. }

set (frgnTgt' := fun b : block =>
     DomTgt nu2 b && (negb (locBlocksTgt nu2 b)
       && REACH tm2 (exportedTgt nu2 (trv0 :: nil)) b)).

set (nu' := replace_externs nu2 frgnSrc' frgnTgt').

assert (VALINJ': Forall2 (val_inject (as_inj j)) args targs).
  { apply val_list_inject_forall_inject in MU_VALINJ.
    apply forall_vals_inject_restrictD in MU_VALINJ.
    generalize MU_VALINJ; unfold mu; rewrite as_inj_marshal.
    unfold nu; rewrite replace_locals_as_inj; auto. }

assert (VALINJ'':
  Forall2 (val_inject (restrict (as_inj j) (vis j))) args targs)
  by (apply val_list_inject_forall_inject; auto).

assert (J_WD: SM_wd j)
  by (apply (match_sm_wd sim _ _ _ _ _ _ MATCH)).

assert (J_VAL: sm_valid j m tm)
  by (apply match_validblocks in MATCH; auto).

assert (NU_WD: SM_wd nu).
  { edestruct eff_after_check1
    with (mu := j) (m1 := m) (m2 := tm) (vals1 := args) (vals2 := targs)
       (pubSrc' := pubSrc') (pubTgt' := pubTgt'); auto. }

assert (NU_VAL: sm_valid nu m tm).
  { edestruct eff_after_check1
    with (mu := j) (m1 := m) (m2 := tm) (vals1 := args) (vals2 := targs)
      (pubSrc' := pubSrc') (pubTgt' := pubTgt'); auto.
    destruct H0; auto. }

assert (EINCR: extern_incr nu nu2).
  { apply reestablish_extern_incr'; auto.
    unfold nu; rewrite replace_locals_as_inj.
    apply inject_incr_trans with (f2 := as_inj mu); auto.
    unfold mu, nu; rewrite as_inj_marshal, replace_locals_as_inj.
    apply inject_incr_refl.
    destruct INCR; auto.
    intros b; unfold nu; rewrite replace_locals_extBlocksSrc; intros A.
    destruct INCR as [X [Y W]]; apply Y.
    unfold mu, nu, marshal, DomSrc; simpl.
    rewrite replace_locals_extBlocksSrc, A.
    solve[rewrite !orb_true_iff; auto].
    intros b; unfold nu; rewrite replace_locals_extBlocksTgt; intros A.
    destruct INCR as [X [Y W]]; apply W.
    unfold mu, nu, marshal, DomTgt; simpl.
    rewrite replace_locals_extBlocksTgt, A.
    solve[rewrite !orb_true_iff; auto]. }

assert (NUMU2_SEP: sm_inject_separated nu mu2 m tm).
  { apply injsep_marshal' in SEP2; auto. }

assert (RESTRICT_MU2_NU: restrict (as_inj mu2) (DomSrc nu) = as_inj nu).
  { apply restrict_as_inj_eq with (m1 := m) (m2 := tm); auto.
    destruct INCR as [INCR _].
    apply inject_incr_trans with (f2 := as_inj mu); auto.
    unfold mu; rewrite as_inj_marshal.
    apply inject_incr_refl. }

assert (LOCNU_IN_DOMSRC:
  forall b, locBlocksSrc nu b=true -> DomSrc mu2 b=true).
  { unfold nu; rewrite replace_locals_locBlocksSrc.
    intros b LOC. cut (DomSrc mu b=true). intro DOM.
    destruct INCR as [X [Y W]]; auto.
    unfold mu; rewrite DomSrc_marshal.
    unfold nu; rewrite replace_locals_DomSrc.
    unfold DomSrc; rewrite LOC; auto. }

assert (LOCNU_IN_DOMTGT:
  forall b, locBlocksTgt nu b=true -> DomTgt mu2 b=true).
  { intros b LOC. cut (DomTgt mu b=true). intro DOM.
    destruct INCR as [X [Y W]]; auto.
    unfold mu; rewrite DomTgt_marshal.
    unfold nu; rewrite replace_locals_DomTgt.
    unfold nu in LOC; rewrite replace_locals_locBlocksTgt in LOC.
    unfold DomTgt. rewrite LOC; auto. }

assert (NU_SEP: sm_inject_separated nu nu2 m tm)
  by (unfold nu; apply reestablish_sm_injsep in NUMU2_SEP; auto).

assert (NU2_WD: SM_wd nu2).
  { apply reestablish_wd; auto.
    solve[destruct NUMU2_SEP; auto].
    intros b; unfold nu; rewrite replace_locals_extBlocksTgt.
    intros EXT. cut (DomTgt mu b=true). intro DOM.
    destruct INCR as [X [Y W]]; auto.
    unfold mu; rewrite DomTgt_marshal.
    unfold nu; rewrite replace_locals_DomTgt.
    unfold DomTgt; rewrite EXT; rewrite orb_true_iff; auto. }

assert (NU2_VAL: sm_valid nu2 m' tm2)
  by (apply reestablish_sm_valid; auto).

assert (NU2_INJ: Mem.inject (as_inj nu2) m' tm2).
  { unfold nu2; rewrite reestablish_as_inj'; auto.
    unfold mu in INCR; destruct INCR as [X _].
    rewrite as_inj_marshal in X; auto.
    intros b LOC LOCOF; case_eq (as_inj mu2 b); auto.
    intros [b0 d0] ASINJ; elimtype False.
    destruct NUMU2_SEP as [X Y].
    cut (as_inj nu b = None). intro ASINJ'.
    destruct (X _ _ _ ASINJ' ASINJ).
    unfold DomSrc in H; rewrite LOC in H; inv H.
    unfold as_inj, join.
    assert (extern_of nu b = None) as ->; auto.
      generalize (disjoint_extern_local_Src NU_WD b).
      rewrite LOC; inversion 1; subst. congruence.
      case_eq (extern_of nu b); auto; intros [? ?] EXT.
      apply extern_DomRng in EXT; auto.
      destruct EXT as [W _]; rewrite H0 in W; congruence. }

assert (NU2_VINJ: val_inject (as_inj nu2) rv trv0)
  by (simpl in RVALINJ; unfold nu2; rewrite reestablish_as_inj; auto).

rename H2 into ATEXTSRC.

generalize (@eff_after_external _ _ _ _ _ _ _ _ _ _ _
  sim cd j c d m ef args tm sig targs ef sig INJ MATCH
  ATEXTSRC AT VALINJ''
  pubSrc' refl_equal
  pubTgt' refl_equal
  nu refl_equal nu2 rv m' trv0 tm2
  EINCR NU_SEP NU2_WD NU2_VAL NU2_INJ NU2_VINJ FORWARD TFWD2
  frgnSrc' refl_equal
  frgnTgt' refl_equal
  nu' refl_equal).

destruct 1 as [acd [ac [ad [AFT1 [AFT2 AMATCH]]]]]; auto.
apply unchanged_on_validblock with (V :=
  fun b ofs => REACH m (getBlocks args) b=false); auto.
intros b ofs BVAL [X Y].
unfold nu in Y; unfold pubSrc', pubTgt' in Y.
rewrite replace_locals_pubBlocksSrc in Y.
unfold nu in X; rewrite replace_locals_locBlocksSrc in X.
rewrite X in Y; simpl in Y.
apply REACH_mono' with (B2 := exportedSrc j args); auto.
solve[intros b'; unfold exportedSrc; intros ->; auto].

apply unchanged_on_validblock with (V :=
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
generalize (match_sm_wd sim _ _ _ _ _ _ MATCH); intros WD.
apply REACH_as_inj_REACH with (m2 := tm) (vals2 := targs) in HR''; auto.
destruct HR'' as [b' [d' [INJ'' HR'']]].
assert (b = b' /\ d0 = d') as [? ?].
  unfold nu in INJ0; rewrite HR', replace_locals_as_inj in INJ0.
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

edestruct eff_after_check1
  with (mu := j) (m1 := m) (m2 := tm) (vals1 := args) (vals2 := targs)
       (pubSrc' := pubSrc') (pubTgt' := pubTgt'); auto.

set (tr2' := Event.mk m m' args (Some rv) :: tr2).
set (ttr' := Event.mk tm tm2 targs (Some trv0) :: ttr).

exists acd, nu', (z',ttr',ad), tm2.
split; auto.
econstructor; eauto.

apply unchanged_on_validblock with (V :=
  fun b ofs => ~target_accessible mu m tm args b ofs); auto.
intros b ofs X Y.
unfold target_accessible; intros [VAL TA].
destruct TA as [b0 [d0 [FR [RC PERM]]]]; auto.
apply REACH_as_inj_REACH' with (m2 := tm) (vals2 := targs) (mu := j) in RC; auto.
destruct RC as [b2 [d2 [INJ' RR]]].
assert (b = b2).
  apply foreign_in_all in FR.
  unfold mu, nu in FR; rewrite as_inj_marshal, replace_locals_as_inj in FR.
  solve[rewrite FR in INJ'; inv INJ'; auto].
solve[subst; congruence].

instantiate (1 := x).
assert (VALINJ''' : val_list_inject (as_inj j) args targs).
  solve[apply forall_inject_val_list_inject; auto].
generalize (P_closed spec_closed ef x (sig_args sig) z PRE VALINJ''' INJ).
assert (z = tz) as -> by (inv TRMATCH; auto).
solve[auto].
generalize (Q_closed spec_closed ef x
  (sig_res sig) (Some rv) z' (Some trv0) POST RVALINJ INJ2).
solve[auto].

constructor. constructor.
destruct H0 as [VAL [INJ' VINJ]].
apply mk_match_event
  with (j := replace_locals j pubSrc' pubTgt')
       (j' := nu2); auto.
solve[apply extern_incr_as_inj; auto].
solve[inv TRMATCH; auto].
solve[rewrite H11 in AFT1; inv AFT1; auto]. }
Qed.

Lemma safe_match_target_step cd j c m d tm z tr :
  (forall n, safeN tr_source geS n (z,tr,c) m) ->
  match_state cd j c m d tm ->
  ~TraceSemantics.yielded target d ->
  exists c' m' d' tm' n tn,
    corestepN source geS n c m c' m'
    /\ corestepN target geT (S tn) d tm d' tm'
    /\ exists cd' j', match_state cd' j' c' m' d' tm'.
Proof.
set (my_P := fun (x: data) =>
  forall j c m d tm z tr,
  (forall n, safeN tr_source geS n (z,tr,c) m) ->
  match_state x j c m d tm ->
  ~TraceSemantics.yielded target d ->
  exists c' m' d' tm' n tn,
    corestepN source geS n c m c' m'
    /\ corestepN target geT (S tn) d tm d' tm'
    /\ exists cd' j', match_state cd' j' c' m' d' tm').
assert (my_well_founded_induction
     : (forall x, (forall y, ord y x -> my_P y) -> my_P x) ->
       forall a, my_P a)
  by (apply well_founded_induction; destruct sim; auto).
unfold my_P in my_well_founded_induction.
intros SAFE; revert cd j SAFE.
intros cd j; revert j c m d tm z tr.
apply my_well_founded_induction; auto.
intros. rename H0 into SAFE. rename H into IH.
destruct (TraceSemantics.yielded_dec source c).
exists c, m, d, tm, O, O; split; simpl; auto.
split; auto.
eapply yielded_src_tgt in y; eauto. contradiction.
solve[exists x, j; auto].
generalize (SAFE (S O)); simpl.
assert (TraceSemantics.halted source (z,tr,c) = None) as ->
  by (apply TraceSemantics.nyielded_nhalted in n; auto).
intros [[[z' tr'] c2] [m2 [STEP _]]].
inv STEP.
rename H11 into STEP.
generalize STEP as STEP'; intro.
eapply (core_diagram sim) in STEP; eauto.
destruct STEP as [d2 [tm2 [cd2 [mu2 [_ [_ [_ [MATCH2 [_ [_ STEP2]]]]]]]]]].
destruct STEP2.
destruct H0 as [n0 TSTEPN].
solve[exists c2, m2, d2, tm2, (S O), n0; split; simpl; eauto].
destruct H0 as [[n0 TSTEPN] ORD].
assert (SAFE': forall n,
  safeN (TraceSemantics.coopsem z_init source spec) geS n (z', tr', c2) m2).
  { intros n1; specialize (SAFE (S n1)).
    eapply safe_corestep_forward; eauto. apply tr_src_det.
    constructor; auto. }
destruct n0. inv TSTEPN.
generalize (IH _ ORD _ c2 m2 d2 tm2 _ _ SAFE' MATCH2 H2).
intros [c' [m' [d' [tm' [n' [tn' [A [B E]]]]]]]].
exists c', m', d', tm', (S n'), tn'; split; auto.
solve[exists c2, m2; split; auto].
solve[exists c2, m2, d2, tm2, (S O), n0; split; simpl; eauto].
eapply TraceSemantics.nyielded_natext in n; eauto.
solve[rewrite n in H9; congruence].
Qed.

Lemma safe_match_target_atext cd j c m d tm z tr ef sig args :
  (forall n, safeN tr_source geS n (z,tr,c) m) ->
  match_state cd j c m d tm ->
  at_external target d = Some (ef, sig, args) ->
  exists c' m' n,
    corestepN source geS n c m c' m'
    /\ TraceSemantics.yielded source c'
    /\ exists cd' j', match_state cd' j' c' m' d tm.
Proof.
set (my_P := fun (x: data) =>
  forall j c m,
  (forall n, safeN tr_source geS n (z,tr,c) m) ->
  match_state x j c m d tm ->
  at_external target d = Some (ef, sig, args) ->
  exists c' m' n,
    corestepN source geS n c m c' m'
    /\ TraceSemantics.yielded source c'
    /\ exists cd' j', match_state cd' j' c' m' d tm).
assert (my_well_founded_induction
     : (forall x, (forall y, ord y x -> my_P y) -> my_P x) ->
       forall a, my_P a)
  by (apply well_founded_induction; destruct sim; auto).
unfold my_P in my_well_founded_induction.
intros SAFE; revert cd j SAFE.
intros cd j; revert j c m.
apply my_well_founded_induction; auto.
intros. rename H0 into SAFE. rename H into IH.
destruct (TraceSemantics.yielded_dec source c).
exists c, m, O; split; simpl; auto.
split; auto.
solve[exists x, j; auto].
generalize (SAFE (S O)); simpl.
assert (TraceSemantics.halted source (z,tr,c) = None) as ->
  by (apply TraceSemantics.nyielded_nhalted in n; auto).
intros [[[z' tr'] c2] [m2 [STEP _]]].
inv STEP.
rename H11 into STEP.
generalize STEP as STEP'; intro.
eapply (core_diagram sim) in STEP; eauto.
destruct STEP as [d2 [tm2 [cd2 [mu2 [_ [_ [_ [MATCH2 [_ [_ STEP2]]]]]]]]]].
destruct STEP2.
destruct H0 as [n0 TSTEPN].
destruct TSTEPN as [? [? [TSTEP _]]].
apply corestep_not_at_external in TSTEP.
rewrite TSTEP in H2; congruence.
destruct H0 as [[n0 TSTEPN] ORD].
destruct n0. inv TSTEPN.
assert (SAFE2: forall n, safeN tr_source geS n (z',tr',c2) m2).
  { intros n1; specialize (SAFE (S n1)).
    eapply safe_corestep_forward in SAFE; eauto.  apply tr_src_det.
    constructor; auto. }
generalize (IH _ ORD _ _ _ SAFE2 MATCH2 H2).
intros [c' [m' [n0 [STEPN [SY MATCH']]]]].
exists c', m', (S n0).
split; auto.
exists c2, m2; split; auto.
destruct TSTEPN as [? [? [TSTEP _]]].
apply corestep_not_at_external in TSTEP.
rewrite TSTEP in H2; inv H2.
exists c, m, O.
split; auto.
simpl; eauto.
split.
left; exists ef0, sig0, args0; auto.
exists x, j; auto.
Qed.

(* Trace refinement: *)

Lemma trace_refinement z z' c d d' m tm tm' tr0 ttr0 ttr cd j tn :
  match_state cd j c m d tm ->
  match_trace tr0 ttr0 ->
  (forall n, safeN tr_source geS n (z,tr0,c) m) ->
  corestepN tr_target geT tn (z,ttr0,d) tm (z',ttr,d') tm' ->
  exists z'' c' m' tr n,
    corestepN tr_source geS n (z,tr0,c) m (z'',tr,c') m'
    /\ match_trace tr ttr.
Proof.
intros MATCH TMATCH SSAFE TSTEPN.
assert (TRMATCH: trace_match_state cd j (z,tr0,c) m (z,ttr0,d) tm)
  by (constructor; auto).
revert c d m tm z cd j tr0 ttr0 MATCH SSAFE TMATCH TSTEPN TRMATCH.
set (my_P := fun (x: nat) =>
   forall (c : C) (d : D) (m tm : mem) (z : Z) (cd : data)
     (j : SM_Injection) (tr0 ttr0 : list Event.t),
   match_state cd j c m d tm ->
   (forall n : nat,
    safeN (TraceSemantics.coopsem z_init source spec) geS n (z, tr0, c) m) ->
   match_trace tr0 ttr0 ->
   corestepN (TraceSemantics.coopsem z_init target spec) geT x
     (z, ttr0, d) tm (z', ttr, d') tm' ->
   trace_match_state cd j (z, tr0, c) m (z, ttr0, d) tm ->
   exists (z'' : Z) (c' : C) (m' : mem) (tr : list Event.t)
   (n : nat),
     corestepN (TraceSemantics.coopsem z_init source spec) geS n
       (z, tr0, c) m (z'', tr, c') m' /\ match_trace tr ttr).
assert (my_well_founded_induction
     : (forall x, (forall y, lt y x -> my_P y) -> my_P x) ->
       forall a, my_P a)
  by (apply well_founded_induction; apply lt_wf).
unfold my_P in my_well_founded_induction.
apply my_well_founded_induction; auto.
intros until ttr0; intros MATCH SSAFE TMATCH TSTEPN TRMATCH.
rename H into IHtn. destruct x.
solve[inv TSTEPN; exists z', c, m, tr0, O; split; try constructor; auto].
destruct TSTEPN as [d2 [tm2 [TSTEP TSTEPN]]].
generalize TSTEP as TSTEP'; intro; inv TSTEP.

{ (*target corestep*)
  rename H6 into TSTEP; rename c' into d2.
  assert (TNY: ~TraceSemantics.yielded target d).
    { intros [[ef [sig [args Y]]]|[rv Y]].
      apply corestep_not_at_external in TSTEP.
      rewrite TSTEP in Y; inv Y.
      apply corestep_not_halted in TSTEP.
      rewrite TSTEP in Y; inv Y. }
  eapply nyielded_tgt_src in TNY; eauto.
  generalize (safe_match_target_step SSAFE MATCH).
  intros [c2 [m2 [d2' [tm2' [n [tn0 [STEPN [TSTEPN' MATCH2]]]]]]]].
  solve[apply TraceSemantics.corestep_nyielded in TSTEP; auto].

  assert (SSAFE': forall n,
    safeN (TraceSemantics.coopsem z_init source spec) geS n (z, tr0, c2) m2).
    { intros n1; specialize (SSAFE (plus n1 (S n))).
      generalize tr_src_det. intro.
      eapply TraceSemantics.corestepN_CORESTEPN in STEPN; eauto.
      eapply safe_corestepN_forward in STEPN; eauto. }

  destruct MATCH2 as [cd2 [j2 MATCH2]].
  assert (TSTEPN'':
    corestepN tr_target geT (S x) (z,ttr0,d) tm (z',ttr,d') tm').
    { exists (z,ttr0,d2), tm2; split; auto. }
  case_eq (lt_dec tn0 (S x)). intros LT _.
  generalize (TraceSemantics.corestepN_splits_lt tgt_det TSTEPN' TSTEPN'' LT).
  intros [nx [ny [EQ [POS [A B]]]]].

  assert (LT': (ny < S x)%nat) by omega.
  destruct (IHtn ny LT' c2 _ _ _ _ _ _ _ _ MATCH2 SSAFE' TMATCH B)
    as [z'' [c' [m' [tr [n' [STEPN' MATCH']]]]]].
  solve[constructor; auto].
  exists z'', c', m', tr, (plus n n'); split; auto.
  rewrite corestepN_add.
  exists (z,tr0,c2), m2; split; auto.
  solve[apply TraceSemantics.corestepN_CORESTEPN; auto].
  intros NLT _. assert (GEQ: (S tn0 >= S x)%nat) by omega.
  generalize (TraceSemantics.corestepN_geq tgt_det TSTEPN' TSTEPN'' GEQ).
  intros [? ?]; subst z' ttr.
  exists z,c,m,tr0,O; split; auto.
  simpl; auto. }

{ (* target at external *)
  rename H2 into TATEXT; rename c' into d2.
  set (d2' := (z'0,Event.mk tm tm2 args (Some rv)::ttr0,d2)) in *.
  generalize (safe_match_target_atext SSAFE MATCH TATEXT).
  intros [c2 [m2 [n [STEPN [SY [cd2 [j2 MATCH2]]]]]]].
  assert (exists args, at_external source c2 = Some (ef,sig,args))
    as [args0 ATEXT].
    { destruct SY as [H|H].
      destruct H as [ef' [sig' [args' ATEXT]]].
      generalize ATEXT as ATEXT'; intro.
      eapply (core_at_external sim) in ATEXT; eauto.
      destruct ATEXT as [_ [? [? ATEXT'']]].
      rewrite ATEXT'' in TATEXT; inv TATEXT; exists args'; auto.
      destruct H as [rv' HALT].
      Arguments core_halted : default implicits.
      eapply core_halted in HALT; eauto.
      destruct HALT as [? [? [? THALT]]].
      generalize (@at_external_halted_excl _ _ _ target d).
      rewrite THALT. intros [W|W]; try congruence. }
  assert (SSAFE': forall n,
    safeN (TraceSemantics.coopsem z_init source spec) geS n (z, tr0, c2) m2).
    { intros n1; specialize (SSAFE (plus n1 (S n))).
      generalize tr_src_det. intro.
      eapply TraceSemantics.corestepN_CORESTEPN in STEPN; eauto.
      eapply safe_corestepN_forward in STEPN; eauto. }
  generalize SSAFE' as SSAFE''; intro.
  generalize (SSAFE' (S O)); simpl.
  assert (TraceSemantics.halted source (z,tr0,c2) = None) as ->.
    { generalize (@at_external_halted_excl _ _ _ source c2).
      rewrite ATEXT. intros [W|W]; try congruence.
      unfold TraceSemantics.halted; simpl; rewrite W; auto. }
  intros [c2' [m2' [STEP _]]].
  assert (trace_match_state cd2 j2 (z,tr0,c2) m2 (z,ttr0,d) tm)
    by (constructor; auto).
  generalize STEP as STEP'; intro.
  eapply extern_semantics_preservation in STEP; eauto.
  destruct STEP as [cd3 [j3 [[[z'' ttr'] d3] [tm3 [TSTEP'' TRMATCH']]]]].
  assert ((z'',ttr',d3) = d2' /\ tm2=tm3) as [EQ1 EQ2].
    { destruct (tr_tgt_det TSTEP' TSTEP'').
      subst d2'; subst tm2; inv H1; auto. }
  inversion EQ1. subst z'' ttr' d3.
  inversion EQ2. subst tm3.
  inv TRMATCH'. rename H15 into TMATCH'; rename H16 into MATCH'.
  set (c2' := (z'0,tr,c0)) in *.
  assert (SSAFE''': forall n,
    safeN (TraceSemantics.coopsem z_init source spec) geS n c2' m2').
    { intros n1; specialize (SSAFE' (S O)).
      assert (STEPN': corestepN tr_source geS (S O) (z,tr0,c2) m2 c2' m2').
        { exists c2', m2'; split; auto. simpl; auto. }
      eapply safe_corestepN_forward in STEPN'; eauto.
      apply tr_src_det. }
  set (ttr' := Event.mk tm tm2 args (Some rv) :: ttr0) in *.
  assert (LT: (x < S x)%nat) by omega.
  destruct (IHtn x LT c0 _ _ _ _ _ _ _ _ MATCH' SSAFE''' TMATCH' TSTEPN)
    as [z'' [c' [m' [tr' [n' [STEPN' MATCH'']]]]]].
  solve[constructor; auto].
  exists z'', c', m', tr', (plus (S n) n'); split; auto.
  rewrite corestepN_add.
  exists (z'0,tr,c0), m2'; split; auto.
  clear - STEPN STEP'.
  assert (STEPN': corestepN tr_source geS n (z,tr0,c) m (z,tr0,c2) m2)
    by (eapply TraceSemantics.corestepN_CORESTEPN; eauto).
  assert (S n = plus n 1) as -> by omega.
  rewrite corestepN_add.
  exists (z,tr0,c2), m2; split; auto.
  solve[simpl; eexists; eauto]. }
Qed.

Section corollary.

Import Event.

Definition injclosed (P : Event.t -> Prop) :=
  forall vals1 vals2 orv1 orv2 m1 m2 m1' m2' j j',
  P (Event.mk m1 m1' vals1 orv1) ->
  Mem.inject (as_inj j) m1 m2 ->
  val_list_inject (as_inj j) vals1 vals2 ->
  Mem.inject (as_inj j') m1' m2' ->
  oval_inject (as_inj j') orv1 orv2 ->
  P (Event.mk m2 m2' vals2 orv2).

Definition tracepred := list (Event.t -> Prop).

Fixpoint tracepred_injclosed (Ps : tracepred) :=
  match Ps with
    | nil => True
    | P :: Ps' => injclosed P /\ tracepred_injclosed Ps'
  end.

Fixpoint app_tracepred (Ps : tracepred) (tr : list Event.t) :=
  match Ps, tr with
    | P :: Ps', ev :: tr' => P ev /\ app_tracepred Ps' tr'
    | _, _ => True
  end.

Lemma app_match_trace (Ps : tracepred) tr tr' :
  tracepred_injclosed Ps ->
  match_trace tr tr' ->
  app_tracepred Ps tr ->
  app_tracepred Ps tr'.
Proof.
revert tr tr'; induction Ps; auto.
intros tr tr' [A B] E.
destruct tr; auto.
inv E; auto.
intros [G H].
destruct tr'; simpl; auto.
split.
inv E.
inv H3.
apply forall_inject_val_list_inject in H4.
unfold injclosed in A.
destruct t0, t1.
eapply A; eauto.
eapply IHPs; eauto.
inv E; auto.
Qed.

Lemma corollary c d m tm cd j Ps z :
  (* trace semantics source configuration <z,nil,c> is safe *)
  (forall n, safeN tr_source geS n (z,nil,c) m) ->

  (* matching configurations: <c,m> ~j <d,tm> *)
  match_state cd j c m d tm ->

  (* P closed under ~EVENT *)
  tracepred_injclosed Ps ->

  (* <c,m> --tr-->* <c',m'> /\ tr |- Ps *)
  (forall c' m' z' tr,
    corestep_star tr_source geS (z,nil,c) m (z',tr,c') m' ->
    app_tracepred Ps tr) ->

  (* \forall d' tm' tr'. <d,tm> --tr'-->* <d',tm'>  ==>  tr' |- Ps *)
  forall d' tm' z' tr',
    corestep_star tr_target geT (z,nil,d) tm (z',tr',d') tm' ->
    app_tracepred Ps tr'.
Proof.
intros SAFE MATCH CLOSED PSRC ? ? ? ? [n TSTEPN].
assert (TRMATCH: match_trace nil nil) by constructor.
eapply trace_refinement in MATCH; eauto.
destruct MATCH as [z'' [c' [m' [tr'' [n' [STEPN TRMATCH']]]]]].
eapply app_match_trace; eauto.
eapply PSRC; exists n'; eauto.
Qed.

(* Print Assumptions corollary.  *)

(* Section Variables: *)
(* C : Type *)
(* D : Type *)
(* F : Type *)
(* TF : Type *)
(* TV : Type *)
(* V : Type *)
(* Z : Type *)
(* entry_points : list (val * val * signature) *)
(* ext_spec_det : det spec *)
(* geS : Genv.t F V *)
(* geT : Genv.t TF TV *)
(* sim : SM_simulation_inject source target geS geT entry_points *)
(* source : EffectSem *)
(* spec : ext_spec Z *)
(* spec_closed : closed spec *)
(* spec_ok : forall (ef : external_function) (x : ext_spec_type spec ef) *)
(*             (tys : list typ) (args targs : list val)  *)
(*             (m : mem) (rty : option typ) (rv : option val)  *)
(*             (m' tm : mem) (z z' : Z) (j : SM_Injection), *)
(*           ext_spec_pre spec ef x tys args z m -> *)
(*           ext_spec_post spec ef x rty rv z' m' -> *)
(*           Mem.inject (as_inj j) m tm -> *)
(*           val_list_inject (restrict (as_inj j) (vis j)) args targs -> *)
(*           mem_forward m m' -> *)
(*           Mem.unchanged_on *)
(*             (fun (b : block) (_ : BinNums.Z) => *)
(*              REACH m (getBlocks args) b = false) m m' -> *)
(*           exists (j' : SM_Injection) (rv' : option val)  *)
(*           (tm' : mem), *)
(*             incr j j' /\ *)
(*             oval_inject (as_inj j') rv rv' /\ *)
(*             Mem.inject (as_inj j') m' tm' /\ *)
(*             sm_inject_separated j j' m tm /\ *)
(*             SM_wd j' /\ *)
(*             sm_valid j' m' tm' /\ *)
(*             mem_forward tm tm' /\ *)
(*             Mem.unchanged_on *)
(*               (fun (b : block) (ofs : BinNums.Z) => *)
(*                ~ target_accessible j m tm args b ofs) tm tm' *)
(* src_det : corestep_fun source *)
(* target : EffectSem *)
(* tgt_det : corestep_fun target *)
(* z_init : Z *)
(* Axioms: *)
(* REACH : mem -> (block -> bool) -> block -> bool *)
(* REACHAX : forall (m : mem) (B : block -> bool) (b : block), *)
(*           REACH m B b = true <-> *)
(*           (exists L : list (block * BinNums.Z), *)
(*              reach m (fun bb : block => B bb = true) L b) *)
(* functional_extensionality_dep : forall (A : Type) (B : A -> Type) *)
(*                                   (f g : forall x : A, B x), *)
(*                                 (forall x : A, f x = g x) -> f = g  *)

End corollary.

End open_semantics_preservation.