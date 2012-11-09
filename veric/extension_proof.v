Load loadpath.
Require Import msl.predicates_hered.
Require Import veric.sim veric.step_lemmas veric.base veric.expr 
               veric.extspec veric.juicy_extspec veric.extension.

Set Implicit Arguments.

Section SafetyMonotonicity.
 Variables 
  (G cT M D Zext: Type) 
  (CS: CoreSemantics G cT M D)
  (csig: ext_sig M Z) 
  (handled: ext_sig M Zext).

Lemma safety_monotonicity : forall ge n z c m,
  safeN CS (link csig handled) ge n z c m -> 
  safeN CS csig ge n z c m.
Proof. 
intros ge n; induction n; auto.
intros  ora c m; simpl; intros H1.
destruct (at_external CS c).
destruct p; destruct p.
destruct (safely_halted CS ge c).
auto.
destruct H1 as [x [H1 H2]].
if_tac in H1.
elimtype False; apply H1.
exists x; split; auto.
intros ret m' z' H3; destruct (H2 ret m' z' H3) as [c' [H4 H5]].
exists c'; split; auto.
destruct (safely_halted CS ge c); auto.
destruct H1 as [c' [m' [H1 H2]]].
exists c'; exists m'; split; auto.
Qed.

End SafetyMonotonicity.

Module ExtensionSoundness. Section ExtensionSoundness.
 Variables
  (G: Type) (** global environments *)
  (xT: Type) (** corestates of extended semantics *)
  (cT: nat -> Type) (** corestates of core semantics *)
  (M: Type) (** memories *)
  (D: Type) (** initialization data *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)

  (esem: CoreSemantics G xT M D) (** extended semantics *)
  (csem: forall i:nat, option (CoreSemantics G (cT i) M D)) (** a set of core semantics *)

  (csig: ext_sig M Z) (** client signature *)
  (esig: ext_sig M Zext) (** extension signature *)
  (handled: list AST.external_function) (** functions handled by this extension *)
  (E: Extension.Sig cT Zint esem csem csig esig handled). 

Import SafetyInterpolant.
Import TruePropCoercion.

Definition proj_zint := (proj_zint E). 
Coercion proj_zint : xT >-> Zint.

Definition proj_zext := (proj_zext E).
Coercion proj_zext : Z >-> Zext.

Notation ALL_SAFE := (all_safe E).
Notation PROJ_CORE := E.(Extension.proj_core).
Notation "zint \o zext" := (E.(Extension.zmult) zint zext) 
  (at level 66, left associativity). 
Notation ACTIVE := (E.(Extension.active)).
Notation RUNNABLE := (E.(Extension.runnable)).
Notation "'CORE' i 'is' ( CS , c ) 'in' s" := 
  (csem i = Some CS /\ PROJ_CORE i s = Some c)
  (at level 66, no associativity).
Notation core_exists := E.(Extension.core_exists).
Notation active_csem := E.(Extension.active_csem).
Notation active_proj_core := E.(Extension.active_proj_core).
Notation after_at_external_excl := E.(Extension.after_at_external_excl).
Notation notat_external_handled := E.(Extension.notat_external_handled).
Notation at_external_not_handled := E.(Extension.at_external_not_handled).
Notation ext_upd_at_external := E.(Extension.ext_upd_at_external).
Notation runnable_false := E.(Extension.runnable_false).

Program Definition ExtSound: EXTENSION_SOUNDNESS.Sig E.
Proof.
constructor.
inversion 1; subst; intros ge n; induction n.
intros s m z H1; simpl; auto.
intros s m z H1.
simpl; case_eq (at_external esem s).

(*CASE 1: at_external OUTER = Some _; i.e. _really_ at_external*) 
intros [[ef sig] args] AT_EXT.
destruct (at_external_halted_excl esem ge s) as [H2|H2].
rewrite AT_EXT in H2; congruence.
simpl; rewrite H2.
destruct (at_extern_call s ef sig args AT_EXT) as [CS [c [[H3 H4] H5]]].
generalize H1 as H1'; intro.
specialize (H1 (ACTIVE s) CS c H3 H4).
simpl in H1.
rewrite H5 in H1.
destruct (at_external_halted_excl CS ge c) as [H6|H6].
rewrite H6 in H5; congruence.
rewrite H6 in H1; clear H6.
destruct H1 as [x H1].
destruct H1 as [H7 H8].
generalize (Extension.esem_csem_linkable E); intros Hlink.
assert (H16: IN ef (DIFF csig handled)).
 apply in_diff.
 eapply Extension.at_external_csig; eauto.
 solve[eapply Extension.at_external_not_handled with (esem := esem); eauto].
specialize (Hlink ef 
  (ext_spec_pre esig ef) (ext_spec_post esig ef) 
  (ext_spec_pre csig ef) (ext_spec_post csig ef) H16).
destruct Hlink with (x' := x) 
 (tys := sig_args sig) (args := args) (m := m) (z := (s \o z)) 
 as [x' [H17 H18]]; auto.
exists x'.
erewrite at_external_not_handled; eauto.
split; auto.
rewrite Extension.zmult_proj in H17; auto.
intros ret m' z' POST.
destruct (H8 ret m' (s \o z')) as [c' [H10 H11]].
specialize (H18 (sig_res sig) ret m' (s \o z')).
rewrite Extension.zmult_proj in H18.
eapply H18 in POST; eauto.
specialize (at_extern_ret z s c m z' m' (sig_args sig) args (sig_res sig) ret c' CS
 ef sig x' (ext_spec_pre esig ef) (ext_spec_post esig ef)).
hnf in at_extern_ret.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
destruct at_extern_ret as [s' [H12 [H13 [H14 H15]]]].
exists s'.
split; auto.
rewrite H12.
eapply IHn.
intros j CSj cj CSEMJ PROJJ.
case_eq (eq_nat_dec (ACTIVE s) j).
(*i=j*)
intros Heq _. 
subst j.
rewrite CSEMJ in H14; inversion H14; rewrite H1 in *.
rewrite PROJJ in H15; inversion H15; rewrite H6 in *.
unfold proj_zint in H12.
unfold proj_zint.
rewrite <-H12.
eapply ext_upd_at_external in H13; eauto.
rewrite <-H13; auto.
(*i<>j*)
intros Hneq _.
specialize (at_extern_rest z s c m z' s' m' (sig_args sig) args (sig_res sig) ret c' CS
  ef x' sig (ext_spec_pre esig ef) (ext_spec_post esig ef)).
hnf in at_extern_rest.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
destruct (at_extern_rest j CSj cj Hneq) as [H19 H20].
rewrite <-H12.
eapply H20; eauto.
destruct H19 as [H21 H22]; auto.

(*CASE 2: at_external OUTER = None; i.e., inner corestep or handled function*)
intros H2.
case_eq (safely_halted esem ge s); auto.
case_eq (RUNNABLE ge s).
(*active thread i is runnable*)
intros RUN.
destruct (active_csem s) as [CS CSEM].
destruct (active_proj_core s) as [c PROJECT].
destruct (core_prog ge n (s \o z) s m c CS H1 RUN)
 as [c' [s' [m' [CORESTEP_C [CORESTEP_T ?]]]]]; auto.
generalize (core_pres ge n z s c m CS s' c' m' H1)
 as INV'; auto.
intros Hsafehalt.
exists s'; exists m'; split; [auto|].
eauto.

(*active thread not runnable*)
intros RUN.
destruct (active_csem s) as [CS CSEM].
destruct (active_proj_core s) as [c PROJECT].
destruct (handled_prog ge n z s m H1 RUN H2)
 as [[s' [m' [CORESTEP_T CORES_PRES]]]|[rv SAFELY_HALTED]].
2: intros CONTRA; rewrite CONTRA in SAFELY_HALTED; congruence.
exists s'; exists m'.
split; auto.
eapply IHn.
destruct (runnable_false ge s RUN CSEM PROJECT) 
 as [SAFELY_HALTED|[ef [sig [args AT_EXT]]]].

(*subcase A of no runnable thread: safely halted*)
intros j CSj cj CSEMj PROJECTj.
set (i := ACTIVE s) in *.
case_eq (eq_nat_dec i j).
(*i=j*)
intros Heq _.
subst j.
destruct (core_exists ge i s m s' m' CORESTEP_T PROJECTj)
 as [c0 PROJECT0].
rewrite PROJECT in PROJECT0; inversion PROJECT0; subst.
rewrite CSEM in CSEMj; inversion CSEMj; rename H4 into H3; rewrite <-H3 in *.
specialize (H1 i CS c0 CSEM PROJECT).
simpl in H1. 
destruct SAFELY_HALTED as [rv SAFELY_HALTED].
destruct (@at_external_halted_excl G (cT i) M D CS ge c0) as [H4|H4]; 
 [|congruence].
destruct n; simpl; auto.
destruct (safely_halted_halted ge s m s' m' i CS c0 rv) as [H6 H7]; auto.
rewrite H7 in PROJECTj; inversion PROJECTj; subst.
rewrite H4, SAFELY_HALTED; auto.
(*i<>j*)
intros Hneq _.
destruct (CORES_PRES i c CS) as [c' [[_ PROJ'] H5]]. 
split; auto.
specialize (handled_rest ge s m s' m' c CS).
hnf in handled_rest.
spec handled_rest; auto.
spec handled_rest; auto.
spec handled_rest; auto.
spec handled_rest; auto.
destruct (handled_rest j CSj cj Hneq) as [H6 H7].
eapply H7 with (z:=z); eauto.
eapply H1; eauto.
destruct (core_exists ge j s m s' m' CORESTEP_T PROJECTj)
 as [c0 PROJECT0].
specialize (H1 j CSj c0 CSEMj PROJECT0).
destruct H6 as [H8 H9].
split; auto.
rewrite H9 in PROJECT0; inversion PROJECT0; subst; auto.

(*subcase B of no runnable thread: at external INNER*)
intros j CSj cj CSEMj PROJECTj.
set (i := ACTIVE s) in *.
case_eq (eq_nat_dec i j).
(*i=j*)
intros Heq _.
subst j.
destruct (core_exists ge i s m s' m' CORESTEP_T PROJECTj)
 as [c0 PROJECT0].
rewrite PROJECT in PROJECT0; inversion PROJECT0; subst.
generalize CSEMj as CSEMj'; intro.
rewrite CSEM in CSEMj; inversion CSEMj; rename H4 into H3; rewrite <-H3 in *.
specialize (H1 i CS c0 CSEM PROJECT).
simpl in H1. 
rewrite AT_EXT in H1.
remember (safely_halted CS ge c0) as SAFELY_HALTED.
destruct SAFELY_HALTED. 
solve[destruct ef; elimtype False; auto].
destruct H1 as [x H1].
destruct H1 as [PRE POST].
specialize (handled_pres ge s z m c0 s' m' cj CS ef sig args
  (ext_spec_pre csig ef)
  (ext_spec_post csig ef) x).
(*rewrite Heq in handled_pres.*)
hnf in handled_pres.
spec handled_pres; auto.
spec handled_pres; auto.
spec handled_pres; auto. 
 eapply notat_external_handled; eauto.
spec handled_pres; auto.
spec handled_pres; auto.
spec handled_pres; auto.
spec handled_pres; auto.
destruct (CORES_PRES i c0 CS) as [c' H4]; [split; auto|].
destruct handled_pres as [[AT_EXT' [PRE' ACT']] | POST'].
(*pre-preserved case*)
destruct H4 as [[H4 H5] H6].
rewrite H5 in PROJECTj; inversion PROJECTj; subst.
specialize (H6 (ef,sig) args (ef,sig) args AT_EXT AT_EXT'); subst.
clear - PRE' POST AT_EXT' H4 H5 HeqSAFELY_HALTED H2 AT_EXT PROJECT CSEMj'.
destruct n; simpl; auto.
rewrite AT_EXT.
rewrite <-HeqSAFELY_HALTED.
exists x.
split; auto.
intros ret m'' s'' H8.
destruct (POST ret m'' s'' H8) as [c'' [H9 H10]].
exists c''; split; auto.
eapply safe_downward1; eauto.
(*post case*)
destruct H4 as [[H4 H5] H6].
rewrite H5 in PROJECTj; inversion PROJECTj; rename H7 into H1; rewrite <-H1 in *.
destruct POST' as [ret [AFTER_EXT POST']].
generalize (after_at_external_excl i c0 ret H4 AFTER_EXT); intros AT_EXT'.
clear - PRE POST POST' AT_EXT' AFTER_EXT H4 H5 H6 HeqSAFELY_HALTED.
destruct n; simpl; auto.
rewrite AT_EXT'.
case_eq (safely_halted CS ge c'); auto.
destruct (POST ret m' (s' \o z) POST') as [c'' [AFTER_EXT' SAFEN]].
unfold i in AFTER_EXT'.
rewrite AFTER_EXT in AFTER_EXT'; inversion AFTER_EXT'; subst.
simpl in SAFEN.
rewrite AT_EXT' in SAFEN.
intros SAFELY_HALTED; rewrite SAFELY_HALTED in SAFEN.
destruct SAFEN as [c3 [m'' [H7 H8]]].
exists c3; exists m''; split; auto.
(*i<>j: i.e., nonactive thread*)
intros Hneq _.
destruct (CORES_PRES i c CS) as [c' [[_ PROJ'] H5]]. 
split; auto.
specialize (handled_rest ge s m s' m' c CS).
hnf in handled_rest.
spec handled_rest; auto.
spec handled_rest; auto.
left; exists ef; exists sig; exists args; auto.
spec handled_rest; auto.
spec handled_rest; auto.
destruct (handled_rest j CSj cj Hneq) as [H6 H7].
eapply H7 with (z:=z); eauto.
eapply H1; eauto.
destruct (core_exists ge j s m s' m' CORESTEP_T PROJECTj)
 as [c0 PROJECT0].
specialize (H1 j CSj c0 CSEMj PROJECT0).
destruct H6 as [H8 H9].
split; auto.
rewrite H9 in PROJECT0; inversion PROJECT0; subst; auto.
Qed.

End ExtensionSoundness. End ExtensionSoundness.

Section CoreCompat.
Variables (G xT M D Z Zint Zext: Type) (cT: nat -> Type)
  (esem: CoreSemantics G xT M D) 
  (csem: forall i:nat, option (CoreSemantics G (cT i) M D))
  (csig: ext_sig M Z)
  (esig: ext_sig M Zext)
  (handled: list AST.external_function)
  (E: Extension.Sig cT Zint esem csem csig esig handled).

Import Extension.

Inductive core_compat: Type := CoreCompat: forall
  (*when the active thread is runnable, a step in the extended semantics can be tracked 
     back to a corestep of the active thread*)
  (runnable_corestep: forall ge s m s' m' c CS,
    runnable E ge s=true -> 
    csem (active E s) = Some CS -> proj_core E (active E s) s = Some c -> 
    corestep esem ge s m s' m' -> 
    exists c', corestep CS ge c m c' m' /\ proj_core E (active E s) s' = Some c') 

  (*after a corestep of the active inner core, the active thread's new corestate
     is appropriately injected into the extended state*)
  (corestep_pres: forall ge s (c: cT (active E s)) m c' s' m' CS,
    csem (active E s) = Some CS -> proj_core E (active E s) s = Some c -> 
    corestep CS ge c m c' m' -> corestep esem ge s m s' m' -> 
    (active E s = active E s' /\ proj_core E (active E s) s' = Some c'))

  (*a corestep of the currently active core forces a corestep of the extended semantics*)
  (corestep_prog: forall ge s (c: cT (active E s)) m c' m' CS,
    csem (active E s) = Some CS ->  proj_core E (active E s) s = Some c -> 
    corestep CS ge c m c' m' -> 
    exists s', corestep esem ge s m s' m')

  (*other cores remain unchanged after coresteps of the active core*)
  (corestep_others1: forall ge s s' (c: cT (active E s')) m c' m' CS,
    csem (active E s') = Some CS -> proj_core E (active E s') s' = Some c' -> 
    corestep CS ge c m c' m' -> corestep esem ge s m s' m' -> 
    forall j, (active E s)<>j -> proj_core E j s = proj_core E j s')

  (corestep_others2: forall ge s c m s' c' m' CS n,
    csem (active E s) = Some CS -> proj_core E (active E s) s = Some c -> 
    corestepN CS ge n c m c' m' -> corestepN esem ge n s m s' m' -> 
    forall j, (active E s)<>j -> proj_core E j s = proj_core E j s')

  (after_ext_pres: forall s (c: cT (active E s)) c' s' CS retv,
    csem (active E s) = Some CS -> proj_core E (active E s) s = Some c -> 
    after_external CS retv c = Some c' -> 
    after_external esem retv s = Some s' -> 
    active E s=active E s')

  (after_ext_prog: forall s (c: cT (active E s)) c' CS retv,
    csem (active E s) = Some CS -> proj_core E (active E s) s = Some c -> 
    after_external CS retv c = Some c' -> 
    exists s', after_external esem retv s = Some s' /\
      proj_core E (active E s) s' = Some c')

  (after_ext_others: forall s s' retv,
    after_external esem retv s = Some s' -> 
    forall j, (active E s)<>j -> proj_core E j s = proj_core E j s')

  (* REPEATED HERE TO GET AROUND A BUG IN PROGRAM: 
     HYP (1) NOT GENERATED WHEN PROVING OBLIGATION
     if the extended machine is at external, then the active thread is at
     external (an extension only implements external functions, it doesn't
     introduce them)*)
  (at_extern_call: forall s ef sig args,
    (*1*)at_external esem s = Some (ef, sig, args) -> 
    exists CS, exists c, 
      csem (active E s) = Some CS /\ proj_core E (active E s) s = Some c /\
      at_external CS c = Some (ef, sig, args)),
  core_compat.

Variable Hcore_compat: core_compat.

Lemma corestep_step: 
  forall ge s (c: cT (active E s)) m c' m' CS,
  csem (active E s) = Some CS -> 
  proj_core E (active E s) s = Some c -> 
  corestep CS ge c m c' m' -> 
  exists s', corestep esem ge s m s' m' /\
    active E s = active E s' /\ proj_core E (active E s) s' = Some c'.
Proof.
intros.
inv Hcore_compat.
generalize H1 as H1'; intro.
eapply corestep_prog in H1; eauto.
destruct H1 as [s' H1].
exists s'.
split; auto. 
eapply corestep_pres; eauto.
Qed.

Lemma corestep_stepN: 
  forall n ge s (c: cT (active E s)) m c' m' CS,
  csem (active E s) = Some CS -> 
  proj_core E (active E s) s = Some c -> 
  corestepN CS ge n c m c' m' -> 
  exists s', corestepN esem ge n s m s' m' /\ 
    active E s = active E s' /\ proj_core E (active E s) s' = Some c'.
Proof.
inv Hcore_compat.
generalize corestep_step; intro H1.
intros n ge.
induction n; auto.
intros.
inv H2.
simpl.
exists s.
split; auto.
intros.
simpl in H2.
destruct H2 as [c2 [m2 [H5 H6]]].
eapply H1 in H5; eauto.
destruct H5 as [s2 [H5 [H7 H9]]].
forget (active E s) as i.
subst i.
destruct (IHn s2 c2 m2 c' m' CS) as [s' [H10 [H11 H13]]]; auto.
exists s'.
split3.
simpl.
exists s2; exists m2; split; auto.
auto.
auto.
Qed.

Lemma corestep_step_star: 
  forall ge s (c: cT (active E s)) m c' m' CS,
  csem (active E s) = Some CS -> 
  proj_core E (active E s) s = Some c -> 
  corestep_star CS ge c m c' m' -> 
  exists s', corestep_star esem ge s m s' m' /\ 
    active E s = active E s' /\ proj_core E (active E s) s' = Some c'.
Proof.
intros.
destruct H1 as [n H1].
eapply corestep_stepN in H1; eauto.
destruct H1 as [s' [H1 [H2 H4]]].
exists s'.
split3; auto.
exists n; auto.
Qed.

Lemma corestep_step_plus: 
  forall ge s (c: cT (active E s)) m c' m' CS,
  csem (active E s) = Some CS -> 
  proj_core E (active E s) s = Some c -> 
  corestep_plus CS ge c m c' m' -> 
  exists s', corestep_plus esem ge s m s' m' /\ 
    active E s = active E s' /\ proj_core E (active E s) s' = Some c'.
Proof.
intros.
destruct H1 as [n H1].
eapply corestep_stepN in H1; eauto.
destruct H1 as [s' [H1 [H2 H4]]].
exists s'.
split3; auto.
exists n; auto.
Qed.

End CoreCompat.
    
Section CompilableExtension.
Variables (fT: forall X:Type, Type) (cT dT D1 D2 Z Zint Zext: Type)
  (esem: forall (T: Type) (D: Type) (CS: CompcertCoreSem genv T D), 
    CompcertCoreSem genv (fT T) D) 
  (source: CompcertCoreSem genv cT D1) (target: CompcertCoreSem genv dT D2)
  (csig: ext_sig mem Z) (esig: ext_sig mem Zext) (handled: list AST.external_function).

Notation PROJ_CORE := (Extension.proj_core).
Infix "\o" := (Extension.zmult) (at level 66, left associativity). 
Notation ACTIVE := (Extension.active).
Notation RUNNABLE := (Extension.runnable).
Notation "'CORE' i 'is' ( CS , c ) 'in' s" := 
  (csem i = Some CS /\ PROJ_CORE i s = Some c)
  (at level 66, no associativity, only parsing).
Notation core_exists := (Extension.core_exists).
Notation active_csem := (Extension.active_csem).
Notation active_proj_core := (Extension.active_proj_core).
Notation after_at_external_excl := (Extension.after_at_external_excl).
Notation notat_external_handled := (Extension.notat_external_handled).
Notation at_external_not_handled := (Extension.at_external_not_handled).
Notation ext_upd_at_external := (Extension.ext_upd_at_external).
Notation runnable_false := (Extension.runnable_false).

Let xT := fT cT.
Let yT := fT dT.

Definition cores (aT:Type) (D: Type) (CS: CompcertCoreSem genv aT D) :=
  fun i:nat => Some (csem CS).

Variable (E1: Extension.Sig (fun _:nat => cT) Zint 
  (esem source) (cores source) csig esig handled).
Variable (E2: Extension.Sig (fun _:nat => dT) Zint 
  (esem target) (cores target) csig esig handled).
Variables (ge: genv) (entry_points: list (val*val*signature)).

Import Sim_inj.

Variable (core_simulation: Forward_simulation_inject D1 D2 source target ge ge entry_points).

Definition match_states (cd: core_data core_simulation) (j: meminj) (s1: xT) m1 (s2: yT) m2 :=
  ACTIVE E1 s1=ACTIVE E2 s2 /\
  RUNNABLE E1 ge s1=RUNNABLE E2 ge s2 /\
  forall i c1, PROJ_CORE E1 i s1 = Some c1 -> 
    exists c2, PROJ_CORE E2 i s2 = Some c2 /\ 
      match_state core_simulation cd j c1 m1 c2 m2.

Inductive compilable_extension: Type := CompilableExtension: forall 
  (safely_halted_match: forall cd j c1 c2 m1 m1' m2 rv s1 s2 s1',
    match_states cd j s1 m1 s2 m2 -> 
    PROJ_CORE E1 (ACTIVE E1 s1) s1 = Some c1 -> 
    PROJ_CORE E2 (ACTIVE E2 s2) s2 = Some c2 -> 
    safely_halted source ge c1 = Some rv -> 
    corestep (esem source) ge s1 m1 s1' m1' ->  
    safely_halted target ge c2 = Some rv /\
    exists s2', exists m2', exists cd', exists j', 
      inject_incr j j' /\
      Events.inject_separated j j' m1 m2 /\
      corestep (esem target) ge s2 m2 s2' m2' /\
      match_states cd' j' s1' m1' s2' m2')

  (match_others: forall cd cd' j j' s1 c1 m1 c1' m1' s2 c2 m2 c2' m2' d1 d2 i n,
    PROJ_CORE E1 (ACTIVE E1 s1) s1 = Some c1 -> 
    PROJ_CORE E2 (ACTIVE E2 s2) s2 = Some c2 -> 
    PROJ_CORE E1 i s1 = Some d1 -> 
    PROJ_CORE E2 i s2 = Some d2 -> 
    ACTIVE E1 s1 <> i -> 
    match_states cd j s1 m1 s2 m2 -> 
    inject_incr j j' -> 
    Events.inject_separated j j' m1 m2 -> 
    corestep source ge c1 m1 c1' m1' -> 
    corestepN target ge n c2 m2 c2' m2' -> 
    match_state core_simulation cd' j' c1' m1' c2' m2' -> 
    match_state core_simulation cd' j' d1 m1' d2 m2')

  (corestep_runnable: forall s1 c1 m1 c1' m1' s1' s2 c2 m2 c2' m2' s2' n,
    PROJ_CORE E1 (ACTIVE E1 s1) s1 = Some c1 -> 
    PROJ_CORE E2 (ACTIVE E2 s2) s2 = Some c2 -> 
    RUNNABLE E1 ge s1=RUNNABLE E2 ge s2 -> 
    corestep source ge c1 m1 c1' m1' -> 
    corestepN target ge n c2 m2 c2' m2' -> 
    corestep (esem source) ge s1 m1 s1' m1' -> 
    corestepN (esem target) ge n s2 m2 s2' m2' -> 
    RUNNABLE E1 ge s1'=RUNNABLE E2 ge s2')

  (extension_diagram: forall c1 s1 m1 s1' m1' c2 s2 m2 ef sig args1 args2 cd j,
    ACTIVE E1 s1 = ACTIVE E2 s2 -> 
    RUNNABLE E1 ge s1=false -> RUNNABLE E2 ge s2=false -> 
    PROJ_CORE E1 (ACTIVE E1 s1) s1 = Some c1 -> 
    PROJ_CORE E2 (ACTIVE E2 s2) s2 = Some c2 -> 
    at_external source c1 = Some (ef, sig, args1) -> 
    at_external target c2 = Some (ef, sig, args2) -> 
    match_states cd j s1 m1 s2 m2 -> 
    Mem.inject j m1 m2 -> 
    Events.meminj_preserves_globals ge j -> 
    Forall2 (val_inject j) args1 args2 -> 
    Forall2 Val.has_type args2 (sig_args sig) -> 
    corestep (esem source) ge s1 m1 s1' m1' -> 
    exists s2', exists m2', exists cd', exists j',
      inject_incr j j' /\
      Events.inject_separated j j' m1 m2 /\
      match_states cd' j' s1' m1' s2' m2' /\
      corestep (esem target) ge s2 m2 s2' m2')

  (at_external_diagram: forall c1 s1 m1 c2 s2 m2 ef sig args1 args2 cd j,
    ACTIVE E1 s1=ACTIVE E2 s2 -> 
    RUNNABLE E1 ge s1=RUNNABLE E2 ge s2 -> 
    PROJ_CORE E1 (ACTIVE E1 s1) s1 = Some c1 -> 
    PROJ_CORE E2 (ACTIVE E1 s1) s2 = Some c2 -> 
    at_external (esem source) s1 = Some (ef, sig, args1) -> 
    at_external source c1 = Some (ef, sig, args1) -> 
    match_state core_simulation cd j c1 m1 c2 m2 -> 
    Mem.inject j m1 m2 -> 
    Events.meminj_preserves_globals ge j -> 
    Forall2 (val_inject j) args1 args2 -> 
    Forall2 Val.has_type args2 (sig_args sig) -> 
    at_external target c2 = Some (ef, sig, args2) -> 
    at_external (esem target) s2 = Some (ef, sig, args2))

  (after_external_diagram: 
    forall d1 s1 m1 d2 s2 m2 s1' m1' s2' m2' ef sig args1 retv1 retv2 cd j cd' j' i,
    match_state core_simulation cd j d1 m1 d2 m2 -> 
    at_external (esem source) s1 = Some (ef, sig, args1) -> 
    Events.meminj_preserves_globals ge j -> 
    inject_incr j j' -> 
    Events.inject_separated j j' m1 m2 -> 
    Mem.inject j' m1' m2' -> 
    val_inject j' retv1 retv2 -> 
    mem_forward m1 m1' -> 
    Events.mem_unchanged_on (Events.loc_unmapped j) m1 m1' -> 
    mem_forward m2 m2' -> 
    Events.mem_unchanged_on (Events.loc_out_of_reach j m1) m2 m2' -> 
    Val.has_type retv2 (proj_sig_res sig) -> 
    after_external (esem source) (Some retv1) s1 = Some s1' -> 
    after_external (esem target) (Some retv2) s2 = Some s2' -> 
    PROJ_CORE E1 i s1' = Some d1 -> 
    PROJ_CORE E2 i s2' = Some d2 -> 
    ACTIVE E1 s1 <> i -> 
    match_state core_simulation cd' j' d1 m1' d2 m2')

  (after_external_runnable: forall ge s1 m1 s2 m2 retv1 retv2 s1' s2' cd j,
    RUNNABLE E1 ge s1=RUNNABLE E2 ge s2 -> 
    match_states cd j s1 m1 s2 m2 -> 
    after_external (esem source) retv1 s1 = Some s1' -> 
    after_external (esem target) retv2 s2 = Some s2' ->     
    RUNNABLE E1 ge s1'=RUNNABLE E2 ge s2')

  (make_initial_core_diagram: forall ge v1 vals1 s1 m1 v2 vals2 m2 j sig,
    make_initial_core (esem source) ge v1 vals1 = Some s1 -> 
    Mem.inject j m1 m2 -> 
    Forall2 (val_inject j) vals1 vals2 -> 
    Forall2 Val.has_type vals2 (sig_args sig) -> 
    exists cd, exists s2, 
      make_initial_core (esem target) ge v2 vals2 = Some s2 /\
      match_states cd j s1 m1 s2 m2),
  compilable_extension.

Variables (esig_compilable: compilable_extension)
  (core_compat1: core_compat E1)
  (core_compat2: core_compat E2).

Program Definition extended_simulation: 
  Forward_simulation_inject D1 D2 (esem source) (esem target) ge ge entry_points :=
      Build_Forward_simulation_inject 
      (core_data core_simulation) 
      match_states 
      (core_ord core_simulation)
      _ _ _ _ _ _.
Next Obligation. apply (core_ord_wf core_simulation). Qed.
Next Obligation. 
rename H0 into MATCH.
generalize MATCH as MATCH'; intro.
destruct MATCH as [ACT [RUN MATCH_CORES]].
rename H into STEP.
case_eq (RUNNABLE E1 ge st1).

(*Case 1: runnable thread, appeal to core diagram for cores*)
intros RUN1.
assert (RUN2: RUNNABLE E2 ge st2 = true) by (rewrite <-RUN; auto).
destruct (active_proj_core E1 st1) as [c1 PROJ1].
assert (exists c1', corestep source ge c1 m1 c1' m1') as [c1' STEP1].
 inv esig_compilable.
 inv core_compat1.
 specialize (runnable_corestep ge st1 m1 st1' m1' c1 source).
 destruct runnable_corestep as [c1' [H3 H4]]; auto.
 solve[exists c1'; auto].
assert (PROJ1': PROJ_CORE E1 (ACTIVE E1 st1') st1' = Some c1').
 inv core_compat1.
 specialize (corestep_pres ge st1 c1 m1 c1' st1' m1' source).
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 destruct corestep_pres; auto.
 solve[rewrite <-H; auto].
assert (ACT1': ACTIVE E1 st1 = ACTIVE E1 st1').
 inv core_compat1.
 specialize (corestep_pres ge st1 c1 m1 c1' st1' m1' source).
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 spec corestep_pres; auto.
 solve[destruct corestep_pres; auto].
generalize (core_diagram core_simulation) as DIAG; intro.
destruct (MATCH_CORES (ACTIVE E1 st1) c1 PROJ1) as [c2 [PROJ2 MATCH12]].
specialize (DIAG c1 m1 c1' m1' STEP1 cd c2 j m2 MATCH12).
destruct DIAG as [c2' [m2' [cd' [j' [INJ_INCR [INJ_SEP [MATCH12' STEP2]]]]]]].
destruct STEP2 as [STEP2|STEP2].

(*corestep_plus case*)
destruct STEP2 as [n STEP2].
generalize (corestep_stepN core_compat2) as CSTEPN; intro.
specialize (CSTEPN (S n) ge st2 c2 m2 c2' m2' target).
spec CSTEPN; auto.
spec CSTEPN; auto. rewrite <-ACT; auto.
spec CSTEPN; auto.
destruct CSTEPN as [st2' [ESEM2 [ACT2' PROJ2']]].
exists st2'; exists m2'; exists cd'; exists j'.
split3; auto.
split; auto.
 (*Subgoal: match_states*)
 hnf.
 split.
 rewrite <-ACT1', <-ACT2'; auto.
 split.
 inv esig_compilable.
 specialize (corestep_runnable st1 c1 m1 c1' m1' st1' st2 c2 m2 c2' m2' st2' (S n)).
 spec corestep_runnable; auto.
 spec corestep_runnable; auto. rewrite <-ACT; auto.
 
  intros i _c _PROJ1'.
  case_eq (eq_nat_dec (ACTIVE E1 st1) i).
  
  (*ACTIVE E1 st1 = i*)
  intros EQ _. 
  rewrite <-EQ in *; clear EQ.
  exists c2'.
  rewrite ACT, ACT2'; auto.
  rewrite <-ACT1' in PROJ1'.
  rewrite PROJ1' in _PROJ1'.
  inv _PROJ1'.
  rewrite <-ACT2'.
  solve[split; auto].

  (*ACTIVE E1 st1 <> i*)
  intros NEQ _.
  assert (_PROJ1: PROJ_CORE E1 i st1 = Some _c). 
   inv core_compat1.
   specialize (corestep_others1 ge st1 st1' c1 m1 c1' m1' source).
   spec corestep_others1; auto.
   spec corestep_others1; auto. 
   spec corestep_others1; auto.
   spec corestep_others1; auto.
   specialize (corestep_others1 i NEQ).
   solve[rewrite corestep_others1; auto].
  assert (exists _d, PROJ_CORE E2 i st2 = Some _d) as [_d _PROJ2].
   destruct (MATCH_CORES i _c _PROJ1) as [_d [_PROJ2 _MATCH12]].
   solve[exists _d; auto].
  assert (_PROJ2': PROJ_CORE E2 i st2' = Some _d). 
   inv core_compat2.
   specialize (corestep_others2 ge st2 c2 m2 st2' c2' m2' target (S n)).
   spec corestep_others2; auto.
   spec corestep_others2; auto. rewrite <-ACT; auto.
   spec corestep_others2; auto.
   spec corestep_others2; auto.
   rewrite ACT in NEQ.
   specialize (corestep_others2 i NEQ).
   solve[rewrite <-corestep_others2; auto].
  exists _d; split; auto.
  inv esig_compilable.
  specialize (match_others cd cd' j j' st1 c1 m1 c1' m1' st2 c2 m2 c2' m2' _c _d i (S n)).
  spec match_others; auto.
  solve[spec match_others; auto; rewrite <-ACT; auto].
  solve[left; exists n; auto].

(*corestep_star case*)
destruct STEP2 as [[n STEP2] ORD].
generalize (corestep_stepN core_compat2) as CSTEPN; intro.
specialize (CSTEPN n ge st2 c2 m2 c2' m2' target).
spec CSTEPN; auto.
spec CSTEPN; auto. rewrite <-ACT; auto.
spec CSTEPN; auto.
destruct CSTEPN as [st2' [ESEM2 [ACT2' PROJ2']]].
exists st2'; exists m2'; exists cd'; exists j'.
split3; auto.
split; auto.
 (*Subgoal: match_states*)
 hnf.
 split.
 rewrite <-ACT1', <-ACT2'; auto.
 split.
 inv esig_compilable.
 specialize (corestep_runnable st1 c1 m1 c1' m1' st1' st2 c2 m2 c2' m2' st2' n).
 spec corestep_runnable; auto.
 spec corestep_runnable; auto. rewrite <-ACT; auto.
 
  intros i _c _PROJ1'.
  case_eq (eq_nat_dec (ACTIVE E1 st1) i).
  
  (*ACTIVE E1 st1 = i*)
  intros EQ _. 
  rewrite <-EQ in *; clear EQ.
  exists c2'.
  rewrite ACT, ACT2'; auto.
  rewrite <-ACT1' in PROJ1'.
  rewrite PROJ1' in _PROJ1'.
  inv _PROJ1'.
  rewrite <-ACT2'.
  solve[split; auto].

  (*ACTIVE E1 st1 <> i*)
  intros NEQ _.
  assert (_PROJ1: PROJ_CORE E1 i st1 = Some _c). 
   inv core_compat1.
   specialize (corestep_others1 ge st1 st1' c1 m1 c1' m1' source).
   spec corestep_others1; auto.
   spec corestep_others1; auto. 
   spec corestep_others1; auto.
   spec corestep_others1; auto.
   specialize (corestep_others1 i NEQ).
   solve[rewrite corestep_others1; auto].
  assert (exists _d, PROJ_CORE E2 i st2 = Some _d) as [_d _PROJ2].
   destruct (MATCH_CORES i _c _PROJ1) as [_d [_PROJ2 _MATCH12]].
   solve[exists _d; auto].
  assert (_PROJ2': PROJ_CORE E2 i st2' = Some _d). 
   inv core_compat2.
   specialize (corestep_others2 ge st2 c2 m2 st2' c2' m2' target n).
   spec corestep_others2; auto.
   spec corestep_others2; auto. rewrite <-ACT; auto.
   spec corestep_others2; auto.
   spec corestep_others2; auto.
   rewrite ACT in NEQ.
   specialize (corestep_others2 i NEQ).
   solve[rewrite <-corestep_others2; auto].
  exists _d; split; auto.
  inv esig_compilable.
  specialize (match_others cd cd' j j' st1 c1 m1 c1' m1' st2 c2 m2 c2' m2' _c _d i n).
  spec match_others; auto.
  solve[spec match_others; auto; rewrite <-ACT; auto].
  solve[right; split; [exists n; auto|auto]].

(*runnable = false*)
intros RUN1.
destruct (active_proj_core E1) with (s := st1) as [c1 PROJ1].
generalize PROJ1 as _PROJ1; intro.
destruct (active_csem E1) with (s := st1) as [CS ACT1]; inv ACT1.
apply (runnable_false E1) with (c := c1) (CS := source) (ge := ge) in PROJ1; auto.
destruct PROJ1 as [[rv HALT]|[ef [sig [args AT_EXT]]]].

(*active thread is safely halted*)
specialize (MATCH_CORES (ACTIVE E1 st1) c1 _PROJ1).
destruct MATCH_CORES as [c2 [PROJ2 MATCH12]].
destruct (core_halted core_simulation cd j c1 m1 c2 m2 rv MATCH12 HALT) 
 as [SAFE2 INJ].
inv esig_compilable.
eapply safely_halted_match with (m1' := m1') in MATCH'; eauto.
2: rewrite <-ACT, PROJ2; eauto.
destruct MATCH' as [H7 [st2' [m2' [cd' [j' [INJ_INCR [SEP [STEP2' MATCH12']]]]]]]].
exists st2'; exists m2'; exists cd'; exists j'.
split3; auto; split; auto.
solve[left; exists 0%nat; eexists; eexists; split; simpl; eauto].

(*active thread is at_external*)
destruct (MATCH_CORES (ACTIVE E1 st1) c1 _PROJ1) as [c2 [PROJ2 MATCH12]].
destruct (core_at_external core_simulation cd j c1 m1 c2 m2 ef args sig MATCH12 AT_EXT)
 as [H6 [H7 [vals2 [H8 [H9 H10]]]]].
inv esig_compilable. 
edestruct extension_diagram as [s2' H11]; eauto.
rewrite <-ACT; auto.
destruct H11 as [m2' [cd' [j' [? [? [? ?]]]]]].
exists s2'; exists m2'; exists cd'; exists j'.
split3; auto; split; auto.
solve[left; exists 0%nat; simpl; eexists; eexists; split; simpl; eauto].
Qed.

(*we punt in the make_initial_core case of the simulation proof; to do more requires 
   assuming too much about the structure of the extension w/r/t its inner cores*)
Next Obligation. 
inv esig_compilable.
eapply make_initial_core_diagram; eauto.
(*rename H0 into INIT.
rename H1 into INJ.
rename H2 into VALINJ.
rename H3 into TYPE.
inv core_compat1.
destruct (Extension.active_csem E1 c1) as [CS CORES].
destruct (Extension.active_proj_core E1 c1) as [_c1 PROJ1].
destruct (make_init1 ge c1 v1 vals1 (ACTIVE E1 c1) CS CORES INIT)
 as [_c1' [INIT' PROJ1']].
rewrite PROJ1' in PROJ1.
inv PROJ1.
unfold cores in CORES.
inv CORES.
generalize (core_initial core_simulation v1 v2 sig H vals1 _c1 m1 j vals2 m2 INIT');
 intro MATCH.
spec MATCH; auto.
spec MATCH; auto.
spec MATCH; auto.
destruct MATCH  as [cd [_c2 [? ?]]].
exists cd.
clear make_init2.
inv core_compat2.
specialize (make_init2 ge _c2 v2 vals2 O target).
spec make_init2; auto.
spec make_init2; auto.
destruct make_init2 as [c2 [INIT2 MATCH2]].
exists c2.
split; auto.*)
Qed.

Next Obligation. 
rename H into MATCH; hnf in MATCH.
destruct MATCH as [ACT [RUN MATCH_CORES]].
Admitted. (*TODO*)

Next Obligation. 
rename H into MATCH.
hnf in MATCH.
destruct MATCH as [ACT [RUN MATCH_CORES]].
destruct (active_proj_core E1) with (s := st1) as [c1 PROJ1].
assert (AT_EXT1: at_external source c1 = Some (e, ef_sig, vals1)).
 inv core_compat1.
 edestruct (at_extern_call) as [CS [c [CORES [PROJ AT_EXT]]]]; eauto.
 rewrite PROJ in PROJ1; inv PROJ1.
 solve[unfold cores in CORES; inv CORES; auto].
destruct (MATCH_CORES (ACTIVE E1 st1) c1 PROJ1) as [c2 [PROJ2 MATCH12]].
destruct (core_at_external core_simulation cd j c1 m1 c2 m2 e vals1 ef_sig MATCH12 AT_EXT1)
 as [INJ [GLOBS [vals2 [VALINJ [TYPE AT_EXT2]]]]].
split3; auto.
exists vals2.
split3; auto.
inv esig_compilable.
specialize (at_external_diagram c1 st1 m1 c2 st2 m2 e ef_sig vals1 vals2 cd j).
spec at_external_diagram; auto.
Qed.

Next Obligation. 
rename H0 into MATCH.
generalize MATCH as MATCH'; intro.
hnf in MATCH.
destruct MATCH as [ACT [RUN MATCH_CORES]].
generalize MATCH_CORES as MATCH_CORES'; intro.
destruct (active_proj_core E1) with (s := st1) as [c1 PROJ1].
assert (AT_EXT1: at_external source c1 = Some (e, ef_sig, vals1)).
 inv core_compat1.
 edestruct (at_extern_call) as [CS [c [CORES [PROJ AT_EXT]]]]; eauto.
 rewrite PROJ in PROJ1; inv PROJ1.
 solve[unfold cores in CORES; inv CORES; auto].
destruct (MATCH_CORES (ACTIVE E1 st1) c1 PROJ1) as [c2 [PROJ2 MATCH12]].
destruct (core_after_external core_simulation cd j j' c1 c2 m1 e 
                vals1 ret1 m1' m2 m2' ret2 ef_sig)
 as [cd' [c1' [c2' [AFTER1 [AFTER2 MATCH12']]]]]; auto.
exists cd'.
assert (exists st1', after_external (esem source) (Some ret1) st1 = Some st1' /\
         PROJ_CORE E1 (ACTIVE E1 st1') st1' = Some c1') as [st1' [? PROJ1']].
 inv core_compat1.
 specialize (after_ext_prog st1 c1 c1' source (Some ret1)).
 spec after_ext_prog; auto.
 spec after_ext_prog; auto.
 spec after_ext_prog; auto.
 destruct after_ext_prog as [st1' [? ?]].
 exists st1'; split; auto.
 assert (ACTIVE E1 st1=ACTIVE E1 st1') as <-.
  eapply after_ext_pres; eauto.
  solve[unfold cores; eauto].
 solve[unfold cores; eauto].
assert (exists st2', after_external (esem target) (Some ret2) st2 = Some st2' /\
         PROJ_CORE E2 (ACTIVE E2 st2') st2' = Some c2') as [st2' [? PROJ2']].
 inv core_compat2.
 specialize (after_ext_prog st2 c2 c2' target (Some ret2)).
 spec after_ext_prog; auto.
 spec after_ext_prog; auto.
 rewrite <-ACT; auto.
 spec after_ext_prog; auto.
 destruct after_ext_prog as [st2' [? ?]].
 exists st2'; split; auto.
 assert (ACTIVE E2 st2=ACTIVE E2 st2') as <-.
  eapply after_ext_pres; eauto.
  solve[unfold cores; eauto].
 unfold cores; eauto.
 solve[rewrite ACT in PROJ2; auto].
 solve[rewrite ACT in PROJ2; auto]. 
exists st1'; exists st2'.
split3; auto.

hnf.
assert (ACTIVE E1 st1=ACTIVE E1 st1') as <-.
 inv core_compat1.
 eapply after_ext_pres; eauto.
 solve[unfold cores; eauto].
assert (ACTIVE E2 st2=ACTIVE E2 st2') as <-.
 inv core_compat2.
 eapply after_ext_pres; eauto.
 unfold cores; eauto.
 solve[rewrite <-ACT; auto].
split3; auto.
inv esig_compilable.
eapply after_external_runnable; eauto.

intros i _c _PROJ1'.
case_eq (eq_nat_dec (ACTIVE E1 st1) i).
(*ACTIVE E1 st1 = i*)
intros EQ _; rewrite <-EQ in *; clear EQ.
exists c2'; split; auto.
rewrite ACT; auto.
rewrite _PROJ1' in PROJ1'.
inv PROJ1'; auto.

(*ACTIVE E1 st1 <> i*)
intros NEQ _.
specialize (MATCH_CORES' i _c).
spec MATCH_CORES'.
 inv core_compat1.
 solve[erewrite after_ext_others; eauto].
destruct MATCH_CORES' as [_d [_PROJ2 _MATCH12]].
exists _d; split; auto.
 inv core_compat2.
 erewrite <-after_ext_others; eauto.
 solve[rewrite <-ACT; auto].
inv esig_compilable.
eapply after_external_diagram; eauto.
inv core_compat2.
erewrite <-after_ext_others; eauto.
solve[rewrite <-ACT; auto].
Qed.

End CompilableExtension.


