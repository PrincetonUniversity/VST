Add LoadPath "..".
Require Import veric.sim veric.sim_step_lemmas veric.base veric.expr.
Require Import ListSet.

Set Implicit Arguments.

Notation mem := Memory.mem.

Section ExtSig.
Variables (M ora_state: Type).

Inductive extsig := mk_extsig: 
  forall (handled: list AST.external_function)
         (extspec: external_specification M external_function ora_state), 
         extsig.

Definition extsig2handled (sigma: extsig) :=
  match sigma with mk_extsig l _ => l end.
Coercion extsig2handled : extsig >-> list.

Definition extsig2extspec (sigma: extsig) :=
  match sigma with mk_extsig _ spec => spec end.
Coercion extsig2extspec : extsig >-> external_specification.

Definition spec_of 
  (ef: AST.external_function) (sigma: extsig) (x: ext_spec_type sigma ef) :=
  (ext_spec_pre sigma ef x, ext_spec_post sigma ef x).

Definition handles (ef: AST.external_function) (sigma: extsig) := 
  List.In ef sigma.

End ExtSig.

(*for now, punt on spec extension (TO FILL IN LATER)*)
Definition extends 
  (M ora_state1 ora_state2: Type) 
  (sigma1: extsig M ora_state1) (sigma2: extsig M ora_state2) :=
  forall ef, List.In ef sigma1 -> List.In ef sigma2.

Lemma extfunc_eqdec : forall ef1 ef2 : AST.external_function, 
  {ef1=ef2} + {~ef1=ef2}.
Proof.
intros ef1 ef2; repeat decide equality.
apply Address.EqDec_int.
apply Address.EqDec_int.
Qed.

Definition link
  (M ora_state1 ora_state2: Type) 
  (sigma1: extsig M ora_state1) (sigma2: extsig M ora_state2) :=
  mk_extsig (ListSet.set_diff extfunc_eqdec sigma1 sigma2) sigma1.

Module Extension. Record Sig
  (G: Type) (*type of global environments*)
  (W: Type) (*type of corestates of extended semantics*)
  (C: Type) (*type of corestates of core semantics*)
  (M: Type) (*type of memories*)
  (D: Type) (*type of initialization data*)
  (ext_state: Type) (*the type of _really_ external state*)

  (*extended semantics*)
  (wsem: CoreSemantics G W M D) 
  (*a set of core semantics*)
  (csem: nat -> option (CoreSemantics G C M D))

  (*signature of external functions*)
  (signature: extsig M ext_state)
  (*subset of external functions "implemented" by this extension*)
  (handled: extsig M W) := Make {

    (*generalized projection of core i from state w*)
    proj_core : W -> nat -> option C;
    proj_exists : forall ge i w c' m w' m', 
      corestep wsem ge w m w' m' -> proj_core w' i = Some c' -> 
      exists c, proj_core w i = Some c;

    (*the active (i.e., currently scheduled) thread*)
    active : W -> nat;
    active_csem : forall w, exists CS, csem (active w) = Some CS;
    active_proj_core : forall w, exists c, proj_core w (active w) = Some c;

    (*runnable = Some i when active w = i and i is runnable (i.e., not blocked
      waiting on an external function call)*)
    runnable : W -> option nat;
    runnable_active : forall w i, 
      runnable w = Some i -> active w = i;
    runnable_none : forall w c CS,
      runnable w = None -> proj_core w (active w) = Some c -> 
      csem (active w) = Some CS -> 
      exists ef, exists args, at_external CS c = Some (ef, args);

    (*a thread is no longer "at external" once the extension has returned 
      to it with the result of the external function call*)
    after_at_external_excl : forall i CS c c' ret,
      csem i = Some CS -> after_external CS ret c = Some c' -> 
      at_external CS c' = None;

    handles_ok: forall w i CS c ef args,
      csem i = Some CS -> proj_core w i = Some c -> 
      at_external CS c = Some (ef, args) -> 
      at_external wsem w = None -> 
      handles ef signature;

    proj_ext_state : W -> ext_state;
    lift_pred : (ext_state -> M -> Prop) -> (W -> M -> Prop);
    proj_ext_state_pre : forall ef x P Q args w m,
      spec_of ef (link signature handled) x = (P, Q) -> 
      P args (proj_ext_state w) m <-> lift_pred (P args) w m;
    proj_ext_state_post : forall ef x P Q ret w m,
      spec_of ef (link signature handled) x = (P, Q) -> 
      Q ret (proj_ext_state w) m <-> lift_pred (Q ret) w m;
    ext_upd_at_external : forall ge w m w' m',
      corestep wsem ge w m w' m' -> 
      proj_ext_state w = proj_ext_state w';

    inj_ext_state : ext_state -> W -> W;
    proj_inj : forall ora w, proj_ext_state (inj_ext_state ora w) = ora;

    (*a global invariant characterizing "safe" extensions*)
    all_safe (ge: G) (n: nat) (w: W) (m: M) :=
      forall i CS c, csem i = Some CS -> proj_core w i = Some c -> 
        safeN CS signature ge n (proj_ext_state w) c m
  }.

End Extension. 

(*an extension E is safe when all states satisfy the "all_safe" invariant*)

Section SafeExtension.
Variables
  (G W C M D ext_state: Type) 
  (wsem: CoreSemantics G W M D) 
  (csem: nat -> option (CoreSemantics G C M D))
  (signature: extsig M ext_state)
  (handled: extsig M W).

Notation inv := Extension.all_safe.

Definition safe_extension (E: Extension.Sig wsem csem signature handled) := 
  forall ge n w m,  E.(inv) ge n w m -> 
    safeN wsem (link signature handled) ge n (E.(Extension.proj_ext_state) w) w m.

End SafeExtension.

Section SafetyMonotonicity.
Variables 
  (G C W M D ext_state: Type) (CS: CoreSemantics G C M D)
  (signature: extsig M ext_state) 
  (handled: extsig M W).

Lemma safety_monotonicity : forall ge n ora c m,
  safeN CS (link signature handled) ge n ora c m -> 
  safeN CS signature ge n ora c m.
Admitted.

End SafetyMonotonicity.

Section SafetyCriteria.
Variables
  (G W C M D ext_state: Type) 
  (wsem: CoreSemantics G W M D) 
  (csem: nat -> option (CoreSemantics G C M D))
  (signature: extsig M ext_state)
  (handled: extsig M W)
  (E: Extension.Sig wsem csem signature handled).

Notation ALL_SAFE := E.(Extension.all_safe).
Notation PROJ := E.(Extension.proj_core).
Notation PROJ_EXT := E.(Extension.proj_ext_state).
Notation INJ_EXT := E.(Extension.inj_ext_state).
Notation LIFT := E.(Extension.lift_pred).
Notation ACTIVE := (E.(Extension.active)).
Notation RUNNABLE := (E.(Extension.runnable)).
Notation "'THREAD' i 'is' ( CS , c ) 'in' w" := 
  (csem i = Some CS /\ PROJ w i = Some c)
  (at level 66, no associativity, only parsing).
Notation proj_exists := E.(Extension.proj_exists).
Notation active_csem := E.(Extension.active_csem).
Notation active_proj_core := E.(Extension.active_proj_core).
Notation after_at_external_excl := E.(Extension.after_at_external_excl).
Notation handles_ok := E.(Extension.handles_ok).
Notation proj_inj := E.(Extension.proj_inj).
Notation proj_ext_state_pre := E.(Extension.proj_ext_state_pre).
Notation proj_ext_state_post := E.(Extension.proj_ext_state_post).
Notation ext_upd_at_external := E.(Extension.ext_upd_at_external).
Notation runnable_active := E.(Extension.runnable_active).
Notation runnable_none := E.(Extension.runnable_none).

Lemma all_safe_downward ge n w m :
  ALL_SAFE ge (S n) w m -> ALL_SAFE ge n w m.
Proof. intros INV i CS c H2 H3; eapply safe_downward1; eauto. Qed.

Inductive safety_criteria: Type := SafetyCriteria: forall 
  (*coresteps preserve the invariant*)
  (core_pres: forall ge n w c m CS i w' c' m', 
    ALL_SAFE ge n w m -> 
    ACTIVE w = i -> THREAD i is (CS, c) in w -> 
    corestep CS ge c m c' m' -> corestep wsem ge w m w' m' -> 
    THREAD i is (CS, c') in w' /\ ALL_SAFE ge n w' m')

  (*corestates satisfying the invariant can corestep*)
  (core_prog: forall ge n w m i c CS, 
    ALL_SAFE ge n w m -> 
    ACTIVE w = i -> RUNNABLE w = Some i -> THREAD i is (CS, c) in w -> 
    exists c', exists w', exists m', 
      corestep CS ge c m c' m' /\ corestep wsem ge w m w' m' /\
      THREAD i is (CS, c') in w')

  (*"handled" steps respect function specifications*)
  (handled_pres: forall ge w m c w' m' c' CS ef args P Q x, 
    let i := ACTIVE w in THREAD i is (CS, c) in w -> 
    at_external CS c = Some (ef, args) -> 
    handles ef signature -> 
    spec_of ef signature x = (P, Q) -> LIFT (P args) w m -> 
    corestep wsem ge w m w' m' -> 
    THREAD i is (CS, c') in w' -> 
      ((at_external CS c' = Some (ef, args) /\ LIFT (P args) w' m' /\
        (forall j, ACTIVE w' = j -> i <> j)) \/
      (exists ret, after_external CS ret c = Some c' /\ LIFT (Q ret) w' m')))

  (*"internal" states satisfying the invariant can step; moreover, core 
     states that stay "at_external" remain unchanged*)
  (handled_prog: forall ge n w m,
    ALL_SAFE ge n w m -> RUNNABLE w = None -> 
    exists w', exists m', corestep wsem ge w m w' m' /\ 
      forall i c CS, THREAD i is (CS, c) in w -> 
        exists c', THREAD i is (CS, c') in w' /\ 
          (forall ef args ef' args', 
            at_external CS c = Some (ef, args) -> 
            at_external CS c' = Some (ef', args') -> c=c'))

  (*safety of other threads is preserved when handling one step of 
     blocked thread i*)
  (handled_rest: forall ge w m w' m' c CS ef args,
    let i := ACTIVE w in THREAD i is (CS, c) in w -> 
    at_external CS c = Some (ef, args) -> 
    at_external wsem w = None -> 
    corestep wsem ge w m w' m' -> 
    (forall CS0 c0 j, i <> j ->  
      (THREAD j is (CS0, c0) in w' -> THREAD j is (CS0, c0) in w) /\
      (forall n, safeN CS0 signature ge (S n) (PROJ_EXT w) c0 m -> 
                 safeN CS0 signature ge n (PROJ_EXT w') c0 m')))

  (*if the extended machine is at external, then the active thread is
     at external (an extension only implements external functions, it doesn't
     introduce them)*)
  (at_extern_call: forall w ef args,
    at_external wsem w = Some (ef, args) -> 
    exists CS, exists c, 
      THREAD (ACTIVE w) is (CS, c) in w /\ 
      at_external CS c = Some (ef, args))

  (*inject the results of an external call into the extended machine state*)
  (at_extern_ret: forall i c w m ora m' args ret c' P Q CS ef x,
    THREAD i is (CS, c) in w -> 
    spec_of ef signature x = (P, Q) -> 
    P args (PROJ_EXT w) m -> Q ret ora m' -> 
    after_external CS ret c = Some c' -> 
    exists w', 
      INJ_EXT ora w' = w' /\
      after_external wsem ret w = Some w' /\ 
      THREAD i is (CS, c') in w') 

  (*safety of other threads is preserved when returning from an external 
     function call*)
  (at_extern_rest: forall i c w m ora w' m' args ret c' P Q CS ef x,
    THREAD i is (CS, c) in w -> 
    spec_of ef signature x = (P, Q) -> 
    P args (PROJ_EXT w) m -> Q ret ora m' -> 
    after_external CS ret c = Some c' -> 
    after_external wsem ret w = Some w' -> 
    THREAD i is (CS, c') in w' -> 
    (forall CS0 c0 j, i <> j -> 
      (THREAD j is (CS0, c0) in w' -> THREAD j is (CS0, c0) in w) /\
      (forall ge n, safeN CS0 signature ge (S n) (PROJ_EXT w) c0 m -> 
        safeN CS0 signature ge n (PROJ_EXT w') c0 m'))),
  safety_criteria.

Lemma safety_criteria_safe : safety_criteria -> safe_extension E.
Proof.
inversion 1; subst; intros ge n; induction n.
intros w m H1; simpl; auto.
intros w m H1.
simpl; case_eq (at_external wsem w).

(*CASE 1: at_external = Some _; i.e. _really_ at_external*) 
intros [ef args] AT_EXT.
destruct (at_external_halted_excl wsem ge w) as [H2|H2].
rewrite AT_EXT in H2; congruence.
simpl; rewrite H2.
destruct (at_extern_call w ef args AT_EXT) as [CS [c [[H3 H4] H5]]].
generalize H1 as H1'; intro.
specialize (H1 (ACTIVE w) CS c H3 H4).
simpl in H1.
rewrite H5 in H1.
destruct (at_external_halted_excl CS ge c) as [H6|H6].
rewrite H6 in H5; congruence.
rewrite H6 in H1; clear H6.
destruct H1 as [x H1].
destruct H1 as [H7 H8].
exists x.
split; auto.
intros ret m' z' POST.
destruct (H8 ret m' z' POST) as [c' [H10 H11]].
specialize (at_extern_ret (ACTIVE w) c w m z' m' args ret c' 
  (ext_spec_pre signature ef x) (ext_spec_post signature ef x) CS ef x).
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
destruct at_extern_ret as [w' [H12 [H13 [H14 H15]]]].
exists w'.
split; auto.
eapply safety_monotonicity.
assert (z' = PROJ_EXT w') as -> by (rewrite <-H12, proj_inj; auto).
eapply IHn.
intros j CSj cj CSEMJ PROJJ.
case_eq (eq_nat_dec (ACTIVE w) j).
(*i=j*)
intros Heq _; rewrite Heq in *.
rewrite CSEMJ in H14; inversion H14; rewrite H6 in *.
rewrite PROJJ in H15; inversion H15; rewrite H9 in *.
auto.
(*i<>j*)
intros Hneq _.
specialize (at_extern_rest (ACTIVE w) c w m (PROJ_EXT w') w' m' args ret c'
  (ext_spec_pre signature ef x) (ext_spec_post signature ef x) CS ef x).
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
spec at_extern_rest; auto.
destruct (at_extern_rest CSj cj j Hneq) as [H16 H17].
eapply H17; eauto.
destruct H16 as [H18 H19]; auto.
eapply H1'; eauto.

(*CASE 2: at_external = None; i.e., handled function*)
intros H2.
destruct (safely_halted wsem ge w); auto.
case_eq (RUNNABLE w).
(*active thread i*)
intros i RUN.
generalize (runnable_active _ RUN) as ACT; intro.
rewrite <-ACT in *.
destruct (active_csem w) as [CS CSEM].
destruct (active_proj_core w) as [c PROJECT].
destruct (core_prog ge n w m i c CS (all_safe_downward H1) ACT) 
 as [c' [w' [m' [CORESTEP_C [CORESTEP_W [CSEM' PROJECT']]]]]]; auto.
rewrite <-ACT; auto.
rewrite <-ACT; auto.
destruct (core_pres ge n w c m CS i w' c' m' (all_safe_downward H1) ACT)
 as [_ INV']; auto.
rewrite <-ACT in *; auto.
exists w'; exists m'; split; [auto|].
erewrite ext_upd_at_external; eauto.
(*active thread none*)
intros RUN.
destruct (active_csem w) as [CS CSEM].
destruct (active_proj_core w) as [c PROJECT].
destruct (handled_prog ge n w m (all_safe_downward H1) RUN) 
 as [w' [m' [CORESTEP_W CORES_PRES]]].
exists w'; exists m'.
split; auto.
erewrite ext_upd_at_external; eauto; eapply IHn.
destruct (runnable_none w RUN PROJECT CSEM) 
 as [ef [args AT_EXT]].
intros j CSj cj CSEMj PROJECTj.
set (i := ACTIVE w) in *.
case_eq (eq_nat_dec i j).
(*i=j*)
intros Heq _; rewrite Heq in *.
destruct (proj_exists ge j w m w' m' CORESTEP_W PROJECTj)
 as [c0 PROJECT0].
rewrite PROJECT in PROJECT0; inversion PROJECT0; subst.
rewrite CSEM in CSEMj; inversion CSEMj; rewrite <-H3 in *.
specialize (H1 j CS c0 CSEM PROJECT).
simpl in H1. 
rewrite AT_EXT in H1.
remember (safely_halted CS ge c0) as SAFELY_HALTED.
destruct SAFELY_HALTED; [solve[elimtype False; auto]|].
destruct H1 as [x H1].
destruct H1 as [PRE POST].
specialize (handled_pres ge w m c0 w' m' cj CS ef args
  (ext_spec_pre signature ef x)
  (ext_spec_post signature ef x) x).
rewrite Heq in handled_pres.
hnf in handled_pres.
spec handled_pres; auto.
spec handled_pres; auto.
spec handled_pres; auto. 
 eapply handles_ok; eauto.
spec handled_pres; auto.
spec handled_pres; auto.
rewrite <-proj_ext_state_pre 
 with (ef := ef) (x := x) (Q := ext_spec_post signature ef x); auto.
spec handled_pres; auto.
spec handled_pres; auto.
destruct (CORES_PRES j c0 CS) as [c' H4]; [split; auto|].
destruct handled_pres as [[AT_EXT' [PRE' ACT']] | POST'].
(*pre-preserved case*)
destruct H4 as [[H4 H5] H6].
rewrite H5 in PROJECTj; inversion PROJECTj; subst.
specialize (H6 ef args ef args AT_EXT AT_EXT'); subst.
clear - PRE' POST AT_EXT' H4 H5 HeqSAFELY_HALTED.
destruct n; simpl; auto.
rewrite AT_EXT', <-HeqSAFELY_HALTED.
exists x.
split.
apply proj_ext_state_pre 
 with (ef := ef) (x := x) (Q := ext_spec_post signature ef x); auto.
intros ret m'' w'' H8.
destruct (POST ret m'' w'' H8) as [c'' [H9 H10]].
exists c''; split; auto.
eapply safe_downward1; eauto.
(*post case*)
destruct H4 as [[H4 H5] H6].
rewrite H5 in PROJECTj; inversion PROJECTj; rewrite <-H1 in *.
destruct POST' as [ret [AFTER_EXT POST']].
generalize (after_at_external_excl j c0 ret H4 AFTER_EXT); intros AT_EXT'.
clear - PRE POST POST' AT_EXT' AFTER_EXT H4 H5 H6 HeqSAFELY_HALTED.
destruct n; simpl; auto.
rewrite AT_EXT'.
case_eq (safely_halted CS ge c'); auto.
apply proj_ext_state_post 
 with (ef := ef) (x := x) (P := ext_spec_pre signature ef x) in POST'; auto.
destruct (POST ret m' (PROJ_EXT w') POST') as [c'' [AFTER_EXT' SAFEN]].
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
specialize (handled_rest ge w m w' m' c CS ef args).
hnf in handled_rest.
spec handled_rest; auto.
spec handled_rest; auto.
spec handled_rest; auto.
(* eapply handles_ok with (i := i); eauto.*)
spec handled_rest; auto.
destruct (handled_rest CSj cj j Hneq) as [H6 H7].
eapply H7; eauto.
destruct (proj_exists ge j w m w' m' CORESTEP_W PROJECTj)
 as [c0 PROJECT0].
specialize (H1 j CSj c0 CSEMj PROJECT0).
destruct H6 as [H8 H9].
split; auto.
rewrite H9 in PROJECT0; inversion PROJECT0; subst; auto.
Qed.

End SafetyCriteria.
