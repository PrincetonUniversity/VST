Add LoadPath "..".
Require Import veric.sim veric.sim_step_lemmas veric.base veric.expr.
Require Import ListSet.

Set Implicit Arguments.

Notation mem := Memory.mem.

Section ExtSig.
Variable ora_state: Type.

Inductive extsig := mk_extsig: 
  forall (handled: list AST.external_function)
         (extspec: external_specification mem external_function ora_state), 
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
  (ora_state1 ora_state2: Type) 
  (sigma1: extsig ora_state1) (sigma2: extsig ora_state2) :=
  forall ef, List.In ef sigma1 -> List.In ef sigma2.

Lemma extfunc_eqdec : forall ef1 ef2 : AST.external_function, 
  {ef1=ef2} + {~ef1=ef2}.
Proof.
intros ef1 ef2; repeat decide equality.
apply Address.EqDec_int.
apply Address.EqDec_int.
Qed.

Definition link
  (ora_state1 ora_state2: Type) 
  (sigma1: extsig ora_state1) (sigma2: extsig ora_state2) :=
  mk_extsig (ListSet.set_diff extfunc_eqdec sigma1 sigma2) sigma1.

Module Extension. Record Sig
  (G: Type) (*type of global environments*)
  (W: Type) (*type of corestates of extended semantics*)
  (C: Type) (*type of corestates of core semantics*)
  (D: Type) (*type of initialization data*)

  (*extended semantics*)
  (wsem: CompcertCoreSem G W D) 
  (*a set of core semantics*)
  (csem: nat -> option (CompcertCoreSem G C D))

  (*signature of external functions; we assume Z = W, which limits modularity (BAD!) *)
  (signature: extsig W)
  (*subset of external functions "implemented" by this extension*)
  (handled: extsig W) := Make {

    (*generalized projection of core i from state w*)
    proj_core : W -> nat -> option C;
    proj_exists : forall ge i w c' m w' m', 
      corestep wsem ge w m w' m' -> proj_core w' i = Some c' -> 
      exists c, proj_core w i = Some c;

    (*the active (i.e., runnable and currently scheduled) thread, if any*)
    active : W -> option nat;
    active_csem : forall w i,
      active w = Some i -> exists CS, csem i = Some CS;
    active_proj_core : forall w i, 
      active w = Some i -> exists c, proj_core w i = Some c;
    active_none : forall w i c CS,
      active w = None -> proj_core w i = Some c -> csem i = Some CS -> 
      exists ef, exists args, at_external CS c = Some (ef, args);

    after_at_external_excl : forall i CS c c' ret,
      csem i = Some CS -> after_external CS ret c = Some c' -> 
      at_external CS c' = None;

    (*a global invariant characterizing "safe" extensions*)
    all_safe (ge: G) (n: nat) (ora: W) (w: W) (m: Memory.mem) :=
      forall i CS c, csem i = Some CS -> proj_core w i = Some c -> 
        safeN CS signature ge n w c m
  }.

End Extension. 

(*an extension E is safe when all states satisfy the global invariant E.(inv)*)

Section SafeExtension.
Variables
  (G W C D: Type) 
  (wsem: CompcertCoreSem G W D) 
  (csem: nat -> option (CompcertCoreSem G C D))
  (signature: extsig W)
  (handled: extsig W).

Notation inv := Extension.all_safe.

Definition safe_extension (E: Extension.Sig wsem csem signature handled) := 
  forall ge n ora w m, 
    E.(inv) ge n ora w m -> 
    safeN wsem (link signature handled) ge n ora w m.

End SafeExtension.

Section SafetyMonotonicity.
Variables 
  (G C D ora_state: Type) (CS: CompcertCoreSem G C D)
  (signature handled: extsig ora_state).

Lemma safety_monotonicity : forall ge n ora c m,
  safeN CS (link signature handled) ge n ora c m -> 
  safeN CS signature ge n ora c m.
Admitted.

End SafetyMonotonicity.

Section SafetyCriteria.
Variables
  (G W C D: Type) 
  (wsem: CompcertCoreSem G W D) 
  (csem: nat -> option (CompcertCoreSem G C D))
  (signature: extsig W)
  (handled: extsig W)
  (E: Extension.Sig wsem csem signature handled).

Notation ALL_SAFE := E.(Extension.all_safe).
Notation PROJ := E.(Extension.proj_core).
Notation ACTIVE := (E.(Extension.active)).
Notation "'THREAD' i 'is' ( CS , c ) 'in' w" := 
  (csem i = Some CS /\ PROJ w i = Some c)
  (at level 66, no associativity, only parsing).
Notation proj_exists := E.(Extension.proj_exists).
Notation active_csem := E.(Extension.active_csem).
Notation active_proj_core := E.(Extension.active_proj_core).
Notation active_none := E.(Extension.active_none).
Notation after_at_external_excl := E.(Extension.after_at_external_excl).

Lemma all_safe_downward ge n ora w m :
  ALL_SAFE ge (S n) ora w m -> ALL_SAFE ge n ora w m.
Proof. intros INV i CS c H2 H3; eapply safe_downward1; eauto. Qed.

Definition NOT_ACTIVE (w: W) (i: nat) :=
  exists j, i <> j /\ ACTIVE w = Some j.

Inductive safety_criteria: Type := SafetyCriteria: forall 
  (*coresteps preserve the invariant*)
  (core_pres: forall ge n ora w c m CS i w' c' m', 
    ALL_SAFE ge n ora w m -> 
    ACTIVE w = Some i -> THREAD i is (CS, c) in w -> 
    corestep CS ge c m c' m' -> corestep wsem ge w m w' m' -> 
    THREAD i is (CS, c') in w' /\ ALL_SAFE ge n ora w' m')

  (*corestates satisfying the invariant can corestep*)
  (core_prog: forall ge n ora w m i c CS, 
    ALL_SAFE ge n ora w m -> 
    ACTIVE w = Some i -> THREAD i is (CS, c) in w -> 
    exists c', exists w', exists m', 
      corestep CS ge c m c' m' /\ corestep wsem ge w m w' m' /\
      THREAD i is (CS, c') in w')

  (*steps "internal" to the extension respect function specifications*)
  (exten_pres: forall ge w m c i w' m' c' CS ef args P Q x, 
    THREAD i is (CS, c) in w -> 
    at_external CS c = Some (ef, args) -> 
    handles ef signature -> 
    spec_of ef signature x = (P, Q) -> P args w m -> 
    corestep wsem ge w m w' m' -> 
    THREAD i is (CS, c') in w' -> 
      (at_external CS c' = Some (ef, args) /\ P args w' m' /\
        (forall j, ACTIVE w' = Some j -> i <> j)) \/
      (exists ret, after_external CS ret c = Some c' /\ Q ret w' m'))

  (*"internal" states satisfying the invariant can step; moreover, core 
     states that remain "at_external" remain unchanged*)
  (exten_prog: forall ge n ora w m,
    ALL_SAFE ge n ora w m -> ACTIVE w = None -> 
    exists w', exists m', corestep wsem ge w m w' m' /\ 
      forall i c CS, THREAD i is (CS, c) in w -> 
        exists c', THREAD i is (CS, c') in w' /\ 
          (forall ef args ef' args', 
            at_external CS c = Some (ef, args) -> 
            at_external CS c' = Some (ef', args') -> c=c'))

  (at_extern_call: forall w ef args,
    at_external wsem w = Some (ef, args) -> 
    exists i, exists CS, exists c, 
      THREAD i is (CS, c) in w /\ 
      at_external CS c = Some (ef, args))

  (at_extern_ret: forall i c w m w' m' args ret c' P Q CS ef x,
    THREAD i is (CS, c) in w -> 
    spec_of ef signature x = (P, Q) -> 
    P args w m -> Q ret w' m' -> 
    after_external CS ret c = Some c' -> 
    exists w', 
      after_external wsem ret w = Some w' /\ 
      THREAD i is (CS, c') in w' /\
      (forall CS0 c0 j, i <> j -> 
        (THREAD j is (CS0, c0) in w' -> THREAD j is (CS0, c0) in w) /\
        (forall ge n, safeN CS0 signature ge (S n) w c0 m -> 
                      safeN CS0 signature ge n w' c0 m'))),
  safety_criteria.

Lemma safety_criteria_safe : safety_criteria -> safe_extension E.
Proof.
inversion 1; subst; intros ge n; induction n.
intros ora w m H1; simpl; auto.
intros ora w m H1.
simpl; case_eq (at_external wsem w).

(*at_external = Some _*) 
intros [ef args] AT_EXT.
destruct (at_external_halted_excl wsem ge w) as [H2|H2].
rewrite AT_EXT in H2; congruence.
simpl; rewrite H2.
destruct (at_extern_call w ef args AT_EXT) as [i [CS [c [[H3 H4] H5]]]].
generalize H1 as H1'; intro.
specialize (H1 i CS c H3 H4).
simpl in H1.
rewrite H5 in H1.
destruct (at_external_halted_excl CS ge c) as [H6|H6].
rewrite H6 in H5; congruence.
rewrite H6 in H1; clear H6.
assert (EVOLVE: ext_spec_evolve signature w w) by admit. (*evolve*)
destruct H1 as [x H1]. 
destruct (H1 w EVOLVE) as [H7 H8].
exists x; intros w2 H9. 
split.
admit. (*by H7 and ext_specs on external states*)
intros ret m' w' POST.
destruct (H8 ret m' w' POST) as [c' [H10 H11]].
specialize (at_extern_ret i c w m w' m' args ret c' 
  (ext_spec_pre signature ef x) (ext_spec_post signature ef x) CS ef x).
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
spec at_extern_ret; auto.
destruct at_extern_ret as [w'' [H12 [[H13 H14] H15]]].
exists w''.
split; auto.
eapply safety_monotonicity; eapply IHn.
intros j CSj cj CSEMJ PROJJ.
case_eq (eq_nat_dec i j).
(*i=j*)
intros Heq _; subst.
rewrite CSEMJ in H13; inversion H13; subst.
rewrite PROJJ in H14; inversion H14; subst.
admit. (*by H11*)
(*i<>j*)
intros Hneq _.
destruct (H15 CSj cj j Hneq) as [H16 H17].
destruct H16 as [H16 H18]. split; auto.
specialize (H1' j CSj cj CSEMJ H18).
eapply H17; eauto.

(*at_external = None*)
intros H2.
destruct (safely_halted wsem ge w); auto.
case_eq (ACTIVE w).
(*active thread i*)
intros i ACT.
destruct (active_csem _ ACT) as [CS CSEM].
destruct (active_proj_core _ ACT) as [c PROJECT].
destruct (core_prog ge n ora w m i c CS (all_safe_downward H1) ACT) 
 as [c' [w' [m' [CORESTEP_C [CORESTEP_W [CSEM' PROJECT']]]]]]; [split; auto|].
destruct (core_pres ge n ora w c m CS i w' c' m' (all_safe_downward H1) ACT)
 as [_ INV']; auto.
exists w'; exists m'; split; [auto|].
apply IHn; auto.
(*active thread none*)
intros ACT.
destruct (exten_prog ge n ora w m (all_safe_downward H1) ACT) 
 as [w' [m' [CORESTEP_W CORES_PRES]]].
exists w'; exists m'.
split; auto.
apply IHn.
intros i CS c CSEM PROJECT.
destruct (proj_exists ge i w m w' m' CORESTEP_W PROJECT)
 as [c0 PROJECT0].
destruct (active_none w i ACT PROJECT0 CSEM) 
 as [ef [args AT_EXT]].
specialize (H1 i CS c0 CSEM PROJECT0).
simpl in H1; rewrite AT_EXT in H1.
remember (safely_halted CS ge c0) as SAFELY_HALTED.
destruct SAFELY_HALTED; [solve[elimtype False; auto]|].
destruct H1 as [x H1].
specialize (H1 w).
assert (H3: ext_spec_evolve signature w w) by admit. (*evolve*)
destruct (H1 H3) as [PRE POST].
specialize (exten_pres ge w m c0 i w' m' c CS ef args
  (ext_spec_pre signature ef x)
  (ext_spec_post signature ef x) x).
spec exten_pres; auto.
spec exten_pres; auto.
spec exten_pres; auto. admit. (*handled*)
spec exten_pres; auto.
spec exten_pres; auto.
spec exten_pres; auto.
spec exten_pres; auto.
destruct (CORES_PRES i c0 CS) as [c' H4]; [split; auto|].
destruct exten_pres as [[AT_EXT' [PRE' ACT']] | POST'].
(*pre-preserved case*)
destruct H4 as [[H4 H5] H6].
rewrite H5 in PROJECT; inversion PROJECT; subst.
specialize (H6 ef args ef args AT_EXT AT_EXT'); subst.
clear - PRE' POST AT_EXT' H4 H5 HeqSAFELY_HALTED.
destruct n; simpl; auto.
rewrite AT_EXT', <-HeqSAFELY_HALTED.
exists x.
intros w2 H6.
split.
admit. (*by PRE' and ext_specs on external state*)
intros ret m'' w'' H8.
destruct (POST ret m'' w'' H8) as [c'' [H9 H10]].
exists c''; split; auto.
eapply safe_downward1; eauto.

(*post case*)
destruct H4 as [[H4 H5] H6].
rewrite H5 in PROJECT; inversion PROJECT; subst.
destruct POST' as [ret [AFTER_EXT POST']].
generalize (after_at_external_excl i c0 ret H4 AFTER_EXT); intros AT_EXT'.
clear - PRE POST POST' AT_EXT' AFTER_EXT H4 H5 H6 HeqSAFELY_HALTED.
destruct n; simpl; auto.
rewrite AT_EXT'.
case_eq (safely_halted CS ge c); auto.
destruct (POST ret m' w' POST') as [c' [AFTER_EXT' SAFEN]].
rewrite AFTER_EXT in AFTER_EXT'; inversion AFTER_EXT'; subst.
simpl in SAFEN.
rewrite AT_EXT' in SAFEN.
intros SAFELY_HALTED; rewrite SAFELY_HALTED in SAFEN.
destruct SAFEN as [c'' [m'' [H7 H8]]].
exists c''; exists m''; split; auto.
Qed.

End SafetyCriteria.
