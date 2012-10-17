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

    (*the active (i.e., runnable and currently scheduled) thread, if any*)
    active : W -> option nat;
    active_csem : forall w i,
      active w = Some i -> exists CS, csem i = Some CS;
    active_proj_core : forall w i, 
      active w = Some i -> exists c, proj_core w i = Some c;

    (*a global invariant characterizing "safe" extensions*)
    inv (ge: G) (n: nat) (ora: W) (w: W) (m: Memory.mem) :=
      (forall ge n i CS c, csem i = Some CS -> proj_core w i = Some c -> 
        safeN CS signature ge n w c m) -> 
      safeN wsem (link signature handled) ge n ora w m
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

Notation inv := Extension.inv.

Definition safe_extension (E: Extension.Sig wsem csem signature handled) := 
  forall ge n ora w m, E.(inv) ge n ora w m.

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

Notation INV := E.(Extension.inv).
Notation PROJ := E.(Extension.proj_core).
Notation ACTIVE := E.(Extension.active).
Notation active_csem := E.(Extension.active_csem).
Notation active_proj_core := E.(Extension.active_proj_core).

Inductive safety_criteria: Type := SafetyCriteria: forall 
  (core_pres: forall ge n ora w c m CS i c' m', 
    INV ge n ora w m -> 
    PROJ w i = Some c -> 
    csem i = Some CS -> 
    CS.(corestep) ge c m c' m' -> 
    exists w', 
      wsem.(corestep) ge w m w' m' /\ 
      PROJ w' i = Some c' /\ 
      INV ge n ora w' m')
  (core_prog: forall ge n ora w m i c CS, 
    INV ge n ora w m -> 
    PROJ w i = Some c -> 
    csem i = Some CS -> 
    ACTIVE w = Some i ->
    exists c', exists m', 
      CS.(corestep) ge c m c' m')

  (extension_pres: forall ge n ora w m w' m',
    INV ge n ora w m -> 
    ACTIVE w = None -> 
    wsem.(corestep) ge w m w' m' -> 
    INV ge n ora w' m')
  (extension_prog: forall ge n ora w m,
    INV ge n ora w m -> 
    ACTIVE w = None -> 
    exists w', exists m',
      wsem.(corestep) ge w m w' m')
  
  (specs_satisfied: forall ge w m i w' m' c CS ef args P Q x, 
    PROJ w i = Some c -> 
    csem i = Some CS -> 
    at_external CS c = Some (ef,args) -> 
    handles ef signature -> 
    spec_of ef signature x = (P, Q) -> 
    P args w m -> 
    wsem.(corestep) ge w m w' m' -> 
    exists c', PROJ w' i = Some c' /\ 
      (*NOTE: we could assume c=c' here (stronger) but this makes it impossible
        to implement, e.g., a garbage collection extension*)
      (at_external CS c' = Some (ef,args) /\ P args w' m' /\
        (forall j, ACTIVE w' = Some j -> i <> j)) \/
      (ACTIVE w' = Some i /\ Q Vundef w' m')),

  safety_criteria.

Lemma safety_criteria_safe : safety_criteria -> safe_extension E.
Proof.
inversion 1; simpl in *; subst; intros ge n; induction n.
intros ora w m H1; simpl; auto.
intros ora w m H1; simpl.
case_eq (at_external wsem w).
admit. (*at_external = Some _*) 
intros H2.
destruct (safely_halted wsem ge w); auto.
case_eq (ACTIVE w).
(*active thread i*)
intros i ACT.
destruct (active_csem _ ACT) as [CS CSEM].
destruct (active_proj_core _ ACT) as [c PROJECT].
destruct (core_prog ge n ora w m i c CS (IHn ora w m) PROJECT CSEM ACT) 
 as [c' [m' CORESTEP]].
destruct (core_pres ge n ora w c m CS i c' m' (IHn ora w m) PROJECT CSEM CORESTEP)
 as [w' [CORESTEP_W [PROJ_W INV_W]]].
exists w'; exists m'; split; auto.
specialize (IHn ora w m H1).
eapply safety_monotonicity with (handled := handled); eauto.
admit. (*should follow from IHn and CORESTEP_W*)
Admitted.

End SafetyCriteria.
