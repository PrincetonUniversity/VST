Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Axioms.

Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.

Module CompilerCorrectness.

Definition globvar_eq {V1 V2: Type} (v1:globvar V1) (v2:globvar V2) :=
  match v1, v2 with
  | mkglobvar _ init1 readonly1 volatile1,
    mkglobvar _ init2 readonly2 volatile2 =>
    init1 = init2 /\ readonly1 =  readonly2 /\ volatile1 = volatile2
  end.

Inductive external_description :=
| extern_func: signature -> external_description
| extern_globvar: external_description.

Definition entryPts_ok  {F1 V1 F2 V2:Type}
  (P1 : AST.program F1 V1)    (P2 : AST.program F2 V2)
  (ExternIdents: list (ident * external_description))
  (entryPts: list (val * val * signature)): Prop :=
  forall e d, In (e,d) ExternIdents ->
    exists b, Genv.find_symbol  (Genv.globalenv P1) e = Some b /\
      Genv.find_symbol (Genv.globalenv P2) e = Some b /\
      match d with
        extern_func sig => In (Vptr b Int.zero,Vptr b Int.zero, sig) entryPts /\
        exists f1, exists f2, Genv.find_funct_ptr (Genv.globalenv P1) b = Some f1 /\
          Genv.find_funct_ptr (Genv.globalenv P2) b = Some f2
        | extern_globvar  => exists v1, exists v2,
          Genv.find_var_info (Genv.globalenv P1) b = Some v1 /\
          Genv.find_var_info (Genv.globalenv P2) b = Some v2 /\
          globvar_eq v1 v2
      end.

Definition entryPts_inject_ok {F1 V1 F2 V2:Type}
  (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (j: meminj)
  (ExternIdents : list (ident * external_description))
  (entryPts: list (val * val * signature)): Prop :=
  forall e d, In (e,d) ExternIdents ->
    exists b1, exists b2, Genv.find_symbol (Genv.globalenv P1) e = Some b1 /\
      Genv.find_symbol (Genv.globalenv P2) e = Some b2 /\
      j b1 = Some(b2,0) /\
      match d with
      | extern_func sig =>
        In (Vptr b1 Int.zero,Vptr b2 Int.zero, sig) entryPts /\
        exists f1, exists f2,
          Genv.find_funct_ptr (Genv.globalenv P1) b1 = Some f1 /\
          Genv.find_funct_ptr (Genv.globalenv P2) b2 = Some f2
      | extern_globvar =>
        exists v1, exists v2,
          Genv.find_var_info  (Genv.globalenv P1) b1 = Some v1 /\
          Genv.find_var_info  (Genv.globalenv P2) b2 = Some v2 /\
          globvar_eq v1 v2
      end.

Definition externvars_ok  {F1 V1:Type}  (P1 : AST.program F1 V1)
  (ExternIdents : list (ident * external_description)) : Prop :=
  forall b v, Genv.find_var_info  (Genv.globalenv P1) b = Some v ->
    exists e, Genv.find_symbol (Genv.globalenv P1) e = Some b /\
      In (e,extern_globvar) ExternIdents.

Definition GenvHyp {F1 V1 F2 V2}
  (P1 : AST.program F1 V1) (P2 : AST.program F2 V2): Prop :=
  (forall id : ident,
    Genv.find_symbol (Genv.globalenv P2) id =
    Genv.find_symbol (Genv.globalenv P1) id) /\
  (forall b : block,
    block_is_volatile (Genv.globalenv P2) b =
    block_is_volatile (Genv.globalenv P1) b).

Inductive core_correctness
  (I: forall F C V
      (Sem : CoreSemantics (Genv.t F V) C mem)
      (P : AST.program F V),Prop)
  (ExternIdents: list (ident * external_description))
  entrypoints :
  forall (F1 C1 V1 F2 C2 V2:Type)
    (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem)
    (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem)
    (P1 : AST.program F1 V1)
    (P2 : AST.program F2 V2), Type :=
    corec_eq : forall  (F1 C1 V1 F2 C2 V2:Type)
      (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem)
      (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem)
      (P1 : AST.program F1 V1)
      (P2 : AST.program F2 V2)
      (Eq_init : forall m1 : mem,
            Genv.init_mem P1 = Some m1 -> Genv.init_mem P2 = Some m1)
      (*(Eq_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 P1.(prog_defs)->
        (exists m2, initial_mem Sem2  (Genv.globalenv P2)  m2 P2.(prog_defs)
          /\ m1 = m2))*)
      (ePts_ok: entryPts_ok P1 P2 ExternIdents entrypoints)
      (R:Forward_simulation_eq.Forward_simulation_equals Sem1 Sem2
        (Genv.globalenv P1) (Genv.globalenv P2) entrypoints),
      prog_main P1 = prog_main P2 ->
      (*HERE IS THE INJECTION OF THE GENV-ASSUMPTIONS INTO THE PROOF:*)
      GenvHyp P1 P2 ->
      I _ _ _  Sem1 P1 -> I _ _ _  Sem2 P2 ->
      core_correctness I ExternIdents entrypoints F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2
| corec_ext: forall (F1 C1 V1 F2 C2 V2:Type)
  (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem)
  (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem)
  (P1 : AST.program F1 V1)
  (P2 : AST.program F2 V2)
  (Extends_init : forall m1 : mem, Genv.init_mem P1 = Some m1 ->
    exists m2, Genv.init_mem P2 = Some m2 /\ Mem.extends m1 m2)
  (*(Extends_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 P1.(prog_defs)->
    (exists m2, initial_mem Sem2  (Genv.globalenv P2)  m2 P2.(prog_defs)
      /\ Mem.extends m1 m2))*)
  (ePts_ok: entryPts_ok P1 P2 ExternIdents entrypoints)
  (R:Forward_simulation_ext.Forward_simulation_extends Sem1 Sem2
    (Genv.globalenv P1) (Genv.globalenv P2) entrypoints),
  prog_main P1 = prog_main P2 ->
  (*HERE IS THE INJECTION OF THE GENV-ASSUMPTIONS INTO THE PROOF:*)
  GenvHyp P1 P2 ->
  I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 ->
  core_correctness I ExternIdents entrypoints F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2

| corec_inj : forall (F1 C1 V1 F2 C2 V2:Type)
  (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem)
  (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem)
  (P1 : AST.program F1 V1)
  (P2 : AST.program F2 V2)
  jInit
  (Inj_init : forall m1 : mem, Genv.init_mem P1 = Some m1 ->
      exists m2, Genv.init_mem P2 = Some m2 /\ Mem.inject jInit m1 m2)
  (*(Inj_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 P1.(prog_defs)->
    (exists m2, initial_mem Sem2  (Genv.globalenv P2)  m2 P2.(prog_defs)
      /\ Mem.inject jInit m1 m2))*)
  (ePts_ok: entryPts_inject_ok P1 P2 jInit ExternIdents entrypoints)
  (preserves_globals: meminj_preserves_globals (Genv.globalenv P1) jInit)
  (R:Forward_simulation_inj.Forward_simulation_inject Sem1 Sem2
    (Genv.globalenv P1) (Genv.globalenv P2) entrypoints),
  prog_main P1 = prog_main P2 ->
 (*HERE IS THE INJECTION OF THE GENV-ASSUMPTIONS INTO THE PROOF:*)
  GenvHyp P1 P2 ->
  externvars_ok P1 ExternIdents ->
  I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 ->
  core_correctness I ExternIdents entrypoints F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2

| corec_trans: forall  (F1 C1 V1 F2 C2 V2 F3 C3 V3:Type)
  (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem)
  (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem)
  (Sem3 : CoreSemantics (Genv.t F3 V3) C3 mem)
  (P1 : AST.program F1 V1)
  (P2 : AST.program F2 V2)
  (P3 : AST.program F3 V3),
  core_correctness I ExternIdents entrypoints F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
  core_correctness I ExternIdents entrypoints F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3 ->
  core_correctness I ExternIdents entrypoints F1 C1 V1 F3 C3 V3 Sem1 Sem3 P1 P3.

Lemma corec_I: forall {F1 C1 V1 F2 C2 V2}
  (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem)
  (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem)
  (P1 : AST.program F1 V1)
  (P2 : AST.program F2 V2)  ExternIdents I entrypoints,
  core_correctness I ExternIdents entrypoints F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
  I _ _ _ Sem1 P1 /\ I _ _ _ Sem2 P2.
Proof. intros. induction X; intuition. Qed.

Lemma corec_main: forall {F1 C1 V1 F2 C2 V2}
  (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem)
  (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem)
  (P1 : AST.program F1 V1)
  (P2 : AST.program F2 V2)  ExternIdents I entrypoints,
  core_correctness I ExternIdents entrypoints F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
  prog_main P1 = prog_main P2.
Proof. intros. induction X; intuition. congruence. Qed.

(*TRANSITIVITY OF THE GENV-ASSUMPTIONS:*)
Lemma corec_Genv:forall {F1 C1 V1 F2 C2 V2}
  (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem)
  (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem)
  (P1 : AST.program F1 V1)
  (P2 : AST.program F2 V2)  ExternIdents I entrypoints,
  core_correctness I ExternIdents entrypoints F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 ->
  GenvHyp P1 P2.
Proof.
  intros. induction X; intuition.
  destruct IHX1.
  destruct IHX2.
  split; intros; eauto. rewrite H1. apply H.
Qed.

Inductive core_correctnessT
  (I: forall F C V
      (Sem : CoreSemantics (Genv.t F V) C mem)
      (P : AST.program F V),Prop)
  (ExternIdents: list (ident * external_description))
  entrypoints :
  forall (F1 C1 V F2 C2:Type)
    (Sem1 : CoreSemantics (Genv.t F1 V) C1 mem)
    (Sem2 : CoreSemantics (Genv.t F2 V) C2 mem)
    (P1 : AST.program F1 V)
    (P2 : AST.program F2 V), Type :=
  corecT_eq : forall  (F1 C1 V F2 C2:Type)
      (Sem1 : CoreSemantics (Genv.t F1 V) C1 mem)
      (Sem2 : CoreSemantics (Genv.t F2 V) C2 mem)
      (P1 : AST.program F1 V)
      (P2 : AST.program F2 V)
      transf (HP: P2 = transform_program transf P1)
      (ePts_ok: entryPts_ok P1 P2 ExternIdents entrypoints)
      (R:Forward_simulation_eq.Forward_simulation_equals Sem1 Sem2
        (Genv.globalenv P1) (Genv.globalenv P2) entrypoints),
      I _ _ _  Sem1 P1 -> I _ _ _  Sem2 P2 ->
      core_correctnessT I ExternIdents entrypoints F1 C1 V F2 C2 Sem1 Sem2 P1 P2
| corecT_ext: forall (F1 C1 V F2 C2:Type)
  (Sem1 : CoreSemantics (Genv.t F1 V) C1 mem)
  (Sem2 : CoreSemantics (Genv.t F2 V) C2 mem)
  (P1 : AST.program F1 V)
  (P2 : AST.program F2 V)
   transf (HP: P2=transform_program transf P1)
  (*(Extends_init : forall m1 : mem, Genv.init_mem P1 = Some m1 ->
    exists m2, Genv.init_mem P2 = Some m2 /\ Mem.extends m1 m2)*)
  (*(Extends_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 P1.(prog_defs)->
    (exists m2, initial_mem Sem2  (Genv.globalenv P2)  m2 P2.(prog_defs)
      /\ Mem.extends m1 m2))*)
  (ePts_ok: entryPts_ok P1 P2 ExternIdents entrypoints)
  (R:Forward_simulation_ext.Forward_simulation_extends Sem1 Sem2
    (Genv.globalenv P1) (Genv.globalenv P2) entrypoints),
  I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 ->
  core_correctnessT I ExternIdents entrypoints F1 C1 V F2 C2 Sem1 Sem2 P1 P2

| corecT_inj : forall (F1 C1 V F2 C2:Type)
  (Sem1 : CoreSemantics (Genv.t F1 V) C1 mem)
  (Sem2 : CoreSemantics (Genv.t F2 V) C2 mem)
  (P1 : AST.program F1 V)
  (P2 : AST.program F2 V)
   transf (HP: P2=transform_program transf P1) m
  (InitMem: Genv.init_mem P1 = Some m)
  (ePts_ok: entryPts_inject_ok P1 P2 (Mem.flat_inj (Mem.nextblock m)) ExternIdents entrypoints)
  (*(preserves_globals: meminj_preserves_globals (Genv.globalenv P1) (Mem.flat_inj (Mem.nextblock m)))*)
  (R:Forward_simulation_inj.Forward_simulation_inject Sem1 Sem2
    (Genv.globalenv P1) (Genv.globalenv P2) entrypoints),
 (*THE PRESENCE OF (HP: P2=transform_program transf P1) eliminates
    the need for some assumptions:
  prog_main P1 = prog_main P2 ->
  GenvHyp P1 P2 ->,
   and jInit is (Mem.flat_inj (Mem.nextblock m)) where m=init_mam P1*)
  externvars_ok P1 ExternIdents ->
  I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 ->
  core_correctnessT I ExternIdents entrypoints F1 C1 V F2 C2 Sem1 Sem2 P1 P2

| corecT_trans: forall  (F1 C1 V F2 C2 F3 C3:Type)
  (Sem1 : CoreSemantics (Genv.t F1 V) C1 mem)
  (Sem2 : CoreSemantics (Genv.t F2 V) C2 mem)
  (Sem3 : CoreSemantics (Genv.t F3 V) C3 mem)
  (P1 : AST.program F1 V)
  (P2 : AST.program F2 V)
  (P3 : AST.program F3 V)
   transf12 (HP: P2=transform_program transf12 P1)
   transf23 (HPP: P3=transform_program transf23 P2),
  core_correctnessT I ExternIdents entrypoints F1 C1 V F2 C2 Sem1 Sem2 P1 P2 ->
  core_correctnessT I ExternIdents entrypoints F2 C2 V F3 C3 Sem2 Sem3 P2 P3 ->
  core_correctnessT I ExternIdents entrypoints F1 C1 V F3 C3 Sem1 Sem3 P1 P3.

(*The same relation for CoopCoreSems - we define this explicitly in order
  enable doing induction on it: induction on core_correctnessT's that
  are instantiated to CoopCoreSems doesn't work.*)

Inductive coop_correctnessT
  (I: forall F C V
      (Sem : CoopCoreSem (Genv.t F V) C)
      (P : AST.program F V),Prop)
  (ExternIdents: list (ident * external_description))
  entrypoints:
  forall (F1 C1 V F2 C2:Type)
    (Sem1 : CoopCoreSem (Genv.t F1 V) C1)
    (Sem2 : CoopCoreSem (Genv.t F2 V) C2)
    (P1 : AST.program F1 V)
    (P2 : AST.program F2 V) (transf: F1 -> F2), Type :=
  coopT_eq : forall  (F1 C1 V F2 C2:Type)
      (Sem1 : CoopCoreSem (Genv.t F1 V) C1)
      (Sem2 : CoopCoreSem (Genv.t F2 V) C2)
      (P1 : AST.program F1 V)
      (P2 : AST.program F2 V)
      transf (HP: P2 = transform_program transf P1)
      (ePts_ok: entryPts_ok P1 P2 ExternIdents entrypoints)
      (R:Forward_simulation_eq.Forward_simulation_equals Sem1 Sem2
        (Genv.globalenv P1) (Genv.globalenv P2) entrypoints),
      I _ _ _  Sem1 P1 -> I _ _ _  Sem2 P2 ->
      coop_correctnessT I ExternIdents entrypoints F1 C1 V F2 C2 Sem1 Sem2 P1 P2 transf
| coopT_ext: forall (F1 C1 V F2 C2:Type)
  (Sem1 : CoopCoreSem (Genv.t F1 V) C1)
  (Sem2 : CoopCoreSem (Genv.t F2 V) C2)
  (P1 : AST.program F1 V)
  (P2 : AST.program F2 V)
   transf (HP: P2=transform_program transf P1)
  (ePts_ok: entryPts_ok P1 P2 ExternIdents entrypoints)
  (R:Forward_simulation_ext.Forward_simulation_extends Sem1 Sem2
    (Genv.globalenv P1) (Genv.globalenv P2) entrypoints),
  I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 ->
  coop_correctnessT I ExternIdents entrypoints F1 C1 V F2 C2 Sem1 Sem2 P1 P2 transf

| coopT_inj : forall (F1 C1 V F2 C2:Type)
  (Sem1 : CoopCoreSem (Genv.t F1 V) C1)
  (Sem2 : CoopCoreSem (Genv.t F2 V) C2)
  (P1 : AST.program F1 V)
  (P2 : AST.program F2 V)
   transf (HP: P2=transform_program transf P1) (*m
  (InitMem: Genv.init_mem P1 = Some m) *)
  (ePts_ok: forall m, Genv.init_mem P1 = Some m ->
       entryPts_inject_ok P1 P2 (Mem.flat_inj (Mem.nextblock m)) ExternIdents entrypoints)
  (R:Forward_simulation_inj.Forward_simulation_inject Sem1 Sem2
    (Genv.globalenv P1) (Genv.globalenv P2) entrypoints),
  externvars_ok P1 ExternIdents ->
  I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 ->
  coop_correctnessT I ExternIdents entrypoints F1 C1 V F2 C2 Sem1 Sem2 P1 P2 transf

| coopT_trans: forall  (F1 C1 V F2 C2 F3 C3:Type)
  (Sem1 : CoopCoreSem (Genv.t F1 V) C1)
  (Sem2 : CoopCoreSem (Genv.t F2 V) C2)
  (Sem3 : CoopCoreSem (Genv.t F3 V) C3)
  (P1 : AST.program F1 V)
  (P2 : AST.program F2 V)
  (P3 : AST.program F3 V)
   transf12 (HP: P2=transform_program transf12 P1)
   transf23 (HPP: P3=transform_program transf23 P2),
  coop_correctnessT I ExternIdents entrypoints F1 C1 V F2 C2 Sem1 Sem2 P1 P2 transf12->
  coop_correctnessT I ExternIdents entrypoints F2 C2 V F3 C3 Sem2 Sem3 P2 P3 transf23 ->
  coop_correctnessT I ExternIdents entrypoints F1 C1 V F3 C3 Sem1 Sem3 P1 P3 (fun f => transf23 (transf12 f)).

(*The relation WITHOUT the trans-case, NOT specialized to program translations*)
Inductive cc_sim (I: forall F C V
                    (Sem : CoopCoreSem (Genv.t F V) C)
                    (P : AST.program F V), Prop)
          (ExternIdents: list (ident * external_description))
          entrypoints:
forall (F1 C1 V1 F2 C2 V2:Type)
  (Sem1 : CoopCoreSem (Genv.t F1 V1) C1)
  (Sem2 : CoopCoreSem(Genv.t F2 V2) C2)
  (P1 : AST.program F1 V1)
  (P2 : AST.program F2 V2), Type :=
  ccs_eq : forall  (F1 C1 V1 F2 C2 V2:Type)
    (Sem1 : CoopCoreSem(Genv.t F1 V1) C1)
    (Sem2 : CoopCoreSem(Genv.t F2 V2) C2)
    (P1 : AST.program F1 V1)
    (P2 : AST.program F2 V2)
    (Eq_init : forall m1 : mem, Genv.init_mem P1 = Some m1 ->
                                Genv.init_mem P2 = Some m1)
    (*(Eq_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 P1.(prog_defs)->
      (exists m2, initial_mem Sem2 (Genv.globalenv P2)  m2 P2.(prog_defs) /\ m1=m2))*)
    (ePts_ok: entryPts_ok P1 P2 ExternIdents entrypoints)
    (R:Forward_simulation_eq.Forward_simulation_equals Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints),
    prog_main P1 = prog_main P2 ->
   (*HERE IS THE INJECTION OF THE GENV-ASSUMPTIONS INTO THE PROOF:*)
    GenvHyp P1 P2 ->
    I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 ->
    cc_sim I ExternIdents entrypoints F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2
 | ccs_ext : forall  (F1 C1 V1 F2 C2 V2:Type)
    (Sem1 : CoopCoreSem (Genv.t F1 V1) C1)
    (Sem2 : CoopCoreSem (Genv.t F2 V2) C2)
   (P1 : AST.program F1 V1)
   (P2 : AST.program F2 V2)
   (Ext_init : forall m1 : mem, Genv.init_mem P1 = Some m1 ->
         exists m2, Genv.init_mem P2 = Some m2 /\ Mem.extends m1 m2)
   (*(Extends_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 P1.(prog_defs)->
     (exists m2, initial_mem Sem2  (Genv.globalenv P2)  m2 P2.(prog_defs) /\
       Mem.extends m1 m2))*)
   (ePts_ok: entryPts_ok P1 P2 ExternIdents entrypoints)
   (R:Forward_simulation_ext.Forward_simulation_extends Sem1 Sem2
     (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints),
   prog_main P1 = prog_main P2 ->
  (*HERE IS THE INJECTION OF THE GENV-ASSUMPTIONS INTO THE PROOF:*)
   GenvHyp P1 P2 ->
   I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 ->
               cc_sim I ExternIdents  entrypoints F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2
 | ccs_inj : forall  (F1 C1 V1 F2 C2 V2:Type)
    (Sem1 : CoopCoreSem (Genv.t F1 V1) C1)
    (Sem2 : CoopCoreSem (Genv.t F2 V2) C2)
   (P1 : AST.program F1 V1)
   (P2 : AST.program F2 V2)
   jInit
   (Inj_init : forall m1 : mem, Genv.init_mem P1 = Some m1 ->
      exists m2, Genv.init_mem P2 = Some m2 /\ Mem.inject jInit m1 m2)
   (*(Inj_init: forall m1, initial_mem Sem1  (Genv.globalenv P1)  m1 P1.(prog_defs)->
     (exists m2, initial_mem Sem2  (Genv.globalenv P2)  m2 P2.(prog_defs)
       /\ Mem.inject jInit m1 m2))*)
   (ePts_ok: entryPts_inject_ok P1 P2 jInit ExternIdents entrypoints)
   (preserves_globals: meminj_preserves_globals (Genv.globalenv P1) jInit)
   (R:Forward_simulation_inj.Forward_simulation_inject Sem1 Sem2
     (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints),
   prog_main P1 = prog_main P2 ->
   (*HERE IS THE INJECTION OF THE GENV-ASSUMPTIONS INTO THE PROOF:*)
   GenvHyp P1 P2 ->
   externvars_ok P1 ExternIdents ->
   I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 ->
   cc_sim I ExternIdents entrypoints  F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2.


(*The relation WITHOUT the trans-case, AND specialized to program translations,
  so its proof of transitivity does not need GenvHyp. Of course this means we need
  to have V1=V2*)
Inductive cc_simT (I: forall F C V
                    (Sem : CoopCoreSem (Genv.t F V) C)
                    (P : AST.program F V), Prop)
          (ExternIdents: list (ident * external_description))
          entrypoints:
forall (F1 C1 V F2 C2:Type)
  (Sem1 : CoopCoreSem (Genv.t F1 V) C1)
  (Sem2 : CoopCoreSem(Genv.t F2 V) C2)
  (P1 : AST.program F1 V)
  (P2 : AST.program F2 V) (transf: F1 -> F2), Type :=
  ccs_eqT : forall  (F1 C1 V F2 C2:Type)
    (Sem1 : CoopCoreSem(Genv.t F1 V) C1)
    (Sem2 : CoopCoreSem(Genv.t F2 V) C2)
    (P1 : AST.program F1 V)
    (P2 : AST.program F2 V)
    transf (HP: P2=transform_program transf P1)
    (ePts_ok: entryPts_ok P1 P2 ExternIdents entrypoints)
    (R:Forward_simulation_eq.Forward_simulation_equals Sem1 Sem2
      (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints),
    I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 ->
    cc_simT I ExternIdents entrypoints F1 C1 V F2 C2 Sem1 Sem2 P1 P2 transf
 | ccs_extT : forall  (F1 C1 V F2 C2:Type)
    (Sem1 : CoopCoreSem (Genv.t F1 V) C1)
    (Sem2 : CoopCoreSem (Genv.t F2 V) C2)
   (P1 : AST.program F1 V)
   (P2 : AST.program F2 V)
   transf (HP: P2=transform_program transf P1)
   (ePts_ok: entryPts_ok P1 P2 ExternIdents entrypoints)
   (R:Forward_simulation_ext.Forward_simulation_extends Sem1 Sem2
     (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints),
   I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 ->
   cc_simT I ExternIdents  entrypoints F1 C1 V F2 C2 Sem1 Sem2 P1 P2 transf
 | ccs_injT : forall  (F1 C1 V F2 C2:Type)
    (Sem1 : CoopCoreSem (Genv.t F1 V) C1)
    (Sem2 : CoopCoreSem (Genv.t F2 V) C2)
   (P1 : AST.program F1 V)
   (P2 : AST.program F2 V)
   transf (HP: P2=transform_program transf P1) (*m
  (InitMem: Genv.init_mem P1 = Some m) *)
  (ePts_ok: forall m, Genv.init_mem P1 = Some m ->
      entryPts_inject_ok P1 P2 (Mem.flat_inj (Mem.nextblock m)) ExternIdents entrypoints)
   (R:Forward_simulation_inj.Forward_simulation_inject Sem1 Sem2
     (Genv.globalenv P1) (Genv.globalenv P2)  entrypoints),
   externvars_ok P1 ExternIdents ->
   I _ _ _ Sem1 P1 -> I _ _ _ Sem2 P2 ->
   cc_simT I ExternIdents entrypoints  F1 C1 V F2 C2 Sem1 Sem2 P1 P2 transf.
End CompilerCorrectness.