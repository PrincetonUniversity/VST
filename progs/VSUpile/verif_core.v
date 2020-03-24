Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import VST.floyd.linking.

Require Import verif_stdlib. (*M is a parameter of that module, so we're getting access to it now*)
Require Import spec_pile_private.

Require Import verif_pile.
Definition PILE := (*verif_pile.*)PILEPRIV M.

Require Import verif_onepile.
Definition ONEPILE := verif_onepile.ONEPILE PILE.

Definition onepile_pile_prog: Clight.program := 
  match link_progs pile.prog onepile.prog with
    Errors.OK p => p
  | _ => pile.prog (*arbitrary*)
  end.
Definition mrg_prog1 := ltac:
  (let x := eval hnf in onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).
Instance mrg_cs1 : compspecs. make_compspecs mrg_prog1. Defined.

Definition mrg_Vprog1:varspecs. mk_varspecs mrg_prog1. Defined.

(*unresolved imports*)
Definition mrg_Imports1:funspecs := MF_ASI.

Definition mrg_Exports1:funspecs := 
G_merge (spec_pile.PileASI M PILE) (spec_onepile.OnepileASI M ONEPILE).

Definition Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog1 mrg_cs1 nil mrg_Imports1 mrg_prog1 mrg_Exports1.
Proof.
  VSUMerge (PilePrivateVSU M) (OnepileVSU M PILE).
Qed.

Require Import verif_apile.
Definition APILE := verif_apile.APILE M PILE.

Definition apile_onepile_pile_prog: Clight.program := 
  match link_progs mrg_prog1 apile.prog with
    Errors.OK p => p
  | _ => apile.prog (*arbitrary*)
  end.
Definition mrg_prog2 := ltac:
  (let x := eval hnf in apile_onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).

Instance mrg_cs2 : compspecs. make_compspecs mrg_prog2. Defined.

Definition mrg_Vprog2:varspecs. mk_varspecs mrg_prog2. Defined.

(*unresolved imports*)
Definition mrg_Imports2:funspecs := MF_ASI.

Definition mrg_Exports2:funspecs := G_merge  mrg_Exports1 (Apile_ASI M PILE).

Definition Apile_Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog2 mrg_cs2 nil mrg_Imports2 mrg_prog2 mrg_Exports2.
Proof.
  VSUMerge (Onepile_Pile_VSU) (ApileVSU M PILE).
  intuition.
Qed.

Require Import verif_triang.

Definition triang_apile_onepile_pile_prog: Clight.program := 
  match link_progs mrg_prog2 triang.prog with
    Errors.OK p => p
  | _ => triang.prog (*arbitrary*)
  end.
Definition mrg_prog3 := ltac:
  (let x := eval hnf in triang_apile_onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).

Instance mrg_cs3 : compspecs. make_compspecs mrg_prog3. Defined.

Definition mrg_Vprog3:varspecs. mk_varspecs mrg_prog3. Defined.

(*unresolved imports*)
Definition mrg_Imports3:funspecs := MF_ASI.

Definition mrg_Exports3:funspecs := G_merge mrg_Exports2 (spec_triang.TriangASI M).

Definition Triang_Apile_Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog3 mrg_cs3 nil mrg_Imports3 mrg_prog3 mrg_Exports3.
Proof.
  VSUMerge (Apile_Onepile_Pile_VSU) (TriangVSU M PILE).
Qed.

Definition mm_triang_apile_onepile_pile_prog: Clight.program := 
  match link_progs stdlib.prog mrg_prog3 with
    Errors.OK p => p
  | _ => triang.prog (*arbitrary*)
  end.
Definition coreprog := ltac:
  (let x := eval hnf in mm_triang_apile_onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).

Instance coreCS : compspecs. make_compspecs coreprog. Defined.

Definition coreVprog:varspecs. mk_varspecs coreprog. Defined.

Definition coreImports:funspecs := nil.

Definition coreExports:funspecs := G_merge MF_ASI mrg_Exports3.

Definition MM_Triang_Apile_Onepile_Pile_VSU:
@VSU NullExtension.Espec coreVprog coreCS MF_E coreImports coreprog coreExports.
Proof.
  VSUMerge MallocFreeVSU (Triang_Apile_Onepile_Pile_VSU). congruence.
Qed.

Definition CoreVSU: @CanonicalVSU NullExtension.Espec
   coreVprog coreCS MF_E coreImports coreprog coreExports.
Proof.
eapply VSU_to_CanonicalVSU. apply MM_Triang_Apile_Onepile_Pile_VSU.
Qed.