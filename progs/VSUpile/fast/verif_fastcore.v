Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import VST.floyd.linking.

Require Import verif_stdlib. (*M is a parameter of that module, so we're getting access to it now*)
Require Import spec_fastpile_private.

Require Import verif_fastpile.
Definition PILE := (*verif_fastpile.*)PILEPRIV M.

Require Import verif_fastonepile.
Definition ONEPILE := verif_fastonepile.ONEPILE PILE.

Definition onepile_pile_prog: Clight.program := 
  match link_progs fastpile.prog onepile.prog with
    Errors.OK p => p
  | _ => fastpile.prog (*arbitrary*)
  end.
Definition mrg_prog1 := ltac:
  (let x := eval hnf in onepile_pile_prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).
Instance mrg_cs1 : compspecs. make_compspecs mrg_prog1. Defined.

Definition mrg_Vprog1:varspecs. mk_varspecs mrg_prog1. Defined.

(*unresolved imports*)
Definition mrg_Imports1:funspecs := MM_ASI.

Definition mrg_Exports1:funspecs := 
G_merge (spec_fastpile.PileASI M PILE) (spec_onepile.OnepileASI M ONEPILE).

Definition Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog1 mrg_cs1 nil mrg_Imports1 mrg_prog1 mrg_Exports1.
Proof.
  VSUMerge (PilePrivateVSU M) (OnepileVSU M PILE).
Qed.

Require Import verif_fastapile.
Definition APILE := verif_fastapile.APILE PILE.

Definition apile_onepile_pile_prog: Clight.program := 
  match link_progs mrg_prog1 fastapile.prog with
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
Definition mrg_Imports2:funspecs := MM_ASI.

Definition mrg_Exports2:funspecs := G_merge  mrg_Exports1 (Apile_ASI M PILE).

Definition Apile_Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog2 mrg_cs2 nil mrg_Imports2 mrg_prog2 mrg_Exports2.
Proof.
  VSUMerge (Onepile_Pile_VSU) (ApileVSU M PILE).
  intuition.
Qed.

Require Import verif_fasttriang.

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
Definition mrg_Imports3:funspecs := MM_ASI.

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

Definition coreExports:funspecs := G_merge MM_ASI mrg_Exports3.

Definition MM_Triang_Apile_Onepile_Pile_VSU:
@VSU NullExtension.Espec coreVprog coreCS MM_E coreImports coreprog coreExports.
Proof.
  VSUMerge MMVSU (Triang_Apile_Onepile_Pile_VSU). congruence.
Qed.

Definition CoreVSU: @CanonicalVSU NullExtension.Espec
   coreVprog coreCS MM_E coreImports coreprog coreExports.
Proof.
eapply VSU_to_CanonicalVSU. apply MM_Triang_Apile_Onepile_Pile_VSU.
Qed.