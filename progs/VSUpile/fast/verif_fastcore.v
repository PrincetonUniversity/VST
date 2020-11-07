Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import VST.floyd.linking.

Require Import spec_stdlib.

Require Import verif_stdlib.
Require Import verif_fastpile.
Require Import verif_fastonepile.
Require Import verif_fastapile.
Require Import verif_fasttriang.

Section CORE_VSU.
Variable M: MallocFreeAPD.
Definition PrivPILE: spec_fastpile_private.FastpilePrivateAPD:= PILEPRIV M.
Definition PILE: spec_fastpile.PileAPD := spec_fastpile_private.pilepreds PrivPILE. 

Definition ONEPILE : spec_onepile.OnePileAPD := ONEPILE PILE.

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

Definition mrg_Imports1:funspecs := (MF_ASI M).

Definition mrg_Exports1:funspecs := 
G_merge (spec_fastpile.PileASI M PILE) (spec_onepile.OnepileASI M ONEPILE).

Definition Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog1 mrg_cs1 nil mrg_Imports1 mrg_prog1 mrg_Exports1 (one_pile PILE None).
Proof.
  VSULink_tac (PilePrivateVSU M) (OnepileVSU M PILE).
  extensionality gv. simpl. rewrite emp_sepcon; trivial.
Qed.

Definition APILE := verif_fastapile.APILE (*M*) PrivPILE.

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

Definition mrg_Imports2:funspecs := MF_ASI M.

Definition mrg_Exports2:funspecs := G_merge  mrg_Exports1 (Apile_ASI M PrivPILE).

Definition Apile_Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog2 mrg_cs2 nil mrg_Imports2 mrg_prog2 mrg_Exports2
   (fun gv => one_pile PILE None gv * apile PrivPILE [] gv)%logic.
Proof.
  VSULink_tac (Onepile_Pile_VSU) (ApileVSU M PrivPILE).
  intuition.
  extensionality gv; trivial.
Qed.

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

Definition mrg_Imports3:funspecs := MF_ASI M.

Definition mrg_Exports3:funspecs := G_merge mrg_Exports2 (spec_triang.TriangASI M).

Definition Triang_Apile_Onepile_Pile_VSU:
@VSU NullExtension.Espec
   mrg_Vprog3 mrg_cs3 nil mrg_Imports3 mrg_prog3 mrg_Exports3
  (fun gv => one_pile PILE None gv * apile PrivPILE [] gv)%logic.
Proof.
  VSULink_tac (Apile_Onepile_Pile_VSU) (TriangVSU M PILE).
  extensionality gv. simpl. rewrite sepcon_emp. trivial.
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

Definition coreExports:funspecs := G_merge (MF_ASI M) mrg_Exports3.

Definition coreBuiltins:funspecs := (MallocFreeASI M). (*i.e. MF_E M*)

Definition Core_VSU:
@VSU NullExtension.Espec coreVprog coreCS coreBuiltins coreImports coreprog coreExports
     (fun gv => one_pile PILE None gv * apile PrivPILE [] gv)%logic.
Proof.
  VSULink_tac (MallocFreeVSU M) (Triang_Apile_Onepile_Pile_VSU).
  extensionality gv. simpl. rewrite emp_sepcon; trivial.
Qed.

Definition Core_CanVSU: @CanonicalVSU NullExtension.Espec
   coreVprog coreCS coreBuiltins coreImports coreprog coreExports
   (fun gv => one_pile PILE None gv * apile PrivPILE [] gv)%logic.
Proof.
eapply VSU_to_CanonicalVSU. apply Core_VSU.
Qed.
End CORE_VSU.