Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import PileModel. (*needed for decreasing etc*)
Require Import simple_spec_stdlib.
Require Import simple_spec_onepile.
Require Import pile.
Require Import apile.
Require Import simple_spec_apile.
Require Import simple_spec_triang.
Require Import main.
Require Import simple_spec_main.
Require Import simple_verif_stdlib.
Require Import simple_verif_pile.
Require Import simple_verif_onepile.
Require Import simple_verif_apile.
Require Import simple_verif_triang.

Definition Onepile_Pile_VSU :=
  ltac:(linkVSUs PileVSU OnepileVSU). 

Definition Apile_Onepile_Pile_VSU :=
  ltac:(linkVSUs Onepile_Pile_VSU ApileVSU). 

Definition Triang_Apile_Onepile_Pile_VSU :=
  ltac:(linkVSUs Apile_Onepile_Pile_VSU TriangVSU). 

Definition Core_VSU :=
  ltac:(linkVSUs MallocFreeVSU Triang_Apile_Onepile_Pile_VSU).

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition main_QPprog := ltac:(QPprog prog).
Definition whole_prog := ltac:(QPlink_progs main_QPprog (VSU_prog Core_VSU)).
Definition Vprog: varspecs := QPvarspecs whole_prog.
Definition Main_imports := filter (matchImportExport main_QPprog) (VSU_Exports Core_VSU). 
Definition mainspec :=  main_spec whole_prog.
Definition Gprog := mainspec :: Main_imports.

Lemma body_main: semax_body Vprog Gprog f_main mainspec.
Proof.
pose Core_VSU.
start_function.
forward_call gv.
forward_for_simple_bound 10
  (EX i:Z,
   PROP() LOCAL(gvars gv)
   SEP (onepile (Some (decreasing (Z.to_nat i))) gv;
          apile (decreasing (Z.to_nat i)) gv;
          mem_mgr gv; has_ext tt)).
- 
 entailer!.
-
forward_call (i+1, decreasing(Z.to_nat i), gv).
rep_lia.
forward_call (i+1, decreasing(Z.to_nat i), gv).
rep_lia. rewrite decreasing_inc by lia.
entailer!.
-
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (10,gv).
lia.
forward.
Qed.

Definition MainComp:  MainCompType nil main_QPprog Core_VSU whole_prog (snd (main_spec whole_prog))  emp.
Proof.
mkComponent prog.
solve_SF_internal body_main.
Qed.

Lemma WholeComp: WholeCompType Core_VSU MainComp.
Proof. proveWholeComponent. Qed.

Lemma WholeProgSafe: WholeProgSafeType WholeComp tt.
Proof. proveWholeProgSafe. Qed.

Eval red in WholeProgSafeType WholeComp tt.

