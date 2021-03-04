Require Import VST.floyd.proofauto.
Require Import VST.veric.initial_world.
Require Import VST.floyd.VSU.

Require Import PileModel.
Require Import verif_fastcore.
Require Import main.
Require Import spec_main.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition main_QPprog := ltac:(QPprog prog).
Definition whole_prog := ltac:(QPlink_progs main_QPprog (VSU_prog Core_VSU)).
Definition Vprog: varspecs := QPvarspecs whole_prog.
Definition Main_imports := filter (matchImportExport main_QPprog) (VSU_Exports Core_VSU). 
Definition mainspec :=  main_spec whole_prog.
Definition Gprog := Main_imports ++ [mainspec].

Lemma body_main: semax_body Vprog Gprog f_main mainspec.
Proof.
pose Core_VSU.
start_function.
change (verif_fastonepile.one_pile PILE None gv)
 with (spec_onepile.onepile (verif_fastonepile.ONEPILE PILE) None gv).
forward_call gv.
fold ONEPILE.
set (APILE := verif_fastapile.apile PrivPILE).
set (M := verif_stdlib.M).
forward_for_simple_bound 10
  (EX i:Z,
   PROP() LOCAL(gvars gv)
   SEP (spec_onepile.onepile ONEPILE (Some (decreasing (Z.to_nat i))) gv;
          APILE (decreasing (Z.to_nat i)) gv;
          spec_stdlib.mem_mgr M gv; has_ext tt)).
- 
 entailer!.
-
unfold APILE, M, ONEPILE.
forward_call (i+1, decreasing(Z.to_nat i), gv).
forward_call (i+1, decreasing(Z.to_nat i), gv).
rewrite decreasing_inc by lia.
entailer!.
unfold APILE, M. simpl; cancel.
-
unfold APILE, M, ONEPILE.
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (10,gv).
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
