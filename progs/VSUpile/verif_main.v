Require Import VST.floyd.proofauto.
Require Import VST.veric.initial_world.
Require Import VST.floyd.VSU.

Require Import PileModel.
Require Import verif_core.
Require Import main.
Require Import spec_main.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition whole_prog := ltac:(QPlink_progs (QPprog prog) (VSU_prog Core_VSU)).
Definition Vprog: varspecs := QPvarspecs whole_prog.
Definition Main_imports := VSU_Exports Core_VSU. 
Definition mainspec :=  main_spec whole_prog.
Definition Gprog := mainspec :: Main_imports.

Ltac expand_main_pre ::= 
  lazymatch goal with
  | vsu: VSU _ _ _ _ _ |- _ => 
    (eapply main_pre_InitGpred || report_failure); 
        [ try apply (VSU_MkInitPred vsu); report_failure
        | try (unfold Vardefs; simpl; reflexivity); report_failure
        | try solve [repeat constructor]; report_failure
        |  ];
     clear vsu;
     match goal with
      |- semax _ (PROPx _ (LOCALx _ (SEPx (?R _ :: _))) * _)%logic _ _ =>
        let x := unfold_all R in change R with x
     end
  | |- _ => expand_main_pre_old
  end.

Lemma body_main: semax_body Vprog Gprog f_main mainspec.
Proof.
pose Core_VSU.
start_function.
repeat change ((sepcon ?A ?B) gv) with (sepcon (A gv) (B gv)).
change (verif_onepile.one_pile PILE None gv)
 with (spec_onepile.onepile (verif_onepile.ONEPILE PILE) None gv).
forward_call gv.
cancel.  (* why is this line necessary? *)
fold ONEPILE.
set (APILE := verif_apile.apile verif_stdlib.M PrivPILE).
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
rep_lia.
forward_call (i+1, decreasing(Z.to_nat i), gv).
rep_lia. rewrite decreasing_inc by lia.
entailer!.
unfold APILE, M. simpl; cancel.
-
unfold APILE, M, ONEPILE.
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (decreasing (Z.to_nat 10), gv).
compute; split; congruence.
forward_call (10,gv).
lia.
forward.
Qed.

Definition MainComp:  MainCompType nil (QPprog prog) Core_VSU whole_prog (snd (main_spec whole_prog))  emp.
Proof.
mkComponent prog.
solve_SF_internal body_main.
Qed.

Lemma WholeComp: WholeCompType Core_VSU MainComp.
Proof. proveWholeComponent. Qed.

Lemma WholeProgSafe: WholeProgSafeType WholeComp tt.
Proof. proveWholeProgSafe. Qed.

Eval red in WholeProgSafeType WholeComp tt.
