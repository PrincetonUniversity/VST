Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import apile.
Require Import simple_spec_stdlib.
Require Import simple_spec_pile.
Require Import simple_spec_apile.


Lemma make_apile: forall gv, 
     globals_ok gv ->
    @data_at APileCompSpecs Ews size_t nullval
          (gv _a_pile) |-- apile nil gv.
Proof.
intros. unfold apile, pilerep.
assert_PROP (headptr (gv _a_pile)) by entailer!.
Exists nullval.
unfold listrep. entailer!.
unfold_data_at (data_at _ tpile _ _).
rewrite field_at_data_at. simpl.
rewrite field_compatible_field_address
   by auto with field_compatible.
simpl. normalize.
rewrite <- data_at_nullptr.
cancel.
Qed.

Lemma apile_Init: VSU_initializer prog (apile nil).
  Proof. 
    InitGPred_tac.  rewrite sepcon_emp.
    apply make_apile; auto.
Qed.

  Definition apile_imported_specs:funspecs := 
     [ Pile_add_spec; Pile_count_spec].

  Definition apile_internal_specs: funspecs := ApileASI.

  Definition ApileVprog: varspecs. mk_varspecs prog. Defined.
  Definition ApileGprog: funspecs := apile_imported_specs ++ apile_internal_specs.

Lemma body_Apile_add: semax_body ApileVprog ApileGprog f_Apile_add Apile_add_spec.
Proof.
start_function.
unfold apile; Intros.
forward_call (gv _a_pile, n,sigma,gv).
entailer!. simpl. unfold apile. entailer!.
Qed.

Lemma body_Apile_count: semax_body ApileVprog ApileGprog f_Apile_count Apile_count_spec.
Proof.
start_function.
unfold apile in *; Intros.
forward_call (gv _a_pile, sigma).
forward.
Qed. 

  Definition ApileVSU: @VSU NullExtension.Espec 
      nil apile_imported_specs ltac:(QPprog prog) ApileASI (apile nil) .
  Proof. 
    mkVSU prog apile_internal_specs. 
    + solve_SF_internal body_Apile_add.
    + solve_SF_internal body_Apile_count.
    + apply apile_Init.
  Qed.


