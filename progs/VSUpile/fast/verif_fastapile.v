Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import fastapile.
Require Import spec_stdlib.
Require Import spec_fastpile.
Require Import spec_fastpile_private.
Require Import spec_apile.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Section Apile_VSU.
Variable M: MallocFreeAPD.
Variable PILEPRIV: FastpilePrivateAPD. (*apile is parametric in a PRIVATE pile predicate structure*)

Definition apile (sigma: list Z) (gv: globals) : mpred :=
  pilerep PILEPRIV sigma (gv _a_pile).
(*We define apile in terms of pilerep and then,
  in the proof of make_apile below, use the axiom
  spec_pile_private.pile_rep_exposed 
  to exploit the representation exposure*)

Lemma make_apile: forall gv, 
  globals_ok gv ->
  data_at Ews tuint (Vint (Int.repr 0)) (gv apile._a_pile) |-- apile nil gv.
Proof.
intros. unfold apile. rewrite pile_rep_exposed. (*HERE*) 
unfold fastprep.
 Exists 0.
 assert_PROP (headptr (gv _a_pile)) by entailer!.
 entailer!. 
 unfold_data_at (data_at _ tpile _ _).
 rewrite field_at_data_at. simpl.
 rewrite field_compatible_field_address
   by auto with field_compatible.
 simpl. normalize. rewrite data_at_tuint_tint.
assert (change_composite_env CompSpecs FastpileCompSpecs).
{ make_cs_preserve CompSpecs FastpileCompSpecs. }
change_compspecs FastpileCompSpecs.
apply derives_refl.
Qed.

Lemma apile_Init: VSU_initializer prog (apile nil).
  Proof. 
    InitGPred_tac.  rewrite sepcon_emp.
    apply make_apile; auto.
Qed.


Definition APILE: APileAPD := Build_APileAPD apile (*APileCompSpecs make_apile*).

Definition Apile_ASI: funspecs := ApileASI M APILE.

Definition apile_imported_specs:funspecs := 
     [ Pile_add_spec M PILEPRIV; Pile_count_spec PILEPRIV].

Definition apile_internal_specs: funspecs := Apile_ASI.

Definition ApileVprog: varspecs. mk_varspecs prog. Defined.
Definition ApileGprog: funspecs := apile_imported_specs ++ apile_internal_specs.

Lemma body_Apile_add: semax_body ApileVprog ApileGprog f_Apile_add (Apile_add_spec M APILE).
Proof.
start_function. 
simpl spec_apile.apile. unfold apile.
forward_call (gv _a_pile, n,sigma,gv).
entailer!.
Qed.

Lemma body_Apile_count: semax_body ApileVprog ApileGprog f_Apile_count (Apile_count_spec M APILE).
Proof.
start_function.
simpl spec_apile.apile. unfold apile in *.
forward_call (gv _a_pile, sigma).
forward.
Qed.

Definition ApileVSU: @VSU NullExtension.Espec 
      nil apile_imported_specs ltac:(QPprog prog) Apile_ASI (apile nil).
  Proof. 
    mkVSU prog apile_internal_specs.
    + solve_SF_internal body_Apile_add.
    + solve_SF_internal body_Apile_count.
    + apply apile_Init.
  Qed.

End Apile_VSU.

