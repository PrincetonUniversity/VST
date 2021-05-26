Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import apile.
Require Import spec_stdlib.
Require Import spec_pile.
Require Import spec_pile_private.
Require Import spec_apile.

Instance APileCompSpecs : compspecs. make_compspecs prog. Defined.

Section Apile_VSU.
Variable M: MallocFreeAPD.
Variable PILEPRIV: PilePrivateAPD M. (*apile is parametric in a PRIVATE pile predicate structure*)

Definition apile (sigma: list Z) (gv: globals): mpred :=
  !!(headptr (gv _a_pile)) && pilerep PILEPRIV sigma (gv _a_pile).
(*We define apile in terms of pilerep and then,
  in the proof of make_apile below, use the axiom
  spec_pile_private.pile_rep_exposed 
  to exploit the representation exposure*)

Lemma make_apile: forall gv, 
  globals_ok gv ->
  data_at Ews size_t nullval (gv apile._a_pile) |-- apile nil gv.
Proof.
intros. unfold apile. rewrite pile_rep_exposed. (*HERE*) 
unfold prep.
assert_PROP (headptr (gv _a_pile)) by entailer!.
Exists nullval.
unfold listrep. entailer!.
unfold_data_at (data_at _ spec_pile.tpile _ _).
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

Definition APILE: APileAPD := Build_APileAPD apile (*APileCompSpecs make_apile*) (*_ apile_Init*).

  Definition Apile_ASI: funspecs := ApileASI M APILE.

  Definition apile_imported_specs:funspecs := 
     [ Pile_add_spec M PILEPRIV; Pile_count_spec PILEPRIV].

  Definition apile_internal_specs: funspecs := Apile_ASI.

  Definition ApileVprog: varspecs. mk_varspecs prog. Defined.
  Definition ApileGprog: funspecs := apile_imported_specs ++ apile_internal_specs.

Lemma body_Apile_add: semax_body ApileVprog ApileGprog f_Apile_add (Apile_add_spec M APILE).
Proof.
start_function.
simpl spec_apile.apile. unfold apile; Intros.
forward_call (gv _a_pile, n,sigma,gv).
entailer!. simpl. unfold apile. entailer!.
Qed.

Lemma body_Apile_count: semax_body ApileVprog ApileGprog f_Apile_count (Apile_count_spec M APILE).
Proof.
start_function.
simpl spec_apile.apile. unfold apile in *; Intros.
forward_call (gv _a_pile, sigma).
forward.
entailer!. simpl. unfold apile. entailer!.
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
