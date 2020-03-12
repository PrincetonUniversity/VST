Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import apile.
Require Import spec_stdlib.
Require Import spec_pile.
Require Import spec_pile_private.
Require Import spec_apile.

Instance APileCompSpecs : compspecs. make_compspecs prog. Defined.

Section Apile_VSU.
Variable M: MemMGRPredicates.
Variable PILEPRIV: PilePrivatePredicates M. (*apile is parametric in a PRIVATE pile predicate structure*)

Definition apile (gv: globals) (sigma: list Z) : mpred :=
  pilerep PILEPRIV sigma (gv _a_pile).
(*We define apile in terms of pilerep and then,
  in the proof of make_apile below, use the axiom
  spec_pile_private.pile_rep_exposed 
  to exploit the representation exposure*)

Lemma make_apile: forall gv, 
  headptr (gv apile._a_pile) ->
  data_at Ews tuint (Vint (Int.repr 0))
          (gv apile._a_pile) |-- apile gv nil.
Proof.
intros. unfold apile. rewrite pile_rep_exposed. (*HERE*) 
unfold prep. 
 Exists (Vint (Int.repr 0)).
 unfold listrep. entailer!.
 unfold_data_at (data_at _ spec_pile.tpile _ _).
 rewrite field_at_data_at. simpl.
 rewrite field_compatible_field_address
   by auto with field_compatible.
 simpl. normalize.
 rewrite <- data_at_nullptr.
 cancel.
Qed.

Definition APILE: APilePredicates := Build_APilePredicates apile APileCompSpecs make_apile.

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

  Definition ApileComponent: @Component NullExtension.Espec ApileVprog _ 
      nil apile_imported_specs prog Apile_ASI apile_internal_specs.
  Proof. 
    mkComponent. 
    + solve_SF_internal body_Apile_add.
    + solve_SF_internal body_Apile_count.
  Qed.

Definition ApileVSU: @VSU NullExtension.Espec ApileVprog _ 
      nil apile_imported_specs prog Apile_ASI.
  Proof. eexists; apply ApileComponent. Qed.
End Apile_VSU.

