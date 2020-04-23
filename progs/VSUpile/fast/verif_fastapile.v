Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import fastapile.
Require Import spec_stdlib.
Require Import spec_fastpile.
Require Import spec_fastpile_private.
Require Import spec_apile.

Instance APileCompSpecs : compspecs. make_compspecs prog. Defined.

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
  headptr (gv apile._a_pile) ->
  @data_at APileCompSpecs Ews tuint (Vint (Int.repr 0))
          (gv fastapile._a_pile) |-- apile nil gv.
Proof.
intros. unfold apile. rewrite pile_rep_exposed. (*HERE*) 
unfold fastprep. 
 Exists 0.
 entailer!. 
 unfold_data_at (data_at _ tpile _ _).
 rewrite field_at_data_at. simpl.
 rewrite field_compatible_field_address
   by auto with field_compatible.
 simpl. normalize. rewrite data_at_tuint_tint.
assert (change_composite_env APileCompSpecs FastpileCompSpecs).
{ make_cs_preserve APileCompSpecs FastpileCompSpecs. }
change_compspecs FastpileCompSpecs. trivial.
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

  Lemma MyInitData gv (H: headptr (gv _a_pile)):
        initialize.gv_globvar2pred gv (_a_pile, v_a_pile) gv 
        |-- apile nil gv.
  Proof. eapply derives_trans. 2: apply (make_apile _ H).
         unfold initialize.gv_globvar2pred, apile. simpl.
         unfold initialize.gv_lift2, initialize.gv_lift0; simpl.
         rewrite predicates_sl.sepcon_emp. forget (gv _a_pile) as p.
         erewrite <- (mapsto_data_at'' Ews); trivial. apply derives_refl. 
  Qed.

  Lemma apile_Init gv: InitGPred (Vardefs prog) gv |-- apile nil gv.
  Proof. unfold InitGPred. simpl; Intros. sep_apply MyInitData; trivial. Qed.

  Definition ApileComponent: @Component NullExtension.Espec ApileVprog _ 
      nil apile_imported_specs prog Apile_ASI (apile nil) apile_internal_specs.
  Proof. 
    mkComponent. 
    + solve_SF_internal body_Apile_add.
    + solve_SF_internal body_Apile_count.
    + sep_apply apile_Init; simpl; cancel.
  Qed.

Definition ApileVSU: @VSU NullExtension.Espec ApileVprog _ 
      nil apile_imported_specs prog Apile_ASI (apile nil).
  Proof. eexists; apply ApileComponent. Qed.
End Apile_VSU.