Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import apile.
Require Import simple_spec_stdlib.
Require Import simple_spec_pile.
Require Import simple_spec_apile.

Lemma make_apile: forall gv, headptr (gv _a_pile) ->
    @data_at APileCompSpecs Ews tuint (Vint (Int.repr 0))
          (gv _a_pile) |-- apile nil gv.
Proof.
intros. unfold apile, pilerep.
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

  Lemma MyInitData gv (H: headptr (gv _a_pile)):
        initialize.gv_globvar2pred gv (_a_pile, v_a_pile)
        |-- apile nil gv.
  Proof.
  eapply derives_trans; [ | apply make_apile; auto].
  unfold initialize.gv_globvar2pred, apile. simpl.
  rewrite predicates_sl.sepcon_emp. forget (gv _a_pile) as p.
  erewrite <- (mapsto_data_at'' Ews); auto.
  apply derives_refl.
  Qed.

  Lemma apile_Init gv: InitGPred (Vardefs prog) gv |-- apile nil gv.
  Proof. unfold InitGPred. simpl; Intros. rewrite sepcon_emp.  apply MyInitData; trivial. Qed.

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

  Definition ApileComponent: @Component NullExtension.Espec ApileVprog _ 
      nil apile_imported_specs prog ApileASI (apile nil) apile_internal_specs.
  Proof. 
    mkComponent. 
    + solve_SF_internal body_Apile_add.
    + solve_SF_internal body_Apile_count.
    + intros. unfold InitGPred; simpl. rewrite sepcon_emp. Intros.
      sep_apply MyInitData. cancel.
  Qed.

Definition ApileVSU: @VSU NullExtension.Espec ApileVprog _ 
      nil apile_imported_specs prog ApileASI (apile nil).
  Proof. eexists; apply ApileComponent. Qed.


