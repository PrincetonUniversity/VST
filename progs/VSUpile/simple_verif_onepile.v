Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import onepile.
Require Import simple_spec_stdlib.
Require Import simple_spec_pile.
Require Import simple_spec_onepile.

  Definition onepile_imported_specs:funspecs := 
     [ Pile_new_spec; Pile_add_spec; Pile_count_spec].

  Definition onepile_internal_specs: funspecs := OnepileASI.

  Definition OnepileVprog: varspecs. mk_varspecs prog. Defined.
  Definition OnepileGprog: funspecs := onepile_imported_specs ++ onepile_internal_specs.

Lemma body_Onepile_init: semax_body OnepileVprog OnepileGprog f_Onepile_init Onepile_init_spec.
Proof.
start_function.
forward_call gv.
Intros p.
unfold onepile.
forward.
unfold onepile.
Exists p.
entailer!.
Qed.

Lemma body_Onepile_add: semax_body OnepileVprog OnepileGprog f_Onepile_add Onepile_add_spec.
Proof.
start_function.
unfold onepile.
Intros p.
forward.
forward_call (p,n,sigma,gv).
forward.
unfold onepile.
Exists p.
entailer!.
Qed.

Lemma body_Onepile_count: semax_body OnepileVprog OnepileGprog f_Onepile_count Onepile_count_spec.
Proof.
start_function.
unfold onepile.
Intros p.
forward.
forward_call (p,sigma).
forward.
Exists p.
entailer!.
Qed.


Lemma make_onepile: forall gv,
  data_at_ Ews (tptr (Tstruct onepile._pile noattr)) (gv onepile._the_pile)
   |-- onepile None gv.
Proof.
intros. cancel.
Qed.

  Lemma onepile_Init_aux gv: headptr (gv _the_pile) ->
    globvar2pred gv (_the_pile, v_the_pile)
    |-- data_at_ Ews (tptr (Tstruct _pile noattr)) (gv _the_pile).
  Proof. intros.
    unfold globvar2pred. simpl.
         rewrite sepcon_emp.
    destruct H as [b Hb]; rewrite Hb in *.
    eapply derives_trans. 
    + apply mapsto_zeros_memory_block. apply writable_readable. apply writable_Ews.
    + rewrite <- memory_block_data_at_; simpl; trivial.
      apply headptr_field_compatible; trivial. exists b; trivial. cbv; trivial. simpl; rep_lia.
      econstructor. reflexivity. apply Z.divide_0_r.
  Qed.

  Lemma onepile_Init_aux2 gv: headptr (gv _the_pile) ->
    globvar2pred gv (_the_pile, v_the_pile)
    |--  onepile None gv.
  Proof. intros. sep_apply onepile_Init_aux. apply make_onepile; trivial. Qed.

  Lemma onepile_Init gv: InitGPred (Vardefs prog) gv |-- onepile None gv.
  Proof. unfold InitGPred. simpl; Intros. sep_apply onepile_Init_aux2; trivial. simpl. trivial. Qed.

  Definition OnepileComponent: @Component NullExtension.Espec OnepileVprog _ 
      nil onepile_imported_specs prog OnepileASI (onepile None) onepile_internal_specs.
  Proof.
    mkComponent. 
    + solve_SF_internal body_Onepile_init.
    + solve_SF_internal body_Onepile_add.
    + solve_SF_internal body_Onepile_count.
    + sep_apply onepile_Init; simpl; cancel.
  Qed.

Definition OnepileVSU: @VSU NullExtension.Espec OnepileVprog _ 
      nil onepile_imported_specs prog OnepileASI (onepile None).
  Proof. eexists; apply OnepileComponent. Qed.
