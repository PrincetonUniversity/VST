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

Lemma onepile_Init: VSU_initializer prog (onepile None).
Proof. InitGPred_tac. normalize. apply data_at_data_at_. Qed.


Definition OnepileVSU: @VSU NullExtension.Espec
      nil onepile_imported_specs ltac:(QPprog prog) OnepileASI (onepile None).
  Proof.
    mkVSU prog onepile_internal_specs. 
    + solve_SF_internal body_Onepile_init.
    + solve_SF_internal body_Onepile_add.
    + solve_SF_internal body_Onepile_count.
    + apply onepile_Init.
  Qed.

