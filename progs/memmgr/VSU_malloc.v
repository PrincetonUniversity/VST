Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.

Require Import ASI_malloc.
Require Import malloc_lemmas.
Require Import malloc_sep.
Require Import VSU_malloc_definitions.

Require Import verif_malloc_free.
Require Import verif_bin2size2bin.
Require Import verif_list_from_block.
Require Import verif_fill_bin.
Require Import verif_malloc_small.
Require Import verif_malloc_large.
Require Import verif_free_small.
Require Import verif_free_large.
Require Import verif_pre_fill.
Require Import verif_try_pre_fill.

  Lemma create_memmgr_R: VSU_initializer malloc.prog (mem_mgr_R emptyResvec).
  Proof. InitGPred_tac.
    eapply derives_trans. 2: apply create_mem_mgr_R. entailer!.
  Qed. 
(*Old proof
Lemma create_memmgr_R gv: InitGPred (Vardefs malloc.prog) gv |-- mem_mgr_R emptyResvec gv.
Proof. unfold Vardefs. simpl. unfold InitGPred. simpl; Intros. rewrite sepcon_emp.
    eapply derives_trans. 2: apply create_mem_mgr_R. entailer!.
    unfold globvar2pred. simpl.
(*    unfold initialize.gv_globvar2pred. simpl.
         unfold initialize.gv_lift2, initialize.gv_lift0; simpl.
         rewrite predicates_sl.sepcon_emp. *) rewrite sepcon_emp.
    destruct HP_bin as [b Hb]; rewrite Hb in *; clear.
    eapply derives_trans. 
    2:{ apply (mapsto_zeros_data_atTarrayTptr_nullval_N 50%nat Ews tvoid b Ptrofs.zero).
        apply writable_readable; apply writable_Ews.
        apply Z.divide_0_r. }
    apply derives_refl.
Qed.*)

  Definition MF_R_VSU: @VSU NullExtension.Espec 
      nil MF_Imports ltac:(QPprog malloc.prog)
      (Malloc_R_ASI R_APD malloc._pre_fill malloc._try_pre_fill malloc._malloc malloc._free)
      (mem_mgr_R emptyResvec).
  Proof.
    mkVSU malloc.prog MF_internal_specs.
  + solve_SF_internal body_malloc_large.
  + solve_SF_internal body_malloc_small.
  + solve_SF_internal body_free_large.
  + solve_SF_internal body_free_small.
  + solve_SF_internal body_bin2size.
  + solve_SF_internal body_size2bin.
  + solve_SF_internal body_list_from_block.
  + solve_SF_internal body_fill_bin.
  + solve_SF_internal body_pre_fill.
  + solve_SF_internal body_try_pre_fill.
  + solve_SF_internal body_malloc.
  + solve_SF_internal body_free.
  + apply create_memmgr_R.
  Qed.

  Definition MF_VSU: @VSU NullExtension.Espec 
      nil MF_Imports ltac:(QPprog malloc.prog)
      (Malloc_ASI (ForgetR R_APD) malloc._malloc malloc._free) (mem_mgr (ForgetR R_APD)).
  Proof.
    eapply VSU_entail.
    + eapply VSU_Exports_sub.
      - apply MF_R_VSU.
      - LNR_tac.
      - apply MallocASI_sqsub_MallocR_ASI.
        LNR_tac. 
    + intros; simpl. Exists emptyResvec; trivial.
  Qed.