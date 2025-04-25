Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat. Import NoOracle.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library. (*for body_lemma_of_funspec *)
Require Import stdlib.
Require Import spec_stdlib.

Require VST.veric.version. From Coq Require Import String.
Lemma version_test: False.
 assert (VST.veric.version.compcert_version = "3.15"%string /\
         stdlib.Info.version = "3.15"%string)
       by (compute; auto;
            match goal with |- ?G => fail 100 "Version mismatch; cannot prove" G end).
 assert (VST.veric.version.bitsize = stdlib.Info.bitsize) by
    (try reflexivity; match goal with |- ?G => fail 100 "Bitsize mismatch; cannot prove" G end).
Abort.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Parameter M: MallocFreeAPD.

Axiom mem_mgr_rep: forall gv, emp |-- mem_mgr M gv.

Parameter body_malloc:
   VST.floyd.library.body_lemma_of_funspec EF_malloc (snd (malloc_spec' M)).

Parameter body_free:
   VST.floyd.library.body_lemma_of_funspec EF_free (snd (free_spec' M)).

Parameter body_exit:
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "exit" (mksignature (Xint :: nil) Xvoid cc_default))
    (snd (exit_spec)).

Definition placeholder_spec :=
 DECLARE _placeholder
 WITH u: unit
 PRE [ ]
   PROP (False) PARAMS () GLOBALS () SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

  Definition MF_ASI: funspecs := MallocFreeASI M.

  Definition MF_imported_specs:funspecs :=  nil.

  Definition MF_internal_specs: funspecs := placeholder_spec::MF_ASI.

  Definition MFVprog : varspecs. mk_varspecs prog. Defined.
  Definition MFGprog: funspecs := MF_imported_specs ++ MF_internal_specs.

  Lemma MF_Init: VSU_initializer prog (mem_mgr M).
  Proof. InitGPred_tac. apply mem_mgr_rep. Qed.

Lemma body_placeholder: semax_body MFVprog MFGprog f_placeholder placeholder_spec.
Proof.
start_function.
contradiction.
Qed.

(*same proof as in library.v, but the statement is a little different*)
Lemma semax_func_cons_malloc_aux {cs: compspecs} (gv: globals) (gx : genviron) (ret : option val) z:
  (EX p : val,
   PROP ( )
        LOCAL (temp ret_temp p)
        SEP (mem_mgr M gv; if eq_dec p nullval then emp else malloc_token' M Ews z p * memory_block Ews z p))%assert
    (make_ext_rval gx (rettype_of_type (tptr tvoid)) ret) |-- !! is_pointer_or_null (force_val ret).
Proof.
 intros.
 monPred.unseal. Intros p.
 rewrite <- insert_local.
 monPred.unseal.
 apply bi.pure_elim_l; intro.
 destruct H; unfold_lift in H.
 unfold_lift in H0. destruct ret; try contradiction.
 unfold eval_id in H. simpl in H. subst p.
 if_tac. rewrite H; entailer!.
 renormalize. monPred.unseal. entailer!.
Qed.


Definition MF_E : funspecs := MF_ASI.

Definition MallocFreeVSU: VSU
         MF_E MF_imported_specs ltac:(QPprog prog) MF_ASI (mem_mgr M).
  Proof.
    mkVSU prog MF_internal_specs.
    - solve_SF_internal body_placeholder.
    - solve_SF_external body_malloc.
      destruct x; simpl.
      Intros. eapply derives_trans.
      apply semax_func_cons_malloc_aux.
      destruct ret; simpl; trivial.
    - solve_SF_external body_free.
    - solve_SF_external body_exit.
    - apply MF_Init.
Qed.
