Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat. Import NoOracle.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library. (*for body_lemma_of_funspec *)
Require Import stdlib.
Require Import spec_stdlib.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

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
   PROP() RETURN() SEP().

  Definition MF_ASI: funspecs := MallocFreeASI M.

  Definition MF_imported_specs: funspecs :=  nil.

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
Lemma semax_func_cons_malloc_aux {cs: compspecs} (gv: globals) (ret : option val) z:
  (EX p : val,
   PROP ( )
        RETURN (p)
        SEP (mem_mgr M gv; if eq_dec p nullval then emp else malloc_token' M Ews z p * memory_block Ews z p))%assert
    (make_ext_rval (rettype_of_type (tptr tvoid)) ret) |-- !! is_pointer_or_null (force_val ret).
Proof.
 intros.
 unfold PROPx, RETURNx, SEPx.
 monPred.unseal. Intros p; subst.
 if_tac; entailer!.
Qed.

Definition MF_E : funspecs := MF_ASI.

Definition MallocFreeVSU: VSU
         MF_E MF_imported_specs ltac:(QPprog prog) MF_ASI (mem_mgr M).
  Proof.
    mkVSU prog MF_internal_specs.
    - solve_SF_internal body_placeholder.
    - solve_SF_external body_malloc. 
      Intros. eapply derives_trans.
      destruct x as [n gv].
      apply (semax_func_cons_malloc_aux gv ret n).
      destruct ret; simpl; trivial.
    - solve_SF_external body_free.
    - solve_SF_external body_exit.
    - apply MF_Init.
Qed.
