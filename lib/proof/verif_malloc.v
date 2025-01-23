Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library. (*for body_lemma_of_funspec *)
Require Import VSTlib.malloc_extern.
Require Import VSTlib.spec_malloc.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.

#[export] Declare Instance M `{VSTGS_OK: !VSTGS OK_ty Σ} : MallocAPD.


Section GFUNCTORS.
Context `{VSTGS_OK: !VSTGS OK_ty Σ}.
Axiom mem_mgr_rep: forall gv, emp |-- mem_mgr gv.

Parameter body_malloc:
 forall {Espec: ext_spec OK_ty} {cs: compspecs} ,
   VST.floyd.library.body_lemma_of_funspec EF_malloc (snd malloc_spec').

Parameter body_free:
 forall {Espec: ext_spec OK_ty} {cs: compspecs} ,
   VST.floyd.library.body_lemma_of_funspec EF_free (snd free_spec').

(*
Parameter body_exit:
 forall {Espec: ext_spec OK_ty},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "exit" (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
    (snd (exit_spec)).
*)

Definition malloc_placeholder_spec : ident * @funspec Σ :=
 DECLARE _malloc_placeholder
 WITH u: unit
 PRE [ ]
   PROP (False) PARAMS () GLOBALS () SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

  Definition MF_ASI: funspecs := MallocASI.

  Definition MF_imported_specs: @funspecs Σ :=  nil.

  Definition MF_internal_specs: funspecs := malloc_placeholder_spec::MF_ASI.

  Definition MFVprog : varspecs. mk_varspecs prog. Defined.
  Definition MFGprog: funspecs := MF_imported_specs ++ MF_internal_specs.

  Lemma MF_Init: VSU_initializer prog mem_mgr.
  Proof. InitGPred_tac. apply mem_mgr_rep. Qed.

Lemma body_malloc_placeholder: semax_body MFVprog MFGprog f_malloc_placeholder malloc_placeholder_spec.
Proof.
start_function.
contradiction.
Qed.

(*same proof as in library.v, but the statement is a little different*)
Lemma semax_func_cons_malloc_aux {cs: compspecs} (gv: globals) (gx : genviron) (ret : option val) z:
  (EX p : val,
   PROP ( )
        LOCAL (temp ret_temp p)
        SEP (mem_mgr gv; if eq_dec p nullval then emp else malloc_token' Ews z p * memory_block Ews z p))%assert
    (make_ext_rval gx (rettype_of_type (tptr tvoid)) ret) |-- !! is_pointer_or_null (force_val ret).
Proof.
 intros.
 monPred.unseal. Intros p.
 rewrite <- insert_local.
 monPred.unseal.
 apply bi.pure_elim_l; intros (? & ?).
 super_unfold_lift.
 destruct ret; try contradiction.
 unfold eval_id in H. Transparent peq. simpl in H. Opaque peq. subst p.
 if_tac. rewrite H; entailer!.
 renormalize. monPred.unseal. entailer!.
Qed.

Definition MF_E : funspecs := MF_ASI.

Definition MallocVSU `{Espec: ext_spec OK_ty} : 
      VSU MF_E MF_imported_specs ltac:(QPprog prog) MF_ASI mem_mgr.
  Proof. 
    mkVSU prog MF_internal_specs.
    - solve_SF_internal body_malloc_placeholder.
    - solve_SF_external body_malloc.
      destruct x as [n gv].
      Intros. eapply derives_trans.
      apply (semax_func_cons_malloc_aux gv gx ret n).
      destruct ret; simpl; trivial.
    - solve_SF_external body_free.
    - apply MF_Init.
Qed.

End GFUNCTORS.

