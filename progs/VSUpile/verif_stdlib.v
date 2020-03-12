Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library. (*for body_lemma_of_funspec *)
Require Import stdlib.
Require Import spec_stdlib.
(*
Definition prog := ltac:
  (let x := eval hnf in prog in
   let x := eval simpl in x in 
   let x := eval compute in x in 
       exact x).*)

Instance CompSpecs : compspecs. make_compspecs prog. Defined.

(*For now, we axiomatize the existence of a MemMGRPredicate structure*)
Parameter M: MemMGRPredicates.
(*
Definition myExit_spec := try_spec "exit" (snd spec_stdlib.exit_spec) (prog_defs prog).*)

Parameter body_malloc:
 forall {Espec: OracleKind} {cs: compspecs} ,
   VST.floyd.library.body_lemma_of_funspec EF_malloc (snd (malloc_spec' M)).

Parameter body_free:
 forall {Espec: OracleKind} {cs: compspecs} ,
   VST.floyd.library.body_lemma_of_funspec EF_free (snd (free_spec' M)).

Parameter body_exit:
 forall {Espec: OracleKind},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "exit"
       {| sig_args := AST.Tint :: nil; sig_res := None; sig_cc := cc_default |})
    (snd (exit_spec)).

Section MM_VSU.
Definition placeholder_spec :=
 DECLARE _placeholder
 WITH u: unit
 PRE [ ]
   PROP (False) PARAMS () GLOBALS () SEP()
 POST [ tint ]
   PROP() LOCAL() SEP().

  Definition MM_ASI: funspecs := MMASI M.

  Definition MM_imported_specs:funspecs :=  nil.

  Definition MM_internal_specs: funspecs := placeholder_spec::MM_ASI.

  Definition MMVprog : varspecs. mk_varspecs prog. Defined.
  Definition MMGprog: funspecs := MM_imported_specs ++ MM_internal_specs.

Lemma body_placeholder: semax_body MMVprog MMGprog f_placeholder placeholder_spec.
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
    (make_ext_rval gx ret) |-- !! is_pointer_or_null (force_val ret).
Proof.
 rewrite exp_unfold. Intros p.
 rewrite <- insert_local.
 rewrite lower_andp.
 apply derives_extract_prop; intro.
 destruct H; unfold_lift in H. rewrite retval_ext_rval in H.
 subst p.
 if_tac. rewrite H; entailer!.
 renormalize. entailer!.
Qed.

(*Existing Instance NullExtension.Espec.*)
(*
Lemma tcret_malloc: 
tcret_proof (tptr tvoid) (rmaps.ConstType (Z * globals))
  (fun (_ : list Type) (x : Z * globals) =>
   let (n, gv) := x in
   (EX p : val,
    PROP ( )
    LOCAL (temp ret_temp p)
    SEP (mem_mgr gv;
    if @eq_dec val Memory.EqDec_val p nullval
    then @emp mpred Nveric Sveric
    else malloc_token' Ews n p * memory_block Ews n p))%assert).
Proof.
red; intros.
destruct x.
 rewrite exp_unfold. Intros p.
 rewrite <- insert_local.
 rewrite lower_andp.
 red in H. simpl in H. destruct ret; try contradiction. clear H.
 apply derives_extract_prop; intro.
 destruct H; unfold_lift in H.  rewrite retval_ext_rval in H. simpl in H. subst p.
 unfold_lift in H0. 
 if_tac. rewrite H; entailer!.
 renormalize. entailer!. simpl. auto.
Qed.
Lemma tcret_free:
   tcret_proof tvoid (rmaps.ConstType (Z * val * globals))
  (fun (_ : list Type) (x : Z * val * globals) =>
   let (p0, gv) := x in
   let (_, _) := p0 in PROP ( )  LOCAL ()  SEP (mem_mgr gv)).
Proof.
hnf; intros; normalize.
Qed.


Lemma tcret_exit: 
  tcret_proof tvoid (rmaps.ConstType Z)
  (fun (_ : list Type) (_ : Z) => PROP (False)  LOCAL ()  SEP ()).
Proof.
hnf; intros; normalize.
Qed.*)

(*Maybe we should add the specs for malloc, free, exit, also into the E argument?
  Maybe the type of the E argument should not be funspecs, but 
   external_function * funspec)?*)

  Definition MM_E : funspecs := MM_ASI.

  Definition MMComponent: @Component NullExtension.Espec MMVprog CompSpecs 
      (*nil*)MM_E MM_imported_specs prog MM_ASI MM_internal_specs.
  Proof. 
    mkComponent. 
    - clear; solve_SF_external (@body_malloc NullExtension.Espec CompSpecs). 
      destruct x as [a gv]. apply andp_left1. eapply derives_trans.
      apply (semax_func_cons_malloc_aux gv(*b*) gx ret a).
      destruct ret; simpl; trivial.
    - clear; solve_SF_external (@body_free NullExtension.Espec CompSpecs).
    - clear; solve_SF_external (@body_exit NullExtension.Espec).
    - clear; solve_SF_internal body_placeholder.
Time  Qed. (*2.5s*)

Definition MMVSU: @VSU NullExtension.Espec MMVprog CompSpecs 
      (*nil*)MM_E MM_imported_specs prog MM_ASI.
  Proof. eexists; apply MMComponent. Qed.
End MM_VSU.


