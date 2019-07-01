Require Import VST.floyd.proofauto.
Require Import linking.
Require VST.floyd.library.
Require Import spec_stdlib.

Parameter body_malloc:
 forall {Espec: OracleKind} {cs: compspecs} ,
   VST.floyd.library.body_lemma_of_funspec EF_malloc (snd malloc_spec').

Parameter body_free:
 forall {Espec: OracleKind} {cs: compspecs} ,
   VST.floyd.library.body_lemma_of_funspec EF_free (snd free_spec').

Parameter body_exit:
 forall {Espec: OracleKind},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "exit"
       {| sig_args := AST.Tint :: nil; sig_res := None; sig_cc := cc_default |})
    (snd exit_spec).

Definition Gprog : funspecs :=   
   spec_stdlib.specs ++ spec_stdlib.ispecs.

Lemma body_placeholder: semax_body Vprog Gprog stdlib.f_placeholder spec_stdlib.placeholder_spec.
Proof.
start_function.
contradiction.
Qed.

(*same proof as in library.v, but the statement is a little different*)
Lemma semax_func_cons_malloc_aux {cs: compspecs} (gv: globals) (gx : genviron) (ret : option val) z:
  (EX p : val,
   PROP ( )
        LOCAL (temp ret_temp p)
        SEP (spec_stdlib.mem_mgr gv; if eq_dec p nullval then emp else malloc_token' Ews z p * memory_block Ews z p))%assert
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

Existing Instance NullExtension.Espec.


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
  tcret_proof tvoid (rmaps.ConstType unit)
  (fun (_ : list Type) (_ : unit) => PROP (False)  LOCAL ()  SEP ()).
Proof.
hnf; intros; normalize.
Qed.

Definition module : list semax_body_proof :=
 [mk_external stdlib._malloc (tptr tvoid) tcret_malloc body_malloc;
  mk_external stdlib._free tvoid tcret_free body_free;
  mk_external stdlib._exit tvoid tcret_exit body_exit;
  mk_body body_placeholder].

