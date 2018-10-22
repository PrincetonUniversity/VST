Require Import VST.floyd.base2.
Require Import VST.floyd.sublist.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.compare_lemmas.
Require Import VST.floyd.semax_tactics.
Require Import VST.floyd.forward.
Require Import VST.floyd.call_lemmas.
Require Import VST.floyd.forward_lemmas.
Require Import VST.floyd.for_lemmas.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.aggregate_type.
Require VST.floyd.aggregate_pred. Import VST.floyd.aggregate_pred.aggregate_pred.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.field_compat.
Require Import VST.floyd.stronger.
Require Import VST.floyd.loadstore_mapsto.
Require Import VST.floyd.loadstore_field_at.
Require Import VST.floyd.nested_loadstore.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Require Import VST.floyd.sc_set_load_store.
(*Require Import VST.floyd.unfold_data_at.*)
Require Import VST.floyd.entailer.
Require Import VST.floyd.globals_lemmas.
Require Import VST.floyd.diagnosis.
Require Import VST.floyd.freezer.
Import ListNotations.
Import String.

Definition body_lemma_of_funspec  {Espec: OracleKind} (ef: external_function) (f: funspec) :=
  match f with mk_funspec sig _ A P Q _ _ =>
    semax_external (map fst (fst sig)) ef A P Q
  end.

Definition try_spec  (name: string) (spec: funspec) : 
   list (ident * globdef Clight.fundef type) -> list (ident*funspec) :=
fun defs => 
 match ext_link_prog' defs name with
 | Some id => [(id,spec)]
 | None => nil
 end.
Arguments try_spec name spec defs / .

Definition exit_spec' :=
 WITH u: unit
 PRE [1%positive OF tint]
   PROP () LOCAL() SEP()
 POST [ tvoid ]
   PROP(False) LOCAL() SEP().

Definition exit_spec := try_spec "exit" exit_spec'.

Parameter body_exit:
 forall {Espec: OracleKind},
  body_lemma_of_funspec
    (EF_external "exit"
       {| sig_args := AST.Tint :: nil; sig_res := None; sig_cc := cc_default |})
   exit_spec'.

Parameter malloc_token : forall {cs: compspecs}, share -> type -> val -> mpred.
Parameter malloc_token_valid_pointer:
  forall {cs: compspecs} sh t p, malloc_token sh t p |-- valid_pointer p.
Hint Resolve malloc_token_valid_pointer : valid_pointer.

Parameter malloc_token_local_facts:
  forall {cs: compspecs} sh t p, malloc_token sh t p |-- !! malloc_compatible (sizeof t) p.
Hint Resolve malloc_token_local_facts : saturate_local.
Parameter malloc_token_change_composite: forall {cs_from cs_to} {CCE : change_composite_env cs_from cs_to} sh t,
  cs_preserve_type cs_from cs_to (coeq cs_from cs_to) t = true ->
  @malloc_token cs_from sh t = @malloc_token cs_to sh t.
Ltac change_compspecs' cs cs' ::=
  match goal with
  | |- context [@data_at cs' ?sh ?t ?v1] => erewrite (@data_at_change_composite cs' cs _ sh t); [| apply JMeq_refl | reflexivity]
  | |- context [@field_at cs' ?sh ?t ?gfs ?v1] => erewrite (@field_at_change_composite cs' cs _ sh t gfs); [| apply JMeq_refl | reflexivity]
  | |- context [@data_at_ cs' ?sh ?t] => erewrite (@data_at__change_composite cs' cs _ sh t); [| reflexivity]
  | |- context [@field_at_ cs' ?sh ?t ?gfs] => erewrite (@field_at__change_composite cs' cs _ sh t gfs); [| reflexivity]
  | |- context [@malloc_token cs' ?sh ?t] => erewrite (@malloc_token_change_composite cs' cs _ sh t); [| reflexivity]
  | |- context [?A cs'] => change (A cs') with (A cs)
  | |- context [?A cs' ?B] => change (A cs' B) with (A cs B)
  | |- context [?A cs' ?B ?C] => change (A cs' B C) with (A cs B C)
  | |- context [?A cs' ?B ?C ?D] => change (A cs' B C D) with (A cs B C D)
  | |- context [?A cs' ?B ?C ?D ?E] => change (A cs' B C D E) with (A cs B C D E)
  | |- context [?A cs' ?B ?C ?D ?E ?F] => change (A cs' B C D E F) with (A cs B C D E F)
 end.
(*
Parameter malloc_token_precise:
  forall {cs: compspecs} sh t p, predicates_sl.precise (malloc_token sh t p).
*)
Definition malloc_spec'  {cs: compspecs} :=
   WITH t:type
   PRE [ 1%positive OF size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       LOCAL (temp 1%positive (Vptrofs (Ptrofs.repr (sizeof t))))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (if eq_dec p nullval then emp
            else (malloc_token Ews t p * data_at_ Ews t p)).

Parameter body_malloc:
 forall {Espec: OracleKind} {cs: compspecs} ,
  body_lemma_of_funspec EF_malloc malloc_spec'.

Definition free_spec'  {cs: compspecs} :=
   WITH t: type, p:val
   PRE [ 1%positive OF tptr tvoid ]
       PROP ()
       LOCAL (temp 1%positive p)
       SEP (malloc_token Ews t p; data_at_ Ews t p)
    POST [ Tvoid ]
       PROP ()
       LOCAL ()
       SEP ().

Parameter body_free:
 forall {Espec: OracleKind} {cs: compspecs} ,
  body_lemma_of_funspec EF_free free_spec'.

Definition library_G  {cs: compspecs} prog :=
 let defs := prog_defs prog in 
  try_spec "exit" exit_spec' defs ++
  try_spec "_malloc" malloc_spec' defs ++
  try_spec "_free" free_spec' defs.

Ltac with_library prog G :=
  let pr := eval unfold prog in prog in  
 let x := constr:(library_G pr ++ G) in
  let x := eval cbv beta delta [app library_G] in x in
  let x := simpl_prog_defs x in 
  let x := eval cbv beta iota zeta delta [try_spec] in x in 
  let x := eval simpl in x in 
    with_library' pr x.

Lemma semax_func_cons_malloc_aux:
  forall {cs: compspecs} (gx : genviron) (t :type) (ret : option val),
(EX p : val,
 PROP ( )
 LOCAL (temp ret_temp p)
 SEP (if eq_dec p nullval
      then emp
      else malloc_token Ews t p * data_at_ Ews t p))%assert
  (make_ext_rval gx ret) |-- !! is_pointer_or_null (force_val ret).
Proof.
 intros.
 rewrite exp_unfold. Intros p.
 rewrite <- insert_local.
 rewrite lower_andp.
 apply derives_extract_prop; intro.
 destruct H; unfold_lift in H. rewrite retval_ext_rval in H.
 subst p.
 if_tac. rewrite H; entailer!.
 renormalize. entailer!.
Qed.
