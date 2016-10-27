Require Import floyd.base.
Require Import floyd.sublist.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.compare_lemmas.
Require Import floyd.semax_tactics.
Require Import floyd.forward.
Require Import floyd.call_lemmas.
Require Import floyd.forward_lemmas.
Require Import floyd.for_lemmas.
Require Import floyd.nested_pred_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.efield_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.aggregate_type.
Require floyd.aggregate_pred. Import floyd.aggregate_pred.aggregate_pred.
Require Import floyd.reptype_lemmas.
Require Import floyd.data_at_rec_lemmas.
Require Import floyd.field_at.
Require Import floyd.field_compat.
Require Import floyd.stronger.
Require Import floyd.loadstore_mapsto.
Require Import floyd.loadstore_field_at.
Require Import floyd.nested_loadstore.
Require Import floyd.local2ptree.
Require Import floyd.proj_reptype_lemmas.
Require Import floyd.replace_refill_reptype_lemmas.
Require Import floyd.sc_set_load_store.
(*Require Import floyd.unfold_data_at.*)
Require Import floyd.entailer.
Require Import floyd.globals_lemmas.
Require Import floyd.diagnosis.
Require Import floyd.freezer.
Import ListNotations.

Definition body_lemma_of_funspec  {Espec: OracleKind} (ef: external_function) (f: funspec) :=
  match f with mk_funspec sig _ A P Q =>
    semax_external (map fst (fst sig)) ef A P Q
  end.

Definition exit_spec' := 
 WITH u: unit
 PRE [1%positive OF tint]
   PROP () LOCAL() SEP()
 POST [ tvoid ]
   PROP(False) LOCAL() SEP().

Definition exit_spec (prog: program) :=
 DECLARE (ext_link_prog prog "exit") exit_spec'.

Parameter body_exit:
 forall {Espec: OracleKind}, 
  body_lemma_of_funspec 
    (EF_external "exit"
       {| sig_args := AST.Tint :: nil; sig_res := None; sig_cc := cc_default |})
   exit_spec'.

Parameter malloc_token : share -> Z -> val -> mpred.
Parameter malloc_token_valid_pointer:
  forall sh n p, malloc_token sh n p |-- valid_pointer p.
Hint Resolve malloc_token_valid_pointer : valid_pointer.
Parameter malloc_token_local_facts:
  forall sh n p, malloc_token sh n p |-- !! malloc_compatible n p.
Hint Resolve malloc_token_local_facts : saturate_local.

Definition malloc_spec' :=
   WITH n:Z
   PRE [ 1%positive OF tuint ]
       PROP (0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive (Vint (Int.repr n)))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (if eq_dec p nullval then emp 
            else (malloc_token Tsh n p * memory_block Tsh n p)).

Definition malloc_spec (prog: program) :=
  DECLARE (ext_link_prog prog "_malloc") malloc_spec'.

Parameter body_malloc:
 forall {Espec: OracleKind}, 
  body_lemma_of_funspec EF_malloc malloc_spec'.

Definition free_spec' :=
   WITH p:_, n:_
   PRE [ 1%positive OF tptr tvoid ]
       PROP ()
       LOCAL (temp 1%positive p)
       SEP (malloc_token Tsh n p; memory_block Tsh n p)
    POST [ Tvoid ] 
       PROP ()
       LOCAL ()
       SEP ().

Definition free_spec  (prog: program) :=
  DECLARE (ext_link_prog prog "_free") free_spec'.

Parameter body_free:
 forall {Espec: OracleKind}, 
  body_lemma_of_funspec EF_free free_spec'.

Definition library_G prog :=
  [exit_spec prog; malloc_spec prog; free_spec prog].

Ltac with_library prog G :=
 let x := eval hnf in (augment_funspecs prog (library_G prog ++ G))
   in exact x.

