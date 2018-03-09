Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
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
Import ListNotations.
Import String.

(* This file demonstrates a bug in the Coq 8.8 development version as of 3 March 2018.
  This bug was not present in Coq 8.7.1 or Coq 8.7.2.
  The bug manifests as a universe inconsistency in malloc_spec'.
*)

Parameter malloc_token : forall {cs: compspecs}, share -> type -> val -> mpred.
Parameter malloc_token_valid_pointer:
  forall {cs: compspecs} sh t p, malloc_token sh t p |-- valid_pointer p.
Hint Resolve malloc_token_valid_pointer : valid_pointer.
Parameter malloc_token_local_facts:
  forall {cs: compspecs} sh t p, malloc_token sh t p |-- !! malloc_compatible (sizeof t) p.
Hint Resolve malloc_token_local_facts : saturate_local.
Parameter malloc_token_precise:
  forall {cs: compspecs} sh t p, predicates_sl.precise (malloc_token sh t p).

Definition malloc_spec'  :=
   WITH cs: compspecs, t:type
   PRE [ 1%positive OF tuint ]
       PROP (0 <= sizeof t <= Int.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       LOCAL (temp 1%positive (Vint (Int.repr (sizeof t))))
       SEP ()
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (if eq_dec p nullval then emp
            else (malloc_token Tsh t p * data_at_ Tsh t p)).
