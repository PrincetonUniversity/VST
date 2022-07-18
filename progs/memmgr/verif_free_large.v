Require Import VST.floyd.proofauto.
Require Import malloc.
Require Import malloc_lemmas.
Require Import malloc_sep.
Require Import VSU_malloc_definitions.
Local Open Scope logic.

(*
Definition Gprog : funspecs := external_specs ++ private_specs.
*)
Lemma body_free_large: semax_body MF_Vprog MF_Gprog f_free_large free_large_spec.
Proof. 
start_function. 
forward_call( (offset_val (-(WA+WORD)) p), (s+WA+WORD) ). (*! munmap( p-(WASTE+WORD), s+WASTE+WORD ) !*)
+ entailer!. destruct p; try contradiction; simpl. normalize.
  rewrite Ptrofs.sub_add_opp. reflexivity.
+ (* munmap pre *)
  entailer!. 
  sep_apply (free_large_chunk s p); try rep_lia.
  entailer!.
(* + rep_lia.*)
+ entailer!.   
Qed.
(*
Definition module := [mk_body body_free_large].
*)