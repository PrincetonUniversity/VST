Require Import VST.floyd.proofauto.
Require Import malloc.
Require Import malloc_lemmas.
Require Import malloc_sep. (*New: to get access to the CompSpecs defined in that file*)
Require Import VSU_malloc_definitions.

Lemma body_bin2size: semax_body MF_Vprog MF_Gprog f_bin2size bin2size_spec.
Proof. start_function. forward. 
Qed.

Lemma body_size2bin: semax_body MF_Vprog MF_Gprog f_size2bin size2bin_spec.
Proof. start_function. 
  forward_call (BINS-1). (*rep_lia. *)
  forward_if.
  - (* then *) 
    forward. entailer!. f_equal. f_equal. unfold size2binZ; simpl. 
    bdestruct (bin2sizeZ (BINS - 1) <? s); trivial; try lia.
  - (* else *)
    forward.  entailer!. f_equal. unfold size2binZ. 
    bdestruct (bin2sizeZ (BINS - 1) <? s); try lia.
    unfold Int.divu. do 2 rewrite Int.unsigned_repr by rep_lia. 
    f_equal. normalize.  f_equal. rep_lia.
Qed.
 (*
Definition module := 
  [mk_body body_bin2size; mk_body body_size2bin].
*)