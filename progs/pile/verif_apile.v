Require Import VST.floyd.proofauto.
Require Import linking.
Require Import apile.
Require Import spec_stdlib.
Require Import spec_pile.
Require Import spec_apile.

Definition Gprog : funspecs :=   
   [Pile_add_spec; Pile_count_spec] ++ spec_apile.specs.

Lemma body_Apile_add: semax_body Vprog Gprog f_Apile_add Apile_add_spec.
Proof.
start_function.
unfold apile.
forward_call (gv _a_pile, n,sigma,gv).
forward.
Qed.

Lemma body_Apile_count: semax_body Vprog Gprog f_Apile_count Apile_count_spec.
Proof.
start_function.
unfold apile in *.
forward_call (gv _a_pile, sigma).
forward.
Qed.

Definition module := 
  [mk_body body_Apile_add; mk_body body_Apile_count].

