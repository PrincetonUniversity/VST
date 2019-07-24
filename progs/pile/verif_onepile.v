Require Import VST.floyd.proofauto.
Require Import linking.
Require Import onepile.
Require Import spec_stdlib.
Require Import spec_pile.
Require Import spec_onepile.

Definition Gprog : funspecs :=   
   spec_pile.specs ++ spec_onepile.specs.

Lemma body_Onepile_init: semax_body Vprog Gprog f_Onepile_init Onepile_init_spec.
Proof.
start_function.
forward_call gv.
Intros p.
unfold onepile.
forward.
forward.
unfold onepile.
Exists p.
entailer!.
Qed.

Lemma body_Onepile_add: semax_body Vprog Gprog f_Onepile_add Onepile_add_spec.
Proof.
start_function.
unfold onepile.
Intros p.
forward.
forward_call (p,n,sigma,gv).
forward.
unfold onepile.
Exists p.
entailer!.
Qed.

Lemma body_Onepile_count: semax_body Vprog Gprog f_Onepile_count Onepile_count_spec.
Proof.
start_function.
unfold onepile in *.
Intros p.
forward.
forward_call (p,sigma).
forward.
Exists p.
entailer!.
Qed.

Definition module := 
  [mk_body body_Onepile_init; mk_body body_Onepile_add; 
   mk_body body_Onepile_count].
