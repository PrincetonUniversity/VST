Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope logic.

Lemma body_SHA256_Init: semax_body Vprog Gtot f_SHA256_Init SHA256_Init_spec.
Proof.
start_function.
name c_ _c.
revert Delta POSTCONDITION; simpl_typed_mapsto; intros.
normalize.

replace_SEP 0%Z (`(array_at tuint Tsh (ZnthV tuint nil) 0 8 c)).
entailer.

do 8 (forward; [entailer!; [reflexivity | clear; omega .. ]
              | rewrite upd_Znth_next by (compute; reflexivity); simpl app]).
forward. (* c->Nl=0; *)
forward. (* c->Nh=0; *)
forward. (* c->num=0; *)
forward. (* return; *)
unfold sha256state_.
apply exp_right with (init_registers, (Int.zero, (Int.zero, (nil, Int.zero)))).
simpl_typed_mapsto.
unfold s256_h, s256_Nh,s256_Nl, s256_num, s256_data, fst,snd.
entailer!.
repeat split.
simpl; change CBLOCK with 64; omega.
exists 0; simpl; reflexivity.
apply derives_refl'; f_equal.
f_equal.
unfold init_registers.
simpl.
repeat (apply f_equal2; [apply int_eq_e; compute; reflexivity | ]); auto.
Qed.
