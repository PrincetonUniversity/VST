Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.sha_lemmas.
Require Import sha.spec_sha.
Local Open Scope nat.
Local Open Scope logic.

Lemma body_SHA256_Init: semax_body Vprog Gtot f_SHA256_Init SHA256_Init_spec.
Proof.
start_function.
name c_ _c.
unfold data_at_.
do 8 (forward; unfold upd_Znth_in_list, sublist; simpl app).
repeat forward.
Exists (map Vint init_registers, 
      (Vint Int.zero, (Vint Int.zero, (list_repeat (Z.to_nat 64) Vundef, Vint Int.zero)))).
(* BUG: entailer! is far too slow here,
 becuase [simple apply prop_and_same_derives'] takes forever. *)
simple apply andp_right; [apply prop_right | ].
repeat split; auto.
rewrite hash_blocks_equation. reflexivity.
apply Z.divide_0_r.
unfold data_at. apply derives_refl'; f_equal.
f_equal.
simpl.
repeat (apply f_equal2; [f_equal; apply int_eq_e; compute; reflexivity | ]); auto.
Time Qed. (* 27 sec *)
