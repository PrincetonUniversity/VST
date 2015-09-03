Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.sha_lemmas.
Require Import sha.spec_sha.
Local Open Scope nat.
Local Open Scope logic.

Arguments upd_reptype_array t0 i v v0 / .  (* move this to floyd? *)

Lemma body_SHA256_Init: semax_body Vprog Gtot f_SHA256_Init SHA256_Init_spec.
Proof.
start_function.
name c_ _c.
unfold data_at_.
(*
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
forward.
*)
repeat forward.
simpl.
unfold sha256state_.
apply exp_right with (map Vint init_registers, 
      (Vint Int.zero, (Vint Int.zero, (nil, Vint Int.zero)))).
entailer!.
repeat split; auto.
rewrite hash_blocks_equation. reflexivity.
apply Z.divide_0_r.
apply derives_refl'; f_equal.
f_equal.
simpl.
repeat (apply f_equal2; [f_equal; apply int_eq_e; compute; reflexivity | ]); auto.
Qed.
