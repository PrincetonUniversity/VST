Require Import VST.floyd.proofauto.
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
(* BEGIN: without these lines, the "do 8 forward" takes 40 times as long. *)
unfold field_at_.
unfold_data_at (field_at _ _ _ _ _).
simpl fst; simpl snd.
(* END: without these lines *)
Time do 8 (forward; unfold upd_Znth; if_tac;
  unfold Zlength in *; simpl Zlength_aux in *; try lia;
  unfold sublist; simpl app).
Time repeat forward. (* 14 sec *)
unfold sha256state_.
Exists (map Vint init_registers,
      (Vint Int.zero, (Vint Int.zero, (repeat Vundef (Z.to_nat 64), Vint Int.zero)))).
unfold_data_at (data_at _ _ _ _).
Time entailer!. (* 5.2 sec *)
repeat split; auto.
unfold s256_h, fst, s256a_regs.
rewrite hash_blocks_equation. reflexivity.
unfold data_at. apply derives_refl'; f_equal.
f_equal.
simpl.
repeat (apply f_equal2; [f_equal; apply int_eq_e; compute; reflexivity | ]); auto.
Time Qed. (* 33.6 sec *)
