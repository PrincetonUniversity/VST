(* This file is for lemmas that
  (a) are used in the proof that the functional prog = functional spec
  AND (b) are used in the proof about the C program.
This file DOES NOT IMPORT anything about C or CompCert
  (except the CompCert Integers module)
*)
Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.
Require Import sha.general_lemmas.
Require Import sha.SHA256.

Lemma length_Round:
  forall regs f n,
   length regs = 8%nat ->
   length (Round regs f n) = 8%nat.
Proof.
intros.
destruct (zlt n 0).
rewrite Round_equation.
rewrite if_true by auto; auto.
replace n with (n+1-1) by omega.
rewrite <- (Z2Nat.id (n+1)) by omega.
revert regs H; induction (Z.to_nat (n+1)); intros.
rewrite Round_equation.
change (Z.of_nat 0 - 1) with (-1).
rewrite if_true by omega. auto.
clear n g. rename n0 into n.
rewrite Round_equation.
rewrite inj_S.
unfold Z.succ.
rewrite Z.add_simpl_r.
rewrite if_false by omega.
specialize (IHn0 _ H).
clear - IHn0.
rename f into f'.
destruct (Round regs f' (Z.of_nat n - 1))
  as [ | a [ | b [ | c [ | d [ | e [ | f [ | g [ | h [ | ]]]]]]]]]; try inv IHn0.
reflexivity.
Qed.

Lemma length_hash_block:
 forall regs block,
   length regs = 8%nat ->
   length block = 16%nat ->
   length (hash_block regs block) = 8%nat.
Proof.
intros.
unfold hash_block.
rewrite (length_map2 _ _ _ _ _ _ 8%nat); auto.
apply length_Round; auto.
Qed.

(* END COMMON LEMMAS *)