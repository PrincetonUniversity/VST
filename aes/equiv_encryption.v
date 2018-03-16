Require Import aes.spec_encryption_LL.
Require Import aes.spec_AES256_HL.
Require Import aes.tablesLL.
Require Import aes.GF_ops_LL.
Require Import aes.conv_HL_to_LL.
Require Import aes.bitfiddling.
Require Import aes.list_lemmas.
Require Import aes.equiv_GF_ops.
Require Import List. Import ListNotations.

Lemma split_quad_eq: forall {T : Type} (c0 c1 c2 c3 c0' c1' c2' c3' : T),
  c0 = c0' -> c1 = c1' -> c2 = c2' -> c3 = c3' -> (c0, c1, c2, c3) = (c0', c1', c2', c3').
Proof.
  intros. congruence.
Qed.

Lemma split_4eq: forall (T : Type) (c0 c1 c2 c3 c0' c1' c2' c3' : T),
  (c0, c1, c2, c3) = (c0', c1', c2', c3') ->
  c0 = c0' /\ c1 = c1' /\ c2 = c2' /\ c3 = c3'.
Proof.
  intros. inversion H. subst. auto.
Qed.

Lemma get_uint32_le_sublist: forall i l,
  0 <= i <= Zlength l - 4 ->
  get_uint32_le l i = get_uint32_le (sublist i (i+4) l) 0.
Proof.
  intros. unfold get_uint32_le.
  do 4 rewrite Znth_sublist by omega.
  replace (0 + i) with i by omega.
  replace (0 + 1 + i) with (i + 1) by omega.
  replace (0 + 2 + i) with (i + 2) by omega.
  replace (0 + 3 + i) with (i + 3) by omega.
  reflexivity.
Qed.

Lemma get_uint32_le_word_to_int: forall b0 b1 b2 b3,
  get_uint32_le (map Int.unsigned [b0; b1; b2; b3]) 0 = word_to_int (b0, b1, b2, b3).
Proof.
  intros. unfold get_uint32_le. unfold word_to_int.
  do 4 rewrite Znth_map by (change (Zlength [b0; b1; b2; b3]) with 4; omega).
  do 4 rewrite Int.repr_unsigned.
  reflexivity.
Qed.

Lemma initial_round_equiv: forall S K,
  (mbed_tls_initial_add_round_key
    (map Int.unsigned (state_to_list S))
    (map Int.unsigned (block_to_ints K))
  ) = state_to_four_ints (AddRoundKey S K).
Proof.
  intros.
  destruct S as [[[w0 w1] w2] w3].
  destruct w0 as [[[?p0 ?p0] ?p0] ?p0].
  destruct w1 as [[[?p0 ?p0] ?p0] ?p0].
  destruct w2 as [[[?p0 ?p0] ?p0] ?p0].
  destruct w3 as [[[?p0 ?p0] ?p0] ?p0].
  destruct K as [[[w0 w1] w2] w3].
  destruct w0 as [[[?k0 ?k0] ?k0] ?k0].
  destruct w1 as [[[?k0 ?k0] ?k0] ?k0].
  destruct w2 as [[[?k0 ?k0] ?k0] ?k0].
  destruct w3 as [[[?k0 ?k0] ?k0] ?k0].

  (* simpl LHS (low level) *)
  unfold mbed_tls_initial_add_round_key.
  unfold mbed_tls_initial_add_round_key_col.
  match goal with
  | |- context [ Znth 3 ?l  ] => let l' := (eval_list l) in change l with l'
  end.
  match goal with
  | |- context [ Znth 0 (?e0 :: ?rest) ] =>
    change (Znth 0 (e0 :: rest)) with e0
  end.
  match goal with
  | |- context [ Znth 1 (?e0 :: ?e1 :: ?rest) ] =>
    change (Znth 1 (e0 :: e1 :: rest)) with e1
  end.
  match goal with
  | |- context [ Znth 2 (?e0 :: ?e1 :: ?e2 :: ?rest) ] =>
    change (Znth 2 (e0 :: e1 :: e2 :: rest)) with e2
  end.
  match goal with
  | |- context [ Znth 3 (?e0 :: ?e1 :: ?e2 :: ?e3 :: ?rest) ] =>
    change (Znth 3 (e0 :: e1 :: e2 :: e3 :: rest)) with e3
  end.
  match goal with
  | |- context [ map Int.unsigned ?l ] => let l' := (eval_list l) in change l with l'
  end.
  rewrite (get_uint32_le_sublist (0 * 4)) by (simpl; omega).
  rewrite (get_uint32_le_sublist (1 * 4)) by (simpl; omega).
  rewrite (get_uint32_le_sublist (2 * 4)) by (simpl; omega).
  rewrite (get_uint32_le_sublist (3 * 4)) by (simpl; omega).
  do 4 rewrite sublist_map.
  do 4 match goal with
  | |- context [sublist ?i ?j ?l] =>
    let r := eval_list (sublist i j l) in change (sublist i j l) with r
  end.
  do 4 rewrite Int.repr_unsigned.
  do 4 rewrite get_uint32_le_word_to_int.
  do 4 rewrite xor_word_to_int.

  (* simpl RHS (high level) *)
  unfold AddRoundKey. unfold transpose. unfold xor_word. unfold state_to_four_ints, transpose.

  reflexivity.
Qed.

Definition FT0b0(i: Z): int := GF_ops_LL.times2 (Znth i FSb).
Definition FT0b1(i: Z): int := Znth i FSb.
Definition FT0b2(i: Z): int := Znth i FSb.
Definition FT0b3(i: Z): int := GF_ops_LL.times3 (Znth i FSb).
(* Note: according to calc_FT0, it should FT0b3 is
     (Int.and (Int.xor (GF_ops_LL.times2 (Znth i FSb)) (Znth i FSb)) (Int.repr 255))
   but we prefer to use an equivalent "medium-level" formulation *)

Lemma times3_times2: forall i,
  0 <= Int.unsigned i < 256 ->
  Int.and (Int.xor (times2 i) i) (Int.repr 255) = times3 i.
Proof.
  intros. unfold times2, times3.
  rewrite <- (mask_byte_nop _ H) at 3.
  repeat rewrite <- (Int.and_commut (Int.repr 255)).
  rewrite <- Int.and_xor_distrib.
  rewrite <- Int.and_assoc.
  rewrite Int.and_idem.
  f_equal. rewrite Int.xor_commut.
  reflexivity.
Qed.

Lemma calc_FT0_expose_bytes: forall i,
  0 <= i < 256 ->
  calc_FT0 i = word_to_int (FT0b0 i, FT0b1 i, FT0b2 i, FT0b3 i).
Proof.
  intros.
  Transparent calc_FT0. unfold calc_FT0.
  unfold word_to_int.
  unfold FT0b0, FT0b1, FT0b2, FT0b3.
  rewrite xor_is_or_4_bytes.
  f_equal. f_equal. apply times3_times2. apply FSb_range.
Qed.

Lemma calc_FT1_expose_bytes: forall i,
  0 <= i < 256 ->
  calc_FT1 i = word_to_int (FT0b3 i, FT0b0 i, FT0b1 i, FT0b2 i).
Proof.
  intros.
  Transparent calc_FT1. unfold calc_FT1.
  rewrite calc_FT0_expose_bytes by assumption.
  rewrite rot8_word_to_int.
  reflexivity.
Qed.

Lemma calc_FT2_expose_bytes: forall i,
  0 <= i < 256 ->
  calc_FT2 i = word_to_int (FT0b2 i, FT0b3 i, FT0b0 i, FT0b1 i).
Proof.
  intros.
  Transparent calc_FT2. unfold calc_FT2, calc_FT1.
  rewrite calc_FT0_expose_bytes by assumption.
  do 2 rewrite rot8_word_to_int.
  reflexivity.
Qed.

Lemma calc_FT3_expose_bytes: forall i,
  0 <= i < 256 ->
  calc_FT3 i = word_to_int (FT0b1 i, FT0b2 i, FT0b3 i, FT0b0 i).
Proof.
  intros.
  Transparent calc_FT3. unfold calc_FT3, calc_FT2, calc_FT1.
  rewrite calc_FT0_expose_bytes by assumption.
  do 3 rewrite rot8_word_to_int.
  reflexivity.
Qed.

Lemma split_quad_eq': forall {T : Type} (c0 c1 c2 c3 c0' c1' c2' c3' : T),
  c0 = c0' -> c1 = c1' -> c2 = c2' -> c3 = c3' -> (c0, (c1, (c2, c3))) = (c0', (c1', (c2', c3'))).
Proof.
  intros. congruence.
Qed.

Lemma xor_assoc_5: forall i0 i1 i2 i3 i4,
  Int.xor (Int.xor (Int.xor (Int.xor i4 i0) i1) i2) i3 =
  Int.xor (Int.xor (Int.xor (Int.xor i0 i1) i2) i3) i4.
Proof.
  intros.
  rewrite <- (Int.xor_commut i4).
  repeat rewrite Int.xor_assoc.
  reflexivity.
Qed.

Axiom byte_range_admit: forall b, 0 <= Int.unsigned b < 256.

Lemma round_equiv: forall S K,
  (mbed_tls_fround
    (state_to_four_ints S)
    (map Int.unsigned (block_to_ints K))
    0
  ) = state_to_four_ints (round S K).
Proof.
  intros.
  destruct S as [[[w0 w1] w2] w3].
  destruct w0 as [[[?p0 ?p0] ?p0] ?p0].
  destruct w1 as [[[?p0 ?p0] ?p0] ?p0].
  destruct w2 as [[[?p0 ?p0] ?p0] ?p0].
  destruct w3 as [[[?p0 ?p0] ?p0] ?p0].
  destruct K as [[[w0 w1] w2] w3].
  destruct w0 as [[[?k0 ?k0] ?k0] ?k0].
  destruct w1 as [[[?k0 ?k0] ?k0] ?k0].
  destruct w2 as [[[?k0 ?k0] ?k0] ?k0].
  destruct w3 as [[[?k0 ?k0] ?k0] ?k0].

  (* unfold LHS (low level): *)
  unfold mbed_tls_fround. unfold state_to_four_ints.
  match goal with
  | |- context [ Znth (0 + 3) ?l ] => let l' := (eval_list l) in change l with l'
  end.
  match goal with
  | |- context [ Znth 0 (?e0 :: ?rest) ] =>
    change (Znth 0 (e0 :: rest)) with e0
  end.
  match goal with
  | |- context [ Znth (0 + 1) (?e0 :: ?e1 :: ?rest)] =>
    change (Znth (0 + 1) (e0 :: e1 :: rest)) with e1
  end.
  match goal with
  | |- context [ Znth (0 + 2) (?e0 :: ?e1 :: ?e2 :: ?rest)] =>
    change (Znth (0 + 2) (e0 :: e1 :: e2 :: rest)) with e2
  end.
  match goal with
  | |- context [ Znth (0 + 3) (?e0 :: ?e1 :: ?e2 :: ?e3 :: ?rest) ] =>
    change (Znth (0 + 3) (e0 :: e1 :: e2 :: e3 :: rest)) with e3
  end.
  unfold mbed_tls_fround_col.
  unfold transpose.
  do 4 rewrite byte0_word_to_int.
  do 4 rewrite byte1_word_to_int.
  do 4 rewrite byte2_word_to_int.
  do 4 rewrite byte3_word_to_int.
  do 4 rewrite Int.repr_unsigned.

  (* unfold RHS (high level): *)
  unfold round. unfold AddRoundKey, MixColumns, ShiftRows, SubBytes.
  unfold transpose. unfold sub_word, xor_word, transform_column.

  Transparent FT0 FT1 FT2 FT3.
  unfold FT0, FT1, FT2, FT3.
  assert (forall b, 0 <= Int.unsigned b < 256) as B by apply byte_range_admit.
  do 16 rewrite Znth_fill_list by apply B.

  do 4 rewrite calc_FT0_expose_bytes by apply B.
  do 4 rewrite calc_FT1_expose_bytes by apply B.
  do 4 rewrite calc_FT2_expose_bytes by apply B.
  do 4 rewrite calc_FT3_expose_bytes by apply B.

  repeat rewrite xor_word_to_int.
  unfold FT0b0, FT0b1, FT0b2, FT0b3.
  repeat rewrite equiv_sbox.
  repeat rewrite times2_equiv by apply B.
  repeat rewrite times3_equiv by apply B.
  repeat rewrite <- Int.xor_assoc.

  apply split_quad_eq'; f_equal; apply split_quad_eq; apply xor_assoc_5.
Qed.

Lemma final_round_equiv: forall S K,
  (mbed_tls_final_fround
    (state_to_four_ints S)
    (map Int.unsigned (block_to_ints K))
    0
  ) = state_to_four_ints (last_round S K).
Proof.
  intros.
  destruct S as [[[w0 w1] w2] w3].
  destruct w0 as [[[?p0 ?p0] ?p0] ?p0].
  destruct w1 as [[[?p0 ?p0] ?p0] ?p0].
  destruct w2 as [[[?p0 ?p0] ?p0] ?p0].
  destruct w3 as [[[?p0 ?p0] ?p0] ?p0].
  destruct K as [[[w0 w1] w2] w3].
  destruct w0 as [[[?k0 ?k0] ?k0] ?k0].
  destruct w1 as [[[?k0 ?k0] ?k0] ?k0].
  destruct w2 as [[[?k0 ?k0] ?k0] ?k0].
  destruct w3 as [[[?k0 ?k0] ?k0] ?k0].

  (* unfold LHS (low level): *)
  unfold mbed_tls_final_fround. unfold state_to_four_ints. 
  match goal with
  | |- context [ Znth (0 + 3) ?l ] => let l' := (eval_list l) in change l with l'
  end.
  match goal with
  | |- context [ Znth 0 (?e0 :: ?rest) ] =>
    change (Znth 0 (e0 :: rest)) with e0
  end.
  match goal with
  | |- context [ Znth (0 + 1) (?e0 :: ?e1 :: ?rest) ] =>
    change (Znth (0 + 1) (e0 :: e1 :: rest)) with e1
  end.
  match goal with
  | |- context [ Znth (0 + 2) (?e0 :: ?e1 :: ?e2 :: ?rest) ] =>
    change (Znth (0 + 2) (e0 :: e1 :: e2 :: rest)) with e2
  end.
  match goal with
  | |- context [ Znth (0 + 3) (?e0 :: ?e1 :: ?e2 :: ?e3 :: ?rest) ] =>
    change (Znth (0 + 3) (e0 :: e1 :: e2 :: e3 :: rest)) with e3
  end.
  unfold mbed_tls_final_fround_col.
  unfold transpose.
  do 4 rewrite byte0_word_to_int.
  do 4 rewrite byte1_word_to_int.
  do 4 rewrite byte2_word_to_int.
  do 4 rewrite byte3_word_to_int.
  do 4 rewrite Int.repr_unsigned.
  do 4 rewrite xor_byte0_with_FSb.
  do 4 rewrite xor_byte1_with_FSb.
  do 4 rewrite xor_byte2_with_FSb.
  do 4 rewrite xor_byte3_with_FSb.

  (* unfold RHS (high level): *)
  unfold last_round. unfold AddRoundKey, ShiftRows, SubBytes.
  unfold transpose. unfold sub_word, xor_word.

  do 16 rewrite equiv_sbox.
  do 16 match goal with
  | |- context [Int.xor (look_sbox ?p) ?k] => rewrite (Int.xor_commut (look_sbox p) k)
  end.
  reflexivity.
Qed.

Ltac eta5 HH :=
  let Hnew := fresh in match type of HH with
  | ?f = (fun a1 a2 a3 a4 a5 => ?e) =>
    assert (forall a1 a2 a3 a4 a5, f a1 a2 a3 a4 a5 = e) as Hnew by (intro; rewrite HH; reflexivity)
  end;
  clear HH; rename Hnew into HH.

Lemma mbed_tls_initial_round_sublist: forall s ks,
  4 <= Zlength ks ->
  mbed_tls_initial_add_round_key s ks = mbed_tls_initial_add_round_key s (sublist 0 4 ks).
Proof.
  intros.
  unfold mbed_tls_initial_add_round_key.
  unfold mbed_tls_initial_add_round_key_col.
  do 4 rewrite Znth_sublist by omega.
  reflexivity.
Qed.

Lemma mbed_tls_fround_sublist: forall i s ks,
  0 <= i <= Zlength ks - 4 ->
  mbed_tls_fround s ks i = mbed_tls_fround s (sublist i (i+4) ks) 0.
Proof.
  intros. unfold mbed_tls_fround.
  do 4 rewrite Znth_sublist by omega.
  replace (0 + i) with i by omega.
  replace (0 + 1 + i) with (i + 1) by omega.
  replace (0 + 2 + i) with (i + 2) by omega.
  replace (0 + 3 + i) with (i + 3) by omega.
  reflexivity.
Qed.

Lemma mbed_tls_final_fround_sublist: forall i s ks,
  0 <= i <= Zlength ks - 4 ->
  mbed_tls_final_fround s ks i = mbed_tls_final_fround s (sublist i (i+4) ks) 0.
Proof.
  intros. unfold mbed_tls_final_fround.
  do 4 rewrite Znth_sublist by omega.
  replace (0 + i) with i by omega.
  replace (0 + 1 + i) with (i + 1) by omega.
  replace (0 + 2 + i) with (i + 2) by omega.
  replace (0 + 3 + i) with (i + 3) by omega.
  reflexivity.
Qed.

Lemma HL_equiv_LL_encryption: forall exp_key plaintext,
  Zlength exp_key = 15 ->
  (mbed_tls_aes_enc
     (map Int.unsigned (state_to_list plaintext))
     ((blocks_to_Zwords exp_key) ++ (list_repeat (8%nat) 0))
  ) = output_four_ints_as_bytes (state_to_four_ints (Cipher exp_key plaintext)).
Proof.
  intros.
  unfold mbed_tls_aes_enc. cbv zeta. f_equal.
  do 15 (destruct exp_key as [ | [[[?k0 ?k0] ?k0] ?k0] exp_key]; [ inversion H | ]).
  assert (exp_key = nil). {
    destruct exp_key; [ reflexivity | ].
    exfalso. do 16 rewrite Zlength_cons in H.
    pose proof (Zlength_nonneg exp_key). omega.
  }
  subst exp_key. clear H.

  (* simpl LHS (low level) *)
  match goal with
  | |- context [?l1 ++ ?l2] =>
    let r := eval_list (l1 ++ l2) in change (l1 ++ l2) with r
  end.
  rewrite mbed_tls_final_fround_sublist by (simpl; omega).
  unfold mbed_tls_enc_rounds.
  simpl (4 + 4 * Z.of_nat _).
  rewrite (mbed_tls_fround_sublist 4) by (simpl; omega).
  rewrite (mbed_tls_fround_sublist 8) by (simpl; omega).
  rewrite (mbed_tls_fround_sublist 12) by (simpl; omega).
  rewrite (mbed_tls_fround_sublist 16) by (simpl; omega).
  rewrite (mbed_tls_fround_sublist 20) by (simpl; omega).
  rewrite (mbed_tls_fround_sublist 24) by (simpl; omega).
  rewrite (mbed_tls_fround_sublist 28) by (simpl; omega).
  rewrite (mbed_tls_fround_sublist 32) by (simpl; omega).
  rewrite (mbed_tls_fround_sublist 36) by (simpl; omega).
  rewrite (mbed_tls_fround_sublist 40) by (simpl; omega).
  rewrite (mbed_tls_fround_sublist 44) by (simpl; omega).
  rewrite (mbed_tls_fround_sublist 48) by (simpl; omega).
  rewrite (mbed_tls_fround_sublist 52) by (simpl; omega).
  rewrite mbed_tls_initial_round_sublist by (cbv; intro; discriminate).
  do 15 match goal with
  | |- context [sublist ?i ?j ?l] =>
    let r := eval_list (sublist i j l) in change (sublist i j l) with r
  end.

  (* simpl RHS (high level) *)
  unfold Cipher.
  unfold apply_rounds.

  (* apply equivalence lemmas for rounds *)
  rewrite <- final_round_equiv. f_equal.
  do 13 (rewrite <- round_equiv; f_equal).
  rewrite <- initial_round_equiv. f_equal.
Qed.
