Require Import aes.aes_spec_ll.
Require Import aes.spec_AES256_HL.
Require Import aes.tablesLL.
Require Import aes.GF_ops_LL.
Require Import List. Import ListNotations.

(* Note: In the standard, the 4x4 matrix is filled with bytes column-wise, but the
   high-level spec fills it row-wise, so we have to transpose in the right spots *)

Definition state_to_list (s : state) : list int :=
  match transpose s with
  | ((b11, b12, b13, b14), (b21, b22, b23, b24), (b31, b32, b33, b34), (b41, b42, b43, b44)) =>
    [ b11; b12; b13; b14 ;  b21; b22; b23; b24 ;  b31; b32; b33; b34 ;  b41; b42; b43; b44 ]
  end.

Definition list_to_state (l : list int) : state := transpose
  match l with
  | [ b11; b12; b13; b14 ;  b21; b22; b23; b24 ;  b31; b32; b33; b34 ;  b41; b42; b43; b44 ] =>
    ((b11, b12, b13, b14), (b21, b22, b23, b24), (b31, b32, b33, b34), (b41, b42, b43, b44))
  (* should not happen: *)
  | _ => let z4 := (Int.zero, Int.zero, Int.zero, Int.zero) in
         (z4, z4, z4, z4)
  end.

Definition word_to_int (w : word) : int :=
  match w with (b0, b1, b2, b3) =>
    (Int.or (Int.or (Int.or
             b0
    (Int.shl b1 (Int.repr  8)))
    (Int.shl b2 (Int.repr 16)))
    (Int.shl b3 (Int.repr 24)))
  end.

(*
Definition int_to_word (x : int) : word := (
  (Int.and           x                (Int.repr 255)),
  (Int.and (Int.shru x (Int.repr  8)) (Int.repr 255)),
  (Int.and (Int.shru x (Int.repr 16)) (Int.repr 255)),
  (Int.and (Int.shru x (Int.repr 24)) (Int.repr 255))
).

Definition four_ints_to_state (s : four_ints) : state := transpose match s with
| (c0, (c1, (c2, c3))) => (int_to_word c0, int_to_word c1, int_to_word c2, int_to_word c3)
end.
*)

Definition state_to_four_ints (s : state) : four_ints := match transpose s with
| (c0, c1, c2, c3) => (word_to_int c0, (word_to_int c1, (word_to_int c2, word_to_int c3)))
end.

Definition block_to_ints (b : block) : list int :=
  match b with (w0, w1, w2, w3) => [word_to_int w0; word_to_int w1; word_to_int w2; word_to_int w3] end.

Definition blocks_to_ints (blocks : list block) : list int := flat_map block_to_ints blocks.

Definition blocks_to_Zwords (blocks : list block) : list Z := map Int.unsigned (blocks_to_ints blocks).

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

Lemma byte0_word_to_int: forall b0 b1 b2 b3,
  byte0 (word_to_int (b0, b1, b2, b3)) = Int.unsigned b0.
Admitted.

Lemma byte1_word_to_int: forall b0 b1 b2 b3,
  byte1 (word_to_int (b0, b1, b2, b3)) = Int.unsigned b1.
Admitted.

Lemma byte2_word_to_int: forall b0 b1 b2 b3,
  byte2 (word_to_int (b0, b1, b2, b3)) = Int.unsigned b2.
Admitted.

Lemma byte3_word_to_int: forall b0 b1 b2 b3,
  byte3 (word_to_int (b0, b1, b2, b3)) = Int.unsigned b3.
Admitted.

Ltac eval_list l :=
  let l' := eval hnf in l in lazymatch l' with
  | ?h :: ?tl => let tl' := eval_list tl in constr:(h :: tl')
  | (@nil ?T) => constr:(@nil T)
  end.

Lemma xor_byte0_with_FSb: forall b0 b1 b2 b3 i,
  Int.xor (word_to_int (b0, b1, b2, b3)) (Znth i tablesLL.FSb Int.zero)
  = word_to_int ((Int.xor b0 (Znth i tablesLL.FSb Int.zero)), b1, b2, b3).
Admitted.

Lemma xor_byte1_with_FSb: forall b0 b1 b2 b3 i,
  Int.xor (word_to_int (b0, b1, b2, b3)) (Int.shl (Znth i tablesLL.FSb Int.zero) (Int.repr 8))
  = word_to_int (b0, (Int.xor b1 (Znth i tablesLL.FSb Int.zero)), b2, b3).
Admitted.

Lemma xor_byte2_with_FSb: forall b0 b1 b2 b3 i,
  Int.xor (word_to_int (b0, b1, b2, b3)) (Int.shl (Znth i tablesLL.FSb Int.zero) (Int.repr 16))
  = word_to_int (b0, b1, (Int.xor b2 (Znth i tablesLL.FSb Int.zero)), b3).
Admitted.

Lemma xor_byte3_with_FSb: forall b0 b1 b2 b3 i,
  Int.xor (word_to_int (b0, b1, b2, b3)) (Int.shl (Znth i tablesLL.FSb Int.zero) (Int.repr 24))
  = word_to_int (b0, b1, b2, (Int.xor b3 (Znth i tablesLL.FSb Int.zero))).
Admitted.

Lemma equiv_sbox: forall b,
  Znth (Int.unsigned b) tablesLL.FSb Int.zero = look_sbox b.
Admitted.

Lemma get_uint32_le_sublist: forall i l,
  0 <= i <= Zlength l - 4 ->
  get_uint32_le l i = get_uint32_le (sublist i (i+4) l) 0.
Proof.
  intros. rewrite get_uint32_le_def.
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
  intros. rewrite get_uint32_le_def. unfold word_to_int.
  do 4 rewrite Znth_map with (d' := Int.zero) by (change (Zlength [b0; b1; b2; b3]) with 4; omega).
  do 4 rewrite Int.repr_unsigned.
  reflexivity.
Qed.

Lemma xor_word_to_int: forall a0 a1 a2 a3 b0 b1 b2 b3,
  Int.xor (word_to_int (a0, a1, a2, a3)) (word_to_int (b0, b1, b2, b3))
  = word_to_int ((Int.xor a0 b0), (Int.xor a1 b1), (Int.xor a2 b2), (Int.xor a3 b3)).
Proof.
  intros. unfold word_to_int.
Admitted.

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
  rewrite mbed_tls_initial_add_round_key_def.
  rewrite mbed_tls_initial_add_round_key_col_def.
  match goal with
  | |- context [ Znth 3 ?l ?d ] => let l' := (eval_list l) in change l with l'
  end.
  match goal with
  | |- context [ Znth 0 (?e0 :: ?rest) ?d ] =>
    change (Znth 0 (e0 :: rest) d) with e0
  end.
  match goal with
  | |- context [ Znth 1 (?e0 :: ?e1 :: ?rest) ?d ] =>
    change (Znth 1 (e0 :: e1 :: rest) d) with e1
  end.
  match goal with
  | |- context [ Znth 2 (?e0 :: ?e1 :: ?e2 :: ?rest) ?d ] =>
    change (Znth 2 (e0 :: e1 :: e2 :: rest) d) with e2
  end.
  match goal with
  | |- context [ Znth 3 (?e0 :: ?e1 :: ?e2 :: ?e3 :: ?rest) ?d ] =>
    change (Znth 3 (e0 :: e1 :: e2 :: e3 :: rest) d) with e3
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

Lemma Znth_fill_list: forall {T: Type} (i n: Z) (f: Z -> T) (d: T),
  0 <= i < n ->
  Znth i (fill_list n f) d = f i.
Admitted.

Lemma rot8_word_to_int: forall b0 b1 b2 b3,
  rot8 (word_to_int (b0, b1, b2, b3)) = word_to_int (b3, b0, b1, b2).
Admitted.

Definition FT0b0(i: Z): int := GF_ops_LL.times2 (Znth i FSb Int.zero).
Definition FT0b1(i: Z): int := Znth i FSb Int.zero.
Definition FT0b2(i: Z): int := Znth i FSb Int.zero.
Definition FT0b3(i: Z): int := GF_ops_LL.times3 (Znth i FSb Int.zero).
(* Note: according to calc_FT0, it should FT0b3 is
     (Int.and (Int.xor (GF_ops_LL.times2 (Znth i FSb Int.zero)) (Znth i FSb Int.zero)) (Int.repr 255))
   but we prefer to use an equivalent "medium-level" formulation *)

Lemma mask_byte_nop: forall i,
  0 <= Int.unsigned i < 256 ->
  Int.and i (Int.repr 255) = i.
Admitted.

Lemma FSb_range: forall i,
  0 <= Int.unsigned (Znth i FSb Int.zero) < 256.
Admitted.

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
  rewrite Int.xor_is_or by admit.
  rewrite Int.xor_is_or by admit.
  rewrite Int.xor_is_or by admit.
  f_equal. f_equal. apply times3_times2. apply FSb_range.
Admitted.

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

Lemma times2_equiv: forall b,
  0 <= Int.unsigned b < 256 ->
  times2 b = ff_mult (Int.repr 2) b.
Admitted.

Lemma times3_equiv: forall b,
  0 <= Int.unsigned b < 256 ->
  times3 b = ff_mult (Int.repr 3) b.
Admitted.

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
  (AES_LL_Spec.mbed_tls_fround
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
  rewrite mbed_tls_fround_def. unfold state_to_four_ints.
  match goal with
  | |- context [ Znth (0 + 3) ?l ?d ] => let l' := (eval_list l) in change l with l'
  end.
  match goal with
  | |- context [ Znth 0 (?e0 :: ?rest) ?d ] =>
    change (Znth 0 (e0 :: rest) d) with e0
  end.
  match goal with
  | |- context [ Znth (0 + 1) (?e0 :: ?e1 :: ?rest) ?d ] =>
    change (Znth (0 + 1) (e0 :: e1 :: rest) d) with e1
  end.
  match goal with
  | |- context [ Znth (0 + 2) (?e0 :: ?e1 :: ?e2 :: ?rest) ?d ] =>
    change (Znth (0 + 2) (e0 :: e1 :: e2 :: rest) d) with e2
  end.
  match goal with
  | |- context [ Znth (0 + 3) (?e0 :: ?e1 :: ?e2 :: ?e3 :: ?rest) ?d ] =>
    change (Znth (0 + 3) (e0 :: e1 :: e2 :: e3 :: rest) d) with e3
  end.
  rewrite mbed_tls_fround_col_def.
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
  rewrite mbed_tls_final_fround_def. unfold state_to_four_ints. 
  match goal with
  | |- context [ Znth (0 + 3) ?l ?d ] => let l' := (eval_list l) in change l with l'
  end.
  match goal with
  | |- context [ Znth 0 (?e0 :: ?rest) ?d ] =>
    change (Znth 0 (e0 :: rest) d) with e0
  end.
  match goal with
  | |- context [ Znth (0 + 1) (?e0 :: ?e1 :: ?rest) ?d ] =>
    change (Znth (0 + 1) (e0 :: e1 :: rest) d) with e1
  end.
  match goal with
  | |- context [ Znth (0 + 2) (?e0 :: ?e1 :: ?e2 :: ?rest) ?d ] =>
    change (Znth (0 + 2) (e0 :: e1 :: e2 :: rest) d) with e2
  end.
  match goal with
  | |- context [ Znth (0 + 3) (?e0 :: ?e1 :: ?e2 :: ?e3 :: ?rest) ?d ] =>
    change (Znth (0 + 3) (e0 :: e1 :: e2 :: e3 :: rest) d) with e3
  end.
  rewrite mbed_tls_final_fround_col_def.
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
  rewrite mbed_tls_initial_add_round_key_def.
  rewrite mbed_tls_initial_add_round_key_col_def.
  do 4 rewrite Znth_sublist by omega.
  reflexivity.
Qed.

Lemma mbed_tls_fround_sublist: forall i s ks,
  0 <= i <= Zlength ks - 4 ->
  AES_LL_Spec.mbed_tls_fround s ks i = AES_LL_Spec.mbed_tls_fround s (sublist i (i+4) ks) 0.
Proof.
  intros. rewrite mbed_tls_fround_def.
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
  intros. rewrite mbed_tls_final_fround_def.
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
  rewrite mbed_tls_aes_enc_def. cbv zeta. f_equal.
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
  rewrite mbed_tls_enc_rounds_def.
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
