Require Export aes.spec_AES256_HL.
Require Export aes.spec_encryption_LL.
Require Export List. Export ListNotations.

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
