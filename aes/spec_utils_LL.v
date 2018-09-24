Require Export List. Export ListNotations.
Require Export ZArith.
Local Open Scope Z_scope.
Require Export compcert.lib.Integers.
Require Export VST.floyd.sublist.

Definition Nk := 8. (* number of words in key *)
Definition Nr := 14. (* number of cipher rounds *)
Definition Nb := 4. (* number of words in a block (state) *)

(* arr: list of 4 bytes *)
Definition get_uint32_le (arr: list Z) (i: Z) : int :=
 (Int.or (Int.or (Int.or
            (Int.repr (Znth  i    arr))
   (Int.shl (Int.repr (Znth (i+1) arr)) (Int.repr  8)))
   (Int.shl (Int.repr (Znth (i+2) arr)) (Int.repr 16)))
   (Int.shl (Int.repr (Znth (i+3) arr)) (Int.repr 24))).

(* outputs a list of 4 bytes *)
Definition put_uint32_le (x : int) : list int :=
  [ (Int.and           x                (Int.repr 255));
    (Int.and (Int.shru x (Int.repr  8)) (Int.repr 255));
    (Int.and (Int.shru x (Int.repr 16)) (Int.repr 255));
    (Int.and (Int.shru x (Int.repr 24)) (Int.repr 255)) ].

Definition byte0 (x : int) : Z :=
  (Z.land (Int.unsigned x) (Int.unsigned (Int.repr 255))).
Definition byte1 (x : int) : Z :=
  (Z.land (Int.unsigned (Int.shru x (Int.repr 8))) (Int.unsigned (Int.repr 255))).
Definition byte2 (x : int) : Z :=
  (Z.land (Int.unsigned (Int.shru x (Int.repr 16))) (Int.unsigned (Int.repr 255))).
Definition byte3 (x : int) : Z :=
  (Z.land (Int.unsigned (Int.shru x (Int.repr 24))) (Int.unsigned (Int.repr 255))).
