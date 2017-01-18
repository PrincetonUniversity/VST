Require Import Integers.
Require Import ZArith. Open Scope Z.
Require Import floyd.sublist.
Require Import aes.tablesLL.

Definition four_ints := (int * (int * (int * int)))%type.

Definition col (i : Z) (s : four_ints) : int := match i with
| 0 => fst s
| 1 => fst (snd s)
| 2 => fst (snd (snd s))
| 3 => snd (snd (snd s))
| _ => Int.zero (* should not happen *)
end.


Goal forall S13,
(Int.unsigned
        (Znth
           (Z.land (Int.unsigned (Int.shru (col 2 S13) (Int.repr 16))) (Int.unsigned (Int.repr 255)))
           FSb Int.zero) ?= Byte.max_unsigned) = Gt
-> False.
intros S18 H2.
inversion H2.
(* fast, but if we do this in verif_encryption_ll.v, on the exact same goal, it takes forever, why?? *)


