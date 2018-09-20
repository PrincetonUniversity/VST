(* Andrew W. Appel and Stephen Yi-Hsien Lin,
    May 2013, October 2013, March 2014 *)

Require Recdef.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.sublist.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import List.
Require Import sha.general_lemmas.

(* THIS BLOCK OF STUFF is not needed to define SHA256,
  but is useful for reasoning about it *)
Definition LBLOCKz : Z := 16. (* length of a block, in 32-bit integers *)
Definition WORD : Z := 4.  (* length of a word, in bytes *)
Definition CBLOCKz : Z := (LBLOCKz * WORD)%Z. (* length of a block, in characters *)
Definition hi_part (z: Z) := Int.repr (z / Int.modulus).
Definition lo_part (z: Z) := Int.repr z.


Fixpoint little_endian_integer (contents: list byte) : int :=
 match contents with
 | nil => Int.zero
 | c::cr => Int.or (Int.shl (little_endian_integer cr) (Int.repr 8)) (Int.repr (Byte.unsigned c))
 end.

Definition big_endian_integer (contents: list byte) : int :=
   little_endian_integer (rev contents).

(* END OF "THIS BLOCK OF STUFF" *)

Import ListNotations.

(* PREPROCESSING: CONVERTING STRINGS TO PADDED MESSAGE BLOCKS *)

(*converting a string to a list of Z *)
Fixpoint str_to_bytes (str : string) : list byte :=
  match str with
    |EmptyString => nil
    |String c s => Byte.repr (Z.of_N (N_of_ascii c)) :: str_to_bytes s
    end.

Definition generate_and_pad msg :=
  let n := Zlength msg in
   bytelist_to_intlist (msg ++ [Byte.repr 128%Z]
                ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) Byte.zero)
           ++ [Int.repr (n * 8 / Int.modulus); Int.repr (n * 8)].

(*ROUND FUNCTION*)

(*hardcoding the constants, first 32 bits of the fractional parts of the cube roots of the first 64 prime numbers*)
Definition K256 := map Int.repr
  [1116352408 ; 1899447441; 3049323471; 3921009573;
   961987163   ; 1508970993; 2453635748; 2870763221;
   3624381080; 310598401  ; 607225278  ; 1426881987;
   1925078388; 2162078206; 2614888103; 3248222580;
   3835390401; 4022224774; 264347078  ; 604807628;
   770255983  ; 1249150122; 1555081692; 1996064986;
   2554220882; 2821834349; 2952996808; 3210313671;
   3336571891; 3584528711; 113926993  ; 338241895;
   666307205  ; 773529912  ; 1294757372; 1396182291;
   1695183700; 1986661051; 2177026350; 2456956037;
   2730485921; 2820302411; 3259730800; 3345764771;
   3516065817; 3600352804; 4094571909; 275423344;
   430227734  ; 506948616  ; 659060556  ; 883997877;
   958139571  ; 1322822218; 1537002063; 1747873779;
   1955562222; 2024104815; 2227730452; 2361852424;
   2428436474; 2756734187; 3204031479; 3329325298].

(*functions used for round function*)
Definition Ch (x y z : int) : int :=
  Int.xor (Int.and x y) (Int.and (Int.not x) z).

Definition Maj (x y z : int) : int :=
  Int.xor (Int.xor (Int.and x z) (Int.and y z) ) (Int.and x y).

Definition Rotr b x := Int.ror x (Int.repr b).

Definition Sigma_0 (x : int) : int :=
          Int.xor (Int.xor (Rotr 2 x) (Rotr 13 x)) (Rotr 22 x).
Definition Sigma_1 (x : int) : int :=
          Int.xor (Int.xor (Rotr 6 x) (Rotr 11 x)) (Rotr 25 x).
Definition sigma_0 (x : int) : int :=
          Int.xor (Int.xor (Rotr 7 x) (Rotr 18 x)) (Shr 3 x).
Definition sigma_1 (x : int) : int :=
          Int.xor (Int.xor (Rotr 17 x) (Rotr 19 x)) (Shr 10 x).

(* word function *)
Function W (M: Z -> int) (t: Z) {measure Z.to_nat t} : int :=
  if zlt t 16
  then M t
  else  (Int.add (Int.add (sigma_1 (W M (t-2))) (W M (t-7)))
               (Int.add (sigma_0 (W M (t-15))) (W M (t-16)))).
Proof.
intros; apply Z2Nat.inj_lt; omega.
intros; apply Z2Nat.inj_lt; omega.
intros; apply Z2Nat.inj_lt; omega.
intros; apply Z2Nat.inj_lt; omega.
Qed.

(*registers that represent intermediate and final hash values*)
Definition registers := list int.

(*initializing the values of registers, first thirty-two bits of the fractional
    parts of the square roots of the first eight prime numbers*)
Definition init_registers : registers :=
  map Int.repr  [1779033703; 3144134277; 1013904242; 2773480762;
                        1359893119; 2600822924; 528734635; 1541459225].

Definition nthi (il: list int) (t: Z) := nth (Z.to_nat t) il Int.zero.

Definition rnd_function (x : registers) (k : int) (w : int) : registers:=
  match x with
  |  [a; b; c; d; e; f; g; h] =>
     let T1 := Int.add (Int.add (Int.add (Int.add h (Sigma_1 e)) (Ch e f g)) k) w in
     let T2 := Int.add (Sigma_0 a) (Maj a b c) in
       [Int.add T1 T2; a; b; c; Int.add d T1; e; f; g]
  | _ => nil  (* impossible *)
  end.

Function Round  (regs: registers) (M: Z ->int) (t: Z)
        {measure (fun t => Z.to_nat(t+1)) t} : registers :=
 if zlt t 0 then regs
 else rnd_function (Round regs M (t-1)) (nthi K256 t) (W M t).
Proof. intros; apply Z2Nat.inj_lt; omega.
Qed.

Definition hash_block (r: registers) (block: list int) : registers :=
      map2 Int.add r (Round r (nthi block) 63).

Function hash_blocks (r: registers) (msg: list int) {measure length msg} : registers :=
  match msg with
  | nil => r
  | _ => hash_blocks (hash_block r (firstn 16 msg)) (skipn 16 msg)
  end.
Proof. intros.
 destruct (lt_dec (length msg) 16).
 rewrite skipn_length_short. simpl; omega. subst; simpl in *; omega.
 rewrite <- teq; auto.
 rewrite skipn_length. simpl; omega.
Qed.

Definition SHA_256 (str : list byte) : list byte :=
    intlist_to_bytelist (hash_blocks init_registers (generate_and_pad str)).
