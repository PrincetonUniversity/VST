(* Lennart Beringer, June 2015*)

(*This is a formalization in Gallina of Dan Bernstein's document
"Salsa20 specification" (version 2005.04.27), Sections 1 - 9.*)

Require Import compcert.lib.Coqlib.
Require Import Coq.Strings.String.
Require Import VST.msl.Extensionality.
Require Import List. Import ListNotations.

Require Import compcert.lib.Integers.
Require Import sha.functional_prog.

Require Import sha.pure_lemmas.
Require Import sha.general_lemmas.

Definition map4 {A B} (f:A -> B) a :=
  match a with (a0, a1, a2, a3) => (f a0, f a1, f a2, f a3) end.

Definition bytelist2Z (l:list byte) : Z :=
  match l with
      [a; b; c; d] => Byte.unsigned d + Byte.unsigned c * 2^8 + Byte.unsigned b * 2^16 + Byte.unsigned a * 2^24
    | _ => 0 end.
Definition hexstring_to_Z s := bytelist2Z (hexstring_to_bytelist s).

Goal Zmod (hexstring_to_Z "c0a8787e"%string +
      hexstring_to_Z "9fd1161d"%string) (2^32)  =
     hexstring_to_Z "60798e9b"%string.
reflexivity. Qed.

(*Explicit definition of sum following Bernstein's "Salsa20 specification" paper:*)
Definition sum (a b:int): int :=
  Int.repr (Zmod (Int.unsigned a + Int.unsigned b) (2^32)).

(*Of course, it's equivalnt to Int.add:*)
Lemma sum_add: forall x y, sum x y = Int.add x y.
Proof. intros. unfold sum. rewrite Int.add_unsigned.
  apply Int.eqm_samerepr. apply Int.eqmod_sym.
  apply Int.eqmod_mod. cbv; trivial.
Qed.

Lemma sum_zero_r a: sum a Int.zero = a.
 unfold sum. rewrite Int.unsigned_zero.
  rewrite Z.add_0_r. rewrite <- Int.unsigned_repr_eq.
  rewrite Int.repr_unsigned.
  apply Int.repr_unsigned.
Qed.

Lemma sum_sym a b: sum a b = sum b a.
 unfold sum. rewrite Z.add_comm. trivial. Qed.

Lemma sum_zero_l a: sum Int.zero a = a.
  rewrite sum_sym. apply sum_zero_r. Qed.

(*We're using sum in the following because it appears to compute more nicely.*)

(*hexstring_to_int*)
Definition x2i s : int := Int.repr (hexstring_to_Z s).

Goal sum (x2i "c0a8787e"%string)
         (x2i "9fd1161d"%string) =
     x2i "60798e9b"%string.
reflexivity. Qed.

Goal Int.xor (x2i "c0a8787e"%string)
         (x2i "9fd1161d"%string) =
     x2i "5f796e63"%string.
reflexivity. Qed.

Definition QuadWord:Type := (int * int * int * int)%type.

Definition quarterround (y:QuadWord): QuadWord :=
  match y with (y0, y1, y2, y3) =>
    let z1 := Int.xor y1 (Int.rol (sum y0 y3) (Int.repr 7)) in
    let z2 := Int.xor y2 (Int.rol (sum y0 z1) (Int.repr 9)) in
    let z3 := Int.xor y3 (Int.rol (sum z1 z2) (Int.repr 13)) in
    let z0 := Int.xor y0 (Int.rol (sum z2 z3) (Int.repr 18))
    in (z0, z1, z2, z3)
  end.

Definition quarterround_old (y:QuadWord): QuadWord :=
  match y with (y0, y1, y2, y3) =>
    let z1 := Int.xor y1 (Int.rol (sum y0 y3) (Int.repr 7)) in
    let z2 := Int.xor y2 (Int.rol (sum z1 y0) (Int.repr 9)) in
    let z3 := Int.xor y3 (Int.rol (sum z2 z1) (Int.repr 13)) in
    let z0 := Int.xor y0 (Int.rol (sum z3 z2) (Int.repr 18))
    in (z0, z1, z2, z3)
  end.
Lemma QR y: quarterround y = quarterround_old y.
destruct y as [[[y0 y1] y2] y3]. simpl. repeat rewrite sum_add.
repeat rewrite (Int.add_commut y0).
f_equal. f_equal. f_equal. f_equal. f_equal.
rewrite Int.add_commut.  f_equal.  f_equal. rewrite Int.add_commut. trivial.
f_equal. rewrite Int.add_commut. trivial.
Qed.

Definition zeroHex := x2i "00000000".
Goal zeroHex = Int.zero. reflexivity. Qed.

Goal quarterround (Int.zero, Int.zero, Int.zero, Int.zero) =
     (Int.zero, Int.zero, Int.zero, Int.zero).
reflexivity. Qed.

Goal quarterround (map4 x2i ("d3917c5b", "55f1c407", "52a58a7a", "8f887a3b")%string) =
     map4 x2i ("3e2f308c", "d90a8f36", "6ab2a923", "2883524c")%string. reflexivity. Qed.

(*MEMORYEXHAUSTION. USE VM_COMPUTE INSTEAD!
  Eval compute in (quarterround (Int.zero, Int.zero, Int.zero, Int.zero)).*)

Definition SixteenWord:Type := (QuadWord * QuadWord * QuadWord * QuadWord)%type.

Definition rowround(y: SixteenWord) : SixteenWord :=
  match y with
    ((y0, y1, y2, y3), (y4, y5, y6, y7), (y8, y9, y10, y11), (y12, y13, y14, y15)) =>
  match quarterround(y0, y1, y2, y3) with (z0, z1, z2, z3) =>
  match quarterround(y5, y6, y7, y4) with (z5, z6, z7, z4) =>
  match quarterround(y10, y11, y8, y9) with (z10, z11, z8, z9) =>
  match quarterround(y15, y12, y13, y14) with (z15, z12, z13, z14) =>
  ((z0, z1, z2, z3), (z4, z5, z6, z7), (z8, z9, z10, z11), (z12, z13, z14, z15))
  end end end end end.

Goal rowround (map4 x2i ("08521bd6", "1fe88837", "bb2aa576", "3aa26365"),
               map4 x2i ("c54c6a5b", "2fc74c2f", "6dd39cc3", "da0a64f6"),
               map4 x2i ("90a2f23d", "067f95a6", "06b35f61", "41e4732e"),
               map4 x2i ("e859c100", "ea4d84b7", "0f619bff", "bc6e965a"))%string =
      (map4 x2i ("a890d39d", "65d71596", "e9487daa", "c8ca6a86"),
       map4 x2i ("949d2192", "764b7754", "e408d9b9", "7a41b4d1"),
       map4 x2i ("3402e183", "3c3af432", "50669f96", "d89ef0a8"),
       map4 x2i ("0040ede5", "b545fbce", "d257ed4f", "1818882d"))%string.
 reflexivity. Qed.

Definition columnround(x: SixteenWord) : SixteenWord :=
  match x with
    ((x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15)) =>
  match quarterround(x0, x4, x8, x12) with (y0, y4, y8, y12) =>
  match quarterround(x5, x9, x13, x1) with (y5, y9, y13, y1) =>
  match quarterround(x10, x14, x2, x6) with (y10, y14, y2, y6) =>
  match quarterround(x15, x3, x7, x11) with (y15, y3, y7, y11) =>
  ((y0, y1, y2, y3), (y4, y5, y6, y7), (y8, y9, y10, y11), (y12, y13, y14, y15))
  end end end end end.

Lemma columnround_rowround: forall x,
  match columnround x with
     ((y0, y1, y2, y3), (y4, y5, y6, y7), (y8, y9, y10, y11), (y12, y13, y14, y15)) =>
  match x with
    ((x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15)) =>
  ((y0, y4, y8, y12), (y1, y5, y9, y13), (y2, y6, y10, y14), (y3, y7, y11, y15))
  =
  rowround ((x0, x4, x8, x12), (x1, x5, x9, x13), (x2, x6, x10, x14), (x3, x7, x11, x15))
  end end.
Proof. intros.
  destruct x as [[[X0 X1] X2] X3].
  unfold columnround. unfold rowround.
  destruct X0 as [[[x0 x1] x2] x3].
  destruct X1 as [[[x4 x5] x6] x7].
  destruct X2 as [[[x8 x9] x10] x11].
  destruct X3 as [[[x12 x13] x14] x15].
  remember (quarterround (x0, x4, x8, x12)) as QR0.
  remember (quarterround (x5, x9, x13, x1)) as  QR1.
  remember (quarterround (x10, x14, x2, x6)) as  QR2.
  remember (quarterround (x15, x3, x7, x11)) as  QR3.
  clear HeqQR0 HeqQR1 HeqQR2 HeqQR3.
  destruct QR0 as [[[q0 q1] q2] q3].
  destruct QR1 as [[[q4 q5] q6] q7].
  destruct QR2 as [[[q8 q9] q10] q11].
  destruct QR3 as [[[q12 q13] q14] q15]. trivial.
Qed.

Goal columnround
       (map4 x2i ("08521bd6", "1fe88837", "bb2aa576", "3aa26365"),
        map4 x2i ("c54c6a5b", "2fc74c2f", "6dd39cc3", "da0a64f6"),
        map4 x2i ("90a2f23d", "067f95a6", "06b35f61", "41e4732e"),
        map4 x2i ("e859c100", "ea4d84b7", "0f619bff", "bc6e965a"))%string =
     (map4 x2i ("8c9d190a", "ce8e4c90", "1ef8e9d3", "1326a71a"),
      map4 x2i ("90a20123", "ead3c4f3", "63a091a0", "f0708d69"),
      map4 x2i ("789b010c", "d195a681", "eb7d5504", "a774135c"),
      map4 x2i ("481c2027", "53a8e4b5", "4c1f89c5", "3f78c9c8"))%string.
 reflexivity. Qed.

Definition doubleround(x: SixteenWord) : SixteenWord :=
  rowround(columnround(x)).

Goal doubleround
        (map4 x2i ("de501066", "6f9eb8f7", "e4fbbd9b", "454e3f57"),
         map4 x2i ("b75540d3", "43e93a4c", "3a6f2aa0", "726d6b36"),
         map4 x2i ("9243f484", "9145d1e8", "4fa9d247", "dc8dee11"),
         map4 x2i ("054bf545", "254dd653", "d9421b6d", "67b276c1"))%string
      = (map4 x2i ("ccaaf672", "23d960f7", "9153e63a", "cd9a60d0"),
         map4 x2i ("50440492", "f07cad19", "ae344aa0", "df4cfdfc"),
         map4 x2i ("ca531c29", "8e7943db", "ac1680cd", "d503ca00"),
         map4 x2i ("a74b2ad6", "bc331c5c", "1dda24c7", "ee928277"))%string.
reflexivity. Qed.

Definition QuadByte:Type := (byte * byte * byte * byte)%type.
Definition littleendian (b:QuadByte): int :=
  match b with (b0, b1, b2, b3) =>
  Int.repr
   (Byte.unsigned b0 + 2^8 * Byte.unsigned b1 +
         2^16 * Byte.unsigned b2 + 2^24 * Byte.unsigned b3)
  end.

Goal littleendian (Byte.zero, Byte.zero, Byte.zero, Byte.zero) = x2i "00000000".
  reflexivity. Qed.

Goal littleendian (Byte.repr 86, Byte.repr 75, Byte.repr 30, Byte.repr 9) =
     x2i "091e4b56".
  reflexivity. Qed.

Goal littleendian (Byte.repr 255, Byte.repr 255, Byte.repr 255, Byte.repr 250) =
     x2i "faffffff".
  reflexivity. Qed.

Definition littleendian_invert (w:int) : QuadByte :=
  let b3 := Int.unsigned w / (2^24) in
    let w2 := Z.modulo (Int.unsigned w) (2^24) in
  let b2 := w2 / (2^16) in
    let w1 := Z.modulo w2 (2^16) in
  let b1 := w1 / (2^8) in
  (Byte.repr (Z.modulo w1 (2^8)),
   Byte.repr b1,
    Byte.repr b2, Byte.repr b3).

Goal littleendian_invert (x2i "faffffff") =
     (Byte.repr 255, Byte.repr 255, Byte.repr 255, Byte.repr 250).
  reflexivity. Qed.

Definition SixtyFourByte:Type :=
 (QuadByte * QuadByte * QuadByte * QuadByte * QuadByte * QuadByte * QuadByte * QuadByte *
  QuadByte * QuadByte * QuadByte * QuadByte * QuadByte * QuadByte * QuadByte * QuadByte)%type.

Fixpoint rounds n (x: SixteenWord) : SixteenWord :=
  match n with O => x
   | S k => rounds k (doubleround x)
  end.

Definition map16 {A B} (f:A -> B) a :=
  match a with (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,a14, a15) =>
     (f a0, f a1, f a2, f a3, f a4, f a5, f a6, f a7, f a8, f a9, f a10, f a11, f a12, f a13, f a14, f a15)
  end.

Definition Salsa20r (n:nat) (x:SixtyFourByte):SixtyFourByte :=
  match map16 littleendian x with
     ( x0,  x1, x2,  x3,  x4,  x5,  x6,  x7,
       x8,  x9, x10, x11, x12, x13, x14, x15) =>
    match rounds n
       ((x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15))
    with ((z0,  z1,  z2,  z3), (z4,  z5,  z6, z7),
          (z8,  z9, z10, z11), (z12, z13, z14, z15))
    => map16 littleendian_invert
        (sum z0 x0, sum z1 x1, sum z2 x2, sum z3 x3,
         sum z4 x4, sum z5 x5, sum z6 x6, sum z7 x7,
         sum z8 x8, sum z9 x9, sum z10 x10, sum z11 x11,
         sum z12 x12, sum z13 x13, sum z14 x14, sum z15 x15)
     end
  end.

Definition Salsa20 (x:SixtyFourByte):SixtyFourByte :=
  match map16 littleendian x with
     ( x0,  x1,  x2,  x3,  x4,  x5,  x6,  x7,
       x8,  x9,  x10, x11, x12, x13, x14, x15) =>
    match
       doubleround (doubleround (doubleround (doubleround (doubleround (
       doubleround (doubleround (doubleround (doubleround (doubleround (
       (x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15)))))))))))
    with ((z0,  z1,  z2,  z3), (z4,  z5,  z6, z7),
          (z8,  z9, z10, z11), (z12, z13, z14, z15))
    => map16 littleendian_invert
        (sum z0 x0, sum z1 x1, sum z2 x2, sum z3 x3,
         sum z4 x4, sum z5 x5, sum z6 x6, sum z7 x7,
         sum z8 x8, sum z9 x9, sum z10 x10, sum z11 x11,
         sum z12 x12, sum z13 x13, sum z14 x14, sum z15 x15)
     end
  end.

Goal Salsa20
   ((Byte.repr 211, Byte.repr 159, Byte.repr  13, Byte.repr 115), (Byte.repr  76, Byte.repr  55, Byte.repr  82, Byte.repr 183), (Byte.repr  3, Byte.repr 117, Byte.repr 222, Byte.repr  37), (Byte.repr 191, Byte.repr 187, Byte.repr 234, Byte.repr 136),
    (Byte.repr 49, Byte.repr 237, Byte.repr 179, Byte.repr  48), (Byte.repr  1, Byte.repr 106, Byte.repr 178, Byte.repr 219), (Byte.repr 175, Byte.repr 199, Byte.repr 166, Byte.repr  48), (Byte.repr  86, Byte.repr  16, Byte.repr 179, Byte.repr 207),
    (Byte.repr 31, Byte.repr 240, Byte.repr  32, Byte.repr  63), (Byte.repr  15, Byte.repr  83, Byte.repr  93, Byte.repr 161), (Byte.repr 116, Byte.repr 147, Byte.repr  48, Byte.repr 113), (Byte.repr 238, Byte.repr  55, Byte.repr 204, Byte.repr  36),
    (Byte.repr 79, Byte.repr 201, Byte.repr 235, Byte.repr  79), (Byte.repr  3, Byte.repr  81, Byte.repr 156, Byte.repr  47), (Byte.repr 203, Byte.repr  26, Byte.repr 244, Byte.repr 243), (Byte.repr  88, Byte.repr 118, Byte.repr 104, Byte.repr  54))
 = ((Byte.repr 109, Byte.repr  42, Byte.repr 178, Byte.repr 168), (Byte.repr 156, Byte.repr 240, Byte.repr 248, Byte.repr 238), (Byte.repr 168, Byte.repr 196, Byte.repr 190, Byte.repr 203), (Byte.repr  26, Byte.repr 110, Byte.repr 170, Byte.repr 154),
    (Byte.repr 29, Byte.repr  29, Byte.repr 150, Byte.repr  26), (Byte.repr 150, Byte.repr  30, Byte.repr 235, Byte.repr 249), (Byte.repr 190, Byte.repr 163, Byte.repr 251, Byte.repr  48), (Byte.repr  69, Byte.repr 144, Byte.repr  51, Byte.repr  57),
    (Byte.repr 118, Byte.repr  40, Byte.repr 152, Byte.repr 157), (Byte.repr 180, Byte.repr  57, Byte.repr  27, Byte.repr  94), (Byte.repr 107, Byte.repr  42, Byte.repr 236, Byte.repr  35), (Byte.repr  27, Byte.repr 111, Byte.repr 114, Byte.repr 114),
    (Byte.repr 219, Byte.repr 236, Byte.repr 232, Byte.repr 135), (Byte.repr 111, Byte.repr 155, Byte.repr 110, Byte.repr  18), (Byte.repr  24, Byte.repr 232, Byte.repr  95, Byte.repr 158), (Byte.repr 179, Byte.repr  19, Byte.repr  48, Byte.repr 202)).
reflexivity. Qed.

Goal Salsa20
   ((Byte.repr 88, Byte.repr 118, Byte.repr 104, Byte.repr  54), (Byte.repr  79, Byte.repr 201, Byte.repr 235, Byte.repr  79), (Byte.repr  3, Byte.repr  81, Byte.repr 156, Byte.repr  47), (Byte.repr 203, Byte.repr  26, Byte.repr 244, Byte.repr 243),
    (Byte.repr 191, Byte.repr 187, Byte.repr 234, Byte.repr 136), (Byte.repr 211, Byte.repr 159, Byte.repr  13, Byte.repr 115), (Byte.repr  76, Byte.repr  55, Byte.repr  82, Byte.repr 183), (Byte.repr  3, Byte.repr 117, Byte.repr 222, Byte.repr  37),
    (Byte.repr 86, Byte.repr  16, Byte.repr 179, Byte.repr 207), (Byte.repr  49, Byte.repr 237, Byte.repr 179, Byte.repr  48), (Byte.repr  1, Byte.repr 106, Byte.repr 178, Byte.repr 219), (Byte.repr 175, Byte.repr 199, Byte.repr 166, Byte.repr  48),
    (Byte.repr 238, Byte.repr  55, Byte.repr 204, Byte.repr  36), (Byte.repr  31, Byte.repr 240, Byte.repr  32, Byte.repr  63), (Byte.repr  15, Byte.repr  83, Byte.repr  93, Byte.repr 161), (Byte.repr 116, Byte.repr 147, Byte.repr  48, Byte.repr 113))
= ((Byte.repr 179, Byte.repr  19, Byte.repr  48, Byte.repr 202), (Byte.repr 219, Byte.repr 236, Byte.repr 232, Byte.repr 135), (Byte.repr 111, Byte.repr 155, Byte.repr 110, Byte.repr  18), (Byte.repr  24, Byte.repr 232, Byte.repr  95, Byte.repr 158),
   (Byte.repr 26, Byte.repr 110, Byte.repr 170, Byte.repr 154), (Byte.repr 109, Byte.repr  42, Byte.repr 178, Byte.repr 168), (Byte.repr 156, Byte.repr 240, Byte.repr 248, Byte.repr 238), (Byte.repr 168, Byte.repr 196, Byte.repr 190, Byte.repr 203),
   (Byte.repr 69, Byte.repr 144, Byte.repr  51, Byte.repr  57), (Byte.repr  29, Byte.repr  29, Byte.repr 150, Byte.repr  26), (Byte.repr 150, Byte.repr  30, Byte.repr 235, Byte.repr 249), (Byte.repr 190, Byte.repr 163, Byte.repr 251, Byte.repr  48),
   (Byte.repr 27, Byte.repr 111, Byte.repr 114, Byte.repr 114), (Byte.repr 118, Byte.repr  40, Byte.repr 152, Byte.repr 157), (Byte.repr 180, Byte.repr  57, Byte.repr  27, Byte.repr  94), (Byte.repr 107, Byte.repr  42, Byte.repr 236, Byte.repr  35)).
reflexivity. Qed.

(*Bernsteins's final test case (Salsa20^1000000 (...) = (...) is unlikely to terminate even using
  vm_compute (running time of the above Salsa 20's is about 5secs for the reflexivity, plus 2secs for the Qed) so we're not testing it.*)

Definition Sigma0:QuadByte := (Byte.repr 101, Byte.repr 120, Byte.repr 112, Byte.repr 97).
Definition Sigma1:QuadByte := (Byte.repr 110, Byte.repr 100, Byte.repr 32, Byte.repr 51).
Definition Sigma2:QuadByte := (Byte.repr 50, Byte.repr 45, Byte.repr 98, Byte.repr 121).
Definition Sigma3:QuadByte := (Byte.repr 116, Byte.repr 101, Byte.repr 32, Byte.repr 107).

Definition Salsa20K0K1 (k0 k1 n:  QuadByte * QuadByte * QuadByte * QuadByte):SixtyFourByte :=
  match k0 with (a, b, c, d) =>
  match k1 with (e, f, g, h) =>
  match n with (i, j, k, l) =>
  Salsa20 (Sigma0, a, b, c, d, Sigma1, i, j, k, l, Sigma2, e, f, g, h, Sigma3)
  end end end.

Definition Tau0:QuadByte := (Byte.repr 101, Byte.repr 120, Byte.repr 112, Byte.repr 97).
Definition Tau1:QuadByte := (Byte.repr 110, Byte.repr 100, Byte.repr 32, Byte.repr 49).
Definition Tau2:QuadByte := (Byte.repr 54, Byte.repr 45, Byte.repr 98, Byte.repr 121).
Definition Tau3:QuadByte := (Byte.repr 116, Byte.repr 101, Byte.repr 32, Byte.repr 107).

Definition Salsa20K (k n:  QuadByte * QuadByte * QuadByte * QuadByte):SixtyFourByte :=
  match k with (a, b, c, d) =>
  match n with (i, j, k, l) =>
  Salsa20 (Tau0, a, b, c, d, Tau1, i, j, k, l, Tau2, a, b, c, d, Tau3)
  end end.

Definition K0 : QuadByte * QuadByte * QuadByte * QuadByte :=
  ((Byte.repr 1, Byte.repr 2, Byte.repr 3, Byte.repr 4),
   (Byte.repr 5, Byte.repr 6, Byte.repr 7, Byte.repr 8),
   (Byte.repr 9, Byte.repr 10, Byte.repr 11, Byte.repr 12),
   (Byte.repr 13, Byte.repr 14, Byte.repr 15, Byte.repr 16)).

Definition K1 : QuadByte * QuadByte * QuadByte * QuadByte :=
  ((Byte.repr 201, Byte.repr 202, Byte.repr 203, Byte.repr 204),
   (Byte.repr 205, Byte.repr 206, Byte.repr 207, Byte.repr 208),
   (Byte.repr 209, Byte.repr 210, Byte.repr 211, Byte.repr 212),
   (Byte.repr 213, Byte.repr 214, Byte.repr 215, Byte.repr 216)).

Definition n : QuadByte * QuadByte * QuadByte * QuadByte :=
  ((Byte.repr 101, Byte.repr 102, Byte.repr 103, Byte.repr 104),
   (Byte.repr 105, Byte.repr 106, Byte.repr 107, Byte.repr 108),
   (Byte.repr 109, Byte.repr 110, Byte.repr 111, Byte.repr 112),
   (Byte.repr 113, Byte.repr 114, Byte.repr 115, Byte.repr 116)).

Goal Salsa20K0K1 K0 K1 n =
  ((Byte.repr 69, Byte.repr  37, Byte.repr  68, Byte.repr  39), (Byte.repr  41, Byte.repr  15, Byte.repr 107, Byte.repr 193), (Byte.repr 255, Byte.repr 139, Byte.repr 122, Byte.repr  6), (Byte.repr 170, Byte.repr 233, Byte.repr 217, Byte.repr  98),
   (Byte.repr 89, Byte.repr 144, Byte.repr 182, Byte.repr 106), (Byte.repr  21, Byte.repr  51, Byte.repr 200, Byte.repr  65), (Byte.repr 239, Byte.repr  49, Byte.repr 222, Byte.repr  34), (Byte.repr 215, Byte.repr 114, Byte.repr  40, Byte.repr 126),
   (Byte.repr 104, Byte.repr 197, Byte.repr  7, Byte.repr 225), (Byte.repr 197, Byte.repr 153, Byte.repr  31, Byte.repr  2), (Byte.repr 102, Byte.repr  78, Byte.repr  76, Byte.repr 176), (Byte.repr  84, Byte.repr 245, Byte.repr 246, Byte.repr 184),
   (Byte.repr 177, Byte.repr 160, Byte.repr 133, Byte.repr 130), (Byte.repr  6, Byte.repr  72, Byte.repr 149, Byte.repr 119), (Byte.repr 192, Byte.repr 195, Byte.repr 132, Byte.repr 236), (Byte.repr 234, Byte.repr 103, Byte.repr 246, Byte.repr  74)).
reflexivity. Qed.

Goal Salsa20K K0 n =
  ((Byte.repr 39, Byte.repr 173, Byte.repr  46, Byte.repr 248), (Byte.repr  30, Byte.repr 200, Byte.repr  82, Byte.repr  17), (Byte.repr  48, Byte.repr  67, Byte.repr 254, Byte.repr 239), (Byte.repr  37, Byte.repr  18, Byte.repr  13, Byte.repr 247),
   (Byte.repr 241, Byte.repr 200, Byte.repr  61, Byte.repr 144), (Byte.repr  10, Byte.repr  55, Byte.repr  50, Byte.repr 185), (Byte.repr  6, Byte.repr  47, Byte.repr 246, Byte.repr 253), (Byte.repr 143, Byte.repr  86, Byte.repr 187, Byte.repr 225),
   (Byte.repr 134, Byte.repr  85, Byte.repr 110, Byte.repr 246), (Byte.repr 161, Byte.repr 163, Byte.repr  43, Byte.repr 235), (Byte.repr 231, Byte.repr  94, Byte.repr 171, Byte.repr  51), (Byte.repr 145, Byte.repr 214, Byte.repr 112, Byte.repr  29),
   (Byte.repr 14, Byte.repr 232, Byte.repr  5, Byte.repr  16), (Byte.repr 151, Byte.repr 140, Byte.repr 183, Byte.repr 141), (Byte.repr 171, Byte.repr  9, Byte.repr 122, Byte.repr 181), (Byte.repr 104, Byte.repr 182, Byte.repr 177, Byte.repr 193)).
reflexivity. Qed.

Goal SHA256.str_to_bytes "expand 32-byte k" =
  match Sigma0 with (a, b, c, d) =>
  match Sigma1 with (e, f, g, h) =>
  match Sigma2 with (i, j, k, l) =>
  match Sigma3 with (m, n, o, p) =>
   [a; b; c; d; e; f; g; h; i; j; k; l; m; n; o; p]
  end end end end.
reflexivity. Qed.

Goal SHA256.str_to_bytes "expand 16-byte k" =
  match Tau0 with (a, b, c, d) =>
  match Tau1 with (e, f, g, h) =>
  match Tau2 with (i, j, k, l) =>
  match Tau3 with (m, n, o, p) =>
   [a; b; c; d; e; f; g; h; i; j; k; l; m; n; o; p]
  end end end end.
reflexivity. Qed.

(*Next, the HSalsa20/r function from Bernstein's paper "Extending the Salsa20 nonce"*)
Definition ThirtyTwoByte:Type :=
 (QuadByte * QuadByte * QuadByte * QuadByte * QuadByte * QuadByte * QuadByte * QuadByte)%type.

Definition SixteenByte:Type := (QuadByte * QuadByte * QuadByte * QuadByte)%type.
Definition Salsa20_constant : QuadWord :=
 (x2i "61707865", x2i "3320646e", x2i "79622d32", x2i "6b206574").

(*Note: we expect clients to do the halfing of the inout argument: we do r rounds, not r/2*)
Definition HSalsa20_k_n_2r (r:nat) (k:ThirtyTwoByte) (nonce:SixteenByte):SixteenWord :=
  match k with (q1, q2, q3, q4, q11, q12, q13, q14) =>
  match nonce with (q6, q7, q8, q9) =>
    let x1 := littleendian q1 in
    let x2 := littleendian q2 in
    let x3 := littleendian q3 in
    let x4 := littleendian q4 in
    let x6 := littleendian q6 in
    let x7 := littleendian q7 in
    let x8 := littleendian q8 in
    let x9 := littleendian q9 in
    let x11 := littleendian q11 in
    let x12 := littleendian q12 in
    let x13 := littleendian q13 in
    let x14 := littleendian q14 in
  match Salsa20_constant with (x0, x5, x10, x15) =>
    rounds r
       ((x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15))
  end end end.

Definition HSalsa20 (r:nat) (k:ThirtyTwoByte) (nonce:SixteenByte):ThirtyTwoByte :=
  match HSalsa20_k_n_2r r k nonce
    with ((z0,  z1,  z2,  z3), (z4,  z5,  z6, z7),
          (z8,  z9, z10, z11), (z12, z13, z14, z15))
    => (littleendian_invert z0,
         littleendian_invert z5,
         littleendian_invert z10,
         littleendian_invert z15,
         littleendian_invert z6,
         littleendian_invert z7,
         littleendian_invert z8,
         littleendian_invert z9)
     end.
Definition HSalsa20_k_n_2r' (r:nat) (k:ThirtyTwoByte) (nonce:SixteenByte):SixtyFourByte:=
  match k with (q1, q2, q3, q4, q11, q12, q13, q14) =>
  match nonce with (q6, q7, q8, q9) =>
    let x1 := littleendian q1 in
    let x2 := littleendian q2 in
    let x3 := littleendian q3 in
    let x4 := littleendian q4 in
    let x6 := littleendian q6 in
    let x7 := littleendian q7 in
    let x8 := littleendian q8 in
    let x9 := littleendian q9 in
    let x11 := littleendian q11 in
    let x12 := littleendian q12 in
    let x13 := littleendian q13 in
    let x14 := littleendian q14 in
  match Salsa20_constant with (x0, x5, x10, x15) =>
  match rounds r
       ((x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15))
  with ((w0, w1, w2, w3), (w4, w5, w6, w7), (w8, w9, w10, w11), (w12, w13, w14, w15)) =>
     map16 littleendian_invert (w0, w1, w2, w3, w4, w5, w6, w7,
                               w8, w9, w10, w11, w12, w13, w14, w15)
  end end end end.

Definition TwentyFourByte:Type := (QuadByte * QuadByte * QuadByte * QuadByte * QuadByte * QuadByte)%type.
Definition EightByte:Type := (QuadByte * QuadByte)%type.

(*Note: we expect clients to do the halfing of the input argument: we do r rounds, not r/2.
(Note: by using return type SixteenWord rather than SixtyFourByte, we avoid a littleendian-conversion
 roundtrip at the boundary between XSalsa20_k_n_cntr_2r and XSalsa20*)
Definition XSalsa20_k_n_cntr_2r (r:nat) (k:ThirtyTwoByte) (nonce:TwentyFourByte)(cntr:EightByte)
  :(*SixtyFourByte*)SixteenWord :=
  match k with (q1, q2, q3, q4, q11, q12, q13, q14) =>
  match nonce with (q6, q7, q8, q9, x6', x7') =>
    let x1 := littleendian q1 in
    let x2 := littleendian q2 in
    let x3 := littleendian q3 in
    let x4 := littleendian q4 in
    let x6 := littleendian q6 in
    let x7 := littleendian q7 in
    let x8 := littleendian q8 in
    let x9 := littleendian q9 in
    let x11 := littleendian q11 in
    let x12 := littleendian q12 in
    let x13 := littleendian q13 in
    let x14 := littleendian q14 in
  match Salsa20_constant with (x0, x5, x10, x15) =>
  match rounds r
       ((x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15))
  with ((z0,  z1,  z2,  z3), (z4,  z5,  z6, z7),
        (z8,  z9, z10, z11), (z12, z13, z14, z15)) =>
  match cntr with (x8', x9') =>
       ((x0, z0, z5, z10),
        (z15, x5, littleendian x6', littleendian x7'),
        (littleendian x8', littleendian x9', x10, z6),
        (z7, z8, z9, x15))
  end end end end end.

Definition XSalsa20 (r:nat) (k:ThirtyTwoByte) (nonce:TwentyFourByte)(cntr:EightByte)
  :SixtyFourByte :=
  match XSalsa20_k_n_cntr_2r r k nonce cntr with
   ((x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15))
  =>
  match rounds r ((x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15))

  with ((z0,  z1,  z2,  z3), (z4,  z5,  z6, z7),
        (z8,  z9, z10, z11), (z12, z13, z14, z15))
    => map16 littleendian_invert (sum z0 x0, sum z1 x1,sum z2 x2 ,sum z3 x3,
                             sum z4 x4, sum z5 x5, sum z6 x6, sum z7 x7,
                             sum z8 x8, sum z9 x9, sum z10 x10, sum z11 x11,
                             sum z12 x12, sum z13 x13, sum z14 x14, sum z15 x15)
     end
  end.

Definition XSalsa20_k_n_cntr_2r' (r:nat) (k:ThirtyTwoByte) (nonce:TwentyFourByte)(cntr:EightByte)
  :SixtyFourByte :=
  match k with (q1, q2, q3, q4, q11, q12, q13, q14) =>
  match nonce with (q6, q7, q8, q9, x6', x7') =>
    let x1 := littleendian q1 in
    let x2 := littleendian q2 in
    let x3 := littleendian q3 in
    let x4 := littleendian q4 in
    let x6 := littleendian q6 in
    let x7 := littleendian q7 in
    let x8 := littleendian q8 in
    let x9 := littleendian q9 in
    let x11 := littleendian q11 in
    let x12 := littleendian q12 in
    let x13 := littleendian q13 in
    let x14 := littleendian q14 in
  match Salsa20_constant with (x0, x5, x10, x15) =>
  match rounds r
       ((x0, x1, x2, x3), (x4, x5, x6, x7), (x8, x9, x10, x11), (x12, x13, x14, x15))
  with ((z0,  z1,  z2,  z3), (z4,  z5,  z6, z7),
        (z8,  z9, z10, z11), (z12, z13, z14, z15)) =>
  match cntr with (x8', x9') =>
       (littleendian_invert x0, littleendian_invert z0, littleendian_invert z5, littleendian_invert z10,
        littleendian_invert z15, littleendian_invert x5, x6', x7',
        x8', x9', littleendian_invert x10, littleendian_invert z6,
        littleendian_invert z7, littleendian_invert z8, littleendian_invert z9, littleendian_invert x15)
  end end end end end.

Lemma littleendian_inv b:
  littleendian_invert (littleendian b) = b.
Proof. destruct b as [[[b0 b1] b2] b3].
  unfold littleendian_invert, littleendian.
  destruct (Byte.unsigned_range_2 b0). destruct (Byte.unsigned_range_2 b1).
  destruct (Byte.unsigned_range_2 b2). destruct (Byte.unsigned_range_2 b3).
  assert (2 ^ 8 * Byte.unsigned b1 <= 2 ^ 8 * Byte.max_unsigned).
               apply Zmult_le_compat_l; trivial.
  assert (2 ^ 16 * Byte.unsigned b2 <= 2 ^ 16 * Byte.max_unsigned).
               apply Zmult_le_compat_l; trivial.
  assert (2 ^ 24 * Byte.unsigned b3 <= 2 ^ 24 * Byte.max_unsigned).
               apply Zmult_le_compat_l; trivial.
  assert (0 <= 2 ^ 8 * Byte.unsigned b1). apply Z.mul_nonneg_cancel_l; trivial.
  assert (0 <= 2 ^ 16 * Byte.unsigned b2). apply Z.mul_nonneg_cancel_l; trivial.
  assert (0 <= 2 ^ 24 * Byte.unsigned b3). apply Z.mul_nonneg_cancel_l; trivial.
  rewrite Int.unsigned_repr.
  2:{ split. clear H0 H2 H4 H6.
             apply OMEGA2; trivial.
             apply OMEGA2; trivial.
             apply OMEGA2; trivial.
            eapply Z.le_trans. apply Z.add_le_mono; try eassumption.
              apply Z.add_le_mono; try eassumption.
              apply Z.add_le_mono; eassumption.
              compute. clear; congruence.
  }
  assert (0 <= Byte.unsigned b0 + 2 ^ 8 * Byte.unsigned b1 + 2 ^ 16 * Byte.unsigned b2 < 2 ^ 24).
              split. apply OMEGA2; trivial. apply OMEGA2; trivial.
              assert (Byte.unsigned b0 + 2 ^ 8 * Byte.unsigned b1 + 2 ^ 16 * Byte.unsigned b2 <= 2 ^ 24 -1). 2: omega.
              eapply Z.le_trans. apply Z.add_le_mono; try eassumption.
              apply Z.add_le_mono; try eassumption. simpl. omega.
  erewrite (Zmod_unique _ (2^24) (Byte.unsigned b3)); try eassumption.
  2:{ rewrite (Z.mul_comm (2^24)). rewrite Z.add_comm. reflexivity. }
  assert (0 <= Byte.unsigned b0 + 2 ^ 8 * Byte.unsigned b1 < 2 ^ 16).
             split. apply OMEGA2; trivial.
              assert (Byte.unsigned b0 + 2 ^ 8 * Byte.unsigned b1 <= 2 ^ 16 -1). 2: omega.
              eapply Z.le_trans. apply Z.add_le_mono; try eassumption.
              simpl. omega.
  erewrite (Zmod_unique _ (2^16) (Byte.unsigned b2)); try eassumption.
  2:{ rewrite (Z.mul_comm (2^16)). rewrite Z.add_comm. reflexivity. }
  erewrite (Zmod_unique _ (2^8) (Byte.unsigned b1)).
  2:{ rewrite (Z.mul_comm (2^8)). rewrite Z.add_comm. reflexivity. }
     2: apply Byte.unsigned_range.
  rewrite Byte.repr_unsigned.
    erewrite (Zdiv_unique _ _ (Byte.unsigned b1)).
      rewrite Byte.repr_unsigned.
      erewrite (Zdiv_unique _ _ (Byte.unsigned b2)).
        rewrite Byte.repr_unsigned.
        erewrite (Zdiv_unique _ _ (Byte.unsigned b3)).
          rewrite Byte.repr_unsigned. reflexivity.
      rewrite (Z.mul_comm (2^24)). rewrite Z.add_comm. reflexivity.
      assumption.
    rewrite (Z.mul_comm (2^16)). rewrite Z.add_comm. reflexivity.
    assumption.
  rewrite (Z.mul_comm (2^8)). rewrite Z.add_comm. reflexivity.
  apply Byte.unsigned_range.
Qed.

Lemma inv_littleendian b:
  littleendian (littleendian_invert b) = b.
Proof.
  unfold littleendian_invert, littleendian.
  rewrite Byte.unsigned_repr.
  2:{ assert (0 <= ((Int.unsigned b mod 2 ^ 24) mod 2 ^ 16) mod 2 ^ 8 < Byte.max_unsigned +1). 2:omega.
           apply Z_mod_lt. simpl; omega. }
  rewrite <- Zmod_div_mod; trivial. 2: exists (2^8); trivial.
  rewrite <- Zmod_div_mod; trivial. 2: exists (2^16); trivial.
  rewrite <- Zmod_div_mod; trivial. 2: exists (2^8); trivial.
  assert (Q1: 0 <= Int.unsigned b mod 2 ^ 16 / 2 ^ 8 <= Byte.max_unsigned).
    destruct (Z_mod_lt (Int.unsigned b) (2 ^ 16)). cbv; trivial.
           split. apply Z_div_pos; trivial. cbv; trivial.
           remember (Int.unsigned b mod 2 ^ 16).
           assert (z / 2 ^ 8 < Byte.max_unsigned + 1). 2: omega.
           assert (Byte.max_unsigned + 1 = 2^8) by reflexivity. rewrite H1; clear H1.
           apply Zdiv_lt_upper_bound; trivial.
  rewrite Byte.unsigned_repr; trivial.
  assert (Q2: 0 <= Int.unsigned b mod 2 ^ 24 / 2 ^ 16 <= Byte.max_unsigned).
    destruct (Z_mod_lt (Int.unsigned b) (2 ^ 24)). cbv; trivial.
           split. apply Z_div_pos; trivial. cbv; trivial.
           remember (Int.unsigned b mod 2 ^ 24).
           assert (z / 2 ^ 16 < Byte.max_unsigned + 1). 2: omega.
           assert (Byte.max_unsigned + 1 = 2^8) by reflexivity. rewrite H1; clear H1.
           apply Zdiv_lt_upper_bound; trivial.
  rewrite Byte.unsigned_repr; trivial.
  assert (Q3: 0 <= Int.unsigned b / 2 ^ 24 <= Byte.max_unsigned).
           split. apply Z_div_pos; trivial. cbv; trivial. apply Int.unsigned_range.
           remember (Int.unsigned b).
           assert (z / 2 ^ 24 < Byte.max_unsigned + 1). 2: omega.
           assert (Byte.max_unsigned + 1 = 2^8) by reflexivity. rewrite H; clear H.
           apply Zdiv_lt_upper_bound; trivial. subst z. apply Int.unsigned_range.
  rewrite Byte.unsigned_repr; trivial.
  assert (Int.repr
  (Int.unsigned b mod 2 ^ 8 + 2 ^ 8 * (Int.unsigned b mod 2 ^ 16 / 2 ^ 8) +
   2 ^ 16 * (Int.unsigned b mod 2 ^ 24 / 2 ^ 16) +
   2 ^ 24 * (Int.unsigned b / 2 ^ 24)) = Int.repr (Int.unsigned b)).
  2: rewrite Int.repr_unsigned in *; trivial.
  f_equal. remember (Int.unsigned b).
  assert (z mod 2 ^ 8 + 2 ^ 8 * (z mod 2 ^ 16 / 2 ^ 8) +
         2 ^ 16 * (z mod 2 ^ 24 / 2 ^ 16) + 2 ^ 24 * (z / 2 ^ 24) =
      2 ^ 24 * (z / 2 ^ 24) + z mod 2 ^ 24).
  2:{ rewrite <- (Z.div_mod z (2^24)) in H. assumption. cbv; omega. }
  rewrite Z.add_comm. f_equal.
  assert (z mod 2 ^ 8 + 2 ^ 8 * (z mod 2 ^ 16 / 2 ^ 8) +
            2 ^ 16 * (z mod 2 ^ 24 / 2 ^ 16) =
     2 ^ 16 * (z mod 2 ^ 24 / 2 ^ 16) + (z mod 2 ^ 24) mod 2 ^ 16).
  2:{ rewrite <- (Z.div_mod (z mod 2 ^ 24) (2^16)) in H. assumption. cbv; omega. }
  rewrite Z.add_comm. f_equal.
  rewrite <- Zmod_div_mod; trivial. 2: exists (2^8); trivial.
  assert (z mod 2 ^ 8 + 2 ^ 8 * (z mod 2 ^ 16 / 2 ^ 8) =
          2 ^ 8 * (z mod 2 ^ 16 / 2 ^ 8) + (z mod 2 ^ 16) mod 2 ^ 8).
  2:{ rewrite <- (Z.div_mod (z mod 2 ^ 16) (2^8)) in H. assumption. cbv; omega. }
  rewrite <- Zmod_div_mod; trivial. 2: exists (2^8); trivial.
  apply Z.add_comm.
Qed.

Lemma littleendian_inv_iff q i:
    littleendian i = q <-> littleendian_invert q = i.
split; intros; subst.
apply littleendian_inv.
apply inv_littleendian.
Qed.

Module Type GeneralizedCascade.
  Parameter K1 : Type. (*finite*)
  Parameter I1 : Type.
  Parameter K2 : Type. (*finite*)
  Parameter H: K1 -> I1 -> K2.
  Parameter I2 : Type.
  Parameter L : Type.
  Parameter S : K2 -> I2 -> L.
  Parameter X : K1 -> I1 -> I2 -> L.
  Parameter X_char : forall k1 i1 i2, X k1 i1 i2 = S (H k1 i1) i2.
End GeneralizedCascade.


Module SalsaGeneralizedCascade <: GeneralizedCascade.
  Definition K1:Type := ThirtyTwoByte.
  Definition I1:Type := SixteenByte.
  Definition K2:Type := ThirtyTwoByte.
  Definition H: K1 -> I1 -> K2 := HSalsa20 10.
  Definition I2:Type := SixteenByte.
  Definition L:Type := SixtyFourByte.
  Definition X (k1:K1) (i1: I1) (i2: I2): L :=
    match i1 with (((x, y), z), u) =>
    match i2 with (((a, b), c), d) =>
       XSalsa20 10 k1 (x, y, z, u, a, b) (c, d)
    end end.

  Definition S (k: K2) (i: I2) : L :=
    match k with (((((((k0, k1), k2), k3), k4), k5), k6), k7) =>
     Salsa20K0K1 (((k0, k1), k2), k3) (((k4, k5), k6), k7) i
    end.

  Lemma X_char k1 i1 i2: X k1 i1 i2 = S (H k1 i1) i2.
    unfold X, S, H.
    destruct k1 as (((((((k0, k1), k2), k3), k4), k5), k6), k7).
    destruct i1 as (((a, b), c), d).
    destruct i2 as (((x, y), z), u).
    unfold HSalsa20, XSalsa20.
    unfold XSalsa20_k_n_cntr_2r, HSalsa20_k_n_2r. unfold Salsa20K0K1. unfold Salsa20.
    unfold Sigma0, Sigma1, Sigma2, Sigma3.
    unfold Salsa20_constant.
    remember (rounds 10
           (x2i "61707865", littleendian k0, littleendian k1,
           littleendian k2,
           (littleendian k3, x2i "3320646e", littleendian a, littleendian b),
           (littleendian c, littleendian d, x2i "79622d32", littleendian k4),
           (littleendian k5, littleendian k6, littleendian k7,
           x2i "6b206574"))) as ROUND1.
    destruct ROUND1 as (((qw1, qw2), qw3), qw4).
    destruct qw1 as (((w0, w1), w2), w3).
    destruct qw2 as (((w4, w5), w6), w7).
    destruct qw3 as (((w8, w9), w10), w11).
    destruct qw4 as (((w12, w13), w14), w15).
    clear HeqROUND1.
    unfold map16.
    remember (littleendian
                                     (Byte.repr 101, Byte.repr 120,
                                     Byte.repr 112, Byte.repr 97),
                                  littleendian (littleendian_invert w0),
                                  littleendian (littleendian_invert w5),
                                  littleendian (littleendian_invert w10),
                                  (littleendian (littleendian_invert w15),
                                  littleendian
                                    (Byte.repr 110, Byte.repr 100,
                                    Byte.repr 32, Byte.repr 51),
                                  littleendian x, littleendian y),
                                  (littleendian z, littleendian u,
                                  littleendian
                                    (Byte.repr 50, Byte.repr 45,
                                    Byte.repr 98, Byte.repr 121),
                                  littleendian (littleendian_invert w6)),
                                  (littleendian (littleendian_invert w7),
                                  littleendian (littleendian_invert w8),
                                  littleendian (littleendian_invert w9),
                                  littleendian
                                    (Byte.repr 116, Byte.repr 101,
                                    Byte.repr 32, Byte.repr 107))) as RHS.
    remember
       (x2i "61707865", w0, w5, w10,
       (w15, x2i "3320646e", littleendian x, littleendian y),
       (littleendian z, littleendian u, x2i "79622d32", w6),
       (w7, w8, w9, x2i "6b206574")) as LHS.
    assert (LHS = RHS).
      subst. repeat rewrite inv_littleendian. reflexivity.
    rewrite H0. clear H0 HeqLHS HeqRHS LHS.
    unfold x2i, rounds.
    remember (doubleround
       (doubleround
          (doubleround
             (doubleround
                (doubleround
                   (doubleround
                      (doubleround
                         (doubleround (doubleround (doubleround RHS)))))))))) as ROUND2.
    clear HeqROUND2 RHS.
    destruct ROUND2 as (((qw0, qw1), qw2), qw3).
    destruct qw0 as (((x0, x1), x2), x3).
    destruct qw1 as (((x4, x5), x6), x7).
    destruct qw2 as (((x8, x9), x10), x11).
    destruct qw3 as (((x12, x13), x14), x15).
    repeat rewrite inv_littleendian. reflexivity.
Qed.
End SalsaGeneralizedCascade.
Check SalsaGeneralizedCascade.X_char.
(*About 1 day*)