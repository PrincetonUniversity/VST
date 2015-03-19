
Require Import Arith.

Require Import Integers.
Require Import Coqlib.
Require Import List.
Require Import List. Import ListNotations.
Definition Blist := list bool.

Definition asZ (x : bool) : Z := if x then 1 else 0.

Lemma asZT: asZ true = 1. reflexivity. Qed.
Lemma asZF: asZ false = 0. reflexivity. Qed.


Definition convertByteBits (bits : Blist) (byte : Z) : Prop :=
  exists (b0 b1 b2 b3 b4 b5 b6 b7 : bool),
   bits = [b0; b1; b2; b3; b4; b5; b6; b7] /\
   byte =  (1 * (asZ b0) + 2 * (asZ b1) + 4 * (asZ b2) + 8 * (asZ b3)
         + 16 * (asZ b4) + 32 * (asZ b5) + 64 * (asZ b6) + 128 * (asZ b7)).
(* TODO: stuck here *)

Lemma AUX1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15: 
Z.lxor
  (1 * 1 + 2 * 1 + 4 * asZ b2 + 8 * asZ b3 + 16 * asZ b4 + 32 * asZ b5 +
   64 * asZ b6 + 128 * asZ b7)
  (1 * asZ b8 + 2 * asZ b9 + 4 * asZ b10 + 8 * asZ b11 + 16 * asZ b12 +
   32 * asZ b13 + 64 * asZ b14 + 128 * asZ b15) =
1 * (if negb b8 then 1 else 0) + 2 * (if negb b9 then 1 else 0) +
4 * (if xorb b2 b10 then 1 else 0) + 8 * (if xorb b3 b11 then 1 else 0) +
16 * (if xorb b4 b12 then 1 else 0) + 32 * (if xorb b5 b13 then 1 else 0) +
64 * (if xorb b6 b14 then 1 else 0) + 128 * (if xorb b7 b15 then 1 else 0).
Proof.
      destruct b2; try rewrite asZT; try rewrite asZF.
      { rewrite (xorb_true_l b10).
        destruct b3; try rewrite asZT; try rewrite asZF.
        { rewrite (xorb_true_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
        { rewrite (xorb_false_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
      }
      { rewrite (xorb_false_l b10).
        destruct b3; try rewrite asZT; try rewrite asZF.
        { rewrite (xorb_true_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
        { rewrite (xorb_false_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
      }
Qed.
Lemma AUX2 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15: 
Z.lxor (1 * 1 + 2 * 0 + 4 * asZ b2 + 8 * asZ b3 + 16 * asZ b4 + 32 * asZ b5 +
   64 * asZ b6 + 128 * asZ b7)
  (1 * asZ b8 + 2 * asZ b9 + 4 * asZ b10 + 8 * asZ b11 + 16 * asZ b12 +
   32 * asZ b13 + 64 * asZ b14 + 128 * asZ b15) =
1 * (if negb b8 then 1 else 0) + 2 * (if b9 then 1 else 0) +
4 * (if xorb b2 b10 then 1 else 0) + 8 * (if xorb b3 b11 then 1 else 0) +
16 * (if xorb b4 b12 then 1 else 0) + 32 * (if xorb b5 b13 then 1 else 0) +
64 * (if xorb b6 b14 then 1 else 0) + 128 * (if xorb b7 b15 then 1 else 0).
Proof.
      destruct b2; try rewrite asZT; try rewrite asZF.
      { rewrite (xorb_true_l b10).
        destruct b3; try rewrite asZT; try rewrite asZF.
        { rewrite (xorb_true_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
        { rewrite (xorb_false_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
      }
      { rewrite (xorb_false_l b10).
        destruct b3; try rewrite asZT; try rewrite asZF.
        { rewrite (xorb_true_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
        { rewrite (xorb_false_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
      }
Qed.

Lemma AUX3 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15: 
Z.lxor
  (1 * 0 + 2 * 1 + 4 * asZ b2 + 8 * asZ b3 + 16 * asZ b4 + 32 * asZ b5 +
   64 * asZ b6 + 128 * asZ b7)
  (1 * asZ b8 + 2 * asZ b9 + 4 * asZ b10 + 8 * asZ b11 + 16 * asZ b12 +
   32 * asZ b13 + 64 * asZ b14 + 128 * asZ b15) =
1 * (if b8 then 1 else 0) + 2 * (if negb b9 then 1 else 0) +
4 * (if xorb b2 b10 then 1 else 0) + 8 * (if xorb b3 b11 then 1 else 0) +
16 * (if xorb b4 b12 then 1 else 0) + 32 * (if xorb b5 b13 then 1 else 0) +
64 * (if xorb b6 b14 then 1 else 0) + 128 * (if xorb b7 b15 then 1 else 0).
Proof.
      destruct b2; try rewrite asZT; try rewrite asZF.
      { rewrite (xorb_true_l b10).
        destruct b3; try rewrite asZT; try rewrite asZF.
        { rewrite (xorb_true_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
        { rewrite (xorb_false_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
      }
      { rewrite (xorb_false_l b10).
        destruct b3; try rewrite asZT; try rewrite asZF.
        { rewrite (xorb_true_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
        { rewrite (xorb_false_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
      }
Qed.

Lemma AUX4 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15: 
Z.lxor (1 * 0 + 2 * 0 + 4 * asZ b2 + 8 * asZ b3 + 16 * asZ b4 + 32 * asZ b5 +
   64 * asZ b6 + 128 * asZ b7)
  (1 * asZ b8 + 2 * asZ b9 + 4 * asZ b10 + 8 * asZ b11 + 16 * asZ b12 +
   32 * asZ b13 + 64 * asZ b14 + 128 * asZ b15) =
1 * (if b8 then 1 else 0) + 2 * (if b9 then 1 else 0) +
4 * (if xorb b2 b10 then 1 else 0) + 8 * (if xorb b3 b11 then 1 else 0) +
16 * (if xorb b4 b12 then 1 else 0) + 32 * (if xorb b5 b13 then 1 else 0) +
64 * (if xorb b6 b14 then 1 else 0) + 128 * (if xorb b7 b15 then 1 else 0).
Proof.
      destruct b2; try rewrite asZT; try rewrite asZF.
      { rewrite (xorb_true_l b10).
        destruct b3; try rewrite asZT; try rewrite asZF.
        { rewrite (xorb_true_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
        { rewrite (xorb_false_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
      }
      { rewrite (xorb_false_l b10).
        destruct b3; try rewrite asZT; try rewrite asZF.
        { rewrite (xorb_true_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
        { rewrite (xorb_false_l b11).
          destruct b4; destruct b5; destruct b6; destruct b7; destruct b8; destruct b9; 
          destruct b10; destruct b11; destruct b12; destruct b13; destruct b14; destruct b15; trivial.
        }
      }
Qed.


Lemma xor_correspondence :
  forall (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : bool)
         (byte0 byte1 : Z),
    convertByteBits [b0; b1; b2; b3; b4; b5; b6; b7] byte0 ->
    convertByteBits [b8; b9; b10; b11; b12; b13; b14; b15] byte1 ->

    convertByteBits
      [xorb b0 b8; xorb b1 b9; xorb b2 b10; xorb b3 b11; 
       xorb b4 b12; xorb b5 b13; xorb b6 b14; xorb b7 b15]
      (Z.lxor byte0 byte1).
Proof.
  intros.
  generalize dependent H. generalize dependent H0. intros H0 H1.
  unfold convertByteBits. unfold asZ.

  do 8 eexists. split. reflexivity.
  unfold convertByteBits in *.

  destruct H0 as [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ]] ]] ].  (* nested 8 *)
  destruct H.
  symmetry in H.
  inversion H. clear H.
  subst.

  destruct H1 as [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ]] ]] ].  (* nested 8 *)
  destruct H.
  symmetry in H.
  inversion H. clear H.
  subst.
  destruct b0; try rewrite asZT; try rewrite asZF.
  { rewrite (xorb_true_l b8).
    destruct b1; try rewrite asZT; try rewrite asZF.
    { rewrite (xorb_true_l b9). apply AUX1. }
    { rewrite (xorb_false_l b9). apply AUX2. }
  }
  { rewrite (xorb_false_l b8).
    destruct b1; try rewrite asZT; try rewrite asZF.
    { rewrite (xorb_true_l b9). apply AUX3. }
    { rewrite (xorb_false_l b9). apply AUX4. }
  }
Qed.