Require Import Recdef.
Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.
(*
Require Import split_array_lemmas.
Require Import fragments.*)
Require Import ZArith. 
Require Import Salsa20.
Require Import tweetNaclBase.
Require Import verif_salsa_base.

Require Import tweetnaclVerifiableC.
Require Import Snuffle.

(*from spec_sha*)
Definition data_block (sh: share) (contents: list Z):val -> mpred :=
  !! Forall isbyteZ contents &&
  data_at sh (tarray tuchar (Zlength contents)) (map Vint (map Int.repr contents)).

Definition CoreInSEP (data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte)) 
                     (v: val * val * val) : mpred :=
  match data with (Nonce, C, K) =>
  match v with (n, c, k) => 
   (SByte Nonce n) * (SByte C c) * (ThirtyTwoByte K k)
  end end.

Definition prepare_data 
           (data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte)) :=
match data with ((Nonce, C), K) =>
  match Nonce with (N1, N2, N3, N4) => 
  match C with (C1, C2, C3, C4) => 
  match K with ((K1, K2, K3, K4), (L1, L2, L3, L4)) => 
      map littleendian [C1; K1; K2; K3; K4; C2; N1; N2; N3; N4; C3; L1; L2; L3; L4; C4]
  end end end
end.

Lemma prepare_data_length x: length (prepare_data x) = 16%nat.
Proof. destruct x as [[s0 s1] [s2 s3]]. simpl.
  destruct s0 as [[[? ?] ?] ?].
  destruct s1 as [[[? ?] ?] ?].
  destruct s2 as [[[? ?] ?] ?].
  destruct s3 as [[[? ?] ?] ?]. reflexivity.
Qed.

Definition sumlist := combinelist _ Int.add.

Definition sumlist_Some:= combinelist _ Int.add.

Definition sumlist_SomeInv:= combinelist_SomeInv _ Int.add.

Definition sumlist_length:= combinelist_length _ Int.add.

Definition sumlist_symm:= combinelist_symm _ Int.add Int.add_commut. 

Definition sumlist_char_nth:= combinelist_char_nth _ Int.add.

Definition sumlist_char_Znth:= combinelist_char_Znth _ Int.add.

Definition Snuffle20 x := bind (Snuffle 20 x) (fun y => sumlist y x).

Lemma Snuffle20_length s l: Snuffle20 s = Some l -> length s = 16%nat -> length l = 16%nat.
Proof. unfold Snuffle20, bind; intros. remember (Snuffle 20 s).
  destruct o; simpl. 
    symmetry in Heqo. symmetry in H; rewrite sumlist_symm in H.
      rewrite (sumlist_length _ _ _ H).
      apply (Snuffle_length _ _ _ Heqo H0). inv H.
Qed.

Definition fcore_result h data l :=
  match Snuffle20 (prepare_data data) 
  with None => False
     | Some x => 
             if Int.eq (Int.repr h) Int.zero 
             then l=QuadChunks2ValList (map littleendian_invert x)
             else match data with ((Nonce, C), K) =>
                    match Nonce with (N1, N2, N3, N4) => 
                    match C with (C1, C2, C3, C4) => 
                    firstn 32 l = QuadByte2ValList (littleendian_invert (Int.sub (Znth 0 x Int.zero)  (littleendian C1))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 5 x Int.zero)  (littleendian C2))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 10 x Int.zero) (littleendian C3))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 15 x Int.zero) (littleendian C4))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 6 x Int.zero)  (littleendian N1))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 7 x Int.zero)  (littleendian N2))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 8 x Int.zero)  (littleendian N3))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 9 x Int.zero)  (littleendian N4)))
                    end end end
  end.

Definition fcorePOST_SEP data d out RESULT :=
  CoreInSEP data d *
  data_at Tsh (tarray tuchar 64) RESULT out.

Definition f_core_POST d out h (data: SixteenByte * SixteenByte * (SixteenByte * SixteenByte) ) := 
EX RESULT:_,     
   PROP (fcore_result h data RESULT)
   LOCAL ()
   SEP (`(fcorePOST_SEP data d out RESULT)).

Definition core_spec :=
  DECLARE _core
   WITH c : val, k:val, h:Z,
        nonce:val, out:val, OUT: list val,
        data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte)
   PRE [ _out OF tptr tuchar,
         _in OF tptr tuchar,
         _k OF tptr tuchar,
         _c OF tptr tuchar,
         _h OF tint ]
      PROP ((*length OUT = 64%nat*))
      LOCAL (temp _in nonce; temp _out out; 
             temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
      SEP ( `(CoreInSEP data (nonce, c, k)); 
            `(data_at Tsh (tarray tuchar 64) OUT out))
  POST [ tvoid ] (f_core_POST (nonce, c, k) out h data).

Definition ld32_spec :=
  DECLARE _ld32
   WITH x : val, B:QuadByte
   PRE [ _x OF tptr tuchar ]
      PROP ()
      LOCAL (temp _x x)
      SEP ( `(data_at Tsh (Tarray tuchar 4 noattr) (QuadByte2ValList B) x))
  POST [ tuint ] 
     PROP ()
     LOCAL (temp ret_temp (Vint (littleendian B)))
     SEP (`(QByte B x)).

Definition st32_spec :=
  DECLARE _st32
   WITH x : val, u:int
   PRE [ _x OF tptr tuchar, _u OF tuint ]
      PROP ()
      LOCAL (temp _x x; temp _u (Vint u))
      SEP (`(EX l:_, !!(Zlength l = 4) && data_at Tsh (Tarray tuchar 4 noattr) l x))
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (`(QByte (littleendian_invert u) x)).

Definition L32_spec :=
  DECLARE _L32
   WITH x : int, c: int
   PRE [ _x OF tuint, _c OF tint ]
      PROP (0 < Int.unsigned c < 32) (*yes, c=Int.zero needs to be ruled out - it leads to undefined behaviour in the shift-right operation*)
      LOCAL (temp _x (Vint x); temp _c (Vint c))
      SEP ()
  POST [ tuint ] 
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.rol x c)))
     SEP ().

Definition crypto_core_salsa20_spec :=
  DECLARE _crypto_core_salsa20_tweet
   WITH c : val, k:val, 
        nonce:val, out:val, OUT: list val,
        data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte)
   PRE [ _out OF tptr tuchar,
         _in OF tptr tuchar,
         _k OF tptr tuchar,
         _c OF tptr tuchar ]
      PROP ((*length OUT = 64%nat*))
      LOCAL (temp _in nonce; temp _out out; 
             temp _c c; temp _k k)
      SEP ( `(CoreInSEP data (nonce, c, k)); 
            `(data_at Tsh (tarray tuchar 64) OUT out))
  POST [ tint ] 
       EX l:_, 
       PROP (exists x, Snuffle20 (prepare_data data) = Some x /\
             l=QuadChunks2ValList (map littleendian_invert x))
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (`(CoreInSEP data (nonce, c, k)); `(data_at Tsh (tarray tuchar 64) l out)).
            
Definition crypto_core_hsalsa20_spec :=
  DECLARE _crypto_core_hsalsa20_tweet
   WITH c : val, k:val, 
        nonce:val, out:val, OUT: list val,
        data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte)
   PRE [ _out OF tptr tuchar,
         _in OF tptr tuchar,
         _k OF tptr tuchar,
         _c OF tptr tuchar ]
      PROP ((*length OUT = 64%nat*))
      LOCAL (temp _in nonce; temp _out out; 
             temp _c c; temp _k k)
      SEP ( `(CoreInSEP data (nonce, c, k)); 
            `(data_at Tsh (tarray tuchar 64) OUT out))
  POST [ tint ] 
       EX l:_, 
       PROP (exists x, Snuffle 20 (prepare_data data) = Some x /\
             firstn 32 l = QuadByte2ValList (littleendian_invert (Znth 0  x Int.zero)) ++
                            QuadByte2ValList (littleendian_invert (Znth 5  x Int.zero)) ++
                            QuadByte2ValList (littleendian_invert (Znth 10 x Int.zero)) ++
                            QuadByte2ValList (littleendian_invert (Znth 15 x Int.zero)) ++
                            QuadByte2ValList (littleendian_invert (Znth 6  x Int.zero)) ++
                            QuadByte2ValList (littleendian_invert (Znth 7  x Int.zero)) ++
                            QuadByte2ValList (littleendian_invert (Znth 8  x Int.zero)) ++
                            QuadByte2ValList (littleendian_invert (Znth 9  x Int.zero)))
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (`(CoreInSEP data (nonce, c, k)); `(data_at Tsh (tarray tuchar 64) l out)).
(*Could stengthen postcondition to include the guarantee that second half of OUT 
  is not modified, by replacing firstn 32 l = ... by l = ... ++ Skipn32 OUT*)

Definition SalsaVarSpecs : varspecs := (_sigma, tarray tuchar 16)::nil.
Definition SalsaFunSpecs : funspecs := 
  core_spec :: ld32_spec :: L32_spec::st32_spec::crypto_core_salsa20_spec::crypto_core_hsalsa20_spec::nil.
