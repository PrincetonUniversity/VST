Require Import Recdef.
Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import sha.general_lemmas.
Require Import ZArith.
Require Import tweetnacl20140427.Salsa20.
Require Import tweetnacl20140427.tweetNaclBase.
Require Import tweetnacl20140427.verif_salsa_base.

Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.Snuffle.
Require Import VST.floyd.library.

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
                    l = QuadByte2ValList (littleendian_invert (Int.sub (Znth 0 x)  (littleendian C1))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 5 x)  (littleendian C2))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 10 x) (littleendian C3))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 15 x) (littleendian C4))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 6 x)  (littleendian N1))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 7 x)  (littleendian N2))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 8 x)  (littleendian N3))) ++
                    QuadByte2ValList (littleendian_invert (Int.sub (Znth 9 x)  (littleendian N4)))
                    end end end
  end.

Definition OutLen h := if Int.eq (Int.repr h) Int.zero then 64 else 32.

Definition fcorePOST_SEP h data d l out :=
  CoreInSEP data d *
  data_at Tsh (tarray tuchar (OutLen h)) l out.

Definition f_core_POST d out h (data: SixteenByte * SixteenByte * (SixteenByte * SixteenByte) ) :=
EX l:_,
   PROP (fcore_result h data l)
   LOCAL ()
   SEP (fcorePOST_SEP h data d l out).

Definition core_spec :=
  DECLARE _core
   WITH c : val, k:val, h:Z,
        nonce:val, out:val, OUT:list val,
        data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte)
   PRE [ _out OF tptr tuchar,
         _in OF tptr tuchar,
         _k OF tptr tuchar,
         _c OF tptr tuchar,
         _h OF tint ]
      PROP ()
      LOCAL (temp _in nonce; temp _out out;
             temp _c c; temp _k k; temp _h (Vint (Int.repr h)))
      SEP (CoreInSEP data (nonce, c, k);
           data_at Tsh (tarray tuchar (OutLen h)) OUT out)
  POST [ tvoid ] (f_core_POST (nonce, c, k) out h data).

Definition ld32_spec :=
  DECLARE _ld32
   WITH x : val, B:QuadByte
   PRE [ _x OF tptr tuchar ]
      PROP ()
      LOCAL (temp _x x)
      SEP (data_at Tsh (tarray tuchar 4) (QuadByte2ValList B) x)
  POST [ tuint ] 
     PROP ()
     LOCAL (temp ret_temp (Vint (littleendian B)))
     SEP (QByte B x).

Definition st32_spec :=
  DECLARE _st32
   WITH x : val, u:int
   PRE [ _x OF tptr tuchar, _u OF tuint ]
      PROP ()
      LOCAL (temp _x x; temp _u (Vint u))
      SEP (data_at_ Tsh (tarray tuchar 4) x)
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (QByte (littleendian_invert u) x).

Definition L32_spec :=
  DECLARE _L32
   WITH x : int, c: int
   PRE [ _x OF tuint, _c OF tint ]
      PROP (0 < Int.signed c < 32) (*yes, c=Int.zero needs to be ruled out - it leads to undefined behaviour in the shift-right operation*)
      LOCAL (temp _x (Vint x); temp _c (Vint c))
      SEP ()
  POST [ tuint ]
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.rol x c)))
     SEP ().

Definition bigendian64 (b c:QuadByte): int64 :=
  match b, c with (b0, b1, b2, b3), (c0, c1, c2, c3) =>
  Int64.repr
   (       Byte.unsigned c3 +
    2^8  * Byte.unsigned c2 +
    2^16 * Byte.unsigned c1 +
    2^24 * Byte.unsigned c0 +
    2^32 * Byte.unsigned b3 +
    2^40 * Byte.unsigned b2 +
    2^48 * Byte.unsigned b1 +
    2^56 * Byte.unsigned b0
    )
  end.

Definition dl64_spec :=
  DECLARE _dl64
   WITH x : val, B:QuadByte, C: QuadByte
   PRE [ _x OF tptr tuchar ]
      PROP ()
      LOCAL (temp _x x)
      SEP (data_at Tsh (tarray tuchar 8) (QuadByte2ValList B++QuadByte2ValList C) x)
  POST [ tulong ] 
     PROP ()
     LOCAL (temp ret_temp (Vlong (bigendian64 B C)))
     SEP (data_at Tsh (tarray tuchar 8) (QuadByte2ValList B++QuadByte2ValList C) x).

Definition bigendian64_invert (w:int64) : QuadByte * QuadByte:=
    let w3 := Int64.unsigned w in
  let b3 := w3 / (2^56) in 
    let w2 := Z.modulo w3 (2^56) in
  let b2 := w2 / (2^48) in 
    let w1 := Z.modulo w2 (2^48) in
  let b1 := w1 / (2^40) in 
    let w0 := Z.modulo w1 (2^40) in
  let b0 := w0 / (2^32) in 
    let u3 := Z.modulo w0 (2^32) in
  let c3 := u3 / (2^24) in 
    let u2 := Z.modulo u3 (2^24) in
  let c2 := u2 / (2^16) in 
    let u1 := Z.modulo u2 (2^16) in
  let c1 := u1 / (2^8) in
    let c0 := Z.modulo u1 (2^8) in
  ((Byte.repr b3, Byte.repr b2, Byte.repr b1, Byte.repr b0), 
   (Byte.repr c3, Byte.repr c2, Byte.repr c1, Byte.repr c0)).

Lemma bigendian64_inv: forall b c: QuadByte, bigendian64_invert (bigendian64 b c) = (b,c).
Proof. destruct b as [[[b3 b2] b1] b0]. destruct c as [[[c3 c2] c1] c0].
  unfold bigendian64_invert, bigendian64.
  destruct (Byte.unsigned_range_2 b0). destruct (Byte.unsigned_range_2 b1).
  destruct (Byte.unsigned_range_2 b2). destruct (Byte.unsigned_range_2 b3).
  destruct (Byte.unsigned_range_2 c0). destruct (Byte.unsigned_range_2 c1).
  destruct (Byte.unsigned_range_2 c2). destruct (Byte.unsigned_range_2 c3).
  assert (2 ^ 8 * Byte.unsigned c1 <= 2 ^ 8 * Byte.max_unsigned).
               apply Zmult_le_compat_l; trivial.
  assert (2 ^ 16 * Byte.unsigned c2 <= 2 ^ 16 * Byte.max_unsigned).
               apply Zmult_le_compat_l; trivial.
  assert (2 ^ 24 * Byte.unsigned c3 <= 2 ^ 24 * Byte.max_unsigned).
               apply Zmult_le_compat_l; trivial.
  assert (2 ^ 32 * Byte.unsigned b0 <= 2 ^ 32 * Byte.max_unsigned).
               apply Zmult_le_compat_l; trivial.
  assert (2 ^ 40 * Byte.unsigned b1 <= 2 ^ 40 * Byte.max_unsigned).
               apply Zmult_le_compat_l; trivial.
  assert (2 ^ 48 * Byte.unsigned b2 <= 2 ^ 48 * Byte.max_unsigned).
               apply Zmult_le_compat_l; trivial.
  assert (2 ^ 56 * Byte.unsigned b3 <= 2 ^ 56 * Byte.max_unsigned).
               apply Zmult_le_compat_l; trivial.
  assert (0 <= 2 ^ 8 * Byte.unsigned c1). apply Z.mul_nonneg_cancel_l; trivial.
  assert (0 <= 2 ^ 16 * Byte.unsigned c2). apply Z.mul_nonneg_cancel_l; trivial.
  assert (0 <= 2 ^ 24 * Byte.unsigned c3). apply Z.mul_nonneg_cancel_l; trivial. 
  assert (0 <= 2 ^ 32 * Byte.unsigned b0). apply Z.mul_nonneg_cancel_l; trivial.
  assert (0 <= 2 ^ 40 * Byte.unsigned b1). apply Z.mul_nonneg_cancel_l; trivial.
  assert (0 <= 2 ^ 48 * Byte.unsigned b2). apply Z.mul_nonneg_cancel_l; trivial. 
  assert (0 <= 2 ^ 56 * Byte.unsigned b3). apply Z.mul_nonneg_cancel_l; trivial. 
  rewrite Int64.unsigned_repr.
  2:{ split. clear H0 H2 H4 H6 H8 H10 H12 H14.
             apply OMEGA2; trivial.
             apply OMEGA2; trivial.
             apply OMEGA2; trivial.
             apply OMEGA2; trivial.
             apply OMEGA2; trivial.
             apply OMEGA2; trivial.
             apply OMEGA2; trivial.
            eapply Z.le_trans. apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption.
              apply Z.add_le_mono; try eassumption.  
              apply Z.add_le_mono; eassumption.
            unfold Int64.max_unsigned; simpl. omega.
  }
  assert (0 <= Byte.unsigned c0 + 2 ^ 8 * Byte.unsigned c1 + 2 ^ 16 * Byte.unsigned c2 +
          2 ^ 24 * Byte.unsigned c3 + 2 ^ 32 * Byte.unsigned b0 + 2 ^ 40 * Byte.unsigned b1 +
          2 ^ 48 * Byte.unsigned b2 < 2 ^ 56). 
              split. apply OMEGA2; trivial. apply OMEGA2; trivial. apply OMEGA2; trivial. apply OMEGA2; trivial. apply OMEGA2; trivial. apply OMEGA2; trivial.
              assert (Byte.unsigned c0 + 2 ^ 8 * Byte.unsigned c1 + 2 ^ 16 * Byte.unsigned c2 
                      + 2 ^ 24 * Byte.unsigned c3 + 2 ^ 32 * Byte.unsigned b0 
                      + 2 ^ 40 * Byte.unsigned b1 + 2 ^ 48 * Byte.unsigned b2 <= 2 ^ 56 -1). 2: omega.
              eapply Z.le_trans. apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption. apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption. apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption. simpl. omega.
  erewrite (Zmod_unique _ (2^56) (Byte.unsigned b3)); try eassumption.
     2:{ rewrite (Z.mul_comm (2^56)). rewrite Z.add_comm. reflexivity. }
  assert (0 <= Byte.unsigned c0 + 2 ^ 8 * Byte.unsigned c1 + 2 ^ 16 * Byte.unsigned c2 +
          2 ^ 24 * Byte.unsigned c3 + 2 ^ 32 * Byte.unsigned b0 + 2 ^ 40 * Byte.unsigned b1 < 2 ^ 48). 
              split. apply OMEGA2; trivial. apply OMEGA2; trivial. apply OMEGA2; trivial. apply OMEGA2; trivial. apply OMEGA2; trivial. 
              assert (Byte.unsigned c0 + 2 ^ 8 * Byte.unsigned c1 + 2 ^ 16 * Byte.unsigned c2 
                      + 2 ^ 24 * Byte.unsigned c3 + 2 ^ 32 * Byte.unsigned b0 
                      + 2 ^ 40 * Byte.unsigned b1 <= 2 ^ 48 -1). 2: omega.
              eapply Z.le_trans. apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption. apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption. apply Z.add_le_mono; try eassumption. simpl. omega. 
  erewrite (Zmod_unique _ (2^48) (Byte.unsigned b2)); try eassumption.
     2:{ rewrite (Z.mul_comm (2^48)). rewrite Z.add_comm. reflexivity. }
  assert (0 <= Byte.unsigned c0 + 2 ^ 8 * Byte.unsigned c1 + 2 ^ 16 * Byte.unsigned c2 +
          2 ^ 24 * Byte.unsigned c3 + 2 ^ 32 * Byte.unsigned b0 < 2 ^ 40). 
              split. apply OMEGA2; trivial. apply OMEGA2; trivial.  apply OMEGA2; trivial.  apply OMEGA2; trivial.
              assert (Byte.unsigned c0 + 2 ^ 8 * Byte.unsigned c1 + 2 ^ 16 * Byte.unsigned c2 
                      + 2 ^ 24 * Byte.unsigned c3 + 2 ^ 32 * Byte.unsigned b0 <= 2 ^ 40 -1). 2: omega.
              eapply Z.le_trans. apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption. apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption. simpl. omega.
  erewrite (Zmod_unique _ (2^40) (Byte.unsigned b1)); try eassumption.
     2:{ rewrite (Z.mul_comm (2^40)). rewrite Z.add_comm. reflexivity. }
  assert (0 <= Byte.unsigned c0 + 2 ^ 8 * Byte.unsigned c1 + 2 ^ 16 * Byte.unsigned c2 +
          2 ^ 24 * Byte.unsigned c3 < 2 ^ 32). 
              split. apply OMEGA2; trivial. apply OMEGA2; trivial. apply OMEGA2; trivial.
              assert (Byte.unsigned c0 + 2 ^ 8 * Byte.unsigned c1 + 2 ^ 16 * Byte.unsigned c2 
                      + 2 ^ 24 * Byte.unsigned c3 <= 2 ^ 32 -1). 2: omega.
              eapply Z.le_trans. apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption. apply Z.add_le_mono; try eassumption. simpl. omega.
  erewrite (Zmod_unique _ (2^32) (Byte.unsigned b0)); try eassumption.
     2:{ rewrite (Z.mul_comm (2^32)). rewrite Z.add_comm. reflexivity. }
  assert (0 <= Byte.unsigned c0 + 2 ^ 8 * Byte.unsigned c1 + 2 ^ 16 * Byte.unsigned c2 < 2 ^ 24). 
              split. apply OMEGA2; trivial. apply OMEGA2; trivial.
              assert (Byte.unsigned c0 + 2 ^ 8 * Byte.unsigned c1 + 2 ^ 16 * Byte.unsigned c2 <= 2 ^ 24 -1). 2: omega.
              eapply Z.le_trans. apply Z.add_le_mono; try eassumption. 
              apply Z.add_le_mono; try eassumption. simpl. omega.
  erewrite (Zmod_unique _ (2^24) (Byte.unsigned c3)); try eassumption.
     2:{ rewrite (Z.mul_comm (2^24)). rewrite Z.add_comm. reflexivity. }
  assert (0 <= Byte.unsigned c0 + 2 ^ 8 * Byte.unsigned c1 < 2 ^ 16).
             split. apply OMEGA2; trivial.
              assert (Byte.unsigned c0 + 2 ^ 8 * Byte.unsigned c1 <= 2 ^ 16 -1). 2: omega.
              eapply Z.le_trans. apply Z.add_le_mono; try eassumption. 
              simpl. omega.
  erewrite (Zmod_unique _ (2^16) (Byte.unsigned c2)); try eassumption.
     2:{ rewrite (Z.mul_comm (2^16)). rewrite Z.add_comm. reflexivity. }
  erewrite (Zmod_unique _ (2^8) (Byte.unsigned c1)).
     2:{ rewrite (Z.mul_comm (2^8)). rewrite Z.add_comm. reflexivity. }
     2: apply Byte.unsigned_range. 
  erewrite (Zdiv_unique _ _ (Byte.unsigned b3));
       [  | rewrite (Z.mul_comm (2^56)), Z.add_comm; reflexivity
          | assumption ]. 
  rewrite Byte.repr_unsigned. 
  erewrite (Zdiv_unique _ _ (Byte.unsigned b2));
       [  | rewrite (Z.mul_comm (2^48)), Z.add_comm; reflexivity
          | assumption ]. 
  rewrite Byte.repr_unsigned. 
  erewrite (Zdiv_unique _ _ (Byte.unsigned b1));
       [  | rewrite (Z.mul_comm (2^40)), Z.add_comm; reflexivity
          | assumption ]. 
  rewrite Byte.repr_unsigned. 
  erewrite (Zdiv_unique _ _ (Byte.unsigned b0));
       [  | rewrite (Z.mul_comm (2^32)), Z.add_comm; reflexivity
          | assumption ]. 
  rewrite Byte.repr_unsigned. 
  erewrite (Zdiv_unique _ _ (Byte.unsigned c3));
       [  | rewrite (Z.mul_comm (2^24)), Z.add_comm; reflexivity
          | assumption ].
  rewrite Byte.repr_unsigned. 
  erewrite (Zdiv_unique _ _ (Byte.unsigned c2));
       [  | rewrite (Z.mul_comm (2^16)), Z.add_comm; reflexivity
          | assumption ]. 
  rewrite Byte.repr_unsigned. 
  erewrite (Zdiv_unique _ _ (Byte.unsigned c1));
       [  | rewrite (Z.mul_comm (2^8)), Z.add_comm; reflexivity
          | ]. 
  rewrite Byte.repr_unsigned. 
  rewrite Byte.repr_unsigned. trivial.
  apply Byte.unsigned_range. 
Qed.


Definition ts64_spec :=
  DECLARE _ts64
   WITH x : val, u:int64
   PRE [ _x OF tptr tuchar, _u OF tulong ]
      PROP ()
      LOCAL (temp _x x; temp _u (Vlong u))
      SEP (data_at_ Tsh (tarray tuchar 8) x)
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (let (B, C) := bigendian64_invert u in
          data_at Tsh (tarray tuchar 8) (QuadByte2ValList B++QuadByte2ValList C) x).


Definition crypto_core_salsa20_spec :=
  DECLARE _crypto_core_salsa20_tweet
   WITH c : val, k:val,
        nonce:val, out:val,
        data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte)
   PRE [ _out OF tptr tuchar,
         _in OF tptr tuchar,
         _k OF tptr tuchar,
         _c OF tptr tuchar ]
      PROP ()
      LOCAL (temp _in nonce; temp _out out;
             temp _c c; temp _k k)
      SEP ( CoreInSEP data (nonce, c, k);
            data_at_ Tsh (tarray tuchar 64) out)
  POST [ tint ]
       EX res:_,
       PROP (Snuffle20 (prepare_data data) = Some res)
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (CoreInSEP data (nonce, c, k);
            data_at Tsh (tarray tuchar 64) (QuadChunks2ValList (map littleendian_invert res)) out).

Definition hSalsaOut x :=
           QuadByte2ValList (littleendian_invert (Znth 0  x)) ++
           QuadByte2ValList (littleendian_invert (Znth 5  x)) ++
           QuadByte2ValList (littleendian_invert (Znth 10 x)) ++
           QuadByte2ValList (littleendian_invert (Znth 15 x)) ++
           QuadByte2ValList (littleendian_invert (Znth 6  x)) ++
           QuadByte2ValList (littleendian_invert (Znth 7  x)) ++
           QuadByte2ValList (littleendian_invert (Znth 8  x)) ++
           QuadByte2ValList (littleendian_invert (Znth 9  x)).

Definition crypto_core_hsalsa20_spec :=
  DECLARE _crypto_core_hsalsa20_tweet
   WITH c : val, k:val,
        nonce:val, out:val, OUT: list val,
        data : SixteenByte * SixteenByte * (SixteenByte * SixteenByte)
   PRE [ _out OF tptr tuchar,
         _in OF tptr tuchar,
         _k OF tptr tuchar,
         _c OF tptr tuchar ]
      PROP ()
      LOCAL (temp _in nonce; temp _out out;
             temp _c c; temp _k k)
      SEP (CoreInSEP data (nonce, c, k);
           data_at Tsh (tarray tuchar 32) OUT out)
  POST [ tint ]
       EX res:list int,
       PROP (Snuffle 20 (prepare_data data) = Some res)
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (CoreInSEP data (nonce, c, k); data_at Tsh (tarray tuchar 32) (hSalsaOut res) out).

Parameter SIGMA: SixteenByte.
Definition Sigma_vector : val -> mpred :=
  data_at Tsh (tarray tuchar 16) (SixteenByte2ValList SIGMA).

Fixpoint ZZ (zbytes: list byte) (n: nat): int * list byte :=
  match n with
   O => (Int.one, zbytes)
  | S k => match ZZ zbytes k with (u,zb) =>
             let v := (Int.unsigned u + (Byte.unsigned (Znth (Z.of_nat k+8) zb)))
             in (Int.shru (Int.repr v) (Int.repr 8),
                 upd_Znth (Z.of_nat k+8) zb (Byte.repr (Z.modulo v 256))) end

  end.

Fixpoint ZCont (r: nat) (zcont: list byte): list byte :=
  match r with
     O => zcont
   | S n => let zb := ZCont n zcont in
            let zz := ZZ zb (8:nat) in snd zz
  end.

Lemma ZCont0 bytes: ZCont O bytes = bytes. reflexivity. Qed.
Lemma ZContS bytes n: ZCont (S n) bytes = snd (ZZ (ZCont n bytes) 8). reflexivity. Qed.

Definition bytes_at x q i mbytes :=
match x with
  Vint _ => list_repeat (Z.to_nat i) (Byte.zero)
| _ => sublist q (q+i) mbytes
end.


Lemma Zlength_bytes_at x q i mbytes : 0<=q -> 0 <= i ->
  q + i <= Zlength mbytes -> Zlength (bytes_at x q i mbytes) = i.
Proof. intros. destruct x; simpl; try rewrite Zlength_sublist; try omega.
  rewrite Zlength_list_repeat; omega.
Qed.

Definition bxorlist := combinelist _ Byte.xor.
Definition Bl2VL (l: list byte) := map Vint (map Int.repr (map Byte.unsigned l)).

Definition message_at (mCont: list byte) (m:val): mpred :=
  match m with
    Vint i => !!(i=Int.zero) && emp
  | Vptr b z => data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m
  | _ => FF
  end.

Inductive CONTENT SIGMA K (mInit:val) (mCont zbytes:list byte): nat -> list byte -> list byte -> Prop :=
  CONT_zero: CONTENT SIGMA K mInit mCont  zbytes O zbytes nil
| CONT_succ: forall n zN resN ,
             CONTENT SIGMA K mInit mCont zbytes n zN resN ->
             forall d,
             SixteenByte2ValList d = Bl2VL (ZCont n zbytes) ->
             forall snuff srbytes Xor,
             Snuffle20 (prepare_data (d, SIGMA, K)) = Some snuff ->
             QuadChunks2ValList (map littleendian_invert snuff) =
                map Vint (map Int.repr (map Byte.unsigned srbytes)) ->
             bxorlist (bytes_at mInit (Z.of_nat n * 64) 64 mCont) srbytes = Some Xor ->
             CONTENT SIGMA K mInit mCont zbytes (S n) (snd (ZZ zN (8:nat))) (resN++Xor).

Lemma CONT_Zlength SIGMA K mInit mCont zbytes:
  forall n zB x,
   CONTENT SIGMA K mInit mCont zbytes n zB x ->
   Zlength x = (Z.of_nat n * 64)%Z.
Proof.
  induction n; intros; inv H. reflexivity.
  rewrite Zlength_app. erewrite IHn. 2: eassumption.
  unfold bxorlist in H5.
  apply combinelist_Zlength in H5. destruct H5. rewrite H, <- H0; clear H H0.
  apply Snuffle20_length in H3.
  specialize (QuadChunk2ValList_ZLength(map littleendian_invert snuff)).
  rewrite H4; clear H4. repeat rewrite Zlength_map. intros H; rewrite H; clear H.
  rewrite Zlength_correct, H3; clear H3. simpl.
  rewrite Pos2Z.inj_mul, Zpos_P_of_succ_nat, <- Zmult_succ_l_reverse. trivial.
  apply prepare_data_length.
Qed.

Lemma CONTCONT SIGMA K mInit mCont zbytes:
  forall n zB x,
   CONTENT SIGMA K mInit mCont zbytes n zB x ->
   ZCont n zbytes = zB.
Proof.
  induction n; intros; inv H.
  apply ZCont0.
  rewrite ZContS. erewrite IHn. 2: eassumption. trivial.
Qed.

Lemma ZZ_Zlength: forall n zbytes u U, ZZ zbytes n = (u,U) ->
      Zlength zbytes=16 -> Z.of_nat n <= 8 -> Zlength U = 16.
Proof. induction n; simpl; intros.
+ inv H. trivial.
+ remember (ZZ zbytes n). destruct p. symmetry in Heqp. inv H.
  rewrite Zpos_P_of_succ_nat in H1.
  apply IHn in Heqp; trivial; clear IHn.
  rewrite upd_Znth_Zlength; trivial.
  omega.
  omega.
Qed.

Lemma Zlength_ZCont: forall n zbytes, Zlength zbytes = 16 -> Zlength (ZCont n zbytes) = 16.
Proof.
  induction n; intros. rewrite ZCont0. trivial.
  rewrite ZContS. specialize (ZZ_Zlength 8 (ZCont n zbytes)); intros.
  remember (ZZ (ZCont n zbytes) 8). destruct p; simpl.
  apply (H0 _ _ (eq_refl _ )).
  apply IHn; trivial. simpl; omega.
Qed.

Lemma SixteenByte2ValList_exists bytes: Zlength bytes = 16 ->
  exists d, SixteenByte2ValList d = map Vint (map Int.repr (map Byte.unsigned bytes)).
Proof. intros.
  apply listD16 in H.
  destruct H as [v0 [v1 [v2 [v3 [v4 [v5 [v6 [v7 [v8
        [v9 [v10 [v11 [v12 [v13 [v14 [v15 V]]]]]]]]]]]]]]]].
  subst; simpl.
  exists ((v0, v1, v2, v3), (v4, v5, v6, v7), (v8, v9, v10, v11), (v12, v13, v14, v15)).
  rewrite SixteenByte2ValList_char. reflexivity.
Qed.

Definition ContSpec bInit SIGMA K mInit mCont zbytes  srbytes :=
    let n:= (Int64.unsigned bInit) / 64 in
    if zeq ((Int64.unsigned bInit) mod 64) 0
    then exists zbytesR, CONTENT SIGMA K mInit mCont zbytes (Z.to_nat n) zbytesR srbytes
    else exists zN resN d snuff bytes lastbytes(*zbytes*),
         CONTENT SIGMA K mInit mCont zbytes (Z.to_nat n) zN resN /\
             SixteenByte2ValList d = Bl2VL (ZCont (Z.to_nat n) zbytes) /\
             Snuffle20 (prepare_data (d, SIGMA, K)) = Some snuff /\
             QuadChunks2ValList (map littleendian_invert snuff) =
                map Vint (map Int.repr (map Byte.unsigned bytes)) /\
             bxorlist (bytes_at mInit (n * 64) ((Int64.unsigned bInit) mod 64) mCont)
                                (sublist 0 ((Int64.unsigned bInit) mod 64) bytes) = Some lastbytes /\
             (*zbytesR = (snd (ZZ zN (8:nat)))/\*) srbytes = (resN++lastbytes).

(*TODO: refine non-zero-case of this spec, relating COUT to mCont and K and Nonce*)
Definition crypto_stream_xor_postsep b (Nonce:SixteenByte) K mCont cLen nonce c m :=
  (if Int64.eq b Int64.zero
   then data_at_ Tsh (Tarray tuchar cLen noattr) c
   else (EX COUT:_, !!(exists zbytes, match Nonce with (Nnc0, Nnc1, _, _) =>
                SixteenByte2ValList
                  (Nnc0, Nnc1, (Byte.zero, Byte.zero, Byte.zero, Byte.zero),
                           (Byte.zero, Byte.zero, Byte.zero, Byte.zero)) =
                map Vint (map Int.repr (map Byte.unsigned zbytes))
                /\  ContSpec b SIGMA K m mCont zbytes COUT end)
           && data_at Tsh (Tarray tuchar cLen noattr) (Bl2VL COUT) c))
                    * SByte Nonce nonce
                    * message_at mCont m.

(*Precondition length mCont = Int64.unsigned b comes from textual spec in
  https://download.libsodium.org/doc/advanced/salsa20.html
  TODO: support the following part of the tetxual spec:
      m and c can point to the same address (in-place encryption/decryption).
     If they don't, the regions should not overlap.*)
Definition crypto_stream_salsa20_xor_spec :=
  DECLARE _crypto_stream_salsa20_tweet_xor
   WITH c : val, k:val, m:val, nonce:val, b:int64,
        Nonce : SixteenByte, K: SixteenByte * SixteenByte,
        mCont: list byte, gv: globals
   PRE [ _c OF tptr tuchar, _m OF tptr tuchar, _b OF tulong,
         _n OF tptr tuchar, _k OF tptr tuchar]
      PROP (Zlength mCont = Int64.unsigned b)
      LOCAL (temp _c c; temp _m m; temp _b (Vlong b);
             temp _n nonce; temp _k k; gvars gv)
      SEP ( SByte Nonce nonce;
            data_at_ Tsh (Tarray tuchar (Int64.unsigned b) noattr) c;
            ThirtyTwoByte K k;
            Sigma_vector (gv _sigma);
            message_at mCont m
            (*data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m*))
  POST [ tint ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (Sigma_vector (gv _sigma); ThirtyTwoByte K k;
            crypto_stream_xor_postsep b Nonce K mCont (Int64.unsigned b) nonce c m).

Definition f_crypto_stream_xsalsa20_tweet_xor_spec := 
  DECLARE _crypto_stream_salsa20_tweet_xor
   WITH c : val, k:val, nonce:val, m:val, d:int64, mCont: list byte,
        Nonce : SixteenByte, Nonce2 : SixteenByte, K: SixteenByte * SixteenByte,
        gv: globals
   PRE [ _c OF tptr tuchar, _m OF tptr tuchar,  _d OF tulong,
         _n OF tptr tuchar, _k OF tptr tuchar]
      PROP (Zlength mCont = Int64.unsigned d)
      LOCAL (temp _c c; temp _m m; temp _d (Vlong d);
             temp _n nonce; temp _k k; gvars gv)
      SEP ( SByte Nonce nonce; SByte Nonce2 (offset_val 16 nonce);
            data_at_ Tsh (Tarray tuchar (Int64.unsigned d) noattr) c;
            ThirtyTwoByte K k;
            message_at mCont m;
            Sigma_vector (gv _sigma)
            (*data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m*))
  POST [ tint ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (Sigma_vector (gv _sigma);
            EX HSalsaRes:_, crypto_stream_xor_postsep d Nonce2 HSalsaRes
              mCont (Int64.unsigned d)
              (offset_val 16 nonce) c m;
            data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList Nonce) nonce;
            ThirtyTwoByte K k).

Definition f_crypto_stream_xsalsa20_tweet_spec :=
  DECLARE _crypto_stream_xsalsa20_tweet
   WITH c : val, k:val, nonce:val, d:int64,
        Nonce : SixteenByte, Nonce2 : SixteenByte, K: SixteenByte * SixteenByte,
        gv: globals
   PRE [ _c OF tptr tuchar,  _d OF tulong,
         _n OF tptr tuchar, _k OF tptr tuchar]
      PROP ()
      LOCAL (temp _c c; (*temp _m m;*) temp _d (Vlong d);
             temp _n nonce; temp _k k; gvars gv)
      SEP ( SByte Nonce nonce; SByte Nonce2 (offset_val 16 nonce);
            data_at_ Tsh (Tarray tuchar (Int64.unsigned d) noattr) c;
            ThirtyTwoByte K k;
            Sigma_vector (gv _sigma)
            (*data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m*))
  POST [ tint ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (Sigma_vector (gv _sigma);
            EX HSalsaRes:_, crypto_stream_xor_postsep d Nonce2 HSalsaRes
              (list_repeat (Z.to_nat (Int64.unsigned d)) Byte.zero) (Int64.unsigned d)
              (offset_val 16 nonce) c nullval;
            data_at Tsh (Tarray tuchar 16 noattr) (SixteenByte2ValList Nonce) nonce;
            ThirtyTwoByte K k).
(*            crypto_stream_xor_postsep d Nonce K (list_repeat (Z.to_nat (Int64.unsigned d)) Byte.zero) (Int64.unsigned d) nonce c k nullval). *)

(*TODO: support the following part of the tetxual spec:
      m and c can point to the same address (in-place encryption/decryption). 
     If they don't, the regions should not overlap.*)
Definition f_crypto_stream_salsa20_tweet_spec := 
  DECLARE _crypto_stream_salsa20_tweet
   WITH c : val, k:val, nonce:val, d:int64,
        Nonce : SixteenByte, K: SixteenByte * SixteenByte,
        (*mCont: list byte, *) gv: globals
   PRE [ _c OF tptr tuchar, (*_m OF tptr tuchar,*) _d OF tulong,
         _n OF tptr tuchar, _k OF tptr tuchar]
      PROP ((*Zlength mCont = Int64.unsigned b*))
      LOCAL (temp _c c; (*temp _m m;*) temp _d (Vlong d);
             temp _n nonce; temp _k k; gvars gv)
      SEP ( SByte Nonce nonce;
            data_at_ Tsh (Tarray tuchar (Int64.unsigned d) noattr) c;
            ThirtyTwoByte K k;
            Sigma_vector (gv _sigma)
            (*data_at Tsh (tarray tuchar (Zlength mCont)) (Bl2VL mCont) m*))
  POST [ tint ] 
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr 0)))
       SEP (Sigma_vector (gv _sigma);
            ThirtyTwoByte K k;
            crypto_stream_xor_postsep d Nonce K (list_repeat (Z.to_nat (Int64.unsigned d)) Byte.zero) (Int64.unsigned d) nonce c nullval). 

Definition vn_spec :=
  DECLARE _vn
  WITH x:val, y:val, n:Z, xsh: share, ysh: share, xcont:list byte, ycont:list byte
  PRE [_x OF tptr tuchar, _y OF tptr tuchar, _n OF tint]
    PROP (readable_share xsh; readable_share ysh; 0<=n<= Int.max_unsigned)
    LOCAL (temp _x x; temp _y y; temp _n (Vint (Int.repr n)))
    SEP (data_at xsh (Tarray tuchar n noattr) (map Vint (map Int.repr (map Byte.unsigned xcont))) x;
         data_at ysh (Tarray tuchar n noattr) (map Vint (map Int.repr (map Byte.unsigned ycont))) y)
  POST [tint]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (if list_eq_dec Byte.eq_dec xcont ycont then 0 else -1))))
    SEP (data_at xsh (Tarray tuchar n noattr) (map Vint (map Int.repr (map Byte.unsigned xcont))) x;
         data_at ysh (Tarray tuchar n noattr) (map Vint (map Int.repr (map Byte.unsigned ycont))) y). 
    
Definition verify16_spec :=
  DECLARE _crypto_verify_16_tweet
  WITH x:val, y:val, n:Z, xsh: share, ysh: share, xcont:list byte, ycont:list byte
  PRE [_x OF tptr tuchar, _y OF tptr tuchar]
    PROP (readable_share xsh; readable_share ysh)
    LOCAL (temp _x x; temp _y y)
    SEP (data_at xsh (Tarray tuchar 16 noattr) (map Vint (map Int.repr (map Byte.unsigned xcont))) x;
         data_at ysh (Tarray tuchar 16 noattr) (map Vint (map Int.repr (map Byte.unsigned ycont))) y)
  POST [tint]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (if list_eq_dec Byte.eq_dec xcont ycont then 0 else -1))))
    SEP (data_at xsh (Tarray tuchar 16 noattr) (map Vint (map Int.repr (map Byte.unsigned xcont))) x;
         data_at ysh (Tarray tuchar 16 noattr) (map Vint (map Int.repr (map Byte.unsigned ycont))) y).
       
Definition verify32_spec :=
  DECLARE _crypto_verify_32_tweet
  WITH x:val, y:val, n:Z, xsh: share, ysh: share, xcont:list byte, ycont:list byte
  PRE [_x OF tptr tuchar, _y OF tptr tuchar]
    PROP (readable_share xsh; readable_share ysh)
    LOCAL (temp _x x; temp _y y)
    SEP (data_at xsh (Tarray tuchar 32 noattr) (map Vint (map Int.repr (map Byte.unsigned xcont))) x;
         data_at ysh (Tarray tuchar 32 noattr) (map Vint (map Int.repr (map Byte.unsigned ycont))) y)
  POST [tint]
    PROP ()
    LOCAL (temp ret_temp (Vint (Int.repr (if list_eq_dec Byte.eq_dec xcont ycont then 0 else -1))))
    SEP (data_at xsh (Tarray tuchar 32 noattr) (map Vint (map Int.repr (map Byte.unsigned xcont))) x;
         data_at ysh (Tarray tuchar 32 noattr) (map Vint (map Int.repr (map Byte.unsigned ycont))) y).       

Definition SalsaVarSpecs : varspecs := (_sigma, tarray tuchar 16)::nil.

Definition SalsaFunSpecs : funspecs := 
  ltac:(with_library prog (core_spec :: ld32_spec :: L32_spec::st32_spec::dl64_spec::ts64_spec::
                           crypto_core_salsa20_spec::crypto_core_hsalsa20_spec::
                           crypto_stream_salsa20_xor_spec::f_crypto_stream_salsa20_tweet_spec::
                           verify32_spec::verify16_spec::vn_spec::nil)).
