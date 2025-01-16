From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "32sse2".
  Definition abi := "standard".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "tweetnacl20140427/tweetnaclVerifiableC.c".
  Definition normalized := true.
End Info.

Definition _A : ident := 102%positive.
Definition _Ch : ident := 119%positive.
Definition _D : ident := 44%positive.
Definition _D2 : ident := 45%positive.
Definition _I : ident := 48%positive.
Definition _K : ident := 125%positive.
Definition _L : ident := 140%positive.
Definition _L32 : ident := 51%positive.
Definition _M : ident := 104%positive.
Definition _Maj : ident := 120%positive.
Definition _R : ident := 118%positive.
Definition _S : ident := 105%positive.
Definition _Sigma0 : ident := 121%positive.
Definition _Sigma1 : ident := 122%positive.
Definition _X : ident := 46%positive.
Definition _Y : ident := 47%positive.
Definition _Z : ident := 103%positive.
Definition __0 : ident := 39%positive.
Definition __121665 : ident := 43%positive.
Definition __9 : ident := 40%positive.
Definition ___builtin_ais_annot : ident := 1%positive.
Definition ___builtin_annot : ident := 18%positive.
Definition ___builtin_annot_intval : ident := 19%positive.
Definition ___builtin_bswap : ident := 3%positive.
Definition ___builtin_bswap16 : ident := 5%positive.
Definition ___builtin_bswap32 : ident := 4%positive.
Definition ___builtin_bswap64 : ident := 2%positive.
Definition ___builtin_clz : ident := 6%positive.
Definition ___builtin_clzl : ident := 7%positive.
Definition ___builtin_clzll : ident := 8%positive.
Definition ___builtin_ctz : ident := 9%positive.
Definition ___builtin_ctzl : ident := 10%positive.
Definition ___builtin_ctzll : ident := 11%positive.
Definition ___builtin_debug : ident := 37%positive.
Definition ___builtin_expect : ident := 26%positive.
Definition ___builtin_fabs : ident := 12%positive.
Definition ___builtin_fabsf : ident := 13%positive.
Definition ___builtin_fmadd : ident := 29%positive.
Definition ___builtin_fmax : ident := 27%positive.
Definition ___builtin_fmin : ident := 28%positive.
Definition ___builtin_fmsub : ident := 30%positive.
Definition ___builtin_fnmadd : ident := 31%positive.
Definition ___builtin_fnmsub : ident := 32%positive.
Definition ___builtin_fsqrt : ident := 14%positive.
Definition ___builtin_membar : ident := 20%positive.
Definition ___builtin_memcpy_aligned : ident := 16%positive.
Definition ___builtin_read16_reversed : ident := 33%positive.
Definition ___builtin_read32_reversed : ident := 34%positive.
Definition ___builtin_sel : ident := 17%positive.
Definition ___builtin_sqrt : ident := 15%positive.
Definition ___builtin_unreachable : ident := 25%positive.
Definition ___builtin_va_arg : ident := 22%positive.
Definition ___builtin_va_copy : ident := 23%positive.
Definition ___builtin_va_end : ident := 24%positive.
Definition ___builtin_va_start : ident := 21%positive.
Definition ___builtin_write16_reversed : ident := 35%positive.
Definition ___builtin_write32_reversed : ident := 36%positive.
Definition ___compcert_i64_dtos : ident := 160%positive.
Definition ___compcert_i64_dtou : ident := 161%positive.
Definition ___compcert_i64_sar : ident := 172%positive.
Definition ___compcert_i64_sdiv : ident := 166%positive.
Definition ___compcert_i64_shl : ident := 170%positive.
Definition ___compcert_i64_shr : ident := 171%positive.
Definition ___compcert_i64_smod : ident := 168%positive.
Definition ___compcert_i64_smulh : ident := 173%positive.
Definition ___compcert_i64_stod : ident := 162%positive.
Definition ___compcert_i64_stof : ident := 164%positive.
Definition ___compcert_i64_udiv : ident := 167%positive.
Definition ___compcert_i64_umod : ident := 169%positive.
Definition ___compcert_i64_umulh : ident := 174%positive.
Definition ___compcert_i64_utod : ident := 163%positive.
Definition ___compcert_i64_utof : ident := 165%positive.
Definition ___compcert_va_composite : ident := 159%positive.
Definition ___compcert_va_float64 : ident := 158%positive.
Definition ___compcert_va_int32 : ident := 156%positive.
Definition ___compcert_va_int64 : ident := 157%positive.
Definition _a : ident := 91%positive.
Definition _add : ident := 129%positive.
Definition _add1305 : ident := 83%positive.
Definition _b : ident := 76%positive.
Definition _c : ident := 50%positive.
Definition _car25519 : ident := 94%positive.
Definition _carry : ident := 141%positive.
Definition _chk : ident := 147%positive.
Definition _core : ident := 72%positive.
Definition _crypto_box_curve25519xsalsa20poly1305_tweet : ident := 116%positive.
Definition _crypto_box_curve25519xsalsa20poly1305_tweet_afternm : ident := 114%positive.
Definition _crypto_box_curve25519xsalsa20poly1305_tweet_beforenm : ident := 113%positive.
Definition _crypto_box_curve25519xsalsa20poly1305_tweet_keypair : ident := 112%positive.
Definition _crypto_box_curve25519xsalsa20poly1305_tweet_open : ident := 117%positive.
Definition _crypto_box_curve25519xsalsa20poly1305_tweet_open_afternm : ident := 115%positive.
Definition _crypto_core_hsalsa20_tweet : ident := 74%positive.
Definition _crypto_core_salsa20_tweet : ident := 73%positive.
Definition _crypto_hash_sha512_tweet : ident := 128%positive.
Definition _crypto_hashblocks_sha512_tweet : ident := 126%positive.
Definition _crypto_onetimeauth_poly1305_tweet : ident := 87%positive.
Definition _crypto_onetimeauth_poly1305_tweet_verify : ident := 88%positive.
Definition _crypto_scalarmult_curve25519_tweet : ident := 110%positive.
Definition _crypto_scalarmult_curve25519_tweet_base : ident := 111%positive.
Definition _crypto_secretbox_xsalsa20poly1305_tweet : ident := 89%positive.
Definition _crypto_secretbox_xsalsa20poly1305_tweet_open : ident := 90%positive.
Definition _crypto_sign_ed25519_tweet : ident := 146%positive.
Definition _crypto_sign_ed25519_tweet_keypair : ident := 139%positive.
Definition _crypto_sign_ed25519_tweet_open : ident := 155%positive.
Definition _crypto_stream_salsa20_tweet : ident := 79%positive.
Definition _crypto_stream_salsa20_tweet_xor : ident := 78%positive.
Definition _crypto_stream_xsalsa20_tweet : ident := 81%positive.
Definition _crypto_stream_xsalsa20_tweet_xor : ident := 82%positive.
Definition _crypto_verify_16_tweet : ident := 62%positive.
Definition _crypto_verify_32_tweet : ident := 63%positive.
Definition _cswap : ident := 130%positive.
Definition _d : ident := 60%positive.
Definition _den : ident := 149%positive.
Definition _den2 : ident := 150%positive.
Definition _den4 : ident := 151%positive.
Definition _den6 : ident := 152%positive.
Definition _dl64 : ident := 55%positive.
Definition _e : ident := 108%positive.
Definition _f : ident := 109%positive.
Definition _g : ident := 86%positive.
Definition _gf0 : ident := 41%positive.
Definition _gf1 : ident := 42%positive.
Definition _h : ident := 67%positive.
Definition _i : ident := 54%positive.
Definition _in : ident := 65%positive.
Definition _inv25519 : ident := 106%positive.
Definition _iv : ident := 127%positive.
Definition _j : ident := 70%positive.
Definition _k : ident := 66%positive.
Definition _ld32 : ident := 53%positive.
Definition _m : ident := 71%positive.
Definition _main : ident := 175%positive.
Definition _minusp : ident := 84%positive.
Definition _mlen : ident := 154%positive.
Definition _modL : ident := 142%positive.
Definition _n : ident := 59%positive.
Definition _neq25519 : ident := 99%positive.
Definition _num : ident := 148%positive.
Definition _o : ident := 93%positive.
Definition _out : ident := 64%positive.
Definition _p : ident := 95%positive.
Definition _pack : ident := 134%positive.
Definition _pack25519 : ident := 98%positive.
Definition _par25519 : ident := 100%positive.
Definition _pk : ident := 137%positive.
Definition _pow2523 : ident := 107%positive.
Definition _q : ident := 96%positive.
Definition _r : ident := 85%positive.
Definition _randombytes : ident := 38%positive.
Definition _reduce : ident := 143%positive.
Definition _s : ident := 80%positive.
Definition _scalarbase : ident := 136%positive.
Definition _scalarmult : ident := 135%positive.
Definition _sel25519 : ident := 97%positive.
Definition _set25519 : ident := 92%positive.
Definition _sigma : ident := 75%positive.
Definition _sigma0 : ident := 123%positive.
Definition _sigma1 : ident := 124%positive.
Definition _sk : ident := 138%positive.
Definition _sm : ident := 144%positive.
Definition _smlen : ident := 145%positive.
Definition _st32 : ident := 56%positive.
Definition _t : ident := 69%positive.
Definition _ts64 : ident := 57%positive.
Definition _tx : ident := 131%positive.
Definition _ty : ident := 132%positive.
Definition _u : ident := 52%positive.
Definition _unpack25519 : ident := 101%positive.
Definition _unpackneg : ident := 153%positive.
Definition _vn : ident := 61%positive.
Definition _w : ident := 68%positive.
Definition _x : ident := 49%positive.
Definition _y : ident := 58%positive.
Definition _z : ident := 77%positive.
Definition _zi : ident := 133%positive.
Definition _t'1 : ident := 176%positive.
Definition _t'10 : ident := 185%positive.
Definition _t'11 : ident := 186%positive.
Definition _t'12 : ident := 187%positive.
Definition _t'13 : ident := 188%positive.
Definition _t'14 : ident := 189%positive.
Definition _t'15 : ident := 190%positive.
Definition _t'16 : ident := 191%positive.
Definition _t'17 : ident := 192%positive.
Definition _t'18 : ident := 193%positive.
Definition _t'19 : ident := 194%positive.
Definition _t'2 : ident := 177%positive.
Definition _t'20 : ident := 195%positive.
Definition _t'21 : ident := 196%positive.
Definition _t'22 : ident := 197%positive.
Definition _t'23 : ident := 198%positive.
Definition _t'24 : ident := 199%positive.
Definition _t'25 : ident := 200%positive.
Definition _t'26 : ident := 201%positive.
Definition _t'27 : ident := 202%positive.
Definition _t'28 : ident := 203%positive.
Definition _t'29 : ident := 204%positive.
Definition _t'3 : ident := 178%positive.
Definition _t'30 : ident := 205%positive.
Definition _t'31 : ident := 206%positive.
Definition _t'32 : ident := 207%positive.
Definition _t'33 : ident := 208%positive.
Definition _t'34 : ident := 209%positive.
Definition _t'4 : ident := 179%positive.
Definition _t'5 : ident := 180%positive.
Definition _t'6 : ident := 181%positive.
Definition _t'7 : ident := 182%positive.
Definition _t'8 : ident := 183%positive.
Definition _t'9 : ident := 184%positive.

Definition v__0 := {|
  gvar_info := (tarray tuchar 16);
  gvar_init := (Init_space 16 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v__9 := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := (Init_int8 (Int.repr 9) :: Init_space 31 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_gf0 := {|
  gvar_info := (tarray tlong 16);
  gvar_init := (Init_space 128 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_gf1 := {|
  gvar_info := (tarray tlong 16);
  gvar_init := (Init_int64 (Int64.repr 1) :: Init_space 120 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v__121665 := {|
  gvar_info := (tarray tlong 16);
  gvar_init := (Init_int64 (Int64.repr 56129) :: Init_int64 (Int64.repr 1) ::
                Init_space 112 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_D := {|
  gvar_info := (tarray tlong 16);
  gvar_init := (Init_int64 (Int64.repr 30883) ::
                Init_int64 (Int64.repr 4953) ::
                Init_int64 (Int64.repr 19914) ::
                Init_int64 (Int64.repr 30187) ::
                Init_int64 (Int64.repr 55467) ::
                Init_int64 (Int64.repr 16705) ::
                Init_int64 (Int64.repr 2637) ::
                Init_int64 (Int64.repr 112) ::
                Init_int64 (Int64.repr 59544) ::
                Init_int64 (Int64.repr 30585) ::
                Init_int64 (Int64.repr 16505) ::
                Init_int64 (Int64.repr 36039) ::
                Init_int64 (Int64.repr 65139) ::
                Init_int64 (Int64.repr 11119) ::
                Init_int64 (Int64.repr 27886) ::
                Init_int64 (Int64.repr 20995) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_D2 := {|
  gvar_info := (tarray tlong 16);
  gvar_init := (Init_int64 (Int64.repr 61785) ::
                Init_int64 (Int64.repr 9906) ::
                Init_int64 (Int64.repr 39828) ::
                Init_int64 (Int64.repr 60374) ::
                Init_int64 (Int64.repr 45398) ::
                Init_int64 (Int64.repr 33411) ::
                Init_int64 (Int64.repr 5274) ::
                Init_int64 (Int64.repr 224) ::
                Init_int64 (Int64.repr 53552) ::
                Init_int64 (Int64.repr 61171) ::
                Init_int64 (Int64.repr 33010) ::
                Init_int64 (Int64.repr 6542) ::
                Init_int64 (Int64.repr 64743) ::
                Init_int64 (Int64.repr 22239) ::
                Init_int64 (Int64.repr 55772) ::
                Init_int64 (Int64.repr 9222) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_X := {|
  gvar_info := (tarray tlong 16);
  gvar_init := (Init_int64 (Int64.repr 54554) ::
                Init_int64 (Int64.repr 36645) ::
                Init_int64 (Int64.repr 11616) ::
                Init_int64 (Int64.repr 51542) ::
                Init_int64 (Int64.repr 42930) ::
                Init_int64 (Int64.repr 38181) ::
                Init_int64 (Int64.repr 51040) ::
                Init_int64 (Int64.repr 26924) ::
                Init_int64 (Int64.repr 56412) ::
                Init_int64 (Int64.repr 64982) ::
                Init_int64 (Int64.repr 57905) ::
                Init_int64 (Int64.repr 49316) ::
                Init_int64 (Int64.repr 21502) ::
                Init_int64 (Int64.repr 52590) ::
                Init_int64 (Int64.repr 14035) ::
                Init_int64 (Int64.repr 8553) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_Y := {|
  gvar_info := (tarray tlong 16);
  gvar_init := (Init_int64 (Int64.repr 26200) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) ::
                Init_int64 (Int64.repr 26214) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_I := {|
  gvar_info := (tarray tlong 16);
  gvar_init := (Init_int64 (Int64.repr 41136) ::
                Init_int64 (Int64.repr 18958) ::
                Init_int64 (Int64.repr 6951) ::
                Init_int64 (Int64.repr 50414) ::
                Init_int64 (Int64.repr 58488) ::
                Init_int64 (Int64.repr 44335) ::
                Init_int64 (Int64.repr 6150) ::
                Init_int64 (Int64.repr 12099) ::
                Init_int64 (Int64.repr 55207) ::
                Init_int64 (Int64.repr 15867) ::
                Init_int64 (Int64.repr 153) ::
                Init_int64 (Int64.repr 11085) ::
                Init_int64 (Int64.repr 57099) ::
                Init_int64 (Int64.repr 20417) ::
                Init_int64 (Int64.repr 9344) ::
                Init_int64 (Int64.repr 11139) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_L32 := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_x, tuint) :: (_c, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oor
                 (Ebinop Oshl (Etempvar _x tuint) (Etempvar _c tint) tuint)
                 (Ebinop Oshr
                   (Ebinop Oand (Etempvar _x tuint)
                     (Econst_int (Int.repr (-1)) tuint) tuint)
                   (Ebinop Osub (Econst_int (Int.repr 32) tint)
                     (Etempvar _c tint) tint) tuint) tuint)))
|}.

Definition f_ld32 := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_u, tuint) :: (_t'3, tuchar) :: (_t'2, tuchar) ::
               (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _u
    (Ederef
      (Ebinop Oadd (Etempvar _x (tptr tuchar)) (Econst_int (Int.repr 3) tint)
        (tptr tuchar)) tuchar))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Ederef
          (Ebinop Oadd (Etempvar _x (tptr tuchar))
            (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar))
      (Sset _u
        (Ebinop Oor
          (Ebinop Oshl (Etempvar _u tuint) (Econst_int (Int.repr 8) tint)
            tuint) (Etempvar _t'3 tuchar) tuint)))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Ederef
            (Ebinop Oadd (Etempvar _x (tptr tuchar))
              (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar))
        (Sset _u
          (Ebinop Oor
            (Ebinop Oshl (Etempvar _u tuint) (Econst_int (Int.repr 8) tint)
              tuint) (Etempvar _t'2 tuchar) tuint)))
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _x (tptr tuchar))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
        (Sreturn (Some (Ebinop Oor
                         (Ebinop Oshl (Etempvar _u tuint)
                           (Econst_int (Int.repr 8) tint) tuint)
                         (Etempvar _t'1 tuchar) tuint)))))))
|}.

Definition f_dl64 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_u, tulong) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _u (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 8) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _x (tptr tuchar)) (Etempvar _i tint)
                  (tptr tuchar)) tuchar))
            (Sset _u
              (Ebinop Oor
                (Ebinop Oshl (Etempvar _u tulong)
                  (Econst_int (Int.repr 8) tint) tulong)
                (Etempvar _t'1 tuchar) tulong))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Sreturn (Some (Etempvar _u tulong)))))
|}.

Definition f_st32 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tuchar)) :: (_u, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 4) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _x (tptr tuchar)) (Etempvar _i tint)
              (tptr tuchar)) tuchar) (Etempvar _u tuint))
        (Sset _u
          (Ebinop Oshr (Etempvar _u tuint) (Econst_int (Int.repr 8) tint)
            tuint))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_ts64 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tuchar)) :: (_u, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 7) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                     (Econst_int (Int.repr 0) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _x (tptr tuchar)) (Etempvar _i tint)
              (tptr tuchar)) tuchar) (Etempvar _u tulong))
        (Sset _u
          (Ebinop Oshr (Etempvar _u tulong) (Econst_int (Int.repr 8) tint)
            tulong))))
    (Sset _i
      (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_vn := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tuchar)) :: (_y, (tptr tuchar)) :: (_n, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_d, tuint) :: (_t'2, tuchar) ::
               (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _d (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _n tint)
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _x (tptr tuchar)) (Etempvar _i tuint)
                  (tptr tuchar)) tuchar))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _y (tptr tuchar))
                    (Etempvar _i tuint) (tptr tuchar)) tuchar))
              (Sset _d
                (Ebinop Oor (Etempvar _d tuint)
                  (Ebinop Oxor (Etempvar _t'1 tuchar) (Etempvar _t'2 tuchar)
                    tint) tuint)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Sreturn (Some (Ebinop Osub
                     (Ebinop Oand (Econst_int (Int.repr 1) tint)
                       (Ebinop Oshr
                         (Ebinop Osub (Etempvar _d tuint)
                           (Econst_int (Int.repr 1) tint) tuint)
                         (Econst_int (Int.repr 8) tint) tuint) tuint)
                     (Econst_int (Int.repr 1) tint) tuint)))))
|}.

Definition f_crypto_verify_16_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tuchar)) :: (_y, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _vn (Tfunction ((tptr tuchar) :: (tptr tuchar) :: tint :: nil) tint
                cc_default))
    ((Etempvar _x (tptr tuchar)) :: (Etempvar _y (tptr tuchar)) ::
     (Econst_int (Int.repr 16) tint) :: nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_crypto_verify_32_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tuchar)) :: (_y, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _vn (Tfunction ((tptr tuchar) :: (tptr tuchar) :: tint :: nil) tint
                cc_default))
    ((Etempvar _x (tptr tuchar)) :: (Etempvar _y (tptr tuchar)) ::
     (Econst_int (Int.repr 32) tint) :: nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_core := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_in, (tptr tuchar)) ::
                (_k, (tptr tuchar)) :: (_c, (tptr tuchar)) :: (_h, tint) ::
                nil);
  fn_vars := ((_w, (tarray tuint 16)) :: (_x, (tarray tuint 16)) ::
              (_y, (tarray tuint 16)) :: (_t, (tarray tuint 4)) :: nil);
  fn_temps := ((_i, tint) :: (_j, tint) :: (_m, tint) :: (_t'10, tuint) ::
               (_t'9, tuint) :: (_t'8, tuint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) ::
               (_t'34, tuint) :: (_t'33, tuint) :: (_t'32, tuint) ::
               (_t'31, tuint) :: (_t'30, tuint) :: (_t'29, tuint) ::
               (_t'28, tuint) :: (_t'27, tuint) :: (_t'26, tuint) ::
               (_t'25, tuint) :: (_t'24, tuint) :: (_t'23, tuint) ::
               (_t'22, tuint) :: (_t'21, tuint) :: (_t'20, tuint) ::
               (_t'19, tuint) :: (_t'18, tuint) :: (_t'17, tuint) ::
               (_t'16, tuint) :: (_t'15, tuint) :: (_t'14, tuint) ::
               (_t'13, tuint) :: (_t'12, tuint) :: (_t'11, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 4) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _ld32 (Tfunction ((tptr tuchar) :: nil) tuint cc_default))
              ((Ebinop Oadd (Etempvar _c (tptr tuchar))
                 (Ebinop Omul (Econst_int (Int.repr 4) tint)
                   (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _x (tarray tuint 16))
                  (Ebinop Omul (Econst_int (Int.repr 5) tint)
                    (Etempvar _i tint) tint) (tptr tuint)) tuint)
              (Etempvar _t'1 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _ld32 (Tfunction ((tptr tuchar) :: nil) tuint
                              cc_default))
                ((Ebinop Oadd (Etempvar _k (tptr tuchar))
                   (Ebinop Omul (Econst_int (Int.repr 4) tint)
                     (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _x (tarray tuint 16))
                    (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                      (Etempvar _i tint) tint) (tptr tuint)) tuint)
                (Etempvar _t'2 tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _ld32 (Tfunction ((tptr tuchar) :: nil) tuint
                                cc_default))
                  ((Ebinop Oadd (Etempvar _in (tptr tuchar))
                     (Ebinop Omul (Econst_int (Int.repr 4) tint)
                       (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                      (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                        (Etempvar _i tint) tint) (tptr tuint)) tuint)
                  (Etempvar _t'3 tuint)))
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _ld32 (Tfunction ((tptr tuchar) :: nil) tuint
                                cc_default))
                  ((Ebinop Oadd
                     (Ebinop Oadd (Etempvar _k (tptr tuchar))
                       (Econst_int (Int.repr 16) tint) (tptr tuchar))
                     (Ebinop Omul (Econst_int (Int.repr 4) tint)
                       (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                      (Ebinop Oadd (Econst_int (Int.repr 11) tint)
                        (Etempvar _i tint) tint) (tptr tuint)) tuint)
                  (Etempvar _t'4 tuint)))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 16) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'34
              (Ederef
                (Ebinop Oadd (Evar _x (tarray tuint 16)) (Etempvar _i tint)
                  (tptr tuint)) tuint))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _y (tarray tuint 16)) (Etempvar _i tint)
                  (tptr tuint)) tuint) (Etempvar _t'34 tuint))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 20) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _j (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                   (Econst_int (Int.repr 4) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Sset _m (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _m tint)
                                           (Econst_int (Int.repr 4) tint)
                                           tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _t'33
                                (Ederef
                                  (Ebinop Oadd (Evar _x (tarray tuint 16))
                                    (Ebinop Omod
                                      (Ebinop Oadd
                                        (Ebinop Omul
                                          (Econst_int (Int.repr 5) tint)
                                          (Etempvar _j tint) tint)
                                        (Ebinop Omul
                                          (Econst_int (Int.repr 4) tint)
                                          (Etempvar _m tint) tint) tint)
                                      (Econst_int (Int.repr 16) tint) tint)
                                    (tptr tuint)) tuint))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Evar _t (tarray tuint 4))
                                    (Etempvar _m tint) (tptr tuint)) tuint)
                                (Etempvar _t'33 tuint))))
                          (Sset _m
                            (Ebinop Oadd (Etempvar _m tint)
                              (Econst_int (Int.repr 1) tint) tint))))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'31
                              (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                  (Econst_int (Int.repr 0) tint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sset _t'32
                                (Ederef
                                  (Ebinop Oadd (Evar _t (tarray tuint 4))
                                    (Econst_int (Int.repr 3) tint)
                                    (tptr tuint)) tuint))
                              (Scall (Some _t'5)
                                (Evar _L32 (Tfunction (tuint :: tint :: nil)
                                             tuint cc_default))
                                ((Ebinop Oadd (Etempvar _t'31 tuint)
                                   (Etempvar _t'32 tuint) tuint) ::
                                 (Econst_int (Int.repr 7) tint) :: nil))))
                          (Ssequence
                            (Sset _t'30
                              (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuint)) tuint))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _t (tarray tuint 4))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuint)) tuint)
                              (Ebinop Oxor (Etempvar _t'30 tuint)
                                (Etempvar _t'5 tuint) tuint))))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'28
                                (Ederef
                                  (Ebinop Oadd (Evar _t (tarray tuint 4))
                                    (Econst_int (Int.repr 1) tint)
                                    (tptr tuint)) tuint))
                              (Ssequence
                                (Sset _t'29
                                  (Ederef
                                    (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 0) tint)
                                      (tptr tuint)) tuint))
                                (Scall (Some _t'6)
                                  (Evar _L32 (Tfunction
                                               (tuint :: tint :: nil) tuint
                                               cc_default))
                                  ((Ebinop Oadd (Etempvar _t'28 tuint)
                                     (Etempvar _t'29 tuint) tuint) ::
                                   (Econst_int (Int.repr 9) tint) :: nil))))
                            (Ssequence
                              (Sset _t'27
                                (Ederef
                                  (Ebinop Oadd (Evar _t (tarray tuint 4))
                                    (Econst_int (Int.repr 2) tint)
                                    (tptr tuint)) tuint))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Evar _t (tarray tuint 4))
                                    (Econst_int (Int.repr 2) tint)
                                    (tptr tuint)) tuint)
                                (Ebinop Oxor (Etempvar _t'27 tuint)
                                  (Etempvar _t'6 tuint) tuint))))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'25
                                  (Ederef
                                    (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 2) tint)
                                      (tptr tuint)) tuint))
                                (Ssequence
                                  (Sset _t'26
                                    (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tuint)) tuint))
                                  (Scall (Some _t'7)
                                    (Evar _L32 (Tfunction
                                                 (tuint :: tint :: nil) tuint
                                                 cc_default))
                                    ((Ebinop Oadd (Etempvar _t'25 tuint)
                                       (Etempvar _t'26 tuint) tuint) ::
                                     (Econst_int (Int.repr 13) tint) :: nil))))
                              (Ssequence
                                (Sset _t'24
                                  (Ederef
                                    (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr tuint)) tuint))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Evar _t (tarray tuint 4))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr tuint)) tuint)
                                  (Ebinop Oxor (Etempvar _t'24 tuint)
                                    (Etempvar _t'7 tuint) tuint))))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'22
                                    (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                        (Econst_int (Int.repr 3) tint)
                                        (tptr tuint)) tuint))
                                  (Ssequence
                                    (Sset _t'23
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _t (tarray tuint 4))
                                          (Econst_int (Int.repr 2) tint)
                                          (tptr tuint)) tuint))
                                    (Scall (Some _t'8)
                                      (Evar _L32 (Tfunction
                                                   (tuint :: tint :: nil)
                                                   tuint cc_default))
                                      ((Ebinop Oadd (Etempvar _t'22 tuint)
                                         (Etempvar _t'23 tuint) tuint) ::
                                       (Econst_int (Int.repr 18) tint) ::
                                       nil))))
                                (Ssequence
                                  (Sset _t'21
                                    (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                        (Econst_int (Int.repr 0) tint)
                                        (tptr tuint)) tuint))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd (Evar _t (tarray tuint 4))
                                        (Econst_int (Int.repr 0) tint)
                                        (tptr tuint)) tuint)
                                    (Ebinop Oxor (Etempvar _t'21 tuint)
                                      (Etempvar _t'8 tuint) tuint))))
                              (Ssequence
                                (Sset _m (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _m tint)
                                                   (Econst_int (Int.repr 4) tint)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sset _t'20
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _t (tarray tuint 4))
                                            (Etempvar _m tint) (tptr tuint))
                                          tuint))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _w (tarray tuint 16))
                                            (Ebinop Oadd
                                              (Ebinop Omul
                                                (Econst_int (Int.repr 4) tint)
                                                (Etempvar _j tint) tint)
                                              (Ebinop Omod
                                                (Ebinop Oadd
                                                  (Etempvar _j tint)
                                                  (Etempvar _m tint) tint)
                                                (Econst_int (Int.repr 4) tint)
                                                tint) tint) (tptr tuint))
                                          tuint) (Etempvar _t'20 tuint))))
                                  (Sset _m
                                    (Ebinop Oadd (Etempvar _m tint)
                                      (Econst_int (Int.repr 1) tint) tint))))))))))
                  (Sset _j
                    (Ebinop Oadd (Etempvar _j tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Sset _m (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _m tint)
                                   (Econst_int (Int.repr 16) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _t'19
                        (Ederef
                          (Ebinop Oadd (Evar _w (tarray tuint 16))
                            (Etempvar _m tint) (tptr tuint)) tuint))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _x (tarray tuint 16))
                            (Etempvar _m tint) (tptr tuint)) tuint)
                        (Etempvar _t'19 tuint))))
                  (Sset _m
                    (Ebinop Oadd (Etempvar _m tint)
                      (Econst_int (Int.repr 1) tint) tint))))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Sifthenelse (Etempvar _h tint)
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 16) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'17
                    (Ederef
                      (Ebinop Oadd (Evar _x (tarray tuint 16))
                        (Etempvar _i tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _t'18
                      (Ederef
                        (Ebinop Oadd (Evar _y (tarray tuint 16))
                          (Etempvar _i tint) (tptr tuint)) tuint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _x (tarray tuint 16))
                          (Etempvar _i tint) (tptr tuint)) tuint)
                      (Ebinop Oadd (Etempvar _t'17 tuint)
                        (Etempvar _t'18 tuint) tuint)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 4) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'9)
                        (Evar _ld32 (Tfunction ((tptr tuchar) :: nil) tuint
                                      cc_default))
                        ((Ebinop Oadd (Etempvar _c (tptr tuchar))
                           (Ebinop Omul (Econst_int (Int.repr 4) tint)
                             (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
                      (Ssequence
                        (Sset _t'16
                          (Ederef
                            (Ebinop Oadd (Evar _x (tarray tuint 16))
                              (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                (Etempvar _i tint) tint) (tptr tuint)) tuint))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _x (tarray tuint 16))
                              (Ebinop Omul (Econst_int (Int.repr 5) tint)
                                (Etempvar _i tint) tint) (tptr tuint)) tuint)
                          (Ebinop Osub (Etempvar _t'16 tuint)
                            (Etempvar _t'9 tuint) tuint))))
                    (Ssequence
                      (Scall (Some _t'10)
                        (Evar _ld32 (Tfunction ((tptr tuchar) :: nil) tuint
                                      cc_default))
                        ((Ebinop Oadd (Etempvar _in (tptr tuchar))
                           (Ebinop Omul (Econst_int (Int.repr 4) tint)
                             (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
                      (Ssequence
                        (Sset _t'15
                          (Ederef
                            (Ebinop Oadd (Evar _x (tarray tuint 16))
                              (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                                (Etempvar _i tint) tint) (tptr tuint)) tuint))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _x (tarray tuint 16))
                              (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                                (Etempvar _i tint) tint) (tptr tuint)) tuint)
                          (Ebinop Osub (Etempvar _t'15 tuint)
                            (Etempvar _t'10 tuint) tuint))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 4) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'14
                        (Ederef
                          (Ebinop Oadd (Evar _x (tarray tuint 16))
                            (Ebinop Omul (Econst_int (Int.repr 5) tint)
                              (Etempvar _i tint) tint) (tptr tuint)) tuint))
                      (Scall None
                        (Evar _st32 (Tfunction
                                      ((tptr tuchar) :: tuint :: nil) tvoid
                                      cc_default))
                        ((Ebinop Oadd (Etempvar _out (tptr tuchar))
                           (Ebinop Omul (Econst_int (Int.repr 4) tint)
                             (Etempvar _i tint) tint) (tptr tuchar)) ::
                         (Etempvar _t'14 tuint) :: nil)))
                    (Ssequence
                      (Sset _t'13
                        (Ederef
                          (Ebinop Oadd (Evar _x (tarray tuint 16))
                            (Ebinop Oadd (Econst_int (Int.repr 6) tint)
                              (Etempvar _i tint) tint) (tptr tuint)) tuint))
                      (Scall None
                        (Evar _st32 (Tfunction
                                      ((tptr tuchar) :: tuint :: nil) tvoid
                                      cc_default))
                        ((Ebinop Oadd
                           (Ebinop Oadd (Etempvar _out (tptr tuchar))
                             (Econst_int (Int.repr 16) tint) (tptr tuchar))
                           (Ebinop Omul (Econst_int (Int.repr 4) tint)
                             (Etempvar _i tint) tint) (tptr tuchar)) ::
                         (Etempvar _t'13 tuint) :: nil)))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))))
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 16) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'11
                  (Ederef
                    (Ebinop Oadd (Evar _x (tarray tuint 16))
                      (Etempvar _i tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _t'12
                    (Ederef
                      (Ebinop Oadd (Evar _y (tarray tuint 16))
                        (Etempvar _i tint) (tptr tuint)) tuint))
                  (Scall None
                    (Evar _st32 (Tfunction ((tptr tuchar) :: tuint :: nil)
                                  tvoid cc_default))
                    ((Ebinop Oadd (Etempvar _out (tptr tuchar))
                       (Ebinop Omul (Econst_int (Int.repr 4) tint)
                         (Etempvar _i tint) tint) (tptr tuchar)) ::
                     (Ebinop Oadd (Etempvar _t'11 tuint)
                       (Etempvar _t'12 tuint) tuint) :: nil)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))))))
|}.

Definition f_crypto_core_salsa20_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_in, (tptr tuchar)) ::
                (_k, (tptr tuchar)) :: (_c, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _core (Tfunction
                  ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                   (tptr tuchar) :: tint :: nil) tvoid cc_default))
    ((Etempvar _out (tptr tuchar)) :: (Etempvar _in (tptr tuchar)) ::
     (Etempvar _k (tptr tuchar)) :: (Etempvar _c (tptr tuchar)) ::
     (Econst_int (Int.repr 0) tint) :: nil))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_crypto_core_hsalsa20_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_in, (tptr tuchar)) ::
                (_k, (tptr tuchar)) :: (_c, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _core (Tfunction
                  ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                   (tptr tuchar) :: tint :: nil) tvoid cc_default))
    ((Etempvar _out (tptr tuchar)) :: (Etempvar _in (tptr tuchar)) ::
     (Etempvar _k (tptr tuchar)) :: (Etempvar _c (tptr tuchar)) ::
     (Econst_int (Int.repr 1) tint) :: nil))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition v_sigma := {|
  gvar_info := (tarray tuchar 16);
  gvar_init := (Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 120) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 107) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_crypto_stream_salsa20_tweet_xor := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr tuchar)) :: (_m, (tptr tuchar)) :: (_b, tulong) ::
                (_n, (tptr tuchar)) :: (_k, (tptr tuchar)) :: nil);
  fn_vars := ((_z, (tarray tuchar 16)) :: (_x, (tarray tuchar 64)) :: nil);
  fn_temps := ((_u, tuint) :: (_i, tuint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'8, tuchar) :: (_t'7, tuchar) :: (_t'6, tuchar) ::
               (_t'5, tuchar) :: (_t'4, tuchar) :: (_t'3, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Eunop Onotbool (Etempvar _b tulong) tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                         (Econst_int (Int.repr 16) tint) tint)
            Sskip
            Sbreak)
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _z (tarray tuchar 16)) (Etempvar _i tuint)
                (tptr tuchar)) tuchar) (Econst_int (Int.repr 0) tint)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                           (Econst_int (Int.repr 8) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'8
                (Ederef
                  (Ebinop Oadd (Etempvar _n (tptr tuchar))
                    (Etempvar _i tuint) (tptr tuchar)) tuchar))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _z (tarray tuchar 16))
                    (Etempvar _i tuint) (tptr tuchar)) tuchar)
                (Etempvar _t'8 tuchar))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Ssequence
        (Swhile
          (Ebinop Oge (Etempvar _b tulong) (Econst_int (Int.repr 64) tint)
            tint)
          (Ssequence
            (Scall None
              (Evar _crypto_core_salsa20_tweet (Tfunction
                                                 ((tptr tuchar) ::
                                                  (tptr tuchar) ::
                                                  (tptr tuchar) ::
                                                  (tptr tuchar) :: nil) tint
                                                 cc_default))
              ((Evar _x (tarray tuchar 64)) ::
               (Evar _z (tarray tuchar 16)) :: (Etempvar _k (tptr tuchar)) ::
               (Evar _sigma (tarray tuchar 16)) :: nil))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                   (Econst_int (Int.repr 64) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sifthenelse (Etempvar _m (tptr tuchar))
                        (Ssequence
                          (Sset _t'7
                            (Ederef
                              (Ebinop Oadd (Etempvar _m (tptr tuchar))
                                (Etempvar _i tuint) (tptr tuchar)) tuchar))
                          (Sset _t'1 (Ecast (Etempvar _t'7 tuchar) tint)))
                        (Sset _t'1
                          (Ecast (Econst_int (Int.repr 0) tint) tint)))
                      (Ssequence
                        (Sset _t'6
                          (Ederef
                            (Ebinop Oadd (Evar _x (tarray tuchar 64))
                              (Etempvar _i tuint) (tptr tuchar)) tuchar))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _c (tptr tuchar))
                              (Etempvar _i tuint) (tptr tuchar)) tuchar)
                          (Ebinop Oxor (Etempvar _t'1 tint)
                            (Etempvar _t'6 tuchar) tint)))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tuint)
                      (Econst_int (Int.repr 1) tint) tuint))))
              (Ssequence
                (Sset _u (Econst_int (Int.repr 1) tint))
                (Ssequence
                  (Ssequence
                    (Sset _i (Econst_int (Int.repr 8) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                       (Econst_int (Int.repr 16) tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Ssequence
                            (Sset _t'5
                              (Ederef
                                (Ebinop Oadd (Evar _z (tarray tuchar 16))
                                  (Etempvar _i tuint) (tptr tuchar)) tuchar))
                            (Sset _u
                              (Ebinop Oadd (Etempvar _u tuint)
                                (Ecast (Etempvar _t'5 tuchar) tuint) tuint)))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _z (tarray tuchar 16))
                                  (Etempvar _i tuint) (tptr tuchar)) tuchar)
                              (Etempvar _u tuint))
                            (Sset _u
                              (Ebinop Oshr (Etempvar _u tuint)
                                (Econst_int (Int.repr 8) tint) tuint)))))
                      (Sset _i
                        (Ebinop Oadd (Etempvar _i tuint)
                          (Econst_int (Int.repr 1) tint) tuint))))
                  (Ssequence
                    (Sset _b
                      (Ebinop Osub (Etempvar _b tulong)
                        (Econst_int (Int.repr 64) tint) tulong))
                    (Ssequence
                      (Sset _c
                        (Ebinop Oadd (Etempvar _c (tptr tuchar))
                          (Econst_int (Int.repr 64) tint) (tptr tuchar)))
                      (Sifthenelse (Etempvar _m (tptr tuchar))
                        (Sset _m
                          (Ebinop Oadd (Etempvar _m (tptr tuchar))
                            (Econst_int (Int.repr 64) tint) (tptr tuchar)))
                        Sskip))))))))
        (Ssequence
          (Sifthenelse (Etempvar _b tulong)
            (Ssequence
              (Scall None
                (Evar _crypto_core_salsa20_tweet (Tfunction
                                                   ((tptr tuchar) ::
                                                    (tptr tuchar) ::
                                                    (tptr tuchar) ::
                                                    (tptr tuchar) :: nil)
                                                   tint cc_default))
                ((Evar _x (tarray tuchar 64)) ::
                 (Evar _z (tarray tuchar 16)) ::
                 (Etempvar _k (tptr tuchar)) ::
                 (Evar _sigma (tarray tuchar 16)) :: nil))
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                   (Etempvar _b tulong) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sifthenelse (Etempvar _m (tptr tuchar))
                        (Ssequence
                          (Sset _t'4
                            (Ederef
                              (Ebinop Oadd (Etempvar _m (tptr tuchar))
                                (Etempvar _i tuint) (tptr tuchar)) tuchar))
                          (Sset _t'2 (Ecast (Etempvar _t'4 tuchar) tint)))
                        (Sset _t'2
                          (Ecast (Econst_int (Int.repr 0) tint) tint)))
                      (Ssequence
                        (Sset _t'3
                          (Ederef
                            (Ebinop Oadd (Evar _x (tarray tuchar 64))
                              (Etempvar _i tuint) (tptr tuchar)) tuchar))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _c (tptr tuchar))
                              (Etempvar _i tuint) (tptr tuchar)) tuchar)
                          (Ebinop Oxor (Etempvar _t'2 tint)
                            (Etempvar _t'3 tuchar) tint)))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tuint)
                      (Econst_int (Int.repr 1) tint) tuint)))))
            Sskip)
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_crypto_stream_salsa20_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr tuchar)) :: (_d, tulong) :: (_n, (tptr tuchar)) ::
                (_k, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _crypto_stream_salsa20_tweet_xor (Tfunction
                                             ((tptr tuchar) ::
                                              (tptr tuchar) :: tulong ::
                                              (tptr tuchar) ::
                                              (tptr tuchar) :: nil) tint
                                             cc_default))
    ((Etempvar _c (tptr tuchar)) :: (Econst_int (Int.repr 0) tint) ::
     (Etempvar _d tulong) :: (Etempvar _n (tptr tuchar)) ::
     (Etempvar _k (tptr tuchar)) :: nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_crypto_stream_xsalsa20_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr tuchar)) :: (_d, tulong) :: (_n, (tptr tuchar)) ::
                (_k, (tptr tuchar)) :: nil);
  fn_vars := ((_s, (tarray tuchar 32)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _crypto_core_hsalsa20_tweet (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         (tptr tuchar) :: (tptr tuchar) ::
                                         nil) tint cc_default))
    ((Evar _s (tarray tuchar 32)) :: (Etempvar _n (tptr tuchar)) ::
     (Etempvar _k (tptr tuchar)) :: (Evar _sigma (tarray tuchar 16)) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _crypto_stream_salsa20_tweet (Tfunction
                                           ((tptr tuchar) :: tulong ::
                                            (tptr tuchar) :: (tptr tuchar) ::
                                            nil) tint cc_default))
      ((Etempvar _c (tptr tuchar)) :: (Etempvar _d tulong) ::
       (Ebinop Oadd (Etempvar _n (tptr tuchar))
         (Econst_int (Int.repr 16) tint) (tptr tuchar)) ::
       (Evar _s (tarray tuchar 32)) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_crypto_stream_xsalsa20_tweet_xor := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr tuchar)) :: (_m, (tptr tuchar)) :: (_d, tulong) ::
                (_n, (tptr tuchar)) :: (_k, (tptr tuchar)) :: nil);
  fn_vars := ((_s, (tarray tuchar 32)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _crypto_core_hsalsa20_tweet (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         (tptr tuchar) :: (tptr tuchar) ::
                                         nil) tint cc_default))
    ((Evar _s (tarray tuchar 32)) :: (Etempvar _n (tptr tuchar)) ::
     (Etempvar _k (tptr tuchar)) :: (Evar _sigma (tarray tuchar 16)) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _crypto_stream_salsa20_tweet_xor (Tfunction
                                               ((tptr tuchar) ::
                                                (tptr tuchar) :: tulong ::
                                                (tptr tuchar) ::
                                                (tptr tuchar) :: nil) tint
                                               cc_default))
      ((Etempvar _c (tptr tuchar)) :: (Etempvar _m (tptr tuchar)) ::
       (Etempvar _d tulong) ::
       (Ebinop Oadd (Etempvar _n (tptr tuchar))
         (Econst_int (Int.repr 16) tint) (tptr tuchar)) ::
       (Evar _s (tarray tuchar 32)) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_add1305 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr tuint)) :: (_c, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_j, tuint) :: (_u, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _u (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _j (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                       (Econst_int (Int.repr 17) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _h (tptr tuint)) (Etempvar _j tuint)
                  (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _c (tptr tuint)) (Etempvar _j tuint)
                    (tptr tuint)) tuint))
              (Sset _u
                (Ebinop Oadd (Etempvar _u tuint)
                  (Ebinop Oadd (Etempvar _t'1 tuint) (Etempvar _t'2 tuint)
                    tuint) tuint))))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _h (tptr tuint)) (Etempvar _j tuint)
                  (tptr tuint)) tuint)
              (Ebinop Oand (Etempvar _u tuint)
                (Econst_int (Int.repr 255) tint) tuint))
            (Sset _u
              (Ebinop Oshr (Etempvar _u tuint) (Econst_int (Int.repr 8) tint)
                tuint)))))
      (Sset _j
        (Ebinop Oadd (Etempvar _j tuint) (Econst_int (Int.repr 1) tint)
          tuint)))))
|}.

Definition v_minusp := {|
  gvar_info := (tarray tuint 17);
  gvar_init := (Init_int32 (Int.repr 5) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) ::
                Init_int32 (Int.repr 252) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_crypto_onetimeauth_poly1305_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_m, (tptr tuchar)) ::
                (_n, tulong) :: (_k, (tptr tuchar)) :: nil);
  fn_vars := ((_x, (tarray tuint 17)) :: (_r, (tarray tuint 17)) ::
              (_h, (tarray tuint 17)) :: (_c, (tarray tuint 17)) ::
              (_g, (tarray tuint 17)) :: nil);
  fn_temps := ((_s, tuint) :: (_i, tuint) :: (_j, tuint) :: (_u, tuint) ::
               (_t'3, tuint) :: (_t'2, tint) :: (_t'1, tuint) ::
               (_t'28, tuchar) :: (_t'27, tuint) :: (_t'26, tuint) ::
               (_t'25, tuint) :: (_t'24, tuint) :: (_t'23, tuint) ::
               (_t'22, tuint) :: (_t'21, tuint) :: (_t'20, tuchar) ::
               (_t'19, tuint) :: (_t'18, tuint) :: (_t'17, tuint) ::
               (_t'16, tuint) :: (_t'15, tuint) :: (_t'14, tuint) ::
               (_t'13, tuint) :: (_t'12, tuint) :: (_t'11, tuint) ::
               (_t'10, tuint) :: (_t'9, tuint) :: (_t'8, tuint) ::
               (_t'7, tuint) :: (_t'6, tuint) :: (_t'5, tuchar) ::
               (_t'4, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _j (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                       (Econst_int (Int.repr 17) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tuint))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _h (tarray tuint 17)) (Etempvar _j tuint)
                  (tptr tuint)) tuint) (Etempvar _t'1 tuint)))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _r (tarray tuint 17)) (Etempvar _j tuint)
                (tptr tuint)) tuint) (Etempvar _t'1 tuint))))
      (Sset _j
        (Ebinop Oadd (Etempvar _j tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Ssequence
    (Ssequence
      (Sset _j (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                         (Econst_int (Int.repr 16) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'28
              (Ederef
                (Ebinop Oadd (Etempvar _k (tptr tuchar)) (Etempvar _j tuint)
                  (tptr tuchar)) tuchar))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _r (tarray tuint 17)) (Etempvar _j tuint)
                  (tptr tuint)) tuint) (Etempvar _t'28 tuchar))))
        (Sset _j
          (Ebinop Oadd (Etempvar _j tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Ssequence
      (Ssequence
        (Sset _t'27
          (Ederef
            (Ebinop Oadd (Evar _r (tarray tuint 17))
              (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _r (tarray tuint 17))
              (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint)
          (Ebinop Oand (Etempvar _t'27 tuint) (Econst_int (Int.repr 15) tint)
            tuint)))
      (Ssequence
        (Ssequence
          (Sset _t'26
            (Ederef
              (Ebinop Oadd (Evar _r (tarray tuint 17))
                (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _r (tarray tuint 17))
                (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint)
            (Ebinop Oand (Etempvar _t'26 tuint)
              (Econst_int (Int.repr 252) tint) tuint)))
        (Ssequence
          (Ssequence
            (Sset _t'25
              (Ederef
                (Ebinop Oadd (Evar _r (tarray tuint 17))
                  (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _r (tarray tuint 17))
                  (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint)
              (Ebinop Oand (Etempvar _t'25 tuint)
                (Econst_int (Int.repr 15) tint) tuint)))
          (Ssequence
            (Ssequence
              (Sset _t'24
                (Ederef
                  (Ebinop Oadd (Evar _r (tarray tuint 17))
                    (Econst_int (Int.repr 8) tint) (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _r (tarray tuint 17))
                    (Econst_int (Int.repr 8) tint) (tptr tuint)) tuint)
                (Ebinop Oand (Etempvar _t'24 tuint)
                  (Econst_int (Int.repr 252) tint) tuint)))
            (Ssequence
              (Ssequence
                (Sset _t'23
                  (Ederef
                    (Ebinop Oadd (Evar _r (tarray tuint 17))
                      (Econst_int (Int.repr 11) tint) (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _r (tarray tuint 17))
                      (Econst_int (Int.repr 11) tint) (tptr tuint)) tuint)
                  (Ebinop Oand (Etempvar _t'23 tuint)
                    (Econst_int (Int.repr 15) tint) tuint)))
              (Ssequence
                (Ssequence
                  (Sset _t'22
                    (Ederef
                      (Ebinop Oadd (Evar _r (tarray tuint 17))
                        (Econst_int (Int.repr 12) tint) (tptr tuint)) tuint))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _r (tarray tuint 17))
                        (Econst_int (Int.repr 12) tint) (tptr tuint)) tuint)
                    (Ebinop Oand (Etempvar _t'22 tuint)
                      (Econst_int (Int.repr 252) tint) tuint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'21
                      (Ederef
                        (Ebinop Oadd (Evar _r (tarray tuint 17))
                          (Econst_int (Int.repr 15) tint) (tptr tuint))
                        tuint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _r (tarray tuint 17))
                          (Econst_int (Int.repr 15) tint) (tptr tuint))
                        tuint)
                      (Ebinop Oand (Etempvar _t'21 tuint)
                        (Econst_int (Int.repr 15) tint) tuint)))
                  (Ssequence
                    (Swhile
                      (Ebinop Ogt (Etempvar _n tulong)
                        (Econst_int (Int.repr 0) tint) tint)
                      (Ssequence
                        (Ssequence
                          (Sset _j (Econst_int (Int.repr 0) tint))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                                             (Econst_int (Int.repr 17) tint)
                                             tint)
                                Sskip
                                Sbreak)
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Evar _c (tarray tuint 17))
                                    (Etempvar _j tuint) (tptr tuint)) tuint)
                                (Econst_int (Int.repr 0) tint)))
                            (Sset _j
                              (Ebinop Oadd (Etempvar _j tuint)
                                (Econst_int (Int.repr 1) tint) tuint))))
                        (Ssequence
                          (Ssequence
                            (Sset _j (Econst_int (Int.repr 0) tint))
                            (Sloop
                              (Ssequence
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _j tuint)
                                                 (Econst_int (Int.repr 16) tint)
                                                 tint)
                                    (Sset _t'2
                                      (Ecast
                                        (Ebinop Olt (Etempvar _j tuint)
                                          (Etempvar _n tulong) tint) tbool))
                                    (Sset _t'2
                                      (Econst_int (Int.repr 0) tint)))
                                  (Sifthenelse (Etempvar _t'2 tint)
                                    Sskip
                                    Sbreak))
                                (Ssequence
                                  (Sset _t'20
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _m (tptr tuchar))
                                        (Etempvar _j tuint) (tptr tuchar))
                                      tuchar))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _c (tarray tuint 17))
                                        (Etempvar _j tuint) (tptr tuint))
                                      tuint) (Etempvar _t'20 tuchar))))
                              (Sset _j
                                (Ebinop Oadd (Etempvar _j tuint)
                                  (Econst_int (Int.repr 1) tint) tuint))))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _c (tarray tuint 17))
                                  (Etempvar _j tuint) (tptr tuint)) tuint)
                              (Econst_int (Int.repr 1) tint))
                            (Ssequence
                              (Sset _m
                                (Ebinop Oadd (Etempvar _m (tptr tuchar))
                                  (Etempvar _j tuint) (tptr tuchar)))
                              (Ssequence
                                (Sset _n
                                  (Ebinop Osub (Etempvar _n tulong)
                                    (Etempvar _j tuint) tulong))
                                (Ssequence
                                  (Scall None
                                    (Evar _add1305 (Tfunction
                                                     ((tptr tuint) ::
                                                      (tptr tuint) :: nil)
                                                     tvoid cc_default))
                                    ((Evar _h (tarray tuint 17)) ::
                                     (Evar _c (tarray tuint 17)) :: nil))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _i
                                        (Econst_int (Int.repr 0) tint))
                                      (Sloop
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _i tuint)
                                                         (Econst_int (Int.repr 17) tint)
                                                         tint)
                                            Sskip
                                            Sbreak)
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _x (tarray tuint 17))
                                                  (Etempvar _i tuint)
                                                  (tptr tuint)) tuint)
                                              (Econst_int (Int.repr 0) tint))
                                            (Ssequence
                                              (Sset _j
                                                (Econst_int (Int.repr 0) tint))
                                              (Sloop
                                                (Ssequence
                                                  (Sifthenelse (Ebinop Olt
                                                                 (Etempvar _j tuint)
                                                                 (Econst_int (Int.repr 17) tint)
                                                                 tint)
                                                    Sskip
                                                    Sbreak)
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Ole
                                                                   (Etempvar _j tuint)
                                                                   (Etempvar _i tuint)
                                                                   tint)
                                                      (Ssequence
                                                        (Sset _t'19
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _r (tarray tuint 17))
                                                              (Ebinop Osub
                                                                (Etempvar _i tuint)
                                                                (Etempvar _j tuint)
                                                                tuint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sset _t'3
                                                          (Ecast
                                                            (Etempvar _t'19 tuint)
                                                            tuint)))
                                                      (Ssequence
                                                        (Sset _t'18
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _r (tarray tuint 17))
                                                              (Ebinop Osub
                                                                (Ebinop Oadd
                                                                  (Etempvar _i tuint)
                                                                  (Econst_int (Int.repr 17) tint)
                                                                  tuint)
                                                                (Etempvar _j tuint)
                                                                tuint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sset _t'3
                                                          (Ecast
                                                            (Ebinop Omul
                                                              (Econst_int (Int.repr 320) tint)
                                                              (Etempvar _t'18 tuint)
                                                              tuint) tuint))))
                                                    (Ssequence
                                                      (Sset _t'16
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _x (tarray tuint 17))
                                                            (Etempvar _i tuint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _t'17
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _h (tarray tuint 17))
                                                              (Etempvar _j tuint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _x (tarray tuint 17))
                                                              (Etempvar _i tuint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Oadd
                                                            (Etempvar _t'16 tuint)
                                                            (Ebinop Omul
                                                              (Etempvar _t'17 tuint)
                                                              (Etempvar _t'3 tuint)
                                                              tuint) tuint))))))
                                                (Sset _j
                                                  (Ebinop Oadd
                                                    (Etempvar _j tuint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tuint))))))
                                        (Sset _i
                                          (Ebinop Oadd (Etempvar _i tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _i
                                          (Econst_int (Int.repr 0) tint))
                                        (Sloop
                                          (Ssequence
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _i tuint)
                                                           (Econst_int (Int.repr 17) tint)
                                                           tint)
                                              Sskip
                                              Sbreak)
                                            (Ssequence
                                              (Sset _t'15
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _x (tarray tuint 17))
                                                    (Etempvar _i tuint)
                                                    (tptr tuint)) tuint))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _h (tarray tuint 17))
                                                    (Etempvar _i tuint)
                                                    (tptr tuint)) tuint)
                                                (Etempvar _t'15 tuint))))
                                          (Sset _i
                                            (Ebinop Oadd (Etempvar _i tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint))))
                                      (Ssequence
                                        (Sset _u
                                          (Econst_int (Int.repr 0) tint))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _j
                                              (Econst_int (Int.repr 0) tint))
                                            (Sloop
                                              (Ssequence
                                                (Sifthenelse (Ebinop Olt
                                                               (Etempvar _j tuint)
                                                               (Econst_int (Int.repr 16) tint)
                                                               tint)
                                                  Sskip
                                                  Sbreak)
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'14
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _h (tarray tuint 17))
                                                          (Etempvar _j tuint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Sset _u
                                                      (Ebinop Oadd
                                                        (Etempvar _u tuint)
                                                        (Etempvar _t'14 tuint)
                                                        tuint)))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _h (tarray tuint 17))
                                                          (Etempvar _j tuint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Ebinop Oand
                                                        (Etempvar _u tuint)
                                                        (Econst_int (Int.repr 255) tint)
                                                        tuint))
                                                    (Sset _u
                                                      (Ebinop Oshr
                                                        (Etempvar _u tuint)
                                                        (Econst_int (Int.repr 8) tint)
                                                        tuint)))))
                                              (Sset _j
                                                (Ebinop Oadd
                                                  (Etempvar _j tuint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tuint))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'13
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _h (tarray tuint 17))
                                                    (Econst_int (Int.repr 16) tint)
                                                    (tptr tuint)) tuint))
                                              (Sset _u
                                                (Ebinop Oadd
                                                  (Etempvar _u tuint)
                                                  (Etempvar _t'13 tuint)
                                                  tuint)))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _h (tarray tuint 17))
                                                    (Econst_int (Int.repr 16) tint)
                                                    (tptr tuint)) tuint)
                                                (Ebinop Oand
                                                  (Etempvar _u tuint)
                                                  (Econst_int (Int.repr 3) tint)
                                                  tuint))
                                              (Ssequence
                                                (Sset _u
                                                  (Ebinop Omul
                                                    (Econst_int (Int.repr 5) tint)
                                                    (Ebinop Oshr
                                                      (Etempvar _u tuint)
                                                      (Econst_int (Int.repr 2) tint)
                                                      tuint) tuint))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _j
                                                      (Econst_int (Int.repr 0) tint))
                                                    (Sloop
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Olt
                                                            (Etempvar _j tuint)
                                                            (Econst_int (Int.repr 16) tint)
                                                            tint)
                                                          Sskip
                                                          Sbreak)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Sset _t'12
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _h (tarray tuint 17))
                                                                  (Etempvar _j tuint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sset _u
                                                              (Ebinop Oadd
                                                                (Etempvar _u tuint)
                                                                (Etempvar _t'12 tuint)
                                                                tuint)))
                                                          (Ssequence
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _h (tarray tuint 17))
                                                                  (Etempvar _j tuint)
                                                                  (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oand
                                                                (Etempvar _u tuint)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tuint))
                                                            (Sset _u
                                                              (Ebinop Oshr
                                                                (Etempvar _u tuint)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tuint)))))
                                                      (Sset _j
                                                        (Ebinop Oadd
                                                          (Etempvar _j tuint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tuint))))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Sset _t'11
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _h (tarray tuint 17))
                                                            (Econst_int (Int.repr 16) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Sset _u
                                                        (Ebinop Oadd
                                                          (Etempvar _u tuint)
                                                          (Etempvar _t'11 tuint)
                                                          tuint)))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _h (tarray tuint 17))
                                                          (Econst_int (Int.repr 16) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Etempvar _u tuint))))))))))))))))))
                    (Ssequence
                      (Ssequence
                        (Sset _j (Econst_int (Int.repr 0) tint))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                                           (Econst_int (Int.repr 17) tint)
                                           tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Sset _t'10
                                (Ederef
                                  (Ebinop Oadd (Evar _h (tarray tuint 17))
                                    (Etempvar _j tuint) (tptr tuint)) tuint))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Evar _g (tarray tuint 17))
                                    (Etempvar _j tuint) (tptr tuint)) tuint)
                                (Etempvar _t'10 tuint))))
                          (Sset _j
                            (Ebinop Oadd (Etempvar _j tuint)
                              (Econst_int (Int.repr 1) tint) tuint))))
                      (Ssequence
                        (Scall None
                          (Evar _add1305 (Tfunction
                                           ((tptr tuint) :: (tptr tuint) ::
                                            nil) tvoid cc_default))
                          ((Evar _h (tarray tuint 17)) ::
                           (Evar _minusp (tarray tuint 17)) :: nil))
                        (Ssequence
                          (Ssequence
                            (Sset _t'9
                              (Ederef
                                (Ebinop Oadd (Evar _h (tarray tuint 17))
                                  (Econst_int (Int.repr 16) tint)
                                  (tptr tuint)) tuint))
                            (Sset _s
                              (Eunop Oneg
                                (Ebinop Oshr (Etempvar _t'9 tuint)
                                  (Econst_int (Int.repr 7) tint) tuint)
                                tuint)))
                          (Ssequence
                            (Ssequence
                              (Sset _j (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _j tuint)
                                                 (Econst_int (Int.repr 17) tint)
                                                 tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _t'6
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _h (tarray tuint 17))
                                          (Etempvar _j tuint) (tptr tuint))
                                        tuint))
                                    (Ssequence
                                      (Sset _t'7
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _g (tarray tuint 17))
                                            (Etempvar _j tuint) (tptr tuint))
                                          tuint))
                                      (Ssequence
                                        (Sset _t'8
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _h (tarray tuint 17))
                                              (Etempvar _j tuint)
                                              (tptr tuint)) tuint))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _h (tarray tuint 17))
                                              (Etempvar _j tuint)
                                              (tptr tuint)) tuint)
                                          (Ebinop Oxor (Etempvar _t'6 tuint)
                                            (Ebinop Oand (Etempvar _s tuint)
                                              (Ebinop Oxor
                                                (Etempvar _t'7 tuint)
                                                (Etempvar _t'8 tuint) tuint)
                                              tuint) tuint))))))
                                (Sset _j
                                  (Ebinop Oadd (Etempvar _j tuint)
                                    (Econst_int (Int.repr 1) tint) tuint))))
                            (Ssequence
                              (Ssequence
                                (Sset _j (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _j tuint)
                                                   (Econst_int (Int.repr 16) tint)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Sset _t'5
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _k (tptr tuchar))
                                            (Ebinop Oadd (Etempvar _j tuint)
                                              (Econst_int (Int.repr 16) tint)
                                              tuint) (tptr tuchar)) tuchar))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _c (tarray tuint 17))
                                            (Etempvar _j tuint) (tptr tuint))
                                          tuint) (Etempvar _t'5 tuchar))))
                                  (Sset _j
                                    (Ebinop Oadd (Etempvar _j tuint)
                                      (Econst_int (Int.repr 1) tint) tuint))))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Evar _c (tarray tuint 17))
                                      (Econst_int (Int.repr 16) tint)
                                      (tptr tuint)) tuint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Scall None
                                    (Evar _add1305 (Tfunction
                                                     ((tptr tuint) ::
                                                      (tptr tuint) :: nil)
                                                     tvoid cc_default))
                                    ((Evar _h (tarray tuint 17)) ::
                                     (Evar _c (tarray tuint 17)) :: nil))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _j
                                        (Econst_int (Int.repr 0) tint))
                                      (Sloop
                                        (Ssequence
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _j tuint)
                                                         (Econst_int (Int.repr 16) tint)
                                                         tint)
                                            Sskip
                                            Sbreak)
                                          (Ssequence
                                            (Sset _t'4
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _h (tarray tuint 17))
                                                  (Etempvar _j tuint)
                                                  (tptr tuint)) tuint))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _out (tptr tuchar))
                                                  (Etempvar _j tuint)
                                                  (tptr tuchar)) tuchar)
                                              (Etempvar _t'4 tuint))))
                                        (Sset _j
                                          (Ebinop Oadd (Etempvar _j tuint)
                                            (Econst_int (Int.repr 1) tint)
                                            tuint))))
                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))
|}.

Definition f_crypto_onetimeauth_poly1305_tweet_verify := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr tuchar)) :: (_m, (tptr tuchar)) :: (_n, tulong) ::
                (_k, (tptr tuchar)) :: nil);
  fn_vars := ((_x, (tarray tuchar 16)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _crypto_onetimeauth_poly1305_tweet (Tfunction
                                               ((tptr tuchar) ::
                                                (tptr tuchar) :: tulong ::
                                                (tptr tuchar) :: nil) tint
                                               cc_default))
    ((Evar _x (tarray tuchar 16)) :: (Etempvar _m (tptr tuchar)) ::
     (Etempvar _n tulong) :: (Etempvar _k (tptr tuchar)) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _crypto_verify_16_tweet (Tfunction
                                      ((tptr tuchar) :: (tptr tuchar) :: nil)
                                      tint cc_default))
      ((Etempvar _h (tptr tuchar)) :: (Evar _x (tarray tuchar 16)) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_crypto_secretbox_xsalsa20poly1305_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr tuchar)) :: (_m, (tptr tuchar)) :: (_d, tulong) ::
                (_n, (tptr tuchar)) :: (_k, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _d tulong)
                 (Econst_int (Int.repr 32) tint) tint)
    (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
    Sskip)
  (Ssequence
    (Scall None
      (Evar _crypto_stream_xsalsa20_tweet_xor (Tfunction
                                                ((tptr tuchar) ::
                                                 (tptr tuchar) :: tulong ::
                                                 (tptr tuchar) ::
                                                 (tptr tuchar) :: nil) tint
                                                cc_default))
      ((Etempvar _c (tptr tuchar)) :: (Etempvar _m (tptr tuchar)) ::
       (Etempvar _d tulong) :: (Etempvar _n (tptr tuchar)) ::
       (Etempvar _k (tptr tuchar)) :: nil))
    (Ssequence
      (Scall None
        (Evar _crypto_onetimeauth_poly1305_tweet (Tfunction
                                                   ((tptr tuchar) ::
                                                    (tptr tuchar) ::
                                                    tulong ::
                                                    (tptr tuchar) :: nil)
                                                   tint cc_default))
        ((Ebinop Oadd (Etempvar _c (tptr tuchar))
           (Econst_int (Int.repr 16) tint) (tptr tuchar)) ::
         (Ebinop Oadd (Etempvar _c (tptr tuchar))
           (Econst_int (Int.repr 32) tint) (tptr tuchar)) ::
         (Ebinop Osub (Etempvar _d tulong) (Econst_int (Int.repr 32) tint)
           tulong) :: (Etempvar _c (tptr tuchar)) :: nil))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 16) tint) tint)
                Sskip
                Sbreak)
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _c (tptr tuchar)) (Etempvar _i tint)
                    (tptr tuchar)) tuchar) (Econst_int (Int.repr 0) tint)))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_crypto_secretbox_xsalsa20poly1305_tweet_open := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr tuchar)) :: (_c, (tptr tuchar)) :: (_d, tulong) ::
                (_n, (tptr tuchar)) :: (_k, (tptr tuchar)) :: nil);
  fn_vars := ((_x, (tarray tuchar 32)) :: nil);
  fn_temps := ((_i, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt (Etempvar _d tulong)
                 (Econst_int (Int.repr 32) tint) tint)
    (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
    Sskip)
  (Ssequence
    (Scall None
      (Evar _crypto_stream_xsalsa20_tweet (Tfunction
                                            ((tptr tuchar) :: tulong ::
                                             (tptr tuchar) ::
                                             (tptr tuchar) :: nil) tint
                                            cc_default))
      ((Evar _x (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
       (Etempvar _n (tptr tuchar)) :: (Etempvar _k (tptr tuchar)) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _crypto_onetimeauth_poly1305_tweet_verify (Tfunction
                                                            ((tptr tuchar) ::
                                                             (tptr tuchar) ::
                                                             tulong ::
                                                             (tptr tuchar) ::
                                                             nil) tint
                                                            cc_default))
          ((Ebinop Oadd (Etempvar _c (tptr tuchar))
             (Econst_int (Int.repr 16) tint) (tptr tuchar)) ::
           (Ebinop Oadd (Etempvar _c (tptr tuchar))
             (Econst_int (Int.repr 32) tint) (tptr tuchar)) ::
           (Ebinop Osub (Etempvar _d tulong) (Econst_int (Int.repr 32) tint)
             tulong) :: (Evar _x (tarray tuchar 32)) :: nil))
        (Sifthenelse (Ebinop One (Etempvar _t'1 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
          Sskip))
      (Ssequence
        (Scall None
          (Evar _crypto_stream_xsalsa20_tweet_xor (Tfunction
                                                    ((tptr tuchar) ::
                                                     (tptr tuchar) ::
                                                     tulong ::
                                                     (tptr tuchar) ::
                                                     (tptr tuchar) :: nil)
                                                    tint cc_default))
          ((Etempvar _m (tptr tuchar)) :: (Etempvar _c (tptr tuchar)) ::
           (Etempvar _d tulong) :: (Etempvar _n (tptr tuchar)) ::
           (Etempvar _k (tptr tuchar)) :: nil))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 32) tint) tint)
                  Sskip
                  Sbreak)
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _m (tptr tuchar))
                      (Etempvar _i tint) (tptr tuchar)) tuchar)
                  (Econst_int (Int.repr 0) tint)))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))
|}.

Definition f_set25519 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tlong)) :: (_a, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 16) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tlong)) (Etempvar _i tint)
              (tptr tlong)) tlong))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _r (tptr tlong)) (Etempvar _i tint)
              (tptr tlong)) tlong) (Etempvar _t'1 tlong))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_car25519 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_c, tlong) :: (_t'4, tlong) :: (_t'3, tlong) ::
               (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 16) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong)
            (Ebinop Oadd (Etempvar _t'4 tlong)
              (Ebinop Oshl (Econst_long (Int64.repr 1) tlong)
                (Econst_int (Int.repr 16) tint) tlong) tlong)))
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                  (tptr tlong)) tlong))
            (Sset _c
              (Ebinop Oshr (Etempvar _t'3 tlong)
                (Econst_int (Int.repr 16) tint) tlong)))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _o (tptr tlong))
                    (Ebinop Omul
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint)
                      (Ebinop Olt (Etempvar _i tint)
                        (Econst_int (Int.repr 15) tint) tint) tint)
                    (tptr tlong)) tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _o (tptr tlong))
                    (Ebinop Omul
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint)
                      (Ebinop Olt (Etempvar _i tint)
                        (Econst_int (Int.repr 15) tint) tint) tint)
                    (tptr tlong)) tlong)
                (Ebinop Oadd (Etempvar _t'2 tlong)
                  (Ebinop Oadd
                    (Ebinop Osub (Etempvar _c tlong)
                      (Econst_int (Int.repr 1) tint) tlong)
                    (Ebinop Omul
                      (Ebinop Omul (Econst_int (Int.repr 37) tint)
                        (Ebinop Osub (Etempvar _c tlong)
                          (Econst_int (Int.repr 1) tint) tlong) tlong)
                      (Ebinop Oeq (Etempvar _i tint)
                        (Econst_int (Int.repr 15) tint) tint) tlong) tlong)
                  tlong)))
            (Ssequence
              (Sset _t'1
                (Ederef
                  (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                    (tptr tlong)) tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                    (tptr tlong)) tlong)
                (Ebinop Osub (Etempvar _t'1 tlong)
                  (Ebinop Oshl (Etempvar _c tlong)
                    (Econst_int (Int.repr 16) tint) tlong) tlong)))))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_sel25519 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tlong)) :: (_q, (tptr tlong)) :: (_b, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t, tlong) :: (_i, tlong) :: (_c, tlong) :: (_t'4, tlong) ::
               (_t'3, tlong) :: (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Sset _c
    (Ecast
      (Eunop Onotint
        (Ebinop Osub (Etempvar _b tint) (Econst_int (Int.repr 1) tint) tint)
        tint) tlong))
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                       (Econst_int (Int.repr 16) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Etempvar _p (tptr tlong)) (Etempvar _i tlong)
                  (tptr tlong)) tlong))
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd (Etempvar _q (tptr tlong)) (Etempvar _i tlong)
                    (tptr tlong)) tlong))
              (Sset _t
                (Ebinop Oand (Etempvar _c tlong)
                  (Ebinop Oxor (Etempvar _t'3 tlong) (Etempvar _t'4 tlong)
                    tlong) tlong))))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _p (tptr tlong)) (Etempvar _i tlong)
                    (tptr tlong)) tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _p (tptr tlong)) (Etempvar _i tlong)
                    (tptr tlong)) tlong)
                (Ebinop Oxor (Etempvar _t'2 tlong) (Etempvar _t tlong) tlong)))
            (Ssequence
              (Sset _t'1
                (Ederef
                  (Ebinop Oadd (Etempvar _q (tptr tlong)) (Etempvar _i tlong)
                    (tptr tlong)) tlong))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _q (tptr tlong)) (Etempvar _i tlong)
                    (tptr tlong)) tlong)
                (Ebinop Oxor (Etempvar _t'1 tlong) (Etempvar _t tlong) tlong))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tlong) (Econst_int (Int.repr 1) tint)
          tlong)))))
|}.

Definition f_pack25519 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tuchar)) :: (_n, (tptr tlong)) :: nil);
  fn_vars := ((_m, (tarray tlong 16)) :: (_t, (tarray tlong 16)) :: nil);
  fn_temps := ((_i, tint) :: (_j, tint) :: (_b, tint) :: (_t'11, tlong) ::
               (_t'10, tlong) :: (_t'9, tlong) :: (_t'8, tlong) ::
               (_t'7, tlong) :: (_t'6, tlong) :: (_t'5, tlong) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, tlong) ::
               (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 16) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'11
            (Ederef
              (Ebinop Oadd (Etempvar _n (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _t (tarray tlong 16)) (Etempvar _i tint)
                (tptr tlong)) tlong) (Etempvar _t'11 tlong))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Scall None
      (Evar _car25519 (Tfunction ((tptr tlong) :: nil) tvoid cc_default))
      ((Evar _t (tarray tlong 16)) :: nil))
    (Ssequence
      (Scall None
        (Evar _car25519 (Tfunction ((tptr tlong) :: nil) tvoid cc_default))
        ((Evar _t (tarray tlong 16)) :: nil))
      (Ssequence
        (Scall None
          (Evar _car25519 (Tfunction ((tptr tlong) :: nil) tvoid cc_default))
          ((Evar _t (tarray tlong 16)) :: nil))
        (Ssequence
          (Ssequence
            (Sset _j (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                               (Econst_int (Int.repr 2) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'10
                      (Ederef
                        (Ebinop Oadd (Evar _t (tarray tlong 16))
                          (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _m (tarray tlong 16))
                          (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                      (Ebinop Osub (Etempvar _t'10 tlong)
                        (Econst_int (Int.repr 65517) tint) tlong)))
                  (Ssequence
                    (Ssequence
                      (Sset _i (Econst_int (Int.repr 1) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                         (Econst_int (Int.repr 15) tint)
                                         tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Ssequence
                              (Sset _t'8
                                (Ederef
                                  (Ebinop Oadd (Evar _t (tarray tlong 16))
                                    (Etempvar _i tint) (tptr tlong)) tlong))
                              (Ssequence
                                (Sset _t'9
                                  (Ederef
                                    (Ebinop Oadd (Evar _m (tarray tlong 16))
                                      (Ebinop Osub (Etempvar _i tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      (tptr tlong)) tlong))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Evar _m (tarray tlong 16))
                                      (Etempvar _i tint) (tptr tlong)) tlong)
                                  (Ebinop Osub
                                    (Ebinop Osub (Etempvar _t'8 tlong)
                                      (Econst_int (Int.repr 65535) tint)
                                      tlong)
                                    (Ebinop Oand
                                      (Ebinop Oshr (Etempvar _t'9 tlong)
                                        (Econst_int (Int.repr 16) tint)
                                        tlong) (Econst_int (Int.repr 1) tint)
                                      tlong) tlong))))
                            (Ssequence
                              (Sset _t'7
                                (Ederef
                                  (Ebinop Oadd (Evar _m (tarray tlong 16))
                                    (Ebinop Osub (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    (tptr tlong)) tlong))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Evar _m (tarray tlong 16))
                                    (Ebinop Osub (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    (tptr tlong)) tlong)
                                (Ebinop Oand (Etempvar _t'7 tlong)
                                  (Econst_int (Int.repr 65535) tint) tlong)))))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'5
                          (Ederef
                            (Ebinop Oadd (Evar _t (tarray tlong 16))
                              (Econst_int (Int.repr 15) tint) (tptr tlong))
                            tlong))
                        (Ssequence
                          (Sset _t'6
                            (Ederef
                              (Ebinop Oadd (Evar _m (tarray tlong 16))
                                (Econst_int (Int.repr 14) tint) (tptr tlong))
                              tlong))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _m (tarray tlong 16))
                                (Econst_int (Int.repr 15) tint) (tptr tlong))
                              tlong)
                            (Ebinop Osub
                              (Ebinop Osub (Etempvar _t'5 tlong)
                                (Econst_int (Int.repr 32767) tint) tlong)
                              (Ebinop Oand
                                (Ebinop Oshr (Etempvar _t'6 tlong)
                                  (Econst_int (Int.repr 16) tint) tlong)
                                (Econst_int (Int.repr 1) tint) tlong) tlong))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'4
                            (Ederef
                              (Ebinop Oadd (Evar _m (tarray tlong 16))
                                (Econst_int (Int.repr 15) tint) (tptr tlong))
                              tlong))
                          (Sset _b
                            (Ecast
                              (Ebinop Oand
                                (Ebinop Oshr (Etempvar _t'4 tlong)
                                  (Econst_int (Int.repr 16) tint) tlong)
                                (Econst_int (Int.repr 1) tint) tlong) tint)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'3
                              (Ederef
                                (Ebinop Oadd (Evar _m (tarray tlong 16))
                                  (Econst_int (Int.repr 14) tint)
                                  (tptr tlong)) tlong))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _m (tarray tlong 16))
                                  (Econst_int (Int.repr 14) tint)
                                  (tptr tlong)) tlong)
                              (Ebinop Oand (Etempvar _t'3 tlong)
                                (Econst_int (Int.repr 65535) tint) tlong)))
                          (Scall None
                            (Evar _sel25519 (Tfunction
                                              ((tptr tlong) ::
                                               (tptr tlong) :: tint :: nil)
                                              tvoid cc_default))
                            ((Evar _t (tarray tlong 16)) ::
                             (Evar _m (tarray tlong 16)) ::
                             (Ebinop Osub (Econst_int (Int.repr 1) tint)
                               (Etempvar _b tint) tint) :: nil))))))))
              (Sset _j
                (Ebinop Oadd (Etempvar _j tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 16) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'2
                      (Ederef
                        (Ebinop Oadd (Evar _t (tarray tlong 16))
                          (Etempvar _i tint) (tptr tlong)) tlong))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _o (tptr tuchar))
                          (Ebinop Omul (Econst_int (Int.repr 2) tint)
                            (Etempvar _i tint) tint) (tptr tuchar)) tuchar)
                      (Ebinop Oand (Etempvar _t'2 tlong)
                        (Econst_int (Int.repr 255) tint) tlong)))
                  (Ssequence
                    (Sset _t'1
                      (Ederef
                        (Ebinop Oadd (Evar _t (tarray tlong 16))
                          (Etempvar _i tint) (tptr tlong)) tlong))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _o (tptr tuchar))
                          (Ebinop Oadd
                            (Ebinop Omul (Econst_int (Int.repr 2) tint)
                              (Etempvar _i tint) tint)
                            (Econst_int (Int.repr 1) tint) tint)
                          (tptr tuchar)) tuchar)
                      (Ebinop Oshr (Etempvar _t'1 tlong)
                        (Econst_int (Int.repr 8) tint) tlong)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint)))))))))
|}.

Definition f_neq25519 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tlong)) :: (_b, (tptr tlong)) :: nil);
  fn_vars := ((_c, (tarray tuchar 32)) :: (_d, (tarray tuchar 32)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _pack25519 (Tfunction ((tptr tuchar) :: (tptr tlong) :: nil) tvoid
                       cc_default))
    ((Evar _c (tarray tuchar 32)) :: (Etempvar _a (tptr tlong)) :: nil))
  (Ssequence
    (Scall None
      (Evar _pack25519 (Tfunction ((tptr tuchar) :: (tptr tlong) :: nil)
                         tvoid cc_default))
      ((Evar _d (tarray tuchar 32)) :: (Etempvar _b (tptr tlong)) :: nil))
    (Ssequence
      (Scall (Some _t'1)
        (Evar _crypto_verify_32_tweet (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         nil) tint cc_default))
        ((Evar _c (tarray tuchar 32)) :: (Evar _d (tarray tuchar 32)) :: nil))
      (Sreturn (Some (Etempvar _t'1 tint))))))
|}.

Definition f_par25519 := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tlong)) :: nil);
  fn_vars := ((_d, (tarray tuchar 32)) :: nil);
  fn_temps := ((_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _pack25519 (Tfunction ((tptr tuchar) :: (tptr tlong) :: nil) tvoid
                       cc_default))
    ((Evar _d (tarray tuchar 32)) :: (Etempvar _a (tptr tlong)) :: nil))
  (Ssequence
    (Sset _t'1
      (Ederef
        (Ebinop Oadd (Evar _d (tarray tuchar 32))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
    (Sreturn (Some (Ebinop Oand (Etempvar _t'1 tuchar)
                     (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_unpack25519 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: (_n, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'3, tuchar) :: (_t'2, tuchar) ::
               (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 16) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'2
            (Ederef
              (Ebinop Oadd (Etempvar _n (tptr tuchar))
                (Ebinop Omul (Econst_int (Int.repr 2) tint)
                  (Etempvar _i tint) tint) (tptr tuchar)) tuchar))
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Etempvar _n (tptr tuchar))
                  (Ebinop Oadd
                    (Ebinop Omul (Econst_int (Int.repr 2) tint)
                      (Etempvar _i tint) tint) (Econst_int (Int.repr 1) tint)
                    tint) (tptr tuchar)) tuchar))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                  (tptr tlong)) tlong)
              (Ebinop Oadd (Etempvar _t'2 tuchar)
                (Ebinop Oshl (Ecast (Etempvar _t'3 tuchar) tlong)
                  (Econst_int (Int.repr 8) tint) tlong) tlong)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Sset _t'1
      (Ederef
        (Ebinop Oadd (Etempvar _o (tptr tlong))
          (Econst_int (Int.repr 15) tint) (tptr tlong)) tlong))
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _o (tptr tlong))
          (Econst_int (Int.repr 15) tint) (tptr tlong)) tlong)
      (Ebinop Oand (Etempvar _t'1 tlong) (Econst_int (Int.repr 32767) tint)
        tlong))))
|}.

Definition f_A := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: (_a, (tptr tlong)) ::
                (_b, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 16) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tlong)) (Etempvar _i tint)
              (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'2
            (Ederef
              (Ebinop Oadd (Etempvar _b (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong)
            (Ebinop Oadd (Etempvar _t'1 tlong) (Etempvar _t'2 tlong) tlong)))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_Z := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: (_a, (tptr tlong)) ::
                (_b, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 16) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tlong)) (Etempvar _i tint)
              (tptr tlong)) tlong))
        (Ssequence
          (Sset _t'2
            (Ederef
              (Ebinop Oadd (Etempvar _b (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _i tint)
                (tptr tlong)) tlong)
            (Ebinop Osub (Etempvar _t'1 tlong) (Etempvar _t'2 tlong) tlong)))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_M := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: (_a, (tptr tlong)) ::
                (_b, (tptr tlong)) :: nil);
  fn_vars := ((_t, (tarray tlong 31)) :: nil);
  fn_temps := ((_i, tlong) :: (_j, tlong) :: (_t'6, tlong) ::
               (_t'5, tlong) :: (_t'4, tlong) :: (_t'3, tlong) ::
               (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                       (Econst_int (Int.repr 31) tint) tint)
          Sskip
          Sbreak)
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _t (tarray tlong 31)) (Etempvar _i tlong)
              (tptr tlong)) tlong) (Econst_int (Int.repr 0) tint)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tlong) (Econst_int (Int.repr 1) tint)
          tlong))))
  (Ssequence
    (Ssequence
      (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                         (Econst_int (Int.repr 16) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tlong))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _j tlong)
                               (Econst_int (Int.repr 16) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'4
                    (Ederef
                      (Ebinop Oadd (Evar _t (tarray tlong 31))
                        (Ebinop Oadd (Etempvar _i tlong) (Etempvar _j tlong)
                          tlong) (tptr tlong)) tlong))
                  (Ssequence
                    (Sset _t'5
                      (Ederef
                        (Ebinop Oadd (Etempvar _a (tptr tlong))
                          (Etempvar _i tlong) (tptr tlong)) tlong))
                    (Ssequence
                      (Sset _t'6
                        (Ederef
                          (Ebinop Oadd (Etempvar _b (tptr tlong))
                            (Etempvar _j tlong) (tptr tlong)) tlong))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _t (tarray tlong 31))
                            (Ebinop Oadd (Etempvar _i tlong)
                              (Etempvar _j tlong) tlong) (tptr tlong)) tlong)
                        (Ebinop Oadd (Etempvar _t'4 tlong)
                          (Ebinop Omul (Etempvar _t'5 tlong)
                            (Etempvar _t'6 tlong) tlong) tlong))))))
              (Sset _j
                (Ebinop Oadd (Etempvar _j tlong)
                  (Econst_int (Int.repr 1) tint) tlong)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tlong) (Econst_int (Int.repr 1) tint)
            tlong))))
    (Ssequence
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                           (Econst_int (Int.repr 15) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Evar _t (tarray tlong 31))
                    (Etempvar _i tlong) (tptr tlong)) tlong))
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd (Evar _t (tarray tlong 31))
                      (Ebinop Oadd (Etempvar _i tlong)
                        (Econst_int (Int.repr 16) tint) tlong) (tptr tlong))
                    tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _t (tarray tlong 31))
                      (Etempvar _i tlong) (tptr tlong)) tlong)
                  (Ebinop Oadd (Etempvar _t'2 tlong)
                    (Ebinop Omul (Econst_int (Int.repr 38) tint)
                      (Etempvar _t'3 tlong) tlong) tlong)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tlong) (Econst_int (Int.repr 1) tint)
              tlong))))
      (Ssequence
        (Ssequence
          (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                             (Econst_int (Int.repr 16) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd (Evar _t (tarray tlong 31))
                      (Etempvar _i tlong) (tptr tlong)) tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _o (tptr tlong))
                      (Etempvar _i tlong) (tptr tlong)) tlong)
                  (Etempvar _t'1 tlong))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tlong) (Econst_int (Int.repr 1) tint)
                tlong))))
        (Ssequence
          (Scall None
            (Evar _car25519 (Tfunction ((tptr tlong) :: nil) tvoid
                              cc_default))
            ((Etempvar _o (tptr tlong)) :: nil))
          (Scall None
            (Evar _car25519 (Tfunction ((tptr tlong) :: nil) tvoid
                              cc_default))
            ((Etempvar _o (tptr tlong)) :: nil)))))))
|}.

Definition f_S := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: (_a, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _M (Tfunction ((tptr tlong) :: (tptr tlong) :: (tptr tlong) :: nil)
             tvoid cc_default))
  ((Etempvar _o (tptr tlong)) :: (Etempvar _a (tptr tlong)) ::
   (Etempvar _a (tptr tlong)) :: nil))
|}.

Definition f_inv25519 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: (_i, (tptr tlong)) :: nil);
  fn_vars := ((_c, (tarray tlong 16)) :: nil);
  fn_temps := ((_a, tint) :: (_t'1, tint) :: (_t'3, tlong) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _a (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _a tint)
                       (Econst_int (Int.repr 16) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'3
            (Ederef
              (Ebinop Oadd (Etempvar _i (tptr tlong)) (Etempvar _a tint)
                (tptr tlong)) tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _c (tarray tlong 16)) (Etempvar _a tint)
                (tptr tlong)) tlong) (Etempvar _t'3 tlong))))
      (Sset _a
        (Ebinop Oadd (Etempvar _a tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Sset _a (Econst_int (Int.repr 253) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Oge (Etempvar _a tint)
                         (Econst_int (Int.repr 0) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Scall None
              (Evar _S (Tfunction ((tptr tlong) :: (tptr tlong) :: nil) tvoid
                         cc_default))
              ((Evar _c (tarray tlong 16)) :: (Evar _c (tarray tlong 16)) ::
               nil))
            (Ssequence
              (Sifthenelse (Ebinop One (Etempvar _a tint)
                             (Econst_int (Int.repr 2) tint) tint)
                (Sset _t'1
                  (Ecast
                    (Ebinop One (Etempvar _a tint)
                      (Econst_int (Int.repr 4) tint) tint) tbool))
                (Sset _t'1 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'1 tint)
                (Scall None
                  (Evar _M (Tfunction
                             ((tptr tlong) :: (tptr tlong) :: (tptr tlong) ::
                              nil) tvoid cc_default))
                  ((Evar _c (tarray tlong 16)) ::
                   (Evar _c (tarray tlong 16)) ::
                   (Etempvar _i (tptr tlong)) :: nil))
                Sskip))))
        (Sset _a
          (Ebinop Osub (Etempvar _a tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sset _a (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _a tint)
                         (Econst_int (Int.repr 16) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Evar _c (tarray tlong 16)) (Etempvar _a tint)
                  (tptr tlong)) tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _a tint)
                  (tptr tlong)) tlong) (Etempvar _t'2 tlong))))
        (Sset _a
          (Ebinop Oadd (Etempvar _a tint) (Econst_int (Int.repr 1) tint)
            tint))))))
|}.

Definition f_pow2523 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr tlong)) :: (_i, (tptr tlong)) :: nil);
  fn_vars := ((_c, (tarray tlong 16)) :: nil);
  fn_temps := ((_a, tint) :: (_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _a (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _a tint)
                       (Econst_int (Int.repr 16) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'2
            (Ederef
              (Ebinop Oadd (Etempvar _i (tptr tlong)) (Etempvar _a tint)
                (tptr tlong)) tlong))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _c (tarray tlong 16)) (Etempvar _a tint)
                (tptr tlong)) tlong) (Etempvar _t'2 tlong))))
      (Sset _a
        (Ebinop Oadd (Etempvar _a tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Sset _a (Econst_int (Int.repr 250) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Oge (Etempvar _a tint)
                         (Econst_int (Int.repr 0) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Scall None
              (Evar _S (Tfunction ((tptr tlong) :: (tptr tlong) :: nil) tvoid
                         cc_default))
              ((Evar _c (tarray tlong 16)) :: (Evar _c (tarray tlong 16)) ::
               nil))
            (Sifthenelse (Ebinop One (Etempvar _a tint)
                           (Econst_int (Int.repr 1) tint) tint)
              (Scall None
                (Evar _M (Tfunction
                           ((tptr tlong) :: (tptr tlong) :: (tptr tlong) ::
                            nil) tvoid cc_default))
                ((Evar _c (tarray tlong 16)) ::
                 (Evar _c (tarray tlong 16)) :: (Etempvar _i (tptr tlong)) ::
                 nil))
              Sskip)))
        (Sset _a
          (Ebinop Osub (Etempvar _a tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sset _a (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _a tint)
                         (Econst_int (Int.repr 16) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Evar _c (tarray tlong 16)) (Etempvar _a tint)
                  (tptr tlong)) tlong))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _o (tptr tlong)) (Etempvar _a tint)
                  (tptr tlong)) tlong) (Etempvar _t'1 tlong))))
        (Sset _a
          (Ebinop Oadd (Etempvar _a tint) (Econst_int (Int.repr 1) tint)
            tint))))))
|}.

Definition f_crypto_scalarmult_curve25519_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_q, (tptr tuchar)) :: (_n, (tptr tuchar)) ::
                (_p, (tptr tuchar)) :: nil);
  fn_vars := ((_z, (tarray tuchar 32)) :: (_x, (tarray tlong 80)) ::
              (_a, (tarray tlong 16)) :: (_b, (tarray tlong 16)) ::
              (_c, (tarray tlong 16)) :: (_d, (tarray tlong 16)) ::
              (_e, (tarray tlong 16)) :: (_f, (tarray tlong 16)) :: nil);
  fn_temps := ((_r, tlong) :: (_i, tlong) :: (_t'3, tlong) ::
               (_t'2, tlong) :: (_t'1, tlong) :: (_t'12, tuchar) ::
               (_t'11, tuchar) :: (_t'10, tuchar) :: (_t'9, tlong) ::
               (_t'8, tuchar) :: (_t'7, tlong) :: (_t'6, tlong) ::
               (_t'5, tlong) :: (_t'4, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                       (Econst_int (Int.repr 31) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'12
            (Ederef
              (Ebinop Oadd (Etempvar _n (tptr tuchar)) (Etempvar _i tlong)
                (tptr tuchar)) tuchar))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _z (tarray tuchar 32)) (Etempvar _i tlong)
                (tptr tuchar)) tuchar) (Etempvar _t'12 tuchar))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tlong) (Econst_int (Int.repr 1) tint)
          tlong))))
  (Ssequence
    (Ssequence
      (Sset _t'11
        (Ederef
          (Ebinop Oadd (Etempvar _n (tptr tuchar))
            (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar))
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _z (tarray tuchar 32))
            (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar)
        (Ebinop Oor
          (Ebinop Oand (Etempvar _t'11 tuchar)
            (Econst_int (Int.repr 127) tint) tint)
          (Econst_int (Int.repr 64) tint) tint)))
    (Ssequence
      (Ssequence
        (Sset _t'10
          (Ederef
            (Ebinop Oadd (Evar _z (tarray tuchar 32))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _z (tarray tuchar 32))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
          (Ebinop Oand (Etempvar _t'10 tuchar)
            (Econst_int (Int.repr 248) tint) tint)))
      (Ssequence
        (Scall None
          (Evar _unpack25519 (Tfunction
                               ((tptr tlong) :: (tptr tuchar) :: nil) tvoid
                               cc_default))
          ((Evar _x (tarray tlong 80)) :: (Etempvar _p (tptr tuchar)) :: nil))
        (Ssequence
          (Ssequence
            (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                               (Econst_int (Int.repr 16) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'9
                      (Ederef
                        (Ebinop Oadd (Evar _x (tarray tlong 80))
                          (Etempvar _i tlong) (tptr tlong)) tlong))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _b (tarray tlong 16))
                          (Etempvar _i tlong) (tptr tlong)) tlong)
                      (Etempvar _t'9 tlong)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'1
                            (Ecast (Econst_int (Int.repr 0) tint) tlong))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _c (tarray tlong 16))
                                (Etempvar _i tlong) (tptr tlong)) tlong)
                            (Etempvar _t'1 tlong)))
                        (Sset _t'2 (Ecast (Etempvar _t'1 tlong) tlong)))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _a (tarray tlong 16))
                            (Etempvar _i tlong) (tptr tlong)) tlong)
                        (Etempvar _t'2 tlong)))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _d (tarray tlong 16))
                          (Etempvar _i tlong) (tptr tlong)) tlong)
                      (Etempvar _t'2 tlong)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tlong)
                  (Econst_int (Int.repr 1) tint) tlong))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'3 (Ecast (Econst_int (Int.repr 1) tint) tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _d (tarray tlong 16))
                      (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                  (Etempvar _t'3 tlong)))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _a (tarray tlong 16))
                    (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
                (Etempvar _t'3 tlong)))
            (Ssequence
              (Ssequence
                (Sset _i (Ecast (Econst_int (Int.repr 254) tint) tlong))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Oge (Etempvar _i tlong)
                                   (Econst_int (Int.repr 0) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Sset _t'8
                          (Ederef
                            (Ebinop Oadd (Evar _z (tarray tuchar 32))
                              (Ebinop Oshr (Etempvar _i tlong)
                                (Econst_int (Int.repr 3) tint) tlong)
                              (tptr tuchar)) tuchar))
                        (Sset _r
                          (Ecast
                            (Ebinop Oand
                              (Ebinop Oshr (Etempvar _t'8 tuchar)
                                (Ebinop Oand (Etempvar _i tlong)
                                  (Econst_int (Int.repr 7) tint) tlong) tint)
                              (Econst_int (Int.repr 1) tint) tint) tlong)))
                      (Ssequence
                        (Scall None
                          (Evar _sel25519 (Tfunction
                                            ((tptr tlong) :: (tptr tlong) ::
                                             tint :: nil) tvoid cc_default))
                          ((Evar _a (tarray tlong 16)) ::
                           (Evar _b (tarray tlong 16)) ::
                           (Etempvar _r tlong) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _sel25519 (Tfunction
                                              ((tptr tlong) ::
                                               (tptr tlong) :: tint :: nil)
                                              tvoid cc_default))
                            ((Evar _c (tarray tlong 16)) ::
                             (Evar _d (tarray tlong 16)) ::
                             (Etempvar _r tlong) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _A (Tfunction
                                         ((tptr tlong) :: (tptr tlong) ::
                                          (tptr tlong) :: nil) tvoid
                                         cc_default))
                              ((Evar _e (tarray tlong 16)) ::
                               (Evar _a (tarray tlong 16)) ::
                               (Evar _c (tarray tlong 16)) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _Z (Tfunction
                                           ((tptr tlong) :: (tptr tlong) ::
                                            (tptr tlong) :: nil) tvoid
                                           cc_default))
                                ((Evar _a (tarray tlong 16)) ::
                                 (Evar _a (tarray tlong 16)) ::
                                 (Evar _c (tarray tlong 16)) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _A (Tfunction
                                             ((tptr tlong) :: (tptr tlong) ::
                                              (tptr tlong) :: nil) tvoid
                                             cc_default))
                                  ((Evar _c (tarray tlong 16)) ::
                                   (Evar _b (tarray tlong 16)) ::
                                   (Evar _d (tarray tlong 16)) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _Z (Tfunction
                                               ((tptr tlong) ::
                                                (tptr tlong) ::
                                                (tptr tlong) :: nil) tvoid
                                               cc_default))
                                    ((Evar _b (tarray tlong 16)) ::
                                     (Evar _b (tarray tlong 16)) ::
                                     (Evar _d (tarray tlong 16)) :: nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _S (Tfunction
                                                 ((tptr tlong) ::
                                                  (tptr tlong) :: nil) tvoid
                                                 cc_default))
                                      ((Evar _d (tarray tlong 16)) ::
                                       (Evar _e (tarray tlong 16)) :: nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _S (Tfunction
                                                   ((tptr tlong) ::
                                                    (tptr tlong) :: nil)
                                                   tvoid cc_default))
                                        ((Evar _f (tarray tlong 16)) ::
                                         (Evar _a (tarray tlong 16)) :: nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _M (Tfunction
                                                     ((tptr tlong) ::
                                                      (tptr tlong) ::
                                                      (tptr tlong) :: nil)
                                                     tvoid cc_default))
                                          ((Evar _a (tarray tlong 16)) ::
                                           (Evar _c (tarray tlong 16)) ::
                                           (Evar _a (tarray tlong 16)) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _M (Tfunction
                                                       ((tptr tlong) ::
                                                        (tptr tlong) ::
                                                        (tptr tlong) :: nil)
                                                       tvoid cc_default))
                                            ((Evar _c (tarray tlong 16)) ::
                                             (Evar _b (tarray tlong 16)) ::
                                             (Evar _e (tarray tlong 16)) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _A (Tfunction
                                                         ((tptr tlong) ::
                                                          (tptr tlong) ::
                                                          (tptr tlong) ::
                                                          nil) tvoid
                                                         cc_default))
                                              ((Evar _e (tarray tlong 16)) ::
                                               (Evar _a (tarray tlong 16)) ::
                                               (Evar _c (tarray tlong 16)) ::
                                               nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _Z (Tfunction
                                                           ((tptr tlong) ::
                                                            (tptr tlong) ::
                                                            (tptr tlong) ::
                                                            nil) tvoid
                                                           cc_default))
                                                ((Evar _a (tarray tlong 16)) ::
                                                 (Evar _a (tarray tlong 16)) ::
                                                 (Evar _c (tarray tlong 16)) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _S (Tfunction
                                                             ((tptr tlong) ::
                                                              (tptr tlong) ::
                                                              nil) tvoid
                                                             cc_default))
                                                  ((Evar _b (tarray tlong 16)) ::
                                                   (Evar _a (tarray tlong 16)) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _Z (Tfunction
                                                               ((tptr tlong) ::
                                                                (tptr tlong) ::
                                                                (tptr tlong) ::
                                                                nil) tvoid
                                                               cc_default))
                                                    ((Evar _c (tarray tlong 16)) ::
                                                     (Evar _d (tarray tlong 16)) ::
                                                     (Evar _f (tarray tlong 16)) ::
                                                     nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _M (Tfunction
                                                                 ((tptr tlong) ::
                                                                  (tptr tlong) ::
                                                                  (tptr tlong) ::
                                                                  nil) tvoid
                                                                 cc_default))
                                                      ((Evar _a (tarray tlong 16)) ::
                                                       (Evar _c (tarray tlong 16)) ::
                                                       (Evar __121665 (tarray tlong 16)) ::
                                                       nil))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _A (Tfunction
                                                                   ((tptr tlong) ::
                                                                    (tptr tlong) ::
                                                                    (tptr tlong) ::
                                                                    nil)
                                                                   tvoid
                                                                   cc_default))
                                                        ((Evar _a (tarray tlong 16)) ::
                                                         (Evar _a (tarray tlong 16)) ::
                                                         (Evar _d (tarray tlong 16)) ::
                                                         nil))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _M (Tfunction
                                                                    ((tptr tlong) ::
                                                                    (tptr tlong) ::
                                                                    (tptr tlong) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                          ((Evar _c (tarray tlong 16)) ::
                                                           (Evar _c (tarray tlong 16)) ::
                                                           (Evar _a (tarray tlong 16)) ::
                                                           nil))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _M 
                                                            (Tfunction
                                                              ((tptr tlong) ::
                                                               (tptr tlong) ::
                                                               (tptr tlong) ::
                                                               nil) tvoid
                                                              cc_default))
                                                            ((Evar _a (tarray tlong 16)) ::
                                                             (Evar _d (tarray tlong 16)) ::
                                                             (Evar _f (tarray tlong 16)) ::
                                                             nil))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _M 
                                                              (Tfunction
                                                                ((tptr tlong) ::
                                                                 (tptr tlong) ::
                                                                 (tptr tlong) ::
                                                                 nil) tvoid
                                                                cc_default))
                                                              ((Evar _d (tarray tlong 16)) ::
                                                               (Evar _b (tarray tlong 16)) ::
                                                               (Evar _x (tarray tlong 80)) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _S 
                                                                (Tfunction
                                                                  ((tptr tlong) ::
                                                                   (tptr tlong) ::
                                                                   nil) tvoid
                                                                  cc_default))
                                                                ((Evar _b (tarray tlong 16)) ::
                                                                 (Evar _e (tarray tlong 16)) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _sel25519 
                                                                  (Tfunction
                                                                    ((tptr tlong) ::
                                                                    (tptr tlong) ::
                                                                    tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Evar _a (tarray tlong 16)) ::
                                                                   (Evar _b (tarray tlong 16)) ::
                                                                   (Etempvar _r tlong) ::
                                                                   nil))
                                                                (Scall None
                                                                  (Evar _sel25519 
                                                                  (Tfunction
                                                                    ((tptr tlong) ::
                                                                    (tptr tlong) ::
                                                                    tint ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Evar _c (tarray tlong 16)) ::
                                                                   (Evar _d (tarray tlong 16)) ::
                                                                   (Etempvar _r tlong) ::
                                                                   nil)))))))))))))))))))))))))
                  (Sset _i
                    (Ebinop Osub (Etempvar _i tlong)
                      (Econst_int (Int.repr 1) tint) tlong))))
              (Ssequence
                (Ssequence
                  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                                     (Econst_int (Int.repr 16) tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Ssequence
                          (Sset _t'7
                            (Ederef
                              (Ebinop Oadd (Evar _a (tarray tlong 16))
                                (Etempvar _i tlong) (tptr tlong)) tlong))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _x (tarray tlong 80))
                                (Ebinop Oadd (Etempvar _i tlong)
                                  (Econst_int (Int.repr 16) tint) tlong)
                                (tptr tlong)) tlong) (Etempvar _t'7 tlong)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'6
                              (Ederef
                                (Ebinop Oadd (Evar _c (tarray tlong 16))
                                  (Etempvar _i tlong) (tptr tlong)) tlong))
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _x (tarray tlong 80))
                                  (Ebinop Oadd (Etempvar _i tlong)
                                    (Econst_int (Int.repr 32) tint) tlong)
                                  (tptr tlong)) tlong) (Etempvar _t'6 tlong)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'5
                                (Ederef
                                  (Ebinop Oadd (Evar _b (tarray tlong 16))
                                    (Etempvar _i tlong) (tptr tlong)) tlong))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Evar _x (tarray tlong 80))
                                    (Ebinop Oadd (Etempvar _i tlong)
                                      (Econst_int (Int.repr 48) tint) tlong)
                                    (tptr tlong)) tlong)
                                (Etempvar _t'5 tlong)))
                            (Ssequence
                              (Sset _t'4
                                (Ederef
                                  (Ebinop Oadd (Evar _d (tarray tlong 16))
                                    (Etempvar _i tlong) (tptr tlong)) tlong))
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Evar _x (tarray tlong 80))
                                    (Ebinop Oadd (Etempvar _i tlong)
                                      (Econst_int (Int.repr 64) tint) tlong)
                                    (tptr tlong)) tlong)
                                (Etempvar _t'4 tlong)))))))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tlong)
                        (Econst_int (Int.repr 1) tint) tlong))))
                (Ssequence
                  (Scall None
                    (Evar _inv25519 (Tfunction
                                      ((tptr tlong) :: (tptr tlong) :: nil)
                                      tvoid cc_default))
                    ((Ebinop Oadd (Evar _x (tarray tlong 80))
                       (Econst_int (Int.repr 32) tint) (tptr tlong)) ::
                     (Ebinop Oadd (Evar _x (tarray tlong 80))
                       (Econst_int (Int.repr 32) tint) (tptr tlong)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _M (Tfunction
                                 ((tptr tlong) :: (tptr tlong) ::
                                  (tptr tlong) :: nil) tvoid cc_default))
                      ((Ebinop Oadd (Evar _x (tarray tlong 80))
                         (Econst_int (Int.repr 16) tint) (tptr tlong)) ::
                       (Ebinop Oadd (Evar _x (tarray tlong 80))
                         (Econst_int (Int.repr 16) tint) (tptr tlong)) ::
                       (Ebinop Oadd (Evar _x (tarray tlong 80))
                         (Econst_int (Int.repr 32) tint) (tptr tlong)) ::
                       nil))
                    (Ssequence
                      (Scall None
                        (Evar _pack25519 (Tfunction
                                           ((tptr tuchar) :: (tptr tlong) ::
                                            nil) tvoid cc_default))
                        ((Etempvar _q (tptr tuchar)) ::
                         (Ebinop Oadd (Evar _x (tarray tlong 80))
                           (Econst_int (Int.repr 16) tint) (tptr tlong)) ::
                         nil))
                      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))
|}.

Definition f_crypto_scalarmult_curve25519_tweet_base := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_q, (tptr tuchar)) :: (_n, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _crypto_scalarmult_curve25519_tweet (Tfunction
                                                ((tptr tuchar) ::
                                                 (tptr tuchar) ::
                                                 (tptr tuchar) :: nil) tint
                                                cc_default))
    ((Etempvar _q (tptr tuchar)) :: (Etempvar _n (tptr tuchar)) ::
     (Evar __9 (tarray tuchar 32)) :: nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_crypto_box_curve25519xsalsa20poly1305_tweet_keypair := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_y, (tptr tuchar)) :: (_x, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _randombytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                         cc_default))
    ((Etempvar _x (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _crypto_scalarmult_curve25519_tweet_base (Tfunction
                                                       ((tptr tuchar) ::
                                                        (tptr tuchar) :: nil)
                                                       tint cc_default))
      ((Etempvar _y (tptr tuchar)) :: (Etempvar _x (tptr tuchar)) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_crypto_box_curve25519xsalsa20poly1305_tweet_beforenm := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_k, (tptr tuchar)) :: (_y, (tptr tuchar)) ::
                (_x, (tptr tuchar)) :: nil);
  fn_vars := ((_s, (tarray tuchar 32)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _crypto_scalarmult_curve25519_tweet (Tfunction
                                                ((tptr tuchar) ::
                                                 (tptr tuchar) ::
                                                 (tptr tuchar) :: nil) tint
                                                cc_default))
    ((Evar _s (tarray tuchar 32)) :: (Etempvar _x (tptr tuchar)) ::
     (Etempvar _y (tptr tuchar)) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _crypto_core_hsalsa20_tweet (Tfunction
                                          ((tptr tuchar) :: (tptr tuchar) ::
                                           (tptr tuchar) :: (tptr tuchar) ::
                                           nil) tint cc_default))
      ((Etempvar _k (tptr tuchar)) :: (Evar __0 (tarray tuchar 16)) ::
       (Evar _s (tarray tuchar 32)) :: (Evar _sigma (tarray tuchar 16)) ::
       nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_crypto_box_curve25519xsalsa20poly1305_tweet_afternm := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr tuchar)) :: (_m, (tptr tuchar)) :: (_d, tulong) ::
                (_n, (tptr tuchar)) :: (_k, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _crypto_secretbox_xsalsa20poly1305_tweet (Tfunction
                                                     ((tptr tuchar) ::
                                                      (tptr tuchar) ::
                                                      tulong ::
                                                      (tptr tuchar) ::
                                                      (tptr tuchar) :: nil)
                                                     tint cc_default))
    ((Etempvar _c (tptr tuchar)) :: (Etempvar _m (tptr tuchar)) ::
     (Etempvar _d tulong) :: (Etempvar _n (tptr tuchar)) ::
     (Etempvar _k (tptr tuchar)) :: nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_crypto_box_curve25519xsalsa20poly1305_tweet_open_afternm := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr tuchar)) :: (_c, (tptr tuchar)) :: (_d, tulong) ::
                (_n, (tptr tuchar)) :: (_k, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _crypto_secretbox_xsalsa20poly1305_tweet_open (Tfunction
                                                          ((tptr tuchar) ::
                                                           (tptr tuchar) ::
                                                           tulong ::
                                                           (tptr tuchar) ::
                                                           (tptr tuchar) ::
                                                           nil) tint
                                                          cc_default))
    ((Etempvar _m (tptr tuchar)) :: (Etempvar _c (tptr tuchar)) ::
     (Etempvar _d tulong) :: (Etempvar _n (tptr tuchar)) ::
     (Etempvar _k (tptr tuchar)) :: nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_crypto_box_curve25519xsalsa20poly1305_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr tuchar)) :: (_m, (tptr tuchar)) :: (_d, tulong) ::
                (_n, (tptr tuchar)) :: (_y, (tptr tuchar)) ::
                (_x, (tptr tuchar)) :: nil);
  fn_vars := ((_k, (tarray tuchar 32)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _crypto_box_curve25519xsalsa20poly1305_tweet_beforenm (Tfunction
                                                                  ((tptr tuchar) ::
                                                                   (tptr tuchar) ::
                                                                   (tptr tuchar) ::
                                                                   nil) tint
                                                                  cc_default))
    ((Evar _k (tarray tuchar 32)) :: (Etempvar _y (tptr tuchar)) ::
     (Etempvar _x (tptr tuchar)) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _crypto_box_curve25519xsalsa20poly1305_tweet_afternm (Tfunction
                                                                   ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                   cc_default))
      ((Etempvar _c (tptr tuchar)) :: (Etempvar _m (tptr tuchar)) ::
       (Etempvar _d tulong) :: (Etempvar _n (tptr tuchar)) ::
       (Evar _k (tarray tuchar 32)) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_crypto_box_curve25519xsalsa20poly1305_tweet_open := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr tuchar)) :: (_c, (tptr tuchar)) :: (_d, tulong) ::
                (_n, (tptr tuchar)) :: (_y, (tptr tuchar)) ::
                (_x, (tptr tuchar)) :: nil);
  fn_vars := ((_k, (tarray tuchar 32)) :: nil);
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _crypto_box_curve25519xsalsa20poly1305_tweet_beforenm (Tfunction
                                                                  ((tptr tuchar) ::
                                                                   (tptr tuchar) ::
                                                                   (tptr tuchar) ::
                                                                   nil) tint
                                                                  cc_default))
    ((Evar _k (tarray tuchar 32)) :: (Etempvar _y (tptr tuchar)) ::
     (Etempvar _x (tptr tuchar)) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _crypto_box_curve25519xsalsa20poly1305_tweet_open_afternm 
      (Tfunction
        ((tptr tuchar) :: (tptr tuchar) :: tulong :: (tptr tuchar) ::
         (tptr tuchar) :: nil) tint cc_default))
      ((Etempvar _m (tptr tuchar)) :: (Etempvar _c (tptr tuchar)) ::
       (Etempvar _d tulong) :: (Etempvar _n (tptr tuchar)) ::
       (Evar _k (tarray tuchar 32)) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_R := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_x, tulong) :: (_c, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oor
                 (Ebinop Oshr (Etempvar _x tulong) (Etempvar _c tint) tulong)
                 (Ebinop Oshl (Etempvar _x tulong)
                   (Ebinop Osub (Econst_int (Int.repr 64) tint)
                     (Etempvar _c tint) tint) tulong) tulong)))
|}.

Definition f_Ch := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_x, tulong) :: (_y, tulong) :: (_z, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oxor
                 (Ebinop Oand (Etempvar _x tulong) (Etempvar _y tulong)
                   tulong)
                 (Ebinop Oand (Eunop Onotint (Etempvar _x tulong) tulong)
                   (Etempvar _z tulong) tulong) tulong)))
|}.

Definition f_Maj := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_x, tulong) :: (_y, tulong) :: (_z, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oxor
                 (Ebinop Oxor
                   (Ebinop Oand (Etempvar _x tulong) (Etempvar _y tulong)
                     tulong)
                   (Ebinop Oand (Etempvar _x tulong) (Etempvar _z tulong)
                     tulong) tulong)
                 (Ebinop Oand (Etempvar _y tulong) (Etempvar _z tulong)
                   tulong) tulong)))
|}.

Definition f_Sigma0 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_x, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _R (Tfunction (tulong :: tint :: nil) tulong cc_default))
        ((Etempvar _x tulong) :: (Econst_int (Int.repr 28) tint) :: nil))
      (Scall (Some _t'2)
        (Evar _R (Tfunction (tulong :: tint :: nil) tulong cc_default))
        ((Etempvar _x tulong) :: (Econst_int (Int.repr 34) tint) :: nil)))
    (Scall (Some _t'3)
      (Evar _R (Tfunction (tulong :: tint :: nil) tulong cc_default))
      ((Etempvar _x tulong) :: (Econst_int (Int.repr 39) tint) :: nil)))
  (Sreturn (Some (Ebinop Oxor
                   (Ebinop Oxor (Etempvar _t'1 tulong) (Etempvar _t'2 tulong)
                     tulong) (Etempvar _t'3 tulong) tulong))))
|}.

Definition f_Sigma1 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_x, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _R (Tfunction (tulong :: tint :: nil) tulong cc_default))
        ((Etempvar _x tulong) :: (Econst_int (Int.repr 14) tint) :: nil))
      (Scall (Some _t'2)
        (Evar _R (Tfunction (tulong :: tint :: nil) tulong cc_default))
        ((Etempvar _x tulong) :: (Econst_int (Int.repr 18) tint) :: nil)))
    (Scall (Some _t'3)
      (Evar _R (Tfunction (tulong :: tint :: nil) tulong cc_default))
      ((Etempvar _x tulong) :: (Econst_int (Int.repr 41) tint) :: nil)))
  (Sreturn (Some (Ebinop Oxor
                   (Ebinop Oxor (Etempvar _t'1 tulong) (Etempvar _t'2 tulong)
                     tulong) (Etempvar _t'3 tulong) tulong))))
|}.

Definition f_sigma0 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_x, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _R (Tfunction (tulong :: tint :: nil) tulong cc_default))
      ((Etempvar _x tulong) :: (Econst_int (Int.repr 1) tint) :: nil))
    (Scall (Some _t'2)
      (Evar _R (Tfunction (tulong :: tint :: nil) tulong cc_default))
      ((Etempvar _x tulong) :: (Econst_int (Int.repr 8) tint) :: nil)))
  (Sreturn (Some (Ebinop Oxor
                   (Ebinop Oxor (Etempvar _t'1 tulong) (Etempvar _t'2 tulong)
                     tulong)
                   (Ebinop Oshr (Etempvar _x tulong)
                     (Econst_int (Int.repr 7) tint) tulong) tulong))))
|}.

Definition f_sigma1 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_x, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _R (Tfunction (tulong :: tint :: nil) tulong cc_default))
      ((Etempvar _x tulong) :: (Econst_int (Int.repr 19) tint) :: nil))
    (Scall (Some _t'2)
      (Evar _R (Tfunction (tulong :: tint :: nil) tulong cc_default))
      ((Etempvar _x tulong) :: (Econst_int (Int.repr 61) tint) :: nil)))
  (Sreturn (Some (Ebinop Oxor
                   (Ebinop Oxor (Etempvar _t'1 tulong) (Etempvar _t'2 tulong)
                     tulong)
                   (Ebinop Oshr (Etempvar _x tulong)
                     (Econst_int (Int.repr 6) tint) tulong) tulong))))
|}.

Definition v_K := {|
  gvar_info := (tarray tulong 80);
  gvar_init := (Init_int64 (Int64.repr 4794697086780616226) ::
                Init_int64 (Int64.repr 8158064640168781261) ::
                Init_int64 (Int64.repr (-5349999486874862801)) ::
                Init_int64 (Int64.repr (-1606136188198331460)) ::
                Init_int64 (Int64.repr 4131703408338449720) ::
                Init_int64 (Int64.repr 6480981068601479193) ::
                Init_int64 (Int64.repr (-7908458776815382629)) ::
                Init_int64 (Int64.repr (-6116909921290321640)) ::
                Init_int64 (Int64.repr (-2880145864133508542)) ::
                Init_int64 (Int64.repr 1334009975649890238) ::
                Init_int64 (Int64.repr 2608012711638119052) ::
                Init_int64 (Int64.repr 6128411473006802146) ::
                Init_int64 (Int64.repr 8268148722764581231) ::
                Init_int64 (Int64.repr (-9160688886553864527)) ::
                Init_int64 (Int64.repr (-7215885187991268811)) ::
                Init_int64 (Int64.repr (-4495734319001033068)) ::
                Init_int64 (Int64.repr (-1973867731355612462)) ::
                Init_int64 (Int64.repr (-1171420211273849373)) ::
                Init_int64 (Int64.repr 1135362057144423861) ::
                Init_int64 (Int64.repr 2597628984639134821) ::
                Init_int64 (Int64.repr 3308224258029322869) ::
                Init_int64 (Int64.repr 5365058923640841347) ::
                Init_int64 (Int64.repr 6679025012923562964) ::
                Init_int64 (Int64.repr 8573033837759648693) ::
                Init_int64 (Int64.repr (-7476448914759557205)) ::
                Init_int64 (Int64.repr (-6327057829258317296)) ::
                Init_int64 (Int64.repr (-5763719355590565569)) ::
                Init_int64 (Int64.repr (-4658551843659510044)) ::
                Init_int64 (Int64.repr (-4116276920077217854)) ::
                Init_int64 (Int64.repr (-3051310485924567259)) ::
                Init_int64 (Int64.repr 489312712824947311) ::
                Init_int64 (Int64.repr 1452737877330783856) ::
                Init_int64 (Int64.repr 2861767655752347644) ::
                Init_int64 (Int64.repr 3322285676063803686) ::
                Init_int64 (Int64.repr 5560940570517711597) ::
                Init_int64 (Int64.repr 5996557281743188959) ::
                Init_int64 (Int64.repr 7280758554555802590) ::
                Init_int64 (Int64.repr 8532644243296465576) ::
                Init_int64 (Int64.repr (-9096487096722542874)) ::
                Init_int64 (Int64.repr (-7894198246740708037)) ::
                Init_int64 (Int64.repr (-6719396339535248540)) ::
                Init_int64 (Int64.repr (-6333637450476146687)) ::
                Init_int64 (Int64.repr (-4446306890439682159)) ::
                Init_int64 (Int64.repr (-4076793802049405392)) ::
                Init_int64 (Int64.repr (-3345356375505022440)) ::
                Init_int64 (Int64.repr (-2983346525034927856)) ::
                Init_int64 (Int64.repr (-860691631967231958)) ::
                Init_int64 (Int64.repr 1182934255886127544) ::
                Init_int64 (Int64.repr 1847814050463011016) ::
                Init_int64 (Int64.repr 2177327727835720531) ::
                Init_int64 (Int64.repr 2830643537854262169) ::
                Init_int64 (Int64.repr 3796741975233480872) ::
                Init_int64 (Int64.repr 4115178125766777443) ::
                Init_int64 (Int64.repr 5681478168544905931) ::
                Init_int64 (Int64.repr 6601373596472566643) ::
                Init_int64 (Int64.repr 7507060721942968483) ::
                Init_int64 (Int64.repr 8399075790359081724) ::
                Init_int64 (Int64.repr 8693463985226723168) ::
                Init_int64 (Int64.repr (-8878714635349349518)) ::
                Init_int64 (Int64.repr (-8302665154208450068)) ::
                Init_int64 (Int64.repr (-8016688836872298968)) ::
                Init_int64 (Int64.repr (-6606660893046293015)) ::
                Init_int64 (Int64.repr (-4685533653050689259)) ::
                Init_int64 (Int64.repr (-4147400797238176981)) ::
                Init_int64 (Int64.repr (-3880063495543823972)) ::
                Init_int64 (Int64.repr (-3348786107499101689)) ::
                Init_int64 (Int64.repr (-1523767162380948706)) ::
                Init_int64 (Int64.repr (-757361751448694408)) ::
                Init_int64 (Int64.repr 500013540394364858) ::
                Init_int64 (Int64.repr 748580250866718886) ::
                Init_int64 (Int64.repr 1242879168328830382) ::
                Init_int64 (Int64.repr 1977374033974150939) ::
                Init_int64 (Int64.repr 2944078676154940804) ::
                Init_int64 (Int64.repr 3659926193048069267) ::
                Init_int64 (Int64.repr 4368137639120453308) ::
                Init_int64 (Int64.repr 4836135668995329356) ::
                Init_int64 (Int64.repr 5532061633213252278) ::
                Init_int64 (Int64.repr 6448918945643986474) ::
                Init_int64 (Int64.repr 6902733635092675308) ::
                Init_int64 (Int64.repr 7801388544844847127) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_crypto_hashblocks_sha512_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tuchar)) :: (_m, (tptr tuchar)) :: (_n, tulong) ::
                nil);
  fn_vars := ((_z, (tarray tulong 8)) :: (_b, (tarray tulong 8)) ::
              (_a, (tarray tulong 8)) :: (_w, (tarray tulong 16)) :: nil);
  fn_temps := ((_t, tulong) :: (_i, tint) :: (_j, tint) :: (_t'9, tulong) ::
               (_t'8, tulong) :: (_t'7, tulong) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tulong) :: (_t'3, tulong) ::
               (_t'2, tulong) :: (_t'1, tulong) :: (_t'31, tulong) ::
               (_t'30, tulong) :: (_t'29, tulong) :: (_t'28, tulong) ::
               (_t'27, tulong) :: (_t'26, tulong) :: (_t'25, tulong) ::
               (_t'24, tulong) :: (_t'23, tulong) :: (_t'22, tulong) ::
               (_t'21, tulong) :: (_t'20, tulong) :: (_t'19, tulong) ::
               (_t'18, tulong) :: (_t'17, tulong) :: (_t'16, tulong) ::
               (_t'15, tulong) :: (_t'14, tulong) :: (_t'13, tulong) ::
               (_t'12, tulong) :: (_t'11, tulong) :: (_t'10, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 8) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _dl64 (Tfunction ((tptr tuchar) :: nil) tulong
                              cc_default))
                ((Ebinop Oadd (Etempvar _x (tptr tuchar))
                   (Ebinop Omul (Econst_int (Int.repr 8) tint)
                     (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
              (Sset _t'2 (Ecast (Etempvar _t'1 tulong) tulong)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _a (tarray tulong 8)) (Etempvar _i tint)
                  (tptr tulong)) tulong) (Etempvar _t'2 tulong)))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _z (tarray tulong 8)) (Etempvar _i tint)
                (tptr tulong)) tulong) (Etempvar _t'2 tulong))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Swhile
      (Ebinop Oge (Etempvar _n tulong) (Econst_int (Int.repr 128) tint) tint)
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 16) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _dl64 (Tfunction ((tptr tuchar) :: nil) tulong
                                cc_default))
                  ((Ebinop Oadd (Etempvar _m (tptr tuchar))
                     (Ebinop Omul (Econst_int (Int.repr 8) tint)
                       (Etempvar _i tint) tint) (tptr tuchar)) :: nil))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _w (tarray tulong 16))
                      (Etempvar _i tint) (tptr tulong)) tulong)
                  (Etempvar _t'3 tulong))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 80) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _j (Econst_int (Int.repr 0) tint))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                       (Econst_int (Int.repr 8) tint) tint)
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Sset _t'31
                            (Ederef
                              (Ebinop Oadd (Evar _a (tarray tulong 8))
                                (Etempvar _j tint) (tptr tulong)) tulong))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _b (tarray tulong 8))
                                (Etempvar _j tint) (tptr tulong)) tulong)
                            (Etempvar _t'31 tulong))))
                      (Sset _j
                        (Ebinop Oadd (Etempvar _j tint)
                          (Econst_int (Int.repr 1) tint) tint))))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'30
                            (Ederef
                              (Ebinop Oadd (Evar _a (tarray tulong 8))
                                (Econst_int (Int.repr 4) tint) (tptr tulong))
                              tulong))
                          (Scall (Some _t'4)
                            (Evar _Sigma1 (Tfunction (tulong :: nil) tulong
                                            cc_default))
                            ((Etempvar _t'30 tulong) :: nil)))
                        (Ssequence
                          (Sset _t'27
                            (Ederef
                              (Ebinop Oadd (Evar _a (tarray tulong 8))
                                (Econst_int (Int.repr 4) tint) (tptr tulong))
                              tulong))
                          (Ssequence
                            (Sset _t'28
                              (Ederef
                                (Ebinop Oadd (Evar _a (tarray tulong 8))
                                  (Econst_int (Int.repr 5) tint)
                                  (tptr tulong)) tulong))
                            (Ssequence
                              (Sset _t'29
                                (Ederef
                                  (Ebinop Oadd (Evar _a (tarray tulong 8))
                                    (Econst_int (Int.repr 6) tint)
                                    (tptr tulong)) tulong))
                              (Scall (Some _t'5)
                                (Evar _Ch (Tfunction
                                            (tulong :: tulong :: tulong ::
                                             nil) tulong cc_default))
                                ((Etempvar _t'27 tulong) ::
                                 (Etempvar _t'28 tulong) ::
                                 (Etempvar _t'29 tulong) :: nil))))))
                      (Ssequence
                        (Sset _t'24
                          (Ederef
                            (Ebinop Oadd (Evar _a (tarray tulong 8))
                              (Econst_int (Int.repr 7) tint) (tptr tulong))
                            tulong))
                        (Ssequence
                          (Sset _t'25
                            (Ederef
                              (Ebinop Oadd (Evar _K (tarray tulong 80))
                                (Etempvar _i tint) (tptr tulong)) tulong))
                          (Ssequence
                            (Sset _t'26
                              (Ederef
                                (Ebinop Oadd (Evar _w (tarray tulong 16))
                                  (Ebinop Omod (Etempvar _i tint)
                                    (Econst_int (Int.repr 16) tint) tint)
                                  (tptr tulong)) tulong))
                            (Sset _t
                              (Ebinop Oadd
                                (Ebinop Oadd
                                  (Ebinop Oadd
                                    (Ebinop Oadd (Etempvar _t'24 tulong)
                                      (Etempvar _t'4 tulong) tulong)
                                    (Etempvar _t'5 tulong) tulong)
                                  (Etempvar _t'25 tulong) tulong)
                                (Etempvar _t'26 tulong) tulong))))))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'23
                              (Ederef
                                (Ebinop Oadd (Evar _a (tarray tulong 8))
                                  (Econst_int (Int.repr 0) tint)
                                  (tptr tulong)) tulong))
                            (Scall (Some _t'6)
                              (Evar _Sigma0 (Tfunction (tulong :: nil) tulong
                                              cc_default))
                              ((Etempvar _t'23 tulong) :: nil)))
                          (Ssequence
                            (Sset _t'20
                              (Ederef
                                (Ebinop Oadd (Evar _a (tarray tulong 8))
                                  (Econst_int (Int.repr 0) tint)
                                  (tptr tulong)) tulong))
                            (Ssequence
                              (Sset _t'21
                                (Ederef
                                  (Ebinop Oadd (Evar _a (tarray tulong 8))
                                    (Econst_int (Int.repr 1) tint)
                                    (tptr tulong)) tulong))
                              (Ssequence
                                (Sset _t'22
                                  (Ederef
                                    (Ebinop Oadd (Evar _a (tarray tulong 8))
                                      (Econst_int (Int.repr 2) tint)
                                      (tptr tulong)) tulong))
                                (Scall (Some _t'7)
                                  (Evar _Maj (Tfunction
                                               (tulong :: tulong :: tulong ::
                                                nil) tulong cc_default))
                                  ((Etempvar _t'20 tulong) ::
                                   (Etempvar _t'21 tulong) ::
                                   (Etempvar _t'22 tulong) :: nil))))))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _b (tarray tulong 8))
                              (Econst_int (Int.repr 7) tint) (tptr tulong))
                            tulong)
                          (Ebinop Oadd
                            (Ebinop Oadd (Etempvar _t tulong)
                              (Etempvar _t'6 tulong) tulong)
                            (Etempvar _t'7 tulong) tulong)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'19
                            (Ederef
                              (Ebinop Oadd (Evar _b (tarray tulong 8))
                                (Econst_int (Int.repr 3) tint) (tptr tulong))
                              tulong))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _b (tarray tulong 8))
                                (Econst_int (Int.repr 3) tint) (tptr tulong))
                              tulong)
                            (Ebinop Oadd (Etempvar _t'19 tulong)
                              (Etempvar _t tulong) tulong)))
                        (Ssequence
                          (Ssequence
                            (Sset _j (Econst_int (Int.repr 0) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                               (Econst_int (Int.repr 8) tint)
                                               tint)
                                  Sskip
                                  Sbreak)
                                (Ssequence
                                  (Sset _t'18
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _b (tarray tulong 8))
                                        (Etempvar _j tint) (tptr tulong))
                                      tulong))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _a (tarray tulong 8))
                                        (Ebinop Omod
                                          (Ebinop Oadd (Etempvar _j tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint)
                                          (Econst_int (Int.repr 8) tint)
                                          tint) (tptr tulong)) tulong)
                                    (Etempvar _t'18 tulong))))
                              (Sset _j
                                (Ebinop Oadd (Etempvar _j tint)
                                  (Econst_int (Int.repr 1) tint) tint))))
                          (Sifthenelse (Ebinop Oeq
                                         (Ebinop Omod (Etempvar _i tint)
                                           (Econst_int (Int.repr 16) tint)
                                           tint)
                                         (Econst_int (Int.repr 15) tint)
                                         tint)
                            (Ssequence
                              (Sset _j (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                                 (Econst_int (Int.repr 16) tint)
                                                 tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'17
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _w (tarray tulong 16))
                                              (Ebinop Omod
                                                (Ebinop Oadd
                                                  (Etempvar _j tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint)
                                                (Econst_int (Int.repr 16) tint)
                                                tint) (tptr tulong)) tulong))
                                        (Scall (Some _t'8)
                                          (Evar _sigma0 (Tfunction
                                                          (tulong :: nil)
                                                          tulong cc_default))
                                          ((Etempvar _t'17 tulong) :: nil)))
                                      (Ssequence
                                        (Sset _t'16
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _w (tarray tulong 16))
                                              (Ebinop Omod
                                                (Ebinop Oadd
                                                  (Etempvar _j tint)
                                                  (Econst_int (Int.repr 14) tint)
                                                  tint)
                                                (Econst_int (Int.repr 16) tint)
                                                tint) (tptr tulong)) tulong))
                                        (Scall (Some _t'9)
                                          (Evar _sigma1 (Tfunction
                                                          (tulong :: nil)
                                                          tulong cc_default))
                                          ((Etempvar _t'16 tulong) :: nil))))
                                    (Ssequence
                                      (Sset _t'14
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _w (tarray tulong 16))
                                            (Etempvar _j tint) (tptr tulong))
                                          tulong))
                                      (Ssequence
                                        (Sset _t'15
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _w (tarray tulong 16))
                                              (Ebinop Omod
                                                (Ebinop Oadd
                                                  (Etempvar _j tint)
                                                  (Econst_int (Int.repr 9) tint)
                                                  tint)
                                                (Econst_int (Int.repr 16) tint)
                                                tint) (tptr tulong)) tulong))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _w (tarray tulong 16))
                                              (Etempvar _j tint)
                                              (tptr tulong)) tulong)
                                          (Ebinop Oadd
                                            (Etempvar _t'14 tulong)
                                            (Ebinop Oadd
                                              (Ebinop Oadd
                                                (Etempvar _t'15 tulong)
                                                (Etempvar _t'8 tulong)
                                                tulong)
                                              (Etempvar _t'9 tulong) tulong)
                                            tulong))))))
                                (Sset _j
                                  (Ebinop Oadd (Etempvar _j tint)
                                    (Econst_int (Int.repr 1) tint) tint))))
                            Sskip)))))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 8) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'12
                        (Ederef
                          (Ebinop Oadd (Evar _a (tarray tulong 8))
                            (Etempvar _i tint) (tptr tulong)) tulong))
                      (Ssequence
                        (Sset _t'13
                          (Ederef
                            (Ebinop Oadd (Evar _z (tarray tulong 8))
                              (Etempvar _i tint) (tptr tulong)) tulong))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _a (tarray tulong 8))
                              (Etempvar _i tint) (tptr tulong)) tulong)
                          (Ebinop Oadd (Etempvar _t'12 tulong)
                            (Etempvar _t'13 tulong) tulong))))
                    (Ssequence
                      (Sset _t'11
                        (Ederef
                          (Ebinop Oadd (Evar _a (tarray tulong 8))
                            (Etempvar _i tint) (tptr tulong)) tulong))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _z (tarray tulong 8))
                            (Etempvar _i tint) (tptr tulong)) tulong)
                        (Etempvar _t'11 tulong)))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sset _m
                (Ebinop Oadd (Etempvar _m (tptr tuchar))
                  (Econst_int (Int.repr 128) tint) (tptr tuchar)))
              (Sset _n
                (Ebinop Osub (Etempvar _n tulong)
                  (Econst_int (Int.repr 128) tint) tulong)))))))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 8) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'10
                (Ederef
                  (Ebinop Oadd (Evar _z (tarray tulong 8)) (Etempvar _i tint)
                    (tptr tulong)) tulong))
              (Scall None
                (Evar _ts64 (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                              cc_default))
                ((Ebinop Oadd (Etempvar _x (tptr tuchar))
                   (Ebinop Omul (Econst_int (Int.repr 8) tint)
                     (Etempvar _i tint) tint) (tptr tuchar)) ::
                 (Etempvar _t'10 tulong) :: nil))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Sreturn (Some (Etempvar _n tulong))))))
|}.

Definition v_iv := {|
  gvar_info := (tarray tuchar 64);
  gvar_init := (Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 9) ::
                Init_int8 (Int.repr 230) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 243) :: Init_int8 (Int.repr 188) ::
                Init_int8 (Int.repr 201) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 187) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 174) :: Init_int8 (Int.repr 133) ::
                Init_int8 (Int.repr 132) :: Init_int8 (Int.repr 202) ::
                Init_int8 (Int.repr 167) :: Init_int8 (Int.repr 59) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 243) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 254) :: Init_int8 (Int.repr 148) ::
                Init_int8 (Int.repr 248) :: Init_int8 (Int.repr 43) ::
                Init_int8 (Int.repr 165) :: Init_int8 (Int.repr 79) ::
                Init_int8 (Int.repr 245) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 29) ::
                Init_int8 (Int.repr 54) :: Init_int8 (Int.repr 241) ::
                Init_int8 (Int.repr 81) :: Init_int8 (Int.repr 14) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 127) ::
                Init_int8 (Int.repr 173) :: Init_int8 (Int.repr 230) ::
                Init_int8 (Int.repr 130) :: Init_int8 (Int.repr 209) ::
                Init_int8 (Int.repr 155) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 140) ::
                Init_int8 (Int.repr 43) :: Init_int8 (Int.repr 62) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 31) ::
                Init_int8 (Int.repr 31) :: Init_int8 (Int.repr 131) ::
                Init_int8 (Int.repr 217) :: Init_int8 (Int.repr 171) ::
                Init_int8 (Int.repr 251) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 189) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 91) :: Init_int8 (Int.repr 224) ::
                Init_int8 (Int.repr 205) :: Init_int8 (Int.repr 25) ::
                Init_int8 (Int.repr 19) :: Init_int8 (Int.repr 126) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 121) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_crypto_hash_sha512_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_m, (tptr tuchar)) ::
                (_n, tulong) :: nil);
  fn_vars := ((_h, (tarray tuchar 64)) :: (_x, (tarray tuchar 256)) :: nil);
  fn_temps := ((_i, tulong) :: (_b, tulong) :: (_t'3, tuchar) ::
               (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _b (Etempvar _n tulong))
  (Ssequence
    (Ssequence
      (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                         (Econst_int (Int.repr 64) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Evar _iv (tarray tuchar 64))
                  (Etempvar _i tulong) (tptr tuchar)) tuchar))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _h (tarray tuchar 64))
                  (Etempvar _i tulong) (tptr tuchar)) tuchar)
              (Etempvar _t'3 tuchar))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
            tulong))))
    (Ssequence
      (Scall None
        (Evar _crypto_hashblocks_sha512_tweet (Tfunction
                                                ((tptr tuchar) ::
                                                 (tptr tuchar) :: tulong ::
                                                 nil) tint cc_default))
        ((Evar _h (tarray tuchar 64)) :: (Etempvar _m (tptr tuchar)) ::
         (Etempvar _n tulong) :: nil))
      (Ssequence
        (Sset _m
          (Ebinop Oadd (Etempvar _m (tptr tuchar)) (Etempvar _n tulong)
            (tptr tuchar)))
        (Ssequence
          (Sset _n
            (Ebinop Oand (Etempvar _n tulong)
              (Econst_int (Int.repr 127) tint) tulong))
          (Ssequence
            (Sset _m
              (Ebinop Osub (Etempvar _m (tptr tuchar)) (Etempvar _n tulong)
                (tptr tuchar)))
            (Ssequence
              (Ssequence
                (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                   (Econst_int (Int.repr 256) tint) tint)
                      Sskip
                      Sbreak)
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _x (tarray tuchar 256))
                          (Etempvar _i tulong) (tptr tuchar)) tuchar)
                      (Econst_int (Int.repr 0) tint)))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tulong)
                      (Econst_int (Int.repr 1) tint) tulong))))
              (Ssequence
                (Ssequence
                  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                     (Etempvar _n tulong) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _t'2
                          (Ederef
                            (Ebinop Oadd (Etempvar _m (tptr tuchar))
                              (Etempvar _i tulong) (tptr tuchar)) tuchar))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _x (tarray tuchar 256))
                              (Etempvar _i tulong) (tptr tuchar)) tuchar)
                          (Etempvar _t'2 tuchar))))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tulong)
                        (Econst_int (Int.repr 1) tint) tulong))))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _x (tarray tuchar 256))
                        (Etempvar _n tulong) (tptr tuchar)) tuchar)
                    (Econst_int (Int.repr 128) tint))
                  (Ssequence
                    (Sset _n
                      (Ecast
                        (Ebinop Osub (Econst_int (Int.repr 256) tint)
                          (Ebinop Omul (Econst_int (Int.repr 128) tint)
                            (Ebinop Olt (Etempvar _n tulong)
                              (Econst_int (Int.repr 112) tint) tint) tint)
                          tint) tulong))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _x (tarray tuchar 256))
                            (Ebinop Osub (Etempvar _n tulong)
                              (Econst_int (Int.repr 9) tint) tulong)
                            (tptr tuchar)) tuchar)
                        (Ebinop Oshr (Etempvar _b tulong)
                          (Econst_int (Int.repr 61) tint) tulong))
                      (Ssequence
                        (Scall None
                          (Evar _ts64 (Tfunction
                                        ((tptr tuchar) :: tulong :: nil)
                                        tvoid cc_default))
                          ((Ebinop Osub
                             (Ebinop Oadd (Evar _x (tarray tuchar 256))
                               (Etempvar _n tulong) (tptr tuchar))
                             (Econst_int (Int.repr 8) tint) (tptr tuchar)) ::
                           (Ebinop Oshl (Etempvar _b tulong)
                             (Econst_int (Int.repr 3) tint) tulong) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _crypto_hashblocks_sha512_tweet (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                            ((Evar _h (tarray tuchar 64)) ::
                             (Evar _x (tarray tuchar 256)) ::
                             (Etempvar _n tulong) :: nil))
                          (Ssequence
                            (Ssequence
                              (Sset _i
                                (Ecast (Econst_int (Int.repr 0) tint) tulong))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt
                                                 (Etempvar _i tulong)
                                                 (Econst_int (Int.repr 64) tint)
                                                 tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _t'1
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _h (tarray tuchar 64))
                                          (Etempvar _i tulong) (tptr tuchar))
                                        tuchar))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _out (tptr tuchar))
                                          (Etempvar _i tulong) (tptr tuchar))
                                        tuchar) (Etempvar _t'1 tuchar))))
                                (Sset _i
                                  (Ebinop Oadd (Etempvar _i tulong)
                                    (Econst_int (Int.repr 1) tint) tulong))))
                            (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))
|}.

Definition f_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (tarray tlong 16))) ::
                (_q, (tptr (tarray tlong 16))) :: nil);
  fn_vars := ((_a, (tarray tlong 16)) :: (_b, (tarray tlong 16)) ::
              (_c, (tarray tlong 16)) :: (_d, (tarray tlong 16)) ::
              (_t, (tarray tlong 16)) :: (_e, (tarray tlong 16)) ::
              (_f, (tarray tlong 16)) :: (_g, (tarray tlong 16)) ::
              (_h, (tarray tlong 16)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _Z (Tfunction ((tptr tlong) :: (tptr tlong) :: (tptr tlong) :: nil)
               tvoid cc_default))
    ((Evar _a (tarray tlong 16)) ::
     (Ederef
       (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
         (Econst_int (Int.repr 1) tint) (tptr (tarray tlong 16)))
       (tarray tlong 16)) ::
     (Ederef
       (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
         (Econst_int (Int.repr 0) tint) (tptr (tarray tlong 16)))
       (tarray tlong 16)) :: nil))
  (Ssequence
    (Scall None
      (Evar _Z (Tfunction
                 ((tptr tlong) :: (tptr tlong) :: (tptr tlong) :: nil) tvoid
                 cc_default))
      ((Evar _t (tarray tlong 16)) ::
       (Ederef
         (Ebinop Oadd (Etempvar _q (tptr (tarray tlong 16)))
           (Econst_int (Int.repr 1) tint) (tptr (tarray tlong 16)))
         (tarray tlong 16)) ::
       (Ederef
         (Ebinop Oadd (Etempvar _q (tptr (tarray tlong 16)))
           (Econst_int (Int.repr 0) tint) (tptr (tarray tlong 16)))
         (tarray tlong 16)) :: nil))
    (Ssequence
      (Scall None
        (Evar _M (Tfunction
                   ((tptr tlong) :: (tptr tlong) :: (tptr tlong) :: nil)
                   tvoid cc_default))
        ((Evar _a (tarray tlong 16)) :: (Evar _a (tarray tlong 16)) ::
         (Evar _t (tarray tlong 16)) :: nil))
      (Ssequence
        (Scall None
          (Evar _A (Tfunction
                     ((tptr tlong) :: (tptr tlong) :: (tptr tlong) :: nil)
                     tvoid cc_default))
          ((Evar _b (tarray tlong 16)) ::
           (Ederef
             (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
               (Econst_int (Int.repr 0) tint) (tptr (tarray tlong 16)))
             (tarray tlong 16)) ::
           (Ederef
             (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
               (Econst_int (Int.repr 1) tint) (tptr (tarray tlong 16)))
             (tarray tlong 16)) :: nil))
        (Ssequence
          (Scall None
            (Evar _A (Tfunction
                       ((tptr tlong) :: (tptr tlong) :: (tptr tlong) :: nil)
                       tvoid cc_default))
            ((Evar _t (tarray tlong 16)) ::
             (Ederef
               (Ebinop Oadd (Etempvar _q (tptr (tarray tlong 16)))
                 (Econst_int (Int.repr 0) tint) (tptr (tarray tlong 16)))
               (tarray tlong 16)) ::
             (Ederef
               (Ebinop Oadd (Etempvar _q (tptr (tarray tlong 16)))
                 (Econst_int (Int.repr 1) tint) (tptr (tarray tlong 16)))
               (tarray tlong 16)) :: nil))
          (Ssequence
            (Scall None
              (Evar _M (Tfunction
                         ((tptr tlong) :: (tptr tlong) :: (tptr tlong) ::
                          nil) tvoid cc_default))
              ((Evar _b (tarray tlong 16)) :: (Evar _b (tarray tlong 16)) ::
               (Evar _t (tarray tlong 16)) :: nil))
            (Ssequence
              (Scall None
                (Evar _M (Tfunction
                           ((tptr tlong) :: (tptr tlong) :: (tptr tlong) ::
                            nil) tvoid cc_default))
                ((Evar _c (tarray tlong 16)) ::
                 (Ederef
                   (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
                     (Econst_int (Int.repr 3) tint) (tptr (tarray tlong 16)))
                   (tarray tlong 16)) ::
                 (Ederef
                   (Ebinop Oadd (Etempvar _q (tptr (tarray tlong 16)))
                     (Econst_int (Int.repr 3) tint) (tptr (tarray tlong 16)))
                   (tarray tlong 16)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _M (Tfunction
                             ((tptr tlong) :: (tptr tlong) :: (tptr tlong) ::
                              nil) tvoid cc_default))
                  ((Evar _c (tarray tlong 16)) ::
                   (Evar _c (tarray tlong 16)) ::
                   (Evar _D2 (tarray tlong 16)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _M (Tfunction
                               ((tptr tlong) :: (tptr tlong) ::
                                (tptr tlong) :: nil) tvoid cc_default))
                    ((Evar _d (tarray tlong 16)) ::
                     (Ederef
                       (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
                         (Econst_int (Int.repr 2) tint)
                         (tptr (tarray tlong 16))) (tarray tlong 16)) ::
                     (Ederef
                       (Ebinop Oadd (Etempvar _q (tptr (tarray tlong 16)))
                         (Econst_int (Int.repr 2) tint)
                         (tptr (tarray tlong 16))) (tarray tlong 16)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _A (Tfunction
                                 ((tptr tlong) :: (tptr tlong) ::
                                  (tptr tlong) :: nil) tvoid cc_default))
                      ((Evar _d (tarray tlong 16)) ::
                       (Evar _d (tarray tlong 16)) ::
                       (Evar _d (tarray tlong 16)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _Z (Tfunction
                                   ((tptr tlong) :: (tptr tlong) ::
                                    (tptr tlong) :: nil) tvoid cc_default))
                        ((Evar _e (tarray tlong 16)) ::
                         (Evar _b (tarray tlong 16)) ::
                         (Evar _a (tarray tlong 16)) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _Z (Tfunction
                                     ((tptr tlong) :: (tptr tlong) ::
                                      (tptr tlong) :: nil) tvoid cc_default))
                          ((Evar _f (tarray tlong 16)) ::
                           (Evar _d (tarray tlong 16)) ::
                           (Evar _c (tarray tlong 16)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _A (Tfunction
                                       ((tptr tlong) :: (tptr tlong) ::
                                        (tptr tlong) :: nil) tvoid
                                       cc_default))
                            ((Evar _g (tarray tlong 16)) ::
                             (Evar _d (tarray tlong 16)) ::
                             (Evar _c (tarray tlong 16)) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _A (Tfunction
                                         ((tptr tlong) :: (tptr tlong) ::
                                          (tptr tlong) :: nil) tvoid
                                         cc_default))
                              ((Evar _h (tarray tlong 16)) ::
                               (Evar _b (tarray tlong 16)) ::
                               (Evar _a (tarray tlong 16)) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _M (Tfunction
                                           ((tptr tlong) :: (tptr tlong) ::
                                            (tptr tlong) :: nil) tvoid
                                           cc_default))
                                ((Ederef
                                   (Ebinop Oadd
                                     (Etempvar _p (tptr (tarray tlong 16)))
                                     (Econst_int (Int.repr 0) tint)
                                     (tptr (tarray tlong 16)))
                                   (tarray tlong 16)) ::
                                 (Evar _e (tarray tlong 16)) ::
                                 (Evar _f (tarray tlong 16)) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _M (Tfunction
                                             ((tptr tlong) :: (tptr tlong) ::
                                              (tptr tlong) :: nil) tvoid
                                             cc_default))
                                  ((Ederef
                                     (Ebinop Oadd
                                       (Etempvar _p (tptr (tarray tlong 16)))
                                       (Econst_int (Int.repr 1) tint)
                                       (tptr (tarray tlong 16)))
                                     (tarray tlong 16)) ::
                                   (Evar _h (tarray tlong 16)) ::
                                   (Evar _g (tarray tlong 16)) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _M (Tfunction
                                               ((tptr tlong) ::
                                                (tptr tlong) ::
                                                (tptr tlong) :: nil) tvoid
                                               cc_default))
                                    ((Ederef
                                       (Ebinop Oadd
                                         (Etempvar _p (tptr (tarray tlong 16)))
                                         (Econst_int (Int.repr 2) tint)
                                         (tptr (tarray tlong 16)))
                                       (tarray tlong 16)) ::
                                     (Evar _g (tarray tlong 16)) ::
                                     (Evar _f (tarray tlong 16)) :: nil))
                                  (Scall None
                                    (Evar _M (Tfunction
                                               ((tptr tlong) ::
                                                (tptr tlong) ::
                                                (tptr tlong) :: nil) tvoid
                                               cc_default))
                                    ((Ederef
                                       (Ebinop Oadd
                                         (Etempvar _p (tptr (tarray tlong 16)))
                                         (Econst_int (Int.repr 3) tint)
                                         (tptr (tarray tlong 16)))
                                       (tarray tlong 16)) ::
                                     (Evar _e (tarray tlong 16)) ::
                                     (Evar _h (tarray tlong 16)) :: nil)))))))))))))))))))
|}.

Definition f_cswap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (tarray tlong 16))) ::
                (_q, (tptr (tarray tlong 16))) :: (_b, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 4) tint) tint)
        Sskip
        Sbreak)
      (Scall None
        (Evar _sel25519 (Tfunction
                          ((tptr tlong) :: (tptr tlong) :: tint :: nil) tvoid
                          cc_default))
        ((Ederef
           (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
             (Etempvar _i tint) (tptr (tarray tlong 16))) (tarray tlong 16)) ::
         (Ederef
           (Ebinop Oadd (Etempvar _q (tptr (tarray tlong 16)))
             (Etempvar _i tint) (tptr (tarray tlong 16))) (tarray tlong 16)) ::
         (Etempvar _b tuchar) :: nil)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_pack := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuchar)) :: (_p, (tptr (tarray tlong 16))) :: nil);
  fn_vars := ((_tx, (tarray tlong 16)) :: (_ty, (tarray tlong 16)) ::
              (_zi, (tarray tlong 16)) :: nil);
  fn_temps := ((_t'1, tuchar) :: (_t'2, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _inv25519 (Tfunction ((tptr tlong) :: (tptr tlong) :: nil) tvoid
                      cc_default))
    ((Evar _zi (tarray tlong 16)) ::
     (Ederef
       (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
         (Econst_int (Int.repr 2) tint) (tptr (tarray tlong 16)))
       (tarray tlong 16)) :: nil))
  (Ssequence
    (Scall None
      (Evar _M (Tfunction
                 ((tptr tlong) :: (tptr tlong) :: (tptr tlong) :: nil) tvoid
                 cc_default))
      ((Evar _tx (tarray tlong 16)) ::
       (Ederef
         (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
           (Econst_int (Int.repr 0) tint) (tptr (tarray tlong 16)))
         (tarray tlong 16)) :: (Evar _zi (tarray tlong 16)) :: nil))
    (Ssequence
      (Scall None
        (Evar _M (Tfunction
                   ((tptr tlong) :: (tptr tlong) :: (tptr tlong) :: nil)
                   tvoid cc_default))
        ((Evar _ty (tarray tlong 16)) ::
         (Ederef
           (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
             (Econst_int (Int.repr 1) tint) (tptr (tarray tlong 16)))
           (tarray tlong 16)) :: (Evar _zi (tarray tlong 16)) :: nil))
      (Ssequence
        (Scall None
          (Evar _pack25519 (Tfunction ((tptr tuchar) :: (tptr tlong) :: nil)
                             tvoid cc_default))
          ((Etempvar _r (tptr tuchar)) :: (Evar _ty (tarray tlong 16)) ::
           nil))
        (Ssequence
          (Scall (Some _t'1)
            (Evar _par25519 (Tfunction ((tptr tlong) :: nil) tuchar
                              cc_default))
            ((Evar _tx (tarray tlong 16)) :: nil))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _r (tptr tuchar))
                  (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _r (tptr tuchar))
                  (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar)
              (Ebinop Oxor (Etempvar _t'2 tuchar)
                (Ebinop Oshl (Etempvar _t'1 tuchar)
                  (Econst_int (Int.repr 7) tint) tint) tint))))))))
|}.

Definition f_scalarmult := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (tarray tlong 16))) ::
                (_q, (tptr (tarray tlong 16))) :: (_s, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_b, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _set25519 (Tfunction ((tptr tlong) :: (tptr tlong) :: nil) tvoid
                      cc_default))
    ((Ederef
       (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
         (Econst_int (Int.repr 0) tint) (tptr (tarray tlong 16)))
       (tarray tlong 16)) :: (Evar _gf0 (tarray tlong 16)) :: nil))
  (Ssequence
    (Scall None
      (Evar _set25519 (Tfunction ((tptr tlong) :: (tptr tlong) :: nil) tvoid
                        cc_default))
      ((Ederef
         (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
           (Econst_int (Int.repr 1) tint) (tptr (tarray tlong 16)))
         (tarray tlong 16)) :: (Evar _gf1 (tarray tlong 16)) :: nil))
    (Ssequence
      (Scall None
        (Evar _set25519 (Tfunction ((tptr tlong) :: (tptr tlong) :: nil)
                          tvoid cc_default))
        ((Ederef
           (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
             (Econst_int (Int.repr 2) tint) (tptr (tarray tlong 16)))
           (tarray tlong 16)) :: (Evar _gf1 (tarray tlong 16)) :: nil))
      (Ssequence
        (Scall None
          (Evar _set25519 (Tfunction ((tptr tlong) :: (tptr tlong) :: nil)
                            tvoid cc_default))
          ((Ederef
             (Ebinop Oadd (Etempvar _p (tptr (tarray tlong 16)))
               (Econst_int (Int.repr 3) tint) (tptr (tarray tlong 16)))
             (tarray tlong 16)) :: (Evar _gf0 (tarray tlong 16)) :: nil))
        (Ssequence
          (Sset _i (Econst_int (Int.repr 255) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                             (Econst_int (Int.repr 0) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'1
                    (Ederef
                      (Ebinop Oadd (Etempvar _s (tptr tuchar))
                        (Ebinop Odiv (Etempvar _i tint)
                          (Econst_int (Int.repr 8) tint) tint) (tptr tuchar))
                      tuchar))
                  (Sset _b
                    (Ecast
                      (Ebinop Oand
                        (Ebinop Oshr (Etempvar _t'1 tuchar)
                          (Ebinop Oand (Etempvar _i tint)
                            (Econst_int (Int.repr 7) tint) tint) tint)
                        (Econst_int (Int.repr 1) tint) tint) tuchar)))
                (Ssequence
                  (Scall None
                    (Evar _cswap (Tfunction
                                   ((tptr (tarray tlong 16)) ::
                                    (tptr (tarray tlong 16)) :: tuchar ::
                                    nil) tvoid cc_default))
                    ((Etempvar _p (tptr (tarray tlong 16))) ::
                     (Etempvar _q (tptr (tarray tlong 16))) ::
                     (Etempvar _b tuchar) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _add (Tfunction
                                   ((tptr (tarray tlong 16)) ::
                                    (tptr (tarray tlong 16)) :: nil) tvoid
                                   cc_default))
                      ((Etempvar _q (tptr (tarray tlong 16))) ::
                       (Etempvar _p (tptr (tarray tlong 16))) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _add (Tfunction
                                     ((tptr (tarray tlong 16)) ::
                                      (tptr (tarray tlong 16)) :: nil) tvoid
                                     cc_default))
                        ((Etempvar _p (tptr (tarray tlong 16))) ::
                         (Etempvar _p (tptr (tarray tlong 16))) :: nil))
                      (Scall None
                        (Evar _cswap (Tfunction
                                       ((tptr (tarray tlong 16)) ::
                                        (tptr (tarray tlong 16)) :: tuchar ::
                                        nil) tvoid cc_default))
                        ((Etempvar _p (tptr (tarray tlong 16))) ::
                         (Etempvar _q (tptr (tarray tlong 16))) ::
                         (Etempvar _b tuchar) :: nil)))))))
            (Sset _i
              (Ebinop Osub (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))))))
|}.

Definition f_scalarbase := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (tarray tlong 16))) :: (_s, (tptr tuchar)) :: nil);
  fn_vars := ((_q, (tarray (tarray tlong 16) 4)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _set25519 (Tfunction ((tptr tlong) :: (tptr tlong) :: nil) tvoid
                      cc_default))
    ((Ederef
       (Ebinop Oadd (Evar _q (tarray (tarray tlong 16) 4))
         (Econst_int (Int.repr 0) tint) (tptr (tarray tlong 16)))
       (tarray tlong 16)) :: (Evar _X (tarray tlong 16)) :: nil))
  (Ssequence
    (Scall None
      (Evar _set25519 (Tfunction ((tptr tlong) :: (tptr tlong) :: nil) tvoid
                        cc_default))
      ((Ederef
         (Ebinop Oadd (Evar _q (tarray (tarray tlong 16) 4))
           (Econst_int (Int.repr 1) tint) (tptr (tarray tlong 16)))
         (tarray tlong 16)) :: (Evar _Y (tarray tlong 16)) :: nil))
    (Ssequence
      (Scall None
        (Evar _set25519 (Tfunction ((tptr tlong) :: (tptr tlong) :: nil)
                          tvoid cc_default))
        ((Ederef
           (Ebinop Oadd (Evar _q (tarray (tarray tlong 16) 4))
             (Econst_int (Int.repr 2) tint) (tptr (tarray tlong 16)))
           (tarray tlong 16)) :: (Evar _gf1 (tarray tlong 16)) :: nil))
      (Ssequence
        (Scall None
          (Evar _M (Tfunction
                     ((tptr tlong) :: (tptr tlong) :: (tptr tlong) :: nil)
                     tvoid cc_default))
          ((Ederef
             (Ebinop Oadd (Evar _q (tarray (tarray tlong 16) 4))
               (Econst_int (Int.repr 3) tint) (tptr (tarray tlong 16)))
             (tarray tlong 16)) :: (Evar _X (tarray tlong 16)) ::
           (Evar _Y (tarray tlong 16)) :: nil))
        (Scall None
          (Evar _scalarmult (Tfunction
                              ((tptr (tarray tlong 16)) ::
                               (tptr (tarray tlong 16)) :: (tptr tuchar) ::
                               nil) tvoid cc_default))
          ((Etempvar _p (tptr (tarray tlong 16))) ::
           (Evar _q (tarray (tarray tlong 16) 4)) ::
           (Etempvar _s (tptr tuchar)) :: nil))))))
|}.

Definition f_crypto_sign_ed25519_tweet_keypair := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pk, (tptr tuchar)) :: (_sk, (tptr tuchar)) :: nil);
  fn_vars := ((_d, (tarray tuchar 64)) ::
              (_p, (tarray (tarray tlong 16) 4)) :: nil);
  fn_temps := ((_i, tint) :: (_t'4, tuchar) :: (_t'3, tuchar) ::
               (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _randombytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                         cc_default))
    ((Etempvar _sk (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _crypto_hash_sha512_tweet (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         tulong :: nil) tint cc_default))
      ((Evar _d (tarray tuchar 64)) :: (Etempvar _sk (tptr tuchar)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Evar _d (tarray tuchar 64))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _d (tarray tuchar 64))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
          (Ebinop Oand (Etempvar _t'4 tuchar)
            (Econst_int (Int.repr 248) tint) tint)))
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Ederef
              (Ebinop Oadd (Evar _d (tarray tuchar 64))
                (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _d (tarray tuchar 64))
                (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar)
            (Ebinop Oand (Etempvar _t'3 tuchar)
              (Econst_int (Int.repr 127) tint) tint)))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Evar _d (tarray tuchar 64))
                  (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _d (tarray tuchar 64))
                  (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar)
              (Ebinop Oor (Etempvar _t'2 tuchar)
                (Econst_int (Int.repr 64) tint) tint)))
          (Ssequence
            (Scall None
              (Evar _scalarbase (Tfunction
                                  ((tptr (tarray tlong 16)) ::
                                   (tptr tuchar) :: nil) tvoid cc_default))
              ((Evar _p (tarray (tarray tlong 16) 4)) ::
               (Evar _d (tarray tuchar 64)) :: nil))
            (Ssequence
              (Scall None
                (Evar _pack (Tfunction
                              ((tptr tuchar) :: (tptr (tarray tlong 16)) ::
                               nil) tvoid cc_default))
                ((Etempvar _pk (tptr tuchar)) ::
                 (Evar _p (tarray (tarray tlong 16) 4)) :: nil))
              (Ssequence
                (Ssequence
                  (Sset _i (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                     (Econst_int (Int.repr 32) tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _t'1
                          (Ederef
                            (Ebinop Oadd (Etempvar _pk (tptr tuchar))
                              (Etempvar _i tint) (tptr tuchar)) tuchar))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _sk (tptr tuchar))
                              (Ebinop Oadd (Econst_int (Int.repr 32) tint)
                                (Etempvar _i tint) tint) (tptr tuchar))
                            tuchar) (Etempvar _t'1 tuchar))))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
|}.

Definition v_L := {|
  gvar_info := (tarray tulong 32);
  gvar_init := (Init_int64 (Int64.repr 237) :: Init_int64 (Int64.repr 211) ::
                Init_int64 (Int64.repr 245) :: Init_int64 (Int64.repr 92) ::
                Init_int64 (Int64.repr 26) :: Init_int64 (Int64.repr 99) ::
                Init_int64 (Int64.repr 18) :: Init_int64 (Int64.repr 88) ::
                Init_int64 (Int64.repr 214) :: Init_int64 (Int64.repr 156) ::
                Init_int64 (Int64.repr 247) :: Init_int64 (Int64.repr 162) ::
                Init_int64 (Int64.repr 222) :: Init_int64 (Int64.repr 249) ::
                Init_int64 (Int64.repr 222) :: Init_int64 (Int64.repr 20) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 0) ::
                Init_int64 (Int64.repr 0) :: Init_int64 (Int64.repr 16) ::
                nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_modL := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuchar)) :: (_x, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_carry, tlong) :: (_i, tlong) :: (_j, tlong) ::
               (_t'16, tulong) :: (_t'15, tlong) :: (_t'14, tlong) ::
               (_t'13, tlong) :: (_t'12, tlong) :: (_t'11, tlong) ::
               (_t'10, tulong) :: (_t'9, tlong) :: (_t'8, tlong) ::
               (_t'7, tlong) :: (_t'6, tlong) :: (_t'5, tulong) ::
               (_t'4, tlong) :: (_t'3, tlong) :: (_t'2, tlong) ::
               (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 63) tint) tlong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Oge (Etempvar _i tlong)
                       (Econst_int (Int.repr 32) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _carry (Ecast (Econst_int (Int.repr 0) tint) tlong))
          (Ssequence
            (Ssequence
              (Sset _j
                (Ebinop Osub (Etempvar _i tlong)
                  (Econst_int (Int.repr 32) tint) tlong))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _j tlong)
                                 (Ebinop Osub (Etempvar _i tlong)
                                   (Econst_int (Int.repr 12) tint) tlong)
                                 tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'14
                        (Ederef
                          (Ebinop Oadd (Etempvar _x (tptr tlong))
                            (Etempvar _j tlong) (tptr tlong)) tlong))
                      (Ssequence
                        (Sset _t'15
                          (Ederef
                            (Ebinop Oadd (Etempvar _x (tptr tlong))
                              (Etempvar _i tlong) (tptr tlong)) tlong))
                        (Ssequence
                          (Sset _t'16
                            (Ederef
                              (Ebinop Oadd (Evar _L (tarray tulong 32))
                                (Ebinop Osub (Etempvar _j tlong)
                                  (Ebinop Osub (Etempvar _i tlong)
                                    (Econst_int (Int.repr 32) tint) tlong)
                                  tlong) (tptr tulong)) tulong))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Etempvar _x (tptr tlong))
                                (Etempvar _j tlong) (tptr tlong)) tlong)
                            (Ebinop Oadd (Etempvar _t'14 tlong)
                              (Ebinop Osub (Etempvar _carry tlong)
                                (Ebinop Omul
                                  (Ebinop Omul
                                    (Econst_int (Int.repr 16) tint)
                                    (Etempvar _t'15 tlong) tlong)
                                  (Etempvar _t'16 tulong) tulong) tulong)
                              tulong)))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'13
                          (Ederef
                            (Ebinop Oadd (Etempvar _x (tptr tlong))
                              (Etempvar _j tlong) (tptr tlong)) tlong))
                        (Sset _carry
                          (Ebinop Oshr
                            (Ebinop Oadd (Etempvar _t'13 tlong)
                              (Econst_int (Int.repr 128) tint) tlong)
                            (Econst_int (Int.repr 8) tint) tlong)))
                      (Ssequence
                        (Sset _t'12
                          (Ederef
                            (Ebinop Oadd (Etempvar _x (tptr tlong))
                              (Etempvar _j tlong) (tptr tlong)) tlong))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _x (tptr tlong))
                              (Etempvar _j tlong) (tptr tlong)) tlong)
                          (Ebinop Osub (Etempvar _t'12 tlong)
                            (Ebinop Oshl (Etempvar _carry tlong)
                              (Econst_int (Int.repr 8) tint) tlong) tlong))))))
                (Sset _j
                  (Ebinop Oadd (Etempvar _j tlong)
                    (Econst_int (Int.repr 1) tint) tlong))))
            (Ssequence
              (Ssequence
                (Sset _t'11
                  (Ederef
                    (Ebinop Oadd (Etempvar _x (tptr tlong))
                      (Etempvar _j tlong) (tptr tlong)) tlong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _x (tptr tlong))
                      (Etempvar _j tlong) (tptr tlong)) tlong)
                  (Ebinop Oadd (Etempvar _t'11 tlong) (Etempvar _carry tlong)
                    tlong)))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _x (tptr tlong)) (Etempvar _i tlong)
                    (tptr tlong)) tlong) (Econst_int (Int.repr 0) tint))))))
      (Sset _i
        (Ebinop Osub (Etempvar _i tlong) (Econst_int (Int.repr 1) tint)
          tlong))))
  (Ssequence
    (Sset _carry (Ecast (Econst_int (Int.repr 0) tint) tlong))
    (Ssequence
      (Ssequence
        (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tlong))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _j tlong)
                           (Econst_int (Int.repr 32) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _t'8
                  (Ederef
                    (Ebinop Oadd (Etempvar _x (tptr tlong))
                      (Etempvar _j tlong) (tptr tlong)) tlong))
                (Ssequence
                  (Sset _t'9
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tlong))
                        (Econst_int (Int.repr 31) tint) (tptr tlong)) tlong))
                  (Ssequence
                    (Sset _t'10
                      (Ederef
                        (Ebinop Oadd (Evar _L (tarray tulong 32))
                          (Etempvar _j tlong) (tptr tulong)) tulong))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _x (tptr tlong))
                          (Etempvar _j tlong) (tptr tlong)) tlong)
                      (Ebinop Oadd (Etempvar _t'8 tlong)
                        (Ebinop Osub (Etempvar _carry tlong)
                          (Ebinop Omul
                            (Ebinop Oshr (Etempvar _t'9 tlong)
                              (Econst_int (Int.repr 4) tint) tlong)
                            (Etempvar _t'10 tulong) tulong) tulong) tulong)))))
              (Ssequence
                (Ssequence
                  (Sset _t'7
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tlong))
                        (Etempvar _j tlong) (tptr tlong)) tlong))
                  (Sset _carry
                    (Ebinop Oshr (Etempvar _t'7 tlong)
                      (Econst_int (Int.repr 8) tint) tlong)))
                (Ssequence
                  (Sset _t'6
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tlong))
                        (Etempvar _j tlong) (tptr tlong)) tlong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tlong))
                        (Etempvar _j tlong) (tptr tlong)) tlong)
                    (Ebinop Oand (Etempvar _t'6 tlong)
                      (Econst_int (Int.repr 255) tint) tlong))))))
          (Sset _j
            (Ebinop Oadd (Etempvar _j tlong) (Econst_int (Int.repr 1) tint)
              tlong))))
      (Ssequence
        (Ssequence
          (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tlong))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _j tlong)
                             (Econst_int (Int.repr 32) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'4
                  (Ederef
                    (Ebinop Oadd (Etempvar _x (tptr tlong))
                      (Etempvar _j tlong) (tptr tlong)) tlong))
                (Ssequence
                  (Sset _t'5
                    (Ederef
                      (Ebinop Oadd (Evar _L (tarray tulong 32))
                        (Etempvar _j tlong) (tptr tulong)) tulong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tlong))
                        (Etempvar _j tlong) (tptr tlong)) tlong)
                    (Ebinop Osub (Etempvar _t'4 tlong)
                      (Ebinop Omul (Etempvar _carry tlong)
                        (Etempvar _t'5 tulong) tulong) tulong)))))
            (Sset _j
              (Ebinop Oadd (Etempvar _j tlong) (Econst_int (Int.repr 1) tint)
                tlong))))
        (Ssequence
          (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                             (Econst_int (Int.repr 32) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tlong))
                        (Ebinop Oadd (Etempvar _i tlong)
                          (Econst_int (Int.repr 1) tint) tlong) (tptr tlong))
                      tlong))
                  (Ssequence
                    (Sset _t'3
                      (Ederef
                        (Ebinop Oadd (Etempvar _x (tptr tlong))
                          (Etempvar _i tlong) (tptr tlong)) tlong))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _x (tptr tlong))
                          (Ebinop Oadd (Etempvar _i tlong)
                            (Econst_int (Int.repr 1) tint) tlong)
                          (tptr tlong)) tlong)
                      (Ebinop Oadd (Etempvar _t'2 tlong)
                        (Ebinop Oshr (Etempvar _t'3 tlong)
                          (Econst_int (Int.repr 8) tint) tlong) tlong))))
                (Ssequence
                  (Sset _t'1
                    (Ederef
                      (Ebinop Oadd (Etempvar _x (tptr tlong))
                        (Etempvar _i tlong) (tptr tlong)) tlong))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _r (tptr tuchar))
                        (Etempvar _i tlong) (tptr tuchar)) tuchar)
                    (Ebinop Oand (Etempvar _t'1 tlong)
                      (Econst_int (Int.repr 255) tint) tlong)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tlong) (Econst_int (Int.repr 1) tint)
                tlong))))))))
|}.

Definition f_reduce := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuchar)) :: nil);
  fn_vars := ((_x, (tarray tlong 64)) :: nil);
  fn_temps := ((_i, tlong) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                       (Econst_int (Int.repr 64) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _r (tptr tuchar)) (Etempvar _i tlong)
                (tptr tuchar)) tuchar))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _x (tarray tlong 64)) (Etempvar _i tlong)
                (tptr tlong)) tlong) (Ecast (Etempvar _t'1 tuchar) tulong))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tlong) (Econst_int (Int.repr 1) tint)
          tlong))))
  (Ssequence
    (Ssequence
      (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                         (Econst_int (Int.repr 64) tint) tint)
            Sskip
            Sbreak)
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _r (tptr tuchar)) (Etempvar _i tlong)
                (tptr tuchar)) tuchar) (Econst_int (Int.repr 0) tint)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tlong) (Econst_int (Int.repr 1) tint)
            tlong))))
    (Scall None
      (Evar _modL (Tfunction ((tptr tuchar) :: (tptr tlong) :: nil) tvoid
                    cc_default))
      ((Etempvar _r (tptr tuchar)) :: (Evar _x (tarray tlong 64)) :: nil))))
|}.

Definition f_crypto_sign_ed25519_tweet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_sm, (tptr tuchar)) :: (_smlen, (tptr tulong)) ::
                (_m, (tptr tuchar)) :: (_n, tulong) ::
                (_sk, (tptr tuchar)) :: nil);
  fn_vars := ((_d, (tarray tuchar 64)) :: (_h, (tarray tuchar 64)) ::
              (_r, (tarray tuchar 64)) :: (_x, (tarray tlong 64)) ::
              (_p, (tarray (tarray tlong 16) 4)) :: nil);
  fn_temps := ((_i, tlong) :: (_j, tlong) :: (_t'10, tuchar) ::
               (_t'9, tuchar) :: (_t'8, tuchar) :: (_t'7, tuchar) ::
               (_t'6, tuchar) :: (_t'5, tuchar) :: (_t'4, tuchar) ::
               (_t'3, tuchar) :: (_t'2, tuchar) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _crypto_hash_sha512_tweet (Tfunction
                                      ((tptr tuchar) :: (tptr tuchar) ::
                                       tulong :: nil) tint cc_default))
    ((Evar _d (tarray tuchar 64)) :: (Etempvar _sk (tptr tuchar)) ::
     (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Ssequence
      (Sset _t'10
        (Ederef
          (Ebinop Oadd (Evar _d (tarray tuchar 64))
            (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _d (tarray tuchar 64))
            (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
        (Ebinop Oand (Etempvar _t'10 tuchar) (Econst_int (Int.repr 248) tint)
          tint)))
    (Ssequence
      (Ssequence
        (Sset _t'9
          (Ederef
            (Ebinop Oadd (Evar _d (tarray tuchar 64))
              (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar))
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _d (tarray tuchar 64))
              (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar)
          (Ebinop Oand (Etempvar _t'9 tuchar)
            (Econst_int (Int.repr 127) tint) tint)))
      (Ssequence
        (Ssequence
          (Sset _t'8
            (Ederef
              (Ebinop Oadd (Evar _d (tarray tuchar 64))
                (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _d (tarray tuchar 64))
                (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar)
            (Ebinop Oor (Etempvar _t'8 tuchar)
              (Econst_int (Int.repr 64) tint) tint)))
        (Ssequence
          (Sassign (Ederef (Etempvar _smlen (tptr tulong)) tulong)
            (Ebinop Oadd (Etempvar _n tulong) (Econst_int (Int.repr 64) tint)
              tulong))
          (Ssequence
            (Ssequence
              (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                                 (Etempvar _n tulong) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _t'7
                      (Ederef
                        (Ebinop Oadd (Etempvar _m (tptr tuchar))
                          (Etempvar _i tlong) (tptr tuchar)) tuchar))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Etempvar _sm (tptr tuchar))
                          (Ebinop Oadd (Econst_int (Int.repr 64) tint)
                            (Etempvar _i tlong) tlong) (tptr tuchar)) tuchar)
                      (Etempvar _t'7 tuchar))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tlong)
                    (Econst_int (Int.repr 1) tint) tlong))))
            (Ssequence
              (Ssequence
                (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                                   (Econst_int (Int.repr 32) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _t'6
                        (Ederef
                          (Ebinop Oadd (Evar _d (tarray tuchar 64))
                            (Ebinop Oadd (Econst_int (Int.repr 32) tint)
                              (Etempvar _i tlong) tlong) (tptr tuchar))
                          tuchar))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _sm (tptr tuchar))
                            (Ebinop Oadd (Econst_int (Int.repr 32) tint)
                              (Etempvar _i tlong) tlong) (tptr tuchar))
                          tuchar) (Etempvar _t'6 tuchar))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tlong)
                      (Econst_int (Int.repr 1) tint) tlong))))
              (Ssequence
                (Scall None
                  (Evar _crypto_hash_sha512_tweet (Tfunction
                                                    ((tptr tuchar) ::
                                                     (tptr tuchar) ::
                                                     tulong :: nil) tint
                                                    cc_default))
                  ((Evar _r (tarray tuchar 64)) ::
                   (Ebinop Oadd (Etempvar _sm (tptr tuchar))
                     (Econst_int (Int.repr 32) tint) (tptr tuchar)) ::
                   (Ebinop Oadd (Etempvar _n tulong)
                     (Econst_int (Int.repr 32) tint) tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _reduce (Tfunction ((tptr tuchar) :: nil) tvoid
                                    cc_default))
                    ((Evar _r (tarray tuchar 64)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _scalarbase (Tfunction
                                          ((tptr (tarray tlong 16)) ::
                                           (tptr tuchar) :: nil) tvoid
                                          cc_default))
                      ((Evar _p (tarray (tarray tlong 16) 4)) ::
                       (Evar _r (tarray tuchar 64)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _pack (Tfunction
                                      ((tptr tuchar) ::
                                       (tptr (tarray tlong 16)) :: nil) tvoid
                                      cc_default))
                        ((Etempvar _sm (tptr tuchar)) ::
                         (Evar _p (tarray (tarray tlong 16) 4)) :: nil))
                      (Ssequence
                        (Ssequence
                          (Sset _i
                            (Ecast (Econst_int (Int.repr 0) tint) tlong))
                          (Sloop
                            (Ssequence
                              (Sifthenelse (Ebinop Olt (Etempvar _i tlong)
                                             (Econst_int (Int.repr 32) tint)
                                             tint)
                                Sskip
                                Sbreak)
                              (Ssequence
                                (Sset _t'5
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _sk (tptr tuchar))
                                      (Ebinop Oadd (Etempvar _i tlong)
                                        (Econst_int (Int.repr 32) tint)
                                        tlong) (tptr tuchar)) tuchar))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Etempvar _sm (tptr tuchar))
                                      (Ebinop Oadd (Etempvar _i tlong)
                                        (Econst_int (Int.repr 32) tint)
                                        tlong) (tptr tuchar)) tuchar)
                                  (Etempvar _t'5 tuchar))))
                            (Sset _i
                              (Ebinop Oadd (Etempvar _i tlong)
                                (Econst_int (Int.repr 1) tint) tlong))))
                        (Ssequence
                          (Scall None
                            (Evar _crypto_hash_sha512_tweet (Tfunction
                                                              ((tptr tuchar) ::
                                                               (tptr tuchar) ::
                                                               tulong :: nil)
                                                              tint
                                                              cc_default))
                            ((Evar _h (tarray tuchar 64)) ::
                             (Etempvar _sm (tptr tuchar)) ::
                             (Ebinop Oadd (Etempvar _n tulong)
                               (Econst_int (Int.repr 64) tint) tulong) ::
                             nil))
                          (Ssequence
                            (Scall None
                              (Evar _reduce (Tfunction ((tptr tuchar) :: nil)
                                              tvoid cc_default))
                              ((Evar _h (tarray tuchar 64)) :: nil))
                            (Ssequence
                              (Ssequence
                                (Sset _i
                                  (Ecast (Econst_int (Int.repr 0) tint)
                                    tlong))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _i tlong)
                                                   (Econst_int (Int.repr 64) tint)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _x (tarray tlong 64))
                                          (Etempvar _i tlong) (tptr tlong))
                                        tlong)
                                      (Econst_int (Int.repr 0) tint)))
                                  (Sset _i
                                    (Ebinop Oadd (Etempvar _i tlong)
                                      (Econst_int (Int.repr 1) tint) tlong))))
                              (Ssequence
                                (Ssequence
                                  (Sset _i
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      tlong))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i tlong)
                                                     (Econst_int (Int.repr 32) tint)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Sset _t'4
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _r (tarray tuchar 64))
                                              (Etempvar _i tlong)
                                              (tptr tuchar)) tuchar))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _x (tarray tlong 64))
                                              (Etempvar _i tlong)
                                              (tptr tlong)) tlong)
                                          (Ecast (Etempvar _t'4 tuchar)
                                            tulong))))
                                    (Sset _i
                                      (Ebinop Oadd (Etempvar _i tlong)
                                        (Econst_int (Int.repr 1) tint) tlong))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _i
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        tlong))
                                    (Sloop
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _i tlong)
                                                       (Econst_int (Int.repr 32) tint)
                                                       tint)
                                          Sskip
                                          Sbreak)
                                        (Ssequence
                                          (Sset _j
                                            (Ecast
                                              (Econst_int (Int.repr 0) tint)
                                              tlong))
                                          (Sloop
                                            (Ssequence
                                              (Sifthenelse (Ebinop Olt
                                                             (Etempvar _j tlong)
                                                             (Econst_int (Int.repr 32) tint)
                                                             tint)
                                                Sskip
                                                Sbreak)
                                              (Ssequence
                                                (Sset _t'1
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _x (tarray tlong 64))
                                                      (Ebinop Oadd
                                                        (Etempvar _i tlong)
                                                        (Etempvar _j tlong)
                                                        tlong) (tptr tlong))
                                                    tlong))
                                                (Ssequence
                                                  (Sset _t'2
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _h (tarray tuchar 64))
                                                        (Etempvar _i tlong)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Ssequence
                                                    (Sset _t'3
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _d (tarray tuchar 64))
                                                          (Etempvar _j tlong)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _x (tarray tlong 64))
                                                          (Ebinop Oadd
                                                            (Etempvar _i tlong)
                                                            (Etempvar _j tlong)
                                                            tlong)
                                                          (tptr tlong))
                                                        tlong)
                                                      (Ebinop Oadd
                                                        (Etempvar _t'1 tlong)
                                                        (Ebinop Omul
                                                          (Etempvar _t'2 tuchar)
                                                          (Ecast
                                                            (Etempvar _t'3 tuchar)
                                                            tulong) tulong)
                                                        tulong))))))
                                            (Sset _j
                                              (Ebinop Oadd
                                                (Etempvar _j tlong)
                                                (Econst_int (Int.repr 1) tint)
                                                tlong)))))
                                      (Sset _i
                                        (Ebinop Oadd (Etempvar _i tlong)
                                          (Econst_int (Int.repr 1) tint)
                                          tlong))))
                                  (Ssequence
                                    (Scall None
                                      (Evar _modL (Tfunction
                                                    ((tptr tuchar) ::
                                                     (tptr tlong) :: nil)
                                                    tvoid cc_default))
                                      ((Ebinop Oadd
                                         (Etempvar _sm (tptr tuchar))
                                         (Econst_int (Int.repr 32) tint)
                                         (tptr tuchar)) ::
                                       (Evar _x (tarray tlong 64)) :: nil))
                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))
|}.

Definition f_unpackneg := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr (tarray tlong 16))) :: (_p, (tptr tuchar)) :: nil);
  fn_vars := ((_t, (tarray tlong 16)) :: (_chk, (tarray tlong 16)) ::
              (_num, (tarray tlong 16)) :: (_den, (tarray tlong 16)) ::
              (_den2, (tarray tlong 16)) :: (_den4, (tarray tlong 16)) ::
              (_den6, (tarray tlong 16)) :: nil);
  fn_temps := ((_t'3, tuchar) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'4, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _set25519 (Tfunction ((tptr tlong) :: (tptr tlong) :: nil) tvoid
                      cc_default))
    ((Ederef
       (Ebinop Oadd (Etempvar _r (tptr (tarray tlong 16)))
         (Econst_int (Int.repr 2) tint) (tptr (tarray tlong 16)))
       (tarray tlong 16)) :: (Evar _gf1 (tarray tlong 16)) :: nil))
  (Ssequence
    (Scall None
      (Evar _unpack25519 (Tfunction ((tptr tlong) :: (tptr tuchar) :: nil)
                           tvoid cc_default))
      ((Ederef
         (Ebinop Oadd (Etempvar _r (tptr (tarray tlong 16)))
           (Econst_int (Int.repr 1) tint) (tptr (tarray tlong 16)))
         (tarray tlong 16)) :: (Etempvar _p (tptr tuchar)) :: nil))
    (Ssequence
      (Scall None
        (Evar _S (Tfunction ((tptr tlong) :: (tptr tlong) :: nil) tvoid
                   cc_default))
        ((Evar _num (tarray tlong 16)) ::
         (Ederef
           (Ebinop Oadd (Etempvar _r (tptr (tarray tlong 16)))
             (Econst_int (Int.repr 1) tint) (tptr (tarray tlong 16)))
           (tarray tlong 16)) :: nil))
      (Ssequence
        (Scall None
          (Evar _M (Tfunction
                     ((tptr tlong) :: (tptr tlong) :: (tptr tlong) :: nil)
                     tvoid cc_default))
          ((Evar _den (tarray tlong 16)) :: (Evar _num (tarray tlong 16)) ::
           (Evar _D (tarray tlong 16)) :: nil))
        (Ssequence
          (Scall None
            (Evar _Z (Tfunction
                       ((tptr tlong) :: (tptr tlong) :: (tptr tlong) :: nil)
                       tvoid cc_default))
            ((Evar _num (tarray tlong 16)) ::
             (Evar _num (tarray tlong 16)) ::
             (Ederef
               (Ebinop Oadd (Etempvar _r (tptr (tarray tlong 16)))
                 (Econst_int (Int.repr 2) tint) (tptr (tarray tlong 16)))
               (tarray tlong 16)) :: nil))
          (Ssequence
            (Scall None
              (Evar _A (Tfunction
                         ((tptr tlong) :: (tptr tlong) :: (tptr tlong) ::
                          nil) tvoid cc_default))
              ((Evar _den (tarray tlong 16)) ::
               (Ederef
                 (Ebinop Oadd (Etempvar _r (tptr (tarray tlong 16)))
                   (Econst_int (Int.repr 2) tint) (tptr (tarray tlong 16)))
                 (tarray tlong 16)) :: (Evar _den (tarray tlong 16)) :: nil))
            (Ssequence
              (Scall None
                (Evar _S (Tfunction ((tptr tlong) :: (tptr tlong) :: nil)
                           tvoid cc_default))
                ((Evar _den2 (tarray tlong 16)) ::
                 (Evar _den (tarray tlong 16)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _S (Tfunction ((tptr tlong) :: (tptr tlong) :: nil)
                             tvoid cc_default))
                  ((Evar _den4 (tarray tlong 16)) ::
                   (Evar _den2 (tarray tlong 16)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _M (Tfunction
                               ((tptr tlong) :: (tptr tlong) ::
                                (tptr tlong) :: nil) tvoid cc_default))
                    ((Evar _den6 (tarray tlong 16)) ::
                     (Evar _den4 (tarray tlong 16)) ::
                     (Evar _den2 (tarray tlong 16)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _M (Tfunction
                                 ((tptr tlong) :: (tptr tlong) ::
                                  (tptr tlong) :: nil) tvoid cc_default))
                      ((Evar _t (tarray tlong 16)) ::
                       (Evar _den6 (tarray tlong 16)) ::
                       (Evar _num (tarray tlong 16)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _M (Tfunction
                                   ((tptr tlong) :: (tptr tlong) ::
                                    (tptr tlong) :: nil) tvoid cc_default))
                        ((Evar _t (tarray tlong 16)) ::
                         (Evar _t (tarray tlong 16)) ::
                         (Evar _den (tarray tlong 16)) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _pow2523 (Tfunction
                                           ((tptr tlong) :: (tptr tlong) ::
                                            nil) tvoid cc_default))
                          ((Evar _t (tarray tlong 16)) ::
                           (Evar _t (tarray tlong 16)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _M (Tfunction
                                       ((tptr tlong) :: (tptr tlong) ::
                                        (tptr tlong) :: nil) tvoid
                                       cc_default))
                            ((Evar _t (tarray tlong 16)) ::
                             (Evar _t (tarray tlong 16)) ::
                             (Evar _num (tarray tlong 16)) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _M (Tfunction
                                         ((tptr tlong) :: (tptr tlong) ::
                                          (tptr tlong) :: nil) tvoid
                                         cc_default))
                              ((Evar _t (tarray tlong 16)) ::
                               (Evar _t (tarray tlong 16)) ::
                               (Evar _den (tarray tlong 16)) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _M (Tfunction
                                           ((tptr tlong) :: (tptr tlong) ::
                                            (tptr tlong) :: nil) tvoid
                                           cc_default))
                                ((Evar _t (tarray tlong 16)) ::
                                 (Evar _t (tarray tlong 16)) ::
                                 (Evar _den (tarray tlong 16)) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _M (Tfunction
                                             ((tptr tlong) :: (tptr tlong) ::
                                              (tptr tlong) :: nil) tvoid
                                             cc_default))
                                  ((Ederef
                                     (Ebinop Oadd
                                       (Etempvar _r (tptr (tarray tlong 16)))
                                       (Econst_int (Int.repr 0) tint)
                                       (tptr (tarray tlong 16)))
                                     (tarray tlong 16)) ::
                                   (Evar _t (tarray tlong 16)) ::
                                   (Evar _den (tarray tlong 16)) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _S (Tfunction
                                               ((tptr tlong) ::
                                                (tptr tlong) :: nil) tvoid
                                               cc_default))
                                    ((Evar _chk (tarray tlong 16)) ::
                                     (Ederef
                                       (Ebinop Oadd
                                         (Etempvar _r (tptr (tarray tlong 16)))
                                         (Econst_int (Int.repr 0) tint)
                                         (tptr (tarray tlong 16)))
                                       (tarray tlong 16)) :: nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _M (Tfunction
                                                 ((tptr tlong) ::
                                                  (tptr tlong) ::
                                                  (tptr tlong) :: nil) tvoid
                                                 cc_default))
                                      ((Evar _chk (tarray tlong 16)) ::
                                       (Evar _chk (tarray tlong 16)) ::
                                       (Evar _den (tarray tlong 16)) :: nil))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'1)
                                          (Evar _neq25519 (Tfunction
                                                            ((tptr tlong) ::
                                                             (tptr tlong) ::
                                                             nil) tint
                                                            cc_default))
                                          ((Evar _chk (tarray tlong 16)) ::
                                           (Evar _num (tarray tlong 16)) ::
                                           nil))
                                        (Sifthenelse (Etempvar _t'1 tint)
                                          (Scall None
                                            (Evar _M (Tfunction
                                                       ((tptr tlong) ::
                                                        (tptr tlong) ::
                                                        (tptr tlong) :: nil)
                                                       tvoid cc_default))
                                            ((Ederef
                                               (Ebinop Oadd
                                                 (Etempvar _r (tptr (tarray tlong 16)))
                                                 (Econst_int (Int.repr 0) tint)
                                                 (tptr (tarray tlong 16)))
                                               (tarray tlong 16)) ::
                                             (Ederef
                                               (Ebinop Oadd
                                                 (Etempvar _r (tptr (tarray tlong 16)))
                                                 (Econst_int (Int.repr 0) tint)
                                                 (tptr (tarray tlong 16)))
                                               (tarray tlong 16)) ::
                                             (Evar _I (tarray tlong 16)) ::
                                             nil))
                                          Sskip))
                                      (Ssequence
                                        (Scall None
                                          (Evar _S (Tfunction
                                                     ((tptr tlong) ::
                                                      (tptr tlong) :: nil)
                                                     tvoid cc_default))
                                          ((Evar _chk (tarray tlong 16)) ::
                                           (Ederef
                                             (Ebinop Oadd
                                               (Etempvar _r (tptr (tarray tlong 16)))
                                               (Econst_int (Int.repr 0) tint)
                                               (tptr (tarray tlong 16)))
                                             (tarray tlong 16)) :: nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _M (Tfunction
                                                       ((tptr tlong) ::
                                                        (tptr tlong) ::
                                                        (tptr tlong) :: nil)
                                                       tvoid cc_default))
                                            ((Evar _chk (tarray tlong 16)) ::
                                             (Evar _chk (tarray tlong 16)) ::
                                             (Evar _den (tarray tlong 16)) ::
                                             nil))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'2)
                                                (Evar _neq25519 (Tfunction
                                                                  ((tptr tlong) ::
                                                                   (tptr tlong) ::
                                                                   nil) tint
                                                                  cc_default))
                                                ((Evar _chk (tarray tlong 16)) ::
                                                 (Evar _num (tarray tlong 16)) ::
                                                 nil))
                                              (Sifthenelse (Etempvar _t'2 tint)
                                                (Sreturn (Some (Eunop Oneg
                                                                 (Econst_int (Int.repr 1) tint)
                                                                 tint)))
                                                Sskip))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'3)
                                                  (Evar _par25519 (Tfunction
                                                                    ((tptr tlong) ::
                                                                    nil)
                                                                    tuchar
                                                                    cc_default))
                                                  ((Ederef
                                                     (Ebinop Oadd
                                                       (Etempvar _r (tptr (tarray tlong 16)))
                                                       (Econst_int (Int.repr 0) tint)
                                                       (tptr (tarray tlong 16)))
                                                     (tarray tlong 16)) ::
                                                   nil))
                                                (Ssequence
                                                  (Sset _t'4
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _p (tptr tuchar))
                                                        (Econst_int (Int.repr 31) tint)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Sifthenelse (Ebinop Oeq
                                                                 (Etempvar _t'3 tuchar)
                                                                 (Ebinop Oshr
                                                                   (Etempvar _t'4 tuchar)
                                                                   (Econst_int (Int.repr 7) tint)
                                                                   tint)
                                                                 tint)
                                                    (Scall None
                                                      (Evar _Z (Tfunction
                                                                 ((tptr tlong) ::
                                                                  (tptr tlong) ::
                                                                  (tptr tlong) ::
                                                                  nil) tvoid
                                                                 cc_default))
                                                      ((Ederef
                                                         (Ebinop Oadd
                                                           (Etempvar _r (tptr (tarray tlong 16)))
                                                           (Econst_int (Int.repr 0) tint)
                                                           (tptr (tarray tlong 16)))
                                                         (tarray tlong 16)) ::
                                                       (Evar _gf0 (tarray tlong 16)) ::
                                                       (Ederef
                                                         (Ebinop Oadd
                                                           (Etempvar _r (tptr (tarray tlong 16)))
                                                           (Econst_int (Int.repr 0) tint)
                                                           (tptr (tarray tlong 16)))
                                                         (tarray tlong 16)) ::
                                                       nil))
                                                    Sskip)))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _M (Tfunction
                                                             ((tptr tlong) ::
                                                              (tptr tlong) ::
                                                              (tptr tlong) ::
                                                              nil) tvoid
                                                             cc_default))
                                                  ((Ederef
                                                     (Ebinop Oadd
                                                       (Etempvar _r (tptr (tarray tlong 16)))
                                                       (Econst_int (Int.repr 3) tint)
                                                       (tptr (tarray tlong 16)))
                                                     (tarray tlong 16)) ::
                                                   (Ederef
                                                     (Ebinop Oadd
                                                       (Etempvar _r (tptr (tarray tlong 16)))
                                                       (Econst_int (Int.repr 0) tint)
                                                       (tptr (tarray tlong 16)))
                                                     (tarray tlong 16)) ::
                                                   (Ederef
                                                     (Ebinop Oadd
                                                       (Etempvar _r (tptr (tarray tlong 16)))
                                                       (Econst_int (Int.repr 1) tint)
                                                       (tptr (tarray tlong 16)))
                                                     (tarray tlong 16)) ::
                                                   nil))
                                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))
|}.

Definition f_crypto_sign_ed25519_tweet_open := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr tuchar)) :: (_mlen, (tptr tulong)) ::
                (_sm, (tptr tuchar)) :: (_n, tulong) ::
                (_pk, (tptr tuchar)) :: nil);
  fn_vars := ((_t, (tarray tuchar 32)) :: (_h, (tarray tuchar 64)) ::
              (_p, (tarray (tarray tlong 16) 4)) ::
              (_q, (tarray (tarray tlong 16) 4)) :: nil);
  fn_temps := ((_i, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'5, tuchar) :: (_t'4, tuchar) :: (_t'3, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Ederef (Etempvar _mlen (tptr tulong)) tulong)
    (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
  (Ssequence
    (Sifthenelse (Ebinop Olt (Etempvar _n tulong)
                   (Econst_int (Int.repr 64) tint) tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _unpackneg (Tfunction
                             ((tptr (tarray tlong 16)) :: (tptr tuchar) ::
                              nil) tint cc_default))
          ((Evar _q (tarray (tarray tlong 16) 4)) ::
           (Etempvar _pk (tptr tuchar)) :: nil))
        (Sifthenelse (Etempvar _t'1 tint)
          (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
          Sskip))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Etempvar _n tulong) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'5
                  (Ederef
                    (Ebinop Oadd (Etempvar _sm (tptr tuchar))
                      (Etempvar _i tint) (tptr tuchar)) tuchar))
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _m (tptr tuchar))
                      (Etempvar _i tint) (tptr tuchar)) tuchar)
                  (Etempvar _t'5 tuchar))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 32) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _t'4
                    (Ederef
                      (Ebinop Oadd (Etempvar _pk (tptr tuchar))
                        (Etempvar _i tint) (tptr tuchar)) tuchar))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _m (tptr tuchar))
                        (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 32) tint) tint)
                        (tptr tuchar)) tuchar) (Etempvar _t'4 tuchar))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Scall None
              (Evar _crypto_hash_sha512_tweet (Tfunction
                                                ((tptr tuchar) ::
                                                 (tptr tuchar) :: tulong ::
                                                 nil) tint cc_default))
              ((Evar _h (tarray tuchar 64)) :: (Etempvar _m (tptr tuchar)) ::
               (Etempvar _n tulong) :: nil))
            (Ssequence
              (Scall None
                (Evar _reduce (Tfunction ((tptr tuchar) :: nil) tvoid
                                cc_default))
                ((Evar _h (tarray tuchar 64)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _scalarmult (Tfunction
                                      ((tptr (tarray tlong 16)) ::
                                       (tptr (tarray tlong 16)) ::
                                       (tptr tuchar) :: nil) tvoid
                                      cc_default))
                  ((Evar _p (tarray (tarray tlong 16) 4)) ::
                   (Evar _q (tarray (tarray tlong 16) 4)) ::
                   (Evar _h (tarray tuchar 64)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _scalarbase (Tfunction
                                        ((tptr (tarray tlong 16)) ::
                                         (tptr tuchar) :: nil) tvoid
                                        cc_default))
                    ((Evar _q (tarray (tarray tlong 16) 4)) ::
                     (Ebinop Oadd (Etempvar _sm (tptr tuchar))
                       (Econst_int (Int.repr 32) tint) (tptr tuchar)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _add (Tfunction
                                   ((tptr (tarray tlong 16)) ::
                                    (tptr (tarray tlong 16)) :: nil) tvoid
                                   cc_default))
                      ((Evar _p (tarray (tarray tlong 16) 4)) ::
                       (Evar _q (tarray (tarray tlong 16) 4)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _pack (Tfunction
                                      ((tptr tuchar) ::
                                       (tptr (tarray tlong 16)) :: nil) tvoid
                                      cc_default))
                        ((Evar _t (tarray tuchar 32)) ::
                         (Evar _p (tarray (tarray tlong 16) 4)) :: nil))
                      (Ssequence
                        (Sset _n
                          (Ebinop Osub (Etempvar _n tulong)
                            (Econst_int (Int.repr 64) tint) tulong))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'2)
                              (Evar _crypto_verify_32_tweet (Tfunction
                                                              ((tptr tuchar) ::
                                                               (tptr tuchar) ::
                                                               nil) tint
                                                              cc_default))
                              ((Etempvar _sm (tptr tuchar)) ::
                               (Evar _t (tarray tuchar 32)) :: nil))
                            (Sifthenelse (Etempvar _t'2 tint)
                              (Ssequence
                                (Ssequence
                                  (Sset _i (Econst_int (Int.repr 0) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i tint)
                                                     (Etempvar _n tulong)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _m (tptr tuchar))
                                            (Etempvar _i tint) (tptr tuchar))
                                          tuchar)
                                        (Econst_int (Int.repr 0) tint)))
                                    (Sset _i
                                      (Ebinop Oadd (Etempvar _i tint)
                                        (Econst_int (Int.repr 1) tint) tint))))
                                (Sreturn (Some (Eunop Oneg
                                                 (Econst_int (Int.repr 1) tint)
                                                 tint))))
                              Sskip))
                          (Ssequence
                            (Ssequence
                              (Sset _i (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                                 (Etempvar _n tulong) tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _t'3
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _sm (tptr tuchar))
                                          (Ebinop Oadd (Etempvar _i tint)
                                            (Econst_int (Int.repr 64) tint)
                                            tint) (tptr tuchar)) tuchar))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _m (tptr tuchar))
                                          (Etempvar _i tint) (tptr tuchar))
                                        tuchar) (Etempvar _t'3 tuchar))))
                                (Sset _i
                                  (Ebinop Oadd (Etempvar _i tint)
                                    (Econst_int (Int.repr 1) tint) tint))))
                            (Ssequence
                              (Sassign
                                (Ederef (Etempvar _mlen (tptr tulong))
                                  tulong) (Etempvar _n tulong))
                              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tuint :: nil) (tptr tvoid)
     cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xint :: AST.Xint :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tuint :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xint :: AST.Xint :: nil) AST.Xint
                     cc_default)) (tint :: tint :: nil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_randombytes,
   Gfun(External (EF_external "randombytes"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tuchar) :: tulong :: nil) tvoid
     cc_default)) :: (__0, Gvar v__0) :: (__9, Gvar v__9) ::
 (_gf0, Gvar v_gf0) :: (_gf1, Gvar v_gf1) :: (__121665, Gvar v__121665) ::
 (_D, Gvar v_D) :: (_D2, Gvar v_D2) :: (_X, Gvar v_X) :: (_Y, Gvar v_Y) ::
 (_I, Gvar v_I) :: (_L32, Gfun(Internal f_L32)) ::
 (_ld32, Gfun(Internal f_ld32)) :: (_dl64, Gfun(Internal f_dl64)) ::
 (_st32, Gfun(Internal f_st32)) :: (_ts64, Gfun(Internal f_ts64)) ::
 (_vn, Gfun(Internal f_vn)) ::
 (_crypto_verify_16_tweet, Gfun(Internal f_crypto_verify_16_tweet)) ::
 (_crypto_verify_32_tweet, Gfun(Internal f_crypto_verify_32_tweet)) ::
 (_core, Gfun(Internal f_core)) ::
 (_crypto_core_salsa20_tweet, Gfun(Internal f_crypto_core_salsa20_tweet)) ::
 (_crypto_core_hsalsa20_tweet, Gfun(Internal f_crypto_core_hsalsa20_tweet)) ::
 (_sigma, Gvar v_sigma) ::
 (_crypto_stream_salsa20_tweet_xor, Gfun(Internal f_crypto_stream_salsa20_tweet_xor)) ::
 (_crypto_stream_salsa20_tweet, Gfun(Internal f_crypto_stream_salsa20_tweet)) ::
 (_crypto_stream_xsalsa20_tweet, Gfun(Internal f_crypto_stream_xsalsa20_tweet)) ::
 (_crypto_stream_xsalsa20_tweet_xor, Gfun(Internal f_crypto_stream_xsalsa20_tweet_xor)) ::
 (_add1305, Gfun(Internal f_add1305)) :: (_minusp, Gvar v_minusp) ::
 (_crypto_onetimeauth_poly1305_tweet, Gfun(Internal f_crypto_onetimeauth_poly1305_tweet)) ::
 (_crypto_onetimeauth_poly1305_tweet_verify, Gfun(Internal f_crypto_onetimeauth_poly1305_tweet_verify)) ::
 (_crypto_secretbox_xsalsa20poly1305_tweet, Gfun(Internal f_crypto_secretbox_xsalsa20poly1305_tweet)) ::
 (_crypto_secretbox_xsalsa20poly1305_tweet_open, Gfun(Internal f_crypto_secretbox_xsalsa20poly1305_tweet_open)) ::
 (_set25519, Gfun(Internal f_set25519)) ::
 (_car25519, Gfun(Internal f_car25519)) ::
 (_sel25519, Gfun(Internal f_sel25519)) ::
 (_pack25519, Gfun(Internal f_pack25519)) ::
 (_neq25519, Gfun(Internal f_neq25519)) ::
 (_par25519, Gfun(Internal f_par25519)) ::
 (_unpack25519, Gfun(Internal f_unpack25519)) :: (_A, Gfun(Internal f_A)) ::
 (_Z, Gfun(Internal f_Z)) :: (_M, Gfun(Internal f_M)) ::
 (_S, Gfun(Internal f_S)) :: (_inv25519, Gfun(Internal f_inv25519)) ::
 (_pow2523, Gfun(Internal f_pow2523)) ::
 (_crypto_scalarmult_curve25519_tweet, Gfun(Internal f_crypto_scalarmult_curve25519_tweet)) ::
 (_crypto_scalarmult_curve25519_tweet_base, Gfun(Internal f_crypto_scalarmult_curve25519_tweet_base)) ::
 (_crypto_box_curve25519xsalsa20poly1305_tweet_keypair, Gfun(Internal f_crypto_box_curve25519xsalsa20poly1305_tweet_keypair)) ::
 (_crypto_box_curve25519xsalsa20poly1305_tweet_beforenm, Gfun(Internal f_crypto_box_curve25519xsalsa20poly1305_tweet_beforenm)) ::
 (_crypto_box_curve25519xsalsa20poly1305_tweet_afternm, Gfun(Internal f_crypto_box_curve25519xsalsa20poly1305_tweet_afternm)) ::
 (_crypto_box_curve25519xsalsa20poly1305_tweet_open_afternm, Gfun(Internal f_crypto_box_curve25519xsalsa20poly1305_tweet_open_afternm)) ::
 (_crypto_box_curve25519xsalsa20poly1305_tweet, Gfun(Internal f_crypto_box_curve25519xsalsa20poly1305_tweet)) ::
 (_crypto_box_curve25519xsalsa20poly1305_tweet_open, Gfun(Internal f_crypto_box_curve25519xsalsa20poly1305_tweet_open)) ::
 (_R, Gfun(Internal f_R)) :: (_Ch, Gfun(Internal f_Ch)) ::
 (_Maj, Gfun(Internal f_Maj)) :: (_Sigma0, Gfun(Internal f_Sigma0)) ::
 (_Sigma1, Gfun(Internal f_Sigma1)) :: (_sigma0, Gfun(Internal f_sigma0)) ::
 (_sigma1, Gfun(Internal f_sigma1)) :: (_K, Gvar v_K) ::
 (_crypto_hashblocks_sha512_tweet, Gfun(Internal f_crypto_hashblocks_sha512_tweet)) ::
 (_iv, Gvar v_iv) ::
 (_crypto_hash_sha512_tweet, Gfun(Internal f_crypto_hash_sha512_tweet)) ::
 (_add, Gfun(Internal f_add)) :: (_cswap, Gfun(Internal f_cswap)) ::
 (_pack, Gfun(Internal f_pack)) ::
 (_scalarmult, Gfun(Internal f_scalarmult)) ::
 (_scalarbase, Gfun(Internal f_scalarbase)) ::
 (_crypto_sign_ed25519_tweet_keypair, Gfun(Internal f_crypto_sign_ed25519_tweet_keypair)) ::
 (_L, Gvar v_L) :: (_modL, Gfun(Internal f_modL)) ::
 (_reduce, Gfun(Internal f_reduce)) ::
 (_crypto_sign_ed25519_tweet, Gfun(Internal f_crypto_sign_ed25519_tweet)) ::
 (_unpackneg, Gfun(Internal f_unpackneg)) ::
 (_crypto_sign_ed25519_tweet_open, Gfun(Internal f_crypto_sign_ed25519_tweet_open)) ::
 nil).

Definition public_idents : list ident :=
(_crypto_sign_ed25519_tweet_open :: _crypto_sign_ed25519_tweet ::
 _crypto_sign_ed25519_tweet_keypair :: _crypto_hash_sha512_tweet ::
 _crypto_hashblocks_sha512_tweet ::
 _crypto_box_curve25519xsalsa20poly1305_tweet_open ::
 _crypto_box_curve25519xsalsa20poly1305_tweet ::
 _crypto_box_curve25519xsalsa20poly1305_tweet_open_afternm ::
 _crypto_box_curve25519xsalsa20poly1305_tweet_afternm ::
 _crypto_box_curve25519xsalsa20poly1305_tweet_beforenm ::
 _crypto_box_curve25519xsalsa20poly1305_tweet_keypair ::
 _crypto_scalarmult_curve25519_tweet_base ::
 _crypto_scalarmult_curve25519_tweet ::
 _crypto_secretbox_xsalsa20poly1305_tweet_open ::
 _crypto_secretbox_xsalsa20poly1305_tweet ::
 _crypto_onetimeauth_poly1305_tweet_verify ::
 _crypto_onetimeauth_poly1305_tweet :: _crypto_stream_xsalsa20_tweet_xor ::
 _crypto_stream_xsalsa20_tweet :: _crypto_stream_salsa20_tweet ::
 _crypto_stream_salsa20_tweet_xor :: _crypto_core_hsalsa20_tweet ::
 _crypto_core_salsa20_tweet :: _crypto_verify_32_tweet ::
 _crypto_verify_16_tweet :: _randombytes :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


