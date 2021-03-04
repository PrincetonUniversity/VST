From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Module Info.
  Definition version := "3.8".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "32sse2".
  Definition abi := "standard".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "aes/mbedtls/library/aes.c".
  Definition normalized := false.
End Info.

Definition _FSb : ident := $"FSb".
Definition _FT0 : ident := $"FT0".
Definition _FT1 : ident := $"FT1".
Definition _FT2 : ident := $"FT2".
Definition _FT3 : ident := $"FT3".
Definition _RCON : ident := $"RCON".
Definition _RK : ident := $"RK".
Definition _RSb : ident := $"RSb".
Definition _RT0 : ident := $"RT0".
Definition _RT1 : ident := $"RT1".
Definition _RT2 : ident := $"RT2".
Definition _RT3 : ident := $"RT3".
Definition _SK : ident := $"SK".
Definition _X0 : ident := $"X0".
Definition _X1 : ident := $"X1".
Definition _X2 : ident := $"X2".
Definition _X3 : ident := $"X3".
Definition _Y0 : ident := $"Y0".
Definition _Y1 : ident := $"Y1".
Definition _Y2 : ident := $"Y2".
Definition _Y3 : ident := $"Y3".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition ___stringlit_5 : ident := $"__stringlit_5".
Definition ___stringlit_6 : ident := $"__stringlit_6".
Definition _aes_gen_tables : ident := $"aes_gen_tables".
Definition _aes_init_done : ident := $"aes_init_done".
Definition _aes_tables_struct : ident := $"aes_tables_struct".
Definition _aes_test_ecb_dec : ident := $"aes_test_ecb_dec".
Definition _aes_test_ecb_enc : ident := $"aes_test_ecb_enc".
Definition _b0 : ident := $"b0".
Definition _b0__1 : ident := $"b0__1".
Definition _b0__2 : ident := $"b0__2".
Definition _b0__3 : ident := $"b0__3".
Definition _b0__4 : ident := $"b0__4".
Definition _b0__5 : ident := $"b0__5".
Definition _b0__6 : ident := $"b0__6".
Definition _b0__7 : ident := $"b0__7".
Definition _b1 : ident := $"b1".
Definition _b1__1 : ident := $"b1__1".
Definition _b1__2 : ident := $"b1__2".
Definition _b1__3 : ident := $"b1__3".
Definition _b1__4 : ident := $"b1__4".
Definition _b1__5 : ident := $"b1__5".
Definition _b1__6 : ident := $"b1__6".
Definition _b1__7 : ident := $"b1__7".
Definition _b2 : ident := $"b2".
Definition _b2__1 : ident := $"b2__1".
Definition _b2__2 : ident := $"b2__2".
Definition _b2__3 : ident := $"b2__3".
Definition _b2__4 : ident := $"b2__4".
Definition _b2__5 : ident := $"b2__5".
Definition _b2__6 : ident := $"b2__6".
Definition _b2__7 : ident := $"b2__7".
Definition _b3 : ident := $"b3".
Definition _b3__1 : ident := $"b3__1".
Definition _b3__2 : ident := $"b3__2".
Definition _b3__3 : ident := $"b3__3".
Definition _b3__4 : ident := $"b3__4".
Definition _b3__5 : ident := $"b3__5".
Definition _b3__6 : ident := $"b3__6".
Definition _b3__7 : ident := $"b3__7".
Definition _buf : ident := $"buf".
Definition _ctx : ident := $"ctx".
Definition _cty : ident := $"cty".
Definition _exit : ident := $"exit".
Definition _i : ident := $"i".
Definition _input : ident := $"input".
Definition _iv : ident := $"iv".
Definition _j : ident := $"j".
Definition _key : ident := $"key".
Definition _key_word : ident := $"key_word".
Definition _keybits : ident := $"keybits".
Definition _log : ident := $"log".
Definition _logi : ident := $"logi".
Definition _logx : ident := $"logx".
Definition _logx__1 : ident := $"logx__1".
Definition _logx__2 : ident := $"logx__2".
Definition _logx__3 : ident := $"logx__3".
Definition _logy : ident := $"logy".
Definition _logy__1 : ident := $"logy__1".
Definition _logy__2 : ident := $"logy__2".
Definition _logy__3 : ident := $"logy__3".
Definition _m : ident := $"m".
Definition _m__1 : ident := $"m__1".
Definition _m__2 : ident := $"m__2".
Definition _m__3 : ident := $"m__3".
Definition _main : ident := $"main".
Definition _mbedtls_aes_context_struct : ident := $"mbedtls_aes_context_struct".
Definition _mbedtls_aes_crypt_ecb : ident := $"mbedtls_aes_crypt_ecb".
Definition _mbedtls_aes_decrypt : ident := $"mbedtls_aes_decrypt".
Definition _mbedtls_aes_encrypt : ident := $"mbedtls_aes_encrypt".
Definition _mbedtls_aes_free : ident := $"mbedtls_aes_free".
Definition _mbedtls_aes_init : ident := $"mbedtls_aes_init".
Definition _mbedtls_aes_self_test : ident := $"mbedtls_aes_self_test".
Definition _mbedtls_aes_setkey_dec : ident := $"mbedtls_aes_setkey_dec".
Definition _mbedtls_aes_setkey_enc : ident := $"mbedtls_aes_setkey_enc".
Definition _mbedtls_zeroize : ident := $"mbedtls_zeroize".
Definition _memcmp : ident := $"memcmp".
Definition _memset : ident := $"memset".
Definition _mode : ident := $"mode".
Definition _n : ident := $"n".
Definition _nr : ident := $"nr".
Definition _output : ident := $"output".
Definition _p : ident := $"p".
Definition _pow : ident := $"pow".
Definition _printf : ident := $"printf".
Definition _prod1 : ident := $"prod1".
Definition _prod2 : ident := $"prod2".
Definition _prod3 : ident := $"prod3".
Definition _prod4 : ident := $"prod4".
Definition _rcon : ident := $"rcon".
Definition _ret : ident := $"ret".
Definition _rk : ident := $"rk".
Definition _rk0 : ident := $"rk0".
Definition _rk7 : ident := $"rk7".
Definition _rk__1 : ident := $"rk__1".
Definition _rk__2 : ident := $"rk__2".
Definition _rk__3 : ident := $"rk__3".
Definition _rot : ident := $"rot".
Definition _sk : ident := $"sk".
Definition _tables : ident := $"tables".
Definition _tmp : ident := $"tmp".
Definition _u : ident := $"u".
Definition _v : ident := $"v".
Definition _verbose : ident := $"verbose".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _z : ident := $"z".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 21);
  gvar_init := (Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 69) ::
                Init_int8 (Int.repr 83) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_6 := {|
  gvar_info := (tarray tschar 2);
  gvar_init := (Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 8);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_mbedtls_zeroize := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr tvoid)) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tuchar)) :: (_t'2, (tptr tuchar)) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _p (Etempvar _v (tptr tvoid)))
  (Sloop
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'1 (Etempvar _n tuint))
          (Sset _n
            (Ebinop Osub (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
              tuint)))
        (Sifthenelse (Etempvar _t'1 tuint) Sskip Sbreak))
      (Ssequence
        (Ssequence
          (Sset _t'2 (Etempvar _p (tptr tuchar)))
          (Sset _p
            (Ebinop Oadd (Etempvar _t'2 (tptr tuchar))
              (Econst_int (Int.repr 1) tint) (tptr tuchar))))
        (Sassign (Ederef (Etempvar _t'2 (tptr tuchar)) tuchar)
          (Econst_int (Int.repr 0) tint))))
    Sskip))
|}.

Definition v_tables := {|
  gvar_info := (Tstruct _aes_tables_struct noattr);
  gvar_init := (Init_space 8744 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_aes_init_done := {|
  gvar_info := tint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_aes_gen_tables := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_pow, (tarray tint 256)) :: (_log, (tarray tint 256)) :: nil);
  fn_temps := ((_i, tint) :: (_x, tint) :: (_y, tint) :: (_z, tint) ::
               (_rot, tuint) :: (_logi, tint) :: (_prod1, tint) ::
               (_prod2, tint) :: (_prod3, tint) :: (_prod4, tint) ::
               (_logx, tint) :: (_logy, tint) :: (_m, tint) ::
               (_logx__1, tint) :: (_logy__1, tint) :: (_m__1, tint) ::
               (_logx__2, tint) :: (_logy__2, tint) :: (_m__2, tint) ::
               (_logx__3, tint) :: (_logy__3, tint) :: (_m__3, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sset _x (Econst_int (Int.repr 1) tint)))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 256) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _pow (tarray tint 256)) (Etempvar _i tint)
                (tptr tint)) tint) (Etempvar _x tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _log (tarray tint 256)) (Etempvar _x tint)
                  (tptr tint)) tint) (Etempvar _i tint))
            (Ssequence
              (Sifthenelse (Ebinop Oand (Etempvar _x tint)
                             (Econst_int (Int.repr 128) tint) tint)
                (Sset _t'1 (Ecast (Econst_int (Int.repr 27) tint) tint))
                (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tint)))
              (Sset _x
                (Ebinop Oand
                  (Ebinop Oxor (Etempvar _x tint)
                    (Ebinop Oxor
                      (Ebinop Oshl (Etempvar _x tint)
                        (Econst_int (Int.repr 1) tint) tint)
                      (Etempvar _t'1 tint) tint) tint)
                  (Econst_int (Int.repr 255) tint) tint))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sset _x (Econst_int (Int.repr 1) tint)))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 10) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield (Evar _tables (Tstruct _aes_tables_struct noattr))
                    _RCON (tarray tuint 10)) (Etempvar _i tint) (tptr tuint))
                tuint) (Ecast (Etempvar _x tint) tuint))
            (Ssequence
              (Sifthenelse (Ebinop Oand (Etempvar _x tint)
                             (Econst_int (Int.repr 128) tint) tint)
                (Sset _t'2 (Ecast (Econst_int (Int.repr 27) tint) tint))
                (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tint)))
              (Sset _x
                (Ebinop Oand
                  (Ebinop Oxor
                    (Ebinop Oshl (Etempvar _x tint)
                      (Econst_int (Int.repr 1) tint) tint)
                    (Etempvar _t'2 tint) tint)
                  (Econst_int (Int.repr 255) tint) tint)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield (Evar _tables (Tstruct _aes_tables_struct noattr)) _FSb
              (tarray tuchar 256)) (Econst_int (Int.repr 0) tint)
            (tptr tuchar)) tuchar) (Econst_int (Int.repr 99) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield (Evar _tables (Tstruct _aes_tables_struct noattr)) _RSb
                (tarray tuchar 256)) (Econst_int (Int.repr 99) tint)
              (tptr tuchar)) tuchar) (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 1) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 256) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _logi
                    (Ederef
                      (Ebinop Oadd (Evar _log (tarray tint 256))
                        (Etempvar _i tint) (tptr tint)) tint))
                  (Ssequence
                    (Sset _x
                      (Ederef
                        (Ebinop Oadd (Evar _pow (tarray tint 256))
                          (Ebinop Osub (Econst_int (Int.repr 255) tint)
                            (Etempvar _logi tint) tint) (tptr tint)) tint))
                    (Ssequence
                      (Sset _y (Etempvar _x tint))
                      (Ssequence
                        (Sset _y
                          (Ebinop Oand
                            (Ebinop Oor
                              (Ebinop Oshl (Etempvar _y tint)
                                (Econst_int (Int.repr 1) tint) tint)
                              (Ebinop Oshr (Etempvar _y tint)
                                (Econst_int (Int.repr 7) tint) tint) tint)
                            (Econst_int (Int.repr 255) tint) tint))
                        (Ssequence
                          (Sset _x
                            (Ebinop Oxor (Etempvar _x tint)
                              (Etempvar _y tint) tint))
                          (Ssequence
                            (Sset _y
                              (Ebinop Oand
                                (Ebinop Oor
                                  (Ebinop Oshl (Etempvar _y tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  (Ebinop Oshr (Etempvar _y tint)
                                    (Econst_int (Int.repr 7) tint) tint)
                                  tint) (Econst_int (Int.repr 255) tint)
                                tint))
                            (Ssequence
                              (Sset _x
                                (Ebinop Oxor (Etempvar _x tint)
                                  (Etempvar _y tint) tint))
                              (Ssequence
                                (Sset _y
                                  (Ebinop Oand
                                    (Ebinop Oor
                                      (Ebinop Oshl (Etempvar _y tint)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      (Ebinop Oshr (Etempvar _y tint)
                                        (Econst_int (Int.repr 7) tint) tint)
                                      tint) (Econst_int (Int.repr 255) tint)
                                    tint))
                                (Ssequence
                                  (Sset _x
                                    (Ebinop Oxor (Etempvar _x tint)
                                      (Etempvar _y tint) tint))
                                  (Ssequence
                                    (Sset _y
                                      (Ebinop Oand
                                        (Ebinop Oor
                                          (Ebinop Oshl (Etempvar _y tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint)
                                          (Ebinop Oshr (Etempvar _y tint)
                                            (Econst_int (Int.repr 7) tint)
                                            tint) tint)
                                        (Econst_int (Int.repr 255) tint)
                                        tint))
                                    (Ssequence
                                      (Sset _x
                                        (Ebinop Oxor (Etempvar _x tint)
                                          (Ebinop Oxor (Etempvar _y tint)
                                            (Econst_int (Int.repr 99) tint)
                                            tint) tint))
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                _FSb (tarray tuchar 256))
                                              (Etempvar _i tint)
                                              (tptr tuchar)) tuchar)
                                          (Ecast (Etempvar _x tint) tuchar))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                _RSb (tarray tuchar 256))
                                              (Etempvar _x tint)
                                              (tptr tuchar)) tuchar)
                                          (Ecast (Etempvar _i tint) tuchar)))))))))))))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 256) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _x
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Evar _tables (Tstruct _aes_tables_struct noattr))
                          _FSb (tarray tuchar 256)) (Etempvar _i tint)
                        (tptr tuchar)) tuchar))
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Ebinop Oand (Etempvar _x tint)
                                     (Econst_int (Int.repr 128) tint) tint)
                        (Sset _t'3
                          (Ecast (Econst_int (Int.repr 27) tint) tint))
                        (Sset _t'3
                          (Ecast (Econst_int (Int.repr 0) tint) tint)))
                      (Sset _y
                        (Ebinop Oand
                          (Ebinop Oxor
                            (Ebinop Oshl (Etempvar _x tint)
                              (Econst_int (Int.repr 1) tint) tint)
                            (Etempvar _t'3 tint) tint)
                          (Econst_int (Int.repr 255) tint) tint)))
                    (Ssequence
                      (Sset _z
                        (Ebinop Oand
                          (Ebinop Oxor (Etempvar _y tint) (Etempvar _x tint)
                            tint) (Econst_int (Int.repr 255) tint) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                _FT0 (tarray tuint 256)) (Etempvar _i tint)
                              (tptr tuint)) tuint)
                          (Ebinop Oxor
                            (Ebinop Oxor
                              (Ebinop Oxor (Ecast (Etempvar _y tint) tuint)
                                (Ebinop Oshl (Ecast (Etempvar _x tint) tuint)
                                  (Econst_int (Int.repr 8) tint) tuint)
                                tuint)
                              (Ebinop Oshl (Ecast (Etempvar _x tint) tuint)
                                (Econst_int (Int.repr 16) tint) tuint) tuint)
                            (Ebinop Oshl (Ecast (Etempvar _z tint) tuint)
                              (Econst_int (Int.repr 24) tint) tuint) tuint))
                        (Ssequence
                          (Sset _rot
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                  _FT0 (tarray tuint 256)) (Etempvar _i tint)
                                (tptr tuint)) tuint))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                    _FT1 (tarray tuint 256))
                                  (Etempvar _i tint) (tptr tuint)) tuint)
                              (Ebinop Oor
                                (Ebinop Oand
                                  (Ebinop Oshl (Etempvar _rot tuint)
                                    (Econst_int (Int.repr 8) tint) tuint)
                                  (Econst_int (Int.repr (-1)) tuint) tuint)
                                (Ebinop Oshr (Etempvar _rot tuint)
                                  (Econst_int (Int.repr 24) tint) tuint)
                                tuint))
                            (Ssequence
                              (Sset _rot
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Evar _tables (Tstruct _aes_tables_struct noattr))
                                      _FT1 (tarray tuint 256))
                                    (Etempvar _i tint) (tptr tuint)) tuint))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Evar _tables (Tstruct _aes_tables_struct noattr))
                                        _FT2 (tarray tuint 256))
                                      (Etempvar _i tint) (tptr tuint)) tuint)
                                  (Ebinop Oor
                                    (Ebinop Oand
                                      (Ebinop Oshl (Etempvar _rot tuint)
                                        (Econst_int (Int.repr 8) tint) tuint)
                                      (Econst_int (Int.repr (-1)) tuint)
                                      tuint)
                                    (Ebinop Oshr (Etempvar _rot tuint)
                                      (Econst_int (Int.repr 24) tint) tuint)
                                    tuint))
                                (Ssequence
                                  (Sset _rot
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Evar _tables (Tstruct _aes_tables_struct noattr))
                                          _FT2 (tarray tuint 256))
                                        (Etempvar _i tint) (tptr tuint))
                                      tuint))
                                  (Ssequence
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Evar _tables (Tstruct _aes_tables_struct noattr))
                                            _FT3 (tarray tuint 256))
                                          (Etempvar _i tint) (tptr tuint))
                                        tuint)
                                      (Ebinop Oor
                                        (Ebinop Oand
                                          (Ebinop Oshl (Etempvar _rot tuint)
                                            (Econst_int (Int.repr 8) tint)
                                            tuint)
                                          (Econst_int (Int.repr (-1)) tuint)
                                          tuint)
                                        (Ebinop Oshr (Etempvar _rot tuint)
                                          (Econst_int (Int.repr 24) tint)
                                          tuint) tuint))
                                    (Ssequence
                                      (Sset _x
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                              _RSb (tarray tuchar 256))
                                            (Etempvar _i tint) (tptr tuchar))
                                          tuchar))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'4
                                            (Ecast (Etempvar _x tint) tbool))
                                          (Sifthenelse (Etempvar _t'4 tint)
                                            (Ssequence
                                              (Sset _logx
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _log (tarray tint 256))
                                                    (Econst_int (Int.repr 14) tint)
                                                    (tptr tint)) tint))
                                              (Ssequence
                                                (Sset _logy
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _log (tarray tint 256))
                                                      (Etempvar _x tint)
                                                      (tptr tint)) tint))
                                                (Ssequence
                                                  (Sset _m
                                                    (Ebinop Omod
                                                      (Ebinop Oadd
                                                        (Etempvar _logx tint)
                                                        (Etempvar _logy tint)
                                                        tint)
                                                      (Econst_int (Int.repr 255) tint)
                                                      tint))
                                                  (Sset _prod1
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _pow (tarray tint 256))
                                                        (Etempvar _m tint)
                                                        (tptr tint)) tint)))))
                                            (Sset _prod1
                                              (Econst_int (Int.repr 0) tint))))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'5
                                              (Ecast (Etempvar _x tint)
                                                tbool))
                                            (Sifthenelse (Etempvar _t'5 tint)
                                              (Ssequence
                                                (Sset _logx__1
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _log (tarray tint 256))
                                                      (Econst_int (Int.repr 9) tint)
                                                      (tptr tint)) tint))
                                                (Ssequence
                                                  (Sset _logy__1
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _log (tarray tint 256))
                                                        (Etempvar _x tint)
                                                        (tptr tint)) tint))
                                                  (Ssequence
                                                    (Sset _m__1
                                                      (Ebinop Omod
                                                        (Ebinop Oadd
                                                          (Etempvar _logx__1 tint)
                                                          (Etempvar _logy__1 tint)
                                                          tint)
                                                        (Econst_int (Int.repr 255) tint)
                                                        tint))
                                                    (Sset _prod2
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _pow (tarray tint 256))
                                                          (Etempvar _m__1 tint)
                                                          (tptr tint)) tint)))))
                                              (Sset _prod2
                                                (Econst_int (Int.repr 0) tint))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'6
                                                (Ecast (Etempvar _x tint)
                                                  tbool))
                                              (Sifthenelse (Etempvar _t'6 tint)
                                                (Ssequence
                                                  (Sset _logx__2
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _log (tarray tint 256))
                                                        (Econst_int (Int.repr 13) tint)
                                                        (tptr tint)) tint))
                                                  (Ssequence
                                                    (Sset _logy__2
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _log (tarray tint 256))
                                                          (Etempvar _x tint)
                                                          (tptr tint)) tint))
                                                    (Ssequence
                                                      (Sset _m__2
                                                        (Ebinop Omod
                                                          (Ebinop Oadd
                                                            (Etempvar _logx__2 tint)
                                                            (Etempvar _logy__2 tint)
                                                            tint)
                                                          (Econst_int (Int.repr 255) tint)
                                                          tint))
                                                      (Sset _prod3
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _pow (tarray tint 256))
                                                            (Etempvar _m__2 tint)
                                                            (tptr tint))
                                                          tint)))))
                                                (Sset _prod3
                                                  (Econst_int (Int.repr 0) tint))))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'7
                                                  (Ecast (Etempvar _x tint)
                                                    tbool))
                                                (Sifthenelse (Etempvar _t'7 tint)
                                                  (Ssequence
                                                    (Sset _logx__3
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _log (tarray tint 256))
                                                          (Econst_int (Int.repr 11) tint)
                                                          (tptr tint)) tint))
                                                    (Ssequence
                                                      (Sset _logy__3
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _log (tarray tint 256))
                                                            (Etempvar _x tint)
                                                            (tptr tint))
                                                          tint))
                                                      (Ssequence
                                                        (Sset _m__3
                                                          (Ebinop Omod
                                                            (Ebinop Oadd
                                                              (Etempvar _logx__3 tint)
                                                              (Etempvar _logy__3 tint)
                                                              tint)
                                                            (Econst_int (Int.repr 255) tint)
                                                            tint))
                                                        (Sset _prod4
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _pow (tarray tint 256))
                                                              (Etempvar _m__3 tint)
                                                              (tptr tint))
                                                            tint)))))
                                                  (Sset _prod4
                                                    (Econst_int (Int.repr 0) tint))))
                                              (Ssequence
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                        _RT0
                                                        (tarray tuint 256))
                                                      (Etempvar _i tint)
                                                      (tptr tuint)) tuint)
                                                  (Ebinop Oxor
                                                    (Ebinop Oxor
                                                      (Ebinop Oxor
                                                        (Ecast
                                                          (Etempvar _prod1 tint)
                                                          tuint)
                                                        (Ebinop Oshl
                                                          (Ecast
                                                            (Etempvar _prod2 tint)
                                                            tuint)
                                                          (Econst_int (Int.repr 8) tint)
                                                          tuint) tuint)
                                                      (Ebinop Oshl
                                                        (Ecast
                                                          (Etempvar _prod3 tint)
                                                          tuint)
                                                        (Econst_int (Int.repr 16) tint)
                                                        tuint) tuint)
                                                    (Ebinop Oshl
                                                      (Ecast
                                                        (Etempvar _prod4 tint)
                                                        tuint)
                                                      (Econst_int (Int.repr 24) tint)
                                                      tuint) tuint))
                                                (Ssequence
                                                  (Sset _rot
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                          _RT0
                                                          (tarray tuint 256))
                                                        (Etempvar _i tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                            _RT1
                                                            (tarray tuint 256))
                                                          (Etempvar _i tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Ebinop Oor
                                                        (Ebinop Oand
                                                          (Ebinop Oshl
                                                            (Etempvar _rot tuint)
                                                            (Econst_int (Int.repr 8) tint)
                                                            tuint)
                                                          (Econst_int (Int.repr (-1)) tuint)
                                                          tuint)
                                                        (Ebinop Oshr
                                                          (Etempvar _rot tuint)
                                                          (Econst_int (Int.repr 24) tint)
                                                          tuint) tuint))
                                                    (Ssequence
                                                      (Sset _rot
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                              _RT1
                                                              (tarray tuint 256))
                                                            (Etempvar _i tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                _RT2
                                                                (tarray tuint 256))
                                                              (Etempvar _i tint)
                                                              (tptr tuint))
                                                            tuint)
                                                          (Ebinop Oor
                                                            (Ebinop Oand
                                                              (Ebinop Oshl
                                                                (Etempvar _rot tuint)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tuint)
                                                              (Econst_int (Int.repr (-1)) tuint)
                                                              tuint)
                                                            (Ebinop Oshr
                                                              (Etempvar _rot tuint)
                                                              (Econst_int (Int.repr 24) tint)
                                                              tuint) tuint))
                                                        (Ssequence
                                                          (Sset _rot
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                  _RT2
                                                                  (tarray tuint 256))
                                                                (Etempvar _i tint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                  _RT3
                                                                  (tarray tuint 256))
                                                                (Etempvar _i tint)
                                                                (tptr tuint))
                                                              tuint)
                                                            (Ebinop Oor
                                                              (Ebinop Oand
                                                                (Ebinop Oshl
                                                                  (Etempvar _rot tuint)
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  tuint)
                                                                (Econst_int (Int.repr (-1)) tuint)
                                                                tuint)
                                                              (Ebinop Oshr
                                                                (Etempvar _rot tuint)
                                                                (Econst_int (Int.repr 24) tint)
                                                                tuint) tuint))))))))))))))))))))))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint)))))))))
|}.

Definition f_mbedtls_aes_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction
                  (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                  (tptr tvoid) cc_default))
  ((Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
   (Econst_int (Int.repr 0) tint) ::
   (Esizeof (Tstruct _mbedtls_aes_context_struct noattr) tuint) :: nil))
|}.

Definition f_mbedtls_aes_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Scall None
    (Evar _mbedtls_zeroize (Tfunction (Tcons (tptr tvoid) (Tcons tuint Tnil))
                             tvoid cc_default))
    ((Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
     (Esizeof (Tstruct _mbedtls_aes_context_struct noattr) tuint) :: nil)))
|}.

Definition f_mbedtls_aes_setkey_enc := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                (_key, (tptr tuchar)) :: (_keybits, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_key_word, tuint) :: (_RK, (tptr tuint)) ::
               (_tmp, tint) :: (_b0, tuint) :: (_b1, tuint) ::
               (_b2, tuint) :: (_b3, tuint) :: (_rk0, tuint) ::
               (_rk7, tuint) :: (_rcon, tuint) :: (_b0__1, tuint) ::
               (_b1__1, tuint) :: (_b2__1, tuint) :: (_b3__1, tuint) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _tmp (Evar _aes_init_done tint))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _tmp tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Scall None (Evar _aes_gen_tables (Tfunction Tnil tvoid cc_default))
          nil)
        (Sassign (Evar _aes_init_done tint) (Econst_int (Int.repr 1) tint)))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef
            (Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr)))
            (Tstruct _mbedtls_aes_context_struct noattr)) _nr tint)
        (Econst_int (Int.repr 14) tint))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Ecast
                (Efield
                  (Ederef
                    (Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr)))
                    (Tstruct _mbedtls_aes_context_struct noattr)) _buf
                  (tarray tuint 68)) (tptr tuint)))
            (Sset _RK (Etempvar _t'1 (tptr tuint))))
          (Sassign
            (Efield
              (Ederef
                (Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr)))
                (Tstruct _mbedtls_aes_context_struct noattr)) _rk
              (tptr tuint)) (Etempvar _t'1 (tptr tuint))))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                               (Ebinop Oshr (Etempvar _keybits tuint)
                                 (Econst_int (Int.repr 5) tint) tuint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _b0
                      (Ecast
                        (Ederef
                          (Ebinop Oadd (Etempvar _key (tptr tuchar))
                            (Ebinop Oshl (Etempvar _i tuint)
                              (Econst_int (Int.repr 2) tint) tuint)
                            (tptr tuchar)) tuchar) tuint))
                    (Ssequence
                      (Sset _b1
                        (Ecast
                          (Ederef
                            (Ebinop Oadd (Etempvar _key (tptr tuchar))
                              (Ebinop Oadd
                                (Ebinop Oshl (Etempvar _i tuint)
                                  (Econst_int (Int.repr 2) tint) tuint)
                                (Econst_int (Int.repr 1) tint) tuint)
                              (tptr tuchar)) tuchar) tuint))
                      (Ssequence
                        (Sset _b2
                          (Ecast
                            (Ederef
                              (Ebinop Oadd (Etempvar _key (tptr tuchar))
                                (Ebinop Oadd
                                  (Ebinop Oshl (Etempvar _i tuint)
                                    (Econst_int (Int.repr 2) tint) tuint)
                                  (Econst_int (Int.repr 2) tint) tuint)
                                (tptr tuchar)) tuchar) tuint))
                        (Ssequence
                          (Sset _b3
                            (Ecast
                              (Ederef
                                (Ebinop Oadd (Etempvar _key (tptr tuchar))
                                  (Ebinop Oadd
                                    (Ebinop Oshl (Etempvar _i tuint)
                                      (Econst_int (Int.repr 2) tint) tuint)
                                    (Econst_int (Int.repr 3) tint) tuint)
                                  (tptr tuchar)) tuchar) tuint))
                          (Sset _key_word
                            (Ebinop Oor
                              (Ebinop Oor
                                (Ebinop Oor (Etempvar _b0 tuint)
                                  (Ebinop Oshl (Etempvar _b1 tuint)
                                    (Econst_int (Int.repr 8) tint) tuint)
                                  tuint)
                                (Ebinop Oshl (Etempvar _b2 tuint)
                                  (Econst_int (Int.repr 16) tint) tuint)
                                tuint)
                              (Ebinop Oshl (Etempvar _b3 tuint)
                                (Econst_int (Int.repr 24) tint) tuint) tuint))))))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _RK (tptr tuint))
                        (Etempvar _i tuint) (tptr tuint)) tuint)
                    (Etempvar _key_word tuint))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tuint)
                  (Econst_int (Int.repr 1) tint) tuint))))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                 (Econst_int (Int.repr 7) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _rk0
                      (Ederef
                        (Ebinop Oadd (Etempvar _RK (tptr tuint))
                          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _rk7
                        (Ederef
                          (Ebinop Oadd (Etempvar _RK (tptr tuint))
                            (Econst_int (Int.repr 7) tint) (tptr tuint))
                          tuint))
                      (Ssequence
                        (Sset _rcon
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                _RCON (tarray tuint 10)) (Etempvar _i tuint)
                              (tptr tuint)) tuint))
                        (Ssequence
                          (Sset _b0__1
                            (Ecast
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                    _FSb (tarray tuchar 256))
                                  (Ebinop Oand
                                    (Ebinop Oshr (Etempvar _rk7 tuint)
                                      (Econst_int (Int.repr 8) tint) tuint)
                                    (Econst_int (Int.repr 255) tint) tuint)
                                  (tptr tuchar)) tuchar) tuint))
                          (Ssequence
                            (Sset _b1__1
                              (Ecast
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Evar _tables (Tstruct _aes_tables_struct noattr))
                                      _FSb (tarray tuchar 256))
                                    (Ebinop Oand
                                      (Ebinop Oshr (Etempvar _rk7 tuint)
                                        (Econst_int (Int.repr 16) tint)
                                        tuint)
                                      (Econst_int (Int.repr 255) tint) tuint)
                                    (tptr tuchar)) tuchar) tuint))
                            (Ssequence
                              (Sset _b2__1
                                (Ecast
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Evar _tables (Tstruct _aes_tables_struct noattr))
                                        _FSb (tarray tuchar 256))
                                      (Ebinop Oand
                                        (Ebinop Oshr (Etempvar _rk7 tuint)
                                          (Econst_int (Int.repr 24) tint)
                                          tuint)
                                        (Econst_int (Int.repr 255) tint)
                                        tuint) (tptr tuchar)) tuchar) tuint))
                              (Ssequence
                                (Sset _b3__1
                                  (Ecast
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Evar _tables (Tstruct _aes_tables_struct noattr))
                                          _FSb (tarray tuchar 256))
                                        (Ebinop Oand (Etempvar _rk7 tuint)
                                          (Econst_int (Int.repr 255) tint)
                                          tuint) (tptr tuchar)) tuchar)
                                    tuint))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Etempvar _RK (tptr tuint))
                                        (Econst_int (Int.repr 8) tint)
                                        (tptr tuint)) tuint)
                                    (Ebinop Oxor
                                      (Ebinop Oxor
                                        (Ebinop Oxor
                                          (Ebinop Oxor
                                            (Ebinop Oxor
                                              (Etempvar _rk0 tuint)
                                              (Etempvar _rcon tuint) tuint)
                                            (Etempvar _b0__1 tuint) tuint)
                                          (Ebinop Oshl
                                            (Etempvar _b1__1 tuint)
                                            (Econst_int (Int.repr 8) tint)
                                            tuint) tuint)
                                        (Ebinop Oshl (Etempvar _b2__1 tuint)
                                          (Econst_int (Int.repr 16) tint)
                                          tuint) tuint)
                                      (Ebinop Oshl (Etempvar _b3__1 tuint)
                                        (Econst_int (Int.repr 24) tint)
                                        tuint) tuint))
                                  (Ssequence
                                    (Sset _rk0
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _RK (tptr tuint))
                                          (Econst_int (Int.repr 1) tint)
                                          (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sset _rk7
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _RK (tptr tuint))
                                            (Econst_int (Int.repr 8) tint)
                                            (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _RK (tptr tuint))
                                              (Econst_int (Int.repr 9) tint)
                                              (tptr tuint)) tuint)
                                          (Ebinop Oxor (Etempvar _rk0 tuint)
                                            (Etempvar _rk7 tuint) tuint))
                                        (Ssequence
                                          (Sset _rk0
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _RK (tptr tuint))
                                                (Econst_int (Int.repr 2) tint)
                                                (tptr tuint)) tuint))
                                          (Ssequence
                                            (Sset _rk7
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _RK (tptr tuint))
                                                  (Econst_int (Int.repr 9) tint)
                                                  (tptr tuint)) tuint))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _RK (tptr tuint))
                                                    (Econst_int (Int.repr 10) tint)
                                                    (tptr tuint)) tuint)
                                                (Ebinop Oxor
                                                  (Etempvar _rk0 tuint)
                                                  (Etempvar _rk7 tuint)
                                                  tuint))
                                              (Ssequence
                                                (Sset _rk0
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Etempvar _RK (tptr tuint))
                                                      (Econst_int (Int.repr 3) tint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sset _rk7
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Etempvar _RK (tptr tuint))
                                                        (Econst_int (Int.repr 10) tint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Etempvar _RK (tptr tuint))
                                                          (Econst_int (Int.repr 11) tint)
                                                          (tptr tuint))
                                                        tuint)
                                                      (Ebinop Oxor
                                                        (Etempvar _rk0 tuint)
                                                        (Etempvar _rk7 tuint)
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _rk0
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Etempvar _RK (tptr tuint))
                                                            (Econst_int (Int.repr 4) tint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _rk7
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Etempvar _RK (tptr tuint))
                                                              (Econst_int (Int.repr 11) tint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _b0__1
                                                            (Ecast
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                  (Ebinop Oand
                                                                    (Etempvar _rk7 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                  (tptr tuchar))
                                                                tuchar)
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _b1__1
                                                              (Ecast
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _rk7 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                  tuchar)
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _b2__1
                                                                (Ecast
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _rk7 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _b3__1
                                                                  (Ecast
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _rk7 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk0 tuint)
                                                                    (Etempvar _b0__1 tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b1__1 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b2__1 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b3__1 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _rk0
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _rk7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 12) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk0 tuint)
                                                                    (Etempvar _rk7 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _rk0
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 6) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _rk7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 13) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk0 tuint)
                                                                    (Etempvar _rk7 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _rk0
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _rk7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 14) tint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 15) tint)
                                                                    (tptr tuint))
                                                                    tuint)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk0 tuint)
                                                                    (Etempvar _rk7 tuint)
                                                                    tuint))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _RK (tptr tuint))
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    (tptr tuint)))))))))))))))))))))))))))))))))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
|}.

Definition f_mbedtls_aes_setkey_dec := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                (_key, (tptr tuchar)) :: (_keybits, tuint) :: nil);
  fn_vars := ((_cty, (Tstruct _mbedtls_aes_context_struct noattr)) :: nil);
  fn_temps := ((_i, tint) :: (_j, tint) :: (_ret, tint) ::
               (_RK, (tptr tuint)) :: (_SK, (tptr tuint)) ::
               (_key_word, tuint) :: (_sk, tuint) :: (_b0, tuint) ::
               (_b1, tuint) :: (_b2, tuint) :: (_b3, tuint) ::
               (_t'20, (tptr tuint)) :: (_t'19, (tptr tuint)) ::
               (_t'18, (tptr tuint)) :: (_t'17, (tptr tuint)) ::
               (_t'16, (tptr tuint)) :: (_t'15, (tptr tuint)) ::
               (_t'14, (tptr tuint)) :: (_t'13, (tptr tuint)) ::
               (_t'12, (tptr tuint)) :: (_t'11, (tptr tuint)) ::
               (_t'10, (tptr tuint)) :: (_t'9, (tptr tuint)) ::
               (_t'8, (tptr tuint)) :: (_t'7, (tptr tuint)) ::
               (_t'6, (tptr tuint)) :: (_t'5, (tptr tuint)) ::
               (_t'4, (tptr tuint)) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _mbedtls_aes_init (Tfunction
                              (Tcons
                                (tptr (Tstruct _mbedtls_aes_context_struct noattr))
                                Tnil) tvoid cc_default))
    ((Eaddrof (Evar _cty (Tstruct _mbedtls_aes_context_struct noattr))
       (tptr (Tstruct _mbedtls_aes_context_struct noattr))) :: nil))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Ecast
            (Efield
              (Ederef
                (Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr)))
                (Tstruct _mbedtls_aes_context_struct noattr)) _buf
              (tarray tuint 68)) (tptr tuint)))
        (Sset _RK (Etempvar _t'1 (tptr tuint))))
      (Sassign
        (Efield
          (Ederef
            (Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr)))
            (Tstruct _mbedtls_aes_context_struct noattr)) _rk (tptr tuint))
        (Etempvar _t'1 (tptr tuint))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _mbedtls_aes_setkey_enc (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _mbedtls_aes_context_struct noattr))
                                                (Tcons (tptr tuchar)
                                                  (Tcons tuint Tnil))) tint
                                              cc_default))
              ((Eaddrof
                 (Evar _cty (Tstruct _mbedtls_aes_context_struct noattr))
                 (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
               (Etempvar _key (tptr tuchar)) :: (Etempvar _keybits tuint) ::
               nil))
            (Sset _t'3 (Ecast (Etempvar _t'2 tint) tint)))
          (Sset _ret (Etempvar _t'3 tint)))
        (Sifthenelse (Ebinop One (Etempvar _t'3 tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sgoto _exit)
          Sskip))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr)))
              (Tstruct _mbedtls_aes_context_struct noattr)) _nr tint)
          (Efield (Evar _cty (Tstruct _mbedtls_aes_context_struct noattr))
            _nr tint))
        (Ssequence
          (Sset _SK
            (Ebinop Oadd
              (Efield
                (Evar _cty (Tstruct _mbedtls_aes_context_struct noattr)) _rk
                (tptr tuint))
              (Ebinop Omul
                (Efield
                  (Evar _cty (Tstruct _mbedtls_aes_context_struct noattr))
                  _nr tint) (Econst_int (Int.repr 4) tint) tint)
              (tptr tuint)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'4 (Etempvar _SK (tptr tuint)))
                (Sset _SK
                  (Ebinop Oadd (Etempvar _t'4 (tptr tuint))
                    (Econst_int (Int.repr 1) tint) (tptr tuint))))
              (Sset _key_word (Ederef (Etempvar _t'4 (tptr tuint)) tuint)))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'5 (Etempvar _RK (tptr tuint)))
                  (Sset _RK
                    (Ebinop Oadd (Etempvar _t'5 (tptr tuint))
                      (Econst_int (Int.repr 1) tint) (tptr tuint))))
                (Sassign (Ederef (Etempvar _t'5 (tptr tuint)) tuint)
                  (Etempvar _key_word tuint)))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'6 (Etempvar _SK (tptr tuint)))
                    (Sset _SK
                      (Ebinop Oadd (Etempvar _t'6 (tptr tuint))
                        (Econst_int (Int.repr 1) tint) (tptr tuint))))
                  (Sset _key_word
                    (Ederef (Etempvar _t'6 (tptr tuint)) tuint)))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'7 (Etempvar _RK (tptr tuint)))
                      (Sset _RK
                        (Ebinop Oadd (Etempvar _t'7 (tptr tuint))
                          (Econst_int (Int.repr 1) tint) (tptr tuint))))
                    (Sassign (Ederef (Etempvar _t'7 (tptr tuint)) tuint)
                      (Etempvar _key_word tuint)))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'8 (Etempvar _SK (tptr tuint)))
                        (Sset _SK
                          (Ebinop Oadd (Etempvar _t'8 (tptr tuint))
                            (Econst_int (Int.repr 1) tint) (tptr tuint))))
                      (Sset _key_word
                        (Ederef (Etempvar _t'8 (tptr tuint)) tuint)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'9 (Etempvar _RK (tptr tuint)))
                          (Sset _RK
                            (Ebinop Oadd (Etempvar _t'9 (tptr tuint))
                              (Econst_int (Int.repr 1) tint) (tptr tuint))))
                        (Sassign (Ederef (Etempvar _t'9 (tptr tuint)) tuint)
                          (Etempvar _key_word tuint)))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'10 (Etempvar _SK (tptr tuint)))
                            (Sset _SK
                              (Ebinop Oadd (Etempvar _t'10 (tptr tuint))
                                (Econst_int (Int.repr 1) tint) (tptr tuint))))
                          (Sset _key_word
                            (Ederef (Etempvar _t'10 (tptr tuint)) tuint)))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sset _t'11 (Etempvar _RK (tptr tuint)))
                              (Sset _RK
                                (Ebinop Oadd (Etempvar _t'11 (tptr tuint))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuint))))
                            (Sassign
                              (Ederef (Etempvar _t'11 (tptr tuint)) tuint)
                              (Etempvar _key_word tuint)))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _i
                                  (Ebinop Osub
                                    (Efield
                                      (Ederef
                                        (Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr)))
                                        (Tstruct _mbedtls_aes_context_struct noattr))
                                      _nr tint)
                                    (Econst_int (Int.repr 1) tint) tint))
                                (Sset _SK
                                  (Ebinop Osub (Etempvar _SK (tptr tuint))
                                    (Econst_int (Int.repr 8) tint)
                                    (tptr tuint))))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Ogt (Etempvar _i tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _j (Econst_int (Int.repr 0) tint))
                                    (Sloop
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _j tint)
                                                       (Econst_int (Int.repr 4) tint)
                                                       tint)
                                          Sskip
                                          Sbreak)
                                        (Ssequence
                                          (Sset _sk
                                            (Ederef
                                              (Etempvar _SK (tptr tuint))
                                              tuint))
                                          (Ssequence
                                            (Sset _b0
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                    _FSb (tarray tuchar 256))
                                                  (Ebinop Oand
                                                    (Etempvar _sk tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) (tptr tuchar))
                                                tuchar))
                                            (Ssequence
                                              (Sset _b1
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                      _FSb
                                                      (tarray tuchar 256))
                                                    (Ebinop Oand
                                                      (Ebinop Oshr
                                                        (Etempvar _sk tuint)
                                                        (Econst_int (Int.repr 8) tint)
                                                        tuint)
                                                      (Econst_int (Int.repr 255) tint)
                                                      tuint) (tptr tuchar))
                                                  tuchar))
                                              (Ssequence
                                                (Sset _b2
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                        _FSb
                                                        (tarray tuchar 256))
                                                      (Ebinop Oand
                                                        (Ebinop Oshr
                                                          (Etempvar _sk tuint)
                                                          (Econst_int (Int.repr 16) tint)
                                                          tuint)
                                                        (Econst_int (Int.repr 255) tint)
                                                        tuint) (tptr tuchar))
                                                    tuchar))
                                                (Ssequence
                                                  (Sset _b3
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                          _FSb
                                                          (tarray tuchar 256))
                                                        (Ebinop Oand
                                                          (Ebinop Oshr
                                                            (Etempvar _sk tuint)
                                                            (Econst_int (Int.repr 24) tint)
                                                            tuint)
                                                          (Econst_int (Int.repr 255) tint)
                                                          tuint)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Ssequence
                                                    (Sset _b0
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                            _RT0
                                                            (tarray tuint 256))
                                                          (Etempvar _b0 tuint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _b1
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                              _RT1
                                                              (tarray tuint 256))
                                                            (Etempvar _b1 tuint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _b2
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                _RT2
                                                                (tarray tuint 256))
                                                              (Etempvar _b2 tuint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _b3
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                  _RT3
                                                                  (tarray tuint 256))
                                                                (Etempvar _b3 tuint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'12
                                                                (Etempvar _RK (tptr tuint)))
                                                              (Sset _RK
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'12 (tptr tuint))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuint))))
                                                            (Sassign
                                                              (Ederef
                                                                (Etempvar _t'12 (tptr tuint))
                                                                tuint)
                                                              (Ebinop Oxor
                                                                (Ebinop Oxor
                                                                  (Ebinop Oxor
                                                                    (Etempvar _b0 tuint)
                                                                    (Etempvar _b1 tuint)
                                                                    tuint)
                                                                  (Etempvar _b2 tuint)
                                                                  tuint)
                                                                (Etempvar _b3 tuint)
                                                                tuint)))))))))))))
                                      (Ssequence
                                        (Sset _j
                                          (Ebinop Oadd (Etempvar _j tint)
                                            (Econst_int (Int.repr 1) tint)
                                            tint))
                                        (Sset _SK
                                          (Ebinop Oadd
                                            (Etempvar _SK (tptr tuint))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuint)))))))
                                (Ssequence
                                  (Sset _i
                                    (Ebinop Osub (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint))
                                  (Sset _SK
                                    (Ebinop Osub (Etempvar _SK (tptr tuint))
                                      (Econst_int (Int.repr 8) tint)
                                      (tptr tuint))))))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'13 (Etempvar _SK (tptr tuint)))
                                  (Sset _SK
                                    (Ebinop Oadd
                                      (Etempvar _t'13 (tptr tuint))
                                      (Econst_int (Int.repr 1) tint)
                                      (tptr tuint))))
                                (Sset _key_word
                                  (Ederef (Etempvar _t'13 (tptr tuint))
                                    tuint)))
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'14 (Etempvar _RK (tptr tuint)))
                                    (Sset _RK
                                      (Ebinop Oadd
                                        (Etempvar _t'14 (tptr tuint))
                                        (Econst_int (Int.repr 1) tint)
                                        (tptr tuint))))
                                  (Sassign
                                    (Ederef (Etempvar _t'14 (tptr tuint))
                                      tuint) (Etempvar _key_word tuint)))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'15
                                        (Etempvar _SK (tptr tuint)))
                                      (Sset _SK
                                        (Ebinop Oadd
                                          (Etempvar _t'15 (tptr tuint))
                                          (Econst_int (Int.repr 1) tint)
                                          (tptr tuint))))
                                    (Sset _key_word
                                      (Ederef (Etempvar _t'15 (tptr tuint))
                                        tuint)))
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'16
                                          (Etempvar _RK (tptr tuint)))
                                        (Sset _RK
                                          (Ebinop Oadd
                                            (Etempvar _t'16 (tptr tuint))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuint))))
                                      (Sassign
                                        (Ederef (Etempvar _t'16 (tptr tuint))
                                          tuint) (Etempvar _key_word tuint)))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'17
                                            (Etempvar _SK (tptr tuint)))
                                          (Sset _SK
                                            (Ebinop Oadd
                                              (Etempvar _t'17 (tptr tuint))
                                              (Econst_int (Int.repr 1) tint)
                                              (tptr tuint))))
                                        (Sset _key_word
                                          (Ederef
                                            (Etempvar _t'17 (tptr tuint))
                                            tuint)))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'18
                                              (Etempvar _RK (tptr tuint)))
                                            (Sset _RK
                                              (Ebinop Oadd
                                                (Etempvar _t'18 (tptr tuint))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr tuint))))
                                          (Sassign
                                            (Ederef
                                              (Etempvar _t'18 (tptr tuint))
                                              tuint)
                                            (Etempvar _key_word tuint)))
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'19
                                                (Etempvar _SK (tptr tuint)))
                                              (Sset _SK
                                                (Ebinop Oadd
                                                  (Etempvar _t'19 (tptr tuint))
                                                  (Econst_int (Int.repr 1) tint)
                                                  (tptr tuint))))
                                            (Sset _key_word
                                              (Ederef
                                                (Etempvar _t'19 (tptr tuint))
                                                tuint)))
                                          (Ssequence
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'20
                                                  (Etempvar _RK (tptr tuint)))
                                                (Sset _RK
                                                  (Ebinop Oadd
                                                    (Etempvar _t'20 (tptr tuint))
                                                    (Econst_int (Int.repr 1) tint)
                                                    (tptr tuint))))
                                              (Sassign
                                                (Ederef
                                                  (Etempvar _t'20 (tptr tuint))
                                                  tuint)
                                                (Etempvar _key_word tuint)))
                                            (Ssequence
                                              (Slabel _exit
                                                (Scall None
                                                  (Evar _mbedtls_aes_free 
                                                  (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _mbedtls_aes_context_struct noattr))
                                                      Tnil) tvoid cc_default))
                                                  ((Eaddrof
                                                     (Evar _cty (Tstruct _mbedtls_aes_context_struct noattr))
                                                     (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                                                   nil)))
                                              (Sreturn (Some (Etempvar _ret tint))))))))))))))))))))))))))
|}.

Definition f_mbedtls_aes_encrypt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                (_input, (tptr tuchar)) :: (_output, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_RK, (tptr tuint)) :: (_X0, tuint) ::
               (_X1, tuint) :: (_X2, tuint) :: (_X3, tuint) ::
               (_Y0, tuint) :: (_Y1, tuint) :: (_Y2, tuint) ::
               (_Y3, tuint) :: (_tmp, tuint) :: (_b0, tuint) ::
               (_b1, tuint) :: (_b2, tuint) :: (_b3, tuint) ::
               (_b0__1, tuint) :: (_b1__1, tuint) :: (_b2__1, tuint) ::
               (_b3__1, tuint) :: (_b0__2, tuint) :: (_b1__2, tuint) ::
               (_b2__2, tuint) :: (_b3__2, tuint) :: (_b0__3, tuint) ::
               (_b1__3, tuint) :: (_b2__3, tuint) :: (_b3__3, tuint) ::
               (_rk, tuint) :: (_b0__4, tuint) :: (_b1__4, tuint) ::
               (_b2__4, tuint) :: (_b3__4, tuint) :: (_rk__1, tuint) ::
               (_b0__5, tuint) :: (_b1__5, tuint) :: (_b2__5, tuint) ::
               (_b3__5, tuint) :: (_rk__2, tuint) :: (_b0__6, tuint) ::
               (_b1__6, tuint) :: (_b2__6, tuint) :: (_b3__6, tuint) ::
               (_rk__3, tuint) :: (_b0__7, tuint) :: (_b1__7, tuint) ::
               (_b2__7, tuint) :: (_b3__7, tuint) :: (_t'20, (tptr tuint)) ::
               (_t'19, (tptr tuint)) :: (_t'18, (tptr tuint)) ::
               (_t'17, (tptr tuint)) :: (_t'16, (tptr tuint)) ::
               (_t'15, (tptr tuint)) :: (_t'14, (tptr tuint)) ::
               (_t'13, (tptr tuint)) :: (_t'12, (tptr tuint)) ::
               (_t'11, (tptr tuint)) :: (_t'10, (tptr tuint)) ::
               (_t'9, (tptr tuint)) :: (_t'8, (tptr tuint)) ::
               (_t'7, (tptr tuint)) :: (_t'6, (tptr tuint)) ::
               (_t'5, (tptr tuint)) :: (_t'4, (tptr tuint)) ::
               (_t'3, (tptr tuint)) :: (_t'2, (tptr tuint)) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _RK
    (Efield
      (Ederef
        (Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr)))
        (Tstruct _mbedtls_aes_context_struct noattr)) _rk (tptr tuint)))
  (Ssequence
    (Ssequence
      (Sset _b0
        (Ecast
          (Ederef
            (Ebinop Oadd (Etempvar _input (tptr tuchar))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar) tuint))
      (Ssequence
        (Sset _b1
          (Ecast
            (Ederef
              (Ebinop Oadd (Etempvar _input (tptr tuchar))
                (Ebinop Oadd (Econst_int (Int.repr 0) tint)
                  (Econst_int (Int.repr 1) tint) tint) (tptr tuchar)) tuchar)
            tuint))
        (Ssequence
          (Sset _b2
            (Ecast
              (Ederef
                (Ebinop Oadd (Etempvar _input (tptr tuchar))
                  (Ebinop Oadd (Econst_int (Int.repr 0) tint)
                    (Econst_int (Int.repr 2) tint) tint) (tptr tuchar))
                tuchar) tuint))
          (Ssequence
            (Sset _b3
              (Ecast
                (Ederef
                  (Ebinop Oadd (Etempvar _input (tptr tuchar))
                    (Ebinop Oadd (Econst_int (Int.repr 0) tint)
                      (Econst_int (Int.repr 3) tint) tint) (tptr tuchar))
                  tuchar) tuint))
            (Sset _X0
              (Ebinop Oor
                (Ebinop Oor
                  (Ebinop Oor (Etempvar _b0 tuint)
                    (Ebinop Oshl (Etempvar _b1 tuint)
                      (Econst_int (Int.repr 8) tint) tuint) tuint)
                  (Ebinop Oshl (Etempvar _b2 tuint)
                    (Econst_int (Int.repr 16) tint) tuint) tuint)
                (Ebinop Oshl (Etempvar _b3 tuint)
                  (Econst_int (Int.repr 24) tint) tuint) tuint))))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'1 (Etempvar _RK (tptr tuint)))
          (Sset _RK
            (Ebinop Oadd (Etempvar _t'1 (tptr tuint))
              (Econst_int (Int.repr 1) tint) (tptr tuint))))
        (Sset _tmp (Ederef (Etempvar _t'1 (tptr tuint)) tuint)))
      (Ssequence
        (Sset _X0
          (Ebinop Oxor (Etempvar _X0 tuint) (Etempvar _tmp tuint) tuint))
        (Ssequence
          (Ssequence
            (Sset _b0__1
              (Ecast
                (Ederef
                  (Ebinop Oadd (Etempvar _input (tptr tuchar))
                    (Econst_int (Int.repr 4) tint) (tptr tuchar)) tuchar)
                tuint))
            (Ssequence
              (Sset _b1__1
                (Ecast
                  (Ederef
                    (Ebinop Oadd (Etempvar _input (tptr tuchar))
                      (Ebinop Oadd (Econst_int (Int.repr 4) tint)
                        (Econst_int (Int.repr 1) tint) tint) (tptr tuchar))
                    tuchar) tuint))
              (Ssequence
                (Sset _b2__1
                  (Ecast
                    (Ederef
                      (Ebinop Oadd (Etempvar _input (tptr tuchar))
                        (Ebinop Oadd (Econst_int (Int.repr 4) tint)
                          (Econst_int (Int.repr 2) tint) tint) (tptr tuchar))
                      tuchar) tuint))
                (Ssequence
                  (Sset _b3__1
                    (Ecast
                      (Ederef
                        (Ebinop Oadd (Etempvar _input (tptr tuchar))
                          (Ebinop Oadd (Econst_int (Int.repr 4) tint)
                            (Econst_int (Int.repr 3) tint) tint)
                          (tptr tuchar)) tuchar) tuint))
                  (Sset _X1
                    (Ebinop Oor
                      (Ebinop Oor
                        (Ebinop Oor (Etempvar _b0__1 tuint)
                          (Ebinop Oshl (Etempvar _b1__1 tuint)
                            (Econst_int (Int.repr 8) tint) tuint) tuint)
                        (Ebinop Oshl (Etempvar _b2__1 tuint)
                          (Econst_int (Int.repr 16) tint) tuint) tuint)
                      (Ebinop Oshl (Etempvar _b3__1 tuint)
                        (Econst_int (Int.repr 24) tint) tuint) tuint))))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'2 (Etempvar _RK (tptr tuint)))
                (Sset _RK
                  (Ebinop Oadd (Etempvar _t'2 (tptr tuint))
                    (Econst_int (Int.repr 1) tint) (tptr tuint))))
              (Sset _tmp (Ederef (Etempvar _t'2 (tptr tuint)) tuint)))
            (Ssequence
              (Sset _X1
                (Ebinop Oxor (Etempvar _X1 tuint) (Etempvar _tmp tuint)
                  tuint))
              (Ssequence
                (Ssequence
                  (Sset _b0__2
                    (Ecast
                      (Ederef
                        (Ebinop Oadd (Etempvar _input (tptr tuchar))
                          (Econst_int (Int.repr 8) tint) (tptr tuchar))
                        tuchar) tuint))
                  (Ssequence
                    (Sset _b1__2
                      (Ecast
                        (Ederef
                          (Ebinop Oadd (Etempvar _input (tptr tuchar))
                            (Ebinop Oadd (Econst_int (Int.repr 8) tint)
                              (Econst_int (Int.repr 1) tint) tint)
                            (tptr tuchar)) tuchar) tuint))
                    (Ssequence
                      (Sset _b2__2
                        (Ecast
                          (Ederef
                            (Ebinop Oadd (Etempvar _input (tptr tuchar))
                              (Ebinop Oadd (Econst_int (Int.repr 8) tint)
                                (Econst_int (Int.repr 2) tint) tint)
                              (tptr tuchar)) tuchar) tuint))
                      (Ssequence
                        (Sset _b3__2
                          (Ecast
                            (Ederef
                              (Ebinop Oadd (Etempvar _input (tptr tuchar))
                                (Ebinop Oadd (Econst_int (Int.repr 8) tint)
                                  (Econst_int (Int.repr 3) tint) tint)
                                (tptr tuchar)) tuchar) tuint))
                        (Sset _X2
                          (Ebinop Oor
                            (Ebinop Oor
                              (Ebinop Oor (Etempvar _b0__2 tuint)
                                (Ebinop Oshl (Etempvar _b1__2 tuint)
                                  (Econst_int (Int.repr 8) tint) tuint)
                                tuint)
                              (Ebinop Oshl (Etempvar _b2__2 tuint)
                                (Econst_int (Int.repr 16) tint) tuint) tuint)
                            (Ebinop Oshl (Etempvar _b3__2 tuint)
                              (Econst_int (Int.repr 24) tint) tuint) tuint))))))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'3 (Etempvar _RK (tptr tuint)))
                      (Sset _RK
                        (Ebinop Oadd (Etempvar _t'3 (tptr tuint))
                          (Econst_int (Int.repr 1) tint) (tptr tuint))))
                    (Sset _tmp (Ederef (Etempvar _t'3 (tptr tuint)) tuint)))
                  (Ssequence
                    (Sset _X2
                      (Ebinop Oxor (Etempvar _X2 tuint) (Etempvar _tmp tuint)
                        tuint))
                    (Ssequence
                      (Ssequence
                        (Sset _b0__3
                          (Ecast
                            (Ederef
                              (Ebinop Oadd (Etempvar _input (tptr tuchar))
                                (Econst_int (Int.repr 12) tint)
                                (tptr tuchar)) tuchar) tuint))
                        (Ssequence
                          (Sset _b1__3
                            (Ecast
                              (Ederef
                                (Ebinop Oadd (Etempvar _input (tptr tuchar))
                                  (Ebinop Oadd
                                    (Econst_int (Int.repr 12) tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  (tptr tuchar)) tuchar) tuint))
                          (Ssequence
                            (Sset _b2__3
                              (Ecast
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _input (tptr tuchar))
                                    (Ebinop Oadd
                                      (Econst_int (Int.repr 12) tint)
                                      (Econst_int (Int.repr 2) tint) tint)
                                    (tptr tuchar)) tuchar) tuint))
                            (Ssequence
                              (Sset _b3__3
                                (Ecast
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _input (tptr tuchar))
                                      (Ebinop Oadd
                                        (Econst_int (Int.repr 12) tint)
                                        (Econst_int (Int.repr 3) tint) tint)
                                      (tptr tuchar)) tuchar) tuint))
                              (Sset _X3
                                (Ebinop Oor
                                  (Ebinop Oor
                                    (Ebinop Oor (Etempvar _b0__3 tuint)
                                      (Ebinop Oshl (Etempvar _b1__3 tuint)
                                        (Econst_int (Int.repr 8) tint) tuint)
                                      tuint)
                                    (Ebinop Oshl (Etempvar _b2__3 tuint)
                                      (Econst_int (Int.repr 16) tint) tuint)
                                    tuint)
                                  (Ebinop Oshl (Etempvar _b3__3 tuint)
                                    (Econst_int (Int.repr 24) tint) tuint)
                                  tuint))))))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'4 (Etempvar _RK (tptr tuint)))
                            (Sset _RK
                              (Ebinop Oadd (Etempvar _t'4 (tptr tuint))
                                (Econst_int (Int.repr 1) tint) (tptr tuint))))
                          (Sset _tmp
                            (Ederef (Etempvar _t'4 (tptr tuint)) tuint)))
                        (Ssequence
                          (Sset _X3
                            (Ebinop Oxor (Etempvar _X3 tuint)
                              (Etempvar _tmp tuint) tuint))
                          (Ssequence
                            (Sset _tmp
                              (Efield
                                (Ederef
                                  (Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr)))
                                  (Tstruct _mbedtls_aes_context_struct noattr))
                                _nr tint))
                            (Ssequence
                              (Ssequence
                                (Sset _i
                                  (Ebinop Osub
                                    (Ebinop Oshr (Etempvar _tmp tuint)
                                      (Econst_int (Int.repr 1) tint) tuint)
                                    (Econst_int (Int.repr 1) tint) tuint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Ogt
                                                   (Etempvar _i tint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'5
                                              (Etempvar _RK (tptr tuint)))
                                            (Sset _RK
                                              (Ebinop Oadd
                                                (Etempvar _t'5 (tptr tuint))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr tuint))))
                                          (Sset _rk
                                            (Ederef
                                              (Etempvar _t'5 (tptr tuint))
                                              tuint)))
                                        (Ssequence
                                          (Sset _b0__4
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                  _FT0 (tarray tuint 256))
                                                (Ebinop Oand
                                                  (Etempvar _X0 tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) (tptr tuint)) tuint))
                                          (Ssequence
                                            (Sset _b1__4
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                    _FT1 (tarray tuint 256))
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _X1 tuint)
                                                      (Econst_int (Int.repr 8) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) (tptr tuint))
                                                tuint))
                                            (Ssequence
                                              (Sset _b2__4
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                      _FT2
                                                      (tarray tuint 256))
                                                    (Ebinop Oand
                                                      (Ebinop Oshr
                                                        (Etempvar _X2 tuint)
                                                        (Econst_int (Int.repr 16) tint)
                                                        tuint)
                                                      (Econst_int (Int.repr 255) tint)
                                                      tuint) (tptr tuint))
                                                  tuint))
                                              (Ssequence
                                                (Sset _b3__4
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                        _FT3
                                                        (tarray tuint 256))
                                                      (Ebinop Oand
                                                        (Ebinop Oshr
                                                          (Etempvar _X3 tuint)
                                                          (Econst_int (Int.repr 24) tint)
                                                          tuint)
                                                        (Econst_int (Int.repr 255) tint)
                                                        tuint) (tptr tuint))
                                                    tuint))
                                                (Ssequence
                                                  (Sset _Y0
                                                    (Ebinop Oxor
                                                      (Ebinop Oxor
                                                        (Ebinop Oxor
                                                          (Ebinop Oxor
                                                            (Etempvar _rk tuint)
                                                            (Etempvar _b0__4 tuint)
                                                            tuint)
                                                          (Etempvar _b1__4 tuint)
                                                          tuint)
                                                        (Etempvar _b2__4 tuint)
                                                        tuint)
                                                      (Etempvar _b3__4 tuint)
                                                      tuint))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'6
                                                          (Etempvar _RK (tptr tuint)))
                                                        (Sset _RK
                                                          (Ebinop Oadd
                                                            (Etempvar _t'6 (tptr tuint))
                                                            (Econst_int (Int.repr 1) tint)
                                                            (tptr tuint))))
                                                      (Sset _rk
                                                        (Ederef
                                                          (Etempvar _t'6 (tptr tuint))
                                                          tuint)))
                                                    (Ssequence
                                                      (Sset _b0__4
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                              _FT0
                                                              (tarray tuint 256))
                                                            (Ebinop Oand
                                                              (Etempvar _X1 tuint)
                                                              (Econst_int (Int.repr 255) tint)
                                                              tuint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _b1__4
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                _FT1
                                                                (tarray tuint 256))
                                                              (Ebinop Oand
                                                                (Ebinop Oshr
                                                                  (Etempvar _X2 tuint)
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  tuint)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tuint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _b2__4
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                  _FT2
                                                                  (tarray tuint 256))
                                                                (Ebinop Oand
                                                                  (Ebinop Oshr
                                                                    (Etempvar _X3 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                  (Econst_int (Int.repr 255) tint)
                                                                  tuint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _b3__4
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT3
                                                                    (tarray tuint 256))
                                                                  (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X0 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _Y1
                                                                (Ebinop Oxor
                                                                  (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk tuint)
                                                                    (Etempvar _b0__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__4 tuint)
                                                                    tuint)
                                                                  (Etempvar _b3__4 tuint)
                                                                  tuint))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'7
                                                                    (Etempvar _RK (tptr tuint)))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'7 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                                  (Sset _rk
                                                                    (Ederef
                                                                    (Etempvar _t'7 (tptr tuint))
                                                                    tuint)))
                                                                (Ssequence
                                                                  (Sset _b0__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT0
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _X2 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _b1__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT1
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X3 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b2__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT2
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X0 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b3__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT3
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X1 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _Y2
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk tuint)
                                                                    (Etempvar _b0__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b3__4 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'8
                                                                    (Etempvar _RK (tptr tuint)))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'8 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                                    (Sset _rk
                                                                    (Ederef
                                                                    (Etempvar _t'8 (tptr tuint))
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _b0__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT0
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _X3 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b1__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT1
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X0 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b2__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT2
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X1 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b3__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT3
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X2 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _Y3
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk tuint)
                                                                    (Etempvar _b0__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b3__4 tuint)
                                                                    tuint)))))))))))))))))))))))))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'9
                                              (Etempvar _RK (tptr tuint)))
                                            (Sset _RK
                                              (Ebinop Oadd
                                                (Etempvar _t'9 (tptr tuint))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr tuint))))
                                          (Sset _rk__1
                                            (Ederef
                                              (Etempvar _t'9 (tptr tuint))
                                              tuint)))
                                        (Ssequence
                                          (Sset _b0__5
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                  _FT0 (tarray tuint 256))
                                                (Ebinop Oand
                                                  (Etempvar _Y0 tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) (tptr tuint)) tuint))
                                          (Ssequence
                                            (Sset _b1__5
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                    _FT1 (tarray tuint 256))
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _Y1 tuint)
                                                      (Econst_int (Int.repr 8) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) (tptr tuint))
                                                tuint))
                                            (Ssequence
                                              (Sset _b2__5
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                      _FT2
                                                      (tarray tuint 256))
                                                    (Ebinop Oand
                                                      (Ebinop Oshr
                                                        (Etempvar _Y2 tuint)
                                                        (Econst_int (Int.repr 16) tint)
                                                        tuint)
                                                      (Econst_int (Int.repr 255) tint)
                                                      tuint) (tptr tuint))
                                                  tuint))
                                              (Ssequence
                                                (Sset _b3__5
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                        _FT3
                                                        (tarray tuint 256))
                                                      (Ebinop Oand
                                                        (Ebinop Oshr
                                                          (Etempvar _Y3 tuint)
                                                          (Econst_int (Int.repr 24) tint)
                                                          tuint)
                                                        (Econst_int (Int.repr 255) tint)
                                                        tuint) (tptr tuint))
                                                    tuint))
                                                (Ssequence
                                                  (Sset _X0
                                                    (Ebinop Oxor
                                                      (Ebinop Oxor
                                                        (Ebinop Oxor
                                                          (Ebinop Oxor
                                                            (Etempvar _rk__1 tuint)
                                                            (Etempvar _b0__5 tuint)
                                                            tuint)
                                                          (Etempvar _b1__5 tuint)
                                                          tuint)
                                                        (Etempvar _b2__5 tuint)
                                                        tuint)
                                                      (Etempvar _b3__5 tuint)
                                                      tuint))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'10
                                                          (Etempvar _RK (tptr tuint)))
                                                        (Sset _RK
                                                          (Ebinop Oadd
                                                            (Etempvar _t'10 (tptr tuint))
                                                            (Econst_int (Int.repr 1) tint)
                                                            (tptr tuint))))
                                                      (Sset _rk__1
                                                        (Ederef
                                                          (Etempvar _t'10 (tptr tuint))
                                                          tuint)))
                                                    (Ssequence
                                                      (Sset _b0__5
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                              _FT0
                                                              (tarray tuint 256))
                                                            (Ebinop Oand
                                                              (Etempvar _Y1 tuint)
                                                              (Econst_int (Int.repr 255) tint)
                                                              tuint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _b1__5
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                _FT1
                                                                (tarray tuint 256))
                                                              (Ebinop Oand
                                                                (Ebinop Oshr
                                                                  (Etempvar _Y2 tuint)
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  tuint)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tuint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _b2__5
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                  _FT2
                                                                  (tarray tuint 256))
                                                                (Ebinop Oand
                                                                  (Ebinop Oshr
                                                                    (Etempvar _Y3 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                  (Econst_int (Int.repr 255) tint)
                                                                  tuint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _b3__5
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT3
                                                                    (tarray tuint 256))
                                                                  (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y0 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _X1
                                                                (Ebinop Oxor
                                                                  (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__1 tuint)
                                                                    (Etempvar _b0__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__5 tuint)
                                                                    tuint)
                                                                  (Etempvar _b3__5 tuint)
                                                                  tuint))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'11
                                                                    (Etempvar _RK (tptr tuint)))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'11 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                                  (Sset _rk__1
                                                                    (Ederef
                                                                    (Etempvar _t'11 (tptr tuint))
                                                                    tuint)))
                                                                (Ssequence
                                                                  (Sset _b0__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT0
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _Y2 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _b1__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT1
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y3 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b2__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT2
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y0 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b3__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT3
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y1 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _X2
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__1 tuint)
                                                                    (Etempvar _b0__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b3__5 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'12
                                                                    (Etempvar _RK (tptr tuint)))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'12 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                                    (Sset _rk__1
                                                                    (Ederef
                                                                    (Etempvar _t'12 (tptr tuint))
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _b0__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT0
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _Y3 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b1__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT1
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y0 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b2__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT2
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y1 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b3__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT3
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y2 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _X3
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__1 tuint)
                                                                    (Etempvar _b0__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b3__5 tuint)
                                                                    tuint)))))))))))))))))))))))))))
                                  (Sset _i
                                    (Ebinop Osub (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint))))
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'13
                                        (Etempvar _RK (tptr tuint)))
                                      (Sset _RK
                                        (Ebinop Oadd
                                          (Etempvar _t'13 (tptr tuint))
                                          (Econst_int (Int.repr 1) tint)
                                          (tptr tuint))))
                                    (Sset _rk__2
                                      (Ederef (Etempvar _t'13 (tptr tuint))
                                        tuint)))
                                  (Ssequence
                                    (Sset _b0__6
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Evar _tables (Tstruct _aes_tables_struct noattr))
                                            _FT0 (tarray tuint 256))
                                          (Ebinop Oand (Etempvar _X0 tuint)
                                            (Econst_int (Int.repr 255) tint)
                                            tuint) (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sset _b1__6
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                              _FT1 (tarray tuint 256))
                                            (Ebinop Oand
                                              (Ebinop Oshr
                                                (Etempvar _X1 tuint)
                                                (Econst_int (Int.repr 8) tint)
                                                tuint)
                                              (Econst_int (Int.repr 255) tint)
                                              tuint) (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sset _b2__6
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                _FT2 (tarray tuint 256))
                                              (Ebinop Oand
                                                (Ebinop Oshr
                                                  (Etempvar _X2 tuint)
                                                  (Econst_int (Int.repr 16) tint)
                                                  tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) (tptr tuint)) tuint))
                                        (Ssequence
                                          (Sset _b3__6
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                  _FT3 (tarray tuint 256))
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _X3 tuint)
                                                    (Econst_int (Int.repr 24) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) (tptr tuint)) tuint))
                                          (Ssequence
                                            (Sset _Y0
                                              (Ebinop Oxor
                                                (Ebinop Oxor
                                                  (Ebinop Oxor
                                                    (Ebinop Oxor
                                                      (Etempvar _rk__2 tuint)
                                                      (Etempvar _b0__6 tuint)
                                                      tuint)
                                                    (Etempvar _b1__6 tuint)
                                                    tuint)
                                                  (Etempvar _b2__6 tuint)
                                                  tuint)
                                                (Etempvar _b3__6 tuint)
                                                tuint))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'14
                                                    (Etempvar _RK (tptr tuint)))
                                                  (Sset _RK
                                                    (Ebinop Oadd
                                                      (Etempvar _t'14 (tptr tuint))
                                                      (Econst_int (Int.repr 1) tint)
                                                      (tptr tuint))))
                                                (Sset _rk__2
                                                  (Ederef
                                                    (Etempvar _t'14 (tptr tuint))
                                                    tuint)))
                                              (Ssequence
                                                (Sset _b0__6
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                        _FT0
                                                        (tarray tuint 256))
                                                      (Ebinop Oand
                                                        (Etempvar _X1 tuint)
                                                        (Econst_int (Int.repr 255) tint)
                                                        tuint) (tptr tuint))
                                                    tuint))
                                                (Ssequence
                                                  (Sset _b1__6
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                          _FT1
                                                          (tarray tuint 256))
                                                        (Ebinop Oand
                                                          (Ebinop Oshr
                                                            (Etempvar _X2 tuint)
                                                            (Econst_int (Int.repr 8) tint)
                                                            tuint)
                                                          (Econst_int (Int.repr 255) tint)
                                                          tuint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _b2__6
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                            _FT2
                                                            (tarray tuint 256))
                                                          (Ebinop Oand
                                                            (Ebinop Oshr
                                                              (Etempvar _X3 tuint)
                                                              (Econst_int (Int.repr 16) tint)
                                                              tuint)
                                                            (Econst_int (Int.repr 255) tint)
                                                            tuint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _b3__6
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                              _FT3
                                                              (tarray tuint 256))
                                                            (Ebinop Oand
                                                              (Ebinop Oshr
                                                                (Etempvar _X0 tuint)
                                                                (Econst_int (Int.repr 24) tint)
                                                                tuint)
                                                              (Econst_int (Int.repr 255) tint)
                                                              tuint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _Y1
                                                          (Ebinop Oxor
                                                            (Ebinop Oxor
                                                              (Ebinop Oxor
                                                                (Ebinop Oxor
                                                                  (Etempvar _rk__2 tuint)
                                                                  (Etempvar _b0__6 tuint)
                                                                  tuint)
                                                                (Etempvar _b1__6 tuint)
                                                                tuint)
                                                              (Etempvar _b2__6 tuint)
                                                              tuint)
                                                            (Etempvar _b3__6 tuint)
                                                            tuint))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'15
                                                                (Etempvar _RK (tptr tuint)))
                                                              (Sset _RK
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'15 (tptr tuint))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuint))))
                                                            (Sset _rk__2
                                                              (Ederef
                                                                (Etempvar _t'15 (tptr tuint))
                                                                tuint)))
                                                          (Ssequence
                                                            (Sset _b0__6
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT0
                                                                    (tarray tuint 256))
                                                                  (Ebinop Oand
                                                                    (Etempvar _X2 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _b1__6
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT1
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X3 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _b2__6
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT2
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X0 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _b3__6
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT3
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X1 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _Y2
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__2 tuint)
                                                                    (Etempvar _b0__6 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__6 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__6 tuint)
                                                                    tuint)
                                                                    (Etempvar _b3__6 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'16
                                                                    (Etempvar _RK (tptr tuint)))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'16 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                                    (Sset _rk__2
                                                                    (Ederef
                                                                    (Etempvar _t'16 (tptr tuint))
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _b0__6
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT0
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _X3 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b1__6
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT1
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X0 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b2__6
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT2
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X1 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b3__6
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FT3
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X2 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _Y3
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__2 tuint)
                                                                    (Etempvar _b0__6 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__6 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__6 tuint)
                                                                    tuint)
                                                                    (Etempvar _b3__6 tuint)
                                                                    tuint)))))))))))))))))))))))))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'17
                                          (Etempvar _RK (tptr tuint)))
                                        (Sset _RK
                                          (Ebinop Oadd
                                            (Etempvar _t'17 (tptr tuint))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuint))))
                                      (Sset _rk__3
                                        (Ederef (Etempvar _t'17 (tptr tuint))
                                          tuint)))
                                    (Ssequence
                                      (Sset _b0__7
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                              _FSb (tarray tuchar 256))
                                            (Ebinop Oand (Etempvar _Y0 tuint)
                                              (Econst_int (Int.repr 255) tint)
                                              tuint) (tptr tuchar)) tuchar))
                                      (Ssequence
                                        (Sset _b1__7
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                _FSb (tarray tuchar 256))
                                              (Ebinop Oand
                                                (Ebinop Oshr
                                                  (Etempvar _Y1 tuint)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) (tptr tuchar)) tuchar))
                                        (Ssequence
                                          (Sset _b2__7
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                  _FSb (tarray tuchar 256))
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _Y2 tuint)
                                                    (Econst_int (Int.repr 16) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) (tptr tuchar))
                                              tuchar))
                                          (Ssequence
                                            (Sset _b3__7
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                    _FSb (tarray tuchar 256))
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _Y3 tuint)
                                                      (Econst_int (Int.repr 24) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) (tptr tuchar))
                                                tuchar))
                                            (Ssequence
                                              (Sset _X0
                                                (Ebinop Oxor
                                                  (Ebinop Oxor
                                                    (Ebinop Oxor
                                                      (Ebinop Oxor
                                                        (Etempvar _rk__3 tuint)
                                                        (Etempvar _b0__7 tuint)
                                                        tuint)
                                                      (Ebinop Oshl
                                                        (Etempvar _b1__7 tuint)
                                                        (Econst_int (Int.repr 8) tint)
                                                        tuint) tuint)
                                                    (Ebinop Oshl
                                                      (Etempvar _b2__7 tuint)
                                                      (Econst_int (Int.repr 16) tint)
                                                      tuint) tuint)
                                                  (Ebinop Oshl
                                                    (Etempvar _b3__7 tuint)
                                                    (Econst_int (Int.repr 24) tint)
                                                    tuint) tuint))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'18
                                                      (Etempvar _RK (tptr tuint)))
                                                    (Sset _RK
                                                      (Ebinop Oadd
                                                        (Etempvar _t'18 (tptr tuint))
                                                        (Econst_int (Int.repr 1) tint)
                                                        (tptr tuint))))
                                                  (Sset _rk__3
                                                    (Ederef
                                                      (Etempvar _t'18 (tptr tuint))
                                                      tuint)))
                                                (Ssequence
                                                  (Sset _b0__7
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                          _FSb
                                                          (tarray tuchar 256))
                                                        (Ebinop Oand
                                                          (Etempvar _Y1 tuint)
                                                          (Econst_int (Int.repr 255) tint)
                                                          tuint)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Ssequence
                                                    (Sset _b1__7
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                            _FSb
                                                            (tarray tuchar 256))
                                                          (Ebinop Oand
                                                            (Ebinop Oshr
                                                              (Etempvar _Y2 tuint)
                                                              (Econst_int (Int.repr 8) tint)
                                                              tuint)
                                                            (Econst_int (Int.repr 255) tint)
                                                            tuint)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Ssequence
                                                      (Sset _b2__7
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                              _FSb
                                                              (tarray tuchar 256))
                                                            (Ebinop Oand
                                                              (Ebinop Oshr
                                                                (Etempvar _Y3 tuint)
                                                                (Econst_int (Int.repr 16) tint)
                                                                tuint)
                                                              (Econst_int (Int.repr 255) tint)
                                                              tuint)
                                                            (tptr tuchar))
                                                          tuchar))
                                                      (Ssequence
                                                        (Sset _b3__7
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                _FSb
                                                                (tarray tuchar 256))
                                                              (Ebinop Oand
                                                                (Ebinop Oshr
                                                                  (Etempvar _Y0 tuint)
                                                                  (Econst_int (Int.repr 24) tint)
                                                                  tuint)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tuint)
                                                              (tptr tuchar))
                                                            tuchar))
                                                        (Ssequence
                                                          (Sset _X1
                                                            (Ebinop Oxor
                                                              (Ebinop Oxor
                                                                (Ebinop Oxor
                                                                  (Ebinop Oxor
                                                                    (Etempvar _rk__3 tuint)
                                                                    (Etempvar _b0__7 tuint)
                                                                    tuint)
                                                                  (Ebinop Oshl
                                                                    (Etempvar _b1__7 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                  tuint)
                                                                (Ebinop Oshl
                                                                  (Etempvar _b2__7 tuint)
                                                                  (Econst_int (Int.repr 16) tint)
                                                                  tuint)
                                                                tuint)
                                                              (Ebinop Oshl
                                                                (Etempvar _b3__7 tuint)
                                                                (Econst_int (Int.repr 24) tint)
                                                                tuint) tuint))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'19
                                                                  (Etempvar _RK (tptr tuint)))
                                                                (Sset _RK
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'19 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                              (Sset _rk__3
                                                                (Ederef
                                                                  (Etempvar _t'19 (tptr tuint))
                                                                  tuint)))
                                                            (Ssequence
                                                              (Sset _b0__7
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _Y2 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                  tuchar))
                                                              (Ssequence
                                                                (Sset _b1__7
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y3 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                (Ssequence
                                                                  (Sset _b2__7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y0 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                  (Ssequence
                                                                    (Sset _b3__7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y1 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _X2
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__3 tuint)
                                                                    (Etempvar _b0__7 tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b1__7 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b2__7 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b3__7 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'20
                                                                    (Etempvar _RK (tptr tuint)))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'20 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                                    (Sset _rk__3
                                                                    (Ederef
                                                                    (Etempvar _t'20 (tptr tuint))
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _b0__7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _Y3 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _b1__7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y0 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _b2__7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y1 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _b3__7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _FSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y2 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _X3
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__3 tuint)
                                                                    (Etempvar _b0__7 tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b1__7 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b2__7 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b3__7 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    tuint)))))))))))))))))))))))))
                                  (Ssequence
                                    (Ssequence
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _output (tptr tuchar))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr tuchar)) tuchar)
                                        (Ecast
                                          (Ebinop Oand (Etempvar _X0 tuint)
                                            (Econst_int (Int.repr 255) tint)
                                            tuint) tuchar))
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _output (tptr tuchar))
                                              (Ebinop Oadd
                                                (Econst_int (Int.repr 0) tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint) (tptr tuchar)) tuchar)
                                          (Ecast
                                            (Ebinop Oand
                                              (Ebinop Oshr
                                                (Etempvar _X0 tuint)
                                                (Econst_int (Int.repr 8) tint)
                                                tuint)
                                              (Econst_int (Int.repr 255) tint)
                                              tuint) tuchar))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _output (tptr tuchar))
                                                (Ebinop Oadd
                                                  (Econst_int (Int.repr 0) tint)
                                                  (Econst_int (Int.repr 2) tint)
                                                  tint) (tptr tuchar))
                                              tuchar)
                                            (Ecast
                                              (Ebinop Oand
                                                (Ebinop Oshr
                                                  (Etempvar _X0 tuint)
                                                  (Econst_int (Int.repr 16) tint)
                                                  tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) tuchar))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _output (tptr tuchar))
                                                (Ebinop Oadd
                                                  (Econst_int (Int.repr 0) tint)
                                                  (Econst_int (Int.repr 3) tint)
                                                  tint) (tptr tuchar))
                                              tuchar)
                                            (Ecast
                                              (Ebinop Oand
                                                (Ebinop Oshr
                                                  (Etempvar _X0 tuint)
                                                  (Econst_int (Int.repr 24) tint)
                                                  tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) tuchar)))))
                                    (Ssequence
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _output (tptr tuchar))
                                              (Econst_int (Int.repr 4) tint)
                                              (tptr tuchar)) tuchar)
                                          (Ecast
                                            (Ebinop Oand (Etempvar _X1 tuint)
                                              (Econst_int (Int.repr 255) tint)
                                              tuint) tuchar))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _output (tptr tuchar))
                                                (Ebinop Oadd
                                                  (Econst_int (Int.repr 4) tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint) (tptr tuchar))
                                              tuchar)
                                            (Ecast
                                              (Ebinop Oand
                                                (Ebinop Oshr
                                                  (Etempvar _X1 tuint)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) tuchar))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _output (tptr tuchar))
                                                  (Ebinop Oadd
                                                    (Econst_int (Int.repr 4) tint)
                                                    (Econst_int (Int.repr 2) tint)
                                                    tint) (tptr tuchar))
                                                tuchar)
                                              (Ecast
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _X1 tuint)
                                                    (Econst_int (Int.repr 16) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) tuchar))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _output (tptr tuchar))
                                                  (Ebinop Oadd
                                                    (Econst_int (Int.repr 4) tint)
                                                    (Econst_int (Int.repr 3) tint)
                                                    tint) (tptr tuchar))
                                                tuchar)
                                              (Ecast
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _X1 tuint)
                                                    (Econst_int (Int.repr 24) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) tuchar)))))
                                      (Ssequence
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _output (tptr tuchar))
                                                (Econst_int (Int.repr 8) tint)
                                                (tptr tuchar)) tuchar)
                                            (Ecast
                                              (Ebinop Oand
                                                (Etempvar _X2 tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) tuchar))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _output (tptr tuchar))
                                                  (Ebinop Oadd
                                                    (Econst_int (Int.repr 8) tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint) (tptr tuchar))
                                                tuchar)
                                              (Ecast
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _X2 tuint)
                                                    (Econst_int (Int.repr 8) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) tuchar))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _output (tptr tuchar))
                                                    (Ebinop Oadd
                                                      (Econst_int (Int.repr 8) tint)
                                                      (Econst_int (Int.repr 2) tint)
                                                      tint) (tptr tuchar))
                                                  tuchar)
                                                (Ecast
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _X2 tuint)
                                                      (Econst_int (Int.repr 16) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) tuchar))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _output (tptr tuchar))
                                                    (Ebinop Oadd
                                                      (Econst_int (Int.repr 8) tint)
                                                      (Econst_int (Int.repr 3) tint)
                                                      tint) (tptr tuchar))
                                                  tuchar)
                                                (Ecast
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _X2 tuint)
                                                      (Econst_int (Int.repr 24) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) tuchar)))))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _output (tptr tuchar))
                                                (Econst_int (Int.repr 12) tint)
                                                (tptr tuchar)) tuchar)
                                            (Ecast
                                              (Ebinop Oand
                                                (Etempvar _X3 tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) tuchar))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _output (tptr tuchar))
                                                  (Ebinop Oadd
                                                    (Econst_int (Int.repr 12) tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint) (tptr tuchar))
                                                tuchar)
                                              (Ecast
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _X3 tuint)
                                                    (Econst_int (Int.repr 8) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) tuchar))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _output (tptr tuchar))
                                                    (Ebinop Oadd
                                                      (Econst_int (Int.repr 12) tint)
                                                      (Econst_int (Int.repr 2) tint)
                                                      tint) (tptr tuchar))
                                                  tuchar)
                                                (Ecast
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _X3 tuint)
                                                      (Econst_int (Int.repr 16) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) tuchar))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _output (tptr tuchar))
                                                    (Ebinop Oadd
                                                      (Econst_int (Int.repr 12) tint)
                                                      (Econst_int (Int.repr 3) tint)
                                                      tint) (tptr tuchar))
                                                  tuchar)
                                                (Ecast
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _X3 tuint)
                                                      (Econst_int (Int.repr 24) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) tuchar)))))))))))))))))))))))))
|}.

Definition f_mbedtls_aes_decrypt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                (_input, (tptr tuchar)) :: (_output, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_RK, (tptr tuint)) :: (_X0, tuint) ::
               (_X1, tuint) :: (_X2, tuint) :: (_X3, tuint) ::
               (_Y0, tuint) :: (_Y1, tuint) :: (_Y2, tuint) ::
               (_Y3, tuint) :: (_tmp, tuint) :: (_b0, tuint) ::
               (_b1, tuint) :: (_b2, tuint) :: (_b3, tuint) ::
               (_b0__1, tuint) :: (_b1__1, tuint) :: (_b2__1, tuint) ::
               (_b3__1, tuint) :: (_b0__2, tuint) :: (_b1__2, tuint) ::
               (_b2__2, tuint) :: (_b3__2, tuint) :: (_b0__3, tuint) ::
               (_b1__3, tuint) :: (_b2__3, tuint) :: (_b3__3, tuint) ::
               (_rk, tuint) :: (_b0__4, tuint) :: (_b1__4, tuint) ::
               (_b2__4, tuint) :: (_b3__4, tuint) :: (_rk__1, tuint) ::
               (_b0__5, tuint) :: (_b1__5, tuint) :: (_b2__5, tuint) ::
               (_b3__5, tuint) :: (_rk__2, tuint) :: (_b0__6, tuint) ::
               (_b1__6, tuint) :: (_b2__6, tuint) :: (_b3__6, tuint) ::
               (_rk__3, tuint) :: (_b0__7, tuint) :: (_b1__7, tuint) ::
               (_b2__7, tuint) :: (_b3__7, tuint) :: (_t'20, (tptr tuint)) ::
               (_t'19, (tptr tuint)) :: (_t'18, (tptr tuint)) ::
               (_t'17, (tptr tuint)) :: (_t'16, (tptr tuint)) ::
               (_t'15, (tptr tuint)) :: (_t'14, (tptr tuint)) ::
               (_t'13, (tptr tuint)) :: (_t'12, (tptr tuint)) ::
               (_t'11, (tptr tuint)) :: (_t'10, (tptr tuint)) ::
               (_t'9, (tptr tuint)) :: (_t'8, (tptr tuint)) ::
               (_t'7, (tptr tuint)) :: (_t'6, (tptr tuint)) ::
               (_t'5, (tptr tuint)) :: (_t'4, (tptr tuint)) ::
               (_t'3, (tptr tuint)) :: (_t'2, (tptr tuint)) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _RK
    (Efield
      (Ederef
        (Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr)))
        (Tstruct _mbedtls_aes_context_struct noattr)) _rk (tptr tuint)))
  (Ssequence
    (Ssequence
      (Sset _b0
        (Ecast
          (Ederef
            (Ebinop Oadd (Etempvar _input (tptr tuchar))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar) tuint))
      (Ssequence
        (Sset _b1
          (Ecast
            (Ederef
              (Ebinop Oadd (Etempvar _input (tptr tuchar))
                (Ebinop Oadd (Econst_int (Int.repr 0) tint)
                  (Econst_int (Int.repr 1) tint) tint) (tptr tuchar)) tuchar)
            tuint))
        (Ssequence
          (Sset _b2
            (Ecast
              (Ederef
                (Ebinop Oadd (Etempvar _input (tptr tuchar))
                  (Ebinop Oadd (Econst_int (Int.repr 0) tint)
                    (Econst_int (Int.repr 2) tint) tint) (tptr tuchar))
                tuchar) tuint))
          (Ssequence
            (Sset _b3
              (Ecast
                (Ederef
                  (Ebinop Oadd (Etempvar _input (tptr tuchar))
                    (Ebinop Oadd (Econst_int (Int.repr 0) tint)
                      (Econst_int (Int.repr 3) tint) tint) (tptr tuchar))
                  tuchar) tuint))
            (Sset _X0
              (Ebinop Oor
                (Ebinop Oor
                  (Ebinop Oor (Etempvar _b0 tuint)
                    (Ebinop Oshl (Etempvar _b1 tuint)
                      (Econst_int (Int.repr 8) tint) tuint) tuint)
                  (Ebinop Oshl (Etempvar _b2 tuint)
                    (Econst_int (Int.repr 16) tint) tuint) tuint)
                (Ebinop Oshl (Etempvar _b3 tuint)
                  (Econst_int (Int.repr 24) tint) tuint) tuint))))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'1 (Etempvar _RK (tptr tuint)))
          (Sset _RK
            (Ebinop Oadd (Etempvar _t'1 (tptr tuint))
              (Econst_int (Int.repr 1) tint) (tptr tuint))))
        (Sset _tmp (Ederef (Etempvar _t'1 (tptr tuint)) tuint)))
      (Ssequence
        (Sset _X0
          (Ebinop Oxor (Etempvar _X0 tuint) (Etempvar _tmp tuint) tuint))
        (Ssequence
          (Ssequence
            (Sset _b0__1
              (Ecast
                (Ederef
                  (Ebinop Oadd (Etempvar _input (tptr tuchar))
                    (Econst_int (Int.repr 4) tint) (tptr tuchar)) tuchar)
                tuint))
            (Ssequence
              (Sset _b1__1
                (Ecast
                  (Ederef
                    (Ebinop Oadd (Etempvar _input (tptr tuchar))
                      (Ebinop Oadd (Econst_int (Int.repr 4) tint)
                        (Econst_int (Int.repr 1) tint) tint) (tptr tuchar))
                    tuchar) tuint))
              (Ssequence
                (Sset _b2__1
                  (Ecast
                    (Ederef
                      (Ebinop Oadd (Etempvar _input (tptr tuchar))
                        (Ebinop Oadd (Econst_int (Int.repr 4) tint)
                          (Econst_int (Int.repr 2) tint) tint) (tptr tuchar))
                      tuchar) tuint))
                (Ssequence
                  (Sset _b3__1
                    (Ecast
                      (Ederef
                        (Ebinop Oadd (Etempvar _input (tptr tuchar))
                          (Ebinop Oadd (Econst_int (Int.repr 4) tint)
                            (Econst_int (Int.repr 3) tint) tint)
                          (tptr tuchar)) tuchar) tuint))
                  (Sset _X1
                    (Ebinop Oor
                      (Ebinop Oor
                        (Ebinop Oor (Etempvar _b0__1 tuint)
                          (Ebinop Oshl (Etempvar _b1__1 tuint)
                            (Econst_int (Int.repr 8) tint) tuint) tuint)
                        (Ebinop Oshl (Etempvar _b2__1 tuint)
                          (Econst_int (Int.repr 16) tint) tuint) tuint)
                      (Ebinop Oshl (Etempvar _b3__1 tuint)
                        (Econst_int (Int.repr 24) tint) tuint) tuint))))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'2 (Etempvar _RK (tptr tuint)))
                (Sset _RK
                  (Ebinop Oadd (Etempvar _t'2 (tptr tuint))
                    (Econst_int (Int.repr 1) tint) (tptr tuint))))
              (Sset _tmp (Ederef (Etempvar _t'2 (tptr tuint)) tuint)))
            (Ssequence
              (Sset _X1
                (Ebinop Oxor (Etempvar _X1 tuint) (Etempvar _tmp tuint)
                  tuint))
              (Ssequence
                (Ssequence
                  (Sset _b0__2
                    (Ecast
                      (Ederef
                        (Ebinop Oadd (Etempvar _input (tptr tuchar))
                          (Econst_int (Int.repr 8) tint) (tptr tuchar))
                        tuchar) tuint))
                  (Ssequence
                    (Sset _b1__2
                      (Ecast
                        (Ederef
                          (Ebinop Oadd (Etempvar _input (tptr tuchar))
                            (Ebinop Oadd (Econst_int (Int.repr 8) tint)
                              (Econst_int (Int.repr 1) tint) tint)
                            (tptr tuchar)) tuchar) tuint))
                    (Ssequence
                      (Sset _b2__2
                        (Ecast
                          (Ederef
                            (Ebinop Oadd (Etempvar _input (tptr tuchar))
                              (Ebinop Oadd (Econst_int (Int.repr 8) tint)
                                (Econst_int (Int.repr 2) tint) tint)
                              (tptr tuchar)) tuchar) tuint))
                      (Ssequence
                        (Sset _b3__2
                          (Ecast
                            (Ederef
                              (Ebinop Oadd (Etempvar _input (tptr tuchar))
                                (Ebinop Oadd (Econst_int (Int.repr 8) tint)
                                  (Econst_int (Int.repr 3) tint) tint)
                                (tptr tuchar)) tuchar) tuint))
                        (Sset _X2
                          (Ebinop Oor
                            (Ebinop Oor
                              (Ebinop Oor (Etempvar _b0__2 tuint)
                                (Ebinop Oshl (Etempvar _b1__2 tuint)
                                  (Econst_int (Int.repr 8) tint) tuint)
                                tuint)
                              (Ebinop Oshl (Etempvar _b2__2 tuint)
                                (Econst_int (Int.repr 16) tint) tuint) tuint)
                            (Ebinop Oshl (Etempvar _b3__2 tuint)
                              (Econst_int (Int.repr 24) tint) tuint) tuint))))))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'3 (Etempvar _RK (tptr tuint)))
                      (Sset _RK
                        (Ebinop Oadd (Etempvar _t'3 (tptr tuint))
                          (Econst_int (Int.repr 1) tint) (tptr tuint))))
                    (Sset _tmp (Ederef (Etempvar _t'3 (tptr tuint)) tuint)))
                  (Ssequence
                    (Sset _X2
                      (Ebinop Oxor (Etempvar _X2 tuint) (Etempvar _tmp tuint)
                        tuint))
                    (Ssequence
                      (Ssequence
                        (Sset _b0__3
                          (Ecast
                            (Ederef
                              (Ebinop Oadd (Etempvar _input (tptr tuchar))
                                (Econst_int (Int.repr 12) tint)
                                (tptr tuchar)) tuchar) tuint))
                        (Ssequence
                          (Sset _b1__3
                            (Ecast
                              (Ederef
                                (Ebinop Oadd (Etempvar _input (tptr tuchar))
                                  (Ebinop Oadd
                                    (Econst_int (Int.repr 12) tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  (tptr tuchar)) tuchar) tuint))
                          (Ssequence
                            (Sset _b2__3
                              (Ecast
                                (Ederef
                                  (Ebinop Oadd
                                    (Etempvar _input (tptr tuchar))
                                    (Ebinop Oadd
                                      (Econst_int (Int.repr 12) tint)
                                      (Econst_int (Int.repr 2) tint) tint)
                                    (tptr tuchar)) tuchar) tuint))
                            (Ssequence
                              (Sset _b3__3
                                (Ecast
                                  (Ederef
                                    (Ebinop Oadd
                                      (Etempvar _input (tptr tuchar))
                                      (Ebinop Oadd
                                        (Econst_int (Int.repr 12) tint)
                                        (Econst_int (Int.repr 3) tint) tint)
                                      (tptr tuchar)) tuchar) tuint))
                              (Sset _X3
                                (Ebinop Oor
                                  (Ebinop Oor
                                    (Ebinop Oor (Etempvar _b0__3 tuint)
                                      (Ebinop Oshl (Etempvar _b1__3 tuint)
                                        (Econst_int (Int.repr 8) tint) tuint)
                                      tuint)
                                    (Ebinop Oshl (Etempvar _b2__3 tuint)
                                      (Econst_int (Int.repr 16) tint) tuint)
                                    tuint)
                                  (Ebinop Oshl (Etempvar _b3__3 tuint)
                                    (Econst_int (Int.repr 24) tint) tuint)
                                  tuint))))))
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sset _t'4 (Etempvar _RK (tptr tuint)))
                            (Sset _RK
                              (Ebinop Oadd (Etempvar _t'4 (tptr tuint))
                                (Econst_int (Int.repr 1) tint) (tptr tuint))))
                          (Sset _tmp
                            (Ederef (Etempvar _t'4 (tptr tuint)) tuint)))
                        (Ssequence
                          (Sset _X3
                            (Ebinop Oxor (Etempvar _X3 tuint)
                              (Etempvar _tmp tuint) tuint))
                          (Ssequence
                            (Sset _tmp
                              (Efield
                                (Ederef
                                  (Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr)))
                                  (Tstruct _mbedtls_aes_context_struct noattr))
                                _nr tint))
                            (Ssequence
                              (Ssequence
                                (Sset _i
                                  (Ebinop Osub
                                    (Ebinop Oshr (Etempvar _tmp tuint)
                                      (Econst_int (Int.repr 1) tint) tuint)
                                    (Econst_int (Int.repr 1) tint) tuint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Ogt
                                                   (Etempvar _i tint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'5
                                              (Etempvar _RK (tptr tuint)))
                                            (Sset _RK
                                              (Ebinop Oadd
                                                (Etempvar _t'5 (tptr tuint))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr tuint))))
                                          (Sset _rk
                                            (Ederef
                                              (Etempvar _t'5 (tptr tuint))
                                              tuint)))
                                        (Ssequence
                                          (Sset _b0__4
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                  _RT0 (tarray tuint 256))
                                                (Ebinop Oand
                                                  (Etempvar _X0 tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) (tptr tuint)) tuint))
                                          (Ssequence
                                            (Sset _b1__4
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                    _RT1 (tarray tuint 256))
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _X3 tuint)
                                                      (Econst_int (Int.repr 8) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) (tptr tuint))
                                                tuint))
                                            (Ssequence
                                              (Sset _b2__4
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                      _RT2
                                                      (tarray tuint 256))
                                                    (Ebinop Oand
                                                      (Ebinop Oshr
                                                        (Etempvar _X2 tuint)
                                                        (Econst_int (Int.repr 16) tint)
                                                        tuint)
                                                      (Econst_int (Int.repr 255) tint)
                                                      tuint) (tptr tuint))
                                                  tuint))
                                              (Ssequence
                                                (Sset _b3__4
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                        _RT3
                                                        (tarray tuint 256))
                                                      (Ebinop Oand
                                                        (Ebinop Oshr
                                                          (Etempvar _X1 tuint)
                                                          (Econst_int (Int.repr 24) tint)
                                                          tuint)
                                                        (Econst_int (Int.repr 255) tint)
                                                        tuint) (tptr tuint))
                                                    tuint))
                                                (Ssequence
                                                  (Sset _Y0
                                                    (Ebinop Oxor
                                                      (Ebinop Oxor
                                                        (Ebinop Oxor
                                                          (Ebinop Oxor
                                                            (Etempvar _rk tuint)
                                                            (Etempvar _b0__4 tuint)
                                                            tuint)
                                                          (Etempvar _b1__4 tuint)
                                                          tuint)
                                                        (Etempvar _b2__4 tuint)
                                                        tuint)
                                                      (Etempvar _b3__4 tuint)
                                                      tuint))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'6
                                                          (Etempvar _RK (tptr tuint)))
                                                        (Sset _RK
                                                          (Ebinop Oadd
                                                            (Etempvar _t'6 (tptr tuint))
                                                            (Econst_int (Int.repr 1) tint)
                                                            (tptr tuint))))
                                                      (Sset _rk
                                                        (Ederef
                                                          (Etempvar _t'6 (tptr tuint))
                                                          tuint)))
                                                    (Ssequence
                                                      (Sset _b0__4
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                              _RT0
                                                              (tarray tuint 256))
                                                            (Ebinop Oand
                                                              (Etempvar _X1 tuint)
                                                              (Econst_int (Int.repr 255) tint)
                                                              tuint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _b1__4
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                _RT1
                                                                (tarray tuint 256))
                                                              (Ebinop Oand
                                                                (Ebinop Oshr
                                                                  (Etempvar _X0 tuint)
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  tuint)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tuint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _b2__4
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                  _RT2
                                                                  (tarray tuint 256))
                                                                (Ebinop Oand
                                                                  (Ebinop Oshr
                                                                    (Etempvar _X3 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                  (Econst_int (Int.repr 255) tint)
                                                                  tuint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _b3__4
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT3
                                                                    (tarray tuint 256))
                                                                  (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X2 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _Y1
                                                                (Ebinop Oxor
                                                                  (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk tuint)
                                                                    (Etempvar _b0__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__4 tuint)
                                                                    tuint)
                                                                  (Etempvar _b3__4 tuint)
                                                                  tuint))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'7
                                                                    (Etempvar _RK (tptr tuint)))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'7 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                                  (Sset _rk
                                                                    (Ederef
                                                                    (Etempvar _t'7 (tptr tuint))
                                                                    tuint)))
                                                                (Ssequence
                                                                  (Sset _b0__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT0
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _X2 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _b1__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT1
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X1 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b2__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT2
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X0 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b3__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT3
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X3 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _Y2
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk tuint)
                                                                    (Etempvar _b0__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b3__4 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'8
                                                                    (Etempvar _RK (tptr tuint)))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'8 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                                    (Sset _rk
                                                                    (Ederef
                                                                    (Etempvar _t'8 (tptr tuint))
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _b0__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT0
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _X3 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b1__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT1
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X2 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b2__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT2
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X1 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b3__4
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT3
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X0 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _Y3
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk tuint)
                                                                    (Etempvar _b0__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__4 tuint)
                                                                    tuint)
                                                                    (Etempvar _b3__4 tuint)
                                                                    tuint)))))))))))))))))))))))))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'9
                                              (Etempvar _RK (tptr tuint)))
                                            (Sset _RK
                                              (Ebinop Oadd
                                                (Etempvar _t'9 (tptr tuint))
                                                (Econst_int (Int.repr 1) tint)
                                                (tptr tuint))))
                                          (Sset _rk__1
                                            (Ederef
                                              (Etempvar _t'9 (tptr tuint))
                                              tuint)))
                                        (Ssequence
                                          (Sset _b0__5
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                  _RT0 (tarray tuint 256))
                                                (Ebinop Oand
                                                  (Etempvar _Y0 tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) (tptr tuint)) tuint))
                                          (Ssequence
                                            (Sset _b1__5
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                    _RT1 (tarray tuint 256))
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _Y3 tuint)
                                                      (Econst_int (Int.repr 8) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) (tptr tuint))
                                                tuint))
                                            (Ssequence
                                              (Sset _b2__5
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                      _RT2
                                                      (tarray tuint 256))
                                                    (Ebinop Oand
                                                      (Ebinop Oshr
                                                        (Etempvar _Y2 tuint)
                                                        (Econst_int (Int.repr 16) tint)
                                                        tuint)
                                                      (Econst_int (Int.repr 255) tint)
                                                      tuint) (tptr tuint))
                                                  tuint))
                                              (Ssequence
                                                (Sset _b3__5
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                        _RT3
                                                        (tarray tuint 256))
                                                      (Ebinop Oand
                                                        (Ebinop Oshr
                                                          (Etempvar _Y1 tuint)
                                                          (Econst_int (Int.repr 24) tint)
                                                          tuint)
                                                        (Econst_int (Int.repr 255) tint)
                                                        tuint) (tptr tuint))
                                                    tuint))
                                                (Ssequence
                                                  (Sset _X0
                                                    (Ebinop Oxor
                                                      (Ebinop Oxor
                                                        (Ebinop Oxor
                                                          (Ebinop Oxor
                                                            (Etempvar _rk__1 tuint)
                                                            (Etempvar _b0__5 tuint)
                                                            tuint)
                                                          (Etempvar _b1__5 tuint)
                                                          tuint)
                                                        (Etempvar _b2__5 tuint)
                                                        tuint)
                                                      (Etempvar _b3__5 tuint)
                                                      tuint))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'10
                                                          (Etempvar _RK (tptr tuint)))
                                                        (Sset _RK
                                                          (Ebinop Oadd
                                                            (Etempvar _t'10 (tptr tuint))
                                                            (Econst_int (Int.repr 1) tint)
                                                            (tptr tuint))))
                                                      (Sset _rk__1
                                                        (Ederef
                                                          (Etempvar _t'10 (tptr tuint))
                                                          tuint)))
                                                    (Ssequence
                                                      (Sset _b0__5
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                              _RT0
                                                              (tarray tuint 256))
                                                            (Ebinop Oand
                                                              (Etempvar _Y1 tuint)
                                                              (Econst_int (Int.repr 255) tint)
                                                              tuint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _b1__5
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                _RT1
                                                                (tarray tuint 256))
                                                              (Ebinop Oand
                                                                (Ebinop Oshr
                                                                  (Etempvar _Y0 tuint)
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  tuint)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tuint)
                                                              (tptr tuint))
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _b2__5
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                  _RT2
                                                                  (tarray tuint 256))
                                                                (Ebinop Oand
                                                                  (Ebinop Oshr
                                                                    (Etempvar _Y3 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                  (Econst_int (Int.repr 255) tint)
                                                                  tuint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _b3__5
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT3
                                                                    (tarray tuint 256))
                                                                  (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y2 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _X1
                                                                (Ebinop Oxor
                                                                  (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__1 tuint)
                                                                    (Etempvar _b0__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__5 tuint)
                                                                    tuint)
                                                                  (Etempvar _b3__5 tuint)
                                                                  tuint))
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Sset _t'11
                                                                    (Etempvar _RK (tptr tuint)))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'11 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                                  (Sset _rk__1
                                                                    (Ederef
                                                                    (Etempvar _t'11 (tptr tuint))
                                                                    tuint)))
                                                                (Ssequence
                                                                  (Sset _b0__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT0
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _Y2 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _b1__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT1
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y1 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b2__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT2
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y0 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b3__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT3
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y3 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _X2
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__1 tuint)
                                                                    (Etempvar _b0__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b3__5 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'12
                                                                    (Etempvar _RK (tptr tuint)))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'12 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                                    (Sset _rk__1
                                                                    (Ederef
                                                                    (Etempvar _t'12 (tptr tuint))
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _b0__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT0
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _Y3 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b1__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT1
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y2 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b2__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT2
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y1 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b3__5
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT3
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y0 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _X3
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__1 tuint)
                                                                    (Etempvar _b0__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__5 tuint)
                                                                    tuint)
                                                                    (Etempvar _b3__5 tuint)
                                                                    tuint)))))))))))))))))))))))))))
                                  (Sset _i
                                    (Ebinop Osub (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint))))
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'13
                                        (Etempvar _RK (tptr tuint)))
                                      (Sset _RK
                                        (Ebinop Oadd
                                          (Etempvar _t'13 (tptr tuint))
                                          (Econst_int (Int.repr 1) tint)
                                          (tptr tuint))))
                                    (Sset _rk__2
                                      (Ederef (Etempvar _t'13 (tptr tuint))
                                        tuint)))
                                  (Ssequence
                                    (Sset _b0__6
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Evar _tables (Tstruct _aes_tables_struct noattr))
                                            _RT0 (tarray tuint 256))
                                          (Ebinop Oand (Etempvar _X0 tuint)
                                            (Econst_int (Int.repr 255) tint)
                                            tuint) (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sset _b1__6
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                              _RT1 (tarray tuint 256))
                                            (Ebinop Oand
                                              (Ebinop Oshr
                                                (Etempvar _X3 tuint)
                                                (Econst_int (Int.repr 8) tint)
                                                tuint)
                                              (Econst_int (Int.repr 255) tint)
                                              tuint) (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sset _b2__6
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                _RT2 (tarray tuint 256))
                                              (Ebinop Oand
                                                (Ebinop Oshr
                                                  (Etempvar _X2 tuint)
                                                  (Econst_int (Int.repr 16) tint)
                                                  tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) (tptr tuint)) tuint))
                                        (Ssequence
                                          (Sset _b3__6
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                  _RT3 (tarray tuint 256))
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _X1 tuint)
                                                    (Econst_int (Int.repr 24) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) (tptr tuint)) tuint))
                                          (Ssequence
                                            (Sset _Y0
                                              (Ebinop Oxor
                                                (Ebinop Oxor
                                                  (Ebinop Oxor
                                                    (Ebinop Oxor
                                                      (Etempvar _rk__2 tuint)
                                                      (Etempvar _b0__6 tuint)
                                                      tuint)
                                                    (Etempvar _b1__6 tuint)
                                                    tuint)
                                                  (Etempvar _b2__6 tuint)
                                                  tuint)
                                                (Etempvar _b3__6 tuint)
                                                tuint))
                                            (Ssequence
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'14
                                                    (Etempvar _RK (tptr tuint)))
                                                  (Sset _RK
                                                    (Ebinop Oadd
                                                      (Etempvar _t'14 (tptr tuint))
                                                      (Econst_int (Int.repr 1) tint)
                                                      (tptr tuint))))
                                                (Sset _rk__2
                                                  (Ederef
                                                    (Etempvar _t'14 (tptr tuint))
                                                    tuint)))
                                              (Ssequence
                                                (Sset _b0__6
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                        _RT0
                                                        (tarray tuint 256))
                                                      (Ebinop Oand
                                                        (Etempvar _X1 tuint)
                                                        (Econst_int (Int.repr 255) tint)
                                                        tuint) (tptr tuint))
                                                    tuint))
                                                (Ssequence
                                                  (Sset _b1__6
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                          _RT1
                                                          (tarray tuint 256))
                                                        (Ebinop Oand
                                                          (Ebinop Oshr
                                                            (Etempvar _X0 tuint)
                                                            (Econst_int (Int.repr 8) tint)
                                                            tuint)
                                                          (Econst_int (Int.repr 255) tint)
                                                          tuint)
                                                        (tptr tuint)) tuint))
                                                  (Ssequence
                                                    (Sset _b2__6
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                            _RT2
                                                            (tarray tuint 256))
                                                          (Ebinop Oand
                                                            (Ebinop Oshr
                                                              (Etempvar _X3 tuint)
                                                              (Econst_int (Int.repr 16) tint)
                                                              tuint)
                                                            (Econst_int (Int.repr 255) tint)
                                                            tuint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sset _b3__6
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                              _RT3
                                                              (tarray tuint 256))
                                                            (Ebinop Oand
                                                              (Ebinop Oshr
                                                                (Etempvar _X2 tuint)
                                                                (Econst_int (Int.repr 24) tint)
                                                                tuint)
                                                              (Econst_int (Int.repr 255) tint)
                                                              tuint)
                                                            (tptr tuint))
                                                          tuint))
                                                      (Ssequence
                                                        (Sset _Y1
                                                          (Ebinop Oxor
                                                            (Ebinop Oxor
                                                              (Ebinop Oxor
                                                                (Ebinop Oxor
                                                                  (Etempvar _rk__2 tuint)
                                                                  (Etempvar _b0__6 tuint)
                                                                  tuint)
                                                                (Etempvar _b1__6 tuint)
                                                                tuint)
                                                              (Etempvar _b2__6 tuint)
                                                              tuint)
                                                            (Etempvar _b3__6 tuint)
                                                            tuint))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Sset _t'15
                                                                (Etempvar _RK (tptr tuint)))
                                                              (Sset _RK
                                                                (Ebinop Oadd
                                                                  (Etempvar _t'15 (tptr tuint))
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  (tptr tuint))))
                                                            (Sset _rk__2
                                                              (Ederef
                                                                (Etempvar _t'15 (tptr tuint))
                                                                tuint)))
                                                          (Ssequence
                                                            (Sset _b0__6
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT0
                                                                    (tarray tuint 256))
                                                                  (Ebinop Oand
                                                                    (Etempvar _X2 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Ssequence
                                                              (Sset _b1__6
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT1
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X1 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                  tuint))
                                                              (Ssequence
                                                                (Sset _b2__6
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT2
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X0 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                (Ssequence
                                                                  (Sset _b3__6
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT3
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X3 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                  (Ssequence
                                                                    (Sset _Y2
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__2 tuint)
                                                                    (Etempvar _b0__6 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__6 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__6 tuint)
                                                                    tuint)
                                                                    (Etempvar _b3__6 tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'16
                                                                    (Etempvar _RK (tptr tuint)))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'16 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                                    (Sset _rk__2
                                                                    (Ederef
                                                                    (Etempvar _t'16 (tptr tuint))
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _b0__6
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT0
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _X3 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b1__6
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT1
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X2 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b2__6
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT2
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X1 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _b3__6
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RT3
                                                                    (tarray tuint 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _X0 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuint))
                                                                    tuint))
                                                                    (Sset _Y3
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__2 tuint)
                                                                    (Etempvar _b0__6 tuint)
                                                                    tuint)
                                                                    (Etempvar _b1__6 tuint)
                                                                    tuint)
                                                                    (Etempvar _b2__6 tuint)
                                                                    tuint)
                                                                    (Etempvar _b3__6 tuint)
                                                                    tuint)))))))))))))))))))))))))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'17
                                          (Etempvar _RK (tptr tuint)))
                                        (Sset _RK
                                          (Ebinop Oadd
                                            (Etempvar _t'17 (tptr tuint))
                                            (Econst_int (Int.repr 1) tint)
                                            (tptr tuint))))
                                      (Sset _rk__3
                                        (Ederef (Etempvar _t'17 (tptr tuint))
                                          tuint)))
                                    (Ssequence
                                      (Sset _b0__7
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                              _RSb (tarray tuchar 256))
                                            (Ebinop Oand (Etempvar _Y0 tuint)
                                              (Econst_int (Int.repr 255) tint)
                                              tuint) (tptr tuchar)) tuchar))
                                      (Ssequence
                                        (Sset _b1__7
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                _RSb (tarray tuchar 256))
                                              (Ebinop Oand
                                                (Ebinop Oshr
                                                  (Etempvar _Y3 tuint)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) (tptr tuchar)) tuchar))
                                        (Ssequence
                                          (Sset _b2__7
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                  _RSb (tarray tuchar 256))
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _Y2 tuint)
                                                    (Econst_int (Int.repr 16) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) (tptr tuchar))
                                              tuchar))
                                          (Ssequence
                                            (Sset _b3__7
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                    _RSb (tarray tuchar 256))
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _Y1 tuint)
                                                      (Econst_int (Int.repr 24) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) (tptr tuchar))
                                                tuchar))
                                            (Ssequence
                                              (Sset _X0
                                                (Ebinop Oxor
                                                  (Ebinop Oxor
                                                    (Ebinop Oxor
                                                      (Ebinop Oxor
                                                        (Etempvar _rk__3 tuint)
                                                        (Etempvar _b0__7 tuint)
                                                        tuint)
                                                      (Ebinop Oshl
                                                        (Etempvar _b1__7 tuint)
                                                        (Econst_int (Int.repr 8) tint)
                                                        tuint) tuint)
                                                    (Ebinop Oshl
                                                      (Etempvar _b2__7 tuint)
                                                      (Econst_int (Int.repr 16) tint)
                                                      tuint) tuint)
                                                  (Ebinop Oshl
                                                    (Etempvar _b3__7 tuint)
                                                    (Econst_int (Int.repr 24) tint)
                                                    tuint) tuint))
                                              (Ssequence
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'18
                                                      (Etempvar _RK (tptr tuint)))
                                                    (Sset _RK
                                                      (Ebinop Oadd
                                                        (Etempvar _t'18 (tptr tuint))
                                                        (Econst_int (Int.repr 1) tint)
                                                        (tptr tuint))))
                                                  (Sset _rk__3
                                                    (Ederef
                                                      (Etempvar _t'18 (tptr tuint))
                                                      tuint)))
                                                (Ssequence
                                                  (Sset _b0__7
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                          _RSb
                                                          (tarray tuchar 256))
                                                        (Ebinop Oand
                                                          (Etempvar _Y1 tuint)
                                                          (Econst_int (Int.repr 255) tint)
                                                          tuint)
                                                        (tptr tuchar))
                                                      tuchar))
                                                  (Ssequence
                                                    (Sset _b1__7
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                            _RSb
                                                            (tarray tuchar 256))
                                                          (Ebinop Oand
                                                            (Ebinop Oshr
                                                              (Etempvar _Y0 tuint)
                                                              (Econst_int (Int.repr 8) tint)
                                                              tuint)
                                                            (Econst_int (Int.repr 255) tint)
                                                            tuint)
                                                          (tptr tuchar))
                                                        tuchar))
                                                    (Ssequence
                                                      (Sset _b2__7
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                              _RSb
                                                              (tarray tuchar 256))
                                                            (Ebinop Oand
                                                              (Ebinop Oshr
                                                                (Etempvar _Y3 tuint)
                                                                (Econst_int (Int.repr 16) tint)
                                                                tuint)
                                                              (Econst_int (Int.repr 255) tint)
                                                              tuint)
                                                            (tptr tuchar))
                                                          tuchar))
                                                      (Ssequence
                                                        (Sset _b3__7
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                _RSb
                                                                (tarray tuchar 256))
                                                              (Ebinop Oand
                                                                (Ebinop Oshr
                                                                  (Etempvar _Y2 tuint)
                                                                  (Econst_int (Int.repr 24) tint)
                                                                  tuint)
                                                                (Econst_int (Int.repr 255) tint)
                                                                tuint)
                                                              (tptr tuchar))
                                                            tuchar))
                                                        (Ssequence
                                                          (Sset _X1
                                                            (Ebinop Oxor
                                                              (Ebinop Oxor
                                                                (Ebinop Oxor
                                                                  (Ebinop Oxor
                                                                    (Etempvar _rk__3 tuint)
                                                                    (Etempvar _b0__7 tuint)
                                                                    tuint)
                                                                  (Ebinop Oshl
                                                                    (Etempvar _b1__7 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                  tuint)
                                                                (Ebinop Oshl
                                                                  (Etempvar _b2__7 tuint)
                                                                  (Econst_int (Int.repr 16) tint)
                                                                  tuint)
                                                                tuint)
                                                              (Ebinop Oshl
                                                                (Etempvar _b3__7 tuint)
                                                                (Econst_int (Int.repr 24) tint)
                                                                tuint) tuint))
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'19
                                                                  (Etempvar _RK (tptr tuint)))
                                                                (Sset _RK
                                                                  (Ebinop Oadd
                                                                    (Etempvar _t'19 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                              (Sset _rk__3
                                                                (Ederef
                                                                  (Etempvar _t'19 (tptr tuint))
                                                                  tuint)))
                                                            (Ssequence
                                                              (Sset _b0__7
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _Y2 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                  tuchar))
                                                              (Ssequence
                                                                (Sset _b1__7
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y1 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                (Ssequence
                                                                  (Sset _b2__7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y0 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                  (Ssequence
                                                                    (Sset _b3__7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y3 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _X2
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__3 tuint)
                                                                    (Etempvar _b0__7 tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b1__7 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b2__7 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b3__7 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'20
                                                                    (Etempvar _RK (tptr tuint)))
                                                                    (Sset _RK
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'20 (tptr tuint))
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (tptr tuint))))
                                                                    (Sset _rk__3
                                                                    (Ederef
                                                                    (Etempvar _t'20 (tptr tuint))
                                                                    tuint)))
                                                                    (Ssequence
                                                                    (Sset _b0__7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Etempvar _Y3 tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _b1__7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y2 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _b2__7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y1 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Ssequence
                                                                    (Sset _b3__7
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Evar _tables (Tstruct _aes_tables_struct noattr))
                                                                    _RSb
                                                                    (tarray tuchar 256))
                                                                    (Ebinop Oand
                                                                    (Ebinop Oshr
                                                                    (Etempvar _Y0 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tuint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sset _X3
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Ebinop Oxor
                                                                    (Etempvar _rk__3 tuint)
                                                                    (Etempvar _b0__7 tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b1__7 tuint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b2__7 tuint)
                                                                    (Econst_int (Int.repr 16) tint)
                                                                    tuint)
                                                                    tuint)
                                                                    (Ebinop Oshl
                                                                    (Etempvar _b3__7 tuint)
                                                                    (Econst_int (Int.repr 24) tint)
                                                                    tuint)
                                                                    tuint)))))))))))))))))))))))))
                                  (Ssequence
                                    (Ssequence
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _output (tptr tuchar))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr tuchar)) tuchar)
                                        (Ecast
                                          (Ebinop Oand (Etempvar _X0 tuint)
                                            (Econst_int (Int.repr 255) tint)
                                            tuint) tuchar))
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _output (tptr tuchar))
                                              (Ebinop Oadd
                                                (Econst_int (Int.repr 0) tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint) (tptr tuchar)) tuchar)
                                          (Ecast
                                            (Ebinop Oand
                                              (Ebinop Oshr
                                                (Etempvar _X0 tuint)
                                                (Econst_int (Int.repr 8) tint)
                                                tuint)
                                              (Econst_int (Int.repr 255) tint)
                                              tuint) tuchar))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _output (tptr tuchar))
                                                (Ebinop Oadd
                                                  (Econst_int (Int.repr 0) tint)
                                                  (Econst_int (Int.repr 2) tint)
                                                  tint) (tptr tuchar))
                                              tuchar)
                                            (Ecast
                                              (Ebinop Oand
                                                (Ebinop Oshr
                                                  (Etempvar _X0 tuint)
                                                  (Econst_int (Int.repr 16) tint)
                                                  tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) tuchar))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _output (tptr tuchar))
                                                (Ebinop Oadd
                                                  (Econst_int (Int.repr 0) tint)
                                                  (Econst_int (Int.repr 3) tint)
                                                  tint) (tptr tuchar))
                                              tuchar)
                                            (Ecast
                                              (Ebinop Oand
                                                (Ebinop Oshr
                                                  (Etempvar _X0 tuint)
                                                  (Econst_int (Int.repr 24) tint)
                                                  tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) tuchar)))))
                                    (Ssequence
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Etempvar _output (tptr tuchar))
                                              (Econst_int (Int.repr 4) tint)
                                              (tptr tuchar)) tuchar)
                                          (Ecast
                                            (Ebinop Oand (Etempvar _X1 tuint)
                                              (Econst_int (Int.repr 255) tint)
                                              tuint) tuchar))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _output (tptr tuchar))
                                                (Ebinop Oadd
                                                  (Econst_int (Int.repr 4) tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint) (tptr tuchar))
                                              tuchar)
                                            (Ecast
                                              (Ebinop Oand
                                                (Ebinop Oshr
                                                  (Etempvar _X1 tuint)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) tuchar))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _output (tptr tuchar))
                                                  (Ebinop Oadd
                                                    (Econst_int (Int.repr 4) tint)
                                                    (Econst_int (Int.repr 2) tint)
                                                    tint) (tptr tuchar))
                                                tuchar)
                                              (Ecast
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _X1 tuint)
                                                    (Econst_int (Int.repr 16) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) tuchar))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _output (tptr tuchar))
                                                  (Ebinop Oadd
                                                    (Econst_int (Int.repr 4) tint)
                                                    (Econst_int (Int.repr 3) tint)
                                                    tint) (tptr tuchar))
                                                tuchar)
                                              (Ecast
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _X1 tuint)
                                                    (Econst_int (Int.repr 24) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) tuchar)))))
                                      (Ssequence
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _output (tptr tuchar))
                                                (Econst_int (Int.repr 8) tint)
                                                (tptr tuchar)) tuchar)
                                            (Ecast
                                              (Ebinop Oand
                                                (Etempvar _X2 tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) tuchar))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _output (tptr tuchar))
                                                  (Ebinop Oadd
                                                    (Econst_int (Int.repr 8) tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint) (tptr tuchar))
                                                tuchar)
                                              (Ecast
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _X2 tuint)
                                                    (Econst_int (Int.repr 8) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) tuchar))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _output (tptr tuchar))
                                                    (Ebinop Oadd
                                                      (Econst_int (Int.repr 8) tint)
                                                      (Econst_int (Int.repr 2) tint)
                                                      tint) (tptr tuchar))
                                                  tuchar)
                                                (Ecast
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _X2 tuint)
                                                      (Econst_int (Int.repr 16) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) tuchar))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _output (tptr tuchar))
                                                    (Ebinop Oadd
                                                      (Econst_int (Int.repr 8) tint)
                                                      (Econst_int (Int.repr 3) tint)
                                                      tint) (tptr tuchar))
                                                  tuchar)
                                                (Ecast
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _X2 tuint)
                                                      (Econst_int (Int.repr 24) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) tuchar)))))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Etempvar _output (tptr tuchar))
                                                (Econst_int (Int.repr 12) tint)
                                                (tptr tuchar)) tuchar)
                                            (Ecast
                                              (Ebinop Oand
                                                (Etempvar _X3 tuint)
                                                (Econst_int (Int.repr 255) tint)
                                                tuint) tuchar))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Etempvar _output (tptr tuchar))
                                                  (Ebinop Oadd
                                                    (Econst_int (Int.repr 12) tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint) (tptr tuchar))
                                                tuchar)
                                              (Ecast
                                                (Ebinop Oand
                                                  (Ebinop Oshr
                                                    (Etempvar _X3 tuint)
                                                    (Econst_int (Int.repr 8) tint)
                                                    tuint)
                                                  (Econst_int (Int.repr 255) tint)
                                                  tuint) tuchar))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _output (tptr tuchar))
                                                    (Ebinop Oadd
                                                      (Econst_int (Int.repr 12) tint)
                                                      (Econst_int (Int.repr 2) tint)
                                                      tint) (tptr tuchar))
                                                  tuchar)
                                                (Ecast
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _X3 tuint)
                                                      (Econst_int (Int.repr 16) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) tuchar))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Etempvar _output (tptr tuchar))
                                                    (Ebinop Oadd
                                                      (Econst_int (Int.repr 12) tint)
                                                      (Econst_int (Int.repr 3) tint)
                                                      tint) (tptr tuchar))
                                                  tuchar)
                                                (Ecast
                                                  (Ebinop Oand
                                                    (Ebinop Oshr
                                                      (Etempvar _X3 tuint)
                                                      (Econst_int (Int.repr 24) tint)
                                                      tuint)
                                                    (Econst_int (Int.repr 255) tint)
                                                    tuint) tuchar)))))))))))))))))))))))))
|}.

Definition f_mbedtls_aes_crypt_ecb := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                (_mode, tint) :: (_input, (tptr tuchar)) ::
                (_output, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _mode tint)
                 (Econst_int (Int.repr 1) tint) tint)
    (Scall None
      (Evar _mbedtls_aes_encrypt (Tfunction
                                   (Tcons
                                     (tptr (Tstruct _mbedtls_aes_context_struct noattr))
                                     (Tcons (tptr tuchar)
                                       (Tcons (tptr tuchar) Tnil))) tvoid
                                   cc_default))
      ((Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
       (Etempvar _input (tptr tuchar)) :: (Etempvar _output (tptr tuchar)) ::
       nil))
    (Scall None
      (Evar _mbedtls_aes_decrypt (Tfunction
                                   (Tcons
                                     (tptr (Tstruct _mbedtls_aes_context_struct noattr))
                                     (Tcons (tptr tuchar)
                                       (Tcons (tptr tuchar) Tnil))) tvoid
                                   cc_default))
      ((Etempvar _ctx (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
       (Etempvar _input (tptr tuchar)) :: (Etempvar _output (tptr tuchar)) ::
       nil)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition v_aes_test_ecb_dec := {|
  gvar_info := (tarray (tarray tuchar 16) 3);
  gvar_init := (Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 106) :: Init_int8 (Int.repr 194) ::
                Init_int8 (Int.repr 209) :: Init_int8 (Int.repr 245) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 88) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 145) :: Init_int8 (Int.repr 126) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 233) ::
                Init_int8 (Int.repr 235) :: Init_int8 (Int.repr 224) ::
                Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 227) ::
                Init_int8 (Int.repr 30) :: Init_int8 (Int.repr 158) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 103) ::
                Init_int8 (Int.repr 24) :: Init_int8 (Int.repr 242) ::
                Init_int8 (Int.repr 146) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 156) ::
                Init_int8 (Int.repr 25) :: Init_int8 (Int.repr 241) ::
                Init_int8 (Int.repr 91) :: Init_int8 (Int.repr 164) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 140) ::
                Init_int8 (Int.repr 207) :: Init_int8 (Int.repr 253) ::
                Init_int8 (Int.repr 187) :: Init_int8 (Int.repr 203) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 31) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 86) :: Init_int8 (Int.repr 88) ::
                Init_int8 (Int.repr 93) :: Init_int8 (Int.repr 138) ::
                Init_int8 (Int.repr 74) :: Init_int8 (Int.repr 222) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_aes_test_ecb_enc := {|
  gvar_info := (tarray (tarray tuchar 16) 3);
  gvar_init := (Init_int8 (Int.repr 195) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 192) :: Init_int8 (Int.repr 218) ::
                Init_int8 (Int.repr 141) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 26) ::
                Init_int8 (Int.repr 254) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 190) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 127) ::
                Init_int8 (Int.repr 243) :: Init_int8 (Int.repr 246) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 42) ::
                Init_int8 (Int.repr 232) :: Init_int8 (Int.repr 215) ::
                Init_int8 (Int.repr 131) :: Init_int8 (Int.repr 17) ::
                Init_int8 (Int.repr 56) :: Init_int8 (Int.repr 240) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 86) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 177) :: Init_int8 (Int.repr 20) ::
                Init_int8 (Int.repr 139) :: Init_int8 (Int.repr 121) ::
                Init_int8 (Int.repr 238) :: Init_int8 (Int.repr 204) ::
                Init_int8 (Int.repr 147) :: Init_int8 (Int.repr 160) ::
                Init_int8 (Int.repr 238) :: Init_int8 (Int.repr 93) ::
                Init_int8 (Int.repr 255) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 180) :: Init_int8 (Int.repr 234) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 164) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_mbedtls_aes_self_test := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_verbose, tint) :: nil);
  fn_vars := ((_key, (tarray tuchar 32)) :: (_buf, (tarray tuchar 64)) ::
              (_iv, (tarray tuchar 16)) ::
              (_ctx, (Tstruct _mbedtls_aes_context_struct noattr)) :: nil);
  fn_temps := ((_ret, tint) :: (_i, tint) :: (_j, tint) :: (_u, tint) ::
               (_v, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _ret (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Scall None
      (Evar _memset (Tfunction
                      (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                      (tptr tvoid) cc_default))
      ((Evar _key (tarray tuchar 32)) :: (Econst_int (Int.repr 0) tint) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _mbedtls_aes_init (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _mbedtls_aes_context_struct noattr))
                                    Tnil) tvoid cc_default))
        ((Eaddrof (Evar _ctx (Tstruct _mbedtls_aes_context_struct noattr))
           (tptr (Tstruct _mbedtls_aes_context_struct noattr))) :: nil))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 6) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _u
                  (Ebinop Oshr (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))
                (Ssequence
                  (Sset _v
                    (Ebinop Oand (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))
                  (Ssequence
                    (Sifthenelse (Ebinop One (Etempvar _verbose tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq (Etempvar _v tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Sset _t'1
                            (Ecast (Evar ___stringlit_2 (tarray tschar 4))
                              (tptr tschar)))
                          (Sset _t'1
                            (Ecast (Evar ___stringlit_1 (tarray tschar 4))
                              (tptr tschar))))
                        (Scall None
                          (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil)
                                          tint
                                          {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                          ((Evar ___stringlit_3 (tarray tschar 21)) ::
                           (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                             (Ebinop Omul (Etempvar _u tint)
                               (Econst_int (Int.repr 64) tint) tint) tint) ::
                           (Etempvar _t'1 (tptr tschar)) :: nil)))
                      Sskip)
                    (Ssequence
                      (Scall None
                        (Evar _memset (Tfunction
                                        (Tcons (tptr tvoid)
                                          (Tcons tint (Tcons tuint Tnil)))
                                        (tptr tvoid) cc_default))
                        ((Evar _buf (tarray tuchar 64)) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 16) tint) :: nil))
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq (Etempvar _v tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Ssequence
                            (Scall None
                              (Evar _mbedtls_aes_setkey_dec (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _mbedtls_aes_context_struct noattr))
                                                                (Tcons
                                                                  (tptr tuchar)
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                              tint
                                                              cc_default))
                              ((Eaddrof
                                 (Evar _ctx (Tstruct _mbedtls_aes_context_struct noattr))
                                 (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                               (Evar _key (tarray tuchar 32)) ::
                               (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                                 (Ebinop Omul (Etempvar _u tint)
                                   (Econst_int (Int.repr 64) tint) tint)
                                 tint) :: nil))
                            (Ssequence
                              (Ssequence
                                (Sset _j (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _j tint)
                                                   (Econst_int (Int.repr 10000) tint)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Scall None
                                      (Evar _mbedtls_aes_crypt_ecb (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _mbedtls_aes_context_struct noattr))
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    Tnil))))
                                                                    tint
                                                                    cc_default))
                                      ((Eaddrof
                                         (Evar _ctx (Tstruct _mbedtls_aes_context_struct noattr))
                                         (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                                       (Etempvar _v tint) ::
                                       (Evar _buf (tarray tuchar 64)) ::
                                       (Evar _buf (tarray tuchar 64)) :: nil)))
                                  (Sset _j
                                    (Ebinop Oadd (Etempvar _j tint)
                                      (Econst_int (Int.repr 1) tint) tint))))
                              (Ssequence
                                (Scall (Some _t'2)
                                  (Evar _memcmp (Tfunction
                                                  (Tcons (tptr tvoid)
                                                    (Tcons (tptr tvoid)
                                                      (Tcons tuint Tnil)))
                                                  tint cc_default))
                                  ((Evar _buf (tarray tuchar 64)) ::
                                   (Ederef
                                     (Ebinop Oadd
                                       (Evar _aes_test_ecb_dec (tarray (tarray tuchar 16) 3))
                                       (Etempvar _u tint)
                                       (tptr (tarray tuchar 16)))
                                     (tarray tuchar 16)) ::
                                   (Econst_int (Int.repr 16) tint) :: nil))
                                (Sifthenelse (Ebinop One (Etempvar _t'2 tint)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  (Ssequence
                                    (Sifthenelse (Ebinop One
                                                   (Etempvar _verbose tint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      (Scall None
                                        (Evar _printf (Tfunction
                                                        (Tcons (tptr tschar)
                                                          Tnil) tint
                                                        {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                        ((Evar ___stringlit_4 (tarray tschar 8)) ::
                                         nil))
                                      Sskip)
                                    (Ssequence
                                      (Sset _ret
                                        (Econst_int (Int.repr 1) tint))
                                      (Sgoto _exit)))
                                  Sskip))))
                          (Ssequence
                            (Scall None
                              (Evar _mbedtls_aes_setkey_enc (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _mbedtls_aes_context_struct noattr))
                                                                (Tcons
                                                                  (tptr tuchar)
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                              tint
                                                              cc_default))
                              ((Eaddrof
                                 (Evar _ctx (Tstruct _mbedtls_aes_context_struct noattr))
                                 (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                               (Evar _key (tarray tuchar 32)) ::
                               (Ebinop Oadd (Econst_int (Int.repr 128) tint)
                                 (Ebinop Omul (Etempvar _u tint)
                                   (Econst_int (Int.repr 64) tint) tint)
                                 tint) :: nil))
                            (Ssequence
                              (Ssequence
                                (Sset _j (Econst_int (Int.repr 0) tint))
                                (Sloop
                                  (Ssequence
                                    (Sifthenelse (Ebinop Olt
                                                   (Etempvar _j tint)
                                                   (Econst_int (Int.repr 10000) tint)
                                                   tint)
                                      Sskip
                                      Sbreak)
                                    (Scall None
                                      (Evar _mbedtls_aes_crypt_ecb (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _mbedtls_aes_context_struct noattr))
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    Tnil))))
                                                                    tint
                                                                    cc_default))
                                      ((Eaddrof
                                         (Evar _ctx (Tstruct _mbedtls_aes_context_struct noattr))
                                         (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                                       (Etempvar _v tint) ::
                                       (Evar _buf (tarray tuchar 64)) ::
                                       (Evar _buf (tarray tuchar 64)) :: nil)))
                                  (Sset _j
                                    (Ebinop Oadd (Etempvar _j tint)
                                      (Econst_int (Int.repr 1) tint) tint))))
                              (Ssequence
                                (Scall (Some _t'3)
                                  (Evar _memcmp (Tfunction
                                                  (Tcons (tptr tvoid)
                                                    (Tcons (tptr tvoid)
                                                      (Tcons tuint Tnil)))
                                                  tint cc_default))
                                  ((Evar _buf (tarray tuchar 64)) ::
                                   (Ederef
                                     (Ebinop Oadd
                                       (Evar _aes_test_ecb_enc (tarray (tarray tuchar 16) 3))
                                       (Etempvar _u tint)
                                       (tptr (tarray tuchar 16)))
                                     (tarray tuchar 16)) ::
                                   (Econst_int (Int.repr 16) tint) :: nil))
                                (Sifthenelse (Ebinop One (Etempvar _t'3 tint)
                                               (Econst_int (Int.repr 0) tint)
                                               tint)
                                  (Ssequence
                                    (Sifthenelse (Ebinop One
                                                   (Etempvar _verbose tint)
                                                   (Econst_int (Int.repr 0) tint)
                                                   tint)
                                      (Scall None
                                        (Evar _printf (Tfunction
                                                        (Tcons (tptr tschar)
                                                          Tnil) tint
                                                        {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                        ((Evar ___stringlit_4 (tarray tschar 8)) ::
                                         nil))
                                      Sskip)
                                    (Ssequence
                                      (Sset _ret
                                        (Econst_int (Int.repr 1) tint))
                                      (Sgoto _exit)))
                                  Sskip)))))
                        (Sifthenelse (Ebinop One (Etempvar _verbose tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Scall None
                            (Evar _printf (Tfunction
                                            (Tcons (tptr tschar) Tnil) tint
                                            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                            ((Evar ___stringlit_5 (tarray tschar 8)) :: nil))
                          Sskip)))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Sifthenelse (Ebinop One (Etempvar _verbose tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_6 (tarray tschar 2)) :: nil))
            Sskip)
          (Ssequence
            (Sset _ret (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Slabel _exit
                (Scall None
                  (Evar _mbedtls_aes_free (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _mbedtls_aes_context_struct noattr))
                                              Tnil) tvoid cc_default))
                  ((Eaddrof
                     (Evar _ctx (Tstruct _mbedtls_aes_context_struct noattr))
                     (tptr (Tstruct _mbedtls_aes_context_struct noattr))) ::
                   nil)))
              (Sreturn (Some (Etempvar _ret tint))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _mbedtls_aes_context_struct Struct
   ((_nr, tint) :: (_rk, (tptr tuint)) :: (_buf, (tarray tuint 68)) :: nil)
   noattr ::
 Composite _aes_tables_struct Struct
   ((_FSb, (tarray tuchar 256)) :: (_FT0, (tarray tuint 256)) ::
    (_FT1, (tarray tuint 256)) :: (_FT2, (tarray tuint 256)) ::
    (_FT3, (tarray tuint 256)) :: (_RSb, (tarray tuchar 256)) ::
    (_RT0, (tarray tuint 256)) :: (_RT1, (tarray tuint 256)) ::
    (_RT2, (tarray tuint 256)) :: (_RT3, (tarray tuint 256)) ::
    (_RCON, (tarray tuint 10)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_6, Gvar v___stringlit_6) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_memcmp,
   Gfun(External (EF_external "memcmp"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
     cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
     cc_default)) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) AST.Tint
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_mbedtls_zeroize, Gfun(Internal f_mbedtls_zeroize)) ::
 (_tables, Gvar v_tables) :: (_aes_init_done, Gvar v_aes_init_done) ::
 (_aes_gen_tables, Gfun(Internal f_aes_gen_tables)) ::
 (_mbedtls_aes_init, Gfun(Internal f_mbedtls_aes_init)) ::
 (_mbedtls_aes_free, Gfun(Internal f_mbedtls_aes_free)) ::
 (_mbedtls_aes_setkey_enc, Gfun(Internal f_mbedtls_aes_setkey_enc)) ::
 (_mbedtls_aes_setkey_dec, Gfun(Internal f_mbedtls_aes_setkey_dec)) ::
 (_mbedtls_aes_encrypt, Gfun(Internal f_mbedtls_aes_encrypt)) ::
 (_mbedtls_aes_decrypt, Gfun(Internal f_mbedtls_aes_decrypt)) ::
 (_mbedtls_aes_crypt_ecb, Gfun(Internal f_mbedtls_aes_crypt_ecb)) ::
 (_aes_test_ecb_dec, Gvar v_aes_test_ecb_dec) ::
 (_aes_test_ecb_enc, Gvar v_aes_test_ecb_enc) ::
 (_mbedtls_aes_self_test, Gfun(Internal f_mbedtls_aes_self_test)) :: nil).

Definition public_idents : list ident :=
(_mbedtls_aes_self_test :: _mbedtls_aes_crypt_ecb :: _mbedtls_aes_decrypt ::
 _mbedtls_aes_encrypt :: _mbedtls_aes_setkey_dec ::
 _mbedtls_aes_setkey_enc :: _mbedtls_aes_free :: _mbedtls_aes_init ::
 _printf :: _memset :: _memcmp :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


