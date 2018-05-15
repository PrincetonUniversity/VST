From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition _FSb : ident := 5%positive.
Definition _FT0 : ident := 6%positive.
Definition _FT1 : ident := 7%positive.
Definition _FT2 : ident := 8%positive.
Definition _FT3 : ident := 9%positive.
Definition _RCON : ident := 15%positive.
Definition _RK : ident := 108%positive.
Definition _RSb : ident := 10%positive.
Definition _RT0 : ident := 11%positive.
Definition _RT1 : ident := 12%positive.
Definition _RT2 : ident := 13%positive.
Definition _RT3 : ident := 14%positive.
Definition _SK : ident := 125%positive.
Definition _X0 : ident := 131%positive.
Definition _X1 : ident := 132%positive.
Definition _X2 : ident := 133%positive.
Definition _X3 : ident := 134%positive.
Definition _Y0 : ident := 135%positive.
Definition _Y1 : ident := 136%positive.
Definition _Y2 : ident := 137%positive.
Definition _Y3 : ident := 138%positive.
Definition ___builtin_annot : ident := 23%positive.
Definition ___builtin_annot_intval : ident := 24%positive.
Definition ___builtin_bswap : ident := 17%positive.
Definition ___builtin_bswap16 : ident := 19%positive.
Definition ___builtin_bswap32 : ident := 18%positive.
Definition ___builtin_bswap64 : ident := 49%positive.
Definition ___builtin_clz : ident := 50%positive.
Definition ___builtin_clzl : ident := 51%positive.
Definition ___builtin_clzll : ident := 52%positive.
Definition ___builtin_ctz : ident := 53%positive.
Definition ___builtin_ctzl : ident := 54%positive.
Definition ___builtin_ctzll : ident := 55%positive.
Definition ___builtin_debug : ident := 67%positive.
Definition ___builtin_fabs : ident := 20%positive.
Definition ___builtin_fmadd : ident := 58%positive.
Definition ___builtin_fmax : ident := 56%positive.
Definition ___builtin_fmin : ident := 57%positive.
Definition ___builtin_fmsub : ident := 59%positive.
Definition ___builtin_fnmadd : ident := 60%positive.
Definition ___builtin_fnmsub : ident := 61%positive.
Definition ___builtin_fsqrt : ident := 21%positive.
Definition ___builtin_membar : ident := 25%positive.
Definition ___builtin_memcpy_aligned : ident := 22%positive.
Definition ___builtin_nop : ident := 66%positive.
Definition ___builtin_read16_reversed : ident := 62%positive.
Definition ___builtin_read32_reversed : ident := 63%positive.
Definition ___builtin_va_arg : ident := 27%positive.
Definition ___builtin_va_copy : ident := 28%positive.
Definition ___builtin_va_end : ident := 29%positive.
Definition ___builtin_va_start : ident := 26%positive.
Definition ___builtin_write16_reversed : ident := 64%positive.
Definition ___builtin_write32_reversed : ident := 65%positive.
Definition ___compcert_i64_dtos : ident := 34%positive.
Definition ___compcert_i64_dtou : ident := 35%positive.
Definition ___compcert_i64_sar : ident := 46%positive.
Definition ___compcert_i64_sdiv : ident := 40%positive.
Definition ___compcert_i64_shl : ident := 44%positive.
Definition ___compcert_i64_shr : ident := 45%positive.
Definition ___compcert_i64_smod : ident := 42%positive.
Definition ___compcert_i64_smulh : ident := 47%positive.
Definition ___compcert_i64_stod : ident := 36%positive.
Definition ___compcert_i64_stof : ident := 38%positive.
Definition ___compcert_i64_udiv : ident := 41%positive.
Definition ___compcert_i64_umod : ident := 43%positive.
Definition ___compcert_i64_umulh : ident := 48%positive.
Definition ___compcert_i64_utod : ident := 37%positive.
Definition ___compcert_i64_utof : ident := 39%positive.
Definition ___compcert_va_composite : ident := 33%positive.
Definition ___compcert_va_float64 : ident := 32%positive.
Definition ___compcert_va_int32 : ident := 30%positive.
Definition ___compcert_va_int64 : ident := 31%positive.
Definition ___stringlit_1 : ident := 175%positive.
Definition ___stringlit_2 : ident := 176%positive.
Definition ___stringlit_3 : ident := 177%positive.
Definition ___stringlit_4 : ident := 178%positive.
Definition ___stringlit_5 : ident := 179%positive.
Definition ___stringlit_6 : ident := 180%positive.
Definition _aes_gen_tables : ident := 101%positive.
Definition _aes_init_done : ident := 76%positive.
Definition _aes_tables_struct : ident := 16%positive.
Definition _aes_test_ecb_dec : ident := 170%positive.
Definition _aes_test_ecb_enc : ident := 171%positive.
Definition _b0 : ident := 110%positive.
Definition _b0__1 : ident := 117%positive.
Definition _b0__2 : ident := 139%positive.
Definition _b0__3 : ident := 143%positive.
Definition _b0__4 : ident := 147%positive.
Definition _b0__5 : ident := 152%positive.
Definition _b0__6 : ident := 157%positive.
Definition _b0__7 : ident := 162%positive.
Definition _b1 : ident := 111%positive.
Definition _b1__1 : ident := 118%positive.
Definition _b1__2 : ident := 140%positive.
Definition _b1__3 : ident := 144%positive.
Definition _b1__4 : ident := 148%positive.
Definition _b1__5 : ident := 153%positive.
Definition _b1__6 : ident := 158%positive.
Definition _b1__7 : ident := 163%positive.
Definition _b2 : ident := 112%positive.
Definition _b2__1 : ident := 119%positive.
Definition _b2__2 : ident := 141%positive.
Definition _b2__3 : ident := 145%positive.
Definition _b2__4 : ident := 149%positive.
Definition _b2__5 : ident := 154%positive.
Definition _b2__6 : ident := 159%positive.
Definition _b2__7 : ident := 164%positive.
Definition _b3 : ident := 113%positive.
Definition _b3__1 : ident := 120%positive.
Definition _b3__2 : ident := 142%positive.
Definition _b3__3 : ident := 146%positive.
Definition _b3__4 : ident := 150%positive.
Definition _b3__5 : ident := 155%positive.
Definition _b3__6 : ident := 160%positive.
Definition _b3__7 : ident := 165%positive.
Definition _buf : ident := 3%positive.
Definition _ctx : ident := 102%positive.
Definition _cty : ident := 124%positive.
Definition _exit : ident := 127%positive.
Definition _i : ident := 77%positive.
Definition _input : ident := 129%positive.
Definition _iv : ident := 174%positive.
Definition _j : ident := 122%positive.
Definition _key : ident := 105%positive.
Definition _key_word : ident := 107%positive.
Definition _keybits : ident := 106%positive.
Definition _log : ident := 82%positive.
Definition _logi : ident := 84%positive.
Definition _logx : ident := 89%positive.
Definition _logx__1 : ident := 92%positive.
Definition _logx__2 : ident := 95%positive.
Definition _logx__3 : ident := 98%positive.
Definition _logy : ident := 90%positive.
Definition _logy__1 : ident := 93%positive.
Definition _logy__2 : ident := 96%positive.
Definition _logy__3 : ident := 99%positive.
Definition _m : ident := 91%positive.
Definition _m__1 : ident := 94%positive.
Definition _m__2 : ident := 97%positive.
Definition _m__3 : ident := 100%positive.
Definition _main : ident := 182%positive.
Definition _mbedtls_aes_context_struct : ident := 4%positive.
Definition _mbedtls_aes_crypt_ecb : ident := 169%positive.
Definition _mbedtls_aes_decrypt : ident := 167%positive.
Definition _mbedtls_aes_encrypt : ident := 166%positive.
Definition _mbedtls_aes_free : ident := 104%positive.
Definition _mbedtls_aes_init : ident := 103%positive.
Definition _mbedtls_aes_self_test : ident := 181%positive.
Definition _mbedtls_aes_setkey_dec : ident := 128%positive.
Definition _mbedtls_aes_setkey_enc : ident := 121%positive.
Definition _mbedtls_zeroize : ident := 74%positive.
Definition _memcmp : ident := 68%positive.
Definition _memset : ident := 69%positive.
Definition _mode : ident := 168%positive.
Definition _n : ident := 72%positive.
Definition _nr : ident := 1%positive.
Definition _output : ident := 130%positive.
Definition _p : ident := 73%positive.
Definition _pow : ident := 81%positive.
Definition _printf : ident := 70%positive.
Definition _prod1 : ident := 85%positive.
Definition _prod2 : ident := 86%positive.
Definition _prod3 : ident := 87%positive.
Definition _prod4 : ident := 88%positive.
Definition _rcon : ident := 116%positive.
Definition _ret : ident := 123%positive.
Definition _rk : ident := 2%positive.
Definition _rk0 : ident := 114%positive.
Definition _rk7 : ident := 115%positive.
Definition _rk__1 : ident := 151%positive.
Definition _rk__2 : ident := 156%positive.
Definition _rk__3 : ident := 161%positive.
Definition _rot : ident := 83%positive.
Definition _sk : ident := 126%positive.
Definition _tables : ident := 75%positive.
Definition _tmp : ident := 109%positive.
Definition _u : ident := 173%positive.
Definition _v : ident := 71%positive.
Definition _verbose : ident := 172%positive.
Definition _x : ident := 78%positive.
Definition _y : ident := 79%positive.
Definition _z : ident := 80%positive.
Definition _t'1 : ident := 183%positive.
Definition _t'10 : ident := 192%positive.
Definition _t'11 : ident := 193%positive.
Definition _t'12 : ident := 194%positive.
Definition _t'13 : ident := 195%positive.
Definition _t'14 : ident := 196%positive.
Definition _t'15 : ident := 197%positive.
Definition _t'16 : ident := 198%positive.
Definition _t'17 : ident := 199%positive.
Definition _t'18 : ident := 200%positive.
Definition _t'19 : ident := 201%positive.
Definition _t'2 : ident := 184%positive.
Definition _t'20 : ident := 202%positive.
Definition _t'3 : ident := 185%positive.
Definition _t'4 : ident := 186%positive.
Definition _t'5 : ident := 187%positive.
Definition _t'6 : ident := 188%positive.
Definition _t'7 : ident := 189%positive.
Definition _t'8 : ident := 190%positive.
Definition _t'9 : ident := 191%positive.

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
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_memcmp,
   Gfun(External (EF_external "memcmp"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
     cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
     cc_default)) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)
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
 _printf :: _memset :: _memcmp :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fsqrt :: ___builtin_fabs ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


