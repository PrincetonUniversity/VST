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
  Definition source_file := "sha/hkdf.c".
  Definition normalized := false.
End Info.

Definition _HKDF : ident := $"HKDF".
Definition _HKDF_expand : ident := $"HKDF_expand".
Definition _HKDF_extract : ident := $"HKDF_extract".
Definition _HMAC : ident := $"HMAC".
Definition _HMAC2 : ident := $"HMAC2".
Definition _HMAC_Final : ident := $"HMAC_Final".
Definition _HMAC_Init : ident := $"HMAC_Init".
Definition _HMAC_Update : ident := $"HMAC_Update".
Definition _HMAC_cleanup : ident := $"HMAC_cleanup".
Definition _K : ident := $"K".
Definition _K256 : ident := $"K256".
Definition _Ki : ident := $"Ki".
Definition _Nh : ident := $"Nh".
Definition _Nl : ident := $"Nl".
Definition _SHA256 : ident := $"SHA256".
Definition _SHA256_Final : ident := $"SHA256_Final".
Definition _SHA256_Init : ident := $"SHA256_Init".
Definition _SHA256_Update : ident := $"SHA256_Update".
Definition _SHA256_addlength : ident := $"SHA256_addlength".
Definition _SHA256state_st : ident := $"SHA256state_st".
Definition _T1 : ident := $"T1".
Definition _T2 : ident := $"T2".
Definition _V : ident := $"V".
Definition _X : ident := $"X".
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
Definition _a : ident := $"a".
Definition _add_len : ident := $"add_len".
Definition _additional : ident := $"additional".
Definition _aux : ident := $"aux".
Definition _b : ident := $"b".
Definition _buf : ident := $"buf".
Definition _c : ident := $"c".
Definition _cNh : ident := $"cNh".
Definition _cNl : ident := $"cNl".
Definition _ctr : ident := $"ctr".
Definition _ctx : ident := $"ctx".
Definition _ctx_key : ident := $"ctx_key".
Definition _custom : ident := $"custom".
Definition _d : ident := $"d".
Definition _data : ident := $"data".
Definition _data_ : ident := $"data_".
Definition _data_len : ident := $"data_len".
Definition _digest_len : ident := $"digest_len".
Definition _done : ident := $"done".
Definition _dummy : ident := $"dummy".
Definition _e : ident := $"e".
Definition _entropy_len : ident := $"entropy_len".
Definition _extr1 : ident := $"extr1".
Definition _extr2 : ident := $"extr2".
Definition _f : ident := $"f".
Definition _fragment : ident := $"fragment".
Definition _free : ident := $"free".
Definition _g : ident := $"g".
Definition _get_entropy : ident := $"get_entropy".
Definition _h : ident := $"h".
Definition _hmac : ident := $"hmac".
Definition _hmac_ctx : ident := $"hmac_ctx".
Definition _hmac_ctx_st : ident := $"hmac_ctx_st".
Definition _i : ident := $"i".
Definition _i_ctx : ident := $"i_ctx".
Definition _ilen : ident := $"ilen".
Definition _in : ident := $"in".
Definition _info : ident := $"info".
Definition _info_len : ident := $"info_len".
Definition _input : ident := $"input".
Definition _interval : ident := $"interval".
Definition _j : ident := $"j".
Definition _key : ident := $"key".
Definition _key_len : ident := $"key_len".
Definition _keylen : ident := $"keylen".
Definition _l : ident := $"l".
Definition _left : ident := $"left".
Definition _len : ident := $"len".
Definition _ll : ident := $"ll".
Definition _m : ident := $"m".
Definition _m__1 : ident := $"m__1".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _mbedtls_hmac_drbg_context : ident := $"mbedtls_hmac_drbg_context".
Definition _mbedtls_hmac_drbg_free : ident := $"mbedtls_hmac_drbg_free".
Definition _mbedtls_hmac_drbg_init : ident := $"mbedtls_hmac_drbg_init".
Definition _mbedtls_hmac_drbg_random : ident := $"mbedtls_hmac_drbg_random".
Definition _mbedtls_hmac_drbg_random_with_add : ident := $"mbedtls_hmac_drbg_random_with_add".
Definition _mbedtls_hmac_drbg_reseed : ident := $"mbedtls_hmac_drbg_reseed".
Definition _mbedtls_hmac_drbg_seed : ident := $"mbedtls_hmac_drbg_seed".
Definition _mbedtls_hmac_drbg_seed_buf : ident := $"mbedtls_hmac_drbg_seed_buf".
Definition _mbedtls_hmac_drbg_set_entropy_len : ident := $"mbedtls_hmac_drbg_set_entropy_len".
Definition _mbedtls_hmac_drbg_set_prediction_resistance : ident := $"mbedtls_hmac_drbg_set_prediction_resistance".
Definition _mbedtls_hmac_drbg_set_reseed_interval : ident := $"mbedtls_hmac_drbg_set_reseed_interval".
Definition _mbedtls_hmac_drbg_update : ident := $"mbedtls_hmac_drbg_update".
Definition _mbedtls_md_context_t : ident := $"mbedtls_md_context_t".
Definition _mbedtls_md_free : ident := $"mbedtls_md_free".
Definition _mbedtls_md_get_size : ident := $"mbedtls_md_get_size".
Definition _mbedtls_md_hmac_finish : ident := $"mbedtls_md_hmac_finish".
Definition _mbedtls_md_hmac_reset : ident := $"mbedtls_md_hmac_reset".
Definition _mbedtls_md_hmac_starts : ident := $"mbedtls_md_hmac_starts".
Definition _mbedtls_md_hmac_update : ident := $"mbedtls_md_hmac_update".
Definition _mbedtls_md_info_from_string : ident := $"mbedtls_md_info_from_string".
Definition _mbedtls_md_info_from_type : ident := $"mbedtls_md_info_from_type".
Definition _mbedtls_md_info_t : ident := $"mbedtls_md_info_t".
Definition _mbedtls_md_setup : ident := $"mbedtls_md_setup".
Definition _mbedtls_zeroize : ident := $"mbedtls_zeroize".
Definition _md : ident := $"md".
Definition _md_ctx : ident := $"md_ctx".
Definition _md_info : ident := $"md_info".
Definition _md_len : ident := $"md_len".
Definition _md_name : ident := $"md_name".
Definition _md_size : ident := $"md_size".
Definition _md_type : ident := $"md_type".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _mocked_sha256_info : ident := $"mocked_sha256_info".
Definition _n : ident := $"n".
Definition _num : ident := $"num".
Definition _o_ctx : ident := $"o_ctx".
Definition _out : ident := $"out".
Definition _out_key : ident := $"out_key".
Definition _out_len : ident := $"out_len".
Definition _output : ident := $"output".
Definition _p : ident := $"p".
Definition _p_rng : ident := $"p_rng".
Definition _pad : ident := $"pad".
Definition _prediction_resistance : ident := $"prediction_resistance".
Definition _previous : ident := $"previous".
Definition _prk : ident := $"prk".
Definition _prk_len : ident := $"prk_len".
Definition _prk_len_temp : ident := $"prk_len_temp".
Definition _reseed_counter : ident := $"reseed_counter".
Definition _reseed_interval : ident := $"reseed_interval".
Definition _reset : ident := $"reset".
Definition _resistance : ident := $"resistance".
Definition _ret : ident := $"ret".
Definition _rounds : ident := $"rounds".
Definition _s0 : ident := $"s0".
Definition _s1 : ident := $"s1".
Definition _salt : ident := $"salt".
Definition _salt_len : ident := $"salt_len".
Definition _secret : ident := $"secret".
Definition _secret_len : ident := $"secret_len".
Definition _seed : ident := $"seed".
Definition _seedlen : ident := $"seedlen".
Definition _sep : ident := $"sep".
Definition _sep_value : ident := $"sep_value".
Definition _sha256_block_data_order : ident := $"sha256_block_data_order".
Definition _sha_ctx : ident := $"sha_ctx".
Definition _t : ident := $"t".
Definition _test_md_get_size : ident := $"test_md_get_size".
Definition _todo : ident := $"todo".
Definition _use_len : ident := $"use_len".
Definition _v : ident := $"v".
Definition _xn : ident := $"xn".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.

Definition f_HKDF_extract := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out_key, (tptr tuchar)) :: (_out_len, (tptr tuint)) ::
                (_secret, (tptr tuchar)) :: (_secret_len, tuint) ::
                (_salt, (tptr tuchar)) :: (_salt_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_len, tuint) :: (_t'1, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _HMAC (Tfunction
                    (Tcons (tptr tuchar)
                      (Tcons tint
                        (Tcons (tptr tuchar)
                          (Tcons tint (Tcons (tptr tuchar) Tnil)))))
                    (tptr tuchar) cc_default))
      ((Etempvar _salt (tptr tuchar)) :: (Etempvar _salt_len tuint) ::
       (Etempvar _secret (tptr tuchar)) :: (Etempvar _secret_len tuint) ::
       (Etempvar _out_key (tptr tuchar)) :: nil))
    (Sifthenelse (Ebinop Oeq (Etempvar _t'1 (tptr tuchar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Sassign (Ederef (Etempvar _out_len (tptr tuint)) tuint)
      (Econst_int (Int.repr 32) tint))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition f_HKDF_expand := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out_key, (tptr tuchar)) :: (_out_len, tuint) ::
                (_prk, (tptr tuchar)) :: (_prk_len, tuint) ::
                (_info, (tptr tuchar)) :: (_info_len, tuint) :: nil);
  fn_vars := ((_previous, (tarray tuchar 64)) ::
              (_hmac, (Tstruct _hmac_ctx_st noattr)) :: (_ctr, tuchar) ::
              nil);
  fn_temps := ((_digest_len, tuint) :: (_n, tuint) :: (_done, tuint) ::
               (_i, tuint) :: (_ret, tint) :: (_todo, tuint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _digest_len (Econst_int (Int.repr 32) tint))
  (Ssequence
    (Sset _done (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _ret (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sset _n
          (Ebinop Odiv
            (Ebinop Osub
              (Ebinop Oadd (Etempvar _out_len tuint)
                (Etempvar _digest_len tuint) tuint)
              (Econst_int (Int.repr 1) tint) tuint)
            (Etempvar _digest_len tuint) tuint))
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Olt
                           (Ebinop Oadd (Etempvar _out_len tuint)
                             (Etempvar _digest_len tuint) tuint)
                           (Etempvar _out_len tuint) tint)
              (Sset _t'1 (Econst_int (Int.repr 1) tint))
              (Sset _t'1
                (Ecast
                  (Ebinop Ogt (Etempvar _n tuint)
                    (Econst_int (Int.repr 255) tint) tint) tbool)))
            (Sifthenelse (Etempvar _t'1 tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip))
          (Ssequence
            (Scall None
              (Evar _HMAC_Init (Tfunction
                                 (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                                   (Tcons (tptr tuchar) (Tcons tint Tnil)))
                                 tvoid cc_default))
              ((Eaddrof (Evar _hmac (Tstruct _hmac_ctx_st noattr))
                 (tptr (Tstruct _hmac_ctx_st noattr))) ::
               (Etempvar _prk (tptr tuchar)) :: (Etempvar _prk_len tuint) ::
               nil))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                   (Etempvar _n tuint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sassign (Evar _ctr tuchar)
                        (Ebinop Oadd (Etempvar _i tuint)
                          (Econst_int (Int.repr 1) tint) tuint))
                      (Ssequence
                        (Sifthenelse (Ebinop One (Etempvar _i tuint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Ssequence
                            (Scall None
                              (Evar _HMAC_Init (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _hmac_ctx_st noattr))
                                                   (Tcons (tptr tuchar)
                                                     (Tcons tint Tnil)))
                                                 tvoid cc_default))
                              ((Eaddrof
                                 (Evar _hmac (Tstruct _hmac_ctx_st noattr))
                                 (tptr (Tstruct _hmac_ctx_st noattr))) ::
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) ::
                               (Econst_int (Int.repr 0) tint) :: nil))
                            (Scall None
                              (Evar _HMAC_Update (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _hmac_ctx_st noattr))
                                                     (Tcons (tptr tvoid)
                                                       (Tcons tuint Tnil)))
                                                   tvoid cc_default))
                              ((Eaddrof
                                 (Evar _hmac (Tstruct _hmac_ctx_st noattr))
                                 (tptr (Tstruct _hmac_ctx_st noattr))) ::
                               (Evar _previous (tarray tuchar 64)) ::
                               (Etempvar _digest_len tuint) :: nil)))
                          Sskip)
                        (Ssequence
                          (Scall None
                            (Evar _HMAC_Update (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _hmac_ctx_st noattr))
                                                   (Tcons (tptr tvoid)
                                                     (Tcons tuint Tnil)))
                                                 tvoid cc_default))
                            ((Eaddrof
                               (Evar _hmac (Tstruct _hmac_ctx_st noattr))
                               (tptr (Tstruct _hmac_ctx_st noattr))) ::
                             (Etempvar _info (tptr tuchar)) ::
                             (Etempvar _info_len tuint) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _HMAC_Update (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _hmac_ctx_st noattr))
                                                     (Tcons (tptr tvoid)
                                                       (Tcons tuint Tnil)))
                                                   tvoid cc_default))
                              ((Eaddrof
                                 (Evar _hmac (Tstruct _hmac_ctx_st noattr))
                                 (tptr (Tstruct _hmac_ctx_st noattr))) ::
                               (Eaddrof (Evar _ctr tuchar) (tptr tuchar)) ::
                               (Econst_int (Int.repr 1) tint) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _HMAC_Final (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _hmac_ctx_st noattr))
                                                      (Tcons (tptr tuchar)
                                                        Tnil)) tvoid
                                                    cc_default))
                                ((Eaddrof
                                   (Evar _hmac (Tstruct _hmac_ctx_st noattr))
                                   (tptr (Tstruct _hmac_ctx_st noattr))) ::
                                 (Evar _previous (tarray tuchar 64)) :: nil))
                              (Ssequence
                                (Sset _todo (Etempvar _digest_len tuint))
                                (Ssequence
                                  (Sifthenelse (Ebinop Ogt
                                                 (Ebinop Oadd
                                                   (Etempvar _done tuint)
                                                   (Etempvar _todo tuint)
                                                   tuint)
                                                 (Etempvar _out_len tuint)
                                                 tint)
                                    (Sset _todo
                                      (Ebinop Osub (Etempvar _out_len tuint)
                                        (Etempvar _done tuint) tuint))
                                    Sskip)
                                  (Ssequence
                                    (Scall None
                                      (Evar _memcpy (Tfunction
                                                      (Tcons (tptr tvoid)
                                                        (Tcons (tptr tvoid)
                                                          (Tcons tuint Tnil)))
                                                      (tptr tvoid)
                                                      cc_default))
                                      ((Ebinop Oadd
                                         (Etempvar _out_key (tptr tuchar))
                                         (Etempvar _done tuint)
                                         (tptr tuchar)) ::
                                       (Evar _previous (tarray tuchar 64)) ::
                                       (Etempvar _todo tuint) :: nil))
                                    (Sset _done
                                      (Ebinop Oadd (Etempvar _done tuint)
                                        (Etempvar _todo tuint) tuint)))))))))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tuint)
                      (Econst_int (Int.repr 1) tint) tuint))))
              (Ssequence
                (Sset _ret (Econst_int (Int.repr 1) tint))
                (Ssequence
                  (Scall None
                    (Evar _HMAC_cleanup (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _hmac_ctx_st noattr))
                                            Tnil) tvoid cc_default))
                    ((Eaddrof (Evar _hmac (Tstruct _hmac_ctx_st noattr))
                       (tptr (Tstruct _hmac_ctx_st noattr))) :: nil))
                  (Ssequence Sskip (Sreturn (Some (Etempvar _ret tint)))))))))))))
|}.

Definition f_HKDF := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out_key, (tptr tuchar)) :: (_out_len, tuint) ::
                (_secret, (tptr tuchar)) :: (_secret_len, tuint) ::
                (_salt, (tptr tuchar)) :: (_salt_len, tuint) ::
                (_info, (tptr tuchar)) :: (_info_len, tuint) :: nil);
  fn_vars := ((_prk, (tarray tuchar 64)) :: (_prk_len, tuint) :: nil);
  fn_temps := ((_extr1, tint) :: (_prk_len_temp, tuint) :: (_extr2, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _HKDF_extract (Tfunction
                            (Tcons (tptr tuchar)
                              (Tcons (tptr tuint)
                                (Tcons (tptr tuchar)
                                  (Tcons tuint
                                    (Tcons (tptr tuchar) (Tcons tuint Tnil))))))
                            tint cc_default))
      ((Evar _prk (tarray tuchar 64)) ::
       (Eaddrof (Evar _prk_len tuint) (tptr tuint)) ::
       (Etempvar _secret (tptr tuchar)) :: (Etempvar _secret_len tuint) ::
       (Etempvar _salt (tptr tuchar)) :: (Etempvar _salt_len tuint) :: nil))
    (Sset _extr1 (Etempvar _t'1 tint)))
  (Ssequence
    (Sset _prk_len_temp (Evar _prk_len tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _HKDF_expand (Tfunction
                               (Tcons (tptr tuchar)
                                 (Tcons tuint
                                   (Tcons (tptr tuchar)
                                     (Tcons tuint
                                       (Tcons (tptr tuchar)
                                         (Tcons tuint Tnil)))))) tint
                               cc_default))
          ((Etempvar _out_key (tptr tuchar)) :: (Etempvar _out_len tuint) ::
           (Evar _prk (tarray tuchar 64)) ::
           (Etempvar _prk_len_temp tuint) ::
           (Etempvar _info (tptr tuchar)) :: (Etempvar _info_len tuint) ::
           nil))
        (Sset _extr2 (Etempvar _t'2 tint)))
      (Ssequence
        (Ssequence
          (Sifthenelse (Eunop Onotbool (Etempvar _extr1 tint) tint)
            (Sset _t'3 (Econst_int (Int.repr 1) tint))
            (Sset _t'3
              (Ecast (Eunop Onotbool (Etempvar _extr2 tint) tint) tbool)))
          (Sifthenelse (Etempvar _t'3 tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip))
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))
|}.

Definition composites : list composite_definition :=
(Composite _SHA256state_st Struct
   ((_h, (tarray tuint 8)) :: (_Nl, tuint) :: (_Nh, tuint) ::
    (_data, (tarray tuchar 64)) :: (_num, tuint) :: nil)
   noattr ::
 Composite _hmac_ctx_st Struct
   ((_md_ctx, (Tstruct _SHA256state_st noattr)) ::
    (_i_ctx, (Tstruct _SHA256state_st noattr)) ::
    (_o_ctx, (Tstruct _SHA256state_st noattr)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap64,
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
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
     (tptr tvoid) cc_default)) ::
 (_HMAC_Init,
   Gfun(External (EF_external "HMAC_Init"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
       (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid cc_default)) ::
 (_HMAC_Update,
   Gfun(External (EF_external "HMAC_Update"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid cc_default)) ::
 (_HMAC_Final,
   Gfun(External (EF_external "HMAC_Final"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _hmac_ctx_st noattr)) (Tcons (tptr tuchar) Tnil))
     tvoid cc_default)) ::
 (_HMAC_cleanup,
   Gfun(External (EF_external "HMAC_cleanup"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _hmac_ctx_st noattr)) Tnil) tvoid cc_default)) ::
 (_HMAC,
   Gfun(External (EF_external "HMAC"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuchar)
       (Tcons tint
         (Tcons (tptr tuchar) (Tcons tint (Tcons (tptr tuchar) Tnil)))))
     (tptr tuchar) cc_default)) ::
 (_HKDF_extract, Gfun(Internal f_HKDF_extract)) ::
 (_HKDF_expand, Gfun(Internal f_HKDF_expand)) ::
 (_HKDF, Gfun(Internal f_HKDF)) :: nil).

Definition public_idents : list ident :=
(_HKDF :: _HKDF_expand :: _HKDF_extract :: _HMAC :: _HMAC_cleanup ::
 _HMAC_Final :: _HMAC_Update :: _HMAC_Init :: _memcpy :: ___builtin_debug ::
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


