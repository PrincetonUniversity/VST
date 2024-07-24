From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.13".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "hmac_drbg.c".
  Definition normalized := true.
End Info.

Definition _HMAC : ident := $"HMAC".
Definition _HMAC2 : ident := $"HMAC2".
Definition _HMAC_Final : ident := $"HMAC_Final".
Definition _HMAC_Init : ident := $"HMAC_Init".
Definition _HMAC_Update : ident := $"HMAC_Update".
Definition _HMAC_cleanup : ident := $"HMAC_cleanup".
Definition _K : ident := $"K".
Definition _Nh : ident := $"Nh".
Definition _Nl : ident := $"Nl".
Definition _SHA256_Final : ident := $"SHA256_Final".
Definition _SHA256_Init : ident := $"SHA256_Init".
Definition _SHA256_Update : ident := $"SHA256_Update".
Definition _SHA256state_st : ident := $"SHA256state_st".
Definition _V : ident := $"V".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_cls : ident := $"__builtin_cls".
Definition ___builtin_clsl : ident := $"__builtin_clsl".
Definition ___builtin_clsll : ident := $"__builtin_clsll".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fence : ident := $"__builtin_fence".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
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
Definition _add_len : ident := $"add_len".
Definition _additional : ident := $"additional".
Definition _aux : ident := $"aux".
Definition _buf : ident := $"buf".
Definition _c : ident := $"c".
Definition _ctx : ident := $"ctx".
Definition _ctx_key : ident := $"ctx_key".
Definition _custom : ident := $"custom".
Definition _d : ident := $"d".
Definition _data : ident := $"data".
Definition _data_len : ident := $"data_len".
Definition _dummy : ident := $"dummy".
Definition _entropy_len : ident := $"entropy_len".
Definition _free : ident := $"free".
Definition _get_entropy : ident := $"get_entropy".
Definition _h : ident := $"h".
Definition _hmac : ident := $"hmac".
Definition _hmac_ctx : ident := $"hmac_ctx".
Definition _hmac_ctx_st : ident := $"hmac_ctx_st".
Definition _i : ident := $"i".
Definition _i_ctx : ident := $"i_ctx".
Definition _ilen : ident := $"ilen".
Definition _info : ident := $"info".
Definition _input : ident := $"input".
Definition _interval : ident := $"interval".
Definition _j : ident := $"j".
Definition _key : ident := $"key".
Definition _key_len : ident := $"key_len".
Definition _keylen : ident := $"keylen".
Definition _left : ident := $"left".
Definition _len : ident := $"len".
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
Definition _out_len : ident := $"out_len".
Definition _output : ident := $"output".
Definition _p : ident := $"p".
Definition _p_rng : ident := $"p_rng".
Definition _pad : ident := $"pad".
Definition _prediction_resistance : ident := $"prediction_resistance".
Definition _reseed_counter : ident := $"reseed_counter".
Definition _reseed_interval : ident := $"reseed_interval".
Definition _reset : ident := $"reset".
Definition _resistance : ident := $"resistance".
Definition _ret : ident := $"ret".
Definition _rounds : ident := $"rounds".
Definition _seed : ident := $"seed".
Definition _seedlen : ident := $"seedlen".
Definition _sep : ident := $"sep".
Definition _sep_value : ident := $"sep_value".
Definition _sha_ctx : ident := $"sha_ctx".
Definition _test_md_get_size : ident := $"test_md_get_size".
Definition _use_len : ident := $"use_len".
Definition _v : ident := $"v".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.

Definition f_HMAC_Init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) ::
                (_key, (tptr tuchar)) :: (_len, tint) :: nil);
  fn_vars := ((_pad, (tarray tuchar 64)) :: (_ctx_key, (tarray tuchar 64)) ::
              nil);
  fn_temps := ((_i, tint) :: (_j, tint) :: (_reset, tint) ::
               (_aux, tuchar) :: (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _reset (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _key (tptr tuchar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sset _reset (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sset _j (Econst_int (Int.repr 64) tint))
          (Sifthenelse (Ebinop Olt (Etempvar _j tint) (Etempvar _len tint)
                         tint)
            (Ssequence
              (Scall None
                (Evar _SHA256_Init (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _SHA256state_st noattr))
                                       Tnil) tvoid cc_default))
                ((Eaddrof
                   (Efield
                     (Ederef
                       (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                       (Tstruct _hmac_ctx_st noattr)) _md_ctx
                     (Tstruct _SHA256state_st noattr))
                   (tptr (Tstruct _SHA256state_st noattr))) :: nil))
              (Ssequence
                (Scall None
                  (Evar _SHA256_Update (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _SHA256state_st noattr))
                                           (Tcons (tptr tvoid)
                                             (Tcons tulong Tnil))) tvoid
                                         cc_default))
                  ((Eaddrof
                     (Efield
                       (Ederef
                         (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                         (Tstruct _hmac_ctx_st noattr)) _md_ctx
                       (Tstruct _SHA256state_st noattr))
                     (tptr (Tstruct _SHA256state_st noattr))) ::
                   (Etempvar _key (tptr tuchar)) :: (Etempvar _len tint) ::
                   nil))
                (Ssequence
                  (Scall None
                    (Evar _SHA256_Final (Tfunction
                                          (Tcons (tptr tuchar)
                                            (Tcons
                                              (tptr (Tstruct _SHA256state_st noattr))
                                              Tnil)) tvoid cc_default))
                    ((Evar _ctx_key (tarray tuchar 64)) ::
                     (Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                           (Tstruct _hmac_ctx_st noattr)) _md_ctx
                         (Tstruct _SHA256state_st noattr))
                       (tptr (Tstruct _SHA256state_st noattr))) :: nil))
                  (Scall None
                    (Evar _memset (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons tint (Tcons tulong Tnil)))
                                    (tptr tvoid) cc_default))
                    ((Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                       (Econst_int (Int.repr 32) tint) (tptr tuchar)) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 32) tint) :: nil)))))
            (Ssequence
              (Scall None
                (Evar _memcpy (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                                (tptr tvoid) cc_default))
                ((Evar _ctx_key (tarray tuchar 64)) ::
                 (Etempvar _key (tptr tuchar)) :: (Etempvar _len tint) ::
                 nil))
              (Scall None
                (Evar _memset (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons tint (Tcons tulong Tnil)))
                                (tptr tvoid) cc_default))
                ((Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                   (Etempvar _len tint) (tptr tuchar)) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Osub (Esizeof (tarray tuchar 64) tulong)
                   (Etempvar _len tint) tulong) :: nil))))))
      Sskip)
    (Ssequence
      (Sifthenelse (Etempvar _reset tint)
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 64) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'2
                      (Ederef
                        (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                          (Etempvar _i tint) (tptr tuchar)) tuchar))
                    (Sset _aux (Ecast (Etempvar _t'2 tuchar) tuchar)))
                  (Ssequence
                    (Sset _aux
                      (Ecast
                        (Ebinop Oxor (Econst_int (Int.repr 54) tint)
                          (Etempvar _aux tuchar) tint) tuchar))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _pad (tarray tuchar 64))
                          (Etempvar _i tint) (tptr tuchar)) tuchar)
                      (Etempvar _aux tuchar)))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Scall None
              (Evar _SHA256_Init (Tfunction
                                   (Tcons
                                     (tptr (Tstruct _SHA256state_st noattr))
                                     Tnil) tvoid cc_default))
              ((Eaddrof
                 (Efield
                   (Ederef
                     (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                     (Tstruct _hmac_ctx_st noattr)) _i_ctx
                   (Tstruct _SHA256state_st noattr))
                 (tptr (Tstruct _SHA256state_st noattr))) :: nil))
            (Ssequence
              (Scall None
                (Evar _SHA256_Update (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _SHA256state_st noattr))
                                         (Tcons (tptr tvoid)
                                           (Tcons tulong Tnil))) tvoid
                                       cc_default))
                ((Eaddrof
                   (Efield
                     (Ederef
                       (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                       (Tstruct _hmac_ctx_st noattr)) _i_ctx
                     (Tstruct _SHA256state_st noattr))
                   (tptr (Tstruct _SHA256state_st noattr))) ::
                 (Evar _pad (tarray tuchar 64)) ::
                 (Econst_int (Int.repr 64) tint) :: nil))
              (Ssequence
                (Ssequence
                  (Sset _i (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                     (Econst_int (Int.repr 64) tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Ssequence
                          (Sset _t'1
                            (Ederef
                              (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                                (Etempvar _i tint) (tptr tuchar)) tuchar))
                          (Sset _aux (Ecast (Etempvar _t'1 tuchar) tuchar)))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _pad (tarray tuchar 64))
                              (Etempvar _i tint) (tptr tuchar)) tuchar)
                          (Ebinop Oxor (Econst_int (Int.repr 92) tint)
                            (Etempvar _aux tuchar) tint))))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                (Ssequence
                  (Scall None
                    (Evar _SHA256_Init (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _SHA256state_st noattr))
                                           Tnil) tvoid cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                           (Tstruct _hmac_ctx_st noattr)) _o_ctx
                         (Tstruct _SHA256state_st noattr))
                       (tptr (Tstruct _SHA256state_st noattr))) :: nil))
                  (Scall None
                    (Evar _SHA256_Update (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _SHA256state_st noattr))
                                             (Tcons (tptr tvoid)
                                               (Tcons tulong Tnil))) tvoid
                                           cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                           (Tstruct _hmac_ctx_st noattr)) _o_ctx
                         (Tstruct _SHA256state_st noattr))
                       (tptr (Tstruct _SHA256state_st noattr))) ::
                     (Evar _pad (tarray tuchar 64)) ::
                     (Econst_int (Int.repr 64) tint) :: nil)))))))
        Sskip)
      (Scall None
        (Evar _memcpy (Tfunction
                        (Tcons (tptr tvoid)
                          (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                        (tptr tvoid) cc_default))
        ((Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
               (Tstruct _hmac_ctx_st noattr)) _md_ctx
             (Tstruct _SHA256state_st noattr))
           (tptr (Tstruct _SHA256state_st noattr))) ::
         (Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
               (Tstruct _hmac_ctx_st noattr)) _i_ctx
             (Tstruct _SHA256state_st noattr))
           (tptr (Tstruct _SHA256state_st noattr))) ::
         (Esizeof (Tstruct _SHA256state_st noattr) tulong) :: nil)))))
|}.

Definition f_HMAC_Update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) ::
                (_data, (tptr tvoid)) :: (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _SHA256_Update (Tfunction
                         (Tcons (tptr (Tstruct _SHA256state_st noattr))
                           (Tcons (tptr tvoid) (Tcons tulong Tnil))) tvoid
                         cc_default))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
         (Tstruct _hmac_ctx_st noattr)) _md_ctx
       (Tstruct _SHA256state_st noattr))
     (tptr (Tstruct _SHA256state_st noattr))) ::
   (Etempvar _data (tptr tvoid)) :: (Etempvar _len tulong) :: nil))
|}.

Definition f_HMAC_Final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) ::
                (_md, (tptr tuchar)) :: nil);
  fn_vars := ((_buf, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _SHA256_Final (Tfunction
                          (Tcons (tptr tuchar)
                            (Tcons (tptr (Tstruct _SHA256state_st noattr))
                              Tnil)) tvoid cc_default))
    ((Evar _buf (tarray tuchar 32)) ::
     (Eaddrof
       (Efield
         (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
           (Tstruct _hmac_ctx_st noattr)) _md_ctx
         (Tstruct _SHA256state_st noattr))
       (tptr (Tstruct _SHA256state_st noattr))) :: nil))
  (Ssequence
    (Scall None
      (Evar _memcpy (Tfunction
                      (Tcons (tptr tvoid)
                        (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                      (tptr tvoid) cc_default))
      ((Eaddrof
         (Efield
           (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
             (Tstruct _hmac_ctx_st noattr)) _md_ctx
           (Tstruct _SHA256state_st noattr))
         (tptr (Tstruct _SHA256state_st noattr))) ::
       (Eaddrof
         (Efield
           (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
             (Tstruct _hmac_ctx_st noattr)) _o_ctx
           (Tstruct _SHA256state_st noattr))
         (tptr (Tstruct _SHA256state_st noattr))) ::
       (Esizeof (Tstruct _SHA256state_st noattr) tulong) :: nil))
    (Ssequence
      (Scall None
        (Evar _SHA256_Update (Tfunction
                               (Tcons (tptr (Tstruct _SHA256state_st noattr))
                                 (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                               tvoid cc_default))
        ((Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
               (Tstruct _hmac_ctx_st noattr)) _md_ctx
             (Tstruct _SHA256state_st noattr))
           (tptr (Tstruct _SHA256state_st noattr))) ::
         (Evar _buf (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
         nil))
      (Scall None
        (Evar _SHA256_Final (Tfunction
                              (Tcons (tptr tuchar)
                                (Tcons
                                  (tptr (Tstruct _SHA256state_st noattr))
                                  Tnil)) tvoid cc_default))
        ((Etempvar _md (tptr tuchar)) ::
         (Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
               (Tstruct _hmac_ctx_st noattr)) _md_ctx
             (Tstruct _SHA256state_st noattr))
           (tptr (Tstruct _SHA256state_st noattr))) :: nil)))))
|}.

Definition f_HMAC_cleanup := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction
                  (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil)))
                  (tptr tvoid) cc_default))
  ((Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr))) ::
   (Econst_int (Int.repr 0) tint) ::
   (Esizeof (Tstruct _hmac_ctx_st noattr) tulong) :: nil))
|}.

Definition v_m := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_HMAC := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tuchar)) :: (_key_len, tint) ::
                (_d, (tptr tuchar)) :: (_n, tint) :: (_md, (tptr tuchar)) ::
                nil);
  fn_vars := ((_c, (Tstruct _hmac_ctx_st noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _md (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sset _md (Evar _m (tarray tuchar 32)))
    Sskip)
  (Ssequence
    (Scall None
      (Evar _HMAC_Init (Tfunction
                         (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                           (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                         cc_default))
      ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
         (tptr (Tstruct _hmac_ctx_st noattr))) ::
       (Etempvar _key (tptr tuchar)) :: (Etempvar _key_len tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _HMAC_Update (Tfunction
                             (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                               (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                             tvoid cc_default))
        ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
           (tptr (Tstruct _hmac_ctx_st noattr))) ::
         (Etempvar _d (tptr tuchar)) :: (Etempvar _n tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _HMAC_Final (Tfunction
                              (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                                (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
          ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
             (tptr (Tstruct _hmac_ctx_st noattr))) ::
           (Etempvar _md (tptr tuchar)) :: nil))
        (Ssequence
          (Scall None
            (Evar _HMAC_cleanup (Tfunction
                                  (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                                    Tnil) tvoid cc_default))
            ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
               (tptr (Tstruct _hmac_ctx_st noattr))) :: nil))
          (Sreturn (Some (Etempvar _md (tptr tuchar)))))))))
|}.

Definition v_m__1 := {|
  gvar_info := (tarray tuchar 64);
  gvar_init := (Init_space 64 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_HMAC2 := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tuchar)) :: (_key_len, tint) ::
                (_d, (tptr tuchar)) :: (_n, tint) :: (_md, (tptr tuchar)) ::
                nil);
  fn_vars := ((_c, (Tstruct _hmac_ctx_st noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _md (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sset _md (Evar _m__1 (tarray tuchar 64)))
    Sskip)
  (Ssequence
    (Scall None
      (Evar _HMAC_Init (Tfunction
                         (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                           (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                         cc_default))
      ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
         (tptr (Tstruct _hmac_ctx_st noattr))) ::
       (Etempvar _key (tptr tuchar)) :: (Etempvar _key_len tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _HMAC_Update (Tfunction
                             (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                               (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                             tvoid cc_default))
        ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
           (tptr (Tstruct _hmac_ctx_st noattr))) ::
         (Etempvar _d (tptr tuchar)) :: (Etempvar _n tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _HMAC_Final (Tfunction
                              (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                                (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
          ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
             (tptr (Tstruct _hmac_ctx_st noattr))) ::
           (Etempvar _md (tptr tuchar)) :: nil))
        (Ssequence
          (Scall None
            (Evar _HMAC_Init (Tfunction
                               (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                                 (Tcons (tptr tuchar) (Tcons tint Tnil)))
                               tvoid cc_default))
            ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
               (tptr (Tstruct _hmac_ctx_st noattr))) ::
             (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
             (Etempvar _key_len tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _HMAC_Update (Tfunction
                                   (Tcons
                                     (tptr (Tstruct _hmac_ctx_st noattr))
                                     (Tcons (tptr tvoid) (Tcons tulong Tnil)))
                                   tvoid cc_default))
              ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
                 (tptr (Tstruct _hmac_ctx_st noattr))) ::
               (Etempvar _d (tptr tuchar)) :: (Etempvar _n tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _HMAC_Final (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _hmac_ctx_st noattr))
                                      (Tcons (tptr tuchar) Tnil)) tvoid
                                    cc_default))
                ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
                   (tptr (Tstruct _hmac_ctx_st noattr))) ::
                 (Ebinop Oadd (Etempvar _md (tptr tuchar))
                   (Econst_int (Int.repr 32) tint) (tptr tuchar)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _HMAC_cleanup (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _hmac_ctx_st noattr))
                                          Tnil) tvoid cc_default))
                  ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
                     (tptr (Tstruct _hmac_ctx_st noattr))) :: nil))
                (Sreturn (Some (Etempvar _md (tptr tuchar))))))))))))
|}.

Definition v_mocked_sha256_info := {|
  gvar_info := (Tstruct _mbedtls_md_info_t noattr);
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_mbedtls_md_info_from_string := {|
  fn_return := (tptr (Tstruct _mbedtls_md_info_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_md_name, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof
                 (Evar _mocked_sha256_info (Tstruct _mbedtls_md_info_t noattr))
                 (tptr (Tstruct _mbedtls_md_info_t noattr)))))
|}.

Definition f_mbedtls_md_info_from_type := {|
  fn_return := (tptr (Tstruct _mbedtls_md_info_t noattr));
  fn_callconv := cc_default;
  fn_params := ((_md_type, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof
                 (Evar _mocked_sha256_info (Tstruct _mbedtls_md_info_t noattr))
                 (tptr (Tstruct _mbedtls_md_info_t noattr)))))
|}.

Definition f_mbedtls_md_get_size := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 32) tint)))
|}.

Definition f_test_md_get_size := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_info, (Tstruct _mbedtls_md_info_t noattr)) :: nil);
  fn_temps := ((_ret, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _mbedtls_md_get_size (Tfunction
                                 (Tcons
                                   (tptr (Tstruct _mbedtls_md_info_t noattr))
                                   Tnil) tuchar cc_default))
    ((Eaddrof (Evar _info (Tstruct _mbedtls_md_info_t noattr))
       (tptr (Tstruct _mbedtls_md_info_t noattr))) :: nil))
  (Sset _ret (Ecast (Etempvar _t'1 tuchar) tuchar)))
|}.

Definition f_mbedtls_md_setup := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                (_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
                (_hmac, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_sha_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _hmac_ctx_st noattr) tulong) :: nil))
    (Sset _sha_ctx
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _hmac_ctx_st noattr)))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Etempvar _sha_ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 20864) tint) tint)))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef
            (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
            (Tstruct _mbedtls_md_context_t noattr)) _hmac_ctx (tptr tvoid))
        (Etempvar _sha_ctx (tptr (Tstruct _hmac_ctx_st noattr))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
              (Tstruct _mbedtls_md_context_t noattr)) _md_info
            (tptr (Tstruct _mbedtls_md_info_t noattr)))
          (Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_mbedtls_md_hmac_starts := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                (_key, (tptr tuchar)) :: (_keylen, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_hmac_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _hmac_ctx
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
        (Tstruct _mbedtls_md_context_t noattr)) _hmac_ctx (tptr tvoid)))
  (Ssequence
    (Scall None
      (Evar _HMAC_Init (Tfunction
                         (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                           (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                         cc_default))
      ((Etempvar _hmac_ctx (tptr (Tstruct _hmac_ctx_st noattr))) ::
       (Ecast (Etempvar _key (tptr tuchar)) (tptr tuchar)) ::
       (Etempvar _keylen tulong) :: nil))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_mbedtls_md_hmac_reset := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_md_context_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_hmac_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _hmac_ctx
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
        (Tstruct _mbedtls_md_context_t noattr)) _hmac_ctx (tptr tvoid)))
  (Ssequence
    (Scall None
      (Evar _HMAC_Init (Tfunction
                         (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                           (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                         cc_default))
      ((Etempvar _hmac_ctx (tptr (Tstruct _hmac_ctx_st noattr))) ::
       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_mbedtls_md_hmac_update := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                (_input, (tptr tuchar)) :: (_ilen, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_hmac_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _hmac_ctx
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
        (Tstruct _mbedtls_md_context_t noattr)) _hmac_ctx (tptr tvoid)))
  (Ssequence
    (Scall None
      (Evar _HMAC_Update (Tfunction
                           (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                             (Tcons (tptr tvoid) (Tcons tulong Tnil))) tvoid
                           cc_default))
      ((Etempvar _hmac_ctx (tptr (Tstruct _hmac_ctx_st noattr))) ::
       (Ecast (Etempvar _input (tptr tuchar)) (tptr tvoid)) ::
       (Etempvar _ilen tulong) :: nil))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_mbedtls_md_hmac_finish := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                (_output, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_hmac_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _hmac_ctx
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
        (Tstruct _mbedtls_md_context_t noattr)) _hmac_ctx (tptr tvoid)))
  (Ssequence
    (Scall None
      (Evar _HMAC_Final (Tfunction
                          (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                            (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
      ((Etempvar _hmac_ctx (tptr (Tstruct _hmac_ctx_st noattr))) ::
       (Etempvar _output (tptr tuchar)) :: nil))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_mbedtls_md_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_md_context_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_hmac_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _hmac_ctx
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
        (Tstruct _mbedtls_md_context_t noattr)) _hmac_ctx (tptr tvoid)))
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Etempvar _hmac_ctx (tptr (Tstruct _hmac_ctx_st noattr))) :: nil)))
|}.

Definition f_mbedtls_zeroize := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, (tptr tvoid)) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tuchar)) :: (_t'2, (tptr tuchar)) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _p (Etempvar _v (tptr tvoid)))
  (Sloop
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'1 (Etempvar _n tulong))
          (Sset _n
            (Ebinop Osub (Etempvar _t'1 tulong)
              (Econst_int (Int.repr 1) tint) tulong)))
        (Sifthenelse (Etempvar _t'1 tulong) Sskip Sbreak))
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

Definition f_mbedtls_hmac_drbg_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction
                  (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil)))
                  (tptr tvoid) cc_default))
  ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
   (Econst_int (Int.repr 0) tint) ::
   (Esizeof (Tstruct _mbedtls_hmac_drbg_context noattr) tulong) :: nil))
|}.

Definition f_mbedtls_hmac_drbg_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_additional, (tptr tuchar)) :: (_add_len, tulong) :: nil);
  fn_vars := ((_sep, (tarray tuchar 1)) :: (_K, (tarray tuchar 32)) :: nil);
  fn_temps := ((_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
               (_md_len, tulong) :: (_rounds, tint) :: (_sep_value, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _info
    (Efield
      (Efield
        (Ederef
          (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
          (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
        (Tstruct _mbedtls_md_context_t noattr)) _md_info
      (tptr (Tstruct _mbedtls_md_info_t noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _mbedtls_md_get_size (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _mbedtls_md_info_t noattr))
                                       Tnil) tuchar cc_default))
        ((Etempvar _info (tptr (Tstruct _mbedtls_md_info_t noattr))) :: nil))
      (Sset _md_len (Ecast (Etempvar _t'1 tuchar) tulong)))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop One (Etempvar _add_len tulong)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sset _t'2
              (Ecast
                (Ebinop One (Etempvar _additional (tptr tuchar))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
                tbool))
            (Sset _t'2 (Econst_int (Int.repr 0) tint)))
          (Sifthenelse (Etempvar _t'2 tint)
            (Sset _t'3 (Ecast (Econst_int (Int.repr 2) tint) tint))
            (Sset _t'3 (Ecast (Econst_int (Int.repr 1) tint) tint))))
        (Sset _rounds (Etempvar _t'3 tint)))
      (Ssequence
        (Sset _sep_value (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _sep_value tint)
                           (Etempvar _rounds tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _sep (tarray tuchar 1))
                    (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
                (Etempvar _sep_value tint))
              (Ssequence
                (Scall None
                  (Evar _mbedtls_md_hmac_reset (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                   Tnil) tint cc_default))
                  ((Eaddrof
                     (Efield
                       (Ederef
                         (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                         (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
                       (Tstruct _mbedtls_md_context_t noattr))
                     (tptr (Tstruct _mbedtls_md_context_t noattr))) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _mbedtls_md_hmac_update (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                      (Tcons (tptr tuchar)
                                                        (Tcons tulong Tnil)))
                                                    tint cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                           (Tstruct _mbedtls_hmac_drbg_context noattr))
                         _md_ctx (Tstruct _mbedtls_md_context_t noattr))
                       (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                     (Efield
                       (Ederef
                         (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                         (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
                       (tarray tuchar 32)) :: (Etempvar _md_len tulong) ::
                     nil))
                  (Ssequence
                    (Scall None
                      (Evar _mbedtls_md_hmac_update (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                        (Tcons (tptr tuchar)
                                                          (Tcons tulong Tnil)))
                                                      tint cc_default))
                      ((Eaddrof
                         (Efield
                           (Ederef
                             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                             (Tstruct _mbedtls_hmac_drbg_context noattr))
                           _md_ctx (Tstruct _mbedtls_md_context_t noattr))
                         (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                       (Evar _sep (tarray tuchar 1)) ::
                       (Econst_int (Int.repr 1) tint) :: nil))
                    (Ssequence
                      (Sifthenelse (Ebinop Oeq (Etempvar _rounds tint)
                                     (Econst_int (Int.repr 2) tint) tint)
                        (Scall None
                          (Evar _mbedtls_md_hmac_update (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                            (Tcons
                                                              (tptr tuchar)
                                                              (Tcons tulong
                                                                Tnil))) tint
                                                          cc_default))
                          ((Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                 (Tstruct _mbedtls_hmac_drbg_context noattr))
                               _md_ctx
                               (Tstruct _mbedtls_md_context_t noattr))
                             (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                           (Etempvar _additional (tptr tuchar)) ::
                           (Etempvar _add_len tulong) :: nil))
                        Sskip)
                      (Ssequence
                        (Scall None
                          (Evar _mbedtls_md_hmac_finish (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                            (Tcons
                                                              (tptr tuchar)
                                                              Tnil)) tint
                                                          cc_default))
                          ((Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                 (Tstruct _mbedtls_hmac_drbg_context noattr))
                               _md_ctx
                               (Tstruct _mbedtls_md_context_t noattr))
                             (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                           (Evar _K (tarray tuchar 32)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _mbedtls_md_hmac_starts (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                              (Tcons
                                                                (tptr tuchar)
                                                                (Tcons tulong
                                                                  Tnil)))
                                                            tint cc_default))
                            ((Eaddrof
                               (Efield
                                 (Ederef
                                   (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                   (Tstruct _mbedtls_hmac_drbg_context noattr))
                                 _md_ctx
                                 (Tstruct _mbedtls_md_context_t noattr))
                               (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                             (Evar _K (tarray tuchar 32)) ::
                             (Etempvar _md_len tulong) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _mbedtls_md_hmac_update (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                                (Tcons
                                                                  (tptr tuchar)
                                                                  (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                              tint
                                                              cc_default))
                              ((Eaddrof
                                 (Efield
                                   (Ederef
                                     (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                     (Tstruct _mbedtls_hmac_drbg_context noattr))
                                   _md_ctx
                                   (Tstruct _mbedtls_md_context_t noattr))
                                 (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                               (Efield
                                 (Ederef
                                   (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                   (Tstruct _mbedtls_hmac_drbg_context noattr))
                                 _V (tarray tuchar 32)) ::
                               (Etempvar _md_len tulong) :: nil))
                            (Scall None
                              (Evar _mbedtls_md_hmac_finish (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                                (Tcons
                                                                  (tptr tuchar)
                                                                  Tnil)) tint
                                                              cc_default))
                              ((Eaddrof
                                 (Efield
                                   (Ederef
                                     (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                     (Tstruct _mbedtls_hmac_drbg_context noattr))
                                   _md_ctx
                                   (Tstruct _mbedtls_md_context_t noattr))
                                 (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                               (Efield
                                 (Ederef
                                   (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                   (Tstruct _mbedtls_hmac_drbg_context noattr))
                                 _V (tarray tuchar 32)) :: nil)))))))))))
          (Sset _sep_value
            (Ebinop Oadd (Etempvar _sep_value tint)
              (Econst_int (Int.repr 1) tint) tint)))))))
|}.

Definition f_mbedtls_hmac_drbg_seed_buf := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
                (_data, (tptr tuchar)) :: (_data_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tint) :: (_t'4, tuchar) :: (_t'3, tuchar) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _mbedtls_md_setup (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _mbedtls_md_context_t noattr))
                                      (Tcons
                                        (tptr (Tstruct _mbedtls_md_info_t noattr))
                                        (Tcons tint Tnil))) tint cc_default))
          ((Eaddrof
             (Efield
               (Ederef
                 (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                 (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
               (Tstruct _mbedtls_md_context_t noattr))
             (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
           (Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
           (Econst_int (Int.repr 1) tint) :: nil))
        (Sset _t'2 (Ecast (Etempvar _t'1 tint) tint)))
      (Sset _ret (Etempvar _t'2 tint)))
    (Sifthenelse (Ebinop One (Etempvar _t'2 tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sreturn (Some (Etempvar _ret tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some _t'3)
        (Evar _mbedtls_md_get_size (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _mbedtls_md_info_t noattr))
                                       Tnil) tuchar cc_default))
        ((Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
         nil))
      (Scall None
        (Evar _mbedtls_md_hmac_starts (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _mbedtls_md_context_t noattr))
                                          (Tcons (tptr tuchar)
                                            (Tcons tulong Tnil))) tint
                                        cc_default))
        ((Eaddrof
           (Efield
             (Ederef
               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
               (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
             (Tstruct _mbedtls_md_context_t noattr))
           (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
         (Efield
           (Ederef
             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
             (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
           (tarray tuchar 32)) :: (Etempvar _t'3 tuchar) :: nil)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'4)
          (Evar _mbedtls_md_get_size (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _mbedtls_md_info_t noattr))
                                         Tnil) tuchar cc_default))
          ((Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
           nil))
        (Scall None
          (Evar _memset (Tfunction
                          (Tcons (tptr tvoid)
                            (Tcons tint (Tcons tulong Tnil))) (tptr tvoid)
                          cc_default))
          ((Efield
             (Ederef
               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
               (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
             (tarray tuchar 32)) :: (Econst_int (Int.repr 1) tint) ::
           (Etempvar _t'4 tuchar) :: nil)))
      (Ssequence
        (Scall None
          (Evar _mbedtls_hmac_drbg_update (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                              (Tcons (tptr tuchar)
                                                (Tcons tulong Tnil))) tvoid
                                            cc_default))
          ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
           (Etempvar _data (tptr tuchar)) :: (Etempvar _data_len tulong) ::
           nil))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_mbedtls_hmac_drbg_reseed := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_additional, (tptr tuchar)) :: (_len, tulong) :: nil);
  fn_vars := ((_seed, (tarray tuchar 384)) :: nil);
  fn_temps := ((_seedlen, tulong) :: (_entropy_len, tulong) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _entropy_len
    (Efield
      (Ederef
        (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
        (Tstruct _mbedtls_hmac_drbg_context noattr)) _entropy_len tulong))
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Ogt (Etempvar _len tulong)
                     (Econst_int (Int.repr 256) tint) tint)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Sset _t'1
          (Ecast
            (Ebinop Ogt
              (Ebinop Oadd (Etempvar _entropy_len tulong)
                (Etempvar _len tulong) tulong)
              (Econst_int (Int.repr 384) tint) tint) tbool)))
      (Sifthenelse (Etempvar _t'1 tint)
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 5) tint) tint)))
        Sskip))
    (Ssequence
      (Scall None
        (Evar _memset (Tfunction
                        (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil)))
                        (tptr tvoid) cc_default))
        ((Evar _seed (tarray tuchar 384)) ::
         (Econst_int (Int.repr 0) tint) ::
         (Econst_int (Int.repr 384) tint) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _get_entropy (Tfunction
                                 (Tcons (tptr tuchar) (Tcons tulong Tnil))
                                 tint cc_default))
            ((Evar _seed (tarray tuchar 384)) ::
             (Etempvar _entropy_len tulong) :: nil))
          (Sifthenelse (Ebinop One (Etempvar _t'2 tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 9) tint) tint)))
            Sskip))
        (Ssequence
          (Sset _seedlen (Etempvar _entropy_len tulong))
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop One (Etempvar _additional (tptr tuchar))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sset _t'3
                  (Ecast
                    (Ebinop One (Etempvar _len tulong)
                      (Econst_int (Int.repr 0) tint) tint) tbool))
                (Sset _t'3 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'3 tint)
                (Ssequence
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons (tptr tvoid)
                                        (Tcons tulong Tnil))) (tptr tvoid)
                                    cc_default))
                    ((Ebinop Oadd (Evar _seed (tarray tuchar 384))
                       (Etempvar _seedlen tulong) (tptr tuchar)) ::
                     (Etempvar _additional (tptr tuchar)) ::
                     (Etempvar _len tulong) :: nil))
                  (Sset _seedlen
                    (Ebinop Oadd (Etempvar _seedlen tulong)
                      (Etempvar _len tulong) tulong)))
                Sskip))
            (Ssequence
              (Scall None
                (Evar _mbedtls_hmac_drbg_update (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                    (Tcons (tptr tuchar)
                                                      (Tcons tulong Tnil)))
                                                  tvoid cc_default))
                ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                 (Evar _seed (tarray tuchar 384)) ::
                 (Etempvar _seedlen tulong) :: nil))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                      (Tstruct _mbedtls_hmac_drbg_context noattr))
                    _reseed_counter tint) (Econst_int (Int.repr 1) tint))
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
|}.

Definition f_mbedtls_hmac_drbg_seed := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
                (_custom, (tptr tuchar)) :: (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tint) :: (_entropy_len, tulong) ::
               (_md_size, tulong) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tuchar) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _mbedtls_md_setup (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _mbedtls_md_context_t noattr))
                                      (Tcons
                                        (tptr (Tstruct _mbedtls_md_info_t noattr))
                                        (Tcons tint Tnil))) tint cc_default))
          ((Eaddrof
             (Efield
               (Ederef
                 (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                 (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
               (Tstruct _mbedtls_md_context_t noattr))
             (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
           (Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
           (Econst_int (Int.repr 1) tint) :: nil))
        (Sset _t'2 (Ecast (Etempvar _t'1 tint) tint)))
      (Sset _ret (Etempvar _t'2 tint)))
    (Sifthenelse (Ebinop One (Etempvar _t'2 tint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sreturn (Some (Etempvar _ret tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some _t'3)
        (Evar _mbedtls_md_get_size (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _mbedtls_md_info_t noattr))
                                       Tnil) tuchar cc_default))
        ((Etempvar _md_info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
         nil))
      (Sset _md_size (Ecast (Etempvar _t'3 tuchar) tulong)))
    (Ssequence
      (Scall None
        (Evar _mbedtls_md_hmac_starts (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _mbedtls_md_context_t noattr))
                                          (Tcons (tptr tuchar)
                                            (Tcons tulong Tnil))) tint
                                        cc_default))
        ((Eaddrof
           (Efield
             (Ederef
               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
               (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
             (Tstruct _mbedtls_md_context_t noattr))
           (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
         (Efield
           (Ederef
             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
             (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
           (tarray tuchar 32)) :: (Etempvar _md_size tulong) :: nil))
      (Ssequence
        (Scall None
          (Evar _memset (Tfunction
                          (Tcons (tptr tvoid)
                            (Tcons tint (Tcons tulong Tnil))) (tptr tvoid)
                          cc_default))
          ((Efield
             (Ederef
               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
               (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
             (tarray tuchar 32)) :: (Econst_int (Int.repr 1) tint) ::
           (Etempvar _md_size tulong) :: nil))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                (Tstruct _mbedtls_hmac_drbg_context noattr)) _reseed_interval
              tint) (Econst_int (Int.repr 10000) tint))
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Ole (Etempvar _md_size tulong)
                             (Econst_int (Int.repr 20) tint) tint)
                (Sset _t'4 (Ecast (Econst_int (Int.repr 16) tint) tint))
                (Sifthenelse (Ebinop Ole (Etempvar _md_size tulong)
                               (Econst_int (Int.repr 28) tint) tint)
                  (Ssequence
                    (Sset _t'4 (Ecast (Econst_int (Int.repr 24) tint) tint))
                    (Sset _t'4 (Ecast (Etempvar _t'4 tint) tint)))
                  (Ssequence
                    (Sset _t'4 (Ecast (Econst_int (Int.repr 32) tint) tint))
                    (Sset _t'4 (Ecast (Etempvar _t'4 tint) tint)))))
              (Sset _entropy_len (Ecast (Etempvar _t'4 tint) tulong)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                    (Tstruct _mbedtls_hmac_drbg_context noattr)) _entropy_len
                  tulong)
                (Ebinop Odiv
                  (Ebinop Omul (Etempvar _entropy_len tulong)
                    (Econst_int (Int.repr 3) tint) tulong)
                  (Econst_int (Int.repr 2) tint) tulong))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'5)
                        (Evar _mbedtls_hmac_drbg_reseed (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                            (Tcons
                                                              (tptr tuchar)
                                                              (Tcons tulong
                                                                Tnil))) tint
                                                          cc_default))
                        ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                         (Etempvar _custom (tptr tuchar)) ::
                         (Etempvar _len tulong) :: nil))
                      (Sset _t'6 (Ecast (Etempvar _t'5 tint) tint)))
                    (Sset _ret (Etempvar _t'6 tint)))
                  (Sifthenelse (Ebinop One (Etempvar _t'6 tint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Sreturn (Some (Etempvar _ret tint)))
                    Sskip))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                        (Tstruct _mbedtls_hmac_drbg_context noattr))
                      _entropy_len tulong) (Etempvar _entropy_len tulong))
                  (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))
|}.

Definition f_mbedtls_hmac_drbg_set_prediction_resistance := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_resistance, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef
      (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
      (Tstruct _mbedtls_hmac_drbg_context noattr)) _prediction_resistance
    tint) (Etempvar _resistance tint))
|}.

Definition f_mbedtls_hmac_drbg_set_entropy_len := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef
      (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
      (Tstruct _mbedtls_hmac_drbg_context noattr)) _entropy_len tulong)
  (Etempvar _len tulong))
|}.

Definition f_mbedtls_hmac_drbg_set_reseed_interval := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_interval, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef
      (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
      (Tstruct _mbedtls_hmac_drbg_context noattr)) _reseed_interval tint)
  (Etempvar _interval tint))
|}.

Definition f_mbedtls_hmac_drbg_random_with_add := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p_rng, (tptr tvoid)) :: (_output, (tptr tuchar)) ::
                (_out_len, tulong) :: (_additional, (tptr tuchar)) ::
                (_add_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tint) ::
               (_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
               (_md_len, tulong) :: (_left, tulong) ::
               (_out, (tptr tuchar)) ::
               (_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
               (_prediction_resistance, tint) :: (_reseed_counter, tint) ::
               (_reseed_interval, tint) :: (_use_len, tulong) ::
               (_t'6, tulong) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _ctx
    (Ecast (Etempvar _p_rng (tptr tvoid))
      (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))))
  (Ssequence
    (Sset _left (Etempvar _out_len tulong))
    (Ssequence
      (Sset _out (Etempvar _output (tptr tuchar)))
      (Ssequence
        (Sset _prediction_resistance
          (Efield
            (Ederef
              (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
              (Tstruct _mbedtls_hmac_drbg_context noattr))
            _prediction_resistance tint))
        (Ssequence
          (Sset _reseed_counter
            (Efield
              (Ederef
                (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                (Tstruct _mbedtls_hmac_drbg_context noattr)) _reseed_counter
              tint))
          (Ssequence
            (Sset _reseed_interval
              (Efield
                (Ederef
                  (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                  (Tstruct _mbedtls_hmac_drbg_context noattr))
                _reseed_interval tint))
            (Ssequence
              (Sset _info
                (Efield
                  (Efield
                    (Ederef
                      (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                      (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
                    (Tstruct _mbedtls_md_context_t noattr)) _md_info
                  (tptr (Tstruct _mbedtls_md_info_t noattr))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _mbedtls_md_get_size (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _mbedtls_md_info_t noattr))
                                                   Tnil) tuchar cc_default))
                    ((Etempvar _info (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
                     nil))
                  (Sset _md_len (Ecast (Etempvar _t'1 tuchar) tulong)))
                (Ssequence
                  (Sifthenelse (Ebinop Ogt (Etempvar _out_len tulong)
                                 (Econst_int (Int.repr 1024) tint) tint)
                    (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 3) tint)
                                     tint)))
                    Sskip)
                  (Ssequence
                    (Sifthenelse (Ebinop Ogt (Etempvar _add_len tulong)
                                   (Econst_int (Int.repr 256) tint) tint)
                      (Sreturn (Some (Eunop Oneg
                                       (Econst_int (Int.repr 5) tint) tint)))
                      Sskip)
                    (Ssequence
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq
                                       (Etempvar _prediction_resistance tint)
                                       (Econst_int (Int.repr 1) tint) tint)
                          (Sset _t'4 (Econst_int (Int.repr 1) tint))
                          (Sset _t'4
                            (Ecast
                              (Ebinop Ogt (Etempvar _reseed_counter tint)
                                (Etempvar _reseed_interval tint) tint) tbool)))
                        (Sifthenelse (Etempvar _t'4 tint)
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'2)
                                    (Evar _mbedtls_hmac_drbg_reseed (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tint
                                                                    cc_default))
                                    ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                                     (Etempvar _additional (tptr tuchar)) ::
                                     (Etempvar _add_len tulong) :: nil))
                                  (Sset _t'3
                                    (Ecast (Etempvar _t'2 tint) tint)))
                                (Sset _ret (Etempvar _t'3 tint)))
                              (Sifthenelse (Ebinop One (Etempvar _t'3 tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Sreturn (Some (Etempvar _ret tint)))
                                Sskip))
                            (Sset _add_len
                              (Ecast (Econst_int (Int.repr 0) tint) tulong)))
                          Sskip))
                      (Ssequence
                        (Ssequence
                          (Sifthenelse (Ebinop One
                                         (Etempvar _additional (tptr tuchar))
                                         (Ecast
                                           (Econst_int (Int.repr 0) tint)
                                           (tptr tvoid)) tint)
                            (Sset _t'5
                              (Ecast
                                (Ebinop One (Etempvar _add_len tulong)
                                  (Econst_int (Int.repr 0) tint) tint) tbool))
                            (Sset _t'5 (Econst_int (Int.repr 0) tint)))
                          (Sifthenelse (Etempvar _t'5 tint)
                            (Scall None
                              (Evar _mbedtls_hmac_drbg_update (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                                  (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                tvoid
                                                                cc_default))
                              ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                               (Etempvar _additional (tptr tuchar)) ::
                               (Etempvar _add_len tulong) :: nil))
                            Sskip))
                        (Ssequence
                          (Swhile
                            (Ebinop One (Etempvar _left tulong)
                              (Econst_int (Int.repr 0) tint) tint)
                            (Ssequence
                              (Ssequence
                                (Sifthenelse (Ebinop Ogt
                                               (Etempvar _left tulong)
                                               (Etempvar _md_len tulong)
                                               tint)
                                  (Sset _t'6
                                    (Ecast (Etempvar _md_len tulong) tulong))
                                  (Sset _t'6
                                    (Ecast (Etempvar _left tulong) tulong)))
                                (Sset _use_len (Etempvar _t'6 tulong)))
                              (Ssequence
                                (Scall None
                                  (Evar _mbedtls_md_hmac_reset (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                                   Tnil) tint
                                                                 cc_default))
                                  ((Eaddrof
                                     (Efield
                                       (Ederef
                                         (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                         (Tstruct _mbedtls_hmac_drbg_context noattr))
                                       _md_ctx
                                       (Tstruct _mbedtls_md_context_t noattr))
                                     (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                                   nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _mbedtls_md_hmac_update (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                    tint
                                                                    cc_default))
                                    ((Eaddrof
                                       (Efield
                                         (Ederef
                                           (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                           (Tstruct _mbedtls_hmac_drbg_context noattr))
                                         _md_ctx
                                         (Tstruct _mbedtls_md_context_t noattr))
                                       (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                                     (Efield
                                       (Ederef
                                         (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                         (Tstruct _mbedtls_hmac_drbg_context noattr))
                                       _V (tarray tuchar 32)) ::
                                     (Etempvar _md_len tulong) :: nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _mbedtls_md_hmac_finish (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    Tnil))
                                                                    tint
                                                                    cc_default))
                                      ((Eaddrof
                                         (Efield
                                           (Ederef
                                             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                             (Tstruct _mbedtls_hmac_drbg_context noattr))
                                           _md_ctx
                                           (Tstruct _mbedtls_md_context_t noattr))
                                         (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                                       (Efield
                                         (Ederef
                                           (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                           (Tstruct _mbedtls_hmac_drbg_context noattr))
                                         _V (tarray tuchar 32)) :: nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _memcpy (Tfunction
                                                        (Tcons (tptr tvoid)
                                                          (Tcons (tptr tvoid)
                                                            (Tcons tulong
                                                              Tnil)))
                                                        (tptr tvoid)
                                                        cc_default))
                                        ((Etempvar _out (tptr tuchar)) ::
                                         (Efield
                                           (Ederef
                                             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                             (Tstruct _mbedtls_hmac_drbg_context noattr))
                                           _V (tarray tuchar 32)) ::
                                         (Etempvar _use_len tulong) :: nil))
                                      (Ssequence
                                        (Sset _out
                                          (Ebinop Oadd
                                            (Etempvar _out (tptr tuchar))
                                            (Etempvar _use_len tulong)
                                            (tptr tuchar)))
                                        (Sset _left
                                          (Ebinop Osub
                                            (Etempvar _left tulong)
                                            (Etempvar _use_len tulong)
                                            tulong)))))))))
                          (Ssequence
                            (Scall None
                              (Evar _mbedtls_hmac_drbg_update (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                                  (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tulong
                                                                    Tnil)))
                                                                tvoid
                                                                cc_default))
                              ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                               (Etempvar _additional (tptr tuchar)) ::
                               (Etempvar _add_len tulong) :: nil))
                            (Ssequence
                              (Sset _reseed_counter
                                (Efield
                                  (Ederef
                                    (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                    (Tstruct _mbedtls_hmac_drbg_context noattr))
                                  _reseed_counter tint))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                      (Tstruct _mbedtls_hmac_drbg_context noattr))
                                    _reseed_counter tint)
                                  (Ebinop Oadd
                                    (Etempvar _reseed_counter tint)
                                    (Econst_int (Int.repr 1) tint) tint))
                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))
|}.

Definition f_mbedtls_hmac_drbg_random := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p_rng, (tptr tvoid)) :: (_output, (tptr tuchar)) ::
                (_out_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tint) ::
               (_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _ctx
    (Ecast (Etempvar _p_rng (tptr tvoid))
      (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _mbedtls_hmac_drbg_random_with_add (Tfunction
                                                   (Tcons (tptr tvoid)
                                                     (Tcons (tptr tuchar)
                                                       (Tcons tulong
                                                         (Tcons (tptr tuchar)
                                                           (Tcons tulong
                                                             Tnil))))) tint
                                                   cc_default))
        ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
         (Etempvar _output (tptr tuchar)) :: (Etempvar _out_len tulong) ::
         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
         (Econst_int (Int.repr 0) tint) :: nil))
      (Sset _ret (Etempvar _t'1 tint)))
    (Sreturn (Some (Etempvar _ret tint)))))
|}.

Definition f_mbedtls_hmac_drbg_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Scall None
      (Evar _mbedtls_md_free (Tfunction
                               (Tcons
                                 (tptr (Tstruct _mbedtls_md_context_t noattr))
                                 Tnil) tvoid cc_default))
      ((Eaddrof
         (Efield
           (Ederef
             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
             (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
           (Tstruct _mbedtls_md_context_t noattr))
         (tptr (Tstruct _mbedtls_md_context_t noattr))) :: nil))
    (Scall None
      (Evar _mbedtls_zeroize (Tfunction
                               (Tcons (tptr tvoid) (Tcons tulong Tnil)) tvoid
                               cc_default))
      ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
       (Esizeof (Tstruct _mbedtls_hmac_drbg_context noattr) tulong) :: nil))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _mbedtls_md_context_t Struct
   (Member_plain _md_info (tptr (Tstruct _mbedtls_md_info_t noattr)) ::
    Member_plain _md_ctx (tptr tvoid) ::
    Member_plain _hmac_ctx (tptr tvoid) :: nil)
   noattr ::
 Composite _mbedtls_hmac_drbg_context Struct
   (Member_plain _md_ctx (Tstruct _mbedtls_md_context_t noattr) ::
    Member_plain _V (tarray tuchar 32) ::
    Member_plain _reseed_counter tint :: Member_plain _entropy_len tulong ::
    Member_plain _prediction_resistance tint ::
    Member_plain _reseed_interval tint :: nil)
   noattr ::
 Composite _SHA256state_st Struct
   (Member_plain _h (tarray tuint 8) :: Member_plain _Nl tuint ::
    Member_plain _Nh tuint :: Member_plain _data (tarray tuchar 64) ::
    Member_plain _num tuint :: nil)
   noattr ::
 Composite _hmac_ctx_st Struct
   (Member_plain _md_ctx (Tstruct _SHA256state_st noattr) ::
    Member_plain _i_ctx (Tstruct _SHA256state_st noattr) ::
    Member_plain _o_ctx (Tstruct _SHA256state_st noattr) :: nil)
   noattr ::
 Composite _mbedtls_md_info_t Struct (Member_plain _dummy tint :: nil) noattr ::
 nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
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
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
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
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_fence,
   Gfun(External (EF_builtin "__builtin_fence"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
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
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil)))
     (tptr tvoid) cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid)
     cc_default)) ::
 (_SHA256_Init,
   Gfun(External (EF_external "SHA256_Init"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _SHA256state_st noattr)) Tnil) tvoid cc_default)) ::
 (_SHA256_Update,
   Gfun(External (EF_external "SHA256_Update"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _SHA256state_st noattr))
       (Tcons (tptr tvoid) (Tcons tulong Tnil))) tvoid cc_default)) ::
 (_SHA256_Final,
   Gfun(External (EF_external "SHA256_Final"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tuchar)
       (Tcons (tptr (Tstruct _SHA256state_st noattr)) Tnil)) tvoid
     cc_default)) :: (_HMAC_Init, Gfun(Internal f_HMAC_Init)) ::
 (_HMAC_Update, Gfun(Internal f_HMAC_Update)) ::
 (_HMAC_Final, Gfun(Internal f_HMAC_Final)) ::
 (_HMAC_cleanup, Gfun(Internal f_HMAC_cleanup)) :: (_m, Gvar v_m) ::
 (_HMAC, Gfun(Internal f_HMAC)) :: (_m__1, Gvar v_m__1) ::
 (_HMAC2, Gfun(Internal f_HMAC2)) ::
 (_mocked_sha256_info, Gvar v_mocked_sha256_info) ::
 (_mbedtls_md_info_from_string, Gfun(Internal f_mbedtls_md_info_from_string)) ::
 (_mbedtls_md_info_from_type, Gfun(Internal f_mbedtls_md_info_from_type)) ::
 (_mbedtls_md_get_size, Gfun(Internal f_mbedtls_md_get_size)) ::
 (_test_md_get_size, Gfun(Internal f_test_md_get_size)) ::
 (_mbedtls_md_setup, Gfun(Internal f_mbedtls_md_setup)) ::
 (_mbedtls_md_hmac_starts, Gfun(Internal f_mbedtls_md_hmac_starts)) ::
 (_mbedtls_md_hmac_reset, Gfun(Internal f_mbedtls_md_hmac_reset)) ::
 (_mbedtls_md_hmac_update, Gfun(Internal f_mbedtls_md_hmac_update)) ::
 (_mbedtls_md_hmac_finish, Gfun(Internal f_mbedtls_md_hmac_finish)) ::
 (_mbedtls_md_free, Gfun(Internal f_mbedtls_md_free)) ::
 (_get_entropy,
   Gfun(External (EF_external "get_entropy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tuchar) (Tcons tulong Tnil))
     tint cc_default)) ::
 (_mbedtls_zeroize, Gfun(Internal f_mbedtls_zeroize)) ::
 (_mbedtls_hmac_drbg_init, Gfun(Internal f_mbedtls_hmac_drbg_init)) ::
 (_mbedtls_hmac_drbg_update, Gfun(Internal f_mbedtls_hmac_drbg_update)) ::
 (_mbedtls_hmac_drbg_seed_buf, Gfun(Internal f_mbedtls_hmac_drbg_seed_buf)) ::
 (_mbedtls_hmac_drbg_reseed, Gfun(Internal f_mbedtls_hmac_drbg_reseed)) ::
 (_mbedtls_hmac_drbg_seed, Gfun(Internal f_mbedtls_hmac_drbg_seed)) ::
 (_mbedtls_hmac_drbg_set_prediction_resistance, Gfun(Internal f_mbedtls_hmac_drbg_set_prediction_resistance)) ::
 (_mbedtls_hmac_drbg_set_entropy_len, Gfun(Internal f_mbedtls_hmac_drbg_set_entropy_len)) ::
 (_mbedtls_hmac_drbg_set_reseed_interval, Gfun(Internal f_mbedtls_hmac_drbg_set_reseed_interval)) ::
 (_mbedtls_hmac_drbg_random_with_add, Gfun(Internal f_mbedtls_hmac_drbg_random_with_add)) ::
 (_mbedtls_hmac_drbg_random, Gfun(Internal f_mbedtls_hmac_drbg_random)) ::
 (_mbedtls_hmac_drbg_free, Gfun(Internal f_mbedtls_hmac_drbg_free)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _mbedtls_hmac_drbg_free :: _mbedtls_hmac_drbg_random ::
 _mbedtls_hmac_drbg_random_with_add ::
 _mbedtls_hmac_drbg_set_reseed_interval ::
 _mbedtls_hmac_drbg_set_entropy_len ::
 _mbedtls_hmac_drbg_set_prediction_resistance :: _mbedtls_hmac_drbg_seed ::
 _mbedtls_hmac_drbg_reseed :: _mbedtls_hmac_drbg_seed_buf ::
 _mbedtls_hmac_drbg_update :: _mbedtls_hmac_drbg_init :: _get_entropy ::
 _mbedtls_md_free :: _mbedtls_md_hmac_finish :: _mbedtls_md_hmac_update ::
 _mbedtls_md_hmac_reset :: _mbedtls_md_hmac_starts :: _mbedtls_md_setup ::
 _test_md_get_size :: _mbedtls_md_get_size :: _mbedtls_md_info_from_type ::
 _mbedtls_md_info_from_string :: _HMAC2 :: _HMAC :: _HMAC_cleanup ::
 _HMAC_Final :: _HMAC_Update :: _HMAC_Init :: _SHA256_Final ::
 _SHA256_Update :: _SHA256_Init :: _memset :: _memcpy :: _free :: _malloc ::
 ___builtin_debug :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
 ___builtin_fence :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


