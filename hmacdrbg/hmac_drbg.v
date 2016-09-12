
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition _HMAC : ident := 110%positive.
Definition _HMAC2 : ident := 112%positive.
Definition _HMAC_Final : ident := 106%positive.
Definition _HMAC_Init : ident := 103%positive.
Definition _HMAC_Update : ident := 104%positive.
Definition _HMAC_cleanup : ident := 107%positive.
Definition _K : ident := 156%positive.
Definition _K256 : ident := 57%positive.
Definition _Ki : ident := 74%positive.
Definition _Nh : ident := 3%positive.
Definition _Nl : ident := 2%positive.
Definition _SHA256 : ident := 91%positive.
Definition _SHA256_Final : ident := 90%positive.
Definition _SHA256_Init : ident := 77%positive.
Definition _SHA256_Update : ident := 86%positive.
Definition _SHA256_addlength : ident := 81%positive.
Definition _SHA256state_st : ident := 6%positive.
Definition _T1 : ident := 69%positive.
Definition _T2 : ident := 70%positive.
Definition _V : ident := 117%positive.
Definition _X : ident := 72%positive.
Definition ___builtin_annot : ident := 9%positive.
Definition ___builtin_annot_intval : ident := 10%positive.
Definition ___builtin_bswap : ident := 33%positive.
Definition ___builtin_bswap16 : ident := 35%positive.
Definition ___builtin_bswap32 : ident := 34%positive.
Definition ___builtin_clz : ident := 36%positive.
Definition ___builtin_clzl : ident := 37%positive.
Definition ___builtin_clzll : ident := 38%positive.
Definition ___builtin_ctz : ident := 39%positive.
Definition ___builtin_ctzl : ident := 40%positive.
Definition ___builtin_ctzll : ident := 41%positive.
Definition ___builtin_debug : ident := 52%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_fmadd : ident := 45%positive.
Definition ___builtin_fmax : ident := 43%positive.
Definition ___builtin_fmin : ident := 44%positive.
Definition ___builtin_fmsub : ident := 46%positive.
Definition ___builtin_fnmadd : ident := 47%positive.
Definition ___builtin_fnmsub : ident := 48%positive.
Definition ___builtin_fsqrt : ident := 42%positive.
Definition ___builtin_membar : ident := 11%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition ___builtin_nop : ident := 51%positive.
Definition ___builtin_read16_reversed : ident := 49%positive.
Definition ___builtin_read32_reversed : ident := 53%positive.
Definition ___builtin_va_arg : ident := 13%positive.
Definition ___builtin_va_copy : ident := 14%positive.
Definition ___builtin_va_end : ident := 15%positive.
Definition ___builtin_va_start : ident := 12%positive.
Definition ___builtin_write16_reversed : ident := 50%positive.
Definition ___builtin_write32_reversed : ident := 54%positive.
Definition ___compcert_va_composite : ident := 19%positive.
Definition ___compcert_va_float64 : ident := 18%positive.
Definition ___compcert_va_int32 : ident := 16%positive.
Definition ___compcert_va_int64 : ident := 17%positive.
Definition ___i64_dtos : ident := 20%positive.
Definition ___i64_dtou : ident := 21%positive.
Definition ___i64_sar : ident := 32%positive.
Definition ___i64_sdiv : ident := 26%positive.
Definition ___i64_shl : ident := 30%positive.
Definition ___i64_shr : ident := 31%positive.
Definition ___i64_smod : ident := 28%positive.
Definition ___i64_stod : ident := 22%positive.
Definition ___i64_stof : ident := 24%positive.
Definition ___i64_udiv : ident := 27%positive.
Definition ___i64_umod : ident := 29%positive.
Definition ___i64_utod : ident := 23%positive.
Definition ___i64_utof : ident := 25%positive.
Definition _a : ident := 60%positive.
Definition _add_len : ident := 152%positive.
Definition _additional : ident := 151%positive.
Definition _aux : ident := 101%positive.
Definition _b : ident := 61%positive.
Definition _buf : ident := 105%positive.
Definition _c : ident := 62%positive.
Definition _cNh : ident := 80%positive.
Definition _cNl : ident := 79%positive.
Definition _ctx : ident := 58%positive.
Definition _ctx_key : ident := 102%positive.
Definition _custom : ident := 164%positive.
Definition _d : ident := 63%positive.
Definition _data : ident := 4%positive.
Definition _data_ : ident := 82%positive.
Definition _data_len : ident := 159%positive.
Definition _dummy : ident := 123%positive.
Definition _e : ident := 64%positive.
Definition _entropy_len : ident := 119%positive.
Definition _f : ident := 65%positive.
Definition _fragment : ident := 85%positive.
Definition _free : ident := 125%positive.
Definition _g : ident := 66%positive.
Definition _get_entropy : ident := 147%positive.
Definition _h : ident := 1%positive.
Definition _hmac : ident := 135%positive.
Definition _hmac_ctx : ident := 115%positive.
Definition _hmac_ctx_st : ident := 96%positive.
Definition _i : ident := 75%positive.
Definition _i_ctx : ident := 94%positive.
Definition _ilen : ident := 142%positive.
Definition _in : ident := 59%positive.
Definition _info : ident := 132%positive.
Definition _input : ident := 141%positive.
Definition _interval : ident := 170%positive.
Definition _j : ident := 98%positive.
Definition _key : ident := 97%positive.
Definition _key_len : ident := 109%positive.
Definition _keylen : ident := 138%positive.
Definition _l : ident := 73%positive.
Definition _left : ident := 174%positive.
Definition _len : ident := 78%positive.
Definition _ll : ident := 88%positive.
Definition _m : ident := 108%positive.
Definition _m__1 : ident := 111%positive.
Definition _main : ident := 92%positive.
Definition _malloc : ident := 124%positive.
Definition _mbedtls_hmac_drbg_context : ident := 122%positive.
Definition _mbedtls_hmac_drbg_free : ident := 179%positive.
Definition _mbedtls_hmac_drbg_init : ident := 150%positive.
Definition _mbedtls_hmac_drbg_random : ident := 178%positive.
Definition _mbedtls_hmac_drbg_random_with_add : ident := 177%positive.
Definition _mbedtls_hmac_drbg_reseed : ident := 163%positive.
Definition _mbedtls_hmac_drbg_seed : ident := 166%positive.
Definition _mbedtls_hmac_drbg_seed_buf : ident := 160%positive.
Definition _mbedtls_hmac_drbg_set_entropy_len : ident := 169%positive.
Definition _mbedtls_hmac_drbg_set_prediction_resistance : ident := 168%positive.
Definition _mbedtls_hmac_drbg_set_reseed_interval : ident := 171%positive.
Definition _mbedtls_hmac_drbg_update : ident := 158%positive.
Definition _mbedtls_md_context_t : ident := 116%positive.
Definition _mbedtls_md_free : ident := 146%positive.
Definition _mbedtls_md_get_size : ident := 131%positive.
Definition _mbedtls_md_hmac_finish : ident := 145%positive.
Definition _mbedtls_md_hmac_reset : ident := 140%positive.
Definition _mbedtls_md_hmac_starts : ident := 139%positive.
Definition _mbedtls_md_hmac_update : ident := 143%positive.
Definition _mbedtls_md_info_from_string : ident := 128%positive.
Definition _mbedtls_md_info_from_type : ident := 130%positive.
Definition _mbedtls_md_info_t : ident := 113%positive.
Definition _mbedtls_md_setup : ident := 137%positive.
Definition _mbedtls_zeroize : ident := 149%positive.
Definition _md : ident := 87%positive.
Definition _md_ctx : ident := 93%positive.
Definition _md_info : ident := 114%positive.
Definition _md_len : ident := 153%positive.
Definition _md_name : ident := 127%positive.
Definition _md_size : ident := 165%positive.
Definition _md_type : ident := 129%positive.
Definition _memcpy : ident := 55%positive.
Definition _memset : ident := 56%positive.
Definition _mocked_sha256_info : ident := 126%positive.
Definition _n : ident := 84%positive.
Definition _num : ident := 5%positive.
Definition _o_ctx : ident := 95%positive.
Definition _out : ident := 175%positive.
Definition _out_len : ident := 173%positive.
Definition _output : ident := 144%positive.
Definition _p : ident := 83%positive.
Definition _p_rng : ident := 172%positive.
Definition _pad : ident := 100%positive.
Definition _prediction_resistance : ident := 120%positive.
Definition _reseed_counter : ident := 118%positive.
Definition _reseed_interval : ident := 121%positive.
Definition _reset : ident := 99%positive.
Definition _resistance : ident := 167%positive.
Definition _ret : ident := 133%positive.
Definition _rounds : ident := 154%positive.
Definition _s0 : ident := 67%positive.
Definition _s1 : ident := 68%positive.
Definition _seed : ident := 161%positive.
Definition _seedlen : ident := 162%positive.
Definition _sep : ident := 155%positive.
Definition _sep_value : ident := 157%positive.
Definition _sha256_block_data_order : ident := 76%positive.
Definition _sha_ctx : ident := 136%positive.
Definition _t : ident := 71%positive.
Definition _test_md_get_size : ident := 134%positive.
Definition _use_len : ident := 176%positive.
Definition _v : ident := 148%positive.
Definition _xn : ident := 89%positive.
Definition _t'1 : ident := 180%positive.
Definition _t'2 : ident := 181%positive.
Definition _t'3 : ident := 182%positive.
Definition _t'4 : ident := 183%positive.
Definition _t'5 : ident := 184%positive.
Definition _t'6 : ident := 185%positive.
Definition _t'7 : ident := 186%positive.

Definition f_HMAC_Init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) ::
                (_key, (tptr tuchar)) :: (_len, tint) :: nil);
  fn_vars := ((_pad, (tarray tuchar 64)) :: (_ctx_key, (tarray tuchar 64)) ::
              nil);
  fn_temps := ((_i, tint) :: (_j, tint) :: (_reset, tint) ::
               (_aux, tuchar) :: nil);
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
                                             (Tcons tuint Tnil))) tvoid
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
                                      (Tcons tint (Tcons tuint Tnil)))
                                    (tptr tvoid) cc_default))
                    ((Eaddrof
                       (Ederef
                         (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                           (Econst_int (Int.repr 32) tint) (tptr tuchar))
                         tuchar) (tptr tuchar)) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 32) tint) :: nil)))))
            (Ssequence
              (Scall None
                (Evar _memcpy (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                ((Evar _ctx_key (tarray tuchar 64)) ::
                 (Etempvar _key (tptr tuchar)) :: (Etempvar _len tint) ::
                 nil))
              (Scall None
                (Evar _memset (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                ((Eaddrof
                   (Ederef
                     (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                       (Etempvar _len tint) (tptr tuchar)) tuchar)
                   (tptr tuchar)) :: (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Osub (Esizeof (tarray tuchar 64) tuint)
                   (Etempvar _len tint) tuint) :: nil))))))
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
                  (Sset _aux
                    (Ecast
                      (Ederef
                        (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                          (Etempvar _i tint) (tptr tuchar)) tuchar) tuchar))
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
                                           (Tcons tuint Tnil))) tvoid
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
                        (Sset _aux
                          (Ecast
                            (Ederef
                              (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                                (Etempvar _i tint) (tptr tuchar)) tuchar)
                            tuchar))
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
                                               (Tcons tuint Tnil))) tvoid
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
                          (Tcons (tptr tvoid) (Tcons tuint Tnil)))
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
         (Esizeof (Tstruct _SHA256state_st noattr) tuint) :: nil)))))
|}.

Definition f_HMAC_Update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) ::
                (_data, (tptr tvoid)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _SHA256_Update (Tfunction
                         (Tcons (tptr (Tstruct _SHA256state_st noattr))
                           (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                         cc_default))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
         (Tstruct _hmac_ctx_st noattr)) _md_ctx
       (Tstruct _SHA256state_st noattr))
     (tptr (Tstruct _SHA256state_st noattr))) ::
   (Etempvar _data (tptr tvoid)) :: (Etempvar _len tuint) :: nil))
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
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) (tptr tvoid)
                      cc_default))
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
       (Esizeof (Tstruct _SHA256state_st noattr) tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar _SHA256_Update (Tfunction
                               (Tcons (tptr (Tstruct _SHA256state_st noattr))
                                 (Tcons (tptr tvoid) (Tcons tuint Tnil)))
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
                  (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                  (tptr tvoid) cc_default))
  ((Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr))) ::
   (Econst_int (Int.repr 0) tint) ::
   (Esizeof (Tstruct _hmac_ctx_st noattr) tuint) :: nil))
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
                               (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                             cc_default))
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
                               (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                             cc_default))
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
                                     (Tcons (tptr tvoid) (Tcons tuint Tnil)))
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
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _hmac_ctx_st noattr) tuint) :: nil))
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
                (_key, (tptr tuchar)) :: (_keylen, tuint) :: nil);
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
       (Etempvar _keylen tuint) :: nil))
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
                (_input, (tptr tuchar)) :: (_ilen, tuint) :: nil);
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
                             (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                           cc_default))
      ((Etempvar _hmac_ctx (tptr (Tstruct _hmac_ctx_st noattr))) ::
       (Ecast (Etempvar _input (tptr tuchar)) (tptr tvoid)) ::
       (Etempvar _ilen tuint) :: nil))
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
                  (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                  (tptr tvoid) cc_default))
  ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
   (Econst_int (Int.repr 0) tint) ::
   (Esizeof (Tstruct _mbedtls_hmac_drbg_context noattr) tuint) :: nil))
|}.

Definition f_mbedtls_hmac_drbg_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_additional, (tptr tuchar)) :: (_add_len, tuint) :: nil);
  fn_vars := ((_sep, (tarray tuchar 1)) :: (_K, (tarray tuchar 32)) :: nil);
  fn_temps := ((_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
               (_md_len, tuint) :: (_rounds, tint) :: (_sep_value, tint) ::
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
      (Sset _md_len (Etempvar _t'1 tuchar)))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop One (Etempvar _add_len tuint)
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
                                                        (Tcons tuint Tnil)))
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
                       (tarray tuchar 32)) :: (Etempvar _md_len tuint) ::
                     nil))
                  (Ssequence
                    (Scall None
                      (Evar _mbedtls_md_hmac_update (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                        (Tcons (tptr tuchar)
                                                          (Tcons tuint Tnil)))
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
                                                              (Tcons tuint
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
                           (Etempvar _add_len tuint) :: nil))
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
                                                                (Tcons tuint
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
                             (Etempvar _md_len tuint) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _mbedtls_md_hmac_update (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _mbedtls_md_context_t noattr))
                                                                (Tcons
                                                                  (tptr tuchar)
                                                                  (Tcons
                                                                    tuint
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
                               (Etempvar _md_len tuint) :: nil))
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
                (_data, (tptr tuchar)) :: (_data_len, tuint) :: nil);
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
                                            (Tcons tuint Tnil))) tint
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
                            (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
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
                                                (Tcons tuint Tnil))) tvoid
                                            cc_default))
          ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
           (Etempvar _data (tptr tuchar)) :: (Etempvar _data_len tuint) ::
           nil))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_mbedtls_hmac_drbg_reseed := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                (_additional, (tptr tuchar)) :: (_len, tuint) :: nil);
  fn_vars := ((_seed, (tarray tuchar 384)) :: nil);
  fn_temps := ((_seedlen, tuint) :: (_entropy_len, tuint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _entropy_len
    (Efield
      (Ederef
        (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
        (Tstruct _mbedtls_hmac_drbg_context noattr)) _entropy_len tuint))
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Ogt (Etempvar _len tuint)
                     (Econst_int (Int.repr 256) tint) tint)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Sset _t'1
          (Ecast
            (Ebinop Ogt
              (Ebinop Oadd (Etempvar _entropy_len tuint)
                (Etempvar _len tuint) tuint) (Econst_int (Int.repr 384) tint)
              tint) tbool)))
      (Sifthenelse (Etempvar _t'1 tint)
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 5) tint) tint)))
        Sskip))
    (Ssequence
      (Scall None
        (Evar _memset (Tfunction
                        (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                        (tptr tvoid) cc_default))
        ((Evar _seed (tarray tuchar 384)) ::
         (Econst_int (Int.repr 0) tint) ::
         (Econst_int (Int.repr 384) tint) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _get_entropy (Tfunction
                                 (Tcons (tptr tuchar) (Tcons tuint Tnil))
                                 tint cc_default))
            ((Evar _seed (tarray tuchar 384)) ::
             (Etempvar _entropy_len tuint) :: nil))
          (Sifthenelse (Ebinop One (Etempvar _t'2 tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 9) tint) tint)))
            Sskip))
        (Ssequence
          (Sset _seedlen (Etempvar _entropy_len tuint))
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop One (Etempvar _additional (tptr tuchar))
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) tint)
                (Sset _t'3
                  (Ecast
                    (Ebinop One (Etempvar _len tuint)
                      (Econst_int (Int.repr 0) tint) tint) tbool))
                (Sset _t'3 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'3 tint)
                (Ssequence
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                    (tptr tvoid) cc_default))
                    ((Ebinop Oadd (Evar _seed (tarray tuchar 384))
                       (Etempvar _seedlen tuint) (tptr tuchar)) ::
                     (Etempvar _additional (tptr tuchar)) ::
                     (Etempvar _len tuint) :: nil))
                  (Sset _seedlen
                    (Ebinop Oadd (Etempvar _seedlen tuint)
                      (Etempvar _len tuint) tuint)))
                Sskip))
            (Ssequence
              (Scall None
                (Evar _mbedtls_hmac_drbg_update (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                    (Tcons (tptr tuchar)
                                                      (Tcons tuint Tnil)))
                                                  tvoid cc_default))
                ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                 (Evar _seed (tarray tuchar 384)) ::
                 (Etempvar _seedlen tuint) :: nil))
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
                (_custom, (tptr tuchar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tint) :: (_entropy_len, tuint) :: (_md_size, tuint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
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
      (Sset _md_size (Etempvar _t'3 tuchar)))
    (Ssequence
      (Scall None
        (Evar _mbedtls_md_hmac_starts (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _mbedtls_md_context_t noattr))
                                          (Tcons (tptr tuchar)
                                            (Tcons tuint Tnil))) tint
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
           (tarray tuchar 32)) :: (Etempvar _md_size tuint) :: nil))
      (Ssequence
        (Scall None
          (Evar _memset (Tfunction
                          (Tcons (tptr tvoid)
                            (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
                          cc_default))
          ((Efield
             (Ederef
               (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
               (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
             (tarray tuchar 32)) :: (Econst_int (Int.repr 1) tint) ::
           (Etempvar _md_size tuint) :: nil))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                (Tstruct _mbedtls_hmac_drbg_context noattr)) _reseed_interval
              tint) (Econst_int (Int.repr 10000) tint))
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Ole (Etempvar _md_size tuint)
                             (Econst_int (Int.repr 20) tint) tint)
                (Sset _t'4 (Ecast (Econst_int (Int.repr 16) tint) tint))
                (Sifthenelse (Ebinop Ole (Etempvar _md_size tuint)
                               (Econst_int (Int.repr 28) tint) tint)
                  (Ssequence
                    (Sset _t'5 (Ecast (Econst_int (Int.repr 24) tint) tint))
                    (Sset _t'4 (Ecast (Etempvar _t'5 tint) tint)))
                  (Ssequence
                    (Sset _t'5 (Ecast (Econst_int (Int.repr 32) tint) tint))
                    (Sset _t'4 (Ecast (Etempvar _t'5 tint) tint)))))
              (Sset _entropy_len (Etempvar _t'4 tint)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                    (Tstruct _mbedtls_hmac_drbg_context noattr)) _entropy_len
                  tuint)
                (Ebinop Odiv
                  (Ebinop Omul (Etempvar _entropy_len tuint)
                    (Econst_int (Int.repr 3) tint) tuint)
                  (Econst_int (Int.repr 2) tint) tuint))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'6)
                        (Evar _mbedtls_hmac_drbg_reseed (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                            (Tcons
                                                              (tptr tuchar)
                                                              (Tcons tuint
                                                                Tnil))) tint
                                                          cc_default))
                        ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                         (Etempvar _custom (tptr tuchar)) ::
                         (Etempvar _len tuint) :: nil))
                      (Sset _t'7 (Ecast (Etempvar _t'6 tint) tint)))
                    (Sset _ret (Etempvar _t'7 tint)))
                  (Sifthenelse (Ebinop One (Etempvar _t'7 tint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    (Sreturn (Some (Etempvar _ret tint)))
                    Sskip))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                        (Tstruct _mbedtls_hmac_drbg_context noattr))
                      _entropy_len tuint) (Etempvar _entropy_len tuint))
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
                (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef
      (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
      (Tstruct _mbedtls_hmac_drbg_context noattr)) _entropy_len tuint)
  (Etempvar _len tuint))
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
                (_out_len, tuint) :: (_additional, (tptr tuchar)) ::
                (_add_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ret, tint) ::
               (_ctx, (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
               (_md_len, tuint) :: (_left, tuint) :: (_out, (tptr tuchar)) ::
               (_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
               (_prediction_resistance, tint) :: (_reseed_counter, tint) ::
               (_reseed_interval, tint) :: (_use_len, tuint) ::
               (_t'6, tuint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _ctx
    (Ecast (Etempvar _p_rng (tptr tvoid))
      (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))))
  (Ssequence
    (Sset _left (Etempvar _out_len tuint))
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
                  (Sset _md_len (Etempvar _t'1 tuchar)))
                (Ssequence
                  (Sifthenelse (Ebinop Ogt (Etempvar _out_len tuint)
                                 (Econst_int (Int.repr 1024) tint) tint)
                    (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 3) tint)
                                     tint)))
                    Sskip)
                  (Ssequence
                    (Sifthenelse (Ebinop Ogt (Etempvar _add_len tuint)
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
                                                                    tuint
                                                                    Tnil)))
                                                                    tint
                                                                    cc_default))
                                    ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                                     (Etempvar _additional (tptr tuchar)) ::
                                     (Etempvar _add_len tuint) :: nil))
                                  (Sset _t'3
                                    (Ecast (Etempvar _t'2 tint) tint)))
                                (Sset _ret (Etempvar _t'3 tint)))
                              (Sifthenelse (Ebinop One (Etempvar _t'3 tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Sreturn (Some (Etempvar _ret tint)))
                                Sskip))
                            (Sset _add_len (Econst_int (Int.repr 0) tint)))
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
                                (Ebinop One (Etempvar _add_len tuint)
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
                                                                    tuint
                                                                    Tnil)))
                                                                tvoid
                                                                cc_default))
                              ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                               (Etempvar _additional (tptr tuchar)) ::
                               (Etempvar _add_len tuint) :: nil))
                            Sskip))
                        (Ssequence
                          (Swhile
                            (Ebinop One (Etempvar _left tuint)
                              (Econst_int (Int.repr 0) tint) tint)
                            (Ssequence
                              (Ssequence
                                (Sifthenelse (Ebinop Ogt
                                               (Etempvar _left tuint)
                                               (Etempvar _md_len tuint) tint)
                                  (Sset _t'6
                                    (Ecast (Etempvar _md_len tuint) tuint))
                                  (Sset _t'6
                                    (Ecast (Etempvar _left tuint) tuint)))
                                (Sset _use_len (Etempvar _t'6 tuint)))
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
                                                                    tuint
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
                                     (Etempvar _md_len tuint) :: nil))
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
                                                            (Tcons tuint
                                                              Tnil)))
                                                        (tptr tvoid)
                                                        cc_default))
                                        ((Etempvar _out (tptr tuchar)) ::
                                         (Efield
                                           (Ederef
                                             (Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                                             (Tstruct _mbedtls_hmac_drbg_context noattr))
                                           _V (tarray tuchar 32)) ::
                                         (Etempvar _use_len tuint) :: nil))
                                      (Ssequence
                                        (Sset _out
                                          (Ebinop Oadd
                                            (Etempvar _out (tptr tuchar))
                                            (Etempvar _use_len tuint)
                                            (tptr tuchar)))
                                        (Sset _left
                                          (Ebinop Osub (Etempvar _left tuint)
                                            (Etempvar _use_len tuint) tuint)))))))))
                          (Ssequence
                            (Scall None
                              (Evar _mbedtls_hmac_drbg_update (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                                                                  (Tcons
                                                                    (tptr tuchar)
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                tvoid
                                                                cc_default))
                              ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
                               (Etempvar _additional (tptr tuchar)) ::
                               (Etempvar _add_len tuint) :: nil))
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
                (_out_len, tuint) :: nil);
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
                                                       (Tcons tuint
                                                         (Tcons (tptr tuchar)
                                                           (Tcons tuint Tnil)))))
                                                   tint cc_default))
        ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
         (Etempvar _output (tptr tuchar)) :: (Etempvar _out_len tuint) ::
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
                               (Tcons (tptr tvoid) (Tcons tuint Tnil)) tvoid
                               cc_default))
      ((Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))) ::
       (Esizeof (Tstruct _mbedtls_hmac_drbg_context noattr) tuint) :: nil))))
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
   ((_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
    (_md_ctx, (tptr tvoid)) :: (_hmac_ctx, (tptr tvoid)) :: nil)
   noattr ::
 Composite _mbedtls_hmac_drbg_context Struct
   ((_md_ctx, (Tstruct _mbedtls_md_context_t noattr)) ::
    (_V, (tarray tuchar 32)) :: (_reseed_counter, tint) ::
    (_entropy_len, tuint) :: (_prediction_resistance, tint) ::
    (_reseed_interval, tint) :: nil)
   noattr ::
 Composite _SHA256state_st Struct
   ((_h, (tarray tuint 8)) :: (_Nl, tuint) :: (_Nh, tuint) ::
    (_data, (tarray tuchar 64)) :: (_num, tuint) :: nil)
   noattr ::
 Composite _hmac_ctx_st Struct
   ((_md_ctx, (Tstruct _SHA256state_st noattr)) ::
    (_i_ctx, (Tstruct _SHA256state_st noattr)) ::
    (_o_ctx, (Tstruct _SHA256state_st noattr)) :: nil)
   noattr ::
 Composite _mbedtls_md_info_t Struct ((_dummy, tint) :: nil) noattr :: nil).

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
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
 (___i64_dtos,
   Gfun(External (EF_runtime "__i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___i64_dtou,
   Gfun(External (EF_runtime "__i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___i64_stod,
   Gfun(External (EF_runtime "__i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___i64_utod,
   Gfun(External (EF_runtime "__i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___i64_stof,
   Gfun(External (EF_runtime "__i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___i64_utof,
   Gfun(External (EF_runtime "__i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___i64_sdiv,
   Gfun(External (EF_runtime "__i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_udiv,
   Gfun(External (EF_runtime "__i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_smod,
   Gfun(External (EF_runtime "__i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umod,
   Gfun(External (EF_runtime "__i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_shl,
   Gfun(External (EF_runtime "__i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___i64_shr,
   Gfun(External (EF_runtime "__i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___i64_sar,
   Gfun(External (EF_runtime "__i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
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
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
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
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
     (tptr tvoid) cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
     cc_default)) ::
 (_SHA256_Init,
   Gfun(External (EF_external "SHA256_Init"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr (Tstruct _SHA256state_st noattr)) Tnil) tvoid cc_default)) ::
 (_SHA256_Update,
   Gfun(External (EF_external "SHA256_Update"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr (Tstruct _SHA256state_st noattr))
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid cc_default)) ::
 (_SHA256_Final,
   Gfun(External (EF_external "SHA256_Final"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
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
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tuchar) (Tcons tuint Tnil))
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
 (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
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
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fsqrt :: ___builtin_ctzll ::
 ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll :: ___builtin_clzl ::
 ___builtin_clz :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___i64_sar :: ___i64_shr :: ___i64_shl :: ___i64_umod ::
 ___i64_smod :: ___i64_udiv :: ___i64_sdiv :: ___i64_utof :: ___i64_stof ::
 ___i64_utod :: ___i64_stod :: ___i64_dtou :: ___i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fabs :: nil);
prog_main := _main;
prog_types := composites;
prog_comp_env := make_composite_env composites;
prog_comp_env_eq := refl_equal _
|}.

