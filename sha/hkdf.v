From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition _HKDF : ident := 201%positive.
Definition _HKDF_expand : ident := 197%positive.
Definition _HKDF_extract : ident := 188%positive.
Definition _HMAC : ident := 113%positive.
Definition _HMAC2 : ident := 115%positive.
Definition _HMAC_Final : ident := 109%positive.
Definition _HMAC_Init : ident := 106%positive.
Definition _HMAC_Update : ident := 107%positive.
Definition _HMAC_cleanup : ident := 110%positive.
Definition _K : ident := 159%positive.
Definition _K256 : ident := 60%positive.
Definition _Ki : ident := 77%positive.
Definition _Nh : ident := 3%positive.
Definition _Nl : ident := 2%positive.
Definition _SHA256 : ident := 94%positive.
Definition _SHA256_Final : ident := 93%positive.
Definition _SHA256_Init : ident := 80%positive.
Definition _SHA256_Update : ident := 89%positive.
Definition _SHA256_addlength : ident := 84%positive.
Definition _SHA256state_st : ident := 6%positive.
Definition _T1 : ident := 72%positive.
Definition _T2 : ident := 73%positive.
Definition _V : ident := 120%positive.
Definition _X : ident := 75%positive.
Definition ___builtin_annot : ident := 13%positive.
Definition ___builtin_annot_intval : ident := 14%positive.
Definition ___builtin_bswap : ident := 7%positive.
Definition ___builtin_bswap16 : ident := 9%positive.
Definition ___builtin_bswap32 : ident := 8%positive.
Definition ___builtin_bswap64 : ident := 39%positive.
Definition ___builtin_clz : ident := 40%positive.
Definition ___builtin_clzl : ident := 41%positive.
Definition ___builtin_clzll : ident := 42%positive.
Definition ___builtin_ctz : ident := 43%positive.
Definition ___builtin_ctzl : ident := 44%positive.
Definition ___builtin_ctzll : ident := 45%positive.
Definition ___builtin_debug : ident := 55%positive.
Definition ___builtin_fabs : ident := 10%positive.
Definition ___builtin_fmadd : ident := 48%positive.
Definition ___builtin_fmax : ident := 46%positive.
Definition ___builtin_fmin : ident := 47%positive.
Definition ___builtin_fmsub : ident := 49%positive.
Definition ___builtin_fnmadd : ident := 50%positive.
Definition ___builtin_fnmsub : ident := 51%positive.
Definition ___builtin_fsqrt : ident := 11%positive.
Definition ___builtin_membar : ident := 15%positive.
Definition ___builtin_memcpy_aligned : ident := 12%positive.
Definition ___builtin_nop : ident := 54%positive.
Definition ___builtin_read16_reversed : ident := 52%positive.
Definition ___builtin_read32_reversed : ident := 56%positive.
Definition ___builtin_va_arg : ident := 17%positive.
Definition ___builtin_va_copy : ident := 18%positive.
Definition ___builtin_va_end : ident := 19%positive.
Definition ___builtin_va_start : ident := 16%positive.
Definition ___builtin_write16_reversed : ident := 53%positive.
Definition ___builtin_write32_reversed : ident := 57%positive.
Definition ___compcert_i64_dtos : ident := 24%positive.
Definition ___compcert_i64_dtou : ident := 25%positive.
Definition ___compcert_i64_sar : ident := 36%positive.
Definition ___compcert_i64_sdiv : ident := 30%positive.
Definition ___compcert_i64_shl : ident := 34%positive.
Definition ___compcert_i64_shr : ident := 35%positive.
Definition ___compcert_i64_smod : ident := 32%positive.
Definition ___compcert_i64_smulh : ident := 37%positive.
Definition ___compcert_i64_stod : ident := 26%positive.
Definition ___compcert_i64_stof : ident := 28%positive.
Definition ___compcert_i64_udiv : ident := 31%positive.
Definition ___compcert_i64_umod : ident := 33%positive.
Definition ___compcert_i64_umulh : ident := 38%positive.
Definition ___compcert_i64_utod : ident := 27%positive.
Definition ___compcert_i64_utof : ident := 29%positive.
Definition ___compcert_va_composite : ident := 23%positive.
Definition ___compcert_va_float64 : ident := 22%positive.
Definition ___compcert_va_int32 : ident := 20%positive.
Definition ___compcert_va_int64 : ident := 21%positive.
Definition _a : ident := 63%positive.
Definition _add_len : ident := 155%positive.
Definition _additional : ident := 154%positive.
Definition _aux : ident := 104%positive.
Definition _b : ident := 64%positive.
Definition _buf : ident := 108%positive.
Definition _c : ident := 65%positive.
Definition _cNh : ident := 83%positive.
Definition _cNl : ident := 82%positive.
Definition _ctr : ident := 195%positive.
Definition _ctx : ident := 61%positive.
Definition _ctx_key : ident := 105%positive.
Definition _custom : ident := 167%positive.
Definition _d : ident := 66%positive.
Definition _data : ident := 4%positive.
Definition _data_ : ident := 85%positive.
Definition _data_len : ident := 162%positive.
Definition _digest_len : ident := 192%positive.
Definition _done : ident := 194%positive.
Definition _dummy : ident := 126%positive.
Definition _e : ident := 67%positive.
Definition _entropy_len : ident := 122%positive.
Definition _extr1 : ident := 198%positive.
Definition _extr2 : ident := 200%positive.
Definition _f : ident := 68%positive.
Definition _fragment : ident := 88%positive.
Definition _free : ident := 128%positive.
Definition _g : ident := 69%positive.
Definition _get_entropy : ident := 150%positive.
Definition _h : ident := 1%positive.
Definition _hmac : ident := 138%positive.
Definition _hmac_ctx : ident := 118%positive.
Definition _hmac_ctx_st : ident := 99%positive.
Definition _i : ident := 78%positive.
Definition _i_ctx : ident := 97%positive.
Definition _ilen : ident := 145%positive.
Definition _in : ident := 62%positive.
Definition _info : ident := 135%positive.
Definition _info_len : ident := 191%positive.
Definition _input : ident := 144%positive.
Definition _interval : ident := 173%positive.
Definition _j : ident := 101%positive.
Definition _key : ident := 100%positive.
Definition _key_len : ident := 112%positive.
Definition _keylen : ident := 141%positive.
Definition _l : ident := 76%positive.
Definition _left : ident := 177%positive.
Definition _len : ident := 81%positive.
Definition _ll : ident := 91%positive.
Definition _m : ident := 111%positive.
Definition _m__1 : ident := 114%positive.
Definition _main : ident := 95%positive.
Definition _malloc : ident := 127%positive.
Definition _mbedtls_hmac_drbg_context : ident := 125%positive.
Definition _mbedtls_hmac_drbg_free : ident := 182%positive.
Definition _mbedtls_hmac_drbg_init : ident := 153%positive.
Definition _mbedtls_hmac_drbg_random : ident := 181%positive.
Definition _mbedtls_hmac_drbg_random_with_add : ident := 180%positive.
Definition _mbedtls_hmac_drbg_reseed : ident := 166%positive.
Definition _mbedtls_hmac_drbg_seed : ident := 169%positive.
Definition _mbedtls_hmac_drbg_seed_buf : ident := 163%positive.
Definition _mbedtls_hmac_drbg_set_entropy_len : ident := 172%positive.
Definition _mbedtls_hmac_drbg_set_prediction_resistance : ident := 171%positive.
Definition _mbedtls_hmac_drbg_set_reseed_interval : ident := 174%positive.
Definition _mbedtls_hmac_drbg_update : ident := 161%positive.
Definition _mbedtls_md_context_t : ident := 119%positive.
Definition _mbedtls_md_free : ident := 149%positive.
Definition _mbedtls_md_get_size : ident := 134%positive.
Definition _mbedtls_md_hmac_finish : ident := 148%positive.
Definition _mbedtls_md_hmac_reset : ident := 143%positive.
Definition _mbedtls_md_hmac_starts : ident := 142%positive.
Definition _mbedtls_md_hmac_update : ident := 146%positive.
Definition _mbedtls_md_info_from_string : ident := 131%positive.
Definition _mbedtls_md_info_from_type : ident := 133%positive.
Definition _mbedtls_md_info_t : ident := 116%positive.
Definition _mbedtls_md_setup : ident := 140%positive.
Definition _mbedtls_zeroize : ident := 152%positive.
Definition _md : ident := 90%positive.
Definition _md_ctx : ident := 96%positive.
Definition _md_info : ident := 117%positive.
Definition _md_len : ident := 156%positive.
Definition _md_name : ident := 130%positive.
Definition _md_size : ident := 168%positive.
Definition _md_type : ident := 132%positive.
Definition _memcpy : ident := 58%positive.
Definition _memset : ident := 59%positive.
Definition _mocked_sha256_info : ident := 129%positive.
Definition _n : ident := 87%positive.
Definition _num : ident := 5%positive.
Definition _o_ctx : ident := 98%positive.
Definition _out : ident := 178%positive.
Definition _out_key : ident := 183%positive.
Definition _out_len : ident := 176%positive.
Definition _output : ident := 147%positive.
Definition _p : ident := 86%positive.
Definition _p_rng : ident := 175%positive.
Definition _pad : ident := 103%positive.
Definition _prediction_resistance : ident := 123%positive.
Definition _previous : ident := 193%positive.
Definition _prk : ident := 189%positive.
Definition _prk_len : ident := 190%positive.
Definition _prk_len_temp : ident := 199%positive.
Definition _reseed_counter : ident := 121%positive.
Definition _reseed_interval : ident := 124%positive.
Definition _reset : ident := 102%positive.
Definition _resistance : ident := 170%positive.
Definition _ret : ident := 136%positive.
Definition _rounds : ident := 157%positive.
Definition _s0 : ident := 70%positive.
Definition _s1 : ident := 71%positive.
Definition _salt : ident := 186%positive.
Definition _salt_len : ident := 187%positive.
Definition _secret : ident := 184%positive.
Definition _secret_len : ident := 185%positive.
Definition _seed : ident := 164%positive.
Definition _seedlen : ident := 165%positive.
Definition _sep : ident := 158%positive.
Definition _sep_value : ident := 160%positive.
Definition _sha256_block_data_order : ident := 79%positive.
Definition _sha_ctx : ident := 139%positive.
Definition _t : ident := 74%positive.
Definition _test_md_get_size : ident := 137%positive.
Definition _todo : ident := 196%positive.
Definition _use_len : ident := 179%positive.
Definition _v : ident := 151%positive.
Definition _xn : ident := 92%positive.
Definition _t'1 : ident := 202%positive.
Definition _t'2 : ident := 203%positive.
Definition _t'3 : ident := 204%positive.

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
((___builtin_bswap,
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
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
     (tptr tvoid) cc_default)) ::
 (_HMAC_Init,
   Gfun(External (EF_external "HMAC_Init"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
       (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid cc_default)) ::
 (_HMAC_Update,
   Gfun(External (EF_external "HMAC_Update"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid cc_default)) ::
 (_HMAC_Final,
   Gfun(External (EF_external "HMAC_Final"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr (Tstruct _hmac_ctx_st noattr)) (Tcons (tptr tuchar) Tnil))
     tvoid cc_default)) ::
 (_HMAC_cleanup,
   Gfun(External (EF_external "HMAC_cleanup"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr (Tstruct _hmac_ctx_st noattr)) Tnil) tvoid cc_default)) ::
 (_HMAC,
   Gfun(External (EF_external "HMAC"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: nil) (Some AST.Tint) cc_default))
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
 ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


