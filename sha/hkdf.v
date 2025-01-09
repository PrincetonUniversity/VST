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
  Definition source_file := "sha/hkdf.c".
  Definition normalized := false.
End Info.

Definition _HKDF : ident := 206%positive.
Definition _HKDF_expand : ident := 202%positive.
Definition _HKDF_extract : ident := 193%positive.
Definition _HMAC : ident := 118%positive.
Definition _HMAC2 : ident := 120%positive.
Definition _HMAC_Final : ident := 114%positive.
Definition _HMAC_Init : ident := 111%positive.
Definition _HMAC_Update : ident := 112%positive.
Definition _HMAC_cleanup : ident := 115%positive.
Definition _K : ident := 164%positive.
Definition _K256 : ident := 46%positive.
Definition _Ki : ident := 63%positive.
Definition _Nh : ident := 4%positive.
Definition _Nl : ident := 3%positive.
Definition _SHA256 : ident := 80%positive.
Definition _SHA256_Final : ident := 79%positive.
Definition _SHA256_Init : ident := 66%positive.
Definition _SHA256_Update : ident := 75%positive.
Definition _SHA256_addlength : ident := 70%positive.
Definition _SHA256state_st : ident := 1%positive.
Definition _T1 : ident := 58%positive.
Definition _T2 : ident := 59%positive.
Definition _V : ident := 126%positive.
Definition _X : ident := 61%positive.
Definition ___builtin_ais_annot : ident := 7%positive.
Definition ___builtin_annot : ident := 24%positive.
Definition ___builtin_annot_intval : ident := 25%positive.
Definition ___builtin_bswap : ident := 9%positive.
Definition ___builtin_bswap16 : ident := 11%positive.
Definition ___builtin_bswap32 : ident := 10%positive.
Definition ___builtin_bswap64 : ident := 8%positive.
Definition ___builtin_clz : ident := 12%positive.
Definition ___builtin_clzl : ident := 13%positive.
Definition ___builtin_clzll : ident := 14%positive.
Definition ___builtin_ctz : ident := 15%positive.
Definition ___builtin_ctzl : ident := 16%positive.
Definition ___builtin_ctzll : ident := 17%positive.
Definition ___builtin_debug : ident := 41%positive.
Definition ___builtin_expect : ident := 32%positive.
Definition ___builtin_fabs : ident := 18%positive.
Definition ___builtin_fabsf : ident := 19%positive.
Definition ___builtin_fmadd : ident := 35%positive.
Definition ___builtin_fmax : ident := 33%positive.
Definition ___builtin_fmin : ident := 34%positive.
Definition ___builtin_fmsub : ident := 36%positive.
Definition ___builtin_fnmadd : ident := 37%positive.
Definition ___builtin_fnmsub : ident := 38%positive.
Definition ___builtin_fsqrt : ident := 20%positive.
Definition ___builtin_membar : ident := 26%positive.
Definition ___builtin_memcpy_aligned : ident := 22%positive.
Definition ___builtin_read16_reversed : ident := 39%positive.
Definition ___builtin_read32_reversed : ident := 42%positive.
Definition ___builtin_sel : ident := 23%positive.
Definition ___builtin_sqrt : ident := 21%positive.
Definition ___builtin_unreachable : ident := 31%positive.
Definition ___builtin_va_arg : ident := 28%positive.
Definition ___builtin_va_copy : ident := 29%positive.
Definition ___builtin_va_end : ident := 30%positive.
Definition ___builtin_va_start : ident := 27%positive.
Definition ___builtin_write16_reversed : ident := 40%positive.
Definition ___builtin_write32_reversed : ident := 43%positive.
Definition ___compcert_i64_dtos : ident := 85%positive.
Definition ___compcert_i64_dtou : ident := 86%positive.
Definition ___compcert_i64_sar : ident := 97%positive.
Definition ___compcert_i64_sdiv : ident := 91%positive.
Definition ___compcert_i64_shl : ident := 95%positive.
Definition ___compcert_i64_shr : ident := 96%positive.
Definition ___compcert_i64_smod : ident := 93%positive.
Definition ___compcert_i64_smulh : ident := 98%positive.
Definition ___compcert_i64_stod : ident := 87%positive.
Definition ___compcert_i64_stof : ident := 89%positive.
Definition ___compcert_i64_udiv : ident := 92%positive.
Definition ___compcert_i64_umod : ident := 94%positive.
Definition ___compcert_i64_umulh : ident := 99%positive.
Definition ___compcert_i64_utod : ident := 88%positive.
Definition ___compcert_i64_utof : ident := 90%positive.
Definition ___compcert_va_composite : ident := 84%positive.
Definition ___compcert_va_float64 : ident := 83%positive.
Definition ___compcert_va_int32 : ident := 81%positive.
Definition ___compcert_va_int64 : ident := 82%positive.
Definition _a : ident := 49%positive.
Definition _add_len : ident := 160%positive.
Definition _additional : ident := 159%positive.
Definition _aux : ident := 109%positive.
Definition _b : ident := 50%positive.
Definition _buf : ident := 113%positive.
Definition _c : ident := 51%positive.
Definition _cNh : ident := 69%positive.
Definition _cNl : ident := 68%positive.
Definition _ctr : ident := 200%positive.
Definition _ctx : ident := 47%positive.
Definition _ctx_key : ident := 110%positive.
Definition _custom : ident := 172%positive.
Definition _d : ident := 52%positive.
Definition _data : ident := 5%positive.
Definition _data_ : ident := 71%positive.
Definition _data_len : ident := 167%positive.
Definition _digest_len : ident := 197%positive.
Definition _done : ident := 199%positive.
Definition _dummy : ident := 131%positive.
Definition _e : ident := 53%positive.
Definition _entropy_len : ident := 128%positive.
Definition _extr1 : ident := 203%positive.
Definition _extr2 : ident := 205%positive.
Definition _f : ident := 54%positive.
Definition _fragment : ident := 74%positive.
Definition _free : ident := 133%positive.
Definition _g : ident := 55%positive.
Definition _get_entropy : ident := 155%positive.
Definition _h : ident := 2%positive.
Definition _hmac : ident := 143%positive.
Definition _hmac_ctx : ident := 124%positive.
Definition _hmac_ctx_st : ident := 101%positive.
Definition _i : ident := 64%positive.
Definition _i_ctx : ident := 103%positive.
Definition _ilen : ident := 150%positive.
Definition _in : ident := 48%positive.
Definition _info : ident := 140%positive.
Definition _info_len : ident := 196%positive.
Definition _input : ident := 149%positive.
Definition _interval : ident := 178%positive.
Definition _j : ident := 106%positive.
Definition _key : ident := 105%positive.
Definition _key_len : ident := 117%positive.
Definition _keylen : ident := 146%positive.
Definition _l : ident := 62%positive.
Definition _left : ident := 182%positive.
Definition _len : ident := 67%positive.
Definition _ll : ident := 77%positive.
Definition _m : ident := 116%positive.
Definition _m__1 : ident := 119%positive.
Definition _main : ident := 100%positive.
Definition _malloc : ident := 132%positive.
Definition _mbedtls_hmac_drbg_context : ident := 125%positive.
Definition _mbedtls_hmac_drbg_free : ident := 187%positive.
Definition _mbedtls_hmac_drbg_init : ident := 158%positive.
Definition _mbedtls_hmac_drbg_random : ident := 186%positive.
Definition _mbedtls_hmac_drbg_random_with_add : ident := 185%positive.
Definition _mbedtls_hmac_drbg_reseed : ident := 171%positive.
Definition _mbedtls_hmac_drbg_seed : ident := 174%positive.
Definition _mbedtls_hmac_drbg_seed_buf : ident := 168%positive.
Definition _mbedtls_hmac_drbg_set_entropy_len : ident := 177%positive.
Definition _mbedtls_hmac_drbg_set_prediction_resistance : ident := 176%positive.
Definition _mbedtls_hmac_drbg_set_reseed_interval : ident := 179%positive.
Definition _mbedtls_hmac_drbg_update : ident := 166%positive.
Definition _mbedtls_md_context_t : ident := 121%positive.
Definition _mbedtls_md_free : ident := 154%positive.
Definition _mbedtls_md_get_size : ident := 139%positive.
Definition _mbedtls_md_hmac_finish : ident := 153%positive.
Definition _mbedtls_md_hmac_reset : ident := 148%positive.
Definition _mbedtls_md_hmac_starts : ident := 147%positive.
Definition _mbedtls_md_hmac_update : ident := 151%positive.
Definition _mbedtls_md_info_from_string : ident := 136%positive.
Definition _mbedtls_md_info_from_type : ident := 138%positive.
Definition _mbedtls_md_info_t : ident := 123%positive.
Definition _mbedtls_md_setup : ident := 145%positive.
Definition _mbedtls_zeroize : ident := 157%positive.
Definition _md : ident := 76%positive.
Definition _md_ctx : ident := 102%positive.
Definition _md_info : ident := 122%positive.
Definition _md_len : ident := 161%positive.
Definition _md_name : ident := 135%positive.
Definition _md_size : ident := 173%positive.
Definition _md_type : ident := 137%positive.
Definition _memcpy : ident := 44%positive.
Definition _memset : ident := 45%positive.
Definition _mocked_sha256_info : ident := 134%positive.
Definition _n : ident := 73%positive.
Definition _num : ident := 6%positive.
Definition _o_ctx : ident := 104%positive.
Definition _out : ident := 183%positive.
Definition _out_key : ident := 188%positive.
Definition _out_len : ident := 181%positive.
Definition _output : ident := 152%positive.
Definition _p : ident := 72%positive.
Definition _p_rng : ident := 180%positive.
Definition _pad : ident := 108%positive.
Definition _prediction_resistance : ident := 129%positive.
Definition _previous : ident := 198%positive.
Definition _prk : ident := 194%positive.
Definition _prk_len : ident := 195%positive.
Definition _prk_len_temp : ident := 204%positive.
Definition _reseed_counter : ident := 127%positive.
Definition _reseed_interval : ident := 130%positive.
Definition _reset : ident := 107%positive.
Definition _resistance : ident := 175%positive.
Definition _ret : ident := 141%positive.
Definition _rounds : ident := 162%positive.
Definition _s0 : ident := 56%positive.
Definition _s1 : ident := 57%positive.
Definition _salt : ident := 191%positive.
Definition _salt_len : ident := 192%positive.
Definition _secret : ident := 189%positive.
Definition _secret_len : ident := 190%positive.
Definition _seed : ident := 169%positive.
Definition _seedlen : ident := 170%positive.
Definition _sep : ident := 163%positive.
Definition _sep_value : ident := 165%positive.
Definition _sha256_block_data_order : ident := 65%positive.
Definition _sha_ctx : ident := 144%positive.
Definition _t : ident := 60%positive.
Definition _test_md_get_size : ident := 142%positive.
Definition _todo : ident := 201%positive.
Definition _use_len : ident := 184%positive.
Definition _v : ident := 156%positive.
Definition _xn : ident := 78%positive.
Definition _t'1 : ident := 207%positive.
Definition _t'2 : ident := 208%positive.
Definition _t'3 : ident := 209%positive.

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
                    ((tptr tuchar) :: tint :: (tptr tuchar) :: tint ::
                     (tptr tuchar) :: nil) (tptr tuchar) cc_default))
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
                                 ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                                  (tptr tuchar) :: tint :: nil) tvoid
                                 cc_default))
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
                                                 ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                                                  (tptr tuchar) :: tint ::
                                                  nil) tvoid cc_default))
                              ((Eaddrof
                                 (Evar _hmac (Tstruct _hmac_ctx_st noattr))
                                 (tptr (Tstruct _hmac_ctx_st noattr))) ::
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) ::
                               (Econst_int (Int.repr 0) tint) :: nil))
                            (Scall None
                              (Evar _HMAC_Update (Tfunction
                                                   ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                                                    (tptr tvoid) :: tuint ::
                                                    nil) tvoid cc_default))
                              ((Eaddrof
                                 (Evar _hmac (Tstruct _hmac_ctx_st noattr))
                                 (tptr (Tstruct _hmac_ctx_st noattr))) ::
                               (Evar _previous (tarray tuchar 64)) ::
                               (Etempvar _digest_len tuint) :: nil)))
                          Sskip)
                        (Ssequence
                          (Scall None
                            (Evar _HMAC_Update (Tfunction
                                                 ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                                                  (tptr tvoid) :: tuint ::
                                                  nil) tvoid cc_default))
                            ((Eaddrof
                               (Evar _hmac (Tstruct _hmac_ctx_st noattr))
                               (tptr (Tstruct _hmac_ctx_st noattr))) ::
                             (Etempvar _info (tptr tuchar)) ::
                             (Etempvar _info_len tuint) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _HMAC_Update (Tfunction
                                                   ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                                                    (tptr tvoid) :: tuint ::
                                                    nil) tvoid cc_default))
                              ((Eaddrof
                                 (Evar _hmac (Tstruct _hmac_ctx_st noattr))
                                 (tptr (Tstruct _hmac_ctx_st noattr))) ::
                               (Eaddrof (Evar _ctr tuchar) (tptr tuchar)) ::
                               (Econst_int (Int.repr 1) tint) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _HMAC_Final (Tfunction
                                                    ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                                                     (tptr tuchar) :: nil)
                                                    tvoid cc_default))
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
                                                      ((tptr tvoid) ::
                                                       (tptr tvoid) ::
                                                       tuint :: nil)
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
                                          ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                                           nil) tvoid cc_default))
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
                            ((tptr tuchar) :: (tptr tuint) ::
                             (tptr tuchar) :: tuint :: (tptr tuchar) ::
                             tuint :: nil) tint cc_default))
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
                               ((tptr tuchar) :: tuint :: (tptr tuchar) ::
                                tuint :: (tptr tuchar) :: tuint :: nil) tint
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
   (Member_plain _h (tarray tuint 8) :: Member_plain _Nl tuint ::
    Member_plain _Nh tuint :: Member_plain _data (tarray tuchar 64) ::
    Member_plain _num tuint :: nil)
   noattr ::
 Composite _hmac_ctx_st Struct
   (Member_plain _md_ctx (Tstruct _SHA256state_st noattr) ::
    Member_plain _i_ctx (Tstruct _SHA256state_st noattr) ::
    Member_plain _o_ctx (Tstruct _SHA256state_st noattr) :: nil)
   noattr :: nil).

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
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tuint :: nil) (tptr tvoid) cc_default)) ::
 (_HMAC_Init,
   Gfun(External (EF_external "HMAC_Init"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xvoid cc_default))
     ((tptr (Tstruct _hmac_ctx_st noattr)) :: (tptr tuchar) :: tint :: nil)
     tvoid cc_default)) ::
 (_HMAC_Update,
   Gfun(External (EF_external "HMAC_Update"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xvoid cc_default))
     ((tptr (Tstruct _hmac_ctx_st noattr)) :: (tptr tvoid) :: tuint :: nil)
     tvoid cc_default)) ::
 (_HMAC_Final,
   Gfun(External (EF_external "HMAC_Final"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _hmac_ctx_st noattr)) :: (tptr tuchar) :: nil) tvoid
     cc_default)) ::
 (_HMAC_cleanup,
   Gfun(External (EF_external "HMAC_cleanup"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _hmac_ctx_st noattr)) :: nil) tvoid cc_default)) ::
 (_HMAC,
   Gfun(External (EF_external "HMAC"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xptr :: AST.Xint ::
                      AST.Xptr :: nil) AST.Xptr cc_default))
     ((tptr tuchar) :: tint :: (tptr tuchar) :: tint :: (tptr tuchar) :: nil)
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


