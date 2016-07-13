Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _FSb : ident := 54%positive.
Definition _FT0 : ident := 55%positive.
Definition _FT1 : ident := 56%positive.
Definition _FT2 : ident := 57%positive.
Definition _FT3 : ident := 58%positive.
Definition _HMAC : ident := 233%positive.
Definition _HMAC2 : ident := 235%positive.
Definition _HMAC_Final : ident := 180%positive.
Definition _HMAC_Init : ident := 178%positive.
Definition _HMAC_Update : ident := 179%positive.
Definition _HMAC_cleanup : ident := 228%positive.
Definition _K : ident := 204%positive.
Definition _Nh : ident := 169%positive.
Definition _Nl : ident := 168%positive.
Definition _RCON : ident := 64%positive.
Definition _RK : ident := 78%positive.
Definition _RSb : ident := 59%positive.
Definition _RT0 : ident := 60%positive.
Definition _RT1 : ident := 61%positive.
Definition _RT2 : ident := 62%positive.
Definition _RT3 : ident := 63%positive.
Definition _SHA256_Final : ident := 222%positive.
Definition _SHA256_Init : ident := 220%positive.
Definition _SHA256_Update : ident := 221%positive.
Definition _SHA256state_st : ident := 171%positive.
Definition _SK : ident := 83%positive.
Definition _V : ident := 165%positive.
Definition _X0 : ident := 88%positive.
Definition _X1 : ident := 89%positive.
Definition _X2 : ident := 90%positive.
Definition _X3 : ident := 91%positive.
Definition _Y0 : ident := 92%positive.
Definition _Y1 : ident := 93%positive.
Definition _Y2 : ident := 94%positive.
Definition _Y3 : ident := 95%positive.
Definition __2009 : ident := 272%positive.
Definition __225 : ident := 4%positive.
Definition __364 : ident := 101%positive.
Definition __393 : ident := 110%positive.
Definition ___builtin_annot : ident := 7%positive.
Definition ___builtin_annot_intval : ident := 8%positive.
Definition ___builtin_bswap : ident := 31%positive.
Definition ___builtin_bswap16 : ident := 33%positive.
Definition ___builtin_bswap32 : ident := 32%positive.
Definition ___builtin_clz : ident := 34%positive.
Definition ___builtin_ctz : ident := 35%positive.
Definition ___builtin_debug : ident := 48%positive.
Definition ___builtin_fabs : ident := 5%positive.
Definition ___builtin_fmadd : ident := 39%positive.
Definition ___builtin_fmax : ident := 37%positive.
Definition ___builtin_fmin : ident := 38%positive.
Definition ___builtin_fmsub : ident := 40%positive.
Definition ___builtin_fnmadd : ident := 41%positive.
Definition ___builtin_fnmsub : ident := 42%positive.
Definition ___builtin_fsqrt : ident := 36%positive.
Definition ___builtin_membar : ident := 9%positive.
Definition ___builtin_memcpy_aligned : ident := 6%positive.
Definition ___builtin_nop : ident := 47%positive.
Definition ___builtin_read16_reversed : ident := 43%positive.
Definition ___builtin_read32_reversed : ident := 44%positive.
Definition ___builtin_va_arg : ident := 11%positive.
Definition ___builtin_va_copy : ident := 12%positive.
Definition ___builtin_va_end : ident := 13%positive.
Definition ___builtin_va_start : ident := 10%positive.
Definition ___builtin_write16_reversed : ident := 45%positive.
Definition ___builtin_write32_reversed : ident := 46%positive.
Definition ___compcert_va_composite : ident := 17%positive.
Definition ___compcert_va_float64 : ident := 16%positive.
Definition ___compcert_va_int32 : ident := 14%positive.
Definition ___compcert_va_int64 : ident := 15%positive.
Definition ___i64_dtos : ident := 18%positive.
Definition ___i64_dtou : ident := 19%positive.
Definition ___i64_sar : ident := 30%positive.
Definition ___i64_sdiv : ident := 24%positive.
Definition ___i64_shl : ident := 28%positive.
Definition ___i64_shr : ident := 29%positive.
Definition ___i64_smod : ident := 26%positive.
Definition ___i64_stod : ident := 20%positive.
Definition ___i64_stof : ident := 22%positive.
Definition ___i64_udiv : ident := 25%positive.
Definition ___i64_umod : ident := 27%positive.
Definition ___i64_utod : ident := 21%positive.
Definition ___i64_utof : ident := 23%positive.
Definition ___stringlit_1 : ident := 154%positive.
Definition ___stringlit_2 : ident := 155%positive.
Definition ___stringlit_3 : ident := 156%positive.
Definition ___stringlit_4 : ident := 157%positive.
Definition ___stringlit_5 : ident := 158%positive.
Definition _add_input : ident := 137%positive.
Definition _add_len : ident := 136%positive.
Definition _additional : ident := 135%positive.
Definition _aes_ctx : ident := 107%positive.
Definition _aes_gen_tables : ident := 72%positive.
Definition _aes_init_done : ident := 65%positive.
Definition _aux : ident := 225%positive.
Definition _block_cipher_df : ident := 133%positive.
Definition _block_size : ident := 239%positive.
Definition _buf : ident := 3%positive.
Definition _buf_len : ident := 131%positive.
Definition _buffer : ident := 271%positive.
Definition _c : ident := 232%positive.
Definition _calloc : ident := 249%positive.
Definition _chain : ident := 129%positive.
Definition _clone_func : ident := 246%positive.
Definition _counter : ident := 102%positive.
Definition _ctr_drbg_self_test_entropy : ident := 152%positive.
Definition _ctr_drbg_update_internal : ident := 134%positive.
Definition _ctx : ident := 73%positive.
Definition _ctx_alloc_func : ident := 244%positive.
Definition _ctx_free_func : ident := 245%positive.
Definition _ctx_key : ident := 226%positive.
Definition _cty : ident := 82%positive.
Definition _custom : ident := 115%positive.
Definition _d : ident := 231%positive.
Definition _data : ident := 126%positive.
Definition _data_len : ident := 127%positive.
Definition _digest_func : ident := 243%positive.
Definition _dst : ident := 254%positive.
Definition _dummy : ident := 175%positive.
Definition _entropy_len : ident := 105%positive.
Definition _entropy_source_nopr : ident := 146%positive.
Definition _entropy_source_pr : ident := 145%positive.
Definition _exit : ident := 84%positive.
Definition _f_entropy : ident := 108%positive.
Definition _finish_func : ident := 242%positive.
Definition _free : ident := 177%positive.
Definition _get_entropy : ident := 199%positive.
Definition _h : ident := 167%positive.
Definition _hmac : ident := 189%positive.
Definition _hmac_ctx : ident := 163%positive.
Definition _hmac_ctx_st : ident := 174%positive.
Definition _i : ident := 66%positive.
Definition _i_ctx : ident := 172%positive.
Definition _ilen : ident := 195%positive.
Definition _info : ident := 187%positive.
Definition _input : ident := 86%positive.
Definition _interval : ident := 124%positive.
Definition _ipad : ident := 263%positive.
Definition _iv : ident := 130%positive.
Definition _j : ident := 80%positive.
Definition _key : ident := 76%positive.
Definition _key_len : ident := 230%positive.
Definition _keybits : ident := 77%positive.
Definition _keylen : ident := 192%positive.
Definition _left : ident := 215%positive.
Definition _len : ident := 116%positive.
Definition _log : ident := 71%positive.
Definition _m : ident := 229%positive.
Definition _m__1 : ident := 234%positive.
Definition _main : ident := 100%positive.
Definition _malloc : ident := 176%positive.
Definition _mbedtls_aes_crypt_ecb : ident := 99%positive.
Definition _mbedtls_aes_decrypt : ident := 97%positive.
Definition _mbedtls_aes_encrypt : ident := 96%positive.
Definition _mbedtls_aes_free : ident := 75%positive.
Definition _mbedtls_aes_init : ident := 74%positive.
Definition _mbedtls_aes_setkey_dec : ident := 85%positive.
Definition _mbedtls_aes_setkey_enc : ident := 79%positive.
Definition _mbedtls_ctr_drbg_free : ident := 120%positive.
Definition _mbedtls_ctr_drbg_init : ident := 114%positive.
Definition _mbedtls_ctr_drbg_random : ident := 144%positive.
Definition _mbedtls_ctr_drbg_random_with_add : ident := 143%positive.
Definition _mbedtls_ctr_drbg_reseed : ident := 117%positive.
Definition _mbedtls_ctr_drbg_seed : ident := 119%positive.
Definition _mbedtls_ctr_drbg_seed_entropy_len : ident := 118%positive.
Definition _mbedtls_ctr_drbg_self_test : ident := 159%positive.
Definition _mbedtls_ctr_drbg_set_entropy_len : ident := 123%positive.
Definition _mbedtls_ctr_drbg_set_prediction_resistance : ident := 122%positive.
Definition _mbedtls_ctr_drbg_set_reseed_interval : ident := 125%positive.
Definition _mbedtls_ctr_drbg_update : ident := 138%positive.
Definition _mbedtls_hmac_drbg_context : ident := 166%positive.
Definition _mbedtls_hmac_drbg_free : ident := 219%positive.
Definition _mbedtls_hmac_drbg_init : ident := 200%positive.
Definition _mbedtls_hmac_drbg_random : ident := 218%positive.
Definition _mbedtls_hmac_drbg_random_with_add : ident := 217%positive.
Definition _mbedtls_hmac_drbg_reseed : ident := 208%positive.
Definition _mbedtls_hmac_drbg_seed : ident := 210%positive.
Definition _mbedtls_hmac_drbg_seed_buf : ident := 207%positive.
Definition _mbedtls_hmac_drbg_set_entropy_len : ident := 212%positive.
Definition _mbedtls_hmac_drbg_set_prediction_resistance : ident := 211%positive.
Definition _mbedtls_hmac_drbg_set_reseed_interval : ident := 213%positive.
Definition _mbedtls_hmac_drbg_update : ident := 206%positive.
Definition _mbedtls_md : ident := 261%positive.
Definition _mbedtls_md_clone : ident := 256%positive.
Definition _mbedtls_md_context_t : ident := 164%positive.
Definition _mbedtls_md_finish : ident := 260%positive.
Definition _mbedtls_md_free : ident := 198%positive.
Definition _mbedtls_md_get_name : ident := 268%positive.
Definition _mbedtls_md_get_size : ident := 186%positive.
Definition _mbedtls_md_get_type : ident := 267%positive.
Definition _mbedtls_md_hmac : ident := 265%positive.
Definition _mbedtls_md_hmac_finish : ident := 197%positive.
Definition _mbedtls_md_hmac_reset : ident := 194%positive.
Definition _mbedtls_md_hmac_starts : ident := 193%positive.
Definition _mbedtls_md_hmac_update : ident := 196%positive.
Definition _mbedtls_md_info_from_string : ident := 183%positive.
Definition _mbedtls_md_info_from_type : ident := 185%positive.
Definition _mbedtls_md_info_t : ident := 160%positive.
Definition _mbedtls_md_init : ident := 253%positive.
Definition _mbedtls_md_init_ctx : ident := 257%positive.
Definition _mbedtls_md_list : ident := 252%positive.
Definition _mbedtls_md_process : ident := 266%positive.
Definition _mbedtls_md_setup : ident := 191%positive.
Definition _mbedtls_md_starts : ident := 258%positive.
Definition _mbedtls_md_update : ident := 259%positive.
Definition _mbedtls_sha1 : ident := 280%positive.
Definition _mbedtls_sha1_clone : ident := 275%positive.
Definition _mbedtls_sha1_finish : ident := 278%positive.
Definition _mbedtls_sha1_free : ident := 274%positive.
Definition _mbedtls_sha1_info : ident := 248%positive.
Definition _mbedtls_sha1_init : ident := 273%positive.
Definition _mbedtls_sha1_process : ident := 279%positive.
Definition _mbedtls_sha1_starts : ident := 276%positive.
Definition _mbedtls_sha1_update : ident := 277%positive.
Definition _mbedtls_zeroize : ident := 53%positive.
Definition _md : ident := 227%positive.
Definition _md_ctx : ident := 162%positive.
Definition _md_info : ident := 161%positive.
Definition _md_len : ident := 201%positive.
Definition _md_name : ident := 182%positive.
Definition _md_size : ident := 209%positive.
Definition _md_type : ident := 184%positive.
Definition _memcmp : ident := 112%positive.
Definition _memcpy : ident := 111%positive.
Definition _memset : ident := 49%positive.
Definition _mocked_sha256_info : ident := 181%positive.
Definition _mode : ident := 98%positive.
Definition _n : ident := 51%positive.
Definition _name : ident := 237%positive.
Definition _nonce_pers_nopr : ident := 148%positive.
Definition _nonce_pers_pr : ident := 147%positive.
Definition _nr : ident := 1%positive.
Definition _num : ident := 170%positive.
Definition _o_ctx : ident := 173%positive.
Definition _opad : ident := 264%positive.
Definition _out : ident := 216%positive.
Definition _out_len : ident := 214%positive.
Definition _output : ident := 87%positive.
Definition _output_len : ident := 142%positive.
Definition _p : ident := 52%positive.
Definition _p_entropy : ident := 109%positive.
Definition _p_rng : ident := 141%positive.
Definition _pad : ident := 224%positive.
Definition _pow : ident := 70%positive.
Definition _prediction_resistance : ident := 104%positive.
Definition _printf : ident := 113%positive.
Definition _process_func : ident := 247%positive.
Definition _reseed_counter : ident := 103%positive.
Definition _reseed_interval : ident := 106%positive.
Definition _reset : ident := 223%positive.
Definition _resistance : ident := 121%positive.
Definition _result_nopr : ident := 150%positive.
Definition _result_pr : ident := 149%positive.
Definition _ret : ident := 81%positive.
Definition _rk : ident := 2%positive.
Definition _rounds : ident := 202%positive.
Definition _seed : ident := 139%positive.
Definition _seedlen : ident := 140%positive.
Definition _sep : ident := 203%positive.
Definition _sep_value : ident := 205%positive.
Definition _sha1_clone_wrap : ident := 285%positive.
Definition _sha1_ctx_alloc : ident := 284%positive.
Definition _sha1_ctx_free : ident := 286%positive.
Definition _sha1_finish_wrap : ident := 283%positive.
Definition _sha1_process_wrap : ident := 287%positive.
Definition _sha1_starts_wrap : ident := 281%positive.
Definition _sha1_update_wrap : ident := 282%positive.
Definition _sha_ctx : ident := 190%positive.
Definition _size : ident := 238%positive.
Definition _src : ident := 255%positive.
Definition _starts_func : ident := 240%positive.
Definition _state : ident := 270%positive.
Definition _strcmp : ident := 250%positive.
Definition _sum : ident := 262%positive.
Definition _supported_digests : ident := 251%positive.
Definition _test_md_get_size : ident := 188%positive.
Definition _test_offset : ident := 151%positive.
Definition _tmp : ident := 128%positive.
Definition _total : ident := 269%positive.
Definition _type : ident := 236%positive.
Definition _update_func : ident := 241%positive.
Definition _use_len : ident := 132%positive.
Definition _v : ident := 50%positive.
Definition _verbose : ident := 153%positive.
Definition _x : ident := 67%positive.
Definition _y : ident := 68%positive.
Definition _z : ident := 69%positive.

Definition v_mocked_sha256_info := {|
  gvar_info := (Tstruct _mbedtls_md_info_t noattr);
  gvar_init := (Init_space 0 :: nil);
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

Definition f_mbedtls_md_setup := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                (_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
                (_hmac, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_sha_ctx, (tptr (Tstruct _hmac_ctx_st noattr))) ::
               (288%positive, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some 288%positive)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _hmac_ctx_st noattr) tuint) :: nil))
    (Sset _sha_ctx
      (Ecast (Etempvar 288%positive (tptr tvoid))
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
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_mbedtls_md_hmac_starts := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                (_key, (tptr tuchar)) :: (_keylen, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _HMAC_Init (Tfunction
                       (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                         (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                       cc_default))
    ((Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
         (Tstruct _mbedtls_md_context_t noattr)) _hmac_ctx (tptr tvoid)) ::
     (Ecast (Etempvar _key (tptr tuchar)) (tptr tuchar)) ::
     (Etempvar _keylen tuint) :: nil))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_mbedtls_md_hmac_reset := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_md_context_t noattr))) :: nil);
  fn_vars := ((_buf, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _HMAC_Final (Tfunction
                        (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
         (Tstruct _mbedtls_md_context_t noattr)) _hmac_ctx (tptr tvoid)) ::
     (Evar _buf (tarray tuchar 32)) :: nil))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_mbedtls_md_hmac_update := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                (_input, (tptr tuchar)) :: (_ilen, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _HMAC_Update (Tfunction
                         (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                           (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                         cc_default))
    ((Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
         (Tstruct _mbedtls_md_context_t noattr)) _hmac_ctx (tptr tvoid)) ::
     (Etempvar _input (tptr tuchar)) :: (Etempvar _ilen tuint) :: nil))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_mbedtls_md_hmac_finish := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_md_context_t noattr))) ::
                (_output, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _HMAC_Final (Tfunction
                        (Tcons (tptr (Tstruct _hmac_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
         (Tstruct _mbedtls_md_context_t noattr)) _hmac_ctx (tptr tvoid)) ::
     (Etempvar _output (tptr tuchar)) :: nil))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_mbedtls_md_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _mbedtls_md_context_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _HMAC_cleanup (Tfunction
                          (Tcons (tptr (Tstruct _hmac_ctx_st noattr)) Tnil)
                          tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
         (Tstruct _mbedtls_md_context_t noattr)) _hmac_ctx (tptr tvoid)) ::
     nil))
  (Scall None
    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _ctx (tptr (Tstruct _mbedtls_md_context_t noattr)))
         (Tstruct _mbedtls_md_context_t noattr)) _hmac_ctx (tptr tvoid)) ::
     nil)))
|}.

Definition composites : list composite_definition :=
(Composite _mbedtls_md_context_t Struct
   ((_md_info, (tptr (Tstruct _mbedtls_md_info_t noattr))) ::
    (_md_ctx, (tptr tvoid)) :: (_hmac_ctx, (tptr tvoid)) :: nil)
   noattr ::
 Composite _SHA256state_st Struct
   ((_h, (tarray tuint 8)) :: (_Nl, tuint) :: (_Nh, tuint) ::
    (_data, (tarray tuchar 64)) :: (_num, tuint) :: nil)
   noattr ::
 Composite _hmac_ctx_st Struct
   ((_md_ctx, (Tstruct _SHA256state_st noattr)) ::
    (_i_ctx, (Tstruct _SHA256state_st noattr)) ::
    (_o_ctx, (Tstruct _SHA256state_st noattr)) :: nil)
   noattr :: Composite _mbedtls_md_info_t Struct nil noattr :: nil).

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
   Gfun(External (EF_external "__i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___i64_dtou,
   Gfun(External (EF_external "__i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___i64_stod,
   Gfun(External (EF_external "__i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___i64_utod,
   Gfun(External (EF_external "__i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___i64_stof,
   Gfun(External (EF_external "__i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___i64_utof,
   Gfun(External (EF_external "__i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___i64_sdiv,
   Gfun(External (EF_external "__i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_udiv,
   Gfun(External (EF_external "__i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_smod,
   Gfun(External (EF_external "__i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umod,
   Gfun(External (EF_external "__i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_shl,
   Gfun(External (EF_external "__i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___i64_shr,
   Gfun(External (EF_external "__i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___i64_sar,
   Gfun(External (EF_external "__i64_sar"
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
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
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
 (_mocked_sha256_info, Gvar v_mocked_sha256_info) ::
 (_mbedtls_md_info_from_string, Gfun(Internal f_mbedtls_md_info_from_string)) ::
 (_mbedtls_md_info_from_type, Gfun(Internal f_mbedtls_md_info_from_type)) ::
 (_mbedtls_md_get_size, Gfun(Internal f_mbedtls_md_get_size)) ::
 (_mbedtls_md_setup, Gfun(Internal f_mbedtls_md_setup)) ::
 (_mbedtls_md_hmac_starts, Gfun(Internal f_mbedtls_md_hmac_starts)) ::
 (_mbedtls_md_hmac_reset, Gfun(Internal f_mbedtls_md_hmac_reset)) ::
 (_mbedtls_md_hmac_update, Gfun(Internal f_mbedtls_md_hmac_update)) ::
 (_mbedtls_md_hmac_finish, Gfun(Internal f_mbedtls_md_hmac_finish)) ::
 (_mbedtls_md_free, Gfun(Internal f_mbedtls_md_free)) :: nil);
prog_public :=
(_mbedtls_md_free :: _mbedtls_md_hmac_finish :: _mbedtls_md_hmac_update ::
 _mbedtls_md_hmac_reset :: _mbedtls_md_hmac_starts :: _mbedtls_md_setup ::
 _mbedtls_md_get_size :: _mbedtls_md_info_from_type ::
 _mbedtls_md_info_from_string :: _HMAC_cleanup :: _HMAC_Final ::
 _HMAC_Update :: _HMAC_Init :: _free :: _malloc :: ___builtin_debug ::
 ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fsqrt :: ___builtin_ctz :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___i64_sar :: ___i64_shr :: ___i64_shl :: ___i64_umod :: ___i64_smod ::
 ___i64_udiv :: ___i64_sdiv :: ___i64_utof :: ___i64_stof :: ___i64_utod ::
 ___i64_stod :: ___i64_dtou :: ___i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fabs :: nil);
prog_main := _main;
prog_types := composites;
prog_comp_env := make_composite_env composites;
prog_comp_env_eq := refl_equal _
|}.
