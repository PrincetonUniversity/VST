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
  Definition source_file := "sha/hmac.c".
  Definition normalized := false.
End Info.

Definition _HMAC : ident := $"HMAC".
Definition _HMAC2 : ident := $"HMAC2".
Definition _HMAC_Final : ident := $"HMAC_Final".
Definition _HMAC_Init : ident := $"HMAC_Init".
Definition _HMAC_Update : ident := $"HMAC_Update".
Definition _HMAC_cleanup : ident := $"HMAC_cleanup".
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
Definition _aux : ident := $"aux".
Definition _b : ident := $"b".
Definition _buf : ident := $"buf".
Definition _c : ident := $"c".
Definition _cNh : ident := $"cNh".
Definition _cNl : ident := $"cNl".
Definition _ctx : ident := $"ctx".
Definition _ctx_key : ident := $"ctx_key".
Definition _d : ident := $"d".
Definition _data : ident := $"data".
Definition _data_ : ident := $"data_".
Definition _e : ident := $"e".
Definition _f : ident := $"f".
Definition _fragment : ident := $"fragment".
Definition _g : ident := $"g".
Definition _h : ident := $"h".
Definition _hmac_ctx_st : ident := $"hmac_ctx_st".
Definition _i : ident := $"i".
Definition _i_ctx : ident := $"i_ctx".
Definition _in : ident := $"in".
Definition _j : ident := $"j".
Definition _key : ident := $"key".
Definition _key_len : ident := $"key_len".
Definition _l : ident := $"l".
Definition _len : ident := $"len".
Definition _ll : ident := $"ll".
Definition _m : ident := $"m".
Definition _m__1 : ident := $"m__1".
Definition _main : ident := $"main".
Definition _md : ident := $"md".
Definition _md_ctx : ident := $"md_ctx".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _n : ident := $"n".
Definition _num : ident := $"num".
Definition _o_ctx : ident := $"o_ctx".
Definition _p : ident := $"p".
Definition _pad : ident := $"pad".
Definition _reset : ident := $"reset".
Definition _s0 : ident := $"s0".
Definition _s1 : ident := $"s1".
Definition _sha256_block_data_order : ident := $"sha256_block_data_order".
Definition _t : ident := $"t".
Definition _xn : ident := $"xn".

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
                    ((Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                       (Econst_int (Int.repr 32) tint) (tptr tuchar)) ::
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
                ((Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                   (Etempvar _len tint) (tptr tuchar)) ::
                 (Econst_int (Int.repr 0) tint) ::
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
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
     cc_default)) ::
 (_SHA256_Init,
   Gfun(External (EF_external "SHA256_Init"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _SHA256state_st noattr)) Tnil) tvoid cc_default)) ::
 (_SHA256_Update,
   Gfun(External (EF_external "SHA256_Update"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _SHA256state_st noattr))
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid cc_default)) ::
 (_SHA256_Final,
   Gfun(External (EF_external "SHA256_Final"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tuchar)
       (Tcons (tptr (Tstruct _SHA256state_st noattr)) Tnil)) tvoid
     cc_default)) :: (_HMAC_Init, Gfun(Internal f_HMAC_Init)) ::
 (_HMAC_Update, Gfun(Internal f_HMAC_Update)) ::
 (_HMAC_Final, Gfun(Internal f_HMAC_Final)) ::
 (_HMAC_cleanup, Gfun(Internal f_HMAC_cleanup)) :: (_m, Gvar v_m) ::
 (_HMAC, Gfun(Internal f_HMAC)) :: (_m__1, Gvar v_m__1) ::
 (_HMAC2, Gfun(Internal f_HMAC2)) :: nil).

Definition public_idents : list ident :=
(_HMAC2 :: _HMAC :: _HMAC_cleanup :: _HMAC_Final :: _HMAC_Update ::
 _HMAC_Init :: _SHA256_Final :: _SHA256_Update :: _SHA256_Init :: _memset ::
 _memcpy :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


