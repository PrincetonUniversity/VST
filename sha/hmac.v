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
  Definition source_file := "sha/hmac.c".
  Definition normalized := false.
End Info.

Definition _HMAC : ident := 118%positive.
Definition _HMAC2 : ident := 120%positive.
Definition _HMAC_Final : ident := 114%positive.
Definition _HMAC_Init : ident := 111%positive.
Definition _HMAC_Update : ident := 112%positive.
Definition _HMAC_cleanup : ident := 115%positive.
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
Definition _aux : ident := 109%positive.
Definition _b : ident := 50%positive.
Definition _buf : ident := 113%positive.
Definition _c : ident := 51%positive.
Definition _cNh : ident := 69%positive.
Definition _cNl : ident := 68%positive.
Definition _ctx : ident := 47%positive.
Definition _ctx_key : ident := 110%positive.
Definition _d : ident := 52%positive.
Definition _data : ident := 5%positive.
Definition _data_ : ident := 71%positive.
Definition _e : ident := 53%positive.
Definition _f : ident := 54%positive.
Definition _fragment : ident := 74%positive.
Definition _g : ident := 55%positive.
Definition _h : ident := 2%positive.
Definition _hmac_ctx_st : ident := 101%positive.
Definition _i : ident := 64%positive.
Definition _i_ctx : ident := 103%positive.
Definition _in : ident := 48%positive.
Definition _j : ident := 106%positive.
Definition _key : ident := 105%positive.
Definition _key_len : ident := 117%positive.
Definition _l : ident := 62%positive.
Definition _len : ident := 67%positive.
Definition _ll : ident := 77%positive.
Definition _m : ident := 116%positive.
Definition _m__1 : ident := 119%positive.
Definition _main : ident := 100%positive.
Definition _md : ident := 76%positive.
Definition _md_ctx : ident := 102%positive.
Definition _memcpy : ident := 44%positive.
Definition _memset : ident := 45%positive.
Definition _n : ident := 73%positive.
Definition _num : ident := 6%positive.
Definition _o_ctx : ident := 104%positive.
Definition _p : ident := 72%positive.
Definition _pad : ident := 108%positive.
Definition _reset : ident := 107%positive.
Definition _s0 : ident := 56%positive.
Definition _s1 : ident := 57%positive.
Definition _sha256_block_data_order : ident := 65%positive.
Definition _t : ident := 60%positive.
Definition _xn : ident := 78%positive.

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
                                     ((tptr (Tstruct _SHA256state_st noattr)) ::
                                      nil) tvoid cc_default))
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
                                         ((tptr (Tstruct _SHA256state_st noattr)) ::
                                          (tptr tvoid) :: tuint :: nil) tvoid
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
                                          ((tptr tuchar) ::
                                           (tptr (Tstruct _SHA256state_st noattr)) ::
                                           nil) tvoid cc_default))
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
                                    ((tptr tvoid) :: tint :: tuint :: nil)
                                    (tptr tvoid) cc_default))
                    ((Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                       (Econst_int (Int.repr 32) tint) (tptr tuchar)) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 32) tint) :: nil)))))
            (Ssequence
              (Scall None
                (Evar _memcpy (Tfunction
                                ((tptr tvoid) :: (tptr tvoid) :: tuint ::
                                 nil) (tptr tvoid) cc_default))
                ((Evar _ctx_key (tarray tuchar 64)) ::
                 (Etempvar _key (tptr tuchar)) :: (Etempvar _len tint) ::
                 nil))
              (Scall None
                (Evar _memset (Tfunction
                                ((tptr tvoid) :: tint :: tuint :: nil)
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
                                   ((tptr (Tstruct _SHA256state_st noattr)) ::
                                    nil) tvoid cc_default))
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
                                       ((tptr (Tstruct _SHA256state_st noattr)) ::
                                        (tptr tvoid) :: tuint :: nil) tvoid
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
                                         ((tptr (Tstruct _SHA256state_st noattr)) ::
                                          nil) tvoid cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
                           (Tstruct _hmac_ctx_st noattr)) _o_ctx
                         (Tstruct _SHA256state_st noattr))
                       (tptr (Tstruct _SHA256state_st noattr))) :: nil))
                  (Scall None
                    (Evar _SHA256_Update (Tfunction
                                           ((tptr (Tstruct _SHA256state_st noattr)) ::
                                            (tptr tvoid) :: tuint :: nil)
                                           tvoid cc_default))
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
                        ((tptr tvoid) :: (tptr tvoid) :: tuint :: nil)
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
                         ((tptr (Tstruct _SHA256state_st noattr)) ::
                          (tptr tvoid) :: tuint :: nil) tvoid cc_default))
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
                          ((tptr tuchar) ::
                           (tptr (Tstruct _SHA256state_st noattr)) :: nil)
                          tvoid cc_default))
    ((Evar _buf (tarray tuchar 32)) ::
     (Eaddrof
       (Efield
         (Ederef (Etempvar _ctx (tptr (Tstruct _hmac_ctx_st noattr)))
           (Tstruct _hmac_ctx_st noattr)) _md_ctx
         (Tstruct _SHA256state_st noattr))
       (tptr (Tstruct _SHA256state_st noattr))) :: nil))
  (Ssequence
    (Scall None
      (Evar _memcpy (Tfunction ((tptr tvoid) :: (tptr tvoid) :: tuint :: nil)
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
       (Esizeof (Tstruct _SHA256state_st noattr) tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar _SHA256_Update (Tfunction
                               ((tptr (Tstruct _SHA256state_st noattr)) ::
                                (tptr tvoid) :: tuint :: nil) tvoid
                               cc_default))
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
                              ((tptr tuchar) ::
                               (tptr (Tstruct _SHA256state_st noattr)) ::
                               nil) tvoid cc_default))
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
  (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tuint :: nil)
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
                         ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                          (tptr tuchar) :: tint :: nil) tvoid cc_default))
      ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
         (tptr (Tstruct _hmac_ctx_st noattr))) ::
       (Etempvar _key (tptr tuchar)) :: (Etempvar _key_len tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _HMAC_Update (Tfunction
                             ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                              (tptr tvoid) :: tuint :: nil) tvoid cc_default))
        ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
           (tptr (Tstruct _hmac_ctx_st noattr))) ::
         (Etempvar _d (tptr tuchar)) :: (Etempvar _n tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _HMAC_Final (Tfunction
                              ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                               (tptr tuchar) :: nil) tvoid cc_default))
          ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
             (tptr (Tstruct _hmac_ctx_st noattr))) ::
           (Etempvar _md (tptr tuchar)) :: nil))
        (Ssequence
          (Scall None
            (Evar _HMAC_cleanup (Tfunction
                                  ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                                   nil) tvoid cc_default))
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
                         ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                          (tptr tuchar) :: tint :: nil) tvoid cc_default))
      ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
         (tptr (Tstruct _hmac_ctx_st noattr))) ::
       (Etempvar _key (tptr tuchar)) :: (Etempvar _key_len tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _HMAC_Update (Tfunction
                             ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                              (tptr tvoid) :: tuint :: nil) tvoid cc_default))
        ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
           (tptr (Tstruct _hmac_ctx_st noattr))) ::
         (Etempvar _d (tptr tuchar)) :: (Etempvar _n tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _HMAC_Final (Tfunction
                              ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                               (tptr tuchar) :: nil) tvoid cc_default))
          ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
             (tptr (Tstruct _hmac_ctx_st noattr))) ::
           (Etempvar _md (tptr tuchar)) :: nil))
        (Ssequence
          (Scall None
            (Evar _HMAC_Init (Tfunction
                               ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                                (tptr tuchar) :: tint :: nil) tvoid
                               cc_default))
            ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
               (tptr (Tstruct _hmac_ctx_st noattr))) ::
             (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
             (Etempvar _key_len tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _HMAC_Update (Tfunction
                                   ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                                    (tptr tvoid) :: tuint :: nil) tvoid
                                   cc_default))
              ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
                 (tptr (Tstruct _hmac_ctx_st noattr))) ::
               (Etempvar _d (tptr tuchar)) :: (Etempvar _n tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _HMAC_Final (Tfunction
                                    ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                                     (tptr tuchar) :: nil) tvoid cc_default))
                ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
                   (tptr (Tstruct _hmac_ctx_st noattr))) ::
                 (Ebinop Oadd (Etempvar _md (tptr tuchar))
                   (Econst_int (Int.repr 32) tint) (tptr tuchar)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _HMAC_cleanup (Tfunction
                                        ((tptr (Tstruct _hmac_ctx_st noattr)) ::
                                         nil) tvoid cc_default))
                  ((Eaddrof (Evar _c (Tstruct _hmac_ctx_st noattr))
                     (tptr (Tstruct _hmac_ctx_st noattr))) :: nil))
                (Sreturn (Some (Etempvar _md (tptr tuchar))))))))))))
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
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xint :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: tint :: tuint :: nil) (tptr tvoid) cc_default)) ::
 (_SHA256_Init,
   Gfun(External (EF_external "SHA256_Init"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _SHA256state_st noattr)) :: nil) tvoid cc_default)) ::
 (_SHA256_Update,
   Gfun(External (EF_external "SHA256_Update"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xint :: nil)
                     AST.Xvoid cc_default))
     ((tptr (Tstruct _SHA256state_st noattr)) :: (tptr tvoid) :: tuint ::
      nil) tvoid cc_default)) ::
 (_SHA256_Final,
   Gfun(External (EF_external "SHA256_Final"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr tuchar) :: (tptr (Tstruct _SHA256state_st noattr)) :: nil) tvoid
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
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


