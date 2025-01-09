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
  Definition source_file := "sha/sha.c".
  Definition normalized := false.
End Info.

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
Definition _b : ident := 50%positive.
Definition _c : ident := 51%positive.
Definition _cNh : ident := 69%positive.
Definition _cNl : ident := 68%positive.
Definition _ctx : ident := 47%positive.
Definition _d : ident := 52%positive.
Definition _data : ident := 5%positive.
Definition _data_ : ident := 71%positive.
Definition _e : ident := 53%positive.
Definition _f : ident := 54%positive.
Definition _fragment : ident := 74%positive.
Definition _g : ident := 55%positive.
Definition _h : ident := 2%positive.
Definition _i : ident := 64%positive.
Definition _in : ident := 48%positive.
Definition _l : ident := 62%positive.
Definition _len : ident := 67%positive.
Definition _ll : ident := 77%positive.
Definition _main : ident := 100%positive.
Definition _md : ident := 76%positive.
Definition _memcpy : ident := 44%positive.
Definition _memset : ident := 45%positive.
Definition _n : ident := 73%positive.
Definition _num : ident := 6%positive.
Definition _p : ident := 72%positive.
Definition _s0 : ident := 56%positive.
Definition _s1 : ident := 57%positive.
Definition _sha256_block_data_order : ident := 65%positive.
Definition _t : ident := 60%positive.
Definition _xn : ident := 78%positive.
Definition _t'1 : ident := 101%positive.

Definition v_K256 := {|
  gvar_info := (tarray tuint 64);
  gvar_init := (Init_int32 (Int.repr 1116352408) ::
                Init_int32 (Int.repr 1899447441) ::
                Init_int32 (Int.repr (-1245643825)) ::
                Init_int32 (Int.repr (-373957723)) ::
                Init_int32 (Int.repr 961987163) ::
                Init_int32 (Int.repr 1508970993) ::
                Init_int32 (Int.repr (-1841331548)) ::
                Init_int32 (Int.repr (-1424204075)) ::
                Init_int32 (Int.repr (-670586216)) ::
                Init_int32 (Int.repr 310598401) ::
                Init_int32 (Int.repr 607225278) ::
                Init_int32 (Int.repr 1426881987) ::
                Init_int32 (Int.repr 1925078388) ::
                Init_int32 (Int.repr (-2132889090)) ::
                Init_int32 (Int.repr (-1680079193)) ::
                Init_int32 (Int.repr (-1046744716)) ::
                Init_int32 (Int.repr (-459576895)) ::
                Init_int32 (Int.repr (-272742522)) ::
                Init_int32 (Int.repr 264347078) ::
                Init_int32 (Int.repr 604807628) ::
                Init_int32 (Int.repr 770255983) ::
                Init_int32 (Int.repr 1249150122) ::
                Init_int32 (Int.repr 1555081692) ::
                Init_int32 (Int.repr 1996064986) ::
                Init_int32 (Int.repr (-1740746414)) ::
                Init_int32 (Int.repr (-1473132947)) ::
                Init_int32 (Int.repr (-1341970488)) ::
                Init_int32 (Int.repr (-1084653625)) ::
                Init_int32 (Int.repr (-958395405)) ::
                Init_int32 (Int.repr (-710438585)) ::
                Init_int32 (Int.repr 113926993) ::
                Init_int32 (Int.repr 338241895) ::
                Init_int32 (Int.repr 666307205) ::
                Init_int32 (Int.repr 773529912) ::
                Init_int32 (Int.repr 1294757372) ::
                Init_int32 (Int.repr 1396182291) ::
                Init_int32 (Int.repr 1695183700) ::
                Init_int32 (Int.repr 1986661051) ::
                Init_int32 (Int.repr (-2117940946)) ::
                Init_int32 (Int.repr (-1838011259)) ::
                Init_int32 (Int.repr (-1564481375)) ::
                Init_int32 (Int.repr (-1474664885)) ::
                Init_int32 (Int.repr (-1035236496)) ::
                Init_int32 (Int.repr (-949202525)) ::
                Init_int32 (Int.repr (-778901479)) ::
                Init_int32 (Int.repr (-694614492)) ::
                Init_int32 (Int.repr (-200395387)) ::
                Init_int32 (Int.repr 275423344) ::
                Init_int32 (Int.repr 430227734) ::
                Init_int32 (Int.repr 506948616) ::
                Init_int32 (Int.repr 659060556) ::
                Init_int32 (Int.repr 883997877) ::
                Init_int32 (Int.repr 958139571) ::
                Init_int32 (Int.repr 1322822218) ::
                Init_int32 (Int.repr 1537002063) ::
                Init_int32 (Int.repr 1747873779) ::
                Init_int32 (Int.repr 1955562222) ::
                Init_int32 (Int.repr 2024104815) ::
                Init_int32 (Int.repr (-2067236844)) ::
                Init_int32 (Int.repr (-1933114872)) ::
                Init_int32 (Int.repr (-1866530822)) ::
                Init_int32 (Int.repr (-1538233109)) ::
                Init_int32 (Int.repr (-1090935817)) ::
                Init_int32 (Int.repr (-965641998)) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_sha256_block_data_order := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _SHA256state_st noattr))) ::
                (_in, (tptr tvoid)) :: nil);
  fn_vars := ((_X, (tarray tuint 16)) :: nil);
  fn_temps := ((_a, tuint) :: (_b, tuint) :: (_c, tuint) :: (_d, tuint) ::
               (_e, tuint) :: (_f, tuint) :: (_g, tuint) :: (_h, tuint) ::
               (_s0, tuint) :: (_s1, tuint) :: (_T1, tuint) ::
               (_T2, tuint) :: (_t, tuint) :: (_l, tuint) :: (_Ki, tuint) ::
               (_i, tint) :: (_data, (tptr tuchar)) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _data (Etempvar _in (tptr tvoid)))
  (Ssequence
    (Sset _a
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
              (Tstruct _SHA256state_st noattr)) _h (tarray tuint 8))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sset _b
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                (Tstruct _SHA256state_st noattr)) _h (tarray tuint 8))
            (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
      (Ssequence
        (Sset _c
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                  (Tstruct _SHA256state_st noattr)) _h (tarray tuint 8))
              (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
        (Ssequence
          (Sset _d
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                    (Tstruct _SHA256state_st noattr)) _h (tarray tuint 8))
                (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
          (Ssequence
            (Sset _e
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                      (Tstruct _SHA256state_st noattr)) _h (tarray tuint 8))
                  (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _f
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                        (Tstruct _SHA256state_st noattr)) _h
                      (tarray tuint 8)) (Econst_int (Int.repr 5) tint)
                    (tptr tuint)) tuint))
              (Ssequence
                (Sset _g
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                          (Tstruct _SHA256state_st noattr)) _h
                        (tarray tuint 8)) (Econst_int (Int.repr 6) tint)
                      (tptr tuint)) tuint))
                (Ssequence
                  (Sset _h
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                            (Tstruct _SHA256state_st noattr)) _h
                          (tarray tuint 8)) (Econst_int (Int.repr 7) tint)
                        (tptr tuint)) tuint))
                  (Ssequence
                    (Ssequence
                      (Sset _i (Econst_int (Int.repr 0) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                         (Econst_int (Int.repr 16) tint)
                                         tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'1)
                                  (Evar ___builtin_read32_reversed (Tfunction
                                                                    ((tptr tuint) ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                  ((Ecast (Etempvar _data (tptr tuchar))
                                     (tptr tuint)) :: nil))
                                (Sset _l (Ecast (Etempvar _t'1 tuint) tuint)))
                              (Sset _data
                                (Ebinop Oadd (Etempvar _data (tptr tuchar))
                                  (Econst_int (Int.repr 4) tint)
                                  (tptr tuchar))))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Evar _X (tarray tuint 16))
                                    (Etempvar _i tint) (tptr tuint)) tuint)
                                (Etempvar _l tuint))
                              (Ssequence
                                (Sset _Ki
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _K256 (tarray tuint 64))
                                      (Etempvar _i tint) (tptr tuint)) tuint))
                                (Ssequence
                                  (Sset _T1
                                    (Ebinop Oadd
                                      (Ebinop Oadd
                                        (Ebinop Oadd
                                          (Ebinop Oadd (Etempvar _l tuint)
                                            (Etempvar _h tuint) tuint)
                                          (Ebinop Oxor
                                            (Ebinop Oxor
                                              (Ebinop Oor
                                                (Ebinop Oshl
                                                  (Etempvar _e tuint)
                                                  (Econst_int (Int.repr 26) tint)
                                                  tuint)
                                                (Ebinop Oshr
                                                  (Ebinop Oand
                                                    (Etempvar _e tuint)
                                                    (Econst_int (Int.repr (-1)) tuint)
                                                    tuint)
                                                  (Ebinop Osub
                                                    (Econst_int (Int.repr 32) tint)
                                                    (Econst_int (Int.repr 26) tint)
                                                    tint) tuint) tuint)
                                              (Ebinop Oor
                                                (Ebinop Oshl
                                                  (Etempvar _e tuint)
                                                  (Econst_int (Int.repr 21) tint)
                                                  tuint)
                                                (Ebinop Oshr
                                                  (Ebinop Oand
                                                    (Etempvar _e tuint)
                                                    (Econst_int (Int.repr (-1)) tuint)
                                                    tuint)
                                                  (Ebinop Osub
                                                    (Econst_int (Int.repr 32) tint)
                                                    (Econst_int (Int.repr 21) tint)
                                                    tint) tuint) tuint)
                                              tuint)
                                            (Ebinop Oor
                                              (Ebinop Oshl
                                                (Etempvar _e tuint)
                                                (Econst_int (Int.repr 7) tint)
                                                tuint)
                                              (Ebinop Oshr
                                                (Ebinop Oand
                                                  (Etempvar _e tuint)
                                                  (Econst_int (Int.repr (-1)) tuint)
                                                  tuint)
                                                (Ebinop Osub
                                                  (Econst_int (Int.repr 32) tint)
                                                  (Econst_int (Int.repr 7) tint)
                                                  tint) tuint) tuint) tuint)
                                          tuint)
                                        (Ebinop Oxor
                                          (Ebinop Oand (Etempvar _e tuint)
                                            (Etempvar _f tuint) tuint)
                                          (Ebinop Oand
                                            (Eunop Onotint
                                              (Etempvar _e tuint) tuint)
                                            (Etempvar _g tuint) tuint) tuint)
                                        tuint) (Etempvar _Ki tuint) tuint))
                                  (Ssequence
                                    (Sset _T2
                                      (Ebinop Oadd
                                        (Ebinop Oxor
                                          (Ebinop Oxor
                                            (Ebinop Oor
                                              (Ebinop Oshl
                                                (Etempvar _a tuint)
                                                (Econst_int (Int.repr 30) tint)
                                                tuint)
                                              (Ebinop Oshr
                                                (Ebinop Oand
                                                  (Etempvar _a tuint)
                                                  (Econst_int (Int.repr (-1)) tuint)
                                                  tuint)
                                                (Ebinop Osub
                                                  (Econst_int (Int.repr 32) tint)
                                                  (Econst_int (Int.repr 30) tint)
                                                  tint) tuint) tuint)
                                            (Ebinop Oor
                                              (Ebinop Oshl
                                                (Etempvar _a tuint)
                                                (Econst_int (Int.repr 19) tint)
                                                tuint)
                                              (Ebinop Oshr
                                                (Ebinop Oand
                                                  (Etempvar _a tuint)
                                                  (Econst_int (Int.repr (-1)) tuint)
                                                  tuint)
                                                (Ebinop Osub
                                                  (Econst_int (Int.repr 32) tint)
                                                  (Econst_int (Int.repr 19) tint)
                                                  tint) tuint) tuint) tuint)
                                          (Ebinop Oor
                                            (Ebinop Oshl (Etempvar _a tuint)
                                              (Econst_int (Int.repr 10) tint)
                                              tuint)
                                            (Ebinop Oshr
                                              (Ebinop Oand
                                                (Etempvar _a tuint)
                                                (Econst_int (Int.repr (-1)) tuint)
                                                tuint)
                                              (Ebinop Osub
                                                (Econst_int (Int.repr 32) tint)
                                                (Econst_int (Int.repr 10) tint)
                                                tint) tuint) tuint) tuint)
                                        (Ebinop Oxor
                                          (Ebinop Oxor
                                            (Ebinop Oand (Etempvar _a tuint)
                                              (Etempvar _b tuint) tuint)
                                            (Ebinop Oand (Etempvar _a tuint)
                                              (Etempvar _c tuint) tuint)
                                            tuint)
                                          (Ebinop Oand (Etempvar _b tuint)
                                            (Etempvar _c tuint) tuint) tuint)
                                        tuint))
                                    (Ssequence
                                      (Sset _h (Etempvar _g tuint))
                                      (Ssequence
                                        (Sset _g (Etempvar _f tuint))
                                        (Ssequence
                                          (Sset _f (Etempvar _e tuint))
                                          (Ssequence
                                            (Sset _e
                                              (Ebinop Oadd
                                                (Etempvar _d tuint)
                                                (Etempvar _T1 tuint) tuint))
                                            (Ssequence
                                              (Sset _d (Etempvar _c tuint))
                                              (Ssequence
                                                (Sset _c (Etempvar _b tuint))
                                                (Ssequence
                                                  (Sset _b
                                                    (Etempvar _a tuint))
                                                  (Sset _a
                                                    (Ebinop Oadd
                                                      (Etempvar _T1 tuint)
                                                      (Etempvar _T2 tuint)
                                                      tuint)))))))))))))))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    (Ssequence
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                         (Econst_int (Int.repr 64) tint)
                                         tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Sset _s0
                              (Ederef
                                (Ebinop Oadd (Evar _X (tarray tuint 16))
                                  (Ebinop Oand
                                    (Ebinop Oadd (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    (Econst_int (Int.repr 15) tint) tint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sset _s0
                                (Ebinop Oxor
                                  (Ebinop Oxor
                                    (Ebinop Oor
                                      (Ebinop Oshl (Etempvar _s0 tuint)
                                        (Econst_int (Int.repr 25) tint)
                                        tuint)
                                      (Ebinop Oshr
                                        (Ebinop Oand (Etempvar _s0 tuint)
                                          (Econst_int (Int.repr (-1)) tuint)
                                          tuint)
                                        (Ebinop Osub
                                          (Econst_int (Int.repr 32) tint)
                                          (Econst_int (Int.repr 25) tint)
                                          tint) tuint) tuint)
                                    (Ebinop Oor
                                      (Ebinop Oshl (Etempvar _s0 tuint)
                                        (Econst_int (Int.repr 14) tint)
                                        tuint)
                                      (Ebinop Oshr
                                        (Ebinop Oand (Etempvar _s0 tuint)
                                          (Econst_int (Int.repr (-1)) tuint)
                                          tuint)
                                        (Ebinop Osub
                                          (Econst_int (Int.repr 32) tint)
                                          (Econst_int (Int.repr 14) tint)
                                          tint) tuint) tuint) tuint)
                                  (Ebinop Oshr (Etempvar _s0 tuint)
                                    (Econst_int (Int.repr 3) tint) tuint)
                                  tuint))
                              (Ssequence
                                (Sset _s1
                                  (Ederef
                                    (Ebinop Oadd (Evar _X (tarray tuint 16))
                                      (Ebinop Oand
                                        (Ebinop Oadd (Etempvar _i tint)
                                          (Econst_int (Int.repr 14) tint)
                                          tint)
                                        (Econst_int (Int.repr 15) tint) tint)
                                      (tptr tuint)) tuint))
                                (Ssequence
                                  (Sset _s1
                                    (Ebinop Oxor
                                      (Ebinop Oxor
                                        (Ebinop Oor
                                          (Ebinop Oshl (Etempvar _s1 tuint)
                                            (Econst_int (Int.repr 15) tint)
                                            tuint)
                                          (Ebinop Oshr
                                            (Ebinop Oand (Etempvar _s1 tuint)
                                              (Econst_int (Int.repr (-1)) tuint)
                                              tuint)
                                            (Ebinop Osub
                                              (Econst_int (Int.repr 32) tint)
                                              (Econst_int (Int.repr 15) tint)
                                              tint) tuint) tuint)
                                        (Ebinop Oor
                                          (Ebinop Oshl (Etempvar _s1 tuint)
                                            (Econst_int (Int.repr 13) tint)
                                            tuint)
                                          (Ebinop Oshr
                                            (Ebinop Oand (Etempvar _s1 tuint)
                                              (Econst_int (Int.repr (-1)) tuint)
                                              tuint)
                                            (Ebinop Osub
                                              (Econst_int (Int.repr 32) tint)
                                              (Econst_int (Int.repr 13) tint)
                                              tint) tuint) tuint) tuint)
                                      (Ebinop Oshr (Etempvar _s1 tuint)
                                        (Econst_int (Int.repr 10) tint)
                                        tuint) tuint))
                                  (Ssequence
                                    (Sset _T1
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _X (tarray tuint 16))
                                          (Ebinop Oand (Etempvar _i tint)
                                            (Econst_int (Int.repr 15) tint)
                                            tint) (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sset _t
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _X (tarray tuint 16))
                                            (Ebinop Oand
                                              (Ebinop Oadd (Etempvar _i tint)
                                                (Econst_int (Int.repr 9) tint)
                                                tint)
                                              (Econst_int (Int.repr 15) tint)
                                              tint) (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sset _T1
                                          (Ebinop Oadd (Etempvar _T1 tuint)
                                            (Ebinop Oadd
                                              (Ebinop Oadd
                                                (Etempvar _s0 tuint)
                                                (Etempvar _s1 tuint) tuint)
                                              (Etempvar _t tuint) tuint)
                                            tuint))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _X (tarray tuint 16))
                                                (Ebinop Oand
                                                  (Etempvar _i tint)
                                                  (Econst_int (Int.repr 15) tint)
                                                  tint) (tptr tuint)) tuint)
                                            (Etempvar _T1 tuint))
                                          (Ssequence
                                            (Sset _Ki
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _K256 (tarray tuint 64))
                                                  (Etempvar _i tint)
                                                  (tptr tuint)) tuint))
                                            (Ssequence
                                              (Sset _T1
                                                (Ebinop Oadd
                                                  (Etempvar _T1 tuint)
                                                  (Ebinop Oadd
                                                    (Ebinop Oadd
                                                      (Ebinop Oadd
                                                        (Etempvar _h tuint)
                                                        (Ebinop Oxor
                                                          (Ebinop Oxor
                                                            (Ebinop Oor
                                                              (Ebinop Oshl
                                                                (Etempvar _e tuint)
                                                                (Econst_int (Int.repr 26) tint)
                                                                tuint)
                                                              (Ebinop Oshr
                                                                (Ebinop Oand
                                                                  (Etempvar _e tuint)
                                                                  (Econst_int (Int.repr (-1)) tuint)
                                                                  tuint)
                                                                (Ebinop Osub
                                                                  (Econst_int (Int.repr 32) tint)
                                                                  (Econst_int (Int.repr 26) tint)
                                                                  tint)
                                                                tuint) tuint)
                                                            (Ebinop Oor
                                                              (Ebinop Oshl
                                                                (Etempvar _e tuint)
                                                                (Econst_int (Int.repr 21) tint)
                                                                tuint)
                                                              (Ebinop Oshr
                                                                (Ebinop Oand
                                                                  (Etempvar _e tuint)
                                                                  (Econst_int (Int.repr (-1)) tuint)
                                                                  tuint)
                                                                (Ebinop Osub
                                                                  (Econst_int (Int.repr 32) tint)
                                                                  (Econst_int (Int.repr 21) tint)
                                                                  tint)
                                                                tuint) tuint)
                                                            tuint)
                                                          (Ebinop Oor
                                                            (Ebinop Oshl
                                                              (Etempvar _e tuint)
                                                              (Econst_int (Int.repr 7) tint)
                                                              tuint)
                                                            (Ebinop Oshr
                                                              (Ebinop Oand
                                                                (Etempvar _e tuint)
                                                                (Econst_int (Int.repr (-1)) tuint)
                                                                tuint)
                                                              (Ebinop Osub
                                                                (Econst_int (Int.repr 32) tint)
                                                                (Econst_int (Int.repr 7) tint)
                                                                tint) tuint)
                                                            tuint) tuint)
                                                        tuint)
                                                      (Ebinop Oxor
                                                        (Ebinop Oand
                                                          (Etempvar _e tuint)
                                                          (Etempvar _f tuint)
                                                          tuint)
                                                        (Ebinop Oand
                                                          (Eunop Onotint
                                                            (Etempvar _e tuint)
                                                            tuint)
                                                          (Etempvar _g tuint)
                                                          tuint) tuint)
                                                      tuint)
                                                    (Etempvar _Ki tuint)
                                                    tuint) tuint))
                                              (Ssequence
                                                (Sset _T2
                                                  (Ebinop Oadd
                                                    (Ebinop Oxor
                                                      (Ebinop Oxor
                                                        (Ebinop Oor
                                                          (Ebinop Oshl
                                                            (Etempvar _a tuint)
                                                            (Econst_int (Int.repr 30) tint)
                                                            tuint)
                                                          (Ebinop Oshr
                                                            (Ebinop Oand
                                                              (Etempvar _a tuint)
                                                              (Econst_int (Int.repr (-1)) tuint)
                                                              tuint)
                                                            (Ebinop Osub
                                                              (Econst_int (Int.repr 32) tint)
                                                              (Econst_int (Int.repr 30) tint)
                                                              tint) tuint)
                                                          tuint)
                                                        (Ebinop Oor
                                                          (Ebinop Oshl
                                                            (Etempvar _a tuint)
                                                            (Econst_int (Int.repr 19) tint)
                                                            tuint)
                                                          (Ebinop Oshr
                                                            (Ebinop Oand
                                                              (Etempvar _a tuint)
                                                              (Econst_int (Int.repr (-1)) tuint)
                                                              tuint)
                                                            (Ebinop Osub
                                                              (Econst_int (Int.repr 32) tint)
                                                              (Econst_int (Int.repr 19) tint)
                                                              tint) tuint)
                                                          tuint) tuint)
                                                      (Ebinop Oor
                                                        (Ebinop Oshl
                                                          (Etempvar _a tuint)
                                                          (Econst_int (Int.repr 10) tint)
                                                          tuint)
                                                        (Ebinop Oshr
                                                          (Ebinop Oand
                                                            (Etempvar _a tuint)
                                                            (Econst_int (Int.repr (-1)) tuint)
                                                            tuint)
                                                          (Ebinop Osub
                                                            (Econst_int (Int.repr 32) tint)
                                                            (Econst_int (Int.repr 10) tint)
                                                            tint) tuint)
                                                        tuint) tuint)
                                                    (Ebinop Oxor
                                                      (Ebinop Oxor
                                                        (Ebinop Oand
                                                          (Etempvar _a tuint)
                                                          (Etempvar _b tuint)
                                                          tuint)
                                                        (Ebinop Oand
                                                          (Etempvar _a tuint)
                                                          (Etempvar _c tuint)
                                                          tuint) tuint)
                                                      (Ebinop Oand
                                                        (Etempvar _b tuint)
                                                        (Etempvar _c tuint)
                                                        tuint) tuint) tuint))
                                                (Ssequence
                                                  (Sset _h
                                                    (Etempvar _g tuint))
                                                  (Ssequence
                                                    (Sset _g
                                                      (Etempvar _f tuint))
                                                    (Ssequence
                                                      (Sset _f
                                                        (Etempvar _e tuint))
                                                      (Ssequence
                                                        (Sset _e
                                                          (Ebinop Oadd
                                                            (Etempvar _d tuint)
                                                            (Etempvar _T1 tuint)
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _d
                                                            (Etempvar _c tuint))
                                                          (Ssequence
                                                            (Sset _c
                                                              (Etempvar _b tuint))
                                                            (Ssequence
                                                              (Sset _b
                                                                (Etempvar _a tuint))
                                                              (Sset _a
                                                                (Ebinop Oadd
                                                                  (Etempvar _T1 tuint)
                                                                  (Etempvar _T2 tuint)
                                                                  tuint)))))))))))))))))))))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint)))
                      (Ssequence
                        (Sset _t
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                  (Tstruct _SHA256state_st noattr)) _h
                                (tarray tuint 8))
                              (Econst_int (Int.repr 0) tint) (tptr tuint))
                            tuint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                    (Tstruct _SHA256state_st noattr)) _h
                                  (tarray tuint 8))
                                (Econst_int (Int.repr 0) tint) (tptr tuint))
                              tuint)
                            (Ebinop Oadd (Etempvar _t tuint)
                              (Etempvar _a tuint) tuint))
                          (Ssequence
                            (Sset _t
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                      (Tstruct _SHA256state_st noattr)) _h
                                    (tarray tuint 8))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                        (Tstruct _SHA256state_st noattr)) _h
                                      (tarray tuint 8))
                                    (Econst_int (Int.repr 1) tint)
                                    (tptr tuint)) tuint)
                                (Ebinop Oadd (Etempvar _t tuint)
                                  (Etempvar _b tuint) tuint))
                              (Ssequence
                                (Sset _t
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                          (Tstruct _SHA256state_st noattr))
                                        _h (tarray tuint 8))
                                      (Econst_int (Int.repr 2) tint)
                                      (tptr tuint)) tuint))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                            (Tstruct _SHA256state_st noattr))
                                          _h (tarray tuint 8))
                                        (Econst_int (Int.repr 2) tint)
                                        (tptr tuint)) tuint)
                                    (Ebinop Oadd (Etempvar _t tuint)
                                      (Etempvar _c tuint) tuint))
                                  (Ssequence
                                    (Sset _t
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                              (Tstruct _SHA256state_st noattr))
                                            _h (tarray tuint 8))
                                          (Econst_int (Int.repr 3) tint)
                                          (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                                (Tstruct _SHA256state_st noattr))
                                              _h (tarray tuint 8))
                                            (Econst_int (Int.repr 3) tint)
                                            (tptr tuint)) tuint)
                                        (Ebinop Oadd (Etempvar _t tuint)
                                          (Etempvar _d tuint) tuint))
                                      (Ssequence
                                        (Sset _t
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                                  (Tstruct _SHA256state_st noattr))
                                                _h (tarray tuint 8))
                                              (Econst_int (Int.repr 4) tint)
                                              (tptr tuint)) tuint))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                                    (Tstruct _SHA256state_st noattr))
                                                  _h (tarray tuint 8))
                                                (Econst_int (Int.repr 4) tint)
                                                (tptr tuint)) tuint)
                                            (Ebinop Oadd (Etempvar _t tuint)
                                              (Etempvar _e tuint) tuint))
                                          (Ssequence
                                            (Sset _t
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                                      (Tstruct _SHA256state_st noattr))
                                                    _h (tarray tuint 8))
                                                  (Econst_int (Int.repr 5) tint)
                                                  (tptr tuint)) tuint))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                                        (Tstruct _SHA256state_st noattr))
                                                      _h (tarray tuint 8))
                                                    (Econst_int (Int.repr 5) tint)
                                                    (tptr tuint)) tuint)
                                                (Ebinop Oadd
                                                  (Etempvar _t tuint)
                                                  (Etempvar _f tuint) tuint))
                                              (Ssequence
                                                (Sset _t
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                                          (Tstruct _SHA256state_st noattr))
                                                        _h (tarray tuint 8))
                                                      (Econst_int (Int.repr 6) tint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                                            (Tstruct _SHA256state_st noattr))
                                                          _h
                                                          (tarray tuint 8))
                                                        (Econst_int (Int.repr 6) tint)
                                                        (tptr tuint)) tuint)
                                                    (Ebinop Oadd
                                                      (Etempvar _t tuint)
                                                      (Etempvar _g tuint)
                                                      tuint))
                                                  (Ssequence
                                                    (Sset _t
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                                              (Tstruct _SHA256state_st noattr))
                                                            _h
                                                            (tarray tuint 8))
                                                          (Econst_int (Int.repr 7) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _ctx (tptr (Tstruct _SHA256state_st noattr)))
                                                                (Tstruct _SHA256state_st noattr))
                                                              _h
                                                              (tarray tuint 8))
                                                            (Econst_int (Int.repr 7) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Ebinop Oadd
                                                          (Etempvar _t tuint)
                                                          (Etempvar _h tuint)
                                                          tuint))
                                                      (Sreturn None))))))))))))))))))))))))))))
|}.

Definition f_SHA256_Init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _SHA256state_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
            (Tstruct _SHA256state_st noattr)) _h (tarray tuint 8))
        (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
    (Econst_int (Int.repr 1779033703) tuint))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
              (Tstruct _SHA256state_st noattr)) _h (tarray tuint 8))
          (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
      (Econst_int (Int.repr (-1150833019)) tuint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                (Tstruct _SHA256state_st noattr)) _h (tarray tuint 8))
            (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint)
        (Econst_int (Int.repr 1013904242) tuint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                  (Tstruct _SHA256state_st noattr)) _h (tarray tuint 8))
              (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint)
          (Econst_int (Int.repr (-1521486534)) tuint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                    (Tstruct _SHA256state_st noattr)) _h (tarray tuint 8))
                (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint)
            (Econst_int (Int.repr 1359893119) tuint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                      (Tstruct _SHA256state_st noattr)) _h (tarray tuint 8))
                  (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint)
              (Econst_int (Int.repr (-1694144372)) tuint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                        (Tstruct _SHA256state_st noattr)) _h
                      (tarray tuint 8)) (Econst_int (Int.repr 6) tint)
                    (tptr tuint)) tuint)
                (Econst_int (Int.repr 528734635) tuint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                          (Tstruct _SHA256state_st noattr)) _h
                        (tarray tuint 8)) (Econst_int (Int.repr 7) tint)
                      (tptr tuint)) tuint)
                  (Econst_int (Int.repr 1541459225) tuint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                        (Tstruct _SHA256state_st noattr)) _Nl tuint)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                          (Tstruct _SHA256state_st noattr)) _Nh tuint)
                      (Econst_int (Int.repr 0) tint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                          (Tstruct _SHA256state_st noattr)) _num tuint)
                      (Econst_int (Int.repr 0) tint))))))))))))
|}.

Definition f_SHA256_addlength := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _SHA256state_st noattr))) ::
                (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, tuint) :: (_cNl, tuint) :: (_cNh, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _cNl
    (Efield
      (Ederef (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
        (Tstruct _SHA256state_st noattr)) _Nl tuint))
  (Ssequence
    (Sset _cNh
      (Efield
        (Ederef (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
          (Tstruct _SHA256state_st noattr)) _Nh tuint))
    (Ssequence
      (Sset _l
        (Ebinop Oand
          (Ebinop Oadd (Etempvar _cNl tuint)
            (Ebinop Oshl (Ecast (Etempvar _len tuint) tuint)
              (Econst_int (Int.repr 3) tint) tuint) tuint)
          (Econst_int (Int.repr (-1)) tuint) tuint))
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _l tuint) (Etempvar _cNl tuint)
                       tint)
          (Sset _cNh
            (Ebinop Oadd (Etempvar _cNh tuint) (Econst_int (Int.repr 1) tint)
              tuint))
          Sskip)
        (Ssequence
          (Sset _cNh
            (Ebinop Oadd (Etempvar _cNh tuint)
              (Ebinop Oshr (Etempvar _len tuint)
                (Econst_int (Int.repr 29) tint) tuint) tuint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                  (Tstruct _SHA256state_st noattr)) _Nl tuint)
              (Etempvar _l tuint))
            (Sassign
              (Efield
                (Ederef (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                  (Tstruct _SHA256state_st noattr)) _Nh tuint)
              (Etempvar _cNh tuint))))))))
|}.

Definition f_SHA256_Update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct _SHA256state_st noattr))) ::
                (_data_, (tptr tvoid)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_data, (tptr tuchar)) :: (_p, (tptr tuchar)) ::
               (_n, tuint) :: (_fragment, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _data (Etempvar _data_ (tptr tvoid)))
  (Ssequence
    (Scall None
      (Evar _SHA256_addlength (Tfunction
                                ((tptr (Tstruct _SHA256state_st noattr)) ::
                                 tuint :: nil) tvoid cc_default))
      ((Etempvar _c (tptr (Tstruct _SHA256state_st noattr))) ::
       (Etempvar _len tuint) :: nil))
    (Ssequence
      (Sset _n
        (Efield
          (Ederef (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
            (Tstruct _SHA256state_st noattr)) _num tuint))
      (Ssequence
        (Sset _p
          (Efield
            (Ederef (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
              (Tstruct _SHA256state_st noattr)) _data (tarray tuchar 64)))
        (Ssequence
          (Sifthenelse (Ebinop One (Etempvar _n tuint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _fragment
                (Ebinop Osub
                  (Ebinop Omul (Econst_int (Int.repr 16) tint)
                    (Econst_int (Int.repr 4) tint) tint) (Etempvar _n tuint)
                  tuint))
              (Sifthenelse (Ebinop Oge (Etempvar _len tuint)
                             (Etempvar _fragment tuint) tint)
                (Ssequence
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    ((tptr tvoid) :: (tptr tvoid) :: tuint ::
                                     nil) (tptr tvoid) cc_default))
                    ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                       (Etempvar _n tuint) (tptr tuchar)) ::
                     (Etempvar _data (tptr tuchar)) ::
                     (Etempvar _fragment tuint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _sha256_block_data_order (Tfunction
                                                       ((tptr (Tstruct _SHA256state_st noattr)) ::
                                                        (tptr tvoid) :: nil)
                                                       tvoid cc_default))
                      ((Etempvar _c (tptr (Tstruct _SHA256state_st noattr))) ::
                       (Etempvar _p (tptr tuchar)) :: nil))
                    (Ssequence
                      (Sset _data
                        (Ebinop Oadd (Etempvar _data (tptr tuchar))
                          (Etempvar _fragment tuint) (tptr tuchar)))
                      (Ssequence
                        (Sset _len
                          (Ebinop Osub (Etempvar _len tuint)
                            (Etempvar _fragment tuint) tuint))
                        (Scall None
                          (Evar _memset (Tfunction
                                          ((tptr tvoid) :: tint :: tuint ::
                                           nil) (tptr tvoid) cc_default))
                          ((Etempvar _p (tptr tuchar)) ::
                           (Econst_int (Int.repr 0) tint) ::
                           (Ebinop Omul (Econst_int (Int.repr 16) tint)
                             (Econst_int (Int.repr 4) tint) tint) :: nil))))))
                (Ssequence
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    ((tptr tvoid) :: (tptr tvoid) :: tuint ::
                                     nil) (tptr tvoid) cc_default))
                    ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                       (Etempvar _n tuint) (tptr tuchar)) ::
                     (Etempvar _data (tptr tuchar)) ::
                     (Etempvar _len tuint) :: nil))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                          (Tstruct _SHA256state_st noattr)) _num tuint)
                      (Ebinop Oadd (Etempvar _n tuint)
                        (Ecast (Etempvar _len tuint) tuint) tuint))
                    (Sreturn None)))))
            Sskip)
          (Ssequence
            (Swhile
              (Ebinop Oge (Etempvar _len tuint)
                (Ebinop Omul (Econst_int (Int.repr 16) tint)
                  (Econst_int (Int.repr 4) tint) tint) tint)
              (Ssequence
                (Scall None
                  (Evar _sha256_block_data_order (Tfunction
                                                   ((tptr (Tstruct _SHA256state_st noattr)) ::
                                                    (tptr tvoid) :: nil)
                                                   tvoid cc_default))
                  ((Etempvar _c (tptr (Tstruct _SHA256state_st noattr))) ::
                   (Etempvar _data (tptr tuchar)) :: nil))
                (Ssequence
                  (Sset _data
                    (Ebinop Oadd (Etempvar _data (tptr tuchar))
                      (Ebinop Omul (Econst_int (Int.repr 16) tint)
                        (Econst_int (Int.repr 4) tint) tint) (tptr tuchar)))
                  (Sset _len
                    (Ebinop Osub (Etempvar _len tuint)
                      (Ebinop Omul (Econst_int (Int.repr 16) tint)
                        (Econst_int (Int.repr 4) tint) tint) tuint)))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                    (Tstruct _SHA256state_st noattr)) _num tuint)
                (Etempvar _len tuint))
              (Ssequence
                (Sifthenelse (Ebinop One (Etempvar _len tuint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    ((tptr tvoid) :: (tptr tvoid) :: tuint ::
                                     nil) (tptr tvoid) cc_default))
                    ((Etempvar _p (tptr tuchar)) ::
                     (Etempvar _data (tptr tuchar)) ::
                     (Etempvar _len tuint) :: nil))
                  Sskip)
                (Sreturn None)))))))))
|}.

Definition f_SHA256_Final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_md, (tptr tuchar)) ::
                (_c, (tptr (Tstruct _SHA256state_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tuchar)) :: (_n, tuint) :: (_cNl, tuint) ::
               (_cNh, tuint) :: (_ll, tuint) :: (_xn, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Efield
      (Ederef (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
        (Tstruct _SHA256state_st noattr)) _data (tarray tuchar 64)))
  (Ssequence
    (Sset _n
      (Efield
        (Ederef (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
          (Tstruct _SHA256state_st noattr)) _num tuint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _n tuint)
            (tptr tuchar)) tuchar) (Econst_int (Int.repr 128) tint))
      (Ssequence
        (Sset _n
          (Ebinop Oadd (Etempvar _n tuint) (Econst_int (Int.repr 1) tint)
            tuint))
        (Ssequence
          (Sifthenelse (Ebinop Ogt (Etempvar _n tuint)
                         (Ebinop Osub
                           (Ebinop Omul (Econst_int (Int.repr 16) tint)
                             (Econst_int (Int.repr 4) tint) tint)
                           (Econst_int (Int.repr 8) tint) tint) tint)
            (Ssequence
              (Scall None
                (Evar _memset (Tfunction
                                ((tptr tvoid) :: tint :: tuint :: nil)
                                (tptr tvoid) cc_default))
                ((Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _n tuint)
                   (tptr tuchar)) :: (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Osub
                   (Ebinop Omul (Econst_int (Int.repr 16) tint)
                     (Econst_int (Int.repr 4) tint) tint) (Etempvar _n tuint)
                   tuint) :: nil))
              (Ssequence
                (Sset _n (Econst_int (Int.repr 0) tint))
                (Scall None
                  (Evar _sha256_block_data_order (Tfunction
                                                   ((tptr (Tstruct _SHA256state_st noattr)) ::
                                                    (tptr tvoid) :: nil)
                                                   tvoid cc_default))
                  ((Etempvar _c (tptr (Tstruct _SHA256state_st noattr))) ::
                   (Etempvar _p (tptr tuchar)) :: nil))))
            Sskip)
          (Ssequence
            (Scall None
              (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tuint :: nil)
                              (tptr tvoid) cc_default))
              ((Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _n tuint)
                 (tptr tuchar)) :: (Econst_int (Int.repr 0) tint) ::
               (Ebinop Osub
                 (Ebinop Osub
                   (Ebinop Omul (Econst_int (Int.repr 16) tint)
                     (Econst_int (Int.repr 4) tint) tint)
                   (Econst_int (Int.repr 8) tint) tint) (Etempvar _n tuint)
                 tuint) :: nil))
            (Ssequence
              (Sset _p
                (Ebinop Oadd (Etempvar _p (tptr tuchar))
                  (Ebinop Osub
                    (Ebinop Omul (Econst_int (Int.repr 16) tint)
                      (Econst_int (Int.repr 4) tint) tint)
                    (Econst_int (Int.repr 8) tint) tint) (tptr tuchar)))
              (Ssequence
                (Sset _cNh
                  (Efield
                    (Ederef
                      (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                      (Tstruct _SHA256state_st noattr)) _Nh tuint))
                (Ssequence
                  (Ssequence
                    (Scall None
                      (Evar ___builtin_write32_reversed (Tfunction
                                                          ((tptr tuint) ::
                                                           tuint :: nil)
                                                          tvoid cc_default))
                      ((Ecast (Etempvar _p (tptr tuchar)) (tptr tuint)) ::
                       (Etempvar _cNh tuint) :: nil))
                    (Sset _p
                      (Ebinop Oadd (Etempvar _p (tptr tuchar))
                        (Econst_int (Int.repr 4) tint) (tptr tuchar))))
                  (Ssequence
                    (Sset _cNl
                      (Efield
                        (Ederef
                          (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                          (Tstruct _SHA256state_st noattr)) _Nl tuint))
                    (Ssequence
                      (Ssequence
                        (Scall None
                          (Evar ___builtin_write32_reversed (Tfunction
                                                              ((tptr tuint) ::
                                                               tuint :: nil)
                                                              tvoid
                                                              cc_default))
                          ((Ecast (Etempvar _p (tptr tuchar)) (tptr tuint)) ::
                           (Etempvar _cNl tuint) :: nil))
                        (Sset _p
                          (Ebinop Oadd (Etempvar _p (tptr tuchar))
                            (Econst_int (Int.repr 4) tint) (tptr tuchar))))
                      (Ssequence
                        (Sset _p
                          (Ebinop Osub (Etempvar _p (tptr tuchar))
                            (Ebinop Omul (Econst_int (Int.repr 16) tint)
                              (Econst_int (Int.repr 4) tint) tint)
                            (tptr tuchar)))
                        (Ssequence
                          (Scall None
                            (Evar _sha256_block_data_order (Tfunction
                                                             ((tptr (Tstruct _SHA256state_st noattr)) ::
                                                              (tptr tvoid) ::
                                                              nil) tvoid
                                                             cc_default))
                            ((Etempvar _c (tptr (Tstruct _SHA256state_st noattr))) ::
                             (Etempvar _p (tptr tuchar)) :: nil))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                                  (Tstruct _SHA256state_st noattr)) _num
                                tuint) (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Scall None
                                (Evar _memset (Tfunction
                                                ((tptr tvoid) :: tint ::
                                                 tuint :: nil) (tptr tvoid)
                                                cc_default))
                                ((Etempvar _p (tptr tuchar)) ::
                                 (Econst_int (Int.repr 0) tint) ::
                                 (Ebinop Omul (Econst_int (Int.repr 16) tint)
                                   (Econst_int (Int.repr 4) tint) tint) ::
                                 nil))
                              (Ssequence
                                (Ssequence
                                  (Sset _xn (Econst_int (Int.repr 0) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _xn tuint)
                                                     (Ebinop Odiv
                                                       (Econst_int (Int.repr 32) tint)
                                                       (Econst_int (Int.repr 4) tint)
                                                       tint) tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Sset _ll
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _c (tptr (Tstruct _SHA256state_st noattr)))
                                                  (Tstruct _SHA256state_st noattr))
                                                _h (tarray tuint 8))
                                              (Etempvar _xn tuint)
                                              (tptr tuint)) tuint))
                                        (Ssequence
                                          (Scall None
                                            (Evar ___builtin_write32_reversed 
                                            (Tfunction
                                              ((tptr tuint) :: tuint :: nil)
                                              tvoid cc_default))
                                            ((Ecast
                                               (Etempvar _md (tptr tuchar))
                                               (tptr tuint)) ::
                                             (Etempvar _ll tuint) :: nil))
                                          (Sset _md
                                            (Ebinop Oadd
                                              (Etempvar _md (tptr tuchar))
                                              (Econst_int (Int.repr 4) tint)
                                              (tptr tuchar))))))
                                    (Sset _xn
                                      (Ebinop Oadd (Etempvar _xn tuint)
                                        (Econst_int (Int.repr 1) tint) tuint))))
                                (Sreturn None)))))))))))))))))
|}.

Definition f_SHA256 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_d, (tptr tuchar)) :: (_n, tuint) :: (_md, (tptr tuchar)) ::
                nil);
  fn_vars := ((_c, (Tstruct _SHA256state_st noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _SHA256_Init (Tfunction
                         ((tptr (Tstruct _SHA256state_st noattr)) :: nil)
                         tvoid cc_default))
    ((Eaddrof (Evar _c (Tstruct _SHA256state_st noattr))
       (tptr (Tstruct _SHA256state_st noattr))) :: nil))
  (Ssequence
    (Scall None
      (Evar _SHA256_Update (Tfunction
                             ((tptr (Tstruct _SHA256state_st noattr)) ::
                              (tptr tvoid) :: tuint :: nil) tvoid cc_default))
      ((Eaddrof (Evar _c (Tstruct _SHA256state_st noattr))
         (tptr (Tstruct _SHA256state_st noattr))) ::
       (Etempvar _d (tptr tuchar)) :: (Etempvar _n tuint) :: nil))
    (Scall None
      (Evar _SHA256_Final (Tfunction
                            ((tptr tuchar) ::
                             (tptr (Tstruct _SHA256state_st noattr)) :: nil)
                            tvoid cc_default))
      ((Etempvar _md (tptr tuchar)) ::
       (Eaddrof (Evar _c (Tstruct _SHA256state_st noattr))
         (tptr (Tstruct _SHA256state_st noattr))) :: nil))))
|}.

Definition composites : list composite_definition :=
(Composite _SHA256state_st Struct
   (Member_plain _h (tarray tuint 8) :: Member_plain _Nl tuint ::
    Member_plain _Nh tuint :: Member_plain _data (tarray tuchar 64) ::
    Member_plain _num tuint :: nil)
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
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
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
 (_K256, Gvar v_K256) ::
 (_sha256_block_data_order, Gfun(Internal f_sha256_block_data_order)) ::
 (_SHA256_Init, Gfun(Internal f_SHA256_Init)) ::
 (_SHA256_addlength, Gfun(Internal f_SHA256_addlength)) ::
 (_SHA256_Update, Gfun(Internal f_SHA256_Update)) ::
 (_SHA256_Final, Gfun(Internal f_SHA256_Final)) ::
 (_SHA256, Gfun(Internal f_SHA256)) :: nil).

Definition public_idents : list ident :=
(_SHA256 :: _SHA256_Final :: _SHA256_Update :: _SHA256_addlength ::
 _SHA256_Init :: _sha256_block_data_order :: _memset :: _memcpy ::
 ___builtin_write32_reversed :: ___builtin_read32_reversed ::
 ___builtin_debug :: ___builtin_write16_reversed ::
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


