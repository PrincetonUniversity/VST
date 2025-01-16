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
  Definition source_file := "progs/string.c".
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := 1%positive.
Definition ___builtin_annot : ident := 18%positive.
Definition ___builtin_annot_intval : ident := 19%positive.
Definition ___builtin_bswap : ident := 3%positive.
Definition ___builtin_bswap16 : ident := 5%positive.
Definition ___builtin_bswap32 : ident := 4%positive.
Definition ___builtin_bswap64 : ident := 2%positive.
Definition ___builtin_clz : ident := 6%positive.
Definition ___builtin_clzl : ident := 7%positive.
Definition ___builtin_clzll : ident := 8%positive.
Definition ___builtin_ctz : ident := 9%positive.
Definition ___builtin_ctzl : ident := 10%positive.
Definition ___builtin_ctzll : ident := 11%positive.
Definition ___builtin_debug : ident := 37%positive.
Definition ___builtin_expect : ident := 26%positive.
Definition ___builtin_fabs : ident := 12%positive.
Definition ___builtin_fabsf : ident := 13%positive.
Definition ___builtin_fmadd : ident := 29%positive.
Definition ___builtin_fmax : ident := 27%positive.
Definition ___builtin_fmin : ident := 28%positive.
Definition ___builtin_fmsub : ident := 30%positive.
Definition ___builtin_fnmadd : ident := 31%positive.
Definition ___builtin_fnmsub : ident := 32%positive.
Definition ___builtin_fsqrt : ident := 14%positive.
Definition ___builtin_membar : ident := 20%positive.
Definition ___builtin_memcpy_aligned : ident := 16%positive.
Definition ___builtin_read16_reversed : ident := 33%positive.
Definition ___builtin_read32_reversed : ident := 34%positive.
Definition ___builtin_sel : ident := 17%positive.
Definition ___builtin_sqrt : ident := 15%positive.
Definition ___builtin_unreachable : ident := 25%positive.
Definition ___builtin_va_arg : ident := 22%positive.
Definition ___builtin_va_copy : ident := 23%positive.
Definition ___builtin_va_end : ident := 24%positive.
Definition ___builtin_va_start : ident := 21%positive.
Definition ___builtin_write16_reversed : ident := 35%positive.
Definition ___builtin_write32_reversed : ident := 36%positive.
Definition ___compcert_i64_dtos : ident := 51%positive.
Definition ___compcert_i64_dtou : ident := 52%positive.
Definition ___compcert_i64_sar : ident := 63%positive.
Definition ___compcert_i64_sdiv : ident := 57%positive.
Definition ___compcert_i64_shl : ident := 61%positive.
Definition ___compcert_i64_shr : ident := 62%positive.
Definition ___compcert_i64_smod : ident := 59%positive.
Definition ___compcert_i64_smulh : ident := 64%positive.
Definition ___compcert_i64_stod : ident := 53%positive.
Definition ___compcert_i64_stof : ident := 55%positive.
Definition ___compcert_i64_udiv : ident := 58%positive.
Definition ___compcert_i64_umod : ident := 60%positive.
Definition ___compcert_i64_umulh : ident := 65%positive.
Definition ___compcert_i64_utod : ident := 54%positive.
Definition ___compcert_i64_utof : ident := 56%positive.
Definition ___compcert_va_composite : ident := 50%positive.
Definition ___compcert_va_float64 : ident := 49%positive.
Definition ___compcert_va_int32 : ident := 47%positive.
Definition ___compcert_va_int64 : ident := 48%positive.
Definition _i : ident := 43%positive.
Definition _j : ident := 44%positive.
Definition _main : ident := 66%positive.
Definition _mallocN : ident := 38%positive.
Definition _n1 : ident := 41%positive.
Definition _n2 : ident := 42%positive.
Definition _next : ident := 45%positive.
Definition _s1 : ident := 39%positive.
Definition _s2 : ident := 40%positive.
Definition _strcspn_kmp : ident := 46%positive.
Definition _t'1 : ident := 67%positive.
Definition _t'2 : ident := 68%positive.
Definition _t'3 : ident := 69%positive.
Definition _t'4 : ident := 70%positive.
Definition _t'5 : ident := 71%positive.

Definition f_strcspn_kmp := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s1, (tptr tschar)) :: (_s2, (tptr tschar)) ::
                (_n1, tint) :: (_n2, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_j, tint) :: (_next, (tptr tint)) ::
               (_t'1, (tptr tvoid)) :: (_t'5, tschar) :: (_t'4, tschar) ::
               (_t'3, tschar) :: (_t'2, tschar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (tint :: nil) (tptr tvoid) cc_default))
      ((Ebinop Omul (Etempvar _n2 tint) (Esizeof tint tuint) tuint) :: nil))
    (Sset _next (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tint))))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _j (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _next (tptr tint))
              (Econst_int (Int.repr 0) tint) (tptr tint)) tint)
          (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
        (Ssequence
          (Swhile
            (Ebinop Olt (Etempvar _i tint) (Etempvar _n2 tint) tint)
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd (Etempvar _s2 (tptr tschar))
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint) (tptr tschar))
                  tschar))
              (Ssequence
                (Sset _t'5
                  (Ederef
                    (Ebinop Oadd (Etempvar _s2 (tptr tschar))
                      (Ebinop Oadd (Etempvar _j tint)
                        (Econst_int (Int.repr 1) tint) tint) (tptr tschar))
                    tschar))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tschar)
                               (Etempvar _t'5 tschar) tint)
                  (Ssequence
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint))
                    (Ssequence
                      (Sset _j
                        (Ebinop Oadd (Etempvar _j tint)
                          (Econst_int (Int.repr 1) tint) tint))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _next (tptr tint))
                            (Etempvar _i tint) (tptr tint)) tint)
                        (Etempvar _j tint))))
                  (Sifthenelse (Ebinop Oeq (Etempvar _j tint)
                                 (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                   tint) tint)
                    (Ssequence
                      (Sset _i
                        (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 1) tint) tint))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _next (tptr tint))
                            (Etempvar _i tint) (tptr tint)) tint)
                        (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
                    (Sset _j
                      (Ederef
                        (Ebinop Oadd (Etempvar _next (tptr tint))
                          (Etempvar _j tint) (tptr tint)) tint)))))))
          (Ssequence
            (Sset _i (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
            (Ssequence
              (Sset _j (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
              (Ssequence
                (Swhile
                  (Ebinop Olt (Etempvar _i tint) (Etempvar _n1 tint) tint)
                  (Ssequence
                    (Sset _t'2
                      (Ederef
                        (Ebinop Oadd (Etempvar _s1 (tptr tschar))
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint)
                          (tptr tschar)) tschar))
                    (Ssequence
                      (Sset _t'3
                        (Ederef
                          (Ebinop Oadd (Etempvar _s2 (tptr tschar))
                            (Ebinop Oadd (Etempvar _j tint)
                              (Econst_int (Int.repr 1) tint) tint)
                            (tptr tschar)) tschar))
                      (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tschar)
                                     (Etempvar _t'3 tschar) tint)
                        (Ssequence
                          (Sset _i
                            (Ebinop Oadd (Etempvar _i tint)
                              (Econst_int (Int.repr 1) tint) tint))
                          (Ssequence
                            (Sset _j
                              (Ebinop Oadd (Etempvar _j tint)
                                (Econst_int (Int.repr 1) tint) tint))
                            (Sifthenelse (Ebinop Oeq (Etempvar _j tint)
                                           (Ebinop Osub (Etempvar _n2 tint)
                                             (Econst_int (Int.repr 1) tint)
                                             tint) tint)
                              (Sreturn (Some (Ebinop Oadd
                                               (Ebinop Osub
                                                 (Etempvar _i tint)
                                                 (Etempvar _n2 tint) tint)
                                               (Econst_int (Int.repr 1) tint)
                                               tint)))
                              Sskip)))
                        (Sifthenelse (Ebinop Oeq (Etempvar _j tint)
                                       (Eunop Oneg
                                         (Econst_int (Int.repr 1) tint) tint)
                                       tint)
                          (Sset _i
                            (Ebinop Oadd (Etempvar _i tint)
                              (Econst_int (Int.repr 1) tint) tint))
                          (Sset _j
                            (Ederef
                              (Ebinop Oadd (Etempvar _next (tptr tint))
                                (Etempvar _j tint) (tptr tint)) tint)))))))
                (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                 tint)))))))))))
|}.

Definition composites : list composite_definition :=
nil.

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
 (_mallocN,
   Gfun(External (EF_external "mallocN"
                   (mksignature (AST.Xint :: nil) AST.Xptr cc_default))
     (tint :: nil) (tptr tvoid) cc_default)) ::
 (_strcspn_kmp, Gfun(Internal f_strcspn_kmp)) :: nil).

Definition public_idents : list ident :=
(_strcspn_kmp :: _mallocN :: ___builtin_debug ::
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


