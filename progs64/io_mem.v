From Stdlib Require Import String List ZArith.
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
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "progs64/io_mem.c".
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 17%positive.
Definition ___builtin_annot_intval : ident := 18%positive.
Definition ___builtin_bswap : ident := 2%positive.
Definition ___builtin_bswap16 : ident := 4%positive.
Definition ___builtin_bswap32 : ident := 3%positive.
Definition ___builtin_bswap64 : ident := 1%positive.
Definition ___builtin_cls : ident := 26%positive.
Definition ___builtin_clsl : ident := 27%positive.
Definition ___builtin_clsll : ident := 28%positive.
Definition ___builtin_clz : ident := 5%positive.
Definition ___builtin_clzl : ident := 6%positive.
Definition ___builtin_clzll : ident := 7%positive.
Definition ___builtin_ctz : ident := 8%positive.
Definition ___builtin_ctzl : ident := 9%positive.
Definition ___builtin_ctzll : ident := 10%positive.
Definition ___builtin_debug : ident := 35%positive.
Definition ___builtin_expect : ident := 25%positive.
Definition ___builtin_fabs : ident := 11%positive.
Definition ___builtin_fabsf : ident := 12%positive.
Definition ___builtin_fmadd : ident := 29%positive.
Definition ___builtin_fmax : ident := 33%positive.
Definition ___builtin_fmin : ident := 34%positive.
Definition ___builtin_fmsub : ident := 30%positive.
Definition ___builtin_fnmadd : ident := 31%positive.
Definition ___builtin_fnmsub : ident := 32%positive.
Definition ___builtin_fsqrt : ident := 13%positive.
Definition ___builtin_membar : ident := 19%positive.
Definition ___builtin_memcpy_aligned : ident := 15%positive.
Definition ___builtin_sel : ident := 16%positive.
Definition ___builtin_sqrt : ident := 14%positive.
Definition ___builtin_unreachable : ident := 24%positive.
Definition ___builtin_va_arg : ident := 21%positive.
Definition ___builtin_va_copy : ident := 22%positive.
Definition ___builtin_va_end : ident := 23%positive.
Definition ___builtin_va_start : ident := 20%positive.
Definition ___compcert_i64_dtos : ident := 57%positive.
Definition ___compcert_i64_dtou : ident := 58%positive.
Definition ___compcert_i64_sar : ident := 69%positive.
Definition ___compcert_i64_sdiv : ident := 63%positive.
Definition ___compcert_i64_shl : ident := 67%positive.
Definition ___compcert_i64_shr : ident := 68%positive.
Definition ___compcert_i64_smod : ident := 65%positive.
Definition ___compcert_i64_smulh : ident := 70%positive.
Definition ___compcert_i64_stod : ident := 59%positive.
Definition ___compcert_i64_stof : ident := 61%positive.
Definition ___compcert_i64_udiv : ident := 64%positive.
Definition ___compcert_i64_umod : ident := 66%positive.
Definition ___compcert_i64_umulh : ident := 71%positive.
Definition ___compcert_i64_utod : ident := 60%positive.
Definition ___compcert_i64_utof : ident := 62%positive.
Definition ___compcert_va_composite : ident := 56%positive.
Definition ___compcert_va_float64 : ident := 55%positive.
Definition ___compcert_va_int32 : ident := 53%positive.
Definition ___compcert_va_int64 : ident := 54%positive.
Definition _buf : ident := 42%positive.
Definition _c : ident := 50%positive.
Definition _d : ident := 49%positive.
Definition _exit : ident := 38%positive.
Definition _free : ident := 37%positive.
Definition _getchars : ident := 39%positive.
Definition _i : ident := 41%positive.
Definition _j : ident := 51%positive.
Definition _k : ident := 45%positive.
Definition _main : ident := 52%positive.
Definition _malloc : ident := 36%positive.
Definition _n : ident := 48%positive.
Definition _print_int : ident := 47%positive.
Definition _print_intr : ident := 46%positive.
Definition _putchars : ident := 40%positive.
Definition _q : ident := 43%positive.
Definition _r : ident := 44%positive.
Definition _t'1 : ident := 72%positive.
Definition _t'2 : ident := 73%positive.
Definition _t'3 : ident := 74%positive.
Definition _t'4 : ident := 75%positive.

Definition f_print_intr := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_i, tuint) :: (_buf, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_q, tuint) :: (_r, tuchar) :: (_k, tint) :: (_t'1, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _k (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _i tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Ssequence
        (Sset _q
          (Ebinop Odiv (Etempvar _i tuint) (Econst_int (Int.repr 10) tuint)
            tuint))
        (Ssequence
          (Sset _r
            (Ecast
              (Ebinop Omod (Etempvar _i tuint)
                (Econst_int (Int.repr 10) tuint) tuint) tuchar))
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _print_intr (Tfunction (tuint :: (tptr tuchar) :: nil)
                                    tint cc_default))
                ((Etempvar _q tuint) :: (Etempvar _buf (tptr tuchar)) :: nil))
              (Sset _k (Etempvar _t'1 tint)))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _buf (tptr tuchar)) (Etempvar _k tint)
                  (tptr tuchar)) tuchar)
              (Ebinop Oadd (Etempvar _r tuchar)
                (Econst_int (Int.repr 48) tint) tint)))))
      Sskip)
    (Sreturn (Some (Ebinop Oadd (Etempvar _k tint)
                     (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_print_int := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_i, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_buf, (tptr tuchar)) :: (_k, tint) :: (_t'2, tint) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (tulong :: nil) (tptr tvoid) cc_default))
      ((Econst_int (Int.repr 5) tint) :: nil))
    (Sset _buf (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _buf (tptr tuchar)) tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _i tuint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _buf (tptr tuchar))
                (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
            (Econst_int (Int.repr 48) tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _buf (tptr tuchar))
                  (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
              (Econst_int (Int.repr 10) tint))
            (Sset _k (Econst_int (Int.repr 2) tint))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _print_intr (Tfunction (tuint :: (tptr tuchar) :: nil)
                                  tint cc_default))
              ((Etempvar _i tuint) :: (Etempvar _buf (tptr tuchar)) :: nil))
            (Sset _k (Etempvar _t'2 tint)))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _buf (tptr tuchar)) (Etempvar _k tint)
                  (tptr tuchar)) tuchar) (Econst_int (Int.repr 10) tint))
            (Sset _k
              (Ebinop Oadd (Etempvar _k tint) (Econst_int (Int.repr 1) tint)
                tint)))))
      (Ssequence
        (Scall None
          (Evar _putchars (Tfunction ((tptr tuchar) :: tint :: nil) tint
                            cc_default))
          ((Etempvar _buf (tptr tuchar)) :: (Etempvar _k tint) :: nil))
        (Scall None
          (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
          ((Etempvar _buf (tptr tuchar)) :: nil))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_n, tuint) :: (_d, tuint) :: (_c, tuchar) ::
               (_buf, (tptr tuchar)) :: (_i, tint) :: (_j, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, (tptr tvoid)) ::
               (_t'4, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _n (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _malloc (Tfunction (tulong :: nil) (tptr tvoid) cc_default))
          ((Econst_int (Int.repr 4) tint) :: nil))
        (Sset _buf (Etempvar _t'1 (tptr tvoid))))
      (Ssequence
        (Sifthenelse (Eunop Onotbool (Etempvar _buf (tptr tuchar)) tint)
          (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil))
          Sskip)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _getchars (Tfunction ((tptr tuchar) :: tint :: nil) tint
                                cc_default))
              ((Etempvar _buf (tptr tuchar)) ::
               (Econst_int (Int.repr 4) tint) :: nil))
            (Sset _i (Etempvar _t'2 tint)))
          (Ssequence
            (Swhile
              (Ebinop Olt (Etempvar _n tuint)
                (Econst_int (Int.repr 1000) tint) tint)
              (Ssequence
                (Ssequence
                  (Sset _j (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                     (Etempvar _i tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Ssequence
                          (Sset _t'4
                            (Ederef
                              (Ebinop Oadd (Etempvar _buf (tptr tuchar))
                                (Etempvar _j tint) (tptr tuchar)) tuchar))
                          (Sset _c (Ecast (Etempvar _t'4 tuchar) tuchar)))
                        (Ssequence
                          (Sset _d
                            (Ebinop Osub (Ecast (Etempvar _c tuchar) tuint)
                              (Ecast (Econst_int (Int.repr 48) tint) tuint)
                              tuint))
                          (Ssequence
                            (Sifthenelse (Ebinop Oge (Etempvar _d tuint)
                                           (Econst_int (Int.repr 10) tint)
                                           tint)
                              (Ssequence
                                (Scall None
                                  (Evar _free (Tfunction
                                                ((tptr tvoid) :: nil) tvoid
                                                cc_default))
                                  ((Etempvar _buf (tptr tuchar)) :: nil))
                                (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                              Sskip)
                            (Ssequence
                              (Sset _n
                                (Ebinop Oadd (Etempvar _n tuint)
                                  (Etempvar _d tuint) tuint))
                              (Scall None
                                (Evar _print_int (Tfunction (tuint :: nil)
                                                   tvoid cc_default))
                                ((Etempvar _n tuint) :: nil)))))))
                    (Sset _j
                      (Ebinop Oadd (Etempvar _j tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _getchars (Tfunction ((tptr tuchar) :: tint :: nil)
                                      tint cc_default))
                    ((Etempvar _buf (tptr tuchar)) ::
                     (Econst_int (Int.repr 4) tint) :: nil))
                  (Sset _i (Etempvar _t'3 tint)))))
            (Ssequence
              (Scall None
                (Evar _free (Tfunction ((tptr tvoid) :: nil) tvoid
                              cc_default))
                ((Etempvar _buf (tptr tuchar)) :: nil))
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
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
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
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
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
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
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
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
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
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
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tint :: nil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tlong :: nil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tlong :: nil) tint cc_default)) ::
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
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc, Gfun(External EF_malloc (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
 (_getchars,
   Gfun(External (EF_external "getchars"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tuchar) :: tint :: nil) tint
     cc_default)) ::
 (_putchars,
   Gfun(External (EF_external "putchars"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tuchar) :: tint :: nil) tint
     cc_default)) :: (_print_intr, Gfun(Internal f_print_intr)) ::
 (_print_int, Gfun(Internal f_print_int)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _print_int :: _print_intr :: _putchars :: _getchars :: _exit ::
 _free :: _malloc :: ___builtin_debug :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_clsll ::
 ___builtin_clsl :: ___builtin_cls :: ___builtin_expect ::
 ___builtin_unreachable :: ___builtin_va_end :: ___builtin_va_copy ::
 ___builtin_va_arg :: ___builtin_va_start :: ___builtin_membar ::
 ___builtin_annot_intval :: ___builtin_annot :: ___builtin_sel ::
 ___builtin_memcpy_aligned :: ___builtin_sqrt :: ___builtin_fsqrt ::
 ___builtin_fabsf :: ___builtin_fabs :: ___builtin_ctzll ::
 ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll :: ___builtin_clzl ::
 ___builtin_clz :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_bswap64 :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


