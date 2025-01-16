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
  Definition source_file := "progs/fib.c".
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
Definition ___compcert_i64_dtos : ident := 58%positive.
Definition ___compcert_i64_dtou : ident := 59%positive.
Definition ___compcert_i64_sar : ident := 70%positive.
Definition ___compcert_i64_sdiv : ident := 64%positive.
Definition ___compcert_i64_shl : ident := 68%positive.
Definition ___compcert_i64_shr : ident := 69%positive.
Definition ___compcert_i64_smod : ident := 66%positive.
Definition ___compcert_i64_smulh : ident := 71%positive.
Definition ___compcert_i64_stod : ident := 60%positive.
Definition ___compcert_i64_stof : ident := 62%positive.
Definition ___compcert_i64_udiv : ident := 65%positive.
Definition ___compcert_i64_umod : ident := 67%positive.
Definition ___compcert_i64_umulh : ident := 72%positive.
Definition ___compcert_i64_utod : ident := 61%positive.
Definition ___compcert_i64_utof : ident := 63%positive.
Definition ___compcert_va_composite : ident := 57%positive.
Definition ___compcert_va_float64 : ident := 56%positive.
Definition ___compcert_va_int32 : ident := 54%positive.
Definition ___compcert_va_int64 : ident := 55%positive.
Definition _a : ident := 50%positive.
Definition _a0 : ident := 39%positive.
Definition _a1 : ident := 40%positive.
Definition _a2 : ident := 41%positive.
Definition _b : ident := 51%positive.
Definition _fib_loop : ident := 43%positive.
Definition _fib_loop_mod : ident := 46%positive.
Definition _fib_loop_save_var : ident := 44%positive.
Definition _fib_rec : ident := 47%positive.
Definition _i : ident := 42%positive.
Definition _main : ident := 53%positive.
Definition _mod : ident := 45%positive.
Definition _n : ident := 38%positive.
Definition _swap_int : ident := 52%positive.
Definition _x : ident := 48%positive.
Definition _y : ident := 49%positive.
Definition _t'1 : ident := 73%positive.
Definition _t'2 : ident := 74%positive.

Definition f_fib_loop := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_a0, tint) :: (_a1, tint) :: (_a2, tint) :: (_i, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _a0 (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _a1 (Econst_int (Int.repr 1) tint))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _n tint)
                           tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _a2
                (Ebinop Oadd (Etempvar _a0 tint) (Etempvar _a1 tint) tint))
              (Ssequence
                (Sset _a0 (Etempvar _a1 tint))
                (Sset _a1 (Etempvar _a2 tint)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Sreturn (Some (Etempvar _a0 tint))))))
|}.

Definition f_fib_loop_save_var := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_a0, tint) :: (_a1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _a0 (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _a1 (Econst_int (Int.repr 1) tint))
    (Ssequence
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Ogt (Etempvar _n tint)
                         (Econst_int (Int.repr 0) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _a1
              (Ebinop Oadd (Etempvar _a0 tint) (Etempvar _a1 tint) tint))
            (Sset _a0
              (Ebinop Osub (Etempvar _a1 tint) (Etempvar _a0 tint) tint))))
        (Sset _n
          (Ebinop Osub (Etempvar _n tint) (Econst_int (Int.repr 1) tint)
            tint)))
      (Sreturn (Some (Etempvar _a0 tint))))))
|}.

Definition f_fib_loop_mod := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_n, tint) :: (_mod, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_a0, tint) :: (_a1, tint) :: (_a2, tint) :: (_i, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _a0 (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _a1 (Econst_int (Int.repr 1) tint))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar _n tint)
                           tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _a2
                (Ebinop Omod
                  (Ebinop Oadd (Etempvar _a0 tint) (Etempvar _a1 tint) tint)
                  (Etempvar _mod tint) tint))
              (Ssequence
                (Sset _a0 (Etempvar _a1 tint))
                (Sset _a1 (Etempvar _a2 tint)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Sreturn (Some (Etempvar _a0 tint))))))
|}.

Definition f_fib_rec := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _n tint) (Econst_int (Int.repr 0) tint)
                 tint)
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _n tint)
                   (Econst_int (Int.repr 1) tint) tint)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _fib_rec (Tfunction (tint :: nil) tint cc_default))
          ((Ebinop Osub (Etempvar _n tint) (Econst_int (Int.repr 2) tint)
             tint) :: nil))
        (Scall (Some _t'2)
          (Evar _fib_rec (Tfunction (tint :: nil) tint cc_default))
          ((Ebinop Osub (Etempvar _n tint) (Econst_int (Int.repr 1) tint)
             tint) :: nil)))
      (Sreturn (Some (Ebinop Oadd (Etempvar _t'1 tint) (Etempvar _t'2 tint)
                       tint))))))
|}.

Definition f_swap_int := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tint)) :: (_y, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_a, tint) :: (_b, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _a (Ederef (Etempvar _x (tptr tint)) tint))
  (Ssequence
    (Sset _b (Ederef (Etempvar _y (tptr tint)) tint))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _a tint) (Etempvar _b tint) tint)
        (Sreturn None)
        Sskip)
      (Ssequence
        (Sassign (Ederef (Etempvar _x (tptr tint)) tint) (Etempvar _b tint))
        (Sassign (Ederef (Etempvar _y (tptr tint)) tint) (Etempvar _a tint))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 0) tint)))
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
 (_fib_loop, Gfun(Internal f_fib_loop)) ::
 (_fib_loop_save_var, Gfun(Internal f_fib_loop_save_var)) ::
 (_fib_loop_mod, Gfun(Internal f_fib_loop_mod)) ::
 (_fib_rec, Gfun(Internal f_fib_rec)) ::
 (_swap_int, Gfun(Internal f_swap_int)) :: (_main, Gfun(Internal f_main)) ::
 nil).

Definition public_idents : list ident :=
(_main :: _swap_int :: _fib_rec :: _fib_loop_mod :: _fib_loop_save_var ::
 _fib_loop :: ___builtin_debug :: ___builtin_write32_reversed ::
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


