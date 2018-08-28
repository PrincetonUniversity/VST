From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.3"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "progs/nest3.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := 10%positive.
Definition ___builtin_annot : ident := 17%positive.
Definition ___builtin_annot_intval : ident := 18%positive.
Definition ___builtin_bswap : ident := 11%positive.
Definition ___builtin_bswap16 : ident := 13%positive.
Definition ___builtin_bswap32 : ident := 12%positive.
Definition ___builtin_bswap64 : ident := 43%positive.
Definition ___builtin_clz : ident := 44%positive.
Definition ___builtin_clzl : ident := 45%positive.
Definition ___builtin_clzll : ident := 46%positive.
Definition ___builtin_ctz : ident := 47%positive.
Definition ___builtin_ctzl : ident := 48%positive.
Definition ___builtin_ctzll : ident := 49%positive.
Definition ___builtin_debug : ident := 61%positive.
Definition ___builtin_fabs : ident := 14%positive.
Definition ___builtin_fmadd : ident := 52%positive.
Definition ___builtin_fmax : ident := 50%positive.
Definition ___builtin_fmin : ident := 51%positive.
Definition ___builtin_fmsub : ident := 53%positive.
Definition ___builtin_fnmadd : ident := 54%positive.
Definition ___builtin_fnmsub : ident := 55%positive.
Definition ___builtin_fsqrt : ident := 15%positive.
Definition ___builtin_membar : ident := 19%positive.
Definition ___builtin_memcpy_aligned : ident := 16%positive.
Definition ___builtin_nop : ident := 60%positive.
Definition ___builtin_read16_reversed : ident := 56%positive.
Definition ___builtin_read32_reversed : ident := 57%positive.
Definition ___builtin_va_arg : ident := 21%positive.
Definition ___builtin_va_copy : ident := 22%positive.
Definition ___builtin_va_end : ident := 23%positive.
Definition ___builtin_va_start : ident := 20%positive.
Definition ___builtin_write16_reversed : ident := 58%positive.
Definition ___builtin_write32_reversed : ident := 59%positive.
Definition ___compcert_i64_dtos : ident := 28%positive.
Definition ___compcert_i64_dtou : ident := 29%positive.
Definition ___compcert_i64_sar : ident := 40%positive.
Definition ___compcert_i64_sdiv : ident := 34%positive.
Definition ___compcert_i64_shl : ident := 38%positive.
Definition ___compcert_i64_shr : ident := 39%positive.
Definition ___compcert_i64_smod : ident := 36%positive.
Definition ___compcert_i64_smulh : ident := 41%positive.
Definition ___compcert_i64_stod : ident := 30%positive.
Definition ___compcert_i64_stof : ident := 32%positive.
Definition ___compcert_i64_udiv : ident := 35%positive.
Definition ___compcert_i64_umod : ident := 37%positive.
Definition ___compcert_i64_umulh : ident := 42%positive.
Definition ___compcert_i64_utod : ident := 31%positive.
Definition ___compcert_i64_utof : ident := 33%positive.
Definition ___compcert_va_composite : ident := 27%positive.
Definition ___compcert_va_float64 : ident := 26%positive.
Definition ___compcert_va_int32 : ident := 24%positive.
Definition ___compcert_va_int64 : ident := 25%positive.
Definition _a : ident := 3%positive.
Definition _b : ident := 6%positive.
Definition _c : ident := 9%positive.
Definition _get : ident := 72%positive.
Definition _i : ident := 71%positive.
Definition _main : ident := 76%positive.
Definition _multi_command : ident := 74%positive.
Definition _multi_command_s : ident := 75%positive.
Definition _p : ident := 62%positive.
Definition _p0 : ident := 63%positive.
Definition _p1 : ident := 64%positive.
Definition _p2 : ident := 65%positive.
Definition _p3 : ident := 66%positive.
Definition _p4 : ident := 67%positive.
Definition _p5 : ident := 68%positive.
Definition _p6 : ident := 69%positive.
Definition _p7 : ident := 70%positive.
Definition _set : ident := 73%positive.
Definition _x1 : ident := 1%positive.
Definition _x2 : ident := 2%positive.
Definition _y1 : ident := 4%positive.
Definition _y2 : ident := 5%positive.
Definition _z1 : ident := 7%positive.
Definition _z2 : ident := 8%positive.

Definition v_p := {|
  gvar_info := (Tstruct _c noattr);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_p0 := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_p1 := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_p2 := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_p3 := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_p4 := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_p5 := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_p6 := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_p7 := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_get := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i
    (Efield
      (Efield (Efield (Evar _p (Tstruct _c noattr)) _z2 (Tstruct _b noattr))
        _y2 (Tstruct _a noattr)) _x2 tint))
  (Sreturn (Some (Etempvar _i tint))))
|}.

Definition f_set := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_i, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Efield (Efield (Evar _p (Tstruct _c noattr)) _z2 (Tstruct _b noattr))
      _y2 (Tstruct _a noattr)) _x2 tint) (Etempvar _i tint))
|}.

Definition f_multi_command := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i
    (Efield
      (Efield (Efield (Evar _p (Tstruct _c noattr)) _z1 (Tstruct _b noattr))
        _y1 (Tstruct _a noattr)) _x1 tint))
  (Ssequence
    (Sassign
      (Efield
        (Efield
          (Efield (Evar _p (Tstruct _c noattr)) _z2 (Tstruct _b noattr)) _y2
          (Tstruct _a noattr)) _x2 tint)
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))
    (Ssequence
      (Sset _i
        (Efield
          (Efield
            (Efield (Evar _p (Tstruct _c noattr)) _z1 (Tstruct _b noattr))
            _y1 (Tstruct _a noattr)) _x2 tint))
      (Ssequence
        (Sassign
          (Efield
            (Efield
              (Efield (Evar _p (Tstruct _c noattr)) _z2 (Tstruct _b noattr))
              _y2 (Tstruct _a noattr)) _x1 tint)
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 2) tint)
            tint))
        (Ssequence
          (Sset _i
            (Efield
              (Efield
                (Efield (Evar _p (Tstruct _c noattr)) _z1
                  (Tstruct _b noattr)) _y2 (Tstruct _a noattr)) _x1 tint))
          (Ssequence
            (Sassign
              (Efield
                (Efield
                  (Efield (Evar _p (Tstruct _c noattr)) _z2
                    (Tstruct _b noattr)) _y1 (Tstruct _a noattr)) _x2 tint)
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 3) tint)
                tint))
            (Ssequence
              (Sset _i
                (Efield
                  (Efield
                    (Efield (Evar _p (Tstruct _c noattr)) _z1
                      (Tstruct _b noattr)) _y2 (Tstruct _a noattr)) _x2 tint))
              (Sassign
                (Efield
                  (Efield
                    (Efield (Evar _p (Tstruct _c noattr)) _z2
                      (Tstruct _b noattr)) _y1 (Tstruct _a noattr)) _x1 tint)
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 4) tint) tint)))))))))
|}.

Definition f_multi_command_s := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Evar _p0 tint))
  (Ssequence
    (Sassign (Evar _p7 tint)
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))
    (Ssequence
      (Sset _i (Evar _p1 tint))
      (Ssequence
        (Sassign (Evar _p6 tint)
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 2) tint)
            tint))
        (Ssequence
          (Sset _i (Evar _p2 tint))
          (Ssequence
            (Sassign (Evar _p5 tint)
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 3) tint)
                tint))
            (Ssequence
              (Sset _i (Evar _p3 tint))
              (Sassign (Evar _p4 tint)
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 4) tint) tint)))))))))
|}.

Definition composites : list composite_definition :=
(Composite _a Struct ((_x1, tint) :: (_x2, tint) :: nil) noattr ::
 Composite _b Struct
   ((_y1, (Tstruct _a noattr)) :: (_y2, (Tstruct _a noattr)) :: nil)
   noattr ::
 Composite _c Struct
   ((_z1, (Tstruct _b noattr)) :: (_z2, (Tstruct _b noattr)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
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
 (_p, Gvar v_p) :: (_p0, Gvar v_p0) :: (_p1, Gvar v_p1) ::
 (_p2, Gvar v_p2) :: (_p3, Gvar v_p3) :: (_p4, Gvar v_p4) ::
 (_p5, Gvar v_p5) :: (_p6, Gvar v_p6) :: (_p7, Gvar v_p7) ::
 (_get, Gfun(Internal f_get)) :: (_set, Gfun(Internal f_set)) ::
 (_multi_command, Gfun(Internal f_multi_command)) ::
 (_multi_command_s, Gfun(Internal f_multi_command_s)) :: nil).

Definition public_idents : list ident :=
(_multi_command_s :: _multi_command :: _set :: _get :: _p7 :: _p6 :: _p5 ::
 _p4 :: _p3 :: _p2 :: _p1 :: _p0 :: _p :: ___builtin_debug ::
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
 ___builtin_bswap :: ___builtin_ais_annot :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


