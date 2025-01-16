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
  Definition source_file := "progs/union.c".
  Definition normalized := true.
End Info.

Definition __113 : ident := 7%positive.
Definition ___builtin_ais_annot : ident := 10%positive.
Definition ___builtin_annot : ident := 27%positive.
Definition ___builtin_annot_intval : ident := 28%positive.
Definition ___builtin_bswap : ident := 12%positive.
Definition ___builtin_bswap16 : ident := 14%positive.
Definition ___builtin_bswap32 : ident := 13%positive.
Definition ___builtin_bswap64 : ident := 11%positive.
Definition ___builtin_clz : ident := 15%positive.
Definition ___builtin_clzl : ident := 16%positive.
Definition ___builtin_clzll : ident := 17%positive.
Definition ___builtin_ctz : ident := 18%positive.
Definition ___builtin_ctzl : ident := 19%positive.
Definition ___builtin_ctzll : ident := 20%positive.
Definition ___builtin_debug : ident := 46%positive.
Definition ___builtin_expect : ident := 35%positive.
Definition ___builtin_fabs : ident := 21%positive.
Definition ___builtin_fabsf : ident := 22%positive.
Definition ___builtin_fmadd : ident := 38%positive.
Definition ___builtin_fmax : ident := 36%positive.
Definition ___builtin_fmin : ident := 37%positive.
Definition ___builtin_fmsub : ident := 39%positive.
Definition ___builtin_fnmadd : ident := 40%positive.
Definition ___builtin_fnmsub : ident := 41%positive.
Definition ___builtin_fsqrt : ident := 23%positive.
Definition ___builtin_membar : ident := 29%positive.
Definition ___builtin_memcpy_aligned : ident := 25%positive.
Definition ___builtin_read16_reversed : ident := 42%positive.
Definition ___builtin_read32_reversed : ident := 43%positive.
Definition ___builtin_sel : ident := 26%positive.
Definition ___builtin_sqrt : ident := 24%positive.
Definition ___builtin_unreachable : ident := 34%positive.
Definition ___builtin_va_arg : ident := 31%positive.
Definition ___builtin_va_copy : ident := 32%positive.
Definition ___builtin_va_end : ident := 33%positive.
Definition ___builtin_va_start : ident := 30%positive.
Definition ___builtin_write16_reversed : ident := 44%positive.
Definition ___builtin_write32_reversed : ident := 45%positive.
Definition ___compcert_i64_dtos : ident := 59%positive.
Definition ___compcert_i64_dtou : ident := 60%positive.
Definition ___compcert_i64_sar : ident := 71%positive.
Definition ___compcert_i64_sdiv : ident := 65%positive.
Definition ___compcert_i64_shl : ident := 69%positive.
Definition ___compcert_i64_shr : ident := 70%positive.
Definition ___compcert_i64_smod : ident := 67%positive.
Definition ___compcert_i64_smulh : ident := 72%positive.
Definition ___compcert_i64_stod : ident := 61%positive.
Definition ___compcert_i64_stof : ident := 63%positive.
Definition ___compcert_i64_udiv : ident := 66%positive.
Definition ___compcert_i64_umod : ident := 68%positive.
Definition ___compcert_i64_umulh : ident := 73%positive.
Definition ___compcert_i64_utod : ident := 62%positive.
Definition ___compcert_i64_utof : ident := 64%positive.
Definition ___compcert_va_composite : ident := 58%positive.
Definition ___compcert_va_float64 : ident := 57%positive.
Definition ___compcert_va_int32 : ident := 55%positive.
Definition ___compcert_va_int64 : ident := 56%positive.
Definition _c : ident := 5%positive.
Definition _choice_i : ident := 2%positive.
Definition _choice_p : ident := 3%positive.
Definition _const_or_not : ident := 4%positive.
Definition _f : ident := 8%positive.
Definition _fabs_single : ident := 54%positive.
Definition _g : ident := 48%positive.
Definition _h : ident := 50%positive.
Definition _i : ident := 9%positive.
Definition _main : ident := 74%positive.
Definition _n : ident := 6%positive.
Definition _p : ident := 49%positive.
Definition _p_or_i : ident := 1%positive.
Definition _t : ident := 51%positive.
Definition _u : ident := 53%positive.
Definition _unconst : ident := 52%positive.
Definition _x : ident := 47%positive.
Definition _t'1 : ident := 75%positive.
Definition _t'2 : ident := 76%positive.

Definition f_g := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_i, tuint) :: nil);
  fn_vars := ((_x, (Tunion _p_or_i noattr)) :: nil);
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _x (Tunion _p_or_i noattr)) _choice_i tuint)
    (Etempvar _i tuint))
  (Ssequence
    (Sset _t'1 (Efield (Evar _x (Tunion _p_or_i noattr)) _choice_i tuint))
    (Sreturn (Some (Etempvar _t'1 tuint)))))
|}.

Definition f_h := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) :: nil);
  fn_vars := ((_x, (Tunion _p_or_i noattr)) :: nil);
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _x (Tunion _p_or_i noattr)) _choice_p (tptr tvoid))
    (Etempvar _p (tptr tvoid)))
  (Ssequence
    (Sset _t'1
      (Efield (Evar _x (Tunion _p_or_i noattr)) _choice_p (tptr tvoid)))
    (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))
|}.

Definition f_unconst := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tschar)) :: nil);
  fn_vars := ((_t, (Tunion _const_or_not noattr)) :: nil);
  fn_temps := ((_t'1, (tptr tschar)) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _t (Tunion _const_or_not noattr)) _c (tptr tschar))
    (Etempvar _x (tptr tschar)))
  (Ssequence
    (Sset _t'1
      (Efield (Evar _t (Tunion _const_or_not noattr)) _n (tptr tschar)))
    (Sreturn (Some (Etempvar _t'1 (tptr tschar))))))
|}.

Definition f_fabs_single := {|
  fn_return := tfloat;
  fn_callconv := cc_default;
  fn_params := ((_x, tfloat) :: nil);
  fn_vars := ((_u, (Tunion __113 noattr)) :: nil);
  fn_temps := ((_t'2, tuint) :: (_t'1, tfloat) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _u (Tunion __113 noattr)) _f tfloat)
    (Etempvar _x tfloat))
  (Ssequence
    (Ssequence
      (Sset _t'2 (Efield (Evar _u (Tunion __113 noattr)) _i tuint))
      (Sassign (Efield (Evar _u (Tunion __113 noattr)) _i tuint)
        (Ebinop Oand (Etempvar _t'2 tuint)
          (Econst_int (Int.repr 2147483647) tint) tuint)))
    (Ssequence
      (Sset _t'1 (Efield (Evar _u (Tunion __113 noattr)) _f tfloat))
      (Sreturn (Some (Etempvar _t'1 tfloat))))))
|}.

Definition composites : list composite_definition :=
(Composite _p_or_i Union
   (Member_plain _choice_i tuint :: Member_plain _choice_p (tptr tvoid) ::
    nil)
   noattr ::
 Composite _const_or_not Union
   (Member_plain _c (tptr tschar) :: Member_plain _n (tptr tschar) :: nil)
   noattr ::
 Composite __113 Union
   (Member_plain _f tfloat :: Member_plain _i tuint :: nil)
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
 (_g, Gfun(Internal f_g)) :: (_h, Gfun(Internal f_h)) ::
 (_unconst, Gfun(Internal f_unconst)) ::
 (_fabs_single, Gfun(Internal f_fabs_single)) :: nil).

Definition public_idents : list ident :=
(_fabs_single :: _unconst :: _h :: _g :: ___builtin_debug ::
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


