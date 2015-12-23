Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _temp : ident := 85%positive.
Definition _j : ident := 65%positive.
Definition ___builtin_read32_reversed : ident := 40%positive.
Definition _p3 : ident := 112%positive.
Definition _p1 : ident := 110%positive.
Definition ___i64_stod : ident := 16%positive.
Definition ___builtin_fnmsub : ident := 38%positive.
Definition _y : ident := 46%positive.
Definition _head : ident := 69%positive.
Definition _p : ident := 62%positive.
Definition _odd : ident := 54%positive.
Definition _p2 : ident := 111%positive.
Definition ___i64_smod : ident := 22%positive.
Definition ___compcert_va_float64 : ident := 12%positive.
Definition _deserialize : ident := 92%positive.
Definition _c : ident := 108%positive.
Definition _get : ident := 104%positive.
Definition _sub1 : ident := 63%positive.
Definition ___compcert_va_int32 : ident := 10%positive.
Definition ___builtin_debug : ident := 44%positive.
Definition ___builtin_annot : ident := 3%positive.
Definition ___builtin_memcpy_aligned : ident := 2%positive.
Definition ___builtin_fabs : ident := 1%positive.
Definition _t2 : ident := 121%positive.
Definition ___builtin_ctz : ident := 31%positive.
Definition _cond : ident := 88%positive.
Definition _out : ident := 119%positive.
Definition _insert : ident := 79%positive.
Definition _insert_node : ident := 72%positive.
Definition _add : ident := 49%positive.
Definition _sub3 : ident := 66%positive.
Definition _y1 : ident := 59%positive.
Definition ___builtin_annot_intval : ident := 4%positive.
Definition _p0 : ident := 109%positive.
Definition _insert_value : ident := 78%positive.
Definition _intpair : ident := 94%positive.
Definition _s : ident := 68%positive.
Definition _a : ident := 58%positive.
Definition ___builtin_bswap32 : ident := 28%positive.
Definition _p4 : ident := 113%positive.
Definition _ser : ident := 102%positive.
Definition ___builtin_va_arg : ident := 7%positive.
Definition _des : ident := 103%positive.
Definition _intpair_message : ident := 99%positive.
Definition ___i64_udiv : ident := 21%positive.
Definition ___i64_stof : ident := 18%positive.
Definition _len : ident := 101%positive.
Definition _merge : ident := 89%positive.
Definition _x : ident := 45%positive.
Definition _z1 : ident := 106%positive.
Definition _next : ident := 80%positive.
Definition ___compcert_va_composite : ident := 13%positive.
Definition ___builtin_bswap : ident := 27%positive.
Definition _ret : ident := 84%positive.
Definition _do_or : ident := 82%positive.
Definition ___builtin_fmax : ident := 33%positive.
Definition _product : ident := 123%positive.
Definition _x1 : ident := 56%positive.
Definition ___i64_shr : ident := 25%positive.
Definition ___i64_dtou : ident := 15%positive.
Definition _y2 : ident := 60%positive.
Definition _p6 : ident := 115%positive.
Definition _q : ident := 100%positive.
Definition _p5 : ident := 114%positive.
Definition ___i64_sdiv : ident := 20%positive.
Definition ___builtin_fsqrt : ident := 32%positive.
Definition _message : ident := 93%positive.
Definition _multi_command : ident := 117%positive.
Definition _set : ident := 105%positive.
Definition _list : ident := 70%positive.
Definition ___i64_shl : ident := 24%positive.
Definition _intpair_serialize : ident := 96%positive.
Definition _foo : ident := 67%positive.
Definition ___i64_utod : ident := 17%positive.
Definition ___builtin_va_copy : ident := 8%positive.
Definition ___builtin_membar : ident := 5%positive.
Definition _sorted : ident := 73%positive.
Definition _n : ident := 50%positive.
Definition ___builtin_nop : ident := 43%positive.
Definition _index : ident := 74%positive.
Definition _main : ident := 53%positive.
Definition _z : ident := 47%positive.
Definition _z2 : ident := 107%positive.
Definition _x2 : ident := 57%positive.
Definition _serialize : ident := 91%positive.
Definition ___builtin_fmsub : ident := 36%positive.
Definition ___i64_dtos : ident := 14%positive.
Definition ___builtin_va_start : ident := 6%positive.
Definition _multi_command_s : ident := 118%positive.
Definition _intpair_deserialize : ident := 98%positive.
Definition ___i64_sar : ident := 26%positive.
Definition ___i64_utof : ident := 19%positive.
Definition ___builtin_read16_reversed : ident := 39%positive.
Definition _bufsize : ident := 90%positive.
Definition _do_and : ident := 83%positive.
Definition _b : ident := 61%positive.
Definition ___compcert_va_int64 : ident := 11%positive.
Definition _p7 : ident := 116%positive.
Definition _length : ident := 97%positive.
Definition _t3 : ident := 122%positive.
Definition ___builtin_fnmadd : ident := 37%positive.
Definition _insertionsort : ident := 81%positive.
Definition _sortedvalue : ident := 76%positive.
Definition _va : ident := 86%positive.
Definition ___builtin_write32_reversed : ident := 42%positive.
Definition ___builtin_va_end : ident := 9%positive.
Definition _sub2 : ident := 64%positive.
Definition _dotprod : ident := 52%positive.
Definition ___builtin_write16_reversed : ident := 41%positive.
Definition _vb : ident := 87%positive.
Definition _guard : ident := 77%positive.
Definition _tail : ident := 71%positive.
Definition _t1 : ident := 120%positive.
Definition _previous : ident := 75%positive.
Definition ___builtin_fmin : ident := 34%positive.
Definition ___builtin_bswap16 : ident := 29%positive.
Definition _buf : ident := 95%positive.
Definition _even : ident := 55%positive.
Definition ___builtin_fmadd : ident := 35%positive.
Definition ___builtin_clz : ident := 30%positive.
Definition ___i64_umod : ident := 23%positive.
Definition _sum : ident := 51%positive.
Definition _i : ident := 48%positive.

Definition f_product := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tlong)) :: (_a, (tptr tlong)) ::
                (_b, (tptr tlong)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t1, tint) :: (_t2, tint) :: (_t3, tlong) :: nil);
  fn_body :=
(Ssequence
  (Sset _t1
    (Ecast
      (Ederef
        (Ebinop Oadd (Etempvar _a (tptr tlong))
          (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong) tint))
  (Ssequence
    (Sset _t2
      (Ecast
        (Ederef
          (Ebinop Oadd (Etempvar _b (tptr tlong))
            (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong) tint))
    (Ssequence
      (Sset _t3
        (Ecast (Ebinop Omul (Etempvar _t1 tint) (Etempvar _t2 tint) tint)
          tlong))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _out (tptr tlong))
              (Econst_int (Int.repr 0) tint) (tptr tlong)) tlong)
          (Etempvar _t3 tlong))
        (Sreturn None)))))
|}.

Definition composites : list composite_definition :=
nil.

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
 (_product, Gfun(Internal f_product)) :: nil);
prog_public :=
(_product :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fsqrt :: ___builtin_ctz :: ___builtin_clz ::
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

