From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.4"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "atomics/kvnode_atomic.c"%string.
  Definition normalized := false.
End Info.

Definition _CAS_SC : ident := 78%positive.
Definition ___builtin_ais_annot : ident := 6%positive.
Definition ___builtin_annot : ident := 13%positive.
Definition ___builtin_annot_intval : ident := 14%positive.
Definition ___builtin_bswap : ident := 7%positive.
Definition ___builtin_bswap16 : ident := 9%positive.
Definition ___builtin_bswap32 : ident := 8%positive.
Definition ___builtin_bswap64 : ident := 39%positive.
Definition ___builtin_clz : ident := 40%positive.
Definition ___builtin_clzl : ident := 41%positive.
Definition ___builtin_clzll : ident := 42%positive.
Definition ___builtin_ctz : ident := 43%positive.
Definition ___builtin_ctzl : ident := 44%positive.
Definition ___builtin_ctzll : ident := 45%positive.
Definition ___builtin_debug : ident := 57%positive.
Definition ___builtin_fabs : ident := 10%positive.
Definition ___builtin_fmadd : ident := 48%positive.
Definition ___builtin_fmax : ident := 46%positive.
Definition ___builtin_fmin : ident := 47%positive.
Definition ___builtin_fmsub : ident := 49%positive.
Definition ___builtin_fnmadd : ident := 50%positive.
Definition ___builtin_fnmsub : ident := 51%positive.
Definition ___builtin_fsqrt : ident := 11%positive.
Definition ___builtin_membar : ident := 15%positive.
Definition ___builtin_memcpy_aligned : ident := 12%positive.
Definition ___builtin_nop : ident := 56%positive.
Definition ___builtin_read16_reversed : ident := 52%positive.
Definition ___builtin_read32_reversed : ident := 53%positive.
Definition ___builtin_va_arg : ident := 17%positive.
Definition ___builtin_va_copy : ident := 18%positive.
Definition ___builtin_va_end : ident := 19%positive.
Definition ___builtin_va_start : ident := 16%positive.
Definition ___builtin_write16_reversed : ident := 54%positive.
Definition ___builtin_write32_reversed : ident := 55%positive.
Definition ___compcert_i64_dtos : ident := 24%positive.
Definition ___compcert_i64_dtou : ident := 25%positive.
Definition ___compcert_i64_sar : ident := 36%positive.
Definition ___compcert_i64_sdiv : ident := 30%positive.
Definition ___compcert_i64_shl : ident := 34%positive.
Definition ___compcert_i64_shr : ident := 35%positive.
Definition ___compcert_i64_smod : ident := 32%positive.
Definition ___compcert_i64_smulh : ident := 37%positive.
Definition ___compcert_i64_stod : ident := 26%positive.
Definition ___compcert_i64_stof : ident := 28%positive.
Definition ___compcert_i64_udiv : ident := 31%positive.
Definition ___compcert_i64_umod : ident := 33%positive.
Definition ___compcert_i64_umulh : ident := 38%positive.
Definition ___compcert_i64_utod : ident := 27%positive.
Definition ___compcert_i64_utof : ident := 29%positive.
Definition ___compcert_va_composite : ident := 23%positive.
Definition ___compcert_va_float64 : ident := 22%positive.
Definition ___compcert_va_int32 : ident := 20%positive.
Definition ___compcert_va_int64 : ident := 21%positive.
Definition _a : ident := 1%positive.
Definition _acquire : ident := 63%positive.
Definition _atomic_exchange_SC : ident := 79%positive.
Definition _atomic_loc : ident := 5%positive.
Definition _c : ident := 77%positive.
Definition _d : ident := 90%positive.
Definition _data : ident := 83%positive.
Definition _exit : ident := 58%positive.
Definition _free : ident := 59%positive.
Definition _free_atomic : ident := 72%positive.
Definition _freelock : ident := 62%positive.
Definition _i : ident := 68%positive.
Definition _in : ident := 89%positive.
Definition _l : ident := 69%positive.
Definition _load_SC : ident := 74%positive.
Definition _load_relaxed : ident := 80%positive.
Definition _lock : ident := 4%positive.
Definition _lock_t : ident := 2%positive.
Definition _main : ident := 81%positive.
Definition _make_atomic : ident := 70%positive.
Definition _makelock : ident := 61%positive.
Definition _malloc : ident := 60%positive.
Definition _n : ident := 65%positive.
Definition _node : ident := 84%positive.
Definition _out : ident := 85%positive.
Definition _p : ident := 66%positive.
Definition _read : ident := 88%positive.
Definition _release : ident := 64%positive.
Definition _snap : ident := 87%positive.
Definition _store_SC : ident := 76%positive.
Definition _surely_malloc : ident := 67%positive.
Definition _tgt : ident := 71%positive.
Definition _v : ident := 75%positive.
Definition _val : ident := 3%positive.
Definition _ver : ident := 86%positive.
Definition _version : ident := 82%positive.
Definition _write : ident := 91%positive.
Definition _x : ident := 73%positive.
Definition _t'1 : ident := 92%positive.
Definition _t'2 : ident := 93%positive.
Definition _t'3 : ident := 94%positive.

Definition f_read := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_n, (tptr (Tstruct _node noattr))) :: (_out, (tptr tint)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_ver, (tptr tint)) :: (_snap, tint) :: (_i, tint) ::
               (_l, (tptr tint)) :: (_v, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Sset _ver
        (Efield
          (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _version (tptr tint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _load_SC (Tfunction (Tcons (tptr tint) Tnil) tint
                             cc_default))
            ((Etempvar _ver (tptr tint)) :: nil))
          (Sset _snap (Etempvar _t'1 tint)))
        (Ssequence
          (Sifthenelse (Ebinop Oand (Etempvar _snap tint)
                         (Ebinop Oeq (Econst_int (Int.repr 1) tint)
                           (Econst_int (Int.repr 1) tint) tint) tint)
            Scontinue
            Sskip)
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 8) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _l
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _n (tptr (Tstruct _node noattr)))
                              (Tstruct _node noattr)) _data
                            (tarray (tptr tint) 8)) (Etempvar _i tint)
                          (tptr (tptr tint))) (tptr tint)))
                    (Ssequence
                      (Scall (Some _t'2)
                        (Evar _load_SC (Tfunction (Tcons (tptr tint) Tnil)
                                         tint cc_default))
                        ((Etempvar _l (tptr tint)) :: nil))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _out (tptr tint))
                            (Etempvar _i tint) (tptr tint)) tint)
                        (Etempvar _t'2 tint)))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _load_SC (Tfunction (Tcons (tptr tint) Tnil) tint
                                   cc_default))
                  ((Etempvar _ver (tptr tint)) :: nil))
                (Sset _v (Etempvar _t'3 tint)))
              (Sifthenelse (Ebinop Oeq (Etempvar _v tint)
                             (Etempvar _snap tint) tint)
                (Sreturn None)
                Sskip)))))))
  Sskip)
|}.

Definition f_write := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_n, (tptr (Tstruct _node noattr))) :: (_in, (tptr tint)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_ver, (tptr tint)) :: (_v, tint) :: (_i, tint) ::
               (_l, (tptr tint)) :: (_d, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _ver
    (Efield
      (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
        (Tstruct _node noattr)) _version (tptr tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _load_SC (Tfunction (Tcons (tptr tint) Tnil) tint cc_default))
        ((Etempvar _ver (tptr tint)) :: nil))
      (Sset _v (Etempvar _t'1 tint)))
    (Ssequence
      (Scall None
        (Evar _store_SC (Tfunction (Tcons (tptr tint) (Tcons tint Tnil))
                          tvoid cc_default))
        ((Etempvar _ver (tptr tint)) ::
         (Ebinop Oadd (Etempvar _v tint) (Econst_int (Int.repr 1) tint) tint) ::
         nil))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 8) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _l
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
                          (Tstruct _node noattr)) _data
                        (tarray (tptr tint) 8)) (Etempvar _i tint)
                      (tptr (tptr tint))) (tptr tint)))
                (Ssequence
                  (Sset _d
                    (Ederef
                      (Ebinop Oadd (Etempvar _in (tptr tint))
                        (Etempvar _i tint) (tptr tint)) tint))
                  (Scall None
                    (Evar _store_SC (Tfunction
                                      (Tcons (tptr tint) (Tcons tint Tnil))
                                      tvoid cc_default))
                    ((Etempvar _l (tptr tint)) :: (Etempvar _d tint) :: nil)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Scall None
          (Evar _store_SC (Tfunction (Tcons (tptr tint) (Tcons tint Tnil))
                            tvoid cc_default))
          ((Etempvar _ver (tptr tint)) ::
           (Ebinop Oadd (Etempvar _v tint) (Econst_int (Int.repr 2) tint)
             tint) :: nil))))))
|}.

Definition composites : list composite_definition :=
(Composite _node Struct
   ((_version, (tptr tint)) :: (_data, (tarray (tptr tint) 8)) :: nil)
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
 (_load_SC,
   Gfun(External (EF_external "load_SC"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tint) Tnil) tint cc_default)) ::
 (_store_SC,
   Gfun(External (EF_external "store_SC"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tint) (Tcons tint Tnil)) tvoid
     cc_default)) :: (_read, Gfun(Internal f_read)) ::
 (_write, Gfun(Internal f_write)) :: nil).

Definition public_idents : list ident :=
(_write :: _read :: _store_SC :: _load_SC :: ___builtin_debug ::
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


