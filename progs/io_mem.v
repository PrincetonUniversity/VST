From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.7"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "progs/io_mem.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 9%positive.
Definition ___builtin_annot_intval : ident := 10%positive.
Definition ___builtin_bswap : ident := 2%positive.
Definition ___builtin_bswap16 : ident := 4%positive.
Definition ___builtin_bswap32 : ident := 3%positive.
Definition ___builtin_bswap64 : ident := 1%positive.
Definition ___builtin_clz : ident := 35%positive.
Definition ___builtin_clzl : ident := 36%positive.
Definition ___builtin_clzll : ident := 37%positive.
Definition ___builtin_ctz : ident := 38%positive.
Definition ___builtin_ctzl : ident := 39%positive.
Definition ___builtin_ctzll : ident := 40%positive.
Definition ___builtin_debug : ident := 51%positive.
Definition ___builtin_fabs : ident := 5%positive.
Definition ___builtin_fmadd : ident := 43%positive.
Definition ___builtin_fmax : ident := 41%positive.
Definition ___builtin_fmin : ident := 42%positive.
Definition ___builtin_fmsub : ident := 44%positive.
Definition ___builtin_fnmadd : ident := 45%positive.
Definition ___builtin_fnmsub : ident := 46%positive.
Definition ___builtin_fsqrt : ident := 6%positive.
Definition ___builtin_membar : ident := 11%positive.
Definition ___builtin_memcpy_aligned : ident := 7%positive.
Definition ___builtin_read16_reversed : ident := 47%positive.
Definition ___builtin_read32_reversed : ident := 48%positive.
Definition ___builtin_sel : ident := 8%positive.
Definition ___builtin_va_arg : ident := 13%positive.
Definition ___builtin_va_copy : ident := 14%positive.
Definition ___builtin_va_end : ident := 15%positive.
Definition ___builtin_va_start : ident := 12%positive.
Definition ___builtin_write16_reversed : ident := 49%positive.
Definition ___builtin_write32_reversed : ident := 50%positive.
Definition ___compcert_i64_dtos : ident := 20%positive.
Definition ___compcert_i64_dtou : ident := 21%positive.
Definition ___compcert_i64_sar : ident := 32%positive.
Definition ___compcert_i64_sdiv : ident := 26%positive.
Definition ___compcert_i64_shl : ident := 30%positive.
Definition ___compcert_i64_shr : ident := 31%positive.
Definition ___compcert_i64_smod : ident := 28%positive.
Definition ___compcert_i64_smulh : ident := 33%positive.
Definition ___compcert_i64_stod : ident := 22%positive.
Definition ___compcert_i64_stof : ident := 24%positive.
Definition ___compcert_i64_udiv : ident := 27%positive.
Definition ___compcert_i64_umod : ident := 29%positive.
Definition ___compcert_i64_umulh : ident := 34%positive.
Definition ___compcert_i64_utod : ident := 23%positive.
Definition ___compcert_i64_utof : ident := 25%positive.
Definition ___compcert_va_composite : ident := 19%positive.
Definition ___compcert_va_float64 : ident := 18%positive.
Definition ___compcert_va_int32 : ident := 16%positive.
Definition ___compcert_va_int64 : ident := 17%positive.
Definition _buf : ident := 58%positive.
Definition _c : ident := 66%positive.
Definition _d : ident := 65%positive.
Definition _exit : ident := 52%positive.
Definition _free : ident := 53%positive.
Definition _getchars : ident := 55%positive.
Definition _i : ident := 57%positive.
Definition _j : ident := 67%positive.
Definition _k : ident := 61%positive.
Definition _main : ident := 68%positive.
Definition _malloc : ident := 54%positive.
Definition _n : ident := 64%positive.
Definition _print_int : ident := 63%positive.
Definition _print_intr : ident := 62%positive.
Definition _putchars : ident := 56%positive.
Definition _q : ident := 59%positive.
Definition _r : ident := 60%positive.
Definition _t'1 : ident := 69%positive.
Definition _t'2 : ident := 70%positive.
Definition _t'3 : ident := 71%positive.
Definition _t'4 : ident := 72%positive.

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
                (Evar _print_intr (Tfunction
                                    (Tcons tuint (Tcons (tptr tuchar) Tnil))
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
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Econst_int (Int.repr 5) tint) :: nil))
    (Sset _buf (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _buf (tptr tuchar)) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
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
              (Evar _print_intr (Tfunction
                                  (Tcons tuint (Tcons (tptr tuchar) Tnil))
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
          (Evar _putchars (Tfunction (Tcons (tptr tuchar) (Tcons tint Tnil))
                            tint cc_default))
          ((Etempvar _buf (tptr tuchar)) :: (Etempvar _k tint) :: nil))
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
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
          (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                          cc_default))
          ((Econst_int (Int.repr 4) tint) :: nil))
        (Sset _buf (Etempvar _t'1 (tptr tvoid))))
      (Ssequence
        (Sifthenelse (Eunop Onotbool (Etempvar _buf (tptr tuchar)) tint)
          (Scall None
            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil))
          Sskip)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _getchars (Tfunction
                                (Tcons (tptr tuchar) (Tcons tint Tnil)) tint
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
                                                (Tcons (tptr tvoid) Tnil)
                                                tvoid cc_default))
                                  ((Etempvar _buf (tptr tuchar)) :: nil))
                                (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                              Sskip)
                            (Ssequence
                              (Sset _n
                                (Ebinop Oadd (Etempvar _n tuint)
                                  (Etempvar _d tuint) tuint))
                              (Scall None
                                (Evar _print_int (Tfunction
                                                   (Tcons tuint Tnil) tvoid
                                                   cc_default))
                                ((Etempvar _n tuint) :: nil)))))))
                    (Sset _j
                      (Ebinop Oadd (Etempvar _j tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _getchars (Tfunction
                                      (Tcons (tptr tuchar) (Tcons tint Tnil))
                                      tint cc_default))
                    ((Etempvar _buf (tptr tuchar)) ::
                     (Econst_int (Int.repr 4) tint) :: nil))
                  (Sset _i (Etempvar _t'3 tint)))))
            (Ssequence
              (Scall None
                (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                              cc_default))
                ((Etempvar _buf (tptr tuchar)) :: nil))
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
nil.

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
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
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
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_getchars,
   Gfun(External (EF_external "getchars"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tuchar) (Tcons tint Tnil))
     tint cc_default)) ::
 (_putchars,
   Gfun(External (EF_external "putchars"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tuchar) (Tcons tint Tnil))
     tint cc_default)) :: (_print_intr, Gfun(Internal f_print_intr)) ::
 (_print_int, Gfun(Internal f_print_int)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _print_int :: _print_intr :: _putchars :: _getchars :: _malloc ::
 _free :: _exit :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


