Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _s2 : ident := 32%positive.
Definition ___compcert_va_int64 : ident := 16%positive.
Definition _strcspn_kmp : ident := 38%positive.
Definition ___builtin_fmadd : ident := 24%positive.
Definition ___builtin_fmax : ident := 22%positive.
Definition ___compcert_va_float64 : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition ___builtin_va_arg : ident := 12%positive.
Definition ___builtin_annot_intval : ident := 10%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _j : ident := 36%positive.
Definition _s1 : ident := 31%positive.
Definition ___builtin_va_end : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition ___builtin_fnmadd : ident := 26%positive.
Definition ___builtin_bswap32 : ident := 19%positive.
Definition _main : ident := 39%positive.
Definition ___builtin_va_start : ident := 11%positive.
Definition _next : ident := 37%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition ___builtin_read16_reversed : ident := 28%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_fsqrt : ident := 21%positive.
Definition ___builtin_bswap : ident := 18%positive.
Definition ___builtin_annot : ident := 9%positive.
Definition ___builtin_va_copy : ident := 13%positive.
Definition ___builtin_fnmsub : ident := 27%positive.
Definition _n1 : ident := 33%positive.
Definition ___builtin_fmsub : ident := 25%positive.
Definition ___compcert_va_int32 : ident := 15%positive.
Definition _n2 : ident := 34%positive.
Definition ___builtin_read32_reversed : ident := 29%positive.
Definition _i : ident := 35%positive.
Definition _mallocN : ident := 30%positive.
Definition ___builtin_fmin : ident := 23%positive.
Definition ___builtin_bswap16 : ident := 20%positive.
Definition _next' : ident := 40%positive.


Definition f_strcspn_kmp := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s1, (tptr tschar)) :: (_s2, (tptr tschar)) ::
                (_n1, tint) :: (_n2, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_j, tint) :: (_next, (tptr tint)) ::
               (_next', (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _next')
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
      ((Ebinop Omul (Etempvar _n2 tint) (Econst_int (Int.repr 4) tuint)
         tuint) :: nil))
    (Sset _next (Ecast (Etempvar _next' (tptr tvoid)) (tptr tint))))
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
            (Sifthenelse (Ebinop Oeq
                           (Ederef
                             (Ebinop Oadd (Etempvar _s2 (tptr tschar))
                               (Ebinop Oadd (Etempvar _i tint)
                                 (Econst_int (Int.repr 1) tint) tint)
                               (tptr tschar)) tschar)
                           (Ederef
                             (Ebinop Oadd (Etempvar _s2 (tptr tschar))
                               (Ebinop Oadd (Etempvar _j tint)
                                 (Econst_int (Int.repr 1) tint) tint)
                               (tptr tschar)) tschar) tint)
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
                             (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                             tint)
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
                      (Etempvar _j tint) (tptr tint)) tint)))))
          (Ssequence
            (Sset _i (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
            (Ssequence
              (Sset _j (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
              (Ssequence
                (Swhile
                  (Ebinop Olt (Etempvar _i tint) (Etempvar _n1 tint) tint)
                  (Sifthenelse (Ebinop Oeq
                                 (Ederef
                                   (Ebinop Oadd (Etempvar _s1 (tptr tschar))
                                     (Ebinop Oadd (Etempvar _i tint)
                                       (Econst_int (Int.repr 1) tint) tint)
                                     (tptr tschar)) tschar)
                                 (Ederef
                                   (Ebinop Oadd (Etempvar _s2 (tptr tschar))
                                     (Ebinop Oadd (Etempvar _j tint)
                                       (Econst_int (Int.repr 1) tint) tint)
                                     (tptr tschar)) tschar) tint)
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
                                         (Econst_int (Int.repr 1) tint) tint)
                                       tint)
                          (Sreturn (Some (Ebinop Oadd
                                           (Ebinop Osub (Etempvar _i tint)
                                             (Etempvar _n2 tint) tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint)))
                          Sskip)))
                    (Sifthenelse (Ebinop Oeq (Etempvar _j tint)
                                   (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                     tint) tint)
                      (Sset _i
                        (Ebinop Oadd (Etempvar _i tint)
                          (Econst_int (Int.repr 1) tint) tint))
                      (Sset _j
                        (Ederef
                          (Ebinop Oadd (Etempvar _next (tptr tint))
                            (Etempvar _j tint) (tptr tint)) tint)))))
                (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                 tint)))))))))))
|}.

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
   Gfun(External (EF_builtin ___builtin_fabs
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin ___builtin_memcpy_aligned
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin ___builtin_annot
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin ___builtin_va_start
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin ___builtin_va_arg
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin ___builtin_va_copy
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin ___builtin_va_end
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external ___compcert_va_int32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external ___compcert_va_int64
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external ___compcert_va_float64
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin ___builtin_bswap
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin ___builtin_bswap32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin ___builtin_bswap16
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin ___builtin_fsqrt
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin ___builtin_fmax
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin ___builtin_fmin
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin ___builtin_fmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin ___builtin_fmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin ___builtin_fnmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin ___builtin_fnmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin ___builtin_read16_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin ___builtin_read32_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin ___builtin_write16_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin ___builtin_write32_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (_mallocN,
   Gfun(External (EF_external _mallocN
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint Tnil) (tptr tvoid) cc_default)) ::
 (_strcspn_kmp, Gfun(Internal f_strcspn_kmp)) :: nil);
prog_main := _main
|}.

