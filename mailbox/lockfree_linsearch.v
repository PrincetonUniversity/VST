
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition ___builtin_annot : ident := 5%positive.
Definition ___builtin_annot_intval : ident := 6%positive.
Definition ___builtin_bswap : ident := 29%positive.
Definition ___builtin_bswap16 : ident := 31%positive.
Definition ___builtin_bswap32 : ident := 30%positive.
Definition ___builtin_clz : ident := 32%positive.
Definition ___builtin_clzl : ident := 33%positive.
Definition ___builtin_clzll : ident := 34%positive.
Definition ___builtin_ctz : ident := 35%positive.
Definition ___builtin_ctzl : ident := 36%positive.
Definition ___builtin_ctzll : ident := 37%positive.
Definition ___builtin_debug : ident := 50%positive.
Definition ___builtin_fabs : ident := 3%positive.
Definition ___builtin_fmadd : ident := 41%positive.
Definition ___builtin_fmax : ident := 39%positive.
Definition ___builtin_fmin : ident := 40%positive.
Definition ___builtin_fmsub : ident := 42%positive.
Definition ___builtin_fnmadd : ident := 43%positive.
Definition ___builtin_fnmsub : ident := 44%positive.
Definition ___builtin_fsqrt : ident := 38%positive.
Definition ___builtin_membar : ident := 7%positive.
Definition ___builtin_memcpy_aligned : ident := 4%positive.
Definition ___builtin_nop : ident := 49%positive.
Definition ___builtin_read16_reversed : ident := 45%positive.
Definition ___builtin_read32_reversed : ident := 46%positive.
Definition ___builtin_va_arg : ident := 9%positive.
Definition ___builtin_va_copy : ident := 10%positive.
Definition ___builtin_va_end : ident := 11%positive.
Definition ___builtin_va_start : ident := 8%positive.
Definition ___builtin_write16_reversed : ident := 47%positive.
Definition ___builtin_write32_reversed : ident := 48%positive.
Definition ___compcert_va_composite : ident := 15%positive.
Definition ___compcert_va_float64 : ident := 14%positive.
Definition ___compcert_va_int32 : ident := 12%positive.
Definition ___compcert_va_int64 : ident := 13%positive.
Definition ___i64_dtos : ident := 16%positive.
Definition ___i64_dtou : ident := 17%positive.
Definition ___i64_sar : ident := 28%positive.
Definition ___i64_sdiv : ident := 22%positive.
Definition ___i64_shl : ident := 26%positive.
Definition ___i64_shr : ident := 27%positive.
Definition ___i64_smod : ident := 24%positive.
Definition ___i64_stod : ident := 18%positive.
Definition ___i64_stof : ident := 20%positive.
Definition ___i64_udiv : ident := 23%positive.
Definition ___i64_umod : ident := 25%positive.
Definition ___i64_utod : ident := 19%positive.
Definition ___i64_utof : ident := 21%positive.
Definition _a : ident := 1%positive.
Definition _acquire : ident := 51%positive.
Definition _c : ident := 59%positive.
Definition _e : ident := 74%positive.
Definition _entry : ident := 66%positive.
Definition _exit : ident := 67%positive.
Definition _get_item : ident := 79%positive.
Definition _i : ident := 75%positive.
Definition _idx : ident := 73%positive.
Definition _key : ident := 62%positive.
Definition _l : ident := 54%positive.
Definition _lkey : ident := 63%positive.
Definition _lock_t : ident := 2%positive.
Definition _lvalue : ident := 65%positive.
Definition _m_entries : ident := 72%positive.
Definition _main : ident := 61%positive.
Definition _malloc : ident := 68%positive.
Definition _n : ident := 69%positive.
Definition _p : ident := 70%positive.
Definition _prev_key : ident := 76%positive.
Definition _probed_key : ident := 78%positive.
Definition _release : ident := 52%positive.
Definition _set_item : ident := 77%positive.
Definition _simulate_atomic_CAS : ident := 60%positive.
Definition _simulate_atomic_load : ident := 56%positive.
Definition _simulate_atomic_store : ident := 58%positive.
Definition _surely_malloc : ident := 71%positive.
Definition _tgt : ident := 53%positive.
Definition _v : ident := 57%positive.
Definition _value : ident := 64%positive.
Definition _x : ident := 55%positive.
Definition _t'1 : ident := 80%positive.
Definition _t'2 : ident := 81%positive.

Definition f_surely_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Etempvar _n tuint) :: nil))
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tvoid)) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Sreturn (Some (Etempvar _p (tptr tvoid))))))
|}.

Definition v_m_entries := {|
  gvar_info := (tarray (tptr (Tstruct _entry noattr)) 20);
  gvar_init := (Init_space 80 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_set_item := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, tint) :: (_value, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_idx, tint) :: (_e, (tptr (Tstruct _entry noattr))) ::
               (_i, (tptr tint)) :: (_l, (tptr (Tstruct _lock_t noattr))) ::
               (_prev_key, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _idx (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _e
          (Ederef
            (Ebinop Oadd
              (Evar _m_entries (tarray (tptr (Tstruct _entry noattr)) 20))
              (Etempvar _idx tint) (tptr (tptr (Tstruct _entry noattr))))
            (tptr (Tstruct _entry noattr))))
        (Ssequence
          (Sset _i
            (Eaddrof
              (Efield
                (Ederef (Etempvar _e (tptr (Tstruct _entry noattr)))
                  (Tstruct _entry noattr)) _key tint) (tptr tint)))
          (Ssequence
            (Sset _l
              (Efield
                (Ederef (Etempvar _e (tptr (Tstruct _entry noattr)))
                  (Tstruct _entry noattr)) _lkey
                (tptr (Tstruct _lock_t noattr))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _simulate_atomic_CAS (Tfunction
                                               (Tcons (tptr tint)
                                                 (Tcons
                                                   (tptr (Tstruct _lock_t noattr))
                                                   (Tcons tint
                                                     (Tcons tint Tnil))))
                                               tint cc_default))
                  ((Etempvar _i (tptr tint)) ::
                   (Etempvar _l (tptr (Tstruct _lock_t noattr))) ::
                   (Econst_int (Int.repr 0) tint) :: (Etempvar _key tint) ::
                   nil))
                (Sset _prev_key (Etempvar _t'1 tint)))
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _prev_key tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Sset _t'2 (Econst_int (Int.repr 1) tint))
                  (Sset _t'2
                    (Ecast
                      (Ebinop Oeq (Etempvar _prev_key tint)
                        (Etempvar _key tint) tint) tbool)))
                (Sifthenelse (Etempvar _t'2 tint)
                  (Ssequence
                    (Sset _i
                      (Eaddrof
                        (Efield
                          (Ederef
                            (Etempvar _e (tptr (Tstruct _entry noattr)))
                            (Tstruct _entry noattr)) _value tint)
                        (tptr tint)))
                    (Ssequence
                      (Sset _l
                        (Efield
                          (Ederef
                            (Etempvar _e (tptr (Tstruct _entry noattr)))
                            (Tstruct _entry noattr)) _lvalue
                          (tptr (Tstruct _lock_t noattr))))
                      (Ssequence
                        (Scall None
                          (Evar _simulate_atomic_store (Tfunction
                                                         (Tcons (tptr tint)
                                                           (Tcons
                                                             (tptr (Tstruct _lock_t noattr))
                                                             (Tcons tint
                                                               Tnil))) tvoid
                                                         cc_default))
                          ((Etempvar _i (tptr tint)) ::
                           (Etempvar _l (tptr (Tstruct _lock_t noattr))) ::
                           (Etempvar _value tint) :: nil))
                        (Sreturn None))))
                  Sskip)))))))
    (Sset _idx
      (Ebinop Oadd (Etempvar _idx tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_get_item := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_key, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_idx, tint) :: (_e, (tptr (Tstruct _entry noattr))) ::
               (_i, (tptr tint)) :: (_l, (tptr (Tstruct _lock_t noattr))) ::
               (_probed_key, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _idx (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _e
          (Ederef
            (Ebinop Oadd
              (Evar _m_entries (tarray (tptr (Tstruct _entry noattr)) 20))
              (Etempvar _idx tint) (tptr (tptr (Tstruct _entry noattr))))
            (tptr (Tstruct _entry noattr))))
        (Ssequence
          (Sset _i
            (Eaddrof
              (Efield
                (Ederef (Etempvar _e (tptr (Tstruct _entry noattr)))
                  (Tstruct _entry noattr)) _key tint) (tptr tint)))
          (Ssequence
            (Sset _l
              (Efield
                (Ederef (Etempvar _e (tptr (Tstruct _entry noattr)))
                  (Tstruct _entry noattr)) _lkey
                (tptr (Tstruct _lock_t noattr))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _simulate_atomic_load (Tfunction
                                                (Tcons (tptr tint)
                                                  (Tcons
                                                    (tptr (Tstruct _lock_t noattr))
                                                    Tnil)) tint cc_default))
                  ((Etempvar _i (tptr tint)) ::
                   (Etempvar _l (tptr (Tstruct _lock_t noattr))) :: nil))
                (Sset _probed_key (Etempvar _t'1 tint)))
              (Ssequence
                (Sifthenelse (Ebinop Oeq (Etempvar _probed_key tint)
                               (Etempvar _key tint) tint)
                  (Ssequence
                    (Sset _i
                      (Eaddrof
                        (Efield
                          (Ederef
                            (Etempvar _e (tptr (Tstruct _entry noattr)))
                            (Tstruct _entry noattr)) _value tint)
                        (tptr tint)))
                    (Ssequence
                      (Sset _l
                        (Efield
                          (Ederef
                            (Etempvar _e (tptr (Tstruct _entry noattr)))
                            (Tstruct _entry noattr)) _lvalue
                          (tptr (Tstruct _lock_t noattr))))
                      (Ssequence
                        (Scall (Some _t'2)
                          (Evar _simulate_atomic_load (Tfunction
                                                        (Tcons (tptr tint)
                                                          (Tcons
                                                            (tptr (Tstruct _lock_t noattr))
                                                            Tnil)) tint
                                                        cc_default))
                          ((Etempvar _i (tptr tint)) ::
                           (Etempvar _l (tptr (Tstruct _lock_t noattr))) ::
                           nil))
                        (Sreturn (Some (Etempvar _t'2 tint))))))
                  Sskip)
                (Sifthenelse (Ebinop Oeq (Etempvar _probed_key tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  Sskip)))))))
    (Sset _idx
      (Ebinop Oadd (Etempvar _idx tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _lock_t Struct ((_a, (tarray (tptr tvoid) 4)) :: nil) noattr ::
 Composite _entry Struct
   ((_key, tint) :: (_lkey, (tptr (Tstruct _lock_t noattr))) ::
    (_value, tint) :: (_lvalue, (tptr (Tstruct _lock_t noattr))) :: nil)
   noattr :: nil).

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
   Gfun(External (EF_runtime "__i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___i64_dtou,
   Gfun(External (EF_runtime "__i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___i64_stod,
   Gfun(External (EF_runtime "__i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___i64_utod,
   Gfun(External (EF_runtime "__i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___i64_stof,
   Gfun(External (EF_runtime "__i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___i64_utof,
   Gfun(External (EF_runtime "__i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___i64_sdiv,
   Gfun(External (EF_runtime "__i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_udiv,
   Gfun(External (EF_runtime "__i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_smod,
   Gfun(External (EF_runtime "__i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umod,
   Gfun(External (EF_runtime "__i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_shl,
   Gfun(External (EF_runtime "__i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___i64_shr,
   Gfun(External (EF_runtime "__i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___i64_sar,
   Gfun(External (EF_runtime "__i64_sar"
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
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_simulate_atomic_load,
   Gfun(External (EF_external "simulate_atomic_load"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tint) (Tcons (tptr (Tstruct _lock_t noattr)) Tnil)) tint
     cc_default)) ::
 (_simulate_atomic_store,
   Gfun(External (EF_external "simulate_atomic_store"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tint)
       (Tcons (tptr (Tstruct _lock_t noattr)) (Tcons tint Tnil))) tvoid
     cc_default)) ::
 (_simulate_atomic_CAS,
   Gfun(External (EF_external "simulate_atomic_CAS"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tint)
       (Tcons (tptr (Tstruct _lock_t noattr)) (Tcons tint (Tcons tint Tnil))))
     tint cc_default)) :: (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_m_entries, Gvar v_m_entries) :: (_set_item, Gfun(Internal f_set_item)) ::
 (_get_item, Gfun(Internal f_get_item)) :: nil);
prog_public :=
(_get_item :: _set_item :: _m_entries :: _surely_malloc ::
 _simulate_atomic_CAS :: _simulate_atomic_store :: _simulate_atomic_load ::
 _malloc :: _exit :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fsqrt :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
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

