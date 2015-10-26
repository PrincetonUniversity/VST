Require Import Clightdefs.

Local Open Scope Z_scope.

Definition ___builtin_bswap : ident := 40%positive.
Definition ___i64_utof : ident := 32%positive.
Definition ___builtin_annot : ident := 16%positive.
Definition ___i64_shr : ident := 38%positive.
Definition ___builtin_fmax : ident := 46%positive.
Definition _ser : ident := 62%positive.
Definition _p : ident := 54%positive.
Definition ___compcert_va_int64 : ident := 24%positive.
Definition ___builtin_va_end : ident := 22%positive.
Definition ___builtin_annot_intval : ident := 17%positive.
Definition _serialize : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition ___builtin_fnmadd : ident := 50%positive.
Definition ___builtin_clz : ident := 43%positive.
Definition _y : ident := 12%positive.
Definition _des : ident := 63%positive.
Definition ___builtin_read32_reversed : ident := 53%positive.
Definition ___builtin_fmin : ident := 47%positive.
Definition _message : ident := 10%positive.
Definition _length : ident := 57%positive.
Definition ___builtin_ctz : ident := 44%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition ___i64_umod : ident := 36%positive.
Definition ___i64_stof : ident := 31%positive.
Definition ___builtin_fabs : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition ___compcert_va_composite : ident := 26%positive.
Definition ___builtin_va_start : ident := 19%positive.
Definition ___i64_sar : ident := 39%positive.
Definition _len : ident := 61%positive.
Definition _x : ident := 11%positive.
Definition ___builtin_fmsub : ident := 49%positive.
Definition _intpair_message : ident := 59%positive.
Definition ___i64_shl : ident := 37%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition _intpair_deserialize : ident := 58%positive.
Definition ___i64_dtou : ident := 28%positive.
Definition _bufsize : ident := 7%positive.
Definition ___builtin_bswap16 : ident := 42%positive.
Definition ___builtin_va_copy : ident := 21%positive.
Definition ___builtin_membar : ident := 18%positive.
Definition _deserialize : ident := 9%positive.
Definition _main : ident := 64%positive.
Definition ___builtin_read16_reversed : ident := 52%positive.
Definition ___builtin_fsqrt : ident := 45%positive.
Definition ___builtin_bswap32 : ident := 41%positive.
Definition _intpair : ident := 13%positive.
Definition ___i64_dtos : ident := 27%positive.
Definition ___i64_sdiv : ident := 33%positive.
Definition _intpair_serialize : ident := 56%positive.
Definition ___compcert_va_float64 : ident := 25%positive.
Definition ___builtin_memcpy_aligned : ident := 15%positive.
Definition _q : ident := 60%positive.
Definition ___i64_udiv : ident := 34%positive.
Definition ___i64_stod : ident := 29%positive.
Definition _buf : ident := 55%positive.
Definition ___i64_smod : ident := 35%positive.
Definition ___i64_utod : ident := 30%positive.
Definition ___compcert_va_int32 : ident := 23%positive.
Definition ___builtin_fnmsub : ident := 51%positive.
Definition ___builtin_fmadd : ident := 48%positive.
Definition ___builtin_va_arg : ident := 20%positive.

Definition f_intpair_serialize := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _intpair noattr))) ::
                (_buf, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, tint) :: (_y, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _intpair noattr)))
        (Tstruct _intpair noattr)) _x tint))
  (Ssequence
    (Sset _y
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _intpair noattr)))
          (Tstruct _intpair noattr)) _y tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _buf (tptr tuchar)) (tptr tint))
            (Econst_int (Int.repr 0) tint) (tptr tint)) tint)
        (Etempvar _x tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _buf (tptr tuchar)) (tptr tint))
              (Econst_int (Int.repr 1) tint) (tptr tint)) tint)
          (Etempvar _y tint))
        (Sreturn (Some (Econst_int (Int.repr 8) tint)))))))
|}.

Definition f_intpair_deserialize := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _intpair noattr))) ::
                (_buf, (tptr tuchar)) :: (_length, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, tint) :: (_y, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x
    (Ederef
      (Ebinop Oadd (Ecast (Etempvar _buf (tptr tuchar)) (tptr tint))
        (Econst_int (Int.repr 0) tint) (tptr tint)) tint))
  (Ssequence
    (Sset _y
      (Ederef
        (Ebinop Oadd (Ecast (Etempvar _buf (tptr tuchar)) (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint)) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _intpair noattr)))
            (Tstruct _intpair noattr)) _x tint) (Etempvar _x tint))
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _intpair noattr)))
            (Tstruct _intpair noattr)) _y tint) (Etempvar _y tint)))))
|}.

Definition v_intpair_message := {|
  gvar_info := (Tstruct _message noattr);
  gvar_init := (Init_int32 (Int.repr 8) ::
                Init_addrof _intpair_serialize (Int.repr 0) ::
                Init_addrof _intpair_deserialize (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_p, (Tstruct _intpair noattr)) ::
              (_q, (Tstruct _intpair noattr)) :: (_buf, (tarray tuchar 8)) ::
              nil);
  fn_temps := ((_len, tint) :: (_x, tint) :: (_y, tint) ::
               (_ser,
                (tptr (Tfunction
                        (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint
                        cc_default))) ::
               (_des,
                (tptr (Tfunction
                        (Tcons (tptr tvoid)
                          (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                        cc_default))) :: (65%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _p (Tstruct _intpair noattr)) _x tint)
    (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Sassign (Efield (Evar _p (Tstruct _intpair noattr)) _y tint)
      (Econst_int (Int.repr 2) tint))
    (Ssequence
      (Sset _ser
        (Efield (Evar _intpair_message (Tstruct _message noattr)) _serialize
          (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil))
                  tint cc_default))))
      (Ssequence
        (Ssequence
          (Scall (Some 65%positive)
            (Etempvar _ser (tptr (Tfunction
                                   (Tcons (tptr tvoid)
                                     (Tcons (tptr tuchar) Tnil)) tint
                                   cc_default)))
            ((Eaddrof (Evar _p (Tstruct _intpair noattr))
               (tptr (Tstruct _intpair noattr))) ::
             (Evar _buf (tarray tuchar 8)) :: nil))
          (Sset _len (Etempvar 65%positive tint)))
        (Ssequence
          (Sset _des
            (Efield (Evar _intpair_message (Tstruct _message noattr))
              _deserialize
              (tptr (Tfunction
                      (Tcons (tptr tvoid)
                        (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                      cc_default))))
          (Ssequence
            (Scall None
              (Etempvar _des (tptr (Tfunction
                                     (Tcons (tptr tvoid)
                                       (Tcons (tptr tuchar)
                                         (Tcons tint Tnil))) tvoid
                                     cc_default)))
              ((Eaddrof (Evar _q (Tstruct _intpair noattr))
                 (tptr (Tstruct _intpair noattr))) ::
               (Evar _buf (tarray tuchar 8)) ::
               (Econst_int (Int.repr 8) tint) :: nil))
            (Ssequence
              (Sset _x (Efield (Evar _q (Tstruct _intpair noattr)) _x tint))
              (Ssequence
                (Sset _y
                  (Efield (Evar _q (Tstruct _intpair noattr)) _y tint))
                (Sreturn (Some (Ebinop Oadd (Etempvar _x tint)
                                 (Etempvar _y tint) tint)))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _message Struct
   ((_bufsize, tint) ::
    (_serialize,
     (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint
             cc_default))) ::
    (_deserialize,
     (tptr (Tfunction
             (Tcons (tptr tvoid) (Tcons (tptr tuchar) (Tcons tint Tnil)))
             tvoid cc_default))) :: nil)
   noattr ::
 Composite _intpair Struct ((_x, tint) :: (_y, tint) :: nil) noattr :: nil).

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
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin ___builtin_membar
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
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
 (___compcert_va_composite,
   Gfun(External (EF_external ___compcert_va_composite
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___i64_dtos,
   Gfun(External (EF_external ___i64_dtos
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___i64_dtou,
   Gfun(External (EF_external ___i64_dtou
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___i64_stod,
   Gfun(External (EF_external ___i64_stod
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___i64_utod,
   Gfun(External (EF_external ___i64_utod
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___i64_stof,
   Gfun(External (EF_external ___i64_stof
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___i64_utof,
   Gfun(External (EF_external ___i64_utof
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___i64_sdiv,
   Gfun(External (EF_external ___i64_sdiv
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_udiv,
   Gfun(External (EF_external ___i64_udiv
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_smod,
   Gfun(External (EF_external ___i64_smod
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umod,
   Gfun(External (EF_external ___i64_umod
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_shl,
   Gfun(External (EF_external ___i64_shl
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___i64_shr,
   Gfun(External (EF_external ___i64_shr
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___i64_sar,
   Gfun(External (EF_external ___i64_sar
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
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
 (___builtin_clz,
   Gfun(External (EF_builtin ___builtin_clz
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin ___builtin_ctz
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
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
 (_intpair_serialize, Gfun(Internal f_intpair_serialize)) ::
 (_intpair_deserialize, Gfun(Internal f_intpair_deserialize)) ::
 (_intpair_message, Gvar v_intpair_message) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: _intpair_message :: _intpair_deserialize :: _intpair_serialize ::
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

