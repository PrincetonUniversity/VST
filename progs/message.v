Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _length : ident := 40%positive.
Definition _bufsize : ident := 32%positive.
Definition ___compcert_va_int64 : ident := 16%positive.
Definition _buf : ident := 38%positive.
Definition _des : ident := 46%positive.
Definition ___builtin_fmadd : ident := 24%positive.
Definition ___builtin_fmax : ident := 22%positive.
Definition ___compcert_va_float64 : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition _q : ident := 43%positive.
Definition ___builtin_va_arg : ident := 12%positive.
Definition _main : ident := 47%positive.
Definition ___builtin_annot_intval : ident := 10%positive.
Definition _len : ident := 44%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _struct_intpair : ident := 36%positive.
Definition _serialize : ident := 31%positive.
Definition ___builtin_va_end : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition ___builtin_fnmadd : ident := 26%positive.
Definition ___builtin_bswap32 : ident := 19%positive.
Definition _intpair_serialize : ident := 39%positive.
Definition ___builtin_va_start : ident := 11%positive.
Definition _p : ident := 37%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition ___builtin_read16_reversed : ident := 28%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition _intpair_message : ident := 42%positive.
Definition ___builtin_fsqrt : ident := 21%positive.
Definition ___builtin_bswap : ident := 18%positive.
Definition ___builtin_annot : ident := 9%positive.
Definition _ser : ident := 45%positive.
Definition _intpair_deserialize : ident := 41%positive.
Definition ___builtin_va_copy : ident := 13%positive.
Definition ___builtin_fnmsub : ident := 27%positive.
Definition _struct_message : ident := 33%positive.
Definition ___builtin_fmsub : ident := 25%positive.
Definition ___compcert_va_int32 : ident := 15%positive.
Definition _y : ident := 34%positive.
Definition ___builtin_read32_reversed : ident := 29%positive.
Definition _x : ident := 35%positive.
Definition _deserialize : ident := 30%positive.
Definition ___builtin_fmin : ident := 23%positive.
Definition ___builtin_bswap16 : ident := 20%positive.
Definition _len' : ident := 48%positive.

Definition t_struct_message :=
   (Tstruct _struct_message
     (Fcons _bufsize tint
       (Fcons _serialize
         (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil))
                 tint cc_default))
         (Fcons _deserialize
           (tptr (Tfunction
                   (Tcons (tptr tvoid)
                     (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                   cc_default)) Fnil))) noattr).
Definition t_struct_intpair :=
   (Tstruct _struct_intpair (Fcons _x tint (Fcons _y tint Fnil)) noattr).

Definition f_intpair_serialize := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr t_struct_intpair)) :: (_buf, (tptr tuchar)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_x, tint) :: (_y, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x
    (Efield (Ederef (Etempvar _p (tptr t_struct_intpair)) t_struct_intpair)
      _x tint))
  (Ssequence
    (Sset _y
      (Efield (Ederef (Etempvar _p (tptr t_struct_intpair)) t_struct_intpair)
        _y tint))
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
  fn_params := ((_p, (tptr t_struct_intpair)) :: (_buf, (tptr tuchar)) ::
                (_length, tint) :: nil);
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
          (Ederef (Etempvar _p (tptr t_struct_intpair)) t_struct_intpair) _x
          tint) (Etempvar _x tint))
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr t_struct_intpair)) t_struct_intpair) _y
          tint) (Etempvar _y tint)))))
|}.

Definition v_intpair_message := {|
  gvar_info := t_struct_message;
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
  fn_vars := ((_p, t_struct_intpair) :: (_q, t_struct_intpair) ::
              (_buf, (tarray tuchar 8)) :: nil);
  fn_temps := ((_len, tint) :: (_x, tint) :: (_y, tint) ::
               (_ser,
                (tptr (Tfunction
                        (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint
                        cc_default))) ::
               (_des,
                (tptr (Tfunction
                        (Tcons (tptr tvoid)
                          (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                        cc_default))) :: (_len', tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _p t_struct_intpair) _x tint)
    (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Sassign (Efield (Evar _p t_struct_intpair) _y tint)
      (Econst_int (Int.repr 2) tint))
    (Ssequence
      (Sset _ser
        (Efield (Evar _intpair_message t_struct_message) _serialize
          (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil))
                  tint cc_default))))
      (Ssequence
        (Ssequence
          (Scall (Some _len')
            (Etempvar _ser (tptr (Tfunction
                                   (Tcons (tptr tvoid)
                                     (Tcons (tptr tuchar) Tnil)) tint
                                   cc_default)))
            ((Eaddrof (Evar _p t_struct_intpair) (tptr t_struct_intpair)) ::
             (Evar _buf (tarray tuchar 8)) :: nil))
          (Sset _len (Etempvar _len' tint)))
        (Ssequence
          (Sset _des
            (Efield (Evar _intpair_message t_struct_message) _deserialize
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
              ((Eaddrof (Evar _q t_struct_intpair) (tptr t_struct_intpair)) ::
               (Evar _buf (tarray tuchar 8)) ::
               (Econst_int (Int.repr 8) tint) :: nil))
            (Ssequence
              (Sset _x (Efield (Evar _q t_struct_intpair) _x tint))
              (Ssequence
                (Sset _y (Efield (Evar _q t_struct_intpair) _y tint))
                (Sreturn (Some (Ebinop Oadd (Etempvar _x tint)
                                 (Etempvar _y tint) tint)))))))))))
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
 (_intpair_serialize, Gfun(Internal f_intpair_serialize)) ::
 (_intpair_deserialize, Gfun(Internal f_intpair_deserialize)) ::
 (_intpair_message, Gvar v_intpair_message) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_main := _main
|}.

