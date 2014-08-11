Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _v : ident := 40%positive.
Definition _head : ident := 32%positive.
Definition ___compcert_va_int64 : ident := 16%positive.
Definition _sumlist : ident := 38%positive.
Definition ___builtin_fmadd : ident := 24%positive.
Definition ___builtin_fmax : ident := 22%positive.
Definition ___compcert_va_float64 : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition _main : ident := 43%positive.
Definition ___builtin_va_arg : ident := 12%positive.
Definition ___builtin_annot_intval : ident := 10%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _t : ident := 36%positive.
Definition _tail : ident := 31%positive.
Definition ___builtin_va_end : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition ___builtin_fnmadd : ident := 26%positive.
Definition ___builtin_bswap32 : ident := 19%positive.
Definition _w : ident := 39%positive.
Definition ___builtin_va_start : ident := 11%positive.
Definition _h : ident := 37%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition ___builtin_read16_reversed : ident := 28%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition _r : ident := 42%positive.
Definition ___builtin_fsqrt : ident := 21%positive.
Definition ___builtin_bswap : ident := 18%positive.
Definition ___builtin_annot : ident := 9%positive.
Definition _reverse : ident := 41%positive.
Definition ___builtin_va_copy : ident := 13%positive.
Definition ___builtin_fnmsub : ident := 27%positive.
Definition _three : ident := 33%positive.
Definition ___builtin_fmsub : ident := 25%positive.
Definition ___compcert_va_int32 : ident := 15%positive.
Definition _p : ident := 34%positive.
Definition ___builtin_read32_reversed : ident := 29%positive.
Definition _s : ident := 35%positive.
Definition _struct_list : ident := 30%positive.
Definition ___builtin_fmin : ident := 23%positive.
Definition ___builtin_bswap16 : ident := 20%positive.
Definition _r' : ident := 44%positive.
Definition _s' : ident := 45%positive.

Definition t_struct_list :=
   (Tstruct _struct_list
     (Fcons _head tint (Fcons _tail (Tcomp_ptr _struct_list noattr) Fnil))
     noattr).

Definition v_three := {|
  gvar_info := (tarray t_struct_list 3);
  gvar_init := (Init_int32 (Int.repr 1) :: Init_addrof _three (Int.repr 8) ::
                Init_int32 (Int.repr 2) ::
                Init_addrof _three (Int.repr 16) ::
                Init_int32 (Int.repr 3) :: Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_sumlist := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr t_struct_list)) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, tint) :: (_t, (tptr t_struct_list)) :: (_h, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _s (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _t (Etempvar _p (tptr t_struct_list)))
    (Ssequence
      (Swhile
        (Etempvar _t (tptr t_struct_list))
        (Ssequence
          (Sset _h
            (Efield (Ederef (Etempvar _t (tptr t_struct_list)) t_struct_list)
              _head tint))
          (Ssequence
            (Sset _t
              (Efield
                (Ederef (Etempvar _t (tptr t_struct_list)) t_struct_list)
                _tail (tptr t_struct_list)))
            (Sset _s
              (Ebinop Oadd (Etempvar _s tint) (Etempvar _h tint) tint)))))
      (Sreturn (Some (Etempvar _s tint))))))
|}.

Definition f_reverse := {|
  fn_return := (tptr t_struct_list);
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr t_struct_list)) :: nil);
  fn_vars := nil;
  fn_temps := ((_w, (tptr t_struct_list)) :: (_t, (tptr t_struct_list)) ::
               (_v, (tptr t_struct_list)) :: nil);
  fn_body :=
(Ssequence
  (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sset _v (Etempvar _p (tptr t_struct_list)))
    (Ssequence
      (Swhile
        (Etempvar _v (tptr t_struct_list))
        (Ssequence
          (Sset _t
            (Efield (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list)
              _tail (tptr t_struct_list)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list)
                _tail (tptr t_struct_list))
              (Etempvar _w (tptr t_struct_list)))
            (Ssequence
              (Sset _w (Etempvar _v (tptr t_struct_list)))
              (Sset _v (Etempvar _t (tptr t_struct_list)))))))
      (Sreturn (Some (Etempvar _w (tptr t_struct_list)))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_r, (tptr t_struct_list)) :: (_s, tint) :: (_s', tint) ::
               (_r', (tptr t_struct_list)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _r')
      (Evar _reverse (Tfunction (Tcons (tptr t_struct_list) Tnil)
                       (tptr t_struct_list) cc_default))
      ((Evar _three (tarray t_struct_list 3)) :: nil))
    (Sset _r (Etempvar _r' (tptr t_struct_list))))
  (Ssequence
    (Ssequence
      (Scall (Some _s')
        (Evar _sumlist (Tfunction (Tcons (tptr t_struct_list) Tnil) tint
                         cc_default))
        ((Etempvar _r (tptr t_struct_list)) :: nil))
      (Sset _s (Etempvar _s' tint)))
    (Sreturn (Some (Etempvar _s tint)))))
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
     tvoid cc_default)) :: (_three, Gvar v_three) ::
 (_sumlist, Gfun(Internal f_sumlist)) ::
 (_reverse, Gfun(Internal f_reverse)) :: (_main, Gfun(Internal f_main)) ::
 nil);
prog_main := _main
|}.

