
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition ___builtin_annot : ident := 3%positive.
Definition ___builtin_annot_intval : ident := 4%positive.
Definition ___builtin_bswap : ident := 27%positive.
Definition ___builtin_bswap16 : ident := 29%positive.
Definition ___builtin_bswap32 : ident := 28%positive.
Definition ___builtin_clz : ident := 30%positive.
Definition ___builtin_clzl : ident := 31%positive.
Definition ___builtin_clzll : ident := 32%positive.
Definition ___builtin_ctz : ident := 33%positive.
Definition ___builtin_ctzl : ident := 34%positive.
Definition ___builtin_ctzll : ident := 35%positive.
Definition ___builtin_debug : ident := 48%positive.
Definition ___builtin_fabs : ident := 1%positive.
Definition ___builtin_fmadd : ident := 39%positive.
Definition ___builtin_fmax : ident := 37%positive.
Definition ___builtin_fmin : ident := 38%positive.
Definition ___builtin_fmsub : ident := 40%positive.
Definition ___builtin_fnmadd : ident := 41%positive.
Definition ___builtin_fnmsub : ident := 42%positive.
Definition ___builtin_fsqrt : ident := 36%positive.
Definition ___builtin_membar : ident := 5%positive.
Definition ___builtin_memcpy_aligned : ident := 2%positive.
Definition ___builtin_nop : ident := 47%positive.
Definition ___builtin_read16_reversed : ident := 43%positive.
Definition ___builtin_read32_reversed : ident := 44%positive.
Definition ___builtin_va_arg : ident := 7%positive.
Definition ___builtin_va_copy : ident := 8%positive.
Definition ___builtin_va_end : ident := 9%positive.
Definition ___builtin_va_start : ident := 6%positive.
Definition ___builtin_write16_reversed : ident := 45%positive.
Definition ___builtin_write32_reversed : ident := 46%positive.
Definition ___compcert_va_composite : ident := 13%positive.
Definition ___compcert_va_float64 : ident := 12%positive.
Definition ___compcert_va_int32 : ident := 10%positive.
Definition ___compcert_va_int64 : ident := 11%positive.
Definition ___i64_dtos : ident := 14%positive.
Definition ___i64_dtou : ident := 15%positive.
Definition ___i64_sar : ident := 26%positive.
Definition ___i64_sdiv : ident := 20%positive.
Definition ___i64_shl : ident := 24%positive.
Definition ___i64_shr : ident := 25%positive.
Definition ___i64_smod : ident := 22%positive.
Definition ___i64_stod : ident := 16%positive.
Definition ___i64_stof : ident := 18%positive.
Definition ___i64_udiv : ident := 21%positive.
Definition ___i64_umod : ident := 23%positive.
Definition ___i64_utod : ident := 17%positive.
Definition ___i64_utof : ident := 19%positive.
Definition _a : ident := 70%positive.
Definition _arena : ident := 57%positive.
Definition _b : ident := 71%positive.
Definition _copytree : ident := 66%positive.
Definition _depth : ident := 59%positive.
Definition _i : ident := 67%positive.
Definition _int_or_ptr_to_int : ident := 52%positive.
Definition _int_or_ptr_to_ptr : ident := 53%positive.
Definition _int_to_int_or_ptr : ident := 54%positive.
Definition _leaf : ident := 56%positive.
Definition _main : ident := 73%positive.
Definition _maketree : ident := 64%positive.
Definition _next : ident := 58%positive.
Definition _p : ident := 61%positive.
Definition _print : ident := 72%positive.
Definition _print_int : ident := 69%positive.
Definition _print_intx : ident := 68%positive.
Definition _ptr_to_int_or_ptr : ident := 55%positive.
Definition _putchar : ident := 49%positive.
Definition _q : ident := 62%positive.
Definition _r : ident := 60%positive.
Definition _s : ident := 63%positive.
Definition _t : ident := 65%positive.
Definition _test_int_or_ptr : ident := 51%positive.
Definition _x : ident := 50%positive.
Definition _t'1 : ident := 74%positive.
Definition _t'2 : ident := 75%positive.
Definition _t'3 : ident := 76%positive.
Definition _t'4 : ident := 77%positive.
Definition _t'5 : ident := 78%positive.

Definition f_test_int_or_ptr := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Ecast (Etempvar _x (tptr tvoid)) tuint)
                   (Econst_int (Int.repr 1) tint) tuint) tint)))
|}.

Definition f_int_or_ptr_to_int := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x (tptr tvoid)) tuint)))
|}.

Definition f_int_or_ptr_to_ptr := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x (tptr tvoid)) (tptr tvoid))))
|}.

Definition f_int_to_int_or_ptr := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_x, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x tuint) (tptr tvoid))))
|}.

Definition f_ptr_to_int_or_ptr := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x (tptr tvoid)) (tptr tvoid))))
|}.

Definition v_leaf := {|
  gvar_info := tint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_arena := {|
  gvar_info := (tarray (tptr tvoid) 1000);
  gvar_init := (Init_space 4000 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_next := {|
  gvar_info := (tptr (tptr tvoid));
  gvar_init := (Init_addrof _arena (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_maketree := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_depth, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, (tptr tvoid)) :: (_p, (tptr tvoid)) ::
               (_q, (tptr tvoid)) :: (_s, (tptr (tptr tvoid))) ::
               (_t'5, (tptr tvoid)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _depth tint)
               (Econst_int (Int.repr 0) tint) tint)
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'1 (Evar _leaf tint))
          (Sassign (Evar _leaf tint)
            (Ebinop Oadd (Etempvar _t'1 tint) (Econst_int (Int.repr 1) tint)
              tint)))
        (Scall (Some _t'2)
          (Evar _int_to_int_or_ptr (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                     cc_default))
          ((Ebinop Oor
             (Ebinop Oshl (Etempvar _t'1 tint) (Econst_int (Int.repr 1) tint)
               tint) (Econst_int (Int.repr 1) tint) tint) :: nil)))
      (Sset _r (Etempvar _t'2 (tptr tvoid))))
    (Sreturn (Some (Etempvar _r (tptr tvoid)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'3)
        (Evar _maketree (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
        ((Ebinop Osub (Etempvar _depth tint) (Econst_int (Int.repr 1) tint)
           tint) :: nil))
      (Sset _p (Etempvar _t'3 (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'4)
          (Evar _maketree (Tfunction (Tcons tint Tnil) (tptr tvoid)
                            cc_default))
          ((Ebinop Osub (Etempvar _depth tint) (Econst_int (Int.repr 1) tint)
             tint) :: nil))
        (Sset _q (Etempvar _t'4 (tptr tvoid))))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _next (tptr (tptr tvoid)))
              (Econst_int (Int.repr 0) tint) (tptr (tptr tvoid)))
            (tptr tvoid)) (Etempvar _p (tptr tvoid)))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _next (tptr (tptr tvoid)))
                (Econst_int (Int.repr 1) tint) (tptr (tptr tvoid)))
              (tptr tvoid)) (Etempvar _q (tptr tvoid)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _ptr_to_int_or_ptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                           (tptr tvoid) cc_default))
                ((Evar _next (tptr (tptr tvoid))) :: nil))
              (Sset _r (Etempvar _t'5 (tptr tvoid))))
            (Ssequence
              (Sassign (Evar _next (tptr (tptr tvoid)))
                (Ebinop Oadd (Evar _next (tptr (tptr tvoid)))
                  (Econst_int (Int.repr 2) tint) (tptr (tptr tvoid))))
              (Sreturn (Some (Etempvar _r (tptr tvoid)))))))))))
|}.

Definition f_copytree := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, (tptr tvoid)) :: (_p, (tptr tvoid)) ::
               (_q, (tptr tvoid)) :: (_s, (tptr (tptr tvoid))) ::
               (_t'5, tint) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'5)
    (Evar _test_int_or_ptr (Tfunction (Tcons (tptr tvoid) Tnil) tint
                             cc_default))
    ((Etempvar _t (tptr tvoid)) :: nil))
  (Sifthenelse (Etempvar _t'5 tint)
    (Sreturn (Some (Etempvar _t (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _int_or_ptr_to_ptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                     (tptr tvoid) cc_default))
          ((Etempvar _t (tptr tvoid)) :: nil))
        (Sset _s (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (tptr tvoid)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _copytree (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid)
                              cc_default))
            ((Ederef
               (Ebinop Oadd (Etempvar _s (tptr (tptr tvoid)))
                 (Econst_int (Int.repr 0) tint) (tptr (tptr tvoid)))
               (tptr tvoid)) :: nil))
          (Sset _p (Etempvar _t'2 (tptr tvoid))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _copytree (Tfunction (Tcons (tptr tvoid) Tnil)
                                (tptr tvoid) cc_default))
              ((Ederef
                 (Ebinop Oadd (Etempvar _s (tptr (tptr tvoid)))
                   (Econst_int (Int.repr 1) tint) (tptr (tptr tvoid)))
                 (tptr tvoid)) :: nil))
            (Sset _q (Etempvar _t'3 (tptr tvoid))))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _next (tptr (tptr tvoid)))
                  (Econst_int (Int.repr 0) tint) (tptr (tptr tvoid)))
                (tptr tvoid)) (Etempvar _p (tptr tvoid)))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _next (tptr (tptr tvoid)))
                    (Econst_int (Int.repr 1) tint) (tptr (tptr tvoid)))
                  (tptr tvoid)) (Etempvar _q (tptr tvoid)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _ptr_to_int_or_ptr (Tfunction
                                               (Tcons (tptr tvoid) Tnil)
                                               (tptr tvoid) cc_default))
                    ((Evar _next (tptr (tptr tvoid))) :: nil))
                  (Sset _r (Etempvar _t'4 (tptr tvoid))))
                (Ssequence
                  (Sassign (Evar _next (tptr (tptr tvoid)))
                    (Ebinop Oadd (Evar _next (tptr (tptr tvoid)))
                      (Econst_int (Int.repr 2) tint) (tptr (tptr tvoid))))
                  (Sreturn (Some (Etempvar _r (tptr tvoid)))))))))))))
|}.

Definition f_print_intx := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_i, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Ogt (Etempvar _i tuint) (Econst_int (Int.repr 0) tint)
               tint)
  (Ssequence
    (Scall None
      (Evar _print_intx (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Ebinop Odiv (Etempvar _i tuint) (Econst_int (Int.repr 10) tint)
         tuint) :: nil))
    (Scall None (Evar _putchar (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Ebinop Oadd (Econst_int (Int.repr 48) tint)
         (Ebinop Omod (Etempvar _i tuint) (Econst_int (Int.repr 10) tint)
           tuint) tuint) :: nil)))
  Sskip)
|}.

Definition f_print_int := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_i, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _i tuint) (Econst_int (Int.repr 0) tint)
               tint)
  (Scall None (Evar _putchar (Tfunction (Tcons tint Tnil) tint cc_default))
    ((Econst_int (Int.repr 48) tint) :: nil))
  (Scall None
    (Evar _print_intx (Tfunction (Tcons tuint Tnil) tvoid cc_default))
    ((Etempvar _i tuint) :: nil)))
|}.

Definition f_print := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_a, (tptr tvoid)) :: (_b, (tptr tvoid)) ::
               (_q, (tptr (tptr tvoid))) :: (_t'3, tint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'3)
    (Evar _test_int_or_ptr (Tfunction (Tcons (tptr tvoid) Tnil) tint
                             cc_default))
    ((Etempvar _p (tptr tvoid)) :: nil))
  (Sifthenelse (Etempvar _t'3 tint)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _int_or_ptr_to_int (Tfunction (Tcons (tptr tvoid) Tnil) tuint
                                     cc_default))
          ((Etempvar _p (tptr tvoid)) :: nil))
        (Sset _i (Etempvar _t'1 tuint)))
      (Scall None
        (Evar _print_int (Tfunction (Tcons tuint Tnil) tvoid cc_default))
        ((Ebinop Oshr (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
           tuint) :: nil)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _int_or_ptr_to_ptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                     (tptr tvoid) cc_default))
          ((Etempvar _p (tptr tvoid)) :: nil))
        (Sset _q (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr (tptr tvoid)))))
      (Ssequence
        (Sset _a
          (Ederef
            (Ebinop Oadd (Etempvar _q (tptr (tptr tvoid)))
              (Econst_int (Int.repr 0) tint) (tptr (tptr tvoid)))
            (tptr tvoid)))
        (Ssequence
          (Sset _b
            (Ederef
              (Ebinop Oadd (Etempvar _q (tptr (tptr tvoid)))
                (Econst_int (Int.repr 1) tint) (tptr (tptr tvoid)))
              (tptr tvoid)))
          (Ssequence
            (Scall None
              (Evar _putchar (Tfunction (Tcons tint Tnil) tint cc_default))
              ((Econst_int (Int.repr 40) tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _print (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                               cc_default))
                ((Etempvar _a (tptr tvoid)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _putchar (Tfunction (Tcons tint Tnil) tint
                                   cc_default))
                  ((Econst_int (Int.repr 44) tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _print (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                   cc_default))
                    ((Etempvar _b (tptr tvoid)) :: nil))
                  (Scall None
                    (Evar _putchar (Tfunction (Tcons tint Tnil) tint
                                     cc_default))
                    ((Econst_int (Int.repr 41) tint) :: nil)))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _maketree (Tfunction (Tcons tint Tnil) (tptr tvoid) cc_default))
        ((Econst_int (Int.repr 3) tint) :: nil))
      (Sset _p (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _copytree (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid)
                            cc_default)) ((Etempvar _p (tptr tvoid)) :: nil))
        (Sset _p (Etempvar _t'2 (tptr tvoid))))
      (Ssequence
        (Scall None
          (Evar _print (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _p (tptr tvoid)) :: nil))
        (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
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
 (_putchar,
   Gfun(External (EF_external "putchar"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (_test_int_or_ptr, Gfun(Internal f_test_int_or_ptr)) ::
 (_int_or_ptr_to_int, Gfun(Internal f_int_or_ptr_to_int)) ::
 (_int_or_ptr_to_ptr, Gfun(Internal f_int_or_ptr_to_ptr)) ::
 (_int_to_int_or_ptr, Gfun(Internal f_int_to_int_or_ptr)) ::
 (_ptr_to_int_or_ptr, Gfun(Internal f_ptr_to_int_or_ptr)) ::
 (_leaf, Gvar v_leaf) :: (_arena, Gvar v_arena) :: (_next, Gvar v_next) ::
 (_maketree, Gfun(Internal f_maketree)) ::
 (_copytree, Gfun(Internal f_copytree)) ::
 (_print_intx, Gfun(Internal f_print_intx)) ::
 (_print_int, Gfun(Internal f_print_int)) ::
 (_print, Gfun(Internal f_print)) :: (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: _print :: _print_int :: _print_intx :: _copytree :: _maketree ::
 _next :: _arena :: _leaf :: _ptr_to_int_or_ptr :: _int_to_int_or_ptr ::
 _int_or_ptr_to_ptr :: _int_or_ptr_to_int :: _test_int_or_ptr :: _putchar ::
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fsqrt :: ___builtin_ctzll ::
 ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll :: ___builtin_clzl ::
 ___builtin_clz :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___i64_sar :: ___i64_shr :: ___i64_shl :: ___i64_umod ::
 ___i64_smod :: ___i64_udiv :: ___i64_sdiv :: ___i64_utof :: ___i64_stof ::
 ___i64_utod :: ___i64_stod :: ___i64_dtou :: ___i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fabs :: nil);
prog_main := _main;
prog_types := composites;
prog_comp_env := make_composite_env composites;
prog_comp_env_eq := refl_equal _
|}.

