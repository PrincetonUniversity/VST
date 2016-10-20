
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition ___builtin_annot : ident := 7%positive.
Definition ___builtin_annot_intval : ident := 8%positive.
Definition ___builtin_bswap : ident := 31%positive.
Definition ___builtin_bswap16 : ident := 33%positive.
Definition ___builtin_bswap32 : ident := 32%positive.
Definition ___builtin_clz : ident := 34%positive.
Definition ___builtin_clzl : ident := 35%positive.
Definition ___builtin_clzll : ident := 36%positive.
Definition ___builtin_ctz : ident := 37%positive.
Definition ___builtin_ctzl : ident := 38%positive.
Definition ___builtin_ctzll : ident := 39%positive.
Definition ___builtin_debug : ident := 52%positive.
Definition ___builtin_fabs : ident := 5%positive.
Definition ___builtin_fmadd : ident := 43%positive.
Definition ___builtin_fmax : ident := 41%positive.
Definition ___builtin_fmin : ident := 42%positive.
Definition ___builtin_fmsub : ident := 44%positive.
Definition ___builtin_fnmadd : ident := 45%positive.
Definition ___builtin_fnmsub : ident := 46%positive.
Definition ___builtin_fsqrt : ident := 40%positive.
Definition ___builtin_membar : ident := 9%positive.
Definition ___builtin_memcpy_aligned : ident := 6%positive.
Definition ___builtin_nop : ident := 51%positive.
Definition ___builtin_read16_reversed : ident := 47%positive.
Definition ___builtin_read32_reversed : ident := 48%positive.
Definition ___builtin_va_arg : ident := 11%positive.
Definition ___builtin_va_copy : ident := 12%positive.
Definition ___builtin_va_end : ident := 13%positive.
Definition ___builtin_va_start : ident := 10%positive.
Definition ___builtin_write16_reversed : ident := 49%positive.
Definition ___builtin_write32_reversed : ident := 50%positive.
Definition ___compcert_va_composite : ident := 17%positive.
Definition ___compcert_va_float64 : ident := 16%positive.
Definition ___compcert_va_int32 : ident := 14%positive.
Definition ___compcert_va_int64 : ident := 15%positive.
Definition ___i64_dtos : ident := 18%positive.
Definition ___i64_dtou : ident := 19%positive.
Definition ___i64_sar : ident := 30%positive.
Definition ___i64_sdiv : ident := 24%positive.
Definition ___i64_shl : ident := 28%positive.
Definition ___i64_shr : ident := 29%positive.
Definition ___i64_smod : ident := 26%positive.
Definition ___i64_stod : ident := 20%positive.
Definition ___i64_stof : ident := 22%positive.
Definition ___i64_udiv : ident := 25%positive.
Definition ___i64_umod : ident := 27%positive.
Definition ___i64_utod : ident := 21%positive.
Definition ___i64_utof : ident := 23%positive.
Definition _a : ident := 1%positive.
Definition _acquire : ident := 54%positive.
Definition _add : ident := 73%positive.
Definition _arg : ident := 76%positive.
Definition _buf : ident := 66%positive.
Definition _consumer : ident := 78%positive.
Definition _d : ident := 70%positive.
Definition _data : ident := 3%positive.
Definition _free : ident := 60%positive.
Definition _get_request : ident := 69%positive.
Definition _i : ident := 79%positive.
Definition _len : ident := 72%positive.
Definition _length : ident := 63%positive.
Definition _lock_t : ident := 2%positive.
Definition _main : ident := 80%positive.
Definition _makecond : ident := 57%positive.
Definition _makelock : ident := 53%positive.
Definition _malloc : ident := 61%positive.
Definition _process : ident := 67%positive.
Definition _process_request : ident := 71%positive.
Definition _producer : ident := 77%positive.
Definition _r : ident := 74%positive.
Definition _release : ident := 55%positive.
Definition _remove : ident := 75%positive.
Definition _request : ident := 68%positive.
Definition _request_t : ident := 4%positive.
Definition _requests_consumer : ident := 64%positive.
Definition _requests_lock : ident := 62%positive.
Definition _requests_producer : ident := 65%positive.
Definition _signalcond : ident := 59%positive.
Definition _spawn : ident := 56%positive.
Definition _waitcond : ident := 58%positive.
Definition _t'1 : ident := 81%positive.

Definition v_requests_lock := {|
  gvar_info := (Tstruct _lock_t noattr);
  gvar_init := (Init_space 16 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_length := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_requests_consumer := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_requests_producer := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_buf := {|
  gvar_info := (tarray (tptr (Tstruct _request_t noattr)) 10);
  gvar_init := (Init_space 40 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_process := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_data, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn None)
|}.

Definition f_get_request := {|
  fn_return := (tptr (Tstruct _request_t noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_request, (tptr (Tstruct _request_t noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _request_t noattr) tuint) :: nil))
    (Sset _request
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _request_t noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _request (tptr (Tstruct _request_t noattr)))
          (Tstruct _request_t noattr)) _data tint)
      (Econst_int (Int.repr 1) tint))
    (Sreturn (Some (Etempvar _request (tptr (Tstruct _request_t noattr)))))))
|}.

Definition f_process_request := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_request, (tptr (Tstruct _request_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_d, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _d
    (Efield
      (Ederef (Etempvar _request (tptr (Tstruct _request_t noattr)))
        (Tstruct _request_t noattr)) _data tint))
  (Ssequence
    (Scall None
      (Evar _process (Tfunction (Tcons tint Tnil) tvoid cc_default))
      ((Etempvar _d tint) :: nil))
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _request (tptr (Tstruct _request_t noattr))) :: nil))))
|}.

Definition f_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_request, (tptr (Tstruct _request_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_len, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _len (Evar _length tint))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Evar _buf (tarray (tptr (Tstruct _request_t noattr)) 10))
          (Etempvar _len tint) (tptr (tptr (Tstruct _request_t noattr))))
        (tptr (Tstruct _request_t noattr)))
      (Etempvar _request (tptr (Tstruct _request_t noattr))))
    (Sreturn None)))
|}.

Definition f_remove := {|
  fn_return := (tptr (Tstruct _request_t noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_len, tint) :: (_r, (tptr (Tstruct _request_t noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _len (Evar _length tint))
  (Ssequence
    (Sset _r
      (Ederef
        (Ebinop Oadd
          (Evar _buf (tarray (tptr (Tstruct _request_t noattr)) 10))
          (Ebinop Osub (Etempvar _len tint) (Econst_int (Int.repr 1) tint)
            tint) (tptr (tptr (Tstruct _request_t noattr))))
        (tptr (Tstruct _request_t noattr))))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Evar _buf (tarray (tptr (Tstruct _request_t noattr)) 10))
            (Ebinop Osub (Etempvar _len tint) (Econst_int (Int.repr 1) tint)
              tint) (tptr (tptr (Tstruct _request_t noattr))))
          (tptr (Tstruct _request_t noattr))) (Econst_int (Int.repr 0) tint))
      (Sreturn (Some (Etempvar _r (tptr (Tstruct _request_t noattr))))))))
|}.

Definition f_producer := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_arg, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_request, (tptr (Tstruct _request_t noattr))) ::
               (_len, tint) :: (_t'1, (tptr (Tstruct _request_t noattr))) ::
               nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_request (Tfunction Tnil
                               (tptr (Tstruct _request_t noattr)) cc_default))
          nil)
        (Sset _request (Etempvar _t'1 (tptr (Tstruct _request_t noattr)))))
      (Ssequence
        (Scall None
          (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                           cc_default))
          ((Ecast
             (Eaddrof (Evar _requests_lock (Tstruct _lock_t noattr))
               (tptr (Tstruct _lock_t noattr))) (tptr tvoid)) :: nil))
        (Ssequence
          (Sset _len (Evar _length tint))
          (Ssequence
            (Swhile
              (Ebinop Oge (Etempvar _len tint)
                (Econst_int (Int.repr 10) tint) tint)
              (Ssequence
                (Scall None
                  (Evar _waitcond (Tfunction
                                    (Tcons (tptr tint)
                                      (Tcons (tptr tvoid) Tnil)) tvoid
                                    cc_default))
                  ((Eaddrof (Evar _requests_producer tint) (tptr tint)) ::
                   (Ecast
                     (Eaddrof (Evar _requests_lock (Tstruct _lock_t noattr))
                       (tptr (Tstruct _lock_t noattr))) (tptr tvoid)) :: nil))
                (Sset _len (Evar _length tint))))
            (Ssequence
              (Scall None
                (Evar _add (Tfunction
                             (Tcons (tptr (Tstruct _request_t noattr)) Tnil)
                             tvoid cc_default))
                ((Etempvar _request (tptr (Tstruct _request_t noattr))) ::
                 nil))
              (Ssequence
                (Sassign (Evar _length tint)
                  (Ebinop Oadd (Etempvar _len tint)
                    (Econst_int (Int.repr 1) tint) tint))
                (Ssequence
                  (Scall None
                    (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                     cc_default))
                    ((Ecast
                       (Eaddrof
                         (Evar _requests_lock (Tstruct _lock_t noattr))
                         (tptr (Tstruct _lock_t noattr))) (tptr tvoid)) ::
                     nil))
                  (Scall None
                    (Evar _signalcond (Tfunction (Tcons (tptr tint) Tnil)
                                        tvoid cc_default))
                    ((Eaddrof (Evar _requests_consumer tint) (tptr tint)) ::
                     nil))))))))))
  Sskip)
|}.

Definition f_consumer := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_arg, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_request, (tptr (Tstruct _request_t noattr))) ::
               (_len, tint) :: (_t'1, (tptr (Tstruct _request_t noattr))) ::
               nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Scall None
        (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Ecast
           (Eaddrof (Evar _requests_lock (Tstruct _lock_t noattr))
             (tptr (Tstruct _lock_t noattr))) (tptr tvoid)) :: nil))
      (Ssequence
        (Sset _len (Evar _length tint))
        (Ssequence
          (Swhile
            (Ebinop Oeq (Etempvar _len tint) (Econst_int (Int.repr 0) tint)
              tint)
            (Ssequence
              (Scall None
                (Evar _waitcond (Tfunction
                                  (Tcons (tptr tint)
                                    (Tcons (tptr tvoid) Tnil)) tvoid
                                  cc_default))
                ((Eaddrof (Evar _requests_consumer tint) (tptr tint)) ::
                 (Ecast
                   (Eaddrof (Evar _requests_lock (Tstruct _lock_t noattr))
                     (tptr (Tstruct _lock_t noattr))) (tptr tvoid)) :: nil))
              (Sset _len (Evar _length tint))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _remove (Tfunction Tnil
                                (tptr (Tstruct _request_t noattr))
                                cc_default)) nil)
              (Sset _request
                (Etempvar _t'1 (tptr (Tstruct _request_t noattr)))))
            (Ssequence
              (Sassign (Evar _length tint)
                (Ebinop Osub (Etempvar _len tint)
                  (Econst_int (Int.repr 1) tint) tint))
              (Ssequence
                (Scall None
                  (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                   cc_default))
                  ((Ecast
                     (Eaddrof (Evar _requests_lock (Tstruct _lock_t noattr))
                       (tptr (Tstruct _lock_t noattr))) (tptr tvoid)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _signalcond (Tfunction (Tcons (tptr tint) Tnil)
                                        tvoid cc_default))
                    ((Eaddrof (Evar _requests_producer tint) (tptr tint)) ::
                     nil))
                  (Scall None
                    (Evar _process_request (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _request_t noattr))
                                               Tnil) tvoid cc_default))
                    ((Etempvar _request (tptr (Tstruct _request_t noattr))) ::
                     nil))))))))))
  Sskip)
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_len, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 10) tint) tint)
            Sskip
            Sbreak)
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Evar _buf (tarray (tptr (Tstruct _request_t noattr)) 10))
                (Etempvar _i tint) (tptr (tptr (Tstruct _request_t noattr))))
              (tptr (Tstruct _request_t noattr)))
            (Econst_int (Int.repr 0) tint)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sassign (Evar _length tint) (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Scall None
          (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
          ((Ecast
             (Eaddrof (Evar _requests_lock (Tstruct _lock_t noattr))
               (tptr (Tstruct _lock_t noattr))) (tptr tvoid)) :: nil))
        (Ssequence
          (Scall None
            (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                             cc_default))
            ((Ecast
               (Eaddrof (Evar _requests_lock (Tstruct _lock_t noattr))
                 (tptr (Tstruct _lock_t noattr))) (tptr tvoid)) :: nil))
          (Ssequence
            (Scall None
              (Evar _makecond (Tfunction (Tcons (tptr tint) Tnil) tvoid
                                cc_default))
              ((Eaddrof (Evar _requests_producer tint) (tptr tint)) :: nil))
            (Ssequence
              (Scall None
                (Evar _makecond (Tfunction (Tcons (tptr tint) Tnil) tvoid
                                  cc_default))
                ((Eaddrof (Evar _requests_consumer tint) (tptr tint)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _spawn (Tfunction
                                 (Tcons
                                   (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                           (tptr tvoid) cc_default))
                                   (Tcons (tptr tvoid) Tnil)) tvoid
                                 cc_default))
                  ((Ecast
                     (Eaddrof
                       (Evar _consumer (Tfunction (Tcons (tptr tvoid) Tnil)
                                         (tptr tvoid) cc_default))
                       (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                               (tptr tvoid) cc_default))) (tptr tvoid)) ::
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
                   nil))
                (Ssequence
                  (Scall None
                    (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                     cc_default))
                    ((Eaddrof (Evar _requests_lock (Tstruct _lock_t noattr))
                       (tptr (Tstruct _lock_t noattr))) :: nil))
                  (Ssequence
                    (Sset _len (Evar _length tint))
                    (Ssequence
                      (Swhile
                        (Ebinop One (Etempvar _len tint)
                          (Econst_int (Int.repr 0) tint) tint)
                        (Ssequence
                          (Scall None
                            (Evar _waitcond (Tfunction
                                              (Tcons (tptr tint)
                                                (Tcons (tptr tvoid) Tnil))
                                              tvoid cc_default))
                            ((Eaddrof (Evar _requests_producer tint)
                               (tptr tint)) ::
                             (Ecast
                               (Eaddrof
                                 (Evar _requests_lock (Tstruct _lock_t noattr))
                                 (tptr (Tstruct _lock_t noattr)))
                               (tptr tvoid)) :: nil))
                          (Sset _len (Evar _length tint))))
                      (Ssequence
                        (Scall None
                          (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil)
                                           tvoid cc_default))
                          ((Ecast
                             (Eaddrof
                               (Evar _requests_lock (Tstruct _lock_t noattr))
                               (tptr (Tstruct _lock_t noattr))) (tptr tvoid)) ::
                           nil))
                        (Ssequence
                          (Scall None
                            (Evar _spawn (Tfunction
                                           (Tcons
                                             (tptr (Tfunction
                                                     (Tcons (tptr tvoid)
                                                       Tnil) (tptr tvoid)
                                                     cc_default))
                                             (Tcons (tptr tvoid) Tnil)) tvoid
                                           cc_default))
                            ((Ecast
                               (Eaddrof
                                 (Evar _producer (Tfunction
                                                   (Tcons (tptr tvoid) Tnil)
                                                   (tptr tvoid) cc_default))
                                 (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                         (tptr tvoid) cc_default)))
                               (tptr tvoid)) ::
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) :: nil))
                          (Ssequence
                            (Sloop Sskip Sskip)
                            (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _lock_t Struct ((_a, (tarray (tptr tvoid) 4)) :: nil) noattr ::
 Composite _request_t Struct ((_data, tint) :: nil) noattr :: nil).

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
 (_makelock,
   Gfun(External (EF_external "makelock"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_release,
   Gfun(External (EF_external "release"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_spawn,
   Gfun(External (EF_external "spawn"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons
       (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid) cc_default))
       (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (_makecond,
   Gfun(External (EF_external "makecond"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tint) Tnil) tvoid cc_default)) ::
 (_waitcond,
   Gfun(External (EF_external "waitcond"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tint) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (_signalcond,
   Gfun(External (EF_external "signalcond"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tint) Tnil) tvoid cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_requests_lock, Gvar v_requests_lock) :: (_length, Gvar v_length) ::
 (_requests_consumer, Gvar v_requests_consumer) ::
 (_requests_producer, Gvar v_requests_producer) :: (_buf, Gvar v_buf) ::
 (_process, Gfun(Internal f_process)) ::
 (_get_request, Gfun(Internal f_get_request)) ::
 (_process_request, Gfun(Internal f_process_request)) ::
 (_add, Gfun(Internal f_add)) :: (_remove, Gfun(Internal f_remove)) ::
 (_producer, Gfun(Internal f_producer)) ::
 (_consumer, Gfun(Internal f_consumer)) :: (_main, Gfun(Internal f_main)) ::
 nil);
prog_public :=
(_main :: _consumer :: _producer :: _remove :: _add :: _process_request ::
 _get_request :: _process :: _buf :: _requests_producer ::
 _requests_consumer :: _length :: _requests_lock :: _malloc :: _free ::
 _signalcond :: _waitcond :: _makecond :: _spawn :: _release :: _acquire ::
 _makelock :: ___builtin_debug :: ___builtin_nop ::
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

