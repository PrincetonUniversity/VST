
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
Definition _arg : ident := 96%positive.
Definition _avail : ident := 92%positive.
Definition _available : ident := 89%positive.
Definition _b : ident := 77%positive.
Definition _buf : ident := 97%positive.
Definition _buffer : ident := 60%positive.
Definition _bufs : ident := 72%positive.
Definition _c : ident := 69%positive.
Definition _comm : ident := 74%positive.
Definition _d : ident := 100%positive.
Definition _data : ident := 59%positive.
Definition _exit : ident := 61%positive.
Definition _finish_read : ident := 84%positive.
Definition _finish_write : ident := 95%positive.
Definition _i : ident := 70%positive.
Definition _i__1 : ident := 91%positive.
Definition _initialize_channels : ident := 79%positive.
Definition _initialize_reader : ident := 82%positive.
Definition _initialize_writer : ident := 88%positive.
Definition _l : ident := 54%positive.
Definition _last : ident := 90%positive.
Definition _last_given : ident := 87%positive.
Definition _last_read : ident := 76%positive.
Definition _last_taken : ident := 85%positive.
Definition _lock : ident := 73%positive.
Definition _lock_t : ident := 2%positive.
Definition _lr : ident := 81%positive.
Definition _main : ident := 58%positive.
Definition _makelock : ident := 63%positive.
Definition _malloc : ident := 62%positive.
Definition _memset : ident := 71%positive.
Definition _n : ident := 65%positive.
Definition _p : ident := 66%positive.
Definition _r : ident := 78%positive.
Definition _reader : ident := 98%positive.
Definition _reading : ident := 75%positive.
Definition _release : ident := 52%positive.
Definition _rr : ident := 80%positive.
Definition _s : ident := 68%positive.
Definition _simulate_atomic_exchange : ident := 57%positive.
Definition _spawn : ident := 64%positive.
Definition _start_read : ident := 83%positive.
Definition _start_write : ident := 93%positive.
Definition _surely_malloc : ident := 67%positive.
Definition _tgt : ident := 53%positive.
Definition _v : ident := 55%positive.
Definition _w : ident := 94%positive.
Definition _writer : ident := 99%positive.
Definition _writing : ident := 86%positive.
Definition _x : ident := 56%positive.
Definition _t'1 : ident := 101%positive.
Definition _t'2 : ident := 102%positive.
Definition _t'3 : ident := 103%positive.
Definition _t'4 : ident := 104%positive.
Definition _t'5 : ident := 105%positive.

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

Definition f_memset := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tvoid)) :: (_c, tint) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tint)) :: (_i, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _p (Ecast (Etempvar _s (tptr tvoid)) (tptr tint)))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                         (Ebinop Odiv (Etempvar _n tuint)
                           (Econst_int (Int.repr 4) tint) tuint) tint)
            Sskip
            Sbreak)
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _p (tptr tint)) (Etempvar _i tuint)
                (tptr tint)) tint) (Etempvar _c tint)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Sreturn (Some (Etempvar _s (tptr tvoid))))))
|}.

Definition v_bufs := {|
  gvar_info := (tarray (tptr (Tstruct _buffer noattr)) 5);
  gvar_init := (Init_space 20 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_lock := {|
  gvar_info := (tarray (tptr (Tstruct _lock_t noattr)) 3);
  gvar_init := (Init_space 12 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_comm := {|
  gvar_info := (tarray (tptr tint) 3);
  gvar_init := (Init_space 12 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_reading := {|
  gvar_info := (tarray (tptr tint) 3);
  gvar_init := (Init_space 12 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_last_read := {|
  gvar_info := (tarray (tptr tint) 3);
  gvar_init := (Init_space 12 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_initialize_channels := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_b, (tptr (Tstruct _buffer noattr))) ::
               (_r, tint) :: (_c, (tptr tint)) ::
               (_l, (tptr (Tstruct _lock_t noattr))) ::
               (_t'5, (tptr tvoid)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Ebinop Oadd (Econst_int (Int.repr 3) tint)
                         (Econst_int (Int.repr 2) tint) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                     cc_default))
              ((Esizeof (Tstruct _buffer noattr) tuint) :: nil))
            (Sset _b (Etempvar _t'1 (tptr tvoid))))
          (Ssequence
            (Scall None
              (Evar _memset (Tfunction
                              (Tcons (tptr tvoid)
                                (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
                              cc_default))
              ((Etempvar _b (tptr (Tstruct _buffer noattr))) ::
               (Econst_int (Int.repr 0) tint) ::
               (Esizeof (Tstruct _buffer noattr) tuint) :: nil))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Evar _bufs (tarray (tptr (Tstruct _buffer noattr)) 5))
                  (Etempvar _i tint) (tptr (tptr (Tstruct _buffer noattr))))
                (tptr (Tstruct _buffer noattr)))
              (Etempvar _b (tptr (Tstruct _buffer noattr)))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Sset _r (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                       (Econst_int (Int.repr 3) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                     cc_default))
              ((Esizeof tint tuint) :: nil))
            (Sset _c (Etempvar _t'2 (tptr tvoid))))
          (Ssequence
            (Sassign (Ederef (Etempvar _c (tptr tint)) tint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _comm (tarray (tptr tint) 3))
                    (Etempvar _r tint) (tptr (tptr tint))) (tptr tint))
                (Etempvar _c (tptr tint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                           (tptr tvoid) cc_default))
                    ((Esizeof tint tuint) :: nil))
                  (Sset _c (Etempvar _t'3 (tptr tvoid))))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _reading (tarray (tptr tint) 3))
                        (Etempvar _r tint) (tptr (tptr tint))) (tptr tint))
                    (Etempvar _c (tptr tint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                               (tptr tvoid) cc_default))
                        ((Esizeof tint tuint) :: nil))
                      (Sset _c (Etempvar _t'4 (tptr tvoid))))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Evar _last_read (tarray (tptr tint) 3))
                            (Etempvar _r tint) (tptr (tptr tint)))
                          (tptr tint)) (Etempvar _c (tptr tint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'5)
                            (Evar _surely_malloc (Tfunction
                                                   (Tcons tuint Tnil)
                                                   (tptr tvoid) cc_default))
                            ((Esizeof (Tstruct _lock_t noattr) tuint) :: nil))
                          (Sset _l (Etempvar _t'5 (tptr tvoid))))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Evar _lock (tarray (tptr (Tstruct _lock_t noattr)) 3))
                                (Etempvar _r tint)
                                (tptr (tptr (Tstruct _lock_t noattr))))
                              (tptr (Tstruct _lock_t noattr)))
                            (Etempvar _l (tptr (Tstruct _lock_t noattr))))
                          (Ssequence
                            (Scall None
                              (Evar _makelock (Tfunction
                                                (Tcons (tptr tvoid) Tnil)
                                                tvoid cc_default))
                              ((Etempvar _l (tptr (Tstruct _lock_t noattr))) ::
                               nil))
                            (Scall None
                              (Evar _release (Tfunction
                                               (Tcons (tptr tvoid) Tnil)
                                               tvoid cc_default))
                              ((Etempvar _l (tptr (Tstruct _lock_t noattr))) ::
                               nil)))))))))))))
      (Sset _r
        (Ebinop Oadd (Etempvar _r tint) (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_initialize_reader := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_rr, (tptr tint)) :: (_lr, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _rr
    (Ederef
      (Ebinop Oadd (Evar _reading (tarray (tptr tint) 3)) (Etempvar _r tint)
        (tptr (tptr tint))) (tptr tint)))
  (Ssequence
    (Sset _lr
      (Ederef
        (Ebinop Oadd (Evar _last_read (tarray (tptr tint) 3))
          (Etempvar _r tint) (tptr (tptr tint))) (tptr tint)))
    (Ssequence
      (Sassign (Ederef (Etempvar _rr (tptr tint)) tint)
        (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
      (Sassign (Ederef (Etempvar _lr (tptr tint)) tint)
        (Econst_int (Int.repr 1) tint)))))
|}.

Definition f_start_read := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_r, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tint) :: (_c, (tptr tint)) ::
               (_l, (tptr (Tstruct _lock_t noattr))) :: (_rr, (tptr tint)) ::
               (_lr, (tptr tint)) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _c
    (Ederef
      (Ebinop Oadd (Evar _comm (tarray (tptr tint) 3)) (Etempvar _r tint)
        (tptr (tptr tint))) (tptr tint)))
  (Ssequence
    (Sset _l
      (Ederef
        (Ebinop Oadd (Evar _lock (tarray (tptr (Tstruct _lock_t noattr)) 3))
          (Etempvar _r tint) (tptr (tptr (Tstruct _lock_t noattr))))
        (tptr (Tstruct _lock_t noattr))))
    (Ssequence
      (Sset _rr
        (Ederef
          (Ebinop Oadd (Evar _reading (tarray (tptr tint) 3))
            (Etempvar _r tint) (tptr (tptr tint))) (tptr tint)))
      (Ssequence
        (Sset _lr
          (Ederef
            (Ebinop Oadd (Evar _last_read (tarray (tptr tint) 3))
              (Etempvar _r tint) (tptr (tptr tint))) (tptr tint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _simulate_atomic_exchange (Tfunction
                                                (Tcons (tptr tint)
                                                  (Tcons
                                                    (tptr (Tstruct _lock_t noattr))
                                                    (Tcons tint Tnil))) tint
                                                cc_default))
              ((Etempvar _c (tptr tint)) ::
               (Etempvar _l (tptr (Tstruct _lock_t noattr))) ::
               (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))
            (Sset _b (Etempvar _t'1 tint)))
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Oge (Etempvar _b tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sset _t'2
                  (Ecast
                    (Ebinop Olt (Etempvar _b tint)
                      (Ebinop Oadd (Econst_int (Int.repr 3) tint)
                        (Econst_int (Int.repr 2) tint) tint) tint) tbool))
                (Sset _t'2 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'2 tint)
                (Sassign (Ederef (Etempvar _lr (tptr tint)) tint)
                  (Etempvar _b tint))
                (Sset _b (Ederef (Etempvar _lr (tptr tint)) tint))))
            (Ssequence
              (Sassign (Ederef (Etempvar _rr (tptr tint)) tint)
                (Etempvar _b tint))
              (Sreturn (Some (Etempvar _b tint))))))))))
|}.

Definition f_finish_read := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_rr, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _rr
    (Ederef
      (Ebinop Oadd (Evar _reading (tarray (tptr tint) 3)) (Etempvar _r tint)
        (tptr (tptr tint))) (tptr tint)))
  (Sassign (Ederef (Etempvar _rr (tptr tint)) tint)
    (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
|}.

Definition v_last_taken := {|
  gvar_info := (tarray tint 3);
  gvar_init := (Init_space 12 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_writing := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_last_given := {|
  gvar_info := tint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_initialize_writer := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _last_given tint) (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign (Evar _writing tint)
      (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 3) tint) tint)
            Sskip
            Sbreak)
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _last_taken (tarray tint 3))
                (Etempvar _i tint) (tptr tint)) tint)
            (Econst_int (Int.repr 1) tint)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))))
|}.

Definition f_start_write := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_available, (tarray tint 5)) :: nil);
  fn_temps := ((_i, tint) :: (_last, tint) :: (_r, tint) :: (_i__1, tint) ::
               (_avail, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Ebinop Oadd (Econst_int (Int.repr 3) tint)
                         (Econst_int (Int.repr 2) tint) tint) tint)
          Sskip
          Sbreak)
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _available (tarray tint 5)) (Etempvar _i tint)
              (tptr tint)) tint) (Econst_int (Int.repr 1) tint)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Sset _last (Evar _last_given tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _available (tarray tint 5))
            (Etempvar _last tint) (tptr tint)) tint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Ssequence
          (Sset _r (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                             (Econst_int (Int.repr 3) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _last
                  (Ederef
                    (Ebinop Oadd (Evar _last_taken (tarray tint 3))
                      (Etempvar _r tint) (tptr tint)) tint))
                (Sifthenelse (Ebinop One (Etempvar _last tint)
                               (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                 tint) tint)
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _available (tarray tint 5))
                        (Etempvar _last tint) (tptr tint)) tint)
                    (Econst_int (Int.repr 0) tint))
                  Sskip)))
            (Sset _r
              (Ebinop Oadd (Etempvar _r tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Ssequence
            (Sset _i__1 (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i__1 tint)
                               (Ebinop Oadd (Econst_int (Int.repr 3) tint)
                                 (Econst_int (Int.repr 2) tint) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Sset _avail
                    (Ederef
                      (Ebinop Oadd (Evar _available (tarray tint 5))
                        (Etempvar _i__1 tint) (tptr tint)) tint))
                  (Sifthenelse (Etempvar _avail tint)
                    (Ssequence
                      (Sassign (Evar _writing tint) (Etempvar _i__1 tint))
                      (Sreturn (Some (Etempvar _i__1 tint))))
                    Sskip)))
              (Sset _i__1
                (Ebinop Oadd (Etempvar _i__1 tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Scall None
            (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
            ((Econst_int (Int.repr 1) tint) :: nil)))))))
|}.

Definition f_finish_write := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_last, tint) :: (_w, tint) :: (_r, tint) ::
               (_c, (tptr tint)) :: (_l, (tptr (Tstruct _lock_t noattr))) ::
               (_b, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _last (Evar _last_given tint))
  (Ssequence
    (Sset _w (Evar _writing tint))
    (Ssequence
      (Ssequence
        (Sset _r (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _r tint)
                           (Econst_int (Int.repr 3) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _c
                (Ederef
                  (Ebinop Oadd (Evar _comm (tarray (tptr tint) 3))
                    (Etempvar _r tint) (tptr (tptr tint))) (tptr tint)))
              (Ssequence
                (Sset _l
                  (Ederef
                    (Ebinop Oadd
                      (Evar _lock (tarray (tptr (Tstruct _lock_t noattr)) 3))
                      (Etempvar _r tint)
                      (tptr (tptr (Tstruct _lock_t noattr))))
                    (tptr (Tstruct _lock_t noattr))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'1)
                      (Evar _simulate_atomic_exchange (Tfunction
                                                        (Tcons (tptr tint)
                                                          (Tcons
                                                            (tptr (Tstruct _lock_t noattr))
                                                            (Tcons tint Tnil)))
                                                        tint cc_default))
                      ((Etempvar _c (tptr tint)) ::
                       (Etempvar _l (tptr (Tstruct _lock_t noattr))) ::
                       (Etempvar _w tint) :: nil))
                    (Sset _b (Etempvar _t'1 tint)))
                  (Sifthenelse (Ebinop Oeq (Etempvar _b tint)
                                 (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                   tint) tint)
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _last_taken (tarray tint 3))
                          (Etempvar _r tint) (tptr tint)) tint)
                      (Etempvar _last tint))
                    Sskip)))))
          (Sset _r
            (Ebinop Oadd (Etempvar _r tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Sassign (Evar _last_given tint) (Etempvar _w tint))
        (Sassign (Evar _writing tint)
          (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))))))
|}.

Definition f_reader := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_arg, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, tint) :: (_b, tint) ::
               (_buf, (tptr (Tstruct _buffer noattr))) :: (_v, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _r (Ederef (Ecast (Etempvar _arg (tptr tvoid)) (tptr tint)) tint))
  (Ssequence
    (Scall None
      (Evar _initialize_reader (Tfunction (Tcons tint Tnil) tvoid cc_default))
      ((Etempvar _r tint) :: nil))
    (Ssequence
      (Sloop
        (Ssequence
          Sskip
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _start_read (Tfunction (Tcons tint Tnil) tint
                                    cc_default)) ((Etempvar _r tint) :: nil))
              (Sset _b (Etempvar _t'1 tint)))
            (Ssequence
              (Sset _buf
                (Ederef
                  (Ebinop Oadd
                    (Evar _bufs (tarray (tptr (Tstruct _buffer noattr)) 5))
                    (Etempvar _b tint)
                    (tptr (tptr (Tstruct _buffer noattr))))
                  (tptr (Tstruct _buffer noattr))))
              (Ssequence
                (Sset _v
                  (Efield
                    (Ederef (Etempvar _buf (tptr (Tstruct _buffer noattr)))
                      (Tstruct _buffer noattr)) _data tint))
                (Scall None
                  (Evar _finish_read (Tfunction (Tcons tint Tnil) tvoid
                                       cc_default))
                  ((Etempvar _r tint) :: nil))))))
        Sskip)
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_writer := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_arg, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_v, tint) :: (_b, tint) ::
               (_buf, (tptr (Tstruct _buffer noattr))) :: (_t'1, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Scall None (Evar _initialize_writer (Tfunction Tnil tvoid cc_default))
    nil)
  (Ssequence
    (Sset _v (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sloop
        (Ssequence
          Sskip
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _start_write (Tfunction Tnil tint cc_default)) nil)
              (Sset _b (Etempvar _t'1 tint)))
            (Ssequence
              (Sset _buf
                (Ederef
                  (Ebinop Oadd
                    (Evar _bufs (tarray (tptr (Tstruct _buffer noattr)) 5))
                    (Etempvar _b tint)
                    (tptr (tptr (Tstruct _buffer noattr))))
                  (tptr (Tstruct _buffer noattr))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _buf (tptr (Tstruct _buffer noattr)))
                      (Tstruct _buffer noattr)) _data tint)
                  (Etempvar _v tint))
                (Ssequence
                  (Scall None
                    (Evar _finish_write (Tfunction Tnil tvoid cc_default))
                    nil)
                  (Sset _v
                    (Ebinop Oadd (Etempvar _v tint)
                      (Econst_int (Int.repr 1) tint) tint)))))))
        Sskip)
      (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_d, (tptr tint)) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None (Evar _initialize_channels (Tfunction Tnil tvoid cc_default))
      nil)
    (Ssequence
      (Scall None
        (Evar _spawn (Tfunction
                       (Tcons
                         (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                 (tptr tvoid) cc_default))
                         (Tcons (tptr tvoid) Tnil)) tvoid cc_default))
        ((Ecast
           (Eaddrof
             (Evar _writer (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid)
                             cc_default))
             (tptr (Tfunction (Tcons (tptr tvoid) Tnil) (tptr tvoid)
                     cc_default))) (tptr tvoid)) ::
         (Econst_int (Int.repr 0) tint) :: nil))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 3) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                           (tptr tvoid) cc_default))
                    ((Esizeof tint tuint) :: nil))
                  (Sset _d (Etempvar _t'1 (tptr tvoid))))
                (Ssequence
                  (Sassign (Ederef (Etempvar _d (tptr tint)) tint)
                    (Etempvar _i tint))
                  (Scall None
                    (Evar _spawn (Tfunction
                                   (Tcons
                                     (tptr (Tfunction
                                             (Tcons (tptr tvoid) Tnil)
                                             (tptr tvoid) cc_default))
                                     (Tcons (tptr tvoid) Tnil)) tvoid
                                   cc_default))
                    ((Ecast
                       (Eaddrof
                         (Evar _reader (Tfunction (Tcons (tptr tvoid) Tnil)
                                         (tptr tvoid) cc_default))
                         (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                 (tptr tvoid) cc_default))) (tptr tvoid)) ::
                     (Ecast (Etempvar _d (tptr tint)) (tptr tvoid)) :: nil)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Sloop Sskip Sskip))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _lock_t Struct ((_a, (tarray (tptr tvoid) 2)) :: nil) noattr ::
 Composite _buffer Struct ((_data, tint) :: nil) noattr :: nil).

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
 (_makelock,
   Gfun(External (EF_external "makelock"
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
 (_simulate_atomic_exchange,
   Gfun(External (EF_external "simulate_atomic_exchange"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tint)
       (Tcons (tptr (Tstruct _lock_t noattr)) (Tcons tint Tnil))) tint
     cc_default)) :: (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_memset, Gfun(Internal f_memset)) :: (_bufs, Gvar v_bufs) ::
 (_lock, Gvar v_lock) :: (_comm, Gvar v_comm) ::
 (_reading, Gvar v_reading) :: (_last_read, Gvar v_last_read) ::
 (_initialize_channels, Gfun(Internal f_initialize_channels)) ::
 (_initialize_reader, Gfun(Internal f_initialize_reader)) ::
 (_start_read, Gfun(Internal f_start_read)) ::
 (_finish_read, Gfun(Internal f_finish_read)) ::
 (_last_taken, Gvar v_last_taken) :: (_writing, Gvar v_writing) ::
 (_last_given, Gvar v_last_given) ::
 (_initialize_writer, Gfun(Internal f_initialize_writer)) ::
 (_start_write, Gfun(Internal f_start_write)) ::
 (_finish_write, Gfun(Internal f_finish_write)) ::
 (_reader, Gfun(Internal f_reader)) :: (_writer, Gfun(Internal f_writer)) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: _writer :: _reader :: _finish_write :: _start_write ::
 _initialize_writer :: _last_given :: _writing :: _last_taken ::
 _finish_read :: _start_read :: _initialize_reader :: _initialize_channels ::
 _last_read :: _reading :: _comm :: _lock :: _bufs :: _memset ::
 _surely_malloc :: _simulate_atomic_exchange :: _spawn :: _release ::
 _makelock :: _malloc :: _exit :: ___builtin_debug :: ___builtin_nop ::
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

