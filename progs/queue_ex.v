
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition ___builtin_annot : ident := 15%positive.
Definition ___builtin_annot_intval : ident := 16%positive.
Definition ___builtin_bswap : ident := 39%positive.
Definition ___builtin_bswap16 : ident := 41%positive.
Definition ___builtin_bswap32 : ident := 40%positive.
Definition ___builtin_clz : ident := 42%positive.
Definition ___builtin_clzl : ident := 43%positive.
Definition ___builtin_clzll : ident := 44%positive.
Definition ___builtin_ctz : ident := 45%positive.
Definition ___builtin_ctzl : ident := 46%positive.
Definition ___builtin_ctzll : ident := 47%positive.
Definition ___builtin_debug : ident := 60%positive.
Definition ___builtin_fabs : ident := 13%positive.
Definition ___builtin_fmadd : ident := 51%positive.
Definition ___builtin_fmax : ident := 49%positive.
Definition ___builtin_fmin : ident := 50%positive.
Definition ___builtin_fmsub : ident := 52%positive.
Definition ___builtin_fnmadd : ident := 53%positive.
Definition ___builtin_fnmsub : ident := 54%positive.
Definition ___builtin_fsqrt : ident := 48%positive.
Definition ___builtin_membar : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 14%positive.
Definition ___builtin_nop : ident := 59%positive.
Definition ___builtin_read16_reversed : ident := 55%positive.
Definition ___builtin_read32_reversed : ident := 56%positive.
Definition ___builtin_va_arg : ident := 19%positive.
Definition ___builtin_va_copy : ident := 20%positive.
Definition ___builtin_va_end : ident := 21%positive.
Definition ___builtin_va_start : ident := 18%positive.
Definition ___builtin_write16_reversed : ident := 57%positive.
Definition ___builtin_write32_reversed : ident := 58%positive.
Definition ___compcert_va_composite : ident := 25%positive.
Definition ___compcert_va_float64 : ident := 24%positive.
Definition ___compcert_va_int32 : ident := 22%positive.
Definition ___compcert_va_int64 : ident := 23%positive.
Definition ___i64_dtos : ident := 26%positive.
Definition ___i64_dtou : ident := 27%positive.
Definition ___i64_sar : ident := 38%positive.
Definition ___i64_sdiv : ident := 32%positive.
Definition ___i64_shl : ident := 36%positive.
Definition ___i64_shr : ident := 37%positive.
Definition ___i64_smod : ident := 34%positive.
Definition ___i64_stod : ident := 28%positive.
Definition ___i64_stof : ident := 30%positive.
Definition ___i64_udiv : ident := 33%positive.
Definition ___i64_umod : ident := 35%positive.
Definition ___i64_utod : ident := 29%positive.
Definition ___i64_utof : ident := 31%positive.
Definition ___stringlit_1 : ident := 109%positive.
Definition _a : ident := 1%positive.
Definition _acquire : ident := 66%positive.
Definition _addc : ident := 7%positive.
Definition _arg : ident := 99%positive.
Definition _buf : ident := 3%positive.
Definition _c : ident := 78%positive.
Definition _c__1 : ident := 86%positive.
Definition _d : ident := 10%positive.
Definition _exit : ident := 61%positive.
Definition _f : ident := 101%positive.
Definition _free : ident := 62%positive.
Definition _freecond : ident := 69%positive.
Definition _freelock : ident := 65%positive.
Definition _freelock2 : ident := 93%positive.
Definition _h : ident := 88%positive.
Definition _head : ident := 5%positive.
Definition _i : ident := 77%positive.
Definition _i__1 : ident := 103%positive.
Definition _i__2 : ident := 104%positive.
Definition _i__3 : ident := 107%positive.
Definition _j : ident := 108%positive.
Definition _l : ident := 79%positive.
Definition _l__1 : ident := 105%positive.
Definition _len : ident := 84%positive.
Definition _length : ident := 4%positive.
Definition _lock : ident := 11%positive.
Definition _lock_t : ident := 2%positive.
Definition _main : ident := 91%positive.
Definition _makecond : ident := 68%positive.
Definition _makelock : ident := 64%positive.
Definition _malloc : ident := 63%positive.
Definition _n : ident := 72%positive.
Definition _newq : ident := 75%positive.
Definition _p : ident := 73%positive.
Definition _printf : ident := 92%positive.
Definition _q : ident := 76%positive.
Definition _q0 : ident := 96%positive.
Definition _q1 : ident := 106%positive.
Definition _q_add : ident := 87%positive.
Definition _q_del : ident := 82%positive.
Definition _q_new : ident := 80%positive.
Definition _q_remove : ident := 90%positive.
Definition _q_tryremove : ident := 89%positive.
Definition _queue : ident := 9%positive.
Definition _queue_t : ident := 12%positive.
Definition _r : ident := 83%positive.
Definition _release : ident := 67%positive.
Definition _release2 : ident := 94%positive.
Definition _remc : ident := 8%positive.
Definition _results : ident := 98%positive.
Definition _signalcond : ident := 71%positive.
Definition _spawn : ident := 95%positive.
Definition _surely_malloc : ident := 74%positive.
Definition _t : ident := 85%positive.
Definition _tail : ident := 6%positive.
Definition _tgt : ident := 81%positive.
Definition _thread_locks : ident := 97%positive.
Definition _tid : ident := 102%positive.
Definition _v : ident := 100%positive.
Definition _waitcond : ident := 70%positive.
Definition _t'1 : ident := 110%positive.
Definition _t'2 : ident := 111%positive.
Definition _t'3 : ident := 112%positive.
Definition _t'4 : ident := 113%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

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

Definition f_q_new := {|
  fn_return := (tptr (Tstruct _queue_t noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_newq, (tptr (Tstruct _queue_t noattr))) ::
               (_q, (tptr (Tstruct _queue noattr))) :: (_i, tint) ::
               (_c, (tptr tint)) :: (_l, (tptr (Tstruct _lock_t noattr))) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _queue_t noattr) tuint) :: nil))
    (Sset _newq
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _queue_t noattr)))))
  (Ssequence
    (Sset _q
      (Eaddrof
        (Efield
          (Ederef (Etempvar _newq (tptr (Tstruct _queue_t noattr)))
            (Tstruct _queue_t noattr)) _d (Tstruct _queue noattr))
        (tptr (Tstruct _queue noattr))))
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
                  (Efield
                    (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                      (Tstruct _queue noattr)) _buf (tarray (tptr tvoid) 10))
                  (Etempvar _i tint) (tptr (tptr tvoid))) (tptr tvoid))
              (Econst_int (Int.repr 0) tint)))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
              (Tstruct _queue noattr)) _length tint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                (Tstruct _queue noattr)) _head tint)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                  (Tstruct _queue noattr)) _tail tint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                         (tptr tvoid) cc_default))
                  ((Esizeof tint tuint) :: nil))
                (Sset _c (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tint))))
              (Ssequence
                (Scall None
                  (Evar _makecond (Tfunction (Tcons (tptr tint) Tnil) tvoid
                                    cc_default))
                  ((Etempvar _c (tptr tint)) :: nil))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                        (Tstruct _queue noattr)) _addc (tptr tint))
                    (Etempvar _c (tptr tint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                               (tptr tvoid) cc_default))
                        ((Esizeof tint tuint) :: nil))
                      (Sset _c
                        (Ecast (Etempvar _t'3 (tptr tvoid)) (tptr tint))))
                    (Ssequence
                      (Scall None
                        (Evar _makecond (Tfunction (Tcons (tptr tint) Tnil)
                                          tvoid cc_default))
                        ((Etempvar _c (tptr tint)) :: nil))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _q (tptr (Tstruct _queue noattr)))
                              (Tstruct _queue noattr)) _remc (tptr tint))
                          (Etempvar _c (tptr tint)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'4)
                              (Evar _surely_malloc (Tfunction
                                                     (Tcons tuint Tnil)
                                                     (tptr tvoid) cc_default))
                              ((Esizeof (Tstruct _lock_t noattr) tuint) ::
                               nil))
                            (Sset _l
                              (Ecast (Etempvar _t'4 (tptr tvoid))
                                (tptr (Tstruct _lock_t noattr)))))
                          (Ssequence
                            (Scall None
                              (Evar _makelock (Tfunction
                                                (Tcons (tptr tvoid) Tnil)
                                                tvoid cc_default))
                              ((Etempvar _l (tptr (Tstruct _lock_t noattr))) ::
                               nil))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _newq (tptr (Tstruct _queue_t noattr)))
                                    (Tstruct _queue_t noattr)) _lock
                                  (tptr (Tstruct _lock_t noattr)))
                                (Etempvar _l (tptr (Tstruct _lock_t noattr))))
                              (Ssequence
                                (Scall None
                                  (Evar _release (Tfunction
                                                   (Tcons (tptr tvoid) Tnil)
                                                   tvoid cc_default))
                                  ((Etempvar _l (tptr (Tstruct _lock_t noattr))) ::
                                   nil))
                                (Sreturn (Some (Etempvar _newq (tptr (Tstruct _queue_t noattr)))))))))))))))))))))
|}.

Definition f_q_del := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tgt, (tptr (Tstruct _queue_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr tvoid)) :: (_q, (tptr (Tstruct _queue noattr))) ::
               (_c, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Efield
      (Ederef (Etempvar _tgt (tptr (Tstruct _queue_t noattr)))
        (Tstruct _queue_t noattr)) _lock (tptr (Tstruct _lock_t noattr))))
  (Ssequence
    (Scall None
      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _l (tptr tvoid)) :: nil))
    (Ssequence
      (Scall None
        (Evar _freelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default)) ((Etempvar _l (tptr tvoid)) :: nil))
      (Ssequence
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _l (tptr tvoid)) :: nil))
        (Ssequence
          (Sset _q
            (Eaddrof
              (Efield
                (Ederef (Etempvar _tgt (tptr (Tstruct _queue_t noattr)))
                  (Tstruct _queue_t noattr)) _d (Tstruct _queue noattr))
              (tptr (Tstruct _queue noattr))))
          (Ssequence
            (Sset _c
              (Efield
                (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                  (Tstruct _queue noattr)) _addc (tptr tint)))
            (Ssequence
              (Scall None
                (Evar _freecond (Tfunction (Tcons (tptr tint) Tnil) tvoid
                                  cc_default))
                ((Etempvar _c (tptr tint)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
                  ((Etempvar _c (tptr tint)) :: nil))
                (Ssequence
                  (Sset _c
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                        (Tstruct _queue noattr)) _remc (tptr tint)))
                  (Ssequence
                    (Scall None
                      (Evar _freecond (Tfunction (Tcons (tptr tint) Tnil)
                                        tvoid cc_default))
                      ((Etempvar _c (tptr tint)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                      tvoid cc_default))
                        ((Etempvar _c (tptr tint)) :: nil))
                      (Scall None
                        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                      tvoid cc_default))
                        ((Etempvar _tgt (tptr (Tstruct _queue_t noattr))) ::
                         nil)))))))))))))
|}.

Definition f_q_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_tgt, (tptr (Tstruct _queue_t noattr))) ::
                (_r, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr tvoid)) :: (_q, (tptr (Tstruct _queue noattr))) ::
               (_len, tint) :: (_c, (tptr tint)) :: (_t, tint) ::
               (_c__1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Efield
      (Ederef (Etempvar _tgt (tptr (Tstruct _queue_t noattr)))
        (Tstruct _queue_t noattr)) _lock (tptr (Tstruct _lock_t noattr))))
  (Ssequence
    (Scall None
      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _l (tptr tvoid)) :: nil))
    (Ssequence
      (Sset _q
        (Eaddrof
          (Efield
            (Ederef (Etempvar _tgt (tptr (Tstruct _queue_t noattr)))
              (Tstruct _queue_t noattr)) _d (Tstruct _queue noattr))
          (tptr (Tstruct _queue noattr))))
      (Ssequence
        (Sset _len
          (Efield
            (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
              (Tstruct _queue noattr)) _length tint))
        (Ssequence
          (Swhile
            (Ebinop Oge (Etempvar _len tint) (Econst_int (Int.repr 10) tint)
              tint)
            (Ssequence
              (Sset _c
                (Efield
                  (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                    (Tstruct _queue noattr)) _addc (tptr tint)))
              (Ssequence
                (Scall None
                  (Evar _waitcond (Tfunction
                                    (Tcons (tptr tint)
                                      (Tcons (tptr tvoid) Tnil)) tvoid
                                    cc_default))
                  ((Etempvar _c (tptr tint)) :: (Etempvar _l (tptr tvoid)) ::
                   nil))
                (Sset _len
                  (Efield
                    (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                      (Tstruct _queue noattr)) _length tint)))))
          (Ssequence
            (Sset _t
              (Efield
                (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                  (Tstruct _queue noattr)) _tail tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                        (Tstruct _queue noattr)) _buf
                      (tarray (tptr tvoid) 10)) (Etempvar _t tint)
                    (tptr (tptr tvoid))) (tptr tvoid))
                (Etempvar _r (tptr tvoid)))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                      (Tstruct _queue noattr)) _tail tint)
                  (Ebinop Omod
                    (Ebinop Oadd (Etempvar _t tint)
                      (Econst_int (Int.repr 1) tint) tint)
                    (Econst_int (Int.repr 10) tint) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                        (Tstruct _queue noattr)) _length tint)
                    (Ebinop Oadd (Etempvar _len tint)
                      (Econst_int (Int.repr 1) tint) tint))
                  (Ssequence
                    (Sset _c__1
                      (Efield
                        (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                          (Tstruct _queue noattr)) _remc (tptr tint)))
                    (Ssequence
                      (Scall None
                        (Evar _signalcond (Tfunction (Tcons (tptr tint) Tnil)
                                            tvoid cc_default))
                        ((Etempvar _c__1 (tptr tint)) :: nil))
                      (Scall None
                        (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil)
                                         tvoid cc_default))
                        ((Etempvar _l (tptr tvoid)) :: nil)))))))))))))
|}.

Definition f_q_tryremove := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_tgt, (tptr (Tstruct _queue_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr tvoid)) :: (_q, (tptr (Tstruct _queue noattr))) ::
               (_len, tint) :: (_h, tint) :: (_r, (tptr tvoid)) ::
               (_c, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Efield
      (Ederef (Etempvar _tgt (tptr (Tstruct _queue_t noattr)))
        (Tstruct _queue_t noattr)) _lock (tptr (Tstruct _lock_t noattr))))
  (Ssequence
    (Scall None
      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _l (tptr tvoid)) :: nil))
    (Ssequence
      (Sset _q
        (Eaddrof
          (Efield
            (Ederef (Etempvar _tgt (tptr (Tstruct _queue_t noattr)))
              (Tstruct _queue_t noattr)) _d (Tstruct _queue noattr))
          (tptr (Tstruct _queue noattr))))
      (Ssequence
        (Sset _len
          (Efield
            (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
              (Tstruct _queue noattr)) _length tint))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _len tint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Scall None
                (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                 cc_default))
                ((Etempvar _l (tptr tvoid)) :: nil))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))
            Sskip)
          (Ssequence
            (Sset _h
              (Efield
                (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                  (Tstruct _queue noattr)) _head tint))
            (Ssequence
              (Sset _r
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                        (Tstruct _queue noattr)) _buf
                      (tarray (tptr tvoid) 10)) (Etempvar _h tint)
                    (tptr (tptr tvoid))) (tptr tvoid)))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                          (Tstruct _queue noattr)) _buf
                        (tarray (tptr tvoid) 10)) (Etempvar _h tint)
                      (tptr (tptr tvoid))) (tptr tvoid))
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                        (Tstruct _queue noattr)) _head tint)
                    (Ebinop Omod
                      (Ebinop Oadd (Etempvar _h tint)
                        (Econst_int (Int.repr 1) tint) tint)
                      (Econst_int (Int.repr 10) tint) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                          (Tstruct _queue noattr)) _length tint)
                      (Ebinop Osub (Etempvar _len tint)
                        (Econst_int (Int.repr 1) tint) tint))
                    (Ssequence
                      (Sset _c
                        (Efield
                          (Ederef
                            (Etempvar _q (tptr (Tstruct _queue noattr)))
                            (Tstruct _queue noattr)) _addc (tptr tint)))
                      (Ssequence
                        (Scall None
                          (Evar _signalcond (Tfunction
                                              (Tcons (tptr tint) Tnil) tvoid
                                              cc_default))
                          ((Etempvar _c (tptr tint)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _release (Tfunction
                                             (Tcons (tptr tvoid) Tnil) tvoid
                                             cc_default))
                            ((Etempvar _l (tptr tvoid)) :: nil))
                          (Sreturn (Some (Etempvar _r (tptr tvoid)))))))))))))))))
|}.

Definition f_q_remove := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_tgt, (tptr (Tstruct _queue_t noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr tvoid)) :: (_q, (tptr (Tstruct _queue noattr))) ::
               (_len, tint) :: (_c, (tptr tint)) :: (_h, tint) ::
               (_r, (tptr tvoid)) :: (_c__1, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _l
    (Efield
      (Ederef (Etempvar _tgt (tptr (Tstruct _queue_t noattr)))
        (Tstruct _queue_t noattr)) _lock (tptr (Tstruct _lock_t noattr))))
  (Ssequence
    (Scall None
      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _l (tptr tvoid)) :: nil))
    (Ssequence
      (Sset _q
        (Eaddrof
          (Efield
            (Ederef (Etempvar _tgt (tptr (Tstruct _queue_t noattr)))
              (Tstruct _queue_t noattr)) _d (Tstruct _queue noattr))
          (tptr (Tstruct _queue noattr))))
      (Ssequence
        (Sset _len
          (Efield
            (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
              (Tstruct _queue noattr)) _length tint))
        (Ssequence
          (Swhile
            (Ebinop Oeq (Etempvar _len tint) (Econst_int (Int.repr 0) tint)
              tint)
            (Ssequence
              (Sset _c
                (Efield
                  (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                    (Tstruct _queue noattr)) _remc (tptr tint)))
              (Ssequence
                (Scall None
                  (Evar _waitcond (Tfunction
                                    (Tcons (tptr tint)
                                      (Tcons (tptr tvoid) Tnil)) tvoid
                                    cc_default))
                  ((Etempvar _c (tptr tint)) :: (Etempvar _l (tptr tvoid)) ::
                   nil))
                (Sset _len
                  (Efield
                    (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                      (Tstruct _queue noattr)) _length tint)))))
          (Ssequence
            (Sset _h
              (Efield
                (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                  (Tstruct _queue noattr)) _head tint))
            (Ssequence
              (Sset _r
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                        (Tstruct _queue noattr)) _buf
                      (tarray (tptr tvoid) 10)) (Etempvar _h tint)
                    (tptr (tptr tvoid))) (tptr tvoid)))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                          (Tstruct _queue noattr)) _buf
                        (tarray (tptr tvoid) 10)) (Etempvar _h tint)
                      (tptr (tptr tvoid))) (tptr tvoid))
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                        (Tstruct _queue noattr)) _head tint)
                    (Ebinop Omod
                      (Ebinop Oadd (Etempvar _h tint)
                        (Econst_int (Int.repr 1) tint) tint)
                      (Econst_int (Int.repr 10) tint) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _q (tptr (Tstruct _queue noattr)))
                          (Tstruct _queue noattr)) _length tint)
                      (Ebinop Osub (Etempvar _len tint)
                        (Econst_int (Int.repr 1) tint) tint))
                    (Ssequence
                      (Sset _c__1
                        (Efield
                          (Ederef
                            (Etempvar _q (tptr (Tstruct _queue noattr)))
                            (Tstruct _queue noattr)) _addc (tptr tint)))
                      (Ssequence
                        (Scall None
                          (Evar _signalcond (Tfunction
                                              (Tcons (tptr tint) Tnil) tvoid
                                              cc_default))
                          ((Etempvar _c__1 (tptr tint)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _release (Tfunction
                                             (Tcons (tptr tvoid) Tnil) tvoid
                                             cc_default))
                            ((Etempvar _l (tptr tvoid)) :: nil))
                          (Sreturn (Some (Etempvar _r (tptr tvoid)))))))))))))))))
|}.

Definition v_q0 := {|
  gvar_info := (tptr (Tstruct _queue_t noattr));
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_thread_locks := {|
  gvar_info := (tarray (tptr (Tstruct _lock_t noattr)) 3);
  gvar_init := (Init_space 12 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_results := {|
  gvar_info := (tarray (tarray tint 3) 3);
  gvar_init := (Init_space 36 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_f := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_arg, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, tint) :: (_i, tint) :: (_d, (tptr tint)) :: (_v, tint) ::
               (_l, (tptr (Tstruct _lock_t noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t (Ederef (Ecast (Etempvar _arg (tptr tvoid)) (tptr tint)) tint))
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
                (Evar _q_remove (Tfunction
                                  (Tcons (tptr (Tstruct _queue_t noattr))
                                    Tnil) (tptr tvoid) cc_default))
                ((Evar _q0 (tptr (Tstruct _queue_t noattr))) :: nil))
              (Sset _d (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tint))))
            (Ssequence
              (Sset _v (Ederef (Etempvar _d (tptr tint)) tint))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Ederef
                      (Ebinop Oadd (Evar _results (tarray (tarray tint 3) 3))
                        (Etempvar _t tint) (tptr (tarray tint 3)))
                      (tarray tint 3)) (Etempvar _i tint) (tptr tint)) tint)
                (Etempvar _v tint)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Sset _l
        (Ederef
          (Ebinop Oadd
            (Evar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 3))
            (Etempvar _t tint) (tptr (tptr (Tstruct _lock_t noattr))))
          (tptr (Tstruct _lock_t noattr))))
      (Ssequence
        (Scall None
          (Evar _release2 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
          ((Etempvar _l (tptr (Tstruct _lock_t noattr))) :: nil))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_tid, (tarray tint 3)) :: nil);
  fn_temps := ((_i, tint) :: (_l, (tptr (Tstruct _lock_t noattr))) ::
               (_t, (tptr tvoid)) :: (_i__1, tint) :: (_d, (tptr tint)) ::
               (_i__2, tint) :: (_l__1, (tptr (Tstruct _lock_t noattr))) ::
               (_q1, (tptr (Tstruct _queue_t noattr))) :: (_i__3, tint) ::
               (_j, tint) :: (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _queue_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _tid (tarray tint 3))
          (Econst_int (Int.repr 0) tint) (tptr tint)) tint)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _tid (tarray tint 3))
            (Econst_int (Int.repr 1) tint) (tptr tint)) tint)
        (Econst_int (Int.repr 1) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _tid (tarray tint 3))
              (Econst_int (Int.repr 2) tint) (tptr tint)) tint)
          (Econst_int (Int.repr 2) tint))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _q_new (Tfunction Tnil (tptr (Tstruct _queue_t noattr))
                             cc_default)) nil)
            (Sassign (Evar _q0 (tptr (Tstruct _queue_t noattr)))
              (Etempvar _t'1 (tptr (Tstruct _queue_t noattr)))))
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
                      (Scall (Some _t'2)
                        (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                        (tptr tvoid) cc_default))
                        ((Esizeof (Tstruct _lock_t noattr) tuint) :: nil))
                      (Sset _l
                        (Ecast (Etempvar _t'2 (tptr tvoid))
                          (tptr (Tstruct _lock_t noattr)))))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Evar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 3))
                            (Etempvar _i tint)
                            (tptr (tptr (Tstruct _lock_t noattr))))
                          (tptr (Tstruct _lock_t noattr)))
                        (Etempvar _l (tptr (Tstruct _lock_t noattr))))
                      (Ssequence
                        (Scall None
                          (Evar _makelock (Tfunction
                                            (Tcons (tptr tvoid) Tnil) tvoid
                                            cc_default))
                          ((Ecast
                             (Etempvar _l (tptr (Tstruct _lock_t noattr)))
                             (tptr tvoid)) :: nil))
                        (Ssequence
                          (Sset _t
                            (Eaddrof
                              (Ederef
                                (Ebinop Oadd (Evar _tid (tarray tint 3))
                                  (Etempvar _i tint) (tptr tint)) tint)
                              (tptr tint)))
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
                                 (Evar _f (Tfunction
                                            (Tcons (tptr tvoid) Tnil)
                                            (tptr tvoid) cc_default))
                                 (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                         (tptr tvoid) cc_default)))
                               (tptr tvoid)) :: (Etempvar _t (tptr tvoid)) ::
                             nil)))))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Ssequence
                (Sset _i__1 (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i__1 tint)
                                   (Econst_int (Int.repr 9) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'3)
                          (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                          (tptr tvoid) cc_default))
                          ((Esizeof tint tuint) :: nil))
                        (Sset _d
                          (Ecast (Etempvar _t'3 (tptr tvoid)) (tptr tint))))
                      (Ssequence
                        (Sassign (Ederef (Etempvar _d (tptr tint)) tint)
                          (Etempvar _i__1 tint))
                        (Scall None
                          (Evar _q_add (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _queue_t noattr))
                                           (Tcons (tptr tvoid) Tnil)) tvoid
                                         cc_default))
                          ((Evar _q0 (tptr (Tstruct _queue_t noattr))) ::
                           (Etempvar _d (tptr tint)) :: nil)))))
                  (Sset _i__1
                    (Ebinop Oadd (Etempvar _i__1 tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Ssequence
                  (Sset _i__2 (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i__2 tint)
                                     (Econst_int (Int.repr 3) tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Sset _l__1
                          (Ederef
                            (Ebinop Oadd
                              (Evar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 3))
                              (Etempvar _i__2 tint)
                              (tptr (tptr (Tstruct _lock_t noattr))))
                            (tptr (Tstruct _lock_t noattr))))
                        (Ssequence
                          (Scall None
                            (Evar _acquire (Tfunction
                                             (Tcons (tptr tvoid) Tnil) tvoid
                                             cc_default))
                            ((Etempvar _l__1 (tptr (Tstruct _lock_t noattr))) ::
                             nil))
                          (Ssequence
                            (Scall None
                              (Evar _freelock2 (Tfunction
                                                 (Tcons (tptr tvoid) Tnil)
                                                 tvoid cc_default))
                              ((Etempvar _l__1 (tptr (Tstruct _lock_t noattr))) ::
                               nil))
                            (Scall None
                              (Evar _free (Tfunction
                                            (Tcons (tptr tvoid) Tnil) tvoid
                                            cc_default))
                              ((Etempvar _l__1 (tptr (Tstruct _lock_t noattr))) ::
                               nil))))))
                    (Sset _i__2
                      (Ebinop Oadd (Etempvar _i__2 tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                (Ssequence
                  (Sset _q1 (Evar _q0 (tptr (Tstruct _queue_t noattr))))
                  (Ssequence
                    (Scall None
                      (Evar _q_del (Tfunction
                                     (Tcons (tptr (Tstruct _queue_t noattr))
                                       Tnil) tvoid cc_default))
                      ((Etempvar _q1 (tptr (Tstruct _queue_t noattr))) ::
                       nil))
                    (Ssequence
                      (Sset _i__3 (Econst_int (Int.repr 0) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i__3 tint)
                                         (Econst_int (Int.repr 3) tint) tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Sset _j (Econst_int (Int.repr 0) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt (Etempvar _j tint)
                                               (Econst_int (Int.repr 3) tint)
                                               tint)
                                  Sskip
                                  Sbreak)
                                (Scall None
                                  (Evar _printf (Tfunction
                                                  (Tcons (tptr tschar) Tnil)
                                                  tint
                                                  {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                                  ((Evar ___stringlit_1 (tarray tschar 4)) ::
                                   (Ederef
                                     (Ebinop Oadd
                                       (Ederef
                                         (Ebinop Oadd
                                           (Evar _results (tarray (tarray tint 3) 3))
                                           (Etempvar _i__3 tint)
                                           (tptr (tarray tint 3)))
                                         (tarray tint 3)) (Etempvar _j tint)
                                       (tptr tint)) tint) :: nil)))
                              (Sset _j
                                (Ebinop Oadd (Etempvar _j tint)
                                  (Econst_int (Int.repr 1) tint) tint)))))
                        (Sset _i__3
                          (Ebinop Oadd (Etempvar _i__3 tint)
                            (Econst_int (Int.repr 1) tint) tint)))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _lock_t Struct ((_a, (tarray (tptr tvoid) 4)) :: nil) noattr ::
 Composite _queue Struct
   ((_buf, (tarray (tptr tvoid) 10)) :: (_length, tint) :: (_head, tint) ::
    (_tail, tint) :: (_addc, (tptr tint)) :: (_remc, (tptr tint)) :: nil)
   noattr ::
 Composite _queue_t Struct
   ((_d, (Tstruct _queue noattr)) ::
    (_lock, (tptr (Tstruct _lock_t noattr))) :: nil)
   noattr :: nil).

Definition prog : Clight.program := {|
prog_defs :=
((___stringlit_1, Gvar v___stringlit_1) ::
 (___builtin_fabs,
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
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_makelock,
   Gfun(External (EF_external "makelock"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_freelock,
   Gfun(External (EF_external "freelock"
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
 (_freelock2,
   Gfun(External (EF_external "freelock2"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_release2,
   Gfun(External (EF_external "release2"
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
 (_freecond,
   Gfun(External (EF_external "freecond"
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
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_q_new, Gfun(Internal f_q_new)) :: (_q_del, Gfun(Internal f_q_del)) ::
 (_q_add, Gfun(Internal f_q_add)) ::
 (_q_tryremove, Gfun(Internal f_q_tryremove)) ::
 (_q_remove, Gfun(Internal f_q_remove)) :: (_q0, Gvar v_q0) ::
 (_thread_locks, Gvar v_thread_locks) :: (_results, Gvar v_results) ::
 (_f, Gfun(Internal f_f)) :: (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: _f :: _results :: _thread_locks :: _q0 :: _q_remove ::
 _q_tryremove :: _q_add :: _q_del :: _q_new :: _surely_malloc ::
 _signalcond :: _waitcond :: _freecond :: _makecond :: _spawn :: _release2 ::
 _freelock2 :: _release :: _acquire :: _freelock :: _makelock :: _malloc ::
 _free :: _exit :: _printf :: ___builtin_debug :: ___builtin_nop ::
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

