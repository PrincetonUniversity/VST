
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
Definition _a : ident := 1%positive.
Definition _acquire : ident := 65%positive.
Definition _addc : ident := 7%positive.
Definition _buf : ident := 3%positive.
Definition _c : ident := 74%positive.
Definition _c__1 : ident := 82%positive.
Definition _d : ident := 10%positive.
Definition _free : ident := 61%positive.
Definition _freecond : ident := 68%positive.
Definition _freelock : ident := 64%positive.
Definition _h : ident := 84%positive.
Definition _head : ident := 5%positive.
Definition _i : ident := 73%positive.
Definition _l : ident := 75%positive.
Definition _len : ident := 80%positive.
Definition _length : ident := 4%positive.
Definition _lock : ident := 11%positive.
Definition _lock_t : ident := 2%positive.
Definition _main : ident := 88%positive.
Definition _makecond : ident := 67%positive.
Definition _makelock : ident := 63%positive.
Definition _malloc : ident := 62%positive.
Definition _newq : ident := 71%positive.
Definition _q : ident := 72%positive.
Definition _q_add : ident := 83%positive.
Definition _q_del : ident := 78%positive.
Definition _q_new : ident := 76%positive.
Definition _q_remove : ident := 87%positive.
Definition _q_tryremove : ident := 86%positive.
Definition _queue : ident := 9%positive.
Definition _queue_t : ident := 12%positive.
Definition _r : ident := 85%positive.
Definition _release : ident := 66%positive.
Definition _remc : ident := 8%positive.
Definition _request : ident := 79%positive.
Definition _signalcond : ident := 70%positive.
Definition _t : ident := 81%positive.
Definition _tail : ident := 6%positive.
Definition _tgt : ident := 77%positive.
Definition _waitcond : ident := 69%positive.
Definition _t'1 : ident := 89%positive.
Definition _t'2 : ident := 90%positive.
Definition _t'3 : ident := 91%positive.
Definition _t'4 : ident := 92%positive.

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
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
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
                  (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                  cc_default)) ((Esizeof tint tuint) :: nil))
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
                        (Evar _malloc (Tfunction (Tcons tuint Tnil)
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
                              (Evar _malloc (Tfunction (Tcons tuint Tnil)
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
                (_request, (tptr tvoid)) :: nil);
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
                (Etempvar _request (tptr tvoid)))
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
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
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
 (_q_new, Gfun(Internal f_q_new)) :: (_q_del, Gfun(Internal f_q_del)) ::
 (_q_add, Gfun(Internal f_q_add)) ::
 (_q_tryremove, Gfun(Internal f_q_tryremove)) ::
 (_q_remove, Gfun(Internal f_q_remove)) :: nil);
prog_public :=
(_q_remove :: _q_tryremove :: _q_add :: _q_del :: _q_new :: _signalcond ::
 _waitcond :: _freecond :: _makecond :: _release :: _acquire :: _freelock ::
 _makelock :: _malloc :: _free :: ___builtin_debug :: ___builtin_nop ::
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

