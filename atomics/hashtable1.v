
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition _CAS_SC : ident := 74%positive.
Definition ___builtin_annot : ident := 8%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition ___builtin_bswap : ident := 32%positive.
Definition ___builtin_bswap16 : ident := 34%positive.
Definition ___builtin_bswap32 : ident := 33%positive.
Definition ___builtin_clz : ident := 35%positive.
Definition ___builtin_clzl : ident := 36%positive.
Definition ___builtin_clzll : ident := 37%positive.
Definition ___builtin_ctz : ident := 38%positive.
Definition ___builtin_ctzl : ident := 39%positive.
Definition ___builtin_ctzll : ident := 40%positive.
Definition ___builtin_debug : ident := 53%positive.
Definition ___builtin_fabs : ident := 6%positive.
Definition ___builtin_fmadd : ident := 44%positive.
Definition ___builtin_fmax : ident := 42%positive.
Definition ___builtin_fmin : ident := 43%positive.
Definition ___builtin_fmsub : ident := 45%positive.
Definition ___builtin_fnmadd : ident := 46%positive.
Definition ___builtin_fnmsub : ident := 47%positive.
Definition ___builtin_fsqrt : ident := 41%positive.
Definition ___builtin_membar : ident := 10%positive.
Definition ___builtin_memcpy_aligned : ident := 7%positive.
Definition ___builtin_nop : ident := 52%positive.
Definition ___builtin_read16_reversed : ident := 48%positive.
Definition ___builtin_read32_reversed : ident := 49%positive.
Definition ___builtin_va_arg : ident := 12%positive.
Definition ___builtin_va_copy : ident := 13%positive.
Definition ___builtin_va_end : ident := 14%positive.
Definition ___builtin_va_start : ident := 11%positive.
Definition ___builtin_write16_reversed : ident := 50%positive.
Definition ___builtin_write32_reversed : ident := 51%positive.
Definition ___compcert_va_composite : ident := 18%positive.
Definition ___compcert_va_float64 : ident := 17%positive.
Definition ___compcert_va_int32 : ident := 15%positive.
Definition ___compcert_va_int64 : ident := 16%positive.
Definition ___i64_dtos : ident := 19%positive.
Definition ___i64_dtou : ident := 20%positive.
Definition ___i64_sar : ident := 31%positive.
Definition ___i64_sdiv : ident := 25%positive.
Definition ___i64_shl : ident := 29%positive.
Definition ___i64_shr : ident := 30%positive.
Definition ___i64_smod : ident := 27%positive.
Definition ___i64_stod : ident := 21%positive.
Definition ___i64_stof : ident := 23%positive.
Definition ___i64_udiv : ident := 26%positive.
Definition ___i64_umod : ident := 28%positive.
Definition ___i64_utod : ident := 22%positive.
Definition ___i64_utof : ident := 24%positive.
Definition _a : ident := 1%positive.
Definition _acquire : ident := 59%positive.
Definition _add_item : ident := 92%positive.
Definition _arg : ident := 97%positive.
Definition _atomic_loc : ident := 5%positive.
Definition _c : ident := 73%positive.
Definition _entry : ident := 79%positive.
Definition _exit : ident := 54%positive.
Definition _f : ident := 102%positive.
Definition _free : ident := 55%positive.
Definition _free_atomic : ident := 68%positive.
Definition _freelock : ident := 58%positive.
Definition _freelock2 : ident := 80%positive.
Definition _freeze_table : ident := 96%positive.
Definition _get_item : ident := 91%positive.
Definition _i : ident := 64%positive.
Definition _i__1 : ident := 103%positive.
Definition _i__2 : ident := 104%positive.
Definition _i__3 : ident := 106%positive.
Definition _idx : ident := 87%positive.
Definition _init_table : ident := 93%positive.
Definition _integer_hash : ident := 86%positive.
Definition _key : ident := 77%positive.
Definition _keys : ident := 94%positive.
Definition _l : ident := 65%positive.
Definition _l__1 : ident := 105%positive.
Definition _load_SC : ident := 70%positive.
Definition _load_relaxed : ident := 75%positive.
Definition _lock : ident := 4%positive.
Definition _lock_t : ident := 2%positive.
Definition _m_entries : ident := 83%positive.
Definition _main : ident := 76%positive.
Definition _make_atomic : ident := 66%positive.
Definition _makelock : ident := 57%positive.
Definition _malloc : ident := 56%positive.
Definition _n : ident := 61%positive.
Definition _p : ident := 62%positive.
Definition _probed_key : ident := 88%positive.
Definition _r : ident := 101%positive.
Definition _release : ident := 60%positive.
Definition _release2 : ident := 81%positive.
Definition _res : ident := 99%positive.
Definition _result : ident := 89%positive.
Definition _results : ident := 85%positive.
Definition _set_item : ident := 90%positive.
Definition _spawn : ident := 82%positive.
Definition _store_SC : ident := 72%positive.
Definition _surely_malloc : ident := 63%positive.
Definition _t : ident := 98%positive.
Definition _tgt : ident := 67%positive.
Definition _thread_locks : ident := 84%positive.
Definition _total : ident := 100%positive.
Definition _v : ident := 71%positive.
Definition _val : ident := 3%positive.
Definition _value : ident := 78%positive.
Definition _values : ident := 95%positive.
Definition _x : ident := 69%positive.
Definition _t'1 : ident := 107%positive.
Definition _t'2 : ident := 108%positive.
Definition _t'3 : ident := 109%positive.
Definition _t'4 : ident := 110%positive.

Definition v_m_entries := {|
  gvar_info := (tarray (Tstruct _entry noattr) 16384);
  gvar_init := (Init_space 131072 :: nil);
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
  gvar_info := (tarray (tptr tint) 3);
  gvar_init := (Init_space 12 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_integer_hash := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_i, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Omul (Ecast (Etempvar _i tint) tuint)
                 (Ecast (Econst_int (Int.repr 654435761) tint) tuint) tuint)))
|}.

Definition f_set_item := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, tint) :: (_value, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_idx, tint) :: (_i, (tptr (Tstruct _atomic_loc noattr))) ::
               (_probed_key, tint) :: (_result, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _integer_hash (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Etempvar _key tint) :: nil))
    (Sset _idx (Etempvar _t'1 tint)))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _idx
          (Ebinop Oand (Etempvar _idx tint)
            (Ebinop Osub (Econst_int (Int.repr 16384) tint)
              (Econst_int (Int.repr 1) tint) tint) tint))
        (Ssequence
          (Sset _i
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                  (Etempvar _idx tint) (tptr (Tstruct _entry noattr)))
                (Tstruct _entry noattr)) _key
              (tptr (Tstruct _atomic_loc noattr))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _load_SC (Tfunction
                                 (Tcons (tptr (Tstruct _atomic_loc noattr))
                                   Tnil) tint cc_default))
                ((Etempvar _i (tptr (Tstruct _atomic_loc noattr))) :: nil))
              (Sset _probed_key (Etempvar _t'2 tint)))
            (Ssequence
              (Sifthenelse (Ebinop One (Etempvar _probed_key tint)
                             (Etempvar _key tint) tint)
                (Ssequence
                  (Sifthenelse (Ebinop One (Etempvar _probed_key tint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    Scontinue
                    Sskip)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _CAS_SC (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _atomic_loc noattr))
                                          (Tcons tint (Tcons tint Tnil)))
                                        tint cc_default))
                        ((Etempvar _i (tptr (Tstruct _atomic_loc noattr))) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Etempvar _key tint) :: nil))
                      (Sset _result (Etempvar _t'3 tint)))
                    (Sifthenelse (Eunop Onotbool (Etempvar _result tint)
                                   tint)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'4)
                            (Evar _load_SC (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _atomic_loc noattr))
                                               Tnil) tint cc_default))
                            ((Etempvar _i (tptr (Tstruct _atomic_loc noattr))) ::
                             nil))
                          (Sset _probed_key (Etempvar _t'4 tint)))
                        (Sifthenelse (Ebinop One (Etempvar _probed_key tint)
                                       (Etempvar _key tint) tint)
                          Scontinue
                          Sskip))
                      Sskip)))
                Sskip)
              (Ssequence
                (Sset _i
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                        (Etempvar _idx tint) (tptr (Tstruct _entry noattr)))
                      (Tstruct _entry noattr)) _value
                    (tptr (Tstruct _atomic_loc noattr))))
                (Ssequence
                  (Scall None
                    (Evar _store_SC (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _atomic_loc noattr))
                                        (Tcons tint Tnil)) tvoid cc_default))
                    ((Etempvar _i (tptr (Tstruct _atomic_loc noattr))) ::
                     (Etempvar _value tint) :: nil))
                  (Sreturn None))))))))
    (Sset _idx
      (Ebinop Oadd (Etempvar _idx tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_get_item := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_key, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_idx, tint) :: (_i, (tptr (Tstruct _atomic_loc noattr))) ::
               (_probed_key, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _integer_hash (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Etempvar _key tint) :: nil))
    (Sset _idx (Etempvar _t'1 tint)))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _idx
          (Ebinop Oand (Etempvar _idx tint)
            (Ebinop Osub (Econst_int (Int.repr 16384) tint)
              (Econst_int (Int.repr 1) tint) tint) tint))
        (Ssequence
          (Sset _i
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                  (Etempvar _idx tint) (tptr (Tstruct _entry noattr)))
                (Tstruct _entry noattr)) _key
              (tptr (Tstruct _atomic_loc noattr))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _load_SC (Tfunction
                                 (Tcons (tptr (Tstruct _atomic_loc noattr))
                                   Tnil) tint cc_default))
                ((Etempvar _i (tptr (Tstruct _atomic_loc noattr))) :: nil))
              (Sset _probed_key (Etempvar _t'2 tint)))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _probed_key tint)
                             (Etempvar _key tint) tint)
                (Ssequence
                  (Sset _i
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                          (Etempvar _idx tint)
                          (tptr (Tstruct _entry noattr)))
                        (Tstruct _entry noattr)) _value
                      (tptr (Tstruct _atomic_loc noattr))))
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _load_SC (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _atomic_loc noattr))
                                         Tnil) tint cc_default))
                      ((Etempvar _i (tptr (Tstruct _atomic_loc noattr))) ::
                       nil))
                    (Sreturn (Some (Etempvar _t'3 tint)))))
                Sskip)
              (Sifthenelse (Ebinop Oeq (Etempvar _probed_key tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip))))))
    (Sset _idx
      (Ebinop Oadd (Etempvar _idx tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_add_item := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_key, tint) :: (_value, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_idx, tint) :: (_i, (tptr (Tstruct _atomic_loc noattr))) ::
               (_probed_key, tint) :: (_result, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _integer_hash (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Etempvar _key tint) :: nil))
    (Sset _idx (Etempvar _t'1 tint)))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _idx
          (Ebinop Oand (Etempvar _idx tint)
            (Ebinop Osub (Econst_int (Int.repr 16384) tint)
              (Econst_int (Int.repr 1) tint) tint) tint))
        (Ssequence
          (Sset _i
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                  (Etempvar _idx tint) (tptr (Tstruct _entry noattr)))
                (Tstruct _entry noattr)) _key
              (tptr (Tstruct _atomic_loc noattr))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _load_SC (Tfunction
                                 (Tcons (tptr (Tstruct _atomic_loc noattr))
                                   Tnil) tint cc_default))
                ((Etempvar _i (tptr (Tstruct _atomic_loc noattr))) :: nil))
              (Sset _probed_key (Etempvar _t'2 tint)))
            (Ssequence
              (Sifthenelse (Ebinop Oeq (Etempvar _probed_key tint)
                             (Etempvar _key tint) tint)
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                Sskip)
              (Ssequence
                (Sifthenelse (Ebinop One (Etempvar _probed_key tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  Scontinue
                  Sskip)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _CAS_SC (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _atomic_loc noattr))
                                        (Tcons tint (Tcons tint Tnil))) tint
                                      cc_default))
                      ((Etempvar _i (tptr (Tstruct _atomic_loc noattr))) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Etempvar _key tint) :: nil))
                    (Sset _result (Etempvar _t'3 tint)))
                  (Ssequence
                    (Sifthenelse (Eunop Onotbool (Etempvar _result tint)
                                   tint)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'4)
                            (Evar _load_SC (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _atomic_loc noattr))
                                               Tnil) tint cc_default))
                            ((Etempvar _i (tptr (Tstruct _atomic_loc noattr))) ::
                             nil))
                          (Sset _probed_key (Etempvar _t'4 tint)))
                        (Sifthenelse (Ebinop Oeq (Etempvar _probed_key tint)
                                       (Etempvar _key tint) tint)
                          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                          Scontinue))
                      Sskip)
                    (Ssequence
                      (Sset _i
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                              (Etempvar _idx tint)
                              (tptr (Tstruct _entry noattr)))
                            (Tstruct _entry noattr)) _value
                          (tptr (Tstruct _atomic_loc noattr))))
                      (Ssequence
                        (Scall None
                          (Evar _store_SC (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _atomic_loc noattr))
                                              (Tcons tint Tnil)) tvoid
                                            cc_default))
                          ((Etempvar _i (tptr (Tstruct _atomic_loc noattr))) ::
                           (Etempvar _value tint) :: nil))
                        (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))))))
    (Sset _idx
      (Ebinop Oadd (Etempvar _idx tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_init_table := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'2, (tptr (Tstruct _atomic_loc noattr))) ::
               (_t'1, (tptr (Tstruct _atomic_loc noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 16384) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _make_atomic (Tfunction (Tcons tint Tnil)
                                 (tptr (Tstruct _atomic_loc noattr))
                                 cc_default))
            ((Econst_int (Int.repr 0) tint) :: nil))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                  (Etempvar _i tint) (tptr (Tstruct _entry noattr)))
                (Tstruct _entry noattr)) _key
              (tptr (Tstruct _atomic_loc noattr)))
            (Etempvar _t'1 (tptr (Tstruct _atomic_loc noattr)))))
        (Ssequence
          (Scall (Some _t'2)
            (Evar _make_atomic (Tfunction (Tcons tint Tnil)
                                 (tptr (Tstruct _atomic_loc noattr))
                                 cc_default))
            ((Econst_int (Int.repr 0) tint) :: nil))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                  (Etempvar _i tint) (tptr (Tstruct _entry noattr)))
                (Tstruct _entry noattr)) _value
              (tptr (Tstruct _atomic_loc noattr)))
            (Etempvar _t'2 (tptr (Tstruct _atomic_loc noattr)))))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_freeze_table := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_keys, (tptr tint)) :: (_values, (tptr tint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_l, (tptr (Tstruct _atomic_loc noattr))) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                     (Econst_int (Int.repr 16384) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _l
          (Efield
            (Ederef
              (Ebinop Oadd
                (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                (Etempvar _i tint) (tptr (Tstruct _entry noattr)))
              (Tstruct _entry noattr)) _key
            (tptr (Tstruct _atomic_loc noattr))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _free_atomic (Tfunction
                                   (Tcons (tptr (Tstruct _atomic_loc noattr))
                                     Tnil) tint cc_default))
              ((Etempvar _l (tptr (Tstruct _atomic_loc noattr))) :: nil))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _keys (tptr tint)) (Etempvar _i tint)
                  (tptr tint)) tint) (Etempvar _t'1 tint)))
          (Ssequence
            (Sset _l
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                    (Etempvar _i tint) (tptr (Tstruct _entry noattr)))
                  (Tstruct _entry noattr)) _value
                (tptr (Tstruct _atomic_loc noattr))))
            (Ssequence
              (Scall (Some _t'2)
                (Evar _free_atomic (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _atomic_loc noattr))
                                       Tnil) tint cc_default))
                ((Etempvar _l (tptr (Tstruct _atomic_loc noattr))) :: nil))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _values (tptr tint))
                    (Etempvar _i tint) (tptr tint)) tint)
                (Etempvar _t'2 tint)))))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_f := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_arg, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, tint) :: (_l, (tptr (Tstruct _lock_t noattr))) ::
               (_res, (tptr tint)) :: (_total, tint) :: (_i, tint) ::
               (_r, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t (Ederef (Ecast (Etempvar _arg (tptr tvoid)) (tptr tint)) tint))
  (Ssequence
    (Sset _l
      (Ederef
        (Ebinop Oadd
          (Evar _thread_locks (tarray (tptr (Tstruct _lock_t noattr)) 3))
          (Etempvar _t tint) (tptr (tptr (Tstruct _lock_t noattr))))
        (tptr (Tstruct _lock_t noattr))))
    (Ssequence
      (Sset _res
        (Ederef
          (Ebinop Oadd (Evar _results (tarray (tptr tint) 3))
            (Etempvar _t tint) (tptr (tptr tint))) (tptr tint)))
      (Ssequence
        (Sset _total (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default)) ((Etempvar _arg (tptr tvoid)) :: nil))
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
                        (Evar _add_item (Tfunction
                                          (Tcons tint (Tcons tint Tnil)) tint
                                          cc_default))
                        ((Ebinop Oadd (Etempvar _i tint)
                           (Econst_int (Int.repr 1) tint) tint) ::
                         (Econst_int (Int.repr 1) tint) :: nil))
                      (Sset _r (Etempvar _t'1 tint)))
                    (Sifthenelse (Etempvar _r tint)
                      (Sset _total
                        (Ebinop Oadd (Etempvar _total tint)
                          (Econst_int (Int.repr 1) tint) tint))
                      Sskip)))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Sassign (Ederef (Etempvar _res (tptr tint)) tint)
                (Etempvar _total tint))
              (Ssequence
                (Scall None
                  (Evar _release2 (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                    cc_default))
                  ((Etempvar _l (tptr (Tstruct _lock_t noattr))) :: nil))
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_keys, (tarray tint 16384)) ::
              (_values, (tarray tint 16384)) :: nil);
  fn_temps := ((_total, tint) :: (_i, tint) ::
               (_l, (tptr (Tstruct _lock_t noattr))) :: (_i__1, tint) ::
               (_t, (tptr tint)) :: (_i__2, tint) ::
               (_l__1, (tptr (Tstruct _lock_t noattr))) ::
               (_r, (tptr tint)) :: (_i__3, tint) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _total (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Scall None (Evar _init_table (Tfunction Tnil tvoid cc_default)) nil)
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
                    ((Esizeof (Tstruct _lock_t noattr) tuint) :: nil))
                  (Sset _l
                    (Ecast (Etempvar _t'1 (tptr tvoid))
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
                    (Ssequence
                      (Scall (Some _t'2)
                        (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                               (tptr tvoid) cc_default))
                        ((Esizeof tint tuint) :: nil))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _results (tarray (tptr tint) 3))
                            (Etempvar _i tint) (tptr (tptr tint)))
                          (tptr tint))
                        (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tint))))
                    (Scall None
                      (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil)
                                        tvoid cc_default))
                      ((Ecast (Etempvar _l (tptr (Tstruct _lock_t noattr)))
                         (tptr tvoid)) :: nil))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Ssequence
            (Sset _i__1 (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i__1 tint)
                               (Econst_int (Int.repr 3) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                             (tptr tvoid) cc_default))
                      ((Esizeof tint tuint) :: nil))
                    (Sset _t
                      (Ecast (Etempvar _t'3 (tptr tvoid)) (tptr tint))))
                  (Ssequence
                    (Sassign (Ederef (Etempvar _t (tptr tint)) tint)
                      (Etempvar _i__1 tint))
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
                           (Evar _f (Tfunction (Tcons (tptr tvoid) Tnil)
                                      (tptr tvoid) cc_default))
                           (tptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                   (tptr tvoid) cc_default))) (tptr tvoid)) ::
                       (Ecast (Etempvar _t (tptr tint)) (tptr tvoid)) :: nil)))))
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
                        (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil)
                                         tvoid cc_default))
                        ((Etempvar _l__1 (tptr (Tstruct _lock_t noattr))) ::
                         nil))
                      (Ssequence
                        (Scall None
                          (Evar _freelock2 (Tfunction
                                             (Tcons (tptr tvoid) Tnil) tvoid
                                             cc_default))
                          ((Etempvar _l__1 (tptr (Tstruct _lock_t noattr))) ::
                           nil))
                        (Ssequence
                          (Scall None
                            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil)
                                          tvoid cc_default))
                            ((Etempvar _l__1 (tptr (Tstruct _lock_t noattr))) ::
                             nil))
                          (Ssequence
                            (Sset _r
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _results (tarray (tptr tint) 3))
                                  (Etempvar _i__2 tint) (tptr (tptr tint)))
                                (tptr tint)))
                            (Ssequence
                              (Sset _i__3
                                (Ederef (Etempvar _r (tptr tint)) tint))
                              (Ssequence
                                (Scall None
                                  (Evar _free (Tfunction
                                                (Tcons (tptr tvoid) Tnil)
                                                tvoid cc_default))
                                  ((Etempvar _r (tptr tint)) :: nil))
                                (Sset _total
                                  (Ebinop Oadd (Etempvar _total tint)
                                    (Etempvar _i__3 tint) tint))))))))))
                (Sset _i__2
                  (Ebinop Oadd (Etempvar _i__2 tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Scall None
              (Evar _freeze_table (Tfunction
                                    (Tcons (tptr tint)
                                      (Tcons (tptr tint) Tnil)) tvoid
                                    cc_default))
              ((Evar _keys (tarray tint 16384)) ::
               (Evar _values (tarray tint 16384)) :: nil)))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _lock_t Struct ((_a, (tarray (tptr tvoid) 2)) :: nil) noattr ::
 Composite _entry Struct
   ((_key, (tptr (Tstruct _atomic_loc noattr))) ::
    (_value, (tptr (Tstruct _atomic_loc noattr))) :: nil)
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
 (_makelock,
   Gfun(External (EF_external "makelock"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
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
 (_surely_malloc,
   Gfun(External (EF_external "surely_malloc"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_make_atomic,
   Gfun(External (EF_external "make_atomic"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint Tnil) (tptr (Tstruct _atomic_loc noattr)) cc_default)) ::
 (_free_atomic,
   Gfun(External (EF_external "free_atomic"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _atomic_loc noattr)) Tnil) tint cc_default)) ::
 (_load_SC,
   Gfun(External (EF_external "load_SC"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _atomic_loc noattr)) Tnil) tint cc_default)) ::
 (_store_SC,
   Gfun(External (EF_external "store_SC"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr (Tstruct _atomic_loc noattr)) (Tcons tint Tnil)) tvoid
     cc_default)) ::
 (_CAS_SC,
   Gfun(External (EF_external "CAS_SC"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _atomic_loc noattr))
       (Tcons tint (Tcons tint Tnil))) tint cc_default)) ::
 (_m_entries, Gvar v_m_entries) :: (_thread_locks, Gvar v_thread_locks) ::
 (_results, Gvar v_results) ::
 (_integer_hash, Gfun(Internal f_integer_hash)) ::
 (_set_item, Gfun(Internal f_set_item)) ::
 (_get_item, Gfun(Internal f_get_item)) ::
 (_add_item, Gfun(Internal f_add_item)) ::
 (_init_table, Gfun(Internal f_init_table)) ::
 (_freeze_table, Gfun(Internal f_freeze_table)) ::
 (_f, Gfun(Internal f_f)) :: (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: _f :: _freeze_table :: _init_table :: _add_item :: _get_item ::
 _set_item :: _integer_hash :: _results :: _thread_locks :: _m_entries ::
 _CAS_SC :: _store_SC :: _load_SC :: _free_atomic :: _make_atomic ::
 _surely_malloc :: _spawn :: _release2 :: _freelock2 :: _acquire ::
 _makelock :: _free :: ___builtin_debug :: ___builtin_nop ::
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

