From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition _CAS_RA : ident := 67%positive.
Definition ___builtin_annot : ident := 12%positive.
Definition ___builtin_annot_intval : ident := 13%positive.
Definition ___builtin_bswap : ident := 6%positive.
Definition ___builtin_bswap16 : ident := 8%positive.
Definition ___builtin_bswap32 : ident := 7%positive.
Definition ___builtin_bswap64 : ident := 38%positive.
Definition ___builtin_clz : ident := 39%positive.
Definition ___builtin_clzl : ident := 40%positive.
Definition ___builtin_clzll : ident := 41%positive.
Definition ___builtin_ctz : ident := 42%positive.
Definition ___builtin_ctzl : ident := 43%positive.
Definition ___builtin_ctzll : ident := 44%positive.
Definition ___builtin_debug : ident := 56%positive.
Definition ___builtin_fabs : ident := 9%positive.
Definition ___builtin_fmadd : ident := 47%positive.
Definition ___builtin_fmax : ident := 45%positive.
Definition ___builtin_fmin : ident := 46%positive.
Definition ___builtin_fmsub : ident := 48%positive.
Definition ___builtin_fnmadd : ident := 49%positive.
Definition ___builtin_fnmsub : ident := 50%positive.
Definition ___builtin_fsqrt : ident := 10%positive.
Definition ___builtin_membar : ident := 14%positive.
Definition ___builtin_memcpy_aligned : ident := 11%positive.
Definition ___builtin_nop : ident := 55%positive.
Definition ___builtin_read16_reversed : ident := 51%positive.
Definition ___builtin_read32_reversed : ident := 52%positive.
Definition ___builtin_va_arg : ident := 16%positive.
Definition ___builtin_va_copy : ident := 17%positive.
Definition ___builtin_va_end : ident := 18%positive.
Definition ___builtin_va_start : ident := 15%positive.
Definition ___builtin_write16_reversed : ident := 53%positive.
Definition ___builtin_write32_reversed : ident := 54%positive.
Definition ___compcert_i64_dtos : ident := 23%positive.
Definition ___compcert_i64_dtou : ident := 24%positive.
Definition ___compcert_i64_sar : ident := 35%positive.
Definition ___compcert_i64_sdiv : ident := 29%positive.
Definition ___compcert_i64_shl : ident := 33%positive.
Definition ___compcert_i64_shr : ident := 34%positive.
Definition ___compcert_i64_smod : ident := 31%positive.
Definition ___compcert_i64_smulh : ident := 36%positive.
Definition ___compcert_i64_stod : ident := 25%positive.
Definition ___compcert_i64_stof : ident := 27%positive.
Definition ___compcert_i64_udiv : ident := 30%positive.
Definition ___compcert_i64_umod : ident := 32%positive.
Definition ___compcert_i64_umulh : ident := 37%positive.
Definition ___compcert_i64_utod : ident := 26%positive.
Definition ___compcert_i64_utof : ident := 28%positive.
Definition ___compcert_va_composite : ident := 22%positive.
Definition ___compcert_va_float64 : ident := 21%positive.
Definition ___compcert_va_int32 : ident := 19%positive.
Definition ___compcert_va_int64 : ident := 20%positive.
Definition _a : ident := 1%positive.
Definition _acquire : ident := 61%positive.
Definition _add_item : ident := 81%positive.
Definition _arg : ident := 83%positive.
Definition _entry : ident := 5%positive.
Definition _exit : ident := 57%positive.
Definition _f : ident := 89%positive.
Definition _free : ident := 58%positive.
Definition _freelock2 : ident := 62%positive.
Definition _get_item : ident := 80%positive.
Definition _i : ident := 74%positive.
Definition _i__1 : ident := 90%positive.
Definition _i__2 : ident := 91%positive.
Definition _i__3 : ident := 93%positive.
Definition _idx : ident := 76%positive.
Definition _init_table : ident := 82%positive.
Definition _integer_hash : ident := 75%positive.
Definition _key : ident := 3%positive.
Definition _keys : ident := 94%positive.
Definition _l : ident := 85%positive.
Definition _l__1 : ident := 92%positive.
Definition _load_acq : ident := 65%positive.
Definition _lock_t : ident := 2%positive.
Definition _m_entries : ident := 68%positive.
Definition _main : ident := 96%positive.
Definition _makelock : ident := 60%positive.
Definition _malloc : ident := 59%positive.
Definition _n : ident := 71%positive.
Definition _p : ident := 72%positive.
Definition _probed_key : ident := 77%positive.
Definition _r : ident := 88%positive.
Definition _release2 : ident := 63%positive.
Definition _res : ident := 86%positive.
Definition _result : ident := 78%positive.
Definition _results : ident := 70%positive.
Definition _set_item : ident := 79%positive.
Definition _spawn : ident := 64%positive.
Definition _store_rel : ident := 66%positive.
Definition _surely_malloc : ident := 73%positive.
Definition _t : ident := 84%positive.
Definition _thread_locks : ident := 69%positive.
Definition _total : ident := 87%positive.
Definition _value : ident := 4%positive.
Definition _values : ident := 95%positive.
Definition _t'1 : ident := 97%positive.
Definition _t'2 : ident := 98%positive.
Definition _t'3 : ident := 99%positive.
Definition _t'4 : ident := 100%positive.
Definition _t'5 : ident := 101%positive.

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
  fn_temps := ((_idx, tint) :: (_i, (tptr tint)) :: (_probed_key, tint) ::
               (_result, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
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
                (Tstruct _entry noattr)) _key (tptr tint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _load_acq (Tfunction (Tcons (tptr tint) Tnil) tint
                                  cc_default))
                ((Etempvar _i (tptr tint)) :: nil))
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
                        (Evar _CAS_RA (Tfunction
                                        (Tcons (tptr tint)
                                          (Tcons tint (Tcons tint Tnil)))
                                        tint cc_default))
                        ((Etempvar _i (tptr tint)) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Etempvar _key tint) :: nil))
                      (Sset _result (Etempvar _t'3 tint)))
                    (Sifthenelse (Eunop Onotbool (Etempvar _result tint)
                                   tint)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'4)
                            (Evar _load_acq (Tfunction
                                              (Tcons (tptr tint) Tnil) tint
                                              cc_default))
                            ((Etempvar _i (tptr tint)) :: nil))
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
                      (Tstruct _entry noattr)) _value (tptr tint)))
                (Ssequence
                  (Scall None
                    (Evar _store_rel (Tfunction
                                       (Tcons (tptr tint) (Tcons tint Tnil))
                                       tvoid cc_default))
                    ((Etempvar _i (tptr tint)) :: (Etempvar _value tint) ::
                     nil))
                  (Sreturn None))))))))
    (Sset _idx
      (Ebinop Oadd (Etempvar _idx tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_get_item := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_key, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_idx, tint) :: (_i, (tptr tint)) :: (_probed_key, tint) ::
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
                (Tstruct _entry noattr)) _key (tptr tint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _load_acq (Tfunction (Tcons (tptr tint) Tnil) tint
                                  cc_default))
                ((Etempvar _i (tptr tint)) :: nil))
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
                        (Tstruct _entry noattr)) _value (tptr tint)))
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _load_acq (Tfunction (Tcons (tptr tint) Tnil)
                                        tint cc_default))
                      ((Etempvar _i (tptr tint)) :: nil))
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
  fn_temps := ((_idx, tint) :: (_i, (tptr tint)) :: (_probed_key, tint) ::
               (_result, tint) :: (_t'5, tint) :: (_t'4, tint) ::
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
                (Tstruct _entry noattr)) _key (tptr tint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _load_acq (Tfunction (Tcons (tptr tint) Tnil) tint
                                  cc_default))
                ((Etempvar _i (tptr tint)) :: nil))
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
                        (Evar _CAS_RA (Tfunction
                                        (Tcons (tptr tint)
                                          (Tcons tint (Tcons tint Tnil)))
                                        tint cc_default))
                        ((Etempvar _i (tptr tint)) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Etempvar _key tint) :: nil))
                      (Sset _result (Etempvar _t'3 tint)))
                    (Sifthenelse (Eunop Onotbool (Etempvar _result tint)
                                   tint)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'4)
                            (Evar _load_acq (Tfunction
                                              (Tcons (tptr tint) Tnil) tint
                                              cc_default))
                            ((Etempvar _i (tptr tint)) :: nil))
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
                      (Tstruct _entry noattr)) _value (tptr tint)))
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _CAS_RA (Tfunction
                                    (Tcons (tptr tint)
                                      (Tcons tint (Tcons tint Tnil))) tint
                                    cc_default))
                    ((Etempvar _i (tptr tint)) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Etempvar _value tint) :: nil))
                  (Sreturn (Some (Etempvar _t'5 tint))))))))))
    (Sset _idx
      (Ebinop Oadd (Etempvar _idx tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_init_table := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_p, (tptr tint)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
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
            (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                   cc_default))
            ((Esizeof tint tuint) :: nil))
          (Sset _p (Etempvar _t'1 (tptr tvoid))))
        (Ssequence
          (Sassign (Ederef (Etempvar _p (tptr tint)) tint)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                    (Etempvar _i tint) (tptr (Tstruct _entry noattr)))
                  (Tstruct _entry noattr)) _key (tptr tint))
              (Etempvar _p (tptr tint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _surely_malloc (Tfunction (Tcons tuint Tnil)
                                         (tptr tvoid) cc_default))
                  ((Esizeof tint tuint) :: nil))
                (Sset _p (Etempvar _t'2 (tptr tvoid))))
              (Ssequence
                (Sassign (Ederef (Etempvar _p (tptr tint)) tint)
                  (Econst_int (Int.repr 0) tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                        (Etempvar _i tint) (tptr (Tstruct _entry noattr)))
                      (Tstruct _entry noattr)) _value (tptr tint))
                  (Etempvar _p (tptr tint)))))))))
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
                        (Evar _freelock2 (Tfunction (Tcons (tptr tvoid) Tnil)
                                           tvoid cc_default))
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
                                              (Tcons (tptr tvoid) Tnil) tvoid
                                              cc_default))
                                ((Etempvar _r (tptr tint)) :: nil))
                              (Sset _total
                                (Ebinop Oadd (Etempvar _total tint)
                                  (Etempvar _i__3 tint) tint))))))))))
              (Sset _i__2
                (Ebinop Oadd (Etempvar _i__2 tint)
                  (Econst_int (Int.repr 1) tint) tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _lock_t Struct ((_a, (tarray (tptr tvoid) 2)) :: nil) noattr ::
 Composite _entry Struct
   ((_key, (tptr tint)) :: (_value, (tptr tint)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap,
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
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
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
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
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
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
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
 (_load_acq,
   Gfun(External (EF_external "load_acq"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tint) Tnil) tint cc_default)) ::
 (_store_rel,
   Gfun(External (EF_external "store_rel"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tint) (Tcons tint Tnil)) tvoid
     cc_default)) ::
 (_CAS_RA,
   Gfun(External (EF_external "CAS_RA"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tint) (Tcons tint (Tcons tint Tnil))) tint cc_default)) ::
 (_m_entries, Gvar v_m_entries) :: (_thread_locks, Gvar v_thread_locks) ::
 (_results, Gvar v_results) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_integer_hash, Gfun(Internal f_integer_hash)) ::
 (_set_item, Gfun(Internal f_set_item)) ::
 (_get_item, Gfun(Internal f_get_item)) ::
 (_add_item, Gfun(Internal f_add_item)) ::
 (_init_table, Gfun(Internal f_init_table)) :: (_f, Gfun(Internal f_f)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _f :: _init_table :: _add_item :: _get_item :: _set_item ::
 _integer_hash :: _surely_malloc :: _results :: _thread_locks ::
 _m_entries :: _CAS_RA :: _store_rel :: _load_acq :: _spawn :: _release2 ::
 _freelock2 :: _acquire :: _makelock :: _malloc :: _free :: _exit ::
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


