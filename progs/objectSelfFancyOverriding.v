From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.10".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "32sse2".
  Definition abi := "standard".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "progs/objectSelfFancyOverriding.c".
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 30%positive.
Definition ___builtin_annot_intval : ident := 31%positive.
Definition ___builtin_bswap : ident := 15%positive.
Definition ___builtin_bswap16 : ident := 17%positive.
Definition ___builtin_bswap32 : ident := 16%positive.
Definition ___builtin_bswap64 : ident := 14%positive.
Definition ___builtin_clz : ident := 18%positive.
Definition ___builtin_clzl : ident := 19%positive.
Definition ___builtin_clzll : ident := 20%positive.
Definition ___builtin_ctz : ident := 21%positive.
Definition ___builtin_ctzl : ident := 22%positive.
Definition ___builtin_ctzll : ident := 23%positive.
Definition ___builtin_debug : ident := 49%positive.
Definition ___builtin_expect : ident := 38%positive.
Definition ___builtin_fabs : ident := 24%positive.
Definition ___builtin_fabsf : ident := 25%positive.
Definition ___builtin_fmadd : ident := 41%positive.
Definition ___builtin_fmax : ident := 39%positive.
Definition ___builtin_fmin : ident := 40%positive.
Definition ___builtin_fmsub : ident := 42%positive.
Definition ___builtin_fnmadd : ident := 43%positive.
Definition ___builtin_fnmsub : ident := 44%positive.
Definition ___builtin_fsqrt : ident := 26%positive.
Definition ___builtin_membar : ident := 32%positive.
Definition ___builtin_memcpy_aligned : ident := 28%positive.
Definition ___builtin_read16_reversed : ident := 45%positive.
Definition ___builtin_read32_reversed : ident := 46%positive.
Definition ___builtin_sel : ident := 29%positive.
Definition ___builtin_sqrt : ident := 27%positive.
Definition ___builtin_unreachable : ident := 37%positive.
Definition ___builtin_va_arg : ident := 34%positive.
Definition ___builtin_va_copy : ident := 35%positive.
Definition ___builtin_va_end : ident := 36%positive.
Definition ___builtin_va_start : ident := 33%positive.
Definition ___builtin_write16_reversed : ident := 47%positive.
Definition ___builtin_write32_reversed : ident := 48%positive.
Definition ___compcert_i64_dtos : ident := 86%positive.
Definition ___compcert_i64_dtou : ident := 87%positive.
Definition ___compcert_i64_sar : ident := 98%positive.
Definition ___compcert_i64_sdiv : ident := 92%positive.
Definition ___compcert_i64_shl : ident := 96%positive.
Definition ___compcert_i64_shr : ident := 97%positive.
Definition ___compcert_i64_smod : ident := 94%positive.
Definition ___compcert_i64_smulh : ident := 99%positive.
Definition ___compcert_i64_stod : ident := 88%positive.
Definition ___compcert_i64_stof : ident := 90%positive.
Definition ___compcert_i64_udiv : ident := 93%positive.
Definition ___compcert_i64_umod : ident := 95%positive.
Definition ___compcert_i64_umulh : ident := 100%positive.
Definition ___compcert_i64_utod : ident := 89%positive.
Definition ___compcert_i64_utof : ident := 91%positive.
Definition ___compcert_va_composite : ident := 85%positive.
Definition ___compcert_va_float64 : ident := 84%positive.
Definition ___compcert_va_int32 : ident := 82%positive.
Definition ___compcert_va_int64 : ident := 83%positive.
Definition _c : ident := 63%positive.
Definition _col : ident := 75%positive.
Definition _colU : ident := 80%positive.
Definition _color : ident := 12%positive.
Definition _d : ident := 55%positive.
Definition _data : ident := 7%positive.
Definition _exit : ident := 51%positive.
Definition _fancy_reset : ident := 62%positive.
Definition _fancyfoo_methods : ident := 64%positive.
Definition _fancyfoo_object : ident := 13%positive.
Definition _fancymethods : ident := 11%positive.
Definition _foo_methods : ident := 59%positive.
Definition _foo_object : ident := 8%positive.
Definition _foo_reset : ident := 53%positive.
Definition _foo_twiddle : ident := 56%positive.
Definition _foo_twiddleR : ident := 58%positive.
Definition _getcolor : ident := 10%positive.
Definition _i : ident := 54%positive.
Definition _main : ident := 81%positive.
Definition _make_fancyfoo : ident := 65%positive.
Definition _make_fancyfooTyped : ident := 66%positive.
Definition _make_foo : ident := 61%positive.
Definition _malloc : ident := 50%positive.
Definition _methods : ident := 5%positive.
Definition _mtable : ident := 6%positive.
Definition _object : ident := 2%positive.
Definition _p : ident := 60%positive.
Definition _p_reset : ident := 68%positive.
Definition _p_twiddle : ident := 69%positive.
Definition _pmtable : ident := 67%positive.
Definition _q : ident := 70%positive.
Definition _q_getcolor : ident := 74%positive.
Definition _q_reset : ident := 72%positive.
Definition _q_setcolor : ident := 73%positive.
Definition _qmtable : ident := 71%positive.
Definition _reset : ident := 1%positive.
Definition _s_reset : ident := 57%positive.
Definition _self : ident := 52%positive.
Definition _setcolor : ident := 9%positive.
Definition _twiddle : ident := 3%positive.
Definition _twiddleR : ident := 4%positive.
Definition _u : ident := 76%positive.
Definition _u_getcolor : ident := 79%positive.
Definition _u_reset : ident := 78%positive.
Definition _umtable : ident := 77%positive.
Definition _t'1 : ident := 101%positive.
Definition _t'10 : ident := 110%positive.
Definition _t'2 : ident := 102%positive.
Definition _t'3 : ident := 103%positive.
Definition _t'4 : ident := 104%positive.
Definition _t'5 : ident := 105%positive.
Definition _t'6 : ident := 106%positive.
Definition _t'7 : ident := 107%positive.
Definition _t'8 : ident := 108%positive.
Definition _t'9 : ident := 109%positive.

Definition f_foo_reset := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _object noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef
      (Ecast (Etempvar _self (tptr (Tstruct _object noattr)))
        (tptr (Tstruct _foo_object noattr))) (Tstruct _foo_object noattr))
    _data tint) (Econst_int (Int.repr 0) tint))
|}.

Definition f_foo_twiddle := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _object noattr))) :: (_i, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_d, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _d
    (Efield
      (Ederef
        (Ecast (Etempvar _self (tptr (Tstruct _object noattr)))
          (tptr (Tstruct _foo_object noattr))) (Tstruct _foo_object noattr))
      _data tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef
          (Ecast (Etempvar _self (tptr (Tstruct _object noattr)))
            (tptr (Tstruct _foo_object noattr)))
          (Tstruct _foo_object noattr)) _data tint)
      (Ebinop Oadd (Etempvar _d tint)
        (Ebinop Omul (Econst_int (Int.repr 2) tint) (Etempvar _i tint) tint)
        tint))
    (Sreturn (Some (Ebinop Oadd (Etempvar _d tint) (Etempvar _i tint) tint)))))
|}.

Definition f_foo_twiddleR := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _object noattr))) :: (_i, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_mtable, (tptr (Tstruct _methods noattr))) ::
               (_s_reset,
                (tptr (Tfunction (Tcons (tptr (Tstruct _object noattr)) Tnil)
                        tvoid cc_default))) :: (_d, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _d
    (Efield
      (Ederef
        (Ecast (Etempvar _self (tptr (Tstruct _object noattr)))
          (tptr (Tstruct _foo_object noattr))) (Tstruct _foo_object noattr))
      _data tint))
  (Ssequence
    (Sset _mtable
      (Efield
        (Ederef (Etempvar _self (tptr (Tstruct _object noattr)))
          (Tstruct _object noattr)) _mtable (tptr (Tstruct _methods noattr))))
    (Ssequence
      (Sset _s_reset
        (Efield
          (Ederef (Etempvar _mtable (tptr (Tstruct _methods noattr)))
            (Tstruct _methods noattr)) _reset
          (tptr (Tfunction (Tcons (tptr (Tstruct _object noattr)) Tnil) tvoid
                  cc_default))))
      (Ssequence
        (Scall None
          (Etempvar _s_reset (tptr (Tfunction
                                     (Tcons (tptr (Tstruct _object noattr))
                                       Tnil) tvoid cc_default)))
          ((Etempvar _self (tptr (Tstruct _object noattr))) :: nil))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Ecast (Etempvar _self (tptr (Tstruct _object noattr)))
                  (tptr (Tstruct _foo_object noattr)))
                (Tstruct _foo_object noattr)) _data tint)
            (Ebinop Oadd (Etempvar _d tint)
              (Ebinop Omul (Econst_int (Int.repr 2) tint) (Etempvar _i tint)
                tint) tint))
          (Sreturn (Some (Ebinop Oadd (Etempvar _d tint) (Etempvar _i tint)
                           tint))))))))
|}.

Definition v_foo_methods := {|
  gvar_info := (Tstruct _methods noattr);
  gvar_init := (Init_addrof _foo_reset (Ptrofs.repr 0) ::
                Init_addrof _foo_twiddle (Ptrofs.repr 0) ::
                Init_addrof _foo_twiddleR (Ptrofs.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_make_foo := {|
  fn_return := (tptr (Tstruct _object noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _foo_object noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _foo_object noattr) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _foo_object noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _p (tptr (Tstruct _foo_object noattr))) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _foo_object noattr)))
            (Tstruct _foo_object noattr)) _mtable
          (tptr (Tstruct _methods noattr)))
        (Eaddrof (Evar _foo_methods (Tstruct _methods noattr))
          (tptr (Tstruct _methods noattr))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _foo_object noattr)))
              (Tstruct _foo_object noattr)) _data tint)
          (Econst_int (Int.repr 0) tint))
        (Sreturn (Some (Ecast
                         (Etempvar _p (tptr (Tstruct _foo_object noattr)))
                         (tptr (Tstruct _object noattr)))))))))
|}.

Definition f_fancy_reset := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _object noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef
        (Ecast (Etempvar _self (tptr (Tstruct _object noattr)))
          (tptr (Tstruct _foo_object noattr))) (Tstruct _foo_object noattr))
      _data tint) (Econst_int (Int.repr 0) tint))
  (Sassign
    (Efield
      (Ederef
        (Ecast (Etempvar _self (tptr (Tstruct _object noattr)))
          (tptr (Tstruct _fancyfoo_object noattr)))
        (Tstruct _fancyfoo_object noattr)) _color tint)
    (Econst_int (Int.repr 0) tint)))
|}.

Definition f_setcolor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _object noattr))) :: (_c, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sassign
  (Efield
    (Ederef
      (Ecast (Etempvar _self (tptr (Tstruct _object noattr)))
        (tptr (Tstruct _fancyfoo_object noattr)))
      (Tstruct _fancyfoo_object noattr)) _color tint) (Etempvar _c tint))
|}.

Definition f_getcolor := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _object noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef
        (Ecast (Etempvar _self (tptr (Tstruct _object noattr)))
          (tptr (Tstruct _fancyfoo_object noattr)))
        (Tstruct _fancyfoo_object noattr)) _color tint))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition v_fancyfoo_methods := {|
  gvar_info := (Tstruct _fancymethods noattr);
  gvar_init := (Init_addrof _fancy_reset (Ptrofs.repr 0) ::
                Init_addrof _foo_twiddle (Ptrofs.repr 0) ::
                Init_addrof _foo_twiddleR (Ptrofs.repr 0) ::
                Init_addrof _setcolor (Ptrofs.repr 0) ::
                Init_addrof _getcolor (Ptrofs.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_make_fancyfoo := {|
  fn_return := (tptr (Tstruct _object noattr));
  fn_callconv := cc_default;
  fn_params := ((_c, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _fancyfoo_object noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _fancyfoo_object noattr) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _fancyfoo_object noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _p (tptr (Tstruct _fancyfoo_object noattr)))
                   tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _fancyfoo_object noattr)))
            (Tstruct _fancyfoo_object noattr)) _mtable
          (tptr (Tstruct _fancymethods noattr)))
        (Eaddrof (Evar _fancyfoo_methods (Tstruct _fancymethods noattr))
          (tptr (Tstruct _fancymethods noattr))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _fancyfoo_object noattr)))
              (Tstruct _fancyfoo_object noattr)) _data tint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _fancyfoo_object noattr)))
                (Tstruct _fancyfoo_object noattr)) _color tint)
            (Etempvar _c tint))
          (Sreturn (Some (Ecast
                           (Etempvar _p (tptr (Tstruct _fancyfoo_object noattr)))
                           (tptr (Tstruct _object noattr))))))))))
|}.

Definition f_make_fancyfooTyped := {|
  fn_return := (tptr (Tstruct _fancyfoo_object noattr));
  fn_callconv := cc_default;
  fn_params := ((_c, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _fancyfoo_object noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _fancyfoo_object noattr) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _fancyfoo_object noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _p (tptr (Tstruct _fancyfoo_object noattr)))
                   tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _fancyfoo_object noattr)))
            (Tstruct _fancyfoo_object noattr)) _mtable
          (tptr (Tstruct _fancymethods noattr)))
        (Eaddrof (Evar _fancyfoo_methods (Tstruct _fancymethods noattr))
          (tptr (Tstruct _fancymethods noattr))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _fancyfoo_object noattr)))
              (Tstruct _fancyfoo_object noattr)) _data tint)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _fancyfoo_object noattr)))
                (Tstruct _fancyfoo_object noattr)) _color tint)
            (Etempvar _c tint))
          (Sreturn (Some (Etempvar _p (tptr (Tstruct _fancyfoo_object noattr))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _object noattr))) ::
               (_pmtable, (tptr (Tstruct _methods noattr))) ::
               (_p_reset,
                (tptr (Tfunction (Tcons (tptr (Tstruct _object noattr)) Tnil)
                        tvoid cc_default))) ::
               (_p_twiddle,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _object noattr))
                          (Tcons tint Tnil)) tint cc_default))) ::
               (_i, tint) :: (_q, (tptr (Tstruct _object noattr))) ::
               (_qmtable, (tptr (Tstruct _fancymethods noattr))) ::
               (_q_reset,
                (tptr (Tfunction (Tcons (tptr (Tstruct _object noattr)) Tnil)
                        tvoid cc_default))) ::
               (_q_setcolor,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _object noattr))
                          (Tcons tint Tnil)) tvoid cc_default))) ::
               (_q_getcolor,
                (tptr (Tfunction (Tcons (tptr (Tstruct _object noattr)) Tnil)
                        tint cc_default))) :: (_col, tint) ::
               (_u, (tptr (Tstruct _fancyfoo_object noattr))) ::
               (_umtable, (tptr (Tstruct _fancymethods noattr))) ::
               (_u_reset,
                (tptr (Tfunction (Tcons (tptr (Tstruct _object noattr)) Tnil)
                        tvoid cc_default))) ::
               (_u_getcolor,
                (tptr (Tfunction (Tcons (tptr (Tstruct _object noattr)) Tnil)
                        tint cc_default))) :: (_colU, tint) ::
               (_t'6, tint) ::
               (_t'5, (tptr (Tstruct _fancyfoo_object noattr))) ::
               (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, (tptr (Tstruct _object noattr))) ::
               (_t'1, (tptr (Tstruct _object noattr))) ::
               (_t'10, (tptr (Tstruct _methods noattr))) ::
               (_t'9, (tptr (Tstruct _methods noattr))) ::
               (_t'8, (tptr (Tstruct _methods noattr))) ::
               (_t'7, (tptr (Tstruct _methods noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _make_foo (Tfunction Tnil (tptr (Tstruct _object noattr))
                          cc_default)) nil)
      (Sset _p (Etempvar _t'1 (tptr (Tstruct _object noattr)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _make_fancyfoo (Tfunction (Tcons tint Tnil)
                                 (tptr (Tstruct _object noattr)) cc_default))
          ((Econst_int (Int.repr 4) tint) :: nil))
        (Sset _q (Etempvar _t'2 (tptr (Tstruct _object noattr)))))
      (Ssequence
        (Sset _pmtable
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _object noattr)))
              (Tstruct _object noattr)) _mtable
            (tptr (Tstruct _methods noattr))))
        (Ssequence
          (Sset _p_reset
            (Efield
              (Ederef (Etempvar _pmtable (tptr (Tstruct _methods noattr)))
                (Tstruct _methods noattr)) _reset
              (tptr (Tfunction (Tcons (tptr (Tstruct _object noattr)) Tnil)
                      tvoid cc_default))))
          (Ssequence
            (Scall None
              (Etempvar _p_reset (tptr (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _object noattr))
                                           Tnil) tvoid cc_default)))
              ((Etempvar _p (tptr (Tstruct _object noattr))) :: nil))
            (Ssequence
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef (Etempvar _q (tptr (Tstruct _object noattr)))
                      (Tstruct _object noattr)) _mtable
                    (tptr (Tstruct _methods noattr))))
                (Sset _qmtable
                  (Ecast (Etempvar _t'10 (tptr (Tstruct _methods noattr)))
                    (tptr (Tstruct _fancymethods noattr)))))
              (Ssequence
                (Sset _q_reset
                  (Efield
                    (Ederef
                      (Etempvar _qmtable (tptr (Tstruct _fancymethods noattr)))
                      (Tstruct _fancymethods noattr)) _reset
                    (tptr (Tfunction
                            (Tcons (tptr (Tstruct _object noattr)) Tnil)
                            tvoid cc_default))))
                (Ssequence
                  (Scall None
                    (Etempvar _q_reset (tptr (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _object noattr))
                                                 Tnil) tvoid cc_default)))
                    ((Etempvar _q (tptr (Tstruct _object noattr))) :: nil))
                  (Ssequence
                    (Ssequence
                      (Sset _t'9
                        (Efield
                          (Ederef
                            (Etempvar _q (tptr (Tstruct _object noattr)))
                            (Tstruct _object noattr)) _mtable
                          (tptr (Tstruct _methods noattr))))
                      (Sset _qmtable
                        (Ecast
                          (Etempvar _t'9 (tptr (Tstruct _methods noattr)))
                          (tptr (Tstruct _fancymethods noattr)))))
                    (Ssequence
                      (Sset _q_getcolor
                        (Efield
                          (Ederef
                            (Etempvar _qmtable (tptr (Tstruct _fancymethods noattr)))
                            (Tstruct _fancymethods noattr)) _getcolor
                          (tptr (Tfunction
                                  (Tcons (tptr (Tstruct _object noattr))
                                    Tnil) tint cc_default))))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'3)
                            (Etempvar _q_getcolor (tptr (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _object noattr))
                                                            Tnil) tint
                                                          cc_default)))
                            ((Etempvar _q (tptr (Tstruct _object noattr))) ::
                             nil))
                          (Sset _col (Etempvar _t'3 tint)))
                        (Ssequence
                          (Sset _pmtable
                            (Efield
                              (Ederef
                                (Etempvar _p (tptr (Tstruct _object noattr)))
                                (Tstruct _object noattr)) _mtable
                              (tptr (Tstruct _methods noattr))))
                          (Ssequence
                            (Sset _p_twiddle
                              (Efield
                                (Ederef
                                  (Etempvar _pmtable (tptr (Tstruct _methods noattr)))
                                  (Tstruct _methods noattr)) _twiddleR
                                (tptr (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _object noattr))
                                          (Tcons tint Tnil)) tint cc_default))))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'4)
                                  (Etempvar _p_twiddle (tptr (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct _object noattr))
                                                                 (Tcons tint
                                                                   Tnil))
                                                               tint
                                                               cc_default)))
                                  ((Etempvar _p (tptr (Tstruct _object noattr))) ::
                                   (Econst_int (Int.repr 3) tint) :: nil))
                                (Sset _i (Etempvar _t'4 tint)))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'5)
                                    (Evar _make_fancyfooTyped (Tfunction
                                                                (Tcons tint
                                                                  Tnil)
                                                                (tptr (Tstruct _fancyfoo_object noattr))
                                                                cc_default))
                                    ((Econst_int (Int.repr 9) tint) :: nil))
                                  (Sset _u
                                    (Etempvar _t'5 (tptr (Tstruct _fancyfoo_object noattr)))))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'8
                                      (Efield
                                        (Ederef
                                          (Ecast
                                            (Etempvar _u (tptr (Tstruct _fancyfoo_object noattr)))
                                            (tptr (Tstruct _object noattr)))
                                          (Tstruct _object noattr)) _mtable
                                        (tptr (Tstruct _methods noattr))))
                                    (Sset _umtable
                                      (Ecast
                                        (Etempvar _t'8 (tptr (Tstruct _methods noattr)))
                                        (tptr (Tstruct _fancymethods noattr)))))
                                  (Ssequence
                                    (Sset _u_reset
                                      (Efield
                                        (Ederef
                                          (Etempvar _umtable (tptr (Tstruct _fancymethods noattr)))
                                          (Tstruct _fancymethods noattr))
                                        _reset
                                        (tptr (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _object noattr))
                                                  Tnil) tvoid cc_default))))
                                    (Ssequence
                                      (Scall None
                                        (Etempvar _u_reset (tptr (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _object noattr))
                                                                    Tnil)
                                                                   tvoid
                                                                   cc_default)))
                                        ((Ecast
                                           (Etempvar _u (tptr (Tstruct _fancyfoo_object noattr)))
                                           (tptr (Tstruct _object noattr))) ::
                                         nil))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'7
                                            (Efield
                                              (Ederef
                                                (Ecast
                                                  (Etempvar _u (tptr (Tstruct _fancyfoo_object noattr)))
                                                  (tptr (Tstruct _object noattr)))
                                                (Tstruct _object noattr))
                                              _mtable
                                              (tptr (Tstruct _methods noattr))))
                                          (Sset _umtable
                                            (Ecast
                                              (Etempvar _t'7 (tptr (Tstruct _methods noattr)))
                                              (tptr (Tstruct _fancymethods noattr)))))
                                        (Ssequence
                                          (Sset _u_getcolor
                                            (Efield
                                              (Ederef
                                                (Etempvar _umtable (tptr (Tstruct _fancymethods noattr)))
                                                (Tstruct _fancymethods noattr))
                                              _getcolor
                                              (tptr (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _object noattr))
                                                        Tnil) tint
                                                      cc_default))))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'6)
                                                (Etempvar _u_getcolor (tptr 
                                                (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _object noattr))
                                                    Tnil) tint cc_default)))
                                                ((Ecast
                                                   (Etempvar _u (tptr (Tstruct _fancyfoo_object noattr)))
                                                   (tptr (Tstruct _object noattr))) ::
                                                 nil))
                                              (Sset _colU
                                                (Etempvar _t'6 tint)))
                                            (Sreturn (Some (Ebinop Oadd
                                                             (Ebinop Oadd
                                                               (Etempvar _i tint)
                                                               (Etempvar _col tint)
                                                               tint)
                                                             (Etempvar _colU tint)
                                                             tint))))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _methods Struct
   (Member_plain _reset
      (tptr (Tfunction (Tcons (tptr (Tstruct _object noattr)) Tnil) tvoid
              cc_default)) ::
    Member_plain _twiddle
      (tptr (Tfunction
              (Tcons (tptr (Tstruct _object noattr)) (Tcons tint Tnil)) tint
              cc_default)) ::
    Member_plain _twiddleR
      (tptr (Tfunction
              (Tcons (tptr (Tstruct _object noattr)) (Tcons tint Tnil)) tint
              cc_default)) :: nil)
   noattr ::
 Composite _object Struct
   (Member_plain _mtable (tptr (Tstruct _methods noattr)) :: nil)
   noattr ::
 Composite _foo_object Struct
   (Member_plain _mtable (tptr (Tstruct _methods noattr)) ::
    Member_plain _data tint :: nil)
   noattr ::
 Composite _fancymethods Struct
   (Member_plain _reset
      (tptr (Tfunction (Tcons (tptr (Tstruct _object noattr)) Tnil) tvoid
              cc_default)) ::
    Member_plain _twiddle
      (tptr (Tfunction
              (Tcons (tptr (Tstruct _object noattr)) (Tcons tint Tnil)) tint
              cc_default)) ::
    Member_plain _twiddleR
      (tptr (Tfunction
              (Tcons (tptr (Tstruct _object noattr)) (Tcons tint Tnil)) tint
              cc_default)) ::
    Member_plain _setcolor
      (tptr (Tfunction
              (Tcons (tptr (Tstruct _object noattr)) (Tcons tint Tnil)) tvoid
              cc_default)) ::
    Member_plain _getcolor
      (tptr (Tfunction (Tcons (tptr (Tstruct _object noattr)) Tnil) tint
              cc_default)) :: nil)
   noattr ::
 Composite _fancyfoo_object Struct
   (Member_plain _mtable (tptr (Tstruct _fancymethods noattr)) ::
    Member_plain _data tint :: Member_plain _color tint :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons tint (Tcons tint Tnil)) tint
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_foo_reset, Gfun(Internal f_foo_reset)) ::
 (_foo_twiddle, Gfun(Internal f_foo_twiddle)) ::
 (_foo_twiddleR, Gfun(Internal f_foo_twiddleR)) ::
 (_foo_methods, Gvar v_foo_methods) ::
 (_make_foo, Gfun(Internal f_make_foo)) ::
 (_fancy_reset, Gfun(Internal f_fancy_reset)) ::
 (_setcolor, Gfun(Internal f_setcolor)) ::
 (_getcolor, Gfun(Internal f_getcolor)) ::
 (_fancyfoo_methods, Gvar v_fancyfoo_methods) ::
 (_make_fancyfoo, Gfun(Internal f_make_fancyfoo)) ::
 (_make_fancyfooTyped, Gfun(Internal f_make_fancyfooTyped)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _make_fancyfooTyped :: _make_fancyfoo :: _fancyfoo_methods ::
 _getcolor :: _setcolor :: _fancy_reset :: _make_foo :: _foo_methods ::
 _foo_twiddleR :: _foo_twiddle :: _foo_reset :: _exit :: _malloc ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


