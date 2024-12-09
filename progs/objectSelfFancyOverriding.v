From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
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

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _c : ident := $"c".
Definition _col : ident := $"col".
Definition _colU : ident := $"colU".
Definition _color : ident := $"color".
Definition _d : ident := $"d".
Definition _data : ident := $"data".
Definition _exit : ident := $"exit".
Definition _fancy_reset : ident := $"fancy_reset".
Definition _fancyfoo_methods : ident := $"fancyfoo_methods".
Definition _fancyfoo_object : ident := $"fancyfoo_object".
Definition _fancymethods : ident := $"fancymethods".
Definition _foo_methods : ident := $"foo_methods".
Definition _foo_object : ident := $"foo_object".
Definition _foo_reset : ident := $"foo_reset".
Definition _foo_twiddle : ident := $"foo_twiddle".
Definition _foo_twiddleR : ident := $"foo_twiddleR".
Definition _getcolor : ident := $"getcolor".
Definition _i : ident := $"i".
Definition _main : ident := $"main".
Definition _make_fancyfoo : ident := $"make_fancyfoo".
Definition _make_fancyfooTyped : ident := $"make_fancyfooTyped".
Definition _make_foo : ident := $"make_foo".
Definition _malloc : ident := $"malloc".
Definition _methods : ident := $"methods".
Definition _mtable : ident := $"mtable".
Definition _object : ident := $"object".
Definition _p : ident := $"p".
Definition _p_reset : ident := $"p_reset".
Definition _p_twiddle : ident := $"p_twiddle".
Definition _pmtable : ident := $"pmtable".
Definition _q : ident := $"q".
Definition _q_getcolor : ident := $"q_getcolor".
Definition _q_reset : ident := $"q_reset".
Definition _q_setcolor : ident := $"q_setcolor".
Definition _qmtable : ident := $"qmtable".
Definition _reset : ident := $"reset".
Definition _s_reset : ident := $"s_reset".
Definition _self : ident := $"self".
Definition _setcolor : ident := $"setcolor".
Definition _twiddle : ident := $"twiddle".
Definition _twiddleR : ident := $"twiddleR".
Definition _u : ident := $"u".
Definition _u_getcolor : ident := $"u_getcolor".
Definition _u_reset : ident := $"u_reset".
Definition _umtable : ident := $"umtable".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

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
                (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: nil)
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
          (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: nil) tvoid
                  cc_default))))
      (Ssequence
        (Scall None
          (Etempvar _s_reset (tptr (Tfunction
                                     ((tptr (Tstruct _object noattr)) :: nil)
                                     tvoid cc_default)))
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
      (Evar _malloc (Tfunction (tuint :: nil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _foo_object noattr) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _foo_object noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _p (tptr (Tstruct _foo_object noattr))) tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
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
      (Evar _malloc (Tfunction (tuint :: nil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _fancyfoo_object noattr) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _fancyfoo_object noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _p (tptr (Tstruct _fancyfoo_object noattr)))
                   tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
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
      (Evar _malloc (Tfunction (tuint :: nil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _fancyfoo_object noattr) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (Tstruct _fancyfoo_object noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _p (tptr (Tstruct _fancyfoo_object noattr)))
                   tint)
      (Scall None (Evar _exit (Tfunction (tint :: nil) tvoid cc_default))
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
                (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: nil)
                        tvoid cc_default))) ::
               (_p_twiddle,
                (tptr (Tfunction
                        ((tptr (Tstruct _object noattr)) :: tint :: nil) tint
                        cc_default))) :: (_i, tint) ::
               (_q, (tptr (Tstruct _object noattr))) ::
               (_qmtable, (tptr (Tstruct _fancymethods noattr))) ::
               (_q_reset,
                (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: nil)
                        tvoid cc_default))) ::
               (_q_setcolor,
                (tptr (Tfunction
                        ((tptr (Tstruct _object noattr)) :: tint :: nil)
                        tvoid cc_default))) ::
               (_q_getcolor,
                (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: nil)
                        tint cc_default))) :: (_col, tint) ::
               (_u, (tptr (Tstruct _fancyfoo_object noattr))) ::
               (_umtable, (tptr (Tstruct _fancymethods noattr))) ::
               (_u_reset,
                (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: nil)
                        tvoid cc_default))) ::
               (_u_getcolor,
                (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: nil)
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
        (Evar _make_foo (Tfunction nil (tptr (Tstruct _object noattr))
                          cc_default)) nil)
      (Sset _p (Etempvar _t'1 (tptr (Tstruct _object noattr)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _make_fancyfoo (Tfunction (tint :: nil)
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
              (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: nil) tvoid
                      cc_default))))
          (Ssequence
            (Scall None
              (Etempvar _p_reset (tptr (Tfunction
                                         ((tptr (Tstruct _object noattr)) ::
                                          nil) tvoid cc_default)))
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
                    (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: nil)
                            tvoid cc_default))))
                (Ssequence
                  (Scall None
                    (Etempvar _q_reset (tptr (Tfunction
                                               ((tptr (Tstruct _object noattr)) ::
                                                nil) tvoid cc_default)))
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
                                  ((tptr (Tstruct _object noattr)) :: nil)
                                  tint cc_default))))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'3)
                            (Etempvar _q_getcolor (tptr (Tfunction
                                                          ((tptr (Tstruct _object noattr)) ::
                                                           nil) tint
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
                                        ((tptr (Tstruct _object noattr)) ::
                                         tint :: nil) tint cc_default))))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'4)
                                  (Etempvar _p_twiddle (tptr (Tfunction
                                                               ((tptr (Tstruct _object noattr)) ::
                                                                tint :: nil)
                                                               tint
                                                               cc_default)))
                                  ((Etempvar _p (tptr (Tstruct _object noattr))) ::
                                   (Econst_int (Int.repr 3) tint) :: nil))
                                (Sset _i (Etempvar _t'4 tint)))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'5)
                                    (Evar _make_fancyfooTyped (Tfunction
                                                                (tint :: nil)
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
                                                ((tptr (Tstruct _object noattr)) ::
                                                 nil) tvoid cc_default))))
                                    (Ssequence
                                      (Scall None
                                        (Etempvar _u_reset (tptr (Tfunction
                                                                   ((tptr (Tstruct _object noattr)) ::
                                                                    nil)
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
                                                      ((tptr (Tstruct _object noattr)) ::
                                                       nil) tint cc_default))))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'6)
                                                (Etempvar _u_getcolor (tptr 
                                                (Tfunction
                                                  ((tptr (Tstruct _object noattr)) ::
                                                   nil) tint cc_default)))
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
      (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: nil) tvoid
              cc_default)) ::
    Member_plain _twiddle
      (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: tint :: nil) tint
              cc_default)) ::
    Member_plain _twiddleR
      (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: tint :: nil) tint
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
      (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: nil) tvoid
              cc_default)) ::
    Member_plain _twiddle
      (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: tint :: nil) tint
              cc_default)) ::
    Member_plain _twiddleR
      (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: tint :: nil) tint
              cc_default)) ::
    Member_plain _setcolor
      (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: tint :: nil) tvoid
              cc_default)) ::
    Member_plain _getcolor
      (tptr (Tfunction ((tptr (Tstruct _object noattr)) :: nil) tint
              cc_default)) :: nil)
   noattr ::
 Composite _fancyfoo_object Struct
   (Member_plain _mtable (tptr (Tstruct _fancymethods noattr)) ::
    Member_plain _data tint :: Member_plain _color tint :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tuint :: nil) (tptr tvoid)
     cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xint :: AST.Xint :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tuint :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xint :: AST.Xint :: nil) AST.Xint
                     cc_default)) (tint :: tint :: nil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc, Gfun(External EF_malloc (tuint :: nil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
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
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


