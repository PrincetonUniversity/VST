From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.13".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "mailbox/mailbox.c".
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
Definition _a : ident := $"a".
Definition _arg : ident := $"arg".
Definition _atom_exchange : ident := $"atom_exchange".
Definition _atom_int : ident := $"atom_int".
Definition _avail : ident := $"avail".
Definition _available : ident := $"available".
Definition _b : ident := $"b".
Definition _buf : ident := $"buf".
Definition _buffer : ident := $"buffer".
Definition _bufs : ident := $"bufs".
Definition _c : ident := $"c".
Definition _comm : ident := $"comm".
Definition _d : ident := $"d".
Definition _data : ident := $"data".
Definition _exit : ident := $"exit".
Definition _finish_read : ident := $"finish_read".
Definition _finish_write : ident := $"finish_write".
Definition _i : ident := $"i".
Definition _i__1 : ident := $"i__1".
Definition _initialize_channels : ident := $"initialize_channels".
Definition _initialize_reader : ident := $"initialize_reader".
Definition _initialize_writer : ident := $"initialize_writer".
Definition _last : ident := $"last".
Definition _last_given : ident := $"last_given".
Definition _last_read : ident := $"last_read".
Definition _last_taken : ident := $"last_taken".
Definition _lr : ident := $"lr".
Definition _main : ident := $"main".
Definition _make_atomic : ident := $"make_atomic".
Definition _malloc : ident := $"malloc".
Definition _memset : ident := $"memset".
Definition _n : ident := $"n".
Definition _p : ident := $"p".
Definition _r : ident := $"r".
Definition _reader : ident := $"reader".
Definition _reading : ident := $"reading".
Definition _rr : ident := $"rr".
Definition _s : ident := $"s".
Definition _spawn : ident := $"spawn".
Definition _start_read : ident := $"start_read".
Definition _start_write : ident := $"start_write".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _v : ident := $"v".
Definition _w : ident := $"w".
Definition _writer : ident := $"writer".
Definition _writing : ident := $"writing".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.

Definition f_surely_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Etempvar _n tulong) :: nil))
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
  fn_params := ((_s, (tptr tvoid)) :: (_c, tint) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tint)) :: (_i, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _p (Ecast (Etempvar _s (tptr tvoid)) (tptr tint)))
  (Ssequence
    (Ssequence
      (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                         (Ebinop Odiv (Etempvar _n tulong)
                           (Econst_int (Int.repr 4) tint) tulong) tint)
            Sskip
            Sbreak)
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _p (tptr tint)) (Etempvar _i tulong)
                (tptr tint)) tint) (Etempvar _c tint)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
            tulong))))
    (Sreturn (Some (Etempvar _s (tptr tvoid))))))
|}.

Definition v_bufs := {|
  gvar_info := (tarray (tptr (Tstruct _buffer noattr)) 5);
  gvar_init := (Init_space 40 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_comm := {|
  gvar_info := (tarray (tptr (Tstruct _atom_int noattr)) 3);
  gvar_init := (Init_space 24 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_reading := {|
  gvar_info := (tarray (tptr tint) 3);
  gvar_init := (Init_space 24 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_last_read := {|
  gvar_info := (tarray (tptr tint) 3);
  gvar_init := (Init_space 24 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_initialize_channels := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_b, (tptr (Tstruct _buffer noattr))) ::
               (_r, tint) :: (_a, (tptr (Tstruct _atom_int noattr))) ::
               (_c, (tptr tint)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _atom_int noattr))) ::
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
              (Evar _surely_malloc (Tfunction (Tcons tulong Tnil)
                                     (tptr tvoid) cc_default))
              ((Esizeof (Tstruct _buffer noattr) tulong) :: nil))
            (Sset _b (Etempvar _t'1 (tptr tvoid))))
          (Ssequence
            (Scall None
              (Evar _memset (Tfunction
                              (Tcons (tptr tvoid)
                                (Tcons tint (Tcons tulong Tnil)))
                              (tptr tvoid) cc_default))
              ((Etempvar _b (tptr (Tstruct _buffer noattr))) ::
               (Econst_int (Int.repr 0) tint) ::
               (Esizeof (Tstruct _buffer noattr) tulong) :: nil))
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
              (Evar _make_atomic (Tfunction (Tcons tint Tnil)
                                   (tptr (Tstruct _atom_int noattr))
                                   cc_default))
              ((Econst_int (Int.repr 0) tint) :: nil))
            (Sset _a (Etempvar _t'2 (tptr (Tstruct _atom_int noattr)))))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Evar _comm (tarray (tptr (Tstruct _atom_int noattr)) 3))
                  (Etempvar _r tint)
                  (tptr (tptr (Tstruct _atom_int noattr))))
                (tptr (Tstruct _atom_int noattr)))
              (Etempvar _a (tptr (Tstruct _atom_int noattr))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _surely_malloc (Tfunction (Tcons tulong Tnil)
                                         (tptr tvoid) cc_default))
                  ((Esizeof tint tulong) :: nil))
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
                      (Evar _surely_malloc (Tfunction (Tcons tulong Tnil)
                                             (tptr tvoid) cc_default))
                      ((Esizeof tint tulong) :: nil))
                    (Sset _c (Etempvar _t'4 (tptr tvoid))))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _last_read (tarray (tptr tint) 3))
                        (Etempvar _r tint) (tptr (tptr tint))) (tptr tint))
                    (Etempvar _c (tptr tint)))))))))
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
  fn_temps := ((_b, tint) :: (_c, (tptr (Tstruct _atom_int noattr))) ::
               (_rr, (tptr tint)) :: (_lr, (tptr tint)) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _c
    (Ederef
      (Ebinop Oadd (Evar _comm (tarray (tptr (Tstruct _atom_int noattr)) 3))
        (Etempvar _r tint) (tptr (tptr (Tstruct _atom_int noattr))))
      (tptr (Tstruct _atom_int noattr))))
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
            (Evar _atom_exchange (Tfunction
                                   (Tcons (tptr (Tstruct _atom_int noattr))
                                     (Tcons tint Tnil)) tint cc_default))
            ((Etempvar _c (tptr (Tstruct _atom_int noattr))) ::
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
            (Sreturn (Some (Etempvar _b tint)))))))))
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
               (_c, (tptr (Tstruct _atom_int noattr))) :: (_b, tint) ::
               (_t'1, tint) :: nil);
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
                  (Ebinop Oadd
                    (Evar _comm (tarray (tptr (Tstruct _atom_int noattr)) 3))
                    (Etempvar _r tint)
                    (tptr (tptr (Tstruct _atom_int noattr))))
                  (tptr (Tstruct _atom_int noattr))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _atom_exchange (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _atom_int noattr))
                                             (Tcons tint Tnil)) tint
                                           cc_default))
                    ((Etempvar _c (tptr (Tstruct _atom_int noattr))) ::
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
                  Sskip))))
          (Sset _r
            (Ebinop Oadd (Etempvar _r tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Sassign (Evar _last_given tint) (Etempvar _w tint))
        (Sassign (Evar _writing tint)
          (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))))))
|}.

Definition f_reader := {|
  fn_return := tint;
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
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_arg, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_v, tuint) :: (_b, tint) ::
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
                  (Etempvar _v tuint))
                (Ssequence
                  (Scall None
                    (Evar _finish_write (Tfunction Tnil tvoid cc_default))
                    nil)
                  (Sset _v
                    (Ebinop Oadd (Etempvar _v tuint)
                      (Econst_int (Int.repr 1) tint) tuint)))))))
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
                         (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint
                                 cc_default)) (Tcons (tptr tvoid) Tnil))
                       tvoid cc_default))
        ((Ecast
           (Eaddrof
             (Evar _writer (Tfunction (Tcons (tptr tvoid) Tnil) tint
                             cc_default))
             (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default)))
           (tptr tvoid)) ::
         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
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
                    (Evar _surely_malloc (Tfunction (Tcons tulong Tnil)
                                           (tptr tvoid) cc_default))
                    ((Esizeof tint tulong) :: nil))
                  (Sset _d (Etempvar _t'1 (tptr tvoid))))
                (Ssequence
                  (Sassign (Ederef (Etempvar _d (tptr tint)) tint)
                    (Etempvar _i tint))
                  (Scall None
                    (Evar _spawn (Tfunction
                                   (Tcons
                                     (tptr (Tfunction
                                             (Tcons (tptr tvoid) Tnil) tint
                                             cc_default))
                                     (Tcons (tptr tvoid) Tnil)) tvoid
                                   cc_default))
                    ((Ecast
                       (Eaddrof
                         (Evar _reader (Tfunction (Tcons (tptr tvoid) Tnil)
                                         tint cc_default))
                         (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint
                                 cc_default))) (tptr tvoid)) ::
                     (Ecast (Etempvar _d (tptr tint)) (tptr tvoid)) :: nil)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Sloop Sskip Sskip))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _buffer Struct (Member_plain _data tint :: nil) noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
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
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
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
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
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
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
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
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
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
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_make_atomic,
   Gfun(External (EF_external "make_atomic"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons tint Tnil) (tptr (Tstruct _atom_int noattr)) cc_default)) ::
 (_atom_exchange,
   Gfun(External (EF_external "atom_exchange"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) (Tcons tint Tnil)) tint
     cc_default)) ::
 (_spawn,
   Gfun(External (EF_external "spawn"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default))
       (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_memset, Gfun(Internal f_memset)) :: (_bufs, Gvar v_bufs) ::
 (_comm, Gvar v_comm) :: (_reading, Gvar v_reading) ::
 (_last_read, Gvar v_last_read) ::
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
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _writer :: _reader :: _finish_write :: _start_write ::
 _initialize_writer :: _last_given :: _writing :: _last_taken ::
 _finish_read :: _start_read :: _initialize_reader :: _initialize_channels ::
 _last_read :: _reading :: _comm :: _bufs :: _memset :: _surely_malloc ::
 _spawn :: _atom_exchange :: _make_atomic :: _exit :: _malloc ::
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


