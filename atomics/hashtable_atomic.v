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
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "atomics/hashtable_atomic.c".
  Definition normalized := true.
End Info.

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
Definition ___dummy : ident := $"__dummy".
Definition ___pthread_t : ident := $"__pthread_t".
Definition _acquire : ident := $"acquire".
Definition _add_item : ident := $"add_item".
Definition _arg : ident := $"arg".
Definition _args : ident := $"args".
Definition _atom_CAS : ident := $"atom_CAS".
Definition _atom_int : ident := $"atom_int".
Definition _atom_load : ident := $"atom_load".
Definition _atom_store : ident := $"atom_store".
Definition _b : ident := $"b".
Definition _entry : ident := $"entry".
Definition _exit : ident := $"exit".
Definition _exit_thread : ident := $"exit_thread".
Definition _expected : ident := $"expected".
Definition _f : ident := $"f".
Definition _free : ident := $"free".
Definition _free_atomic : ident := $"free_atomic".
Definition _freelock : ident := $"freelock".
Definition _get_item : ident := $"get_item".
Definition _i : ident := $"i".
Definition _i__1 : ident := $"i__1".
Definition _i__2 : ident := $"i__2".
Definition _i__3 : ident := $"i__3".
Definition _idx : ident := $"idx".
Definition _init_table : ident := $"init_table".
Definition _integer_hash : ident := $"integer_hash".
Definition _key : ident := $"key".
Definition _l : ident := $"l".
Definition _l__1 : ident := $"l__1".
Definition _lock : ident := $"lock".
Definition _m_entries : ident := $"m_entries".
Definition _main : ident := $"main".
Definition _make_atomic : ident := $"make_atomic".
Definition _makelock : ident := $"makelock".
Definition _malloc : ident := $"malloc".
Definition _n : ident := $"n".
Definition _p : ident := $"p".
Definition _probed_key : ident := $"probed_key".
Definition _r : ident := $"r".
Definition _ref : ident := $"ref".
Definition _release : ident := $"release".
Definition _res : ident := $"res".
Definition _result : ident := $"result".
Definition _results : ident := $"results".
Definition _set_item : ident := $"set_item".
Definition _spawn : ident := $"spawn".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _t : ident := $"t".
Definition _thrd_create : ident := $"thrd_create".
Definition _thrd_exit : ident := $"thrd_exit".
Definition _thread_locks : ident := $"thread_locks".
Definition _total : ident := $"total".
Definition _value : ident := $"value".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.

Definition v_m_entries := {|
  gvar_info := (tarray (Tstruct _entry noattr) 16384);
  gvar_init := (Init_space 262144 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_thread_locks := {|
  gvar_info := (tarray (tptr (Tstruct _atom_int noattr)) 3);
  gvar_init := (Init_space 24 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_results := {|
  gvar_info := (tarray (tptr tint) 3);
  gvar_init := (Init_space 24 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

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
  fn_vars := ((_ref, tint) :: nil);
  fn_temps := ((_idx, tint) :: (_i, (tptr (Tstruct _atom_int noattr))) ::
               (_probed_key, tint) :: (_result, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'4, tint) :: nil);
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
        (Sassign (Evar _ref tint) (Econst_int (Int.repr 0) tint))
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
                (tptr (Tstruct _atom_int noattr))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _atom_load (Tfunction
                                     (Tcons (tptr (Tstruct _atom_int noattr))
                                       Tnil) tint cc_default))
                  ((Etempvar _i (tptr (Tstruct _atom_int noattr))) :: nil))
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
                          (Evar _atom_CAS (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _atom_int noattr))
                                              (Tcons (tptr tint)
                                                (Tcons tint Tnil))) tint
                                            cc_default))
                          ((Etempvar _i (tptr (Tstruct _atom_int noattr))) ::
                           (Eaddrof (Evar _ref tint) (tptr tint)) ::
                           (Etempvar _key tint) :: nil))
                        (Sset _result (Etempvar _t'3 tint)))
                      (Sifthenelse (Eunop Onotbool (Etempvar _result tint)
                                     tint)
                        (Ssequence
                          (Sset _t'4 (Evar _ref tint))
                          (Sifthenelse (Ebinop One (Etempvar _t'4 tint)
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
                          (Etempvar _idx tint)
                          (tptr (Tstruct _entry noattr)))
                        (Tstruct _entry noattr)) _value
                      (tptr (Tstruct _atom_int noattr))))
                  (Ssequence
                    (Scall None
                      (Evar _atom_store (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _atom_int noattr))
                                            (Tcons tint Tnil)) tvoid
                                          cc_default))
                      ((Etempvar _i (tptr (Tstruct _atom_int noattr))) ::
                       (Etempvar _value tint) :: nil))
                    (Sreturn None)))))))))
    (Sset _idx
      (Ebinop Oadd (Etempvar _idx tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_get_item := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_key, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_idx, tint) :: (_i, (tptr (Tstruct _atom_int noattr))) ::
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
              (tptr (Tstruct _atom_int noattr))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _atom_load (Tfunction
                                   (Tcons (tptr (Tstruct _atom_int noattr))
                                     Tnil) tint cc_default))
                ((Etempvar _i (tptr (Tstruct _atom_int noattr))) :: nil))
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
                      (tptr (Tstruct _atom_int noattr))))
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _atom_load (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _atom_int noattr))
                                           Tnil) tint cc_default))
                      ((Etempvar _i (tptr (Tstruct _atom_int noattr))) ::
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
  fn_vars := ((_ref, tint) :: nil);
  fn_temps := ((_idx, tint) :: (_i, (tptr (Tstruct _atom_int noattr))) ::
               (_probed_key, tint) :: (_result, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'5, tint) :: nil);
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
        (Sassign (Evar _ref tint) (Econst_int (Int.repr 0) tint))
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
                (tptr (Tstruct _atom_int noattr))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _atom_load (Tfunction
                                     (Tcons (tptr (Tstruct _atom_int noattr))
                                       Tnil) tint cc_default))
                  ((Etempvar _i (tptr (Tstruct _atom_int noattr))) :: nil))
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
                          (Evar _atom_CAS (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _atom_int noattr))
                                              (Tcons (tptr tint)
                                                (Tcons tint Tnil))) tint
                                            cc_default))
                          ((Etempvar _i (tptr (Tstruct _atom_int noattr))) ::
                           (Eaddrof (Evar _ref tint) (tptr tint)) ::
                           (Etempvar _key tint) :: nil))
                        (Sset _result (Etempvar _t'3 tint)))
                      (Sifthenelse (Eunop Onotbool (Etempvar _result tint)
                                     tint)
                        (Ssequence
                          (Sset _t'5 (Evar _ref tint))
                          (Sifthenelse (Ebinop One (Etempvar _t'5 tint)
                                         (Etempvar _key tint) tint)
                            Scontinue
                            Sskip))
                        Sskip)))
                  Sskip)
                (Ssequence
                  (Sassign (Evar _ref tint) (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sset _i
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                            (Etempvar _idx tint)
                            (tptr (Tstruct _entry noattr)))
                          (Tstruct _entry noattr)) _value
                        (tptr (Tstruct _atom_int noattr))))
                    (Ssequence
                      (Scall (Some _t'4)
                        (Evar _atom_CAS (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _atom_int noattr))
                                            (Tcons (tptr tint)
                                              (Tcons tint Tnil))) tint
                                          cc_default))
                        ((Etempvar _i (tptr (Tstruct _atom_int noattr))) ::
                         (Eaddrof (Evar _ref tint) (tptr tint)) ::
                         (Etempvar _value tint) :: nil))
                      (Sreturn (Some (Etempvar _t'4 tint))))))))))))
    (Sset _idx
      (Ebinop Oadd (Etempvar _idx tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_init_table := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'2, (tptr (Tstruct _atom_int noattr))) ::
               (_t'1, (tptr (Tstruct _atom_int noattr))) :: nil);
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
                                 (tptr (Tstruct _atom_int noattr))
                                 cc_default))
            ((Econst_int (Int.repr 0) tint) :: nil))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                  (Etempvar _i tint) (tptr (Tstruct _entry noattr)))
                (Tstruct _entry noattr)) _key
              (tptr (Tstruct _atom_int noattr)))
            (Etempvar _t'1 (tptr (Tstruct _atom_int noattr)))))
        (Ssequence
          (Scall (Some _t'2)
            (Evar _make_atomic (Tfunction (Tcons tint Tnil)
                                 (tptr (Tstruct _atom_int noattr))
                                 cc_default))
            ((Econst_int (Int.repr 0) tint) :: nil))
          (Sassign
            (Efield
              (Ederef
                (Ebinop Oadd
                  (Evar _m_entries (tarray (Tstruct _entry noattr) 16384))
                  (Etempvar _i tint) (tptr (Tstruct _entry noattr)))
                (Tstruct _entry noattr)) _value
              (tptr (Tstruct _atom_int noattr)))
            (Etempvar _t'2 (tptr (Tstruct _atom_int noattr)))))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_f := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_arg, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, tint) :: (_l, (tptr (Tstruct _atom_int noattr))) ::
               (_res, (tptr tint)) :: (_total, tint) :: (_i, tint) ::
               (_r, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t (Ederef (Ecast (Etempvar _arg (tptr tvoid)) (tptr tint)) tint))
  (Ssequence
    (Sset _l
      (Ederef
        (Ebinop Oadd
          (Evar _thread_locks (tarray (tptr (Tstruct _atom_int noattr)) 3))
          (Etempvar _t tint) (tptr (tptr (Tstruct _atom_int noattr))))
        (tptr (Tstruct _atom_int noattr))))
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
                  (Evar _release (Tfunction
                                   (Tcons (tptr (Tstruct _atom_int noattr))
                                     Tnil) tvoid cc_default))
                  ((Etempvar _l (tptr (Tstruct _atom_int noattr))) :: nil))
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_total, tint) :: (_i, tint) ::
               (_l, (tptr (Tstruct _atom_int noattr))) :: (_i__1, tint) ::
               (_t, (tptr tint)) :: (_i__2, tint) ::
               (_l__1, (tptr (Tstruct _atom_int noattr))) ::
               (_r, (tptr tint)) :: (_i__3, tint) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr (Tstruct _atom_int noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
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
                    (Evar _surely_malloc (Tfunction (Tcons tulong Tnil)
                                           (tptr tvoid) cc_default))
                    ((Esizeof tint tulong) :: nil))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _results (tarray (tptr tint) 3))
                        (Etempvar _i tint) (tptr (tptr tint))) (tptr tint))
                    (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tint))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'2)
                      (Evar _makelock (Tfunction Tnil
                                        (tptr (Tstruct _atom_int noattr))
                                        cc_default)) nil)
                    (Sset _l
                      (Etempvar _t'2 (tptr (Tstruct _atom_int noattr)))))
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Evar _thread_locks (tarray (tptr (Tstruct _atom_int noattr)) 3))
                        (Etempvar _i tint)
                        (tptr (tptr (Tstruct _atom_int noattr))))
                      (tptr (Tstruct _atom_int noattr)))
                    (Etempvar _l (tptr (Tstruct _atom_int noattr)))))))
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
                      (Evar _surely_malloc (Tfunction (Tcons tulong Tnil)
                                             (tptr tvoid) cc_default))
                      ((Esizeof tint tulong) :: nil))
                    (Sset _t
                      (Ecast (Etempvar _t'3 (tptr tvoid)) (tptr tint))))
                  (Ssequence
                    (Sassign (Ederef (Etempvar _t (tptr tint)) tint)
                      (Etempvar _i__1 tint))
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
                           (Evar _f (Tfunction (Tcons (tptr tvoid) Tnil) tint
                                      cc_default))
                           (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint
                                   cc_default))) (tptr tvoid)) ::
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
                        (Evar _thread_locks (tarray (tptr (Tstruct _atom_int noattr)) 3))
                        (Etempvar _i__2 tint)
                        (tptr (tptr (Tstruct _atom_int noattr))))
                      (tptr (Tstruct _atom_int noattr))))
                  (Ssequence
                    (Scall None
                      (Evar _acquire (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _atom_int noattr))
                                         Tnil) tvoid cc_default))
                      ((Etempvar _l__1 (tptr (Tstruct _atom_int noattr))) ::
                       nil))
                    (Ssequence
                      (Scall None
                        (Evar _freelock (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _atom_int noattr))
                                            Tnil) tvoid cc_default))
                        ((Etempvar _l__1 (tptr (Tstruct _atom_int noattr))) ::
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
                                (Etempvar _i__3 tint) tint)))))))))
              (Sset _i__2
                (Ebinop Oadd (Etempvar _i__2 tint)
                  (Econst_int (Int.repr 1) tint) tint))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _entry Struct
   (Member_plain _key (tptr (Tstruct _atom_int noattr)) ::
    Member_plain _value (tptr (Tstruct _atom_int noattr)) :: nil)
   noattr :: nil).

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
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_make_atomic,
   Gfun(External (EF_external "make_atomic"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons tint Tnil) (tptr (Tstruct _atom_int noattr)) cc_default)) ::
 (_atom_load,
   Gfun(External (EF_external "atom_load"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tint cc_default)) ::
 (_atom_store,
   Gfun(External (EF_external "atom_store"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) (Tcons tint Tnil)) tvoid
     cc_default)) ::
 (_atom_CAS,
   Gfun(External (EF_external "atom_CAS"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr))
       (Tcons (tptr tint) (Tcons tint Tnil))) tint cc_default)) ::
 (_makelock,
   Gfun(External (EF_external "makelock"
                   (mksignature nil AST.Tlong cc_default)) Tnil
     (tptr (Tstruct _atom_int noattr)) cc_default)) ::
 (_freelock,
   Gfun(External (EF_external "freelock"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid cc_default)) ::
 (_release,
   Gfun(External (EF_external "release"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr (Tstruct _atom_int noattr)) Tnil) tvoid cc_default)) ::
 (_spawn,
   Gfun(External (EF_external "spawn"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tint cc_default))
       (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
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
 _m_entries :: _spawn :: _release :: _acquire :: _freelock :: _makelock ::
 _atom_CAS :: _atom_store :: _atom_load :: _make_atomic :: _malloc ::
 _free :: _exit :: ___builtin_debug :: ___builtin_write32_reversed ::
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


