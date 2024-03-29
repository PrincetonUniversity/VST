From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.12".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "32sse2".
  Definition abi := "standard".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "progs/load_demo.c".
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 23%positive.
Definition ___builtin_annot_intval : ident := 24%positive.
Definition ___builtin_bswap : ident := 8%positive.
Definition ___builtin_bswap16 : ident := 10%positive.
Definition ___builtin_bswap32 : ident := 9%positive.
Definition ___builtin_bswap64 : ident := 7%positive.
Definition ___builtin_clz : ident := 11%positive.
Definition ___builtin_clzl : ident := 12%positive.
Definition ___builtin_clzll : ident := 13%positive.
Definition ___builtin_ctz : ident := 14%positive.
Definition ___builtin_ctzl : ident := 15%positive.
Definition ___builtin_ctzll : ident := 16%positive.
Definition ___builtin_debug : ident := 42%positive.
Definition ___builtin_expect : ident := 31%positive.
Definition ___builtin_fabs : ident := 17%positive.
Definition ___builtin_fabsf : ident := 18%positive.
Definition ___builtin_fmadd : ident := 34%positive.
Definition ___builtin_fmax : ident := 32%positive.
Definition ___builtin_fmin : ident := 33%positive.
Definition ___builtin_fmsub : ident := 35%positive.
Definition ___builtin_fnmadd : ident := 36%positive.
Definition ___builtin_fnmsub : ident := 37%positive.
Definition ___builtin_fsqrt : ident := 19%positive.
Definition ___builtin_membar : ident := 25%positive.
Definition ___builtin_memcpy_aligned : ident := 21%positive.
Definition ___builtin_read16_reversed : ident := 38%positive.
Definition ___builtin_read32_reversed : ident := 39%positive.
Definition ___builtin_sel : ident := 22%positive.
Definition ___builtin_sqrt : ident := 20%positive.
Definition ___builtin_unreachable : ident := 30%positive.
Definition ___builtin_va_arg : ident := 27%positive.
Definition ___builtin_va_copy : ident := 28%positive.
Definition ___builtin_va_end : ident := 29%positive.
Definition ___builtin_va_start : ident := 26%positive.
Definition ___builtin_write16_reversed : ident := 40%positive.
Definition ___builtin_write32_reversed : ident := 41%positive.
Definition ___compcert_i64_dtos : ident := 72%positive.
Definition ___compcert_i64_dtou : ident := 73%positive.
Definition ___compcert_i64_sar : ident := 84%positive.
Definition ___compcert_i64_sdiv : ident := 78%positive.
Definition ___compcert_i64_shl : ident := 82%positive.
Definition ___compcert_i64_shr : ident := 83%positive.
Definition ___compcert_i64_smod : ident := 80%positive.
Definition ___compcert_i64_smulh : ident := 85%positive.
Definition ___compcert_i64_stod : ident := 74%positive.
Definition ___compcert_i64_stof : ident := 76%positive.
Definition ___compcert_i64_udiv : ident := 79%positive.
Definition ___compcert_i64_umod : ident := 81%positive.
Definition ___compcert_i64_umulh : ident := 86%positive.
Definition ___compcert_i64_utod : ident := 75%positive.
Definition ___compcert_i64_utof : ident := 77%positive.
Definition ___compcert_va_composite : ident := 71%positive.
Definition ___compcert_va_float64 : ident := 70%positive.
Definition ___compcert_va_int32 : ident := 68%positive.
Definition ___compcert_va_int64 : ident := 69%positive.
Definition _b0 : ident := 54%positive.
Definition _b1 : ident := 55%positive.
Definition _b2 : ident := 56%positive.
Definition _b3 : ident := 57%positive.
Definition _fiddle : ident := 52%positive.
Definition _fst : ident := 2%positive.
Definition _get22 : ident := 47%positive.
Definition _get_little_endian : ident := 58%positive.
Definition _i : ident := 44%positive.
Definition _input : ident := 53%positive.
Definition _int_pair : ident := 1%positive.
Definition _left : ident := 5%positive.
Definition _main : ident := 67%positive.
Definition _obj : ident := 62%positive.
Definition _onetwo : ident := 59%positive.
Definition _p : ident := 45%positive.
Definition _pair_pair : ident := 4%positive.
Definition _pp : ident := 61%positive.
Definition _pps : ident := 43%positive.
Definition _r : ident := 51%positive.
Definition _res : ident := 46%positive.
Definition _res1 : ident := 64%positive.
Definition _res2 : ident := 65%positive.
Definition _res3 : ident := 66%positive.
Definition _right : ident := 6%positive.
Definition _size : ident := 49%positive.
Definition _snd : ident := 3%positive.
Definition _sum : ident := 48%positive.
Definition _tagword : ident := 50%positive.
Definition _threefour : ident := 60%positive.
Definition _v : ident := 63%positive.
Definition _t'1 : ident := 87%positive.
Definition _t'2 : ident := 88%positive.
Definition _t'3 : ident := 89%positive.

Definition f_get22 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_pps, (tptr (Tstruct _pair_pair noattr))) :: (_i, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _int_pair noattr))) :: (_res, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Eaddrof
      (Efield
        (Ederef
          (Ebinop Oadd (Etempvar _pps (tptr (Tstruct _pair_pair noattr)))
            (Etempvar _i tint) (tptr (Tstruct _pair_pair noattr)))
          (Tstruct _pair_pair noattr)) _right (Tstruct _int_pair noattr))
      (tptr (Tstruct _int_pair noattr))))
  (Ssequence
    (Sset _res
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _int_pair noattr)))
          (Tstruct _int_pair noattr)) _snd tint))
    (Sreturn (Some (Etempvar _res tint)))))
|}.

Definition f_fiddle := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_sum, tuint) :: (_size, tuint) :: (_i, tuint) ::
               (_tagword, tuint) :: (_r, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _tagword
    (Ederef
      (Ebinop Oadd (Etempvar _p (tptr tuint))
        (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) (tptr tuint)) tuint))
  (Ssequence
    (Sset _sum
      (Ebinop Oand (Etempvar _tagword tuint) (Econst_int (Int.repr 255) tint)
        tuint))
    (Ssequence
      (Sset _size
        (Ebinop Oshr (Etempvar _tagword tuint)
          (Econst_int (Int.repr 10) tint) tuint))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                             (Etempvar _size tuint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _r
                  (Ederef
                    (Ebinop Oadd (Etempvar _p (tptr tuint))
                      (Etempvar _i tuint) (tptr tuint)) tuint))
                (Sset _sum
                  (Ebinop Oadd (Etempvar _sum tuint) (Etempvar _r tuint)
                    tuint))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                tuint))))
        (Sreturn (Some (Etempvar _sum tuint)))))))
|}.

Definition f_get_little_endian := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_input, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_b0, tuint) :: (_b1, tuint) :: (_b2, tuint) ::
               (_b3, tuint) :: (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd (Etempvar _input (tptr tuchar))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
    (Sset _b0 (Ecast (Etempvar _t'2 tuchar) tuint)))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Ederef
          (Ebinop Oadd (Etempvar _input (tptr tuchar))
            (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar))
      (Sset _b1 (Ecast (Etempvar _t'1 tuchar) tuint)))
    (Ssequence
      (Sset _b2
        (Ederef
          (Ebinop Oadd (Etempvar _input (tptr tuchar))
            (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar))
      (Ssequence
        (Sset _b3
          (Ederef
            (Ebinop Oadd (Etempvar _input (tptr tuchar))
              (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar))
        (Sreturn (Some (Ebinop Oor
                         (Ebinop Oor
                           (Ebinop Oor (Etempvar _b0 tuint)
                             (Ebinop Oshl (Etempvar _b1 tuint)
                               (Econst_int (Int.repr 8) tint) tuint) tuint)
                           (Ebinop Oshl (Etempvar _b2 tuint)
                             (Econst_int (Int.repr 16) tint) tuint) tuint)
                         (Ebinop Oshl (Etempvar _b3 tuint)
                           (Econst_int (Int.repr 24) tint) tuint) tuint)))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_onetwo, (Tstruct _int_pair noattr)) ::
              (_threefour, (Tstruct _int_pair noattr)) ::
              (_pp, (Tstruct _pair_pair noattr)) ::
              (_pps, (tarray (Tstruct _pair_pair noattr) 1)) ::
              (_obj, (tarray tuint 3)) :: (_v, (tarray tuchar 4)) :: nil);
  fn_temps := ((_p, (tptr tuint)) :: (_res1, tint) :: (_res2, tint) ::
               (_res3, tuint) :: (_t'3, tuint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sassign (Efield (Evar _onetwo (Tstruct _int_pair noattr)) _fst tint)
      (Econst_int (Int.repr 1) tint))
    (Ssequence
      (Sassign (Efield (Evar _onetwo (Tstruct _int_pair noattr)) _snd tint)
        (Econst_int (Int.repr 2) tint))
      (Ssequence
        (Sassign
          (Efield (Evar _threefour (Tstruct _int_pair noattr)) _fst tint)
          (Econst_int (Int.repr 3) tint))
        (Ssequence
          (Sassign
            (Efield (Evar _threefour (Tstruct _int_pair noattr)) _snd tint)
            (Econst_int (Int.repr 4) tint))
          (Ssequence
            (Sassign
              (Efield (Evar _pp (Tstruct _pair_pair noattr)) _left
                (Tstruct _int_pair noattr))
              (Evar _onetwo (Tstruct _int_pair noattr)))
            (Ssequence
              (Sassign
                (Efield (Evar _pp (Tstruct _pair_pair noattr)) _right
                  (Tstruct _int_pair noattr))
                (Evar _threefour (Tstruct _int_pair noattr)))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Evar _pps (tarray (Tstruct _pair_pair noattr) 1))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (Tstruct _pair_pair noattr)))
                    (Tstruct _pair_pair noattr))
                  (Evar _pp (Tstruct _pair_pair noattr)))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _obj (tarray tuint 3))
                        (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
                    (Ebinop Oshl (Econst_int (Int.repr 2) tint)
                      (Econst_int (Int.repr 10) tint) tint))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _obj (tarray tuint 3))
                          (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
                      (Econst_int (Int.repr 11) tint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _obj (tarray tuint 3))
                            (Econst_int (Int.repr 2) tint) (tptr tuint))
                          tuint) (Econst_int (Int.repr 12) tint))
                      (Ssequence
                        (Sset _p
                          (Ebinop Oadd (Evar _obj (tarray tuint 3))
                            (Econst_int (Int.repr 1) tint) (tptr tuint)))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _v (tarray tuchar 4))
                                (Econst_int (Int.repr 0) tint) (tptr tuchar))
                              tuchar) (Econst_int (Int.repr 10) tint))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _v (tarray tuchar 4))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuchar)) tuchar)
                              (Econst_int (Int.repr 20) tint))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Evar _v (tarray tuchar 4))
                                    (Econst_int (Int.repr 2) tint)
                                    (tptr tuchar)) tuchar)
                                (Econst_int (Int.repr 30) tint))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd (Evar _v (tarray tuchar 4))
                                      (Econst_int (Int.repr 3) tint)
                                      (tptr tuchar)) tuchar)
                                  (Econst_int (Int.repr 40) tint))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'1)
                                      (Evar _get22 (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _pair_pair noattr))
                                                       (Tcons tint Tnil))
                                                     tint cc_default))
                                      ((Evar _pps (tarray (Tstruct _pair_pair noattr) 1)) ::
                                       (Econst_int (Int.repr 0) tint) :: nil))
                                    (Sset _res1 (Etempvar _t'1 tint)))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'2)
                                        (Evar _fiddle (Tfunction
                                                        (Tcons (tptr tuint)
                                                          Tnil) tint
                                                        cc_default))
                                        ((Etempvar _p (tptr tuint)) :: nil))
                                      (Sset _res2 (Etempvar _t'2 tint)))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'3)
                                          (Evar _get_little_endian (Tfunction
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    Tnil)
                                                                    tuint
                                                                    cc_default))
                                          ((Evar _v (tarray tuchar 4)) ::
                                           nil))
                                        (Sset _res3 (Etempvar _t'3 tuint)))
                                      (Sreturn (Some (Ebinop Oadd
                                                       (Ebinop Oadd
                                                         (Etempvar _res1 tint)
                                                         (Etempvar _res2 tint)
                                                         tint)
                                                       (Ebinop Oshr
                                                         (Etempvar _res3 tuint)
                                                         (Econst_int (Int.repr 24) tint)
                                                         tuint) tuint)))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _int_pair Struct
   (Member_plain _fst tint :: Member_plain _snd tint :: nil)
   noattr ::
 Composite _pair_pair Struct
   (Member_plain _left (Tstruct _int_pair noattr) ::
    Member_plain _right (Tstruct _int_pair noattr) :: nil)
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
 (_get22, Gfun(Internal f_get22)) :: (_fiddle, Gfun(Internal f_fiddle)) ::
 (_get_little_endian, Gfun(Internal f_get_little_endian)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _get_little_endian :: _fiddle :: _get22 :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


