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
  Definition source_file := "malloc.c".
  Definition normalized := true.
End Info.

Definition _Nblocks : ident := 71%positive.
Definition ___builtin_annot : ident := 17%positive.
Definition ___builtin_annot_intval : ident := 18%positive.
Definition ___builtin_bswap : ident := 2%positive.
Definition ___builtin_bswap16 : ident := 4%positive.
Definition ___builtin_bswap32 : ident := 3%positive.
Definition ___builtin_bswap64 : ident := 1%positive.
Definition ___builtin_clz : ident := 5%positive.
Definition ___builtin_clzl : ident := 6%positive.
Definition ___builtin_clzll : ident := 7%positive.
Definition ___builtin_ctz : ident := 8%positive.
Definition ___builtin_ctzl : ident := 9%positive.
Definition ___builtin_ctzll : ident := 10%positive.
Definition ___builtin_debug : ident := 36%positive.
Definition ___builtin_expect : ident := 25%positive.
Definition ___builtin_fabs : ident := 11%positive.
Definition ___builtin_fabsf : ident := 12%positive.
Definition ___builtin_fmadd : ident := 28%positive.
Definition ___builtin_fmax : ident := 26%positive.
Definition ___builtin_fmin : ident := 27%positive.
Definition ___builtin_fmsub : ident := 29%positive.
Definition ___builtin_fnmadd : ident := 30%positive.
Definition ___builtin_fnmsub : ident := 31%positive.
Definition ___builtin_fsqrt : ident := 13%positive.
Definition ___builtin_membar : ident := 19%positive.
Definition ___builtin_memcpy_aligned : ident := 15%positive.
Definition ___builtin_read16_reversed : ident := 32%positive.
Definition ___builtin_read32_reversed : ident := 33%positive.
Definition ___builtin_sel : ident := 16%positive.
Definition ___builtin_sqrt : ident := 14%positive.
Definition ___builtin_unreachable : ident := 24%positive.
Definition ___builtin_va_arg : ident := 21%positive.
Definition ___builtin_va_copy : ident := 22%positive.
Definition ___builtin_va_end : ident := 23%positive.
Definition ___builtin_va_start : ident := 20%positive.
Definition ___builtin_write16_reversed : ident := 34%positive.
Definition ___builtin_write32_reversed : ident := 35%positive.
Definition ___compcert_i64_dtos : ident := 49%positive.
Definition ___compcert_i64_dtou : ident := 50%positive.
Definition ___compcert_i64_sar : ident := 61%positive.
Definition ___compcert_i64_sdiv : ident := 55%positive.
Definition ___compcert_i64_shl : ident := 59%positive.
Definition ___compcert_i64_shr : ident := 60%positive.
Definition ___compcert_i64_smod : ident := 57%positive.
Definition ___compcert_i64_smulh : ident := 62%positive.
Definition ___compcert_i64_stod : ident := 51%positive.
Definition ___compcert_i64_stof : ident := 53%positive.
Definition ___compcert_i64_udiv : ident := 56%positive.
Definition ___compcert_i64_umod : ident := 58%positive.
Definition ___compcert_i64_umulh : ident := 63%positive.
Definition ___compcert_i64_utod : ident := 52%positive.
Definition ___compcert_i64_utof : ident := 54%positive.
Definition ___compcert_va_composite : ident := 48%positive.
Definition ___compcert_va_float64 : ident := 47%positive.
Definition ___compcert_va_int32 : ident := 45%positive.
Definition ___compcert_va_int64 : ident := 46%positive.
Definition _addr : ident := 39%positive.
Definition _b : ident := 65%positive.
Definition _bin : ident := 69%positive.
Definition _bin2size : ident := 66%positive.
Definition _chunks : ident := 79%positive.
Definition _fildes : ident := 41%positive.
Definition _fill_bin : ident := 81%positive.
Definition _free : ident := 87%positive.
Definition _free_large : ident := 86%positive.
Definition _free_small : ident := 85%positive.
Definition _ful : ident := 78%positive.
Definition _j : ident := 73%positive.
Definition _len : ident := 40%positive.
Definition _list_from_block : ident := 74%positive.
Definition _main : ident := 64%positive.
Definition _malloc : ident := 88%positive.
Definition _malloc_large : ident := 84%positive.
Definition _malloc_small : ident := 83%positive.
Definition _mmap : ident := 37%positive.
Definition _mmap0 : ident := 43%positive.
Definition _mmap0_placeholder : ident := 44%positive.
Definition _munmap : ident := 38%positive.
Definition _n : ident := 75%positive.
Definition _nbytes : ident := 82%positive.
Definition _p : ident := 42%positive.
Definition _pre_fill : ident := 76%positive.
Definition _q : ident := 72%positive.
Definition _req : ident := 77%positive.
Definition _s : ident := 67%positive.
Definition _size2bin : ident := 68%positive.
Definition _tl : ident := 70%positive.
Definition _try_pre_fill : ident := 80%positive.
Definition _t'1 : ident := 89%positive.
Definition _t'2 : ident := 90%positive.
Definition _t'3 : ident := 91%positive.
Definition _t'4 : ident := 92%positive.

Definition f_bin2size := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_b, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Omul
                 (Ebinop Osub
                   (Ebinop Omul
                     (Ebinop Oadd (Etempvar _b tint)
                       (Econst_int (Int.repr 1) tint) tint)
                     (Econst_int (Int.repr 2) tint) tint)
                   (Econst_int (Int.repr 1) tint) tint)
                 (Econst_int (Int.repr 4) tint) tint)))
|}.

Definition f_size2bin := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _bin2size (Tfunction (Tcons tint Tnil) tuint cc_default))
    ((Ebinop Osub (Econst_int (Int.repr 50) tint)
       (Econst_int (Int.repr 1) tint) tint) :: nil))
  (Sifthenelse (Ebinop Ogt (Etempvar _s tuint) (Etempvar _t'1 tuint) tint)
    (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
    (Sreturn (Some (Ebinop Odiv
                     (Ebinop Oadd (Etempvar _s tuint)
                       (Ebinop Osub
                         (Ebinop Omul (Econst_int (Int.repr 4) tint)
                           (Ebinop Osub (Econst_int (Int.repr 2) tint)
                             (Econst_int (Int.repr 1) tint) tint) tint)
                         (Econst_int (Int.repr 1) tint) tint) tuint)
                     (Ebinop Omul (Econst_int (Int.repr 4) tint)
                       (Econst_int (Int.repr 2) tint) tint) tuint)))))
|}.

Definition v_bin := {|
  gvar_info := (tarray (tptr tvoid) 50);
  gvar_init := (Init_space 200 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_list_from_block := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_s, tuint) :: (_p, (tptr tschar)) :: (_tl, (tptr tvoid)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_Nblocks, tint) :: (_q, (tptr tschar)) :: (_j, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _Nblocks
    (Ebinop Odiv
      (Ebinop Osub (Econst_int (Int.repr 524288) tint)
        (Econst_int (Int.repr 4) tint) tint)
      (Ebinop Oadd (Etempvar _s tuint) (Econst_int (Int.repr 4) tint) tuint)
      tuint))
  (Ssequence
    (Sset _q
      (Ebinop Oadd (Etempvar _p (tptr tschar)) (Econst_int (Int.repr 4) tint)
        (tptr tschar)))
    (Ssequence
      (Sset _j (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Swhile
          (Ebinop One (Etempvar _j tint)
            (Ebinop Osub (Etempvar _Nblocks tint)
              (Econst_int (Int.repr 1) tint) tint) tint)
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Ecast (Etempvar _q (tptr tschar)) (tptr tuint))
                  (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
              (Etempvar _s tuint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ecast
                    (Ebinop Oadd
                      (Ecast (Etempvar _q (tptr tschar)) (tptr tuint))
                      (Econst_int (Int.repr 1) tint) (tptr tuint))
                    (tptr (tptr tvoid))) (tptr tvoid))
                (Ebinop Oadd
                  (Ebinop Oadd (Etempvar _q (tptr tschar))
                    (Econst_int (Int.repr 4) tint) (tptr tschar))
                  (Ebinop Oadd (Etempvar _s tuint)
                    (Econst_int (Int.repr 4) tint) tuint) (tptr tschar)))
              (Ssequence
                (Sset _q
                  (Ebinop Oadd (Etempvar _q (tptr tschar))
                    (Ebinop Oadd (Etempvar _s tuint)
                      (Econst_int (Int.repr 4) tint) tuint) (tptr tschar)))
                (Sset _j
                  (Ebinop Oadd (Etempvar _j tint)
                    (Econst_int (Int.repr 1) tint) tint))))))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Ecast (Etempvar _q (tptr tschar)) (tptr tuint))
                (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
            (Etempvar _s tuint))
          (Ssequence
            (Sassign
              (Ederef
                (Ecast
                  (Ebinop Oadd
                    (Ecast (Etempvar _q (tptr tschar)) (tptr tuint))
                    (Econst_int (Int.repr 1) tint) (tptr tuint))
                  (tptr (tptr tvoid))) (tptr tvoid))
              (Etempvar _tl (tptr tvoid)))
            (Sreturn (Some (Ecast
                             (Ebinop Oadd
                               (Ebinop Oadd (Etempvar _p (tptr tschar))
                                 (Econst_int (Int.repr 4) tint)
                                 (tptr tschar))
                               (Econst_int (Int.repr 4) tint) (tptr tschar))
                             (tptr tvoid))))))))))
|}.

Definition f_pre_fill := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_n, tuint) :: (_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tint) :: (_t'3, (tptr tvoid)) :: (_t'2, tuint) ::
               (_t'1, tint) :: (_t'4, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _size2bin (Tfunction (Tcons tuint Tnil) tint cc_default))
      ((Etempvar _n tuint) :: nil))
    (Sset _b (Etempvar _t'1 tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _bin2size (Tfunction (Tcons tint Tnil) tuint cc_default))
        ((Etempvar _b tint) :: nil))
      (Ssequence
        (Sset _t'4
          (Ederef
            (Ebinop Oadd (Evar _bin (tarray (tptr tvoid) 50))
              (Etempvar _b tint) (tptr (tptr tvoid))) (tptr tvoid)))
        (Scall (Some _t'3)
          (Evar _list_from_block (Tfunction
                                   (Tcons tuint
                                     (Tcons (tptr tschar)
                                       (Tcons (tptr tvoid) Tnil)))
                                   (tptr tvoid) cc_default))
          ((Etempvar _t'2 tuint) :: (Etempvar _p (tptr tvoid)) ::
           (Etempvar _t'4 (tptr tvoid)) :: nil))))
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _bin (tarray (tptr tvoid) 50)) (Etempvar _b tint)
          (tptr (tptr tvoid))) (tptr tvoid)) (Etempvar _t'3 (tptr tvoid)))))
|}.

Definition f_try_pre_fill := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_n, tuint) :: (_req, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tint) :: (_ful, tint) :: (_chunks, tint) ::
               (_p, (tptr tschar)) :: (_t'4, (tptr tvoid)) ::
               (_t'3, tuint) :: (_t'2, tint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _bin2size (Tfunction (Tcons tint Tnil) tuint cc_default))
      ((Ebinop Osub (Econst_int (Int.repr 50) tint)
         (Econst_int (Int.repr 1) tint) tint) :: nil))
    (Sifthenelse (Ebinop Olt (Etempvar _t'1 tuint) (Etempvar _n tuint) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _size2bin (Tfunction (Tcons tuint Tnil) tint cc_default))
        ((Etempvar _n tuint) :: nil))
      (Sset _b (Etempvar _t'2 tint)))
    (Ssequence
      (Sset _ful (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _bin2size (Tfunction (Tcons tint Tnil) tuint cc_default))
            ((Etempvar _b tint) :: nil))
          (Sset _chunks
            (Ebinop Odiv
              (Ebinop Osub (Econst_int (Int.repr 524288) tint)
                (Econst_int (Int.repr 4) tint) tint)
              (Ebinop Oadd (Etempvar _t'3 tuint)
                (Econst_int (Int.repr 4) tint) tuint) tuint)))
        (Ssequence
          (Swhile
            (Ebinop Olt (Econst_int (Int.repr 0) tint)
              (Ebinop Osub (Etempvar _req tint) (Etempvar _ful tint) tint)
              tint)
            (Ssequence
              (Sifthenelse (Ebinop Olt
                             (Ebinop Osub
                               (Econst_int (Int.repr 2147483647) tint)
                               (Etempvar _ful tint) tint)
                             (Etempvar _chunks tint) tint)
                (Sreturn (Some (Etempvar _ful tint)))
                Sskip)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _mmap0 (Tfunction
                                   (Tcons (tptr tvoid)
                                     (Tcons tuint (Tcons tint Tnil)))
                                   (tptr tvoid) cc_default))
                    ((Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
                     (Econst_int (Int.repr 524288) tint) ::
                     (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))
                  (Sset _p
                    (Ecast (Etempvar _t'4 (tptr tvoid)) (tptr tschar))))
                (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr tschar))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  (Sreturn (Some (Etempvar _ful tint)))
                  (Ssequence
                    (Scall None
                      (Evar _pre_fill (Tfunction
                                        (Tcons tuint
                                          (Tcons (tptr tvoid) Tnil)) tvoid
                                        cc_default))
                      ((Etempvar _n tuint) :: (Etempvar _p (tptr tschar)) ::
                       nil))
                    (Sset _ful
                      (Ebinop Oadd (Etempvar _ful tint)
                        (Etempvar _chunks tint) tint)))))))
          (Sreturn (Some (Etempvar _ful tint))))))))
|}.

Definition f_fill_bin := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_b, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, tuint) :: (_p, (tptr tschar)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _bin2size (Tfunction (Tcons tint Tnil) tuint cc_default))
      ((Etempvar _b tint) :: nil))
    (Sset _s (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _mmap0 (Tfunction
                       (Tcons (tptr tvoid) (Tcons tuint (Tcons tint Tnil)))
                       (tptr tvoid) cc_default))
        ((Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
         (Econst_int (Int.repr 524288) tint) ::
         (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))
      (Sset _p (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tschar))))
    (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr tschar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      (Ssequence
        (Scall (Some _t'3)
          (Evar _list_from_block (Tfunction
                                   (Tcons tuint
                                     (Tcons (tptr tschar)
                                       (Tcons (tptr tvoid) Tnil)))
                                   (tptr tvoid) cc_default))
          ((Etempvar _s tuint) :: (Etempvar _p (tptr tschar)) ::
           (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
        (Sreturn (Some (Etempvar _t'3 (tptr tvoid))))))))
|}.

Definition f_malloc_small := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_nbytes, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tint) :: (_q, (tptr tvoid)) :: (_p, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _size2bin (Tfunction (Tcons tuint Tnil) tint cc_default))
      ((Etempvar _nbytes tuint) :: nil))
    (Sset _b (Etempvar _t'1 tint)))
  (Ssequence
    (Sset _p
      (Ederef
        (Ebinop Oadd (Evar _bin (tarray (tptr tvoid) 50)) (Etempvar _b tint)
          (tptr (tptr tvoid))) (tptr tvoid)))
    (Ssequence
      (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tvoid)) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _fill_bin (Tfunction (Tcons tint Tnil) (tptr tvoid)
                                cc_default)) ((Etempvar _b tint) :: nil))
            (Sset _p (Etempvar _t'2 (tptr tvoid))))
          (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tvoid)) tint)
            (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid))))
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _bin (tarray (tptr tvoid) 50))
                  (Etempvar _b tint) (tptr (tptr tvoid))) (tptr tvoid))
              (Etempvar _p (tptr tvoid)))))
        Sskip)
      (Ssequence
        (Sset _q
          (Ederef (Ecast (Etempvar _p (tptr tvoid)) (tptr (tptr tvoid)))
            (tptr tvoid)))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _bin (tarray (tptr tvoid) 50))
                (Etempvar _b tint) (tptr (tptr tvoid))) (tptr tvoid))
            (Etempvar _q (tptr tvoid)))
          (Sreturn (Some (Etempvar _p (tptr tvoid)))))))))
|}.

Definition f_malloc_large := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_nbytes, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tschar)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mmap0 (Tfunction
                     (Tcons (tptr tvoid) (Tcons tuint (Tcons tint Tnil)))
                     (tptr tvoid) cc_default))
      ((Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
       (Ebinop Oadd
         (Ebinop Oadd (Etempvar _nbytes tuint) (Econst_int (Int.repr 4) tint)
           tuint) (Econst_int (Int.repr 4) tint) tuint) ::
       (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) :: nil))
    (Sset _p (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr tschar))))
  (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr tschar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Ecast
              (Ebinop Oadd (Etempvar _p (tptr tschar))
                (Econst_int (Int.repr 4) tint) (tptr tschar)) (tptr tuint))
            (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
        (Etempvar _nbytes tuint))
      (Sreturn (Some (Ecast
                       (Ebinop Oadd
                         (Ebinop Oadd (Etempvar _p (tptr tschar))
                           (Econst_int (Int.repr 4) tint) (tptr tschar))
                         (Econst_int (Int.repr 4) tint) (tptr tschar))
                       (tptr tvoid)))))))
|}.

Definition f_free_small := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) :: (_s, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, tint) :: (_q, (tptr tvoid)) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _size2bin (Tfunction (Tcons tuint Tnil) tint cc_default))
      ((Etempvar _s tuint) :: nil))
    (Sset _b (Etempvar _t'1 tint)))
  (Ssequence
    (Sset _q
      (Ederef
        (Ebinop Oadd (Evar _bin (tarray (tptr tvoid) 50)) (Etempvar _b tint)
          (tptr (tptr tvoid))) (tptr tvoid)))
    (Ssequence
      (Sassign
        (Ederef (Ecast (Etempvar _p (tptr tvoid)) (tptr (tptr tvoid)))
          (tptr tvoid)) (Etempvar _q (tptr tvoid)))
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _bin (tarray (tptr tvoid) 50))
            (Etempvar _b tint) (tptr (tptr tvoid))) (tptr tvoid))
        (Etempvar _p (tptr tvoid))))))
|}.

Definition f_free_large := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) :: (_s, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _munmap (Tfunction (Tcons (tptr tvoid) (Tcons tuint Tnil)) tint
                  cc_default))
  ((Ebinop Osub (Ecast (Etempvar _p (tptr tvoid)) (tptr tschar))
     (Ebinop Oadd (Econst_int (Int.repr 4) tint)
       (Econst_int (Int.repr 4) tint) tint) (tptr tschar)) ::
   (Ebinop Oadd
     (Ebinop Oadd (Etempvar _s tuint) (Econst_int (Int.repr 4) tint) tuint)
     (Econst_int (Int.repr 4) tint) tuint) :: nil))
|}.

Definition f_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, tuint) :: (_t'1, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop One (Etempvar _p (tptr tvoid))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _p (tptr tvoid)) (tptr tuint))
            (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) (tptr tuint))
          tuint))
      (Sset _s (Ecast (Etempvar _t'2 tuint) tuint)))
    (Ssequence
      (Scall (Some _t'1)
        (Evar _bin2size (Tfunction (Tcons tint Tnil) tuint cc_default))
        ((Ebinop Osub (Econst_int (Int.repr 50) tint)
           (Econst_int (Int.repr 1) tint) tint) :: nil))
      (Sifthenelse (Ebinop Ole (Etempvar _s tuint) (Etempvar _t'1 tuint)
                     tint)
        (Scall None
          (Evar _free_small (Tfunction
                              (Tcons (tptr tvoid) (Tcons tuint Tnil)) tvoid
                              cc_default))
          ((Etempvar _p (tptr tvoid)) :: (Etempvar _s tuint) :: nil))
        (Scall None
          (Evar _free_large (Tfunction
                              (Tcons (tptr tvoid) (Tcons tuint Tnil)) tvoid
                              cc_default))
          ((Etempvar _p (tptr tvoid)) :: (Etempvar _s tuint) :: nil)))))
  Sskip)
|}.

Definition f_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_nbytes, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tuint) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'3)
    (Evar _bin2size (Tfunction (Tcons tint Tnil) tuint cc_default))
    ((Ebinop Osub (Econst_int (Int.repr 50) tint)
       (Econst_int (Int.repr 1) tint) tint) :: nil))
  (Sifthenelse (Ebinop Ogt (Etempvar _nbytes tuint) (Etempvar _t'3 tuint)
                 tint)
    (Ssequence
      (Scall (Some _t'1)
        (Evar _malloc_large (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                              cc_default)) ((Etempvar _nbytes tuint) :: nil))
      (Sreturn (Some (Etempvar _t'1 (tptr tvoid)))))
    (Ssequence
      (Scall (Some _t'2)
        (Evar _malloc_small (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                              cc_default)) ((Etempvar _nbytes tuint) :: nil))
      (Sreturn (Some (Etempvar _t'2 (tptr tvoid)))))))
|}.

Definition composites : list composite_definition :=
nil.

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
 (_mmap0,
   Gfun(External (EF_external "mmap0"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tint cc_default))
     (Tcons (tptr tvoid) (Tcons tuint (Tcons tint Tnil))) (tptr tvoid)
     cc_default)) ::
 (_munmap,
   Gfun(External (EF_external "munmap"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tint cc_default)) :: (_bin2size, Gfun(Internal f_bin2size)) ::
 (_size2bin, Gfun(Internal f_size2bin)) :: (_bin, Gvar v_bin) ::
 (_list_from_block, Gfun(Internal f_list_from_block)) ::
 (_pre_fill, Gfun(Internal f_pre_fill)) ::
 (_try_pre_fill, Gfun(Internal f_try_pre_fill)) ::
 (_fill_bin, Gfun(Internal f_fill_bin)) ::
 (_malloc_small, Gfun(Internal f_malloc_small)) ::
 (_malloc_large, Gfun(Internal f_malloc_large)) ::
 (_free_small, Gfun(Internal f_free_small)) ::
 (_free_large, Gfun(Internal f_free_large)) ::
 (_free, Gfun(Internal f_free)) :: (_malloc, Gfun(Internal f_malloc)) :: nil).

Definition public_idents : list ident :=
(_malloc :: _free :: _try_pre_fill :: _pre_fill :: _munmap :: _mmap0 ::
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


