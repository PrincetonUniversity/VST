From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.5"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "progs/int_or_ptr.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 10%positive.
Definition ___builtin_annot_intval : ident := 11%positive.
Definition ___builtin_bswap : ident := 4%positive.
Definition ___builtin_bswap16 : ident := 6%positive.
Definition ___builtin_bswap32 : ident := 5%positive.
Definition ___builtin_bswap64 : ident := 36%positive.
Definition ___builtin_clz : ident := 37%positive.
Definition ___builtin_clzl : ident := 38%positive.
Definition ___builtin_clzll : ident := 39%positive.
Definition ___builtin_ctz : ident := 40%positive.
Definition ___builtin_ctzl : ident := 41%positive.
Definition ___builtin_ctzll : ident := 42%positive.
Definition ___builtin_debug : ident := 54%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_fmadd : ident := 45%positive.
Definition ___builtin_fmax : ident := 43%positive.
Definition ___builtin_fmin : ident := 44%positive.
Definition ___builtin_fmsub : ident := 46%positive.
Definition ___builtin_fnmadd : ident := 47%positive.
Definition ___builtin_fnmsub : ident := 48%positive.
Definition ___builtin_fsqrt : ident := 8%positive.
Definition ___builtin_membar : ident := 12%positive.
Definition ___builtin_memcpy_aligned : ident := 9%positive.
Definition ___builtin_nop : ident := 53%positive.
Definition ___builtin_read16_reversed : ident := 49%positive.
Definition ___builtin_read32_reversed : ident := 50%positive.
Definition ___builtin_va_arg : ident := 14%positive.
Definition ___builtin_va_copy : ident := 15%positive.
Definition ___builtin_va_end : ident := 16%positive.
Definition ___builtin_va_start : ident := 13%positive.
Definition ___builtin_write16_reversed : ident := 51%positive.
Definition ___builtin_write32_reversed : ident := 52%positive.
Definition ___compcert_i64_dtos : ident := 21%positive.
Definition ___compcert_i64_dtou : ident := 22%positive.
Definition ___compcert_i64_sar : ident := 33%positive.
Definition ___compcert_i64_sdiv : ident := 27%positive.
Definition ___compcert_i64_shl : ident := 31%positive.
Definition ___compcert_i64_shr : ident := 32%positive.
Definition ___compcert_i64_smod : ident := 29%positive.
Definition ___compcert_i64_smulh : ident := 34%positive.
Definition ___compcert_i64_stod : ident := 23%positive.
Definition ___compcert_i64_stof : ident := 25%positive.
Definition ___compcert_i64_udiv : ident := 28%positive.
Definition ___compcert_i64_umod : ident := 30%positive.
Definition ___compcert_i64_umulh : ident := 35%positive.
Definition ___compcert_i64_utod : ident := 24%positive.
Definition ___compcert_i64_utof : ident := 26%positive.
Definition ___compcert_va_composite : ident := 20%positive.
Definition ___compcert_va_float64 : ident := 19%positive.
Definition ___compcert_va_int32 : ident := 17%positive.
Definition ___compcert_va_int64 : ident := 18%positive.
Definition _a : ident := 78%positive.
Definition _arena : ident := 64%positive.
Definition _b : ident := 79%positive.
Definition _copytree : ident := 74%positive.
Definition _depth : ident := 67%positive.
Definition _exit : ident := 56%positive.
Definition _i : ident := 75%positive.
Definition _int_or_ptr_to_int : ident := 59%positive.
Definition _int_or_ptr_to_ptr : ident := 60%positive.
Definition _int_to_int_or_ptr : ident := 61%positive.
Definition _leaf : ident := 63%positive.
Definition _left : ident := 1%positive.
Definition _main : ident := 81%positive.
Definition _makenode : ident := 66%positive.
Definition _maketree : ident := 71%positive.
Definition _next : ident := 65%positive.
Definition _p : ident := 69%positive.
Definition _print : ident := 80%positive.
Definition _print_int : ident := 77%positive.
Definition _print_intx : ident := 76%positive.
Definition _ptr_to_int_or_ptr : ident := 62%positive.
Definition _putchar : ident := 55%positive.
Definition _q : ident := 70%positive.
Definition _r : ident := 68%positive.
Definition _right : ident := 2%positive.
Definition _s : ident := 73%positive.
Definition _t : ident := 72%positive.
Definition _test_int_or_ptr : ident := 58%positive.
Definition _tree : ident := 3%positive.
Definition _x : ident := 57%positive.
Definition _t'1 : ident := 82%positive.
Definition _t'2 : ident := 83%positive.
Definition _t'3 : ident := 84%positive.
Definition _t'4 : ident := 85%positive.
Definition _t'5 : ident := 86%positive.
Definition _t'6 : ident := 87%positive.
Definition _t'7 : ident := 88%positive.
Definition _t'8 : ident := 89%positive.

Definition f_test_int_or_ptr := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 2%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand
                   (Ecast (Etempvar _x (talignas 2%N (tptr tvoid))) tuint)
                   (Econst_int (Int.repr 1) tint) tuint) tint)))
|}.

Definition f_int_or_ptr_to_int := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 2%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x (talignas 2%N (tptr tvoid))) tuint)))
|}.

Definition f_int_or_ptr_to_ptr := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_x, (talignas 2%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x (talignas 2%N (tptr tvoid))) (tptr tvoid))))
|}.

Definition f_int_to_int_or_ptr := {|
  fn_return := (talignas 2%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_x, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x tuint) (talignas 2%N (tptr tvoid)))))
|}.

Definition f_ptr_to_int_or_ptr := {|
  fn_return := (talignas 2%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Etempvar _x (tptr tvoid)) (talignas 2%N (tptr tvoid)))))
|}.

Definition v_leaf := {|
  gvar_info := tint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_arena := {|
  gvar_info := (tarray (Tstruct _tree noattr) 1000);
  gvar_init := (Init_space 8000 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_next := {|
  gvar_info := (tptr (Tstruct _tree noattr));
  gvar_init := (Init_addrof _arena (Ptrofs.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_makenode := {|
  fn_return := (tptr (Tstruct _tree noattr));
  fn_callconv := cc_default;
  fn_params := ((_left, (talignas 2%N (tptr tvoid))) ::
                (_right, (talignas 2%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _tree noattr))) ::
               (_t'4, (tptr (Tstruct _tree noattr))) ::
               (_t'3, (tptr (Tstruct _tree noattr))) ::
               (_t'2, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2 (Evar _next (tptr (Tstruct _tree noattr))))
  (Sifthenelse (Ebinop Olt (Etempvar _t'2 (tptr (Tstruct _tree noattr)))
                 (Ebinop Osub
                   (Ebinop Oadd
                     (Evar _arena (tarray (Tstruct _tree noattr) 1000))
                     (Econst_int (Int.repr 1000) tint)
                     (tptr (Tstruct _tree noattr)))
                   (Econst_int (Int.repr 1) tint)
                   (tptr (Tstruct _tree noattr))) tint)
    (Ssequence
      (Ssequence
        (Sset _t'4 (Evar _next (tptr (Tstruct _tree noattr))))
        (Sassign
          (Efield
            (Ederef (Etempvar _t'4 (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _left (talignas 2%N (tptr tvoid)))
          (Etempvar _left (talignas 2%N (tptr tvoid)))))
      (Ssequence
        (Ssequence
          (Sset _t'3 (Evar _next (tptr (Tstruct _tree noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _t'3 (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _right (talignas 2%N (tptr tvoid)))
            (Etempvar _right (talignas 2%N (tptr tvoid)))))
        (Ssequence
          (Ssequence
            (Sset _t'1 (Evar _next (tptr (Tstruct _tree noattr))))
            (Sassign (Evar _next (tptr (Tstruct _tree noattr)))
              (Ebinop Oadd (Etempvar _t'1 (tptr (Tstruct _tree noattr)))
                (Econst_int (Int.repr 1) tint) (tptr (Tstruct _tree noattr)))))
          (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _tree noattr))))))))
    (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
      ((Econst_int (Int.repr 1) tint) :: nil))))
|}.

Definition f_maketree := {|
  fn_return := (talignas 2%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_depth, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, (talignas 2%N (tptr tvoid))) ::
               (_p, (talignas 2%N (tptr tvoid))) ::
               (_q, (talignas 2%N (tptr tvoid))) ::
               (_t'6, (talignas 2%N (tptr tvoid))) ::
               (_t'5, (tptr (Tstruct _tree noattr))) ::
               (_t'4, (talignas 2%N (tptr tvoid))) ::
               (_t'3, (talignas 2%N (tptr tvoid))) ::
               (_t'2, (talignas 2%N (tptr tvoid))) :: (_t'1, tint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _depth tint)
               (Econst_int (Int.repr 0) tint) tint)
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'1 (Evar _leaf tint))
          (Sassign (Evar _leaf tint)
            (Ebinop Oadd (Etempvar _t'1 tint) (Econst_int (Int.repr 1) tint)
              tint)))
        (Scall (Some _t'2)
          (Evar _int_to_int_or_ptr (Tfunction (Tcons tuint Tnil)
                                     (talignas 2%N (tptr tvoid)) cc_default))
          ((Ebinop Oor
             (Ebinop Oshl (Etempvar _t'1 tint) (Econst_int (Int.repr 1) tint)
               tint) (Econst_int (Int.repr 1) tint) tint) :: nil)))
      (Sset _r (Etempvar _t'2 (talignas 2%N (tptr tvoid)))))
    (Sreturn (Some (Etempvar _r (talignas 2%N (tptr tvoid))))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'3)
        (Evar _maketree (Tfunction (Tcons tint Tnil)
                          (talignas 2%N (tptr tvoid)) cc_default))
        ((Ebinop Osub (Etempvar _depth tint) (Econst_int (Int.repr 1) tint)
           tint) :: nil))
      (Sset _p (Etempvar _t'3 (talignas 2%N (tptr tvoid)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'4)
          (Evar _maketree (Tfunction (Tcons tint Tnil)
                            (talignas 2%N (tptr tvoid)) cc_default))
          ((Ebinop Osub (Etempvar _depth tint) (Econst_int (Int.repr 1) tint)
             tint) :: nil))
        (Sset _q (Etempvar _t'4 (talignas 2%N (tptr tvoid)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'5)
            (Evar _makenode (Tfunction
                              (Tcons (talignas 2%N (tptr tvoid))
                                (Tcons (talignas 2%N (tptr tvoid)) Tnil))
                              (tptr (Tstruct _tree noattr)) cc_default))
            ((Etempvar _p (talignas 2%N (tptr tvoid))) ::
             (Etempvar _q (talignas 2%N (tptr tvoid))) :: nil))
          (Scall (Some _t'6)
            (Evar _ptr_to_int_or_ptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                       (talignas 2%N (tptr tvoid))
                                       cc_default))
            ((Etempvar _t'5 (tptr (Tstruct _tree noattr))) :: nil)))
        (Sreturn (Some (Etempvar _t'6 (talignas 2%N (tptr tvoid)))))))))
|}.

Definition f_copytree := {|
  fn_return := (talignas 2%N (tptr tvoid));
  fn_callconv := cc_default;
  fn_params := ((_t, (talignas 2%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (talignas 2%N (tptr tvoid))) ::
               (_q, (talignas 2%N (tptr tvoid))) ::
               (_s, (tptr (Tstruct _tree noattr))) :: (_t'6, tint) ::
               (_t'5, (talignas 2%N (tptr tvoid))) ::
               (_t'4, (tptr (Tstruct _tree noattr))) ::
               (_t'3, (talignas 2%N (tptr tvoid))) ::
               (_t'2, (talignas 2%N (tptr tvoid))) :: (_t'1, (tptr tvoid)) ::
               (_t'8, (talignas 2%N (tptr tvoid))) ::
               (_t'7, (talignas 2%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'6)
    (Evar _test_int_or_ptr (Tfunction
                             (Tcons (talignas 2%N (tptr tvoid)) Tnil) tint
                             cc_default))
    ((Etempvar _t (talignas 2%N (tptr tvoid))) :: nil))
  (Sifthenelse (Etempvar _t'6 tint)
    (Sreturn (Some (Etempvar _t (talignas 2%N (tptr tvoid)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _int_or_ptr_to_ptr (Tfunction
                                     (Tcons (talignas 2%N (tptr tvoid)) Tnil)
                                     (tptr tvoid) cc_default))
          ((Etempvar _t (talignas 2%N (tptr tvoid))) :: nil))
        (Sset _s
          (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _tree noattr)))))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _left (talignas 2%N (tptr tvoid))))
            (Scall (Some _t'2)
              (Evar _copytree (Tfunction
                                (Tcons (talignas 2%N (tptr tvoid)) Tnil)
                                (talignas 2%N (tptr tvoid)) cc_default))
              ((Etempvar _t'8 (talignas 2%N (tptr tvoid))) :: nil)))
          (Sset _p (Etempvar _t'2 (talignas 2%N (tptr tvoid)))))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _right
                  (talignas 2%N (tptr tvoid))))
              (Scall (Some _t'3)
                (Evar _copytree (Tfunction
                                  (Tcons (talignas 2%N (tptr tvoid)) Tnil)
                                  (talignas 2%N (tptr tvoid)) cc_default))
                ((Etempvar _t'7 (talignas 2%N (tptr tvoid))) :: nil)))
            (Sset _q (Etempvar _t'3 (talignas 2%N (tptr tvoid)))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _makenode (Tfunction
                                  (Tcons (talignas 2%N (tptr tvoid))
                                    (Tcons (talignas 2%N (tptr tvoid)) Tnil))
                                  (tptr (Tstruct _tree noattr)) cc_default))
                ((Etempvar _p (talignas 2%N (tptr tvoid))) ::
                 (Etempvar _q (talignas 2%N (tptr tvoid))) :: nil))
              (Scall (Some _t'5)
                (Evar _ptr_to_int_or_ptr (Tfunction (Tcons (tptr tvoid) Tnil)
                                           (talignas 2%N (tptr tvoid))
                                           cc_default))
                ((Etempvar _t'4 (tptr (Tstruct _tree noattr))) :: nil)))
            (Sreturn (Some (Etempvar _t'5 (talignas 2%N (tptr tvoid)))))))))))
|}.

Definition f_print_intx := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_i, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Ogt (Etempvar _i tuint) (Econst_int (Int.repr 0) tint)
               tint)
  (Ssequence
    (Scall None
      (Evar _print_intx (Tfunction (Tcons tuint Tnil) tvoid cc_default))
      ((Ebinop Odiv (Etempvar _i tuint) (Econst_int (Int.repr 10) tint)
         tuint) :: nil))
    (Scall None (Evar _putchar (Tfunction (Tcons tint Tnil) tint cc_default))
      ((Ebinop Oadd (Econst_int (Int.repr 48) tint)
         (Ebinop Omod (Etempvar _i tuint) (Econst_int (Int.repr 10) tint)
           tuint) tuint) :: nil)))
  Sskip)
|}.

Definition f_print_int := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_i, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _i tuint) (Econst_int (Int.repr 0) tint)
               tint)
  (Scall None (Evar _putchar (Tfunction (Tcons tint Tnil) tint cc_default))
    ((Econst_int (Int.repr 48) tint) :: nil))
  (Scall None
    (Evar _print_intx (Tfunction (Tcons tuint Tnil) tvoid cc_default))
    ((Etempvar _i tuint) :: nil)))
|}.

Definition f_print := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (talignas 2%N (tptr tvoid))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_q, (tptr (Tstruct _tree noattr))) ::
               (_a, (talignas 2%N (tptr tvoid))) ::
               (_b, (talignas 2%N (tptr tvoid))) :: (_t'3, tint) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'3)
    (Evar _test_int_or_ptr (Tfunction
                             (Tcons (talignas 2%N (tptr tvoid)) Tnil) tint
                             cc_default))
    ((Etempvar _p (talignas 2%N (tptr tvoid))) :: nil))
  (Sifthenelse (Etempvar _t'3 tint)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _int_or_ptr_to_int (Tfunction
                                     (Tcons (talignas 2%N (tptr tvoid)) Tnil)
                                     tuint cc_default))
          ((Etempvar _p (talignas 2%N (tptr tvoid))) :: nil))
        (Sset _i (Etempvar _t'1 tuint)))
      (Scall None
        (Evar _print_int (Tfunction (Tcons tuint Tnil) tvoid cc_default))
        ((Ebinop Oshr (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
           tuint) :: nil)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _int_or_ptr_to_ptr (Tfunction
                                     (Tcons (talignas 2%N (tptr tvoid)) Tnil)
                                     (tptr tvoid) cc_default))
          ((Etempvar _p (talignas 2%N (tptr tvoid))) :: nil))
        (Sset _q
          (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr (Tstruct _tree noattr)))))
      (Ssequence
        (Sset _a
          (Efield
            (Ederef (Etempvar _q (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _left (talignas 2%N (tptr tvoid))))
        (Ssequence
          (Sset _b
            (Efield
              (Ederef (Etempvar _q (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _right (talignas 2%N (tptr tvoid))))
          (Ssequence
            (Scall None
              (Evar _putchar (Tfunction (Tcons tint Tnil) tint cc_default))
              ((Econst_int (Int.repr 40) tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _print (Tfunction
                               (Tcons (talignas 2%N (tptr tvoid)) Tnil) tvoid
                               cc_default))
                ((Etempvar _a (talignas 2%N (tptr tvoid))) :: nil))
              (Ssequence
                (Scall None
                  (Evar _putchar (Tfunction (Tcons tint Tnil) tint
                                   cc_default))
                  ((Econst_int (Int.repr 44) tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _print (Tfunction
                                   (Tcons (talignas 2%N (tptr tvoid)) Tnil)
                                   tvoid cc_default))
                    ((Etempvar _b (talignas 2%N (tptr tvoid))) :: nil))
                  (Scall None
                    (Evar _putchar (Tfunction (Tcons tint Tnil) tint
                                     cc_default))
                    ((Econst_int (Int.repr 41) tint) :: nil)))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (talignas 2%N (tptr tvoid))) ::
               (_t'2, (talignas 2%N (tptr tvoid))) ::
               (_t'1, (talignas 2%N (tptr tvoid))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _maketree (Tfunction (Tcons tint Tnil)
                          (talignas 2%N (tptr tvoid)) cc_default))
        ((Econst_int (Int.repr 3) tint) :: nil))
      (Sset _p (Etempvar _t'1 (talignas 2%N (tptr tvoid)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _copytree (Tfunction (Tcons (talignas 2%N (tptr tvoid)) Tnil)
                            (talignas 2%N (tptr tvoid)) cc_default))
          ((Etempvar _p (talignas 2%N (tptr tvoid))) :: nil))
        (Sset _p (Etempvar _t'2 (talignas 2%N (tptr tvoid)))))
      (Ssequence
        (Scall None
          (Evar _print (Tfunction (Tcons (talignas 2%N (tptr tvoid)) Tnil)
                         tvoid cc_default))
          ((Etempvar _p (talignas 2%N (tptr tvoid))) :: nil))
        (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _tree Struct
   ((_left, (talignas 2%N (tptr tvoid))) ::
    (_right, (talignas 2%N (tptr tvoid))) :: nil)
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
 (_putchar,
   Gfun(External (EF_external "putchar"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_test_int_or_ptr, Gfun(Internal f_test_int_or_ptr)) ::
 (_int_or_ptr_to_int, Gfun(Internal f_int_or_ptr_to_int)) ::
 (_int_or_ptr_to_ptr, Gfun(Internal f_int_or_ptr_to_ptr)) ::
 (_int_to_int_or_ptr, Gfun(Internal f_int_to_int_or_ptr)) ::
 (_ptr_to_int_or_ptr, Gfun(Internal f_ptr_to_int_or_ptr)) ::
 (_leaf, Gvar v_leaf) :: (_arena, Gvar v_arena) :: (_next, Gvar v_next) ::
 (_makenode, Gfun(Internal f_makenode)) ::
 (_maketree, Gfun(Internal f_maketree)) ::
 (_copytree, Gfun(Internal f_copytree)) ::
 (_print_intx, Gfun(Internal f_print_intx)) ::
 (_print_int, Gfun(Internal f_print_int)) ::
 (_print, Gfun(Internal f_print)) :: (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _print :: _print_int :: _print_intx :: _copytree :: _maketree ::
 _makenode :: _next :: _arena :: _leaf :: _ptr_to_int_or_ptr ::
 _int_to_int_or_ptr :: _int_or_ptr_to_ptr :: _int_or_ptr_to_int ::
 _test_int_or_ptr :: _exit :: _putchar :: ___builtin_debug ::
 ___builtin_nop :: ___builtin_write32_reversed ::
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


