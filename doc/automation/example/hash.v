From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition ___builtin_annot : ident := 13%positive.
Definition ___builtin_annot_intval : ident := 14%positive.
Definition ___builtin_bswap : ident := 7%positive.
Definition ___builtin_bswap16 : ident := 9%positive.
Definition ___builtin_bswap32 : ident := 8%positive.
Definition ___builtin_bswap64 : ident := 39%positive.
Definition ___builtin_clz : ident := 40%positive.
Definition ___builtin_clzl : ident := 41%positive.
Definition ___builtin_clzll : ident := 42%positive.
Definition ___builtin_ctz : ident := 43%positive.
Definition ___builtin_ctzl : ident := 44%positive.
Definition ___builtin_ctzll : ident := 45%positive.
Definition ___builtin_debug : ident := 57%positive.
Definition ___builtin_fabs : ident := 10%positive.
Definition ___builtin_fmadd : ident := 48%positive.
Definition ___builtin_fmax : ident := 46%positive.
Definition ___builtin_fmin : ident := 47%positive.
Definition ___builtin_fmsub : ident := 49%positive.
Definition ___builtin_fnmadd : ident := 50%positive.
Definition ___builtin_fnmsub : ident := 51%positive.
Definition ___builtin_fsqrt : ident := 11%positive.
Definition ___builtin_membar : ident := 15%positive.
Definition ___builtin_memcpy_aligned : ident := 12%positive.
Definition ___builtin_nop : ident := 56%positive.
Definition ___builtin_read16_reversed : ident := 52%positive.
Definition ___builtin_read32_reversed : ident := 53%positive.
Definition ___builtin_va_arg : ident := 17%positive.
Definition ___builtin_va_copy : ident := 18%positive.
Definition ___builtin_va_end : ident := 19%positive.
Definition ___builtin_va_start : ident := 16%positive.
Definition ___builtin_write16_reversed : ident := 54%positive.
Definition ___builtin_write32_reversed : ident := 55%positive.
Definition ___compcert_i64_dtos : ident := 24%positive.
Definition ___compcert_i64_dtou : ident := 25%positive.
Definition ___compcert_i64_sar : ident := 36%positive.
Definition ___compcert_i64_sdiv : ident := 30%positive.
Definition ___compcert_i64_shl : ident := 34%positive.
Definition ___compcert_i64_shr : ident := 35%positive.
Definition ___compcert_i64_smod : ident := 32%positive.
Definition ___compcert_i64_smulh : ident := 37%positive.
Definition ___compcert_i64_stod : ident := 26%positive.
Definition ___compcert_i64_stof : ident := 28%positive.
Definition ___compcert_i64_udiv : ident := 31%positive.
Definition ___compcert_i64_umod : ident := 33%positive.
Definition ___compcert_i64_umulh : ident := 38%positive.
Definition ___compcert_i64_utod : ident := 27%positive.
Definition ___compcert_i64_utof : ident := 29%positive.
Definition ___compcert_va_composite : ident := 23%positive.
Definition ___compcert_va_float64 : ident := 22%positive.
Definition ___compcert_va_int32 : ident := 20%positive.
Definition ___compcert_va_int64 : ident := 21%positive.
Definition _b : ident := 74%positive.
Definition _buckets : ident := 5%positive.
Definition _c : ident := 66%positive.
Definition _cell : ident := 3%positive.
Definition _copy_string : ident := 69%positive.
Definition _count : ident := 2%positive.
Definition _exit : ident := 59%positive.
Definition _get : ident := 75%positive.
Definition _h : ident := 73%positive.
Definition _hash : ident := 67%positive.
Definition _hashtable : ident := 6%positive.
Definition _i : ident := 65%positive.
Definition _incr : ident := 79%positive.
Definition _incr_list : ident := 78%positive.
Definition _incrx : ident := 80%positive.
Definition _key : ident := 1%positive.
Definition _main : ident := 81%positive.
Definition _malloc : ident := 58%positive.
Definition _n : ident := 64%positive.
Definition _new_cell : ident := 71%positive.
Definition _new_table : ident := 70%positive.
Definition _next : ident := 4%positive.
Definition _p : ident := 68%positive.
Definition _r : ident := 77%positive.
Definition _r0 : ident := 76%positive.
Definition _s : ident := 63%positive.
Definition _strcmp : ident := 62%positive.
Definition _strcpy : ident := 61%positive.
Definition _strlen : ident := 60%positive.
Definition _table : ident := 72%positive.
Definition _t'1 : ident := 82%positive.
Definition _t'2 : ident := 83%positive.
Definition _t'3 : ident := 84%positive.
Definition _t'4 : ident := 85%positive.
Definition _t'5 : ident := 86%positive.
Definition _t'6 : ident := 87%positive.

Definition f_hash := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tuint) :: (_i, tuint) :: (_c, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _n (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _c
        (Ederef
          (Ebinop Oadd (Etempvar _s (tptr tschar)) (Etempvar _i tuint)
            (tptr tschar)) tschar))
      (Ssequence
        (Swhile
          (Etempvar _c tint)
          (Ssequence
            (Sset _n
              (Ebinop Oadd
                (Ebinop Omul (Etempvar _n tuint)
                  (Econst_int (Int.repr 65599) tuint) tuint)
                (Ecast (Etempvar _c tint) tuint) tuint))
            (Ssequence
              (Sset _i
                (Ebinop Oadd (Etempvar _i tuint)
                  (Econst_int (Int.repr 1) tint) tuint))
              (Sset _c
                (Ederef
                  (Ebinop Oadd (Etempvar _s (tptr tschar))
                    (Etempvar _i tuint) (tptr tschar)) tschar)))))
        (Sreturn (Some (Etempvar _n tuint)))))))
|}.

Definition f_copy_string := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_n, tint) :: (_p, (tptr tschar)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _strlen (Tfunction (Tcons (tptr tschar) Tnil) tuint cc_default))
      ((Etempvar _s (tptr tschar)) :: nil))
    (Sset _n
      (Ebinop Oadd (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tint)
        tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
        ((Etempvar _n tint) :: nil))
      (Sset _p (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tschar)) tint)
        (Scall None
          (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        Sskip)
      (Ssequence
        (Scall None
          (Evar _strcpy (Tfunction
                          (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil))
                          (tptr tschar) cc_default))
          ((Etempvar _p (tptr tschar)) :: (Etempvar _s (tptr tschar)) :: nil))
        (Sreturn (Some (Etempvar _p (tptr tschar))))))))
|}.

Definition f_new_table := {|
  fn_return := (tptr (Tstruct _hashtable noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_p, (tptr (Tstruct _hashtable noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _hashtable noattr) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _hashtable noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _p (tptr (Tstruct _hashtable noattr))) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 109) tint) tint)
              Sskip
              Sbreak)
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _hashtable noattr)))
                      (Tstruct _hashtable noattr)) _buckets
                    (tarray (tptr (Tstruct _cell noattr)) 109))
                  (Etempvar _i tint) (tptr (tptr (Tstruct _cell noattr))))
                (tptr (Tstruct _cell noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Sreturn (Some (Etempvar _p (tptr (Tstruct _hashtable noattr))))))))
|}.

Definition f_new_cell := {|
  fn_return := (tptr (Tstruct _cell noattr));
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tschar)) :: (_count, tint) ::
                (_next, (tptr (Tstruct _cell noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _cell noattr))) ::
               (_t'2, (tptr tschar)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _cell noattr) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _cell noattr)))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr (Tstruct _cell noattr)))
                   tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _copy_string (Tfunction (Tcons (tptr tschar) Tnil)
                               (tptr tschar) cc_default))
          ((Etempvar _key (tptr tschar)) :: nil))
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
              (Tstruct _cell noattr)) _key (tptr tschar))
          (Etempvar _t'2 (tptr tschar))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
              (Tstruct _cell noattr)) _count tuint) (Etempvar _count tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                (Tstruct _cell noattr)) _next (tptr (Tstruct _cell noattr)))
            (Etempvar _next (tptr (Tstruct _cell noattr))))
          (Sreturn (Some (Etempvar _p (tptr (Tstruct _cell noattr))))))))))
|}.

Definition f_get := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _hashtable noattr))) ::
                (_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, tuint) :: (_b, tuint) ::
               (_p, (tptr (Tstruct _cell noattr))) :: (_t'2, tint) ::
               (_t'1, tuint) :: (_t'4, (tptr tschar)) :: (_t'3, tuint) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _hash (Tfunction (Tcons (tptr tschar) Tnil) tuint cc_default))
      ((Etempvar _s (tptr tschar)) :: nil))
    (Sset _h (Etempvar _t'1 tuint)))
  (Ssequence
    (Sset _b
      (Ebinop Omod (Etempvar _h tuint) (Econst_int (Int.repr 109) tint)
        tuint))
    (Ssequence
      (Sset _p
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _table (tptr (Tstruct _hashtable noattr)))
                (Tstruct _hashtable noattr)) _buckets
              (tarray (tptr (Tstruct _cell noattr)) 109)) (Etempvar _b tuint)
            (tptr (tptr (Tstruct _cell noattr))))
          (tptr (Tstruct _cell noattr))))
      (Ssequence
        (Swhile
          (Etempvar _p (tptr (Tstruct _cell noattr)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                      (Tstruct _cell noattr)) _key (tptr tschar)))
                (Scall (Some _t'2)
                  (Evar _strcmp (Tfunction
                                  (Tcons (tptr tschar)
                                    (Tcons (tptr tschar) Tnil)) tint
                                  cc_default))
                  ((Etempvar _t'4 (tptr tschar)) ::
                   (Etempvar _s (tptr tschar)) :: nil)))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                        (Tstruct _cell noattr)) _count tuint))
                  (Sreturn (Some (Etempvar _t'3 tuint))))
                Sskip))
            (Sset _p
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                  (Tstruct _cell noattr)) _next
                (tptr (Tstruct _cell noattr))))))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_incr_list := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r0, (tptr (tptr (Tstruct _cell noattr)))) ::
                (_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _cell noattr))) ::
               (_r, (tptr (tptr (Tstruct _cell noattr)))) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _cell noattr))) ::
               (_t'4, (tptr tschar)) :: (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _r (Etempvar _r0 (tptr (tptr (Tstruct _cell noattr)))))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _p
          (Ederef (Etempvar _r (tptr (tptr (Tstruct _cell noattr))))
            (tptr (Tstruct _cell noattr))))
        (Ssequence
          (Sifthenelse (Eunop Onotbool
                         (Etempvar _p (tptr (Tstruct _cell noattr))) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _new_cell (Tfunction
                                    (Tcons (tptr tschar)
                                      (Tcons tint
                                        (Tcons (tptr (Tstruct _cell noattr))
                                          Tnil)))
                                    (tptr (Tstruct _cell noattr)) cc_default))
                  ((Etempvar _s (tptr tschar)) ::
                   (Econst_int (Int.repr 1) tint) ::
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
                   nil))
                (Sassign
                  (Ederef (Etempvar _r (tptr (tptr (Tstruct _cell noattr))))
                    (tptr (Tstruct _cell noattr)))
                  (Etempvar _t'1 (tptr (Tstruct _cell noattr)))))
              (Sreturn None))
            Sskip)
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                    (Tstruct _cell noattr)) _key (tptr tschar)))
              (Scall (Some _t'2)
                (Evar _strcmp (Tfunction
                                (Tcons (tptr tschar)
                                  (Tcons (tptr tschar) Tnil)) tint
                                cc_default))
                ((Etempvar _t'4 (tptr tschar)) ::
                 (Etempvar _s (tptr tschar)) :: nil)))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                        (Tstruct _cell noattr)) _count tuint))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                        (Tstruct _cell noattr)) _count tuint)
                    (Ebinop Oadd (Etempvar _t'3 tuint)
                      (Econst_int (Int.repr 1) tint) tuint)))
                (Sreturn None))
              Sskip)))))
    (Sset _r
      (Eaddrof
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
            (Tstruct _cell noattr)) _next (tptr (Tstruct _cell noattr)))
        (tptr (tptr (Tstruct _cell noattr)))))))
|}.

Definition f_incr := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _hashtable noattr))) ::
                (_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, tuint) :: (_b, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _hash (Tfunction (Tcons (tptr tschar) Tnil) tuint cc_default))
      ((Etempvar _s (tptr tschar)) :: nil))
    (Sset _h (Etempvar _t'1 tuint)))
  (Ssequence
    (Sset _b
      (Ebinop Omod (Etempvar _h tuint) (Econst_int (Int.repr 109) tint)
        tuint))
    (Scall None
      (Evar _incr_list (Tfunction
                         (Tcons (tptr (tptr (Tstruct _cell noattr)))
                           (Tcons (tptr tschar) Tnil)) tvoid cc_default))
      ((Ebinop Oadd
         (Efield
           (Ederef (Etempvar _table (tptr (Tstruct _hashtable noattr)))
             (Tstruct _hashtable noattr)) _buckets
           (tarray (tptr (Tstruct _cell noattr)) 109)) (Etempvar _b tuint)
         (tptr (tptr (Tstruct _cell noattr)))) ::
       (Etempvar _s (tptr tschar)) :: nil))))
|}.

Definition f_incrx := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _hashtable noattr))) ::
                (_s, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, tuint) :: (_b, tuint) ::
               (_p, (tptr (Tstruct _cell noattr))) ::
               (_t'3, (tptr (Tstruct _cell noattr))) :: (_t'2, tint) ::
               (_t'1, tuint) :: (_t'6, (tptr tschar)) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _cell noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _hash (Tfunction (Tcons (tptr tschar) Tnil) tuint cc_default))
      ((Etempvar _s (tptr tschar)) :: nil))
    (Sset _h (Etempvar _t'1 tuint)))
  (Ssequence
    (Sset _b
      (Ebinop Omod (Etempvar _h tuint) (Econst_int (Int.repr 109) tint)
        tuint))
    (Ssequence
      (Sset _p
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _table (tptr (Tstruct _hashtable noattr)))
                (Tstruct _hashtable noattr)) _buckets
              (tarray (tptr (Tstruct _cell noattr)) 109)) (Etempvar _b tuint)
            (tptr (tptr (Tstruct _cell noattr))))
          (tptr (Tstruct _cell noattr))))
      (Ssequence
        (Swhile
          (Etempvar _p (tptr (Tstruct _cell noattr)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                      (Tstruct _cell noattr)) _key (tptr tschar)))
                (Scall (Some _t'2)
                  (Evar _strcmp (Tfunction
                                  (Tcons (tptr tschar)
                                    (Tcons (tptr tschar) Tnil)) tint
                                  cc_default))
                  ((Etempvar _t'6 (tptr tschar)) ::
                   (Etempvar _s (tptr tschar)) :: nil)))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint)
                             (Econst_int (Int.repr 0) tint) tint)
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                          (Tstruct _cell noattr)) _count tuint))
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                          (Tstruct _cell noattr)) _count tuint)
                      (Ebinop Oadd (Etempvar _t'5 tuint)
                        (Econst_int (Int.repr 1) tint) tuint)))
                  (Sreturn None))
                Sskip))
            (Sset _p
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _cell noattr)))
                  (Tstruct _cell noattr)) _next
                (tptr (Tstruct _cell noattr))))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _table (tptr (Tstruct _hashtable noattr)))
                      (Tstruct _hashtable noattr)) _buckets
                    (tarray (tptr (Tstruct _cell noattr)) 109))
                  (Etempvar _b tuint) (tptr (tptr (Tstruct _cell noattr))))
                (tptr (Tstruct _cell noattr))))
            (Scall (Some _t'3)
              (Evar _new_cell (Tfunction
                                (Tcons (tptr tschar)
                                  (Tcons tint
                                    (Tcons (tptr (Tstruct _cell noattr))
                                      Tnil))) (tptr (Tstruct _cell noattr))
                                cc_default))
              ((Etempvar _s (tptr tschar)) ::
               (Econst_int (Int.repr 1) tint) ::
               (Etempvar _t'4 (tptr (Tstruct _cell noattr))) :: nil)))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _table (tptr (Tstruct _hashtable noattr)))
                    (Tstruct _hashtable noattr)) _buckets
                  (tarray (tptr (Tstruct _cell noattr)) 109))
                (Etempvar _b tuint) (tptr (tptr (Tstruct _cell noattr))))
              (tptr (Tstruct _cell noattr)))
            (Etempvar _t'3 (tptr (Tstruct _cell noattr)))))))))
|}.

Definition composites : list composite_definition :=
(Composite _cell Struct
   ((_key, (tptr tschar)) :: (_count, tuint) ::
    (_next, (tptr (Tstruct _cell noattr))) :: nil)
   noattr ::
 Composite _hashtable Struct
   ((_buckets, (tarray (tptr (Tstruct _cell noattr)) 109)) :: nil)
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
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_strlen,
   Gfun(External (EF_external "strlen"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tschar) Tnil) tuint cc_default)) ::
 (_strcpy,
   Gfun(External (EF_external "strcpy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil)) (tptr tschar)
     cc_default)) ::
 (_strcmp,
   Gfun(External (EF_external "strcmp"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tschar) (Tcons (tptr tschar) Tnil)) tint cc_default)) ::
 (_hash, Gfun(Internal f_hash)) ::
 (_copy_string, Gfun(Internal f_copy_string)) ::
 (_new_table, Gfun(Internal f_new_table)) ::
 (_new_cell, Gfun(Internal f_new_cell)) :: (_get, Gfun(Internal f_get)) ::
 (_incr_list, Gfun(Internal f_incr_list)) ::
 (_incr, Gfun(Internal f_incr)) :: (_incrx, Gfun(Internal f_incrx)) :: nil).

Definition public_idents : list ident :=
(_incrx :: _incr :: _incr_list :: _get :: _new_cell :: _new_table ::
 _copy_string :: _hash :: _strcmp :: _strcpy :: _strlen :: _exit ::
 _malloc :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap64 ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fsqrt :: ___builtin_fabs ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


