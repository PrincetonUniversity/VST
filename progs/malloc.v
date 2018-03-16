
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition ___builtin_annot : ident := 3%positive.
Definition ___builtin_annot_intval : ident := 4%positive.
Definition ___builtin_bswap : ident := 29%positive.
Definition ___builtin_bswap16 : ident := 32%positive.
Definition ___builtin_bswap32 : ident := 31%positive.
Definition ___builtin_bswap64 : ident := 30%positive.
Definition ___builtin_clz : ident := 33%positive.
Definition ___builtin_clzl : ident := 34%positive.
Definition ___builtin_clzll : ident := 35%positive.
Definition ___builtin_ctz : ident := 36%positive.
Definition ___builtin_ctzl : ident := 37%positive.
Definition ___builtin_ctzll : ident := 38%positive.
Definition ___builtin_debug : ident := 51%positive.
Definition ___builtin_fabs : ident := 1%positive.
Definition ___builtin_fmadd : ident := 42%positive.
Definition ___builtin_fmax : ident := 40%positive.
Definition ___builtin_fmin : ident := 41%positive.
Definition ___builtin_fmsub : ident := 43%positive.
Definition ___builtin_fnmadd : ident := 44%positive.
Definition ___builtin_fnmsub : ident := 45%positive.
Definition ___builtin_fsqrt : ident := 39%positive.
Definition ___builtin_membar : ident := 5%positive.
Definition ___builtin_memcpy_aligned : ident := 2%positive.
Definition ___builtin_nop : ident := 50%positive.
Definition ___builtin_read16_reversed : ident := 46%positive.
Definition ___builtin_read32_reversed : ident := 47%positive.
Definition ___builtin_va_arg : ident := 7%positive.
Definition ___builtin_va_copy : ident := 8%positive.
Definition ___builtin_va_end : ident := 9%positive.
Definition ___builtin_va_start : ident := 6%positive.
Definition ___builtin_write16_reversed : ident := 48%positive.
Definition ___builtin_write32_reversed : ident := 49%positive.
Definition ___compcert_va_composite : ident := 13%positive.
Definition ___compcert_va_float64 : ident := 12%positive.
Definition ___compcert_va_int32 : ident := 10%positive.
Definition ___compcert_va_int64 : ident := 11%positive.
Definition ___i64_dtos : ident := 14%positive.
Definition ___i64_dtou : ident := 15%positive.
Definition ___i64_sar : ident := 26%positive.
Definition ___i64_sdiv : ident := 20%positive.
Definition ___i64_shl : ident := 24%positive.
Definition ___i64_shr : ident := 25%positive.
Definition ___i64_smod : ident := 22%positive.
Definition ___i64_smulh : ident := 27%positive.
Definition ___i64_stod : ident := 16%positive.
Definition ___i64_stof : ident := 18%positive.
Definition ___i64_udiv : ident := 21%positive.
Definition ___i64_umod : ident := 23%positive.
Definition ___i64_umulh : ident := 28%positive.
Definition ___i64_utod : ident := 17%positive.
Definition ___i64_utof : ident := 19%positive.
Definition ___stringlit_1 : ident := 59%positive.
Definition ___stringlit_2 : ident := 60%positive.
Definition ___stringlit_3 : ident := 61%positive.
Definition ___stringlit_4 : ident := 62%positive.
Definition ___stringlit_5 : ident := 73%positive.
Definition _abort : ident := 52%positive.
Definition _b : ident := 55%positive.
Definition _bin : ident := 64%positive.
Definition _bin2size : ident := 56%positive.
Definition _fill_bin : ident := 67%positive.
Definition _free : ident := 71%positive.
Definition _free_small : ident := 70%positive.
Definition _main : ident := 75%positive.
Definition _malloc : ident := 74%positive.
Definition _malloc_small : ident := 69%positive.
Definition _nbytes : ident := 68%positive.
Definition _p : ident := 65%positive.
Definition _printf : ident := 53%positive.
Definition _q : ident := 66%positive.
Definition _result : ident := 72%positive.
Definition _s : ident := 57%positive.
Definition _sbrk : ident := 54%positive.
Definition _size2bin : ident := 58%positive.
Definition _testclaim : ident := 63%positive.
Definition _t'1 : ident := 76%positive.
Definition _t'10 : ident := 85%positive.
Definition _t'11 : ident := 86%positive.
Definition _t'12 : ident := 87%positive.
Definition _t'13 : ident := 88%positive.
Definition _t'14 : ident := 89%positive.
Definition _t'15 : ident := 90%positive.
Definition _t'16 : ident := 91%positive.
Definition _t'17 : ident := 92%positive.
Definition _t'18 : ident := 93%positive.
Definition _t'2 : ident := 77%positive.
Definition _t'3 : ident := 78%positive.
Definition _t'4 : ident := 79%positive.
Definition _t'5 : ident := 80%positive.
Definition _t'6 : ident := 81%positive.
Definition _t'7 : ident := 82%positive.
Definition _t'8 : ident := 83%positive.
Definition _t'9 : ident := 84%positive.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 177);
  gvar_init := (Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 63) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 38) ::
                Init_int8 (Int.repr 38) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 60) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 83) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 38) ::
                Init_int8 (Int.repr 38) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 98) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 38) ::
                Init_int8 (Int.repr 38) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 50) :: Init_int8 (Int.repr 98) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 43) :: Init_int8 (Int.repr 87) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 40) ::
                Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 79) ::
                Init_int8 (Int.repr 82) :: Init_int8 (Int.repr 68) ::
                Init_int8 (Int.repr 42) :: Init_int8 (Int.repr 65) ::
                Init_int8 (Int.repr 76) :: Init_int8 (Int.repr 73) ::
                Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 48) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 30);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 58) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 58) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 102) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 96) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 39) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_5 := {|
  gvar_info := (tarray tschar 32);
  gvar_init := (Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 41) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 40) :: Init_int8 (Int.repr 87) ::
                Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 82) ::
                Init_int8 (Int.repr 68) :: Init_int8 (Int.repr 42) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 71) ::
                Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 41) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 61) ::
                Init_int8 (Int.repr 61) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 48) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 51) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 51) ::
                Init_int8 (Int.repr 122) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

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
                   (Econst_int (Int.repr 1) tint) tint) (Esizeof tuint tuint)
                 tuint)))
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
    ((Ebinop Osub (Econst_int (Int.repr 8) tint)
       (Econst_int (Int.repr 1) tint) tint) :: nil))
  (Sifthenelse (Ebinop Ogt (Etempvar _s tuint) (Etempvar _t'1 tuint) tint)
    (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
    (Sreturn (Some (Ebinop Odiv
                     (Ebinop Oadd (Etempvar _s tuint)
                       (Ebinop Osub
                         (Ebinop Omul (Esizeof tuint tuint)
                           (Ebinop Osub (Econst_int (Int.repr 2) tint)
                             (Econst_int (Int.repr 1) tint) tint) tuint)
                         (Econst_int (Int.repr 1) tint) tuint) tuint)
                     (Ebinop Omul (Esizeof tuint tuint)
                       (Econst_int (Int.repr 2) tint) tuint) tuint)))))
|}.

Definition f_testclaim := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_s, tint) :: (_b, tint) :: (_t'18, tvoid) :: (_t'17, tint) ::
               (_t'16, tvoid) :: (_t'15, tuint) :: (_t'14, tint) ::
               (_t'13, tint) :: (_t'12, tint) :: (_t'11, tuint) ::
               (_t'10, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tuint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _s (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _s tint)
                     (Econst_int (Int.repr 122) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _size2bin (Tfunction (Tcons tuint Tnil) tint cc_default))
            ((Etempvar _s tint) :: nil))
          (Sset _b (Etempvar _t'1 tint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _bin2size (Tfunction (Tcons tint Tnil) tuint cc_default))
              ((Etempvar _b tint) :: nil))
            (Scall None
              (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                              {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
              ((Evar ___stringlit_1 (tarray tschar 16)) ::
               (Etempvar _s tint) :: (Etempvar _b tint) ::
               (Etempvar _t'2 tuint) :: nil)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _bin2size (Tfunction (Tcons tint Tnil) tuint
                                  cc_default))
                ((Ebinop Osub (Econst_int (Int.repr 8) tint)
                   (Econst_int (Int.repr 1) tint) tint) :: nil))
              (Sifthenelse (Ebinop Ole (Etempvar _s tint)
                             (Etempvar _t'3 tuint) tint)
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'5)
                          (Evar _size2bin (Tfunction (Tcons tuint Tnil) tint
                                            cc_default))
                          ((Etempvar _s tint) :: nil))
                        (Scall (Some _t'6)
                          (Evar _bin2size (Tfunction (Tcons tint Tnil) tuint
                                            cc_default))
                          ((Etempvar _t'5 tint) :: nil)))
                      (Sifthenelse (Ebinop Ole (Etempvar _s tint)
                                     (Etempvar _t'6 tuint) tint)
                        (Ssequence
                          (Scall (Some _t'8)
                            (Evar _size2bin (Tfunction (Tcons tuint Tnil)
                                              tint cc_default))
                            ((Etempvar _s tint) :: nil))
                          (Sset _t'7
                            (Ecast
                              (Ebinop Olt (Etempvar _t'8 tint)
                                (Econst_int (Int.repr 8) tint) tint) tbool)))
                        (Sset _t'7 (Econst_int (Int.repr 0) tint))))
                    (Sifthenelse (Etempvar _t'7 tint)
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'10)
                                (Evar _size2bin (Tfunction (Tcons tuint Tnil)
                                                  tint cc_default))
                                ((Etempvar _s tint) :: nil))
                              (Scall (Some _t'11)
                                (Evar _bin2size (Tfunction (Tcons tint Tnil)
                                                  tuint cc_default))
                                ((Etempvar _t'10 tint) :: nil)))
                            (Scall (Some _t'12)
                              (Evar _size2bin (Tfunction (Tcons tuint Tnil)
                                                tint cc_default))
                              ((Etempvar _t'11 tuint) :: nil)))
                          (Scall (Some _t'13)
                            (Evar _size2bin (Tfunction (Tcons tuint Tnil)
                                              tint cc_default))
                            ((Etempvar _s tint) :: nil)))
                        (Sset _t'9
                          (Ecast
                            (Ebinop Oeq (Etempvar _t'12 tint)
                              (Etempvar _t'13 tint) tint) tbool)))
                      (Sset _t'9 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'9 tint)
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'14)
                            (Evar _size2bin (Tfunction (Tcons tuint Tnil)
                                              tint cc_default))
                            ((Etempvar _s tint) :: nil))
                          (Scall (Some _t'15)
                            (Evar _bin2size (Tfunction (Tcons tint Tnil)
                                              tuint cc_default))
                            ((Etempvar _t'14 tint) :: nil)))
                        (Sset _t'4
                          (Ecast
                            (Ebinop Oeq
                              (Ebinop Omod
                                (Ebinop Oadd (Etempvar _t'15 tuint)
                                  (Esizeof tuint tuint) tuint)
                                (Ebinop Omul (Esizeof tuint tuint)
                                  (Econst_int (Int.repr 2) tint) tuint)
                                tuint) (Econst_int (Int.repr 0) tint) tint)
                            tbool)))
                      (Sset _t'4 (Ecast (Etempvar _t'4 tint) tint)))
                    (Sset _t'4 (Ecast (Econst_int (Int.repr 0) tint) tint))))
                (Sset _t'4 (Ecast (Econst_int (Int.repr 1) tint) tint))))
            (Sifthenelse (Etempvar _t'4 tint)
              (Sset _t'16
                (Ecast (Ecast (Econst_int (Int.repr 0) tint) tvoid) tvoid))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'17)
                    (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                                    {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
                    ((Evar ___stringlit_4 (tarray tschar 30)) ::
                     (Evar ___stringlit_3 (tarray tschar 9)) ::
                     (Econst_int (Int.repr 48) tint) ::
                     (Evar ___stringlit_2 (tarray tschar 177)) :: nil))
                  (Scall (Some _t'18)
                    (Evar _abort (Tfunction Tnil tvoid cc_default)) nil))
                (Sset _t'16 (Ecast (Etempvar _t'18 tvoid) tvoid))))))))
    (Sset _s
      (Ebinop Oadd (Etempvar _s tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition v_bin := {|
  gvar_info := (tarray (tptr tvoid) 8);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_fill_bin := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_b, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, tuint) :: (_p, (tptr tschar)) :: (_q, (tptr tschar)) ::
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
        (Evar _sbrk (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
        ((Ebinop Omul
           (Ebinop Oshl (Econst_int (Int.repr 2) tint)
             (Econst_int (Int.repr 16) tint) tint) (Esizeof tuint tuint)
           tuint) :: nil))
      (Sset _p (Ecast (Etempvar _t'2 (tptr tvoid)) (tptr tschar))))
    (Ssequence
      (Ssequence
        (Sset _q
          (Ebinop Oadd (Etempvar _p (tptr tschar)) (Etempvar _s tuint)
            (tptr tschar)))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt
                           (Ebinop Oadd
                             (Ebinop Oadd (Etempvar _q (tptr tschar))
                               (Etempvar _s tuint) (tptr tschar))
                             (Esizeof tuint tuint) (tptr tschar))
                           (Ebinop Oadd (Etempvar _p (tptr tschar))
                             (Ebinop Omul
                               (Ebinop Oshl (Econst_int (Int.repr 2) tint)
                                 (Econst_int (Int.repr 16) tint) tint)
                               (Esizeof tuint tuint) tuint) (tptr tschar))
                           tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Ecast (Etempvar _q (tptr tschar)) (tptr tuint))
                    (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
                (Etempvar _s tuint))
              (Sassign
                (Ederef
                  (Ecast
                    (Ebinop Oadd
                      (Ecast (Etempvar _q (tptr tschar)) (tptr tuint))
                      (Econst_int (Int.repr 1) tint) (tptr tuint))
                    (tptr (tptr tvoid))) (tptr tvoid))
                (Ebinop Oadd (Etempvar _q (tptr tschar))
                  (Ebinop Oadd (Etempvar _s tuint) (Esizeof tuint tuint)
                    tuint) (tptr tschar)))))
          (Sset _q
            (Ebinop Oadd (Etempvar _q (tptr tschar))
              (Ebinop Oadd (Etempvar _s tuint) (Esizeof tuint tuint) tuint)
              (tptr tschar)))))
      (Ssequence
        (Sset _q
          (Ebinop Osub (Etempvar _q (tptr tschar))
            (Ebinop Oadd (Etempvar _s tuint) (Esizeof tuint tuint) tuint)
            (tptr tschar)))
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
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
            (Sreturn (Some (Ecast
                             (Ebinop Oadd
                               (Ebinop Oadd (Etempvar _p (tptr tschar))
                                 (Etempvar _s tuint) (tptr tschar))
                               (Esizeof tuint tuint) (tptr tschar))
                             (tptr tvoid))))))))))
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
        (Ebinop Oadd (Evar _bin (tarray (tptr tvoid) 8)) (Etempvar _b tint)
          (tptr (tptr tvoid))) (tptr tvoid)))
    (Ssequence
      (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tvoid)) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _fill_bin (Tfunction (Tcons tint Tnil) (tptr tvoid)
                                cc_default)) ((Etempvar _b tint) :: nil))
            (Sset _p (Etempvar _t'2 (tptr tvoid))))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _bin (tarray (tptr tvoid) 8))
                (Etempvar _b tint) (tptr (tptr tvoid))) (tptr tvoid))
            (Etempvar _p (tptr tvoid))))
        Sskip)
      (Ssequence
        (Sset _q
          (Ederef (Ecast (Etempvar _p (tptr tvoid)) (tptr (tptr tvoid)))
            (tptr tvoid)))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _bin (tarray (tptr tvoid) 8))
                (Etempvar _b tint) (tptr (tptr tvoid))) (tptr tvoid))
            (Etempvar _q (tptr tvoid)))
          (Sreturn (Some (Etempvar _p (tptr tvoid)))))))))
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
        (Ebinop Oadd (Evar _bin (tarray (tptr tvoid) 8)) (Etempvar _b tint)
          (tptr (tptr tvoid))) (tptr tvoid)))
    (Ssequence
      (Sassign
        (Ederef (Ecast (Etempvar _p (tptr tvoid)) (tptr (tptr tvoid)))
          (tptr tvoid)) (Etempvar _q (tptr tvoid)))
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _bin (tarray (tptr tvoid) 8)) (Etempvar _b tint)
            (tptr (tptr tvoid))) (tptr tvoid)) (Etempvar _p (tptr tvoid))))))
|}.

Definition f_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _s
    (Ecast
      (Ederef
        (Ebinop Oadd (Ecast (Etempvar _p (tptr tvoid)) (tptr (tptr tvoid)))
          (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
          (tptr (tptr tvoid))) (tptr tvoid)) tuint))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _bin2size (Tfunction (Tcons tint Tnil) tuint cc_default))
      ((Ebinop Osub (Econst_int (Int.repr 8) tint)
         (Econst_int (Int.repr 1) tint) tint) :: nil))
    (Sifthenelse (Ebinop Ole (Etempvar _s tuint) (Etempvar _t'1 tuint) tint)
      (Scall None
        (Evar _free_small (Tfunction (Tcons (tptr tvoid) (Tcons tuint Tnil))
                            tvoid cc_default))
        ((Etempvar _p (tptr tvoid)) :: (Etempvar _s tuint) :: nil))
      Sskip)))
|}.

Definition f_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_s, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_result, (tptr tvoid)) :: (_t'5, tvoid) :: (_t'4, tint) ::
               (_t'3, tvoid) :: (_t'2, tuint) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'2)
      (Evar _bin2size (Tfunction (Tcons tint Tnil) tuint cc_default))
      ((Ebinop Osub (Econst_int (Int.repr 8) tint)
         (Econst_int (Int.repr 1) tint) tint) :: nil))
    (Sifthenelse (Ebinop Ogt (Etempvar _s tuint) (Etempvar _t'2 tuint) tint)
      (Sset _result (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Scall (Some _t'1)
          (Evar _malloc_small (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                cc_default)) ((Etempvar _s tuint) :: nil))
        (Sset _result (Etempvar _t'1 (tptr tvoid))))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq
                   (Ebinop Omod (Ecast (Etempvar _result (tptr tvoid)) tint)
                     (Ebinop Omul (Esizeof tuint tuint)
                       (Econst_int (Int.repr 2) tint) tuint) tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sset _t'3 (Ecast (Ecast (Econst_int (Int.repr 0) tint) tvoid) tvoid))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                            {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
            ((Evar ___stringlit_4 (tarray tschar 30)) ::
             (Evar ___stringlit_3 (tarray tschar 9)) ::
             (Econst_int (Int.repr 110) tint) ::
             (Evar ___stringlit_5 (tarray tschar 32)) :: nil))
          (Scall (Some _t'5) (Evar _abort (Tfunction Tnil tvoid cc_default))
            nil))
        (Sset _t'3 (Ecast (Etempvar _t'5 tvoid) tvoid))))
    (Sreturn (Some (Etempvar _result (tptr tvoid))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_q, (tptr tvoid)) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None (Evar _testclaim (Tfunction Tnil tvoid cc_default)) nil)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                          cc_default))
          ((Econst_int (Int.repr 100) tint) :: nil))
        (Sset _p (Etempvar _t'1 (tptr tvoid))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                            cc_default))
            ((Econst_int (Int.repr 10) tint) :: nil))
          (Sset _q (Etempvar _t'2 (tptr tvoid))))
        (Ssequence
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default)) ((Etempvar _p (tptr tvoid)) :: nil))
          (Ssequence
            (Scall None
              (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default)) ((Etempvar _q (tptr tvoid)) :: nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                  cc_default))
                  ((Econst_int (Int.repr 100) tint) :: nil))
                (Sset _p (Etempvar _t'3 (tptr tvoid))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                    cc_default))
                    ((Econst_int (Int.repr 10) tint) :: nil))
                  (Sset _q (Etempvar _t'4 (tptr tvoid))))
                (Ssequence
                  (Scall None
                    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                    ((Etempvar _p (tptr tvoid)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                    cc_default))
                      ((Etempvar _q (tptr tvoid)) :: nil))
                    (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
nil.

Definition prog : Clight.program := {|
prog_defs :=
((___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_5, Gvar v___stringlit_5) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___builtin_fabs,
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
 (___i64_smulh,
   Gfun(External (EF_runtime "__i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umulh,
   Gfun(External (EF_runtime "__i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
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
 (_abort,
   Gfun(External (EF_external "abort" (mksignature nil None cc_default)) Tnil
     tvoid cc_default)) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_sbrk,
   Gfun(External (EF_external "sbrk"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_bin2size, Gfun(Internal f_bin2size)) ::
 (_size2bin, Gfun(Internal f_size2bin)) ::
 (_testclaim, Gfun(Internal f_testclaim)) :: (_bin, Gvar v_bin) ::
 (_fill_bin, Gfun(Internal f_fill_bin)) ::
 (_malloc_small, Gfun(Internal f_malloc_small)) ::
 (_free_small, Gfun(Internal f_free_small)) ::
 (_free, Gfun(Internal f_free)) :: (_malloc, Gfun(Internal f_malloc)) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: _malloc :: _free :: _free_small :: _malloc_small :: _fill_bin ::
 _size2bin :: _sbrk :: _printf :: _abort :: ___builtin_debug ::
 ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fsqrt :: ___builtin_ctzll ::
 ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll :: ___builtin_clzl ::
 ___builtin_clz :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap64 :: ___builtin_bswap :: ___i64_umulh :: ___i64_smulh ::
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

