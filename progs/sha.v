Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _p : ident := 45%positive.
Definition _a : ident := 22%positive.
Definition _T1 : ident := 31%positive.
Definition _Nh : ident := 15%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _ignore : ident := 50%positive.
Definition _SHA256_addlength : ident := 43%positive.
Definition _in : ident := 21%positive.
Definition ___builtin_read32_reversed : ident := 10%positive.
Definition _xn : ident := 52%positive.
Definition _SHA256_Init : ident := 39%positive.
Definition _K256 : ident := 19%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition _SHA256 : ident := 54%positive.
Definition _T2 : ident := 32%positive.
Definition _fragment : ident := 47%positive.
Definition _b : ident := 23%positive.
Definition _memcpy : ident := 11%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition _X : ident := 34%positive.
Definition _len : ident := 40%positive.
Definition _Ki : ident := 36%positive.
Definition _cNh : ident := 42%positive.
Definition _md : ident := 49%positive.
Definition _sha256_block_data_order : ident := 38%positive.
Definition _c : ident := 24%positive.
Definition _data_ : ident := 44%positive.
Definition _n : ident := 46%positive.
Definition _g : ident := 28%positive.
Definition _SHA256_Final : ident := 53%positive.
Definition _e : ident := 26%positive.
Definition _ll : ident := 51%positive.
Definition _d : ident := 25%positive.
Definition _memset : ident := 12%positive.
Definition _t : ident := 33%positive.
Definition _Nl : ident := 16%positive.
Definition _s1 : ident := 30%positive.
Definition _cNl : ident := 41%positive.
Definition _ctx : ident := 20%positive.
Definition _s0 : ident := 29%positive.
Definition _data : ident := 14%positive.
Definition _main : ident := 55%positive.
Definition _i : ident := 37%positive.
Definition _f : ident := 27%positive.
Definition _num : ident := 13%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition _struct_SHA256state_st : ident := 18%positive.
Definition _SHA256_Update : ident := 48%positive.
Definition _l : ident := 35%positive.
Definition _h : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition _ignore'2 : ident := 59%positive.
Definition _ignore' : ident := 57%positive.
Definition _l' : ident := 56%positive.
Definition _ignore'1 : ident := 58%positive.

Definition t_struct_SHA256state_st :=
   (Tstruct _struct_SHA256state_st
     (Fcons _h (tarray tuint 8)
       (Fcons _Nl tuint
         (Fcons _Nh tuint
           (Fcons _data (tarray tuchar 64) (Fcons _num tuint Fnil)))))
     noattr).

Definition v_K256 := {|
  gvar_info := (tarray tuint 64);
  gvar_init := (Init_int32 (Int.repr 1116352408) ::
                Init_int32 (Int.repr 1899447441) ::
                Init_int32 (Int.repr (-1245643825)) ::
                Init_int32 (Int.repr (-373957723)) ::
                Init_int32 (Int.repr 961987163) ::
                Init_int32 (Int.repr 1508970993) ::
                Init_int32 (Int.repr (-1841331548)) ::
                Init_int32 (Int.repr (-1424204075)) ::
                Init_int32 (Int.repr (-670586216)) ::
                Init_int32 (Int.repr 310598401) ::
                Init_int32 (Int.repr 607225278) ::
                Init_int32 (Int.repr 1426881987) ::
                Init_int32 (Int.repr 1925078388) ::
                Init_int32 (Int.repr (-2132889090)) ::
                Init_int32 (Int.repr (-1680079193)) ::
                Init_int32 (Int.repr (-1046744716)) ::
                Init_int32 (Int.repr (-459576895)) ::
                Init_int32 (Int.repr (-272742522)) ::
                Init_int32 (Int.repr 264347078) ::
                Init_int32 (Int.repr 604807628) ::
                Init_int32 (Int.repr 770255983) ::
                Init_int32 (Int.repr 1249150122) ::
                Init_int32 (Int.repr 1555081692) ::
                Init_int32 (Int.repr 1996064986) ::
                Init_int32 (Int.repr (-1740746414)) ::
                Init_int32 (Int.repr (-1473132947)) ::
                Init_int32 (Int.repr (-1341970488)) ::
                Init_int32 (Int.repr (-1084653625)) ::
                Init_int32 (Int.repr (-958395405)) ::
                Init_int32 (Int.repr (-710438585)) ::
                Init_int32 (Int.repr 113926993) ::
                Init_int32 (Int.repr 338241895) ::
                Init_int32 (Int.repr 666307205) ::
                Init_int32 (Int.repr 773529912) ::
                Init_int32 (Int.repr 1294757372) ::
                Init_int32 (Int.repr 1396182291) ::
                Init_int32 (Int.repr 1695183700) ::
                Init_int32 (Int.repr 1986661051) ::
                Init_int32 (Int.repr (-2117940946)) ::
                Init_int32 (Int.repr (-1838011259)) ::
                Init_int32 (Int.repr (-1564481375)) ::
                Init_int32 (Int.repr (-1474664885)) ::
                Init_int32 (Int.repr (-1035236496)) ::
                Init_int32 (Int.repr (-949202525)) ::
                Init_int32 (Int.repr (-778901479)) ::
                Init_int32 (Int.repr (-694614492)) ::
                Init_int32 (Int.repr (-200395387)) ::
                Init_int32 (Int.repr 275423344) ::
                Init_int32 (Int.repr 430227734) ::
                Init_int32 (Int.repr 506948616) ::
                Init_int32 (Int.repr 659060556) ::
                Init_int32 (Int.repr 883997877) ::
                Init_int32 (Int.repr 958139571) ::
                Init_int32 (Int.repr 1322822218) ::
                Init_int32 (Int.repr 1537002063) ::
                Init_int32 (Int.repr 1747873779) ::
                Init_int32 (Int.repr 1955562222) ::
                Init_int32 (Int.repr 2024104815) ::
                Init_int32 (Int.repr (-2067236844)) ::
                Init_int32 (Int.repr (-1933114872)) ::
                Init_int32 (Int.repr (-1866530822)) ::
                Init_int32 (Int.repr (-1538233109)) ::
                Init_int32 (Int.repr (-1090935817)) ::
                Init_int32 (Int.repr (-965641998)) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_sha256_block_data_order := {|
  fn_return := tvoid;
  fn_params := ((_ctx, (tptr t_struct_SHA256state_st)) ::
                (_in, (tptr tvoid)) :: nil);
  fn_vars := ((_X, (tarray tuint 16)) :: nil);
  fn_temps := ((_a, tuint) :: (_b, tuint) :: (_c, tuint) :: (_d, tuint) ::
               (_e, tuint) :: (_f, tuint) :: (_g, tuint) :: (_h, tuint) ::
               (_s0, tuint) :: (_s1, tuint) :: (_T1, tuint) ::
               (_T2, tuint) :: (_t, tuint) :: (_l, tuint) :: (_Ki, tuint) ::
               (_i, tint) :: (_data, (tptr tuchar)) :: (_l', tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _data (Etempvar _in (tptr tvoid)))
  (Ssequence
    (Sset _a
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
              t_struct_SHA256state_st) _h (tarray tuint 8))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sset _b
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                t_struct_SHA256state_st) _h (tarray tuint 8))
            (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint))
      (Ssequence
        (Sset _c
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                  t_struct_SHA256state_st) _h (tarray tuint 8))
              (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint))
        (Ssequence
          (Sset _d
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                    t_struct_SHA256state_st) _h (tarray tuint 8))
                (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint))
          (Ssequence
            (Sset _e
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                      t_struct_SHA256state_st) _h (tarray tuint 8))
                  (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _f
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                        t_struct_SHA256state_st) _h (tarray tuint 8))
                    (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint))
              (Ssequence
                (Sset _g
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _ctx (tptr t_struct_SHA256state_st))
                          t_struct_SHA256state_st) _h (tarray tuint 8))
                      (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint))
                (Ssequence
                  (Sset _h
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _ctx (tptr t_struct_SHA256state_st))
                            t_struct_SHA256state_st) _h (tarray tuint 8))
                        (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint))
                  (Ssequence
                    (Ssequence
                      (Sset _i (Econst_int (Int.repr 0) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                         (Econst_int (Int.repr 16) tint)
                                         tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Scall (Some _l')
                                  (Evar ___builtin_read32_reversed (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)
                                                                    tuint))
                                  ((Ecast (Etempvar _data (tptr tuchar))
                                     (tptr tuint)) :: nil))
                                (Sset _l (Ecast (Etempvar _l' tuint) tuint)))
                              (Sset _data
                                (Ebinop Oadd (Etempvar _data (tptr tuchar))
                                  (Econst_int (Int.repr 4) tint)
                                  (tptr tuchar))))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd (Evar _X (tarray tuint 16))
                                    (Etempvar _i tint) (tptr tuint)) tuint)
                                (Etempvar _l tuint))
                              (Ssequence
                                (Sset _Ki
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _K256 (tarray tuint 64))
                                      (Etempvar _i tint) (tptr tuint)) tuint))
                                (Ssequence
                                  (Sset _T1
                                    (Ebinop Oadd
                                      (Ebinop Oadd
                                        (Ebinop Oadd
                                          (Ebinop Oadd (Etempvar _l tuint)
                                            (Etempvar _h tuint) tuint)
                                          (Ebinop Oxor
                                            (Ebinop Oxor
                                              (Ebinop Oor
                                                (Ebinop Oshl
                                                  (Etempvar _e tuint)
                                                  (Econst_int (Int.repr 26) tint)
                                                  tuint)
                                                (Ebinop Oshr
                                                  (Ebinop Oand
                                                    (Etempvar _e tuint)
                                                    (Econst_int (Int.repr (-1)) tuint)
                                                    tuint)
                                                  (Ebinop Osub
                                                    (Econst_int (Int.repr 32) tint)
                                                    (Econst_int (Int.repr 26) tint)
                                                    tint) tuint) tuint)
                                              (Ebinop Oor
                                                (Ebinop Oshl
                                                  (Etempvar _e tuint)
                                                  (Econst_int (Int.repr 21) tint)
                                                  tuint)
                                                (Ebinop Oshr
                                                  (Ebinop Oand
                                                    (Etempvar _e tuint)
                                                    (Econst_int (Int.repr (-1)) tuint)
                                                    tuint)
                                                  (Ebinop Osub
                                                    (Econst_int (Int.repr 32) tint)
                                                    (Econst_int (Int.repr 21) tint)
                                                    tint) tuint) tuint)
                                              tuint)
                                            (Ebinop Oor
                                              (Ebinop Oshl
                                                (Etempvar _e tuint)
                                                (Econst_int (Int.repr 7) tint)
                                                tuint)
                                              (Ebinop Oshr
                                                (Ebinop Oand
                                                  (Etempvar _e tuint)
                                                  (Econst_int (Int.repr (-1)) tuint)
                                                  tuint)
                                                (Ebinop Osub
                                                  (Econst_int (Int.repr 32) tint)
                                                  (Econst_int (Int.repr 7) tint)
                                                  tint) tuint) tuint) tuint)
                                          tuint)
                                        (Ebinop Oxor
                                          (Ebinop Oand (Etempvar _e tuint)
                                            (Etempvar _f tuint) tuint)
                                          (Ebinop Oand
                                            (Eunop Onotint
                                              (Etempvar _e tuint) tuint)
                                            (Etempvar _g tuint) tuint) tuint)
                                        tuint) (Etempvar _Ki tuint) tuint))
                                  (Ssequence
                                    (Sset _T2
                                      (Ebinop Oadd
                                        (Ebinop Oxor
                                          (Ebinop Oxor
                                            (Ebinop Oor
                                              (Ebinop Oshl
                                                (Etempvar _a tuint)
                                                (Econst_int (Int.repr 30) tint)
                                                tuint)
                                              (Ebinop Oshr
                                                (Ebinop Oand
                                                  (Etempvar _a tuint)
                                                  (Econst_int (Int.repr (-1)) tuint)
                                                  tuint)
                                                (Ebinop Osub
                                                  (Econst_int (Int.repr 32) tint)
                                                  (Econst_int (Int.repr 30) tint)
                                                  tint) tuint) tuint)
                                            (Ebinop Oor
                                              (Ebinop Oshl
                                                (Etempvar _a tuint)
                                                (Econst_int (Int.repr 19) tint)
                                                tuint)
                                              (Ebinop Oshr
                                                (Ebinop Oand
                                                  (Etempvar _a tuint)
                                                  (Econst_int (Int.repr (-1)) tuint)
                                                  tuint)
                                                (Ebinop Osub
                                                  (Econst_int (Int.repr 32) tint)
                                                  (Econst_int (Int.repr 19) tint)
                                                  tint) tuint) tuint) tuint)
                                          (Ebinop Oor
                                            (Ebinop Oshl (Etempvar _a tuint)
                                              (Econst_int (Int.repr 10) tint)
                                              tuint)
                                            (Ebinop Oshr
                                              (Ebinop Oand
                                                (Etempvar _a tuint)
                                                (Econst_int (Int.repr (-1)) tuint)
                                                tuint)
                                              (Ebinop Osub
                                                (Econst_int (Int.repr 32) tint)
                                                (Econst_int (Int.repr 10) tint)
                                                tint) tuint) tuint) tuint)
                                        (Ebinop Oxor
                                          (Ebinop Oxor
                                            (Ebinop Oand (Etempvar _a tuint)
                                              (Etempvar _b tuint) tuint)
                                            (Ebinop Oand (Etempvar _a tuint)
                                              (Etempvar _c tuint) tuint)
                                            tuint)
                                          (Ebinop Oand (Etempvar _b tuint)
                                            (Etempvar _c tuint) tuint) tuint)
                                        tuint))
                                    (Ssequence
                                      (Sset _h (Etempvar _g tuint))
                                      (Ssequence
                                        (Sset _g (Etempvar _f tuint))
                                        (Ssequence
                                          (Sset _f (Etempvar _e tuint))
                                          (Ssequence
                                            (Sset _e
                                              (Ebinop Oadd
                                                (Etempvar _d tuint)
                                                (Etempvar _T1 tuint) tuint))
                                            (Ssequence
                                              (Sset _d (Etempvar _c tuint))
                                              (Ssequence
                                                (Sset _c (Etempvar _b tuint))
                                                (Ssequence
                                                  (Sset _b
                                                    (Etempvar _a tuint))
                                                  (Sset _a
                                                    (Ebinop Oadd
                                                      (Etempvar _T1 tuint)
                                                      (Etempvar _T2 tuint)
                                                      tuint)))))))))))))))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    (Ssequence
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                         (Econst_int (Int.repr 64) tint)
                                         tint)
                            Sskip
                            Sbreak)
                          (Ssequence
                            (Sset _s0
                              (Ederef
                                (Ebinop Oadd (Evar _X (tarray tuint 16))
                                  (Ebinop Oand
                                    (Ebinop Oadd (Etempvar _i tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    (Econst_int (Int.repr 15) tint) tint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sset _s0
                                (Ebinop Oxor
                                  (Ebinop Oxor
                                    (Ebinop Oor
                                      (Ebinop Oshl (Etempvar _s0 tuint)
                                        (Econst_int (Int.repr 25) tint)
                                        tuint)
                                      (Ebinop Oshr
                                        (Ebinop Oand (Etempvar _s0 tuint)
                                          (Econst_int (Int.repr (-1)) tuint)
                                          tuint)
                                        (Ebinop Osub
                                          (Econst_int (Int.repr 32) tint)
                                          (Econst_int (Int.repr 25) tint)
                                          tint) tuint) tuint)
                                    (Ebinop Oor
                                      (Ebinop Oshl (Etempvar _s0 tuint)
                                        (Econst_int (Int.repr 14) tint)
                                        tuint)
                                      (Ebinop Oshr
                                        (Ebinop Oand (Etempvar _s0 tuint)
                                          (Econst_int (Int.repr (-1)) tuint)
                                          tuint)
                                        (Ebinop Osub
                                          (Econst_int (Int.repr 32) tint)
                                          (Econst_int (Int.repr 14) tint)
                                          tint) tuint) tuint) tuint)
                                  (Ebinop Oshr (Etempvar _s0 tuint)
                                    (Econst_int (Int.repr 3) tint) tuint)
                                  tuint))
                              (Ssequence
                                (Sset _s1
                                  (Ederef
                                    (Ebinop Oadd (Evar _X (tarray tuint 16))
                                      (Ebinop Oand
                                        (Ebinop Oadd (Etempvar _i tint)
                                          (Econst_int (Int.repr 14) tint)
                                          tint)
                                        (Econst_int (Int.repr 15) tint) tint)
                                      (tptr tuint)) tuint))
                                (Ssequence
                                  (Sset _s1
                                    (Ebinop Oxor
                                      (Ebinop Oxor
                                        (Ebinop Oor
                                          (Ebinop Oshl (Etempvar _s1 tuint)
                                            (Econst_int (Int.repr 15) tint)
                                            tuint)
                                          (Ebinop Oshr
                                            (Ebinop Oand (Etempvar _s1 tuint)
                                              (Econst_int (Int.repr (-1)) tuint)
                                              tuint)
                                            (Ebinop Osub
                                              (Econst_int (Int.repr 32) tint)
                                              (Econst_int (Int.repr 15) tint)
                                              tint) tuint) tuint)
                                        (Ebinop Oor
                                          (Ebinop Oshl (Etempvar _s1 tuint)
                                            (Econst_int (Int.repr 13) tint)
                                            tuint)
                                          (Ebinop Oshr
                                            (Ebinop Oand (Etempvar _s1 tuint)
                                              (Econst_int (Int.repr (-1)) tuint)
                                              tuint)
                                            (Ebinop Osub
                                              (Econst_int (Int.repr 32) tint)
                                              (Econst_int (Int.repr 13) tint)
                                              tint) tuint) tuint) tuint)
                                      (Ebinop Oshr (Etempvar _s1 tuint)
                                        (Econst_int (Int.repr 10) tint)
                                        tuint) tuint))
                                  (Ssequence
                                    (Sset _T1
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _X (tarray tuint 16))
                                          (Ebinop Oand (Etempvar _i tint)
                                            (Econst_int (Int.repr 15) tint)
                                            tint) (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sset _t
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _X (tarray tuint 16))
                                            (Ebinop Oand
                                              (Ebinop Oadd (Etempvar _i tint)
                                                (Econst_int (Int.repr 9) tint)
                                                tint)
                                              (Econst_int (Int.repr 15) tint)
                                              tint) (tptr tuint)) tuint))
                                      (Ssequence
                                        (Sset _T1
                                          (Ebinop Oadd (Etempvar _T1 tuint)
                                            (Ebinop Oadd
                                              (Ebinop Oadd
                                                (Etempvar _s0 tuint)
                                                (Etempvar _s1 tuint) tuint)
                                              (Etempvar _t tuint) tuint)
                                            tuint))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _X (tarray tuint 16))
                                                (Ebinop Oand
                                                  (Etempvar _i tint)
                                                  (Econst_int (Int.repr 15) tint)
                                                  tint) (tptr tuint)) tuint)
                                            (Etempvar _T1 tuint))
                                          (Ssequence
                                            (Sset _Ki
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _K256 (tarray tuint 64))
                                                  (Etempvar _i tint)
                                                  (tptr tuint)) tuint))
                                            (Ssequence
                                              (Sset _T1
                                                (Ebinop Oadd
                                                  (Etempvar _T1 tuint)
                                                  (Ebinop Oadd
                                                    (Ebinop Oadd
                                                      (Ebinop Oadd
                                                        (Etempvar _h tuint)
                                                        (Ebinop Oxor
                                                          (Ebinop Oxor
                                                            (Ebinop Oor
                                                              (Ebinop Oshl
                                                                (Etempvar _e tuint)
                                                                (Econst_int (Int.repr 26) tint)
                                                                tuint)
                                                              (Ebinop Oshr
                                                                (Ebinop Oand
                                                                  (Etempvar _e tuint)
                                                                  (Econst_int (Int.repr (-1)) tuint)
                                                                  tuint)
                                                                (Ebinop Osub
                                                                  (Econst_int (Int.repr 32) tint)
                                                                  (Econst_int (Int.repr 26) tint)
                                                                  tint)
                                                                tuint) tuint)
                                                            (Ebinop Oor
                                                              (Ebinop Oshl
                                                                (Etempvar _e tuint)
                                                                (Econst_int (Int.repr 21) tint)
                                                                tuint)
                                                              (Ebinop Oshr
                                                                (Ebinop Oand
                                                                  (Etempvar _e tuint)
                                                                  (Econst_int (Int.repr (-1)) tuint)
                                                                  tuint)
                                                                (Ebinop Osub
                                                                  (Econst_int (Int.repr 32) tint)
                                                                  (Econst_int (Int.repr 21) tint)
                                                                  tint)
                                                                tuint) tuint)
                                                            tuint)
                                                          (Ebinop Oor
                                                            (Ebinop Oshl
                                                              (Etempvar _e tuint)
                                                              (Econst_int (Int.repr 7) tint)
                                                              tuint)
                                                            (Ebinop Oshr
                                                              (Ebinop Oand
                                                                (Etempvar _e tuint)
                                                                (Econst_int (Int.repr (-1)) tuint)
                                                                tuint)
                                                              (Ebinop Osub
                                                                (Econst_int (Int.repr 32) tint)
                                                                (Econst_int (Int.repr 7) tint)
                                                                tint) tuint)
                                                            tuint) tuint)
                                                        tuint)
                                                      (Ebinop Oxor
                                                        (Ebinop Oand
                                                          (Etempvar _e tuint)
                                                          (Etempvar _f tuint)
                                                          tuint)
                                                        (Ebinop Oand
                                                          (Eunop Onotint
                                                            (Etempvar _e tuint)
                                                            tuint)
                                                          (Etempvar _g tuint)
                                                          tuint) tuint)
                                                      tuint)
                                                    (Etempvar _Ki tuint)
                                                    tuint) tuint))
                                              (Ssequence
                                                (Sset _T2
                                                  (Ebinop Oadd
                                                    (Ebinop Oxor
                                                      (Ebinop Oxor
                                                        (Ebinop Oor
                                                          (Ebinop Oshl
                                                            (Etempvar _a tuint)
                                                            (Econst_int (Int.repr 30) tint)
                                                            tuint)
                                                          (Ebinop Oshr
                                                            (Ebinop Oand
                                                              (Etempvar _a tuint)
                                                              (Econst_int (Int.repr (-1)) tuint)
                                                              tuint)
                                                            (Ebinop Osub
                                                              (Econst_int (Int.repr 32) tint)
                                                              (Econst_int (Int.repr 30) tint)
                                                              tint) tuint)
                                                          tuint)
                                                        (Ebinop Oor
                                                          (Ebinop Oshl
                                                            (Etempvar _a tuint)
                                                            (Econst_int (Int.repr 19) tint)
                                                            tuint)
                                                          (Ebinop Oshr
                                                            (Ebinop Oand
                                                              (Etempvar _a tuint)
                                                              (Econst_int (Int.repr (-1)) tuint)
                                                              tuint)
                                                            (Ebinop Osub
                                                              (Econst_int (Int.repr 32) tint)
                                                              (Econst_int (Int.repr 19) tint)
                                                              tint) tuint)
                                                          tuint) tuint)
                                                      (Ebinop Oor
                                                        (Ebinop Oshl
                                                          (Etempvar _a tuint)
                                                          (Econst_int (Int.repr 10) tint)
                                                          tuint)
                                                        (Ebinop Oshr
                                                          (Ebinop Oand
                                                            (Etempvar _a tuint)
                                                            (Econst_int (Int.repr (-1)) tuint)
                                                            tuint)
                                                          (Ebinop Osub
                                                            (Econst_int (Int.repr 32) tint)
                                                            (Econst_int (Int.repr 10) tint)
                                                            tint) tuint)
                                                        tuint) tuint)
                                                    (Ebinop Oxor
                                                      (Ebinop Oxor
                                                        (Ebinop Oand
                                                          (Etempvar _a tuint)
                                                          (Etempvar _b tuint)
                                                          tuint)
                                                        (Ebinop Oand
                                                          (Etempvar _a tuint)
                                                          (Etempvar _c tuint)
                                                          tuint) tuint)
                                                      (Ebinop Oand
                                                        (Etempvar _b tuint)
                                                        (Etempvar _c tuint)
                                                        tuint) tuint) tuint))
                                                (Ssequence
                                                  (Sset _h
                                                    (Etempvar _g tuint))
                                                  (Ssequence
                                                    (Sset _g
                                                      (Etempvar _f tuint))
                                                    (Ssequence
                                                      (Sset _f
                                                        (Etempvar _e tuint))
                                                      (Ssequence
                                                        (Sset _e
                                                          (Ebinop Oadd
                                                            (Etempvar _d tuint)
                                                            (Etempvar _T1 tuint)
                                                            tuint))
                                                        (Ssequence
                                                          (Sset _d
                                                            (Etempvar _c tuint))
                                                          (Ssequence
                                                            (Sset _c
                                                              (Etempvar _b tuint))
                                                            (Ssequence
                                                              (Sset _b
                                                                (Etempvar _a tuint))
                                                              (Sset _a
                                                                (Ebinop Oadd
                                                                  (Etempvar _T1 tuint)
                                                                  (Etempvar _T2 tuint)
                                                                  tuint)))))))))))))))))))))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint)))
                      (Ssequence
                        (Sset _t
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                  t_struct_SHA256state_st) _h
                                (tarray tuint 8))
                              (Econst_int (Int.repr 0) tint) (tptr tuint))
                            tuint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                    t_struct_SHA256state_st) _h
                                  (tarray tuint 8))
                                (Econst_int (Int.repr 0) tint) (tptr tuint))
                              tuint)
                            (Ebinop Oadd (Etempvar _t tuint)
                              (Etempvar _a tuint) tuint))
                          (Ssequence
                            (Sset _t
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                      t_struct_SHA256state_st) _h
                                    (tarray tuint 8))
                                  (Econst_int (Int.repr 1) tint)
                                  (tptr tuint)) tuint))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                        t_struct_SHA256state_st) _h
                                      (tarray tuint 8))
                                    (Econst_int (Int.repr 1) tint)
                                    (tptr tuint)) tuint)
                                (Ebinop Oadd (Etempvar _t tuint)
                                  (Etempvar _b tuint) tuint))
                              (Ssequence
                                (Sset _t
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                          t_struct_SHA256state_st) _h
                                        (tarray tuint 8))
                                      (Econst_int (Int.repr 2) tint)
                                      (tptr tuint)) tuint))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                            t_struct_SHA256state_st) _h
                                          (tarray tuint 8))
                                        (Econst_int (Int.repr 2) tint)
                                        (tptr tuint)) tuint)
                                    (Ebinop Oadd (Etempvar _t tuint)
                                      (Etempvar _c tuint) tuint))
                                  (Ssequence
                                    (Sset _t
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                              t_struct_SHA256state_st) _h
                                            (tarray tuint 8))
                                          (Econst_int (Int.repr 3) tint)
                                          (tptr tuint)) tuint))
                                    (Ssequence
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                                t_struct_SHA256state_st) _h
                                              (tarray tuint 8))
                                            (Econst_int (Int.repr 3) tint)
                                            (tptr tuint)) tuint)
                                        (Ebinop Oadd (Etempvar _t tuint)
                                          (Etempvar _d tuint) tuint))
                                      (Ssequence
                                        (Sset _t
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                                  t_struct_SHA256state_st) _h
                                                (tarray tuint 8))
                                              (Econst_int (Int.repr 4) tint)
                                              (tptr tuint)) tuint))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                                    t_struct_SHA256state_st)
                                                  _h (tarray tuint 8))
                                                (Econst_int (Int.repr 4) tint)
                                                (tptr tuint)) tuint)
                                            (Ebinop Oadd (Etempvar _t tuint)
                                              (Etempvar _e tuint) tuint))
                                          (Ssequence
                                            (Sset _t
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                                      t_struct_SHA256state_st)
                                                    _h (tarray tuint 8))
                                                  (Econst_int (Int.repr 5) tint)
                                                  (tptr tuint)) tuint))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                                        t_struct_SHA256state_st)
                                                      _h (tarray tuint 8))
                                                    (Econst_int (Int.repr 5) tint)
                                                    (tptr tuint)) tuint)
                                                (Ebinop Oadd
                                                  (Etempvar _t tuint)
                                                  (Etempvar _f tuint) tuint))
                                              (Ssequence
                                                (Sset _t
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                                          t_struct_SHA256state_st)
                                                        _h (tarray tuint 8))
                                                      (Econst_int (Int.repr 6) tint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                                            t_struct_SHA256state_st)
                                                          _h
                                                          (tarray tuint 8))
                                                        (Econst_int (Int.repr 6) tint)
                                                        (tptr tuint)) tuint)
                                                    (Ebinop Oadd
                                                      (Etempvar _t tuint)
                                                      (Etempvar _g tuint)
                                                      tuint))
                                                  (Ssequence
                                                    (Sset _t
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                                              t_struct_SHA256state_st)
                                                            _h
                                                            (tarray tuint 8))
                                                          (Econst_int (Int.repr 7) tint)
                                                          (tptr tuint))
                                                        tuint))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _ctx (tptr t_struct_SHA256state_st))
                                                                t_struct_SHA256state_st)
                                                              _h
                                                              (tarray tuint 8))
                                                            (Econst_int (Int.repr 7) tint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Ebinop Oadd
                                                          (Etempvar _t tuint)
                                                          (Etempvar _h tuint)
                                                          tuint))
                                                      (Sreturn None))))))))))))))))))))))))))))
|}.

Definition f_SHA256_Init := {|
  fn_return := tvoid;
  fn_params := ((_c, (tptr t_struct_SHA256state_st)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
            t_struct_SHA256state_st) _h (tarray tuint 8))
        (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
    (Econst_int (Int.repr 1779033703) tuint))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
              t_struct_SHA256state_st) _h (tarray tuint 8))
          (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
      (Econst_int (Int.repr (-1150833019)) tuint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                t_struct_SHA256state_st) _h (tarray tuint 8))
            (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint)
        (Econst_int (Int.repr 1013904242) tuint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                  t_struct_SHA256state_st) _h (tarray tuint 8))
              (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint)
          (Econst_int (Int.repr (-1521486534)) tuint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                    t_struct_SHA256state_st) _h (tarray tuint 8))
                (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint)
            (Econst_int (Int.repr 1359893119) tuint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                      t_struct_SHA256state_st) _h (tarray tuint 8))
                  (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint)
              (Econst_int (Int.repr (-1694144372)) tuint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                        t_struct_SHA256state_st) _h (tarray tuint 8))
                    (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint)
                (Econst_int (Int.repr 528734635) tuint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                          t_struct_SHA256state_st) _h (tarray tuint 8))
                      (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint)
                  (Econst_int (Int.repr 1541459225) tuint))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                        t_struct_SHA256state_st) _Nl tuint)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                          t_struct_SHA256state_st) _Nh tuint)
                      (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _c (tptr t_struct_SHA256state_st))
                            t_struct_SHA256state_st) _num tuint)
                        (Econst_int (Int.repr 0) tint))
                      (Sreturn None))))))))))))
|}.

Definition f_SHA256_addlength := {|
  fn_return := tvoid;
  fn_params := ((_c, (tptr t_struct_SHA256state_st)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_l, tuint) :: (_cNl, tuint) :: (_cNh, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _cNl
    (Efield
      (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
        t_struct_SHA256state_st) _Nl tuint))
  (Ssequence
    (Sset _cNh
      (Efield
        (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
          t_struct_SHA256state_st) _Nh tuint))
    (Ssequence
      (Sset _l
        (Ebinop Oand
          (Ebinop Oadd (Etempvar _cNl tuint)
            (Ebinop Oshl (Ecast (Etempvar _len tuint) tuint)
              (Econst_int (Int.repr 3) tint) tuint) tuint)
          (Econst_int (Int.repr (-1)) tuint) tuint))
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _l tuint) (Etempvar _cNl tuint)
                       tint)
          (Sset _cNh
            (Ebinop Oadd (Etempvar _cNh tuint) (Econst_int (Int.repr 1) tint)
              tuint))
          Sskip)
        (Ssequence
          (Sset _cNh
            (Ebinop Oadd (Etempvar _cNh tuint)
              (Ebinop Oshr (Etempvar _len tuint)
                (Econst_int (Int.repr 29) tint) tuint) tuint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                  t_struct_SHA256state_st) _Nl tuint) (Etempvar _l tuint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                    t_struct_SHA256state_st) _Nh tuint)
                (Etempvar _cNh tuint))
              (Sreturn None))))))))
|}.

Definition f_SHA256_Update := {|
  fn_return := tvoid;
  fn_params := ((_c, (tptr t_struct_SHA256state_st)) ::
                (_data_, (tptr tvoid)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_data, (tptr tuchar)) :: (_p, (tptr tuchar)) ::
               (_n, tuint) :: (_fragment, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _data (Etempvar _data_ (tptr tvoid)))
  (Ssequence
    (Scall None
      (Evar _SHA256_addlength (Tfunction
                                (Tcons (tptr t_struct_SHA256state_st)
                                  (Tcons tuint Tnil)) tvoid))
      ((Etempvar _c (tptr t_struct_SHA256state_st)) ::
       (Etempvar _len tuint) :: nil))
    (Ssequence
      (Sset _n
        (Efield
          (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
            t_struct_SHA256state_st) _num tuint))
      (Ssequence
        (Sset _p
          (Efield
            (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
              t_struct_SHA256state_st) _data (tarray tuchar 64)))
        (Ssequence
          (Sifthenelse (Ebinop One (Etempvar _n tuint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _fragment
                (Ebinop Osub
                  (Ebinop Omul (Econst_int (Int.repr 16) tint)
                    (Econst_int (Int.repr 4) tint) tint) (Etempvar _n tuint)
                  tuint))
              (Sifthenelse (Ebinop Oge (Etempvar _len tuint)
                             (Etempvar _fragment tuint) tint)
                (Ssequence
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                    (tptr tvoid)))
                    ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                       (Etempvar _n tuint) (tptr tuchar)) ::
                     (Etempvar _data (tptr tuchar)) ::
                     (Etempvar _fragment tuint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _sha256_block_data_order (Tfunction
                                                       (Tcons
                                                         (tptr t_struct_SHA256state_st)
                                                         (Tcons (tptr tvoid)
                                                           Tnil)) tvoid))
                      ((Etempvar _c (tptr t_struct_SHA256state_st)) ::
                       (Etempvar _p (tptr tuchar)) :: nil))
                    (Ssequence
                      (Sset _data
                        (Ebinop Oadd (Etempvar _data (tptr tuchar))
                          (Etempvar _fragment tuint) (tptr tuchar)))
                      (Ssequence
                        (Sset _len
                          (Ebinop Osub (Etempvar _len tuint)
                            (Etempvar _fragment tuint) tuint))
                        (Scall None
                          (Evar _memset (Tfunction
                                          (Tcons (tptr tvoid)
                                            (Tcons tint (Tcons tuint Tnil)))
                                          (tptr tvoid)))
                          ((Etempvar _p (tptr tuchar)) ::
                           (Econst_int (Int.repr 0) tint) ::
                           (Ebinop Omul (Econst_int (Int.repr 16) tint)
                             (Econst_int (Int.repr 4) tint) tint) :: nil))))))
                (Ssequence
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                    (tptr tvoid)))
                    ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                       (Etempvar _n tuint) (tptr tuchar)) ::
                     (Etempvar _data (tptr tuchar)) ::
                     (Etempvar _len tuint) :: nil))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                          t_struct_SHA256state_st) _num tuint)
                      (Ebinop Oadd (Etempvar _n tuint)
                        (Ecast (Etempvar _len tuint) tuint) tuint))
                    (Sreturn None)))))
            Sskip)
          (Ssequence
            (Swhile
              (Ebinop Oge (Etempvar _len tuint)
                (Ebinop Omul (Econst_int (Int.repr 16) tint)
                  (Econst_int (Int.repr 4) tint) tint) tint)
              (Ssequence
                (Scall None
                  (Evar _sha256_block_data_order (Tfunction
                                                   (Tcons
                                                     (tptr t_struct_SHA256state_st)
                                                     (Tcons (tptr tvoid)
                                                       Tnil)) tvoid))
                  ((Etempvar _c (tptr t_struct_SHA256state_st)) ::
                   (Etempvar _data (tptr tuchar)) :: nil))
                (Ssequence
                  (Sset _data
                    (Ebinop Oadd (Etempvar _data (tptr tuchar))
                      (Ebinop Omul (Econst_int (Int.repr 16) tint)
                        (Econst_int (Int.repr 4) tint) tint) (tptr tuchar)))
                  (Sset _len
                    (Ebinop Osub (Etempvar _len tuint)
                      (Ebinop Omul (Econst_int (Int.repr 16) tint)
                        (Econst_int (Int.repr 4) tint) tint) tuint)))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                    t_struct_SHA256state_st) _num tuint)
                (Etempvar _len tuint))
              (Ssequence
                (Sifthenelse (Ebinop One (Etempvar _len tuint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                    (tptr tvoid)))
                    ((Etempvar _p (tptr tuchar)) ::
                     (Etempvar _data (tptr tuchar)) ::
                     (Etempvar _len tuint) :: nil))
                  Sskip)
                (Sreturn None)))))))))
|}.

Definition f_SHA256_Final := {|
  fn_return := tvoid;
  fn_params := ((_md, (tptr tuchar)) ::
                (_c, (tptr t_struct_SHA256state_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tuchar)) :: (_n, tuint) :: (_cNl, tuint) ::
               (_cNh, tuint) :: (_ignore, (tptr tvoid)) :: (_ll, tuint) ::
               (_xn, tuint) :: (_ignore'2, (tptr tvoid)) ::
               (_ignore'1, (tptr tvoid)) :: (_ignore', (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Efield
      (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
        t_struct_SHA256state_st) _data (tarray tuchar 64)))
  (Ssequence
    (Sset _n
      (Efield
        (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
          t_struct_SHA256state_st) _num tuint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _n tuint)
            (tptr tuchar)) tuchar) (Econst_int (Int.repr 128) tint))
      (Ssequence
        (Sset _n
          (Ebinop Oadd (Etempvar _n tuint) (Econst_int (Int.repr 1) tint)
            tuint))
        (Ssequence
          (Sifthenelse (Ebinop Ogt (Etempvar _n tuint)
                         (Ebinop Osub
                           (Ebinop Omul (Econst_int (Int.repr 16) tint)
                             (Econst_int (Int.repr 4) tint) tint)
                           (Econst_int (Int.repr 8) tint) tint) tint)
            (Ssequence
              (Ssequence
                (Scall (Some _ignore')
                  (Evar _memset (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons tint (Tcons tuint Tnil)))
                                  (tptr tvoid)))
                  ((Ebinop Oadd (Etempvar _p (tptr tuchar))
                     (Etempvar _n tuint) (tptr tuchar)) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Ebinop Osub
                     (Ebinop Omul (Econst_int (Int.repr 16) tint)
                       (Econst_int (Int.repr 4) tint) tint)
                     (Etempvar _n tuint) tuint) :: nil))
                (Sset _ignore (Etempvar _ignore' (tptr tvoid))))
              (Ssequence
                (Sset _n (Econst_int (Int.repr 0) tint))
                (Scall None
                  (Evar _sha256_block_data_order (Tfunction
                                                   (Tcons
                                                     (tptr t_struct_SHA256state_st)
                                                     (Tcons (tptr tvoid)
                                                       Tnil)) tvoid))
                  ((Etempvar _c (tptr t_struct_SHA256state_st)) ::
                   (Etempvar _p (tptr tuchar)) :: nil))))
            Sskip)
          (Ssequence
            (Ssequence
              (Scall (Some _ignore'1)
                (Evar _memset (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid)))
                ((Ebinop Oadd (Etempvar _p (tptr tuchar)) (Etempvar _n tuint)
                   (tptr tuchar)) :: (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Osub
                   (Ebinop Osub
                     (Ebinop Omul (Econst_int (Int.repr 16) tint)
                       (Econst_int (Int.repr 4) tint) tint)
                     (Econst_int (Int.repr 8) tint) tint) (Etempvar _n tuint)
                   tuint) :: nil))
              (Sset _ignore (Etempvar _ignore'1 (tptr tvoid))))
            (Ssequence
              (Sset _p
                (Ebinop Oadd (Etempvar _p (tptr tuchar))
                  (Ebinop Osub
                    (Ebinop Omul (Econst_int (Int.repr 16) tint)
                      (Econst_int (Int.repr 4) tint) tint)
                    (Econst_int (Int.repr 8) tint) tint) (tptr tuchar)))
              (Ssequence
                (Sset _cNh
                  (Efield
                    (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                      t_struct_SHA256state_st) _Nh tuint))
                (Ssequence
                  (Ssequence
                    (Scall None
                      (Evar ___builtin_write32_reversed (Tfunction
                                                          (Tcons (tptr tuint)
                                                            (Tcons tuint
                                                              Tnil)) tvoid))
                      ((Ecast (Etempvar _p (tptr tuchar)) (tptr tuint)) ::
                       (Etempvar _cNh tuint) :: nil))
                    (Sset _p
                      (Ebinop Oadd (Etempvar _p (tptr tuchar))
                        (Econst_int (Int.repr 4) tint) (tptr tuchar))))
                  (Ssequence
                    (Sset _cNl
                      (Efield
                        (Ederef (Etempvar _c (tptr t_struct_SHA256state_st))
                          t_struct_SHA256state_st) _Nl tuint))
                    (Ssequence
                      (Ssequence
                        (Scall None
                          (Evar ___builtin_write32_reversed (Tfunction
                                                              (Tcons
                                                                (tptr tuint)
                                                                (Tcons tuint
                                                                  Tnil))
                                                              tvoid))
                          ((Ecast (Etempvar _p (tptr tuchar)) (tptr tuint)) ::
                           (Etempvar _cNl tuint) :: nil))
                        (Sset _p
                          (Ebinop Oadd (Etempvar _p (tptr tuchar))
                            (Econst_int (Int.repr 4) tint) (tptr tuchar))))
                      (Ssequence
                        (Sset _p
                          (Ebinop Osub (Etempvar _p (tptr tuchar))
                            (Ebinop Omul (Econst_int (Int.repr 16) tint)
                              (Econst_int (Int.repr 4) tint) tint)
                            (tptr tuchar)))
                        (Ssequence
                          (Scall None
                            (Evar _sha256_block_data_order (Tfunction
                                                             (Tcons
                                                               (tptr t_struct_SHA256state_st)
                                                               (Tcons
                                                                 (tptr tvoid)
                                                                 Tnil))
                                                             tvoid))
                            ((Etempvar _c (tptr t_struct_SHA256state_st)) ::
                             (Etempvar _p (tptr tuchar)) :: nil))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _c (tptr t_struct_SHA256state_st))
                                  t_struct_SHA256state_st) _num tuint)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _ignore'2)
                                  (Evar _memset (Tfunction
                                                  (Tcons (tptr tvoid)
                                                    (Tcons tint
                                                      (Tcons tuint Tnil)))
                                                  (tptr tvoid)))
                                  ((Etempvar _p (tptr tuchar)) ::
                                   (Econst_int (Int.repr 0) tint) ::
                                   (Ebinop Omul
                                     (Econst_int (Int.repr 16) tint)
                                     (Econst_int (Int.repr 4) tint) tint) ::
                                   nil))
                                (Sset _ignore
                                  (Etempvar _ignore'2 (tptr tvoid))))
                              (Ssequence
                                (Ssequence
                                  (Sset _xn (Econst_int (Int.repr 0) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _xn tuint)
                                                     (Ebinop Odiv
                                                       (Econst_int (Int.repr 32) tint)
                                                       (Econst_int (Int.repr 4) tint)
                                                       tint) tint)
                                        Sskip
                                        Sbreak)
                                      (Ssequence
                                        (Sset _ll
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _c (tptr t_struct_SHA256state_st))
                                                  t_struct_SHA256state_st) _h
                                                (tarray tuint 8))
                                              (Etempvar _xn tuint)
                                              (tptr tuint)) tuint))
                                        (Ssequence
                                          (Scall None
                                            (Evar ___builtin_write32_reversed 
                                            (Tfunction
                                              (Tcons (tptr tuint)
                                                (Tcons tuint Tnil)) tvoid))
                                            ((Ecast
                                               (Etempvar _md (tptr tuchar))
                                               (tptr tuint)) ::
                                             (Etempvar _ll tuint) :: nil))
                                          (Sset _md
                                            (Ebinop Oadd
                                              (Etempvar _md (tptr tuchar))
                                              (Econst_int (Int.repr 4) tint)
                                              (tptr tuchar))))))
                                    (Sset _xn
                                      (Ebinop Oadd (Etempvar _xn tuint)
                                        (Econst_int (Int.repr 1) tint) tuint))))
                                (Sreturn None)))))))))))))))))
|}.

Definition f_SHA256 := {|
  fn_return := tvoid;
  fn_params := ((_d, (tptr tuchar)) :: (_n, tuint) :: (_md, (tptr tuchar)) ::
                nil);
  fn_vars := ((_c, t_struct_SHA256state_st) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _SHA256_Init (Tfunction (Tcons (tptr t_struct_SHA256state_st) Tnil)
                         tvoid))
    ((Eaddrof (Evar _c t_struct_SHA256state_st)
       (tptr t_struct_SHA256state_st)) :: nil))
  (Ssequence
    (Scall None
      (Evar _SHA256_Update (Tfunction
                             (Tcons (tptr t_struct_SHA256state_st)
                               (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                             tvoid))
      ((Eaddrof (Evar _c t_struct_SHA256state_st)
         (tptr t_struct_SHA256state_st)) :: (Etempvar _d (tptr tuchar)) ::
       (Etempvar _n tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar _SHA256_Final (Tfunction
                              (Tcons (tptr tuchar)
                                (Tcons (tptr t_struct_SHA256state_st) Tnil))
                              tvoid))
        ((Etempvar _md (tptr tuchar)) ::
         (Eaddrof (Evar _c t_struct_SHA256state_st)
           (tptr t_struct_SHA256state_st)) :: nil))
      (Sreturn None))))
|}.

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
   Gfun(External (EF_builtin ___builtin_fabs
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)))
     (Tcons tdouble Tnil) tdouble)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin ___builtin_memcpy_aligned
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid)) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint)))
     (Tcons (tptr tschar) (Tcons tint Tnil)) tint)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin ___builtin_read32_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)))
     (Tcons (tptr tuint) Tnil) tuint)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin ___builtin_write32_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None))
     (Tcons (tptr tuint) (Tcons tuint Tnil)) tvoid)) ::
 (_memcpy,
   Gfun(External (EF_external _memcpy
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint)))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
     (tptr tvoid))) ::
 (_memset,
   Gfun(External (EF_external _memset
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint)))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil))) (tptr tvoid))) ::
 (_K256, Gvar v_K256) ::
 (_sha256_block_data_order, Gfun(Internal f_sha256_block_data_order)) ::
 (_SHA256_Init, Gfun(Internal f_SHA256_Init)) ::
 (_SHA256_addlength, Gfun(Internal f_SHA256_addlength)) ::
 (_SHA256_Update, Gfun(Internal f_SHA256_Update)) ::
 (_SHA256_Final, Gfun(Internal f_SHA256_Final)) ::
 (_SHA256, Gfun(Internal f_SHA256)) :: nil);
prog_main := _main
|}.

