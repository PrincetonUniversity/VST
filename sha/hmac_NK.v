Require Import Clightdefs.

Require Import sha.sha.
Definition t_struct_SHA256state_st := sha.t_struct_SHA256state_st.

Local Open Scope Z_scope.

Definition _m__1 : ident := 1165%positive.
Definition _SHA256_Final : ident := 1140%positive.
Definition ___compcert_va_int64 : ident := 1116%positive.
Definition _SHA256_Init : ident := 1138%positive.
Definition _key : ident := 1146%positive.
Definition _n : ident := 1162%positive.
Definition _HMAC_Update : ident := 1154%positive.
Definition ___builtin_fmax : ident := 1122%positive.
Definition ___builtin_va_arg : ident := 1112%positive.
Definition _c : ident := 1163%positive.
Definition ___builtin_annot_intval : ident := 1110%positive.
Definition _struct_hmac_ctx_st : ident := 1144%positive.
Definition ___builtin_negl : ident := 113%positive.
Definition ___builtin_write32_reversed : ident := 112%positive.
Definition ___builtin_write16_reversed : ident := 111%positive.
Definition _memset : ident := 1131%positive.
Definition _j : ident := 1149%positive.
Definition _HMAC2 : ident := 1166%positive.
Definition _m : ident := 1159%positive.
Definition ___builtin_addl : ident := 114%positive.
Definition _HMAC_cleanup : ident := 1158%positive.
Definition ___builtin_read16_reversed : ident := 1128%positive.
Definition ___builtin_fabs : ident := 117%positive.
Definition ___builtin_fsqrt : ident := 1121%positive.
Definition ___builtin_bswap : ident := 1118%positive.
Definition _ctx : ident := 1145%positive.
Definition ___builtin_va_copy : ident := 1113%positive.
Definition ___builtin_fnmsub : ident := 1127%positive.
Definition _data : ident := 1133%positive.
Definition _buf : ident := 1156%positive.
Definition ___builtin_fmsub : ident := 1125%positive.
Definition ___compcert_va_int32 : ident := 1115%positive.
Definition _key_len : ident := 1160%positive.
Definition ___builtin_bswap16 : ident := 1120%positive.
Definition _num : ident := 1132%positive.
Definition ___builtin_fmadd : ident := 1124%positive.
Definition _main : ident := 1167%positive.
Definition ___compcert_va_float64 : ident := 1117%positive.
Definition ___builtin_memcpy_aligned : ident := 118%positive.
Definition ___builtin_subl : ident := 115%positive.
Definition _reset : ident := 1150%positive.
Definition _md_ctx : ident := 1143%positive.
Definition _HMAC_Init : ident := 1153%positive.
Definition _len : ident := 1147%positive.
Definition _HMAC_Final : ident := 1157%positive.
Definition _h : ident := 1136%positive.
Definition ___builtin_va_end : ident := 1114%positive.
Definition ___builtin_mull : ident := 116%positive.
Definition ___builtin_fnmadd : ident := 1126%positive.
Definition ___builtin_bswap32 : ident := 1119%positive.
Definition _SHA256_Update : ident := 1139%positive.
Definition _d : ident := 1161%positive.
Definition ___builtin_va_start : ident := 1111%positive.
Definition _struct_SHA256state_st : ident := 1137%positive.
Definition _i_ctx : ident := 1142%positive.
Definition ___builtin_annot : ident := 119%positive.
Definition _HMAC : ident := 1164%positive.
Definition _ctx_key : ident := 1152%positive.
Definition _o_ctx : ident := 1141%positive.
Definition _Nh : ident := 1134%positive.
Definition ___builtin_read32_reversed : ident := 1129%positive.
Definition _md : ident := 1155%positive.
Definition _Nl : ident := 1135%positive.
Definition _memcpy : ident := 1130%positive.
Definition ___builtin_fmin : ident := 1123%positive.
Definition _pad : ident := 1151%positive.
Definition _i : ident := 1148%positive.
(*
Definition t_struct_SHA256state_st :=
   (Tstruct _struct_SHA256state_st
     (Fcons _h (tarray tuint 8)
       (Fcons _Nl tuint
         (Fcons _Nh tuint
           (Fcons _data (tarray tuchar 64) (Fcons _num tuint Fnil)))))
     noattr).
*)
Definition t_struct_hmac_ctx_st :=
   (Tstruct _struct_hmac_ctx_st
     (Fcons _md_ctx
       (Tstruct _struct_SHA256state_st
         (Fcons _h (tarray tuint 8)
           (Fcons _Nl tuint
             (Fcons _Nh tuint
               (Fcons _data (tarray tuchar 64) (Fcons _num tuint Fnil)))))
         noattr)
       (Fcons _i_ctx
         (Tstruct _struct_SHA256state_st
           (Fcons _h (tarray tuint 8)
             (Fcons _Nl tuint
               (Fcons _Nh tuint
                 (Fcons _data (tarray tuchar 64) (Fcons _num tuint Fnil)))))
           noattr)
         (Fcons _o_ctx
           (Tstruct _struct_SHA256state_st
             (Fcons _h (tarray tuint 8)
               (Fcons _Nl tuint
                 (Fcons _Nh tuint
                   (Fcons _data (tarray tuchar 64) (Fcons _num tuint Fnil)))))
             noattr) Fnil))) noattr).

Definition f_HMAC_Init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr t_struct_hmac_ctx_st)) ::
                (_key, (tptr tuchar)) :: (_len, tint) :: nil);
  fn_vars := ((_pad, (tarray tuchar 64)) :: (_ctx_key, (tarray tuchar 64)) ::
              nil);
  fn_temps := ((_i, tint) :: (_j, tint) :: (_reset, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _reset (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _key (tptr tuchar))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sset _reset (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sset _j (Econst_int (Int.repr 64) tint))
          (Sifthenelse (Ebinop Olt (Etempvar _j tint) (Etempvar _len tint)
                         tint)
            (Ssequence
              (Scall None
                (Evar _SHA256_Init (Tfunction
                                     (Tcons (tptr t_struct_SHA256state_st)
                                       Tnil) tvoid cc_default))
                ((Eaddrof
                   (Efield
                     (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                       t_struct_hmac_ctx_st) _md_ctx t_struct_SHA256state_st)
                   (tptr t_struct_SHA256state_st)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _SHA256_Update (Tfunction
                                         (Tcons
                                           (tptr t_struct_SHA256state_st)
                                           (Tcons (tptr tvoid)
                                             (Tcons tuint Tnil))) tvoid
                                         cc_default))
                  ((Eaddrof
                     (Efield
                       (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                         t_struct_hmac_ctx_st) _md_ctx
                       t_struct_SHA256state_st)
                     (tptr t_struct_SHA256state_st)) ::
                   (Etempvar _key (tptr tuchar)) :: (Etempvar _len tint) ::
                   nil))
                (Ssequence
                  (Scall None
                    (Evar _SHA256_Final (Tfunction
                                          (Tcons (tptr tuchar)
                                            (Tcons
                                              (tptr t_struct_SHA256state_st)
                                              Tnil)) tvoid cc_default))
                    ((Evar _ctx_key (tarray tuchar 64)) ::
                     (Eaddrof
                       (Efield
                         (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                           t_struct_hmac_ctx_st) _md_ctx
                         t_struct_SHA256state_st)
                       (tptr t_struct_SHA256state_st)) :: nil))
                  (Scall None
                    (Evar _memset (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons tint (Tcons tuint Tnil)))
                                    (tptr tvoid) cc_default))
                    ((Eaddrof
                       (Ederef
                         (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                           (Econst_int (Int.repr 32) tint) (tptr tuchar))
                         tuchar) (tptr tuchar)) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 32) tint) :: nil)))))
            (Ssequence
              (Scall None
                (Evar _memcpy (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                ((Evar _ctx_key (tarray tuchar 64)) ::
                 (Etempvar _key (tptr tuchar)) :: (Etempvar _len tint) ::
                 nil))
              (Scall None
                (Evar _memset (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                ((Eaddrof
                   (Ederef
                     (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                       (Etempvar _len tint) (tptr tuchar)) tuchar)
                   (tptr tuchar)) :: (Econst_int (Int.repr 0) tint) ::
                 (Ebinop Osub (Econst_int (Int.repr 64) tuint)
                   (Etempvar _len tint) tuint) :: nil))))))
      Sskip)
    (Ssequence
      (Sifthenelse (Etempvar _reset tint)
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                               (Econst_int (Int.repr 64) tint) tint)
                  Sskip
                  Sbreak)
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _pad (tarray tuchar 64))
                      (Etempvar _i tint) (tptr tuchar)) tuchar)
                  (Ebinop Oxor (Econst_int (Int.repr 54) tint)
                    (Ederef
                      (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                        (Etempvar _i tint) (tptr tuchar)) tuchar) tint)))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tint)
                  (Econst_int (Int.repr 1) tint) tint))))
          (Ssequence
            (Scall None
              (Evar _SHA256_Init (Tfunction
                                   (Tcons (tptr t_struct_SHA256state_st)
                                     Tnil) tvoid cc_default))
              ((Eaddrof
                 (Efield
                   (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                     t_struct_hmac_ctx_st) _i_ctx t_struct_SHA256state_st)
                 (tptr t_struct_SHA256state_st)) :: nil))
            (Ssequence
              (Scall None
                (Evar _SHA256_Update (Tfunction
                                       (Tcons (tptr t_struct_SHA256state_st)
                                         (Tcons (tptr tvoid)
                                           (Tcons tuint Tnil))) tvoid
                                       cc_default))
                ((Eaddrof
                   (Efield
                     (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                       t_struct_hmac_ctx_st) _i_ctx t_struct_SHA256state_st)
                   (tptr t_struct_SHA256state_st)) ::
                 (Evar _pad (tarray tuchar 64)) ::
                 (Econst_int (Int.repr 64) tint) :: nil))
              (Ssequence
                (Ssequence
                  (Sset _i (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                     (Econst_int (Int.repr 64) tint) tint)
                        Sskip
                        Sbreak)
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _pad (tarray tuchar 64))
                            (Etempvar _i tint) (tptr tuchar)) tuchar)
                        (Ebinop Oxor (Econst_int (Int.repr 92) tint)
                          (Ederef
                            (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                              (Etempvar _i tint) (tptr tuchar)) tuchar) tint)))
                    (Sset _i
                      (Ebinop Oadd (Etempvar _i tint)
                        (Econst_int (Int.repr 1) tint) tint))))
                (Ssequence
                  (Scall None
                    (Evar _SHA256_Init (Tfunction
                                         (Tcons
                                           (tptr t_struct_SHA256state_st)
                                           Tnil) tvoid cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                           t_struct_hmac_ctx_st) _o_ctx
                         t_struct_SHA256state_st)
                       (tptr t_struct_SHA256state_st)) :: nil))
                  (Scall None
                    (Evar _SHA256_Update (Tfunction
                                           (Tcons
                                             (tptr t_struct_SHA256state_st)
                                             (Tcons (tptr tvoid)
                                               (Tcons tuint Tnil))) tvoid
                                           cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                           t_struct_hmac_ctx_st) _o_ctx
                         t_struct_SHA256state_st)
                       (tptr t_struct_SHA256state_st)) ::
                     (Evar _pad (tarray tuchar 64)) ::
                     (Econst_int (Int.repr 64) tint) :: nil)))))))
        Sskip)
      (Scall None
        (Evar _memcpy (Tfunction
                        (Tcons (tptr tvoid)
                          (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                        (tptr tvoid) cc_default))
        ((Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
               t_struct_hmac_ctx_st) _md_ctx t_struct_SHA256state_st)
           (tptr t_struct_SHA256state_st)) ::
         (Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
               t_struct_hmac_ctx_st) _i_ctx t_struct_SHA256state_st)
           (tptr t_struct_SHA256state_st)) ::
         (Econst_int (Int.repr 108) tuint) :: nil)))))
|}.

Definition f_HMAC_Update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr t_struct_hmac_ctx_st)) ::
                (_data, (tptr tvoid)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _SHA256_Update (Tfunction
                         (Tcons (tptr t_struct_SHA256state_st)
                           (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                         cc_default))
  ((Eaddrof
     (Efield
       (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
         t_struct_hmac_ctx_st) _md_ctx t_struct_SHA256state_st)
     (tptr t_struct_SHA256state_st)) :: (Etempvar _data (tptr tvoid)) ::
   (Etempvar _len tuint) :: nil))
|}.

Definition f_HMAC_Final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr t_struct_hmac_ctx_st)) ::
                (_md, (tptr tuchar)) :: nil);
  fn_vars := ((_buf, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _SHA256_Final (Tfunction
                          (Tcons (tptr tuchar)
                            (Tcons (tptr t_struct_SHA256state_st) Tnil))
                          tvoid cc_default))
    ((Evar _buf (tarray tuchar 32)) ::
     (Eaddrof
       (Efield
         (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
           t_struct_hmac_ctx_st) _md_ctx t_struct_SHA256state_st)
       (tptr t_struct_SHA256state_st)) :: nil))
  (Ssequence
    (Scall None
      (Evar _memcpy (Tfunction
                      (Tcons (tptr tvoid)
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) (tptr tvoid)
                      cc_default))
      ((Eaddrof
         (Efield
           (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
             t_struct_hmac_ctx_st) _md_ctx t_struct_SHA256state_st)
         (tptr t_struct_SHA256state_st)) ::
       (Eaddrof
         (Efield
           (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
             t_struct_hmac_ctx_st) _o_ctx t_struct_SHA256state_st)
         (tptr t_struct_SHA256state_st)) ::
       (Econst_int (Int.repr 108) tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar _SHA256_Update (Tfunction
                               (Tcons (tptr t_struct_SHA256state_st)
                                 (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                               tvoid cc_default))
        ((Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
               t_struct_hmac_ctx_st) _md_ctx t_struct_SHA256state_st)
           (tptr t_struct_SHA256state_st)) ::
         (Evar _buf (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
         nil))
      (Scall None
        (Evar _SHA256_Final (Tfunction
                              (Tcons (tptr tuchar)
                                (Tcons (tptr t_struct_SHA256state_st) Tnil))
                              tvoid cc_default))
        ((Etempvar _md (tptr tuchar)) ::
         (Eaddrof
           (Efield
             (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
               t_struct_hmac_ctx_st) _md_ctx t_struct_SHA256state_st)
           (tptr t_struct_SHA256state_st)) :: nil)))))
|}.

Definition f_HMAC_cleanup := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr t_struct_hmac_ctx_st)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction
                  (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                  (tptr tvoid) cc_default))
  ((Etempvar _ctx (tptr t_struct_hmac_ctx_st)) ::
   (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 324) tuint) ::
   nil))
|}.

Definition v_m := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_HMAC := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tuchar)) :: (_key_len, tint) ::
                (_d, (tptr tuchar)) :: (_n, tint) :: (_md, (tptr tuchar)) ::
                nil);
  fn_vars := ((_c, t_struct_hmac_ctx_st) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _md (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sset _md (Evar _m (tarray tuchar 32)))
    Sskip)
  (Ssequence
    (Scall None
      (Evar _HMAC_Init (Tfunction
                         (Tcons (tptr t_struct_hmac_ctx_st)
                           (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                         cc_default))
      ((Eaddrof (Evar _c t_struct_hmac_ctx_st) (tptr t_struct_hmac_ctx_st)) ::
       (Etempvar _key (tptr tuchar)) :: (Etempvar _key_len tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _HMAC_Update (Tfunction
                             (Tcons (tptr t_struct_hmac_ctx_st)
                               (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                             cc_default))
        ((Eaddrof (Evar _c t_struct_hmac_ctx_st) (tptr t_struct_hmac_ctx_st)) ::
         (Etempvar _d (tptr tuchar)) :: (Etempvar _n tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _HMAC_Final (Tfunction
                              (Tcons (tptr t_struct_hmac_ctx_st)
                                (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
          ((Eaddrof (Evar _c t_struct_hmac_ctx_st)
             (tptr t_struct_hmac_ctx_st)) :: (Etempvar _md (tptr tuchar)) ::
           nil))
        (Ssequence
          (Scall None
            (Evar _HMAC_cleanup (Tfunction
                                  (Tcons (tptr t_struct_hmac_ctx_st) Tnil)
                                  tvoid cc_default))
            ((Eaddrof (Evar _c t_struct_hmac_ctx_st)
               (tptr t_struct_hmac_ctx_st)) :: nil))
          (Sreturn (Some (Etempvar _md (tptr tuchar)))))))))
|}.

Definition v_m__1 := {|
  gvar_info := (tarray tuchar 64);
  gvar_init := (Init_space 64 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_HMAC2 := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tuchar)) :: (_key_len, tint) ::
                (_d, (tptr tuchar)) :: (_n, tint) :: (_md, (tptr tuchar)) ::
                nil);
  fn_vars := ((_c, t_struct_hmac_ctx_st) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _md (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sset _md (Evar _m__1 (tarray tuchar 64)))
    Sskip)
  (Ssequence
    (Scall None
      (Evar _HMAC_Init (Tfunction
                         (Tcons (tptr t_struct_hmac_ctx_st)
                           (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid
                         cc_default))
      ((Eaddrof (Evar _c t_struct_hmac_ctx_st) (tptr t_struct_hmac_ctx_st)) ::
       (Etempvar _key (tptr tuchar)) :: (Etempvar _key_len tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _HMAC_Update (Tfunction
                             (Tcons (tptr t_struct_hmac_ctx_st)
                               (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                             cc_default))
        ((Eaddrof (Evar _c t_struct_hmac_ctx_st) (tptr t_struct_hmac_ctx_st)) ::
         (Etempvar _d (tptr tuchar)) :: (Etempvar _n tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _HMAC_Final (Tfunction
                              (Tcons (tptr t_struct_hmac_ctx_st)
                                (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
          ((Eaddrof (Evar _c t_struct_hmac_ctx_st)
             (tptr t_struct_hmac_ctx_st)) :: (Etempvar _md (tptr tuchar)) ::
           nil))
        (Ssequence
          (Scall None
            (Evar _HMAC_Init (Tfunction
                               (Tcons (tptr t_struct_hmac_ctx_st)
                                 (Tcons (tptr tuchar) (Tcons tint Tnil)))
                               tvoid cc_default))
            ((Eaddrof (Evar _c t_struct_hmac_ctx_st)
               (tptr t_struct_hmac_ctx_st)) ::
             (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
             (Etempvar _key_len tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _HMAC_Update (Tfunction
                                   (Tcons (tptr t_struct_hmac_ctx_st)
                                     (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                   tvoid cc_default))
              ((Eaddrof (Evar _c t_struct_hmac_ctx_st)
                 (tptr t_struct_hmac_ctx_st)) ::
               (Etempvar _d (tptr tuchar)) :: (Etempvar _n tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _HMAC_Final (Tfunction
                                    (Tcons (tptr t_struct_hmac_ctx_st)
                                      (Tcons (tptr tuchar) Tnil)) tvoid
                                    cc_default))
                ((Eaddrof (Evar _c t_struct_hmac_ctx_st)
                   (tptr t_struct_hmac_ctx_st)) ::
                 (Ebinop Oadd (Etempvar _md (tptr tuchar))
                   (Econst_int (Int.repr 32) tint) (tptr tuchar)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _HMAC_cleanup (Tfunction
                                        (Tcons (tptr t_struct_hmac_ctx_st)
                                          Tnil) tvoid cc_default))
                  ((Eaddrof (Evar _c t_struct_hmac_ctx_st)
                     (tptr t_struct_hmac_ctx_st)) :: nil))
                (Sreturn (Some (Etempvar _md (tptr tuchar))))))))))))
|}.

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
   Gfun(External (EF_builtin ___builtin_fabs
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin ___builtin_memcpy_aligned
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin ___builtin_annot
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin ___builtin_va_start
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin ___builtin_va_arg
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin ___builtin_va_copy
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin ___builtin_va_end
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external ___compcert_va_int32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external ___compcert_va_int64
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external ___compcert_va_float64
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin ___builtin_bswap
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin ___builtin_bswap32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin ___builtin_bswap16
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin ___builtin_fsqrt
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin ___builtin_fmax
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin ___builtin_fmin
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin ___builtin_fmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin ___builtin_fmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin ___builtin_fnmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin ___builtin_fnmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin ___builtin_read16_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin ___builtin_read32_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin ___builtin_write16_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin ___builtin_write32_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external _memcpy
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
     (tptr tvoid) cc_default)) ::
 (_memset,
   Gfun(External (EF_external _memset
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
     cc_default)) ::
 (_SHA256_Init,
   Gfun(External (EF_external _SHA256_Init
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr t_struct_SHA256state_st) Tnil) tvoid cc_default)) ::
 (_SHA256_Update,
   Gfun(External (EF_external _SHA256_Update
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr t_struct_SHA256state_st)
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid cc_default)) ::
 (_SHA256_Final,
   Gfun(External (EF_external _SHA256_Final
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tuchar) (Tcons (tptr t_struct_SHA256state_st) Tnil)) tvoid
     cc_default)) :: (_HMAC_Init, Gfun(Internal f_HMAC_Init)) ::
 (_HMAC_Update, Gfun(Internal f_HMAC_Update)) ::
 (_HMAC_Final, Gfun(Internal f_HMAC_Final)) ::
 (_HMAC_cleanup, Gfun(Internal f_HMAC_cleanup)) :: (_m, Gvar v_m) ::
 (_HMAC, Gfun(Internal f_HMAC)) :: (_m__1, Gvar v_m__1) ::
 (_HMAC2, Gfun(Internal f_HMAC2)) :: nil);
prog_main := _main
|}.

