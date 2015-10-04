(*Lenb: manually added cc_default in abou 10 places*)

Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _key_len : ident := 16%positive.
Definition _i : ident := 24%positive.
Definition _bufferIn : ident := 22%positive.
Definition _digest : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition _SHA256 : ident := 12%positive.
Definition _memcpy : ident := 10%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _text_len : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition _main : ident := 26%positive.
Definition _k_opad : ident := 19%positive.
Definition _memset : ident := 11%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition _tk2 : ident := 21%positive.
Definition _k_ipad : ident := 18%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition _text : ident := 13%positive.
Definition _hmac_sha256 : ident := 25%positive.
Definition _key : ident := 15%positive.
Definition _bufferOut : ident := 23%positive.
Definition _tk : ident := 20%positive.

Definition f_hmac_sha256 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_text, (tptr tuchar)) :: (_text_len, tint) ::
                (_key, (tptr tuchar)) :: (_key_len, tint) ::
                (_digest, (tptr tvoid)) :: nil);
  fn_vars := ((_k_ipad, (tarray tuchar 65)) ::
              (_k_opad, (tarray tuchar 65)) :: (_tk, (tarray tuchar 32)) ::
              (_tk2, (tarray tuchar 32)) ::
              (_bufferIn, (tarray tuchar 1024)) ::
              (_bufferOut, (tarray tuchar 1024)) :: nil);
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ogt (Etempvar _key_len tint)
                 (Econst_int (Int.repr 64) tint) tint)
    (Ssequence
      (Scall None
        (Evar _SHA256 (Tfunction
                        (Tcons (tptr tuchar)
                          (Tcons tuint (Tcons (tptr tuchar) Tnil)))
                        tvoid cc_default))
        ((Etempvar _key (tptr tuchar)) :: (Etempvar _key_len tint) ::
         (Evar _tk (tarray tuchar 32)) :: nil))
      (Ssequence
        (Sset _key (Evar _tk (tarray tuchar 32)))
        (Sset _key_len (Econst_int (Int.repr 32) tint))))
    Sskip)
  (Ssequence
    (Scall None
      (Evar _memset (Tfunction
                      (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                      (tptr tvoid) cc_default))
      ((Evar _k_ipad (tarray tuchar 65)) :: (Econst_int (Int.repr 0) tint) ::
       (Econst_int (Int.repr 65) tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar _memset (Tfunction
                        (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                        (tptr tvoid) cc_default))
        ((Evar _k_opad (tarray tuchar 65)) ::
         (Econst_int (Int.repr 0) tint) ::
         (Econst_int (Int.repr 65) tuint) :: nil))
      (Ssequence
        (Scall None
          (Evar _memcpy (Tfunction
                          (Tcons (tptr tvoid)
                            (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                          (tptr tvoid) cc_default))
          ((Evar _k_ipad (tarray tuchar 65)) ::
           (Etempvar _key (tptr tuchar)) :: (Etempvar _key_len tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _memcpy (Tfunction
                            (Tcons (tptr tvoid)
                              (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                            (tptr tvoid) cc_default))
            ((Evar _k_opad (tarray tuchar 65)) ::
             (Etempvar _key (tptr tuchar)) :: (Etempvar _key_len tint) ::
             nil))
          (Ssequence
            (Ssequence
              (Sset _i (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                 (Econst_int (Int.repr 64) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _k_ipad (tarray tuchar 65))
                          (Etempvar _i tint) (tptr tuchar)) tuchar)
                      (Ebinop Oxor
                        (Ederef
                          (Ebinop Oadd (Evar _k_ipad (tarray tuchar 65))
                            (Etempvar _i tint) (tptr tuchar)) tuchar)
                        (Econst_int (Int.repr 54) tint) tint))
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _k_opad (tarray tuchar 65))
                          (Etempvar _i tint) (tptr tuchar)) tuchar)
                      (Ebinop Oxor
                        (Ederef
                          (Ebinop Oadd (Evar _k_opad (tarray tuchar 65))
                            (Etempvar _i tint) (tptr tuchar)) tuchar)
                        (Econst_int (Int.repr 92) tint) tint))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Ssequence
              (Scall None
                (Evar _memset (Tfunction
                                (Tcons (tptr tvoid)
                                  (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                ((Evar _bufferIn (tarray tuchar 1024)) ::
                 (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 1024) tint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _memcpy (Tfunction
                                  (Tcons (tptr tvoid)
                                    (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                  (tptr tvoid) cc_default))
                  ((Evar _bufferIn (tarray tuchar 1024)) ::
                   (Evar _k_ipad (tarray tuchar 65)) ::
                   (Econst_int (Int.repr 64) tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                    (tptr tvoid) cc_default))
                    ((Ebinop Oadd (Evar _bufferIn (tarray tuchar 1024))
                       (Econst_int (Int.repr 64) tint) (tptr tuchar)) ::
                     (Etempvar _text (tptr tuchar)) ::
                     (Etempvar _text_len tint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _SHA256 (Tfunction
                                      (Tcons (tptr tuchar)
                                        (Tcons tuint
                                          (Tcons (tptr tuchar) Tnil))) tvoid cc_default))
                      ((Evar _bufferIn (tarray tuchar 1024)) ::
                       (Ebinop Oadd (Econst_int (Int.repr 64) tint)
                         (Etempvar _text_len tint) tint) ::
                       (Evar _tk2 (tarray tuchar 32)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _memset (Tfunction
                                        (Tcons (tptr tvoid)
                                          (Tcons tint (Tcons tuint Tnil)))
                                        (tptr tvoid) cc_default))
                        ((Evar _bufferOut (tarray tuchar 1024)) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Econst_int (Int.repr 1024) tint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _memcpy (Tfunction
                                          (Tcons (tptr tvoid)
                                            (Tcons (tptr tvoid)
                                              (Tcons tuint Tnil)))
                                          (tptr tvoid) cc_default))
                          ((Evar _bufferOut (tarray tuchar 1024)) ::
                           (Evar _k_opad (tarray tuchar 65)) ::
                           (Econst_int (Int.repr 64) tint) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _memcpy (Tfunction
                                            (Tcons (tptr tvoid)
                                              (Tcons (tptr tvoid)
                                                (Tcons tuint Tnil)))
                                            (tptr tvoid) cc_default))
                            ((Ebinop Oadd
                               (Evar _bufferOut (tarray tuchar 1024))
                               (Econst_int (Int.repr 64) tint) (tptr tuchar)) ::
                             (Evar _tk2 (tarray tuchar 32)) ::
                             (Econst_int (Int.repr 32) tint) :: nil))
                          (Ssequence
                            (Scall None
                             (Evar _SHA256 (Tfunction
                                            (Tcons (tptr tuchar)
                                              (Tcons tuint
                                                (Tcons (tptr tuchar) Tnil)))
                                            tvoid cc_default))
                             ((Evar _bufferOut (tarray tuchar 1024)) ::
                              (Ebinop Oadd (Econst_int (Int.repr 64) tint)
                                (Econst_int (Int.repr 32) tint) tint) ::
                              (Etempvar _digest (tptr tvoid)) :: nil))
                          (Sreturn None)))))))))))))))
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
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
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
     cc_default))::
 (_SHA256,
   Gfun(External (EF_external _SHA256
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tuchar) (Tcons tuint (Tcons (tptr tuchar) Tnil))) tvoid cc_default)) ::
 (_hmac_sha256, Gfun(Internal f_hmac_sha256)) :: nil);
prog_main := _main
|}.

