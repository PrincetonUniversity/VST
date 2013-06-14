Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _x : ident := 15%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _y : ident := 14%positive.
Definition _intpair_serialize : ident := 19%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition _p : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition _buf : ident := 18%positive.
Definition _struct_intpair : ident := 16%positive.
Definition _main : ident := 27%positive.
Definition _struct_message : ident := 13%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition _ser : ident := 25%positive.
Definition _bufsize : ident := 12%positive.
Definition _des : ident := 26%positive.
Definition _len : ident := 24%positive.
Definition _q : ident := 23%positive.
Definition _serialize : ident := 11%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition _intpair_deserialize : ident := 21%positive.
Definition _deserialize : ident := 10%positive.
Definition _intpair_message : ident := 22%positive.
Definition _length : ident := 20%positive.
Definition _len' : ident := 28%positive.

Definition t_struct_message :=
   (Tstruct _struct_message
     (Fcons _bufsize tint
       (Fcons _serialize
         (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil))
                 tint))
         (Fcons _deserialize
           (tptr (Tfunction
                   (Tcons (tptr tvoid)
                     (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid)) Fnil)))
     noattr).
Definition t_struct_intpair :=
   (Tstruct _struct_intpair (Fcons _x tint (Fcons _y tint Fnil)) noattr).

Definition f_intpair_serialize := {|
  fn_return := tint;
  fn_params := ((_p, (tptr t_struct_intpair)) :: (_buf, (tptr tuchar)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_x, tint) :: (_y, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x
    (Efield (Ederef (Etempvar _p (tptr t_struct_intpair)) t_struct_intpair)
      _x tint))
  (Ssequence
    (Sset _y
      (Efield (Ederef (Etempvar _p (tptr t_struct_intpair)) t_struct_intpair)
        _y tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Ecast (Etempvar _buf (tptr tuchar)) (tptr tint))
            (Econst_int (Int.repr 0) tint) (tptr tint)) tint)
        (Etempvar _x tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Ecast (Etempvar _buf (tptr tuchar)) (tptr tint))
              (Econst_int (Int.repr 1) tint) (tptr tint)) tint)
          (Etempvar _y tint))
        (Sreturn (Some (Econst_int (Int.repr 8) tint)))))))
|}.

Definition f_intpair_deserialize := {|
  fn_return := tvoid;
  fn_params := ((_p, (tptr t_struct_intpair)) :: (_buf, (tptr tuchar)) ::
                (_length, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, tint) :: (_y, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _x
    (Ederef
      (Ebinop Oadd (Ecast (Etempvar _buf (tptr tuchar)) (tptr tint))
        (Econst_int (Int.repr 0) tint) (tptr tint)) tint))
  (Ssequence
    (Sset _y
      (Ederef
        (Ebinop Oadd (Ecast (Etempvar _buf (tptr tuchar)) (tptr tint))
          (Econst_int (Int.repr 1) tint) (tptr tint)) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr t_struct_intpair)) t_struct_intpair) _x
          tint) (Etempvar _x tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr t_struct_intpair)) t_struct_intpair)
            _y tint) (Etempvar _y tint))
        (Sreturn None)))))
|}.

Definition v_intpair_message := {|
  gvar_info := t_struct_message;
  gvar_init := (Init_int32 (Int.repr 8) ::
                Init_addrof _intpair_serialize (Int.repr 0) ::
                Init_addrof _intpair_deserialize (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_main := {|
  fn_return := tint;
  fn_params := nil;
  fn_vars := ((_p, t_struct_intpair) :: (_q, t_struct_intpair) ::
              (_buf, (tarray tuchar 8)) :: nil);
  fn_temps := ((_len, tint) :: (_x, tint) :: (_y, tint) ::
               (_ser,
                (tptr (Tfunction
                        (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil)) tint))) ::
               (_des,
                (tptr (Tfunction
                        (Tcons (tptr tvoid)
                          (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid))) ::
               (_len', tint) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _p t_struct_intpair) _x tint)
    (Econst_int (Int.repr 1) tint))
  (Ssequence
    (Sassign (Efield (Evar _p t_struct_intpair) _y tint)
      (Econst_int (Int.repr 2) tint))
    (Ssequence
      (Sset _ser
        (Efield (Evar _intpair_message t_struct_message) _serialize
          (tptr (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tuchar) Tnil))
                  tint))))
      (Ssequence
        (Ssequence
          (Scall (Some _len')
            (Etempvar _ser (tptr (Tfunction
                                   (Tcons (tptr tvoid)
                                     (Tcons (tptr tuchar) Tnil)) tint)))
            ((Eaddrof (Evar _p t_struct_intpair) (tptr t_struct_intpair)) ::
             (Evar _buf (tarray tuchar 8)) :: nil))
          (Sset _len (Etempvar _len' tint)))
        (Ssequence
          (Sset _des
            (Efield (Evar _intpair_message t_struct_message) _deserialize
              (tptr (Tfunction
                      (Tcons (tptr tvoid)
                        (Tcons (tptr tuchar) (Tcons tint Tnil))) tvoid))))
          (Ssequence
            (Scall None
              (Etempvar _des (tptr (Tfunction
                                     (Tcons (tptr tvoid)
                                       (Tcons (tptr tuchar)
                                         (Tcons tint Tnil))) tvoid)))
              ((Eaddrof (Evar _q t_struct_intpair) (tptr t_struct_intpair)) ::
               (Evar _buf (tarray tuchar 8)) ::
               (Econst_int (Int.repr 8) tint) :: nil))
            (Ssequence
              (Sset _x (Efield (Evar _q t_struct_intpair) _x tint))
              (Ssequence
                (Sset _y (Efield (Evar _q t_struct_intpair) _y tint))
                (Sreturn (Some (Ebinop Oadd (Etempvar _x tint)
                                 (Etempvar _y tint) tint)))))))))))
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
 (_intpair_serialize, Gfun(Internal f_intpair_serialize)) ::
 (_intpair_deserialize, Gfun(Internal f_intpair_deserialize)) ::
 (_intpair_message, Gvar v_intpair_message) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_main := _main
|}.

