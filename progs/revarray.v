Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _t : ident := 15%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _s : ident := 14%positive.
Definition _main : ident := 19%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition _four : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition _i : ident := 18%positive.
Definition _reverse : ident := 16%positive.
Definition _hi : ident := 13%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition _lo : ident := 12%positive.
Definition _n : ident := 11%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition _a : ident := 10%positive.


Definition f_reverse := {|
  fn_return := tvoid;
  fn_params := ((_a, (tptr tint)) :: (_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_lo, tint) :: (_hi, tint) :: (_s, tint) :: (_t, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _lo (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _hi (Etempvar _n tint))
    (Ssequence
      (Swhile
        (Ebinop Olt (Etempvar _lo tint)
          (Ebinop Osub (Etempvar _hi tint) (Econst_int (Int.repr 1) tint)
            tint) tint)
        (Ssequence
          (Sset _t
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _lo tint)
                (tptr tint)) tint))
          (Ssequence
            (Sset _s
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tint))
                  (Ebinop Osub (Etempvar _hi tint)
                    (Econst_int (Int.repr 1) tint) tint) (tptr tint)) tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _a (tptr tint))
                    (Ebinop Osub (Etempvar _hi tint)
                      (Econst_int (Int.repr 1) tint) tint) (tptr tint)) tint)
                (Etempvar _t tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _a (tptr tint))
                      (Etempvar _lo tint) (tptr tint)) tint)
                  (Etempvar _s tint))
                (Ssequence
                  (Sset _lo
                    (Ebinop Oadd (Etempvar _lo tint)
                      (Econst_int (Int.repr 1) tint) tint))
                  (Sset _hi
                    (Ebinop Osub (Etempvar _hi tint)
                      (Econst_int (Int.repr 1) tint) tint))))))))
      (Sreturn None))))
|}.

Definition v_four := {|
  gvar_info := (tarray tint 4);
  gvar_init := (Init_int32 (Int.repr 1) :: Init_int32 (Int.repr 2) ::
                Init_int32 (Int.repr 3) :: Init_int32 (Int.repr 4) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_main := {|
  fn_return := tint;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _reverse (Tfunction (Tcons (tptr tint) (Tcons tint Tnil)) tvoid))
    ((Evar _four (tarray tint 4)) :: (Econst_int (Int.repr 4) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _reverse (Tfunction (Tcons (tptr tint) (Tcons tint Tnil)) tvoid))
      ((Evar _four (tarray tint 4)) :: (Econst_int (Int.repr 4) tint) :: nil))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
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
 (_reverse, Gfun(Internal f_reverse)) :: (_four, Gvar v_four) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_main := _main
|}.

