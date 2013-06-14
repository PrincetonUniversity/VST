Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _sumarray : ident := 15%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _x : ident := 14%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition _main : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition _four : ident := 16%positive.
Definition _s : ident := 13%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition _i : ident := 12%positive.
Definition _n : ident := 11%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition _a : ident := 10%positive.
Definition _s' : ident := 18%positive.


Definition f_sumarray := {|
  fn_return := tint;
  fn_params := ((_a, (tptr tint)) :: (_n, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_s, tint) :: (_x, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _s (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Swhile
        (Ebinop Olt (Etempvar _i tint) (Etempvar _n tint) tint)
        (Ssequence
          (Sset _x
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tint)) (Etempvar _i tint)
                (tptr tint)) tint))
          (Ssequence
            (Sset _s
              (Ebinop Oadd (Etempvar _s tint) (Etempvar _x tint) tint))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint)))))
      (Sreturn (Some (Etempvar _s tint))))))
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
  fn_temps := ((_s, tint) :: (_s', tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _s')
      (Evar _sumarray (Tfunction (Tcons (tptr tint) (Tcons tint Tnil)) tint))
      ((Evar _four (tarray tint 4)) :: (Econst_int (Int.repr 4) tint) :: nil))
    (Sset _s (Etempvar _s' tint)))
  (Sreturn (Some (Etempvar _s tint))))
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
 (_sumarray, Gfun(Internal f_sumarray)) :: (_four, Gvar v_four) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_main := _main
|}.

