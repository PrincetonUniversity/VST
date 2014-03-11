Require Import Clightdefs.

Local Open Scope Z_scope.

Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition _do_or : ident := 12%positive.
Definition _a : ident := 10%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _main : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition _b : ident := 11%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition _do_and : ident := 13%positive.


Definition f_do_or := {|
  fn_return := tbool;
  fn_params := ((_a, tbool) :: (_b, tbool) :: nil);
  fn_vars := nil;
  fn_temps := ((15%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Etempvar _a tbool)
    (Sset 15%positive (Econst_int (Int.repr 1) tint))
    (Ssequence
      (Sset 15%positive (Ecast (Etempvar _b tbool) tbool))
      (Sset 15%positive (Ecast (Etempvar 15%positive tbool) tint))))
  (Sreturn (Some (Etempvar 15%positive tint))))
|}.

Definition f_do_and := {|
  fn_return := tbool;
  fn_params := ((_a, tbool) :: (_b, tbool) :: nil);
  fn_vars := nil;
  fn_temps := ((16%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Etempvar _a tbool)
    (Ssequence
      (Sset 16%positive (Ecast (Etempvar _b tbool) tbool))
      (Sset 16%positive (Ecast (Etempvar 16%positive tbool) tint)))
    (Sset 16%positive (Econst_int (Int.repr 0) tint)))
  (Sreturn (Some (Etempvar 16%positive tint))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 0) tint)))
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
 (_do_or, Gfun(Internal f_do_or)) :: (_do_and, Gfun(Internal f_do_and)) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_main := _main
|}.

