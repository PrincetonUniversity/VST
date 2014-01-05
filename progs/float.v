Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _y1 : ident := 15%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _s : ident := 14%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition _y2 : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition _main : ident := 18%positive.
Definition _x1 : ident := 16%positive.
Definition _struct_foo : ident := 13%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition _x : ident := 12%positive.
Definition _y : ident := 11%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition _z : ident := 10%positive.

Definition t_struct_foo :=
   (Tstruct _struct_foo
     (Fcons _x tint (Fcons _y tfloat (Fcons _z tdouble Fnil))) noattr).

Definition v_s := {|
  gvar_info := t_struct_foo;
  gvar_init := (Init_int32 (Int.repr 5) ::
                Init_float32 (Float.double_of_bits (Int64.repr 4614861056357957632)) ::
                Init_float64 (Float.double_of_bits (Int64.repr 0)) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_main := {|
  fn_return := tint;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_y1, tdouble) :: (_x1, tint) :: (_y2, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _y1 (Efield (Evar _s t_struct_foo) _y tfloat))
  (Ssequence
    (Sset _x1 (Efield (Evar _s t_struct_foo) _x tint))
    (Ssequence
      (Sset _y2 (Ecast (Efield (Evar _s t_struct_foo) _y tfloat) tint))
      (Ssequence
        (Sset _y1 (Efield (Evar _s t_struct_foo) _z tdouble))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
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
     (Tcons (tptr tschar) (Tcons tint Tnil)) tint)) :: (_s, Gvar v_s) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_main := _main
|}.

