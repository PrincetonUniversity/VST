Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _struct_b : ident := 15%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _y1 : ident := 14%positive.
Definition _p : ident := 19%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition _z1 : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition _struct_c : ident := 18%positive.
Definition _z2 : ident := 16%positive.
Definition _y2 : ident := 13%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition _struct_a : ident := 12%positive.
Definition _main : ident := 23%positive.
Definition _x1 : ident := 11%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition _get : ident := 21%positive.
Definition _x2 : ident := 10%positive.
Definition _set : ident := 22%positive.
Definition _i : ident := 20%positive.

Definition t_struct_b :=
   (Tstruct _struct_b
     (Fcons _y1
       (Tstruct _struct_a (Fcons _x1 tint (Fcons _x2 tint Fnil)) noattr)
       (Fcons _y2
         (Tstruct _struct_a (Fcons _x1 tint (Fcons _x2 tint Fnil)) noattr)
         Fnil)) noattr).
Definition t_struct_c :=
   (Tstruct _struct_c
     (Fcons _z1
       (Tstruct _struct_b
         (Fcons _y1
           (Tstruct _struct_a (Fcons _x1 tint (Fcons _x2 tint Fnil)) noattr)
           (Fcons _y2
             (Tstruct _struct_a (Fcons _x1 tint (Fcons _x2 tint Fnil))
               noattr) Fnil)) noattr)
       (Fcons _z2
         (Tstruct _struct_b
           (Fcons _y1
             (Tstruct _struct_a (Fcons _x1 tint (Fcons _x2 tint Fnil))
               noattr)
             (Fcons _y2
               (Tstruct _struct_a (Fcons _x1 tint (Fcons _x2 tint Fnil))
                 noattr) Fnil)) noattr) Fnil)) noattr).
Definition t_struct_a :=
   (Tstruct _struct_a (Fcons _x1 tint (Fcons _x2 tint Fnil)) noattr).

Definition v_p := {|
  gvar_info := t_struct_c;
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_get := {|
  fn_return := tint;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i
    (Efield
      (Efield (Efield (Evar _p t_struct_c) _z2 t_struct_b) _y2 t_struct_a)
      _x2 tint))
  (Sreturn (Some (Etempvar _i tint))))
|}.

Definition f_set := {|
  fn_return := tvoid;
  fn_params := ((_i, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Efield (Efield (Evar _p t_struct_c) _z2 t_struct_b) _y2 t_struct_a)
      _x2 tint) (Etempvar _i tint))
  (Sreturn None))
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
     (Tcons (tptr tschar) (Tcons tint Tnil)) tint)) :: (_p, Gvar v_p) ::
 (_get, Gfun(Internal f_get)) :: (_set, Gfun(Internal f_set)) :: nil);
prog_main := _main
|}.

