Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _main : ident := 15%positive.
Definition _h : ident := 7%positive.
Definition ___builtin_annot_intval : ident := 3%positive.
Definition ___builtin_fabs : ident := 1%positive.
Definition _r : ident := 14%positive.
Definition _s : ident := 9%positive.
Definition _three : ident := 4%positive.
Definition _p : ident := 8%positive.
Definition _reverse : ident := 13%positive.
Definition _t : ident := 6%positive.
Definition _v : ident := 12%positive.
Definition _w : ident := 11%positive.
Definition _struct_list : ident := 5%positive.
Definition ___builtin_memcpy_aligned : ident := 2%positive.
Definition _sumlist : ident := 10%positive.

Definition t_struct_list :=
   (Tstruct _struct_list
     (Fcons _h tint (Fcons _t (Tcomp_ptr _struct_list noattr) Fnil)) noattr).

Definition v_three := {|
  gvar_info := (tarray t_struct_list 3);
  gvar_init := (Init_int32 (Int.repr 1) :: Init_addrof _three (Int.repr 8) ::
                Init_int32 (Int.repr 2) ::
                Init_addrof _three (Int.repr 16) ::
                Init_int32 (Int.repr 3) :: Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_sumlist := {|
  fn_return := tint;
  fn_params := ((_p, (tptr t_struct_list)) :: nil);
  fn_vars := nil;
  fn_temps := ((_s, tint) :: (_t, (tptr t_struct_list)) :: (_h, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _s (Ecast (Econst_int (Int.repr 0) tint) tint))
  (Ssequence
    (Sset _t (Ecast (Etempvar _p (tptr t_struct_list)) (tptr t_struct_list)))
    (Ssequence
      (Swhile
        (Etempvar _t (tptr t_struct_list))
        (Ssequence
          (Sset _h
            (Ecast
              (Efield
                (Ederef (Etempvar _t (tptr t_struct_list)) t_struct_list) _h
                tint) tint))
          (Ssequence
            (Sset _t
              (Ecast
                (Efield
                  (Ederef (Etempvar _t (tptr t_struct_list)) t_struct_list)
                  _t (tptr t_struct_list)) (tptr t_struct_list)))
            (Sset _s
              (Ecast (Ebinop Oadd (Etempvar _s tint) (Etempvar _h tint) tint)
                tint)))))
      (Sreturn (Some (Etempvar _s tint))))))
|}.

Definition f_reverse := {|
  fn_return := (tptr t_struct_list);
  fn_params := ((_p, (tptr t_struct_list)) :: nil);
  fn_vars := nil;
  fn_temps := ((_w, (tptr t_struct_list)) :: (_t, (tptr t_struct_list)) ::
               (_v, (tptr t_struct_list)) :: nil);
  fn_body :=
(Ssequence
  (Sset _w
    (Ecast (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
      (tptr t_struct_list)))
  (Ssequence
    (Sset _v (Ecast (Etempvar _p (tptr t_struct_list)) (tptr t_struct_list)))
    (Ssequence
      (Swhile
        (Etempvar _v (tptr t_struct_list))
        (Ssequence
          (Sset _t
            (Ecast
              (Efield
                (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list) _t
                (tptr t_struct_list)) (tptr t_struct_list)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _v (tptr t_struct_list)) t_struct_list) _t
                (tptr t_struct_list)) (Etempvar _w (tptr t_struct_list)))
            (Ssequence
              (Sset _w
                (Ecast (Etempvar _v (tptr t_struct_list))
                  (tptr t_struct_list)))
              (Sset _v
                (Ecast (Etempvar _t (tptr t_struct_list))
                  (tptr t_struct_list)))))))
      (Sreturn (Some (Etempvar _w (tptr t_struct_list)))))))
|}.

(* as produced by Clightgen, version as of 6 jan 2012 ...
Definition f_main := {|
  fn_return := tint;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_r, (tptr t_struct_list)) :: (_s, tint) ::
               (17%positive, tint) :: (16%positive, (tptr t_struct_list)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some 16%positive)
      (Evar _reverse (Tfunction (Tcons (tptr t_struct_list) Tnil)
                       (tptr t_struct_list)))
      ((Evar _three (tarray t_struct_list 3)) :: nil))
    (Sset _r
      (Ecast (Etempvar 16%positive (tptr t_struct_list))
        (tptr t_struct_list))))
  (Ssequence
    (Ssequence
      (Scall (Some 17%positive)
        (Evar _sumlist (Tfunction (Tcons (tptr t_struct_list) Tnil) tint))
        ((Etempvar _r (tptr t_struct_list)) :: nil))
      (Sset _s (Ecast (Etempvar 17%positive tint) tint)))
    (Sreturn (Some (Etempvar _s tint)))))
|}.
*)

Definition f_main := {|
  fn_return := tint;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_r, (tptr t_struct_list)) :: (_s, tint) :: nil);
  fn_body :=
(Ssequence
    (Scall (Some _r)
      (Evar _reverse (Tfunction (Tcons (tptr t_struct_list) Tnil)
                       (tptr t_struct_list)))
      ((Evar _three (tarray t_struct_list 3)) :: nil))
  (Ssequence
      (Scall (Some _s)
        (Evar _sumlist (Tfunction (Tcons (tptr t_struct_list) Tnil) tint))
        ((Etempvar _r (tptr t_struct_list)) :: nil))
    (Sreturn (Some (Etempvar _s tint)))))
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
 (_three, Gvar v_three) :: (_sumlist, Gfun(Internal f_sumlist)) ::
 (_reverse, Gfun(Internal f_reverse)) :: (_main, Gfun(Internal f_main)) ::
 nil);
prog_main := _main
|}.

