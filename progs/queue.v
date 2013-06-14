Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _main : ident := 31%positive.
Definition _a : ident := 15%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _i : ident := 29%positive.
Definition _b : ident := 14%positive.
Definition _j : ident := 30%positive.
Definition _make_elem : ident := 28%positive.
Definition _Q : ident := 19%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition _head : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition _struct_fifo : ident := 18%positive.
Definition _tail : ident := 16%positive.
Definition _fifo_get : ident := 27%positive.
Definition _next : ident := 13%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition _fifo_empty : ident := 25%positive.
Definition _struct_elem : ident := 12%positive.
Definition _n : ident := 26%positive.
Definition _fifo_put : ident := 24%positive.
Definition _t : ident := 23%positive.
Definition _freeN : ident := 11%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition _p : ident := 21%positive.
Definition _mallocN : ident := 10%positive.
Definition _h : ident := 22%positive.
Definition _fifo_new : ident := 20%positive.
Definition _Q'1 : ident := 34%positive.
Definition _p'1 : ident := 35%positive.
Definition _p'3 : ident := 37%positive.
Definition _p' : ident := 33%positive.
Definition _p'2 : ident := 36%positive.
Definition _Q' : ident := 32%positive.

Definition t_struct_fifo :=
   (Tstruct _struct_fifo
     (Fcons _head
       (tptr (Tstruct _struct_elem
               (Fcons _a tint
                 (Fcons _b tint
                   (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
               noattr))
       (Fcons _tail
         (tptr (Tstruct _struct_elem
                 (Fcons _a tint
                   (Fcons _b tint
                     (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
                 noattr)) Fnil)) noattr).
Definition t_struct_elem :=
   (Tstruct _struct_elem
     (Fcons _a tint
       (Fcons _b tint (Fcons _next (Tcomp_ptr _struct_elem noattr) Fnil)))
     noattr).

Definition f_fifo_new := {|
  fn_return := (tptr t_struct_fifo);
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_Q, (tptr t_struct_fifo)) :: (_Q', (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _Q')
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid)))
      ((Econst_int (Int.repr 8) tuint) :: nil))
    (Sset _Q (Ecast (Etempvar _Q' (tptr tvoid)) (tptr t_struct_fifo))))
  (Ssequence
    (Sassign
      (Efield (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo) _head
        (tptr t_struct_elem))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sassign
        (Efield (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo)
          _tail (tptr t_struct_elem))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Sreturn (Some (Etempvar _Q (tptr t_struct_fifo)))))))
|}.

Definition f_fifo_put := {|
  fn_return := tvoid;
  fn_params := ((_Q, (tptr t_struct_fifo)) :: (_p, (tptr t_struct_elem)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr t_struct_elem)) :: (_t, (tptr t_struct_elem)) ::
               nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield (Ederef (Etempvar _p (tptr t_struct_elem)) t_struct_elem) _next
      (tptr t_struct_elem))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sset _h
      (Efield (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo) _head
        (tptr t_struct_elem)))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Sassign
            (Efield (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo)
              _head (tptr t_struct_elem)) (Etempvar _p (tptr t_struct_elem)))
          (Sassign
            (Efield (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo)
              _tail (tptr t_struct_elem)) (Etempvar _p (tptr t_struct_elem))))
        (Ssequence
          (Sset _t
            (Efield (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo)
              _tail (tptr t_struct_elem)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _t (tptr t_struct_elem)) t_struct_elem)
                _next (tptr t_struct_elem))
              (Etempvar _p (tptr t_struct_elem)))
            (Sassign
              (Efield
                (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo)
                _tail (tptr t_struct_elem))
              (Etempvar _p (tptr t_struct_elem))))))
      (Sreturn None))))
|}.

Definition f_fifo_empty := {|
  fn_return := tint;
  fn_params := ((_Q, (tptr t_struct_fifo)) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr t_struct_elem)) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo) _head
      (tptr t_struct_elem)))
  (Sreturn (Some (Ebinop Oeq (Etempvar _h (tptr t_struct_elem))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))))
|}.

Definition f_fifo_get := {|
  fn_return := (tptr t_struct_elem);
  fn_params := ((_Q, (tptr t_struct_fifo)) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr t_struct_elem)) :: (_n, (tptr t_struct_elem)) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo) _head
      (tptr t_struct_elem)))
  (Ssequence
    (Sset _n
      (Efield (Ederef (Etempvar _h (tptr t_struct_elem)) t_struct_elem) _next
        (tptr t_struct_elem)))
    (Ssequence
      (Sassign
        (Efield (Ederef (Etempvar _Q (tptr t_struct_fifo)) t_struct_fifo)
          _head (tptr t_struct_elem)) (Etempvar _n (tptr t_struct_elem)))
      (Sreturn (Some (Etempvar _h (tptr t_struct_elem)))))))
|}.

Definition f_make_elem := {|
  fn_return := (tptr t_struct_elem);
  fn_params := ((_a, tint) :: (_b, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr t_struct_elem)) :: (_p', (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _p')
      (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid)))
      ((Econst_int (Int.repr 12) tuint) :: nil))
    (Sset _p (Etempvar _p' (tptr tvoid))))
  (Ssequence
    (Sassign
      (Efield (Ederef (Etempvar _p (tptr t_struct_elem)) t_struct_elem) _a
        tint) (Etempvar _a tint))
    (Ssequence
      (Sassign
        (Efield (Ederef (Etempvar _p (tptr t_struct_elem)) t_struct_elem) _b
          tint) (Etempvar _b tint))
      (Sreturn (Some (Etempvar _p (tptr t_struct_elem)))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_j, tint) :: (_Q, (tptr t_struct_fifo)) ::
               (_p, (tptr t_struct_elem)) :: (_p'3, (tptr t_struct_elem)) ::
               (_p'2, (tptr t_struct_elem)) ::
               (_p'1, (tptr t_struct_elem)) ::
               (_Q'1, (tptr t_struct_fifo)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _Q'1) (Evar _fifo_new (Tfunction Tnil (tptr t_struct_fifo)))
      nil)
    (Sset _Q (Etempvar _Q'1 (tptr t_struct_fifo))))
  (Ssequence
    (Ssequence
      (Scall (Some _p'1)
        (Evar _make_elem (Tfunction (Tcons tint (Tcons tint Tnil))
                           (tptr t_struct_elem)))
        ((Econst_int (Int.repr 1) tint) :: (Econst_int (Int.repr 10) tint) ::
         nil))
      (Sset _p (Etempvar _p'1 (tptr t_struct_elem))))
    (Ssequence
      (Scall None
        (Evar _fifo_put (Tfunction
                          (Tcons (tptr t_struct_fifo)
                            (Tcons (tptr t_struct_elem) Tnil)) tvoid))
        ((Etempvar _Q (tptr t_struct_fifo)) ::
         (Etempvar _p (tptr t_struct_elem)) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _p'2)
            (Evar _make_elem (Tfunction (Tcons tint (Tcons tint Tnil))
                               (tptr t_struct_elem)))
            ((Econst_int (Int.repr 2) tint) ::
             (Econst_int (Int.repr 20) tint) :: nil))
          (Sset _p (Etempvar _p'2 (tptr t_struct_elem))))
        (Ssequence
          (Scall None
            (Evar _fifo_put (Tfunction
                              (Tcons (tptr t_struct_fifo)
                                (Tcons (tptr t_struct_elem) Tnil)) tvoid))
            ((Etempvar _Q (tptr t_struct_fifo)) ::
             (Etempvar _p (tptr t_struct_elem)) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _p'3)
                (Evar _fifo_get (Tfunction (Tcons (tptr t_struct_fifo) Tnil)
                                  (tptr t_struct_elem)))
                ((Etempvar _Q (tptr t_struct_fifo)) :: nil))
              (Sset _p (Etempvar _p'3 (tptr t_struct_elem))))
            (Ssequence
              (Sset _i
                (Efield
                  (Ederef (Etempvar _p (tptr t_struct_elem)) t_struct_elem)
                  _a tint))
              (Ssequence
                (Sset _j
                  (Efield
                    (Ederef (Etempvar _p (tptr t_struct_elem)) t_struct_elem)
                    _b tint))
                (Ssequence
                  (Scall None
                    (Evar _freeN (Tfunction
                                   (Tcons (tptr tvoid) (Tcons tint Tnil))
                                   tvoid))
                    ((Etempvar _p (tptr t_struct_elem)) ::
                     (Econst_int (Int.repr 12) tuint) :: nil))
                  (Sreturn (Some (Ebinop Oadd (Etempvar _i tint)
                                   (Etempvar _j tint) tint))))))))))))
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
 (_mallocN,
   Gfun(External (EF_external _mallocN
                   (mksignature (AST.Tint :: nil) (Some AST.Tint)))
     (Tcons tint Tnil) (tptr tvoid))) ::
 (_freeN,
   Gfun(External (EF_external _freeN
                   (mksignature (AST.Tint :: AST.Tint :: nil) None))
     (Tcons (tptr tvoid) (Tcons tint Tnil)) tvoid)) ::
 (_fifo_new, Gfun(Internal f_fifo_new)) ::
 (_fifo_put, Gfun(Internal f_fifo_put)) ::
 (_fifo_empty, Gfun(Internal f_fifo_empty)) ::
 (_fifo_get, Gfun(Internal f_fifo_get)) ::
 (_make_elem, Gfun(Internal f_make_elem)) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_main := _main
|}.

