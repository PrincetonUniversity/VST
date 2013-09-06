Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _previous : ident := 16%positive.
Definition _main : ident := 24%positive.
Definition _next : ident := 22%positive.
Definition _sortedvalue : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition _head : ident := 12%positive.
Definition _struct_list : ident := 10%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _sorted : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition _insert_value : ident := 19%positive.
Definition _tail : ident := 11%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition _p : ident := 21%positive.
Definition _guard : ident := 18%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition _insert_node : ident := 13%positive.
Definition _index : ident := 15%positive.
Definition _insertionsort : ident := 23%positive.
Definition _insert : ident := 20%positive.
Definition _guard'1 : ident := 26%positive.
Definition _sorted' : ident := 27%positive.
Definition _guard' : ident := 25%positive.

Definition t_struct_list :=
   (Tstruct _struct_list
     (Fcons _head tint (Fcons _tail (Tcomp_ptr _struct_list noattr) Fnil))
     noattr).

Definition f_insert := {|
  fn_return := (tptr t_struct_list);
  fn_params := ((_insert_node, (tptr t_struct_list)) ::
                (_sorted, (tptr t_struct_list)) :: nil);
  fn_vars := nil;
  fn_temps := ((_index, (tptr t_struct_list)) ::
               (_previous, (tptr t_struct_list)) :: (_sortedvalue, tint) ::
               (_guard, tint) :: (_insert_value, tint) :: (_guard'1, tint) ::
               (_guard', tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _previous (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sset _insert_value
      (Efield
        (Ederef (Etempvar _insert_node (tptr t_struct_list)) t_struct_list)
        _head tint))
    (Ssequence
      (Sset _index (Etempvar _sorted (tptr t_struct_list)))
      (Ssequence
        (Sifthenelse (Etempvar _index (tptr t_struct_list))
          (Sset _sortedvalue
            (Efield
              (Ederef (Etempvar _index (tptr t_struct_list)) t_struct_list)
              _head tint))
          Sskip)
        (Ssequence
          (Ssequence
            (Sifthenelse (Etempvar _index (tptr t_struct_list))
              (Ssequence
                (Sset _guard'
                  (Ecast
                    (Ebinop Ogt (Etempvar _insert_value tint)
                      (Etempvar _sortedvalue tint) tint) tbool))
                (Sset _guard' (Ecast (Etempvar _guard' tbool) tint)))
              (Sset _guard' (Econst_int (Int.repr 0) tint)))
            (Sset _guard (Etempvar _guard' tint)))
          (Ssequence
            (Swhile
              (Etempvar _guard tint)
              (Ssequence
                (Sset _previous (Etempvar _index (tptr t_struct_list)))
                (Ssequence
                  (Sset _index
                    (Efield
                      (Ederef (Etempvar _index (tptr t_struct_list))
                        t_struct_list) _tail (tptr t_struct_list)))
                  (Ssequence
                    (Sifthenelse (Etempvar _index (tptr t_struct_list))
                      (Sset _sortedvalue
                        (Efield
                          (Ederef (Etempvar _index (tptr t_struct_list))
                            t_struct_list) _head tint))
                      Sskip)
                    (Ssequence
                      (Sifthenelse (Etempvar _index (tptr t_struct_list))
                        (Ssequence
                          (Sset _guard'1
                            (Ecast
                              (Ebinop Ogt (Etempvar _insert_value tint)
                                (Etempvar _sortedvalue tint) tint) tbool))
                          (Sset _guard'1
                            (Ecast (Etempvar _guard'1 tbool) tint)))
                        (Sset _guard'1 (Econst_int (Int.repr 0) tint)))
                      (Sset _guard (Etempvar _guard'1 tint)))))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _insert_node (tptr t_struct_list))
                    t_struct_list) _tail (tptr t_struct_list))
                (Etempvar _index (tptr t_struct_list)))
              (Ssequence
                (Sifthenelse (Etempvar _previous (tptr t_struct_list))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _previous (tptr t_struct_list))
                          t_struct_list) _tail (tptr t_struct_list))
                      (Etempvar _insert_node (tptr t_struct_list)))
                    (Sreturn (Some (Etempvar _sorted (tptr t_struct_list)))))
                  Sskip)
                (Sreturn (Some (Etempvar _insert_node (tptr t_struct_list))))))))))))
|}.

Definition f_insertionsort := {|
  fn_return := (tptr t_struct_list);
  fn_params := ((_p, (tptr t_struct_list)) :: nil);
  fn_vars := nil;
  fn_temps := ((_index, (tptr t_struct_list)) ::
               (_sorted, (tptr t_struct_list)) ::
               (_next, (tptr t_struct_list)) ::
               (_sorted', (tptr t_struct_list)) :: nil);
  fn_body :=
(Ssequence
  (Sset _sorted (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sset _index (Etempvar _p (tptr t_struct_list)))
    (Ssequence
      (Swhile
        (Etempvar _index (tptr t_struct_list))
        (Ssequence
          (Sset _next
            (Efield
              (Ederef (Etempvar _index (tptr t_struct_list)) t_struct_list)
              _tail (tptr t_struct_list)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _index (tptr t_struct_list)) t_struct_list)
                _tail (tptr t_struct_list))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
            (Ssequence
              (Ssequence
                (Scall (Some _sorted')
                  (Evar _insert (Tfunction
                                  (Tcons (tptr t_struct_list)
                                    (Tcons (tptr t_struct_list) Tnil))
                                  (tptr t_struct_list)))
                  ((Etempvar _index (tptr t_struct_list)) ::
                   (Etempvar _sorted (tptr t_struct_list)) :: nil))
                (Sset _sorted (Etempvar _sorted' (tptr t_struct_list))))
              (Sset _index (Etempvar _next (tptr t_struct_list)))))))
      (Sreturn (Some (Etempvar _sorted (tptr t_struct_list)))))))
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
 (_insert, Gfun(Internal f_insert)) ::
 (_insertionsort, Gfun(Internal f_insertionsort)) ::
 (_main, Gfun(Internal f_main)) :: nil);
prog_main := _main
|}.

