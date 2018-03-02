Require Import Clightdefs.
Local Open Scope Z_scope.
Definition ___builtin_annot : ident := 6%positive.
Definition ___builtin_annot_intval : ident := 7%positive.
Definition ___builtin_bswap : ident := 30%positive.
Definition ___builtin_bswap16 : ident := 32%positive.
Definition ___builtin_bswap32 : ident := 31%positive.
Definition ___builtin_clz : ident := 33%positive.
Definition ___builtin_clzl : ident := 34%positive.
Definition ___builtin_clzll : ident := 35%positive.
Definition ___builtin_ctz : ident := 36%positive.
Definition ___builtin_ctzl : ident := 37%positive.
Definition ___builtin_ctzll : ident := 38%positive.
Definition ___builtin_debug : ident := 51%positive.
Definition ___builtin_fabs : ident := 4%positive.
Definition ___builtin_fmadd : ident := 42%positive.
Definition ___builtin_fmax : ident := 40%positive.
Definition ___builtin_fmin : ident := 41%positive.
Definition ___builtin_fmsub : ident := 43%positive.
Definition ___builtin_fnmadd : ident := 44%positive.
Definition ___builtin_fnmsub : ident := 45%positive.
Definition ___builtin_fsqrt : ident := 39%positive.
Definition ___builtin_membar : ident := 8%positive.
Definition ___builtin_memcpy_aligned : ident := 5%positive.
Definition ___builtin_nop : ident := 50%positive.
Definition ___builtin_read16_reversed : ident := 46%positive.
Definition ___builtin_read32_reversed : ident := 47%positive.
Definition ___builtin_va_arg : ident := 10%positive.
Definition ___builtin_va_copy : ident := 11%positive.
Definition ___builtin_va_end : ident := 12%positive.
Definition ___builtin_va_start : ident := 9%positive.
Definition ___builtin_write16_reversed : ident := 48%positive.
Definition ___builtin_write32_reversed : ident := 49%positive.
Definition ___compcert_va_composite : ident := 16%positive.
Definition ___compcert_va_float64 : ident := 15%positive.
Definition ___compcert_va_int32 : ident := 13%positive.
Definition ___compcert_va_int64 : ident := 14%positive.
Definition ___i64_dtos : ident := 17%positive.
Definition ___i64_dtou : ident := 18%positive.
Definition ___i64_sar : ident := 29%positive.
Definition ___i64_sdiv : ident := 23%positive.
Definition ___i64_shl : ident := 27%positive.
Definition ___i64_shr : ident := 28%positive.
Definition ___i64_smod : ident := 25%positive.
Definition ___i64_stod : ident := 19%positive.
Definition ___i64_stof : ident := 21%positive.
Definition ___i64_udiv : ident := 24%positive.
Definition ___i64_umod : ident := 26%positive.
Definition ___i64_utod : ident := 20%positive.
Definition ___i64_utof : ident := 22%positive.
Definition _a : ident := 56%positive.
Definition _apply : ident := 55%positive.
Definition _apply0 : ident := 54%positive.
Definition _b : ident := 57%positive.
Definition _cmp : ident := 62%positive.
Definition _f : ident := 52%positive.
Definition _fool : ident := 59%positive.
Definition _foollist : ident := 77%positive.
Definition _guard : ident := 66%positive.
Definition _head : ident := 1%positive.
Definition _index : ident := 63%positive.
Definition _insert : ident := 68%positive.
Definition _insert_node : ident := 60%positive.
Definition _insert_value : ident := 67%positive.
Definition _insertionsort : ident := 71%positive.
Definition _larger : ident := 73%positive.
Definition _list : ident := 2%positive.
Definition _main : ident := 79%positive.
Definition _next : ident := 70%positive.
Definition _p : ident := 69%positive.
Definition _previous : ident := 64%positive.
Definition _r : ident := 78%positive.
Definition _six : ident := 76%positive.
Definition _smaller : ident := 74%positive.
Definition _sorted : ident := 61%positive.
Definition _sortedvalue : ident := 65%positive.
Definition _tail : ident := 3%positive.
Definition _tmp : ident := 58%positive.
Definition _weird_order : ident := 75%positive.
Definition _x : ident := 53%positive.
Definition _y : ident := 72%positive.
Definition _t'1 : ident := 80%positive.
Definition _t'2 : ident := 81%positive.
Definition _t'3 : ident := 82%positive.
Definition _t'4 : ident := 83%positive.

Definition f_apply0 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_f,
                 (tptr (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid
                         cc_default))) :: (_x, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Etempvar _f (tptr (Tfunction (Tcons tint (Tcons tint Tnil)) tvoid
                       cc_default)))
  ((Ecast (Etempvar _x (tptr tvoid)) tint) ::
   (Ecast (Etempvar _x (tptr tvoid)) tint) :: nil))
|}.

Definition f_apply := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_f,
                 (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))) ::
                (_x, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Etempvar _f (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default)))
  ((Etempvar _x (tptr tvoid)) :: nil))
|}.

Definition f_fool := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, (tptr tint)) :: (_tmp, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _b (Ecast (Etempvar _a (tptr tvoid)) (tptr tint)))
  (Ssequence
    (Sset _tmp
      (Ederef
        (Ebinop Oadd (Etempvar _b (tptr tint)) (Econst_int (Int.repr 1) tint)
          (tptr tint)) tint))
    (Sassign (Ederef (Etempvar _b (tptr tint)) tint)
      (Ebinop Oadd
        (Ebinop Omul (Etempvar _tmp tint) (Econst_int (Int.repr 3) tint)
          tint) (Econst_int (Int.repr 1) tint) tint))))
|}.

Definition f_insert := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_insert_node, (tptr (Tstruct _list noattr))) ::
                (_sorted, (tptr (Tstruct _list noattr))) ::
                (_cmp,
                 (tptr (Tfunction (Tcons tint (Tcons tint Tnil)) tint
                         cc_default))) :: nil);
  fn_vars := nil;
  fn_temps := ((_index, (tptr (Tstruct _list noattr))) ::
               (_previous, (tptr (Tstruct _list noattr))) ::
               (_sortedvalue, tint) :: (_guard, tint) ::
               (_insert_value, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _previous (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _insert_value
      (Efield
        (Ederef (Etempvar _insert_node (tptr (Tstruct _list noattr)))
          (Tstruct _list noattr)) _head tint))
    (Ssequence
      (Sset _index (Etempvar _sorted (tptr (Tstruct _list noattr))))
      (Ssequence
        (Sifthenelse (Etempvar _index (tptr (Tstruct _list noattr)))
          (Sset _sortedvalue
            (Efield
              (Ederef (Etempvar _index (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _head tint))
          Sskip)
        (Ssequence
          (Ssequence
            (Sifthenelse (Etempvar _index (tptr (Tstruct _list noattr)))
              (Ssequence
                (Scall (Some _t'2)
                  (Etempvar _cmp (tptr (Tfunction
                                         (Tcons tint (Tcons tint Tnil)) tint
                                         cc_default)))
                  ((Etempvar _insert_value tint) ::
                   (Etempvar _sortedvalue tint) :: nil))
                (Sset _t'1 (Ecast (Etempvar _t'2 tint) tbool)))
              (Sset _t'1 (Econst_int (Int.repr 0) tint)))
            (Sset _guard (Etempvar _t'1 tint)))
          (Ssequence
            (Swhile
              (Etempvar _guard tint)
              (Ssequence
                (Sset _previous
                  (Etempvar _index (tptr (Tstruct _list noattr))))
                (Ssequence
                  (Sset _index
                    (Efield
                      (Ederef (Etempvar _index (tptr (Tstruct _list noattr)))
                        (Tstruct _list noattr)) _tail
                      (tptr (Tstruct _list noattr))))
                  (Ssequence
                    (Sifthenelse (Etempvar _index (tptr (Tstruct _list noattr)))
                      (Sset _sortedvalue
                        (Efield
                          (Ederef
                            (Etempvar _index (tptr (Tstruct _list noattr)))
                            (Tstruct _list noattr)) _head tint))
                      Sskip)
                    (Ssequence
                      (Sifthenelse (Etempvar _index (tptr (Tstruct _list noattr)))
                        (Ssequence
                          (Scall (Some _t'4)
                            (Etempvar _cmp (tptr (Tfunction
                                                   (Tcons tint
                                                     (Tcons tint Tnil)) tint
                                                   cc_default)))
                            ((Etempvar _insert_value tint) ::
                             (Etempvar _sortedvalue tint) :: nil))
                          (Sset _t'3 (Ecast (Etempvar _t'4 tint) tbool)))
                        (Sset _t'3 (Econst_int (Int.repr 0) tint)))
                      (Sset _guard (Etempvar _t'3 tint)))))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _insert_node (tptr (Tstruct _list noattr)))
                    (Tstruct _list noattr)) _tail
                  (tptr (Tstruct _list noattr)))
                (Etempvar _index (tptr (Tstruct _list noattr))))
              (Ssequence
                (Sifthenelse (Etempvar _previous (tptr (Tstruct _list noattr)))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _previous (tptr (Tstruct _list noattr)))
                          (Tstruct _list noattr)) _tail
                        (tptr (Tstruct _list noattr)))
                      (Etempvar _insert_node (tptr (Tstruct _list noattr))))
                    (Sreturn (Some (Etempvar _sorted (tptr (Tstruct _list noattr))))))
                  Sskip)
                (Sreturn (Some (Etempvar _insert_node (tptr (Tstruct _list noattr)))))))))))))
|}.

Definition f_insertionsort := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _list noattr))) ::
                (_cmp,
                 (tptr (Tfunction (Tcons tint (Tcons tint Tnil)) tint
                         cc_default))) :: nil);
  fn_vars := nil;
  fn_temps := ((_index, (tptr (Tstruct _list noattr))) ::
               (_sorted, (tptr (Tstruct _list noattr))) ::
               (_next, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _sorted (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _index (Etempvar _p (tptr (Tstruct _list noattr))))
    (Ssequence
      (Swhile
        (Etempvar _index (tptr (Tstruct _list noattr)))
        (Ssequence
          (Sset _next
            (Efield
              (Ederef (Etempvar _index (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _index (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _list noattr)))
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _insert (Tfunction
                                  (Tcons (tptr (Tstruct _list noattr))
                                    (Tcons (tptr (Tstruct _list noattr))
                                      (Tcons
                                        (tptr (Tfunction
                                                (Tcons tint
                                                  (Tcons tint Tnil)) tint
                                                cc_default)) Tnil)))
                                  (tptr (Tstruct _list noattr)) cc_default))
                  ((Etempvar _index (tptr (Tstruct _list noattr))) ::
                   (Etempvar _sorted (tptr (Tstruct _list noattr))) ::
                   (Etempvar _cmp (tptr (Tfunction
                                          (Tcons tint (Tcons tint Tnil)) tint
                                          cc_default))) :: nil))
                (Sset _sorted (Etempvar _t'1 (tptr (Tstruct _list noattr)))))
              (Sset _index (Etempvar _next (tptr (Tstruct _list noattr))))))))
      (Sreturn (Some (Etempvar _sorted (tptr (Tstruct _list noattr))))))))
|}.

Definition f_larger := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, tint) :: (_y, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Ogt (Etempvar _x tint) (Etempvar _y tint) tint)))
|}.

Definition f_smaller := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, tint) :: (_y, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Olt (Etempvar _x tint) (Etempvar _y tint) tint)))
|}.

Definition f_weird_order := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, tint) :: (_y, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Oeq
               (Ebinop Omod (Etempvar _x tint) (Econst_int (Int.repr 3) tint)
                 tint)
               (Ebinop Omod (Etempvar _y tint) (Econst_int (Int.repr 3) tint)
                 tint) tint)
  (Sreturn (Some (Ebinop Olt (Etempvar _x tint) (Etempvar _y tint) tint)))
  (Sreturn (Some (Ebinop Olt
                   (Ebinop Omod (Etempvar _x tint)
                     (Econst_int (Int.repr 3) tint) tint)
                   (Ebinop Omod (Etempvar _y tint)
                     (Econst_int (Int.repr 3) tint) tint) tint))))
|}.

Definition v_six := {|
  gvar_info := (tarray (Tstruct _list noattr) 7);
  gvar_init := (Init_int32 (Int.repr 5) :: Init_addrof _six (Int.repr 8) ::
                Init_int32 (Int.repr 2) :: Init_addrof _six (Int.repr 16) ::
                Init_int32 (Int.repr 4) :: Init_addrof _six (Int.repr 24) ::
                Init_int32 (Int.repr 0) :: Init_addrof _six (Int.repr 32) ::
                Init_int32 (Int.repr 8) :: Init_addrof _six (Int.repr 40) ::
                Init_int32 (Int.repr 1) :: Init_addrof _six (Int.repr 48) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_foollist := {|
  gvar_info := (tarray tint 2);
  gvar_init := (Init_int32 (Int.repr 1) :: Init_int32 (Int.repr 2) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_r, (tptr (Tstruct _list noattr))) ::
               (_t'3, (tptr (Tstruct _list noattr))) ::
               (_t'2, (tptr (Tstruct _list noattr))) ::
               (_t'1, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None
      (Evar _apply (Tfunction
                     (Tcons
                       (tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                               cc_default)) (Tcons (tptr tvoid) Tnil)) tvoid
                     cc_default))
      ((Evar _fool (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
       (Evar _foollist (tarray tint 2)) :: nil))
    (Ssequence
      (Sset _r (Evar _six (tarray (Tstruct _list noattr) 7)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _insertionsort (Tfunction
                                   (Tcons (tptr (Tstruct _list noattr))
                                     (Tcons
                                       (tptr (Tfunction
                                               (Tcons tint (Tcons tint Tnil))
                                               tint cc_default)) Tnil))
                                   (tptr (Tstruct _list noattr)) cc_default))
            ((Etempvar _r (tptr (Tstruct _list noattr))) ::
             (Evar _larger (Tfunction (Tcons tint (Tcons tint Tnil)) tint
                             cc_default)) :: nil))
          (Sset _r (Etempvar _t'1 (tptr (Tstruct _list noattr)))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _insertionsort (Tfunction
                                     (Tcons (tptr (Tstruct _list noattr))
                                       (Tcons
                                         (tptr (Tfunction
                                                 (Tcons tint
                                                   (Tcons tint Tnil)) tint
                                                 cc_default)) Tnil))
                                     (tptr (Tstruct _list noattr))
                                     cc_default))
              ((Etempvar _r (tptr (Tstruct _list noattr))) ::
               (Evar _smaller (Tfunction (Tcons tint (Tcons tint Tnil)) tint
                                cc_default)) :: nil))
            (Sset _r (Etempvar _t'2 (tptr (Tstruct _list noattr)))))
          (Ssequence
            (Scall (Some _t'3)
              (Evar _insertionsort (Tfunction
                                     (Tcons (tptr (Tstruct _list noattr))
                                       (Tcons
                                         (tptr (Tfunction
                                                 (Tcons tint
                                                   (Tcons tint Tnil)) tint
                                                 cc_default)) Tnil))
                                     (tptr (Tstruct _list noattr))
                                     cc_default))
              ((Etempvar _r (tptr (Tstruct _list noattr))) ::
               (Evar _weird_order (Tfunction (Tcons tint (Tcons tint Tnil))
                                    tint cc_default)) :: nil))
            (Sset _r (Etempvar _t'3 (tptr (Tstruct _list noattr)))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _list Struct
   ((_head, tint) :: (_tail, (tptr (Tstruct _list noattr))) :: nil)
   noattr :: nil).

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___i64_dtos,
   Gfun(External (EF_runtime "__i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___i64_dtou,
   Gfun(External (EF_runtime "__i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___i64_stod,
   Gfun(External (EF_runtime "__i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___i64_utod,
   Gfun(External (EF_runtime "__i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___i64_stof,
   Gfun(External (EF_runtime "__i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___i64_utof,
   Gfun(External (EF_runtime "__i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___i64_sdiv,
   Gfun(External (EF_runtime "__i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_udiv,
   Gfun(External (EF_runtime "__i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_smod,
   Gfun(External (EF_runtime "__i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umod,
   Gfun(External (EF_runtime "__i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_shl,
   Gfun(External (EF_runtime "__i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___i64_shr,
   Gfun(External (EF_runtime "__i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___i64_sar,
   Gfun(External (EF_runtime "__i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_apply0, Gfun(Internal f_apply0)) :: (_apply, Gfun(Internal f_apply)) ::
 (_fool, Gfun(Internal f_fool)) :: (_insert, Gfun(Internal f_insert)) ::
 (_insertionsort, Gfun(Internal f_insertionsort)) ::
 (_larger, Gfun(Internal f_larger)) ::
 (_smaller, Gfun(Internal f_smaller)) ::
 (_weird_order, Gfun(Internal f_weird_order)) :: (_six, Gvar v_six) ::
 (_foollist, Gvar v_foollist) :: (_main, Gfun(Internal f_main)) :: nil);
prog_public :=
(_main :: _foollist :: _six :: _weird_order :: _smaller :: _larger ::
 _insertionsort :: _insert :: _fool :: _apply :: _apply0 ::
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fsqrt :: ___builtin_ctzll ::
 ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll :: ___builtin_clzl ::
 ___builtin_clz :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: ___i64_sar :: ___i64_shr :: ___i64_shl :: ___i64_umod ::
 ___i64_smod :: ___i64_udiv :: ___i64_sdiv :: ___i64_utof :: ___i64_stof ::
 ___i64_utod :: ___i64_stod :: ___i64_dtou :: ___i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_memcpy_aligned :: ___builtin_fabs :: nil);
prog_main := _main;
prog_types := composites;
prog_comp_env := make_composite_env composites;
prog_comp_env_eq := refl_equal _
|}.

