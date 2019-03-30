From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.5"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "standard"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "progs/tree.c"%string.
  Definition normalized := true.
End Info.

Definition _BinaryTree : ident := 9%positive.
Definition _XList : ident := 1%positive.
Definition _Xfoo : ident := 70%positive.
Definition _Xnode : ident := 4%positive.
Definition _Xnode_add : ident := 66%positive.
Definition _YList : ident := 7%positive.
Definition _YList_add : ident := 67%positive.
Definition _YTree_add : ident := 69%positive.
Definition _Ynode : ident := 8%positive.
Definition _Ynode_add : ident := 68%positive.
Definition ___builtin_annot : ident := 19%positive.
Definition ___builtin_annot_intval : ident := 20%positive.
Definition ___builtin_bswap : ident := 13%positive.
Definition ___builtin_bswap16 : ident := 15%positive.
Definition ___builtin_bswap32 : ident := 14%positive.
Definition ___builtin_bswap64 : ident := 45%positive.
Definition ___builtin_clz : ident := 46%positive.
Definition ___builtin_clzl : ident := 47%positive.
Definition ___builtin_clzll : ident := 48%positive.
Definition ___builtin_ctz : ident := 49%positive.
Definition ___builtin_ctzl : ident := 50%positive.
Definition ___builtin_ctzll : ident := 51%positive.
Definition ___builtin_debug : ident := 63%positive.
Definition ___builtin_fabs : ident := 16%positive.
Definition ___builtin_fmadd : ident := 54%positive.
Definition ___builtin_fmax : ident := 52%positive.
Definition ___builtin_fmin : ident := 53%positive.
Definition ___builtin_fmsub : ident := 55%positive.
Definition ___builtin_fnmadd : ident := 56%positive.
Definition ___builtin_fnmsub : ident := 57%positive.
Definition ___builtin_fsqrt : ident := 17%positive.
Definition ___builtin_membar : ident := 21%positive.
Definition ___builtin_memcpy_aligned : ident := 18%positive.
Definition ___builtin_nop : ident := 62%positive.
Definition ___builtin_read16_reversed : ident := 58%positive.
Definition ___builtin_read32_reversed : ident := 59%positive.
Definition ___builtin_va_arg : ident := 23%positive.
Definition ___builtin_va_copy : ident := 24%positive.
Definition ___builtin_va_end : ident := 25%positive.
Definition ___builtin_va_start : ident := 22%positive.
Definition ___builtin_write16_reversed : ident := 60%positive.
Definition ___builtin_write32_reversed : ident := 61%positive.
Definition ___compcert_i64_dtos : ident := 30%positive.
Definition ___compcert_i64_dtou : ident := 31%positive.
Definition ___compcert_i64_sar : ident := 42%positive.
Definition ___compcert_i64_sdiv : ident := 36%positive.
Definition ___compcert_i64_shl : ident := 40%positive.
Definition ___compcert_i64_shr : ident := 41%positive.
Definition ___compcert_i64_smod : ident := 38%positive.
Definition ___compcert_i64_smulh : ident := 43%positive.
Definition ___compcert_i64_stod : ident := 32%positive.
Definition ___compcert_i64_stof : ident := 34%positive.
Definition ___compcert_i64_udiv : ident := 37%positive.
Definition ___compcert_i64_umod : ident := 39%positive.
Definition ___compcert_i64_umulh : ident := 44%positive.
Definition ___compcert_i64_utod : ident := 33%positive.
Definition ___compcert_i64_utof : ident := 35%positive.
Definition ___compcert_va_composite : ident := 29%positive.
Definition ___compcert_va_float64 : ident := 28%positive.
Definition ___compcert_va_int32 : ident := 26%positive.
Definition ___compcert_va_int64 : ident := 27%positive.
Definition _left : ident := 11%positive.
Definition _list : ident := 2%positive.
Definition _main : ident := 71%positive.
Definition _next : ident := 6%positive.
Definition _node : ident := 5%positive.
Definition _p : ident := 64%positive.
Definition _q : ident := 65%positive.
Definition _right : ident := 12%positive.
Definition _tree : ident := 10%positive.
Definition _v : ident := 3%positive.
Definition _t'1 : ident := 72%positive.
Definition _t'2 : ident := 73%positive.
Definition _t'3 : ident := 74%positive.
Definition _t'4 : ident := 75%positive.

Definition f_Xnode_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _Xnode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_q, (tptr (Tstruct _XList noattr))) :: (_t'2, tuint) ::
               (_t'1, (tptr (Tstruct _Xnode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _Xnode noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _Xnode noattr)))
            (Tstruct _Xnode noattr)) _v tuint))
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _Xnode noattr)))
            (Tstruct _Xnode noattr)) _v tuint)
        (Ebinop Oadd (Etempvar _t'2 tuint) (Econst_int (Int.repr 1) tint)
          tuint)))
    (Ssequence
      (Sset _q
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _Xnode noattr)))
            (Tstruct _Xnode noattr)) _list (tptr (Tstruct _XList noattr))))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop One
                         (Etempvar _q (tptr (Tstruct _XList noattr)))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _q (tptr (Tstruct _XList noattr)))
                  (Tstruct _XList noattr)) _node
                (tptr (Tstruct _Xnode noattr))))
            (Scall None
              (Evar _Xnode_add (Tfunction
                                 (Tcons (tptr (Tstruct _Xnode noattr)) Tnil)
                                 tvoid cc_default))
              ((Etempvar _t'1 (tptr (Tstruct _Xnode noattr))) :: nil))))
        (Sset _q
          (Efield
            (Ederef (Etempvar _q (tptr (Tstruct _XList noattr)))
              (Tstruct _XList noattr)) _next (tptr (Tstruct _XList noattr))))))))
|}.

Definition f_Ynode_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _Ynode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, (tptr (Tstruct _YList noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _Ynode noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _Ynode noattr)))
            (Tstruct _Ynode noattr)) _v tuint))
      (Sassign
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _Ynode noattr)))
            (Tstruct _Ynode noattr)) _v tuint)
        (Ebinop Oadd (Etempvar _t'2 tuint) (Econst_int (Int.repr 1) tint)
          tuint)))
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _Ynode noattr)))
            (Tstruct _Ynode noattr)) _list (tptr (Tstruct _YList noattr))))
      (Scall None
        (Evar _YList_add (Tfunction
                           (Tcons (tptr (Tstruct _YList noattr)) Tnil) tvoid
                           cc_default))
        ((Etempvar _t'1 (tptr (Tstruct _YList noattr))) :: nil)))))
|}.

Definition f_YList_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _YList noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _BinaryTree noattr))) ::
               (_t'1, (tptr (Tstruct _YList noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _YList noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _YList noattr)))
            (Tstruct _YList noattr)) _tree
          (tptr (Tstruct _BinaryTree noattr))))
      (Scall None
        (Evar _YTree_add (Tfunction
                           (Tcons (tptr (Tstruct _BinaryTree noattr)) Tnil)
                           tvoid cc_default))
        ((Etempvar _t'2 (tptr (Tstruct _BinaryTree noattr))) :: nil)))
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _YList noattr)))
            (Tstruct _YList noattr)) _next (tptr (Tstruct _YList noattr))))
      (Scall None
        (Evar _YList_add (Tfunction
                           (Tcons (tptr (Tstruct _YList noattr)) Tnil) tvoid
                           cc_default))
        ((Etempvar _t'1 (tptr (Tstruct _YList noattr))) :: nil)))))
|}.

Definition f_YTree_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _BinaryTree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, (tptr (Tstruct _Ynode noattr))) ::
               (_t'2, (tptr (Tstruct _BinaryTree noattr))) ::
               (_t'1, (tptr (Tstruct _BinaryTree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _BinaryTree noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _BinaryTree noattr)))
            (Tstruct _BinaryTree noattr)) _node
          (tptr (Tstruct _Ynode noattr))))
      (Scall None
        (Evar _Ynode_add (Tfunction
                           (Tcons (tptr (Tstruct _Ynode noattr)) Tnil) tvoid
                           cc_default))
        ((Etempvar _t'3 (tptr (Tstruct _Ynode noattr))) :: nil)))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _BinaryTree noattr)))
              (Tstruct _BinaryTree noattr)) _left
            (tptr (Tstruct _BinaryTree noattr))))
        (Scall None
          (Evar _YTree_add (Tfunction
                             (Tcons (tptr (Tstruct _BinaryTree noattr)) Tnil)
                             tvoid cc_default))
          ((Etempvar _t'2 (tptr (Tstruct _BinaryTree noattr))) :: nil)))
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _BinaryTree noattr)))
              (Tstruct _BinaryTree noattr)) _right
            (tptr (Tstruct _BinaryTree noattr))))
        (Scall None
          (Evar _YTree_add (Tfunction
                             (Tcons (tptr (Tstruct _BinaryTree noattr)) Tnil)
                             tvoid cc_default))
          ((Etempvar _t'1 (tptr (Tstruct _BinaryTree noattr))) :: nil))))))
|}.

Definition f_Xfoo := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _Xnode noattr))) :: nil);
  fn_vars := ((_q, (Tstruct _Xnode noattr)) :: nil);
  fn_temps := ((_t'4, (tptr (Tstruct _XList noattr))) :: (_t'3, tuint) ::
               (_t'2, (tptr (Tstruct _XList noattr))) :: (_t'1, tuint) ::
               nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _Xnode noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _Xnode noattr)))
            (Tstruct _Xnode noattr)) _list (tptr (Tstruct _XList noattr))))
      (Sassign
        (Efield (Evar _q (Tstruct _Xnode noattr)) _list
          (tptr (Tstruct _XList noattr)))
        (Etempvar _t'4 (tptr (Tstruct _XList noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _Xnode noattr)))
              (Tstruct _Xnode noattr)) _v tuint))
        (Sassign (Efield (Evar _q (Tstruct _Xnode noattr)) _v tuint)
          (Etempvar _t'3 tuint)))
      (Ssequence
        (Scall None
          (Evar _Xnode_add (Tfunction
                             (Tcons (tptr (Tstruct _Xnode noattr)) Tnil)
                             tvoid cc_default))
          ((Eaddrof (Evar _q (Tstruct _Xnode noattr))
             (tptr (Tstruct _Xnode noattr))) :: nil))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield (Evar _q (Tstruct _Xnode noattr)) _list
                (tptr (Tstruct _XList noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _Xnode noattr)))
                  (Tstruct _Xnode noattr)) _list
                (tptr (Tstruct _XList noattr)))
              (Etempvar _t'2 (tptr (Tstruct _XList noattr)))))
          (Ssequence
            (Sset _t'1 (Efield (Evar _q (Tstruct _Xnode noattr)) _v tuint))
            (Sassign
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _Xnode noattr)))
                  (Tstruct _Xnode noattr)) _v tuint) (Etempvar _t'1 tuint))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 0) tint)))
|}.

Definition composites : list composite_definition :=
(Composite _Xnode Struct
   ((_list, (tptr (Tstruct _XList noattr))) :: (_v, tuint) :: nil)
   noattr ::
 Composite _XList Struct
   ((_node, (tptr (Tstruct _Xnode noattr))) ::
    (_next, (tptr (Tstruct _XList noattr))) :: nil)
   noattr ::
 Composite _Ynode Struct
   ((_list, (tptr (Tstruct _YList noattr))) :: (_v, tuint) :: nil)
   noattr ::
 Composite _YList Struct
   ((_tree, (tptr (Tstruct _BinaryTree noattr))) ::
    (_next, (tptr (Tstruct _YList noattr))) :: nil)
   noattr ::
 Composite _BinaryTree Struct
   ((_node, (tptr (Tstruct _Ynode noattr))) ::
    (_left, (tptr (Tstruct _BinaryTree noattr))) ::
    (_right, (tptr (Tstruct _BinaryTree noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap,
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
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
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
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
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
 (_Xnode_add, Gfun(Internal f_Xnode_add)) ::
 (_Ynode_add, Gfun(Internal f_Ynode_add)) ::
 (_YList_add, Gfun(Internal f_YList_add)) ::
 (_YTree_add, Gfun(Internal f_YTree_add)) ::
 (_Xfoo, Gfun(Internal f_Xfoo)) :: (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _Xfoo :: _YTree_add :: _YList_add :: _Ynode_add :: _Xnode_add ::
 ___builtin_debug :: ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fsqrt ::
 ___builtin_fabs :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


