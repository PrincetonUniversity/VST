From Stdlib Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "32sse2".
  Definition abi := "standard".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "progs/tree.c".
  Definition normalized := true.
End Info.

Definition _BinaryTree : ident := 10%positive.
Definition _XList : ident := 3%positive.
Definition _Xfoo : ident := 56%positive.
Definition _Xnode : ident := 1%positive.
Definition _Xnode_add : ident := 52%positive.
Definition _YList : ident := 8%positive.
Definition _YList_add : ident := 53%positive.
Definition _YTree_add : ident := 55%positive.
Definition _Ynode : ident := 7%positive.
Definition _Ynode_add : ident := 54%positive.
Definition ___builtin_ais_annot : ident := 13%positive.
Definition ___builtin_annot : ident := 30%positive.
Definition ___builtin_annot_intval : ident := 31%positive.
Definition ___builtin_bswap : ident := 15%positive.
Definition ___builtin_bswap16 : ident := 17%positive.
Definition ___builtin_bswap32 : ident := 16%positive.
Definition ___builtin_bswap64 : ident := 14%positive.
Definition ___builtin_clz : ident := 18%positive.
Definition ___builtin_clzl : ident := 19%positive.
Definition ___builtin_clzll : ident := 20%positive.
Definition ___builtin_ctz : ident := 21%positive.
Definition ___builtin_ctzl : ident := 22%positive.
Definition ___builtin_ctzll : ident := 23%positive.
Definition ___builtin_debug : ident := 49%positive.
Definition ___builtin_expect : ident := 38%positive.
Definition ___builtin_fabs : ident := 24%positive.
Definition ___builtin_fabsf : ident := 25%positive.
Definition ___builtin_fmadd : ident := 41%positive.
Definition ___builtin_fmax : ident := 39%positive.
Definition ___builtin_fmin : ident := 40%positive.
Definition ___builtin_fmsub : ident := 42%positive.
Definition ___builtin_fnmadd : ident := 43%positive.
Definition ___builtin_fnmsub : ident := 44%positive.
Definition ___builtin_fsqrt : ident := 26%positive.
Definition ___builtin_membar : ident := 32%positive.
Definition ___builtin_memcpy_aligned : ident := 28%positive.
Definition ___builtin_read16_reversed : ident := 45%positive.
Definition ___builtin_read32_reversed : ident := 46%positive.
Definition ___builtin_sel : ident := 29%positive.
Definition ___builtin_sqrt : ident := 27%positive.
Definition ___builtin_unreachable : ident := 37%positive.
Definition ___builtin_va_arg : ident := 34%positive.
Definition ___builtin_va_copy : ident := 35%positive.
Definition ___builtin_va_end : ident := 36%positive.
Definition ___builtin_va_start : ident := 33%positive.
Definition ___builtin_write16_reversed : ident := 47%positive.
Definition ___builtin_write32_reversed : ident := 48%positive.
Definition ___compcert_i64_dtos : ident := 62%positive.
Definition ___compcert_i64_dtou : ident := 63%positive.
Definition ___compcert_i64_sar : ident := 74%positive.
Definition ___compcert_i64_sdiv : ident := 68%positive.
Definition ___compcert_i64_shl : ident := 72%positive.
Definition ___compcert_i64_shr : ident := 73%positive.
Definition ___compcert_i64_smod : ident := 70%positive.
Definition ___compcert_i64_smulh : ident := 75%positive.
Definition ___compcert_i64_stod : ident := 64%positive.
Definition ___compcert_i64_stof : ident := 66%positive.
Definition ___compcert_i64_udiv : ident := 69%positive.
Definition ___compcert_i64_umod : ident := 71%positive.
Definition ___compcert_i64_umulh : ident := 76%positive.
Definition ___compcert_i64_utod : ident := 65%positive.
Definition ___compcert_i64_utof : ident := 67%positive.
Definition ___compcert_va_composite : ident := 61%positive.
Definition ___compcert_va_float64 : ident := 60%positive.
Definition ___compcert_va_int32 : ident := 58%positive.
Definition ___compcert_va_int64 : ident := 59%positive.
Definition _left : ident := 11%positive.
Definition _list : ident := 2%positive.
Definition _main : ident := 57%positive.
Definition _next : ident := 6%positive.
Definition _node : ident := 5%positive.
Definition _p : ident := 50%positive.
Definition _q : ident := 51%positive.
Definition _right : ident := 12%positive.
Definition _tree : ident := 9%positive.
Definition _v : ident := 4%positive.
Definition _t'1 : ident := 77%positive.
Definition _t'2 : ident := 78%positive.
Definition _t'3 : ident := 79%positive.
Definition _t'4 : ident := 80%positive.

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
                                 ((tptr (Tstruct _Xnode noattr)) :: nil)
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
        (Evar _YList_add (Tfunction ((tptr (Tstruct _YList noattr)) :: nil)
                           tvoid cc_default))
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
                           ((tptr (Tstruct _BinaryTree noattr)) :: nil) tvoid
                           cc_default))
        ((Etempvar _t'2 (tptr (Tstruct _BinaryTree noattr))) :: nil)))
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _YList noattr)))
            (Tstruct _YList noattr)) _next (tptr (Tstruct _YList noattr))))
      (Scall None
        (Evar _YList_add (Tfunction ((tptr (Tstruct _YList noattr)) :: nil)
                           tvoid cc_default))
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
        (Evar _Ynode_add (Tfunction ((tptr (Tstruct _Ynode noattr)) :: nil)
                           tvoid cc_default))
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
                             ((tptr (Tstruct _BinaryTree noattr)) :: nil)
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
                             ((tptr (Tstruct _BinaryTree noattr)) :: nil)
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
          (Evar _Xnode_add (Tfunction ((tptr (Tstruct _Xnode noattr)) :: nil)
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
   (Member_plain _list (tptr (Tstruct _XList noattr)) ::
    Member_plain _v tuint :: nil)
   noattr ::
 Composite _XList Struct
   (Member_plain _node (tptr (Tstruct _Xnode noattr)) ::
    Member_plain _next (tptr (Tstruct _XList noattr)) :: nil)
   noattr ::
 Composite _Ynode Struct
   (Member_plain _list (tptr (Tstruct _YList noattr)) ::
    Member_plain _v tuint :: nil)
   noattr ::
 Composite _YList Struct
   (Member_plain _tree (tptr (Tstruct _BinaryTree noattr)) ::
    Member_plain _next (tptr (Tstruct _YList noattr)) :: nil)
   noattr ::
 Composite _BinaryTree Struct
   (Member_plain _node (tptr (Tstruct _Ynode noattr)) ::
    Member_plain _left (tptr (Tstruct _BinaryTree noattr)) ::
    Member_plain _right (tptr (Tstruct _BinaryTree noattr)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tuint :: nil) (tptr tvoid)
     cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xint :: AST.Xint :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tuint :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xint :: AST.Xint :: nil) AST.Xint
                     cc_default)) (tint :: tint :: nil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_Xnode_add, Gfun(Internal f_Xnode_add)) ::
 (_Ynode_add, Gfun(Internal f_Ynode_add)) ::
 (_YList_add, Gfun(Internal f_YList_add)) ::
 (_YTree_add, Gfun(Internal f_YTree_add)) ::
 (_Xfoo, Gfun(Internal f_Xfoo)) :: (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _Xfoo :: _YTree_add :: _YList_add :: _Ynode_add :: _Xnode_add ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


