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
  Definition source_file := "progs/queue2.c"%string.
  Definition normalized := true.
End Info.

Definition _Q : ident := 3%positive.
Definition ___builtin_annot : ident := ltac:(string2ident "__builtin_annot"%string).
Definition ___builtin_annot_intval : ident := ltac:(string2ident "__builtin_annot_intval"%string).
Definition ___builtin_bswap : ident := ltac:(string2ident "__builtin_bswap"%string).
Definition ___builtin_bswap16 : ident := ltac:(string2ident "__builtin_bswap16"%string).
Definition ___builtin_bswap32 : ident := ltac:(string2ident "__builtin_bswap32"%string).
Definition ___builtin_bswap64 : ident := ltac:(string2ident "__builtin_bswap64"%string).
Definition ___builtin_clz : ident := ltac:(string2ident "__builtin_clz"%string).
Definition ___builtin_clzl : ident := ltac:(string2ident "__builtin_clzl"%string).
Definition ___builtin_clzll : ident := ltac:(string2ident "__builtin_clzll"%string).
Definition ___builtin_ctz : ident := ltac:(string2ident "__builtin_ctz"%string).
Definition ___builtin_ctzl : ident := ltac:(string2ident "__builtin_ctzl"%string).
Definition ___builtin_ctzll : ident := ltac:(string2ident "__builtin_ctzll"%string).
Definition ___builtin_debug : ident := ltac:(string2ident "__builtin_debug"%string).
Definition ___builtin_fabs : ident := ltac:(string2ident "__builtin_fabs"%string).
Definition ___builtin_fmadd : ident := ltac:(string2ident "__builtin_fmadd"%string).
Definition ___builtin_fmax : ident := ltac:(string2ident "__builtin_fmax"%string).
Definition ___builtin_fmin : ident := ltac:(string2ident "__builtin_fmin"%string).
Definition ___builtin_fmsub : ident := ltac:(string2ident "__builtin_fmsub"%string).
Definition ___builtin_fnmadd : ident := ltac:(string2ident "__builtin_fnmadd"%string).
Definition ___builtin_fnmsub : ident := ltac:(string2ident "__builtin_fnmsub"%string).
Definition ___builtin_fsqrt : ident := ltac:(string2ident "__builtin_fsqrt"%string).
Definition ___builtin_membar : ident := ltac:(string2ident "__builtin_membar"%string).
Definition ___builtin_memcpy_aligned : ident := ltac:(string2ident "__builtin_memcpy_aligned"%string).
Definition ___builtin_nop : ident := ltac:(string2ident "__builtin_nop"%string).
Definition ___builtin_read16_reversed : ident := ltac:(string2ident "__builtin_read16_reversed"%string).
Definition ___builtin_read32_reversed : ident := ltac:(string2ident "__builtin_read32_reversed"%string).
Definition ___builtin_va_arg : ident := ltac:(string2ident "__builtin_va_arg"%string).
Definition ___builtin_va_copy : ident := ltac:(string2ident "__builtin_va_copy"%string).
Definition ___builtin_va_end : ident := ltac:(string2ident "__builtin_va_end"%string).
Definition ___builtin_va_start : ident := ltac:(string2ident "__builtin_va_start"%string).
Definition ___builtin_write16_reversed : ident := ltac:(string2ident "__builtin_write16_reversed"%string).
Definition ___builtin_write32_reversed : ident := ltac:(string2ident "__builtin_write32_reversed"%string).
Definition ___compcert_i64_dtos : ident := ltac:(string2ident "__compcert_i64_dtos"%string).
Definition ___compcert_i64_dtou : ident := ltac:(string2ident "__compcert_i64_dtou"%string).
Definition ___compcert_i64_sar : ident := ltac:(string2ident "__compcert_i64_sar"%string).
Definition ___compcert_i64_sdiv : ident := ltac:(string2ident "__compcert_i64_sdiv"%string).
Definition ___compcert_i64_shl : ident := ltac:(string2ident "__compcert_i64_shl"%string).
Definition ___compcert_i64_shr : ident := ltac:(string2ident "__compcert_i64_shr"%string).
Definition ___compcert_i64_smod : ident := ltac:(string2ident "__compcert_i64_smod"%string).
Definition ___compcert_i64_smulh : ident := ltac:(string2ident "__compcert_i64_smulh"%string).
Definition ___compcert_i64_stod : ident := ltac:(string2ident "__compcert_i64_stod"%string).
Definition ___compcert_i64_stof : ident := ltac:(string2ident "__compcert_i64_stof"%string).
Definition ___compcert_i64_udiv : ident := ltac:(string2ident "__compcert_i64_udiv"%string).
Definition ___compcert_i64_umod : ident := ltac:(string2ident "__compcert_i64_umod"%string).
Definition ___compcert_i64_umulh : ident := ltac:(string2ident "__compcert_i64_umulh"%string).
Definition ___compcert_i64_utod : ident := ltac:(string2ident "__compcert_i64_utod"%string).
Definition ___compcert_i64_utof : ident := ltac:(string2ident "__compcert_i64_utof"%string).
Definition ___compcert_va_composite : ident := ltac:(string2ident "__compcert_va_composite"%string).
Definition ___compcert_va_float64 : ident := ltac:(string2ident "__compcert_va_float64"%string).
Definition ___compcert_va_int32 : ident := ltac:(string2ident "__compcert_va_int32"%string).
Definition ___compcert_va_int64 : ident := ltac:(string2ident "__compcert_va_int64"%string).
Definition _data : ident := 4%positive.
Definition _elem : ident := ltac:(string2ident "elem"%string).
Definition _exit : ident := ltac:(string2ident "exit"%string).
Definition _fifo : ident := ltac:(string2ident "fifo"%string).
Definition _fifo_empty : ident := ltac:(string2ident "fifo_empty"%string).
Definition _fifo_get : ident := ltac:(string2ident "fifo_get"%string).
Definition _fifo_new : ident := ltac:(string2ident "fifo_new"%string).
Definition _fifo_put : ident := ltac:(string2ident "fifo_put"%string).
Definition _free : ident := ltac:(string2ident "free"%string).
Definition _h : ident := 5%positive.
Definition _head : ident := 6%positive.
Definition _i : ident := 7%positive.
Definition _main : ident := ltac:(string2ident "main"%string).
Definition _make_elem : ident := ltac:(string2ident "make_elem"%string).
Definition _malloc : ident := ltac:(string2ident "malloc"%string).
Definition _n : ident := 8%positive.
Definition _next : ident := 9%positive.
Definition _p : ident := 10%positive.
Definition _surely_malloc : ident := ltac:(string2ident "surely_malloc"%string).
Definition _t : ident := 11%positive.
Definition _tail : ident := 12%positive.
Definition _t'1 : ident := 13%positive.
Definition _t'2 : ident := 14%positive.
Definition _t'3 : ident := 15%positive.
Definition _t'4 : ident := 16%positive.

Definition f_surely_malloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Etempvar _n tuint) :: nil))
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _p (tptr tvoid)) tint)
      (Scall None (Evar _exit (Tfunction (Tcons tint Tnil) tvoid cc_default))
        ((Econst_int (Int.repr 1) tint) :: nil))
      Sskip)
    (Sreturn (Some (Etempvar _p (tptr tvoid))))))
|}.

Definition f_fifo_new := {|
  fn_return := (tptr (Tstruct _fifo noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_Q, (tptr (Tstruct _fifo noattr))) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _fifo noattr) tuint) :: nil))
    (Sset _Q
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _fifo noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
          (Tstruct _fifo noattr)) _head (tptr (Tstruct _elem noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
            (Tstruct _fifo noattr)) _tail (tptr (Tstruct _elem noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Sreturn (Some (Etempvar _Q (tptr (Tstruct _fifo noattr))))))))
|}.

Definition f_fifo_put := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_Q, (tptr (Tstruct _fifo noattr))) ::
                (_p, (tptr (Tstruct _elem noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _elem noattr))) ::
               (_t, (tptr (Tstruct _elem noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _p (tptr (Tstruct _elem noattr)))
        (Tstruct _elem noattr)) _next (tptr (Tstruct _elem noattr)))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sset _h
      (Efield
        (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
          (Tstruct _fifo noattr)) _head (tptr (Tstruct _elem noattr))))
    (Sifthenelse (Ebinop Oeq (Etempvar _h (tptr (Tstruct _elem noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
              (Tstruct _fifo noattr)) _head (tptr (Tstruct _elem noattr)))
          (Etempvar _p (tptr (Tstruct _elem noattr))))
        (Sassign
          (Efield
            (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
              (Tstruct _fifo noattr)) _tail (tptr (Tstruct _elem noattr)))
          (Etempvar _p (tptr (Tstruct _elem noattr)))))
      (Ssequence
        (Sset _t
          (Efield
            (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
              (Tstruct _fifo noattr)) _tail (tptr (Tstruct _elem noattr))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _t (tptr (Tstruct _elem noattr)))
                (Tstruct _elem noattr)) _next (tptr (Tstruct _elem noattr)))
            (Etempvar _p (tptr (Tstruct _elem noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
                (Tstruct _fifo noattr)) _tail (tptr (Tstruct _elem noattr)))
            (Etempvar _p (tptr (Tstruct _elem noattr)))))))))
|}.

Definition f_fifo_empty := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_Q, (tptr (Tstruct _fifo noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _elem noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
        (Tstruct _fifo noattr)) _head (tptr (Tstruct _elem noattr))))
  (Sreturn (Some (Ebinop Oeq (Etempvar _h (tptr (Tstruct _elem noattr)))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint))))
|}.

Definition f_fifo_get := {|
  fn_return := (tptr (Tstruct _elem noattr));
  fn_callconv := cc_default;
  fn_params := ((_Q, (tptr (Tstruct _fifo noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _elem noattr))) ::
               (_n, (tptr (Tstruct _elem noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Efield
      (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
        (Tstruct _fifo noattr)) _head (tptr (Tstruct _elem noattr))))
  (Ssequence
    (Sset _n
      (Efield
        (Ederef (Etempvar _h (tptr (Tstruct _elem noattr)))
          (Tstruct _elem noattr)) _next (tptr (Tstruct _elem noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _Q (tptr (Tstruct _fifo noattr)))
            (Tstruct _fifo noattr)) _head (tptr (Tstruct _elem noattr)))
        (Etempvar _n (tptr (Tstruct _elem noattr))))
      (Sreturn (Some (Etempvar _h (tptr (Tstruct _elem noattr))))))))
|}.

Definition f_make_elem := {|
  fn_return := (tptr (Tstruct _elem noattr));
  fn_callconv := cc_default;
  fn_params := ((_data, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _elem noattr))) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _elem noattr) tuint) :: nil))
    (Sset _p (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _elem noattr)))
          (Tstruct _elem noattr)) _data tint) (Etempvar _data tint))
    (Sreturn (Some (Etempvar _p (tptr (Tstruct _elem noattr)))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_Q, (tptr (Tstruct _fifo noattr))) ::
               (_p, (tptr (Tstruct _elem noattr))) ::
               (_t'4, (tptr (Tstruct _elem noattr))) ::
               (_t'3, (tptr (Tstruct _elem noattr))) ::
               (_t'2, (tptr (Tstruct _elem noattr))) ::
               (_t'1, (tptr (Tstruct _fifo noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _fifo_new (Tfunction Tnil (tptr (Tstruct _fifo noattr))
                          cc_default)) nil)
      (Sset _Q (Etempvar _t'1 (tptr (Tstruct _fifo noattr)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _make_elem (Tfunction (Tcons tint Tnil)
                             (tptr (Tstruct _elem noattr)) cc_default))
          ((Econst_int (Int.repr 1) tint) :: nil))
        (Sset _p (Etempvar _t'2 (tptr (Tstruct _elem noattr)))))
      (Ssequence
        (Scall None
          (Evar _fifo_put (Tfunction
                            (Tcons (tptr (Tstruct _fifo noattr))
                              (Tcons (tptr (Tstruct _elem noattr)) Tnil))
                            tvoid cc_default))
          ((Etempvar _Q (tptr (Tstruct _fifo noattr))) ::
           (Etempvar _p (tptr (Tstruct _elem noattr))) :: nil))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _make_elem (Tfunction (Tcons tint Tnil)
                                 (tptr (Tstruct _elem noattr)) cc_default))
              ((Econst_int (Int.repr 2) tint) :: nil))
            (Sset _p (Etempvar _t'3 (tptr (Tstruct _elem noattr)))))
          (Ssequence
            (Scall None
              (Evar _fifo_put (Tfunction
                                (Tcons (tptr (Tstruct _fifo noattr))
                                  (Tcons (tptr (Tstruct _elem noattr)) Tnil))
                                tvoid cc_default))
              ((Etempvar _Q (tptr (Tstruct _fifo noattr))) ::
               (Etempvar _p (tptr (Tstruct _elem noattr))) :: nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _fifo_get (Tfunction
                                    (Tcons (tptr (Tstruct _fifo noattr))
                                      Tnil) (tptr (Tstruct _elem noattr))
                                    cc_default))
                  ((Etempvar _Q (tptr (Tstruct _fifo noattr))) :: nil))
                (Sset _p (Etempvar _t'4 (tptr (Tstruct _elem noattr)))))
              (Ssequence
                (Sset _i
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _elem noattr)))
                      (Tstruct _elem noattr)) _data tint))
                (Ssequence
                  (Scall None
                    (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                  cc_default))
                    ((Etempvar _p (tptr (Tstruct _elem noattr))) :: nil))
                  (Sreturn (Some (Etempvar _i tint)))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _elem Struct
   ((_data, tint) :: (_next, (tptr (Tstruct _elem noattr))) :: nil)
   noattr ::
 Composite _fifo Struct
   ((_head, (tptr (Tstruct _elem noattr))) ::
    (_tail, (tptr (Tstruct _elem noattr))) :: nil)
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
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_exit,
   Gfun(External (EF_external "exit"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons tint Tnil) tvoid cc_default)) ::
 (_surely_malloc, Gfun(Internal f_surely_malloc)) ::
 (_fifo_new, Gfun(Internal f_fifo_new)) ::
 (_fifo_put, Gfun(Internal f_fifo_put)) ::
 (_fifo_empty, Gfun(Internal f_fifo_empty)) ::
 (_fifo_get, Gfun(Internal f_fifo_get)) ::
 (_make_elem, Gfun(Internal f_make_elem)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _make_elem :: _fifo_get :: _fifo_empty :: _fifo_put :: _fifo_new ::
 _surely_malloc :: _exit :: _free :: _malloc :: ___builtin_debug ::
 ___builtin_nop :: ___builtin_write32_reversed ::
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


