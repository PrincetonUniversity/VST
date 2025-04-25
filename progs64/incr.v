From Coq Require Import String List ZArith.
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
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "progs64/incr.c".
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition __l : ident := $"_l".
Definition _a : ident := $"a".
Definition _acquire : ident := $"acquire".
Definition _append : ident := $"append".
Definition _atom_int : ident := $"atom_int".
Definition _b : ident := $"b".
Definition _c : ident := $"c".
Definition _compute2 : ident := $"compute2".
Definition _counter : ident := $"counter".
Definition _ctr : ident := $"ctr".
Definition _d : ident := $"d".
Definition _delete : ident := $"delete".
Definition _e : ident := $"e".
Definition _f : ident := $"f".
Definition _foo : ident := $"foo".
Definition _four : ident := $"four".
Definition _freeN : ident := $"freeN".
Definition _freelock : ident := $"freelock".
Definition _g : ident := $"g".
Definition _h : ident := $"h".
Definition _head : ident := $"head".
Definition _hi : ident := $"hi".
Definition _i : ident := $"i".
Definition _incr : ident := $"incr".
Definition _insert : ident := $"insert".
Definition _j : ident := $"j".
Definition _key : ident := $"key".
Definition _l : ident := $"l".
Definition _left : ident := $"left".
Definition _list : ident := $"list".
Definition _lo : ident := $"lo".
Definition _lock : ident := $"lock".
Definition _lookup : ident := $"lookup".
Definition _main : ident := $"main".
Definition _makelock : ident := $"makelock".
Definition _mallocN : ident := $"mallocN".
Definition _mid : ident := $"mid".
Definition _p : ident := $"p".
Definition _pa : ident := $"pa".
Definition _pb : ident := $"pb".
Definition _pushdown_left : ident := $"pushdown_left".
Definition _q : ident := $"q".
Definition _r : ident := $"r".
Definition _read : ident := $"read".
Definition _release : ident := $"release".
Definition _right : ident := $"right".
Definition _s : ident := $"s".
Definition _search : ident := $"search".
Definition _spawn : ident := $"spawn".
Definition _sub1 : ident := $"sub1".
Definition _sub2 : ident := $"sub2".
Definition _sub3 : ident := $"sub3".
Definition _t : ident := $"t".
Definition _tail : ident := $"tail".
Definition _tgt : ident := $"tgt".
Definition _thread_func : ident := $"thread_func".
Definition _thread_lock : ident := $"thread_lock".
Definition _tree : ident := $"tree".
Definition _tree_free : ident := $"tree_free".
Definition _treebox_free : ident := $"treebox_free".
Definition _treebox_new : ident := $"treebox_new".
Definition _turn_left : ident := $"turn_left".
Definition _u : ident := $"u".
Definition _v : ident := $"v".
Definition _val : ident := $"val".
Definition _value : ident := $"value".
Definition _x : ident := $"x".
Definition _x1 : ident := $"x1".
Definition _x2 : ident := $"x2".
Definition _y : ident := $"y".
Definition _y1 : ident := $"y1".
Definition _y2 : ident := $"y2".
Definition _z : ident := $"z".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.

Definition v_c := {|
  gvar_info := (Tstruct _counter noattr);
  gvar_init := (Init_space 16 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_incr := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'3, (tptr (Tstruct _atom_int noattr))) :: (_t'2, tuint) ::
               (_t'1, (tptr (Tstruct _atom_int noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield (Evar _c (Tstruct _counter noattr)) _lock
        (tptr (Tstruct _atom_int noattr))))
    (Scall None
      (Evar _acquire (Tfunction ((tptr (Tstruct _atom_int noattr)) :: nil)
                       tvoid cc_default))
      ((Etempvar _t'3 (tptr (Tstruct _atom_int noattr))) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'2 (Efield (Evar _c (Tstruct _counter noattr)) _ctr tuint))
      (Sassign (Efield (Evar _c (Tstruct _counter noattr)) _ctr tuint)
        (Ebinop Oadd (Etempvar _t'2 tuint) (Econst_int (Int.repr 1) tint)
          tuint)))
    (Ssequence
      (Sset _t'1
        (Efield (Evar _c (Tstruct _counter noattr)) _lock
          (tptr (Tstruct _atom_int noattr))))
      (Scall None
        (Evar _release (Tfunction ((tptr (Tstruct _atom_int noattr)) :: nil)
                         tvoid cc_default))
        ((Etempvar _t'1 (tptr (Tstruct _atom_int noattr))) :: nil)))))
|}.

Definition f_read := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t, tuint) :: (_t'2, (tptr (Tstruct _atom_int noattr))) ::
               (_t'1, (tptr (Tstruct _atom_int noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield (Evar _c (Tstruct _counter noattr)) _lock
        (tptr (Tstruct _atom_int noattr))))
    (Scall None
      (Evar _acquire (Tfunction ((tptr (Tstruct _atom_int noattr)) :: nil)
                       tvoid cc_default))
      ((Etempvar _t'2 (tptr (Tstruct _atom_int noattr))) :: nil)))
  (Ssequence
    (Sset _t (Efield (Evar _c (Tstruct _counter noattr)) _ctr tuint))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield (Evar _c (Tstruct _counter noattr)) _lock
            (tptr (Tstruct _atom_int noattr))))
        (Scall None
          (Evar _release (Tfunction
                           ((tptr (Tstruct _atom_int noattr)) :: nil) tvoid
                           cc_default))
          ((Etempvar _t'1 (tptr (Tstruct _atom_int noattr))) :: nil)))
      (Sreturn (Some (Etempvar _t tuint))))))
|}.

Definition f_thread_func := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_thread_lock, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None (Evar _incr (Tfunction nil tvoid cc_default)) nil)
  (Ssequence
    (Scall None
      (Evar _release (Tfunction ((tptr (Tstruct _atom_int noattr)) :: nil)
                       tvoid cc_default))
      ((Ecast (Etempvar _thread_lock (tptr tvoid))
         (tptr (Tstruct _atom_int noattr))) :: nil))
    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_compute2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_thread_lock, (tptr (Tstruct _atom_int noattr))) ::
               (_t, tuint) :: (_t'3, tuint) ::
               (_t'2, (tptr (Tstruct _atom_int noattr))) ::
               (_t'1, (tptr (Tstruct _atom_int noattr))) ::
               (_t'6, (tptr (Tstruct _atom_int noattr))) ::
               (_t'5, (tptr (Tstruct _atom_int noattr))) ::
               (_t'4, (tptr (Tstruct _atom_int noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Efield (Evar _c (Tstruct _counter noattr)) _ctr tuint)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _makelock (Tfunction nil (tptr (Tstruct _atom_int noattr))
                          cc_default)) nil)
      (Sassign
        (Efield (Evar _c (Tstruct _counter noattr)) _lock
          (tptr (Tstruct _atom_int noattr)))
        (Etempvar _t'1 (tptr (Tstruct _atom_int noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Efield (Evar _c (Tstruct _counter noattr)) _lock
            (tptr (Tstruct _atom_int noattr))))
        (Scall None
          (Evar _release (Tfunction
                           ((tptr (Tstruct _atom_int noattr)) :: nil) tvoid
                           cc_default))
          ((Etempvar _t'6 (tptr (Tstruct _atom_int noattr))) :: nil)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _makelock (Tfunction nil (tptr (Tstruct _atom_int noattr))
                              cc_default)) nil)
          (Sset _thread_lock
            (Etempvar _t'2 (tptr (Tstruct _atom_int noattr)))))
        (Ssequence
          (Scall None
            (Evar _spawn (Tfunction
                           ((tptr (Tfunction ((tptr tvoid) :: nil) tint
                                    cc_default)) :: (tptr tvoid) :: nil)
                           tvoid cc_default))
            ((Ecast
               (Eaddrof
                 (Evar _thread_func (Tfunction ((tptr tvoid) :: nil) tint
                                      cc_default))
                 (tptr (Tfunction ((tptr tvoid) :: nil) tint cc_default)))
               (tptr tvoid)) ::
             (Ecast (Etempvar _thread_lock (tptr (Tstruct _atom_int noattr)))
               (tptr tvoid)) :: nil))
          (Ssequence
            (Scall None (Evar _incr (Tfunction nil tvoid cc_default)) nil)
            (Ssequence
              (Scall None
                (Evar _acquire (Tfunction
                                 ((tptr (Tstruct _atom_int noattr)) :: nil)
                                 tvoid cc_default))
                ((Etempvar _thread_lock (tptr (Tstruct _atom_int noattr))) ::
                 nil))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _read (Tfunction nil tuint cc_default)) nil)
                  (Sset _t (Etempvar _t'3 tuint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Efield (Evar _c (Tstruct _counter noattr)) _lock
                        (tptr (Tstruct _atom_int noattr))))
                    (Scall None
                      (Evar _acquire (Tfunction
                                       ((tptr (Tstruct _atom_int noattr)) ::
                                        nil) tvoid cc_default))
                      ((Etempvar _t'5 (tptr (Tstruct _atom_int noattr))) ::
                       nil)))
                  (Ssequence
                    (Scall None
                      (Evar _freelock (Tfunction
                                        ((tptr (Tstruct _atom_int noattr)) ::
                                         nil) tvoid cc_default))
                      ((Etempvar _thread_lock (tptr (Tstruct _atom_int noattr))) ::
                       nil))
                    (Ssequence
                      (Ssequence
                        (Sset _t'4
                          (Efield (Evar _c (Tstruct _counter noattr)) _lock
                            (tptr (Tstruct _atom_int noattr))))
                        (Scall None
                          (Evar _freelock (Tfunction
                                            ((tptr (Tstruct _atom_int noattr)) ::
                                             nil) tvoid cc_default))
                          ((Etempvar _t'4 (tptr (Tstruct _atom_int noattr))) ::
                           nil)))
                      (Sreturn (Some (Etempvar _t tuint))))))))))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _compute2 (Tfunction nil tint cc_default)) nil)
    (Sreturn (Some (Etempvar _t'1 tint))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _counter Struct
   (Member_plain _ctr tuint ::
    Member_plain _lock (tptr (Tstruct _atom_int noattr)) :: nil)
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
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
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
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
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
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
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
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
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
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
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
 (_makelock,
   Gfun(External (EF_external "makelock"
                   (mksignature nil AST.Xptr cc_default)) nil
     (tptr (Tstruct _atom_int noattr)) cc_default)) ::
 (_freelock,
   Gfun(External (EF_external "freelock"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _atom_int noattr)) :: nil) tvoid cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _atom_int noattr)) :: nil) tvoid cc_default)) ::
 (_release,
   Gfun(External (EF_external "release"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _atom_int noattr)) :: nil) tvoid cc_default)) ::
 (_spawn,
   Gfun(External (EF_external "spawn"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tfunction ((tptr tvoid) :: nil) tint cc_default)) ::
      (tptr tvoid) :: nil) tvoid cc_default)) :: (_c, Gvar v_c) ::
 (_incr, Gfun(Internal f_incr)) :: (_read, Gfun(Internal f_read)) ::
 (_thread_func, Gfun(Internal f_thread_func)) ::
 (_compute2, Gfun(Internal f_compute2)) :: (_main, Gfun(Internal f_main)) ::
 nil).

Definition public_idents : list ident :=
(_main :: _compute2 :: _thread_func :: _read :: _incr :: _c :: _spawn ::
 _release :: _acquire :: _freelock :: _makelock :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


