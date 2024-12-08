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
  Definition source_file := "progs64/strlib.c".
  Definition normalized := true.
End Info.

Definition _N : ident := $"N".
Definition _Q : ident := $"Q".
Definition __IO_FILE : ident := $"_IO_FILE".
Definition __IO_backup_base : ident := $"_IO_backup_base".
Definition __IO_buf_base : ident := $"_IO_buf_base".
Definition __IO_buf_end : ident := $"_IO_buf_end".
Definition __IO_codecvt : ident := $"_IO_codecvt".
Definition __IO_marker : ident := $"_IO_marker".
Definition __IO_read_base : ident := $"_IO_read_base".
Definition __IO_read_end : ident := $"_IO_read_end".
Definition __IO_read_ptr : ident := $"_IO_read_ptr".
Definition __IO_save_base : ident := $"_IO_save_base".
Definition __IO_save_end : ident := $"_IO_save_end".
Definition __IO_wide_data : ident := $"_IO_wide_data".
Definition __IO_write_base : ident := $"_IO_write_base".
Definition __IO_write_end : ident := $"_IO_write_end".
Definition __IO_write_ptr : ident := $"_IO_write_ptr".
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
Definition ___pad5 : ident := $"__pad5".
Definition ___stringlit_1 : ident := $"__stringlit_1".
Definition ___stringlit_2 : ident := $"__stringlit_2".
Definition ___stringlit_3 : ident := $"__stringlit_3".
Definition ___stringlit_4 : ident := $"__stringlit_4".
Definition __chain : ident := $"_chain".
Definition __codecvt : ident := $"_codecvt".
Definition __cur_column : ident := $"_cur_column".
Definition __fileno : ident := $"_fileno".
Definition __flags : ident := $"_flags".
Definition __flags2 : ident := $"_flags2".
Definition __freeres_buf : ident := $"_freeres_buf".
Definition __freeres_list : ident := $"_freeres_list".
Definition __l : ident := $"_l".
Definition __lock : ident := $"_lock".
Definition __markers : ident := $"_markers".
Definition __mode : ident := $"_mode".
Definition __offset : ident := $"_offset".
Definition __old_offset : ident := $"_old_offset".
Definition __shortbuf : ident := $"_shortbuf".
Definition __unused2 : ident := $"_unused2".
Definition __vtable_offset : ident := $"_vtable_offset".
Definition __wide_data : ident := $"_wide_data".
Definition _a : ident := $"a".
Definition _acquire : ident := $"acquire".
Definition _append : ident := $"append".
Definition _args : ident := $"args".
Definition _atom_int : ident := $"atom_int".
Definition _b : ident := $"b".
Definition _buf : ident := $"buf".
Definition _bufsize : ident := $"bufsize".
Definition _c : ident := $"c".
Definition _compute2 : ident := $"compute2".
Definition _counter : ident := $"counter".
Definition _ctr : ident := $"ctr".
Definition _d : ident := $"d".
Definition _d1 : ident := $"d1".
Definition _d2 : ident := $"d2".
Definition _data : ident := $"data".
Definition _delete : ident := $"delete".
Definition _des : ident := $"des".
Definition _deserialize : ident := $"deserialize".
Definition _dest : ident := $"dest".
Definition _dest_ctr : ident := $"dest_ctr".
Definition _do_and : ident := $"do_and".
Definition _do_or : ident := $"do_or".
Definition _e : ident := $"e".
Definition _elem : ident := $"elem".
Definition _exit : ident := $"exit".
Definition _f : ident := $"f".
Definition _fifo : ident := $"fifo".
Definition _fifo_empty : ident := $"fifo_empty".
Definition _fifo_get : ident := $"fifo_get".
Definition _fifo_new : ident := $"fifo_new".
Definition _fifo_put : ident := $"fifo_put".
Definition _foo : ident := $"foo".
Definition _foo_methods : ident := $"foo_methods".
Definition _foo_object : ident := $"foo_object".
Definition _foo_reset : ident := $"foo_reset".
Definition _foo_twiddle : ident := $"foo_twiddle".
Definition _four : ident := $"four".
Definition _fprintf : ident := $"fprintf".
Definition _free : ident := $"free".
Definition _freeN : ident := $"freeN".
Definition _freelock : ident := $"freelock".
Definition _g : ident := $"g".
Definition _get : ident := $"get".
Definition _get_branch : ident := $"get_branch".
Definition _getchar : ident := $"getchar".
Definition _getchar_blocking : ident := $"getchar_blocking".
Definition _getchars : ident := $"getchars".
Definition _h : ident := $"h".
Definition _head : ident := $"head".
Definition _hi : ident := $"hi".
Definition _i : ident := $"i".
Definition _i__1 : ident := $"i__1".
Definition _i__2 : ident := $"i__2".
Definition _incr : ident := $"incr".
Definition _init_ctr : ident := $"init_ctr".
Definition _insert : ident := $"insert".
Definition _intpair : ident := $"intpair".
Definition _intpair_deserialize : ident := $"intpair_deserialize".
Definition _intpair_message : ident := $"intpair_message".
Definition _intpair_serialize : ident := $"intpair_serialize".
Definition _j : ident := $"j".
Definition _k : ident := $"k".
Definition _key : ident := $"key".
Definition _l : ident := $"l".
Definition _last_foo : ident := $"last_foo".
Definition _left : ident := $"left".
Definition _len : ident := $"len".
Definition _length : ident := $"length".
Definition _list : ident := $"list".
Definition _lo : ident := $"lo".
Definition _lock : ident := $"lock".
Definition _lookup : ident := $"lookup".
Definition _main : ident := $"main".
Definition _make_elem : ident := $"make_elem".
Definition _make_foo : ident := $"make_foo".
Definition _makelock : ident := $"makelock".
Definition _malloc : ident := $"malloc".
Definition _mallocN : ident := $"mallocN".
Definition _message : ident := $"message".
Definition _methods : ident := $"methods".
Definition _mid : ident := $"mid".
Definition _min : ident := $"min".
Definition _minimum : ident := $"minimum".
Definition _mtable : ident := $"mtable".
Definition _multi_command : ident := $"multi_command".
Definition _multi_command_s : ident := $"multi_command_s".
Definition _n : ident := $"n".
Definition _next : ident := $"next".
Definition _object : ident := $"object".
Definition _p : ident := $"p".
Definition _p0 : ident := $"p0".
Definition _p1 : ident := $"p1".
Definition _p2 : ident := $"p2".
Definition _p3 : ident := $"p3".
Definition _p4 : ident := $"p4".
Definition _p5 : ident := $"p5".
Definition _p6 : ident := $"p6".
Definition _p7 : ident := $"p7".
Definition _p_fa : ident := $"p_fa".
Definition _p_reset : ident := $"p_reset".
Definition _p_twiddle : ident := $"p_twiddle".
Definition _pa : ident := $"pa".
Definition _pb : ident := $"pb".
Definition _print_int : ident := $"print_int".
Definition _print_intr : ident := $"print_intr".
Definition _printf : ident := $"printf".
Definition _pushdown_left : ident := $"pushdown_left".
Definition _putchar : ident := $"putchar".
Definition _putchar_blocking : ident := $"putchar_blocking".
Definition _putchars : ident := $"putchars".
Definition _q : ident := $"q".
Definition _r : ident := $"r".
Definition _read : ident := $"read".
Definition _release : ident := $"release".
Definition _res : ident := $"res".
Definition _reset : ident := $"reset".
Definition _reverse : ident := $"reverse".
Definition _right : ident := $"right".
Definition _s : ident := $"s".
Definition _search : ident := $"search".
Definition _self : ident := $"self".
Definition _ser : ident := $"ser".
Definition _serialize : ident := $"serialize".
Definition _set : ident := $"set".
Definition _shift : ident := $"shift".
Definition _sorted_shift : ident := $"sorted_shift".
Definition _spawn : ident := $"spawn".
Definition _src : ident := $"src".
Definition _stdout : ident := $"stdout".
Definition _str : ident := $"str".
Definition _str1 : ident := $"str1".
Definition _str2 : ident := $"str2".
Definition _strcat : ident := $"strcat".
Definition _strchr : ident := $"strchr".
Definition _strcmp : ident := $"strcmp".
Definition _strcpy : ident := $"strcpy".
Definition _strlen : ident := $"strlen".
Definition _sub1 : ident := $"sub1".
Definition _sub2 : ident := $"sub2".
Definition _sub3 : ident := $"sub3".
Definition _sumlist : ident := $"sumlist".
Definition _surely_malloc : ident := $"surely_malloc".
Definition _t : ident := $"t".
Definition _tail : ident := $"tail".
Definition _tgt : ident := $"tgt".
Definition _thread_func : ident := $"thread_func".
Definition _thread_lock : ident := $"thread_lock".
Definition _three : ident := $"three".
Definition _tree : ident := $"tree".
Definition _tree_free : ident := $"tree_free".
Definition _treebox_free : ident := $"treebox_free".
Definition _treebox_new : ident := $"treebox_new".
Definition _turn_left : ident := $"turn_left".
Definition _twiddle : ident := $"twiddle".
Definition _u : ident := $"u".
Definition _v : ident := $"v".
Definition _val : ident := $"val".
Definition _value : ident := $"value".
Definition _w : ident := $"w".
Definition _x : ident := $"x".
Definition _x1 : ident := $"x1".
Definition _x2 : ident := $"x2".
Definition _y : ident := $"y".
Definition _y1 : ident := $"y1".
Definition _y2 : ident := $"y2".
Definition _z : ident := $"z".
Definition _z1 : ident := $"z1".
Definition _z2 : ident := $"z2".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.

Definition f_strchr := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: (_c, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_d, tschar) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _str (tptr tschar)) (Etempvar _i tulong)
                (tptr tschar)) tschar))
          (Sset _d (Ecast (Etempvar _t'1 tschar) tschar)))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _d tschar) (Etempvar _c tint)
                         tint)
            (Sreturn (Some (Ebinop Oadd (Etempvar _str (tptr tschar))
                             (Etempvar _i tulong) (tptr tschar))))
            Sskip)
          (Sifthenelse (Ebinop Oeq (Etempvar _d tschar)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_strcpy := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr tschar)) :: (_src, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_d, tschar) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _src (tptr tschar)) (Etempvar _i tulong)
                (tptr tschar)) tschar))
          (Sset _d (Ecast (Etempvar _t'1 tschar) tschar)))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _dest (tptr tschar))
                (Etempvar _i tulong) (tptr tschar)) tschar)
            (Etempvar _d tschar))
          (Sifthenelse (Ebinop Oeq (Etempvar _d tschar)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sreturn (Some (Etempvar _dest (tptr tschar))))
            Sskip))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_strcat := {|
  fn_return := (tptr tschar);
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr tschar)) :: (_src, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_j, tulong) :: (_d, tschar) ::
               (_t'2, tschar) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        Sskip
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _dest (tptr tschar))
                  (Etempvar _i tulong) (tptr tschar)) tschar))
            (Sset _d (Ecast (Etempvar _t'2 tschar) tschar)))
          (Sifthenelse (Ebinop Oeq (Etempvar _d tschar)
                         (Econst_int (Int.repr 0) tint) tint)
            Sbreak
            Sskip)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Ssequence
    (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        Sskip
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _src (tptr tschar))
                  (Etempvar _j tulong) (tptr tschar)) tschar))
            (Sset _d (Ecast (Etempvar _t'1 tschar) tschar)))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _dest (tptr tschar))
                  (Ebinop Oadd (Etempvar _i tulong) (Etempvar _j tulong)
                    tulong) (tptr tschar)) tschar) (Etempvar _d tschar))
            (Sifthenelse (Ebinop Oeq (Etempvar _d tschar)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sreturn (Some (Etempvar _dest (tptr tschar))))
              Sskip))))
      (Sset _j
        (Ebinop Oadd (Etempvar _j tulong) (Econst_int (Int.repr 1) tint)
          tulong)))))
|}.

Definition f_strcmp := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_str1, (tptr tschar)) :: (_str2, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_d1, tuchar) :: (_d2, tuchar) ::
               (_t'1, tint) :: (_t'3, tschar) :: (_t'2, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Ssequence
          (Sset _t'3
            (Ederef
              (Ebinop Oadd (Etempvar _str1 (tptr tschar))
                (Etempvar _i tulong) (tptr tschar)) tschar))
          (Sset _d1 (Ecast (Ecast (Etempvar _t'3 tschar) tuchar) tuchar)))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _str2 (tptr tschar))
                  (Etempvar _i tulong) (tptr tschar)) tschar))
            (Sset _d2 (Ecast (Ecast (Etempvar _t'2 tschar) tuchar) tuchar)))
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _d1 tuchar)
                           (Econst_int (Int.repr 0) tint) tint)
              (Sset _t'1
                (Ecast
                  (Ebinop Oeq (Etempvar _d2 tuchar)
                    (Econst_int (Int.repr 0) tint) tint) tbool))
              (Sset _t'1 (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar _t'1 tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Ebinop Olt (Etempvar _d1 tuchar)
                             (Etempvar _d2 tuchar) tint)
                (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                 tint)))
                (Sifthenelse (Ebinop Ogt (Etempvar _d1 tuchar)
                               (Etempvar _d2 tuchar) tint)
                  (Sreturn (Some (Econst_int (Int.repr 1) tint)))
                  Sskip)))))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_strlen := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_str, (tptr tschar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'1, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      Sskip
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _str (tptr tschar)) (Etempvar _i tulong)
              (tptr tschar)) tschar))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tschar)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sreturn (Some (Etempvar _i tulong)))
          Sskip)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition composites : list composite_definition :=
nil.

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
 (_strchr, Gfun(Internal f_strchr)) :: (_strcpy, Gfun(Internal f_strcpy)) ::
 (_strcat, Gfun(Internal f_strcat)) :: (_strcmp, Gfun(Internal f_strcmp)) ::
 (_strlen, Gfun(Internal f_strlen)) :: nil).

Definition public_idents : list ident :=
(_strlen :: _strcmp :: _strcat :: _strcpy :: _strchr :: ___builtin_debug ::
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


