From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.12".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "32sse2".
  Definition abi := "standard".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "progs/printf.c".
  Definition normalized := true.
End Info.

Definition __139 : ident := 4%positive.
Definition __140 : ident := 1%positive.
Definition __213 : ident := 92%positive.
Definition __214 : ident := 69%positive.
Definition __215 : ident := 89%positive.
Definition __Bigint : ident := 7%positive.
Definition ___builtin_annot : ident := 132%positive.
Definition ___builtin_annot_intval : ident := 133%positive.
Definition ___builtin_bswap : ident := 117%positive.
Definition ___builtin_bswap16 : ident := 119%positive.
Definition ___builtin_bswap32 : ident := 118%positive.
Definition ___builtin_bswap64 : ident := 116%positive.
Definition ___builtin_clz : ident := 120%positive.
Definition ___builtin_clzl : ident := 121%positive.
Definition ___builtin_clzll : ident := 122%positive.
Definition ___builtin_ctz : ident := 123%positive.
Definition ___builtin_ctzl : ident := 124%positive.
Definition ___builtin_ctzll : ident := 125%positive.
Definition ___builtin_debug : ident := 151%positive.
Definition ___builtin_expect : ident := 140%positive.
Definition ___builtin_fabs : ident := 126%positive.
Definition ___builtin_fabsf : ident := 127%positive.
Definition ___builtin_fmadd : ident := 143%positive.
Definition ___builtin_fmax : ident := 141%positive.
Definition ___builtin_fmin : ident := 142%positive.
Definition ___builtin_fmsub : ident := 144%positive.
Definition ___builtin_fnmadd : ident := 145%positive.
Definition ___builtin_fnmsub : ident := 146%positive.
Definition ___builtin_fsqrt : ident := 128%positive.
Definition ___builtin_membar : ident := 134%positive.
Definition ___builtin_memcpy_aligned : ident := 130%positive.
Definition ___builtin_read16_reversed : ident := 147%positive.
Definition ___builtin_read32_reversed : ident := 148%positive.
Definition ___builtin_sel : ident := 131%positive.
Definition ___builtin_sqrt : ident := 129%positive.
Definition ___builtin_unreachable : ident := 139%positive.
Definition ___builtin_va_arg : ident := 136%positive.
Definition ___builtin_va_copy : ident := 137%positive.
Definition ___builtin_va_end : ident := 138%positive.
Definition ___builtin_va_start : ident := 135%positive.
Definition ___builtin_write16_reversed : ident := 149%positive.
Definition ___builtin_write32_reversed : ident := 150%positive.
Definition ___cleanup : ident := 104%positive.
Definition ___compcert_i64_dtos : ident := 163%positive.
Definition ___compcert_i64_dtou : ident := 164%positive.
Definition ___compcert_i64_sar : ident := 175%positive.
Definition ___compcert_i64_sdiv : ident := 169%positive.
Definition ___compcert_i64_shl : ident := 173%positive.
Definition ___compcert_i64_shr : ident := 174%positive.
Definition ___compcert_i64_smod : ident := 171%positive.
Definition ___compcert_i64_smulh : ident := 176%positive.
Definition ___compcert_i64_stod : ident := 165%positive.
Definition ___compcert_i64_stof : ident := 167%positive.
Definition ___compcert_i64_udiv : ident := 170%positive.
Definition ___compcert_i64_umod : ident := 172%positive.
Definition ___compcert_i64_umulh : ident := 177%positive.
Definition ___compcert_i64_utod : ident := 166%positive.
Definition ___compcert_i64_utof : ident := 168%positive.
Definition ___compcert_va_composite : ident := 162%positive.
Definition ___compcert_va_float64 : ident := 161%positive.
Definition ___compcert_va_int32 : ident := 159%positive.
Definition ___compcert_va_int64 : ident := 160%positive.
Definition ___count : ident := 5%positive.
Definition ___getreent : ident := 152%positive.
Definition ___locale_t : ident := 102%positive.
Definition ___sFILE64 : ident := 35%positive.
Definition ___sbuf : ident := 32%positive.
Definition ___sdidinit : ident := 103%positive.
Definition ___sf : ident := 115%positive.
Definition ___sglue : ident := 114%positive.
Definition ___stringlit_1 : ident := 155%positive.
Definition ___stringlit_2 : ident := 156%positive.
Definition ___stringlit_3 : ident := 157%positive.
Definition ___tm : ident := 14%positive.
Definition ___tm_hour : ident := 17%positive.
Definition ___tm_isdst : ident := 23%positive.
Definition ___tm_mday : ident := 18%positive.
Definition ___tm_min : ident := 16%positive.
Definition ___tm_mon : ident := 19%positive.
Definition ___tm_sec : ident := 15%positive.
Definition ___tm_wday : ident := 21%positive.
Definition ___tm_yday : ident := 22%positive.
Definition ___tm_year : ident := 20%positive.
Definition ___value : ident := 6%positive.
Definition ___wch : ident := 2%positive.
Definition ___wchb : ident := 3%positive.
Definition __add : ident := 68%positive.
Definition __asctime_buf : ident := 72%positive.
Definition __atexit : ident := 29%positive.
Definition __atexit0 : ident := 112%positive.
Definition __base : ident := 33%positive.
Definition __bf : ident := 41%positive.
Definition __blksize : ident := 56%positive.
Definition __close : ident := 49%positive.
Definition __cookie : ident := 45%positive.
Definition __cvtbuf : ident := 110%positive.
Definition __cvtlen : ident := 109%positive.
Definition __data : ident := 43%positive.
Definition __dso_handle : ident := 26%positive.
Definition __emergency : ident := 99%positive.
Definition __errno : ident := 94%positive.
Definition __file : ident := 40%positive.
Definition __flags : ident := 39%positive.
Definition __flags2 : ident := 57%positive.
Definition __fnargs : ident := 25%positive.
Definition __fns : ident := 31%positive.
Definition __fntypes : ident := 27%positive.
Definition __freelist : ident := 108%positive.
Definition __gamma_signgam : ident := 74%positive.
Definition __getdate_err : ident := 82%positive.
Definition __glue : ident := 62%positive.
Definition __h_errno : ident := 88%positive.
Definition __inc : ident := 98%positive.
Definition __ind : ident := 30%positive.
Definition __iobs : ident := 64%positive.
Definition __is_cxa : ident := 28%positive.
Definition __k : ident := 9%positive.
Definition __l64a_buf : ident := 80%positive.
Definition __lb : ident := 55%positive.
Definition __lbfsize : ident := 42%positive.
Definition __locale : ident := 101%positive.
Definition __localtime_buf : ident := 73%positive.
Definition __lock : ident := 60%positive.
Definition __maxwds : ident := 10%positive.
Definition __mblen_state : ident := 77%positive.
Definition __mbrlen_state : ident := 83%positive.
Definition __mbrtowc_state : ident := 84%positive.
Definition __mbsrtowcs_state : ident := 85%positive.
Definition __mbstate : ident := 61%positive.
Definition __mbtowc_state : ident := 78%positive.
Definition __mult : ident := 67%positive.
Definition __nbuf : ident := 54%positive.
Definition __new : ident := 111%positive.
Definition __next : ident := 8%positive.
Definition __nextf : ident := 90%positive.
Definition __niobs : ident := 63%positive.
Definition __nmalloc : ident := 91%positive.
Definition __offset : ident := 58%positive.
Definition __on_exit_args : ident := 24%positive.
Definition __p : ident := 36%positive.
Definition __p5s : ident := 107%positive.
Definition __r : ident := 37%positive.
Definition __r48 : ident := 76%positive.
Definition __rand48 : ident := 65%positive.
Definition __rand_next : ident := 75%positive.
Definition __read : ident := 46%positive.
Definition __reent : ident := 44%positive.
Definition __result : ident := 105%positive.
Definition __result_k : ident := 106%positive.
Definition __seed : ident := 66%positive.
Definition __seek : ident := 48%positive.
Definition __seek64 : ident := 59%positive.
Definition __sig_func : ident := 113%positive.
Definition __sign : ident := 11%positive.
Definition __signal_buf : ident := 81%positive.
Definition __size : ident := 34%positive.
Definition __stderr : ident := 97%positive.
Definition __stdin : ident := 95%positive.
Definition __stdout : ident := 96%positive.
Definition __strtok_last : ident := 71%positive.
Definition __ub : ident := 50%positive.
Definition __ubuf : ident := 53%positive.
Definition __unspecified_locale_info : ident := 100%positive.
Definition __unused : ident := 93%positive.
Definition __unused_rand : ident := 70%positive.
Definition __up : ident := 51%positive.
Definition __ur : ident := 52%positive.
Definition __w : ident := 38%positive.
Definition __wcrtomb_state : ident := 86%positive.
Definition __wcsrtombs_state : ident := 87%positive.
Definition __wctomb_state : ident := 79%positive.
Definition __wds : ident := 12%positive.
Definition __write : ident := 47%positive.
Definition __x : ident := 13%positive.
Definition _fprintf : ident := 153%positive.
Definition _main : ident := 158%positive.
Definition _printf : ident := 154%positive.
Definition _t'1 : ident := 178%positive.
Definition _t'2 : ident := 179%positive.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 16);
  gvar_init := (Init_int8 (Int.repr 84) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 37) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 37) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 46) ::
                Init_int8 (Int.repr 10) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 110) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 15);
  gvar_init := (Init_int8 (Int.repr 72) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 44) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 119) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 108) :: Init_int8 (Int.repr 100) ::
                Init_int8 (Int.repr 33) :: Init_int8 (Int.repr 10) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct __reent noattr))) ::
               (_t'2, (tptr (Tstruct ___sFILE64 noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None
      (Evar _printf (Tfunction (Tcons (tptr tschar) Tnil) tint
                      {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
      ((Evar ___stringlit_1 (tarray tschar 15)) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar ___getreent (Tfunction Tnil (tptr (Tstruct __reent noattr))
                              cc_default)) nil)
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _t'1 (tptr (Tstruct __reent noattr)))
                (Tstruct __reent noattr)) __stdout
              (tptr (Tstruct ___sFILE64 noattr))))
          (Scall None
            (Evar _fprintf (Tfunction
                             (Tcons (tptr (Tstruct ___sFILE64 noattr))
                               (Tcons (tptr tschar) Tnil)) tint
                             {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
            ((Etempvar _t'2 (tptr (Tstruct ___sFILE64 noattr))) ::
             (Evar ___stringlit_3 (tarray tschar 16)) ::
             (Evar ___stringlit_2 (tarray tschar 5)) ::
             (Econst_int (Int.repr 2) tint) :: nil))))
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite __140 Union
   (Member_plain ___wch tuint :: Member_plain ___wchb (tarray tuchar 4) ::
    nil)
   noattr ::
 Composite __139 Struct
   (Member_plain ___count tint ::
    Member_plain ___value (Tunion __140 noattr) :: nil)
   noattr ::
 Composite __Bigint Struct
   (Member_plain __next (tptr (Tstruct __Bigint noattr)) ::
    Member_plain __k tint :: Member_plain __maxwds tint ::
    Member_plain __sign tint :: Member_plain __wds tint ::
    Member_plain __x (tarray tuint 1) :: nil)
   noattr ::
 Composite ___tm Struct
   (Member_plain ___tm_sec tint :: Member_plain ___tm_min tint ::
    Member_plain ___tm_hour tint :: Member_plain ___tm_mday tint ::
    Member_plain ___tm_mon tint :: Member_plain ___tm_year tint ::
    Member_plain ___tm_wday tint :: Member_plain ___tm_yday tint ::
    Member_plain ___tm_isdst tint :: nil)
   noattr ::
 Composite __on_exit_args Struct
   (Member_plain __fnargs (tarray (tptr tvoid) 32) ::
    Member_plain __dso_handle (tarray (tptr tvoid) 32) ::
    Member_plain __fntypes tuint :: Member_plain __is_cxa tuint :: nil)
   noattr ::
 Composite __atexit Struct
   (Member_plain __next (tptr (Tstruct __atexit noattr)) ::
    Member_plain __ind tint ::
    Member_plain __fns (tarray (tptr (Tfunction Tnil tvoid cc_default)) 32) ::
    Member_plain __on_exit_args (Tstruct __on_exit_args noattr) :: nil)
   noattr ::
 Composite ___sbuf Struct
   (Member_plain __base (tptr tuchar) :: Member_plain __size tint :: nil)
   noattr ::
 Composite ___sFILE64 Struct
   (Member_plain __p (tptr tuchar) :: Member_plain __r tint ::
    Member_plain __w tint :: Member_plain __flags tshort ::
    Member_plain __file tshort ::
    Member_plain __bf (Tstruct ___sbuf noattr) ::
    Member_plain __lbfsize tint ::
    Member_plain __data (tptr (Tstruct __reent noattr)) ::
    Member_plain __cookie (tptr tvoid) ::
    Member_plain __read
      (tptr (Tfunction
              (Tcons (tptr (Tstruct __reent noattr))
                (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tuint Tnil))))
              tint cc_default)) ::
    Member_plain __write
      (tptr (Tfunction
              (Tcons (tptr (Tstruct __reent noattr))
                (Tcons (tptr tvoid) (Tcons (tptr tschar) (Tcons tuint Tnil))))
              tint cc_default)) ::
    Member_plain __seek
      (tptr (Tfunction
              (Tcons (tptr (Tstruct __reent noattr))
                (Tcons (tptr tvoid) (Tcons tint (Tcons tint Tnil)))) tint
              cc_default)) ::
    Member_plain __close
      (tptr (Tfunction
              (Tcons (tptr (Tstruct __reent noattr))
                (Tcons (tptr tvoid) Tnil)) tint cc_default)) ::
    Member_plain __ub (Tstruct ___sbuf noattr) ::
    Member_plain __up (tptr tuchar) :: Member_plain __ur tint ::
    Member_plain __ubuf (tarray tuchar 3) ::
    Member_plain __nbuf (tarray tuchar 1) ::
    Member_plain __lb (Tstruct ___sbuf noattr) ::
    Member_plain __blksize tint :: Member_plain __flags2 tint ::
    Member_plain __offset tlong ::
    Member_plain __seek64
      (tptr (Tfunction
              (Tcons (tptr (Tstruct __reent noattr))
                (Tcons (tptr tvoid) (Tcons tlong (Tcons tint Tnil)))) tlong
              cc_default)) :: Member_plain __lock (tptr tvoid) ::
    Member_plain __mbstate (Tstruct __139 noattr) :: nil)
   noattr ::
 Composite __glue Struct
   (Member_plain __next (tptr (Tstruct __glue noattr)) ::
    Member_plain __niobs tint ::
    Member_plain __iobs (tptr (Tstruct ___sFILE64 noattr)) :: nil)
   noattr ::
 Composite __rand48 Struct
   (Member_plain __seed (tarray tushort 3) ::
    Member_plain __mult (tarray tushort 3) :: Member_plain __add tushort ::
    nil)
   noattr ::
 Composite __214 Struct
   (Member_plain __unused_rand tuint ::
    Member_plain __strtok_last (tptr tschar) ::
    Member_plain __asctime_buf (tarray tschar 26) ::
    Member_plain __localtime_buf (Tstruct ___tm noattr) ::
    Member_plain __gamma_signgam tint :: Member_plain __rand_next tulong ::
    Member_plain __r48 (Tstruct __rand48 noattr) ::
    Member_plain __mblen_state (Tstruct __139 noattr) ::
    Member_plain __mbtowc_state (Tstruct __139 noattr) ::
    Member_plain __wctomb_state (Tstruct __139 noattr) ::
    Member_plain __l64a_buf (tarray tschar 8) ::
    Member_plain __signal_buf (tarray tschar 24) ::
    Member_plain __getdate_err tint ::
    Member_plain __mbrlen_state (Tstruct __139 noattr) ::
    Member_plain __mbrtowc_state (Tstruct __139 noattr) ::
    Member_plain __mbsrtowcs_state (Tstruct __139 noattr) ::
    Member_plain __wcrtomb_state (Tstruct __139 noattr) ::
    Member_plain __wcsrtombs_state (Tstruct __139 noattr) ::
    Member_plain __h_errno tint :: nil)
   noattr ::
 Composite __215 Struct
   (Member_plain __nextf (tarray (tptr tuchar) 30) ::
    Member_plain __nmalloc (tarray tuint 30) :: nil)
   noattr ::
 Composite __213 Union
   (Member_plain __reent (Tstruct __214 noattr) ::
    Member_plain __unused (Tstruct __215 noattr) :: nil)
   noattr ::
 Composite __reent Struct
   (Member_plain __errno tint ::
    Member_plain __stdin (tptr (Tstruct ___sFILE64 noattr)) ::
    Member_plain __stdout (tptr (Tstruct ___sFILE64 noattr)) ::
    Member_plain __stderr (tptr (Tstruct ___sFILE64 noattr)) ::
    Member_plain __inc tint :: Member_plain __emergency (tarray tschar 25) ::
    Member_plain __unspecified_locale_info tint ::
    Member_plain __locale (tptr (Tstruct ___locale_t noattr)) ::
    Member_plain ___sdidinit tint ::
    Member_plain ___cleanup
      (tptr (Tfunction (Tcons (tptr (Tstruct __reent noattr)) Tnil) tvoid
              cc_default)) ::
    Member_plain __result (tptr (Tstruct __Bigint noattr)) ::
    Member_plain __result_k tint ::
    Member_plain __p5s (tptr (Tstruct __Bigint noattr)) ::
    Member_plain __freelist (tptr (tptr (Tstruct __Bigint noattr))) ::
    Member_plain __cvtlen tint :: Member_plain __cvtbuf (tptr tschar) ::
    Member_plain __new (Tunion __213 noattr) ::
    Member_plain __atexit (tptr (Tstruct __atexit noattr)) ::
    Member_plain __atexit0 (Tstruct __atexit noattr) ::
    Member_plain __sig_func
      (tptr (tptr (Tfunction (Tcons tint Tnil) tvoid cc_default))) ::
    Member_plain ___sglue (Tstruct __glue noattr) ::
    Member_plain ___sf (tarray (Tstruct ___sFILE64 noattr) 3) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) :: (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons tint (Tcons tint Tnil)) tint
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___getreent,
   Gfun(External (EF_external "__getreent"
                   (mksignature nil AST.Tint cc_default)) Tnil
     (tptr (Tstruct __reent noattr)) cc_default)) ::
 (_fprintf,
   Gfun(External (EF_external "fprintf"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr (Tstruct ___sFILE64 noattr)) (Tcons (tptr tschar) Tnil))
     tint {|cc_vararg:=(Some 2); cc_unproto:=false; cc_structret:=false|})) ::
 (_printf,
   Gfun(External (EF_external "printf"
                   (mksignature (AST.Tint :: nil) AST.Tint
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tint
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _printf :: _fprintf :: ___getreent :: ___builtin_debug ::
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
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


