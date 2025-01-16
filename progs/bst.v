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
  Definition model := "32sse2".
  Definition abi := "standard".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "progs/bst.c".
  Definition normalized := true.
End Info.

Definition ___builtin_ais_annot : ident := 6%positive.
Definition ___builtin_annot : ident := 23%positive.
Definition ___builtin_annot_intval : ident := 24%positive.
Definition ___builtin_bswap : ident := 8%positive.
Definition ___builtin_bswap16 : ident := 10%positive.
Definition ___builtin_bswap32 : ident := 9%positive.
Definition ___builtin_bswap64 : ident := 7%positive.
Definition ___builtin_clz : ident := 11%positive.
Definition ___builtin_clzl : ident := 12%positive.
Definition ___builtin_clzll : ident := 13%positive.
Definition ___builtin_ctz : ident := 14%positive.
Definition ___builtin_ctzl : ident := 15%positive.
Definition ___builtin_ctzll : ident := 16%positive.
Definition ___builtin_debug : ident := 42%positive.
Definition ___builtin_expect : ident := 31%positive.
Definition ___builtin_fabs : ident := 17%positive.
Definition ___builtin_fabsf : ident := 18%positive.
Definition ___builtin_fmadd : ident := 34%positive.
Definition ___builtin_fmax : ident := 32%positive.
Definition ___builtin_fmin : ident := 33%positive.
Definition ___builtin_fmsub : ident := 35%positive.
Definition ___builtin_fnmadd : ident := 36%positive.
Definition ___builtin_fnmsub : ident := 37%positive.
Definition ___builtin_fsqrt : ident := 19%positive.
Definition ___builtin_membar : ident := 25%positive.
Definition ___builtin_memcpy_aligned : ident := 21%positive.
Definition ___builtin_read16_reversed : ident := 38%positive.
Definition ___builtin_read32_reversed : ident := 39%positive.
Definition ___builtin_sel : ident := 22%positive.
Definition ___builtin_sqrt : ident := 20%positive.
Definition ___builtin_unreachable : ident := 30%positive.
Definition ___builtin_va_arg : ident := 27%positive.
Definition ___builtin_va_copy : ident := 28%positive.
Definition ___builtin_va_end : ident := 29%positive.
Definition ___builtin_va_start : ident := 26%positive.
Definition ___builtin_write16_reversed : ident := 40%positive.
Definition ___builtin_write32_reversed : ident := 41%positive.
Definition ___compcert_i64_dtos : ident := 75%positive.
Definition ___compcert_i64_dtou : ident := 76%positive.
Definition ___compcert_i64_sar : ident := 87%positive.
Definition ___compcert_i64_sdiv : ident := 81%positive.
Definition ___compcert_i64_shl : ident := 85%positive.
Definition ___compcert_i64_shr : ident := 86%positive.
Definition ___compcert_i64_smod : ident := 83%positive.
Definition ___compcert_i64_smulh : ident := 88%positive.
Definition ___compcert_i64_stod : ident := 77%positive.
Definition ___compcert_i64_stof : ident := 79%positive.
Definition ___compcert_i64_udiv : ident := 82%positive.
Definition ___compcert_i64_umod : ident := 84%positive.
Definition ___compcert_i64_umulh : ident := 89%positive.
Definition ___compcert_i64_utod : ident := 78%positive.
Definition ___compcert_i64_utof : ident := 80%positive.
Definition ___compcert_va_composite : ident := 74%positive.
Definition ___compcert_va_float64 : ident := 73%positive.
Definition ___compcert_va_int32 : ident := 71%positive.
Definition ___compcert_va_int64 : ident := 72%positive.
Definition ___stringlit_1 : ident := 66%positive.
Definition ___stringlit_2 : ident := 67%positive.
Definition ___stringlit_3 : ident := 68%positive.
Definition ___stringlit_4 : ident := 69%positive.
Definition __l : ident := 56%positive.
Definition _b : ident := 50%positive.
Definition _delete : ident := 63%positive.
Definition _freeN : ident := 44%positive.
Definition _insert : ident := 55%positive.
Definition _key : ident := 2%positive.
Definition _l : ident := 57%positive.
Definition _left : ident := 4%positive.
Definition _lookup : ident := 65%positive.
Definition _main : ident := 70%positive.
Definition _mallocN : ident := 43%positive.
Definition _mid : ident := 59%positive.
Definition _p : ident := 45%positive.
Definition _pa : ident := 47%positive.
Definition _pb : ident := 48%positive.
Definition _pushdown_left : ident := 62%positive.
Definition _q : ident := 61%positive.
Definition _r : ident := 58%positive.
Definition _right : ident := 5%positive.
Definition _t : ident := 51%positive.
Definition _tree : ident := 1%positive.
Definition _tree_free : ident := 49%positive.
Definition _treebox_free : ident := 52%positive.
Definition _treebox_new : ident := 46%positive.
Definition _turn_left : ident := 60%positive.
Definition _v : ident := 64%positive.
Definition _value : ident := 3%positive.
Definition _x : ident := 53%positive.
Definition _y : ident := 54%positive.
Definition _t'1 : ident := 90%positive.

Definition v___stringlit_3 := {|
  gvar_info := (tarray tschar 5);
  gvar_init := (Init_int8 (Int.repr 102) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 117) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 6);
  gvar_init := (Init_int8 (Int.repr 116) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_4 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 79) :: Init_int8 (Int.repr 78) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v___stringlit_2 := {|
  gvar_info := (tarray tschar 4);
  gvar_init := (Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_treebox_new := {|
  fn_return := (tptr (tptr (Tstruct _tree noattr)));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr (tptr (Tstruct _tree noattr)))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _mallocN (Tfunction (tint :: nil) (tptr tvoid) cc_default))
      ((Esizeof (tptr (Tstruct _tree noattr)) tuint) :: nil))
    (Sset _p
      (Ecast (Etempvar _t'1 (tptr tvoid))
        (tptr (tptr (Tstruct _tree noattr))))))
  (Ssequence
    (Sassign
      (Ederef (Etempvar _p (tptr (tptr (Tstruct _tree noattr))))
        (tptr (Tstruct _tree noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Sreturn (Some (Etempvar _p (tptr (tptr (Tstruct _tree noattr))))))))
|}.

Definition f_tree_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_pa, (tptr (Tstruct _tree noattr))) ::
               (_pb, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Sifthenelse (Ebinop One (Etempvar _p (tptr (Tstruct _tree noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Ssequence
    (Sset _pa
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
    (Ssequence
      (Sset _pb
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Scall None
          (Evar _freeN (Tfunction ((tptr tvoid) :: tint :: nil) tvoid
                         cc_default))
          ((Etempvar _p (tptr (Tstruct _tree noattr))) ::
           (Esizeof (Tstruct _tree noattr) tuint) :: nil))
        (Ssequence
          (Scall None
            (Evar _tree_free (Tfunction
                               ((tptr (Tstruct _tree noattr)) :: nil) tvoid
                               cc_default))
            ((Etempvar _pa (tptr (Tstruct _tree noattr))) :: nil))
          (Scall None
            (Evar _tree_free (Tfunction
                               ((tptr (Tstruct _tree noattr)) :: nil) tvoid
                               cc_default))
            ((Etempvar _pb (tptr (Tstruct _tree noattr))) :: nil))))))
  Sskip)
|}.

Definition f_treebox_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_b, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t
    (Ederef (Etempvar _b (tptr (tptr (Tstruct _tree noattr))))
      (tptr (Tstruct _tree noattr))))
  (Ssequence
    (Scall None
      (Evar _tree_free (Tfunction ((tptr (Tstruct _tree noattr)) :: nil)
                         tvoid cc_default))
      ((Etempvar _t (tptr (Tstruct _tree noattr))) :: nil))
    (Scall None
      (Evar _freeN (Tfunction ((tptr tvoid) :: tint :: nil) tvoid cc_default))
      ((Etempvar _b (tptr (tptr (Tstruct _tree noattr)))) ::
       (Esizeof (tptr (Tstruct _tree noattr)) tuint) :: nil))))
|}.

Definition f_insert := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree noattr)))) :: (_x, tint) ::
                (_value, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) :: (_y, tint) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Sset _p
        (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
          (tptr (Tstruct _tree noattr))))
      (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _tree noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _mallocN (Tfunction (tint :: nil) (tptr tvoid)
                               cc_default))
              ((Esizeof (Tstruct _tree noattr) tuint) :: nil))
            (Sset _p
              (Ecast (Etempvar _t'1 (tptr tvoid))
                (tptr (Tstruct _tree noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _key tint) (Etempvar _x tint))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _value (tptr tvoid))
                (Etempvar _value (tptr tvoid)))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _left
                    (tptr (Tstruct _tree noattr)))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                        (Tstruct _tree noattr)) _right
                      (tptr (Tstruct _tree noattr)))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
                        (tptr (Tstruct _tree noattr)))
                      (Etempvar _p (tptr (Tstruct _tree noattr))))
                    (Sreturn None)))))))
        (Ssequence
          (Sset _y
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _key tint))
          (Sifthenelse (Ebinop Olt (Etempvar _x tint) (Etempvar _y tint)
                         tint)
            (Sset _t
              (Eaddrof
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _left
                  (tptr (Tstruct _tree noattr)))
                (tptr (tptr (Tstruct _tree noattr)))))
            (Sifthenelse (Ebinop Olt (Etempvar _y tint) (Etempvar _x tint)
                           tint)
              (Sset _t
                (Eaddrof
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _right
                    (tptr (Tstruct _tree noattr)))
                  (tptr (tptr (Tstruct _tree noattr)))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _value (tptr tvoid))
                  (Etempvar _value (tptr tvoid)))
                (Sreturn None))))))))
  Sskip)
|}.

Definition f_turn_left := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((__l, (tptr (tptr (Tstruct _tree noattr)))) ::
                (_l, (tptr (Tstruct _tree noattr))) ::
                (_r, (tptr (Tstruct _tree noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_mid, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _mid
    (Efield
      (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
        (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _tree noattr)))
          (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr)))
      (Etempvar _mid (tptr (Tstruct _tree noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _tree noattr)))
            (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr)))
        (Etempvar _l (tptr (Tstruct _tree noattr))))
      (Sassign
        (Ederef (Etempvar __l (tptr (tptr (Tstruct _tree noattr))))
          (tptr (Tstruct _tree noattr)))
        (Etempvar _r (tptr (Tstruct _tree noattr)))))))
|}.

Definition f_pushdown_left := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) ::
               (_q, (tptr (Tstruct _tree noattr))) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Sset _p
        (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
          (tptr (Tstruct _tree noattr))))
      (Ssequence
        (Sset _q
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _right (tptr (Tstruct _tree noattr))))
        (Sifthenelse (Ebinop Oeq (Etempvar _q (tptr (Tstruct _tree noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Ssequence
            (Sset _q
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _left
                (tptr (Tstruct _tree noattr))))
            (Ssequence
              (Sassign
                (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
                  (tptr (Tstruct _tree noattr)))
                (Etempvar _q (tptr (Tstruct _tree noattr))))
              (Ssequence
                (Scall None
                  (Evar _freeN (Tfunction ((tptr tvoid) :: tint :: nil) tvoid
                                 cc_default))
                  ((Etempvar _p (tptr (Tstruct _tree noattr))) ::
                   (Esizeof (Tstruct _tree noattr) tuint) :: nil))
                (Sreturn None))))
          (Ssequence
            (Scall None
              (Evar _turn_left (Tfunction
                                 ((tptr (tptr (Tstruct _tree noattr))) ::
                                  (tptr (Tstruct _tree noattr)) ::
                                  (tptr (Tstruct _tree noattr)) :: nil) tvoid
                                 cc_default))
              ((Etempvar _t (tptr (tptr (Tstruct _tree noattr)))) ::
               (Etempvar _p (tptr (Tstruct _tree noattr))) ::
               (Etempvar _q (tptr (Tstruct _tree noattr))) :: nil))
            (Sset _t
              (Eaddrof
                (Efield
                  (Ederef (Etempvar _q (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _left
                  (tptr (Tstruct _tree noattr)))
                (tptr (tptr (Tstruct _tree noattr))))))))))
  Sskip)
|}.

Definition f_delete := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree noattr)))) :: (_x, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) :: (_y, tint) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Sset _p
        (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
          (tptr (Tstruct _tree noattr))))
      (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _tree noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn None)
        (Ssequence
          (Sset _y
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _key tint))
          (Sifthenelse (Ebinop Olt (Etempvar _x tint) (Etempvar _y tint)
                         tint)
            (Sset _t
              (Eaddrof
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _left
                  (tptr (Tstruct _tree noattr)))
                (tptr (tptr (Tstruct _tree noattr)))))
            (Sifthenelse (Ebinop Olt (Etempvar _y tint) (Etempvar _x tint)
                           tint)
              (Sset _t
                (Eaddrof
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                      (Tstruct _tree noattr)) _right
                    (tptr (Tstruct _tree noattr)))
                  (tptr (tptr (Tstruct _tree noattr)))))
              (Ssequence
                (Scall None
                  (Evar _pushdown_left (Tfunction
                                         ((tptr (tptr (Tstruct _tree noattr))) ::
                                          nil) tvoid cc_default))
                  ((Etempvar _t (tptr (tptr (Tstruct _tree noattr)))) :: nil))
                (Sreturn None))))))))
  Sskip)
|}.

Definition f_lookup := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (tptr (Tstruct _tree noattr)))) :: (_x, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _tree noattr))) :: (_v, (tptr tvoid)) ::
               (_y, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Ederef (Etempvar _t (tptr (tptr (Tstruct _tree noattr))))
      (tptr (Tstruct _tree noattr))))
  (Ssequence
    (Swhile
      (Ebinop One (Etempvar _p (tptr (Tstruct _tree noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sset _y
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
              (Tstruct _tree noattr)) _key tint))
        (Sifthenelse (Ebinop Olt (Etempvar _x tint) (Etempvar _y tint) tint)
          (Sset _p
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                (Tstruct _tree noattr)) _left (tptr (Tstruct _tree noattr))))
          (Sifthenelse (Ebinop Olt (Etempvar _y tint) (Etempvar _x tint)
                         tint)
            (Sset _p
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                  (Tstruct _tree noattr)) _right
                (tptr (Tstruct _tree noattr))))
            (Ssequence
              (Sset _v
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _tree noattr)))
                    (Tstruct _tree noattr)) _value (tptr tvoid)))
              (Sreturn (Some (Etempvar _v (tptr tvoid)))))))))
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr (tptr (Tstruct _tree noattr)))) ::
               (_t'1, (tptr (tptr (Tstruct _tree noattr)))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _treebox_new (Tfunction nil
                             (tptr (tptr (Tstruct _tree noattr))) cc_default))
        nil)
      (Sset _p (Etempvar _t'1 (tptr (tptr (Tstruct _tree noattr))))))
    (Ssequence
      (Scall None
        (Evar _insert (Tfunction
                        ((tptr (tptr (Tstruct _tree noattr))) :: tint ::
                         (tptr tvoid) :: nil) tvoid cc_default))
        ((Etempvar _p (tptr (tptr (Tstruct _tree noattr)))) ::
         (Econst_int (Int.repr 3) tint) ::
         (Evar ___stringlit_1 (tarray tschar 6)) :: nil))
      (Ssequence
        (Scall None
          (Evar _insert (Tfunction
                          ((tptr (tptr (Tstruct _tree noattr))) :: tint ::
                           (tptr tvoid) :: nil) tvoid cc_default))
          ((Etempvar _p (tptr (tptr (Tstruct _tree noattr)))) ::
           (Econst_int (Int.repr 1) tint) ::
           (Evar ___stringlit_2 (tarray tschar 4)) :: nil))
        (Ssequence
          (Scall None
            (Evar _insert (Tfunction
                            ((tptr (tptr (Tstruct _tree noattr))) :: tint ::
                             (tptr tvoid) :: nil) tvoid cc_default))
            ((Etempvar _p (tptr (tptr (Tstruct _tree noattr)))) ::
             (Econst_int (Int.repr 4) tint) ::
             (Evar ___stringlit_3 (tarray tschar 5)) :: nil))
          (Ssequence
            (Scall None
              (Evar _insert (Tfunction
                              ((tptr (tptr (Tstruct _tree noattr))) ::
                               tint :: (tptr tvoid) :: nil) tvoid cc_default))
              ((Etempvar _p (tptr (tptr (Tstruct _tree noattr)))) ::
               (Econst_int (Int.repr 1) tint) ::
               (Evar ___stringlit_4 (tarray tschar 4)) :: nil))
            (Ssequence
              (Scall None
                (Evar _treebox_free (Tfunction
                                      ((tptr (tptr (Tstruct _tree noattr))) ::
                                       nil) tvoid cc_default))
                ((Etempvar _p (tptr (tptr (Tstruct _tree noattr)))) :: nil))
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _tree Struct
   (Member_plain _key tint :: Member_plain _value (tptr tvoid) ::
    Member_plain _left (tptr (Tstruct _tree noattr)) ::
    Member_plain _right (tptr (Tstruct _tree noattr)) :: nil)
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
     cc_default)) :: (___stringlit_3, Gvar v___stringlit_3) ::
 (___stringlit_1, Gvar v___stringlit_1) ::
 (___stringlit_4, Gvar v___stringlit_4) ::
 (___stringlit_2, Gvar v___stringlit_2) ::
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
 (_mallocN,
   Gfun(External (EF_external "mallocN"
                   (mksignature (AST.Xint :: nil) AST.Xptr cc_default))
     (tint :: nil) (tptr tvoid) cc_default)) ::
 (_freeN,
   Gfun(External (EF_external "freeN"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tint :: nil) tvoid
     cc_default)) :: (_treebox_new, Gfun(Internal f_treebox_new)) ::
 (_tree_free, Gfun(Internal f_tree_free)) ::
 (_treebox_free, Gfun(Internal f_treebox_free)) ::
 (_insert, Gfun(Internal f_insert)) ::
 (_turn_left, Gfun(Internal f_turn_left)) ::
 (_pushdown_left, Gfun(Internal f_pushdown_left)) ::
 (_delete, Gfun(Internal f_delete)) :: (_lookup, Gfun(Internal f_lookup)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _lookup :: _delete :: _pushdown_left :: _turn_left :: _insert ::
 _treebox_free :: _tree_free :: _treebox_new :: _freeN :: _mallocN ::
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


