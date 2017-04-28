
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition _CAS_SC : ident := 74%positive.
Definition ___builtin_annot : ident := 8%positive.
Definition ___builtin_annot_intval : ident := 9%positive.
Definition ___builtin_bswap : ident := 32%positive.
Definition ___builtin_bswap16 : ident := 34%positive.
Definition ___builtin_bswap32 : ident := 33%positive.
Definition ___builtin_clz : ident := 35%positive.
Definition ___builtin_clzl : ident := 36%positive.
Definition ___builtin_clzll : ident := 37%positive.
Definition ___builtin_ctz : ident := 38%positive.
Definition ___builtin_ctzl : ident := 39%positive.
Definition ___builtin_ctzll : ident := 40%positive.
Definition ___builtin_debug : ident := 53%positive.
Definition ___builtin_fabs : ident := 6%positive.
Definition ___builtin_fmadd : ident := 44%positive.
Definition ___builtin_fmax : ident := 42%positive.
Definition ___builtin_fmin : ident := 43%positive.
Definition ___builtin_fmsub : ident := 45%positive.
Definition ___builtin_fnmadd : ident := 46%positive.
Definition ___builtin_fnmsub : ident := 47%positive.
Definition ___builtin_fsqrt : ident := 41%positive.
Definition ___builtin_membar : ident := 10%positive.
Definition ___builtin_memcpy_aligned : ident := 7%positive.
Definition ___builtin_nop : ident := 52%positive.
Definition ___builtin_read16_reversed : ident := 48%positive.
Definition ___builtin_read32_reversed : ident := 49%positive.
Definition ___builtin_va_arg : ident := 12%positive.
Definition ___builtin_va_copy : ident := 13%positive.
Definition ___builtin_va_end : ident := 14%positive.
Definition ___builtin_va_start : ident := 11%positive.
Definition ___builtin_write16_reversed : ident := 50%positive.
Definition ___builtin_write32_reversed : ident := 51%positive.
Definition ___compcert_va_composite : ident := 18%positive.
Definition ___compcert_va_float64 : ident := 17%positive.
Definition ___compcert_va_int32 : ident := 15%positive.
Definition ___compcert_va_int64 : ident := 16%positive.
Definition ___i64_dtos : ident := 19%positive.
Definition ___i64_dtou : ident := 20%positive.
Definition ___i64_sar : ident := 31%positive.
Definition ___i64_sdiv : ident := 25%positive.
Definition ___i64_shl : ident := 29%positive.
Definition ___i64_shr : ident := 30%positive.
Definition ___i64_smod : ident := 27%positive.
Definition ___i64_stod : ident := 21%positive.
Definition ___i64_stof : ident := 23%positive.
Definition ___i64_udiv : ident := 26%positive.
Definition ___i64_umod : ident := 28%positive.
Definition ___i64_utod : ident := 22%positive.
Definition ___i64_utof : ident := 24%positive.
Definition _a : ident := 1%positive.
Definition _acquire : ident := 59%positive.
Definition _add : ident := 97%positive.
Definition _atomic_loc : ident := 5%positive.
Definition _c : ident := 72%positive.
Definition _curr : ident := 87%positive.
Definition _del_node : ident := 85%positive.
Definition _e : ident := 82%positive.
Definition _exit : ident := 54%positive.
Definition _first : ident := 78%positive.
Definition _free : ident := 55%positive.
Definition _free_atomic : ident := 68%positive.
Definition _freelock : ident := 58%positive.
Definition _head : ident := 81%positive.
Definition _l : ident := 65%positive.
Definition _l1 : ident := 90%positive.
Definition _l2 : ident := 91%positive.
Definition _load_SC : ident := 70%positive.
Definition _locate : ident := 92%positive.
Definition _lock : ident := 4%positive.
Definition _lock_t : ident := 2%positive.
Definition _main : ident := 75%positive.
Definition _make_atomic : ident := 66%positive.
Definition _makelock : ident := 57%positive.
Definition _malloc : ident := 56%positive.
Definition _n : ident := 61%positive.
Definition _n1 : ident := 93%positive.
Definition _n2 : ident := 96%positive.
Definition _n3 : ident := 94%positive.
Definition _new_node : ident := 84%positive.
Definition _next : ident := 76%positive.
Definition _nnext : ident := 83%positive.
Definition _node : ident := 77%positive.
Definition _node_pair : ident := 80%positive.
Definition _p : ident := 62%positive.
Definition _pred : ident := 86%positive.
Definition _r : ident := 73%positive.
Definition _release : ident := 60%positive.
Definition _remove : ident := 98%positive.
Definition _result : ident := 95%positive.
Definition _second : ident := 79%positive.
Definition _store_SC : ident := 71%positive.
Definition _succ : ident := 88%positive.
Definition _surely_malloc : ident := 63%positive.
Definition _tgt : ident := 67%positive.
Definition _v : ident := 64%positive.
Definition _val : ident := 3%positive.
Definition _validate : ident := 89%positive.
Definition _x : ident := 69%positive.
Definition _t'1 : ident := 99%positive.
Definition _t'2 : ident := 100%positive.
Definition _t'3 : ident := 101%positive.
Definition _t'4 : ident := 102%positive.

Definition v_head := {|
  gvar_info := (tptr (Tstruct _node noattr));
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_new_node := {|
  fn_return := (tptr (Tstruct _node noattr));
  fn_callconv := cc_default;
  fn_params := ((_e, tint) :: (_nnext, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, (tptr (Tstruct _node noattr))) ::
               (_l, (tptr (Tstruct _lock_t noattr))) ::
               (_n, (tptr (Tstruct _atomic_loc noattr))) ::
               (_t'3, (tptr (Tstruct _atomic_loc noattr))) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                             cc_default))
      ((Esizeof (Tstruct _node noattr) tuint) :: nil))
    (Sset _r (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _r (tptr (Tstruct _node noattr)))
          (Tstruct _node noattr)) _val tint) (Etempvar _e tint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _surely_malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid)
                                 cc_default))
          ((Esizeof (Tstruct _lock_t noattr) tuint) :: nil))
        (Sset _l (Etempvar _t'2 (tptr tvoid))))
      (Ssequence
        (Scall None
          (Evar _makelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
          ((Etempvar _l (tptr (Tstruct _lock_t noattr))) :: nil))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _r (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _lock
              (tptr (Tstruct _lock_t noattr)))
            (Etempvar _l (tptr (Tstruct _lock_t noattr))))
          (Ssequence
            (Scall None
              (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                               cc_default))
              ((Etempvar _l (tptr (Tstruct _lock_t noattr))) :: nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _make_atomic (Tfunction (Tcons (tptr tvoid) Tnil)
                                       (tptr (Tstruct _atomic_loc noattr))
                                       cc_default))
                  ((Etempvar _nnext (tptr (Tstruct _node noattr))) :: nil))
                (Sset _n (Etempvar _t'3 (tptr (Tstruct _atomic_loc noattr)))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _r (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _next
                    (tptr (Tstruct _atomic_loc noattr)))
                  (Etempvar _n (tptr (Tstruct _atomic_loc noattr))))
                (Sreturn (Some (Etempvar _r (tptr (Tstruct _node noattr)))))))))))))
|}.

Definition f_del_node := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_n, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _atomic_loc noattr))) ::
               (_l, (tptr (Tstruct _lock_t noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Efield
      (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
        (Tstruct _node noattr)) _next (tptr (Tstruct _atomic_loc noattr))))
  (Ssequence
    (Scall None
      (Evar _free_atomic (Tfunction
                           (Tcons (tptr (Tstruct _atomic_loc noattr)) Tnil)
                           (tptr tvoid) cc_default))
      ((Etempvar _p (tptr (Tstruct _atomic_loc noattr))) :: nil))
    (Ssequence
      (Sset _l
        (Efield
          (Ederef (Etempvar _n (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _lock (tptr (Tstruct _lock_t noattr))))
      (Ssequence
        (Scall None
          (Evar _freelock (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                            cc_default))
          ((Etempvar _l (tptr (Tstruct _lock_t noattr))) :: nil))
        (Ssequence
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
            ((Etempvar _l (tptr (Tstruct _lock_t noattr))) :: nil))
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
            ((Etempvar _n (tptr (Tstruct _node noattr))) :: nil)))))))
|}.

Definition f_validate := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_e, tint) :: (_pred, (tptr (Tstruct _node noattr))) ::
                (_curr, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_succ, (tptr (Tstruct _node noattr))) :: (_v, tint) ::
               (_n, (tptr (Tstruct _atomic_loc noattr))) ::
               (_p, (tptr (Tstruct _node noattr))) :: (_r, tint) ::
               (_t'3, tint) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _succ (Evar _head (tptr (Tstruct _node noattr))))
  (Ssequence
    (Sset _v
      (Efield
        (Ederef (Etempvar _succ (tptr (Tstruct _node noattr)))
          (Tstruct _node noattr)) _val tint))
    (Ssequence
      (Swhile
        (Ebinop Olt (Etempvar _v tint) (Etempvar _e tint) tint)
        (Ssequence
          (Sset _n
            (Efield
              (Ederef (Etempvar _succ (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _next
              (tptr (Tstruct _atomic_loc noattr))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _load_SC (Tfunction
                                 (Tcons (tptr (Tstruct _atomic_loc noattr))
                                   Tnil) (tptr tvoid) cc_default))
                ((Etempvar _n (tptr (Tstruct _atomic_loc noattr))) :: nil))
              (Sset _succ
                (Ecast (Etempvar _t'1 (tptr tvoid))
                  (tptr (Tstruct _node noattr)))))
            (Sset _v
              (Efield
                (Ederef (Etempvar _succ (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _val tint)))))
      (Ssequence
        (Sset _n
          (Efield
            (Ederef (Etempvar _pred (tptr (Tstruct _node noattr)))
              (Tstruct _node noattr)) _next
            (tptr (Tstruct _atomic_loc noattr))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _load_SC (Tfunction
                               (Tcons (tptr (Tstruct _atomic_loc noattr))
                                 Tnil) (tptr tvoid) cc_default))
              ((Etempvar _n (tptr (Tstruct _atomic_loc noattr))) :: nil))
            (Sset _p (Etempvar _t'2 (tptr tvoid))))
          (Ssequence
            (Sset _r
              (Ebinop Oeq (Etempvar _succ (tptr (Tstruct _node noattr)))
                (Etempvar _curr (tptr (Tstruct _node noattr))) tint))
            (Ssequence
              (Ssequence
                (Sifthenelse (Etempvar _r tint)
                  (Sset _t'3
                    (Ecast
                      (Ebinop Oeq (Etempvar _p (tptr (Tstruct _node noattr)))
                        (Etempvar _curr (tptr (Tstruct _node noattr))) tint)
                      tbool))
                  (Sset _t'3 (Econst_int (Int.repr 0) tint)))
                (Sset _r (Etempvar _t'3 tint)))
              (Sreturn (Some (Etempvar _r tint))))))))))
|}.

Definition f_locate := {|
  fn_return := (tptr (Tstruct _node_pair noattr));
  fn_callconv := cc_default;
  fn_params := ((_e, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_pred, (tptr (Tstruct _node noattr))) ::
               (_n, (tptr (Tstruct _atomic_loc noattr))) ::
               (_curr, (tptr (Tstruct _node noattr))) :: (_v, tint) ::
               (_l1, (tptr (Tstruct _lock_t noattr))) ::
               (_l2, (tptr (Tstruct _lock_t noattr))) ::
               (_r, (tptr (Tstruct _node_pair noattr))) :: (_t'4, tint) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Sset _pred (Evar _head (tptr (Tstruct _node noattr))))
      (Ssequence
        (Sset _n
          (Efield
            (Ederef (Etempvar _pred (tptr (Tstruct _node noattr)))
              (Tstruct _node noattr)) _next
            (tptr (Tstruct _atomic_loc noattr))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _load_SC (Tfunction
                               (Tcons (tptr (Tstruct _atomic_loc noattr))
                                 Tnil) (tptr tvoid) cc_default))
              ((Etempvar _n (tptr (Tstruct _atomic_loc noattr))) :: nil))
            (Sset _curr
              (Ecast (Etempvar _t'1 (tptr tvoid))
                (tptr (Tstruct _node noattr)))))
          (Ssequence
            (Sset _v
              (Efield
                (Ederef (Etempvar _curr (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _val tint))
            (Ssequence
              (Swhile
                (Ebinop Olt (Etempvar _v tint) (Etempvar _e tint) tint)
                (Ssequence
                  (Sset _pred (Etempvar _curr (tptr (Tstruct _node noattr))))
                  (Ssequence
                    (Sset _n
                      (Efield
                        (Ederef
                          (Etempvar _curr (tptr (Tstruct _node noattr)))
                          (Tstruct _node noattr)) _next
                        (tptr (Tstruct _atomic_loc noattr))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'2)
                          (Evar _load_SC (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _atomic_loc noattr))
                                             Tnil) (tptr tvoid) cc_default))
                          ((Etempvar _n (tptr (Tstruct _atomic_loc noattr))) ::
                           nil))
                        (Sset _curr
                          (Ecast (Etempvar _t'2 (tptr tvoid))
                            (tptr (Tstruct _node noattr)))))
                      (Sset _v
                        (Efield
                          (Ederef
                            (Etempvar _curr (tptr (Tstruct _node noattr)))
                            (Tstruct _node noattr)) _val tint))))))
              (Ssequence
                (Sset _l1
                  (Efield
                    (Ederef (Etempvar _pred (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _lock
                    (tptr (Tstruct _lock_t noattr))))
                (Ssequence
                  (Sset _l2
                    (Efield
                      (Ederef (Etempvar _curr (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _lock
                      (tptr (Tstruct _lock_t noattr))))
                  (Ssequence
                    (Scall None
                      (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil)
                                       tvoid cc_default))
                      ((Etempvar _l1 (tptr (Tstruct _lock_t noattr))) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _acquire (Tfunction (Tcons (tptr tvoid) Tnil)
                                         tvoid cc_default))
                        ((Etempvar _l2 (tptr (Tstruct _lock_t noattr))) ::
                         nil))
                      (Ssequence
                        (Scall (Some _t'4)
                          (Evar _validate (Tfunction
                                            (Tcons tint
                                              (Tcons
                                                (tptr (Tstruct _node noattr))
                                                (Tcons
                                                  (tptr (Tstruct _node noattr))
                                                  Tnil))) tint cc_default))
                          ((Etempvar _e tint) ::
                           (Etempvar _pred (tptr (Tstruct _node noattr))) ::
                           (Etempvar _curr (tptr (Tstruct _node noattr))) ::
                           nil))
                        (Sifthenelse (Etempvar _t'4 tint)
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'3)
                                (Evar _surely_malloc (Tfunction
                                                       (Tcons tuint Tnil)
                                                       (tptr tvoid)
                                                       cc_default))
                                ((Esizeof (Tstruct _node_pair noattr) tuint) ::
                                 nil))
                              (Sset _r (Etempvar _t'3 (tptr tvoid))))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _r (tptr (Tstruct _node_pair noattr)))
                                    (Tstruct _node_pair noattr)) _first
                                  (tptr (Tstruct _node noattr)))
                                (Etempvar _pred (tptr (Tstruct _node noattr))))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _r (tptr (Tstruct _node_pair noattr)))
                                      (Tstruct _node_pair noattr)) _second
                                    (tptr (Tstruct _node noattr)))
                                  (Etempvar _curr (tptr (Tstruct _node noattr))))
                                (Sreturn (Some (Etempvar _r (tptr (Tstruct _node_pair noattr))))))))
                          (Ssequence
                            (Scall None
                              (Evar _release (Tfunction
                                               (Tcons (tptr tvoid) Tnil)
                                               tvoid cc_default))
                              ((Etempvar _l1 (tptr (Tstruct _lock_t noattr))) ::
                               nil))
                            (Scall None
                              (Evar _release (Tfunction
                                               (Tcons (tptr tvoid) Tnil)
                                               tvoid cc_default))
                              ((Etempvar _l2 (tptr (Tstruct _lock_t noattr))) ::
                               nil)))))))))))))))
  Sskip)
|}.

Definition f_add := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_e, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, (tptr (Tstruct _node_pair noattr))) ::
               (_n1, (tptr (Tstruct _node noattr))) ::
               (_n3, (tptr (Tstruct _node noattr))) :: (_v, tint) ::
               (_result, tint) :: (_n2, (tptr (Tstruct _node noattr))) ::
               (_n, (tptr (Tstruct _atomic_loc noattr))) ::
               (_l, (tptr (Tstruct _lock_t noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node_pair noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _locate (Tfunction (Tcons tint Tnil)
                      (tptr (Tstruct _node_pair noattr)) cc_default))
      ((Etempvar _e tint) :: nil))
    (Sset _r (Etempvar _t'1 (tptr (Tstruct _node_pair noattr)))))
  (Ssequence
    (Sset _n1
      (Efield
        (Ederef (Etempvar _r (tptr (Tstruct _node_pair noattr)))
          (Tstruct _node_pair noattr)) _first (tptr (Tstruct _node noattr))))
    (Ssequence
      (Sset _n3
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _node_pair noattr)))
            (Tstruct _node_pair noattr)) _second
          (tptr (Tstruct _node noattr))))
      (Ssequence
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _r (tptr (Tstruct _node_pair noattr))) :: nil))
        (Ssequence
          (Sset _v
            (Efield
              (Ederef (Etempvar _n3 (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _val tint))
          (Ssequence
            (Sifthenelse (Ebinop One (Etempvar _v tint) (Etempvar _e tint)
                           tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar _new_node (Tfunction
                                      (Tcons tint
                                        (Tcons (tptr (Tstruct _node noattr))
                                          Tnil))
                                      (tptr (Tstruct _node noattr))
                                      cc_default))
                    ((Etempvar _e tint) ::
                     (Etempvar _n3 (tptr (Tstruct _node noattr))) :: nil))
                  (Sset _n2 (Etempvar _t'2 (tptr (Tstruct _node noattr)))))
                (Ssequence
                  (Sset _n
                    (Efield
                      (Ederef (Etempvar _n1 (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _next
                      (tptr (Tstruct _atomic_loc noattr))))
                  (Ssequence
                    (Scall None
                      (Evar _store_SC (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _atomic_loc noattr))
                                          (Tcons (tptr tvoid) Tnil)) tvoid
                                        cc_default))
                      ((Etempvar _n (tptr (Tstruct _atomic_loc noattr))) ::
                       (Etempvar _n2 (tptr (Tstruct _node noattr))) :: nil))
                    (Sset _result (Econst_int (Int.repr 1) tint)))))
              (Sset _result (Econst_int (Int.repr 0) tint)))
            (Ssequence
              (Sset _l
                (Efield
                  (Ederef (Etempvar _n1 (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _lock
                  (tptr (Tstruct _lock_t noattr))))
              (Ssequence
                (Scall None
                  (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                   cc_default))
                  ((Etempvar _l (tptr (Tstruct _lock_t noattr))) :: nil))
                (Ssequence
                  (Sset _l
                    (Efield
                      (Ederef (Etempvar _n3 (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _lock
                      (tptr (Tstruct _lock_t noattr))))
                  (Ssequence
                    (Scall None
                      (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil)
                                       tvoid cc_default))
                      ((Etempvar _l (tptr (Tstruct _lock_t noattr))) :: nil))
                    (Sreturn (Some (Etempvar _result tint)))))))))))))
|}.

Definition f_remove := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_e, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, (tptr (Tstruct _node_pair noattr))) ::
               (_n1, (tptr (Tstruct _node noattr))) ::
               (_n2, (tptr (Tstruct _node noattr))) :: (_v, tint) ::
               (_result, tint) ::
               (_n, (tptr (Tstruct _atomic_loc noattr))) ::
               (_n3, (tptr (Tstruct _node noattr))) ::
               (_l, (tptr (Tstruct _lock_t noattr))) ::
               (_t'2, (tptr tvoid)) ::
               (_t'1, (tptr (Tstruct _node_pair noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _locate (Tfunction (Tcons tint Tnil)
                      (tptr (Tstruct _node_pair noattr)) cc_default))
      ((Etempvar _e tint) :: nil))
    (Sset _r (Etempvar _t'1 (tptr (Tstruct _node_pair noattr)))))
  (Ssequence
    (Sset _n1
      (Efield
        (Ederef (Etempvar _r (tptr (Tstruct _node_pair noattr)))
          (Tstruct _node_pair noattr)) _first (tptr (Tstruct _node noattr))))
    (Ssequence
      (Sset _n2
        (Efield
          (Ederef (Etempvar _r (tptr (Tstruct _node_pair noattr)))
            (Tstruct _node_pair noattr)) _second
          (tptr (Tstruct _node noattr))))
      (Ssequence
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Etempvar _r (tptr (Tstruct _node_pair noattr))) :: nil))
        (Ssequence
          (Sset _v
            (Efield
              (Ederef (Etempvar _n2 (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _val tint))
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _v tint) (Etempvar _e tint)
                           tint)
              (Ssequence
                (Sset _n
                  (Efield
                    (Ederef (Etempvar _n2 (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _next
                    (tptr (Tstruct _atomic_loc noattr))))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'2)
                      (Evar _load_SC (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _atomic_loc noattr))
                                         Tnil) (tptr tvoid) cc_default))
                      ((Etempvar _n (tptr (Tstruct _atomic_loc noattr))) ::
                       nil))
                    (Sset _n3 (Etempvar _t'2 (tptr tvoid))))
                  (Ssequence
                    (Sset _n
                      (Efield
                        (Ederef (Etempvar _n1 (tptr (Tstruct _node noattr)))
                          (Tstruct _node noattr)) _next
                        (tptr (Tstruct _atomic_loc noattr))))
                    (Ssequence
                      (Scall None
                        (Evar _store_SC (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _atomic_loc noattr))
                                            (Tcons (tptr tvoid) Tnil)) tvoid
                                          cc_default))
                        ((Etempvar _n (tptr (Tstruct _atomic_loc noattr))) ::
                         (Etempvar _n3 (tptr (Tstruct _node noattr))) :: nil))
                      (Sset _result (Econst_int (Int.repr 1) tint))))))
              (Sset _result (Econst_int (Int.repr 0) tint)))
            (Ssequence
              (Sset _l
                (Efield
                  (Ederef (Etempvar _n1 (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _lock
                  (tptr (Tstruct _lock_t noattr))))
              (Ssequence
                (Scall None
                  (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                   cc_default))
                  ((Etempvar _l (tptr (Tstruct _lock_t noattr))) :: nil))
                (Ssequence
                  (Sset _l
                    (Efield
                      (Ederef (Etempvar _n2 (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _lock
                      (tptr (Tstruct _lock_t noattr))))
                  (Ssequence
                    (Scall None
                      (Evar _release (Tfunction (Tcons (tptr tvoid) Tnil)
                                       tvoid cc_default))
                      ((Etempvar _l (tptr (Tstruct _lock_t noattr))) :: nil))
                    (Sreturn (Some (Etempvar _result tint)))))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _lock_t Struct ((_a, (tarray (tptr tvoid) 2)) :: nil) noattr ::
 Composite _node Struct
   ((_val, tint) :: (_next, (tptr (Tstruct _atomic_loc noattr))) ::
    (_lock, (tptr (Tstruct _lock_t noattr))) :: nil)
   noattr ::
 Composite _node_pair Struct
   ((_first, (tptr (Tstruct _node noattr))) ::
    (_second, (tptr (Tstruct _node noattr))) :: nil)
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
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_makelock,
   Gfun(External (EF_external "makelock"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_freelock,
   Gfun(External (EF_external "freelock"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_acquire,
   Gfun(External (EF_external "acquire"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_release,
   Gfun(External (EF_external "release"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_surely_malloc,
   Gfun(External (EF_external "surely_malloc"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_make_atomic,
   Gfun(External (EF_external "make_atomic"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) (tptr (Tstruct _atomic_loc noattr))
     cc_default)) ::
 (_free_atomic,
   Gfun(External (EF_external "free_atomic"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _atomic_loc noattr)) Tnil) (tptr tvoid)
     cc_default)) ::
 (_load_SC,
   Gfun(External (EF_external "load_SC"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _atomic_loc noattr)) Tnil) (tptr tvoid)
     cc_default)) ::
 (_store_SC,
   Gfun(External (EF_external "store_SC"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr (Tstruct _atomic_loc noattr)) (Tcons (tptr tvoid) Tnil))
     tvoid cc_default)) :: (_head, Gvar v_head) ::
 (_new_node, Gfun(Internal f_new_node)) ::
 (_del_node, Gfun(Internal f_del_node)) ::
 (_validate, Gfun(Internal f_validate)) ::
 (_locate, Gfun(Internal f_locate)) :: (_add, Gfun(Internal f_add)) ::
 (_remove, Gfun(Internal f_remove)) :: nil);
prog_public :=
(_remove :: _add :: _locate :: _validate :: _del_node :: _new_node ::
 _head :: _store_SC :: _load_SC :: _free_atomic :: _make_atomic ::
 _surely_malloc :: _release :: _acquire :: _freelock :: _makelock :: _free ::
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

