Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Local Open Scope logic.

(*Set Printing Depth 10. *)

Definition __builtin_read32_reversed_spec :=
 DECLARE ___builtin_read32_reversed
  WITH p: val, sh: share, contents: Z -> int
  PRE [ 1%positive OF tptr tuint ] 
        PROP() LOCAL (`(eq p) (eval_id 1%positive))
        SEP (`(array_at tuchar sh contents 0 4 p))
  POST [ tuint ] 
     local (`(eq (Vint (big_endian_integer contents))) retval) &&
     `(array_at tuchar sh contents 0 4 p).

(*        SEP (`(rangespec 0 4 (fun i => mapsto_ sh tuchar (add_ptr_int tuchar p i)))) *)

Definition __builtin_write32_reversed_spec :=
 DECLARE ___builtin_write32_reversed
  WITH p: val, sh: share, contents: Z -> int
  PRE [ 1%positive OF tptr tuint, 2%positive OF tuint ] 
        PROP(writable_share sh)
        LOCAL (`(eq p) (eval_id 1%positive);
                     `(eq (Vint(big_endian_integer contents))) (eval_id 2%positive))
        SEP (`(memory_block sh (Int.repr 4) p))
  POST [ tvoid ] 
     `(array_at tuchar sh contents 0 4 p).

Definition memcpy_spec :=
  DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, n: Z, contents: Z -> int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (writable_share (snd sh))
       LOCAL (`(eq p) (eval_id 1%positive); `(eq q) (eval_id 2%positive);
                    `(eq n) (`Int.unsigned (`force_int (eval_id 3%positive))))
       SEP (`(array_at tuchar (fst sh) contents 0 n q);
              `(memory_block (snd sh) (Int.repr n) p))
    POST [ tptr tvoid ]
         local (`(eq p) retval) &&
       (`(array_at tuchar (fst sh) contents 0 n q) *
        `(array_at tuchar (snd sh) contents 0 n p)).

Definition memset_spec :=
  DECLARE _memset
   WITH sh : share, p: val, n: Z, c: int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tint, 3%positive OF tuint ]
       PROP (writable_share sh)
       LOCAL (`(eq p) (eval_id 1%positive); `(eq (Vint c)) (eval_id 2%positive);
                    `(eq n) (`Int.unsigned (`force_int (eval_id 3%positive))))
       SEP (`(memory_block sh (Int.repr n) p))
    POST [ tptr tvoid ]
         local (`(eq p) retval) &&
       (`(array_at tuchar sh (fun _ => c) 0 n p)).

Goal forall c r,  typed_mapsto Tsh t_struct_SHA256state_st c r = TT.
 intros.
 simpl in r.
 simpl_typed_mapsto.
 destruct r as [r_h [r_Nl [r_Nh [r_data r_num]]]].
 simpl.
Abort.

Definition sha256state_ (a: s256abs) (c: val) : mpred :=
   EX r:s256state, 
    !!  s256_relate a r  &&  typed_mapsto Tsh t_struct_SHA256state_st c r.

Definition data_block (contents: list Z) (v: val) :=
  array_at tuchar Tsh (@ZnthV tuchar (map Int.repr contents)) 0 (Zlength contents) v.

Definition sha256_block_data_order_spec :=
  DECLARE _sha256_block_data_order
    WITH a: s256abs, b: list int, ctx : val, data: val, sh: share
   PRE [ _ctx OF tptr t_struct_SHA256state_st, _in OF tptr tvoid ]
         PROP(length b = LBLOCK) 
         LOCAL (`(eq ctx) (eval_id _ctx); `(eq data) (eval_id _in))
         SEP (`(sha256state_ a ctx); `(data_block (intlist_to_Zlist b) data);
                `(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K)) (eval_var _K256 (tarray tuint 64)))
   POST [ tvoid ]
          (`(sha256state_ (process_block_abs b a) ctx) *
          `(data_block (intlist_to_Zlist b) data) *
          `(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K)) (eval_var _K256 (tarray tuint 64))).
                
Definition SHA256_addlength_spec :=
 DECLARE _SHA256_addlength
 WITH len : nat, a: s256abs, c: val
 PRE [ _c OF tptr t_struct_SHA256state_st , _len OF tuint ]
   PROP ( ) 
   LOCAL (`(eq (Z.of_nat len)) (`Int.unsigned (`force_int (eval_id _len))); `(eq c) (eval_id _c))
   SEP(`(sha256state_ a c))
 POST [ tvoid ]
   SEP(`(sha256state_ (addlength_rel len a) c)).

Definition SHA256_Init_spec :=
  DECLARE _SHA256_Init
   WITH c : val 
   PRE [ _c OF tptr t_struct_SHA256state_st ]
         PROP () LOCAL (`(eq c) (eval_id _c))
         SEP(`(typed_mapsto_ Tsh t_struct_SHA256state_st c))
  POST [ tvoid ] 
         SEP(`(sha256state_ init_s256abs c)).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ ] P 'POST' [ tz ] Q" :=
     (mk_funspec (nil, tz) (t1*t2*t3*t4*t5*t6)
           (fun x => match x with (((((x1,x2),x3),x4),x5),x6) => P%logic end)
           (fun x => match x with (((((x1,x2),x3),x4),x5,x6)) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
              x5 at level 0, x6 at level 0, P at level 100, Q at level 100).

Notation "'WITH'  x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] P 'POST' [ tz ] Q" :=
     (mk_funspec ((cons u%formals .. (cons v%formals nil) ..), tz) (t1*t2*t3*t4*t5*t6)
           (fun x => match x with (((((x1,x2),x3),x4),x5),x6) => P%logic end)
           (fun x => match x with (((((x1,x2),x3),x4),x5),x6) => Q%logic end))
            (at level 200, x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, 
             x5 at level 0, x6 at level 0, P at level 100, Q at level 100).

Inductive update_abs: forall (msg: list Z) (a a': s256abs), Prop :=
| UA_short: forall msg hashed data
         (H: length (data++msg) < CBLOCK),
         update_abs msg 
           (S256abs hashed 0 data)
           (S256abs hashed 0 (data++msg))
| UA_long: forall (msg newblock: list Z) (b: list int) hashed data (msg': list Z) a'',
        newblock = firstn CBLOCK (data++msg) ->
        intlist_to_Zlist b = newblock ->
        newblock ++ msg' = data ++ msg ->
        update_abs msg' (S256abs (hashed++b) 0 nil)   a'' ->
        update_abs msg (S256abs hashed 0 data) a''.

Definition SHA256_Update_spec :=
  DECLARE _SHA256_Update
   WITH a: s256abs, data: list Z, c : val, d: val, sh: share, len : nat
   PRE [ _c OF tptr t_struct_SHA256state_st, _data_ OF tptr tvoid, _len OF tuint ]
         PROP ((len <= length data)%nat)
         LOCAL (`(eq c) (eval_id _c); `(eq d) (eval_id _data_); 
                                  `(eq (Z.of_nat len)) (`Int.unsigned (`force_int (eval_id _len))))
         SEP(`(sha256state_ a c); `(data_block data d))
  POST [ tvoid ] 
         EX a':_, 
          PROP (update_abs data a a') LOCAL ()
          SEP(`(sha256state_ a' c); `(data_block data d)).

Definition s256a_regs (a: s256abs) : list int :=
 match a with S256abs hashed _ _  => 
          process_msg init_registers hashed 
 end.

Definition SHA256_Final_spec :=
  DECLARE _SHA256_Final
   WITH a: s256abs, md: val, c : val,  shmd: share, sh: share
   PRE [ _md OF tptr tuchar, _c OF tptr t_struct_SHA256state_st ]
         PROP (writable_share shmd) 
         LOCAL (`(eq md) (eval_id _md); `(eq c) (eval_id _c))
         SEP(`(sha256state_ a c); `(memory_block shmd (Int.repr 32) md))
  POST [ tvoid ] 
         EX a':s256abs,
         PROP (sha_finish a a') LOCAL ()
         SEP(`(sha256state_ a' c); `(data_block (intlist_to_Zlist (s256a_regs a')) md)).

Definition SHA256_spec :=
  DECLARE _SHA256
   WITH d: val, len: Z, sh: share*share, data: list Z, md: val
   PRE [ _d OF tptr tuchar, _n OF tuint, _md OF tptr tuchar ]
         PROP (writable_share (snd sh)) 
         LOCAL (`(eq d) (eval_id _data_);
                     `(eq (Z.of_nat (length data))) (`Int.unsigned (`force_int (eval_id _n)));
                     `(eq md) (eval_id _md))
         SEP(`(data_block data d);
               `(memory_block (snd sh) (Int.repr 32) md))
  POST [ tvoid ] 
         SEP(`(data_block data d); 
               `(data_block (SHA_256 data) md)).

Definition Vprog : varspecs := (_K256, tarray tuint 64)::nil.

Definition Gprog : funspecs := 
  __builtin_read32_reversed_spec::
  __builtin_write32_reversed_spec::
  memcpy_spec:: memset_spec::
  sha256_block_data_order_spec:: SHA256_Init_spec::
  SHA256_Update_spec:: SHA256_Final_spec::
  SHA256_spec:: nil.

Fixpoint do_builtins (n: nat) (defs : list (ident * globdef fundef type)) : funspecs :=
 match n, defs with
  | S n', (id, Gfun (External (EF_builtin _ sig) argtys resty))::defs' => 
     (id, mk_funspec (iota_formals 1%positive argtys, resty) unit FF FF) 
      :: do_builtins n' defs'
  | _, _ => nil
 end.

Definition Gtot := do_builtins 3 (prog_defs prog) ++ Gprog.

Lemma sha256state__isptr:
 forall a c, sha256state_ a c = !!(isptr c) && sha256state_ a c.
Proof.
intros. unfold sha256state_. normalize. apply f_equal.
extensionality r.
rewrite <- andp_assoc.
rewrite (andp_comm (!!isptr c)).
rewrite andp_assoc.
f_equal.
simpl_typed_mapsto.
rewrite field_mapsto_isptr at 1. normalize.
Qed.

Ltac simpl_stackframe_of := 
  unfold stackframe_of, fn_vars; simpl map; unfold fold_right; rewrite sepcon_emp;
  repeat rewrite var_block_typed_mapsto_. 

Fixpoint loops (s: statement) : list statement :=
 match s with 
  | Ssequence a b => loops a ++ loops b
  | Sloop _ _ => [s]
  | Sifthenelse _ a b => loops a ++ loops b
  | _ => nil
  end.

Definition block_data_order_loop1 := 
   nth 0 (loops (fn_body f_sha256_block_data_order)) Sskip.

Definition block_data_order_loop2 := 
   nth 1 (loops (fn_body f_sha256_block_data_order)) Sskip.

Definition Delta_loop1 : tycontext :=
 initialized _i
          (initialized _h
           (initialized _g
              (initialized _f
                 (initialized _e
                    (initialized _d
                       (initialized _c
                          (initialized _b
                             (initialized _a
                                (initialized _data
     (func_tycontext f_sha256_block_data_order Vprog Gtot)))))))))).

Lemma read32_reversed_in_bytearray:
 forall {Espec: OracleKind} Delta (ofs: int) (lo hi: Z) base e sh contents i P Q, 
 PROPx P (LOCALx (tc_environ Delta :: Q) (SEP ())) |-- PROP ((lo <= Int.unsigned ofs <= hi-4 )%Z)
         LOCAL (tc_expr Delta e; `(eq (offset_val ofs base)) (eval_expr e))
         SEP () ->
 semax Delta  (PROPx P (LOCALx Q (SEP (`(array_at tuchar sh contents lo hi base)))))
        (Scall (Some i)
           (Evar ___builtin_read32_reversed
              (Tfunction (Tcons (tptr tuint) Tnil) tuint))
           [e])
        (normal_ret_assert
         (PROP () 
         (LOCALx (`(eq (Vint (big_endian_integer (fun z => contents (z+Int.unsigned ofs)%Z)))) (eval_id i)
                        :: Q)                 
         SEP (`(array_at tuchar sh contents lo hi base))))).
Admitted.

Lemma split_array_at:
  forall (i : Z) (ty : type) (sh : Share.t) (contents : Z -> reptype ty)
    (lo hi : Z) (v : val),
  (lo <= i <= hi)%Z ->
  array_at ty sh contents lo hi v =
  array_at ty sh contents lo i v * array_at ty sh contents i hi v.
Admitted.

Arguments Int.unsigned n : simpl never. (*  remove this once recompiled forward.v *)

Lemma semax_store_initialize_array:
forall Espec (Delta: tycontext) n sh t1 (contents: Z -> reptype t1)
              (lo hi: Z)
              (v1: environ-> val) inject P Q R            
             e1  e2 (v2: Z) (v: reptype t1),
    writable_share sh ->
    typeof e1 =  tptr t1 ->
    type_is_volatile t1 = false ->
    repinject t1 = Some inject ->
    nth_error R n = Some (`(arrayof_' (mapsto_ Tsh t1) t1 v2 (Z.to_nat (hi-v2))) v1) ->
    PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
          local (`eq (`(eval_binop Oadd (tptr t1) tint) v1 `(Vint (Int.repr v2))) (eval_expr e1))
          && !! (in_range lo hi v2)
          && local (tc_expr Delta e1) && local (tc_expr Delta (Ecast e2 t1))
          && local (`(eq (inject v)) (eval_expr (Ecast e2 t1))) ->
    @semax Espec Delta 
       (|> PROPx P (LOCALx Q (SEPx R)))
       (Sassign (Ederef e1 t1) e2) 
       (normal_ret_assert
          (PROPx P (LOCALx Q
              (SEPx (replace_nth n R
                    (`(array_at t1 sh (upd contents v2 v) lo (lo+1)) v1 *
                     `(arrayof_' (mapsto_ Tsh t1) t1 (v2+1) (Z.to_nat (hi-(v2+1)))) v1)))))).
Admitted.

Lemma numbd_lift0:
  forall n f,
   numbd n (@liftx (LiftEnviron mpred) f) = 
   (@liftx (LiftEnviron mpred)) (numbd n f).
Proof. reflexivity. Qed.

Definition rearrange_regs :=
(Ssequence
     (Sset _T1
        (Ebinop Oadd
           (Ebinop Oadd
              (Ebinop Oadd
                 (Ebinop Oadd (Etempvar _l tuint) (Etempvar _h tuint) tuint)
                 (Ebinop Oxor
                    (Ebinop Oxor
                       (Ebinop Oor
                          (Ebinop Oshl (Etempvar _e tuint)
                             (Econst_int (Int.repr 26) tint) tuint)
                          (Ebinop Oshr
                             (Ebinop Oand (Etempvar _e tuint)
                                (Econst_int (Int.repr (-1)) tuint) tuint)
                             (Ebinop Osub (Econst_int (Int.repr 32) tint)
                                (Econst_int (Int.repr 26) tint) tint) tuint)
                          tuint)
                       (Ebinop Oor
                          (Ebinop Oshl (Etempvar _e tuint)
                             (Econst_int (Int.repr 21) tint) tuint)
                          (Ebinop Oshr
                             (Ebinop Oand (Etempvar _e tuint)
                                (Econst_int (Int.repr (-1)) tuint) tuint)
                             (Ebinop Osub (Econst_int (Int.repr 32) tint)
                                (Econst_int (Int.repr 21) tint) tint) tuint)
                          tuint) tuint)
                    (Ebinop Oor
                       (Ebinop Oshl (Etempvar _e tuint)
                          (Econst_int (Int.repr 7) tint) tuint)
                       (Ebinop Oshr
                          (Ebinop Oand (Etempvar _e tuint)
                             (Econst_int (Int.repr (-1)) tuint) tuint)
                          (Ebinop Osub (Econst_int (Int.repr 32) tint)
                             (Econst_int (Int.repr 7) tint) tint) tuint)
                       tuint) tuint) tuint)
              (Ebinop Oxor
                 (Ebinop Oand (Etempvar _e tuint) (Etempvar _f tuint) tuint)
                 (Ebinop Oand (Eunop Onotint (Etempvar _e tuint) tuint)
                    (Etempvar _g tuint) tuint) tuint) tuint)
           (Etempvar _Ki tuint) tuint))
     (Ssequence
        (Sset _T2
           (Ebinop Oadd
              (Ebinop Oxor
                 (Ebinop Oxor
                    (Ebinop Oor
                       (Ebinop Oshl (Etempvar _a tuint)
                          (Econst_int (Int.repr 30) tint) tuint)
                       (Ebinop Oshr
                          (Ebinop Oand (Etempvar _a tuint)
                             (Econst_int (Int.repr (-1)) tuint) tuint)
                          (Ebinop Osub (Econst_int (Int.repr 32) tint)
                             (Econst_int (Int.repr 30) tint) tint) tuint)
                       tuint)
                    (Ebinop Oor
                       (Ebinop Oshl (Etempvar _a tuint)
                          (Econst_int (Int.repr 19) tint) tuint)
                       (Ebinop Oshr
                          (Ebinop Oand (Etempvar _a tuint)
                             (Econst_int (Int.repr (-1)) tuint) tuint)
                          (Ebinop Osub (Econst_int (Int.repr 32) tint)
                             (Econst_int (Int.repr 19) tint) tint) tuint)
                       tuint) tuint)
                 (Ebinop Oor
                    (Ebinop Oshl (Etempvar _a tuint)
                       (Econst_int (Int.repr 10) tint) tuint)
                    (Ebinop Oshr
                       (Ebinop Oand (Etempvar _a tuint)
                          (Econst_int (Int.repr (-1)) tuint) tuint)
                       (Ebinop Osub (Econst_int (Int.repr 32) tint)
                          (Econst_int (Int.repr 10) tint) tint) tuint) tuint)
                 tuint)
              (Ebinop Oxor
                 (Ebinop Oxor
                    (Ebinop Oand (Etempvar _a tuint) (Etempvar _b tuint)
                       tuint)
                    (Ebinop Oand (Etempvar _a tuint) (Etempvar _c tuint)
                       tuint) tuint)
                 (Ebinop Oand (Etempvar _b tuint) (Etempvar _c tuint) tuint)
                 tuint) tuint))
        (Ssequence (Sset _h (Etempvar _g tuint))
           (Ssequence (Sset _g (Etempvar _f tuint))
              (Ssequence (Sset _f (Etempvar _e tuint))
                 (Ssequence
                    (Sset _e
                       (Ebinop Oadd (Etempvar _d tuint) (Etempvar _T1 tuint)
                          tuint))
                    (Ssequence (Sset _d (Etempvar _c tuint))
                       (Ssequence (Sset _c (Etempvar _b tuint))
                          (Ssequence (Sset _b (Etempvar _a tuint))
                             (Sset _a
                                (Ebinop Oadd (Etempvar _T1 tuint)
                                   (Etempvar _T2 tuint) tuint))))))))))).

Lemma rearrange_regs_proof:
 forall (Espec: OracleKind) X i (data: val) b regs
 (Hdata: isptr data)
 (H: length b = LBLOCK)
 (H0: i < 16), 
 semax (initialized _Ki (initialized _l (initialized _l' Delta_loop1)))
  (PROP  ()
   LOCAL 
   (`(eq (offset_val (Int.repr (Zsucc (Z.of_nat i) * 4)) data)) (eval_id _data);
   `(eq (Vint (big_endian_integer
             (fun z : Z =>
              @ZnthV tuchar (map Int.repr (intlist_to_Zlist b)) (z + Z.of_nat i * 4)))))
       (eval_id _l);
   `(eq X) (eval_var _X (tarray tuint 16));
   `(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i);
   `(eq (map Vint (rnd_64 regs K (firstn i b))))
     (`cons (eval_id _a)
        (`cons (eval_id _b)
           (`cons (eval_id _c)
              (`cons (eval_id _d)
                 (`cons (eval_id _e)
                    (`cons (eval_id _f)
                       (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP()) rearrange_regs
  (normal_ret_assert
     (PROP  (S i <= 16)
      LOCAL  (`(eq X) (eval_var _X (tarray tuint 16));
      `(eq (Vint (Int.repr (Z.succ (Z.of_nat i) - 1)))) (eval_id _i);
      `(eq (offset_val (Int.repr (Z.succ (Z.of_nat i) * 4)) data)) (eval_id _data);
      `(eq (map Vint (rnd_64 regs K (firstn (S i) b))))
        (`cons (eval_id _a)
           (`cons (eval_id _b)
              (`cons (eval_id _c)
                 (`cons (eval_id _d)
                    (`cons (eval_id _e)
                       (`cons (eval_id _f)
                          (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
        SEP())).
Admitted.

Lemma sha256_block_data_order_loop1_proof:
  forall (Espec : OracleKind)
     (b: list int) (data: val) (regs: list int)
     (Hdata: isptr data),
     length b = LBLOCK ->
     semax Delta_loop1
  (PROP ()
   LOCAL (`(eq (Vint (Int.repr 0))) (eval_id _i);
               `(eq data) (eval_id _data);
               `(eq (map Vint regs)) 
                  (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                   (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
   SEP ( `(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(arrayof_ (mapsto_ Tsh tuint) tuint 16) (eval_var _X (tarray tuint 16));
           `(data_block (intlist_to_Zlist b) data)))
  block_data_order_loop1
  (normal_ret_assert
    (PROP () 
     LOCAL(`(eq (map Vint (rnd_64 regs K b))) 
                   (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
     SEP ( `(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(array_at tuint Tsh (@ZnthV tuint (map swap b)) 0 16) (eval_var _X (tarray tuint 16));
           `(data_block (intlist_to_Zlist b) data))) ).
Proof.
unfold block_data_order_loop1, Delta_loop1.
intros.
simpl nth; fold rearrange_regs.
abbreviate_semax.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name l_ _l.
name Ki _Ki.
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
assert (LBE := LBLOCK_zeq).
normalize.

Definition loop1_inv (rg0: list int) (b: list int) (data X: val) (delta: Z) (i: nat) :=
    PROP ( i <= 16 )
    LOCAL  (`(eq X) (eval_var _X (tarray tuint 16));
               `(eq (Vint (Int.repr (Z.of_nat i - delta)))) (eval_id _i);
               `(eq (offset_val (Int.repr ((Z.of_nat i)*4)) data)) (eval_id _data);
     `(eq (map Vint (rnd_64 rg0 K (firstn i b))))
      (`cons (eval_id _a)
         (`cons (eval_id _b)
            (`cons (eval_id _c)
               (`cons (eval_id _d)
                  (`cons (eval_id _e)
                     (`cons (eval_id _f)
                        (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
     SEP (`(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))
      (eval_var _K256 (tarray tuint 64));
    `(array_at tuint Tsh (@ZnthV tuint (map swap b)) 0 (Z.of_nat i) X);
   `(arrayof_' (mapsto_ Tsh tuint) tuint (Z.of_nat i) (LBLOCK-i) X);
   `(data_block (intlist_to_Zlist b) data)).

apply semax_pre with (EX X:val, EX i:nat, loop1_inv regs b data X 0 i).
unfold loop1_inv.
go_lower.
apply exp_right with (eval_var _X (tarray tuint 16) rho).
apply exp_right with 0.
(* 345,184   326,392*)
abstract (solve [entailer!; omega]).
(* 419,452   431,980 *)
apply extract_exists_pre; intro X.

apply semax_post' with (loop1_inv regs b data X 0 LBLOCK).
unfold loop1_inv.
(* 419,452  431,980 *)
abstract 
solve [entailer! ;
           rewrite <- H2; repeat f_equal; 
           symmetry; apply firstn_same; omega].
(* 445,728  479,964 *)
clear POSTCONDITION.

apply (semax_loop _ _ (EX i:nat, loop1_inv regs b data X 1 i)).
Focus 2. {
apply extract_exists_pre; intro i.
forward.
apply exp_right with i.
(* 452,280  481,476 *)
abstract
solve [unfold loop1_inv;  entailer! ; f_equal; omega].
(* 561,900  574,392 *)
} Unfocus.

apply extract_exists_pre; intro i.
unfold loop1_inv.
forward_if (
PROP  (i < 16)
   LOCAL  (`(eq X) (eval_var _X (tarray tuint 16));
   `(eq (Vint (Int.repr (Z.of_nat (0 + i))))) (eval_id _i);
               `(eq (offset_val (Int.repr ((Z.of_nat i)*4)) data)) (eval_id _data);
   `(eq (map Vint (rnd_64 regs K (firstn i b))))
     (`cons (eval_id _a)
        (`cons (eval_id _b)
           (`cons (eval_id _c)
              (`cons (eval_id _d)
                 (`cons (eval_id _e)
                    (`cons (eval_id _f)
                       (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP 
   (`(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))
      (eval_var _K256 (tarray tuint 64));
   `(array_at tuint Tsh (@ZnthV tuint (map swap b)) 0 (Z.of_nat i) X);
   `(arrayof_' (mapsto_ Tsh tuint) tuint (Z.of_nat i) (LBLOCK-i) X);
   `(data_block (intlist_to_Zlist b) data))).
(* 587,640  592,608 *)
abstract solve [entailer].
(* 613,416  655,716 *)
forward.
(* 619,968  655,716 *)
abstract solve [entailer; apply prop_right; clear - H2; split; [omega | f_equal; omega]].
(* 726,056  709,784 *)
eapply semax_pre; [ | apply semax_break ].
unfold POSTCONDITION, abbreviate.
unfold overridePost. rewrite if_false by congruence.
unfold loop1_ret_assert.
rewrite normal_ret_assert_elim.
(* 738,188  709,784 *)
abstract solve [entailer; 
 assert (i=16) by omega; subst i; 
 apply andp_right; [ apply prop_right | cancel];
 replace 16 with LBLOCK in H3 by omega;
 repeat split; auto].
(* 854,860 750,176 *)
unfold MORE_COMMANDS, POSTCONDITION, abbreviate.
make_sequential.
unfold loop1_ret_assert.
apply extract_exists_post with (S i).
rewrite inj_S.
simpl plus.
normalize.

(* 945,760 834,556 *)

do 2 apply -> seq_assoc.
eapply semax_frame_seq
 with (P1 := [])
         (Q1 :=  [
`(eq X) (eval_var _X (tarray tuint 16)),  
`(eq (Vint (Int.repr (Z.of_nat i)))) (eval_id _i),
`(eq (offset_val (Int.repr (Z.of_nat i * 4)) data)) (eval_id _data),
`(eq (map Vint (rnd_64 regs K (firstn i b))))
  (`cons (eval_id _a)
     (`cons (eval_id _b)
        (`cons (eval_id _c)
           (`cons (eval_id _d)
              (`cons (eval_id _e)
                 (`cons (eval_id _f)
                    (`cons (eval_id _g) (`cons (eval_id _h) `[]))))))))])
         (Frame := [`(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))
      (eval_var _K256 (tarray tuint 64)),
   `(array_at tuint Tsh (@ZnthV tuint (map swap b)) 0 (Z.of_nat i) X),
   `(arrayof_' (mapsto_ Tsh tuint) tuint (Z.of_nat i) (LBLOCK - i) X)]); 
   [apply (read32_reversed_in_bytearray _ (Int.repr (Z.of_nat i * 4)) 0 (Zlength (intlist_to_Zlist b)) data _ Tsh 
                     (@ZnthV tuchar (map Int.repr (intlist_to_Zlist b))))
   | | | ].
(* 945,760 834,556 *)
abstract solve [entailer!; try omega; 
 rewrite Zlength_correct; rewrite length_intlist_to_Zlist; rewrite H;
 replace (Z.of_nat (4 * LBLOCK) - 4)%Z
  with ((Z.of_nat LBLOCK - 1) * 4)%Z; 
    [apply Zmult_le_compat_r; omega | ];
 rewrite Zmult_comm;
 rewrite Z.mul_sub_distr_l;
 reflexivity].
(* 990,216 849,172 *)
abstract solve [entailer!].
(* 1,078,128 849,172 *)
auto 50 with closed.
simpl.
change (array_at tuchar Tsh (@ZnthV tuchar (map Int.repr (intlist_to_Zlist b))) 0
        (Zlength (intlist_to_Zlist b)) data)
  with (data_block  (intlist_to_Zlist b) data).

forward. (* l := l'; *)
forward. (* data := data + 4; *)
(* 1,194,800 849,172 *)
abstract solve [entailer!].
(* 1,254,920 849,172 *)
normalize.
(* 1,291,784 894,136 *)
simpl typeof.

replace (LBLOCK-i) with (Z.to_nat (Z.of_nat LBLOCK - Z.of_nat i))
 by (rewrite Z2Nat.inj_sub by omega; repeat rewrite Nat2Z.id; auto).

eapply semax_seq'.
ensure_normal_ret_assert;
hoist_later_in_pre.

match goal with
| |- @semax ?Esp ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) 
     (Sassign (Ederef (Ebinop Oadd ?e1 ?ei _) ?t) ?e2) _ =>
  let n := fresh "n" in evar (n: nat); 
  let sh := fresh "sh" in evar (sh: share);
  let contents := fresh "contents" in evar (contents: Z -> reptype t);
  let lo := fresh "lo" in evar (lo: Z);
  let hi := fresh "hi" in evar (hi: Z);
  let a := fresh "a" in evar (a: val);
  let H := fresh in 
  assert (H: PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx (number_list O R))) 
     |-- (`(numbd n (arrayof_' (mapsto_ sh t) t lo (Z.to_nat (hi-lo)) a))) * TT);
  [unfold number_list, n, sh, contents, lo, hi, a; 
  repeat rewrite @numbd_lift0; 
  repeat rewrite @numbd_lift1; repeat rewrite @numbd_lift2;
  solve [go_lower; repeat apply andp_left2; cancel ]
 | clear H ];
eapply(@semax_store_initialize_array _ Delta n sh tuint contents lo hi (`a));
unfold number_list, n, sh, contents, lo, hi, a;
  clear n sh contents lo hi a;
  [solve [auto] | reflexivity | reflexivity 
  | reflexivity
  | autorewrite with norm; try reflexivity;
    fail 4 "Cannot prove 6th premise of semax_store_initialize_array"
  | ]
end.
name l'_ _l'.
(* 1,371,592 965,884 *)
solve [entailer!; [eapply eval_var_isptr; eauto | omega | omega]].
(* 1,433,728 1,066,896 *)
instantiate (1:= (@ZnthV tuint (map swap b))).
unfold replace_nth; abbreviate_semax.
(* 1,503,420 1,083,564 *)

rewrite <- (array_at_ext tuint Tsh (@ZnthV tuint (map swap b))
     (upd (@ZnthV tuint (map swap b)) (Z.of_nat i)
              (big_endian_integer
                 (fun z : Z =>
                  @ZnthV tuchar (map Int.repr (intlist_to_Zlist b))
                    (z + Z.of_nat i * 4))))).
Focus 2.
intros.
unfold upd.
if_tac; try auto.
subst i0.
unfold ZnthV.
rewrite Nat2Z.id.
symmetry; apply nth_big_endian_int; omega.
(* 1,506,948 1,110,852 *)
normalize.
gather_SEP 4%Z 0%Z.
replace_SEP 0%Z
  (`(array_at tuint Tsh (@ZnthV tuint (map swap b))
        0 (Z.of_nat i + 1) X)).
apply andp_left2.
apply andp_left2.
go_lower.
rewrite <- split_array_at.
cancel.
omega.
(* 1,506,948 1,134,576 *)
forward.  (* Ki=K256[i]; *)
(* 1,689,280 1,212,872 *)
abstract solve [entailer!; 
  [omega | change (Zlength K) with 64%Z; omega 
  | eapply eval_var_isptr; eauto]].
(* 1,811,028 1,406,332 *)
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.

match goal with 
  |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ 
       (normal_ret_assert (PROPx ?P (LOCALx ?Q _)))
 => apply semax_post' with (PROPx P (LOCALx Q (SEPx R)));
  [ | change R with (nil++R); apply semax_frame_PQR with (R2:=R)]
end.
apply andp_derives; auto.
apply andp_derives; auto.
replace (Z.succ (Z.of_nat i)) with (Z.of_nat i + 1)%Z by omega.
go_lower0; cancel.
apply derives_refl'; f_equal.
rewrite Z2Nat.inj_sub by omega.
repeat rewrite Nat2Z.id; auto.
rewrite Z2Nat.inj_add by omega.
repeat rewrite Nat2Z.id; auto.
f_equal.
change (Z.to_nat 1) with 1.
clear; omega.
auto 50 with closed.
(* 1,811,028 1,429,048 *)
eapply semax_pre; [ | apply rearrange_regs_proof; auto ].
entailer!.
destruct data; inv Hdata; simpl; f_equal.
rewrite Int.add_assoc.
f_equal.
unfold Z.succ.
rewrite Z.mul_add_distr_r.
rewrite <- add_repr.
f_equal.
destruct (eval_id _l' rho); inv H2.
inv H3; auto.
Qed.

Lemma datablock_local_facts:
 forall f data,
  data_block f data |-- !! (isptr data).
Admitted.
Hint Resolve datablock_local_facts : saturate_local.

Lemma local_and_retval:
 forall (i: ident) (P: val -> Prop) (R: mpred),
    `(local (`P retval) && `R) (get_result1 i) = local (`P (eval_id i)) && `R.
Proof.
intros.
extensionality rho.
super_unfold_lift.
unfold get_result1. simpl.
unfold local, lift1.
f_equal; auto.
Qed.
Hint Rewrite local_and_retval: norm.

Lemma sha256_block_data_order_loop2_proof:
  forall (Espec : OracleKind)
     (b: list int) (data: val) (regs: list int),
     length b = LBLOCK ->
     semax  
       (initialized _i
          (initialized _h
           (initialized _g
              (initialized _f
                 (initialized _e
                    (initialized _d
                       (initialized _c
                          (initialized _b
                             (initialized _a
                                (initialized _data
   (func_tycontext f_sha256_block_data_order Vprog Gtot)))))))))))
  (PROP ()
   LOCAL (`(eq (map Vint (rnd_64 regs K b))) 
                   (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
   SEP ( `(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(arrayof_ (mapsto_ Tsh tuint) tuint 16) (eval_var _X (tarray tuint 16))))
  block_data_order_loop2
  (normal_ret_assert
    (PROP () 
     LOCAL(`(eq (map Vint (rnd_64 regs K (rev (generate_word (rev b) 48)))))
                   (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
     SEP ( `(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(arrayof_ (mapsto_ Tsh tuint) tuint 16) (eval_var _X (tarray tuint 16))))).
Admitted.

Lemma semax_seq_congr:  (* not provable *)
 forall (Espec: OracleKind) s1 s1' s2 s2',
  (forall Delta P R, semax Delta P s1 R <-> semax Delta P s1' R) ->
  (forall Delta P R, semax Delta P s2 R <-> semax Delta P s2' R) ->
 (forall Delta P R, 
    semax Delta P (Ssequence s1 s2) R <->
    semax Delta P (Ssequence s1' s2') R).
Abort.

Definition load8 id ofs :=
 (Sset id
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
              t_struct_SHA256state_st) _h (tarray tuint 8))
          (Econst_int (Int.repr ofs) tint) (tptr tuint)) tuint)).

Lemma sha256_block_load8:
  forall (Espec : OracleKind) 
     (data: val) (r_h: list int) (ctx: val)
   (H5 : length r_h = 8),
     semax  
      (initialized _data
         (func_tycontext f_sha256_block_data_order Vprog Gtot))
  (PROP  ()
   LOCAL  (`eq (eval_id _data) (eval_expr (Etempvar _in (tptr tvoid)));
   `(eq ctx) (eval_id _ctx); `(eq data) (eval_id _in))
   SEP  (`(array_at tuint Tsh (@ZnthV tuint r_h) 0 (Zlength r_h) ctx)))
   (Ssequence (load8 _a 0)
     (Ssequence (load8 _b 1)
     (Ssequence (load8 _c 2)
     (Ssequence (load8 _d 3)
     (Ssequence (load8 _e 4)
     (Ssequence (load8 _f 5)
     (Ssequence (load8 _g 6)
     (Ssequence (load8 _h 7)
         Sskip))))))))
  (normal_ret_assert 
  (PROP  ()
   LOCAL  (`(eq (map Vint r_h))
                    (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
)));
   `eq (eval_id _data) (eval_expr (Etempvar _in (tptr tvoid)));
   `(eq ctx) (eval_id _ctx); `(eq data) (eval_id _in))
   SEP  (`(array_at tuint Tsh (@ZnthV tuint r_h) 0 (Zlength r_h) ctx)))).
Proof.
intros.
simplify_Delta.
unfold load8.
abbreviate_semax.
normalize.
simpl.
normalize.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name l_ _l.
name Ki _Ki.
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
abbreviate_semax.
assert (H5': Zlength r_h = 8%Z).
rewrite Zlength_correct; rewrite H5; reflexivity.
do 8 (forward; [abstract (entailer!; omega) | ]).
forward.  (* skip; *)
entailer.
do 9 (destruct r_h as [ | ?h r_h ] ; [inv H5 | ]).
reflexivity.
inv H5.
Qed.

Definition get_h (n: Z) :=
    Sset _t
        (Ederef
           (Ebinop Oadd
              (Efield
                 (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                    t_struct_SHA256state_st) _h (tarray tuint 8))
              (Econst_int (Int.repr n) tint) (tptr tuint)) tuint).

Definition add_h (n: Z) (i: ident) :=
   Sassign
       (Ederef
          (Ebinop Oadd
             (Efield
                (Ederef (Etempvar _ctx (tptr t_struct_SHA256state_st))
                   t_struct_SHA256state_st) _h (tarray tuint 8))
             (Econst_int (Int.repr n) tint) (tptr tuint)) tuint)
       (Ebinop Oadd (Etempvar _t tuint) (Etempvar i tuint) tuint).

Definition add_them_back :=
 [get_h 0, add_h 0 _a,
  get_h 1, add_h 1 _b,
  get_h 2, add_h 2 _c,
  get_h 3, add_h 3 _d,
  get_h 4, add_h 4 _e,
  get_h 5, add_h 5 _f,
  get_h 6, add_h 6 _g,
  get_h 7, add_h 7 _h].


Lemma add_them_back_proof:
  forall (Espec : OracleKind)
     (b: list int) (r_h: list int)(ctx: val)(hashed: list int),
     length b = LBLOCK ->
     semax  
       (initialized _i
          (initialized _h
           (initialized _g
              (initialized _f
                 (initialized _e
                    (initialized _d
                       (initialized _c
                          (initialized _b
                             (initialized _a
                                (initialized _data
   (func_tycontext f_sha256_block_data_order Vprog Gtot)))))))))))
   (PROP  ()
   LOCAL 
   (`(eq (map Vint (rnd_64 r_h K (rev (generate_word (rev b) 48)))))
      (`cons (eval_id _a)
         (`cons (eval_id _b)
            (`cons (eval_id _c)
               (`cons (eval_id _d)
                  (`cons (eval_id _e)
                     (`cons (eval_id _f)
                        (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
   SEP 
   (`(array_at tuint Tsh (@ZnthV tuint (process_msg init_registers hashed)) 0
       (Zlength (process_msg init_registers hashed)) ctx)))
   (sequence add_them_back Sskip)
  (normal_ret_assert
   (PROP() LOCAL() 
    SEP (`(array_at tuint Tsh (@ZnthV tuint 
                   (map2 Int.add (process_msg init_registers hashed)
                                         (rnd_64 r_h K (rev (generate_word (rev b) 48)))))
            0 (Zlength (process_msg init_registers hashed)) ctx)))).
Admitted.

Lemma array_at_arrayof_:
  forall t sh f N N' v,
 N' = Z.of_nat N ->
 array_at t sh f 0 N' v |-- arrayof_ (mapsto_ sh t) t N v.
Proof.
intros.
Admitted.

Hint Extern 1 (array_at _ _ _ _ _ _ |-- arrayof_ _ _ _ _) =>
  (apply array_at_arrayof_; reflexivity) : cancel.

Lemma elim_globals_only:
  forall Delta g i t rho,
  tc_environ Delta rho /\ (glob_types Delta) ! i = Some g ->
  eval_var i t (globals_only rho) = eval_var i t rho.
Admitted.

Lemma body_sha256_block_data_order: semax_body Vprog Gtot f_sha256_block_data_order sha256_block_data_order_spec.
Proof.
start_function.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name l_ _l.
name Ki _Ki.
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
unfold sha256state_.
simpl_stackframe_of. 
normalize. intros [r_h [r_Nl [r_Nh [r_data r_num]]]].
repeat simpl_typed_mapsto.
unfold fst,snd.
normalize.
unfold s256_relate in H1. destruct a.
simpl in H1.
unfold s256_Nh, s256_Nl, s256_data, s256_num, fst, snd in H1.
destruct H1 as [? [? [? [H4 [H4b H4c]]]]].
destruct H4b as [n H4b].
change (length hashed = 16 * n)%nat in H4b.
assert (length r_h = 8%nat) by (subst r_h; apply length_process_msg).
(* assert (H5': Zlength r_h = 8) by (rewrite Zlength_correct; rewrite H5; reflexivity). *)
forward. (* data = in; *)
abbreviate_semax.
match goal with |- semax _ (PROPx nil ?QR) _ _ =>
 apply semax_pre0 with (PROPx [isptr data] QR)
end.
apply andp_right; [ | apply andp_left2; auto].
entailer.
normalize.
match goal with |- semax _ _ ?c _ =>
 eapply seq_assocN with (cs := sequenceN 8 c)
end.
eapply semax_frame1.
eapply sha256_block_load8 with (ctx:=ctx); eassumption.
simplify_Delta; reflexivity.
entailer!.
auto 50 with closed.
abbreviate_semax.
simpl.
change (lift1 (arrayof_ (mapsto_ Tsh tuint) tuint (Pos.to_nat 16)))
  with (`(arrayof_ (mapsto_ Tsh tuint) tuint (Pos.to_nat 16))).
change (lift1 (array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K)))
    with (`(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))).

forward.  (* i = 0; *)

eapply semax_frame_seq.
replace Delta with Delta_loop1
 by (simplify_Delta; reflexivity).
simple apply (sha256_block_data_order_loop1_proof
  _ b data r_h); auto.
entailer!.
auto 50 with closed.
simpl; abbreviate_semax.

eapply semax_frame_seq.
apply sha256_block_data_order_loop2_proof
              with (regs:=r_h)(b:=b); eassumption.
entailer!.
auto 50 with closed.
unfold app; abbreviate_semax.
eapply seq_assocN with (cs := add_them_back).

eapply semax_frame1.
apply (add_them_back_proof _ b r_h ctx hashed); try eassumption.
simplify_Delta; reflexivity.
entailer. cancel.
auto 50 with closed.
simpl; abbreviate_semax.

forward.
entailer.
unfold frame_ret_assert; simpl.
unfold sha256state_.
normalize.
remember (map2 Int.add (process_msg init_registers hashed)
        (rnd_64 (process_msg init_registers hashed) K
           (rev (generate_word (rev b) 48)))) as regs.
apply exp_right with (regs, (r_Nl, (r_Nh, (r_data, r_num)))).
simpl_typed_mapsto. unfold fst,snd.
autorewrite with norm.

assert (length regs = 8%nat)
  by (subst; apply length_map2_add_rnd_64; auto).
rewrite Zlength_correct; rewrite length_process_msg.
rewrite (Zlength_correct regs); rewrite H1.
simpl Z.of_nat.
apply andp_right.
Focus 2. {
unfold stackframe_of; simpl.
rewrite var_block_typed_mapsto_.
normalize. simpl_typed_mapsto.
change (Pos.to_nat 16) with 16%nat.
unfold id.
erewrite elim_globals_only
  by (split; [eassumption | reflexivity]).
cancel.
} Unfocus.
apply prop_right.
repeat split; simpl; auto.
subst regs.
apply process_msg_block; auto.
eauto.
unfold s256_Nh, s256_Nl; simpl.
rewrite length_intlist_to_Zlist.
rewrite app_length.
rewrite H.
rewrite length_intlist_to_Zlist in H2.
change CBLOCK with 64%nat.
change LBLOCK with 16%nat.
rewrite mult_plus_distr_l.
change (4*16)%nat with 64%nat.
omega.
exists (S n). rewrite app_length. rewrite H4b; rewrite H.
change LBLOCK with 16%nat.
transitivity (16 * n + 16 * 1)%nat; [reflexivity | ].
rewrite <- mult_plus_distr_l.
rewrite plus_comm. reflexivity.
Qed.


(*

Ltac unfold_for_go_lower :=
  cbv delta [PROPx LOCALx SEPx
                       eval_exprlist eval_expr eval_lvalue cast_expropt 
                       eval_cast eval_binop eval_unop
                      tc_expropt tc_expr tc_lvalue 
                      typecheck_expr typecheck_lvalue
                      function_body_ret_assert 
                      make_args' bind_ret get_result1 retval
                      eval_cast classify_cast
                      denote_tc_assert
    liftx LiftEnviron Tarrow Tend lift_S lift_T
    lift_prod lift_last lifted lift_uncurry_open lift_curry 
     local lift lift0 lift1 lift2 lift3 
    LiftNatDed' LiftSepLog' LiftClassicalSep' 
    LiftNatDed LiftSepLog
   ] beta iota.

Ltac go_lower0 := 
intros ?rho;
 try (simple apply grab_tc_environ; intro);
 repeat (progress unfold_for_go_lower;
      simpl andp; simpl prop; simpl sepcon; simpl emp; simpl orp; cbv beta iota).


Ltac ff := 
match goal with Delta := context [initialized ?i (@pair ?u ?v ?w ?x)] |- _ =>
 let D := fresh "D" in
  set (D := initialized i (@pair u v w x)) in Delta;
  cbv delta [initialized] in D; simpl in D;
  unfold D in *; clear D
end.
*)










