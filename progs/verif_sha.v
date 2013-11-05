Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Local Open Scope logic.

Definition __builtin_read32_reversed_spec :=
 DECLARE ___builtin_read32_reversed
  WITH p: val, sh: share, contents: Z -> int
  PRE [ 1%positive OF tptr tuint ] 
        PROP() LOCAL (`(eq p) (eval_id 1%positive))
        SEP (`(array_at tuchar sh (cSome contents) 0 4 p))
  POST [ tuint ] 
     local (`(eq (Vint (big_endian_integer contents))) retval) &&
     `(array_at tuchar sh (cSome contents) 0 4 p).

Definition __builtin_write32_reversed_spec :=
 DECLARE ___builtin_write32_reversed
  WITH p: val, sh: share, contents: Z -> int
  PRE [ 1%positive OF tptr tuint, 2%positive OF tuint ] 
        PROP(writable_share sh)
        LOCAL (`(eq p) (eval_id 1%positive);
                     `(eq (Vint(big_endian_integer contents))) (eval_id 2%positive))
        SEP (`(memory_block sh (Int.repr 4) p))
  POST [ tvoid ] 
     `(array_at tuchar sh (cSome contents) 0 4 p).

Definition memcpy_spec :=
  DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, n: Z, contents: Z -> int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (writable_share (snd sh))
       LOCAL (`(eq p) (eval_id 1%positive); `(eq q) (eval_id 2%positive);
                    `(eq n) (`Int.unsigned (`force_int (eval_id 3%positive))))
       SEP (`(array_at tuchar (fst sh) (cSome contents) 0 n q);
              `(memory_block (snd sh) (Int.repr n) p))
    POST [ tptr tvoid ]
         local (`(eq p) retval) &&
       (`(array_at tuchar (fst sh) (cSome contents) 0 n q) *
        `(array_at tuchar (snd sh) (cSome contents) 0 n p)).

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
       (`(array_at tuchar sh (fun _ => Some c) 0 n p)).

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
  array_at tuchar Tsh (ZnthV tuchar (map Int.repr contents)) 0 (Zlength contents) v.

Lemma datablock_local_facts:
 forall f data,
  data_block f data |-- !! (isptr data).
Admitted.
Hint Resolve datablock_local_facts : saturate_local.

Definition sha256_block_data_order_spec :=
  DECLARE _sha256_block_data_order
    WITH a: s256abs, b: list int, ctx : val, data: val, sh: share
   PRE [ _ctx OF tptr t_struct_SHA256state_st, _in OF tptr tvoid ]
         PROP(length b = LBLOCK) 
         LOCAL (`(eq ctx) (eval_id _ctx); `(eq data) (eval_id _in))
         SEP (`(sha256state_ a ctx); `(data_block (intlist_to_Zlist b) data);
                `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K)) (eval_var _K256 (tarray tuint 64)))
   POST [ tvoid ]
          (`(sha256state_ (process_block_abs b a) ctx) *
          `(data_block (intlist_to_Zlist b) data) *
          `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K)) (eval_var _K256 (tarray tuint 64))).
                
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
 forall {Espec: OracleKind} Delta (ofs: int) (lo hi: Z) base e sh contents i P Q
 (VS:  (var_types Delta) ! ___builtin_read32_reversed = None) 
 (GS: (glob_types Delta) ! ___builtin_read32_reversed =
    Some (Global_func (snd __builtin_read32_reversed_spec)))
 (TE: typeof e = tptr tuint)
 (CLOQ: Forall (closed_wrt_vars (eq i)) Q)
 (Hcontents: forall i, (lo <= i < hi)%Z -> isSome (contents i)),
 PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (TT))) |-- PROP ((lo <= Int.unsigned ofs <= hi-4 )%Z)
         LOCAL (tc_expr Delta e; `(eq (offset_val ofs base)) (eval_expr e))
         SEP  (TT) ->
 semax Delta  (PROPx P (LOCALx Q (SEP (`(array_at tuchar sh contents lo hi base)))))
        (Scall (Some i)
           (Evar ___builtin_read32_reversed
              (Tfunction (Tcons (tptr tuint) Tnil) tuint))
           [e])
        (normal_ret_assert
         (PROP () 
         (LOCALx (`(eq (Vint (big_endian_integer (fun z => force_option Int.zero (contents (z+Int.unsigned ofs)%Z))))) (eval_id i)
                        :: Q)                 
         SEP (`(array_at tuchar sh contents lo hi base))))).
Proof.
intros.
apply semax_pre with
 (PROP  ((lo <= Int.unsigned ofs <= hi - 4)%Z)
        (LOCALx (tc_expr Delta e :: `(eq (offset_val ofs base)) (eval_expr e) :: Q)
         (SEP(`(array_at tuchar sh contents lo hi base))))).
rewrite <- (andp_dup (PROPx P _)).
eapply derives_trans; [ apply andp_derives | ].
eapply derives_trans; [ | apply H].
apply andp_derives; auto.
apply andp_derives; auto.
go_lowerx.
apply sepcon_derives; auto.
apply TT_right.
instantiate (1:= PROPx nil (LOCALx Q (SEP  (`(array_at tuchar sh contents lo hi base))))).
go_lowerx. entailer.
go_lowerx; entailer.
normalize.
clear H.
normalize.
rewrite (split_array_at (Int.unsigned ofs)) by omega.
rewrite (split_array_at (Int.unsigned ofs + 4)%Z) with (hi:=hi) by omega.
normalize.
match goal with |- semax _ (PROPx _ (LOCALx _ ?A)) _ _ =>
 replace A  with (SEPx( [
         `(array_at tuchar sh contents (Int.unsigned ofs)
             (Int.unsigned ofs + 4) base)] ++
               [`(array_at tuchar sh contents lo (Int.unsigned ofs) base),
         `(array_at tuchar sh contents (Int.unsigned ofs + 4) hi base)]))
 by (simpl app; apply pred_ext; go_lowerx; cancel)
end.
eapply semax_frame1; try reflexivity;
 [ |  apply derives_refl | auto 50 with closed].
eapply semax_pre_post.
Focus 3.
evar (tl: typelist).
replace (Tcons (tptr tuint) Tnil) with tl.
unfold tl.
eapply semax_call_id1'; try eassumption.
2: reflexivity.
apply GS.
2: reflexivity.
Unfocus.
instantiate (3:=nil).
apply andp_left2.
instantiate (2:=(offset_val ofs base, sh, fun z => force_option Int.zero (contents (z + Int.unsigned ofs)%Z))).
cbv beta iota.
instantiate (1:=nil).
unfold split; simpl @snd.
go_lowerx.
entailer.
apply andp_right; [apply prop_right; repeat split; auto | ].
hnf. simpl.
rewrite TE.
repeat rewrite denote_tc_assert_andp; repeat split; auto.
rewrite <- H3.
rewrite TE.
destruct base; inv Pbase; reflexivity.
pattern ofs at 4;
 replace ofs with (Int.repr (sizeof tuchar * Int.unsigned ofs))%Z
 by (simpl sizeof; rewrite Z.mul_1_l; apply Int.repr_unsigned).
rewrite <- offset_val_array_at.
apply derives_refl'.
apply equal_f. rewrite Z.add_0_r. apply array_at_ext.
intros. unfold cSome. rewrite Z.sub_add.
clear - H5 H0 Hcontents.
specialize (Hcontents i0);
 destruct (contents i0); [ | elimtype False; apply Hcontents; omega]. reflexivity.
2: auto with closed.
intros; apply andp_left2.
apply normal_ret_assert_derives'.
go_lowerx.
entailer.
apply derives_refl'.
pattern ofs at 2;
 replace ofs with (Int.repr (sizeof tuchar * Int.unsigned ofs))%Z
 by (simpl sizeof; rewrite Z.mul_1_l; apply Int.repr_unsigned).
rewrite <- offset_val_array_at.
apply equal_f. rewrite Z.add_0_r. 
apply array_at_ext; intros.
unfold cSome. rewrite Z.sub_add.
clear - H3 H0 Hcontents.
specialize (Hcontents i0); destruct (contents i0);
  [reflexivity | contradiction Hcontents; omega].
Qed.


(* Arguments Int.unsigned n : simpl never.   remove this once recompiled forward.v *)

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
 forall (Espec: OracleKind) i (data: val) b regs
 (Hdata: isptr data)
 (H: length b = LBLOCK)
 (H0: i < 16), 
 semax (initialized _Ki (initialized _l (initialized _l' Delta_loop1)))
  (PROP  ()
   LOCAL 
   (`(eq (offset_val (Int.repr (Zsucc (Z.of_nat i) * 4)) data)) (eval_id _data);
   `(eq (Vint (big_endian_integer
             (fun z : Z =>
              force_option Int.zero
                (ZnthV tuchar (map Int.repr (intlist_to_Zlist b))
                   (z + Z.of_nat i * 4))))))
       (eval_id _l);
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
      LOCAL  (`(eq (Vint (Int.repr (Z.succ (Z.of_nat i) - 1)))) (eval_id _i);
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

Definition f_upto {A} (f: Z -> option A) (bound: Z) (i: Z) : option A :=
 if zlt i bound then f i else None.

Lemma array_at_f_upto_lo:
  forall t sh contents lo hi, 
  array_at t sh (f_upto contents lo) lo hi = array_at_ t sh lo hi.
Proof.
intros; apply array_at_ext; intros.
unfold f_upto; if_tac; auto. omega.
Qed.

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
   SEP ( `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16));
           `(data_block (intlist_to_Zlist b) data)))
  block_data_order_loop1
  (normal_ret_assert
    (PROP () 
     LOCAL(`(eq (map Vint (rnd_64 regs K b))) 
                   (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
     SEP ( `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(array_at tuint Tsh (ZnthV tuint (map swap b)) 0 16) (eval_var _X (tarray tuint 16));
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
name l'_ _l'.
name Ki _Ki.
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
assert (LBE := LBLOCK_zeq).
normalize.

Definition loop1_inv (rg0: list int) (b: list int) (data: val) (delta: Z) (i: nat) :=
    PROP ( i <= 16 )
    LOCAL  (`(eq (Vint (Int.repr (Z.of_nat i - delta)))) (eval_id _i);
               `(eq (offset_val (Int.repr ((Z.of_nat i)*4)) data)) (eval_id _data);
     `(eq (map Vint (rnd_64 rg0 K (firstn i b))))
      (`cons (eval_id _a)
         (`cons (eval_id _b)
            (`cons (eval_id _c)
               (`cons (eval_id _d)
                  (`cons (eval_id _e)
                     (`cons (eval_id _f)
                        (`cons (eval_id _g) (`cons (eval_id _h) `[])))))))))
     SEP (`(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
      (eval_var _K256 (tarray tuint 64));
    `(array_at tuint Tsh (f_upto (ZnthV tuint (map swap b)) (Z.of_nat i) ) 0 (Z.of_nat LBLOCK)) (eval_var _X (tarray tuint 16));
   `(data_block (intlist_to_Zlist b) data)).

apply semax_pre with (EX i:nat, loop1_inv regs b data 0 i).
unfold loop1_inv.
apply exp_right with 0.
(* 345,184   326,392*)
rewrite array_at_f_upto_lo.
abstract (solve [entailer!; omega]).
(* 419,452   431,980 *)

apply semax_post' with (loop1_inv regs b data 0 LBLOCK).
unfold loop1_inv.
(* 419,452  431,980 *)
abstract 
solve [entailer! ;
           rewrite <- H2; repeat f_equal; 
           symmetry; apply firstn_same; omega].
(* 445,728  479,964 *)
clear POSTCONDITION.

apply (semax_loop _ _ (EX i:nat, loop1_inv regs b data 1 i)).
Focus 2. {
apply extract_exists_pre; intro i.
forward.  (*  i += 1; *)
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
   LOCAL  (`(eq (Vint (Int.repr (Z.of_nat (0 + i))))) (eval_id _i);
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
   (`(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
      (eval_var _K256 (tarray tuint 64));
   `(array_at tuint Tsh (f_upto (ZnthV tuint (map swap b)) (Z.of_nat i)) 0 (Z.of_nat LBLOCK)) (eval_var _X (tarray tuint 16));
   `(data_block (intlist_to_Zlist b) data))).
(* 587,640  592,608 *)
abstract solve [entailer].
(* 613,416  655,716 *)
forward.  (* skip; *)
(* 619,968  655,716 *)
abstract solve [entailer; apply prop_right; clear - H2; split; [omega | f_equal; omega]].
(* 726,056  709,784 *)
forward.  (* break; *)
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
         (Frame := [`(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
      (eval_var _K256 (tarray tuint 64)),
   `(array_at tuint Tsh (f_upto (ZnthV tuint (map swap b)) (Z.of_nat i)) 0 (Z.of_nat LBLOCK)) (eval_var _X (tarray tuint 16))]); 
   [apply (read32_reversed_in_bytearray _ (Int.repr (Z.of_nat i * 4)) 0 (Zlength (intlist_to_Zlist b)) data _ Tsh 
                     (ZnthV tuchar (map Int.repr (intlist_to_Zlist b))))
   | | | ].
reflexivity.
reflexivity.
reflexivity.
auto 50 with closed.
(* 945,760 834,556 *)
intros.
apply ZnthV_isSome.
rewrite Zlength_correct. rewrite map_length.
rewrite Zlength_correct in H1.
apply H1.
abstract solve [entailer!; repeat split; auto; try omega; 
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
change (array_at tuchar Tsh (ZnthV tuchar (map Int.repr (intlist_to_Zlist b))) 0
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
forward.
entailer; apply prop_right; repeat split; try omega; eapply eval_var_isptr; eauto.

rewrite <- (array_at_ext tuint Tsh 
    (f_upto (ZnthV tuint (map swap b)) (Z.of_nat (S i)))
     (upd (f_upto (ZnthV tuint (map swap b)) (Z.of_nat i)) (Z.of_nat i)
             (Some (big_endian_integer
                 (fun z : Z =>
                  force_option Int.zero (ZnthV tuchar (map Int.repr (intlist_to_Zlist b))
                    (z + Z.of_nat i * 4))))))).

Focus 2.
intros.
unfold upd.
if_tac; try auto.
2: unfold f_upto; rewrite inj_S; if_tac; if_tac; auto; omega.
unfold f_upto.
rewrite if_true by (rewrite inj_S; omega).
unfold ZnthV. subst i0.
rewrite Nat2Z.id.
rewrite <- nth_big_endian_int by omega; reflexivity.
(* 1,506,948 1,110,852 *)
(* 1,506,948 1,134,576 *)
assert (isSome (ZnthV tuint K (Z.of_nat i))).
apply ZnthV_isSome.  
split; try omega. apply Z.lt_trans with 16%Z. omega. compute; auto.
clear H1.
forward.  (* Ki=K256[i]; *)
(* 1,689,280 1,212,872 *)
abstract (
assert (Zlength K = 64%Z) by reflexivity;
entailer!; try apply_ZnthV_isSome; try omega;
 eapply eval_var_isptr; eauto).
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
unfold Z.succ. rewrite inj_S.
go_lower0; cancel.
auto 50 with closed.
(* 1,811,028 1,429,048 *)
change (match b with
                | [] => []
                | a :: l => a :: firstn i l
                end) with (firstn (S i) b).
eapply semax_pre; [ | apply rearrange_regs_proof; auto ].
entailer!.
destruct data; inv Hdata; simpl; f_equal.
rewrite Int.add_assoc.
f_equal.
unfold Z.succ.
rewrite Z.mul_add_distr_r.
rewrite <- add_repr.
f_equal.
Qed.

Lemma local_and_retval: (* do we need this? *)
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
     semax  Delta_loop1
 (PROP ()
   LOCAL (`(eq (map Vint (rnd_64 regs K b))) 
                   (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
   SEP ( `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16))))
  block_data_order_loop2
  (normal_ret_assert
    (PROP () 
     LOCAL(`(eq (map Vint (rnd_64 regs K (rev (generate_word (rev b) 48)))))
                   (`cons (eval_id _a) (`cons (eval_id _b) (`cons (eval_id _c) (`cons (eval_id _d)
                     (`cons (eval_id _e) (`cons (eval_id _f) (`cons (eval_id _g) (`cons (eval_id _h) `nil)))))
))))
     SEP ( `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16))))).
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
   SEP  (`(array_at tuint Tsh (ZnthV tuint r_h) 0 (Zlength r_h) ctx)))
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
   SEP  (`(array_at tuint Tsh (ZnthV tuint r_h) 0 (Zlength r_h) ctx)))).
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

do 8 (forward; [ (entailer!; try apply_ZnthV_isSome; omega) | ]).
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
     semax  Delta_loop1
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
   (`(array_at tuint Tsh (ZnthV tuint (process_msg init_registers hashed)) 0
       (Zlength (process_msg init_registers hashed)) ctx)))
   (sequence add_them_back Sskip)
  (normal_ret_assert
   (PROP() LOCAL() 
    SEP (`(array_at tuint Tsh (ZnthV tuint 
                   (map2 Int.add (process_msg init_registers hashed)
                                         (rnd_64 r_h K (rev (generate_word (rev b) 48)))))
            0 (Zlength (process_msg init_registers hashed)) ctx)))).
Admitted.

(*
Lemma array_at_arrayof_:
  forall t sh f N N' v,
 N' = Z.of_nat N ->
 array_at t sh f 0 N' v |-- arrayof_ (mapsto_ sh t) t N v.
Proof.
intros.
Admitted.
*)

(*
Hint Extern 1 (array_at _ _ _ _ _ _ |-- arrayof_ _ _ _ _) =>
  (apply array_at_arrayof_; reflexivity) : cancel.
*)

Hint Extern 2 (array_at _ _ _ _ _ _ |-- array_at_ _ _ _ _ _) =>
  (apply array_at__array_at; clear; simpl; congruence) : cancel.
(* move the Hint to malloc_lemmas.v, 
  and change the name of array_at__array_at to array_at_array_at_
*)

Lemma elim_globals_only:
  forall Delta g i t rho,
  tc_environ Delta rho /\ (glob_types Delta) ! i = Some g ->
  eval_var i t (globals_only rho) = eval_var i t rho.
Admitted.


Lemma sha256_block_data_order_return:
forall (Espec : OracleKind) (hashed : list int) (delta : nat)
  (data0 : list Z) (b : list int) (ctx data : val) (r_h : list int)
  (r_Nl r_Nh : int) (r_data : list int) (r_num : int) (n : nat),
length b = LBLOCK ->
r_h = process_msg init_registers hashed ->
length (intlist_to_Zlist hashed) =
delta + Z.to_nat (Int.unsigned r_Nh * Int.modulus + Int.unsigned r_Nl) ->
data0 = map Int.unsigned (firstn (Z.to_nat (Int.unsigned r_num)) r_data) ->
length data0 < CBLOCK ->
length hashed = (16 * n)%nat ->
length r_data = CBLOCK ->
length r_h = 8 ->
isptr data ->
semax (initialized _t Delta_loop1)
  (PROP  ()
   LOCAL ()
   SEP 
   (`(array_at tuint Tsh
        (ZnthV tuint
           (map2 Int.add (process_msg init_registers hashed)
              (rnd_64 r_h K (rev (generate_word (rev b) 48))))) 0
        (Zlength (process_msg init_registers hashed)) ctx);
   `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
     (eval_var _K256 (tarray tuint 64));
   `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16));
   `(data_block (intlist_to_Zlist b) data);
   `(field_mapsto Tsh t_struct_SHA256state_st _Nl ctx (Vint r_Nl));
   `(field_mapsto Tsh t_struct_SHA256state_st _Nh ctx (Vint r_Nh));
   `(array_at tuchar Tsh (ZnthV tuchar r_data) 0 (Zlength r_data)
       (offset_val (Int.repr 40) ctx));
   `(field_mapsto Tsh t_struct_SHA256state_st _num ctx (Vint r_num))))
  (Sreturn None)
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (`(sha256state_ (process_block_abs b (S256abs hashed delta data0))
             ctx) * `(data_block (intlist_to_Zlist b) data) *
         `(array_at tuint Tsh (ZnthV tuint K) 0 (Zlength K))
           (eval_var _K256 (tarray tuint 64))))
     (stackframe_of f_sha256_block_data_order)).
Proof.
intros.
forward. (* return; *)
unfold frame_ret_assert; simpl.
unfold sha256state_.
set (regs := map2 Int.add (process_msg init_registers hashed)
        (rnd_64 (process_msg init_registers hashed) K
           (rev (generate_word (rev b) 48)))).
repeat rewrite exp_sepcon1.
apply exp_right with (regs, (r_Nl, (r_Nh, (r_data, r_num)))).
simpl_typed_mapsto.
unfold s256_relate, s256_h, s256_Nh, s256_Nl, s256_data, s256_num.
unfold fst,snd.
entailer!.
* 
apply process_msg_block; eauto.
* 
rewrite length_intlist_to_Zlist.
rewrite app_length.
rewrite H.
rewrite length_intlist_to_Zlist in *.
change CBLOCK with 64%nat.
change LBLOCK with 16%nat.
rewrite mult_plus_distr_l.
change (4*16)%nat with 64%nat.
omega.
*
exists (S n). rewrite app_length. rewrite H4, H.
change LBLOCK with 16%nat.
transitivity (16 * n + 16 * 1)%nat; [reflexivity | ].
rewrite <- mult_plus_distr_l.
rewrite plus_comm. reflexivity.
*
assert (Lregs: length regs = 8%nat)
  by (subst; apply length_map2_add_rnd_64; auto).
rewrite Zlength_correct; rewrite length_process_msg.
rewrite (Zlength_correct regs); rewrite Lregs.
simpl Z.of_nat.
unfold stackframe_of; simpl.
rewrite var_block_typed_mapsto_.
normalize. simpl_typed_mapsto.
change (Pos.to_nat 16) with 16%nat.
unfold id.
erewrite elim_globals_only
  by (split; [eassumption | reflexivity]).
apply andp_right; [ | cancel].
apply prop_right; compute; congruence.
Qed.

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
do 2 match goal with |- appcontext [lift1 ?A] => 
  change (lift1 A) with (`A)
end.
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

simpl.
do 2 match goal with |- appcontext [lift1 ?A] => 
  change (lift1 A) with (`A)
end.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
eapply sha256_block_data_order_return; eauto.
Qed.










