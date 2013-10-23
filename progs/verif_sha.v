Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Local Open Scope logic.

Set Printing Depth 10.

Definition big_endian_integer (contents: Z -> int) : int :=
  Int.or (Int.shl (contents 3) (Int.repr 24))
  (Int.or (Int.shl (contents 2) (Int.repr 16))
   (Int.or (Int.shl (contents 1) (Int.repr 8))
      (contents 0))).

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

Definition LBLOCK : Z := 16.   (* length of a block, in 32-bit integers *)
Definition CBLOCK : Z := (LBLOCK * 4)%Z.  (* length of a block, in characters *)

Goal forall c r,  typed_mapsto Tsh t_struct_SHA256state_st c r = TT.
 intros.
 simpl in r.
 simpl_typed_mapsto.
 destruct r as [r_h [r_Nl [r_Nh [r_data r_num]]]].
 simpl.
Abort.

Definition s256state := (list int * (int * (int * (list int * int))))%type.
Definition s256_h (s: s256state) := fst s.
Definition s256_Nl (s: s256state) := fst (snd s).
Definition s256_Nh (s: s256state) := fst (snd (snd s)).
Definition s256_data (s: s256state) := fst (snd (snd (snd s))).
Definition s256_num (s: s256state) := snd (snd (snd (snd s))).

Inductive s256abs :=  (* SHA-256 abstract state *)
 S256abs: forall (hashed: list int)   (* words hashed, so far *)
                         (delta: Z) (* length of "hashed" minus the recorded length in hl *)
                         (data: list Z)  (* bytes in the partial block not yet hashed *)
                     (range:  0 <= Zlength data < CBLOCK),
                     s256abs.

Definition s256_relate (a: s256abs) (r: s256state) : Prop :=
     match a with S256abs hashed delta data _ =>
         s256_h r = process_msg init_registers hashed 
       /\ Zlength (intlist_to_Zlist hashed) = 
             delta + (Int.unsigned (s256_Nh r) * Int.modulus + Int.unsigned (s256_Nl r))
       /\ data = map Int.unsigned (firstn (Z.to_nat (Int.unsigned (s256_num r))) (s256_data r))
       /\ Zlength (s256_data r) = CBLOCK
     end.

Definition sha256state_ (a: s256abs) (c: val) : mpred :=
   EX r:s256state, 
    !!  s256_relate a r  &&  typed_mapsto Tsh t_struct_SHA256state_st c r.

Definition data_block (contents: list Z) (v: val) :=
  array_at tuchar Tsh (@ZnthV tuchar (map Int.repr contents)) 0 (Zlength contents) v.

Lemma Zlength_process_block:
  forall r b, Zlength (process_block r b) = 8.
Proof.
 intros. unfold process_block.
Admitted.

Definition process_block_abs (b: list int) (a: s256abs) : s256abs :=
match a with
| S256abs hashed delta data range =>
    S256abs (hashed++b) (delta+CBLOCK) data range
end.

Definition sha256_block_data_order_spec :=
  DECLARE _sha256_block_data_order
    WITH a: s256abs, b: list int, ctx : val, data: val, sh: share
   PRE [ _ctx OF tptr t_struct_SHA256state_st, _in OF tptr tvoid ]
         PROP(Zlength b = LBLOCK) 
         LOCAL (`(eq ctx) (eval_id _ctx); `(eq data) (eval_id _in))
         SEP (`(sha256state_ a ctx); `(data_block (intlist_to_Zlist b) data);
                `(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K)) (eval_var _K256 (tarray tuint 64)))
   POST [ tvoid ]
          (`(sha256state_ (process_block_abs b a) ctx) *
            `(data_block (intlist_to_Zlist b) data)).

Definition init_s256abs : s256abs.
 apply (S256abs nil 0 nil).
 simpl; split; reflexivity.
Defined.

Definition addlength_rel (n: Z) (a: s256abs) : s256abs :=
 match a with S256abs hashed delta data range =>
     S256abs hashed (delta-n) data range
 end.
                                  
Definition SHA256_addlength_spec :=
 DECLARE _SHA256_addlength
 WITH len : Z, a: s256abs, c: val
 PRE [ _c OF tptr t_struct_SHA256state_st , _len OF tuint ]
   PROP ( ) 
   LOCAL (`(eq len) (`Int.unsigned (`force_int (eval_id _len))); `(eq c) (eval_id _c))
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

Lemma zero_le_Zlength: forall A (l: list A), 0 <= Zlength l.
Proof.
intros. rewrite Zlength_correct. omega.
Qed.

Lemma grab_and_process_block_length:
 forall n r firstr msg r' m',
    Zlength msg >= Z_of_nat n ->
    grab_and_process_block n r firstr msg  = (r',m') ->
    Zlength r' = 8.
Proof.
 induction n; intros.
 inv H0.
 apply Zlength_process_block.
 rewrite Zlength_correct in H.
 apply Nat2Z.inj_ge in H.
 destruct msg.
 inv H.
 simpl in H.
 apply IHn in H0; auto.
 rewrite Zlength_correct; apply Nat2Z.inj_ge.
 omega.
Qed.

Inductive update_abs: forall (msg: list Z) (a a': s256abs), Prop :=
| UA_short: forall msg hashed data range
         (H: Zlength (data++msg) < CBLOCK),
         update_abs msg 
           (S256abs hashed 0 data range)
           (S256abs hashed 0 (data++msg) (conj (zero_le_Zlength _ _) H))
| UA_long: forall (msg newblock: list Z) (b: list int) hashed data (msg': list Z) 
                      range range' a'',
        newblock = firstn (Z.to_nat CBLOCK) (data++msg) ->
        intlist_to_Zlist b = newblock ->
        newblock ++ msg' = data ++ msg ->
        update_abs msg' (S256abs (hashed++b) 0 nil range')   a'' ->
        update_abs msg (S256abs hashed 0 data range) a''.

Definition SHA256_Update_spec :=
  DECLARE _SHA256_Update
   WITH a: s256abs, data: list Z, c : val, d: val, sh: share, len : Z
   PRE [ _c OF tptr t_struct_SHA256state_st, _data_ OF tptr tvoid, _len OF tuint ]
         PROP (len <= Zlength data)
         LOCAL (`(eq c) (eval_id _c); `(eq d) (eval_id _data_); 
                                  `(eq len) (`Int.unsigned (`force_int (eval_id _len))))
         SEP(`(sha256state_ a c); `(data_block data d))
  POST [ tvoid ] 
         EX a':_, 
          PROP (update_abs data a a') LOCAL ()
          SEP(`(sha256state_ a' c); `(data_block data d)).

Definition s256a_regs (a: s256abs) : list int :=
 match a with S256abs hashed _ _ _  => 
          process_msg init_registers hashed 
 end.

Definition sha_finish (a a': s256abs) :=
 match a, a' with
 | S256abs hashed delta data range,
   S256abs hashed' delta' data' range' =>
     hashed' = generate_and_pad (intlist_to_Zlist hashed ++ data) 0
  /\ data'=nil /\ delta=0 /\ delta'=0
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
                     `(eq (Zlength data)) (`Int.unsigned (`force_int (eval_id _n)));
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

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.

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

Lemma lift2more {A}{B}{T}:
  forall (v :A) (v': B) (F: A -> B -> T),
   @liftx (LiftEnviron T) (F v v') = 
     @liftx (Tarrow A (Tarrow B (LiftEnviron T))) F `v `v'.
Proof. reflexivity. Qed.

Lemma lift1more {A}{T}:
  forall (v :A) (F: A -> T),
   @liftx (LiftEnviron T) (F v) = 
     @liftx (Tarrow A (LiftEnviron T)) F `v.
Proof. reflexivity. Qed.

Ltac simpl_stackframe_of := 
  unfold stackframe_of, fn_vars; simpl map; unfold fold_right; rewrite sepcon_emp;
  repeat rewrite var_block_typed_mapsto_. 

Lemma ditch_SEP: forall P Q R S,
   PROPx P (LOCALx Q (SEPx (TT::nil))) |-- S ->
     PROPx P (LOCALx Q (SEPx R)) |-- S.
Proof.
intros.
eapply derives_trans; [| apply H]; clear H.
go_lowerx.
normalize.
Qed.

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

Lemma Zlength_process_msg:
  forall b, Zlength (process_msg init_registers b) = 8.
Proof.
 intros.
Admitted.

Fixpoint eval_ids (ids: list ident) : environ -> list val :=
  match ids with
  |  id::ids' => `cons (eval_id id) (eval_ids ids')
  | nil => `nil
 end.
  
Lemma sha256_block_data_order_loop1_proof:
  forall (Espec : OracleKind)
     (b: list int) (data: val) (regs: list int),
     Zlength b = LBLOCK ->
     semax (initialized _i
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
   LOCAL (`(eq (map Vint regs)) (eval_ids [_a,_b,_c,_d,_e,_f,_g,_h]))
   SEP ( `(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(arrayof_ (mapsto_ Tsh tuint) tuint 16) (eval_var _X (tarray tuint 16));
           `(data_block (intlist_to_Zlist b) data)))
  block_data_order_loop1
  (normal_ret_assert
    (PROP () 
     LOCAL(`(eq (map Vint (rnd_64 regs K (rev b)))) (eval_ids [_a,_b,_c,_d,_e,_f,_g,_h]))
     SEP ( `(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(array_at tuint Tsh (@ZnthV tuint b) 0 16) (eval_var _X (tarray tuint 16));
           `(data_block (intlist_to_Zlist b) data))) ).
Admitted.
Lemma sha256_block_data_order_loop2_proof:
  forall (Espec : OracleKind)
     (b: list int) (data: val) (regs: list int),
     Zlength b = LBLOCK ->
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
   LOCAL (`(eq (map Vint (rnd_64 regs K (rev b)))) (eval_ids [_a,_b,_c,_d,_e,_f,_g,_h]))
   SEP ( `(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(arrayof_ (mapsto_ Tsh tuint) tuint 16) (eval_var _X (tarray tuint 16))))
  block_data_order_loop2
  (normal_ret_assert
    (PROP () 
     LOCAL(`(eq (map Vint (rnd_64 regs K (rev (generate_word b 48))))) (eval_ids [_a,_b,_c,_d,_e,_f,_g,_h]))
     SEP ( `(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))
                   (eval_expr (Evar _K256 (tarray tuint 64)));
           `(arrayof_ (mapsto_ Tsh tuint) tuint 16) (eval_var _X (tarray tuint 16))))).
Admitted.

Lemma semax_seq_congr:
 forall (Espec: OracleKind) s1 s1' s2 s2',
  (forall Delta P R, semax Delta P s1 R <-> semax Delta P s1' R) ->
  (forall Delta P R, semax Delta P s2 R <-> semax Delta P s2' R) ->
 (forall Delta P R, 
    semax Delta P (Ssequence s1 s2) R <->
    semax Delta P (Ssequence s1' s2') R).
Admitted.

Lemma seq_assoc8:  
  forall {Espec: OracleKind},
   forall Delta P s1 s2 s3 s4 s5 s6 s7 s8 s9 R,
        @semax Espec Delta P 
     (Ssequence s1 (Ssequence s2 (Ssequence s3 (Ssequence s4
      (Ssequence s5 (Ssequence s6 (Ssequence s7 (Ssequence s8 s9))))))))
        R <->
        @semax Espec Delta P 
     (Ssequence 
        (Ssequence s1 (Ssequence s2 (Ssequence s3 (Ssequence s4
         (Ssequence s5 (Ssequence s6 (Ssequence s7 s8))))))) s9)
        R.
Proof.
intros.
repeat (rewrite <- seq_assoc; apply semax_seq_congr; intros; [apply iff_refl | ]).
apply iff_refl.
Qed.

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
     (b: list int) (data: val) (r_h: list int) (r_data: list int)
        (ctx: val) (r_num r_Nl r_Nh : int) (hashed : list int) 
   (delta: Z)(data0: list Z)
(*  (range : 0 <= Zlength data0 < CBLOCK)
  (H :     Zlength b = LBLOCK)
  (H0 : sizeof (tarray tuint 16) <= Int.max_unsigned)
  (H1 : r_h = process_msg init_registers hashed)
*)  (H2 : Zlength (intlist_to_Zlist hashed) =
     delta + (Int.unsigned r_Nh * Int.modulus + Int.unsigned r_Nl))
  (H3 : data0 = map Int.unsigned (firstn (Z.to_nat (Int.unsigned r_num)) r_data))
  (H4 : Zlength r_data = CBLOCK)
   (H5 : Zlength r_h = 8),
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
          (load8 _h 7))))))))
  (normal_ret_assert 
  (PROP  ()
   LOCAL  (`(eq (Vint (@ZnthV tuint r_h 7))) (eval_id _h);
                `(eq (Vint (@ZnthV tuint r_h 6))) (eval_id _g);
                `(eq (Vint (@ZnthV tuint r_h 5))) (eval_id _f);
                `(eq (Vint (@ZnthV tuint r_h 4))) (eval_id _e);
                `(eq (Vint (@ZnthV tuint r_h 3))) (eval_id _d);
                `(eq (Vint (@ZnthV tuint r_h 2))) (eval_id _c);
                `(eq (Vint (@ZnthV tuint r_h 1))) (eval_id _b);
                `(eq (Vint (@ZnthV tuint r_h 0))) (eval_id _a);
   `eq (eval_id _data) (eval_expr (Etempvar _in (tptr tvoid)));
   `(eq ctx) (eval_id _ctx); `(eq data) (eval_id _in))
   SEP  (`(array_at tuint Tsh (@ZnthV tuint r_h) 0 (Zlength r_h) ctx)))).
Proof.
intros.
normalize.
simpl.
normalize.
unfold load8.
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
forward; [entailer! ;  omega | ]. (* a = ctx->h[0]; *)
forward; [entailer! ;  omega | ]. (* b = ctx->h[1]; *)
forward; [entailer! ;  omega | ]. (* c = ctx->h[2]; *)
forward; [entailer! ;  omega | ]. (* d = ctx->h[3]; *)
forward; [entailer! ;  omega | ]. (* e = ctx->h[4]; *)
forward; [entailer! ;  omega | ]. (* f = ctx->h[5]; *)
forward; [entailer! ;  omega | ]. (* g = ctx->h[6]; *)
(* NOTE: the next line exhibits a bug in the forward tactic;
  it can't handle a load if it's the last command in a sequence. *)
(* forward; [entailer! ;  omega | ]. (* h = ctx->h[7]; *) *)
Admitted.


Lemma array_at_arrayof_:
  forall t sh f N N' v,
 N' = Z.of_nat N ->
 array_at t sh f 0 N' v |-- arrayof_ (mapsto_ sh t) t N v.
Admitted.

Hint Extern 1 (array_at _ _ _ _ _ _ |-- arrayof_ _ _ _ _) =>
  (apply array_at_arrayof_; reflexivity) : cancel.

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
destruct H1 as [? [? [? ?]]].
assert (Zlength r_h = 8) by (subst r_h; apply Zlength_process_msg).
forward. (* data = in; *)

(**** BEGIN   the eight load-from-array-h[] commands.
  Ideally, we'd just do it with these commands:
forward; [entailer! ;  omega | ]. (* a = ctx->h[0]; *)
forward; [entailer! ;  omega | ]. (* b = ctx->h[1]; *)
forward; [entailer! ;  omega | ]. (* c = ctx->h[2]; *)
forward; [entailer! ;  omega | ]. (* d = ctx->h[3]; *)
forward; [entailer! ;  omega | ]. (* e = ctx->h[4]; *)
forward; [entailer! ;  omega | ]. (* f = ctx->h[5]; *)
forward; [entailer! ;  omega | ]. (* g = ctx->h[6]; *)
forward; [entailer! ;  omega | ]. (* h = ctx->h[7]; *)
but they use an extra gigabyte of memory and blow up Coq.
So instead we use the Lemma sha256_block_load8,
 as follows.
*)

apply seq_assoc8.
eapply semax_seq'; 
  [ eapply semax_pre; 
     [ | apply semax_frame_PQR with (R2:= [
   `(field_mapsto Tsh t_struct_SHA256state_st _Nl ctx (Vint r_Nl)),
   `(field_mapsto Tsh t_struct_SHA256state_st _Nh ctx (Vint r_Nh)),
   `(array_at tuchar Tsh (@ZnthV tuint r_data) 0 (Zlength r_data)
       (offset_val (Int.repr 40) ctx)),
   `(field_mapsto Tsh t_struct_SHA256state_st _num ctx (Vint r_num)),
   `(arrayof_ (mapsto_ Tsh tuint) tuint (Pos.to_nat 16))
     (eval_var _X (tarray tuint 16)),
   `(data_block (intlist_to_Zlist b) data),
   `(array_at tuint Tsh (@ZnthV tuint K) 0 (Zlength K))
     (eval_var _K256 (tarray tuint 64))]);
      [unfold closed_wrt_modvars; solve [auto 50 with closed] |
      eapply sha256_block_load8 with (ctx:=ctx); eassumption
   ]]
  | ]; [ solve [entailer] | ].
abbreviate_semax.
unfold app.
(**** END   the eight load-from-array-h[] commands. *)

forward.  (* i = 0; *)

eapply semax_seq'; 
  [ eapply semax_pre; 
     [ | apply semax_frame_PQR with (R2:= 
            [`(array_at tuint Tsh (@ZnthV tuint r_h) 0 (Zlength r_h) ctx),
   `(field_mapsto Tsh t_struct_SHA256state_st _Nl ctx (Vint r_Nl)),
   `(field_mapsto Tsh t_struct_SHA256state_st _Nh ctx (Vint r_Nh)),
   `(array_at tuchar Tsh (@ZnthV tuint r_data) 0 (Zlength r_data)
       (offset_val (Int.repr 40) ctx)),
   `(field_mapsto Tsh t_struct_SHA256state_st _num ctx (Vint r_num))]); 
      [unfold closed_wrt_modvars; solve [auto 50 with closed] |
     apply sha256_block_data_order_loop1_proof
              with (regs:=r_h)(b:=b)(data:=data); eassumption 
   ]]
  | ].

entailer.
apply andp_right.
apply prop_right; clear - H5.
forget (process_msg init_registers hashed) as r.
do 9 (destruct r as [ | ?h r ] ; [inv H5 | ]).
reflexivity.
repeat rewrite Zlength_cons in H5.
rewrite Zlength_correct in H5.
pose proof (seplog.Z_of_nat_ge_O (length r)).
omega.
cancel.
unfold app.
abbreviate_semax.

eapply semax_seq'; 
  [ eapply semax_pre; 
     [ | apply semax_frame_PQR with (R2:= 
            [
   `(data_block (intlist_to_Zlist b) data),
   `(array_at tuint Tsh (@ZnthV tuint r_h) 0 (Zlength r_h) ctx),
   `(field_mapsto Tsh t_struct_SHA256state_st _Nl ctx (Vint r_Nl)),
   `(field_mapsto Tsh t_struct_SHA256state_st _Nh ctx (Vint r_Nh)),
   `(array_at tuchar Tsh (@ZnthV tuint r_data) 0 (Zlength r_data)
       (offset_val (Int.repr 40) ctx)),
   `(field_mapsto Tsh t_struct_SHA256state_st _num ctx (Vint r_num))]); 
      [unfold closed_wrt_modvars; solve [auto 50 with closed] |
     apply sha256_block_data_order_loop2_proof
              with (regs:=r_h)(b:=b); eassumption 
   ]]
  | ].
unfold app.

Focus 1.

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
    fold_right  (* should really make a special version of fold_right *)
   ] beta iota.

Ltac go_lower0 := 
intros ?rho;
 try (simple apply grab_tc_environ; intro);
 repeat (progress unfold_for_go_lower;
      simpl andp; simpl prop; simpl sepcon; simpl emp; simpl orp; cbv beta iota).

Ltac go_lower :=
 go_lower0;
 autorewrite with go_lower;
 repeat findvar;
 simpl;
 autorewrite with go_lower.

unfold eval_ids.
go_lower0.
autorewrite with go_lower.
repeat findvar.
entailer. cancel.
abbreviate_semax.




(* . . . and so on *)

Admitted.






(*
Ltac ff := 
match goal with Delta := context [initialized ?i (@pair ?u ?v ?w ?x)] |- _ =>
 let D := fresh "D" in
  set (D := initialized i (@pair u v w x)) in Delta;
  cbv delta [initialized] in D; simpl in D;
  unfold D in *; clear D
end.
*)










