Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Local Open Scope logic.

Definition swap (i: int) : int :=
 Int.or (Int.shl (Int.and i (Int.repr 255)) (Int.repr 24))
   (Int.or (Int.shl (Int.and (Rt 8 i) (Int.repr 255)) (Int.repr 16))
      (Int.or (Int.shl (Int.and (Rt 16 i) (Int.repr 255)) (Int.repr 8))
         (Rt 24 i))).

Definition big_endian_integer (contents: Z -> int) : int :=
  Int.or (Int.shl (contents 3) (Int.repr 24))
  (Int.or (Int.shl (contents 2) (Int.repr 16))
   (Int.or (Int.shl (contents 1) (Int.repr 8))
      (contents 0))).

Definition LBLOCK : nat := 16%nat.   (* length of a block, in 32-bit integers *)
Definition CBLOCK : nat := (LBLOCK * 4)%nat.  (* length of a block, in characters *)

Global Opaque LBLOCK.  (* so that LBLOCK-i  does not inappropriately simplify *)

Definition s256state := (list val * (val * (val * (list val * val))))%type.
Definition s256_h (s: s256state) := fst s.
Definition s256_Nl (s: s256state) := fst (snd s).
Definition s256_Nh (s: s256state) := fst (snd (snd s)).
Definition s256_data (s: s256state) := fst (snd (snd (snd s))).
Definition s256_num (s: s256state) := snd (snd (snd (snd s))).
Arguments s256_h  !s.
Arguments s256_Nl  !s.
Arguments s256_Nh  !s.
Arguments s256_data  !s.
Arguments s256_num  !s.
Arguments fst _ _ !p.
Arguments snd _ _ !p.

Inductive s256abs :=  (* SHA-256 abstract state *)
 S256abs: forall (hashed: list int)   (* words hashed, so far *)
                         (data: list Z)  (* bytes in the partial block not yet hashed *),
                     s256abs.

Definition s256a_regs (a: s256abs) : list int :=
 match a with S256abs hashed _  => 
          process_msg init_registers hashed 
 end.

Definition s256a_len (a: s256abs) := 
  match a with S256abs hashed data => Zlength hashed end.

Definition hilo hi lo := (Int.unsigned hi * Int.modulus + Int.unsigned lo)%Z.

Definition s256_relate (a: s256abs) (r: s256state) : Prop :=
     match a with S256abs hashed data =>
         s256_h r = map Vint (process_msg init_registers hashed) 
       /\ (exists hi, exists lo, s256_Nh r = Vint hi /\ s256_Nl r = Vint lo /\
             Zlength hashed * 4 + Zlength data = hilo hi lo)%Z
       /\ (exists dd, data = map Int.unsigned dd /\ s256_data r = map Vint dd)
       /\ length data < CBLOCK
       /\ NPeano.divide LBLOCK (length hashed)
       /\ s256_num r = Vint (Int.repr (Zlength data))
     end%nat.

Definition init_s256abs : s256abs := S256abs nil nil.

Definition sha_finish (a: s256abs) : list Z :=
 match a with
 | S256abs hashed data => 
     SHA_256 (intlist_to_Zlist (map swap hashed) ++ data)
 end.

Definition cVint (f: Z -> int) (i: Z) := Vint (f i).

Goal forall c r,  data_at Tsh t_struct_SHA256state_st r c = TT.
 intros.
 simpl in r.
 simpl_data_at.
 destruct r as [r_h [r_Nl [r_Nh [r_data r_num]]]].
 simpl.
Abort.

Definition sha256_length (len: Z)  (c: val) : mpred :=
   EX lo:int, EX hi:int, 
     !! (hilo hi lo = len) &&
     (field_at Tsh t_struct_SHA256state_st _Nl (Vint lo) c *
      field_at Tsh t_struct_SHA256state_st _Nh (Vint hi) c).

Definition sha256state_ (a: s256abs) (c: val) : mpred :=
   EX r:s256state, 
    !!  s256_relate a r  &&  data_at Tsh t_struct_SHA256state_st r c.

Definition tuints (vl: list int) := ZnthV tuint (map Vint vl).
Definition tuchars (vl: list int) :=  ZnthV tuchar (map Vint vl).

Definition data_block (sh: share) (contents: list Z) :=
  array_at tuchar sh (tuchars (map Int.repr contents)) 0 (Zlength contents).

Definition __builtin_read32_reversed_spec :=
 DECLARE ___builtin_read32_reversed
  WITH p: val, sh: share, contents: Z -> int
  PRE [ 1%positive OF tptr tuint ] 
        PROP() LOCAL (`(eq p) (eval_id 1%positive))
        SEP (`(array_at tuchar sh (cVint contents) 0 4 p))
  POST [ tuint ] 
     local (`(eq (Vint (big_endian_integer contents))) retval) &&
     `(array_at tuchar sh (cVint contents) 0 4 p).

Definition __builtin_write32_reversed_spec :=
 DECLARE ___builtin_write32_reversed
  WITH p: val, sh: share, contents: Z -> int
  PRE [ 1%positive OF tptr tuint, 2%positive OF tuint ] 
        PROP(writable_share sh)
        LOCAL (`(eq p) (eval_id 1%positive);
                     `(eq (Vint(big_endian_integer contents))) (eval_id 2%positive))
        SEP (`(memory_block sh (Int.repr 4) p))
  POST [ tvoid ] 
     `(array_at tuchar sh (cVint contents) 0 4 p).

Definition memcpy_spec :=
  DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, n: Z, contents: Z -> int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (writable_share (snd sh))
       LOCAL (`(eq p) (eval_id 1%positive); `(eq q) (eval_id 2%positive);
                    `(eq n) (`Int.unsigned (`force_int (eval_id 3%positive))))
       SEP (`(array_at tuchar (fst sh) (cVint contents) 0 n q);
              `(memory_block (snd sh) (Int.repr n) p))
    POST [ tptr tvoid ]
         local (`(eq p) retval) &&
       (`(array_at tuchar (fst sh) (cVint contents) 0 n q) *
        `(array_at tuchar (snd sh) (cVint contents) 0 n p)).

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
       (`(array_at tuchar sh (fun _ => Vint c) 0 n p)).

Definition K_vector : environ -> mpred :=
  `(array_at tuint Tsh (tuints K) 0 (Zlength K)) (eval_var _K256 (tarray tuint 64)).

Lemma K_vector_closed:
  forall S, closed_wrt_vars S K_vector.
Proof. unfold K_vector; auto with closed. Qed.
Hint Resolve K_vector_closed : closed.

Definition sha256_block_data_order_spec :=
  DECLARE _sha256_block_data_order
    WITH hashed: list int, b: list int, ctx : val, data: val, sh: share
   PRE [ _ctx OF tptr t_struct_SHA256state_st, _in OF tptr tvoid ]
         PROP(length b = LBLOCK; NPeano.divide LBLOCK (length hashed)) 
         LOCAL (`(eq ctx) (eval_id _ctx); `(eq data) (eval_id _in))
         SEP (`(array_at tuint Tsh  (tuints (process_msg init_registers hashed)) 0 8 ctx);
                `(data_block sh (intlist_to_Zlist (map swap b)) data);
                 K_vector)
   POST [ tvoid ]
          (`(array_at tuint Tsh  (tuints (process_msg init_registers (hashed++b))) 0 8 ctx) *
          `(data_block sh (intlist_to_Zlist (map swap b)) data) *
          K_vector).
 
Definition SHA256_addlength_spec :=
 DECLARE _SHA256_addlength
 WITH len : nat, c: val, n: Z
 PRE [ _c OF tptr t_struct_SHA256state_st , _len OF tuint ]
   PROP ( ) 
   LOCAL (`(eq (Z.of_nat len)) (`Int.unsigned (`force_int (eval_id _len))); 
               `(eq c) (eval_id _c))
   SEP (`(sha256_length n c))
 POST [ tvoid ]
   `(sha256_length (n+Z.of_nat len) c).

Definition SHA256_Init_spec :=
  DECLARE _SHA256_Init
   WITH c : val 
   PRE [ _c OF tptr t_struct_SHA256state_st ]
         PROP () LOCAL (`(eq c) (eval_id _c))
         SEP(`(data_at_ Tsh t_struct_SHA256state_st c))
  POST [ tvoid ] 
          (`(sha256state_ init_s256abs c)).

Inductive update_abs: list Z -> s256abs -> s256abs -> Prop :=
 Update_abs:
   (forall msg hashed blocks oldfrag newfrag,
        length oldfrag < CBLOCK ->
        length newfrag < CBLOCK ->
       NPeano.divide LBLOCK (length hashed) ->
       NPeano.divide LBLOCK (length blocks) -> 
       oldfrag++msg = intlist_to_Zlist (map swap blocks) ++ newfrag ->
   update_abs msg (S256abs hashed oldfrag) 
                              (S256abs (hashed++blocks) newfrag))%nat.

Definition BOUND : Z := (Int64.modulus - Int.modulus)%Z.
Opaque BOUND.

Definition SHA256_Update_spec :=
  DECLARE _SHA256_Update
   WITH a: s256abs, data: list Z, c : val, d: val, sh: share, len : nat
   PRE [ _c OF tptr t_struct_SHA256state_st, _data_ OF tptr tvoid, _len OF tuint ]
         PROP ((len <= length data)%nat; (s256a_len a < BOUND)%Z)
         LOCAL (`(eq c) (eval_id _c); `(eq d) (eval_id _data_); 
                                  `(eq (Z.of_nat len)) (`Int.unsigned (`force_int (eval_id _len))))
         SEP(K_vector; `(sha256state_ a c); `(data_block sh data d))
  POST [ tvoid ] 
         EX a':_, 
          PROP (update_abs (firstn len data) a a') LOCAL ()
          SEP(K_vector; `(sha256state_ a' c); `(data_block sh data d)).

Definition SHA256_Final_spec :=
  DECLARE _SHA256_Final
   WITH a: s256abs, md: val, c : val,  shmd: share, sh: share
   PRE [ _md OF tptr tuchar, _c OF tptr t_struct_SHA256state_st ]
         PROP (writable_share shmd) 
         LOCAL (`(eq md) (eval_id _md); `(eq c) (eval_id _c))
         SEP(K_vector; `(sha256state_ a c);
               `(memory_block shmd (Int.repr 32) md))
  POST [ tvoid ] 
         PROP () LOCAL ()
         SEP(K_vector; `(data_at_ Tsh t_struct_SHA256state_st c);
               `(data_block shmd (sha_finish a) md)).

Definition SHA256_spec :=
  DECLARE _SHA256
   WITH d: val, len: Z, dsh: share, msh: share, data: list Z, md: val
   PRE [ _d OF tptr tuchar, _n OF tuint, _md OF tptr tuchar ]
         PROP (writable_share msh) 
         LOCAL (`(eq d) (eval_id _data_);
                     `(eq (Z.of_nat (length data))) (`Int.unsigned (`force_int (eval_id _n)));
                     `(eq md) (eval_id _md))
         SEP(K_vector; `(data_block dsh data d); `(memory_block msh (Int.repr 32) md))
  POST [ tvoid ] 
         SEP(K_vector; `(data_block dsh data d); `(data_block msh (SHA_256 data) md)).

Definition Vprog : varspecs := (_K256, tarray tuint 64)::nil.

Definition Gprog : funspecs := 
  __builtin_read32_reversed_spec::
  __builtin_write32_reversed_spec::
  memcpy_spec:: memset_spec::
  sha256_block_data_order_spec:: SHA256_Init_spec::
  SHA256_addlength_spec::
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

Ltac simpl_stackframe_of := 
  unfold stackframe_of, fn_vars; simpl map; unfold fold_right; rewrite sepcon_emp;
  repeat rewrite var_block_data_at_ by reflexivity. 

Fixpoint loops (s: statement) : list statement :=
 match s with 
  | Ssequence a b => loops a ++ loops b
  | Sloop _ _ => [s]
  | Sifthenelse _ a b => loops a ++ loops b
  | _ => nil
  end.

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






