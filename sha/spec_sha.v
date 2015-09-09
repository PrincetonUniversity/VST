Require Import floyd.proofauto.
Import ListNotations.
Require Import sha.sha.
Require Import general_lemmas.
Require Import sha.SHA256.
Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.  
Open Scope logic.

Definition s256state := (list val * (val * (val * (list val * val))))%type.
Definition s256_h (s: s256state) := fst s.
Definition s256_Nl (s: s256state) := fst (snd s).
Definition s256_Nh (s: s256state) := fst (snd (snd s)).
Definition s256_data (s: s256state) := fst (snd (snd (snd s))).
Definition s256_num (s: s256state) := snd (snd (snd (snd s))).

Inductive s256abs :=  (* SHA-256 abstract state *)
 S256abs: forall (hashed: list int)   (* words hashed, so far *)
                         (data: list Z)  (* bytes in the partial block not yet hashed *),
                     s256abs.

Definition s256a_regs (a: s256abs) : list int :=
 match a with S256abs hashed data  => 
          hash_blocks init_registers hashed 
 end.

Definition bitlength (hashed: list int) (data: list Z) := 
     ((Zlength hashed * WORD + Zlength data) * 8)%Z. 

Definition s256a_len (a: s256abs) : Z := 
  match a with S256abs hashed data => bitlength hashed data  end.

Definition s256_relate (a: s256abs) (r: s256state) : Prop :=
     match a with S256abs hashed data =>
         s256_h r = map Vint (hash_blocks init_registers hashed) 
       /\ (s256_Nh r = Vint (hi_part (bitlength hashed data)) /\
            s256_Nl r = Vint (lo_part (bitlength hashed data)))
       /\ s256_data r = map Vint (map Int.repr data)
       /\ (Zlength data < CBLOCKz /\ Forall isbyteZ data)
       /\ (LBLOCKz | Zlength hashed)
       /\ s256_num r = Vint (Int.repr (Zlength data))
     end.

Definition init_s256abs : s256abs := S256abs nil nil.

Definition sha_finish (a: s256abs) : list Z :=
 match a with
 | S256abs hashed data => 
     SHA_256 (intlist_to_Zlist hashed ++ data)
 end.

Definition cVint (f: Z -> int) (i: Z) := Vint (f i).

Definition t_struct_SHA256state_st := Tstruct _SHA256state_st noattr.

Definition sha256state_ (a: s256abs) (c: val) : mpred :=
   EX r:s256state, 
    !!  s256_relate a r  &&  data_at Tsh t_struct_SHA256state_st r c.

Definition data_block (sh: share) (contents: list Z) :=
  !! Forall isbyteZ contents &&
  data_at sh (tarray tuchar (Zlength contents)) (map Vint (map Int.repr contents)).

Definition _ptr : ident := 81%positive.
Definition _x : ident := 82%positive.

Definition __builtin_read32_reversed_spec :=
 DECLARE ___builtin_read32_reversed
  WITH p: val, sh: share, contents: list int
  PRE [ _ptr OF tptr tuint ] 
        PROP  (Zlength contents >= 4)
        LOCAL (temp _ptr p)
        SEP   (`(data_at sh (tarray tuchar 4) (map Vint contents) p))
  POST [ tuint ] 
     PROP() LOCAL (temp ret_temp  (Vint (big_endian_integer contents)))
     SEP (`(data_at sh (tarray tuchar 4) (map Vint contents) p)).

Definition __builtin_write32_reversed_spec :=
 DECLARE ___builtin_write32_reversed
  WITH p: val, sh: share, contents: list int
  PRE [ _ptr OF tptr tuint, _x OF tuint ] 
        PROP  (writable_share sh;
               Zlength contents >= 4)
        LOCAL (temp _ptr p;
               temp _x (Vint(big_endian_integer contents)))
        SEP   (`(memory_block sh 4 p))
  POST [ tvoid ] 
     PROP() LOCAL() 
     SEP(`(data_at sh (tarray tuchar 4) (map Vint contents)  p)).

Definition memcpy_spec :=
  DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, n: Z, contents: list int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (readable_share (fst sh); writable_share (snd sh); 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive q; temp 3%positive (Vint (Int.repr n)))
       SEP (`(data_at (fst sh) (tarray tuchar n) (map Vint contents) q);
              `(memory_block (snd sh) n p))
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(`(data_at (fst sh) (tarray tuchar n) (map Vint contents) q);
             `(data_at (snd sh) (tarray tuchar n) (map Vint contents) p)).

Definition memset_spec :=
  DECLARE _memset
   WITH sh : share, p: val, n: Z, c: int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tint, 3%positive OF tuint ]
       PROP (writable_share sh; 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive (Vint c);
                   temp 3%positive (Vint (Int.repr n)))
       SEP (`(memory_block sh n p))
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(`(data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint c)) p)).

Definition K_vector : val -> mpred :=
  data_at Tsh (tarray tuint (Zlength K256)) (map Vint K256).

Definition sha256_block_data_order_spec :=
  DECLARE _sha256_block_data_order
    WITH hashed: list int, b: list int, ctx : val, data: val, sh: share, kv : val
   PRE [ _ctx OF tptr t_struct_SHA256state_st, _in OF tptr tvoid ]
         PROP(Zlength b = LBLOCKz; (LBLOCKz | Zlength hashed)) 
         LOCAL (temp _ctx ctx; temp _in data; gvar _K256 kv)
         SEP (`(field_at Tsh t_struct_SHA256state_st [StructField _h] (map Vint (hash_blocks init_registers hashed)) ctx);
                `(data_block sh (intlist_to_Zlist b) data);
                 `(K_vector kv))
   POST [ tvoid ]
       PROP() LOCAL()
       SEP(`(field_at Tsh t_struct_SHA256state_st  [StructField _h] (map Vint (hash_blocks init_registers (hashed++b))) ctx);
             `(data_block sh (intlist_to_Zlist b) data);
             `(K_vector kv)).

Definition SHA256_addlength_spec :=
 DECLARE _SHA256_addlength
 WITH len : Z, c: val, n: Z
 PRE [ _c OF tptr t_struct_SHA256state_st , _len OF tuint ]
   PROP ( 0 <= n+len*8 < two_p 64; 0 <= len <= Int.max_unsigned; 0 <= n) 
   LOCAL (temp _len (Vint (Int.repr len)); temp _c c)
   SEP (`(field_at Tsh t_struct_SHA256state_st [StructField _Nl] (Vint (lo_part n)) c);
          `(field_at Tsh t_struct_SHA256state_st [StructField _Nh] (Vint (hi_part n)) c))
 POST [ tvoid ]
   PROP() LOCAL()
   SEP (`(field_at Tsh t_struct_SHA256state_st [StructField _Nl] (Vint (lo_part (n+len*8))) c);
          `(field_at Tsh t_struct_SHA256state_st [StructField _Nh] (Vint (hi_part (n+len*8))) c)).

Definition SHA256_Init_spec :=
  DECLARE _SHA256_Init
   WITH c : val 
   PRE [ _c OF tptr t_struct_SHA256state_st ]
         PROP () LOCAL (temp _c c)
         SEP(`(data_at_ Tsh t_struct_SHA256state_st c))
  POST [ tvoid ] 
         PROP() LOCAL() SEP(`(sha256state_ init_s256abs c)).

Inductive update_abs: list Z -> s256abs -> s256abs -> Prop :=
 Update_abs:
   (forall msg hashed blocks oldfrag newfrag,
        Zlength oldfrag < CBLOCKz ->
        Zlength newfrag < CBLOCKz ->
       (LBLOCKz | Zlength hashed) ->
       (LBLOCKz | Zlength blocks) -> 
       oldfrag++msg = intlist_to_Zlist blocks ++ newfrag ->
   update_abs msg (S256abs hashed oldfrag) 
                              (S256abs (hashed++blocks) newfrag)).

Definition SHA256_Update_spec :=
  DECLARE _SHA256_Update
   WITH a: s256abs, data: list Z, c : val, d: val, sh: share, len : Z, kv : val
   PRE [ _c OF tptr t_struct_SHA256state_st, _data_ OF tptr tvoid, _len OF tuint ]
         PROP (readable_share sh; len <= Zlength data; 0 <= len <= Int.max_unsigned;
                   (s256a_len a + len * 8 < two_p 64)%Z)
         LOCAL (temp _c c; temp _data_ d; temp _len (Vint (Int.repr len));
                     gvar _K256 kv)
         SEP(`(K_vector kv);
               `(sha256state_ a c); `(data_block sh data d))
  POST [ tvoid ] 
         EX a':_, 
          PROP (update_abs (sublist 0 len data) a a')
          LOCAL ()
          SEP(`(K_vector kv);
                `(sha256state_ a' c); `(data_block sh data d)).

Definition SHA256_Final_spec :=
  DECLARE _SHA256_Final
   WITH a: s256abs, md: val, c : val,  shmd: share, kv : val
   PRE [ _md OF tptr tuchar, _c OF tptr t_struct_SHA256state_st ]
         PROP (writable_share shmd) 
         LOCAL (temp _md md; temp _c c;
                      gvar _K256 kv)
         SEP(`(K_vector kv);
               `(sha256state_ a c);
               `(memory_block shmd 32 md))
  POST [ tvoid ] 
         PROP () LOCAL ()
         SEP(`(K_vector kv);
               `(data_at_ Tsh t_struct_SHA256state_st c);
               `(data_block shmd (sha_finish a) md)).

Definition SHA256_spec :=
  DECLARE _SHA256
   WITH d: val, len: Z, dsh: share, msh: share, data: list Z, md: val, kv : val
   PRE [ _d OF tptr tuchar, _n OF tuint, _md OF tptr tuchar ]
         PROP (readable_share dsh; writable_share msh; Zlength data * 8 < two_p 64; Zlength data <= Int.max_unsigned) 
         LOCAL (temp _d d; temp _n (Vint (Int.repr (Zlength data)));
                     temp _md md;
                      gvar _K256 kv)
         SEP(`(K_vector kv);
               `(data_block dsh data d); `(memory_block msh 32 md))
  POST [ tvoid ] 
         PROP () LOCAL ()
         SEP(`(K_vector kv);
               `(data_block dsh data d); `(data_block msh (SHA_256 data) md)).

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
  | S n', (id, Gfun (External (EF_builtin _ sig) argtys resty cc_default))::defs' => 
     (id, mk_funspec (iota_formals 1%positive argtys, resty) unit FF FF) 
      :: do_builtins n' defs'
  | _, _ => nil
 end.

Definition Gtot := do_builtins 3 (prog_defs prog) ++ Gprog.