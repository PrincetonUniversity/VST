Require Import VST.floyd.proofauto.
Import ListNotations.
Require Import sha.sha.
Require Import sha.general_lemmas.
Require Import sha.vst_lemmas.
Require Import sha.SHA256.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Open Scope logic.

Definition s256state := (list val * (val * (val * (list val * val))))%type.
Definition s256_h (s: s256state) := fst s.
Definition s256_Nl (s: s256state) := fst (snd s).
Definition s256_Nh (s: s256state) := fst (snd (snd s)).
Definition s256_data (s: s256state) := fst (snd (snd (snd s))).
Definition s256_num (s: s256state) := snd (snd (snd (snd s))).

Definition s256abs := list byte. (* SHA-256 abstract state *)

Definition s256a_hashed (a: s256abs) : list int :=
  bytelist_to_intlist (sublist 0 ((Zlength a / CBLOCKz) * CBLOCKz) a).

Definition s256a_data (a: s256abs) : list byte :=
  sublist ((Zlength a / CBLOCKz) * CBLOCKz) (Zlength a) a.

Definition S256abs (hashed: list int) (data: list byte) : s256abs :=
 intlist_to_bytelist hashed ++ data.

Definition s256a_regs (a: s256abs) : list int :=
      hash_blocks init_registers (s256a_hashed a).

Definition s256a_len (a: s256abs) := (Zlength a * 8)%Z.

Definition s256_relate (a: s256abs) (r: s256state) : Prop :=
         s256_h r = map Vint (s256a_regs a)
       /\ (s256_Nh r = Vint (hi_part (s256a_len a)) /\
            s256_Nl r = Vint (lo_part (s256a_len a)))
       /\ sublist 0 (Zlength (s256a_data a)) (s256_data r) =
             map Vubyte (s256a_data a)
       /\ s256_num r = Vint (Int.repr (Zlength (s256a_data a))).

Definition cVint (f: Z -> int) (i: Z) := Vint (f i).

Definition t_struct_SHA256state_st := Tstruct _SHA256state_st noattr.

Definition sha256state_ (sh: share) (a: s256abs) (c: val) : mpred :=
   EX r:s256state,
    !!  s256_relate a r  &&  data_at sh t_struct_SHA256state_st r c.

Definition _ptr : ident := 81%positive.
Definition _x : ident := 82%positive.

Definition __builtin_read32_reversed_spec :=
 DECLARE ___builtin_read32_reversed
  WITH p: val, sh: share, contents: list byte
  PRE [ _ptr OF tptr tuint ]
        PROP  (Zlength contents >= 4)
        LOCAL (temp _ptr p)
        SEP   (data_at sh (tarray tuchar 4) (map Vubyte contents) p)
  POST [ tuint ]
     PROP() LOCAL (temp ret_temp  (Vint (big_endian_integer contents)))
     SEP (data_at sh (tarray tuchar 4) (map Vubyte contents) p).

Definition __builtin_write32_reversed_spec :=
 DECLARE ___builtin_write32_reversed
  WITH p: val, sh: share, contents: list byte
  PRE [ _ptr OF tptr tuint, _x OF tuint ]
        PROP  (writable_share sh;
               Zlength contents >= 4)
        LOCAL (temp _ptr p;
               temp _x (Vint(big_endian_integer contents)))
        SEP   (memory_block sh 4 p)
  POST [ tvoid ]
     PROP() LOCAL()
     SEP(data_at sh (tarray tuchar 4) (map Vubyte contents)  p).

Definition memcpy_spec :=
  DECLARE _memcpy
   WITH qsh : share, psh: share, p: val, q: val, n: Z, contents: list int
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (readable_share qsh; writable_share psh; 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive q; temp 3%positive (Vint (Int.repr n)))
       SEP (data_at qsh (tarray tuchar n) (map Vint contents) q;
              memory_block psh n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at qsh (tarray tuchar n) (map Vint contents) q;
             data_at psh (tarray tuchar n) (map Vint contents) p).

Definition memset_spec :=
  DECLARE _memset
   WITH sh : share, p: val, n: Z, c: int
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tint, 3%positive OF tuint ]
       PROP (writable_share sh; 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive (Vint c);
                   temp 3%positive (Vint (Int.repr n)))
       SEP (memory_block sh n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint c)) p).

Definition K_vector (gv: globals) : mpred :=
  data_at Ews (tarray tuint (Zlength K256)) (map Vint K256) (gv _K256).

Definition sha256_block_data_order_spec :=
  DECLARE _sha256_block_data_order
    WITH regs: list int, b: list int, ctx : val, wsh: share, data: val, sh: share, gv: globals
   PRE [ _ctx OF tptr t_struct_SHA256state_st, _in OF tptr tvoid ]
         PROP(Zlength regs = 8; Zlength b = LBLOCKz; 
                  writable_share wsh; readable_share sh)
         LOCAL (temp _ctx ctx; temp _in data; gvars gv)
         SEP (field_at wsh t_struct_SHA256state_st [StructField _h] (map Vint regs) ctx;
                data_block sh (intlist_to_bytelist b) data;
                K_vector gv)
   POST [ tvoid ]
       PROP() LOCAL()
       SEP(field_at wsh t_struct_SHA256state_st  [StructField _h] (map Vint (hash_block regs b)) ctx;
             data_block sh (intlist_to_bytelist b) data;
             K_vector gv).

Definition SHA256_addlength_spec :=
 DECLARE _SHA256_addlength
 WITH len : Z, c: val, sh: share, n: Z
 PRE [ _c OF tptr t_struct_SHA256state_st , _len OF tuint ]
   PROP (writable_share sh;
             0 <= n+len*8 < two_p 64; 0 <= len <= Int.max_unsigned; 0 <= n)
   LOCAL (temp _len (Vint (Int.repr len)); temp _c c)
   SEP (field_at sh t_struct_SHA256state_st [StructField _Nl] (Vint (lo_part n)) c;
          field_at sh t_struct_SHA256state_st [StructField _Nh] (Vint (hi_part n)) c)
 POST [ tvoid ]
   PROP() LOCAL()
   SEP (field_at sh t_struct_SHA256state_st [StructField _Nl] (Vint (lo_part (n+len*8))) c;
          field_at sh t_struct_SHA256state_st [StructField _Nh] (Vint (hi_part (n+len*8))) c).

Definition SHA256_Init_spec :=
  DECLARE _SHA256_Init
   WITH c : val, sh: share
   PRE [ _c OF tptr t_struct_SHA256state_st ]
         PROP (writable_share sh) LOCAL (temp _c c)
         SEP(data_at_ sh t_struct_SHA256state_st c)
  POST [ tvoid ]
         PROP() LOCAL() SEP(sha256state_ sh nil c).

Definition SHA256_Update_spec :=
  DECLARE _SHA256_Update
   WITH a: s256abs, data: list byte, c : val, wsh: share, d: val, sh: share, len : Z, gv: globals
   PRE [ _c OF tptr t_struct_SHA256state_st, _data_ OF tptr tvoid, _len OF tuint ]
         PROP (writable_share wsh; readable_share sh; 
                   len <= Zlength data; 0 <= len <= Int.max_unsigned;
                   (s256a_len a + len * 8 < two_p 64)%Z)
         LOCAL (temp _c c; temp _data_ d; temp _len (Vint (Int.repr len));
                     gvars gv)
         SEP(K_vector gv;
               sha256state_ wsh a c; data_block sh data d)
  POST [ tvoid ]
          PROP ()
          LOCAL ()
          SEP(K_vector gv;
                sha256state_ wsh (a ++ sublist 0 len data) c;
                data_block sh data d).

Definition SHA256_Final_spec :=
  DECLARE _SHA256_Final
   WITH a: s256abs, md: val, c : val,  wsh: share, shmd: share, gv : globals
   PRE [ _md OF tptr tuchar, _c OF tptr t_struct_SHA256state_st ]
         PROP (writable_share wsh; writable_share shmd)
         LOCAL (temp _md md; temp _c c;
                      gvars gv)
         SEP(K_vector gv;
               sha256state_ wsh a c;
               memory_block shmd 32 md)
  POST [ tvoid ]
         PROP () LOCAL ()
         SEP(K_vector gv;
               data_at_ wsh t_struct_SHA256state_st c;
               data_block shmd (SHA_256 a) md).

Definition SHA256_spec :=
  DECLARE _SHA256
   WITH d: val, len: Z, dsh: share, msh: share, data: list byte, md: val, gv: globals
   PRE [ _d OF tptr tuchar, _n OF tuint, _md OF tptr tuchar ]
         PROP (readable_share dsh; writable_share msh; 
                   Zlength data * 8 < two_p 64; Zlength data <= Int.max_unsigned)
         LOCAL (temp _d d; temp _n (Vint (Int.repr (Zlength data)));
                     temp _md md;
                      gvars gv)
         SEP(K_vector gv;
               data_block dsh data d; memory_block msh 32 md)
  POST [ tvoid ]
         PROP () LOCAL ()
         SEP(K_vector gv;
               data_block dsh data d; data_block msh (SHA_256 data) md).

Definition Gprog : funspecs :=
  __builtin_read32_reversed_spec::
  __builtin_write32_reversed_spec::
  memcpy_spec:: memset_spec::
  sha256_block_data_order_spec:: SHA256_Init_spec::
  SHA256_addlength_spec::
  SHA256_Update_spec:: SHA256_Final_spec::
  SHA256_spec:: nil.

Fixpoint do_builtins (n: nat) (defs : list (ident * globdef Clight.fundef type)) : funspecs :=
 match n, defs with
  | S n', (id, Gfun (External (EF_builtin _ sig) argtys resty cc_default))::defs' =>
     (id, NDmk_funspec (iota_formals 1%positive argtys, resty) cc_default unit FF FF)
      :: do_builtins n' defs'
  | _, _ => nil
 end.

Definition Gtot := do_builtins 3 (prog_defs prog) ++ Gprog.
