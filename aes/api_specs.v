Require Export VST.floyd.proofauto.
Require Export VST.floyd.reassoc_seq.
Require Export aes.aes.
Require Export aes.GF_ops_LL.
Require Export aes.tablesLL.
Require Export aes.spec_utils_LL.
Require Export aes.list_utils.
Require Export aes.spec_encryption_LL.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition t_struct_aesctx := Tstruct _mbedtls_aes_context_struct noattr.
Definition t_struct_tables := Tstruct _aes_tables_struct noattr.

Definition tables_initialized (tables : val) := data_at Ews t_struct_tables
  (map Vint FSb, (map Vint FT0, (map Vint FT1, (map Vint FT2, (map Vint FT3,
  (map Vint RSb, (map Vint RT0, (map Vint RT1, (map Vint RT2, (map Vint RT3,
  (map Vint RCON))))))))))) tables.

Definition Vundef256 : list val := repeat Vundef 256%nat.

Definition tables_uninitialized tables := data_at Ews t_struct_tables (Vundef256, 
  (Vundef256, (Vundef256, (Vundef256, (Vundef256, (Vundef256,
  (Vundef256, (Vundef256, (Vundef256, (Vundef256, 
  (repeat Vundef 10))))))))))) tables.

Definition gen_tables_spec :=
  DECLARE _aes_gen_tables
    WITH gv: globals
    PRE [  ]
      PROP ()
      LOCAL (gvars gv)
      SEP (tables_uninitialized (gv _tables))
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (tables_initialized (gv _tables))
.


(* TODO replace this HL spec by a LL spec, and move HL spec to actual spec *)

Definition word_to_int (w : (int * int * int * int)) : int :=
  match w with (b0, b1, b2, b3) =>
    (Int.or (Int.or (Int.or
             b0
    (Int.shl b1 (Int.repr  8)))
    (Int.shl b2 (Int.repr 16)))
    (Int.shl b3 (Int.repr 24)))
  end.

(* SubWord function from section 5.2: apply S-box to each byte in a word *)
Definition SubWord (w: int) : int := word_to_int (
  (Znth (byte0 w) FSb),
  (Znth (byte1 w) FSb),
  (Znth (byte2 w) FSb),
  (Znth (byte3 w) FSb)
).

Definition RotWord(i: int): int := 
  Int.or (Int.and (Int.shl i (Int.repr 8)) (Int.repr (-1))) (Int.shru i (Int.repr 24)).

(* round constant (RCon) array, described in section 5.2 and explicitly written
 * out in appendix A.3 (256-bit key expansion example) *)
Definition RCon : list int := map (fun i => Int.shl i (Int.repr 24)) [
  (* 0x01000000 *) (Int.repr 1);
  (* 0x02000000 *) (Int.repr 2);
  (* 0x04000000 *) (Int.repr 4);
  (* 0x08000000 *) (Int.repr 8);
  (* 0x10000000 *) (Int.repr 16);
  (* 0x20000000 *) (Int.repr 32);
  (* 0x40000000 *) (Int.repr 64)
].

Definition GrowKeyByOne(w: list int): list int :=
  let i := Zlength w in
  let temp := (Znth (i-1) w) in
  let temp' := if (i mod Nk =? 0) then
    Int.xor (SubWord (RotWord temp)) (Znth (i/Nk) RCon)
  else if (i mod Nk =? 4) then
    SubWord temp
  else
    temp
  in
    w ++ [Int.xor (Znth (i-8) w) temp'].

Fixpoint pow_fun{T: Type}(f: T -> T)(n: nat)(a: T): T := match n with
| O => a
| S m => f (pow_fun f m a)
end.

(* +2 because 1 is for the initial round which is not counted, and 1 superfluous round key is
   created in the last loop iteration, because each iteration creates 2 round keys.
   -Nk because the first two round keys are just the unexpanded key.
  Note that (Nb*(Nr+2)-Nk) = 56. *)
Definition KeyExpansion2: list int -> list int := pow_fun GrowKeyByOne (Z.to_nat (Nb*(Nr+2)-Nk)).

(* arr: list of bytes *)
Definition get_uint32_le (arr: list Z) (i: Z) : int :=
 (Int.or (Int.or (Int.or
            (Int.repr (Znth  i    arr))
   (Int.shl (Int.repr (Znth (i+1) arr)) (Int.repr  8)))
   (Int.shl (Int.repr (Znth (i+2) arr)) (Int.repr 16)))
   (Int.shl (Int.repr (Znth (i+3) arr)) (Int.repr 24))).

Definition key_bytes_to_key_words(key_bytes: list Z): list int := 
  fill_list 8 (fun i => get_uint32_le key_bytes (i*4)).

(* end TODO *)

(* Note: clightgen turns global variables of type int to pointers to int, to make them addressable,
   so aes_init_done is a pointer to int, not an int! *)
Definition key_expansion_spec :=
  DECLARE _mbedtls_aes_setkey_enc
    WITH ctx : val, key : val, ctx_sh : share, key_sh : share, key_chars : list Z,
         init_done : Z, ish: share, gv: globals
    PRE [ _ctx OF (tptr t_struct_aesctx), _key OF (tptr tuchar), _keybits OF tuint  ]
      PROP (writable_share ctx_sh; readable_share key_sh; readable_share ish;
            Zlength key_chars = 32;
            init_done = 1 (*TODO also prove case where init_done=0*))
      LOCAL (temp _ctx ctx; temp _key key; temp _keybits (Vint (Int.repr 256)); 
             gvars gv)
      SEP (data_at ctx_sh t_struct_aesctx 
                   (Vint Int.zero,
                   (nullval, 
                   (map Vint (repeat_op_table 68 Int.zero id)))) ctx;
           data_at key_sh (tarray tuchar (4*8)) (map Vint (map Int.repr key_chars)) key;
           (*if init_done ?= 1 then tables_initialized tables else tables_uninitialized tables*)
           data_at ish tint (Vint (Int.repr init_done)) (gv _aes_init_done);
           tables_initialized (gv _tables))
    POST [  tint ]
      PROP () 
      LOCAL (temp ret_temp (Vint Int.zero))
      SEP (data_at key_sh (tarray tuchar (4*8)) (map Vint (map Int.repr key_chars)) key;
           data_at ctx_sh t_struct_aesctx 
                   (Vint (Int.repr 14),
                   ((field_address t_struct_aesctx [StructField _buf] ctx), 
                   (map Vint (KeyExpansion2 (key_bytes_to_key_words key_chars))
                    ++ (repeat_op_table 4 (Vint Int.zero) id)))) ctx;
           data_at ish tint (Vint (Int.repr init_done)) (gv _aes_init_done);
           tables_initialized (gv _tables)).


Definition encryption_spec_ll :=
  DECLARE _mbedtls_aes_encrypt
  WITH ctx : val, input : val, output : val, (* arguments *)
       ctx_sh : share, in_sh : share, out_sh : share, (* shares *)
       plaintext : list Z, (* 16 chars *)
       exp_key : list Z, (* expanded key, 4*(Nr+1)=60 32-bit integers *)
       gv: globals (* global var *)
  PRE [ _ctx OF (tptr t_struct_aesctx), _input OF (tptr tuchar), _output OF (tptr tuchar) ]
    PROP (Zlength plaintext = 16; Zlength exp_key = 60;
          readable_share ctx_sh; readable_share in_sh; writable_share out_sh)
    LOCAL (temp _ctx ctx; temp _input input; temp _output output; gvars gv)
    SEP (data_at ctx_sh (t_struct_aesctx) (
          (Vint (Int.repr Nr)),
          ((field_address t_struct_aesctx [StructField _buf] ctx),
          (map Vint (map Int.repr (exp_key ++ (list_repeat (8%nat) 0)))))
          (* The following weaker precondition would also be provable, but less conveniently, and   *)
          (* since mbedtls_aes_init zeroes the whole buffer, we exploit this to simplify the proof  *)
          (* ((map Vint (map Int.repr exp_key)) ++ (list_repeat (8%nat) Vundef))) *)
         ) ctx;
         data_at in_sh (tarray tuchar 16) (map Vint (map Int.repr plaintext)) input;
         data_at_ out_sh (tarray tuchar 16) output;
         tables_initialized (gv _tables))
  POST [ tvoid ]
    PROP() LOCAL()
    SEP (data_at ctx_sh (t_struct_aesctx) (
          (Vint (Int.repr Nr)),
          ((field_address t_struct_aesctx [StructField _buf] ctx),
          (map Vint (map Int.repr (exp_key ++ (list_repeat (8%nat) 0)))))
         ) ctx;
         data_at in_sh  (tarray tuchar 16)
                 (map Vint (map Int.repr plaintext)) input;
         data_at out_sh (tarray tuchar 16)
                 (map Vint (mbed_tls_aes_enc plaintext (exp_key ++ (list_repeat (8%nat) 0)))) output;
         tables_initialized (gv _tables)).

Definition Gprog : funspecs := ltac:(with_library prog [
  gen_tables_spec; key_expansion_spec; encryption_spec_ll
]).

(* This is to make sure do_compute_expr (invoked by load_tac and others), which calls hnf on the
   expression it's computing, does not unfold field_address.
   TODO floyd: Ideally, we'd have "Global Opaque field_address field_address0" in the library,
   but some proofs want to unfold field_address (they shouldn't, though). *)
Global Opaque field_address.

(* entailer! calls simpl, and if simpl tries to evaluate a column of the final AES encryption result,
   it takes forever, so we have to prevent this: *)
Arguments col _ _ : simpl never.
(* Same problem with "Z.land _ 255" *)
Arguments Z.land _ _ : simpl never.

(* This one is to prevent simplification of "12 - _", which is fast, but produces silly verbose goals *)
Arguments Nat.sub _ _ : simpl never.
