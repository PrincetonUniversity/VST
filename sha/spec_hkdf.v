Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import floyd.library.

Require Import sha.spec_sha.
(*Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.hmac.*)
(*Require Import sha.spec_hmac.*)
Require Import sha.protocol_spec_hmac.

Require Import sha.hkdf_functional_prog.
Require Import sha.hkdf.

Require Import hmacdrbg.hmac_drbg_compspecs.

(*Definition Vprog : varspecs. Proof. mk_varspecs prog. Defined.*)

Declare Module HMAC_SPEC : HMAC_ABSTRACT_SPEC.
Definition digest_len:Z := 32.
Definition expand_out_post sh PrkCont InfoCont olen out: Z * mpred :=
  let n := (olen + digest_len - 1) / digest_len in
  if zlt (olen + digest_len) olen 
  then (0, memory_block sh olen out)
  else if zlt 255 n 
       then (0, memory_block sh olen out)
       else (1, data_block sh (HKDF_expand PrkCont InfoCont olen) out).

(*todo: refine spec to capture path leading to rv=0*)
Definition HKDF_expand_spec :=
  DECLARE _HKDF_expand
   WITH out: val, olen:Z,
        prk: val, PRK:spec_hmac.DATA,
        info: val, INFO:spec_hmac.DATA,
        kv:val, shmd: share
   PRE [ _out_key OF tptr tuchar, _out_len OF tuint,
         _prk OF tptr tuchar, _prk_len OF tuint,
         _info OF tptr tuchar, _info_len OF tuint]
         PROP (writable_share shmd; 
               spec_hmac.has_lengthK (spec_hmac.LEN PRK) (spec_hmac.CONT PRK);
               spec_hmac.LEN INFO = Zlength (spec_hmac.CONT INFO);
               0 <= Zlength (spec_hmac.CONT INFO) <= Int.max_unsigned /\
                 Zlength (spec_hmac.CONT INFO) + 97 < two_power_pos 61;
               0 <= olen /\ olen + 32 <= Int.max_unsigned)
         LOCAL (temp _out_key out; temp _out_len (Vint (Int.repr olen)); 
                temp _prk prk;
                temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK)));
                temp _info info;
                temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
                gvar sha._K256 kv)
         SEP(data_block Tsh (spec_hmac.CONT INFO) info;
             data_block Tsh (spec_hmac.CONT PRK) prk;
             K_vector kv;
             memory_block shmd olen out
             (*data_at_ shmd (tarray tuchar olen) out*))
  POST [ tint ] EX result:_,
          PROP (result = expand_out_post shmd (spec_hmac.CONT PRK) (spec_hmac.CONT INFO) olen out)
          LOCAL (temp ret_temp (Vint (Int.repr (fst result))))
          SEP(K_vector kv;
              data_block Tsh (spec_hmac.CONT INFO) info;
              data_block Tsh (spec_hmac.CONT PRK) prk;
              (snd result)).

Definition HKDF_extract_spec :=
  DECLARE _HKDF_extract
   WITH out: val, olen:val,
        secret: val, SECRET:spec_hmac.DATA,
        salt: val, SALT:spec_hmac.DATA,
        kv:val, shmd: share
   PRE [_out_key OF tptr tuchar, _out_len OF tptr tuint,
        _secret OF tptr tuchar, _secret_len OF tuint,
        _salt OF tptr tuchar, _salt_len OF tuint ]
         PROP (writable_share shmd; spec_hmac.has_lengthK (spec_hmac.LEN SALT) (spec_hmac.CONT SALT);
               spec_hmac.has_lengthD 512 (spec_hmac.LEN SECRET) (spec_hmac.CONT SECRET))
         LOCAL (temp _out_key out;  
                temp _out_len olen;
                temp _salt salt;
                temp _salt_len (Vint (Int.repr (spec_hmac.LEN SALT)));
                temp _secret secret;
                temp _secret_len (Vint (Int.repr (spec_hmac.LEN SECRET)));
                gvar sha._K256 kv)
         SEP(data_block Tsh (spec_hmac.CONT SECRET) secret;
             data_block Tsh (spec_hmac.CONT SALT) salt;
             K_vector kv; data_at_ Tsh tuint olen;
             memory_block shmd 32 out)
  POST [ tint ] EX x:int, 
          PROP ()
          LOCAL ((*temp _out_len (Vint (Int.repr 32));*) temp ret_temp (Vint x))
          SEP(K_vector kv;
              data_block Tsh (spec_hmac.CONT SECRET) secret;
              data_block Tsh (spec_hmac.CONT SALT) salt; data_at Tsh tuint (Vint (Int.repr 32)) olen;
              data_block shmd (HKFD_extract (spec_hmac.CONT SALT) (spec_hmac.CONT SECRET)) out).

Definition HKDF_spec :=
  DECLARE _HKDF
   WITH out: val, olen:Z, 
        secret: val, SECRET:spec_hmac.DATA,
        salt: val, SALT:spec_hmac.DATA,
        info:val, INFO:spec_hmac.DATA,
        kv:val, shmd: share
   PRE [_out_key OF tptr tuchar, _out_len OF tuint,
        _secret OF tptr tuchar, _secret_len OF tuint,
        _salt OF tptr tuchar, _salt_len OF tuint,
        _info OF tptr tuchar, _info_len OF tuint ]
         PROP (writable_share shmd; spec_hmac.has_lengthK (spec_hmac.LEN SALT) (spec_hmac.CONT SALT); 
               spec_hmac.has_lengthD 512 (spec_hmac.LEN SECRET) (spec_hmac.CONT SECRET))
         LOCAL (temp _out_key out; temp _out_len (Vint (Int.repr olen)); 
                temp _salt salt;
                temp _salt_len (Vint (Int.repr (spec_hmac.LEN SALT)));
                temp _secret secret;
                temp _secret_len (Vint (Int.repr (spec_hmac.LEN SECRET)));
                temp _info info;
                temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
                gvar sha._K256 kv)
         SEP(data_block Tsh (spec_hmac.CONT SECRET) secret;
             data_block Tsh (spec_hmac.CONT SALT) salt;
             data_block Tsh (spec_hmac.CONT INFO) info;
             K_vector kv;
             memory_block shmd olen out)
  POST [ tint ] 
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr 1)))
          SEP(K_vector kv;
              data_block Tsh (spec_hmac.CONT SECRET) secret;
              data_block Tsh (spec_hmac.CONT SALT) salt;
              data_block Tsh (spec_hmac.CONT INFO) info;
              data_block shmd (HKDF (spec_hmac.CONT SALT) (spec_hmac.CONT SECRET) (spec_hmac.CONT INFO) olen) out).

(*generalizes spec_sha.memcpy_spec by allowing SRC/TGT-array to be longer than necessary*)
Definition memcpy_spec :=
  DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, n: Z, m:Z, k:Z, contents: list int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (readable_share (fst sh); writable_share (snd sh); 0 <= k <= n;
       k <= m <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive q; temp 3%positive (Vint (Int.repr k)))
       SEP (data_at (fst sh) (tarray tuchar m) (map Vint contents) q;
              memory_block (snd sh) n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at (fst sh) (tarray tuchar m) (map Vint contents) q;
           data_at (snd sh) (tarray tuchar k) (map Vint (sublist 0 k contents)) p;
              memory_block (snd sh) (n-k) (offset_val k p)).
(*Definition memcpy_spec := (_memcpy, snd spec_sha.memcpy_spec). *)

(***************** We combine all specifications to a specification context *******)

(*Definition SHA256_spec := (_SHA256, snd spec_sha.SHA256_spec). *)(*
Definition sha256init_spec := (_SHA256_Init, snd SHA256_Init_spec).
Definition sha256update_spec := (_SHA256_Update, snd SHA256_Update_spec).
Definition sha256final_spec := (_SHA256_Final, snd SHA256_Final_spec).
Definition memset_spec := (_memset, snd spec_sha.memset_spec). *)

Definition Hkdf_VarSpecs : varspecs := (sha._K256, tarray tuint 64)::nil.


Definition hmac_init_funspec:=
    (WITH x : val * Z * list Z * val + val * Z * list Z * val * block * int PRE
     [(hmac._ctx, tptr spec_hmac.t_struct_hmac_ctx_st), (hmac._key, tptr tuchar),
     (hmac._len, tint)] match x with
                        | inl (c, l, key, kv) =>
                            PROP ( )
                            LOCAL (temp hmac._ctx c; temp hmac._key nullval;
                            temp hmac._len (Vint (Int.repr l)); 
                            gvar sha._K256 kv)
                            SEP (HMAC_SPEC.FULL key c;
                            spec_sha.K_vector kv)
                        | inr (c, l, key, kv, b0, i) =>
                            PROP (spec_hmac.has_lengthK l key)
                            LOCAL (temp hmac._ctx c; temp hmac._key (Vptr b0 i);
                            temp hmac._len (Vint (Int.repr l)); 
                            gvar sha._K256 kv)
                            SEP (HMAC_SPEC.EMPTY c;
                            spec_sha.data_block Tsh key (Vptr b0 i); 
                            spec_sha.K_vector kv)
                        end
     POST [tvoid] match x with
                  | inl (c, _, key, kv) =>
                      PROP ( )
                      LOCAL ()
                      SEP (HMAC_SPEC.REP
                             (HMAC_SPEC.hABS key []) c;
                      spec_sha.K_vector kv)
                  | inr (c, _, key, kv, b0, i) =>
                      PROP ( )
                      LOCAL ()
                      SEP (HMAC_SPEC.REP
                             (HMAC_SPEC.hABS key []) c;
                      spec_sha.data_block Tsh key (Vptr b0 i); 
                      spec_sha.K_vector kv)
                  end).

Definition Hkdf_FunSpecs : funspecs := ltac:(with_library prog (
  HKDF_spec :: HKDF_expand_spec :: HKDF_extract_spec :: 
  memcpy_spec:: (*memcpy__data_at:: *)
  (*memset_spec::*)
  HMAC_SPEC.hmac_update_spec::
  HMAC_SPEC.hmac_final_spec::  
  HMAC_SPEC.hmac_cleanup_spec::  
  (hmac._HMAC_Init,hmac_init_funspec)::
  HMAC_SPEC.hmac_crypto_spec::nil)).
(*
Definition HMS : hmacstate := default_val t_struct_hmac_ctx_st.

Lemma change_compspecs_t_struct_SHA256state_st:
  @data_at spec_sha.CompSpecs Tsh t_struct_SHA256state_st =
  @data_at CompSpecs Tsh t_struct_SHA256state_st.
Proof.
extensionality gfs v.
reflexivity.
Qed.

Hint Rewrite change_compspecs_t_struct_SHA256state_st : norm.
*)
