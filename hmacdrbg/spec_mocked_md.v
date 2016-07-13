Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import mocked_md.
Require Import sha.spec_hmacNK.
Require Import sha.funspec_hmacNK.
Require Import sha.spec_sha.
Require Import sha.HMAC256_functional_prog.

(*
Require Import mocked_md_compspecs.
*)

Module UNDER_SPEC := OPENSSL_HMAC_ABSTRACT_SPEC.

Inductive HABS := hABS: forall (key data:list Z), HABS.

Definition mdstate: Type := (val * (val * val))%type.

Definition t_struct_md_ctx_st := Tstruct _mbedtls_md_context_t noattr.

Definition convert_abs (h: HABS): UNDER_SPEC.HABS :=
  match h with hABS key data => UNDER_SPEC.hABS key data end.

Definition md_relate (h: HABS) (r:mdstate) :=
  UNDER_SPEC.REP (convert_abs h) (snd (snd r)).

Definition REP (h: HABS) (c: val): mpred :=
  EX r: mdstate,
        (md_relate h r && data_at Tsh t_struct_md_ctx_st r c).

Definition FULL key c:mpred :=
  EX r: mdstate,
        (UNDER_SPEC.FULL key (snd (snd r)) && data_at Tsh t_struct_md_ctx_st r c).

Definition EMPTY c :=
  EX r: mdstate,
        (UNDER_SPEC.EMPTY (snd (snd r)) && data_at Tsh t_struct_md_ctx_st r c).

Definition md_get_size_spec :=
  DECLARE _mbedtls_md_get_size
   WITH u:unit
   PRE [ _md_info OF tptr (Tstruct _mbedtls_md_info_t noattr)]
         PROP ()
         LOCAL ()
         SEP ()
  POST [ tuchar ] 
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.repr (Z.of_nat SHA256.DigestLength))))
     SEP ().
 
Definition md_reset_spec :=
  DECLARE _mbedtls_md_hmac_reset
   WITH c : val, l:Z, key:list Z, kv:val, d:list Z
   PRE [ _ctx OF tptr t_struct_md_ctx_st]
         PROP (has_lengthK l key)
         LOCAL (temp _ctx c; gvar sha._K256 kv)
         SEP ( `(FULL key c); `(K_vector kv))
  POST [ tint ] 
     PROP ()
     LOCAL ()
     SEP (`(REP (hABS key nil) c); `(K_vector kv)).

Definition md_starts_spec :=
  DECLARE _mbedtls_md_hmac_starts
   WITH c : val, l:Z, key:list Z, kv:val, b:block, i:Int.int
   PRE [ _ctx OF tptr t_struct_md_ctx_st,
         _key OF tptr tuchar,
         _keylen OF tint ]
         PROP (has_lengthK l key)
         LOCAL (temp _ctx c; temp _key (Vptr b i); temp _keylen (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP (`(EMPTY c); 
              `(data_block Tsh key (Vptr b i)); `(K_vector kv))
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (`(REP (hABS key nil) c); `(data_block Tsh key (Vptr b i)); `(K_vector kv)).

Definition md_update_spec :=
  DECLARE _mbedtls_md_hmac_update
   WITH key: list Z, c : val, d:val, data:list Z, data1:list Z, kv:val
   PRE [ _ctx OF tptr t_struct_md_ctx_st, 
         _input OF tptr tvoid, 
         _ilen OF tuint]
         PROP (0 <= Zlength data1 <= Int.max_unsigned /\
               Zlength data1 + Zlength data + 64 < two_power_pos 61) 
         LOCAL (temp _ctx c; temp _input d; temp  _ilen (Vint (Int.repr (Zlength data1)));
                gvar sha._K256 kv)
         SEP(`(REP (hABS key data) c); `(data_block Tsh data1 d); `(K_vector kv))
  POST [ tvoid ] 
          PROP () 
          LOCAL ()
          SEP(`(REP (hABS key (data++data1)) c); 
              `(data_block Tsh data1 d);`(K_vector kv)).

Definition md_final_spec :=
  DECLARE _mbedtls_md_hmac_finish
   WITH data:list Z, key:list Z, c : val, md:val, shmd: share, kv:val
   PRE [ _ctx OF tptr t_struct_md_ctx_st,
         _output OF tptr tuchar ]
       PROP (writable_share shmd) 
       LOCAL (temp _output md; temp _ctx c;
              gvar sha._K256 kv)
       SEP(`(REP (hABS key data) c); `(K_vector kv);
           `(memory_block shmd 32 md))
  POST [ tvoid ] 
          PROP () 
          LOCAL ()
          SEP(`(K_vector kv);
              `(FULL key c);
              `(data_block shmd (HMAC256 data key) md)).

