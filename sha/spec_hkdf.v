Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import VST.floyd.library.
Require Import sha.vst_lemmas.
Require Import sha.protocol_spec_hmac.

Require Import sha.hkdf_functional_prog.
Require Import sha.hkdf.

Require Import VST.veric.change_compspecs.

Instance CompSpecs : compspecs. 
Proof. make_compspecs prog. Defined. (*
Instance CompSpecs_Preserve: change_composite_env spec_sha.CompSpecs CompSpecs.
  make_cs_preserve spec_sha.CompSpecs CompSpecs.
Defined.*)
Instance CompSpecs_Preserve: change_composite_env spec_hmac.CompSpecs CompSpecs.
  make_cs_preserve spec_hmac.CompSpecs CompSpecs.
Defined.

(*Require Import sha.hkdf_compspecs.*)

Declare Module HMAC_SPEC : HMAC_ABSTRACT_SPEC.

Definition digest_len:Z := 32.
Definition expand_out_post sh PrkCont InfoCont olen out: Z * mpred :=
  let n := (olen + digest_len - 1) / digest_len in
  if zlt (olen + digest_len) olen 
  then (0, memory_block sh olen out)
  else if zlt 255 n 
       then (0, memory_block sh olen out)
       else (1, data_block sh (HKDF_expand PrkCont InfoCont olen) out).

Definition HKDF_expand_spec :=
  DECLARE _HKDF_expand
   WITH out: val, olen:Z,
        prk: val, PRK:spec_hmac.DATA,
        info: val, INFO:spec_hmac.DATA,
        gv: globals, shmd: share
   PRE [ _out_key OF tptr tuchar, _out_len OF tuint,
         _prk OF tptr tuchar, _prk_len OF tuint,
         _info OF tptr tuchar, _info_len OF tuint]
         PROP (writable_share shmd; 
               spec_hmac.has_lengthK (spec_hmac.LEN PRK) (spec_hmac.CONT PRK);
               Zlength (spec_hmac.CONT INFO) = spec_hmac.LEN INFO;
               0 <= Zlength (spec_hmac.CONT INFO) <= Int.max_unsigned /\
                 Zlength (spec_hmac.CONT INFO) + 97 < two_power_pos 61;
               0 <= olen /\ olen + 32 <= Int.max_unsigned)
         LOCAL (temp _out_key out; temp _out_len (Vint (Int.repr olen)); 
                temp _prk prk;
                temp _prk_len (Vint (Int.repr (spec_hmac.LEN PRK)));
                temp _info info;
                temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
                gvars gv)
         SEP(data_block Tsh (spec_hmac.CONT INFO) info;
             data_block Tsh (spec_hmac.CONT PRK) prk;
             spec_sha.K_vector gv;
             memory_block shmd olen out)
  POST [ tint ] EX result:_,
          PROP (result = expand_out_post shmd (spec_hmac.CONT PRK) (spec_hmac.CONT INFO) olen out)
          LOCAL (temp ret_temp (Vint (Int.repr (fst result))))
          SEP(spec_sha.K_vector gv;
              data_block Tsh (spec_hmac.CONT INFO) info;
              data_block Tsh (spec_hmac.CONT PRK) prk;
              (snd result)).

Definition HKDF_extract_spec :=
  DECLARE _HKDF_extract
   WITH out: val, olen:val,
        secret: val, SECRET:spec_hmac.DATA,
        salt: val, SALT:spec_hmac.DATA,
        gv: globals, shmd: share
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
                gvars gv)
         SEP(data_block Tsh (spec_hmac.CONT SECRET) secret;
             data_block Tsh (spec_hmac.CONT SALT) salt;
             spec_sha.K_vector gv; data_at_ Tsh tuint olen;
             memory_block shmd 32 out)
  POST [ tint ]  
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr 1)))
          SEP(spec_sha.K_vector gv;
              data_block Tsh (spec_hmac.CONT SECRET) secret;
              data_block Tsh (spec_hmac.CONT SALT) salt; data_at Tsh tuint (Vint (Int.repr 32)) olen;
              data_block shmd (HKDF_extract (spec_hmac.CONT SALT) (spec_hmac.CONT SECRET)) out).

Definition HKDF_spec :=
  DECLARE _HKDF
   WITH out: val, olen:Z, 
        secret: val, SECRET:spec_hmac.DATA,
        salt: val, SALT:spec_hmac.DATA,
        info:val, INFO:spec_hmac.DATA,
        gv:globals, shmd: share
   PRE [_out_key OF tptr tuchar, _out_len OF tuint,
        _secret OF tptr tuchar, _secret_len OF tuint,
        _salt OF tptr tuchar, _salt_len OF tuint,
        _info OF tptr tuchar, _info_len OF tuint ]
         PROP (writable_share shmd; 
               spec_hmac.has_lengthK (spec_hmac.LEN SALT) (spec_hmac.CONT SALT); 
               spec_hmac.has_lengthD 512 (spec_hmac.LEN SECRET) (spec_hmac.CONT SECRET);
               Zlength (spec_hmac.CONT INFO) = spec_hmac.LEN INFO; 
               0 <= Zlength (spec_hmac.CONT INFO) <= Int.max_unsigned;
               Zlength (spec_hmac.CONT INFO) + 97 < two_power_pos 61; 
               0 <= olen; olen + 32 <= Int.max_unsigned)
         LOCAL (temp _out_key out; temp _out_len (Vint (Int.repr olen)); 
                temp _salt salt;
                temp _salt_len (Vint (Int.repr (spec_hmac.LEN SALT)));
                temp _secret secret;
                temp _secret_len (Vint (Int.repr (spec_hmac.LEN SECRET)));
                temp _info info;
                temp _info_len (Vint (Int.repr (spec_hmac.LEN INFO)));
                gvars gv)
         SEP(data_block Tsh (spec_hmac.CONT SECRET) secret;
             data_block Tsh (spec_hmac.CONT SALT) salt;
             data_block Tsh (spec_hmac.CONT INFO) info;
             spec_sha.K_vector gv;
             memory_block shmd olen out)
  POST [ tint ] EX r:Z,
          PROP ()
          LOCAL (temp ret_temp (Vint (Int.repr r)))
          SEP(spec_sha.K_vector gv;
              data_block Tsh (spec_hmac.CONT SECRET) secret;
              data_block Tsh (spec_hmac.CONT SALT) salt;
              data_block Tsh (spec_hmac.CONT INFO) info;
              if zlt 255 ((olen + 31) / 32) 
              then (!!(r=0) && memory_block shmd olen out)
              else (!!(r=1) && data_block shmd (HKDF (spec_hmac.CONT SALT) (spec_hmac.CONT SECRET) (spec_hmac.CONT INFO) olen) out)).

(*generalizes spec_sha.memcpy_spec by allowing SRC/TGT-array to be longer than necessary.
 Also adds cs to the WITH clause. Because we're copying a tarray tuchar we don't need a
field_compatible/size_compatible side condition (cf Lemma memory_block_data_at__tarray_tuchar) *)
Definition memcpy_tuchar_array_spec {cs:compspecs} :=
  DECLARE _memcpy
   WITH shq : share, shp:share, p: val, q: val, n: Z, m:Z, k:Z, contents: list byte
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (readable_share shq; writable_share shp; 0 <= k <= n;
       k <= m <= Int.max_unsigned) 
       LOCAL (temp 1%positive p; temp 2%positive q; temp 3%positive (Vint (Int.repr k)))
       SEP (@data_at cs shq (tarray tuchar m) (map Vubyte contents) q;
            @memory_block shp n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at shq (tarray tuchar m) (map Vubyte contents) q;
           data_at shp (tarray tuchar k) (map Vubyte (sublist 0 k contents)) p;
           memory_block shp (n-k) (offset_val k p)).

(*Definition memcpy_spec := (_memcpy, snd spec_sha.memcpy_spec). *)

(***************** We combine all specifications to a specification context *******)

(*Definition SHA256_spec := (_SHA256, snd spec_sha.SHA256_spec). *)(*
Definition sha256init_spec := (_SHA256_Init, snd SHA256_Init_spec).
Definition sha256update_spec := (_SHA256_Update, snd SHA256_Update_spec).
Definition sha256final_spec := (_SHA256_Final, snd SHA256_Final_spec).
Definition memset_spec := (_memset, snd spec_sha.memset_spec). *)

Definition Hkdf_VarSpecs : varspecs := (sha._K256, tarray tuint 64)::nil.


Definition hmac_init_funspec:=
    (WITH x : share * val * Z * list byte * globals + share * val * Z * list byte * globals * val
     PRE
     [(hmac._ctx, tptr spec_hmac.t_struct_hmac_ctx_st), (hmac._key, tptr tuchar),
     (hmac._len, tint)] match x with
                        | inl (sh,c, l, key, gv) =>
                            PROP ( )
                            LOCAL (temp hmac._ctx c; temp hmac._key nullval;
                                   temp hmac._len (Vint (Int.repr l)); gvars gv)
                            SEP (HMAC_SPEC.FULL sh key c; spec_sha.K_vector gv)
                        | inr (sh,c, l, key, gv, k) =>
                            PROP (spec_hmac.has_lengthK l key)
                            LOCAL (temp hmac._ctx c; temp hmac._key k;
                                   temp hmac._len (Vint (Int.repr l)); 
                                   gvars gv)
                            SEP (HMAC_SPEC.EMPTY sh c;
                                 data_block Tsh key k; 
                                 spec_sha.K_vector gv)
                        end
     POST [tvoid] match x with
                  | inl (sh,c, _, key, gv) =>
                      PROP ( )
                      LOCAL ()
                      SEP (HMAC_SPEC.REP sh
                             (HMAC_SPEC.hABS key []) c;
                           spec_sha.K_vector gv)
                  | inr (sh,c, _, key, gv, k) =>
                      PROP ( )
                      LOCAL ()
                      SEP (HMAC_SPEC.REP sh
                             (HMAC_SPEC.hABS key []) c;
                           data_block Tsh key k; 
                           spec_sha.K_vector gv)
                  end).

Definition Hkdf_FunSpecs : funspecs := ltac:(with_library prog (
  HKDF_spec :: HKDF_expand_spec :: HKDF_extract_spec :: 
  memcpy_tuchar_array_spec:: (*memcpy__data_at:: *)
  (*memset_spec::*)
  (HMAC_SPEC.hmac_update_spec)::
  (HMAC_SPEC.hmac_final_spec)::  
  (HMAC_SPEC.hmac_cleanup_spec)::  
  (_HMAC_Init, hmac_init_funspec)::
  (HMAC_SPEC.hmac_crypto_spec)::nil)).

Lemma change_compspecs_data_block: forall sh v,
  @data_block spec_hmac.CompSpecs sh v =
  @data_block CompSpecs sh v.
Proof.
  intros.
  unfold data_block.
  apply data_at_change_composite; auto.
Qed.

(*
Inductive augmentFunspecsResult :=
  OK_aFR: funspecs -> augmentFunspecsResult 
| DeleteErr_aFR: ident -> augmentFunspecsResult 
| NoDeletaErr_aFR: ident -> augmentFunspecsResult
| MismatchErr_aFR: list ident ->  augmentFunspecsResult.

Fixpoint my_augment_funspecs' (fds: list (ident * fundef)) (G:funspecs) :augmentFunspecsResult :=
 match fds with
 | (i,fd)::fds' => match delete_id i G with
                       | Some (f, G') => 
                              match my_augment_funspecs' fds' G' with
                               | OK_aFR G2 => OK_aFR ((i,f)::G2)
                               | DeleteErr_aFR i => DeleteErr_aFR i
                               | NoDeletaErr_aFR i => NoDeletaErr_aFR i
                               | MismatchErr_aFR l => MismatchErr_aFR l
                              end
                       | None =>
                              match my_augment_funspecs' fds' G with
                               | OK_aFR G2 => OK_aFR ((i, vacuous_funspec fd)::G2)
                               | DeleteErr_aFR i => DeleteErr_aFR i
                               | NoDeletaErr_aFR i => NoDeletaErr_aFR i
                               | MismatchErr_aFR l => MismatchErr_aFR l
                              end
                        end
 | nil => match G with nil => OK_aFR nil | (* _::_ => None*) (h::t) => MismatchErr_aFR (map fst (h::t)) end
 end.
(*
Fixpoint my_augment_funspecs' (fds: list (ident * fundef)) (G:funspecs) : option funspecs :=
 match fds with
 | (i,fd)::fds' => match delete_id i G with
                       | Some (f, G') => 
                              match my_augment_funspecs' fds' G' with
                               | Some G2 => Some ((i,f)::G2)
                               | None => None
                              end
                       | None =>
                              match my_augment_funspecs' fds' G with
                               | Some G2 => Some ((i, vacuous_funspec fd)::G2)
                               | None => None
                              end
                        end
 | nil => match G with nil => Some nil | _::_ => None end
 end.*)

Definition StringofPos (p:positive): string := String (Coq.Strings.Ascii.ascii_of_pos p) EmptyString.

Delimit Scope string_scope with string.
Bind Scope string_scope with string.
Open Local Scope string_scope.
Definition printlist (l:list ident):string := List.fold_right (fun p s => String (Coq.Strings.Ascii.ascii_of_pos p) s) EmptyString l.

Ltac mywith_library' p G :=
  let x := eval hnf in (my_augment_funspecs' (prog_funct p) G) in match x with
  | OK_aFR ?l => exact l
  | DeleteErr_aFR ?i => let v := constr:("Delete " ++ (StringofPos i)) in fail 5 v
  | NoDeletaErr_aFR ?i => let v:= constr:("NoDelete " ++ (StringofPos i)) in fail 5 v
  | MismatchErr_aFR ?l => let v := constr:("Mismatch " ++ printlist (map fst l))                                  
                          in fail 5 v
  end.

Ltac mywith_library prog G := mywith_library' prog G.
Locate _HMAC.
Definition Hkdf_FunSpecs : funspecs := ltac:(with_library prog (
(*  HKDF_spec :: HKDF_expand_spec :: HKDF_extract_spec :: 
  memcpy_spec:: (*memcpy__data_at:: *)
  (*memset_spec::*)
  HMAC_SPEC.hmac_update_spec::
  HMAC_SPEC.hmac_final_spec::  
  HMAC_SPEC.hmac_cleanup_spec::  
  (_HMAC_Init,hmac_init_funspec)::*)
  _HMAC, (snd HMAC_SPEC.hmac_crypto_spec)::nil)).
Definition Hkdf_FunSpecs : funspecs := ltac:(with_library prog (
  HKDF_spec :: HKDF_expand_spec :: HKDF_extract_spec :: 
  memcpy_spec:: (*memcpy__data_at:: *)
  (*memset_spec::*)
  HMAC_SPEC.hmac_update_spec::
  HMAC_SPEC.hmac_final_spec::  
  HMAC_SPEC.hmac_cleanup_spec::  
  (_HMAC_Init,hmac_init_funspec)::
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
*)