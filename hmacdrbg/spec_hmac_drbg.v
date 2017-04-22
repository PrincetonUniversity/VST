Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.HMAC256_DRBG_functional_prog.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.entropy.
Require Import sha.protocol_spec_hmac. 
Require Import sha.general_lemmas.
Require Import sha.HMAC256_functional_prog.

(* mocked_md *)
Require Import sha.spec_sha.
Require Import floyd.library.

Require Import hmacdrbg.hmac_drbg_compspecs.

Declare Module UNDER_SPEC : HMAC_ABSTRACT_SPEC.
Definition mdstate: Type := (val * (val * val))%type.

Definition md_info_state: Type := val%type.

Definition t_struct_md_ctx_st := Tstruct _mbedtls_md_context_t noattr.

Definition md_relate (h: UNDER_SPEC.HABS) (r:mdstate) :=
  UNDER_SPEC.REP h (snd (snd r)).

Definition md_full (key: list Z) (r:mdstate) :=
  UNDER_SPEC.FULL key (snd (snd r)).

Definition md_empty (r:mdstate) := 
  UNDER_SPEC.EMPTY (snd (snd r)).

Lemma FULL_isptr k q:
  UNDER_SPEC.FULL k q = !!isptr q && UNDER_SPEC.FULL k q.
Proof.
apply pred_ext.
+ apply andp_right; trivial. apply UNDER_SPEC.FULL_isptr.
+ entailer!.
Qed.

Lemma EMPTY_isptr q:
  UNDER_SPEC.EMPTY q = !!isptr q && UNDER_SPEC.EMPTY q.
Proof.
apply pred_ext.
+ apply andp_right; trivial. apply UNDER_SPEC.EMPTY_isptr.
+ entailer!.
Qed.

Lemma REP_isptr abs q:
  UNDER_SPEC.REP abs q = !!isptr q && UNDER_SPEC.REP abs q.
Proof.
destruct abs.
apply pred_ext.
+ apply andp_right; trivial. apply UNDER_SPEC.REP_isptr.
+ entailer!.
Qed. 

Definition md_free_spec :=
 DECLARE _mbedtls_md_free
  WITH ctx:val, r:mdstate
  PRE  [ _ctx OF tptr (Tstruct _mbedtls_md_context_t noattr) ]
       PROP() 
       LOCAL(temp _ctx ctx) 
       SEP (data_at Tsh t_struct_md_ctx_st r ctx;
            UNDER_SPEC.EMPTY (snd (snd r)); 
            malloc_token Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) (snd (snd r)))
  POST [ tvoid ] 
    SEP (data_at Tsh t_struct_md_ctx_st r ctx).

Definition mbedtls_zeroize_spec :=
  DECLARE _mbedtls_zeroize
   WITH n: Z, v:val
    PRE [_v OF tptr tvoid, _n OF tuint ] 
       PROP (0<=n<= Int.max_unsigned)
       LOCAL (temp _n (Vint (Int.repr n)); temp _v v)
       SEP (data_at_ Tsh (tarray tuchar n ) v)
    POST [ tvoid ]
       SEP (data_block Tsh (list_repeat (Z.to_nat n) 0) v).

Definition drbg_memcpy_spec :=
  DECLARE _memcpy
   WITH sh : share*share, p: val, q: val, n: Z, contents: list int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (readable_share (fst sh); writable_share (snd sh); 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive q; temp 3%positive (Vint (Int.repr n)))
       SEP (data_at (fst sh) (tarray tuchar n) (map Vint contents) q;
              memory_block (snd sh) n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at (fst sh) (tarray tuchar n) (map Vint contents) q;
             data_at (snd sh) (tarray tuchar n) (map Vint contents) p).

Definition drbg_memset_spec :=
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
(*This results in using sha's compspecs
Definition drbg_memset_spec := (_memset, snd spec_sha.memset_spec). 
Definition drbg_memcpy_spec := (_memcpy, snd spec_sha.memcpy_spec). 
*)

Definition md_get_size_spec :=
  DECLARE _mbedtls_md_get_size
   WITH u:unit
   PRE [ _md_info OF tptr (Tstruct _mbedtls_md_info_t noattr)]
         PROP ()
         LOCAL ()
         SEP ()
  POST [ tuchar ] 
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.repr (32 (*Z.of_nat SHA256.DigestLength*)))))
     SEP ().

Definition md_reset_spec :=
  DECLARE _mbedtls_md_hmac_reset
   WITH c : val, r: mdstate, key:list Z, kv:val
   PRE [ _ctx OF tptr (Tstruct _mbedtls_md_context_t noattr)]
         PROP ()
         LOCAL (temp _ctx c; gvar sha._K256 kv)
         SEP (UNDER_SPEC.FULL key (snd (snd r)); 
              data_at Tsh (Tstruct _mbedtls_md_context_t noattr) r c; K_vector kv)
  POST [ tint ] 
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.zero)))
     SEP (md_relate (UNDER_SPEC.hABS key nil) r;
          data_at Tsh (Tstruct _mbedtls_md_context_t noattr) r c;
          K_vector kv).

Definition md_starts_spec :=
  DECLARE _mbedtls_md_hmac_starts
   WITH c : val, r: mdstate, l:Z, key:list Z, kv:val, b:block, i:Int.int
   PRE [ _ctx OF tptr t_struct_md_ctx_st,
         _key OF tptr tuchar,
         _keylen OF tuint ]
         PROP (sha.spec_hmac.has_lengthK l key; Forall isbyteZ key)
         LOCAL (temp _ctx c; temp _key (Vptr b i); temp _keylen (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP (UNDER_SPEC.EMPTY (snd (snd r));
              data_at Tsh t_struct_md_ctx_st r c;
              data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr b i); K_vector kv)
  POST [ tint ] 
     PROP (Forall isbyteZ key)
     LOCAL (temp ret_temp (Vint (Int.zero)))
     SEP (md_relate (UNDER_SPEC.hABS key nil) r;
          data_at Tsh t_struct_md_ctx_st r c;
          data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr b i);
          K_vector kv).

Definition md_update_spec :=
  DECLARE _mbedtls_md_hmac_update
   WITH key: list Z, c : val, r:mdstate, d:val, data:list Z, data1:list Z, kv:val
   PRE [ _ctx OF tptr t_struct_md_ctx_st, 
         _input OF tptr tuchar, 
         _ilen OF tuint]
         PROP (0 <= Zlength data1 <= Int.max_unsigned;
               Zlength data1 + Zlength data + 64 < two_power_pos 61;
               Forall isbyteZ data1)
         LOCAL (temp _ctx c; temp _input d; temp  _ilen (Vint (Int.repr (Zlength data1)));
                gvar sha._K256 kv)
         SEP(md_relate (UNDER_SPEC.hABS key data) r;
             data_at Tsh t_struct_md_ctx_st r c;
             data_at Tsh (tarray tuchar (Zlength data1)) (map Vint (map Int.repr data1)) d; K_vector kv)
  POST [ tint ] 
          PROP (Forall isbyteZ data1) 
          LOCAL (temp ret_temp (Vint (Int.zero)))
          SEP(md_relate (UNDER_SPEC.hABS key (data ++ data1)) r;
              data_at Tsh t_struct_md_ctx_st r c; 
              data_at Tsh (tarray tuchar (Zlength data1)) (map Vint (map Int.repr data1)) d; K_vector kv).

Definition md_final_spec :=
  DECLARE _mbedtls_md_hmac_finish
   WITH data:list Z, key:list Z, c : val, r:mdstate, md:val, shmd: share, kv:val
   PRE [ _ctx OF tptr t_struct_md_ctx_st,
         _output OF tptr tuchar ]
       PROP (writable_share shmd) 
       LOCAL (temp _output md; temp _ctx c;
              gvar sha._K256 kv)
       SEP((md_relate (UNDER_SPEC.hABS key data) r);
           (data_at Tsh t_struct_md_ctx_st r c);
           (K_vector kv);
           (memory_block shmd 32 md))
  POST [ tint ] 
          PROP (Forall isbyteZ (HMAC256 data key)) 
          LOCAL (temp ret_temp (Vint (Int.zero)))
          SEP(K_vector kv;
              UNDER_SPEC.FULL key (snd (snd r));
              data_at Tsh t_struct_md_ctx_st r c;
              data_at shmd (tarray tuchar (Zlength (HMAC256 data key))) (map Vint (map Int.repr (HMAC256 data key))) md).

Definition md_setup_spec :=
  DECLARE _mbedtls_md_setup
   WITH md_ctx : mdstate, c:val, h:val, info:val
   PRE [ _ctx OF tptr (Tstruct _mbedtls_md_context_t noattr),
         _md_info OF tptr (Tstruct _mbedtls_md_info_t noattr),
         _hmac OF tint]
       PROP () 
       LOCAL (temp _md_info info; temp _ctx c; temp _hmac h)
       SEP(data_at Tsh (Tstruct _mbedtls_md_context_t noattr) md_ctx c)
  POST [ tint ] EX r:_,
          PROP (r=0 \/ r=-20864) 
          LOCAL (temp ret_temp (Vint (Int.repr r)))
          SEP( 
              if zeq r 0
              then (EX p:_, !!malloc_compatible (sizeof (Tstruct _hmac_ctx_st noattr)) p && 
                              memory_block Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
                              malloc_token Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
                              data_at Tsh (Tstruct _mbedtls_md_context_t noattr) (info, (fst(snd md_ctx), p)) c)
              else data_at Tsh (Tstruct _mbedtls_md_context_t noattr) md_ctx c).
(* end mocked_md *)

Inductive hmac256drbgabs :=
  HMAC256DRBGabs: forall (key: list Z) (V: list Z) (reseed_counter entropy_len: Z) (prediction_resistance: bool) (reseed_interval: Z), hmac256drbgabs.

Definition hmac256drbgstate: Type := (mdstate * (list val * (val * (val * (val * val)))))%type.

Definition hmac256drbg_relate (a: hmac256drbgabs) (r: hmac256drbgstate) : mpred :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               match r with (md_ctx', (V', (reseed_counter', (entropy_len', (prediction_resistance', reseed_interval'))))) =>
                            md_full key md_ctx'
                                      && !! (
                                        map Vint (map Int.repr V) = V'
                                        /\ Zlength V = 32 /\ Forall isbyteZ V
                                        /\ Vint (Int.repr reseed_counter) = reseed_counter'
                                        /\ Vint (Int.repr entropy_len) = entropy_len'
                                        /\ Vint (Int.repr reseed_interval) = reseed_interval'
                                        /\ Val.of_bool prediction_resistance = prediction_resistance'
                                      )
               end
  end.

Definition hmac256drbgstate_md_FULL key (r: hmac256drbgstate) : mpred :=
  md_full key (fst r).

Definition hmac256drbgabs_entropy_len (a: hmac256drbgabs): Z :=
  match a with HMAC256DRBGabs _ _ _ entropy_len _ _ => entropy_len end.

Definition hmac256drbgabs_value (a: hmac256drbgabs): list Z :=
  match a with HMAC256DRBGabs _ V _ _ _ _ => V end.

Definition hmac256drbgabs_key (a: hmac256drbgabs): list Z :=
  match a with HMAC256DRBGabs key _ _ _ _ _ => key end.

Definition hmac256drbgabs_prediction_resistance (a: hmac256drbgabs): bool :=
  match a with HMAC256DRBGabs _ _ _ _ pr _ => pr end.

Definition hmac256drbgabs_reseed_counter (a: hmac256drbgabs): Z :=
  match a with HMAC256DRBGabs _ _ reseed_counter _ _ _ => reseed_counter end.

Definition hmac256drbgabs_reseed_interval (a: hmac256drbgabs): Z :=
  match a with HMAC256DRBGabs _ _ _ _ _ reseed_interval => reseed_interval end.

Definition hmac256drbgabs_increment_reseed_counter (a: hmac256drbgabs): hmac256drbgabs :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval => HMAC256DRBGabs key V (reseed_counter + 1) entropy_len prediction_resistance reseed_interval end.

Definition hmac256drbgabs_update_value (a: hmac256drbgabs) (new_value: list Z): hmac256drbgabs :=
  match a with HMAC256DRBGabs key _ reseed_counter entropy_len prediction_resistance reseed_interval => HMAC256DRBGabs key new_value reseed_counter entropy_len prediction_resistance reseed_interval end.

Definition hmac256drbgabs_update_key (a: hmac256drbgabs) (new_key: list Z): hmac256drbgabs :=
  match a with HMAC256DRBGabs _ V reseed_counter entropy_len prediction_resistance reseed_interval => HMAC256DRBGabs new_key V reseed_counter entropy_len prediction_resistance reseed_interval end.

Definition hmac256drbgabs_update_reseed_counter (a: hmac256drbgabs) (new_counter: Z): hmac256drbgabs :=
  match a with HMAC256DRBGabs key V _ entropy_len prediction_resistance reseed_interval => HMAC256DRBGabs key V new_counter entropy_len prediction_resistance reseed_interval end.

Definition hmac256drbgabs_metadata_same (a: hmac256drbgabs) (b: hmac256drbgabs): Prop :=
  match a with HMAC256DRBGabs _ _ reseed_counter entropy_len prediction_resistance reseed_interval =>
               match b with HMAC256DRBGabs _ _ reseed_counter' entropy_len' prediction_resistance' reseed_interval' =>
                            reseed_counter = reseed_counter'
                            /\ entropy_len = entropy_len'
                            /\ prediction_resistance = prediction_resistance'
                            /\ reseed_interval = reseed_interval'
               end
  end.

Definition hmac256drbgabs_of_state_handle (a: DRBG_state_handle) entropy_len reseed_interval: hmac256drbgabs :=
  match a with ((V, key, reseed_counter),_, prediction_resistance) =>
               HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval
  end.

Definition hmac256drbgabs_to_state_handle (a: hmac256drbgabs): DRBG_state_handle :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               ((V, key, reseed_counter), 32(*256*) (* security strength, not used *), prediction_resistance)
  end.

Definition hmac256drbgstate_md_info_pointer (a: hmac256drbgstate): val := fst (fst a).

Definition t_struct_mbedtls_md_info := Tstruct _mbedtls_md_info_t noattr.

Definition t_struct_hmac256drbg_context_st := Tstruct _mbedtls_hmac_drbg_context noattr.

Definition hmac256drbgabs_to_state (a: hmac256drbgabs) (old: hmac256drbgstate):hmac256drbgstate :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               match old with (md_ctx', _) =>
                            (md_ctx', (map Vint (map Int.repr V), (Vint (Int.repr reseed_counter), (Vint (Int.repr entropy_len), (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval))))))
               end
  end.

Definition hmac256drbgabs_common_mpreds (final_state_abs: hmac256drbgabs) (old_state: hmac256drbgstate) (ctx: val) (info_contents: reptype t_struct_mbedtls_md_info): mpred :=
                  let st := hmac256drbgabs_to_state final_state_abs old_state in
                  (data_at Tsh t_struct_hmac256drbg_context_st st ctx) *
                  (data_at Tsh t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer st)) *
                  (hmac256drbg_relate final_state_abs st).

Definition hmac256drbgabs_hmac_drbg_update (a:hmac256drbgabs) (additional_data: list Z): hmac256drbgabs :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               let (key', V') := HMAC256_DRBG_update additional_data key V in
               HMAC256DRBGabs key' V' reseed_counter entropy_len prediction_resistance reseed_interval
  end.

Definition da_emp sh t v p := !! (p = nullval) && emp || 
                              !!(sizeof t > 0) && data_at sh t v p. (*in particular: weak_valid_ptr p in RHS case*)


Definition contents_with_add additional add_len contents:list Z := 
  if (andb (negb (eq_dec additional nullval)) (negb (eq_dec add_len 0))) then contents else [].

Definition hmac_drbg_update_spec :=
  DECLARE _mbedtls_hmac_drbg_update
   WITH contents: list Z,
        additional: val, add_len: Z,
        ctx: val, initial_state: hmac256drbgstate,
        initial_state_abs: hmac256drbgabs,
        kv: val, info_contents: md_info_state
     PRE [ _ctx OF (tptr t_struct_hmac256drbg_context_st),
           _additional OF (tptr tuchar), _add_len OF tuint ]
       PROP (
         0 <= add_len <= Int.max_unsigned;
         Zlength (hmac256drbgabs_value initial_state_abs) = 32 (*Z.of_nat SHA256.DigestLength*);
         add_len = Zlength contents \/ add_len = 0;
         Forall isbyteZ (hmac256drbgabs_value initial_state_abs);
         Forall isbyteZ contents
       )
       LOCAL (temp _ctx ctx;
              temp _additional additional;
              temp _add_len (Vint (Int.repr add_len));
              gvar sha._K256 kv)
       SEP (
         da_emp Tsh (tarray tuchar (Zlength contents)) (map Vint (map Int.repr contents)) additional;
         data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx;
         hmac256drbg_relate initial_state_abs initial_state;
         data_at Tsh t_struct_mbedtls_md_info
                  info_contents (hmac256drbgstate_md_info_pointer initial_state);
         K_vector kv)
    POST [ tvoid ]
       PROP (
         )
       LOCAL ()
       SEP (
         hmac256drbgabs_common_mpreds
            (hmac256drbgabs_hmac_drbg_update initial_state_abs 
               (contents_with_add additional add_len contents))
            initial_state ctx info_contents;
         da_emp Tsh (tarray tuchar (Zlength contents)) (map Vint (map Int.repr contents)) additional;
         K_vector kv).

Definition mbedtls_HMAC256_DRBG_reseed_function (entropy_stream: ENTROPY.stream) (a:hmac256drbgabs)
           (additional_input: list Z): ENTROPY.result DRBG_state_handle :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               let sec_strength:Z := 32 (*not used -- measured in bytes, since that's how the calculations in DRBG_instantiate_function work *) in
               let state_handle: DRBG_state_handle := ((V, key, reseed_counter), sec_strength, prediction_resistance) in
               let max_additional_input_length := 256 
               in HMAC256_DRBG_reseed_function entropy_len entropy_len max_additional_input_length 
                     entropy_stream state_handle prediction_resistance additional_input
  end.

Definition hmac256drbgabs_reseed (a: hmac256drbgabs) (s: ENTROPY.stream) (additional_data: list Z) : hmac256drbgabs :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               match (mbedtls_HMAC256_DRBG_reseed_function s a additional_data) with
                 | ENTROPY.success ((V', key', reseed_counter'), _, pr') _ =>
                   HMAC256DRBGabs key' V' reseed_counter' entropy_len pr' reseed_interval
                 | ENTROPY.error _ _ => a
               end
  end.

Definition get_stream_result {X} (result: ENTROPY.result X): ENTROPY.stream :=
  match result with
    | ENTROPY.success _ s => s
    | ENTROPY.error _ s => s
  end.

Definition result_success {X} (result: ENTROPY.result X): Prop :=
  match result with
    | ENTROPY.success _ _ => True
    | ENTROPY.error _ _ => False
  end.

Parameter ENT_GenErr: Z.
Parameter ENT_GenErrAx: Vzero <> Vint (Int.repr ENT_GenErr)  /\ Int.repr ENT_GenErr <> Int.repr (-20864).

Definition return_value_relate_result {X} (result: ENTROPY.result X) (ret_value: val): Prop :=
  match result with
    | ENTROPY.error e _ => match e with
                             | ENTROPY.generic_error => ret_value = Vint (Int.repr ENT_GenErr) (*WAS: ret_value <> Vzero*)
                             | ENTROPY.catastrophic_error => ret_value = Vint (Int.repr (-9))
                           end
    | ENTROPY.success _ _ => ret_value = Vzero
  end.

Parameter Stream: ENTROPY.stream -> mpred.

Definition reseedPOST rv contents additional add_len s
          initial_state_abs ctx
          info_contents kv (initial_state: reptype t_struct_hmac256drbg_context_st):=
  if ((zlt 256 add_len) || (zlt 384 (hmac256drbgabs_entropy_len initial_state_abs + add_len)))%bool
  then (!!(rv = Vint (Int.neg (Int.repr 5))) &&
       (da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
         data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx *
         hmac256drbg_relate initial_state_abs initial_state *
         data_at Tsh t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state) *
         Stream s * K_vector kv))
  else (!!(return_value_relate_result (mbedtls_HMAC256_DRBG_reseed_function s initial_state_abs 
            (contents_with_add additional add_len contents)) rv)
        && (hmac256drbgabs_common_mpreds (hmac256drbgabs_reseed initial_state_abs s 
             (contents_with_add additional add_len contents)) initial_state ctx info_contents *
         da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
         Stream (get_stream_result (mbedtls_HMAC256_DRBG_reseed_function s initial_state_abs (contents_with_add additional add_len contents))) *
         spec_sha.K_vector kv)).

(*384 equals MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT*)

Definition hmac_drbg_reseed_spec :=
  DECLARE _mbedtls_hmac_drbg_reseed
   WITH contents: list Z,
        additional: val, add_len: Z,
        ctx: val, initial_state: hmac256drbgstate,
        initial_state_abs: hmac256drbgabs,
        kv: val, info_contents: md_info_state,
        s: ENTROPY.stream
    PRE [ _ctx OF (tptr t_struct_hmac256drbg_context_st), _additional OF (tptr tuchar), _len OF tuint ]
       PROP (
         0 <= add_len <= Int.max_unsigned;
         Zlength (hmac256drbgabs_value initial_state_abs) = 32 (*Z.of_nat SHA256.DigestLength*);
         add_len = Zlength contents;
         0 <= hmac256drbgabs_entropy_len initial_state_abs; 
         hmac256drbgabs_entropy_len initial_state_abs+ Zlength contents < Int.modulus;
         0 < hmac256drbgabs_entropy_len initial_state_abs + Zlength (contents_with_add additional add_len contents) < Int.modulus;
         Forall isbyteZ (hmac256drbgabs_value initial_state_abs);
         Forall isbyteZ contents
       )
       LOCAL (temp _ctx ctx; temp _additional additional; temp _len (Vint (Int.repr add_len)); gvar sha._K256 kv)
       SEP (
         da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
         data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx;
         hmac256drbg_relate initial_state_abs initial_state;
         data_at Tsh t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state);
         Stream s;
         K_vector kv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (reseedPOST ret_value contents additional add_len s
          initial_state_abs ctx
          info_contents kv initial_state).

Definition mbedtls_HMAC256_DRBG_generate_function (entropy_stream: ENTROPY.stream) (a:hmac256drbgabs) 
            (requested_number_of_bytes: Z) (additional_input: list Z): ENTROPY.result (list Z * DRBG_state_handle) :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               HMAC256_DRBG_generate_function (HMAC256_DRBG_reseed_function entropy_len entropy_len 256) 
                      10000(* reseed_interval *) 
                      1024 (*max_number_of_bytes_per_request*)
                      256 (*max_additional_input_length*) 
                      entropy_stream
                      ((V, key, reseed_counter), 
                        32(*256*) (*max security strength in bytes, not used *), 
                        prediction_resistance) 
                      requested_number_of_bytes 
                      32 (*requested security strength, not used *)
                      prediction_resistance additional_input
  end.

Definition hmac256drbgabs_generate (a: hmac256drbgabs) (s: ENTROPY.stream) (bytes: Z) (additional_data: list Z) : hmac256drbgabs :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               match (mbedtls_HMAC256_DRBG_generate_function s a bytes additional_data) with
                 | ENTROPY.success (_, ((V', key', reseed_counter'), _, pr')) _ =>
                   HMAC256DRBGabs key' V' reseed_counter' entropy_len pr' reseed_interval
                 | ENTROPY.error _ _ => a
               end
  end.

Definition generatePOST ret_value contents additional add_len output out_len ctx initial_state initial_state_abs kv info_contents s :=
if out_len >? 1024
then (!!(ret_value = Vint (Int.neg (Int.repr 3))) &&
       (data_at_ Tsh (tarray tuchar out_len) output *
         da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
         data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx *
         hmac256drbg_relate initial_state_abs initial_state *
         data_at Tsh t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state) *
         Stream s *
         K_vector kv))
else
  if (add_len >? 256)
  then (!!(ret_value = Vint (Int.neg (Int.repr 5))) &&
       (data_at_ Tsh (tarray tuchar out_len) output *
         da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
         data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx *
         hmac256drbg_relate initial_state_abs initial_state *
         data_at Tsh t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state) *
         Stream s *
         K_vector kv))
  else let g := (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len (*contents*)(contents_with_add additional add_len contents))
       in (!!(return_value_relate_result g ret_value)) &&
          (match g with
            | ENTROPY.error _ _ => (data_at_ Tsh (tarray tuchar out_len) output)
            | ENTROPY.success (bytes, _) _ => (data_at Tsh (tarray tuchar out_len) (map Vint (map Int.repr bytes)) output)
          end *
          hmac256drbgabs_common_mpreds (hmac256drbgabs_generate initial_state_abs s out_len (*contents*)(contents_with_add additional add_len contents)) initial_state ctx info_contents *
          da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
          Stream (get_stream_result g) *
          K_vector kv).

Definition hmac_drbg_generate_spec :=
  DECLARE _mbedtls_hmac_drbg_random_with_add
   WITH contents: list Z,
        additional: val, add_len: Z,
        output: val, out_len: Z,
        ctx: val, initial_state: hmac256drbgstate,
        initial_state_abs: hmac256drbgabs,
        kv: val, info_contents: md_info_state,
        s: ENTROPY.stream
    PRE [ _p_rng OF (tptr tvoid), _output OF (tptr tuchar), _out_len OF tuint, _additional OF (tptr tuchar), _add_len OF tuint ]
       PROP (
         0 <= add_len <= Int.max_unsigned;
         0 <= out_len <= Int.max_unsigned;
         Zlength (hmac256drbgabs_value initial_state_abs) = 32 (*Z.of_nat SHA256.DigestLength*);
         add_len = Zlength contents;
         0 < hmac256drbgabs_entropy_len initial_state_abs; 
         hmac256drbgabs_entropy_len initial_state_abs + Zlength contents <= 384;
         hmac256drbgabs_reseed_interval initial_state_abs = 10000;
         0 <= hmac256drbgabs_reseed_counter initial_state_abs <= Int.max_signed;
         Forall isbyteZ (hmac256drbgabs_value initial_state_abs);
         Forall isbyteZ contents
       )
       LOCAL (temp _p_rng ctx; temp _output output; temp _out_len (Vint (Int.repr out_len)); 
              temp _additional additional; temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
       SEP (
         data_at_ Tsh (tarray tuchar out_len) output;
         da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
         data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx;
         hmac256drbg_relate initial_state_abs initial_state;
         data_at Tsh t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state);
         Stream s;
         K_vector kv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (generatePOST ret_value contents additional add_len output out_len ctx initial_state initial_state_abs kv info_contents s).

Definition hmac_drbg_seed_buf_spec :=
  DECLARE _mbedtls_hmac_drbg_seed_buf
   WITH ctx: val, info:val, d_len: Z, data:val, Data: list Z,
        Ctx: hmac256drbgstate,
        CTX: hmac256drbgabs,
        kv: val, Info: md_info_state
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _md_info OF (tptr (Tstruct _mbedtls_md_info_t noattr)),
         _data OF tptr tuchar, _data_len OF tuint ]
       PROP ( (d_len = Zlength Data \/ d_len=0) /\
              0 <= d_len <= Int.max_unsigned /\ Forall isbyteZ Data)
       LOCAL (temp _ctx ctx; temp _md_info info;
              temp _data_len (Vint (Int.repr d_len)); temp _data data; gvar sha._K256 kv)
       SEP (
         data_at Tsh t_struct_hmac256drbg_context_st Ctx ctx;
         hmac256drbg_relate CTX Ctx;
         data_at Tsh t_struct_mbedtls_md_info Info info;
         da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data;
         K_vector kv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (data_at Tsh t_struct_mbedtls_md_info Info info *
            da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data *
            K_vector kv;
            orp ( !!(ret_value = Vint (Int.repr (-20864))) &&
                  data_at Tsh t_struct_hmac256drbg_context_st Ctx ctx *
                  hmac256drbg_relate CTX Ctx)
                ( !!(ret_value <> Vint (Int.repr (-20864))) &&
                  match Ctx, CTX
                  with (mds, (V', (RC', (EL', (PR', RI'))))),
                              HMAC256DRBGabs key V RC EL PR RI
                     => EX KEY:list Z, EX VAL:list Z, EX p:val,
                          !!(HMAC256_DRBG_update (contents_with_add data d_len Data) V (list_repeat 32 1) = (KEY, VAL))
                          && md_full key mds * malloc_token Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
                             data_at Tsh t_struct_hmac256drbg_context_st ((info, (fst(snd mds), p)), (map Vint (map Int.repr VAL), (RC', (EL', (PR', RI'))))) ctx *
                             hmac256drbg_relate (HMAC256DRBGabs KEY VAL RC EL PR RI) ((info, (fst(snd mds), p)), (map Vint (map Int.repr VAL), (RC', (EL', (PR', RI')))))
                  end)
       ).


Definition get_entropy_spec :=
  DECLARE _get_entropy
   WITH
        sh: share,
        s: ENTROPY.stream,
        buf: val, len: Z
    PRE [ 1%positive OF (tptr tuchar), 2%positive OF tuint ]
       PROP (
         0 <= len <= Int.max_unsigned;
         writable_share sh
       )
       LOCAL (temp 1%positive buf; temp 2%positive (Vint (Int.repr len)))
       SEP (
         memory_block sh len buf;
         (Stream s)
           )
    POST [ tint ]
       EX ret_value:_,
       PROP (
           return_value_relate_result (get_entropy 0 len len false s) ret_value
         )
       LOCAL (temp ret_temp ret_value)
       SEP (
         Stream (get_stream_result (get_entropy 0 len len false s));
         (match ENTROPY.get_bytes (Z.to_nat len) s with
            | ENTROPY.error _ _ => memory_block sh len buf
            | ENTROPY.success bytes _ =>
              data_at sh (tarray tuchar len) (map Vint (map Int.repr (bytes))) buf
                 end)
       ).

Definition size_of_HMACDRBGCTX:Z:= sizeof (Tstruct _mbedtls_hmac_drbg_context noattr).

Definition hmac_drbg_init_spec :=
  DECLARE _mbedtls_hmac_drbg_init
   WITH c : val
   PRE [ _ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr) ]
         PROP () 
         LOCAL (temp _ctx c)
         SEP(memory_block Tsh size_of_HMACDRBGCTX c)
  POST [ tvoid ]  
          PROP () 
          LOCAL ()
          SEP(data_at Tsh (tarray tuchar size_of_HMACDRBGCTX)
                (list_repeat (Z.to_nat size_of_HMACDRBGCTX) (Vint Int.zero)) c).

Definition hmac_drbg_random_spec :=
  DECLARE _mbedtls_hmac_drbg_random
   WITH output: val, out_len: Z,
        ctx: val, initial_state: hmac256drbgstate,
        initial_state_abs: hmac256drbgabs,
        kv: val, info_contents: md_info_state,
        s: ENTROPY.stream
    PRE [_p_rng OF tptr tvoid, _output OF tptr tuchar, _out_len OF tuint ]
       PROP ( 
         0 <= out_len <= Int.max_unsigned;
         Zlength (hmac256drbgabs_value initial_state_abs) = 32 (*Z.of_nat SHA256.DigestLength*);
         0 < hmac256drbgabs_entropy_len initial_state_abs <= 384;
         hmac256drbgabs_reseed_interval initial_state_abs = 10000;
         0 <= hmac256drbgabs_reseed_counter initial_state_abs <= Int.max_signed;
         Forall isbyteZ (hmac256drbgabs_value initial_state_abs))
       LOCAL (temp _p_rng ctx; temp _output output;
              temp _out_len (Vint (Int.repr out_len)); gvar sha._K256 kv)
       SEP (
         data_at_ Tsh (tarray tuchar out_len) output;
         data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx;
         hmac256drbg_relate initial_state_abs initial_state;
         data_at Tsh t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state);
         Stream s;
         K_vector kv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (generatePOST ret_value nil nullval 0 output out_len ctx initial_state initial_state_abs kv info_contents s).

Definition setPR_ABS res (a: hmac256drbgabs): hmac256drbgabs :=
  match a with HMAC256DRBGabs key V x el r reseed_interval => 
               HMAC256DRBGabs key V x el res reseed_interval
  end.

Definition setPR_CTX res (r: hmac256drbgstate): hmac256drbgstate :=
  match r with (md_ctx, (V, (rc, (el, (r, ri))))) => 
               (md_ctx, (V, (rc, (el, (res, ri))))) 
  end.

Definition hmac_drbg_setPredictionResistance_spec :=
  DECLARE _mbedtls_hmac_drbg_set_prediction_resistance 
   WITH ctx:val, CTX:hmac256drbgstate, ABS:_, r:bool
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _resistance OF tint ]
       PROP ( )
       LOCAL (temp _ctx ctx; temp _resistance (Val.of_bool r))
       SEP (data_at Tsh t_struct_hmac256drbg_context_st CTX ctx;
            hmac256drbg_relate ABS CTX)
    POST [ tvoid ]
       SEP (data_at Tsh t_struct_hmac256drbg_context_st (setPR_CTX (Val.of_bool r) CTX) ctx;
            hmac256drbg_relate (setPR_ABS r ABS) (setPR_CTX (Val.of_bool r) CTX)).

Definition setEL_ABS el (a: hmac256drbgabs): hmac256drbgabs :=
  match a with HMAC256DRBGabs key V x _ pr reseed_interval => 
               HMAC256DRBGabs key V x el pr reseed_interval
  end.

Definition setEL_CTX el (r: hmac256drbgstate): hmac256drbgstate :=
  match r with (md_ctx, (V, (rc, (_, (pr, ri))))) => 
               (md_ctx, (V, (rc, (el, (pr, ri))))) 
  end.

Definition hmac_drbg_setEntropyLen_spec :=
  DECLARE _mbedtls_hmac_drbg_set_entropy_len
   WITH ctx:val, CTX:hmac256drbgstate, ABS:_, l:_
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _len OF tuint ]
       PROP ( )
       LOCAL (temp _ctx ctx; temp _len (Vint (Int.repr l)))
       SEP (data_at Tsh t_struct_hmac256drbg_context_st CTX ctx;
            hmac256drbg_relate ABS CTX)
    POST [ tvoid ]
       SEP (data_at Tsh t_struct_hmac256drbg_context_st (setEL_CTX (Vint (Int.repr l)) CTX) ctx;
            hmac256drbg_relate (setEL_ABS l ABS) (setEL_CTX (Vint (Int.repr l)) CTX)).

Definition setRI_ABS ri (a: hmac256drbgabs): hmac256drbgabs :=
  match a with HMAC256DRBGabs key V x el pr _ => 
               HMAC256DRBGabs key V x el pr ri
  end.

Definition setRI_CTX ri (r: hmac256drbgstate): hmac256drbgstate :=
  match r with (md_ctx, (V, (rc, (el, (pr, _))))) => 
               (md_ctx, (V, (rc, (el, (pr, ri))))) 
  end.

Definition hmac_drbg_setReseedInterval_spec :=
  DECLARE _mbedtls_hmac_drbg_set_reseed_interval
   WITH ctx:val, CTX:hmac256drbgstate, ABS:_, l:_
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _interval OF tint ]
       PROP ( )
       LOCAL (temp _ctx ctx; temp _interval (Vint (Int.repr l)))
       SEP (data_at Tsh t_struct_hmac256drbg_context_st CTX ctx;
            hmac256drbg_relate ABS CTX)
    POST [ tvoid ]
       SEP (data_at Tsh t_struct_hmac256drbg_context_st (setRI_CTX (Vint (Int.repr l)) CTX) ctx;
            hmac256drbg_relate (setRI_ABS l ABS) (setRI_CTX (Vint (Int.repr l)) CTX)).


Definition hmac_drbg_free_spec :=
  DECLARE _mbedtls_hmac_drbg_free
   WITH ctx:val, CTX:hmac256drbgstate, ABS:_
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr) ]
       PROP ( )
       LOCAL (temp _ctx ctx)
       SEP (da_emp Tsh t_struct_hmac256drbg_context_st CTX ctx;
            if Val.eq ctx nullval then emp else
                 (hmac256drbg_relate ABS CTX *
                  malloc_token Tsh 324 (snd(snd (fst CTX)))))
    POST [ tvoid ] 
      EX vret:unit, PROP ()
       LOCAL ()
       SEP (if Val.eq ctx nullval then emp else data_block Tsh (list_repeat (Z.to_nat size_of_HMACDRBGCTX) 0) ctx).

Definition HmacDrbgVarSpecs : varspecs := (sha._K256, tarray tuint 64)::nil.

Definition ndfs_merge fA cA A PA QA FSA (HFSA: FSA = NDmk_funspec fA cA A PA QA) 
                    fB cB B PB QB FSB (HFSB: FSB = NDmk_funspec fB cB B PB QB): option funspec.
destruct (eq_dec fA fB); subst.
+ destruct (eq_dec cA cB); subst.
  - apply Some. eapply (NDmk_funspec fB cB (A+B) 
         (fun x => match x with inl a => PA a | inr b => PB b end)
         (fun x => match x with inl a => QA a | inr b => QB b end)).
  - apply None.
+ apply None.
Defined.
(*
Definition fs_merge (fA fB: funspec): option funspec :=
 match fA, fB with (mk_funspec sgA ccA A PreA PostA), (mk_funspec sgB ccB B PreB PostB) =>
  if eq_dec sgA sgB 
  then if eq_dec ccA ccB
       then Some (mk_funspec sgB ccB (A+B)
                   (fun x => match x with inl a => PreA a | inr b => PreB b end)
                   (fun x => match x with inl a => PostA a | inr b => PostB b end))
       else None
  else None
 end.
*)

Definition hmac_init_funspec:=
    (WITH x : val * Z * list Z * val + val * Z * list Z * val * block * int PRE
     [(hmac._ctx, tptr spec_hmac.t_struct_hmac_ctx_st), (hmac._key, tptr tuchar),
     (hmac._len, tint)] match x with
                        | inl (c, l, key, kv) =>
                            PROP ( )
                            LOCAL (temp hmac._ctx c; temp hmac._key nullval;
                            temp hmac._len (Vint (Int.repr l)); 
                            gvar sha._K256 kv)
                            SEP (UNDER_SPEC.FULL key c;
                            spec_sha.K_vector kv)
                        | inr (c, l, key, kv, b0, i) =>
                            PROP (spec_hmac.has_lengthK l key)
                            LOCAL (temp hmac._ctx c; temp hmac._key (Vptr b0 i);
                            temp hmac._len (Vint (Int.repr l)); 
                            gvar sha._K256 kv)
                            SEP (UNDER_SPEC.EMPTY c;
                            spec_sha.data_block Tsh key (Vptr b0 i); 
                            spec_sha.K_vector kv)
                        end
     POST [tvoid] match x with
                  | inl (c, _, key, kv) =>
                      PROP ( )
                      LOCAL ()
                      SEP (UNDER_SPEC.REP
                             (UNDER_SPEC.hABS key []) c;
                      spec_sha.K_vector kv)
                  | inr (c, _, key, kv, b0, i) =>
                      PROP ( )
                      LOCAL ()
                      SEP (UNDER_SPEC.REP
                             (UNDER_SPEC.hABS key []) c;
                      spec_sha.data_block Tsh key (Vptr b0 i); 
                      spec_sha.K_vector kv)
                  end).
(*
Lemma hmac_init_merge: 
  fs_merge (snd UNDER_SPEC.hmac_reset_spec)
           (snd UNDER_SPEC.hmac_starts_spec)
  = Some hmac_init_funspec.
Proof. simpl. rewrite if_true; trivial. Qed.*)

Lemma hmac_init_merge: 
  ndfs_merge _ _ _ _ _ (snd UNDER_SPEC.hmac_reset_spec) (eq_refl _)
             _ _ _ _ _ (snd UNDER_SPEC.hmac_starts_spec) (eq_refl _)
  = Some hmac_init_funspec.
Proof. unfold ndfs_merge. simpl. rewrite if_true; trivial. Qed. 

Definition HmacDrbgFunSpecs : funspecs :=  ltac:(with_library prog (
  md_free_spec ::hmac_drbg_free_spec::mbedtls_zeroize_spec::
  hmac_drbg_setReseedInterval_spec::hmac_drbg_setEntropyLen_spec::
  hmac_drbg_setPredictionResistance_spec::hmac_drbg_random_spec::hmac_drbg_init_spec::
  hmac_drbg_update_spec::
  hmac_drbg_reseed_spec::
  hmac_drbg_generate_spec::hmac_drbg_seed_buf_spec ::
  get_entropy_spec::
  md_reset_spec::md_final_spec::md_update_spec::
  md_starts_spec::md_setup_spec::md_get_size_spec::

  UNDER_SPEC.hmac_update_spec::
  UNDER_SPEC.hmac_final_spec:: 
  (hmac._HMAC_Init,hmac_init_funspec)::

  drbg_memcpy_spec:: drbg_memset_spec::
  sha.spec_hmac.sha256init_spec::sha.spec_hmac.sha256update_spec::sha.spec_hmac.sha256final_spec::nil)).
