Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.HMAC256_DRBG_functional_prog.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.entropy.
Require Import sha.protocol_spec_hmac. 
Require Import sha.vst_lemmas.
Require Import sha.HMAC256_functional_prog.

(* mocked_md *)
Require Import sha.spec_sha.
Require Import VST.floyd.library.

Require Export hmacdrbg.hmac_drbg_compspecs.

Ltac fix_hmacdrbg_compspecs :=
  rewrite (@data_at__change_composite spec_hmac.CompSpecs hmac_drbg_compspecs.CompSpecs
            hmac_drbg_compspecs.CompSpecs_Preserve) by reflexivity.

Declare Module UNDER_SPEC : HMAC_ABSTRACT_SPEC.
Definition mdstate: Type := (val * (val * val))%type.

Definition md_info_state: Type := val%type.

Definition t_struct_md_ctx_st := Tstruct _mbedtls_md_context_t noattr.

Definition md_relate (key data : list byte) (r:mdstate) :=
  malloc_token Ews (Tstruct _hmac_ctx_st noattr) (snd (snd r)) *
  UNDER_SPEC.REP Ews (UNDER_SPEC.hABS key data) (snd (snd r)).

Definition md_full (key: list byte) (r:mdstate) :=
  malloc_token Ews (Tstruct _hmac_ctx_st noattr) (snd (snd r)) *
  UNDER_SPEC.FULL Ews key (snd (snd r)).

Definition md_empty (r:mdstate) := 
  malloc_token Ews (Tstruct _hmac_ctx_st noattr) (snd (snd r)) *
  UNDER_SPEC.EMPTY Ews (snd (snd r)).

Lemma md_relate_full: forall key data r, md_relate key data r |-- md_full key r.
Proof.
intros. unfold md_full, md_relate. cancel. apply UNDER_SPEC.REP_FULL.
Qed.

Lemma md_full_empty: forall key r, md_full key r |-- md_empty r.
Proof.
intros. unfold md_full, md_empty. cancel. apply UNDER_SPEC.FULL_EMPTY.
Qed.

Lemma md_empty_unfold: forall (r: mdstate), 
       md_empty r = 
       malloc_token Ews (Tstruct _hmac_ctx_st noattr) (snd (snd r)) *
       data_at_ Ews (Tstruct _hmac_ctx_st noattr) (snd (snd r)).
Proof.
intros.
unfold md_empty.
f_equal.
symmetry.
apply pred_ext.
eapply derives_trans; [ | apply UNDER_SPEC.mkEmpty].
fix_hmacdrbg_compspecs.
apply derives_refl.
eapply derives_trans.
apply UNDER_SPEC.EmptyDissolve.
fix_hmacdrbg_compspecs.
apply derives_refl.
Qed.

Hint Resolve UNDER_SPEC.FULL_isptr : saturate_local.
Hint Resolve UNDER_SPEC.EMPTY_isptr : saturate_local.
Hint Resolve UNDER_SPEC.REP_isptr : saturate_local.

Definition md_free_spec :=
 DECLARE _mbedtls_md_free
  WITH ctx:val, r:mdstate, sh: share
  PRE  [ _ctx OF tptr t_struct_md_ctx_st ]
       PROP(writable_share sh) 
       LOCAL(temp _ctx ctx) 
       SEP (data_at sh t_struct_md_ctx_st r ctx;
            md_empty r)
  POST [ tvoid ] 
       PROP () LOCAL () SEP (data_at sh t_struct_md_ctx_st r ctx).

Definition mbedtls_zeroize_spec :=
  DECLARE _mbedtls_zeroize
   WITH n: Z, v:val, sh: share
    PRE [_v OF tptr tvoid, _n OF tuint ] 
       PROP (writable_share sh; 0<=n<= Ptrofs.max_unsigned)
       LOCAL (temp _n (Vint (Int.repr n)); temp _v v)
       SEP (data_at_ sh (tarray tuchar n ) v)
    POST [ tvoid ]
       PROP () LOCAL () SEP (data_block sh (list_repeat (Z.to_nat n) Byte.zero) v).

Definition drbg_memcpy_spec :=
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

Definition drbg_memset_spec :=
  DECLARE _memset
   WITH sh : share, p: val, n: Z, c: int 
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tint, 3%positive OF tuint ]
       PROP (writable_share sh; 0 <= n <= Ptrofs.max_unsigned)
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
   WITH c : val, r: mdstate, sh: share, key:list byte, gv:globals
   PRE [ _ctx OF tptr (Tstruct _mbedtls_md_context_t noattr)]
         PROP (writable_share sh)
         LOCAL (temp _ctx c; gvars gv)
         SEP (md_full key r; 
              data_at sh (Tstruct _mbedtls_md_context_t noattr) r c; K_vector gv)
  POST [ tint ] 
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.zero)))
     SEP (md_relate key nil r;
          data_at sh (Tstruct _mbedtls_md_context_t noattr) r c;
          K_vector gv).

Definition md_starts_spec :=
  DECLARE _mbedtls_md_hmac_starts
   WITH c : val, shc: share, r: mdstate, l:Z, key:list byte, b:block, i:ptrofs, shk: share, gv: globals
   PRE [ _ctx OF tptr t_struct_md_ctx_st,
         _key OF tptr tuchar,
         _keylen OF tuint ]
         PROP (writable_share shc; readable_share shk;
                   sha.spec_hmac.has_lengthK l key)
         LOCAL (temp _ctx c; temp _key (Vptr b i); temp _keylen (Vint (Int.repr l));
                gvars gv)
         SEP (md_empty r;
              data_at shc t_struct_md_ctx_st r c;
              data_at shk (tarray tuchar (Zlength key)) (map Vubyte key) (Vptr b i); K_vector gv)
  POST [ tint ] 
     PROP ()
     LOCAL (temp ret_temp (Vint (Int.zero)))
     SEP (md_relate key nil r;
          data_at shc t_struct_md_ctx_st r c;
          data_at shk (tarray tuchar (Zlength key)) (map Vubyte key) (Vptr b i);
          K_vector gv).

Definition md_update_spec :=
  DECLARE _mbedtls_md_hmac_update
   WITH key: list byte, c : val, r:mdstate, wsh: share, d:val, sh: share, data:list byte, data1:list byte, gv: globals
   PRE [ _ctx OF tptr t_struct_md_ctx_st, 
         _input OF tptr tuchar, 
         _ilen OF tuint]
         PROP (writable_share wsh; readable_share sh;
               Zlength data1 + Zlength data + 64 < two_power_pos 61)
         LOCAL (temp _ctx c; temp _input d; temp  _ilen (Vint (Int.repr (Zlength data1)));
                gvars gv)
         SEP(md_relate key data r;
             data_at wsh t_struct_md_ctx_st r c;
             data_at sh (tarray tuchar (Zlength data1)) (map Vubyte data1) d; K_vector gv)
  POST [ tint ] 
          PROP () 
          LOCAL (temp ret_temp (Vint (Int.zero)))
          SEP(md_relate key (data ++ data1) r;
              data_at wsh t_struct_md_ctx_st r c; 
              data_at sh (tarray tuchar (Zlength data1)) (map Vubyte data1) d; K_vector gv).

Definition md_final_spec :=
  DECLARE _mbedtls_md_hmac_finish
   WITH data:list byte, key:list byte, c : val, r:mdstate, wsh: share, md:val, shmd: share, gv: globals
   PRE [ _ctx OF tptr t_struct_md_ctx_st,
         _output OF tptr tuchar ]
       PROP (writable_share wsh; writable_share shmd) 
       LOCAL (temp _output md; temp _ctx c; gvars gv)
       SEP(md_relate key data r;
             data_at wsh t_struct_md_ctx_st r c;
             K_vector gv;
             data_at_ shmd (tarray tuchar 32) md)
  POST [ tint ] 
          PROP () 
          LOCAL (temp ret_temp (Vint (Int.zero)))
          SEP(K_vector gv;
              md_full key r;
              data_at wsh t_struct_md_ctx_st r c;
              data_at shmd (tarray tuchar 32) (map Vubyte (HMAC256 data key)) md).

Definition md_setup_spec :=
  DECLARE _mbedtls_md_setup
   WITH md_ctx : mdstate, c:val, wsh: share, h:val, info:val
   PRE [ _ctx OF tptr (Tstruct _mbedtls_md_context_t noattr),
         _md_info OF tptr (Tstruct _mbedtls_md_info_t noattr),
         _hmac OF tint]
       PROP (writable_share wsh) 
       LOCAL (temp _md_info info; temp _ctx c; temp _hmac h)
       SEP(data_at wsh (Tstruct _mbedtls_md_context_t noattr) md_ctx c)
  POST [ tint ] EX r:_,
          PROP (r=0 \/ r=-20864) 
          LOCAL (temp ret_temp (Vint (Int.repr r)))
          SEP(if zeq r 0
              then (EX p: val, 
                         md_empty (info, (fst(snd md_ctx), p)) *
                         data_at wsh (Tstruct _mbedtls_md_context_t noattr) (info, (fst(snd md_ctx), p)) c)
             else data_at wsh (Tstruct _mbedtls_md_context_t noattr) md_ctx c).
(* end mocked_md *)

Inductive hmac256drbgabs :=
  HMAC256DRBGabs: forall (key: list byte) (V: list byte) (reseed_counter entropy_len: Z) (prediction_resistance: bool) (reseed_interval: Z), hmac256drbgabs.

Definition hmac256drbgstate: Type := (mdstate * (list val * (val * (val * (val * val)))))%type.

Definition hmac256drbg_relate (a: hmac256drbgabs) (r: hmac256drbgstate) : mpred :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               match r with (md_ctx', (V', (reseed_counter', (entropy_len', (prediction_resistance', reseed_interval'))))) =>
                            md_full key md_ctx'
                           && !! (
                                map Vubyte V = V'
                              /\ Zlength V = 32 
                              /\ Vint (Int.repr reseed_counter) = reseed_counter'
                              /\ Vint (Int.repr entropy_len) = entropy_len'
                              /\ Vint (Int.repr reseed_interval) = reseed_interval'
                              /\ Val.of_bool prediction_resistance = prediction_resistance'
                             )
               end
  end.

Definition hmac256drbgabs_entropy_len (a: hmac256drbgabs): Z :=
  match a with HMAC256DRBGabs _ _ _ entropy_len _ _ => entropy_len end.

Definition hmac256drbgabs_value (a: hmac256drbgabs): list byte :=
  match a with HMAC256DRBGabs _ V _ _ _ _ => V end.

Definition hmac256drbgabs_key (a: hmac256drbgabs): list byte :=
  match a with HMAC256DRBGabs key _ _ _ _ _ => key end.

Definition hmac256drbgabs_prediction_resistance (a: hmac256drbgabs): bool :=
  match a with HMAC256DRBGabs _ _ _ _ pr _ => pr end.

Definition hmac256drbgabs_reseed_counter (a: hmac256drbgabs): Z :=
  match a with HMAC256DRBGabs _ _ reseed_counter _ _ _ => reseed_counter end.

Definition hmac256drbgabs_reseed_interval (a: hmac256drbgabs): Z :=
  match a with HMAC256DRBGabs _ _ _ _ _ reseed_interval => reseed_interval end.

Definition hmac256drbgabs_increment_reseed_counter (a: hmac256drbgabs): hmac256drbgabs :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval => HMAC256DRBGabs key V (reseed_counter + 1) entropy_len prediction_resistance reseed_interval end.

Definition hmac256drbgabs_update_value (a: hmac256drbgabs) (new_value: list byte): hmac256drbgabs :=
  match a with HMAC256DRBGabs key _ reseed_counter entropy_len prediction_resistance reseed_interval => HMAC256DRBGabs key new_value reseed_counter entropy_len prediction_resistance reseed_interval end.

Definition hmac256drbgabs_update_key (a: hmac256drbgabs) (new_key: list byte): hmac256drbgabs :=
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
                            (md_ctx', (map Vubyte V, (Vint (Int.repr reseed_counter), (Vint (Int.repr entropy_len), (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval))))))
               end
  end.

Definition hmac256drbgabs_common_mpreds sh (final_state_abs: hmac256drbgabs) (old_state: hmac256drbgstate) (ctx: val) (info_contents: reptype t_struct_mbedtls_md_info): mpred :=
                  let st := hmac256drbgabs_to_state final_state_abs old_state in
                  (data_at sh t_struct_hmac256drbg_context_st st ctx) *
                  (data_at sh t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer st)) *
                  (hmac256drbg_relate final_state_abs st).

Definition hmac256drbgabs_hmac_drbg_update (a:hmac256drbgabs) (additional_data: list byte): hmac256drbgabs :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               let (key', V') := HMAC256_DRBG_update additional_data key V in
               HMAC256DRBGabs key' V' reseed_counter entropy_len prediction_resistance reseed_interval
  end.

Definition da_emp sh t v p := !! (p = nullval) && emp || 
                              !!(sizeof t > 0) && data_at sh t v p. (*in particular: weak_valid_ptr p in RHS case*)


Definition contents_with_add additional add_len contents:list byte := 
  if (andb (negb (eq_dec additional nullval)) (negb (eq_dec add_len 0))) then contents else [].

Definition hmac_drbg_update_spec :=
  DECLARE _mbedtls_hmac_drbg_update
   WITH contents: list byte,
        additional: val, sha: share, add_len: Z,
        ctx: val, shc: share, initial_state: hmac256drbgstate,
        I: hmac256drbgabs,
        info_contents: md_info_state, gv: globals
     PRE [ _ctx OF (tptr t_struct_hmac256drbg_context_st),
           _additional OF (tptr tuchar), _add_len OF tuint ]
       PROP (readable_share sha; writable_share shc;
         0 <= add_len <= Ptrofs.max_unsigned;
         Zlength (hmac256drbgabs_value I) = 32 (*Z.of_nat SHA256.DigestLength*);
         add_len = Zlength contents \/ add_len = 0
       )
       LOCAL (temp _ctx ctx;
              temp _additional additional;
              temp _add_len (Vint (Int.repr add_len));
              gvars gv)
       SEP (
         da_emp sha (tarray tuchar (Zlength contents)) (map Vubyte contents) additional;
         data_at shc t_struct_hmac256drbg_context_st initial_state ctx;
         hmac256drbg_relate I initial_state;
         data_at shc t_struct_mbedtls_md_info
                  info_contents (hmac256drbgstate_md_info_pointer initial_state);
         K_vector gv)
    POST [ tvoid ]
       PROP (
         )
       LOCAL ()
       SEP (
         hmac256drbgabs_common_mpreds shc
            (hmac256drbgabs_hmac_drbg_update I 
               (contents_with_add additional add_len contents))
            initial_state ctx info_contents;
         da_emp sha (tarray tuchar (Zlength contents)) (map Vubyte contents) additional;
         K_vector gv).

Definition mbedtls_HMAC256_DRBG_reseed_function (entropy_stream: ENTROPY.stream) (a:hmac256drbgabs)
           (additional_input: list byte): ENTROPY.result DRBG_state_handle :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               let sec_strength:Z := 32 (*not used -- measured in bytes, since that's how the calculations in DRBG_instantiate_function work *) in
               let state_handle: DRBG_state_handle := ((V, key, reseed_counter), sec_strength, prediction_resistance) in
               let max_additional_input_length := 256 
               in HMAC256_DRBG_reseed_function entropy_len entropy_len max_additional_input_length 
                     entropy_stream state_handle prediction_resistance additional_input
  end.

Definition hmac256drbgabs_reseed (a: hmac256drbgabs) (s: ENTROPY.stream) (additional_data: list byte) : hmac256drbgabs :=
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

Definition reseedPOST rv (contents : list byte) additional sha add_len s
          I ctx shc
          info_contents gv (initial_state: reptype t_struct_hmac256drbg_context_st):=
  if ((zlt 256 add_len) || (zlt 384 (hmac256drbgabs_entropy_len I + add_len)))%bool
  then (!!(rv = Vint (Int.neg (Int.repr 5))) &&
       (da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional *
         data_at shc t_struct_hmac256drbg_context_st initial_state ctx *
         hmac256drbg_relate I initial_state *
         data_at shc t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state) *
         Stream s * K_vector gv))
  else (!!(return_value_relate_result (mbedtls_HMAC256_DRBG_reseed_function s I 
            (contents_with_add additional add_len contents)) rv)
        && (hmac256drbgabs_common_mpreds shc (hmac256drbgabs_reseed I s 
             (contents_with_add additional add_len contents)) initial_state ctx info_contents *
         da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional *
         Stream (get_stream_result (mbedtls_HMAC256_DRBG_reseed_function s I (contents_with_add additional add_len contents))) *
         spec_sha.K_vector gv)).

(*384 equals MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT*)

Definition hmac_drbg_reseed_spec :=
  DECLARE _mbedtls_hmac_drbg_reseed
   WITH contents: list byte,
        additional: val, sha: share, add_len: Z,
        ctx: val, shc: share, initial_state: hmac256drbgstate,
        I: hmac256drbgabs,
        info_contents: md_info_state,
        s: ENTROPY.stream, gv: globals
    PRE [ _ctx OF (tptr t_struct_hmac256drbg_context_st), _additional OF (tptr tuchar), _len OF tuint ]
       PROP (readable_share sha; writable_share shc;
         0 <= add_len <= Ptrofs.max_unsigned;
         Zlength (hmac256drbgabs_value I) = 32 (*Z.of_nat SHA256.DigestLength*);
         add_len = Zlength contents;
         0 <= hmac256drbgabs_entropy_len I; 
         hmac256drbgabs_entropy_len I+ Zlength contents < Ptrofs.modulus;
         0 < hmac256drbgabs_entropy_len I + Zlength (contents_with_add additional add_len contents) < Ptrofs.modulus
       )
       LOCAL (temp _ctx ctx; temp _additional additional; temp _len (Vint (Int.repr add_len)); gvars gv)
       SEP (
         da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional;
         data_at shc t_struct_hmac256drbg_context_st initial_state ctx;
         hmac256drbg_relate I initial_state;
         data_at shc t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state);
         Stream s;
         K_vector gv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (reseedPOST ret_value contents additional sha add_len s
          I ctx shc
          info_contents gv initial_state).

Definition mbedtls_HMAC256_DRBG_generate_function (entropy_stream: ENTROPY.stream) (a:hmac256drbgabs) 
            (requested_number_of_bytes: Z) (additional_input: list byte): ENTROPY.result (list byte * DRBG_state_handle) :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               HMAC256_DRBG_generate_function (HMAC256_DRBG_reseed_function entropy_len entropy_len 256) 
                      (*10000*) reseed_interval 
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

Definition hmac256drbgabs_generate (a: hmac256drbgabs) (s: ENTROPY.stream) (bytes: Z) (additional_data: list byte) : hmac256drbgabs :=
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               match (mbedtls_HMAC256_DRBG_generate_function s a bytes additional_data) with
                 | ENTROPY.success (_, ((V', key', reseed_counter'), _, pr')) _ =>
                   HMAC256DRBGabs key' V' reseed_counter' entropy_len pr' reseed_interval
                 | ENTROPY.error _ _ => a
               end
  end.

Definition generatePOST ret_value (contents: list byte) additional sha add_len output sho out_len ctx shc initial_state I gv info_contents s :=
if out_len >? 1024
then (!!(ret_value = Vint (Int.neg (Int.repr 3))) &&
       (data_at_ sho (tarray tuchar out_len) output *
         da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional *
         data_at shc t_struct_hmac256drbg_context_st initial_state ctx *
         hmac256drbg_relate I initial_state *
         data_at shc t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state) *
         Stream s *
         K_vector gv))
else
  if (add_len >? 256)
  then (!!(ret_value = Vint (Int.neg (Int.repr 5))) &&
       (data_at_ sho (tarray tuchar out_len) output *
         da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional *
         data_at shc t_struct_hmac256drbg_context_st initial_state ctx *
         hmac256drbg_relate I initial_state *
         data_at shc t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state) *
         Stream s *
         K_vector gv))
  else let g := (mbedtls_HMAC256_DRBG_generate_function s I out_len (*contents*)(contents_with_add additional add_len contents))
       in (!!(return_value_relate_result g ret_value)) &&
          (match g with
            | ENTROPY.error _ _ => (data_at_ sho (tarray tuchar out_len) output)
            | ENTROPY.success (bytes, _) _ => (data_at sho (tarray tuchar out_len) (map Vubyte bytes) output)
          end *
          hmac256drbgabs_common_mpreds shc (hmac256drbgabs_generate I s out_len (*contents*)(contents_with_add additional add_len contents)) initial_state ctx info_contents *
          da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional *
          Stream (get_stream_result g) *
          K_vector gv).

Definition  RI_range (z:Z): Prop:= 0 < z /\ z+1 < Int.max_signed. (*Here*)

Definition hmac_drbg_generate_spec :=
  DECLARE _mbedtls_hmac_drbg_random_with_add
   WITH contents: list byte,
        additional: val, sha: share, add_len: Z,
        output: val, sho: share, out_len: Z,
        ctx: val, shc: share, initial_state: hmac256drbgstate,
        I: hmac256drbgabs,
        info_contents: md_info_state,
        s: ENTROPY.stream, gv: globals
    PRE [ _p_rng OF (tptr tvoid), _output OF (tptr tuchar), _out_len OF tuint, _additional OF (tptr tuchar), _add_len OF tuint ]
       PROP (readable_share sha; writable_share shc; writable_share sho;
         0 <= add_len <= Ptrofs.max_unsigned;
         0 <= out_len <= Ptrofs.max_unsigned;
         Zlength (hmac256drbgabs_value I) = 32 (*Z.of_nat SHA256.DigestLength*);
         add_len = Zlength contents;
         0 < hmac256drbgabs_entropy_len I; 
         hmac256drbgabs_entropy_len I + Zlength contents <= 384;
(*         hmac256drbgabs_reseed_interval I = 10000;*)
         RI_range (hmac256drbgabs_reseed_interval I) /\
         0 <= hmac256drbgabs_reseed_counter I < Int.max_signed
       )
       LOCAL (temp _p_rng ctx; temp _output output; temp _out_len (Vint (Int.repr out_len)); 
              temp _additional additional; temp _add_len (Vint (Int.repr add_len)); gvars gv)
       SEP (
         data_at_ sho (tarray tuchar out_len) output;
         da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional;
         data_at shc t_struct_hmac256drbg_context_st initial_state ctx;
         hmac256drbg_relate I initial_state;
         data_at shc t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state);
         Stream s;
         K_vector gv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (generatePOST ret_value contents additional sha add_len output sho out_len ctx shc initial_state I gv info_contents s).

Definition hmac_drbg_seed_buf_spec :=
  DECLARE _mbedtls_hmac_drbg_seed_buf
   WITH ctx: val, shc: share, info:val, d_len: Z, data:val, shd: share, Data: list byte,
        Ctx: hmac256drbgstate,
        CTX: hmac256drbgabs,
        Info: md_info_state, gv: globals
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _md_info OF (tptr (Tstruct _mbedtls_md_info_t noattr)),
         _data OF tptr tuchar, _data_len OF tuint ]
       PROP (writable_share shc; readable_share shd;
                 (d_len = Zlength Data \/ d_len=0) /\
              0 <= d_len <= Ptrofs.max_unsigned)
       LOCAL (temp _ctx ctx; temp _md_info info;
              temp _data_len (Vint (Int.repr d_len)); temp _data data; gvars gv)
       SEP (data_at shc t_struct_hmac256drbg_context_st Ctx ctx;
         hmac256drbg_relate CTX Ctx;
         data_at shc t_struct_mbedtls_md_info Info info;
         da_emp shd (tarray tuchar (Zlength Data)) (map Vubyte Data) data;
         K_vector gv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (data_at shc t_struct_mbedtls_md_info Info info *
            da_emp shd (tarray tuchar (Zlength Data)) (map Vubyte Data) data *
            K_vector gv;
            if Val.eq ret_value (Vint (Int.repr (-20864)))
            then data_at shc t_struct_hmac256drbg_context_st Ctx ctx *
                 hmac256drbg_relate CTX Ctx
            else match Ctx, CTX
                         with (mds, (V', (RC', (EL', (PR', RI'))))),
                              HMAC256DRBGabs key V RC EL PR RI
                         => EX KEY:list byte, EX VAL:list byte, EX p:val,
                          !!(HMAC256_DRBG_update (contents_with_add data d_len Data) V (list_repeat 32 Byte.one) = (KEY, VAL))
                             && md_full key mds *
                                data_at shc t_struct_hmac256drbg_context_st ((info, (fst(snd mds), p)), (map Vubyte VAL, (RC', (EL', (PR', RI'))))) ctx *
                                hmac256drbg_relate (HMAC256DRBGabs KEY VAL RC EL PR RI) ((info, (fst(snd mds), p)), (map Vubyte VAL, (RC', (EL', (PR', RI')))))
                        end).

Definition GetEntropy_PostSep sh len s buf :=
  match ENTROPY.get_bytes (Z.to_nat len) s with
            | ENTROPY.error _ _ => memory_block sh len buf
            | ENTROPY.success bytes _ =>
              data_at sh (tarray tuchar len) (map Vubyte bytes) buf
                 end.

Definition get_entropy_spec :=
  DECLARE _get_entropy
   WITH
        sh: share,
        s: ENTROPY.stream,
        buf: val, len: Z
    PRE [ 1%positive OF (tptr tuchar), 2%positive OF tuint ]
       PROP (
         0 <= len <= Ptrofs.max_unsigned;
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
         GetEntropy_PostSep sh len s buf
         (*Unfolded definition is not permitted here any longer, as of approx May29th
           (match ENTROPY.get_bytes (Z.to_nat len) s with
            | ENTROPY.error _ _ => memory_block sh len buf
            | ENTROPY.success bytes _ =>
              data_at sh (tarray tuchar len) (map Vint (map Int.repr (bytes))) buf
                 end)*)
       ).

Definition size_of_HMACDRBGCTX:Z:= sizeof (Tstruct _mbedtls_hmac_drbg_context noattr).

Definition hmac_drbg_init_spec :=
  DECLARE _mbedtls_hmac_drbg_init
   WITH c : val, shc: share
   PRE [ _ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr) ]
         PROP (writable_share shc) 
         LOCAL (temp _ctx c)
         SEP(memory_block shc size_of_HMACDRBGCTX c)
  POST [ tvoid ]  
          PROP () 
          LOCAL ()
          SEP(data_at shc (tarray tuchar size_of_HMACDRBGCTX)
                (list_repeat (Z.to_nat size_of_HMACDRBGCTX) (Vint Int.zero)) c).

Definition hmac_drbg_random_spec :=
  DECLARE _mbedtls_hmac_drbg_random
   WITH output: val, sho: share, out_len: Z,
        ctx: val, shc: share, initial_state: hmac256drbgstate,
        I: hmac256drbgabs,
        info_contents: md_info_state,
        s: ENTROPY.stream, gv: globals
    PRE [_p_rng OF tptr tvoid, _output OF tptr tuchar, _out_len OF tuint ]
       PROP (writable_share sho; writable_share shc;
         0 <= out_len <= Ptrofs.max_unsigned;
         Zlength (hmac256drbgabs_value I) = 32 (*Z.of_nat SHA256.DigestLength*);
         0 < hmac256drbgabs_entropy_len I <= 384;
         RI_range (hmac256drbgabs_reseed_interval I);
         0 <= hmac256drbgabs_reseed_counter I < Int.max_signed)
       LOCAL (temp _p_rng ctx; temp _output output;
              temp _out_len (Vint (Int.repr out_len)); gvars gv)
       SEP (
         data_at_ sho (tarray tuchar out_len) output;
         data_at shc t_struct_hmac256drbg_context_st initial_state ctx;
         hmac256drbg_relate I initial_state;
         data_at shc t_struct_mbedtls_md_info info_contents (hmac256drbgstate_md_info_pointer initial_state);
         Stream s;
         K_vector gv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (generatePOST ret_value nil nullval Tsh 0 output sho out_len ctx shc initial_state I gv info_contents s).

(*********************************** hmac_drbg_seed specification ******************************)

(*Parameter max_personalization_string_length: Z. (*NIST SP 800-90A, page 38, Table2: 2^35 bits;
         Our personalization string is a list of bytes, so have max length 2^32*)
  Axiom max_personalization_string336: 336 <= max_personalization_string_length.*)
  (*Definition max_personalization_string_length: Z := 20. *)(*Appendix B2 of NIST SP 800-90A says: 160 bits. We measure in bytes*)
Definition max_personalization_string_length: Z := 336. (*= MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT -48*) 

(*Max entropy_length*)
Definition max_elength: Z:= 2^32. (*bytes. NIST SP 800-90A, page 38, Table2: 2^35 bits*)

Definition instantiate_function_256  (es: ENTROPY.stream) (prflag: bool)
            (pers_string: list byte): ENTROPY.result DRBG_state_handle :=
   if (Zlength pers_string) >? max_personalization_string_length 
   then ENTROPY.error ENTROPY.generic_error es
   else let secStrength := 32
        in  match get_entropy (secStrength+secStrength/2) (secStrength+secStrength/2) max_elength prflag es
            with ENTROPY.error e s' => ENTROPY.error ENTROPY.catastrophic_error s'
               | ENTROPY.success entropy s' =>
                   let initial_working_state := HMAC256_DRBG_instantiate_algorithm entropy nil pers_string secStrength
                   in ENTROPY.success (initial_working_state, secStrength, prflag) s'                    
            end.

Inductive hmac_any:=
  hmac_any_empty: hmac_any
| hmac_any_rep: forall key data : list byte, hmac_any
| hmac_any_full: forall k:list byte, hmac_any.

Definition hmac_interp (d:hmac_any) (r: mdstate):mpred :=
  match d with
    hmac_any_empty => md_empty r
  | hmac_any_rep key data => md_relate key data r
  | hmac_any_full k => md_full k r
  end.

Definition preseed_relate d rc pr ri (r : hmac256drbgstate):mpred:=
    match r with
     (md_ctx', (V', (reseed_counter', (entropy_len', (prediction_resistance', reseed_interval'))))) =>
    hmac_interp d md_ctx' &&
    !! (map Vubyte initial_key = V' /\
        (Vint (Int.repr rc) = reseed_counter')  (*Explicitly reset in sucessful runs of reseed and hence seed*)
        (*Vint (Int.repr entropy_len) = entropy_len' Explicitly set in seed*) /\
        Vint (Int.repr ri) = reseed_interval' /\
        Val.of_bool pr = prediction_resistance')
   end.

(*specification for the expected case, in which 0<=len<=256.
  Also, use instantiate_function_256 in PROP of PRE, and assume SUCCESS.
  Alternative specs (and proofs can be found in verif_hmac_drbg_NISTseed.v*)
Definition hmac_drbg_seed_inst256_spec :=
  DECLARE _mbedtls_hmac_drbg_seed
   WITH dp:_, ctx: val, shc: share, info:val, len: Z, data:val, shd: share, Data: list byte,
        Ctx: hmac256drbgstate,
        Info: md_info_state, s:ENTROPY.stream, rc:Z, pr_flag:bool, ri:Z,
        handle_ss: DRBG_state_handle * ENTROPY.stream, gv: globals
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _md_info OF tptr (Tstruct _mbedtls_md_info_t noattr),
         _custom OF tptr tuchar, _len OF tuint ]
       PROP (writable_share shc; readable_share shd;
             len = Zlength Data /\ 0 <= len <=256 /\ 
             instantiate_function_256 s pr_flag (contents_with_add data (Zlength Data) Data)
               = ENTROPY.success (fst handle_ss) (snd handle_ss))
       LOCAL (temp _ctx ctx; temp _md_info info;
              temp _len (Vint (Int.repr len)); temp _custom data; gvars gv)
       SEP (
         data_at shc t_struct_hmac256drbg_context_st Ctx ctx;
         preseed_relate dp rc pr_flag ri Ctx;
         data_at shc t_struct_mbedtls_md_info Info info;
         da_emp shd (tarray tuchar (Zlength Data)) (map Vubyte Data) data;
         K_vector gv; Stream s)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp (Vint ret_value))
       SEP (data_at shc t_struct_mbedtls_md_info Info info;
            da_emp shd (tarray tuchar (Zlength Data)) (map Vubyte Data) data;
            K_vector gv;
            if Int.eq ret_value (Int.repr (-20864))
            then data_at shc t_struct_hmac256drbg_context_st Ctx ctx *
                 preseed_relate dp rc pr_flag ri Ctx * Stream s
            else !!(ret_value = Int.zero) && 
                 md_empty (fst Ctx) *
                 EX p:val, (* malloc_token Ews (Tstruct _hmac_ctx_st noattr) p * *)
                 match (fst Ctx, fst handle_ss) with
                     ((M1, (M2, M3)), ((((newV, newK), newRC), newEL), newPR)) =>
                   let CtxFinal := ((info, (M2, p)),
                                            (map Vubyte newV, (Vint (Int.repr newRC), (Vint (Int.repr 32), (Val.of_bool newPR, Vint (Int.repr 10000)))))) 
                   in data_at shc t_struct_hmac256drbg_context_st CtxFinal ctx *
                      hmac256drbg_relate (HMAC256DRBGabs newK newV newRC 32 newPR 10000) CtxFinal *
                      Stream (snd handle_ss) 
                end).

(*********************************** end of hmac_drbg_seed specification ******************************)
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
   WITH ctx:val, shc: share, CTX:hmac256drbgstate, ABS:_, r:bool
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _resistance OF tint ]
       PROP ( writable_share shc)
       LOCAL (temp _ctx ctx; temp _resistance (Val.of_bool r))
       SEP (data_at shc t_struct_hmac256drbg_context_st CTX ctx;
            hmac256drbg_relate ABS CTX)
    POST [ tvoid ]
       PROP () 
       LOCAL ()
       SEP (data_at shc t_struct_hmac256drbg_context_st (setPR_CTX (Val.of_bool r) CTX) ctx;
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
   WITH ctx:val, shc: share, CTX:hmac256drbgstate, ABS:_, l:_
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _len OF tuint ]
       PROP (writable_share shc )
       LOCAL (temp _ctx ctx; temp _len (Vint (Int.repr l)))
       SEP (data_at shc t_struct_hmac256drbg_context_st CTX ctx;
            hmac256drbg_relate ABS CTX)
    POST [ tvoid ]
       PROP () 
       LOCAL ()
       SEP (data_at shc t_struct_hmac256drbg_context_st (setEL_CTX (Vint (Int.repr l)) CTX) ctx;
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
   WITH ctx:val, shc: share, CTX:hmac256drbgstate, ABS:_, l:_
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _interval OF tint ]
       PROP (writable_share shc )
       LOCAL (temp _ctx ctx; temp _interval (Vint (Int.repr l)))
       SEP (data_at shc t_struct_hmac256drbg_context_st CTX ctx;
            hmac256drbg_relate ABS CTX)
    POST [ tvoid ]
       PROP () 
       LOCAL ()
       SEP (data_at shc t_struct_hmac256drbg_context_st (setRI_CTX (Vint (Int.repr l)) CTX) ctx;
            hmac256drbg_relate (setRI_ABS l ABS) (setRI_CTX (Vint (Int.repr l)) CTX)).

Definition hmac_drbg_free_spec :=
  DECLARE _mbedtls_hmac_drbg_free
   WITH ctx:val, shc: share, CTX:hmac256drbgstate, ABS:_
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr) ]
       PROP (writable_share shc )
       LOCAL (temp _ctx ctx)
       SEP (da_emp shc t_struct_hmac256drbg_context_st CTX ctx;
            if Val.eq ctx nullval then emp else
                 hmac256drbg_relate ABS CTX)
    POST [ tvoid ] 
      EX vret:unit, PROP ()
       LOCAL ()
       SEP (if Val.eq ctx nullval then emp else data_block shc (list_repeat (Z.to_nat size_of_HMACDRBGCTX) Byte.zero) ctx).

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
    (WITH x : val * share * Z * list byte * globals + val * share * Z * list byte * block * ptrofs * share * globals
     PRE
     [(hmac._ctx, tptr spec_hmac.t_struct_hmac_ctx_st), (hmac._key, tptr tuchar),
     (hmac._len, tint)] match x with
                        | inl (c, sh, l, key, gv) =>
                            PROP (writable_share sh)
                            LOCAL (temp hmac._ctx c; temp hmac._key nullval;
                            temp hmac._len (Vint (Int.repr l)); 
                            gvars gv)
                            SEP (UNDER_SPEC.FULL sh key c;
                            spec_sha.K_vector gv)
                        | inr (c, sh, l, key, b0, i, shk, gv) =>
                            PROP (writable_share sh; readable_share shk; spec_hmac.has_lengthK l key)
                            LOCAL (temp hmac._ctx c; temp hmac._key (Vptr b0 i);
                            temp hmac._len (Vint (Int.repr l)); 
                            gvars gv)
                            SEP (UNDER_SPEC.EMPTY sh c;
                            data_block shk key (Vptr b0 i); 
                            spec_sha.K_vector gv)
                        end
     POST [tvoid] match x with
                  | inl (c, sh, _, key, gv) =>
                      PROP ( )
                      LOCAL ()
                      SEP (UNDER_SPEC.REP sh
                             (UNDER_SPEC.hABS key []) c;
                      spec_sha.K_vector gv)
                  | inr (c, sh, _, key, b0, i, shk, gv) =>
                      PROP ( )
                      LOCAL ()
                      SEP (UNDER_SPEC.REP sh
                             (UNDER_SPEC.hABS key []) c;
                      data_block shk key (Vptr b0 i); 
                      spec_sha.K_vector gv)
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
Proof.
  unfold ndfs_merge. simpl. rewrite if_true; trivial.
  f_equal.
  unfold hmac_init_funspec.
  f_equal.
  + extensionality.
    destruct x as [[[[c l] key] gv] | [[[[[c l] key] b0] i] gv]].
    - auto.
    - change_compspecs CompSepcs.
      auto.
  + extensionality.
    destruct x as [[[[c l] key] gv] | [[[[[c l] key] b0] i] gv]].
    - auto.
    - change_compspecs CompSepcs.
      auto.
Qed.

Definition HmacDrbgFunSpecs : funspecs :=  ltac:(with_library prog (
  md_free_spec ::hmac_drbg_free_spec::mbedtls_zeroize_spec::
  hmac_drbg_setReseedInterval_spec::hmac_drbg_setEntropyLen_spec::
  hmac_drbg_setPredictionResistance_spec::hmac_drbg_random_spec::hmac_drbg_init_spec::
  hmac_drbg_seed_inst256_spec::
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
