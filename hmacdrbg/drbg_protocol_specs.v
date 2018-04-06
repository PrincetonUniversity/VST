Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import sha.general_lemmas.
Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.entropy.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.

Require Import sha.HMAC256_functional_prog.
Require Import hmacdrbg.entropy_lemmas.
Require Import VST.floyd.library.

Require Import hmacdrbg.HMAC256_DRBG_bridge_to_FCF.

Definition WF (I:hmac256drbgabs):=
         Zlength (hmac256drbgabs_value I) = 32 /\ 
         0 < hmac256drbgabs_entropy_len I <= 384 /\
         RI_range (hmac256drbgabs_reseed_interval I) /\
         0 <= hmac256drbgabs_reseed_counter I < Int.max_signed /\
         Forall isbyteZ (hmac256drbgabs_value I).

Definition REP gv (Info:md_info_state) (A:hmac256drbgabs) (v: val): mpred :=
  EX a:hmac256drbgstate, 
       (!! WF A) &&
          data_at Tsh t_struct_hmac256drbg_context_st a v
          * hmac256drbg_relate A a
          * data_at Tsh t_struct_mbedtls_md_info Info (hmac256drbgstate_md_info_pointer a)
          * spec_sha.K_vector gv.

Definition AREP gv (A:hmac256drbgabs) (v: val): mpred :=
  EX Info:md_info_state, REP gv Info A v. 

Definition seedREP dp rc pr ri gv (Info:md_info_state) (info:val) (v: val): mpred :=
  EX a:hmac256drbgstate, 
          data_at Tsh t_struct_hmac256drbg_context_st a v
          * preseed_relate dp rc pr ri a
          * data_at Tsh t_struct_mbedtls_md_info Info info
          * spec_sha.K_vector gv.

Definition seedbufREP gv (Info:md_info_state) (info:val) (A:hmac256drbgabs) (v: val): mpred :=
  EX a:hmac256drbgstate,
     !! (0 < hmac256drbgabs_entropy_len A <= 384 /\
         RI_range (hmac256drbgabs_reseed_interval A) /\
         0 <= hmac256drbgabs_reseed_counter A < Int.max_signed)
     && data_at Tsh t_struct_hmac256drbg_context_st a v
          * hmac256drbg_relate A a
          * data_at Tsh t_struct_mbedtls_md_info Info info
          * spec_sha.K_vector gv.

(*TODO: init, free*)

(*based on hmac_drbg_seed_inst256_spec*)
Definition drbg_seed_inst256_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_seed
   WITH dp:_, ctx: val, info:val, len: Z, data:val, Data: list Z,
        Info: md_info_state, s:ENTROPY.stream, rc:Z, pr_flag:bool, ri:Z,
        handle_ss: DRBG_functions.DRBG_state_handle * ENTROPY.stream, gv: globals
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _md_info OF tptr (Tstruct _mbedtls_md_info_t noattr),
         _custom OF tptr tuchar, _len OF tuint ]
       PROP (len = Zlength Data /\ 0 <= len <=256 /\ Forall isbyteZ Data /\
             instantiate_function_256 s pr_flag (contents_with_add data (Zlength Data) Data)
               = ENTROPY.success (fst handle_ss) (snd handle_ss))
       LOCAL (temp _ctx ctx; temp _md_info info;
              temp _len (Vint (Int.repr len)); temp _custom data; gvars gv)
       SEP (seedREP dp rc pr_flag ri gv Info info ctx; Stream s;
            da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp (Vint ret_value))
       SEP (da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data;
            if Int.eq ret_value (Int.repr (-20864))
            then seedREP dp rc pr_flag ri gv Info info ctx * Stream s                 
            else !!(ret_value = Int.zero) &&                  
                 EX p:val, malloc_token Tsh (Tstruct _hmac_ctx_st noattr) p *
                 match fst handle_ss with ((((newV, newK), newRC), newEL), newPR) =>
                    AREP gv (HMAC256DRBGabs newK newV newRC 32 newPR 10000) ctx *
                    Stream (snd handle_ss) * EX mds:mdstate, md_empty mds   
                 end).

Definition drbg_seed_buf_abs_spec :=
  DECLARE _mbedtls_hmac_drbg_seed_buf
   WITH ctx: val, info:val, d_len: Z, data:val, Data: list Z,
        I: hmac256drbgabs, Info:md_info_state,
        gv: globals
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _md_info OF (tptr (Tstruct _mbedtls_md_info_t noattr)),
         _data OF tptr tuchar, _data_len OF tuint ]
       PROP (d_len = Zlength Data \/ d_len=0;
             0 <= d_len <= Int.max_unsigned; Forall isbyteZ Data)
       LOCAL (temp _ctx ctx; temp _md_info info;
              temp _data_len (Vint (Int.repr d_len)); temp _data data; gvars gv)
       SEP (seedbufREP gv Info info I ctx;
            da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data *
            if Val.eq ret_value (Vint (Int.repr (-20864)))
            then seedbufREP gv Info info I ctx
            else match I with HMAC256DRBGabs key V RC EL PR RI =>
                 EX KEY:list Z, EX VAL:list Z, EX p:val, EX mds:mdstate,
                 !!(hmacdrbg.HMAC256_DRBG_functional_prog.HMAC256_DRBG_update (contents_with_add data d_len Data) V (list_repeat 32 1) = (KEY, VAL))
                 && md_full key mds * malloc_token Tsh (Tstruct _hmac_ctx_st noattr) p *
                 REP gv Info (HMAC256DRBGabs KEY VAL RC EL PR RI) ctx end).

Definition drbg_setPredictionResistance_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_set_prediction_resistance 
   WITH ctx:val, A:_, r:bool, gv:globals
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _resistance OF tint ]
       PROP ( )
       LOCAL (temp _ctx ctx; temp _resistance (Val.of_bool r))
       SEP (AREP gv A ctx)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (AREP gv (setPR_ABS r A) ctx).


Definition drbg_setEntropyLen_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_set_entropy_len
   WITH ctx:val, A:_, l:_, gv:globals
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _len OF tuint ]
       PROP ( 0 < l <= 384 )
       LOCAL (temp _ctx ctx; temp _len (Vint (Int.repr l)))
       SEP (AREP gv A ctx)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (AREP gv (setEL_ABS l A) ctx).

Definition drbg_setReseedInterval_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_set_reseed_interval
   WITH ctx:val, A:_, ri:_, gv:globals
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _interval OF tint ]
       PROP (RI_range ri )
       LOCAL (temp _ctx ctx; temp _interval (Vint (Int.repr ri)))
       SEP (AREP gv A ctx)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (AREP gv (setRI_ABS ri A) ctx).

Definition drbg_update_abs_spec :=
  DECLARE _mbedtls_hmac_drbg_update
   WITH contents: list Z,
        additional: val, add_len: Z,
        ctx: val, I: hmac256drbgabs,
        gv: globals
     PRE [ _ctx OF (tptr t_struct_hmac256drbg_context_st),
           _additional OF (tptr tuchar), _add_len OF tuint ]
       PROP (0 <= add_len <= Int.max_unsigned;
             add_len = Zlength contents \/ add_len = 0;
             Forall isbyteZ contents)
       LOCAL (temp _ctx ctx;
              temp _additional additional;
              temp _add_len (Vint (Int.repr add_len));
              gvars gv)
       SEP (AREP gv I ctx;
            da_emp Tsh (tarray tuchar (Zlength contents)) (map Vint (map Int.repr contents)) additional)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (AREP gv (hmac256drbgabs_hmac_drbg_update I (contents_with_add additional add_len contents)) ctx;
            da_emp Tsh (tarray tuchar (Zlength contents)) (map Vint (map Int.repr contents)) additional).

Definition drbg_reseed_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_reseed
   WITH contents: list Z,
        additional: val, add_len: Z,
        ctx: val, I: hmac256drbgabs,
        s: ENTROPY.stream, gv: globals
    PRE [ _ctx OF (tptr t_struct_hmac256drbg_context_st), _additional OF (tptr tuchar), _len OF tuint ]
       PROP (0 <= add_len <= Int.max_unsigned;
             add_len = Zlength contents;
             0 < hmac256drbgabs_entropy_len I + Zlength (contents_with_add additional add_len contents) < Int.modulus;         
             Forall isbyteZ contents)
       LOCAL (temp _ctx ctx; temp _additional additional; temp _len (Vint (Int.repr add_len)); gvars gv)
       SEP ( da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
              AREP gv I ctx; Stream s)
    POST [ tint ]
       EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (if ((zlt 256 add_len) || (zlt 384 (hmac256drbgabs_entropy_len I + add_len)))%bool
  then (!!(rv = Vint (Int.neg (Int.repr 5))) &&
       (da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
         AREP gv I ctx * Stream s))
  else (let F := mbedtls_HMAC256_DRBG_reseed_function s I (contents_with_add additional add_len contents)
        in !!(return_value_relate_result F rv)
           && AREP gv ((*match F with ENTROPY.error _ _ => I | 
                  ENTROPY.success (V, K, rc, _, pr) _ => HMAC256DRBGabs K V rc (hmac256drbgabs_entropy_len I) pr
                                (hmac256drbgabs_reseed_interval I) end*)
                     (hmac256drbgabs_reseed I s (contents_with_add additional add_len contents))) ctx *
              da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
              Stream (get_stream_result F))).

Definition generate_absPOST ret_value contents additional add_len output out_len ctx I gv s :=
if out_len >? 1024
then (!!(ret_value = Vint (Int.neg (Int.repr 3))) &&
       (data_at_ Tsh (tarray tuchar out_len) output *
         da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
         AREP gv I ctx * Stream s))
else
  if (add_len >? 256)
  then (!!(ret_value = Vint (Int.neg (Int.repr 5))) &&
       (data_at_ Tsh (tarray tuchar out_len) output *
         da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
         AREP gv I ctx * Stream s))
  else let F := (mbedtls_HMAC256_DRBG_generate_function s I out_len (contents_with_add additional add_len contents))
       in (!!(return_value_relate_result F ret_value)) &&
          (match F with
            | ENTROPY.error _ _ => (data_at_ Tsh (tarray tuchar out_len) output)
            | ENTROPY.success (bytes, _) _ => (data_at Tsh (tarray tuchar out_len) (map Vint (map Int.repr bytes)) output)
          end *
          da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
          Stream (get_stream_result F) *
          AREP gv (hmac256drbgabs_generate I s out_len (contents_with_add additional add_len contents)) ctx).

Definition hmac_drbg_generate_abs_spec :=
  DECLARE _mbedtls_hmac_drbg_random_with_add
   WITH contents: list Z,
        additional: val, add_len: Z,
        output: val, out_len: Z,
        ctx: val, 
        I: hmac256drbgabs,
        s: ENTROPY.stream, gv: globals
    PRE [ _p_rng OF (tptr tvoid), _output OF (tptr tuchar), _out_len OF tuint, 
          _additional OF (tptr tuchar), _add_len OF tuint ]
       PROP (0 <= add_len <= Int.max_unsigned;
             0 <= out_len <= Int.max_unsigned;
             add_len = Zlength contents;
             hmac256drbgabs_entropy_len I + Zlength contents <= 384;
             Forall isbyteZ contents)
       LOCAL (temp _p_rng ctx; temp _output output; temp _out_len (Vint (Int.repr out_len)); 
              temp _additional additional; temp _add_len (Vint (Int.repr add_len)); gvars gv)
       SEP (data_at_ Tsh (tarray tuchar out_len) output;
            da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
            AREP gv I ctx; Stream s)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (generate_absPOST ret_value contents additional add_len output out_len ctx I gv s).

Definition drbg_random_abs_spec :=
  DECLARE _mbedtls_hmac_drbg_random
   WITH output: val, n: Z, ctx: val, 
        I: hmac256drbgabs,
        s: ENTROPY.stream, bytes:_, F:_, ss:_, gv: globals
    PRE [_p_rng OF tptr tvoid, _output OF tptr tuchar, _out_len OF tuint ]
       PROP (0 <= n <= 1024;
         mbedtls_generate s I n = Some(bytes, ss, F))
       LOCAL (temp _p_rng ctx; temp _output output;
              temp _out_len (Vint (Int.repr n)); gvars gv)
       SEP (data_at_ Tsh (tarray tuchar n) output;
            AREP gv I ctx; Stream s)
    POST [ tint ] 
       PROP () 
       LOCAL (temp ret_temp (Vint Int.zero))
       SEP (data_at Tsh (tarray tuchar n) (map Vint (map Int.repr bytes)) output;
            AREP gv F ctx; Stream ss).

Definition drbg_random_abs_spec1 :=
  DECLARE _mbedtls_hmac_drbg_random
   WITH output: val, n: Z, ctx: val, 
        I: hmac256drbgabs,
        s: ENTROPY.stream, bytes:_, J:_, ss:_, gv: globals
    PRE [_p_rng OF tptr tvoid, _output OF tptr tuchar, _out_len OF tuint ]
       PROP (0 <= n <= 1024;
         mbedtls_HMAC256_DRBG_generate_function s I n [] = ENTROPY.success (bytes, J) ss)
       LOCAL (temp _p_rng ctx; temp _output output;
              temp _out_len (Vint (Int.repr n)); gvars gv)
       SEP (data_at_ Tsh (tarray tuchar n) output;
            AREP gv I ctx; Stream s)
    POST [ tint ] EX F: hmac256drbgabs,  
       PROP (F = match J with ((((VV, KK), RC), _), PR) =>
                   HMAC256DRBGabs KK VV RC (hmac256drbgabs_entropy_len I) PR 
                                 (hmac256drbgabs_reseed_interval I)
                      end) 
       LOCAL (temp ret_temp (Vint Int.zero))
       SEP (data_at Tsh (tarray tuchar n) (map Vint (map Int.repr bytes)) output;
            AREP gv F ctx; Stream ss).
