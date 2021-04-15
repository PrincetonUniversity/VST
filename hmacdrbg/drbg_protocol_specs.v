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
         0 <= hmac256drbgabs_reseed_counter I < Int.max_signed.

Definition REP sh gv (Info:md_info_state) (A:hmac256drbgabs) (v: val): mpred :=
  EX a:hmac256drbgstate, 
       (!! WF A) &&
          data_at sh t_struct_hmac256drbg_context_st a v
          * hmac256drbg_relate A a
          * data_at sh t_struct_mbedtls_md_info Info (hmac256drbgstate_md_info_pointer a)
          * spec_sha.K_vector gv.

Definition AREP sh gv (A:hmac256drbgabs) (v: val): mpred :=
  EX Info:md_info_state, REP sh gv Info A v. 

Definition seedREP sh dp rc pr ri gv (Info:md_info_state) (info:val) (v: val): mpred :=
  EX a:hmac256drbgstate, 
          data_at sh t_struct_hmac256drbg_context_st a v
          * preseed_relate dp rc pr ri a
          * data_at sh t_struct_mbedtls_md_info Info info
          * spec_sha.K_vector gv.

Definition seedbufREP sh gv (Info:md_info_state) (info:val) (A:hmac256drbgabs) (v: val): mpred :=
  EX a:hmac256drbgstate,
     !! (0 < hmac256drbgabs_entropy_len A <= 384 /\
         RI_range (hmac256drbgabs_reseed_interval A) /\
         0 <= hmac256drbgabs_reseed_counter A < Int.max_signed)
     && data_at sh t_struct_hmac256drbg_context_st a v
          * hmac256drbg_relate A a
          * data_at sh t_struct_mbedtls_md_info Info info
          * spec_sha.K_vector gv.

(*TODO: init, free*)

(*based on hmac_drbg_seed_inst256_spec*)
Definition drbg_seed_inst256_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_seed
   WITH sh: share, dp:_, ctx: val, info:val, len: Z, data:val, Data: list byte,
        Info: md_info_state, s:ENTROPY.stream, rc:Z, pr_flag:bool, ri:Z,
        handle_ss: DRBG_functions.DRBG_state_handle * ENTROPY.stream, gv: globals
    PRE [tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         tptr (Tstruct _mbedtls_md_info_t noattr),
         tptr tuchar, tuint ]
       PROP (writable_share sh; 
                 len = Zlength Data /\ 0 <= len <=256 /\
             instantiate_function_256 s pr_flag (contents_with_add data (Zlength Data) Data)
               = ENTROPY.success (fst handle_ss) (snd handle_ss))
       PARAMS (ctx; info; data; Vint (Int.repr len)) GLOBALS (gv)
       SEP (seedREP sh dp rc pr_flag ri gv Info info ctx; Stream s;
            da_emp sh (tarray tuchar (Zlength Data)) (map Vubyte Data) data;
            mem_mgr gv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp (Vint ret_value))
       SEP (da_emp sh (tarray tuchar (Zlength Data)) (map Vubyte Data) data;
            if Int.eq ret_value (Int.repr (-20864))
            then seedREP sh dp rc pr_flag ri gv Info info ctx * Stream s                 
            else !!(ret_value = Int.zero) &&                  
                 EX p:val, 
                 match fst handle_ss with ((((newV, newK), newRC), newEL), newPR) =>
                    AREP sh gv (HMAC256DRBGabs newK newV newRC 32 newPR 10000) ctx *
                    Stream (snd handle_ss) * EX mds:mdstate, md_empty mds   
                 end;
            mem_mgr gv).

Definition drbg_seed_buf_abs_spec :=
  DECLARE _mbedtls_hmac_drbg_seed_buf
   WITH sh: share, ctx: val, info:val, d_len: Z, data:val, Data: list byte,
        I: hmac256drbgabs, Info:md_info_state,
        gv: globals
    PRE [ tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
          tptr (Tstruct _mbedtls_md_info_t noattr),
          tptr tuchar,  tuint ]
       PROP (writable_share sh; 
                d_len = Zlength Data \/ d_len=0;
             0 <= d_len <= Int.max_unsigned)
       PARAMS (ctx; info; data; Vint (Int.repr d_len)) GLOBALS (gv)
       SEP (seedbufREP sh gv Info info I ctx;
            da_emp sh (tarray tuchar (Zlength Data)) (map Vubyte Data) data;
            mem_mgr gv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (da_emp sh (tarray tuchar (Zlength Data)) (map Vubyte Data) data *
            if Val.eq ret_value (Vint (Int.repr (-20864)))
            then seedbufREP sh gv Info info I ctx
            else match I with HMAC256DRBGabs key V RC EL PR RI =>
                 EX KEY:list byte, EX VAL:list byte, EX p:val, EX mds:mdstate,
                 !!(hmacdrbg.HMAC256_DRBG_functional_prog.HMAC256_DRBG_update (contents_with_add data d_len Data) V (repeat Byte.one 32) = (KEY, VAL))
                 && md_full key mds *
                 REP sh gv Info (HMAC256DRBGabs KEY VAL RC EL PR RI) ctx end;
            mem_mgr gv).

Definition drbg_setPredictionResistance_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_set_prediction_resistance 
   WITH sh: share, ctx:val, A:_, r:bool, gv:globals
    PRE [ tptr (Tstruct _mbedtls_hmac_drbg_context noattr), tint ]
       PROP (writable_share sh)
       PARAMS (ctx; Val.of_bool r) GLOBALS ()
       SEP (AREP sh gv A ctx)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (AREP sh gv (setPR_ABS r A) ctx).

Definition drbg_setEntropyLen_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_set_entropy_len
   WITH sh: share, ctx:val, A:_, l:_, gv:globals
    PRE [ tptr (Tstruct _mbedtls_hmac_drbg_context noattr), tuint ]
       PROP (writable_share sh; 0 < l <= 384 )
       PARAMS (ctx;Vint (Int.repr l)) GLOBALS()
       SEP (AREP sh gv A ctx)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (AREP sh gv (setEL_ABS l A) ctx).

Definition drbg_setReseedInterval_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_set_reseed_interval
   WITH sh: share, ctx:val, A:_, ri:_, gv:globals
    PRE [ tptr (Tstruct _mbedtls_hmac_drbg_context noattr), tint ]
       PROP (writable_share sh; RI_range ri )
       PARAMS (ctx; Vint (Int.repr ri)) GLOBALS ()
       SEP (AREP sh gv A ctx)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (AREP sh gv (setRI_ABS ri A) ctx).

Definition drbg_update_abs_spec :=
  DECLARE _mbedtls_hmac_drbg_update
   WITH contents: list byte,
        additional: val, sha: share, add_len: Z,
        ctx: val, shc: share, I: hmac256drbgabs,
        gv: globals
     PRE [tptr t_struct_hmac256drbg_context_st,
         tptr tuchar, tuint ]
       PROP (readable_share sha; writable_share shc; 0 <= add_len <= Int.max_unsigned;
             add_len = Zlength contents \/ add_len = 0)
       PARAMS (ctx; additional; Vint (Int.repr add_len))
       GLOBALS (gv)
       SEP (AREP shc gv I ctx;
            da_emp sha (tarray tuchar (Zlength contents)) (map Vubyte contents) additional)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (AREP shc gv (hmac256drbgabs_hmac_drbg_update I (contents_with_add additional add_len contents)) ctx;
            da_emp sha (tarray tuchar (Zlength contents)) (map Vubyte contents) additional).

Definition drbg_reseed_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_reseed
   WITH contents: list byte,
        additional: val, sha: share, add_len: Z,
        ctx: val, shc: share, I: hmac256drbgabs,
        s: ENTROPY.stream, gv: globals
    PRE [ tptr t_struct_hmac256drbg_context_st, tptr tuchar, tuint ]
       PROP (readable_share sha; writable_share shc; 0 <= add_len <= Int.max_unsigned;
             add_len = Zlength contents;
             0 < hmac256drbgabs_entropy_len I + Zlength (contents_with_add additional add_len contents) < Int.modulus)
       PARAMS (ctx; additional; Vint (Int.repr add_len)) GLOBALS (gv)
       SEP ( da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional;
              AREP shc gv I ctx; Stream s)
    POST [ tint ]
       EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (if ((zlt 256 add_len) || (zlt 384 (hmac256drbgabs_entropy_len I + add_len)))%bool
  then (!!(rv = Vint (Int.neg (Int.repr 5))) &&
       (da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional *
         AREP shc gv I ctx * Stream s))
  else (let F := mbedtls_HMAC256_DRBG_reseed_function s I (contents_with_add additional add_len contents)
        in !!(return_value_relate_result F rv)
           && AREP shc gv ((*match F with ENTROPY.error _ _ => I | 
                  ENTROPY.success (V, K, rc, _, pr) _ => HMAC256DRBGabs K V rc (hmac256drbgabs_entropy_len I) pr
                                (hmac256drbgabs_reseed_interval I) end*)
                     (hmac256drbgabs_reseed I s (contents_with_add additional add_len contents))) ctx *
              da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional *
              Stream (get_stream_result F))).

Definition generate_absPOST ret_value (contents: list byte) additional sha add_len output sho out_len ctx shc I gv s :=
if out_len >? 1024
then (!!(ret_value = Vint (Int.neg (Int.repr 3))) &&
       (data_at_ sho (tarray tuchar out_len) output *
         da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional *
         AREP shc gv I ctx * Stream s))
else
  if (add_len >? 256)
  then (!!(ret_value = Vint (Int.neg (Int.repr 5))) &&
       (data_at_ sho (tarray tuchar out_len) output *
         da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional *
         AREP shc gv I ctx * Stream s))
  else let F := (mbedtls_HMAC256_DRBG_generate_function s I out_len (contents_with_add additional add_len contents))
       in (!!(return_value_relate_result F ret_value)) &&
          (match F with
            | ENTROPY.error _ _ => (data_at_ sho (tarray tuchar out_len) output)
            | ENTROPY.success (bytes, _) _ => (data_at sho (tarray tuchar out_len) (map Vubyte bytes) output)
          end *
          da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional *
          Stream (get_stream_result F) *
          AREP shc gv (hmac256drbgabs_generate I s out_len (contents_with_add additional add_len contents)) ctx).

Definition hmac_drbg_generate_abs_spec :=
  DECLARE _mbedtls_hmac_drbg_random_with_add
   WITH contents: list byte,
        additional: val, sha: share, add_len: Z,
        output: val, sho: share, out_len: Z,
        ctx: val, shc: share,
        I: hmac256drbgabs,
        s: ENTROPY.stream, gv: globals
    PRE [ tptr tvoid, tptr tuchar, tuint, 
          tptr tuchar, tuint ]
       PROP (readable_share sha; writable_share shc; writable_share sho;
             0 <= add_len <= Int.max_unsigned;
             0 <= out_len <= Int.max_unsigned;
             add_len = Zlength contents;
             hmac256drbgabs_entropy_len I + Zlength contents <= 384)
       PARAMS (ctx; output; Vint (Int.repr out_len); additional; Vint (Int.repr add_len))
       GLOBALS (gv)
       SEP (data_at_ sho (tarray tuchar out_len) output;
            da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional;
            AREP shc gv I ctx; Stream s)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (generate_absPOST ret_value contents additional sha add_len output sho out_len ctx shc I gv s).

Definition drbg_random_abs_spec :=
  DECLARE _mbedtls_hmac_drbg_random
   WITH output: val, sho: share, n: Z, ctx: val, shc: share,
        I: hmac256drbgabs,
        s: ENTROPY.stream, bytes:_, F:_, ss:_, gv: globals
    PRE [ tptr tvoid, tptr tuchar, tuint ]
       PROP (writable_share sho; writable_share shc;
         0 <= n <= 1024;
         mbedtls_generate s I n = Some(bytes, ss, F))
       PARAMS (ctx; output; Vint (Int.repr n)) GLOBALS (gv)
       SEP (data_at_ sho (tarray tuchar n) output;
            AREP shc gv I ctx; Stream s)
    POST [ tint ] 
       PROP () 
       LOCAL (temp ret_temp (Vint Int.zero))
       SEP (data_at sho (tarray tuchar n) (map Vubyte bytes) output;
            AREP shc gv F ctx; Stream ss).

Definition drbg_random_abs_spec1 :=
  DECLARE _mbedtls_hmac_drbg_random
   WITH output: val, sho: share, n: Z, ctx: val, shc: share,
        I: hmac256drbgabs,
        s: ENTROPY.stream, bytes:_, J:_, ss:_, gv: globals
    PRE [ tptr tvoid, tptr tuchar, tuint ]
       PROP (writable_share sho; writable_share shc;
         0 <= n <= 1024;
         mbedtls_HMAC256_DRBG_generate_function s I n [] = ENTROPY.success (bytes, J) ss)
       PARAMS (ctx; output; Vint (Int.repr n)) GLOBALS (gv)
       SEP (data_at_ sho (tarray tuchar n) output;
            AREP shc gv I ctx; Stream s)
    POST [ tint ] EX F: hmac256drbgabs,  
       PROP (F = match J with ((((VV, KK), RC), _), PR) =>
                   HMAC256DRBGabs KK VV RC (hmac256drbgabs_entropy_len I) PR 
                                 (hmac256drbgabs_reseed_interval I)
                      end) 
       LOCAL (temp ret_temp (Vint Int.zero))
       SEP (data_at sho (tarray tuchar n) (map Vubyte bytes) output;
            AREP shc gv F ctx; Stream ss).
