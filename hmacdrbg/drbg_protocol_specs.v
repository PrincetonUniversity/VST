Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import sha.general_lemmas.
Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.entropy.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.

Require Import sha.HMAC256_functional_prog.
Require Import hmacdrbg.entropy_lemmas.
Require Import floyd.library.
Require Import floyd.deadvars.

Require Import hmacdrbg.HMAC256_DRBG_bridge_to_FCF.

Lemma Bridge s I n bytes J ss (M: mbedtls_HMAC256_DRBG_generate_function s I n [] = ENTROPY.success (bytes, J) ss):
  match I with HMAC256DRBGabs K V reseed_counter entropy_len prediction_resistance reseed_interval =>
  reseed_counter <= reseed_interval -> prediction_resistance = false ->
  match J with (ws,sstrength,prflag) =>
  s=ss /\ Generate reseed_interval (V,K,reseed_counter) n = DRBG_functions.generate_algorithm_success bytes ws
  end end.
Proof. destruct I. destruct J as [[ws sstrength] prf]. simpl. simpl in M.
remember (n >? 1024) as d; destruct d; try discriminate.
rewrite andb_negb_r in M. intros; subst.
apply Zgt_is_gt_bool_f in H. rewrite H.
remember (HMAC_DRBG_algorithms.HMAC_DRBG_generate_helper_Z HMAC256 key V n) as p; destruct p.
unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm in M; simpl in M.
rewrite H, <- Heqp in M. inv M; split; trivial.
Qed.

Definition mbedlts_generate s I n :=
   match mbedtls_HMAC256_DRBG_generate_function s I n [] 
   with ENTROPY.success (bytes, J) ss =>
          match J with ((((VV, KK), RC), _), PR) =>
            Some (bytes, ss, HMAC256DRBGabs KK VV RC (hmac256drbgabs_entropy_len I) PR 
                                 (hmac256drbgabs_reseed_interval I))
          end
      | _ => None  
   end.

Lemma Bridge' s I n bytes F ss (M: mbedlts_generate s I n = Some(bytes, ss, F)):
  match I with HMAC256DRBGabs K V reseed_counter entropy_len prediction_resistance reseed_interval =>
  reseed_counter <= reseed_interval -> prediction_resistance = false ->
  match F with HMAC256DRBGabs KK VV rc _ _ _ =>
  s=ss /\ rc=reseed_counter+1 /\
  Generate reseed_interval (V,K,reseed_counter) n = DRBG_functions.generate_algorithm_success bytes ((VV,KK), rc)
  end end.
Proof. destruct I. destruct F. simpl. unfold mbedlts_generate in M. simpl in M.
remember (n >? 1024) as d; destruct d; try discriminate.
rewrite andb_negb_r in M. intros; subst.
apply Zgt_is_gt_bool_f in H. rewrite H.
remember (HMAC_DRBG_algorithms.HMAC_DRBG_generate_helper_Z HMAC256 key V n) as p; destruct p.
unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm in M; simpl in M.
rewrite H, <- Heqp in M. inv M; auto. 
Qed.

Definition WF (I:hmac256drbgabs):=
         Zlength (hmac256drbgabs_value I) = 32 /\ 
         0 < hmac256drbgabs_entropy_len I <= 384 /\
         RI_range (hmac256drbgabs_reseed_interval I) /\
         0 <= hmac256drbgabs_reseed_counter I <= Int.max_signed /\
         Forall isbyteZ (hmac256drbgabs_value I).

Definition REP kv (Info:md_info_state) (A:hmac256drbgabs) (v: val): mpred :=
  EX a:hmac256drbgstate, 
       (!! WF A) &&
          data_at Tsh t_struct_hmac256drbg_context_st a v
          * hmac256drbg_relate A a
          * data_at Tsh t_struct_mbedtls_md_info Info (hmac256drbgstate_md_info_pointer a)
          * spec_sha.K_vector kv.

Definition AREP kv (A:hmac256drbgabs) (v: val): mpred :=
  EX Info:md_info_state, REP kv Info A v. 

Definition seedREP dp rc pr ri kv (Info:md_info_state) (info:val) (v: val): mpred :=
  EX a:hmac256drbgstate, 
          data_at Tsh t_struct_hmac256drbg_context_st a v
          * preseed_relate dp rc pr ri a
          * data_at Tsh t_struct_mbedtls_md_info Info info
          * spec_sha.K_vector kv.

Definition seedbufREP kv (Info:md_info_state) (info:val) (A:hmac256drbgabs) (v: val): mpred :=
  EX a:hmac256drbgstate,
     !! (0 < hmac256drbgabs_entropy_len A <= 384 /\
         RI_range (hmac256drbgabs_reseed_interval A) /\
         0 <= hmac256drbgabs_reseed_counter A <= Int.max_signed)
     && data_at Tsh t_struct_hmac256drbg_context_st a v
          * hmac256drbg_relate A a
          * data_at Tsh t_struct_mbedtls_md_info Info info
          * spec_sha.K_vector kv.

(*TODO: init, free*)

(*based on hmac_drbg_seed_inst256_spec*)
Definition drbg_seed_inst256_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_seed
   WITH dp:_, ctx: val, info:val, len: Z, data:val, Data: list Z,
        kv: val, Info: md_info_state, s:ENTROPY.stream, rc:Z, pr_flag:bool, ri:Z,
        handle_ss: DRBG_functions.DRBG_state_handle * ENTROPY.stream
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _md_info OF tptr (Tstruct _mbedtls_md_info_t noattr),
         _custom OF tptr tuchar, _len OF tuint ]
       PROP (len = Zlength Data /\ 0 <= len <=256 /\ Forall isbyteZ Data /\
             instantiate_function_256 s pr_flag (contents_with_add data (Zlength Data) Data)
               = ENTROPY.success (fst handle_ss) (snd handle_ss))
       LOCAL (temp _ctx ctx; temp _md_info info;
              temp _len (Vint (Int.repr len)); temp _custom data; gvar sha._K256 kv)
       SEP (seedREP dp rc pr_flag ri kv Info info ctx; Stream s;
            da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp (Vint ret_value))
       SEP (da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data;
            if Int.eq ret_value (Int.repr (-20864))
            then seedREP dp rc pr_flag ri kv Info info ctx * Stream s                 
            else !!(ret_value = Int.zero) &&                  
                 EX p:val, malloc_token Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
                 match fst handle_ss with ((((newV, newK), newRC), newEL), newPR) =>
                    AREP kv (HMAC256DRBGabs newK newV newRC 32 newPR 10000) ctx *
                    Stream (snd handle_ss) * EX mds:mdstate, md_empty mds   
                 end).

Definition drbg_seed_buf_abs_spec :=
  DECLARE _mbedtls_hmac_drbg_seed_buf
   WITH ctx: val, info:val, d_len: Z, data:val, Data: list Z,
        I: hmac256drbgabs, Info:md_info_state,
        kv: val 
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _md_info OF (tptr (Tstruct _mbedtls_md_info_t noattr)),
         _data OF tptr tuchar, _data_len OF tuint ]
       PROP (d_len = Zlength Data \/ d_len=0;
             0 <= d_len <= Int.max_unsigned; Forall isbyteZ Data)
       LOCAL (temp _ctx ctx; temp _md_info info;
              temp _data_len (Vint (Int.repr d_len)); temp _data data; gvar sha._K256 kv)
       SEP (seedbufREP kv Info info I ctx;
            da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data *
            if Val.eq ret_value (Vint (Int.repr (-20864)))
            then seedbufREP kv Info info I ctx
            else match I with HMAC256DRBGabs key V RC EL PR RI =>
                 EX KEY:list Z, EX VAL:list Z, EX p:val, EX mds:mdstate,
                 !!(hmacdrbg.HMAC256_DRBG_functional_prog.HMAC256_DRBG_update (contents_with_add data d_len Data) V (list_repeat 32 1) = (KEY, VAL))
                 && md_full key mds * malloc_token Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
                 REP kv Info (HMAC256DRBGabs KEY VAL RC EL PR RI) ctx end).

Definition drbg_setPredictionResistance_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_set_prediction_resistance 
   WITH ctx:val, A:_, r:bool, kv:_
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _resistance OF tint ]
       PROP ( )
       LOCAL (temp _ctx ctx; temp _resistance (Val.of_bool r))
       SEP (AREP kv A ctx)
    POST [ tvoid ] SEP (AREP kv (setPR_ABS r A) ctx).


Definition drbg_setEntropyLen_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_set_entropy_len
   WITH ctx:val, A:_, l:_, kv:_
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _len OF tuint ]
       PROP ( 0 < l <= 384 )
       LOCAL (temp _ctx ctx; temp _len (Vint (Int.repr l)))
       SEP (AREP kv A ctx)
    POST [ tvoid ]
       SEP (AREP kv (setEL_ABS l A) ctx).

Definition drbg_setReseedInterval_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_set_reseed_interval
   WITH ctx:val, A:_, ri:_, kv:_
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _interval OF tint ]
       PROP (RI_range ri )
       LOCAL (temp _ctx ctx; temp _interval (Vint (Int.repr ri)))
       SEP (AREP kv A ctx)
    POST [ tvoid ]
       SEP (AREP kv (setRI_ABS ri A) ctx).

Definition drbg_update_abs_spec :=
  DECLARE _mbedtls_hmac_drbg_update
   WITH contents: list Z,
        additional: val, add_len: Z,
        ctx: val, I: hmac256drbgabs,
        kv: val
     PRE [ _ctx OF (tptr t_struct_hmac256drbg_context_st),
           _additional OF (tptr tuchar), _add_len OF tuint ]
       PROP (0 <= add_len <= Int.max_unsigned;
             add_len = Zlength contents \/ add_len = 0;
             Forall isbyteZ contents)
       LOCAL (temp _ctx ctx;
              temp _additional additional;
              temp _add_len (Vint (Int.repr add_len));
              gvar sha._K256 kv)
       SEP (AREP kv I ctx;
            da_emp Tsh (tarray tuchar (Zlength contents)) (map Vint (map Int.repr contents)) additional)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (AREP kv (hmac256drbgabs_hmac_drbg_update I (contents_with_add additional add_len contents)) ctx;
            da_emp Tsh (tarray tuchar (Zlength contents)) (map Vint (map Int.repr contents)) additional).

Definition drbg_reseed_spec_abs :=
  DECLARE _mbedtls_hmac_drbg_reseed
   WITH contents: list Z,
        additional: val, add_len: Z,
        ctx: val, I: hmac256drbgabs,
        kv: val, s: ENTROPY.stream
    PRE [ _ctx OF (tptr t_struct_hmac256drbg_context_st), _additional OF (tptr tuchar), _len OF tuint ]
       PROP (0 <= add_len <= Int.max_unsigned;
             add_len = Zlength contents;
             0 < hmac256drbgabs_entropy_len I + Zlength (contents_with_add additional add_len contents) < Int.modulus;         
             Forall isbyteZ contents)
       LOCAL (temp _ctx ctx; temp _additional additional; temp _len (Vint (Int.repr add_len)); gvar sha._K256 kv)
       SEP ( da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
              AREP kv I ctx; Stream s)
    POST [ tint ]
       EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (if ((zlt 256 add_len) || (zlt 384 (hmac256drbgabs_entropy_len I + add_len)))%bool
  then (!!(rv = Vint (Int.neg (Int.repr 5))) &&
       (da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
         AREP kv I ctx * Stream s))
  else (EX F:_, 
       !!(F = mbedtls_HMAC256_DRBG_reseed_function s I (contents_with_add additional add_len contents) /\
          return_value_relate_result F rv)
        && AREP kv (match F with ENTROPY.error _ _ => I | 
                  ENTROPY.success (V, K, rc, _, pr) _ => HMAC256DRBGabs K V rc (hmac256drbgabs_entropy_len I) pr
                                (hmac256drbgabs_reseed_interval I) end) ctx *
         da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
         Stream (get_stream_result F))).

(*random_with_add not yet done using REP/AREP*)
(*from verif_hmacdrbg_other*)
Definition drbg_random_abs_spec :=
  DECLARE _mbedtls_hmac_drbg_random
   WITH output: val, n: Z, ctx: val, 
        I: hmac256drbgabs, kv: val, 
        s: ENTROPY.stream, bytes:_, F:_, ss:_
    PRE [_p_rng OF tptr tvoid, _output OF tptr tuchar, _out_len OF tuint ]
       PROP (0 <= n <= 1024;
         mbedlts_generate s I n = Some(bytes, ss, F))
       LOCAL (temp _p_rng ctx; temp _output output;
              temp _out_len (Vint (Int.repr n)); gvar sha._K256 kv)
       SEP (data_at_ Tsh (tarray tuchar n) output;
            AREP kv I ctx; Stream s)
    POST [ tint ] 
       PROP () 
       LOCAL (temp ret_temp (Vint Int.zero))
       SEP (data_at Tsh (tarray tuchar n) (map Vint (map Int.repr bytes)) output;
            AREP kv F ctx; Stream ss).

Definition drbg_random_abs_spec1 :=
  DECLARE _mbedtls_hmac_drbg_random
   WITH output: val, n: Z, ctx: val, 
        I: hmac256drbgabs, kv: val, 
        s: ENTROPY.stream, bytes:_, J:_, ss:_
    PRE [_p_rng OF tptr tvoid, _output OF tptr tuchar, _out_len OF tuint ]
       PROP (0 <= n <= 1024;
         mbedtls_HMAC256_DRBG_generate_function s I n [] = ENTROPY.success (bytes, J) ss)
       LOCAL (temp _p_rng ctx; temp _output output;
              temp _out_len (Vint (Int.repr n)); gvar sha._K256 kv)
       SEP (data_at_ Tsh (tarray tuchar n) output;
            AREP kv I ctx; Stream s)
    POST [ tint ] EX F: hmac256drbgabs,  
       PROP (F = match J with ((((VV, KK), RC), _), PR) =>
                   HMAC256DRBGabs KK VV RC (hmac256drbgabs_entropy_len I) PR 
                                 (hmac256drbgabs_reseed_interval I)
                      end) 
       LOCAL (temp ret_temp (Vint Int.zero))
       SEP (data_at Tsh (tarray tuchar n) (map Vint (map Int.repr bytes)) output;
            AREP kv F ctx; Stream ss).

Lemma AUX s I n bytes J ss: mbedtls_HMAC256_DRBG_generate_function s I n [] =
  ENTROPY.success (bytes, J) ss ->
  hmac256drbgabs_generate I s n [] = 
  match J with ((((VV, KK), RC), _), PR) =>
     HMAC256DRBGabs KK VV RC (hmac256drbgabs_entropy_len I) PR 
                    (hmac256drbgabs_reseed_interval I)
  end.
Proof. unfold hmac256drbgabs_generate. intros H; rewrite H.
  destruct I. simpl. destruct J. destruct p. destruct d. destruct p. f_equal.
Qed. 

Lemma false_zgt z a: false = (z >? a) -> z<=a. 
Proof. unfold Z.gtb.
  remember (z ?= a). destruct c. symmetry in Heqc; apply Z.compare_eq in Heqc. subst; intros. omega.
  symmetry in Heqc. destruct (Z.compare_lt_iff z a); intros. apply H in Heqc. omega.
  discriminate.
Qed. 
Lemma false_zge z a: false = (z >=? a) -> z<=a. 
Proof. unfold Z.geb.
  remember (z ?= a). destruct c; intros; try discriminate.
  symmetry in Heqc. destruct (Z.compare_lt_iff z a); intros. apply H0 in Heqc. omega.
Qed.

Lemma HMAC_DRBG_updateWF a b c d e:
      (d,e) = HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256_functional_prog.HMAC256 a b c ->
       Zlength e = 32 /\ Forall isbyteZ e.
Proof. unfold HMAC_DRBG_algorithms.HMAC_DRBG_update.
  destruct a; intros.
  + inversion H; clear H; split. apply hmac_common_lemmas.HMAC_Zlength.
    apply hmac_common_lemmas.isbyte_hmac.
  + inversion H; clear H. rewrite hmac_common_lemmas.HMAC_Zlength.
    split; trivial. apply hmac_common_lemmas.isbyte_hmac.
Qed.

Lemma HMAC256_DRBG_generate_algorithmWF a v k rc n l bytes V K RC (N:n >=0)
      (A: 0<= a < Int.max_signed) (Rc: 0<=rc) 
      (H: DRBG_functions.generate_algorithm_success bytes (V, K, RC) =
          HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm a (v,k,rc) n l):
      Zlength V = 32 /\ 0 <= RC <= Int.max_signed /\ Forall isbyteZ V.
Proof.
  unfold  HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm in H.
  unfold HMAC_DRBG_algorithms.HMAC_DRBG_generate_algorithm in H.
  remember (rc >? a) as q; destruct q; try discriminate.
  apply false_zgt in Heqq.
  destruct l.
  + rewrite HMAC_DRBG_algorithms.HMAC_DRBG_generate_helper_Z_equation in H.
    remember (0 >=? n). destruct b.
    - symmetry in Heqb; apply Z.geb_le in Heqb.
      assert (NN: n=0) by omega. subst n; clear N Heqb. simpl in H.
      inversion H; clear H. subst.
      split. apply hmac_common_lemmas.HMAC_Zlength.
      split. split; omega.
      apply hmac_common_lemmas.isbyte_hmac. 
    - remember (HMAC_DRBG_algorithms.HMAC_DRBG_generate_helper_Z
           HMAC256_functional_prog.HMAC256 k v (n - Z.of_nat 32)). 
      destruct p. 
      remember (HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256_functional_prog.HMAC256
         [] k (HMAC256_functional_prog.HMAC256 l k)). 
      destruct p. inv H. 
      apply HMAC_DRBG_updateWF in Heqp0. destruct Heqp0.
      split; trivial. split; trivial. omega.
  + remember (HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256_functional_prog.HMAC256 (z :: l) k v). 
    destruct p.
    rewrite HMAC_DRBG_algorithms.HMAC_DRBG_generate_helper_Z_equation in H.
    remember (0 >=? n) as b; destruct b.
    - symmetry in Heqb. apply Z.geb_le in Heqb.
      assert (NN: n=0) by omega. subst n; clear N Heqb.
      remember (HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256_functional_prog.HMAC256
         (z :: l) l0 l1). 
      destruct p. inv H. apply HMAC_DRBG_updateWF in Heqp0. destruct Heqp0.
      split; trivial. split; trivial. omega.
    - remember (HMAC_DRBG_algorithms.HMAC_DRBG_generate_helper_Z
           HMAC256_functional_prog.HMAC256 l0 l1 (n - Z.of_nat 32)).
      destruct p.
      remember (HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256_functional_prog.HMAC256
         (z :: l) l0 (HMAC256_functional_prog.HMAC256 l2 l0)). 
      destruct p. inv H. apply HMAC_DRBG_updateWF in Heqp1. destruct Heqp1.
      split; trivial. split; trivial. omega.
Qed.

Lemma HMAC256_DRBG_generate_functionWF f a b c s v k rc d pr n e l V K RC z PR ss bytes
      (A: 0<= a < Int.max_signed) (N: n>=0) (Rc: 0<=rc)
      (F: forall s d z b x y zz A B C D ss, ENTROPY.success (A, B, zz, C, D) ss = f s (d, z, b) x y -> 0<=zz)
      (H : ENTROPY.success (bytes, (V, K, RC, z, PR)) ss =
          HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_function f a b c s (v, k, rc, d, pr) n e pr l):
Zlength V = 32 /\ 0 <= RC <= Int.max_signed /\ Forall isbyteZ V.
Proof.
  unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_function in H.
  unfold DRBG_functions.DRBG_generate_function in H.
  remember (n >? b) as q1; destruct q1; try discriminate.
  remember (e >? d) as q2; destruct q2; try discriminate.
  remember (Zlength l >? c) as q3; destruct q3; try discriminate.
  assert (P: (pr && negb pr)%bool = false). { destruct pr; trivial. }
  rewrite P in H; clear P.
  remember (DRBG_functions.DRBG_generate_function_helper
        (HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm a) f s
        (v, k, rc, d, pr) n pr l pr 1). 
  destruct r; try discriminate.
  destruct p. symmetry in H; inv H.
  unfold DRBG_functions.DRBG_generate_function_helper in Heqr.
  destruct PR.
  + remember (f s (v, k, rc, z, true) true l). 
    destruct r; try discriminate.
    destruct p. destruct p. apply false_zgt in Heqq1. apply false_zgt in Heqq2. apply false_zgt in Heqq3.
    remember (HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm a p n []).
    destruct d.
    * remember (f s0 (p, z0, b0) true [] ). 
      destruct r; try discriminate.
      destruct p0. destruct p0.
         remember (HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm a p0 n []).
         destruct d; try discriminate.
         symmetry in Heqr; inv Heqr. destruct p0 as [[XX yy] zz].
         apply HMAC256_DRBG_generate_algorithmWF in Heqd0; trivial.
         apply F in Heqr1; trivial.
    * symmetry in Heqr; inv Heqr.
      destruct p as [[? ?] ?]. apply HMAC256_DRBG_generate_algorithmWF in Heqd; trivial.
      apply F in Heqr0; trivial.
  + remember (HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm a
           (v, k, rc) n l).
    destruct d.
    - remember (f s (v, k, rc, z, false) false l). destruct r; try discriminate.
      destruct p. destruct p.
      remember (HMAC256_DRBG_functional_prog.HMAC256_DRBG_generate_algorithm a p n
           []).
      destruct d; try discriminate. symmetry in Heqr; inv Heqr.
      destruct p as [[? ?] ?]. apply HMAC256_DRBG_generate_algorithmWF in Heqd0; trivial.
      apply F in Heqr0; trivial.
    - symmetry in Heqr; inv Heqr. apply HMAC256_DRBG_generate_algorithmWF in Heqd; trivial.
Qed.

Lemma HMAC256_DRBG_reseed_algorithmWF d l y A B zz 
      (H: (A, B, zz) = HMAC256_DRBG_functional_prog.HMAC256_DRBG_reseed_algorithm d l y):
      0 <= zz <= Int.max_signed.
Proof.
  unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_reseed_algorithm, HMAC_DRBG_algorithms.HMAC_DRBG_reseed_algorithm in H.
  destruct d as [[? ?] ?]. 
  remember (HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256_functional_prog.HMAC256
         (l ++ y) l1 l0) as q; destruct q. inv H. rewrite int_max_signed_eq. omega.
Qed.

Lemma HMAC256_DRBG_reseed_functionWF a b c s t x y A B zz C D ss 
      (H: ENTROPY.success (A, B, zz, C, D) ss =
        HMAC256_DRBG_functional_prog.HMAC256_DRBG_reseed_function a b c s t x y):
      0 <= zz <= Int.max_signed.
Proof. unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_reseed_function, DRBG_functions.DRBG_reseed_function in H.
  destruct t. destruct p.
  remember ((x && negb b0)%bool) as bb; destruct bb; try discriminate.
  remember (Zlength y >? c) as cc; destruct cc; try discriminate.
  remember (get_entropy z a b x s) as dd. destruct dd; try discriminate. inv H.
  eapply HMAC256_DRBG_reseed_algorithmWF; eassumption.
Qed.

Lemma mbedtls_HMAC256_DRBG_reseed_functionWF a s data ss A B zz C D
      (H: mbedtls_HMAC256_DRBG_reseed_function s a data =
          ENTROPY.success (A, B, zz, C, D)  ss):
      0 <= zz <= Int.max_signed.
Proof. unfold mbedtls_HMAC256_DRBG_reseed_function in H.
  destruct a; symmetry in H. eapply HMAC256_DRBG_reseed_functionWF; eauto. Qed.

Lemma mbedtls_HMAC256_DRBG_generate_functionWF_success s k v rc el pr rsi n l bytes V K RC z PR ss
      (N: n>=0) (Rc: 0<=rc) (HRSI: 0 <= rsi < Int.max_signed)
      (H: ENTROPY.success (bytes, (V, K, RC, z, PR)) ss =
        mbedtls_HMAC256_DRBG_generate_function s (HMAC256DRBGabs k v rc el pr rsi) n l):
Zlength V = 32 /\ 0 <= RC <= Int.max_signed /\ Forall isbyteZ V.
Proof. unfold mbedtls_HMAC256_DRBG_generate_function in H.
  apply HMAC256_DRBG_generate_functionWF in H; trivial.
  intros. eapply HMAC256_DRBG_reseed_functionWF; eassumption.
Qed.

Lemma hmac256drbgabs_generateWF I s n l K V RC el PR rsi (N:n>=0)
      (HI: Zlength (hmac256drbgabs_value I) = 32 /\ 
           0 <= hmac256drbgabs_reseed_counter I <= Int.max_signed /\
           Forall isbyteZ  (hmac256drbgabs_value I)) (HRSI: 0 <= rsi < Int.max_signed)
      (G: hmac256drbgabs_generate I s n l = HMAC256DRBGabs K V RC el PR rsi):
      Zlength V = 32 /\ 0 <= RC <= Int.max_signed /\ Forall isbyteZ V.
Proof. unfold hmac256drbgabs_generate in G. destruct I; simpl in HI.
  remember ( mbedtls_HMAC256_DRBG_generate_function s
        (HMAC256DRBGabs key V0 reseed_counter entropy_len
           prediction_resistance reseed_interval) n l). 
  destruct r.
  + destruct p. destruct d. destruct p. destruct d. destruct p.
    inv G. apply mbedtls_HMAC256_DRBG_generate_functionWF_success in Heqr; trivial. omega.
  + inv G. trivial.
Qed. 

Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.
Require Import hmacdrbg.verif_hmac_drbg_seed_common.
Opaque mbedtls_HMAC256_DRBG_reseed_function.
Opaque initial_key. Opaque initial_value.
Opaque mbedtls_HMAC256_DRBG_reseed_function.
Opaque list_repeat. 

Lemma drbg_seed_256: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_seed drbg_seed_inst256_spec_abs.
Proof.
  start_function.
  abbreviate_semax.
  destruct H as [HDlen1 [HDlen2 [HData RES]]]. destruct handle_ss as [handle ss]. simpl in RES.
  unfold seedREP.
  rewrite extract_exists_in_SEP. Intros Ctx.  
  rewrite data_at_isptr with (p:=ctx). Intros.
  destruct ctx; try contradiction.
  unfold_data_at 1%nat. 
  destruct Ctx as [MdCTX [V [RC [EL [PR RI]]]]]. simpl.
  destruct MdCTX as [M1 [M2 M3]].
  freeze [1;2;3;4;5] FIELDS.
  rewrite field_at_compatible'. Intros. rename H into FC_mdx.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial. rewrite int_add_repr_0_r.
  freeze [0;2;3;4;5;6] FR0.
  Time forward_call ((M1,(M2,M3)), Vptr b i, Vint (Int.repr 1), info).

  Intros v. rename H into Hv.
  forward.
  forward_if (
     PROP (v=0)
   LOCAL (temp _ret (Vint (Int.repr v)); temp _t'2 (Vint (Int.repr v));
   temp _ctx (Vptr b i); temp _md_info info; temp _len (Vint (Int.repr len));
   temp _custom data; gvar sha._K256 kv)
   SEP ( (EX p : val, !!malloc_compatible (sizeof (Tstruct _hmac_ctx_st noattr)) p &&
          memory_block Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
          malloc_token Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
          data_at Tsh (Tstruct _mbedtls_md_context_t noattr) (info,(M2,p)) (Vptr b i));
         FRZL FR0)).
  { destruct Hv; try omega. rewrite if_false; trivial. clear H. subst v.
    forward. Exists (Int.repr (-20864)).
    rewrite Int.eq_true.
    entailer!. unfold seedREP. thaw FR0. unfold preseed_relate.
    Exists ((M1, (M2, M3)), (map Vint (map Int.repr initial_key), 
             (Vint (Int.repr rc), (EL, (Val.of_bool  pr_flag, Vint (Int.repr ri)))))).
    entailer!.
    unfold_data_at 2%nat. thaw FIELDS. cancel.
    rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true; simpl; trivial. rewrite int_add_repr_0_r; trivial. }
  { subst v. clear Hv. simpl. forward. entailer!. }
  Intros. subst v. clear Hv. Intros p. rename H into MCp. simpl in MCp.

  (*Alloction / md_setup succeeded. Now get md_size*)
  deadvars!.
  forward_call tt.

  (*call mbedtls_md_hmac_starts( &ctx->md_ctx, ctx->V, md_size )*)
  thaw FR0. subst.
  assert (ZL_VV: Zlength initial_key =32) by reflexivity.
  thaw FIELDS.
  freeze [4;5;6;7] FIELDS1.
  rewrite field_at_compatible'. Intros. rename H into FC_V.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial.
  rewrite <- ZL_VV.
  freeze [0;2;5;6;8;9] FR2.
  replace_SEP 1 (UNDER_SPEC.EMPTY p).
  { entailer!. 
    eapply derives_trans. 2: apply UNDER_SPEC.mkEmpty.
    rewrite data_at__memory_block. simpl. entailer!. 
  }
  forward_call (Vptr b i, ((info,(M2,p)):mdstate), 32, HMAC_DRBG_algorithms.initial_key, kv, b, Int.add i (Int.repr 12)).
  { simpl. cancel. }
  { split; trivial. red. simpl. rewrite int_max_signed_eq.
    split. trivial. split. omega. rewrite two_power_pos_equiv.
    replace (2^64) with 18446744073709551616. omega. reflexivity.
    apply isbyteZ_initialKey.
  }
  Intros. clear H.

  (*call  memset( ctx->V, 0x01, md_size )*)
  freeze [0;1;3;4] FR3.
  forward_call (Tsh, Vptr b (Int.add i (Int.repr 12)), 32, Int.one).
  { rewrite sepcon_comm. apply sepcon_derives.
     - apply data_at_memory_block.
     - cancel. }

  (*ctx->reseed_interval = MBEDTLS_HMAC_DRBG_RESEED_INTERVAL;*)
  rewrite ZL_VV.
  thaw FR3. thaw FR2. unfold md_relate. simpl.
  replace_SEP 2 (field_at Tsh t_struct_hmac256drbg_context_st [StructField _md_ctx] (info, (M2, p)) (Vptr b i)). {
    entailer!. rewrite field_at_data_at.
    simpl. rewrite field_compatible_field_address by auto with field_compatible. simpl.
    rewrite int_add_repr_0_r.
    cancel.
  }
  thaw FIELDS1. forward.
  freeze [0;4;5;6;7] FIELDS2.
  freeze [0;1;2;3;4;5;6;7;8;9] ALLSEP.

  forward_if
  (PROP ( )
   LOCAL (temp _md_size (Vint (Int.repr 32)); temp _ctx (Vptr b i); temp _md_info info;
   temp _len (Vint (Int.repr (Zlength Data))); temp _custom data; gvar sha._K256 kv;
   temp _t'4 (Vint (Int.repr 32)))
   SEP (FRZL ALLSEP)).
  { elim H; trivial. }
  { clear H.
    forward_if.
    + elim H; trivial. 
    + clear H. forward. forward. entailer!.  }
  forward. 
  deadvars!. (*drop_LOCAL 7%nat.  _t'4 *)

  (*NEXT INSTRUCTION:  ctx->entropy_len = entropy_len * 3 / 2*)
  thaw ALLSEP. thaw FIELDS2. forward.

  assert (FOURTYEIGHT: Int.unsigned (Int.mul (Int.repr 32) (Int.repr 3)) / 2 = 48).
  { rewrite mul_repr. simpl.
    rewrite Int.unsigned_repr. reflexivity. rewrite int_max_unsigned_eq; omega. }
  set (myABS := HMAC256DRBGabs initial_key initial_value rc 48 pr_flag 10000) in *.
  assert (myST: exists ST:hmac256drbgstate, ST =
    ((info, (M2, p)), (map Vint (list_repeat 32 Int.one), (Vint (Int.repr rc),
        (Vint (Int.repr 48), (Val.of_bool pr_flag, Vint (Int.repr 10000))))))). eexists; reflexivity.
  destruct myST as [ST HST].

  freeze [0;1;2;3;4] FR_CTX.
  freeze [3;4;6;7;8] KVStreamInfoDataFreeBlk.

  (*NEXT INSTRUCTION: mbedtls_hmac_drbg_reseed( ctx, custom, len ) *)
  freeze [1;2;3] INI.
  specialize (Forall_list_repeat isbyteZ 32 1); intros IB1.
  replace_SEP 0 (
         data_at Tsh t_struct_hmac256drbg_context_st ST (Vptr b i) *
         hmac256drbg_relate myABS ST).
  { entailer!. thaw INI. clear - FC_V IB1. (*KVStreamInfoDataFreeBlk.*) thaw FR_CTX.
    apply andp_right. apply prop_right. repeat split; trivial. apply IB1. split; omega.
    unfold_data_at 2%nat. 
    cancel. unfold md_full; simpl.
    rewrite field_at_data_at; simpl.
    unfold field_address. rewrite if_true; simpl; trivial.
    cancel.
    apply UNDER_SPEC.REP_FULL.
  }

  clear INI.
  thaw KVStreamInfoDataFreeBlk. freeze [3;7] OLD_MD.
  forward_call (Data, data, Zlength Data, Vptr b i, ST, myABS, kv, Info, s).
  { unfold hmac256drbgstate_md_info_pointer.
    subst ST; simpl. cancel.
  }
  { subst myABS; simpl. rewrite <- initialize.max_unsigned_modulus in *; rewrite int_max_unsigned_eq.
    split. omega. (* rewrite int_max_unsigned_eq; omega.*)
    split. reflexivity.
    split. reflexivity.
    split. omega.
    split. (*change Int.modulus with 4294967296.*) omega.
    split. (* change Int.modulus with 4294967296.*)
       unfold contents_with_add. if_tac. omega. rewrite Zlength_nil; omega.
    split. apply IB1. split; omega.
    assumption.
  }

  Intros v.
  assert (ZLc': Zlength (contents_with_add data (Zlength Data) Data) = 0 \/
                 Zlength (contents_with_add data (Zlength Data) Data) = Zlength Data).
         { unfold contents_with_add. if_tac. right; trivial. left; trivial. }
  forward.
  deadvars!. 
  forward_if (
   PROP ( v = nullval)
   LOCAL (temp _ret v; temp _t'7 v;
   temp _entropy_len (Vint (Int.repr 32)); temp _ctx (Vptr b i);
   gvar sha._K256 kv)
   SEP (reseedPOST v Data data (Zlength Data) s
          myABS (Vptr b i) Info kv ST; FRZL OLD_MD)).
  { rename H into Hv. forward. simpl. Exists v.
    apply andp_right. apply prop_right; trivial.
    apply andp_right. apply prop_right; split; trivial.
    unfold reseedPOST.

    remember ((zlt 256 (Zlength Data) || zlt 384 (hmac256drbgabs_entropy_len myABS + Zlength Data)) %bool) as d.
    unfold myABS in Heqd; simpl in Heqd.
    destruct (zlt 256 (Zlength Data)); simpl in Heqd.
    + omega.
    + destruct (zlt 384 (48 + Zlength Data)); simpl in Heqd; try omega.
      subst d.
      unfold hmac256drbgstate_md_info_pointer, hmac256drbg_relate; simpl. Intros.
      rename H into RV.
      remember (mbedtls_HMAC256_DRBG_reseed_function s myABS
         (contents_with_add data (Zlength Data) Data)) as MRS.
      rewrite (ReseedRes _ _ _ RV). cancel.
      unfold return_value_relate_result in RV.
      assert (ZLc'256F: Zlength (contents_with_add data (Zlength Data) Data) >? 256 = false).
      { apply Zgt_is_gt_bool_f. destruct ZLc' as [ZLc' | ZLc']; rewrite ZLc'; trivial. omega. }
      unfold hmac256drbgabs_common_mpreds, hmac256drbgstate_md_info_pointer.
      destruct MRS.
      - exfalso. inv RV. simpl in Hv. discriminate.
      - simpl. Intros. Exists p. thaw OLD_MD. cancel.
        subst myABS. rewrite <- instantiate256_reseed in HeqMRS; trivial.
        rewrite RES in HeqMRS. inv HeqMRS. 
  }
  { rename H into Hv. forward. entailer!. 
    apply negb_false_iff in Hv.
    symmetry in Hv; apply binop_lemmas2.int_eq_true in Hv; subst v. trivial.
  }
  deadvars!. Intros. subst v. unfold reseedPOST. 

  remember ((zlt 256 (Zlength Data)
          || zlt 384 (hmac256drbgabs_entropy_len myABS + Zlength Data))%bool) as d.
  destruct d; Intros.

  assert (ZLc'256F: Zlength (contents_with_add data (Zlength Data) Data) >? 256 = false).
      { destruct ZLc' as [HH | HH]; rewrite HH. reflexivity.
        apply Zgt_is_gt_bool_f. omega. }
  subst myABS.
  rewrite <- instantiate256_reseed, RES; trivial. clear - RES HST ZLc'256F.
  destruct handle as [[[[newV newK] newRC] dd] newPR].
  unfold hmac256drbgabs_common_mpreds.
  simpl. subst ST. unfold hmac256drbgstate_md_info_pointer. simpl.
  unfold_data_at 1%nat. 
  freeze [0;1;2;4;5;6;7;8;9;10;11;12;13] ALLSEP.
  forward. forward.
 
  Exists Int.zero. simpl.
  apply andp_right. apply prop_right; trivial.
  apply andp_right. apply prop_right; split; trivial. 
  Exists p. Exists (M1, (M2, M3)).
  thaw ALLSEP. thaw OLD_MD.
  Transparent hmac256drbgabs_reseed. unfold hmac256drbgabs_reseed. Opaque hmac256drbgabs_reseed.
  rewrite <- instantiate256_reseed, RES; trivial. simpl. 
  normalize.
  cancel.
  unfold AREP, REP. 
  Exists Info 
     ((info, (M2, p),
     (map Vint (map Int.repr newV),
     (Vint (Int.repr newRC),
     (Vint (Int.repr 32), (Val.of_bool newPR, Vint (Int.repr 10000))))))).
  simpl; normalize.
  apply andp_right.
  { apply prop_right.
    erewrite instantiate256_reseed with (rc:=newRC)(ri:=32) in RES; try eassumption.
    apply mbedtls_HMAC256_DRBG_reseed_functionWF in RES.
    unfold WF; simpl; intuition. red; rewrite int_max_signed_eq; omega. } 
  unfold_data_at 2%nat; cancel. 
  apply hmac_interp_empty.
Time Qed. (*Coq8.6: 24secs*)

Lemma body_hmac_drbg_seed_buf: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_seed_buf drbg_seed_buf_abs_spec.
Proof.
  start_function.
  abbreviate_semax.
  rename H into HDlen1; rename H0 into HDlen2; rename H1 into HData.
  unfold seedbufREP.
  rewrite extract_exists_in_SEP. Intros Ctx.
  rename H into WF1. rename H0 into WF2. rename H1 into WF3. rename H2 into WF4. 
  rewrite data_at_isptr with (p:=ctx). Intros.
  destruct ctx; try contradiction; clear Pctx.
  unfold_data_at 1%nat.
  destruct Ctx as [mds [V [RC [EL [PR RI]]]]]; simpl.
  destruct mds as [M1 [M2 M3]]. 
  freeze [1;2;3;4;5] FIELDS. unfold hmac256drbgstate_md_info_pointer; simpl.
  rewrite field_at_compatible'. Intros. rename H into FC_mdx.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial. rewrite int_add_repr_0_r.
  freeze [0;2;3;4;5] FR0.
  time forward_call ((M1,(M2,M3)), Vptr b i, Vint (Int.repr 1), info).

  Intros v. rename H into Hv. simpl.
  forward. 
  forward_if (
     PROP (v=0)
   LOCAL (temp _ret (Vint (Int.repr v)); temp _t'2 (Vint (Int.repr v));
   temp _ctx (Vptr b i); temp _md_info info; temp _data_len (Vint (Int.repr d_len));
   temp _data data; gvar sha._K256 kv)
   SEP ( (EX p : val, !!malloc_compatible (sizeof (Tstruct _hmac_ctx_st noattr))p &&
            memory_block Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
            malloc_token Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
            data_at Tsh (Tstruct _mbedtls_md_context_t noattr) (info,(M2,p)) (Vptr b i));
            FRZL FR0)).
  { destruct Hv; try omega. rewrite if_false; trivial.
    forward. Exists (Vint (Int.repr (-20864))). rewrite if_true; trivial.
    entailer!.
    thaw FR0; unfold seedbufREP. cancel.
    Exists (M1, (M2, M3), (V, (RC, (EL, (PR, RI))))); unfold hmac256drbgstate_md_info_pointer; simpl.
    entailer!. 
    unfold_data_at 2%nat. thaw FIELDS. cancel. rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true; simpl; trivial. rewrite int_add_repr_0_r; trivial. }
  { subst v; clear Hv. rewrite if_true; trivial.
    forward. entailer!.
  }
  Intros. subst v. clear Hv. Intros p. rename H into MCp.

  forward_call tt.

  thaw FR0. unfold hmac256drbg_relate. destruct I. Intros; subst.
  rename V0 into V. rename H0 into lenV. rename H1 into isbtV.
  thaw FIELDS.
  freeze [4;5;6;7] FIELDS1.
  rewrite field_at_compatible'. Intros. rename H into FC_V.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial.

  freeze [0;2;5;6;8] FR2.
  replace_SEP 1 (UNDER_SPEC.EMPTY p).
  { entailer!. 
    eapply derives_trans. 2: apply UNDER_SPEC.mkEmpty.
    rewrite data_at__memory_block. simpl. entailer!. 
  }
  forward_call (Vptr b i, (((*M1*)info,(M2,p)):mdstate), 32, V, kv, b, Int.add i (Int.repr 12)).
  { rewrite lenV; simpl. cancel. }
  { split; trivial. red. simpl. rewrite int_max_signed_eq, lenV.
    split. trivial. split. omega. rewrite two_power_pos_equiv.
    replace (2^64) with 18446744073709551616 by reflexivity. omega.
  }
  Intros.

  forward_call tt.

  freeze [0;1;3;4] FR3. rewrite lenV.
  forward_call (Tsh, Vptr b (Int.add i (Int.repr 12)), 32, Int.one).
  { rewrite sepcon_comm. apply sepcon_derives. 2: cancel.
    eapply derives_trans. apply data_at_memory_block. cancel.
  }

  thaw FR3. thaw FR2. unfold md_relate. simpl.
  freeze [1;3;5;6;7;8] OTHER.
  freeze [1;2;3] INI.

  assert (exists xx:reptype t_struct_hmac256drbg_context_st, xx =
   (((*M1*)info, (M2, p)),
    (list_repeat (Z.to_nat 32) (Vint Int.one),
     (Vint (Int.repr reseed_counter),
      (Vint (Int.repr entropy_len),
       (Val.of_bool prediction_resistance,
        (Vint (Int.repr reseed_interval)))))))). eexists; reflexivity.
  destruct H as [xx XX].

  replace_SEP 0
    (data_at Tsh t_struct_hmac256drbg_context_st xx (Vptr b i)).
  { entailer. unfold_data_at 1%nat.
    thaw INI.
    rewrite field_at_data_at. unfold field_address. rewrite if_true. 2: assumption.
    simpl. rewrite int_add_repr_0_r.
    unfold t_struct_md_ctx_st. cancel.
    clear OTHER. thaw FIELDS1. cancel.
    rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true. 2: assumption. simpl. cancel.
  }
  clear INI. thaw OTHER.
  specialize (Forall_list_repeat isbyteZ 32 1); intros IB1.
  set (ABS:= HMAC256DRBGabs V (list_repeat 32 1) reseed_counter entropy_len prediction_resistance reseed_interval) in *.
  replace_SEP 1 (hmac256drbg_relate  ABS xx).
  { entailer!. subst ABS; unfold md_full. simpl.
    apply andp_right. apply prop_right. repeat split; trivial. apply IB1. split; omega.
    apply UNDER_SPEC.REP_FULL.
  }

  forward_call (Data, data, d_len, Vptr b i, xx, ABS, kv, Info).
  { subst xx. unfold hmac256drbgstate_md_info_pointer; simpl. cancel. 
  }
  { subst ABS; simpl. repeat split; trivial; try omega. apply IB1. split; omega.
  }

  freeze [0;1;2;3;4] ALLSEP.
  forward. Exists (Vint (Int.repr 0)). rewrite if_false; [ | intros N; inv N]. 
  thaw ALLSEP.
  unfold hmac256drbgabs_common_mpreds. simpl.
  remember(HMAC256_DRBG_functional_prog.HMAC256_DRBG_update (contents_with_add data d_len Data) V
             (list_repeat 32 1)) as HH.
  destruct HH as [KEY VALUE]. unfold hmac256drbgstate_md_info_pointer; simpl.
  Exists KEY VALUE p (M1, (M2, M3)). normalize. simpl in *.
  apply andp_right.
  { apply prop_right. split; trivial. split; trivial. }
  cancel. unfold REP. 
  Exists (info, (M2, p),
          (map Vint (map Int.repr VALUE),
          (Vint (Int.repr reseed_counter),
          (Vint (Int.repr entropy_len),
          (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))); simpl.
  entailer!.
  red; simpl. intuition. 
Time Qed. (*Coq8.6: 12secs*)

Require Import hmacdrbg.verif_hmac_drbg_reseed. (*for use of lemma REST*)
Opaque hmac256drbgabs_reseed.
Opaque mbedtls_HMAC256_DRBG_reseed_function. 

Lemma body_hmac_drbg_reseed: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_hmac_drbg_reseed drbg_reseed_spec_abs.
Proof.
  start_function. rename H into addlenRange. rename H0 into Haddlen. 
  rename H1 into BOUND. rename H2 into isbt_contents.
  rename lvar0 into seed.
  unfold AREP. focus_SEP 2.
  rewrite extract_exists_in_SEP. Intros Info. unfold REP.
  rewrite extract_exists_in_SEP. Intros i. rename H into WFI. 
  destruct I.
  destruct i as [md_ctx' [V' [reseed_counter' [entropy_len' [prediction_resistance' reseed_interval']]]]].
  unfold hmac256drbg_relate.
  Intros. simpl in *.
  rename H into XH1.
  rename H0 into XH2.
  rename H1 into XH3.
  rename H2 into XH4.
  rename H3 into El2.
  rename H4 into XH6.
  rename H5 into XH7. red in WFI; simpl in WFI.
  rewrite da_emp_isptrornull. (*needed later*)
  rewrite data_at_isptr with (p:=ctx).
  Intros.

  (* entropy_len = ctx->entropy_len *)
  simpl in *.
  remember (contents_with_add additional add_len contents) as contents'.
  assert (ZLc': Zlength contents' = 0 \/ Zlength contents' = Zlength contents).
    { subst contents'. unfold contents_with_add.
      destruct (eq_dec add_len 0); simpl.
        rewrite andb_false_r. left; apply Zlength_nil.
        destruct (Memory.EqDec_val additional nullval); simpl. left; apply Zlength_nil.
        right; trivial.
    }

  freeze [1;2;3;4;5;6] FR1.
  forward. 

  remember (orb (zlt 256 add_len) (zlt 384 (entropy_len + add_len))) as add_len_too_high.

  (* if (len > MBEDTLS_HMAC_DRBG_MAX_INPUT ||
        entropy_len + len > MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT) *)
  freeze [0;1] FR2.
  forward_if (PROP  ()
      LOCAL  (temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      temp _t'1 (Val.of_bool add_len_too_high);
      gvar sha._K256 kv)
      SEP  (FRZL FR2)).
  { forward. entailer!. }
  { forward. (*red in WFI; simpl in WFI.*) entailer!. simpl.
      unfold Int.ltu; simpl.
      rewrite add_repr.
      rewrite Int.unsigned_repr. 2: rewrite int_max_unsigned_eq; omega.
      rewrite Int.unsigned_repr_eq, Zmod_small.
      + destruct (zlt 384 (entropy_len + (Zlength contents))); simpl; try reflexivity.
      + clear - H WFI addlenRange.
        rewrite <-initialize.max_unsigned_modulus, int_max_unsigned_eq; omega.
  }

  forward_if (PROP  (add_len_too_high = false)
      LOCAL  (temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      gvar sha._K256 kv)
      SEP (FRZL FR2)
  ).
  { rewrite H in *. subst add_len_too_high. forward.
    Exists seed (Vint (Int.neg (Int.repr 5))). unfold AREP. Exists Info.
    unfold REP. entailer!.
    thaw FR2.
    Exists (md_ctx',
            (map Vint (map Int.repr V),
            (Vint (Int.repr reseed_counter),
            (Vint (Int.repr entropy_len),
            (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))).
    simpl; cancel. entailer!.
    thaw FR1. cancel.
  }
  {
    forward.
    entailer!.
  }
  Intros. unfold POSTCONDITION, abbreviate; clear POSTCONDITION. rewrite H in *; clear H add_len_too_high.
  abbreviate_semax.
  symmetry in Heqadd_len_too_high; apply orb_false_iff in Heqadd_len_too_high; destruct Heqadd_len_too_high.

  assert (AL256: 256 >= add_len).
  { destruct (zlt 256 add_len); try discriminate; trivial. }
  assert (EL384 : 384 >= entropy_len + add_len).
  { destruct ( zlt 384 (entropy_len + add_len)); try discriminate; trivial. }

  thaw FR2. thaw FR1.
  unfold hmac256drbgstate_md_info_pointer; simpl. freeze [0;1;2;4;5;6;7] FR3.
  (* memset( seed, 0, MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT ); *)
  forward_call (Tsh, seed, 384, Int.zero).
  { rewrite data_at__memory_block.
    change (sizeof (tarray tuchar 384)) with 384.
    normalize. cancel.
  }

  assert_PROP (field_compatible (tarray tuchar 384) [] seed) as Hfield by entailer!.
  replace_SEP 0 ((data_at Tsh (tarray tuchar entropy_len)
         (list_repeat (Z.to_nat entropy_len) (Vint Int.zero)) seed) * (data_at Tsh (tarray tuchar (384 - entropy_len))
         (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero)) (offset_val entropy_len seed))).
  {
    erewrite <- data_at_complete_split with (length:=384)(AB:=list_repeat (Z.to_nat 384) (Vint Int.zero)); 
    repeat rewrite Zlength_list_repeat; trivial; try omega. 
    solve [go_lower; apply derives_refl]. 
    solve [rewrite Zplus_minus; assumption].
    rewrite list_repeat_app, Z2Nat.inj_sub; try omega. rewrite le_plus_minus_r; trivial. apply Z2Nat.inj_le; try omega.
  }
  flatten_sepcon_in_SEP.

  replace_SEP 0 (memory_block Tsh entropy_len seed).
  { entailer!.
     eapply derives_trans. apply data_at_memory_block. 
     simpl. rewrite Z.max_r, Z.mul_1_l; trivial; omega.
  }

  (* get_entropy(seed, entropy_len ) *)
  thaw FR3. freeze [1;2;3;4;5;7] FR4.
  forward_call (Tsh, s, seed, entropy_len).
  { split. split; try omega. rewrite int_max_unsigned_eq. omega.
    apply writable_share_top.
  }
  Intros vret. rename H1 into ENT.
  assert (AL256': add_len >? 256 = false).
  { remember (add_len >? 256) as d.
    destruct d; symmetry in Heqd; trivial.
    apply Zgt_is_gt_bool in Heqd.
    destruct (zlt 256 add_len); try discriminate; omega.
  }
  assert (EAL256': (entropy_len + add_len)  >? 384 = false).
  { remember (entropy_len + add_len >? 384) as d.
    destruct d; symmetry in Heqd; trivial.
    apply Zgt_is_gt_bool in Heqd.
    destruct (zlt 384 (entropy_len + add_len)); try discriminate; omega.
  }

  (* if( get_entropy(seed, entropy_len ) != 0 ) *)
  freeze [0;1;2] FR5.
  forward_if (
      PROP  (vret=Vzero)
      LOCAL  (temp _t'2 vret;
      temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      gvar sha._K256 kv)
      SEP (FRZL FR5)
  ).
  { (* != 0 case *)
    forward.
    Exists seed (Vint (Int.neg (Int.repr (9)))). 
    Exists (mbedtls_HMAC256_DRBG_reseed_function s
           (HMAC256DRBGabs key V reseed_counter entropy_len
              prediction_resistance reseed_interval)
              (contents_with_add additional (Zlength contents) contents)).
    entailer.
    unfold AREP, REP.
    Exists Info
      (md_ctx',
         (map Vint (map Int.repr V),
         (Vint (Int.repr reseed_counter),
         (Vint (Int.repr entropy_len),
         (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))).


    unfold return_value_relate_result, get_entropy in ENT.
    simpl in ENT.
    remember (ENTROPY.get_bytes (Z.to_nat entropy_len) s) as  GE.
    destruct GE.
    + inv ENT. discriminate.
    + thaw FR5. unfold get_entropy. rewrite <- HeqGE.
      unfold hmac256drbg_relate.
Transparent hmac256drbgabs_reseed. 
unfold hmac256drbgabs_reseed.
Opaque hmac256drbgabs_reseed.
      remember (mbedtls_HMAC256_DRBG_reseed_function s
            (HMAC256DRBGabs key V reseed_counter 32 prediction_resistance
               reseed_interval) (contents_with_add additional (Zlength contents) contents)) as M.
      remember (mbedtls_HMAC256_DRBG_reseed_function s
             (HMAC256DRBGabs key V reseed_counter 32 prediction_resistance
                reseed_interval) contents).
Transparent mbedtls_HMAC256_DRBG_reseed_function. 
      unfold mbedtls_HMAC256_DRBG_reseed_function in *.
Opaque mbedtls_HMAC256_DRBG_reseed_function.
      unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_reseed_function, DRBG_functions.DRBG_reseed_function in *.
      rewrite andb_negb_r in *.
      unfold return_value_relate_result in ENT.
      unfold get_entropy in *; simpl in *. rewrite <- HeqGE in *.
      rewrite AL256' in *.
      remember (Zlength (contents_with_add additional (Zlength contents) contents)) as ZLa.
      assert (ZLa256: ZLa >? 256 = false).
      { destruct ZLc' as [PP | PP]; rewrite PP; trivial. }
      rewrite ZLa256 in *. subst M r. normalize. simpl. cancel.
      unfold get_entropy. simpl. 
      
      apply andp_right. 
      { destruct WFI as [WF1 [WF2 [WF3 [WF4 WF5]]]].
        apply prop_right. red in WF3. repeat split; simpl; trivial;  omega. }
      thaw FR4. cancel.
      rewrite data_at__memory_block. entailer!.
      destruct seed; inv Pseed. unfold offset_val.
      rewrite <- repr_unsigned with (i:=i).
      assert (XX: sizeof (tarray tuchar 384) = entropy_len + (384 - entropy_len)).
      { simpl. omega. }
      rewrite XX.
      rewrite (memory_block_split Tsh b (Int.unsigned i) entropy_len (384 - entropy_len)), add_repr; try omega.
      cancel.
      eapply derives_trans. apply data_at_memory_block.
          simpl. rewrite Z.max_r, Z.mul_1_l; try omega; trivial.
      rewrite Zplus_minus. cbv; trivial.
      assert (Int.unsigned i >= 0) by (pose proof (Int.unsigned_range i); omega).
      split. omega.
      clear - Hfield. red in Hfield; simpl in Hfield. omega.
  }
  {
    forward.
    entailer!. clear FR4 FR5. 
    apply negb_false_iff in H1. symmetry in H1; apply binop_lemmas2.int_eq_true in H1.
    subst vret; split; trivial.
  }
  Intros. subst vret. unfold return_value_relate_result in ENT.
  (* now that we know entropy call succeeded, use that fact to simplify the SEP clause *)
  remember (entropy.ENTROPY.get_bytes (Z.to_nat entropy_len) s) as entropy_result.
  unfold entropy.get_entropy in ENT;
  rewrite <- Heqentropy_result in ENT.
  destruct entropy_result; [|
    normalize;
    simpl in ENT; destruct e; [inversion ENT | inversion ENT ]
    ].
  2: solve [ destruct ENT_GenErrAx as [EC1 _]; elim EC1; trivial ].
  clear ENT.

  rename l into entropy_bytes.
  thaw FR5. thaw FR4.
(*  eapply REST with (s0:=s0)(contents':=contents'); trivial.*)
  destruct WFI as [WFI1 [WFI2 [WFI3 WFI4]]].
  eapply semax_pre_post.
  Focus 3. 
    eapply (@REST Espec contents additional add_len ctx md_ctx'
              V' reseed_counter' entropy_len' prediction_resistance' reseed_interval' key V
              reseed_counter entropy_len prediction_resistance reseed_interval kv Info s seed
              addlenRange WFI1); try reflexivity; trivial; try omega.
    subst contents'; try omega.
    subst contents'; trivial.
    eassumption.
  { unfold hmac256drbgstate_md_info_pointer. entailer!. }
  intros. unfold POSTCONDITION, abbreviate. old_go_lower.
  destruct ek; [normalize | normalize | normalize | ].
  unfold reseedPOST; destruct vl; normalize. simpl.
  Exists x v. rewrite <- Heqcontents' in *. 
  unfold hmac256drbgabs_common_mpreds, hmac256drbgstate_md_info_pointer; simpl.
  remember (mbedtls_HMAC256_DRBG_reseed_function s
              (HMAC256DRBGabs key V reseed_counter entropy_len
                 prediction_resistance reseed_interval) contents') as r.
  Exists r. normalize. entailer!. Exists Info. 
  remember (HMAC_DRBG_algorithms.HMAC_DRBG_update HMAC256
             (entropy_bytes ++ contents_with_add additional (Zlength contents) contents)
             key V) as f. clear Heqf. destruct f.
  remember (HMAC256DRBGabs l l0 1 entropy_len prediction_resistance
         (*10000*)reseed_interval). clear Heqh.
  cancel.
  remember (hmac256drbgabs_to_state
     (hmac256drbgabs_reseed
        (HMAC256DRBGabs key V reseed_counter entropy_len
           prediction_resistance (*10000*)reseed_interval) s
        (contents_with_add additional (Zlength contents) contents))
     (md_ctx',
     (map Vint (map Int.repr V),
     (Vint (Int.repr reseed_counter),
     (Vint (Int.repr entropy_len),
     (Val.of_bool prediction_resistance, Vint (Int.repr (*10000*)reseed_interval))))))) as st.
  Exists st. normalize.
  apply andp_right.
  { unfold hmac256drbg_relate. normalize. 
    remember (hmac256drbgabs_reseed
    (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
       (*10000*)reseed_interval) s (contents_with_add additional (Zlength contents) contents)). 
    destruct h0. subst st. simpl. normalize.
Transparent  hmac256drbgabs_reseed.
    unfold hmac256drbgabs_reseed in Heqh0.
Opaque  hmac256drbgabs_reseed.
    remember (mbedtls_HMAC256_DRBG_reseed_function s
         (HMAC256DRBGabs key V reseed_counter entropy_len
            prediction_resistance (*10000*)reseed_interval)
         (contents_with_add additional (Zlength contents) contents)) as r.
    destruct r.
    + destruct d as [[[[? ?] ?] ?] ?]; simpl. inv Heqh0.
      symmetry in Heqr. apply mbedtls_HMAC256_DRBG_reseed_functionWF in Heqr.  
      apply prop_right; red; simpl. red in WFI3. repeat split; trivial; omega. 
    + inv Heqh0. apply prop_right; red; simpl. red in WFI3. repeat split; trivial; omega. }
 
  cancel.
Time Qed.  (*Coq8.6: 15sec*)

Opaque hmac256drbgabs_generate.
Lemma body_hmac_drbg_random_abs: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_random drbg_random_abs_spec.
Proof.
  start_function.
  abbreviate_semax.
  rename H0 into M. destruct H as [N1 N2].
  unfold AREP. focus_SEP 1.
  rewrite extract_exists_in_SEP. Intros Info. unfold REP.
  rewrite extract_exists_in_SEP. Intros i. 
  destruct H as [WF1 [WF2 [WF3 [WF4 WF5]]]].
  forward. simpl.
  forward_call (@nil Z, nullval, Z0, output, n, ctx, i,
                I, kv, Info, s).
  { rewrite da_emp_null; trivial. cancel. }
  { rewrite Zlength_nil.
    repeat (split; try assumption; try rewrite int_max_unsigned_eq; try omega).
    constructor. }
  Intros v. forward. unfold mbedlts_generate in M.
  remember (mbedtls_HMAC256_DRBG_generate_function s I n []) as q; destruct q; try discriminate. 
  destruct p as [bytes' J].
  destruct J as [[[[V K] RC] x] PR]. inv M.
  unfold generatePOST, contents_with_add; simpl. 
  apply Zgt_is_gt_bool_f in N2. rewrite N2 in *. 
  rewrite <- Heqq in *.
  unfold return_value_relate_result, da_emp; simpl. 
  symmetry in Heqq.
  apply AUX in Heqq. rewrite Heqq.
  Intros. inversion H0; clear H0; subst v.
  assert_PROP (n=Zlength(map Vint (map Int.repr bytes))) as HN by entailer!.
  entailer!. 
  Exists Info
     (hmac256drbgabs_to_state
       (hmac256drbgabs_generate I s (Zlength (map Vint (map Int.repr bytes))) []) i).
  rewrite Heqq. unfold hmac256drbgabs_common_mpreds. 
  normalize. 
  apply andp_right. 
  + apply prop_right. red. simpl.
    apply hmac256drbgabs_generateWF in Heqq. intuition.
    omega. intuition. red in WF3. clear - WF3. omega. 
  + cancel. 
    apply orp_left; [ trivial | normalize].
Time Qed. (*Coq8.6: 2.3secs*)

Opaque hmac256drbgabs_generate.
Lemma body_hmac_drbg_random_abs1: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_random drbg_random_abs_spec1.
Proof.
  start_function.
  abbreviate_semax.
  destruct H as [N1 N2]. rename H0 into M.
  unfold AREP. focus_SEP 1.
  rewrite extract_exists_in_SEP. Intros Info. unfold REP.
  rewrite extract_exists_in_SEP. Intros i. 
  destruct H as [WF1 [WF2 [WF3 [WF4 WF5]]]].
  forward. simpl.
  forward_call (@nil Z, nullval, Z0, output, n, ctx, i,
                I, kv, Info, s).
  { rewrite da_emp_null; trivial. cancel. }
  { rewrite Zlength_nil.
    repeat (split; try assumption; try rewrite int_max_unsigned_eq; try omega).
    constructor. }
  Intros v. forward. destruct J as [[[[V K] RC] x] PR].
  unfold generatePOST, contents_with_add; simpl. 
  apply Zgt_is_gt_bool_f in N2. rewrite N2 in *. 
  rewrite M in *.
  unfold return_value_relate_result, da_emp; simpl. 
  Exists (hmac256drbgabs_generate I s n []).
  apply AUX in M. rewrite <- M.
  Intros. inversion H0; clear H0; subst v.
  assert_PROP (n=Zlength(map Vint (map Int.repr bytes))) as HN by entailer!.
  entailer!.
  Exists Info
     (hmac256drbgabs_to_state
       (hmac256drbgabs_generate I s (Zlength (map Vint (map Int.repr bytes))) []) i).
  unfold hmac256drbgabs_common_mpreds; simpl.
  normalize.
  apply andp_right. 
  + apply prop_right. rewrite M; red. simpl.
    apply hmac256drbgabs_generateWF in M. intuition.
    omega. intuition. red in WF3. omega. 
  + cancel.
    apply orp_left; [ trivial | normalize].
Time Qed. (*Coq8.6: 2.3secs*)

Require Import hmacdrbg.verif_hmac_drbg_update.

Lemma HMAC_DRBG_update_concreteWF c K V k v
      (H: (k, v) = HMAC_DRBG_update_concrete HMAC256 c K V):
      Zlength v = 32 /\ Forall isbyteZ v.
Proof.
  rewrite <- HMAC_DRBG_update_concrete_correct in H.
  eapply HMAC_DRBG_updateWF; eauto. 
Qed.

Lemma body_hmac_drbg_update_abs: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_hmac_drbg_update drbg_update_abs_spec.
Proof. start_function. rename lvar1 into K. rename lvar0 into sep.
  rename H into AL1. rename H0 into HAL. rename H1 into isbtContents.
  unfold AREP. focus_SEP 2.
  rewrite extract_exists_in_SEP. Intros Info.
  unfold REP. 
  rewrite extract_exists_in_SEP. Intros i.
  rename H into WFI.
  destruct i as [IS1 [IS2 [IS3 [IS4 [IS5 IS6]]]]].
  rewrite da_emp_isptrornull.

  (* info = md_ctx.md_info *)
  destruct IS1 as [IS1a [IS1b IS1c]]. simpl.
  rewrite data_at_isptr with (p:=ctx).
  unfold hmac256drbgstate_md_info_pointer. simpl.
  rewrite data_at_isptr with (p:=IS1a).
  Intros.
  freeze [1;3;4;5;6] FR0.
  freeze [0;2] FR1.

  Time forward. 
  thaw FR1.

  (* md_len = mbedtls_md_get_size( info ); *)
  freeze [0;1] FR1.
  forward_call tt.

  remember (andb (negb (eq_dec additional nullval)) (negb (eq_dec add_len 0))) as na.
  freeze [0;1] FR2. clear PIS1a.
  forward_if (
      PROP  ()
      LOCAL  (temp _md_len (Vint (Int.repr 32)); lvar _K (tarray tuchar 32) K;
      temp _ctx ctx;
      lvar _sep (tarray tuchar 1) sep;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
      temp _t'2 (Val.of_bool na);
      gvar sha._K256 kv)
      SEP  (FRZL (FR2))).
  {
    (* show that add_len <> 0 implies the post condition *)
    forward.
    { entailer. destruct additional; try contradiction; simpl in PNadditional.
      subst i; simpl. entailer!. (* simpl. *)
      thaw FR2. thaw FR1. thaw FR0. normalize.
      rewrite da_emp_ptr. normalize.
      eapply denote_tc_test_eq_split. 
      auto 50 with valid_pointer. (* TODO regression, this should have solved it *)
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer2. 
      apply sepcon_valid_pointer2.
      apply sepcon_valid_pointer2. 
      apply sepcon_valid_pointer2. 
      apply data_at_valid_ptr; auto. auto 50 with valid_pointer.
    }

    { entailer!.
      destruct additional; simpl in PNadditional; try contradiction.
      subst i; simpl; trivial.
      simpl. destruct (initial_world.EqDec_Z add_len 0); trivial; omega.
    }
  }

  {
    (* show that add_len = 0 implies the post condition *)
    forward.
    entailer!. simpl. rewrite andb_false_r. reflexivity.
  }

  remember (update_rounds na) as rounds. unfold update_rounds in Heqrounds.
  forward_if ( PROP  ()
      LOCAL  (temp _md_len (Vint (Int.repr 32)); lvar _K (tarray tuchar 32) K;
      temp _ctx ctx;
      lvar _sep (tarray tuchar 1) sep;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
      temp _t'3 (Vint (Int.repr rounds));
      gvar sha._K256 kv)
      SEP  (FRZL FR2)
  ).
  {
    (* non_empty_additional = true *)
    forward. rewrite H in *; clear H.
    entailer!.
  }
  {
    (* non_empty_additional = false *)
    forward. rewrite H in *; clear H.
    entailer!.
  }

  forward.
  (*deadvars!. VST Issue*)
  drop_LOCAL 7%nat. (*_t'3*)
  remember (hmac256drbgabs_key I) as initial_key.
  remember (hmac256drbgabs_value I) as initial_value.

  (* for ( sep_value = 0; sep_value < rounds; sep_value++ ) *)
  Time forward_for_simple_bound rounds (EX i: Z,
      PROP  ()
      LOCAL ((*In VST 1.6, we need to add the entry for temp*)
               temp _rounds (Vint (Int.repr rounds));
       temp _md_len (Vint (Int.repr 32));
       temp _ctx ctx;
       lvar _K (tarray tuchar 32) K; lvar _sep (tarray tuchar 1) sep;
       temp _additional additional; temp _add_len (Vint (Int.repr add_len));
       gvar sha._K256 kv
         )
      SEP  (
        (EX key: list Z, EX value: list Z, EX final_state_abs: hmac256drbgabs,
          !!(
              (key, value) = HMAC_DRBG_update_round HMAC256
                (*contents*) (if na then contents else [])
                initial_key initial_value (Z.to_nat i)
              /\ key = hmac256drbgabs_key final_state_abs
              /\ value = hmac256drbgabs_value final_state_abs
              /\ hmac256drbgabs_metadata_same final_state_abs I
              /\ Zlength value = Z.of_nat SHA256.DigestLength
              /\ Forall general_lemmas.isbyteZ value
            ) &&
           (hmac256drbgabs_common_mpreds final_state_abs
             (*initial_state*) ((IS1a,(IS1b,IS1c)),(IS2,(IS3,(IS4,(IS5,IS6)))))
              ctx Info)
         );
        (data_at_ Tsh (tarray tuchar 32) K);
        (da_emp Tsh (tarray tuchar (Zlength contents)) (map Vint (map Int.repr contents)) additional);
        (data_at_ Tsh (tarray tuchar 1) sep );
        (spec_sha.K_vector kv)
         )
  ). (* 2 *)
  {
    (* Int.min_signed <= 0 <= rounds *)
    rewrite Heqrounds; destruct na; auto.
  }
  {
    (* rounds <= Int.max_signed *)
    rewrite Heqrounds; destruct na; auto.
  }
  {
    (* pre conditions imply loop invariant *)
    entailer!.
    Exists (hmac256drbgabs_key I) (hmac256drbgabs_value I) I.
    destruct I. simpl. Time entailer!.
    + destruct WFI as [WFIa WFIb]. simpl in *. split. apply WFIa. apply WFIb.
    + thaw FR2. thaw FR1. thaw FR0. cancel.
    unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state. cancel.
    unfold hmac256drbg_relate. entailer!.
  }
  {
    (* loop body *)
    Intros key value state_abs. 
    clear FR2 FR1 FR0.

    + simpl.
    unfold hmac256drbgabs_common_mpreds. repeat flatten_sepcon_in_SEP.
    unfold hmac256drbgabs_to_state. simpl. destruct state_abs. simpl in *. subst key0 value.
    abbreviate_semax. Intros.
    freeze [1;2;3;5;6] FR0.
    unfold_data_at 1%nat. thaw FR0.
    freeze [7;8;9;10] OtherFields.
    rewrite (field_at_data_at _ _ [StructField _md_ctx]); simpl.
    rewrite (field_at_data_at _ _ [StructField _V]); simpl.

    freeze [0;1;2;3;4;5;8] FR1.
    assert_PROP (field_compatible t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx) as FC_ctx_MDCTX by entailer!.
    assert (FA_ctx_MDCTX: field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx = ctx).
    { unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [|contradiction].
      simpl. rewrite offset_val_force_ptr. destruct ctx; try contradiction. reflexivity.
    }
    assert_PROP (field_compatible t_struct_hmac256drbg_context_st [StructField _V] ctx) as FC_ctx_V by entailer!.
    assert (FA_ctx_V: field_address t_struct_hmac256drbg_context_st [StructField _V] ctx = offset_val 12 ctx).
    { unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [|contradiction].
      reflexivity.
    }
    thaw FR1.
    unfold hmac256drbg_relate. unfold md_full.

    (* sep[0] = sep_value; *)
    freeze [0;1;2;3;5;6;7;8] FR2.
    forward.
    thaw FR2. freeze [0;1;3;5;7;8] FR3.

    (* mbedtls_md_hmac_reset( &ctx->md_ctx ); *)
    Time forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)), key, kv). 

    (* mbedtls_md_hmac_update( &ctx->md_ctx, ctx->V, md_len ); *)
    thaw FR3. rewrite <- H4. freeze [3;4;5;6;8] FR4.
    Time forward_call (key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)),
                       field_address t_struct_hmac256drbg_context_st [StructField _V] ctx,
                       @nil Z, V, kv). 
    {
      rewrite H4.
      repeat split; [hnf;auto | hnf;auto | assumption].
    }
    Intros. 
    simpl.
    assert (Hiuchar: Int.zero_ext 8 (Int.repr i) = Int.repr i).
    {
      clear - H Heqrounds. destruct na; subst;
      apply zero_ext_inrange;
      rewrite hmac_pure_lemmas.unsigned_repr_isbyte by (hnf; omega); simpl; omega.
    }

    (* mbedtls_md_hmac_update( &ctx->md_ctx, sep, 1 ); *)
    thaw FR4. freeze [2;4;5;6;7] FR5.
    unfold upd_Znth, sublist. simpl. rewrite Hiuchar; clear Hiuchar.
    Time forward_call (key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)), sep, V, [i], kv). 
    {
      (* prove the PROP clauses *)
      rewrite H4.
      change (Zlength [i]) with 1.
      repeat split; [hnf;auto | hnf;auto | ].
      unfold general_lemmas.isbyteZ.
      repeat constructor.
      omega.
      destruct na; subst rounds; omega.
    }
    Intros. 

    (* if( rounds == 2 ) *)
     thaw FR5.
     freeze [2;4;5;6;7] FR6.

     Time forward_if (PROP  ()
      LOCAL  (temp _sep_value (Vint (Int.repr i));
      temp _rounds (Vint (Int.repr rounds));  temp _md_len (Vint (Int.repr 32));
      temp _ctx ctx; lvar _K (tarray tuchar (Zlength V)) K;
      lvar _sep (tarray tuchar 1) sep; temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
      SEP  (md_relate (UNDER_SPEC.hABS key (V ++ [i] ++ (if na then contents else nil))) (*md_ctx*)(IS1a, (IS1b, IS1c));
      (data_at Tsh t_struct_md_ctx_st (*md_ctx*)(IS1a, (IS1b, IS1c))
          (field_address t_struct_hmac256drbg_context_st
             [StructField _md_ctx] ctx));
      (spec_sha.K_vector kv);FRZL FR6;      
      (da_emp Tsh (tarray tuchar (Zlength contents))
          (map Vint (map Int.repr contents)) additional))
    ). (* 4.4 *)
    {
      (* rounds = 2 case *)
      destruct na; rewrite Heqrounds in *; [ clear H2 | solve [inv H2]]. 
      subst rounds. simpl in Heqna.
      assert (isptr additional) as Hisptr_add.
      { 
        destruct additional; simpl in PNadditional; try contradiction.
        subst i0; simpl in *; discriminate. trivial.
      }
      clear PNadditional.
      destruct additional; try contradiction. clear Hisptr_add.
      simpl in Heqna. destruct HAL; subst add_len. 2: solve [simpl in Heqna; discriminate].
      rewrite da_emp_ptr. Intros.

      (* mbedtls_md_hmac_update( &ctx->md_ctx, additional, add_len ); *)
      Time forward_call (key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                         (*md_ctx*)(IS1a, (IS1b, IS1c)), Vptr b i0, V ++ [i], contents, kv).
      {
        (* prove the PROP clause matches *)
        repeat split; [omega | omega | | assumption].
        rewrite Zlength_app; rewrite H4.
        simpl. remember (Zlength contents) as n; clear - AL1.
        destruct AL1. rewrite <- Zplus_assoc.
        unfold Int.max_unsigned in H0.
        rewrite hmac_pure_lemmas.IntModulus32 in H0; rewrite two_power_pos_equiv.
        simpl. simpl in H0.
        assert (H1: Z.pow_pos 2 61 = 2305843009213693952) by reflexivity; rewrite H1; clear H1.
        omega.
      }
      (* prove the post condition of the if statement *)
      rewrite <- app_assoc.
      rewrite H4. rewrite da_emp_ptr.
      entailer!. 
    }
    {
      (* rounds <> 2 case *)
      assert (RNDS1: rounds = 1).
      { subst rounds.
        destruct na; trivial; elim H2; trivial. }
      rewrite RNDS1 in *; clear H2 H.
      assert (NAF: na = false).
      { destruct na; try omega. trivial. }
      rewrite NAF in *. clear Heqrounds.
      forward. rewrite H4, NAF.
      destruct additional; try contradiction; simpl in PNadditional.
      + subst i0. rewrite da_emp_null; trivial. entailer!.
      + rewrite da_emp_ptr. Intros. normalize. entailer!.
    }

    (* mbedtls_md_hmac_finish( &ctx->md_ctx, K ); *)
    thaw FR6. freeze [3;4;5;6;8] FR8.  rewrite H4.
    rewrite data_at__memory_block. change (sizeof (tarray tuchar 32)) with 32.
    Intros.
    Time forward_call ((V ++ [i] ++ (if na then contents else [])), key,
                       field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)), K, Tsh, kv). 
    Intros.
    freeze [0;1;2;4] FR9.
    rewrite data_at_isptr with (p:=K). Intros.
    apply vst_lemmas.isptrD in PK; destruct PK as [sk [ik HK]]; subst K.
    thaw FR9.
    replace_SEP 1 (UNDER_SPEC.EMPTY (snd (snd (*md_ctx*)(IS1a, (IS1b, IS1c))))) by (entailer!; apply UNDER_SPEC.FULL_EMPTY).

    (* mbedtls_md_hmac_starts( &ctx->md_ctx, K, md_len ); *)
    Time forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)),
                       (Zlength (HMAC256 (V ++ [i] ++ (if na then contents else [])) key)),
                       HMAC256 (V ++ [i] ++ (if na then contents else [])) key, kv, sk, ik). 
    {
      (* prove the function parameters match up *)
      apply prop_right. 
      rewrite hmac_common_lemmas.HMAC_Zlength, FA_ctx_MDCTX; simpl.
      rewrite offset_val_force_ptr, isptr_force_ptr, sem_cast_neutral_ptr; trivial. auto.
    }
    {
      split.
      + (* prove that output of HMAC can serve as its key *)
        unfold spec_hmac.has_lengthK; simpl.
        repeat split; try reflexivity; rewrite hmac_common_lemmas.HMAC_Zlength;
        hnf; auto.
      + (* prove that the output of HMAC are bytes *)
        apply hmac_common_lemmas.isbyte_hmac.
    }
    Intros.

    thaw FR8. freeze [2;4;6;7;8] FR9.
    (* mbedtls_md_hmac_update( &ctx->md_ctx, ctx->V, md_len ); *)
    Time forward_call (HMAC256 (V ++ [i] ++ (if na then contents else [])) key,
                       field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)),
                       field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, @nil Z, V, kv). (*9 *)
    {
      (* prove the function parameters match up *)
      rewrite H4, FA_ctx_V. apply prop_right. destruct ctx; try contradiction. split; reflexivity.
    }
    {
      (* prove the PROP clauses *)
      rewrite H4.
      repeat split; [hnf;auto | hnf;auto | assumption].
    }
    Intros.
    rewrite H4.
    replace_SEP 2 (memory_block Tsh (sizeof (tarray tuchar 32)) (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)) by (entailer!; apply data_at_memory_block).
    simpl.
    (* mbedtls_md_hmac_finish( &ctx->md_ctx, ctx->V ); *)
    Time forward_call (V, HMAC256 (V ++ i::(if na then contents else [])) key,
                       field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       (*md_ctx*)(IS1a, (IS1b, IS1c)),
                       field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, Tsh, kv). 
    Time old_go_lower. (*24 secs, 1.45GB -> 1.55GB*)(*necessary due to existence of local () && in postcondition of for-rule!!!*)
    idtac "previous timing was for old_go_lower (goal: 22secs)". 
    Intros.
    Exists (HMAC256 (V ++ [i] ++ (if na then contents else [])) key).
    apply andp_right. solve [apply prop_right; subst; repeat split; auto;omega].

    Exists (HMAC256 V (HMAC256 (V ++ [i] ++ (if na then contents else [])) key)).
    Exists (HMAC256DRBGabs (HMAC256 (V ++ [i] ++ (if na then contents else [])) key)
                           (HMAC256 V (HMAC256 (V ++ [i] ++ (if na then contents else [])) key)) reseed_counter entropy_len prediction_resistance reseed_interval).
    normalize.
    apply andp_right. apply prop_right. repeat split; eauto.
      subst initial_key initial_value.
      apply HMAC_DRBG_update_round_incremental_Z; try eassumption. omega.
      apply hmac_common_lemmas.HMAC_Zlength.
    cancel.
    thaw FR9. cancel.
    unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state.
    unfold hmac256drbgstate_md_FULL.
    unfold hmac256drbg_relate.
    rewrite hmac_common_lemmas.HMAC_Zlength. rewrite hmac_common_lemmas.HMAC_Zlength.
    cancel.
    unfold md_full. entailer!.
    { apply hmac_common_lemmas.HMAC_Zlength. }
    repeat rewrite sepcon_assoc. rewrite sepcon_comm. apply sepcon_derives. 2: apply derives_refl.
    unfold_data_at 3%nat.
    thaw OtherFields. cancel.
    rewrite (field_at_data_at _ _ [StructField _md_ctx]);
    rewrite (field_at_data_at _ _ [StructField _V]).
    cancel.
  }
  Intros key value final_state_abs.
  (* return *)
  forward.
 
  (* prove function post condition *)
  Exists K sep; entailer!.
  Exists Info (hmac256drbgabs_to_state final_state_abs
     (IS1a, (IS1b, IS1c), (IS2, (IS3, (IS4, (IS5, IS6)))))). 
(*        (hmac256drbgabs_hmac_drbg_update I
            (contents_with_add additional add_len contents)).
         sep.*)
  unfold hmac256drbgabs_hmac_drbg_update.
  unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_update.
  destruct I.
  rewrite HMAC_DRBG_update_concrete_correct.
  rename H into Hupdate_rounds.
  rename H2 into Hmetadata.
  Time entailer!. (* 2 *)
  { remember (HMAC_DRBG_update_concrete HMAC256
       (contents_with_add additional add_len contents) key V ) as h; destruct h; simpl.
    apply HMAC_DRBG_update_concreteWF in Heqh.
    red in WFI; simpl in WFI. red; simpl. intuition.
  }
  unfold hmac256drbgabs_common_mpreds, hmac256drbgstate_md_info_pointer; simpl.
(*  Exists Info (hmac256drbgabs_to_state final_state_abs
     (IS1a, (IS1b, IS1c), (IS2, (IS3, (IS4, (IS5, IS6)))))). *)
  entailer!. 
  destruct final_state_abs; unfold hmac256drbgabs_metadata_same in Hmetadata. clear FR2 FR1 FR0.
  destruct Hmetadata as [Hreseed_counter [Hentropy_len [Hpr Hrseed_interval]]]; subst.
  replace (HMAC_DRBG_update_concrete HMAC256 (*contents*) (contents_with_add additional add_len contents)  key V) with (key0, V0).
  { unfold AREP, REP, hmac256drbgabs_common_mpreds. cancel. }
  simpl in Hupdate_rounds.
(*  unfold hmac256drbgabs_key, hmac256drbgabs_value in Hupdate_rounds.*)
  rewrite Hupdate_rounds in *. unfold HMAC_DRBG_update_concrete.
  clear - HAL PNadditional. unfold contents_with_add.
  destruct additional; simpl in PNadditional; try contradiction.
  - subst i ; simpl; trivial.
  - f_equal.
    destruct (Memory.EqDec_val (Vptr b i) nullval); simpl. discriminate. clear n.
    destruct (initial_world.EqDec_Z add_len 0); simpl; trivial.
    destruct HAL; try solve[omega].
    subst add_len. destruct contents; simpl; trivial. elim n.
idtac "Timing the Qed of hmacdrbg_update". apply Zlength_nil.
Time Qed. (*Coq8.6: 31secs*)

Lemma body_hmac_drbg_setEntropyLen:
      semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_set_entropy_len drbg_setEntropyLen_spec_abs.
Proof.
  start_function.
  abbreviate_semax. unfold AREP.
  rewrite extract_exists_in_SEP. Intros Info.
  unfold REP. 
  rewrite extract_exists_in_SEP. Intros a.
  destruct a as [md_ctx [V [rc [el [pr ri]]]]].
  destruct A as [K VV RC EL PR RI].
  unfold hmac256drbg_relate. normalize.
  rewrite data_at_isptr. Intros. destruct ctx; try contradiction.
  unfold_data_at 1%nat.
  freeze [0;1;2;4;5;6;7;8] FR. forward. forward.
  unfold AREP, REP. 
  Exists Info (md_ctx,
     (map Vint (map Int.repr VV),
     (Vint (Int.repr RC),
     (Vint (Int.repr l), (Val.of_bool PR, Vint (Int.repr RI)))))).
  simpl; entailer!.
  + red in H0; simpl in H0. red; simpl. intuition. 
  + unfold_data_at 1%nat; thaw FR; cancel.
Time Qed. (*1.8s*)

Lemma body_hmac_drbg_setPredictionResistance:
      semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_set_prediction_resistance drbg_setPredictionResistance_spec_abs.
Proof.
  start_function.
  abbreviate_semax. unfold AREP.
  rewrite extract_exists_in_SEP. Intros Info.
  unfold REP. 
  rewrite extract_exists_in_SEP. Intros a.
  destruct a as [md_ctx [V [rc [el [pr ri]]]]].
  destruct A as [K VV RC EL PR RI].
  unfold hmac256drbg_relate. normalize.
  rewrite data_at_isptr. Intros. destruct ctx; try contradiction.
  unfold_data_at 1%nat. 
  freeze [0;1;2;3;5;6;7;8] FR. forward. forward. 
  unfold AREP, REP. 
  Exists Info (md_ctx,
     (map Vint (map Int.repr VV),
     (Vint (Int.repr RC),
     (Vint (Int.repr EL), (Val.of_bool r, Vint (Int.repr RI)))))).
  simpl; entailer!.
  unfold_data_at 1%nat; thaw FR; cancel.
Time Qed. (*1.8s*)

Lemma body_hmac_drbg_setReseedInterval:
      semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_set_reseed_interval drbg_setReseedInterval_spec_abs.
Proof.
  start_function.
  abbreviate_semax. unfold AREP.
  rewrite extract_exists_in_SEP. Intros Info.
  unfold REP. 
  rewrite extract_exists_in_SEP. Intros a.
  destruct a as [md_ctx [V [rc [el [pr z]]]]].
  destruct A as [K VV RC EL PR RI].
  unfold hmac256drbg_relate. normalize.
  rewrite data_at_isptr. Intros. destruct ctx; try contradiction.
  unfold_data_at 1%nat.
  freeze [0;1;2;3;4;6;7;8] FR. forward. forward.
  unfold AREP, REP. 
  Exists Info (md_ctx,
     (map Vint (map Int.repr VV),
     (Vint (Int.repr RC),
     (Vint (Int.repr EL), (Val.of_bool PR, Vint (Int.repr ri)))))).
  simpl; entailer!. 
  + red; simpl. red in H0; simpl in H0. intuition.
  + unfold_data_at 1%nat; thaw FR; cancel. 
Time Qed. (*1.8s*) 
