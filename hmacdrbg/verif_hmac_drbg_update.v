Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import sha.HMAC256_functional_prog.
Require Import sha.spec_sha.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
 
Fixpoint HMAC_DRBG_update_round (HMAC: list Z -> list Z -> list Z) (provided_data K V: list Z) (round: nat): (list Z * list Z) :=
  match round with
    | O => (K, V)
    | S round' =>
      let (K, V) := HMAC_DRBG_update_round HMAC provided_data K V round' in
      let K := HMAC (V ++ [Z.of_nat round'] ++ provided_data) K in
      let V := HMAC V K in
      (K, V)
  end.

Definition HMAC_DRBG_update_concrete (HMAC: list Z -> list Z -> list Z) (provided_data K V: list Z): (list Z * list Z) :=
  let rounds := match provided_data with
                  | [] => 1%nat
                  | _ => 2%nat
                end in
  HMAC_DRBG_update_round HMAC provided_data K V rounds.

Theorem HMAC_DRBG_update_concrete_correct:
  forall HMAC provided_data K V, HMAC_DRBG_update HMAC provided_data K V = HMAC_DRBG_update_concrete HMAC provided_data K V.
Proof.
  intros.
  destruct provided_data; reflexivity.
Qed.

Definition update_rounds (non_empty_additional: bool): Z :=
  if non_empty_additional then 2 else 1.

Lemma HMAC_DRBG_update_round_incremental:
  forall key V initial_state_abs contents n,
    (key, V) = HMAC_DRBG_update_round HMAC256 contents
                           (hmac256drbgabs_key initial_state_abs)
                           (hmac256drbgabs_value initial_state_abs) n ->
    (HMAC256 (V ++ (Z.of_nat n) :: contents) key,
     HMAC256 V (HMAC256 (V ++ (Z.of_nat n) :: contents) key)) =
    HMAC_DRBG_update_round HMAC256 contents
                           (hmac256drbgabs_key initial_state_abs)
                           (hmac256drbgabs_value initial_state_abs) (n + 1).
Proof.
  intros.
  rewrite plus_comm.
  simpl.
  rewrite <- H.
  reflexivity.
Qed.

Lemma HMAC_DRBG_update_round_incremental_Z:
  forall key V initial_state_abs contents i,
    0 <= i ->
    (key, V) = HMAC_DRBG_update_round HMAC256 contents
                           (hmac256drbgabs_key initial_state_abs)
                           (hmac256drbgabs_value initial_state_abs) (Z.to_nat i) ->
    (HMAC256 (V ++ i :: contents) key,
     HMAC256 V (HMAC256 (V ++ i :: contents) key)) =
    HMAC_DRBG_update_round HMAC256 contents
                           (hmac256drbgabs_key initial_state_abs)
                           (hmac256drbgabs_value initial_state_abs) (Z.to_nat (i + 1)).
Proof.
  intros.
  specialize (HMAC_DRBG_update_round_incremental _ _ _ _ _ H0); intros. clear H0.
  rewrite (Z2Nat.id _ H) in H1. 
  rewrite Z2Nat.inj_add; try assumption; omega.
Qed.

Section DRBG_Update_Loop.
Variable Espec : OracleKind.
Variable contents : list Z.
Variable additional : val.
Variable add_len : Z.
Variable ctx : val.
Variable initial_state : hmac256drbgstate.
Variable initial_state_abs : hmac256drbgabs.
Variable kv : val.
Variable info_contents : md_info_state.
Variable sep : val.
Variable K : val.
Variable initial_value : list Z.
Variable V' : list val.
Variable reseed_counter' : val.
Variable entropy_len' : val.
Variable prediction_resistance' : val.
Variable reseed_interval' : val.
Variable md_ctx : mdstate.
Variable non_empty_additional : bool.
Variable rounds : Z.
Variable initial_key : list Z.
Variable i : Z.
Variable key : list Z.
Variable value : list Z.
Variable state_abs : hmac256drbgabs.
(*
Lemma my_entail: forall V
(H : 0 <= add_len <= Int.max_unsigned)
(Heqinitial_value : initial_value = hmac256drbgabs_value initial_state_abs)
(H0 : Zlength initial_value = 32)
(H1 : add_len = Zlength contents)
(H2 : Forall general_lemmas.isbyteZ initial_value)
(H3 : Forall general_lemmas.isbyteZ contents)
(HeqIS : (md_ctx,
        (V',
        (reseed_counter',
        (entropy_len', (prediction_resistance', reseed_interval'))))) =
        initial_state)
(Heqnon_empty_additional : non_empty_additional =
                          (if initial_world.EqDec_Z add_len 0
                           then false
                           else
                            if base.EqDec_val additional nullval
                            then false
                            else true))
(Heqrounds : rounds = (if non_empty_additional then 2 else 1))
(Heqinitial_key : initial_key = hmac256drbgabs_key initial_state_abs)
(H4 : 0 <= i < rounds)
(*(H8 : match initial_state_abs with
     | HMAC256DRBGabs _ _ reseed_counter'0 entropy_len'0
       prediction_resistance'0 reseed_interval'0 =>
         reseed_counter = reseed_counter'0 /\
         entropy_len = entropy_len'0 /\
         prediction_resistance = prediction_resistance'0 /\
         reseed_interval = reseed_interval'0
     end)*)
(isptrCtx : isptr ctx)
(FC_ctx_MDCTX : field_compatible t_struct_hmac256drbg_context_st
                 [StructField _md_ctx] ctx)
(FA_ctx_MDCTX : field_address t_struct_hmac256drbg_context_st
                 [StructField _md_ctx] ctx = ctx)
(FC_ctx_V : field_compatible t_struct_hmac256drbg_context_st [StructField _V]
             ctx)
(FA_ctx_V : field_address t_struct_hmac256drbg_context_st [StructField _V] ctx =
           offset_val 12 ctx)
(H5 : (key, V) =
     HMAC_DRBG_update_round HMAC256 contents initial_key initial_value
       (Z.to_nat i))
(H9 : Zlength V = 32)
(H10 : Forall general_lemmas.isbyteZ V)
(Hiuchar : Int.zero_ext 8 (Int.repr i) = Int.repr i)
(H6 : Forall general_lemmas.isbyteZ [i])
(isptrAdditional : isptr additional)
(b : block)
(i0 : int)
(H7 : field_compatible (tarray tuchar 32) [] (Vptr b i0))
(H11 : Forall general_lemmas.isbyteZ (HMAC256 (V ++ [i] ++ contents) key))
(HisptrK : isptr (Vptr b i0)),

ENTAIL Delta,
PROP 
(Forall general_lemmas.isbyteZ (HMAC256 V (HMAC256 (V ++ i :: contents) key)))

LOCAL  (temp _sep_value (Vint (Int.repr i));
temp _rounds (Vint (Int.repr rounds)); temp _md_len (Vint (Int.repr 32));
temp _ctx ctx; lvar _K (tarray tuchar 32) (Vptr b i0);
lvar _sep (tarray tuchar 1) sep; temp _additional additional;
temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
SEP  (K_vector kv;
UNDER_SPEC.FULL (HMAC256 (V ++ i :: contents) key) (snd (snd md_ctx));
data_at Tsh t_struct_md_ctx_st md_ctx
  (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx);
data_at Tsh
  (tarray tuchar (Zlength (HMAC256 V (HMAC256 (V ++ i :: contents) key))))
  (map Vint (map Int.repr (HMAC256 V (HMAC256 (V ++ i :: contents) key))))
  (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx);
data_at Tsh (tarray tuchar (Zlength (HMAC256 (V ++ [i] ++ contents) key)))
  (map Vint (map Int.repr (HMAC256 (V ++ [i] ++ contents) key))) (Vptr b i0);
data_at Tsh (tarray tuchar (Zlength [i])) (map Vint (map Int.repr [i])) sep;
field_at Tsh t_struct_hmac256drbg_context_st [StructField _reseed_counter]
  (fst
     (snd
        (snd
           (let (md_ctx', _) := initial_state in
            (md_ctx',
            (map Vint (map Int.repr V),
            (Vint (Int.repr reseed_counter),
            (Vint (Int.repr entropy_len),
            (Val.of_bool prediction_resistance,
            Vint (Int.repr reseed_interval)))))))))) ctx;
field_at Tsh t_struct_hmac256drbg_context_st [StructField _entropy_len]
  (fst
     (snd
        (snd
           (snd
              (let (md_ctx', _) := initial_state in
               (md_ctx',
               (map Vint (map Int.repr V),
               (Vint (Int.repr reseed_counter),
               (Vint (Int.repr entropy_len),
               (Val.of_bool prediction_resistance,
               Vint (Int.repr reseed_interval))))))))))) ctx;
field_at Tsh t_struct_hmac256drbg_context_st
  [StructField _prediction_resistance]
  (fst
     (snd
        (snd
           (snd
              (snd
                 (let (md_ctx', _) := initial_state in
                  (md_ctx',
                  (map Vint (map Int.repr V),
                  (Vint (Int.repr reseed_counter),
                  (Vint (Int.repr entropy_len),
                  (Val.of_bool prediction_resistance,
                  Vint (Int.repr reseed_interval)))))))))))) ctx;
field_at Tsh t_struct_hmac256drbg_context_st [StructField _reseed_interval]
  (snd
     (snd
        (snd
           (snd
              (snd
                 (let (md_ctx', _) := initial_state in
                  (md_ctx',
                  (map Vint (map Int.repr V),
                  (Vint (Int.repr reseed_counter),
                  (Vint (Int.repr entropy_len),
                  (Val.of_bool prediction_resistance,
                  Vint (Int.repr reseed_interval)))))))))))) ctx;
data_at Tsh t_struct_mbedtls_md_info info_contents
  (hmac256drbgstate_md_info_pointer
     (let (md_ctx', _) := initial_state in
      (md_ctx',
      (map Vint (map Int.repr V),
      (Vint (Int.repr reseed_counter),
      (Vint (Int.repr entropy_len),
      (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval))))))));
data_at Tsh (tarray tuchar (Zlength contents))
  (map Vint (map Int.repr contents)) additional; emp)
|-- (fun x : environ =>
     local (`(eq (Vint (Int.repr rounds))) (eval_id _rounds)) x &&
     (PROP  (0 <= i + 1 <= rounds)
      LOCAL  (temp _sep_value (Vint (Int.repr i));
      temp _rounds (Vint (Int.repr rounds));
      temp _md_len (Vint (Int.repr 32)); temp _ctx ctx;
      lvar _K (tarray tuchar 32) (Vptr b i0);
      lvar _sep (tarray tuchar 1) sep; temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
      SEP 
      (EX  key0 : list Z,
       (EX  value0 : list Z,
        (EX  final_state_abs : hmac256drbgabs,
         !!((key0, value0) =
            HMAC_DRBG_update_round HMAC256 contents initial_key initial_value
              (Z.to_nat (i + 1)) /\
            key0 = hmac256drbgabs_key final_state_abs /\
            value0 = hmac256drbgabs_value final_state_abs /\
            hmac256drbgabs_metadata_same final_state_abs initial_state_abs /\
            Zlength value0 = 32 /\ Forall general_lemmas.isbyteZ value0) &&
         hmac256drbgabs_common_mpreds final_state_abs initial_state ctx
           info_contents)); data_at_ Tsh (tarray tuchar 32) (Vptr b i0);
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional; data_at_ Tsh (tarray tuchar 1) sep; K_vector kv)) x).
*)

Lemma hmac_drbg_update_loop: forall
(H : 0 <= add_len <= Int.max_unsigned)
(Heqinitial_value : initial_value = hmac256drbgabs_value initial_state_abs)
(H0 : Zlength initial_value = Z.of_nat SHA256.DigestLength)
(H1 : add_len = Zlength contents)
(H2 : Forall general_lemmas.isbyteZ initial_value)
(H3 : Forall general_lemmas.isbyteZ contents)
(HeqIS : (md_ctx,
        (V',
        (reseed_counter',
        (entropy_len', (prediction_resistance', reseed_interval'))))) =
        initial_state)
(*FR0 := abbreviate : list mpred
FR1 := abbreviate : list mpred*)
(Heqnon_empty_additional : non_empty_additional =
                          (if eq_dec add_len 0
                           then false
                           else
                            if eq_dec additional nullval then false else true))
(Heqrounds : rounds = (if non_empty_additional then 2 else 1))
(Heqinitial_key : initial_key = hmac256drbgabs_key initial_state_abs)
(H4 : 0 <= i < rounds)
(H5 : (key, value) =
     HMAC_DRBG_update_round HMAC256 contents initial_key initial_value
       (Z.to_nat i))
(H6 : key = hmac256drbgabs_key state_abs)
(H7 : value = hmac256drbgabs_value state_abs)
(H8 : hmac256drbgabs_metadata_same state_abs initial_state_abs)
(H9 : Zlength value = Z.of_nat SHA256.DigestLength)
(H10 : Forall general_lemmas.isbyteZ value),
semax
  (initialized_list
     [_info; _md_len; _rounds; _sep_value; 226%positive; 225%positive;
     224%positive]
     (func_tycontext f_mbedtls_hmac_drbg_update HmacDrbgVarSpecs
        HmacDrbgFunSpecs))
  (PROP  ()
   LOCAL  (temp _sep_value (Vint (Int.repr i));
   temp _rounds (Vint (Int.repr rounds)); temp _md_len (Vint (Int.repr 32));
   temp _ctx ctx; lvar _K (tarray tuchar 32) K;
   lvar _sep (tarray tuchar 1) sep; temp _additional additional;
   temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
   SEP 
   (hmac256drbgabs_common_mpreds state_abs initial_state ctx info_contents;
   data_at_ Tsh (tarray tuchar 32) K;
   da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
     additional; data_at_ Tsh (tarray tuchar 1) sep; K_vector kv))
  (Ssequence
     (Sassign
        (Ederef
           (Ebinop Oadd (Evar _sep (tarray tuchar 1))
              (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
        (Etempvar _sep_value tint))
     (Ssequence
        (Scall None
           (Evar _mbedtls_md_hmac_reset
              (Tfunction
                 (Tcons (tptr (Tstruct _mbedtls_md_context_t noattr)) Tnil)
                 tint cc_default))
           [Eaddrof
              (Efield
                 (Ederef
                    (Etempvar _ctx
                       (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                    (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
                 (Tstruct _mbedtls_md_context_t noattr))
              (tptr (Tstruct _mbedtls_md_context_t noattr))])
        (Ssequence
           (Scall None
              (Evar _mbedtls_md_hmac_update
                 (Tfunction
                    (Tcons (tptr (Tstruct _mbedtls_md_context_t noattr))
                       (Tcons (tptr tuchar) (Tcons tuint Tnil))) tint
                    cc_default))
              [Eaddrof
                 (Efield
                    (Ederef
                       (Etempvar _ctx
                          (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                       (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
                    (Tstruct _mbedtls_md_context_t noattr))
                 (tptr (Tstruct _mbedtls_md_context_t noattr));
              Efield
                (Ederef
                   (Etempvar _ctx
                      (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                   (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
                (tarray tuchar 32); Etempvar _md_len tuint])
           (Ssequence
              (Scall None
                 (Evar _mbedtls_md_hmac_update
                    (Tfunction
                       (Tcons (tptr (Tstruct _mbedtls_md_context_t noattr))
                          (Tcons (tptr tuchar) (Tcons tuint Tnil))) tint
                       cc_default))
                 [Eaddrof
                    (Efield
                       (Ederef
                          (Etempvar _ctx
                             (tptr
                                (Tstruct _mbedtls_hmac_drbg_context noattr)))
                          (Tstruct _mbedtls_hmac_drbg_context noattr))
                       _md_ctx (Tstruct _mbedtls_md_context_t noattr))
                    (tptr (Tstruct _mbedtls_md_context_t noattr));
                 Evar _sep (tarray tuchar 1); Econst_int (Int.repr 1) tint])
              (Ssequence
                 (Sifthenelse
                    (Ebinop Oeq (Etempvar _rounds tint)
                       (Econst_int (Int.repr 2) tint) tint)
                    (Scall None
                       (Evar _mbedtls_md_hmac_update
                          (Tfunction
                             (Tcons
                                (tptr (Tstruct _mbedtls_md_context_t noattr))
                                (Tcons (tptr tuchar) (Tcons tuint Tnil)))
                             tint cc_default))
                       [Eaddrof
                          (Efield
                             (Ederef
                                (Etempvar _ctx
                                   (tptr
                                      (Tstruct _mbedtls_hmac_drbg_context
                                         noattr)))
                                (Tstruct _mbedtls_hmac_drbg_context noattr))
                             _md_ctx (Tstruct _mbedtls_md_context_t noattr))
                          (tptr (Tstruct _mbedtls_md_context_t noattr));
                       Etempvar _additional (tptr tuchar);
                       Etempvar _add_len tuint]) Sskip)
                 (Ssequence
                    (Scall None
                       (Evar _mbedtls_md_hmac_finish
                          (Tfunction
                             (Tcons
                                (tptr (Tstruct _mbedtls_md_context_t noattr))
                                (Tcons (tptr tuchar) Tnil)) tint cc_default))
                       [Eaddrof
                          (Efield
                             (Ederef
                                (Etempvar _ctx
                                   (tptr
                                      (Tstruct _mbedtls_hmac_drbg_context
                                         noattr)))
                                (Tstruct _mbedtls_hmac_drbg_context noattr))
                             _md_ctx (Tstruct _mbedtls_md_context_t noattr))
                          (tptr (Tstruct _mbedtls_md_context_t noattr));
                       Evar _K (tarray tuchar 32)])
                    (Ssequence
                       (Scall None
                          (Evar _mbedtls_md_hmac_starts
                             (Tfunction
                                (Tcons
                                   (tptr
                                      (Tstruct _mbedtls_md_context_t noattr))
                                   (Tcons (tptr tuchar) (Tcons tuint Tnil)))
                                tint cc_default))
                          [Eaddrof
                             (Efield
                                (Ederef
                                   (Etempvar _ctx
                                      (tptr
                                         (Tstruct _mbedtls_hmac_drbg_context
                                            noattr)))
                                   (Tstruct _mbedtls_hmac_drbg_context noattr))
                                _md_ctx
                                (Tstruct _mbedtls_md_context_t noattr))
                             (tptr (Tstruct _mbedtls_md_context_t noattr));
                          Evar _K (tarray tuchar 32); Etempvar _md_len tuint])
                       (Ssequence
                          (Scall None
                             (Evar _mbedtls_md_hmac_update
                                (Tfunction
                                   (Tcons
                                      (tptr
                                         (Tstruct _mbedtls_md_context_t
                                            noattr))
                                      (Tcons (tptr tuchar) (Tcons tuint Tnil)))
                                   tint cc_default))
                             [Eaddrof
                                (Efield
                                   (Ederef
                                      (Etempvar _ctx
                                         (tptr
                                            (Tstruct
                                               _mbedtls_hmac_drbg_context
                                               noattr)))
                                      (Tstruct _mbedtls_hmac_drbg_context
                                         noattr)) _md_ctx
                                   (Tstruct _mbedtls_md_context_t noattr))
                                (tptr (Tstruct _mbedtls_md_context_t noattr));
                             Efield
                               (Ederef
                                  (Etempvar _ctx
                                     (tptr
                                        (Tstruct _mbedtls_hmac_drbg_context
                                           noattr)))
                                  (Tstruct _mbedtls_hmac_drbg_context noattr))
                               _V (tarray tuchar 32); Etempvar _md_len tuint])
                          (Scall None
                             (Evar _mbedtls_md_hmac_finish
                                (Tfunction
                                   (Tcons
                                      (tptr
                                         (Tstruct _mbedtls_md_context_t
                                            noattr))
                                      (Tcons (tptr tuchar) Tnil)) tint
                                   cc_default))
                             [Eaddrof
                                (Efield
                                   (Ederef
                                      (Etempvar _ctx
                                         (tptr
                                            (Tstruct
                                               _mbedtls_hmac_drbg_context
                                               noattr)))
                                      (Tstruct _mbedtls_hmac_drbg_context
                                         noattr)) _md_ctx
                                   (Tstruct _mbedtls_md_context_t noattr))
                                (tptr (Tstruct _mbedtls_md_context_t noattr));
                             Efield
                               (Ederef
                                  (Etempvar _ctx
                                     (tptr
                                        (Tstruct _mbedtls_hmac_drbg_context
                                           noattr)))
                                  (Tstruct _mbedtls_hmac_drbg_context noattr))
                               _V (tarray tuchar 32)])))))))))
  (normal_ret_assert
     (local
        (`(eq (Vint (Int.repr rounds))) (eval_expr (Etempvar _rounds tint))) &&
      PROP  (0 <= i + 1 <= rounds)
      LOCAL  (temp _sep_value (Vint (Int.repr i));
      temp _rounds (Vint (Int.repr rounds));
      temp _md_len (Vint (Int.repr 32)); temp _ctx ctx;
      lvar _K (tarray tuchar 32) K; lvar _sep (tarray tuchar 1) sep;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
      gvar sha._K256 kv)
      SEP 
      (EX  key0 : list Z,
       (EX  value0 : list Z,
        (EX  final_state_abs : hmac256drbgabs,
         !!((key0, value0) =
            HMAC_DRBG_update_round HMAC256 contents initial_key initial_value
              (Z.to_nat (i + 1)) /\
            key0 = hmac256drbgabs_key final_state_abs /\
            value0 = hmac256drbgabs_value final_state_abs /\
            hmac256drbgabs_metadata_same final_state_abs initial_state_abs /\
            Zlength value0 = Z.of_nat SHA256.DigestLength /\
            Forall general_lemmas.isbyteZ value0) &&
         hmac256drbgabs_common_mpreds final_state_abs initial_state ctx
           info_contents)); data_at_ Tsh (tarray tuchar 32) K;
      da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional; data_at_ Tsh (tarray tuchar 1) sep; K_vector kv))).
Admitted.
(*Proof. intros. subst initial_state. simpl.
    unfold hmac256drbgabs_common_mpreds. repeat flatten_sepcon_in_SEP. 
    (*unfold hmac256drbgabs_to_state. simpl.*)
    unfold hmac256drbgabs_to_state. simpl. destruct state_abs. simpl in *. subst key0 value.
    abbreviate_semax. Intros. 
    freeze [1;2;3;5;6] FR0.
    rewrite data_at_isptr with (p:= ctx).
    rewrite da_emp_isptrornull. normalize.
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
    }(*
    assert (Hfield_md_ctx: forall ctx', isptr ctx' -> 
        field_compatible t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx' -> 
         ctx' = field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx').
    {
      intros ctx'' Hisptr Hfc.
      unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [|contradiction].
      simpl. change (Int.repr 0) with Int.zero. rewrite offset_val_force_ptr.
      destruct ctx''; inversion Hisptr. reflexivity.
    }
    assert (Hfield_V: forall ctx', isptr ctx' -> 
             field_compatible t_struct_hmac256drbg_context_st [StructField _V] ctx' ->
             offset_val 12 ctx' = field_address t_struct_hmac256drbg_context_st [StructField _V] ctx').
    {
      intros ctx'' Hisptr Hfc.
      unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [reflexivity|contradiction].
    }*)
    thaw FR1.
    destruct state_abs.
(*    destruct initial_state as [md_ctx [V' [reseed_counter' [entropy_len' [prediction_resistance' reseed_interval']]]]].*)
    (*rewrite <- HeqIS in *; simpl in *. subst key0 value.*)
    unfold hmac256drbg_relate. unfold md_full.
(*    assert (Hmdlen_V: md_len = Vint (Int.repr (Zlength V))).
    { rewrite H9; trivial. }*)

    (* sep[0] = sep_value; *)
    freeze [0;1;2;3;5;6;7;8] FR2.
    forward.
    thaw FR2. freeze [0;1;3;5;7;8] FR3.

    (* mbedtls_md_hmac_reset( &ctx->md_ctx ); *)
    Time forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, 
                       md_ctx, key, kv). (*LENB: 8secs Naphat's measure: 79 *)
    (*{
      entailer!.
    }*)
(*    Intros. v; subst v.*)

    (* mbedtls_md_hmac_update( &ctx->md_ctx, ctx->V, md_len ); *)
    thaw FR3. rewrite <- H9. freeze [3;4;5;6;8] FR4.
    Time forward_call (key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       md_ctx, field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, 
                       @nil Z, V, kv). (*LENB: 8, Naphat: 83 *)
    (*{
      entailer!.
      rewrite H9; reflexivity.
    }*)
    (*{
      rewrite H9.
      change (Z.of_nat SHA256.DigestLength) with 32.
      cancel.
    }*)
    {
      rewrite H9.
      repeat split; [hnf;auto | hnf;auto | assumption].
    }
    Intros. (*Intros v; subst v.*)
      
(*    unfold upd_Znth.
    unfold sublist. *)
    simpl. 
    assert (Hiuchar: Int.zero_ext 8 (Int.repr i) = Int.repr i).
    {
      clear - H4 Heqrounds. destruct non_empty_additional; subst;
      apply zero_ext_inrange;
      rewrite hmac_pure_lemmas.unsigned_repr_isbyte by (hnf; omega); simpl; omega.
    }
    (*rewrite Hiuchar.*)

    (* mbedtls_md_hmac_update( &ctx->md_ctx, sep, 1 ); *)
    thaw FR4. rewrite Hiuchar; clear Hiuchar. freeze [2;4;5;6;7] FR5.
    unfold upd_Znth, sublist. simpl.
    Time forward_call (key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       md_ctx, sep, V, [i], kv). (*LENB: 8, Naphat: 62 *)
    (*{
      entailer!.
    }
    { (*LENB: this SC is now now discharged manually*)
      unfold upd_Znth, sublist. simpl.  
      change (Zlength [i]) with 1. rewrite Hiuchar. cancel. 
    }*)
    {
      (* prove the PROP clauses *)
      rewrite H9.
      change (Zlength [i]) with 1.
      repeat split; [hnf;auto | hnf;auto | ].
      unfold general_lemmas.isbyteZ.
      repeat constructor.
      omega.
      destruct non_empty_additional; subst rounds; omega.
    }
    Intros. (*Intros v; subst v.*)
      
    (* if( rounds == 2 ) *)
     thaw FR5. 
     freeze [2;4;5;6;7] FR6.
     Time forward_if_tac (PROP  ()
      LOCAL  (temp _sep_value (Vint (Int.repr i));
      temp _rounds (Vint (Int.repr rounds));  temp _md_len (Vint (Int.repr 32));
      temp _ctx ctx; lvar _K (tarray tuchar (Zlength V)) K;
      lvar _sep (tarray tuchar 1) sep; temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
      SEP  (md_relate (hABS key (V ++ [i] ++ contents)) md_ctx;
      (data_at Tsh t_struct_md_ctx_st md_ctx
          (field_address t_struct_hmac256drbg_context_st
             [StructField _md_ctx] ctx));
      (*(data_at Tsh (tarray tuchar (Zlength [i])) [Vint (Int.repr i)] sep);*)
      (K_vector kv);FRZL FR6; 
      (*(data_at Tsh (tarray tuchar (Zlength V)) (map Vint (map Int.repr V))
          (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx));
      (field_at Tsh t_struct_hmac256drbg_context_st
          [StructField _reseed_counter] (Vint (Int.repr reseed_counter)) ctx);
      (field_at Tsh t_struct_hmac256drbg_context_st
          [StructField _entropy_len] (Vint (Int.repr entropy_len)) ctx);
      (field_at Tsh t_struct_hmac256drbg_context_st
          [StructField _prediction_resistance] (Val.of_bool prediction_resistance) ctx);
      (field_at Tsh t_struct_hmac256drbg_context_st
          [StructField _reseed_interval] (Vint (Int.repr reseed_interval))
          ctx);
      (data_at Tsh t_struct_mbedtls_md_info info_contents
          (hmac256drbgstate_md_info_pointer
             (md_ctx,
         (V',
         (reseed_counter',
         (entropy_len', (Val.of_bool prediction_resistance, reseed_interval')))))));
      (data_at_ Tsh (tarray tuchar (Zlength V)) K);*)
      (da_emp Tsh (tarray tuchar (Zlength contents))
          (map Vint (map Int.repr contents)) additional)) 
    ). (* 42 *)
    { 
      (* rounds = 2 case *)
      rewrite H1.
      assert (isptr additional) as Hisptr_add.
      { subst add_len. clear - H7 PNadditional Heqrounds Heqnon_empty_additional.
        subst.
        destruct (initial_world.EqDec_Z (Zlength contents) 0). discriminate .
        destruct (base.EqDec_val additional nullval). discriminate.
        destruct additional; simpl in *; try contradiction; subst. elim n0; trivial. trivial.
      }
      clear PNadditional.
      destruct additional; try contradiction. clear additional.
      rewrite da_emp_ptr. 

      (* mbedtls_md_hmac_update( &ctx->md_ctx, additional, add_len ); *)
      Time forward_call (key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                         md_ctx, Vptr b i0, V ++ [i], contents, kv). (*LENB: 8=9.5, Naophat:  63 *)
      (*{
        (* prove the parameters match up *)
        entailer!.
      }*)
      {
        (* prove the PROP clause matches *)
        rewrite H1 in *. repeat split; [omega | omega | | assumption].
        rewrite Zlength_app; rewrite H9.
        simpl. remember (Zlength contents) as n; clear - H.
        destruct H. rewrite <- Zplus_assoc.
        unfold Int.max_unsigned in H0.
        rewrite hmac_pure_lemmas.IntModulus32 in H0; rewrite two_power_pos_equiv.
        simpl. simpl in H0.
        assert (H1: Z.pow_pos 2 61 = 2305843009213693952) by reflexivity; rewrite H1; clear H1.
        omega.
      }
      (* prove the post condition of the if statement *)
      rewrite <- app_assoc.
      (*Intros v.
      rewrite H10.*) rewrite H9. rewrite da_emp_ptr.
      entailer!. (*subst add_len; trivial.*)
    }
    {
      (* rounds <> 2 case *)
      assert (RNDS1: rounds = 1).
      { subst rounds.
        destruct non_empty_additional. elim H7; trivial. trivial. }
      rewrite RNDS1 in *; clear H7 H4.
      assert (NA: non_empty_additional = false).
      { destruct non_empty_additional; try omega. trivial. }
      rewrite NA in *. clear Heqrounds.
      
      forward. (*
      assert (Add_NULL: additional = nullval).
      { assert (rounds = 1). subst add_len. clear - H7 PNadditional Heqrounds Heqnon_empty_additional.
        destruct additional; simpl in PNadditional; try contradiction.
        + subst; reflexivity.
        + subst.
          destruct (initial_world.EqDec_Z (Zlength contents) 0). discriminate .
        destruct (base.EqDec_val additional nullval). discriminate.
        destruct additional; simpl in *; try contradiction; subst. elim n0; trivial. trivial.
      }subst rounds.
      freeze [0;1;2;3;4] FR7.
      forward.*)
      rewrite H1, H9.
      entailer!.
      destruct contents.
      + simpl. (*rewrite H1.*) apply derives_refl. 
      + (* contents not empty, which is a contradiction *)
        exfalso.
        (*rewrite H1 in *;*) rewrite Zlength_cons in *.
        remember (initial_world.EqDec_Z (Z.succ (Zlength l)) 0) as d.
        destruct d as [Zlength_eq | Zlength_neq].
        - assert (0 <= Zlength l) by (apply Zlength_nonneg).
          destruct (Zlength l); [inversion Zlength_eq| omega | omega].
        - destruct (base.EqDec_val additional nullval). rewrite e in xx. contradiction.
          elim H7; trivial.
    }
    rewrite H9.

    (* mbedtls_md_hmac_finish( &ctx->md_ctx, K ); *)
    thaw FR6. freeze [3;4;5;6;8] FR8.  rewrite H9.
    rewrite data_at__memory_block. change (sizeof (*cenv_cs*) (tarray tuchar 32)) with 32.
    Intros.
    Time forward_call ((V ++ [i] ++ contents), key, 
                       field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, 
                       md_ctx, K, Tsh, kv). (*LENB: 7, Naphat 62 *)
    (*{
      (* prove the parameters match up *)
      entailer!.
    }*)
    (*Side condition now automatically discharged
    {
      change (sizeof cenv_cs (tarray tuchar (Z.of_nat SHA256.DigestLength))) with 32.
      cancel.
    }*)
    Intros.
    freeze [0;1;2;4] FR9.
    assert_PROP (isptr K) as HisptrK by entailer!. 
    destruct K; try solve [contradiction].
    thaw FR9.
    replace_SEP 1 (UNDER_SPEC.EMPTY (snd (snd md_ctx))) by (entailer!; apply UNDER_SPEC.FULL_EMPTY).

    (* mbedtls_md_hmac_starts( &ctx->md_ctx, K, md_len ); *)
    Time forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx,
                       md_ctx, (Zlength (HMAC256 (V ++ [i] ++ contents) key)),
                       HMAC256 (V ++ [i] ++ contents) key, kv, b, i0). (*14; Naphat 75 *)
    {
      (* prove the function parameters match up *)
      apply prop_right. rewrite hmac_common_lemmas.HMAC_Zlength, FA_ctx_MDCTX; simpl.
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
(*    assert_PROP (field_compatible t_struct_hmac256drbg_context_st [StructField _V] ctx) as FC_vctx_V by entailer!.*)
    (* mbedtls_md_hmac_update( &ctx->md_ctx, ctx->V, md_len ); *)
    Time forward_call (HMAC256 (V ++ [i] ++ contents) key,
                       field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx,
                       field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, @nil Z, V, kv). (*9; Naphat 72 *)
    {
      (* prove the function parameters match up *)
      rewrite H9. apply prop_right; reflexivity.
    }
    (*{
      (* prove the function SEP clauses match up *)
      rewrite H9; cancel.
    }*)
    {
      (* prove the PROP clauses *)
      rewrite H9.
      repeat split; [hnf;auto | hnf;auto | assumption].
    }
    Intros.
    rewrite H9.
(*    normalize.*)
    replace_SEP 2 (memory_block Tsh (sizeof (*cenv_cs*) (tarray tuchar 32)) (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)) by (entailer!; apply data_at_memory_block).
    simpl.
    (* mbedtls_md_hmac_finish( &ctx->md_ctx, ctx->V ); *)
    Time forward_call (V, HMAC256 (V ++ i::contents) key, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx, field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, Tsh, kv). (*9; Naphat: 75 *)
    (*{
      (* prove the function parameters match up *)
      entailer!.
    }*)
    Time old_go_lower. (*24 secs, 1.45GB -> 1.55GB*)(*necessary due to existence of local () && in postcondition of for-rule!!!*)
    Exists (HMAC256 (V ++ [i] ++ contents) key) (HMAC256 V (HMAC256 (V ++ [i] ++ contents) key)) (HMAC256DRBGabs (HMAC256 (V ++ [i] ++ contents) key) (HMAC256 V (HMAC256 (V ++ [i] ++ contents) key)) reseed_counter entropy_len prediction_resistance reseed_interval).
    Intros. apply andp_right. 
    apply prop_right. clear FR9. subst. intuition. 
      apply HMAC_DRBG_update_round_incremental_Z; assumption.
      apply hmac_common_lemmas.HMAC_Zlength.
    cancel.
    thaw FR9. cancel.
    unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state.
    unfold hmac256drbgstate_md_FULL.
    unfold hmac256drbg_relate.
    rewrite H1, hmac_common_lemmas.HMAC_Zlength. rewrite hmac_common_lemmas.HMAC_Zlength.
    cancel.
    unfold md_full. entailer!. repeat rewrite sepcon_assoc. rewrite sepcon_comm. apply sepcon_derives. 2: apply derives_refl.
    unfold_data_at 3%nat.
    thaw OtherFields. cancel.
    rewrite (field_at_data_at _ _ [StructField _md_ctx]);
    rewrite (field_at_data_at _ _ [StructField _V]). cancel.
Time Qed. (*121secs, 1.67GB -> 1.75GB*)
  *)
End DRBG_Update_Loop.

Lemma body_hmac_drbg_update: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_update hmac_drbg_update_spec.
Proof.
  start_function. 
(*  name ctx' _ctx.
  name add_len' _add_len.
  name additional' _additional.*)
  rename lvar0 into sep.
  rename lvar1 into K.
  abbreviate_semax.
  destruct initial_state as [IS1 [IS2 [IS3 [IS4 [IS5 IS6]]]]].
  rewrite da_emp_isptrornull. (*needed later*)

  (* info = md_ctx.md_info *)
  destruct IS1 as [IS1a [IS1b IS1c]]. simpl.
  rewrite data_at_isptr with (p:=ctx). 
  unfold hmac256drbgstate_md_info_pointer. simpl.
  rewrite data_at_isptr with (p:=IS1a). 
  normalize.
  freeze [0;1;2;4;6] FR0. 
  freeze [0;2] FR1.

  Time forward. (*8.5pl2: 3secs. BUT without doing the 2 lines
     unfold hmac256drbgstate_md_info_pointer. simpl.
     rewrite data_at_isptr with (p:=IS1a),
     this
     entailer takes 1230secs.
     And when we leave the IS1a-data-at unfrozen (eg omit the construction of FR1), it also takes significantly more than 3 secs*)
  thaw FR1.

  (* md_len = mbedtls_md_get_size( info ); *)
  freeze [0;1] FR1.
  forward_call tt.

  (*Intros md_len. LENB: replaced by the following*)
  change (Z.of_nat SHA256.DigestLength) with 32.
(*  remember (Vint (Int.repr (Z.of_nat SHA256.DigestLength))) as md_len.*)

  (* rounds = ( additional != NULL && add_len != 0 ) ? 2 : 1; *)
(*  remember (if eq_dec add_len 0 then false else if eq_dec additional nullval then false else true) as non_empty_additional.*)
  remember (andb (negb (eq_dec additional nullval)) (negb (eq_dec add_len 0))) as na.
  freeze [0;1] FR2.
  forward_if (
      PROP  ()
      LOCAL  (temp _md_len (Vint (Int.repr 32)); lvar _K (tarray tuchar 32) K;
      temp _ctx ctx;
      lvar _sep (tarray tuchar 1) sep;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
      temp 225%positive (Val.of_bool na);
(*      temp 225%positive (Val.of_bool non_empty_additional);*)
      gvar sha._K256 kv)
      SEP  (FRZL (FR2))). 
  {
    (* show that add_len <> 0 implies the post condition *)
    forward.
    { entailer. destruct additional; try contradiction; simpl in PNadditional.
      subst i; simpl. entailer!. (* simpl. *)
      thaw FR2. thaw FR1. thaw FR0. normalize.
      rewrite da_emp_ptr.
      apply denote_tc_comparable_split; auto 50 with valid_pointer.
      (* TODO regression, this should have solved it *) 
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer2.
      apply data_at_valid_ptr; auto.

      simpl. clear - H4 H. rewrite Zmax_right; omega.
    } 

    { entailer!.
      destruct additional; simpl in PNadditional; try contradiction.
      subst i; simpl; trivial.
      simpl. destruct (initial_world.EqDec_Z (Zlength contents) 0); trivial; omega.
    }
  } 
  

  {
    (* show that add_len = 0 implies the post condition *)
    forward. 
    entailer!. rewrite H4. simpl. rewrite andb_false_r. reflexivity. 
  }

  remember (update_rounds na) as rounds. unfold update_rounds in Heqrounds.
  forward_if ( PROP  ()
      LOCAL  (temp _md_len (Vint (Int.repr 32)); lvar _K (tarray tuchar 32) K;
      temp _ctx ctx;
      lvar _sep (tarray tuchar 1) sep;
      temp _additional additional; temp _add_len (Vint (Int.repr add_len));
(*      temp 141%positive (Vint (Int.repr rounds));*)
      temp 226%positive (Vint (Int.repr rounds));
      gvar sha._K256 kv
             )
      SEP  (FRZL FR2) 
  ).
  {
    (* non_empty_additional = true *)
    forward. rewrite H4 in *; clear H4.
    entailer!.
  }
  {
    (* non_empty_additional = false *)
    forward. rewrite H4 in *; clear H4.
    entailer!.
  }

  forward.
  drop_LOCAL 7%nat.
  remember (hmac256drbgabs_key initial_state_abs) as initial_key.
  remember (hmac256drbgabs_value initial_state_abs) as initial_value.

  (* verif_sha_final2.v, @exp (environ -> mpred) *)
  (* for ( sep_value = 0; sep_value < rounds; sep_value++ ) *)
  Time forward_for_simple_bound rounds (
                              EX i: Z,
      PROP  (
      (* (key, value) = HMAC_DRBG_update_round HMAC256 (map Int.signed contents) old_key old_value 0 (Z.to_nat i);
      (*
      le i (update_rounds non_empty_additional);
       *)
      key = hmac256drbgabs_key final_state_abs;
      value = hmac256drbgabs_value final_state_abs;
      hmac256drbgabs_metadata_same final_state_abs state_abs *)
        ) 
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
              (key, value) = HMAC_DRBG_update_round HMAC256 contents initial_key initial_value (Z.to_nat i)
              /\ key = hmac256drbgabs_key final_state_abs
              /\ value = hmac256drbgabs_value final_state_abs
              /\ hmac256drbgabs_metadata_same final_state_abs initial_state_abs
              /\ Zlength value = Z.of_nat SHA256.DigestLength
              /\ Forall general_lemmas.isbyteZ value
            ) &&
           (hmac256drbgabs_common_mpreds final_state_abs 
             (*initial_state*) ((IS1a,(IS1b,IS1c)),(IS2,(IS3,(IS4,(IS5,IS6)))))
              ctx info_contents)
         );
        (* `(update_relate_final_state ctx final_state_abs); *)
        (data_at_ Tsh (tarray tuchar 32) K);
        (da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional);
        (data_at_ Tsh (tarray tuchar 1) sep );
        (K_vector kv)
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
    Exists (hmac256drbgabs_key initial_state_abs) (hmac256drbgabs_value initial_state_abs) initial_state_abs.
    destruct initial_state_abs. simpl. Time entailer!.
    thaw FR2. thaw FR1. thaw FR0. cancel.
    unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state. cancel.
    unfold hmac256drbg_relate. entailer!. 
  }
  {
    (* loop body *)
(*    change (`(eq (Vint (Int.repr rounds))) (eval_expr (Etempvar _rounds tint))) with (temp _rounds (Vint (Int.repr rounds))).*)
    Intros key value state_abs. 
    eapply hmac_drbg_update_loop; try eassumption. reflexivity.
    rewrite Heqna. clear - PNadditional.
    destruct additional; simpl in PNadditional; try contradiction.
    subst; simpl. destruct (initial_world.EqDec_Z add_len 0); trivial.
    simpl. destruct (initial_world.EqDec_Z add_len 0); trivial.
  }

  Intros key value final_state_abs.
  (* return *)
  forward.

  (* prove function post condition *)
  Exists K sep.
  unfold hmac256drbgabs_hmac_drbg_update.
  unfold HMAC256_DRBG_functional_prog.HMAC256_DRBG_update.
  destruct initial_state_abs.
  rewrite HMAC_DRBG_update_concrete_correct.
  Time entailer!. (* 29 *)

  rename H4 into Hupdate_rounds.
  rename H7 into Hmetadata.
  destruct final_state_abs; unfold hmac256drbgabs_metadata_same in Hmetadata. clear FR2 FR1 FR0.
  destruct Hmetadata as [Hreseed_counter [Hentropy_len [Hpr Hrseed_interval]]]; subst.
  replace (HMAC_DRBG_update_concrete HMAC256 contents key V) with (key0, V0). apply derives_refl.
(*  cancel.*)
  unfold hmac256drbgabs_key, hmac256drbgabs_value in Hupdate_rounds. 
  rewrite Hupdate_rounds in *. unfold HMAC_DRBG_update_concrete.
  f_equal. destruct additional; simpl in PNadditional; try contradiction.
  + subst i; simpl.   
    destruct contents; try reflexivity.
    destruct (initial_world.EqDec_Z (Zlength (z :: contents)) 0); simpl; trivial.
    apply Zlength_nil_inv in e; discriminate.
  }
  simpl.
  destruct contents.
  {
    reflexivity.
  }
  { destruct (initial_world.EqDec_Z (Zlength (z :: contents)) 0); simpl; trivial.
    apply Zlength_nil_inv in e; discriminate.
  }
SearchAbout Zlength 0.
     rewrite Zlength_ in e. xomega.
    destruct (eq_dec (Zlength (z :: contents)) 0) as [Zlength_eq | Zlength_neq].
    rewrite Zlength_cons, Zlength_correct. simpl. in Zlength_eq; omega.
    destruct (eq_dec additional nullval) as [additional_eq | additional_neq].
    subst. repeat rewrite Zlength_map in H11; inversion H11 as [isptr_null H']; inversion isptr_null.
    reflexivity.
  } reflexivity.
  replace (Z.to_nat
        (if if eq_dec (Zlength contents) 0
            then false
            else if eq_dec additional nullval then false else true
         then 2
         else 1)) with (match contents with | [] => 1%nat | _ => 2%nat end).
  reflexivity.
  destruct contents.
  {
    reflexivity.
  }
  {
    destruct (eq_dec (Zlength (z :: contents)) 0) as [Zlength_eq | Zlength_neq].
    rewrite Zlength_cons, Zlength_correct in Zlength_eq; omega.
    destruct (eq_dec additional nullval) as [additional_eq | additional_neq].
    subst. repeat rewrite Zlength_map in H11; inversion H11 as [isptr_null H']; inversion isptr_null.
    reflexivity.
  }
Time Qed. (*48secs*)



  rename H1 into Hupdate_rounds.
  rename H7 into Hmetadata.
  destruct final_state_abs; unfold hmac256drbgabs_metadata_same in Hmetadata. clear FR1.
  destruct Hmetadata as [Hreseed_counter [Hentropy_len [Hpr Hrseed_interval]]]; subst.
  replace (HMAC_DRBG_update_concrete HMAC256 contents key V) with (key0, V0).
  cancel.
  unfold hmac256drbgabs_key, hmac256drbgabs_value in H4 (*Hupdate_rounds*).
  rewrite H4 (*Hupdate_rounds*). unfold HMAC_DRBG_update_concrete.
  replace (Z.to_nat
        (if if eq_dec (Zlength contents) 0
            then false
            else if eq_dec additional nullval then false else true
         then 2
         else 1)) with (match contents with | [] => 1%nat | _ => 2%nat end).
  reflexivity.
  destruct contents.
  {
    reflexivity.
  }
  {
    destruct (eq_dec (Zlength (z :: contents)) 0) as [Zlength_eq | Zlength_neq].
    rewrite Zlength_cons, Zlength_correct in Zlength_eq; omega.
    destruct (eq_dec additional nullval) as [additional_eq | additional_neq].
    subst. repeat rewrite Zlength_map in H11; inversion H11 as [isptr_null H']; inversion isptr_null.
    reflexivity.
  }
Time Qed. (*48secs*)