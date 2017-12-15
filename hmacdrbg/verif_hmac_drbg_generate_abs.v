Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import VST.floyd.sublist.

Require Import sha.HMAC256_functional_prog.
Require Import sha.general_lemmas.
Require Import sha.spec_sha.

Require Import hmacdrbg.entropy.
Require Import hmacdrbg.entropy_lemmas.
Require Import hmacdrbg.HMAC256_DRBG_functional_prog.
Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.HMAC_DRBG_pure_lemmas.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import hmacdrbg.drbg_protocol_specs.
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
Require Import hmacdrbg.verif_hmac_drbg_generate_common.

Opaque HMAC256.
Opaque hmac256drbgabs_generate.
Opaque HMAC256_DRBG_generate_function.
Opaque mbedtls_HMAC256_DRBG_generate_function.
Definition POSTRESEED (IS:reptype t_struct_hmac256drbg_context_st)
   (b:bool) (s:ENTROPY.stream) (mc:mdstate) (K V:list Z) (RC EL:Z) (PR:bool) (RI:Z) (c:list Z)
   (s':ENTROPY.stream) (K':list Z) (ctx':reptype t_struct_hmac256drbg_context_st):Prop :=
if b then 
  exists VV KK aa zz cc ss, 
    mbedtls_HMAC256_DRBG_reseed_function s
         (HMAC256DRBGabs K V RC EL PR RI) c
    = ENTROPY.success (VV, KK, aa, zz, cc) ss 
    /\ s' = ss /\ K'=KK /\
       ctx' = (mc,
            (map Vint (map Int.repr VV),
            (Vint (Int.repr aa),
            (Vint (Int.repr EL),
            (Val.of_bool cc, Vint (Int.repr RI))))))
else s'=s /\ K'=K /\ ctx'=IS.

Definition POSTUPDATE (b:bool) additional c key V (mc:mdstate) RC EL PR RI ctx1 key1 K' (ctx':reptype t_struct_hmac256drbg_context_st): Prop :=
  if b 
  then (exists (bb : block), exists (ii : int), exists (UVal : list Z),
        additional = Vptr bb ii /\
        (K', UVal) =
           HMAC256_DRBG_update
             (contents_with_add (Vptr bb ii) (Zlength c) c) key V /\
        ctx' = (mc,
         (map Vint (map Int.repr UVal),
         (Vint (Int.repr RC),
         (Vint (Int.repr EL),
         (Val.of_bool PR, Vint (Int.repr RI)))))))
  else (ctx' = ctx1 /\ K'=key1). 

Opaque mbedtls_HMAC256_DRBG_reseed_function.

Lemma body_hmac_drbg_generate_abs: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_random_with_add hmac_drbg_generate_abs_spec.
Proof.
  start_function. 
  unfold AREP. focus_SEP 2. rewrite extract_exists_in_SEP. Intros Info.
  unfold REP. rewrite extract_exists_in_SEP. Intros a.
  rename H4 into WFI.  
  assert (Hreseed_counter_in_range: 0 <= hmac256drbgabs_reseed_counter I < Int.max_signed) by apply WFI.
  assert (Hreseed_interval: RI_range (hmac256drbgabs_reseed_interval I)) by apply WFI.
  assert (isbtV: Forall isbyteZ (hmac256drbgabs_value I)) by apply WFI.
  rename H1 into AddLenC. rename H2 into Hentlen. rename H3 into isbtContents.
  rename H into Haddlen. rename H0 into Houtlen.
  destruct I. 
  destruct a as [md_ctx' [V' [reseed_counter' [entropy_len' [prediction_resistance' reseed_interval']]]]].
  unfold hmac256drbg_relate.
  normalize.
  unfold hmac256drbgstate_md_info_pointer.
  simpl. rewrite da_emp_isptrornull.
  rename H into ZlengthV.

  rewrite da_emp_isptrornull. (*needed later*)
  rewrite data_at_isptr with (p:=ctx).
  normalize. 
  set (I := HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval) in *.
  set (a := (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval))))))) in *.

  (* mbedtls_hmac_drbg_context *ctx = p_rng; *)
  forward. 

  (* int left = out_len *)
  forward.

  (* out = output *)
  forward.

  (* prediction_resistance = ctx->prediction_resistance *)
  destruct ctx; try contradiction.  (*subst initial_state.*)
  destruct md_ctx' as [mc1 [mc2 mc3]]. simpl.
  rewrite data_at_isptr with (p:=mc1). normalize.
  freeze [1;2;3;4;5;6] FR0. 
  Time forward. (*Coq8.5pl2:3secs - and without the freezer it is virtually nonterminating*)
  {
    (* typechecking *)
    entailer!.
    destruct prediction_resistance; constructor.
  }

  (* reseed_counter = ctx->reseed_counter *)
  forward.

  (* reseed_interval = ctx->reseed_interval *)
  forward.

  (* info = ctx->md_ctx.md_info; *)
  forward.

  (* md_len = mbedtls_md_get_size(info); *)
  forward_call tt.

  (* if( out_len > MBEDTLS_HMAC_DRBG_MAX_REQUEST ) *)
  forward_if (
      PROP  (out_len <= 1024)
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr 32)); temp _info (*(let (x, _) := md_ctx' in x)*)mc1;
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx (*ctx*)(Vptr b i); temp _p_rng (*ctx*)(Vptr b i); temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
      SEP  (data_at_ Tsh (tarray tuchar out_len) output;
      da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
      data_at Tsh t_struct_hmac256drbg_context_st (*initial_state*)(mc1, (mc2, mc3),
     (map Vint (map Int.repr V),
     (Vint (Int.repr reseed_counter),
     (Vint (Int.repr entropy_len),
     (Val.of_bool prediction_resistance,
     Vint (Int.repr reseed_interval))))))  (*ctx*)(Vptr b i);
      md_full key (*md_ctx'*)(mc1, (mc2, mc3));
      data_at Tsh t_struct_mbedtls_md_info Info (*(fst md_ctx')*) mc1;
      Stream s; K_vector kv)
    ).
  {
    (* return( MBEDTLS_ERR_HMAC_DRBG_REQUEST_TOO_BIG ); *)
    forward.

    (* prove post condition of the function *)
    Exists (Vint (Int.repr (-3))). entailer!.
    assert (Hout_len: out_len >? 1024 = true).
    {
      rewrite Z.gtb_ltb.
      apply Z.ltb_lt.
      assumption.
    }
    unfold generate_absPOST. rewrite Hout_len; simpl. entailer!.
    thaw FR0. cancel. unfold AREP, REP.
    Exists Info. Exists a. entailer!.
    unfold hmac256drbg_relate. subst I; simpl in *.
    entailer!.
  }
  {
    forward.
    entailer!. thaw FR0. cancel.
  }

  Intros. clear Pctx FR0.
  assert (Hout_len: 0 <= out_len <= 1024) by omega.
  assert (Hout_lenb: out_len >? 1024 = false).
  {
    rewrite Z.gtb_ltb.
    apply Z.ltb_nlt.
    omega.
  }
  clear H.

  freeze [0;1;2;3;4;5;6] FR2.

  (* III. if( add_len > MBEDTLS_HMAC_DRBG_MAX_INPUT ) *)
  forward_if (
      PROP  (add_len <= 256) (* ADDED *)
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr 32));
              temp _info mc1 (*(let (x, _) := md_ctx' in x)*);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx (*ctx*)(Vptr b i); temp _p_rng (*ctx*)(Vptr b i); temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
      SEP  (FRZL FR2)). 
  {
    (* return( MBEDTLS_ERR_HMAC_DRBG_INPUT_TOO_BIG ); *)
    forward.

    (* prove function post condition *)
    Exists (Vint (Int.repr (-5))). entailer!.
    assert (Hadd_lenb: Zlength contents >? 256 = true).
    {
      rewrite Z.gtb_ltb.
      apply Z.ltb_lt.
      assumption.
    }
    unfold generate_absPOST. rewrite Hout_lenb, Hadd_lenb; simpl.
    entailer!. 
    thaw FR2. cancel. unfold AREP, REP. Exists Info. Exists a.
    entailer!. unfold hmac256drbg_relate; subst I a; simpl in *; entailer!.
  }
  { 
    (*"empty" branch of III: skip*)
    forward.
    entailer!.
  }
  Intros. 
  assert (Hadd_len: 0 <= add_len <= 256) by omega.
  assert (Hadd_lenb: add_len >? 256 = false).
  {
    rewrite Z.gtb_ltb.
    apply Z.ltb_nlt.
    omega.
  }
  (*  subst add_len. *) clear H.
  unfold POSTCONDITION, abbreviate, generate_absPOST. rewrite Hout_lenb, Hadd_lenb. abbreviate_semax.
  assert (ZLa: Zlength (contents_with_add additional add_len contents) >? 256 = false).
     { unfold contents_with_add. if_tac. subst; trivial. rewrite Zlength_nil; trivial. }

  (*1. (aka VII and IX) Check reseed counter and PR*)
  set (should_reseed := orb prediction_resistance (reseed_counter >? reseed_interval)) in *.
  forward_if (
      PROP  ()
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr 32)); temp _info mc1(*(let (x, _) := md_ctx' in x)*);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx (*ctx*)(Vptr b i); temp _p_rng (*ctx*)(Vptr b i); temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv;
      temp _t'4 (Val.of_bool should_reseed) (* ADDED *)
      )
      SEP (FRZL FR2)). 
  {
    forward.
    entailer!.

    rename H into Hpr.
    destruct prediction_resistance; simpl. 
    (* true *) reflexivity.
    (* false *) inversion Hpr.
  }
  {
    rename H into Hpr.
    destruct prediction_resistance; try solve [inversion Hpr].
    simpl in should_reseed; clear Hpr. 
    forward.
    entailer!.
    
    subst should_reseed; rewrite Z.gtb_ltb.
    unfold Int.lt. 
    unfold hmac256drbgabs_reseed_counter in Hreseed_counter_in_range.
    destruct Hreseed_interval as [AA BB]. simpl in *. (*red in AA. *)
    remember (reseed_interval <? reseed_counter) as r; simpl. destruct r. 
    {
      (* reseed_interval < reseed_counter *)
      symmetry in Heqr; apply Zlt_is_lt_bool in Heqr. unfold Int.lt.
      rewrite zlt_true; [reflexivity | ].
      rewrite !Int.signed_repr; change Int.min_signed with (-2147483648); change Int.max_signed with (2147483647) in *; try omega.
    }
    { (*subst initial_state_abs.
      assert (Hltb: 10000 <? reseed_counter = false) by (rewrite Z.ltb_nlt; assumption).
      rewrite Hltb.*)
      symmetry in Heqr; apply Z.ltb_ge in Heqr. unfold Int.lt.
      rewrite zlt_false; [reflexivity | ].
      rewrite !Int.signed_repr; change Int.min_signed with (-2147483648); change Int.max_signed with (2147483647) in *; try omega.
    }
  }
(*  exfalso. apply myAx. Time Qed. 12s*)
  set (after_reseed_add_len := if should_reseed then 0 else add_len) in *.
  rename a into aaa.
(*  assert (HIS: exists IS: reptype t_struct_hmac256drbg_context_st, IS = a). 
  { exists a; trivial. }
  destruct HIS as [IS HIS].*)

  set (contents' := contents_with_add additional add_len contents) in *.
  assert (C' : contents' = nil \/ contents' = contents).
  { subst contents'; unfold contents_with_add. if_tac. right; trivial. left; trivial. }
  assert (ZLc' : Zlength contents' = 0 \/ Zlength contents' = Zlength contents).
  { destruct C' as [C' | C']; rewrite C'. left; trivial. right; trivial. }

  forward_if (
   PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance); 
   temp _out output; temp _left (Vint (Int.repr out_len)); temp _ctx (Vptr b i);
   temp _p_rng (Vptr b i); temp _output output; temp _out_len (Vint (Int.repr out_len));
   temp _additional additional; temp _add_len (Vint (Int.repr after_reseed_add_len));
   gvar sha._K256 kv; temp _t'4 (Val.of_bool should_reseed))
   SEP (EX stream1 :ENTROPY.stream, EX key1:list Z, EX ctx1: reptype t_struct_hmac256drbg_context_st,
        (!! POSTRESEED aaa should_reseed s (mc1, (mc2,mc3)) key V reseed_counter entropy_len
            prediction_resistance reseed_interval
            (contents_with_add additional (Zlength contents) contents)
            stream1 key1 ctx1)
         &&
       (data_at Tsh t_struct_hmac256drbg_context_st ctx1 (Vptr b i) *
        data_at_ Tsh (tarray tuchar out_len) output *
        da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
        data_at Tsh t_struct_mbedtls_md_info Info mc1 * K_vector kv *
        md_full key1 (mc1, (mc2, mc3)) *
        Stream stream1))).

  { (*Case should_reseed = true*)
    assert (Hshould_reseed: should_reseed = true) by apply H; clear H.
    unfold POSTCONDITION, abbreviate. rewrite Hshould_reseed in *. clear POSTCONDITION. thaw FR2. 
    abbreviate_semax.

    forward_call (contents, additional, add_len, (*ctx*)Vptr b i, aaa, I, kv, Info, s).
    { subst I aaa; cancel.
      unfold hmac256drbg_relate. simpl in *. entailer!.
    } 
    { red in WFI; simpl in *. repeat split; trivial; try omega.
      change Int.modulus with 4294967296. omega. 
      subst contents'. destruct ZLc' as [ZLc' | ZLc']; rewrite ZLc'; omega. 
      subst contents'. destruct ZLc' as [ZLc' | ZLc']; rewrite ZLc' in *.
      change Int.modulus with 4294967296; omega. 
      change Int.modulus with 4294967296; omega. 
    }
     
    Intros return_value.
    forward. 

    assert (F: 0>? 256 = false) by reflexivity.

    forward_if (PROP  (return_value = Vzero) (* ADDED *)
      LOCAL  (temp _ret return_value; 
      temp _md_len (Vint (Int.repr 32)); temp _info (*(let (x, _) := md_ctx' in x)*)mc1;
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx (*ctx*)(Vptr b i); temp _p_rng (*ctx*)(Vptr b i); temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv; 
      temp _t'4 (Val.of_bool true))
      SEP (reseedPOST return_value contents additional add_len s I 
                (Vptr b i) Info kv aaa;
          data_at_ Tsh (tarray tuchar out_len) output)).
    {
      (* reseed's return_value != 0 *) 
      rename H into Hrv.
      forward. simpl in *.
(*      clear - Hadd_lenb Hadd_len Hrv H3 Hout_lenb ZLa F H4 Hshould_reseed.*)
      Exists (Vint return_value).
      apply andp_right. apply prop_right; auto.
      apply andp_right. auto.
      normalize.
      apply entailment1; trivial. }

     { (* reseed's return_value = 0 *)
       rename H into Hrv.
       forward. entailer!. unfold Vzero. f_equal. 
       apply negb_false_iff in Hrv. apply int_eq_e in Hrv. trivial.
     }
 
     forward. subst I after_reseed_add_len. rewrite Hshould_reseed in *. clear Hshould_reseed should_reseed.
     entailer!. simpl in *. (*
     Exists  ss KK (mc1, (mc2, mc3),
            (map Vint (map Int.repr VV),
            (Vint (Int.repr aa),
            (Vint (Int.repr entropy_len),
            (Val.of_bool cc, Vint (Int.repr reseed_interval)))))).*)
     unfold reseedPOST; simpl.
     remember ((zlt 256 (Zlength contents)
       || zlt 384 (entropy_len + Zlength contents))%bool) as d.
     destruct (zlt 256 (Zlength contents)); simpl in Heqd; [ omega |].
     destruct (zlt 384 (entropy_len + Zlength contents)); simpl in Heqd; subst d; [ simpl in *; omega |].
     Intros. (* cancel.*)
     unfold return_value_relate_result in H2.
     remember (mbedtls_HMAC256_DRBG_reseed_function s
         (HMAC256DRBGabs key V reseed_counter entropy_len
            prediction_resistance reseed_interval)
         (contents_with_add additional (Zlength contents) contents)) as Reseed.
(*     remember ((hmac256drbgabs_reseed I s
        (contents_with_add additional (Zlength contents) contents))).
     unfold hmac256drbgabs_reseed in Heqh. rewrite <- HeqReseed in Heqh.*)
     destruct Reseed.
     + destruct d as [[[[RSVal RSKey] aa] bb] cc]. (* destruct I; simpl in *. 
       unfold (*hmac256drbgabs_reseed, *)postReseedCtx, postReseedKey, postReseedStream.
       subst I; rewrite <- HeqReseed. simpl. simpl in Heqh. subst h. *)
       Exists s0 RSKey (mc1, (mc2, mc3),
         (map Vint (map Int.repr RSVal),
         (Vint (Int.repr aa),
         (Vint (Int.repr entropy_len), (Val.of_bool cc, Vint (Int.repr reseed_interval)))))).
       unfold hmac256drbgabs_common_mpreds.
       simpl; normalize.
       apply andp_right; [ apply prop_right | cancel].
       exists RSVal, RSKey, aa, bb, cc, s0. repeat split; trivial. 
     + destruct e; [ discriminate |]. 
       destruct ENT_GenErrAx as [X _]. elim X; trivial.
  }
  { (*Case should_reseed = false*)
    forward. subst after_reseed_add_len. rewrite H (*, Haaa*) in *. clear H (*Haaa*).
    Exists s key aaa. entailer!. thaw FR2; cancel.
  }
  clear FR2. Intros stream1 key1 ctx1. rename H into PRS. 

(*  exfalso. apply myAx. Time Qed. 42s*)
(*  assert (HIC: exists IC: reptype t_struct_mbedtls_md_info, IC = Info).
  { exists Info; trivial. }
  destruct HIC as [IC HIC]. *)

  freeze [1;3;6] FR3.
  freeze [0;1;3;4] FR4.

  set (na:=(negb (eq_dec additional nullval) && negb (eq_dec ((if should_reseed then 0 else Zlength contents)) 0))%bool) in *.
 
  forward_if
  (PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance); 
   temp _out output; temp _left (Vint (Int.repr out_len)); 
   temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvar sha._K256 kv;
   temp _t'4 (Val.of_bool should_reseed);
   temp _t'5 (Val.of_bool na))
   SEP (FRZL FR4;
        da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional)).
  { destruct additional; simpl in PNadditional; try contradiction.
    + subst i0; entailer.
    + rewrite da_emp_ptr. normalize.
      apply denote_tc_test_eq_split.
      apply sepcon_valid_pointer2. 
      apply data_at_valid_ptr; trivial. apply top_share_nonidentity.
      auto 50 with valid_pointer.
  }
  { forward. entailer!. subst after_reseed_add_len na.
    destruct should_reseed; simpl; trivial. rewrite andb_false_r. reflexivity.
    destruct (initial_world.EqDec_Z (Zlength contents)  0); simpl. 
    + rewrite e. simpl. rewrite andb_false_r. reflexivity.
    + rewrite Int.eq_false; simpl. 
      destruct (Memory.EqDec_val additional nullval); try reflexivity. contradiction. 
      intros N. assert (U: Int.unsigned (Int.repr (Zlength contents)) = Int.unsigned (Int.repr 0)). rewrite N; trivial. clear N.
      rewrite Int.unsigned_repr in U; trivial. rewrite U in n. elim n; trivial. 
  }
  { forward. rewrite H in *. entailer!. }

  thaw FR4.
  forward_if (EX ctx2:reptype t_struct_hmac256drbg_context_st, EX key2:list Z, 
  (PROP (POSTUPDATE na additional contents key V (mc1,(mc2,mc3)) reseed_counter entropy_len prediction_resistance reseed_interval ctx1 key1 key2 ctx2)
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance);
   temp _out output; temp _left (Vint (Int.repr out_len)); 
   temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); 
   gvar sha._K256 kv; temp _t'4 (Val.of_bool should_reseed);
   temp _t'5 (Val.of_bool na))
   SEP (FRZL FR3; K_vector kv;
   da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
    data_at Tsh t_struct_hmac256drbg_context_st ctx2 (Vptr b i) *
    md_full key2 (mc1, (mc2, mc3))))).
   { rewrite H in *. subst na.
     destruct should_reseed; simpl in *. rewrite andb_false_r in H; discriminate.
     destruct (initial_world.EqDec_Z (Zlength contents) 0); simpl in H.
     { rewrite andb_false_r in H; discriminate. }
     rewrite andb_true_r in H.
     destruct additional; simpl in PNadditional; try contradiction.
     { subst i0; discriminate. }
     destruct PRS as [? [? ?]]; subst key1 stream1 ctx1. clear H. 
     
       forward_call (contents, Vptr b0 i0, after_reseed_add_len, 
                    (*ctx*)Vptr b i,aaa,I, kv, Info
                 ).
       { assert (FR: Frame = [data_at_ Tsh (tarray tuchar out_len) output * Stream s]).
         { subst Frame; reflexivity. }
         subst Frame.
         subst after_reseed_add_len add_len aaa. cancel.
         thaw FR3. (*subst (*aaa*) IC.*)
         unfold hmac256drbg_relate, hmac256drbgstate_md_info_pointer; simpl. cancel. entailer!. 
       }
       { (*subst na.*)subst after_reseed_add_len.  entailer. unfold hmac256drbgabs_common_mpreds.
         remember ( HMAC256_DRBG_update
             (contents_with_add (Vptr b0 i0) (Zlength contents) contents) key
             V) as UPD. destruct UPD as [KK VV]. simpl. 
         Exists (mc1, (mc2, mc3),
            (map Vint (map Int.repr VV),
            (Vint (Int.repr reseed_counter),
            (Vint (Int.repr entropy_len),
            (Val.of_bool prediction_resistance,
            Vint (Int.repr reseed_interval)))))) KK.
         normalize.  
         apply andp_right; [ apply prop_right | thaw FR3; cancel].
         split; [| repeat split; trivial].
         exists b0, i0, VV. repeat split; trivial. }  
     }
     { clear - H. forward. rewrite H in *. 
       Exists ctx1 key1. entailer!. }
  Intros ctx2 key2. rename H into PUPD.

(*exfalso. apply myAx. Time Qed. 54s*)

set (after_reseed_state_abs := if should_reseed
          then hmac256drbgabs_reseed I s (contents_with_add additional add_len contents)
          else I) in *.

assert (ZLength_ARSA_val: Zlength (hmac256drbgabs_value after_reseed_state_abs) = 32).
{ subst after_reseed_state_abs add_len.
  destruct should_reseed; trivial. 
  apply Zlength_hmac256drbgabs_reseed_value; trivial. }

assert (isbyte_ARSA_val: Forall isbyteZ (hmac256drbgabs_value after_reseed_state_abs)).
{ subst after_reseed_state_abs add_len.
  destruct should_reseed; trivial.
  apply isbyteZ_hmac256drbgabs_reseed_value; trivial. }

set (after_update_state_abs := (if na then hmac256drbgabs_hmac_drbg_update I contents else after_reseed_state_abs)) in *.

assert (ZLength_AUSA_val: Zlength (hmac256drbgabs_value after_update_state_abs) = 32).
{ subst after_update_state_abs.
  destruct na; trivial. apply Zlength_hmac256drbgabs_update_value. } 

assert (isbyte_AUSA_val: Forall isbyteZ (hmac256drbgabs_value after_update_state_abs)).
{ subst after_update_state_abs.
  destruct na; trivial. apply isbyteZ_hmac256drbgabs_update_value. }

thaw FR3.
set (after_update_Mpred := hmac256drbgabs_common_mpreds after_update_state_abs aaa (Vptr b i) Info) in *.
apply semax_pre with (P':=
  (PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance); 
   temp _out output; temp _left (Vint (Int.repr out_len)); 
   temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvar sha._K256 kv)
   SEP (data_at_ Tsh (tarray tuchar out_len) output; Stream stream1; 
     K_vector kv;
     da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
     after_update_Mpred ))).
{ go_lower. normalize.
  apply andp_right. apply prop_right; repeat split; trivial. cancel.
  subst after_update_Mpred. unfold hmac256drbgabs_common_mpreds(*. subst IC*); simpl.
  unfold hmac256drbg_relate, hmac256drbgstate_md_info_pointer.
  remember (hmac256drbgabs_to_state after_update_state_abs aaa).
  unfold hmac256drbgabs_to_state in Heqh. subst after_update_state_abs aaa. simpl in *.

  destruct should_reseed; subst add_len I; simpl in *.
  + assert (NA: na= false).
    { subst na. rewrite andb_false_r; trivial. }
    rewrite NA in *.
    remember (mbedtls_HMAC256_DRBG_reseed_function s (HMAC256DRBGabs key V reseed_counter entropy_len
             prediction_resistance reseed_interval)
                              (contents_with_add additional (Zlength contents)  contents)) as M.
    destruct PRS as [VV [KK [aa [zz [cc [ss [HM [? [? ?]]]]]]]]]. subst ss KK ctx1; rewrite HM in *.
    remember (HMAC256_DRBG_update contents key V) as UPD; destruct UPD as [KKK VVV].
    subst M after_reseed_state_abs. subst h; simpl in *.
    destruct PUPD; subst key2 ctx2. entailer!. 
  + destruct PRS as [? [? ?]]; subst stream1 key1 ctx1 after_reseed_state_abs.
    destruct (Memory.EqDec_val additional nullval); simpl in *.
    - destruct PUPD; subst ctx2 key2 na h; simpl in *. entailer!.
    - remember (initial_world.EqDec_Z (Zlength contents) 0) as q; destruct q; simpl in *. 
      * destruct PUPD; subst ctx2 key2 na h; simpl in *. entailer!. 
      * destruct PUPD as [bb [ii [UVAL [ADD [HUPD CTX2 ]]]]]. 
        unfold contents_with_add in HUPD. simpl in HUPD; rewrite <- Heqq in HUPD; simpl in HUPD.  
        rewrite <- HUPD in *. subst h ctx2; simpl in *. entailer!.
}  
subst after_update_Mpred.
assert (TR: mkSTREAM1 (prediction_resistance || (reseed_counter >? reseed_interval)) s
  key V reseed_counter entropy_len prediction_resistance reseed_interval
  additional contents stream1).
{ subst. red.
  remember ((prediction_resistance || (reseed_counter >? reseed_interval))%bool) as sr.
  destruct sr.
  + subst should_reseed. simpl in *.
    destruct PRS as [VV [KK [aa [zz [cc [ss [M [ES [? ?]]]]]]]]]. subst stream1 key1 ctx1. rewrite M; trivial.
  + subst should_reseed. simpl in *. destruct PRS as [? [? ?]]; subst stream1 key1 ctx1; trivial.
}
clear PUPD PRS ctx1 key1 ctx2 key2.

freeze [1;3] StreamAdd.
rewrite data_at__isptr with (p:=output). Intros.

set (AUV:=hmac256drbgabs_value after_update_state_abs) in *.
set (AUK:=hmac256drbgabs_key after_update_state_abs) in *.

set (HLP := HMAC_DRBG_generate_helper_Z HMAC256 (*after_update_key after_update_value*) AUK AUV).

  forward_while (
    EX done: Z,
      PROP  (0 <= done <= out_len; ((*WMod.*)is_multiple done 32) \/ done = out_len)
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr 32)); temp _info mc1(*(let (x, _) := md_ctx' in x)*);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out (offset_val done output); temp _left (Vint (Int.repr (out_len - done))); 
      temp _ctx (*ctx*)(Vptr b i); temp _p_rng (*ctx*)(Vptr b i); temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len));
      gvar sha._K256 kv
      )
      SEP  ((*Stream stream1;*)
      hmac256drbgabs_common_mpreds (hmac256drbgabs_update_value after_update_state_abs 
              (fst (HLP done)))
        aaa (Vptr b i) Info; FRZL StreamAdd; 
      data_at Tsh (tarray tuchar out_len) ((map Vint (map Int.repr
          (sublist 0 done (snd (HLP done))))) ++ 
          list_repeat (Z.to_nat (out_len - done)) Vundef) output; 
      K_vector kv)
  ).
  {
    (* prove the current precondition implies the loop condition *)
    Exists 0.
    change (sublist 0 0 (snd (HLP 0))) with (@nil Z).
    replace (out_len - 0) with out_len by omega.
    change ((map Vint (map Int.repr []) ++
          list_repeat (Z.to_nat out_len) Vundef)) with (list_repeat (Z.to_nat out_len) Vundef).
    assert (Hafter_update: (hmac256drbgabs_update_value after_update_state_abs(*AUSA*)
            (fst (HLP 0))) = after_update_state_abs(*AUSA*)).
    {
      simpl. (*destruct AUSA.*) simpl. subst AUV; simpl. destruct after_update_state_abs; reflexivity. (* unfold hmac256drbgabs_update_value.
      subst after_update_value; destruct after_update_state_abs; reflexivity.*)
    }
    rewrite Hafter_update.
    (*entailer!.*) go_lower. normalize. apply andp_right. apply prop_right; repeat split; trivial. omega. omega.
    left; exists 0; omega.
    cancel.
  }
  {
    (* prove the type checking of the loop condition *)
    entailer!.
  }
  { (*LOOP BODY -- INLINED VERSION*)
    (*semax_subcommand HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_random_with_add. *)
Opaque HMAC_DRBG_generate_helper_Z.
Opaque hmac256drbgabs_reseed.
Opaque mbedtls_HMAC256_DRBG_generate_function.
    eapply semax_post. (* TODO: generate_loopbody should be formalized in a better way such that it can be directly applied, and thus stackframe_of do not need to be unfolded manually. *)
    2: eapply (generate_loopbody StreamAdd) (*with (IS:=aaa) (IC:=IC)*); simpl; trivial.
    intros. unfold POSTCONDITION, abbreviate. old_go_lower. unfold loop1_ret_assert.
    subst; destruct ek; Intros; simpl; try cancel.
    unfold overridePost; simpl. destruct vl. unfold stackframe_of; simpl. cancel. normalize. (*
    rename H into Hdone.
    destruct H0 as [Hmultiple | Hcontra]; [| subst done; elim HRE; f_equal; omega].
    destruct Hmultiple as [n Hmultiple].
    unfold hmac256drbgabs_common_mpreds.
    normalize.
    assert (Hfield_md_ctx: forall ctx', isptr ctx' -> field_compatible t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx' -> ctx' = field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx').
    {
      intros ctx'' Hisptr Hfc.
      unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [|contradiction].
      simpl. change (Int.repr 0) with Int.zero. rewrite offset_val_force_ptr.
      destruct ctx''; inversion Hisptr. reflexivity.
    }
    unfold_data_at 1%nat.
    
    freeze [2;3;4;5] FR_unused_struct_fields.
    freeze [0;3;5] FR1.

    rewrite (field_at_data_at _ _ [StructField _md_ctx]). simpl.
    rewrite (field_at_data_at _ _ [StructField _V]). 
    simpl.

    unfold hmac256drbg_relate. subst I; simpl in *.

    destruct after_update_state_abs. simpl in *.
    unfold hmac256drbgabs_update_value.
(*    rewrite Heqinitial_state.*)
    unfold hmac256drbgabs_to_state.
(*    rewrite Heqafter_update_key.*)
    simpl in AUV, AUK. subst AUV AUK.
    unfold md_full. subst a; simpl.
    normalize. 

    (* size_t use_len = left > md_len ? md_len : left; *)
    forward_if (
  (PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance);
   temp _out (offset_val done output); temp _left (Vint (Int.repr (out_len - done)));
   temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvar sha._K256 kv;
      temp _t'6 (Vint (Int.repr (Z.min (Z.of_nat SHA256.DigestLength) (out_len - done)))))
   SEP (FRZL FR1;
   data_at Tsh (Tstruct _mbedtls_md_context_t noattr) (mc1, (mc2, mc3))
     (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] (Vptr b i));
   data_at Tsh (tarray tuchar 32)
     (map Vint (map Int.repr (fst (HLP done))))
     (field_address t_struct_hmac256drbg_context_st [StructField _V] (Vptr b i));
   data_at Tsh (tarray tuchar out_len)
     (map Vint
        (map Int.repr (sublist 0 done (snd (HLP done)))) ++
      list_repeat (Z.to_nat (out_len - done)) Vundef) output;
   UNDER_SPEC.FULL key0 mc3; K_vector kv))).
    {
      (* md_len < left *)
      forward.
      entailer!.
      rewrite Z.min_l; [reflexivity | omega].
    }
    {
      (* md_len >= left *)
      forward.
      entailer!.
      rewrite Z.min_r; [reflexivity | omega].
    }
    forward.

    (* mbedtls_md_hmac_reset( &ctx->md_ctx ); *)
    assert_PROP (field_compatible (Tarray tuchar 32 noattr) 
          []
          (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))) as FC_V by entailer!.
    assert_PROP (field_compatible t_struct_hmac256drbg_context_st
         [StructField _md_ctx] (Vptr b i)) as FC_M by entailer.
    forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] (*ctx*)(Vptr b i), (*md_ctx'*)(mc1,(mc2,mc3)), key0, kv).
    { simpl. cancel. }

    (* mbedtls_md_hmac_update( &ctx->md_ctx, ctx->V, md_len ); *)
    rename H into HZlength_V.  
    rename H0 into HisbyteZ_V.
    assert_PROP (field_compatible t_struct_hmac256drbg_context_st [StructField _V] (Vptr b i)) as FCV by entailer!.
    forward_call (key0, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] (*ctx*)(Vptr b i),
                  (*md_ctx'*)(mc1,(mc2,mc3)), 
                  field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i), 
                  @nil Z, (fst (HLP done)), kv).

    { simpl. apply prop_right. rewrite HZlength_V, field_address_offset; trivial.
      split; simpl; trivial. 
    }
    { simpl; simpl in HZlength_V; rewrite HZlength_V (*, <- Hmultiple*).
      cancel.
    }
    {
      simpl; simpl in HZlength_V; rewrite HZlength_V. 
      change Int.max_unsigned with 4294967295.
      change (two_power_pos 61) with 2305843009213693952.
      repeat split; try omega.
      apply HMAC_DRBG_generate_helper_Z_isbyteZ_fst; auto; try omega.
      apply isbyteZ_HMAC256. 
    }

    (*Intros vret; subst vret.*)
    rewrite app_nil_l.

    replace_SEP 2 (memory_block Tsh 32 (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))).
    { 
      entailer!.
      simpl in HZlength_V.
      unfold hmac256drbgabs_value.
      rewrite HZlength_V.
      apply data_at_memory_block.
    }

    (* mbedtls_md_hmac_finish( &ctx->md_ctx, ctx->V ); *)
    forward_call ((fst(HLP done)), key0, 
               field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] (*ctx*)(Vptr b i), 
               (*md_ctx'*)(mc1, (mc2, mc3)),
               field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i), Tsh, kv).
    {
      entailer!.
      rewrite field_address_offset; trivial. 
    }
    Intros vret; subst vret. simpl.
    assert_PROP (field_compatible (tarray tuchar out_len) [] output) as
        Hfield_compat_output by entailer!.
    replace_SEP 5 (
        data_at Tsh (tarray tuchar done) (map Vint (map Int.repr (sublist 0 done (snd (HLP done))))) output *
        data_at Tsh (tarray tuchar (out_len - done)) (list_repeat (Z.to_nat (out_len - done)) Vundef) (offset_val done output)
    ).
    {
      entailer!.
      apply derives_refl'.

      assert (HZlength1: Zlength (map Vint (map Int.repr (sublist 0 (n * 32)%Z (snd (HLP (n * 32)%Z))))) = (n * 32)%Z).
      {
        do 2 rewrite Zlength_map.
        rewrite Zlength_sublist; [omega|omega|]. subst HLP.
        rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; auto; try omega.
        apply hmac_common_lemmas.HMAC_Zlength.
        exists n; reflexivity.
      }
      
      apply data_at_complete_split; try rewrite HZlength1; try rewrite Zlength_list_repeat; auto; try omega.
      (*simpl. simpl in HZlength1. rewrite HZlength1.*)
      replace ((n * 32)%Z + (out_len - (n * 32)%Z)) with out_len by omega. assumption.
    }
    normalize.
    
    remember (offset_val done output) as done_output.
    remember (Z.min 32 (out_len - done)) as use_len.
    assert_PROP (field_compatible (tarray tuchar (out_len - done)) [] done_output) as Hfield_compat_done_output.
    {
      clear Heqdone_output Hmultiple.
      entailer!.
    }
    replace_SEP 1 (
        data_at Tsh (tarray tuchar use_len) (list_repeat (Z.to_nat use_len) Vundef) done_output *
        data_at Tsh (tarray tuchar (out_len - done - use_len)) (list_repeat (Z.to_nat (out_len - done - use_len)) Vundef) (offset_val use_len done_output)
    ).
    {
      clear Hmultiple Heqdone_output.
      entailer!.
      apply derives_refl'.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_list_repeat; auto; try omega.
        replace (32 + (out_len - done - 32)) with (out_len - done) by omega; assumption.
        rewrite list_repeat_app.
        rewrite <- Z2Nat.inj_add; try omega.
        replace (32 + (out_len - done - 32)) with (out_len - done) by omega; reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_list_repeat; auto; try omega.
        replace (out_len - done + (out_len - done - (out_len - done))) with (out_len - done) by omega; assumption.
        replace (out_len - done - (out_len - done)) with 0 by omega; simpl; rewrite app_nil_r; reflexivity.
      }
    }
    normalize.

    replace_SEP 0 (memory_block Tsh use_len done_output).
    {
      clear Hmultiple.
      entailer!.
      eapply derives_trans; [apply data_at_memory_block|].
      replace (sizeof (*cenv_cs*) (tarray tuchar (Z.min 32 (out_len - done)))) with (Z.min 32 (out_len - done)).
      apply derives_refl.
      simpl.
      destruct (Z.min_dec 32 (out_len - done));
      rewrite Zmax0r; omega.
    }
    set (H256 := HMAC256 (fst (HLP done)) key0) in *.
    assert (ZL_H256: Zlength H256 = 32).
    { subst H256. apply hmac_common_lemmas.HMAC_Zlength. }
    replace_SEP 6 (data_at Tsh (tarray tuchar use_len)
                      (sublist 0 use_len (map Vint (map Int.repr H256)))
                      (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i)) *
                   data_at Tsh (tarray tuchar (32 - use_len))
                      (sublist use_len 32 (map Vint (map Int.repr (H256))))
                      (offset_val use_len (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i)))).
    {
      clear Hmultiple.
      entailer!.
      apply derives_refl'.
      remember (fst (HLP done)) as V0'; clear HeqV0'.
      rewrite ZL_H256, Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        rewrite sublist_nil.
        rewrite app_nil_r.
        symmetry; apply sublist_same.
        reflexivity.
        repeat rewrite Zlength_map; rewrite ZL_H256; reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (out_len - done - 0 + (32 - (out_len - done))) with 32 by omega; auto.
        rewrite sublist_rejoin; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
        rewrite sublist_same; try reflexivity; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
      }
    }
    (* memcpy( out, ctx->V, use_len ); *)
    forward_call ((Tsh, Tsh), done_output, 
                  field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i), 
                  use_len,
                  sublist 0 use_len (map Int.repr H256)).
    {
      (*replace (map Vint (sublist 0 use_len (map Int.repr H256))) with 
              (sublist 0 use_len (map Vint (map Int.repr H256))).*)
      rewrite sublist_map. (*
      change (@data_at CompSpecs (fst (Tsh, Tsh)) (tarray tuchar use_len)
         (sublist 0 use_len (map Vint (map Int.repr H256)))
         (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))) with
      (@data_at hmac_drbg_compspecs.CompSpecs (fst (Tsh, Tsh)) (tarray tuchar use_len)
         (sublist 0 use_len (map Vint (map Int.repr H256)))
         (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))).*)
      Time entailer!.
      rewrite field_address_offset; trivial. 
    }
    { simpl. rewrite sublist_map. cancel. }
    { repeat split; auto;
      subst use_len; destruct (Z.min_dec 32 (out_len - done)); try omega.
      rewrite e; change (Int.max_unsigned) with 4294967295; omega.
    }

    simpl.
    gather_SEP 0 7.
    replace_SEP 0 (data_at Tsh (tarray tuchar 32) (map Vint (map Int.repr H256))
                               (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))).
    {
      clear Hmultiple.
      entailer!.
      apply derives_refl'.
      rewrite <- sublist_map.
      remember (fst (HLP done)) as V0'; clear HeqV0'.
      symmetry.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        rewrite sublist_nil.
        rewrite sublist_same; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
        remember (map Vint (map Int.repr (HMAC256 V0' key0))) as data.
        apply data_at_complete_split; subst data; repeat rewrite Zlength_map; try rewrite ZL_H256, Zlength_nil; auto; try omega.
        rewrite app_nil_r; reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        remember (sublist 0 (out_len - done) (map Vint (map Int.repr (HMAC256 V0' key0)))) as data_left.
        remember (sublist (out_len - done) 32
        (map Vint (map Int.repr (HMAC256 V0' key0)))) as data_right.
        apply data_at_complete_split; subst data_left data_right; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (out_len - done - 0 + (32 - (out_len - done))) with 32 by omega; auto.
        rewrite sublist_rejoin; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
        rewrite sublist_same; try reflexivity; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
      }
    }

    gather_SEP 1 2.
    replace_SEP 0 (data_at Tsh (tarray tuchar (out_len - done)) 
         ( (map Vint (sublist 0 use_len (map Int.repr H256)))
           ++ (list_repeat (Z.to_nat (out_len - done - use_len)) Vundef))
         done_output).
    {
      clear Heqdone_output Hmultiple.
      entailer!.
      apply derives_refl'.
      rewrite Zmin_spec.
      symmetry.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; 
           repeat rewrite Zlength_map; try rewrite Zlength_list_repeat; trivial; try omega.
        + rewrite Zlength_sublist; try omega.
            replace (32 - 0 + (out_len - done - 32)) with (out_len - done) by omega; trivial.
            rewrite Zlength_map; omega.
        + rewrite Zlength_sublist; try rewrite Zlength_map; omega. 
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; change ((fix map (l : list int) : list val :=
               match l with
               | [] => []
               | a :: t => Vint a :: map t
               end)
              (sublist 0 (out_len - done)
                 (map Int.repr H256)))  with (map Vint
              (sublist 0 (out_len - done)
                 (map Int.repr H256))); repeat rewrite Zlength_list_repeat; auto; try omega;
        rewrite Zlength_map; rewrite Zlength_sublist; try rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (out_len - done - 0 + (out_len - done - (out_len - done))) with (out_len - done) by omega.
        assumption.
      }
    }

    gather_SEP 2 0.
    replace_SEP 0 (
                  data_at Tsh (tarray tuchar out_len) 
                    ((map Vint (map Int.repr (sublist 0 done (snd (HLP done))))) ++
                     (map Vint (sublist 0 use_len (map Int.repr H256)) ++
                      list_repeat (Z.to_nat (out_len - done - use_len)) Vundef)) output).
    {
      entailer!.
      apply derives_refl'.
      symmetry.
      assert (HZlength1: Zlength ((snd (HLP (n * 32)%Z))) = (n * 32)%Z).
      { subst HLP.
        rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; auto; try omega.
        apply hmac_common_lemmas.HMAC_Zlength.
        exists n; reflexivity.
      }
      rewrite Zmin_spec. simpl in *.
      destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption];
      try rewrite HZlength_V.
      apply data_at_complete_split;
      repeat rewrite Zlength_app; repeat rewrite Zlength_map; try rewrite HZlength1; repeat rewrite Zlength_list_repeat; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega;
      try rewrite HZlength_V.
      replace ((n * 32)%Z - 0 + (32 - 0 + (out_len - (n * 32)%Z - 32))) with out_len by omega;
      assumption. 
      replace ((n * 32)%Z - 0 + (out_len - (n * 32)%Z - 0 + (out_len - (n * 32)%Z - (out_len - (n * 32)%Z)))) with out_len by omega.
      apply data_at_complete_split;
      repeat rewrite Zlength_app; repeat rewrite Zlength_map; try rewrite HZlength1; repeat rewrite Zlength_list_repeat; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega;
      try rewrite HZlength_V.
      replace (n * 32 - 0 + (out_len - n * 32 - 0 + (out_len - n * 32 - (out_len - n * 32)))) with
         out_len by omega.
      assumption.
    }

    (* out += use_len; *)
    forward.

    (* left -= use_len; *)
    forward.
    { 
      old_go_lower. 
      Exists (done + use_len).
      unfold hmac256drbgabs_common_mpreds; normalize.

      unfold_data_at 4%nat.
      rewrite (field_at_data_at _ _ [StructField _md_ctx]);
      rewrite (field_at_data_at _ _ [StructField _V]).
    
      unfold md_full.
    
      thaw FR1.
      thaw FR_unused_struct_fields.
      (*Ideal proof - but takes ages:
      Time entailer!. (*Coq8.5pl2: 1245secs*)
      {
        rewrite Zmin_spec.
        destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption]; repeat split; try omega.
        left; exists (n + 1); omega.
        replace (out_len - ((n * 32)%Z + 32)) with (out_len - (n * 32)%Z - 32) by omega;
        reflexivity.
        right; omega.
        replace (out_len - ((n * 32)%Z + (out_len - (n * 32)%Z))) with (out_len - (n * 32)%Z - (out_len - (n * 32)%Z)) by omega;
        reflexivity.
      }
      So let's do it by hand*)
      subst. rewrite (*H10,*) offset_offset_val. (*clear H10.*)
      apply andp_right. 
      { apply prop_right. 
        rewrite Zmin_spec.
        destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption]; repeat split; try omega.
        left; exists (n + 1); omega.
        replace (out_len - ((n * 32)%Z + 32)) with (out_len - (n * 32)%Z - 32) by omega.
        (*reflexivity.*) assumption. 
        (*right; omega.*)
        f_equal. f_equal. omega.
(*        replace (out_len - ((n * 32)%Z + (out_len - (n * 32)%Z))) with (out_len - (n * 32)%Z - (out_len - (n * 32)%Z)) by omega.*)
        assumption.
        right; omega. 
        assumption.
        f_equal. f_equal. omega.
        assumption.
      }
      cancel.

      (*Rest as with "ideal proof"*) 
      unfold md_full. simpl. normalize.
      replace H256 with (fst (HLP (n * 32 + Z.min 32 (out_len - n * 32))))%Z.
(*      replace (HMAC256 (fst (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)%Z))
              key0) with (fst (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32 + Z.min 32 (out_len - n * 32))))%Z.*)
      simpl.
      apply andp_right. apply prop_right; repeat split; trivial.
      { subst HLP. apply HMAC_DRBG_generate_helper_Z_Zlength_fst; trivial.
        rewrite Zmin_spec. destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption]; try rewrite HZlength_V; omega.
        apply hmac_common_lemmas.HMAC_Zlength. }
      { subst HLP.
        apply HMAC_DRBG_generate_helper_Z_isbyteZ_fst; trivial.
          rewrite Zmin_spec. destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption]; try rewrite HZlength_V; omega. 
          apply isbyteZ_HMAC256. } 
      unfold md_full. simpl. cancel. 
      rewrite app_assoc.
      replace (map Vint
        (map Int.repr
           (sublist 0 (n * 32)%Z
              (snd (HLP (n * 32)%Z)))) ++
        map Vint
         (sublist 0 (Z.min 32 (out_len - (n * 32)%Z))
           (map Int.repr
              (fst
                 (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))))) with (map Vint
        (map Int.repr
           (sublist 0 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))
              (snd
                 (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))))).
      replace (out_len - (n * 32)%Z - Z.min 32 (out_len - (n * 32)%Z)) with (out_len - ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))) by omega.
      apply derives_refl.
      (*reflexivity.*) (*entailer!.*)
      rewrite <- map_app.
      rewrite sublist_map.
      rewrite <- map_app.
      replace (sublist 0 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))
           (snd
              (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))) with (sublist 0 (n * 32)%Z
           (snd (HLP (n * 32)%Z)) ++
         sublist 0 (Z.min 32 (out_len - (n * 32)%Z))
           (fst
              (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))).
      reflexivity.
      replace (snd
              (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z)))) 
      with (snd (HLP (n * 32)%Z) ++ 
            fst (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z)))).
      {
        apply while_loop_post_sublist_app; auto. 
      }
      {
        apply while_loop_post_incremental_snd; auto.
        intros contra; rewrite contra, Zminus_diag in HRE. clear - HRE.
        elim HRE; trivial. 
      }
      {
        apply while_loop_post_incremental_fst; auto.
        intros contra; rewrite contra, Zminus_diag in HRE. clear - HRE.
        elim HRE; trivial. 
      }
    }
(*END OF INLINED LOOP BODY
Require Import hamcdrbg_verif_gen_whilebody.
  { (*LOOP BODY*) 
    semax_subcommand HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_random_with_add. 
    eapply gen_loopbodywith (after_update_state_abs :=after_update_state_abs). *)
  }*)
  } (*exfalso. apply myAx. Time Qed. 63s*)
  (*POST LOOP*)
  
  assert (Hdone: done = out_len).
  {
    clear - HRE H Hout_len.
    assert (Hdiff: out_len - done = 0).
    {
      unfold Int.eq in HRE.
      unfold zeq in HRE.
      destruct (Z.eq_dec (Int.unsigned (Int.repr (out_len - done)))
                (Int.unsigned (Int.repr 0))).
      rewrite (Int.unsigned_repr (out_len - done)) in e.
      rewrite e; reflexivity.
      change (Int.max_unsigned) with 4294967295; omega.
      rewrite HRE in *. elim n; trivial.
    }
    omega.
  }
  subst done.
  clear H H0.
  replace (out_len - out_len) with 0 by omega. clear HRE.
  change (list_repeat (Z.to_nat 0) Vundef) with (@nil val).
  rewrite app_nil_r.
  unfold hmac256drbgabs_common_mpreds.
  normalize. unfold hmac256drbg_relate.
  remember (hmac256drbgabs_update_value after_update_state_abs (fst (HLP out_len))) as ABS3.
  remember (hmac256drbgabs_to_state ABS3 aaa) as CTX3.
  destruct ABS3. destruct CTX3 as [aa [bb [cc [dd [ee ff]]]]]. normalize.
  unfold hmac256drbgabs_to_state in HeqCTX3. subst aaa; simpl in HeqCTX3. inv HeqCTX3.
  
  set (ctx3 := (mc1, (mc2, mc3),
          (map Vint (map Int.repr V0),
          (Vint (Int.repr reseed_counter0),
          (Vint (Int.repr entropy_len0),
          (Val.of_bool prediction_resistance0, Vint (Int.repr reseed_interval0))))))) in *.
  thaw StreamAdd.
  freeze [3;5] StreamOut. 

  (* mbedtls_hmac_drbg_update( ctx, additional, add_len ); *)
  (*subst add_len.*)
  forward_call (contents,
         additional, after_reseed_add_len, 
         (*ctx*)Vptr b i, ctx3,
         hmac256drbgabs_update_value after_update_state_abs (fst (HLP out_len)),
         kv, Info).
  { subst after_reseed_add_len. unfold hmac256drbg_relate. rewrite <- HeqABS3.
    subst ctx3. simpl. normalize. 
    apply andp_right. apply prop_right. repeat split; trivial.
    cancel. }
  { subst after_reseed_add_len. rewrite <- HeqABS3; simpl.
    split. destruct should_reseed; omega.
    split. assumption.
    split. destruct should_reseed; omega.
    split. assumption. assumption. }

  unfold hmac256drbgabs_common_mpreds. normalize.

  remember ((hmac256drbgabs_hmac_drbg_update
                (hmac256drbgabs_update_value after_update_state_abs (fst (HLP out_len)))
                (contents_with_add additional after_reseed_add_len contents))) as ABS4.
  set (ctx4 := hmac256drbgabs_to_state ABS4 ctx3) in *. rewrite <- HeqABS3 in HeqABS4.
  unfold hmac256drbg_relate.
  subst ctx3. simpl in ctx4. destruct ABS4. simpl in ctx4. subst ctx4. simpl. normalize.
  unfold hmac256drbgstate_md_info_pointer. simpl.
  freeze [2;3;4;5] FR5. 
  unfold_data_at 1%nat.
  freeze [1;2;4;5;6;7] FIELDS.
  forward. 
assert (RC_x: 0 <= hmac256drbgabs_reseed_counter after_reseed_state_abs < Int.max_signed).
{ subst after_reseed_state_abs.
  destruct should_reseed; simpl in *; [|trivial]. simpl.
  Transparent hmac256drbgabs_reseed. unfold hmac256drbgabs_reseed. Opaque hmac256drbgabs_reseed. simpl.
  assert (RS: mbedtls_HMAC256_DRBG_reseed_function =
          fun (entropy_stream: ENTROPY.stream) (a:hmac256drbgabs)
           (additional_input: list Z) =>
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               let sec_strength:Z := 32 (*not used -- measured in bytes, since that's how the calculations in DRBG_instantiate_function work *) in
               let state_handle: DRBG_state_handle := ((V, key, reseed_counter), sec_strength, prediction_resistance) in
               let max_additional_input_length := 256 
               in HMAC256_DRBG_reseed_function entropy_len entropy_len max_additional_input_length 
                     entropy_stream state_handle prediction_resistance additional_input
  end) by reflexivity.
  rewrite RS; clear RS. Opaque HMAC256_DRBG_reseed_function. subst I; simpl.
  remember (HMAC256_DRBG_reseed_function entropy_len entropy_len 256 s
      (V, key, reseed_counter, 32, prediction_resistance)
      prediction_resistance
      (contents_with_add additional (Zlength contents) contents)) as r.
  destruct r.  
  + destruct d as [[[[? ?] ?] ?] ?]. apply verif_hmac_drbg_WF.HMAC256_DRBG_reseed_functionWFaux in Heqr. simpl. apply Heqr.
  + simpl. trivial. }

assert (RC_y: 0 <= hmac256drbgabs_reseed_counter after_update_state_abs < Int.max_signed).
{ subst after_update_state_abs.
  destruct na; trivial. subst I; simpl.
  destruct (HMAC256_DRBG_update contents key V). simpl; trivial. }
  assert (RC1: 0 <= reseed_counter1 < Int.max_signed).
  { clear - RC_x RC_y HeqABS3 HeqABS4. 
    unfold hmac256drbgabs_hmac_drbg_update in HeqABS4.
    remember (HMAC256_DRBG_update
               (contents_with_add additional
                  after_reseed_add_len contents) key0
               V0) as z. destruct z. inv HeqABS4.
    unfold hmac256drbgabs_update_value in HeqABS3.
    subst after_update_state_abs.
    destruct na.
    + subst; simpl in *.
      remember (HMAC256_DRBG_update contents key V) as q. destruct q.
      inv HeqABS3. trivial. 
    + subst; simpl in *. subst after_reseed_state_abs. simpl in *.
      destruct should_reseed.
      - simpl in *.
        remember (hmac256drbgabs_reseed I s
              (contents_with_add additional (Zlength contents) contents)) as q.
        destruct q. simpl in *. inv HeqABS3; trivial.
      - subst I; simpl in *. inv HeqABS3; trivial. } 
  forward.
  forward.
  Exists (Vint (Int.repr 0)).
  apply andp_right. apply prop_right; split; trivial.
  thaw FIELDS. thaw FR5. thaw StreamOut.  
(*
  clear - WFI HeqABS4 HeqABS3 STREAM1 H1 H3 H4 H6 Hreseed_counter_in_range
          Hout_lenb ZLa Hreseed_interval.*)
  eapply derives_trans. apply (entailment2 key0 V0 reseed_counter0 entropy_len0 prediction_resistance0 reseed_interval0); try assumption; simpl in *. 
  + red in WFI; subst I; simpl in *. apply WFI.
  + normalize. unfold AREP, REP. Exists Info a. normalize.
Time Qed. (*61s*) 