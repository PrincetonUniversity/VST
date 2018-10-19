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
   (b:bool) (s:ENTROPY.stream) (mc:mdstate) (K V:list byte) (RC EL:Z) (PR:bool) (RI:Z) (c:list byte)
   (s':ENTROPY.stream) (K':list byte) (ctx':reptype t_struct_hmac256drbg_context_st):Prop :=
if b then 
  exists VV KK aa zz cc ss, 
    mbedtls_HMAC256_DRBG_reseed_function s
         (HMAC256DRBGabs K V RC EL PR RI) c
    = ENTROPY.success (VV, KK, aa, zz, cc) ss 
    /\ s' = ss /\ K'=KK /\
       ctx' = (mc,
            (map Vubyte VV,
            (Vint (Int.repr aa),
            (Vint (Int.repr EL),
            (Val.of_bool cc, Vint (Int.repr RI))))))
else s'=s /\ K'=K /\ ctx'=IS.

Definition POSTUPDATE (b:bool) additional c key V (mc:mdstate) RC EL PR RI ctx1 key1 K' (ctx':reptype t_struct_hmac256drbg_context_st): Prop :=
  if b 
  then (exists (bb : block), exists (ii : ptrofs), exists (UVal : list byte),
        additional = Vptr bb ii /\
        (K', UVal) =
           HMAC256_DRBG_update
             (contents_with_add (Vptr bb ii) (Zlength c) c) key V /\
        ctx' = (mc,
         (map Vubyte UVal,
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
  rename H3 into WFI.  
  assert (Hreseed_counter_in_range: 0 <= hmac256drbgabs_reseed_counter I < Int.max_signed) by apply WFI.
  assert (Hreseed_interval: RI_range (hmac256drbgabs_reseed_interval I)) by apply WFI.
  rename H1 into AddLenC. rename H2 into Hentlen.
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
        (map Vubyte V,
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
  forward_if  (out_len <= 1024).
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
    entailer!. 
  }

  Intros.  thaw FR0. clear Pctx.
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
  forward_if (add_len <= 256).
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
     { unfold contents_with_add. simple_if_tac. subst; trivial. rewrite Zlength_nil; trivial. }

  (*1. (aka VII and IX) Check reseed counter and PR*)
  set (should_reseed := orb prediction_resistance (reseed_counter >? reseed_interval)) in *.
  forward_if (temp _t'4 (Val.of_bool should_reseed)).
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
  { subst contents'; unfold contents_with_add. simple_if_tac. right; trivial. left; trivial. }
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
   gvars gv; temp _t'4 (Val.of_bool should_reseed))
   SEP (EX stream1 :ENTROPY.stream, EX key1:list byte, EX ctx1: reptype t_struct_hmac256drbg_context_st,
        (!! POSTRESEED aaa should_reseed s (mc1, (mc2,mc3)) key V reseed_counter entropy_len
            prediction_resistance reseed_interval
            (contents_with_add additional (Zlength contents) contents)
            stream1 key1 ctx1)
         &&
       (data_at shc t_struct_hmac256drbg_context_st ctx1 (Vptr b i) *
        data_at_ sho (tarray tuchar out_len) output *
        da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional *
        data_at shc t_struct_mbedtls_md_info Info mc1 * K_vector gv *
        md_full key1 (mc1, (mc2, mc3)) *
        Stream stream1))).

  { (*Case should_reseed = true*)
    assert (Hshould_reseed: should_reseed = true) by apply H; clear H.
    unfold POSTCONDITION, abbreviate. rewrite Hshould_reseed in *. clear POSTCONDITION. thaw FR2. 
    abbreviate_semax.

    forward_call (contents, additional, sha, add_len, (*ctx*)Vptr b i, shc, aaa, I, Info, s, gv).
    { subst I aaa; cancel.
      unfold hmac256drbg_relate. simpl in *. entailer!.
    } 
    { split3; auto. red in WFI; simpl in *. repeat split; trivial; try rep_omega.
      subst contents'. destruct ZLc' as [ZLc' | ZLc']; rewrite ZLc'; rep_omega.
    }
     
    Intros return_value.
    forward. 

    assert (F: 0>? 256 = false) by reflexivity.
    forward_if (return_value = Vzero).
    {
      (* reseed's return_value != 0 *) 
      rename H into Hrv.
      forward. simpl in *.
(*      clear - Hadd_lenb Hadd_len Hrv H3 Hout_lenb ZLa F H4 Hshould_reseed.*)
      Exists (Vint return_value).
      apply andp_right. apply prop_right; auto.
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
         (map Vubyte RSVal,
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
 
  forward_if (temp _t'5 (Val.of_bool na)).
  { destruct additional; simpl in PNadditional; try contradiction.
    + subst i0; entailer.
    + rewrite da_emp_ptr. normalize.
      apply denote_tc_test_eq_split.
      apply sepcon_valid_pointer2. 
      apply data_at_valid_ptr; auto.
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
  forward_if (EX ctx2:reptype t_struct_hmac256drbg_context_st, EX key2:list byte, 
  (PROP (POSTUPDATE na additional contents key V (mc1,(mc2,mc3)) reseed_counter entropy_len prediction_resistance reseed_interval ctx1 key1 key2 ctx2)
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance);
   temp _out output; temp _left (Vint (Int.repr out_len)); 
   temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); 
   gvars gv; temp _t'4 (Val.of_bool should_reseed);
   temp _t'5 (Val.of_bool na))
   SEP (FRZL FR3; K_vector gv;
   da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional;
    data_at shc t_struct_hmac256drbg_context_st ctx2 (Vptr b i) *
    md_full key2 (mc1, (mc2, mc3))))).
  { rewrite H in *. subst na.
     destruct should_reseed; simpl in PRS, H. rewrite andb_false_r in H; discriminate.
     destruct (initial_world.EqDec_Z (Zlength contents) 0); simpl in H.
     { rewrite andb_false_r in H; discriminate. }
     rewrite andb_true_r in H.
     destruct additional; simpl in PNadditional; try contradiction.
     { subst i0; discriminate. }
     destruct PRS as [? [? ?]]; subst key1 stream1 ctx1. clear H. 
     
       forward_call (contents, Vptr b0 i0, sha, after_reseed_add_len, 
                    (*ctx*)Vptr b i, shc, aaa,I, Info, gv).
       { assert (FR: Frame = [data_at_ sho (tarray tuchar out_len) output * Stream s]).
         { subst Frame; reflexivity. }
         subst Frame.
         subst after_reseed_add_len add_len aaa. cancel.
         thaw FR3. (*subst (*aaa*) IC.*)
         unfold hmac256drbg_relate, hmac256drbgstate_md_info_pointer; simpl. cancel. entailer!. 
       }
        split3; auto.
       { (*subst na.*)subst after_reseed_add_len.  entailer. unfold hmac256drbgabs_common_mpreds.
         remember ( HMAC256_DRBG_update
             (contents_with_add (Vptr b0 i0) (Zlength contents) contents) key
             V) as UPD. destruct UPD as [KK VV]. simpl. 
         Exists (mc1, (mc2, mc3),
            (map Vubyte VV,
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

set (after_update_state_abs := (if na then hmac256drbgabs_hmac_drbg_update I contents else after_reseed_state_abs)) in *.

assert (ZLength_AUSA_val: Zlength (hmac256drbgabs_value after_update_state_abs) = 32).
{ subst after_update_state_abs.
  destruct na; trivial. apply Zlength_hmac256drbgabs_update_value. } 

thaw FR3.
set (after_update_Mpred := hmac256drbgabs_common_mpreds shc after_update_state_abs aaa (Vptr b i) Info) in *.
apply semax_pre with (P':=
  (PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance); 
   temp _out output; temp _left (Vint (Int.repr out_len)); 
   temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvars gv)
   SEP (data_at_ sho (tarray tuchar out_len) output; Stream stream1; 
     K_vector gv;
     da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional;
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
      gvars gv
      )
      SEP  ((*Stream stream1;*)
      hmac256drbgabs_common_mpreds shc (hmac256drbgabs_update_value after_update_state_abs 
              (fst (HLP done)))
        aaa (Vptr b i) Info; FRZL StreamAdd; 
      data_at sho (tarray tuchar out_len) ((map Vubyte
          (sublist 0 done (snd (HLP done)))) ++ 
          list_repeat (Z.to_nat (out_len - done)) Vundef) output; 
      K_vector gv)
  ).
  {
    (* prove the current precondition implies the loop condition *)
    Exists 0.
    change (sublist 0 0 (snd (HLP 0))) with (@nil byte).
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
    apply sequential.
    eapply semax_post_flipped'. (* TODO: generate_loopbody should be formalized in a better way such that it can be directly applied, and thus stackframe_of do not need to be unfolded manually. *)
    eapply (generate_loopbody StreamAdd) (*with (IS:=aaa) (IC:=IC)*); simpl; trivial.
    unfold POSTCONDITION, abbreviate. simpl_ret_assert.
    old_go_lower.
    subst.
    Intros v; Exists v. entailer!. apply derives_refl.
   }

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
          (map Vubyte V0,
          (Vint (Int.repr reseed_counter0),
          (Vint (Int.repr entropy_len0),
          (Val.of_bool prediction_resistance0, Vint (Int.repr reseed_interval0))))))) in *.
  thaw StreamAdd.
  freeze [3;5] StreamOut. 

  (* mbedtls_hmac_drbg_update( ctx, additional, add_len ); *)
  (*subst add_len.*)
  forward_call (contents,
         additional, sha, after_reseed_add_len, 
         (*ctx*)Vptr b i, shc, ctx3,
         hmac256drbgabs_update_value after_update_state_abs (fst (HLP out_len)),
         Info, gv).
  { subst after_reseed_add_len. unfold hmac256drbg_relate. rewrite <- HeqABS3.
    subst ctx3. simpl. normalize. 
    apply andp_right. apply prop_right. repeat split; trivial.
    cancel. }
  { split3; auto. subst after_reseed_add_len. rewrite <- HeqABS3; simpl.
    split. destruct should_reseed; rep_omega.
    split. assumption.
    destruct should_reseed; omega. }

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
           (additional_input: list byte) =>
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
  + normalize. unfold AREP, REP. Exists Info a. normalize. apply derives_refl.
Time Qed. (*61s*) 