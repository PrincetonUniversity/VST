Require Import floyd.proofauto.

Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.

Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC_refined_fp.

Require Import sha.hmac_sha256.

Require Import HMAC_definitions.
(*Require Import HMAC_part2LE. this file contains the implementation for the path key_len <= 64*)
(*Require Import HMAC_part2GT. this file contains the implementation for the path key_len > 64*)

(*Declare Module PART2LE: HMAC_PART2LE.*)
Declare Module PART2GT: HMAC_PART2GT.

(*Definition restLE := PART2LE.HMAC_LE.*)
Definition restGT := PART2GT.HMAC_GT.

Require Import HMAC_LoopBodyGT.

Lemma body_hmac_sha256: semax_body Vprog Gtot 
      f_hmac_sha256 hmac_spec.
Proof.
start_function.
name text' _text.
name key' _key.
name digest' _digest.
name textlen' _text_len.
name keylen' _key_len. 
assert (perms: permissions).
  unfold permissions, permissions', topshares. 
  specialize writable_share_top. simpl. intuition.
simpl_stackframe_of.
remember {| HMAC_Refined.args := a; 
            HMAC_Refined.locals := HMAC_Refined.initLocalVals |} as h0.
remember (tsh, (ksh, dsh)) as argshares.
apply semax_pre with (P':= EX V: VALUES, ASSN topshares argshares KV initFlags h0 a A A V).
(*apply semax_pre with (P' := ASSN_EQ topshares argshares initFlags h0 a A A).*)
  (*unfold interprete, ASSN, ASSN'. *) 
  unfold (*ASSN_EQ,*) ASSN, ASSN_SuperCanon, f_hmac_sha256.
  subst argshares. simpl.
  intros rho. apply exp_right with (x:=ApplyVAR rho).
  (*apply exp_right with (x:=eval_var sha._K256 (tarray tuint 64) rho).*)
  unfold ApplyVAR. simpl.
  unfold prop_args in H; simpl in H.
  destruct H as [HA1 [HA2 [HA3 [HA4 [HA5 [HA6 HA7]]]]]].
  unfold sizes, sizes'.
  unfold repr_locals, repr_local. simpl.
  abstract solve [entailer; cancel]. 
unfold (*ASSN_EQ,*) ASSN, ASSN_SuperCanon.
apply extract_exists_pre; intro VALS.
(*apply extract_exists_pre; intro KV. *)
remember (HMAC_Refined.snippet1 h0) as h1.
specialize (Zgt_cases (key_len a) 64); intros GT.
normalize.
remember
  (if key_len a >? 64 then 
    {| TEXT := TEXT A;
       TEXTLEN := TEXTLEN A;
       KEY := tk VALS; (* take care of assignment key = tk*) 
       KEYLEN := Vint (Int.repr SHA256_DIGEST_LENGTH); 
                      (*assignment key_len = SHA256_DIGEST_LENGTH*)
       DIGEST := DIGEST A |} 
    else A) as ANEW. 
remember (args h1) as anew.
forward_if (ASSN_SuperCanon topshares argshares A ANEW KV
   {| k_ipad := true;
                   k_opad := true;
                   tk:= negb (key_len a >? 64);
                   tk2:= true;
                   bufferIn:= true;
                   bufferOut:= true |} a anew (locals h1) VALS).
{ (*Then*)
  make_sequential. simpl. 
  (*destruct argshares as [tsh [ksh dsh]].*)
  unfold ASSN_SuperCanon. simpl.
  unfold repr_key.
  forward_call (KEY A, key_len a, ksh, tk topshares, key a, tk VALS).
  { assert (FR: Frame = 
       [`(data_at_ Tsh (Tarray tuchar 65 noattr) (k_ipad VALS)),
        `(data_at_ Tsh (Tarray tuchar 65 noattr) (k_opad VALS)), 
        `(data_at_ Tsh (Tarray tuchar 32 noattr) (tk2 VALS)),
        `(data_at_ Tsh (Tarray tuchar 1024 noattr) (bufferIn VALS)),
        `(data_at_ Tsh (Tarray tuchar 1024 noattr) (bufferOut VALS)),
        `(repr_text a tsh (TEXT A)), `(array_at_ tuchar dsh 0 32 (DIGEST A))]).
      subst Frame. reflexivity.
    rewrite FR; clear FR Frame.
    simpl. intros rho. entailer.
    unfold repr_locals, repr_key, repr_local. simpl.
    apply andp_right.  
      entailer. rewrite H4.
      destruct H as [[HA1a HA1b] [[HA2a [HA2b TL1024]] [HA3 [HA4 [HA5 [HA6 HA7]]]]]].
      rewrite <- H4, H5, H6 in *; clear H4 H5 H6.
      rewrite HA1b, HA2b in *.
      rewrite Zlength_correct in *.
      rewrite HA7 in *. simpl. unfold isPosSigned in HA1a.
      unfold two_power_pos, shift_pos. simpl. 
      assert (8 * Int.max_signed < 18446744073709551616). 
        rewrite int_max_signed_eq. omega.
      entailer. unfold repr_key.
      apply derives_trans with (Q:=!!(isptr (KEY A) /\ Forall isbyteZ (key a))).
           entailer. normalize. split; trivial. rewrite int_max_unsigned_eq. rewrite int_max_signed_eq in HA1a. omega.
    rewrite <- AxiomK. cancel.
      rewrite memory_block_array_tuchar; try omega.
      rewrite memory_block_array_tuchar; try omega.
      rewrite <- (data_at__array_at_ Tsh tuchar 32 noattr(tk VALS)); try omega; trivial.
   } 
   after_call.
   forward.
   forward. subst ANEW anew. 
   unfold ASSN_SuperCanon. simpl.
   intros rho. 
   entailer.
   unfold HMAC_Refined.snippet1; simpl.
   remember (HMAC_Refined.initLocalVals).
   unfold sem_cast_neutral in H4. simpl in H4. 
      destruct H as [[HA1a HA1b] [[HA2a [HA2b TL1024]] [HA3 [HA4 [HA5 [HA6 HA7]]]]]].
     rewrite HA1b in *. unfold force_val, Val.of_bool in H4.
     unfold both_int in H4. 
     unfold Int.lt in H4.
   rewrite Int.signed_repr in H4.
      Focus 2. rewrite int_min_signed_eq, int_max_signed_eq. omega.
   rewrite Int.signed_repr in H4.
      Focus 2. rewrite int_min_signed_eq.
               unfold isPosSigned in HA1a. omega.
   destruct (key_len a >? 64).
   { (*Case key_len a > 64*)
     clear H4. simpl.
     unfold repr_locals. 
     unfold repr_key, repr_text. rewrite Zplus_comm in TL1024. simpl in *.
     unfold repr_key_len, repr_text_len in *. rewrite Zplus_comm. simpl in *.
     rewrite HA2b in *; simpl in *. 
     rewrite Zlength_correct in *. rewrite Zlength_correct. 
     rewrite length_SHA256'. unfold SHA256_DIGEST_LENGTH. simpl.
     apply andp_right.
        unfold isPosSigned. rewrite H3, <- H10.
        abstract entailer. 
     rewrite memory_block_array_tuchar; try omega.
       cancel. rewrite functional_prog.SHA_256'_eq. simpl.
       rewrite <- HA1b. unfold SEPx. simpl.
        cancel. entailer. 
         rewrite <- AxiomK. cancel. }
   { exfalso.
     destruct (zlt 64 (key_len a)). omega.
      discriminate. (* inversion H4.*) }
  }
{ (* ELSE*)
  forward.
  unfold overridePost, ASSN_SuperCanon; simpl.
  intros x. unfold repr_locals; simpl. entailer.
   unfold HMAC_Refined.snippet1; simpl.
   remember (HMAC_Refined.initLocalVals). 
   unfold sem_cast_neutral in H2. simpl in H2.
(*  destruct argshares as [tsh [ksh dsh]]. *)
     destruct H as [[HH1 HH2] [[HH3 HH4] [HH5 [HH6 [HH7 [HH8 HH9]]]]]].
     rewrite HH2 in *. unfold force_val, Val.of_bool in H2.
     unfold both_int in H2. 
     unfold Int.lt in H2.
   rewrite <- H6 in *.
   rewrite Int.signed_repr in H2.
      Focus 2. rewrite int_min_signed_eq, int_max_signed_eq. omega.
   rewrite Int.signed_repr in H2.
      Focus 2. rewrite int_min_signed_eq.
               unfold isPosSigned in HH1. omega.
   destruct (key_len a >? 64).
   { (*Case key_len a > 64*)
     exfalso. 
     destruct (zlt 64 (key_len a)). discriminate. (*inversion H2.*) omega. }
   { unfold repr_key_len, repr_text_len. simpl.
     rewrite HH9, HH2; simpl.
     abstract entailer. 
   }
}
(*snippet 2*)
unfold ASSN_SuperCanon, repr_locals. simpl. normalize.

remember (key_len a >? 64) as KLENGTH.
destruct KLENGTH.
{ (* case key_len a > 64 *) 
  unfold HMAC_Refined.snippet1; simpl.
  remember (HMAC_Refined.initLocalVals).
  subst ANEW. simpl. simpl in *. unfold  SHA256_DIGEST_LENGTH in *; simpl in *.
  subst argshares.
  destruct H as [[HH1 HH2] [[HH3 [HH4 TL1024]] [HH5 [HH6 [HH7 [HH8 HH9]]]]]].
  unfold prop_args in H1. simpl in H1.
  rewrite HH4 in *.
  assert (TLN: text_len anew = text_len a).
     rewrite Heqanew, Heqh1, Heqh0. unfold HMAC_Refined.snippet1.
     simpl. rewrite <- HeqKLENGTH. simpl. reflexivity.
  assert (KLN: key_len anew = 32).
     rewrite Heqanew, Heqh1, Heqh0. unfold HMAC_Refined.snippet1.
     simpl. rewrite <- HeqKLENGTH. simpl. reflexivity.
  assert (TN: text anew = text a).
     rewrite Heqanew, Heqh1, Heqh0. unfold HMAC_Refined.snippet1.
     simpl. rewrite <- HeqKLENGTH. simpl. reflexivity.
  assert (KN: key anew = functional_prog.SHA_256' (key a)).
     rewrite Heqanew, Heqh1, Heqh0. unfold HMAC_Refined.snippet1.
     simpl. rewrite <- HeqKLENGTH. simpl. reflexivity.
  unfold repr_key_len, repr_text_len in H1. rewrite TN, KN, TLN, KLN in H1.
  clear H1. (*all conjuncts are trivial, or equal to assumptions we already have*)
  clear H0.

  assert (TLrange: 0 <= text_len a <= Int.max_unsigned).
    clear - HH3. destruct HH3.
    rewrite int_max_signed_eq in H0. rewrite int_max_unsigned_eq. omega.
  simpl in HH8. rewrite Int.unsigned_repr in HH8; trivial.
  assert (KLrange: 0 <= key_len a <= Int.max_unsigned).
    clear - HH1. destruct HH1.
    rewrite int_max_signed_eq in H0. rewrite int_max_unsigned_eq. omega.
  rewrite HH2 in HH9; simpl in HH9.
    rewrite Int.unsigned_repr in HH9; trivial.

  assert (TKN: tk (locals h1) = functional_prog.SHA_256' (key a)).
     rewrite Heqh1, Heqh0. unfold HMAC_Refined.snippet1. simpl.
     rewrite <- HeqKLENGTH. simpl. reflexivity.

  forward_call (* memset *) (Tsh, k_ipad VALS, 65, Int.zero).
  { assert (FR: Frame = [
        `(data_at_ Tsh (tarray tuchar 65) (k_opad VALS)),
        `(data_block Tsh (tk (locals h1)) (tk VALS)), (*DIFFERS FROM ELSE*)
        `(data_at_ Tsh (tarray tuchar 32) (tk2 VALS)),
        `(data_at_ Tsh (tarray tuchar 1024) (bufferIn VALS)),
        `(data_at_ Tsh (tarray tuchar 1024) (bufferOut VALS)), 
        `(K_vector KV),
        `(repr_key a ksh (KEY A)),
        `(repr_text a tsh (TEXT A)),
        `(memory_block dsh (Int.repr 32) (DIGEST A))]).  
      subst Frame. reflexivity. 
    rewrite FR. clear FR Frame.
    unfold repr_locals; simpl. intros rho.
    rewrite TKN.
    entailer.
    apply andp_right.
      rewrite <- H5; clear H5. simpl.
      rewrite (data_at__isptr _ _ (k_ipad VALS)). abstract entailer.
    assert (SF: Int.repr 65 = Int.repr (sizeof (tarray tuchar 65))) by reflexivity.
    rewrite SF, align_1_memory_block_data_at_; trivial.
   }
   after_call. 
   (*Warning: Collision between bound variables of name x *)
   subst retval0.

  forward_call (* memset *) (Tsh, k_opad VALS, 65, Int.zero).
  { assert (FR: Frame = [
        `(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0 65 (k_ipad VALS)),
        `(data_block Tsh (tk (locals h1)) (tk VALS)), (*DIFFERS FROM ELSE*)
        `(data_at_ Tsh (tarray tuchar 32) (tk2 VALS)),
        `(data_at_ Tsh (tarray tuchar 1024) (bufferIn VALS)),
        `(data_at_ Tsh (tarray tuchar 1024) (bufferOut VALS)), 
        `(K_vector KV),
        `(repr_key a ksh (KEY A)),
        `(repr_text a tsh (TEXT A)),
        `(memory_block dsh (Int.repr 32) (DIGEST A))]).  
      subst Frame. reflexivity.
    rewrite FR. clear FR Frame.
    unfold repr_locals; simpl. intros rho.
    entailer.
    rewrite TKN.
    apply andp_right.
      rewrite <- H6; clear H6. simpl.
      rewrite (data_at__isptr _ _ (k_opad VALS)). abstract entailer.
    assert (SF: Int.repr 65 = Int.repr (sizeof (tarray tuchar 65))) by reflexivity.
    rewrite SF, align_1_memory_block_data_at_; trivial. cancel.
   }
   after_call. 
   (*Warning: Collision between bound variables of name x *) 
   subst retval0.

   assert (ZLenSha: Zlength (tk (locals h1)) = 32).
     rewrite TKN, Zlength_correct.
     rewrite length_SHA256'. reflexivity.

   (**************** memcpy( k_ipad, key, key_len ) ******)
   unfold repr_key, data_block. 
   rewrite ZLenSha, TKN.
   eapply semax_pre with (P' :=(
   PROP  ((Forall isbyteZ (key a)); (Forall isbyteZ (functional_prog.SHA_256' (key a))))
   LOCAL  (`(eq (TEXT A)) (eval_id _text); `(eq (tk VALS)) (eval_id _key);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64));
   `(eq (Vint (Int.repr (text_len a)))) (eval_id _text_len);
   `(eq (Vint (Int.repr 32))) (eval_id _key_len);
   `(eq (DIGEST A)) (eval_id _digest);
   `(eq (k_ipad VALS)) (eval_var _k_ipad (tarray tuchar 65));
   `(eq (k_opad VALS)) (eval_var _k_opad (tarray tuchar 65));
   `(eq (tk VALS)) (eval_var _tk (tarray tuchar 32));
   `(eq (tk2 VALS)) (eval_var _tk2 (tarray tuchar 32));
   `(eq (bufferIn VALS)) (eval_var _bufferIn (tarray tuchar 1024));
   `(eq (bufferOut VALS)) (eval_var _bufferOut (tarray tuchar 1024)))
   SEP 
   (`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0 65 (k_opad VALS));
   `(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0 65 (k_ipad VALS));
   `(array_at tuchar Tsh
       (tuchars (map Int.repr (functional_prog.SHA_256' (key a)))) 0 32
       (tk VALS)); `(data_at_ Tsh (tarray tuchar 32) (tk2 VALS));
   `(data_at_ Tsh (tarray tuchar 1024) (bufferIn VALS));
   `(data_at_ Tsh (tarray tuchar 1024) (bufferOut VALS)); `(K_vector KV);
   `(array_at tuchar ksh (tuchars (map Int.repr (key a))) 0 (Zlength (key a))
       (KEY A)); `(repr_text a tsh (TEXT A));
   `(memory_block dsh (Int.repr 32) (DIGEST A))))).
   abstract entailer.

   normalize. rename H into isByteKey. rename H0 into isByteShaKey.

   (* following this recipe doesn't quite work, since some rewrite rule is missing to cleanup
      the postcondition after after_call
   eapply semax_seq'.
   frame_SEP 7 1.*)
   remember (Tsh, Tsh, k_ipad VALS, tk VALS, 32, 
            force_int oo (ZnthV tuchar (map Vint (map Int.repr (functional_prog.SHA_256' (key a)))))
       ) as WITNESS. 
   forward_call (* memcopy *) WITNESS.
   { rewrite HeqWITNESS; clear HeqWITNESS WITNESS.
     rewrite (split_array_at 32 tuchar _ _ 0 65 (k_ipad VALS)); try omega.
     assert (FR: Frame =
       [`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0 65 (k_opad VALS)),
        `(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 32 65 (k_ipad VALS)),
        `(data_at_ Tsh (tarray tuchar 32) (tk2 VALS)),
        `(data_at_ Tsh (tarray tuchar 1024) (bufferIn VALS)),
        `(data_at_ Tsh (tarray tuchar 1024) (bufferOut VALS)),
        `(K_vector KV),
        `(array_at tuchar ksh (tuchars (map Int.repr (key a))) 0 (Zlength (key a))
           (KEY A)),
        `(repr_text a tsh (TEXT A)),
        `(memory_block dsh (Int.repr 32) (DIGEST A)) ]).
       subst Frame. reflexivity.
     rewrite FR. clear FR Frame. 
     entailer. 
     cancel.
     rewrite sepcon_comm.
     apply sepcon_derives.
       apply array_at_ext'.
         intros. unfold tuchars, cVint, ZnthV. simpl. if_tac. omega. simpl.
          destruct (nth_mapVintZ i (functional_prog.SHA_256' (key a))) as [? I].
            rewrite Zlength_correct.
            rewrite length_SHA256'. simpl. assumption.            
          rewrite I; reflexivity.
     rewrite memory_block_array_tuchar. apply array_at_array_at_. reflexivity. 
          omega.  
   } 
   after_call. 
   (*Warning: Collision between bound variables of name x *)
   subst WITNESS. normalize. 
   subst retval0. 

   (**************** memcpy( k_opad, key, key_len ) ******)
(*   frame_SEP does not apply for some reason*)
   remember (Tsh, Tsh, k_opad VALS, tk VALS, 32, 
            force_int oo (ZnthV tuchar (map Vint (map Int.repr (functional_prog.SHA_256' (key a)))))
       ) as WITNESS.
   forward_call WITNESS.
   { rewrite HeqWITNESS; clear HeqWITNESS WITNESS.
     rewrite (split_array_at 32 tuchar _ _ 0 65 (k_opad VALS)); try omega.
     assert (FR: Frame =
       [`(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 32 65 (k_opad VALS)),
        `(array_at tuchar Tsh
          (cVint
            (force_int
               oo ZnthV tuchar
             (map Vint (map Int.repr (functional_prog.SHA_256' (key a)))))) 0 32 (k_ipad VALS)),
        `(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 32 65 (k_ipad VALS)),
        `(data_at_ Tsh (tarray tuchar 32) (tk2 VALS)),
        `(data_at_ Tsh (tarray tuchar 1024) (bufferIn VALS)),
        `(data_at_ Tsh (tarray tuchar 1024) (bufferOut VALS)),
        `(K_vector KV),
        `(array_at tuchar ksh (tuchars (map Int.repr (key a))) 0 (Zlength (key a))
           (KEY A)),
        `(repr_text a tsh (TEXT A)),
        `(memory_block dsh (Int.repr 32) (DIGEST A)) ]).
       subst Frame. reflexivity.
     rewrite FR. clear FR Frame. 
     entailer. 
     cancel.
     rewrite memory_block_array_tuchar. apply array_at_array_at_. reflexivity. 
          omega.  
   } 
   after_call. 
   subst WITNESS. normalize. 
   subst retval0. 

   (***************for -loop*********************)
     rewrite (split_array_at 64 tuchar Tsh _ 32 65); try omega.
     rewrite (split_array_at 64 tuchar Tsh _ 32 65); try omega.
  normalize.
  eapply semax_seq'. 
  frame_SEP 5 0 6 2. (* we want iall terms for k_ipad, k_opad below index 64*)
  unfold isbyteZ in isByteShaKey. 
  forward_for_simple_bound 64 (EX i:Z, 
  (PROP  ()
   LOCAL  (`(eq (TEXT A)) (eval_id _text); `(eq (tk VALS)) (eval_id _key);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64));
   `(eq (Vint (Int.repr (text_len a)))) (eval_id _text_len);
   `(eq (Vint (Int.repr 32))) (eval_id _key_len);
   `(eq (DIGEST A)) (eval_id _digest);
   `(eq (k_ipad VALS)) (eval_var _k_ipad (tarray tuchar 65));
   `(eq (k_opad VALS)) (eval_var _k_opad (tarray tuchar 65));
   `(eq (tk VALS)) (eval_var _tk (tarray tuchar 32));
   `(eq (tk2 VALS)) (eval_var _tk2 (tarray tuchar 32));
   `(eq (bufferIn VALS)) (eval_var _bufferIn (tarray tuchar 1024));
   `(eq (bufferOut VALS)) (eval_var _bufferOut (tarray tuchar 1024)))
   SEP 
   (
   `(array_at tuchar Tsh
       (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr (map Byte.unsigned (map Byte.repr (HMAC_FUN.mkKey (key a))))))))
       i 64 (k_opad VALS));
   `(array_at tuchar Tsh
       (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr (map Byte.unsigned (map Byte.repr (HMAC_FUN.mkKey (key a))))))))
       i 64 (k_ipad VALS));
   `(array_at tuchar Tsh
       (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr (map Byte.unsigned (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey (key a))) Opad))))))
       0 i (k_opad VALS));
   `(array_at tuchar Tsh
       (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr (map Byte.unsigned (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey (key a))) Ipad))))))
       0 i (k_ipad VALS))))).
   
   { (*precondition implies "invariant"*)
     rewrite array_at_emp. rewrite array_at_emp. entailer.
     apply andp_right. unfold array_at. abstract entailer.
     repeat rewrite (map_map Byte.unsigned). 
     rewrite (split_array_at 32 tuchar Tsh _ 0 64); try omega.
     rewrite (split_array_at 32 tuchar Tsh _ 0 64); try omega.
     assert (EQ: forall i, 0 <= i < 32 ->
         cVint (force_int oo ZnthV tuchar
            (map Vint (map Int.repr (functional_prog.SHA_256' (key a))))) i =
        cVint (force_int oo ZnthV tuchar
           (map Vint (map (fun x : byte => Int.repr (Byte.unsigned x))
                   (map Byte.repr (HMAC_FUN.mkKey (key a)))))) i).
     { intros; unfold cVint. f_equal; simpl.
       unfold ZnthV. destruct (zlt i 0); simpl; trivial.
       assert (I: (0 <= Z.to_nat i < length (functional_prog.SHA_256' (key a)))%nat).
          clear - H8. destruct H8. split; try omega.
          rewrite length_SHA256'. simpl. apply Z2Nat.inj_lt in H0. apply H0.
          trivial. omega.
       unfold HMAC_FUN.mkKey. simpl. rewrite HH9, <- HeqKLENGTH.
       unfold HMAC_FUN.zeroPad. rewrite map_app.  rewrite map_app.  rewrite map_app.  
       destruct (nth_mapVint (Z.to_nat i) (functional_prog.SHA_256' (key a))); trivial.
       rewrite H9. (* simpl. rewrite map_map. rewrite map_map.*)
       rewrite app_nth1.
       2: repeat rewrite map_length; apply I.  
       rewrite <- nth_default_eq in H9. unfold nth_default in H9.
       remember (nth_error
          (map Vint (map Int.repr (functional_prog.SHA_256' (key a))))
          (Z.to_nat i)) as d. 
       destruct d; inversion H9. clear H9; subst v. 
       apply eq_sym in Heqd. destruct (map_nth_error_inv _ _ _  _ Heqd) as [? [? ?]].
       inv H10; clear Heqd. destruct (map_nth_error_inv _ _ _  _ H9) as [? [? ?]]. 
       subst x0; clear H9.
       rewrite nth_map' with (d':=Int.zero). 
       rewrite nth_map' with (d':=Byte.repr Z0). 
       rewrite nth_map' with (d':=Z0). 
       rewrite <- nth_default_eq. unfold nth_default. rewrite H10.
       rewrite Byte.unsigned_repr. trivial.
       rewrite Forall_forall in isByteShaKey. 
       apply nth_error_in in H10. apply isByteShaKey in H10.
         unfold Byte.max_unsigned, Byte.modulus, Byte.wordsize. simpl. omega.
       apply I.
       rewrite map_length. apply I.
       repeat rewrite map_length. apply I.
     }
     assert (EQ2: forall i : Z, 32 <= i < 64 ->
        Vint Int.zero =
        cVint (force_int oo ZnthV tuchar
         (map Vint
           (map (fun x : byte => Int.repr (Byte.unsigned x))
              (map Byte.repr (HMAC_FUN.mkKey (key a)))))) i).
     { unfold cVint; simpl. intros. f_equal. 
       unfold ZnthV. if_tac. omega. clear H9. 
       assert (L: (Z.to_nat i < length (HMAC_FUN.mkKey (key a)))%nat).
          clear - H8. destruct H8. rewrite HMAC_FUN.mkKey_length. unfold SHA256_BlockSize.
          apply Z2Nat.inj_lt in H0. simpl in H0. omega. omega. omega.
       rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Byte.repr Z0). 
           rewrite nth_map' with (d':=Z0).
             unfold HMAC_FUN.mkKey. simpl. rewrite HH9, <- HeqKLENGTH.
             unfold HMAC_FUN.zeroPad. clear - H8. destruct H8 as [X Y]. 
             rewrite app_nth2.
               rewrite nth_Nlist. reflexivity.   
               rewrite length_SHA256'. simpl.
                   apply Z2Nat.inj_lt in Y. simpl in Y; omega. omega. omega. 
             rewrite length_SHA256'. simpl.
                   apply Z2Nat.inj_le in X. simpl in X; omega. omega. omega.
         repeat rewrite map_length; apply L.
         repeat rewrite map_length; apply L.
         repeat rewrite map_length; apply L.
     }
     rewrite <- (array_at_ext tuchar Tsh _ _ _ 32 EQ).
     rewrite <- (array_at_ext tuchar Tsh _ _ _ _ EQ2). abstract cancel.
   }
   { (*show that body satisfies "invariant"*)
     eapply (loopbodyGT Espec); try eassumption.
   }    
   { (*show increment*) trivial. (*normalize.*) }
   unfold update_tycon; simpl.
   repeat rewrite array_at_emp; simpl. normalize. 

(****************** continuation after for-loop **************************)
 remember (map Byte.unsigned
                         (HMAC_FUN.mkArg
                            (map Byte.repr (HMAC_FUN.mkKey (key a))) Ipad))
     as KIPAD.
 remember (force_int
           oo ZnthV tuchar
                (map Vint (map Int.repr KIPAD))) as IPAD.
 remember (map Byte.unsigned
                         (HMAC_FUN.mkArg
                            (map Byte.repr (HMAC_FUN.mkKey (key a))) Opad))
     as KOPAD.
 remember (force_int
           oo ZnthV tuchar
                (map Vint (map Int.repr KOPAD))) as OPAD.
  remember (force_int oo ZnthV tuchar (map Vint (map Int.repr (functional_prog.SHA_256' (key a))))) as KKEY. 
 remember (fun _ : Z => Vint Int.zero) as ZERO.
rewrite Zplus_comm in TL1024. 

eapply semax_pre0.
2: solve [eapply restGT; eassumption].
abstract solve [entailer; cancel].
}

{ (* case key_len a <= 64 *) 
   admit.
}
Qed.