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
Require Import HMAC_lemmas.

Lemma loopbodyGT: forall Espec 
(A : ARGS)
(a : HMAC_Refined.Args)
(KV : val)
(text' : name _text)
(key' : name _key)
(digest' : name _digest)
(textlen' : name _text_len)
(keylen' : name _key_len)
(VALS : VALUES)
(isByteKey : Forall isbyteZ (key a))
(i : Z)
(Delta := func_tycontext f_hmac_sha256 Vprog Gtot)
(H : 0 <= i < 64),
@semax Espec  (initialized _i Delta)
  (PROP  ()
   LOCAL  (`(eq (Vint (Int.repr i))) (eval_id _i);
   `(eq (Vint (Int.repr 64))) (eval_expr (Econst_int (Int.repr 64) tint));
   `(eq (TEXT A)) (eval_id _text); `(eq (tk VALS)) (eval_id _key);
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
   (`(array_at tuchar Tsh
        (cVint
           (force_int
            oo ZnthV tuchar
                 (map Vint
                    (map Int.repr
                       (map Byte.unsigned
                          (map Byte.repr (HMAC_FUN.mkKey (key a)))))))) i 64
        (k_opad VALS));
   `(array_at tuchar Tsh
       (cVint
          (force_int
           oo ZnthV tuchar
                (map Vint
                   (map Int.repr
                      (map Byte.unsigned
                         (map Byte.repr (HMAC_FUN.mkKey (key a)))))))) i 64
       (k_ipad VALS));
   `(array_at tuchar Tsh
       (cVint
          (force_int
           oo ZnthV tuchar
                (map Vint
                   (map Int.repr
                      (map Byte.unsigned
                         (HMAC_FUN.mkArg
                            (map Byte.repr (HMAC_FUN.mkKey (key a))) Opad))))))
       0 i (k_opad VALS));
   `(array_at tuchar Tsh
       (cVint
          (force_int
           oo ZnthV tuchar
                (map Vint
                   (map Int.repr
                      (map Byte.unsigned
                         (HMAC_FUN.mkArg
                            (map Byte.repr (HMAC_FUN.mkKey (key a))) Ipad))))))
       0 i (k_ipad VALS))))
  (Ssequence
     (Sassign
        (Ederef
           (Ebinop Oadd (Evar _k_ipad (tarray tuchar 65)) (Etempvar _i tint)
              (tptr tuchar)) tuchar)
        (Ebinop Oxor
           (Ederef
              (Ebinop Oadd (Evar _k_ipad (tarray tuchar 65))
                 (Etempvar _i tint) (tptr tuchar)) tuchar)
           (Econst_int (Int.repr 54) tint) tint))
     (Sassign
        (Ederef
           (Ebinop Oadd (Evar _k_opad (tarray tuchar 65)) (Etempvar _i tint)
              (tptr tuchar)) tuchar)
        (Ebinop Oxor
           (Ederef
              (Ebinop Oadd (Evar _k_opad (tarray tuchar 65))
                 (Etempvar _i tint) (tptr tuchar)) tuchar)
           (Econst_int (Int.repr 92) tint) tint)))
  (normal_ret_assert
     (PROP  (0 <= i + 1 <= 64)
      LOCAL  (`(eq (Vint (Int.repr i))) (eval_id _i);
      `(eq (Vint (Int.repr 64))) (eval_expr (Econst_int (Int.repr 64) tint));
      `(eq (TEXT A)) (eval_id _text); `(eq (tk VALS)) (eval_id _key);
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
      (`(array_at tuchar Tsh
           (cVint
              (force_int
               oo ZnthV tuchar
                    (map Vint
                       (map Int.repr
                          (map Byte.unsigned
                             (map Byte.repr (HMAC_FUN.mkKey (key a))))))))
           (i + 1) 64 (k_opad VALS));
      `(array_at tuchar Tsh
          (cVint
             (force_int
              oo ZnthV tuchar
                   (map Vint
                      (map Int.repr
                         (map Byte.unsigned
                            (map Byte.repr (HMAC_FUN.mkKey (key a))))))))
          (i + 1) 64 (k_ipad VALS));
      `(array_at tuchar Tsh
          (cVint
             (force_int
              oo ZnthV tuchar
                   (map Vint
                      (map Int.repr
                         (map Byte.unsigned
                            (HMAC_FUN.mkArg
                               (map Byte.repr (HMAC_FUN.mkKey (key a))) Opad))))))
          0 (i + 1) (k_opad VALS));
      `(array_at tuchar Tsh
          (cVint
             (force_int
              oo ZnthV tuchar
                   (map Vint
                      (map Int.repr
                         (map Byte.unsigned
                            (HMAC_FUN.mkArg
                               (map Byte.repr (HMAC_FUN.mkKey (key a))) Ipad))))))
          0 (i + 1) (k_ipad VALS))))).
Proof. intros. 
     remember (cVint
             (force_int
              oo ZnthV tuchar
                   (map Vint
                      (map Int.repr
                         (map Byte.unsigned
                            (map Byte.repr (HMAC_FUN.mkKey (key a)))))))) as KKEY.
     remember (cVint
            (force_int
             oo ZnthV tuchar
                  (map Vint
                     (map Int.repr
                        (map Byte.unsigned
                           (HMAC_FUN.mkArg
                              (map Byte.repr (HMAC_FUN.mkKey (key a))) Opad)))))) as OPAD.
     remember (cVint
            (force_int
             oo ZnthV tuchar
                  (map Vint
                     (map Int.repr
                        (map Byte.unsigned
                           (HMAC_FUN.mkArg
                              (map Byte.repr (HMAC_FUN.mkKey (key a))) Ipad)))))) as IPAD.
destruct (nth_mapVintZ i (map Byte.unsigned (map Byte.repr (HMAC_FUN.mkKey (key a))))) as [n Hn].
    rewrite Zlength_correct, map_length. rewrite map_length, HMAC_FUN.mkKey_length. simpl. assumption.
simple eapply semax_seq'.

eapply semax_pre0; [ apply now_later | ].
{ eapply semax_post_flipped'.
   eapply NEWsemax_loadstore_array. 
     reflexivity. trivial. reflexivity. reflexivity. reflexivity.
     { entailer; repeat instantiate_Vptr.
       destruct (k_ipad VALS) eqn:?Hipad; try contradiction.
       rewrite <- Hipad in *.
       repeat apply andp_right; rel_expr. 
       intro; simpl. rewrite <- H0. rewrite Hipad. reflexivity.
       simpl typeof. simpl.
         instantiate (2:=Tsh). repeat rewrite sepcon_assoc. rewrite sepcon_comm.
         erewrite (split3_array_at' i tuchar Tsh _ i _ (k_ipad VALS)). 
         rewrite array_at_emp. normalize. rewrite (sepcon_comm TT). repeat rewrite sepcon_assoc. 
         apply sepcon_derives. rewrite Hipad. unfold add_ptr_int. simpl. rewrite mul_repr, Z.mul_1_l. cancel.
         entailer.
         reflexivity. 
         reflexivity.
         reflexivity.
         reflexivity.
         omega.
         discriminate.
         intros; simpl. 
           unfold ZnthV, cVint. simpl. if_tac. omega. 
           rewrite Hn. simpl. reflexivity.
         reflexivity.
     }
     instantiate (5:=1%nat). reflexivity. 
     trivial. 
     trivial. 
     split; omega. 

   eapply derives_refl.
}

  normalize.

   assert (Keyisbyte: Forall isbyteZ (HMAC_FUN.mkKey (key a))).
     unfold HMAC_FUN.mkKey.
     destruct (Zlength (key a) >? Z.of_nat SHA256_BlockSize);
       apply zeropad_isbyteZ; trivial.
     apply isbyte_sha.
eapply semax_pre0; [ apply now_later | ].
{ eapply semax_post_flipped'.
   eapply NEWsemax_loadstore_array. 
     reflexivity. trivial. reflexivity. reflexivity. reflexivity.
     { entailer; repeat instantiate_Vptr.
       destruct (k_opad VALS) eqn:?Hopad; try contradiction.
       rewrite <- Hopad in *.
       repeat apply andp_right; rel_expr.  
       intro; simpl. rewrite <- H0. rewrite Hopad. reflexivity.
       simpl typeof. simpl.
         instantiate (2:=Tsh). repeat rewrite sepcon_assoc. rewrite sepcon_comm.
         erewrite (split3_array_at' i tuchar Tsh _ i _ (k_opad VALS)); try reflexivity. 
         rewrite array_at_emp. normalize.
         rewrite <- (sepcon_comm (array_at tuchar Tsh
  (cVint
     (force_int
      oo ZnthV tuchar
           (map Vint
              (map Int.repr
                 (map Byte.unsigned (map Byte.repr (HMAC_FUN.mkKey (key a))))))))
  (Z.succ i) 64 (k_opad VALS))).
         repeat rewrite <- sepcon_assoc. apply sepcon_derives. entailer.
         rewrite Hopad. unfold add_ptr_int. simpl. rewrite mul_repr, Z.mul_1_l. cancel.
         omega.
         discriminate.
         intros; simpl. 
           unfold ZnthV, cVint. simpl. if_tac. omega. 
           rewrite Hn. simpl. reflexivity.
         reflexivity.
     }
     instantiate (5:=0%nat). reflexivity. 
     trivial. 
     trivial. 
     split; omega. 

   entailer. rewrite (split_array_at (i+1) tuchar Tsh _ i 64); try omega.
   rewrite (split_array_at (i+1) tuchar Tsh _ i 64); try omega.
   rewrite (split_array_at i tuchar Tsh _ 0 (i+1)); try omega.
   rewrite (split_array_at i tuchar Tsh _ 0 (i+1)); try omega.
   cancel. 
   assert (ARITH1: forall PAD BPAD 
     (HPAD: PAD = Byte.intval BPAD) k, i <= k < i+1 ->
     (upd
     (cVint
        (force_int
         oo ZnthV tuchar
              (map Vint
                 (map Int.repr
                    (map Byte.unsigned
                       (map Byte.repr (HMAC_FUN.mkKey (key a)))))))) i
     (Vint (Int.zero_ext 8 (Int.xor n (Int.repr PAD))))) k
     = (cVint
         (force_int
          oo ZnthV tuchar
               (map Vint
                  (map Int.repr
                     (map Byte.unsigned
                        (HMAC_FUN.mkArg
                           (map Byte.repr (HMAC_FUN.mkKey (key a))) BPAD)))))) k).
   { intros. unfold cVint, ZnthV, upd. if_tac. subst; simpl. 2: omega.
     if_tac. omega. simpl. f_equal.

    rewrite map_unsigned_Brepr_isbyte in Hn; trivial.
    rewrite (nth_indep _ _ (Vint Int.zero)) in Hn.
     erewrite mapnth' in Hn; try reflexivity.
     inversion Hn; clear Hn.
    rewrite H17.
    eapply nthD_1 in H17. instantiate (1:=Z0) in H17.
    destruct H17 as [z [KeyZ [NZ NN]]].
    rewrite Forall_forall in Keyisbyte. apply Keyisbyte in KeyZ.
     unfold HMAC_FUN.mkArg.
     rewrite (nth_indep _ _ (Vint Int.zero)).
     erewrite mapnth'. unfold force_int. 2: reflexivity.
     erewrite mapnth'. simpl.
     Focus 2. instantiate (1:=Z0). reflexivity.
     erewrite mapnth'.
     Focus 2. instantiate (1:=Byte.zero). reflexivity.
     erewrite mapnth'. simpl.
     Focus 2. instantiate (1:=(Byte.zero, Byte.zero)). reflexivity.  
     rewrite combine_nth.
     unfold sixtyfour. rewrite nth_Nlist. simpl. unfold Opad.
     erewrite mapnth'.
     Focus 2. instantiate (1:=0). reflexivity.
     rewrite NZ. clear NZ. subst n.
     apply Int.same_bits_eq. clear - KeyZ. intros.
        unfold Int.zero_ext. (*, Int.Zzero_ext. simpl.*)
     rewrite Int.testbit_repr; trivial.
     rewrite Int.testbit_repr; trivial.
     rewrite Int.Zzero_ext_spec; try omega.

     rewrite sha_lemmas.Ztest_Inttest, Int.bits_xor; trivial.
     rewrite Ztest_Bytetest.
     if_tac.
        assert (iB: 0 <= i < Byte.zwordsize).
          unfold Byte.zwordsize; simpl; omega.
        rewrite Byte.bits_xor; trivial.
        repeat rewrite Int.testbit_repr; trivial. 
        repeat rewrite Byte.testbit_repr; trivial.
     rewrite Byte.bits_above. trivial. apply H0.

    destruct H as [_ H]. apply Z2Nat.inj_lt in H; try omega. apply H.
    rewrite map_length. unfold sixtyfour. rewrite HMAC_FUN.mkKey_length, length_Nlist. reflexivity.
    repeat rewrite map_length. rewrite combine_length. rewrite map_length.
      unfold sixtyfour. rewrite HMAC_FUN.mkKey_length, length_Nlist. simpl.
      destruct H as [_ H]. apply Z2Nat.inj_lt in H; try omega. apply H.
    rewrite HMAC_FUN.mkKey_length. simpl.
      destruct H as [_ H]. apply Z2Nat.inj_lt in H; try omega. apply H.
    repeat rewrite map_length. rewrite HMAC_FUN.mkKey_length. simpl.
      destruct H as [_ H]. apply Z2Nat.inj_lt in H; try omega. apply H.
  }

  assert (Arth92 := ARITH1 54 Ipad (eq_refl _)).
  assert (Arth54 := ARITH1 92 Opad (eq_refl _)). clear ARITH1.
  erewrite (array_at_ext tuchar Tsh _ _ i (i+1) Arth92).
  erewrite (array_at_ext tuchar Tsh _ _ i (i+1) Arth54).
  clear Arth54 Arth92; cancel.

  assert (ARITH1: forall PAD k, i + 1 <= k < 64 ->
    upd (cVint
     (force_int
      oo ZnthV tuchar
           (map Vint
              (map Int.repr
                 (map Byte.unsigned (map Byte.repr (HMAC_FUN.mkKey (key a))))))))
     i (Vint (Int.zero_ext 8 (Int.xor n (Int.repr PAD)))) k 
   = cVint (force_int
      oo ZnthV tuchar
        (map Vint
           (map Int.repr
              (map Byte.unsigned (map Byte.repr (HMAC_FUN.mkKey (key a)))))))
    k).
   { clear. intros. unfold upd. if_tac. subst. omega. trivial. }

  rewrite (array_at_ext tuchar Tsh _ _ (i+1) 64 (ARITH1 92)).
  rewrite (array_at_ext tuchar Tsh _ _ (i+1) 64 (ARITH1 54)). cancel.
 }
Qed.