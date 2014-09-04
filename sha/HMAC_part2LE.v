Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.HMAC_functional_prog.

Require Import sha.hmac_sha256.

Require Import HMAC_definitions.

(*
Lemma andp_left: forall (P:Prop) (Q R: val -> mpred),
    (P -> Q |-- R) ->
    (!!P  && Q) |-- R.
Proof. intros. normalize. Qed. 
*)
Lemma andp_leftV: forall {A} (P:Prop) (Q R: A -> mpred) (v:A),
    (P -> Q v |-- R v) ->
    (!!P  && Q) v |-- R v.
Proof. intros. normalize.  unfold seplog.prop. unfold LiftNatDed. 
normalize. 
Qed.

Module HMAC_Part2ImplementationLE <: HMAC_PART2LE.

Lemma HMAC_LE Espec tsh ksh dsh: forall
(A : ARGS)
(a : HMAC_Refined.Args)
(KV : val)
(HH1 : 0 <= key_len a < Int.max_signed)
(HH2 : KEYLEN A = Vint (Int.repr (key_len a)))
(HH3 : isPosSigned (text_len a))
(TL : TEXTLEN A = Vint (Int.repr (text_len a)))
(TL1024 : 64 + text_len a <= 1024)
(HH5 : writable_share ksh)
(HH6 : writable_share dsh)
(HH7 : readable_share tsh)
(HH8 : Zlength (text a) = text_len a)
(HH9 : Zlength (key a) = key_len a)
(text' : name _text)
(key' : name _key)
(digest' : name _digest)
(textlen' : name _text_len)
(keylen' : name _key_len)
(perms : permissions)
(h0 : HMAC_Refined.hmacState)
(l : HMAC_Refined.Locals)
(Heql : l = HMAC_Refined.initLocalVals)
(Heqh0 : h0 = {| HMAC_Refined.args := a; HMAC_Refined.locals := l |})
(VALS : VALUES)
(HeqKLENGTH : false = (key_len a >? 64))
(GT : key_len a <= 64)
(H0 : sizes)
(TLrange : 0 <= text_len a <= Int.max_unsigned)
(isByteKey : Forall isbyteZ (key a))
(Delta := func_tycontext f_hmac_sha256 Vprog Gtot)
(*(POSTCONDITION := abbreviate : ret_assert)
(MORE_COMMANDS := abbreviate : statement)*)
(KL : 0 <= key_len a <= Int.max_unsigned)
(LK : (length (key a) <= 64)%nat)
(H : align_compatible tuchar (k_opad VALS))
(H1 : isptr (k_opad VALS))
(H2 : offset_in_range 64 (k_opad VALS))
(H3 : offset_in_range 64 (k_ipad VALS))
(H4 : align_compatible tuchar (k_ipad VALS))
(H5 : isptr (k_ipad VALS))
(KIPAD : list Z)
(HeqKIPAD : KIPAD =
           map Byte.unsigned
             (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey (key a))) Ipad))
(IPAD : Z -> int)
(HeqIPAD : IPAD = force_int oo ZnthV tuchar (map Vint (map Int.repr KIPAD)))
(KOPAD : list Z)
(HeqKOPAD : KOPAD =
           map Byte.unsigned
             (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey (key a))) Opad))
(OPAD : Z -> int)
(HeqOPAD : OPAD = force_int oo ZnthV tuchar (map Vint (map Int.repr KOPAD)))
(KKEY : Z -> int)
(HeqKKEY : KKEY = force_int oo ZnthV tuchar (map Vint (map Int.repr (key a))))
(ZERO : Z -> val)
(HeqZERO : ZERO = (fun _ : Z => Vint Int.zero)),
@semax Espec (initialized _i Delta)
  (PROP  ()
   LOCAL  (`(eq (TEXT A)) (eval_id _text); `(eq (KEY A)) (eval_id _key);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64));
   `(eq (TEXTLEN A)) (eval_id _text_len);
   `(eq (KEYLEN A)) (eval_id _key_len); `(eq (DIGEST A)) (eval_id _digest);
   `(eq (k_ipad VALS)) (eval_var _k_ipad (tarray tuchar 65));
   `(eq (k_opad VALS)) (eval_var _k_opad (tarray tuchar 65));
   `(eq (tk VALS)) (eval_var _tk (tarray tuchar 32));
   `(eq (tk2 VALS)) (eval_var _tk2 (tarray tuchar 32));
   `(eq (bufferIn VALS)) (eval_var _bufferIn (tarray tuchar 1024));
   `(eq (bufferOut VALS)) (eval_var _bufferOut (tarray tuchar 1024)))
   SEP  (`emp; `emp; `(array_at tuchar Tsh ZERO 64 65 (k_opad VALS));
   `(array_at tuchar Tsh ZERO 64 65 (k_ipad VALS));
   `(array_at tuchar Tsh (cVint OPAD) 0 64 (k_opad VALS));
   `(array_at tuchar Tsh (cVint IPAD) 0 64 (k_ipad VALS));
   `(array_at tuchar ksh (cVint KKEY) 0 (key_len a) (KEY A));
   `(data_at_ Tsh (tarray tuchar 32) (tk VALS));
   `(data_at_ Tsh (tarray tuchar 32) (tk2 VALS));
   `(data_at_ Tsh (tarray tuchar 1024) (bufferIn VALS));
   `(data_at_ Tsh (tarray tuchar 1024) (bufferOut VALS)); `(K_vector KV);
   `(repr_text a tsh (TEXT A)); `(memory_block dsh (Int.repr 32) (DIGEST A))))
  (Ssequence
     (Scall None
        (Evar _memset
           (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
              (tptr tvoid) cc_default))
        [Evar _bufferIn (tarray tuchar 1024), Econst_int (Int.repr 0) tint,
        Econst_int (Int.repr 1024) tint])
     (Ssequence
        (Scall None
           (Evar _memcpy
              (Tfunction
                 (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                 (tptr tvoid) cc_default))
           [Evar _bufferIn (tarray tuchar 1024),
           Evar _k_ipad (tarray tuchar 65), Econst_int (Int.repr 64) tint])
        (Ssequence
           (Scall None
              (Evar _memcpy
                 (Tfunction
                    (Tcons (tptr tvoid)
                       (Tcons (tptr tvoid) (Tcons tuint Tnil))) (tptr tvoid)
                    cc_default))
              [Ebinop Oadd (Evar _bufferIn (tarray tuchar 1024))
                 (Econst_int (Int.repr 64) tint) (tptr tuchar),
              Etempvar _text (tptr tuchar), Etempvar _text_len tint])
           (Ssequence
              (Scall None
                 (Evar _SHA256
                    (Tfunction
                       (Tcons (tptr tuchar)
                          (Tcons tuint (Tcons (tptr tuchar) Tnil))) tvoid
                       cc_default))
                 [Evar _bufferIn (tarray tuchar 1024),
                 Ebinop Oadd (Econst_int (Int.repr 64) tint)
                   (Etempvar _text_len tint) tint,
                 Evar _tk2 (tarray tuchar 32)])
              (Ssequence
                 (Scall None
                    (Evar _memset
                       (Tfunction
                          (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                          (tptr tvoid) cc_default))
                    [Evar _bufferOut (tarray tuchar 1024),
                    Econst_int (Int.repr 0) tint,
                    Econst_int (Int.repr 1024) tint])
                 (Ssequence
                    (Scall None
                       (Evar _memcpy
                          (Tfunction
                             (Tcons (tptr tvoid)
                                (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                             (tptr tvoid) cc_default))
                       [Evar _bufferOut (tarray tuchar 1024),
                       Evar _k_opad (tarray tuchar 65),
                       Econst_int (Int.repr 64) tint])
                    (Ssequence
                       (Scall None
                          (Evar _memcpy
                             (Tfunction
                                (Tcons (tptr tvoid)
                                   (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                          [Ebinop Oadd (Evar _bufferOut (tarray tuchar 1024))
                             (Econst_int (Int.repr 64) tint) (tptr tuchar),
                          Evar _tk2 (tarray tuchar 32),
                          Econst_int (Int.repr 32) tint])
                       (Ssequence 
                         (Scall None
                          (Evar _SHA256
                             (Tfunction
                                (Tcons (tptr tuchar)
                                   (Tcons tuint (Tcons (tptr tuchar) Tnil)))
                                tvoid cc_default))
                          [Evar _bufferOut (tarray tuchar 1024),
                          Ebinop Oadd (Econst_int (Int.repr 64) tint)
                            (Econst_int (Int.repr 32) tint) tint,
                          Etempvar _digest (tptr tvoid)])
                         (Sreturn None)))))))))
  (frame_ret_assert
     (function_body_ret_assert tvoid
        SEP  (`(K_vector KV);
        `(repr_key a ksh (KEY A)); 
        `(repr_text a tsh (TEXT A));
        `(repr_digest false (fst (RefinedHMAC a)) dsh (DIGEST A))))
     (stackframe_of f_hmac_sha256)).
Proof.
intros.
  (*frame_SEP 1.  does not work*)
  gather_SEP 9.
  forward_call (* memset *) (Tsh, bufferIn VALS, 1024, Int.zero).
  { entailer. 
    rewrite HH2, TL in *. inversion H8; clear H8. inversion H9; clear H9.
    subst textlen' keylen'.
    rewrite <- H14; simpl.
    apply andp_right. 
     (*THIS SHOULD BE provable just by using normalize, and/or sem_cast_neutral_ptr.*)
     unfold data_at_, data_at, data_at', array_at'; simpl. normalize.
    repeat rewrite sepcon_assoc.
    apply sepcon_derives. 
      rewrite <- (memory_block_data_at_ Tsh (tarray tuchar 1024)).
      simpl. normalize.
      reflexivity.
      reflexivity.
    apply sepcon_fold. rewrite <- H7. subst Frame. reflexivity.
   }
   after_call. 
   (*Warning: Collision between bound variables of name x *)
   subst retval0.  

   focus_SEP 11 3.
   (* eapply semax_seq'.
   frame_SEP 0 1.*)
(*NEW*)
   rewrite (split_offset_array_at tuchar Tsh _ 0 64 1024). normalize.
     2: omega.
     2: simpl; omega.
     2: reflexivity.
  rename H6 into BufferInOffset0.
  rename H7 into BufferInOffset1024. (*
  assert (BufferInOffset64: offset_in_range 64 (bufferIn VALS)).
  red. destruct (bufferIn VALS); simpl; trivial. destruct  BufferInOffset1024. destruct BufferInOffset0.
     rewrite Zplus_0_r in *. omega.*)

   focus_SEP 0 2.
   remember (Tsh, Tsh, bufferIn VALS, k_ipad VALS, 64, IPAD) as WITNESS. 
   forward_call WITNESS.
   { rewrite HeqWITNESS; clear HeqWITNESS WITNESS. 
     assert (FR: Frame = [
     `(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0 (1024 - 64)
         (offset_val (Int.repr 64) (bufferIn VALS)));
      `(array_at tuchar Tsh ZERO 64 65 (k_opad VALS));
      `(array_at tuchar Tsh ZERO 64 65 (k_ipad VALS));
      `(array_at tuchar Tsh (cVint OPAD) 0 64 (k_opad VALS));
      `(array_at tuchar ksh (cVint KKEY) 0 (key_len a) (KEY A));
      `(data_at_ Tsh (tarray tuchar 32) (tk VALS));
      `(data_at_ Tsh (tarray tuchar 32) (tk2 VALS));
      `(data_at_ Tsh (tarray tuchar 1024) (bufferOut VALS)); `(K_vector KV);
      `(repr_text a tsh (TEXT A)); `(memory_block dsh (Int.repr 32) (DIGEST A))]).
      subst Frame. reflexivity.
     rewrite FR; clear FR Frame.
     entailer. cancel.
     rewrite memory_block_array_tuchar. cancel. omega.
   }
   after_call.
   subst WITNESS. (*doing frameSEP above yields sth like this: 
          unfold update_tycon. simpl. intros. normalize. simpl. entailer.*)
   normalize.
   subst retval0.
   assert (KIPAD_length: length KIPAD = 64%nat).
     subst KIPAD. unfold HMAC_FUN.mkArg. repeat rewrite map_length.
     rewrite combine_length, map_length. rewrite HMAC_FUN.mkKey_length.
     unfold sixtyfour. rewrite length_Nlist. unfold SHA256_BlockSize. reflexivity.
   assert (KOPAD_length: length KOPAD = 64%nat).
     subst KOPAD. unfold HMAC_FUN.mkArg. repeat rewrite map_length.
     rewrite combine_length, map_length. rewrite HMAC_FUN.mkKey_length.
     unfold sixtyfour. rewrite length_Nlist. unfold SHA256_BlockSize. reflexivity.
   
   remember (64 + text_len a) as tla.
   focus_SEP 11 2.
   unfold repr_text, data_block. simpl. normalize. rename H6 into isByteText. 
   (*the simpl prior to the normalize is important - otherwise the fact isByte text is
     not pushed above the line. SO WHEN does normalize need to be preceded by simpl?
     We don't want to do it always, since it would unfold 64 + X etc*) 

   focus_SEP 1.
   rewrite (split_offset_array_at tuchar Tsh _ 0 (text_len a) 960). normalize.
     2: subst; omega.
     2: simpl; omega.
     2: reflexivity.
   rename H6 into BufferInOffset64_0.
   rename H7 into BufferInOffset64_960.
   focus_SEP 0 2.
   remember (960 - text_len a) as nsa.
   remember (offset_val (Int.repr (64 + text_len a)) (bufferIn VALS)) as buffIn64TLA.
   remember (force_int
           oo ZnthV tuchar
                (map Vint
                   (map Int.repr (text a))))
      as CONTENT.
   remember (tsh, Tsh, offset_val (Int.repr 64) (bufferIn VALS), TEXT A, text_len a,  
            CONTENT) as WITNESS. 
   forward_call WITNESS.
   { rewrite HeqWITNESS; clear HeqWITNESS WITNESS. 
     assert (FR: Frame = [
     `(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0 nsa buffIn64TLA);
      `(array_at tuchar Tsh (cVint IPAD) 0 64 (k_ipad VALS));
      `(array_at tuchar Tsh (cVint IPAD) 0 64 (bufferIn VALS));
      `(array_at tuchar Tsh ZERO 64 65 (k_opad VALS));
      `(array_at tuchar Tsh ZERO 64 65 (k_ipad VALS));
      `(array_at tuchar Tsh (cVint OPAD) 0 64 (k_opad VALS));
      `(array_at tuchar ksh (cVint KKEY) 0 (key_len a) (KEY A));
      `(data_at_ Tsh (tarray tuchar 32) (tk VALS));
      `(data_at_ Tsh (tarray tuchar 32) (tk2 VALS));
      `(data_at_ Tsh (tarray tuchar 1024) (bufferOut VALS)); `(K_vector KV);
      `(memory_block dsh (Int.repr 32) (DIGEST A))]). 
      subst Frame. reflexivity.
     rewrite FR; clear FR Frame.
     entailer. 
     remember (64 + text_len a) as tla. (*AGAIN*)
     rewrite HH2 in *. inversion H8; clear H8. subst keylen'. 
     rewrite TL in *. inversion H7; clear H7. subst textlen'.
     rewrite <- H13. 
     entailer.
     cancel.
     rewrite sepcon_comm.
     apply sepcon_derives.
       unfold repr_text, data_block.
       simpl. entailer. rewrite HH8. apply array_at_ext'.
       intros. unfold tuchars, cVint, ZnthV. simpl. 
       if_tac. omega. 
       destruct (nth_mapVintZ i (text a)) as [? NTH]. rewrite HH8; assumption.
       rewrite NTH; reflexivity.
     rewrite memory_block_array_tuchar'.
       apply array_at_array_at_; reflexivity.
       eapply isptr_offset_val'. assumption.   
       clear - HH3. destruct HH3. omega. 
    }
    after_call.

    subst WITNESS.
    normalize.
    subst retval0.


   focus_SEP 1 4 10 12.
   remember (HMAC_FUN.innerArg (text a) (map Byte.repr (HMAC_FUN.mkKey (key a)))) as INNERARG.
   remember (bufferIn VALS, tla, Tsh, Tsh, INNERARG, tk2 VALS) as WITNESS.
   forward_call WITNESS.
   { rewrite HeqWITNESS; clear HeqWITNESS WITNESS. 
     assert (FR: Frame = [
      `(array_at tuchar tsh (cVint CONTENT) 0 (text_len a) (TEXT A));
      `(array_at tuchar Tsh ZERO tla 1024 (bufferIn VALS));
      `(array_at tuchar Tsh (cVint IPAD) 0 64 (k_ipad VALS));
      `(array_at tuchar Tsh ZERO 64 65 (k_opad VALS));
      `(array_at tuchar Tsh ZERO 64 65 (k_ipad VALS));
      `(array_at tuchar Tsh (cVint OPAD) 0 64 (k_opad VALS));
      `(array_at tuchar ksh (cVint KKEY) 0 (key_len a) (KEY A));
      `(data_at_ Tsh (tarray tuchar 32) (tk VALS));
      `(data_at_ Tsh (tarray tuchar 1024) (bufferOut VALS));
      `(memory_block dsh (Int.repr 32) (DIGEST A))]). 
      subst Frame. reflexivity.
     rewrite FR; clear FR Frame.

     entailer.
     rewrite HH2 in *. inversion H8; clear H8. subst keylen'. 
     rewrite TL in *. inversion H7; clear H7. subst textlen'.
     assert (InnerArgTLA:
       Z.of_nat
         (length
            (HMAC_FUN.innerArg (text a)
               (map Byte.repr (HMAC_FUN.mkKey (key a)))))
        = 64 + text_len a).
         unfold HMAC_FUN.innerArg, HMAC_FUN.mkArgZ. 
         rewrite map_length in KIPAD_length.
         rewrite app_length, map_length, KIPAD_length.
         rewrite <- HH8, Zlength_correct, Nat2Z.inj_add. reflexivity.
     rewrite InnerArgTLA. 
     remember (64 + text_len a) as tla. (*AGAIN*)
     assert (TLA_POS64: tla * 8 < two_power_pos 64).
      clear - Heqtla TL1024 HH3.
       rewrite two_power_pos_equiv. destruct HH3.
        remember (text_len a) as z; clear Heqz.  subst. 
        clear - H TL1024. remember (64 + z). clear Heqz0. 
        assert (z0 * 8 <= 1024 * 8) by omega. clear - H0.
        destruct (zlt (z0 * 8) (2^64)).  trivial. exfalso. simpl in *. 
          unfold Z.pow_pos in g. simpl in g. omega.
     entailer.
     cancel.
     rewrite <- AxiomK. cancel. 
     rewrite <- memory_block_data_at_; try reflexivity.
      normalize. cancel. 
     unfold data_block. 
      assert (Forall isbyteZ
        (HMAC_FUN.innerArg (text a) (map Byte.repr (HMAC_FUN.mkKey (key a))))).
        rewrite Forall_forall.
        unfold HMAC_FUN.innerArg; intros. apply in_app_or in H8.
        destruct H8.
          unfold HMAC_FUN.mkArgZ in H8. 
          apply list_in_map_inv in H8. destruct H8 as [b [B1 _]]. subst x.
          apply isByte_ByteUnsigned.
        rewrite Forall_forall in isByteText. apply isByteText; trivial.
      entailer.
    unfold HMAC_FUN.innerArg, HMAC_FUN.mkArgZ. rewrite Zlength_correct.
      rewrite app_length, KIPAD_length.
   red in BufferInOffset64_960. red in BufferInOffset1024.
   rewrite (split_offset_array_at tuchar Tsh _ 0 64 (Z.of_nat (64 + length (text a)))). 
     Focus 2. destruct HH3. clear - H19. rewrite Nat2Z.inj_add. split. omega.
              assert (64 = Z.of_nat 64) by reflexivity. 
              rewrite <- H. remember 64. clear Heqz H. omega. 
     2: simpl; omega.
     2: reflexivity.
   entailer.
   assert (offset_in_range (Z.of_nat (64 + length (text a))) (bufferIn VALS)).
     red; intros. clear - HH8 TL1024 HH3 BufferInOffset0 BufferInOffset1024.
     destruct (bufferIn VALS); trivial. rewrite Nat2Z.inj_add. 
              rewrite <- Zlength_correct. rewrite HH8. 
              assert (64 = Z.of_nat 64) by reflexivity. 
              rewrite <- H. split; try omega.
              destruct BufferInOffset0. rewrite Zplus_0_r in H0. destruct HH3. omega.
  entailer.
  remember (map Byte.unsigned
                 (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey (key a)))
                    Ipad)) as KIPAD. (*AGAIN*)
Lemma array_at_local_facts':
  forall (t : type) (sh : Share.t) (f : Z -> reptype t) (lo hi : Z) (v : val),
  array_at t sh f lo hi v |-- array_at t sh f lo hi v && !!isptr v && !!offset_in_range (sizeof t * lo) v &&
!!offset_in_range (sizeof t * hi) v && !!align_compatible t v.
Proof. intros. unfold array_at. entailer. Qed.

  eapply derives_trans.
    eapply sepcon_derives. 
    eapply sepcon_derives. apply derives_refl. apply array_at_local_facts'. apply derives_refl.

  normalize. rename H19 into QQ1. rename H20 into QQ2. rename H21 into QQ3.
  rewrite sepcon_assoc.
  rewrite sepcon_comm.
  repeat rewrite sepcon_assoc.
  apply sepcon_derives.
      apply array_at_ext'; 
         unfold tuchars, cVint, ZnthV; intros.
         simpl. if_tac. omega.
           assert (ARITH: (0 <= Z.to_nat i < 64)%nat).
             destruct H19 as [XX YY]. apply Z2Nat.inj_lt in YY. simpl in YY. omega. assumption. omega.
           rewrite map_app. rewrite map_app, app_nth1.
           destruct (nth_mapVint (Z.to_nat i) KIPAD) as [? N]. rewrite KIPAD_length; apply ARITH.
           rewrite N; reflexivity. 
           repeat rewrite map_length. rewrite KIPAD_length. omega.
  rewrite sepcon_comm.
  apply sepcon_derives.
    assert (Z.of_nat (64 + length (text a)) - 64 = text_len a).
      rewrite  Nat2Z.inj_add. 
              assert (64 = Z.of_nat 64) by reflexivity. 
              rewrite <- H19. 
              rewrite <- Zlength_correct. rewrite HH8. omega.
    rewrite H19.  
      apply array_at_ext'; 
         unfold tuchars, cVint, ZnthV; intros.
         simpl. if_tac. omega. if_tac.  omega.
         rewrite map_app. rewrite map_app, app_nth2. 
           repeat rewrite map_length. rewrite KIPAD_length.
           destruct (nth_mapVint (Z.to_nat i) (text a)) as [? N].
              destruct H20 as [XX YY]. split. omega. apply Z2Nat.inj_lt in YY. simpl in YY.
                rewrite <- HH8, Zlength_correct, Nat2Z.id in YY. apply YY.
              assumption. omega.
           assert ((Z.to_nat (i + 64) - 64)%nat = Z.to_nat i).
             rewrite Z2Nat.inj_add. simpl. omega. omega. omega. 
           rewrite H23, N. reflexivity. 
         repeat rewrite map_length. rewrite KIPAD_length.  rewrite Z2Nat.inj_add. simpl. omega.
             omega. omega.
   rewrite (split_offset_array_at tuchar Tsh _ (64 + text_len a) (64 + text_len a) 1024). normalize.
     2: omega.
     2: simpl; omega.
     2: reflexivity.
   entailer. rewrite Nat2Z.inj_add, <- Zlength_correct, HH8 in QQ1. entailer.
   rewrite array_at_emp.
   assert (960 - text_len a = 1024 - (64 + text_len a)).
     omega.
  rewrite H19. entailer. 

    }
    after_call.
    subst WITNESS.
    normalize.


(****************** outer application of sha **************************)

(*Here's an issue with globals_only - let's try to resolve it uing semax_pre.
 We also remember the fact align_compatible tuchar (bufferOut VALS) that would
  otherwise be lost*)
apply semax_pre with (P':=  (PROP  (align_compatible tuchar (bufferOut VALS))
   LOCAL  (`(eq (TEXT A)) (eval_id _text); `(eq (KEY A)) (eval_id _key);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64));
   `(eq (Vint (Int.repr (text_len a)))) (eval_id _text_len);
   `(eq (KEYLEN A)) (eval_id _key_len); `(eq (DIGEST A)) (eval_id _digest);
   `(eq (k_ipad VALS)) (eval_var _k_ipad (tarray tuchar 65));
   `(eq (k_opad VALS)) (eval_var _k_opad (tarray tuchar 65));
   `(eq (tk VALS)) (eval_var _tk (tarray tuchar 32));
   `(eq (tk2 VALS)) (eval_var _tk2 (tarray tuchar 32));
   `(eq (bufferIn VALS)) (eval_var _bufferIn (tarray tuchar 1024));
   `(eq (bufferOut VALS)) (eval_var _bufferOut (tarray tuchar 1024)))
   SEP ((`K_vector (eval_var sha._K256 (tarray tuint 64)));
     `(data_block Tsh INNERARG (bufferIn VALS));
     `(data_block Tsh (SHA256.SHA_256 INNERARG) (tk2 VALS));
   `(array_at tuchar tsh (cVint CONTENT) 0 (text_len a) (TEXT A));
   `(array_at tuchar Tsh ZERO tla 1024 (bufferIn VALS));
   `(array_at tuchar Tsh (cVint IPAD) 0 64 (k_ipad VALS));
   `(array_at tuchar Tsh ZERO 64 65 (k_opad VALS));
   `(array_at tuchar Tsh ZERO 64 65 (k_ipad VALS));
   `(array_at tuchar Tsh (cVint OPAD) 0 64 (k_opad VALS));
   `(array_at tuchar ksh (cVint KKEY) 0 (key_len a) (KEY A));
   `(data_at_ Tsh (tarray tuchar 32) (tk VALS));
   `(data_at_ Tsh (tarray tuchar 1024) (bufferOut VALS));
   `(memory_block dsh (Int.repr 32) (DIGEST A))))).
  entailer. 
     rewrite HH2 in *. inversion H8; clear H8. subst keylen'. 
     rewrite TL in *. inversion H7; clear H7. subst textlen'.
     rewrite <- AxiomK. entailer. 

     (*This should really have been proven as part of the entailer 3 lines above.
         Also, again the simpl here is necessary to prove the goal*)
     unfold data_at_, data_at. simpl. normalize. 

  normalize. (*in order to push align_compatible tuchar above the line*)
  rename H6 into bufferOutAC.

  unfold MORE_COMMANDS, abbreviate.
  (*frame_SEP 1.  does not work*)
  gather_SEP 11.
  forward_call (* memset *) (Tsh, bufferOut VALS, 1024, Int.zero).
  { entailer. 
     rewrite HH2 in *. inversion H8; clear H8. subst keylen'. 
    repeat rewrite sepcon_assoc.
    apply sepcon_derives. 
      rewrite <- (memory_block_data_at_ Tsh (tarray tuchar 1024)).
      simpl. normalize.
      reflexivity.
      reflexivity.
    apply sepcon_fold. rewrite <- H7. subst Frame. reflexivity.
   }
   after_call. 
   (*Warning: Collision between bound variables of name x *)
   subst retval0.  

   focus_SEP 12.
   rewrite (split_offset_array_at tuchar Tsh _ 0 64 1024). normalize.
     2: omega.
     2: simpl; omega.
     2: reflexivity.
   rename H6 into BufferOutOffset0.
   rename H7 into BufferOutOffset1024.
   focus_SEP 0 8.
   (* eapply semax_seq'.
   frame_SEP 0 1.*)
   remember (Tsh, Tsh, bufferOut VALS, k_opad VALS, 64,  OPAD 
       ) as WITNESS. 
   forward_call WITNESS.
   { rewrite HeqWITNESS; clear HeqWITNESS WITNESS. 
     assert (FR: Frame = [
      `(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0 (1024 - 64)
         (offset_val (Int.repr 64) (bufferOut VALS))); 
      `(K_vector KV);
      `(data_block Tsh INNERARG (bufferIn VALS));
      `(data_block Tsh (SHA256.SHA_256 INNERARG) (tk2 VALS));
      `(array_at tuchar tsh (cVint CONTENT) 0 (text_len a) (TEXT A));
      `(array_at tuchar Tsh ZERO tla 1024 (bufferIn VALS));
      `(array_at tuchar Tsh (cVint IPAD) 0 64 (k_ipad VALS));
      `(array_at tuchar Tsh ZERO 64 65 (k_opad VALS));
      `(array_at tuchar Tsh ZERO 64 65 (k_ipad VALS));
      `(array_at tuchar ksh (cVint KKEY) 0 (key_len a) (KEY A));
      `(data_at_ Tsh (tarray tuchar 32) (tk VALS));
      `(memory_block dsh (Int.repr 32) (DIGEST A))]).
      subst Frame. reflexivity.
     rewrite FR; clear FR Frame.
     entailer. cancel.
     rewrite memory_block_array_tuchar. cancel. omega.
   }
   after_call.
   subst WITNESS. (*doing frameSEP above yields sth like this: 
          unfold update_tycon. simpl. intros. normalize. simpl. entailer.*)
   normalize.
   subst retval0.

   focus_SEP 2.
   rewrite (split_offset_array_at tuchar Tsh _ 0 32 960). normalize.
     2: omega.
     2: simpl; omega.
     2: reflexivity.
   rename H6 into BufferOutOffset64_0.
   rename H7 into BufferOutOffset64_960.
   focus_SEP 6 0.
   remember (force_int
           oo ZnthV tuchar
                (map Vint
                   (map Int.repr (SHA256.SHA_256 INNERARG))))
      as CONTENT1.
   remember (Tsh, Tsh, offset_val (Int.repr 64) (bufferOut VALS), tk2 VALS, 32,  
            CONTENT1) as WITNESS. 
   forward_call WITNESS.
   { rewrite HeqWITNESS; clear HeqWITNESS WITNESS. 
     assert (FR: Frame = [
      `(array_at tuchar ksh (cVint KKEY) 0 (key_len a) (KEY A)),
      `(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 96 1024 (bufferOut VALS)),
      `(array_at tuchar Tsh (cVint OPAD) 0 64 (k_opad VALS)),
      `(array_at tuchar Tsh (cVint OPAD) 0 64 (bufferOut VALS)),
      `(K_vector KV),
      `(data_block Tsh INNERARG (bufferIn VALS)),
      `(array_at tuchar tsh (cVint CONTENT) 0 (text_len a) (TEXT A)),
      `(array_at tuchar Tsh ZERO tla 1024 (bufferIn VALS)),
      `(array_at tuchar Tsh (cVint IPAD) 0 64 (k_ipad VALS)),
      `(array_at tuchar Tsh ZERO 64 65 (k_opad VALS)),
      `(array_at tuchar Tsh ZERO 64 65 (k_ipad VALS)),
      `(data_at_ Tsh (tarray tuchar 32) (tk VALS)),
      `(memory_block dsh (Int.repr 32) (DIGEST A)) ]). 
      subst Frame. reflexivity.
     rewrite FR; clear FR Frame.
     entailer. 
     rewrite HH2 in *. inversion H7; clear H7. subst keylen'. 
     rewrite <- H13.
     entailer. cancel.
(*     rewrite (split_array_at 96). 2: omega.
     cancel.
     rewrite sepcon_comm.*)

(*
  eapply derives_trans.
    eapply sepcon_derives. 
    eapply sepcon_derives. apply derives_refl. apply array_at_local_facts'. apply derives_refl.

*)

     repeat rewrite sepcon_assoc.
     apply sepcon_derives.
       unfold data_block.
       simpl. rewrite <- functional_prog.SHA_256'_eq.
       rewrite Zlength_correct, length_SHA256', Z2Nat.id.
       entailer. apply array_at_ext'.
       intros. unfold tuchars.  unfold cVint. simpl. 
       unfold ZnthV. if_tac. omega. simpl.
       destruct (nth_mapVintZ i (functional_prog.SHA_256'
                 (HMAC_FUN.innerArg (text a)
                    (map Byte.repr (HMAC_FUN.mkKey (key a)))))) as [? NTH].  
         rewrite Zlength_correct, length_SHA256', Z2Nat.id. assumption. 
        unfold SHA256_DIGEST_LENGTH. omega.
       rewrite NTH; reflexivity.
        unfold SHA256_DIGEST_LENGTH. omega.
     rewrite memory_block_array_tuchar'.
     cancel.
     2: eapply isptr_offset_val'; assumption.   
     2: omega.
   rewrite (split_offset_array_at tuchar Tsh _ 96 96 1024). normalize.
     2: omega.
     2: simpl; omega.
     2: reflexivity.
   entailer.
    assert (OR: offset_in_range 96 (bufferOut VALS) ). 
      clear - BufferOutOffset0 BufferOutOffset1024.
      unfold offset_in_range in *.
      destruct (bufferOut VALS); trivial. omega.
    entailer.
   rewrite array_at_emp.
   entailer. (*Here's where we need align_compatible tuchar (bufferOut VALS)*)
    }
    after_call.

    subst WITNESS.
    normalize.
    subst retval0.

   focus_SEP 1 6 14. 
   remember (HMAC_FUN.outerArg  (SHA256.SHA_256 INNERARG) (map Byte.repr (HMAC_FUN.mkKey (key a)))) 
      as OUTERARG.
   remember (bufferOut VALS, 96, Tsh, dsh, OUTERARG, DIGEST A) as WITNESS.
   forward_call WITNESS.
   { rewrite HeqWITNESS; clear HeqWITNESS WITNESS.
     assert (FR: Frame = [
       `(array_at tuchar Tsh (cVint CONTENT1) 0 32 (tk2 VALS)),
       `(array_at tuchar ksh (cVint KKEY) 0 (key_len a) (KEY A)),
       `(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 96 1024 (bufferOut VALS)),
       `(array_at tuchar Tsh (cVint OPAD) 0 64 (k_opad VALS)),
       `(data_block Tsh INNERARG (bufferIn VALS)),
       `(array_at tuchar tsh (cVint CONTENT) 0 (text_len a) (TEXT A)),
       `(array_at tuchar Tsh ZERO tla 1024 (bufferIn VALS)),
       `(array_at tuchar Tsh (cVint IPAD) 0 64 (k_ipad VALS)),
       `(array_at tuchar Tsh ZERO 64 65 (k_opad VALS)),
       `(array_at tuchar Tsh ZERO 64 65 (k_ipad VALS)),
       `(data_at_ Tsh (tarray tuchar 32) (tk VALS))]).
      subst Frame. reflexivity.
     rewrite FR; clear FR Frame. 
     entailer.
     rewrite HH2 in *. inversion H7; clear H7. subst keylen'.
(*     assert (OuterArgLEN:length OUTERARG = 96%nat).
         subst OUTERARG.*) unfold HMAC_FUN.outerArg, HMAC_FUN.mkArgZ. 
(*         rewrite <- HeqKOPAD.*)
(*         rewrite map_length in KOPAD_length.*)
         rewrite app_length, KOPAD_length.
         rewrite <- functional_prog.SHA_256'_eq, length_SHA256'.
     apply andp_right.
         unfold SHA256_DIGEST_LENGTH; simpl. 
         assert (768 < two_power_pos 64). 
         clear. simpl.
          rewrite two_power_pos_equiv. simpl.  
            unfold Z.pow_pos; simpl. omega.
        entailer. 
     rewrite <- AxiomK. 
     cancel. 
     unfold data_block.
 entailer.
     apply andp_right. 
     assert (isBT: Forall isbyteZ
         (map Byte.unsigned
            (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey (key a))) Opad) ++
          functional_prog.SHA_256'
            (HMAC_FUN.innerArg (text a)
               (map Byte.repr (HMAC_FUN.mkKey (key a)))))).
       apply Forall_app.
       split. apply isbyte_map_ByteUnsigned .
              apply isbyte_sha.
     simpl. entailer.
  rewrite Zlength_correct.
      rewrite app_length, KOPAD_length.
      rewrite length_SHA256'.
      rewrite (split_array_at 64 tuchar Tsh _ 0 (Z.of_nat (64 + (Z.to_nat SHA256_DIGEST_LENGTH)))).
      Focus 2.
            clear.
         unfold SHA256_DIGEST_LENGTH; simpl.  omega.
      remember (map Byte.unsigned
                 (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey (key a)))
                    Opad)) as KOPAD. (*AGAIN*)
      rewrite sepcon_comm.
      apply sepcon_derives.
         apply array_at_ext'; 
         unfold tuchars, cVint, ZnthV; intros.
         simpl. if_tac. omega.
           assert (ARITH: (0 <= Z.to_nat i < 64)%nat).
             destruct H7 as [XX YY]. apply Z2Nat.inj_lt in YY. simpl in YY. omega. assumption. omega.
           rewrite map_app. rewrite map_app, app_nth1.
           destruct (nth_mapVint (Z.to_nat i) KOPAD) as [? N]. rewrite KOPAD_length; apply ARITH.
           rewrite N; reflexivity. 
           repeat rewrite map_length. rewrite KOPAD_length. omega.
      rewrite <- (offset_val_array_at 64 tuchar), Zplus_0_r, Nat2Z.inj_add. 
      { apply array_at_ext'; 
         unfold tuchars, cVint, ZnthV; intros. 
         simpl. if_tac. omega. if_tac. omega.
           rewrite map_app. rewrite map_app.
           assert (ARITH: (Z.to_nat i - 64 < Z.to_nat SHA256_DIGEST_LENGTH)%nat).
               clear - H7.
                  unfold SHA256_DIGEST_LENGTH in *.  simpl in *. destruct H7 as [XX YY].
                  apply Z2Nat.inj_lt in YY. simpl in YY. omega. omega. omega.
           clear - ARITH KOPAD_length H21.
           rewrite (app_nth2 (map Vint (map Int.repr KOPAD))); intros.
             repeat rewrite map_length. rewrite KOPAD_length.
             rewrite  Z2Nat.inj_sub. simpl.
             erewrite nth_map'. instantiate (1:=Int.zero). f_equal.
                rewrite map_length. rewrite length_SHA256'. apply ARITH.
          omega.
        rewrite map_length. rewrite map_length. rewrite KOPAD_length. 
          assert (64 <= i). omega. clear -H. apply Z2Nat.inj_le in H; try omega. simpl in H. omega.
      }
      reflexivity.
      unfold offset_strict_in_range. destruct (bufferOut VALS); try contradiction.
      simpl. clear - BufferOutOffset0 BufferOutOffset1024. 
             unfold offset_in_range in *. rewrite Zplus_0_r in *. omega. 
  }
  after_call.
(*
xml_parse-error - unable to communicate wtih coqtop, restarting coqtop.
Error was: Mutex.try_lock: error code 0.
*)

   subst WITNESS. normalize. 

unfold POSTCONDITION, abbreviate.
remember (RefinedHMAC a) as solution. (*without this, the following forward takes ages, and
      clearly does too much simplification/unfolding, resulting in a too big goal*)

forward.
repeat rewrite sepcon_assoc.
apply sepcon_derives. rewrite <- AxiomK. cancel.
unfold repr_text.
assert (TEXTOK: (array_at tuchar tsh
         (cVint
            (force_int oo ZnthV tuchar (map Vint (map Int.repr (text a))))) 0
         (text_len a) (TEXT A)
        |-- data_block tsh (text a) (TEXT A))).
   unfold data_block. entailer.
   rewrite <- HH8. 
   apply array_at_ext'. intros. unfold tuchars. unfold ZnthV, cVint. simpl.
      if_tac. omega. destruct (nth_mapVintZ i (text a)) as [? NTH]. trivial. rewrite NTH; simpl. trivial.
assert (KEYOK: array_at tuchar ksh
  (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr (key a))))) 0
  (key_len a) (KEY A) 
   |-- repr_key a ksh (KEY A)).
   unfold repr_key, data_block. rewrite <- HH9. entailer. 
   apply array_at_ext'. intros. unfold tuchars. unfold ZnthV, cVint. simpl.
      if_tac. omega. destruct (nth_mapVintZ i (key a)) as [? NTH]. trivial. rewrite NTH; simpl. trivial.
assert (DigOK: SHA256.SHA_256
     (HMAC_FUN.outerArg
        (SHA256.SHA_256
           (HMAC_FUN.innerArg (text a)
              (map Byte.repr (HMAC_FUN.mkKey (key a)))))
        (map Byte.repr (HMAC_FUN.mkKey (key a))))
    = digest (fst (RefinedHMAC a))).
   unfold RefinedHMAC. rewrite HMAC_Refined.fst_D.
  rewrite (HMAC_Refined.digest_SN7' _
  (HMAC_Refined.snippet6
           (HMAC_Refined.snippet5
              (HMAC_Refined.snippet4
                 (HMAC_Refined.snippet3
                    (HMAC_Refined.snippet2
                       (HMAC_Refined.snippet1
    (HMAC_Refined.initialHmacState
                    (HMAC_Refined.mkArgs (text a) (key a)))))))))).
   rewrite (HMAC_Refined.OuterArgs (text a) (key a)), functional_prog.SHA_256'_eq.
   unfold HMAC_FUN.INNER. rewrite functional_prog.SHA_256'_eq.
   reflexivity.

   rewrite <- HMAC_Refined.SN1. reflexivity.
   unfold HMAC_Refined.mkArgs, HMAC_Refined.initialHmacState, HMAC_Refined.snippet1.
      simpl. rewrite HH9, <- HeqKLENGTH. simpl. rewrite functional_prog.SHA_256'_eq.
      trivial. 
rewrite DigOK. 
cancel.
unfold stackframe_of. remember (64 + text_len a) as tla. simpl.
unfold var_block. simpl. entailer.
  unfold data_block.
unfold tarray in *. rewrite data_at__array_at_; try omega.
  2: unfold legal_alignas_type; trivial.
apply andp_right.
  unfold array_at_, array_at.
  rewrite <- H8, <- H9, <- H10, <- H11, <- H12, <- H13. entailer.
repeat rewrite memory_block_array_tuchar; try omega.
  rewrite <- H8, <- H9, <- H10, <- H11, <- H12, <- H13.
cancel.
rewrite (split_array_at_ 64 _ _ 0 65); try omega. 
rewrite (split_array_at_ 64 _ _ 0 65); try omega. 
cancel.
unfold HMAC_FUN.outerArg, HMAC_FUN.mkArgZ.
rewrite Zlength_correct, app_length, KOPAD_length, <- functional_prog.SHA_256'_eq, length_SHA256'.
assert (HLen: Z.of_nat (64 + Z.to_nat SHA256_DIGEST_LENGTH) = 96). reflexivity.
rewrite HLen. 

unfold HMAC_FUN.innerArg, HMAC_FUN.mkArgZ.
rewrite Zlength_correct, app_length, KIPAD_length. 
assert (HTLA: Z.of_nat (64 + length (text a)) = 64 + text_len a).
    rewrite <- HH8, Zlength_correct. 
    apply Nat2Z.inj_add.
rewrite HTLA.
rewrite (split_array_at_ (64 + text_len a) _ _ 0 1024); try omega. 
rewrite (split_array_at_ 96 _ _ 0 1024); try omega. 
cancel.
rewrite sepcon_comm.

apply sepcon_derives; apply andp_leftV; intros; apply array_at_array_at_; trivial.
Qed.

End HMAC_Part2ImplementationLE. 