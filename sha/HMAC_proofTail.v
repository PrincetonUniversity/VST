Require Import floyd.proofauto.

Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.

Require Import sha.HMAC_functional_prog.

Require Import sha.hmac_sha256.

Require Import HMAC_definitions.
(*Require Import HMAC_part2LE. this file contains the implementation for the path key_len <= 64*)
(*Require Import HMAC_part2GT. this file contains the implementation for the path key_len > 64*)

Declare Module PART2LE: HMAC_PART2LE.

Definition restLE := PART2LE.HMAC_LE.

Lemma hmac_LE_tail Espec tsh ksh dsh: forall
(A : ARGS)
(a : HMAC_Refined.Args)
(KV : val)
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
(HH1 : 0 <= key_len a < Int.max_signed)
(HH2 : KEYLEN A = Vint (Int.repr (key_len a)))
(HH3 : isPosSigned (text_len a))
(HH4 : TEXTLEN A = Vint (Int.repr (text_len a)))
(TL1024 : 64 + text_len a <= 1024)
(HH5 : writable_share ksh)
(HH6 : writable_share dsh)
(HH7 : readable_share tsh)
(HH8 : Zlength (text a) = text_len a)
(HH9 : Zlength (key a) = key_len a)
(TLrange : 0 <= text_len a <= Int.max_unsigned)
(KLrange : 0 <= key_len a <= Int.max_unsigned)
(isByteKey : Forall isbyteZ (key a))
(Delta := func_tycontext f_hmac_sha256 Vprog Gtot)
(*POSTCONDITION := abbreviate : ret_assert
MORE_COMMANDS := abbreviate : statement*)
(LK : (length (key a) <= 64)%nat),
@semax Espec (initialized _i Delta)
  (PROP  ()
   LOCAL  (`(eq (Vint (Int.repr 64))) `(Vint (Int.repr 64));
   `(eq (TEXT A)) (eval_id _text); `(eq (KEY A)) (eval_id _key);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64));
   `(eq (TEXTLEN A)) (eval_id _text_len);
   `(eq (KEYLEN A)) (eval_id _key_len); `(eq (DIGEST A)) (eval_id _digest);
   `(eq (k_ipad VALS)) (eval_var _k_ipad (tarray tuchar 65));
   `(eq (k_opad VALS)) (eval_var _k_opad (tarray tuchar 65));
   `(eq (tk VALS)) (eval_var _tk (tarray tuchar 32));
   `(eq (tk2 VALS)) (eval_var _tk2 (tarray tuchar 32));
   `(eq (bufferIn VALS)) (eval_var _bufferIn (tarray tuchar 1024));
   `(eq (bufferOut VALS)) (eval_var _bufferOut (tarray tuchar 1024)))
   SEP 
   (`(!!isptr (k_opad VALS) && !!offset_in_range 64 (k_opad VALS) &&
      !!align_compatible tuchar (k_opad VALS) && emp);
   `(!!isptr (k_ipad VALS) && !!offset_in_range 64 (k_ipad VALS) &&
     !!align_compatible tuchar (k_ipad VALS) && emp);
   `(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 64 65 (k_opad VALS));
   `(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 64 65 (k_ipad VALS));
   `(array_at tuchar Tsh
       (cVint
          (force_int
           oo ZnthV tuchar
                (map Vint
                   (map Int.repr
                      (map Byte.unsigned
                         (HMAC_FUN.mkArg
                            (map Byte.repr (HMAC_FUN.mkKey (key a))) Opad))))))
       0 64 (k_opad VALS));
   `(array_at tuchar Tsh
       (cVint
          (force_int
           oo ZnthV tuchar
                (map Vint
                   (map Int.repr
                      (map Byte.unsigned
                         (HMAC_FUN.mkArg
                            (map Byte.repr (HMAC_FUN.mkKey (key a))) Ipad))))))
       0 64 (k_ipad VALS));
   `(array_at tuchar ksh
       (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr (key a)))))
       0 (key_len a) (KEY A)); `(data_at_ Tsh (tarray tuchar 32) (tk VALS));
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
                             Etempvar _digest (tptr tvoid)]) (Sreturn None)))))))))
  (frame_ret_assert
     (function_body_ret_assert tvoid
        SEP  (`(K_vector KV); `(repr_key a ksh (KEY A));
        `(repr_text a tsh (TEXT A));
        `(repr_digest false (fst (RefinedHMAC a)) dsh (DIGEST A))))
     (stackframe_of f_hmac_sha256)).
Proof. intros. 

(*THIS IS THE STEP THAT RUNS OUT OF MEMORY IN HMAC_proof.v*)
normalize. (*WHY are the two `emp terms not eliminated here???*)

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
  remember (force_int oo ZnthV tuchar (map Vint (map Int.repr (key a)))) as KKEY. 
 remember (fun _ : Z => Vint Int.zero) as ZERO.
 normalize. 

 eapply restLE; eassumption.
Qed.