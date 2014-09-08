Require Import floyd.proofauto.

Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.HMAC_functional_prog.

Require Import sha.hmac_sha256.

Require Import HMAC_definitions.

Lemma eval_var_rel_expr: forall _x t rho CONT b i n, 0 <= i < 64 -> eval_var _x t rho = Vptr b n -> 
      TT * array_at tuchar Tsh CONT i 64 (Vptr b n) |-- rel_expr (Evar _x t) (Vptr b n) rho.
Proof. intros. admit. Qed.

(*Same proof as semax_loadstore_array*)
Lemma NEWsemax_loadstore_array:
  forall {Espec: OracleKind},
 forall n k vi lo hi t1 (contents: Z -> reptype t1) v1 v2 (Delta: tycontext) e1 ei e2 sh P Q R, 
  (*H0*) reptype t1 = val -> 
  (*H1*) type_is_by_value t1 ->
  (*H2*) legal_alignas_type t1 = true ->
  (*H3*) typeof e1 = tarray t1 k->
  (*H4*) typeof ei = tint ->
  (*H8*) PROPx P (LOCALx Q (SEPx R)) |--  rel_expr e1 v1 && rel_expr ei (Vint (Int.repr vi))
           && rel_expr (Ecast e2 t1) v2 ->
  (*H7*) nth_error R n = Some (`(array_at t1 sh contents lo hi v1)) ->
  (*H *) writable_share sh ->
  (*H5*) tc_val t1 v2 ->
  (*H6*) in_range lo hi vi ->
   @semax Espec Delta (|> PROPx P (LOCALx Q (SEPx R))) (Sassign (Ederef (Ebinop Oadd e1 ei (tptr t1)) t1) e2) 
          (normal_ret_assert 
           (PROPx P (LOCALx Q (SEPx 
            (replace_nth n R `(array_at t1 sh (upd contents vi (valinject _ v2)) lo hi v1)))))).
Proof. 
intros until R.
intros H0 H1 H2 H3 H4 H8 H7 H H5 H6.
eapply semax_post_flipped'.
apply semax_loadstore_array'; eauto.
apply derives_trans with (!! isptr v1 && PROPx P (LOCALx Q (SEPx R))).
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
rewrite array_at_isptr. normalize.
normalize.
destruct v1; try contradiction.
instantiate (2:=v1).
simpl eval_binop. rewrite mul_repr.
apply andp_right; auto.
eapply derives_trans; [ apply H8 |].
intro rho. simpl.
repeat apply andp_right.
apply rel_lvalue_deref.
eapply rel_expr_binop.
repeat apply andp_left1. apply derives_refl.
apply andp_left1. apply andp_left2. apply derives_refl.
intro; rewrite H4; simpl. rewrite H3; simpl. 
  unfold Cop.sem_add; simpl. rewrite mul_repr. auto.
 apply andp_left2. auto.
rewrite (SEP_nth_isolate _ _ _ H7).
repeat rewrite <- insert_SEP.
apply derives_refl.
rewrite (SEP_replace_nth_isolate _ _ _ `(array_at t1 sh (upd contents vi (valinject t1 v2)) lo hi v1) H7).
rewrite insert_SEP.
auto.
Qed.

Lemma loopbody: forall Espec (tsh ksh dsh: share)
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
(KV0 : val)
(h1 : HMAC_Refined.hmacState)
(Heqh1 : h1 = HMAC_Refined.snippet1 h0)
(HeqKLENGTH : true = (key_len a >? 64))
(GT : key_len a > 64)
(H0 : sizes)
(anew : HMAC_Refined.Args)
(Heqanew : anew = args h1)
(HH1 : isPosSigned (key_len a))
(HH2 : KEYLEN A = Vint (Int.repr (key_len a)))
(HH3 : isPosSigned (text_len a))
(HH4 : TEXTLEN A = Vint (Int.repr (text_len a)))
(TL1024 : 64 + text_len a <= 1024)
(HH5 : writable_share ksh)
(HH6 : writable_share dsh)
(HH7 : readable_share tsh)
(HH8 : Zlength (text a) = text_len a)
(HH9 : Zlength (key a) = key_len a)
(TLN : text_len anew = text_len a)
(KLN : key_len anew = 32)
(TN : text anew = text a)
(KN : key anew = functional_prog.SHA_256' (key a))
(TLrange : 0 <= text_len a <= Int.max_unsigned)
(KLrange : 0 <= key_len a <= Int.max_unsigned)
(TKN : tk (locals h1) = functional_prog.SHA_256' (key a))
(ZLenSha : Zlength (tk (locals h1)) = 32)
(isByteKey : Forall isbyteZ (key a))
(isByteShaKey : Forall (fun i : Z => 0 <= i < 256)
                 (functional_prog.SHA_256' (key a)))
(i : Z)
(Delta := func_tycontext f_hmac_sha256 Vprog Gtot)
(H : 0 <= i < 64),
@semax Espec  (initialized _i Delta)
  (PROP  ()
   LOCAL  (`(eq (Vint (Int.repr i))) (eval_id _i);
   `(eq (Vint (Int.repr 64))) (eval_expr (Econst_int (Int.repr 64) tint));
   `(eq (TEXT A)) (eval_id _text); `(eq (tk VALS)) (eval_id _key);
   `(eq KV0) (eval_var sha._K256 (tarray tuint 64));
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
      `(eq KV0) (eval_var sha._K256 (tarray tuint 64));
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
     simple eapply semax_seq'.

eapply semax_pre0; [ apply now_later | ].

eapply semax_post_flipped'.
   eapply NEWsemax_loadstore_array. 
     reflexivity. trivial. reflexivity. reflexivity.  reflexivity.
     entailer; repeat instantiate_Vptr.
 destruct (k_ipad VALS) eqn:?Hipad; try contradiction.
 rewrite <- Hipad in *.
*  
 repeat apply andp_right; rel_expr. 
  intro; simpl. rewrite <- H1. rewrite Hipad. reflexivity.
  simpl typeof.

works up to here.

     Focus 2. instantiate (1:=k_ipad VALS). instantiate (1:=64). instantiate (1:=i).
              instantiate (1:=KKEY). instantiate (1:=Tsh). instantiate (1:=1%nat). simpl. reflexivity.
     2: apply writable_share_top.
     Focus 3. instantiate (1:=i). unfold in_range. omega.
  match goal with |- ?PQR  |-- _ =>
       apply derives_trans with
       (PQR
   && (TT * `(array_at tuchar Tsh KKEY i 64 (k_ipad VALS)&& !!isptr (k_ipad VALS))))
   end.
(*     && (TT * `(array_at tuchar Tsh (Vfloat oo fz) 0 n z))))
  end.*)
  apply andp_right; auto. 
    rewrite (array_at_isptr tuchar _ _ _ 64 (k_ipad VALS)). entailer. cancel.
  normalize. rename H1 into isPtr_Ipad.
  remember (k_ipad VALS) as v. destruct v; try contradiction.
  clear Heqv isPtr_Ipad.
  apply andp_right.
  go_lowerx. normalize.
  apply andp_left2.
  (*subst. repeat instantiate_Vptr.*)
  apply andp_right.
    apply eval_var_rel_expr. trivial. rewrite <- H10; trivial.
    rel_expr.
  go_lowerx. normalize.
  apply andp_left2. 
    entailer. rel_expr. apply rel_expr'_cast.
    rel_expr.
 unfold eval_var in H.
  remember (Map.get (ve_of rho) _x) as d; destruct d; inv H. destruct p.
  remember (eqb_type t t0) as bb.
  destruct bb; inv H1; apply eq_sym in Heqbb.
    apply eqb_type_spec in Heqbb. subst t. apply eq_sym in Heqd. go_lower.  rel_expr. instantiate (1:=b). unfold seplog.prop. rewrite Heqd. normalize. simpl. entailer.
         simpl. instantiate (1:=Tsh).
   
 admit.
  rel_expr.
  rel_expr.
    rewrite <- H10. remember ( (cVint
     (force_int
      oo ZnthV tuchar
           (map Vint
              (map Int.repr
                 (map Byte.unsigned (map Byte.repr (HMAC_FUN.mkKey (key a))))))))) as CONTENT.
assert (tarray tuchar 65 = tptr tuchar). admit. rewrite H6.
clear - H10. Print rel_expr'.
SearchAbout eval_var.
assert (). 
 rel_expr. 
       unfold eval_var in H10. remember (Map.get (ve_of rho) _k_ipad) as d. destruct d.
         destruct p. remember (eqb_type (tarray tuchar 65) t) as bb.
         destruct bb; inv H10; apply eq_sym in Heqbb.
         apply eqb_type_spec in Heqbb. subst t. apply eq_sym in Heqd.  rel_expr. instantiate (1:=b0). entailer.
         simpl. instantiate (1:=Tsh).
         rewrite (split3_array_at' Z0 tuchar Tsh _ i _ (Vptr b0 Int.zero)(Vptr b0 Int.zero)).
SearchAbout mapsto.
         unfold add_ptr_int; simpl. rewrite Int.add_zero. Focus 2. admit.   rel_expr.
SearchAbout mapsto array_at.
Print rel_expr'. unfold Evar.
  rel_expr.
  rel_expr.
  simple eapply rel_expr_cast; [ | try (simpl; rewrite_eval_id; reflexivity) ].
  simple eapply rel_expr_binop; [ |  | ].
  apply andp_left1. rel_expr.
  apply andp_left2. rel_expr.
  reflexivity.
  reflexivity.

rewrite (array_at_isptr tuchar _ _ _ 64 (k_ipad VALS)).
rewrite (array_at_isptr tuchar _ _ _ 64 (k_opad VALS)).
  go_lowerx. normalize.
  repeat instantiate_Vptr; repeat apply andp_right.
      destruct (k_ipad VALS); try contradiction. rewrite H10.
       unfold eval_var in H10. remember (Map.get (ve_of rho) _k_ipad) as d. destruct d.
         destruct p. remember (eqb_type (tarray tuchar 65) t) as bb.
         destruct bb; inv H10; apply eq_sym in Heqbb.
         apply eqb_type_spec in Heqbb. subst t. apply eq_sym in Heqd.  rel_expr. instantiate (1:=b0). entailer.
         simpl. instantiate (1:=Tsh). entailer.
         rewrite (split3_array_at' i tuchar Tsh _ i _ (eval_var _k_ipad (tarray tuchar 65) rho) (eval_var _k_ipad (tarray tuchar 65) rho)).
         unfold add_ptr_int; simpl. Focus 2. admit. 
  destruct (k_opad VALS); try contradiction.
  repeat instantiate_Vptr; repeat apply andp_right.
     instantiate (1:=k_ipad VALS). rewrite H10. clear - H10. unfold eval_var in H10. rel_expr. repeat instantiate_Vptr; repeat apply andp_right.
  rel_expr. rel_expr. admit.array_at_local_facts
                        instantiate (1:=i). rel_expr. admit.
     Focus 5. simpl. reflexivity. Locate semax_loadstore_array'. 2: reflexivity. 2: trivial. 2: reflexivity.
     Focus 4. apply andp_right.  
                apply andp_right.

SearchAbout rel_lvalue. rel_expr.
          instantiate (1:= i). instantiate (1:= k_ipad VALS). rel_expr.
eauto.
                  apply rel_expr_array_load. reflexivity 
     hoist_later_in_pre.
     simple eapply semax_seq'.
   eapply semax_loadstore_array.
   simple eapply (semax_loadstore_array sx);
      remember (Ederef
        (Ebinop Oadd (Evar _k_ipad (tarray tuchar 65)) (Etempvar _i tint)
           (tptr tuchar)) tuchar) as e1.
        eapply semax_loadstore_array'.
assert (typeof e1 = tuchar). subst e1. simpl. reflexivity.
      remember (Ederef
        (Ebinop Oadd (Evar _k_ipad (tptr tuchar)) (Etempvar _i tint)
           (tptr tuchar)) tuchar) as e1'.
assert (typeof e1' = tuchar). subst e1'. simpl. reflexivity.
          reflexivity. apply I. reflexivity.
        Focus 8. entailer. 
          repeat apply andp_right. 
         (*rel_expr (Evar _k_ipad (tarray tuchar 65)) ?7539 rho*)
          Focus 2. eapply rel_expr_cast.
                   eapply rel_expr_binop.
          instantiate (1:= k_ipad VALS). rel_expr. unfold eval_var in H7.
          Focus 2. rel_expr.
          Focus 2. eapply rel_expr_cast.
                   eapply rel_expr_binop. 
                   (* rel_expr
(*        eapply semax_loadstore_array.?*)
          reflexivity. apply I. reflexivity. admit. (*TODO tarray/tptr*)
          reflexivity. 
        entailer. 
          repeat apply andp_right. 
         (*rel_expr (Evar _k_ipad (tarray tuchar 65)) ?7539 rho*)
          instantiate (1:= k_ipad VALS). rel_expr. unfold eval_var in H7.
          Focus 2. rel_expr.
          Focus 2. eapply rel_expr_cast.
                   eapply rel_expr_binop. 
                   (* rel_expr
      (Ederef
         (Ebinop *)
                  Focus 2. rel_expr. 
                  Focus 2. simpl. eapply rel_expr_deref.
                  rel_expr. auto.
                apply andp_right. 
SearchAbout rel_lvalue. rel_expr. 
           eapply rel_expr_array_load'.
       reflexivity. apply I. reflexivity.
     simple eapply semax_loadstore_array.
       reflexivity. apply I. reflexivity.
       unfold tarray; simpl. admit. (*TODO: refine Lemma semax_loadstore_array' in array_lemmas.v*)
       reflexivity.
     *)*)
