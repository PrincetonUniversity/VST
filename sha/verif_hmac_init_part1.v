Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.

Require Import sha.hmac091c.
Require Import sha.HMAC_lemmas.
Require Import sha.spec_hmac.

Definition initPostKeyNullConditional r (c:val) (k: val) h key : mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 then hmacstate_PreInitNull key h c else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF 
                  else !!(Forall isbyteZ key) &&
                    ((data_at Tsh t_struct_hmac_ctx_st (keyedHMS key) c) *
                    (array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
                      (Vptr b ofs)))
  | _ => FF
  end.

Lemma hmac_init_part1: forall
(Espec : OracleKind)
(c : val)
(k : val)
(l : Z)
(key : list Z)
(KV : val)
(h1:hmacabs)
(KL1 : l = Zlength key)
(KL2 : 0 <= l <= Int.max_signed)
(KL3 : l * 8 < two_p 64)
(ctx' : name _ctx)
(key' : name _key)
(len' : name _len)
(Delta := (initialized _reset 
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs)))
(PostKeyNull : environ -> mpred)
(HeqPostKeyNull : PostKeyNull =
                 EX  cb : block,
                 (EX  cofs : int,
                  (EX  pad : val,
                   (EX  r : Z,
                    PROP  (c = Vptr cb cofs /\ (r=0 \/ r=1))
                    LOCAL  (`(eq (Vint (Int.repr r))) (eval_id _reset);
                    `(eq pad) (eval_var _pad (tarray tuchar 64));
                    `(eq c) (eval_id _ctx); `(eq k) (eval_id _key);
                    `(eq (Vint (Int.repr l))) (eval_id _len);
                    `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
                    SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                    `(initPostKeyNullConditional r c k h1 key);
                    `(K_vector KV)))))),
@semax Espec Delta
  (PROP  ()
   LOCAL  (`(eq (Vint (Int.repr 0))) (eval_id _reset);
   `(eq c) (eval_id _ctx); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(data_at_ Tsh (tarray tuchar 64)) (eval_var _pad (tarray tuchar 64));
   `(K_vector KV); `(initPre c k h1 key)))
     (Sifthenelse
        (Ebinop One (Etempvar _key (tptr tuchar))
           (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
        (Ssequence (Sset _reset (Econst_int (Int.repr 1) tint))
           (Ssequence (Sset _j (Econst_int (Int.repr 64) tint))
              (Sifthenelse
                 (Ebinop Olt (Etempvar _j tint) (Etempvar _len tint) tint)
                 (Ssequence
                    (Scall None
                       (Evar _SHA256_Init
                          (Tfunction
                             (Tcons (tptr t_struct_SHA256state_st) Tnil)
                             tvoid cc_default))
                       [Eaddrof
                          (Efield
                             (Ederef
                                (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                                t_struct_hmac_ctx_st) _md_ctx
                             t_struct_SHA256state_st)
                          (tptr t_struct_SHA256state_st)])
                    (Ssequence
                       (Scall None
                          (Evar _SHA256_Update
                             (Tfunction
                                (Tcons (tptr t_struct_SHA256state_st)
                                   (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                tvoid cc_default))
                          [Eaddrof
                             (Efield
                                (Ederef
                                   (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                                   t_struct_hmac_ctx_st) _md_ctx
                                t_struct_SHA256state_st)
                             (tptr t_struct_SHA256state_st);
                          Etempvar _key (tptr tuchar); Etempvar _len tint])
                       (Ssequence
                          (Scall None
                             (Evar _SHA256_Final
                                (Tfunction
                                   (Tcons (tptr tuchar)
                                      (Tcons (tptr t_struct_SHA256state_st)
                                         Tnil)) tvoid cc_default))
                             [Efield
                                (Ederef
                                   (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                                   t_struct_hmac_ctx_st) _key
                                (tarray tuchar 64);
                             Eaddrof
                               (Efield
                                  (Ederef
                                     (Etempvar _ctx
                                        (tptr t_struct_hmac_ctx_st))
                                     t_struct_hmac_ctx_st) _md_ctx
                                  t_struct_SHA256state_st)
                               (tptr t_struct_SHA256state_st)])
                          (Ssequence
                             (Scall None
                                (Evar _memset
                                   (Tfunction
                                      (Tcons (tptr tvoid)
                                         (Tcons tint (Tcons tuint Tnil)))
                                      (tptr tvoid) cc_default))
                                [Eaddrof
                                   (Ederef
                                      (Ebinop Oadd
                                         (Efield
                                            (Ederef
                                               (Etempvar _ctx
                                                  (tptr t_struct_hmac_ctx_st))
                                               t_struct_hmac_ctx_st) _key
                                            (tarray tuchar 64))
                                         (Econst_int (Int.repr 32) tint)
                                         (tptr tuchar)) tuchar) (tptr tuchar);
                                Econst_int (Int.repr 0) tint;
                                Econst_int (Int.repr 32) tint])
                             (Sassign
                                (Efield
                                   (Ederef
                                      (Etempvar _ctx
                                         (tptr t_struct_hmac_ctx_st))
                                      t_struct_hmac_ctx_st) _key_length tuint)
                                (Econst_int (Int.repr 32) tint))))))
                 (Ssequence
                    (Scall None
                       (Evar _memcpy
                          (Tfunction
                             (Tcons (tptr tvoid)
                                (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                             (tptr tvoid) cc_default))
                       [Efield
                          (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                             t_struct_hmac_ctx_st) _key (tarray tuchar 64);
                       Etempvar _key (tptr tuchar); Etempvar _len tint])
                    (Ssequence
                       (Scall None
                          (Evar _memset
                             (Tfunction
                                (Tcons (tptr tvoid)
                                   (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                          [Eaddrof
                             (Ederef
                                (Ebinop Oadd
                                   (Efield
                                      (Ederef
                                         (Etempvar _ctx
                                            (tptr t_struct_hmac_ctx_st))
                                         t_struct_hmac_ctx_st) _key
                                      (tarray tuchar 64))
                                   (Etempvar _len tint) (tptr tuchar)) tuchar)
                             (tptr tuchar); Econst_int (Int.repr 0) tint;
                          Ebinop Osub (Econst_int (Int.repr 64) tuint)
                            (Etempvar _len tint) tuint])
                       (Sassign
                          (Efield
                             (Ederef
                                (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                                t_struct_hmac_ctx_st) _key_length tuint)
                          (Etempvar _len tint))))))) Sskip)
  (normal_ret_assert PostKeyNull).
Proof. intros. subst Delta. abbreviate_semax.
forward_if PostKeyNull.
  { (* THEN*)
    simpl. 
    unfold force_val2, force_val1; simpl. 
    eapply semax_pre with (P':= EX cb:_, EX cofs:_, EX kb:_, EX kofs:_, EX pad:_,
      (PROP  (c=Vptr cb cofs /\ k=Vptr kb kofs /\ Forall isbyteZ key)
       LOCAL 
         (`(eq (Vint (Int.repr 0))) (eval_id _reset);
          `(eq pad) (eval_var _pad (tarray tuchar 64)); `(eq c) (eval_id _ctx);
          `(eq k) (eval_id _key); `(eq (Vint (Int.repr l))) (eval_id _len);
          `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
      SEP  (
          `(data_at_ Tsh (tarray tuchar 64) pad);
          `(data_at_ Tsh t_struct_hmac_ctx_st (Vptr cb cofs));
          `(K_vector KV);
          `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) k)))).
      entailer.
      destruct key'; try contradiction.
      (*key' is integer, ie Null*)
        simpl in *. subst i. unfold Int.zero in *. simpl in *.
        unfold Vfalse in H0. inversion H0.
      (*key' is ptr*)
        simpl in *. rewrite (data_at__isptr _ t_struct_hmac_ctx_st). 
        entailer. apply isptrD in Pctx'. destruct Pctx' as [cb [cofs CB]]. subst ctx'.
        apply exp_right with (x:=cb).
        apply exp_right with (x:=cofs).
        apply exp_right with (x:=b).
        apply exp_right with (x:=i).
        apply exp_right with (x:=eval_var _pad (tarray tuchar 64) rho).
        entailer. cancel.
        unfold data_block. entailer.
    apply extract_exists_pre. intros cb. 
    apply extract_exists_pre. intros cofs.  
    apply extract_exists_pre. intros kb. 
    apply extract_exists_pre. intros kofs.  
    apply extract_exists_pre. intros pad.  
    normalize. subst c k. rename H1 into isbyte_key. (*subst PostKeyNull.*)

    forward. (*reset =1 *) (*qinxiang: here, forward now intoduces an essentially 
      unnecessary x:val, together with a term `(eq (Vint (Int.repr 0))) `x; in LOCAL*) 
    forward. (*j=HMAC_MAX_MD_CBLOCK*)
    simpl.

    remember
     (PROP  ()
      LOCAL  (
       `(eq (Vint (Int.repr 1))) (eval_id _reset);
       `(eq pad) (eval_var _pad (tarray tuchar 64)); `(eq (Vptr cb cofs)) (eval_id _ctx);
       `(eq (Vptr kb kofs)) (eval_id _key); `(eq (Vint (Int.repr l))) (eval_id _len);
       `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
      SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
            `(data_at Tsh t_struct_hmac_ctx_st (keyedHMS key) (Vptr cb cofs));
           `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
             (Vptr kb kofs));
          `(K_vector KV))) as PostIf_j_Len.

    forward_if PostIf_j_Len. 
    { (* j < len*)
      eapply semax_pre with (P':=
       (PROP  (64 < l)
        LOCAL 
         (`(eq (Vint (Int.repr 64))) (eval_id _j);
          `eq (eval_id _reset) `(Vint (Int.repr 1));
          `(eq pad) (eval_var _pad (tarray tuchar 64)); `(eq (Vptr cb cofs)) (eval_id _ctx);
          `(eq (Vptr kb kofs)) (eval_id _key); `(eq (Vint (Int.repr l))) (eval_id _len);
          `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
        SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
              `(data_at_ Tsh t_struct_hmac_ctx_st (Vptr cb cofs));
              `(K_vector KV);
              `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) (Vptr kb kofs))))).
        entailer. 
      normalize. rename H into lt_64_l.
      clear x. (*here's where we can finally eliminate the spurious x*) 

      (*call to SHA256_init*)
      eapply semax_seq'.
      frame_SEP 1.
      unfold data_at_.
      unfold_data_at 1%nat.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_md_ctx]); try reflexivity.
      normalize. 
      rename H into SCc. rename H0 into ACc.
      (*rewrite isptr_c; simpl.*)
      (*rewrite at_offset'_eq.
      2: rewrite isptr_c; simpl; rewrite Int.add_zero; reflexivity.*)
      forward_call (Vptr cb cofs). 
      { assert (FR: Frame = [
        `(field_at Tsh t_struct_hmac_ctx_st [_key_length] Vundef (Vptr cb cofs));
        `(field_at Tsh t_struct_hmac_ctx_st [_key] [] (Vptr cb cofs));
        `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx]
               ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
        `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx]
             ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs))]).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.   
       entailer. cancel. 
      } 
      after_call.
      normalize. simpl. normalize.

      (*call to SHA256_Update*)
      erewrite (split_offset_array_at _ _ _ 0 l); try reflexivity. 2: subst l; omega.
      normalize. (*
      rewrite isptr_k in H, H0. *) simpl in H, H0. rewrite Zplus_0_r in H.
      rename H into OIR_kofs. rename H0 into OIR_kofs_key.
      eapply semax_seq'.
      frame_SEP 8 0 2.
      remember (init_s256abs, key, Vptr cb cofs,
                Vptr kb kofs, Tsh, l, KV) as WITNESS.
      forward_call WITNESS.
      { assert (FR: Frame = []).
          subst Frame. reflexivity.
        rewrite FR. clear FR Frame.   
        subst WITNESS. entailer.
        apply andp_right.
           apply prop_right. 
             rewrite int_max_signed_eq in KL2. 
             rewrite int_max_unsigned_eq; omega.
        cancel. unfold data_block. 
          simpl. (*not doing this simpl results in a coq anomaly in entailer, and and_pright is not applicable*)
          apply andp_right. entailer. cancel. 
      } 
      after_call. subst WITNESS. simpl. intros rho. normalize. simpl.

     (*commute fun a => and EX x*)
     apply semax_pre with (P':=
      EX  xx : s256abs,
  (PROP  ()
   LOCAL  (tc_environ Delta; 
   `(eq (Vint (Int.repr 64))) (eval_id _j);
   `(eq (Vint (Int.repr 1))) (eval_id _reset);
   `(eq pad) (eval_var _pad (tarray tuchar 64));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(fun a : environ =>
      (PROP  (update_abs (firstn (Z.to_nat l) key) init_s256abs xx)
       LOCAL ()
       SEP  (`(K_vector KV); `(sha256state_ xx (Vptr cb cofs));
       `(data_block Tsh key (Vptr kb kofs)))) a) globals_only;
   `(array_at tuchar Tsh (fun i : Z => tuchars (map Int.repr key) (i + l)) 0
       (Zlength key - l) (Vptr kb (Int.add kofs (Int.repr l))));
   `(field_at Tsh t_struct_hmac_ctx_st [_key_length] Vundef (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_key] [] (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx]
       ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx]
       ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
   `(data_at_ Tsh (tarray tuchar 64) pad)))).
       entailer. rename x into a. apply (exp_right a).
       entailer.
   apply extract_exists_pre. intros ctxSha. simpl. normalize. simpl.

   (*call Final*)
   rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
   normalize. 
   rewrite at_offset'_eq.
     2: simpl; rewrite Int.add_zero; reflexivity.
   unfold nested_field_offset2, nested_field_type2; simpl.
   unfold tarray.
   erewrite (data_at_array_at Tsh tuchar 64 noattr []).
     2: apply JMeq.JMeq_refl. 
     2: omega.
     2: reflexivity. 
   erewrite (split_offset_array_at _ _ _ 0 32 64); try reflexivity. 2: omega.
   normalize.
   eapply semax_seq'.
   frame_SEP 2 3 0.
   remember (ctxSha, Vptr cb (Int.add cofs (Int.repr 328)),
             Vptr cb cofs, Tsh, Tsh, KV) as WITNESS.
   forward_call WITNESS.
     { assert (FR: Frame = []).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.   
       subst WITNESS. entailer. cancel.
       rewrite memory_block_array_tuchar'. cancel. trivial. omega.
     }
     after_call. subst WITNESS. simpl. intros rho. normalize. simpl. normalize. simpl.

   (*call memset*)
   (* doing this: eapply semax_seq'. frame_SEP 3. requires us to do the swap fun a=> vs EX
      after the call, which leaves a state that still doesn't nicely normalize *)
   remember (Tsh, Vptr cb (Int.add cofs (Int.repr 360)), 32, Int.zero) as WITNESS.
   forward_call WITNESS.
     { assert (FR: Frame = [`(K_vector KV);
         `(data_at_ Tsh sha.t_struct_SHA256state_st (Vptr cb cofs));
         `(data_block Tsh (sha_finish ctxSha) (Vptr cb (Int.add cofs (Int.repr 328))));
         `(data_block Tsh key (Vptr kb kofs));
         `(array_at tuchar Tsh (fun i : Z => tuchars (map Int.repr key) (i + l)) 0
              (Zlength key - l) (offset_val (Int.repr l) (Vptr kb kofs)));
         `(field_at Tsh t_struct_hmac_ctx_st [_key_length] Vundef (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx]
              ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx]
              ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
(*         `(data_at_ Tsh t_struct_SHA256state_st sha);*)
         `(data_at_ Tsh (Tarray tuchar 64 noattr) pad)]).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.   
       entailer. cancel. 
       rewrite memory_block_array_tuchar'. cancel. trivial. omega.
     } 
     after_call. subst WITNESS. normalize. subst retval0. 
   (*swap fun a=> with EX
   apply semax_pre with (P':=
    EX  x : val,
  (PROP  ()
   LOCAL  (tc_environ Delta; tc_environ Delta; tc_environ Delta;
   tc_environ Delta; `(eq (Vint (Int.repr 1))) (eval_id _reset);
   `(eq sha) (eval_var _sha_ctx t_struct_SHA256state_st);
   `(eq pad) (eval_var _pad (Tarray tuchar 64 noattr));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq KV) (eval_var sha._K256 (Tarray tuint 64 noattr)))
   SEP 
   (fun a : environ =>
    `(fun x0 : environ =>
      local (`(eq (Vptr cb (Int.add cofs (Int.repr 360)))) retval) x0 &&
      `(array_at tuchar Tsh (fun _ : Z => Vint Int.zero) 0 32
          (Vptr cb (Int.add cofs (Int.repr 360)))) x0)
      (fun rho : environ => env_set (globals_only rho) ret_temp x) a;
   `(K_vector KV);
   `(data_at_ Tsh sha.t_struct_SHA256state_st (Vptr cb cofs));
   `(data_block Tsh (sha_finish mdSha)
       (Vptr cb (Int.add cofs (Int.repr 328))));
   `(data_block Tsh key (Vptr kb kofs));
   `(array_at tuchar Tsh (fun i : Z => tuchars (map Int.repr key) (i + l)) 0
       (Zlength key - l) (offset_val (Int.repr l) k));
   `(field_at Tsh t_struct_hmac_ctx_st [_key_length] Vundef (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx]
       ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx]
       ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
   `(data_at_ Tsh t_struct_SHA256state_st sha);
   `(data_at_ Tsh (Tarray tuchar 64 noattr) pad)))).
    entailer.
    apply exp_right with (x:=Vptr cb (Int.add cofs (Int.repr 360))).
    entailer.
   apply extract_exists_pre. intros x. simpl. normalize.
     unfold local. simpl. red. normalize.*)

   forward. (*ctx->key_length=32*)

   subst PostIf_j_Len.
   entailer. 
   cancel.
   unfold data_block. entailer. cancel. 
   unfold data_at_.
   destruct (zlt 64 (Zlength key)). 2: omega.
   unfold_data_at 2%nat.
   cancel. 
   rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
     entailer.
     rewrite at_offset'_eq.
     2: simpl; rewrite Int.add_zero; reflexivity.
     unfold nested_field_offset2, nested_field_type2; simpl.
     unfold tarray.
     erewrite (data_at_array_at Tsh tuchar 64 noattr).
     2: apply JMeq.JMeq_refl. 
     2: omega.
     2: reflexivity. 
     erewrite (split_offset_array_at _ _ _ 0 32 64); try reflexivity. 2: omega.
     entailer. unfold offset_val. rewrite Int.add_assoc.
        assert (I360: Int.add (Int.repr 328) (Int.repr 32) = Int.repr 360).
          reflexivity. 
        rewrite I360; clear I360.  simpl.
     assert (LengthShaFinish: Zlength (sha_finish ctxSha) = 32).
                 unfold sha_finish. destruct ctxSha.
        rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'. reflexivity.
     rewrite array_at_ext with (f':= fun i : Z =>
         ZnthV tuchar (map Vint (map Int.repr (HMAC_FUN.mkKey key))) (i + 32)).
     Focus 2. intros. unfold ZnthV. if_tac. omega.
              assert (Z32: (Z.to_nat i < 32)%nat).
                  clear - H7; destruct H7 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
                  apply YY. omega. omega.
               unfold HMAC_FUN.mkKey. simpl.
               assert (Kgt: Zlength key > 64) by omega.
               apply Zgt_is_gt_bool in Kgt.
               rewrite Kgt. unfold HMAC_FUN.zeroPad. repeat rewrite map_app.
               rewrite app_nth2; repeat rewrite map_length; rewrite length_SHA256'.
                 remember (Nlist 0 (SHA256_BlockSize - Z.to_nat SHA256_DIGEST_LENGTH)) as NL.
                 simpl.
                 assert (I: (Z.to_nat (i + 32) - 32)%nat = Z.to_nat i).
                             destruct H7. specialize (Z2Nat.inj_sub (i+32) 32).
                             simpl; intros HH. rewrite <- HH, Zplus_comm, Zminus_plus. trivial.
                             omega. 
                 rewrite I. subst NL. 
                 assert (SHA32: (SHA256_BlockSize - Z.to_nat SHA256_DIGEST_LENGTH)%nat = 32%nat) by reflexivity.
                 rewrite SHA32.
                 rewrite nth_map' with (d':=Int.zero).
                   rewrite nth_map' with (d':=Z0).
                     rewrite nth_Nlist; trivial.
                     rewrite length_Nlist; trivial.
                   rewrite  map_length, length_Nlist; trivial.
                 apply (Z2Nat.inj_le 32 (i + 32)); omega.

     cancel.
     rewrite LengthShaFinish.
     rewrite array_at_ext with (f':=ZnthV tuchar (map Vint (map Int.repr (HMAC_FUN.mkKey key)))).
     Focus 2. unfold tuchars, sha_finish; intros. destruct ctxSha. simpl.
              assert (Z32: (Z.to_nat i < 32)%nat).
                  clear - H7; destruct H7 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
                  apply YY. omega. omega.    
              unfold ZnthV. destruct (zlt i 0). omega.   
              rewrite nth_map' with (d':=Int.zero). rewrite nth_map' with (d':=Z0). 
              rewrite nth_map' with (d':=Int.zero). rewrite nth_map' with (d':=Z0). 
              f_equal. f_equal. unfold HMAC_FUN.mkKey. simpl. 
              assert (Z6: Zlength key > 64) by omega. 
              apply Zgt_is_gt_bool in Z6; rewrite Z6.
              unfold HMAC_FUN.zeroPad.
              rewrite <- functional_prog.SHA_256'_eq.
              rewrite app_nth1. inversion H. subst. clear H. simpl in *.
                      rewrite <- H17. rewrite firstn_precise. trivial.
                      rewrite Zlength_correct, Nat2Z.id; trivial.
              rewrite length_SHA256'; trivial.
              rewrite mkKey_length; unfold SHA256_BlockSize; simpl. omega.
              rewrite map_length, mkKey_length; unfold SHA256_BlockSize; simpl. omega.
              rewrite <- functional_prog.SHA_256'_eq, length_SHA256'. trivial.
              rewrite map_length, <- functional_prog.SHA_256'_eq, length_SHA256'. trivial. 
     cancel.
   rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_md_ctx]); try reflexivity.
     normalize. 
     rewrite at_offset'_eq.
     2: simpl; rewrite Int.add_zero; reflexivity.
     unfold nested_field_offset2, nested_field_type2; simpl. rewrite Int.add_zero.
     cancel. rewrite <- Zminus_diag_reverse. rewrite array_at_emp. normalize.
     destruct (zlt 64 (Zlength key)). trivial. omega.
   } 

   { (* j >= len*)
     eapply semax_pre with (P':=
       (PROP  (64 >= l)
        LOCAL 
         (`(eq (Vint (Int.repr 64))) (eval_id _j);
          `eq (eval_id _reset) `(Vint (Int.repr 1));
          `(eq pad) (eval_var _pad (tarray tuchar 64)); `(eq (Vptr cb cofs)) (eval_id _ctx);
          `(eq (Vptr kb kofs)) (eval_id _key); `(eq (Vint (Int.repr l))) (eval_id _len);
          `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
        SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
              `(data_at Tsh t_struct_hmac_ctx_st (default_val t_struct_hmac_ctx_st) (Vptr cb cofs));
              `(K_vector KV);
              `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) (Vptr kb kofs))))).
        entailer. 
     normalize. rename H into ge_64_l. 
     clear x. (*again, remove spurious x*)

     (*call to memcpy*)
     (*eapply semax_seq'.*)
     focus_SEP 1 3.
     (*unfold data_at_. *)
     unfold_data_at 1%nat.
     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
     normalize. 
     rename H into SCc. rename H0 into ACc.
     (*rewrite isptr_c;*) simpl.
     rewrite at_offset_data_at. unfold nested_field_type2, nested_field_offset2; simpl.
     unfold tarray.
     erewrite data_at_array_at. 2: apply JMeq.JMeq_refl. 2: omega. 2: reflexivity.
     erewrite (split_offset_array_at _ _ _ 0 l 64); try reflexivity. 2: omega.
     normalize.
     rename H into OIR0_328. rename H0 into OIR64_328.

     unfold tuchars. remember (64 - l) as l64.
     remember ((Tsh, Tsh), Vptr cb (Int.add cofs (Int.repr 328)), 
             Vptr kb kofs, mkTrep (Tarray tuchar (Zlength key) noattr) 
                     (map Vint (map Int.repr key))) as WITNESS.
     forward_call WITNESS.
     { assert (FR: Frame = [
        `(array_at tuchar Tsh (fun i : Z => ZnthV tuchar [] (i + l)) 0 l64
            (offset_val (Int.repr l) (Vptr cb (Int.add cofs (Int.repr 328)))));
        `(field_at Tsh t_struct_hmac_ctx_st [_key_length] Vundef (Vptr cb cofs));
        `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx]
            ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
        `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx]
            ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
        `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx]
            ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
        `(data_at_ Tsh (Tarray tuchar 64 noattr) pad);
        (*`(array_at tuchar Tsh (ZnthV tuchar []) 0 64 pad);*)
        `(K_vector KV)]).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.   
       subst WITNESS. entailer.
         rewrite Zlength_max_zero.
         assert (HH: match Zlength key with
                     | 0 => 0
                     | Z.pos y' => Z.pos y'
                     | Z.neg y' => Z.neg y'
                 end = Zlength key).
            destruct (Zlength key); reflexivity.
       rewrite HH; clear HH.  
       apply andp_right.
         apply prop_right. split. omega. split; trivial.
          rewrite int_max_unsigned_eq.
         rewrite int_max_signed_eq in KL2; omega. 
       cancel.
       rewrite sepcon_comm.
       apply sepcon_derives.
         erewrite data_at_array_at.
         apply array_lemmas.array_at_ext'. intros. reflexivity. 
         trivial. omega. reflexivity. (*  unfold cVint, ZnthV; intros.
         if_tac. omega. 
              rewrite nth_map' with (d':=Int.zero). trivial.
              rewrite map_length. clear - H0.
              rewrite Zlength_correct in H0; destruct H0 as [XX YY].
              apply Z2Nat.inj_lt in YY; trivial. rewrite Nat2Z.id in YY; trivial. omega.*)
       rewrite memory_block_array_tuchar'. cancel.
         reflexivity. omega.
     } 
     after_call. subst WITNESS. normalize. simpl. subst retval0. 
       remember (map Vint (map Int.repr key)) as CONT.

   (*call memset*)
   remember (Tsh, Vptr cb (Int.add cofs (Int.repr (Zlength key + 328))), l64, Int.zero) as WITNESS.
   forward_call WITNESS.
     { assert (FR: Frame = [
        `(data_at Tsh (Tarray tuchar (Zlength key) noattr)
              CONT (Vptr cb (Int.add cofs (Int.repr 328))));
        `(data_at Tsh (Tarray tuchar (Zlength key) noattr)
              CONT (Vptr kb kofs));
         (* `(array_at tuchar Tsh CONT 0 l k);
         `(array_at tuchar Tsh CONT 0 l (Vptr cb (Int.add cofs (Int.repr 328))));*)
         `(field_at Tsh t_struct_hmac_ctx_st [_key_length] Vundef (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx]
             ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx]
             ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx]
             ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         `(data_at_ Tsh (Tarray tuchar 64 noattr) pad);
         (*`(array_at tuchar Tsh (ZnthV tuchar []) 0 64 pad);*)
         `(K_vector KV)]).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.   
       subst WITNESS. entailer.
       apply andp_right. apply prop_right.
         clear - KL2; split.
           specialize (initial_world.zlength_nonneg _ key); intros.
           rewrite int_max_unsigned_eq. omega.
         unfold offset_val. rewrite Zplus_comm. trivial.
       cancel. rewrite Zplus_comm.
       rewrite memory_block_array_tuchar'. cancel. trivial. omega.
     } 
     after_call. subst WITNESS. normalize. subst retval0. 

   forward. (*ctx->key_length=len*)
   subst PostIf_j_Len. entailer. cancel.
   unfold_data_at 3%nat. entailer.
   cancel.
   destruct (zlt 64 (Zlength key)). omega. cancel.  
   apply sepcon_derives.
   Focus 2. 
      erewrite data_at_array_at. unfold tuchars. apply derives_refl.
      reflexivity. omega. reflexivity.
  (*
   unfold_data_at 1%nat.
   cancel.*)
   rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
     entailer.
     rewrite at_offset'_eq.
     2: simpl; rewrite Int.add_zero; reflexivity.
     remember (64 - Zlength key) as ZK64. 
     unfold nested_field_offset2, nested_field_type2; simpl.
     unfold tarray.
     erewrite (data_at_array_at Tsh tuchar 64 noattr).
     2: apply JMeq.JMeq_refl. 
     2: omega.
     2: reflexivity. 
     erewrite (split_offset_array_at _ _ _ 0 (Zlength key) 64); try reflexivity. 2: omega.
     entailer. unfold offset_val. rewrite Int.add_assoc. rewrite add_repr. rewrite (Zplus_comm 328).
     rewrite sepcon_comm. 
     assert (F64: false = (Zlength key >? 64)). 
       rewrite Z.gtb_ltb. symmetry. apply Fcore_Zaux.Zlt_bool_false. omega.
     apply sepcon_derives. 
       erewrite data_at_array_at. 2: apply JMeq.JMeq_refl. 2: omega. 2: reflexivity.
       apply array_lemmas.array_at_ext'.
         unfold tuchars, cVint, ZnthV; intros. if_tac. omega.
         assert (Z32: (Z.to_nat i < length key)%nat).
                  clear - H1; destruct H1 as [XX YY]. rewrite Zlength_correct, Z2Nat.inj_lt in YY.
                  rewrite Nat2Z.id in YY; trivial. trivial. omega. 
         apply eq_sym.
         assert (L1: (Z.to_nat i < length (HMAC_FUN.mkKey key))%nat).
           rewrite mkKey_length; unfold SHA256_BlockSize.
           assert (Zlength key <= 64) by omega.  apply Z2Nat.inj_le in H3. simpl in H3.
           rewrite Zlength_correct, Nat2Z.id in H3. omega.
           omega. omega.
         rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Z0); trivial.
         rewrite nth_map' with (d':=Z0); trivial. f_equal. f_equal.         
         eapply mkKey_left; trivial. 
         rewrite map_length; trivial. rewrite map_length; trivial. 
       apply array_lemmas.array_at_ext'.
         unfold tuchars, cVint, ZnthV; intros. if_tac. omega.
         assert (L1: (Z.to_nat (i + Zlength key) < length (HMAC_FUN.mkKey key))%nat).
           rewrite mkKey_length; unfold SHA256_BlockSize.
           destruct H1. 
           apply (Z2Nat.inj_lt (i+ Zlength key) 64). omega. omega. omega.
         rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Z0). f_equal.
         rewrite (mkKey_right _ F64 (i + Zlength key)); trivial. omega. trivial.
         rewrite map_length; trivial.
  }

  intros. clear x. (*again, clear spurious x here*)
   entailer. unfold POSTCONDITION, abbreviate; simpl. entailer.
   unfold overridePost, initPostKeyNullConditional. 
   if_tac; trivial.
   entailer.
     apply exp_right with (x:=cb). apply andp_right. entailer.
   entailer.
     apply exp_right with (x:=cofs). 
     rewrite data_at__isptr. normalize.
     apply isptrD in H4. destruct H4 as [pb [pofs PAD]].
     apply exp_right with (x:=Vptr pb pofs).
   entailer.
     apply exp_right with (x:=1). entailer. cancel.
     if_tac; try omega. rewrite PAD; cancel.
  }
  { (*key == NULL*)
     forward. normalize. rewrite HeqPostKeyNull. clear  HeqPostKeyNull. normalize.
     entailer.
     unfold initPre, initPostKeyNullConditional.
     destruct key'; try contradiction; simpl in *; subst; simpl in *.
     (*integer*)
        unfold hmacstate_PreInitNull. normalize. rewrite data_at_isptr.
        normalize. apply isptrD in Pctx'. destruct Pctx' as [cb [cofs CTX']].
        subst; simpl in *. 
        apply isptrD in H1. destruct H1 as [pb [pofs PAD]].
        apply exp_right with (x:=cb). apply andp_right. entailer.
        apply exp_right with (x:=cofs).
        apply exp_right with (x:=Vptr pb pofs).
        apply exp_right with (x:=0). entailer. rewrite PAD. cancel.
        if_tac; try omega.
          apply exp_right with (x:=r). apply exp_right with (x:=v). entailer.
     inversion H0.
  }
  { (*side condition of forward_if key != NULL*)
    intros. entailer. unfold overridePost, normal_ret_assert; simpl. 
    if_tac. simpl. unfold POSTCONDITION, abbreviate, normal_ret_assert.
       entailer. trivial.
  }
Qed.



















