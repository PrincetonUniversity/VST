Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.

Require Import sha.hmac_NK.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.
Require Import sha.spec_hmacADT.

Definition initPostKeyNullConditional l r (c:val) (k: val) h key ctxkey: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 
                   then (hmacstate_PreInitNull key h c) * (data_at_ Tsh (tarray tuchar 64) ctxkey)
                   else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF 
                  else EX ll:_, EX CONT:_,
                      !!(Forall isbyteZ key /\ has_lengthK ll key /\ l = Vint(Int.repr ll)) &&
                    ((data_at Tsh t_struct_hmac_ctx_st CONT c) *
                     (data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                      ctxkey) *
                     (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
(*                   (array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key))*)
                      (Vptr b ofs)))
  | _ => FF
  end. 

Lemma hmac_init_part1: forall
(Espec : OracleKind)
(c : val)
(k : val)
(l : val)
(key : list Z)
(KV : val)
(h1:hmacabs)
(ctx' : name _ctx)
(key' : name _key)
(len' : name _len)
(Delta := initialized _reset 
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))
(PostKeyNull : environ -> mpred)
(HeqPostKeyNull : PostKeyNull =
                 EX  cb : block,
                 (EX  cofs : int,
                  (EX  pad : val,
                   (EX  r : Z,
                    (EX  ctxkey : val,
                     PROP  (c = Vptr cb cofs /\ (r = 0 \/ r = 1))
                     LOCAL  (`(eq (Vint (Int.repr r))) (eval_id _reset);
                     `(eq pad) (eval_var _pad (tarray tuchar 64));
                     `(eq c) (eval_id _ctx); `(eq k) (eval_id _key);
                     `(eq l) (eval_id _len);
                     `(eq ctxkey) (eval_var _ctx_key (tarray tuchar 64));
                     `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
                     SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                     `(initPostKeyNullConditional l r c k h1 key ctxkey);
                     `(K_vector KV))))))),
@semax Espec (initialized _reset Delta)
  (PROP  ()
   LOCAL  (`(eq (Vint (Int.repr 0))) (eval_id _reset);
   `(eq c) (eval_id _ctx); `(eq k) (eval_id _key); `(eq l) (eval_id _len);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(data_at_ Tsh (tarray tuchar 64)) (eval_var _pad (tarray tuchar 64));
   `(data_at_ Tsh (tarray tuchar 64)) (eval_var _ctx_key (tarray tuchar 64));
   `(K_vector KV); `(initPre l c k h1 key)))
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
                       (Tfunction (Tcons (tptr t_struct_SHA256state_st) Tnil)
                          tvoid cc_default))
                    [Eaddrof
                       (Efield
                          (Ederef (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
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
                                   (Tcons (tptr t_struct_SHA256state_st) Tnil))
                                tvoid cc_default))
                          [Evar _ctx_key (tarray tuchar 64);
                          Eaddrof
                            (Efield
                               (Ederef
                                  (Etempvar _ctx (tptr t_struct_hmac_ctx_st))
                                  t_struct_hmac_ctx_st) _md_ctx
                               t_struct_SHA256state_st)
                            (tptr t_struct_SHA256state_st)])
                       (Scall None
                          (Evar _memset
                             (Tfunction
                                (Tcons (tptr tvoid)
                                   (Tcons tint (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                          [Eaddrof
                             (Ederef
                                (Ebinop Oadd
                                   (Evar _ctx_key (tarray tuchar 64))
                                   (Econst_int (Int.repr 32) tint)
                                   (tptr tuchar)) tuchar) (tptr tuchar);
                          Econst_int (Int.repr 0) tint;
                          Econst_int (Int.repr 32) tint]))))
              (Ssequence
                 (Scall None
                    (Evar _memcpy
                       (Tfunction
                          (Tcons (tptr tvoid)
                             (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                          (tptr tvoid) cc_default))
                    [Evar _ctx_key (tarray tuchar 64);
                    Etempvar _key (tptr tuchar); Etempvar _len tint])
                 (Scall None
                    (Evar _memset
                       (Tfunction
                          (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                          (tptr tvoid) cc_default))
                    [Eaddrof
                       (Ederef
                          (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                             (Etempvar _len tint) (tptr tuchar)) tuchar)
                       (tptr tuchar); Econst_int (Int.repr 0) tint;
                    Ebinop Osub (Econst_int (Int.repr 64) tuint)
                      (Etempvar _len tint) tuint]))))) Sskip)
  (normal_ret_assert PostKeyNull).
Proof. intros. subst Delta. abbreviate_semax.
forward_if PostKeyNull.
  { (* THEN*)
    simpl.  
    unfold force_val2, force_val1; simpl.
    eapply semax_pre with (P':= EX cb:_, EX cofs:_, EX kb:_, EX kofs:_, EX CONT:_,
      EX pad:_, EX ctxkey:_, EX  ll : Z,
      (PROP  (c=Vptr cb cofs /\ k=Vptr kb kofs /\ Forall isbyteZ key /\
              has_lengthK ll key /\ l = Vint (Int.repr ll)) 
       LOCAL 
         (`(eq (Vint (Int.repr 0))) (eval_id _reset);
          `(eq pad) (eval_var _pad (tarray tuchar 64)); `(eq c) (eval_id _ctx);
          `(eq k) (eval_id _key); `(eq  l) (eval_id _len);
          `(eq ctxkey) (eval_var _ctx_key (tarray tuchar 64));
          `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
      SEP  (
          `(data_at_ Tsh (tarray tuchar 64) pad);
          `(data_at Tsh t_struct_hmac_ctx_st CONT (Vptr cb cofs));
          `(K_vector KV);
          `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) k);
(*          `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) k);*)
          `(data_at_ Tsh (tarray tuchar 64) ctxkey)))).
      entailer.
      destruct key'; try contradiction. simpl in *.
      (*key' is integer, ie Null*)
       { simpl in *. subst i. unfold Int.zero in *. simpl in *.
        unfold Vfalse in H0. inversion H0. }
      (*key' is ptr*)
       { simpl in *. normalize. rewrite (data_at_isptr _ t_struct_hmac_ctx_st). 
        entailer. clear HeqPostKeyNull.
        apply isptrD in Pctx'. destruct Pctx' as [cb [cofs CB]]. subst ctx'.
        apply exp_right with (x:=cb).
        apply exp_right with (x:=cofs).
        apply exp_right with (x:=b).
        apply exp_right with (x:=i).
        apply exp_right with (x:=CONT).
        apply exp_right with (x:=eval_var _pad (tarray tuchar 64) rho).
        apply exp_right with (x:=eval_var _ctx_key (tarray tuchar 64) rho).
        apply exp_right with (x:=ll).
        entailer. cancel.
        unfold data_block. entailer.
       }
    apply extract_exists_pre. intros cb. 
    apply extract_exists_pre. intros cofs.  
    apply extract_exists_pre. intros kb. 
    apply extract_exists_pre. intros kofs.  
    apply extract_exists_pre. intros CONT.  
    apply extract_exists_pre. intros pad.  
    apply extract_exists_pre. intros ctxkey.  
    apply extract_exists_pre. intros ll.  
    normalize. subst c k l. rename H1 into isbyte_key. 
    rename H2 into KL. rename ll into l. (*subst PostKeyNull.*)
    destruct KL as [KL1 [KL2 KL3]].

    forward. (*reset =1 *) (*qinxiang: here, forward now intoduces an essentially 
      unnecessary x:val, together with a term `(eq (Vint (Int.repr 0))) `x; in LOCAL*) 
    forward. (*j=HMAC_MAX_MD_CBLOCK*)
    simpl.

    remember
     (EX CONT:_, PROP  ()
      LOCAL  (
       `(eq (Vint (Int.repr 1))) (eval_id _reset);
       `(eq pad) (eval_var _pad (tarray tuchar 64)); `(eq (Vptr cb cofs)) (eval_id _ctx);
       `(eq (Vptr kb kofs)) (eval_id _key); `(eq (Vint (Int.repr l))) (eval_id _len);
       `(eq ctxkey) (eval_var _ctx_key (tarray tuchar 64));
       `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
      SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
            `(data_at Tsh t_struct_hmac_ctx_st CONT (Vptr cb cofs));
            `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
              (Vptr kb kofs));
(*           `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
             (Vptr kb kofs));*)
           `(data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                ctxkey);
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
                  `(eq ctxkey) (eval_var _ctx_key (tarray tuchar 64));
          `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
        SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
              `(data_at Tsh t_struct_hmac_ctx_st CONT (Vptr cb cofs));
              `(K_vector KV); `(data_at_ Tsh (tarray tuchar 64) ctxkey);
              `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                (Vptr kb kofs))
              (*`(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) (Vptr kb kofs))*)))).
        entailer. cancel. 
      normalize. rename H into lt_64_l.
      clear x. (*here's where we can finally elimnate the spurious x*) 
      unfold_data_at 1%nat.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
      normalize.
      (*new: extract info from field_address as early as possible*)
      rewrite data_at_isptr; normalize.
      apply isptrD in H; destruct H as [? [? PT]]; rewrite PT.
      unfold field_address in PT.
      destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
           (Vptr cb cofs)); inversion PT. 
      subst x x0; clear PT.
      rename f into FC.

      (*call to SHA256_init*)
      eapply semax_seq'.
      myframe_SEP'' [2].
      forward_call (Vptr cb cofs). 
      { assert (FR: Frame = []).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.   
       entailer. clear HeqPostKeyNull.
       unfold nested_field_type2, t_struct_hmac_ctx_st; simpl.
       eapply derives_trans.
         apply data_at_data_at_. (*reflexivity.*)
         cancel.
      } 
      after_call.
      normalize. simpl. (*normalize.*)

      (*call to SHA256_Update*)
      (*XXX: was: erewrite (split_offset_array_at _ _ _ 0 l); try reflexivity. 2: subst l; omega.*)      
      (*Now:*) rewrite (split_offset_array_at (Z.to_nat l)); try reflexivity. 
               Focus 2. subst l. repeat rewrite Zlength_map.
                        rewrite Z2Nat.id; omega. 
               Focus 2. subst l. rewrite Z2Nat.id; omega.
               rewrite firstn_same.
               Focus 2. repeat rewrite map_length.
                        subst l. rewrite Zlength_correct. rewrite Nat2Z.id. omega.

      normalize. simpl in H, H0. rewrite Zplus_0_r in H.
      rename H into OIR_kofs. rename H0 into OIR_kofs_key.

      eapply semax_seq'.
      myframe_SEP'' [6; 0; 2].
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
        cancel. unfold data_block. rewrite Zlength_correct. 
          entailer. 
      } 
      after_call. subst WITNESS. simpl. intros rho. normalize. simpl.
      assert (L: Z.to_nat l = length (map Vint (map Int.repr key))).
        subst l. rewrite Zlength_correct. repeat rewrite map_length. 
        rewrite Nat2Z.id. trivial.
      specialize (skipn_exact_length (map Vint (map Int.repr key))).
      rewrite <- L. unfold skipn; intros SEL; rewrite SEL.
      clear SEL.
               rewrite firstn_same.
               Focus 2. repeat rewrite map_length.
                        subst l. rewrite Zlength_correct. rewrite Nat2Z.id. omega.

     (*commute fun a => and EX x*)
     apply semax_pre with (P':=
      EX  xx : s256abs,
  (PROP  (update_abs key init_s256abs xx)
   LOCAL  (tc_environ Delta; 
   `(eq (Vint (Int.repr 64))) (eval_id _j);
   `(eq (Vint (Int.repr 1))) (eval_id _reset);
   `(eq pad) (eval_var _pad (tarray tuchar 64));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq ctxkey) (eval_var _ctx_key (tarray tuchar 64));
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP (`(K_vector KV); `(sha256state_ xx (Vptr cb cofs));
       `(data_block Tsh key (Vptr kb kofs));
       `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] (snd (snd CONT))
         (Vptr cb cofs));
       `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] (fst (snd CONT))
         (Vptr cb cofs)); `(data_at_ Tsh (tarray tuchar 64) pad);
       `(data_at_ Tsh (tarray tuchar 64) ctxkey)))).
   { entailer. apply (exp_right x).
     apply andp_right. apply prop_right. split; trivial.
     apply andp_right. trivial.
     cancel. eapply derives_trans; try eapply data_at_data_at_.
             assert (NULL: sizeof (tarray tuchar (Zlength key - Z.of_nat (length key))) = 0).
               rewrite Zlength_correct, <- Zminus_diag_reverse. reflexivity.
             rewrite data_at__memory_block.
               rewrite NULL, memory_block_zero_Vptr. entailer.
               reflexivity.
               rewrite NULL. omega.
   }
   apply extract_exists_pre. intros ctxSha. normalize. rename H into updAbs.

   (*call Final*)
   (*rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.
   normalize. 
   rewrite at_offset'_eq.
     2: simpl; rewrite Int.add_zero; reflexivity.
   unfold nested_field_offset2, nested_field_type2; simpl.
   unfold tarray.*) (*
   unfold data_at_, tarray. simpl. erewrite (data_at_array_at Tsh tuchar 64 noattr []).
     2: apply JMeq.JMeq_refl. 
     2: omega.
     2: reflexivity. *)
(*   erewrite (split_offset_array_at _ _ _ 0 32 64); try reflexivity. 2: omega.
   normalize.*)
    unfold data_at_ at 2, tarray. simpl. 
   (*now:*) unfold tarray. rewrite (data_at_Tarray_split3 Tsh tuchar 64 noattr 32). 2: omega.
            simpl.
            specialize (split_offset_array_at 32). unfold tarray; intros SOA.
            rewrite SOA; try reflexivity; simpl; clear SOA.
               2: rewrite Zlength_correct; simpl; omega.
               2: omega. 
   normalize.
   rewrite data_at_isptr. normalize.
   eapply semax_seq'.
   (*frame_SEP 2 3 0.*)
    myframe_SEP'' [2; 3; 0].   
   remember (ctxSha, ctxkey,
             Vptr cb cofs, Tsh, KV) as WITNESS.
   forward_call WITNESS.
     { assert (FR: Frame = []).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.   
       subst WITNESS. entailer. cancel.
       (*XXX was: rewrite memory_block_array_tuchar'. cancel. trivial. omega.*)
       (*Now*) eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. entailer.
               reflexivity. simpl. omega.
     }
     after_call. subst WITNESS. simpl. intros rho. normalize. simpl. normalize. simpl.

   (*call memset*)
   (* doing this: eapply semax_seq'. frame_SEP 3. requires us to do the swap fun a=> vs EX
      after the call, which leaves a state that still doesn't nicely normalize *)
   remember (Tsh, offset_val (Int.repr 32) ctxkey, 32, Int.zero) as WITNESS.
   forward_call WITNESS.
     { assert (FR: Frame = [`(K_vector KV);
         `(data_at_ Tsh sha.t_struct_SHA256state_st (Vptr cb cofs));
         `(data_block Tsh (sha_finish ctxSha) ctxkey);
         `(data_block Tsh key (Vptr kb kofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]
              ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]
              ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         `(data_at_ Tsh (Tarray tuchar 64 noattr) pad)]).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.   
       entailer. cancel.
       (*was: rewrite memory_block_array_tuchar'. cancel. trivial. omega.*)
       (*Now*) eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. entailer.
               reflexivity. simpl. omega.
     } 
     after_call. subst WITNESS.
   subst PostIf_j_Len.
   entailer.
   apply (exp_right (default_val t_struct_hmac_ctx_st)). 
     apply andp_right. trivial.
     apply andp_right. trivial.
     apply andp_right. trivial.
     cancel.
   unfold data_block. entailer. cancel. 
   unfold data_at_.
   unfold_data_at 4%nat.
   destruct (zlt 64 (Zlength key)). 2: omega.
   cancel. 
   rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
      simpl. unfold nested_field_type2. simpl. unfold field_address; simpl.
   destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
            (Vptr cb cofs)).
   2: elim (n FC).
   unfold nested_field_offset2; simpl. rewrite Int.add_zero. cancel.
     unfold tarray. rewrite (data_at_Tarray_split3 Tsh tuchar 64 noattr 32). 2: omega.
     specialize (split_offset_array_at 32). unfold tarray; intros SOA.
     rewrite SOA with (len :=64)(v:=(eval_var _ctx_key (Tarray tuchar 64 noattr) rho)); try reflexivity; clear SOA.
       Focus 2. rewrite Zlength_correct, app_length, force_lengthn_length_n, Nat2Z.inj_add, nat_of_Z_eq.
                assert (HZ: Z.of_nat 32=32) by reflexivity. rewrite HZ; clear HZ. omega.
                omega.
       2: simpl; omega.
     entailer. 
     rewrite firstn_app1.
     Focus 2. rewrite force_lengthn_length_n. simpl; omega. 
     rewrite firstn_same. 
     Focus 2. rewrite force_lengthn_length_n. simpl; omega. 
     assert (LengthShaFinish: Zlength (sha_finish ctxSha) = 32).
                 unfold sha_finish. destruct ctxSha.
        rewrite <- functional_prog.SHA_256'_eq, Zlength_correct, length_SHA256'. reflexivity.
     rewrite LengthShaFinish. 
     assert (NZ: nat_of_Z 32 = 32%nat) by reflexivity. rewrite NZ; clear NZ.
     rewrite skipn_force_lengthn_app.
     assert (SF:64 - Z.of_nat 32 = 32) by reflexivity. rewrite SF; clear SF.
     rewrite sepcon_comm. 
     apply sepcon_derives. 
     { apply data_at_Tarray_ext_derives. intros. 
              unfold Znth. if_tac. omega.
              assert (Z32: (Z.to_nat i < 32)%nat).
                  clear - H5; destruct H5 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
                  apply YY. omega. omega.
         apply data_at_triv.
         rewrite nth_force_lengthn. 2: simpl; omega.
         rewrite nth_indep with (d:=(default_val tuchar))(d':=Vint (Int.repr 0)).
         rewrite nth_indep with (d:=(default_val tuchar))(d':=Vint (Int.repr 0)).
         repeat rewrite map_nth. f_equal. f_equal. unfold sha_finish. destruct ctxSha.
         unfold HMAC_SHA256.mkKey. simpl. 
              assert (Z6: Zlength key > 64) by omega. 
              apply Zgt_is_gt_bool in Z6; rewrite Z6.
              unfold HMAC_SHA256.zeroPad.
              rewrite <- functional_prog.SHA_256'_eq.
              rewrite app_nth1. inversion updAbs. clear POSTCONDITION HeqPostKeyNull PostKeyNull. subst. clear updAbs. simpl in *.
                      rewrite <- H16. trivial.
              rewrite length_SHA256'; trivial.
              repeat rewrite map_length. rewrite mkKey_length; unfold SHA256.BlockSize; simpl. omega.
              repeat rewrite map_length. unfold sha_finish. inversion updAbs. rewrite <- functional_prog.SHA_256'_eq, length_SHA256'. trivial.
       }
     { apply data_at_Tarray_ext_derives. intros. 
       unfold Znth. if_tac. omega. if_tac. omega. clear H3 H4. 
       apply data_at_triv.
       assert (Z32: (Z.to_nat i < 32)%nat).
                  clear - H5; destruct H5 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
                  apply YY. omega. omega.
       unfold HMAC_SHA256.mkKey. 
               assert (Kgt: Zlength key > Z.of_nat SHA256.BlockSize).  simpl; omega.
               apply Zgt_is_gt_bool in Kgt.
               rewrite Kgt. unfold HMAC_SHA256.zeroPad. repeat rewrite map_app.
               rewrite app_nth2; repeat rewrite map_length; rewrite length_SHA256'.
                 assert (Z.to_nat 32 - SHA256.DigestLength = 0)%nat.                   
                            unfold SHA256.DigestLength. simpl; omega.
                 rewrite H3.
                 assert (SHA32: (SHA256.BlockSize - SHA256.DigestLength)%nat = 32%nat) by reflexivity.
                 rewrite SHA32; clear SHA32.
                 rewrite nth_map' with (d':=Int.zero).
                   rewrite nth_map' with (d':=Z0).
                     rewrite nth_list_repeat; trivial.
                 assert (X: (nat_of_Z (32 + 1) = 1 + 32)%nat) by reflexivity.
                 rewrite X; clear X. rewrite <- skipn_drop.
                 rewrite skipn_app2.
                   repeat rewrite map_length. unfold  SHA256.Hash. rewrite length_SHA256'.
                   assert (32 - SHA256.DigestLength = 0)%nat by reflexivity. rewrite H4.
                 rewrite skipn_0.
                 do 2 rewrite skipn_map.
                rewrite skipn_list_repeat. do 2 rewrite map_list_repeat. reflexivity.
                repeat rewrite map_length. unfold  SHA256.Hash. rewrite length_SHA256'. 
                   unfold SHA256.DigestLength. omega. 
                rewrite length_list_repeat. omega. 
                rewrite map_length, length_list_repeat. omega. 
                unfold SHA256.DigestLength. simpl; omega.
         }
   } 

   { (* j >= len*)
     eapply semax_pre with (P':=
       (PROP  (64 >= l)
        LOCAL 
         (
   `(eq (Vint (Int.repr 64))) (eval_id _j);
   `(eq (Vint (Int.repr 1))) (eval_id _reset); 
   `(eq pad) (eval_var _pad (tarray tuchar 64));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq ctxkey) (eval_var _ctx_key (tarray tuchar 64));
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
     `(data_at Tsh t_struct_hmac_ctx_st CONT (Vptr cb cofs)); `(K_vector KV);
     `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                  (Vptr kb kofs));
     (*`(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
        (Vptr kb kofs));*)
     `(data_at Tsh (Tarray tuchar 64 noattr) [] ctxkey)))).
        entailer. 
     normalize. rename H into ge_64_l. 
     clear x. (*again, remove spurious x*)

     (*call to memcpy*)
     focus_SEP 1 3.
     unfold data_at_. 
     rewrite data_at_isptr with (p:=ctxkey). normalize. simpl.
     apply isptrD in H. destruct H as [ckb [ckofs CTK]]; subst ctxkey. simpl.
     apply semax_pre with (P':= 
       (PROP  (offset_in_range 0 (Vptr ckb ckofs) /\ offset_in_range 64 (Vptr ckb ckofs))
        LOCAL  (`(eq (Vint (Int.repr 64))) (eval_id _j);
                `(eq (Vint (Int.repr 1))) (eval_id _reset);
                `(eq pad) (eval_var _pad (tarray tuchar 64));
                `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
                `(eq (Vint (Int.repr l))) (eval_id _len);
                `(eq (Vptr ckb ckofs)) (eval_var _ctx_key (tarray tuchar 64));
                `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
        SEP  (`(data_at Tsh t_struct_hmac_ctx_st CONT (Vptr cb cofs));
              `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
               (Vptr kb kofs)); `(data_at Tsh (tarray tuchar 64) [] pad);
              `(K_vector KV);
              `(data_at Tsh (Tarray tuchar 64 noattr) [] (Vptr ckb ckofs))))).
     { entailer. 
       specialize (split_offset_array_at 0 Tsh). unfold tarray. intros X.
       rewrite X with (len:=64)(v:=Vptr ckb ckofs). entailer.
       apply prop_right. specialize (Int.unsigned_range ckofs). intros x; omega.
       reflexivity. rewrite Zlength_correct; simpl; omega. simpl; omega.
     }
     normalize. rename H into OIR0_328. rename H0 into OIR64_328.
      
     unfold tarray.
     (*was:     erewrite data_at_array_at. 2: apply JMeq.JMeq_refl. 2: omega. 2: reflexivity.
                erewrite (split_offset_array_at _ _ _ 0 l 64); try reflexivity. 2: omega.
                unfold tuchars.
          normalize.
          rename H into OIR0_328. rename H0 into OIR64_328.*)

     remember (64 - l) as l64.
     remember ((Tsh, Tsh), Vptr ckb ckofs, 
             Vptr kb kofs, mkTrep (Tarray tuchar (Zlength key) noattr) 
                     (map Vint (map Int.repr key))) as WITNESS.
     forward_call WITNESS.
     { assert (FR: Frame = [
         `(data_at Tsh (Tarray tuchar l64 noattr)
             (Znth l [] Vundef :: skipn (nat_of_Z (l + 1)) [])
             (offset_val (Int.repr l) (Vptr ckb ckofs)));
         `(data_at_ Tsh t_struct_hmac_ctx_st (Vptr cb cofs));
         `(data_at_ Tsh (Tarray tuchar 64 noattr) pad); `(K_vector KV)]).
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
       rewrite HH.  
       apply andp_right.
         apply prop_right. split. omega. split; trivial.
          rewrite int_max_unsigned_eq.
         rewrite int_max_signed_eq in KL2; omega.
       cancel.
              rewrite (data_at_Tarray_split3a Tsh tuchar 64 noattr (Zlength key)). 2: omega.
              specialize (split_offset_array_at (length key)). unfold tarray; intros SOA.
              rewrite SOA; try reflexivity; clear SOA.
              Focus 2. repeat rewrite Zlength_correct.
                       repeat rewrite map_length. rewrite app_length.
                       rewrite force_lengthn_length_n, nat_of_Z_of_nat; simpl.
                       rewrite Nat2Z.inj_add. omega. 
              2: rewrite Zlength_correct in ge_64_l; omega.
        entailer. rewrite firstn_app1.
              Focus 2. rewrite force_lengthn_length_n. trivial.
              rewrite firstn_precise.
              Focus 2. repeat rewrite map_length.  rewrite force_lengthn_length_n. trivial.
        apply sepcon_derives. 
         eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. entailer.
               simpl. rewrite <- Zlength_correct.
               rewrite Zlength_max_zero, HH. cancel.
               reflexivity.
               simpl. rewrite <- Zlength_correct, Zlength_max_zero, HH. 
               rewrite <- initialize.max_unsigned_modulus. specialize Int.max_signed_unsigned; omega.
         
              rewrite skipn_app2.
              Focus 2. rewrite force_lengthn_length_n. omega.
              rewrite force_lengthn_length_n.
              assert (X: (length key - length key = 0)%nat). omega.
              rewrite X, skipn_0, <- Zlength_correct.
              unfold offset_val. cancel. 
     } 
     after_call. subst WITNESS. normalize. simpl. subst retval0. 
       remember (map Vint (map Int.repr key)) as KCONT.

   (*call memset*)
   remember (Tsh, Vptr ckb (Int.add ckofs (Int.repr (Zlength key))), l64, Int.zero) as WITNESS.
   forward_call WITNESS.
     { assert (FR: Frame = [
            `(data_at Tsh (Tarray tuchar (Zlength key) noattr) KCONT (Vptr ckb ckofs));
            `(data_at Tsh (Tarray tuchar (Zlength key) noattr) KCONT (Vptr kb kofs));
            `(data_at_ Tsh t_struct_hmac_ctx_st (Vptr cb cofs));
            `(data_at_ Tsh (Tarray tuchar 64 noattr) pad); `(K_vector KV)]).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.   
       subst WITNESS. entailer. rewrite <- H0.
       apply andp_right. apply prop_right.
         split; trivial.
         split; trivial.
         clear - KL2; split.
           specialize (initial_world.zlength_nonneg _ key); intros.
           rewrite int_max_unsigned_eq. omega.
         unfold offset_val. simpl. rewrite Int.add_zero, Int.mul_commut, Int.mul_one. trivial.
       cancel. 
         eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. 
               rewrite sizeof_Tarray. entailer.
         assert (64 - Zlength key >= 0). omega.
         rewrite Zmax_spec. destruct (zlt (64 - Zlength key) 0); trivial. omega.
         reflexivity.
         rewrite  sizeof_Tarray. 
         assert (64 - Zlength key <= 64) by omega.
         assert (64 < Int.modulus).
         2: omega.
         rewrite <- initialize.max_unsigned_modulus, int_max_unsigned_eq. omega.
         rewrite Zmax_spec. destruct (zlt (64 - Zlength key) 0); trivial. omega.
     } 
     after_call. subst WITNESS. normalize. 

   subst PostIf_j_Len. entailer. 
   apply (exp_right (default_val t_struct_hmac_ctx_st)).
   apply andp_right. trivial. 
   apply andp_right. trivial. 
   apply andp_right. trivial. cancel. unfold tarray.

   destruct (zlt 64 (Zlength key)). omega. rewrite Zlength_correct in g. apply (Nat2Z.inj_ge 64) in g.
   clear H H0 TC0 h1.
     remember (64 - Zlength key) as ZK64.
     rewrite (data_at_Tarray_split3a Tsh tuchar 64 noattr (Zlength key)). 2: omega.
              simpl. unfold nat_of_Z. rewrite Zlength_correct, Nat2Z.id.
              rewrite sepcon_comm.
              specialize (split_offset_array_at (length key) Tsh tuchar 64). unfold tarray; intros SOA.
              rewrite SOA; try reflexivity; clear SOA.
      2: rewrite Zlength_correct, app_length, force_lengthn_length_n, Nat2Z.inj_add; omega.
      2: rewrite Zlength_correct in ge_64_l; omega.
      assert (STO: sizeof tuchar = 1) by reflexivity. rewrite STO, Z.mul_1_l. rewrite Z.mul_1_l.
      entailer. 

     remember (64 - Zlength key) as ZK64. 
      specialize (split_offset_array_at (Z.to_nat ZK64) Tsh tuchar ZK64). intros X. unfold tarray in X. 
        rewrite X. clear X. entailer.
     remember (64 - Zlength key) as ZK64. 
     assert (F64: false = (Zlength key >? 64)). 
       rewrite Z.gtb_ltb. symmetry. apply Fcore_Zaux.Zlt_bool_false. omega.
      rewrite firstn_app1. 2: rewrite force_lengthn_length_n; trivial.
      rewrite firstn_precise. 2: rewrite length_list_repeat; trivial.
      rewrite firstn_precise. 2: rewrite force_lengthn_length_n; trivial.
      assert (NULL: ZK64 - Z.of_nat (Z.to_nat ZK64) = 0).
        rewrite Z2Nat.id. omega. omega.
      rewrite NULL.
      rewrite skipn_short. 2: rewrite length_list_repeat; omega.
      apply derives_trans
       with (Q:=data_at Tsh (Tarray tuchar (Z.of_nat (length key)) noattr)
                  (map Vint (map Int.repr key)) (Vptr ckb ckofs) *
                data_at Tsh (Tarray tuchar (Z.of_nat (Z.to_nat ZK64)) noattr)
                  (list_repeat (Z.to_nat ZK64) (Vint Int.zero))
                  (Vptr ckb (Int.add ckofs (Int.repr (Z.of_nat (length key)))))).
          cancel.
          eapply derives_trans; try apply data_at_data_at_.
          rewrite data_at__memory_block. simpl. entailer.
          reflexivity. simpl. specialize Int.modulus_pos. omega.
      apply sepcon_derives.
      { apply data_at_Tarray_ext_derives. intros i I.
        apply data_at_triv. unfold Znth. if_tac. trivial. clear H.
        rewrite nth_force_lengthn.
        Focus 2. split. omega. destruct I as [Ipos I]. apply Z2Nat.inj_lt in I; trivial.
                 rewrite Nat2Z.id in I. trivial. omega.
         assert (Z32: (Z.to_nat i < length key)%nat).
                  clear - I; destruct I as [XX YY]. rewrite Z2Nat.inj_lt in YY.
                  rewrite Nat2Z.id in YY; trivial. trivial. omega. 
         apply eq_sym.
         assert (L1: (Z.to_nat i < length (HMAC_SHA256.mkKey key))%nat).
           rewrite mkKey_length; unfold SHA256.BlockSize.
           assert (Zlength key <= 64) by omega.  apply Z2Nat.inj_le in H. simpl in H.
           rewrite Zlength_correct, Nat2Z.id in H. omega.
           omega. omega.
         rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Z0); trivial.
         rewrite nth_map' with (d':=Z0); trivial. f_equal. f_equal.         
         eapply mkKey_left; trivial. rewrite Zlength_correct. trivial.
         rewrite map_length; trivial. rewrite map_length; trivial.
      }
      { unfold offset_val. rewrite skipn_force_lengthn_app. rewrite Z2Nat.id.  
        rewrite HeqZK64, Zlength_correct.
        apply data_at_Tarray_ext_derives. rewrite <- Zlength_correct, <- HeqZK64.
        intros i I.
        apply data_at_triv. unfold Znth. if_tac. trivial. clear H.
        rewrite Zlength_correct.
        destruct (zlt (Z.of_nat (length key)) 0).
        rewrite <- Zlength_correct in l. omega.
        rewrite nth_indep with (d:=(default_val tuchar))(d':=Vint (Int.repr 0)).
        Focus 2.  rewrite length_list_repeat. apply Z2Nat.inj_lt. omega. omega. omega.
        rewrite nth_list_repeat. rewrite HeqZK64, Zlength_correct in I.
        remember (Z.to_nat i) as K; destruct K; simpl.
         rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Z0); trivial. f_equal. f_equal.    
         rewrite mkKey_right; trivial. rewrite Zlength_correct. omega.
         rewrite mkKey_length, Nat2Z.id. unfold SHA256.BlockSize. omega.
         rewrite map_length, mkKey_length, Nat2Z.id. unfold SHA256.BlockSize. omega.
        rewrite nth_skipn. 
         assert (K + Z.to_nat (Z.of_nat (length key) + 1) = Z.to_nat (Z.of_nat (length key) + i))%nat.
            rewrite Z2Nat.inj_add. rewrite Z2Nat.inj_add. rewrite <- HeqK.
            remember (Z.to_nat (Z.of_nat (length key))) as u. simpl. rewrite <- plus_n_Sm. rewrite <- (plus_Snm_nSm u). omega.
            rewrite <- Zlength_correct. apply Zlength_nonneg.
            omega.
            rewrite <- Zlength_correct. apply Zlength_nonneg.
            omega.
         rewrite H; clear H.
         rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Z0); trivial. f_equal. f_equal. 
         rewrite mkKey_right; trivial. rewrite Zlength_correct. omega.
         rewrite mkKey_length. unfold SHA256.BlockSize. apply (Z2Nat.inj_lt _ 64). omega. omega. omega. 
         rewrite map_length. rewrite mkKey_length. unfold SHA256.BlockSize. apply (Z2Nat.inj_lt _ 64). omega. omega. omega. 
         omega.
      }
      reflexivity. rewrite Zlength_correct, length_list_repeat. omega.
      rewrite Z2Nat.id; omega.
  }

  intros. clear x. (*again, clear spurious x here*)
   entailer. unfold POSTCONDITION, abbreviate; simpl. entailer.
   unfold overridePost, initPostKeyNullConditional. 
   if_tac; trivial.
   entailer. rename x into st.
     apply exp_right with (x:=cb). apply andp_right. trivial. 
   entailer.
     apply exp_right with (x:=cofs). 
     rewrite data_at__isptr. normalize.
     apply isptrD in H4. destruct H4 as [pb [pofs PAD]].
     apply exp_right with (x:=Vptr pb pofs).
   entailer. 
     apply exp_right with (x:=1). entailer.
     apply isptrD in H5. destruct H5 as [ckb [ckofs CK]].
     apply exp_right with (x:=Vptr ckb ckofs).
     entailer. cancel.
     if_tac; try omega. rewrite PAD, CK; cancel.
     apply exp_right with (x:= Zlength key).
     apply (exp_right st). entailer.
     apply andp_right. apply prop_right. unfold has_lengthK; clear H. split; trivial. split; trivial.
     cancel.
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
        apply isptrD in H2. destruct H2 as [ckb [ckofs CK]].
        apply exp_right with (x:=Vptr ckb ckofs). entailer. cancel. 
        if_tac; try omega.
          apply exp_right with (x:=r). rewrite CK; cancel. 
          apply exp_right with (x:=v). entailer.
     inversion H0.
  }
  { (*side condition of forward_if key != NULL*)
    intros. entailer. unfold overridePost, normal_ret_assert; simpl. 
    if_tac. simpl. unfold POSTCONDITION, abbreviate, normal_ret_assert.
       entailer. trivial.
  }
Qed.



















