Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.

Require Import sha.hmac091c.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.
Require Import sha.spec_hmac.

Definition initPostKeyNullConditional r (c:val) (k: val) h key : mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 then hmacstate_PreInitNull key h c else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF 
                  else !!(Forall isbyteZ key) &&
                    ((data_at Tsh t_struct_hmac_ctx_st (keyedHMS key) c) *
                    (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
(*                    (array_at Tsh tuchar 0 (Zlength key)  (map Vint (map Int.repr key)) *)
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
          `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) k)))).
(*          `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) k)))).*)
      { entailer.
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
      }
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
            `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
              (Vptr kb kofs));
(*           `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
             (Vptr kb kofs));*)
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
              `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                (Vptr kb kofs))
    (*          `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) (Vptr kb kofs))*)
               ))).
        entailer. 
      normalize. rename H into lt_64_l.
      clear x. (*here's where we can finally eliminate the spurious x*) 

      (*call to SHA256_init*)
      eapply semax_seq'.
      myframe_SEP'' [1].
      unfold data_at_. simpl.
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

      forward_call (Vptr cb cofs). 
      { assert (FR: Frame = [
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] Vundef (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _key] [] (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]
              ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]
              ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs))]).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.  
       entailer. cancel.
      } 
      after_call.
      normalize. simpl. (*normalize.*)

      (*call to SHA256_Update*)
      (*was: erewrite (split_offset_array_at _ _ _ 0 l); try reflexivity. 2: subst l; omega.*)
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
      myframe_SEP'' [8; 0; 2].
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

     (*commute fun a => and EX x, and eliminate empty array at Vptr kb ofs*)
     apply semax_pre with (P':=
      EX  xx : s256abs,
  (PROP  (update_abs key init_s256abs xx)
   LOCAL  (tc_environ Delta; 
   `(eq (Vint (Int.repr 64))) (eval_id _j);
   `(eq (Vint (Int.repr 1))) (eval_id _reset);
   `(eq pad) (eval_var _pad (tarray tuchar 64));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP  (`(K_vector KV); `(sha256state_ xx (Vptr cb cofs));
       `(data_block Tsh key (Vptr kb kofs));
       `(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] Vundef
          (Vptr cb cofs));
       `(field_at Tsh t_struct_hmac_ctx_st [StructField _key] [] (Vptr cb cofs));
       `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]
           ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
       `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]
           ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
       `(data_at_ Tsh (tarray tuchar 64) pad)))).
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
   rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.

      (*new: extract info from field_address as early as possible*)
      rewrite data_at_isptr; normalize.
      apply isptrD in H; destruct H as [? [? PT]]; rewrite PT.
      unfold field_address in PT.
      destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _key]
           (Vptr cb cofs)); inversion PT. 
      subst x x0; clear PT.

   (*was
      normalize. 
      rewrite at_offset'_eq.
      2: simpl; rewrite Int.add_zero; reflexivity.*)

   unfold nested_field_offset2, nested_field_type2; simpl.
   unfold tarray.

   (*was erewrite (data_at_array_at Tsh tuchar 64 noattr []).
     2: apply JMeq.JMeq_refl. 
     2: omega.
     2: reflexivity. 
     erewrite (split_offset_array_at _ _ _ 0 32 64); try reflexivity. 2: omega.*)
   (*now:*) unfold tarray. rewrite (data_at_Tarray_split3 Tsh tuchar 64 noattr 32). 2: omega.
            simpl.
            specialize (split_offset_array_at 32). unfold tarray; intros SOA.
            rewrite SOA; try reflexivity; simpl; clear SOA.
               2: rewrite Zlength_correct; simpl; omega.
               2: omega.

   normalize. rename H into BND1; rename H0 into BND2; rename H1 into BND3.

   eapply semax_seq'.
   myframe_SEP'' [2; 3; 0].
   remember (ctxSha, Vptr cb (Int.add cofs (Int.repr 328)),
             Vptr cb cofs, Tsh, KV) as WITNESS.
   forward_call WITNESS.
     { assert (FR: Frame = []).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.   
       subst WITNESS. entailer. cancel.
       (*was: rewrite memory_block_array_tuchar'. cancel. trivial. omega.*)
       (*Now*) eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. entailer.
               reflexivity. simpl. omega.
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
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] Vundef (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]
              ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]
              ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
(*         `(data_at_ Tsh t_struct_SHA256state_st sha);*)
         `(data_at_ Tsh (Tarray tuchar 64 noattr) pad)]).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.   
       entailer. cancel. 
       (*was: rewrite memory_block_array_tuchar'. cancel. trivial. omega.*)
       (*Now*) eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. entailer.
               reflexivity. simpl. omega.
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
   unfold_data_at 4%nat.
   destruct (zlt 64 (Zlength key)). 2: omega.
   cancel. 
   rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.
   unfold field_address.
   destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _key]
              (Vptr cb cofs)); try contradiction. clear f0.
     unfold nested_field_offset2, nested_field_type2; simpl.
     unfold tarray. rewrite (data_at_Tarray_split3 Tsh tuchar 64 noattr 32). 2: omega.
     specialize (split_offset_array_at 32). unfold tarray; intros SOA.
     rewrite SOA with (len :=64)(v:=Vptr cb (Int.add cofs (Int.repr 328))); try reflexivity; clear SOA.
       Focus 2. rewrite Zlength_correct, app_length, force_lengthn_length_n, Nat2Z.inj_add, nat_of_Z_eq.
                assert (Z.of_nat 32=32) by reflexivity. rewrite H2; clear H2. omega.
                omega.
       2: simpl; omega.
     entailer. apply andp_right. apply prop_right. red; omega.
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
     unfold offset_val. rewrite int_add_assoc1.
     rewrite sepcon_assoc. rewrite sepcon_comm. 
     apply sepcon_derives. 
     { apply sepcon_derives.
       { rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
         unfold nested_field_type2, field_address, nested_field_offset2; simpl.
         rewrite int_add_repr_0_r.
         destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
            (Vptr cb cofs)). cancel.
         elim (n f). (*Qinxiang: why is this ok - they're about different fileds (md_cts versus _key -
                        maybe it's because md_ctx comes before _key in the record?*)
       }
       { apply data_at_Tarray_ext_derives. intros. 
              unfold Znth. if_tac. omega.
              assert (Z32: (Z.to_nat i < 32)%nat).
                  clear - H2; destruct H2 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
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
              rewrite app_nth1. inversion updAbs. subst. clear updAbs. simpl in *.
                      rewrite <- H13. trivial.
              rewrite length_SHA256'; trivial.
              repeat rewrite map_length. rewrite mkKey_length; unfold SHA256.BlockSize; simpl. omega.
              repeat rewrite map_length. unfold sha_finish. inversion updAbs. rewrite <- functional_prog.SHA_256'_eq, length_SHA256'. trivial.
       }
     }
     { assert (X: 328 + Z.of_nat 32 = 360) by reflexivity. rewrite X; clear X.
       apply data_at_Tarray_ext_derives. intros. 
       unfold Znth. if_tac. omega. if_tac. omega. clear H3 H4. 
       apply data_at_triv.
       assert (Z32: (Z.to_nat i < 32)%nat).
                  clear - H2; destruct H2 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
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
         (`(eq (Vint (Int.repr 64))) (eval_id _j);
          `eq (eval_id _reset) `(Vint (Int.repr 1));
          `(eq pad) (eval_var _pad (tarray tuchar 64)); `(eq (Vptr cb cofs)) (eval_id _ctx);
          `(eq (Vptr kb kofs)) (eval_id _key); `(eq (Vint (Int.repr l))) (eval_id _len);
          `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
        SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
              `(data_at_ Tsh t_struct_hmac_ctx_st (Vptr cb cofs)); `(K_vector KV);
              `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                  (Vptr kb kofs))))).
        entailer. 
     normalize. rename H into ge_64_l. 
     clear x. (*again, remove spurious x*)

     (*call to memcpy*)
     (*eapply semax_seq'.*)
     focus_SEP 1 3.
     unfold data_at_. 
     unfold_data_at 1%nat.
     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.
     (*new: extract field_address as early as possible*)
      rewrite data_at_isptr; normalize.
      apply isptrD in H; destruct H as [? [? PT]]; rewrite PT.
      unfold field_address in PT.
      destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _key]
           (Vptr cb cofs)); inversion PT. 
      subst x x0; clear PT.
      unfold nested_field_offset2, nested_field_type2; simpl. 
     (*was: normalize. 
            rename H into SCc. rename H0 into ACc.
           (*rewrite isptr_c;*) simpl.
           rewrite at_offset_data_at. unfold nested_field_type2, nested_field_offset2; simpl.*)
     unfold tarray.
     (*was:     erewrite data_at_array_at. 2: apply JMeq.JMeq_refl. 2: omega. 2: reflexivity.
                erewrite (split_offset_array_at _ _ _ 0 l 64); try reflexivity. 2: omega.
                unfold tuchars.*)
     (*now:*) remember (`(data_at Tsh (Tarray tuchar 64 noattr) [] pad)) as ZZ.
              rewrite (data_at_Tarray_split3a Tsh tuchar 64 noattr l). 2: omega.
              simpl.
              specialize (split_offset_array_at (Z.to_nat l)). unfold tarray; intros SOA.
              rewrite SOA; try reflexivity; clear SOA.
              Focus 2. rewrite Zlength_correct, app_length, force_lengthn_length_n. simpl. 
                       rewrite Nat2Z.inj_add. repeat rewrite nat_of_Z_eq; omega.
              2:rewrite Z2Nat.id; omega.
              subst ZZ.

     normalize.
     rename H into OIR0_328. rename H0 into OIR64_328.

     (*new:*) rewrite firstn_app1.
              Focus 2. rewrite force_lengthn_length_n. trivial.
              rewrite firstn_precise.
              Focus 2. rewrite force_lengthn_length_n. trivial.
              rewrite skipn_app2.
              Focus 2. rewrite force_lengthn_length_n. unfold  nat_of_Z. omega.
              rewrite force_lengthn_length_n.
              assert (X: (Z.to_nat l - nat_of_Z l = 0)%nat).
                   unfold nat_of_Z.  omega. 
              rewrite X, skipn_0, Z2Nat.id; clear X. 2: omega.

     remember (64 - l) as l64.
     remember ((Tsh, Tsh), Vptr cb (Int.add cofs (Int.repr 328)), 
             Vptr kb kofs, mkTrep (Tarray tuchar (Zlength key) noattr) 
                     (map Vint (map Int.repr key))) as WITNESS.
     forward_call WITNESS.
     { assert (FR: Frame = [
         `(data_at Tsh (Tarray tuchar l64 noattr)
             (Znth l [] Vundef :: skipn (nat_of_Z (l + 1)) [])
               (offset_val (Int.repr l) (Vptr cb (Int.add cofs (Int.repr 328)))));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] Vundef (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         `(data_at Tsh (Tarray tuchar 64 noattr) [] pad); `(K_vector KV)]).
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
       rewrite HH (*was: clear HH*).  
       apply andp_right.
         apply prop_right. split. omega. split; trivial.
          rewrite int_max_unsigned_eq.
         rewrite int_max_signed_eq in KL2; omega. 
       cancel.
       (*was: rewrite sepcon_comm.
              apply sepcon_derives.
                erewrite data_at_array_at.
                apply array_lemmas.array_at_ext'. intros. reflexivity. 
                trivial. omega. reflexivity. 
              rewrite memory_block_array_tuchar'. cancel.
             reflexivity. omega.*)
       (*Now*) eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. entailer.
               simpl.
               rewrite Zlength_max_zero, HH. cancel.
               reflexivity.
               simpl. rewrite Zlength_max_zero, HH. 
               rewrite <- initialize.max_unsigned_modulus. specialize Int.max_signed_unsigned; omega.
         
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
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] Vundef (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]
             ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]
             ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]
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
       cancel.
       (*was:  rewrite memory_block_array_tuchar'. cancel. trivial. omega.*)
       (*Now*) eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. entailer.
               rewrite sizeof_Tarray, Zplus_comm. cancel.
               apply Zmax_right; omega. 
               reflexivity.
               rewrite sizeof_Tarray, <- initialize.max_unsigned_modulus, int_max_unsigned_eq. omega.
               apply Zmax_right; omega.
     } 
     after_call. subst WITNESS. normalize. subst retval0. 

   forward. (*ctx->key_length=len*)
   subst PostIf_j_Len. entailer. cancel.
   unfold_data_at 3%nat. entailer.
   cancel.
   destruct (zlt 64 (Zlength key)). omega. cancel. rewrite Zlength_correct in g. apply (Nat2Z.inj_ge 64) in g.
   clear H H0 TC0 h1.
   (*was: apply sepcon_derives.
       Focus 2. 
      erewrite data_at_array_at. unfold tuchars. apply derives_refl.
      reflexivity. omega. reflexivity.*)
  (*
   unfold_data_at 1%nat.
   cancel.*)
   rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.
     (*was:entailer.
     rewrite at_offset'_eq.
     2: simpl; rewrite Int.add_zero; reflexivity.*)
     remember (64 - Zlength key) as ZK64. 
     unfold nested_field_offset2, nested_field_type2; simpl.
     unfold tarray.
     (*was:erewrite (data_at_array_at Tsh tuchar 64 noattr).
     2: apply JMeq.JMeq_refl. 
     2: omega.
     2: reflexivity. 
     erewrite (split_offset_array_at _ _ _ 0 (Zlength key) 64); try reflexivity. 2: omega.
     entailer. unfold offset_val. rewrite Int.add_assoc. rewrite add_repr. rewrite (Zplus_comm 328).*)

     (*now:*) assert (F: field_address t_struct_hmac_ctx_st [StructField _key] (Vptr cb cofs) = Vptr cb (Int.add cofs (Int.repr 328))).
               unfold field_address, nested_field_offset2. simpl. 
              destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _key]
                 (Vptr cb cofs)); try contradiction. trivial.
              rewrite F; clear F.
     rewrite (data_at_Tarray_split3a Tsh tuchar 64 noattr (Zlength key)). 2: omega.
              simpl. unfold nat_of_Z. rewrite Zlength_correct, Nat2Z.id.
              specialize (split_offset_array_at (length key) Tsh tuchar 64). unfold tarray; intros SOA.
              rewrite SOA; try reflexivity; clear SOA.
      2: rewrite Zlength_correct, app_length, force_lengthn_length_n, Nat2Z.inj_add; omega.
      2: rewrite Zlength_correct in ge_64_l; omega.
      apply andp_right. entailer.
     assert (F64: false = (Zlength key >? 64)). 
       rewrite Z.gtb_ltb. symmetry. apply Fcore_Zaux.Zlt_bool_false. omega.
      rewrite sepcon_comm.
      apply sepcon_derives.
      { rewrite firstn_app1. 2: rewrite force_lengthn_length_n; trivial.
        rewrite firstn_precise. 2: rewrite force_lengthn_length_n; trivial.
        apply data_at_Tarray_ext_derives. intros i I.
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
      { rewrite skipn_force_lengthn_app. 
        unfold offset_val.
        rewrite Int.add_assoc, add_repr, (Zplus_comm 328), sizeof_tuchar, Zmult_1_l.
        rewrite HeqZK64, Zlength_correct. apply data_at_Tarray_ext_derives. intros i I.
        apply data_at_triv. unfold Znth. if_tac. trivial. clear H.
        destruct (zlt (Z.of_nat (length key)) 0).
        rewrite <- Zlength_correct in l. omega.
        rewrite nth_indep with (d:=(default_val tuchar))(d':=Vint (Int.repr 0)).
        Focus 2.  rewrite length_list_repeat. apply Z2Nat.inj_lt. omega. omega. omega.
        rewrite nth_list_repeat.
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
      }
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



















