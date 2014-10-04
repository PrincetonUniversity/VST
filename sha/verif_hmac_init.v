Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.spec_hmac.
Require Import HMAC_lemmas.

Require Import sha.hmac091c.

Require Import sha.verif_hmac_init_part1.

Lemma array_at_local_facts'':
  forall (t : type) (sh : Share.t) (f : Z -> reptype t) (lo hi : Z) (v : val),
  array_at t sh f lo hi v
  = array_at t sh f lo hi v && !!isptr v &&
      !!offset_in_range (sizeof t * lo) v &&
      !!offset_in_range (sizeof t * hi) v && !!align_compatible t v.
Proof. intros. apply pred_ext; normalize. apply andp_right; entailer.
  unfold array_at. entailer.
Qed. 

Lemma xor_pad_result: forall key i N z (isbyte_key : Forall isbyteZ key) (I : 0 <= i < 64)
        (HN : nth (Z.to_nat i) (map Vint (map Int.repr (HMAC_FUN.mkKey key))) Vundef =
              Vint N),
      ZnthV tuchar (map Vint (map Int.repr
           (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) (Byte.repr z)))) i =
      Vint (Int.zero_ext 8 (Int.xor (Int.repr z) N)).
Proof. intros. unfold cVint, ZnthV, upd. if_tac. omega. simpl.
            erewrite @nth_mapVint'.
            Focus 2. unfold HMAC_FUN.mkArgZ, HMAC_FUN.mkArg. 
                     repeat rewrite map_length. 
                     rewrite combine_length, length_SF, map_length, mkKey_length. simpl.
                     split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 64); omega.
            f_equal. 
              unfold HMAC_FUN.mkArgZ, HMAC_FUN.mkArg.
              eapply (@nthD_1 _ _ _ _ _ _ _ Int.zero) in HN.
              2: rewrite map_length, mkKey_length; apply (Z2Nat.inj_lt _ 64); omega.
              destruct HN as [zz [Inzz [NTH II]]]. inversion II; clear II; subst zz.
              eapply @nthD_1 in H1.
              2: rewrite mkKey_length; apply (Z2Nat.inj_lt _ 64); omega.
              destruct H1 as [yy [Inyy [NTH II]]]. 
              erewrite mapnth'. instantiate (1:=Byte.repr z). 2: reflexivity.
              erewrite mapnth'. instantiate (1:=(Byte.repr z, Byte.zero)).
              2: simpl; rewrite Byte.xor_zero; trivial.
              rewrite combine_nth.
              2: rewrite map_length, mkKey_length, length_SF; trivial.
              erewrite mapnth'. 2: reflexivity. (*instantiate (1:=0).*) rewrite NTH.
                unfold sixtyfour; rewrite nth_Nlist, Byte.xor_commut; simpl.
              2:  apply (Z2Nat.inj_lt _ 64); omega.
              assert (IB: Forall isbyteZ (HMAC_FUN.mkKey key)). 
               apply Forall_forall. unfold HMAC_FUN.mkKey; intros.
               destruct (Zlength key >? Z.of_nat SHA256_BlockSize). 
               specialize (zeropad_isbyteZ _ (isbyte_sha key)); intros.
               eapply Forall_forall; try eapply H1. assumption.
               specialize (zeropad_isbyteZ _ isbyte_key); intros.
               eapply Forall_forall; try eapply H1. assumption.
              eapply Forall_forall in IB; try eassumption.
             apply Int.same_bits_eq. intros. unfold Int.zero_ext. 
             repeat rewrite Int.testbit_repr; trivial.
             rewrite Int.Zzero_ext_spec; try omega. 
             if_tac. unfold Ipad.
               repeat rewrite Ztest_Bytetest. 
               assert (BZ: 0 <= i0 < Byte.zwordsize). unfold Byte.zwordsize; simpl. omega.            
               rewrite Byte.bits_xor; trivial.
               repeat rewrite Byte.testbit_repr; trivial.
               subst N. rewrite Ztest_Inttest, Int.bits_xor; trivial.
               repeat rewrite Int.testbit_repr; trivial.
             repeat rewrite Ztest_Bytetest. 
               apply Byte.bits_above. apply H1.
Qed.

Definition postResetHMS key (iS oS: s256state): hmacstate :=
  (emptySha, (iS, (oS, 
   (if zlt 64 (Zlength key) then Vint (Int.repr 32) else Vint (Int.repr (Zlength key)), 
   map Vint (map Int.repr (HMAC_FUN.mkKey key)))))).

Lemma body_hmac_init: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Init HMAC_Init_spec.
Proof.
start_function.
name ctx' _ctx.
name key' _key.
name len' _len.
simpl_stackframe_of.
destruct H as [KL1 [KL2 KL3]]. normalize.
(*
eapply semax_pre with (P':=PROP  (isptr k /\ Forall isbyteZ key /\ isptr c)
   LOCAL  (`(eq c) (eval_id _ctx); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   ((EX pad:_, 
            local (`(eq pad) (eval_var _pad (tarray tuchar 64))) && 
            `(data_at_ Tsh (tarray tuchar 64) pad));
   `(data_at_ Tsh t_struct_hmac_ctx_st c); `(data_block Tsh key k);
   `(K_vector KV))).
  entailer. apply exp_right with (x:=eval_var _pad (tarray tuchar 64) rho). 
  entailer. 
normalize. intros pad. normalize. 
apply isptrD in H. destruct H as [kb [kofs isptr_k]]; rewrite isptr_k in *.
apply isptrD in H1. destruct H1 as [cb [cofs isptr_c]]; rewrite isptr_c in *.
rename H0 into isbyte_key.
*)
(*Sset _reset (Econst_int (Int.repr 0) tint)*)
forward.

unfold data_block. normalize. 

(*isolate branch if (key != NULL) *)
apply seq_assoc.

remember (EX  cb : block,
                 (EX  cofs : int,
                  (EX  pad : val,
                   (EX  r : Z,
                    PROP  (c = Vptr cb cofs/\ (r=0 \/ r=1))
                    LOCAL  (`(eq (Vint (Int.repr r))) (eval_id _reset);
                    `(eq pad) (eval_var _pad (tarray tuchar 64));
                    `(eq c) (eval_id _ctx); `(eq k) (eval_id _key);
                    `(eq (Vint (Int.repr l))) (eval_id _len);
                    `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
                    SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                    `(initPostKeyNullConditional r c k h1 key);
                    `(K_vector KV)))))) as PostKeyNull. 
forward_seq. instantiate (1:= PostKeyNull). (*eapply semax_seq.*)
{ assert (DD: Delta = initialized _i (initialized _j (initialized _reset 
               (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs)))).
     admit. (*TODO: Andrew*)
  rewrite DD. clear DD.
  eapply hmac_init_part1; eassumption.
}
(* Proof of  hmac_init_part1: forward_if PostKeyNull.
  { (* THEN*)
    simpl. 
    unfold force_val2, force_val1; simpl. 
    eapply semax_pre with (P':=
      (PROP  ()
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
      entailer. simpl. (*unfold typed_true. normalize.*) cancel.

    forward. (*reset =1 *)
    forward. (*j=HMAC_MAX_MD_CBLOCK*)
    simpl.

    remember
     (PROP  ()
      LOCAL  (
       `(eq (Vint (Int.repr 1))) (eval_id _reset);
       `(eq pad) (eval_var _pad (tarray tuchar 64)); `(eq c) (eval_id _ctx);
       `(eq k) (eval_id _key); `(eq (Vint (Int.repr l))) (eval_id _len);
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
          `(eq pad) (eval_var _pad (tarray tuchar 64)); `(eq c) (eval_id _ctx);
          `(eq k) (eval_id _key); `(eq (Vint (Int.repr l))) (eval_id _len);
          `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
        SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
              `(data_at_ Tsh t_struct_hmac_ctx_st c);
              `(K_vector KV);
              `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) k)))).
        entailer. 
      normalize. rename H into lt_64_l. 

      (*call to SHA256_init*)
      eapply semax_seq'.
      frame_SEP 1.
      unfold data_at_.
      unfold_data_at 1%nat.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_md_ctx]); try reflexivity.
      normalize. 
      rename H into SCc. rename H0 into ACc.
      rewrite isptr_c; simpl.
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
      after_call. rewrite isptr_c; simpl. 
      normalize.

      (*call to SHA256_Update*)
      erewrite (split_offset_array_at _ _ _ 0 l); try reflexivity. 2: subst l; omega.
      normalize.
      rewrite isptr_k in H, H0. simpl in H, H0. rewrite Zplus_0_r in H.
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
   LOCAL  (tc_environ Delta; tc_environ Delta;
   `(eq (Vint (Int.repr 1))) (eval_id _reset);
   `(eq pad) (eval_var _pad (tarray tuchar 64));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(fun a : environ =>
      (PROP  (update_abs (firstn (Z.to_nat l) key) init_s256abs xx)
       LOCAL ()
       SEP  (`(K_vector KV); `(sha256state_ xx (Vptr cb cofs));
       `(data_block Tsh key (Vptr kb kofs)))) a) globals_only;
   `(array_at tuchar Tsh (fun i : Z => tuchars (map Int.repr key) (i + l)) 0
       (Zlength key - l) (offset_val (Int.repr l) k));
   `(field_at Tsh t_struct_hmac_ctx_st [_key_length] Vundef (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_key] [] (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx]
       ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx]
       ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
   `(data_at_ Tsh (tarray tuchar 64) pad)))).
       entailer. rename x into a. apply exp_right with (x:=a).
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
              (Zlength key - l) (offset_val (Int.repr l) k));
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
                  clear - H5; destruct H5 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
                  apply YY. omega. omega.
               unfold HMAC_FUN.mkKey. simpl.
               assert (Kgt: Zlength key > 64) by omega.
               apply Zgt_is_gt_bool in Kgt.
               rewrite Kgt. unfold HMAC_FUN.zeroPad. repeat rewrite map_app.
               rewrite app_nth2; repeat rewrite map_length; rewrite length_SHA256'.
                 remember (Nlist 0 (SHA256_BlockSize - Z.to_nat SHA256_DIGEST_LENGTH)) as NL.
                 simpl.
                 assert (I: (Z.to_nat (i + 32) - 32)%nat = Z.to_nat i).
                             destruct H5. specialize (Z2Nat.inj_sub (i+32) 32).
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
                  clear - H5; destruct H5 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
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
          `(eq pad) (eval_var _pad (tarray tuchar 64)); `(eq c) (eval_id _ctx);
          `(eq k) (eval_id _key); `(eq (Vint (Int.repr l))) (eval_id _len);
          `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
        SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
              `(data_at Tsh t_struct_hmac_ctx_st (default_val t_struct_hmac_ctx_st) c);
              `(K_vector KV);
              `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) k)))).
        entailer. 
     normalize. rename H into ge_64_l. 

     (*call to memcpy*)
     (*eapply semax_seq'.*)
     focus_SEP 1 3.
     (*unfold data_at_. *)
     unfold_data_at 1%nat.
     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
     normalize. 
     rename H into SCc. rename H0 into ACc.
     rewrite isptr_c; simpl.
     rewrite at_offset_data_at. unfold nested_field_type2, nested_field_offset2; simpl.
     unfold tarray.
     erewrite data_at_array_at. 2: apply JMeq.JMeq_refl. 2: omega. 2: reflexivity.
     erewrite (split_offset_array_at _ _ _ 0 l 64); try reflexivity. 2: omega.
     normalize.
     rename H into OIR0_328. rename H0 into OIR64_328.

     unfold tuchars. remember (64 - l) as l64.
     remember ((Tsh, Tsh), Vptr cb (Int.add cofs (Int.repr 328)), 
             k, mkTrep (Tarray tuchar (Zlength key) noattr) 
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
         assert ( match Zlength key with
                     | 0 => 0
                     | Z.pos y' => Z.pos y'
                     | Z.neg y' => Z.neg y'
                 end = Zlength key).
            destruct (Zlength key); reflexivity.
       rewrite H0; clear H0.  
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
              CONT k);
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
                  clear - H0; destruct H0 as [XX YY]. rewrite Zlength_correct, Z2Nat.inj_lt in YY.
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
           destruct H0. 
           apply (Z2Nat.inj_lt (i+ Zlength key) 64). omega. omega. omega.
         rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Z0). f_equal.
         rewrite (mkKey_right _ F64 (i + Zlength key)); trivial. omega. trivial.
         rewrite map_length; trivial.
  }

  intros. entailer. unfold POSTCONDITION, abbreviate; simpl. entailer.
  }
  { (*key == NULL*)
     forward.
     entailer.
  }
  { (*side condition of forward_if key != NULL*)
    intros. entailer. unfold overridePost, normal_ret_assert; simpl. 
    if_tac. simpl. entailer. simpl. entailer.
  }
}
*)

subst PostKeyNull. normalize.
apply extract_exists_pre; intros cb. 
apply extract_exists_pre; intros cofs. 
apply extract_exists_pre; intros pad. 
apply extract_exists_pre; intros r.
normalize. rename H into HC; rewrite HC. rename H0 into R.

(*isolate branch if (reset) *)
apply seq_assoc.

Definition initPostResetConditional r (c:val) (k: val) h key iS oS: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 then hmacstate_PreInitNull key h c else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF
                  else !!(Forall isbyteZ key) &&
                       ((data_at Tsh t_struct_hmac_ctx_st (postResetHMS key iS oS) c) *
                        (array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) (Vptr b ofs)))
  | _ => FF
  end.

remember (EX iSA:_, EX iS:_, EX oSA:_, EX oS:_,
          PROP  (innerShaInit (map Byte.repr (HMAC_FUN.mkKey key)) iSA /\ s256_relate iSA iS /\
                 outerShaInit (map Byte.repr (HMAC_FUN.mkKey key)) oSA /\ s256_relate oSA oS)
                 LOCAL  (
                 `(eq pad) (eval_var _pad (tarray tuchar 64));
                 `(eq (Vptr cb cofs)) (eval_id _ctx);
                 `(eq k) (eval_id _key);
                 `(eq (Vint (Int.repr l))) (eval_id _len);
                 `(eq KV) (eval_var sha._K256 (tarray tuint 64)))

                 SEP  (
                 `(array_at_ tuchar Tsh 0 64 pad); 
                 `(initPostResetConditional r c k h1 key iS oS);
(*                 `(data_at Tsh t_struct_hmac_ctx_st (postResetHMS key iS oS)
                     (Vptr cb cofs));
                 `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0
                     (Zlength key) (Vptr kb kofs));*) `(K_vector KV)))
  as PostResetBranch.
(*forward_seq. instantiate (1:= PostResetBranch).*)
eapply semax_seq. instantiate (1:=PostResetBranch).
{ forward_if PostResetBranch. 
  { (* THEN*)
    remember (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey key)) Ipad)))))) as IPADcont.
    remember (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_FUN.mkArg (map Byte.repr (HMAC_FUN.mkKey key)) Opad)))))) as OPADcont.
    assert (ZLI: Zlength (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Ipad) = 64).
            rewrite Zlength_mkArgZ.
            repeat rewrite map_length. rewrite mkKey_length.
            unfold SHA256_BlockSize; simpl. trivial. 
    assert (ZLO: Zlength (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Opad) = 64).
            rewrite Zlength_mkArgZ.
            repeat rewrite map_length. rewrite mkKey_length.
            unfold SHA256_BlockSize; simpl. trivial. 
    remember (ZnthV tuchar (default_val (Tarray tuchar 64 noattr))) as DEFAULTcont.
    unfold data_at_, tuchars, tarray.
    erewrite data_at_array_at; try reflexivity. 2: omega.
    rewrite array_at_isptr. normalize. apply isptrD in H. destruct H as [pb [pofs Hpad]]. subst pad.
    apply semax_pre with (P':=PROP  (r<>0 /\ Forall isbyteZ key)
         LOCAL  (tc_environ Delta;
            `(eq (Vint (Int.repr r))) (eval_id _reset);
            `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
            `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq k) (eval_id _key);
            `(eq (Vint (Int.repr l))) (eval_id _len);
            `(eq KV) (eval_var sha._K256 (Tarray tuint 64 noattr)))
         SEP  (`(K_vector KV);
               `(array_at tuchar Tsh (ZnthV tuchar (default_val (Tarray tuchar 64 noattr)))
                   0 64 (Vptr pb pofs));
               `(data_at Tsh t_struct_hmac_ctx_st (keyedHMS key) (Vptr cb cofs));
               `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) k))).
    { clear HeqPostResetBranch PostResetBranch.
      unfold initPostKeyNullConditional. entailer.
      destruct key'; try contradiction.
      (*integer, ie key==NULL*)
          simpl in TC0. subst i. simpl. if_tac. subst r. inversion H0.
          apply andp_right. entailer. entailer.
      (*key == Vptr*)
       if_tac. subst r.
          unfold typed_true in H0. simpl in H0. inversion H0.
          entailer. cancel.
    }
    rewrite (array_at_isptr _ _ _ _ _ k). normalize.
    destruct R; subst r. omega. clear H. 
    rename H0 into isbyte_key.
    apply isptrD in H1; destruct H1 as [kb [kofs HK]]; rewrite HK in *.
    
    forward_seq. 
    instantiate (1:= 
      (PROP  ()
       LOCAL  (
        `(eq (Vint (Int.repr 1))) (eval_id _reset);
        `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
        `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq k) (eval_id _key);
        `(eq (Vint (Int.repr l))) (eval_id _len);
        `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
       SEP 
        (`(array_at tuchar Tsh IPADcont 0 64 (Vptr pb pofs));
         `(data_at Tsh t_struct_hmac_ctx_st (keyedHMS key) (Vptr cb cofs));
         `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) (Vptr kb kofs));
        `(K_vector KV)))).
    { (*ipad loop*)
      forward_for_simple_bound' 64 (EX i:Z, 
        (PROP  ()
         LOCAL  (`(eq (Vint (Int.repr 1))) (eval_id _reset);
                 `(eq (Vptr pb pofs)) (eval_var _pad (tarray tuchar 64));
                 `(eq (Vptr cb cofs)) (eval_id _ctx);
                 `(eq (Vptr kb kofs)) (eval_id _key);
                 `(eq (Vint (Int.repr l))) (eval_id _len);
                 `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP  (
          `(array_at tuchar Tsh IPADcont 0 i (Vptr pb pofs));
          `(array_at tuchar Tsh DEFAULTcont i 64 (Vptr pb pofs));
          `(data_at Tsh t_struct_hmac_ctx_st (keyedHMS key) (Vptr cb cofs));
          `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr key))) 0
               (Zlength key) (Vptr kb kofs)); `(K_vector KV)))).
      { (*precondition implies "invariant"*) 
        rewrite array_at_emp. normalize. 
        rewrite array_at_local_facts''. entailer. cancel.
      }
      { unfold normal_ret_assert. simpl. intros rho. 
        rewrite array_at_emp. entailer.
      }
      { unfold_data_at 1%nat. normalize.
        rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
        normalize. rename H into I. rename H0 into SCc. rename H1 into ACc.
        rewrite at_offset'_eq.
        2: simpl; rewrite Int.add_zero; reflexivity.
        eapply semax_pre0; [ apply now_later | ].
        eapply semax_post_flipped'.
        { subst PostResetBranch.
          remember (ZnthV tuchar (map Vint (map Int.repr (HMAC_FUN.mkKey key))) i) as CONTi.
          unfold ZnthV in CONTi. destruct (nth_mapVintZ i (HMAC_FUN.mkKey key)) as [N HN].
              rewrite Zlength_correct, mkKey_length. unfold SHA256_BlockSize; simpl. 
               assumption.            
          assert (Hres: ZnthV tuchar (map Vint (map Int.repr
                   (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Ipad))) i
              = Vint (Int.zero_ext 8 (Int.xor (Int.repr 54) N))). 
          { clear - HN I isbyte_key. apply xor_pad_result; assumption. }
          eapply NEWsemax_loadstore_array
          with (P:= nil)
          (Q:= [`(eq (Vint (Int.repr i))) (eval_id _i);
            `(eq (Vint (Int.repr 64))) (eval_expr (Econst_int (Int.repr 64) tint));
            `(eq (Vint (Int.repr 1))) (eval_id _reset);
            `(eq (Vptr pb pofs)) (eval_var _pad (tarray tuchar 64));
            `(eq (Vptr cb cofs)) (eval_id _ctx);
            `(eq (Vptr kb kofs)) (eval_id _key);
            `(eq (Vint (Int.repr l))) (eval_id _len);
            `(eq KV) (eval_var sha._K256 (tarray tuint 64))])
          (R:= [`(field_at Tsh t_struct_hmac_ctx_st [_key_length]
               (if zlt 64 (Zlength key)
                then Vint (Int.repr 32)
                else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
            `(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [_key])
                (map Vint (map Int.repr (HMAC_FUN.mkKey key)))
               (offset_val
                 (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_key]))
                 (Vptr cb cofs)));
            `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx] emptySha (Vptr cb cofs));
            `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx] emptySha (Vptr cb cofs));
            `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] emptySha (Vptr cb cofs));
            `(array_at tuchar Tsh IPADcont 0 i (Vptr pb pofs));
            `(array_at tuchar Tsh DEFAULTcont i 64 (Vptr pb pofs));
            `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr key))) 0
                (Zlength key) (Vptr kb kofs)); `(K_vector KV)])
          (n:=6%nat)
          (v2:=(ZnthV tuchar (map Vint(map Int.repr (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Ipad))) i)).
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          Focus 2. simpl. unfold value, nested_field_type2, t_struct_hmac_ctx_st; simpl.
            reflexivity.
          2: trivial.     
          instantiate (1:=i). unfold nested_field_offset2, _struct_SHA256state_st; simpl.
          intros rho. normalize.
           apply andp_right. apply andp_right; rel_expr.
           rewrite Hres.
           erewrite (data_at_type_changable Tsh _ (tarray tuchar 64)); try reflexivity.
           unfold tarray. 
           erewrite data_at_array_at; try reflexivity.
           erewrite (split3_array_at' i); try reflexivity. 2: trivial. 2: omega.
           {  rel_expr.  instantiate (1:=cofs). instantiate (1:=cb).
              rel_expr.
                  admit. (*relexpr*)
             unfold nested_field_offset2, _struct_SHA256state_st; simpl.
              instantiate (2:=Tsh). unfold add_ptr_int. simpl.
              instantiate (1:=(ZnthV tuchar (map Vint (map Int.repr (HMAC_FUN.mkKey key))) i)).
              cancel.
             unfold ZnthV in *. if_tac. omega. simpl; rewrite HN. discriminate.
             simpl; intros.
                unfold ZnthV in *. if_tac. omega. simpl; rewrite HN. reflexivity.
             reflexivity.
           } 
          unfold tuchar; simpl. apply ZnthV_map_Vint_is_int. rewrite Zlength_correct in ZLI.
            rewrite Zlength_correct, map_length, ZLI. assumption.
          red. omega.
        }
        { entailer. cancel.
          rewrite (split_array_at (i+1) tuchar Tsh _ i 64); try omega. cancel.
          unfold_data_at 2%nat. cancel.
          rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
          entailer.
          rewrite at_offset'_eq.
          2: simpl; rewrite Int.add_zero; reflexivity. unfold offset_val. cancel.
          apply sepcon_derives.
            rewrite (split_array_at i tuchar Tsh _ 0 (i+1)); try omega.
            cancel.
            apply array_lemmas.array_at_ext'.
            unfold cVint, ZnthV; simpl; intros.
            assert (i0=i). omega. subst i0. simpl.
            destruct (zlt i 0). omega. simpl. rewrite upd_eq.
            destruct (nth_mapVintZ i 
             (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Ipad)) as [n Hn].
             rewrite ZLI; assumption.
            rewrite Hn. unfold HMAC_FUN.mkArgZ in Hn; rewrite Hn. trivial.
          apply array_lemmas.array_at_ext'.
            unfold cVint, ZnthV; simpl; intros. rewrite upd_neq; trivial. omega.
        } 
      }
    }

    (*continuation after ipad-loop*)   
    unfold_data_at 1%nat. normalize.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_i_ctx]); try reflexivity. normalize.
    rewrite at_offset'_eq.
    2: simpl; rewrite Int.add_zero; reflexivity.
    eapply semax_seq'.
    frame_SEP 3.
    forward_call (Vptr cb (Int.add cofs (Int.repr 108))).
    { assert (FR: Frame = nil).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      entailer. 
    }
    after_call. simpl. normalize. 

    eapply semax_seq'.
    frame_SEP 0 5 7.
    remember (init_s256abs, 
            HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Ipad,
            Vptr cb (Int.add cofs (Int.repr 108)),
            Vptr pb pofs, Tsh, 64, KV) as WITNESS.
    forward_call WITNESS.
    { assert (FR: Frame = nil).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      subst WITNESS. entailer.
      unfold data_block. rewrite ZLI. cancel.
      entailer.
      apply andp_right. 
        simpl. apply prop_right. apply isbyte_map_ByteUnsigned.
      apply array_lemmas.array_at_ext'.
      unfold tuchars, cVint, ZnthV; simpl. intros. if_tac. omega. simpl. 
      destruct (nth_mapVintZ i 
           (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Ipad)) as [n Hn].
        rewrite ZLI; assumption.
      rewrite Hn. unfold HMAC_FUN.mkArgZ in Hn; rewrite Hn. trivial.
    }
    after_call. simpl. intros rho. subst WITNESS. rewrite firstn_precise. normalize.
      unfold HMAC_FUN.mkArgZ, HMAC_FUN.mkArg. repeat rewrite map_length.
      unfold sixtyfour. rewrite combine_length, map_length, length_Nlist, mkKey_length.
      unfold SHA256_BlockSize; simpl. trivial.

    simpl.
    apply semax_pre with (P':=EX x : s256abs,
     (PROP  ()
     LOCAL  (tc_environ Delta; tc_environ Delta;
       `(eq (Vint (Int.repr 1))) (eval_id _reset);
       `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
       `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
       `(eq (Vint (Int.repr l))) (eval_id _len);
       `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
     SEP 
      (`(fun a : environ =>
      (PROP 
       (update_abs
          (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Ipad)
          init_s256abs x)
       LOCAL ()
       SEP  (`(K_vector KV);
       `(sha256state_ x (Vptr cb (Int.add cofs (Int.repr 108))));
       `(data_block Tsh
           (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Ipad)
           (Vptr pb pofs)))) a) globals_only;
      `(field_at Tsh t_struct_hmac_ctx_st [_key_length]
          (if zlt 64 (Zlength key)
           then Vint (Int.repr 32)
           else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
      `(field_at Tsh t_struct_hmac_ctx_st [_key]
          (map Vint (map Int.repr (HMAC_FUN.mkKey key))) (Vptr cb cofs));
      `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx] emptySha (Vptr cb cofs));
      `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] emptySha (Vptr cb cofs));
      `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
         (Vptr kb kofs))))).
    entailer. rename x into a. eapply exp_right with (x:=a). entailer.
    apply extract_exists_pre. intros ipadSHAabs.
    rename H into SCc.
    rename H0 into ACc.
    normalize. simpl. normalize. rename H into ipadAbs_def.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_o_ctx]); try reflexivity.
    normalize.
    rewrite at_offset'_eq.
    2: simpl; rewrite Int.add_zero; reflexivity. unfold offset_val; simpl.

    (*essentially the same for opad*)
    forward_seq.
    instantiate (1:= 
  (PROP  ()
   LOCAL  (tc_environ Delta; tc_environ Delta;
   `(eq (Vint (Int.repr 1))) (eval_id _reset);
   `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP  (`(K_vector KV);
   `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
   `(data_block Tsh
       (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Opad)
       (Vptr pb pofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_key_length]
       (if zlt 64 (Zlength key)
        then Vint (Int.repr 32)
        else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_key]
       (map Vint (map Int.repr (HMAC_FUN.mkKey key))) (Vptr cb cofs));
   `(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [_o_ctx]) emptySha
       (Vptr cb
          (Int.add cofs
             (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_o_ctx])))));
   `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] emptySha (Vptr cb cofs));
   `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
       (Vptr kb kofs))))). 
    { (*opad loop*)
      forward_for_simple_bound' 64 (EX i:Z, 
  (PROP  ()
   LOCAL  (`(eq (Vint (Int.repr 1))) (eval_id _reset);
                 `(eq (Vptr pb pofs)) (eval_var _pad (tarray tuchar 64));
                 `(eq (Vptr cb cofs)) (eval_id _ctx);
                 `(eq (Vptr kb kofs)) (eval_id _key);
                 `(eq (Vint (Int.repr l))) (eval_id _len);
                 `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP  (`(K_vector KV);
   `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
   `(array_at tuchar Tsh OPADcont 0 i (Vptr pb pofs));
   `(array_at tuchar Tsh IPADcont i 64 (Vptr pb pofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_key_length]
       (if zlt 64 (Zlength key)
        then Vint (Int.repr 32)
        else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_key]
       (map Vint (map Int.repr (HMAC_FUN.mkKey key))) (Vptr cb cofs));
   `(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [_o_ctx]) emptySha
       (Vptr cb
          (Int.add cofs
             (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_o_ctx])))));
   `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] emptySha (Vptr cb cofs));
   `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
       (Vptr kb kofs))))).
      { (*precondition implies "invariant"*)
        rewrite array_at_emp. unfold data_block. normalize. entailer. 
        apply andp_right.
          unfold array_at. normalize. rewrite ZLI in *. destruct H5.  destruct H7.
            simpl in *. apply prop_right. omega.
        cancel. rewrite ZLI. 
            apply array_lemmas.array_at_ext'. 
            unfold tuchars, cVint, ZnthV; simpl. intros. destruct (zlt i 0). omega.
            destruct (nth_mapVintZ i 
             (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Ipad)) as [n Hn].
            rewrite ZLI. assumption.
            rewrite Hn. unfold HMAC_FUN.mkArgZ in Hn; rewrite Hn. trivial.            
      }
      { unfold normal_ret_assert, data_block. simpl. intros rho. 
        rewrite array_at_emp. entailer.
        apply andp_right. apply prop_right. apply isbyte_map_ByteUnsigned.
        cancel. unfold tuchars. rewrite ZLO.
            apply array_lemmas.array_at_ext'. 
            unfold tuchars, cVint, ZnthV; simpl. intros. destruct (zlt i 0). omega.
            destruct (nth_mapVintZ i 
             (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Opad)) as [n Hn].
            rewrite ZLO. assumption. rewrite Hn. unfold HMAC_FUN.mkArgZ in Hn; rewrite Hn. trivial.
      }
      { (*unfold_data_at 1%nat. normalize.*)
        rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
        normalize. rename H into I. 
        rewrite at_offset'_eq.
        2: simpl; rewrite Int.add_zero; reflexivity.
        eapply semax_pre0; [ apply now_later | ].
        eapply semax_post_flipped'.
        { subst PostResetBranch.
          remember (ZnthV tuchar (map Vint (map Int.repr (HMAC_FUN.mkKey key))) i) as CONTi.
          unfold ZnthV in CONTi. destruct (nth_mapVintZ i (HMAC_FUN.mkKey key)) as [N HN].
              rewrite Zlength_correct, mkKey_length. unfold SHA256_BlockSize; simpl. 
               assumption.
          assert (Hres: ZnthV tuchar (map Vint (map Int.repr
                   (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Opad))) i
              = Vint (Int.zero_ext 8 (Int.xor (Int.repr 92) N))). 
          { clear - HN I isbyte_key. apply xor_pad_result; assumption. }
          eapply NEWsemax_loadstore_array
          with (P:= nil)
          (Q:= [`(eq (Vint (Int.repr i))) (eval_id _i);
            `(eq (Vint (Int.repr 64))) (eval_expr (Econst_int (Int.repr 64) tint));
            `(eq (Vint (Int.repr 1))) (eval_id _reset);
            `(eq (Vptr pb pofs)) (eval_var _pad (tarray tuchar 64));
            `(eq (Vptr cb cofs)) (eval_id _ctx);
            `(eq (Vptr kb kofs)) (eval_id _key);
            `(eq (Vint (Int.repr l))) (eval_id _len);
            `(eq KV) (eval_var sha._K256 (tarray tuint 64))])
          (R:= [`(K_vector KV);
     `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
     `(array_at tuchar Tsh OPADcont 0 i (Vptr pb pofs));
     `(array_at tuchar Tsh IPADcont i 64 (Vptr pb pofs));
     `(field_at Tsh t_struct_hmac_ctx_st [_key_length]
         (if zlt 64 (Zlength key)
          then Vint (Int.repr 32)
          else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
     `(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [_key])
         (map Vint (map Int.repr (HMAC_FUN.mkKey key)))
         (offset_val
            (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_key]))
            (Vptr cb cofs)));
     `(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [_o_ctx])
         emptySha
         (Vptr cb
            (Int.add cofs
               (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_o_ctx])))));
     `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] emptySha (Vptr cb cofs));
     `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
         (Vptr kb kofs))])
          (n:=3%nat)
          (v2:=(ZnthV tuchar (map Vint(map Int.repr (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Opad))) i)).
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          Focus 2. simpl. unfold value, nested_field_type2, t_struct_hmac_ctx_st; simpl.
            reflexivity.
          2: trivial.
          instantiate (1:=i). unfold nested_field_offset2, _struct_SHA256state_st; simpl.
          intros rho. normalize.
           apply andp_right. apply andp_right; rel_expr.
           rewrite Hres.
           erewrite (data_at_type_changable Tsh _ (tarray tuchar 64)); try reflexivity.
           unfold tarray. 
           erewrite data_at_array_at; try reflexivity.
           erewrite (split3_array_at' i _ _ _ 0 64); try reflexivity. 2: trivial. 2: omega.
           { rel_expr. 
              instantiate (1:=cofs). instantiate (1:=cb). admit. (*relexpr*)
             unfold nested_field_offset2, _struct_SHA256state_st; simpl.
              instantiate (2:=Tsh). unfold add_ptr_int. simpl.
              instantiate (1:=(ZnthV tuchar (map Vint (map Int.repr (HMAC_FUN.mkKey key))) i)).
              cancel.
             unfold ZnthV in *. if_tac. omega. simpl; rewrite HN. discriminate.
             simpl; intros.
                unfold ZnthV in *. if_tac. omega. simpl; rewrite HN. reflexivity.
             reflexivity.
           } 
          unfold tuchar; simpl. apply ZnthV_map_Vint_is_int. rewrite Zlength_correct in ZLO.
            rewrite Zlength_correct, map_length, ZLO. assumption.
          red. omega.
        }
        { entailer. cancel.
          rewrite (split_array_at (i+1) tuchar Tsh _ i 64); try omega. cancel.
          unfold_data_at 1%nat. cancel.
          rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
          rewrite at_offset'_eq.
            2: simpl; rewrite Int.add_zero; reflexivity. unfold offset_val.
          unfold_data_at 1%nat. entailer. cancel.
          apply sepcon_derives.
            rewrite (split_array_at i tuchar Tsh _ 0 (i+1)); try omega.
            cancel.
            apply array_lemmas.array_at_ext'.
            unfold cVint, ZnthV; simpl; intros.
            assert (i0=i). omega. subst i0. simpl.
            destruct (zlt i 0). omega. simpl. rewrite upd_eq.
            destruct (nth_mapVintZ i 
             (HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Opad)) as [n Hn].
              rewrite ZLO; assumption.
            rewrite Hn. unfold HMAC_FUN.mkArgZ in Hn; rewrite Hn. trivial.
          apply array_lemmas.array_at_ext'.
            unfold cVint, ZnthV; simpl; intros. rewrite upd_neq; trivial. omega.
        } 
      }
    }

    (*continuation after opad-loop*)   
    (*unfold_data_at 1%nat.*) (*normalize.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_o_ctx]); try reflexivity. normalize.
    rewrite at_offset'_eq.
    2: simpl; rewrite Int.add_zero; reflexivity.*)
    eapply semax_seq'.
    frame_SEP 5.
    forward_call (Vptr cb (Int.add cofs (Int.repr 216))).
    { assert (FR: Frame = nil).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      entailer. 
    }
    after_call. simpl. normalize.

    unfold MORE_COMMANDS, abbreviate. (*WHY IS THIS NOT DONE AUTOMATICALLY?*)
(*    make_sequential.
    frame_SEP 0 1 3.*)
    remember (init_s256abs, 
            HMAC_FUN.mkArgZ (map Byte.repr (HMAC_FUN.mkKey key)) Opad,
            Vptr cb (Int.add cofs (Int.repr 216)),
            Vptr pb pofs, Tsh, 64, KV) as WITNESS.
    forward_call WITNESS.
    { assert (FR: Frame = [
         `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
         `(field_at Tsh t_struct_hmac_ctx_st [_key_length]
              (if zlt 64 (Zlength key)
               then Vint (Int.repr 32)
               else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [_key]
              (map Vint (map Int.repr (HMAC_FUN.mkKey key))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] emptySha (Vptr cb cofs));
         `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
              (Vptr kb kofs))]). 
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      subst WITNESS. entailer. cancel.
    }
    after_call. simpl. intros rho. subst WITNESS PostResetBranch.
        rewrite firstn_precise. entailer.
        rename x into opadSHAabs.
        unfold sha256state_; normalize. rename r into iUpd. rename x into oUpd.
        apply exp_right with (x:=ipadSHAabs). entailer.
        apply exp_right with (x:=iUpd). entailer.
        apply exp_right with (x:=opadSHAabs). entailer.
        apply exp_right with (x:=oUpd). entailer.
        unfold data_block, initPostResetConditional. simpl.
        rewrite ZLO. entailer. cancel.
        unfold_data_at 3%nat. cancel.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_i_ctx]); try reflexivity.
    entailer.
    rewrite at_offset'_eq.
    2: simpl; rewrite Int.add_zero; reflexivity. unfold offset_val; simpl.

    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_o_ctx]); try reflexivity.
    entailer.
    rewrite at_offset'_eq.
    2: simpl; rewrite Int.add_zero; reflexivity. unfold offset_val; simpl.

    cancel.

      unfold HMAC_FUN.mkArgZ, HMAC_FUN.mkArg. repeat rewrite map_length.
      unfold sixtyfour. rewrite combine_length, map_length, length_Nlist, mkKey_length.
      unfold SHA256_BlockSize; simpl. trivial.
  }
  { (*ELSE*) 
    forward. unfold overridePost. simpl. intros rho. apply andp_right. apply prop_right. trivial.
    subst. unfold initPostKeyNullConditional; simpl. entailer.
    rewrite <- H1 in *; simpl in *. unfold typed_false in H0. simpl in H0.
        inversion H0; clear H0. apply negb_false_iff in H6.
        apply eq_sym in H6; apply binop_lemmas.int_eq_true in H6.
    destruct R; subst. simpl.
      remember (eval_id _key rho) as k. destruct k; entailer. 
      remember (Int.eq i Int.zero) as d. destruct d. 2: entailer.
      unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
      destruct h1; entailer.
       destruct H10 as [ii [KLi [KLunsig [SF [ISHA OSHA]]]]].
       apply exp_right with (x:= iSha). 
       apply exp_right with (x:= (iCtx r)).
       apply exp_right with (x:= oSha).
       apply exp_right with (x:= (oCtx r)).
       entailer. rewrite <- Heqd. cancel.
       unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
       apply sepcon_derives. unfold tarray. rewrite data_at__array_at_. cancel. omega. reflexivity.        
       apply exp_right with (x:= r). apply exp_right with (x:=v).
       entailer. apply prop_right. exists ii; eauto.
     simpl. apply Int.one_not_zero in H6. contradiction.
   } 
}
{ (*Continuation after if (reset*)
  subst PostResetBranch.
simpl update_tycon.
apply semax_extensionality_Delta with (Delta). apply expr_lemmas.tycontext_sub_refl.
  apply extract_exists_pre; intros iSA. 
  apply extract_exists_pre; intros iS. 
  apply extract_exists_pre; intros oSA. 
  apply extract_exists_pre; intros oS. unfold initPostResetConditional.
  normalize. 
  rename H into INNER. rename H0 into InnerRelate.
  rename H1 into OUTER. rename H2 into OuterRelate.
  unfold initPostResetConditional; rewrite HC.
  destruct k;
    try solve [apply semax_pre with (P':=FF); try entailer; try apply semax_ff].
  { (*k is integer, ie key==null*)
     destruct (Int.eq i Int.zero). 
     Focus 2. apply semax_pre with (P':=FF); try entailer; try apply semax_ff.
     destruct R; subst r; simpl.
     Focus 2. apply semax_pre with (P':=FF); try entailer; try apply semax_ff.
     unfold hmacstate_PreInitNull; simpl. normalize.
     intros s. normalize. intros v. normalize. rename H into Hs.
     unfold hmac_relate_PreInitNull in Hs. 
     clear INNER InnerRelate OUTER OuterRelate iSA iS oSA oS.
     destruct h1.
     destruct Hs as [XX [IREL [OREL [ILEN [OLEN [KK [ii [KLii [KL [HH1 [HH2 HH3]]]]]]]]]]].
     subst key0. destruct s as [mdS [iS [oS [kl K]]]]. simpl in *. subst kl K.
     unfold_data_at 1%nat.
     (* eapply semax_seq'.
     frame_SEP 3 4.*)
     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_md_ctx]); try reflexivity.
     normalize.
     rename H into SCc. rename H0 into ACc.
     rewrite at_offset'_eq.
     2: simpl; rewrite Int.add_zero; reflexivity.
     remember ((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS) as  WITNESS.
     forward_call WITNESS.
     { assert (FR: Frame = [
          `(field_at Tsh t_struct_hmac_ctx_st [_key_length] (Vint ii) (Vptr cb cofs)); 
          `(field_at Tsh t_struct_hmac_ctx_st [_key]
               (map Vint (map Int.repr (HMAC_FUN.mkKey key))) (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx] oS (Vptr cb cofs));
          `(array_at_ tuchar Tsh 0 64 pad); `(K_vector KV)]).
          subst Frame. reflexivity.
       rewrite FR. clear FR Frame. 
       subst WITNESS. entailer. cancel.
       apply sepcon_derives. 
         rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_i_ctx]); try reflexivity.
         rewrite at_offset'_eq. unfold offset_val. normalize.
         simpl; rewrite Int.add_zero; reflexivity.
       eapply derives_trans.
         apply data_at_data_at_. reflexivity. 
         rewrite <- memory_block_data_at_; try reflexivity. entailer.
     }
     after_call. subst WITNESS. normalize. subst retval0. simpl. 

     forward. (*return*)
     unfold hmacInit. 
     remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
     apply exp_right with (x:=HMACabs iSha iSha oSha KL key).   
     entailer.
     apply andp_right. 
       apply prop_right. exists iSha, oSha.
       rewrite Int.unsigned_repr. auto.
       rewrite int_max_signed_eq  in KL2. rewrite int_max_unsigned_eq.
       destruct (zlt 64 (Zlength key)); omega.     
     simpl_stackframe_of. unfold tarray. 
     rewrite <- data_at__array_at_ with (a:=noattr).
     2: omega. 2: reflexivity.
     cancel.
     unfold hmacstate_, hmac_relate.
      remember (if zlt 64 (Zlength key) then Vint (Int.repr 32)
            else Vint (Int.repr (Zlength key))) as kl.
      normalize.
      apply exp_right with
        (x:=(iS, (iS, (oS, (kl, map Vint (map Int.repr (HMAC_FUN.mkKey key))))))).
      simpl.
      apply andp_right. apply prop_right. repeat split; trivial.
      destruct (zlt 64 (Zlength key)); simpl in *.
         exists (Int.repr 32); eauto.
         rewrite Heqkl, HH1. exists (Int.repr (Int.unsigned ii)).
         rewrite Int.repr_unsigned; eauto.

      unfold_data_at 3%nat. cancel.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_i_ctx]); try reflexivity.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_md_ctx]); try reflexivity.
      entailer. cancel.
      destruct (zlt 64 (Zlength key)); simpl in *;
        rewrite HH1, Int.repr_unsigned; simpl in *.
        cancel.
        cancel.
  }

  { (*k is Vptr, key!=NULL*)
    destruct R; subst r; simpl. 
    apply semax_pre with (P':=FF); try entailer; try apply semax_ff.
    normalize. 
    unfold postResetHMS. simpl. unfold_data_at 1%nat.
    (* eapply semax_seq'.
    frame_SEP 3 4.*)
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_md_ctx]); try reflexivity.
    normalize.
    rename H into SCc. rename H0 into ACc.
    rewrite at_offset'_eq.
    2: simpl; rewrite Int.add_zero; reflexivity.
    rename b into kb; rename i into kofs.
    eapply semax_pre with (P':=PROP  ()
      LOCAL  (`(eq pad) (eval_var _pad (tarray tuchar 64));
       `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
       `(eq (Vint (Int.repr l))) (eval_id _len);
       `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
      SEP  (`(field_at Tsh t_struct_hmac_ctx_st [_key_length]
            (if zlt 64 (Zlength key)
            then Vint (Int.repr 32)
            else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx] oS (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [_key]
              (map Vint (map Int.repr (HMAC_FUN.mkKey key))) (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx] iS (Vptr cb cofs));
          `(data_at_ Tsh (tarray tuchar 64) pad);
          `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
              (Vptr kb kofs));
          `(K_vector KV);
          `(memory_block Tsh (Int.repr (sizeof (nested_field_type2 t_struct_hmac_ctx_st [_md_ctx])))
             (offset_val
                (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_md_ctx]))
             (Vptr cb cofs))))).
    { entailer. cancel.
      unfold tarray. erewrite data_at__array_at_. 2: omega. 2: reflexivity. 
      cancel.
      eapply derives_trans.
        apply data_at_data_at_. reflexivity. 
        rewrite <- memory_block_data_at_; try reflexivity. entailer.
    }
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_i_ctx]); try reflexivity.
    normalize. 
    rewrite at_offset'_eq.
    2: simpl; rewrite Int.add_zero; reflexivity.

    remember ((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS) as  WITNESS.
    forward_call WITNESS.
    { assert (FR: Frame = [
         `(field_at Tsh t_struct_hmac_ctx_st [_key_length]
            (if zlt 64 (Zlength key)
             then Vint (Int.repr 32)
             else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx] oS (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [_key]
            (map Vint (map Int.repr (HMAC_FUN.mkKey key))) (Vptr cb cofs));
         `(data_at_ Tsh (tarray tuchar 64) pad);
         `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
            (Vptr kb kofs)); `(K_vector KV)]).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      subst WITNESS. entailer. cancel. 
    }
    after_call. subst WITNESS. normalize.  subst retval0. simpl. 

    forward. (*return*)
    remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
    apply exp_right with (x:=HMACabs iSA iSA oSA KL key). 
    entailer.
    apply andp_right. 
      apply prop_right. unfold hmacInit. exists iSA, oSA.
      rewrite Int.unsigned_repr. auto.
      rewrite int_max_signed_eq  in KL2. rewrite int_max_unsigned_eq.
      destruct (zlt 64 (Zlength key)); omega.    
    unfold data_block. simpl_stackframe_of. entailer. cancel.
    unfold hmacstate_, hmac_relate.
    remember (if zlt 64 (Zlength key) then Vint (Int.repr 32)
              else Vint (Int.repr (Zlength key))) as kl.
    normalize.
    apply exp_right with
      (x:=(iS, (iS, (oS, (kl, map Vint (map Int.repr (HMAC_FUN.mkKey key))))))).
    simpl. entailer.
    apply andp_right. apply prop_right.
      split. rewrite (updAbs_len _ _ _ INNER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.
      split. rewrite (updAbs_len _ _ _ OUTER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.
      exists (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)).
      rewrite Int.unsigned_repr. 
      split. destruct (zlt 64 (Zlength key)); trivial.
      split; trivial.
      rewrite int_max_signed_eq  in KL2. rewrite int_max_unsigned_eq.
      destruct (zlt 64 (Zlength key)); omega.

    unfold_data_at 3%nat. cancel.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_i_ctx]); try reflexivity.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_md_ctx]); try reflexivity.
    entailer.
  }
} 
Qed.