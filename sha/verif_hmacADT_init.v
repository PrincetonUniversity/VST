Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.spec_hmacADT.
Require Import vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.

Require Import sha.hmac_NK.

Require Import sha.verif_hmacADT_init_part1.

Lemma ZnthV_map_Vint_is_int_I8: forall l (i : Z) ,
       0 <= i < Zlength l -> 
is_int I8 Unsigned
  (ZnthV (Tint I8 Unsigned noattr)
     (map Vint (map Int.repr (map Byte.unsigned l))) i).
Proof.
intros.
unfold ZnthV.
if_tac; [omega | ].
assert (Z.to_nat i < length l)%nat.
destruct H.
rewrite Zlength_correct in H1.
apply Z2Nat.inj_lt in H1; try omega.
rewrite Nat2Z.id in H1. auto.
unfold is_int. simpl.
clear - H1.
revert l H1; induction (Z.to_nat i); destruct l; intros; simpl in *.
omega. rewrite Int.unsigned_repr. apply Byte.unsigned_range_2. 
  destruct (Byte.unsigned_range_2 i0). split. omega.
  assert ( Byte.max_unsigned <= Int.max_unsigned).
    unfold Byte.max_unsigned, Int.max_unsigned. 
    unfold Byte.modulus, Int.modulus, Byte.wordsize, Int.wordsize. simpl. omega.
   omega.
  omega.
 apply IHn; omega.
Qed.

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
        (HN : nth (Z.to_nat i) (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) Vundef =
              Vint N),
      ZnthV tuchar (map Vint (map Int.repr
           (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) (Byte.repr z)))) i =
      Vint (Int.zero_ext 8 (Int.xor (Int.repr z) N)).
Proof. intros. unfold cVint, ZnthV, upd. if_tac. omega. simpl.
            erewrite @nth_mapVint'.
            Focus 2. unfold HMAC_SHA256.mkArgZ, HMAC_SHA256.mkArg. 
                     repeat rewrite map_length. 
                     rewrite combine_length, length_SF, map_length, mkKey_length. simpl.
                     split. apply (Z2Nat.inj_le 0); omega. apply (Z2Nat.inj_lt _ 64); omega.
            f_equal. 
              unfold HMAC_SHA256.mkArgZ, HMAC_SHA256.mkArg.
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
                unfold HMAC_SHA256.sixtyfour; rewrite nth_Nlist, Byte.xor_commut; simpl.
              2:  apply (Z2Nat.inj_lt _ 64); omega.
              assert (IB: Forall isbyteZ (HMAC_SHA256.mkKey key)). 
               apply Forall_forall. unfold HMAC_SHA256.mkKey; intros.
               destruct (Zlength key >? Z.of_nat SHA256.BlockSize). 
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

Definition postResetHMS (ctxS iS oS: s256state): hmacstate :=
  (ctxS, (iS, oS)).

Lemma body_hmac_init: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Init HMAC_Init_spec.
Proof.
start_function.
name ctx' _ctx.
name key' _key.
name len' _len.
simpl_stackframe_of.
(*destruct H as [KL1 [KL2 KL3]].*) normalize.
forward. 

unfold data_block. normalize. 

(*isolate branch if (key != NULL) *)
apply seq_assoc.
unfold initPre.

remember (EX  cb : block,
                 (EX  cofs : int,
                  (EX  pad : val,
                   (EX  r : Z, EX ctxkey:val,
                    PROP  (c = Vptr cb cofs /\ (r=0 \/ r=1))
                    LOCAL  (`(eq (Vint (Int.repr r))) (eval_id _reset);
                    `(eq pad) (eval_var _pad (tarray tuchar 64));
                    `(eq c) (eval_id _ctx); `(eq k) (eval_id _key);
                    `(eq l) (eval_id _len);
                    `(eq ctxkey) (eval_var _ctx_key (tarray tuchar 64));
                    `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
                    SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                    `(initPostKeyNullConditional l r c k h1 key ctxkey);
                    `(K_vector KV)))))) as PostKeyNull. 
forward_seq. instantiate (1:= PostKeyNull). (*eapply semax_seq.*)
{  assert (DD: Delta= initialized _reset Delta) by reflexivity.
   rewrite DD.
   eapply hmac_init_part1; eassumption. 
}
subst PostKeyNull. normalize.
apply extract_exists_pre; intros cb. 
apply extract_exists_pre; intros cofs. 
apply extract_exists_pre; intros pad. 
apply extract_exists_pre; intros r.
apply extract_exists_pre; intros ctxkey.
normalize. rename H into HC; rewrite HC. rename H0 into R.

(*isolate branch if (reset) *)
apply seq_assoc.
Definition initPostResetConditional l r (c:val) (k: val) h key ctxS iS oS: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 then hmacstate_PreInitNull key h c else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF
                  else EX ll:_, !!(Forall isbyteZ key/\ has_lengthK ll key /\ l = Vint(Int.repr ll)) &&
                       ((data_at Tsh t_struct_hmac_ctx_st (postResetHMS ctxS iS oS) c) *
                        (array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) (Vptr b ofs)))
  | _ => FF
  end.
remember (EX iSA:_, EX iS:_, EX oSA:_, EX oS:_, EX CK:_, EX CONT:_,
          PROP  (innerShaInit (map Byte.repr (HMAC_SHA256.mkKey key)) iSA /\ s256_relate iSA iS /\
                 outerShaInit (map Byte.repr (HMAC_SHA256.mkKey key)) oSA /\ s256_relate oSA oS)
                 LOCAL  (
                 `(eq pad) (eval_var _pad (tarray tuchar 64));
                 `(eq (Vptr cb cofs)) (eval_id _ctx);
                 `(eq ctxkey) (eval_var _ctx_key (tarray tuchar 64));
                 `(eq k) (eval_id _key);
                 `(eq l) (eval_id _len);
                 `(eq KV) (eval_var sha._K256 (tarray tuint 64)))

                 SEP  (
                 `(array_at_ tuchar Tsh 0 64 pad); `(data_at Tsh (tarray tuchar 64) CK ctxkey);
                 `(initPostResetConditional l r c k h1 key CONT iS oS); `(K_vector KV)))
  as PostResetBranch.
(*forward_seq. instantiate (1:= PostResetBranch).*)
eapply semax_seq. instantiate (1:=PostResetBranch).
{ forward_if PostResetBranch. 
  { (* THEN*)
    remember (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)))))) as IPADcont.
    remember (cVint (force_int oo ZnthV tuchar (map Vint (map Int.repr 
              (map Byte.unsigned (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)))))) as OPADcont.
    assert (ZLI: Zlength (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad) = 64).
            rewrite Zlength_mkArgZ.
            repeat rewrite map_length. rewrite mkKey_length.
            unfold SHA256.BlockSize; simpl. trivial. 
    assert (ZLO: Zlength (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad) = 64).
            rewrite Zlength_mkArgZ.
            repeat rewrite map_length. rewrite mkKey_length.
            unfold SHA256.BlockSize; simpl. trivial. 
    remember (ZnthV tuchar (default_val (Tarray tuchar 64 noattr))) as DEFAULTcont.
    unfold data_at_, tuchars, tarray.
    erewrite data_at_array_at; try reflexivity. 2: omega.
    rewrite array_at_isptr. normalize. apply isptrD in H. destruct H as [pb [pofs Hpad]]. subst pad.
    apply semax_pre with (P':=EX ll:_,EX CONT:_,
         PROP  (r<>0 /\ Forall isbyteZ key/\ has_lengthK ll key /\ l = Vint(Int.repr ll))
         LOCAL  (tc_environ Delta;
            `(eq (Vint (Int.repr r))) (eval_id _reset);
            `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
            `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq k) (eval_id _key);
            `(eq l) (eval_id _len);
            `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
            `(eq KV) (eval_var sha._K256 (Tarray tuint 64 noattr)))
         SEP  (`(K_vector KV);
               `(array_at tuchar Tsh (ZnthV tuchar (default_val (Tarray tuchar 64 noattr)))
                   0 64 (Vptr pb pofs));
               `(data_at Tsh t_struct_hmac_ctx_st CONT (Vptr cb cofs));
               `(data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                  ctxkey);
               `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) k))).
    { clear HeqPostResetBranch PostResetBranch.
      unfold initPostKeyNullConditional. entailer.
      destruct key'; try contradiction.
      (*integer, ie key==NULL*)
          simpl in TC0. subst i. simpl. if_tac. subst r. inversion H0. normalize.
      (*key == Vptr*)
       if_tac. normalize. entailer. apply (exp_right ll). 
       apply (exp_right CONT). entailer. cancel.
    }
    apply extract_exists_pre. intros ll; normalize.
    apply extract_exists_pre. intros CONT. normalize. subst l; rename ll into l.
    rename H0 into isbyte_key. rename H1 into KL.
    rewrite (array_at_isptr _ _ _ _ _ k). normalize.
    destruct R; subst r. omega. clear H. 
    apply isptrD in H0; destruct H0 as [kb [kofs HK]]; rewrite HK in *.
    rewrite data_at_isptr with (p:=ctxkey). normalize.
    apply isptrD in H; destruct H as [ckb [ckofs HCK]]; rewrite HCK in *.

    forward_seq. 
    instantiate (1:= 
      (PROP  ()
       LOCAL  (
        `(eq (Vint (Int.repr 1))) (eval_id _reset);
        `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
        `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq k) (eval_id _key);
        `(eq (Vint (Int.repr l))) (eval_id _len);
        `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
        `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
       SEP 
        (`(array_at tuchar Tsh IPADcont 0 64 (Vptr pb pofs));
         `(data_at Tsh t_struct_hmac_ctx_st CONT (Vptr cb cofs));
         `(data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckofs));
         `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key) (Vptr kb kofs));
        `(K_vector KV)))).
    { (*ipad loop*)
      forward_for_simple_bound' 64 (EX i:Z, 
        (PROP  ()
         LOCAL  (`(eq (Vint (Int.repr 1))) (eval_id _reset);
                 `(eq (Vptr pb pofs)) (eval_var _pad (tarray tuchar 64));
                 `(eq (Vptr cb cofs)) (eval_id _ctx);
                 `(eq (Vptr kb kofs)) (eval_id _key);
                 `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
                 `(eq (Vint (Int.repr l))) (eval_id _len);
                 `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP  (
          `(array_at tuchar Tsh IPADcont 0 i (Vptr pb pofs));
          `(array_at tuchar Tsh DEFAULTcont i 64 (Vptr pb pofs));
          `(data_at Tsh t_struct_hmac_ctx_st CONT (Vptr cb cofs));
         `(data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckofs));
          `(array_at tuchar Tsh (ZnthV tuchar (map Vint (map Int.repr key))) 0
               (Zlength key) (Vptr kb kofs)); `(K_vector KV)))).
      { (*precondition implies "invariant"*) 
        rewrite array_at_emp. normalize. 
        rewrite array_at_local_facts''. entailer. cancel.
      }
      { unfold normal_ret_assert. simpl. intros rho. 
        rewrite array_at_emp. entailer.
      }
      { rename H into I. 
        (*unfold_data_at 1%nat. normalize.
        rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_key]); try reflexivity.
        normalize. rename H0 into SCc. rename H1 into ACc.
        rewrite at_offset'_eq.
        2: simpl; rewrite Int.add_zero; reflexivity.*)
        eapply semax_pre0; [ apply now_later | ].
        eapply semax_post_flipped'.
        { subst PostResetBranch.
          remember (ZnthV tuchar (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) i) as CONTi.
          unfold ZnthV in CONTi. destruct (nth_mapVintZ i (HMAC_SHA256.mkKey key)) as [N HN].
              rewrite Zlength_correct, mkKey_length. unfold SHA256.BlockSize; simpl. 
               assumption.            
          assert (Hres: ZnthV tuchar (map Vint (map Int.repr
                   (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad))) i
              = Vint (Int.zero_ext 8 (Int.xor (Int.repr 54) N))). 
          { clear - HN I isbyte_key. apply xor_pad_result; try assumption. }
            unfold tarray. 
            erewrite data_at_array_at with (v:= map Vint (map Int.repr (HMAC_SHA256.mkKey key))); try reflexivity.
              2: omega. 
            eapply NEWsemax_loadstore_array with 
              (n:=1%nat)
              (v2:=(ZnthV tuchar (map Vint(map Int.repr (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad))) i)).
             simpl; try reflexivity.
             simpl; try reflexivity.
             simpl; try reflexivity.
             simpl; try reflexivity.
             simpl; try reflexivity.
             { instantiate (1:=i). instantiate (1:=Vptr pb pofs).
               entailer. normalize. 
               apply andp_right. apply andp_right; rel_expr. 
               rewrite Hres. 
               erewrite (split3_array_at' i _ _ _ 0 64); try reflexivity. 2: trivial.
               { rel_expr. 
                 unfold ZnthV in *. if_tac. omega. simpl; rewrite HN. discriminate.
                 simpl; intros.
                 unfold ZnthV in *. if_tac. omega. simpl; rewrite HN. reflexivity.
                 reflexivity.
               } 
             } 
             simpl. reflexivity.
             trivial.
             { unfold HMAC_SHA256.mkArgZ. simpl. apply ZnthV_map_Vint_is_int_I8.
               unfold HMAC_SHA256.mkArgZ in ZLI. rewrite Zlength_correct, map_length in ZLI. 
               rewrite Zlength_correct, ZLI. omega.
             }
             red; omega.   
          }
          { entailer. cancel.
            rewrite (split_array_at (i+1) tuchar Tsh _ i 64); try omega. cancel.
            unfold tarray. erewrite data_at_array_at; try reflexivity.
              2: omega.
            cancel. 
            apply sepcon_derives.
              rewrite (split_array_at i tuchar Tsh _ 0 (i+1)); try omega.
              cancel.
              apply array_lemmas.array_at_ext'.
              unfold cVint, ZnthV; simpl; intros.
              assert (i0=i). omega. subst i0. simpl.
              destruct (zlt i 0). omega. simpl. rewrite upd_eq.
              destruct (nth_mapVintZ i 
               (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)) as [n Hn].
              rewrite ZLI; assumption.
              rewrite Hn. unfold HMAC_SHA256.mkArgZ in Hn; rewrite Hn. trivial.
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
    frame_SEP 0.
    forward_call (Vptr cb (Int.add cofs (Int.repr 108))).
    { assert (FR: Frame = nil).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      entailer. eapply derives_trans. 
         apply data_at_data_at_. reflexivity. cancel. 
    }
    after_call. simpl. normalize. 

    eapply semax_seq'.
    frame_SEP 0 3 6.
    remember (init_s256abs, 
            HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad,
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
           (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)) as [n Hn].
        rewrite ZLI; assumption.
      rewrite Hn. unfold HMAC_SHA256.mkArgZ in Hn; rewrite Hn. trivial.
    }
    after_call. simpl. intros rho. subst WITNESS. rewrite firstn_precise. normalize.
      unfold HMAC_SHA256.mkArgZ, HMAC_SHA256.mkArg. repeat rewrite map_length.
      unfold HMAC_SHA256.sixtyfour. rewrite combine_length, map_length, length_Nlist, mkKey_length.
      unfold SHA256.BlockSize; simpl. trivial.

    simpl.
    apply semax_pre with (P':=EX x : s256abs,
  (PROP  ()
   LOCAL  (tc_environ Delta; tc_environ Delta;
   `(eq (Vint (Int.repr 1))) (eval_id _reset);
   `(eq (Vptr pb pofs)) (eval_var _pad (Tarray tuchar 64 noattr));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(fun a : environ =>
      (PROP 
       (update_abs
          (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)
          init_s256abs x)
       LOCAL ()
       SEP  (`(K_vector KV);
       `(sha256state_ x (Vptr cb (Int.add cofs (Int.repr 108))));
       `(data_block Tsh
           (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)
           (Vptr pb pofs)))) a) globals_only;
   `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx] (snd (snd CONT)) (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] (fst CONT) (Vptr cb cofs));
   `(data_at Tsh (tarray tuchar 64)
       (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckofs));
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
   `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP  (`(K_vector KV);
   `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
   `(data_block Tsh
       (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)
       (Vptr pb pofs));
   `(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [_o_ctx]) (snd (snd CONT))
       (Vptr cb
          (Int.add cofs
             (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_o_ctx])))));
   `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] (fst CONT) (Vptr cb cofs));
   `(data_at Tsh (tarray tuchar 64)
       (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckofs));
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
                 `(eq ctxkey) (eval_var _ctx_key (Tarray tuchar 64 noattr));
                 `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP  (`(K_vector KV);
   `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
   `(array_at tuchar Tsh OPADcont 0 i (Vptr pb pofs));
   `(array_at tuchar Tsh IPADcont i 64 (Vptr pb pofs));
   `(data_at Tsh (nested_field_type2 t_struct_hmac_ctx_st [_o_ctx]) (snd (snd CONT))
       (Vptr cb
          (Int.add cofs
             (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [_o_ctx])))));
   `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] (fst CONT) (Vptr cb cofs));
         `(data_at Tsh (tarray tuchar 64)
              (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckofs));
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
             (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Ipad)) as [n Hn].
            rewrite ZLI. assumption.
            rewrite Hn. unfold HMAC_SHA256.mkArgZ in Hn; rewrite Hn. trivial.            
      }
      { unfold normal_ret_assert, data_block. simpl. intros rho. 
        rewrite array_at_emp. entailer.
        apply andp_right. apply prop_right. apply isbyte_map_ByteUnsigned.
        cancel. unfold tuchars. rewrite ZLO.
            apply array_lemmas.array_at_ext'. 
            unfold tuchars, cVint, ZnthV; simpl. intros. destruct (zlt i 0). omega.
            destruct (nth_mapVintZ i 
             (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)) as [n Hn].
            rewrite ZLO. assumption. rewrite Hn. unfold HMAC_SHA256.mkArgZ in Hn; rewrite Hn. trivial.
      }
      { (*unfold_data_at 1%nat. normalize.*)
        rename H into I. 
        eapply semax_pre0; [ apply now_later | ].
        eapply semax_post_flipped'.
        { subst PostResetBranch.
          remember (ZnthV tuchar (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) i) as CONTi.
          unfold ZnthV in CONTi. destruct (nth_mapVintZ i (HMAC_SHA256.mkKey key)) as [N HN].
              rewrite Zlength_correct, mkKey_length. unfold SHA256.BlockSize; simpl. 
               assumption.
          assert (Hres: ZnthV tuchar (map Vint (map Int.repr
                   (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad))) i
              = Vint (Int.zero_ext 8 (Int.xor (Int.repr 92) N))). 
          { clear - HN I isbyte_key. apply xor_pad_result; assumption. }
          unfold tarray. 
          erewrite data_at_array_at with (v:= map Vint (map Int.repr (HMAC_SHA256.mkKey key))); try reflexivity.
              2: omega. 
          eapply NEWsemax_loadstore_array
          with 
          (n:=3%nat)
          (v2:=(ZnthV tuchar (map Vint(map Int.repr (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad))) i)).
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          simpl; try reflexivity.
          { instantiate (1:=i). instantiate (1:=Vptr pb pofs).
            entailer. normalize. 
            apply andp_right. apply andp_right; rel_expr. 
            rewrite Hres. 
            erewrite (split3_array_at' i _ _ _ 0 64); try reflexivity. 2: trivial.
            { rel_expr. 
              unfold ZnthV in *. if_tac. omega. simpl; rewrite HN. discriminate.
              simpl; intros.
                unfold ZnthV in *. if_tac. omega. simpl; rewrite HN. reflexivity.
              reflexivity. 
            }
          }
          simpl. reflexivity.
          trivial.
          { unfold HMAC_SHA256.mkArgZ. simpl. apply ZnthV_map_Vint_is_int_I8.
            unfold HMAC_SHA256.mkArgZ in ZLO. rewrite Zlength_correct, map_length in ZLO. 
            rewrite Zlength_correct, ZLO. omega.
          }
          red; omega.   
          }
        { entailer. cancel.
          rewrite (split_array_at (i+1) tuchar Tsh _ i 64); try omega. cancel.
          unfold tarray. erewrite data_at_array_at; try reflexivity.
              2: omega.
          cancel. 
          apply sepcon_derives.
            rewrite (split_array_at i tuchar Tsh _ 0 (i+1)); try omega.
            cancel.
            apply array_lemmas.array_at_ext'.
            unfold cVint, ZnthV; simpl; intros.
            assert (i0=i). omega. subst i0. simpl.
            destruct (zlt i 0). omega. simpl. rewrite upd_eq.
            destruct (nth_mapVintZ i 
             (HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad)) as [n Hn].
             rewrite ZLO; assumption.
            rewrite Hn. unfold HMAC_SHA256.mkArgZ in Hn; rewrite Hn. trivial.
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
    frame_SEP 3.
    forward_call (Vptr cb (Int.add cofs (Int.repr 216))).
    { assert (FR: Frame = nil).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      entailer. eapply derives_trans. apply data_at_data_at_. reflexivity. cancel.
    }
    after_call. simpl. normalize.

    unfold MORE_COMMANDS, abbreviate. (*WHY IS THIS NOT DONE AUTOMATICALLY?*)
(*    make_sequential.
    frame_SEP 0 1 3.*)
    remember (init_s256abs, 
            HMAC_SHA256.mkArgZ (map Byte.repr (HMAC_SHA256.mkKey key)) Opad,
            Vptr cb (Int.add cofs (Int.repr 216)),
            Vptr pb pofs, Tsh, 64, KV) as WITNESS.
    forward_call WITNESS.
    { assert (FR: Frame = [
         `(sha256state_ ipadSHAabs (Vptr cb (Int.add cofs (Int.repr 108))));
         `(field_at Tsh t_struct_hmac_ctx_st [_md_ctx] (fst CONT) (Vptr cb cofs));
         `(data_at Tsh (tarray tuchar 64)
            (map Vint (map Int.repr (HMAC_SHA256.mkKey key))) (Vptr ckb ckofs));
         `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
              (Vptr kb kofs))]). 
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      subst WITNESS. entailer. cancel.
    }
    after_call. simpl. intros rho. subst WITNESS PostResetBranch.
    rewrite firstn_precise.
    { entailer.
      rename x into opadSHAabs.
      unfold sha256state_; normalize. rename r into iUpd. rename x into oUpd.
      apply exp_right with (x:=ipadSHAabs). entailer.
      apply exp_right with (x:=iUpd). entailer.
      apply exp_right with (x:=opadSHAabs). entailer.
      apply exp_right with (x:=oUpd). entailer.
      unfold data_block, initPostResetConditional. simpl.
      rewrite ZLO. entailer.
      apply (exp_right (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))). entailer. 
      apply exp_right with (x:=fst CONT). entailer.
      apply exp_right with (x:=l). entailer. cancel.
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
    }

    unfold HMAC_SHA256.mkArgZ, HMAC_SHA256.mkArg. repeat rewrite map_length.
    unfold HMAC_SHA256.sixtyfour. rewrite combine_length, map_length, length_Nlist, mkKey_length.
    unfold SHA256.BlockSize; simpl. trivial.
  }
  { (*ELSE*) 
    forward. unfold overridePost. simpl. intros rho. apply andp_right. apply prop_right. trivial.
    subst. unfold initPostKeyNullConditional; simpl. entailer.
    rewrite <- H1 in *; simpl in *. unfold typed_false in H0. simpl in H0.
        inversion H0; clear H0. apply negb_false_iff in H5.
        apply eq_sym in H5; apply binop_lemmas.int_eq_true in H5.
    destruct R; subst. simpl.
      remember (eval_id _key rho) as k. destruct k; entailer. 
      remember (Int.eq i Int.zero) as d. destruct d. 2: entailer.
      unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
      destruct h1; entailer.
       apply exp_right with (x:= iSha). 
       apply exp_right with (x:= (iCtx r)).
       apply exp_right with (x:= oSha).
       apply exp_right with (x:= (oCtx r)).
       entailer. rewrite <- Heqd. cancel.
       unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl. unfold data_at_.
       apply (exp_right (default_val (tarray tuchar 64))). entailer.
       apply (exp_right r). cancel. entailer.
       apply (exp_right v). cancel.
       apply sepcon_derives. unfold tarray. erewrite data_at_array_at. cancel. reflexivity. omega. reflexivity.
       entailer. 
     simpl. apply Int.one_not_zero in H5. contradiction.
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
  apply extract_exists_pre; intros CK. 
  apply extract_exists_pre; intros CONT. 
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
     destruct Hs as [IREL [OREL [ILEN [OLEN [ISHA OSHA]]]]].
     destruct s as [mdS [iS oS]]. simpl in *.
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
          `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx] oS (Vptr cb cofs));
          `(data_at_ Tsh (tarray tuchar 64) ctxkey);
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
     unfold hmacInit. (**)
     remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
     apply exp_right with (x:=HMACabs iSha iSha oSha).   
     entailer.
     apply andp_right. 
       apply prop_right. exists iSha, oSha. auto. (*
       rewrite Int.unsigned_repr. auto.
       rewrite int_max_signed_eq  in KL2. rewrite int_max_unsigned_eq.
       destruct (zlt 64 (Zlength key)); omega.     *)
     simpl_stackframe_of. unfold tarray. 
     rewrite <- data_at__array_at_ with (a:=noattr).
     2: omega. 2: reflexivity.
     cancel.
     unfold hmacstate_, hmac_relate.
(*      remember (if zlt 64 (Zlength key) then Vint (Int.repr 32)
            else Vint (Int.repr (Zlength key))) as kl.*)
      normalize.
      apply exp_right with (x:=(iS, (iS, oS))).
      simpl. entailer.
(*      apply andp_right. apply prop_right.
      destruct (zlt 64 (Zlength key)); simpl in *. trivial.
          rewrite Int.unsigned_repr. trivial. 
           rewrite int_max_unsigned_eq. rewrite int_max_signed_eq in KL2. omega.*)

      unfold_data_at 3%nat. cancel.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_i_ctx]); try reflexivity.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_md_ctx]); try reflexivity.
      entailer. 
  }

  { (*k is Vptr, key!=NULL*)
    destruct R; subst r; simpl. 
    apply semax_pre with (P':=FF); try entailer; try apply semax_ff.
    normalize. intros ll. normalize. subst l; rename ll into l.
    rename H into isbyteKey. rename H0 into KL. 
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
       `(eq ctxkey) (eval_var _ctx_key (tarray tuchar 64));
       `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
      SEP  (
          `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx] oS (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [_i_ctx] iS (Vptr cb cofs));
          `(data_at_ Tsh (tarray tuchar 64) pad);
          `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
              (Vptr kb kofs));
          `(data_at_ Tsh (tarray tuchar 64) ctxkey); `(K_vector KV);
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
         `(field_at Tsh t_struct_hmac_ctx_st [_o_ctx] oS (Vptr cb cofs));
         `(data_at_ Tsh (tarray tuchar 64) ctxkey);
         `(data_at_ Tsh (tarray tuchar 64) pad);
         `(array_at tuchar Tsh (tuchars (map Int.repr key)) 0 (Zlength key)
            (Vptr kb kofs)); `(K_vector KV)]).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      subst WITNESS. entailer. cancel. 
    }
    after_call. subst WITNESS. normalize.  subst retval0. simpl. 

    forward. (*return*)
    apply exp_right with (x:=HMACabs iSA iSA oSA). 
    entailer.
    apply andp_right. 
      apply prop_right. unfold hmacInit. exists iSA, oSA. auto.
    unfold data_block. simpl_stackframe_of. entailer. cancel.
    unfold hmacstate_, hmac_relate.
    apply exp_right with (x:=(iS, (iS, oS))).
    simpl. entailer.
    apply andp_right. apply prop_right.
      split. rewrite (updAbs_len _ _ _ INNER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.
      rewrite (updAbs_len _ _ _ OUTER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.

    unfold_data_at 3%nat. cancel.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_i_ctx]); try reflexivity.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [_md_ctx]); try reflexivity.
    entailer.
  }
} 
Qed.