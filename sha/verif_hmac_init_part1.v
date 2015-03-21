Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

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
                      (Vptr b ofs)))
  | _ => FF
  end.

Lemma hmac_init_part1: forall
(Espec : OracleKind)
(c : val)
(k : val)
(l : Z)
(key : list Z)
(kv : val)
(h1:hmacabs)
(KL1 : l = Zlength key)
(KL2 : 0 <= l <= Int.max_signed)
(KL3 : l * 8 < two_p 64)
(ctx' : name _ctx)
(key' : name _key)
(len' : name _len)
(Delta := (initialized _reset 
       (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs)))
(PostKeyNull : environ -> mpred)(*
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
                    `(K_vector KV)))))),*)
(HeqPostKeyNull : PostKeyNull =
                 EX  cb : block,
                 (EX  cofs : int,
                  (EX  pad : val,
                   (EX  r : Z,
                    PROP  (c = Vptr cb cofs /\ (r=0 \/ r=1))
                    LOCAL  (temp _reset (Vint (Int.repr r));
                      lvar _pad (tarray tuchar 64) pad; temp _ctx c; temp _key k;
                      temp _len (Vint (Int.repr l));
                      gvar sha._K256 kv)
                    SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                    `(initPostKeyNullConditional r c k h1 key);
                    `(K_vector kv)))))),
@semax Espec Delta
  (PROP  ()
   LOCAL  (temp _reset (Vint (Int.repr 0)); temp _ctx c;
     temp _key k; temp _len (Vint (Int.repr l));
     gvar sha._K256 kv)
   SEP 
   (`(data_at_ Tsh (tarray tuchar 64)) (eval_lvar _pad (tarray tuchar 64));
   `(K_vector kv); `(initPre c k h1 key)))
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
    apply (remember_value (eval_lvar _pad (tarray tuchar 64))); intro pad.
    replace_SEP 0 (`(data_at_ Tsh (tarray tuchar 64) pad)).
      entailer!.
    assert_LOCAL (lvar _pad (tarray tuchar 64) pad).
      entailer!. apply normalize_lvar; auto.
    drop_LOCAL 1%nat.
forward_if PostKeyNull.
  { (* THEN*)
    simpl. 
    unfold force_val2, force_val1 in H; simpl in H.
    unfold initPre. 
    destruct k; try solve [eapply semax_pre; try eapply semax_ff; entailer].
    (*key' is integer, ie Null*)
      remember (Int.eq i Int.zero) as d.
      destruct d; try solve [eapply semax_pre; try eapply semax_ff; entailer].
      apply binop_lemmas.int_eq_true in Heqd. simpl in *. subst i.
      unfold Int.zero in *. simpl in *. inversion H.
    (*key' is ptr*)
    normalize. clear H.
    assert_PROP (isptr c). entailer. apply isptrD in H. destruct H as [cb [cofs CC]]; subst c.
    rename b into kb; rename i into kofs.
    assert_PROP (Forall isbyteZ key).
      { unfold data_block. entailer. }
    rename H into isbyte_key. 
    replace_SEP 1 (`(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr kb kofs))).
       unfold data_block. entailer.

    forward v. subst v. 
    forward. (*j=HMAC_MAX_MD_CBLOCK*)
    simpl.

    remember
     (PROP  ()
      LOCAL  (
       temp _reset (Vint (Int.repr 1));
       lvar _pad (tarray tuchar 64) pad;
       temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
       temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
      SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
            `(data_at Tsh t_struct_hmac_ctx_st (keyedHMS key) (Vptr cb cofs));
            `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
              (Vptr kb kofs));
          `(K_vector kv))) as PostIf_j_Len.

    forward_if PostIf_j_Len. 
    { (* j < len*) 
      rename H into lt_64_l.

      (*call to SHA256_init*)
      remember (`(data_at_ Tsh (tarray tuchar 64) pad)) as PAD.
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

      subst PAD. normalize.

      (*Old proof
      eapply semax_seq'.
      myframe_SEP'' [4].

      forward_call (Vptr cb cofs). 
      { assert (FR: Frame = nil).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.  
       entailer.
      }
      after_call.
      normalize. simpl.*)
      forward_call' (Vptr cb cofs).

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

(*Old call
      (*Now moved up, before the call to sha-init subst PAD. Without this subst, the following myframeSEP'' leaves
           a goal involving closed_vars*)
      myframe_SEP'' [4; 0; 2].
      remember (init_s256abs, key, Vptr cb cofs,
                Vptr kb kofs, Tsh, l, kv) as WITNESS.
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
      after_call.  subst WITNESS. simpl. intros rho. normalize. simpl.*)
      forward_call' (init_s256abs, key, Vptr cb cofs,
                Vptr kb kofs, Tsh, l, kv) ctxSha.
      { assert (FR: Frame = [
            data_at Tsh (tarray tuchar (Z.of_nat (length key) - Z.of_nat (length key)))
               (skipn (length key) (map Vint (map Int.repr key)))
               (offset_val (Int.repr (Z.of_nat (length key))) (Vptr kb kofs));
            field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] Vundef
               (Vptr cb cofs);
            field_at Tsh t_struct_hmac_ctx_st [StructField _key] [] (Vptr cb cofs);
            field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]
               ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs);
            field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]
               ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs);
            data_at_ Tsh (tarray tuchar 64) pad]).
          subst Frame; reflexivity.
          rewrite FR; clear FR Frame.
          unfold data_block. rewrite Zlength_correct. 
          entailer. (*TODO: If we don't instantiate the Frame explxitly here,
                        the call to entailer raises "Anomaly: undefined_evars_of_term: evar not found. Please report."*)
      }
      { clear Frame HeqPostIf_j_Len HeqPostKeyNull.
        subst l. split. omega. 
        split. specialize Int.max_signed_unsigned. omega.
        apply KL3.
      }

      simpl.
      replace_SEP 3 (`emp). 
      { entailer.
        assert (L: length key = length (map Vint (map Int.repr key))).
           repeat rewrite map_length. trivial.
        rewrite L, skipn_exact_length, Z.sub_diag.
        eapply derives_trans; try eapply data_at_data_at_.
             rewrite data_at__memory_block.
               rewrite memory_block_zero_Vptr. entailer.
               reflexivity. simpl; omega.
      }
      rename H into updAbs.

   (*call Final*)
   rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.
   
      (*new: extract info from field_address as early as possible*)
      assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _key] (Vptr cb cofs))).
         entailer.
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

   (*Call to _SHA256_Final*)
   (*Old proof eapply semax_seq'.
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
   *)
   forward_call' (ctxSha, Vptr cb (Int.add cofs (Int.repr 328)),
                  Vptr cb cofs, Tsh, kv).
   { assert (FR: Frame = [
       data_at Tsh (Tarray tuchar 32 noattr) [Znth 32 [] Vundef]
          (Vptr cb (Int.add cofs (Int.repr (328 + 32))));
       data_block Tsh key (Vptr kb kofs);
       field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] Vundef
          (Vptr cb cofs);
       field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]
          ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs);
       field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]
          ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs);
       data_at_ Tsh (Tarray tuchar 64 noattr) pad]).
       subst Frame; reflexivity.
     rewrite FR; clear FR Frame.   
     entailer. cancel.
     (*was: rewrite memory_block_array_tuchar'. cancel. trivial. omega.*)
     (*Now*) eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. entailer.
               reflexivity. simpl; omega.
   }
   normalize.

   (*call memset*)
   (* doing this: eapply semax_seq'. frame_SEP 3. requires us to do the swap fun a=> vs EX
      after the call, which leaves a state that still doesn't nicely normalize *)
   (*Old proof
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
         `(data_at_ Tsh (Tarray tuchar 64 noattr) pad)]).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.   
       entailer. cancel. 
       (*was: rewrite memory_block_array_tuchar'. cancel. trivial. omega.*)
       (*Now*) eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. entailer.
               reflexivity. simpl. omega.
     } 
     after_call. subst WITNESS. normalize. subst retval0. *)
   forward_call' (Tsh, Vptr cb (Int.add cofs (Int.repr 360)), 32, Int.zero) v.
     { assert (FR: Frame = [(K_vector kv);
         (data_at_ Tsh sha.t_struct_SHA256state_st (Vptr cb cofs));
         (data_block Tsh (sha_finish ctxSha) (Vptr cb (Int.add cofs (Int.repr 328))));
         (data_block Tsh key (Vptr kb kofs));
         (field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] Vundef (Vptr cb cofs));
         (field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]
              ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         (field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]
              ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         (data_at_ Tsh (Tarray tuchar 64 noattr) pad)]).
         subst Frame; reflexivity.
       rewrite FR; clear FR Frame.   
       entailer. cancel. 
       (*was: rewrite memory_block_array_tuchar'. cancel. trivial. omega.*)
       (*Now*) eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. entailer.
               reflexivity. simpl; omega.
     }
   normalize. subst v.

   forward. (*ctx->key_length=32*)

   subst PostIf_j_Len. subst PostKeyNull.
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
                assert (TT: Z.of_nat 32=32) by reflexivity. rewrite TT; clear TT. omega.
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
         elim (n f).
       }
       { apply data_at_Tarray_ext_derives. intros. 
              unfold Znth. if_tac. omega.
              assert (Z32: (Z.to_nat i < 32)%nat).
                  clear - H3; destruct H3 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
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
                      rewrite <- H14.
                  assert (XX: Z.to_nat (Zlength key) = length key). rewrite Zlength_correct. rewrite Nat2Z.id. trivial.
                  rewrite XX. rewrite firstn_precise; trivial.
              rewrite length_SHA256'; trivial.
              repeat rewrite map_length. rewrite mkKey_length; unfold SHA256.BlockSize; simpl. omega.
              repeat rewrite map_length. unfold sha_finish. inversion updAbs. rewrite <- functional_prog.SHA_256'_eq, length_SHA256'. trivial.
       }
     }
     { assert (X: 328 + Z.of_nat 32 = 360) by reflexivity. rewrite X; clear X.
       apply data_at_Tarray_ext_derives. intros. 
       unfold Znth. if_tac. omega. if_tac. omega. clear H4 H5. 
       apply data_at_triv.
       assert (Z32: (Z.to_nat i < 32)%nat).
                  clear - H3; destruct H3 as [XX YY]. rewrite Z2Nat.inj_lt in YY.
                  apply YY. omega. omega.
       unfold HMAC_SHA256.mkKey. 
               assert (Kgt: Zlength key > Z.of_nat SHA256.BlockSize).  simpl; omega.
               apply Zgt_is_gt_bool in Kgt.
               rewrite Kgt. unfold HMAC_SHA256.zeroPad. repeat rewrite map_app.
               rewrite app_nth2; repeat rewrite map_length; rewrite length_SHA256'.
                 assert (Z.to_nat 32 - SHA256.DigestLength = 0)%nat.                   
                            unfold SHA256.DigestLength. simpl; omega.
                 rewrite H4.
                 assert (SHA32: (SHA256.BlockSize - SHA256.DigestLength)%nat = 32%nat) by reflexivity.
                 rewrite SHA32; clear SHA32.
                 rewrite nth_map' with (d':=Int.zero).
                   rewrite nth_map' with (d':=Z0).
                     rewrite nth_list_repeat; trivial.
                 assert (X: (nat_of_Z (32 + 1) = 1 + 32)%nat) by reflexivity.
                 rewrite X; clear X. rewrite <- skipn_drop.
                 rewrite skipn_app2.
                   repeat rewrite map_length. unfold  SHA256.Hash. rewrite length_SHA256'.
                   assert (32 - SHA256.DigestLength = 0)%nat by reflexivity. rewrite H5.
                 rewrite skipn_0.
                 do 2 rewrite skipn_map.
                rewrite skipn_list_repeat. do 2 rewrite map_list_repeat. reflexivity.
                omega.
                repeat rewrite map_length. unfold  SHA256.Hash. rewrite length_SHA256'. 
                   unfold SHA256.DigestLength. omega. 
                rewrite length_list_repeat. omega. 
                rewrite map_length, length_list_repeat. omega. 
                unfold SHA256.DigestLength. simpl; omega.
         }
   } 

   { (* j >= len*)
     rename H into ge_64_l. 

     (*call to memcpy*)
     focus_SEP 0 2.
     unfold data_at_. 
     unfold_data_at 1%nat.
     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _key]); try reflexivity.
     (*new: extract field_address as early as possible*)
      assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _key] (Vptr cb cofs))).
        entailer. 
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
   
     (*Old proof
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
       remember (map Vint (map Int.repr key)) as CONT.*)
     forward_call' ((Tsh, Tsh), Vptr cb (Int.add cofs (Int.repr 328)), 
             Vptr kb kofs, mkTrep (Tarray tuchar (Zlength key) noattr) 
                     (map Vint (map Int.repr key))) v.
     { apply prop_right. rewrite Z.max_r.
       destruct (Zlength key); trivial. apply KL2. }
     { assert (FR: Frame = [
         (data_at Tsh (Tarray tuchar l64 noattr)
          (Znth l [] Vundef :: skipn (nat_of_Z (l + 1)) [])
            (offset_val (Int.repr l) (Vptr cb (Int.add cofs (Int.repr 328)))));
         (field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] Vundef (Vptr cb cofs));
         (field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         (field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         (field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx] ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         (data_at Tsh (Tarray tuchar 64 noattr) [] pad); (K_vector kv)]).
         subst Frame. reflexivity.
       rewrite FR. clear FR Frame.  
       entailer. cancel.
       simpl. rewrite Zlength_max_zero.
         assert (HH: match Zlength key with
                     | 0 => 0
                     | Z.pos y' => Z.pos y'
                     | Z.neg y' => Z.neg y'
                 end = Zlength key).
            destruct (Zlength key); reflexivity.
       rewrite HH (*was: clear HH*).
       eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. entailer.
               simpl.
               rewrite Zlength_max_zero, HH. cancel.
               reflexivity.
               simpl. rewrite Zlength_max_zero, HH. 
               rewrite <- initialize.max_unsigned_modulus. specialize Int.max_signed_unsigned; omega.         
     }
     { simpl. split. trivial.
       rewrite Zlength_max_zero.
       assert (HH: match Zlength key with
                     | 0 => 0
                     | Z.pos y' => Z.pos y'
                     | Z.neg y' => Z.neg y'
                 end = Zlength key).
            destruct (Zlength key); reflexivity.
       rewrite HH. subst l; clear - KL2. specialize Int.max_signed_unsigned; omega.
     } 
     subst v; normalize. simpl. 

   (*call memset*)
   (*Old proof remember (Tsh, Vptr cb (Int.add cofs (Int.repr (Zlength key + 328))), l64, Int.zero) as WITNESS.
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
     after_call. subst WITNESS. normalize. subst retval0. *)
   remember (map Vint (map Int.repr key)) as CONT. 
   forward_call' (Tsh, offset_val (Int.repr (Zlength key + 328)) (Vptr cb cofs) , l64, Int.zero) v.
   { (*TODO (forward_call'): this goal should never be presented in this form - but how can we
       prevent the unfolding of arithmetic/ offset_val etc?.
       Looking at the old proof above gave sufficient hints how the goal can be discharged,
       but we need something better.*)
      apply prop_right. clear.
      split. rewrite Zplus_comm. reflexivity. reflexivity.
   }
   { assert (FR: Frame = [
        (data_at Tsh (Tarray tuchar (Zlength key) noattr)
              CONT (Vptr cb (Int.add cofs (Int.repr 328))));
        (data_at Tsh (Tarray tuchar (Zlength key) noattr)
              CONT (Vptr kb kofs));
         (field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] Vundef (Vptr cb cofs));
         (field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx]
             ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         (field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]
             ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         (field_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]
             ([], (Vundef, (Vundef, ([], Vundef)))) (Vptr cb cofs));
         (data_at_ Tsh (Tarray tuchar 64 noattr) pad);
         (K_vector kv)]).
         subst Frame; reflexivity.
       rewrite FR. clear FR Frame.   
       entailer; cancel.
       eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. entailer.
               rewrite sizeof_Tarray, Zplus_comm. cancel.
               apply Zmax_right; omega. 
               reflexivity.
               rewrite sizeof_Tarray, <- initialize.max_unsigned_modulus, int_max_unsigned_eq. omega.
               apply Zmax_right; omega.
   }
   { subst l64 l. split; trivial. split. omega. clear - ge_64_l KL2; destruct KL2. assert (64 <= Int.max_unsigned). 2: omega.
      rewrite int_max_unsigned_eq. omega.
   }
   subst v; normalize.

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

  intros. 
   entailer. unfold POSTCONDITION, abbreviate; simpl. entailer.
   unfold overridePost, initPostKeyNullConditional. 
   if_tac; trivial.
   entailer.
     apply exp_right with (x:=cb). apply andp_right. entailer.
   entailer.
     apply exp_right with (x:=cofs). 
     rewrite data_at__isptr. normalize.
     apply isptrD in Ppad. destruct Ppad as [pb [pofs PAD]].
     apply exp_right with (x:=Vptr pb pofs).
   entailer.
     apply exp_right with (x:=1). entailer. cancel.
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
        apply isptrD in Ppad. destruct Ppad as [pb [pofs PAD]].
        apply exp_right with (x:=cb).
        apply exp_right with (x:=cofs).
        apply exp_right with (x:=Vptr pb pofs).
        apply exp_right with (x:=0). entailer. cancel.
        if_tac; try omega.
          apply exp_right with (x:=r). apply exp_right with (x:=v). entailer.
     inversion H.
  }
  { (*side condition of forward_if key != NULL*)
    intros. entailer. unfold overridePost, normal_ret_assert; simpl. 
    if_tac. simpl. unfold POSTCONDITION, abbreviate, normal_ret_assert.
       entailer. trivial.
  }
Qed.



















