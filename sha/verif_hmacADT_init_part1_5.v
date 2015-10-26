Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

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
                      (Vptr b ofs)))
  | _ => FF
  end. 

Lemma hmac_init_part1_5: forall
(Espec : OracleKind)
(c : val)
(kb : block)
(kofs : int)
(l : val)
(key : list Z)
(kv : val)
(h1 : hmacabs)
(ctx' : name _ctx)
(key' : name _key)
(len' : name _len)
(pad : val)
(ckb : block)
(ckoff : int)
(PostKeyNull : environ -> mpred)
(HeqPostKeyNull : PostKeyNull =
                 EX  cb : block,
                 (EX  cofs : int,
                  (EX  r : Z,
                   PROP  (c = Vptr cb cofs /\ (r = 0 \/ r = 1))
                   LOCAL  (temp _reset (Vint (Int.repr r));
                   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                   lvar _pad (tarray tuchar 64) pad; temp _ctx c;
                   temp _key (Vptr kb kofs); temp _len l; gvar sha._K256 kv)
                   SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                   `(initPostKeyNullConditional l r c (Vptr kb kofs) h1 key
                       (Vptr ckb ckoff)); `(K_vector kv)))))
(Ctx : reptype t_struct_hmac_ctx_st)
(KL2 : 0 <= Zlength key <= Int.max_signed)
(KL3 : Zlength key * 8 < two_p 64)
(L : l = Vint (Int.repr (Zlength key)))
(isbyte_key : Forall isbyteZ key)
(ge_64_l : typed_false tint
            (force_val
               (both_int
                  (fun n1 n2 : int => Some (Val.of_bool (Int.lt n1 n2)))
                  sem_cast_neutral sem_cast_neutral (Vint (Int.repr 64)) l))),
@semax Espec
  (initialized_list [_j; _reset]
     (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr 64)); temp _reset (Vint (Int.repr 1));
   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
   lvar _pad (tarray tuchar 64) pad; temp _ctx c; temp _key (Vptr kb kofs);
   temp _len l; gvar sha._K256 kv)
   SEP  (`(data_at Tsh t_struct_hmac_ctx_st Ctx c);
   `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
       (Vptr kb kofs)); `(data_at_ Tsh (tarray tuchar 64) pad);
   `(data_at_ Tsh (tarray tuchar 64) (Vptr ckb ckoff)); `(K_vector kv)))
  (Ssequence
     (Scall None
        (Evar _memcpy
           (Tfunction
              (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
              (tptr tvoid) cc_default))
        [Evar _ctx_key (tarray tuchar 64); Etempvar _key (tptr tuchar);
        Etempvar _len tint])
     (Scall None
        (Evar _memset
           (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
              (tptr tvoid) cc_default))
        [Eaddrof
           (Ederef
              (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                 (Etempvar _len tint) (tptr tuchar)) tuchar) (tptr tuchar);
        Econst_int (Int.repr 0) tint;
        Ebinop Osub (Econst_int (Int.repr 64) tuint) (Etempvar _len tint)
          tuint])) (normal_ret_assert PostKeyNull).
(*
(Espec : OracleKind)
(kb : block)
(kofs : int)
(l : val)
(key : list Z)
(kv : val)
(h1 : hmacabs)
(ctx' : name _ctx)
(key' : name _key)
(len' : name _len)
(pad : val)
(ckb : block)
(ckoff : int)
(PostKeyNull : environ -> mpred)
(ll : Z)
(Ctx : reptype t_struct_hmac_ctx_st)
(KL : has_lengthK ll key)
(L : l = Vint (Int.repr ll))
(cb : block)
(cofs : int)
(HeqPostKeyNull : PostKeyNull =
                 EX  cb0 : block,
                 (EX  cofs0 : int,
                  (EX  r : Z,
                   PROP  (Vptr cb cofs = Vptr cb0 cofs0 /\ (r = 0 \/ r = 1))
                   LOCAL  (temp _reset (Vint (Int.repr r));
                   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                   lvar _pad (tarray tuchar 64) pad;
                   temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
                   temp _len l; gvar sha._K256 kv)
                   SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                   `(initPostKeyNullConditional l r (Vptr cb cofs)
                       (Vptr kb kofs) h1 key (Vptr ckb ckoff));
                   `(K_vector kv)))))
(isbyte_key : Forall isbyteZ key)
(PostIf_j_Len : environ -> mpred)
(HeqPostIf_j_Len : PostIf_j_Len =
                  EX  CONT : reptype t_struct_hmac_ctx_st,
                  PROP  ()
                  LOCAL  (temp _reset (Vint (Int.repr 1));
                  lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                  lvar _pad (tarray tuchar 64) pad; temp _ctx (Vptr cb cofs);
                  temp _key (Vptr kb kofs); temp _len l; gvar sha._K256 kv)
                  SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                  `(data_at Tsh t_struct_hmac_ctx_st CONT (Vptr cb cofs));
                  `(data_at Tsh (tarray tuchar (Zlength key))
                      (map Vint (map Int.repr key)) (Vptr kb kofs));
                  `(data_at Tsh (tarray tuchar 64)
                      (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                      (Vptr ckb ckoff)); `(K_vector kv)))
(ge_64_l : typed_false tint
            (force_val
               (both_int
                  (fun n1 n2 : int => Some (Val.of_bool (Int.lt n1 n2)))
                  sem_cast_neutral sem_cast_neutral (Vint (Int.repr 64)) l))),
semax
  (initialized_list [_j; _reset]
     (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs))
  (PROP  ()
   LOCAL  (temp _j (Vint (Int.repr 64)); temp _reset (Vint (Int.repr 1));
   lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
   lvar _pad (tarray tuchar 64) pad; temp _ctx (Vptr cb cofs);
   temp _key (Vptr kb kofs); temp _len l; gvar sha._K256 kv)
   SEP  (`(data_at Tsh t_struct_hmac_ctx_st Ctx (Vptr cb cofs));
   `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
       (Vptr kb kofs)); `(data_at_ Tsh (tarray tuchar 64) pad);
   `(data_at_ Tsh (tarray tuchar 64) (Vptr ckb ckoff)); `(K_vector kv)))
  (Ssequence
     (Scall None
        (Evar _memcpy
           (Tfunction
              (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
              (tptr tvoid) cc_default))
        [Evar _ctx_key (tarray tuchar 64); Etempvar _key (tptr tuchar);
        Etempvar _len tint])
     (Scall None
        (Evar _memset
           (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
              (tptr tvoid) cc_default))
        [Eaddrof
           (Ederef
              (Ebinop Oadd (Evar _ctx_key (tarray tuchar 64))
                 (Etempvar _len tint) (tptr tuchar)) tuchar) (tptr tuchar);
        Econst_int (Int.repr 0) tint;
        Ebinop Osub (Econst_int (Int.repr 64) tuint) (Etempvar _len tint)
          tuint])) (normal_ret_assert PostIf_j_Len).*)
Proof. intros.
  subst l. (*rename ll into l. destruct KL as [KL1 [KL2 KL3]].*)

     (*call to memcpy*)
     focus_SEP 1 3.
     unfold data_at_. 
(*     assert_PROP (isptr ctxkey). entailer!. 
     apply isptrD in H; destruct H as [ckb [ckofs CTK]]; subst ctxkey. simpl.*)
     assert_PROP  (offset_in_range 0 (Vptr ckb ckoff) /\ offset_in_range 64 (Vptr ckb ckoff)).
     { entailer. 
       specialize (split_offset_array_at 0 Tsh). unfold tarray. intros X.
       rewrite X with (len:=64)(v:=Vptr ckb ckoff). entailer.
       apply prop_right. specialize (Int.unsigned_range ckoff). intros x; omega.
       reflexivity. rewrite Zlength_correct; simpl; omega. simpl; omega.
     }
     destruct H as [OIR0_328 OIR64_328].
     
     unfold tarray.
     remember (64 - (Zlength key)) as l64.
     assert (HH: match Z.max 0 (Zlength key) with
                     | 0 => 0
                     | Z.pos y' => Z.pos y'
                     | Z.neg y' => Z.neg y'
                 end = Zlength key).
     { rewrite Z.max_r by omega. destruct (Zlength key); reflexivity. }
     forward_call' ((Tsh, Tsh), Vptr ckb ckoff, 
             Vptr kb kofs, mkTrep (Tarray tuchar (Zlength key) noattr) 
                     (map Vint (map Int.repr key))) v.
     { rewrite HH; entailer!. }
     { assert (FR: Frame = [
         (data_at Tsh (Tarray tuchar l64 noattr)
             (Znth (Zlength key) [] Vundef :: skipn (nat_of_Z ((Zlength key) + 1)) [])
             (offset_val (Int.repr (Zlength key)) (Vptr ckb ckoff)));
         (data_at_ Tsh t_struct_hmac_ctx_st c);
         (data_at_ Tsh (Tarray tuchar 64 noattr) pad); (K_vector kv)]).
         subst Frame; reflexivity.
       rewrite FR; clear FR Frame.   
       simpl; entailer!.
         rewrite HH.
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
               rewrite data_at__memory_block. entailer!.
               simpl. rewrite <- Zlength_correct.
               rewrite HH. cancel.
               reflexivity.
               simpl. rewrite <- Zlength_correct, HH. 
               rewrite <- initialize.max_unsigned_modulus. specialize Int.max_signed_unsigned; omega.
         
              rewrite skipn_app2.
              Focus 2. rewrite force_lengthn_length_n. omega.
              rewrite force_lengthn_length_n.
              assert (X: (length key - length key = 0)%nat). omega.
              rewrite X, skipn_0, <- Zlength_correct.
              unfold offset_val. cancel. 
     }
     { simpl; split; auto. rewrite HH. repable_signed. }
     subst v; normalize. simpl. clear HH.  

     assert (l64 <= Int.max_unsigned) by MyOmega. 

     (*call memset*)
     simpl. remember (map Vint (map Int.repr key)) as KCONT.
     forward_call' (Tsh, Vptr ckb (Int.add ckoff (Int.repr (Zlength key))), l64, Int.zero) vret.
     { (*rewrite <- KL1.*)
       match goal with |- _ * _ * ?A * _ * _ * _ |-- _ => 
                  pull_left A end.
       repeat rewrite sepcon_assoc. apply sepcon_derives; [ | cancel].
       eapply derives_trans; try apply data_at_data_at_.
               rewrite data_at__memory_block. 
               rewrite sizeof_Tarray. entailer!.
       rewrite Zmax_spec. simpl in ge_64_l. apply typed_false_of_bool in ge_64_l.
       rewrite if_false. trivial. subst l64. clear - KL2 ge_64_l. 
           apply lt_false_inv in ge_64_l.
           rewrite Int.signed_repr in ge_64_l.
           2: rewrite int_min_signed_eq, int_max_signed_eq; omega.
           rewrite Int.signed_repr in ge_64_l.
           2: rewrite int_min_signed_eq; omega.
           omega.
       reflexivity.
       subst l64.
       rewrite  sizeof_Tarray.
       change Int.modulus with (Int.max_unsigned+1).
       repable_signed. 
       apply Z.max_r. simpl in ge_64_l. apply typed_false_of_bool in ge_64_l. 
           clear - KL2 ge_64_l. 
           apply lt_false_inv in ge_64_l.
           rewrite Int.signed_repr in ge_64_l.
           2: rewrite int_min_signed_eq, int_max_signed_eq; omega.
           rewrite Int.signed_repr in ge_64_l.
           2: rewrite int_min_signed_eq; omega.
           omega. 
     } 
     { split; auto. subst l64. simpl in ge_64_l. apply typed_false_of_bool in ge_64_l. 
           clear - KL2 ge_64_l. 
           apply lt_false_inv in ge_64_l.
           rewrite Int.signed_repr in ge_64_l.
           2: rewrite int_min_signed_eq, int_max_signed_eq; omega.
           rewrite Int.signed_repr in ge_64_l.
           2: rewrite int_min_signed_eq; omega. split. omega. 
           rewrite int_max_unsigned_eq; omega. }

     (*subst PostIf_j_Len.*) subst PostKeyNull.
     normalize.

      assert_PROP (isptr c); [entailer! |].
      make_Vptr c. rename b into cb; rename i into cofs; clear H.
      apply exp_right with cb; apply exp_right with cofs; apply exp_right with 1.
      unfold initPostKeyNullConditional. rewrite zeq_false by omega.
      entailer!. cancel. unfold tarray.

     apply (exp_right (Zlength key)). cancel.
     apply (exp_right (default_val t_struct_hmac_ctx_st)). 
     unfold has_lengthK; entailer. cancel. 
(*
     destruct (zlt 64 (Zlength key)). omega. rewrite Zlength_correct in g. apply (Nat2Z.inj_ge 64) in g.
     clear H0 TC0 h1.*)
     remember (64 - Zlength key) as ZK64.
     rewrite (data_at_Tarray_split3a Tsh tuchar 64 noattr (Zlength key)). 2: omega.
              simpl. unfold nat_of_Z. rewrite Zlength_correct, Nat2Z.id.
              rewrite sepcon_comm.
              specialize (split_offset_array_at (length key) Tsh tuchar 64). unfold tarray; intros SOA.
              rewrite SOA; try reflexivity; clear SOA.
      2: rewrite Zlength_correct, app_length, force_lengthn_length_n, Nat2Z.inj_add; omega.
      2: rewrite Zlength_correct in ge_64_l; omega.
      assert (STO: sizeof tuchar = 1) by reflexivity. rewrite STO, Z.mul_1_l. rewrite Z.mul_1_l.
      entailer!. 

     remember (64 - Zlength key) as ZK64. 
      specialize (split_offset_array_at (Z.to_nat ZK64) Tsh tuchar ZK64). intros X. unfold tarray in X. 
        rewrite X. clear X. entailer!.
     remember (64 - Zlength key) as ZK64. 
     assert (F64: false = (Zlength key >? 64)). 
     { rewrite Z.gtb_ltb. symmetry. apply Fcore_Zaux.Zlt_bool_false. omega. }
     rewrite firstn_app1. 2: rewrite force_lengthn_length_n; trivial.
     rewrite firstn_precise. 2: rewrite length_list_repeat; trivial.
     rewrite firstn_precise. 2: rewrite force_lengthn_length_n; trivial.
     assert (NULL: ZK64 - Z.of_nat (Z.to_nat ZK64) = 0).
     { rewrite Z2Nat.id. omega. omega. }
     rewrite NULL.
     rewrite skipn_short. 2: rewrite length_list_repeat; omega.

     rewrite skipn_force_lengthn_app.
     
     remember (64 -  Z.of_nat (length key)). (*
     remember (Z.of_nat (Z.to_nat (64 - Zlength key))). 
     remember (Z.to_nat (64 - Zlength key)). simpl.*)
     apply derives_trans with
       (Q:= data_at Tsh (Tarray tuchar (Z.of_nat (length key)) noattr)
               (map Vint (map Int.repr key)) (Vptr ckb ckoff) *
            data_at Tsh (Tarray tuchar z noattr) (list_repeat (Z.to_nat z)  (Vint Int.zero))
              (Vptr ckb (Int.add ckoff (Int.repr (Zlength key))))).
     { cancel.  subst ZK64 z. rewrite Zlength_correct, Z2Nat.id.
       cancel.
       eapply derives_trans; try apply data_at_data_at_.
       rewrite data_at__memory_block. simpl. entailer!.
       reflexivity. simpl.
       specialize Int.modulus_pos. omega. rewrite <- Zlength_correct; omega.
     }
     { apply sepcon_derives.
       { apply data_at_Tarray_ext_derives. intros i I.
         apply data_at_triv. unfold Znth. if_tac. trivial. clear H15.
         rewrite nth_force_lengthn.
         Focus 2. split. omega. destruct I as [Ipos I]. apply Z2Nat.inj_lt in I; trivial.
                  rewrite Nat2Z.id in I. trivial. omega.
         assert (Z32: (Z.to_nat i < length key)%nat).
                  clear - I; destruct I as [XX YY]. rewrite Z2Nat.inj_lt in YY.
                  rewrite Nat2Z.id in YY; trivial. trivial. omega. 
         apply eq_sym.
         assert (L1: (Z.to_nat i < length (HMAC_SHA256.mkKey key))%nat).
           rewrite mkKey_length; unfold SHA256.BlockSize.
           assert (Zlength key <= 64) by omega. apply Z2Nat.inj_le in H15. simpl in H15.
           rewrite Zlength_correct, Nat2Z.id in H15. omega.
           omega. omega.
         rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Z0); trivial.
         rewrite nth_map' with (d':=Z0); trivial. f_equal. f_equal.         
         eapply mkKey_left; trivial. rewrite Zlength_correct. trivial.
         rewrite map_length; trivial. rewrite map_length; trivial.
       }
       { unfold offset_val.
         simpl. specialize (Nat2Z.inj_add (length key) 1). simpl; intros ZZ. rewrite <- ZZ. clear ZZ. 
         rewrite Nat2Z.id. (*Z2Nat.id*)
         (*rewrite HeqZK64, Zlength_correct.*)
         (*assert (z = z0). subst. rewrite Z2Nat.id, Zlength_correct; trivial. omega.
         rewrite <- H15 in *. clear H15 Heqz0.*)
         rewrite Zlength_correct.
         apply data_at_Tarray_ext_derives.
(*         assert (z = Z.of_nat (length key)).
            subst. rewrite Z2Nat.id, Zlength_correct; trivial. omega.
         clear Heqz. subst z. subst n. rewrite Z2Nat.id, Zlength_correct. 2: omega.*)
         intros i I.
         apply data_at_triv. unfold Znth. if_tac. trivial. clear H15.
         destruct (zlt (Z.of_nat (length key)) 0).
         rewrite <- Zlength_correct in l. omega.
         rewrite nth_indep with (d:=(default_val tuchar))(d':=Vint (Int.repr 0)).
         Focus 2. rewrite length_list_repeat. apply Z2Nat.inj_lt. omega. omega. omega. 
         rewrite nth_list_repeat. (* rewrite HeqZK64, Zlength_correct in I.*)
         remember (Z.to_nat i) as K; destruct K; simpl.
         rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Z0); trivial. f_equal. f_equal.    
         rewrite mkKey_right; trivial. rewrite Zlength_correct. omega.
         rewrite mkKey_length, Nat2Z.id. unfold SHA256.BlockSize. omega.
         rewrite map_length, mkKey_length, Nat2Z.id. unfold SHA256.BlockSize. omega.
         rewrite nth_skipn. 
         assert (KK: (K + (length key + 1) = Z.to_nat (Z.of_nat (length key) + i))%nat).
            rewrite Z2Nat.inj_add. (*rewrite Z2Nat.inj_add.*) rewrite <- HeqK.
            rewrite Nat2Z.id. omega. omega. omega. (*
            remember (Z.to_nat (Z.of_nat (length key))) as u. simpl. rewrite <- plus_n_Sm. rewrite <- (plus_Snm_nSm u). omega.
            rewrite <- Zlength_correct. apply Zlength_nonneg.
            omega.
            rewrite <- Zlength_correct. apply Zlength_nonneg.
            omega.*)
         rewrite KK; clear KK.
         rewrite nth_map' with (d':=Int.zero).
         rewrite nth_map' with (d':=Z0); trivial. f_equal. f_equal. 
         rewrite mkKey_right; trivial. rewrite Zlength_correct. omega.
         rewrite mkKey_length. unfold SHA256.BlockSize. apply (Z2Nat.inj_lt _ 64). omega. omega. omega. 
         rewrite map_length. rewrite mkKey_length. unfold SHA256.BlockSize. apply (Z2Nat.inj_lt _ 64). omega. omega. omega. 
       }
     } 
     { reflexivity. }
     { rewrite Zlength_correct, length_list_repeat. omega. }
     { rewrite Z2Nat.id; omega. }
Qed.